// pcscf_probing.cpp  — Two-phase P-CSCF traceroute prober (IPv4 + IPv6)
//
// Phase 1: TCP SYN with TTL=1,2,3,... until SYN-ACK received → hop_count
//          Also records which TTLs got ICMP Time-Exceeded replies.
// Phase 2: UDP plain payload TTL=1..hop_count-1, collect ICMP Time-Exceeded,
//          take max responding TTL (n), then send 20 UDP packets at TTL=n.
//
// Requires: CAP_NET_RAW (or root) for raw sockets.
// Usage: ./pcscf_probing -i <iface> -p <pcscf1,pcscf2,...> [-s <src_ip>]

#include <arpa/inet.h>
#include <errno.h>
#include <fcntl.h>
#include <ifaddrs.h>
#include <net/if.h>
#include <netinet/icmp6.h>
#include <netinet/in.h>
#include <netinet/ip.h>
#include <netinet/ip6.h>
#include <netinet/ip_icmp.h>
#include <netinet/tcp.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/select.h>
#include <sys/socket.h>
#include <sys/time.h>
#include <time.h>
#include <unistd.h>
#include <pthread.h>

// ─── Tunables ────────────────────────────────────────────────────────────────

#define PCSCF_PORT 5060
#define MAX_PCSCFS 16
#define MAX_IFACE_LEN 64
#define MAX_TTL 64              // upper bound for Phase 1 sweep
#define PHASE1_TIMEOUT_MS 1500  // wait for SYN-ACK or ICMP per TTL step
#define PHASE2_TIMEOUT_MS 1000  // wait for ICMP per TTL step
#define BURST_COUNT 50          // UDP packets to send at the chosen TTL
#define BURST_INTERVAL_US 20000 // 20 ms = 50 pps, matching VoLTE 20 ms voice frame rate
#define BURST_TIMEOUT_MS 500    // max wait per packet for ICMP reply

// UDP destination port for plain UDP probes (arbitrary, not SIP)
#define UDP_PROBE_PORT 33434

// Burst payload: fixed-size binary blob that mimics a real VoLTE RTP packet.
// Layout: [magic(4)] [seq(4)] [pad(RTP_PAYLOAD_PAD_BYTES)] = RTP_PAYLOAD_BYTES total
//
// Why 46 bytes?
//   AMR-WB 12.65 kbps, 20 ms frame (3GPP TS 26.201, RFC 4867 octet-aligned):
//     12 B RTP header  +  1 B CMR  +  1 B ToC  +  32 B audio frame  =  46 B
//   EVS  13.2 kbps,   20 ms frame (3GPP TS 26.445, RFC 4867 compat mode):
//     12 B RTP header  +  1 B CMR  +  33 B audio frame               =  46 B
//   Both codecs land on the same UDP payload size at their most commonly
//   deployed VoLTE bitrates.  Total IPv4 packet: 46+8+20 = 74 B.
#define RTP_PAYLOAD_BYTES     46   // total UDP payload bytes (AMR-WB / EVS common point)
#define RTP_PAYLOAD_PAD_BYTES 38   // zero-padding after magic(4)+seq(4)
#define RTP_PROBE_MAGIC  0x52545000U // "RTP\0"

// ─── Output tee: stdout + record file ────────────────────────────────────────
// All output goes to both stdout (→ app via pipe) and the record file.
// setvbuf(stdout, NULL, _IONBF, 0) in main() ensures per-character flushing
// so the app receives each line immediately without waiting for binary exit.

#define PROBING_RECORD_PATH "/data/local/tmp/pcscf_probing_record.txt"

static FILE *g_record_fp = NULL;

static void open_record_file(void) {
  g_record_fp = fopen(PROBING_RECORD_PATH, "w");
  if (!g_record_fp)
    fprintf(stderr, "[WARN] Cannot open record file: %s\n",
            PROBING_RECORD_PATH);
}

// Drop-in replacement for printf: writes to stdout AND record file.
static void tee_printf(const char *fmt, ...) {
  va_list ap;

  va_start(ap, fmt);
  vprintf(fmt, ap);
  va_end(ap);

  if (g_record_fp) {
    va_start(ap, fmt);
    vfprintf(g_record_fp, fmt, ap);
    va_end(ap);
    fflush(g_record_fp);
  }
}

// Same as tee_printf but writes to stderr AND record file.
static void tee_fprintf_err(const char *fmt, ...) {
  va_list ap;

  va_start(ap, fmt);
  vfprintf(stderr, fmt, ap);
  va_end(ap);

  if (g_record_fp) {
    va_start(ap, fmt);
    vfprintf(g_record_fp, fmt, ap);
    va_end(ap);
    fflush(g_record_fp);
  }
}

// ─── Summary block buffer
// ───────────────────────────────────────────────────── Accumulates lines for
// one summary block, then flushes the entire block as a single tee_printf call
// so the app receives all lines atomically (no interleave).
//
// Usage:
//   summary_begin();
//   summary_line("  key : value");
//   summary_end("Phase 1 Summary");

#define SUMMARY_BUF_SIZE 4096
static char g_summary_buf[SUMMARY_BUF_SIZE];
static int g_summary_len = 0;

static void summary_begin(void) {
  g_summary_buf[0] = '\0';
  g_summary_len = 0;
}

static void summary_line(const char *fmt, ...) {
  char tmp[512];
  va_list ap;
  va_start(ap, fmt);
  vsnprintf(tmp, sizeof(tmp), fmt, ap);
  va_end(ap);

  int written = snprintf(g_summary_buf + g_summary_len,
                         SUMMARY_BUF_SIZE - g_summary_len, "%s\n", tmp);
  if (written > 0)
    g_summary_len += written;
}

// Flush the accumulated block as one atomic tee_printf.
// Format:
//   \n========== <title> ==========\n
//   <body lines>
//   ==========\n
static void summary_end(const char *title) {
  tee_printf("\n========== %s ==========\n%s==========\n", title,
             g_summary_buf);
}

// ─── IpAddr container ────────────────────────────────────────────────────────

typedef struct {
  int family;
  union {
    struct in_addr v4;
    struct in6_addr v6;
  } addr;
  char str[INET6_ADDRSTRLEN];
} IpAddr;

static int parse_ip(const char *s, IpAddr *out) {
  memset(out, 0, sizeof(*out));
  if (inet_pton(AF_INET6, s, &out->addr.v6) == 1) {
    out->family = AF_INET6;
    inet_ntop(AF_INET6, &out->addr.v6, out->str, sizeof(out->str));
    return 0;
  }
  if (inet_pton(AF_INET, s, &out->addr.v4) == 1) {
    out->family = AF_INET;
    inet_ntop(AF_INET, &out->addr.v4, out->str, sizeof(out->str));
    return 0;
  }
  return -1;
}

// ─── Interface helpers
// ────────────────────────────────────────────────────────

static int get_iface_ip(const char *iface, int want_family, IpAddr *out) {
  struct ifaddrs *list = NULL, *ifa;
  if (getifaddrs(&list) != 0) {
    perror("getifaddrs");
    return -1;
  }
  int found = 0;
  for (ifa = list; ifa; ifa = ifa->ifa_next) {
    if (!ifa->ifa_addr || strcmp(ifa->ifa_name, iface) != 0)
      continue;
    if (ifa->ifa_addr->sa_family != want_family)
      continue;
    memset(out, 0, sizeof(*out));
    out->family = want_family;
    if (want_family == AF_INET6) {
      out->addr.v6 = ((struct sockaddr_in6 *)ifa->ifa_addr)->sin6_addr;
      if (IN6_IS_ADDR_LINKLOCAL(&out->addr.v6))
        continue;
      inet_ntop(AF_INET6, &out->addr.v6, out->str, sizeof(out->str));
    } else {
      out->addr.v4 = ((struct sockaddr_in *)ifa->ifa_addr)->sin_addr;
      inet_ntop(AF_INET, &out->addr.v4, out->str, sizeof(out->str));
    }
    found = 1;
    break;
  }
  freeifaddrs(list);
  return found ? 0 : -1;
}

static int bind_to_iface(int fd, const char *ifname) {
  return setsockopt(fd, SOL_SOCKET, SO_BINDTODEVICE, ifname, strlen(ifname)) ==
                 0
             ? 0
             : -1;
}

// Fill a generic sockaddr union; returns length of the filled structure.
static socklen_t fill_sa(const IpAddr *ip, int port,
                         struct sockaddr_storage *out) {
  memset(out, 0, sizeof(*out));
  if (ip->family == AF_INET6) {
    struct sockaddr_in6 *s6 = (struct sockaddr_in6 *)out;
    s6->sin6_family = AF_INET6;
    s6->sin6_addr = ip->addr.v6;
    s6->sin6_port = htons((uint16_t)port);
    return sizeof(*s6);
  } else {
    struct sockaddr_in *s4 = (struct sockaddr_in *)out;
    s4->sin_family = AF_INET;
    s4->sin_addr = ip->addr.v4;
    s4->sin_port = htons((uint16_t)port);
    return sizeof(*s4);
  }
}

// ─── Utility: millisecond select() wait ──────────────────────────────────────

static int wait_readable(int fd, int timeout_ms) {
  fd_set rfds;
  FD_ZERO(&rfds);
  FD_SET(fd, &rfds);
  struct timeval tv;
  tv.tv_sec = timeout_ms / 1000;
  tv.tv_usec = (timeout_ms % 1000) * 1000;
  return select(fd + 1, &rfds, NULL, NULL, &tv);
}

// ─── Deadline helpers ────────────────────────────────────────────────────────

static void make_deadline(struct timeval *dl, int timeout_ms) {
  gettimeofday(dl, NULL);
  dl->tv_usec += timeout_ms * 1000;
  dl->tv_sec += dl->tv_usec / 1000000;
  dl->tv_usec %= 1000000;
}

static int remaining_ms(const struct timeval *dl) {
  struct timeval now;
  gettimeofday(&now, NULL);
  int ms = (int)((dl->tv_sec - now.tv_sec) * 1000 +
                 (dl->tv_usec - now.tv_usec) / 1000);
  return ms < 0 ? 0 : ms;
}

// ─── set_ttl: set hop-limit / TTL on a socket (IPv4 or IPv6) ─────────────────

static void set_ttl(int fd, int family, int ttl) {
  if (family == AF_INET6) {
    setsockopt(fd, IPPROTO_IPV6, IPV6_UNICAST_HOPS, &ttl, sizeof(ttl));
  } else {
    setsockopt(fd, IPPROTO_IP, IP_TTL, &ttl, sizeof(ttl));
  }
}

// ─── Phase 1: TCP SYN sweep + dual ICMP/TCP raw listener ─────────────────────
//
// For each TTL 1..MAX_TTL:
//   • Send TCP SYN with TTL/hop-limit = ttl.
//   • Listen on BOTH a raw TCP socket (for SYN-ACK) and a raw ICMP socket
//     (for Time-Exceeded) simultaneously via select().
//   • Record any TTL that produced an ICMP Time-Exceeded in tcp_icmp_hops[].
//   • Stop when SYN-ACK is received → that TTL becomes hop_count.
//
// Returns hop_count > 0 on success, -1 on failure.
// tcp_icmp_hops[] is filled with TTL values that got ICMP exceed
// (0-terminated).

static int phase1_find_hop_count(const char *iface, const IpAddr *src,
                                 const IpAddr *dst, int *tcp_icmp_hops,
                                 int *tcp_icmp_count) {
  *tcp_icmp_count = 0;
  memset(tcp_icmp_hops, 0, sizeof(int) * (MAX_TTL + 1));

  int af = dst->family;
  tee_printf("\n[Phase 1] TCP SYN TTL sweep toward %s (%s)\n", dst->str,
             af == AF_INET6 ? "IPv6" : "IPv4");

  // ── Raw TCP socket: receives TCP segments ─────────────────────────────────
  int raw_tcp = socket(af, SOCK_RAW, IPPROTO_TCP);
  if (raw_tcp < 0) {
    perror("[Phase 1] raw TCP socket");
    return -1;
  }
  bind_to_iface(raw_tcp, iface);
  {
    struct sockaddr_storage sa;
    socklen_t slen = fill_sa(src, 0, &sa);
    if (bind(raw_tcp, (struct sockaddr *)&sa, slen) < 0)
      perror("[Phase 1] bind raw_tcp (non-fatal)");
  }

  // ── Raw ICMP socket: receives Time-Exceeded triggered by our SYNs ─────────
  int raw_icmp;
  if (af == AF_INET6) {
    raw_icmp = socket(AF_INET6, SOCK_RAW, IPPROTO_ICMPV6);
    if (raw_icmp < 0) {
      perror("[Phase 1] raw ICMPv6 socket");
      close(raw_tcp);
      return -1;
    }
    struct icmp6_filter flt;
    ICMP6_FILTER_SETBLOCKALL(&flt);
    ICMP6_FILTER_SETPASS(ICMP6_TIME_EXCEEDED, &flt);
    setsockopt(raw_icmp, IPPROTO_ICMPV6, ICMP6_FILTER, &flt, sizeof(flt));
  } else {
    // AF_INET: IPPROTO_ICMP raw socket — kernel prepends the IP header.
    raw_icmp = socket(AF_INET, SOCK_RAW, IPPROTO_ICMP);
    if (raw_icmp < 0) {
      perror("[Phase 1] raw ICMP socket");
      close(raw_tcp);
      return -1;
    }
    // IP_HDRINCL not needed for receiving; kernel delivers full IP packet.
  }
  bind_to_iface(raw_icmp, iface);

  int hop_count = -1;

  for (int ttl = 1; ttl <= MAX_TTL; ttl++) {

    // ── Open TCP connect socket ───────────────────────────────────────────
    int fd = socket(af, SOCK_STREAM, IPPROTO_TCP);
    if (fd < 0) {
      perror("socket TCP");
      break;
    }
    bind_to_iface(fd, iface);
    {
      struct sockaddr_storage sa;
      socklen_t slen = fill_sa(src, 0, &sa);
      if (bind(fd, (struct sockaddr *)&sa, slen) < 0)
        perror("[Phase 1] bind src (non-fatal)");
    }
    set_ttl(fd, af, ttl);

    int flags = fcntl(fd, F_GETFL, 0);
    fcntl(fd, F_SETFL, flags | O_NONBLOCK);

    struct sockaddr_storage dst_sa;
    socklen_t dst_slen = fill_sa(dst, PCSCF_PORT, &dst_sa);
    connect(fd, (struct sockaddr *)&dst_sa, dst_slen);

    uint16_t sport = 0;
    {
      struct sockaddr_storage local;
      socklen_t llen = sizeof(local);
      if (getsockname(fd, (struct sockaddr *)&local, &llen) == 0) {
        if (af == AF_INET6)
          sport = ntohs(((struct sockaddr_in6 *)&local)->sin6_port);
        else
          sport = ntohs(((struct sockaddr_in *)&local)->sin_port);
      }
    }
    tee_printf("[Phase 1] TTL=%2d  SYN sent  src_port=%u\n", ttl, sport);

    // ── Wait for SYN-ACK (raw_tcp) OR ICMP Time-Exceeded (raw_icmp) ──────
    int got_synack = 0;
    int got_icmp = 0;

    struct timeval deadline;
    make_deadline(&deadline, PHASE1_TIMEOUT_MS);

    while (1) {
      int rem = remaining_ms(&deadline);
      if (rem <= 0)
        break;

      fd_set rfds;
      FD_ZERO(&rfds);
      FD_SET(raw_tcp, &rfds);
      FD_SET(raw_icmp, &rfds);
      int maxfd = raw_tcp > raw_icmp ? raw_tcp : raw_icmp;

      struct timeval tv = {rem / 1000, (rem % 1000) * 1000};
      int sel = select(maxfd + 1, &rfds, NULL, NULL, &tv);
      if (sel <= 0)
        break;

      // ── Check raw TCP (SYN-ACK) ───────────────────────────────────────
      if (FD_ISSET(raw_tcp, &rfds)) {
        uint8_t pkt[1500];
        struct sockaddr_storage peer;
        socklen_t plen = sizeof(peer);
        ssize_t n = recvfrom(raw_tcp, pkt, sizeof(pkt), 0,
                             (struct sockaddr *)&peer, &plen);

        // IPv6 raw TCP: kernel strips IP header → pkt starts at TCP.
        // IPv4 raw TCP: kernel keeps IP header   → pkt starts at IP.
        const uint8_t *tcp_hdr = pkt;
        int tcp_offset = 0;
        if (af == AF_INET && n >= 20) {
          int ihl = (pkt[0] & 0x0f) * 4;
          tcp_offset = ihl;
        }
        if (n >= tcp_offset + 20) {
          tcp_hdr = pkt + tcp_offset;
          uint16_t dst_port = ntohs(*(uint16_t *)(tcp_hdr + 2));
          uint8_t tcp_flags = tcp_hdr[13];

          // Verify packet is from the P-CSCF destination.
          int from_dst = 0;
          if (af == AF_INET6)
            from_dst = (memcmp(&((struct sockaddr_in6 *)&peer)->sin6_addr,
                               &dst->addr.v6, 16) == 0);
          else
            from_dst = (((struct sockaddr_in *)&peer)->sin_addr.s_addr ==
                        dst->addr.v4.s_addr);

          if (from_dst && dst_port == sport && (tcp_flags & 0x12) == 0x12) {
            tee_printf("[Phase 1] TTL=%2d  *** SYN-ACK received! "
                       "hop_count=%d ***\n",
                       ttl, ttl);
            got_synack = 1;
          }
        }
      }

      // ── Check raw ICMP (Time-Exceeded for our SYN) ───────────────────
      if (FD_ISSET(raw_icmp, &rfds)) {
        uint8_t pkt[1500];
        struct sockaddr_storage peer;
        socklen_t plen = sizeof(peer);
        ssize_t n = recvfrom(raw_icmp, pkt, sizeof(pkt), 0,
                             (struct sockaddr *)&peer, &plen);

        if (af == AF_INET6) {
          // ICMPv6 layout (kernel strips IPv6 header):
          //   [0]   type  (3 = Time Exceeded)
          //   [1]   code  (0 = hop limit exceeded)
          //   [2-7] checksum + unused
          //   [8]   start of original IPv6 header (40 bytes)
          //   [48]  start of original TCP header
          if (n >= 8 + 40 + 20) {
            uint8_t icmp_type = pkt[0];
            uint8_t icmp_code = pkt[1];
            uint8_t orig_nh = pkt[8 + 6];

            struct in6_addr orig_dst;
            memcpy(&orig_dst, pkt + 8 + 24, 16);

            uint16_t orig_dport = ntohs(*(uint16_t *)(pkt + 8 + 40 + 2));
            uint16_t orig_sport = ntohs(*(uint16_t *)(pkt + 8 + 40));

            if (icmp_type == ICMP6_TIME_EXCEEDED && icmp_code == 0 &&
                orig_nh == IPPROTO_TCP &&
                memcmp(&orig_dst, &dst->addr.v6, 16) == 0 &&
                orig_sport == sport && orig_dport == PCSCF_PORT) {

              char peer_str[INET6_ADDRSTRLEN];
              inet_ntop(AF_INET6, &((struct sockaddr_in6 *)&peer)->sin6_addr,
                        peer_str, sizeof(peer_str));
              tee_printf("[Phase 1] TTL=%2d  ICMP6 Time-Exceeded "
                         "from %s\n",
                         ttl, peer_str);

              tcp_icmp_hops[*tcp_icmp_count] = ttl;
              (*tcp_icmp_count)++;
              got_icmp = 1;
            }
          }
        } else {
          // ICMPv4 layout (kernel includes IP header of the ICMP packet):
          //   [0..ihl-1]   outer IP header
          //   [ihl+0]      ICMP type  (11 = Time Exceeded)
          //   [ihl+1]      ICMP code  (0  = TTL exceeded in transit)
          //   [ihl+4]      start of original IP header (≥20 bytes)
          //   [ihl+4+orig_ihl]  start of original TCP header (≥20 bytes)
          if (n >= 20) {
            int outer_ihl = (pkt[0] & 0x0f) * 4;
            if (n >= outer_ihl + 8 + 20) {
              uint8_t icmp_type = pkt[outer_ihl];
              uint8_t icmp_code = pkt[outer_ihl + 1];
              // Embedded original IP header starts at outer_ihl+8
              const uint8_t *orig_ip = pkt + outer_ihl + 8;
              int orig_ihl = (orig_ip[0] & 0x0f) * 4;
              uint8_t orig_proto = orig_ip[9];

              uint32_t orig_dst_addr;
              memcpy(&orig_dst_addr, orig_ip + 16, 4);

              if (n >= outer_ihl + 8 + orig_ihl + 20 &&
                  icmp_type == ICMP_TIME_EXCEEDED &&
                  icmp_code == ICMP_EXC_TTL && orig_proto == IPPROTO_TCP &&
                  orig_dst_addr == dst->addr.v4.s_addr) {

                const uint8_t *orig_tcp = orig_ip + orig_ihl;
                uint16_t orig_sport2 = ntohs(*(uint16_t *)(orig_tcp));
                uint16_t orig_dport2 = ntohs(*(uint16_t *)(orig_tcp + 2));

                if (orig_sport2 == sport && orig_dport2 == PCSCF_PORT) {
                  char peer_str[INET_ADDRSTRLEN];
                  inet_ntop(AF_INET, &((struct sockaddr_in *)&peer)->sin_addr,
                            peer_str, sizeof(peer_str));
                  tee_printf("[Phase 1] TTL=%2d  ICMP Time-Exceeded "
                             "from %s\n",
                             ttl, peer_str);

                  tcp_icmp_hops[*tcp_icmp_count] = ttl;
                  (*tcp_icmp_count)++;
                  got_icmp = 1;
                }
              }
            }
          }
        }
      }

      if (got_synack)
        break;
    }

    close(fd);

    if (got_synack) {
      hop_count = ttl;
      break;
    }

    (void)got_icmp;
  }

  close(raw_tcp);
  close(raw_icmp);

  if (hop_count < 0)
    tee_fprintf_err("[Phase 1] No SYN-ACK received up to TTL=%d\n", MAX_TTL);
  return hop_count;
}

// ─── Phase 2: UDP plain-payload TTL sweep + burst ────────────────────────────
//
// Sweep TTL=1..hop_count-1:
//   payload = "udp_probing_sweep_ttl_{ttl}"
//   Wait for ICMP Time-Exceeded whose embedded UDP dst port == UDP_PROBE_PORT.
//   Track max TTL that got a response → n.
//
// Burst: send BURST_COUNT packets at TTL=n.
//   payload = "udp_probing_burst_seq_{seq}"
//
// Returns max_responding_ttl (>0), or -1 if none responded.

static int phase2_udp_probe(const char *iface, const IpAddr *src,
                            const IpAddr *dst, int hop_count) {
  int af = dst->family;
  tee_printf("\n[Phase 2] UDP TTL sweep TTL=1..%d toward %s (%s)\n",
             hop_count - 1, dst->str, af == AF_INET6 ? "IPv6" : "IPv4");

  // ── Open raw ICMP receive socket ──────────────────────────────────────────
  int icmp_rx;
  if (af == AF_INET6) {
    icmp_rx = socket(AF_INET6, SOCK_RAW, IPPROTO_ICMPV6);
    if (icmp_rx < 0) {
      perror("[Phase 2] raw ICMPv6 socket");
      return -1;
    }
    struct icmp6_filter flt;
    ICMP6_FILTER_SETBLOCKALL(&flt);
    ICMP6_FILTER_SETPASS(ICMP6_TIME_EXCEEDED, &flt);
    setsockopt(icmp_rx, IPPROTO_ICMPV6, ICMP6_FILTER, &flt, sizeof(flt));
  } else {
    icmp_rx = socket(AF_INET, SOCK_RAW, IPPROTO_ICMP);
    if (icmp_rx < 0) {
      perror("[Phase 2] raw ICMP socket");
      return -1;
    }
  }
  bind_to_iface(icmp_rx, iface);

  int max_responding_ttl = -1;

  for (int ttl = 1; ttl < hop_count; ttl++) {

    // ── Build and send plain UDP probe ───────────────────────────────────
    int udp_fd = socket(af, SOCK_DGRAM, IPPROTO_UDP);
    if (udp_fd < 0) {
      perror("socket UDP");
      continue;
    }
    bind_to_iface(udp_fd, iface);
    {
      struct sockaddr_storage sa;
      socklen_t slen = fill_sa(src, 0, &sa);
      bind(udp_fd, (struct sockaddr *)&sa, slen);
    }
    set_ttl(udp_fd, af, ttl);

    struct sockaddr_storage dst_sa;
    socklen_t dst_slen = fill_sa(dst, UDP_PROBE_PORT, &dst_sa);
    connect(udp_fd, (struct sockaddr *)&dst_sa, dst_slen);

    uint16_t sport = 0;
    {
      struct sockaddr_storage local;
      socklen_t llen = sizeof(local);
      if (getsockname(udp_fd, (struct sockaddr *)&local, &llen) == 0) {
        if (af == AF_INET6)
          sport = ntohs(((struct sockaddr_in6 *)&local)->sin6_port);
        else
          sport = ntohs(((struct sockaddr_in *)&local)->sin_port);
      }
    }

    char payload[64];
    snprintf(payload, sizeof(payload), "udp_probing_sweep_ttl_%d", ttl);

    ssize_t sent = sendto(udp_fd, payload, strlen(payload), 0,
                          (struct sockaddr *)&dst_sa, dst_slen);
    close(udp_fd);

    if (sent < 0) {
      tee_fprintf_err("[Phase 2] TTL=%2d sendto: %s\n", ttl, strerror(errno));
      continue;
    }
    tee_printf("[Phase 2] TTL=%2d  UDP sent  src_port=%u  payload=\"%s\"\n",
               ttl, sport, payload);

    // ── Wait for ICMP Time-Exceeded ───────────────────────────────────────
    struct timeval deadline;
    make_deadline(&deadline, PHASE2_TIMEOUT_MS);

    int got_exceed = 0;
    while (1) {
      int rem = remaining_ms(&deadline);
      if (rem <= 0)
        break;

      int sel = wait_readable(icmp_rx, rem);
      if (sel <= 0)
        break;

      uint8_t pkt[1500];
      struct sockaddr_storage peer;
      socklen_t plen = sizeof(peer);
      ssize_t n = recvfrom(icmp_rx, pkt, sizeof(pkt), 0,
                           (struct sockaddr *)&peer, &plen);

      if (af == AF_INET6) {
        // ICMPv6 layout (kernel strips IPv6 header):
        //   [0-1]  type/code
        //   [2-7]  checksum + unused
        //   [8]    original IPv6 header (40 bytes)
        //   [48]   original UDP header (8 bytes)
        if (n < 8 + 40 + 8)
          continue;

        uint8_t icmp_type = pkt[0];
        uint8_t icmp_code = pkt[1];
        uint8_t orig_nh = pkt[8 + 6];

        struct in6_addr orig_dst;
        memcpy(&orig_dst, pkt + 8 + 24, 16);

        uint16_t orig_sport2 = ntohs(*(uint16_t *)(pkt + 8 + 40));
        uint16_t orig_dport2 = ntohs(*(uint16_t *)(pkt + 8 + 42));

        if (icmp_type != ICMP6_TIME_EXCEEDED || icmp_code != 0)
          continue;
        if (orig_nh != IPPROTO_UDP)
          continue;
        if (memcmp(&orig_dst, &dst->addr.v6, 16) != 0)
          continue;
        if (orig_sport2 != sport || orig_dport2 != UDP_PROBE_PORT)
          continue;

        char peer_str[INET6_ADDRSTRLEN];
        inet_ntop(AF_INET6, &((struct sockaddr_in6 *)&peer)->sin6_addr,
                  peer_str, sizeof(peer_str));
        tee_printf("[Phase 2] TTL=%2d  ICMP6 Time-Exceeded from %s  ✓\n", ttl,
                   peer_str);
        got_exceed = 1;
      } else {
        // ICMPv4 layout (kernel includes outer IP header):
        //   [0..ihl-1]       outer IP header
        //   [ihl]            ICMP type (11 = Time Exceeded)
        //   [ihl+1]          ICMP code (0 = TTL exceeded)
        //   [ihl+4]          embedded original IP header
        //   [ihl+4+orig_ihl] embedded original UDP header (8 bytes)
        if (n < 20)
          continue;
        int outer_ihl = (pkt[0] & 0x0f) * 4;
        if (n < outer_ihl + 8 + 20 + 8)
          continue;

        uint8_t icmp_type = pkt[outer_ihl];
        uint8_t icmp_code = pkt[outer_ihl + 1];
        const uint8_t *orig_ip = pkt + outer_ihl + 8;
        int orig_ihl = (orig_ip[0] & 0x0f) * 4;
        uint8_t orig_proto = orig_ip[9];

        uint32_t orig_dst_addr;
        memcpy(&orig_dst_addr, orig_ip + 16, 4);

        if (n < outer_ihl + 8 + orig_ihl + 8)
          continue;
        const uint8_t *orig_udp = orig_ip + orig_ihl;
        uint16_t orig_sport2 = ntohs(*(uint16_t *)(orig_udp));
        uint16_t orig_dport2 = ntohs(*(uint16_t *)(orig_udp + 2));

        if (icmp_type != ICMP_TIME_EXCEEDED || icmp_code != ICMP_EXC_TTL)
          continue;
        if (orig_proto != IPPROTO_UDP)
          continue;
        if (orig_dst_addr != dst->addr.v4.s_addr)
          continue;
        if (orig_sport2 != sport || orig_dport2 != UDP_PROBE_PORT)
          continue;

        char peer_str[INET_ADDRSTRLEN];
        inet_ntop(AF_INET, &((struct sockaddr_in *)&peer)->sin_addr, peer_str,
                  sizeof(peer_str));
        tee_printf("[Phase 2] TTL=%2d  ICMP Time-Exceeded from %s  ✓\n", ttl,
                   peer_str);
        got_exceed = 1;
      }

      if (got_exceed)
        break;
    }

    if (got_exceed && ttl > max_responding_ttl)
      max_responding_ttl = ttl;

    if (!got_exceed)
      tee_printf("[Phase 2] TTL=%2d  no ICMP response\n", ttl);
  }

  close(icmp_rx);
  return max_responding_ttl;
}

// ─── Phase 2 burst — sender + receiver pthreads for accurate 50 pps ─────────
//
// Problem with a single sequential loop:
//   send → wait ICMP (variable RTT) → sleep BURST_INTERVAL_US → send next
//   The ICMP wait adds latency on top of the sleep, making actual send rate
//   lower than 50 pps and jitter-dependent.
//
// Solution — two concurrent pthreads:
//   burst_sender_thread  : sends one UDP packet every BURST_INTERVAL_US (20 ms).
//                          Records (sport, send_time) into shared ctx under mutex.
//   burst_receiver_thread: listens on the raw ICMP socket for the full burst
//                          window concurrently.  Matches each Time-Exceeded back
//                          to its packet via the original source port.
//
// The receiver is started first so it is ready before the first packet flies.

typedef struct {
  // Read-only config (set before threads start)
  const char   *iface;
  const IpAddr *src;
  const IpAddr *dst;
  int           burst_ttl;
  int           af;
  int           icmp_rx;   // raw ICMP socket, pre-opened and shared

  // Written by sender, read by receiver  (protected by lock)
  pthread_mutex_t lock;
  struct timeval  send_times[BURST_COUNT + 1]; // 1-indexed
  uint16_t        sports[BURST_COUNT + 1];      // 1-indexed
  int             n_sent;                       // packets sent so far
  int             sender_done;                  // set to 1 when sender exits

  // Written by receiver, read by main after join (no lock needed post-join)
  double rtt_ms[BURST_COUNT + 1];              // 1-indexed
  int    received[BURST_COUNT + 1];            // 1-indexed
  int    rx_count;
} BurstCtx;

static void *burst_sender_thread(void *arg) {
  BurstCtx *ctx = (BurstCtx *)arg;
  int        af  = ctx->af;

  for (int i = 1; i <= BURST_COUNT; i++) {
    int udp_fd = socket(af, SOCK_DGRAM, IPPROTO_UDP);
    if (udp_fd < 0) { perror("socket UDP burst"); continue; }
    bind_to_iface(udp_fd, ctx->iface);
    {
      struct sockaddr_storage sa;
      socklen_t slen = fill_sa(ctx->src, 0, &sa);
      bind(udp_fd, (struct sockaddr *)&sa, slen);
    }
    set_ttl(udp_fd, af, ctx->burst_ttl);

    struct sockaddr_storage dst_sa;
    socklen_t dst_slen = fill_sa(ctx->dst, UDP_PROBE_PORT, &dst_sa);
    connect(udp_fd, (struct sockaddr *)&dst_sa, dst_slen);

    // Ephemeral source port — the ICMP match key
    uint16_t sport = 0;
    {
      struct sockaddr_storage local;
      socklen_t llen = sizeof(local);
      if (getsockname(udp_fd, (struct sockaddr *)&local, &llen) == 0) {
        if (af == AF_INET6)
          sport = ntohs(((struct sockaddr_in6 *)&local)->sin6_port);
        else
          sport = ntohs(((struct sockaddr_in *)&local)->sin_port);
      }
    }

    // ── Build RTP-sized binary payload: magic(4) + seq(4) + zeros(38) ──
    struct __attribute__((packed)) {
      uint32_t magic;
      uint32_t seq;
      uint8_t  pad[RTP_PAYLOAD_PAD_BYTES];
    } payload;
    static_assert(sizeof(payload) == RTP_PAYLOAD_BYTES, "payload size mismatch");
    payload.magic = htonl(RTP_PROBE_MAGIC);
    payload.seq   = htonl((uint32_t)i);
    memset(payload.pad, 0, sizeof(payload.pad));

    // Publish sport + send_time before sendto so the receiver can match
    // an ICMP that arrives before n_sent is next checked.
    struct timeval t_send;
    gettimeofday(&t_send, NULL);
    pthread_mutex_lock(&ctx->lock);
    ctx->send_times[i] = t_send;
    ctx->sports[i]     = sport;
    ctx->n_sent        = i;
    pthread_mutex_unlock(&ctx->lock);

    ssize_t s = sendto(udp_fd, &payload, sizeof(payload), 0,
                       (struct sockaddr *)&dst_sa, dst_slen);
    close(udp_fd);

    if (s <= 0)
      tee_fprintf_err("[Burst] #%2d sendto: %s\n", i, strerror(errno));
    else
      tee_printf("[Burst] #%2d/%d  TTL=%d  sport=%-5u  sent  seq=%u  size=%zu B\n",
                 i, BURST_COUNT, ctx->burst_ttl, sport, (uint32_t)i, sizeof(payload));

    if (i < BURST_COUNT)
      usleep(BURST_INTERVAL_US);  // strict 20 ms inter-packet gap
  }

  pthread_mutex_lock(&ctx->lock);
  ctx->sender_done = 1;
  pthread_mutex_unlock(&ctx->lock);
  return NULL;
}

static void *burst_receiver_thread(void *arg) {
  BurstCtx *ctx = (BurstCtx *)arg;
  int        af  = ctx->af;

  // Listening window = time to send all packets + one last-packet RTT headroom
  int window_ms = BURST_COUNT * (BURST_INTERVAL_US / 1000) + BURST_TIMEOUT_MS;
  struct timeval deadline;
  make_deadline(&deadline, window_ms);

  while (remaining_ms(&deadline) > 0) {
    int rem = remaining_ms(&deadline);
    int sel = wait_readable(ctx->icmp_rx, rem < 100 ? rem : 100);
    if (sel <= 0) {
      // Early exit: sender done and every sent packet got a reply
      pthread_mutex_lock(&ctx->lock);
      int done = ctx->sender_done;
      int got  = ctx->rx_count;
      int sent = ctx->n_sent;
      pthread_mutex_unlock(&ctx->lock);
      if (done && got == sent) break;
      continue;
    }

    uint8_t pkt[1500];
    struct sockaddr_storage peer;
    socklen_t plen = sizeof(peer);
    ssize_t n = recvfrom(ctx->icmp_rx, pkt, sizeof(pkt), 0,
                         (struct sockaddr *)&peer, &plen);
    if (n < 0) continue;

    // ── Parse ICMP and extract original (sport, dport) ──────────────────
    uint16_t orig_sport = 0, orig_dport = 0;
    char peer_str[INET6_ADDRSTRLEN] = {0};
    int  icmp_ok = 0;

    if (af == AF_INET6) {
      if (n < 8 + 40 + 8) continue;
      uint8_t icmp_type = pkt[0], icmp_code = pkt[1];
      uint8_t orig_nh = pkt[8 + 6];
      struct in6_addr orig_dst;
      memcpy(&orig_dst, pkt + 8 + 24, 16);
      orig_sport = ntohs(*(uint16_t *)(pkt + 8 + 40));
      orig_dport = ntohs(*(uint16_t *)(pkt + 8 + 42));
      if (icmp_type == ICMP6_TIME_EXCEEDED && icmp_code == 0 &&
          orig_nh == IPPROTO_UDP &&
          memcmp(&orig_dst, &ctx->dst->addr.v6, 16) == 0 &&
          orig_dport == UDP_PROBE_PORT) {
        inet_ntop(AF_INET6, &((struct sockaddr_in6 *)&peer)->sin6_addr,
                  peer_str, sizeof(peer_str));
        icmp_ok = 1;
      }
    } else {
      if (n < 20) continue;
      int outer_ihl = (pkt[0] & 0x0f) * 4;
      if (n < outer_ihl + 8 + 20 + 8) continue;
      uint8_t icmp_type = pkt[outer_ihl], icmp_code = pkt[outer_ihl + 1];
      const uint8_t *orig_ip = pkt + outer_ihl + 8;
      int orig_ihl = (orig_ip[0] & 0x0f) * 4;
      uint8_t orig_proto = orig_ip[9];
      uint32_t orig_dst_addr;
      memcpy(&orig_dst_addr, orig_ip + 16, 4);
      if (n < outer_ihl + 8 + orig_ihl + 8) continue;
      const uint8_t *orig_udp = orig_ip + orig_ihl;
      orig_sport = ntohs(*(uint16_t *)(orig_udp));
      orig_dport = ntohs(*(uint16_t *)(orig_udp + 2));
      if (icmp_type == ICMP_TIME_EXCEEDED && icmp_code == ICMP_EXC_TTL &&
          orig_proto == IPPROTO_UDP &&
          orig_dst_addr == ctx->dst->addr.v4.s_addr &&
          orig_dport == UDP_PROBE_PORT) {
        inet_ntop(AF_INET, &((struct sockaddr_in *)&peer)->sin_addr,
                  peer_str, sizeof(peer_str));
        icmp_ok = 1;
      }
    }
    if (!icmp_ok) continue;

    // ── Match orig_sport → packet index, compute RTT ──────────────────
    struct timeval t_recv;
    gettimeofday(&t_recv, NULL);

    pthread_mutex_lock(&ctx->lock);
    int n_sent_now = ctx->n_sent;
    int idx = -1;
    for (int i = 1; i <= n_sent_now; i++) {
      if (ctx->sports[i] == orig_sport && !ctx->received[i]) {
        idx = i;
        break;
      }
    }
    struct timeval t_send = {0, 0};
    if (idx > 0) t_send = ctx->send_times[idx];
    pthread_mutex_unlock(&ctx->lock);

    if (idx > 0) {
      double rtt = (t_recv.tv_sec  - t_send.tv_sec)  * 1000.0 +
                   (t_recv.tv_usec - t_send.tv_usec) / 1000.0;
      ctx->rtt_ms[idx]   = rtt;
      ctx->received[idx] = 1;
      ctx->rx_count++;
      tee_printf("[Burst] #%2d/%d  RTT=%.3f ms  from %s  \xe2\x9c\x93\n",
                 idx, BURST_COUNT, rtt, peer_str);
    }
  }
  return NULL;
}

static void phase2_burst(const char *iface, const IpAddr *src,
                         const IpAddr *dst, int burst_ttl) {
  int af = dst->family;
  int ip_hdr_sz = (af == AF_INET6) ? 40 : 20;
  tee_printf(
      "\n[Phase 2] Burst: %d UDP pkts @ TTL=%d — sender+receiver pthreads\n"
      "          Rate: %d pps (%d µs interval)  payload=%d B UDP / ~%d B IPv%c\n",
      BURST_COUNT, burst_ttl,
      1000000 / BURST_INTERVAL_US, BURST_INTERVAL_US,
      RTP_PAYLOAD_BYTES, RTP_PAYLOAD_BYTES + 8 + ip_hdr_sz,
      af == AF_INET6 ? '6' : '4');

  // ── Open raw ICMP socket (shared, read-only after open) ───────────────
  int icmp_rx;
  if (af == AF_INET6) {
    icmp_rx = socket(AF_INET6, SOCK_RAW, IPPROTO_ICMPV6);
    if (icmp_rx < 0) { perror("[Burst] raw ICMPv6"); return; }
    struct icmp6_filter flt;
    ICMP6_FILTER_SETBLOCKALL(&flt);
    ICMP6_FILTER_SETPASS(ICMP6_TIME_EXCEEDED, &flt);
    setsockopt(icmp_rx, IPPROTO_ICMPV6, ICMP6_FILTER, &flt, sizeof(flt));
  } else {
    icmp_rx = socket(AF_INET, SOCK_RAW, IPPROTO_ICMP);
    if (icmp_rx < 0) { perror("[Burst] raw ICMP"); return; }
  }
  bind_to_iface(icmp_rx, iface);

  // ── Init shared context ───────────────────────────────────────────────
  BurstCtx ctx;
  memset(&ctx, 0, sizeof(ctx));
  ctx.iface     = iface;
  ctx.src       = src;
  ctx.dst       = dst;
  ctx.burst_ttl = burst_ttl;
  ctx.af        = af;
  ctx.icmp_rx   = icmp_rx;
  pthread_mutex_init(&ctx.lock, NULL);

  // ── Start receiver first so it is ready before the first packet ───────
  pthread_t rx_tid, tx_tid;
  pthread_create(&rx_tid, NULL, burst_receiver_thread, &ctx);
  pthread_create(&tx_tid, NULL, burst_sender_thread,   &ctx);

  pthread_join(tx_tid, NULL);
  pthread_join(rx_tid, NULL);
  pthread_mutex_destroy(&ctx.lock);
  close(icmp_rx);

  // ── Aggregate statistics (single-threaded after join) ─────────────────
  int burst_sent = 0, rx_count = 0;
  double sum = 0.0, min_rtt = 1e9, max_rtt = 0.0;
  for (int i = 1; i <= BURST_COUNT; i++) {
    if (ctx.sports[i] != 0) {
      burst_sent++;
      if (!ctx.received[i])
        tee_printf("[Burst] #%2d/%d  LOST (no ICMP)\n", i, BURST_COUNT);
    }
    if (!ctx.received[i]) continue;
    rx_count++;
    sum += ctx.rtt_ms[i];
    if (ctx.rtt_ms[i] < min_rtt) min_rtt = ctx.rtt_ms[i];
    if (ctx.rtt_ms[i] > max_rtt) max_rtt = ctx.rtt_ms[i];
  }
  double avg_rtt = (rx_count > 0) ? sum / rx_count : 0.0;

  // Jitter = mean |RTT_i − RTT_{i-1}| (RFC 3550)
  double jitter = 0.0;
  int jit_cnt = 0;
  double prev = -1.0;
  for (int i = 1; i <= BURST_COUNT; i++) {
    if (!ctx.received[i]) continue;
    if (prev >= 0.0) {
      double d = ctx.rtt_ms[i] - prev;
      jitter += (d < 0.0 ? -d : d);
      jit_cnt++;
    }
    prev = ctx.rtt_ms[i];
  }
  if (jit_cnt > 0) jitter /= jit_cnt;

  int lost = burst_sent - rx_count;
  double loss_pct = (burst_sent > 0) ? (double)lost / burst_sent * 100.0 : 0.0;

  summary_begin();
  summary_line("  Burst TTL               : %d", burst_ttl);
  summary_line("  Packets sent            : %d", burst_sent);
  summary_line("  Packets received (ICMP) : %d", rx_count);
  summary_line("  Packet loss             : %d/%d  (%.1f%%)", lost, burst_sent, loss_pct);
  if (rx_count > 0) {
    summary_line("  RTT min                 : %.3f ms", min_rtt);
    summary_line("  RTT avg                 : %.3f ms", avg_rtt);
    summary_line("  RTT max                 : %.3f ms", max_rtt);
    summary_line("  Jitter (mean |delta|)   : %.3f ms", jit_cnt > 0 ? jitter : 0.0);
  } else {
    summary_line("  RTT                     : N/A (no replies)");
  }
  summary_end("Burst RTT & Packet Loss Summary");
}

// ─── probe_one: orchestrate both phases + print summary ──────────────────────

static int probe_one(const char *iface, const IpAddr *src, const IpAddr *dst) {
  if (src->family != dst->family) {
    tee_fprintf_err("[SKIP] src/dst address family mismatch (%s vs %s)\n",
                    src->str, dst->str);
    return 0;
  }

  tee_printf("\n=== Probing P-CSCF: %s ===\n", dst->str);

  // ── Phase 1 ──────────────────────────────────────────────────────────────
  int tcp_icmp_hops[MAX_TTL + 1];
  int tcp_icmp_count = 0;

  int hop_count =
      phase1_find_hop_count(iface, src, dst, tcp_icmp_hops, &tcp_icmp_count);
  if (hop_count < 1) {
    tee_fprintf_err("[FAIL] Phase 1 failed for %s\n", dst->str);
    return 0;
  }

  // TCP max hop before target = highest TTL that got ICMP exceed
  int tcp_max_icmp_hop = -1;
  for (int i = 0; i < tcp_icmp_count; i++)
    if (tcp_icmp_hops[i] > tcp_max_icmp_hop)
      tcp_max_icmp_hop = tcp_icmp_hops[i];

  // ── Phase 1 summary (atomic block) ───────────────────────────────────────
  {
    summary_begin();
    summary_line("  hop_count (SYN-ACK TTL)          : %d", hop_count);
    if (tcp_icmp_count > 0) {
      // Build comma-separated TTL list into a temp string first.
      char ttl_list[256] = {0};
      int pos = 0;
      for (int i = 0; i < tcp_icmp_count; i++) {
        int n = snprintf(ttl_list + pos, (int)sizeof(ttl_list) - pos, "%d%s",
                         tcp_icmp_hops[i], i < tcp_icmp_count - 1 ? ", " : "");
        if (n > 0)
          pos += n;
      }
      summary_line("  TCP SYN TTLs that got ICMP exceed : %s", ttl_list);
      summary_line("  TCP max hop before target         : %d",
                   tcp_max_icmp_hop);
    } else {
      summary_line("  TCP SYN TTLs that got ICMP exceed : (none)");
      summary_line("  TCP max hop before target         : N/A");
    }
    summary_end("Phase 1 Summary");
  }

  if (hop_count == 1) {
    tee_printf("[INFO] P-CSCF is 1 hop away — skipping Phase 2.\n");
    return 1;
  }

  // ── Phase 2 ──────────────────────────────────────────────────────────────
  int udp_max_ttl = phase2_udp_probe(iface, src, dst, hop_count);

  // ── Phase 2 summary (atomic block) ───────────────────────────────────────
  {
    summary_begin();
    if (udp_max_ttl > 0)
      summary_line("  UDP max hop before target (burst TTL): %d", udp_max_ttl);
    else
      summary_line(
          "  UDP max hop before target            : N/A (no ICMP received)");
    summary_end("Phase 2 Summary");
  }

  // ── Combined summary (atomic block) ──────────────────────────────────────
  {
    char title[128];
    snprintf(title, sizeof(title), "Combined Summary for %s", dst->str);
    summary_begin();
    if (tcp_max_icmp_hop > 0)
      summary_line("  [TCP] max responding hop before target : %d",
                   tcp_max_icmp_hop);
    else
      summary_line("  [TCP] max responding hop before target : N/A");
    if (udp_max_ttl > 0)
      summary_line("  [UDP] max responding hop before target : %d",
                   udp_max_ttl);
    else
      summary_line("  [UDP] max responding hop before target : N/A");
    summary_end(title);
  }

  if (udp_max_ttl < 1) {
    tee_fprintf_err("[Phase 2] No ICMP received — skipping burst.\n");
    return 1;
  }

  // ── Burst ─────────────────────────────────────────────────────────────────
  phase2_burst(iface, src, dst, udp_max_ttl);

  return 1;
}

// ─── main ────────────────────────────────────────────────────────────────────

static void usage(const char *prog) {
  fprintf(stderr,
          "Usage: %s -i <iface> -p <pcscf1,pcscf2,...> [-s <src_ip>]\n"
          "  -i  Voice interface (e.g. rmnet_data2)\n"
          "  -p  Comma-separated P-CSCF IPv4 or IPv6 addresses\n"
          "  -s  Source IP (optional; auto-detected from iface if omitted)\n"
          "\nRequires CAP_NET_RAW / root for raw sockets.\n",
          prog);
}

int main(int argc, char *argv[]) {
  // ── 關閉 stdout buffering：確保每行輸出立刻送達 app pipe ─────────────────
  setvbuf(stdout, NULL, _IONBF, 0);

  // ── 開啟 record 檔案（截斷舊內容）────────────────────────────────────────
  open_record_file();

  char iface[MAX_IFACE_LEN] = {0};
  char src_str[INET6_ADDRSTRLEN] = {0};
  char pcscf_arg[2048] = {0};

  int opt;
  while ((opt = getopt(argc, argv, "i:p:s:")) != -1) {
    switch (opt) {
    case 'i':
      strncpy(iface, optarg, MAX_IFACE_LEN - 1);
      break;
    case 'p':
      strncpy(pcscf_arg, optarg, sizeof(pcscf_arg) - 1);
      break;
    case 's':
      strncpy(src_str, optarg, INET6_ADDRSTRLEN - 1);
      break;
    default:
      usage(argv[0]);
      if (g_record_fp)
        fclose(g_record_fp);
      return 1;
    }
  }
  if (iface[0] == '\0' || pcscf_arg[0] == '\0') {
    usage(argv[0]);
    if (g_record_fp)
      fclose(g_record_fp);
    return 1;
  }

  srand((unsigned)time(NULL));

  // ── Parse P-CSCF addresses (IPv4 and/or IPv6) ────────────────────────────
  IpAddr pcscfs[MAX_PCSCFS];
  int pcscf_count = 0;
  char *tok = strtok(pcscf_arg, ",");
  while (tok && pcscf_count < MAX_PCSCFS) {
    if (parse_ip(tok, &pcscfs[pcscf_count]) == 0)
      pcscf_count++;
    else
      tee_fprintf_err("[SKIP] Cannot parse: %s\n", tok);
    tok = strtok(NULL, ",");
  }
  if (pcscf_count == 0) {
    tee_fprintf_err("No valid P-CSCF addresses.\n");
    if (g_record_fp)
      fclose(g_record_fp);
    return 1;
  }

  // ── Resolve source address ────────────────────────────────────────────────
  // We may need both an IPv4 and an IPv6 source depending on the P-CSCF list.
  IpAddr src_provided;
  int have_src_provided = 0;

  if (src_str[0] != '\0') {
    if (parse_ip(src_str, &src_provided) != 0) {
      tee_fprintf_err("Invalid -s src_ip: '%s'\n", src_str);
      if (g_record_fp)
        fclose(g_record_fp);
      return 1;
    }
    have_src_provided = 1;
    tee_printf("[INFO] Using provided src: %s\n", src_provided.str);
  }

  // ── Probe each P-CSCF ────────────────────────────────────────────────────
  int overall = 0;
  for (int pi = 0; pi < pcscf_count; pi++) {
    IpAddr src;
    int have_src = 0;
    int need_family = pcscfs[pi].family;

    if (have_src_provided) {
      if (src_provided.family == need_family) {
        src = src_provided;
        have_src = 1;
      } else {
        // Provided -s is for the other family; try auto-detect.
        tee_printf("[INFO] -s address family (%s) doesn't match "
                   "P-CSCF %s — auto-detecting src\n",
                   src_provided.family == AF_INET6 ? "IPv6" : "IPv4",
                   pcscfs[pi].str);
      }
    }

    if (!have_src) {
      if (get_iface_ip(iface, need_family, &src) == 0) {
        have_src = 1;
        tee_printf("[INFO] src %s (getifaddrs): %s\n",
                   need_family == AF_INET6 ? "IPv6" : "IPv4", src.str);
      }
    }

    if (!have_src) {
      tee_fprintf_err("[SKIP] Cannot find %s address for interface '%s' "
                      "— needed for P-CSCF %s. Pass -s <src_ip>.\n",
                      need_family == AF_INET6 ? "IPv6" : "IPv4", iface,
                      pcscfs[pi].str);
      continue;
    }

    if (probe_one(iface, &src, &pcscfs[pi]))
      overall = 1;
  }

  tee_printf("\n[DONE]\n");

  // ── 關閉 record 檔案 ──────────────────────────────────────────────────────
  if (g_record_fp) {
    fclose(g_record_fp);
    g_record_fp = NULL;
  }

  return overall ? 0 : 2;
}
