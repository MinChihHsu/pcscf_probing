LOCAL_PATH := $(call my-dir)
include $(CLEAR_VARS)
LOCAL_MODULE    := pcscf_probing
LOCAL_SRC_FILES := pcscf_probing.cpp
LOCAL_LDLIBS    := -llog
include $(BUILD_EXECUTABLE)

