#
# Copyright 2025, PhD Research Project
# ICS Gateway x86 - Platform Configuration
#
# SPDX-License-Identifier: BSD-2-Clause
#

# Supported platforms for x86 ICS gateway
set(SUPPORTED_PLATFORMS
    "pc99"       # QEMU x86_64 / native x86
)

# Validate platform
if(NOT "${PLATFORM}" IN_LIST SUPPORTED_PLATFORMS)
    message(FATAL_ERROR "Unsupported PLATFORM: ${PLATFORM}. Supported: ${SUPPORTED_PLATFORMS}")
endif()

# Platform-specific settings
if("${PLATFORM}" STREQUAL "pc99")
    message(STATUS "ICS Gateway x86: Building for PC99 (QEMU x86_64)")
    set(KernelPlatform "pc99" CACHE STRING "" FORCE)
endif()

# Enable lwIP for network stack
set(LibLwip ON CACHE BOOL "" FORCE)
