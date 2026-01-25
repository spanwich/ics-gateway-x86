#
# Copyright 2025, PhD Research Project
# ICS Gateway x86 - Pure CAmkES Application
#
# EverParse formally verified Modbus TCP parsing with dual NIC architecture
# Port from ARM modbus_bidirection_poc to x86 pc99 platform
#
# SPDX-License-Identifier: BSD-2-Clause
#

cmake_minimum_required(VERSION 3.8.2)

project(ics_gateway_x86 C ASM)

# Include settings
include(settings.cmake)

# Find lwIP for network stack
set(projects_dir "${CMAKE_CURRENT_LIST_DIR}/../")
find_file(LWIP_PATH lwip PATHS ${projects_dir} CMAKE_FIND_ROOT_PATH_BOTH)
if("${LWIP_PATH}" STREQUAL "LWIP_PATH-NOTFOUND")
    message(FATAL_ERROR "Failed to find lwIP")
endif()

# Include lwIP helpers
include(${projects_dir}/util_libs/liblwip/lwip_helpers.cmake)

# Create SEPARATE lwIP libraries for Net0 and Net1 to prevent shared state corruption
# Each component gets its own lwIP instance with isolated memory pools

# lwIP for Net0 (SCADA-facing driver)
AddLWIPConfiguration(${CMAKE_CURRENT_LIST_DIR}/components/Net0_Driver)

# lwIP for Net1 (PLC-facing driver) - Create separate library with its own config
add_library(liblwip_config_net1 INTERFACE)
target_include_directories(liblwip_config_net1 INTERFACE ${CMAKE_CURRENT_LIST_DIR}/components/Net1_Driver)

file(GLOB lwip_sources_net1
    ${LWIP_PATH}/src/*/*.c
    ${LWIP_PATH}/src/core/ipv4/*.c
)
add_library(lwip_net1 STATIC EXCLUDE_FROM_ALL ${lwip_sources_net1})
target_include_directories(lwip_net1 PUBLIC
    ${LWIP_PATH}/src/include
    ${projects_dir}/util_libs/liblwip/include
    ${projects_dir}/util_libs/liblwip/include/lwip
)
target_link_libraries(lwip_net1 muslc liblwip_config_net1)
target_compile_definitions(lwip_net1 PRIVATE LWIP_NET1_INSTANCE=1)

# Net0_Driver Component (External Network - SCADA facing)
DeclareCAmkESComponent(
    Net0_Driver
    SOURCES
        components/Net0_Driver/net0_driver.c
    INCLUDES
        components/Net0_Driver
        components/include
        ${LWIP_PATH}/src/include
        ${projects_dir}/util_libs/liblwip/include
    LIBS
        sel4_autoconf
        utils
        lwip
        ethdrivers
)

# Net1_Driver Component (Internal Network - PLC facing)
# Uses separate lwip_net1 library for isolation
DeclareCAmkESComponent(
    Net1_Driver
    SOURCES
        components/Net1_Driver/net1_driver.c
    INCLUDES
        components/Net1_Driver
        components/include
        ${LWIP_PATH}/src/include
        ${projects_dir}/util_libs/liblwip/include
    LIBS
        sel4_autoconf
        utils
        lwip_net1
        ethdrivers
)

# ICS_Inbound Component (External -> Internal validation)
# v2.290: F*-only validation with integrated policy enforcement
# Policy constraints are encoded as dependent types in the EverParse/F* specification.
# CVE-2022-0367 mitigation is mathematically proven at the type level.
DeclareCAmkESComponent(
    ICS_Inbound
    SOURCES
        components/ICS_Inbound/ICS_Inbound.c
        components/lib/modbus_policy_fstar.c
        components/include/ModbusTCP_v4_PolicyEnforced.c
        components/include/ModbusTCP_v4_PolicyEnforcedWrapper.c
        components/include/ModbusTCP_v3_Simple.c
        components/include/ModbusTCP_v3_SimpleWrapper.c
        components/lib/everparse_error_handler.c
    INCLUDES
        components/include
)

# ICS_Outbound Component (Internal -> External validation)
# v2.300: Symmetric F*-verified response validation (Zero Trust ICS)
# Response validators prevent data exfiltration, address confusion, and exception abuse.
DeclareCAmkESComponent(
    ICS_Outbound
    SOURCES
        components/ICS_Outbound/ICS_Outbound.c
        components/lib/modbus_response_policy_fstar.c
        components/include/ModbusTCP_v5_ResponsePolicy.c
        components/include/ModbusTCP_v5_ResponsePolicyWrapper.c
        components/lib/everparse_error_handler.c
    INCLUDES
        components/include
)

# ModbusParser Component (Isolated EverParse validator - separate address space)
# EverParse validates protocol syntax only. Policy enforcement is in ICS_Inbound.
DeclareCAmkESComponent(
    ModbusParser
    SOURCES
        components/ModbusParser/ModbusParser.c
        components/include/ModbusTCP_v3_Simple.c
        components/include/ModbusTCP_v3_SimpleWrapper.c
        components/lib/everparse_error_handler.c
    INCLUDES
        components/include
)

CAmkESAddImportPath(components/interfaces)

# Declare root server
DeclareCAmkESRootserver(ics_gateway_x86.camkes)

# Generate final bootable image
GenerateCAmkESRootserver()
