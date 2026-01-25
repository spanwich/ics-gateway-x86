/*
 * ModbusParser - Isolated EverParse Validation Component
 *
 * UNIFIED VERSION: Works for both production (CAmkES) and verification (Frama-C)
 *
 * Production build:
 *   Compiled by CAmkES build system (no special flags)
 *
 * Verification build:
 *   frama-c -wp -wp-rte ModbusParser.c \
 *     -cpp-extra-args="-DFRAMA_C_VERIFICATION" \
 *     -wp-prover alt-ergo
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

/* ============================================================================
 * CONDITIONAL INCLUDES
 * ============================================================================ */

#ifdef FRAMA_C_VERIFICATION
/*
 * VERIFICATION MODE: Use stubs instead of CAmkES headers
 */
#include <stdint.h>
#include <stddef.h>

typedef unsigned long seL4_Word;
typedef int BOOLEAN;
#define TRUE 1
#define FALSE 0

/* Verification buffer model */
#define BUFFER_SIZE 4096
static uint8_t shared_buffer[BUFFER_SIZE];
static int buffer_valid = 0;

/*@
  assigns \nothing;
  ensures buffer_valid != 0 ==> \result == shared_buffer;
  ensures buffer_valid == 0 ==> \result == \null;
*/
uint8_t *parser_buf(seL4_Word badge) {
    if (buffer_valid) {
        return shared_buffer;
    }
    return (uint8_t *)0;
}

/*@
  assigns \nothing;
  ensures \result >= 0;
*/
seL4_Word parser_get_sender_id(void) {
    return 0;
}

/*@
  requires len >= 8 && len <= 260;
  requires input_len == len;
  requires \valid_read(base + (0..len-1));
  assigns \nothing;
  ensures \result == TRUE || \result == FALSE;
*/
extern BOOLEAN ModbusTcpV3SimpleCheckModbusTcpFrameV3(
    uint32_t input_len,
    uint8_t *base,
    uint32_t len);

#define DEBUG_INFO(...) ((void)0)

#else
/*
 * PRODUCTION MODE: Use real CAmkES headers
 */
#define DEBUG_LEVEL DEBUG_LEVEL_INFO
#include "debug_levels.h"

#include <camkes.h>
#include <string.h>
#include <stdint.h>
#include "ModbusTCP_v3_SimpleWrapper.h"

/* CAmkES generates this function but doesn't declare it in the header */
extern seL4_Word parser_get_sender_id(void);

#endif /* FRAMA_C_VERIFICATION */

/* ============================================================================
 * SHARED CONSTANTS (used by both modes)
 * ============================================================================ */

#define MODBUS_MAX_FRAME_SIZE 260
#define MODBUS_MIN_FRAME_SIZE 8

/* ============================================================================
 * MAIN VALIDATION FUNCTION
 * ============================================================================ */

/*@
  assigns \nothing;

  behavior invalid_length:
    assumes payload_length < 8 || payload_length > 260;
    ensures \result == -1;

  behavior valid_length:
    assumes payload_length >= 8 && payload_length <= 260;
    ensures \result == -1 || \result == 0 || \result == 1;

  complete behaviors;
  disjoint behaviors;
*/
int parser_validate(int payload_length) {
    /* Step 1: Bounds check */
    if (payload_length < MODBUS_MIN_FRAME_SIZE ||
        payload_length > MODBUS_MAX_FRAME_SIZE) {
        return -1;
    }

    /* Step 2: Get buffer */
    seL4_Word badge = parser_get_sender_id();

#ifdef FRAMA_C_VERIFICATION
    uint8_t *buf = parser_buf(badge);
#else
    uint8_t *buf = (uint8_t *)parser_get_buf();
#endif

    /* Step 3: Null check */
    if (buf == (uint8_t *)0) {
        return -1;
    }

    /* Step 4: Call EverParse */
    uint32_t input_length = (uint32_t)payload_length;

    BOOLEAN result = ModbusTcpV3SimpleCheckModbusTcpFrameV3(
        input_length, buf, input_length);

    return result ? 1 : 0;
}

/* ============================================================================
 * ENTRY POINT (Production only)
 * ============================================================================ */

#ifndef FRAMA_C_VERIFICATION
int run(void) {
    DEBUG_INFO("ModbusParser: Isolated EverParse validator ready\n");
    /* CAmkES RPC server loop handles dispatch automatically */
    return 0;
}
#else
int run(void) {
    return 0;
}
#endif
