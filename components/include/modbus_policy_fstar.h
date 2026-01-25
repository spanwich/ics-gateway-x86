/*
 * Modbus Policy F* - Unified F*-Only Policy Enforcement
 *
 * This module provides a unified interface for Modbus validation using
 * EverParse/F* verified parsers with INTEGRATED address policy enforcement.
 *
 * VERIFICATION ARCHITECTURE:
 *   - EverParse (F*): Verifies BOTH protocol syntax AND address policy
 *   - Single verification framework: End-to-end mathematically proven
 *   - No separate policy layer: Policy is part of the type specification
 *
 * CVE-2022-0367 MITIGATION:
 * The vulnerability exists because libmodbus only validates read_address
 * but not write_address in FC 0x17. The F* specification enforces that
 * BOTH addresses are within the configured range at the TYPE LEVEL.
 *
 * ACADEMIC CLAIM:
 * "First formally verified Modbus TCP parser with integrated address policy
 *  enforcement using EverParse/F* extraction (USENIX Security 2019)"
 *
 * Author: Ford (Saranachon) Iammongkol
 * Date: 2026-01-25
 * SPDX-License-Identifier: BSD-2-Clause
 */

#ifndef MODBUS_POLICY_FSTAR_H
#define MODBUS_POLICY_FSTAR_H

#include <stdint.h>
#include <stdbool.h>

#ifdef __cplusplus
extern "C" {
#endif

/*
 * =============================================================================
 * POLICY CONFIGURATION (Runtime Modifiable)
 * =============================================================================
 *
 * These globals define the allowed address ranges. They are passed to the
 * F* verified parsers at validation time.
 *
 * Default values match the CVE-2022-0367 test case:
 *   - Holding registers: 100-109 (START_REGISTERS=100, NB_REGISTERS=10)
 */

extern uint16_t g_policy_holding_reg_start;
extern uint16_t g_policy_holding_reg_end;
extern uint16_t g_policy_input_reg_start;
extern uint16_t g_policy_input_reg_end;
extern uint16_t g_policy_coil_start;
extern uint16_t g_policy_coil_end;
extern uint16_t g_policy_discrete_input_start;
extern uint16_t g_policy_discrete_input_end;

/*
 * =============================================================================
 * VALIDATION RESULT CODES
 * =============================================================================
 */
#define FSTAR_RESULT_OK              0  /* Validation passed */
#define FSTAR_RESULT_SYNTAX_ERROR    1  /* Protocol syntax error (F* rejected) */
#define FSTAR_RESULT_POLICY_REJECT   2  /* Address policy violation (F* rejected) */
#define FSTAR_RESULT_INVALID_FC      3  /* Function code not in whitelist */
#define FSTAR_RESULT_TOO_SHORT       4  /* Message too short */

/*
 * =============================================================================
 * UNIFIED VALIDATION FUNCTION
 * =============================================================================
 *
 * Validates Modbus TCP message using F* verified parsers.
 * Policy enforcement is INTEGRATED into the F* specification.
 *
 * Parameters:
 *   payload     - Pointer to MBAP + PDU data (starting at Transaction ID)
 *   payload_len - Length of payload in bytes
 *
 * Returns:
 *   FSTAR_RESULT_OK on success, error code otherwise
 *
 * CVE-2022-0367 MITIGATION:
 * For FC 0x17 (Read/Write Multiple Registers), the F* specification
 * validates BOTH read AND write addresses at the type level.
 * This is the exact vulnerability pattern that libmodbus missed.
 */
uint8_t modbus_validate_with_policy(const uint8_t *payload, uint16_t payload_len);

/*
 * =============================================================================
 * POLICY INITIALIZATION FUNCTIONS
 * =============================================================================
 */

/*
 * Initialize policy with permissive defaults (allow all addresses 0-65535)
 */
void fstar_policy_init_permissive(void);

/*
 * Initialize policy for CVE-2022-0367 test case
 * START_REGISTERS = 100, NB_REGISTERS = 10
 */
void fstar_policy_init_cve_test(void);

/*
 * Set custom policy ranges
 */
void fstar_policy_init_custom(
    uint16_t holding_start, uint16_t holding_end,
    uint16_t input_start, uint16_t input_end,
    uint16_t coil_start, uint16_t coil_end,
    uint16_t discrete_start, uint16_t discrete_end
);

#ifdef __cplusplus
}
#endif

#endif /* MODBUS_POLICY_FSTAR_H */
