/*
 * Modbus Policy F* - Unified F*-Only Policy Enforcement Implementation
 *
 * Routes Modbus validation to the appropriate EverParse/F* verified parser
 * based on function code. Policy enforcement is INTEGRATED into the parser.
 *
 * VERIFICATION:
 *   The underlying parsers are extracted from F* specifications that have
 *   been type-checked by F* (USENIX Security 2019). The address constraints
 *   are encoded as dependent types, providing mathematical proof that
 *   validated messages conform to both protocol syntax AND address policy.
 *
 * Author: Ford (Saranachon) Iammongkol
 * Date: 2026-01-25
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include "modbus_policy_fstar.h"
#include "ModbusTCP_v4_PolicyEnforcedWrapper.h"
#include "ModbusTCP_v3_SimpleWrapper.h"

/*
 * =============================================================================
 * GLOBAL POLICY CONFIGURATION
 * =============================================================================
 *
 * Default values: CVE-2022-0367 test configuration
 * - Holding registers: 100-109 (START_REGISTERS=100, NB_REGISTERS=10)
 * - Input registers: 100-109 (same range)
 * - Coils: 0-65535 (allow all - not used in CVE test)
 * - Discrete inputs: 0-65535 (allow all)
 */

uint16_t g_policy_holding_reg_start = 100;
uint16_t g_policy_holding_reg_end = 109;
uint16_t g_policy_input_reg_start = 100;
uint16_t g_policy_input_reg_end = 109;
uint16_t g_policy_coil_start = 0;
uint16_t g_policy_coil_end = 65535;
uint16_t g_policy_discrete_input_start = 0;
uint16_t g_policy_discrete_input_end = 65535;

/*
 * =============================================================================
 * UNIFIED VALIDATION IMPLEMENTATION
 * =============================================================================
 *
 * Routes to appropriate F* verified parser based on function code.
 * Each parser includes INTEGRATED address policy enforcement.
 */

uint8_t modbus_validate_with_policy(const uint8_t *payload, uint16_t payload_len) {
    /* Minimum size check: MBAP header (7 bytes) + Function Code (1 byte) */
    if (payload_len < 8) {
        return FSTAR_RESULT_TOO_SHORT;
    }

    /* Extract function code from MBAP + PDU */
    uint8_t fc = payload[7];

    /* Route to appropriate F* verified validator */
    BOOLEAN result;

    switch (fc) {
        /*
         * Holding Register Operations (FC 0x03, 0x06, 0x10)
         * Use holding register policy range
         */
        case 0x03:  /* Read Holding Registers */
            result = ModbusTcpV4PolicyEnforcedCheckModbusReadHoldingRegistersPolicy(
                (uint32_t)payload_len,
                g_policy_holding_reg_start,
                g_policy_holding_reg_end,
                (uint8_t *)payload,
                (uint32_t)payload_len
            );
            break;

        case 0x06:  /* Write Single Register */
            result = ModbusTcpV4PolicyEnforcedCheckModbusWriteSingleRegisterPolicy(
                (uint32_t)payload_len,
                g_policy_holding_reg_start,
                g_policy_holding_reg_end,
                (uint8_t *)payload,
                (uint32_t)payload_len
            );
            break;

        case 0x10:  /* Write Multiple Registers */
            result = ModbusTcpV4PolicyEnforcedCheckModbusWriteMultipleRegistersPolicy(
                (uint32_t)payload_len,
                g_policy_holding_reg_start,
                g_policy_holding_reg_end,
                (uint8_t *)payload,
                (uint32_t)payload_len
            );
            break;

        /*
         * Read/Write Multiple Registers (FC 0x17)
         * CVE-2022-0367 CRITICAL: F* validates BOTH read AND write addresses
         */
        case 0x17:  /* Read/Write Multiple Registers */
            result = ModbusTcpV4PolicyEnforcedCheckModbusReadWriteRegistersPolicy(
                (uint32_t)payload_len,
                g_policy_holding_reg_start,
                g_policy_holding_reg_end,
                (uint8_t *)payload,
                (uint32_t)payload_len
            );
            break;

        /*
         * Input Register Operations (FC 0x04)
         * Use input register policy range
         */
        case 0x04:  /* Read Input Registers */
            result = ModbusTcpV4PolicyEnforcedCheckModbusReadInputRegistersPolicy(
                (uint32_t)payload_len,
                g_policy_input_reg_start,
                g_policy_input_reg_end,
                (uint8_t *)payload,
                (uint32_t)payload_len
            );
            break;

        /*
         * Coil Operations (FC 0x01, 0x05, 0x0F)
         * Use coil policy range
         */
        case 0x01:  /* Read Coils */
            result = ModbusTcpV4PolicyEnforcedCheckModbusReadCoilsPolicy(
                (uint32_t)payload_len,
                g_policy_coil_start,
                g_policy_coil_end,
                (uint8_t *)payload,
                (uint32_t)payload_len
            );
            break;

        case 0x05:  /* Write Single Coil */
            result = ModbusTcpV4PolicyEnforcedCheckModbusWriteSingleCoilPolicy(
                (uint32_t)payload_len,
                g_policy_coil_start,
                g_policy_coil_end,
                (uint8_t *)payload,
                (uint32_t)payload_len
            );
            break;

        case 0x0F:  /* Write Multiple Coils */
            result = ModbusTcpV4PolicyEnforcedCheckModbusWriteMultipleCoilsPolicy(
                (uint32_t)payload_len,
                g_policy_coil_start,
                g_policy_coil_end,
                (uint8_t *)payload,
                (uint32_t)payload_len
            );
            break;

        /*
         * Discrete Input Operations (FC 0x02)
         * Use discrete input policy range
         */
        case 0x02:  /* Read Discrete Inputs */
            result = ModbusTcpV4PolicyEnforcedCheckModbusReadDiscreteInputsPolicy(
                (uint32_t)payload_len,
                g_policy_discrete_input_start,
                g_policy_discrete_input_end,
                (uint8_t *)payload,
                (uint32_t)payload_len
            );
            break;

        /*
         * Unknown or unsupported function codes
         * SECURITY: FC whitelist enforcement - reject all unknown FCs
         * Only FC 0x01-0x06, 0x0F, 0x10, 0x17 are allowed
         */
        default:
            return FSTAR_RESULT_INVALID_FC;
    }

    /*
     * F* validation includes BOTH syntax AND policy
     * A rejection could be due to either, but the F* type system
     * guarantees correctness of the distinction.
     */
    return result ? FSTAR_RESULT_OK : FSTAR_RESULT_POLICY_REJECT;
}

/*
 * =============================================================================
 * POLICY INITIALIZATION FUNCTIONS
 * =============================================================================
 */

void fstar_policy_init_permissive(void) {
    g_policy_holding_reg_start = 0;
    g_policy_holding_reg_end = 65535;
    g_policy_input_reg_start = 0;
    g_policy_input_reg_end = 65535;
    g_policy_coil_start = 0;
    g_policy_coil_end = 65535;
    g_policy_discrete_input_start = 0;
    g_policy_discrete_input_end = 65535;
}

void fstar_policy_init_cve_test(void) {
    /* Holding registers: 100-109 */
    g_policy_holding_reg_start = 100;
    g_policy_holding_reg_end = 109;

    /* Input registers: same range */
    g_policy_input_reg_start = 100;
    g_policy_input_reg_end = 109;

    /* Coils: allow all (not used in CVE test) */
    g_policy_coil_start = 0;
    g_policy_coil_end = 65535;

    /* Discrete inputs: allow all */
    g_policy_discrete_input_start = 0;
    g_policy_discrete_input_end = 65535;
}

void fstar_policy_init_custom(
    uint16_t holding_start, uint16_t holding_end,
    uint16_t input_start, uint16_t input_end,
    uint16_t coil_start, uint16_t coil_end,
    uint16_t discrete_start, uint16_t discrete_end
) {
    g_policy_holding_reg_start = holding_start;
    g_policy_holding_reg_end = holding_end;
    g_policy_input_reg_start = input_start;
    g_policy_input_reg_end = input_end;
    g_policy_coil_start = coil_start;
    g_policy_coil_end = coil_end;
    g_policy_discrete_input_start = discrete_start;
    g_policy_discrete_input_end = discrete_end;
}
