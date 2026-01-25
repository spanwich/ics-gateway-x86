/*
 * EverParse Error Handler Implementation
 *
 * Integrates EverParse validation errors with gateway's logging system.
 * Uses debug_levels.h DEBUG_ERROR macro for consistent error reporting.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#define DEBUG_LEVEL DEBUG_LEVEL_INFO
#include "debug_levels.h"
#include "everparse_error_handler.h"

/*
 * Implementation of error callback required by ModbusTCP_v3_SimpleWrapper
 *
 * This function is called whenever EverParse detects a validation failure.
 * We log the error using the gateway's standard DEBUG_ERROR mechanism.
 */
void ModbusTCP_v3_SimpleEverParseError(const char *StructName,
                                        const char *FieldName,
                                        const char *Reason)
{
    DEBUG_ERROR("EverParse validation failed:\n");
    DEBUG_ERROR("  Structure: %s\n", StructName ? StructName : "(unknown)");
    DEBUG_ERROR("  Field: %s\n", FieldName ? FieldName : "(unknown)");
    DEBUG_ERROR("  Reason: %s\n", Reason ? Reason : "(no reason provided)");
}

/* Alias for backward compatibility if old code references the Simple version */
void ModbusTCP_SimpleEverParseError(const char *StructName,
                                     const char *FieldName,
                                     const char *Reason)
{
    ModbusTCP_v3_SimpleEverParseError(StructName, FieldName, Reason);
}

/*
 * v2.290: Error handler for v4 policy-enforced parser
 *
 * This function is called when the F* verified parser detects:
 *   1. Protocol syntax errors (invalid field values, wrong lengths)
 *   2. Policy violations (address out of range, quantity overflow)
 *
 * Both types of errors are handled by the same verified code path,
 * demonstrating F*'s unified verification approach.
 */
void ModbusTCP_v4_PolicyEnforcedEverParseError(const char *StructName,
                                                const char *FieldName,
                                                const char *Reason)
{
    DEBUG_ERROR("F* Policy Validation Failed:\n");
    DEBUG_ERROR("  Structure: %s\n", StructName ? StructName : "(unknown)");
    DEBUG_ERROR("  Field: %s\n", FieldName ? FieldName : "(unknown)");
    DEBUG_ERROR("  Reason: %s\n", Reason ? Reason : "(no reason provided)");
}
