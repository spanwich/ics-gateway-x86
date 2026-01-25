#include "ModbusTCP_v4_PolicyEnforcedWrapper.h"
#include "EverParse.h"
#include "ModbusTCP_v4_PolicyEnforced.h"
void ModbusTCP_v4_PolicyEnforcedEverParseError(const char *StructName, const char *FieldName, const char *Reason);

static
void DefaultErrorHandler(
	const char *typename_s,
	const char *fieldname,
	const char *reason,
	uint64_t error_code,
	uint8_t *context,
	EVERPARSE_INPUT_BUFFER input,
	uint64_t start_pos)
{
	EVERPARSE_ERROR_FRAME *frame = (EVERPARSE_ERROR_FRAME*)context;
	EverParseDefaultErrorHandler(
		typename_s,
		fieldname,
		reason,
		error_code,
		frame,
		input,
		start_pos
	);
}

BOOLEAN ModbusTcpV4PolicyEnforcedCheckModbusReadHoldingRegistersPolicy(uint32_t ___InputLength, uint16_t ___AllowedStart, uint16_t ___AllowedEnd, uint8_t *base, uint32_t len) {
	EVERPARSE_ERROR_FRAME frame;
	frame.filled = FALSE;
	uint64_t result = ModbusTcpV4PolicyEnforcedValidateModbusReadHoldingRegistersPolicy(___InputLength, ___AllowedStart, ___AllowedEnd,  (uint8_t*)&frame, &DefaultErrorHandler, base, len, 0);
	if (EverParseIsError(result))
	{
		if (frame.filled)
		{
			ModbusTCP_v4_PolicyEnforcedEverParseError(frame.typename_s, frame.fieldname, frame.reason);
		}
		return FALSE;
	}
	return TRUE;
}

BOOLEAN ModbusTcpV4PolicyEnforcedCheckModbusWriteSingleRegisterPolicy(uint32_t ___InputLength, uint16_t ___AllowedStart, uint16_t ___AllowedEnd, uint8_t *base, uint32_t len) {
	EVERPARSE_ERROR_FRAME frame;
	frame.filled = FALSE;
	uint64_t result = ModbusTcpV4PolicyEnforcedValidateModbusWriteSingleRegisterPolicy(___InputLength, ___AllowedStart, ___AllowedEnd,  (uint8_t*)&frame, &DefaultErrorHandler, base, len, 0);
	if (EverParseIsError(result))
	{
		if (frame.filled)
		{
			ModbusTCP_v4_PolicyEnforcedEverParseError(frame.typename_s, frame.fieldname, frame.reason);
		}
		return FALSE;
	}
	return TRUE;
}

BOOLEAN ModbusTcpV4PolicyEnforcedCheckModbusWriteMultipleRegistersPolicy(uint32_t ___InputLength, uint16_t ___AllowedStart, uint16_t ___AllowedEnd, uint8_t *base, uint32_t len) {
	EVERPARSE_ERROR_FRAME frame;
	frame.filled = FALSE;
	uint64_t result = ModbusTcpV4PolicyEnforcedValidateModbusWriteMultipleRegistersPolicy(___InputLength, ___AllowedStart, ___AllowedEnd,  (uint8_t*)&frame, &DefaultErrorHandler, base, len, 0);
	if (EverParseIsError(result))
	{
		if (frame.filled)
		{
			ModbusTCP_v4_PolicyEnforcedEverParseError(frame.typename_s, frame.fieldname, frame.reason);
		}
		return FALSE;
	}
	return TRUE;
}

BOOLEAN ModbusTcpV4PolicyEnforcedCheckModbusReadWriteRegistersPolicy(uint32_t ___InputLength, uint16_t ___AllowedStart, uint16_t ___AllowedEnd, uint8_t *base, uint32_t len) {
	EVERPARSE_ERROR_FRAME frame;
	frame.filled = FALSE;
	uint64_t result = ModbusTcpV4PolicyEnforcedValidateModbusReadWriteRegistersPolicy(___InputLength, ___AllowedStart, ___AllowedEnd,  (uint8_t*)&frame, &DefaultErrorHandler, base, len, 0);
	if (EverParseIsError(result))
	{
		if (frame.filled)
		{
			ModbusTCP_v4_PolicyEnforcedEverParseError(frame.typename_s, frame.fieldname, frame.reason);
		}
		return FALSE;
	}
	return TRUE;
}

BOOLEAN ModbusTcpV4PolicyEnforcedCheckModbusReadCoilsPolicy(uint32_t ___InputLength, uint16_t ___AllowedStart, uint16_t ___AllowedEnd, uint8_t *base, uint32_t len) {
	EVERPARSE_ERROR_FRAME frame;
	frame.filled = FALSE;
	uint64_t result = ModbusTcpV4PolicyEnforcedValidateModbusReadCoilsPolicy(___InputLength, ___AllowedStart, ___AllowedEnd,  (uint8_t*)&frame, &DefaultErrorHandler, base, len, 0);
	if (EverParseIsError(result))
	{
		if (frame.filled)
		{
			ModbusTCP_v4_PolicyEnforcedEverParseError(frame.typename_s, frame.fieldname, frame.reason);
		}
		return FALSE;
	}
	return TRUE;
}

BOOLEAN ModbusTcpV4PolicyEnforcedCheckModbusWriteSingleCoilPolicy(uint32_t ___InputLength, uint16_t ___AllowedStart, uint16_t ___AllowedEnd, uint8_t *base, uint32_t len) {
	EVERPARSE_ERROR_FRAME frame;
	frame.filled = FALSE;
	uint64_t result = ModbusTcpV4PolicyEnforcedValidateModbusWriteSingleCoilPolicy(___InputLength, ___AllowedStart, ___AllowedEnd,  (uint8_t*)&frame, &DefaultErrorHandler, base, len, 0);
	if (EverParseIsError(result))
	{
		if (frame.filled)
		{
			ModbusTCP_v4_PolicyEnforcedEverParseError(frame.typename_s, frame.fieldname, frame.reason);
		}
		return FALSE;
	}
	return TRUE;
}

BOOLEAN ModbusTcpV4PolicyEnforcedCheckModbusWriteMultipleCoilsPolicy(uint32_t ___InputLength, uint16_t ___AllowedStart, uint16_t ___AllowedEnd, uint8_t *base, uint32_t len) {
	EVERPARSE_ERROR_FRAME frame;
	frame.filled = FALSE;
	uint64_t result = ModbusTcpV4PolicyEnforcedValidateModbusWriteMultipleCoilsPolicy(___InputLength, ___AllowedStart, ___AllowedEnd,  (uint8_t*)&frame, &DefaultErrorHandler, base, len, 0);
	if (EverParseIsError(result))
	{
		if (frame.filled)
		{
			ModbusTCP_v4_PolicyEnforcedEverParseError(frame.typename_s, frame.fieldname, frame.reason);
		}
		return FALSE;
	}
	return TRUE;
}

BOOLEAN ModbusTcpV4PolicyEnforcedCheckModbusReadDiscreteInputsPolicy(uint32_t ___InputLength, uint16_t ___AllowedStart, uint16_t ___AllowedEnd, uint8_t *base, uint32_t len) {
	EVERPARSE_ERROR_FRAME frame;
	frame.filled = FALSE;
	uint64_t result = ModbusTcpV4PolicyEnforcedValidateModbusReadDiscreteInputsPolicy(___InputLength, ___AllowedStart, ___AllowedEnd,  (uint8_t*)&frame, &DefaultErrorHandler, base, len, 0);
	if (EverParseIsError(result))
	{
		if (frame.filled)
		{
			ModbusTCP_v4_PolicyEnforcedEverParseError(frame.typename_s, frame.fieldname, frame.reason);
		}
		return FALSE;
	}
	return TRUE;
}

BOOLEAN ModbusTcpV4PolicyEnforcedCheckModbusReadInputRegistersPolicy(uint32_t ___InputLength, uint16_t ___AllowedStart, uint16_t ___AllowedEnd, uint8_t *base, uint32_t len) {
	EVERPARSE_ERROR_FRAME frame;
	frame.filled = FALSE;
	uint64_t result = ModbusTcpV4PolicyEnforcedValidateModbusReadInputRegistersPolicy(___InputLength, ___AllowedStart, ___AllowedEnd,  (uint8_t*)&frame, &DefaultErrorHandler, base, len, 0);
	if (EverParseIsError(result))
	{
		if (frame.filled)
		{
			ModbusTCP_v4_PolicyEnforcedEverParseError(frame.typename_s, frame.fieldname, frame.reason);
		}
		return FALSE;
	}
	return TRUE;
}
