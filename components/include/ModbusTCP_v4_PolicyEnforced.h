

#ifndef ModbusTCP_v4_PolicyEnforced_H
#define ModbusTCP_v4_PolicyEnforced_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "EverParse.h"

#define MODBUSTCP_V4_POLICYENFORCED____MODBUS_PROTOCOL_ID (0U)

#define MODBUSTCP_V4_POLICYENFORCED____MBAP_HEADER_PREFIX_SIZE (6U)

#define MODBUSTCP_V4_POLICYENFORCED____FC_READ_COILS (0x01U)

#define MODBUSTCP_V4_POLICYENFORCED____FC_READ_DISCRETE_INPUTS (0x02U)

#define MODBUSTCP_V4_POLICYENFORCED____FC_READ_HOLDING_REGISTERS (0x03U)

#define MODBUSTCP_V4_POLICYENFORCED____FC_READ_INPUT_REGISTERS (0x04U)

#define MODBUSTCP_V4_POLICYENFORCED____FC_WRITE_SINGLE_COIL (0x05U)

#define MODBUSTCP_V4_POLICYENFORCED____FC_WRITE_SINGLE_REGISTER (0x06U)

#define MODBUSTCP_V4_POLICYENFORCED____FC_WRITE_MULTIPLE_COILS (0x0FU)

#define MODBUSTCP_V4_POLICYENFORCED____FC_WRITE_MULTIPLE_REGISTERS (0x10U)

#define MODBUSTCP_V4_POLICYENFORCED____FC_READ_WRITE_MULTIPLE_REGISTERS (0x17U)

#define MODBUSTCP_V4_POLICYENFORCED____COIL_ON (0xFF00U)

#define MODBUSTCP_V4_POLICYENFORCED____COIL_OFF (0x0000U)

#define MODBUSTCP_V4_POLICYENFORCED____MAX_READ_COILS (2000U)

#define MODBUSTCP_V4_POLICYENFORCED____MAX_READ_DISCRETE_INPUTS (2000U)

#define MODBUSTCP_V4_POLICYENFORCED____MAX_READ_REGISTERS (125U)

#define MODBUSTCP_V4_POLICYENFORCED____MAX_WRITE_COILS (1968U)

#define MODBUSTCP_V4_POLICYENFORCED____MAX_WRITE_REGISTERS (123U)

#define MODBUSTCP_V4_POLICYENFORCED____MAX_RW_READ_REGISTERS (125U)

#define MODBUSTCP_V4_POLICYENFORCED____MAX_RW_WRITE_REGISTERS (121U)

uint64_t
ModbusTcpV4PolicyEnforcedValidateModbusReadHoldingRegistersPolicy(
  uint32_t InputLength,
  uint16_t AllowedStart,
  uint16_t AllowedEnd,
  uint8_t *Ctxt,
  void
  (*ErrorHandlerFn)(
    EVERPARSE_STRING x0,
    EVERPARSE_STRING x1,
    EVERPARSE_STRING x2,
    uint64_t x3,
    uint8_t *x4,
    uint8_t *x5,
    uint64_t x6
  ),
  uint8_t *Input,
  uint64_t InputLength0,
  uint64_t StartPosition
);

uint64_t
ModbusTcpV4PolicyEnforcedValidateModbusWriteSingleRegisterPolicy(
  uint32_t InputLength,
  uint16_t AllowedStart,
  uint16_t AllowedEnd,
  uint8_t *Ctxt,
  void
  (*ErrorHandlerFn)(
    EVERPARSE_STRING x0,
    EVERPARSE_STRING x1,
    EVERPARSE_STRING x2,
    uint64_t x3,
    uint8_t *x4,
    uint8_t *x5,
    uint64_t x6
  ),
  uint8_t *Input,
  uint64_t InputLength0,
  uint64_t StartPosition
);

uint64_t
ModbusTcpV4PolicyEnforcedValidateModbusWriteMultipleRegistersPolicy(
  uint32_t InputLength,
  uint16_t AllowedStart,
  uint16_t AllowedEnd,
  uint8_t *Ctxt,
  void
  (*ErrorHandlerFn)(
    EVERPARSE_STRING x0,
    EVERPARSE_STRING x1,
    EVERPARSE_STRING x2,
    uint64_t x3,
    uint8_t *x4,
    uint8_t *x5,
    uint64_t x6
  ),
  uint8_t *Input,
  uint64_t InputLength0,
  uint64_t StartPosition
);

uint64_t
ModbusTcpV4PolicyEnforcedValidateModbusReadWriteRegistersPolicy(
  uint32_t InputLength,
  uint16_t AllowedStart,
  uint16_t AllowedEnd,
  uint8_t *Ctxt,
  void
  (*ErrorHandlerFn)(
    EVERPARSE_STRING x0,
    EVERPARSE_STRING x1,
    EVERPARSE_STRING x2,
    uint64_t x3,
    uint8_t *x4,
    uint8_t *x5,
    uint64_t x6
  ),
  uint8_t *Input,
  uint64_t InputLength0,
  uint64_t StartPosition
);

uint64_t
ModbusTcpV4PolicyEnforcedValidateModbusReadCoilsPolicy(
  uint32_t InputLength,
  uint16_t AllowedStart,
  uint16_t AllowedEnd,
  uint8_t *Ctxt,
  void
  (*ErrorHandlerFn)(
    EVERPARSE_STRING x0,
    EVERPARSE_STRING x1,
    EVERPARSE_STRING x2,
    uint64_t x3,
    uint8_t *x4,
    uint8_t *x5,
    uint64_t x6
  ),
  uint8_t *Input,
  uint64_t InputLength0,
  uint64_t StartPosition
);

uint64_t
ModbusTcpV4PolicyEnforcedValidateModbusWriteSingleCoilPolicy(
  uint32_t InputLength,
  uint16_t AllowedStart,
  uint16_t AllowedEnd,
  uint8_t *Ctxt,
  void
  (*ErrorHandlerFn)(
    EVERPARSE_STRING x0,
    EVERPARSE_STRING x1,
    EVERPARSE_STRING x2,
    uint64_t x3,
    uint8_t *x4,
    uint8_t *x5,
    uint64_t x6
  ),
  uint8_t *Input,
  uint64_t InputLength0,
  uint64_t StartPosition
);

uint64_t
ModbusTcpV4PolicyEnforcedValidateModbusWriteMultipleCoilsPolicy(
  uint32_t InputLength,
  uint16_t AllowedStart,
  uint16_t AllowedEnd,
  uint8_t *Ctxt,
  void
  (*ErrorHandlerFn)(
    EVERPARSE_STRING x0,
    EVERPARSE_STRING x1,
    EVERPARSE_STRING x2,
    uint64_t x3,
    uint8_t *x4,
    uint8_t *x5,
    uint64_t x6
  ),
  uint8_t *Input,
  uint64_t InputLength0,
  uint64_t StartPosition
);

uint64_t
ModbusTcpV4PolicyEnforcedValidateModbusReadDiscreteInputsPolicy(
  uint32_t InputLength,
  uint16_t AllowedStart,
  uint16_t AllowedEnd,
  uint8_t *Ctxt,
  void
  (*ErrorHandlerFn)(
    EVERPARSE_STRING x0,
    EVERPARSE_STRING x1,
    EVERPARSE_STRING x2,
    uint64_t x3,
    uint8_t *x4,
    uint8_t *x5,
    uint64_t x6
  ),
  uint8_t *Input,
  uint64_t InputLength0,
  uint64_t StartPosition
);

uint64_t
ModbusTcpV4PolicyEnforcedValidateModbusReadInputRegistersPolicy(
  uint32_t InputLength,
  uint16_t AllowedStart,
  uint16_t AllowedEnd,
  uint8_t *Ctxt,
  void
  (*ErrorHandlerFn)(
    EVERPARSE_STRING x0,
    EVERPARSE_STRING x1,
    EVERPARSE_STRING x2,
    uint64_t x3,
    uint8_t *x4,
    uint8_t *x5,
    uint64_t x6
  ),
  uint8_t *Input,
  uint64_t InputLength0,
  uint64_t StartPosition
);

#if defined(__cplusplus)
}
#endif

#define ModbusTCP_v4_PolicyEnforced_H_DEFINED
#endif /* ModbusTCP_v4_PolicyEnforced_H */
