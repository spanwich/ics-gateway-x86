

#include "ModbusTCP_v4_PolicyEnforced.h"

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
)
{
  /* Validating field TransactionId */
  /* Checking that we have enough space for a UINT16BE, i.e., 2 bytes */
  BOOLEAN hasBytes0 = 2ULL <= (InputLength0 - StartPosition);
  uint64_t positionAfterModbusReadHoldingRegistersPolicy;
  if (hasBytes0)
  {
    positionAfterModbusReadHoldingRegistersPolicy = StartPosition + 2ULL;
  }
  else
  {
    positionAfterModbusReadHoldingRegistersPolicy =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  uint64_t res0;
  if (EverParseIsSuccess(positionAfterModbusReadHoldingRegistersPolicy))
  {
    res0 = positionAfterModbusReadHoldingRegistersPolicy;
  }
  else
  {
    ErrorHandlerFn("_MODBUS_READ_HOLDING_REGISTERS_POLICY",
      "TransactionId",
      EverParseErrorReasonOfResult(positionAfterModbusReadHoldingRegistersPolicy),
      EverParseGetValidatorErrorKind(positionAfterModbusReadHoldingRegistersPolicy),
      Ctxt,
      Input,
      StartPosition);
    res0 = positionAfterModbusReadHoldingRegistersPolicy;
  }
  uint64_t positionAfterTransactionId = res0;
  if (EverParseIsError(positionAfterTransactionId))
  {
    return positionAfterTransactionId;
  }
  /* Checking that we have enough space for a UINT16BE, i.e., 2 bytes */
  BOOLEAN hasBytes1 = 2ULL <= (InputLength0 - positionAfterTransactionId);
  uint64_t positionAfterProtocolId;
  if (hasBytes1)
  {
    positionAfterProtocolId = positionAfterTransactionId + 2ULL;
  }
  else
  {
    positionAfterProtocolId =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        positionAfterTransactionId);
  }
  uint64_t positionAfterModbusReadHoldingRegistersPolicy0;
  if (EverParseIsError(positionAfterProtocolId))
  {
    positionAfterModbusReadHoldingRegistersPolicy0 = positionAfterProtocolId;
  }
  else
  {
    uint16_t protocolId = Load16Be(Input + (uint32_t)positionAfterTransactionId);
    BOOLEAN
    protocolIdConstraintIsOk =
      protocolId == (uint16_t)MODBUSTCP_V4_POLICYENFORCED____MODBUS_PROTOCOL_ID;
    uint64_t
    positionAfterProtocolId1 =
      EverParseCheckConstraintOk(protocolIdConstraintIsOk,
        positionAfterProtocolId);
    if (EverParseIsError(positionAfterProtocolId1))
    {
      positionAfterModbusReadHoldingRegistersPolicy0 = positionAfterProtocolId1;
    }
    else
    {
      /* Checking that we have enough space for a UINT16BE, i.e., 2 bytes */
      BOOLEAN hasBytes2 = 2ULL <= (InputLength0 - positionAfterProtocolId1);
      uint64_t positionAfterLength;
      if (hasBytes2)
      {
        positionAfterLength = positionAfterProtocolId1 + 2ULL;
      }
      else
      {
        positionAfterLength =
          EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
            positionAfterProtocolId1);
      }
      uint64_t positionAfterModbusReadHoldingRegistersPolicy1;
      if (EverParseIsError(positionAfterLength))
      {
        positionAfterModbusReadHoldingRegistersPolicy1 = positionAfterLength;
      }
      else
      {
        uint16_t length = Load16Be(Input + (uint32_t)positionAfterProtocolId1);
        BOOLEAN
        lengthConstraintIsOk =
          length == (uint16_t)6U &&
            InputLength ==
              (uint32_t)((uint32_t)length +
                (uint32_t)(uint16_t)MODBUSTCP_V4_POLICYENFORCED____MBAP_HEADER_PREFIX_SIZE);
        uint64_t
        positionAfterLength1 = EverParseCheckConstraintOk(lengthConstraintIsOk, positionAfterLength);
        if (EverParseIsError(positionAfterLength1))
        {
          positionAfterModbusReadHoldingRegistersPolicy1 = positionAfterLength1;
        }
        else
        {
          /* Validating field UnitId */
          /* Checking that we have enough space for a UINT8, i.e., 1 byte */
          BOOLEAN hasBytes3 = 1ULL <= (InputLength0 - positionAfterLength1);
          uint64_t positionAfterModbusReadHoldingRegistersPolicy2;
          if (hasBytes3)
          {
            positionAfterModbusReadHoldingRegistersPolicy2 = positionAfterLength1 + 1ULL;
          }
          else
          {
            positionAfterModbusReadHoldingRegistersPolicy2 =
              EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
                positionAfterLength1);
          }
          uint64_t res;
          if (EverParseIsSuccess(positionAfterModbusReadHoldingRegistersPolicy2))
          {
            res = positionAfterModbusReadHoldingRegistersPolicy2;
          }
          else
          {
            ErrorHandlerFn("_MODBUS_READ_HOLDING_REGISTERS_POLICY",
              "UnitId",
              EverParseErrorReasonOfResult(positionAfterModbusReadHoldingRegistersPolicy2),
              EverParseGetValidatorErrorKind(positionAfterModbusReadHoldingRegistersPolicy2),
              Ctxt,
              Input,
              positionAfterLength1);
            res = positionAfterModbusReadHoldingRegistersPolicy2;
          }
          uint64_t positionAfterUnitId = res;
          if (EverParseIsError(positionAfterUnitId))
          {
            positionAfterModbusReadHoldingRegistersPolicy1 = positionAfterUnitId;
          }
          else
          {
            /* Checking that we have enough space for a UINT8, i.e., 1 byte */
            BOOLEAN hasBytes4 = 1ULL <= (InputLength0 - positionAfterUnitId);
            uint64_t positionAfterFunctionCode;
            if (hasBytes4)
            {
              positionAfterFunctionCode = positionAfterUnitId + 1ULL;
            }
            else
            {
              positionAfterFunctionCode =
                EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
                  positionAfterUnitId);
            }
            uint64_t positionAfterModbusReadHoldingRegistersPolicy3;
            if (EverParseIsError(positionAfterFunctionCode))
            {
              positionAfterModbusReadHoldingRegistersPolicy3 = positionAfterFunctionCode;
            }
            else
            {
              uint8_t functionCode = Input[(uint32_t)positionAfterUnitId];
              BOOLEAN
              functionCodeConstraintIsOk =
                functionCode == MODBUSTCP_V4_POLICYENFORCED____FC_READ_HOLDING_REGISTERS;
              uint64_t
              positionAfterFunctionCode1 =
                EverParseCheckConstraintOk(functionCodeConstraintIsOk,
                  positionAfterFunctionCode);
              if (EverParseIsError(positionAfterFunctionCode1))
              {
                positionAfterModbusReadHoldingRegistersPolicy3 = positionAfterFunctionCode1;
              }
              else
              {
                /* Checking that we have enough space for a UINT16BE, i.e., 2 bytes */
                BOOLEAN hasBytes5 = 2ULL <= (InputLength0 - positionAfterFunctionCode1);
                uint64_t positionAfterStartAddress;
                if (hasBytes5)
                {
                  positionAfterStartAddress = positionAfterFunctionCode1 + 2ULL;
                }
                else
                {
                  positionAfterStartAddress =
                    EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
                      positionAfterFunctionCode1);
                }
                uint64_t positionAfterModbusReadHoldingRegistersPolicy4;
                if (EverParseIsError(positionAfterStartAddress))
                {
                  positionAfterModbusReadHoldingRegistersPolicy4 = positionAfterStartAddress;
                }
                else
                {
                  uint16_t startAddress = Load16Be(Input + (uint32_t)positionAfterFunctionCode1);
                  BOOLEAN
                  startAddressConstraintIsOk =
                    startAddress >= AllowedStart && startAddress <= AllowedEnd;
                  uint64_t
                  positionAfterStartAddress1 =
                    EverParseCheckConstraintOk(startAddressConstraintIsOk,
                      positionAfterStartAddress);
                  if (EverParseIsError(positionAfterStartAddress1))
                  {
                    positionAfterModbusReadHoldingRegistersPolicy4 = positionAfterStartAddress1;
                  }
                  else
                  {
                    /* Validating field Quantity */
                    /* Checking that we have enough space for a UINT16BE, i.e., 2 bytes */
                    BOOLEAN hasBytes = 2ULL <= (InputLength0 - positionAfterStartAddress1);
                    uint64_t positionAfterQuantity_refinement;
                    if (hasBytes)
                    {
                      positionAfterQuantity_refinement = positionAfterStartAddress1 + 2ULL;
                    }
                    else
                    {
                      positionAfterQuantity_refinement =
                        EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
                          positionAfterStartAddress1);
                    }
                    uint64_t positionAfterModbusReadHoldingRegistersPolicy5;
                    if (EverParseIsError(positionAfterQuantity_refinement))
                    {
                      positionAfterModbusReadHoldingRegistersPolicy5 =
                        positionAfterQuantity_refinement;
                    }
                    else
                    {
                      /* reading field_value */
                      uint16_t
                      quantity_refinement = Load16Be(Input + (uint32_t)positionAfterStartAddress1);
                      /* start: checking constraint */
                      BOOLEAN
                      quantity_refinementConstraintIsOk =
                        quantity_refinement >= (uint16_t)1U &&
                          quantity_refinement <=
                            (uint16_t)MODBUSTCP_V4_POLICYENFORCED____MAX_READ_REGISTERS
                        &&
                          ((uint32_t)quantity_refinement - (uint32_t)(uint16_t)1U) <=
                            ((uint32_t)AllowedEnd - (uint32_t)startAddress);
                      /* end: checking constraint */
                      positionAfterModbusReadHoldingRegistersPolicy5 =
                        EverParseCheckConstraintOk(quantity_refinementConstraintIsOk,
                          positionAfterQuantity_refinement);
                    }
                    if (EverParseIsSuccess(positionAfterModbusReadHoldingRegistersPolicy5))
                    {
                      positionAfterModbusReadHoldingRegistersPolicy4 =
                        positionAfterModbusReadHoldingRegistersPolicy5;
                    }
                    else
                    {
                      ErrorHandlerFn("_MODBUS_READ_HOLDING_REGISTERS_POLICY",
                        "Quantity.refinement",
                        EverParseErrorReasonOfResult(positionAfterModbusReadHoldingRegistersPolicy5),
                        EverParseGetValidatorErrorKind(positionAfterModbusReadHoldingRegistersPolicy5),
                        Ctxt,
                        Input,
                        positionAfterStartAddress1);
                      positionAfterModbusReadHoldingRegistersPolicy4 =
                        positionAfterModbusReadHoldingRegistersPolicy5;
                    }
                  }
                }
                if (EverParseIsSuccess(positionAfterModbusReadHoldingRegistersPolicy4))
                {
                  positionAfterModbusReadHoldingRegistersPolicy3 =
                    positionAfterModbusReadHoldingRegistersPolicy4;
                }
                else
                {
                  ErrorHandlerFn("_MODBUS_READ_HOLDING_REGISTERS_POLICY",
                    "StartAddress",
                    EverParseErrorReasonOfResult(positionAfterModbusReadHoldingRegistersPolicy4),
                    EverParseGetValidatorErrorKind(positionAfterModbusReadHoldingRegistersPolicy4),
                    Ctxt,
                    Input,
                    positionAfterFunctionCode1);
                  positionAfterModbusReadHoldingRegistersPolicy3 =
                    positionAfterModbusReadHoldingRegistersPolicy4;
                }
              }
            }
            if (EverParseIsSuccess(positionAfterModbusReadHoldingRegistersPolicy3))
            {
              positionAfterModbusReadHoldingRegistersPolicy1 =
                positionAfterModbusReadHoldingRegistersPolicy3;
            }
            else
            {
              ErrorHandlerFn("_MODBUS_READ_HOLDING_REGISTERS_POLICY",
                "FunctionCode",
                EverParseErrorReasonOfResult(positionAfterModbusReadHoldingRegistersPolicy3),
                EverParseGetValidatorErrorKind(positionAfterModbusReadHoldingRegistersPolicy3),
                Ctxt,
                Input,
                positionAfterUnitId);
              positionAfterModbusReadHoldingRegistersPolicy1 =
                positionAfterModbusReadHoldingRegistersPolicy3;
            }
          }
        }
      }
      if (EverParseIsSuccess(positionAfterModbusReadHoldingRegistersPolicy1))
      {
        positionAfterModbusReadHoldingRegistersPolicy0 =
          positionAfterModbusReadHoldingRegistersPolicy1;
      }
      else
      {
        ErrorHandlerFn("_MODBUS_READ_HOLDING_REGISTERS_POLICY",
          "Length",
          EverParseErrorReasonOfResult(positionAfterModbusReadHoldingRegistersPolicy1),
          EverParseGetValidatorErrorKind(positionAfterModbusReadHoldingRegistersPolicy1),
          Ctxt,
          Input,
          positionAfterProtocolId1);
        positionAfterModbusReadHoldingRegistersPolicy0 =
          positionAfterModbusReadHoldingRegistersPolicy1;
      }
    }
  }
  if (EverParseIsSuccess(positionAfterModbusReadHoldingRegistersPolicy0))
  {
    return positionAfterModbusReadHoldingRegistersPolicy0;
  }
  ErrorHandlerFn("_MODBUS_READ_HOLDING_REGISTERS_POLICY",
    "ProtocolId",
    EverParseErrorReasonOfResult(positionAfterModbusReadHoldingRegistersPolicy0),
    EverParseGetValidatorErrorKind(positionAfterModbusReadHoldingRegistersPolicy0),
    Ctxt,
    Input,
    positionAfterTransactionId);
  return positionAfterModbusReadHoldingRegistersPolicy0;
}

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
)
{
  /* Validating field TransactionId */
  /* Checking that we have enough space for a UINT16BE, i.e., 2 bytes */
  BOOLEAN hasBytes0 = 2ULL <= (InputLength0 - StartPosition);
  uint64_t positionAfterModbusWriteSingleRegisterPolicy;
  if (hasBytes0)
  {
    positionAfterModbusWriteSingleRegisterPolicy = StartPosition + 2ULL;
  }
  else
  {
    positionAfterModbusWriteSingleRegisterPolicy =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  uint64_t res0;
  if (EverParseIsSuccess(positionAfterModbusWriteSingleRegisterPolicy))
  {
    res0 = positionAfterModbusWriteSingleRegisterPolicy;
  }
  else
  {
    ErrorHandlerFn("_MODBUS_WRITE_SINGLE_REGISTER_POLICY",
      "TransactionId",
      EverParseErrorReasonOfResult(positionAfterModbusWriteSingleRegisterPolicy),
      EverParseGetValidatorErrorKind(positionAfterModbusWriteSingleRegisterPolicy),
      Ctxt,
      Input,
      StartPosition);
    res0 = positionAfterModbusWriteSingleRegisterPolicy;
  }
  uint64_t positionAfterTransactionId = res0;
  if (EverParseIsError(positionAfterTransactionId))
  {
    return positionAfterTransactionId;
  }
  /* Checking that we have enough space for a UINT16BE, i.e., 2 bytes */
  BOOLEAN hasBytes1 = 2ULL <= (InputLength0 - positionAfterTransactionId);
  uint64_t positionAfterProtocolId;
  if (hasBytes1)
  {
    positionAfterProtocolId = positionAfterTransactionId + 2ULL;
  }
  else
  {
    positionAfterProtocolId =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        positionAfterTransactionId);
  }
  uint64_t positionAfterModbusWriteSingleRegisterPolicy0;
  if (EverParseIsError(positionAfterProtocolId))
  {
    positionAfterModbusWriteSingleRegisterPolicy0 = positionAfterProtocolId;
  }
  else
  {
    uint16_t protocolId = Load16Be(Input + (uint32_t)positionAfterTransactionId);
    BOOLEAN
    protocolIdConstraintIsOk =
      protocolId == (uint16_t)MODBUSTCP_V4_POLICYENFORCED____MODBUS_PROTOCOL_ID;
    uint64_t
    positionAfterProtocolId1 =
      EverParseCheckConstraintOk(protocolIdConstraintIsOk,
        positionAfterProtocolId);
    if (EverParseIsError(positionAfterProtocolId1))
    {
      positionAfterModbusWriteSingleRegisterPolicy0 = positionAfterProtocolId1;
    }
    else
    {
      /* Checking that we have enough space for a UINT16BE, i.e., 2 bytes */
      BOOLEAN hasBytes2 = 2ULL <= (InputLength0 - positionAfterProtocolId1);
      uint64_t positionAfterLength;
      if (hasBytes2)
      {
        positionAfterLength = positionAfterProtocolId1 + 2ULL;
      }
      else
      {
        positionAfterLength =
          EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
            positionAfterProtocolId1);
      }
      uint64_t positionAfterModbusWriteSingleRegisterPolicy1;
      if (EverParseIsError(positionAfterLength))
      {
        positionAfterModbusWriteSingleRegisterPolicy1 = positionAfterLength;
      }
      else
      {
        uint16_t length = Load16Be(Input + (uint32_t)positionAfterProtocolId1);
        BOOLEAN
        lengthConstraintIsOk =
          length == (uint16_t)6U &&
            InputLength ==
              (uint32_t)((uint32_t)length +
                (uint32_t)(uint16_t)MODBUSTCP_V4_POLICYENFORCED____MBAP_HEADER_PREFIX_SIZE);
        uint64_t
        positionAfterLength1 = EverParseCheckConstraintOk(lengthConstraintIsOk, positionAfterLength);
        if (EverParseIsError(positionAfterLength1))
        {
          positionAfterModbusWriteSingleRegisterPolicy1 = positionAfterLength1;
        }
        else
        {
          /* Validating field UnitId */
          /* Checking that we have enough space for a UINT8, i.e., 1 byte */
          BOOLEAN hasBytes3 = 1ULL <= (InputLength0 - positionAfterLength1);
          uint64_t positionAfterModbusWriteSingleRegisterPolicy2;
          if (hasBytes3)
          {
            positionAfterModbusWriteSingleRegisterPolicy2 = positionAfterLength1 + 1ULL;
          }
          else
          {
            positionAfterModbusWriteSingleRegisterPolicy2 =
              EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
                positionAfterLength1);
          }
          uint64_t res1;
          if (EverParseIsSuccess(positionAfterModbusWriteSingleRegisterPolicy2))
          {
            res1 = positionAfterModbusWriteSingleRegisterPolicy2;
          }
          else
          {
            ErrorHandlerFn("_MODBUS_WRITE_SINGLE_REGISTER_POLICY",
              "UnitId",
              EverParseErrorReasonOfResult(positionAfterModbusWriteSingleRegisterPolicy2),
              EverParseGetValidatorErrorKind(positionAfterModbusWriteSingleRegisterPolicy2),
              Ctxt,
              Input,
              positionAfterLength1);
            res1 = positionAfterModbusWriteSingleRegisterPolicy2;
          }
          uint64_t positionAfterUnitId = res1;
          if (EverParseIsError(positionAfterUnitId))
          {
            positionAfterModbusWriteSingleRegisterPolicy1 = positionAfterUnitId;
          }
          else
          {
            /* Checking that we have enough space for a UINT8, i.e., 1 byte */
            BOOLEAN hasBytes4 = 1ULL <= (InputLength0 - positionAfterUnitId);
            uint64_t positionAfterFunctionCode;
            if (hasBytes4)
            {
              positionAfterFunctionCode = positionAfterUnitId + 1ULL;
            }
            else
            {
              positionAfterFunctionCode =
                EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
                  positionAfterUnitId);
            }
            uint64_t positionAfterModbusWriteSingleRegisterPolicy3;
            if (EverParseIsError(positionAfterFunctionCode))
            {
              positionAfterModbusWriteSingleRegisterPolicy3 = positionAfterFunctionCode;
            }
            else
            {
              uint8_t functionCode = Input[(uint32_t)positionAfterUnitId];
              BOOLEAN
              functionCodeConstraintIsOk =
                functionCode == MODBUSTCP_V4_POLICYENFORCED____FC_WRITE_SINGLE_REGISTER;
              uint64_t
              positionAfterFunctionCode1 =
                EverParseCheckConstraintOk(functionCodeConstraintIsOk,
                  positionAfterFunctionCode);
              if (EverParseIsError(positionAfterFunctionCode1))
              {
                positionAfterModbusWriteSingleRegisterPolicy3 = positionAfterFunctionCode1;
              }
              else
              {
                /* Checking that we have enough space for a UINT16BE, i.e., 2 bytes */
                BOOLEAN hasBytes5 = 2ULL <= (InputLength0 - positionAfterFunctionCode1);
                uint64_t positionAfterRegisterAddress;
                if (hasBytes5)
                {
                  positionAfterRegisterAddress = positionAfterFunctionCode1 + 2ULL;
                }
                else
                {
                  positionAfterRegisterAddress =
                    EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
                      positionAfterFunctionCode1);
                }
                uint64_t positionAfterModbusWriteSingleRegisterPolicy4;
                if (EverParseIsError(positionAfterRegisterAddress))
                {
                  positionAfterModbusWriteSingleRegisterPolicy4 = positionAfterRegisterAddress;
                }
                else
                {
                  uint16_t registerAddress = Load16Be(Input + (uint32_t)positionAfterFunctionCode1);
                  BOOLEAN
                  registerAddressConstraintIsOk =
                    registerAddress >= AllowedStart && registerAddress <= AllowedEnd;
                  uint64_t
                  positionAfterRegisterAddress1 =
                    EverParseCheckConstraintOk(registerAddressConstraintIsOk,
                      positionAfterRegisterAddress);
                  if (EverParseIsError(positionAfterRegisterAddress1))
                  {
                    positionAfterModbusWriteSingleRegisterPolicy4 = positionAfterRegisterAddress1;
                  }
                  else
                  {
                    /* Validating field RegisterValue */
                    /* Checking that we have enough space for a UINT16BE, i.e., 2 bytes */
                    BOOLEAN hasBytes = 2ULL <= (InputLength0 - positionAfterRegisterAddress1);
                    uint64_t positionAfterModbusWriteSingleRegisterPolicy5;
                    if (hasBytes)
                    {
                      positionAfterModbusWriteSingleRegisterPolicy5 =
                        positionAfterRegisterAddress1 + 2ULL;
                    }
                    else
                    {
                      positionAfterModbusWriteSingleRegisterPolicy5 =
                        EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
                          positionAfterRegisterAddress1);
                    }
                    uint64_t res;
                    if (EverParseIsSuccess(positionAfterModbusWriteSingleRegisterPolicy5))
                    {
                      res = positionAfterModbusWriteSingleRegisterPolicy5;
                    }
                    else
                    {
                      ErrorHandlerFn("_MODBUS_WRITE_SINGLE_REGISTER_POLICY",
                        "RegisterValue",
                        EverParseErrorReasonOfResult(positionAfterModbusWriteSingleRegisterPolicy5),
                        EverParseGetValidatorErrorKind(positionAfterModbusWriteSingleRegisterPolicy5),
                        Ctxt,
                        Input,
                        positionAfterRegisterAddress1);
                      res = positionAfterModbusWriteSingleRegisterPolicy5;
                    }
                    positionAfterModbusWriteSingleRegisterPolicy4 = res;
                  }
                }
                if (EverParseIsSuccess(positionAfterModbusWriteSingleRegisterPolicy4))
                {
                  positionAfterModbusWriteSingleRegisterPolicy3 =
                    positionAfterModbusWriteSingleRegisterPolicy4;
                }
                else
                {
                  ErrorHandlerFn("_MODBUS_WRITE_SINGLE_REGISTER_POLICY",
                    "RegisterAddress",
                    EverParseErrorReasonOfResult(positionAfterModbusWriteSingleRegisterPolicy4),
                    EverParseGetValidatorErrorKind(positionAfterModbusWriteSingleRegisterPolicy4),
                    Ctxt,
                    Input,
                    positionAfterFunctionCode1);
                  positionAfterModbusWriteSingleRegisterPolicy3 =
                    positionAfterModbusWriteSingleRegisterPolicy4;
                }
              }
            }
            if (EverParseIsSuccess(positionAfterModbusWriteSingleRegisterPolicy3))
            {
              positionAfterModbusWriteSingleRegisterPolicy1 =
                positionAfterModbusWriteSingleRegisterPolicy3;
            }
            else
            {
              ErrorHandlerFn("_MODBUS_WRITE_SINGLE_REGISTER_POLICY",
                "FunctionCode",
                EverParseErrorReasonOfResult(positionAfterModbusWriteSingleRegisterPolicy3),
                EverParseGetValidatorErrorKind(positionAfterModbusWriteSingleRegisterPolicy3),
                Ctxt,
                Input,
                positionAfterUnitId);
              positionAfterModbusWriteSingleRegisterPolicy1 =
                positionAfterModbusWriteSingleRegisterPolicy3;
            }
          }
        }
      }
      if (EverParseIsSuccess(positionAfterModbusWriteSingleRegisterPolicy1))
      {
        positionAfterModbusWriteSingleRegisterPolicy0 =
          positionAfterModbusWriteSingleRegisterPolicy1;
      }
      else
      {
        ErrorHandlerFn("_MODBUS_WRITE_SINGLE_REGISTER_POLICY",
          "Length",
          EverParseErrorReasonOfResult(positionAfterModbusWriteSingleRegisterPolicy1),
          EverParseGetValidatorErrorKind(positionAfterModbusWriteSingleRegisterPolicy1),
          Ctxt,
          Input,
          positionAfterProtocolId1);
        positionAfterModbusWriteSingleRegisterPolicy0 =
          positionAfterModbusWriteSingleRegisterPolicy1;
      }
    }
  }
  if (EverParseIsSuccess(positionAfterModbusWriteSingleRegisterPolicy0))
  {
    return positionAfterModbusWriteSingleRegisterPolicy0;
  }
  ErrorHandlerFn("_MODBUS_WRITE_SINGLE_REGISTER_POLICY",
    "ProtocolId",
    EverParseErrorReasonOfResult(positionAfterModbusWriteSingleRegisterPolicy0),
    EverParseGetValidatorErrorKind(positionAfterModbusWriteSingleRegisterPolicy0),
    Ctxt,
    Input,
    positionAfterTransactionId);
  return positionAfterModbusWriteSingleRegisterPolicy0;
}

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
)
{
  /* Validating field TransactionId */
  /* Checking that we have enough space for a UINT16BE, i.e., 2 bytes */
  BOOLEAN hasBytes0 = 2ULL <= (InputLength0 - StartPosition);
  uint64_t positionAfterModbusWriteMultipleRegistersPolicy;
  if (hasBytes0)
  {
    positionAfterModbusWriteMultipleRegistersPolicy = StartPosition + 2ULL;
  }
  else
  {
    positionAfterModbusWriteMultipleRegistersPolicy =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  uint64_t res0;
  if (EverParseIsSuccess(positionAfterModbusWriteMultipleRegistersPolicy))
  {
    res0 = positionAfterModbusWriteMultipleRegistersPolicy;
  }
  else
  {
    ErrorHandlerFn("_MODBUS_WRITE_MULTIPLE_REGISTERS_POLICY",
      "TransactionId",
      EverParseErrorReasonOfResult(positionAfterModbusWriteMultipleRegistersPolicy),
      EverParseGetValidatorErrorKind(positionAfterModbusWriteMultipleRegistersPolicy),
      Ctxt,
      Input,
      StartPosition);
    res0 = positionAfterModbusWriteMultipleRegistersPolicy;
  }
  uint64_t positionAfterTransactionId = res0;
  if (EverParseIsError(positionAfterTransactionId))
  {
    return positionAfterTransactionId;
  }
  /* Checking that we have enough space for a UINT16BE, i.e., 2 bytes */
  BOOLEAN hasBytes1 = 2ULL <= (InputLength0 - positionAfterTransactionId);
  uint64_t positionAfterProtocolId;
  if (hasBytes1)
  {
    positionAfterProtocolId = positionAfterTransactionId + 2ULL;
  }
  else
  {
    positionAfterProtocolId =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        positionAfterTransactionId);
  }
  uint64_t positionAfterModbusWriteMultipleRegistersPolicy0;
  if (EverParseIsError(positionAfterProtocolId))
  {
    positionAfterModbusWriteMultipleRegistersPolicy0 = positionAfterProtocolId;
  }
  else
  {
    uint16_t protocolId = Load16Be(Input + (uint32_t)positionAfterTransactionId);
    BOOLEAN
    protocolIdConstraintIsOk =
      protocolId == (uint16_t)MODBUSTCP_V4_POLICYENFORCED____MODBUS_PROTOCOL_ID;
    uint64_t
    positionAfterProtocolId1 =
      EverParseCheckConstraintOk(protocolIdConstraintIsOk,
        positionAfterProtocolId);
    if (EverParseIsError(positionAfterProtocolId1))
    {
      positionAfterModbusWriteMultipleRegistersPolicy0 = positionAfterProtocolId1;
    }
    else
    {
      /* Checking that we have enough space for a UINT16BE, i.e., 2 bytes */
      BOOLEAN hasBytes2 = 2ULL <= (InputLength0 - positionAfterProtocolId1);
      uint64_t positionAfterLength;
      if (hasBytes2)
      {
        positionAfterLength = positionAfterProtocolId1 + 2ULL;
      }
      else
      {
        positionAfterLength =
          EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
            positionAfterProtocolId1);
      }
      uint64_t positionAfterModbusWriteMultipleRegistersPolicy1;
      if (EverParseIsError(positionAfterLength))
      {
        positionAfterModbusWriteMultipleRegistersPolicy1 = positionAfterLength;
      }
      else
      {
        uint16_t length = Load16Be(Input + (uint32_t)positionAfterProtocolId1);
        BOOLEAN
        lengthConstraintIsOk =
          length >= (uint16_t)9U && length <= (uint16_t)253U &&
            InputLength ==
              (uint32_t)((uint32_t)length +
                (uint32_t)(uint16_t)MODBUSTCP_V4_POLICYENFORCED____MBAP_HEADER_PREFIX_SIZE);
        uint64_t
        positionAfterLength1 = EverParseCheckConstraintOk(lengthConstraintIsOk, positionAfterLength);
        if (EverParseIsError(positionAfterLength1))
        {
          positionAfterModbusWriteMultipleRegistersPolicy1 = positionAfterLength1;
        }
        else
        {
          /* Validating field UnitId */
          /* Checking that we have enough space for a UINT8, i.e., 1 byte */
          BOOLEAN hasBytes3 = 1ULL <= (InputLength0 - positionAfterLength1);
          uint64_t positionAfterModbusWriteMultipleRegistersPolicy2;
          if (hasBytes3)
          {
            positionAfterModbusWriteMultipleRegistersPolicy2 = positionAfterLength1 + 1ULL;
          }
          else
          {
            positionAfterModbusWriteMultipleRegistersPolicy2 =
              EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
                positionAfterLength1);
          }
          uint64_t res1;
          if (EverParseIsSuccess(positionAfterModbusWriteMultipleRegistersPolicy2))
          {
            res1 = positionAfterModbusWriteMultipleRegistersPolicy2;
          }
          else
          {
            ErrorHandlerFn("_MODBUS_WRITE_MULTIPLE_REGISTERS_POLICY",
              "UnitId",
              EverParseErrorReasonOfResult(positionAfterModbusWriteMultipleRegistersPolicy2),
              EverParseGetValidatorErrorKind(positionAfterModbusWriteMultipleRegistersPolicy2),
              Ctxt,
              Input,
              positionAfterLength1);
            res1 = positionAfterModbusWriteMultipleRegistersPolicy2;
          }
          uint64_t positionAfterUnitId = res1;
          if (EverParseIsError(positionAfterUnitId))
          {
            positionAfterModbusWriteMultipleRegistersPolicy1 = positionAfterUnitId;
          }
          else
          {
            /* Checking that we have enough space for a UINT8, i.e., 1 byte */
            BOOLEAN hasBytes4 = 1ULL <= (InputLength0 - positionAfterUnitId);
            uint64_t positionAfterFunctionCode;
            if (hasBytes4)
            {
              positionAfterFunctionCode = positionAfterUnitId + 1ULL;
            }
            else
            {
              positionAfterFunctionCode =
                EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
                  positionAfterUnitId);
            }
            uint64_t positionAfterModbusWriteMultipleRegistersPolicy3;
            if (EverParseIsError(positionAfterFunctionCode))
            {
              positionAfterModbusWriteMultipleRegistersPolicy3 = positionAfterFunctionCode;
            }
            else
            {
              uint8_t functionCode = Input[(uint32_t)positionAfterUnitId];
              BOOLEAN
              functionCodeConstraintIsOk =
                functionCode == MODBUSTCP_V4_POLICYENFORCED____FC_WRITE_MULTIPLE_REGISTERS;
              uint64_t
              positionAfterFunctionCode1 =
                EverParseCheckConstraintOk(functionCodeConstraintIsOk,
                  positionAfterFunctionCode);
              if (EverParseIsError(positionAfterFunctionCode1))
              {
                positionAfterModbusWriteMultipleRegistersPolicy3 = positionAfterFunctionCode1;
              }
              else
              {
                /* Checking that we have enough space for a UINT16BE, i.e., 2 bytes */
                BOOLEAN hasBytes5 = 2ULL <= (InputLength0 - positionAfterFunctionCode1);
                uint64_t positionAfterStartAddress;
                if (hasBytes5)
                {
                  positionAfterStartAddress = positionAfterFunctionCode1 + 2ULL;
                }
                else
                {
                  positionAfterStartAddress =
                    EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
                      positionAfterFunctionCode1);
                }
                uint64_t positionAfterModbusWriteMultipleRegistersPolicy4;
                if (EverParseIsError(positionAfterStartAddress))
                {
                  positionAfterModbusWriteMultipleRegistersPolicy4 = positionAfterStartAddress;
                }
                else
                {
                  uint16_t startAddress = Load16Be(Input + (uint32_t)positionAfterFunctionCode1);
                  BOOLEAN
                  startAddressConstraintIsOk =
                    startAddress >= AllowedStart && startAddress <= AllowedEnd;
                  uint64_t
                  positionAfterStartAddress1 =
                    EverParseCheckConstraintOk(startAddressConstraintIsOk,
                      positionAfterStartAddress);
                  if (EverParseIsError(positionAfterStartAddress1))
                  {
                    positionAfterModbusWriteMultipleRegistersPolicy4 = positionAfterStartAddress1;
                  }
                  else
                  {
                    /* Checking that we have enough space for a UINT16BE, i.e., 2 bytes */
                    BOOLEAN hasBytes6 = 2ULL <= (InputLength0 - positionAfterStartAddress1);
                    uint64_t positionAfterQuantity;
                    if (hasBytes6)
                    {
                      positionAfterQuantity = positionAfterStartAddress1 + 2ULL;
                    }
                    else
                    {
                      positionAfterQuantity =
                        EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
                          positionAfterStartAddress1);
                    }
                    uint64_t positionAfterModbusWriteMultipleRegistersPolicy5;
                    if (EverParseIsError(positionAfterQuantity))
                    {
                      positionAfterModbusWriteMultipleRegistersPolicy5 = positionAfterQuantity;
                    }
                    else
                    {
                      uint16_t quantity = Load16Be(Input + (uint32_t)positionAfterStartAddress1);
                      BOOLEAN
                      quantityConstraintIsOk =
                        quantity >= (uint16_t)1U &&
                          quantity <= (uint16_t)MODBUSTCP_V4_POLICYENFORCED____MAX_WRITE_REGISTERS
                        &&
                          ((uint32_t)quantity - (uint32_t)(uint16_t)1U) <=
                            ((uint32_t)AllowedEnd - (uint32_t)startAddress);
                      uint64_t
                      positionAfterQuantity1 =
                        EverParseCheckConstraintOk(quantityConstraintIsOk,
                          positionAfterQuantity);
                      if (EverParseIsError(positionAfterQuantity1))
                      {
                        positionAfterModbusWriteMultipleRegistersPolicy5 = positionAfterQuantity1;
                      }
                      else
                      {
                        /* Checking that we have enough space for a UINT8, i.e., 1 byte */
                        BOOLEAN hasBytes7 = 1ULL <= (InputLength0 - positionAfterQuantity1);
                        uint64_t positionAfterByteCount;
                        if (hasBytes7)
                        {
                          positionAfterByteCount = positionAfterQuantity1 + 1ULL;
                        }
                        else
                        {
                          positionAfterByteCount =
                            EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
                              positionAfterQuantity1);
                        }
                        uint64_t positionAfterModbusWriteMultipleRegistersPolicy6;
                        if (EverParseIsError(positionAfterByteCount))
                        {
                          positionAfterModbusWriteMultipleRegistersPolicy6 = positionAfterByteCount;
                        }
                        else
                        {
                          uint8_t byteCount = Input[(uint32_t)positionAfterQuantity1];
                          BOOLEAN
                          byteCountConstraintIsOk =
                            (uint16_t)byteCount == (uint32_t)quantity * (uint32_t)(uint16_t)2U &&
                              length == (uint16_t)(7U + (uint32_t)byteCount);
                          uint64_t
                          positionAfterByteCount1 =
                            EverParseCheckConstraintOk(byteCountConstraintIsOk,
                              positionAfterByteCount);
                          if (EverParseIsError(positionAfterByteCount1))
                          {
                            positionAfterModbusWriteMultipleRegistersPolicy6 =
                              positionAfterByteCount1;
                          }
                          else
                          {
                            /* Validating field RegisterValues */
                            BOOLEAN
                            hasBytes =
                              (uint64_t)(uint32_t)byteCount <=
                                (InputLength0 - positionAfterByteCount1);
                            uint64_t res;
                            if (hasBytes)
                            {
                              res = positionAfterByteCount1 + (uint64_t)(uint32_t)byteCount;
                            }
                            else
                            {
                              res =
                                EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
                                  positionAfterByteCount1);
                            }
                            uint64_t positionAfterModbusWriteMultipleRegistersPolicy7 = res;
                            if
                            (EverParseIsSuccess(positionAfterModbusWriteMultipleRegistersPolicy7))
                            {
                              positionAfterModbusWriteMultipleRegistersPolicy6 =
                                positionAfterModbusWriteMultipleRegistersPolicy7;
                            }
                            else
                            {
                              ErrorHandlerFn("_MODBUS_WRITE_MULTIPLE_REGISTERS_POLICY",
                                "RegisterValues",
                                EverParseErrorReasonOfResult(positionAfterModbusWriteMultipleRegistersPolicy7),
                                EverParseGetValidatorErrorKind(positionAfterModbusWriteMultipleRegistersPolicy7),
                                Ctxt,
                                Input,
                                positionAfterByteCount1);
                              positionAfterModbusWriteMultipleRegistersPolicy6 =
                                positionAfterModbusWriteMultipleRegistersPolicy7;
                            }
                          }
                        }
                        if (EverParseIsSuccess(positionAfterModbusWriteMultipleRegistersPolicy6))
                        {
                          positionAfterModbusWriteMultipleRegistersPolicy5 =
                            positionAfterModbusWriteMultipleRegistersPolicy6;
                        }
                        else
                        {
                          ErrorHandlerFn("_MODBUS_WRITE_MULTIPLE_REGISTERS_POLICY",
                            "ByteCount",
                            EverParseErrorReasonOfResult(positionAfterModbusWriteMultipleRegistersPolicy6),
                            EverParseGetValidatorErrorKind(positionAfterModbusWriteMultipleRegistersPolicy6),
                            Ctxt,
                            Input,
                            positionAfterQuantity1);
                          positionAfterModbusWriteMultipleRegistersPolicy5 =
                            positionAfterModbusWriteMultipleRegistersPolicy6;
                        }
                      }
                    }
                    if (EverParseIsSuccess(positionAfterModbusWriteMultipleRegistersPolicy5))
                    {
                      positionAfterModbusWriteMultipleRegistersPolicy4 =
                        positionAfterModbusWriteMultipleRegistersPolicy5;
                    }
                    else
                    {
                      ErrorHandlerFn("_MODBUS_WRITE_MULTIPLE_REGISTERS_POLICY",
                        "Quantity",
                        EverParseErrorReasonOfResult(positionAfterModbusWriteMultipleRegistersPolicy5),
                        EverParseGetValidatorErrorKind(positionAfterModbusWriteMultipleRegistersPolicy5),
                        Ctxt,
                        Input,
                        positionAfterStartAddress1);
                      positionAfterModbusWriteMultipleRegistersPolicy4 =
                        positionAfterModbusWriteMultipleRegistersPolicy5;
                    }
                  }
                }
                if (EverParseIsSuccess(positionAfterModbusWriteMultipleRegistersPolicy4))
                {
                  positionAfterModbusWriteMultipleRegistersPolicy3 =
                    positionAfterModbusWriteMultipleRegistersPolicy4;
                }
                else
                {
                  ErrorHandlerFn("_MODBUS_WRITE_MULTIPLE_REGISTERS_POLICY",
                    "StartAddress",
                    EverParseErrorReasonOfResult(positionAfterModbusWriteMultipleRegistersPolicy4),
                    EverParseGetValidatorErrorKind(positionAfterModbusWriteMultipleRegistersPolicy4),
                    Ctxt,
                    Input,
                    positionAfterFunctionCode1);
                  positionAfterModbusWriteMultipleRegistersPolicy3 =
                    positionAfterModbusWriteMultipleRegistersPolicy4;
                }
              }
            }
            if (EverParseIsSuccess(positionAfterModbusWriteMultipleRegistersPolicy3))
            {
              positionAfterModbusWriteMultipleRegistersPolicy1 =
                positionAfterModbusWriteMultipleRegistersPolicy3;
            }
            else
            {
              ErrorHandlerFn("_MODBUS_WRITE_MULTIPLE_REGISTERS_POLICY",
                "FunctionCode",
                EverParseErrorReasonOfResult(positionAfterModbusWriteMultipleRegistersPolicy3),
                EverParseGetValidatorErrorKind(positionAfterModbusWriteMultipleRegistersPolicy3),
                Ctxt,
                Input,
                positionAfterUnitId);
              positionAfterModbusWriteMultipleRegistersPolicy1 =
                positionAfterModbusWriteMultipleRegistersPolicy3;
            }
          }
        }
      }
      if (EverParseIsSuccess(positionAfterModbusWriteMultipleRegistersPolicy1))
      {
        positionAfterModbusWriteMultipleRegistersPolicy0 =
          positionAfterModbusWriteMultipleRegistersPolicy1;
      }
      else
      {
        ErrorHandlerFn("_MODBUS_WRITE_MULTIPLE_REGISTERS_POLICY",
          "Length",
          EverParseErrorReasonOfResult(positionAfterModbusWriteMultipleRegistersPolicy1),
          EverParseGetValidatorErrorKind(positionAfterModbusWriteMultipleRegistersPolicy1),
          Ctxt,
          Input,
          positionAfterProtocolId1);
        positionAfterModbusWriteMultipleRegistersPolicy0 =
          positionAfterModbusWriteMultipleRegistersPolicy1;
      }
    }
  }
  if (EverParseIsSuccess(positionAfterModbusWriteMultipleRegistersPolicy0))
  {
    return positionAfterModbusWriteMultipleRegistersPolicy0;
  }
  ErrorHandlerFn("_MODBUS_WRITE_MULTIPLE_REGISTERS_POLICY",
    "ProtocolId",
    EverParseErrorReasonOfResult(positionAfterModbusWriteMultipleRegistersPolicy0),
    EverParseGetValidatorErrorKind(positionAfterModbusWriteMultipleRegistersPolicy0),
    Ctxt,
    Input,
    positionAfterTransactionId);
  return positionAfterModbusWriteMultipleRegistersPolicy0;
}

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
)
{
  /* Validating field TransactionId */
  /* Checking that we have enough space for a UINT16BE, i.e., 2 bytes */
  BOOLEAN hasBytes0 = 2ULL <= (InputLength0 - StartPosition);
  uint64_t positionAfterModbusReadWriteRegistersPolicy;
  if (hasBytes0)
  {
    positionAfterModbusReadWriteRegistersPolicy = StartPosition + 2ULL;
  }
  else
  {
    positionAfterModbusReadWriteRegistersPolicy =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  uint64_t res0;
  if (EverParseIsSuccess(positionAfterModbusReadWriteRegistersPolicy))
  {
    res0 = positionAfterModbusReadWriteRegistersPolicy;
  }
  else
  {
    ErrorHandlerFn("_MODBUS_READ_WRITE_REGISTERS_POLICY",
      "TransactionId",
      EverParseErrorReasonOfResult(positionAfterModbusReadWriteRegistersPolicy),
      EverParseGetValidatorErrorKind(positionAfterModbusReadWriteRegistersPolicy),
      Ctxt,
      Input,
      StartPosition);
    res0 = positionAfterModbusReadWriteRegistersPolicy;
  }
  uint64_t positionAfterTransactionId = res0;
  if (EverParseIsError(positionAfterTransactionId))
  {
    return positionAfterTransactionId;
  }
  /* Checking that we have enough space for a UINT16BE, i.e., 2 bytes */
  BOOLEAN hasBytes1 = 2ULL <= (InputLength0 - positionAfterTransactionId);
  uint64_t positionAfterProtocolId;
  if (hasBytes1)
  {
    positionAfterProtocolId = positionAfterTransactionId + 2ULL;
  }
  else
  {
    positionAfterProtocolId =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        positionAfterTransactionId);
  }
  uint64_t positionAfterModbusReadWriteRegistersPolicy0;
  if (EverParseIsError(positionAfterProtocolId))
  {
    positionAfterModbusReadWriteRegistersPolicy0 = positionAfterProtocolId;
  }
  else
  {
    uint16_t protocolId = Load16Be(Input + (uint32_t)positionAfterTransactionId);
    BOOLEAN
    protocolIdConstraintIsOk =
      protocolId == (uint16_t)MODBUSTCP_V4_POLICYENFORCED____MODBUS_PROTOCOL_ID;
    uint64_t
    positionAfterProtocolId1 =
      EverParseCheckConstraintOk(protocolIdConstraintIsOk,
        positionAfterProtocolId);
    if (EverParseIsError(positionAfterProtocolId1))
    {
      positionAfterModbusReadWriteRegistersPolicy0 = positionAfterProtocolId1;
    }
    else
    {
      /* Checking that we have enough space for a UINT16BE, i.e., 2 bytes */
      BOOLEAN hasBytes2 = 2ULL <= (InputLength0 - positionAfterProtocolId1);
      uint64_t positionAfterLength;
      if (hasBytes2)
      {
        positionAfterLength = positionAfterProtocolId1 + 2ULL;
      }
      else
      {
        positionAfterLength =
          EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
            positionAfterProtocolId1);
      }
      uint64_t positionAfterModbusReadWriteRegistersPolicy1;
      if (EverParseIsError(positionAfterLength))
      {
        positionAfterModbusReadWriteRegistersPolicy1 = positionAfterLength;
      }
      else
      {
        uint16_t length = Load16Be(Input + (uint32_t)positionAfterProtocolId1);
        BOOLEAN
        lengthConstraintIsOk =
          length >= (uint16_t)13U && length <= (uint16_t)253U &&
            InputLength ==
              (uint32_t)((uint32_t)length +
                (uint32_t)(uint16_t)MODBUSTCP_V4_POLICYENFORCED____MBAP_HEADER_PREFIX_SIZE);
        uint64_t
        positionAfterLength1 = EverParseCheckConstraintOk(lengthConstraintIsOk, positionAfterLength);
        if (EverParseIsError(positionAfterLength1))
        {
          positionAfterModbusReadWriteRegistersPolicy1 = positionAfterLength1;
        }
        else
        {
          /* Validating field UnitId */
          /* Checking that we have enough space for a UINT8, i.e., 1 byte */
          BOOLEAN hasBytes3 = 1ULL <= (InputLength0 - positionAfterLength1);
          uint64_t positionAfterModbusReadWriteRegistersPolicy2;
          if (hasBytes3)
          {
            positionAfterModbusReadWriteRegistersPolicy2 = positionAfterLength1 + 1ULL;
          }
          else
          {
            positionAfterModbusReadWriteRegistersPolicy2 =
              EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
                positionAfterLength1);
          }
          uint64_t res1;
          if (EverParseIsSuccess(positionAfterModbusReadWriteRegistersPolicy2))
          {
            res1 = positionAfterModbusReadWriteRegistersPolicy2;
          }
          else
          {
            ErrorHandlerFn("_MODBUS_READ_WRITE_REGISTERS_POLICY",
              "UnitId",
              EverParseErrorReasonOfResult(positionAfterModbusReadWriteRegistersPolicy2),
              EverParseGetValidatorErrorKind(positionAfterModbusReadWriteRegistersPolicy2),
              Ctxt,
              Input,
              positionAfterLength1);
            res1 = positionAfterModbusReadWriteRegistersPolicy2;
          }
          uint64_t positionAfterUnitId = res1;
          if (EverParseIsError(positionAfterUnitId))
          {
            positionAfterModbusReadWriteRegistersPolicy1 = positionAfterUnitId;
          }
          else
          {
            /* Checking that we have enough space for a UINT8, i.e., 1 byte */
            BOOLEAN hasBytes4 = 1ULL <= (InputLength0 - positionAfterUnitId);
            uint64_t positionAfterFunctionCode;
            if (hasBytes4)
            {
              positionAfterFunctionCode = positionAfterUnitId + 1ULL;
            }
            else
            {
              positionAfterFunctionCode =
                EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
                  positionAfterUnitId);
            }
            uint64_t positionAfterModbusReadWriteRegistersPolicy3;
            if (EverParseIsError(positionAfterFunctionCode))
            {
              positionAfterModbusReadWriteRegistersPolicy3 = positionAfterFunctionCode;
            }
            else
            {
              uint8_t functionCode = Input[(uint32_t)positionAfterUnitId];
              BOOLEAN
              functionCodeConstraintIsOk =
                functionCode == MODBUSTCP_V4_POLICYENFORCED____FC_READ_WRITE_MULTIPLE_REGISTERS;
              uint64_t
              positionAfterFunctionCode1 =
                EverParseCheckConstraintOk(functionCodeConstraintIsOk,
                  positionAfterFunctionCode);
              if (EverParseIsError(positionAfterFunctionCode1))
              {
                positionAfterModbusReadWriteRegistersPolicy3 = positionAfterFunctionCode1;
              }
              else
              {
                /* Checking that we have enough space for a UINT16BE, i.e., 2 bytes */
                BOOLEAN hasBytes5 = 2ULL <= (InputLength0 - positionAfterFunctionCode1);
                uint64_t positionAfterReadStartAddress;
                if (hasBytes5)
                {
                  positionAfterReadStartAddress = positionAfterFunctionCode1 + 2ULL;
                }
                else
                {
                  positionAfterReadStartAddress =
                    EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
                      positionAfterFunctionCode1);
                }
                uint64_t positionAfterModbusReadWriteRegistersPolicy4;
                if (EverParseIsError(positionAfterReadStartAddress))
                {
                  positionAfterModbusReadWriteRegistersPolicy4 = positionAfterReadStartAddress;
                }
                else
                {
                  uint16_t
                  readStartAddress = Load16Be(Input + (uint32_t)positionAfterFunctionCode1);
                  BOOLEAN
                  readStartAddressConstraintIsOk =
                    readStartAddress >= AllowedStart && readStartAddress <= AllowedEnd;
                  uint64_t
                  positionAfterReadStartAddress1 =
                    EverParseCheckConstraintOk(readStartAddressConstraintIsOk,
                      positionAfterReadStartAddress);
                  if (EverParseIsError(positionAfterReadStartAddress1))
                  {
                    positionAfterModbusReadWriteRegistersPolicy4 = positionAfterReadStartAddress1;
                  }
                  else
                  {
                    /* Checking that we have enough space for a UINT16BE, i.e., 2 bytes */
                    BOOLEAN hasBytes6 = 2ULL <= (InputLength0 - positionAfterReadStartAddress1);
                    uint64_t positionAfterReadQuantity;
                    if (hasBytes6)
                    {
                      positionAfterReadQuantity = positionAfterReadStartAddress1 + 2ULL;
                    }
                    else
                    {
                      positionAfterReadQuantity =
                        EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
                          positionAfterReadStartAddress1);
                    }
                    uint64_t positionAfterModbusReadWriteRegistersPolicy5;
                    if (EverParseIsError(positionAfterReadQuantity))
                    {
                      positionAfterModbusReadWriteRegistersPolicy5 = positionAfterReadQuantity;
                    }
                    else
                    {
                      uint16_t
                      readQuantity = Load16Be(Input + (uint32_t)positionAfterReadStartAddress1);
                      BOOLEAN
                      readQuantityConstraintIsOk =
                        readQuantity >= (uint16_t)1U &&
                          readQuantity <=
                            (uint16_t)MODBUSTCP_V4_POLICYENFORCED____MAX_RW_READ_REGISTERS
                        &&
                          ((uint32_t)readQuantity - (uint32_t)(uint16_t)1U) <=
                            ((uint32_t)AllowedEnd - (uint32_t)readStartAddress);
                      uint64_t
                      positionAfterReadQuantity1 =
                        EverParseCheckConstraintOk(readQuantityConstraintIsOk,
                          positionAfterReadQuantity);
                      if (EverParseIsError(positionAfterReadQuantity1))
                      {
                        positionAfterModbusReadWriteRegistersPolicy5 = positionAfterReadQuantity1;
                      }
                      else
                      {
                        /* Checking that we have enough space for a UINT16BE, i.e., 2 bytes */
                        BOOLEAN hasBytes7 = 2ULL <= (InputLength0 - positionAfterReadQuantity1);
                        uint64_t positionAfterWriteStartAddress;
                        if (hasBytes7)
                        {
                          positionAfterWriteStartAddress = positionAfterReadQuantity1 + 2ULL;
                        }
                        else
                        {
                          positionAfterWriteStartAddress =
                            EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
                              positionAfterReadQuantity1);
                        }
                        uint64_t positionAfterModbusReadWriteRegistersPolicy6;
                        if (EverParseIsError(positionAfterWriteStartAddress))
                        {
                          positionAfterModbusReadWriteRegistersPolicy6 =
                            positionAfterWriteStartAddress;
                        }
                        else
                        {
                          uint16_t
                          writeStartAddress = Load16Be(Input + (uint32_t)positionAfterReadQuantity1);
                          BOOLEAN
                          writeStartAddressConstraintIsOk =
                            writeStartAddress >= AllowedStart && writeStartAddress <= AllowedEnd;
                          uint64_t
                          positionAfterWriteStartAddress1 =
                            EverParseCheckConstraintOk(writeStartAddressConstraintIsOk,
                              positionAfterWriteStartAddress);
                          if (EverParseIsError(positionAfterWriteStartAddress1))
                          {
                            positionAfterModbusReadWriteRegistersPolicy6 =
                              positionAfterWriteStartAddress1;
                          }
                          else
                          {
                            /* Checking that we have enough space for a UINT16BE, i.e., 2 bytes */
                            BOOLEAN
                            hasBytes8 = 2ULL <= (InputLength0 - positionAfterWriteStartAddress1);
                            uint64_t positionAfterWriteQuantity;
                            if (hasBytes8)
                            {
                              positionAfterWriteQuantity = positionAfterWriteStartAddress1 + 2ULL;
                            }
                            else
                            {
                              positionAfterWriteQuantity =
                                EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
                                  positionAfterWriteStartAddress1);
                            }
                            uint64_t positionAfterModbusReadWriteRegistersPolicy7;
                            if (EverParseIsError(positionAfterWriteQuantity))
                            {
                              positionAfterModbusReadWriteRegistersPolicy7 =
                                positionAfterWriteQuantity;
                            }
                            else
                            {
                              uint16_t
                              writeQuantity =
                                Load16Be(Input + (uint32_t)positionAfterWriteStartAddress1);
                              BOOLEAN
                              writeQuantityConstraintIsOk =
                                writeQuantity >= (uint16_t)1U &&
                                  writeQuantity <=
                                    (uint16_t)MODBUSTCP_V4_POLICYENFORCED____MAX_RW_WRITE_REGISTERS
                                &&
                                  ((uint32_t)writeQuantity - (uint32_t)(uint16_t)1U) <=
                                    ((uint32_t)AllowedEnd - (uint32_t)writeStartAddress);
                              uint64_t
                              positionAfterWriteQuantity1 =
                                EverParseCheckConstraintOk(writeQuantityConstraintIsOk,
                                  positionAfterWriteQuantity);
                              if (EverParseIsError(positionAfterWriteQuantity1))
                              {
                                positionAfterModbusReadWriteRegistersPolicy7 =
                                  positionAfterWriteQuantity1;
                              }
                              else
                              {
                                /* Checking that we have enough space for a UINT8, i.e., 1 byte */
                                BOOLEAN
                                hasBytes9 = 1ULL <= (InputLength0 - positionAfterWriteQuantity1);
                                uint64_t positionAfterWriteByteCount;
                                if (hasBytes9)
                                {
                                  positionAfterWriteByteCount = positionAfterWriteQuantity1 + 1ULL;
                                }
                                else
                                {
                                  positionAfterWriteByteCount =
                                    EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
                                      positionAfterWriteQuantity1);
                                }
                                uint64_t positionAfterModbusReadWriteRegistersPolicy8;
                                if (EverParseIsError(positionAfterWriteByteCount))
                                {
                                  positionAfterModbusReadWriteRegistersPolicy8 =
                                    positionAfterWriteByteCount;
                                }
                                else
                                {
                                  uint8_t
                                  writeByteCount = Input[(uint32_t)positionAfterWriteQuantity1];
                                  BOOLEAN
                                  writeByteCountConstraintIsOk =
                                    (uint16_t)writeByteCount ==
                                      (uint32_t)writeQuantity * (uint32_t)(uint16_t)2U
                                    && length == (uint16_t)(11U + (uint32_t)writeByteCount);
                                  uint64_t
                                  positionAfterWriteByteCount1 =
                                    EverParseCheckConstraintOk(writeByteCountConstraintIsOk,
                                      positionAfterWriteByteCount);
                                  if (EverParseIsError(positionAfterWriteByteCount1))
                                  {
                                    positionAfterModbusReadWriteRegistersPolicy8 =
                                      positionAfterWriteByteCount1;
                                  }
                                  else
                                  {
                                    /* Validating field WriteRegisterValues */
                                    BOOLEAN
                                    hasBytes =
                                      (uint64_t)(uint32_t)writeByteCount <=
                                        (InputLength0 - positionAfterWriteByteCount1);
                                    uint64_t res;
                                    if (hasBytes)
                                    {
                                      res =
                                        positionAfterWriteByteCount1 +
                                          (uint64_t)(uint32_t)writeByteCount;
                                    }
                                    else
                                    {
                                      res =
                                        EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
                                          positionAfterWriteByteCount1);
                                    }
                                    uint64_t positionAfterModbusReadWriteRegistersPolicy9 = res;
                                    if
                                    (
                                      EverParseIsSuccess(positionAfterModbusReadWriteRegistersPolicy9)
                                    )
                                    {
                                      positionAfterModbusReadWriteRegistersPolicy8 =
                                        positionAfterModbusReadWriteRegistersPolicy9;
                                    }
                                    else
                                    {
                                      ErrorHandlerFn("_MODBUS_READ_WRITE_REGISTERS_POLICY",
                                        "WriteRegisterValues",
                                        EverParseErrorReasonOfResult(positionAfterModbusReadWriteRegistersPolicy9),
                                        EverParseGetValidatorErrorKind(positionAfterModbusReadWriteRegistersPolicy9),
                                        Ctxt,
                                        Input,
                                        positionAfterWriteByteCount1);
                                      positionAfterModbusReadWriteRegistersPolicy8 =
                                        positionAfterModbusReadWriteRegistersPolicy9;
                                    }
                                  }
                                }
                                if
                                (EverParseIsSuccess(positionAfterModbusReadWriteRegistersPolicy8))
                                {
                                  positionAfterModbusReadWriteRegistersPolicy7 =
                                    positionAfterModbusReadWriteRegistersPolicy8;
                                }
                                else
                                {
                                  ErrorHandlerFn("_MODBUS_READ_WRITE_REGISTERS_POLICY",
                                    "WriteByteCount",
                                    EverParseErrorReasonOfResult(positionAfterModbusReadWriteRegistersPolicy8),
                                    EverParseGetValidatorErrorKind(positionAfterModbusReadWriteRegistersPolicy8),
                                    Ctxt,
                                    Input,
                                    positionAfterWriteQuantity1);
                                  positionAfterModbusReadWriteRegistersPolicy7 =
                                    positionAfterModbusReadWriteRegistersPolicy8;
                                }
                              }
                            }
                            if (EverParseIsSuccess(positionAfterModbusReadWriteRegistersPolicy7))
                            {
                              positionAfterModbusReadWriteRegistersPolicy6 =
                                positionAfterModbusReadWriteRegistersPolicy7;
                            }
                            else
                            {
                              ErrorHandlerFn("_MODBUS_READ_WRITE_REGISTERS_POLICY",
                                "WriteQuantity",
                                EverParseErrorReasonOfResult(positionAfterModbusReadWriteRegistersPolicy7),
                                EverParseGetValidatorErrorKind(positionAfterModbusReadWriteRegistersPolicy7),
                                Ctxt,
                                Input,
                                positionAfterWriteStartAddress1);
                              positionAfterModbusReadWriteRegistersPolicy6 =
                                positionAfterModbusReadWriteRegistersPolicy7;
                            }
                          }
                        }
                        if (EverParseIsSuccess(positionAfterModbusReadWriteRegistersPolicy6))
                        {
                          positionAfterModbusReadWriteRegistersPolicy5 =
                            positionAfterModbusReadWriteRegistersPolicy6;
                        }
                        else
                        {
                          ErrorHandlerFn("_MODBUS_READ_WRITE_REGISTERS_POLICY",
                            "WriteStartAddress",
                            EverParseErrorReasonOfResult(positionAfterModbusReadWriteRegistersPolicy6),
                            EverParseGetValidatorErrorKind(positionAfterModbusReadWriteRegistersPolicy6),
                            Ctxt,
                            Input,
                            positionAfterReadQuantity1);
                          positionAfterModbusReadWriteRegistersPolicy5 =
                            positionAfterModbusReadWriteRegistersPolicy6;
                        }
                      }
                    }
                    if (EverParseIsSuccess(positionAfterModbusReadWriteRegistersPolicy5))
                    {
                      positionAfterModbusReadWriteRegistersPolicy4 =
                        positionAfterModbusReadWriteRegistersPolicy5;
                    }
                    else
                    {
                      ErrorHandlerFn("_MODBUS_READ_WRITE_REGISTERS_POLICY",
                        "ReadQuantity",
                        EverParseErrorReasonOfResult(positionAfterModbusReadWriteRegistersPolicy5),
                        EverParseGetValidatorErrorKind(positionAfterModbusReadWriteRegistersPolicy5),
                        Ctxt,
                        Input,
                        positionAfterReadStartAddress1);
                      positionAfterModbusReadWriteRegistersPolicy4 =
                        positionAfterModbusReadWriteRegistersPolicy5;
                    }
                  }
                }
                if (EverParseIsSuccess(positionAfterModbusReadWriteRegistersPolicy4))
                {
                  positionAfterModbusReadWriteRegistersPolicy3 =
                    positionAfterModbusReadWriteRegistersPolicy4;
                }
                else
                {
                  ErrorHandlerFn("_MODBUS_READ_WRITE_REGISTERS_POLICY",
                    "ReadStartAddress",
                    EverParseErrorReasonOfResult(positionAfterModbusReadWriteRegistersPolicy4),
                    EverParseGetValidatorErrorKind(positionAfterModbusReadWriteRegistersPolicy4),
                    Ctxt,
                    Input,
                    positionAfterFunctionCode1);
                  positionAfterModbusReadWriteRegistersPolicy3 =
                    positionAfterModbusReadWriteRegistersPolicy4;
                }
              }
            }
            if (EverParseIsSuccess(positionAfterModbusReadWriteRegistersPolicy3))
            {
              positionAfterModbusReadWriteRegistersPolicy1 =
                positionAfterModbusReadWriteRegistersPolicy3;
            }
            else
            {
              ErrorHandlerFn("_MODBUS_READ_WRITE_REGISTERS_POLICY",
                "FunctionCode",
                EverParseErrorReasonOfResult(positionAfterModbusReadWriteRegistersPolicy3),
                EverParseGetValidatorErrorKind(positionAfterModbusReadWriteRegistersPolicy3),
                Ctxt,
                Input,
                positionAfterUnitId);
              positionAfterModbusReadWriteRegistersPolicy1 =
                positionAfterModbusReadWriteRegistersPolicy3;
            }
          }
        }
      }
      if (EverParseIsSuccess(positionAfterModbusReadWriteRegistersPolicy1))
      {
        positionAfterModbusReadWriteRegistersPolicy0 = positionAfterModbusReadWriteRegistersPolicy1;
      }
      else
      {
        ErrorHandlerFn("_MODBUS_READ_WRITE_REGISTERS_POLICY",
          "Length",
          EverParseErrorReasonOfResult(positionAfterModbusReadWriteRegistersPolicy1),
          EverParseGetValidatorErrorKind(positionAfterModbusReadWriteRegistersPolicy1),
          Ctxt,
          Input,
          positionAfterProtocolId1);
        positionAfterModbusReadWriteRegistersPolicy0 = positionAfterModbusReadWriteRegistersPolicy1;
      }
    }
  }
  if (EverParseIsSuccess(positionAfterModbusReadWriteRegistersPolicy0))
  {
    return positionAfterModbusReadWriteRegistersPolicy0;
  }
  ErrorHandlerFn("_MODBUS_READ_WRITE_REGISTERS_POLICY",
    "ProtocolId",
    EverParseErrorReasonOfResult(positionAfterModbusReadWriteRegistersPolicy0),
    EverParseGetValidatorErrorKind(positionAfterModbusReadWriteRegistersPolicy0),
    Ctxt,
    Input,
    positionAfterTransactionId);
  return positionAfterModbusReadWriteRegistersPolicy0;
}

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
)
{
  /* Validating field TransactionId */
  /* Checking that we have enough space for a UINT16BE, i.e., 2 bytes */
  BOOLEAN hasBytes0 = 2ULL <= (InputLength0 - StartPosition);
  uint64_t positionAfterModbusReadCoilsPolicy;
  if (hasBytes0)
  {
    positionAfterModbusReadCoilsPolicy = StartPosition + 2ULL;
  }
  else
  {
    positionAfterModbusReadCoilsPolicy =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  uint64_t res0;
  if (EverParseIsSuccess(positionAfterModbusReadCoilsPolicy))
  {
    res0 = positionAfterModbusReadCoilsPolicy;
  }
  else
  {
    ErrorHandlerFn("_MODBUS_READ_COILS_POLICY",
      "TransactionId",
      EverParseErrorReasonOfResult(positionAfterModbusReadCoilsPolicy),
      EverParseGetValidatorErrorKind(positionAfterModbusReadCoilsPolicy),
      Ctxt,
      Input,
      StartPosition);
    res0 = positionAfterModbusReadCoilsPolicy;
  }
  uint64_t positionAfterTransactionId = res0;
  if (EverParseIsError(positionAfterTransactionId))
  {
    return positionAfterTransactionId;
  }
  /* Checking that we have enough space for a UINT16BE, i.e., 2 bytes */
  BOOLEAN hasBytes1 = 2ULL <= (InputLength0 - positionAfterTransactionId);
  uint64_t positionAfterProtocolId;
  if (hasBytes1)
  {
    positionAfterProtocolId = positionAfterTransactionId + 2ULL;
  }
  else
  {
    positionAfterProtocolId =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        positionAfterTransactionId);
  }
  uint64_t positionAfterModbusReadCoilsPolicy0;
  if (EverParseIsError(positionAfterProtocolId))
  {
    positionAfterModbusReadCoilsPolicy0 = positionAfterProtocolId;
  }
  else
  {
    uint16_t protocolId = Load16Be(Input + (uint32_t)positionAfterTransactionId);
    BOOLEAN
    protocolIdConstraintIsOk =
      protocolId == (uint16_t)MODBUSTCP_V4_POLICYENFORCED____MODBUS_PROTOCOL_ID;
    uint64_t
    positionAfterProtocolId1 =
      EverParseCheckConstraintOk(protocolIdConstraintIsOk,
        positionAfterProtocolId);
    if (EverParseIsError(positionAfterProtocolId1))
    {
      positionAfterModbusReadCoilsPolicy0 = positionAfterProtocolId1;
    }
    else
    {
      /* Checking that we have enough space for a UINT16BE, i.e., 2 bytes */
      BOOLEAN hasBytes2 = 2ULL <= (InputLength0 - positionAfterProtocolId1);
      uint64_t positionAfterLength;
      if (hasBytes2)
      {
        positionAfterLength = positionAfterProtocolId1 + 2ULL;
      }
      else
      {
        positionAfterLength =
          EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
            positionAfterProtocolId1);
      }
      uint64_t positionAfterModbusReadCoilsPolicy1;
      if (EverParseIsError(positionAfterLength))
      {
        positionAfterModbusReadCoilsPolicy1 = positionAfterLength;
      }
      else
      {
        uint16_t length = Load16Be(Input + (uint32_t)positionAfterProtocolId1);
        BOOLEAN
        lengthConstraintIsOk =
          length == (uint16_t)6U &&
            InputLength ==
              (uint32_t)((uint32_t)length +
                (uint32_t)(uint16_t)MODBUSTCP_V4_POLICYENFORCED____MBAP_HEADER_PREFIX_SIZE);
        uint64_t
        positionAfterLength1 = EverParseCheckConstraintOk(lengthConstraintIsOk, positionAfterLength);
        if (EverParseIsError(positionAfterLength1))
        {
          positionAfterModbusReadCoilsPolicy1 = positionAfterLength1;
        }
        else
        {
          /* Validating field UnitId */
          /* Checking that we have enough space for a UINT8, i.e., 1 byte */
          BOOLEAN hasBytes3 = 1ULL <= (InputLength0 - positionAfterLength1);
          uint64_t positionAfterModbusReadCoilsPolicy2;
          if (hasBytes3)
          {
            positionAfterModbusReadCoilsPolicy2 = positionAfterLength1 + 1ULL;
          }
          else
          {
            positionAfterModbusReadCoilsPolicy2 =
              EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
                positionAfterLength1);
          }
          uint64_t res;
          if (EverParseIsSuccess(positionAfterModbusReadCoilsPolicy2))
          {
            res = positionAfterModbusReadCoilsPolicy2;
          }
          else
          {
            ErrorHandlerFn("_MODBUS_READ_COILS_POLICY",
              "UnitId",
              EverParseErrorReasonOfResult(positionAfterModbusReadCoilsPolicy2),
              EverParseGetValidatorErrorKind(positionAfterModbusReadCoilsPolicy2),
              Ctxt,
              Input,
              positionAfterLength1);
            res = positionAfterModbusReadCoilsPolicy2;
          }
          uint64_t positionAfterUnitId = res;
          if (EverParseIsError(positionAfterUnitId))
          {
            positionAfterModbusReadCoilsPolicy1 = positionAfterUnitId;
          }
          else
          {
            /* Checking that we have enough space for a UINT8, i.e., 1 byte */
            BOOLEAN hasBytes4 = 1ULL <= (InputLength0 - positionAfterUnitId);
            uint64_t positionAfterFunctionCode;
            if (hasBytes4)
            {
              positionAfterFunctionCode = positionAfterUnitId + 1ULL;
            }
            else
            {
              positionAfterFunctionCode =
                EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
                  positionAfterUnitId);
            }
            uint64_t positionAfterModbusReadCoilsPolicy3;
            if (EverParseIsError(positionAfterFunctionCode))
            {
              positionAfterModbusReadCoilsPolicy3 = positionAfterFunctionCode;
            }
            else
            {
              uint8_t functionCode = Input[(uint32_t)positionAfterUnitId];
              BOOLEAN
              functionCodeConstraintIsOk =
                functionCode == MODBUSTCP_V4_POLICYENFORCED____FC_READ_COILS;
              uint64_t
              positionAfterFunctionCode1 =
                EverParseCheckConstraintOk(functionCodeConstraintIsOk,
                  positionAfterFunctionCode);
              if (EverParseIsError(positionAfterFunctionCode1))
              {
                positionAfterModbusReadCoilsPolicy3 = positionAfterFunctionCode1;
              }
              else
              {
                /* Checking that we have enough space for a UINT16BE, i.e., 2 bytes */
                BOOLEAN hasBytes5 = 2ULL <= (InputLength0 - positionAfterFunctionCode1);
                uint64_t positionAfterStartAddress;
                if (hasBytes5)
                {
                  positionAfterStartAddress = positionAfterFunctionCode1 + 2ULL;
                }
                else
                {
                  positionAfterStartAddress =
                    EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
                      positionAfterFunctionCode1);
                }
                uint64_t positionAfterModbusReadCoilsPolicy4;
                if (EverParseIsError(positionAfterStartAddress))
                {
                  positionAfterModbusReadCoilsPolicy4 = positionAfterStartAddress;
                }
                else
                {
                  uint16_t startAddress = Load16Be(Input + (uint32_t)positionAfterFunctionCode1);
                  BOOLEAN
                  startAddressConstraintIsOk =
                    startAddress >= AllowedStart && startAddress <= AllowedEnd;
                  uint64_t
                  positionAfterStartAddress1 =
                    EverParseCheckConstraintOk(startAddressConstraintIsOk,
                      positionAfterStartAddress);
                  if (EverParseIsError(positionAfterStartAddress1))
                  {
                    positionAfterModbusReadCoilsPolicy4 = positionAfterStartAddress1;
                  }
                  else
                  {
                    /* Validating field Quantity */
                    /* Checking that we have enough space for a UINT16BE, i.e., 2 bytes */
                    BOOLEAN hasBytes = 2ULL <= (InputLength0 - positionAfterStartAddress1);
                    uint64_t positionAfterQuantity_refinement;
                    if (hasBytes)
                    {
                      positionAfterQuantity_refinement = positionAfterStartAddress1 + 2ULL;
                    }
                    else
                    {
                      positionAfterQuantity_refinement =
                        EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
                          positionAfterStartAddress1);
                    }
                    uint64_t positionAfterModbusReadCoilsPolicy5;
                    if (EverParseIsError(positionAfterQuantity_refinement))
                    {
                      positionAfterModbusReadCoilsPolicy5 = positionAfterQuantity_refinement;
                    }
                    else
                    {
                      /* reading field_value */
                      uint16_t
                      quantity_refinement = Load16Be(Input + (uint32_t)positionAfterStartAddress1);
                      /* start: checking constraint */
                      BOOLEAN
                      quantity_refinementConstraintIsOk =
                        quantity_refinement >= (uint16_t)1U &&
                          quantity_refinement <= MODBUSTCP_V4_POLICYENFORCED____MAX_READ_COILS
                        &&
                          ((uint32_t)quantity_refinement - (uint32_t)(uint16_t)1U) <=
                            ((uint32_t)AllowedEnd - (uint32_t)startAddress);
                      /* end: checking constraint */
                      positionAfterModbusReadCoilsPolicy5 =
                        EverParseCheckConstraintOk(quantity_refinementConstraintIsOk,
                          positionAfterQuantity_refinement);
                    }
                    if (EverParseIsSuccess(positionAfterModbusReadCoilsPolicy5))
                    {
                      positionAfterModbusReadCoilsPolicy4 = positionAfterModbusReadCoilsPolicy5;
                    }
                    else
                    {
                      ErrorHandlerFn("_MODBUS_READ_COILS_POLICY",
                        "Quantity.refinement",
                        EverParseErrorReasonOfResult(positionAfterModbusReadCoilsPolicy5),
                        EverParseGetValidatorErrorKind(positionAfterModbusReadCoilsPolicy5),
                        Ctxt,
                        Input,
                        positionAfterStartAddress1);
                      positionAfterModbusReadCoilsPolicy4 = positionAfterModbusReadCoilsPolicy5;
                    }
                  }
                }
                if (EverParseIsSuccess(positionAfterModbusReadCoilsPolicy4))
                {
                  positionAfterModbusReadCoilsPolicy3 = positionAfterModbusReadCoilsPolicy4;
                }
                else
                {
                  ErrorHandlerFn("_MODBUS_READ_COILS_POLICY",
                    "StartAddress",
                    EverParseErrorReasonOfResult(positionAfterModbusReadCoilsPolicy4),
                    EverParseGetValidatorErrorKind(positionAfterModbusReadCoilsPolicy4),
                    Ctxt,
                    Input,
                    positionAfterFunctionCode1);
                  positionAfterModbusReadCoilsPolicy3 = positionAfterModbusReadCoilsPolicy4;
                }
              }
            }
            if (EverParseIsSuccess(positionAfterModbusReadCoilsPolicy3))
            {
              positionAfterModbusReadCoilsPolicy1 = positionAfterModbusReadCoilsPolicy3;
            }
            else
            {
              ErrorHandlerFn("_MODBUS_READ_COILS_POLICY",
                "FunctionCode",
                EverParseErrorReasonOfResult(positionAfterModbusReadCoilsPolicy3),
                EverParseGetValidatorErrorKind(positionAfterModbusReadCoilsPolicy3),
                Ctxt,
                Input,
                positionAfterUnitId);
              positionAfterModbusReadCoilsPolicy1 = positionAfterModbusReadCoilsPolicy3;
            }
          }
        }
      }
      if (EverParseIsSuccess(positionAfterModbusReadCoilsPolicy1))
      {
        positionAfterModbusReadCoilsPolicy0 = positionAfterModbusReadCoilsPolicy1;
      }
      else
      {
        ErrorHandlerFn("_MODBUS_READ_COILS_POLICY",
          "Length",
          EverParseErrorReasonOfResult(positionAfterModbusReadCoilsPolicy1),
          EverParseGetValidatorErrorKind(positionAfterModbusReadCoilsPolicy1),
          Ctxt,
          Input,
          positionAfterProtocolId1);
        positionAfterModbusReadCoilsPolicy0 = positionAfterModbusReadCoilsPolicy1;
      }
    }
  }
  if (EverParseIsSuccess(positionAfterModbusReadCoilsPolicy0))
  {
    return positionAfterModbusReadCoilsPolicy0;
  }
  ErrorHandlerFn("_MODBUS_READ_COILS_POLICY",
    "ProtocolId",
    EverParseErrorReasonOfResult(positionAfterModbusReadCoilsPolicy0),
    EverParseGetValidatorErrorKind(positionAfterModbusReadCoilsPolicy0),
    Ctxt,
    Input,
    positionAfterTransactionId);
  return positionAfterModbusReadCoilsPolicy0;
}

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
)
{
  /* Validating field TransactionId */
  /* Checking that we have enough space for a UINT16BE, i.e., 2 bytes */
  BOOLEAN hasBytes0 = 2ULL <= (InputLength0 - StartPosition);
  uint64_t positionAfterModbusWriteSingleCoilPolicy;
  if (hasBytes0)
  {
    positionAfterModbusWriteSingleCoilPolicy = StartPosition + 2ULL;
  }
  else
  {
    positionAfterModbusWriteSingleCoilPolicy =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  uint64_t res0;
  if (EverParseIsSuccess(positionAfterModbusWriteSingleCoilPolicy))
  {
    res0 = positionAfterModbusWriteSingleCoilPolicy;
  }
  else
  {
    ErrorHandlerFn("_MODBUS_WRITE_SINGLE_COIL_POLICY",
      "TransactionId",
      EverParseErrorReasonOfResult(positionAfterModbusWriteSingleCoilPolicy),
      EverParseGetValidatorErrorKind(positionAfterModbusWriteSingleCoilPolicy),
      Ctxt,
      Input,
      StartPosition);
    res0 = positionAfterModbusWriteSingleCoilPolicy;
  }
  uint64_t positionAfterTransactionId = res0;
  if (EverParseIsError(positionAfterTransactionId))
  {
    return positionAfterTransactionId;
  }
  /* Checking that we have enough space for a UINT16BE, i.e., 2 bytes */
  BOOLEAN hasBytes1 = 2ULL <= (InputLength0 - positionAfterTransactionId);
  uint64_t positionAfterProtocolId;
  if (hasBytes1)
  {
    positionAfterProtocolId = positionAfterTransactionId + 2ULL;
  }
  else
  {
    positionAfterProtocolId =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        positionAfterTransactionId);
  }
  uint64_t positionAfterModbusWriteSingleCoilPolicy0;
  if (EverParseIsError(positionAfterProtocolId))
  {
    positionAfterModbusWriteSingleCoilPolicy0 = positionAfterProtocolId;
  }
  else
  {
    uint16_t protocolId = Load16Be(Input + (uint32_t)positionAfterTransactionId);
    BOOLEAN
    protocolIdConstraintIsOk =
      protocolId == (uint16_t)MODBUSTCP_V4_POLICYENFORCED____MODBUS_PROTOCOL_ID;
    uint64_t
    positionAfterProtocolId1 =
      EverParseCheckConstraintOk(protocolIdConstraintIsOk,
        positionAfterProtocolId);
    if (EverParseIsError(positionAfterProtocolId1))
    {
      positionAfterModbusWriteSingleCoilPolicy0 = positionAfterProtocolId1;
    }
    else
    {
      /* Checking that we have enough space for a UINT16BE, i.e., 2 bytes */
      BOOLEAN hasBytes2 = 2ULL <= (InputLength0 - positionAfterProtocolId1);
      uint64_t positionAfterLength;
      if (hasBytes2)
      {
        positionAfterLength = positionAfterProtocolId1 + 2ULL;
      }
      else
      {
        positionAfterLength =
          EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
            positionAfterProtocolId1);
      }
      uint64_t positionAfterModbusWriteSingleCoilPolicy1;
      if (EverParseIsError(positionAfterLength))
      {
        positionAfterModbusWriteSingleCoilPolicy1 = positionAfterLength;
      }
      else
      {
        uint16_t length = Load16Be(Input + (uint32_t)positionAfterProtocolId1);
        BOOLEAN
        lengthConstraintIsOk =
          length == (uint16_t)6U &&
            InputLength ==
              (uint32_t)((uint32_t)length +
                (uint32_t)(uint16_t)MODBUSTCP_V4_POLICYENFORCED____MBAP_HEADER_PREFIX_SIZE);
        uint64_t
        positionAfterLength1 = EverParseCheckConstraintOk(lengthConstraintIsOk, positionAfterLength);
        if (EverParseIsError(positionAfterLength1))
        {
          positionAfterModbusWriteSingleCoilPolicy1 = positionAfterLength1;
        }
        else
        {
          /* Validating field UnitId */
          /* Checking that we have enough space for a UINT8, i.e., 1 byte */
          BOOLEAN hasBytes3 = 1ULL <= (InputLength0 - positionAfterLength1);
          uint64_t positionAfterModbusWriteSingleCoilPolicy2;
          if (hasBytes3)
          {
            positionAfterModbusWriteSingleCoilPolicy2 = positionAfterLength1 + 1ULL;
          }
          else
          {
            positionAfterModbusWriteSingleCoilPolicy2 =
              EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
                positionAfterLength1);
          }
          uint64_t res;
          if (EverParseIsSuccess(positionAfterModbusWriteSingleCoilPolicy2))
          {
            res = positionAfterModbusWriteSingleCoilPolicy2;
          }
          else
          {
            ErrorHandlerFn("_MODBUS_WRITE_SINGLE_COIL_POLICY",
              "UnitId",
              EverParseErrorReasonOfResult(positionAfterModbusWriteSingleCoilPolicy2),
              EverParseGetValidatorErrorKind(positionAfterModbusWriteSingleCoilPolicy2),
              Ctxt,
              Input,
              positionAfterLength1);
            res = positionAfterModbusWriteSingleCoilPolicy2;
          }
          uint64_t positionAfterUnitId = res;
          if (EverParseIsError(positionAfterUnitId))
          {
            positionAfterModbusWriteSingleCoilPolicy1 = positionAfterUnitId;
          }
          else
          {
            /* Checking that we have enough space for a UINT8, i.e., 1 byte */
            BOOLEAN hasBytes4 = 1ULL <= (InputLength0 - positionAfterUnitId);
            uint64_t positionAfterFunctionCode;
            if (hasBytes4)
            {
              positionAfterFunctionCode = positionAfterUnitId + 1ULL;
            }
            else
            {
              positionAfterFunctionCode =
                EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
                  positionAfterUnitId);
            }
            uint64_t positionAfterModbusWriteSingleCoilPolicy3;
            if (EverParseIsError(positionAfterFunctionCode))
            {
              positionAfterModbusWriteSingleCoilPolicy3 = positionAfterFunctionCode;
            }
            else
            {
              uint8_t functionCode = Input[(uint32_t)positionAfterUnitId];
              BOOLEAN
              functionCodeConstraintIsOk =
                functionCode == MODBUSTCP_V4_POLICYENFORCED____FC_WRITE_SINGLE_COIL;
              uint64_t
              positionAfterFunctionCode1 =
                EverParseCheckConstraintOk(functionCodeConstraintIsOk,
                  positionAfterFunctionCode);
              if (EverParseIsError(positionAfterFunctionCode1))
              {
                positionAfterModbusWriteSingleCoilPolicy3 = positionAfterFunctionCode1;
              }
              else
              {
                /* Checking that we have enough space for a UINT16BE, i.e., 2 bytes */
                BOOLEAN hasBytes5 = 2ULL <= (InputLength0 - positionAfterFunctionCode1);
                uint64_t positionAfterOutputAddress;
                if (hasBytes5)
                {
                  positionAfterOutputAddress = positionAfterFunctionCode1 + 2ULL;
                }
                else
                {
                  positionAfterOutputAddress =
                    EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
                      positionAfterFunctionCode1);
                }
                uint64_t positionAfterModbusWriteSingleCoilPolicy4;
                if (EverParseIsError(positionAfterOutputAddress))
                {
                  positionAfterModbusWriteSingleCoilPolicy4 = positionAfterOutputAddress;
                }
                else
                {
                  uint16_t outputAddress = Load16Be(Input + (uint32_t)positionAfterFunctionCode1);
                  BOOLEAN
                  outputAddressConstraintIsOk =
                    outputAddress >= AllowedStart && outputAddress <= AllowedEnd;
                  uint64_t
                  positionAfterOutputAddress1 =
                    EverParseCheckConstraintOk(outputAddressConstraintIsOk,
                      positionAfterOutputAddress);
                  if (EverParseIsError(positionAfterOutputAddress1))
                  {
                    positionAfterModbusWriteSingleCoilPolicy4 = positionAfterOutputAddress1;
                  }
                  else
                  {
                    /* Validating field OutputValue */
                    /* Checking that we have enough space for a UINT16BE, i.e., 2 bytes */
                    BOOLEAN hasBytes = 2ULL <= (InputLength0 - positionAfterOutputAddress1);
                    uint64_t positionAfterOutputValue_refinement;
                    if (hasBytes)
                    {
                      positionAfterOutputValue_refinement = positionAfterOutputAddress1 + 2ULL;
                    }
                    else
                    {
                      positionAfterOutputValue_refinement =
                        EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
                          positionAfterOutputAddress1);
                    }
                    uint64_t positionAfterModbusWriteSingleCoilPolicy5;
                    if (EverParseIsError(positionAfterOutputValue_refinement))
                    {
                      positionAfterModbusWriteSingleCoilPolicy5 =
                        positionAfterOutputValue_refinement;
                    }
                    else
                    {
                      /* reading field_value */
                      uint16_t
                      outputValue_refinement =
                        Load16Be(Input + (uint32_t)positionAfterOutputAddress1);
                      /* start: checking constraint */
                      BOOLEAN
                      outputValue_refinementConstraintIsOk =
                        outputValue_refinement == MODBUSTCP_V4_POLICYENFORCED____COIL_ON ||
                          outputValue_refinement ==
                            (uint16_t)MODBUSTCP_V4_POLICYENFORCED____COIL_OFF;
                      /* end: checking constraint */
                      positionAfterModbusWriteSingleCoilPolicy5 =
                        EverParseCheckConstraintOk(outputValue_refinementConstraintIsOk,
                          positionAfterOutputValue_refinement);
                    }
                    if (EverParseIsSuccess(positionAfterModbusWriteSingleCoilPolicy5))
                    {
                      positionAfterModbusWriteSingleCoilPolicy4 =
                        positionAfterModbusWriteSingleCoilPolicy5;
                    }
                    else
                    {
                      ErrorHandlerFn("_MODBUS_WRITE_SINGLE_COIL_POLICY",
                        "OutputValue.refinement",
                        EverParseErrorReasonOfResult(positionAfterModbusWriteSingleCoilPolicy5),
                        EverParseGetValidatorErrorKind(positionAfterModbusWriteSingleCoilPolicy5),
                        Ctxt,
                        Input,
                        positionAfterOutputAddress1);
                      positionAfterModbusWriteSingleCoilPolicy4 =
                        positionAfterModbusWriteSingleCoilPolicy5;
                    }
                  }
                }
                if (EverParseIsSuccess(positionAfterModbusWriteSingleCoilPolicy4))
                {
                  positionAfterModbusWriteSingleCoilPolicy3 =
                    positionAfterModbusWriteSingleCoilPolicy4;
                }
                else
                {
                  ErrorHandlerFn("_MODBUS_WRITE_SINGLE_COIL_POLICY",
                    "OutputAddress",
                    EverParseErrorReasonOfResult(positionAfterModbusWriteSingleCoilPolicy4),
                    EverParseGetValidatorErrorKind(positionAfterModbusWriteSingleCoilPolicy4),
                    Ctxt,
                    Input,
                    positionAfterFunctionCode1);
                  positionAfterModbusWriteSingleCoilPolicy3 =
                    positionAfterModbusWriteSingleCoilPolicy4;
                }
              }
            }
            if (EverParseIsSuccess(positionAfterModbusWriteSingleCoilPolicy3))
            {
              positionAfterModbusWriteSingleCoilPolicy1 = positionAfterModbusWriteSingleCoilPolicy3;
            }
            else
            {
              ErrorHandlerFn("_MODBUS_WRITE_SINGLE_COIL_POLICY",
                "FunctionCode",
                EverParseErrorReasonOfResult(positionAfterModbusWriteSingleCoilPolicy3),
                EverParseGetValidatorErrorKind(positionAfterModbusWriteSingleCoilPolicy3),
                Ctxt,
                Input,
                positionAfterUnitId);
              positionAfterModbusWriteSingleCoilPolicy1 = positionAfterModbusWriteSingleCoilPolicy3;
            }
          }
        }
      }
      if (EverParseIsSuccess(positionAfterModbusWriteSingleCoilPolicy1))
      {
        positionAfterModbusWriteSingleCoilPolicy0 = positionAfterModbusWriteSingleCoilPolicy1;
      }
      else
      {
        ErrorHandlerFn("_MODBUS_WRITE_SINGLE_COIL_POLICY",
          "Length",
          EverParseErrorReasonOfResult(positionAfterModbusWriteSingleCoilPolicy1),
          EverParseGetValidatorErrorKind(positionAfterModbusWriteSingleCoilPolicy1),
          Ctxt,
          Input,
          positionAfterProtocolId1);
        positionAfterModbusWriteSingleCoilPolicy0 = positionAfterModbusWriteSingleCoilPolicy1;
      }
    }
  }
  if (EverParseIsSuccess(positionAfterModbusWriteSingleCoilPolicy0))
  {
    return positionAfterModbusWriteSingleCoilPolicy0;
  }
  ErrorHandlerFn("_MODBUS_WRITE_SINGLE_COIL_POLICY",
    "ProtocolId",
    EverParseErrorReasonOfResult(positionAfterModbusWriteSingleCoilPolicy0),
    EverParseGetValidatorErrorKind(positionAfterModbusWriteSingleCoilPolicy0),
    Ctxt,
    Input,
    positionAfterTransactionId);
  return positionAfterModbusWriteSingleCoilPolicy0;
}

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
)
{
  /* Validating field TransactionId */
  /* Checking that we have enough space for a UINT16BE, i.e., 2 bytes */
  BOOLEAN hasBytes0 = 2ULL <= (InputLength0 - StartPosition);
  uint64_t positionAfterModbusWriteMultipleCoilsPolicy;
  if (hasBytes0)
  {
    positionAfterModbusWriteMultipleCoilsPolicy = StartPosition + 2ULL;
  }
  else
  {
    positionAfterModbusWriteMultipleCoilsPolicy =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  uint64_t res0;
  if (EverParseIsSuccess(positionAfterModbusWriteMultipleCoilsPolicy))
  {
    res0 = positionAfterModbusWriteMultipleCoilsPolicy;
  }
  else
  {
    ErrorHandlerFn("_MODBUS_WRITE_MULTIPLE_COILS_POLICY",
      "TransactionId",
      EverParseErrorReasonOfResult(positionAfterModbusWriteMultipleCoilsPolicy),
      EverParseGetValidatorErrorKind(positionAfterModbusWriteMultipleCoilsPolicy),
      Ctxt,
      Input,
      StartPosition);
    res0 = positionAfterModbusWriteMultipleCoilsPolicy;
  }
  uint64_t positionAfterTransactionId = res0;
  if (EverParseIsError(positionAfterTransactionId))
  {
    return positionAfterTransactionId;
  }
  /* Checking that we have enough space for a UINT16BE, i.e., 2 bytes */
  BOOLEAN hasBytes1 = 2ULL <= (InputLength0 - positionAfterTransactionId);
  uint64_t positionAfterProtocolId;
  if (hasBytes1)
  {
    positionAfterProtocolId = positionAfterTransactionId + 2ULL;
  }
  else
  {
    positionAfterProtocolId =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        positionAfterTransactionId);
  }
  uint64_t positionAfterModbusWriteMultipleCoilsPolicy0;
  if (EverParseIsError(positionAfterProtocolId))
  {
    positionAfterModbusWriteMultipleCoilsPolicy0 = positionAfterProtocolId;
  }
  else
  {
    uint16_t protocolId = Load16Be(Input + (uint32_t)positionAfterTransactionId);
    BOOLEAN
    protocolIdConstraintIsOk =
      protocolId == (uint16_t)MODBUSTCP_V4_POLICYENFORCED____MODBUS_PROTOCOL_ID;
    uint64_t
    positionAfterProtocolId1 =
      EverParseCheckConstraintOk(protocolIdConstraintIsOk,
        positionAfterProtocolId);
    if (EverParseIsError(positionAfterProtocolId1))
    {
      positionAfterModbusWriteMultipleCoilsPolicy0 = positionAfterProtocolId1;
    }
    else
    {
      /* Checking that we have enough space for a UINT16BE, i.e., 2 bytes */
      BOOLEAN hasBytes2 = 2ULL <= (InputLength0 - positionAfterProtocolId1);
      uint64_t positionAfterLength;
      if (hasBytes2)
      {
        positionAfterLength = positionAfterProtocolId1 + 2ULL;
      }
      else
      {
        positionAfterLength =
          EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
            positionAfterProtocolId1);
      }
      uint64_t positionAfterModbusWriteMultipleCoilsPolicy1;
      if (EverParseIsError(positionAfterLength))
      {
        positionAfterModbusWriteMultipleCoilsPolicy1 = positionAfterLength;
      }
      else
      {
        uint16_t length = Load16Be(Input + (uint32_t)positionAfterProtocolId1);
        BOOLEAN
        lengthConstraintIsOk =
          length >= (uint16_t)8U && length <= (uint16_t)254U &&
            InputLength ==
              (uint32_t)((uint32_t)length +
                (uint32_t)(uint16_t)MODBUSTCP_V4_POLICYENFORCED____MBAP_HEADER_PREFIX_SIZE);
        uint64_t
        positionAfterLength1 = EverParseCheckConstraintOk(lengthConstraintIsOk, positionAfterLength);
        if (EverParseIsError(positionAfterLength1))
        {
          positionAfterModbusWriteMultipleCoilsPolicy1 = positionAfterLength1;
        }
        else
        {
          /* Validating field UnitId */
          /* Checking that we have enough space for a UINT8, i.e., 1 byte */
          BOOLEAN hasBytes3 = 1ULL <= (InputLength0 - positionAfterLength1);
          uint64_t positionAfterModbusWriteMultipleCoilsPolicy2;
          if (hasBytes3)
          {
            positionAfterModbusWriteMultipleCoilsPolicy2 = positionAfterLength1 + 1ULL;
          }
          else
          {
            positionAfterModbusWriteMultipleCoilsPolicy2 =
              EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
                positionAfterLength1);
          }
          uint64_t res1;
          if (EverParseIsSuccess(positionAfterModbusWriteMultipleCoilsPolicy2))
          {
            res1 = positionAfterModbusWriteMultipleCoilsPolicy2;
          }
          else
          {
            ErrorHandlerFn("_MODBUS_WRITE_MULTIPLE_COILS_POLICY",
              "UnitId",
              EverParseErrorReasonOfResult(positionAfterModbusWriteMultipleCoilsPolicy2),
              EverParseGetValidatorErrorKind(positionAfterModbusWriteMultipleCoilsPolicy2),
              Ctxt,
              Input,
              positionAfterLength1);
            res1 = positionAfterModbusWriteMultipleCoilsPolicy2;
          }
          uint64_t positionAfterUnitId = res1;
          if (EverParseIsError(positionAfterUnitId))
          {
            positionAfterModbusWriteMultipleCoilsPolicy1 = positionAfterUnitId;
          }
          else
          {
            /* Checking that we have enough space for a UINT8, i.e., 1 byte */
            BOOLEAN hasBytes4 = 1ULL <= (InputLength0 - positionAfterUnitId);
            uint64_t positionAfterFunctionCode;
            if (hasBytes4)
            {
              positionAfterFunctionCode = positionAfterUnitId + 1ULL;
            }
            else
            {
              positionAfterFunctionCode =
                EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
                  positionAfterUnitId);
            }
            uint64_t positionAfterModbusWriteMultipleCoilsPolicy3;
            if (EverParseIsError(positionAfterFunctionCode))
            {
              positionAfterModbusWriteMultipleCoilsPolicy3 = positionAfterFunctionCode;
            }
            else
            {
              uint8_t functionCode = Input[(uint32_t)positionAfterUnitId];
              BOOLEAN
              functionCodeConstraintIsOk =
                functionCode == MODBUSTCP_V4_POLICYENFORCED____FC_WRITE_MULTIPLE_COILS;
              uint64_t
              positionAfterFunctionCode1 =
                EverParseCheckConstraintOk(functionCodeConstraintIsOk,
                  positionAfterFunctionCode);
              if (EverParseIsError(positionAfterFunctionCode1))
              {
                positionAfterModbusWriteMultipleCoilsPolicy3 = positionAfterFunctionCode1;
              }
              else
              {
                /* Checking that we have enough space for a UINT16BE, i.e., 2 bytes */
                BOOLEAN hasBytes5 = 2ULL <= (InputLength0 - positionAfterFunctionCode1);
                uint64_t positionAfterStartAddress;
                if (hasBytes5)
                {
                  positionAfterStartAddress = positionAfterFunctionCode1 + 2ULL;
                }
                else
                {
                  positionAfterStartAddress =
                    EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
                      positionAfterFunctionCode1);
                }
                uint64_t positionAfterModbusWriteMultipleCoilsPolicy4;
                if (EverParseIsError(positionAfterStartAddress))
                {
                  positionAfterModbusWriteMultipleCoilsPolicy4 = positionAfterStartAddress;
                }
                else
                {
                  uint16_t startAddress = Load16Be(Input + (uint32_t)positionAfterFunctionCode1);
                  BOOLEAN
                  startAddressConstraintIsOk =
                    startAddress >= AllowedStart && startAddress <= AllowedEnd;
                  uint64_t
                  positionAfterStartAddress1 =
                    EverParseCheckConstraintOk(startAddressConstraintIsOk,
                      positionAfterStartAddress);
                  if (EverParseIsError(positionAfterStartAddress1))
                  {
                    positionAfterModbusWriteMultipleCoilsPolicy4 = positionAfterStartAddress1;
                  }
                  else
                  {
                    /* Checking that we have enough space for a UINT16BE, i.e., 2 bytes */
                    BOOLEAN hasBytes6 = 2ULL <= (InputLength0 - positionAfterStartAddress1);
                    uint64_t positionAfterQuantity;
                    if (hasBytes6)
                    {
                      positionAfterQuantity = positionAfterStartAddress1 + 2ULL;
                    }
                    else
                    {
                      positionAfterQuantity =
                        EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
                          positionAfterStartAddress1);
                    }
                    uint64_t positionAfterModbusWriteMultipleCoilsPolicy5;
                    if (EverParseIsError(positionAfterQuantity))
                    {
                      positionAfterModbusWriteMultipleCoilsPolicy5 = positionAfterQuantity;
                    }
                    else
                    {
                      uint16_t quantity = Load16Be(Input + (uint32_t)positionAfterStartAddress1);
                      BOOLEAN
                      quantityConstraintIsOk =
                        quantity >= (uint16_t)1U &&
                          quantity <= MODBUSTCP_V4_POLICYENFORCED____MAX_WRITE_COILS
                        &&
                          ((uint32_t)quantity - (uint32_t)(uint16_t)1U) <=
                            ((uint32_t)AllowedEnd - (uint32_t)startAddress);
                      uint64_t
                      positionAfterQuantity1 =
                        EverParseCheckConstraintOk(quantityConstraintIsOk,
                          positionAfterQuantity);
                      if (EverParseIsError(positionAfterQuantity1))
                      {
                        positionAfterModbusWriteMultipleCoilsPolicy5 = positionAfterQuantity1;
                      }
                      else
                      {
                        /* Checking that we have enough space for a UINT8, i.e., 1 byte */
                        BOOLEAN hasBytes7 = 1ULL <= (InputLength0 - positionAfterQuantity1);
                        uint64_t positionAfterByteCount;
                        if (hasBytes7)
                        {
                          positionAfterByteCount = positionAfterQuantity1 + 1ULL;
                        }
                        else
                        {
                          positionAfterByteCount =
                            EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
                              positionAfterQuantity1);
                        }
                        uint64_t positionAfterModbusWriteMultipleCoilsPolicy6;
                        if (EverParseIsError(positionAfterByteCount))
                        {
                          positionAfterModbusWriteMultipleCoilsPolicy6 = positionAfterByteCount;
                        }
                        else
                        {
                          uint8_t byteCount = Input[(uint32_t)positionAfterQuantity1];
                          BOOLEAN
                          byteCountConstraintIsOk =
                            (uint16_t)byteCount ==
                              (((uint32_t)quantity + (uint32_t)(uint16_t)7U) & 0xFFFFU) /
                                (uint32_t)(uint16_t)8U
                            && length == (uint16_t)(7U + (uint32_t)byteCount);
                          uint64_t
                          positionAfterByteCount1 =
                            EverParseCheckConstraintOk(byteCountConstraintIsOk,
                              positionAfterByteCount);
                          if (EverParseIsError(positionAfterByteCount1))
                          {
                            positionAfterModbusWriteMultipleCoilsPolicy6 = positionAfterByteCount1;
                          }
                          else
                          {
                            /* Validating field CoilValues */
                            BOOLEAN
                            hasBytes =
                              (uint64_t)(uint32_t)byteCount <=
                                (InputLength0 - positionAfterByteCount1);
                            uint64_t res;
                            if (hasBytes)
                            {
                              res = positionAfterByteCount1 + (uint64_t)(uint32_t)byteCount;
                            }
                            else
                            {
                              res =
                                EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
                                  positionAfterByteCount1);
                            }
                            uint64_t positionAfterModbusWriteMultipleCoilsPolicy7 = res;
                            if (EverParseIsSuccess(positionAfterModbusWriteMultipleCoilsPolicy7))
                            {
                              positionAfterModbusWriteMultipleCoilsPolicy6 =
                                positionAfterModbusWriteMultipleCoilsPolicy7;
                            }
                            else
                            {
                              ErrorHandlerFn("_MODBUS_WRITE_MULTIPLE_COILS_POLICY",
                                "CoilValues",
                                EverParseErrorReasonOfResult(positionAfterModbusWriteMultipleCoilsPolicy7),
                                EverParseGetValidatorErrorKind(positionAfterModbusWriteMultipleCoilsPolicy7),
                                Ctxt,
                                Input,
                                positionAfterByteCount1);
                              positionAfterModbusWriteMultipleCoilsPolicy6 =
                                positionAfterModbusWriteMultipleCoilsPolicy7;
                            }
                          }
                        }
                        if (EverParseIsSuccess(positionAfterModbusWriteMultipleCoilsPolicy6))
                        {
                          positionAfterModbusWriteMultipleCoilsPolicy5 =
                            positionAfterModbusWriteMultipleCoilsPolicy6;
                        }
                        else
                        {
                          ErrorHandlerFn("_MODBUS_WRITE_MULTIPLE_COILS_POLICY",
                            "ByteCount",
                            EverParseErrorReasonOfResult(positionAfterModbusWriteMultipleCoilsPolicy6),
                            EverParseGetValidatorErrorKind(positionAfterModbusWriteMultipleCoilsPolicy6),
                            Ctxt,
                            Input,
                            positionAfterQuantity1);
                          positionAfterModbusWriteMultipleCoilsPolicy5 =
                            positionAfterModbusWriteMultipleCoilsPolicy6;
                        }
                      }
                    }
                    if (EverParseIsSuccess(positionAfterModbusWriteMultipleCoilsPolicy5))
                    {
                      positionAfterModbusWriteMultipleCoilsPolicy4 =
                        positionAfterModbusWriteMultipleCoilsPolicy5;
                    }
                    else
                    {
                      ErrorHandlerFn("_MODBUS_WRITE_MULTIPLE_COILS_POLICY",
                        "Quantity",
                        EverParseErrorReasonOfResult(positionAfterModbusWriteMultipleCoilsPolicy5),
                        EverParseGetValidatorErrorKind(positionAfterModbusWriteMultipleCoilsPolicy5),
                        Ctxt,
                        Input,
                        positionAfterStartAddress1);
                      positionAfterModbusWriteMultipleCoilsPolicy4 =
                        positionAfterModbusWriteMultipleCoilsPolicy5;
                    }
                  }
                }
                if (EverParseIsSuccess(positionAfterModbusWriteMultipleCoilsPolicy4))
                {
                  positionAfterModbusWriteMultipleCoilsPolicy3 =
                    positionAfterModbusWriteMultipleCoilsPolicy4;
                }
                else
                {
                  ErrorHandlerFn("_MODBUS_WRITE_MULTIPLE_COILS_POLICY",
                    "StartAddress",
                    EverParseErrorReasonOfResult(positionAfterModbusWriteMultipleCoilsPolicy4),
                    EverParseGetValidatorErrorKind(positionAfterModbusWriteMultipleCoilsPolicy4),
                    Ctxt,
                    Input,
                    positionAfterFunctionCode1);
                  positionAfterModbusWriteMultipleCoilsPolicy3 =
                    positionAfterModbusWriteMultipleCoilsPolicy4;
                }
              }
            }
            if (EverParseIsSuccess(positionAfterModbusWriteMultipleCoilsPolicy3))
            {
              positionAfterModbusWriteMultipleCoilsPolicy1 =
                positionAfterModbusWriteMultipleCoilsPolicy3;
            }
            else
            {
              ErrorHandlerFn("_MODBUS_WRITE_MULTIPLE_COILS_POLICY",
                "FunctionCode",
                EverParseErrorReasonOfResult(positionAfterModbusWriteMultipleCoilsPolicy3),
                EverParseGetValidatorErrorKind(positionAfterModbusWriteMultipleCoilsPolicy3),
                Ctxt,
                Input,
                positionAfterUnitId);
              positionAfterModbusWriteMultipleCoilsPolicy1 =
                positionAfterModbusWriteMultipleCoilsPolicy3;
            }
          }
        }
      }
      if (EverParseIsSuccess(positionAfterModbusWriteMultipleCoilsPolicy1))
      {
        positionAfterModbusWriteMultipleCoilsPolicy0 = positionAfterModbusWriteMultipleCoilsPolicy1;
      }
      else
      {
        ErrorHandlerFn("_MODBUS_WRITE_MULTIPLE_COILS_POLICY",
          "Length",
          EverParseErrorReasonOfResult(positionAfterModbusWriteMultipleCoilsPolicy1),
          EverParseGetValidatorErrorKind(positionAfterModbusWriteMultipleCoilsPolicy1),
          Ctxt,
          Input,
          positionAfterProtocolId1);
        positionAfterModbusWriteMultipleCoilsPolicy0 = positionAfterModbusWriteMultipleCoilsPolicy1;
      }
    }
  }
  if (EverParseIsSuccess(positionAfterModbusWriteMultipleCoilsPolicy0))
  {
    return positionAfterModbusWriteMultipleCoilsPolicy0;
  }
  ErrorHandlerFn("_MODBUS_WRITE_MULTIPLE_COILS_POLICY",
    "ProtocolId",
    EverParseErrorReasonOfResult(positionAfterModbusWriteMultipleCoilsPolicy0),
    EverParseGetValidatorErrorKind(positionAfterModbusWriteMultipleCoilsPolicy0),
    Ctxt,
    Input,
    positionAfterTransactionId);
  return positionAfterModbusWriteMultipleCoilsPolicy0;
}

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
)
{
  /* Validating field TransactionId */
  /* Checking that we have enough space for a UINT16BE, i.e., 2 bytes */
  BOOLEAN hasBytes0 = 2ULL <= (InputLength0 - StartPosition);
  uint64_t positionAfterModbusReadDiscreteInputsPolicy;
  if (hasBytes0)
  {
    positionAfterModbusReadDiscreteInputsPolicy = StartPosition + 2ULL;
  }
  else
  {
    positionAfterModbusReadDiscreteInputsPolicy =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  uint64_t res0;
  if (EverParseIsSuccess(positionAfterModbusReadDiscreteInputsPolicy))
  {
    res0 = positionAfterModbusReadDiscreteInputsPolicy;
  }
  else
  {
    ErrorHandlerFn("_MODBUS_READ_DISCRETE_INPUTS_POLICY",
      "TransactionId",
      EverParseErrorReasonOfResult(positionAfterModbusReadDiscreteInputsPolicy),
      EverParseGetValidatorErrorKind(positionAfterModbusReadDiscreteInputsPolicy),
      Ctxt,
      Input,
      StartPosition);
    res0 = positionAfterModbusReadDiscreteInputsPolicy;
  }
  uint64_t positionAfterTransactionId = res0;
  if (EverParseIsError(positionAfterTransactionId))
  {
    return positionAfterTransactionId;
  }
  /* Checking that we have enough space for a UINT16BE, i.e., 2 bytes */
  BOOLEAN hasBytes1 = 2ULL <= (InputLength0 - positionAfterTransactionId);
  uint64_t positionAfterProtocolId;
  if (hasBytes1)
  {
    positionAfterProtocolId = positionAfterTransactionId + 2ULL;
  }
  else
  {
    positionAfterProtocolId =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        positionAfterTransactionId);
  }
  uint64_t positionAfterModbusReadDiscreteInputsPolicy0;
  if (EverParseIsError(positionAfterProtocolId))
  {
    positionAfterModbusReadDiscreteInputsPolicy0 = positionAfterProtocolId;
  }
  else
  {
    uint16_t protocolId = Load16Be(Input + (uint32_t)positionAfterTransactionId);
    BOOLEAN
    protocolIdConstraintIsOk =
      protocolId == (uint16_t)MODBUSTCP_V4_POLICYENFORCED____MODBUS_PROTOCOL_ID;
    uint64_t
    positionAfterProtocolId1 =
      EverParseCheckConstraintOk(protocolIdConstraintIsOk,
        positionAfterProtocolId);
    if (EverParseIsError(positionAfterProtocolId1))
    {
      positionAfterModbusReadDiscreteInputsPolicy0 = positionAfterProtocolId1;
    }
    else
    {
      /* Checking that we have enough space for a UINT16BE, i.e., 2 bytes */
      BOOLEAN hasBytes2 = 2ULL <= (InputLength0 - positionAfterProtocolId1);
      uint64_t positionAfterLength;
      if (hasBytes2)
      {
        positionAfterLength = positionAfterProtocolId1 + 2ULL;
      }
      else
      {
        positionAfterLength =
          EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
            positionAfterProtocolId1);
      }
      uint64_t positionAfterModbusReadDiscreteInputsPolicy1;
      if (EverParseIsError(positionAfterLength))
      {
        positionAfterModbusReadDiscreteInputsPolicy1 = positionAfterLength;
      }
      else
      {
        uint16_t length = Load16Be(Input + (uint32_t)positionAfterProtocolId1);
        BOOLEAN
        lengthConstraintIsOk =
          length == (uint16_t)6U &&
            InputLength ==
              (uint32_t)((uint32_t)length +
                (uint32_t)(uint16_t)MODBUSTCP_V4_POLICYENFORCED____MBAP_HEADER_PREFIX_SIZE);
        uint64_t
        positionAfterLength1 = EverParseCheckConstraintOk(lengthConstraintIsOk, positionAfterLength);
        if (EverParseIsError(positionAfterLength1))
        {
          positionAfterModbusReadDiscreteInputsPolicy1 = positionAfterLength1;
        }
        else
        {
          /* Validating field UnitId */
          /* Checking that we have enough space for a UINT8, i.e., 1 byte */
          BOOLEAN hasBytes3 = 1ULL <= (InputLength0 - positionAfterLength1);
          uint64_t positionAfterModbusReadDiscreteInputsPolicy2;
          if (hasBytes3)
          {
            positionAfterModbusReadDiscreteInputsPolicy2 = positionAfterLength1 + 1ULL;
          }
          else
          {
            positionAfterModbusReadDiscreteInputsPolicy2 =
              EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
                positionAfterLength1);
          }
          uint64_t res;
          if (EverParseIsSuccess(positionAfterModbusReadDiscreteInputsPolicy2))
          {
            res = positionAfterModbusReadDiscreteInputsPolicy2;
          }
          else
          {
            ErrorHandlerFn("_MODBUS_READ_DISCRETE_INPUTS_POLICY",
              "UnitId",
              EverParseErrorReasonOfResult(positionAfterModbusReadDiscreteInputsPolicy2),
              EverParseGetValidatorErrorKind(positionAfterModbusReadDiscreteInputsPolicy2),
              Ctxt,
              Input,
              positionAfterLength1);
            res = positionAfterModbusReadDiscreteInputsPolicy2;
          }
          uint64_t positionAfterUnitId = res;
          if (EverParseIsError(positionAfterUnitId))
          {
            positionAfterModbusReadDiscreteInputsPolicy1 = positionAfterUnitId;
          }
          else
          {
            /* Checking that we have enough space for a UINT8, i.e., 1 byte */
            BOOLEAN hasBytes4 = 1ULL <= (InputLength0 - positionAfterUnitId);
            uint64_t positionAfterFunctionCode;
            if (hasBytes4)
            {
              positionAfterFunctionCode = positionAfterUnitId + 1ULL;
            }
            else
            {
              positionAfterFunctionCode =
                EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
                  positionAfterUnitId);
            }
            uint64_t positionAfterModbusReadDiscreteInputsPolicy3;
            if (EverParseIsError(positionAfterFunctionCode))
            {
              positionAfterModbusReadDiscreteInputsPolicy3 = positionAfterFunctionCode;
            }
            else
            {
              uint8_t functionCode = Input[(uint32_t)positionAfterUnitId];
              BOOLEAN
              functionCodeConstraintIsOk =
                functionCode == MODBUSTCP_V4_POLICYENFORCED____FC_READ_DISCRETE_INPUTS;
              uint64_t
              positionAfterFunctionCode1 =
                EverParseCheckConstraintOk(functionCodeConstraintIsOk,
                  positionAfterFunctionCode);
              if (EverParseIsError(positionAfterFunctionCode1))
              {
                positionAfterModbusReadDiscreteInputsPolicy3 = positionAfterFunctionCode1;
              }
              else
              {
                /* Checking that we have enough space for a UINT16BE, i.e., 2 bytes */
                BOOLEAN hasBytes5 = 2ULL <= (InputLength0 - positionAfterFunctionCode1);
                uint64_t positionAfterStartAddress;
                if (hasBytes5)
                {
                  positionAfterStartAddress = positionAfterFunctionCode1 + 2ULL;
                }
                else
                {
                  positionAfterStartAddress =
                    EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
                      positionAfterFunctionCode1);
                }
                uint64_t positionAfterModbusReadDiscreteInputsPolicy4;
                if (EverParseIsError(positionAfterStartAddress))
                {
                  positionAfterModbusReadDiscreteInputsPolicy4 = positionAfterStartAddress;
                }
                else
                {
                  uint16_t startAddress = Load16Be(Input + (uint32_t)positionAfterFunctionCode1);
                  BOOLEAN
                  startAddressConstraintIsOk =
                    startAddress >= AllowedStart && startAddress <= AllowedEnd;
                  uint64_t
                  positionAfterStartAddress1 =
                    EverParseCheckConstraintOk(startAddressConstraintIsOk,
                      positionAfterStartAddress);
                  if (EverParseIsError(positionAfterStartAddress1))
                  {
                    positionAfterModbusReadDiscreteInputsPolicy4 = positionAfterStartAddress1;
                  }
                  else
                  {
                    /* Validating field Quantity */
                    /* Checking that we have enough space for a UINT16BE, i.e., 2 bytes */
                    BOOLEAN hasBytes = 2ULL <= (InputLength0 - positionAfterStartAddress1);
                    uint64_t positionAfterQuantity_refinement;
                    if (hasBytes)
                    {
                      positionAfterQuantity_refinement = positionAfterStartAddress1 + 2ULL;
                    }
                    else
                    {
                      positionAfterQuantity_refinement =
                        EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
                          positionAfterStartAddress1);
                    }
                    uint64_t positionAfterModbusReadDiscreteInputsPolicy5;
                    if (EverParseIsError(positionAfterQuantity_refinement))
                    {
                      positionAfterModbusReadDiscreteInputsPolicy5 =
                        positionAfterQuantity_refinement;
                    }
                    else
                    {
                      /* reading field_value */
                      uint16_t
                      quantity_refinement = Load16Be(Input + (uint32_t)positionAfterStartAddress1);
                      /* start: checking constraint */
                      BOOLEAN
                      quantity_refinementConstraintIsOk =
                        quantity_refinement >= (uint16_t)1U &&
                          quantity_refinement <=
                            MODBUSTCP_V4_POLICYENFORCED____MAX_READ_DISCRETE_INPUTS
                        &&
                          ((uint32_t)quantity_refinement - (uint32_t)(uint16_t)1U) <=
                            ((uint32_t)AllowedEnd - (uint32_t)startAddress);
                      /* end: checking constraint */
                      positionAfterModbusReadDiscreteInputsPolicy5 =
                        EverParseCheckConstraintOk(quantity_refinementConstraintIsOk,
                          positionAfterQuantity_refinement);
                    }
                    if (EverParseIsSuccess(positionAfterModbusReadDiscreteInputsPolicy5))
                    {
                      positionAfterModbusReadDiscreteInputsPolicy4 =
                        positionAfterModbusReadDiscreteInputsPolicy5;
                    }
                    else
                    {
                      ErrorHandlerFn("_MODBUS_READ_DISCRETE_INPUTS_POLICY",
                        "Quantity.refinement",
                        EverParseErrorReasonOfResult(positionAfterModbusReadDiscreteInputsPolicy5),
                        EverParseGetValidatorErrorKind(positionAfterModbusReadDiscreteInputsPolicy5),
                        Ctxt,
                        Input,
                        positionAfterStartAddress1);
                      positionAfterModbusReadDiscreteInputsPolicy4 =
                        positionAfterModbusReadDiscreteInputsPolicy5;
                    }
                  }
                }
                if (EverParseIsSuccess(positionAfterModbusReadDiscreteInputsPolicy4))
                {
                  positionAfterModbusReadDiscreteInputsPolicy3 =
                    positionAfterModbusReadDiscreteInputsPolicy4;
                }
                else
                {
                  ErrorHandlerFn("_MODBUS_READ_DISCRETE_INPUTS_POLICY",
                    "StartAddress",
                    EverParseErrorReasonOfResult(positionAfterModbusReadDiscreteInputsPolicy4),
                    EverParseGetValidatorErrorKind(positionAfterModbusReadDiscreteInputsPolicy4),
                    Ctxt,
                    Input,
                    positionAfterFunctionCode1);
                  positionAfterModbusReadDiscreteInputsPolicy3 =
                    positionAfterModbusReadDiscreteInputsPolicy4;
                }
              }
            }
            if (EverParseIsSuccess(positionAfterModbusReadDiscreteInputsPolicy3))
            {
              positionAfterModbusReadDiscreteInputsPolicy1 =
                positionAfterModbusReadDiscreteInputsPolicy3;
            }
            else
            {
              ErrorHandlerFn("_MODBUS_READ_DISCRETE_INPUTS_POLICY",
                "FunctionCode",
                EverParseErrorReasonOfResult(positionAfterModbusReadDiscreteInputsPolicy3),
                EverParseGetValidatorErrorKind(positionAfterModbusReadDiscreteInputsPolicy3),
                Ctxt,
                Input,
                positionAfterUnitId);
              positionAfterModbusReadDiscreteInputsPolicy1 =
                positionAfterModbusReadDiscreteInputsPolicy3;
            }
          }
        }
      }
      if (EverParseIsSuccess(positionAfterModbusReadDiscreteInputsPolicy1))
      {
        positionAfterModbusReadDiscreteInputsPolicy0 = positionAfterModbusReadDiscreteInputsPolicy1;
      }
      else
      {
        ErrorHandlerFn("_MODBUS_READ_DISCRETE_INPUTS_POLICY",
          "Length",
          EverParseErrorReasonOfResult(positionAfterModbusReadDiscreteInputsPolicy1),
          EverParseGetValidatorErrorKind(positionAfterModbusReadDiscreteInputsPolicy1),
          Ctxt,
          Input,
          positionAfterProtocolId1);
        positionAfterModbusReadDiscreteInputsPolicy0 = positionAfterModbusReadDiscreteInputsPolicy1;
      }
    }
  }
  if (EverParseIsSuccess(positionAfterModbusReadDiscreteInputsPolicy0))
  {
    return positionAfterModbusReadDiscreteInputsPolicy0;
  }
  ErrorHandlerFn("_MODBUS_READ_DISCRETE_INPUTS_POLICY",
    "ProtocolId",
    EverParseErrorReasonOfResult(positionAfterModbusReadDiscreteInputsPolicy0),
    EverParseGetValidatorErrorKind(positionAfterModbusReadDiscreteInputsPolicy0),
    Ctxt,
    Input,
    positionAfterTransactionId);
  return positionAfterModbusReadDiscreteInputsPolicy0;
}

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
)
{
  /* Validating field TransactionId */
  /* Checking that we have enough space for a UINT16BE, i.e., 2 bytes */
  BOOLEAN hasBytes0 = 2ULL <= (InputLength0 - StartPosition);
  uint64_t positionAfterModbusReadInputRegistersPolicy;
  if (hasBytes0)
  {
    positionAfterModbusReadInputRegistersPolicy = StartPosition + 2ULL;
  }
  else
  {
    positionAfterModbusReadInputRegistersPolicy =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        StartPosition);
  }
  uint64_t res0;
  if (EverParseIsSuccess(positionAfterModbusReadInputRegistersPolicy))
  {
    res0 = positionAfterModbusReadInputRegistersPolicy;
  }
  else
  {
    ErrorHandlerFn("_MODBUS_READ_INPUT_REGISTERS_POLICY",
      "TransactionId",
      EverParseErrorReasonOfResult(positionAfterModbusReadInputRegistersPolicy),
      EverParseGetValidatorErrorKind(positionAfterModbusReadInputRegistersPolicy),
      Ctxt,
      Input,
      StartPosition);
    res0 = positionAfterModbusReadInputRegistersPolicy;
  }
  uint64_t positionAfterTransactionId = res0;
  if (EverParseIsError(positionAfterTransactionId))
  {
    return positionAfterTransactionId;
  }
  /* Checking that we have enough space for a UINT16BE, i.e., 2 bytes */
  BOOLEAN hasBytes1 = 2ULL <= (InputLength0 - positionAfterTransactionId);
  uint64_t positionAfterProtocolId;
  if (hasBytes1)
  {
    positionAfterProtocolId = positionAfterTransactionId + 2ULL;
  }
  else
  {
    positionAfterProtocolId =
      EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
        positionAfterTransactionId);
  }
  uint64_t positionAfterModbusReadInputRegistersPolicy0;
  if (EverParseIsError(positionAfterProtocolId))
  {
    positionAfterModbusReadInputRegistersPolicy0 = positionAfterProtocolId;
  }
  else
  {
    uint16_t protocolId = Load16Be(Input + (uint32_t)positionAfterTransactionId);
    BOOLEAN
    protocolIdConstraintIsOk =
      protocolId == (uint16_t)MODBUSTCP_V4_POLICYENFORCED____MODBUS_PROTOCOL_ID;
    uint64_t
    positionAfterProtocolId1 =
      EverParseCheckConstraintOk(protocolIdConstraintIsOk,
        positionAfterProtocolId);
    if (EverParseIsError(positionAfterProtocolId1))
    {
      positionAfterModbusReadInputRegistersPolicy0 = positionAfterProtocolId1;
    }
    else
    {
      /* Checking that we have enough space for a UINT16BE, i.e., 2 bytes */
      BOOLEAN hasBytes2 = 2ULL <= (InputLength0 - positionAfterProtocolId1);
      uint64_t positionAfterLength;
      if (hasBytes2)
      {
        positionAfterLength = positionAfterProtocolId1 + 2ULL;
      }
      else
      {
        positionAfterLength =
          EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
            positionAfterProtocolId1);
      }
      uint64_t positionAfterModbusReadInputRegistersPolicy1;
      if (EverParseIsError(positionAfterLength))
      {
        positionAfterModbusReadInputRegistersPolicy1 = positionAfterLength;
      }
      else
      {
        uint16_t length = Load16Be(Input + (uint32_t)positionAfterProtocolId1);
        BOOLEAN
        lengthConstraintIsOk =
          length == (uint16_t)6U &&
            InputLength ==
              (uint32_t)((uint32_t)length +
                (uint32_t)(uint16_t)MODBUSTCP_V4_POLICYENFORCED____MBAP_HEADER_PREFIX_SIZE);
        uint64_t
        positionAfterLength1 = EverParseCheckConstraintOk(lengthConstraintIsOk, positionAfterLength);
        if (EverParseIsError(positionAfterLength1))
        {
          positionAfterModbusReadInputRegistersPolicy1 = positionAfterLength1;
        }
        else
        {
          /* Validating field UnitId */
          /* Checking that we have enough space for a UINT8, i.e., 1 byte */
          BOOLEAN hasBytes3 = 1ULL <= (InputLength0 - positionAfterLength1);
          uint64_t positionAfterModbusReadInputRegistersPolicy2;
          if (hasBytes3)
          {
            positionAfterModbusReadInputRegistersPolicy2 = positionAfterLength1 + 1ULL;
          }
          else
          {
            positionAfterModbusReadInputRegistersPolicy2 =
              EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
                positionAfterLength1);
          }
          uint64_t res;
          if (EverParseIsSuccess(positionAfterModbusReadInputRegistersPolicy2))
          {
            res = positionAfterModbusReadInputRegistersPolicy2;
          }
          else
          {
            ErrorHandlerFn("_MODBUS_READ_INPUT_REGISTERS_POLICY",
              "UnitId",
              EverParseErrorReasonOfResult(positionAfterModbusReadInputRegistersPolicy2),
              EverParseGetValidatorErrorKind(positionAfterModbusReadInputRegistersPolicy2),
              Ctxt,
              Input,
              positionAfterLength1);
            res = positionAfterModbusReadInputRegistersPolicy2;
          }
          uint64_t positionAfterUnitId = res;
          if (EverParseIsError(positionAfterUnitId))
          {
            positionAfterModbusReadInputRegistersPolicy1 = positionAfterUnitId;
          }
          else
          {
            /* Checking that we have enough space for a UINT8, i.e., 1 byte */
            BOOLEAN hasBytes4 = 1ULL <= (InputLength0 - positionAfterUnitId);
            uint64_t positionAfterFunctionCode;
            if (hasBytes4)
            {
              positionAfterFunctionCode = positionAfterUnitId + 1ULL;
            }
            else
            {
              positionAfterFunctionCode =
                EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
                  positionAfterUnitId);
            }
            uint64_t positionAfterModbusReadInputRegistersPolicy3;
            if (EverParseIsError(positionAfterFunctionCode))
            {
              positionAfterModbusReadInputRegistersPolicy3 = positionAfterFunctionCode;
            }
            else
            {
              uint8_t functionCode = Input[(uint32_t)positionAfterUnitId];
              BOOLEAN
              functionCodeConstraintIsOk =
                functionCode == MODBUSTCP_V4_POLICYENFORCED____FC_READ_INPUT_REGISTERS;
              uint64_t
              positionAfterFunctionCode1 =
                EverParseCheckConstraintOk(functionCodeConstraintIsOk,
                  positionAfterFunctionCode);
              if (EverParseIsError(positionAfterFunctionCode1))
              {
                positionAfterModbusReadInputRegistersPolicy3 = positionAfterFunctionCode1;
              }
              else
              {
                /* Checking that we have enough space for a UINT16BE, i.e., 2 bytes */
                BOOLEAN hasBytes5 = 2ULL <= (InputLength0 - positionAfterFunctionCode1);
                uint64_t positionAfterStartAddress;
                if (hasBytes5)
                {
                  positionAfterStartAddress = positionAfterFunctionCode1 + 2ULL;
                }
                else
                {
                  positionAfterStartAddress =
                    EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
                      positionAfterFunctionCode1);
                }
                uint64_t positionAfterModbusReadInputRegistersPolicy4;
                if (EverParseIsError(positionAfterStartAddress))
                {
                  positionAfterModbusReadInputRegistersPolicy4 = positionAfterStartAddress;
                }
                else
                {
                  uint16_t startAddress = Load16Be(Input + (uint32_t)positionAfterFunctionCode1);
                  BOOLEAN
                  startAddressConstraintIsOk =
                    startAddress >= AllowedStart && startAddress <= AllowedEnd;
                  uint64_t
                  positionAfterStartAddress1 =
                    EverParseCheckConstraintOk(startAddressConstraintIsOk,
                      positionAfterStartAddress);
                  if (EverParseIsError(positionAfterStartAddress1))
                  {
                    positionAfterModbusReadInputRegistersPolicy4 = positionAfterStartAddress1;
                  }
                  else
                  {
                    /* Validating field Quantity */
                    /* Checking that we have enough space for a UINT16BE, i.e., 2 bytes */
                    BOOLEAN hasBytes = 2ULL <= (InputLength0 - positionAfterStartAddress1);
                    uint64_t positionAfterQuantity_refinement;
                    if (hasBytes)
                    {
                      positionAfterQuantity_refinement = positionAfterStartAddress1 + 2ULL;
                    }
                    else
                    {
                      positionAfterQuantity_refinement =
                        EverParseSetValidatorErrorPos(EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA,
                          positionAfterStartAddress1);
                    }
                    uint64_t positionAfterModbusReadInputRegistersPolicy5;
                    if (EverParseIsError(positionAfterQuantity_refinement))
                    {
                      positionAfterModbusReadInputRegistersPolicy5 =
                        positionAfterQuantity_refinement;
                    }
                    else
                    {
                      /* reading field_value */
                      uint16_t
                      quantity_refinement = Load16Be(Input + (uint32_t)positionAfterStartAddress1);
                      /* start: checking constraint */
                      BOOLEAN
                      quantity_refinementConstraintIsOk =
                        quantity_refinement >= (uint16_t)1U &&
                          quantity_refinement <=
                            (uint16_t)MODBUSTCP_V4_POLICYENFORCED____MAX_READ_REGISTERS
                        &&
                          ((uint32_t)quantity_refinement - (uint32_t)(uint16_t)1U) <=
                            ((uint32_t)AllowedEnd - (uint32_t)startAddress);
                      /* end: checking constraint */
                      positionAfterModbusReadInputRegistersPolicy5 =
                        EverParseCheckConstraintOk(quantity_refinementConstraintIsOk,
                          positionAfterQuantity_refinement);
                    }
                    if (EverParseIsSuccess(positionAfterModbusReadInputRegistersPolicy5))
                    {
                      positionAfterModbusReadInputRegistersPolicy4 =
                        positionAfterModbusReadInputRegistersPolicy5;
                    }
                    else
                    {
                      ErrorHandlerFn("_MODBUS_READ_INPUT_REGISTERS_POLICY",
                        "Quantity.refinement",
                        EverParseErrorReasonOfResult(positionAfterModbusReadInputRegistersPolicy5),
                        EverParseGetValidatorErrorKind(positionAfterModbusReadInputRegistersPolicy5),
                        Ctxt,
                        Input,
                        positionAfterStartAddress1);
                      positionAfterModbusReadInputRegistersPolicy4 =
                        positionAfterModbusReadInputRegistersPolicy5;
                    }
                  }
                }
                if (EverParseIsSuccess(positionAfterModbusReadInputRegistersPolicy4))
                {
                  positionAfterModbusReadInputRegistersPolicy3 =
                    positionAfterModbusReadInputRegistersPolicy4;
                }
                else
                {
                  ErrorHandlerFn("_MODBUS_READ_INPUT_REGISTERS_POLICY",
                    "StartAddress",
                    EverParseErrorReasonOfResult(positionAfterModbusReadInputRegistersPolicy4),
                    EverParseGetValidatorErrorKind(positionAfterModbusReadInputRegistersPolicy4),
                    Ctxt,
                    Input,
                    positionAfterFunctionCode1);
                  positionAfterModbusReadInputRegistersPolicy3 =
                    positionAfterModbusReadInputRegistersPolicy4;
                }
              }
            }
            if (EverParseIsSuccess(positionAfterModbusReadInputRegistersPolicy3))
            {
              positionAfterModbusReadInputRegistersPolicy1 =
                positionAfterModbusReadInputRegistersPolicy3;
            }
            else
            {
              ErrorHandlerFn("_MODBUS_READ_INPUT_REGISTERS_POLICY",
                "FunctionCode",
                EverParseErrorReasonOfResult(positionAfterModbusReadInputRegistersPolicy3),
                EverParseGetValidatorErrorKind(positionAfterModbusReadInputRegistersPolicy3),
                Ctxt,
                Input,
                positionAfterUnitId);
              positionAfterModbusReadInputRegistersPolicy1 =
                positionAfterModbusReadInputRegistersPolicy3;
            }
          }
        }
      }
      if (EverParseIsSuccess(positionAfterModbusReadInputRegistersPolicy1))
      {
        positionAfterModbusReadInputRegistersPolicy0 = positionAfterModbusReadInputRegistersPolicy1;
      }
      else
      {
        ErrorHandlerFn("_MODBUS_READ_INPUT_REGISTERS_POLICY",
          "Length",
          EverParseErrorReasonOfResult(positionAfterModbusReadInputRegistersPolicy1),
          EverParseGetValidatorErrorKind(positionAfterModbusReadInputRegistersPolicy1),
          Ctxt,
          Input,
          positionAfterProtocolId1);
        positionAfterModbusReadInputRegistersPolicy0 = positionAfterModbusReadInputRegistersPolicy1;
      }
    }
  }
  if (EverParseIsSuccess(positionAfterModbusReadInputRegistersPolicy0))
  {
    return positionAfterModbusReadInputRegistersPolicy0;
  }
  ErrorHandlerFn("_MODBUS_READ_INPUT_REGISTERS_POLICY",
    "ProtocolId",
    EverParseErrorReasonOfResult(positionAfterModbusReadInputRegistersPolicy0),
    EverParseGetValidatorErrorKind(positionAfterModbusReadInputRegistersPolicy0),
    Ctxt,
    Input,
    positionAfterTransactionId);
  return positionAfterModbusReadInputRegistersPolicy0;
}

