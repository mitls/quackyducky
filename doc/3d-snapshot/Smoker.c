

#include "Smoker.h"

static inline uint64_t
ValidateSmokerCigarettesConsumed(
  uint8_t *Ctxt,
  void
  (*Err)(
    EverParseString x0,
    EverParseString x1,
    EverParseString x2,
    uint8_t *x3,
    uint32_t x4,
    uint8_t *x5,
    uint64_t x6,
    uint64_t x7
  ),
  uint32_t Uu,
  uint8_t *Input,
  uint64_t StartPosition
)
/*++
    Internal helper function:
        Validator for field _smoker_cigarettesConsumed
        of type Smoker._smoker
--*/
{
  /* Validating field cigarettesConsumed */
  /* Checking that we have enough space for a UINT8, i.e., 1 byte */
  uint64_t positionAfterSmoker;
  if (((uint64_t)Uu - StartPosition) < (uint64_t)1U)
  {
    positionAfterSmoker = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  else
  {
    positionAfterSmoker = StartPosition + (uint64_t)1U;
  }
  if (EverParseIsSuccess(positionAfterSmoker))
  {
    return positionAfterSmoker;
  }
  Err("_smoker",
    "_smoker_cigarettesConsumed",
    EverParseErrorReasonOfResult(positionAfterSmoker),
    Ctxt,
    Uu,
    Input,
    StartPosition,
    positionAfterSmoker);
  return positionAfterSmoker;
}

uint64_t
SmokerValidateSmoker(
  uint8_t *Ctxt,
  void
  (*Err)(
    EverParseString x0,
    EverParseString x1,
    EverParseString x2,
    uint8_t *x3,
    uint32_t x4,
    uint8_t *x5,
    uint64_t x6,
    uint64_t x7
  ),
  uint32_t Uu,
  uint8_t *Input,
  uint64_t StartPosition
)
{
  /* Validating field age */
  /* Checking that we have enough space for a ULONG, i.e., 4 bytes */
  uint64_t positionAfterSmoker;
  if (((uint64_t)Uu - StartPosition) < (uint64_t)4U)
  {
    positionAfterSmoker = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  else
  {
    positionAfterSmoker = StartPosition + (uint64_t)4U;
  }
  uint64_t positionAfterage;
  if (EverParseIsSuccess(positionAfterSmoker))
  {
    positionAfterage = positionAfterSmoker;
  }
  else
  {
    Err("_smoker",
      "age",
      EverParseErrorReasonOfResult(positionAfterSmoker),
      Ctxt,
      Uu,
      Input,
      StartPosition,
      positionAfterSmoker);
    positionAfterage = positionAfterSmoker;
  }
  if (EverParseIsError(positionAfterage))
  {
    return positionAfterage;
  }
  uint8_t *base = Input;
  uint32_t age = Load32Le(base + (uint32_t)StartPosition);
  BOOLEAN ageConstraintIsOk = age >= (uint32_t)(uint8_t)21U;
  uint64_t
  positionOrErrorAfterage =
    EverParseCheckConstraintOkWithFieldId(ageConstraintIsOk,
      StartPosition,
      positionAfterage,
      (uint64_t)1U);
  if (EverParseIsError(positionOrErrorAfterage))
  {
    return positionOrErrorAfterage;
  }
  /* Field _smoker_cigarettesConsumed */
  uint64_t
  positionAfterSmoker0 =
    ValidateSmokerCigarettesConsumed(Ctxt,
      Err,
      Uu,
      Input,
      positionOrErrorAfterage);
  if (EverParseIsSuccess(positionAfterSmoker0))
  {
    return positionAfterSmoker0;
  }
  Err("_smoker",
    "cigarettesConsumed",
    EverParseErrorReasonOfResult(positionAfterSmoker0),
    Ctxt,
    Uu,
    Input,
    positionOrErrorAfterage,
    positionAfterSmoker0);
  return positionAfterSmoker0;
}

