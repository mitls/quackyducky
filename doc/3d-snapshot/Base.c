

#include "Base.h"

uint64_t
BaseValidateUlong(
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
  /* Checking that we have enough space for a ULONG, i.e., 4 bytes */
  uint64_t positionAfterUlong;
  if (((uint64_t)Uu - StartPosition) < (uint64_t)4U)
  {
    positionAfterUlong = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  else
  {
    positionAfterUlong = StartPosition + (uint64_t)4U;
  }
  if (EverParseIsSuccess(positionAfterUlong))
  {
    return positionAfterUlong;
  }
  Err("___ULONG",
    "",
    EverParseErrorReasonOfResult(positionAfterUlong),
    Ctxt,
    Uu,
    Input,
    StartPosition,
    positionAfterUlong);
  return positionAfterUlong;
}

static inline uint64_t
ValidatePairFirst(
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
        Validator for field _Pair_first
        of type Base._Pair
--*/
{
  /* Validating field first */
  uint64_t positionAfterPair = BaseValidateUlong(Ctxt, Err, Uu, Input, StartPosition);
  if (EverParseIsSuccess(positionAfterPair))
  {
    return positionAfterPair;
  }
  Err("_Pair",
    "_Pair_first",
    EverParseErrorReasonOfResult(positionAfterPair),
    Ctxt,
    Uu,
    Input,
    StartPosition,
    positionAfterPair);
  return positionAfterPair;
}

static inline uint64_t
ValidatePairSecond(
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
        Validator for field _Pair_second
        of type Base._Pair
--*/
{
  /* Validating field second */
  uint64_t positionAfterPair = BaseValidateUlong(Ctxt, Err, Uu, Input, StartPosition);
  if (EverParseIsSuccess(positionAfterPair))
  {
    return positionAfterPair;
  }
  Err("_Pair",
    "_Pair_second",
    EverParseErrorReasonOfResult(positionAfterPair),
    Ctxt,
    Uu,
    Input,
    StartPosition,
    positionAfterPair);
  return positionAfterPair;
}

uint64_t
BaseValidatePair(
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
  /* Field _Pair_first */
  uint64_t positionAfterPair = ValidatePairFirst(Ctxt, Err, Uu, Input, StartPosition);
  uint64_t positionAfterfirst;
  if (EverParseIsSuccess(positionAfterPair))
  {
    positionAfterfirst = positionAfterPair;
  }
  else
  {
    Err("_Pair",
      "first",
      EverParseErrorReasonOfResult(positionAfterPair),
      Ctxt,
      Uu,
      Input,
      StartPosition,
      positionAfterPair);
    positionAfterfirst = positionAfterPair;
  }
  if (EverParseIsError(positionAfterfirst))
  {
    return positionAfterfirst;
  }
  /* Field _Pair_second */
  uint64_t positionAfterPair0 = ValidatePairSecond(Ctxt, Err, Uu, Input, positionAfterfirst);
  if (EverParseIsSuccess(positionAfterPair0))
  {
    return positionAfterPair0;
  }
  Err("_Pair",
    "second",
    EverParseErrorReasonOfResult(positionAfterPair0),
    Ctxt,
    Uu,
    Input,
    positionAfterfirst,
    positionAfterPair0);
  return positionAfterPair0;
}

