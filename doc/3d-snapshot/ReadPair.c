

#include "ReadPair.h"

static inline uint64_t
ValidatePairFirst(
  uint32_t *X,
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
        of type ReadPair._Pair
--*/
{
  /* Validating field first */
  /* Checking that we have enough space for a ULONG, i.e., 4 bytes */
  uint64_t positionAfterPair;
  if (((uint64_t)Uu - StartPosition) < (uint64_t)4U)
  {
    positionAfterPair = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  else
  {
    positionAfterPair = StartPosition + (uint64_t)4U;
  }
  uint64_t positionAfterPair0;
  if (EverParseIsSuccess(positionAfterPair))
  {
    positionAfterPair0 = positionAfterPair;
  }
  else
  {
    Err("_Pair",
      "_Pair_first.base",
      EverParseErrorReasonOfResult(positionAfterPair),
      Ctxt,
      Uu,
      Input,
      StartPosition,
      positionAfterPair);
    positionAfterPair0 = positionAfterPair;
  }
  uint64_t positionAfterPair1;
  if (EverParseIsError(positionAfterPair0))
  {
    positionAfterPair1 = positionAfterPair0;
  }
  else
  {
    uint8_t *base = Input;
    uint32_t pair1 = Load32Le(base + (uint32_t)StartPosition);
    *X = pair1;
    if (TRUE)
    {
      positionAfterPair1 = positionAfterPair0;
    }
    else
    {
      positionAfterPair1 = EVERPARSE_VALIDATOR_ERROR_ACTION_FAILED;
    }
  }
  if (EverParseIsSuccess(positionAfterPair1))
  {
    return positionAfterPair1;
  }
  Err("_Pair",
    "_Pair_first",
    EverParseErrorReasonOfResult(positionAfterPair1),
    Ctxt,
    Uu,
    Input,
    StartPosition,
    positionAfterPair1);
  return positionAfterPair1;
}

static inline uint64_t
ValidatePairSecond(
  uint32_t *Y,
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
        of type ReadPair._Pair
--*/
{
  /* Validating field second */
  /* Checking that we have enough space for a ULONG, i.e., 4 bytes */
  uint64_t positionAfterPair;
  if (((uint64_t)Uu - StartPosition) < (uint64_t)4U)
  {
    positionAfterPair = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  else
  {
    positionAfterPair = StartPosition + (uint64_t)4U;
  }
  uint64_t positionAfterPair0;
  if (EverParseIsSuccess(positionAfterPair))
  {
    positionAfterPair0 = positionAfterPair;
  }
  else
  {
    Err("_Pair",
      "_Pair_second.base",
      EverParseErrorReasonOfResult(positionAfterPair),
      Ctxt,
      Uu,
      Input,
      StartPosition,
      positionAfterPair);
    positionAfterPair0 = positionAfterPair;
  }
  uint64_t positionAfterPair1;
  if (EverParseIsError(positionAfterPair0))
  {
    positionAfterPair1 = positionAfterPair0;
  }
  else
  {
    uint8_t *base = Input;
    uint32_t pair1 = Load32Le(base + (uint32_t)StartPosition);
    *Y = pair1;
    if (TRUE)
    {
      positionAfterPair1 = positionAfterPair0;
    }
    else
    {
      positionAfterPair1 = EVERPARSE_VALIDATOR_ERROR_ACTION_FAILED;
    }
  }
  if (EverParseIsSuccess(positionAfterPair1))
  {
    return positionAfterPair1;
  }
  Err("_Pair",
    "_Pair_second",
    EverParseErrorReasonOfResult(positionAfterPair1),
    Ctxt,
    Uu,
    Input,
    StartPosition,
    positionAfterPair1);
  return positionAfterPair1;
}

uint64_t
ReadPairValidatePair(
  uint32_t *X,
  uint32_t *Y,
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
  uint64_t positionAfterPair = ValidatePairFirst(X, Ctxt, Err, Uu, Input, StartPosition);
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
  uint64_t positionAfterPair0 = ValidatePairSecond(Y, Ctxt, Err, Uu, Input, positionAfterfirst);
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

