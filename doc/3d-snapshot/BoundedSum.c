

#include "BoundedSum.h"

static inline uint64_t
ValidateBoundedSumLeft(
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
        Validator for field _boundedSum_left
        of type BoundedSum._boundedSum
--*/
{
  /* SNIPPET_START: boundedSum */
  /* Checking that we have enough space for a ULONG, i.e., 4 bytes */
  uint64_t positionAfterBoundedSum;
  if (((uint64_t)Uu - StartPosition) < (uint64_t)4U)
  {
    positionAfterBoundedSum = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  else
  {
    positionAfterBoundedSum = StartPosition + (uint64_t)4U;
  }
  if (EverParseIsSuccess(positionAfterBoundedSum))
  {
    return positionAfterBoundedSum;
  }
  Err("_boundedSum",
    "_boundedSum_left",
    EverParseErrorReasonOfResult(positionAfterBoundedSum),
    Ctxt,
    Uu,
    Input,
    StartPosition,
    positionAfterBoundedSum);
  return positionAfterBoundedSum;
}

static inline uint64_t
ValidateBoundedSumRight(
  uint32_t Bound,
  uint32_t Left,
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
        Validator for field _boundedSum_right
        of type BoundedSum._boundedSum
--*/
{
  /* Validating field right */
  /* Checking that we have enough space for a ULONG, i.e., 4 bytes */
  uint64_t positionAfterBoundedSum;
  if (((uint64_t)Uu - StartPosition) < (uint64_t)4U)
  {
    positionAfterBoundedSum = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  else
  {
    positionAfterBoundedSum = StartPosition + (uint64_t)4U;
  }
  uint64_t positionAfterBoundedSum0;
  if (EverParseIsSuccess(positionAfterBoundedSum))
  {
    positionAfterBoundedSum0 = positionAfterBoundedSum;
  }
  else
  {
    Err("_boundedSum",
      "_boundedSum_right",
      EverParseErrorReasonOfResult(positionAfterBoundedSum),
      Ctxt,
      Uu,
      Input,
      StartPosition,
      positionAfterBoundedSum);
    positionAfterBoundedSum0 = positionAfterBoundedSum;
  }
  uint64_t positionAfterBoundedSum1;
  if (EverParseIsError(positionAfterBoundedSum0))
  {
    positionAfterBoundedSum1 = positionAfterBoundedSum0;
  }
  else
  {
    /* reading field value */
    uint8_t *base = Input;
    uint32_t boundedSum1 = Load32Le(base + (uint32_t)StartPosition);
    /* start: checking constraint */
    BOOLEAN boundedSumConstraintIsOk = Left <= Bound && boundedSum1 <= (Bound - Left);
    /* end: checking constraint */
    positionAfterBoundedSum1 =
      EverParseCheckConstraintOk(boundedSumConstraintIsOk,
        positionAfterBoundedSum0);
  }
  if (EverParseIsSuccess(positionAfterBoundedSum1))
  {
    return positionAfterBoundedSum1;
  }
  Err("_boundedSum",
    "_boundedSum_right.refinement",
    EverParseErrorReasonOfResult(positionAfterBoundedSum1),
    Ctxt,
    Uu,
    Input,
    StartPosition,
    positionAfterBoundedSum1);
  return positionAfterBoundedSum1;
}

uint64_t
BoundedSumValidateBoundedSum(
  uint32_t Bound,
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
  /* Field _boundedSum_left */
  uint64_t positionAfterBoundedSum = ValidateBoundedSumLeft(Ctxt, Err, Uu, Input, StartPosition);
  uint64_t positionAfterleft;
  if (EverParseIsSuccess(positionAfterBoundedSum))
  {
    positionAfterleft = positionAfterBoundedSum;
  }
  else
  {
    Err("_boundedSum",
      "left",
      EverParseErrorReasonOfResult(positionAfterBoundedSum),
      Ctxt,
      Uu,
      Input,
      StartPosition,
      positionAfterBoundedSum);
    positionAfterleft = positionAfterBoundedSum;
  }
  if (EverParseIsError(positionAfterleft))
  {
    return positionAfterleft;
  }
  uint8_t *base = Input;
  uint32_t left = Load32Le(base + (uint32_t)StartPosition);
  /* Field _boundedSum_right */
  uint64_t
  positionAfterBoundedSum0 =
    ValidateBoundedSumRight(Bound,
      left,
      Ctxt,
      Err,
      Uu,
      Input,
      positionAfterleft);
  if (EverParseIsSuccess(positionAfterBoundedSum0))
  {
    return positionAfterBoundedSum0;
  }
  Err("_boundedSum",
    "right",
    EverParseErrorReasonOfResult(positionAfterBoundedSum0),
    Ctxt,
    Uu,
    Input,
    positionAfterleft,
    positionAfterBoundedSum0);
  return positionAfterBoundedSum0;
}

static inline uint64_t
ValidateMySumBound(
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
        Validator for field mySum_bound
        of type BoundedSum.mySum
--*/
{
  /* Validating field bound */
  /* Checking that we have enough space for a ULONG, i.e., 4 bytes */
  uint64_t positionAftermySum;
  if (((uint64_t)Uu - StartPosition) < (uint64_t)4U)
  {
    positionAftermySum = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  else
  {
    positionAftermySum = StartPosition + (uint64_t)4U;
  }
  if (EverParseIsSuccess(positionAftermySum))
  {
    return positionAftermySum;
  }
  Err("mySum",
    "mySum_bound",
    EverParseErrorReasonOfResult(positionAftermySum),
    Ctxt,
    Uu,
    Input,
    StartPosition,
    positionAftermySum);
  return positionAftermySum;
}

static inline uint64_t
ValidateMySumSum(
  uint32_t Bound,
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
        Validator for field mySum_sum
        of type BoundedSum.mySum
--*/
{
  /* Validating field sum */
  uint64_t
  positionAftermySum = BoundedSumValidateBoundedSum(Bound, Ctxt, Err, Uu, Input, StartPosition);
  if (EverParseIsSuccess(positionAftermySum))
  {
    return positionAftermySum;
  }
  Err("mySum",
    "mySum_sum",
    EverParseErrorReasonOfResult(positionAftermySum),
    Ctxt,
    Uu,
    Input,
    StartPosition,
    positionAftermySum);
  return positionAftermySum;
}

uint64_t
BoundedSumValidateMySum(
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
  /* Field mySum_bound */
  uint64_t positionAftermySum = ValidateMySumBound(Ctxt, Err, Uu, Input, StartPosition);
  uint64_t positionAfterbound;
  if (EverParseIsSuccess(positionAftermySum))
  {
    positionAfterbound = positionAftermySum;
  }
  else
  {
    Err("mySum",
      "bound",
      EverParseErrorReasonOfResult(positionAftermySum),
      Ctxt,
      Uu,
      Input,
      StartPosition,
      positionAftermySum);
    positionAfterbound = positionAftermySum;
  }
  if (EverParseIsError(positionAfterbound))
  {
    return positionAfterbound;
  }
  uint8_t *base = Input;
  uint32_t bound = Load32Le(base + (uint32_t)StartPosition);
  /* Field mySum_sum */
  uint64_t
  positionAftermySum0 = ValidateMySumSum(bound, Ctxt, Err, Uu, Input, positionAfterbound);
  if (EverParseIsSuccess(positionAftermySum0))
  {
    return positionAftermySum0;
  }
  Err("mySum",
    "sum",
    EverParseErrorReasonOfResult(positionAftermySum0),
    Ctxt,
    Uu,
    Input,
    positionAfterbound,
    positionAftermySum0);
  return positionAftermySum0;
}

