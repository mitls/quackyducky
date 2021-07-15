

#include "BoundedSumConst.h"

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
        of type BoundedSumConst._boundedSum
--*/
{
  /* SNIPPET_START: boundedSumCorrect */
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
        of type BoundedSumConst._boundedSum
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
    BOOLEAN
    boundedSumConstraintIsOk =
      Left
      <= (uint32_t)(uint8_t)42U
      && boundedSum1 <= ((uint32_t)(uint8_t)42U - Left);
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
BoundedSumConstValidateBoundedSum(
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
 The following will fail because of integer overflow
// SNIPPET_START: boundedSumNaive
entrypoint typedef struct _boundedSum {
  UINT32 left;
  UINT32 right { left + right <= 42 };
} boundedSum;
// SNIPPET_END: boundedSumNaive

--*/
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
    ValidateBoundedSumRight(left,
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

