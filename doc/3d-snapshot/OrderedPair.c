

#include "OrderedPair.h"

static inline uint64_t
ValidateOrderedPairLesser(
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
        Validator for field _orderedPair_lesser
        of type OrderedPair._orderedPair
--*/
{
  /* Validating field lesser */
  /* Checking that we have enough space for a ULONG, i.e., 4 bytes */
  uint64_t positionAfterOrderedPair;
  if (((uint64_t)Uu - StartPosition) < (uint64_t)4U)
  {
    positionAfterOrderedPair = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  else
  {
    positionAfterOrderedPair = StartPosition + (uint64_t)4U;
  }
  if (EverParseIsSuccess(positionAfterOrderedPair))
  {
    return positionAfterOrderedPair;
  }
  Err("_orderedPair",
    "_orderedPair_lesser",
    EverParseErrorReasonOfResult(positionAfterOrderedPair),
    Ctxt,
    Uu,
    Input,
    StartPosition,
    positionAfterOrderedPair);
  return positionAfterOrderedPair;
}

static inline uint64_t
ValidateOrderedPairGreater(
  uint32_t Lesser,
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
        Validator for field _orderedPair_greater
        of type OrderedPair._orderedPair
--*/
{
  /* Validating field greater */
  /* Checking that we have enough space for a ULONG, i.e., 4 bytes */
  uint64_t positionAfterOrderedPair;
  if (((uint64_t)Uu - StartPosition) < (uint64_t)4U)
  {
    positionAfterOrderedPair = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  else
  {
    positionAfterOrderedPair = StartPosition + (uint64_t)4U;
  }
  uint64_t positionAfterOrderedPair0;
  if (EverParseIsSuccess(positionAfterOrderedPair))
  {
    positionAfterOrderedPair0 = positionAfterOrderedPair;
  }
  else
  {
    Err("_orderedPair",
      "_orderedPair_greater",
      EverParseErrorReasonOfResult(positionAfterOrderedPair),
      Ctxt,
      Uu,
      Input,
      StartPosition,
      positionAfterOrderedPair);
    positionAfterOrderedPair0 = positionAfterOrderedPair;
  }
  uint64_t positionAfterOrderedPair1;
  if (EverParseIsError(positionAfterOrderedPair0))
  {
    positionAfterOrderedPair1 = positionAfterOrderedPair0;
  }
  else
  {
    /* reading field value */
    uint8_t *base = Input;
    uint32_t orderedPair1 = Load32Le(base + (uint32_t)StartPosition);
    /* start: checking constraint */
    BOOLEAN orderedPairConstraintIsOk = Lesser <= orderedPair1;
    /* end: checking constraint */
    positionAfterOrderedPair1 =
      EverParseCheckConstraintOk(orderedPairConstraintIsOk,
        positionAfterOrderedPair0);
  }
  if (EverParseIsSuccess(positionAfterOrderedPair1))
  {
    return positionAfterOrderedPair1;
  }
  Err("_orderedPair",
    "_orderedPair_greater.refinement",
    EverParseErrorReasonOfResult(positionAfterOrderedPair1),
    Ctxt,
    Uu,
    Input,
    StartPosition,
    positionAfterOrderedPair1);
  return positionAfterOrderedPair1;
}

uint64_t
OrderedPairValidateOrderedPair(
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
  /* Field _orderedPair_lesser */
  uint64_t
  positionAfterOrderedPair = ValidateOrderedPairLesser(Ctxt, Err, Uu, Input, StartPosition);
  uint64_t positionAfterlesser;
  if (EverParseIsSuccess(positionAfterOrderedPair))
  {
    positionAfterlesser = positionAfterOrderedPair;
  }
  else
  {
    Err("_orderedPair",
      "lesser",
      EverParseErrorReasonOfResult(positionAfterOrderedPair),
      Ctxt,
      Uu,
      Input,
      StartPosition,
      positionAfterOrderedPair);
    positionAfterlesser = positionAfterOrderedPair;
  }
  if (EverParseIsError(positionAfterlesser))
  {
    return positionAfterlesser;
  }
  uint8_t *base = Input;
  uint32_t lesser = Load32Le(base + (uint32_t)StartPosition);
  /* Field _orderedPair_greater */
  uint64_t
  positionAfterOrderedPair0 =
    ValidateOrderedPairGreater(lesser,
      Ctxt,
      Err,
      Uu,
      Input,
      positionAfterlesser);
  if (EverParseIsSuccess(positionAfterOrderedPair0))
  {
    return positionAfterOrderedPair0;
  }
  Err("_orderedPair",
    "greater",
    EverParseErrorReasonOfResult(positionAfterOrderedPair0),
    Ctxt,
    Uu,
    Input,
    positionAfterlesser,
    positionAfterOrderedPair0);
  return positionAfterOrderedPair0;
}

