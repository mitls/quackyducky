

#include "EnumConstraint.h"

/*
Enum constant
*/
#define RED ((uint32_t)1U)

/*
Enum constant
*/
#define GREEN ((uint32_t)2U)

/*
Enum constant
*/
#define BLUE ((uint32_t)42U)

static inline uint64_t
ValidateEnumConstraintX(
  uint32_t Col,
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
        Validator for field _enum_constraint_x
        of type EnumConstraint._enum_constraint
--*/
{
  /* Validating field x */
  /* Checking that we have enough space for a ULONG, i.e., 4 bytes */
  uint64_t positionAfterEnumConstraint;
  if (((uint64_t)Uu - StartPosition) < (uint64_t)4U)
  {
    positionAfterEnumConstraint = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  else
  {
    positionAfterEnumConstraint = StartPosition + (uint64_t)4U;
  }
  uint64_t positionAfterEnumConstraint0;
  if (EverParseIsSuccess(positionAfterEnumConstraint))
  {
    positionAfterEnumConstraint0 = positionAfterEnumConstraint;
  }
  else
  {
    Err("_enum_constraint",
      "_enum_constraint_x",
      EverParseErrorReasonOfResult(positionAfterEnumConstraint),
      Ctxt,
      Uu,
      Input,
      StartPosition,
      positionAfterEnumConstraint);
    positionAfterEnumConstraint0 = positionAfterEnumConstraint;
  }
  uint64_t positionAfterEnumConstraint1;
  if (EverParseIsError(positionAfterEnumConstraint0))
  {
    positionAfterEnumConstraint1 = positionAfterEnumConstraint0;
  }
  else
  {
    /* reading field value */
    uint8_t *base = Input;
    uint32_t enumConstraint1 = Load32Le(base + (uint32_t)StartPosition);
    /* start: checking constraint */
    BOOLEAN
    enumConstraintConstraintIsOk = enumConstraint1 == (uint32_t)(uint8_t)0U || Col == GREEN;
    /* end: checking constraint */
    positionAfterEnumConstraint1 =
      EverParseCheckConstraintOk(enumConstraintConstraintIsOk,
        positionAfterEnumConstraint0);
  }
  if (EverParseIsSuccess(positionAfterEnumConstraint1))
  {
    return positionAfterEnumConstraint1;
  }
  Err("_enum_constraint",
    "_enum_constraint_x.refinement",
    EverParseErrorReasonOfResult(positionAfterEnumConstraint1),
    Ctxt,
    Uu,
    Input,
    StartPosition,
    positionAfterEnumConstraint1);
  return positionAfterEnumConstraint1;
}

uint64_t
EnumConstraintValidateEnumConstraint(
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
  /* Validating field col */
  /* Checking that we have enough space for a ULONG, i.e., 4 bytes */
  uint64_t positionAfterEnumConstraint;
  if (((uint64_t)Uu - StartPosition) < (uint64_t)4U)
  {
    positionAfterEnumConstraint = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  else
  {
    positionAfterEnumConstraint = StartPosition + (uint64_t)4U;
  }
  uint64_t positionAftercol;
  if (EverParseIsSuccess(positionAfterEnumConstraint))
  {
    positionAftercol = positionAfterEnumConstraint;
  }
  else
  {
    Err("_enum_constraint",
      "col",
      EverParseErrorReasonOfResult(positionAfterEnumConstraint),
      Ctxt,
      Uu,
      Input,
      StartPosition,
      positionAfterEnumConstraint);
    positionAftercol = positionAfterEnumConstraint;
  }
  if (EverParseIsError(positionAftercol))
  {
    return positionAftercol;
  }
  uint8_t *base = Input;
  uint32_t col = Load32Le(base + (uint32_t)StartPosition);
  BOOLEAN colConstraintIsOk = col == RED || col == GREEN || col == BLUE;
  uint64_t
  positionOrErrorAftercol =
    EverParseCheckConstraintOkWithFieldId(colConstraintIsOk,
      StartPosition,
      positionAftercol,
      (uint64_t)1U);
  if (EverParseIsError(positionOrErrorAftercol))
  {
    return positionOrErrorAftercol;
  }
  /* Field _enum_constraint_x */
  uint64_t
  positionAfterEnumConstraint0 =
    ValidateEnumConstraintX(col,
      Ctxt,
      Err,
      Uu,
      Input,
      positionOrErrorAftercol);
  if (EverParseIsSuccess(positionAfterEnumConstraint0))
  {
    return positionAfterEnumConstraint0;
  }
  Err("_enum_constraint",
    "x",
    EverParseErrorReasonOfResult(positionAfterEnumConstraint0),
    Ctxt,
    Uu,
    Input,
    positionOrErrorAftercol,
    positionAfterEnumConstraint0);
  return positionAfterEnumConstraint0;
}

