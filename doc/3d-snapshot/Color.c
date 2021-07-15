

#include "Color.h"

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
ValidateColor(
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
  uint64_t positionAftercolor0;
  if (((uint64_t)Uu - StartPosition) < (uint64_t)4U)
  {
    positionAftercolor0 = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  else
  {
    positionAftercolor0 = StartPosition + (uint64_t)4U;
  }
  uint64_t positionAftercolor1;
  if (EverParseIsSuccess(positionAftercolor0))
  {
    positionAftercolor1 = positionAftercolor0;
  }
  else
  {
    Err("color",
      "",
      EverParseErrorReasonOfResult(positionAftercolor0),
      Ctxt,
      Uu,
      Input,
      StartPosition,
      positionAftercolor0);
    positionAftercolor1 = positionAftercolor0;
  }
  uint64_t positionAftercolor;
  if (EverParseIsError(positionAftercolor1))
  {
    positionAftercolor = positionAftercolor1;
  }
  else
  {
    /* reading field value */
    uint8_t *base = Input;
    uint32_t color = Load32Le(base + (uint32_t)StartPosition);
    /* start: checking constraint */
    BOOLEAN colorConstraintIsOk = color == RED || color == GREEN || color == BLUE || FALSE;
    /* end: checking constraint */
    positionAftercolor = EverParseCheckConstraintOk(colorConstraintIsOk, positionAftercolor1);
  }
  if (EverParseIsSuccess(positionAftercolor))
  {
    return positionAftercolor;
  }
  Err("color",
    ".refinement",
    EverParseErrorReasonOfResult(positionAftercolor),
    Ctxt,
    Uu,
    Input,
    StartPosition,
    positionAftercolor);
  return positionAftercolor;
}

static inline uint64_t
ValidateColoredPointCol(
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
        Validator for field _coloredPoint_col
        of type Color._coloredPoint
--*/
{
  /* Validating field col */
  uint64_t positionAfterColoredPoint = ValidateColor(Ctxt, Err, Uu, Input, StartPosition);
  if (EverParseIsSuccess(positionAfterColoredPoint))
  {
    return positionAfterColoredPoint;
  }
  Err("_coloredPoint",
    "_coloredPoint_col",
    EverParseErrorReasonOfResult(positionAfterColoredPoint),
    Ctxt,
    Uu,
    Input,
    StartPosition,
    positionAfterColoredPoint);
  return positionAfterColoredPoint;
}

static inline uint64_t
ValidateColoredPointX(
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
        Validator for field _coloredPoint_x
        of type Color._coloredPoint
--*/
{
  /* Validating field x */
  /* Checking that we have enough space for a ULONG, i.e., 4 bytes */
  uint64_t positionAfterColoredPoint;
  if (((uint64_t)Uu - StartPosition) < (uint64_t)4U)
  {
    positionAfterColoredPoint = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  else
  {
    positionAfterColoredPoint = StartPosition + (uint64_t)4U;
  }
  if (EverParseIsSuccess(positionAfterColoredPoint))
  {
    return positionAfterColoredPoint;
  }
  Err("_coloredPoint",
    "_coloredPoint_x",
    EverParseErrorReasonOfResult(positionAfterColoredPoint),
    Ctxt,
    Uu,
    Input,
    StartPosition,
    positionAfterColoredPoint);
  return positionAfterColoredPoint;
}

static inline uint64_t
ValidateColoredPointY(
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
        Validator for field _coloredPoint_y
        of type Color._coloredPoint
--*/
{
  /* Validating field y */
  /* Checking that we have enough space for a ULONG, i.e., 4 bytes */
  uint64_t positionAfterColoredPoint;
  if (((uint64_t)Uu - StartPosition) < (uint64_t)4U)
  {
    positionAfterColoredPoint = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  else
  {
    positionAfterColoredPoint = StartPosition + (uint64_t)4U;
  }
  if (EverParseIsSuccess(positionAfterColoredPoint))
  {
    return positionAfterColoredPoint;
  }
  Err("_coloredPoint",
    "_coloredPoint_y",
    EverParseErrorReasonOfResult(positionAfterColoredPoint),
    Ctxt,
    Uu,
    Input,
    StartPosition,
    positionAfterColoredPoint);
  return positionAfterColoredPoint;
}

uint64_t
ColorValidateColoredPoint(
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
  /* Field _coloredPoint_col */
  uint64_t
  positionAfterColoredPoint = ValidateColoredPointCol(Ctxt, Err, Uu, Input, StartPosition);
  uint64_t positionAftercol;
  if (EverParseIsSuccess(positionAfterColoredPoint))
  {
    positionAftercol = positionAfterColoredPoint;
  }
  else
  {
    Err("_coloredPoint",
      "col",
      EverParseErrorReasonOfResult(positionAfterColoredPoint),
      Ctxt,
      Uu,
      Input,
      StartPosition,
      positionAfterColoredPoint);
    positionAftercol = positionAfterColoredPoint;
  }
  if (EverParseIsError(positionAftercol))
  {
    return positionAftercol;
  }
  /* Field _coloredPoint_x */
  uint64_t
  positionAfterColoredPoint0 = ValidateColoredPointX(Ctxt, Err, Uu, Input, positionAftercol);
  uint64_t positionAfterx;
  if (EverParseIsSuccess(positionAfterColoredPoint0))
  {
    positionAfterx = positionAfterColoredPoint0;
  }
  else
  {
    Err("_coloredPoint",
      "x",
      EverParseErrorReasonOfResult(positionAfterColoredPoint0),
      Ctxt,
      Uu,
      Input,
      positionAftercol,
      positionAfterColoredPoint0);
    positionAfterx = positionAfterColoredPoint0;
  }
  if (EverParseIsError(positionAfterx))
  {
    return positionAfterx;
  }
  /* Field _coloredPoint_y */
  uint64_t
  positionAfterColoredPoint1 = ValidateColoredPointY(Ctxt, Err, Uu, Input, positionAfterx);
  if (EverParseIsSuccess(positionAfterColoredPoint1))
  {
    return positionAfterColoredPoint1;
  }
  Err("_coloredPoint",
    "y",
    EverParseErrorReasonOfResult(positionAfterColoredPoint1),
    Ctxt,
    Uu,
    Input,
    positionAfterx,
    positionAfterColoredPoint1);
  return positionAfterColoredPoint1;
}

