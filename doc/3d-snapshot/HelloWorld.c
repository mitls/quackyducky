

#include "HelloWorld.h"

static inline uint64_t
ValidatePointX(
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
        Validator for field _point_x
        of type HelloWorld._point
--*/
{
  /* Validating field x */
  /* Checking that we have enough space for a UINT16, i.e., 2 bytes */
  uint64_t positionAfterPoint;
  if (((uint64_t)Uu - StartPosition) < (uint64_t)2U)
  {
    positionAfterPoint = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  else
  {
    positionAfterPoint = StartPosition + (uint64_t)2U;
  }
  if (EverParseIsSuccess(positionAfterPoint))
  {
    return positionAfterPoint;
  }
  Err("_point",
    "_point_x",
    EverParseErrorReasonOfResult(positionAfterPoint),
    Ctxt,
    Uu,
    Input,
    StartPosition,
    positionAfterPoint);
  return positionAfterPoint;
}

static inline uint64_t
ValidatePointY(
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
        Validator for field _point_y
        of type HelloWorld._point
--*/
{
  /* Validating field y */
  /* Checking that we have enough space for a UINT16, i.e., 2 bytes */
  uint64_t positionAfterPoint;
  if (((uint64_t)Uu - StartPosition) < (uint64_t)2U)
  {
    positionAfterPoint = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  else
  {
    positionAfterPoint = StartPosition + (uint64_t)2U;
  }
  if (EverParseIsSuccess(positionAfterPoint))
  {
    return positionAfterPoint;
  }
  Err("_point",
    "_point_y",
    EverParseErrorReasonOfResult(positionAfterPoint),
    Ctxt,
    Uu,
    Input,
    StartPosition,
    positionAfterPoint);
  return positionAfterPoint;
}

uint64_t
HelloWorldValidatePoint(
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
  /* Field _point_x */
  uint64_t positionAfterPoint = ValidatePointX(Ctxt, Err, Uu, Input, StartPosition);
  uint64_t positionAfterx;
  if (EverParseIsSuccess(positionAfterPoint))
  {
    positionAfterx = positionAfterPoint;
  }
  else
  {
    Err("_point",
      "x",
      EverParseErrorReasonOfResult(positionAfterPoint),
      Ctxt,
      Uu,
      Input,
      StartPosition,
      positionAfterPoint);
    positionAfterx = positionAfterPoint;
  }
  if (EverParseIsError(positionAfterx))
  {
    return positionAfterx;
  }
  /* Field _point_y */
  uint64_t positionAfterPoint0 = ValidatePointY(Ctxt, Err, Uu, Input, positionAfterx);
  if (EverParseIsSuccess(positionAfterPoint0))
  {
    return positionAfterPoint0;
  }
  Err("_point",
    "y",
    EverParseErrorReasonOfResult(positionAfterPoint0),
    Ctxt,
    Uu,
    Input,
    positionAfterx,
    positionAfterPoint0);
  return positionAfterPoint0;
}

