

#include "Triangle.h"

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
        of type Triangle._point
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
        of type Triangle._point
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

static inline uint64_t
ValidatePoint(
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

static inline uint64_t
ValidateTriangleA(
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
        Validator for field _triangle_a
        of type Triangle._triangle
--*/
{
  /* Validating field a */
  uint64_t positionAfterTriangle = ValidatePoint(Ctxt, Err, Uu, Input, StartPosition);
  if (EverParseIsSuccess(positionAfterTriangle))
  {
    return positionAfterTriangle;
  }
  Err("_triangle",
    "_triangle_a",
    EverParseErrorReasonOfResult(positionAfterTriangle),
    Ctxt,
    Uu,
    Input,
    StartPosition,
    positionAfterTriangle);
  return positionAfterTriangle;
}

static inline uint64_t
ValidateTriangleB(
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
        Validator for field _triangle_b
        of type Triangle._triangle
--*/
{
  /* Validating field b */
  uint64_t positionAfterTriangle = ValidatePoint(Ctxt, Err, Uu, Input, StartPosition);
  if (EverParseIsSuccess(positionAfterTriangle))
  {
    return positionAfterTriangle;
  }
  Err("_triangle",
    "_triangle_b",
    EverParseErrorReasonOfResult(positionAfterTriangle),
    Ctxt,
    Uu,
    Input,
    StartPosition,
    positionAfterTriangle);
  return positionAfterTriangle;
}

static inline uint64_t
ValidateTriangleC(
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
        Validator for field _triangle_c
        of type Triangle._triangle
--*/
{
  /* Validating field c */
  uint64_t positionAfterTriangle = ValidatePoint(Ctxt, Err, Uu, Input, StartPosition);
  if (EverParseIsSuccess(positionAfterTriangle))
  {
    return positionAfterTriangle;
  }
  Err("_triangle",
    "_triangle_c",
    EverParseErrorReasonOfResult(positionAfterTriangle),
    Ctxt,
    Uu,
    Input,
    StartPosition,
    positionAfterTriangle);
  return positionAfterTriangle;
}

uint64_t
TriangleValidateTriangle(
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
  /* Field _triangle_a */
  uint64_t positionAfterTriangle = ValidateTriangleA(Ctxt, Err, Uu, Input, StartPosition);
  uint64_t positionAftera;
  if (EverParseIsSuccess(positionAfterTriangle))
  {
    positionAftera = positionAfterTriangle;
  }
  else
  {
    Err("_triangle",
      "a",
      EverParseErrorReasonOfResult(positionAfterTriangle),
      Ctxt,
      Uu,
      Input,
      StartPosition,
      positionAfterTriangle);
    positionAftera = positionAfterTriangle;
  }
  if (EverParseIsError(positionAftera))
  {
    return positionAftera;
  }
  /* Field _triangle_b */
  uint64_t positionAfterTriangle0 = ValidateTriangleB(Ctxt, Err, Uu, Input, positionAftera);
  uint64_t positionAfterb;
  if (EverParseIsSuccess(positionAfterTriangle0))
  {
    positionAfterb = positionAfterTriangle0;
  }
  else
  {
    Err("_triangle",
      "b",
      EverParseErrorReasonOfResult(positionAfterTriangle0),
      Ctxt,
      Uu,
      Input,
      positionAftera,
      positionAfterTriangle0);
    positionAfterb = positionAfterTriangle0;
  }
  if (EverParseIsError(positionAfterb))
  {
    return positionAfterb;
  }
  /* Field _triangle_c */
  uint64_t positionAfterTriangle1 = ValidateTriangleC(Ctxt, Err, Uu, Input, positionAfterb);
  if (EverParseIsSuccess(positionAfterTriangle1))
  {
    return positionAfterTriangle1;
  }
  Err("_triangle",
    "c",
    EverParseErrorReasonOfResult(positionAfterTriangle1),
    Ctxt,
    Uu,
    Input,
    positionAfterb,
    positionAfterTriangle1);
  return positionAfterTriangle1;
}

