

#include "Triangle2.h"

typedef uint8_t *Dtuple2_uint8T___;

static inline uint64_t
ValidateTriangleCorners(
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
        Validator for field _triangle_corners
        of type Triangle2._triangle
--*/
{
  /* Validating field corners */
  uint64_t positionAfterTriangle;
  if ((uint32_t)4U * (uint32_t)(uint8_t)3U % (uint32_t)4U == (uint32_t)0U)
  {
    if (((uint64_t)Uu - StartPosition) < (uint64_t)((uint32_t)4U * (uint32_t)(uint8_t)3U))
    {
      positionAfterTriangle = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
    }
    else
    {
      positionAfterTriangle = StartPosition + (uint64_t)((uint32_t)4U * (uint32_t)(uint8_t)3U);
    }
  }
  else
  {
    positionAfterTriangle = EVERPARSE_VALIDATOR_ERROR_LIST_SIZE_NOT_MULTIPLE;
  }
  if (EverParseIsSuccess(positionAfterTriangle))
  {
    return positionAfterTriangle;
  }
  Err("_triangle",
    "_triangle_corners",
    EverParseErrorReasonOfResult(positionAfterTriangle),
    Ctxt,
    Uu,
    Input,
    StartPosition,
    positionAfterTriangle);
  return positionAfterTriangle;
}

uint64_t
Triangle2ValidateTriangle(
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
  /* Field _triangle_corners */
  uint64_t positionAfterTriangle = ValidateTriangleCorners(Ctxt, Err, Uu, Input, StartPosition);
  if (EverParseIsSuccess(positionAfterTriangle))
  {
    return positionAfterTriangle;
  }
  Err("_triangle",
    "corners",
    EverParseErrorReasonOfResult(positionAfterTriangle),
    Ctxt,
    Uu,
    Input,
    StartPosition,
    positionAfterTriangle);
  return positionAfterTriangle;
}

