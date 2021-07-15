

#include "BF.h"

static inline uint64_t
ValidateDummyEmp(
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
        Validator for field _dummy_emp
        of type BF._dummy
--*/
{
  /* Validating field emp */
  uint64_t positionAfterDummy = StartPosition;
  if (EverParseIsSuccess(positionAfterDummy))
  {
    return positionAfterDummy;
  }
  Err("_dummy",
    "_dummy_emp",
    EverParseErrorReasonOfResult(positionAfterDummy),
    Ctxt,
    Uu,
    Input,
    StartPosition,
    positionAfterDummy);
  return positionAfterDummy;
}

uint64_t
BfValidateDummy(
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
  /* Field _dummy_emp */
  uint64_t positionAfterDummy = ValidateDummyEmp(Ctxt, Err, Uu, Input, StartPosition);
  if (EverParseIsSuccess(positionAfterDummy))
  {
    return positionAfterDummy;
  }
  Err("_dummy",
    "emp",
    EverParseErrorReasonOfResult(positionAfterDummy),
    Ctxt,
    Uu,
    Input,
    StartPosition,
    positionAfterDummy);
  return positionAfterDummy;
}

void BfReadDummy(uint32_t InputLength, uint8_t *Input, uint32_t StartPosition)
{
  
}

