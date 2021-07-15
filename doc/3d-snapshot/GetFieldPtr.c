

#include "GetFieldPtr.h"

static inline uint64_t
ValidateTF1(
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
        Validator for field _T_f1
        of type GetFieldPtr._T
--*/
{
  /* SNIPPET_START: GetFieldPtr.T */
  uint64_t positionAfterT;
  if (((uint64_t)Uu - StartPosition) < (uint64_t)(uint32_t)(uint8_t)10U)
  {
    positionAfterT = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  else
  {
    positionAfterT = StartPosition + (uint64_t)(uint32_t)(uint8_t)10U;
  }
  if (EverParseIsSuccess(positionAfterT))
  {
    return positionAfterT;
  }
  Err("_T",
    "_T_f1",
    EverParseErrorReasonOfResult(positionAfterT),
    Ctxt,
    Uu,
    Input,
    StartPosition,
    positionAfterT);
  return positionAfterT;
}

static inline uint64_t
ValidateTF2(
  uint8_t **Out,
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
        Validator for field _T_f2
        of type GetFieldPtr._T
--*/
{
  /* Validating field f2 */
  uint64_t positionAfterT;
  if (((uint64_t)Uu - StartPosition) < (uint64_t)(uint32_t)(uint8_t)20U)
  {
    positionAfterT = EVERPARSE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  }
  else
  {
    positionAfterT = StartPosition + (uint64_t)(uint32_t)(uint8_t)20U;
  }
  uint64_t positionAfterT0;
  if (EverParseIsSuccess(positionAfterT))
  {
    positionAfterT0 = positionAfterT;
  }
  else
  {
    Err("_T",
      "_T_f2.base",
      EverParseErrorReasonOfResult(positionAfterT),
      Ctxt,
      Uu,
      Input,
      StartPosition,
      positionAfterT);
    positionAfterT0 = positionAfterT;
  }
  uint64_t positionAfterT1;
  if (EverParseIsSuccess(positionAfterT0))
  {
    uint8_t *base = Input;
    uint8_t *x = base + (uint32_t)StartPosition;
    *Out = x;
    BOOLEAN actionSuccessT = TRUE;
    if (!actionSuccessT)
    {
      positionAfterT1 = EVERPARSE_VALIDATOR_ERROR_ACTION_FAILED;
    }
    else
    {
      positionAfterT1 = positionAfterT0;
    }
  }
  else
  {
    positionAfterT1 = positionAfterT0;
  }
  if (EverParseIsSuccess(positionAfterT1))
  {
    return positionAfterT1;
  }
  Err("_T",
    "_T_f2",
    EverParseErrorReasonOfResult(positionAfterT1),
    Ctxt,
    Uu,
    Input,
    StartPosition,
    positionAfterT1);
  return positionAfterT1;
}

uint64_t
GetFieldPtrValidateT(
  uint8_t **Out,
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
  /* Field _T_f1 */
  uint64_t positionAfterT = ValidateTF1(Ctxt, Err, Uu, Input, StartPosition);
  uint64_t positionAfterf1;
  if (EverParseIsSuccess(positionAfterT))
  {
    positionAfterf1 = positionAfterT;
  }
  else
  {
    Err("_T",
      "f1",
      EverParseErrorReasonOfResult(positionAfterT),
      Ctxt,
      Uu,
      Input,
      StartPosition,
      positionAfterT);
    positionAfterf1 = positionAfterT;
  }
  if (EverParseIsError(positionAfterf1))
  {
    return positionAfterf1;
  }
  /* Field _T_f2 */
  uint64_t positionAfterT0 = ValidateTF2(Out, Ctxt, Err, Uu, Input, positionAfterf1);
  if (EverParseIsSuccess(positionAfterT0))
  {
    return positionAfterT0;
  }
  Err("_T",
    "f2",
    EverParseErrorReasonOfResult(positionAfterT0),
    Ctxt,
    Uu,
    Input,
    positionAfterf1,
    positionAfterT0);
  return positionAfterT0;
}

