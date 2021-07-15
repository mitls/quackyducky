

#include "Derived.h"

static inline uint64_t
ValidateTriplePair(
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
        Validator for field _Triple_pair
        of type Derived._Triple
--*/
{
  /* SNIPPET_START: Triple */
  uint64_t positionAfterTriple = BaseValidatePair(Ctxt, Err, Uu, Input, StartPosition);
  if (EverParseIsSuccess(positionAfterTriple))
  {
    return positionAfterTriple;
  }
  Err("_Triple",
    "_Triple_pair",
    EverParseErrorReasonOfResult(positionAfterTriple),
    Ctxt,
    Uu,
    Input,
    StartPosition,
    positionAfterTriple);
  return positionAfterTriple;
}

static inline uint64_t
ValidateTripleThird(
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
        Validator for field _Triple_third
        of type Derived._Triple
--*/
{
  /* Validating field third */
  uint64_t positionAfterTriple = BaseValidateUlong(Ctxt, Err, Uu, Input, StartPosition);
  if (EverParseIsSuccess(positionAfterTriple))
  {
    return positionAfterTriple;
  }
  Err("_Triple",
    "_Triple_third",
    EverParseErrorReasonOfResult(positionAfterTriple),
    Ctxt,
    Uu,
    Input,
    StartPosition,
    positionAfterTriple);
  return positionAfterTriple;
}

uint64_t
DerivedValidateTriple(
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
  /* Field _Triple_pair */
  uint64_t positionAfterTriple = ValidateTriplePair(Ctxt, Err, Uu, Input, StartPosition);
  uint64_t positionAfterpair;
  if (EverParseIsSuccess(positionAfterTriple))
  {
    positionAfterpair = positionAfterTriple;
  }
  else
  {
    Err("_Triple",
      "pair",
      EverParseErrorReasonOfResult(positionAfterTriple),
      Ctxt,
      Uu,
      Input,
      StartPosition,
      positionAfterTriple);
    positionAfterpair = positionAfterTriple;
  }
  if (EverParseIsError(positionAfterpair))
  {
    return positionAfterpair;
  }
  /* Field _Triple_third */
  uint64_t positionAfterTriple0 = ValidateTripleThird(Ctxt, Err, Uu, Input, positionAfterpair);
  if (EverParseIsSuccess(positionAfterTriple0))
  {
    return positionAfterTriple0;
  }
  Err("_Triple",
    "third",
    EverParseErrorReasonOfResult(positionAfterTriple0),
    Ctxt,
    Uu,
    Input,
    positionAfterpair,
    positionAfterTriple0);
  return positionAfterTriple0;
}

static inline uint64_t
ValidateQuad12(
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
        Validator for field _Quad__12
        of type Derived._Quad
--*/
{
  /* Validating field _12 */
  uint64_t positionAfterQuad = BaseValidatePair(Ctxt, Err, Uu, Input, StartPosition);
  if (EverParseIsSuccess(positionAfterQuad))
  {
    return positionAfterQuad;
  }
  Err("_Quad",
    "_Quad__12",
    EverParseErrorReasonOfResult(positionAfterQuad),
    Ctxt,
    Uu,
    Input,
    StartPosition,
    positionAfterQuad);
  return positionAfterQuad;
}

static inline uint64_t
ValidateQuad34(
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
        Validator for field _Quad__34
        of type Derived._Quad
--*/
{
  /* Validating field _34 */
  uint64_t positionAfterQuad = BaseValidatePair(Ctxt, Err, Uu, Input, StartPosition);
  if (EverParseIsSuccess(positionAfterQuad))
  {
    return positionAfterQuad;
  }
  Err("_Quad",
    "_Quad__34",
    EverParseErrorReasonOfResult(positionAfterQuad),
    Ctxt,
    Uu,
    Input,
    StartPosition,
    positionAfterQuad);
  return positionAfterQuad;
}

uint64_t
DerivedValidateQuad(
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
  /* Field _Quad__12 */
  uint64_t positionAfterQuad = ValidateQuad12(Ctxt, Err, Uu, Input, StartPosition);
  uint64_t positionAfter12;
  if (EverParseIsSuccess(positionAfterQuad))
  {
    positionAfter12 = positionAfterQuad;
  }
  else
  {
    Err("_Quad",
      "_12",
      EverParseErrorReasonOfResult(positionAfterQuad),
      Ctxt,
      Uu,
      Input,
      StartPosition,
      positionAfterQuad);
    positionAfter12 = positionAfterQuad;
  }
  if (EverParseIsError(positionAfter12))
  {
    return positionAfter12;
  }
  /* Field _Quad__34 */
  uint64_t positionAfterQuad0 = ValidateQuad34(Ctxt, Err, Uu, Input, positionAfter12);
  if (EverParseIsSuccess(positionAfterQuad0))
  {
    return positionAfterQuad0;
  }
  Err("_Quad",
    "_34",
    EverParseErrorReasonOfResult(positionAfterQuad0),
    Ctxt,
    Uu,
    Input,
    positionAfter12,
    positionAfterQuad0);
  return positionAfterQuad0;
}

