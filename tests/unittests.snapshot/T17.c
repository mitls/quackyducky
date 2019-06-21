/* 
  This file was generated by KreMLin <https://github.com/FStarLang/kremlin>
  KreMLin invocation: krml -I ../../src/lowparse -skip-compilation -tmpdir ../unittests.snapshot -bundle LowParse.\* -drop FStar.Tactics.\* -drop FStar.Reflection.\* T10.fst T11.fst T11_z.fst T12.fst T12_z.fst T13.fst T13_x.fst T14.fst T14_x.fst T15_body.fst T15.fst T16.fst T16_x.fst T17.fst T17_x_a.fst T17_x_b.fst T18.fst T18_x_a.fst T18_x_b.fst T19.fst T1.fst T20.fst T21.fst T22_body_a.fst T22_body_b.fst T22.fst T23.fst T24.fst T24_y.fst T25_bpayload.fst T25.fst T25_payload.fst T26.fst T27.fst T28.fst T29.fst T2.fst T30.fst T31.fst T32.fst T33.fst T34.fst T35.fst T36.fst T3.fst T4.fst T5.fst T6.fst T6le.fst T7.fst T8.fst T8_z.fst T9_b.fst T9.fst Tag2.fst Tag.fst Tagle.fst -warn-error +9
  F* version: 74c6d2a5
  KreMLin version: 1bd260eb
 */

#include "T17.h"

bool T17_uu___is_X_a(T17_t17 projectee)
{
  if (projectee.tag == T17_X_a)
    return true;
  else
    return false;
}

bool T17_uu___is_X_b(T17_t17 projectee)
{
  if (projectee.tag == T17_X_b)
    return true;
  else
    return false;
}

T13_t13 T17___proj__X_b__item___0(T17_t17 projectee)
{
  if (projectee.tag == T17_X_b)
    return projectee._0;
  else
  {
    KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

Tag_tag T17_tag_of_t17(T17_t17 x)
{
  if (x.tag == T17_X_a)
    return Tag_A;
  else if (x.tag == T17_X_b)
    return Tag_B;
  else
  {
    KRML_HOST_EPRINTF("KreMLin abort at %s:%d\n%s\n",
      __FILE__,
      __LINE__,
      "unreachable (pattern matches are exhaustive in F*)");
    KRML_HOST_EXIT(255U);
  }
}

uint32_t T17_t17_validator(LowParse_Slice_slice input, uint32_t pos)
{
  uint32_t len_after_tag;
  if (input.len - pos < (uint32_t)1U)
    len_after_tag = LOWPARSE_LOW_BASE_VALIDATOR_ERROR_NOT_ENOUGH_DATA;
  else
    len_after_tag = pos + (uint32_t)1U;
  if (LOWPARSE_LOW_BASE_VALIDATOR_MAX_LENGTH < len_after_tag)
    return len_after_tag;
  else
  {
    uint8_t k_ = LowParse_Low_Int_read_u8(input, pos);
    if (k_ == (uint8_t)0U)
      return T17_x_a_t17_x_a_validator(input, len_after_tag);
    else if (k_ == (uint8_t)1U)
      return T17_x_b_t17_x_b_validator(input, len_after_tag);
    else
      return LOWPARSE_LOW_BASE_VALIDATOR_ERROR_GENERIC;
  }
}

uint32_t T17_t17_jumper(LowParse_Slice_slice input, uint32_t pos)
{
  uint32_t pos_after_tag = pos + (uint32_t)1U;
  uint8_t k_ = LowParse_Low_Int_read_u8(input, pos);
  if (k_ == (uint8_t)0U)
    return T17_x_a_t17_x_a_jumper(input, pos_after_tag);
  else if (k_ == (uint8_t)1U)
    return T17_x_b_t17_x_b_jumper(input, pos_after_tag);
  else
    return (uint32_t)0U;
}

uint32_t T17_t17_accessor_a(LowParse_Slice_slice input, uint32_t pos)
{
  return pos + (uint32_t)1U;
}

uint32_t T17_t17_accessor_b(LowParse_Slice_slice input, uint32_t pos)
{
  return pos + (uint32_t)1U;
}
