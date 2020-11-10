

#ifndef __BoundedSumWhere_H
#define __BoundedSumWhere_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "EverParse.h"


#include "Smoker.h"

uint64_t
BoundedSumWhereValidateBoundedSum(
  uint32_t Bound,
  uint32_t Uu,
  uint8_t *Input,
  uint64_t StartPosition
);

#if defined(__cplusplus)
}
#endif

#define __BoundedSumWhere_H_DEFINED
#endif
