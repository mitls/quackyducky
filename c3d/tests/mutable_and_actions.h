#include <stdint.h>

typedef struct
  [[everparse::process(1)]]
  [[everparse::entrypoint]]
  [[everparse::mutable_parameter(UINT32 *x)]]
  [[everparse::mutable_parameter(UINT32 *y)]]
_Pair
{
   UINT32 first
       [[everparse::on_success(^{*x = first;
                                 return true; })]];
   UINT32 second
       [[everparse::on_success(^{*y = second;
                                 return true; })]];
} Pair;
