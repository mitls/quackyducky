
typedef struct [[
  everparse::process(0),
  everparse::entrypoint
]] _POINT3
{
  UINT32  x[3];
} POINT3, *PPOINT3;

typedef struct [[
  everparse::process(0),
  everparse::entrypoint,
  everparse::parameter(UINT32 len)
]] _POINTNPARAM
{
  UINT8 dummy;
  UINT32  x                 [[everparse::byte_size(len)]]
            [EVERPARSE_VLA];
} POINTNPARAM, *PPOINTNPARAM;

typedef struct [[
  everparse::process(0),
  everparse::entrypoint,
  everparse::parameter(UINT32 len)
]] _POINTNPARAM2
{
  UINT8 dummy        [[everparse::on_success(
                          ^{return (dummy < 25);}
                       )]];
  UINT32  x                 [[everparse::byte_size_at_most(len)]]
            [EVERPARSE_VLA];
} POINTNPARAM2, *PPOINTNPARAM2;