/*++

Copyright (c) Microsoft Corporation

Module Name:

EverParseEndianness.h

Abstract:

This is an EverParse-related file to read integer values from raw
bytes.

Authors:

nswamy, protz, taramana 5-Feb-2020

--*/
/* This is a hand-written header that selectively includes relevant bits from
 * kremlib.h -- it has to be updated manually to track upstream changes. */

#ifndef __EverParseEndianness_H
#define __EverParseEndianness_H

#if defined(__cplusplus)
extern "C" {
#endif

/*****************************************************************************
 ********* Implementation of LowStar.Endianness (selected bits) **************
 *****************************************************************************/

#include <string.h>
#include <stdint.h>

typedef const char * EverParseString;

/* ... for Windows (MSVC)... not targeting XBOX 360! */
#if defined(_MSC_VER)

#  include <stdlib.h>
#  include <windef.h>

#  define htobe16(x) _byteswap_ushort(x)
#  define htole16(x) (x)
#  define be16toh(x) _byteswap_ushort(x)
#  define le16toh(x) (x)

#  define htobe32(x) _byteswap_ulong(x)
#  define htole32(x) (x)
#  define be32toh(x) _byteswap_ulong(x)
#  define le32toh(x) (x)

#  define htobe64(x) _byteswap_uint64(x)
#  define htole64(x) (x)
#  define be64toh(x) _byteswap_uint64(x)
#  define le64toh(x) (x)

#else

typedef uint8_t BOOLEAN;
#define FALSE 0
#define TRUE 1

/* ... for Linux */
#if defined(__linux__) || defined(__CYGWIN__) || defined (__USE_SYSTEM_ENDIAN_H__)
#  include <endian.h>


/* ... for OSX */
#elif defined(__APPLE__)
#  include <libkern/OSByteOrder.h>
#  define htole64(x) OSSwapHostToLittleInt64(x)
#  define le64toh(x) OSSwapLittleToHostInt64(x)
#  define htobe64(x) OSSwapHostToBigInt64(x)
#  define be64toh(x) OSSwapBigToHostInt64(x)

#  define htole16(x) OSSwapHostToLittleInt16(x)
#  define le16toh(x) OSSwapLittleToHostInt16(x)
#  define htobe16(x) OSSwapHostToBigInt16(x)
#  define be16toh(x) OSSwapBigToHostInt16(x)

#  define htole32(x) OSSwapHostToLittleInt32(x)
#  define le32toh(x) OSSwapLittleToHostInt32(x)
#  define htobe32(x) OSSwapHostToBigInt32(x)
#  define be32toh(x) OSSwapBigToHostInt32(x)

/* ... for other BSDs */
#elif defined(__FreeBSD__) || defined(__NetBSD__) || defined(__DragonFly__)
#  include <sys/endian.h>
#elif defined(__OpenBSD__)
#  include <endian.h>

/* ... for Windows (GCC-like, e.g. mingw or clang) */
#elif (defined(_WIN32) || defined(_WIN64)) &&                                  \
    (defined(__GNUC__) || defined(__clang__))

#  define htobe16(x) __builtin_bswap16(x)
#  define htole16(x) (x)
#  define be16toh(x) __builtin_bswap16(x)
#  define le16toh(x) (x)

#  define htobe32(x) __builtin_bswap32(x)
#  define htole32(x) (x)
#  define be32toh(x) __builtin_bswap32(x)
#  define le32toh(x) (x)

#  define htobe64(x) __builtin_bswap64(x)
#  define htole64(x) (x)
#  define be64toh(x) __builtin_bswap64(x)
#  define le64toh(x) (x)

#else

#error "Unsupported platform"

#endif

#endif

inline static uint16_t Load16(uint8_t *b) {
  uint16_t x;
  memcpy(&x, b, 2);
  return x;
}

inline static uint32_t Load32(uint8_t *b) {
  uint32_t x;
  memcpy(&x, b, 4);
  return x;
}

inline static uint64_t Load64(uint8_t *b) {
  uint64_t x;
  memcpy(&x, b, 8);
  return x;
}

inline static void Store16(uint8_t *b, uint16_t i) {
  memcpy(b, &i, 2);
}

inline static void Store32(uint8_t *b, uint32_t i) {
  memcpy(b, &i, 4);
}

inline static void Store64(uint8_t *b, uint64_t i) {
  memcpy(b, &i, 8);
}

#define Load16Le(b) (le16toh(Load16(b)))
#define Store16Le(b, i) (Store16(b, htole16(i)))
#define Load16Be(b) (be16toh(Load16(b)))
#define Store16Be(b, i) (Store16(b, htobe16(i)))

#define Load32Le(b) (le32toh(Load32(b)))
#define Store32Le(b, i) (Store32(b, htole32(i)))
#define Load32Be(b) (be32toh(Load32(b)))
#define Store32Be(b, i) (Store32(b, htobe32(i)))

#define Load64Le(b) (le64toh(Load64(b)))
#define Store64Le(b, i) (Store64(b, htole64(i)))
#define Load64Be(b) (be64toh(Load64(b)))
#define Store64Be(b, i) (Store64(b, htobe64(i)))


#if defined(__cplusplus)
}
#endif

#endif
