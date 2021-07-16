module LowParse.Size.Enum
include LowParse.Spec.Enum
include LowParse.Size.Combinators

module U32 = FStar.UInt32

inline_for_extraction
let size32_enum_key_gen
  (#k: parser_kind)
  (#key #repr: eqtype)
  (#p: parser k repr)
  (#s: serializer p)
  (s32: size32 s)
  (e: enum key repr)
  (k' : parser_kind)
  (t' : Type)
  (p' : parser k' t')
  (s' : serializer p')
  (u1: unit { k' == parse_filter_kind k } )
  (u15: unit { t' == enum_key e } )
  (u2: unit { p' == parse_enum_key p e } )
  (u3: unit { s' == serialize_enum_key p s e } )
  (f: enum_repr_of_key'_t e)
: Tot (size32 s')
= fun (input: enum_key e) -> (
    [@inline_let]
    let _ = serialize_enum_key_eq s e input in
    (s32 (f input)) <: (r: UInt32.t { size32_postcond (serialize_enum_key p s e) input r } ))

inline_for_extraction
let size32_enum_key
  (#k: parser_kind)
  (#key #repr: eqtype)
  (#p: parser k repr)
  (#s: serializer p)
  (s32: size32 s)
  (e: enum key repr)
  (f: enum_repr_of_key'_t e)
: Tot (size32 (serialize_enum_key p s e))
= size32_enum_key_gen s32 e _ _ _ (serialize_enum_key p s e) () () () () f

inline_for_extraction
let size32_maybe_enum_key_gen'
  (#k: parser_kind)
  (#key #repr: eqtype)
  (#p: parser k repr)
  (#s: serializer p)
  (s32: size32 s)
  (e: enum key repr)
  (f: size32 (serialize_enum_key p s e))
: Tot (size32 (serialize_maybe_enum_key p s e))
= fun (input: maybe_enum_key e) -> ((
    [@inline_let]
    let _ = serialize_maybe_enum_key_eq s e input in
    match input with
    | Known k ->
      [@inline_let]
      let _ = serialize_enum_key_eq s e k in
      f k
    | Unknown r -> s32 r
   ) <: (r: U32.t { size32_postcond (serialize_maybe_enum_key p s e) input r } ))

inline_for_extraction
let size32_maybe_enum_key_gen
  (#k: parser_kind)
  (#key #repr: eqtype)
  (#p: parser k repr)
  (#s: serializer p)
  (s32: size32 s)
  (e: enum key repr)
  (k' : parser_kind)
  (t' : Type)
  (p' : parser k' t')
  (s' : serializer p')
  (u1: unit { k == k' } )
  (u15: unit { t' == maybe_enum_key e } )
  (u2: unit { p' == parse_maybe_enum_key p e } )
  (u3: unit { s' == serialize_maybe_enum_key p s e } )
  (f: enum_repr_of_key'_t e)
: Tot (size32 s')
= size32_maybe_enum_key_gen' s32 e
    (size32_enum_key_gen s32 e _ _ _ (serialize_enum_key _ s e) () () () () f)

inline_for_extraction
let size32_maybe_enum_key
  (#k: parser_kind)
  (#key #repr: eqtype)
  (#p: parser k repr)
  (#s: serializer p)
  (s32: size32 s)
  (e: enum key repr)
  (f: enum_repr_of_key'_t e)
: Tot (size32 (serialize_maybe_enum_key p s e))
= size32_maybe_enum_key_gen  s32 e _ _ _ (serialize_maybe_enum_key p s e) () () () () f
