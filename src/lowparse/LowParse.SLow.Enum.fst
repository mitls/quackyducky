module LowParse.SLow.Enum
include LowParse.Size.Enum
include LowParse.SLow.Combinators

module L = FStar.List.Tot
module U32 = FStar.UInt32

(* Parser for enums *)

inline_for_extraction
let parse32_maybe_enum_key_gen
  (#k: parser_kind)
  (#key #repr: eqtype)
  (#p: parser k repr)
  (p32: parser32 p)
  (e: enum key repr)
  (k' : parser_kind)
  (t' : Type)
  (p' : parser k' t')
  (u1: unit { k' == k })
  (u15: unit { t' == maybe_enum_key e } )
  (u2: unit { p' == parse_maybe_enum_key p e } )
  (f: maybe_enum_key_of_repr'_t e)
: Tot (parser32 p')
= parse32_synth p (maybe_enum_key_of_repr e) f p32 ()

inline_for_extraction
let parse32_maybe_enum_key
  (#k: parser_kind)
  (#key #repr: eqtype)
  (#p: parser k repr)
  (p32: parser32 p)
  (e: enum key repr)
  (f: maybe_enum_key_of_repr'_t e)
: Tot (parser32 (parse_maybe_enum_key p e))
= parse32_maybe_enum_key_gen p32 e _ _ (parse_maybe_enum_key p e) () () () f

module B32 = LowParse.Bytes32

inline_for_extraction
let parse32_enum_key_gen
  (#k: parser_kind)
  (#key #repr: eqtype)
  (p: parser k repr)
  (e: enum key repr)
  (k' : parser_kind)
  (t' : Type)
  (p' : parser k' t')
  (u1: unit { k' == parse_filter_kind k } )
  (u15: unit { t' == enum_key e } )
  (u2: unit { p' == parse_enum_key p e } )
  (pe: parser32 (parse_maybe_enum_key p e))
: Tot (parser32 p')
= (fun (input: bytes32) -> ((
    [@inline_let]
    let _ =
      parse_enum_key_eq p e (B32.reveal input);
      parse_maybe_enum_key_eq p e (B32.reveal input)
    in
    match pe input with
    | Some (k, consumed) ->
      begin match k with
      | Known k' -> Some (k', consumed)
      | _ -> None
      end
    | _ -> None
  ) <: (res: option (enum_key e * U32.t) { parser32_correct (parse_enum_key p e) input res } )))

inline_for_extraction
let parse32_enum_key
  (#k: parser_kind)
  (#key #repr: eqtype)
  (#p: parser k repr)
  (p32: parser32 p)
  (e: enum key repr)
  (f: maybe_enum_key_of_repr'_t e)
: Tot (parser32 (parse_enum_key p e))
= parse32_enum_key_gen p e _ _ (parse_enum_key p e) () () () (parse32_maybe_enum_key p32 e f)

inline_for_extraction
let serialize32_enum_key_gen
  (#k: parser_kind)
  (#key #repr: eqtype)
  (#p: parser k repr)
  (#s: serializer p)
  (s32: serializer32 s)
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
: Tot (serializer32 s')
= fun (input: enum_key e) -> (
    [@inline_let]
    let _ = serialize_enum_key_eq s e input in
    (s32 (f input)) <: (r: bytes32 { serializer32_correct (serialize_enum_key p s e) input r } ))

inline_for_extraction
let serialize32_enum_key
  (#k: parser_kind)
  (#key #repr: eqtype)
  (#p: parser k repr)
  (#s: serializer p)
  (s32: serializer32 s)
  (e: enum key repr)
  (f: enum_repr_of_key'_t e)
: Tot (serializer32 (serialize_enum_key p s e))
= serialize32_enum_key_gen s32 e _ _ _ (serialize_enum_key p s e) () () () () f

inline_for_extraction
let serialize32_maybe_enum_key_gen'
  (#k: parser_kind)
  (#key #repr: eqtype)
  (#p: parser k repr)
  (#s: serializer p)
  (s32: serializer32 s)
  (e: enum key repr)
  (f: serializer32 (serialize_enum_key p s e))
: Tot (serializer32 (serialize_maybe_enum_key p s e))
= fun (input: maybe_enum_key e) -> ((
    [@inline_let]
    let _ = serialize_maybe_enum_key_eq s e input in
    match input with
    | Known k ->
        [@inline_let]
        let _ = serialize_enum_key_eq s e k in
        f k
    | Unknown r -> s32 r
   ) <: (r: bytes32 { serializer32_correct (serialize_maybe_enum_key p s e) input r } ))

inline_for_extraction
let serialize32_maybe_enum_key_gen
  (#k: parser_kind)
  (#key #repr: eqtype)
  (#p: parser k repr)
  (#s: serializer p)
  (s32: serializer32 s)
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
: Tot (serializer32 s')
= serialize32_maybe_enum_key_gen' s32 e
    (serialize32_enum_key_gen s32 e _ _ _ (serialize_enum_key _ s e) () () () () f)

inline_for_extraction
let serialize32_maybe_enum_key
  (#k: parser_kind)
  (#key #repr: eqtype)
  (#p: parser k repr)
  (#s: serializer p)
  (s32: serializer32 s)
  (e: enum key repr)
  (f: enum_repr_of_key'_t e)
: Tot (serializer32 (serialize_maybe_enum_key p s e))
= serialize32_maybe_enum_key_gen s32 e _ _ _ (serialize_maybe_enum_key p s e) () () () () f
