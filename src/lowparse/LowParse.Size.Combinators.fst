module LowParse.Size.Combinators
include LowParse.Size.Base
include LowParse.Spec.Combinators

module U32 = FStar.UInt32

inline_for_extraction
let size32_ret
  (#t: Type)
  (v: t)
  (v_unique: (v' : t) -> Lemma (v == v'))
: Tot (size32 #_ #_ #(parse_ret v) (serialize_ret v v_unique))
= size32_constant #_ #_ #(parse_ret v) (serialize_ret v v_unique) 0ul ()

inline_for_extraction
let size32_empty : size32 #_ #_ #parse_empty serialize_empty
= size32_ret () (fun _ -> ())

inline_for_extraction
let size32_false : size32 #_ #_ #parse_false serialize_false = fun input -> 0ul

let serialize32_kind_precond
  (k1 k2: parser_kind)
: GTot bool
= Some? k1.parser_kind_high &&
  Some? k2.parser_kind_high &&
  Some?.v k1.parser_kind_high + Some?.v k2.parser_kind_high < 4294967296

inline_for_extraction
let size32_nondep_then
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (#s1: serializer p1)
  (s1' : size32 s1 { k1.parser_kind_subkind == Some ParserStrong } )
  (#k2: parser_kind)
  (#t2: Type)
  (#p2: parser k2 t2)
  (#s2: serializer p2)
  (s2' : size32 s2)
: Tot (size32 (serialize_nondep_then s1 s2))
= fun x ->
  [@inline_let] let _ = serialize_nondep_then_eq s1 s2 x in
  match x with
  | (x1, x2) ->
    let v1 = s1' x1 in
    let v2 = s2' x2 in
    let res = add_overflow v1 v2 in
    (res <: (z : U32.t { size32_postcond (serialize_nondep_then s1 s2) x z } ))

inline_for_extraction
let size32_dtuple2
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (#s1: serializer p1)
  (s1' : size32 s1 { k1.parser_kind_subkind == Some ParserStrong } )
  (#k2: parser_kind)
  (#t2: t1 -> Tot Type)
  (#p2: (x: t1) -> Tot (parser k2 (t2 x)))
  (#s2: (x: t1) -> Tot (serializer (p2 x)))
  (s2' : (x: t1) -> Tot (size32 (s2 x)))
: Tot (size32 (serialize_dtuple2 s1 s2))
= fun x ->
  [@inline_let] let _ = serialize_dtuple2_eq s1 s2 x in
  match x with
  | (| x1, x2 |) ->
    let v1 = s1' x1 in
    let v2 = s2' x1 x2 in
    let res = add_overflow v1 v2 in
    (res <: (z : U32.t { size32_postcond (serialize_dtuple2 s1 s2) x z } ))

inline_for_extraction
let size32_filter
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (#s: serializer p)
  (s32: size32 s)
  (f: (t -> GTot bool))
: Tot (size32 #_ #_ #(parse_filter p f) (serialize_filter s f))
= fun x -> s32 x

inline_for_extraction
let size32_synth
  (#k: parser_kind)
  (#t1: Type)
  (#t2: Type)
  (p1: parser k t1)
  (f2: t1 -> GTot t2)
  (s1: serializer p1)
  (s1' : size32 s1)
  (g1: t2 -> GTot t1)
  (g1': (x: t2) -> Tot (y: t1 { y == g1 x } ) )
  (u: unit {
    synth_inverse f2 g1 /\
    synth_injective f2
  })
: Tot (size32 (serialize_synth p1 f2 s1 g1 u))
= fun (input: t2) ->
    [@inline_let] let _ = serialize_synth_eq p1 f2 s1 g1 u input in
    [@inline_let] let x = g1' input in
    [@inline_let] let y = s1' x in
    (y <: (res: U32.t { size32_postcond (serialize_synth p1 f2 s1 g1 u) input res } ))

inline_for_extraction
let size32_synth'
  (#k: parser_kind)
  (#t1: Type)
  (#t2: Type)
  (p1: parser k t1)
  (f2: t1 -> GTot t2)
  (s1: serializer p1)
  (s1' : size32 s1)
  (g1: t2 -> Tot t1)
  (u: unit {
    synth_inverse f2 g1 /\
    synth_injective f2
  })
: Tot (size32 (serialize_synth p1 f2 s1 g1 u))
= size32_synth p1 f2 s1 s1' g1 (fun x -> g1 x) u

inline_for_extraction
let size32_compose_context
  (#pk: parser_kind)
  (#kt1 #kt2: Type)
  (f: (kt2 -> Tot kt1))
  (t: (kt1 -> Tot Type))
  (p: ((k: kt1) -> Tot (parser pk (t k))))
  (s: ((k: kt1) -> Tot (serializer (p k))))
  (s32: ((k: kt1) -> Tot (size32 (s k))))
  (k: kt2)
: Tot (size32 (s (f k)))
= fun input -> s32 (f k) input

inline_for_extraction
let size32_weaken
  (k1: parser_kind)
  (#k2: parser_kind)
  (#t: Type)
  (#p2: parser k2 t)
  (#s2: serializer p2)
  (s2' : size32 s2 { k1 `is_weaker_than` k2 })
: Tot (size32 (serialize_weaken k1 s2))
= fun x -> s2' x
