module LowParse.SLow.Combinators
include LowParse.SLow.Base
include LowParse.Size.Combinators

module B32 = FStar.Bytes
module U32 = FStar.UInt32

#reset-options "--z3rlimit 16 --max_fuel 8 --max_ifuel 8"

inline_for_extraction
let parse32_ret
  (#t: Type)
  (x: t)
: Tot (parser32 (parse_ret x))
= (fun input -> ((Some (x, 0ul)) <: (res: option (t * U32.t) { parser32_correct (parse_ret x) input res } )))

inline_for_extraction
let parse32_empty : parser32 parse_empty = parse32_ret ()

inline_for_extraction
let serialize32_ret
  (#t: Type)
  (v: t)
  (v_unique: (v' : t) -> Lemma (v == v'))
: Tot (serializer32 (serialize_ret v v_unique))
= fun input ->
  [@inline_let]
  let b = B32.empty_bytes in
  assert (B32.reveal b `Seq.equal` Seq.empty);
  (b <: (b: bytes32 { serializer32_correct #_ #_ #(parse_ret v) (serialize_ret v v_unique) input b } ))

inline_for_extraction
let serialize32_empty : serializer32 #_ #_ #parse_empty serialize_empty
= serialize32_ret () (fun _ -> ())

inline_for_extraction
let parse32_false : parser32 parse_false = fun _ -> None

inline_for_extraction
let serialize32_false : serializer32 #_ #_ #parse_false serialize_false = fun input -> B32.empty_bytes

inline_for_extraction
let parse32_and_then
  (#k: parser_kind)
  (#t:Type)
  (#p:parser k t)
  (p32: parser32 p)
  (#k': parser_kind)
  (#t':Type)
  (p': (t -> Tot (parser k' t')))
  (u: unit { and_then_cases_injective p' } )
  (p32' : ((x: t) -> Tot (parser32 (p' x))))
: Tot (parser32 (p `and_then` p'))
= fun (input: bytes32) ->
  ((
  [@inline_let] let _ = and_then_eq p p' (B32.reveal input) in
  match p32 input with
  | Some (v, l) ->
    let input' = B32.slice input l (B32.len input) in
    begin match p32' v input' with
    | Some (v', l') ->
      Some (v', U32.add l l')
    | _ -> None
    end
  | _ -> None
  ) <: (res: option (t' * U32.t) { parser32_correct (p `and_then` p') input res } ))

inline_for_extraction
let parse32_nondep_then
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (p1' : parser32 p1)
  (#k2: parser_kind)
  (#t2: Type)
  (#p2: parser k2 t2)
  (p2' : parser32 p2)
: Tot (parser32 (nondep_then p1 p2))
= fun (input: bytes32) ->
  ((
  [@inline_let] let _ = nondep_then_eq p1 p2 (B32.reveal input) in
  match p1' input with
  | Some (v, l) ->
    let input' = B32.slice input l (B32.len input) in
    begin match p2' input' with
    | Some (v', l') ->
      Some ((v, v'), U32.add l l')
    | _ -> None
    end
  | _ -> None
  ) <: (res: option ((t1 * t2) * U32.t) { parser32_correct (p1 `nondep_then` p2) input res } ))

inline_for_extraction
let serialize32_nondep_then
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (#s1: serializer p1)
  (s1' : serializer32 s1 { k1.parser_kind_subkind == Some ParserStrong } )
  (#k2: parser_kind)
  (#t2: Type)
  (#p2: parser k2 t2)
  (#s2: serializer p2)
  (s2' : serializer32 s2 {
    serialize32_kind_precond k1 k2
  })
: Tot (serializer32 (serialize_nondep_then s1 s2))
= fun (input: t1 * t2) ->
  [@inline_let]
  let _ = serialize_nondep_then_eq s1 s2 input in
  match input with
  | (fs, sn) ->
    let output1 = s1' fs in
    let output2 = s2' sn in
    [@inline_let]
    let _ = assert (B32.length output1 == Seq.length (serialize s1 fs)) in
    [@inline_let]
    let _ = assert (B32.length output2 == Seq.length (serialize s2 sn)) in
  ((B32.append output1 output2) <:
    (res: bytes32 { serializer32_correct (serialize_nondep_then s1 s2) input res } ))

inline_for_extraction
let parse32_dtuple2
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (p1' : parser32 p1)
  (#k2: parser_kind)
  (#t2: (t1 -> Tot Type))
  (#p2: (x: t1) -> Tot (parser k2 (t2 x)))
  (p2' : (x: t1) -> Tot (parser32 (p2 x)))
: Tot (parser32 (parse_dtuple2 p1 p2))
= fun (input: bytes32) ->
  ((
  [@inline_let] let _ = parse_dtuple2_eq p1 p2 (B32.reveal input) in
  match p1' input with
  | Some (v, l) ->
    let input' = B32.slice input l (B32.len input) in
    begin match p2' v input' with
    | Some (v', l') ->
      Some ((| v, v' |), U32.add l l')
    | _ -> None
    end
  | _ -> None
  ) <: (res: option (dtuple2 t1 t2 * U32.t) { parser32_correct (parse_dtuple2 p1 p2) input res } ))

inline_for_extraction
let serialize32_dtuple2
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (#s1: serializer p1)
  (s1' : serializer32 s1 { k1.parser_kind_subkind == Some ParserStrong } )
  (#k2: parser_kind {
    serialize32_kind_precond k1 k2
  })
  (#t2: t1 -> Tot Type)
  (#p2: (x: t1) -> Tot (parser k2 (t2 x)))
  (#s2: (x: t1) -> Tot (serializer (p2 x)))
  (s2' : (x: t1) -> serializer32 (s2 x))
: Tot (serializer32 (serialize_dtuple2 s1 s2))
= fun (input: dtuple2 t1 t2) ->
  [@inline_let]
  let _ = serialize_dtuple2_eq s1 s2 input in
  match input with
  | (| fs, sn |) ->
    let output1 = s1' fs in
    let output2 = s2' fs sn in
    [@inline_let]
    let _ = assert (B32.length output1 == Seq.length (serialize s1 fs)) in
    [@inline_let]
    let _ = assert (B32.length output2 == Seq.length (serialize (s2 fs) sn)) in
  ((B32.append output1 output2) <:
    (res: bytes32 { serializer32_correct (serialize_dtuple2 s1 s2) input res } ))

inline_for_extraction
let parse32_strengthen
  (#k: parser_kind)
  (#t1: Type)
  (#p1: parser k t1)
  (p1' : parser32 p1)
  (p2: t1 -> GTot Type0)
  (prf: parse_strengthen_prf p1 p2)
: Tot (parser32 (parse_strengthen p1 p2 prf))
= fun (xbytes: bytes32) -> ((
  match p1' xbytes with
  | Some (x, consumed) ->
    [@inline_let]
    let _ = prf (B32.reveal xbytes) (U32.v consumed) x in
    [@inline_let]
    let (x' : t1 { p2 x' } ) = x in
    Some (x', consumed)
  | _ -> None
  ) <: (res: option ((x: t1 { p2 x}) * U32.t) { parser32_correct (parse_strengthen p1 p2 prf) xbytes res } ))

inline_for_extraction
let parse32_synth
  (#k: parser_kind)
  (#t1: Type)
  (#t2: Type)
  (p1: parser k t1)
  (f2: t1 -> GTot t2)
  (f2': (x: t1) -> Tot (y: t2 { y == f2 x } )) 
  (p1' : parser32 p1)
  (u: unit {
    synth_injective f2
  })
: Tot (parser32 (parse_synth p1 f2))
= fun (input: bytes32) ->
  ((
    [@inline_let] let _ = parse_synth_eq p1 f2 (B32.reveal input) in
    match p1' input with
    | Some (v1, consumed) -> Some (f2' v1, consumed)
    | _ -> None
   ) <: (res: option (t2 * U32.t) { parser32_correct (parse_synth p1 f2) input res } ))

inline_for_extraction
let parse32_synth'
  (#k: parser_kind)
  (#t1: Type)
  (#t2: Type)
  (p1: parser k t1)
  (f2: t1 -> Tot t2)
  (p1' : parser32 p1)
  (u: unit {
    synth_injective f2
  })
: Tot (parser32 (parse_synth p1 f2))
= parse32_synth p1 f2 (fun x -> f2 x) p1' u

inline_for_extraction
let serialize32_synth
  (#k: parser_kind)
  (#t1: Type)
  (#t2: Type)
  (p1: parser k t1)
  (f2: t1 -> GTot t2)
  (s1: serializer p1)
  (s1' : serializer32 s1)
  (g1: t2 -> GTot t1)
  (g1': (x: t2) -> Tot (y: t1 { y == g1 x } ) )
  (u: unit {
    synth_inverse f2 g1 /\
    synth_injective f2
  })
: Tot (serializer32 (serialize_synth p1 f2 s1 g1 u))
= fun (input: t2) ->
    [@inline_let] let _ = serialize_synth_eq p1 f2 s1 g1 u input in
    let x = g1' input in
    (s1' x <: (res: bytes32 { serializer32_correct (serialize_synth p1 f2 s1 g1 u) input res } ))

inline_for_extraction
let serialize32_synth'
  (#k: parser_kind)
  (#t1: Type)
  (#t2: Type)
  (p1: parser k t1)
  (f2: t1 -> GTot t2)
  (s1: serializer p1)
  (s1' : serializer32 s1)
  (g1: t2 -> Tot t1)
  (u: unit {
    synth_inverse f2 g1 /\
    synth_injective f2
  })
= serialize32_synth p1 f2 s1 s1' g1 (fun x -> g1 x) u

inline_for_extraction
let parse32_filter
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (p32: parser32 p)
  (f: (t -> GTot bool))
  (g: ((x: t) -> Tot (b: bool { b == f x } )))
: Tot (parser32 (parse_filter p f))
= fun (input: bytes32) ->
  ((
    [@inline_let] let _ = parse_filter_eq p f (B32.reveal input) in
    match p32 input with
    | Some (v, consumed) ->
      if g v
      then
        [@inline_let]
        let (v' : t { f v' == true } ) = v in
	Some (v', consumed)
      else
        None
    | _ -> None
  ) <: (res: option ((v': t { f v' == true } ) * U32.t) { parser32_correct (parse_filter p f) input res } ))

inline_for_extraction
let serialize32_filter
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (#s: serializer p)
  (s32: serializer32 s)
  (f: (t -> GTot bool))
: Tot (serializer32 #_ #_ #(parse_filter p f) (serialize_filter s f))
= fun (input: t { f input == true } ) -> s32 input

inline_for_extraction
let make_constant_size_parser32
  (sz: nat)
  (sz' : U32.t { U32.v sz' == sz } )
  (#t: Type)
  (f: ((s: bytes {Seq.length s == sz}) -> GTot (option t)))
  (u: unit {
    make_constant_size_parser_precond sz t f
  } )
  (f' : ((s: B32.lbytes sz) -> Tot (y: option t { y == f (B32.reveal s) } )))
: Tot (parser32 (make_constant_size_parser sz t f))
= fun (input: bytes32) -> ((
    if U32.lt (B32.len input) sz'
    then None
    else begin
      let s' = B32.slice input 0ul sz' in
      match f' s' with
      | None -> None
      | Some v -> Some (v, sz')
    end
  ) <: (res: option (t * U32.t) { parser32_correct (make_constant_size_parser sz t f) input res } ))

inline_for_extraction
let make_total_constant_size_parser32
  (sz: nat)
  (sz' : U32.t { U32.v sz' == sz } )
  (#t: Type)
  (f: ((s: bytes {Seq.length s == sz}) -> GTot (t)))
  (u: unit {
    make_total_constant_size_parser_precond sz t f
  })
  (f' : ((s: B32.lbytes sz) -> Tot (y: t { y == f (B32.reveal s) } )))
: Tot (parser32 (make_total_constant_size_parser sz t f))
= fun (input: bytes32) -> ((
    if U32.lt (B32.len input) sz'
    then None
    else
      let s' = B32.slice input 0ul sz' in
      Some (f' s', sz')
  ) <: (res: option (t * U32.t) { parser32_correct (make_total_constant_size_parser sz t f) input res } ))

inline_for_extraction
let parse32_compose_context
  (#pk: parser_kind)
  (#kt1 #kt2: Type)
  (f: (kt2 -> Tot kt1))
  (t: (kt1 -> Tot Type))
  (p: ((k: kt1) -> Tot (parser pk (t k))))
  (p32: ((k: kt1) -> Tot (parser32 (p k))))
  (k: kt2)
: Tot (parser32 (p (f k)))
= fun input -> p32 (f k) input

inline_for_extraction
let serialize32_compose_context
  (#pk: parser_kind)
  (#kt1 #kt2: Type)
  (f: (kt2 -> Tot kt1))
  (t: (kt1 -> Tot Type))
  (p: ((k: kt1) -> Tot (parser pk (t k))))
  (s: ((k: kt1) -> Tot (serializer (p k))))
  (s32: ((k: kt1) -> Tot (serializer32 (s k))))
  (k: kt2)
: Tot (serializer32 (s (f k)))
= fun input -> s32 (f k) input

inline_for_extraction
let parse32_weaken
  (k1: parser_kind)
  (#k2: parser_kind)
  (#t: Type)
  (#p2: parser k2 t)
  (p2' : parser32 p2 { k1 `is_weaker_than` k2 })
: Tot (parser32 (weaken k1 p2))
= fun x -> p2' x

inline_for_extraction
let serialize32_weaken
  (k1: parser_kind)
  (#k2: parser_kind)
  (#t: Type)
  (#p2: parser k2 t)
  (#s2: serializer p2)
  (s2' : serializer32 s2 { k1 `is_weaker_than` k2 })
: Tot (serializer32 (serialize_weaken k1 s2))
= fun x -> s2' x

inline_for_extraction
let lift_parser32
  (#k: parser_kind)
  (#t: Type)
  (f: unit -> GTot (parser k t))
  (f32: parser32 (f ()))
: Tot (parser32 (lift_parser f))
= fun x -> f32 x

inline_for_extraction
let lift_serializer32
  (#k: parser_kind)
  (#t: Type)
  (f: unit -> GTot (parser k t))
  (s: unit -> GTot (serializer (f ())))
  (s32: serializer32 (s ()))
: Tot (serializer32 (lift_serializer #k #t #f s))
= fun x -> s32 x

inline_for_extraction
let parse32_tagged_union
  (#kt: parser_kind)
  (#tag_t: Type)
  (#pt: parser kt tag_t)
  (pt32: parser32 pt)
  (#data_t: Type)
  (tag_of_data: (data_t -> GTot tag_t))
  (#k: parser_kind)
  (#p: (t: tag_t) -> Tot (parser k (refine_with_tag tag_of_data t)))
  (p32: (t: tag_t) -> Tot (parser32 (p t)))
: Tot (parser32 (parse_tagged_union pt tag_of_data p))
=
  fun input -> 
    parse_tagged_union_eq pt tag_of_data p (B32.reveal input);
    match pt32 input with
    | None -> None
    | Some (tg, consumed_tg) ->
      let input_tg = B32.slice input consumed_tg (B32.len input) in
      begin match p32 tg input_tg with
      | None -> None
      | Some (x, consumed_x) -> Some ((x <: data_t), consumed_tg `U32.add` consumed_x)
      end

inline_for_extraction
let serialize32_tagged_union
  (#kt: parser_kind)
  (#tag_t: Type)
  (#pt: parser kt tag_t)
  (#st: serializer pt)
  (st32: serializer32 st)
  (#data_t: Type)
  (tag_of_data: (data_t -> GTot tag_t))
  (tag_of_data' : ((x: data_t) -> Tot (y: tag_t { y == tag_of_data x })))
  (#k: parser_kind)
  (#p: (t: tag_t) -> Tot (parser k (refine_with_tag tag_of_data t)))
  (#s: (t: tag_t) -> Tot (serializer (p t)))
  (s32: (t: tag_t) -> Tot (serializer32 (s t)))
  (x: squash (
    kt.parser_kind_subkind == Some ParserStrong /\
    begin match kt.parser_kind_high, k.parser_kind_high with
    | Some max1, Some max2 -> max1 + max2 < 4294967296
    | _ -> False
    end
  ))
: Tot (serializer32 (serialize_tagged_union st tag_of_data s))
=
  fun x ->
    serialize_tagged_union_eq st tag_of_data s x;
    let tg = tag_of_data' x in
    st32 tg `B32.append` s32 tg x
