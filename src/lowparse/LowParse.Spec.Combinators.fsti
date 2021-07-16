module LowParse.Spec.Combinators
include LowParse.Spec.Base

module Seq = FStar.Seq
module U8 = FStar.UInt8
module U32 = FStar.UInt32

module T = FStar.Tactics

#reset-options "--using_facts_from '* -FStar.Tactis -FStar.Reflection'"

(** Constant-size parsers *)

let make_constant_size_parser_aux
  (sz: nat)
  (t: Type)
  (f: ((s: bytes {Seq.length s == sz}) -> GTot (option t)))
: Tot (bare_parser t)
= fun (s: bytes) ->
  if Seq.length s < sz
  then None
  else begin
    let s' : bytes = Seq.slice s 0 sz in
    match f s' with
    | None -> None
    | Some v ->
      let (sz: consumed_length s) = sz in
      Some (v, sz)
  end

let make_constant_size_parser_precond_precond
  (sz: nat)
  (t: Type)
  (f: ((s: bytes {Seq.length s == sz}) -> GTot (option t)))
  (s1: bytes { Seq.length s1 == sz } )
  (s2: bytes { Seq.length s2 == sz } )
: GTot Type0
= (Some? (f s1) \/ Some? (f s2)) /\ f s1 == f s2

let make_constant_size_parser_precond
  (sz: nat)
  (t: Type)
  (f: ((s: bytes {Seq.length s == sz}) -> GTot (option t)))
: GTot Type0
= forall (s1: bytes {Seq.length s1 == sz}) (s2: bytes {Seq.length s2 == sz}) . {:pattern (f s1); (f s2)}
    make_constant_size_parser_precond_precond sz t f s1 s2 ==> Seq.equal s1 s2

let make_constant_size_parser_precond'
  (sz: nat)
  (t: Type)
  (f: ((s: bytes {Seq.length s == sz}) -> GTot (option t)))
: GTot Type0
= forall (s1: bytes {Seq.length s1 == sz}) (s2: bytes {Seq.length s2 == sz}) . {:pattern (f s1); (f s2)}
    make_constant_size_parser_precond_precond sz t f s1 s2 ==> s1 == s2

let make_constant_size_parser_injective
  (sz: nat)
  (t: Type)
  (f: ((s: bytes {Seq.length s == sz}) -> GTot (option t)))
: Lemma
  (requires (
    make_constant_size_parser_precond sz t f
  ))
  (ensures (
    injective (make_constant_size_parser_aux sz t f)
  ))
= let p : bare_parser t = make_constant_size_parser_aux sz t f in
  let prf1
    (b1 b2: bytes)
  : Lemma
    (requires (injective_precond p b1 b2))
    (ensures (injective_postcond p b1 b2))
  = assert (Some? (parse p b1));
    assert (Some? (parse p b2));
    let (Some (v1, len1)) = parse p b1 in
    let (Some (v2, len2)) = parse p b2 in
    assert ((len1 <: nat) == (len2 <: nat));
    assert ((len1 <: nat) == sz);
    assert ((len2 <: nat) == sz);
    assert (make_constant_size_parser_precond_precond sz t f (Seq.slice b1 0 len1) (Seq.slice b2 0 len2));
    assert (make_constant_size_parser_precond' sz t f)
  in
  Classical.forall_intro_2 (fun (b1: bytes) -> Classical.move_requires (prf1 b1))

let constant_size_parser_kind
  (sz: nat)
: Tot parser_kind
= strong_parser_kind sz sz None

let make_constant_size_parser
  (sz: nat)
  (t: Type)
  (f: ((s: bytes {Seq.length s == sz}) -> GTot (option t)))
: Pure (
    parser
      (constant_size_parser_kind sz)
      t
  )
  (requires (
    make_constant_size_parser_precond sz t f
  ))
  (ensures (fun _ -> True))
= let p : bare_parser t = make_constant_size_parser_aux sz t f in
  make_constant_size_parser_injective sz t f;
  parser_kind_prop_equiv (constant_size_parser_kind sz) p;
  p

let make_total_constant_size_parser_precond
  (sz: nat)
  (t: Type)
  (f: ((s: bytes {Seq.length s == sz}) -> GTot t))
: GTot Type0
= forall (s1: bytes {Seq.length s1 == sz}) (s2: bytes {Seq.length s2 == sz}) . {:pattern (f s1); (f s2)}
  f s1 == f s2 ==> Seq.equal s1 s2

let make_total_constant_size_parser
  (sz: nat)
  (t: Type)
  (f: ((s: bytes {Seq.length s == sz}) -> GTot t))
: Pure (
    parser
      (total_constant_size_parser_kind sz)
      t
  )
  (requires (
    make_total_constant_size_parser_precond sz t f
  ))
  (ensures (fun _ -> True))
= let p : bare_parser t = make_constant_size_parser sz t (fun x -> Some (f x)) in
  parser_kind_prop_equiv (total_constant_size_parser_kind sz) p;
  p


(** Combinators *)

/// monadic return for the parser monad
unfold
let parse_ret' (#t:Type) (v:t) : Tot (bare_parser t) =
  fun (b: bytes) -> Some (v, (0 <: consumed_length b))

// unfold
inline_for_extraction
let parse_ret_kind : parser_kind =
  strong_parser_kind 0 0 (Some ParserKindMetadataTotal)

let parse_ret (#t:Type) (v:t) : Tot (parser parse_ret_kind t) =
  parser_kind_prop_equiv parse_ret_kind (parse_ret' v);
  parse_ret' v

let serialize_ret
  (#t: Type)
  (v: t)
  (v_unique: (v' : t) -> Lemma (v == v'))
: Tot (serializer (parse_ret v))
= mk_serializer
    (parse_ret v)
    (fun (x: t) -> Seq.empty)
    (fun x -> v_unique x)

let parse_empty : parser parse_ret_kind unit =
  parse_ret ()

let serialize_empty : serializer parse_empty = serialize_ret () (fun _ -> ())

#set-options "--z3rlimit 16"

let fail_parser_kind_precond
  (k: parser_kind)
: GTot Type0
= k.parser_kind_metadata <> Some ParserKindMetadataTotal /\
  (Some? k.parser_kind_high ==> k.parser_kind_low <= Some?.v k.parser_kind_high)

let fail_parser'
  (t: Type)
: Tot (bare_parser t)
= fun _ -> None

let fail_parser
  (k: parser_kind)
  (t: Type)
: Pure (parser k t)
  (requires (fail_parser_kind_precond k))
  (ensures (fun _ -> True))
= let p = fail_parser' t in
  parser_kind_prop_equiv k p;
  strengthen k p

let fail_serializer
  (k: parser_kind {fail_parser_kind_precond k} )
  (t: Type)
  (prf: (x: t) -> Lemma False)
: Tot (serializer (fail_parser k t))
= mk_serializer
    (fail_parser k t)
    (fun x -> prf x; false_elim ())
    (fun x -> prf x)

inline_for_extraction
let parse_false_kind = strong_parser_kind 0 0 (Some ParserKindMetadataFail)

let parse_false : parser parse_false_kind (squash False) = fail_parser _ _

let serialize_false : serializer parse_false = fun input -> false_elim ()

/// monadic bind for the parser monad

let and_then_bare (#t:Type) (#t':Type)
                (p:bare_parser t)
                (p': (t -> Tot (bare_parser t'))) :
                Tot (bare_parser t') =
    fun (b: bytes) ->
    match parse p b with
    | Some (v, l) ->
      begin
	let p'v = p' v in
	let s' : bytes = Seq.slice b l (Seq.length b) in
	match parse p'v s' with
	| Some (v', l') ->
	  let res : consumed_length b = l + l' in
	  Some (v', res)
	| None -> None
      end
    | None -> None

let and_then_cases_injective_precond
  (#t:Type)
  (#t':Type)
  (p': (t -> Tot (bare_parser t')))
  (x1 x2: t)
  (b1 b2: bytes)
: GTot Type0
= Some? (parse (p' x1) b1) /\
  Some? (parse (p' x2) b2) /\ (
    let (Some (v1, _)) = parse (p' x1) b1 in
    let (Some (v2, _)) = parse (p' x2) b2 in
    v1 == v2
  )

let and_then_cases_injective
  (#t:Type)
  (#t':Type)
  (p': (t -> Tot (bare_parser t')))
: GTot Type0
= forall (x1 x2: t) (b1 b2: bytes) . {:pattern (parse (p' x1) b1); (parse (p' x2) b2)}
  and_then_cases_injective_precond p' x1 x2 b1 b2 ==>
  x1 == x2

let and_then_cases_injective_intro
  (#t:Type)
  (#t':Type)
  (p': (t -> Tot (bare_parser t')))
  (lem: (
    (x1: t) -> 
    (x2: t) ->
    (b1: bytes) ->
    (b2: bytes) ->
    Lemma
    (requires (and_then_cases_injective_precond p' x1 x2 b1 b2))
    (ensures (x1 == x2))
  ))
: Lemma
  (and_then_cases_injective p')
= Classical.forall_intro_3 (fun x1 x2 b1 -> Classical.forall_intro (Classical.move_requires (lem x1 x2 b1)))

let and_then_injective
  (#t:Type)
  (#t':Type)
  (p: bare_parser t)
  (p': (t -> Tot (bare_parser t')))
: Lemma
  (requires (
    injective p /\
    (forall (x: t) . injective (p' x)) /\
    and_then_cases_injective p'
  ))
  (ensures (
    injective (and_then_bare p p')
  ))
= let ps = and_then_bare p p' in
  let f
    (b1 b2: bytes)
  : Lemma
    (requires (injective_precond ps b1 b2))
    (ensures (injective_postcond ps b1 b2))
  = let (Some (v1, len1)) = p b1 in
    let (Some (v2, len2)) = p b2 in
    let b1' : bytes = Seq.slice b1 len1 (Seq.length b1) in
    let b2' : bytes = Seq.slice b2 len2 (Seq.length b2) in
    assert (Some? ((p' v1) b1'));
    assert (Some? ((p' v2) b2'));
    assert (and_then_cases_injective_precond p' v1 v2 b1' b2');
    assert (v1 == v2);
    assert (injective_precond p b1 b2);
    assert ((len1 <: nat) == (len2 <: nat));
    assert (injective (p' v1));
    assert (injective_precond (p' v1) b1' b2');
    assert (injective_postcond (p' v1) b1' b2');
    let (Some (_, len1')) = (p' v1) b1' in
    let (Some (_, len2')) = (p' v2) b2' in
    assert ((len1' <: nat) == (len2' <: nat));
    Seq.lemma_split (Seq.slice b1 0 (len1 + len1')) len1;
    Seq.lemma_split (Seq.slice b2 0 (len2 + len2')) len1;
    assert (injective_postcond ps b1 b2)
  in
  Classical.forall_intro_2 (fun x -> Classical.move_requires (f x))

let and_then_no_lookahead_on
    (#t:Type)
    (#t':Type)
    (p: bare_parser t)
    (p': (t -> Tot (bare_parser t')))
    (x: bytes) 
    (x' : bytes)
  : Lemma
    (requires (
      no_lookahead p /\
      injective p /\
      (forall (x: t) . no_lookahead (p' x))
    ))
    (ensures (no_lookahead_on (and_then_bare p p') x x'))
=
    let f = and_then_bare p p' in
    match f x with
    | Some v -> 
      let (y, off) = v in
      let off : nat = off in
      let (off_x : consumed_length x ) = off in
      if off <= Seq.length x'
      then
	let (off_x' : consumed_length x') = off in
	let g () : Lemma
	  (requires (Seq.slice x' 0 off_x' == Seq.slice x 0 off_x))
	  (ensures (
	    Some? (f x') /\ (
	    let (Some v') = f x' in
	    let (y', off') = v' in
	    y == y'
	  )))
	= assert (Some? (p x));
	  let (Some (y1, off1)) = p x in
	  assert (off1 <= off);
	  assert (off1 <= Seq.length x');
	  assert (Seq.slice x' 0 off1 == Seq.slice (Seq.slice x' 0 off_x') 0 off1);
	  assert (Seq.slice x' 0 off1 == Seq.slice x 0 off1);
	  assert (no_lookahead_on p x x');
	  assert (Some? (p x'));
	  let (Some v1') = p x' in
	  let (y1', off1') = v1' in
	  assert (y1 == y1');
	  assert (injective_precond p x x');
	  assert ((off1 <: nat) == (off1' <: nat));
	  let x2 : bytes = Seq.slice x off1 (Seq.length x) in
	  let x2' : bytes = Seq.slice x' off1 (Seq.length x') in
	  let p2 = p' y1 in
	  assert (Some? (p2 x2));
	  let (Some (y2, off2)) = p2 x2 in
	  assert (off == off1 + off2);
	  assert (off2 <= Seq.length x2);
	  assert (off2 <= Seq.length x2');
	  assert (Seq.slice x2' 0 off2 == Seq.slice (Seq.slice x' 0 off_x') off1 (off1 + off2));
	  assert (Seq.slice x2' 0 off2 == Seq.slice x2 0 off2);
	  assert (no_lookahead_on p2 x2 x2');
	  assert (Some? (p2 x2'));
	  let (Some v2') = p2 x2' in
	  let (y2', _) = v2' in
	  assert (y2 == y2')
	in
	Classical.move_requires g ()
      else ()
    | _ -> ()

inline_for_extraction
let and_then_metadata
  (k1 k2: parser_kind_metadata_t)
: Tot parser_kind_metadata_t
= match k1, k2 with
  | Some ParserKindMetadataFail, _ -> k1
  | _, Some ParserKindMetadataFail -> k2
  | Some ParserKindMetadataTotal, Some ParserKindMetadataTotal -> k1
  | _ -> None

// unfold
inline_for_extraction
let and_then_kind
  (k1 k2: parser_kind)
: Tot parser_kind
= {
    parser_kind_low = k1.parser_kind_low + k2.parser_kind_low;
    parser_kind_high =
      begin
	if is_some k1.parser_kind_high `bool_and` is_some k2.parser_kind_high
	then Some (some_v k1.parser_kind_high + some_v k2.parser_kind_high)
	else None
      end;
    parser_kind_metadata = and_then_metadata k1.parser_kind_metadata k2.parser_kind_metadata;
    parser_kind_subkind =
      begin
        if k2.parser_kind_subkind = Some ParserConsumesAll
	then Some ParserConsumesAll
	else if (k1.parser_kind_subkind = Some ParserStrong) `bool_and` (k2.parser_kind_subkind = Some ParserStrong)
	then Some ParserStrong
	else if (k2.parser_kind_high = Some 0) `bool_and` (k2.parser_kind_subkind = Some ParserStrong)
	then k1.parser_kind_subkind
	else None
      end;
  }

let and_then_no_lookahead
  (#k: parser_kind)
  (#t:Type)
  (p:parser k t)
  (#k': parser_kind)
  (#t':Type)
  (p': (t -> Tot (parser k' t')))
: Lemma
  (requires (
    and_then_cases_injective p'
  ))
  (ensures ((k.parser_kind_subkind == Some ParserStrong /\ k'.parser_kind_subkind == Some ParserStrong) ==> no_lookahead (and_then_bare p p')))
= parser_kind_prop_equiv k p;
  Classical.forall_intro (fun (x: t) -> parser_kind_prop_equiv k' (p' x));
  if k.parser_kind_subkind = Some ParserStrong && k.parser_kind_subkind = Some ParserStrong then
    Classical.forall_intro_2 (fun x -> Classical.move_requires (and_then_no_lookahead_on p p' x))
  else ()

#set-options "--max_fuel 8 --max_ifuel 8 --z3rlimit 64"

let and_then_correct
  (#k: parser_kind)
  (#t:Type)
  (p:parser k t)
  (#k': parser_kind)
  (#t':Type)
  (p': (t -> Tot (parser k' t')))
: Lemma
  (requires (
    and_then_cases_injective p'
  ))
  (ensures (
    injective (and_then_bare p p') /\
    parser_kind_prop (and_then_kind k k') (and_then_bare p p')
  ))
= parser_kind_prop_equiv k p;
  Classical.forall_intro (fun x -> parser_kind_prop_equiv k' (p' x));
  parser_kind_prop_equiv (and_then_kind k k') (and_then_bare p p');
  and_then_injective p p';
  and_then_no_lookahead p p'

#reset-options "--using_facts_from '* -FStar.Tactis -FStar.Reflection'"

val and_then
  (#k: parser_kind)
  (#t:Type)
  (p:parser k t)
  (#k': parser_kind)
  (#t':Type)
  (p': (t -> Tot (parser k' t')))
: Pure (parser (and_then_kind k k') t')
  (requires (
    and_then_cases_injective p'
  ))
  (ensures (fun _ -> True))

val and_then_eq
  (#k: parser_kind)
  (#t:Type)
  (p:parser k t)
  (#k': parser_kind)
  (#t':Type)
  (p': (t -> Tot (parser k' t')))
  (input: bytes)
: Lemma
  (requires (and_then_cases_injective p'))
  (ensures (parse (and_then p p') input == and_then_bare p p' input))


/// monadic return for the parser monad
unfold
let parse_fret' (#t #t':Type) (f: t -> GTot t') (v:t) : Tot (bare_parser t') =
  fun (b: bytes) -> Some (f v, (0 <: consumed_length b))

unfold
let parse_fret (#t #t':Type) (f: t -> GTot t') (v:t) : Tot (parser parse_ret_kind t') =
  [@inline_let] let _ = parser_kind_prop_equiv parse_ret_kind (parse_fret' f v) in
  parse_fret' f v

let synth_injective
  (#t1: Type)
  (#t2: Type)
  (f: (t1 -> GTot t2))
: GTot Type0
= forall (x x' : t1) . {:pattern (f x); (f x')} f x == f x' ==> x == x'

let synth_injective_intro
  (#t1: Type)
  (#t2: Type)
  (f: (t1 -> GTot t2))
: Lemma
  (requires (forall (x x' : t1) . f x == f x' ==> x == x'))
  (ensures (synth_injective f))
= ()

let synth_injective_intro'
  (#t1: Type)
  (#t2: Type)
  (f: (t1 -> GTot t2))
  (prf: (
    (x: t1) ->
    (x' : t1) ->
    Lemma
    (requires (f x == f x'))
    (ensures (x == x'))
  ))
: Lemma
  (synth_injective f)
= Classical.forall_intro_2 (fun x -> Classical.move_requires (prf x))
  
let parse_synth'
  (#k: parser_kind)
  (#t1: Type)
  (#t2: Type)
  (p1: parser k t1)
  (f2: t1 -> GTot t2)
: Tot (bare_parser t2)
= fun b -> match parse p1 b with
  | None -> None
  | Some (x1, consumed) -> Some (f2 x1, consumed)

val parse_synth
  (#k: parser_kind)
  (#t1: Type)
  (#t2: Type)
  (p1: parser k t1)
  (f2: t1 -> GTot t2)
: Pure (parser k t2)
  (requires (
    synth_injective f2
  ))
  (ensures (fun _ -> True))

val parse_synth_eq
  (#k: parser_kind)
  (#t1: Type)
  (#t2: Type)
  (p1: parser k t1)
  (f2: t1 -> GTot t2)
  (b: bytes)
: Lemma
  (requires (synth_injective f2))
  (ensures (synth_injective f2 /\ parse (parse_synth p1 f2) b == parse_synth' p1 f2 b))

let bare_serialize_synth
  (#k: parser_kind)
  (#t1: Type)
  (#t2: Type)
  (p1: parser k t1)
  (f2: t1 -> GTot t2)
  (s1: serializer p1)
  (g1: t2 -> GTot t1)
: Tot (bare_serializer t2) =
  fun (x: t2) -> s1 (g1 x)

val bare_serialize_synth_correct
  (#k: parser_kind)
  (#t1: Type)
  (#t2: Type)
  (p1: parser k t1)
  (f2: t1 -> GTot t2)
  (s1: serializer p1)
  (g1: t2 -> GTot t1)
: Lemma
  (requires (
    (forall (x : t2) . f2 (g1 x) == x) /\
    (forall (x x' : t1) . f2 x == f2 x' ==> x == x')
  ))
  (ensures (serializer_correct (parse_synth p1 f2) (bare_serialize_synth p1 f2 s1 g1 )))

let synth_inverse
  (#t1: Type)
  (#t2: Type)
  (f2: (t1 -> GTot t2))
  (g1: (t2 -> GTot t1))
: GTot Type0
= (forall (x : t2) . {:pattern (f2 (g1 x))} f2 (g1 x) == x)

let synth_inverse_intro
  (#t1: Type)
  (#t2: Type)
  (f2: (t1 -> GTot t2))
  (g1: (t2 -> GTot t1))
: Lemma
  (requires (forall (x : t2) . f2 (g1 x) == x))
  (ensures (synth_inverse f2 g1))
= ()

let synth_inverse_intro'
  (#t1: Type)
  (#t2: Type)
  (f2: (t1 -> GTot t2))
  (g1: (t2 -> GTot t1))
  (prf: (x: t2) -> Lemma (f2 (g1 x) == x))
: Lemma
  (ensures (synth_inverse f2 g1))
= Classical.forall_intro prf

let synth_inverse_synth_injective_pat
  (#t1: Type)
  (#t2: Type)
  (f: (t1 -> GTot t2))
  (g: (t2 -> GTot t1))
: Lemma
  (requires (synth_inverse g f))
  (ensures (synth_injective f))
  [SMTPat (synth_inverse g f)]
= assert (forall x1 x2. f x1 == f x2 ==> g (f x1) == g (f x2))

let synth_inverse_synth_injective
  (#t1: Type)
  (#t2: Type)
  (f: (t1 -> GTot t2))
  (g: (t2 -> GTot t1))
: Lemma
  (requires (synth_inverse g f))
  (ensures (synth_injective f))
= ()

let synth_inverse_synth_injective'
  (#t1: Type)
  (#t2: Type)
  (g: (t2 -> GTot t1))
  (f: (t1 -> GTot t2))
  (u: squash (synth_inverse g f))
: Tot (squash (synth_injective f))
= ()

let synth_injective_synth_inverse_synth_inverse_recip
  (#t1: Type)
  (#t2: Type)
  (g: (t2 -> GTot t1))
  (f: (t1 -> GTot t2))
  (u: squash (synth_inverse g f /\ synth_injective g))
: Tot (squash (synth_inverse f g))
= assert (forall x . g (f (g x)) == g x)

val serialize_synth
  (#k: parser_kind)
  (#t1: Type)
  (#t2: Type)
  (p1: parser k t1)
  (f2: t1 -> GTot t2)
  (s1: serializer p1)
  (g1: t2 -> GTot t1)
  (u: unit {
    synth_inverse f2 g1 /\
    synth_injective f2
  })
: Tot (serializer (parse_synth p1 f2))

val serialize_synth_eq
  (#k: parser_kind)
  (#t1: Type)
  (#t2: Type)
  (p1: parser k t1)
  (f2: t1 -> GTot t2)
  (s1: serializer p1)
  (g1: t2 -> GTot t1)
  (u: unit {
    synth_inverse f2 g1 /\
    synth_injective f2
  })
  (x: t2)
: Lemma
  (serialize (serialize_synth p1 f2 s1 g1 u) x == serialize s1 (g1 x))

let serialize_synth_eq'
  (#k: parser_kind)
  (#t1: Type)
  (#t2: Type)
  (p1: parser k t1)
  (f2: t1 -> GTot t2)
  (s1: serializer p1)
  (g1: t2 -> GTot t1)
  (u: unit {
    synth_inverse f2 g1 /\
    synth_injective f2
  })
  (x: t2)
  (y1: bytes)
  (q1: squash (y1 == serialize (serialize_synth p1 f2 s1 g1 u) x))
  (y2: bytes)
  (q2: squash (y2 == serialize s1 (g1 x)))
: Lemma
  (ensures (y1 == y2))
= serialize_synth_eq p1 f2 s1 g1 u x

val serialize_synth_upd_chain
  (#k: parser_kind)
  (#t1: Type)
  (#t2: Type)
  (p1: parser k t1)
  (f2: t1 -> GTot t2)
  (s1: serializer p1)
  (g1: t2 -> GTot t1)
  (u: unit {
    synth_inverse f2 g1 /\
    synth_injective f2
  })
  (x1: t1)
  (x2: t2)
  (y1: t1)
  (y2: t2)
  (i': nat)
  (s' : bytes)
: Lemma
  (requires (
    let s = serialize s1 x1 in
    i' + Seq.length s' <= Seq.length s /\
    serialize s1 y1 == seq_upd_seq s i' s' /\
    x2 == f2 x1 /\
    y2 == f2 y1
  ))
  (ensures (
    let s = serialize (serialize_synth p1 f2 s1 g1 u) x2 in
    i' + Seq.length s' <= Seq.length s /\
    Seq.length s == Seq.length (serialize s1 x1) /\
    serialize (serialize_synth p1 f2 s1 g1 u) y2 == seq_upd_seq s i' s'
  ))

val serialize_synth_upd_bw_chain
  (#k: parser_kind)
  (#t1: Type)
  (#t2: Type)
  (p1: parser k t1)
  (f2: t1 -> GTot t2)
  (s1: serializer p1)
  (g1: t2 -> GTot t1)
  (u: unit {
    synth_inverse f2 g1 /\
    synth_injective f2
  })
  (x1: t1)
  (x2: t2)
  (y1: t1)
  (y2: t2)
  (i': nat)
  (s' : bytes)
: Lemma
  (requires (
    let s = serialize s1 x1 in
    i' + Seq.length s' <= Seq.length s /\
    serialize s1 y1 == seq_upd_bw_seq s i' s' /\
    x2 == f2 x1 /\
    y2 == f2 y1
  ))
  (ensures (
    let s = serialize (serialize_synth p1 f2 s1 g1 u) x2 in
    i' + Seq.length s' <= Seq.length s /\
    Seq.length s == Seq.length (serialize s1 x1) /\
    serialize (serialize_synth p1 f2 s1 g1 u) y2 == seq_upd_bw_seq s i' s'
  ))

(* Strengthened versions of and_then *)

inline_for_extraction
let synth_tagged_union_data
  (#tag_t: Type)
  (#data_t: Type)
  (tag_of_data: (data_t -> GTot tag_t))
  (tg: tag_t)
  (x: refine_with_tag tag_of_data tg)
: Tot data_t
= x

let parse_tagged_union_payload
  (#tag_t: Type)
  (#data_t: Type)
  (tag_of_data: (data_t -> GTot tag_t))
  (#k: parser_kind)
  (p: (t: tag_t) -> Tot (parser k (refine_with_tag tag_of_data t)))
  (tg: tag_t)
: Tot (parser k data_t)
= parse_synth #k #(refine_with_tag tag_of_data tg) (p tg) (synth_tagged_union_data tag_of_data tg)

let parse_tagged_union_payload_and_then_cases_injective
  (#tag_t: Type)
  (#data_t: Type)
  (tag_of_data: (data_t -> GTot tag_t))
  (#k: parser_kind)
  (p: (t: tag_t) -> Tot (parser k (refine_with_tag tag_of_data t)))
: Lemma
  (and_then_cases_injective (parse_tagged_union_payload tag_of_data p))
= and_then_cases_injective_intro (parse_tagged_union_payload tag_of_data p) (fun x1 x2 b1 b2 ->
    parse_synth_eq #k #(refine_with_tag tag_of_data x1) (p x1) (synth_tagged_union_data tag_of_data x1) b1;
    parse_synth_eq #k #(refine_with_tag tag_of_data x2) (p x2) (synth_tagged_union_data tag_of_data x2) b2
  )

val parse_tagged_union
  (#kt: parser_kind)
  (#tag_t: Type)
  (pt: parser kt tag_t)
  (#data_t: Type)
  (tag_of_data: (data_t -> GTot tag_t))
  (#k: parser_kind)
  (p: (t: tag_t) -> Tot (parser k (refine_with_tag tag_of_data t)))
: Tot (parser (and_then_kind kt k) data_t)

val parse_tagged_union_eq
  (#kt: parser_kind)
  (#tag_t: Type)
  (pt: parser kt tag_t)
  (#data_t: Type)
  (tag_of_data: (data_t -> GTot tag_t))
  (#k: parser_kind)
  (p: (t: tag_t) -> Tot (parser k (refine_with_tag tag_of_data t)))
  (input: bytes)
: Lemma
  (parse (parse_tagged_union pt tag_of_data p) input == (match parse pt input with
  | None -> None
  | Some (tg, consumed_tg) ->
    let input_tg = Seq.slice input consumed_tg (Seq.length input) in
    begin match parse (p tg) input_tg with
    | Some (x, consumed_x) -> Some ((x <: data_t), consumed_tg + consumed_x)
    | None -> None
    end
  ))

let bare_parse_tagged_union
  (#kt: parser_kind)
  (#tag_t: Type)
  (pt: parser kt tag_t)
  (#data_t: Type)
  (tag_of_data: (data_t -> GTot tag_t))
  (k': (t: tag_t) -> Tot parser_kind)
  (p: (t: tag_t) -> Tot (parser (k' t) (refine_with_tag tag_of_data t)))
  (input: bytes)
: GTot (option (data_t * consumed_length input))
= match parse pt input with
  | None -> None
  | Some (tg, consumed_tg) ->
    let input_tg = Seq.slice input consumed_tg (Seq.length input) in
    begin match parse (p tg) input_tg with
    | Some (x, consumed_x) -> Some ((x <: data_t), consumed_tg + consumed_x)
    | None -> None
    end

val parse_tagged_union_eq_gen
  (#kt: parser_kind)
  (#tag_t: Type)
  (pt: parser kt tag_t)
  (#data_t: Type)
  (tag_of_data: (data_t -> GTot tag_t))
  (#k: parser_kind)
  (p: (t: tag_t) -> Tot (parser k (refine_with_tag tag_of_data t)))
  (#kt': parser_kind)
  (pt': parser kt' tag_t)
  (lem_pt: (
    (input: bytes) -> 
    Lemma
    (parse pt input == parse pt' input)
  ))
  (k': (t: tag_t) -> Tot parser_kind)
  (p': (t: tag_t) -> Tot (parser (k' t) (refine_with_tag tag_of_data t)))
  (lem_p' : (
    (k: tag_t) ->
    (input: bytes) ->
    Lemma
    (parse (p k) input == parse (p' k) input)
  ))
  (input: bytes)
: Lemma
  (parse (parse_tagged_union pt tag_of_data p) input == bare_parse_tagged_union pt' tag_of_data k' p' input)

let bare_serialize_tagged_union
  (#kt: parser_kind)
  (#tag_t: Type)
  (#pt: parser kt tag_t)
  (st: serializer pt)
  (#data_t: Type)
  (tag_of_data: (data_t -> GTot tag_t))
  (#k: parser_kind)
  (#p: (t: tag_t) -> Tot (parser k (refine_with_tag tag_of_data t)))
  (s: (t: tag_t) -> Tot (serializer (p t)))
: Tot (bare_serializer data_t)
= fun (d: data_t) ->
  let tg = tag_of_data d in
  Seq.append (st tg) (serialize (s tg) d)

let seq_slice_append_l
  (#t: Type)
  (s1 s2: Seq.seq t)
: Lemma
  (Seq.slice (Seq.append s1 s2) 0 (Seq.length s1) == s1)
= assert (Seq.equal (Seq.slice (Seq.append s1 s2) 0 (Seq.length s1)) s1)

let seq_slice_append_r
  (#t: Type)
  (s1 s2: Seq.seq t)
: Lemma
  (Seq.slice (Seq.append s1 s2) (Seq.length s1) (Seq.length (Seq.append s1 s2)) == s2)
= assert (Seq.equal (Seq.slice (Seq.append s1 s2) (Seq.length s1) (Seq.length (Seq.append s1 s2))) s2)

let bare_serialize_tagged_union_correct
  (#kt: parser_kind)
  (#tag_t: Type)
  (#pt: parser kt tag_t)
  (st: serializer pt)
  (#data_t: Type)
  (tag_of_data: (data_t -> GTot tag_t))
  (#k: parser_kind)
  (#p: (t: tag_t) -> Tot (parser k (refine_with_tag tag_of_data t)))
  (s: (t: tag_t) -> Tot (serializer (p t)))
: Lemma
  (requires (kt.parser_kind_subkind == Some ParserStrong))
  (ensures (serializer_correct (parse_tagged_union pt tag_of_data p) (bare_serialize_tagged_union st tag_of_data s)))
= (* same proof as nondep_then *)
  let prf
    (x: data_t)
  : Lemma (parse (parse_tagged_union pt tag_of_data p) (bare_serialize_tagged_union st tag_of_data s x) == Some (x, Seq.length (bare_serialize_tagged_union  st tag_of_data s x)))
  = parse_tagged_union_eq pt tag_of_data p (bare_serialize_tagged_union st tag_of_data s x);
    let t = tag_of_data x in
    let (u: refine_with_tag tag_of_data t) = x in
    let v1' = parse pt (bare_serialize_tagged_union st tag_of_data s x) in
    let v1 = parse pt (serialize st t) in
    assert (Some? v1);
    parser_kind_prop_equiv kt pt;
    assert (no_lookahead_on pt (serialize st t) (bare_serialize_tagged_union st tag_of_data s x));
    let (Some (_, len')) = parse pt (serialize st t) in
    assert (len' == Seq.length (serialize st t));
    assert (len' <= Seq.length (bare_serialize_tagged_union st tag_of_data s x));
    assert (Seq.slice (serialize st t) 0 len' == st t);
    seq_slice_append_l (serialize st t) (serialize (s t) u);
    assert (no_lookahead_on_precond pt (serialize st t) (bare_serialize_tagged_union st tag_of_data s x));
    assert (no_lookahead_on_postcond pt (serialize st t) (bare_serialize_tagged_union st tag_of_data s x));
    assert (Some? v1');
    assert (injective_precond pt (serialize st t) (bare_serialize_tagged_union st tag_of_data s x));
    assert (injective_postcond pt (serialize st t) (bare_serialize_tagged_union st tag_of_data s x));
    let (Some (x1, len1)) = v1 in
    let (Some (x1', len1')) = v1' in
    assert (x1 == x1');
    assert ((len1 <: nat) == (len1' <: nat));
    assert (x1 == t);
    assert (len1 == Seq.length (serialize st t));
    assert (bare_serialize_tagged_union st tag_of_data s x == Seq.append (serialize st t) (serialize (s t) u));
    seq_slice_append_r (serialize st t) (serialize (s t) u);
    ()
  in
  Classical.forall_intro prf

val serialize_tagged_union
  (#kt: parser_kind)
  (#tag_t: Type)
  (#pt: parser kt tag_t)
  (st: serializer pt)
  (#data_t: Type)
  (tag_of_data: (data_t -> GTot tag_t))
  (#k: parser_kind)
  (#p: (t: tag_t) -> Tot (parser k (refine_with_tag tag_of_data t)))
  (s: (t: tag_t) -> Tot (serializer (p t)))
: Pure (serializer (parse_tagged_union pt tag_of_data p))
  (requires (kt.parser_kind_subkind == Some ParserStrong))
  (ensures (fun _ -> True))

val serialize_tagged_union_eq
  (#kt: parser_kind)
  (#tag_t: Type)
  (#pt: parser kt tag_t)
  (st: serializer pt)
  (#data_t: Type)
  (tag_of_data: (data_t -> GTot tag_t))
  (#k: parser_kind)
  (#p: (t: tag_t) -> Tot (parser k (refine_with_tag tag_of_data t)))
  (s: (t: tag_t) -> Tot (serializer (p t)))
  (input: data_t)
: Lemma
  (requires (kt.parser_kind_subkind == Some ParserStrong))
  (ensures (serialize (serialize_tagged_union st tag_of_data s) input == bare_serialize_tagged_union st tag_of_data s input))
  [SMTPat (serialize (serialize_tagged_union st tag_of_data s) input)]

(* Dependent pairs *)

inline_for_extraction
let synth_dtuple2
  (#t1: Type)
  (#t2: t1 -> Type)
  (x: t1)
  (y: t2 x)
: Tot (refine_with_tag #t1 #(dtuple2 t1 t2) dfst x)
= (| x, y |)

let parse_dtuple2
  (#k1: parser_kind)
  (#t1: Type)
  (p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: (t1 -> Tot Type))
  (p2: (x: t1) -> parser k2 (t2 x))
: Tot (parser (and_then_kind k1 k2) (dtuple2 t1 t2))
= parse_tagged_union
    p1
    dfst
    (fun (x: t1) -> parse_synth (p2 x) (synth_dtuple2 x))

inline_for_extraction
let synth_dtuple2_recip
  (#t1: Type)
  (#t2: t1 -> Type)
  (x: t1)
  (y: refine_with_tag #t1 #(dtuple2 t1 t2) dfst x)
: Tot (t2 x)
= dsnd y

val serialize_dtuple2
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (s1: serializer p1 { k1.parser_kind_subkind == Some ParserStrong })
  (#k2: parser_kind)
  (#t2: (t1 -> Tot Type))
  (#p2: (x: t1) -> parser k2 (t2 x))
  (s2: (x: t1) -> serializer (p2 x))
: Tot (serializer (parse_dtuple2 p1 p2))

val parse_dtuple2_eq
  (#k1: parser_kind)
  (#t1: Type)
  (p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: (t1 -> Tot Type))
  (p2: (x: t1) -> parser k2 (t2 x))
  (b: bytes)
: Lemma
  (parse (parse_dtuple2 p1 p2) b == (match parse p1 b with
  | Some (x1, consumed1) ->
    let b' = Seq.slice b consumed1 (Seq.length b) in
    begin match parse (p2 x1) b' with
    | Some (x2, consumed2) ->
      Some ((| x1, x2 |), consumed1 + consumed2)
    | _ -> None
    end
  | _ -> None
  ))

let bare_parse_dtuple2
  (#k1: parser_kind)
  (#t1: Type)
  (p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: (t1 -> Tot Type))
  (p2: (x: t1) -> parser k2 (t2 x))
: Tot (bare_parser (dtuple2 t1 t2))
= fun b ->
  match parse p1 b with
  | Some (x1, consumed1) ->
    let b' = Seq.slice b consumed1 (Seq.length b) in
    begin match parse (p2 x1) b' with
    | Some (x2, consumed2) ->
      Some ((| x1, x2 |), consumed1 + consumed2)
    | _ -> None
    end
  | _ -> None
  
let parse_dtuple2_eq'
  (#k1: parser_kind)
  (#t1: Type)
  (p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: (t1 -> Tot Type))
  (p2: (x: t1) -> parser k2 (t2 x))
  (b: bytes)
: Lemma
  (parse (parse_dtuple2 #k1 #t1 p1 #k2 #t2 p2) b == bare_parse_dtuple2 #k1 #t1 p1 #k2 #t2 p2 b)
= parse_dtuple2_eq p1 p2 b

val serialize_dtuple2_eq
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (s1: serializer p1 { k1.parser_kind_subkind == Some ParserStrong })
  (#k2: parser_kind)
  (#t2: (t1 -> Tot Type))
  (#p2: (x: t1) -> parser k2 (t2 x))
  (s2: (x: t1) -> serializer (p2 x))
  (xy: dtuple2 t1 t2)
: Lemma
  (serialize (serialize_dtuple2 s1 s2) xy == serialize s1 (dfst xy) `Seq.append` serialize (s2 (dfst xy)) (dsnd xy))

let bare_serialize_dtuple2
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (s1: serializer p1 { k1.parser_kind_subkind == Some ParserStrong })
  (#k2: parser_kind)
  (#t2: (t1 -> Tot Type))
  (#p2: (x: t1) -> parser k2 (t2 x))
  (s2: (x: t1) -> serializer (p2 x))
  (xy: dtuple2 t1 t2)
: GTot bytes
= serialize s1 (dfst xy) `Seq.append` serialize (s2 (dfst xy)) (dsnd xy)

let serialize_dtuple2_eq'
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (s1: serializer p1 { k1.parser_kind_subkind == Some ParserStrong })
  (#k2: parser_kind)
  (#t2: (t1 -> Tot Type))
  (#p2: (x: t1) -> parser k2 (t2 x))
  (s2: (x: t1) -> serializer (p2 x))
  (xy: dtuple2 t1 t2)
: Tot (squash (
  (serialize #_ #(dtuple2 t1 t2)  (serialize_dtuple2 #k1 #t1 #p1 s1 #k2 #t2 #p2 s2) xy == bare_serialize_dtuple2 #k1 #t1 #p1 s1 #k2 #t2 #p2 s2 xy)))
= serialize_dtuple2_eq s1 s2 xy


(* Special case for non-dependent parsing *)

val nondep_then
  (#k1: parser_kind)
  (#t1: Type)
  (p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: Type)
  (p2: parser k2 t2)
: Tot (parser (and_then_kind k1 k2) (t1 * t2))

#set-options "--z3rlimit 16"

val nondep_then_eq
  (#k1: parser_kind)
  (#t1: Type)
  (p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: Type)
  (p2: parser k2 t2)
  (b: bytes)
: Lemma
  (parse (nondep_then p1 p2) b == (match parse p1 b with
  | Some (x1, consumed1) ->
    let b' = Seq.slice b consumed1 (Seq.length b) in
    begin match parse p2 b' with
    | Some (x2, consumed2) ->
      Some ((x1, x2), consumed1 + consumed2)
    | _ -> None
    end
  | _ -> None
  ))

let bare_serialize_nondep_then
  (#k1: parser_kind)
  (#t1: Type)
  (p1: parser k1 t1)
  (s1: serializer p1)
  (#k2: parser_kind)
  (#t2: Type)
  (p2: parser k2 t2)
  (s2: serializer p2)
: Tot (bare_serializer (t1 * t2))
= fun (x: t1 * t2) ->
  let (x1, x2) = x in
  Seq.append (s1 x1) (s2 x2)

val serialize_nondep_then
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (s1: serializer p1 { k1.parser_kind_subkind == Some ParserStrong } )
  (#k2: parser_kind)
  (#t2: Type)
  (#p2: parser k2 t2)
  (s2: serializer p2)
: Tot (serializer (nondep_then p1 p2))

val serialize_nondep_then_eq
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (s1: serializer p1 { k1.parser_kind_subkind == Some ParserStrong } )
  (#k2: parser_kind)
  (#t2: Type)
  (#p2: parser k2 t2)
  (s2: serializer p2)
  (input: t1 * t2)
: Lemma
  (serialize (serialize_nondep_then s1 s2) input == bare_serialize_nondep_then p1 s1 p2 s2 input)

val length_serialize_nondep_then
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (s1: serializer p1 { k1.parser_kind_subkind == Some ParserStrong } )
  (#k2: parser_kind)
  (#t2: Type)
  (#p2: parser k2 t2)
  (s2: serializer p2)
  (input1: t1)
  (input2: t2)
: Lemma
  (Seq.length (serialize (serialize_nondep_then s1 s2) (input1, input2)) == Seq.length (serialize s1 input1) + Seq.length (serialize s2 input2))

val serialize_nondep_then_upd_left
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (s1: serializer p1 { k1.parser_kind_subkind == Some ParserStrong } )
  (#k2: parser_kind)
  (#t2: Type)
  (#p2: parser k2 t2)
  (s2: serializer p2)
  (x: t1 * t2)
  (y: t1)
: Lemma
  (requires (Seq.length (serialize s1 y) == Seq.length (serialize s1 (fst x))))
  (ensures (
    let s = serialize (serialize_nondep_then s1 s2) x in
    Seq.length (serialize s1 y) <= Seq.length s /\
    serialize (serialize_nondep_then s1 s2) (y, snd x) == seq_upd_seq s 0 (serialize s1 y)
  ))

val serialize_nondep_then_upd_left_chain
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (s1: serializer p1 { k1.parser_kind_subkind == Some ParserStrong } )
  (#k2: parser_kind)
  (#t2: Type)
  (#p2: parser k2 t2)
  (s2: serializer p2)
  (x: t1 * t2)
  (y: t1)
  (i' : nat)
  (s' : bytes)
: Lemma
  (requires (
    let s1' = serialize s1 (fst x) in
    i' + Seq.length s' <= Seq.length s1' /\
    serialize s1 y == seq_upd_seq s1' i' s'
  ))
  (ensures (
    let s = serialize (serialize_nondep_then s1 s2) x in
    i' + Seq.length s' <= Seq.length s /\
    serialize (serialize_nondep_then s1 s2) (y, snd x) == seq_upd_seq s i' s'
  ))

val serialize_nondep_then_upd_bw_left
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (s1: serializer p1 { k1.parser_kind_subkind == Some ParserStrong } )
  (#k2: parser_kind)
  (#t2: Type)
  (#p2: parser k2 t2)
  (s2: serializer p2)
  (x: t1 * t2)
  (y: t1)
: Lemma
  (requires (Seq.length (serialize s1 y) == Seq.length (serialize s1 (fst x))))
  (ensures (
    let s = serialize (serialize_nondep_then s1 s2) x in
    let len2 = Seq.length (serialize s2 (snd x)) in
    len2 + Seq.length (serialize s1 y) <= Seq.length s /\
    serialize (serialize_nondep_then s1 s2) (y, snd x) == seq_upd_bw_seq s len2 (serialize s1 y)
  ))

#reset-options "--z3refresh --z3rlimit 64 --z3cliopt smt.arith.nl=false --using_facts_from '* -FStar.Tactis -FStar.Reflection'"

val serialize_nondep_then_upd_bw_left_chain
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (s1: serializer p1 { k1.parser_kind_subkind == Some ParserStrong } )
  (#k2: parser_kind)
  (#t2: Type)
  (#p2: parser k2 t2)
  (s2: serializer p2)
  (x: t1 * t2)
  (y: t1)
  (i' : nat)
  (s' : bytes)
: Lemma
  (requires (
    let s1' = serialize s1 (fst x) in
    i' + Seq.length s' <= Seq.length s1' /\
    serialize s1 y == seq_upd_bw_seq s1' i' s'
  ))
  (ensures (
    let s = serialize (serialize_nondep_then s1 s2) x in
    let len2 = Seq.length (serialize s2 (snd x)) in
    len2 + i' + Seq.length s' <= Seq.length s /\
    serialize (serialize_nondep_then s1 s2) (y, snd x) == seq_upd_bw_seq s (len2 + i') s'
  ))

val serialize_nondep_then_upd_right
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (s1: serializer p1 { k1.parser_kind_subkind == Some ParserStrong } )
  (#k2: parser_kind)
  (#t2: Type)
  (#p2: parser k2 t2)
  (s2: serializer p2)
  (x: t1 * t2)
  (y: t2)
: Lemma
  (requires (Seq.length (serialize s2 y) == Seq.length (serialize s2 (snd x))))
  (ensures (
    let s = serialize (serialize_nondep_then s1 s2) x in
    Seq.length (serialize s2 y) <= Seq.length s /\
    serialize (serialize_nondep_then s1 s2) (fst x, y) == seq_upd_seq s (Seq.length s - Seq.length (serialize s2 y)) (serialize s2 y)
  ))

val serialize_nondep_then_upd_right_chain
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (s1: serializer p1 { k1.parser_kind_subkind == Some ParserStrong } )
  (#k2: parser_kind)
  (#t2: Type)
  (#p2: parser k2 t2)
  (s2: serializer p2)
  (x: t1 * t2)
  (y: t2)
  (i' : nat)
  (s' : bytes)
: Lemma
  (requires (
    let s2' = serialize s2 (snd x) in
    i' + Seq.length s' <= Seq.length s2' /\
    serialize s2 y == seq_upd_seq s2' i' s'
  ))
  (ensures (
    let s = serialize (serialize_nondep_then s1 s2) x in
    let l1 = Seq.length (serialize s1 (fst x)) in
    Seq.length s == l1 + Seq.length (serialize s2 (snd x)) /\
    l1 + i' + Seq.length s' <= Seq.length s /\
    serialize (serialize_nondep_then s1 s2) (fst x, y) == seq_upd_seq s (l1 + i') s'
  ))

let serialize_nondep_then_upd_bw_right
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (s1: serializer p1 { k1.parser_kind_subkind == Some ParserStrong } )
  (#k2: parser_kind)
  (#t2: Type)
  (#p2: parser k2 t2)
  (s2: serializer p2)
  (x: t1 * t2)
  (y: t2)
: Lemma
  (requires (Seq.length (serialize s2 y) == Seq.length (serialize s2 (snd x))))
  (ensures (
    let s = serialize (serialize_nondep_then s1 s2) x in
    Seq.length (serialize s2 y) <= Seq.length s /\
    serialize (serialize_nondep_then s1 s2) (fst x, y) == seq_upd_bw_seq s 0 (serialize s2 y)
  ))
= serialize_nondep_then_upd_right s1 s2 x y

let serialize_nondep_then_upd_bw_right_chain
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (s1: serializer p1 { k1.parser_kind_subkind == Some ParserStrong } )
  (#k2: parser_kind)
  (#t2: Type)
  (#p2: parser k2 t2)
  (s2: serializer p2)
  (x: t1 * t2)
  (y: t2)
  (i' : nat)
  (s' : bytes)
: Lemma
  (requires (
    let s2' = serialize s2 (snd x) in
    i' + Seq.length s' <= Seq.length s2' /\
    serialize s2 y == seq_upd_bw_seq s2' i' s'
  ))
  (ensures (
    let s = serialize (serialize_nondep_then s1 s2) x in
    let l1 = Seq.length (serialize s1 (fst x)) in
    Seq.length s == l1 + Seq.length (serialize s2 (snd x)) /\
    i' + Seq.length s' <= Seq.length s /\
    serialize (serialize_nondep_then s1 s2) (fst x, y) == seq_upd_bw_seq s i' s'
  ))
= let s2' = serialize s2 (snd x) in
  let j' = Seq.length s2' - i' - Seq.length s' in
  assert (j' + Seq.length s' <= Seq.length s2');
  assert (serialize s2 y == seq_upd_seq s2' j' s');
  let s = serialize (serialize_nondep_then s1 s2) x in
  serialize_nondep_then_upd_right_chain s1 s2 x y j' s';
  assert (Seq.length (serialize s1 (fst x)) + j' == Seq.length s - i' - Seq.length s');
  ()

#reset-options "--z3rlimit 32 --using_facts_from '* -FStar.Tactis -FStar.Reflection'"

(** Apply a total transformation on parsed data *)

let parse_strengthen_prf
  (#k: parser_kind)
  (#t1: Type)
  (p1: parser k t1)
  (p2: t1 -> GTot Type0)
: Tot Type
= (xbytes: bytes) ->
  (consumed: consumed_length xbytes) ->
  (x: t1) ->
  Lemma
  (requires (parse p1 xbytes == Some (x, consumed)))
  (ensures (p2 x))

let bare_parse_strengthen
  (#k: parser_kind)
  (#t1: Type)
  (p1: parser k t1)
  (p2: t1 -> GTot Type0)
  (prf: parse_strengthen_prf p1 p2)
: Tot (bare_parser (x: t1 { p2 x } ))
= fun (xbytes: bytes) ->
  match parse p1 xbytes with
  | Some (x, consumed) ->
    prf xbytes consumed x;
    let (x' : t1 { p2 x' } ) = x in
    Some (x', consumed)
  | _ -> None

let bare_parse_strengthen_no_lookahead
  (#k: parser_kind)
  (#t1: Type)
  (p1: parser k t1)
  (p2: t1 -> GTot Type0)
  (prf: parse_strengthen_prf p1 p2)
: Lemma
  (no_lookahead p1 ==> no_lookahead (bare_parse_strengthen p1 p2 prf))
= let p' : bare_parser (x: t1 { p2 x } ) = bare_parse_strengthen p1 p2 prf in
  assert (forall (b1 b2: bytes) . no_lookahead_on p1 b1 b2 ==> no_lookahead_on p' b1 b2)

let bare_parse_strengthen_injective
  (#k: parser_kind)
  (#t1: Type)
  (p1: parser k t1)
  (p2: t1 -> GTot Type0)
  (prf: parse_strengthen_prf p1 p2)
: Lemma
  (injective (bare_parse_strengthen p1 p2 prf))
= parser_kind_prop_equiv k p1;
  let p' : bare_parser (x: t1 { p2 x } ) = bare_parse_strengthen p1 p2 prf in
  assert (forall (b1 b2: bytes) . injective_precond p' b1 b2 ==> injective_precond p1 b1 b2);
  assert (forall (b1 b2: bytes) . injective_postcond p1 b1 b2 ==> injective_postcond p' b1 b2)

let bare_parse_strengthen_correct
  (#k: parser_kind)
  (#t1: Type)
  (p1: parser k t1)
  (p2: t1 -> GTot Type0)
  (prf: parse_strengthen_prf p1 p2)
: Lemma
  (injective (bare_parse_strengthen p1 p2 prf) /\
  parser_kind_prop k (bare_parse_strengthen p1 p2 prf))
= parser_kind_prop_equiv k p1;
  bare_parse_strengthen_no_lookahead p1 p2 prf;
  bare_parse_strengthen_injective p1 p2 prf;
  parser_kind_prop_equiv k (bare_parse_strengthen p1 p2 prf);
  ()

let parse_strengthen
  (#k: parser_kind)
  (#t1: Type)
  (p1: parser k t1)
  (p2: t1 -> GTot Type0)
  (prf: parse_strengthen_prf p1 p2)
: Tot (parser k (x: t1 { p2 x } ))
= bare_parse_strengthen_correct p1 p2 prf;
  bare_parse_strengthen p1 p2 prf

let serialize_strengthen'
  (#k: parser_kind)
  (#t1: Type)
  (#p1: parser k t1)
  (p2: t1 -> GTot Type0)
  (prf: parse_strengthen_prf p1 p2)
  (s: serializer p1)
  (input: t1 { p2 input } )
: GTot bytes
= serialize s input

let serialize_strengthen_correct
  (#k: parser_kind)
  (#t1: Type)
  (#p1: parser k t1)
  (p2: t1 -> GTot Type0)
  (prf: parse_strengthen_prf p1 p2)
  (s: serializer p1)
  (input: t1 { p2 input } )
: Lemma
  (let output = serialize_strengthen' p2 prf s input in
  parse (parse_strengthen p1 p2 prf) output == Some (input, Seq.length output))
= ()

let serialize_strengthen
  (#k: parser_kind)
  (#t1: Type)
  (#p1: parser k t1)
  (p2: t1 -> GTot Type0)
  (prf: parse_strengthen_prf p1 p2)
  (s: serializer p1)
: Tot (serializer (parse_strengthen p1 p2 prf))
= Classical.forall_intro (serialize_strengthen_correct p2 prf s);
  serialize_strengthen' p2 prf s

let compose (#t1 #t2 #t3: Type) (f1: t1 -> GTot t2) (f2: t2 -> GTot t3) (x: t1) : GTot t3 =
  let y1 = f1 x in
  f2 y1

val make_total_constant_size_parser_compose
  (sz: nat)
  (t1 t2: Type)
  (f1: ((s: bytes {Seq.length s == sz}) -> GTot t1))
  (g2: t1 -> GTot t2)
: Lemma
  (requires (
    make_total_constant_size_parser_precond sz t1 f1 /\
    (forall x x' . g2 x == g2 x' ==> x == x')
  ))
  (ensures (
    make_total_constant_size_parser_precond sz t1 f1 /\
    make_total_constant_size_parser_precond sz t2 (f1 `compose` g2) /\
    (forall x x' . {:pattern (g2 x); (g2 x')}  g2 x == g2 x' ==> x == x') /\
    (forall input . {:pattern (parse (make_total_constant_size_parser sz t2 (f1 `compose` g2)) input)} parse (make_total_constant_size_parser sz t2 (f1 `compose` g2)) input == parse (make_total_constant_size_parser sz t1 f1 `parse_synth` g2) input)
  ))

(** Tot vs. Ghost *)

unfold
let lift_parser'
  (#k: parser_kind)
  (#t: Type)
  (f: unit -> GTot (parser k t))
: Tot (bare_parser t)
= fun (input: bytes) -> parse (f ()) input

let lift_parser_correct
  (#k: parser_kind)
  (#t: Type)
  (f: unit -> GTot (parser k t))
: Lemma
  (parser_kind_prop k (lift_parser' f))
= parser_kind_prop_ext k (f ()) (lift_parser' f)

let lift_parser
  (#k: parser_kind)
  (#t: Type)
  (f: unit -> GTot (parser k t))
: Tot (parser k t)
= lift_parser_correct f;
  lift_parser' f

unfold
let lift_serializer'
  (#k: parser_kind)
  (#t: Type)
  (#f: unit -> GTot (parser k t))
  (s: unit -> GTot (serializer (f ())))
: Tot (bare_serializer t)
= fun (x: t) -> serialize (s ()) x

let lift_serializer_correct
  (#k: parser_kind)
  (#t: Type)
  (#f: unit -> GTot (parser k t))
  (s: unit -> GTot (serializer (f ())))
: Lemma
  (serializer_correct (lift_parser f) (lift_serializer' s))
= ()

let lift_serializer
  (#k: parser_kind)
  (#t: Type)
  (#f: unit -> GTot (parser k t))
  (s: unit -> GTot (serializer (f ())))
: Tot (serializer #k #t (lift_parser f))
= lift_serializer_correct #k #t #f s;
  lift_serializer' #k #t #f s

(** Refinements *)

// unfold
inline_for_extraction
let parse_filter_kind (k: parser_kind) : Tot parser_kind =
  {
    parser_kind_low = k.parser_kind_low;
    parser_kind_high = k.parser_kind_high;
    parser_kind_metadata =
      begin match k.parser_kind_metadata with
      | Some ParserKindMetadataFail -> Some ParserKindMetadataFail
      | _ -> None
      end;
    parser_kind_subkind = k.parser_kind_subkind;
  }

// unfold
let parse_filter_payload_kind : parser_kind =
  strong_parser_kind 0 0 None

let parse_filter_refine (#t: Type) (f: (t -> GTot bool)) =
  (x: t { f x == true } )

let parse_filter_payload
  (#t: Type)
  (f: (t -> GTot bool))
  (v: t)
: Tot (parser parse_filter_payload_kind (parse_filter_refine f))
= let p = lift_parser (fun () ->
    if f v
    then
      let v' : (x: t { f x == true } ) = v in
      weaken parse_filter_payload_kind (parse_ret v')
    else fail_parser parse_filter_payload_kind (parse_filter_refine f)
  )
  in
  parser_kind_prop_equiv parse_filter_payload_kind p;
  p

val parse_filter
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (f: (t -> GTot bool))
: Tot (parser (parse_filter_kind k) (parse_filter_refine f))

val parse_filter_eq
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (f: (t -> GTot bool))
  (input: bytes)
: Lemma
  (parse (parse_filter p f) input == (match parse p input with
  | None -> None
  | Some (x, consumed) ->
    if f x
    then Some (x, consumed)
    else None
  ))

let serialize_filter'
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  (f: (t -> GTot bool))
: Tot (bare_serializer (x: t { f x == true } ))
= fun (input: t { f input == true } ) -> s input

val serialize_filter_correct
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  (f: (t -> GTot bool))
: Lemma
  (serializer_correct (parse_filter p f) (serialize_filter' s f))

let serialize_filter
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (s: serializer p)
  (f: (t -> GTot bool))
: Tot (serializer (parse_filter p f))
= serialize_filter_correct s f;
  serialize_filter' s f

let serialize_weaken
  (#k: parser_kind)
  (#t: Type)
  (k' : parser_kind)
  (#p: parser k t)
  (s: serializer p { k' `is_weaker_than` k })
: Tot (serializer (weaken k' p))
= serialize_ext _ s (weaken k' p)

(* Helpers to define `if` combinators *)

let cond_true (cond: bool) : Tot Type = (u: unit { cond == true } )

let cond_false (cond: bool) : Tot Type = (u: unit { cond == false } )
