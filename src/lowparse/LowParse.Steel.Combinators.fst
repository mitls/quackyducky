module LowParse.Steel.Combinators
include LowParse.Steel.Validate
include LowParse.Steel.Access
include LowParse.Steel.Leaf
include LowParse.Spec.Combinators

module S = Steel.Memory
module SE = Steel.Effect
module SEA = Steel.Effect.Atomic
module A = Steel.Array
module AP = LowParse.Steel.ArrayPtr

module U32 = FStar.UInt32
module U64 = FStar.UInt64

unfold
let uint64_to_uint32
  (r1: U64.t)
  (sq: squash (is_success r1))
: Tot U32.t
= uint64_to_uint32 r1

#push-options "--z3rlimit 16"
let validate_pair
  #k1 #t1 (#p1: parser k1 t1) (v1: wvalidator p1)
  #k2 #t2 (#p2: parser k2 t2) (v2: wvalidator p2)
: Pure (wvalidator (p1 `nondep_then` p2))
  (requires (k1.parser_kind_subkind == Some ParserStrong))
  (ensures (fun _ -> True))
= fun a len ->
  let ga : Ghost.erased (AP.v byte) = SEA.gget (AP.varrayptr a) in
  let g : Ghost.erased _ = ga.AP.contents in
  nondep_then_eq p1 p2 g;
  let r1 = v1 a len in
  if is_error r1
  then begin
    SEA.return r1
  end
  else begin
    let sq : squash (is_success r1) = () in // FIXME: WHY WHY WHY does refinement or requires not work?
    let consumed = uint64_to_uint32 r1 sq in
    let a2 = AP.split a consumed in
    SEA.reveal_star (AP.varrayptr a) (AP.varrayptr a2); // FIXME: WHY WHY WHY is this needed?
    let ga1 : Ghost.erased (AP.v byte) = SEA.gget (AP.varrayptr a) in
    let g1 : Ghost.erased _ = ga1.AP.contents in
    parse_strong_prefix p1 g1 g;
    let ga2 : Ghost.erased (AP.v byte) = SEA.gget (AP.varrayptr a2) in // FIXME: WHY WHY WHY is this needed?
    let len2 = len `U32.sub` consumed in
    let r2 = v2 a2 len2 in
    AP.join a a2;
    if is_error r2
    then SEA.return r2
    else begin
      let res = r1 `U64.add` r2 in
      parse_strong_prefix p1 g (Seq.slice g 0 (U64.v res));
      nondep_then_eq p1 p2 (Seq.slice g 0 (U64.v res));
      SEA.return res
    end
  end
#pop-options

val destruct_pair
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (j1: parsed_size p1)
  (#k2: parser_kind)
  (#t2: Type)
  (p2: parser k2 t2)
  (a: byte_array)
: SE.Steel byte_array
    (vparse (p1 `nondep_then` p2) a)
    (fun res -> vparse p1 a `SE.star` vparse p2 res)
    (fun _ ->
      k1.parser_kind_subkind == Some ParserStrong
    )
    (fun h res h' ->
      let c = h (vparse (p1 `nondep_then` p2) a) in
      let c1 = h' (vparse p1 a) in
      let c2 = h' (vparse p2 res) in
      merge_into c1 c2 c /\
      c.contents == (c1.contents, c2.contents)
    )

let destruct_pair
  #k1 #t1 #p1 j1 p2 a
=
  elim_vparse (p1 `nondep_then` p2) a;
  let b : Ghost.erased (AP.v byte) = SEA.gget (AP.varrayptr a) in
  nondep_then_eq p1 p2 b.AP.contents;
  let res = peek_strong j1 a in
  SEA.reveal_star (vparse p1 a) (AP.varrayptr res);
  let c1 : Ghost.erased (v k1 t1) = SEA.gget (vparse p1 a) in // FIXME: WHY WHY WHY is the type annotation needed?
  parse_strong_prefix p1 (Seq.slice b.AP.contents 0 (A.length (array_of c1))) b.AP.contents;
  intro_vparse p2 res;
  SEA.return res

val construct_pair
  (#opened: _)
  (#k1: parser_kind)
  (#t1: Type)
  (p1: parser k1 t1)
  (#k2: parser_kind)
  (#t2: Type)
  (p2: parser k2 t2)
  (a1: byte_array)
  (a2: byte_array)
: SEA.SteelGhost unit opened
    (vparse p1 a1 `SE.star` vparse p2 a2)
    (fun _ -> vparse (p1 `nondep_then` p2) a1)
    (fun h ->
      adjacent (h (vparse p1 a1)) (h (vparse p2 a2)) /\
      k1.parser_kind_subkind == Some ParserStrong
    )
    (fun h res h' ->
      let c = h' (vparse (p1 `nondep_then` p2) a1) in
      let c1 = h (vparse p1 a1) in
      let c2 = h (vparse p2 a2) in
      merge_into c1 c2 c /\
      c.contents == (c1.contents, c2.contents)
    )

#push-options "--z3rlimit 16"
#restart-solver

let construct_pair
  #opened #k1 #t1 p1 p2 a1 a2
=
  let v1 : Ghost.erased (v k1 t1) = SEA.gget (vparse p1 a1) in // FIXME: WHY WHY WHY is this type annotation needed?
  elim_vparse p1 a1;
  elim_vparse p2 a2;
  let g1 = SEA.gget (AP.varrayptr a1) in
  let g2 = SEA.gget (AP.varrayptr a2) in
  AP.join a1 a2;
  let g : Ghost.erased (AP.v byte) = SEA.gget (AP.varrayptr a1) in // FIXME: same here
  nondep_then_eq p1 p2 g.AP.contents;
  Seq.lemma_append_inj g1.AP.contents g2.AP.contents (Seq.slice g.AP.contents 0 (A.length (array_of v1))) (Seq.slice g.AP.contents (A.length (array_of v1)) (Seq.length g.AP.contents));
  parse_strong_prefix p1 g1.AP.contents g.AP.contents;
  intro_vparse (p1 `nondep_then` p2) a1

#pop-options

let size_pair
  (#k1: parser_kind)
  (#t1: Type)
  (#p1: parser k1 t1)
  (j1: parsed_size p1)
  (#k2: parser_kind)
  (#t2: Type)
  (#p2: parser k2 t2)
  (j2: parsed_size p2)
: Tot (parsed_size (p1 `nondep_then` p2))
=
  fun a ->
  let g : Ghost.erased (AP.v byte) = SEA.gget (AP.varrayptr a) in
  nondep_then_eq p1 p2 g.AP.contents;
  let len1 = j1 a in
  let a2 = AP.split a len1 in
  let len2 = j2 a2 in
  AP.join a a2;
  SEA.return (len1 `U32.add` len2)

val validate_synth
  (#k1: _) (#t1: _) (#p1: parser k1 t1) (v1: wvalidator p1)
  (#t2: _) (f2: (t1 -> GTot t2))
  (f2_inj: squash (synth_injective f2))
: Tot (wvalidator (p1 `parse_synth` f2))

let validate_synth
  #_ #_ #p1 v1 f2 _
= fun a len ->
  Classical.forall_intro (Classical.move_requires (parse_synth_eq p1 f2));
  v1 a len

val intro_vparse_synth
  (#opened: _)
  (#k1: _) (#t1: _) (p1: parser k1 t1)
  (#t2: _) (f2: (t1 -> GTot t2))
  (f2_inj: squash (synth_injective f2))
  (a: byte_array)
: SEA.SteelGhost unit opened
    (vparse p1 a)
    (fun _ -> vparse (parse_synth p1 f2) a)
    (fun _ -> True)
    (fun h _ h' ->
      let r = h (vparse p1 a) in
      let r' = h' (vparse (parse_synth p1 f2) a) in
      r'.array_perm == r.array_perm /\
      r'.contents == f2 r.contents
    )

let intro_vparse_synth
  p1 f2 _ a
=
  elim_vparse p1 a;
  let g = SEA.gget (AP.varrayptr a) in
  parse_synth_eq p1 f2 g.AP.contents;
  intro_vparse (parse_synth p1 f2) a

val elim_vparse_synth
  (#opened: _)
  (#k1: _) (#t1: _) (p1: parser k1 t1)
  (#t2: _) (f2: (t1 -> GTot t2))
  (f2_inj: squash (synth_injective f2))
  (a: byte_array)
: SEA.SteelGhost unit opened
    (vparse (parse_synth p1 f2) a)
    (fun _ -> vparse p1 a)
    (fun _ -> True)
    (fun h _ h' ->
      let r = h (vparse (parse_synth p1 f2) a) in
      let r' = h' (vparse p1 a) in
      r'.array_perm == r.array_perm /\
      r.contents == f2 r'.contents
    )

let elim_vparse_synth
  p1 f2 _ a
=
  elim_vparse (parse_synth p1 f2) a;
  let g = SEA.gget (AP.varrayptr a) in
  parse_synth_eq p1 f2 g.AP.contents;
  intro_vparse p1 a

let size_synth
  (#k1: _) (#t1: _) (#p1: parser k1 t1)
  (j1: parsed_size p1)
  (#t2: _) (f2: (t1 -> GTot t2))
  (f2_inj: squash (synth_injective f2))
: Tot (parsed_size (p1 `parse_synth` f2))
= fun a ->
  let g = SEA.gget (AP.varrayptr a) in
  parse_synth_eq p1 f2 g.AP.contents;
  j1 a

val intro_vparse_filter
  (#opened: _)
  (#k: _) (#t: _) (p: parser k t)
  (f: (t -> GTot bool))
  (a: byte_array)
: SEA.SteelGhost unit opened
    (vparse p a)
    (fun _ -> vparse (parse_filter p f) a)
    (fun h -> f (h (vparse p a)).contents == true)
    (fun h _ h' ->
      let r = h (vparse p a) in
      let r' = h' (vparse (parse_filter p f) a) in
      f r.contents == true /\
      r'.array_perm == r.array_perm /\
      r'.contents == r.contents
    )

let intro_vparse_filter
  p f a
=
  elim_vparse p a;
  let g = SEA.gget (AP.varrayptr a) in
  parse_filter_eq p f g.AP.contents;
  intro_vparse (parse_filter p f) a

val elim_vparse_filter
  (#opened: _)
  (#k: _) (#t: _) (p: parser k t)
  (f: (t -> GTot bool))
  (a: byte_array)
: SEA.SteelGhost unit opened
    (vparse (parse_filter p f) a)
    (fun _ -> vparse p a)
    (fun _ -> True)
    (fun h _ h' ->
      let r = h (vparse (parse_filter p f) a) in
      let r' = h' (vparse p a) in
      f (r'.contents) == true /\
      r'.array_perm == r.array_perm /\
      r'.contents == r.contents
    )

let elim_vparse_filter
  p f a
=
  elim_vparse (parse_filter p f) a;
  let g = SEA.gget (AP.varrayptr a) in
  parse_filter_eq p f g.AP.contents;
  intro_vparse p a

let size_filter
  (#k: _) (#t: _) (#p: parser k t)
  (j: parsed_size p)
  (f: (t -> GTot bool))
: Tot (parsed_size (p `parse_filter` f))
= fun a ->
  let g = SEA.gget (AP.varrayptr a) in
  assert (Some? (parse (parse_filter p f) g.AP.contents)); // FIXME: WHY WHY WHY?
  parse_filter_eq p f g.AP.contents;
  j a

[@ CMacro ]
let validator_error_constraint_failed : validator_error = normalize_term (set_validator_error_kind 0uL 6uL)

let test_filter
  (#k: parser_kind)
  (#t: Type)
  (p: parser k t)
  (f: (t -> GTot bool))
: Tot Type0
= 
    (x: byte_array) ->
    SE.Steel bool
    (vparse p x)
    (fun _ -> vparse p x)
    (fun _ -> True)
    (fun h res h' ->
      h' (vparse p x) == h (vparse p x) /\
      res == f (h (vparse p x)).contents
    )

val validate_filter_gen
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (v32: wvalidator p)
  (f: (t -> GTot bool))
  (f' : test_filter p f)
: Pure (wvalidator (parse_filter p f))
  (requires (k.parser_kind_subkind == Some ParserStrong))
  (ensures (fun _ -> True))

let validate_filter_gen
  #_ #_ #p v32 f f'
= fun a len ->
  let glong = SEA.gget (AP.varrayptr a) in
  parse_filter_eq p f glong.AP.contents;
  let res = v32 a len in
  if is_error res
  then SEA.return res
  else begin
    let rlen = uint64_to_uint32 res () in
    let a2 = AP.split a rlen in
    let gshort = SEA.gget (AP.varrayptr a) in
    parse_strong_prefix p gshort.AP.contents glong.AP.contents;
    parse_filter_eq p f gshort.AP.contents;
    intro_vparse p a;
    let v = f' a in
    elim_vparse p a;
    let gshort' = SEA.gget (AP.varrayptr a) in
    AP.join a a2;
    parse_injective p gshort.AP.contents gshort'.AP.contents; // because of the intro_vparse ; elim_vparse sequence
    if v
    then SEA.return res
    else SEA.return validator_error_constraint_failed
  end

val validate_filter
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (v32: wvalidator p)
  (p32: leaf_reader p)
  (f: (t -> GTot bool))
  (f' : ((x: t) -> Pure bool (requires True) (ensures (fun y -> y == f x))))
: Pure (wvalidator (parse_filter p f))
  (requires (k.parser_kind_subkind == Some ParserStrong))
  (ensures (fun _ -> True))

let validate_filter
  #_ #_ #p v32 p32 f f'
= validate_filter_gen v32 f
    (fun a -> let r = p32 a in SEA.return (f' r))

val validate_filter'
  (#k: parser_kind)
  (#t: Type)
  (#p: parser k t)
  (v32: wvalidator p)
  (p32: leaf_reader p)
  (f: (t -> Tot bool))
: Pure (wvalidator (parse_filter p f))
  (requires (k.parser_kind_subkind == Some ParserStrong))
  (ensures (fun _ -> True))

let validate_filter' v32 p32 f = validate_filter v32 p32 f (fun x -> f x)
