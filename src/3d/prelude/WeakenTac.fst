module WeakenTac

open EverParse3d.Actions

module T = LowParse.TacLib

let inv_implies_true (inv0:slice_inv) : Tot (squash (inv0 `inv_implies` true_inv)) = ()

let inv_implies_conj (inv0 inv1 inv2: slice_inv) (h01: squash (inv0 `inv_implies` inv1)) (h02: squash (inv0 `inv_implies` inv2)) : Tot (squash (inv0 `inv_implies` (inv1 `conj_inv` inv2))) = ()

let inv_conj_implies_l (inv1 inv2: slice_inv) (inv0: slice_inv) (h: squash (inv1 `inv_implies` inv0)) : Tot (squash ((inv1 `conj_inv` inv2) `inv_implies` inv0)) = ()

let inv_conj_implies_r (inv1 inv2: slice_inv) (inv0: slice_inv) (h: squash (inv2 `inv_implies` inv0)) : Tot (squash ((inv1 `conj_inv` inv2) `inv_implies` inv0)) = ()

let inv_implies_refl (inv: slice_inv) : Tot (squash (inv `inv_implies` inv)) = ()

let eloc_includes_none (l1:eloc) : Tot (squash (l1 `eloc_includes` eloc_none)) = ()

let eloc_includes_union (l0: eloc) (l1 l2: eloc) (h01: squash (l0 `eloc_includes` l1)) (h02: squash (l0 `eloc_includes` l2)) : Tot (squash (l0 `eloc_includes` (l1 `eloc_union` l2))) = ()

let eloc_union_includes_l (l1 l2: eloc) (l0: eloc) (h: squash (l1 `eloc_includes` l0)) : Tot (squash ((l1 `eloc_union` l2) `eloc_includes` l0)) = ()

let eloc_union_includes_r (l1 l2: eloc) (l0: eloc) (h: squash (l2 `eloc_includes` l0)) : Tot (squash ((l1 `eloc_union` l2) `eloc_includes` l0)) = ()

let eloc_includes_refl (l: eloc) : Tot (squash (l `eloc_includes` l)) = ()

let squash_1_to_2 (p: Type0) (_: squash p) : Tot (squash (squash p)) = ()

[@@ noextract_to "Kremlin"]
let rec subterm_appears_in_term
  (conj: T.term)
  (refl: (unit -> T.Tac unit))
  (ltac: (unit -> T.Tac unit))
  (rtac: (unit -> T.Tac unit))
  (subterm: T.term)
  (term: T.term)
: T.Tac (option (unit -> T.Tac unit))
= if subterm `T.term_eq` term
  then
    Some refl
  else
    let (hd, tl) = T.app_head_tail term in
    if hd `T.term_eq` conj
    then
      match tl with 
      | _::_::_ ->
        let ((tl1, _) :: (tl2, _) :: _) = tl in
        begin match subterm_appears_in_term conj refl ltac rtac subterm tl1 with
        | Some f -> Some (fun _ -> ltac (); f ())
        | None ->
	  begin match subterm_appears_in_term conj refl ltac rtac subterm tl2 with
	  | Some f -> Some (fun _ -> rtac (); f ())
	  | None -> None
	  end
        end
      | _ -> None
    else
      None

[@@ plugin; noextract_to "Kremlin"]
let rec weaken_tac () : T.Tac unit =
    let open T in
    let n = T.ngoals () in
    if n = 0 then ()
    else if n > 1 then begin
      T.print "fail: more than 1 goal";
      T.fail "more than 1 goal"
    end
    else
      let g = T.cur_goal () in
      let f = T.term_as_formula g in
      match f with
      | True_ -> ()
      | Implies _ _ ->
        let _ = T.implies_intro () in
        weaken_tac ()
      | Forall _ _ ->
        let _ = T.forall_intro () in
        weaken_tac()
      | And _ _ ->
        T.split ();
        T.iterAll (fun _ -> weaken_tac ())
      | Comp (Eq _) _ _ ->
        T.trefl ();
        T.qed ()
      | _ ->
        T.norm [delta_only ["Prims.auto_squash"]];
	let g = T.cur_goal () in
	let default_ = T.smt in
	let (hd1, tl1) = app_head_tail g in
	tassert (hd1 `T.term_eq` (`Prims.squash));
	tassert (Cons? tl1);
	let ((tl1', _) :: _) = tl1 in
	let (hd2, tl2) = app_head_tail tl1' in
	if hd2 `T.term_eq` (`Prims.squash)
	then begin
          T.apply (`squash_1_to_2);
	  weaken_tac ()
	end else
	if hd2 `T.term_eq` (`eloc_includes)
	then begin
	  tassert (Cons? tl2);
	  tassert (Cons? (List.Tot.Base.tl tl2));
	  let ((tl2_1, _) :: (tl2_2, _) :: _) = tl2 in
	  if tl2_2 `T.term_eq` (`eloc_none)
	  then begin
	    T.apply (`eloc_includes_none);
	    T.qed ()
	  end else
	    let (hd3, _) = app_head_tail tl2_2 in
	    if hd3 `T.term_eq` (`eloc_union)
	    then begin
	      T.apply (`eloc_includes_union);
	      T.iterAll (fun _ -> weaken_tac ())
	    end else begin
	      match subterm_appears_in_term
		(`eloc_union)
		(fun _ -> T.apply (`eloc_includes_refl); T.qed ())
		(fun _ -> T.apply (`eloc_union_includes_l))
		(fun _ -> T.apply (`eloc_union_includes_r))
		tl2_2
		tl2_1
	      with
	      | Some f -> f ()
	      | None -> default_ ()
	    end
	end else
	if hd2 `T.term_eq` (`inv_implies)
	then begin
	  tassert (Cons? tl2);
	  tassert (Cons? (List.Tot.Base.tl tl2));
	  let ((tl2_1, _) :: (tl2_2, _) :: _) = tl2 in
	  if tl2_2 `T.term_eq` (`true_inv)
	  then begin
	    T.apply (`inv_implies_true);
	    T.qed ()
	  end else
	    let (hd3, _) = app_head_tail tl2_2 in
	    if hd3 `T.term_eq` (`conj_inv)
	    then begin
	      T.apply (`inv_implies_conj);
	      T.iterAll (fun _ -> weaken_tac ())
	    end else begin
	      match subterm_appears_in_term
		(`conj_inv)
		(fun _ -> T.apply (`inv_implies_refl); T.qed ())
		(fun _ -> T.apply (`inv_conj_implies_l))
		(fun _ -> T.apply (`inv_conj_implies_r))
		tl2_2
		tl2_1
	      with
	      | Some f -> f ()
	      | None -> default_ ()
	    end
	end else
	  default_ ()
