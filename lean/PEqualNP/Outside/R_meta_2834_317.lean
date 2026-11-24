import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- In a smallest candidate every suffix wire is read. Each raw input also has a
-- separating pair on which both supplied disjunctions stay fixed.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem PEqualNP.Outside.R_meta_2834_317 :
    (¬ HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) 14) →
    (∀ (a b : Fin 9) (R : Circuit) (extra : List ℕ), a ≠ 0 → a ≠ 4 → b ≠ 0 → b ≠ 4 → a ≠ b →
      Monotone2 R → R.size = 13 → extra.length ≤ 3 →
      (R.gates.flatMap Gate.inputs ++ [R.output]).Perm (List.range 24 ++ extra) →
      (∀ x : Fin 9 → Bool, R.eval (List.ofFn x ++ [x 0 || x 4, x a || x b]) =
          ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) → False) →
    (∀ (a b : Fin 9) (R : Circuit) (extra : List ℕ), a ≠ 0 → a ≠ 4 → b ≠ 0 → b ≠ 4 → a ≠ b →
      FanInTwo R → R.size = 13 → extra.length ≤ 2 →
      (R.gates.flatMap Gate.inputs ++ [R.output]).Perm (List.range 24 ++ extra) →
      (∀ x : Fin 9 → Bool, R.eval (List.ofFn x ++ [x 0 || x 4, x a || x b]) =
          ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) → False) →
    ∀ (x1 x2 : Fin (9 : ℕ)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), x1 ≠ (0 : Fin (9 : ℕ)) → x1 ≠ (4 : Fin (9 : ℕ)) → x2 ≠ (0 : Fin (9 : ℕ)) → x2 ≠ (4 : Fin (9 : ℕ)) → x1 ≠ x2 → PEqualNP.MetaComplexity.FanInTwo x3 → x3.size ≤ (13 : ℕ) → (∀ (x11 : Fin (9 : ℕ) → Bool), x3.eval (List.ofFn x11 ++ [x11 (0 : Fin (9 : ℕ)) || x11 (4 : Fin (9 : ℕ)), x11 x1 || x11 x2]) = (x11 (0 : Fin (9 : ℕ)) && x11 (1 : Fin (9 : ℕ)) || x11 (1 : Fin (9 : ℕ)) && x11 (2 : Fin (9 : ℕ)) || x11 (2 : Fin (9 : ℕ)) && x11 (3 : Fin (9 : ℕ)) || x11 (3 : Fin (9 : ℕ)) && x11 (4 : Fin (9 : ℕ)) || x11 (4 : Fin (9 : ℕ)) && x11 (0 : Fin (9 : ℕ)) || x11 (0 : Fin (9 : ℕ)) && x11 (5 : Fin (9 : ℕ)) || x11 (1 : Fin (9 : ℕ)) && x11 (6 : Fin (9 : ℕ)) || x11 (2 : Fin (9 : ℕ)) && x11 (7 : Fin (9 : ℕ)) || x11 (3 : Fin (9 : ℕ)) && x11 (8 : Fin (9 : ℕ)) || x11 (5 : Fin (9 : ℕ)) && x11 (7 : Fin (9 : ℕ)) || x11 (6 : Fin (9 : ℕ)) && x11 (8 : Fin (9 : ℕ)) || x11 (8 : Fin (9 : ℕ)) && x11 (5 : Fin (9 : ℕ)))) → False := by
  let F := fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
  let bank := fun (a b : Fin 9) (x : Fin 9 → Bool) => List.ofFn x ++ [x 0 || x 4, x a || x b]
  have sensitive : ∀ a b : Fin 9, a ≠ 0 → a ≠ 4 → b ≠ 0 → b ≠ 4 → a ≠ b → ∀ i : Fin 9,
      ∃ (x y : Fin 9 → Bool), F x = false ∧ F y = true ∧ ∀ j : ℕ, j ≠ i.val →
        (bank a b x).getD j false = (bank a b y).getD j false := by
    let data : Array ℕ := #[2, 2, 20, 10, 16, 32, 80, 130, 258, 1, 1, 4, 9, 20, 36, 64, 129, 257, 9, 2, 2, 8, 18, 34, 72, 128, 258, 5, 18, 4, 4, 16, 36, 68, 144, 256, 1, 10, 5, 8, 1, 40, 65, 129, 257, 1, 130, 5, 9, 144, 1, 65, 128, 256, 257, 2, 260, 10, 18, 34, 2, 130, 256, 5, 34, 4, 40, 20, 32, 68, 4, 260, 9, 10, 36, 8, 48, 32, 64, 136, 8]
    let mate := fun (a b i : Fin 9) => if i = 0 then 4 else if i = 4 then 0 else if i = a then b else if i = b then a else i
    let base := fun (a b i j : Fin 9) => data[9*i.val + (mate a b i).val]!.testBit j.val
    have table : ∀ (a b i : Fin 9), a ≠ 0 → a ≠ 4 → b ≠ 0 → b ≠ 4 → a ≠ b →
        let x := base a b i
        let y := Function.update x i true
        F x = false ∧ F y = true ∧ (x 0 || x 4) = (y 0 || y 4) ∧ (x a || x b) = (y a || y b) := by decide
    intro a b ha0 ha4 hb0 hb4 hab i
    let x := base a b i
    let y := Function.update x i true
    obtain ⟨neg,pos,fixed,extra⟩ := table a b i ha0 ha4 hb0 hb4 hab
    refine ⟨x,y,neg,pos,?_⟩
    intro j hj
    change (List.ofFn x ++ [x 0 || x 4, x a || x b]).getD j false =
      (List.ofFn y ++ [y 0 || y 4, y a || y b]).getD j false
    by_cases h : j < 9
    · rw [List.getD_append _ _ _ _ (by simpa using h), List.getD_append _ _ _ _ (by simpa using h),
          List.getD_eq_getElem _ _ (by simpa using h), List.getD_eq_getElem _ _ (by simpa using h)]
      simp only [List.getElem_ofFn]
      exact (Function.update_of_ne (fun eq => hj (congrArg Fin.val eq)) _ _).symm
    · rw [List.getD_append_right _ _ _ _ (by simp only [List.length_ofFn]; omega),
          List.getD_append_right _ _ _ _ (by simp only [List.length_ofFn]; omega)]
      change [x 0 || x 4, x a || x b].getD (j-9) false = [y 0 || y 4, y a || y b].getD (j-9) false
      change (x 0 || x 4) = (y 0 || y 4) at fixed
      change (x a || x b) = (y a || y b) at extra
      rw [fixed, extra]
  have unread (C : Circuit) (i : ℕ) (missing : i ∉ C.gates.flatMap Gate.inputs ++ [C.output])
    (x y : List Bool) (lens : x.length = y.length) (agree : ∀ j, j ≠ i → x.getD j false = y.getD j false) :
    C.eval x = C.eval y := by
    let step := fun (w : List Bool) (h : Gate) => w ++ [h.op.eval (h.inputs.map fun j => w.getD j false)]
    have read (t : List Bool) (j : ℕ) (h : j ≠ i) : (x ++ t).getD j false = (y ++ t).getD j false := by
      by_cases b : j < x.length
      · rw [List.getD_append _ _ _ _ b, List.getD_append _ _ _ _ (lens ▸ b), agree j h]
      · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), lens]
    have run (gs : List Gate) (t : List Bool) (ok : ∀ g ∈ gs, i ∉ g.inputs) :
        ∃ v : List Bool, gs.foldl step (x ++ t) = x ++ v ∧ gs.foldl step (y ++ t) = y ++ v := by
      induction gs generalizing t with
      | nil => exact ⟨t,rfl,rfl⟩
      | cons g gs ih =>
        let a := g.op.eval (g.inputs.map fun j => (y ++ t).getD j false)
        have ea : g.op.eval (g.inputs.map fun j => (x ++ t).getD j false) = a := by
          exact congrArg g.op.eval (List.map_congr_left fun j hj => read t j (fun eq => ok g List.mem_cons_self (eq ▸ hj)))
        have bx : step (x ++ t) g = x ++ (t ++ [a]) := by simp only [step, ea, List.append_assoc]
        have byy : step (y ++ t) g = y ++ (t ++ [a]) := by simp only [step, a, List.append_assoc]
        simpa only [List.foldl_cons, bx, byy] using ih (t ++ [a]) (fun q hq => ok q (List.mem_cons_of_mem _ hq))
    have ok : ∀ g ∈ C.gates, i ∉ g.inputs := fun g hg hi => missing (List.mem_append_left _ (List.mem_flatMap.mpr ⟨g,hg,hi⟩))
    have out : C.output ≠ i := fun h => missing (List.mem_append_right _ (by simp [h]))
    obtain ⟨v, hx, hy⟩ := run C.gates [] ok
    simp only [List.append_nil] at hx hy
    change (C.gates.foldl step x).getD C.output false = (C.gates.foldl step y).getD C.output false
    rw [hx,hy,read v _ out]
  have erase (C : Circuit) (valid : FanInTwo C) (n i : ℕ) (hi : i < C.gates.length)
    (unused : n+i ∉ C.gates.flatMap Gate.inputs ++ [C.output]) :
    ∃ D : Circuit, FanInTwo D ∧ D.size + 1 = C.size ∧
      ∀ x : List Bool, x.length = n → D.eval x = C.eval x := by
    let xs := C.gates.take i
    let g := C.gates[i]
    let ys := C.gates.drop (i+1)
    have split : C.gates = xs ++ g :: ys := by
      have h := List.take_append_drop i C.gates
      rw [List.drop_eq_getElem_cons hi] at h
      exact h.symm
    have lx : xs.length = i := by simp [xs, Nat.min_eq_left (Nat.le_of_lt hi)]
    let m := n+i
    let idx := fun j : ℕ => if j < m then j else j-1
    let rename := fun h : Gate => Gate.mk h.op (h.inputs.map idx)
    let D := Circuit.mk (xs ++ ys.map rename) (idx C.output)
    have nx (h : Gate) (hh : h ∈ xs) : h ∈ C.gates := by rw [split]; exact List.mem_append_left _ hh
    have ny (h : Gate) (hh : h ∈ ys) : h ∈ C.gates := by rw [split]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hh)
    have noRead (h : Gate) (hh : h ∈ ys) (j : ℕ) (hj : j ∈ h.inputs) : j ≠ m := by
      intro e
      apply unused
      exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨h, ny h hh, by simpa only [e] using hj⟩)
    have noOut : C.output ≠ m := by
      intro e
      apply unused
      exact List.mem_append_right _ (by simp [e, m])
    refine ⟨D, ?_, ?_, ?_⟩
    · intro h hh
      rcases List.mem_append.mp hh with left | right
      · exact valid h (nx h left)
      · obtain ⟨q, qy, rfl⟩ := List.mem_map.mp right
        simpa only [rename, List.length_map] using valid q (ny q qy)
    · change (xs ++ ys.map rename).length + 1 = C.gates.length
      rw [split]
      simp only [List.length_append, List.length_map, List.length_cons]
      omega
    · intro x hx
      let step := fun (w : List Bool) (h : Gate) => w ++ [h.op.eval (h.inputs.map fun j => w.getD j false)]
      let w := xs.foldl step x
      let val := g.op.eval (g.inputs.map fun j => w.getD j false)
      have lens (gs : List Gate) (v : List Bool) : (gs.foldl step v).length = v.length + gs.length := by
        induction gs generalizing v with
        | nil => simp
        | cons q gs ih =>
          simp only [List.foldl_cons, ih, step, List.length_append, List.length_cons, List.length_nil]
          omega
      have lw : w.length = m := (lens xs x).trans (by rw [hx, lx])
      have read (t : List Bool) (j : ℕ) (hj : j ≠ m) :
          (w ++ t).getD (idx j) false = (w ++ (val :: t)).getD j false := by
        by_cases lo : j < m
        · have k : idx j = j := ite_eq_left lo
          rw [k, List.getD_append _ _ _ _ (lw ▸ lo), List.getD_append _ _ _ _ (lw ▸ lo)]
        · have k : idx j = j-1 := ite_eq_right lo
          rw [k, List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
          have eq : j - w.length = (j-1-w.length) + 1 := by omega
          rw [eq]
          rfl
      have run (hs : List Gate) (ok : ∀ q ∈ hs, ∀ j ∈ q.inputs, j ≠ m) (t : List Bool) :
          ∃ tail : List Bool, (hs.map rename).foldl step (w ++ t) = w ++ tail ∧
            hs.foldl step (w ++ (val :: t)) = w ++ (val :: tail) := by
        induction hs generalizing t with
        | nil => exact ⟨t, rfl, rfl⟩
        | cons q hs ih =>
          let v := q.op.eval (q.inputs.map fun j => (w ++ (val :: t)).getD j false)
          have eqVal : (rename q).op.eval ((rename q).inputs.map fun j => (w ++ t).getD j false) = v := by
            change q.op.eval ((q.inputs.map idx).map _) = q.op.eval _
            rw [List.map_map]
            exact congrArg q.op.eval (List.map_congr_left fun j hj => read t j (ok q List.mem_cons_self j hj))
          have a : step (w ++ t) (rename q) = w ++ (t ++ [v]) := by simp only [step, eqVal, List.append_assoc]
          have b : step (w ++ (val :: t)) q = w ++ (val :: (t ++ [v])) := by simp only [step, v, List.append_assoc, List.cons_append]
          simpa only [List.map_cons, List.foldl_cons, a, b] using
            ih (fun z hz => ok z (List.mem_cons_of_mem q hz)) (t ++ [v])
      obtain ⟨tail, da, ca⟩ := run ys noRead []
      simp only [List.append_nil] at da ca
      change ((xs ++ ys.map rename).foldl step x).getD (idx C.output) false =
        (C.gates.foldl step x).getD C.output false
      rw [split, List.foldl_append, List.foldl_append, List.foldl_cons]
      change ((ys.map rename).foldl step w).getD (idx C.output) false =
        (ys.foldl step (w ++ [val])).getD C.output false
      rw [da, ca, read tail C.output noOut]
  have normalize (C : Circuit) (ok : FanInTwo C) : ∃ N : Circuit, N.size = C.size ∧ FanInTwo N ∧
    (∀ g ∈ N.gates, g.op = .not → g.inputs.length ≤ 1) ∧ ∀ x, N.eval x = C.eval x := by
    letI : DecidableEq GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
    let cut := fun h : Gate => if h.op = .not then Gate.mk .not (h.inputs.take 1) else h
    let N := Circuit.mk (C.gates.map cut) C.output
    have form (g : Gate) : (cut g).op = g.op ∧ (cut g).inputs.length ≤ g.inputs.length ∧
        ((cut g).op = .not → (cut g).inputs.length ≤ 1) := by
      by_cases h : g.op = .not <;> simp [cut,h]
    refine ⟨N, List.length_map cut, ?_, ?_, ?_⟩
    · intro g hg
      obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hg
      exact ⟨(form old).1 ▸ (ok old hold).1, (form old).2.1.trans (ok old hold).2⟩
    · intro g hg
      obtain ⟨old, _, rfl⟩ := List.mem_map.mp hg
      exact (form old).2.2
    · let step := fun (w : List Bool) (g : Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
      have stepEq (w) (g : Gate) : step w (cut g) = step w g := by
        by_cases h : g.op = .not
        · simp only [cut, h, ite_true]
          obtain ⟨op, ins⟩ := g
          change op = .not at h
          subst op
          cases ins <;> rfl
        · simp only [cut, if_neg h]
      have run (gs : List Gate) (x : List Bool) : (gs.map cut).foldl step x = gs.foldl step x := by
        induction gs generalizing x with
        | nil => rfl
        | cons q gs ih => simpa only [List.map_cons, List.foldl_cons, stepEq] using ih (step x q)
      intro x
      exact congrArg (fun (v : List Bool) => v.getD C.output false) (run C.gates x)
  intro short monotone tight a b C ha0 ha4 hb0 hb4 hab fan size computes
  change ∀ x, C.eval (bank a b x) = F x at computes
  obtain ⟨R, sameSize, rf, unary, same⟩ := normalize C fan
  have fits : R.size ≤ 13 := sameSize.trans_le size
  have eqR (x) : R.eval (bank a b x) = F x := (same _).trans (computes x)
  let A := Gate.mk .or [0,4]
  let B := Gate.mk .or [a.val,b.val]
  let full := Circuit.mk (A :: B :: R.gates) R.output
  have legal : FanInTwo full := by
    intro g hg
    rcases List.mem_cons.mp hg with h | hg
    · subst g; exact ⟨Or.inr (Or.inl rfl), by change 2 ≤ 2; decide⟩
    rcases List.mem_cons.mp hg with h | hg
    · subst g; exact ⟨Or.inr (Or.inl rfl), by change 2 ≤ 2; decide⟩
    exact rf g hg
  let step := fun (w : List Bool) (h : Gate) => w ++ [h.op.eval (h.inputs.map fun j => w.getD j false)]
  have actual (x : Fin 9 → Bool) : full.eval (List.ofFn x) = F x := by
    let t := List.ofFn x
    have rd (i : Fin 9) : t.getD i.val false = x i := by
      rw [List.getD_eq_getElem _ _ (by simp [t])]
      simp only [t,List.getElem_ofFn]
    have rd2 (v : Bool) (i : Fin 9) : (t ++ [v]).getD i.val false = x i :=
      (List.getD_append _ _ _ _ (by simp [t])).trans (rd i)
    have va : step t A = t ++ [x 0 || x 4] := by
      change t ++ [(t.getD 0 false || (t.getD 4 false || false))] = _
      have r0 := rd 0
      have r4 := rd 4
      change t.getD 0 false = x 0 at r0
      change t.getD 4 false = x 4 at r4
      rw [r0, r4, Bool.or_false]
    have vb : step (t ++ [x 0 || x 4]) B = bank a b x := by
      change (t ++ [x 0 || x 4]) ++ [((t ++ [x 0 || x 4]).getD a.val false ||
        ((t ++ [x 0 || x 4]).getD b.val false || false))] = t ++ [x 0 || x 4, x a || x b]
      rw [rd2,rd2,Bool.or_false,List.append_assoc]
      rfl
    change (R.gates.foldl step (step (step t A) B)).getD R.output false = F x
    rw [va, vb]
    exact eqR x
  have szFull : full.size = R.size + 2 := by
    change (A :: B :: R.gates).length = R.gates.length + 2
    simp only [List.length_cons]
  have exactSize : R.size = 13 := by
    by_contra h
    exact short ⟨full, legal, by omega, actual⟩
  let reads := R.gates.flatMap Gate.inputs ++ [R.output]
  have all : List.range 24 ⊆ reads := by
    intro j hj
    have jb := List.mem_range.mp hj
    by_contra miss
    by_cases raw : j < 9
    · obtain ⟨x,y,fx,fy,diff⟩ := sensitive a b ha0 ha4 hb0 hb4 hab ⟨j,raw⟩
      have eq := unread R j miss (bank a b x) (bank a b y) (by simp [bank]) diff
      rw [eqR,eqR,fx,fy] at eq
      contradiction
    · have absent : j ∉ full.gates.flatMap Gate.inputs ++ [full.output] := by
        intro h
        rcases List.mem_append.mp h with h | h
        · obtain ⟨g, hg, hjg⟩ := List.mem_flatMap.mp h
          rcases List.mem_cons.mp hg with e | hg
          · subst g
            change j ∈ [0,4] at hjg
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hjg
            omega
          rcases List.mem_cons.mp hg with e | hg
          · subst g
            change j ∈ [a.val,b.val] at hjg
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hjg
            have := a.isLt
            have := b.isLt
            omega
          · exact miss (List.mem_append_left _ (List.mem_flatMap.mpr ⟨g,hg,hjg⟩))
        · exact miss (List.mem_append_right _ h)
      have hj' : 9 + (j - 9) = j := by omega
      have ht : j-9 < full.gates.length := by
        change j-9 < full.size
        omega
      obtain ⟨D,okD,smallD,sameD⟩ := erase full legal 9 (j-9) ht (by simpa only [hj'] using absent)
      exact short ⟨D,okD,by omega,fun x => (sameD (List.ofFn x) List.length_ofFn).trans (actual x)⟩
  obtain ⟨permList, permReads, sub⟩ := List.subperm_iff.mp ((List.nodup_range).subperm all)
  obtain ⟨extra, pe⟩ := sub.exists_perm_append
  have perm : reads.Perm (List.range 24 ++ extra) := permReads.symm.trans pe
  have lengths := perm.length_eq
  change (R.gates.flatMap Gate.inputs ++ [R.output]).length = (List.range 24 ++ extra).length at lengths
  simp only [List.length_append, List.length_singleton, List.length_range] at lengths
  have maxReads (gs : List Gate) (ok : ∀ g ∈ gs, g.inputs.length ≤ 2) :
      (gs.flatMap Gate.inputs).length ≤ 2 * gs.length ∧
      ((∃ g ∈ gs, g.inputs.length ≤ 1) → (gs.flatMap Gate.inputs).length < 2 * gs.length) := by
    induction gs with
    | nil => simp
    | cons h gs ih =>
      obtain ⟨lim, strict⟩ := ih (fun g hg => ok g (List.mem_cons_of_mem h hg))
      have hh := ok h List.mem_cons_self
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      refine ⟨by omega, ?_⟩
      rintro ⟨g,hg,one⟩
      rcases List.mem_cons.mp hg with e | hg
      · subst g; omega
      · have := strict ⟨g,hg,one⟩
        omega
  obtain ⟨bound, less⟩ := maxReads R.gates fun g hg => (rf g hg).2
  have lenR : R.gates.length = 13 := exactSize
  by_cases h : ∃ g ∈ R.gates, g.op = .not
  · obtain ⟨g,hg,op⟩ := h
    have := less ⟨g,hg,unary g hg op⟩
    exact tight a b R extra ha0 ha4 hb0 hb4 hab rf exactSize (by omega) perm eqR
  · have mono : Monotone2 R := by
      intro g hg
      have types : g.op = .and ∨ g.op = .or ∨ g.op = .not := (rf g hg).1
      refine ⟨?_,(rf g hg).2⟩
      rcases types with t | t | t
      · exact Or.inl t
      · exact Or.inr t
      · exact False.elim (h ⟨g,hg,t⟩)
    exact monotone a b R extra ha0 ha4 hb0 hb4 hab mono exactSize (by omega) perm eqR
