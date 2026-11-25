import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 1600000 in
theorem PEqualNP.Outside.R_meta_3250_350
    (hBinary13 :
      let F : (Fin 9 → Bool) → Bool := fun x =>
        ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (5, 7), (6, 8), (8, 5)] :
          List (Fin 9 × Fin 9)).any fun e => x e.1 && x e.2
      ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D →
        (∀ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [x 0 || x 6]) = F x) →
        13 ≤ D.gates.countP (fun g => PEqualNP.CircuitLowerBounds.GateOp.rec (motive := fun _ => Bool) true true false (fun _ => true) true g.op))
    (hMono14 :
      let F : (Fin 9 → Bool) → Bool := fun x =>
        ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (5, 7), (6, 8), (8, 5)] :
          List (Fin 9 × Fin 9)).any fun e => x e.1 && x e.2
      ∀ M : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 M → M.size ≤ 14 →
        ∃ x : Fin 9 → Bool, M.eval (List.ofFn x ++ [x 0 || x 6]) ≠ F x)
    (hRawNot :
      let F : (Fin 9 → Bool) → Bool := fun x =>
        ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (5, 7), (6, 8), (8, 5)] :
          List (Fin 9 × Fin 9)).any fun e => x e.1 && x e.2
      ∀ (u : Fin 10) (M : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.Monotone2 M → M.size ≤ 13 →
        ∃ x : Fin 9 → Bool,
          let xs := List.ofFn x ++ [x 0 || x 6]
          M.eval (xs ++ [!(xs.getD u.val false)]) ≠ F x)
    (hGateNot :
      let F : (Fin 9 → Bool) → Bool := fun x =>
        ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (5, 7), (6, 8), (8, 5)] :
          List (Fin 9 × Fin 9)).any fun e => x e.1 && x e.2
      ∀ (A B : PEqualNP.CircuitLowerBounds.Circuit) (u : ℕ),
        PEqualNP.MetaComplexity.Monotone2 A → PEqualNP.MetaComplexity.Monotone2 B →
        1 ≤ A.size → A.size + B.size ≤ 13 → 10 ≤ u → u < 10 + A.size →
        ∃ x : Fin 9 → Bool,
          let w := A.wires (List.ofFn x ++ [x 0 || x 6])
          B.eval (w ++ [!(w.getD u false)]) ≠ F x) :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x2 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x1 x2.1 && x1 x2.2; ∀ (x2 : Fin (9 : ℕ)) (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ) (x6 : Bool),   x2 ≠ (0 : Fin (9 : ℕ)) →     x2 ≠ (6 : Fin (9 : ℕ)) →       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size ≤ (13 : ℕ) →           (10 : ℕ) ≤ x5 →             x5 < x4 →               x4 ≤ (10 : ℕ) + x3.size →                 (∀ x14 ∈ List.take (x4 - (10 : ℕ)) x3.gates, ↑x2 ∉ x14.inputs) →                   (∀ (x15 : Fin (9 : ℕ) → Bool),                       have x16 : Fin (9 : ℕ) → Bool := Function.update x15 x2 Bool.false;                       x1 x16 ≠ x1 (Function.update x15 x2 Bool.true) → (x3.wires (List.ofFn x16 ++ [x16 (0 : Fin (9 : ℕ)) || x16 (6 : Fin (9 : ℕ))])).getD x5 Bool.false = !x6) →                     ∃ (x16 : Fin (9 : ℕ) → Bool),                       have x17 : List Bool := List.ofFn x16 ++ [x16 (0 : Fin (9 : ℕ)) || x16 (6 : Fin (9 : ℕ))];                       have x18 : Bool := (x3.wires x17).getD x5 Bool.false;                       x3.eval (x17.set (↑x2) (if x6 = Bool.true then x16 x2 || x18 else x16 x2 && x18)) ≠ x1 x16 := by
  dsimp only
  intro v C cut idx disj hv0 hv6 hfanC hszC hidx10 hidxlt hcutle hprior _hsens
  let F : (Fin 9 → Bool) → Bool := fun x =>
    ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (5, 7), (6, 8), (8, 5)] :
      List (Fin 9 × Fin 9)).any fun e => x e.1 && x e.2
  let row : (Fin 9 → Bool) → List Bool := fun x => List.ofFn x ++ [x 0 || x 6]
  let step : List Bool → Gate → List Bool :=
    fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let mapGate : (ℕ → ℕ) → Gate → Gate := fun σ g => ⟨g.op, g.inputs.map σ⟩
  have hrowLen (x : Fin 9 → Bool) : (row x).length = 10 := by
    change (List.ofFn x ++ [x 0 || x 6]).length = 10
    rw [List.length_append, List.length_ofFn]
    rfl
  have hOr2 (a b : Bool) : GateOp.or.eval [a, b] = (a || b) := by
    cases a <;> cases b <;> rfl
  have hAnd2 (a b : Bool) : GateOp.and.eval [a, b] = (a && b) := by
    cases a <;> cases b <;> rfl
  have hFoldLen (gs : List Gate) (w : List Bool) :
      (gs.foldl step w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      change (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).length + gs.length =
        w.length + (gs.length + 1)
      rw [List.length_append]
      simp only [List.length_cons, List.length_nil]
      omega
  have hFoldKeep (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < w.length) :
      (gs.foldl step w).getD j false = w.getD j false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons]
      have hlen : j < (step w g).length := by
        change j < (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).length
        rw [List.length_append]
        omega
      rw [ih (step w g) hlen]
      change (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).getD j false = w.getD j false
      exact List.getD_append w [g.op.eval (g.inputs.map fun i => w.getD i false)] false j hj
  have hGetDSetNe (w : List Bool) (k i : ℕ) (b : Bool) (hne : i ≠ k) :
      (w.set k b).getD i false = w.getD i false := by
    change (w.set k b)[i]?.getD false = w[i]?.getD false
    rw [List.getElem?_set_ne (Ne.symm hne)]
  have hGetDSetSelf (w : List Bool) (k : ℕ) (b : Bool) (hk : k < w.length) :
      (w.set k b).getD k false = b := by
    change (w.set k b)[k]?.getD false = b
    rw [List.getElem?_set_self hk]
    rfl
  have hFoldSetComm (gs : List Gate) (w : List Bool) (k : ℕ) (b : Bool)
      (hk : k < w.length) (hav : ∀ g ∈ gs, k ∉ g.inputs) :
      gs.foldl step (w.set k b) = (gs.foldl step w).set k b := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, List.foldl_cons]
      have hknot : k ∉ g.inputs := hav g (List.mem_cons_self)
      have hmap : (g.inputs.map fun i => (w.set k b).getD i false) =
          (g.inputs.map fun i => w.getD i false) := by
        apply List.map_congr_left
        intro i hi
        exact hGetDSetNe w k i b (fun heq => hknot (heq ▸ hi))
      have hstep : step (w.set k b) g = (step w g).set k b := by
        change w.set k b ++ [g.op.eval (g.inputs.map fun i => (w.set k b).getD i false)] =
          (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).set k b
        rw [hmap, List.set_append_left _ _ hk]
      have hk' : k < (step w g).length := by
        change k < (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).length
        rw [List.length_append]
        omega
      rw [hstep, ih (step w g) hk' (fun h hh => hav h (List.mem_cons_of_mem g hh))]
  have hAppendGetD (w : List Bool) (val : Bool) (j : ℕ) :
      (w ++ [val]).getD j false = if j = w.length then val else w.getD j false := by
    by_cases h1 : j < w.length
    · have hne : j ≠ w.length := by omega
      rw [if_neg hne]
      exact List.getD_append w [val] false j h1
    · by_cases h2 : j = w.length
      · subst h2
        rw [if_pos rfl, List.getD_append_right w [val] false w.length le_rfl]
        simp
      · have hgt : w.length < j := by omega
        rw [if_neg h2, List.getD_eq_default (w ++ [val]) false (by rw [List.length_append]; simp; omega),
          List.getD_eq_default w false (by omega)]
  have hFoldMap (σ : ℕ → ℕ) (gs : List Gate) (a b : List Bool)
      (hmatch : ∀ k, b.getD (σ k) false = a.getD k false)
      (hpres : ∀ t k, σ k = b.length + t ↔ k = a.length + t) :
      ∀ k, ((gs.map (mapGate σ)).foldl step b).getD (σ k) false = (gs.foldl step a).getD k false := by
    induction gs generalizing a b with
    | nil => exact hmatch
    | cons g gs ih =>
      rw [List.map_cons, List.foldl_cons, List.foldl_cons]
      have hinputs : ((mapGate σ g).inputs.map fun i => b.getD i false) =
          (g.inputs.map fun i => a.getD i false) := by
        change (g.inputs.map σ).map (fun i => b.getD i false) = g.inputs.map (fun i => a.getD i false)
        rw [List.map_map]
        apply List.map_congr_left
        intro k _
        exact hmatch k
      have hval : (mapGate σ g).op.eval ((mapGate σ g).inputs.map fun i => b.getD i false) =
          g.op.eval (g.inputs.map fun i => a.getD i false) := by
        change g.op.eval ((mapGate σ g).inputs.map fun i => b.getD i false) =
          g.op.eval (g.inputs.map fun i => a.getD i false)
        rw [hinputs]
      let val := g.op.eval (g.inputs.map fun i => a.getD i false)
      have hmatch' : ∀ k, (step b (mapGate σ g)).getD (σ k) false = (step a g).getD k false := by
        intro k
        change (b ++ [(mapGate σ g).op.eval ((mapGate σ g).inputs.map fun i => b.getD i false)]).getD (σ k) false =
          (a ++ [val]).getD k false
        rw [hval, hAppendGetD b val (σ k), hAppendGetD a val k]
        have hiff := hpres 0 k
        rw [Nat.add_zero, Nat.add_zero] at hiff
        by_cases hk : k = a.length
        · have hk' : σ k = b.length := hiff.mpr hk
          rw [if_pos hk', if_pos hk]
        · have hk' : σ k ≠ b.length := fun h => hk (hiff.mp h)
          rw [if_neg hk', if_neg hk]
          exact hmatch k
      have hpres' : ∀ t k, σ k = (step b (mapGate σ g)).length + t ↔ k = (step a g).length + t := by
        intro t k
        have lb : (step b (mapGate σ g)).length = b.length + 1 := by
          change (b ++ [_]).length = b.length + 1
          rw [List.length_append]
          rfl
        have la : (step a g).length = a.length + 1 := by
          change (a ++ [_]).length = a.length + 1
          rw [List.length_append]
          rfl
        rw [lb, la, Nat.add_right_comm b.length 1 t, Nat.add_assoc b.length t 1]
        have := hpres (1 + t) k
        omega
      exact ih (step a g) (step b (mapGate σ g)) hmatch' hpres'
  refine Classical.byContradiction (fun hno => ?_)
  have hcorr : ∀ x : Fin 9 → Bool,
      let xs := row x
      let b := (C.wires xs).getD idx false
      C.eval (xs.set v.val (if disj = true then x v || b else x v && b)) = F x := by
    intro x
    cases h : Bool.decEq (C.eval ((row x).set v.val (if disj = true then x v || (C.wires (row x)).getD idx false else x v && (C.wires (row x)).getD idx false))) (F x) with
    | isTrue heq => exact heq
    | isFalse hne => exact False.elim (hno ⟨x, hne⟩)
  let pre := C.gates.take (cut - 10)
  let post := C.gates.drop (cut - 10)
  have hsplit : pre ++ post = C.gates := List.take_append_drop (cut - 10) C.gates
  have hprelen : pre.length = cut - 10 := by
    change (C.gates.take (cut - 10)).length = cut - 10
    rw [List.length_take]
    change min (cut - 10) C.size = cut - 10
    omega
  let gnew : Gate := ⟨if disj = true then GateOp.or else GateOp.and, [v.val, idx]⟩
  let rmap : ℕ → ℕ := fun w => if w = v.val then cut else if w < cut then w else w + 1
  let D : Circuit := ⟨pre ++ [gnew] ++ post.map (mapGate rmap), rmap C.output⟩
  have hfanD : FanInTwo D := by
    intro g hg
    change g ∈ pre ++ [gnew] ++ post.map (mapGate rmap) at hg
    rw [List.mem_append, List.mem_append] at hg
    rcases hg with (hg | hg) | hg
    · exact hfanC g (List.mem_of_mem_take hg)
    · rw [List.mem_singleton.mp hg]
      refine ⟨?_, by simp [gnew]⟩
      cases disj <;> simp [gnew]
    · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
      have hg0' := hfanC g0 (List.mem_of_mem_drop hg0)
      exact ⟨hg0'.1, by simpa [mapGate] using hg0'.2⟩
  have hszD : D.size ≤ 14 := by
    change (pre ++ [gnew] ++ post.map (mapGate rmap)).length ≤ 14
    rw [List.length_append, List.length_append, List.length_singleton, List.length_map]
    have hlenC : pre.length + post.length = C.gates.length := by
      rw [← List.length_append, hsplit]
    change C.gates.length ≤ 13 at hszC
    omega
  have hDeval : ∀ x : Fin 9 → Bool, D.eval (row x) = F x := by
    intro x
    let xs := row x
    have hxs10 : xs.length = 10 := hrowLen x
    have hvlt : v.val < 10 := Nat.lt_trans v.isLt (by omega)
    have hselC : (C.wires xs).getD idx false = (pre.foldl step xs).getD idx false := by
      change (C.gates.foldl step xs).getD idx false = _
      rw [← hsplit, List.foldl_append]
      apply hFoldKeep post (pre.foldl step xs) idx
      rw [hFoldLen pre xs, hxs10, hprelen]
      omega
    let m : Bool := if disj = true then x v || (C.wires xs).getD idx false
      else x v && (C.wires xs).getD idx false
    let w0 := pre.foldl step xs
    have hw0len : w0.length = cut := by
      change (pre.foldl step xs).length = cut
      rw [hFoldLen, hxs10, hprelen]
      omega
    have hxget : xs.getD v.val false = x v := by
      change (List.ofFn x ++ [x 0 || x 6]).getD v.val false = x v
      rw [List.getD_append (List.ofFn x) [x 0 || x 6] false v.val (by rw [List.length_ofFn]; exact v.isLt)]
      rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact v.isLt), List.getElem_ofFn]
    have hw0getv : w0.getD v.val false = x v := by
      rw [← hxget]
      exact hFoldKeep pre xs v.val (by omega)
    have hgnewVal : gnew.op.eval (gnew.inputs.map fun i => w0.getD i false) = m := by
      dsimp only [gnew]
      cases hdisj : disj
      · rw [if_neg (by decide)]
        change GateOp.and.eval [w0.getD v.val false, w0.getD idx false] = m
        rw [hAnd2, hw0getv, ← hselC]
        simp [m, hdisj]
      · rw [if_pos rfl]
        change GateOp.or.eval [w0.getD v.val false, w0.getD idx false] = m
        rw [hOr2, hw0getv, ← hselC]
        simp [m, hdisj]
    have hpreSet : pre.foldl step (xs.set v.val m) = w0.set v.val m :=
      hFoldSetComm pre xs v.val m (by omega) hprior
    have hmatch0 : ∀ k, (w0 ++ [m]).getD (rmap k) false = (w0.set v.val m).getD k false := by
      intro k
      by_cases hkv : k = v.val
      · subst hkv
        have hrm : rmap v.val = cut := by simp [rmap]
        rw [hrm, ← hw0len, List.getD_append_right w0 [m] false w0.length le_rfl,
          hGetDSetSelf w0 v.val m (by omega), Nat.sub_self]
        rfl
      · by_cases hkc : k < cut
        · have hrm : rmap k = k := by simp [rmap, hkv, hkc]
          rw [hrm, List.getD_append w0 [m] false k (by omega), hGetDSetNe w0 v.val k m hkv]
        · have hrm : rmap k = k + 1 := by simp [rmap, hkv, hkc]
          rw [hrm, List.getD_eq_default (w0 ++ [m]) false (by rw [List.length_append, hw0len]; simp; omega),
            List.getD_eq_default (w0.set v.val m) false (by rw [List.length_set, hw0len]; omega)]
    have hpres0 : ∀ t k, rmap k = (w0 ++ [m]).length + t ↔ k = (w0.set v.val m).length + t := by
      intro t k
      rw [List.length_append, List.length_set, hw0len]
      simp only [List.length_cons, List.length_nil]
      dsimp only [rmap]
      split_ifs <;> omega
    have hpostMap := hFoldMap rmap post (w0.set v.val m) (w0 ++ [m]) hmatch0 hpres0 C.output
    have hDwires : (D.wires xs) = (post.map (mapGate rmap)).foldl step (w0 ++ [m]) := by
      change (pre ++ [gnew] ++ post.map (mapGate rmap)).foldl step xs = _
      rw [List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
      change (post.map (mapGate rmap)).foldl step (w0 ++ [gnew.op.eval (gnew.inputs.map fun i => w0.getD i false)]) = _
      rw [hgnewVal]
    have hCwires : C.wires (xs.set v.val m) = post.foldl step (w0.set v.val m) := by
      change C.gates.foldl step (xs.set v.val m) = _
      rw [← hsplit, List.foldl_append, hpreSet]
    change (D.wires xs).getD (rmap C.output) false = F x
    rw [hDwires, hpostMap, ← hCwires]
    exact hcorr x
  let isNonNot : Gate → Bool :=
    fun g => GateOp.rec (motive := fun _ => Bool) true true false (fun _ => true) true g.op
  let isNot : Gate → Bool :=
    fun g => GateOp.rec (motive := fun _ => Bool) false false true (fun _ => false) false g.op
  have hNonNotCount := hBinary13 D hfanD hDeval
  change 13 ≤ D.gates.countP isNonNot at hNonNotCount
  have hSplitCount (gs : List Gate) : gs.countP isNonNot + gs.countP isNot = gs.length := by
    induction gs with
    | nil => rfl
    | cons g gs ih =>
      rw [List.countP_cons, List.countP_cons, List.length_cons]
      have hone : (if isNonNot g then 1 else 0) + (if isNot g then 1 else 0) = 1 := by
        cases hop : g.op <;> simp [isNonNot, isNot, hop]
      omega
  have hNotLe1 : D.gates.countP isNot ≤ 1 := by
    have hs := hSplitCount D.gates
    change D.gates.length ≤ 14 at hszD
    omega
  have hMonoFrom (gs : List Gate) (out : ℕ)
      (hf : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
      (hno : ∀ g ∈ gs, isNot g = false) :
      Monotone2 ⟨gs, out⟩ := by
    intro g hg
    change g ∈ gs at hg
    refine ⟨?_, (hf g hg).2⟩
    have hno' := hno g hg
    have hf' := (hf g hg).1
    cases hop : g.op
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; left; trivial
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; right; trivial
    · exfalso
      simp [isNot, hop] at hno'
    · exfalso
      rw [hop] at hf'
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hf'
      rcases hf' with h | h | h <;> cases h
    · exfalso
      rw [hop] at hf'
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hf'
      rcases hf' with h | h | h <;> cases h
  by_cases hc0 : D.gates.countP isNot = 0
  · have hno : ∀ g ∈ D.gates, isNot g = false := by
      intro g hg
      cases hn : isNot g with
      | false => rfl
      | true =>
        have hpos : 0 < D.gates.countP isNot := List.countP_pos_iff.mpr ⟨g, hg, hn⟩
        omega
    have hMonoD : Monotone2 D := hMonoFrom D.gates D.output hfanD hno
    obtain ⟨x, hx⟩ := hMono14 D hMonoD hszD
    exact hx (hDeval x)
  · have hc1 : D.gates.countP isNot = 1 := by omega
    have hDlen14 : D.gates.length = 14 := by
      have hs := hSplitCount D.gates
      change D.gates.length ≤ 14 at hszD
      omega
    have hSplitUnique : ∀ gs : List Gate,
        (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
        gs.countP isNot = 1 →
        ∃ (Ags : List Gate) (gNot : Gate) (Bgs : List Gate),
          gs = Ags ++ [gNot] ++ Bgs ∧ gNot.op = GateOp.not ∧
          (∀ g ∈ Ags, isNot g = false) ∧ (∀ g ∈ Bgs, isNot g = false) := by
      intro gs
      induction gs with
      | nil => intro _ h0; simp at h0
      | cons g gs ih =>
        intro hf hcnt
        cases hop : g.op with
        | not =>
          have hrest0 : gs.countP isNot = 0 := by
            rw [List.countP_cons] at hcnt
            have hn : isNot g = true := by simp [isNot, hop]
            rw [if_pos hn] at hcnt
            omega
          have hno : ∀ h ∈ gs, isNot h = false := by
            intro h hh
            cases hn' : isNot h with
            | false => rfl
            | true =>
              have hpos : 0 < gs.countP isNot := List.countP_pos_iff.mpr ⟨h, hh, hn'⟩
              omega
          exact ⟨[], g, gs, rfl, hop, (fun _ h => False.elim (by cases h)), hno⟩
        | and =>
          have hn : isNot g = false := by simp [isNot, hop]
          rw [List.countP_cons, if_neg (by simp [hn])] at hcnt
          obtain ⟨Ags, gNot, Bgs, heq, hgop, hA, hB⟩ :=
            ih (fun h hh => hf h (List.mem_cons_of_mem g hh)) hcnt
          refine ⟨g :: Ags, gNot, Bgs, by simp [heq], hgop, ?_, hB⟩
          intro h hh
          rcases List.mem_cons.mp hh with rfl | hh'
          · exact hn
          · exact hA h hh'
        | or =>
          have hn : isNot g = false := by simp [isNot, hop]
          rw [List.countP_cons, if_neg (by simp [hn])] at hcnt
          obtain ⟨Ags, gNot, Bgs, heq, hgop, hA, hB⟩ :=
            ih (fun h hh => hf h (List.mem_cons_of_mem g hh)) hcnt
          refine ⟨g :: Ags, gNot, Bgs, by simp [heq], hgop, ?_, hB⟩
          intro h hh
          rcases List.mem_cons.mp hh with rfl | hh'
          · exact hn
          · exact hA h hh'
        | mod _ =>
          exfalso
          have h1 := (hf g List.mem_cons_self).1
          rw [hop] at h1
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
          rcases h1 with h | h | h <;> cases h
        | maj =>
          exfalso
          have h1 := (hf g List.mem_cons_self).1
          rw [hop] at h1
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
          rcases h1 with h | h | h <;> cases h
    obtain ⟨Ags, gNot, Bgs, hDeq, hgNotOp, hAno, hBno⟩ := hSplitUnique D.gates hfanD hc1
    have hABlen : Ags.length + Bgs.length = 13 := by
      have := hDlen14
      rw [hDeq, List.length_append, List.length_append, List.length_singleton] at this
      omega
    have hfanA : ∀ g ∈ Ags, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
      intro g hg
      apply hfanD g
      rw [hDeq, List.mem_append, List.mem_append]
      exact Or.inl (Or.inl hg)
    have hfanB : ∀ g ∈ Bgs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
      intro g hg
      apply hfanD g
      rw [hDeq, List.mem_append, List.mem_append]
      exact Or.inr hg
    have hAlwaysTrueContrad : (∀ xs : List Bool, xs.length = 10 →
        gNot.op.eval (gNot.inputs.map fun j => (Ags.foldl step xs).getD j false) = true) → False := by
      intro htr
      let gTrue : Gate := ⟨GateOp.and, []⟩
      let M : Circuit := ⟨Ags ++ [gTrue] ++ Bgs, D.output⟩
      have hfanM : ∀ g ∈ M.gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
        intro g hg
        change g ∈ Ags ++ [gTrue] ++ Bgs at hg
        rw [List.mem_append, List.mem_append] at hg
        rcases hg with (hg | hg) | hg
        · exact hfanA g hg
        · rw [List.mem_singleton.mp hg]
          refine ⟨by simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; left; rfl, by simp [gTrue]⟩
        · exact hfanB g hg
      have hnoM : ∀ g ∈ M.gates, isNot g = false := by
        intro g hg
        change g ∈ Ags ++ [gTrue] ++ Bgs at hg
        rw [List.mem_append, List.mem_append] at hg
        rcases hg with (hg | hg) | hg
        · exact hAno g hg
        · rw [List.mem_singleton.mp hg]
        · exact hBno g hg
      have hMonoM : Monotone2 M := hMonoFrom M.gates M.output hfanM hnoM
      have hszM : M.size ≤ 14 := by
        change (Ags ++ [gTrue] ++ Bgs).length ≤ 14
        rw [List.length_append, List.length_append, List.length_singleton]
        omega
      obtain ⟨x, hx⟩ := hMono14 M hMonoM hszM
      apply hx
      have hgTrueVal : gTrue.op.eval (gTrue.inputs.map fun j => (Ags.foldl step (row x)).getD j false) = true := rfl
      have hMeq : M.eval (row x) = D.eval (row x) := by
        change (M.wires (row x)).getD D.output false = (D.wires (row x)).getD D.output false
        have hMw : M.wires (row x) = Bgs.foldl step (Ags.foldl step (row x) ++ [true]) := by
          change (Ags ++ [gTrue] ++ Bgs).foldl step (row x) = _
          rw [List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
          change Bgs.foldl step (Ags.foldl step (row x) ++ [gTrue.op.eval _]) = _
          rw [hgTrueVal]
        have hDw : D.wires (row x) = Bgs.foldl step (Ags.foldl step (row x) ++ [true]) := by
          change D.gates.foldl step (row x) = _
          rw [hDeq, List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
          change Bgs.foldl step (Ags.foldl step (row x) ++ [gNot.op.eval _]) = _
          rw [htr (row x) (hrowLen x)]
        rw [hMw, hDw]
      rw [hMeq]
      exact hDeval x
    cases hIn : gNot.inputs with
    | nil =>
      apply hAlwaysTrueContrad
      intro xs _
      rw [hIn, hgNotOp]
      rfl
    | cons u us =>
      by_cases hhi : 10 + Ags.length ≤ u
      · apply hAlwaysTrueContrad
        intro xs hxs
        rw [hIn, hgNotOp, List.map_cons]
        have hdef : (Ags.foldl step xs).getD u false = false :=
          List.getD_eq_default (Ags.foldl step xs) false (by rw [hFoldLen, hxs]; omega)
        change !((Ags.foldl step xs).getD u false) = true
        rw [hdef]
        rfl
      · by_cases h10 : 10 ≤ u
        · let A : Circuit := ⟨Ags, 0⟩
          let B : Circuit := ⟨Bgs, D.output⟩
          have hMonoA : Monotone2 A := hMonoFrom Ags 0 hfanA hAno
          have hMonoB : Monotone2 B := hMonoFrom Bgs D.output hfanB hBno
          have hA1 : 1 ≤ A.size := by change 1 ≤ Ags.length; omega
          have hAB : A.size + B.size ≤ 13 := by change Ags.length + Bgs.length ≤ 13; omega
          have huA : u < 10 + A.size := by change u < 10 + Ags.length; omega
          obtain ⟨x, hx⟩ := hGateNot A B u hMonoA hMonoB hA1 hAB h10 huA
          apply hx
          have heq : B.eval (A.wires (row x) ++ [!(A.wires (row x)).getD u false]) = D.eval (row x) := by
            have hDw : D.wires (row x) = Bgs.foldl step (A.wires (row x) ++ [!(A.wires (row x)).getD u false]) := by
              change D.gates.foldl step (row x) = _
              rw [hDeq, List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
              change Bgs.foldl step (A.wires (row x) ++ [gNot.op.eval (gNot.inputs.map fun j => (A.wires (row x)).getD j false)]) = _
              rw [hIn, hgNotOp, List.map_cons]
              rfl
            change (Bgs.foldl step (A.wires (row x) ++ [!(A.wires (row x)).getD u false])).getD D.output false =
              (D.wires (row x)).getD D.output false
            rw [hDw]
          rw [heq]
          exact hDeval x
        · have hu10 : u < 10 := by omega
          let cutA : ℕ := 10 + Ags.length
          let shiftA : ℕ → ℕ := fun k => if k < 10 then k else k + 1
          let shiftB : ℕ → ℕ := fun k => if k < 10 then k else if k < cutA then k + 1 else if k = cutA then 10 else k
          let M : Circuit := ⟨Ags.map (mapGate shiftA) ++ Bgs.map (mapGate shiftB), shiftB D.output⟩
          have hfanM : ∀ g ∈ M.gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
            intro g hg
            change g ∈ Ags.map (mapGate shiftA) ++ Bgs.map (mapGate shiftB) at hg
            rw [List.mem_append] at hg
            rcases hg with hg | hg
            · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
              exact ⟨(hfanA g0 hg0).1, by simpa [mapGate] using (hfanA g0 hg0).2⟩
            · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
              exact ⟨(hfanB g0 hg0).1, by simpa [mapGate] using (hfanB g0 hg0).2⟩
          have hnoM : ∀ g ∈ M.gates, isNot g = false := by
            intro g hg
            change g ∈ Ags.map (mapGate shiftA) ++ Bgs.map (mapGate shiftB) at hg
            rw [List.mem_append] at hg
            rcases hg with hg | hg
            · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
              exact hAno g0 hg0
            · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
              exact hBno g0 hg0
          have hMonoM : Monotone2 M := hMonoFrom M.gates M.output hfanM hnoM
          have hszM : M.size ≤ 13 := by
            change (Ags.map (mapGate shiftA) ++ Bgs.map (mapGate shiftB)).length ≤ 13
            rw [List.length_append, List.length_map, List.length_map]
            omega
          obtain ⟨x, hx⟩ := hRawNot ⟨u, hu10⟩ M hMonoM hszM
          apply hx
          let xs := row x
          let neg := !(xs.getD u false)
          have hxs10 : xs.length = 10 := hrowLen x
          have hmatchA : ∀ k, (xs ++ [neg]).getD (shiftA k) false = xs.getD k false := by
            intro k
            by_cases hk : k < 10
            · rw [show shiftA k = k from if_pos hk]
              exact List.getD_append xs [neg] false k (by omega)
            · rw [show shiftA k = k + 1 from if_neg hk]
              rw [List.getD_eq_default (xs ++ [neg]) false (by rw [List.length_append, hxs10]; simp; omega),
                List.getD_eq_default xs false (by omega)]
          have hpresA : ∀ t k, shiftA k = (xs ++ [neg]).length + t ↔ k = xs.length + t := by
            intro t k
            rw [List.length_append, hxs10]
            simp only [List.length_cons, List.length_nil]
            dsimp only [shiftA]
            split_ifs <;> omega
          have hwAmap := hFoldMap shiftA Ags xs (xs ++ [neg]) hmatchA hpresA
          let wA := Ags.foldl step xs
          let wAM := (Ags.map (mapGate shiftA)).foldl step (xs ++ [neg])
          have hwAlen : wA.length = cutA := by
            change (Ags.foldl step xs).length = 10 + Ags.length
            rw [hFoldLen, hxs10]
          have hwAMlen : wAM.length = cutA + 1 := by
            change ((Ags.map (mapGate shiftA)).foldl step (xs ++ [neg])).length = 10 + Ags.length + 1
            rw [hFoldLen, List.length_append, List.length_map, hxs10]
            simp only [List.length_cons, List.length_nil]
            omega
          have hnegEq : (wA.getD u false) = xs.getD u false :=
            hFoldKeep Ags xs u (by omega)
          have hwAM10 : wAM.getD 10 false = neg := by
            have h1 := hFoldKeep (Ags.map (mapGate shiftA)) (xs ++ [neg]) 10 (by rw [List.length_append, hxs10]; simp)
            rw [h1, List.getD_append_right xs [neg] false 10 (by omega), hxs10]
            rfl
          have hmatchB : ∀ k, wAM.getD (shiftB k) false = (wA ++ [neg]).getD k false := by
            intro k
            by_cases hk10 : k < 10
            · have hsB : shiftB k = k := by simp [shiftB, hk10]
              have hsA : shiftA k = k := by simp [shiftA, hk10]
              have htmp := hwAmap k
              rw [hsA] at htmp
              rw [hsB, htmp, List.getD_append wA [neg] false k (by omega)]
            · by_cases hkc : k < cutA
              · have hsB : shiftB k = k + 1 := by simp [shiftB, hk10, hkc]
                have hsA : shiftA k = k + 1 := by simp [shiftA, hk10]
                have htmp := hwAmap k
                rw [hsA] at htmp
                rw [hsB, htmp, List.getD_append wA [neg] false k (by omega)]
              · by_cases hke : k = cutA
                · subst hke
                  have hsB : shiftB cutA = 10 := by
                    have hnot10 : ¬ (cutA < 10) := by omega
                    have hnotlt : ¬ (cutA < cutA) := Nat.lt_irrefl cutA
                    simp [shiftB, hnot10, hnotlt]
                  rw [hsB, hwAM10, ← hwAlen, List.getD_append_right wA [neg] false wA.length le_rfl, Nat.sub_self]
                  rfl
                · have hsB : shiftB k = k := by simp [shiftB, hk10, hkc, hke]
                  rw [hsB, List.getD_eq_default wAM false (by rw [hwAMlen]; omega),
                    List.getD_eq_default (wA ++ [neg]) false (by rw [List.length_append, hwAlen]; simp; omega)]
          have hpresB : ∀ t k, shiftB k = wAM.length + t ↔ k = (wA ++ [neg]).length + t := by
            intro t k
            rw [hwAMlen, List.length_append, hwAlen]
            simp only [List.length_cons, List.length_nil]
            dsimp only [shiftB]
            split_ifs <;> omega
          have hwBmap := hFoldMap shiftB Bgs (wA ++ [neg]) wAM hmatchB hpresB D.output
          have hMeval : M.eval (xs ++ [neg]) = D.eval xs := by
            change (M.wires (xs ++ [neg])).getD (shiftB D.output) false = (D.wires xs).getD D.output false
            have hMw : M.wires (xs ++ [neg]) = (Bgs.map (mapGate shiftB)).foldl step wAM := by
              change (Ags.map (mapGate shiftA) ++ Bgs.map (mapGate shiftB)).foldl step (xs ++ [neg]) = _
              rw [List.foldl_append]
            have hDw : D.wires xs = Bgs.foldl step (wA ++ [neg]) := by
              change D.gates.foldl step xs = _
              rw [hDeq, List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
              change Bgs.foldl step (wA ++ [gNot.op.eval (gNot.inputs.map fun j => wA.getD j false)]) = _
              rw [hIn, hgNotOp, List.map_cons]
              change Bgs.foldl step (wA ++ [!(wA.getD u false)]) = _
              rw [hnegEq]
            rw [hMw, hDw, hwBmap]
          change M.eval (xs ++ [!(xs.getD (⟨u, hu10⟩ : Fin 10).val false)]) = F x
          rw [hMeval]
          exact hDeval x
