import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Push
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2852_aux

open PEqualNP.CircuitLowerBounds

def stepW (W : List Bool) (g : Gate) : List Bool :=
  W ++ [g.op.eval (g.inputs.map fun i => W.getD i false)]

def run (gs : List Gate) (W : List Bool) : List Bool := gs.foldl stepW W

theorem run_append (gs gs' : List Gate) (W : List Bool) :
    run (gs ++ gs') W = run gs' (run gs W) := by
  simp [run, List.foldl_append]

theorem run_prefix (gs : List Gate) : ∀ W : List Bool,
    ∃ t : List Bool, run gs W = W ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro W; exact ⟨[], by simp [run], rfl⟩
  | cons g gs ih =>
    intro W
    obtain ⟨t, ht, hl⟩ := ih (stepW W g)
    refine ⟨g.op.eval (g.inputs.map fun i => W.getD i false) :: t, ?_, by simp [hl]⟩
    have e : run (g :: gs) W = run gs (stepW W g) := rfl
    rw [e, ht]; simp [stepW]

theorem run_length (gs : List Gate) (W : List Bool) :
    (run gs W).length = W.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := run_prefix gs W
  rw [ht]; simp [hl]

theorem run_getD_lt (gs : List Gate) (W : List Bool) (i : ℕ) (h : i < W.length) :
    (run gs W).getD i false = W.getD i false := by
  obtain ⟨t, ht, _⟩ := run_prefix gs W
  rw [ht]; simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem run_getD_ge (gs : List Gate) (W : List Bool) (i : ℕ) (h : W.length + gs.length ≤ i) :
    (run gs W).getD i false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none]
  · rfl
  · rw [run_length]; exact h

theorem run_snoc (gs : List Gate) (g : Gate) (W : List Bool) :
    run (gs ++ [g]) W = stepW (run gs W) g := by
  rw [run_append]; rfl

def gateAt (gates : List Gate) (i : ℕ) : Gate := gates.getD i ⟨GateOp.or, []⟩

theorem old_gate (gates : List Gate) (x' : List Bool) (i : ℕ) (hi : i < gates.length) :
    (run gates x').getD (x'.length + i) false =
      (gateAt gates i).op.eval ((gateAt gates i).inputs.map fun q => (run (gates.take i) x').getD q false) := by
  have e1 : gates = gates.take (i + 1) ++ gates.drop (i + 1) := (List.take_append_drop _ _).symm
  have e2 : gates.take (i + 1) = gates.take i ++ [gateAt gates i] := by
    unfold gateAt
    rw [List.getD_eq_getElem _ _ hi, List.take_add_one, List.getElem?_eq_getElem hi]
    rfl
  have hlen : (run (gates.take i) x').length = x'.length + i := by
    rw [run_length, List.length_take]; congr 1; omega
  conv => lhs; rw [e1, run_append]
  rw [run_getD_lt _ _ _ (by rw [run_length, List.length_take]; omega), e2, run_snoc]
  unfold stepW
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hlen]
  simp

theorem old_take (gates : List Gate) (x' : List Bool) (i q : ℕ) (hi : i ≤ gates.length) :
    (run (gates.take i) x').getD q false = if q < x'.length + i then (run gates x').getD q false else false := by
  have hlen : (run (gates.take i) x').length = x'.length + i := by
    rw [run_length, List.length_take]; congr 1; omega
  split_ifs with hq
  · rw [show run gates x' = run (gates.drop i) (run (gates.take i) x') by
      rw [← run_append, List.take_append_drop]]
    rw [run_getD_lt (gates.drop i) _ q (by omega)]
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl

theorem gate_val (gates : List Gate) (X : List Bool) (i : ℕ) (hi : i < gates.length)
    (hrb : ∀ q ∈ (gateAt gates i).inputs, q < X.length + i) :
    (run gates X).getD (X.length + i) false =
      (gateAt gates i).op.eval ((gateAt gates i).inputs.map fun q => (run gates X).getD q false) := by
  rw [old_gate gates X i hi]
  congr 1
  apply List.map_congr_left
  intro q hq
  rw [old_take gates X i q hi.le, if_pos (hrb q hq)]

theorem gateAt_mem (gates : List Gate) (i : ℕ) (hi : i < gates.length) : gateAt gates i ∈ gates := by
  unfold gateAt; rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi

theorem gateAt_set (gates : List Gate) (g : ℕ) (G' : Gate) (j : ℕ) (hg : g < gates.length) :
    gateAt (gates.set g G') j = if j = g then G' else gateAt gates j := by
  unfold gateAt
  split_ifs with h
  · subst h; rw [List.getD_eq_getElem _ _ (by simpa using hg)]; simp
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_set, Ne.symm h, if_false]

theorem eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (l l' : List Bool)
    (hl : l'.length = l.length)
    (h : ∀ k < l.length, l'.getD k false = true → l.getD k false = true) :
    op.eval l' = true → op.eval l = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, id]
    intro h' a ha
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp ha
    have := h k hk (by rw [List.getD_eq_getElem _ _ (by omega)]; exact h' _ (List.getElem_mem _))
    rwa [List.getD_eq_getElem _ _ hk] at this
  · simp only [GateOp.eval, List.any_eq_true, id]
    rintro ⟨a, ha, hat⟩
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp ha
    have := h k (by omega) (by rw [List.getD_eq_getElem _ _ hk]; exact hat)
    rw [List.getD_eq_getElem _ _ (by omega)] at this
    exact ⟨_, List.getElem_mem _, this⟩

theorem wires_le (n : ℕ) (gs gs' : List Gate) (X X' : List Bool) (hX : X.length = n)
    (hX' : X'.length = n) (hlen : gs'.length = gs.length)
    (hin : ∀ q < n, X'.getD q false = true → X.getD q false = true)
    (hstep : ∀ j < gs.length,
      (∀ q < n + j, (run gs' X').getD q false = true → (run gs X).getD q false = true) →
      (run gs' X').getD (n + j) false = true → (run gs X).getD (n + j) false = true) :
    ∀ q, (run gs' X').getD q false = true → (run gs X).getD q false = true := by
  intro q
  induction q using Nat.strong_induction_on with
  | _ q ih =>
  by_cases h1 : q < n
  · rw [run_getD_lt _ _ _ (by omega), run_getD_lt _ _ _ (by omega)]; exact hin q h1
  by_cases h2 : q < n + gs.length
  · obtain ⟨j, rfl⟩ : ∃ j, q = n + j := ⟨q - n, by omega⟩
    exact hstep j (by omega) (fun q' hq' => ih q' hq')
  · intro h
    rw [run_getD_ge _ _ _ (by rw [hX']; omega)] at h
    exact absurd h (by simp)

theorem getD_map (l : List ℕ) (f : ℕ → Bool) (k : ℕ) (hk : k < l.length) :
    (l.map f).getD k false = f (l[k]) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hk)]; simp

theorem step_same (n : ℕ) (gs gs' : List Gate) (X X' : List Bool) (hX : X.length = n)
    (hX' : X'.length = n) (j : ℕ) (hj : j < gs.length) (hj' : j < gs'.length)
    (hgate : gateAt gs' j = gateAt gs j)
    (hop : (gateAt gs j).op = GateOp.and ∨ (gateAt gs j).op = GateOp.or)
    (hrb : ∀ i ∈ (gateAt gs j).inputs, i < n + j)
    (ih : ∀ q < n + j, (run gs' X').getD q false = true → (run gs X).getD q false = true) :
    (run gs' X').getD (n + j) false = true → (run gs X).getD (n + j) false = true := by
  have e1 := gate_val gs' X' j hj' (by rw [hX', hgate]; exact hrb)
  have e2 := gate_val gs X j hj (by rw [hX]; exact hrb)
  rw [hX'] at e1; rw [hX] at e2
  rw [e1, e2, hgate]
  apply eval_mono _ hop _ _ (by simp)
  intro k hk h
  simp only [List.length_map] at hk
  rw [getD_map _ _ _ hk] at h ⊢
  exact ih _ (hrb _ (List.getElem_mem hk)) h

theorem exists_min (n : ℕ) (f : (Fin n → Bool) → Bool) : ∀ x, f x = true →
    ∃ y : Fin n → Bool, (∀ i, y i = true → x i = true) ∧ f y = true ∧
      ∀ z : Fin n → Bool, (∀ i, z i = true → y i = true) → z ≠ y → f z = false := by
  intro x
  induction h : (Finset.univ.filter fun i => x i = true).card using Nat.strong_induction_on
    generalizing x with
  | _ k ih =>
  intro hx
  by_cases hm : ∀ z : Fin n → Bool, (∀ i, z i = true → x i = true) → z ≠ x → f z = false
  · exact ⟨x, fun _ h => h, hx, hm⟩
  · push_neg at hm
    obtain ⟨z, hzx, hne, hz⟩ := hm
    have hz' : f z = true := by simpa using hz
    have hlt : (Finset.univ.filter fun i => z i = true).card < k := by
      rw [← h]
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_subset_ne]
      constructor
      · intro i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hzx i
      · intro heq
        apply hne
        funext i
        have := congrArg (i ∈ ·) heq
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, eq_iff_iff] at this
        cases hzi : z i <;> cases hxi : x i <;> simp_all
    obtain ⟨y, hyz, hy, hmin⟩ := ih _ hlt z rfl hz'
    exact ⟨y, fun i h => hzx i (hyz i h), hy, hmin⟩

theorem ofFn_getD (n : ℕ) (x : Fin n → Bool) (q : ℕ) (hq : q < n) :
    (List.ofFn x).getD q false = x ⟨q, hq⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa using hq)]; simp

/-- The statement of L-meta-2853 is refutable: the narrowing rewrite always keeps the model,
the size, the monotone bound and the minimal-input test. -/
theorem refute : ¬ (∃ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (g b c d : ℕ), (PEqualNP.TopForm.IsAO2 n C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack n C ∧ g < C.gates.length ∧ b < 2 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.getD b 0 = c ∧ d < n + g ∧ (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨C.gates, d⟩ (List.ofFn x) = true → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨C.gates, c⟩ (List.ofFn x) = true)) ∧
  ¬ (PEqualNP.TopForm.IsAO2 n (⟨C.gates.set g ⟨(PEqualNP.MetaComplexity.NestedCover.gateAt C g).op, (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.set b d⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit) ∧ (⟨C.gates.set g ⟨(PEqualNP.MetaComplexity.NestedCover.gateAt C g).op, (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.set b d⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit).size = C.size ∧ (∀ x : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n (⟨C.gates.set g ⟨(PEqualNP.MetaComplexity.NestedCover.gateAt C g).op, (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.set b d⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit) x = true → PEqualNP.MetaComplexity.circuitFun n C x = true) ∧ (PEqualNP.MetaComplexity.circuitFun n (⟨C.gates.set g ⟨(PEqualNP.MetaComplexity.NestedCover.gateAt C g).op, (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.set b d⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit) = PEqualNP.MetaComplexity.circuitFun n C ↔ (∀ x : Fin n → Bool, (PEqualNP.MetaComplexity.circuitFun n C x = true ∧ ∀ y : Fin n → Bool, (∀ i, y i = true → x i = true) → y ≠ x → PEqualNP.MetaComplexity.circuitFun n C y = false) → PEqualNP.MetaComplexity.circuitFun n (⟨C.gates.set g ⟨(PEqualNP.MetaComplexity.NestedCover.gateAt C g).op, (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.set b d⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit) x = true)))) := by
  rintro ⟨n, C, g, b, c, d, ⟨hAO, hRB, hg, hb, hc, hd, himp⟩, hneg⟩
  apply hneg
  obtain ⟨hAnd, -, hTwo⟩ := hAO
  have hRB' : ∀ j < C.gates.length, ∀ i ∈ (gateAt C.gates j).inputs, i < n + j := hRB
  set G : Gate := gateAt C.gates g with hGdef
  have hGG : PEqualNP.MetaComplexity.NestedCover.gateAt C g = G := rfl
  rw [hGG] at hc ⊢
  set G' : Gate := ⟨G.op, G.inputs.set b d⟩ with hG'def
  set gs' := C.gates.set g G' with hgs'
  have hGmem : G ∈ C.gates := gateAt_mem _ _ hg
  have hGop : G.op = GateOp.and ∨ G.op = GateOp.or := hAnd G hGmem
  have hG2 : G.inputs.length = 2 := hTwo G hGmem
  have hlen' : gs'.length = C.gates.length := by simp [gs']
  have hop' : ∀ j < gs'.length, (gateAt gs' j).op = GateOp.and ∨ (gateAt gs' j).op = GateOp.or := by
    intro j hj
    rw [gateAt_set _ _ _ _ hg]
    split_ifs with hjg
    · exact hGop
    · exact hAnd _ (gateAt_mem _ _ (by omega))
  have hrb' : ∀ j < gs'.length, ∀ i ∈ (gateAt gs' j).inputs, i < n + j := by
    intro j hj i hi
    rw [gateAt_set _ _ _ _ hg] at hi
    split_ifs at hi with hjg
    · subst hjg
      rcases List.mem_or_eq_of_mem_set hi with h | h
      · exact hRB' _ hg i h
      · omega
    · exact hRB' j (by omega) i hi
  -- the narrowed circuit lies below the old one, wire by wire
  have key : ∀ x : Fin n → Bool, ∀ q, (run gs' (List.ofFn x)).getD q false = true →
      (run C.gates (List.ofFn x)).getD q false = true := by
    intro x
    apply wires_le n C.gates gs' _ _ (List.length_ofFn) (List.length_ofFn) hlen'
    · intro q _ h; exact h
    · intro j hj ih h
      by_cases hjg : j = g
      · rw [hjg] at hj ih h ⊢
        have e1 := gate_val gs' (List.ofFn x) g (by omega)
          (by rw [List.length_ofFn]; exact hrb' g (by omega))
        have e2 := gate_val C.gates (List.ofFn x) g hj
          (by rw [List.length_ofFn]; exact hRB' g hj)
        rw [List.length_ofFn] at e1 e2
        have hgs : gateAt gs' g = G' := by rw [gateAt_set _ _ _ _ hg, if_pos rfl]
        rw [e1, hgs] at h
        rw [e2]
        have hlenm : (G'.inputs.map fun q => (run gs' (List.ofFn x)).getD q false).length =
            (G.inputs.map fun q => (run C.gates (List.ofFn x)).getD q false).length := by
          simp [G']
        refine eval_mono G.op hGop _ _ hlenm ?_ h
        intro k hk h'
        simp only [List.length_map] at hk
        have hk' : k < G'.inputs.length := by simp [G']; exact hk
        rw [getD_map _ _ _ hk'] at h'
        rw [getD_map _ _ _ hk]
        by_cases hkb : k = b
        · subst hkb
          have e3 : G'.inputs[k] = d := by simp [G']
          rw [e3] at h'
          have hd' := ih d hd h'
          have := himp x hd'
          have hck : G.inputs[k] = c := by
            rw [← hc, List.getD_eq_getElem _ _ hk]
          rw [hck]; exact this
        · have e3 : G'.inputs[k] = G.inputs[k] := by
            simp [G', Ne.symm hkb]
          rw [e3] at h'
          exact ih _ (hRB' g hj _ (List.getElem_mem hk)) h'
      · exact step_same n C.gates gs' _ _ (List.length_ofFn) (List.length_ofFn) j hj
          (by omega) (by rw [gateAt_set _ _ _ _ hg, if_neg hjg])
          (hAnd _ (gateAt_mem _ _ hj)) (hRB' j hj) ih h
  -- the narrowed circuit is monotone
  have mono : ∀ x y : Fin n → Bool, (∀ i, x i = true → y i = true) → ∀ q,
      (run gs' (List.ofFn x)).getD q false = true → (run gs' (List.ofFn y)).getD q false = true := by
    intro x y hxy
    apply wires_le n gs' gs' _ _ (List.length_ofFn) (List.length_ofFn) rfl
    · intro q hq h
      rw [ofFn_getD _ _ _ hq] at h ⊢
      exact hxy _ h
    · intro j hj ih
      exact step_same n gs' gs' _ _ (List.length_ofFn) (List.length_ofFn) j hj hj rfl
        (hop' j hj) (hrb' j hj) ih
  refine ⟨⟨?_, hrb', ?_⟩, by simp [Circuit.size, gs'], ?_, ?_⟩
  · intro g'' hm
    rcases List.mem_or_eq_of_mem_set hm with h | h
    · exact hAnd _ h
    · rw [h]; exact hGop
  · intro g'' hm
    rcases List.mem_or_eq_of_mem_set hm with h | h
    · exact hTwo _ h
    · rw [h]; simp [G', hG2]
  · intro x h
    exact key x _ h
  · constructor
    · intro heq x hx
      rw [heq]; exact hx.1
    · intro hmin
      funext x
      apply Bool.eq_iff_iff.mpr
      constructor
      · intro h; exact key x _ h
      · intro h
        obtain ⟨y, hyx, hy, hymin⟩ := exists_min n (PEqualNP.MetaComplexity.circuitFun n C) x h
        exact mono y x hyx _ (hmin y ⟨hy, hymin⟩)

end PEqualNP.Outside.L_meta_2852_aux

theorem PEqualNP.Outside.L_meta_2852 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (g b c d : ℕ), (PEqualNP.TopForm.IsAO2 n C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack n C ∧ g < C.gates.length ∧ b < 2 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.getD b 0 = c ∧ d < n + g ∧ (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨C.gates, d⟩ (List.ofFn x) = true → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨C.gates, c⟩ (List.ofFn x) = true)) →
  PEqualNP.TopForm.IsAO2 n (⟨C.gates.set g ⟨(PEqualNP.MetaComplexity.NestedCover.gateAt C g).op, (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.set b d⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit) ∧ (⟨C.gates.set g ⟨(PEqualNP.MetaComplexity.NestedCover.gateAt C g).op, (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.set b d⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit).size = C.size ∧ (∀ x : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n (⟨C.gates.set g ⟨(PEqualNP.MetaComplexity.NestedCover.gateAt C g).op, (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.set b d⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit) x = true → PEqualNP.MetaComplexity.circuitFun n C x = true) ∧ (PEqualNP.MetaComplexity.circuitFun n (⟨C.gates.set g ⟨(PEqualNP.MetaComplexity.NestedCover.gateAt C g).op, (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.set b d⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit) = PEqualNP.MetaComplexity.circuitFun n C ↔ (∀ x : Fin n → Bool, (PEqualNP.MetaComplexity.circuitFun n C x = true ∧ ∀ y : Fin n → Bool, (∀ i, y i = true → x i = true) → y ≠ x → PEqualNP.MetaComplexity.circuitFun n C y = false) → PEqualNP.MetaComplexity.circuitFun n (⟨C.gates.set g ⟨(PEqualNP.MetaComplexity.NestedCover.gateAt C g).op, (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.set b d⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit) x = true)) := by
  have h := PEqualNP.Outside.L_meta_2852_aux.refute
  push_neg at h
  exact h
