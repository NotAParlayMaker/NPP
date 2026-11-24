import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2859

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.CircuitMoves

/-- One evaluation step: append the value of gate `g` on the wires `w`. -/
def st (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

/-- A gate with every read renamed by `eraseRedirect n m p`. -/
def ren (n m p : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (eraseRedirect n m p)⟩

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl st x := rfl

theorem getD_append_left (A T : List Bool) (i : ℕ) (h : i < A.length) :
    (A ++ T).getD i false = A.getD i false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left h, ← List.getD_eq_getElem?_getD]

theorem foldl_length (R : List Gate) (A : List Bool) :
    (R.foldl st A).length = A.length + R.length := by
  induction R generalizing A with
  | nil => simp
  | cons g R ih =>
    rw [List.foldl_cons, ih]
    simp only [st, List.length_append, List.length_cons, List.length_nil]
    omega

theorem foldl_prefix (R : List Gate) (A : List Bool) : ∃ T, R.foldl st A = A ++ T := by
  induction R generalizing A with
  | nil => exact ⟨[], by simp⟩
  | cons g R ih =>
    obtain ⟨T, hT⟩ := ih (st A g)
    refine ⟨g.op.eval (g.inputs.map fun i => A.getD i false) :: T, ?_⟩
    rw [List.foldl_cons, hT]
    simp [st]

/-- Reading through the redirect in the list with entry `n + m` removed gives the old value. -/
theorem getD_redirect (A : List Bool) (n m p i : ℕ) (hk : n + m < A.length) (hp : p < n + m)
    (hA : A.getD p false = A.getD (n + m) false) :
    (A.eraseIdx (n + m)).getD (eraseRedirect n m p i) false = A.getD i false := by
  unfold eraseRedirect
  split_ifs with h1 h2
  · subst h1
    rw [List.getD_eq_getElem?_getD, List.getElem?_eraseIdx_of_lt hp,
      ← List.getD_eq_getElem?_getD, hA]
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eraseIdx_of_ge (by omega),
      Nat.sub_add_cancel (by omega), ← List.getD_eq_getElem?_getD]
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eraseIdx_of_lt (by omega),
      ← List.getD_eq_getElem?_getD]

/-- Evaluating the renamed gates from the shortened wires gives the shortened wires. -/
theorem foldl_rel (n m p : ℕ) (hp : p < n + m) (R : List Gate) (A : List Bool)
    (hk : n + m < A.length) (hA : A.getD p false = A.getD (n + m) false) :
    (R.map (ren n m p)).foldl st (A.eraseIdx (n + m)) = (R.foldl st A).eraseIdx (n + m) := by
  induction R generalizing A with
  | nil => rfl
  | cons g R ih =>
    rw [List.map_cons, List.foldl_cons, List.foldl_cons]
    have hstep : st (A.eraseIdx (n + m)) (ren n m p g) = (st A g).eraseIdx (n + m) := by
      show A.eraseIdx (n + m) ++ [g.op.eval ((g.inputs.map (eraseRedirect n m p)).map
          fun i => (A.eraseIdx (n + m)).getD i false)] =
        (A ++ [g.op.eval (g.inputs.map fun i => A.getD i false)]).eraseIdx (n + m)
      rw [List.eraseIdx_append_of_lt_length hk, List.map_map]
      congr 3
      apply List.map_congr_left
      intro i _
      exact getD_redirect A n m p i hk hp hA
    rw [hstep]
    apply ih
    · simp only [st, List.length_append, List.length_cons, List.length_nil]
      omega
    · simp only [st]
      rw [getD_append_left _ _ _ (by omega), getD_append_left _ _ _ hk]
      exact hA

end PEqualNP.Outside.L_meta_2859

open PEqualNP.Outside.L_meta_2859 in
theorem PEqualNP.Outside.L_meta_2859 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (m p : ℕ), PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack n C → m < C.gates.length → p < n + m → PEqualNP.MetaComplexity.Monotone2 (PEqualNP.CircuitMoves.eraseGate n C m p) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack n (PEqualNP.CircuitMoves.eraseGate n C m p) ∧ (PEqualNP.CircuitMoves.eraseGate n C m p).size + 1 = C.size ∧ ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD p false = (C.wires (List.ofFn x)).getD (n + m) false → (PEqualNP.CircuitMoves.eraseGate n C m p).eval (List.ofFn x) = C.eval (List.ofFn x) := by
  intro n C m p hM hR hm hp
  set E := PEqualNP.CircuitMoves.eraseGate n C m p with hEdef
  have hG : E.gates = C.gates.take m ++ (C.gates.drop (m + 1)).map (ren n m p) := by
    rw [hEdef]
    unfold PEqualNP.CircuitMoves.eraseGate
    rw [if_pos hm]
    rfl
  have hO : E.output = PEqualNP.CircuitMoves.eraseRedirect n m p C.output := by
    rw [hEdef]
    unfold PEqualNP.CircuitMoves.eraseGate
    rw [if_pos hm]
  have hlenT : (C.gates.take m).length = m := by simp; omega
  have hlen : E.gates.length = C.gates.length - 1 := by rw [hG]; simp; omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g hg
    rw [hG] at hg
    rcases List.mem_append.1 hg with h | h
    · exact hM g (List.mem_of_mem_take h)
    · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 h
      have := hM g0 (List.mem_of_mem_drop hg0)
      simpa [ren] using this
  · intro j hj i hi
    have hj' : j < C.gates.length - 1 := hlen ▸ hj
    unfold PEqualNP.MetaComplexity.NestedCover.gateAt at hi
    rw [List.getD_eq_getElem _ _ hj] at hi
    simp only [hG] at hi
    by_cases hjm : j < m
    · rw [List.getElem_append_left (by omega), List.getElem_take] at hi
      have hjC : j < C.gates.length := by omega
      exact hR j hjC i (by
        unfold PEqualNP.MetaComplexity.NestedCover.gateAt
        rw [List.getD_eq_getElem _ _ hjC]
        exact hi)
    · rw [List.getElem_append_right (by omega), List.getElem_map, List.getElem_drop] at hi
      simp only [ren, List.mem_map] at hi
      obtain ⟨i0, hi0, rfl⟩ := hi
      have hjC : m + 1 + (j - (C.gates.take m).length) < C.gates.length := by
        rw [hlenT]; omega
      have := hR _ hjC i0 (by
        unfold PEqualNP.MetaComplexity.NestedCover.gateAt
        rw [List.getD_eq_getElem _ _ hjC]
        exact hi0)
      rw [hlenT] at this
      unfold PEqualNP.CircuitMoves.eraseRedirect
      split_ifs <;> omega
  · show E.gates.length + 1 = C.gates.length
    rw [hlen]
    omega
  · intro x hx
    have hsplit : C.gates = C.gates.take m ++ C.gates[m] :: C.gates.drop (m + 1) := by
      rw [← List.drop_eq_getElem_cons hm, List.take_append_drop]
    set W0 := (C.gates.take m).foldl st (List.ofFn x) with hW0
    have hW0len : W0.length = n + m := by
      rw [hW0, foldl_length, List.length_ofFn, hlenT]
    have hWC : C.wires (List.ofFn x) = (C.gates.drop (m + 1)).foldl st (st W0 C.gates[m]) := by
      rw [wires_eq]
      conv_lhs => rw [hsplit]
      rw [List.foldl_append, List.foldl_cons]
    have hWC' : E.wires (List.ofFn x) = ((C.gates.drop (m + 1)).map (ren n m p)).foldl st W0 := by
      rw [wires_eq, hG, List.foldl_append]
    have hk0 : n + m < (st W0 C.gates[m]).length := by
      simp only [st, List.length_append, List.length_cons, List.length_nil]
      omega
    have hA0e : (st W0 C.gates[m]).eraseIdx (n + m) = W0 := by
      simp only [st]
      rw [List.eraseIdx_append_of_length_le (by omega)]
      simp [hW0len]
    have hA0 : (st W0 C.gates[m]).getD p false = (st W0 C.gates[m]).getD (n + m) false := by
      obtain ⟨T, hT⟩ := foldl_prefix (C.gates.drop (m + 1)) (st W0 C.gates[m])
      rw [hWC, hT] at hx
      rwa [getD_append_left _ _ _ (by omega), getD_append_left _ _ _ hk0] at hx
    have hrel := foldl_rel n m p hp (C.gates.drop (m + 1)) (st W0 C.gates[m]) hk0 hA0
    rw [hA0e] at hrel
    have hWlen : n + m < (C.wires (List.ofFn x)).length := by
      rw [wires_eq, foldl_length, List.length_ofFn]
      omega
    unfold PEqualNP.CircuitLowerBounds.Circuit.eval
    rw [hWC', hrel, ← hWC, hO]
    exact getD_redirect _ n m p C.output hWlen hp hx