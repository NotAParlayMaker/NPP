import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2859_aux

open PEqualNP.CircuitLowerBounds PEqualNP.CircuitMoves

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def ren (n m p : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (eraseRedirect n m p)⟩

theorem fold_len (gs : List Gate) :
    ∀ w : List Bool, (gs.foldl step w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp
  | cons g gs ih =>
    intro w
    rw [List.foldl_cons, ih]
    simp [step]
    omega

theorem inv (n m p : ℕ) (W T : List Bool) (v : Bool) (hW : W.length = n + m) (hp : p < n + m)
    (hv : W.getD p false = v) (i : ℕ) :
    (W ++ v :: T).getD i false = (W ++ T).getD (eraseRedirect n m p i) false := by
  unfold eraseRedirect
  simp only [List.getD_eq_getElem?_getD] at hv ⊢
  by_cases h1 : i = n + m
  · rw [if_pos h1, List.getElem?_append_right (by omega), List.getElem?_append_left (by omega), hv]
    simp [h1, hW]
  · rw [if_neg h1]
    by_cases h2 : n + m < i
    · rw [if_pos h2, List.getElem?_append_right (by omega), List.getElem?_append_right (by omega)]
      have h3 : i - W.length = (i - 1 - W.length) + 1 := by omega
      rw [h3]
      simp
    · rw [if_neg h2, List.getElem?_append_left (by omega), List.getElem?_append_left (by omega)]

theorem fold_pre (B : List Gate) (W : List Bool) (v : Bool) :
    ∀ T : List Bool, ∃ T2 : List Bool, B.foldl step (W ++ v :: T) = W ++ v :: T2 := by
  induction B with
  | nil => intro T; exact ⟨T, rfl⟩
  | cons g B ih =>
    intro T
    obtain ⟨T2, h⟩ := ih (T ++ [g.op.eval (g.inputs.map fun i => (W ++ v :: T).getD i false)])
    exact ⟨T2, by rw [List.foldl_cons, ← h]; simp [step]⟩

theorem fold_pair (n m p : ℕ) (W : List Bool) (v : Bool) (hW : W.length = n + m) (hp : p < n + m)
    (hv : W.getD p false = v) (B : List Gate) :
    ∀ T : List Bool, ∃ T2 : List Bool, B.foldl step (W ++ v :: T) = W ++ v :: T2 ∧
      (B.map (ren n m p)).foldl step (W ++ T) = W ++ T2 := by
  induction B with
  | nil => intro T; exact ⟨T, rfl, rfl⟩
  | cons g B ih =>
    intro T
    obtain ⟨T2, h1, h2⟩ := ih (T ++ [g.op.eval (g.inputs.map fun i => (W ++ v :: T).getD i false)])
    refine ⟨T2, ?_, ?_⟩
    · rw [List.foldl_cons, ← h1]
      simp [step]
    · rw [List.map_cons, List.foldl_cons, ← h2]
      congr 1
      simp only [step, ren, List.map_map]
      have h3 : ((fun i => (W ++ T).getD i false) ∘ eraseRedirect n m p) =
          fun i => (W ++ v :: T).getD i false := by
        funext i
        exact (inv n m p W T v hW hp hv i).symm
      rw [h3]
      simp

end PEqualNP.Outside.L_meta_2859_aux

open PEqualNP.CircuitLowerBounds PEqualNP.CircuitMoves PEqualNP.Outside.L_meta_2859_aux in
theorem PEqualNP.Outside.L_meta_2859 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (m p : ℕ), PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack n C → m < C.gates.length → p < n + m → PEqualNP.MetaComplexity.Monotone2 (PEqualNP.CircuitMoves.eraseGate n C m p) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack n (PEqualNP.CircuitMoves.eraseGate n C m p) ∧ (PEqualNP.CircuitMoves.eraseGate n C m p).size + 1 = C.size ∧ ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD p false = (C.wires (List.ofFn x)).getD (n + m) false → (PEqualNP.CircuitMoves.eraseGate n C m p).eval (List.ofFn x) = C.eval (List.ofFn x) := by
  rintro n ⟨gs, out⟩ m p hM hRB hm hp
  replace hm : m < gs.length := hm
  have hE : eraseGate n ⟨gs, out⟩ m p =
      ⟨gs.take m ++ (gs.drop (m + 1)).map (ren n m p), eraseRedirect n m p out⟩ := by
    unfold eraseGate
    rw [if_pos hm]
    rfl
  rw [hE]
  have hga : ∀ j (hj : j < gs.length),
      PEqualNP.MetaComplexity.NestedCover.gateAt ⟨gs, out⟩ j = gs[j] := by
    intro j hj
    simp [PEqualNP.MetaComplexity.NestedCover.gateAt, hj]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_map] at hg
    rcases hg with hg | ⟨a, ha, rfl⟩
    · exact hM g (List.mem_of_mem_take hg)
    · have := hM a (List.mem_of_mem_drop ha)
      simpa [ren] using this
  · intro j hj i hi
    simp only [List.length_append, List.length_take, List.length_map, List.length_drop] at hj
    by_cases hjm : j < m
    · have hL : (gs.take m ++ (gs.drop (m + 1)).map (ren n m p))[j]? = some gs[j] := by
        rw [List.getElem?_append_left (by simp; omega)]
        simp [hjm]
      have h3 : PEqualNP.MetaComplexity.NestedCover.gateAt
          ⟨gs.take m ++ (gs.drop (m + 1)).map (ren n m p), eraseRedirect n m p out⟩ j = gs[j] := by
        simp only [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD, hL]
        rfl
      rw [h3] at hi
      exact hRB j (lt_trans hjm hm) i (by rw [hga j (lt_trans hjm hm)]; exact hi)
    · have hj1 : j + 1 < gs.length := by omega
      have hL : (gs.take m ++ (gs.drop (m + 1)).map (ren n m p))[j]? =
          some (ren n m p gs[j + 1]) := by
        rw [List.getElem?_append_right (by simp; omega)]
        have h4 : m + 1 + (j - m) = j + 1 := by omega
        have h5 : min m gs.length = m := by omega
        simp [h4, h5, hj1]
      have h3 : PEqualNP.MetaComplexity.NestedCover.gateAt
          ⟨gs.take m ++ (gs.drop (m + 1)).map (ren n m p), eraseRedirect n m p out⟩ j =
          ren n m p gs[j + 1] := by
        simp only [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD, hL]
        rfl
      rw [h3] at hi
      simp only [ren, List.mem_map] at hi
      obtain ⟨a, ha, rfl⟩ := hi
      have h6 := hRB (j + 1) hj1 a (by rw [hga _ hj1]; exact ha)
      unfold eraseRedirect
      split_ifs <;> omega
  · simp only [Circuit.size, List.length_append, List.length_take, List.length_map,
      List.length_drop]
    omega
  · intro x hx
    have hdec : gs = gs.take m ++ gs[m] :: gs.drop (m + 1) := by
      rw [← List.drop_eq_getElem_cons hm, List.take_append_drop]
    have hW : ((gs.take m).foldl step (List.ofFn x)).length = n + m := by
      rw [fold_len]
      simp
      omega
    have hfull : gs.foldl step (List.ofFn x) =
        (gs.drop (m + 1)).foldl step ((gs.take m).foldl step (List.ofFn x) ++
          gs[m].op.eval (gs[m].inputs.map fun i =>
            ((gs.take m).foldl step (List.ofFn x)).getD i false) :: []) := by
      conv_lhs => rw [hdec]
      rw [List.foldl_append, List.foldl_cons]
      rfl
    have hv : ((gs.take m).foldl step (List.ofFn x)).getD p false =
          gs[m].op.eval (gs[m].inputs.map fun i =>
            ((gs.take m).foldl step (List.ofFn x)).getD i false) := by
      obtain ⟨T2, h⟩ := fold_pre (gs.drop (m + 1)) ((gs.take m).foldl step (List.ofFn x))
        (gs[m].op.eval (gs[m].inputs.map fun i =>
            ((gs.take m).foldl step (List.ofFn x)).getD i false)) []
      have hx2 : (gs.foldl step (List.ofFn x)).getD p false =
          (gs.foldl step (List.ofFn x)).getD (n + m) false := hx
      rw [hfull, h] at hx2
      simp only [List.getD_eq_getElem?_getD] at hx2 ⊢
      rw [List.getElem?_append_left (by omega), List.getElem?_append_right (by omega)] at hx2
      simpa [hW] using hx2
    obtain ⟨T2, h1, h2⟩ := fold_pair n m p _ _ hW hp hv (gs.drop (m + 1)) []
    show ((gs.take m ++ (gs.drop (m + 1)).map (ren n m p)).foldl step (List.ofFn x)).getD
        (eraseRedirect n m p out) false = (gs.foldl step (List.ofFn x)).getD out false
    rw [hfull, h1, List.foldl_append]
    rw [List.append_nil] at h2
    rw [h2]
    exact (inv n m p _ T2 _ hW hp hv out).symm
