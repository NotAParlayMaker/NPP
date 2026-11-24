import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4518

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def rel (f : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map f⟩

theorem getD_snoc (w : List Bool) (a : Bool) (i : ℕ) :
    (w ++ [a]).getD i false =
      if i < w.length then w.getD i false else if i = w.length then a else false := by
  split_ifs with h1 h2
  · exact List.getD_append _ _ _ _ h1
  · subst h2; simp
  · rw [List.getD_eq_default]; simp; omega

theorem run_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [step]
    omega

theorem run_keep (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp [step]; omega)]
    exact List.getD_append _ _ _ _ h

theorem sim (gs : List Gate) : ∀ (w w' : List Bool) (f : ℕ → ℕ),
    (∀ i, w.getD i false = w'.getD (f i) false) →
    (∀ i < w.length, f i < w'.length) →
    (∀ i, w.length ≤ i → f i + w.length = i + w'.length) →
    ∀ i, (gs.foldl step w).getD i false = ((gs.map (rel f)).foldl step w').getD (f i) false := by
  induction gs with
  | nil => intro w w' f h1 _ _ i; exact h1 i
  | cons g gs ih =>
    intro w w' f h1 h2 h3
    have ha : (rel f g).op.eval ((rel f g).inputs.map fun i => w'.getD i false) =
        g.op.eval (g.inputs.map fun i => w.getD i false) := by
      simp only [rel, List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      exact (h1 i).symm
    simp only [List.map_cons, List.foldl_cons]
    apply ih
    · intro i
      simp only [step, getD_snoc, ha]
      by_cases hi : i < w.length
      · have := h2 i hi
        rw [if_pos hi, if_pos this, h1 i]
      · have := h3 i (by omega)
        by_cases he : i = w.length
        · rw [if_neg hi, if_pos he, if_neg (by omega), if_pos (by omega)]
        · rw [if_neg hi, if_neg he, if_neg (by omega), if_neg (by omega)]
    · intro i hi
      simp only [step, List.length_append, List.length_singleton] at hi ⊢
      by_cases h : i < w.length
      · have := h2 i h; omega
      · have := h3 i (by omega); omega
    · intro i hi
      simp only [step, List.length_append, List.length_singleton] at hi ⊢
      have := h3 i (by omega); omega

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

end PEqualNP.Outside.L_meta_4518

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_4518 in
theorem PEqualNP.Outside.L_meta_4518 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : List PEqualNP.CircuitLowerBounds.Gate) (x4 : PEqualNP.CircuitLowerBounds.Gate), x1.gates = x2 ++ x4 :: x3 → PEqualNP.MetaComplexity.FanInTwo x1 → (∀ x7 ∈ x4.inputs, x7 < (9 : ℕ)) → ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x8 ∧ x8.size = x1.size ∧ PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x8 = PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 ∧ ∀ (x9 : Fin (9 : ℕ) → Bool), (x8.wires (List.ofFn x9)).getD (9 : ℕ) Bool.false = x4.op.eval (List.map (fun (x10 : ℕ) => (List.ofFn x9).getD x10 Bool.false) x4.inputs) := by
  intro C x2 x3 g hC hF hg
  let s2 : ℕ → ℕ := fun i => if i < 9 then i else i + 1
  let p := 9 + x2.length
  let s3 : ℕ → ℕ := fun i => if i < 9 then i else if i < p then i + 1 else if i = p then 9 else i
  refine ⟨⟨g :: (x2.map (rel s2) ++ x3.map (rel s3)), s3 C.output⟩, ?_, ?_, ?_, ?_⟩
  · intro h hh
    simp only [List.mem_cons, List.mem_append, List.mem_map] at hh
    have hF' := fun h' (m : h' ∈ C.gates) => hF h' m
    rw [hC] at hF'
    rcases hh with rfl | ⟨h', m, rfl⟩ | ⟨h', m, rfl⟩
    · exact hF' _ (by simp)
    · have := hF' h' (by simp [m]); simpa [rel] using this
    · have := hF' h' (by simp [m]); simpa [rel] using this
  · simp [Circuit.size, hC]; omega
  · funext x9
    simp only [circuitFun, Circuit.eval, wires_eq, hC, List.foldl_append, List.foldl_cons]
    set x := List.ofFn x9 with hxdef
    have hx : x.length = 9 := by simp [x]
    set v := g.op.eval (g.inputs.map fun i => x.getD i false) with hv
    have hgv : g.op.eval (g.inputs.map fun i => (x2.foldl step x).getD i false) = v := by
      rw [hv]; congr 1
      apply List.map_congr_left
      intro i hi
      exact run_keep _ _ _ (by rw [hx]; exact hg i hi)
    have hA : (x2.foldl step x).length = p := by rw [run_length, hx]
    have hB0 : (step x g) = x ++ [v] := rfl
    have hBl : ((x2.map (rel s2)).foldl step (x ++ [v])).length = p + 1 := by
      rw [run_length]; simp [hx, p]; omega
    have P2 := sim x2 x (x ++ [v]) s2
      (by
        intro i
        simp only [getD_snoc, s2, hx]
        by_cases h : i < 9
        · simp only [h, if_true]
        · simp only [h, if_false]
          rw [List.getD_eq_default _ _ (by omega)]
          split_ifs <;> first | rfl | omega)
      (by intro i hi; rw [hx] at hi; simp only [s2, List.length_append, hx, List.length_singleton]; split_ifs <;> omega)
      (by intro i hi; rw [hx] at hi; simp only [s2, List.length_append, hx, List.length_singleton]; split_ifs <;> omega)
    have P3 := sim x3 (step (x2.foldl step x) g) ((x2.map (rel s2)).foldl step (x ++ [v])) s3
      (by
        intro i
        simp only [step, getD_snoc, hgv, hA]
        by_cases h9 : i < 9
        · rw [if_pos (by omega), P2 i]; simp only [s2, s3, if_pos h9]
        · by_cases hp : i < p
          · rw [if_pos hp, P2 i]; simp only [s2, s3, if_neg h9, if_pos hp]
          · by_cases he : i = p
            · rw [if_neg hp, if_pos he]
              simp only [s3, if_neg h9, if_neg hp, if_pos he]
              rw [run_keep _ _ _ (by simp [hx]), getD_snoc, if_neg (by omega), if_pos (by omega)]
            · rw [if_neg hp, if_neg he]
              simp only [s3, if_neg h9, if_neg hp, if_neg he]
              rw [List.getD_eq_default _ _ (by omega)])
      (by
        intro i hi
        simp only [step, List.length_append, List.length_singleton, hA, hBl] at hi ⊢
        simp only [s3]; split_ifs <;> omega)
      (by
        intro i hi
        simp only [step, List.length_append, List.length_singleton, hA, hBl] at hi ⊢
        simp only [s3]; split_ifs <;> omega)
    exact (P3 C.output).symm
  · intro x9
    simp only [wires_eq, List.foldl_cons, List.foldl_append]
    have hx : (List.ofFn x9).length = 9 := by simp
    rw [run_keep _ _ _ (by rw [run_length]; simp [step]; omega), run_keep _ _ _ (by simp [step])]
    simp [step]
