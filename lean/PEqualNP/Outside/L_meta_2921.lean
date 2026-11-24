import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2921

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def ρ (f : Fin 9 → Fin 9) (i : ℕ) : ℕ :=
  if h : i < 9 then (f ⟨i, h⟩).val else i

lemma foldl_remap (f : Fin 9 → Fin 9) (gs : List Gate) :
    ∀ (w3 w4 : List Bool),
      w3.length = w4.length →
      9 ≤ w4.length →
      (∀ i : ℕ, w3.getD (ρ f i) false = w4.getD i false) →
      ∀ i : ℕ,
        ((gs.map fun g => Gate.mk g.op (g.inputs.map (ρ f))).foldl step w3).getD (ρ f i) false =
        (gs.foldl step w4).getD i false := by
  induction gs with
  | nil =>
    intro w3 w4 _ _ h0 i
    exact h0 i
  | cons g gs ih =>
    intro w3 w4 hlen h9 h0 i
    simp only [List.map_cons, List.foldl_cons]
    have hbit :
        g.op.eval ((g.inputs.map (ρ f)).map fun j => w3.getD j false) =
        g.op.eval (g.inputs.map fun j => w4.getD j false) := by
      congr 1
      rw [List.map_map]
      exact List.map_congr_left fun j _ => h0 j
    apply ih
    · simp [step, hlen]
    · simp [step]; omega
    · intro k
      simp only [step, hbit]
      by_cases hk : k < 9
      · have hr : ρ f k < 9 := by simp [ρ, hk]
        rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
        exact h0 k
      · have hr : ρ f k = k := by simp [ρ, hk]
        rw [hr]
        rcases lt_trichotomy k w4.length with hlt | heq | hgt
        · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ hlt]
          have := h0 k
          rwa [hr] at this
        · subst heq
          rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (le_refl _)]
          simp [hlen]
        · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

end PEqualNP.Outside.L_meta_2921

theorem PEqualNP.Outside.L_meta_2921 : ∀ (x1 : Fin (9 : ℕ) → Fin (9 : ℕ)) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : List Bool), x3.length = x4.length → (9 : ℕ) ≤ x4.length → (∀ (x7 : ℕ), x3.getD (if x8 : x7 < (9 : ℕ) then ↑(x1 (⟨x7, x8⟩ : Fin (9 : ℕ))) else x7) Bool.false = x4.getD x7 Bool.false) → { gates := List.map (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => { op := x8.op, inputs := List.map (fun (x9 : ℕ) => if x10 : x9 < (9 : ℕ) then ↑(x1 (⟨x9, x10⟩ : Fin (9 : ℕ))) else x9) x8.inputs : PEqualNP.CircuitLowerBounds.Gate }) x2.gates, output := if x8 : x2.output < (9 : ℕ) then ↑(x1 (⟨x2.output, x8⟩ : Fin (9 : ℕ))) else x2.output : PEqualNP.CircuitLowerBounds.Circuit }.eval x3 = x2.eval x4 := by
  intro x1 x2 x3 x4 hlen h9 h0
  exact PEqualNP.Outside.L_meta_2921.foldl_remap x1 x2.gates x3 x4 hlen h9 h0 x2.output
