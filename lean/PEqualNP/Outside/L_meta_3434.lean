import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3434

open PEqualNP.CircuitLowerBounds

lemma fold_rename (rho : ℕ → ℕ) (L : ℕ) (hfix : ∀ i, L ≤ i → rho i = i) :
    ∀ (gs : List Gate) (w w' : List Bool), w.length = w'.length → L ≤ w.length →
      (∀ i, i < L → rho i < L ∨ w.length + gs.length ≤ rho i) →
      (∀ i, w'.getD (rho i) false = w.getD i false) →
      ∀ i, ((gs.map (fun g : Gate => ({ op := g.op, inputs := g.inputs.map rho } : Gate))).foldl
          (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w').getD (rho i) false
        = (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD i
            false := by
  intro gs
  induction gs with
  | nil => intro w w' _ _ _ hread i; simpa using hread i
  | cons g gs ih =>
    intro w w' hlen hL hsafe hread
    simp only [List.map_cons, List.foldl_cons, List.map_map]
    have hval : (g.inputs.map ((fun i => w'.getD i false) ∘ rho)) =
        g.inputs.map (fun i => w.getD i false) :=
      List.map_congr_left fun i _ => hread i
    rw [hval]
    apply ih
    · simp [hlen]
    · simp only [List.length_append, List.length_singleton]; omega
    · intro i hi
      rcases hsafe i hi with h | h
      · exact Or.inl h
      · right
        simp only [List.length_append, List.length_cons, List.length_nil] at h ⊢
        omega
    · intro i
      by_cases hi : i < L
      · have h1 : (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).getD i false =
            w.getD i false := List.getD_append _ _ _ _ (by omega)
        rw [h1, ← hread i]
        rcases hsafe i hi with h | h
        · exact List.getD_append _ _ _ _ (by omega)
        · simp only [List.length_cons] at h
          rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]
      · rw [hfix i (by omega)]
        have hr := hread i
        rw [hfix i (by omega)] at hr
        rcases Nat.lt_trichotomy i w.length with h | h | h
        · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ h, hr]
        · rw [List.getD_append_right _ _ _ _ (by omega),
            List.getD_append_right _ _ _ _ (by omega), hlen]
        · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

end PEqualNP.Outside.L_meta_3434

theorem PEqualNP.Outside.L_meta_3434 : ∀ (x1 : ℕ → ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : List Bool), x3.length = x4.length → (∀ (x6 : ℕ), x3.length ≤ x6 → x1 x6 = x6) → (∀ x7 < x3.length, x1 x7 < x3.length ∨ x3.length + x2.size ≤ x1 x7) → (∀ (x8 : ℕ), x4.getD (x1 x8) Bool.false = x3.getD x8 Bool.false) → { gates := List.map (fun (x9 : PEqualNP.CircuitLowerBounds.Gate) => { op := x9.op, inputs := List.map x1 x9.inputs : PEqualNP.CircuitLowerBounds.Gate }) x2.gates, output := x1 x2.output : PEqualNP.CircuitLowerBounds.Circuit }.eval x4 = x2.eval x3 := by
  intro rho C xs ys hlen hfix hsafe hread
  exact PEqualNP.Outside.L_meta_3434.fold_rename rho xs.length hfix C.gates xs ys hlen
    (Nat.le_refl _) hsafe hread C.output
