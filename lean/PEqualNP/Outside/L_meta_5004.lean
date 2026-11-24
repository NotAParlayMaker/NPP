import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5004_aux

open PEqualNP.CircuitLowerBounds

def stepW (acc : List Bool) (g : Gate) : List Bool :=
  acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]

def reGate (ρ : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map ρ⟩

lemma getD_rel {m : ℕ} (ρ : ℕ → ℕ) (hρ1 : ∀ k < m, ρ k < m) (hρ2 : ∀ k, m ≤ k → ρ k = k)
    (W y T : List Bool) (hW : W.length = m) (hy : y.length = m)
    (hv : ∀ k, W.getD (ρ k) false = y.getD k false)
    (k : ℕ) : (W ++ T).getD (ρ k) false = (y ++ T).getD k false := by
  by_cases h : k < m
  · have := hρ1 k h
    rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega), hv k]
  · rw [hρ2 k (by omega)]
    rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
    congr 1
    omega

lemma fold_rel {m : ℕ} (ρ : ℕ → ℕ) (hρ1 : ∀ k < m, ρ k < m) (hρ2 : ∀ k, m ≤ k → ρ k = k)
    (W y : List Bool) (hW : W.length = m) (hy : y.length = m)
    (hv : ∀ k, W.getD (ρ k) false = y.getD k false)
    (gs : List Gate) : ∀ T : List Bool, ∃ R : List Bool,
      (gs.map (reGate ρ)).foldl stepW (W ++ T) = W ++ R ∧
      gs.foldl stepW (y ++ T) = y ++ R := by
  induction gs with
  | nil => intro T; exact ⟨T, rfl, rfl⟩
  | cons g gs ih =>
    intro T
    have hm : (g.inputs.map ρ).map (fun i => (W ++ T).getD i false)
        = g.inputs.map (fun i => (y ++ T).getD i false) := by
      rw [List.map_map]
      exact List.map_congr_left (fun i _ => getD_rel ρ hρ1 hρ2 W y T hW hy hv i)
    have e1 : stepW (W ++ T) (reGate ρ g)
        = W ++ (T ++ [g.op.eval (g.inputs.map fun i => (y ++ T).getD i false)]) := by
      show (W ++ T) ++ [g.op.eval ((g.inputs.map ρ).map fun i => (W ++ T).getD i false)] = _
      rw [hm, List.append_assoc]
    have e2 : stepW (y ++ T) g
        = y ++ (T ++ [g.op.eval (g.inputs.map fun i => (y ++ T).getD i false)]) := by
      show (y ++ T) ++ _ = _
      rw [List.append_assoc]
    obtain ⟨R, h1, h2⟩ := ih (T ++ [g.op.eval (g.inputs.map fun i => (y ++ T).getD i false)])
    refine ⟨R, ?_, ?_⟩
    · rw [List.map_cons, List.foldl_cons, e1, h1]
    · rw [List.foldl_cons, e2, h2]

end PEqualNP.Outside.L_meta_5004_aux

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_5004_aux in
theorem PEqualNP.Outside.L_meta_5004 : ∀ (x1 : ℕ) (x2 : ℕ → ℕ), (∀ x3 < x1, x2 x3 < x1) → (∀ (x4 : ℕ), x1 ≤ x4 → x2 x4 = x4) → ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x5 → ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x7 ∧ x7.size = x5.size ∧ ∀ (x8 x9 : List Bool), x8.length = x1 → x9.length = x1 → (∀ (x12 : ℕ), x8.getD (x2 x12) Bool.false = x9.getD x12 Bool.false) → x7.eval x8 = x5.eval x9 := by
  intro n ρ h1 h2 C hC
  refine ⟨⟨C.gates.map (reGate ρ), ρ C.output⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_map] at hg
    obtain ⟨g', hg', rfl⟩ := hg
    have := hC g' hg'
    simpa [reGate] using this
  · simp [Circuit.size]
  · intro W y hW hy hv
    obtain ⟨R, e1, e2⟩ := fold_rel ρ h1 h2 W y hW hy hv C.gates []
    simp only [List.append_nil] at e1 e2
    show (List.foldl stepW _ _).getD _ false = (List.foldl stepW _ _).getD _ false
    rw [e1, e2, getD_rel ρ h1 h2 W y R hW hy hv]
