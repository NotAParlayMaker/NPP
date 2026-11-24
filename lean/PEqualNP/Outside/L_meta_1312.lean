import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1312

open PEqualNP.CircuitLowerBounds

-- a maximum of numbers at most 1 is at most 1
theorem foldr_max_le (l : List ℕ) (h : ∀ x ∈ l, x ≤ 1) : l.foldr max 0 ≤ 1 := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.foldr_cons]
    have ha : a ≤ 1 := h a (by simp)
    have ht : t.foldr max 0 ≤ 1 := ih (fun x hx => h x (by simp [hx]))
    exact max_le ha ht

-- a lookup with default 0 in a list of numbers at most 1 is at most 1
theorem getD_le (d : List ℕ) (h : ∀ x ∈ d, x ≤ 1) (i : ℕ) : d.getD i 0 ≤ 1 := by
  by_cases hi : i < d.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact h _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (by omega)]
    omega

-- an OR gate over degrees at most 1 has degree at most 1
theorem gate_le (g : Gate) (hg : g.op = GateOp.or) (d : List ℕ) (h : ∀ x ∈ d, x ≤ 1) :
    g.lineDegree d ≤ 1 := by
  have hne : ¬ (g.op = GateOp.and) := by rw [hg]; intro e; cases e
  unfold Gate.lineDegree
  simp only [hne, ↓reduceIte]
  apply foldr_max_le
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨i, _, rfl⟩ := hx
  exact getD_le d h i

-- the invariant along the fold
theorem fold_le (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.or) (d : List ℕ)
    (h : ∀ x ∈ d, x ≤ 1) :
    ∀ x ∈ gs.foldl (fun d g => d ++ [g.lineDegree d]) d, x ≤ 1 := by
  induction gs generalizing d with
  | nil => simpa using h
  | cons g t ih =>
    rw [List.foldl_cons]
    apply ih (fun g' hg' => hgs g' (by simp [hg']))
    intro x hx
    rw [List.mem_append] at hx
    rcases hx with hx | hx
    · exact h x hx
    · rw [List.mem_singleton] at hx
      rw [hx]
      exact gate_le g (hgs g (by simp)) d h

end PEqualNP.Outside.L_meta_1312

theorem PEqualNP.Outside.L_meta_1312 : ∀ (n : ℕ) (marked : Finset ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.or) → PEqualNP.CircuitLowerBounds.HasLineDegree n marked C 1 := by
  intro n marked C hC
  show (C.lineDegrees n marked).getD C.output 0 ≤ 1
  apply PEqualNP.Outside.L_meta_1312.getD_le
  unfold PEqualNP.CircuitLowerBounds.Circuit.lineDegrees
  apply PEqualNP.Outside.L_meta_1312.fold_le C.gates hC
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨i, _, rfl⟩ := hx
  split <;> omega
