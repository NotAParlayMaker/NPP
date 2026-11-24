import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_1791_1
    (hconst : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 13 → ∃ x : Fin 9 → Bool, let v := List.ofFn x ++ [x 0 && x 1]; C.eval (v ++ [true]) ≠ (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5))
    (hpair : ∀ i j : Fin 11, i ≤ j → ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 13 → ∃ x : Fin 9 → Bool, let v := List.ofFn x ++ [x 0 && x 1]; C.eval (v ++ [v.getD i.val false && v.getD j.val false]) ≠ (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) :
    ∀ l : List ℕ, l.length ≤ 2 → ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 13 → ∃ x : Fin 9 → Bool, let v := List.ofFn x ++ [x 0 && x 1]; C.eval (v ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval (l.map (fun k => v.getD k false))]) ≠ (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) := by
  intro l hl C hC hs
  have pair (m n : ℕ) : ∃ x : Fin 9 → Bool, let v := List.ofFn x ++ [x 0 && x 1]; C.eval (v ++ [v.getD m false && v.getD n false]) ≠ (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) := by
    let clamp (k : ℕ) : Fin 11 := ⟨min k 10, by omega⟩
    have get (v : List Bool) (hv : v.length = 10) (k : ℕ) :
        v.getD (clamp k).val false = v.getD k false := by
      by_cases hk : k ≤ 10
      · simp [clamp, Nat.min_eq_left hk]
      · have hbound : 10 ≤ k := by omega
        simp [clamp, hv, hbound]
    by_cases ho : clamp m ≤ clamp n
    · obtain ⟨x, hx⟩ := hpair (clamp m) (clamp n) ho C hC hs
      exact ⟨x, by simpa only [get (List.ofFn x ++ [x 0 && x 1]) (by simp) m, get (List.ofFn x ++ [x 0 && x 1]) (by simp) n] using hx⟩
    · obtain ⟨x, hx⟩ := hpair (clamp n) (clamp m) (le_of_not_ge ho) C hC hs
      exact ⟨x, by simpa only [get (List.ofFn x ++ [x 0 && x 1]) (by simp) m, get (List.ofFn x ++ [x 0 && x 1]) (by simp) n, Bool.and_comm] using hx⟩
  cases l with
  | nil => exact hconst C hC hs
  | cons m l =>
    cases l with
    | nil =>
      obtain ⟨x, hx⟩ := pair m m
      exact ⟨x, by simpa [PEqualNP.CircuitLowerBounds.GateOp.eval] using hx⟩
    | cons n rest =>
      have he : rest = [] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at hl; omega)
      subst rest
      obtain ⟨x, hx⟩ := pair m n
      exact ⟨x, by simpa [PEqualNP.CircuitLowerBounds.GateOp.eval] using hx⟩
