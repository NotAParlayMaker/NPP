import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_241 :
    ∀ n s : ℕ, PEqualNP.MetaComplexity.HasBinarySize n (fun _ : Fin n → Bool => false) s := by
  intro n s
  refine ⟨{ gates := [], output := n }, Nat.zero_le s, ?_⟩
  intro x
  change (List.ofFn x).getD n false = false
  exact List.getD_eq_default (List.ofFn x) false (by simp only [List.length_ofFn, Nat.le_refl])
