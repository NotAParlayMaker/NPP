import PEqualNP.Defs

namespace PEqualNP.Outside
open MetaComplexity

theorem L_meta_241 : ∀ n s : ℕ, HasBinarySize n (fun _ : Fin n → Bool => false) s := by
  intro n s
  refine ⟨⟨[], n⟩, Nat.zero_le s, ?_⟩
  intro x
  change (List.ofFn x).getD n false = false
  simp

end PEqualNP.Outside
