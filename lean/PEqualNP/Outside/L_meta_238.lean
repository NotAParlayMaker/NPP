import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside
open MetaComplexity

theorem L_meta_238 : ∀ s : ℕ, HasBinarySize 2 (fun x : Fin 2 → Bool => xor (x 0) (x 1)) s ↔ 1 ≤ s := by
  intro s
  constructor
  · rintro ⟨⟨gs,o⟩, hs, hf⟩
    by_contra! h
    have empty : gs = [] := by
      change gs.length ≤ s at hs
      apply List.length_eq_zero_iff.mp
      omega
    subst gs
    change ∀ x : Fin 2 → Bool, (List.ofFn x).getD o false = xor (x 0) (x 1) at hf
    cases o with
    | zero => simpa using hf ![false,true]
    | succ o =>
      cases o with
      | zero => simpa using hf ![true,false]
      | succ o => simpa using hf ![true,false]
  · intro hs
    refine ⟨⟨[⟨xor,0,1⟩],2⟩, hs, ?_⟩
    decide

end PEqualNP.Outside
