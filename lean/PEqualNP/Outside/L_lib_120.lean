import Mathlib
import PEqualNP.Defs

-- The same machine decides the complement: relabel its output alphabet through Boolean
-- negation. The output stack holds the same symbol, now read as the negated answer, and no
-- step is added.

namespace PEqualNP.Outside.L_lib_120

open PEqualNP.Library

theorem flip_output (f : List Bool → Bool) (t : ℕ → ℕ)
    (h : ComputableInTime (fun x : List Bool => x) Computability.encodeBool f t) :
    ComputableInTime (fun x : List Bool => x) Computability.encodeBool (fun x => !f x) t := by
  obtain ⟨c, hc⟩ := h
  have hout : ∀ a : List Bool, Turing.TM2OutputsInTime c.tm
      (List.map c.inputAlphabet.invFun a)
      (Option.some (List.map (c.outputAlphabet.trans Equiv.boolNot).invFun
        (Computability.encodeBool (!f a)))) (c.time a.length) := by
    intro a
    have e : (List.map (c.outputAlphabet.trans Equiv.boolNot).invFun
        (Computability.encodeBool (!f a))) =
        List.map c.outputAlphabet.invFun (Computability.encodeBool (f a)) := by
      simp [Computability.encodeBool, Equiv.boolNot]
    rw [e]
    exact c.outputsFun a
  exact ⟨Turing.TM2ComputableInTime.mk
    ⟨c.tm, c.inputAlphabet, c.outputAlphabet.trans Equiv.boolNot⟩ c.time hout, hc⟩

end PEqualNP.Outside.L_lib_120

open PEqualNP.Outside.L_lib_120

theorem PEqualNP.Outside.L_lib_120 : ∀ (t : ℕ → ℕ) (L : Language Bool), L ∈ PEqualNP.Library.DTIME t → Lᶜ ∈ PEqualNP.Library.DTIME t := by
  intro t L hL
  obtain ⟨f, hf, hc⟩ := hL
  refine ⟨fun x => !f x, ?_, flip_output f t hc⟩
  intro a
  show a ∉ L ↔ (!f a) = true
  have h := hf a
  cases hfa : f a
  · rw [hfa] at h
    simp only [Bool.not_false, iff_true]
    intro hm
    exact absurd (h.1 hm) (by simp)
  · rw [hfa] at h
    simp only [Bool.not_true]
    constructor
    · intro hm
      exact absurd (h.2 rfl) hm
    · intro hf'
      exact absurd hf' (by simp)
