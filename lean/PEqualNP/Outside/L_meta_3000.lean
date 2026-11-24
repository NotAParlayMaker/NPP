import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_3000 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3], (∀ (x5 : Fin x2), Fintype.card { x6 : Fin x2 // x3 x6 x5 } = x1 + (1 : ℕ)) → (∀ (x6 x7 : Fin x2), x6 ≠ x7 → ∃! x9 : Fin x2, x3 x6 x9 ∧ x3 x7 x9) → ∀ (x7 : Finset (Fin x2)), x7.card ≤ x1 → ∀ x9 ∉ x7, ∃ (x11 : Fin x2), x3 x11 x9 ∧ ∀ x12 ∈ x7, ¬x3 x11 x12 := by
  classical
  intro q N I _ hl hu Y hY l hlY
  by_contra hcon
  have hcov : ∀ p : Fin N, I p l → ∃ m ∈ Y, I p m := by
    intro p hp
    by_contra h
    exact hcon ⟨p, hp, fun m hm hI => h ⟨m, hm, hI⟩⟩
  have hP : (Finset.univ.filter (fun p : Fin N => I p l)).card = q + 1 := by
    rw [← hl l, Fintype.card_subtype]
  have key : ∀ p ∈ Finset.univ.filter (fun p : Fin N => I p l), ∃ m ∈ Y, I p m :=
    fun p hp => hcov p (Finset.mem_filter.mp hp).2
  choose f hf using key
  have hle := Finset.card_le_card_of_injOn (s := (Finset.univ.filter (fun p : Fin N => I p l)).attach)
    (t := Y) (fun p => f p.1 p.2) (fun p _ => (hf p.1 p.2).1) (by
      intro a _ b _ hab
      by_contra hne
      have hne' : a.1 ≠ b.1 := fun h => hne (Subtype.ext h)
      obtain ⟨m, _, huniq⟩ := hu a.1 b.1 hne'
      have h1 := huniq l ⟨(Finset.mem_filter.mp a.2).2, (Finset.mem_filter.mp b.2).2⟩
      have hab' : f a.1 a.2 = f b.1 b.2 := hab
      have h2 := huniq (f a.1 a.2) ⟨(hf a.1 a.2).2, by rw [hab']; exact (hf b.1 b.2).2⟩
      have e : f a.1 a.2 = l := h2.trans h1.symm
      exact hlY (e ▸ (hf a.1 a.2).1))
  rw [Finset.card_attach] at hle
  omega
