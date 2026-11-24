import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Choose
import Mathlib.Tactic.SplitIfs
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1464 : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (i0 : Fin m),
    3 ≤ (S i0).card → (∀ i : Fin m, i ≠ i0 → (S i ∩ S i0).card ≤ 1) →
    ∃ (r : Fin n → Fin n → Prop) (f : Fin m → Fin n), (∀ a b : Fin n, r a b → ¬ r b a) ∧
      ∀ i : Fin m, i ≠ i0 → f i ∈ S i0 ∧ f i ∉ S i ∧ ∀ y ∈ S i ∩ S i0, r (f i) y := by
  classical
  intro n m S i0 hlarge hsmall
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := Finset.two_lt_card_iff.mp hlarge
  let p : Fin n → Fin n := fun y => if y = a then c else if y = c then b else a
  have mem (y : Fin n) : p y ∈ S i0 := by
    unfold p
    split_ifs <;> assumption
  have no_two_cycle (y : Fin n) : p (p y) ≠ y := by
    by_cases hya : y = a
    · subst y
      simp [p, hac.symm, hab.symm]
    · by_cases hyc : y = c
      · subst y
        simp [p, hac.symm, hab.symm, hbc, hac]
      · have hcy : c ≠ y := fun h => hyc h.symm
        simp [p, hya, hyc, hcy]
  have different (y : Fin n) : p y ≠ y := by
    intro h
    exact no_two_cycle y ((congrArg p h).trans h)
  have witness (i : Fin m) : ∃ x : Fin n, i ≠ i0 →
      x ∈ S i0 ∧ x ∉ S i ∧ ∀ y ∈ S i ∩ S i0, x = p y := by
    by_cases hi : i = i0
    · exact ⟨a, fun h => (h hi).elim⟩
    · by_cases nonempty : (S i ∩ S i0).Nonempty
      · obtain ⟨y, hy⟩ := nonempty
        have unique {z : Fin n} (hz : z ∈ S i ∩ S i0) : z = y :=
          (Finset.card_le_one_iff.mp (hsmall i hi)) hz hy
        refine ⟨p y, fun _ => ⟨mem y, ?_, ?_⟩⟩
        · intro h
          exact different y (unique (Finset.mem_inter.mpr ⟨h, mem y⟩))
        · intro z hz
          rw [unique hz]
      · refine ⟨a, fun _ => ⟨ha, ?_, ?_⟩⟩
        · intro h
          exact nonempty ⟨a, Finset.mem_inter.mpr ⟨h, ha⟩⟩
        · intro y hy
          exact (nonempty ⟨y, hy⟩).elim
  choose f hf using witness
  refine ⟨fun x y => x = p y, f, ?_, hf⟩
  intro x y hxy hyx
  exact no_two_cycle y ((congrArg p hxy).symm.trans hyx.symm)
