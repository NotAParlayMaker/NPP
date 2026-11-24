import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_4067 : let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); have x2 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x2 : Finset (Fin (13 : ℕ))) => {x3 : Fin (13 : ℕ) | ∀ x4 ∈ x2, ¬x1 x4 x3}; have x3 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x3 : Finset (Fin (13 : ℕ))) => {x4 : Fin (13 : ℕ) | ∀ x5 ∈ x3, ¬x1 x4 x5}; have x4 : Finset (Fin (13 : ℕ)) → Prop := fun (x4 : Finset (Fin (13 : ℕ))) => ∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x4 | x1 x6 x5}.card ≤ (2 : ℕ); have x5 : Finset (Fin (13 : ℕ)) → Prop := fun (x5 : Finset (Fin (13 : ℕ))) => ∀ (x6 : Fin (13 : ℕ)), (Finset.filter (x1 x6) x5).card ≤ (2 : ℕ); (∀ (x6 : Finset (Fin (13 : ℕ))), x6.card = (4 : ℕ) → x5 (x2 x6)) ∧ ∀ (x6 : Finset (Fin (13 : ℕ))), x6.card = (4 : ℕ) → x4 (x3 x6) := by
  intro x1
  dsimp only
  have key1 : ∀ x a b c : Fin 13, x1 x a → x1 x b → x1 x c → a ≠ b → a ≠ c → b ≠ c →
      (Finset.univ.filter fun y => ¬ x1 y a ∧ ¬ x1 y b ∧ ¬ x1 y c).card ≤ 3 := by
    simp only [x1]
    decide
  have key2 : ∀ l p q r : Fin 13, x1 p l → x1 q l → x1 r l → p ≠ q → p ≠ r → q ≠ r →
      (Finset.univ.filter fun m => ¬ x1 p m ∧ ¬ x1 q m ∧ ¬ x1 r m).card ≤ 3 := by
    simp only [x1]
    decide
  refine ⟨?_, ?_⟩
  · intro S hS x
    by_contra h
    push Not at h
    obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.mp h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb hc
    have hsub : S ⊆ Finset.univ.filter fun y => ¬ x1 y a ∧ ¬ x1 y b ∧ ¬ x1 y c := by
      intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨ha.1 y hy, hb.1 y hy, hc.1 y hy⟩
    have h1 := Finset.card_le_card hsub
    have h2 := key1 x a b c ha.2 hb.2 hc.2 hab hac hbc
    omega
  · intro T hT l
    by_contra h
    push Not at h
    obtain ⟨p, hp, q, hq, r, hr, hpq, hpr, hqr⟩ := Finset.two_lt_card.mp h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp hq hr
    have hsub : T ⊆ Finset.univ.filter fun m => ¬ x1 p m ∧ ¬ x1 q m ∧ ¬ x1 r m := by
      intro m hm
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hp.1 m hm, hq.1 m hm, hr.1 m hm⟩
    have h1 := Finset.card_le_card hsub
    have h2 := key2 l p q r hp.2 hq.2 hr.2 hpq hpr hqr
    omega
