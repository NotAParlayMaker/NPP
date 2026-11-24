import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_4777 : ∀ (x1 : List (ℕ × ℕ)) (x2 : (Fin (14 : ℕ) → Bool) → Bool), (x1.all fun (x3 : ℕ × ℕ) => Decidable.decide (x3.1 < x3.2)) = Bool.true → (∀ (x4 x5 : Fin (14 : ℕ) → Bool), (∀ (x6 : Fin (14 : ℕ)), x4 x6 = Bool.true → x5 x6 = Bool.true) → x2 x4 = Bool.true → x2 x5 = Bool.true) → (∀ (x5 : Fin (14 : ℕ) → Bool), ((∃ (x6 : Fin (14 : ℕ)) (x7 : Fin (14 : ℕ)), (↑x6, ↑x7) ∈ x1 ∧ x5 x6 = Bool.true ∧ x5 x7 = Bool.true) ∧ ∀ (x6 : Fin (14 : ℕ)), x5 x6 = Bool.true → ¬∃ (x8 : Fin (14 : ℕ)) (x9 : Fin (14 : ℕ)), (↑x8, ↑x9) ∈ x1 ∧ Function.update x5 x6 Bool.false x8 = Bool.true ∧ Function.update x5 x6 Bool.false x9 = Bool.true) → x5 (0 : Fin (14 : ℕ)) = Bool.false ∨ x5 (7 : Fin (14 : ℕ)) = Bool.false → (x2 x5 = Bool.true ↔ ∃ (x8 : Fin (14 : ℕ)) (x9 : Fin (14 : ℕ)), (↑x8, ↑x9) ∈ x1 ∧ x5 x8 = Bool.true ∧ x5 x9 = Bool.true)) → ∀ (x6 : Fin (14 : ℕ) → Bool), (∃ (x7 : Fin (14 : ℕ)) (x8 : Fin (14 : ℕ)), (↑x7, ↑x8) ∈ x1 ∧ (x7 ≠ (0 : Fin (14 : ℕ)) ∨ x8 ≠ (7 : Fin (14 : ℕ))) ∧ x6 x7 = Bool.true ∧ x6 x8 = Bool.true) → x2 x6 = Bool.true := by
  intro E f hlt hmono hmin x ⟨a, b, hab, hne, hxa, hxb⟩
  have hord : ∀ p ∈ E, p.1 < p.2 := by
    intro p hp
    simpa using List.all_eq_true.mp hlt p hp
  have hab' : (a : ℕ) < b := hord _ hab
  obtain ⟨y, hy⟩ : ∃ y : Fin 14 → Bool, y = fun i => decide (i = a ∨ i = b) := ⟨_, rfl⟩
  have hyi : ∀ i, y i = true ↔ (i = a ∨ i = b) := by
    intro i; subst hy; simp
  have hya : y a = true := (hyi a).mpr (Or.inl rfl)
  have hyb : y b = true := (hyi b).mpr (Or.inr rfl)
  have hminy : ∀ i, y i = true → ¬∃ (c : Fin 14) (d : Fin 14), ((c : ℕ), (d : ℕ)) ∈ E ∧
      Function.update y i false c = true ∧ Function.update y i false d = true := by
    intro i hi ⟨c, d, hcd, hc, hd⟩
    have hcd' : (c : ℕ) < d := hord _ hcd
    have hc' : c ≠ i ∧ (c = a ∨ c = b) := by
      by_cases h : c = i
      · subst h; simp at hc
      · rw [Function.update_of_ne h] at hc; exact ⟨h, (hyi c).mp hc⟩
    have hd' : d ≠ i ∧ (d = a ∨ d = b) := by
      by_cases h : d = i
      · subst h; simp at hd
      · rw [Function.update_of_ne h] at hd; exact ⟨h, (hyi d).mp hd⟩
    have hi' := (hyi i).mp hi
    obtain ⟨h1, hc2⟩ := hc'
    obtain ⟨h2, hd2⟩ := hd'
    have hcd_eq : c = d := by
      rcases hi' with rfl | rfl <;> rcases hc2 with rfl | rfl <;> rcases hd2 with rfl | rfl <;>
        first | rfl | exact absurd rfl h1 | exact absurd rfl h2
    subst hcd_eq
    exact lt_irrefl _ hcd'
  have h07 : y 0 = false ∨ y 7 = false := by
    by_cases h0 : y 0 = true
    · right
      rw [Bool.eq_false_iff]
      intro h7
      have h0' := (hyi 0).mp h0
      have h7' := (hyi 7).mp h7
      rcases h0' with rfl | rfl <;> rcases h7' with h7' | h7'
      · exact absurd h7' (by decide)
      · subst h7'; simp at hne
      · subst h7'; exact absurd hab' (by decide)
      · exact absurd h7' (by decide)
    · left; simpa using h0
  have hfy : f y = true :=
    (hmin y ⟨⟨a, b, hab, hya, hyb⟩, hminy⟩ h07).mpr ⟨a, b, hab, hya, hyb⟩
  refine hmono y x (fun i hi => ?_) hfy
  rcases (hyi i).mp hi with rfl | rfl <;> assumption
