import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_3332 : ∀ (x1 : (Fin (9 : ℕ) → Bool) → Bool),   (∀ (x2 : Fin (9 : ℕ)) (x3 : Bool), (x1 fun (x4 : Fin (9 : ℕ)) => Decidable.decide (x4 = x2) && x3) = Bool.false ∧ (x1 fun (x4 : Fin (9 : ℕ)) => !Decidable.decide (x4 = x2) || x3) = Bool.true) →     ∀ (x3 : ℕ) (x4 : Fin x3 → Bool) (x5 x6 : Fin x3 → ℕ × Bool) (x7 : ℕ × Bool) (x8 : (Fin (9 : ℕ) → Bool) → ℕ → Bool),       x7.1 < (10 : ℕ) + x3 →         (∀ (x10 : Fin (9 : ℕ) → Bool) (x11 : Fin (9 : ℕ)), x8 x10 ↑x11 = x10 x11) →           (∀ (x11 : Fin (9 : ℕ) → Bool), x8 x11 (9 : ℕ) = Bool.false) →             (∀ (x12 : Fin (9 : ℕ) → Bool) (x13 : Fin x3),                 have x14 : ℕ × Bool → Bool := fun (x14 : ℕ × Bool) => x8 x12 x14.1 ^^ x14.2;                 x8 x12 ((10 : ℕ) + ↑x13) = if x4 x13 = Bool.true then x14 (x5 x13) && x14 (x6 x13) else x14 (x5 x13) || x14 (x6 x13)) →               (∀ (x13 : Fin (9 : ℕ) → Bool), (x8 x13 x7.1 ^^ x7.2) = x1 x13) → ∃ (x14 : Fin x3), x7.1 = (10 : ℕ) + ↑x14 ∧ (9 : ℕ) ≤ (x5 x14).1 ∧ (9 : ℕ) ≤ (x6 x14).1 := by
  intro f hf n kind left right out eval hbound hinput hconst hgate hout
  have vary (i : Fin 9) (b v : Bool) :
      ∃ a : Fin 9 → Bool, a i = b ∧ eval a out.1 = v := by
    by_cases hv : (v ^^ out.2) = false
    · let a : Fin 9 → Bool := fun j => decide (j = i) && b
      refine ⟨a, by simp [a], ?_⟩
      have h : (eval a out.1 ^^ out.2) = false := (hout a).trans (hf i b).1
      cases v <;> cases hs : out.2 <;> simp_all
    · let a : Fin 9 → Bool := fun j => !decide (j = i) || b
      refine ⟨a, by simp [a], ?_⟩
      have h : (eval a out.1 ^^ out.2) = true := (hout a).trans (hf i b).2
      cases v <;> cases hs : out.2 <;> simp_all
  have hlow : 10 ≤ out.1 := by
    by_contra! h
    by_cases hi : out.1 < 9
    · let i : Fin 9 := ⟨out.1, hi⟩
      obtain ⟨a, ha, hv⟩ := vary i false true
      have he : eval a out.1 = a i := hinput a i
      simp_all
    · have he : out.1 = 9 := by omega
      obtain ⟨a, _, hv⟩ := vary 0 false true
      rw [he, hconst] at hv
      contradiction
  let g : Fin n := ⟨out.1 - 10, by omega⟩
  have hg : out.1 = 10 + g.val := by dsimp [g]; omega
  refine ⟨g, hg, ?_⟩
  have internal (p : ℕ × Bool) (hp : p = left g ∨ p = right g) : 9 ≤ p.1 := by
    by_contra! hi
    let i : Fin 9 := ⟨p.1, hi⟩
    obtain ⟨a, ha, hv⟩ := vary i ((!kind g) ^^ p.2) (kind g)
    have hin : eval a p.1 = a i := hinput a i
    have hlit : (eval a p.1 ^^ p.2) = !kind g := by simp [hin, ha]
    have he := hgate a g
    rw [hg, he] at hv
    rcases hp with hp | hp <;> rw [hp] at hlit <;>
      cases hk : kind g <;> simp [hk] at hlit <;> simp [hk, hlit] at hv
  exact ⟨internal _ (Or.inl rfl), internal _ (Or.inr rfl)⟩
