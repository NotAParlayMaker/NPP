import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7830_aux

def inc (a b : Fin 13) : Prop := a = b ∨ a = b + 1 ∨ a = b + 3 ∨ a = b + 9

def ln (p : Fin 13 → Bool) (l : Fin 13) : Bool := !(p l || p (l + 1) || p (l + 3) || p (l + 9))

def bad (f : Fin 26 → Bool) : Prop :=
  ∃ (a : Fin 13) (b : Fin 13), inc a b ∧ f (Fin.castAdd 13 a) = true ∧ f (Fin.natAdd 13 b) = true

theorem upd (f : Fin 26 → Bool) (i : Fin 26) (P : (Fin 26 → Bool) → Prop) (hf : Maximal P f)
    (hg : P (Function.update f i true)) : f i = true := by
  have h1 : f ≤ Function.update f i true := by
    intro j
    by_cases h : j = i
    · subst h
      rw [Function.update_self]
      exact Bool.le_true _
    · rw [Function.update_of_ne h]
  have h2 := hf.2 hg h1 i
  rw [Function.update_self] at h2
  revert h2
  cases f i <;> simp

theorem cn (a b : Fin 13) : Fin.castAdd 13 a ≠ Fin.natAdd 13 b := by
  intro h
  have := congrArg Fin.val h
  simp at this
  omega

theorem main (f : Fin 26 → Bool) (hf : Maximal (fun g => ¬ bad g) f) :
    ∃ p : Fin 13 → Bool, f = Fin.append p (ln p) ∧
      ∀ a : Fin 13, p a = false → ∃ b : Fin 13, inc a b ∧ ln p b = true := by
  have hnb : ¬ bad f := hf.1
  have hA : ∀ b, f (Fin.natAdd 13 b) = ln (fun i => f (Fin.castAdd 13 i)) b := by
    intro b
    cases hb : f (Fin.natAdd 13 b)
    · cases hl : ln (fun i => f (Fin.castAdd 13 i)) b
      · rfl
      · exfalso
        have key := upd f (Fin.natAdd 13 b) _ hf (by
          rintro ⟨a, b', hinc, h1, h2⟩
          rw [Function.update_of_ne (cn a b)] at h1
          by_cases hbb : b' = b
          · subst hbb
            simp only [ln] at hl
            rcases hinc with h | h | h | h <;> subst h <;> simp_all
          · rw [Function.update_of_ne (fun h => hbb (Fin.natAdd_injective _ _ h))] at h2
            exact hnb ⟨a, b', hinc, h1, h2⟩)
        rw [hb] at key
        cases key
    · have key : ∀ a, inc a b → f (Fin.castAdd 13 a) = false := by
        intro a ha
        cases h : f (Fin.castAdd 13 a)
        · rfl
        · exact absurd ⟨a, b, ha, h, hb⟩ hnb
      simp [ln, key b (Or.inl rfl), key (b + 1) (Or.inr (Or.inl rfl)),
        key (b + 3) (Or.inr (Or.inr (Or.inl rfl))), key (b + 9) (Or.inr (Or.inr (Or.inr rfl)))]
  refine ⟨fun i => f (Fin.castAdd 13 i), ?_, ?_⟩
  · funext j
    have hall : ∀ k : Fin (13 + 13), f k = Fin.append (m := 13) (n := 13)
        (fun i => f (Fin.castAdd 13 i)) (ln (fun i => f (Fin.castAdd 13 i))) k := by
      intro k
      refine Fin.addCases (fun i => ?_) (fun i => ?_) k
      · rw [Fin.append_left]
      · rw [Fin.append_right]
        exact hA i
    exact hall j
  · intro a ha
    by_contra hno
    have key := upd f (Fin.castAdd 13 a) _ hf (by
      rintro ⟨a', b', hinc, h1, h2⟩
      rw [Function.update_of_ne (cn a b').symm] at h2
      by_cases haa : a' = a
      · subst haa
        exact hno ⟨b', hinc, by rw [← hA b']; exact h2⟩
      · rw [Function.update_of_ne (show Fin.castAdd 13 a' ≠ Fin.castAdd 13 a from fun h => haa (Fin.castAdd_injective _ _ h))] at h1
        exact hnb ⟨a', b', hinc, h1, h2⟩)
    have ha2 : f (Fin.castAdd 13 a) = false := ha
    rw [ha2] at key
    cases key

end PEqualNP.Outside.L_meta_7830_aux

theorem PEqualNP.Outside.L_meta_7830 : have x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); have x2 : (Fin (13 : ℕ) → Bool) → Fin (13 : ℕ) → Bool := fun (x2 : Fin (13 : ℕ) → Bool) (x3 : Fin (13 : ℕ)) => !(x2 x3 || x2 (x3 + (1 : Fin (13 : ℕ))) || x2 (x3 + (3 : Fin (13 : ℕ))) || x2 (x3 + (9 : Fin (13 : ℕ)))); have x3 : (Fin (26 : ℕ) → Bool) → Prop := fun (x3 : Fin (26 : ℕ) → Bool) => ∃ (x4 : Fin (13 : ℕ)) (x5 : Fin (13 : ℕ)), x1 x4 x5 ∧ x3 (Fin.castAdd (13 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (13 : ℕ) x5) = Bool.true; ∀ (x4 : Fin (26 : ℕ) → Bool), Maximal (fun (x5 : Fin (26 : ℕ) → Bool) => ¬x3 x5) x4 → ∃ (x6 : Fin (13 : ℕ) → Bool), x4 = Fin.append x6 (x2 x6) ∧ ∀ (x7 : Fin (13 : ℕ)), x6 x7 = Bool.false → ∃ (x9 : Fin (13 : ℕ)), x1 x7 x9 ∧ x2 x6 x9 = Bool.true := by
  exact fun x4 h => PEqualNP.Outside.L_meta_7830_aux.main x4 h
