import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3332

theorem aux (x1 : (Fin 9 → Bool) → Bool)
    (h1 : ∀ (x2 : Fin 9) (x3 : Bool), (x1 fun (x4 : Fin 9) => Decidable.decide (x4 = x2) && x3) = Bool.false ∧ (x1 fun (x4 : Fin 9) => !Decidable.decide (x4 = x2) || x3) = Bool.true)
    (o : (Fin 9 → Bool) → Bool) (hout : ∀ x, o x = x1 x) (j : Fin 9) (g a c : Bool)
    (y : (Fin 9 → Bool) → Bool)
    (h : ∀ x, o x = ((if g = true then (x j ^^ a) && y x else (x j ^^ a) || y x) ^^ c)) : False := by
  have e1 := (h1 j false).1
  have e2 := (h1 j true).1
  have e3 := (h1 j false).2
  have e4 := (h1 j true).2
  rw [← hout, h] at e1 e2 e3 e4
  simp at e1 e2 e3 e4
  cases g <;> cases a <;> cases c <;> simp_all

end PEqualNP.Outside.L_meta_3332

theorem PEqualNP.Outside.L_meta_3332 : ∀ (x1 : (Fin (9 : ℕ) → Bool) → Bool),   (∀ (x2 : Fin (9 : ℕ)) (x3 : Bool), (x1 fun (x4 : Fin (9 : ℕ)) => Decidable.decide (x4 = x2) && x3) = Bool.false ∧ (x1 fun (x4 : Fin (9 : ℕ)) => !Decidable.decide (x4 = x2) || x3) = Bool.true) →     ∀ (x3 : ℕ) (x4 : Fin x3 → Bool) (x5 x6 : Fin x3 → ℕ × Bool) (x7 : ℕ × Bool) (x8 : (Fin (9 : ℕ) → Bool) → ℕ → Bool),       x7.1 < (10 : ℕ) + x3 →         (∀ (x10 : Fin (9 : ℕ) → Bool) (x11 : Fin (9 : ℕ)), x8 x10 ↑x11 = x10 x11) →           (∀ (x11 : Fin (9 : ℕ) → Bool), x8 x11 (9 : ℕ) = Bool.false) →             (∀ (x12 : Fin (9 : ℕ) → Bool) (x13 : Fin x3),                 have x14 : ℕ × Bool → Bool := fun (x14 : ℕ × Bool) => x8 x12 x14.1 ^^ x14.2;                 x8 x12 ((10 : ℕ) + ↑x13) = if x4 x13 = Bool.true then x14 (x5 x13) && x14 (x6 x13) else x14 (x5 x13) || x14 (x6 x13)) →               (∀ (x13 : Fin (9 : ℕ) → Bool), (x8 x13 x7.1 ^^ x7.2) = x1 x13) → ∃ (x14 : Fin x3), x7.1 = (10 : ℕ) + ↑x14 ∧ (9 : ℕ) ≤ (x5 x14).1 ∧ (9 : ℕ) ≤ (x6 x14).1 := by
  intro x1 h1 n g l r out x8 hlt hin hz hgate hout
  by_cases h9 : out.1 < 9
  · exfalso
    obtain ⟨i, hi⟩ : ∃ i : Fin 9, out.1 = (i : ℕ) := ⟨⟨out.1, h9⟩, rfl⟩
    have e1 := hout (fun t => decide (t = i) && false)
    have e2 := hout (fun t => decide (t = i) && true)
    rw [(h1 i false).1] at e1
    rw [(h1 i true).1] at e2
    rw [hi, hin] at e1 e2
    simp at e1 e2
    simp_all
  by_cases h9' : out.1 = 9
  · exfalso
    have e1 := hout (fun t => decide (t = 0) && false)
    have e2 := hout (fun t => !decide (t = 0) || true)
    rw [(h1 0 false).1] at e1
    rw [(h1 0 true).2] at e2
    rw [h9', hz] at e1 e2
    simp_all
  obtain ⟨k, hk⟩ : ∃ k : Fin n, out.1 = 10 + k := ⟨⟨out.1 - 10, by omega⟩, by simp; omega⟩
  refine ⟨k, hk, ?_, ?_⟩
  · by_contra hc
    rw [not_le] at hc
    obtain ⟨j, hj⟩ : ∃ j : Fin 9, (l k).1 = (j : ℕ) := ⟨⟨_, hc⟩, rfl⟩
    apply _root_.PEqualNP.Outside.L_meta_3332.aux x1 h1 (fun x => x8 x out.1 ^^ out.2) hout j (g k) (l k).2 out.2
      (fun x => x8 x (r k).1 ^^ (r k).2)
    intro x
    have hg := hgate x k
    dsimp only at hg
    rw [hk, hg, hj, hin]
  · by_contra hc
    rw [not_le] at hc
    obtain ⟨j, hj⟩ : ∃ j : Fin 9, (r k).1 = (j : ℕ) := ⟨⟨_, hc⟩, rfl⟩
    apply _root_.PEqualNP.Outside.L_meta_3332.aux x1 h1 (fun x => x8 x out.1 ^^ out.2) hout j (g k) (r k).2 out.2
      (fun x => x8 x (l k).1 ^^ (l k).2)
    intro x
    have hg := hgate x k
    dsimp only at hg
    rw [hk, hg, hj, hin, Bool.and_comm, Bool.or_comm]
