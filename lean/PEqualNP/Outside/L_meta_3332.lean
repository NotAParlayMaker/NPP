import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_3332 : ∀ (x1 : (Fin (9 : ℕ) → Bool) → Bool),   (∀ (x2 : Fin (9 : ℕ)) (x3 : Bool), (x1 fun (x4 : Fin (9 : ℕ)) => Decidable.decide (x4 = x2) && x3) = Bool.false ∧ (x1 fun (x4 : Fin (9 : ℕ)) => !Decidable.decide (x4 = x2) || x3) = Bool.true) →     ∀ (x3 : ℕ) (x4 : Fin x3 → Bool) (x5 x6 : Fin x3 → ℕ × Bool) (x7 : ℕ × Bool) (x8 : (Fin (9 : ℕ) → Bool) → ℕ → Bool),       x7.1 < (10 : ℕ) + x3 →         (∀ (x10 : Fin (9 : ℕ) → Bool) (x11 : Fin (9 : ℕ)), x8 x10 ↑x11 = x10 x11) →           (∀ (x11 : Fin (9 : ℕ) → Bool), x8 x11 (9 : ℕ) = Bool.false) →             (∀ (x12 : Fin (9 : ℕ) → Bool) (x13 : Fin x3),                 have x14 : ℕ × Bool → Bool := fun (x14 : ℕ × Bool) => x8 x12 x14.1 ^^ x14.2;                 x8 x12 ((10 : ℕ) + ↑x13) = if x4 x13 = Bool.true then x14 (x5 x13) && x14 (x6 x13) else x14 (x5 x13) || x14 (x6 x13)) →               (∀ (x13 : Fin (9 : ℕ) → Bool), (x8 x13 x7.1 ^^ x7.2) = x1 x13) → ∃ (x14 : Fin x3), x7.1 = (10 : ℕ) + ↑x14 ∧ (9 : ℕ) ≤ (x5 x14).1 ∧ (9 : ℕ) ≤ (x6 x14).1 := by
  intro f hf m isAnd op1 op2 out val hout hin h9 hgate hres
  have fE : ∀ i : Fin 9, f (fun x4 => decide (x4 = i)) = false := fun i => by simpa using (hf i true).1
  have fZ : f (fun _ => false) = false := by simpa using (hf 0 false).1
  have fA : f (fun _ => true) = true := by simpa using (hf 0 true).2
  have fN : ∀ i : Fin 9, f (fun x4 => !decide (x4 = i)) = true := fun i => by simpa using (hf i false).2
  have hg : ∀ x (j : Fin m), val x (10 + j) = if isAnd j = true then
      ((val x (op1 j).1 ^^ (op1 j).2) && (val x (op2 j).1 ^^ (op2 j).2)) else
      ((val x (op1 j).1 ^^ (op1 j).2) || (val x (op2 j).1 ^^ (op2 j).2)) := fun x j => hgate x j
  -- the output literal is a gate
  have hge : 10 ≤ out.1 := by
    by_contra h
    by_cases h9' : out.1 = 9
    · have e1 := hres (fun _ => false)
      have e2 := hres (fun _ => true)
      rw [h9', h9, fZ] at e1
      rw [h9', h9, fA] at e2
      rw [e1] at e2
      exact Bool.false_ne_true e2
    · have hi : out.1 < 9 := by omega
      have hv : ∀ x, val x out.1 = x ⟨out.1, hi⟩ := fun x => hin x ⟨out.1, hi⟩
      have e0 := hres (fun _ => false)
      have e1 := hres (fun x4 => decide (x4 = ⟨out.1, hi⟩))
      rw [hv, fZ] at e0
      rw [hv, fE] at e1
      simp at e0 e1
      rw [e0] at e1
      exact Bool.false_ne_true e1
  obtain ⟨j, hj⟩ : ∃ j : Fin m, out.1 = 10 + j := ⟨⟨out.1 - 10, by omega⟩, by simp; omega⟩
  -- an operand of the output gate that reads an input contradicts the four test inputs
  have operand : ∀ (w : ℕ × Bool) (g : (Fin 9 → Bool) → Bool), w.1 < 9 →
      (∀ x, ((if isAnd j = true then ((val x w.1 ^^ w.2) && g x) else ((val x w.1 ^^ w.2) || g x))
        ^^ out.2) = f x) → False := by
    intro w g hw key
    let i : Fin 9 := ⟨w.1, hw⟩
    have hv : ∀ x, val x w.1 = x i := fun x => hin x i
    have k0 := key (fun _ => false)
    have k1 := key (fun _ => true)
    have k2 := key (fun x4 => decide (x4 = i))
    have k3 := key (fun x4 => !decide (x4 = i))
    rw [hv, fZ] at k0
    rw [hv, fA] at k1
    rw [hv, fE] at k2
    rw [hv, fN] at k3
    simp only [decide_true, Bool.not_true] at k0 k1 k2 k3
    revert k0 k1 k2 k3
    generalize g (fun _ => false) = g0
    generalize g (fun _ => true) = g1
    generalize g (fun x4 => decide (x4 = i)) = g2
    generalize g (fun x4 => !decide (x4 = i)) = g3
    cases isAnd j <;> cases w.2 <;> cases out.2 <;> cases g0 <;> cases g1 <;> cases g2 <;> cases g3 <;> simp
  refine ⟨j, hj, ?_, ?_⟩
  · by_contra h
    rw [not_le] at h
    apply operand (op1 j) (fun x => val x (op2 j).1 ^^ (op2 j).2) h
    intro x
    have := hres x
    rw [hj, hg] at this
    exact this
  · by_contra h
    rw [not_le] at h
    apply operand (op2 j) (fun x => val x (op1 j).1 ^^ (op1 j).2) h
    intro x
    have := hres x
    rw [hj, hg] at this
    rw [← this]
    cases isAnd j <;> simp [Bool.and_comm, Bool.or_comm]
