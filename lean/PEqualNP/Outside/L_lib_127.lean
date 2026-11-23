import Mathlib

namespace PEqualNP.Outside.L_lib_127

open Equiv

-- Two involutions without fixed points: no power of their product sends x to f x.
theorem no_fix {X : Type*} (f t : Perm X) (hf : ∀ x, f (f x) = x) (ht : ∀ x, t (t x) = x)
    (hf0 : ∀ x, f x ≠ x) (ht0 : ∀ x, t x ≠ x) :
    ∀ (k : ℕ) (x : X), ((f * t) ^ k) x ≠ f x := by
  have step : ∀ k : ℕ, (∀ x, ((f * t) ^ k) x ≠ f x) → ∀ x, ((f * t) ^ (k + 2)) x ≠ f x := by
    intro k ih x h
    have e : (f * t) ^ (k + 2) = (f * t) * (f * t) ^ k * (f * t) := by
      rw [pow_succ, pow_succ']
    rw [e] at h
    have h0 : f (t (((f * t) ^ k) (f (t x)))) = f x := h
    have h1 : t (((f * t) ^ k) (f (t x))) = x := f.injective h0
    have h2 : ((f * t) ^ k) (f (t x)) = t x := by
      have h3 := congrArg t h1
      rw [ht] at h3
      exact h3
    exact ih (f (t x)) (by rw [h2, hf])
  have key : ∀ k : ℕ, (∀ x, ((f * t) ^ k) x ≠ f x) ∧ (∀ x, ((f * t) ^ (k + 1)) x ≠ f x) := by
    intro k
    induction k with
    | zero =>
      refine ⟨?_, ?_⟩
      · intro x h
        have h0 : x = f x := h
        exact hf0 x h0.symm
      · intro x h
        have h0 : f (t x) = f x := h
        exact ht0 x (f.injective h0)
    | succ k ih => exact ⟨ih.2, step k ih.1⟩
  intro k
  exact (key k).1

theorem not_same {X : Type*} [Finite X] (f t : Perm X) (hf : ∀ x, f (f x) = x)
    (ht : ∀ x, t (t x) = x) (hf0 : ∀ x, f x ≠ x) (ht0 : ∀ x, t x ≠ x) (x : X) :
    ¬ Perm.SameCycle (f * t) x (f x) := by
  intro h
  obtain ⟨i, _, hi⟩ := h.exists_pow_eq'
  exact no_fix f t hf ht hf0 ht0 i x hi

theorem same_flip {X : Type*} (f t : Perm X) (hf : ∀ x, f (f x) = x) (ht : ∀ x, t (t x) = x)
    {x y : X} (h : Perm.SameCycle (f * t) x y) : Perm.SameCycle (f * t) (f x) (f y) := by
  have hfi : f⁻¹ = f := by
    ext z
    rw [Perm.inv_eq_iff_eq]
    exact (hf z).symm
  have hti : t⁻¹ = t := by
    ext z
    rw [Perm.inv_eq_iff_eq]
    exact (ht z).symm
  have e : f * (f * t) * f⁻¹ = (f * t)⁻¹ := by
    rw [mul_inv_rev, hfi, hti]
    ext z
    simp only [Perm.mul_apply]
    rw [hf]
  have h1 := Perm.SameCycle.conj (g := f) h
  rw [e] at h1
  exact Perm.sameCycle_inv.mp h1

-- A proper 2-colouring of the union of the two matchings.
theorem colouring {X Y : Type*} [Finite X] [LinearOrder Y] (e : X → Y)
    (he : Function.Injective e) (f t : Perm X) (hf : ∀ x, f (f x) = x) (ht : ∀ x, t (t x) = x)
    (hf0 : ∀ x, f x ≠ x) (ht0 : ∀ x, t x ≠ x) :
    ∃ c : X → Bool, (∀ x, c (f x) = !c x) ∧ (∀ x, c (t x) = !c x) := by
  classical
  let s := Perm.SameCycle.setoid (f * t)
  let r : X → X := fun x => Quotient.out (Quotient.mk s x)
  have r_eq : ∀ x y, Perm.SameCycle (f * t) x y → r x = r y := fun x y h =>
    congrArg Quotient.out (Quotient.sound h)
  have r_same : ∀ x, Perm.SameCycle (f * t) (r x) x := fun x =>
    Quotient.exact (Quotient.out_eq (Quotient.mk s x))
  have r_ne : ∀ x, r x ≠ r (f x) := by
    intro x h
    apply not_same f t hf ht hf0 ht0 x
    have h1 := (r_same x).symm
    have h2 := r_same (f x)
    rw [← h] at h2
    exact h1.trans h2
  have flipdec : ∀ x, decide (e (r (f x)) < e (r x)) = !decide (e (r x) < e (r (f x))) := by
    intro x
    have hne : e (r x) ≠ e (r (f x)) := fun h => r_ne x (he h)
    rcases lt_or_gt_of_ne hne with h | h
    · simp [h, lt_asymm h]
    · simp [h, lt_asymm h]
  refine ⟨fun x => decide (e (r x) < e (r (f x))), ?_, ?_⟩
  · intro x
    show decide (e (r (f x)) < e (r (f (f x)))) = !decide (e (r x) < e (r (f x)))
    rw [hf x]
    exact flipdec x
  · intro x
    show decide (e (r (t x)) < e (r (f (t x)))) = !decide (e (r x) < e (r (f x)))
    have h0 : Perm.SameCycle (f * t) ((f * t) x) x :=
      Perm.sameCycle_apply_left.mpr (Perm.SameCycle.refl _ x)
    have a1 : r (f (t x)) = r x := r_eq _ _ h0
    have h1 := same_flip f t hf ht h0
    have h2 : f ((f * t) x) = t x := by rw [Perm.mul_apply, hf]
    rw [h2] at h1
    have a2 : r (t x) = r (f x) := r_eq _ _ h1
    rw [a1, a2]
    exact flipdec x

def swp (n : ℕ) : Perm (Fin n × Bool) where
  toFun x := (x.1, !x.2)
  invFun x := (x.1, !x.2)
  left_inv x := by simp
  right_inv x := by simp

theorem main (n : ℕ) (π : Perm (Fin n × Bool)) :
    ∃ b : Fin n → Bool, ∃ π₀ π₁ : Perm (Fin n), ∀ (ρ : Fin n) (β : Bool),
      (π (ρ, β)).1 = (if (β != b ρ) = true then π₁ else π₀) ρ := by
  have fa : ∀ x : Fin n × Bool, swp n x = (x.1, !x.2) := fun _ => rfl
  have hf : ∀ x, swp n (swp n x) = x := by
    intro x
    rw [fa, fa]
    simp
  have hf0 : ∀ x, swp n x ≠ x := by
    intro x h
    rw [fa] at h
    have h1 := congrArg Prod.snd h
    simp at h1
  have ta : ∀ x, (π⁻¹ * swp n * π) x = π⁻¹ (swp n (π x)) := fun _ => rfl
  have ht : ∀ x, (π⁻¹ * swp n * π) ((π⁻¹ * swp n * π) x) = x := by
    intro x
    rw [ta, ta, Perm.inv_def, Equiv.apply_symm_apply, hf, Equiv.symm_apply_apply]
  have ht0 : ∀ x, (π⁻¹ * swp n * π) x ≠ x := by
    intro x h
    rw [ta] at h
    have h1 := congrArg π h
    rw [Perm.inv_def, Equiv.apply_symm_apply] at h1
    exact hf0 _ h1
  obtain ⟨c, c1, c2⟩ := colouring (fun x : Fin n × Bool => toLex x)
    (fun _ _ h => toLex.injective h) (swp n) (π⁻¹ * swp n * π) hf ht hf0 ht0
  have cb : ∀ (ρ : Fin n) (β : Bool), c (ρ, β) = (β != c (ρ, false)) := by
    intro ρ β
    cases β with
    | false => simp
    | true =>
      have h1 := c1 (ρ, false)
      rw [fa] at h1
      have h2 : c (ρ, true) = !c (ρ, false) := h1
      rw [h2]
      simp
  have pair : ∀ u v : Fin n × Bool, u.1 = v.1 → u = v ∨ u = swp n v := by
    rintro ⟨a, p⟩ ⟨a', q⟩ h
    have h' : a = a' := h
    subst h'
    rw [fa]
    cases p <;> cases q <;> simp
  have inj : ∀ γ : Bool,
      Function.Injective (fun ρ : Fin n => (π (ρ, (γ != c (ρ, false)))).1) := by
    intro γ ρ ρ' h
    have cx : c (ρ, (γ != c (ρ, false))) = γ := by
      rw [cb]
      cases γ <;> cases c (ρ, false) <;> rfl
    have cy : c (ρ', (γ != c (ρ', false))) = γ := by
      rw [cb]
      cases γ <;> cases c (ρ', false) <;> rfl
    rcases pair _ _ h with h1 | h1
    · have h2 := π.injective h1
      exact congrArg Prod.fst h2
    · exfalso
      have h2 : (ρ, (γ != c (ρ, false))) = (π⁻¹ * swp n * π) (ρ', (γ != c (ρ', false))) := by
        rw [ta, ← h1, Perm.inv_def, Equiv.symm_apply_apply]
      have h3 := c2 (ρ', (γ != c (ρ', false)))
      rw [← h2, cx, cy] at h3
      cases γ <;> simp at h3
  refine ⟨fun ρ => c (ρ, false),
    Equiv.ofBijective _ ⟨inj false, Finite.surjective_of_injective (inj false)⟩,
    Equiv.ofBijective _ ⟨inj true, Finite.surjective_of_injective (inj true)⟩, ?_⟩
  intro ρ β
  by_cases hβ : (β != c (ρ, false)) = true
  · rw [if_pos hβ]
    show (π (ρ, β)).1 = (π (ρ, (true != c (ρ, false)))).1
    have h1 : β = (true != c (ρ, false)) := by
      revert hβ
      cases β <;> cases c (ρ, false) <;> simp
    rw [← h1]
  · rw [if_neg hβ]
    show (π (ρ, β)).1 = (π (ρ, (false != c (ρ, false)))).1
    have h1 : β = (false != c (ρ, false)) := by
      revert hβ
      cases β <;> cases c (ρ, false) <;> simp
    rw [← h1]

end PEqualNP.Outside.L_lib_127

theorem PEqualNP.Outside.L_lib_127 : ∀ (n : ℕ) (π : Equiv.Perm (Fin n × Bool)), ∃ b : Fin n → Bool, ∃ π₀ π₁ : Equiv.Perm (Fin n), ∀ (ρ : Fin n) (β : Bool), (π (ρ, β)).1 = (if (β != b ρ) = true then π₁ else π₀) ρ :=
  fun n π => PEqualNP.Outside.L_lib_127.main n π
