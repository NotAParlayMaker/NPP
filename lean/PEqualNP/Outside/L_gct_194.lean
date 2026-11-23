import Mathlib
import PEqualNP.Defs

private theorem L_gct_194_sum_emb (G : Fin 5 → Fin 4 → ℂ) :
    (∑ f : Fin 4 ↪ Fin 5, ∏ j : Fin 4, G (f j) j) =
      ∑ a : Fin 5, ∑ b : Fin 5, ∑ e : Fin 5, ∑ g : Fin 5,
        if a ≠ b ∧ a ≠ e ∧ a ≠ g ∧ b ≠ e ∧ b ≠ g ∧ e ≠ g then
          G a 0 * G b 1 * G e 2 * G g 3 else 0 := by
  classical
  have h1 : (∑ f : Fin 4 ↪ Fin 5, ∏ j : Fin 4, G (f j) j) =
      ∑ q : Fin 4 → Fin 5, if Function.Injective q then ∏ j : Fin 4, G (q j) j else 0 := by
    rw [← Finset.sum_filter]
    refine Finset.sum_bij (fun f _ => (f : Fin 4 → Fin 5)) ?_ ?_ ?_ ?_
    · intro f _
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, f.injective⟩
    · intro f _ f' _ hff
      exact DFunLike.coe_injective hff
    · intro q hq
      exact ⟨⟨q, (Finset.mem_filter.mp hq).2⟩, Finset.mem_univ _, rfl⟩
    · intro f _
      rfl
  have h2 : ∀ F : (Fin 4 → Fin 5) → ℂ, (∑ q : Fin 4 → Fin 5, F q) =
      ∑ a : Fin 5, ∑ b : Fin 5, ∑ e : Fin 5, ∑ g : Fin 5, F ![a, b, e, g] := by
    intro F
    rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
    refine Fintype.sum_bijective
      (fun q : Fin 4 → Fin 5 => (((q 0, q 1), q 2), q 3)) ?_ _ _ ?_
    · refine Function.bijective_iff_has_inverse.mpr
        ⟨fun p => ![p.1.1.1, p.1.1.2, p.1.2, p.2], ?_, ?_⟩
      · intro q
        funext i
        fin_cases i <;> rfl
      · intro p
        rfl
    · intro q
      congr 1
      funext i
      fin_cases i <;> rfl
  have h3 : ∀ a b e g : Fin 5, Function.Injective ![a, b, e, g] ↔
      (a ≠ b ∧ a ≠ e ∧ a ≠ g ∧ b ≠ e ∧ b ≠ g ∧ e ≠ g) := by
    intro a b e g
    constructor
    · intro h
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro hh
        exact absurd (h (a₁ := 0) (a₂ := 1) hh) (by decide)
      · intro hh
        exact absurd (h (a₁ := 0) (a₂ := 2) hh) (by decide)
      · intro hh
        exact absurd (h (a₁ := 0) (a₂ := 3) hh) (by decide)
      · intro hh
        exact absurd (h (a₁ := 1) (a₂ := 2) hh) (by decide)
      · intro hh
        exact absurd (h (a₁ := 1) (a₂ := 3) hh) (by decide)
      · intro hh
        exact absurd (h (a₁ := 2) (a₂ := 3) hh) (by decide)
    · rintro ⟨h01, h02, h03, h12, h13, h23⟩ i j hij
      fin_cases i <;> fin_cases j <;> first
        | rfl
        | exact absurd hij h01
        | exact absurd hij h02
        | exact absurd hij h03
        | exact absurd hij h12
        | exact absurd hij h13
        | exact absurd hij h23
        | exact absurd hij.symm h01
        | exact absurd hij.symm h02
        | exact absurd hij.symm h03
        | exact absurd hij.symm h12
        | exact absurd hij.symm h13
        | exact absurd hij.symm h23
  rw [h1, h2]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun g _ => ?_
  by_cases hc : a ≠ b ∧ a ≠ e ∧ a ≠ g ∧ b ≠ e ∧ b ≠ g ∧ e ≠ g
  · rw [if_pos hc, if_pos ((h3 a b e g).mpr hc), Fin.prod_univ_four]
    rfl
  · rw [if_neg hc, if_neg (fun hi => hc ((h3 a b e g).mp hi))]

set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_gct_194 : ∀ c d : ℂ, (∑ f : Fin 4 ↪ Fin 5, ∏ j : Fin 4, (1 + (if (f j).val = 4 then d * (if j.val = 0 then (1 : ℂ) else if j.val = 1 then -1 else 0) else c * (if j.val = (f j).val then (1 : ℂ) else if j.val = ((f j).val + 1) % 4 then Complex.I else if j.val = ((f j).val + 2) % 4 then -Complex.I else -1)))) = 120 := by
  intro c d
  refine (L_gct_194_sum_emb (fun r j => 1 + (if r.val = 4 then d * (if j.val = 0 then (1 : ℂ) else if j.val = 1 then -1 else 0) else c * (if j.val = r.val then (1 : ℂ) else if j.val = (r.val + 1) % 4 then Complex.I else if j.val = (r.val + 2) % 4 then -Complex.I else -1)))).trans ?_
  simp [Fin.sum_univ_five]
  linear_combination (2 * c ^ 4 * Complex.I ^ 2 - 8 * c ^ 4 * Complex.I + 2 * c ^ 4 + 24 * c ^ 2) * Complex.I_sq
