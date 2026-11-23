import Mathlib
import PEqualNP.Defs

private theorem L208_sum_emb (G : Fin 4 → Fin 6 → ℂ) :
    (∑ f : Fin 4 ↪ Fin 6, ∏ i : Fin 4, G i (f i)) =
      ∑ a : Fin 6, ∑ b : Fin 6, ∑ e : Fin 6, ∑ g : Fin 6,
        if a ≠ b ∧ a ≠ e ∧ a ≠ g ∧ b ≠ e ∧ b ≠ g ∧ e ≠ g then
          G 0 a * G 1 b * G 2 e * G 3 g else 0 := by
  classical
  have h1 : (∑ f : Fin 4 ↪ Fin 6, ∏ i : Fin 4, G i (f i)) =
      ∑ q : Fin 4 → Fin 6, if Function.Injective q then ∏ i : Fin 4, G i (q i) else 0 := by
    rw [← Finset.sum_filter]
    refine Finset.sum_bij (fun f _ => (f : Fin 4 → Fin 6)) ?_ ?_ ?_ ?_
    · intro f _
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, f.injective⟩
    · intro f _ f' _ hff
      exact DFunLike.coe_injective hff
    · intro q hq
      exact ⟨⟨q, (Finset.mem_filter.mp hq).2⟩, Finset.mem_univ _, rfl⟩
    · intro f _
      rfl
  have h2 : ∀ F : (Fin 4 → Fin 6) → ℂ, (∑ q : Fin 4 → Fin 6, F q) =
      ∑ a : Fin 6, ∑ b : Fin 6, ∑ e : Fin 6, ∑ g : Fin 6, F ![a, b, e, g] := by
    intro F
    rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
    refine Fintype.sum_bijective
      (fun q : Fin 4 → Fin 6 => (((q 0, q 1), q 2), q 3)) ?_ _ _ ?_
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
  have h3 : ∀ a b e g : Fin 6, Function.Injective ![a, b, e, g] ↔
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

private noncomputable def L208_fun (z : Fin 7 → ℂ) (p : Fin 4 × Fin 6) : ℂ :=
  if p.1 = 0 then
    (if p.2 = 0 then -(z 4 + z 5 + z 6)
      else if p.2 = 1 then z 0
      else if p.2 = 2 then z 1
      else if p.2 = 3 then z 2
      else if p.2 = 4 then z 3
      else -(z 0 + z 1 + z 2 + z 3))
  else if p.2 = 0 then
    (if p.1 = 1 then z 4 else if p.1 = 2 then z 5 else z 6)
  else 0

private noncomputable def L208_phi : (Fin 7 → ℂ) →ₗ[ℂ] (Fin 4 × Fin 6 → ℂ) where
  toFun := L208_fun
  map_add' := by
    intro x y
    funext p
    simp only [L208_fun, Pi.add_apply]
    split_ifs <;> ring
  map_smul' := by
    intro c x
    funext p
    simp only [L208_fun, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

private theorem L208_inj : Function.Injective L208_phi := by
  intro z w h
  have hf : L208_fun z = L208_fun w := h
  funext i
  fin_cases i
  · have h1 := congrFun hf (0, 1)
    simpa [L208_fun] using h1
  · have h1 := congrFun hf (0, 2)
    simpa [L208_fun] using h1
  · have h1 := congrFun hf (0, 3)
    simpa [L208_fun] using h1
  · have h1 := congrFun hf (0, 4)
    simpa [L208_fun] using h1
  · have h1 := congrFun hf (1, 0)
    simpa [L208_fun] using h1
  · have h1 := congrFun hf (2, 0)
    simpa [L208_fun] using h1
  · have h1 := congrFun hf (3, 0)
    simpa [L208_fun] using h1

set_option maxHeartbeats 8000000 in
private theorem L208_id (z : Fin 7 → ℂ) :
    (∑ f : Fin 4 ↪ Fin 6, ∏ i, (1 + L208_fun z (i, f i))) = 360 := by
  refine (L208_sum_emb (fun i j => 1 + L208_fun z (i, j))).trans ?_
  simp [Fin.sum_univ_six, L208_fun]
  ring

theorem PEqualNP.Outside.L_gct_208 : ∃ L : Submodule ℂ (Fin 4 × Fin 6 → ℂ), (∀ t ∈ L, (∑ f : Fin 4 ↪ Fin 6, ∏ i, (1 + t (i, f i))) = 360) ∧ Module.finrank ℂ L = 7 := by
  refine ⟨LinearMap.range L208_phi, ?_, ?_⟩
  · rintro t ⟨z, rfl⟩
    exact L208_id z
  · rw [LinearMap.finrank_range_of_inj L208_inj]
    simp
