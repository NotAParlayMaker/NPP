import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.Gct208

theorem inj4 (a b c d : Fin 6) : Function.Injective ![a, b, c, d] ↔
    (a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro e
    · exact absurd (@h 0 1 e) (by decide)
    · exact absurd (@h 0 2 e) (by decide)
    · exact absurd (@h 0 3 e) (by decide)
    · exact absurd (@h 1 2 e) (by decide)
    · exact absurd (@h 1 3 e) (by decide)
    · exact absurd (@h 2 3 e) (by decide)
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩ i j hij
    fin_cases i <;> fin_cases j <;> first | rfl | exact absurd hij h1 | exact absurd hij.symm h1 | exact absurd hij h2 | exact absurd hij.symm h2 | exact absurd hij h3 | exact absurd hij.symm h3 | exact absurd hij h4 | exact absurd hij.symm h4 | exact absurd hij h5 | exact absurd hij.symm h5 | exact absurd hij h6 | exact absurd hij.symm h6

theorem sum_emb (g : Fin 4 → Fin 6 → ℂ) :
    (∑ f : Fin 4 ↪ Fin 6, ∏ i, g i (f i)) = ∑ a, ∑ b, ∑ c, ∑ d,
      if (a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d) then g 0 a * g 1 b * g 2 c * g 3 d
      else 0 := by
  classical
  have h1 : (∑ f : Fin 4 ↪ Fin 6, ∏ i, g i (f i)) =
      ∑ f : Fin 4 → Fin 6, if Function.Injective f then ∏ i, g i (f i) else 0 := by
    rw [← Finset.sum_filter,
      Finset.sum_subtype (Finset.univ.filter Function.Injective) (p := Function.Injective)
        (by simp)]
    exact (Fintype.sum_equiv (Equiv.subtypeInjectiveEquivEmbedding (Fin 4) (Fin 6)) _ _
      (fun x => rfl)).symm
  have h2 : (∑ f : Fin 4 → Fin 6, if Function.Injective f then ∏ i, g i (f i) else 0) =
      ∑ p : Fin 6 × Fin 6 × Fin 6 × Fin 6,
        if Function.Injective ![p.1, p.2.1, p.2.2.1, p.2.2.2] then
          ∏ i, g i (![p.1, p.2.1, p.2.2.1, p.2.2.2] i) else 0 := by
    refine (Fintype.sum_equiv
      (⟨fun p => ![p.1, p.2.1, p.2.2.1, p.2.2.2], fun f => (f 0, f 1, f 2, f 3),
        fun p => rfl, fun f => by funext i; fin_cases i <;> rfl⟩ :
        (Fin 6 × Fin 6 × Fin 6 × Fin 6) ≃ (Fin 4 → Fin 6)) _ _ (fun p => rfl)).symm
  rw [h1, h2]
  simp only [Fintype.sum_prod_type, inj4, Fin.prod_univ_four]
  rfl

theorem key (r : Fin 6 → ℂ) (s1 s2 s3 : ℂ) (h0 : r 0 + s1 + s2 + s3 = 0)
    (h1 : r 1 + r 2 + r 3 + r 4 + r 5 = 0) :
    (∑ a : Fin 6, ∑ b : Fin 6, ∑ c : Fin 6, ∑ d : Fin 6,
      if (a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d) then
        (1 + r a) * (1 + if b = 0 then s1 else 0) * (1 + if c = 0 then s2 else 0) *
          (1 + if d = 0 then s3 else 0)
      else 0) = 360 := by
  simp [Fin.sum_univ_six]
  linear_combination 60 * h0 + (60 + 12 * (s1 + s2 + s3)) * h1

noncomputable def w (c : Fin 7 → ℂ) : Fin 4 × Fin 6 → ℂ := fun p =>
  ![![-(c 4 + c 5 + c 6), c 0, c 1, c 2, c 3, -(c 0 + c 1 + c 2 + c 3)],
    ![c 4, 0, 0, 0, 0, 0], ![c 5, 0, 0, 0, 0, 0], ![c 6, 0, 0, 0, 0, 0]] p.1 p.2

noncomputable def phi : (Fin 7 → ℂ) →ₗ[ℂ] (Fin 4 × Fin 6 → ℂ) where
  toFun := w
  map_add' := by
    intro x y
    funext ⟨i, j⟩
    fin_cases i <;> fin_cases j <;> simp [w] <;> ring
  map_smul' := by
    intro m x
    funext ⟨i, j⟩
    fin_cases i <;> fin_cases j <;> simp [w] <;> ring

theorem phi_inj : Function.Injective phi := by
  refine (injective_iff_map_eq_zero phi).2 ?_
  intro c h
  have hw : w c = 0 := h
  funext k
  fin_cases k
  · simpa [w] using congrFun hw (0, 1)
  · simpa [w] using congrFun hw (0, 2)
  · simpa [w] using congrFun hw (0, 3)
  · simpa [w] using congrFun hw (0, 4)
  · simpa [w] using congrFun hw (1, 0)
  · simpa [w] using congrFun hw (2, 0)
  · simpa [w] using congrFun hw (3, 0)

theorem w_row1 (c : Fin 7 → ℂ) (b : Fin 6) : w c (1, b) = if b = 0 then c 4 else 0 := by
  fin_cases b <;> simp [w]

theorem w_row2 (c : Fin 7 → ℂ) (b : Fin 6) : w c (2, b) = if b = 0 then c 5 else 0 := by
  fin_cases b <;> simp [w]

theorem w_row3 (c : Fin 7 → ℂ) (b : Fin 6) : w c (3, b) = if b = 0 then c 6 else 0 := by
  fin_cases b <;> simp [w]

theorem level (c : Fin 7 → ℂ) :
    (∑ f : Fin 4 ↪ Fin 6, ∏ i, (1 + w c (i, f i))) = 360 := by
  refine (sum_emb (fun i j => 1 + w c (i, j))).trans ?_
  simp only [w_row1, w_row2, w_row3]
  refine key (fun j => w c (0, j)) (c 4) (c 5) (c 6) ?_ ?_
  · show -(c 4 + c 5 + c 6) + c 4 + c 5 + c 6 = 0
    ring
  · show c 0 + c 1 + c 2 + c 3 + -(c 0 + c 1 + c 2 + c 3) = 0
    ring

end PEqualNP.Outside.Gct208

theorem PEqualNP.Outside.L_gct_208 : ∃ L : Submodule ℂ (Fin 4 × Fin 6 → ℂ), (∀ t ∈ L, (∑ f : Fin 4 ↪ Fin 6, ∏ i, (1 + t (i, f i))) = 360) ∧ Module.finrank ℂ L = 7 := by
  refine ⟨LinearMap.range PEqualNP.Outside.Gct208.phi, ?_, ?_⟩
  · intro t ht
    obtain ⟨c, rfl⟩ := ht
    exact PEqualNP.Outside.Gct208.level c
  · rw [LinearMap.finrank_range_of_inj PEqualNP.Outside.Gct208.phi_inj]
    simp
