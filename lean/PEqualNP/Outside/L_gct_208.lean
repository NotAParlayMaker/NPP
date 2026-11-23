import PEqualNP.Defs

namespace PEqualNP.Outside.L_gct_208_aux

open Finset

private theorem sum_fun_succ {n : ℕ} (G : (Fin (n + 1) → Fin 6) → ℂ) :
    (∑ g, G g) = ∑ a : Fin 6, ∑ g : Fin n → Fin 6, G (Fin.cons a g) := by
  rw [← (Fin.consEquiv fun _ => Fin 6).sum_comp, Fintype.sum_prod_type]
  rfl

private theorem inj4 (a b c d : Fin 6) :
    Function.Injective ![a, b, c, d] ↔
      (a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d) := by
  constructor
  · intro h
    refine ⟨fun e => ?_, fun e => ?_, fun e => ?_, fun e => ?_, fun e => ?_, fun e => ?_⟩
    · exact absurd (h (a₁ := 0) (a₂ := 1) (by simp [e])) (by decide)
    · exact absurd (h (a₁ := 0) (a₂ := 2) (by simp [e])) (by decide)
    · exact absurd (h (a₁ := 0) (a₂ := 3) (by simp [e])) (by decide)
    · exact absurd (h (a₁ := 1) (a₂ := 2) (by simp [e])) (by decide)
    · exact absurd (h (a₁ := 1) (a₂ := 3) (by simp [e])) (by decide)
    · exact absurd (h (a₁ := 2) (a₂ := 3) (by simp [e])) (by decide)
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩ i j hij
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]

private theorem sum_emb46 (F : (Fin 4 → Fin 6) → ℂ) :
    (∑ f : Fin 4 ↪ Fin 6, F f) =
      ∑ a : Fin 6, ∑ b : Fin 6, ∑ c : Fin 6, ∑ d : Fin 6,
        if a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d then F ![a, b, c, d] else 0 := by
  classical
  have h1 : (∑ f : Fin 4 ↪ Fin 6, F f) =
      ∑ g : Fin 4 → Fin 6, if Function.Injective g then F g else 0 := by
    rw [← Finset.sum_filter]
    rw [Finset.sum_subtype (univ.filter Function.Injective) (p := Function.Injective) (by simp) F]
    exact (Fintype.sum_equiv (Equiv.subtypeInjectiveEquivEmbedding (Fin 4) (Fin 6)).symm _ _
      (fun _ => rfl))
  rw [h1, sum_fun_succ]
  refine sum_congr rfl fun a _ => ?_
  rw [sum_fun_succ]
  refine sum_congr rfl fun b _ => ?_
  rw [sum_fun_succ]
  refine sum_congr rfl fun c _ => ?_
  rw [sum_fun_succ]
  refine sum_congr rfl fun d _ => ?_
  rw [Fintype.sum_unique]
  have e : ∀ z : Fin 0 → Fin 6,
      (Fin.cons a (Fin.cons b (Fin.cons c (Fin.cons d z))) : Fin 4 → Fin 6) = ![a, b, c, d] := by
    intro z; funext i; fin_cases i <;> rfl
  refine (congrArg (fun g : Fin 4 → Fin 6 => if Function.Injective g then F g else 0)
    (e _)).trans ?_
  simp only [inj4]

private def pt (x : Fin 4 → ℂ) (y : Fin 3 → ℂ) : Fin 4 × Fin 6 → ℂ := fun p =>
  ![![-(y 0 + y 1 + y 2), x 0, x 1, x 2, x 3, -(x 0 + x 1 + x 2 + x 3)],
    ![y 0, 0, 0, 0, 0, 0], ![y 1, 0, 0, 0, 0, 0], ![y 2, 0, 0, 0, 0, 0]] p.1 p.2

private def ptLin : ((Fin 4 → ℂ) × (Fin 3 → ℂ)) →ₗ[ℂ] (Fin 4 × Fin 6 → ℂ) where
  toFun v := pt v.1 v.2
  map_add' v w := by
    funext ⟨i, j⟩
    fin_cases i <;> fin_cases j <;> simp [pt] <;> ring
  map_smul' c v := by
    funext ⟨i, j⟩
    fin_cases i <;> fin_cases j <;> simp [pt] <;> ring

private theorem ptLin_injective : Function.Injective ptLin := by
  rintro ⟨x, y⟩ ⟨x', y'⟩ h
  have h' : pt x y = pt x' y' := h
  have hx : x = x' := by
    funext j
    fin_cases j
    · simpa [pt] using congrFun h' (0, 1)
    · simpa [pt] using congrFun h' (0, 2)
    · simpa [pt] using congrFun h' (0, 3)
    · simpa [pt] using congrFun h' (0, 4)
  have hy : y = y' := by
    funext i
    fin_cases i
    · simpa [pt] using congrFun h' (1, 0)
    · simpa [pt] using congrFun h' (2, 0)
    · simpa [pt] using congrFun h' (3, 0)
  rw [hx, hy]

set_option maxHeartbeats 4000000 in
private theorem eval_pt (x : Fin 4 → ℂ) (y : Fin 3 → ℂ) :
    (∑ f : Fin 4 ↪ Fin 6, ∏ i, (1 + pt x y (i, f i))) = 360 := by
  rw [sum_emb46 (fun g => ∏ i, (1 + pt x y (i, g i)))]
  simp (maxSteps := 50000000) [Fin.sum_univ_succ, Fin.prod_univ_succ, pt]
  ring

theorem witness :
    ∃ L : Submodule ℂ (Fin 4 × Fin 6 → ℂ),
      (∀ t ∈ L, (∑ f : Fin 4 ↪ Fin 6, ∏ i, (1 + t (i, f i))) = 360) ∧
      Module.finrank ℂ L = 7 := by
  refine ⟨LinearMap.range ptLin, ?_, ?_⟩
  · rintro _ ⟨⟨x, y⟩, rfl⟩
    exact eval_pt x y
  · rw [LinearMap.finrank_range_of_inj ptLin_injective, Module.finrank_prod,
      Module.finrank_fin_fun, Module.finrank_fin_fun]

end PEqualNP.Outside.L_gct_208_aux

theorem PEqualNP.Outside.L_gct_208 : ∃ L : Submodule ℂ (Fin 4 × Fin 6 → ℂ), (∀ t ∈ L, (∑ f : Fin 4 ↪ Fin 6, ∏ i, (1 + t (i, f i))) = 360) ∧ Module.finrank ℂ L = 7 :=
  PEqualNP.Outside.L_gct_208_aux.witness
