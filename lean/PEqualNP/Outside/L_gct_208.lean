import Mathlib
import PEqualNP.Defs

private noncomputable def shape208 (x : Fin 7 → ℂ) : Fin 4 × Fin 6 → ℂ :=
  fun p => ![![-x 0 - x 1 - x 2 - x 3 - x 4, x 0, x 1, x 2, x 3, x 4],
    ![x 5, 0, 0, 0, 0, 0], ![x 6, 0, 0, 0, 0, 0],
    ![-x 5 - x 6, 0, 0, 0, 0, 0]] p.1 p.2

private noncomputable def map208 : (Fin 7 → ℂ) →ₗ[ℂ] (Fin 4 × Fin 6 → ℂ) where
  toFun := shape208
  map_add' x y := by
    funext p
    rcases p with ⟨i, j⟩
    fin_cases i <;> fin_cases j <;> simp [shape208] <;> ring
  map_smul' a x := by
    funext p
    rcases p with ⟨i, j⟩
    fin_cases i <;> fin_cases j <;> simp [shape208, mul_sub, mul_neg]

private theorem map208_injective : Function.Injective map208 := by
  intro x y h
  funext i
  fin_cases i
  · exact congrFun h (0, 1)
  · exact congrFun h (0, 2)
  · exact congrFun h (0, 3)
  · exact congrFun h (0, 4)
  · exact congrFun h (0, 5)
  · exact congrFun h (1, 0)
  · exact congrFun h (2, 0)

private theorem sum208_cons (n : ℕ) (H : (Fin (n + 1) → Fin 6) → ℂ) :
    (∑ f, H f) = ∑ a, ∑ b, H (Fin.cons a b) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n + 1) => Fin 6))
    _ _ (fun _ => rfl)).symm

private theorem sum208_embeddings (H : (Fin 4 → Fin 6) → ℂ) :
    (∑ f : Fin 4 ↪ Fin 6, H f) =
      ∑ f : Fin 4 → Fin 6, if Function.Injective f then H f else 0 := by
  classical
  let e : (Fin 4 ↪ Fin 6) ≃ {f : Fin 4 → Fin 6 // Function.Injective f} :=
    { toFun := fun f => ⟨f, f.injective⟩
      invFun := fun f => ⟨f.1, f.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  calc
    _ = ∑ f : {f : Fin 4 → Fin 6 // Function.Injective f}, H f.1 :=
      Fintype.sum_equiv e _ _ (fun _ => rfl)
    _ = ∑ f ∈ Finset.univ.filter Function.Injective, H f :=
      (Finset.sum_subtype _ (by simp) H).symm
    _ = _ := by rw [Finset.sum_filter]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
private theorem sum208_shape (x : Fin 7 → ℂ) :
    (∑ f : Fin 4 ↪ Fin 6, ∏ i, (1 + shape208 x (i, f i))) = 360 := by
  classical
  rw [sum208_embeddings (fun f => ∏ i, (1 + shape208 x (i, f i)))]
  simp only [sum208_cons, Fintype.sum_unique]
  norm_num [Fin.sum_univ_succ, Fin.prod_univ_succ, Function.Injective,
    Fin.forall_fin_succ, shape208]
  ring

theorem PEqualNP.Outside.L_gct_208 :
    ∃ L : Submodule ℂ (Fin 4 × Fin 6 → ℂ), (∀ t ∈ L, (∑ f : Fin 4 ↪ Fin 6, ∏ i, (1 + t (i, f i))) = 360) ∧ Module.finrank ℂ L = 7 := by
  refine ⟨LinearMap.range map208, ?_, ?_⟩
  · rintro t ⟨x, rfl⟩
    exact sum208_shape x
  · rw [LinearMap.finrank_range_of_inj map208_injective, Module.finrank_fin_fun]
