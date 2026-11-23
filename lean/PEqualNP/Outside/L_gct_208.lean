import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_gct_208_aux

open Finset

def pt (v : Fin 7 → ℂ) : Fin 4 × Fin 6 → ℂ := fun p =>
  ![![-(v 4 + v 5 + v 6), v 0, v 1, v 2, v 3, -(v 0 + v 1 + v 2 + v 3)],
    ![v 4, 0, 0, 0, 0, 0], ![v 5, 0, 0, 0, 0, 0], ![v 6, 0, 0, 0, 0, 0]] p.1 p.2

def ptLin : (Fin 7 → ℂ) →ₗ[ℂ] (Fin 4 × Fin 6 → ℂ) where
  toFun := pt
  map_add' v w := by
    funext ⟨i, j⟩
    fin_cases i <;> fin_cases j <;> simp [pt] <;> ring
  map_smul' c v := by
    funext ⟨i, j⟩
    fin_cases i <;> fin_cases j <;> simp [pt] <;> ring

lemma ptLin_injective : Function.Injective ptLin := by
  intro v w h
  have h' : pt v = pt w := h
  funext k
  fin_cases k
  · simpa [pt] using congrFun h' (0, 1)
  · simpa [pt] using congrFun h' (0, 2)
  · simpa [pt] using congrFun h' (0, 3)
  · simpa [pt] using congrFun h' (0, 4)
  · simpa [pt] using congrFun h' (1, 0)
  · simpa [pt] using congrFun h' (2, 0)
  · simpa [pt] using congrFun h' (3, 0)

lemma sum_emb (g : (Fin 4 → Fin 6) → ℂ) :
    (∑ f : Fin 4 ↪ Fin 6, g f) =
      ∑ x : Fin 4 → Fin 6, if Function.Injective x then g x else 0 := by
  rw [← Finset.sum_filter, Finset.sum_subtype (univ.filter Function.Injective)
    (p := Function.Injective) (by simp)]
  exact Fintype.sum_equiv ⟨fun f => ⟨f, f.injective⟩, fun x => ⟨x.1, x.2⟩,
    fun _ => rfl, fun _ => rfl⟩ _ _ (fun _ => rfl)

lemma sum_fun (F : (Fin 4 → Fin 6) → ℂ) : (∑ x : Fin 4 → Fin 6, F x) =
    ∑ a : Fin 6, ∑ b : Fin 6, ∑ c : Fin 6, ∑ d : Fin 6, F ![a, b, c, d] := by
  rw [← (Fin.consEquiv _).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← (Fin.consEquiv _).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← (Fin.consEquiv _).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← (Fin.consEquiv _).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Fintype.sum_unique]
  simp only [Fin.consEquiv_apply]
  congr 1

lemma inj_iff (a b c d : Fin 6) : Function.Injective ![a, b, c, d] ↔
    (a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro e
    · have := @h 0 1 (by simpa using e); simp at this
    · have := @h 0 2 (by simpa using e); simp at this
    · have := @h 0 3 (by simpa using e); simp at this
    · have := @h 1 2 (by simpa using e); simp at this
    · have := @h 1 3 (by simpa using e); simp at this
    · have := @h 2 3 (by simpa using e); simp at this
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩ i j e
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]

lemma eval_pt (v : Fin 7 → ℂ) :
    (∑ f : Fin 4 ↪ Fin 6, ∏ i, (1 + pt v (i, f i))) = 360 := by
  rw [sum_emb (fun x => ∏ i, (1 + pt v (i, x i))), sum_fun]
  simp only [inj_iff, Fin.prod_univ_four, Fin.sum_univ_six]
  simp [pt]
  ring

theorem witness : ∃ L : Submodule ℂ (Fin 4 × Fin 6 → ℂ),
    (∀ t ∈ L, (∑ f : Fin 4 ↪ Fin 6, ∏ i, (1 + t (i, f i))) = 360) ∧
      Module.finrank ℂ L = 7 := by
  refine ⟨LinearMap.range ptLin, ?_, ?_⟩
  · rintro _ ⟨v, rfl⟩
    exact eval_pt v
  · rw [LinearMap.finrank_range_of_inj ptLin_injective, Module.finrank_fin_fun]

end PEqualNP.Outside.L_gct_208_aux

theorem PEqualNP.Outside.L_gct_208 : ∃ L : Submodule ℂ (Fin 4 × Fin 6 → ℂ), (∀ t ∈ L, (∑ f : Fin 4 ↪ Fin 6, ∏ i, (1 + t (i, f i))) = 360) ∧ Module.finrank ℂ L = 7 :=
  PEqualNP.Outside.L_gct_208_aux.witness
