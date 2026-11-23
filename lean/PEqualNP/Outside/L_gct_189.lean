import Mathlib

/-!
# A level space of 5 x 5 matrices of dimension 7 (L-gct-189)

The witness is the hook space: matrices supported on row `0` and column `0`, whose row-`0`
entries sum to zero and whose column-`0` entries below the corner sum to zero. Seven free
parameters `x 0, ..., x 6` describe it:

* row `0`: `-(x0 + x1 + x2 + x3), x0, x1, x2, x3`;
* column `0` below the corner: `x4, x5, x6, -(x4 + x5 + x6)`;
* every other entry is zero.

For a matrix `t` supported on the hook, the sum over permutations of `∏ (1 + t (i, σ i))`
equals `4! (1 + v0) + 3! (4 + V) (4 + C)`, with `v0` the corner, `V` the rest of row `0` and
`C` the rest of column `0`. On the hook space `v0 + V = 0` and `C = 0`, so the value is `120`.
The proof expands the sum over all permutations and closes with `ring`.
-/

namespace Gap189

/-- The hook matrix with parameters `x`. -/
def T (x : Fin 7 → ℂ) : Fin 5 × Fin 5 → ℂ := fun p =>
  if p.1 = 0 then
    (if p.2 = 0 then -(x 0 + x 1 + x 2 + x 3)
     else if p.2 = 1 then x 0 else if p.2 = 2 then x 1 else if p.2 = 3 then x 2 else x 3)
  else if p.2 = 0 then
    (if p.1 = 1 then x 4 else if p.1 = 2 then x 5 else if p.1 = 3 then x 6
     else -(x 4 + x 5 + x 6))
  else 0

/-- `T` as a linear map. -/
def Tl : (Fin 7 → ℂ) →ₗ[ℂ] (Fin 5 × Fin 5 → ℂ) where
  toFun := T
  map_add' x y := by
    funext p
    simp only [T, Pi.add_apply]
    split_ifs <;> ring
  map_smul' c x := by
    funext p
    simp only [T, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

theorem Tl_injective : Function.Injective Tl := by
  intro x y h
  have h' : ∀ p, T x p = T y p := fun p => congrFun h p
  funext k
  fin_cases k
  · simpa [T] using h' (0, 1)
  · simpa [T] using h' (0, 2)
  · simpa [T] using h' (0, 3)
  · simpa [T] using h' (0, 4)
  · simpa [T] using h' (1, 0)
  · simpa [T] using h' (2, 0)
  · simpa [T] using h' (3, 0)

theorem sum_perm_succ {n : ℕ} (g : Equiv.Perm (Fin (n + 1)) → ℂ) :
    ∑ σ, g σ = ∑ a : Fin (n + 1), ∑ τ : Equiv.Perm (Fin n),
      g (Equiv.Perm.decomposeFin.symm (a, τ)) := by
  rw [← Equiv.Perm.decomposeFin.symm.sum_comp, Fintype.sum_prod_type]

/-- The sum over embeddings is the sum over permutations. -/
theorem sum_emb (g : (Fin 5 → Fin 5) → ℂ) :
    ∑ f : Fin 5 ↪ Fin 5, g f = ∑ σ : Equiv.Perm (Fin 5), g σ := by
  let e : Equiv.Perm (Fin 5) ≃ (Fin 5 ↪ Fin 5) :=
    { toFun := fun σ => σ.toEmbedding
      invFun := fun f => Equiv.ofBijective f f.injective.bijective_of_finite
      left_inv := fun σ => by ext; rfl
      right_inv := fun f => by ext; rfl }
  rw [← e.sum_comp]
  rfl

theorem level (x : Fin 7 → ℂ) :
    (∑ f : Fin 5 ↪ Fin 5, ∏ i, (1 + T x (i, f i))) = 120 := by
  rw [sum_emb (fun f => ∏ i, (1 + T x (i, f i)))]
  rw [sum_perm_succ]
  simp only [sum_perm_succ (n := 3), sum_perm_succ (n := 2), sum_perm_succ (n := 1),
    sum_perm_succ (n := 0)]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.prod_univ_succ, Fin.prod_univ_zero,
    Equiv.Perm.decomposeFin_symm_apply_zero, Equiv.Perm.decomposeFin_symm_apply_succ,
    Fintype.sum_unique]
  simp +decide [T]
  ring

end Gap189

theorem PEqualNP.Outside.L_gct_189 : ∃ L : Submodule ℂ (Fin 5 × Fin 5 → ℂ), (∀ t ∈ L, (∑ f : Fin 5 ↪ Fin 5, ∏ i, (1 + t (i, f i))) = 120) ∧ Module.finrank ℂ L = 7 := by
  refine ⟨LinearMap.range Gap189.Tl, ?_, ?_⟩
  · rintro t ⟨x, rfl⟩
    exact Gap189.level x
  · rw [LinearMap.finrank_range_of_inj Gap189.Tl_injective, Module.finrank_fin_fun]
