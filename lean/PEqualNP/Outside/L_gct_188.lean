import Mathlib
import PEqualNP.Defs

/-! The witness is the hook: matrices supported on row `0` and column `0`, with the five entries
`t (0, 1..5)` free and `t (0, 0)` minus their sum, and the column entries `t (1, 0)`, `t (2, 0)`
free and `t (3, 0)` minus their sum. The total sum of entries is zero, every 2 x 2
subpermanent sum is (row sum off the corner) * (column sum below the corner) = 0, and no larger
subpermanent fits in a hook. The sum over injections is expanded by brute force. -/

namespace PEqualNP.Outside.L_gct_188_aux

/-- The hook matrix with parameters `c`. -/
def hk (c : Fin 7 → ℂ) : Fin 4 → Fin 6 → ℂ :=
  ![![-(c 0 + c 1 + c 2 + c 3 + c 4), c 0, c 1, c 2, c 3, c 4],
    ![c 5, 0, 0, 0, 0, 0],
    ![c 6, 0, 0, 0, 0, 0],
    ![-(c 5 + c 6), 0, 0, 0, 0, 0]]

/-- The hook as a linear map from the parameters. -/
def phi : (Fin 7 → ℂ) →ₗ[ℂ] (Fin 4 × Fin 6 → ℂ) where
  toFun c := fun p => hk c p.1 p.2
  map_add' a b := by
    funext ⟨i, j⟩
    fin_cases i <;> fin_cases j <;> simp [hk] <;> ring
  map_smul' r a := by
    funext ⟨i, j⟩
    fin_cases i <;> fin_cases j <;> simp [hk] <;> ring

lemma phi_injective : Function.Injective phi := by
  intro a b h
  have e : ∀ p : Fin 4 × Fin 6, hk a p.1 p.2 = hk b p.1 p.2 := fun p => congrFun h p
  funext k
  fin_cases k
  · simpa [hk] using e (0, 1)
  · simpa [hk] using e (0, 2)
  · simpa [hk] using e (0, 3)
  · simpa [hk] using e (0, 4)
  · simpa [hk] using e (0, 5)
  · simpa [hk] using e (1, 0)
  · simpa [hk] using e (2, 0)

lemma injective_vec4_iff {α : Type*} (a b c d : α) :
    Function.Injective ![a, b, c, d] ↔
      a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro e; exact absurd (h (a₁ := 0) (a₂ := 1) e) (by decide)
    · intro e; exact absurd (h (a₁ := 0) (a₂ := 2) e) (by decide)
    · intro e; exact absurd (h (a₁ := 0) (a₂ := 3) e) (by decide)
    · intro e; exact absurd (h (a₁ := 1) (a₂ := 2) e) (by decide)
    · intro e; exact absurd (h (a₁ := 1) (a₂ := 3) e) (by decide)
    · intro e; exact absurd (h (a₁ := 2) (a₂ := 3) e) (by decide)
  · rintro ⟨hab, hac, had, hbc, hbd, hcd⟩ i j hij
    fin_cases i <;> fin_cases j <;> simp_all

lemma sum_emb_fin4_eq_ind {α : Type*} [Fintype α] [DecidableEq α]
    (F : α → α → α → α → ℂ) :
    ∑ f : Fin 4 ↪ α, F (f 0) (f 1) (f 2) (f 3) =
      ∑ a : α, ∑ b : α, ∑ c : α, ∑ d : α,
        (if a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d then (1 : ℂ) else 0) * F a b c d := by
  let e1 : { f : Fin 4 → α // Function.Injective f } ≃ (Fin 4 ↪ α) :=
    { toFun := fun f => ⟨f.1, f.2⟩
      invFun := fun f => ⟨f, f.injective⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let e2 : (Fin 4 → α) ≃ α × α × α × α :=
    { toFun := fun f => (f 0, f 1, f 2, f 3)
      invFun := fun ⟨a, b, c, d⟩ => ![a, b, c, d]
      left_inv := fun f => by ext i; fin_cases i <;> rfl
      right_inv := fun ⟨_, _, _, _⟩ => rfl }
  have h1 : ∑ f : Fin 4 ↪ α, F (f 0) (f 1) (f 2) (f 3) =
      ∑ f : { f : Fin 4 → α // Function.Injective f }, F (f.1 0) (f.1 1) (f.1 2) (f.1 3) := by
    exact (Fintype.sum_equiv e1 _ _ (fun _ => rfl)).symm
  have h2 : ∑ f : { f : Fin 4 → α // Function.Injective f }, F (f.1 0) (f.1 1) (f.1 2) (f.1 3) =
      ∑ f : Fin 4 → α, if Function.Injective f then F (f 0) (f 1) (f 2) (f 3) else 0 := by
    rw [← Finset.sum_filter]
    refine Finset.sum_bij (fun f _ => f.1) ?_ ?_ ?_ ?_
    · intro f _; simp [f.2]
    · intro f₁ _ f₂ _ h; exact Subtype.ext h
    · intro f hf
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
      exact ⟨⟨f, hf⟩, Finset.mem_univ _, rfl⟩
    · intro _ _; rfl
  have h3 : ∑ f : Fin 4 → α, (if Function.Injective f then F (f 0) (f 1) (f 2) (f 3) else 0) =
      ∑ x : α × α × α × α,
        if Function.Injective ![x.1, x.2.1, x.2.2.1, x.2.2.2] then
          F x.1 x.2.1 x.2.2.1 x.2.2.2
        else 0 := by
    exact Fintype.sum_equiv e2 _ _ (fun f => by
      have hf : ![f 0, f 1, f 2, f 3] = f := e2.left_inv f
      simp [e2, hf])
  rw [h1, h2, h3]
  simp only [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  simp only [injective_vec4_iff]
  split_ifs <;> simp

/-- The value on the hook, by brute force over the 6 ^ 4 tuples. -/
lemma hook_sum (c : Fin 7 → ℂ) :
    ∑ a : Fin 6, ∑ b : Fin 6, ∑ d : Fin 6, ∑ e : Fin 6,
      (if a ≠ b ∧ a ≠ d ∧ a ≠ e ∧ b ≠ d ∧ b ≠ e ∧ d ≠ e then (1 : ℂ) else 0) *
        ((1 + hk c 0 a) * (1 + hk c 1 b) * (1 + hk c 2 d) * (1 + hk c 3 e)) = 360 := by
  simp only [Fin.sum_univ_six, hk]
  simp
  ring

end PEqualNP.Outside.L_gct_188_aux

open PEqualNP.Outside.L_gct_188_aux in
theorem PEqualNP.Outside.L_gct_188 : ∃ L : Submodule ℂ (Fin 4 × Fin 6 → ℂ), (∀ t ∈ L, (∑ f : Fin 4 ↪ Fin 6, ∏ i, (1 + t (i, f i))) = 360) ∧ Module.finrank ℂ L = 7
 := by
  refine ⟨LinearMap.range phi, ?_, ?_⟩
  · rintro t ⟨c, rfl⟩
    have h := sum_emb_fin4_eq_ind
      (fun a b d e => (1 + hk c 0 a) * (1 + hk c 1 b) * (1 + hk c 2 d) * (1 + hk c 3 e))
    simp only [Fin.prod_univ_four]
    rw [show (∑ f : Fin 4 ↪ Fin 6, (1 + phi c (0, f 0)) * (1 + phi c (1, f 1)) *
        (1 + phi c (2, f 2)) * (1 + phi c (3, f 3))) =
        ∑ f : Fin 4 ↪ Fin 6, (1 + hk c 0 (f 0)) * (1 + hk c 1 (f 1)) *
        (1 + hk c 2 (f 2)) * (1 + hk c 3 (f 3)) from rfl, h]
    exact hook_sum c
  · rw [LinearMap.finrank_range_of_inj phi_injective]
    simp
