import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_gct_194_aux

open scoped BigOperators

def embOf (p : Fin 5) (σ : Equiv.Perm (Fin 4)) : Fin 4 ↪ Fin 5 where
  toFun := fun j => p.succAbove (σ j)
  inj' := fun _ _ h => σ.injective (Fin.succAbove_right_injective h)

lemma range_embOf (p : Fin 5) (σ : Equiv.Perm (Fin 4)) :
    Set.range (embOf p σ : Fin 4 → Fin 5) = {p}ᶜ := by
  ext x
  simp only [Set.mem_range, Set.mem_compl_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨j, rfl⟩
    exact Fin.succAbove_ne p (σ j)
  · intro hx
    have hxr : x ∈ Set.range p.succAbove := by
      rw [Fin.range_succAbove]
      simpa using hx
    obtain ⟨k, rfl⟩ := hxr
    obtain ⟨j, rfl⟩ := σ.surjective k
    exact ⟨j, rfl⟩

lemma embOf_injective :
    Function.Injective (fun q : Fin 5 × Equiv.Perm (Fin 4) => embOf q.1 q.2) := by
  rintro ⟨p, σ⟩ ⟨p', σ'⟩ h
  change embOf p σ = embOf p' σ' at h
  have hrange : Set.range (embOf p σ : Fin 4 → Fin 5) =
      Set.range (embOf p' σ' : Fin 4 → Fin 5) := by rw [h]
  have hp : p = p' := by
    by_contra hne
    have hin : p' ∈ Set.range (embOf p σ : Fin 4 → Fin 5) := by
      rw [range_embOf]
      exact fun hpp => hne hpp.symm
    have hout : p' ∉ Set.range (embOf p' σ' : Fin 4 → Fin 5) := by
      rw [range_embOf]
      simp
    exact hout (hrange ▸ hin)
  subst hp
  have hσ : σ = σ' := by
    refine Equiv.ext fun j => ?_
    have hxj : p.succAbove (σ j) = p.succAbove (σ' j) := by
      have h' := congrArg (fun e : Fin 4 ↪ Fin 5 => e j) h
      change p.succAbove (σ j) = p.succAbove (σ' j) at h'
      exact h'
    exact Fin.succAbove_right_injective hxj
  subst hσ
  rfl

lemma embOf_bijective :
    Function.Bijective (fun q : Fin 5 × Equiv.Perm (Fin 4) => embOf q.1 q.2) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨embOf_injective, ?_⟩
  simp [Fintype.card_prod, Fintype.card_perm, Fintype.card_embedding_eq]
  norm_num

lemma sum_embeddings (F : (Fin 4 ↪ Fin 5) → ℂ) :
    (∑ f : Fin 4 ↪ Fin 5, F f) =
      ∑ q : Fin 5 × Equiv.Perm (Fin 4), F (embOf q.1 q.2) := by
  exact (Fintype.sum_bijective (fun q : Fin 5 × Equiv.Perm (Fin 4) => embOf q.1 q.2)
    embOf_bijective (fun q => F (embOf q.1 q.2)) F (fun q => rfl)).symm

def M (c d : ℂ) (row : Fin 5) (col : Fin 4) : ℂ :=
  if row.val = 4 then d * (if col.val = 0 then (1 : ℂ) else if col.val = 1 then -1 else 0)
  else c * (if col.val = row.val then (1 : ℂ)
            else if col.val = (row.val + 1) % 4 then Complex.I
            else if col.val = (row.val + 2) % 4 then -Complex.I else -1)

def tuple (a b e f : ℕ) : Fin 4 → Fin 4 :=
  ![Fin.ofNat 4 a, Fin.ofNat 4 b, Fin.ofNat 4 e, Fin.ofNat 4 f]

lemma sumPerm4 : ∀ (g : Equiv.Perm (Fin 4) → ℂ), ∑ σ, g σ =
    ∑ a : Fin 4, ∑ b : Fin 3, ∑ c : Fin 2, ∑ d : Fin 1,
      g (Equiv.Perm.decomposeFin.symm (a, Equiv.Perm.decomposeFin.symm (b,
        Equiv.Perm.decomposeFin.symm (c, Equiv.Perm.decomposeFin.symm (d, 1))))) := by
  intro g
  rw [← Equiv.sum_comp Equiv.Perm.decomposeFin.symm, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Equiv.sum_comp Equiv.Perm.decomposeFin.symm, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Equiv.sum_comp Equiv.Perm.decomposeFin.symm, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Equiv.sum_comp Equiv.Perm.decomposeFin.symm, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Fintype.sum_unique]
  rfl

lemma key : ∀ F : ℕ → ℕ → ℕ → ℕ → ℂ,
    ∑ σ : Equiv.Perm (Fin 4), F (σ 0).val (σ 1).val (σ 2).val (σ 3).val =
    (((F 0 1 2 3 + F 0 1 3 2) + ((F 0 2 1 3 + F 0 2 3 1) + (F 0 3 2 1 + F 0 3 1 2))) + (((F 1 0 2 3 + F 1 0 3 2) + ((F 1 2 0 3 + F 1 2 3 0) + (F 1 3 2 0 + F 1 3 0 2))) + (((F 2 1 0 3 + F 2 1 3 0) + ((F 2 0 1 3 + F 2 0 3 1) + (F 2 3 0 1 + F 2 3 1 0))) + ((F 3 1 2 0 + F 3 1 0 2) + ((F 3 2 1 0 + F 3 2 0 1) + (F 3 0 2 1 + F 3 0 1 2)))))) := by
  intro F
  rw [sumPerm4]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  rfl

theorem main : ∀ c d : ℂ,
    (∑ f : Fin 4 ↪ Fin 5, ∏ j : Fin 4,
      (1 + (if (f j).val = 4 then d * (if j.val = 0 then (1 : ℂ) else if j.val = 1 then -1 else 0)
            else c * (if j.val = (f j).val then (1 : ℂ)
                      else if j.val = ((f j).val + 1) % 4 then Complex.I
                      else if j.val = ((f j).val + 2) % 4 then -Complex.I else -1)))) = 120 := by
  intro c d
  change (∑ f : Fin 4 ↪ Fin 5, ∏ j : Fin 4, (1 + M c d (f j) j)) = 120
  rw [sum_embeddings]
  rw [Fintype.sum_prod_type]
  change (∑ x : Fin 5, ∑ y : Equiv.Perm (Fin 4),
    ∏ j : Fin 4, (1 + M c d (x.succAbove (y j)) j)) = 120
  have h : ∀ (p : Fin 5) (σ : Equiv.Perm (Fin 4)),
      (∏ j : Fin 4, (1 + M c d (p.succAbove (σ j)) j)) =
      (fun a b e f => ∏ j : Fin 4,
        (1 + M c d (p.succAbove (tuple a b e f j)) j))
        (σ 0).val (σ 1).val (σ 2).val (σ 3).val := by
    intro p σ
    congr 1
    funext j
    fin_cases j <;> simp [tuple]
  simp_rw [h]
  change (∑ x : Fin 5, ∑ y : Equiv.Perm (Fin 4),
    (fun a b e f => ∏ j : Fin 4, (1 + M c d (x.succAbove (tuple a b e f j)) j))
      (y 0).val (y 1).val (y 2).val (y 3).val) = 120
  conv_lhs =>
    arg 2
    ext x
    rw [key (fun a b e f => ∏ j : Fin 4,
      (1 + M c d (x.succAbove (tuple a b e f j)) j))]
  rw [Fin.sum_univ_five]
  simp only [Fin.prod_univ_four]
  simp +decide [M]
  linear_combination (2*c^2*(Complex.I^2*c^2 - 4*Complex.I*c^2 + c^2 + 12)) * Complex.I_sq


end PEqualNP.Outside.L_gct_194_aux

theorem PEqualNP.Outside.L_gct_194 : ∀ c d : ℂ, (∑ f : Fin 4 ↪ Fin 5, ∏ j : Fin 4, (1 + (if (f j).val = 4 then d * (if j.val = 0 then (1 : ℂ) else if j.val = 1 then -1 else 0) else c * (if j.val = (f j).val then (1 : ℂ) else if j.val = ((f j).val + 1) % 4 then Complex.I else if j.val = ((f j).val + 2) % 4 then -Complex.I else -1)))) = 120 :=
  PEqualNP.Outside.L_gct_194_aux.main
