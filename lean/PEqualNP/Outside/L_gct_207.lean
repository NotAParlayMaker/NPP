import Mathlib
import PEqualNP.Defs

namespace L207low
open Finset

private theorem restrict_sum {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) (g : β → ℂ)
    (hg : ∀ b, (∀ a, f a ≠ b) → g b = 0) : ∑ b, g b = ∑ a, g (f a) := by
  classical
  calc
    _ = ∑ b ∈ univ.image f, g b := by
      symm
      refine Finset.sum_subset (Finset.subset_univ _) fun b _ hb => hg b ?_
      intro a e
      exact hb (Finset.mem_image.mpr ⟨a,Finset.mem_univ _,e⟩)
    _ = _ := Finset.sum_image (fun _ _ _ _ e => hf e)

private noncomputable def term (k : ℕ) (t : Fin 5 × Fin 7 → ℂ)
    (R : Finset (Fin 5)) (C : Finset (Fin 7)) : ℂ :=
  if h : R.card = k ∧ C.card = k then
    Matrix.permanent (Matrix.of fun a b => t (R.orderEmbOfFin h.1 a,C.orderEmbOfFin h.2 b))
  else 0

private theorem low₁ (t : Fin 5 × Fin 7 → ℂ) :
    (∑ R : Finset (Fin 5), ∑ C : Finset (Fin 7), if h : R.card = 1 ∧ C.card = 1 then
      Matrix.permanent (Matrix.of fun a b => t (R.orderEmbOfFin h.1 a,C.orderEmbOfFin h.2 b))
      else 0) = ∑ i, ∑ j, t (i,j) := by
  change (∑ R, ∑ C, term 1 t R C) = _
  rw [restrict_sum (fun i : Fin 5 => ({i} : Finset _)) Finset.singleton_injective]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [restrict_sum (fun j : Fin 7 => ({j} : Finset _)) Finset.singleton_injective]
    · refine Finset.sum_congr rfl fun j _ => ?_
      simp [term,Matrix.permanent_unique,Finset.orderEmbOfFin_singleton]
    · intro C hC
      have hn : C.card ≠ 1 := by
        rintro hc
        obtain ⟨j,rfl⟩ := Finset.card_eq_one.mp hc
        exact hC j rfl
      simp [term,hn]
  · intro R hR
    have hn : R.card ≠ 1 := by
      rintro hr
      obtain ⟨i,rfl⟩ := Finset.card_eq_one.mp hr
      exact hR i rfl
    simp [term,hn]

private def mark {n : ℕ} (i : Fin n) : Finset (Fin (n+1)) := {i.castSucc,Fin.last n}

private theorem card_mark {n : ℕ} (i : Fin n) : (mark i).card = 2 := by
  simp [mark,Fin.castSucc_ne_last]

private theorem mark_points {n : ℕ} (i : Fin n) :
    (mark i).orderEmbOfFin (card_mark i) 0 = i.castSucc ∧
    (mark i).orderEmbOfFin (card_mark i) 1 = Fin.last n := by
  let e := (mark i).orderEmbOfFin (card_mark i)
  have h0 : e 0 ∈ mark i := Finset.orderEmbOfFin_mem _ _ _
  have h1 : e 1 ∈ mark i := Finset.orderEmbOfFin_mem _ _ _
  have hlt : e 0 < e 1 := e.strictMono (by decide)
  simp only [mark,Finset.mem_insert,Finset.mem_singleton] at h0 h1
  change e 0 = _ ∧ e 1 = _
  have hn : ¬ Fin.last n < i.castSucc := not_lt_of_ge (Fin.le_last _)
  rcases h0 with h0|h0 <;> rcases h1 with h1|h1 <;> simp_all

private theorem mark_inj {n : ℕ} : Function.Injective (@mark n) := by
  intro i j e
  have hi : i.castSucc ∈ mark j := e ▸ (Finset.mem_insert_self _ _)
  simpa [mark,Fin.castSucc_ne_last] using hi

private theorem mark_exists {n : ℕ} {s : Finset (Fin (n+1))} (hs : s.card = 2)
    (hl : Fin.last n ∈ s) : ∃ i : Fin n, mark i = s := by
  obtain ⟨x,y,hxy,rfl⟩ := Finset.card_eq_two.mp hs
  rcases Finset.mem_insert.mp hl with hx | hy
  · subst x
    have hy' : y ≠ Fin.last n := hxy.symm
    obtain ⟨i,hi⟩ := Fin.exists_castSucc_eq.mpr hy'
    refine ⟨i,?_⟩
    rw [mark,hi,Finset.pair_comm]
  · have hy' := Finset.mem_singleton.mp hy
    subst y
    obtain ⟨i,hi⟩ := Fin.exists_castSucc_eq.mpr hxy
    exact ⟨i,by rw [mark,hi]⟩

private noncomputable def slice {n : ℕ} (f : Fin (n+1) → ℂ) (s : Finset (Fin (n+1))) : ℂ :=
  if hs : s.card = 2 then if s.orderEmbOfFin hs 1 = Fin.last n then f (s.orderEmbOfFin hs 0)
    else 0 else 0

private theorem sum_slice {n : ℕ} (f : Fin (n+1) → ℂ) :
    ∑ s, slice f s = ∑ i : Fin n, f i.castSucc := by
  rw [restrict_sum (@mark n) mark_inj]
  · refine Finset.sum_congr rfl fun i _ => ?_
    simp [slice,card_mark,(mark_points i).1,(mark_points i).2]
  · intro s hh
    by_cases hs : s.card = 2
    · have hne : s.orderEmbOfFin hs 1 ≠ Fin.last n := by
        intro he
        obtain ⟨i,hi⟩ := mark_exists hs (he ▸ (Finset.orderEmbOfFin_mem s hs 1))
        exact hh i hi
      simp [slice,hs,hne]
    · simp [slice,hs]

private theorem perm_two (A : Matrix (Fin 2) (Fin 2) ℂ) :
    A.permanent = A 0 0 * A 1 1 + A 1 0 * A 0 1 := by
  have enums : (Finset.univ : Finset (Equiv.Perm (Fin 2))) = {1,Equiv.swap 0 1} := by decide
  have hne : (1 : Equiv.Perm (Fin 2)) ≠ Equiv.swap 0 1 := by decide
  simp [Matrix.permanent,enums,hne,Fin.prod_univ_two]

private theorem low₂ (t : Fin 5 × Fin 7 → ℂ)
    (hzero : ∀ i j, i ≠ 4 → j ≠ 6 → t (i,j) = 0) :
    (∑ R : Finset (Fin 5), ∑ C : Finset (Fin 7), if h : R.card = 2 ∧ C.card = 2 then
      Matrix.permanent (Matrix.of fun a b => t (R.orderEmbOfFin h.1 a,C.orderEmbOfFin h.2 b))
      else 0) = (∑ i : Fin 4, t (i.castSucc,6)) * ∑ j : Fin 6, t (4,j.castSucc) := by
  have factor (R : Finset (Fin 5)) (C : Finset (Fin 7)) :
      term 2 t R C = slice (n:=4) (fun i => t (i,6)) R * slice (n:=6) (fun j => t (4,j)) C := by
    by_cases hr : R.card = 2
    · by_cases hc : C.card = 2
      · let r := R.orderEmbOfFin hr
        let c := C.orderEmbOfFin hc
        have h0r : r 0 ≠ 4 := by have := r.strictMono (show (0 : Fin 2)<1 by decide); omega
        have h0c : c 0 ≠ 6 := by have := c.strictMono (show (0 : Fin 2)<1 by decide); omega
        simp only [term,slice,dite_true,hr,hc,and_self,perm_two,Matrix.of_apply]
        change t (r 0,c 0)*t (r 1,c 1) + t (r 1,c 0)*t (r 0,c 1) =
          (if r 1 = 4 then t (r 0,6) else 0) * (if c 1 = 6 then t (4,c 0) else 0)
        rw [hzero _ _ h0r h0c,zero_mul,zero_add]
        by_cases hr1 : r 1 = 4 <;> by_cases hc1 : c 1 = 6 <;>
          simp [hr1,hc1,hzero,h0r,h0c,mul_comm]
      · simp [term,slice,hc]
    · simp [term,slice,hr]
  change (∑ R, ∑ C, term 2 t R C) = _
  simp_rw [factor, ← Finset.mul_sum]
  rw [← Finset.sum_mul,sum_slice,sum_slice]

end L207low

namespace PEqualNP.Outside.Cross207

-- The rectangular cross parametrization adapts the construction in Gct.Helpers.LevelLow.
private abbrev Parameters := (Fin 5 → ℂ) × (Fin 4 → ℂ)

private def rowPart (x : Fin 5 → ℂ) : Fin 6 → ℂ :=
  Fin.lastCases (-∑ j, x j) x

private def entry (v : Parameters) (p : Fin 5 × Fin 7) : ℂ :=
  Fin.lastCases (Fin.lastCases (-∑ i, v.2 i) (rowPart v.1) p.2)
    (fun i => Fin.lastCases (v.2 i) (fun _ => 0) p.2) p.1

@[local simp] private theorem last4 (a : ℂ) (f : Fin 4 → ℂ) : Fin.lastCases a f (4 : Fin 5) = a := rfl
@[local simp] private theorem last5 (a : ℂ) (f : Fin 5 → ℂ) : Fin.lastCases a f (5 : Fin 6) = a := rfl
@[local simp] private theorem last6 (a : ℂ) (f : Fin 6 → ℂ) : Fin.lastCases a f (6 : Fin 7) = a := rfl

@[local simp] private theorem penultimate (a : ℂ) (f : Fin 6 → ℂ) : Fin.lastCases a f (5 : Fin 7) = f 5 := rfl

private theorem row_zero (x : Fin 5 → ℂ) : ∑ j, rowPart x j = 0 := by
  rw [Fin.sum_univ_castSucc]
  simp [rowPart]

private def parametrization : Parameters →ₗ[ℂ] (Fin 5 × Fin 7 → ℂ) where
  toFun := entry
  map_add' v w := by
    funext ⟨i,j⟩
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => simp [entry, Finset.sum_add_distrib, add_comm]
      | cast j =>
        induction j using Fin.lastCases with
        | last => simp [entry, rowPart, Finset.sum_add_distrib, add_comm]
        | cast j => simp [entry,rowPart]
    | cast i =>
      induction j using Fin.lastCases with
      | last => simp [entry]
      | cast j => simp [entry]
  map_smul' c v := by
    funext ⟨i,j⟩
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => simp [entry, Finset.mul_sum]
      | cast j =>
        induction j using Fin.lastCases with
        | last => simp [entry, rowPart, Finset.mul_sum]
        | cast j => simp [entry,rowPart]
    | cast i =>
      induction j using Fin.lastCases with
      | last => simp [entry]
      | cast j => simp [entry]

private theorem parametrization_injective : Function.Injective parametrization := by
  rintro ⟨x,y⟩ ⟨x',y'⟩ hh
  have h : entry (x,y) = entry (x',y') := hh
  have hx : x = x' := by
    funext j
    have := congrFun h (Fin.last 4,j.castSucc.castSucc)
    simpa [entry,rowPart] using this
  have hy : y = y' := by
    funext i
    have := congrFun h (i.castSucc,Fin.last 6)
    simpa [entry] using this
  rw [hx,hy]

private theorem dimension : Module.finrank ℂ (LinearMap.range parametrization) = 9 := by
  rw [LinearMap.finrank_range_of_inj parametrization_injective, Module.finrank_prod,
    Module.finrank_fin_fun, Module.finrank_fin_fun]

private theorem supported (v : Parameters) (i : Fin 5) (j : Fin 7)
    (hi : i ≠ 4) (hj : j ≠ 6) : entry v (i,j) = 0 := by
  induction i using Fin.lastCases with
  | last => exact (hi rfl).elim
  | cast i =>
    induction j using Fin.lastCases with
    | last => exact (hj rfl).elim
    | cast j => simp [entry]

private theorem offRow (v : Parameters) : ∑ j : Fin 6, entry v (4,j.castSucc) = 0 := by
  change (∑ j : Fin 6, entry v (Fin.last 4,j.castSucc)) = 0
  simpa [entry] using row_zero v.1

private theorem total (v : Parameters) : ∑ i : Fin 5, ∑ j : Fin 7, entry v (i,j) = 0 := by
  have upper (i : Fin 4) : (∑ j : Fin 7, entry v (i.castSucc,j)) = v.2 i := by
    rw [Fin.sum_univ_castSucc]
    simp [entry]
  have lower : (∑ j : Fin 7, entry v (Fin.last 4,j)) = -(∑ i, v.2 i) := by
    rw [Fin.sum_univ_castSucc]
    simp [entry, row_zero]
  rw [Fin.sum_univ_castSucc,lower]
  simp only [upper, add_neg_cancel]

end PEqualNP.Outside.Cross207

namespace PEqualNP.Outside.Cross207

private theorem high_degree (t : Fin 5 × Fin 7 → ℂ)
    (hs : ∀ i j, i ≠ 4 → j ≠ 6 → t (i,j) = 0) (k : ℕ) (hk : 3 ≤ k) :
    (∑ R : Finset (Fin 5), ∑ C : Finset (Fin 7),
      if h : R.card = k ∧ C.card = k then
        Matrix.permanent (Matrix.of fun a b => t (R.orderEmbOfFin h.1 a, C.orderEmbOfFin h.2 b))
      else 0) = 0 := by
  classical
  have : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
  refine Finset.sum_eq_zero fun R _ => Finset.sum_eq_zero fun C _ => ?_
  split
  · rename_i h
    unfold Matrix.permanent
    refine Finset.sum_eq_zero fun σ _ => ?_
    let r : Fin k → Fin 5 := fun i => R.orderEmbOfFin h.1 (σ i)
    let c : Fin k → Fin 7 := fun i => C.orderEmbOfFin h.2 i
    have hr : Function.Injective r := (R.orderEmbOfFin h.1).injective.comp σ.injective
    have hc : Function.Injective c := (C.orderEmbOfFin h.2).injective
    obtain ⟨i,hi,hj⟩ := Fin.exists_ne_and_ne_of_two_lt
      (Function.invFun r 4) (Function.invFun c 6) hk
    refine Finset.prod_eq_zero (Finset.mem_univ i) (hs (r i) (c i) ?_ ?_)
    · intro e
      exact hi (e ▸ (Function.leftInverse_invFun hr i).symm)
    · intro e
      exact hj (e ▸ (Function.leftInverse_invFun hc i).symm)
  · rfl

end PEqualNP.Outside.Cross207

open PEqualNP.Outside.Cross207 in
theorem PEqualNP.Outside.L_gct_207 : ∃ L : Submodule ℂ (Fin 5 × Fin 7 → ℂ), Module.finrank ℂ L = 9 ∧ (∀ t ∈ L, ∀ k : ℕ, 1 ≤ k → k ≤ 5 → (∑ R : Finset (Fin 5), ∑ C : Finset (Fin 7), if h : R.card = k ∧ C.card = k then Matrix.permanent (Matrix.of fun a b => t (R.orderEmbOfFin h.1 a, C.orderEmbOfFin h.2 b)) else 0) = 0) := by
  refine ⟨LinearMap.range parametrization, dimension, ?_⟩
  rintro _ ⟨v,rfl⟩ k hk _
  by_cases h1 : k = 1
  · subst k
    exact (L207low.low₁ (entry v)).trans (total v)
  by_cases h2 : k = 2
  · subst k
    exact (L207low.low₂ (entry v) (supported v)).trans (by rw [offRow, mul_zero])
  exact high_degree (entry v) (supported v) k (by omega)
