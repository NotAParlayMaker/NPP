import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_234_aux

open PEqualNP.MetaComplexity

theorem rank_submatrix_le {α β : Type} [Fintype α] [Fintype β] [DecidableEq β]
    (M : Matrix β β ℚ) (g h : α → β) :
    (M.submatrix g h).rank ≤ M.rank := by
  let pullL : (β → ℚ) →ₗ[ℚ] (α → ℚ) :=
    { toFun := fun w x => w (g x)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let pushR : (α → ℚ) →ₗ[ℚ] (β → ℚ) :=
    { toFun := fun v z => ∑ y : α, if h y = z then v y else 0
      map_add' := fun u v => by
        ext z
        simp only [Pi.add_apply, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun y _ => ?_
        split_ifs <;> ring
      map_smul' := fun c v => by
        ext z
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => ?_
        split_ifs <;> ring }
  have hcomp : (M.submatrix g h).mulVecLin = pullL.comp (M.mulVecLin.comp pushR) := by
    ext v x
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.submatrix_apply,
      LinearMap.comp_apply, pullL, pushR, LinearMap.coe_mk, AddHom.coe_mk]
    calc
      ∑ y : α, M (g x) (h y) * v y
        = ∑ y : α, ∑ z : β, M (g x) z * (if h y = z then v y else 0) := by
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [Finset.sum_eq_single (h y)]
          · simp
          · intro z _ hz
            simp [Ne.symm hz]
          · intro hmem; exact absurd (Finset.mem_univ _) hmem
      _ = ∑ z : β, ∑ y : α, M (g x) z * (if h y = z then v y else 0) := Finset.sum_comm
      _ = ∑ z : β, M (g x) z * ∑ y : α, (if h y = z then v y else 0) := by
          refine Finset.sum_congr rfl fun z _ => (Finset.mul_sum _ _ _).symm
  show Module.finrank ℚ (LinearMap.range (M.submatrix g h).mulVecLin) ≤
    Module.finrank ℚ (LinearMap.range M.mulVecLin)
  rw [hcomp, LinearMap.range_comp]
  exact le_trans (Submodule.finrank_map_le pullL _)
    (Submodule.finrank_mono (LinearMap.range_comp_le_range pushR M.mulVecLin))

theorem minor_le {β : Type} [Fintype β] [DecidableEq β] (M : Matrix β β ℚ) {k : ℕ}
    (r c : Fin k → β) (h : (M.submatrix r c).det ≠ 0) : k ≤ M.rank := by
  have hu : IsUnit (M.submatrix r c) :=
    (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 h)
  have h1 := Matrix.rank_of_isUnit (M.submatrix r c) hu
  have h2 := rank_submatrix_le M r c
  rw [Fintype.card_fin] at h1
  omega

def minor2 (a b c d : Bool) : Bool := (a && d) != (b && c)

theorem minor2_ne (a b c d : Bool) (h : minor2 a b c d = true) :
    (if a = true then (1 : ℚ) else 0) * (if d = true then (1 : ℚ) else 0) -
      (if b = true then (1 : ℚ) else 0) * (if c = true then (1 : ℚ) else 0) ≠ 0 := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all [minor2]

def lbP (p : Fin 3 → Fin 3 → Bool) : ℕ :=
  if ∃ i0 i1 j0 j1 : Fin 3, minor2 (p i0 j0) (p i0 j1) (p i1 j0) (p i1 j1) = true then 2
  else if ∃ i j : Fin 3, p i j = true then 1 else 0

theorem lbP_le {β : Type} [Fintype β] [DecidableEq β] (N : Matrix β β ℚ) (R C : Fin 3 → β)
    (p : Fin 3 → Fin 3 → Bool) (hN : ∀ r c, N (R r) (C c) = if p r c = true then 1 else 0) :
    lbP p ≤ N.rank := by
  unfold lbP
  split_ifs with h1 h2
  · obtain ⟨i0, i1, j0, j1, h⟩ := h1
    have := minor_le N ![R i0, R i1] ![C j0, C j1] (by
      rw [Matrix.det_fin_two]
      simp only [Matrix.submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, hN]
      exact minor2_ne _ _ _ _ h)
    exact this
  · obtain ⟨i, j, h⟩ := h2
    have := minor_le N ![R i] ![C j] (by
      rw [Matrix.det_fin_one]
      simp [hN, h])
    exact this
  · exact Nat.zero_le _

def R : Fin 3 → Fin 3 → Bool := ![![true, false, false], ![false, true, false], ![false, false, true]]

def C : Fin 3 → Fin 3 → Bool := ![![true, true, false], ![true, false, true], ![false, true, true]]

def ff (x : Fin 3 → Bool) : Bool := decide ((x 0).toNat + (x 1).toNat + (x 2).toNat ≤ 1)

def tab (a b c : Fin 3) (r cc : Fin 3) : ℕ :=
  (![![1, 2, (a : ℕ)], ![0, (b : ℕ), 2], ![(c : ℕ), 0, 1]] : Fin 3 → Fin 3 → ℕ) r cc

def patA (a b c : Fin 3) (i : Fin 3) (bb : Bool) (r cc : Fin 3) : Bool :=
  decide (tab a b c r cc = (i : ℕ) ∧ R r i = bb)

theorem key : ∀ a b c : Fin 3, 5 ≤ ∑ i : Fin 3, ∑ bb : Bool, lbP (patA a b c i bb) := by
  decide +kernel

theorem ff_R : ∀ r : Fin 3, ff (R r) = true := by decide

theorem ff_C : ∀ c : Fin 3, ff (C c) = false := by decide

end PEqualNP.Outside.L_meta_234_aux

open PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_234_aux

theorem PEqualNP.Outside.L_meta_234 : ¬ PEqualNP.MetaComplexity.HasTypedRank 3 (fun x : Fin 3 → Bool => decide ((x 0).toNat + (x 1).toNat + (x 2).toNat ≤ 1)) 4 := by
  intro hmain
  have hmain' : HasTypedRank 3 ff 4 := hmain
  obtain ⟨τ, hτ, hr⟩ := hmain'
  have forced : ∀ (r c j : Fin 3), (∀ i : Fin 3, R r i ≠ C c i → i = j) →
      τ (R r) (C c) = (j : ℕ) := by
    intro r c j hj
    obtain ⟨i, hi, hne⟩ := hτ (R r) (C c) (ff_R r) (ff_C c)
    have := hj i hne
    subst this
    exact hi
  have free : ∀ r c : Fin 3, ∃ j : Fin 3, τ (R r) (C c) = (j : ℕ) := by
    intro r c
    obtain ⟨i, hi, _⟩ := hτ (R r) (C c) (ff_R r) (ff_C c)
    exact ⟨i, hi⟩
  obtain ⟨a, ha⟩ := free 0 2
  obtain ⟨b, hb⟩ := free 1 1
  obtain ⟨c, hc⟩ := free 2 0
  have h00 := forced 0 0 1 (by decide)
  have h01 := forced 0 1 2 (by decide)
  have h10 := forced 1 0 0 (by decide)
  have h12 := forced 1 2 2 (by decide)
  have h21 := forced 2 1 0 (by decide)
  have h22 := forced 2 2 1 (by decide)
  have htab : ∀ r cc : Fin 3, τ (R r) (C cc) = tab a b c r cc := by
    intro r cc
    fin_cases r <;> fin_cases cc <;> simp_all [tab]
  have hpat : ∀ (i : Fin 3) (bb : Bool),
      PEqualNP.Outside.L_meta_234_aux.lbP (patA a b c i bb) ≤
        (typedMatrix 3 ff τ i bb).rank := by
    intro i bb
    refine lbP_le (typedMatrix 3 ff τ i bb) R C (patA a b c i bb) ?_
    intro r cc
    simp [typedMatrix, ff_R, ff_C, patA, htab r cc]
  have hsum : (∑ i : Fin 3, ∑ bb : Bool, lbP (patA a b c i bb)) ≤
      ∑ i : Fin 3, ∑ bb : Bool, (typedMatrix 3 ff τ i bb).rank :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun bb _ => hpat i bb
  have hk := key a b c
  omega
