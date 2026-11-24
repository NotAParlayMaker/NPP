import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_992
open Matrix MvPolynomial

private theorem fourOrth {F : Type} [Field F] {p q a b : Fin 3 → F}
    (hp : p ≠ 0) (hq : q ≠ 0) (ha : a ≠ 0)
    (hpq : ∀ c : F, q ≠ c • p) (hab : ∀ c : F, b ≠ c • a)
    (pa : dotProduct p a = 0) (pb : dotProduct p b = 0)
    (qa : dotProduct q a = 0) (qb : dotProduct q b = 0) : False := by
  have nc : crossProduct a b ≠ 0 := crossProduct_ne_zero_iff_linearIndependent.mpr
    ((LinearIndependent.pair_iff' ha).mpr (by simpa [eq_comm] using hab))
  have cx (v : Fin 3 → F) (v0 : v ≠ 0) (va : dotProduct v a = 0) (vb : dotProduct v b = 0) :
      Projectivization.mk F v v0 = Projectivization.mk F (crossProduct a b) nc := by
    apply (Projectivization.mk_eq_mk_iff_crossProduct_eq_zero v0 nc).mpr
    rw [cross_cross_eq_smul_sub_smul', dotProduct_comm a v, va, vb, zero_smul, zero_smul, sub_self]
  obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' F q p hq hp).mp
    ((cx q hq qa qb).trans (cx p hp pa pb).symm)
  exact hpq c hc.symm

private noncomputable def form {F : Type} [Field F] (v : Fin 3 → F) : MvPolynomial (Fin 3) F :=
  ∑ t, C (v t) * X t

private theorem separated {F : Type} [Field F] {k b : ℕ} (P : Fin k → MvPolynomial (Fin 3) F)
    (l : Fin k → Fin 3 → F) (hd : ∀ i, (P i).IsHomogeneous b)
    (diag : ∀ i, eval (l i) (P i) ≠ 0)
    (off : ∀ i j, i ≠ j → eval (l j) (P i) = 0) :
    2 * k ≤ (b + 1) * (b + 2) := by
  classical
  let A := (Finset.univ : Finset (Fin 3)).finsuppAntidiag b
  let W (i : Fin k) (d : ↥A) : F := (P i).coeff d.val
  have ind : LinearIndependent F W := by
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    have hp : ∑ i, c i • P i = 0 := by
      ext d
      by_cases h : d ∈ A
      · have e := congrFun hc (⟨d, h⟩ : ↥A)
        simpa [W, Finset.sum_apply, coeff_sum] using e
      · have van (i : Fin k) : (P i).coeff d = 0 := by
          by_contra ne
          apply h
          simpa [A, Finset.mem_finsuppAntidiag, Finsupp.weight_apply, Finsupp.sum_fintype] using hd i ne
        simp [van]
    have v := congrArg (eval (l j)) hp
    simp only [map_sum, smul_eq_C_mul, map_mul, eval_C, map_zero] at v
    rw [Finset.sum_eq_single j (fun i _ hij => by simp [off i j hij]) (by simp)] at v
    exact (mul_eq_zero.mp v).resolve_right (diag j)
  have hh := ind.fintype_card_le_finrank
  simp only [Fintype.card_fin, Module.finrank_pi, Fintype.card_coe] at hh
  rw [show A.card = (b + 2).choose b by
    simpa [A, Nat.add_comm, Nat.add_assoc] using
      Finset.card_finsuppAntidiag_nat_eq_choose (s := (Finset.univ : Finset (Fin 3))) b] at hh
  rw [← Nat.choose_symm (show b ≤ b + 2 by omega), show b + 2 - b = 2 by omega,
    Nat.choose_two_right] at hh
  have htwo := Nat.div_mul_le_self ((b + 2) * (b + 2 - 1)) 2
  have h := Nat.mul_le_mul_right 2 hh
  have he : b + 2 - 1 = b + 1 := by omega
  rw [he] at htwo h
  nlinarith

private theorem upper : ∀ (F : Type) [Field F] (n k b : ℕ) (pt : Fin n → Fin 3 → F)
    (l : Fin k → Fin 3 → F) (y : Fin k → Finset (Fin n)) (g : (Fin n → Bool) → Bool),
    (∀ p : Fin n, pt p ≠ 0) →
    (∀ p p' : Fin n, p ≠ p' → ∀ c : F, pt p' ≠ c • pt p) →
    (∀ i : Fin k, l i ≠ 0) →
    (∀ i j : Fin k, i ≠ j → ∀ c : F, l j ≠ c • l i) →
    (∀ i : Fin k, (y i).card ≤ b) →
    (∀ i : Fin k, ∀ p ∈ y i, ∑ t : Fin 3, pt p t * l i t ≠ 0) →
    (∀ (i : Fin k) (x : Fin n → Bool), g x = true →
      ∃ p : Fin n, x p = true ∧ ∑ t : Fin 3, pt p t * l i t = 0) →
    (∀ i : Fin k, ∃ p p' : Fin n, p ≠ p' ∧
      ∑ t : Fin 3, pt p t * l i t = 0 ∧ ∑ t : Fin 3, pt p' t * l i t = 0 ∧
      g (fun v : Fin n => decide (v ∈ y i ∨ v = p)) = true ∧
      g (fun v : Fin n => decide (v ∈ y i ∨ v = p')) = true) →
    2 * k ≤ (b + 1) * (b + 2) := by
  classical
  intro F _ n k b pt l y g hp hpp hl hll hy havoid safe two
  have hit (i j : Fin k) (hij : i ≠ j) : ∃ v ∈ y i, dotProduct (pt v) (l j) = 0 := by
    obtain ⟨p, q, hpq, pa, qa, gp, gq⟩ := two i
    by_contra! miss
    have on (v : Fin n) (gv : g (fun w => decide (w ∈ y i ∨ w = v)) = true) :
        dotProduct (pt v) (l j) = 0 := by
      obtain ⟨w, hw, hj⟩ := safe j _ gv
      rcases of_decide_eq_true hw with hy | rfl
      · exact False.elim (miss w hy hj)
      · exact hj
    exact fourOrth (hp p) (hp q) (hl i) (hpp p q hpq) (hll i j hij) pa (on p gp) qa (on q gq)
  have coord (i : Fin k) : ∃ t, l i t ≠ 0 := by
    by_contra! hn
    exact hl i (funext hn)
  choose t ht using coord
  let Q (i : Fin k) : MvPolynomial (Fin 3) F := ∏ p ∈ y i, form (pt p)
  let P (i : Fin k) := Q i * (X (t i)) ^ (b - (y i).card)
  have evform (v z : Fin 3 → F) : eval z (form v) = dotProduct v z := by
    simp [form, dotProduct]
  apply separated P l
  · intro i
    have hform (v : Fin 3 → F) : (form v).IsHomogeneous 1 :=
      IsHomogeneous.sum _ _ _ (fun t _ => isHomogeneous_C_mul_X _ _)
    have hQ : (Q i).IsHomogeneous (y i).card := by
      simpa [Q] using IsHomogeneous.prod (y i) (fun p => form (pt p)) (fun _ => 1)
        (fun p _ => hform (pt p))
    simpa [P, Nat.add_sub_of_le (hy i)] using hQ.mul (isHomogeneous_X_pow (t i) (b - (y i).card))
  · intro i
    simp only [P, Q, map_mul, map_prod, map_pow, eval_X, evform]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr (havoid i)) (pow_ne_zero _ (ht i))
  · intro i j hij
    obtain ⟨v, hv, hd⟩ := hit i j hij
    simp only [P, Q, map_mul, map_prod, evform]
    rw [Finset.prod_eq_zero hv hd, zero_mul]

end PEqualNP.Outside.L_meta_992

theorem PEqualNP.Outside.L_meta_992 :
    ¬ (∃ (F : Type) (_ : Field F) (n k b : ℕ) (pt : Fin n → Fin 3 → F)
      (l : Fin k → Fin 3 → F) (y : Fin k → Finset (Fin n)) (g : (Fin n → Bool) → Bool),
      (∀ p : Fin n, pt p ≠ 0) ∧
      (∀ p p' : Fin n, p ≠ p' → ∀ c : F, pt p' ≠ c • pt p) ∧
      (∀ i : Fin k, l i ≠ 0) ∧
      (∀ i j : Fin k, i ≠ j → ∀ c : F, l j ≠ c • l i) ∧
      (∀ i : Fin k, (y i).card ≤ b) ∧
      (∀ i : Fin k, ∀ p ∈ y i, ∑ t : Fin 3, pt p t * l i t ≠ 0) ∧
      (∀ (i : Fin k) (x : Fin n → Bool), g x = true →
        ∃ p : Fin n, x p = true ∧ ∑ t : Fin 3, pt p t * l i t = 0) ∧
      (∀ i : Fin k, ∃ p p' : Fin n, p ≠ p' ∧
        ∑ t : Fin 3, pt p t * l i t = 0 ∧ ∑ t : Fin 3, pt p' t * l i t = 0 ∧
        g (fun v : Fin n => decide (v ∈ y i ∨ v = p)) = true ∧
        g (fun v : Fin n => decide (v ∈ y i ∨ v = p')) = true) ∧
      (b + 1) * (b + 2) < 2 * k) := by
  rintro ⟨F, _, n, k, b, pt, l, y, g, hp, hpp, hl, hll, hy, havoid, safe, two, hstrict⟩
  exact (Nat.not_lt.mpr (PEqualNP.Outside.L_meta_992.upper F n k b pt l y g
    hp hpp hl hll hy havoid safe two)) hstrict
