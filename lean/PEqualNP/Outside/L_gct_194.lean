import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_gct_194

def insertPick {n m : ℕ} (p : Fin (m + 1)) (f : Fin n ↪ Fin m) :
    Fin (n + 1) ↪ Fin (m + 1) :=
  Fin.Embedding.cons (f.trans (finSuccAboveEquiv p).asEmbedding) (a := p) (by
    rintro ⟨i, hi⟩
    exact ((finSuccAboveEquiv p) (f i)).property hi)

lemma insertPick_zero {n m : ℕ} (p : Fin (m + 1)) (f : Fin n ↪ Fin m) :
    insertPick p f 0 = p := rfl

lemma insertPick_succ {n m : ℕ} (p : Fin (m + 1)) (f : Fin n ↪ Fin m)
    (i : Fin n) : insertPick p f i.succ = p.succAbove (f i) := rfl

noncomputable def pickEquiv (n m : ℕ) :
    Fin (m + 1) × (Fin n ↪ Fin m) ≃ (Fin (n + 1) ↪ Fin (m + 1)) :=
  Equiv.ofBijective (fun pf => insertPick pf.1 pf.2) (by
    constructor
    · rintro ⟨p, f⟩ ⟨q, g⟩ h
      have hpq : p = q := congrArg (fun e : Fin (n + 1) ↪ Fin (m + 1) => e 0) h
      subst q
      congr 1
      apply Function.Embedding.ext
      intro i
      apply Fin.succAbove_right_injective
      exact congrArg (fun e : Fin (n + 1) ↪ Fin (m + 1) => e i.succ) h
    · intro e
      let p := e 0
      let f : Fin n ↪ Fin m :=
        ((Fin.Embedding.tail e).codRestrict {j : Fin (m + 1) | j ≠ p} (fun i hi =>
          Fin.succ_ne_zero i (e.injective hi))).trans (finSuccAboveEquiv p).symm.toEmbedding
      refine ⟨(p, f), ?_⟩
      apply Function.Embedding.ext
      intro i
      change insertPick p f i = e i
      refine Fin.cases rfl (fun j => ?_) i
      rw [insertPick_succ]
      exact congrArg Subtype.val ((finSuccAboveEquiv p).apply_symm_apply
        ⟨e j.succ, fun h => Fin.succ_ne_zero j (e.injective h)⟩))

lemma sumPick {n m : ℕ} (g : (Fin (n + 1) ↪ Fin (m + 1)) → ℂ) :
    (∑ f, g f) = ∑ j : Fin (m + 1), ∑ f : Fin n ↪ Fin m, g (insertPick j f) := by
  rw [← (pickEquiv n m).sum_comp g, Fintype.sum_prod_type]
  rfl

def ent (c d : ℂ) (i : Fin 5) (j : Fin 4) : ℂ :=
  1 + (if i.val = 4 then d * (if j.val = 0 then (1 : ℂ) else if j.val = 1 then -1 else 0)
    else c * (if j.val = i.val then (1 : ℂ) else if j.val = (i.val + 1) % 4 then Complex.I
      else if j.val = (i.val + 2) % 4 then -Complex.I else -1))

def mat (c d x : ℂ) : Fin 5 → Fin 4 → ℂ :=
  ![![1 + c, 1 + c * x, 1 - c * x, 1 - c],
    ![1 - c, 1 + c, 1 + c * x, 1 - c * x],
    ![1 - c * x, 1 - c, 1 + c, 1 + c * x],
    ![1 + c * x, 1 - c * x, 1 - c, 1 + c],
    ![1 + d, 1 - d, 1, 1]]

set_option maxHeartbeats 2000000 in
lemma ent_eq (c d : ℂ) : ent c d = mat c d Complex.I := by
  funext i j
  fin_cases i <;> fin_cases j <;> simp [ent, mat, sub_eq_add_neg]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
lemma expand (a : Fin 5 → Fin 4 → ℂ) :
    (∑ f : Fin 4 ↪ Fin 5, ∏ j : Fin 4, a (f j) j) =
      ∑ p0 : Fin 5, ∑ p1 : Fin 4, ∑ p2 : Fin 3, ∑ p3 : Fin 2,
        a p0 0 * (a (p0.succAbove p1) 1 * (a (p0.succAbove (p1.succAbove p2)) 2 *
          a (p0.succAbove (p1.succAbove (p2.succAbove p3))) 3)) := by
  rw [sumPick (n := 3) (m := 4)]
  refine Finset.sum_congr rfl fun p0 _ => ?_
  rw [sumPick (n := 2) (m := 3)]
  refine Finset.sum_congr rfl fun p1 _ => ?_
  rw [sumPick (n := 1) (m := 2)]
  refine Finset.sum_congr rfl fun p2 _ => ?_
  rw [sumPick (n := 0) (m := 1)]
  refine Finset.sum_congr rfl fun p3 _ => ?_
  rw [Fintype.sum_unique]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, insertPick_zero, insertPick_succ, mul_one]
  rfl

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
lemma poly (c d x : ℂ) (hx : x ^ 2 = -1) :
    (∑ p0 : Fin 5, ∑ p1 : Fin 4, ∑ p2 : Fin 3, ∑ p3 : Fin 2,
        mat c d x p0 0 * (mat c d x (p0.succAbove p1) 1 *
          (mat c d x (p0.succAbove (p1.succAbove p2)) 2 *
          mat c d x (p0.succAbove (p1.succAbove (p2.succAbove p3))) 3))) = 120 := by
  simp +decide only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succAbove, mat]
  simp
  linear_combination (2 * c ^ 2 * (c ^ 2 * x ^ 2 - 4 * c ^ 2 * x + c ^ 2 + 12)) * hx

lemma main_result : ∀ c d : ℂ, (∑ f : Fin 4 ↪ Fin 5, ∏ j : Fin 4, (1 + (if (f j).val = 4 then d * (if j.val = 0 then (1 : ℂ) else if j.val = 1 then -1 else 0) else c * (if j.val = (f j).val then (1 : ℂ) else if j.val = ((f j).val + 1) % 4 then Complex.I else if j.val = ((f j).val + 2) % 4 then -Complex.I else -1)))) = 120 := by
  intro c d
  have h := expand (ent c d)
  rw [ent_eq, poly c d Complex.I Complex.I_sq, ← ent_eq] at h
  exact h

end PEqualNP.Outside.L_gct_194

theorem PEqualNP.Outside.L_gct_194 : ∀ c d : ℂ, (∑ f : Fin 4 ↪ Fin 5, ∏ j : Fin 4, (1 + (if (f j).val = 4 then d * (if j.val = 0 then (1 : ℂ) else if j.val = 1 then -1 else 0) else c * (if j.val = (f j).val then (1 : ℂ) else if j.val = ((f j).val + 1) % 4 then Complex.I else if j.val = ((f j).val + 2) % 4 then -Complex.I else -1)))) = 120 :=
  PEqualNP.Outside.L_gct_194.main_result
