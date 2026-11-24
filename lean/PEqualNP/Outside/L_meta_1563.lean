import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.FinCases
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1563

def ln (t : Fin 13) : Finset (Fin 13) := {t, t + 1, t + 3, t + 9}

def base : Finset (Fin 13) := {0, 1, 3, 9}

theorem ln_zero : ln 0 = base := by decide

abbrev top (x : Fin 13 → Bool) : Prop := x 0 = true ∨ x 1 = true

abbrev above (x : Fin 13 → Bool) : Prop := ∀ v : Fin 13, v ∉ base → x v = true


def exception (p : Bool × Bool) (v : Fin 13) : Bool :=
  decide (v ∉ base ∨ (p.1 = true ∧ v = 3) ∨ (p.2 = true ∧ v = 9))

lemma exc_zero (p : Bool × Bool) : exception p 0 = false := by simp [exception, base]
lemma exc_one (p : Bool × Bool) : exception p 1 = false := by simp [exception, base]
lemma exc_three (p : Bool × Bool) : exception p 3 = p.1 := by simp [exception, base]
lemma exc_nine (p : Bool × Bool) : exception p 9 = p.2 := by simp [exception, base]

lemma exception_injective : Function.Injective exception := by
  intro p q h
  apply Prod.ext
  · simpa only [exc_three] using congrFun h 3
  · simpa only [exc_nine] using congrFun h 9

lemma exc_above (p : Bool × Bool) : above (exception p) := by
  intro v hv
  exact decide_eq_true (Or.inl hv)

lemma false_of_not_true {x : Bool} (h : ¬ x = true) : x = false := by cases x <;> simp_all

lemma exc_classify (x : Fin 13 → Bool) (ht : ¬ top x) (ha : above x) :
    x = exception (x 3, x 9) := by
  have h0 : x 0 = false := false_of_not_true (fun h => ht (Or.inl h))
  have h1 : x 1 = false := false_of_not_true (fun h => ht (Or.inr h))
  funext v
  by_cases hv : v ∈ base
  · simp only [base, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · rw [h0, exc_zero]
    · rw [h1, exc_one]
    · exact (exc_three (x 3, x 9)).symm
    · exact (exc_nine (x 3, x 9)).symm
  · rw [ha v hv, exc_above _ v hv]

lemma coline_fixed (t : Fin 13) :
    top (fun v => decide (v ∉ ln t)) ∨ above (fun v => decide (v ∉ ln t)) := by
  by_cases ht : t = 0
  · right
    intro v hv
    exact decide_eq_true (by simpa only [ht, ln_zero] using hv)
  · left
    have hs : ∀ j : Fin 13, j ≠ 0 → 0 ∉ ln j ∨ 1 ∉ ln j := by decide
    rcases hs t ht with h | h
    · exact Or.inl (decide_eq_true h)
    · exact Or.inr (decide_eq_true h)

lemma exc_card : (Finset.univ.filter (fun x : Fin 13 → Bool => above x ∧ ¬ top x)).card = 4 := by
  classical
  have h : Finset.univ.filter (fun x : Fin 13 → Bool => above x ∧ ¬ top x) =
      Finset.univ.image exception := by
    ext x
    constructor
    · intro hx
      obtain ⟨ha, ht⟩ := (Finset.mem_filter.mp hx).2
      exact Finset.mem_image.mpr ⟨(x 3, x 9), Finset.mem_univ _, (exc_classify x ht ha).symm⟩
    · intro hx
      obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hx
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, exc_above p, ?_⟩
      simp [top, exc_zero, exc_one]
  rw [h, Finset.card_image_of_injective _ exception_injective]
  decide

theorem card_first_two :
    (Finset.univ.filter (fun x : Fin 13 → Bool => x 0 = true ∨ x 1 = true)).card = 6144 := by
  classical
  let p := fun x : Fin 13 → Bool => x 0 = true ∨ x 1 = true
  have hcomp :
      ((Finset.univ : Finset (Fin 13 → Bool)).filter (fun x => ¬p x)).card =
      (Finset.univ : Finset (Fin 11 → Bool)).card := by
    let drop := fun x : Fin 13 → Bool => fun i : Fin 11 => x i.succ.succ
    let pad := fun x : Fin 11 → Bool =>
      (Fin.cons false (Fin.cons false x) : Fin 13 → Bool)
    refine Finset.card_nbij' drop pad (by simp) ?_ ?_ ?_
    · intro y hy
      simp [pad, p]
    · intro x hx
      have hn : ¬p x := (Finset.mem_filter.mp hx).2
      have h0 : x 0 = false := by
        cases he : x 0 <;> simp_all [p]
      have h1 : x 1 = false := by
        cases he : x 1 <;> simp_all [p]
      change Fin.cons false (Fin.cons false (Fin.tail (Fin.tail x))) = x
      conv_rhs => rw [← Fin.cons_self_tail x]
      rw [h0]
      congr 1
      rw [← Fin.cons_self_tail (Fin.tail x)]
      congr 1
      exact h1.symm
    · intro y hy
      funext i
      simp [drop, pad]
  have hs := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin 13 → Bool))) p
  rw [hcomp, Finset.card_univ, Finset.card_univ, Fintype.card_pi_const,
    Fintype.card_pi_const, Fintype.card_bool] at hs
  change ((Finset.univ : Finset (Fin 13 → Bool)).filter p).card = 6144
  omega

lemma classify (x : Fin 13 → Bool) :
    (top x ∨ above x) ↔
      (top x ∨ x = (fun v => decide (v ∉ base)) ∨
        x = (fun v => decide (v ∉ base ∨ v = 3)) ∨
        x = (fun v => decide (v ∉ base ∨ v = 9)) ∨
        x = (fun v => decide (v ∉ base ∨ v = 3 ∨ v = 9))) := by
  constructor
  · intro h
    by_cases ht : top x
    · exact Or.inl ht
    · have ha := h.resolve_left ht
      have he := exc_classify x ht ha
      right
      cases h3 : x 3 <;> cases h9 : x 9 <;>
        rw [h3, h9] at he
      · change x = (fun v => exception (false, false) v) at he
        exact Or.inl (by simpa [exception] using he)
      · change x = (fun v => exception (false, true) v) at he
        exact Or.inr (Or.inr (Or.inl (by simpa [exception] using he)))
      · change x = (fun v => exception (true, false) v) at he
        exact Or.inr (Or.inl (by simpa [exception] using he))
      · change x = (fun v => exception (true, true) v) at he
        exact Or.inr (Or.inr (Or.inr (by simpa [exception] using he)))
  · rintro (ht | rfl | rfl | rfl | rfl)
    · exact Or.inl ht
    · exact Or.inr (fun v hv => decide_eq_true hv)
    · exact Or.inr (fun v hv => decide_eq_true (Or.inl hv))
    · exact Or.inr (fun v hv => decide_eq_true (Or.inl hv))
    · exact Or.inr (fun v hv => decide_eq_true (Or.inl hv))

lemma union_card : (Finset.univ.filter (fun x : Fin 13 → Bool => top x ∨ above x)).card = 6148 := by
  classical
  let A := Finset.univ.filter (fun x : Fin 13 → Bool => top x)
  let B := Finset.univ.filter (fun x : Fin 13 → Bool => above x ∧ ¬ top x)
  have hd : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro x hx hy
    exact (Finset.mem_filter.mp hy).2.2 (Finset.mem_filter.mp hx).2
  have he : Finset.univ.filter (fun x : Fin 13 → Bool => top x ∨ above x) = A ∪ B := by
    ext x
    simp only [A, B, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    tauto
  have hc : A.card = 6144 := card_first_two
  have hb : B.card = 4 := exc_card
  rw [he, Finset.card_union_of_disjoint hd, hc, hb]

end PEqualNP.Outside.L_meta_1563

open PEqualNP.Outside.L_meta_1563

theorem PEqualNP.Outside.L_meta_1563 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    (∀ x y : Fin 13 → Bool, (x 0 = true ∨ x 1 = true ∨ ∀ v : Fin 13, v ∉ L 0 → x v = true) → (∀ v : Fin 13, x v = true → y v = true) → (y 0 = true ∨ y 1 = true ∨ ∀ v : Fin 13, v ∉ L 0 → y v = true)) ∧
    (Finset.univ.filter (fun x : Fin 13 → Bool => (x 0 = true ∨ x 1 = true ∨ ∀ v : Fin 13, v ∉ L 0 → x v = true))).card = 6148 ∧
    (∀ t : Fin 13, ((fun v : Fin 13 => decide (v ∉ L t)) 0 = true ∨ (fun v : Fin 13 => decide (v ∉ L t)) 1 = true ∨ ∀ v : Fin 13, v ∉ L 0 → (fun v : Fin 13 => decide (v ∉ L t)) v = true)) ∧
    (Finset.univ.filter (fun x : Fin 13 → Bool => x 0 = true ∨ x 1 = true)).card = 6144 ∧
    (∀ x : Fin 13 → Bool, (x 0 = true ∨ x 1 = true ∨ ∀ v : Fin 13, v ∉ L 0 → x v = true) ↔ (x 0 = true ∨ x 1 = true ∨ x = (fun v : Fin 13 => decide (v ∉ L 0)) ∨
      x = (fun v : Fin 13 => decide (v ∉ L 0 ∨ v = 3)) ∨ x = (fun v : Fin 13 => decide (v ∉ L 0 ∨ v = 9)) ∨
      x = (fun v : Fin 13 => decide (v ∉ L 0 ∨ v = 3 ∨ v = 9)))) := by
  intro L hL
  have hline (t : Fin 13) : L t = ln t := hL t
  have hb : L 0 = base := (hline 0).trans ln_zero
  refine ⟨?_, ?_, ?_, card_first_two, ?_⟩
  · intro x y hxy h
    rcases hxy with h0 | h1 | ha
    · exact Or.inl (h 0 h0)
    · exact Or.inr (Or.inl (h 1 h1))
    · exact Or.inr (Or.inr (fun v hv => h v (ha v hv)))
  · simpa only [hb, top, above, or_assoc] using union_card
  · intro t
    simpa only [hb, hline t, top, above, or_assoc] using coline_fixed t
  · intro x
    simpa only [hb, top, above, or_assoc] using classify x
