import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1563

lemma card_zero :
    (Finset.univ.filter (fun x : Fin 13 → Bool => ¬ (x 0 = true ∨ x 1 = true))).card = 2048 := by
  have key : Finset.univ.filter (fun x : Fin 13 → Bool => ¬ (x 0 = true ∨ x 1 = true)) =
      Fintype.piFinset (fun v : Fin 13 =>
        if v = 0 ∨ v = 1 then ({false} : Finset Bool) else Finset.univ) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro h v
      simp only [not_or, Bool.not_eq_true] at h
      split_ifs with hv
      · rcases hv with rfl | rfl
        · simp [h.1]
        · simp [h.2]
      · exact Finset.mem_univ _
    · intro h
      have a := h 0
      have b := h 1
      simp at a b
      simp [a, b]
  rw [key, Fintype.card_piFinset]
  decide

lemma card01 :
    (Finset.univ.filter (fun x : Fin 13 → Bool => x 0 = true ∨ x 1 = true)).card = 6144 := by
  have h := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin 13 → Bool))) (fun x => x 0 = true ∨ x 1 = true)
  rw [card_zero] at h
  have hu : (Finset.univ : Finset (Fin 13 → Bool)).card = 8192 := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    norm_num
  rw [hu] at h
  exact Nat.add_right_cancel (m := 2048) (h.trans (by norm_num))

lemma up : ∀ x y : Fin 13 → Bool,
    (x 0 = true ∨ x 1 = true ∨ ∀ v : Fin 13, v ∉ ({0, 1, 3, 9} : Finset (Fin 13)) → x v = true) →
    (∀ v : Fin 13, x v = true → y v = true) →
    (y 0 = true ∨ y 1 = true ∨ ∀ v : Fin 13, v ∉ ({0, 1, 3, 9} : Finset (Fin 13)) → y v = true) := by
  intro x y hx hxy
  rcases hx with h | h | h
  · exact Or.inl (hxy 0 h)
  · exact Or.inr (Or.inl (hxy 1 h))
  · exact Or.inr (Or.inr (fun v hv => hxy v (h v hv)))

lemma hall : ∀ v : Fin 13, v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 4 ∨ v = 5 ∨ v = 6 ∨ v = 7 ∨
    v = 8 ∨ v = 9 ∨ v = 10 ∨ v = 11 ∨ v = 12 := by
  decide

lemma five : ∀ x : Fin 13 → Bool,
    (x 0 = true ∨ x 1 = true ∨ ∀ v : Fin 13, v ∉ ({0, 1, 3, 9} : Finset (Fin 13)) → x v = true) ↔
    (x 0 = true ∨ x 1 = true ∨
      x = (fun v : Fin 13 => decide (v ∉ ({0, 1, 3, 9} : Finset (Fin 13)))) ∨
      x = (fun v : Fin 13 => decide (v ∉ ({0, 1, 3, 9} : Finset (Fin 13)) ∨ v = 3)) ∨
      x = (fun v : Fin 13 => decide (v ∉ ({0, 1, 3, 9} : Finset (Fin 13)) ∨ v = 9)) ∨
      x = (fun v : Fin 13 => decide (v ∉ ({0, 1, 3, 9} : Finset (Fin 13)) ∨ v = 3 ∨ v = 9))) := by
  intro x
  constructor
  · rintro (h | h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · by_cases h0 : x 0 = true
      · exact Or.inl h0
      by_cases h1 : x 1 = true
      · exact Or.inr (Or.inl h1)
      right
      right
      have h0' : x 0 = false := by simpa using h0
      have h1' : x 1 = false := by simpa using h1
      have h2 := h 2 (by decide)
      have h4 := h 4 (by decide)
      have h5 := h 5 (by decide)
      have h6 := h 6 (by decide)
      have h7 := h 7 (by decide)
      have h8 := h 8 (by decide)
      have h10 := h 10 (by decide)
      have h11 := h 11 (by decide)
      have h12 := h 12 (by decide)
      cases h3 : x 3 <;> cases h9 : x 9
      · left
        funext v
        rcases hall v with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp only [h0', h1', h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12] <;> decide
      · right
        right
        left
        funext v
        rcases hall v with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp only [h0', h1', h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12] <;> decide
      · right
        left
        funext v
        rcases hall v with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp only [h0', h1', h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12] <;> decide
      · right
        right
        right
        funext v
        rcases hall v with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp only [h0', h1', h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12] <;> decide
  · rintro (h | h | rfl | rfl | rfl | rfl)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    all_goals
      right
      right
      decide

lemma card4 : ({(fun v : Fin 13 => decide (v ∉ ({0, 1, 3, 9} : Finset (Fin 13)))),
      (fun v : Fin 13 => decide (v ∉ ({0, 1, 3, 9} : Finset (Fin 13)) ∨ v = 3)),
      (fun v : Fin 13 => decide (v ∉ ({0, 1, 3, 9} : Finset (Fin 13)) ∨ v = 9)),
      (fun v : Fin 13 => decide (v ∉ ({0, 1, 3, 9} : Finset (Fin 13)) ∨ v = 3 ∨ v = 9))} :
      Finset (Fin 13 → Bool)).card = 4 := by
  decide

lemma card_all :
    (Finset.univ.filter (fun x : Fin 13 → Bool => (x 0 = true ∨ x 1 = true ∨
      ∀ v : Fin 13, v ∉ ({0, 1, 3, 9} : Finset (Fin 13)) → x v = true))).card = 6148 := by
  have key : Finset.univ.filter (fun x : Fin 13 → Bool => (x 0 = true ∨ x 1 = true ∨
      ∀ v : Fin 13, v ∉ ({0, 1, 3, 9} : Finset (Fin 13)) → x v = true)) =
      Finset.univ.filter (fun x : Fin 13 → Bool => x 0 = true ∨ x 1 = true) ∪
      ({(fun v : Fin 13 => decide (v ∉ ({0, 1, 3, 9} : Finset (Fin 13)))),
      (fun v : Fin 13 => decide (v ∉ ({0, 1, 3, 9} : Finset (Fin 13)) ∨ v = 3)),
      (fun v : Fin 13 => decide (v ∉ ({0, 1, 3, 9} : Finset (Fin 13)) ∨ v = 9)),
      (fun v : Fin 13 => decide (v ∉ ({0, 1, 3, 9} : Finset (Fin 13)) ∨ v = 3 ∨ v = 9))} :
      Finset (Fin 13 → Bool)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    rw [five x]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  rw [key, Finset.card_union_of_disjoint, card01, card4]
  rw [Finset.disjoint_left]
  intro x hx hx'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx'
  rcases hx' with rfl | rfl | rfl | rfl <;> revert hx <;> decide

lemma colines : ∀ t : Fin 13,
    ((fun v : Fin 13 => decide (v ∉ ({t, t + 1, t + 3, t + 9} : Finset (Fin 13)))) 0 = true ∨
     (fun v : Fin 13 => decide (v ∉ ({t, t + 1, t + 3, t + 9} : Finset (Fin 13)))) 1 = true ∨
     ∀ v : Fin 13, v ∉ ({0, 1, 3, 9} : Finset (Fin 13)) →
      (fun v : Fin 13 => decide (v ∉ ({t, t + 1, t + 3, t + 9} : Finset (Fin 13)))) v = true) := by
  decide

end PEqualNP.Outside.L_meta_1563

theorem PEqualNP.Outside.L_meta_1563 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    (∀ x y : Fin 13 → Bool, (x 0 = true ∨ x 1 = true ∨ ∀ v : Fin 13, v ∉ L 0 → x v = true) → (∀ v : Fin 13, x v = true → y v = true) → (y 0 = true ∨ y 1 = true ∨ ∀ v : Fin 13, v ∉ L 0 → y v = true)) ∧
    (Finset.univ.filter (fun x : Fin 13 → Bool => (x 0 = true ∨ x 1 = true ∨ ∀ v : Fin 13, v ∉ L 0 → x v = true))).card = 6148 ∧
    (∀ t : Fin 13, ((fun v : Fin 13 => decide (v ∉ L t)) 0 = true ∨ (fun v : Fin 13 => decide (v ∉ L t)) 1 = true ∨ ∀ v : Fin 13, v ∉ L 0 → (fun v : Fin 13 => decide (v ∉ L t)) v = true)) ∧
    (Finset.univ.filter (fun x : Fin 13 → Bool => x 0 = true ∨ x 1 = true)).card = 6144 ∧
    (∀ x : Fin 13 → Bool, (x 0 = true ∨ x 1 = true ∨ ∀ v : Fin 13, v ∉ L 0 → x v = true) ↔ (x 0 = true ∨ x 1 = true ∨ x = (fun v : Fin 13 => decide (v ∉ L 0)) ∨
      x = (fun v : Fin 13 => decide (v ∉ L 0 ∨ v = 3)) ∨ x = (fun v : Fin 13 => decide (v ∉ L 0 ∨ v = 9)) ∨
      x = (fun v : Fin 13 => decide (v ∉ L 0 ∨ v = 3 ∨ v = 9)))) := by
  intro L hL
  have h0 : L 0 = ({0, 1, 3, 9} : Finset (Fin 13)) := by
    rw [hL]
    decide
  have hc := PEqualNP.Outside.L_meta_1563.colines
  rw [h0]
  refine ⟨PEqualNP.Outside.L_meta_1563.up, PEqualNP.Outside.L_meta_1563.card_all, ?_,
    PEqualNP.Outside.L_meta_1563.card01, PEqualNP.Outside.L_meta_1563.five⟩
  intro t
  rw [hL t]
  exact hc t
