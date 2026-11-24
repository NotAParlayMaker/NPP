import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2839

def wireSet (i : ℕ) : Finset (Fin 9) :=
  if h : i < 9 then {⟨i, h⟩}
  else if i = 9 then {(0 : Fin 9), (4 : Fin 9)}
  else ∅

lemma getD_eq (x4 : Fin 9 → Bool) (i : ℕ) :
    (List.ofFn x4 ++ [x4 (0 : Fin 9) || x4 (4 : Fin 9)]).getD i Bool.false =
    Decidable.decide (∃ k ∈ wireSet i, x4 k = Bool.true) := by
  unfold wireSet
  by_cases h1 : i < 9
  · rw [dite_eq_left h1]
    have hlen : i < (List.ofFn x4).length := by simp [h1]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlen, List.getElem?_ofFn]
    simp [h1]
  · rw [dite_eq_right h1]
    by_cases h2 : i = 9
    · subst h2
      rw [ite_eq_left rfl]
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
      simp
    · rw [ite_eq_right h2]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
      simp

lemma wireSet_card_le (i : ℕ) : (wireSet i).card ≤ 2 := by
  unfold wireSet
  split_ifs
  · simp
  · exact le_trans (Finset.card_insert_le _ _) (by simp)
  · simp

lemma wireSet_union_shape (a b : ℕ) :
    (wireSet a ∪ wireSet b).card ≤ 2 ∨
    ∃ c : Fin 9, wireSet a ∪ wireSet b = {(0 : Fin 9), (4 : Fin 9), c} := by
  unfold wireSet
  by_cases ha1 : a < 9 <;> by_cases hb1 : b < 9
  · left
    simp only [dite_eq_left ha1, dite_eq_left hb1]
    exact le_trans (Finset.card_union_le _ _) (by simp)
  · by_cases hb2 : b = 9
    · right
      refine ⟨⟨a, ha1⟩, ?_⟩
      simp only [dite_eq_left ha1, dite_eq_right hb1, ite_eq_left hb2]
      ext k
      simp [or_comm, or_left_comm]
    · left
      simp only [dite_eq_left ha1, dite_eq_right hb1, ite_eq_right hb2]
      simp
  · by_cases ha2 : a = 9
    · right
      refine ⟨⟨b, hb1⟩, ?_⟩
      simp only [dite_eq_right ha1, ite_eq_left ha2, dite_eq_left hb1]
      ext k
      simp [or_comm, or_left_comm]
    · left
      simp only [dite_eq_right ha1, ite_eq_right ha2, dite_eq_left hb1]
      simp
  · left
    by_cases ha2 : a = 9 <;> by_cases hb2 : b = 9
    · simp only [dite_eq_right ha1, ite_eq_left ha2, dite_eq_right hb1, ite_eq_left hb2, Finset.union_idempotent]
      exact le_trans (Finset.card_insert_le _ _) (by simp)
    · simp only [dite_eq_right ha1, ite_eq_left ha2, dite_eq_right hb1, ite_eq_right hb2, Finset.union_empty]
      exact le_trans (Finset.card_insert_le _ _) (by simp)
    · simp only [dite_eq_right ha1, ite_eq_right ha2, dite_eq_right hb1, ite_eq_left hb2, Finset.empty_union]
      exact le_trans (Finset.card_insert_le _ _) (by simp)
    · simp only [dite_eq_right ha1, ite_eq_right ha2, dite_eq_right hb1, ite_eq_right hb2, Finset.empty_union]
      simp

end PEqualNP.Outside.L_meta_2839

theorem PEqualNP.Outside.L_meta_2839 :
    ∀ (x1 : List ℕ), x1.length ≤ (2 : ℕ) → ∃ (x3 : Finset (Fin (9 : ℕ))), (x3.card ≤ (2 : ℕ) ∨ ∃ (x4 : Fin (9 : ℕ)), x3 = {(0 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ)), x4}) ∧ ∀ (x4 : Fin (9 : ℕ) → Bool), PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x5 : ℕ) => (List.ofFn x4 ++ [x4 (0 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ))]).getD x5 Bool.false) x1) = Decidable.decide (∃ x5 ∈ x3, x4 x5 = Bool.true) := by
  intro x1 hlen
  match x1 with
  | [] =>
    refine ⟨∅, Or.inl (by simp), ?_⟩
    intro x4
    simp [PEqualNP.CircuitLowerBounds.GateOp.eval]
  | [a] =>
    refine ⟨PEqualNP.Outside.L_meta_2839.wireSet a, Or.inl (PEqualNP.Outside.L_meta_2839.wireSet_card_le a), ?_⟩
    intro x4
    simp only [List.map, PEqualNP.CircuitLowerBounds.GateOp.eval, PEqualNP.Outside.L_meta_2839.getD_eq, List.any_cons, List.any_nil, id_eq, Bool.or_false]
  | [a, b] =>
    refine ⟨PEqualNP.Outside.L_meta_2839.wireSet a ∪ PEqualNP.Outside.L_meta_2839.wireSet b, PEqualNP.Outside.L_meta_2839.wireSet_union_shape a b, ?_⟩
    intro x4
    simp only [List.map, PEqualNP.CircuitLowerBounds.GateOp.eval, PEqualNP.Outside.L_meta_2839.getD_eq]
    simp only [List.any_cons, List.any_nil, id_eq, Bool.or_false]
    by_cases h : ∃ x5 ∈ PEqualNP.Outside.L_meta_2839.wireSet a ∪ PEqualNP.Outside.L_meta_2839.wireSet b, x4 x5 = Bool.true
    · rw [decide_eq_true h]
      rcases h with ⟨k, hk, hxk⟩
      rcases Finset.mem_union.mp hk with hka | hkb
      · have : ∃ x5 ∈ PEqualNP.Outside.L_meta_2839.wireSet a, x4 x5 = Bool.true := ⟨k, hka, hxk⟩
        simp [this]
      · have : ∃ x5 ∈ PEqualNP.Outside.L_meta_2839.wireSet b, x4 x5 = Bool.true := ⟨k, hkb, hxk⟩
        simp [this]
    · rw [decide_eq_false h]
      have ha : ¬ ∃ x5 ∈ PEqualNP.Outside.L_meta_2839.wireSet a, x4 x5 = Bool.true := by
        rintro ⟨k, hka, hxk⟩
        exact h ⟨k, Finset.mem_union_left _ hka, hxk⟩
      have hb : ¬ ∃ x5 ∈ PEqualNP.Outside.L_meta_2839.wireSet b, x4 x5 = Bool.true := by
        rintro ⟨k, hkb, hxk⟩
        exact h ⟨k, Finset.mem_union_right _ hkb, hxk⟩
      simp [ha, hb]
  | _ :: _ :: _ :: _ =>
    simp at hlen
