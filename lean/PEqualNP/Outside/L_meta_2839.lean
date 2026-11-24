import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2839

def S (a : ℕ) : Finset (Fin 9) :=
  if a = 9 then {0, 4} else if h : a < 9 then {⟨a, h⟩} else ∅

lemma S_nine : S 9 = {0, 4} := by
  simp [S]

lemma S_lt (a : ℕ) (h : a < 9) : S a = {⟨a, h⟩} := by
  have h9 : a ≠ 9 := by omega
  simp [S, h9, h]

lemma S_gt (a : ℕ) (h : 9 < a) : S a = ∅ := by
  have h9 : a ≠ 9 := by omega
  have h8 : ¬ a < 9 := by omega
  simp [S, h9, h8]

lemma S_card (a : ℕ) : (S a).card ≤ 2 := by
  rcases lt_trichotomy a 9 with h | h | h
  · rw [S_lt a h]
    simp
  · subst h
    rw [S_nine]
    decide
  · rw [S_gt a h]
    simp

lemma S_card_one (a : ℕ) (ha : a ≠ 9) : (S a).card ≤ 1 := by
  rcases lt_trichotomy a 9 with h | h | h
  · rw [S_lt a h]
    simp
  · exact absurd h ha
  · rw [S_gt a h]
    simp

lemma val_iff (a : ℕ) (x : Fin 9 → Bool) :
    (List.ofFn x ++ [x 0 || x 4]).getD a false = true ↔ ∃ i ∈ S a, x i = true := by
  rcases lt_trichotomy a 9 with h | h | h
  · have hlen : a < (List.ofFn x).length := by
      rw [List.length_ofFn]
      exact h
    rw [S_lt a h, List.getD_eq_getElem?_getD, List.getElem?_append_left hlen, List.getElem?_ofFn]
    simp [h]
  · subst h
    rw [S_nine]
    simp [List.getD_eq_getElem?_getD]
  · have hlen : (List.ofFn x ++ [x 0 || x 4]).length ≤ a := by
      rw [List.length_append, List.length_ofFn]
      simp
      omega
    rw [S_gt a h, List.getD_eq_default _ _ hlen]
    simp

lemma union_right (b : ℕ) (hb : b < 9) :
    S 9 ∪ S b = {0, 4, ⟨b, hb⟩} := by
  rw [S_nine, S_lt b hb]
  ext i
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
  tauto

lemma union_left (a : ℕ) (ha : a < 9) :
    S a ∪ S 9 = {0, 4, ⟨a, ha⟩} := by
  rw [S_nine, S_lt a ha]
  ext i
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
  tauto

lemma shape (a b : ℕ) :
    (S a ∪ S b).card ≤ 2 ∨ ∃ t : Fin 9, S a ∪ S b = {0, 4, t} := by
  by_cases ha : a = 9
  · subst ha
    rcases lt_trichotomy b 9 with hb | hb | hb
    · exact Or.inr ⟨⟨b, hb⟩, union_right b hb⟩
    · subst hb
      left
      rw [Finset.union_self]
      exact S_card 9
    · left
      rw [S_gt b hb, Finset.union_empty]
      exact S_card 9
  · by_cases hb : b = 9
    · subst hb
      rcases lt_trichotomy a 9 with h | h | h
      · exact Or.inr ⟨⟨a, h⟩, union_left a h⟩
      · exact absurd h ha
      · left
        rw [S_gt a h, Finset.empty_union]
        exact S_card 9
    · left
      have h1 := S_card_one a ha
      have h2 := S_card_one b hb
      have h3 := Finset.card_union_le (S a) (S b)
      omega

end PEqualNP.Outside.L_meta_2839

theorem PEqualNP.Outside.L_meta_2839 : ∀ (x1 : List ℕ), x1.length ≤ (2 : ℕ) → ∃ (x3 : Finset (Fin (9 : ℕ))), (x3.card ≤ (2 : ℕ) ∨ ∃ (x4 : Fin (9 : ℕ)), x3 = {(0 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ)), x4}) ∧ ∀ (x4 : Fin (9 : ℕ) → Bool), PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x5 : ℕ) => (List.ofFn x4 ++ [x4 (0 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ))]).getD x5 Bool.false) x1) = Decidable.decide (∃ x5 ∈ x3, x4 x5 = Bool.true) := by
  intro x1 hlen
  rcases x1 with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
  · refine ⟨∅, Or.inl (by simp), ?_⟩
    intro x4
    simp [PEqualNP.CircuitLowerBounds.GateOp.eval]
  · refine ⟨PEqualNP.Outside.L_meta_2839.S a, Or.inl (PEqualNP.Outside.L_meta_2839.S_card a), ?_⟩
    intro x4
    have ha := PEqualNP.Outside.L_meta_2839.val_iff a x4
    rw [Bool.eq_iff_iff, decide_eq_true_iff, ← ha]
    simp [PEqualNP.CircuitLowerBounds.GateOp.eval]
  · refine ⟨PEqualNP.Outside.L_meta_2839.S a ∪ PEqualNP.Outside.L_meta_2839.S b, PEqualNP.Outside.L_meta_2839.shape a b, ?_⟩
    intro x4
    have ha := PEqualNP.Outside.L_meta_2839.val_iff a x4
    have hb := PEqualNP.Outside.L_meta_2839.val_iff b x4
    rw [Bool.eq_iff_iff, decide_eq_true_iff]
    simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
      Bool.or_false, Bool.or_eq_true, id_eq, Finset.mem_union]
    rw [ha, hb]
    constructor
    · rintro (⟨i, hi, hx⟩ | ⟨i, hi, hx⟩)
      · exact ⟨i, Or.inl hi, hx⟩
      · exact ⟨i, Or.inr hi, hx⟩
    · rintro ⟨i, hi | hi, hx⟩
      · exact Or.inl ⟨i, hi, hx⟩
      · exact Or.inr ⟨i, hi, hx⟩
  · exfalso
    simp at hlen
