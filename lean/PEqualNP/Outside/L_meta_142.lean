import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_142

open PEqualNP.MetaComplexity

abbrev Input := Fin 5 → Bool
abbrev Formula := DMFormula 5

def target (x : Input) : Bool :=
  (x 0 && (x 1 || x 2)) || ((x 1 || x 2) && x 3) || (x 3 && x 4)

def vars : Formula → Finset (Fin 5)
  | .lit i _ => {i}
  | .and a b => vars a ∪ vars b
  | .or a b => vars a ∪ vars b

lemma vars_nonempty (a : Formula) : (vars a).Nonempty := by
  induction a with
  | lit i b => exact ⟨i, by simp [vars]⟩
  | and a b ih _ => exact ih.mono Finset.subset_union_left
  | or a b ih _ => exact ih.mono Finset.subset_union_left

lemma vars_card (a : Formula) : (vars a).card ≤ a.leaves := by
  induction a with
  | lit i b => simp [vars, DMFormula.leaves]
  | and a b ha hb =>
    exact (Finset.card_union_le _ _).trans (Nat.add_le_add ha hb)
  | or a b ha hb =>
    exact (Finset.card_union_le _ _).trans (Nat.add_le_add ha hb)

lemma eval_agree (a : Formula) (x y : Input)
    (h : ∀ i ∈ vars a, x i = y i) : a.eval x = a.eval y := by
  induction a with
  | lit i b =>
    simp only [DMFormula.eval, h i (by simp [vars])]
  | and a b ha hb =>
    simp only [DMFormula.eval,
      ha (fun i hi => h i (Finset.mem_union_left _ hi)),
      hb (fun i hi => h i (Finset.mem_union_right _ hi))]
  | or a b ha hb =>
    simp only [DMFormula.eval,
      ha (fun i hi => h i (Finset.mem_union_left _ hi)),
      hb (fun i hi => h i (Finset.mem_union_right _ hi))]

set_option maxRecDepth 10000 in
lemma essential : ∀ i : Fin 5, ∃ x : Input,
    target (Function.update x i (!x i)) ≠ target x := by
  decide +kernel

lemma uses_all (a : Formula) (h : ∀ x, a.eval x = target x) :
    vars a = Finset.univ := by
  ext i
  simp only [Finset.mem_univ, iff_true]
  by_contra hi
  obtain ⟨x, hx⟩ := essential i
  apply hx
  rw [← h, ← h]
  apply eval_agree
  intro j hj
  have hn : j ≠ i := by
    intro e
    subst j
    exact hi hj
  exact Function.update_of_ne hn _ _

def bits (m : Fin 32) : Input := fun i => m.val.testBit i.val

def mix (p x y : Input) : Input := fun i => if p i then x i else y i

set_option maxRecDepth 10000 in
set_option synthInstance.maxSize 256 in
lemma bits_surj : ∀ p : Input, ∃ m : Fin 32, ∀ i, bits m i = p i := by
  decide +kernel

-- At each nonconstant mask and each Boolean value, these inputs have that
-- value but their mixed input has the opposite value.
def witness (value : Bool) (m : Fin 32) : Fin 32 × Fin 32 :=
  (if value then truePairs else falsePairs)[m.val]!
  where
    truePairs : List (Fin 32 × Fin 32) := [(0, 0), (10, 3), (5, 3), (5, 3), (3, 5), (3, 5), (24, 3), (10, 3),
      (3, 10), (3, 24), (3, 10), (5, 3), (3, 5), (3, 5), (3, 10), (24, 3),
      (3, 24), (3, 24), (5, 3), (5, 3), (3, 5), (3, 5), (24, 3), (10, 3),
      (3, 10), (3, 24), (3, 10), (5, 3), (3, 5), (3, 5), (3, 10), (0, 0)]
    falsePairs : List (Fin 32 × Fin 32) := [(0, 0), (1, 2), (2, 1), (1, 4), (4, 1), (1, 2), (2, 1), (2, 8),
      (8, 2), (1, 2), (2, 1), (1, 4), (4, 1), (1, 2), (2, 1), (8, 16),
      (16, 8), (1, 2), (2, 1), (1, 4), (4, 1), (1, 2), (2, 1), (2, 8),
      (8, 2), (1, 2), (2, 1), (1, 4), (4, 1), (1, 2), (2, 1), (0, 0)]

set_option maxRecDepth 10000 in
lemma witness_spec : ∀ (m : Fin 32) (value : Bool),
    (∃ i, bits m i = true) → (∃ i, bits m i = false) →
      let x := bits (witness value m).1
      let y := bits (witness value m).2
      target x = value ∧ target y = value ∧ target (mix (bits m) x y) ≠ value := by
  decide +kernel

lemma root_impossible (a b : Formula) (op : Bool → Bool → Bool) (value : Bool)
    (left_value : ∀ u v, op u v = value → u = value)
    (right_value : ∀ u v, op u v = value → v = value)
    (same_value : op value value = value)
    (hsize : a.leaves + b.leaves ≤ 5)
    (hvars : vars a ∪ vars b = Finset.univ)
    (heval : ∀ x, op (a.eval x) (b.eval x) = target x) : False := by
  have hdisj : Disjoint (vars a) (vars b) := by
    have hcard := Finset.card_union_add_card_inter (vars a) (vars b)
    rw [hvars] at hcard
    simp only [Finset.card_univ, Fintype.card_fin] at hcard
    have ha := vars_card a
    have hb := vars_card b
    apply Finset.disjoint_iff_inter_eq_empty.mpr
    apply Finset.card_eq_zero.mp
    omega
  obtain ⟨m, hm⟩ := bits_surj (fun i => decide (i ∈ vars a))
  have hl : ∀ i ∈ vars a, bits m i = true := by
    intro i hi
    simp [hm i, hi]
  have hr : ∀ i ∈ vars b, bits m i = false := by
    intro i hi
    have hn : i ∉ vars a := fun ha => Finset.disjoint_left.mp hdisj ha hi
    simp [hm i, hn]
  obtain ⟨i, hi⟩ := vars_nonempty a
  obtain ⟨j, hj⟩ := vars_nonempty b
  let x := bits (witness value m).1
  let y := bits (witness value m).2
  have ⟨hx, hy, hxy⟩ := witness_spec m value ⟨i, hl i hi⟩ ⟨j, hr j hj⟩
  change target x = value at hx
  change target y = value at hy
  change target (mix (bits m) x y) ≠ value at hxy
  apply hxy
  have ha : a.eval (mix (bits m) x y) = a.eval x :=
    eval_agree _ _ _ (fun k hk => by simp [mix, hl k hk])
  have hb : b.eval (mix (bits m) x y) = b.eval y :=
    eval_agree _ _ _ (fun k hk => by simp [mix, hr k hk])
  rw [← heval, ha, hb, left_value _ _ ((heval x).trans hx),
    right_value _ _ ((heval y).trans hy)]
  exact same_value

lemma lower (a : Formula) (h : ∀ x, a.eval x = target x) : 6 ≤ a.leaves := by
  by_contra hn
  have huv := uses_all a h
  have hs : a.leaves ≤ 5 := by omega
  cases a with
  | lit i b =>
    have hc := congrArg Finset.card huv
    simp [vars] at hc
  | and a b =>
    exact root_impossible a b Bool.and true
      (by decide) (by decide) rfl hs huv h
  | or a b =>
    exact root_impossible a b Bool.or false
      (by decide) (by decide) rfl hs huv h

def upperFormula : Formula :=
  .or (.and (.or (.lit 0 true) (.lit 3 true)) (.or (.lit 1 true) (.lit 2 true)))
    (.and (.lit 3 true) (.lit 4 true))

lemma upper_eval : ∀ x, upperFormula.eval x = target x := by decide +kernel

end PEqualNP.Outside.L_meta_142

open PEqualNP.Outside.L_meta_142

theorem PEqualNP.Outside.L_meta_142 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasLeafSize 5 (fun x : Fin 5 → Bool => (x 0 && (x 1 || x 2)) || ((x 1 || x 2) && x 3) || (x 3 && x 4)) s ↔ 6 ≤ s := by
  intro s
  change PEqualNP.MetaComplexity.HasLeafSize 5 target s ↔ 6 ≤ s
  constructor
  · rintro ⟨a, hsize, heval⟩
    exact (lower a heval).trans hsize
  · intro hs
    exact ⟨upperFormula, hs, upper_eval⟩
