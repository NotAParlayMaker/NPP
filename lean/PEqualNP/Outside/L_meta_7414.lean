import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7414
open PEqualNP.CircuitLowerBounds



def stp (S : Finset ℕ) (o : ℕ × ℕ × ℕ) : Finset ℕ := insert o.2.1 (insert o.2.2 (S.erase o.1))

theorem back : ∀ (ops : List (ℕ × ℕ × ℕ)) (base : List ℕ) (S : Finset ℕ),
    (∀ i : Fin ops.length, (ops.get i).1 ∈ List.foldl stp S (List.take i ops) ∧
      ((ops.get i).1 = (ops.get i).2.1 &&& (ops.get i).2.2 ∨
       (ops.get i).1 = (ops.get i).2.1 ||| (ops.get i).2.2)) →
    (∀ y ∈ List.foldl stp S ops, y ∈ base) →
    (List.foldl stp S ops).card ≤ S.card + ops.length ∧
    ∃ gs : List ℕ, gs.length ≤ ops.length ∧
      (∀ i : Fin gs.length, ∃ u ∈ base ++ List.take i gs, ∃ v ∈ base ++ List.take i gs,
        gs.get i = u &&& v ∨ gs.get i = u ||| v) ∧
      ∀ y ∈ S, y ∈ base ++ gs := by
  intro ops
  induction ops with
  | nil =>
    intro base S _ hB
    exact ⟨by simp, [], by simp, fun i => i.elim0, fun y hy => by simpa using hB y hy⟩
  | cons o rest ih =>
    intro base S hV hB
    have h0 := hV ⟨0, by simp⟩
    have ht : o.1 ∈ S := by simpa using h0.1
    have hop : o.1 = o.2.1 &&& o.2.2 ∨ o.1 = o.2.1 ||| o.2.2 := by simpa using h0.2
    have hV' : ∀ i : Fin rest.length, (rest.get i).1 ∈ List.foldl stp (stp S o) (List.take i rest) ∧
        ((rest.get i).1 = (rest.get i).2.1 &&& (rest.get i).2.2 ∨
         (rest.get i).1 = (rest.get i).2.1 ||| (rest.get i).2.2) := by
      intro i
      have h := hV ⟨i.val + 1, by simp⟩
      simpa using h
    obtain ⟨hc, gs, hgl, hgP, hgS⟩ := ih base (stp S o) hV' (by simpa using hB)
    have hcard : (stp S o).card ≤ S.card + 1 := by
      unfold stp
      have e := Finset.card_erase_of_mem ht
      have h1 := Finset.card_insert_le o.2.2 (S.erase o.1)
      have h2 := Finset.card_insert_le o.2.1 (insert o.2.2 (S.erase o.1))
      have h3 := Finset.card_pos.2 ⟨_, ht⟩
      omega
    have ha : o.2.1 ∈ base ++ gs := hgS _ (by unfold stp; simp)
    have hb : o.2.2 ∈ base ++ gs := hgS _ (by unfold stp; simp)
    refine ⟨by simp only [List.foldl_cons, List.length_cons]; omega, gs ++ [o.1], by simp; omega, ?_, ?_⟩
    · intro i
      by_cases hi : i.val < gs.length
      · obtain ⟨u, hu, v, hv, huv⟩ := hgP ⟨i.val, hi⟩
        have e1 : List.take i.val (gs ++ [o.1]) = List.take i.val gs :=
          List.take_append_of_le_length (le_of_lt hi)
        have e2 : (gs ++ [o.1]).get i = gs.get ⟨i.val, hi⟩ := by
          simp [List.get_eq_getElem, List.getElem_append_left hi]
        rw [e1, e2]
        exact ⟨u, hu, v, hv, huv⟩
      · have hie : i.val = gs.length := by
          have h5 := i.isLt
          simp only [List.length_append, List.length_singleton] at h5
          omega
        have e1 : List.take i.val (gs ++ [o.1]) = gs := by rw [hie]; simp
        have e2 : (gs ++ [o.1]).get i = o.1 := by
          simp [List.get_eq_getElem, hie]
        rw [e1, e2]
        exact ⟨o.2.1, ha, o.2.2, hb, hop⟩
    · intro y hy
      by_cases hyt : y = o.1
      · rw [hyt]; simp
      · have h6 := hgS y (by unfold stp; simp [Finset.mem_erase, hyt, hy])
        rcases List.mem_append.1 h6 with h | h
        · exact List.mem_append_left _ h
        · exact List.mem_append_right _ (List.mem_append_left _ h)

end PEqualNP.Outside.L_meta_7414

open PEqualNP.Outside.L_meta_7414 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_7414 : have x1 : Finset ℕ → ℕ × ℕ × ℕ → Finset ℕ := fun (x1 : Finset ℕ) (x2 : ℕ × ℕ × ℕ) => Insert.insert x2.2.1 (Insert.insert x2.2.2 (x1.erase x2.1)); have x2 : Finset ℕ → List (ℕ × ℕ × ℕ) → Prop := fun (x2 : Finset ℕ) (x3 : List (ℕ × ℕ × ℕ)) =>   ∀ (x4 : Fin x3.length),     have x5 : ℕ × ℕ × ℕ := x3.get x4;     x5.1 ∈ List.foldl x1 x2 (List.take (↑x4) x3) ∧ (x5.1 = x5.2.1 &&& x5.2.2 ∨ x5.1 = x5.2.1 ||| x5.2.2); have x3 : List ℕ → List ℕ → Prop := fun (x3 x4 : List ℕ) => ∀ (x5 : Fin x4.length), ∃ x6 ∈ x3 ++ List.take (↑x5) x4, ∃ x7 ∈ x3 ++ List.take (↑x5) x4, x4.get x5 = x6 &&& x7 ∨ x4.get x5 = x6 ||| x7; ∀ (x4 : List ℕ) (x5 : Finset ℕ) (x6 : List (ℕ × ℕ × ℕ)), x2 x5 x6 → (∀ x8 ∈ List.foldl x1 x5 x6, x8 ∈ x4) → (List.foldl x1 x5 x6).card ≤ x5.card + x6.length ∧ ∃ (x9 : List ℕ), x9.length ≤ x6.length ∧ x3 x4 x9 ∧ ∀ x10 ∈ x5, x10 ∈ x4 ++ x9 := by
  intro st V P base S ops hV hB
  exact back ops base S hV hB
