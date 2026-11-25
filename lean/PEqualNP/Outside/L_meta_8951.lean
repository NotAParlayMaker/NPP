import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8951_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

theorem getD_ofFn {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    (List.ofFn x).getD i false = if h : i < n then x ⟨i, h⟩ else false := by
  split_ifs with h
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, h]

theorem shape (n : ℕ) (C : Circuit) (hA : IsAO2 n C)
    (h1 : ¬∃ g : Gate, C.gates[(1 : ℕ)]? = Option.some g) :
    (∀ x : Fin n → Bool, circuitFun n C x = false) ∨
    (∃ o : Fin n, ∀ x : Fin n → Bool, circuitFun n C x = x o) ∨
    (∃ i j : Fin n, ∀ x : Fin n → Bool, circuitFun n C x = (x i || x j)) ∨
    (∃ i j : Fin n, ∀ x : Fin n → Bool, circuitFun n C x = (x i && x j)) := by
  obtain ⟨gs, o⟩ := C
  obtain ⟨hAO, hRB, h2⟩ := hA
  match gs with
  | [] =>
    by_cases ho : o < n
    · right; left
      refine ⟨⟨o, ho⟩, fun x => ?_⟩
      simp [circuitFun, Circuit.eval, Circuit.wires, ho]
    · left
      intro x
      simp [circuitFun, Circuit.eval, Circuit.wires, ho]
  | [g] =>
    obtain ⟨op, ins⟩ := g
    have hl : ins.length = 2 := h2 ⟨op, ins⟩ (by simp)
    match ins, hl with
    | [i, j], _ =>
      have hrb := hRB 0 (by simp)
      have hi : i < n := by simpa [PEqualNP.MetaComplexity.NestedCover.gateAt] using hrb i (by simp [PEqualNP.MetaComplexity.NestedCover.gateAt])
      have hj : j < n := by simpa [PEqualNP.MetaComplexity.NestedCover.gateAt] using hrb j (by simp [PEqualNP.MetaComplexity.NestedCover.gateAt])
      have hop := hAO ⟨op, [i, j]⟩ (by simp)
      have hw : ∀ x : Fin n → Bool, circuitFun n ⟨[⟨op, [i, j]⟩], o⟩ x =
          (List.ofFn x ++ [op.eval [x ⟨i, hi⟩, x ⟨j, hj⟩]]).getD o false := by
        intro x
        simp [circuitFun, Circuit.eval, Circuit.wires, hi, hj]
      rcases lt_trichotomy o n with ho | ho | ho
      · right; left
        refine ⟨⟨o, ho⟩, fun x => ?_⟩
        rw [hw]
        have hlt : o < (List.ofFn x).length := by simpa using ho
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
        simp [ho]
      · subst ho
        rcases hop with hop | hop
        · right; right; right
          refine ⟨⟨i, hi⟩, ⟨j, hj⟩, fun x => ?_⟩
          rw [hw]
          simp at hop
          simp [hop, List.getD_eq_getElem?_getD, GateOp.eval]
        · right; right; left
          refine ⟨⟨i, hi⟩, ⟨j, hj⟩, fun x => ?_⟩
          rw [hw]
          simp at hop
          simp [hop, List.getD_eq_getElem?_getD, GateOp.eval]
      · left
        intro x
        rw [hw]
        have : (List.ofFn x ++ [op.eval [x ⟨i, hi⟩, x ⟨j, hj⟩]]).length ≤ o := by simp; omega
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none this]
  | _ :: _ :: _ =>
    exact absurd ⟨_, rfl⟩ h1

end PEqualNP.Outside.L_meta_8951_aux

open PEqualNP.Outside.L_meta_8951_aux in
theorem PEqualNP.Outside.L_meta_8951 : ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   have x5 : Finset (Fin x1 × Fin x2) → Finset (Fin (x1 + x2)) := fun (x5 : Finset (Fin x1 × Fin x2)) => x5.biUnion fun (x6 : Fin x1 × Fin x2) => {Fin.castAdd x2 x6.1, Fin.natAdd x1 x6.2};   (∀ (x6 x7 : Fin x1) (x8 x9 : Fin x2), x6 ≠ x7 → x8 ≠ x9 → ¬((x6, x8) ∈ x3 ∧ (x6, x9) ∈ x3 ∧ (x7, x8) ∈ x3 ∧ (x7, x9) ∈ x3)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x4 → (∀ (x8 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x4 x8 = Decidable.decide (∃ x9 ∈ x3, x8 (Fin.castAdd x2 x9.1) = Bool.true ∧ x8 (Fin.natAdd x1 x9.2) = Bool.true)) → (¬∃ (x9 : Finset (Fin x1 × Fin x2)) (x10 : Finset (Fin x1 × Fin x2)) (x11 : Fin (x1 + x2)), x9.Nonempty ∧ x9 ∪ x10 = x3 ∧ Disjoint (x5 x9) (x5 x10) ∧ ∀ x12 ∈ x9, Fin.castAdd x2 x12.1 = x11 ∨ Fin.natAdd x1 x12.2 = x11) → (¬∃ (x10 : PEqualNP.CircuitLowerBounds.Gate), x4.gates[(1 : ℕ)]? = Option.some x10) → ∃ (x11 : Finset (Fin x1)) (x12 : Finset (Fin x2)), (∀ x13 ∈ x3, x13.1 ∈ x11 ∨ x13.2 ∈ x12) ∧ x3.card + x11.card + x12.card ≤ x4.size + (1 : ℕ) := by
  intro x1 x2 x3 x4 x5 _ hA hf hstar h1
  rcases x3.eq_empty_or_nonempty with h0 | ⟨⟨a, b⟩, hab⟩
  · subst h0
    exact ⟨∅, ∅, by simp, by simp⟩
  exfalso
  have hne : ∀ (c : Fin x1) (d : Fin x2), Fin.castAdd x2 c ≠ Fin.natAdd x1 d := by
    intro c d h
    have := congrArg Fin.val h
    simp at this
    omega
  have hsingle : ∀ o : Fin (x1 + x2), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x4 (fun k => decide (k = o)) = false := by
    intro o
    rw [hf]
    simp only [decide_eq_false_iff_not, not_exists, not_and, decide_eq_true_eq]
    intro e _ h1 h2
    exact hne _ _ (h1.trans h2.symm)
  have hedge : ∀ c d, (c, d) ∈ x3 → PEqualNP.MetaComplexity.circuitFun (x1 + x2) x4
      (fun k => decide (k = Fin.castAdd x2 c ∨ k = Fin.natAdd x1 d)) = true := by
    intro c d hcd
    rw [hf]
    simp only [decide_eq_true_eq]
    exact ⟨(c, d), hcd, by simp, by simp⟩
  rcases shape (x1 + x2) x4 hA h1 with h | ⟨o, h⟩ | ⟨i, j, h⟩ | ⟨i, j, h⟩
  · have := hedge a b hab
    rw [h] at this
    exact absurd this (by simp)
  · have := hsingle o
    rw [h] at this
    simp at this
  · have := hsingle i
    rw [h] at this
    simp at this
  · apply hstar
    refine ⟨x3, ∅, i, ⟨(a, b), hab⟩, by simp, by simp [x5], ?_⟩
    intro e he
    have := hedge e.1 e.2 he
    rw [h] at this
    simp at this
    rcases this.1 with h' | h'
    · left; exact h'.symm
    · right; exact h'.symm
