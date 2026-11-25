import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9113_aux

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


def fano (x : Fin 14 → Bool) : Prop := ∃ (x7 : Fin (7 : ℕ)) (x8 : Fin (7 : ℕ)), (x7 = x8 ∨ x7 = x8 + (1 : Fin (7 : ℕ)) ∨ x7 = x8 + (3 : Fin (7 : ℕ))) ∧ x (Fin.castAdd (7 : ℕ) x7) = Bool.true ∧ x (Fin.natAdd (7 : ℕ) x8) = Bool.true

theorem f_single : ∀ o : Fin 14, ¬ fano (fun k => decide (k = o)) := by
  unfold fano; decide

theorem f_cof : ∀ o : Fin 14, fano (fun k => decide (k ≠ o)) := by
  unfold fano; decide

theorem f_inc : fano (fun k => decide (k = 0 ∨ k = 7)) := by
  unfold fano; decide

end PEqualNP.Outside.L_meta_9113_aux

open PEqualNP.Outside.L_meta_9113_aux in
theorem PEqualNP.Outside.L_meta_9113 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   x1.size ≤ (27 : ℕ) →     PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 →       (∀ x4 < x1.size, PEqualNP.TopForm.opnd x1 x4 (0 : Fin (2 : ℕ)) ≠ PEqualNP.TopForm.opnd x1 x4 (1 : Fin (2 : ℕ))) →         (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (0 : ℕ)).op = PEqualNP.CircuitLowerBounds.GateOp.or →           (∀ (x6 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x6) = Bool.true ↔ ∃ (x7 : Fin (7 : ℕ)) (x8 : Fin (7 : ℕ)), (x7 = x8 ∨ x7 = x8 + (1 : Fin (7 : ℕ)) ∨ x7 = x8 + (3 : Fin (7 : ℕ))) ∧ x6 (Fin.castAdd (7 : ℕ) x7) = Bool.true ∧ x6 (Fin.natAdd (7 : ℕ) x8) = Bool.true) →             (have x7 : ℕ := PEqualNP.TopForm.opnd x1 (0 : ℕ) (0 : Fin (2 : ℕ));               have x8 : ℕ := PEqualNP.TopForm.opnd x1 (0 : ℕ) (1 : Fin (2 : ℕ));               Nat.testBit (365118556550 : ℕ) ((14 : ℕ) * Min.min x7 x8 + Max.max x7 x8) = Bool.true) →               (¬∃ (x8 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[(1 : ℕ)]? = Option.some x8) → ∃ (x9 : Bool), PEqualNP.ReadK.lineSingle x1 (14 : ℕ) (fun (x10 : ℕ) => x10 == if x9 = Bool.true then (7 : ℕ) else (0 : ℕ)) (0 : ℕ) (7 : ℕ) = Bool.true := by
  intro C _ hA _ _ hf _ h1
  exfalso
  have hf' : ∀ x : Fin 14 → Bool, PEqualNP.MetaComplexity.circuitFun 14 C x = true ↔ fano x := fun x => hf x
  rcases shape 14 C hA h1 with h | ⟨o, h⟩ | ⟨i, j, h⟩ | ⟨i, j, h⟩
  · have := (hf' _).2 f_inc
    rw [h] at this
    simp at this
  · apply f_single o
    apply (hf' _).1
    rw [h]
    simp
  · apply f_single i
    apply (hf' _).1
    rw [h]
    simp
  · have := (hf' _).2 (f_cof i)
    rw [h] at this
    simp at this
