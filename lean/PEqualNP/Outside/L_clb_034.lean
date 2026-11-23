import Mathlib
import PEqualNP.Defs

namespace LClb034

open PEqualNP.CircuitLowerBounds

-- A circuit with at most one gate, each gate reading at most one wire, reads its output
-- off a single position of the input, for inputs of a fixed length.
lemma one_pos (n : ℕ) (C : Circuit) (hlen : C.gates.length ≤ 1)
    (hin : ∀ g ∈ C.gates, g.inputs.length ≤ 1) :
    ∃ p : ℕ, ∀ x y : List Bool, x.length = n → y.length = n →
      x.getD p false = y.getD p false → C.eval x = C.eval y := by
  obtain ⟨gates, o⟩ := C
  simp only at hlen hin
  match gates, hlen, hin with
  | [], _, _ =>
    refine ⟨o, fun x y _ _ h => ?_⟩
    simpa [Circuit.eval, Circuit.wires] using h
  | [g], _, hin =>
    have hg : g.inputs.length ≤ 1 := hin g (by simp)
    obtain ⟨op, ins⟩ := g
    simp only at hg
    match ins, hg with
    | [], _ =>
      refine ⟨o, fun x y hx hy h => ?_⟩
      simp only [Circuit.eval, Circuit.wires, List.foldl_cons, List.foldl_nil, List.map_nil]
      rcases lt_trichotomy o n with ho | ho | ho
      · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
        exact h
      · subst ho
        rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
        simp [hx, hy]
      · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]
    | [i], _ =>
      refine ⟨if o < n then o else i, fun x y hx hy h => ?_⟩
      simp only [Circuit.eval, Circuit.wires, List.foldl_cons, List.foldl_nil, List.map_cons,
        List.map_nil]
      rcases lt_trichotomy o n with ho | ho | ho
      · rw [if_pos ho] at h
        rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
        exact h
      · rw [if_neg (by omega)] at h
        subst ho
        rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
        simp only [List.getD_eq_getElem?_getD] at h
        simp [hx, hy, h]
      · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]
  | _ :: _ :: _, h, _ => simp at h

lemma getD_set_ne (n j p : ℕ) (hjp : j ≠ p) :
    ((List.replicate n true).set j false).getD p false = (List.replicate n true).getD p false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set_ne hjp]

lemma all_set_false (n j : ℕ) (hj : j < n) :
    ((List.replicate n true).set j false).all id = false := by
  rw [Bool.eq_false_iff]
  intro h
  rw [List.all_eq_true] at h
  have hmem : false ∈ (List.replicate n true).set j false :=
    List.mem_set (by simpa using hj) false
  exact absurd (h false hmem) (by simp)

end LClb034

theorem PEqualNP.Outside.L_clb_034 : ∀ (n d : ℕ), 2 ≤ n → ({x : List Bool | x.all id = true} : Language Bool) ∉ PEqualNP.CircuitLowerBounds.SizeDepth {PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or, PEqualNP.CircuitLowerBounds.GateOp.not} (fun m : ℕ => if m = n then 1 else m + 2) d := by
  intro n d hn hL
  obtain ⟨C, hg, hs, -, hdec⟩ := hL n
  simp only [↓reduceIte] at hg hs
  obtain ⟨p, hp⟩ := LClb034.one_pos n C hs (fun g h => (hg g h).2)
  obtain ⟨j, hj, hjp⟩ : ∃ j, j < n ∧ j ≠ p := by
    by_cases h0 : p = 0
    · exact ⟨1, by omega, by omega⟩
    · exact ⟨0, by omega, fun h => h0 h.symm⟩
  have hall : (List.replicate n true).all id = true := by
    rw [List.all_eq_true]
    intro b hb
    rw [List.eq_of_mem_replicate hb]
    rfl
  have ha : C.eval (List.replicate n true) = true := (hdec _ (by simp)).2 hall
  have hb : C.eval ((List.replicate n true).set j false) = false := by
    rw [Bool.eq_false_iff]
    intro h
    have hmem := (hdec _ (by simp)).1 h
    have hall : ((List.replicate n true).set j false).all id = true := hmem
    rw [LClb034.all_set_false n j hj] at hall
    exact Bool.false_ne_true hall
  have heq := hp ((List.replicate n true).set j false) (List.replicate n true) (by simp) (by simp)
    (LClb034.getD_set_ne n j p hjp)
  rw [hb, ha] at heq
  exact Bool.false_ne_true heq
