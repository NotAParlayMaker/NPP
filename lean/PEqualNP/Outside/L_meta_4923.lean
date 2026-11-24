import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4923

open PEqualNP.CircuitLowerBounds

-- One evaluation step of a circuit: append the value of the next gate.
def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stp x := rfl

theorem fold_len (gs : List Gate) (w : List Bool) :
    (gs.foldl stp w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => rw [List.foldl_cons, ih]; simp [stp]; omega

theorem fold_pre (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stp w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (stp w g) (by simp [stp]; omega)]
    exact List.getD_append _ _ _ _ hi

theorem fold_out (gs : List Gate) (w : List Bool) (i : ℕ) (hi : w.length + gs.length ≤ i) :
    (gs.foldl stp w).getD i false = false :=
  List.getD_eq_default _ _ (by rw [fold_len]; exact hi)

theorem fold_at (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < gs.length) :
    (gs.foldl stp w).getD (w.length + k) false =
      gs[k].op.eval (gs[k].inputs.map fun i => ((gs.take k).foldl stp w).getD i false) := by
  have hW : ((gs.take k).foldl stp w).length = w.length + k := by
    rw [fold_len, List.length_take]; omega
  have e1 : gs.foldl stp w = (gs.drop (k + 1)).foldl stp (stp ((gs.take k).foldl stp w) gs[k]) := by
    calc gs.foldl stp w = (gs.take k ++ gs.drop k).foldl stp w := by rw [List.take_append_drop]
      _ = (gs.drop k).foldl stp ((gs.take k).foldl stp w) := List.foldl_append
      _ = _ := by rw [List.drop_eq_getElem_cons hk, List.foldl_cons]
  rw [e1, fold_pre _ _ _ (by simp [stp, hW])]
  simp only [stp]
  rw [List.getD_append_right _ _ _ _ (by omega), hW]
  simp

-- The inputs reached by wire `w` of the finished circuit, and by wire `a` after `k` gates.
def Sset (n : ℕ) (C : Circuit) (w : ℕ) : Finset (Fin n) :=
  {i : Fin n | (C.wires (List.ofFn fun j : Fin n => decide (j = i))).getD w false = true}

def Tset (n : ℕ) (C : Circuit) (k a : ℕ) : Finset (Fin n) :=
  {i : Fin n | ((C.gates.take k).foldl stp (List.ofFn fun j : Fin n => decide (j = i))).getD a
    false = true}

theorem sset_mem (n : ℕ) (C : Circuit) (w : ℕ) (i : Fin n) :
    i ∈ Sset n C w ↔
      (C.gates.foldl stp (List.ofFn fun j : Fin n => decide (j = i))).getD w false = true := by
  rw [← wires_eq]; simp [Sset]

theorem tset_mem (n : ℕ) (C : Circuit) (k a : ℕ) (i : Fin n) :
    i ∈ Tset n C k a ↔
      ((C.gates.take k).foldl stp (List.ofFn fun j : Fin n => decide (j = i))).getD a false
        = true := by
  simp [Tset]

theorem card_le_one_of {n : ℕ} (s : Finset (Fin n)) (w : ℕ) (h : ∀ i ∈ s, i.val = w) :
    s.card ≤ 1 :=
  Finset.card_le_one.2 fun a ha b hb => Fin.ext ((h a ha).trans (h b hb).symm)

theorem unit_getD (n : ℕ) (i : Fin n) (w : ℕ)
    (h : (List.ofFn fun j : Fin n => decide (j = i)).getD w false = true) : i.val = w := by
  by_cases hw : w < n
  · have e : (List.ofFn fun j : Fin n => decide (j = i)).getD w false =
        decide ((⟨w, hw⟩ : Fin n) = i) := by
      rw [List.getD_eq_getElem _ _ (by simp [hw]), List.getElem_ofFn]
    rw [e] at h
    have := of_decide_eq_true h
    rw [← this]
  · rw [List.getD_eq_default _ _ (by simp; omega)] at h
    exact absurd h (by simp)

theorem wire_ok (n : ℕ) (C : Circuit) (w : ℕ) :
    (Sset n C w).card ≤ 1 ∨
      Sset n C w ∈ (List.range C.gates.length).map (fun j => Sset n C (n + j)) := by
  by_cases h1 : w < n
  · left
    apply card_le_one_of _ w
    intro i hi
    rw [sset_mem] at hi
    rw [fold_pre _ _ _ (by simp [h1])] at hi
    exact unit_getD n i w hi
  · by_cases h2 : w < n + C.gates.length
    · right
      simp only [List.mem_map, List.mem_range]
      exact ⟨w - n, by omega, by congr 1; omega⟩
    · left
      apply card_le_one_of _ 0
      intro i hi
      exfalso
      rw [sset_mem] at hi
      rw [fold_out _ _ _ (by simp; omega)] at hi
      exact Bool.false_ne_true hi

theorem operand_ok (n : ℕ) (C : Circuit) (k a : ℕ) (hk : k ≤ C.gates.length) :
    (Tset n C k a).card ≤ 1 ∨
      Tset n C k a ∈ List.take k ((List.range C.gates.length).map (fun j => Sset n C (n + j))) := by
  have hlen : ∀ i : Fin n,
      ((C.gates.take k).foldl stp (List.ofFn fun j : Fin n => decide (j = i))).length = n + k := by
    intro i; rw [fold_len, List.length_take, List.length_ofFn]; omega
  by_cases h1 : a < n
  · left
    apply card_le_one_of _ a
    intro i hi
    rw [tset_mem] at hi
    rw [fold_pre _ _ _ (by simp [h1])] at hi
    exact unit_getD n i a hi
  · by_cases h2 : a < n + k
    · right
      have e : Tset n C k a = Sset n C a := by
        ext i
        rw [tset_mem, sset_mem]
        have hs : C.gates.foldl stp (List.ofFn fun j : Fin n => decide (j = i)) =
            (C.gates.drop k).foldl stp
              ((C.gates.take k).foldl stp (List.ofFn fun j : Fin n => decide (j = i))) := by
          rw [← List.foldl_append, List.take_append_drop]
        rw [hs, fold_pre (C.gates.drop k)
          ((C.gates.take k).foldl stp (List.ofFn fun j : Fin n => decide (j = i))) a
          (by rw [hlen i]; exact h2)]
      rw [e, ← List.map_take, List.take_range]
      simp only [List.mem_map, List.mem_range]
      exact ⟨a - n, by omega, by congr 1; omega⟩
    · left
      apply card_le_one_of _ 0
      intro i hi
      exfalso
      rw [tset_mem] at hi
      rw [List.getD_eq_default _ _ (by rw [hlen i]; omega)] at hi
      exact Bool.false_ne_true hi

theorem gate_mem (n : ℕ) (C : Circuit) (k : ℕ) (hk : k < C.gates.length) (i : Fin n) :
    i ∈ Sset n C (n + k) ↔
      C.gates[k].op.eval (C.gates[k].inputs.map fun a =>
        ((C.gates.take k).foldl stp (List.ofFn fun j : Fin n => decide (j = i))).getD a false)
        = true := by
  rw [sset_mem]
  have := fold_at C.gates (List.ofFn fun j : Fin n => decide (j = i)) k hk
  rw [List.length_ofFn] at this
  rw [this]

end PEqualNP.Outside.L_meta_4923

open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_4923

theorem PEqualNP.Outside.L_meta_4923 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit),   (∀ x3 ∈ x2.gates, x3.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ x3.inputs.length ≤ (2 : ℕ)) →     ∃ (x4 : List (Finset (Fin x1))),       x4.length ≤ x2.size ∧         (∀ (x5 : ℕ),             have x6 : Finset (Fin x1) := {x6 : Fin x1 | (x2.wires (List.ofFn fun (x7 : Fin x1) => Decidable.decide (x7 = x6))).getD x5 Bool.false = Bool.true};             x6.card ≤ (1 : ℕ) ∨ x6 ∈ x4) ∧           ∀ (x5 : ℕ) (x6 : Finset (Fin x1)), x4[x5]? = Option.some x6 → ∃ (x8 : Finset (Fin x1)) (x9 : Finset (Fin x1)), x6 = x8 ∪ x9 ∧ (x8.card ≤ (1 : ℕ) ∨ x8 ∈ List.take x5 x4) ∧ (x9.card ≤ (1 : ℕ) ∨ x9 ∈ List.take x5 x4) := by
  intro n C hor
  refine ⟨(List.range C.gates.length).map (fun j => Sset n C (n + j)), ?_, ?_, ?_⟩
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size]
  · intro w
    exact wire_ok n C w
  · intro k s hks
    have hk : k < C.gates.length := by
      by_contra hc
      rw [List.getElem?_eq_none (by simp; omega)] at hks
      exact absurd hks (by simp)
    have hs : s = Sset n C (n + k) := by
      simp [List.getElem?_map, List.getElem?_range hk] at hks
      exact hks.symm
    obtain ⟨hop, hlen⟩ := hor _ (List.getElem_mem hk)
    have empty_ok : (∅ : Finset (Fin n)).card ≤ 1 ∨ (∅ : Finset (Fin n)) ∈
        List.take k ((List.range C.gates.length).map (fun j => Sset n C (n + j))) :=
      Or.inl (by simp)
    match hin : C.gates[k].inputs, hlen with
    | [], _ =>
      refine ⟨∅, ∅, ?_, empty_ok, empty_ok⟩
      ext i
      rw [hs, gate_mem n C k hk i, hop, hin]
      simp [GateOp.eval]
    | [a], _ =>
      refine ⟨Tset n C k a, ∅, ?_, operand_ok n C k a hk.le, empty_ok⟩
      ext i
      rw [hs, gate_mem n C k hk i, hop, hin, Finset.mem_union, tset_mem]
      simp [GateOp.eval]
    | [a, b], _ =>
      refine ⟨Tset n C k a, Tset n C k b, ?_, operand_ok n C k a hk.le,
        operand_ok n C k b hk.le⟩
      ext i
      rw [hs, gate_mem n C k hk i, hop, hin, Finset.mem_union, tset_mem, tset_mem]
      simp [GateOp.eval]
    | _ :: _ :: _ :: _, h3 => simp at h3
