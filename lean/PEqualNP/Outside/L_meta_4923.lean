import Mathlib.Data.List.Induction
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_4923

private def basis (n : ℕ) : List (Finset (Fin n)) :=
  List.ofFn fun i => {i}

private def inputSet {n : ℕ} (ws : List (Finset (Fin n))) (g : Gate) (j : ℕ) : Finset (Fin n) :=
  (g.inputs.map fun i => ws.getD i ∅).getD j ∅

private def setStep {n : ℕ} (ws : List (Finset (Fin n))) (g : Gate) :
    List (Finset (Fin n)) :=
  ws ++ [inputSet ws g 0 ∪ inputSet ws g 1]

private def boolStep (ws : List Bool) (g : Gate) : List Bool :=
  ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]

private def bit {n : ℕ} (x : Fin n) (s : Finset (Fin n)) : Bool := decide (x ∈ s)

private theorem bit_read {n : ℕ} (x : Fin n) (ws : List (Finset (Fin n))) (i : ℕ) :
    (ws.map (bit x)).getD i false = bit x (ws.getD i ∅) := by
  induction ws generalizing i with
  | nil => simp [bit]
  | cons s ws ih =>
    cases i with
    | zero => rfl
    | succ i => simpa only [List.map_cons, List.getD_cons_succ] using ih i

private theorem bit_join {n : ℕ} (x : Fin n) (a b : Finset (Fin n)) :
    bit x (a ∪ b) = (bit x a || bit x b) := by
  simp [bit, Finset.mem_union]

private theorem step_match {n : ℕ} (x : Fin n) (ws : List (Finset (Fin n))) (g : Gate)
    (hop : g.op = .or) (hlen : g.inputs.length ≤ 2) :
    (setStep ws g).map (bit x) = boolStep (ws.map (bit x)) g := by
  obtain ⟨op, ins⟩ := g
  change op = .or at hop
  change ins.length ≤ 2 at hlen
  subst op
  have hread (i : ℕ) :
      (Option.map (bit x) ws[i]?).getD false = bit x (ws[i]?.getD ∅) := by
    simpa only [List.getD_eq_getElem?_getD, List.getElem?_map] using bit_read x ws i
  have hEmpty : bit x (∅ : Finset (Fin n)) = false := by simp [bit]
  simp only [setStep, boolStep, inputSet, List.map_append, List.map_cons, List.map_nil, bit_join]
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · rfl
  · simp [GateOp.eval, hread, hEmpty]
  · simp [GateOp.eval, hread]
  · simp at hlen

private theorem fold_match {n : ℕ} (x : Fin n) (gs : List Gate) (ws : List (Finset (Fin n)))
    (hm : ∀ g ∈ gs, g.op = .or ∧ g.inputs.length ≤ 2) :
    (gs.foldl setStep ws).map (bit x) = gs.foldl boolStep (ws.map (bit x)) := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g gs ih =>
    have hg := hm g (by simp)
    simp only [List.foldl_cons]
    rw [ih (setStep ws g) (fun k hk => hm k (List.mem_cons_of_mem _ hk)),
      step_match x ws g hg.1 hg.2]

private theorem base_bit {n : ℕ} (x : Fin n) :
    (basis n).map (bit x) = List.ofFn (fun i : Fin n => decide (i = x)) := by
  simp only [basis, List.map_ofFn]
  congr 1
  funext i
  simp [bit, eq_comm]

private theorem read_allowed {n : ℕ} (ss : List (Finset (Fin n))) (i : ℕ) :
    ((basis n ++ ss).getD i ∅).card ≤ 1 ∨ (basis n ++ ss).getD i ∅ ∈ ss := by
  rw [List.getD_eq_getElem?_getD]
  cases h : (basis n ++ ss)[i]? with
  | none => simp
  | some s =>
    have hmem := List.mem_append.mp (List.mem_of_getElem? h)
    rcases hmem with hbase | hss
    · obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hbase
      simp
    · exact Or.inr hss

private theorem operand_allowed {n : ℕ} (ss : List (Finset (Fin n))) (g : Gate) (j : ℕ) :
    (inputSet (basis n ++ ss) g j).card ≤ 1 ∨ inputSet (basis n ++ ss) g j ∈ ss := by
  unfold inputSet
  rw [List.getD_eq_getElem?_getD]
  cases h : (g.inputs.map fun i => (basis n ++ ss).getD i ∅)[j]? with
  | none => simp
  | some s =>
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp (List.mem_of_getElem? h)
    exact read_allowed ss i

private def formed {n : ℕ} (ss : List (Finset (Fin n))) : Prop :=
  ∀ j s, ss[j]? = some s → ∃ a b : Finset (Fin n),
    s = a ∪ b ∧ (a.card ≤ 1 ∨ a ∈ ss.take j) ∧ (b.card ≤ 1 ∨ b ∈ ss.take j)

private theorem extend_formed {n : ℕ} (ss : List (Finset (Fin n))) (g : Gate)
    (hss : formed ss) :
    formed (ss ++ [inputSet (basis n ++ ss) g 0 ∪ inputSet (basis n ++ ss) g 1]) := by
  let a := inputSet (basis n ++ ss) g 0
  let b := inputSet (basis n ++ ss) g 1
  change formed (ss ++ [a ∪ b])
  intro j s hjs
  by_cases hj : j < ss.length
  · have old : ss[j]? = some s := by
      simpa only [List.getElem?_append_left hj] using hjs
    simpa only [List.take_append_of_le_length hj.le] using hss j s old
  · have hi : j < (ss ++ [a ∪ b]).length := by
      by_contra! h
      rw [List.getElem?_eq_none h] at hjs
      cases hjs
    have same : j = ss.length := by
      simp at hi
      omega
    subst j
    have hs : s = a ∪ b := by
      rw [List.getElem?_append_right (Nat.le_refl _)] at hjs
      simpa using hjs.symm
    rw [List.take_append_length]
    exact ⟨a, b, hs, operand_allowed ss g 0, operand_allowed ss g 1⟩

private theorem build_trace {n : ℕ} (gs : List Gate) :
    ∃ ss : List (Finset (Fin n)), ss.length = gs.length ∧
      gs.foldl setStep (basis n) = basis n ++ ss ∧ formed ss := by
  induction gs using List.reverseRecOn with
  | nil => exact ⟨[], rfl, by simp, by simp [formed]⟩
  | append_singleton gs g ih =>
    obtain ⟨ss, hlen, hfold, hss⟩ := ih
    refine ⟨ss ++ [inputSet (basis n ++ ss) g 0 ∪ inputSet (basis n ++ ss) g 1], ?_, ?_, extend_formed ss g hss⟩
    · simp [hlen]
    · rw [List.foldl_append, hfold]
      simp [setStep, List.append_assoc]

theorem report (n : ℕ) (C : Circuit)
    (hm : ∀ g ∈ C.gates, g.op = .or ∧ g.inputs.length ≤ 2) :
    ∃ ss : List (Finset (Fin n)), ss.length ≤ C.size ∧
      (∀ i, let S := (Finset.univ : Finset (Fin n)).filter (fun x =>
        (C.wires (List.ofFn fun y : Fin n => decide (y = x))).getD i false = true);
        S.card ≤ 1 ∨ S ∈ ss) ∧ formed ss := by
  obtain ⟨ss, hsize, hfold, hformed⟩ := build_trace (n := n) C.gates
  refine ⟨ss, hsize.le, ?_, hformed⟩
  intro i S
  have hTrace (x : Fin n) : C.wires (List.ofFn fun y : Fin n => decide (y = x)) =
      (basis n ++ ss).map (bit x) := by
    change C.gates.foldl boolStep _ = _
    rw [← base_bit x, ← fold_match x C.gates (basis n) hm, hfold]
  have hS : S = (basis n ++ ss).getD i ∅ := by
    ext x
    change x ∈ (Finset.univ : Finset (Fin n)).filter _ ↔ _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hTrace, bit_read,
      bit, decide_eq_true_eq]
  rw [hS]
  exact read_allowed ss i

end PEqualNP.Outside.L_meta_4923

theorem PEqualNP.Outside.L_meta_4923 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit),   (∀ x3 ∈ x2.gates, x3.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ x3.inputs.length ≤ (2 : ℕ)) →     ∃ (x4 : List (Finset (Fin x1))),       x4.length ≤ x2.size ∧         (∀ (x5 : ℕ),             have x6 : Finset (Fin x1) := {x6 : Fin x1 | (x2.wires (List.ofFn fun (x7 : Fin x1) => Decidable.decide (x7 = x6))).getD x5 Bool.false = Bool.true};             x6.card ≤ (1 : ℕ) ∨ x6 ∈ x4) ∧           ∀ (x5 : ℕ) (x6 : Finset (Fin x1)), x4[x5]? = Option.some x6 → ∃ (x8 : Finset (Fin x1)) (x9 : Finset (Fin x1)), x6 = x8 ∪ x9 ∧ (x8.card ≤ (1 : ℕ) ∨ x8 ∈ List.take x5 x4) ∧ (x9.card ≤ (1 : ℕ) ∨ x9 ∈ List.take x5 x4) :=
  PEqualNP.Outside.L_meta_4923.report
