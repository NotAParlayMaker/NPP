import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_699_aux

open PEqualNP.CircuitLowerBounds

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stp x := rfl

lemma ext_foldl (gs : List Gate) (xs : List Bool) : ∃ t, gs.foldl stp xs = xs ++ t := by
  induction gs generalizing xs with
  | nil => exact ⟨[], by simp⟩
  | cons g gs ih =>
    obtain ⟨t, ht⟩ := ih (stp xs g)
    exact ⟨g.op.eval (g.inputs.map fun i => xs.getD i false) :: t, by rw [List.foldl_cons, ht]; simp [stp]⟩

lemma len_foldl (gs : List Gate) (xs : List Bool) :
    (gs.foldl stp xs).length = xs.length + gs.length := by
  induction gs generalizing xs with
  | nil => simp
  | cons g gs ih => simp [List.foldl_cons, ih, stp]; omega

lemma getD_pre (gs : List Gate) (xs : List Bool) (i : ℕ) (h : i < xs.length) :
    (gs.foldl stp xs).getD i false = xs.getD i false := by
  obtain ⟨t, ht⟩ := ext_foldl gs xs
  rw [ht, List.getD_append _ _ _ _ h]

lemma gate_val (C : Circuit) (x : List Bool) (j : ℕ) (g : Gate) (hg : C.gates[j]? = some g) :
    (C.wires x).getD (x.length + j) false =
      g.op.eval (g.inputs.map fun i => ((C.gates.take j).foldl stp x).getD i false) ∧
    ∀ i, ((C.gates.take j).foldl stp x).getD i false =
      if i < x.length + j then (C.wires x).getD i false else false := by
  obtain ⟨hj, hgj⟩ := List.getElem?_eq_some_iff.mp hg
  have hs : C.gates = C.gates.take j ++ g :: C.gates.drop (j+1) := by
    rw [← hgj, ← List.drop_eq_getElem_cons hj, List.take_append_drop]
  have hl : ((C.gates.take j).foldl stp x).length = x.length + j := by
    rw [len_foldl, List.length_take]; omega
  have e : C.wires x = (C.gates.drop (j+1)).foldl stp (stp ((C.gates.take j).foldl stp x) g) := by
    rw [wires_eq]
    conv_lhs => rw [hs]
    rw [List.foldl_append, List.foldl_cons]
  have hl2 : (stp ((C.gates.take j).foldl stp x) g).length = x.length + j + 1 := by
    simp [stp, hl]
  constructor
  · rw [e, getD_pre (C.gates.drop (j+1)) (stp ((C.gates.take j).foldl stp x) g) (x.length + j) (by omega)]
    simp only [stp]
    rw [List.getD_append_right _ _ _ _ (by omega)]
    simp [hl]
  · intro i
    split_ifs with hi
    · rw [e, getD_pre (C.gates.drop (j+1)) (stp ((C.gates.take j).foldl stp x) g) i (by omega)]
      simp only [stp]
      rw [List.getD_append _ _ _ _ (by omega)]
    · rw [List.getD_eq_default _ _ (by omega)]

end PEqualNP.Outside.L_meta_699_aux

open PEqualNP.Outside.L_meta_699_aux

theorem PEqualNP.Outside.L_meta_699 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ r : Fin n, (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (r.val) false = true)) = {r}) ∧ (∀ w : ℕ, n + C.size ≤ w → (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (w) false = true)) = ∅) ∧ (∀ (j a b : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.inputs = [a, b] → (g.op = PEqualNP.CircuitLowerBounds.GateOp.or → (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + j) false = true)) = (if a < n + j then (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (a) false = true)) else ∅) ∪ (if b < n + j then (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (b) false = true)) else ∅)) ∧ (g.op = PEqualNP.CircuitLowerBounds.GateOp.and → (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + j) false = true)) = (if a < n + j then (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (a) false = true)) else ∅) ∩ (if b < n + j then (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (b) false = true)) else ∅))) := by
  intro n C
  have hlen : ∀ p : Fin n, (List.ofFn (fun q : Fin n => decide (q = p))).length = n := by simp
  refine ⟨?_, ?_, ?_⟩
  · intro r
    ext p
    have h := getD_pre C.gates (List.ofFn (fun q : Fin n => decide (q = p))) r.val (by simp)
    rw [← wires_eq] at h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, h]
    simp [eq_comm]
  · intro w hw
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
    rw [List.getD_eq_default]
    · simp
    · rw [wires_eq, len_foldl, hlen]; exact hw
  · intro j a b g hg hi
    have key : ∀ p : Fin n,
        (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + j) false =
          g.op.eval [(if a < n + j then (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD a false else false),
            (if b < n + j then (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD b false else false)] := by
      intro p
      obtain ⟨h1, h2⟩ := gate_val C (List.ofFn (fun q : Fin n => decide (q = p))) j g hg
      rw [hlen] at h1 h2
      rw [h1, hi]
      simp only [List.map_cons, List.map_nil, h2]
    constructor
    · intro ho
      ext p
      rw [Finset.mem_union]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, key, ho]
      split_ifs <;> simp [PEqualNP.CircuitLowerBounds.GateOp.eval]
    · intro ho
      ext p
      rw [Finset.mem_inter]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, key, ho]
      split_ifs <;> simp [PEqualNP.CircuitLowerBounds.GateOp.eval]
