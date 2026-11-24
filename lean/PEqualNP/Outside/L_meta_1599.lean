import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

namespace PEqualNP.Outside.L_meta_1599

-- The wire evaluation lemmas through borvalue are from the accepted proof of L-meta-1553.
def brun (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma bruncons (g : Gate) (gs : List Gate) (x : List Bool) :
    brun (g :: gs) x = brun gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

lemma brunlength (gs : List Gate) (x : List Bool) :
    (brun gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [brun]
  | cons g gs ih => rw [bruncons, ih]; simp; omega

lemma brungetD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (brun gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [bruncons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

lemma brunsplit (gs : List Gate) (x : List Bool) (j : ℕ) :
    brun gs x = brun (gs.drop j) (brun (gs.take j) x) := by
  simpa only [brun, List.foldl_append] using
    congrArg (fun l : List Gate => brun l x) (List.take_append_drop j gs).symm

def bvalue {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma binputvalue {n : ℕ} (C : Circuit) (x : Fin n → Bool) (p : Fin n) :
    bvalue C x p = x p := by
  change (brun C.gates (List.ofFn x)).getD p false = x p
  have hp : (p : ℕ) < (List.ofFn x).length := by simp
  rw [brungetD _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp

lemma bmissingvalue {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.size ≤ w) : bvalue C x w = false := by
  change (brun C.gates (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by simpa [brunlength, Circuit.size] using hw)

lemma bgatevalue {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + C.size) :
    let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
    bvalue C x w = g.op.eval (g.inputs.map fun r => if r < w then bvalue C x r else false) := by
  let j := w - n
  have hj : j < C.gates.length := by unfold j Circuit.size at *; omega
  let g := C.gates[j]
  let earlier := brun (C.gates.take j) (List.ofFn x)
  have plen : earlier.length = w := by
    simp [earlier, brunlength, Nat.min_eq_left hj.le, j]; omega
  have split : brun C.gates (List.ofFn x) = brun (g :: C.gates.drop (j + 1)) earlier := by
    rw [brunsplit C.gates (List.ofFn x) j, List.drop_eq_getElem_cons hj]
  have read (r : ℕ) : earlier.getD r false = if r < w then bvalue C x r else false := by
    by_cases hr : r < w
    · rw [ite_eq_left hr]
      change earlier.getD r false = (brun C.gates (List.ofFn x)).getD r false
      rw [split]
      exact (brungetD _ earlier r (by simpa only [plen] using hr)).symm
    · rw [ite_eq_right hr]
      exact List.getD_eq_default _ _ (by omega)
  change (brun C.gates (List.ofFn x)).getD w false =
    g.op.eval (g.inputs.map fun r => if r < w then bvalue C x r else false)
  rw (occs := [1]) [split]
  rw (occs := [1]) [bruncons]
  rw [brungetD _ _ _ (by simp [plen]), List.getD_append_right _ _ _ _ (by omega)]
  simp only [plen, Nat.sub_self, List.getD_cons_zero, read]

lemma borvalue {n : ℕ} (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : C.gates[k].op = GateOp.or) (x : Fin n → Bool) :
    bvalue C x (n + k) = true ↔ ∃ r ∈ C.gates[k].inputs, r < n + k ∧ bvalue C x r = true := by
  have hw : n + k < n + C.size := by unfold Circuit.size; omega
  have hx := bgatevalue C x (n + k) (by omega) hw
  simp only [Nat.add_sub_cancel_left] at hx
  rw [hx, hop]
  simp [GateOp.eval]

lemma trace {n : ℕ} (C : Circuit) (ops : AndOrOnly C) (u v : Fin n)
    (noAnd : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      gateVal n C j (pairInput u v) ≠ true) (w : ℕ)
    (onPair : bvalue C (pairInput u v) w = true) :
    bvalue C (pairInput u u) w = true ∨ bvalue C (pairInput v v) w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hi : w < n
    · let i : Fin n := ⟨w, hi⟩
      change bvalue C (pairInput u v) i = true at onPair
      change bvalue C (pairInput u u) i = true ∨ bvalue C (pairInput v v) i = true
      simpa [binputvalue, pairInput] using onPair
    by_cases hw : w < n + C.size
    · let j := w - n
      have hj : j < C.gates.length := by unfold j; unfold Circuit.size at hw; omega
      have he : w = n + j := by unfold j; omega
      rcases ops _ (List.getElem_mem (l := C.gates) hj) with hand | hor
      · exact False.elim (noAnd j hj (by unfold gateAt; rw [List.getD_eq_getElem _ _ hj]; exact hand)
          (by change bvalue C (pairInput u v) (n + j) = true; rwa [← he]))
      · obtain ⟨r, hr, hlt, hrp⟩ := (borvalue C j hj hor _).mp (he ▸ onPair)
        rcases ih r (by omega) hrp with hu | hv
        · exact Or.inl (he ▸ (borvalue C j hj hor _).mpr ⟨r, hr, hlt, hu⟩)
        · exact Or.inr (he ▸ (borvalue C j hj hor _).mpr ⟨r, hr, hlt, hv⟩)
    · rw [bmissingvalue C _ w (by omega)] at onPair
      contradiction

lemma singleOff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u : Fin n) :
    graphFun G ∅ (pairInput u u) = false := by
  simp [graphFun, pairInput]

lemma existsOn {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (ops : AndOrOnly C) (correct : circuitFun n C = graphFun G ∅)
    (u v : Fin n) (adj : G.Adj u v) :
    ∃ j, j < C.gates.length ∧ (gateAt C j).op = GateOp.and ∧ gateVal n C j (pairInput u v) = true := by
  have pos : graphFun G ∅ (pairInput u v) = true := by
    simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or,
      decide_eq_true_eq]
    exact ⟨u, v, adj, by simp [pairInput], by simp [pairInput]⟩
  have pair : bvalue C (pairInput u v) C.output = true :=
    (congrFun correct (pairInput u v)).trans pos
  have single (a : Fin n) : bvalue C (pairInput a a) C.output = false :=
    (congrFun correct (pairInput a a)).trans (singleOff G a)
  by_contra! hn
  have noAnd (j : ℕ) (hj : j < C.gates.length) (ha : (gateAt C j).op = GateOp.and) :
      gateVal n C j (pairInput u v) ≠ true := by simpa using hn j hj ha
  rcases trace C ops u v noAnd C.output pair with h | h
  · rw [single u] at h; contradiction
  · rw [single v] at h; contradiction

end PEqualNP.Outside.L_meta_1599

theorem PEqualNP.Outside.L_meta_1599 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.EdgeOwnership.AndOrOnly C → PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ → PEqualNP.EdgeOwnership.EveryEdgeOwned n G C := by
  classical
  intro n G _ C ops correct u v adj
  have e := PEqualNP.Outside.L_meta_1599.existsOn G C ops correct u v adj
  obtain ⟨hj, ha, hv⟩ := Nat.find_spec e
  refine ⟨Nat.find e, hj, hj, ha, hv, ?_⟩
  intro i hi _ hop
  cases he : gateVal n C i (pairInput u v) with
  | false => rfl
  | true => exact False.elim (Nat.find_min e hi ⟨hi.trans hj, hop, he⟩)
