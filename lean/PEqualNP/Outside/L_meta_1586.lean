import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.List.GetD
import Mathlib.Order.Interval.Finset.Nat
import PEqualNP.Defs

-- Wire evaluation follows L-meta-1460 and its L-meta-925 and L-meta-270 sources.


open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1586

private def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

private lemma run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

private lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih => rw [run_cons, ih]; simp; omega

private lemma run_getD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (run gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

private lemma run_split (gs : List Gate) (x : List Bool) (j : ℕ) :
    run gs x = run (gs.drop j) (run (gs.take j) x) := by
  simpa only [run, List.foldl_append] using
    congrArg (fun l : List Gate => run l x) (List.take_append_drop j gs).symm

private def value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

private lemma input_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (p : Fin n) :
    value C x p = x p := by
  change (run C.gates (List.ofFn x)).getD p false = x p
  have hp : (p : ℕ) < (List.ofFn x).length := by simp
  rw [run_getD _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp

private lemma missing_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.size ≤ w) : value C x w = false := by
  change (run C.gates (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by simpa [run_length, Circuit.size] using hw)

-- At a gate, reads of earlier wires agree with the completed run.
-- All other reads contribute false, even if the wire is produced later.
private lemma gate_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + C.size) :
    let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
    value C x w = g.op.eval (g.inputs.map fun r => if r < w then value C x r else false) := by
  let j := w - n
  have hj : j < C.gates.length := by unfold j Circuit.size at *; omega
  let g := C.gates[j]
  let earlier := run (C.gates.take j) (List.ofFn x)
  have plen : earlier.length = w := by
    simp [earlier, run_length, Nat.min_eq_left hj.le, j]; omega
  have split : run C.gates (List.ofFn x) = run (g :: C.gates.drop (j + 1)) earlier := by
    rw [run_split C.gates (List.ofFn x) j, List.drop_eq_getElem_cons hj]
  have read (r : ℕ) : earlier.getD r false = if r < w then value C x r else false := by
    by_cases hr : r < w
    · rw [ite_eq_left hr]
      change earlier.getD r false = (run C.gates (List.ofFn x)).getD r false
      rw [split]
      exact (run_getD _ earlier r (by simpa only [plen] using hr)).symm
    · rw [ite_eq_right hr]
      exact List.getD_eq_default _ _ (by omega)
  change (run C.gates (List.ofFn x)).getD w false =
    g.op.eval (g.inputs.map fun r => if r < w then value C x r else false)
  rw (occs := [1]) [split]
  rw (occs := [1]) [run_cons]
  rw [run_getD _ _ _ (by simp [plen]), List.getD_append_right _ _ _ _ (by omega)]
  simp only [plen, Nat.sub_self, List.getD_cons_zero, read]

open PEqualNP.MetaComplexity.NestedCover
private lemma gateAt_eq (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] :=
  List.getD_eq_getElem _ _ hj

private lemma gate_eval {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j : ℕ)
    (hj : j < C.gates.length) :
    value C x (n + j) = (gateAt C j).op.eval
      ((gateAt C j).inputs.map fun w => if w < n + j then value C x w else false) := by
  rw [gateAt_eq C j hj, gate_value C x (n + j) (by omega) (by unfold Circuit.size; omega)]
  simp

private lemma or_true {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j : ℕ)
    (hj : j < C.gates.length) (ho : (gateAt C j).op = GateOp.or) :
    value C x (n + j) = true ↔ ∃ w ∈ (gateAt C j).inputs, w < n + j ∧ value C x w = true := by
  rw [gate_eval C x j hj, ho]
  simp [GateOp.eval, List.any_eq_true]

private lemma and_true {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j : ℕ)
    (hj : j < C.gates.length) (ho : (gateAt C j).op = GateOp.and) :
    value C x (n + j) = true ↔ ∀ w ∈ (gateAt C j).inputs, w < n + j ∧ value C x w = true := by
  rw [gate_eval C x j hj, ho]
  simp [GateOp.eval, List.all_eq_true]

private def reached (n : ℕ) (C : Circuit) (u w : ℕ) : Prop :=
  ∀ S : Set ℕ, u ∈ S →
    (∀ i : Fin C.gates.length, n + (i : ℕ) ∈ S → (C.gates.get i).op = GateOp.or →
      ∀ a ∈ (C.gates.get i).inputs, a ∈ S) → w ∈ S

private lemma reach_start (n : ℕ) (C : Circuit) (u : ℕ) : reached n C u u :=
  fun _ h _ => h

private lemma reach_child (n : ℕ) (C : Circuit) (u : ℕ) (j : Fin C.gates.length) (w : ℕ)
    (h : reached n C u (n + j.val)) (ho : (gateAt C j.val).op = GateOp.or)
    (hw : w ∈ (gateAt C j.val).inputs) : reached n C u w := by
  intro S hS hClosed
  exact hClosed j (h S hS hClosed) (by simpa only [gateAt_eq C _ j.isLt, List.get_eq_getElem] using ho)
    w (by simpa only [gateAt_eq C _ j.isLt, List.get_eq_getElem] using hw)

private lemma low_reached {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u w : ℕ)
    (hBack : ∀ j : Fin C.gates.length, ∀ a ∈ (C.gates.get j).inputs, a < n + j.val)
    (hu : value C x u = false) (hw : reached n C u w) : value C x w = false := by
  apply hw {a | value C x a = false} hu
  intro j hj hop a ha
  change value C x (n + j.val) = false at hj
  change value C x a = false
  cases ht : value C x a
  · rfl
  · have hOr : (gateAt C j.val).op = GateOp.or := by simpa only [gateAt_eq C _ j.isLt, List.get_eq_getElem] using hop
    have hRead : a ∈ (gateAt C j.val).inputs := by simpa only [gateAt_eq C _ j.isLt, List.get_eq_getElem] using ha
    have yes := (or_true C x _ j.isLt hOr).2 ⟨a, hRead, hBack j a ha, ht⟩
    rw [hj] at yes
    contradiction

private lemma terminal {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : ℕ)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ w, reached n C u w → value C x w = true →
      (∃ p : Fin n, reached n C u (p : ℕ) ∧ x p = true) ∨
        ∃ i : Fin C.gates.length, reached n C u (n + i.val) ∧
          (C.gates.get i).op = GateOp.and ∧ value C x (n + i.val) = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hr ht
    by_cases h : w < n
    · let p : Fin n := ⟨w,h⟩
      exact Or.inl ⟨p, hr, (input_value C x p).symm ▸ ht⟩
    · have hw : w < n + C.gates.length := by
        by_contra! he
        rw [missing_value C x w he] at ht
        contradiction
      let j : Fin C.gates.length := ⟨w - n, by omega⟩
      have he : n + j.val = w := by simp [j]; omega
      have hr' : reached n C u (n + j.val) := he.symm ▸ hr
      have ht' : value C x (n + j.val) = true := he.symm ▸ ht
      rcases (hG (C.gates.get j) (List.getElem_mem j.isLt)).1 with ha | ho
      · exact Or.inr ⟨j, hr', ha, ht'⟩
      · have ho' : (gateAt C j.val).op = GateOp.or := by simpa only [gateAt_eq C _ j.isLt, List.get_eq_getElem] using ho
        obtain ⟨a, ha, hLt, hT⟩ := (or_true C x _ j.isLt ho').1 ht'
        exact ih a (he ▸ hLt) (reach_child n C u j a hr' ho' ha) hT

end PEqualNP.Outside.L_meta_1586

open PEqualNP.MetaComplexity.NestedCover PEqualNP.Outside.L_meta_1586 in
theorem PEqualNP.Outside.L_meta_1586 :

∀ (q m N : ℕ) (L : Fin N → Finset (Fin N)) (i0 : Fin N) (T0 : Finset (Fin N)),
    3 ≤ q → 3 ≤ m → m ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    T0 ⊆ L i0 → T0.card = m →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (u : ℕ),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧ ∀ a ∈ (gates.get i).inputs, a < N + (i : ℕ)) →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false →
    (∀ Y : ℕ, (∀ S : Set ℕ, u ∈ S → (∀ i : Fin gates.length, N + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → Y ∈ S) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, Y⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false) ∧
    (∀ p : Fin N, (∀ S : Set ℕ, u ∈ S → (∀ i : Fin gates.length, N + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → (p : ℕ) ∈ S) → p ∈ L i0) ∧
    (∀ r ∈ L i0 \ T0, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, u⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0 ∨ v = r))) = true →
      (∀ S : Set ℕ, u ∈ S → (∀ i : Fin gates.length, N + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → (r : ℕ) ∈ S) ∨ ∃ a : ℕ, (∀ S : Set ℕ, u ∈ S → (∀ i : Fin gates.length, N + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → a ∈ S) ∧ (∃ i : Fin gates.length, a = N + (i : ℕ) ∧ (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and) ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, a⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0 ∨ v = r))) = true) ∧
    (∀ (a : Fin gates.length) (c : ℕ), (gates.get a).op = PEqualNP.CircuitLowerBounds.GateOp.and → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (a : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false →
      c ∈ (gates.get a).inputs → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, c⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false →
      ∀ r ∈ L i0 \ T0, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (a : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0 ∨ v = r))) = true → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, c⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0 ∨ v = r))) = true) := by
  intro q m N L i0 T0 _ _ _ _ _ _ _ _ _ gates u hG hBack hLow
  let C : Circuit := ⟨gates, u⟩
  let base (v : Fin N) : Bool := decide (v ∉ L i0)
  have low (w : ℕ) (h : reached N C u w) : value C base w = false :=
    low_reached C base u w (fun j => (hBack j).2) hLow h
  have rootInput (p : Fin N) (h : reached N C u (p : ℕ)) : p ∈ L i0 := by
    have he := low (p : ℕ) h
    rw [input_value] at he
    simpa [base] using he
  refine ⟨low, rootInput, ?_, ?_⟩
  · intro r _ hTrue
    let x (v : Fin N) : Bool := decide (v ∉ L i0 ∨ v = r)
    rcases terminal C x u hG u (reach_start N C u) hTrue with ⟨p, hp, h⟩ | ⟨j, hj, ho, h⟩
    · have hp' : p ∈ L i0 := rootInput p hp
      have he : p = r := (of_decide_eq_true h).resolve_left (fun hn => hn hp')
      subst p
      exact Or.inl hp
    · exact Or.inr ⟨N + j.val, hj, ⟨j, rfl, ho⟩, h⟩
  · intro a c ha _ hc _ r _ hT
    let x (v : Fin N) : Bool := decide (v ∉ L i0 ∨ v = r)
    have ho : (gateAt C a.val).op = GateOp.and := by simpa only [gateAt_eq C _ a.isLt, List.get_eq_getElem] using ha
    have hc' : c ∈ (gateAt C a.val).inputs := by simpa only [gateAt_eq C _ a.isLt, List.get_eq_getElem] using hc
    exact ((and_true C x _ a.isLt ho).1 hT c hc').2
