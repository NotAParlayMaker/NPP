import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1044

open PEqualNP.CircuitLowerBounds

-- Seven paths of length three join hubs 0 and 1.
abbrev forward (a b : Fin 16) : Prop :=
  (a = 0 ∧ 2 ≤ b.val ∧ b.val < 9) ∨
  (2 ≤ a.val ∧ a.val < 9 ∧ b.val = a.val + 7) ∨
  (a = 1 ∧ 9 ≤ b.val)

abbrev graph : SimpleGraph (Fin 16) where
  Adj a b := forward a b ∨ forward b a
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by intro a; unfold forward; omega⟩

set_option maxHeartbeats 4000000 in
theorem noSquare : ∀ a b c d : Fin 16,
    graph.Adj a b → graph.Adj b c → graph.Adj c d → graph.Adj d a → a = c ∨ b = d := by
  letI : DecidableRel graph.Adj := fun a b =>
    inferInstanceAs (Decidable (forward a b ∨ forward b a))
  decide

theorem edgeCount : graph.edgeSet.ncard = 21 := by
  rw [Set.ncard_eq_toFinset_card']
  change graph.edgeFinset.card = 21
  have h := SimpleGraph.two_mul_card_edgeFinset (G := graph)
  have count : (Finset.univ.filter (fun p : Fin 16 × Fin 16 => graph.Adj p.1 p.2)).card = 42 := by
    decide
  have twice : 2 * graph.edgeFinset.card = 42 := h.trans count
  omega

-- These eight disjoint edges force every vertex cover to meet eight different vertices.
def leftEnd : Fin 8 → Fin 16 := ![0, 1, 3, 4, 5, 6, 7, 8]
def rightEnd : Fin 8 → Fin 16 := ![2, 9, 10, 11, 12, 13, 14, 15]

theorem coverBound (T : Finset (Fin 16))
    (covers : ∀ i j : Fin 16, graph.Adj i j → i ∈ T ∨ j ∈ T) : 8 ≤ T.card := by
  have joined : ∀ i, graph.Adj (leftEnd i) (rightEnd i) := by decide
  have distinct : ∀ i j : Fin 8, i ≠ j →
      leftEnd i ≠ leftEnd j ∧ leftEnd i ≠ rightEnd j ∧
      rightEnd i ≠ leftEnd j ∧ rightEnd i ≠ rightEnd j := by decide
  let pick (i : Fin 8) : T :=
    if h : leftEnd i ∈ T then ⟨leftEnd i, h⟩
    else ⟨rightEnd i, (covers _ _ (joined i)).resolve_left h⟩
  have inj : Function.Injective pick := by
    intro i j eq
    by_contra different
    have h := congrArg Subtype.val eq
    have d := distinct i j different
    simp only [pick] at h
    split at h <;> split at h <;> simp_all
  simpa using Fintype.card_le_of_injective pick inj

-- Write U and V for the two groups of seven internal vertices.
-- The first factor is (U AND (V OR hub0)) OR (hub1 AND V).
-- The second is the OR of the hubs and the seven middle-edge products.
def circuit : Circuit where
  gates := [
    ⟨.or, [2, 3]⟩, ⟨.or, [16, 4]⟩, ⟨.or, [17, 5]⟩, ⟨.or, [18, 6]⟩,
    ⟨.or, [19, 7]⟩, ⟨.or, [20, 8]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [22, 11]⟩,
    ⟨.or, [23, 12]⟩, ⟨.or, [24, 13]⟩, ⟨.or, [25, 14]⟩, ⟨.or, [26, 15]⟩,
    ⟨.or, [27, 0]⟩, ⟨.and, [21, 28]⟩, ⟨.and, [1, 27]⟩, ⟨.or, [29, 30]⟩,
    ⟨.or, [0, 1]⟩, ⟨.and, [2, 9]⟩, ⟨.or, [32, 33]⟩, ⟨.and, [3, 10]⟩,
    ⟨.or, [34, 35]⟩, ⟨.and, [4, 11]⟩, ⟨.or, [36, 37]⟩, ⟨.and, [5, 12]⟩,
    ⟨.or, [38, 39]⟩, ⟨.and, [6, 13]⟩, ⟨.or, [40, 41]⟩, ⟨.and, [7, 14]⟩,
    ⟨.or, [42, 43]⟩, ⟨.and, [8, 15]⟩, ⟨.or, [44, 45]⟩, ⟨.and, [31, 46]⟩]
  output := 47

def arcs : List (Fin 16 × Fin 16) :=
  [(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),
   (1,9),(1,10),(1,11),(1,12),(1,13),(1,14),(1,15),
   (2,9),(3,10),(4,11),(5,12),(6,13),(7,14),(8,15)]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem detects (x : Fin 16 → Bool) : circuit.eval (List.ofFn x) = true ↔
    ∃ u v, graph.Adj u v ∧ x u = true ∧ x v = true := by
  have direction : ∀ u v : Fin 16, forward u v ↔ (u,v) ∈ arcs := by decide
  have spec : arcs.any (fun p => x p.1 && x p.2) = true ↔
      ∃ u v, graph.Adj u v ∧ x u = true ∧ x v = true := by
    rw [List.any_eq_true]
    constructor
    · rintro ⟨⟨u,v⟩, h, bits⟩
      exact ⟨u, v, Or.inl ((direction u v).mpr h), Bool.and_eq_true_iff.mp bits⟩
    · rintro ⟨u, v, h | h, hu, hv⟩
      · exact ⟨(u,v), (direction u v).mp h, by simp [hu,hv]⟩
      · exact ⟨(v,u), (direction v u).mp h, by simp [hu,hv]⟩
  rw [← spec]
  have hx : List.ofFn x =
      [x 0,x 1,x 2,x 3,x 4,x 5,x 6,x 7,x 8,x 9,x 10,x 11,x 12,x 13,x 14,x 15] := rfl
  rw [hx]
  simp only [circuit, Circuit.eval, Circuit.wires, List.foldl_cons, List.foldl_nil,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append, GateOp.eval,
    List.any_cons, List.any_nil, List.all_cons, List.all_nil, id_eq, List.getD,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
    Bool.or_false, Bool.and_true, arcs]
  simp only [Bool.or_eq_true, Bool.and_eq_true]
  clear direction spec hx
  grind (splits := 40) only

def andGates : Finset ℕ := {13, 14, 17, 19, 21, 23, 25, 27, 29, 31}
def wideGates : Finset ℕ := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 16, 18, 20, 22, 24, 26, 28, 30}
def narrowGates : Finset ℕ := {15}

abbrev wideWire (w : ℕ) : Prop := ∃ u v : Fin 16, u ≠ v ∧
  (circuit.wires (List.ofFn (fun i : Fin 16 => decide (i = u)))).getD w false = true ∧
  (circuit.wires (List.ofFn (fun i : Fin 16 => decide (i = v)))).getD w false = true

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem widths : ∀ j : Fin 32, j.val ∈ wideGates ↔ wideWire (16 + j.val) := by decide

theorem monotone : PEqualNP.MetaComplexity.Monotone2 circuit := by
  simp [PEqualNP.MetaComplexity.Monotone2, circuit]

theorem gateKinds (j : ℕ) (g : Gate) (hj : circuit.gates[j]? = some g) :
    (g.op = GateOp.and → j ∈ andGates) ∧
    (g.op = GateOp.or → j ∈ wideGates ∨ j ∈ narrowGates) := by
  by_cases h : j < 32
  · interval_cases j <;> simp [circuit] at hj <;> subst g <;>
      simp [andGates, wideGates, narrowGates]
  · rw [List.getElem?_eq_none (by change 32 ≤ j; omega)] at hj
    contradiction


def gateAt (j : Fin 32) : Gate := circuit.gates[j.val]'(show j.val < 32 from j.isLt)

def designated (j : ℕ) : ℕ :=
  ((circuit.gates[j]?).map (fun g => g.inputs.headD 0)).getD 0

-- Only gate 13 has two wide inputs. Every other AND begins with a thin wire.
set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem andInputs : ∀ j : Fin 32, j.val ∈ andGates →
    (j.val = 13 → ∀ w ∈ (gateAt j).inputs, wideWire w) ∧
    (j.val ≠ 13 → designated j.val ∈ (gateAt j).inputs ∧ ¬ wideWire (designated j.val)) := by
  decide

theorem inputsOf (j : ℕ) (g : Gate) (hj : circuit.gates[j]? = some g) (op : g.op = .and) :
    (j = 13 → ∀ w ∈ g.inputs, wideWire w) ∧
    (j ≠ 13 → designated j ∈ g.inputs ∧ ¬ wideWire (designated j)) := by
  obtain ⟨bound, eq⟩ := List.getElem?_eq_some_iff.mp hj
  have h := andInputs ⟨j, bound⟩ ((gateKinds j g hj).1 op)
  subst g
  exact h

end PEqualNP.Outside.L_meta_1044

open PEqualNP.Outside.L_meta_1044 in
theorem PEqualNP.Outside.L_meta_1044 :
    ¬ (∀ (n k : ℕ) (G : SimpleGraph (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (A B D Fz :
    Finset ℕ) (des : ℕ → ℕ), (∀ a b c e : Fin n, G.Adj a b → G.Adj b c → G.Adj c e → G.Adj e a → a = c ∨
    b = e) → (∀ T : Finset (Fin n), (∀ i j : Fin n, G.Adj i j → i ∈ T ∨ j ∈ T) → k ≤ T.card) →
    PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔ ∃ u v : Fin
    n, G.Adj u v ∧ x u = true ∧ x v = true) → (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate),
    C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → j ∈ A) → (∀ (j : ℕ) (g :
    PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.op =
    PEqualNP.CircuitLowerBounds.GateOp.or → (∃ u v : Fin n, u ≠ v ∧ (C.wires (List.ofFn (fun i : Fin n
    => decide (i = u)))).getD (n + j) false = true ∧ (C.wires (List.ofFn (fun i : Fin n => decide (i =
    v)))).getD (n + j) false = true) → j ∈ B) → (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate),
    C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.or → ¬ (∃ u v : Fin n, u ≠ v ∧
    (C.wires (List.ofFn (fun i : Fin n => decide (i = u)))).getD (n + j) false = true ∧ (C.wires
    (List.ofFn (fun i : Fin n => decide (i = v)))).getD (n + j) false = true) → j ∈ D) → (∀ (j1 : ℕ) (g1
    : PEqualNP.CircuitLowerBounds.Gate), C.gates[j1]? = some g1 → g1.op =
    PEqualNP.CircuitLowerBounds.GateOp.and → ¬ (∀ w1 ∈ g1.inputs, (∃ a1 b1 : Fin n, a1 ≠ b1 ∧ (C.wires
    (List.ofFn (fun i1 : Fin n => decide (i1 = a1)))).getD w1 false = true ∧ (C.wires (List.ofFn (fun k1
    : Fin n => decide (k1 = b1)))).getD w1 false = true)) → des j1 ∈ g1.inputs ∧ ¬ (∃ a2 b2 : Fin n, a2
    ≠ b2 ∧ (C.wires (List.ofFn (fun i2 : Fin n => decide (i2 = a2)))).getD (des j1) false = true ∧
    (C.wires (List.ofFn (fun k2 : Fin n => decide (k2 = b2)))).getD (des j1) false = true)) → (∀ (j6 :
    ℕ) (g6 : PEqualNP.CircuitLowerBounds.Gate), C.gates[j6]? = some g6 → g6.op =
    PEqualNP.CircuitLowerBounds.GateOp.and → (∀ w7 ∈ g6.inputs, (∃ a7 b7 : Fin n, a7 ≠ b7 ∧ (C.wires
    (List.ofFn (fun i7 : Fin n => decide (i7 = a7)))).getD w7 false = true ∧ (C.wires (List.ofFn (fun k7
    : Fin n => decide (k7 = b7)))).getD w7 false = true)) → Relation.ReflTransGen (fun r3 t3 : ℕ => ∃
    (j3 : ℕ) (g3 : PEqualNP.CircuitLowerBounds.Gate), r3 = n + j3 ∧ C.gates[j3]? = some g3 ∧ ((g3.op =
    PEqualNP.CircuitLowerBounds.GateOp.or ∧ ¬ (∃ a4 b4 : Fin n, a4 ≠ b4 ∧ (C.wires (List.ofFn (fun i4 :
    Fin n => decide (i4 = a4)))).getD r3 false = true ∧ (C.wires (List.ofFn (fun k4 : Fin n => decide
    (k4 = b4)))).getD r3 false = true) ∧ t3 ∈ g3.inputs) ∨ (g3.op =
    PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬ (∀ w5 ∈ g3.inputs, (∃ a5 b5 : Fin n, a5 ≠ b5 ∧ (C.wires
    (List.ofFn (fun i5 : Fin n => decide (i5 = a5)))).getD w5 false = true ∧ (C.wires (List.ofFn (fun k5
    : Fin n => decide (k5 = b5)))).getD w5 false = true)) ∧ t3 = des j3))) C.output (n + j6) → (∀ c8 :
    Fin n, ∃ u8 v8 : Fin n, G.Adj u8 v8 ∧ (C.wires (List.ofFn (fun i8 : Fin n => decide (i8 = u8 ∨ i8 =
    v8)))).getD (n + j6) false = true ∧ c8 ≠ u8 ∧ c8 ≠ v8) → j6 ∈ Fz) → G.edgeSet.ncard + 2 * k ≤ A.card
    + B.card + 2 * D.card + Fz.card + 2) := by
  intro conjecture
  have h := conjecture 16 8 graph circuit andGates wideGates narrowGates {13} designated
    noSquare coverBound monotone detects (fun j g hj => (gateKinds j g hj).1) (by
      intro j g hj _ hw
      have bound : j < 32 := List.getElem?_eq_some_iff.mp hj |>.1
      exact (widths ⟨j,bound⟩).mpr hw) (by
      intro j g hj op hn
      have bound : j < 32 := List.getElem?_eq_some_iff.mp hj |>.1
      exact ((gateKinds j g hj).2 op).resolve_left (fun h => hn ((widths ⟨j,bound⟩).mp h))) (by
      intro j g hj op thin
      have inp := inputsOf j g hj op
      exact inp.2 (fun eq => thin (inp.1 eq))) (by
      intro j g hj op fat _ _
      by_contra miss
      have ne : j ≠ 13 := by simpa using miss
      obtain ⟨mem, thin⟩ := (inputsOf j g hj op).2 ne
      exact thin (fat _ mem))
  rw [edgeCount] at h
  have a : andGates.card = 10 := by decide
  have b : wideGates.card = 21 := by decide
  have d : narrowGates.card = 1 := by decide
  simp only [Finset.card_singleton] at h
  omega
