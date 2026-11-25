import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17108

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def g9WiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem g9_wires_eq (C : Circuit) (x : List Bool) : C.wires x = g9WiresFrom C.gates x := rfl

theorem g9_wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, g9WiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [g9WiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : g9WiresFrom (g :: gs) w
        = g9WiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem g9_getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (g9WiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := g9_wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

theorem g9_wire_input (C : Circuit) (x : List Bool) (i : ℕ) (h : i < x.length) :
    (C.wires x).getD i false = x.getD i false := by
  rw [g9_wires_eq]
  exact g9_getD_wiresFrom _ _ _ h

theorem g9_wire_first (C : Circuit) (g : Gate) (rest : List Gate) (hC : C.gates = g :: rest)
    (x : List Bool) :
    (C.wires x).getD x.length false = g.op.eval (g.inputs.map fun i => x.getD i false) := by
  rw [g9_wires_eq, hC]
  have h1 : g9WiresFrom (g :: rest) x
      = g9WiresFrom rest (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) := rfl
  rw [h1, g9_getD_wiresFrom rest _ _ (by simp)]
  simp

theorem g9_wire_nine (C : Circuit) (g : Gate) (rest : List Gate) (hC : C.gates = g :: rest)
    (y : Fin 9 → Bool) :
    (C.wires (List.ofFn y)).getD 9 false
      = g.op.eval (g.inputs.map fun i => (List.ofFn y).getD i false) := by
  have h := g9_wire_first C g rest hC (List.ofFn y)
  rw [List.length_ofFn] at h
  exact h

theorem g9_rd_lt (y : Fin 9 → Bool) (a : ℕ) (ha : a < 9) :
    (List.ofFn y).getD a false = y ⟨a, ha⟩ := by
  rw [List.getD_eq_getElem _ _ (by simp; exact ha), List.getElem_ofFn]

theorem g9_rd_ge (y : Fin 9 → Bool) (a : ℕ) (ha : 9 ≤ a) :
    (List.ofFn y).getD a false = false := by
  rw [List.getD_eq_default _ _ (by simp; omega)]

def g9Disj (W : (Fin 9 → Bool) → Bool) (i : Fin 9) : Prop :=
  (∀ y : Fin 9 → Bool, W y = !(y i)) ∨
    (∃ j : Fin 9, i < j ∧ ∀ y : Fin 9 → Bool, W y = (y i && y j)) ∨
    (∃ j : Fin 9, i < j ∧ ∀ y : Fin 9 → Bool, W y = (y i || y j))

def g9Hyp (f : (Fin 9 → Bool) → Bool) (i : Fin 9) : Prop :=
  ∀ C : Circuit, FanInTwo C → g9Disj (fun y => (C.wires (List.ofFn y)).getD 9 false) i →
    circuitFun 9 C = f → 16 ≤ C.size

theorem g9_gate_cases (rd : (Fin 9 → Bool) → ℕ → Bool)
    (hlt : ∀ y a, (ha : a < 9) → rd y a = y ⟨a, ha⟩)
    (hge : ∀ y a, 9 ≤ a → rd y a = false)
    (op : GateOp) (ins : List ℕ) (W : (Fin 9 → Bool) → Bool)
    (hW : ∀ y, W y = op.eval (ins.map (rd y)))
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (hlen : ins.length ≤ 2)
    (hnc : ∃ x y, W x ≠ W y)
    (hcp : ∀ a, a < 9 → ∃ x, rd x a ≠ W x) :
    ∃ i : Fin 9, g9Disj W i := by
  have noConst : ∀ c : Bool, ¬ ∀ y, W y = c := by
    intro c hc
    obtain ⟨x, y, hxy⟩ := hnc
    exact hxy ((hc x).trans (hc y).symm)
  have noCopy : ∀ a, a < 9 → ¬ ∀ y, W y = rd y a := by
    intro a ha hc
    obtain ⟨x, hx⟩ := hcp a ha
    exact hx (hc x).symm
  have notCase : ∀ a, (∀ y, W y = !(rd y a)) → ∃ i : Fin 9, g9Disj W i := by
    intro a hWa
    by_cases ha : a < 9
    · exact ⟨⟨a, ha⟩, Or.inl fun y => by rw [hWa y, hlt y a ha]⟩
    · exact (noConst true fun y => by simp [hWa y, hge y a (by omega)]).elim
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · rcases hop with rfl | rfl | rfl
    · exact (noConst true fun y => by simp [hW y, GateOp.eval]).elim
    · exact (noConst false fun y => by simp [hW y, GateOp.eval]).elim
    · exact (noConst true fun y => by simp [hW y, GateOp.eval]).elim
  · rcases hop with rfl | rfl | rfl
    · have h1 : ∀ y, W y = rd y a := fun y => by simp [hW y, GateOp.eval]
      by_cases ha : a < 9
      · exact (noCopy a ha h1).elim
      · exact (noConst false fun y => by rw [h1 y, hge y a (by omega)]).elim
    · have h1 : ∀ y, W y = rd y a := fun y => by simp [hW y, GateOp.eval]
      by_cases ha : a < 9
      · exact (noCopy a ha h1).elim
      · exact (noConst false fun y => by rw [h1 y, hge y a (by omega)]).elim
    · exact notCase a fun y => by simp [hW y, GateOp.eval]
  · rcases hop with rfl | rfl | rfl
    · have h2 : ∀ y, W y = (rd y a && rd y b) := fun y => by simp [hW y, GateOp.eval]
      by_cases ha : a < 9
      · by_cases hb : b < 9
        · rcases lt_trichotomy a b with h | h | h
          · exact ⟨⟨a, ha⟩, Or.inr (Or.inl ⟨⟨b, hb⟩, h, fun y => by
              rw [h2 y, hlt y a ha, hlt y b hb]⟩)⟩
          · rw [← h] at h2
            exact (noCopy a ha fun y => by rw [h2 y, Bool.and_self]).elim
          · exact ⟨⟨b, hb⟩, Or.inr (Or.inl ⟨⟨a, ha⟩, h, fun y => by
              rw [h2 y, hlt y a ha, hlt y b hb, Bool.and_comm]⟩)⟩
        · exact (noConst false fun y => by simp [h2 y, hge y b (by omega)]).elim
      · exact (noConst false fun y => by simp [h2 y, hge y a (by omega)]).elim
    · have h2 : ∀ y, W y = (rd y a || rd y b) := fun y => by simp [hW y, GateOp.eval]
      by_cases ha : a < 9
      · by_cases hb : b < 9
        · rcases lt_trichotomy a b with h | h | h
          · exact ⟨⟨a, ha⟩, Or.inr (Or.inr ⟨⟨b, hb⟩, h, fun y => by
              rw [h2 y, hlt y a ha, hlt y b hb]⟩)⟩
          · rw [← h] at h2
            exact (noCopy a ha fun y => by rw [h2 y, Bool.or_self]).elim
          · exact ⟨⟨b, hb⟩, Or.inr (Or.inr ⟨⟨a, ha⟩, h, fun y => by
              rw [h2 y, hlt y a ha, hlt y b hb, Bool.or_comm]⟩)⟩
        · exact (noCopy a ha fun y => by simp [h2 y, hge y b (by omega)]).elim
      · by_cases hb : b < 9
        · exact (noCopy b hb fun y => by simp [h2 y, hge y a (by omega)]).elim
        · exact (noConst false fun y => by
            simp [h2 y, hge y a (by omega), hge y b (by omega)]).elim
    · exact notCase a fun y => by simp [hW y, GateOp.eval]
  · simp at hlen

theorem g9_core (f : (Fin 9 → Bool) → Bool) (z : Fin 9 → Bool) (hz1 : f z = true)
    (hz : ∀ o : Fin 9, f (fun i => decide (i = o)) = false)
    (H0 : ∀ C : Circuit, IsMinimalCircuit 9 C →
      (∃ x y : Fin 9 → Bool, circuitFun 9 C x ≠ circuitFun 9 C y) →
      (∀ j : ℕ, j < C.gates.length → ∃ x y : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j) false ≠ (C.wires (List.ofFn y)).getD (9 + j) false) ∧
      (∀ i j : ℕ, i < 9 + j → j < C.gates.length → ∃ x : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD i false ≠ (C.wires (List.ofFn x)).getD (9 + j) false))
    (H : ∀ i : Fin 9, g9Hyp f i) :
    ∀ t : ℕ, HasCircuitSize 9 f t → 16 ≤ t := by
  classical
  intro t ⟨C, hfan, hsize, heval⟩
  have hCf : circuitFun 9 C = f := funext heval
  have hex : ∃ s, ∃ D : Circuit, FanInTwo D ∧ D.size = s ∧ circuitFun 9 D = f :=
    ⟨C.size, C, hfan, rfl, hCf⟩
  obtain ⟨D, hDfan, hDsize, hDfun⟩ := Nat.find_spec hex
  have hle : Nat.find hex ≤ C.size := Nat.find_min' hex ⟨C, hfan, rfl, hCf⟩
  have hmin : IsMinimalCircuit 9 D := by
    refine ⟨hDfan, fun E hE hEf => ?_⟩
    rw [hDsize]
    exact Nat.find_min' hex ⟨E, hE, rfl, hEf.trans hDfun⟩
  have hnc : ∃ x y : Fin 9 → Bool, circuitFun 9 D x ≠ circuitFun 9 D y := by
    refine ⟨z, fun i => decide (i = 0), ?_⟩
    rw [hDfun, hz1, hz 0]
    decide
  obtain ⟨hA, hB⟩ := H0 D hmin hnc
  obtain ⟨g, rest, hgs⟩ : ∃ g rest, D.gates = g :: rest := by
    rcases hD : D.gates with _ | ⟨g, rest⟩
    · exfalso
      have hf : ∀ x, f x = (List.ofFn x).getD D.output false := by
        intro x
        rw [← hDfun]
        show (D.wires (List.ofFn x)).getD D.output false = _
        rw [g9_wires_eq, hD]
        rfl
      by_cases ho : D.output < 9
      · have h1 := hf (fun i => decide (i = ⟨D.output, ho⟩))
        rw [hz, g9_rd_lt _ _ ho] at h1
        simp at h1
      · have h1 := hf z
        rw [hz1, g9_rd_ge _ _ (by omega)] at h1
        exact Bool.noConfusion h1
    · exact ⟨g, rest, rfl⟩
  have hmem : g ∈ D.gates := by rw [hgs]; exact List.mem_cons_self
  have hg := hDfan g hmem
  have hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not := by
    have h1 := hg.1
    simpa using h1
  have hlen0 : 0 < D.gates.length := by rw [hgs]; simp
  have hA0 : ∃ x y : Fin 9 → Bool,
      (D.wires (List.ofFn x)).getD 9 false ≠ (D.wires (List.ofFn y)).getD 9 false := by
    simpa only [Nat.add_zero] using hA 0 hlen0
  have hcp : ∀ a, a < 9 → ∃ x : Fin 9 → Bool,
      (List.ofFn x).getD a false ≠ (D.wires (List.ofFn x)).getD 9 false := by
    intro a ha
    obtain ⟨x, hx⟩ := hB a 0 (by omega) hlen0
    refine ⟨x, ?_⟩
    rw [g9_wire_input D (List.ofFn x) a (by simp; omega)] at hx
    simpa only [Nat.add_zero] using hx
  obtain ⟨i, hi⟩ := g9_gate_cases (fun y a => (List.ofFn y).getD a false)
    (fun y a ha => g9_rd_lt y a ha) (fun y a ha => g9_rd_ge y a ha) g.op g.inputs
    (fun y => (D.wires (List.ofFn y)).getD 9 false) (fun y => g9_wire_nine D g rest hgs y)
    hop hg.2 hA0 hcp
  have h16 := H i D hDfan hi hDfun
  omega

end PEqualNP.Outside.L_meta_17108

theorem PEqualNP.Outside.L_meta_17108 : ((∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalCircuit n C → (∃ x y : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n C x ≠ PEqualNP.MetaComplexity.circuitFun n C y) → (∀ j : ℕ, j < C.gates.length → ∃ x y : Fin n → Bool, (C.wires (List.ofFn x)).getD (n + j) false ≠ (C.wires (List.ofFn y)).getD (n + j) false) ∧ (∀ i j : ℕ, i < n + j → j < C.gates.length → ∃ x : Fin n → Bool, (C.wires (List.ofFn x)).getD i false ≠ (C.wires (List.ofFn x)).getD (n + j) false) ∧ (C.gates ≠ [] → C.output + 1 = n + C.gates.length) ∧ (∀ j : ℕ, j + 1 < C.gates.length → ∃ p ∈ C.gates.zipIdx, n + j < n + p.2 ∧ (PEqualNP.CircuitLowerBounds.GateOp.casesOn (motive := fun _ => List ℕ) p.1.op p.1.inputs p.1.inputs (p.1.inputs.take 1) (fun _ => p.1.inputs) p.1.inputs).contains (n + j) = true)) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → ((∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 0)) ∨ (∃ j : Fin 9, (0 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 && y j)) ∨ (∃ j : Fin 9, (0 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y j))) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 2 && x 7) || (x 4 && x 7) || (x 0 && x 8) || (x 3 && x 8) || (x 5 && x 8) || (x 6 && x 8)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → ((∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 1)) ∨ (∃ j : Fin 9, (1 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 1 && y j)) ∨ (∃ j : Fin 9, (1 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 1 || y j))) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 2 && x 7) || (x 4 && x 7) || (x 0 && x 8) || (x 3 && x 8) || (x 5 && x 8) || (x 6 && x 8)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → ((∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 2)) ∨ (∃ j : Fin 9, (2 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 2 && y j)) ∨ (∃ j : Fin 9, (2 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 2 || y j))) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 2 && x 7) || (x 4 && x 7) || (x 0 && x 8) || (x 3 && x 8) || (x 5 && x 8) || (x 6 && x 8)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → ((∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 3)) ∨ (∃ j : Fin 9, (3 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 3 && y j)) ∨ (∃ j : Fin 9, (3 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 3 || y j))) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 2 && x 7) || (x 4 && x 7) || (x 0 && x 8) || (x 3 && x 8) || (x 5 && x 8) || (x 6 && x 8)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → ((∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 4)) ∨ (∃ j : Fin 9, (4 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 4 && y j)) ∨ (∃ j : Fin 9, (4 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 4 || y j))) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 2 && x 7) || (x 4 && x 7) || (x 0 && x 8) || (x 3 && x 8) || (x 5 && x 8) || (x 6 && x 8)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → ((∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 5)) ∨ (∃ j : Fin 9, (5 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 5 && y j)) ∨ (∃ j : Fin 9, (5 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 5 || y j))) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 2 && x 7) || (x 4 && x 7) || (x 0 && x 8) || (x 3 && x 8) || (x 5 && x 8) || (x 6 && x 8)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → ((∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 6)) ∨ (∃ j : Fin 9, (6 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 6 && y j)) ∨ (∃ j : Fin 9, (6 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 6 || y j))) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 2 && x 7) || (x 4 && x 7) || (x 0 && x 8) || (x 3 && x 8) || (x 5 && x 8) || (x 6 && x 8)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → ((∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 7)) ∨ (∃ j : Fin 9, (7 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 7 && y j)) ∨ (∃ j : Fin 9, (7 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 7 || y j))) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 2 && x 7) || (x 4 && x 7) || (x 0 && x 8) || (x 3 && x 8) || (x 5 && x 8) || (x 6 && x 8)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → ((∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 8)) ∨ (∃ j : Fin 9, (8 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 8 && y j)) ∨ (∃ j : Fin 9, (8 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 8 || y j))) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 2 && x 7) || (x 4 && x 7) || (x 0 && x 8) || (x 3 && x 8) || (x 5 && x 8) || (x 6 && x 8)) → 16 ≤ C.size) → ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 2 && x 7) || (x 4 && x 7) || (x 0 && x 8) || (x 3 && x 8) || (x 5 && x 8) || (x 6 && x 8)) t → 16 ≤ t) := by
  intro H0 h0 h1 h2 h3 h4 h5 h6 h7 h8
  refine PEqualNP.Outside.L_meta_17108.g9_core _ (fun i => decide (i = 0 ∨ i = 4)) (by decide)
    (by decide) (fun C hm hnc => ⟨(H0 9 C hm hnc).1, (H0 9 C hm hnc).2.1⟩) ?_
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6
  · exact h7
  · exact h8
