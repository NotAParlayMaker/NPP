import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17109

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem fold_getD (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    rw [List.foldl_cons, ih (step w g) i (by simp [step]; omega)]
    exact List.getD_append _ _ _ _ hi

theorem first_wire (n : ℕ) (C : Circuit) (g : Gate) (rest : List Gate) (hg : C.gates = g :: rest)
    (y : Fin n → Bool) :
    (C.wires (List.ofFn y)).getD n false
      = g.op.eval (g.inputs.map fun i => (List.ofFn y).getD i false) := by
  have h : C.wires (List.ofFn y) = rest.foldl step (step (List.ofFn y) g) := by
    unfold Circuit.wires
    rw [hg]
    rfl
  rw [h, fold_getD _ _ _ (by simp [step])]
  simp [step]

theorem input_wire (n : ℕ) (C : Circuit) (y : Fin n → Bool) (i : Fin n) :
    (C.wires (List.ofFn y)).getD (i : ℕ) false = y i := by
  have h : C.wires (List.ofFn y) = C.gates.foldl step (List.ofFn y) := rfl
  rw [h, fold_getD _ _ _ (by simp)]
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

theorem rd (n : ℕ) (a : ℕ) :
    (∃ i : Fin n, ∀ y : Fin n → Bool, (List.ofFn y).getD a false = y i) ∨
      (∀ y : Fin n → Bool, (List.ofFn y).getD a false = false) := by
  by_cases h : a < n
  · left
    refine ⟨⟨a, h⟩, fun y => ?_⟩
    rw [List.getD_eq_getElem _ _ (by simpa using h)]
    simp
  · right
    intro y
    exact List.getD_eq_default _ _ (by simpa using h)

def Shape (n : ℕ) (C : Circuit) (i : Fin n) : Prop :=
  (∀ y : Fin n → Bool, (C.wires (List.ofFn y)).getD n false = !(y i)) ∨
  (∃ j : Fin n, i < j ∧ ∀ y : Fin n → Bool, (C.wires (List.ofFn y)).getD n false = (y i && y j)) ∨
  (∃ j : Fin n, i < j ∧ ∀ y : Fin n → Bool, (C.wires (List.ofFn y)).getD n false = (y i || y j))

theorem first_shape (n : ℕ) (C : Circuit) (g : Gate) (rest : List Gate)
    (hg : C.gates = g :: rest) (hC : FanInTwo C)
    (hnc : ∃ x y : Fin n → Bool,
      (C.wires (List.ofFn x)).getD n false ≠ (C.wires (List.ofFn y)).getD n false)
    (hcp : ∀ i : Fin n, ∃ x : Fin n → Bool, x i ≠ (C.wires (List.ofFn x)).getD n false) :
    ∃ i : Fin n, Shape n C i := by
  have hw := first_wire n C g rest hg
  have hok := hC g (by rw [hg]; exact List.mem_cons_self)
  have noconst : ∀ b : Bool, (∀ y : Fin n → Bool, (C.wires (List.ofFn y)).getD n false = b) → False := by
    intro b hb
    obtain ⟨x, y, hxy⟩ := hnc
    exact hxy ((hb x).trans (hb y).symm)
  have nocopy : ∀ i : Fin n, (∀ y : Fin n → Bool, (C.wires (List.ofFn y)).getD n false = y i) → False := by
    intro i hi
    obtain ⟨x, hx⟩ := hcp i
    exact hx (hi x).symm
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hlen⟩ := hok
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  simp only at hw hlen
  match ins, hlen, hw with
  | [], _, hw =>
    exfalso
    rcases hop with rfl | rfl | rfl
    · exact noconst true fun y => by rw [hw y]; rfl
    · exact noconst false fun y => by rw [hw y]; rfl
    · exact noconst true fun y => by rw [hw y]; rfl
  | [a], _, hw =>
    simp only [List.map_cons, List.map_nil] at hw
    rcases rd n a with ⟨i, hi⟩ | h0
    · rcases hop with rfl | rfl | rfl
      · exact (nocopy i fun y => by rw [hw y, hi y]; simp [GateOp.eval]).elim
      · exact (nocopy i fun y => by rw [hw y, hi y]; simp [GateOp.eval]).elim
      · exact ⟨i, .inl fun y => by rw [hw y, hi y]; simp [GateOp.eval]⟩
    · exfalso
      rcases hop with rfl | rfl | rfl
      · exact noconst false fun y => by rw [hw y, h0 y]; simp [GateOp.eval]
      · exact noconst false fun y => by rw [hw y, h0 y]; simp [GateOp.eval]
      · exact noconst true fun y => by rw [hw y, h0 y]; simp [GateOp.eval]
  | [a, b], _, hw =>
    simp only [List.map_cons, List.map_nil] at hw
    rcases rd n a with ⟨i, hi⟩ | h0
    · rcases rd n b with ⟨j, hj⟩ | h1
      · rcases hop with rfl | rfl | rfl
        · have e : ∀ y : Fin n → Bool, (C.wires (List.ofFn y)).getD n false = (y i && y j) :=
            fun y => by rw [hw y, hi y, hj y]; simp [GateOp.eval]
          rcases lt_trichotomy i j with h | h | h
          · exact ⟨i, .inr (.inl ⟨j, h, e⟩)⟩
          · subst h
            exact (nocopy i fun y => by rw [e y, Bool.and_self]).elim
          · exact ⟨j, .inr (.inl ⟨i, h, fun y => by rw [e y, Bool.and_comm]⟩)⟩
        · have e : ∀ y : Fin n → Bool, (C.wires (List.ofFn y)).getD n false = (y i || y j) :=
            fun y => by rw [hw y, hi y, hj y]; simp [GateOp.eval]
          rcases lt_trichotomy i j with h | h | h
          · exact ⟨i, .inr (.inr ⟨j, h, e⟩)⟩
          · subst h
            exact (nocopy i fun y => by rw [e y, Bool.or_self]).elim
          · exact ⟨j, .inr (.inr ⟨i, h, fun y => by rw [e y, Bool.or_comm]⟩)⟩
        · exact ⟨i, .inl fun y => by rw [hw y, hi y]; simp [GateOp.eval]⟩
      · rcases hop with rfl | rfl | rfl
        · exact (noconst false fun y => by rw [hw y, h1 y]; simp [GateOp.eval]).elim
        · exact (nocopy i fun y => by rw [hw y, hi y, h1 y]; simp [GateOp.eval]).elim
        · exact ⟨i, .inl fun y => by rw [hw y, hi y]; simp [GateOp.eval]⟩
    · rcases hop with rfl | rfl | rfl
      · exact (noconst false fun y => by rw [hw y, h0 y]; simp [GateOp.eval]).elim
      · rcases rd n b with ⟨j, hj⟩ | h1
        · exact (nocopy j fun y => by rw [hw y, h0 y, hj y]; simp [GateOp.eval]).elim
        · exact (noconst false fun y => by rw [hw y, h0 y, h1 y]; simp [GateOp.eval]).elim
      · exact (noconst true fun y => by rw [hw y, h0 y]; simp [GateOp.eval]).elim
  | _ :: _ :: _ :: _, hlen, _ => simp at hlen

theorem assemble (n K : ℕ) (f : (Fin n → Bool) → Bool) (hf : ∃ x y, f x ≠ f y)
    (hproj : ∀ i : Fin n, ∃ x, f x ≠ x i)
    (red : ∀ C : Circuit, IsMinimalCircuit n C →
      (∃ x y : Fin n → Bool, circuitFun n C x ≠ circuitFun n C y) →
      (∀ j : ℕ, j < C.gates.length → ∃ x y : Fin n → Bool,
        (C.wires (List.ofFn x)).getD (n + j) false ≠ (C.wires (List.ofFn y)).getD (n + j) false) ∧
      (∀ i j : ℕ, i < n + j → j < C.gates.length → ∃ x : Fin n → Bool,
        (C.wires (List.ofFn x)).getD i false ≠ (C.wires (List.ofFn x)).getD (n + j) false))
    (cases : ∀ (i : Fin n) (C : Circuit), FanInTwo C → Shape n C i → circuitFun n C = f → K ≤ C.size) :
    ∀ t : ℕ, HasCircuitSize n f t → K ≤ t := by
  classical
  intro t ht
  have hex : ∃ s, HasCircuitSize n f s := ⟨t, ht⟩
  obtain ⟨C, ok, hsz, hev⟩ := Nat.find_spec hex
  have hfun : circuitFun n C = f := funext hev
  have hmin : IsMinimalCircuit n C := by
    refine ⟨ok, fun D hD hDf => ?_⟩
    have hD' : HasCircuitSize n f D.size :=
      ⟨D, hD, le_rfl, fun x => congrFun (hDf.trans hfun) x⟩
    exact hsz.trans (Nat.find_min' hex hD')
  obtain ⟨h1, h2⟩ := red C hmin (by rw [hfun]; exact hf)
  have hne : C.gates ≠ [] := by
    intro he
    have hv : ∀ x : Fin n → Bool, f x = (List.ofFn x).getD C.output false := by
      intro x
      rw [← hev x]
      unfold Circuit.eval Circuit.wires
      rw [he]
      rfl
    rcases rd n C.output with ⟨i, hi⟩ | h0
    · obtain ⟨x, hx⟩ := hproj i
      exact hx ((hv x).trans (hi x))
    · obtain ⟨x, y, hxy⟩ := hf
      exact hxy (((hv x).trans (h0 x)).trans ((hv y).trans (h0 y)).symm)
  obtain ⟨g, rest, hg⟩ := List.exists_cons_of_ne_nil hne
  have hpos : 0 < C.gates.length := by rw [hg]; simp
  obtain ⟨i, hi⟩ := first_shape n C g rest hg ok (by simpa using h1 0 hpos) (by
    intro i
    obtain ⟨x, hx⟩ := h2 i 0 (by have := i.isLt; omega) hpos
    refine ⟨x, ?_⟩
    rw [input_wire] at hx
    simpa using hx)
  exact (cases i C ok hi hfun).trans (hsz.trans (Nat.find_min' hex ht))

def ff : (Fin 9 → Bool) → Bool := fun x => (x 0 && x 4) || (x 1 && x 5) || (x 0 && x 6) || (x 2 && x 6) || (x 0 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 1 && x 8) || (x 2 && x 8) || (x 3 && x 8) || (x 5 && x 8) || (x 7 && x 8)

theorem ff_nonconst : ∃ x y, ff x ≠ ff y :=
  ⟨fun _ => false, fun _ => true, by decide⟩

theorem ff_proj : ∀ i : Fin 9, ∃ x, ff x ≠ x i := fun i =>
  ⟨fun k => decide (k = i), by revert i; decide +kernel⟩

end PEqualNP.Outside.L_meta_17109

theorem PEqualNP.Outside.L_meta_17109 : ((∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalCircuit n C → (∃ x y : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n C x ≠ PEqualNP.MetaComplexity.circuitFun n C y) → (∀ j : ℕ, j < C.gates.length → ∃ x y : Fin n → Bool, (C.wires (List.ofFn x)).getD (n + j) false ≠ (C.wires (List.ofFn y)).getD (n + j) false) ∧ (∀ i j : ℕ, i < n + j → j < C.gates.length → ∃ x : Fin n → Bool, (C.wires (List.ofFn x)).getD i false ≠ (C.wires (List.ofFn x)).getD (n + j) false) ∧ (C.gates ≠ [] → C.output + 1 = n + C.gates.length) ∧ (∀ j : ℕ, j + 1 < C.gates.length → ∃ p ∈ C.gates.zipIdx, n + j < n + p.2 ∧ (PEqualNP.CircuitLowerBounds.GateOp.casesOn (motive := fun _ => List ℕ) p.1.op p.1.inputs p.1.inputs (p.1.inputs.take 1) (fun _ => p.1.inputs) p.1.inputs).contains (n + j) = true)) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → ((∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 0)) ∨ (∃ j : Fin 9, (0 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 && y j)) ∨ (∃ j : Fin 9, (0 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y j))) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 1 && x 5) || (x 0 && x 6) || (x 2 && x 6) || (x 0 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 1 && x 8) || (x 2 && x 8) || (x 3 && x 8) || (x 5 && x 8) || (x 7 && x 8)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → ((∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 1)) ∨ (∃ j : Fin 9, (1 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 1 && y j)) ∨ (∃ j : Fin 9, (1 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 1 || y j))) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 1 && x 5) || (x 0 && x 6) || (x 2 && x 6) || (x 0 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 1 && x 8) || (x 2 && x 8) || (x 3 && x 8) || (x 5 && x 8) || (x 7 && x 8)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → ((∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 2)) ∨ (∃ j : Fin 9, (2 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 2 && y j)) ∨ (∃ j : Fin 9, (2 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 2 || y j))) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 1 && x 5) || (x 0 && x 6) || (x 2 && x 6) || (x 0 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 1 && x 8) || (x 2 && x 8) || (x 3 && x 8) || (x 5 && x 8) || (x 7 && x 8)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → ((∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 3)) ∨ (∃ j : Fin 9, (3 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 3 && y j)) ∨ (∃ j : Fin 9, (3 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 3 || y j))) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 1 && x 5) || (x 0 && x 6) || (x 2 && x 6) || (x 0 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 1 && x 8) || (x 2 && x 8) || (x 3 && x 8) || (x 5 && x 8) || (x 7 && x 8)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → ((∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 4)) ∨ (∃ j : Fin 9, (4 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 4 && y j)) ∨ (∃ j : Fin 9, (4 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 4 || y j))) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 1 && x 5) || (x 0 && x 6) || (x 2 && x 6) || (x 0 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 1 && x 8) || (x 2 && x 8) || (x 3 && x 8) || (x 5 && x 8) || (x 7 && x 8)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → ((∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 5)) ∨ (∃ j : Fin 9, (5 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 5 && y j)) ∨ (∃ j : Fin 9, (5 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 5 || y j))) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 1 && x 5) || (x 0 && x 6) || (x 2 && x 6) || (x 0 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 1 && x 8) || (x 2 && x 8) || (x 3 && x 8) || (x 5 && x 8) || (x 7 && x 8)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → ((∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 6)) ∨ (∃ j : Fin 9, (6 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 6 && y j)) ∨ (∃ j : Fin 9, (6 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 6 || y j))) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 1 && x 5) || (x 0 && x 6) || (x 2 && x 6) || (x 0 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 1 && x 8) || (x 2 && x 8) || (x 3 && x 8) || (x 5 && x 8) || (x 7 && x 8)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → ((∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 7)) ∨ (∃ j : Fin 9, (7 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 7 && y j)) ∨ (∃ j : Fin 9, (7 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 7 || y j))) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 1 && x 5) || (x 0 && x 6) || (x 2 && x 6) || (x 0 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 1 && x 8) || (x 2 && x 8) || (x 3 && x 8) || (x 5 && x 8) || (x 7 && x 8)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → ((∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 8)) ∨ (∃ j : Fin 9, (8 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 8 && y j)) ∨ (∃ j : Fin 9, (8 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 8 || y j))) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 1 && x 5) || (x 0 && x 6) || (x 2 && x 6) || (x 0 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 1 && x 8) || (x 2 && x 8) || (x 3 && x 8) || (x 5 && x 8) || (x 7 && x 8)) → 16 ≤ C.size) → ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 1 && x 5) || (x 0 && x 6) || (x 2 && x 6) || (x 0 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 1 && x 8) || (x 2 && x 8) || (x 3 && x 8) || (x 5 && x 8) || (x 7 && x 8)) t → 16 ≤ t) := by
  intro red H0 H1 H2 H3 H4 H5 H6 H7 H8
  refine PEqualNP.Outside.L_meta_17109.assemble 9 16 PEqualNP.Outside.L_meta_17109.ff PEqualNP.Outside.L_meta_17109.ff_nonconst PEqualNP.Outside.L_meta_17109.ff_proj
    (fun C h1 h2 => ⟨(red 9 C h1 h2).1, (red 9 C h1 h2).2.1⟩) ?_
  intro i
  fin_cases i
  · exact H0
  · exact H1
  · exact H2
  · exact H3
  · exact H4
  · exact H5
  · exact H6
  · exact H7
  · exact H8
