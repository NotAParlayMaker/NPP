import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

namespace PEqualNP.Outside.L_meta_3306

/-- One fold step: append the value of gate `g` given the wire values `w`. -/
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_fold (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

/-- Swap the first two inputs unless they already run from `x4` to `x3`. -/
def fixInputs (x3 x4 : Finset ℕ) : List ℕ → List ℕ
  | u :: v :: rest => if u ∈ x4 ∧ v ∈ x3 then u :: v :: rest else v :: u :: rest
  | l => l

/-- Reorient the operands of an AND gate; leave every other gate alone. -/
noncomputable def fixGate (x3 x4 : Finset ℕ) (g : Gate) : Gate :=
  letI := gateOpDecEq
  if g.op = GateOp.and then ⟨g.op, fixInputs x3 x4 g.inputs⟩ else g

lemma fixInputs_length (x3 x4 : Finset ℕ) (l : List ℕ) :
    (fixInputs x3 x4 l).length = l.length := by
  match l with
  | [] => rfl
  | [_] => rfl
  | u :: v :: rest => simp only [fixInputs]; split <;> simp

lemma fixInputs_mem (x3 x4 : Finset ℕ) (l : List ℕ) (i : ℕ)
    (h : i ∈ fixInputs x3 x4 l) : i ∈ l := by
  match l with
  | [] => exact absurd h (by simp [fixInputs])
  | [_] => simpa [fixInputs] using h
  | u :: v :: rest =>
    simp only [fixInputs] at h
    split at h
    · simpa using h
    · simp only [List.mem_cons] at h ⊢
      rcases h with h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inr h)

lemma fixInputs_eval (x3 x4 : Finset ℕ) (l : List ℕ) (φ : ℕ → Bool) :
    GateOp.and.eval ((fixInputs x3 x4 l).map φ) = GateOp.and.eval (l.map φ) := by
  match l with
  | [] => rfl
  | [_] => rfl
  | u :: v :: rest =>
    simp only [fixInputs]
    split
    · rfl
    · simp only [List.map_cons, GateOp.eval, List.all_cons, Bool.and_left_comm]

lemma fixGate_op (x3 x4 : Finset ℕ) (g : Gate) : (fixGate x3 x4 g).op = g.op := by
  unfold fixGate
  split <;> rfl

lemma fixGate_eq_self (x3 x4 : Finset ℕ) (g : Gate) (h : g.op ≠ GateOp.and) :
    fixGate x3 x4 g = g := by
  unfold fixGate
  rw [ite_eq_right h]

lemma fixGate_of_or (x3 x4 : Finset ℕ) (g : Gate) (h : g.op = GateOp.or) :
    fixGate x3 x4 g = g :=
  fixGate_eq_self x3 x4 g (by rw [h]; exact fun e => GateOp.noConfusion e)

lemma fixGate_inputs (x3 x4 : Finset ℕ) (g : Gate) (h : g.op = GateOp.and) :
    (fixGate x3 x4 g).inputs = fixInputs x3 x4 g.inputs := by
  unfold fixGate
  rw [ite_eq_left h]

lemma fixGate_inputs_length (x3 x4 : Finset ℕ) (g : Gate) :
    (fixGate x3 x4 g).inputs.length = g.inputs.length := by
  by_cases h : g.op = GateOp.and
  · rw [fixGate_inputs x3 x4 g h, fixInputs_length]
  · rw [fixGate_eq_self x3 x4 g h]

lemma fixGate_mem (x3 x4 : Finset ℕ) (g : Gate) (i : ℕ)
    (h : i ∈ (fixGate x3 x4 g).inputs) : i ∈ g.inputs := by
  by_cases hop : g.op = GateOp.and
  · rw [fixGate_inputs x3 x4 g hop] at h
    exact fixInputs_mem x3 x4 g.inputs i h
  · rw [fixGate_eq_self x3 x4 g hop] at h
    exact h

lemma fixGate_eval (x3 x4 : Finset ℕ) (g : Gate) (w : List Bool) :
    (fixGate x3 x4 g).op.eval ((fixGate x3 x4 g).inputs.map fun i => w.getD i false)
      = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  by_cases hop : g.op = GateOp.and
  · rw [fixGate_inputs x3 x4 g hop, fixGate_op, hop]
    exact fixInputs_eval x3 x4 g.inputs (fun i => w.getD i false)
  · rw [fixGate_eq_self x3 x4 g hop]

lemma fixGate_oriented (x3 x4 : Finset ℕ) (g : Gate) (u v : ℕ)
    (hop : g.op = GateOp.and) (hin : g.inputs = [u, v])
    (hdisj : (u ∈ x3 ∧ v ∈ x4) ∨ (u ∈ x4 ∧ v ∈ x3)) :
    ∃ a b : ℕ, (fixGate x3 x4 g).inputs = [a, b] ∧ a ∈ x4 ∧ b ∈ x3 := by
  have h1 : (fixGate x3 x4 g).inputs = fixInputs x3 x4 [u, v] := by
    rw [fixGate_inputs x3 x4 g hop, hin]
  rw [h1]
  simp only [fixInputs]
  split
  · rename_i h
    exact ⟨u, v, rfl, h.1, h.2⟩
  · rename_i h
    rcases hdisj with ⟨a, b⟩ | ⟨a, b⟩
    · exact ⟨v, u, rfl, b, a⟩
    · exact absurd ⟨a, b⟩ h

lemma foldl_map_step (f : Gate → Gate) (L : List Gate) (w : List Bool)
    (h : ∀ g ∈ L, ∀ w : List Bool,
      (f g).op.eval ((f g).inputs.map fun i => w.getD i false)
        = g.op.eval (g.inputs.map fun i => w.getD i false)) :
    (L.map f).foldl step w = L.foldl step w := by
  induction L generalizing w with
  | nil => rfl
  | cons g L ih =>
    simp only [List.map_cons, List.foldl_cons, step]
    rw [h g (List.mem_cons_self ..) w]
    exact ih _ (fun g' hg' => h g' (List.mem_cons_of_mem _ hg'))

lemma wires_map_fixGate (x3 x4 : Finset ℕ) (C : Circuit) (w : List Bool) :
    (⟨C.gates.map (fixGate x3 x4), C.output⟩ : Circuit).wires w = C.wires w := by
  simp only [wires_eq_fold]
  exact foldl_map_step (fixGate x3 x4) C.gates w (fun g _ w => fixGate_eval x3 x4 g w)

lemma getD_map_lt {α : Type} (L : List α) (f : α → α) (j : ℕ) (d : α)
    (h : j < L.length) : (L.map f).getD j d = f (L.getD j d) := by
  rw [List.getD_eq_getElem _ _ (by simpa using h), List.getD_eq_getElem _ _ h, List.getElem_map]

lemma getD_map_ge {α : Type} (L : List α) (f : α → α) (j : ℕ) (d : α)
    (h : L.length ≤ j) : (L.map f).getD j d = d := by
  rw [List.getD_eq_default _ _ (by simpa using h)]

lemma gateAt_map_lt (x3 x4 : Finset ℕ) (C : Circuit) (j : ℕ) (h : j < C.gates.length) :
    gateAt (⟨C.gates.map (fixGate x3 x4), C.output⟩ : Circuit) j
      = fixGate x3 x4 (gateAt C j) := by
  show (C.gates.map (fixGate x3 x4)).getD j ⟨GateOp.or, []⟩
      = fixGate x3 x4 (C.gates.getD j ⟨GateOp.or, []⟩)
  exact getD_map_lt C.gates (fixGate x3 x4) j ⟨GateOp.or, []⟩ h

lemma gateAt_map_ge (x3 x4 : Finset ℕ) (C : Circuit) (j : ℕ) (h : C.gates.length ≤ j) :
    gateAt (⟨C.gates.map (fixGate x3 x4), C.output⟩ : Circuit) j = gateAt C j := by
  show (C.gates.map (fixGate x3 x4)).getD j ⟨GateOp.or, []⟩ = C.gates.getD j ⟨GateOp.or, []⟩
  rw [getD_map_ge C.gates (fixGate x3 x4) j ⟨GateOp.or, []⟩ h,
    List.getD_eq_default _ _ h]

end PEqualNP.Outside.L_meta_3306

open PEqualNP.Outside.L_meta_3306

theorem PEqualNP.Outside.L_meta_3306 :
∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : Finset ℕ), PEqualNP.TopForm.IsAO2 x1 x2 → (∀ x6 < x2.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x6).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x9 : ℕ) (x10 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x6).inputs = [x9, x10] ∧ (x9 ∈ x3 ∧ x10 ∈ x4 ∨ x9 ∈ x4 ∧ x10 ∈ x3)) → ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x7 ∧ x7.size = x2.size ∧ PEqualNP.MetaComplexity.circuitFun x1 x7 = PEqualNP.MetaComplexity.circuitFun x1 x2 ∧ (∀ (x8 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x8).op = (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x8).op) ∧ (∀ (x8 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x8).op = PEqualNP.CircuitLowerBounds.GateOp.or → PEqualNP.MetaComplexity.NestedCover.gateAt x7 x8 = PEqualNP.MetaComplexity.NestedCover.gateAt x2 x8) ∧ ∀ x8 < x7.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x8).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x11 : ℕ) (x12 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x8).inputs = [x11, x12] ∧ x11 ∈ x4 ∧ x12 ∈ x3 := by
  intro x1 x2 x3 x4 h1 h2
  classical
  rcases h1 with ⟨hAO, hback, htwo⟩
  refine ⟨⟨x2.gates.map (fixGate x3 x4), x2.output⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold PEqualNP.TopForm.IsAO2
    refine ⟨?_, ?_, ?_⟩
    · intro g' hg'
      obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hg'
      rw [fixGate_op]
      exact hAO g hg
    · intro j hj i hi
      have hj' : j < x2.gates.length := by simpa using hj
      rw [gateAt_map_lt x3 x4 x2 j hj'] at hi
      exact hback j hj' i (fixGate_mem x3 x4 (gateAt x2 j) i hi)
    · intro g' hg'
      obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hg'
      rw [fixGate_inputs_length]
      exact htwo g hg
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size]
  · funext y
    simp only [PEqualNP.MetaComplexity.circuitFun, PEqualNP.CircuitLowerBounds.Circuit.eval]
    rw [wires_map_fixGate]
  · intro j
    by_cases hj : j < x2.gates.length
    · rw [gateAt_map_lt x3 x4 x2 j hj, fixGate_op]
    · rw [gateAt_map_ge x3 x4 x2 j (Nat.le_of_not_lt hj)]
  · intro j hj
    by_cases hlt : j < x2.gates.length
    · rw [gateAt_map_lt x3 x4 x2 j hlt, fixGate_of_or x3 x4 (gateAt x2 j) hj]
    · rw [gateAt_map_ge x3 x4 x2 j (Nat.le_of_not_lt hlt)]
  · intro j hj hopj
    have hj' : j < x2.gates.length := by simpa using hj
    have hstep : gateAt (⟨x2.gates.map (fixGate x3 x4), x2.output⟩ : Circuit) j
        = fixGate x3 x4 (gateAt x2 j) := gateAt_map_lt x3 x4 x2 j hj'
    have hopj' : (gateAt x2 j).op = GateOp.and := by
      rw [hstep, fixGate_op] at hopj
      exact hopj
    obtain ⟨u, v, hin, hdisj⟩ := h2 j hj' hopj'
    rw [hstep]
    exact fixGate_oriented x3 x4 (gateAt x2 j) u v hopj' hin hdisj
