import Mathlib.Tactic
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_2311_1
  (lower : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)); ∀ C : Circuit, FanInTwo C → circuitFun 9 C = x1 → 15 ≤ C.size)
  (bridge : ∀ (C : Circuit) (head : Gate) (tail : List Gate), C.gates = head :: tail → IsMinimalCircuit 9 C → (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = !(x 0)) → (∀ g ∈ tail, g.op = .not → g.inputs.length ≤ 1) → (tail.filter (fun g : Gate => [0,9].any fun i => g.inputs.contains i)).length = 2 → ¬ (∃ pre g post, tail = pre ++ g :: post ∧ ((g.op = .and ∧ 0 ∈ g.inputs) ∨ (g.op = .or ∧ 9 ∈ g.inputs)) ∧ ∃ h ∈ post, (fun g : Gate => [0,9].any fun i => g.inputs.contains i) h = false ∧ 10 + pre.length ∈ h.inputs) → (∃ y z : Fin 8 → Bool, circuitFun 9 C (Fin.cons false y) ≠ circuitFun 9 C (Fin.cons false z)) → ∀ g ∈ tail, ¬ ((g.op = .and ∧ 0 ∈ g.inputs) ∨ (g.op = .or ∧ 9 ∈ g.inputs)))
  (remaining : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)); ∀ (C : Circuit) (head : Gate) (tail : List Gate), C.gates = head :: tail → IsMinimalCircuit 9 C → (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = !(x 0)) → circuitFun 9 C = x1 → C.size ≤ 15 → (∀ g ∈ tail, g.op = .not → g.inputs.length ≤ 1) → (tail.filter (fun g : Gate => [0,9].any fun i => g.inputs.contains i)).length = 2 → (∀ g ∈ tail, ¬ ((g.op = .and ∧ 0 ∈ g.inputs) ∨ (g.op = .or ∧ 9 ∈ g.inputs))) → False)
  : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   have x3 : List PEqualNP.CircuitLowerBounds.Gate := List.map (fun (x3 : PEqualNP.CircuitLowerBounds.Gate) => { op := x3.op, inputs := if x3.op.eval [Bool.false] = Bool.true then List.take (1 : ℕ) x3.inputs else x3.inputs : PEqualNP.CircuitLowerBounds.Gate }) (List.drop (1 : ℕ) x2.gates);   have x4 : PEqualNP.CircuitLowerBounds.Gate → Bool := fun (x4 : PEqualNP.CircuitLowerBounds.Gate) => [(0 : ℕ), (9 : ℕ)].any fun (x5 : ℕ) => x4.inputs.contains x5;   have x5 : ℕ := (List.filter x4 x3).length;   have x6 : Prop := ∃ (x6 : List PEqualNP.CircuitLowerBounds.Gate) (x7 : PEqualNP.CircuitLowerBounds.Gate) (x8 : List PEqualNP.CircuitLowerBounds.Gate), x3 = x6 ++ x7 :: x8 ∧ (x7.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (0 : ℕ) ∈ x7.inputs ∨ x7.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (9 : ℕ) ∈ x7.inputs) ∧ ∃ x9 ∈ x8, x4 x9 = Bool.false ∧ (10 : ℕ) + x6.length ∈ x9.inputs;   PEqualNP.MetaComplexity.FanInTwo x2 → (∀ (x8 : Fin (9 : ℕ) → Bool), (x2.wires (List.ofFn x8)).getD (9 : ℕ) Bool.false = !x8 (0 : Fin (9 : ℕ))) → PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x2 = x1 → x2.size ≤ (15 : ℕ) → x5 = (2 : ℕ) → ¬x6 → False := by
  dsimp only
  intro C fan first computes size readers noCascade
  let cut : Gate → Gate := fun g =>
    ⟨g.op, if g.op.eval [false] = true then g.inputs.take 1 else g.inputs⟩
  let allowed : Gate → Prop := fun g =>
    (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2
  let step : List Bool → Gate → List Bool := fun w g =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have cutAllowed (g : Gate) (h : allowed g) : allowed (cut g) := by
    obtain ⟨op,ins⟩ := g
    change (op = .and ∨ op = .or ∨ op = .not) ∧ ins.length ≤ 2 at h
    rcases h with ⟨rfl | rfl | rfl,hlen⟩
    · exact ⟨Or.inl rfl, hlen⟩
    · exact ⟨Or.inr (Or.inl rfl), hlen⟩
    · refine ⟨Or.inr (Or.inr rfl), ?_⟩
      change (ins.take 1).length ≤ 2
      have : (ins.take 1).length ≤ 1 := by simp
      omega
  have cutStep (g : Gate) (h : allowed g) (w : List Bool) : step w (cut g) = step w g := by
    obtain ⟨op,ins⟩ := g
    change (op = .and ∨ op = .or ∨ op = .not) ∧ ins.length ≤ 2 at h
    rcases h with ⟨rfl | rfl | rfl,hlen⟩
    · rfl
    · rfl
    · cases ins <;> rfl
  have cutRun (gs : List Gate) (h : ∀ g ∈ gs, allowed g) (w : List Bool) :
      (gs.map cut).foldl step w = gs.foldl step w := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      simp only [List.map_cons,List.foldl_cons]
      rw [cutStep g (h g List.mem_cons_self)]
      exact ih (fun q hq => h q (List.mem_cons_of_mem _ hq)) _
  have legal : ∀ g ∈ C.gates, allowed g := by
    intro g hg
    simpa only [allowed,Set.mem_insert_iff,Set.mem_singleton_iff] using fan g hg
  let D : Circuit := ⟨C.gates.map cut,C.output⟩
  have sameWires (xs : List Bool) : D.wires xs = C.wires xs := cutRun C.gates legal xs
  have sameFun : circuitFun 9 D = circuitFun 9 C := by
    funext x
    change (D.wires _).getD D.output false = (C.wires _).getD C.output false
    rw [sameWires]
  have sameSize : D.size = C.size := by
    change (C.gates.map cut).length = C.gates.length
    exact List.length_map cut
  have fanD : FanInTwo D := by
    intro g hg
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hg
    simpa only [allowed,Set.mem_insert_iff,Set.mem_singleton_iff] using cutAllowed q (legal q hq)
  have firstD (x : Fin 9 → Bool) : (D.wires (List.ofFn x)).getD 9 false = !(x 0) := by
    rw [sameWires]
    exact first x
  have minD : IsMinimalCircuit 9 D := by
    refine ⟨fanD, ?_⟩
    intro E fanE eqE
    have he := lower E fanE (eqE.trans (sameFun.trans computes))
    have hd : D.size ≤ 15 := sameSize.trans_le size
    omega
  have nonconstant : ∃ y z : Fin 8 → Bool,
      circuitFun 9 D (Fin.cons false y) ≠ circuitFun 9 D (Fin.cons false z) := by
    rw [sameFun,computes]
    refine ⟨fun _ => false, fun i => decide (i = 0 ∨ i = 1), ?_⟩
    decide
  cases hs : C.gates with
  | nil =>
    have hz := first (fun _ => false)
    change (C.gates.foldl step (List.ofFn (fun _ : Fin 9 => false))).getD 9 false = true at hz
    rw [hs,List.foldl_nil,List.getD_eq_default _ _ (by simp)] at hz
    contradiction
  | cons head tail =>
    let tailD := tail.map cut
    have shapeD : D.gates = cut head :: tailD := by simp [D,tailD,hs]
    have short : ∀ g ∈ tailD, g.op = .not → g.inputs.length ≤ 1 := by
      intro g hg hn
      obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hg
      obtain ⟨op,ins⟩ := q
      change op = .not at hn
      subst op
      change (ins.take 1).length ≤ 1
      simp
    have countD : (tailD.filter (fun g => [0,9].any fun i => g.inputs.contains i)).length = 2 := by
      simpa [tailD,hs,cut] using readers
    have noD : ¬ (∃ pre g post, tailD = pre ++ g :: post ∧
      ((g.op = .and ∧ 0 ∈ g.inputs) ∨ (g.op = .or ∧ 9 ∈ g.inputs)) ∧
      ∃ h ∈ post, (fun g : Gate => [0,9].any fun i => g.inputs.contains i) h = false ∧
        10 + pre.length ∈ h.inputs) := by
      simpa [tailD,hs,cut] using noCascade
    have noAbsorber := bridge D (cut head) tailD shapeD minD firstD short countD noD nonconstant
    exact remaining D (cut head) tailD shapeD minD firstD (sameFun.trans computes)
      (sameSize.trans_le size) short countD noAbsorber
