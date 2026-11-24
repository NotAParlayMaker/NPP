import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 6000000 in
theorem PEqualNP.Outside.R_meta_2153_2
    (hSize : ∀ C : Circuit, FanInTwo C → circuitFun 9 C = (fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) → 15 ≤ C.size)
    (hClean : ∀ (n : ℕ) (C : Circuit), IsMinimalCircuit n C →
      (∃ x y : Fin n → Bool, circuitFun n C x ≠ circuitFun n C y) →
      (∀ g ∈ C.gates, g.op = GateOp.not → g.inputs.length ≤ 1) →
      ∀ j g, C.gates[j]? = some g → (∀ i ∈ g.inputs, i < n + j) ∧ g.inputs.Nodup ∧
        (g.op = GateOp.not → g.inputs.length = 1) ∧ (g.op ≠ GateOp.not → g.inputs.length = 2))
    (hBinary : ∀ C : Circuit, FanInTwo C → circuitFun 9 C = (fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) →
      13 ≤ C.gates.countP (fun g => g.op.eval [true]))
    (hRemaining : ∀ C : Circuit, IsMinimalCircuit 9 C → C.gates.length = 15 →
      (C.gates[0]? = some ⟨GateOp.or, [0,4]⟩ ∨ C.gates[0]? = some ⟨GateOp.or, [4,0]⟩) →
      ∀ a : ℕ, a < 10 → C.gates[1]? = some ⟨GateOp.not, [a]⟩ →
      C.gates.countP (fun g => g.op.eval [false]) ≤ 2 →
      (∀ j g, C.gates[j]? = some g → (∀ i ∈ g.inputs, i < 9 + j) ∧ g.inputs.Nodup) →
      circuitFun 9 C ≠ (fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)))) :
  ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (0 : Fin (9 : ℕ)) || x3 (4 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) → Option.map (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => x5.op) x1.gates[(1 : ℕ)]? = Option.some PEqualNP.CircuitLowerBounds.GateOp.not → (16 : ℕ) ≤ x1.size := by
  intro C hFan hFirst hFun hSecond
  by_contra hSmall
  have hSizeC := hSize C hFan hFun
  have hLenC : C.gates.length = 15 := by
    change ¬16 ≤ C.gates.length at hSmall
    change 15 ≤ C.gates.length at hSizeC
    omega
  have andEval (xs : List Bool) : GateOp.and.eval xs = xs.all id := rfl
  have orEval (xs : List Bool) : GateOp.or.eval xs = xs.any id := rfl
  have notEval (xs : List Bool) : GateOp.not.eval xs = !xs.headD false := rfl
  let trim (g : Gate) : Gate := if g.op.eval [false] then ⟨g.op, g.inputs.take 1⟩ else g
  let D : Circuit := ⟨C.gates.map trim, C.output⟩
  have trimOp (g : Gate) : (trim g).op = g.op := by
    dsimp only [trim]
    split <;> rfl
  have trimEval (g : Gate) (hg : g ∈ C.gates) (f : ℕ → Bool) :
      (trim g).op.eval ((trim g).inputs.map f) = g.op.eval (g.inputs.map f) := by
    have ho := (hFan g hg).1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ho
    rcases ho with ho | ho | ho
    · simp [trim, ho, andEval]
    · simp [trim, ho, orEval]
    · cases h : g.inputs <;> simp [trim, ho, notEval, h]
  have hFanD : FanInTwo D := by
    intro g hg
    change g ∈ C.gates.map trim at hg
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hg
    refine ⟨by rw [trimOp]; exact (hFan a ha).1, ?_⟩
    dsimp only [trim]
    split
    · simp
    · exact (hFan a ha).2
  have hUnary : ∀ g ∈ D.gates, g.op = .not → g.inputs.length ≤ 1 := by
    intro g hg hn
    change g ∈ C.gates.map trim at hg
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hg
    rw [trimOp] at hn
    simp [trim, hn, notEval]
  let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have hFold (ls : List Gate) (hls : ∀ g ∈ ls, g ∈ C.gates) :
      ∀ w : List Bool, (ls.map trim).foldl step w = ls.foldl step w := by
    induction ls with
    | nil => intro w; rfl
    | cons g ls ih =>
      intro w
      rw [List.map_cons, List.foldl_cons, List.foldl_cons]
      have hstep : step w (trim g) = step w g := by
        dsimp only [step]
        rw [trimEval g (hls g List.mem_cons_self)]
      rw [hstep]
      exact ih (fun a ha => hls a (List.mem_cons_of_mem _ ha)) _
  have hWires (x : List Bool) : D.wires x = C.wires x :=
    hFold C.gates (fun _ h => h) x
  have hFunD : circuitFun 9 D = circuitFun 9 C := by
    funext x
    change (D.wires (List.ofFn x)).getD C.output false = (C.wires (List.ofFn x)).getD C.output false
    rw [hWires]
  have hLenD : D.gates.length = 15 := by simp [D, hLenC]
  have hMin : IsMinimalCircuit 9 D := ⟨hFanD, fun E hE hEq => by
    have hh := hSize E hE (hEq.trans (hFunD.trans hFun))
    change D.gates.length ≤ E.size
    simpa only [hLenD] using hh⟩
  have hNonconst : ∃ x y : Fin 9 → Bool, circuitFun 9 D x ≠ circuitFun 9 D y := by
    rw [hFunD, hFun]
    refine ⟨fun _ => false, fun i => decide (i = 0 ∨ i = 1), ?_⟩
    decide +kernel
  have hCleanD := hClean 9 D hMin hNonconst hUnary
  have hSecondD : D.gates[1]?.map Gate.op = some GateOp.not := by
    dsimp only [D]
    rw [List.getElem?_map, Option.map_map]
    change C.gates[1]?.map (fun g => (trim g).op) = some GateOp.not
    simpa only [trimOp] using hSecond
  have hSecLt : 1 < D.gates.length := by omega
  let second := D.gates[1]
  have hSecondGet : D.gates[1]? = some second := List.getElem?_eq_getElem hSecLt
  have hSecondOp : second.op = .not := by
    rw [hSecondGet] at hSecondD
    exact Option.some.inj hSecondD
  obtain ⟨hSecondRead, _, hSecondArity, _⟩ := hCleanD 1 second hSecondGet
  obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp (hSecondArity hSecondOp)
  have hSecA : a < 10 := hSecondRead a (by simp [ha])
  have hSec : D.gates[1]? = some ⟨GateOp.not, [a]⟩ := by
    rw [hSecondGet]
    rw [← hSecondOp, ← ha]
  have hStable (ls : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
      (ls.foldl step w).getD i false = w.getD i false := by
    induction ls with
    | nil => intro w i hi; rfl
    | cons g ls ih =>
      intro w i hi
      rw [List.foldl_cons, ih _ _ (by simp [step]; omega)]
      exact List.getD_append _ _ _ _ hi
  have hZeroLt : 0 < D.gates.length := by omega
  let first := D.gates[0]
  have hFirstGet : D.gates[0]? = some first := List.getElem?_eq_getElem hZeroLt
  have hFirstMem : first ∈ D.gates := List.getElem_mem hZeroLt
  obtain ⟨hRead0, _, hArityNot, hArityBin⟩ := hCleanD 0 first hFirstGet
  have hSplit : D.gates = first :: D.gates.drop 1 := by
    simpa only [List.drop_zero, first] using List.drop_eq_getElem_cons hZeroLt
  have hEvalFirst (x : Fin 9 → Bool) :
      first.op.eval (first.inputs.map fun i => (List.ofFn x).getD i false) = (x 0 || x 4) := by
    have hOld : (D.wires (List.ofFn x)).getD 9 false = (x 0 || x 4) := by
      rw [hWires]
      exact hFirst x
    change (D.gates.foldl step (List.ofFn x)).getD 9 false = _ at hOld
    rw [hSplit, List.foldl_cons, hStable _ _ _ (by simp [step])] at hOld
    change ((List.ofFn x) ++ [first.op.eval (first.inputs.map fun i => (List.ofFn x).getD i false)]).getD 9 false = _ at hOld
    rwa [List.getD_append_right _ _ _ _ (by simp), List.length_ofFn,
      Nat.sub_self, List.getD_cons_zero] at hOld
  have hGet (x : Fin 9 → Bool) (i : ℕ) (hi : i < 9) : (List.ofFn x).getD i false = x ⟨i, hi⟩ := by
    rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_ofFn]
  have hOp0 := (hFanD first hFirstMem).1
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hOp0
  have hNot0 : first.op ≠ .not := by
    intro hn
    obtain ⟨k, hk⟩ := List.length_eq_one_iff.mp (hArityNot hn)
    have hkr : k < 9 := hRead0 k (by simp [hk])
    have he := hEvalFirst (fun _ => false)
    rw [hn, hk] at he
    simp only [List.map_cons, List.map_nil] at he
    rw [hGet (fun _ => false) k hkr] at he
    change true = false at he
    exact Bool.noConfusion he
  obtain ⟨u, v, huv⟩ := List.length_eq_two.mp (hArityBin hNot0)
  have hu : u < 9 := hRead0 u (by simp [huv])
  have hv : v < 9 := hRead0 v (by simp [huv])
  let e0 : Fin 9 → Bool := fun i => decide (i.val = 0)
  let e4 : Fin 9 → Bool := fun i => decide (i.val = 4)
  have h0 : first.op.eval [decide (u = 0), decide (v = 0)] = true := by
    have he := hEvalFirst e0
    rw [huv] at he
    simp only [List.map_cons, List.map_nil] at he
    rw [hGet e0 u hu, hGet e0 v hv] at he
    exact he
  have h4 : first.op.eval [decide (u = 4), decide (v = 4)] = true := by
    have he := hEvalFirst e4
    rw [huv] at he
    simp only [List.map_cons, List.map_nil] at he
    rw [hGet e4 u hu, hGet e4 v hv] at he
    exact he
  have hFirstOR : first.op = .or := by
    rcases hOp0 with ho | ho | ho
    · exfalso
      have ha : u = 0 ∧ v = 0 := by
        simpa [ho, andEval] using h0
      have hb : u = 4 ∧ v = 4 := by
        simpa [ho, andEval] using h4
      omega
    · exact ho
    · exact False.elim (hNot0 ho)
  have hFirstList : first.inputs = [0,4] ∨ first.inputs = [4,0] := by
    have ha : u = 0 ∨ v = 0 := by
      simpa [hFirstOR, orEval] using h0
    have hb : u = 4 ∨ v = 4 := by
      simpa [hFirstOR, orEval] using h4
    rw [huv]
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · omega
    · exact Or.inl (by rw [ha, hb])
    · exact Or.inr (by rw [ha, hb])
    · omega
  have hFirstShape : D.gates[0]? = some ⟨GateOp.or, [0,4]⟩ ∨
      D.gates[0]? = some ⟨GateOp.or, [4,0]⟩ := by
    rw [hFirstGet]
    rcases hFirstList with h | h
    · left
      apply congrArg some
      calc
        first = ⟨first.op, first.inputs⟩ := rfl
        _ = ⟨GateOp.or, [0,4]⟩ := by rw [hFirstOR, h]
    · right
      apply congrArg some
      calc
        first = ⟨first.op, first.inputs⟩ := rfl
        _ = ⟨GateOp.or, [4,0]⟩ := by rw [hFirstOR, h]
  have hCount (ls : List Gate) (hls : ∀ g ∈ ls, g ∈ D.gates) :
      ls.countP (fun g => g.op.eval [true]) + ls.countP (fun g => g.op.eval [false]) = ls.length := by
    induction ls with
    | nil => rfl
    | cons g ls ih =>
      have ht := ih (fun a ha => hls a (List.mem_cons_of_mem _ ha))
      have ho := (hFanD g (hls g List.mem_cons_self)).1
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ho
      rcases ho with ho | ho | ho <;> simp [ho, andEval, orEval, notEval] <;> omega
  have hBin := hBinary D hFanD (hFunD.trans hFun)
  have hSum := hCount D.gates (fun _ h => h)
  have hFew : D.gates.countP (fun g => g.op.eval [false]) ≤ 2 := by omega
  have hNormal : ∀ j g, D.gates[j]? = some g → (∀ i ∈ g.inputs, i < 9 + j) ∧ g.inputs.Nodup :=
    fun j g hj => ⟨(hCleanD j g hj).1, (hCleanD j g hj).2.1⟩
  exact hRemaining D hMin hLenD hFirstShape a hSecA hSec hFew hNormal (hFunD.trans hFun)
