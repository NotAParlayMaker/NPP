import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private abbrev TruthTable := BitVec 8

-- Row i assigns to input j the j-th bit of i.
private def inputTables : List TruthTable := [170, 204, 240]

private def gateTable (wires : List TruthTable) (gate : Gate) : TruthTable :=
  let read := fun i => wires.getD i 0
  match gate.op, gate.inputs with
  | .and, [] => 255
  | .and, [i] => read i
  | .and, i :: j :: _ => read i &&& read j
  | .or, [] => 0
  | .or, [i] => read i
  | .or, i :: j :: _ => read i ||| read j
  | .not, [] => 255
  | .not, i :: _ => ~~~(read i)
  | _, _ => 0

private def wireTables (gates : List Gate) (wires : List TruthTable) : List TruthTable :=
  gates.foldl (fun tables g => tables ++ [gateTable tables g]) wires

private theorem readRow (wires : List TruthTable) (row index : ℕ) :
    (wires.map (fun t => t.getLsbD row)).getD index false =
      (wires.getD index 0).getLsbD row := by
  by_cases h : index < wires.length
  · simp [List.getD_eq_getElem?_getD, h]
  · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt h),
      List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    exact BitVec.getLsbD_zero.symm

private theorem gateRow (wires : List TruthTable) (g : Gate) (row : ℕ) (hrow : row < 8)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hlen : g.inputs.length ≤ 2) :
    g.op.eval (g.inputs.map fun i => (wires.map (fun t => t.getLsbD row)).getD i false) =
      (gateTable wires g).getLsbD row := by
  have full : (255#8).getLsbD row = true := by
    interval_cases row <;> rfl
  obtain ⟨op, inputs⟩ := g
  simp only [readRow]
  cases op with
  | and =>
    match inputs, hlen with
    | [], _ => exact full.symm
    | [_], _ | [_, _], _ => simp [gateTable, GateOp.eval]
    | _ :: _ :: _ :: _, h => simp at h
  | or =>
    match inputs, hlen with
    | [], _ | [_], _ | [_, _], _ => simp [gateTable, GateOp.eval]
    | _ :: _ :: _ :: _, h => simp at h
  | not =>
    cases inputs with
    | nil => exact full.symm
    | cons _ _ => simp [gateTable, GateOp.eval, hrow]
  | mod m => simp at hop
  | maj => simp at hop

private theorem wireRows (gates : List Gate) (wires : List TruthTable) (row : ℕ) (hrow : row < 8)
    (ok : FanInTwo ⟨gates, 0⟩) :
    (Circuit.mk gates 0).wires (wires.map (fun t => t.getLsbD row)) =
      (wireTables gates wires).map (fun t => t.getLsbD row) := by
  induction gates generalizing wires with
  | nil => rfl
  | cons g gs ih =>
    have hg := ok g List.mem_cons_self
    change (Circuit.mk gs 0).wires (wires.map (fun t => t.getLsbD row) ++
      [g.op.eval (g.inputs.map fun i => (wires.map (fun t => t.getLsbD row)).getD i false)]) =
        (wireTables gs (wires ++ [gateTable wires g])).map (fun t => t.getLsbD row)
    rw [gateRow wires g row hrow hg.1 hg.2]
    simpa only [List.map_append, List.map_singleton] using
      ih (wires ++ [gateTable wires g]) (fun g' hg' => ok g' (List.mem_cons_of_mem _ hg'))

-- Include existing wires as well as every output of an AND, OR, or NOT gate.
-- The supplied list includes zero for all reads of unavailable wires.
private def nextTables (available : List TruthTable) : List TruthTable :=
  available ++ (255 :: available.map (fun t => ~~~t)) ++
    available.flatMap (fun a => available.flatMap (fun b => [a &&& b, a ||| b]))

private theorem readMem (wires : List TruthTable) (i : ℕ) : wires.getD i 0 ∈ 0 :: wires := by
  by_cases hi : i < wires.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact List.mem_cons_of_mem _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt hi)]
    exact List.mem_cons_self

private theorem gateMem (wires : List TruthTable) (g : Gate)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hlen : g.inputs.length ≤ 2) :
    gateTable wires g ∈ nextTables (0 :: wires) := by
  obtain ⟨op, inputs⟩ := g
  have existing (t : TruthTable) (ht : t ∈ 0 :: wires) :
      t ∈ nextTables (0 :: wires) := List.mem_append_left _ (List.mem_append_left _ ht)
  have full : (255 : TruthTable) ∈ nextTables (0 :: wires) :=
    List.mem_append_left _ (List.mem_append_right _ List.mem_cons_self)
  have binary (i j : ℕ) {t : TruthTable}
      (ht : t ∈ [wires.getD i 0 &&& wires.getD j 0, wires.getD i 0 ||| wires.getD j 0]) :
      t ∈ nextTables (0 :: wires) :=
    List.mem_append_right _ (List.mem_flatMap_of_mem (readMem wires i)
      (List.mem_flatMap_of_mem (readMem wires j) ht))
  cases op with
  | and =>
    match inputs, hlen with
    | [], _ => exact full
    | [i], _ => exact existing _ (readMem wires i)
    | [i, j], _ => exact binary i j List.mem_cons_self
    | _ :: _ :: _ :: _, h => simp at h
  | or =>
    match inputs, hlen with
    | [], _ => exact existing _ List.mem_cons_self
    | [i], _ => exact existing _ (readMem wires i)
    | [i, j], _ => exact binary i j (List.mem_cons_of_mem _ List.mem_cons_self)
    | _ :: _ :: _ :: _, h => simp at h
  | not =>
    cases inputs with
    | nil => exact full
    | cons i _ =>
      exact List.mem_append_left _ (List.mem_append_right _
        (List.mem_cons_of_mem _ (List.mem_map_of_mem (readMem wires i))))
  | mod m => simp at hop
  | maj => simp at hop

private theorem atMostOne (gates : List Gate) (wires : List TruthTable) (out : ℕ)
    (ok : FanInTwo ⟨gates, out⟩) (hsize : gates.length ≤ 1) :
    (wireTables gates wires).getD out 0 ∈ nextTables (0 :: wires) := by
  match gates, hsize with
  | [], _ => exact List.mem_append_left _ (List.mem_append_left _ (readMem wires out))
  | [g], _ =>
    have hg := ok g List.mem_cons_self
    have hm := readMem (wires ++ [gateTable wires g]) out
    change (wires ++ [gateTable wires g]).getD out 0 ∈ nextTables (0 :: wires)
    rw [← List.cons_append, List.mem_append, List.mem_singleton] at hm
    rcases hm with hm | hm
    · exact List.mem_append_left _ (List.mem_append_left _ hm)
    · rw [hm]
      exact gateMem wires g hg.1 hg.2
  | _ :: _ :: _, h => simp at h

private def twoGateTables : List TruthTable :=
  (nextTables (0 :: inputTables)).flatMap fun a => nextTables (0 :: (inputTables ++ [a]))

private theorem atMostTwo (c : Circuit) (ok : FanInTwo c) (hsize : c.size ≤ 2) :
    (wireTables c.gates inputTables).getD c.output 0 ∈ twoGateTables := by
  obtain ⟨gates, out⟩ := c
  cases gates with
  | nil =>
    apply List.mem_flatMap_of_mem (a := (0 : TruthTable))
    · exact List.mem_append_left _ (List.mem_append_left _ List.mem_cons_self)
    · exact List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_left _ (readMem inputTables out)))
  | cons g gs =>
    have hg := ok g List.mem_cons_self
    apply List.mem_flatMap_of_mem (gateMem inputTables g hg.1 hg.2)
    exact atMostOne gs (inputTables ++ [gateTable inputTables g]) out
      (fun g' hg' => ok g' (List.mem_cons_of_mem _ hg'))
      (by simpa [Circuit.size] using hsize)

-- The target table is 10001111 in binary, with row zero at the least significant bit.
private theorem targetAbsent : twoGateTables.contains (143 : TruthTable) = false := by
  rw [twoGateTables, List.contains_flatMap]
  decide

private theorem lowerBound (c : Circuit) (ok : FanInTwo c)
    (eval : ∀ x : Fin 3 → Bool, c.eval (List.ofFn x) = ((x 0 && x 1) || !x 2)) :
    3 ≤ c.size := by
  by_contra! small
  let out := (wireTables c.gates inputTables).getD c.output 0
  have tableEq : out = (143 : TruthTable) := by
    apply BitVec.eq_of_getLsbD_eq
    intro row hrow
    let x : Fin 3 → Bool := fun j => row.testBit j
    have inputs : List.ofFn x = inputTables.map (fun t => t.getLsbD row) := by
      dsimp only [x]
      interval_cases row <;> rfl
    have target : (143 : TruthTable).getLsbD row = ((x 0 && x 1) || !x 2) := by
      dsimp only [x]
      interval_cases row <;> rfl
    have hw := wireRows c.gates inputTables row hrow (fun g hg => ok g hg)
    change c.wires _ = _ at hw
    have h := eval x
    rw [Circuit.eval, inputs, hw, readRow] at h
    exact h.trans target.symm
  have hm := atMostTwo c ok (by omega)
  change out ∈ twoGateTables at hm
  rw [tableEq, ← List.contains_iff_mem, targetAbsent] at hm
  contradiction

theorem L_meta_140 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 3
      (fun x : Fin 3 → Bool => (x 0 && x 1) || !x 2) s ↔ 3 ≤ s := by
  intro s
  constructor
  · rintro ⟨c, ok, size, eval⟩
    exact (lowerBound c ok eval).trans size
  · intro hs
    refine ⟨⟨[⟨.and, [0, 1]⟩, ⟨.not, [2]⟩, ⟨.or, [3, 4]⟩], 5⟩, ?_, hs, ?_⟩
    · simp [FanInTwo]
    · intro x
      rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_zero]
      change Circuit.eval _ [x 0, x 1, x 2] = ((x 0 && x 1) || !x 2)
      cases x 0 <;> cases x 1 <;> cases x 2 <;> rfl

end PEqualNP.Outside
