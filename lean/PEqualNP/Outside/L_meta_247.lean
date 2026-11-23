import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.Meta247

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private abbrev Table := BitVec 16

private def inputIndex (x : Fin 4 → Bool) : ℕ :=
  (if x 0 then 1 else 0) + (if x 1 then 2 else 0) +
    (if x 2 then 4 else 0) + (if x 3 then 8 else 0)

private theorem inputIndex_lt (x : Fin 4 → Bool) : inputIndex x < 16 := by
  unfold inputIndex
  split_ifs <;> decide

private def readTable (x : Fin 4 → Bool) (t : Table) : Bool :=
  t.getLsbD (inputIndex x)

private theorem read_zero (x : Fin 4 → Bool) : readTable x 0 = false :=
  BitVec.getLsbD_zero

private theorem read_not (x : Fin 4 → Bool) (t : Table) :
    readTable x (~~~t) = !(readTable x t) := by
  simp only [readTable, BitVec.getLsbD_not, decide_eq_true (inputIndex_lt x), Bool.true_and]

private def inputs : List Table := [0xaaaa, 0xcccc, 0xf0f0, 0xff00]

private def targetFun (x : Fin 4 → Bool) : Bool :=
  (!(x 3)) || (x 2 && (x 0 || x 1))

private theorem inputList (x : Fin 4 → Bool) : List.ofFn x = [x 0, x 1, x 2, x 3] := by
  simp [List.ofFn_succ]

private theorem inputTables (x : Fin 4 → Bool) : List.ofFn x = inputs.map (readTable x) := by
  rw [inputList]
  simp only [inputs, List.map_cons, List.map_nil, readTable, inputIndex]
  cases x 0 <;> cases x 1 <;> cases x 2 <;> cases x 3 <;> decide

private theorem targetTable (x : Fin 4 → Bool) : readTable x 0xe0ff = targetFun x := by
  unfold readTable inputIndex targetFun
  cases x 0 <;> cases x 1 <;> cases x 2 <;> cases x 3 <;> decide

private theorem table_ext (a b : Table) (h : ∀ x, readTable x a = readTable x b) : a = b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  let x : Fin 4 → Bool := fun j => i.testBit j
  have hx : inputIndex x = i := by
    dsimp only [x]
    interval_cases i <;> decide
  simpa only [readTable, hx] using h x

private theorem getD_table (x : Fin 4 → Bool) (ws : List Table) (i : ℕ) :
    (ws.map (readTable x)).getD i false = readTable x (ws.getD i 0) := by
  by_cases hi : i < ws.length
  · simp [List.getD_eq_getElem?_getD, hi]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]
    simp [readTable]

private def gateTable (ws : List Table) (g : Gate) : Table :=
  match g.op, g.inputs with
  | .and, [] => ~~~0
  | .and, [i] => ws.getD i 0
  | .and, i :: j :: _ => ws.getD i 0 &&& ws.getD j 0
  | .or, [] => 0
  | .or, [i] => ws.getD i 0
  | .or, i :: j :: _ => ws.getD i 0 ||| ws.getD j 0
  | .not, [] => ~~~0
  | .not, i :: _ => ~~~(ws.getD i 0)
  | _, _ => 0

private theorem read_gateTable (x : Fin 4 → Bool) (ws : List Table) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    g.op.eval (g.inputs.map fun i => (ws.map (readTable x)).getD i false) =
      readTable x (gateTable ws g) := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  simp only [getD_table]
  cases op with
  | and =>
    match ins, hlen with
    | [], _ =>
      change true = readTable x (~~~0)
      simp only [read_not, read_zero, Bool.not_false]
    | [i], _ => simp [gateTable, GateOp.eval]
    | [i, j], _ => simp [gateTable, GateOp.eval, readTable, BitVec.getLsbD_and]
    | _ :: _ :: _ :: _, h => simp at h
  | or =>
    match ins, hlen with
    | [], _ => simp [gateTable, GateOp.eval, readTable]
    | [i], _ => simp [gateTable, GateOp.eval]
    | [i, j], _ => simp [gateTable, GateOp.eval, readTable, BitVec.getLsbD_or]
    | _ :: _ :: _ :: _, h => simp at h
  | not =>
    cases ins with
    | nil =>
      change true = readTable x (~~~0)
      simp only [read_not, read_zero, Bool.not_false]
    | cons i is =>
      exact (read_not x (ws.getD i 0)).symm
  | mod m => simp at hop
  | maj => simp at hop

private def wireTables (gs : List Gate) (ws : List Table) : List Table :=
  gs.foldl (fun vs g => vs ++ [gateTable vs g]) ws

private theorem read_wireTables (x : Fin 4 → Bool) (gs : List Gate) (ws : List Table)
    (h : FanInTwo ⟨gs, 0⟩) :
    (Circuit.wires ⟨gs, 0⟩ (ws.map (readTable x))) = (wireTables gs ws).map (readTable x) := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g gs ih =>
    have hg := read_gateTable x ws g (h g List.mem_cons_self)
    change Circuit.wires ⟨gs, 0⟩
        (ws.map (readTable x) ++ [g.op.eval (g.inputs.map fun i =>
          (ws.map (readTable x)).getD i false)]) =
      (wireTables gs (ws ++ [gateTable ws g])).map (readTable x)
    rw [hg, ← List.map_singleton, ← List.map_append]
    exact ih _ (fun g' hg' => h g' (List.mem_cons_of_mem _ hg'))

private theorem circuitTable (C : Circuit) (h : FanInTwo C) (x : Fin 4 → Bool) :
    C.eval (List.ofFn x) = readTable x ((wireTables C.gates inputs).getD C.output 0) := by
  unfold Circuit.eval
  change (Circuit.wires ⟨C.gates, 0⟩ (List.ofFn x)).getD C.output false = _
  rw [inputTables, read_wireTables x C.gates inputs h, getD_table]

/-- Applying a binary gate to two different positions of the wire list. -/
private def pairs : List Table → List Table
  | [] => []
  | a :: ws => (ws.flatMap fun b => [a &&& b, a ||| b]) ++ pairs ws

/-- The distinct tables obtainable by one gate, also retaining those already available. -/
private def choices (ws : List Table) : List Table :=
  (ws ++ ws.map (fun a => ~~~a) ++ pairs ws).eraseDups

private theorem getD_available (ws : List Table) (i : ℕ) : ws.getD i 0 ∈ 0 :: ws := by
  by_cases hi : i < ws.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact List.mem_cons_of_mem _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact List.mem_cons_self

private theorem copy_choice (ws : List Table) (a : Table) (ha : a ∈ ws) : a ∈ choices ws := by
  apply List.mem_eraseDups.2
  exact List.mem_append_left _ (List.mem_append_left _ ha)

private theorem not_choice (ws : List Table) (a : Table) (ha : a ∈ ws) :
    ~~~a ∈ choices ws := by
  apply List.mem_eraseDups.2
  exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map.2 ⟨a, ha, rfl⟩))

private theorem pair_available (ws : List Table) (a b : Table) (ha : a ∈ ws) (hb : b ∈ ws) :
    a = b ∨ (a &&& b ∈ pairs ws ∧ a ||| b ∈ pairs ws) := by
  induction ws with
  | nil => simp at ha
  | cons c ws ih =>
    rcases List.mem_cons.1 ha with rfl | ha' <;> rcases List.mem_cons.1 hb with rfl | hb'
    · exact Or.inl rfl
    · exact Or.inr ⟨List.mem_append_left _ (List.mem_flatMap.2 ⟨b, hb', by simp⟩),
        List.mem_append_left _ (List.mem_flatMap.2 ⟨b, hb', by simp⟩)⟩
    · refine Or.inr ⟨List.mem_append_left _ (List.mem_flatMap.2 ⟨a, ha', ?_⟩),
        List.mem_append_left _ (List.mem_flatMap.2 ⟨a, ha', ?_⟩)⟩
      · rw [BitVec.and_comm]; simp
      · rw [BitVec.or_comm]; simp
    · rcases ih ha' hb' with h | ⟨hAnd, hOr⟩
      · exact Or.inl h
      · exact Or.inr ⟨List.mem_append_right _ hAnd, List.mem_append_right _ hOr⟩

private theorem binary_choice (ws : List Table) (a b c : Table) (ha : a ∈ ws) (hb : b ∈ ws)
    (hc : c ∈ [a &&& b, a ||| b]) : c ∈ choices ws := by
  rcases pair_available ws a b ha hb with rfl | ⟨hAnd, hOr⟩
  · have h : c = a := by simpa using hc
    exact h ▸ copy_choice ws a ha
  · apply List.mem_eraseDups.2
    apply List.mem_append_right
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact hAnd
    · exact hOr

private theorem gate_choice (ws : List Table) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    gateTable ws g ∈ choices (0 :: ws) := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  cases op with
  | and =>
    match ins, hlen with
    | [], _ => exact not_choice _ 0 List.mem_cons_self
    | [i], _ => exact copy_choice _ _ (getD_available ws i)
    | [i, j], _ =>
      exact binary_choice _ _ _ _ (getD_available ws i) (getD_available ws j) (by simp [gateTable])
    | _ :: _ :: _ :: _, h => simp at h
  | or =>
    match ins, hlen with
    | [], _ => exact copy_choice _ 0 List.mem_cons_self
    | [i], _ => exact copy_choice _ _ (getD_available ws i)
    | [i, j], _ =>
      exact binary_choice _ _ _ _ (getD_available ws i) (getD_available ws j) (by simp [gateTable])
    | _ :: _ :: _ :: _, h => simp at h
  | not =>
    cases ins with
    | nil => exact not_choice _ 0 List.mem_cons_self
    | cons i _ => exact not_choice _ _ (getD_available ws i)
  | mod m => simp at hop
  | maj => simp at hop

private def reachable (target : Table) : ℕ → List Table → Bool
  | 0, ws => (0 :: ws).contains target
  | 1, ws => (choices (0 :: ws)).contains target
  | fuel + 2, ws =>
      (choices (0 :: ws)).any (fun c => reachable target (fuel + 1) (ws ++ [c]))

private theorem reachable_of_available (target : Table) (fuel : ℕ) (ws : List Table)
    (h : target ∈ 0 :: ws) : reachable target fuel ws = true := by
  induction fuel generalizing ws with
  | zero => exact List.contains_iff_mem.2 h
  | succ n ih =>
    cases n with
    | zero => exact List.contains_iff_mem.2 (copy_choice _ _ h)
    | succ n =>
      exact List.any_eq_true.2 ⟨0, copy_choice _ _ List.mem_cons_self,
        ih (ws ++ [0]) (List.mem_append_left [0] h)⟩

private theorem reachable_of_circuit (gs : List Gate) (ws : List Table) (fuel o : ℕ)
    (h : FanInTwo ⟨gs, o⟩) (hsize : gs.length ≤ fuel) :
    reachable ((wireTables gs ws).getD o 0) fuel ws = true := by
  induction gs generalizing ws fuel with
  | nil => exact reachable_of_available _ _ _ (getD_available ws o)
  | cons g gs ih =>
    let c := gateTable ws g
    have hc : c ∈ choices (0 :: ws) := gate_choice ws g (h g List.mem_cons_self)
    cases fuel with
    | zero => simp at hsize
    | succ n =>
      cases n with
      | zero =>
        have htail : gs.length ≤ 0 := Nat.le_of_succ_le_succ hsize
        obtain rfl : gs = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp htail)
        let t := (ws ++ [c]).getD o 0
        have ht : t ∈ (0 :: ws) ++ [c] := getD_available (ws ++ [c]) o
        change (choices (0 :: ws)).contains t = true
        apply List.contains_iff_mem.2
        rcases List.mem_append.1 ht with ht | ht
        · exact copy_choice _ _ ht
        · rwa [List.mem_singleton.1 ht]
      | succ n =>
        exact List.any_eq_true.2 ⟨c, hc,
          ih (ws ++ [c]) (n + 1) (fun g' hg' => h g' (List.mem_cons_of_mem _ hg')) (by
            simpa using hsize)⟩

private theorem first_choices : choices (0 :: inputs) =
    [0, 0xaaaa, 0xcccc, 0xf0f0, 0xff00, 0xffff, 0x5555, 0x3333, 0x0f0f, 0x00ff,
     0x8888, 0xeeee, 0xa0a0, 0xfafa, 0xaa00, 0xffaa, 0xc0c0, 0xfcfc, 0xcc00, 0xffcc,
     0xf000, 0xfff0] := by decide +kernel

set_option maxHeartbeats 0 in
private theorem search_excludes : reachable 0xe0ff 3 inputs = false := by
  apply Bool.eq_false_iff.2
  intro h
  obtain ⟨c, hc, hreach⟩ := List.any_eq_true.mp h
  rw [first_choices] at hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    change reachable 0xe0ff 2 (inputs ++ [_]) = true at hreach
    exact (Bool.eq_false_iff.mp (show _ = false by decide +kernel)) hreach

private theorem lower : ¬ HasCircuitSize 4 targetFun 3 := by
  rintro ⟨C, hFan, hsize, heval⟩
  have hcode : (wireTables C.gates inputs).getD C.output 0 = (0xe0ff : Table) := by
    apply table_ext
    intro x
    rw [← circuitTable C hFan x, heval x, targetTable]
  have hreach :=
    reachable_of_circuit C.gates inputs 3 C.output hFan (by unfold Circuit.size at hsize; omega)
  rw [hcode, search_excludes] at hreach
  cases hreach

private def upperC : Circuit :=
  ⟨[⟨.not, [3]⟩, ⟨.or, [0, 1]⟩, ⟨.and, [2, 5]⟩, ⟨.or, [4, 6]⟩], 7⟩

private theorem upper : HasCircuitSize 4 targetFun 4 := by
  refine ⟨upperC, ?_, by decide, ?_⟩
  · intro g hg
    simp only [upperC, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl <;> simp
  · intro x
    unfold upperC targetFun
    rw [inputList]
    cases x 0 <;> cases x 1 <;> cases x 2 <;> cases x 3 <;> decide

end PEqualNP.Outside.Meta247

theorem PEqualNP.Outside.L_meta_247 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 4
      (fun x : Fin 4 → Bool => (!(x 3)) || (x 2 && (x 0 || x 1))) s ↔ 4 ≤ s := by
  intro s
  constructor
  · intro h
    by_contra hs
    obtain ⟨C, ok, hsz, hev⟩ := h
    exact PEqualNP.Outside.Meta247.lower ⟨C, ok, by omega, hev⟩
  · intro hs
    obtain ⟨C, ok, hsz, hev⟩ := PEqualNP.Outside.Meta247.upper
    exact ⟨C, ok, by omega, hev⟩
