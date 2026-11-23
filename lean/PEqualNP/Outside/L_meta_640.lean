import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_640_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private abbrev Table := BitVec 7
private def sample (j : Fin 7) (i : Fin 7) : Bool :=
  decide (i = j)

private def readTable (j : Fin 7) (t : Table) : Bool := t.getLsbD j.val
private theorem read_zero (j : Fin 7) : readTable j 0 = false := BitVec.getLsbD_zero
private theorem read_not (j : Fin 7) (t : Table) : readTable j (~~~t) = !(readTable j t) := by
  simp [readTable, j.isLt]
private def inputs : List Table := [1, 2, 4, 8, 16, 32, 64]
private theorem inputTables (j : Fin 7) : List.ofFn (sample j) = inputs.map (readTable j) := by
  fin_cases j <;> decide
private theorem table_ext (a b : Table) (h : ∀ j, readTable j a = readTable j b) : a = b := by
  apply BitVec.eq_of_getLsbD_eq
  exact fun i hi => h ⟨i,hi⟩

private theorem getD_table (x : Fin 7) (ws : List Table) (i : ℕ) :
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

private theorem read_gateTable (x : Fin 7) (ws : List Table) (g : Gate)
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
    | [i, j], _ => simp [gateTable, GateOp.eval, readTable]
    | _ :: _ :: _ :: _, h => simp at h
  | or =>
    match ins, hlen with
    | [], _ => simp [gateTable, GateOp.eval, readTable]
    | [i], _ => simp [gateTable, GateOp.eval]
    | [i, j], _ => simp [gateTable, GateOp.eval, readTable]
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

private theorem read_wireTables (x : Fin 7) (gs : List Gate) (ws : List Table)
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

private theorem wires_match (C : Circuit) (h : FanInTwo C) (j : Fin 7) (o : ℕ) :
    (C.wires (List.ofFn (sample j))).getD o false =
    readTable j ((wireTables C.gates inputs).getD o 0) := by
  change (Circuit.wires ⟨C.gates, 0⟩ (List.ofFn (sample j))).getD o false = _
  rw [inputTables, read_wireTables j C.gates inputs h, getD_table]

private def target (w : Fin 7) : Table :=
  [7, 25, 97, 42, 82, 76, 52][w.val]!

private def weight (w : Fin 7) (a : Table) : Nat :=
  if ([1329227995784918234087049044867186920, 5071221370932704411313059791360, 10428565347265108857913566633656320, 81129677100233197678978322662400, 20769188765166711696840185878937600, 324523505952506431025504692736000, 83076749736595022173079144124907520] : List Nat)[w.val]!.testBit a.toNat then 2
  else if ([10141360148793691861359230189568, 2658456003949232141543720633216532480, 2866969303500172743601003837406576640, 5318372316631126417074039951433138176, 5690757379391834292916941459371851776, 21269595073591769932580545812775305216, 21766108430977997425753398436750688256] : List Nat)[w.val]!.testBit a.toNat then 1 else 0

private theorem unary : ∀ (w : Fin 7) (a : Table), ~~~a = target w → weight w a = 2 := by
  decide +kernel

private theorem own : ∀ w, weight w (target w) = 2 := by decide +kernel
private theorem zeroWt : ∀ w, weight w 0 = 0 := by decide +kernel
private theorem nonzero : ∀ w, (target w ≠ 0 ∧ target w ≠ ~~~(0 : Table)) := by decide +kernel
private theorem cap : ∀ a : Table, (∑ w : Fin 7, weight w a) ≤ 2 := by decide +kernel

set_option maxHeartbeats 8000000 in
private theorem transition : ∀ (w : Fin 7) (a b : Table),
    a ≠ target w → b ≠ target w →
    (a &&& b = target w ∨ a ||| b = target w) → 2 ≤ weight w a + weight w b := by
  decide +kernel

private def total (w : Fin 7) (ws : List Table) := (ws.map (weight w)).sum

private theorem oneBound (w : Fin 7) (a : Table) (ws : List Table) (h : a ∈ ws) :
    weight w a ≤ total w ws := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with rfl | h
    · simp [total]
    · have := ih h
      change _ ≤ weight w x + total w xs
      omega

private theorem twoBound (w : Fin 7) (a b : Table) (hn : a ≠ b) (ws : List Table)
    (ha : a ∈ ws) (hb : b ∈ ws) : weight w a + weight w b ≤ total w ws := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    change _ ≤ weight w x + total w xs
    rcases List.mem_cons.mp ha with rfl | hax
    · have hb' := (List.mem_cons.mp hb).resolve_left (Ne.symm hn)
      have := oneBound w b xs hb'
      omega
    · rcases List.mem_cons.mp hb with rfl | hb
      · have := oneBound w a xs hax
        omega
      · have := ih hax hb
        omega

private theorem readMem (ws : List Table) (i : Nat) : ws.getD i 0 ∈ 0 :: ws := by
  by_cases h : i < ws.length
  · simp [List.getD_eq_getElem?_getD, h, List.getElem_mem]
  · exact List.mem_cons.mpr (Or.inl (List.getD_eq_default ws 0 (Nat.le_of_not_gt h)))

private theorem twoInputs (w : Fin 7) (ws : List Table) (hn : target w ∉ ws) (i j : Nat)
    (h : ws.getD i 0 &&& ws.getD j 0 = target w ∨ ws.getD i 0 ||| ws.getD j 0 = target w) :
    2 ≤ total w ws := by
  let a := ws.getD i 0
  let b := ws.getD j 0
  have ha : a ∈ 0 :: ws := readMem _ _
  have hb : b ∈ 0 :: ws := readMem _ _
  have ht : target w ∉ 0 :: ws := fun h => (List.mem_cons.mp h).elim (nonzero w).1 hn
  have hna : a ≠ target w := fun e => ht (e ▸ ha)
  have hnb : b ≠ target w := fun e => ht (e ▸ hb)
  change a &&& b = target w ∨ a ||| b = target w at h
  have hab : a ≠ b := by
    intro e
    rw [← e] at h
    simp [hna] at h
  have h1 := transition w a b hna hnb h
  have h2 := twoBound w a b hab (0 :: ws) ha hb
  change _ ≤ weight w 0 + total w ws at h2
  rw [zeroWt] at h2
  omega

private abbrev Good (g : Gate) :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

private theorem unaryInput (w : Fin 7) (ws : List Table) (i : Nat)
    (he : ~~~(ws.getD i 0) = target w) : 2 ≤ total w ws := by
  have h := oneBound w _ (0 :: ws) (readMem ws i)
  change weight w (ws.getD i 0) ≤ weight w 0 + total w ws at h
  simpa only [unary w _ he, zeroWt, Nat.zero_add] using h

private theorem newTarget (w : Fin 7) (ws : List Table) (g : Gate) (hg : Good g)
    (hn : target w ∉ ws) (he : gateTable ws g = target w) : 2 ≤ total w ws := by
  have ht : target w ∉ 0 :: ws := fun h => (List.mem_cons.mp h).elim (nonzero w).1 hn
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  change op = _ ∨ op = _ ∨ op = _ at hop
  change ins.length ≤ 2 at hlen
  match ins, hlen with
  | [], _ =>
    rcases hop with rfl | rfl | rfl
    · exact False.elim ((nonzero w).2 he.symm)
    · exact False.elim ((nonzero w).1 he.symm)
    · exact False.elim ((nonzero w).2 he.symm)
  | [i], _ =>
    rcases hop with rfl | rfl | rfl
    · exact False.elim (ht (he ▸ readMem ws i))
    · exact False.elim (ht (he ▸ readMem ws i))
    · exact unaryInput w ws i he
  | [i, j], _ =>
    rcases hop with rfl | rfl | rfl
    · exact twoInputs w ws hn i j (Or.inl he)
    · exact twoInputs w ws hn i j (Or.inr he)
    · exact unaryInput w ws i he
  | _ :: _ :: _ :: _, h => simp at h

private theorem total_snoc (w : Fin 7) (ws : List Table) (a : Table) :
    total w (ws ++ [a]) = total w ws + weight w a := by simp [total]

-- The first gate to produce a line must read two units already present.
-- Its own two units bring the total for that line to four.
private def Safe (ws : List Table) := ∀ w, target w ∈ ws → 4 ≤ total w ws

private theorem safeStep (ws : List Table) (g : Gate) (hg : Good g) (hs : Safe ws) :
    Safe (ws ++ [gateTable ws g]) := by
  intro w hw
  rw [total_snoc]
  by_cases old : target w ∈ ws
  · have := hs w old
    omega
  · have he : gateTable ws g = target w := by simpa [old, eq_comm] using hw
    have := newTarget w ws g hg old he
    rw [he, own]
    omega

private theorem safeCost (gs : List Gate) (ws : List Table) (hg : ∀ g ∈ gs, Good g)
    (hs : Safe ws) :
    Safe (wireTables gs ws) ∧
    (∑ w, total w (wireTables gs ws)) ≤ (∑ w, total w ws) + 2 * gs.length := by
  induction gs generalizing ws with
  | nil => exact ⟨hs, by simp [wireTables]⟩
  | cons g gs ih =>
    obtain ⟨hs', hc⟩ := ih (ws ++ [gateTable ws g])
      (fun g' h => hg g' (by simp [h])) (safeStep ws g (hg _ (by simp)) hs)
    refine ⟨hs', ?_⟩
    change (∑ w, total w (wireTables gs (ws ++ [gateTable ws g]))) ≤ _
    simp only [total_snoc, Finset.sum_add_distrib] at hc
    have := cap (gateTable ws g)
    rw [List.length_cons]
    omega

private theorem inputSafe : Safe inputs := by
  have h : ∀ w, target w ∉ inputs := by decide +kernel
  exact fun w hw => False.elim (h w hw)

private theorem core (C : Circuit) (hfan : FanInTwo C) (o : Fin 7 → ℕ)
    (ho : ∀ x : Fin 7 → Bool, (C.wires (List.ofFn x)).getD (o 0) false = (x 0 || x 1 || x 2) ∧ (C.wires (List.ofFn x)).getD (o 1) false = (x 0 || x 3 || x 4) ∧ (C.wires (List.ofFn x)).getD (o 2) false = (x 0 || x 5 || x 6) ∧ (C.wires (List.ofFn x)).getD (o 3) false = (x 1 || x 3 || x 5) ∧ (C.wires (List.ofFn x)).getD (o 4) false = (x 1 || x 4 || x 6) ∧ (C.wires (List.ofFn x)).getD (o 5) false = (x 2 || x 3 || x 6) ∧ (C.wires (List.ofFn x)).getD (o 6) false = (x 2 || x 4 || x 5)) : 14 ≤ C.size := by
  obtain ⟨hs, hc⟩ := safeCost C.gates inputs hfan inputSafe
  have hz : (∑ w, total w inputs) = 0 := by decide +kernel
  rw [hz, Nat.zero_add] at hc
  have h4 (w : Fin 7) : 4 ≤ total w (wireTables C.gates inputs) := by
    apply hs
    have he : (wireTables C.gates inputs).getD (o w) 0 = target w := by
      apply table_ext
      intro j
      rw [← wires_match C hfan j (o w)]
      obtain ⟨h0,h1,h2,h3,h4,h5,h6⟩ := ho (sample j)
      fin_cases w
      · change (C.wires (List.ofFn (sample j))).getD (o 0) false = readTable j (target 0)
        rw [h0]
        fin_cases j <;> decide
      · change (C.wires (List.ofFn (sample j))).getD (o 1) false = readTable j (target 1)
        rw [h1]
        fin_cases j <;> decide
      · change (C.wires (List.ofFn (sample j))).getD (o 2) false = readTable j (target 2)
        rw [h2]
        fin_cases j <;> decide
      · change (C.wires (List.ofFn (sample j))).getD (o 3) false = readTable j (target 3)
        rw [h3]
        fin_cases j <;> decide
      · change (C.wires (List.ofFn (sample j))).getD (o 4) false = readTable j (target 4)
        rw [h4]
        fin_cases j <;> decide
      · change (C.wires (List.ofFn (sample j))).getD (o 5) false = readTable j (target 5)
        rw [h5]
        fin_cases j <;> decide
      · change (C.wires (List.ofFn (sample j))).getD (o 6) false = readTable j (target 6)
        rw [h6]
        fin_cases j <;> decide
    have hm := readMem (wireTables C.gates inputs) (o w)
    rw [he] at hm
    exact (List.mem_cons.mp hm).resolve_left (nonzero w).1
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun w _ => h4 w)
  simp at hh
  change 14 ≤ C.gates.length
  omega

private def circuit : Circuit :=
  ⟨[⟨.or,[0,1]⟩,
    ⟨.or,[7,2]⟩,
    ⟨.or,[0,3]⟩,
    ⟨.or,[9,4]⟩,
    ⟨.or,[0,5]⟩,
    ⟨.or,[11,6]⟩,
    ⟨.or,[1,3]⟩,
    ⟨.or,[13,5]⟩,
    ⟨.or,[1,4]⟩,
    ⟨.or,[15,6]⟩,
    ⟨.or,[2,3]⟩,
    ⟨.or,[17,6]⟩,
    ⟨.or,[2,4]⟩,
    ⟨.or,[19,5]⟩], 20⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem circuitValues : ∀ (b0 b1 b2 b3 b4 b5 b6 : Bool),
  (circuit.wires [b0, b1, b2, b3, b4, b5, b6]).getD 8 false = (b0 || b1 || b2) ∧
  (circuit.wires [b0, b1, b2, b3, b4, b5, b6]).getD 10 false = (b0 || b3 || b4) ∧
  (circuit.wires [b0, b1, b2, b3, b4, b5, b6]).getD 12 false = (b0 || b5 || b6) ∧
  (circuit.wires [b0, b1, b2, b3, b4, b5, b6]).getD 14 false = (b1 || b3 || b5) ∧
  (circuit.wires [b0, b1, b2, b3, b4, b5, b6]).getD 16 false = (b1 || b4 || b6) ∧
  (circuit.wires [b0, b1, b2, b3, b4, b5, b6]).getD 18 false = (b2 || b3 || b6) ∧
  (circuit.wires [b0, b1, b2, b3, b4, b5, b6]).getD 20 false = (b2 || b4 || b5) := by decide +kernel

set_option maxRecDepth 4096 in
private theorem upper : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 14 ∧ ∃ o : Fin 7 → ℕ, ∀ x : Fin 7 → Bool, (C.wires (List.ofFn x)).getD (o 0) false = (x 0 || x 1 || x 2) ∧ (C.wires (List.ofFn x)).getD (o 1) false = (x 0 || x 3 || x 4) ∧ (C.wires (List.ofFn x)).getD (o 2) false = (x 0 || x 5 || x 6) ∧ (C.wires (List.ofFn x)).getD (o 3) false = (x 1 || x 3 || x 5) ∧ (C.wires (List.ofFn x)).getD (o 4) false = (x 1 || x 4 || x 6) ∧ (C.wires (List.ofFn x)).getD (o 5) false = (x 2 || x 3 || x 6) ∧ (C.wires (List.ofFn x)).getD (o 6) false = (x 2 || x 4 || x 5)) := by
  refine ⟨circuit, ?_, by decide, fun i => 8 + 2 * i.val, ?_⟩
  · intro g hg
    simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact ⟨Or.inr (Or.inl rfl), by decide⟩
  · intro x
    rw [show List.ofFn x = [x 0,x 1,x 2,x 3,x 4,x 5,x 6] from rfl]
    exact circuitValues (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

end PEqualNP.Outside.L_meta_640_aux

theorem PEqualNP.Outside.L_meta_640 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 14 ∧ ∃ o : Fin 7 → ℕ, ∀ x : Fin 7 → Bool, (C.wires (List.ofFn x)).getD (o 0) false = (x 0 || x 1 || x 2) ∧ (C.wires (List.ofFn x)).getD (o 1) false = (x 0 || x 3 || x 4) ∧ (C.wires (List.ofFn x)).getD (o 2) false = (x 0 || x 5 || x 6) ∧ (C.wires (List.ofFn x)).getD (o 3) false = (x 1 || x 3 || x 5) ∧ (C.wires (List.ofFn x)).getD (o 4) false = (x 1 || x 4 || x 6) ∧ (C.wires (List.ofFn x)).getD (o 5) false = (x 2 || x 3 || x 6) ∧ (C.wires (List.ofFn x)).getD (o 6) false = (x 2 || x 4 || x 5)) ∧ ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 13 ∧ ∃ o : Fin 7 → ℕ, ∀ x : Fin 7 → Bool, (C.wires (List.ofFn x)).getD (o 0) false = (x 0 || x 1 || x 2) ∧ (C.wires (List.ofFn x)).getD (o 1) false = (x 0 || x 3 || x 4) ∧ (C.wires (List.ofFn x)).getD (o 2) false = (x 0 || x 5 || x 6) ∧ (C.wires (List.ofFn x)).getD (o 3) false = (x 1 || x 3 || x 5) ∧ (C.wires (List.ofFn x)).getD (o 4) false = (x 1 || x 4 || x 6) ∧ (C.wires (List.ofFn x)).getD (o 5) false = (x 2 || x 3 || x 6) ∧ (C.wires (List.ofFn x)).getD (o 6) false = (x 2 || x 4 || x 5)) := by
  refine ⟨PEqualNP.Outside.L_meta_640_aux.upper, ?_⟩
  rintro ⟨C, hf, hc, o, ho⟩
  have := PEqualNP.Outside.L_meta_640_aux.core C hf o ho
  omega
