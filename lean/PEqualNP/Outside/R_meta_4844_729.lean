import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Pack the 51 test masks at both switch settings into 102-bit truth tables.
-- The distinguished OR copies the companion on low rows and sets every high row.
set_option maxRecDepth 12000 in
set_option maxHeartbeats 5000000 in
theorem PEqualNP.Outside.R_meta_4844_729
    (encode : let read := fun g : Gate => (if g.op.eval [false,false] then g.inputs.take 1 else g.inputs).any (fun i => decide (i = 6))
    ∀ gs : List Gate, FanInTwo ⟨gs,0⟩ → (∀ g ∈ gs, read g = false) →
    ∃ ds : List (Fin 3 × Fin 25 × Fin 25), ds.length = gs.length ∧
    ∀ a b : List Bool, a.length = b.length → 7 ≤ a.length → a.length + gs.length ≤ 24 →
    (∀ i : ℕ, i ≠ 6 → a.getD i false = b.getD i false) →
    ∀ i : ℕ, i ≠ 6 → ((Circuit.mk (ds.map (fun t : Fin 3 × Fin 25 × Fin 25 => Gate.mk (if t.1 = 0 then .and else if t.1 = 1 then .or else .not) [t.2.1.val,t.2.2.val])) 0).wires a).getD i false =
      ((Circuit.mk gs 0).wires b).getD i false)
    (mirror : ∀ (ds : List (Fin 3 × Fin 25 × Fin 25)) (a : List (BitVec 102)) (r : Fin 102),
    (ds.foldl (fun (w : List (BitVec 102)) (t : Fin 3 × Fin 25 × Fin 25) =>
      let a := w.getD t.2.1.val 0
      let b := w.getD t.2.2.val 0
      w ++ [if t.1 = 0 then a &&& b else if t.1 = 1 then a ||| b else ~~~a]) a).map (fun z => z.getLsbD r.val) =
      (Circuit.mk (ds.map (fun t : Fin 3 × Fin 25 × Fin 25 => Gate.mk (if t.1 = 0 then .and else if t.1 = 1 then .or else .not) [t.2.1.val,t.2.2.val])) 0).wires (a.map (fun z => z.getLsbD r.val)))
    (exclude : let push := fun (w : List (BitVec 102)) (t : Fin 3 × Fin 25 × Fin 25) =>
      let a := w.getD t.2.1.val 0
      let b := w.getD t.2.2.val 0
      w ++ [if t.1 = 0 then a &&& b else if t.1 = 1 then a ||| b else ~~~a]
    let roots : List (BitVec 102) := [3807924113928701241014931235404, 3192193433883754486416663646506, 2614568313340011229683174733824, 5069364460873634476961971568640, 2694918396208125717450334273536, 2565014261931813280899048424560, 0, 4754927388663692843842189393920, 2575877766341616094106074843008, 5070602400912917045245010059852]
    ∀ (p s : List (Fin 3 × Fin 25 × Fin 25)) (j o : Fin 25), p.length + s.length ≤ 13 →
      let w := p.foldl push roots
      let c := w.getD j.val 0
      (∀ i ∈ ([9, 16, 33] : List ℕ), c.getLsbD i = false) →
      (s.foldl push (w ++ [c ||| 5070602400912915354186999136256])).getD o.val 0 ≠ 3469866931654064111730941236296)
    : have x1 : PEqualNP.CircuitLowerBounds.Gate → Bool := fun (x1 : PEqualNP.CircuitLowerBounds.Gate) => (if x1.op.eval [Bool.false, Bool.false] = Bool.true then List.take (1 : ℕ) x1.inputs else x1.inputs).any fun (x2 : ℕ) => Decidable.decide (x2 = (6 : ℕ)); have x2 : Bool → (Fin (8 : ℕ) → Bool) → List Bool := fun (x2 : Bool) (x3 : Fin (8 : ℕ) → Bool) => [x3 (1 : Fin (8 : ℕ)), x3 (0 : Fin (8 : ℕ)), x3 (4 : Fin (8 : ℕ)), x3 (7 : Fin (8 : ℕ)), x3 (5 : Fin (8 : ℕ)), x3 (2 : Fin (8 : ℕ)), x2, x3 (6 : Fin (8 : ℕ)), x3 (3 : Fin (8 : ℕ)), x3 (1 : Fin (8 : ℕ)) || x2]; have x3 : ℕ → Bool := fun (x3 : ℕ) => ([(18369897887404062920 : ℕ), (18446740762289764600 : ℕ), (18446744073709551560 : ℕ), (18446744073709551608 : ℕ)].getD (x3 / (64 : ℕ)) (0 : ℕ)).testBit (x3 % (64 : ℕ)); have x4 : ℕ → Fin (8 : ℕ) → Bool := fun (x4 : ℕ) (x5 : Fin (8 : ℕ)) => x4.testBit ↑x5; ∀ (x5 x6 : List PEqualNP.CircuitLowerBounds.Gate) (x7 : PEqualNP.CircuitLowerBounds.Gate) (x8 : ℕ),   have x9 : PEqualNP.CircuitLowerBounds.Circuit := { gates := x5 ++ x7 :: x6, output := x8 : PEqualNP.CircuitLowerBounds.Circuit };   PEqualNP.MetaComplexity.FanInTwo x9 → x5.length + x6.length ≤ (13 : ℕ) → (∀ x12 ∈ x5 ++ x6, x1 x12 = Bool.false) → x1 x7 = Bool.true → x7.op = PEqualNP.CircuitLowerBounds.GateOp.or → (∀ x15 < (256 : ℕ), List.count Bool.true (List.ofFn (x4 x15)) ≤ (2 : ℕ) ∨ x3 x15 = Bool.false ∨ x15 = (255 : ℕ) → x9.eval (x2 Bool.false (x4 x15)) = x3 x15 ∧ x9.eval (x2 Bool.true (x4 x15)) = (x3 x15 || x4 x15 (0 : Fin (8 : ℕ)) || x4 x15 (3 : Fin (8 : ℕ)))) → (∀ x16 ∈ [(10 : ℕ), (26 : ℕ), (74 : ℕ)], x7.op.eval (List.map (fun (x18 : ℕ) => ({ gates := x5, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (x2 Bool.false (x4 x16))).getD x18 Bool.false) x7.inputs) = Bool.false) → False := by
  let read := fun g : Gate => (if g.op.eval [false,false] then g.inputs.take 1 else g.inputs).any (fun i => decide (i = 6))
  let decode := fun t : Fin 3 × Fin 25 × Fin 25 => Gate.mk (if t.1 = 0 then .and else if t.1 = 1 then .or else .not) [t.2.1.val,t.2.2.val]
  let push := fun (w : List (BitVec 102)) (t : Fin 3 × Fin 25 × Fin 25) =>
      let a := w.getD t.2.1.val 0
      let b := w.getD t.2.2.val 0
      w ++ [if t.1 = 0 then a &&& b else if t.1 = 1 then a ||| b else ~~~a]
  let roots : List (BitVec 102) := [3807924113928701241014931235404, 3192193433883754486416663646506, 2614568313340011229683174733824, 5069364460873634476961971568640, 2694918396208125717450334273536, 2565014261931813280899048424560, 0, 4754927388663692843842189393920, 2575877766341616094106074843008, 5070602400912917045245010059852]
  let high : BitVec 102 := 5070602400912915354186999136256
  let goal : BitVec 102 := 3469866931654064111730941236296
  let rows : List ℕ := [0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 16, 17, 18, 20, 24, 26, 32, 33, 34, 36, 37, 40, 41, 48, 52, 56, 64, 65, 66, 68, 72, 73, 74, 80, 96, 97, 104, 105, 128, 129, 130, 132, 133, 136, 144, 160, 192, 193, 194, 255]
  let bit := fun (r : Fin 102) (z : BitVec 102) => z.getLsbD r.val
  let mask := fun r : Fin 102 => rows.getD (r.val % 51) 0
  let mode := fun r : Fin 102 => bit r high
  let step := fun (w : List Bool) (g : Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let cut := fun i : ℕ => (⟨min i 24, by omega⟩ : Fin 25)
  have evalOr (l : List Bool) : GateOp.or.eval l = l.any id := rfl
  have cutEq {α : Type} (w : List α) (d : α) (hw : w.length ≤ 24) (i : ℕ) :
      w.getD (cut i).val d = w.getD i d := by
    change w.getD (min i 24) d = _
    by_cases hi : i ≤ 24
    · rw [min_eq_left hi]
    · rw [min_eq_right (by omega),List.getD_eq_default _ _ hw,List.getD_eq_default _ _ (by omega)]
  have keep (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl step w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      change (gs.foldl step (step w g)).getD i false = _
      rw [ih (step w g) (by simp [step]; omega), List.getD_append _ _ _ _ hi]
  have ordinaryLen (gs : List Gate) (a : List Bool) :
      (gs.foldl step a).length = a.length + gs.length := by
    induction gs generalizing a with
    | nil => simp
    | cons g gs ih => rw [List.foldl_cons,ih]; simp only [step,List.length_append,List.length_cons,List.length_nil]; omega
  have packedLen (ds : List (Fin 3 × Fin 25 × Fin 25)) (w : List (BitVec 102)) :
      (ds.foldl push w).length = w.length + ds.length := by
    induction ds generalizing w with
    | nil => simp
    | cons d ds ih => rw [List.foldl_cons,ih]; simp only [push,List.length_append,List.length_cons,List.length_nil]; omega
  have readAppend (w : List Bool) (b : Bool) (i : ℕ) :
      (w ++ [b]).getD i false = if i = w.length then b else w.getD i false := by
    by_cases eq : i = w.length
    · subst i; simp [List.getD]
    · rw [ite_eq_right eq]
      by_cases lt : i < w.length
      · exact List.getD_append _ _ _ _ lt
      · rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by omega)]
  have atBit (r : Fin 102) (w : List (BitVec 102)) (i : ℕ) :
      (w.map (bit r)).getD i false = bit r (w.getD i 0) := by
    have hz : bit r (0 : BitVec 102) = false := by simp [bit]
    simpa only [hz] using List.getD_map w (0 : BitVec 102) (n := i) (bit r)
  intro raw I H x pre post g o D fan limit nr hit op tests trace
  have preFan : FanInTwo ⟨pre,0⟩ := fun z hz => fan z (List.mem_append_left _ hz)
  have postFan : FanInTwo ⟨post,0⟩ :=
    fun z hz => fan z (List.mem_append_right _ (List.mem_cons_of_mem _ hz))
  obtain ⟨p,plen,ep⟩ := encode pre preFan (fun z hz => nr z (List.mem_append_left _ hz))
  obtain ⟨s,slen,es⟩ := encode post postFan (fun z hz => nr z (List.mem_append_right _ hz))
  have fanG := fan g (by simp [D])
  have has6 : 6 ∈ g.inputs := by
    change (read g) = true at hit
    simp [read,op,evalOr] at hit
    exact hit
  have companion : ∃ j : ℕ, j ≠ 6 ∧ ∀ w : List Bool, w.length ≤ 24 →
      g.op.eval (g.inputs.map fun i => w.getD i false) = (w.getD 6 false || w.getD j false) := by
    rcases e : g.inputs with _ | ⟨i,_ | ⟨j,_ | ⟨k,rest⟩⟩⟩
    · simp [e] at has6
    · have eq : 6 = i := by simpa [e] using has6
      subst i
      exact ⟨24,by decide,fun w h => by simp [-List.getD_eq_getElem?_getD,op,evalOr,List.getD_eq_default w false h]⟩
    · have eq : 6 = i ∨ 6 = j := by simpa [e] using has6
      rcases eq with rfl | rfl
      · by_cases duplicate : j = 6
        · subst j
          exact ⟨24,by decide,fun w h => by simp [-List.getD_eq_getElem?_getD,op,evalOr,List.getD_eq_default w false h]⟩
        · exact ⟨j,duplicate,fun w _ => by simp [op,evalOr]⟩
      · by_cases duplicate : i = 6
        · subst i
          exact ⟨24,by decide,fun w h => by simp [-List.getD_eq_getElem?_getD,op,evalOr,List.getD_eq_default w false h]⟩
        · exact ⟨i,duplicate,fun w _ => by simp [op,evalOr,Bool.or_comm]⟩
    · have h := fanG.2; simp [e] at h
  obtain ⟨j,j6,comp⟩ := companion
  let A := fun r : Fin 102 => I (mode r) (x (mask r))
  let V := fun r : Fin 102 => pre.foldl step (A r)
  let G := fun r : Fin 102 => g.op.eval (g.inputs.map fun i => (V r).getD i false)
  let P := p.foldl push roots
  let c := P.getD (cut j).val 0
  let Z := P ++ [c ||| high]
  let S := s.foldl push Z
  have lenR : roots.length = 10 := rfl
  have lenA (r : Fin 102) : (A r).length = 10 := rfl
  have lenV (r : Fin 102) : (V r).length = 10 + pre.length := by simp [V,ordinaryLen,lenA]
  have lenP : P.length = 10 + pre.length := by simp [P,packedLen,plen,lenR]
  have lenZ : Z.length = 11 + pre.length := by simp [Z,lenP]; omega
  have lenS : S.length ≤ 24 := by simp [S,packedLen,lenZ,slen]; omega
  have rawTable : ∀ (r : Fin 102) (i : Fin 10), i.val ≠ 6 →
      (roots.map (bit r)).getD i.val false = (A r).getD i.val false := by decide +kernel
  have off (r : Fin 102) (i : ℕ) (hi : i ≠ 6) :
      (roots.map (bit r)).getD i false = (A r).getD i false := by
    by_cases lt : i < 10
    · exact rawTable r ⟨i,lt⟩ hi
    · rw [List.getD_eq_default _ _ (by simp [lenR]; omega), List.getD_eq_default _ _ (by rw [lenA]; omega)]
  have before (r : Fin 102) (i : ℕ) (hi : i ≠ 6) :
      bit r (P.getD i 0) = (V r).getD i false := by
    rw [← atBit]
    change ((p.foldl push roots).map (bit r)).getD i false = _
    rw [mirror p roots r]
    exact ep (roots.map (bit r)) (A r) (by simp [lenR,lenA]) (by simp [lenR])
      (by simp [lenR]; omega) (off r) i hi
  have bitG (r : Fin 102) : bit r (c ||| high) = G r := by
    have h6 : (V r).getD 6 false = mode r := keep pre (A r) 6 (by rw [lenA]; decide)
    change _ = g.op.eval (g.inputs.map _)
    rw [comp _ (by rw [lenV]; omega), h6]
    change ((P.getD (cut j).val 0 ||| high).getLsbD r.val) = _
    rw [BitVec.getLsbD_or,cutEq P 0 (by omega)]
    rw [show (P.getD j 0).getLsbD r.val = _ from before r j j6]
    exact Bool.or_comm _ _
  have nextOff (r : Fin 102) (i : ℕ) (hi : i ≠ 6) :
      (Z.map (bit r)).getD i false = (V r ++ [G r]).getD i false := by
    simp only [Z,List.map_append,List.map_singleton,readAppend,List.length_map,lenP,lenV,bitG r,atBit,before r i hi]
  have o6 : o ≠ 6 := by
    intro eq
    obtain ⟨h,_⟩ := tests 3 (by decide) (by decide +kernel)
    change ((pre ++ g :: post).foldl step (I false (x 3))).getD o false = H 3 at h
    rw [eq,keep _ _ _ (by decide +kernel)] at h
    exact (by decide +kernel : (I false (x 3)).getD 6 false ≠ H 3) h
  have bound : ∀ r : Fin 102, mask r < 256 := by decide +kernel
  have subset : ∀ r : Fin 102, (List.ofFn (x (mask r))).count true ≤ 2 ∨ H (mask r) = false ∨ mask r = 255 := by decide +kernel
  have expected : ∀ r : Fin 102, bit r goal =
      (if mode r then H (mask r) || x (mask r) 0 || x (mask r) 3 else H (mask r)) := by decide +kernel
  have agrees (r : Fin 102) : D.eval (A r) = bit r goal := by
    obtain ⟨lo,hi⟩ := tests (mask r) (bound r) (subset r)
    rw [expected]
    cases e : mode r <;> simpa only [A,e,ite_false,ite_true,Bool.false_eq_true] using (by first | exact lo | exact hi)
  apply exclude p s (cut j) (cut o) (by omega)
  · intro i h
    have val : i = 9 ∨ i = 16 ∨ i = 33 := by simpa using h
    have test (r : Fin 102) (hm : mask r ∈ [10,26,74]) (hb : mode r = false) : bit r c = false := by
      have hG := trace (mask r) hm
      change g.op.eval (g.inputs.map fun i => (pre.foldl step (I false (x (mask r)))).getD i false) = false at hG
      have z : G r = false := by simpa only [G,V,A,hb] using hG
      have h' := (bitG r).trans z
      change (c ||| high).getLsbD r.val = false at h'
      rw [BitVec.getLsbD_or, show high.getLsbD r.val = false from hb, Bool.or_false] at h'
      exact h'
    rcases val with rfl | rfl | rfl
    · exact test 9 (by decide +kernel) (by decide +kernel)
    · exact test 16 (by decide +kernel) (by decide +kernel)
    · exact test 33 (by decide +kernel) (by decide +kernel)
  · change S.getD (cut o).val 0 = goal
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    let r : Fin 102 := ⟨i,hi⟩
    change bit r (S.getD (cut o).val 0) = bit r goal
    rw [cutEq S 0 lenS,← atBit]
    change ((s.foldl push Z).map (bit r)).getD o false = _
    rw [mirror s Z r]
    have e := es (Z.map (bit r)) (V r ++ [G r]) (by simp [lenZ,lenV]; omega)
      (by simp [lenZ]; omega) (by simp [lenZ]; omega) (nextOff r) o o6
    apply e.trans
    change (post.foldl step (V r ++ [G r])).getD o false = bit r goal
    have v := agrees r
    change ((pre ++ g :: post).foldl step (A r)).getD o false = _ at v
    rw [List.foldl_append,List.foldl_cons] at v
    exact v
