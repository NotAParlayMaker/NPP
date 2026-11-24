import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The bit-trace evaluator follows R_meta_3202_726.
set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
theorem PEqualNP.Outside.R_meta_3198_719
    (pinsRead :
        ∀ C : Circuit,
      FanInTwo C →
      (∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 || x 2]) =
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
         x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
         x 6 && x 8 || x 8 && x 5)) →
      ∀ i : Fin 9, ∃ g ∈ C.gates,
        i.val ∈ (if g.op.eval [false, false] then g.inputs.take 1 else g.inputs))
    (early :
      let initial : List (BitVec 61) :=
        [1443720478568556842, 1729947681076298316, 1174314188565220464,
          1157463606481260416, 1756478660170477568, 1188959157915222016,
          1225102312599453696, 2161868489906716672, 2305702271725338624, 1462861361639435642]
      let step := fun (ws : List (BitVec 61)) (g : Fin 3 × List (Fin 25)) =>
        let args := g.2.map fun i => ws.getD i.val 0
        ws ++ [if g.1 = 0 then args.foldr (· &&& ·) (~~~0)
          else if g.1 = 1 then args.foldr (· ||| ·) 0 else ~~~(args.headD 0)]
      ∀ (gs : List (Fin 3 × List (Fin 25))) (out : Fin 25),
        gs.length ≤ 14 →
        (∀ g ∈ gs, g.2.length ≤ 2) →
        (∀ i : Fin 25, i.val < 9 → ∃ g ∈ gs,
          i ∈ (if g.1 = 2 then g.2.take 1 else g.2)) →
        (∃ (i j : Fin gs.length), i.val = 4 ∧ i < j ∧ j.val < 9 ∧
          (gs.get i).1 = 2 ∧ (gs.get j).1 = 2 ∧
          ∀ k : Fin gs.length, (gs.get k).1 = 2 → k = i ∨ k = j) →
        (gs.foldl step initial).getD out.val 0 ≠ 1265520841409113160)
    (late :
      let initial : List (BitVec 61) :=
        [1443720478568556842, 1729947681076298316, 1174314188565220464,
          1157463606481260416, 1756478660170477568, 1188959157915222016,
          1225102312599453696, 2161868489906716672, 2305702271725338624, 1462861361639435642]
      let step := fun (ws : List (BitVec 61)) (g : Fin 3 × List (Fin 25)) =>
        let args := g.2.map fun i => ws.getD i.val 0
        ws ++ [if g.1 = 0 then args.foldr (· &&& ·) (~~~0)
          else if g.1 = 1 then args.foldr (· ||| ·) 0 else ~~~(args.headD 0)]
      ∀ (gs : List (Fin 3 × List (Fin 25))) (out : Fin 25),
        gs.length ≤ 14 →
        (∀ g ∈ gs, g.2.length ≤ 2) →
        (∀ i : Fin 25, i.val < 9 → ∃ g ∈ gs,
          i ∈ (if g.1 = 2 then g.2.take 1 else g.2)) →
        (∃ (i j : Fin gs.length), i.val = 4 ∧ i < j ∧ 9 ≤ j.val ∧
          (gs.get i).1 = 2 ∧ (gs.get j).1 = 2 ∧
          ∀ k : Fin gs.length, (gs.get k).1 = 2 → k = i ∨ k = j) →
        (gs.foldl step initial).getD out.val 0 ≠ 1265520841409113160) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∃ (x3 : Fin x1.gates.length) (x4 : Fin x1.gates.length), x3 < x4 ∧ ↑x3 = (5 : ℕ) ∧ (x1.gates.get x3).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ ∀ (x5 : Fin x1.gates.length), (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.not → x5 = x3 ∨ x5 = x4) → (∀ (x4 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x4)).getD (9 : ℕ) Bool.false = (x4 (0 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x5 : Fin (9 : ℕ) → Bool) => x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ))) → (16 : ℕ) ≤ x1.size := by
  intro C fan neg first result
  by_contra! small
  have hSize : C.gates.length ≤ 15 := by
    change C.gates.length < 16 at small
    omega
  obtain ⟨i, j, hij, hi, hni, hnj, all⟩ := neg
  have hne : C.gates ≠ [] := by
    intro h
    have hi' := i.isLt
    simp [h] at hi'
  obtain ⟨g0, rest, hRest⟩ := List.exists_cons_of_ne_nil hne
  let suffix : Circuit := ⟨rest, C.output⟩
  have lengthRest : rest.length + 1 = C.gates.length := by rw [hRest]; rfl
  have sizeRest : rest.length ≤ 14 := by omega
  have memRest {g : Gate} (h : g ∈ rest) : g ∈ C.gates := by
    rw [hRest]
    exact List.mem_cons_of_mem _ h
  have fanRest : FanInTwo suffix := fun g hg => fan g (memRest hg)
  let scalar (bs : List Bool) (g : Gate) :=
    bs ++ [g.op.eval (g.inputs.map (fun j => bs.getD j false))]
  let bank (x : Fin 9 → Bool) := List.ofFn x ++ [x 0 || x 2]
  have keepPin (l : List Gate) (v : List Bool) (k : ℕ) (inside : k < v.length) :
      (l.foldl scalar v).getD k false = v.getD k false := by
    induction l generalizing v with
    | nil => rfl
    | cons g gs ih =>
      change (gs.foldl scalar (scalar v g)).getD k false = _
      rw [ih _ (by simp [scalar]; omega)]
      exact List.getD_append _ _ _ _ inside
  have headBank (x : Fin 9 → Bool) : scalar (List.ofFn x) g0 = bank x := by
    have atHead : (scalar (List.ofFn x) g0).getD 9 false = (x 0 || x 2) := calc
      _ = (rest.foldl scalar (scalar (List.ofFn x) g0)).getD 9 false :=
        (keepPin _ _ _ (by simp [scalar])).symm
      _ = (C.wires (List.ofFn x)).getD 9 false := by
        change _ = (C.gates.foldl scalar (List.ofFn x)).getD 9 false
        rw [hRest]
        rfl
      _ = _ := first x
    have atNew : (scalar (List.ofFn x) g0).getD 9 false =
        g0.op.eval (g0.inputs.map (fun k => (List.ofFn x).getD k false)) := by
      change (List.ofFn x ++ [_]).getD 9 false = _
      rw [List.getD_append_right _ _ _ _ (by simp), List.length_ofFn]
      rfl
    change List.ofFn x ++ [g0.op.eval (g0.inputs.map (fun k => (List.ofFn x).getD k false))] =
      List.ofFn x ++ [x 0 || x 2]
    rw [← atNew, atHead]
  have wiresSuffix (x : Fin 9 → Bool) : suffix.wires (bank x) = C.wires (List.ofFn x) := by
    change rest.foldl scalar (bank x) = C.gates.foldl scalar (List.ofFn x)
    rw [hRest, ← headBank x]
    rfl
  let target (x : Fin 9 → Bool) :=
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
    x 6 && x 8 || x 8 && x 5
  have resultSuffix (x : Fin 9 → Bool) : suffix.eval (bank x) = target x := by
    change (suffix.wires (bank x)).getD C.output false = target x
    rw [wiresSuffix x]
    exact congrFun result x
  let initial : List (BitVec 61) :=
    [1443720478568556842, 1729947681076298316, 1174314188565220464,
      1157463606481260416, 1756478660170477568, 1188959157915222016,
      1225102312599453696, 2161868489906716672, 2305702271725338624, 1462861361639435642]
  let rows : List ℕ :=
    [0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 13, 16, 17, 18, 20, 21, 24,
      32, 33, 34, 36, 40, 42, 48, 50, 64, 65, 66, 68, 69, 72, 80, 96, 104, 116,
      128, 129, 130, 132, 136, 138, 144, 160, 192, 201, 208, 256, 257, 258, 260, 261, 264, 272,
      276, 288, 320, 384, 385, 402, 511]
  let row (r : Fin 61) (i : Fin 9) : Bool := (rows.getD r.val 0).testBit i.val
  have bits (r : Fin 61) (as : List (BitVec 61)) :
      let bs := as.map fun v => v.getLsbD r.val
      (as.foldr (· &&& ·) (~~~0)).getLsbD r.val = bs.all id ∧
      (as.foldr (· ||| ·) 0).getLsbD r.val = bs.any id ∧
      (~~~(as.headD 0)).getLsbD r.val = !(bs.headD false) := by
    have rb := r.isLt
    induction as with
    | nil =>
      have hz : (0 : BitVec 61).getLsbD r.val = false := BitVec.getLsbD_zero
      have ho : (~~~(0 : BitVec 61)).getLsbD r.val = true := by
        rw [BitVec.getLsbD_not, hz]
        simp [rb]
      exact ⟨ho, hz, ho⟩
    | cons v rest ih =>
      obtain ⟨qa, qo, _⟩ := ih
      refine ⟨?_, ?_, ?_⟩
      · change (v &&& rest.foldr (· &&& ·) (~~~0)).getLsbD r.val =
          (v.getLsbD r.val && (rest.map fun w => w.getLsbD r.val).all id)
        rw [BitVec.getLsbD_and, qa]
      · change (v ||| rest.foldr (· ||| ·) 0).getLsbD r.val =
          (v.getLsbD r.val || (rest.map fun w => w.getLsbD r.val).any id)
        rw [BitVec.getLsbD_or, qo]
      · change (~~~v).getLsbD r.val = !(v.getLsbD r.val)
        rw [BitVec.getLsbD_not]
        simp [rb]
  classical
  let word (g : Gate) : Fin 3 :=
    if g.op = GateOp.and then 0 else if g.op = GateOp.or then 1 else 2
  let cap (j : ℕ) : Fin 25 := ⟨min j 24, lt_of_le_of_lt (Nat.min_le_right _ _) (by decide)⟩
  let enc (g : Gate) : Fin 3 × List (Fin 25) := (word g, g.inputs.map cap)
  let step := fun (ws : List (BitVec 61)) (g : Fin 3 × List (Fin 25)) =>
    let args := g.2.map fun i => ws.getD i.val 0
    ws ++ [if g.1 = 0 then args.foldr (· &&& ·) (~~~0)
      else if g.1 = 1 then args.foldr (· ||| ·) 0 else ~~~(args.headD 0)]
  have knownOp (g : Gate) (hg : g ∈ C.gates) :
      g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not := by
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using (fan g hg).1
  have codeNot (g : Gate) (hg : g ∈ C.gates) : word g = 2 ↔ g.op = GateOp.not := by
    rcases knownOp g hg with h | h | h <;> simp [word, h]
  have clamp {bs : List Bool} (hLen : bs.length ≤ 24) (j : ℕ) :
      bs.getD (cap j).val false = bs.getD j false := by
    by_cases h : j ≤ 24
    · simp [cap, Nat.min_eq_left h]
    · have ha : bs.length ≤ min j 24 := by omega
      have hb : bs.length ≤ j := by omega
      change bs.getD (min j 24) false = bs.getD j false
      rw [List.getD_eq_default _ _ ha, List.getD_eq_default _ _ hb]
  have bitAppend (ws : List (BitVec 61)) (a : BitVec 61) (r : Fin 61) :
      (ws ++ [a]).map (fun u => u.getLsbD r.val) =
        ws.map (fun u => u.getLsbD r.val) ++ [a.getLsbD r.val] := by simp
  have indexed (ws : List (BitVec 61)) (r : Fin 61) (j : ℕ) :
      ((ws.map fun u => u.getLsbD r.val).getD j false) = (ws.getD j 0).getLsbD r.val := by
    induction ws generalizing j with
    | nil => exact BitVec.getLsbD_zero.symm
    | cons a ws ih =>
      cases j with
      | zero => rfl
      | succ j => simpa only [List.map_cons, List.getD_cons_succ] using ih j
  have stepBits (ws : List (BitVec 61)) (r : Fin 61) (hLen : ws.length ≤ 24)
      (g : Gate) (hg : g ∈ C.gates) :
      (step ws (enc g)).map (fun u => u.getLsbD r.val) =
        scalar (ws.map fun u => u.getLsbD r.val) g := by
    let bs := ws.map fun u => u.getLsbD r.val
    let args := (g.inputs.map cap).map (fun i => ws.getD i.val 0)
    have translate :
        args.map (fun u => u.getLsbD r.val) = g.inputs.map (fun j => bs.getD j false) := by
      simp only [args, List.map_map]
      apply List.map_congr_left
      intro j _
      change (ws.getD (cap j).val 0).getLsbD r.val = bs.getD j false
      rw [← indexed, clamp (by simpa [bs] using hLen)]
    change (ws ++ [_]).map (fun u : BitVec 61 => u.getLsbD r.val) = bs ++ [_]
    rw [bitAppend]
    congr 2
    change (if word g = 0 then args.foldr (· &&& ·) (~~~0)
      else if word g = 1 then args.foldr (· ||| ·) 0 else ~~~(args.headD 0)).getLsbD r.val =
      g.op.eval (g.inputs.map (fun j => bs.getD j false))
    rcases knownOp g hg with h | h | h
    · rw [show word g = 0 by simp [word, h], ite_eq_left rfl, (bits r args).1, translate, h]
      rfl
    · rw [show word g = 1 by simp [word, h], ite_eq_right (by decide), ite_eq_left rfl,
        (bits r args).2.1, translate, h]
      rfl
    · rw [show word g = 2 by simp [word, h], ite_eq_right (by decide), ite_eq_right (by decide),
        (bits r args).2.2, translate, h]
      rfl
  have runBits (gs : List Gate) (hmem : ∀ g ∈ gs, g ∈ C.gates)
      (ws : List (BitVec 61)) (hb : ws.length + gs.length ≤ 24) (r : Fin 61) :
      ((gs.map enc).foldl step ws).map (fun u => u.getLsbD r.val) =
        gs.foldl scalar (ws.map fun u => u.getLsbD r.val) := by
    induction gs generalizing ws with
    | nil => rfl
    | cons g rest ih =>
      change ((rest.map enc).foldl step (step ws (enc g))).map (fun u => u.getLsbD r.val) =
        rest.foldl scalar (scalar (ws.map fun u => u.getLsbD r.val) g)
      rw [ih (fun j hj => hmem j (List.mem_cons_of_mem _ hj))]
      · rw [stepBits ws r (by simp at hb; omega) g (hmem g (by simp))]
      · simp [step] at hb ⊢
        omega
  have initialBits (r : Fin 61) :
      initial.map (fun u => u.getLsbD r.val) = bank (row r) := by
    revert r
    decide
  have targetBits (r : Fin 61) :
      (1265520841409113160 : BitVec 61).getLsbD r.val = target (row r) := by
    revert r
    decide
  let gs := rest.map enc
  let final := gs.foldl step initial
  have resulting (r : Fin 61) :
      final.map (fun u => u.getLsbD r.val) = C.wires (List.ofFn (row r)) := by
    change ((rest.map enc).foldl step initial).map (fun u => u.getLsbD r.val) = _
    rw [runBits rest (fun _ h => memRest h) initial (by change 10 + rest.length ≤ 24; omega),
      initialBits, ← wiresSuffix (row r)]
    rfl
  have outLen (r : Fin 61) : (C.wires (List.ofFn (row r))).length ≤ 24 := by
    have aux (l : List Gate) (v : List Bool) : (l.foldl scalar v).length = v.length + l.length := by
      induction l generalizing v with
      | nil => simp
      | cons g qs ih =>
        change (qs.foldl scalar (scalar v g)).length = v.length + (g :: qs).length
        rw [ih]
        simp [scalar]
        omega
    change (C.gates.foldl scalar (List.ofFn (row r))).length ≤ 24
    rw [aux]
    simp
    omega
  have size : gs.length ≤ 14 := by simpa [gs] using sizeRest
  have arity : ∀ g ∈ gs, g.2.length ≤ 2 := by
    intro g hg
    rcases List.mem_map.mp hg with ⟨orig, horig, rfl⟩
    simpa [enc] using (fan orig (memRest horig)).2
  have pinned : ∀ i : Fin 25, i.val < 9 → ∃ g ∈ gs,
      i ∈ (if g.1 = 2 then g.2.take 1 else g.2) := by
    intro i hi
    obtain ⟨g, hg, reads⟩ := pinsRead suffix fanRest resultSuffix ⟨i.val, hi⟩
    have hgRest : g ∈ rest := hg
    have opSem : g.op.eval [false, false] = decide (word g = 2) := by
      rcases knownOp g (memRest hgRest) with h | h | h
      · have hc : word g = 0 := by simp [word, h]
        rw [h, hc]; rfl
      · have hc : word g = 1 := by simp [word, h]
        rw [h, hc]; rfl
      · have hc : word g = 2 := by simp [word, h]
        rw [h, hc]; rfl
    have hraw : i.val ∈ (if word g = 2 then g.inputs.take 1 else g.inputs) := by
      rw [opSem] at reads
      simpa only [decide_eq_true_eq] using reads
    refine ⟨enc g, List.mem_map.mpr ⟨g, hgRest, rfl⟩, ?_⟩
    have hcap : cap i.val = i := by
      apply Fin.ext
      change min i.val 24 = i.val
      exact Nat.min_eq_left (by omega)
    change i ∈ (if word g = 2 then (g.inputs.map cap).take 1 else g.inputs.map cap)
    by_cases op : word g = 2
    · have raw : i.val ∈ g.inputs.take 1 := by simpa only [op, ite_true] using hraw
      rw [ite_eq_left op, ← List.map_take]
      exact List.mem_map.mpr ⟨i.val, raw, hcap⟩
    · have raw : i.val ∈ g.inputs := by simpa only [op, ite_false] using hraw
      rw [ite_eq_right op]
      exact List.mem_map.mpr ⟨i.val, raw, hcap⟩
  let original (k : Fin gs.length) : Fin C.gates.length :=
    ⟨k.val + 1, by have h := k.isLt; simp [gs] at h; omega⟩
  have sameGate (k : Fin gs.length) :
      (gs.get k).1 = word (C.gates.get (original k)) := by
    let rk : Fin rest.length := ⟨k.val, by have h := k.isLt; simpa [gs] using h⟩
    have hget : C.gates.get (original k) = rest.get rk := calc
      _ = C.gates.getD (k.val + 1) g0 :=
        (List.getD_eq_getElem _ _ (original k).isLt).symm
      _ = rest.getD k.val g0 := by rw [hRest, List.getD_cons_succ]
      _ = _ := List.getD_eq_getElem _ _ rk.isLt
    rw [hget]
    simp only [gs, List.get_eq_getElem, List.getElem_map, enc, rk]
  let si : Fin gs.length := ⟨4, by
    have hi' := i.isLt
    simpa [gs] using (show 4 < rest.length by omega)⟩
  let sj : Fin gs.length := ⟨j.val - 1, by
    have hj' := j.isLt
    simpa [gs] using (show j.val - 1 < rest.length by omega)⟩
  have hi' : original si = i := Fin.ext (by change 4 + 1 = i.val; omega)
  have hj' : original sj = j := Fin.ext (by
    change j.val - 1 + 1 = j.val
    have hj := Fin.lt_def.mp hij
    omega)
  have hOrder : si < sj := by
    change 4 < j.val - 1
    have hj := Fin.lt_def.mp hij
    omega
  have siNot : (gs.get si).1 = 2 := by
    rw [sameGate, hi']
    exact (codeNot _ (List.get_mem _ _)).2 hni
  have sjNot : (gs.get sj).1 = 2 := by
    rw [sameGate, hj']
    exact (codeNot _ (List.get_mem _ _)).2 hnj
  have onlyTwo (k : Fin gs.length) (hk : (gs.get k).1 = 2) : k = si ∨ k = sj := by
    have ho : (C.gates.get (original k)).op = GateOp.not :=
      (codeNot _ (List.get_mem _ _)).1 ((sameGate k).symm.trans hk)
    have inj (a b : Fin gs.length) (eq : original a = original b) : a = b := by
      have h := congrArg Fin.val eq
      change a.val + 1 = b.val + 1 at h
      exact Fin.ext (by omega)
    rcases all (original k) ho with h | h
    · exact Or.inl (inj _ _ (h.trans hi'.symm))
    · exact Or.inr (inj _ _ (h.trans hj'.symm))
  have trace : final.getD (cap C.output).val 0 = 1265520841409113160 := by
    apply BitVec.eq_of_getLsbD_eq
    intro n hn
    let r : Fin 61 := ⟨n, hn⟩
    change (final.getD (cap C.output).val 0).getLsbD r.val = _
    rw [← indexed, resulting, clamp (outLen r), targetBits r]
    exact congrFun result (row r)
  by_cases window : sj.val < 9
  · exact early gs (cap C.output) size arity pinned
      ⟨si, sj, rfl, hOrder, window, siNot, sjNot, onlyTwo⟩ trace
  · exact late gs (cap C.output) size arity pinned
      ⟨si, sj, rfl, hOrder, Nat.le_of_not_gt window, siNot, sjNot, onlyTwo⟩ trace
