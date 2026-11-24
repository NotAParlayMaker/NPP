import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_3202_726
    (bits :
      ∀ (r : Fin 59) (as : List (BitVec 59)),
        let bs := as.map fun v => v.getLsbD r.val
        (as.foldr (· &&& ·) (~~~0)).getLsbD r.val = bs.all id ∧
        (as.foldr (· ||| ·) 0).getLsbD r.val = bs.any id ∧
        (~~~(as.headD 0)).getLsbD r.val = !(bs.headD false))
    (noTrace :
      let initial : List (BitVec 59) :=
        [360930119642124586, 432486920269079116, 293578547141297264,
          289365901620316032, 439119665042618368, 297239789478805504,
          306275578149863424, 540467122476679168, 576425567931334656]
      let step := fun (ws : List (BitVec 59)) (g : Fin 3 × List (Fin 25)) =>
        let args := g.2.map fun i => ws.getD i.val 0
        ws ++ [if g.1 = 0 then args.foldr (· &&& ·) (~~~0)
          else if g.1 = 1 then args.foldr (· ||| ·) 0 else ~~~(args.headD 0)]
      ∀ (gs : List (Fin 3 × List (Fin 25))) (out : Fin 25),
        gs.length ≤ 15 →
        (∀ g ∈ gs, g.2.length ≤ 2) →
        (∃ (i j : Fin gs.length), i < j ∧ i.val = 7 ∧
          (gs.get i).1 = 2 ∧ (gs.get j).1 = 2 ∧
          ∀ k : Fin gs.length, (gs.get k).1 = 2 → k = i ∨ k = j) →
        let final := gs.foldl step initial
        final.getD 9 0 = 365715340409853306 →
        final.getD out.val 0 ≠ 316380210352264264) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∃ (x3 : Fin x1.gates.length) (x4 : Fin x1.gates.length), x3 < x4 ∧ ↑x3 = (7 : ℕ) ∧ (x1.gates.get x3).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ ∀ (x5 : Fin x1.gates.length), (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.not → x5 = x3 ∨ x5 = x4) → (∀ (x4 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x4)).getD (9 : ℕ) Bool.false = (x4 (0 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x5 : Fin (9 : ℕ) → Bool) => x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ))) → (16 : ℕ) ≤ x1.size := by
  intro C fan neg first result
  by_contra! small
  have hSize : C.gates.length ≤ 15 := by
    change C.gates.length < 16 at small
    omega
  let initial : List (BitVec 59) :=
    [360930119642124586, 432486920269079116, 293578547141297264,
      289365901620316032, 439119665042618368, 297239789478805504,
      306275578149863424, 540467122476679168, 576425567931334656]
  let rows : List ℕ :=
    [0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 16, 17, 18, 20, 24, 32, 33, 34, 36,
      40, 42, 48, 50, 64, 65, 66, 68, 69, 72, 80, 96, 104, 116, 128, 129, 130,
      132, 136, 138, 144, 160, 192, 201, 208, 256, 257, 258, 260, 261, 264, 272,
      276, 288, 320, 384, 385, 402, 511]
  let row (r : Fin 59) (j : Fin 9) : Bool := (rows.getD r.val 0).testBit j.val
  let target (x : Fin 9 → Bool) :=
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
    x 6 && x 8 || x 8 && x 5
  classical
  let word (g : Gate) : Fin 3 :=
    if g.op = GateOp.and then 0 else if g.op = GateOp.or then 1 else 2
  let cap (j : ℕ) : Fin 25 := ⟨min j 24, lt_of_le_of_lt (Nat.min_le_right _ _) (by decide)⟩
  let enc (g : Gate) : Fin 3 × List (Fin 25) := (word g, g.inputs.map cap)
  let step := fun (ws : List (BitVec 59)) (g : Fin 3 × List (Fin 25)) =>
    let args := g.2.map fun i => ws.getD i.val 0
    ws ++ [if g.1 = 0 then args.foldr (· &&& ·) (~~~0)
      else if g.1 = 1 then args.foldr (· ||| ·) 0 else ~~~(args.headD 0)]
  let scalar (bs : List Bool) (g : Gate) :=
    bs ++ [g.op.eval (g.inputs.map (fun j => bs.getD j false))]
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
  have bitAppend (ws : List (BitVec 59)) (a : BitVec 59) (r : Fin 59) :
      (ws ++ [a]).map (fun u => u.getLsbD r.val) =
        ws.map (fun u => u.getLsbD r.val) ++ [a.getLsbD r.val] := by simp
  have indexed (ws : List (BitVec 59)) (r : Fin 59) (j : ℕ) :
      ((ws.map fun u => u.getLsbD r.val).getD j false) = (ws.getD j 0).getLsbD r.val := by
    induction ws generalizing j with
    | nil => exact BitVec.getLsbD_zero.symm
    | cons a ws ih =>
      cases j with
      | zero => rfl
      | succ j => simpa only [List.map_cons, List.getD_cons_succ] using ih j
  have stepBits (ws : List (BitVec 59)) (r : Fin 59) (hLen : ws.length ≤ 24)
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
    change (ws ++ [_]).map (fun u : BitVec 59 => u.getLsbD r.val) = bs ++ [_]
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
      (ws : List (BitVec 59)) (hb : ws.length + gs.length ≤ 24) (r : Fin 59) :
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
  have initialBits (r : Fin 59) :
      initial.map (fun u => u.getLsbD r.val) = List.ofFn (row r) := by
    revert r
    decide
  have firstBits (r : Fin 59) :
      (365715340409853306 : BitVec 59).getLsbD r.val = (row r 0 || row r 2) := by
    revert r
    decide
  have targetBits (r : Fin 59) :
      (316380210352264264 : BitVec 59).getLsbD r.val = target (row r) := by
    revert r
    decide
  let gs := C.gates.map enc
  let final := gs.foldl step initial
  have resulting (r : Fin 59) :
      final.map (fun u => u.getLsbD r.val) = C.wires (List.ofFn (row r)) := by
    change ((C.gates.map enc).foldl step initial).map (fun u => u.getLsbD r.val) = _
    rw [runBits C.gates (fun _ h => h) initial (by change 9 + C.gates.length ≤ 24; omega), initialBits]
    rfl
  have outLen (r : Fin 59) : (C.wires (List.ofFn (row r))).length ≤ 24 := by
    have aux (l : List Gate) (v : List Bool) : (l.foldl scalar v).length = v.length + l.length := by
      induction l generalizing v with
      | nil => simp
      | cons g gs ih =>
        change (gs.foldl scalar (scalar v g)).length = v.length + (g :: gs).length
        rw [ih]
        simp [scalar]
        omega
    change (C.gates.foldl scalar (List.ofFn (row r))).length ≤ 24
    rw [aux]
    simp
    omega
  have size : gs.length ≤ 15 := by simpa [gs] using hSize
  have arity : ∀ g ∈ gs, g.2.length ≤ 2 := by
    intro g hg
    rcases List.mem_map.mp hg with ⟨orig, horig, rfl⟩
    simpa [enc] using (fan orig horig).2
  have two : ∃ (i j : Fin gs.length), i < j ∧ i.val = 7 ∧
      (gs.get i).1 = 2 ∧ (gs.get j).1 = 2 ∧
      ∀ k : Fin gs.length, (gs.get k).1 = 2 → k = i ∨ k = j := by
    obtain ⟨i, j, hij, hi, hni, hnj, all⟩ := neg
    have length : gs.length = C.gates.length := by simp [gs]
    refine ⟨Fin.cast length.symm i, Fin.cast length.symm j, hij, hi, ?_, ?_, ?_⟩
    · simpa [gs, enc] using (codeNot _ (List.get_mem _ _)).2 hni
    · simpa [gs, enc] using (codeNot _ (List.get_mem _ _)).2 hnj
    · intro k hk
      let k' : Fin C.gates.length := Fin.cast length k
      have hnk : (C.gates.get k').op = GateOp.not :=
        (codeNot _ (List.get_mem _ _)).1 (by simpa [gs, enc, k'] using hk)
      rcases all k' hnk with h | h
      · exact Or.inl (Fin.ext (congrArg (fun i : Fin C.gates.length => i.val) h))
      · exact Or.inr (Fin.ext (congrArg (fun i : Fin C.gates.length => i.val) h))
  have firstWord : final.getD 9 0 = 365715340409853306 := by
    apply BitVec.eq_of_getLsbD_eq
    intro n hn
    let r : Fin 59 := ⟨n, hn⟩
    change (final.getD 9 0).getLsbD r.val = _
    rw [← indexed, resulting, firstBits r]
    exact first (row r)
  apply noTrace gs (cap C.output) size arity two firstWord
  apply BitVec.eq_of_getLsbD_eq
  intro n hn
  let r : Fin 59 := ⟨n, hn⟩
  change (final.getD (cap C.output).val 0).getLsbD r.val = _
  rw [← indexed, resulting, clamp (outLen r), targetBits r]
  exact congrFun result (row r)
