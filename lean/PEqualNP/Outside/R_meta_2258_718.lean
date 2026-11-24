import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
open PEqualNP.TopForm PEqualNP.CleanedNonEdge

-- The first sixteen rows are edges and the other twenty-four are maximal
-- independent sets. Each integer codes the truth column of one input.
-- A least circuit must distinguish each operand of an AND on a negative row
-- and each operand of an OR on a positive row. A junk AND also accepts a
-- negative row. These restrictions prune the finite synthesis problem.
set_option maxHeartbeats 6000000 in
theorem PEqualNP.Outside.R_meta_2258_718
    (essential : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      IsLeastAO G C → ∀ j < C.size, ∀ b : Fin 2,
      ∃ x : Fin n → Bool,
        (let g := gateAt C j
         (g.op = .and → graphFun G ∅ x = false ∧ ∀ u, x u = false →
           graphFun G ∅ (Function.update x u true) = true) ∧
         (g.op = .or → ∃ u v, G.Adj u v ∧ x = pairInput u v)) ∧
        gateVal n C j x ≠ (C.wires (List.ofFn x)).getD (opnd C j b) false)
    (exclude : ∀ (k : ℕ) (op : Fin k → Bool) (a b : Fin k → Fin 32)
        (table : Fin 32 → Fin 40 → Bool) (out : Fin 32), k ≤ 21 → out.val < 11+k →
      let z (j : ℕ) := table (Fin.ofNat 32 j)
      (∀ (i : Fin 11) (r : Fin 40), z i.val r = (([2147418115, 663661903884, 34144976944, 728266375360, 21653750532, 103293914128, 26322415680, 344922804352, 414195942664, 581968119809, 1065151898146] : List ℕ).getD i.val 0).testBit r.val) →
      (∀ j : Fin k, let A := table (a j); let B := table (b j)
        (a j).val < 11+j.val ∧ (b j).val < 11+j.val ∧
        (∀ r, z (11+j.val) r = (if op j then A r && B r else A r || B r)) ∧
        ∀ e : Bool, ∃ r : Fin 40, decide (16 ≤ r.val) = op j ∧ A r = e ∧ B r = !e) →
      (let D : Circuit := ⟨List.ofFn (fun j => ⟨if op j then .and else .or, [(a j).val,(b j).val]⟩), out.val⟩
       ∀ i j : Fin k, op i = true → (∀ r : Fin 40, 16 ≤ r.val → z (11+i.val) r = false) →
         op j = true → ¬InCone 11 D i.val j.val) →
      (∃ J : Finset (Fin k), 3 ≤ J.card ∧ ∀ j ∈ J, op j = true ∧
        ∃ r : Fin 40, 16 ≤ r.val ∧ z (11+j.val) r = true) →
      ∃ r : Fin 40, table out r ≠ decide (r.val < 16)) :
∀ (x1 : SimpleGraph (Fin (11 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit),   x1 = PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))] →     PEqualNP.TopForm.IsLeastAO x1 x3 →       PEqualNP.TopForm.TopForm x1 x3 →         have x7 : Finset ℕ := PEqualNP.TopForm.tops x1 x3;         have x8 : Finset ℕ := PEqualNP.TopForm.centreless x1 x3;         have x9 : Finset ℕ := PEqualNP.TopForm.junk x1 x3;         have x10 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x3;         (∀ x11 ∈ x7,             have x13 : Fin (2 : ℕ) → Finset (Fin (11 : ℕ)) := PEqualNP.TopForm.side x3 x11;             (∀ x14 ∈ x13 (0 : Fin (2 : ℕ)), ∀ x16 ∈ x13 (1 : Fin (2 : ℕ)), x1.Adj x14 x16) ∧ ((x13 (0 : Fin (2 : ℕ))).card ≤ (1 : ℕ) ∨ (x13 (1 : Fin (2 : ℕ))).card ≤ (1 : ℕ))) →           (∀ (x12 x13 : Fin (11 : ℕ)), s(x12, x13) ∈ x10 → ∃ x15 ∈ x7, ∃ (x16 : Fin (2 : ℕ)), ∃ x17 ∈ x9, PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x15 (PEqualNP.EdgeOwnership.pairInput x12 x13) = Bool.true ∧ PEqualNP.CleanedNonEdge.OrReaches (11 : ℕ) x3 (PEqualNP.TopForm.opnd x3 x15 x16) x17 ∧ PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x17 (PEqualNP.EdgeOwnership.pairInput x12 x13) = Bool.true) → (15 : ℕ) + (x7 \ x8).card + (2 : ℕ) * x8.card + x9.card + (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card ≤ x3.size + x10.card → (∀ (x14 : Finset (Fin (11 : ℕ))), PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑x10) x14 → x14.card ≤ (x7 \ x8).card) → (3 : ℕ) ≤ x9.card → (22 : ℕ) ≤ x3.size := by
  intro G inst C eqG least top _ _ _ _ _ _ _ _ hJ
  by_contra! short
  let E : List (ℕ × ℕ) := [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
  let H := edgeGraph 11 E
  let N : List ℕ := [15, 29, 43, 57, 71, 85, 99, 113, 135, 149, 163, 177, 269, 325, 389, 526, 540, 582, 596, 1066, 1186, 1288, 1408, 1546]
  let P : List ℕ := [513, 1025, 18, 258, 36, 1028, 72, 136, 272, 1040, 288, 544, 192, 1088, 640, 768]
  let input (r : ℕ) : Fin 11 → Bool := fun i => r.testBit i.val
  let sample (r : ℕ) := E.any fun e => r.testBit e.1 && r.testBit e.2
  have graphTrue (D : SimpleGraph (Fin 11)) [DecidableRel D.Adj] (x : Fin 11 → Bool) :
      graphFun D ∅ x = true ↔ ∃ u v, D.Adj u v ∧ x u = true ∧ x v = true := by
    change (decide (∃ a ∈ (∅ : Finset (Fin 11)), x a = true) ||
      decide (∃ u v, D.Adj u v ∧ x u = true ∧ x v = true)) = true ↔ _
    simp only [Finset.notMem_empty, false_and, exists_false, decide_false,
      Bool.false_or, decide_eq_true_eq]
  change G = H at eqG
  have same (x : Fin 11 → Bool) : graphFun G ∅ x = graphFun H ∅ x := by
    apply Bool.eq_iff_iff.mpr
    rw [graphTrue G x, graphTrue H x, eqG]
  have sampleCorrect (r : ℕ) : sample r = graphFun H ∅ (input r) := by
    apply Bool.eq_iff_iff.mpr
    rw [graphTrue H]
    change E.any _ = true ↔ _
    rw [List.any_eq_true]
    constructor
    · rintro ⟨⟨u,v⟩, he, hv⟩
      have valid : E.all (fun e => decide (e.1 < 11 ∧ e.2 < 11 ∧ e.1 ≠ e.2)) = true := by
        decide +kernel
      obtain ⟨hu, hv', ne⟩ := of_decide_eq_true (List.all_eq_true.mp valid _ he)
      have adj : H.Adj ⟨u,hu⟩ ⟨v,hv'⟩ := ⟨fun e => ne (congrArg Fin.val e), Or.inl he⟩
      obtain ⟨onU,onV⟩ := Bool.and_eq_true_iff.mp hv
      exact ⟨⟨u,hu⟩, ⟨v,hv'⟩, adj, onU, onV⟩
    · rintro ⟨u,v,he,hu,hv⟩
      rcases he.2 with e | e
      · exact ⟨(u.val,v.val), e, Bool.and_eq_true_iff.mpr ⟨hu,hv⟩⟩
      · exact ⟨(v.val,u.val), e, Bool.and_eq_true_iff.mpr ⟨hv,hu⟩⟩
  have listedNeg : N.all (fun r => !sample r) = true := by decide +kernel
  have listedPos : P.all sample = true := by decide +kernel
  have seenNeg (r : ℕ) (hr : r ∈ N) : graphFun G ∅ (input r) = false := by
    have ok := List.all_eq_true.mp listedNeg r hr
    have bit : sample r = false := by
      cases h : sample r with
      | false => rfl
      | true => rw [h] at ok; contradiction
    exact (same _).trans ((sampleCorrect r).symm.trans bit)
  have seenPos (r : ℕ) (hr : r ∈ P) : graphFun G ∅ (input r) = true := by
    rw [same, ← sampleCorrect]
    exact List.all_eq_true.mp listedPos r hr
  let wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

  have wiresFrom_nil (w : List Bool) : wiresFrom [] w = w := rfl

  have wiresFrom_cons (g : Gate) (gs : List Gate) (w : List Bool) :
      wiresFrom (g :: gs) w =
        wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

  have getD_snoc_lt (l : List Bool) (x d : Bool) (i : ℕ) (hi : i < l.length) :
      (l ++ [x]).getD i d = l.getD i d := by
    simp [List.getD, List.getElem?_append_left hi]

  have getD_snoc_eq (l : List Bool) (x d : Bool) (i : ℕ) (hi : i = l.length) :
      (l ++ [x]).getD i d = x := by
    subst hi
    simp [List.getD]

  have getD_snoc_ne (l : List Bool) (x d : Bool) (i : ℕ) (hi : i ≠ l.length) :
      (l ++ [x]).getD i d = l.getD i d := by
    by_cases hlt : i < l.length
    · exact getD_snoc_lt l x d i hlt
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

  have monotone_and : ∀ a a' b b' : Bool, a ≤ a' → b ≤ b' → (a && b) ≤ (a' && b') := by
    decide

  have monotone_or : ∀ a a' b b' : Bool, a ≤ a' → b ≤ b' → (a || b) ≤ (a' || b') := by
    decide

  have monotone_lists (l : List ℕ) (a b : ℕ → Bool) (le : ∀ i ∈ l, a i ≤ b i) :
      GateOp.and.eval (l.map a) ≤ GateOp.and.eval (l.map b) ∧
        GateOp.or.eval (l.map a) ≤ GateOp.or.eval (l.map b) := by
    induction l with
    | nil => exact ⟨le_rfl,le_rfl⟩
    | cons n l ih =>
      obtain ⟨conj,disj⟩ := ih (fun j hj => le j (List.mem_cons_of_mem n hj))
      have first := le n List.mem_cons_self
      exact ⟨monotone_and _ _ _ _ first conj,monotone_or _ _ _ _ first disj⟩


  have monotone_wires (gs : List Gate) (a b : List Bool)
      (ops : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
      (len : a.length = b.length)
      (ordered : ∀ i, a.getD i false ≤ b.getD i false) :
      ∀ i, (wiresFrom gs a).getD i false ≤ (wiresFrom gs b).getD i false := by
    induction gs generalizing a b with
    | nil => exact ordered
    | cons g tail ih =>
      let x := g.op.eval (g.inputs.map fun i => a.getD i false)
      let y := g.op.eval (g.inputs.map fun i => b.getD i false)
      have xy : x ≤ y := by
        change g.op.eval _ ≤ g.op.eval _
        rcases ops g List.mem_cons_self with eq | eq
        · rw [eq]
          exact (monotone_lists _ _ _ (fun i _ => ordered i)).1
        · rw [eq]
          exact (monotone_lists _ _ _ (fun i _ => ordered i)).2
      have next (i : ℕ) : (a ++ [x]).getD i false ≤ (b ++ [y]).getD i false := by
        by_cases hit : i = a.length
        · rw [getD_snoc_eq _ _ _ _ hit,getD_snoc_eq _ _ _ _ (hit.trans len)]
          exact xy
        · rw [getD_snoc_ne _ _ _ _ hit,getD_snoc_ne _ _ _ _ (by rwa [← len])]
          exact ordered i
      intro i
      change (wiresFrom tail (a ++ [x])).getD i false ≤ (wiresFrom tail (b ++ [y])).getD i false
      exact ih _ _ (fun g h => ops g (List.mem_cons_of_mem _ h)) (by simp [len]) next i

  have extend : ∀ x : Fin 11 → Bool, graphFun H ∅ x = false →
      ∃ r ∈ N, ∀ i, x i ≤ input r i := by decide +kernel
  have sound (j : ℕ) (quiet : ∀ r ∈ N, gateVal 11 C j (input r) = false) :
      BelowF G C j := by
    intro x hx
    cases hf : graphFun G ∅ x with
    | true => rfl
    | false =>
      obtain ⟨r,hr,sup⟩ := extend x ((same x).symm.trans hf)
      have order (i : ℕ) : (List.ofFn x).getD i false ≤ (List.ofFn (input r)).getD i false := by
        by_cases lt : i < 11
        · rw [List.getD_eq_getElem _ _ (by simpa using lt),List.getD_eq_getElem _ _ (by simpa using lt),List.getElem_ofFn,List.getElem_ofFn]
          exact sup ⟨i,lt⟩
        · rw [List.getD_eq_default _ _ (by simp;omega),List.getD_eq_default _ _ (by simp;omega)]
      have le := monotone_wires C.gates _ _ least.1.1 (by simp) order (11+j)
      change gateVal 11 C j x ≤ gateVal 11 C j (input r) at le
      rw [hx,quiet r hr] at le
      exact (by decide : ¬ ((true : Bool) ≤ false)) le |>.elim
  have info (j : ℕ) (hj : j ∈ junk G C) :
      j < C.size ∧ (gateAt C j).op = GateOp.and ∧ IsDirty 11 G C j := by
    unfold junk gatesWhere at hj
    rw [Finset.mem_filter, Finset.mem_range] at hj
    exact hj

  let rows := P ++ N
  let row (t : Fin 40) := input (rows.getD t.val 0)
  let mask (t : Fin 40) := decide (t.val < 16)
  let cols : List ℕ := [2147418115, 663661903884, 34144976944, 728266375360, 21653750532, 103293914128, 26322415680, 344922804352, 414195942664, 581968119809, 1065151898146]
  have startBits : ∀ (i : Fin 11) (t : Fin 40), row t i = (cols.getD i.val 0).testBit t.val := by
    decide +kernel
  have rowMem : ∀ t : Fin 40, if t.val < 16 then rows.getD t.val 0 ∈ P else rows.getD t.val 0 ∈ N := by
    decide +kernel
  have hitsNeg : ∀ n ∈ N, ∃ t : Fin 40, 16 ≤ t.val ∧ rows.getD t.val 0 = n := by
    intro n hn
    simp only [N,List.mem_cons,List.not_mem_nil,or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  have edgeRow : ∀ u v : Fin 11, H.Adj u v → ∃ t : Fin 40, t.val < 16 ∧ row t = pairInput u v := by
    decide +kernel
  have maxRow : ∀ x : Fin 11 → Bool, graphFun H ∅ x = false →
      (∀ u, x u = false → graphFun H ∅ (Function.update x u true) = true) →
      ∃ t : Fin 40, 16 ≤ t.val ∧ row t = x := by
    decide +kernel
  have expected (t : Fin 40) : graphFun G ∅ (row t) = mask t := by
    have ht := rowMem t
    by_cases e : t.val < 16
    · simp only [ite_true,e] at ht
      have he : mask t = true := decide_eq_true e
      rw [he]
      exact seenPos _ ht
    · simp only [ite_false,e] at ht
      have he : mask t = false := decide_eq_false e
      rw [he]
      exact seenNeg _ ht
  let tab (i : Fin 32) (t : Fin 40) := (C.wires (List.ofFn (row t))).getD i.val false
  let op (j : Fin C.size) := (gateAt C j.val).op.eval [true,false] == false
  let A (j : Fin C.size) : Fin 32 := Fin.ofNat 32 (opnd C j.val 0)
  let B (j : Fin C.size) : Fin 32 := Fin.ofNat 32 (opnd C j.val 1)
  have gateMem (j : Fin C.size) : gateAt C j.val ∈ C.gates := by
    unfold gateAt
    rw [List.getD_eq_getElem _ _ j.isLt]
    exact List.getElem_mem _
  have pair (j : Fin C.size) : (gateAt C j.val).inputs = [opnd C j.val 0,opnd C j.val 1] := by
    obtain ⟨u,v,h⟩ := List.length_eq_two.mp (least.1.2.2 _ (gateMem j))
    change (gateAt C j.val).inputs = [(gateAt C j.val).inputs.getD 0 0,(gateAt C j.val).inputs.getD 1 0]
    rw [h]
    rfl
  have earlier (j : Fin C.size) (b : Fin 2) : opnd C j.val b < 11+j.val := by
    apply least.1.2.1 _ j.isLt
    rw [pair]
    fin_cases b <;> simp
  have aval (j : Fin C.size) : (A j).val = opnd C j.val 0 := Nat.mod_eq_of_lt (by have := earlier j 0; omega)
  have bval (j : Fin C.size) : (B j).val = opnd C j.val 1 := Nat.mod_eq_of_lt (by have := earlier j 1; omega)
  let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have oldWire (p : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (p.foldl step w).getD i false = w.getD i false := by
    induction p generalizing w with
    | nil => rfl
    | cons g p ih =>
      rw [List.foldl_cons,ih _ (by simp [step];omega)]
      exact List.getD_append _ _ _ _ hi
  have length (p : List Gate) (w : List Bool) : (p.foldl step w).length = w.length+p.length := by
    induction p generalizing w with
    | nil => rfl
    | cons g p ih => simp only [List.foldl_cons,ih,step,List.length_append,List.length_cons,List.length_nil]; omega
  have gateRow (j : Fin C.size) (t : Fin 40) :
      gateVal 11 C j.val (row t) = (gateAt C j.val).op.eval [tab (A j) t, tab (B j) t] := by
    let inp := List.ofFn (row t)
    let p := C.gates.take j.val
    let g := gateAt C j.val
    let tail := C.gates.drop (j.val+1)
    let w := p.foldl step inp
    have wlen : w.length = 11+j.val := by
      have low : j.val ≤ C.gates.length := j.isLt.le
      simp [w,length,p,inp, low]
    have split : C.gates = p ++ g :: tail := by
      have h := List.take_append_drop j.val C.gates
      rw [List.drop_eq_getElem_cons j.isLt] at h
      change C.gates = C.gates.take j.val ++ C.gates.getD j.val _ :: C.gates.drop (j.val+1)
      rw [List.getD_eq_getElem _ _ j.isLt]
      exact h.symm
    have ws := congrArg (fun l : List Gate => l.foldl step inp) split
    change C.wires inp = _ at ws
    rw [List.foldl_append,List.foldl_cons] at ws
    have wi (u : ℕ) (hu : u < w.length) : (C.wires inp).getD u false = w.getD u false := by
      rw [ws,oldWire _ _ _ (by change u < (step w g).length; simp [step]; omega)]
      exact List.getD_append _ _ _ _ hu
    change (C.wires inp).getD (11+j.val) false = g.op.eval [(C.wires inp).getD (A j).val false,(C.wires inp).getD (B j).val false]
    rw [aval,bval,wi (opnd C j.val 0) (by rw [wlen]; exact earlier j 0),wi (opnd C j.val 1) (by rw [wlen];exact earlier j 1),ws,
      oldWire tail (step w g) (11+j.val) (by simp [step,wlen])]
    change (w ++ [_]).getD _ false = _
    rw [List.getD_append_right _ _ _ _ wlen.le,wlen]
    simp [g,pair]
  have kind (j : Fin C.size) : (gateAt C j.val).op = .and ∨ (gateAt C j.val).op = .or := least.1.1 _ (gateMem j)
  have evalA (u v : Bool) : GateOp.and.eval [u,v] = (u && v) := by cases u <;> cases v <;> rfl
  have evalO (u v : Bool) : GateOp.or.eval [u,v] = (u || v) := by cases u <;> cases v <;> rfl
  have gateAnswer (j : Fin C.size) (t : Fin 40) :
      gateVal 11 C j.val (row t) = (if op j then tab (A j) t && tab (B j) t else tab (A j) t || tab (B j) t) := by
    rw [gateRow]
    rcases kind j with h | h <;> simp [op,h,evalA,evalO]
  have signs (j : Fin C.size) (e : Bool) : ∃ t : Fin 40, decide (16 ≤ t.val) = op j ∧ tab (A j) t = e ∧ tab (B j) t = !e := by
    let b : Fin 2 := if e == op j then 0 else 1
    obtain ⟨x,⟨hAnd,hOr⟩,separate⟩ := essential 11 G C least j.val j.isLt b
    have locate : ∃ t : Fin 40, decide (16 ≤ t.val) = op j ∧ row t = x := by
      rcases kind j with ho | ho
      · obtain ⟨hn,hm⟩ := hAnd ho
        obtain ⟨t,ht,eq⟩ := maxRow x ((same x).symm.trans hn) (fun u hu => (same _).symm.trans (hm u hu))
        exact ⟨t,by simp [op,ho,ht,evalA],eq⟩
      · obtain ⟨u,v,adj,rfl⟩ := hOr ho
        obtain ⟨t,ht,eq⟩ := edgeRow u v (by change (edgeGraph 11 E).Adj u v; rwa [eqG] at adj)
        exact ⟨t,by simp [op,ho,Nat.not_le_of_lt ht,evalO],eq⟩
    obtain ⟨t,ht,rfl⟩ := locate
    refine ⟨t,ht,?_⟩
    have tapA : (C.wires (List.ofFn (row t))).getD (opnd C j.val 0) false = tab (A j) t := by simp only [tab,aval]
    have tapB : (C.wires (List.ofFn (row t))).getD (opnd C j.val 1) false = tab (B j) t := by simp only [tab,bval]
    have pick : (C.wires (List.ofFn (row t))).getD (opnd C j.val b) false =
        (if e == op j then tab (A j) t else tab (B j) t) := by
      by_cases h : (e == op j) = true
      · simpa only [b,h,ite_true] using tapA
      · simpa only [b,ite_eq_right h] using tapB
    rw [gateAnswer,pick] at separate
    have logic : ∀ d e u v : Bool, (if d then u && v else u || v) ≠ (if e == d then u else v) → u = e ∧ v = !e := by decide
    exact logic _ _ _ _ separate
  have dirty (j : ℕ) (hj : j ∈ junk G C) :
      ∃ jj : Fin C.size, jj.val = j ∧ op jj = true ∧ ∃ t : Fin 40, 16 ≤ t.val ∧ tab (Fin.ofNat 32 (11+j)) t = true := by
    obtain ⟨hi,ho,_,x,hx,hno⟩ := info j hj
    let jj : Fin C.size := ⟨j,hi⟩
    have existsNeg : ∃ r ∈ N, gateVal 11 C j (input r) = true := by
      by_contra empty
      have quiet : ∀ r ∈ N, gateVal 11 C j (input r) = false := by
        intro r hr
        cases h : gateVal 11 C j (input r) with
        | false => rfl
        | true => exact False.elim (empty ⟨r,hr,h⟩)
      exact Bool.false_ne_true ((hno.symm).trans (sound j quiet x hx))
    obtain ⟨r,hr,hit⟩ := existsNeg
    obtain ⟨t,ht,rt⟩ := hitsNeg r hr
    refine ⟨jj,rfl,by simp [op,jj,ho,evalA],t,ht,?_⟩
    have ix : (11+j)%32 = 11+j := Nat.mod_eq_of_lt (by omega)
    unfold gateVal at hit
    simpa only [tab,Fin.val_ofNat,ix,row,rt] using hit
  let good := Finset.univ.filter fun j : Fin C.size => op j ∧
    ∃ t : Fin 40, 16 ≤ t.val ∧ tab (Fin.ofNat 32 (11+j.val)) t = true
  have sub : junk G C ⊆ good.image Fin.val := by
    intro j hj
    obtain ⟨jj,he,ho,t,ht,hit⟩ := dirty j hj
    subst j
    exact Finset.mem_image.mpr ⟨jj,Finset.mem_filter.mpr ⟨Finset.mem_univ _,ho,t,ht,hit⟩,rfl⟩
  have hd : 3 ≤ good.card := hJ.trans ((Finset.card_le_card sub).trans (Finset.card_image_le))
  have validOut : C.output < 11+C.size := by
    by_contra! bad
    let t : Fin 40 := 0
    have yes := (congrFun least.2.1 (row t)).trans (expected t)
    change (C.wires (List.ofFn (row t))).getD C.output false = true at yes
    change 11+C.gates.length ≤ C.output at bad
    rw [List.getD_eq_default _ _ (by change (C.gates.foldl step _).length ≤ _; simpa only [length,List.length_ofFn] using bad)] at yes
    contradiction
  let out : Fin 32 := ⟨C.output,by omega⟩
  obtain ⟨t,miss⟩ := exclude C.size op A B tab out (by omega) validOut
    (by intro i t; change (C.gates.foldl step _).getD _ false = _; rw [oldWire _ _ _ (by simp;omega)];
        rw [Fin.val_ofNat,Nat.mod_eq_of_lt (by omega : i.val < 32),List.getD_eq_getElem _ _ (by simp),List.getElem_ofFn]; exact startBits i t)
    (by intro j; refine ⟨by rw [aval];exact earlier j 0,by rw [bval];exact earlier j 1,?_,signs j⟩
        intro t
        have ans := gateAnswer j t
        unfold gateVal at ans
        simpa only [tab,Fin.val_ofNat,Nat.mod_eq_of_lt (by omega : 11+j.val < 32)] using ans)
    (by
      let rebuilt := List.ofFn (fun j : Fin C.size =>
        (⟨if op j then .and else .or, [(A j).val,(B j).val]⟩ : Gate))
      have recovers (j : Fin C.size) : (⟨if op j then .and else .or, [(A j).val,(B j).val]⟩ : Gate) = C.gates[j.val]'j.isLt := by
        have eg := List.getD_eq_getElem C.gates (⟨.or,[]⟩ : Gate) j.isLt
        change gateAt C j.val = _ at eg
        rw [←eg,aval,bval,←pair]
        have ok : (if op j then GateOp.and else GateOp.or) = (gateAt C j.val).op := by
          rcases kind j with ho | ho <;> simp [op,ho,evalA,evalO]
        rw [ok]
      have restores : rebuilt = C.gates := by
        have eq := congrArg List.ofFn (funext recovers)
        exact eq.trans List.ofFn_getElem
      have basis (j : Fin C.size) (h : op j = true) : (gateAt C j.val).op = .and := by
        rcases kind j with ho | ho
        · exact ho
        · simp [op,ho,evalO] at h
      intro temp i j ai clean aj
      have low : BelowF G C i.val := by
        apply sound
        intro r hr
        obtain ⟨t,ht,eq⟩ := hitsNeg r hr
        have hw := clean t ht
        unfold gateVal
        simpa only [tab,Fin.val_ofNat,Nat.mod_eq_of_lt (by omega : 11+i.val < 32),row,eq] using hw
      change ¬ InCone 11 (⟨rebuilt,out.val⟩ : Circuit) i.val j.val
      rw [restores]
      exact top i.val i.isLt j.val j.isLt (basis i ai) low (basis j aj))
    ⟨good,hd,fun _ h => (Finset.mem_filter.mp h).2⟩
  exact miss ((congrFun least.2.1 (row t)).trans (expected t))
