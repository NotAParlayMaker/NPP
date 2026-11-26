import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.CircuitMoves PEqualNP.HeptadCover PEqualNP.GenericRejection
set_option maxHeartbeats 2500000 in
set_option maxRecDepth 8000 in
theorem PEqualNP.Outside.R_meta_5040_82
    (peel : ∀ C : Circuit, Monotone2 C → C.size ≤ 63 →
      ¬ HasLineDegree 26 (Finset.Ico 13 26) C 1 → ¬ HasLineDegree 26 (Finset.range 13) C 1 →
      (∀ u v : Fin 13, u ∈ singerLines3 v → C.eval (incidenceInput {u} {v}) = true) → (∀ j : Fin 36, let r := ((154864532458776913328923231818436173642350964167816379617494761446708840970305666064333610980186298862096319296411637866322823066651732813787683520215880584087994696174523727794542474942805109892481093000432148714521561784232086750948867262360411163194590501214779416935824884826119 : ℕ) >>> (26*j.val)) % 67108864
      ∀ t : Fin 13, circuitFun 26 C (fun i : Fin 26 => Fin.addCases (motive := fun _ => Bool) (fun v : Fin 13 => r.testBit (v-t).val) (fun v : Fin 13 => r.testBit (13+(v-t).val)) i) = false) →
      ∃ a b : Fin 13, a ∈ singerLines3 b ∧ ∃ moves : List (ℕ × ℕ), moves.length = 8 ∧
        (∀ i : Fin moves.length, (moves.get i).1 < C.size-i.val) ∧
        let D := moves.foldl (fun A m => eraseGate 26 A m.1 m.2) C
        ∀ x : Fin 26 → Bool, x (Fin.castAdd 13 a) = false → x (Fin.natAdd 13 b) = false →
          circuitFun 26 D x = circuitFun 26 C x)
    (puncture : ∀ (a b : Fin 13), a ∈ singerLines3 b → ∀ C : Circuit, Monotone2 C →
      (∀ u v : Fin 13, u ∈ singerLines3 v → u ≠ a → v ≠ b → C.eval (incidenceInput {u} {v}) = true) → (∀ j : Fin 36, let r := ((154864532458776913328923231818436173642350964167816379617494761446708840970305666064333610980186298862096319296411637866322823066651732813787683520215880584087994696174523727794542474942805109892481093000432148714521561784232086750948867262360411163194590501214779416935824884826119 : ℕ) >>> (26*j.val)) % 67108864
      ∀ t : Fin 13, circuitFun 26 C (fun i => if i = Fin.castAdd 13 a ∨ i = Fin.natAdd 13 b then false else (fun i : Fin 26 => Fin.addCases (motive := fun _ => Bool) (fun v : Fin 13 => r.testBit (v-t).val) (fun v : Fin 13 => r.testBit (13+(v-t).val)) i) i) = false) → 56 ≤ C.size) : have x1 : List ℕ :=   have x1 : List ℕ :=     have x1 : List ℕ :=       have x1 : List ℕ := [(21496089 : ℕ), (17318185 : ℕ), (20988233 : ℕ), (21004625 : ℕ), (17891877 : ℕ)];       (6308041 : ℕ) :: (21512457 : ℕ) :: (21528849 : ℕ) :: (4751635 : ℕ) :: x1;     have x2 : List ℕ := (6619269 : ℕ) :: (6357127 : ℕ) :: (6570121 : ℕ) :: (6553741 : ℕ) :: (6324419 : ℕ) :: x1;     (19939425 : ℕ) :: (19923045 : ℕ) :: (18890857 : ℕ) :: (6389891 : ℕ) :: x2;   have x2 : List ℕ :=     have x2 : List ℕ := (23085129 : ℕ) :: (23068749 : ℕ) :: (22052945 : ℕ) :: (5275731 : ℕ) :: (22020181 : ℕ) :: x1;     (19415081 : ℕ) :: (7372867 : ℕ) :: (24117317 : ℕ) :: (7340103 : ℕ) :: x2;   have x3 : List ℕ := (21757977 : ℕ) :: (21233693 : ℕ) :: (3735587 : ℕ) :: (19988517 : ℕ) :: (3211303 : ℕ) :: x2;   (7405575 : ℕ) :: (23330829 : ℕ) :: (5799955 : ℕ) :: (22282261 : ℕ) :: x3; ¬∃ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 ∧ x2.size ≤ (63 : ℕ) ∧ x2.output + (1 : ℕ) = (26 : ℕ) + x2.size ∧ (∀ x3 ∈ x2.gates.zipIdx, ∀ x5 ∈ x3.1.inputs, x5 < (26 : ℕ) + x3.2 ∨ x5 = (89 : ℕ)) ∧ ¬PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x2 (1 : ℕ) ∧ ¬PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.range (13 : ℕ)) x2 (1 : ℕ) ∧ (∀ (x3 x4 : Fin (13 : ℕ)), x4 = (0 : Fin (13 : ℕ)) ∨ x4 = (1 : Fin (13 : ℕ)) ∨ x4 = (3 : Fin (13 : ℕ)) ∨ x4 = (9 : Fin (13 : ℕ)) → (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 fun (x6 : Fin (26 : ℕ)) => Decidable.decide (x6 = Fin.castAdd (13 : ℕ) (x3 + x4) ∨ x6 = Fin.natAdd (13 : ℕ) x3)) = Bool.true) ∧ ∀ x3 ∈ x1, ∀ (x5 : Fin (13 : ℕ)), (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 fun (x6 : Fin (26 : ℕ)) => Decidable.decide ((∃ (x7 : Fin (13 : ℕ)), x3.testBit ↑(x7 - x5) = Bool.true ∧ x6 = Fin.castAdd (13 : ℕ) x7) ∨ ∃ (x7 : Fin (13 : ℕ)), x3.testBit ((13 : ℕ) + ↑(x7 - x5)) = Bool.true ∧ x6 = Fin.natAdd (13 : ℕ) x7)) = Bool.false := by
  -- The input-monotonicity argument from L_meta_9153 keeps all rejection tests valid after projection.
  let wf (gs : List Gate) (w : List Bool) : List Bool :=
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

  have getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
      (L ++ [a]).getD w false = L.getD w false := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

  have getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
    simp [List.getD_eq_getElem?_getD]

  have getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
      (L ++ [a]).getD w false = false := by
    rw [List.getD_eq_default]; simp; omega

  have eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (ins : List ℕ)
      (U V : List Bool) (h : ∀ i, U.getD i false = true → V.getD i false = true) :
      op.eval (ins.map fun i => U.getD i false) = true →
      op.eval (ins.map fun i => V.getD i false) = true := by
    rcases hop with rfl | rfl
    · change (ins.map fun i => U.getD i false).all id = true → (ins.map fun i => V.getD i false).all id = true
      simp only [List.all_map, List.all_eq_true, Function.comp, id]
      exact fun hall i hi => h i (hall i hi)
    · change (ins.map fun i => U.getD i false).any id = true → (ins.map fun i => V.getD i false).any id = true
      simp only [List.any_map, List.any_eq_true, Function.comp, id]
      rintro ⟨i, hi, hv⟩
      exact ⟨i,hi,h i hv⟩

  have ofFn_mono (n : ℕ) (x y : Fin n → Bool) (hxy : ∀ v : Fin n, x v = true → y v = true)
      (w : ℕ) : (List.ofFn x).getD w false = true → (List.ofFn y).getD w false = true := by
    by_cases hw : w < n
    · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, dite_true, Option.getD_some]
      exact hxy ⟨w, hw⟩
    · rw [List.getD_eq_default _ _ (by simp; omega)]
      simp

  have wf_cons (g : Gate) (gs : List Gate) (w : List Bool) :
      wf (g :: gs) w = wf gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

  have monoW : ∀ (gs : List Gate), (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
      ∀ U V : List Bool, U.length = V.length → (∀ i, U.getD i false = true → V.getD i false = true) →
      ∀ i, (wf gs U).getD i false = true → (wf gs V).getD i false = true := by
    intro gs
    induction gs with
    | nil => intro _ U V _ h i; exact h i
    | cons g t ih =>
      intro hop U V hlen hUV i
      rw [wf_cons, wf_cons]
      refine ih (fun g' hg' => hop g' (List.mem_cons_of_mem _ hg')) _ _ (by simp [hlen]) ?_ i
      intro j hj
      rcases Nat.lt_trichotomy j U.length with hj' | hj' | hj'
      · rw [getD_snoc_lt _ _ _ hj'] at hj
        rw [getD_snoc_lt _ _ _ (by omega)]
        exact hUV j hj
      · rw [hj', getD_snoc_eq] at hj
        rw [hj', hlen, getD_snoc_eq]
        exact eval_mono g.op (hop g (List.mem_cons_self ..)) g.inputs U V hUV hj
      · rw [getD_snoc_gt _ _ _ hj'] at hj
        exact absurd hj (by simp)

  intro rows
  rintro ⟨C,mono,size,_,_,ld,pd,hits,miss⟩
  let code (j : Fin 36) := ((154864532458776913328923231818436173642350964167816379617494761446708840970305666064333610980186298862096319296411637866322823066651732813787683520215880584087994696174523727794542474942805109892481093000432148714521561784232086750948867262360411163194590501214779416935824884826119 : ℕ) >>> (26*j.val)) % 67108864
  have member : ∀ j : Fin 36, code j ∈ rows := by decide +kernel
  let flag (u v : Fin 13) (i : Fin 26) := decide (i=Fin.castAdd 13 u ∨ i=Fin.natAdd 13 v)
  have flagEq : ∀ u v : Fin 13, List.ofFn (flag u v) = incidenceInput {u} {v} := by decide +kernel
  have diff : ∀ u v : Fin 13, u ∈ singerLines3 v → u-v=0 ∨ u-v=1 ∨ u-v=3 ∨ u-v=9 := by decide +kernel
  have positive (u v : Fin 13) (h : u ∈ singerLines3 v) : C.eval (incidenceInput {u} {v}) = true := by
    rw [←flagEq]
    have z := hits v (u-v) (diff u v h)
    have cancel : v + (u-v) = u := by abel
    change C.eval (List.ofFn (flag (v+(u-v)) v)) = true at z
    rw [cancel] at z
    exact z
  let row (r : Nat) (t : Fin 13) : Fin 26 → Bool := (fun i : Fin 26 => Fin.addCases (motive := fun _ => Bool) (fun v : Fin 13 => r.testBit (v-t).val) (fun v : Fin 13 => r.testBit (13+(v-t).val)) i)
  have leftRight : ∀ c d : Fin 13, Fin.castAdd 13 c ≠ Fin.natAdd 13 d := by decide +kernel
  have rightLeft : ∀ c d : Fin 13, Fin.natAdd 13 d ≠ Fin.castAdd 13 c := fun c d => (leftRight c d).symm
  have castEq : ∀ c d : Fin 13, (Fin.castAdd 13 c = Fin.castAdd 13 d) ↔ c=d := by decide +kernel
  have natEq : ∀ c d : Fin 13, (Fin.natAdd 13 c = Fin.natAdd 13 d) ↔ c=d := by decide +kernel
  have negative (j : Fin 36) (t : Fin 13) : circuitFun 26 C (row (code j) t) = false := by
    have z := miss (code j) (member j) t
    convert z using 2
    funext i
    refine Fin.addCases (m := 13) (n := 13) (fun x => ?_) (fun y => ?_) i
    · simp only [row,Fin.addCases_left,castEq,leftRight,and_false,exists_false,or_false,exists_eq_right',Bool.decide_eq_true]
    · simp only [row,Fin.addCases_right,natEq,rightLeft,and_false,exists_false,false_or,exists_eq_right',Bool.decide_eq_true]
  obtain ⟨a,b,inc,moves,len,valid,agree⟩ := peel C mono size ld pd positive negative
  let edit := fun (A : Circuit) (e : ℕ × ℕ) => eraseGate 26 A e.1 e.2
  have erase {A : Circuit} (g t : ℕ) (hg : g < A.size) (hA : Monotone2 A) :
      (eraseGate 26 A g t).size + 1 = A.size ∧ Monotone2 (eraseGate 26 A g t) := by
    change g < A.gates.length at hg
    unfold eraseGate
    rw [ite_eq_left hg]
    constructor
    · change (A.gates.take g ++ (A.gates.drop (g+1)).map _).length + 1 = A.gates.length
      rw [List.length_append,List.length_take,List.length_map,List.length_drop,Nat.min_eq_left (Nat.le_of_lt hg)]
      omega
    · intro z hz
      simp only [List.mem_append,List.mem_map] at hz
      rcases hz with before | ⟨a,ha,rfl⟩
      · exact hA _ (List.mem_of_mem_take before)
      · obtain ⟨ops,len⟩ := hA _ (List.mem_of_mem_drop ha)
        exact ⟨ops,by simpa using len⟩
  have account (ms : List (ℕ × ℕ)) (A : Circuit) (ok : Monotone2 A)
      (bounds : ∀ i : Fin ms.length, (ms.get i).1 < A.size - i.val) :
      (ms.foldl edit A).size + ms.length = A.size ∧ Monotone2 (ms.foldl edit A) := by
    induction ms generalizing A with
    | nil => exact ⟨rfl,ok⟩
    | cons e es ih =>
      have h0 := bounds ⟨0,by simp⟩
      have one := erase (A:=A) e.1 e.2 (by simpa using h0) ok
      change (edit A e).size + 1 = A.size ∧ Monotone2 (edit A e) at one
      have tail (i : Fin es.length) : (es.get i).1 < (edit A e).size - i.val := by
        have b := bounds ⟨i.val+1,by simp⟩
        change (es.get i).1 < A.size - (i.val+1) at b
        have sz := one.1
        omega
      obtain ⟨cost,legalTail⟩ := ih (edit A e) one.2 tail
      exact ⟨by simpa only [List.foldl_cons,List.length_cons] using (show (es.foldl edit (edit A e)).size + (es.length+1) = A.size by omega),legalTail⟩
  obtain ⟨cost,legalD⟩ := account moves C mono valid
  apply Nat.not_lt_of_ge (puncture a b inc (moves.foldl edit C) legalD ?_ ?_) (by omega)
  · intro u v edge hu hv
    rw [←flagEq]
    have lo : flag u v (Fin.castAdd 13 a) = false := by simp only [flag,castEq,leftRight,hu.symm,or_false,decide_false]
    have hi : flag u v (Fin.natAdd 13 b) = false := by simp only [flag,natEq,rightLeft,hv.symm,false_or,decide_false]
    exact (agree _ lo hi).trans ((congrArg C.eval (flagEq u v)).trans (positive u v edge))
  · intro j rr t
    let n := row (code j) t
    let x : Fin 26 → Bool := fun i => if i = Fin.castAdd 13 a ∨ i = Fin.natAdd 13 b then false else n i
    have same := agree x (by simp [x]) (by simp [x])
    change circuitFun 26 (moves.foldl edit C) x = false
    rw [same]
    by_contra h
    have hx : circuitFun 26 C x = true := Bool.eq_true_of_not_eq_false h
    have hy : circuitFun 26 C n = true := monoW C.gates (fun g hg => (mono g hg).1)
        _ _ (by simp) (ofFn_mono 26 x n (by
          intro i hi
          by_cases hc : i = Fin.castAdd 13 a ∨ i = Fin.natAdd 13 b
          · exact (Bool.false_ne_true (by simpa only [x,ite_eq_left hc] using hi)).elim
          · simpa only [x,ite_eq_right hc] using hi)) C.output hx
    exact Bool.noConfusion (hy.symm.trans (negative j t))
