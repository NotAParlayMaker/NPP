import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_3120_317
    (checked2315 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → (∃ (x4 : Fin x1 → Bool) (x5 : Fin x1 → Bool), x2.eval (List.ofFn x4 ++ [Bool.false]) ≠ x2.eval (List.ofFn x5 ++ [Bool.false])) → (∃ (x5 : Fin x1 → Bool), x2.eval (List.ofFn x5 ++ [Bool.true]) ≠ x2.eval (List.ofFn x5 ++ [Bool.false])) → ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x6 ∧ x6.size < x2.size ∧ ∀ (x7 : Fin x1 → Bool), x6.eval (List.ofFn x7 ++ [Bool.false]) = x2.eval (List.ofFn x7 ++ [Bool.false]))
    (checked2331 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x3 : Fin (9 : ℕ) → Bool) => x3 (0 : Fin (9 : ℕ)) && x3 (1 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (2 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (3 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (4 : Fin (9 : ℕ)) || x3 (4 : Fin (9 : ℕ)) && x3 (0 : Fin (9 : ℕ)) || x3 (0 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (6 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (5 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (8 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ))) → (15 : ℕ) ≤ x1.size)
    (floor : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (PEqualNP.MetaComplexity.circuitFun (7 : ℕ) x1 = fun (x3 : Fin (7 : ℕ) → Bool) => [((0 : Fin (7 : ℕ)), (1 : Fin (7 : ℕ))), ((1 : Fin (7 : ℕ)), (2 : Fin (7 : ℕ))), ((0 : Fin (7 : ℕ)), (4 : Fin (7 : ℕ))), ((1 : Fin (7 : ℕ)), (5 : Fin (7 : ℕ))), ((2 : Fin (7 : ℕ)), (6 : Fin (7 : ℕ))), ((3 : Fin (7 : ℕ)), (5 : Fin (7 : ℕ))), ((4 : Fin (7 : ℕ)), (6 : Fin (7 : ℕ))), ((6 : Fin (7 : ℕ)), (3 : Fin (7 : ℕ)))].any fun (x4 : Fin (7 : ℕ) × Fin (7 : ℕ)) => x3 x4.1 && x3 x4.2) → (11 : ℕ) ≤ List.countP (fun (x4 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.true Bool.true Bool.false (fun (x5 : ℕ) => Bool.true) Bool.true x4.op) x1.gates) :
    ∀ x1 ∈ [(5 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))], ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x3 → (∀ (x5 : Fin (9 : ℕ) → Bool), x3.eval (List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ))] ++ [!x5 x1]) = (x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)))) → (14 : ℕ) ≤ x3.size := by
  let idx {m n : ℕ} (σ : Fin m → Option (Fin n)) (size i : ℕ) : ℕ :=
    if h : i<m then (σ ⟨i,h⟩).elim (n+size) Fin.val else n+(i-m)
  let mapG {m n : ℕ} (σ : Fin m → Option (Fin n)) (size : ℕ) (g : Gate) : Gate :=
    ⟨g.op,g.inputs.map (idx σ size)⟩
  let mapped {m n : ℕ} (σ : Fin m → Option (Fin n)) (C : Circuit) : Circuit :=
    ⟨C.gates.map (mapG σ C.size),idx σ C.size C.output⟩
  let pull {m n : ℕ} (σ : Fin m → Option (Fin n)) (x : Fin n → Bool) : Fin m → Bool :=
    fun k => (σ k).elim false x
  let tr (gs : List Gate) (w : List Bool) := gs.foldl (fun z g => z++[g.op.eval (g.inputs.map fun i => z.getD i false)]) w

  have getraw {n : ℕ} (x : Fin n → Bool) (k : Fin n) : (List.ofFn x).getD k.val false=x k := by
    simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,k.isLt,dif_pos,Option.getD_some]

  have getMapped {m n : ℕ} (σ : Fin m → Option (Fin n)) (x : Fin n → Bool) (size : ℕ)
      (extra : List Bool) (cap : extra.length≤size) (i : ℕ) :
      (List.ofFn x++extra).getD (idx σ size i) false = (List.ofFn (pull σ x)++extra).getD i false := by
    by_cases h : i<m
    · rw [List.getD_append (List.ofFn (pull σ x)) _ _ _ (by simpa using h)]
      have r := getraw (pull σ x) ⟨i,h⟩
      rw [r];simp only [idx,dif_pos h,pull]
      cases q : σ ⟨i,h⟩ with
      | none => exact List.getD_eq_default _ _ (by simp;omega)
      | some k =>
        change (List.ofFn x++extra).getD k.val false=x k
        rw [List.getD_append _ _ _ _ (by simpa using k.isLt),getraw]
    · rw [show idx σ size i=n+(i-m) by simp [idx,h],List.getD_append_right _ _ _ _ (by simp),
          List.getD_append_right _ _ _ _ (by simp;omega)]
      simp

  have traceMapped {m n : ℕ} (σ : Fin m → Option (Fin n)) (x : Fin n → Bool) (size : ℕ)
      (gs : List Gate) (extra : List Bool) (cap : extra.length+gs.length≤size) :
      ∃ out, out.length=extra.length+gs.length ∧
        tr (gs.map (mapG σ size)) (List.ofFn x++extra) = List.ofFn x++out ∧
        tr gs (List.ofFn (pull σ x)++extra) = List.ofFn (pull σ x)++out := by
    induction gs generalizing extra with
    | nil => exact ⟨extra,by simp,rfl,rfl⟩
    | cons g gs ih =>
      let a := g.op.eval (g.inputs.map fun i => (List.ofFn (pull σ x)++extra).getD i false)
      have f : (mapG σ size g).op.eval ((mapG σ size g).inputs.map fun i => (List.ofFn x++extra).getD i false)=a := by
        simp only [a,mapG,List.map_map]
        congr 1
        exact List.map_congr_left (fun i _ => getMapped σ x size extra (by omega) i)
      obtain ⟨o,l,left,right⟩ := ih (extra++[a]) (by simp at cap ⊢;omega)
      refine ⟨o,by simp at l ⊢;omega,?_,?_⟩
      · change tr _ ((List.ofFn x++extra)++[_])=_
        rw [f,List.append_assoc];exact left
      · change tr _ ((List.ofFn (pull σ x)++extra)++[a])=_
        rw [List.append_assoc];exact right

  have mapped_eval {m n : ℕ} (σ : Fin m → Option (Fin n)) (C : Circuit) (x : Fin n → Bool) :
      (mapped σ C).eval (List.ofFn x) = C.eval (List.ofFn (pull σ x)) := by
    obtain ⟨o,len,l,r⟩ := traceMapped σ x C.size C.gates [] (by change 0+C.gates.length ≤ C.gates.length; omega)
    simp only [List.append_nil,List.length_nil,Nat.zero_add] at len l r
    change (tr (C.gates.map (mapG σ C.size)) (List.ofFn x)).getD _ false = (tr C.gates _).getD _ false
    rw [l,r];exact getMapped σ x C.size o (by change o.length≤C.gates.length;omega) C.output
  have mapped_size {m n : ℕ} (σ : Fin m → Option (Fin n)) (C : Circuit) : (mapped σ C).size=C.size := by change (C.gates.map _).length = C.gates.length; exact List.length_map _
  have mapped_fan {m n : ℕ} (σ : Fin m → Option (Fin n)) (C : Circuit) (h : FanInTwo C) : FanInTwo (mapped σ C) := by
    intro g hg
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp (show g∈C.gates.map (mapG σ C.size) from hg)
    simpa [mapG] using h t ht

  let dropLast (n : ℕ) (i : Fin (n+1)) : Option (Fin n) := if h : i.val<n then some ⟨i,h⟩ else none
  have ofDrop {n : ℕ} (x : Fin n → Bool) : List.ofFn (pull (dropLast n) x) = List.ofFn x ++ [false] := by
    rw [List.ofFn_succ']
    rw [List.concat_eq_append]
    congr 1
    · apply congrArg List.ofFn;funext i;simp [pull,dropLast,i.isLt]
    · simp [pull,dropLast]

  let prependNot (C : Circuit) (j : ℕ) : Circuit := ⟨⟨.not,[j]⟩::C.gates,C.output⟩
  have pre_eval {n : ℕ} (C : Circuit) (j : Fin n) (x : Fin n → Bool) :
      (prependNot C j.val).eval (List.ofFn x) = C.eval (List.ofFn x++[!x j]) := by
    change (tr C.gates (List.ofFn x++[GateOp.not.eval ([j.val].map fun i => (List.ofFn x).getD i false)])).getD C.output false=_
    change (tr C.gates (List.ofFn x++[!((List.ofFn x).getD j.val false)])).getD C.output false=_
    rw [getraw]
    rfl
  have pre_fan (C : Circuit) (j : ℕ) (h : FanInTwo C) : FanInTwo (prependNot C j) := by
    intro g hg
    rcases List.mem_cons.mp (show g∈(⟨.not,[j]⟩ : Gate)::C.gates from hg) with rfl|m
    · simp
    · exact h g m
  have pre_size (C : Circuit) (j : ℕ) : (prependNot C j).size=C.size+1 := rfl

  let PinReducible : Prop := ∀ (n : ℕ) (C : Circuit), FanInTwo C →
      (∃ x y : Fin n → Bool, C.eval (List.ofFn x++[false])≠C.eval (List.ofFn y++[false])) →
      (∃ x : Fin n → Bool, C.eval (List.ofFn x++[true])≠C.eval (List.ofFn x++[false])) →
      ∃ D : Circuit, FanInTwo D ∧ D.size<C.size ∧ ∀ x : Fin n → Bool,
        D.eval (List.ofFn x++[false])=C.eval (List.ofFn x++[false])

  have vecOfLength {n : ℕ} (xs : List Bool) (len : xs.length=n) :
      ∃ f : Fin n → Bool, List.ofFn f=xs := by
    subst n; exact ⟨xs.get,by simp⟩

  have pin (rule : PinReducible) (n : ℕ) (C : Circuit) (ok : FanInTwo C)
      (vary : ∃ a b : List Bool, a.length=n ∧ b.length=n ∧ C.eval (a++[false])≠C.eval (b++[false]))
      (sens : ∃ a : List Bool, a.length=n ∧ C.eval (a++[true])≠C.eval (a++[false])) :
      ∃ D : Circuit, FanInTwo D ∧ D.size<C.size ∧ ∀ xs : List Bool, xs.length=n → D.eval xs = C.eval (xs++[false]) := by
    obtain ⟨a,b,al,bl,ne⟩ := vary
    obtain ⟨af,rfl⟩ := vecOfLength a al
    obtain ⟨bf,rfl⟩ := vecOfLength b bl
    obtain ⟨c,cl,diff⟩ := sens
    obtain ⟨cf,rfl⟩ := vecOfLength c cl
    obtain ⟨D,df,dl,ev⟩ := rule n C ok ⟨af,bf,ne⟩ ⟨cf,diff⟩
    refine ⟨mapped (dropLast n) D,mapped_fan _ _ df,by rwa [mapped_size],?_⟩
    intro xs xlen
    obtain ⟨x,rfl⟩ := vecOfLength xs xlen
    rw [mapped_eval,ofDrop,ev]

  let graph (x : Fin 9 → Bool) := x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5
  let theta (z : Fin 7 → Bool) := z 0 && z 1 || z 1 && z 2 || z 0 && z 4 ||
    z 1 && z 5 || z 2 && z 6 || z 3 && z 5 || z 4 && z 6 || z 6 && z 3
  let core (j : Fin 9) (x : Fin 9 → Bool) := [x 1,x 2,x 3,x 5,x 6,x 7,x 8,!x j]
  let pack (j : Fin 9) (x : Fin 9 → Bool) := core j x ++ [x 0,x 4]
  let rot : Fin 11 → Option (Fin 11) := ![some 8,some 0,some 1,some 2,some 9,some 3,some 4,some 5,some 6,some 10,some 7]
  let foldH : Fin 11 → Option (Fin 10) := ![some 1,some 2,some 3,some 5,some 6,some 7,some 8,some 9,some 0,some 4,none]
  let rotateEval (j : Fin 9) (x : Fin 9 → Bool) (h : Bool) : Fin 11 → Bool :=
    ![x 1,x 2,x 3,x 5,x 6,x 7,x 8,!x j,x 0,x 4,h]
  let withNot (j : Fin 9) (x : Fin 9 → Bool) : Fin 10 → Bool := ![x 0,x 1,x 2,x 3,x 4,x 5,x 6,x 7,x 8,!x j]
  let restore (j : Fin 9) (z : Fin 7 → Bool) : Fin 9 → Bool := if j=5 then
    ![false,z 0,z 1,z 2,false,z 3,z 4,z 5,z 6] else ![false,z 5,z 1,z 2,false,z 4,z 3,z 0,z 6]
  let finalMap (j : Fin 9) : Fin 8 → Option (Fin 8) := if j=5 then fun i => some i else
    ![some 5,some 1,some 2,some 4,some 3,some 0,some 6,some 7]
  let post (z : Fin 7 → Bool) : Fin 8 → Bool := ![z 0,z 1,z 2,z 3,z 4,z 5,z 6,!z 3]
  let sample (m : ℕ) (i : Fin 9) := m.testBit i.val

  have geometry (j : Fin 9) (hj : j∈([5,6]:List (Fin 9))) (z : Fin 7 → Bool) :
      (restore j z) 0=false ∧ (restore j z) 4=false ∧ graph (restore j z)=theta z ∧
      List.ofFn (pull (finalMap j) (post z)) = core j (restore j z) := by
    revert z j; decide +kernel

  have triple (rule : PinReducible)
      (lower : ∀ C : Circuit, FanInTwo C → circuitFun 9 C=graph → 15≤C.size)
      (j : Fin 9) (hj : j ∈ ([5,6] : List (Fin 9))) (C : Circuit) (legal : FanInTwo C) (cap : C.size≤13)
      (correct : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x++[x 0 && x 3]++[!x j])=graph x) :
      ∃ B : Circuit, FanInTwo B ∧ B.size≤10 ∧ ∀ z : Fin 7 → Bool, B.eval (List.ofFn z++[!z 3])=theta z := by
    let A := mapped rot C
    have okA : FanInTwo A := mapped_fan rot C legal
    have sizeA : A.size=C.size := mapped_size rot C
    have start (x : Fin 9 → Bool) : A.eval (pack j x++[x 0 && x 3])=graph x := by
      have e := mapped_eval rot C (rotateEval j x (x 0 && x 3))
      exact e.trans (correct x)
    have eq0 (x : Fin 9 → Bool) (zero : (x 0 && x 3)=false) :
        A.eval (pack j x++[false])=graph x := by simpa only [zero] using start x
    have sensitive : ∃ a : List Bool, a.length=10 ∧ A.eval (a++[true])≠A.eval (a++[false]) := by
      by_contra! absent
      have grounded (x : Fin 9 → Bool) : A.eval (pack j x++[false])=graph x := by
        cases e : x 0 && x 3 with
        | false => exact eq0 x e
        | true => have h := absent (pack j x) (by simp [pack,core]);rw [←h,←e];exact start x
      let D := mapped foldH A
      have agrees (x : Fin 9 → Bool) : (prependNot D j.val).eval (List.ofFn x)=graph x := by
        rw [pre_eval]
        have e := mapped_eval foldH A (withNot j x)
        exact e.trans (grounded x)
      have lb := lower (prependNot D j.val) (pre_fan _ _ (mapped_fan foldH A okA)) (funext agrees)
      rw [pre_size,mapped_size] at lb
      omega
    let o := sample 0
    let e12 := sample 6
    have vary : ∃ a b : List Bool, a.length=10 ∧ b.length=10 ∧ A.eval (a++[false])≠A.eval (b++[false]) := by
      refine ⟨pack j o,pack j e12,by simp [pack,core],by simp [pack,core],?_⟩
      rw [eq0 o rfl,eq0 e12 rfl]; decide
    obtain ⟨D,dok,ds,de⟩ := pin rule 10 A okA vary sensitive
    have deq (x : Fin 9 → Bool) (zero : (x 0 && x 3)=false) :
        D.eval (pack j x)=graph x := (de _ (by simp [pack,core])).trans (eq0 x zero)
    let p9 (x : Fin 9 → Bool) := core j x++[x 0]
    have diff4 : ∃ a : List Bool, a.length=9 ∧ D.eval (a++[true])≠D.eval (a++[false]) := by
      refine ⟨p9 (sample 1),by simp [p9,core],?_⟩
      have left : p9 (sample 1)++[true] = pack j (sample 17) := by simp only [List.mem_cons,List.not_mem_nil,or_false] at hj;rcases hj with rfl|rfl <;> rfl
      rw [left]
      change D.eval (pack j (sample 17)) ≠ D.eval (pack j (sample 1))
      rw [deq _ rfl,deq _ rfl];decide
    have var4 : ∃ a b : List Bool, a.length=9 ∧ b.length=9 ∧ D.eval (a++[false])≠D.eval (b++[false]) := by
      refine ⟨p9 o,p9 e12,by simp [p9,core],by simp [p9,core],?_⟩
      change D.eval (pack j o) ≠ D.eval (pack j e12)
      rw [deq _ rfl,deq _ rfl];decide
    obtain ⟨E,eok,es,ee⟩ := pin rule 9 D dok var4 diff4
    have eeq (x : Fin 9 → Bool) (four : x 4=false) (zero : (x 0 && x 3)=false) :
        E.eval (p9 x)=graph x := by
      rw [ee _ (by simp [p9,core])]
      have h : p9 x++[false] = pack j x := by simp [p9,pack,List.append_assoc,four]
      rw [h];exact deq _ zero
    have diff0 : ∃ a : List Bool, a.length=8 ∧ E.eval (a++[true])≠E.eval (a++[false]) := by
      refine ⟨core j (sample 2),by simp [core],?_⟩
      have left : core j (sample 2)++[true] = p9 (sample 3) := by simp only [List.mem_cons,List.not_mem_nil,or_false] at hj;rcases hj with rfl|rfl <;> rfl
      rw [left]
      change E.eval (p9 (sample 3)) ≠ E.eval (p9 (sample 2))
      rw [eeq _ rfl rfl,eeq _ rfl rfl];decide
    have var0 : ∃ a b : List Bool, a.length=8 ∧ b.length=8 ∧ E.eval (a++[false])≠E.eval (b++[false]) := by
      refine ⟨core j o,core j e12,by simp [core],by simp [core],?_⟩
      change E.eval (p9 o) ≠ E.eval (p9 e12)
      rw [eeq _ rfl rfl,eeq _ rfl rfl];decide
    obtain ⟨B,bok,bs,be⟩ := pin rule 8 E eok var0 diff0
    refine ⟨mapped (finalMap j) B,mapped_fan _ B bok,by rw [mapped_size];omega,?_⟩
    intro z
    obtain ⟨h0,h4,goal,hp⟩ := geometry j hj z
    have rw0 := mapped_eval (finalMap j) B (post z)
    change (mapped (finalMap j) B).eval (List.ofFn (post z))=theta z
    rw [rw0,hp,be _ (by simp [core])]
    have last : core j (restore j z)++[false] = p9 (restore j z) := by simp [p9,h0]
    rw [last,eeq _ h4 (by simp [h0]),goal]
  intro j hj C legal correct
  by_contra! cap
  obtain ⟨B,ok,sz,agree⟩ := triple checked2315 checked2331 j hj C legal (by omega) correct
  let D : Circuit := ⟨⟨.not,[3]⟩::B.gates,B.output⟩
  have dlegal : FanInTwo D := by
    intro g hg
    rcases List.mem_cons.mp (show g∈(⟨.not,[3]⟩ : Gate)::B.gates from hg) with rfl|h
    · simp
    · exact ok g h
  have formula (z : Fin 7 → Bool) : D.eval (List.ofFn z) = B.eval (List.ofFn z++[!z 3]) := by
    exact pre_eval B (3 : Fin 7) z
  have lb := floor D dlegal (by
    funext z
    change D.eval (List.ofFn z) = _
    rw [formula,agree]
    simp only [theta,List.any_cons,List.any_nil,Bool.or_false,Bool.or_assoc])
  change 11 ≤ B.gates.countP _ at lb
  have ub := List.countP_le_length (l := B.gates) (p := fun g =>
    GateOp.rec true true false (fun _ => true) true g.op)
  change B.gates.length ≤ 10 at sz
  omega
