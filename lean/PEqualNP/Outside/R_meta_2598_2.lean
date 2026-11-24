import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 16000 in
set_option maxHeartbeats 14000000 in
theorem PEqualNP.Outside.R_meta_2598_2
    (dropCase : ∀ C : Circuit, FanInTwo C → C.size ≤ 17 → ∃ x : Fin 10 → Bool,
      C.eval (List.ofFn x ++ [!x 0, false, true]) ≠ (fun x : Fin 10 → Bool => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 || x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5) x)
    (andCase : ∀ (C : Circuit) (p : Fin 121), p ∈ [1, 2, 13, 14, 15, 21, 25, 28, 30, 32] →
      FanInTwo C → C.size ≤ 17 → ∃ x : Fin 10 → Bool,
        let w := List.ofFn x ++ [!x 0]
        C.eval (w ++ [w.getD (p.val / 11) false && w.getD (p.val % 11) false]) ≠ (fun x : Fin 10 → Bool => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 || x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5) x)
    (orCase : ∀ (C : Circuit) (p : Fin 121), p ∈ [1, 2, 13, 14, 15, 21, 25, 28, 30, 32] →
      FanInTwo C → C.size ≤ 17 → ∃ x : Fin 10 → Bool,
        let w := List.ofFn x ++ [!x 0]
        C.eval (w ++ [w.getD (p.val / 11) false || w.getD (p.val % 11) false]) ≠ (fun x : Fin 10 → Bool => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 || x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5) x)
    (notCase : ∀ (C : Circuit) (i : Fin 11), i ∈ [1, 2] →
      FanInTwo C → C.size ≤ 17 → ∃ x : Fin 10 → Bool,
        let w := List.ofFn x ++ [!x 0]
        C.eval (w ++ [!(w.getD i.val false)]) ≠ (fun x : Fin 10 → Bool => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 || x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5) x) :
  ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) → ∃ (x4 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x4 ++ [!x4 (0 : Fin (10 : ℕ))]) ≠ (fun (x5 : Fin (10 : ℕ) → Bool) => x5 (0 : Fin (10 : ℕ)) && x5 (1 : Fin (10 : ℕ)) || x5 (1 : Fin (10 : ℕ)) && x5 (2 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ)) && x5 (3 : Fin (10 : ℕ)) || x5 (3 : Fin (10 : ℕ)) && x5 (4 : Fin (10 : ℕ)) || x5 (4 : Fin (10 : ℕ)) && x5 (0 : Fin (10 : ℕ)) || x5 (0 : Fin (10 : ℕ)) && x5 (5 : Fin (10 : ℕ)) || x5 (1 : Fin (10 : ℕ)) && x5 (6 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ)) && x5 (7 : Fin (10 : ℕ)) || x5 (3 : Fin (10 : ℕ)) && x5 (8 : Fin (10 : ℕ)) || x5 (4 : Fin (10 : ℕ)) && x5 (9 : Fin (10 : ℕ)) || x5 (5 : Fin (10 : ℕ)) && x5 (7 : Fin (10 : ℕ)) || x5 (7 : Fin (10 : ℕ)) && x5 (9 : Fin (10 : ℕ)) || x5 (9 : Fin (10 : ℕ)) && x5 (6 : Fin (10 : ℕ)) || x5 (6 : Fin (10 : ℕ)) && x5 (8 : Fin (10 : ℕ)) || x5 (8 : Fin (10 : ℕ)) && x5 (5 : Fin (10 : ℕ))) x4 := by
  intro D fanD sizeD
  by_contra noWitness
  let target : (Fin 10 → Bool) → Bool := (fun x : Fin 10 → Bool => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 || x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5)
  let hint (x : Fin 10 → Bool) : Bool := !x 0
  let seed (x : Fin 10 → Bool) : List Bool := List.ofFn x ++ [hint x]
  have seedLength (x : Fin 10 → Bool) : (seed x).length = 11 := by simp [seed]
  have solves (x : Fin 10 → Bool) : D.eval (seed x) = target x := by
    by_contra bad
    exact noWitness ⟨x,bad⟩
  let lift (s : Fin 10 → Fin 10) (i : Fin 11) : Fin 11 :=
    if h : i.val < 10 then ⟨(s ⟨i.val,h⟩).val, Nat.lt_succ_of_lt (s ⟨i.val,h⟩).isLt⟩ else 10
  let source (x : Fin 10 → Bool) (i : Fin 11) : Bool :=
    if h : i.val < 10 then x ⟨i.val,h⟩ else hint x
  have readSeed (x : Fin 10 → Bool) (i : Fin 11) :
      (seed x).getD i.val false = source x i := by
    by_cases hi : i.val < 10
    · rw [show source x i = x ⟨i.val,hi⟩ by simp [source,hi]]
      change (List.ofFn x ++ [hint x]).getD i.val false = _
      rw [List.getD_append _ _ _ _ (by simpa using hi),
        List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_ofFn]
    · have hidx : i.val = 10 := by omega
      rw [show source x i = hint x by simp [source,hi]]
      change (List.ofFn x ++ [hint x]).getD i.val false = _
      rw [hidx, List.getD_append_right _ _ _ _ (by simp), List.length_ofFn, Nat.sub_self]
      rfl
  have readLift (s : Fin 10 → Fin 10) (x : Fin 10 → Bool) (i : Fin 11) :
      (seed x).getD (lift s i).val false =
        (List.ofFn (x ∘ s) ++ [hint x]).getD i.val false := by
    by_cases hi : i.val < 10
    · rw [readSeed]
      have ht : (s ⟨i.val,hi⟩).val < 10 := (s ⟨i.val,hi⟩).isLt
      simp only [lift, hi, dite_true, source, ht]
      rw [List.getD_append _ _ _ _ (by simpa using hi),
        List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_ofFn]
      rfl
    · have hidx : i.val = 10 := by omega
      rw [readSeed, show source x (lift s i) = hint x by simp [source,lift,hi], hidx,
        List.getD_append_right _ _ _ _ (by simp), List.length_ofFn, Nat.sub_self]
      rfl
  let reroute (n q : ℕ) (f : Fin n → Fin q) (i : ℕ) : ℕ :=
    if h : i < n then (f ⟨i,h⟩).val else q + (i - n)
  let mapGate (r : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op,g.inputs.map r⟩
  let mapCircuit (n q : ℕ) (f : Fin n → Fin q) (D : Circuit) : Circuit :=
    ⟨D.gates.map (mapGate (reroute n q f)), reroute n q f D.output⟩
  let step (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have reroute_lt (n q : ℕ) (f : Fin n → Fin q) (i t : ℕ) (hi : i < n + t) :
      reroute n q f i < q + t := by
    by_cases hn : i < n
    · have h := (f ⟨i,hn⟩).isLt
      simp [reroute,hn]
      omega
    · simp [reroute,hn]
      omega
  have fold_map (n q : ℕ) (f : Fin n → Fin q) (gs : List Gate) (t : ℕ)
      (old fresh : List Bool) (hold : old.length = n+t) (hfresh : fresh.length = q+t)
      (hread : ∀ i, fresh.getD (reroute n q f i) false = old.getD i false) :
      ∀ i, ((gs.map (mapGate (reroute n q f))).foldl step fresh).getD (reroute n q f i) false =
        (gs.foldl step old).getD i false := by
    induction gs generalizing t old fresh with
    | nil => exact hread
    | cons g gs ih =>
      simp only [List.map_cons, List.foldl_cons]
      apply ih (t+1)
      · simp [step,hold,Nat.add_assoc]
      · simp [step,hfresh,Nat.add_assoc]
      · intro i
        by_cases hi : i < n+t
        · change (fresh ++ [_]).getD (reroute n q f i) false = (old ++ [_]).getD i false
          rw [List.getD_append _ _ _ _ (by rw [hfresh]; exact reroute_lt n q f i t hi),
            List.getD_append _ _ _ _ (by omega)]
          exact hread i
        · have hn : ¬ i < n := by omega
          have hr : reroute n q f i = q + (i-n) := by simp [reroute,hn]
          have hnew : fresh.length ≤ reroute n q f i := by omega
          have hoff : reroute n q f i - fresh.length = i - old.length := by omega
          change (fresh ++ [_]).getD (reroute n q f i) false = (old ++ [_]).getD i false
          rw [List.getD_append_right _ _ _ _ hnew,
            List.getD_append_right _ _ _ _ (by omega),hoff]
          have same : (mapGate (reroute n q f) g).op.eval
              ((mapGate (reroute n q f) g).inputs.map fun j => fresh.getD j false) =
              g.op.eval (g.inputs.map fun j => old.getD j false) := by
            simp only [mapGate,List.map_map]
            congr 1
            exact List.map_congr_left (fun j _ => hread j)
          rw [same]
  have mapEval (n q : ℕ) (f : Fin n → Fin q) (D : Circuit) (old fresh : List Bool)
      (hold : old.length = n) (hfresh : fresh.length = q)
      (he : ∀ i : Fin n, fresh.getD (f i).val false = old.getD i.val false) :
      (mapCircuit n q f D).eval fresh = D.eval old := by
    have hread (i : ℕ) : fresh.getD (reroute n q f i) false = old.getD i false := by
      by_cases hi : i < n
      · simpa [reroute,hi] using he ⟨i,hi⟩
      · have hnew : fresh.length ≤ reroute n q f i := by simp [reroute,hfresh,hi]
        rw [List.getD_eq_default _ _ hnew,List.getD_eq_default _ _ (by omega)]
    exact fold_map n q f D.gates 0 old fresh (by simpa using hold) (by simpa using hfresh) hread D.output
  have mapFan (n q : ℕ) (f : Fin n → Fin q) (D : Circuit) (hD : FanInTwo D) :
      FanInTwo (mapCircuit n q f D) := by
    intro g hg
    change g ∈ D.gates.map (mapGate (reroute n q f)) at hg
    obtain ⟨original,member,rfl⟩ := List.mem_map.mp hg
    simpa [mapGate] using hD original member
  have mapSize (n q : ℕ) (f : Fin n → Fin q) (D : Circuit) :
      (mapCircuit n q f D).size = D.size := by
    change (D.gates.map (mapGate (reroute n q f))).length = D.gates.length
    exact List.length_map _
  let perm (p : Fin 12) (i : Fin 10) : Fin 10 :=
    (((#[#[0,1,2,3,4,5,6,7,8,9],
      #[0,1,2,7,5,4,6,3,9,8],
      #[0,1,6,8,5,4,2,9,3,7],
      #[0,1,6,9,4,5,2,8,7,3],
      #[0,4,3,2,1,5,9,8,7,6],
      #[0,4,3,8,5,1,9,2,6,7],
      #[0,4,9,6,1,5,3,7,8,2],
      #[0,4,9,7,5,1,3,6,2,8],
      #[0,5,7,2,1,4,8,9,3,6],
      #[0,5,7,9,4,1,8,2,6,3],
      #[0,5,8,3,4,1,7,6,2,9],
      #[0,5,8,6,1,4,7,3,9,2]] : Array (Array (Fin 10)))[p.val]?.getD #[])[i.val]?).getD 0
  let pairReps : List (Fin 11 × Fin 11) := [(0,1), (0,2), (1,2), (1,3), (1,4), (1,10), (2,3), (2,6), (2,8), (2,10)]
  let notReps : List (Fin 11) := [1, 2]
  let pairCodes : List (Fin 121) := [1, 2, 13, 14, 15, 21, 25, 28, 30, 32]
  let encode (a b : Fin 11) : Fin 121 := Fin.ofNat 121 (11 * a.val + b.val)
  have validCode : ∀ a b : Fin 11, (a,b) ∈ pairReps → encode a b ∈ pairCodes := by
    decide +kernel
  have decode (a b : Fin 11) : (encode a b).val / 11 = a.val ∧ (encode a b).val % 11 = b.val := by
    have bounded : 11 * a.val + b.val < 121 := by omega
    change (11 * a.val + b.val) % 121 / 11 = a.val ∧
      (11 * a.val + b.val) % 121 % 11 = b.val
    rw [Nat.mod_eq_of_lt bounded]
    constructor <;> omega
  let complements (i j : Fin 11) : Prop := (i = 0 ∧ j = 10) ∨ (i = 10 ∧ j = 0)
  have align : ∀ i j : Fin 11, i ≠ j → ¬ complements i j → ∃ p : Fin 12,
      (lift (perm p) i,lift (perm p) j) ∈ pairReps ∨
      (lift (perm p) j,lift (perm p) i) ∈ pairReps := by decide +kernel
  have alignNot : ∀ i : Fin 11, i ≠ 0 → i ≠ 10 → ∃ p : Fin 12, lift (perm p) i ∈ notReps := by
    decide +kernel
  have preservesHint : ∀ (p : Fin 12) (x : Fin 10 → Bool), hint (x ∘ perm p) = hint x := by
    decide +kernel
  have preservesTarget : ∀ (p : Fin 12) (x : Fin 10 → Bool), target (x ∘ perm p) = target x := by
    decide +kernel
  have permSource (p : Fin 12) (x : Fin 10 → Bool) (i : Fin 11) :
      source x (lift (perm p) i) = source (x ∘ perm p) i := by
    rw [← readSeed, readLift, ← preservesHint p x]
    exact readSeed _ _
  let aMap (p : Fin 12) (i : Fin 12) : Fin 12 :=
    if h : i.val < 11 then ⟨(lift (perm p) ⟨i.val,h⟩).val, Nat.lt_succ_of_lt (lift (perm p) ⟨i.val,h⟩).isLt⟩ else 11
  have seedAppLength (x : Fin 10 → Bool) (b : Bool) : (seed x ++ [b]).length = 12 := by
    simp [seedLength]
  have evalPerm (p : Fin 12) (T : Circuit) (x : Fin 10 → Bool) (b : Bool) :
      (mapCircuit 12 12 (aMap p) T).eval (seed x ++ [b]) = T.eval (seed (x ∘ perm p) ++ [b]) := by
    apply mapEval 12 12 (aMap p) T _ _ (seedAppLength _ _) (seedAppLength _ _)
    intro i
    by_cases hi : i.val < 11
    · let j : Fin 11 := ⟨i.val,hi⟩
      have hj : (lift (perm p) j).val < 11 := (lift (perm p) j).isLt
      rw [show (aMap p i).val = (lift (perm p) j).val by simp [aMap,hi,j],
        List.getD_append (seed x) [b] false _ (by rw [seedLength]; exact hj),
        List.getD_append (seed (x ∘ perm p)) [b] false _ (by rw [seedLength]; exact hi)]
      exact (readSeed x _).trans ((permSource p x j).trans (readSeed _ j).symm)
    · have hidx : i.val = 11 := by omega
      rw [show (aMap p i).val = 11 by simp [aMap,hi],hidx,
          List.getD_append_right _ _ _ _ (by simp [seedLength]),
          List.getD_append_right _ _ _ _ (by simp [seedLength])]
      simp [seedLength]
  let bin (op : Bool) (u v : Bool) : Bool := if op then u || v else u && v
  have binComm (op u v : Bool) : bin op u v = bin op v u := by
    cases op <;> simp [bin,Bool.or_comm,Bool.and_comm]
  have excludeBin (op : Bool) (T : Circuit) (fanT : FanInTwo T) (sizeT : T.size ≤ 17)
      (i j : Fin 11) (hij : i ≠ j) (noncomplement : ¬ complements i j)
      (he : ∀ x : Fin 10 → Bool, T.eval (seed x ++ [bin op (source x i) (source x j)]) = target x) : False := by
    obtain ⟨p,hp⟩ := align i j hij noncomplement
    let E := mapCircuit 12 12 (aMap p) T
    have fanE := mapFan 12 12 (aMap p) T fanT
    have sizeE : E.size ≤ 17 := by simpa [E,mapSize] using sizeT
    have goal (k l : Fin 11) (hkl : (k,l) ∈ pairReps)
        (e : ∀ x : Fin 10 → Bool, bin op (source x k) (source x l) =
          bin op (source (x ∘ perm p) i) (source (x ∘ perm p) j)) : False := by
      have yes (x : Fin 10 → Bool) : E.eval (seed x ++ [bin op (source x k) (source x l)]) = target x := by
        rw [e]
        exact (evalPerm p T x _).trans ((he _).trans (preservesTarget p x))
      cases op
      · obtain ⟨x,hx⟩ := andCase E (encode k l) (validCode k l hkl) fanE sizeE
        apply hx
        change E.eval (seed x ++ [(seed x).getD ((encode k l).val / 11) false &&
          (seed x).getD ((encode k l).val % 11) false]) = target x
        rw [(decode k l).1,(decode k l).2,readSeed,readSeed]
        exact yes x
      · obtain ⟨x,hx⟩ := orCase E (encode k l) (validCode k l hkl) fanE sizeE
        apply hx
        change E.eval (seed x ++ [(seed x).getD ((encode k l).val / 11) false ||
          (seed x).getD ((encode k l).val % 11) false]) = target x
        rw [(decode k l).1,(decode k l).2,readSeed,readSeed]
        exact yes x
    rcases hp with hp | hp
    · exact goal _ _ hp (by intro x; rw [permSource,permSource])
    · exact goal _ _ hp (by intro x; rw [permSource,permSource,binComm])
  have excludeNot (T : Circuit) (fanT : FanInTwo T) (sizeT : T.size ≤ 17) (i : Fin 11)
      (nonzero : i ≠ 0) (notHint : i ≠ 10)
      (he : ∀ x : Fin 10 → Bool, T.eval (seed x ++ [!source x i]) = target x) : False := by
    obtain ⟨p,hp⟩ := alignNot i nonzero notHint
    let E := mapCircuit 12 12 (aMap p) T
    obtain ⟨x,hx⟩ := notCase E (lift (perm p) i) hp (mapFan _ _ _ _ fanT)
      (by simpa [E,mapSize] using sizeT)
    have yes : E.eval (seed x ++ [!source x (lift (perm p) i)]) = target x := by
      rw [permSource]
      exact (evalPerm p T x _).trans ((he _).trans (preservesTarget p x))
    apply hx
    change E.eval (seed x ++ [!(seed x).getD (lift (perm p) i).val false]) = target x
    rw [readSeed]
    exact yes
  let constants (x : Fin 10 → Bool) := seed x ++ [false,true]
  let aliasWire (a : Fin 13) (i : Fin 12) : Fin 13 :=
    if h : i.val < 11 then ⟨i.val,by omega⟩ else a
  have excludeDrop (T : Circuit) (fanT : FanInTwo T) (sizeT : T.size ≤ 17) (a : Fin 13)
      (he : ∀ x : Fin 10 → Bool,
        T.eval (seed x ++ [(constants x).getD a.val false]) = target x) : False := by
    let E := mapCircuit 12 13 (aliasWire a) T
    obtain ⟨x,hx⟩ := dropCase E (mapFan _ _ _ _ fanT) (by simpa [E,mapSize] using sizeT)
    have eq : E.eval (constants x) = T.eval (seed x ++ [(constants x).getD a.val false]) := by
      apply mapEval 12 13 (aliasWire a) T _ _ (seedAppLength _ _) (by simp [constants,seedLength])
      intro i
      by_cases hi : i.val < 11
      · rw [show (aliasWire a i).val = i.val by simp [aliasWire,hi]]
        exact (List.getD_append _ _ _ _ (by rw [seedLength]; exact hi)).trans
          (List.getD_append _ _ _ _ (by rw [seedLength]; exact hi)).symm
      · have hidx : i.val = 11 := by omega
        rw [show aliasWire a i = a by simp [aliasWire,hi],hidx]
        rw [List.getD_append_right (seed x) [(constants x).getD a.val false] false 11
          (by rw [seedLength]),seedLength,Nat.sub_self]
        rfl
    exact hx (eq.trans (he x))
  have readConstant (x : Fin 10 → Bool) (i : Fin 11) :
      (constants x).getD i.val false = source x i := by
    have eq := List.getD_append (seed x) [false,true] false i.val (by rw [seedLength]; exact i.isLt)
    exact eq.trans (readSeed x i)
  have readFalse (x : Fin 10 → Bool) : (constants x).getD (11 : Fin 13).val false = false := by
    change (constants x).getD 11 false = false
    rw [show constants x = seed x ++ [false,true] from rfl,
      List.getD_append_right _ _ _ _ (by simp [seedLength]),seedLength,Nat.sub_self]
    rfl
  have readTrue (x : Fin 10 → Bool) : (constants x).getD (12 : Fin 13).val false = true := by
    change (constants x).getD 12 false = true
    rw [show constants x = seed x ++ [false,true] from rfl,
      List.getD_append_right _ _ _ _ (by simp [seedLength]),seedLength]
    rfl
  let witnessA : Fin 10 → Bool := fun i => decide (i = 3 ∨ i = 4)
  let witnessB : Fin 10 → Bool := fun i => decide (i = 6 ∨ i = 8)
  have outA : target witnessA = true := by decide
  have outB : target witnessB = true := by decide
  let witnessZ : Fin 10 → Bool := fun _ => false
  have outZ : target witnessZ = false := by decide
  have noWire : ∀ i : Fin 11, i = 10 ∨ source witnessA i = false ∨ source witnessB i = false := by
    decide +kernel
  cases hg : D.gates with
  | nil =>
    have noGate (x : Fin 10 → Bool) : (seed x).getD D.output false = target x := by
      have hx := solves x
      change (D.gates.foldl step (seed x)).getD D.output false = target x at hx
      rw [hg,List.foldl_nil] at hx
      exact hx
    by_cases ho : D.output < 11
    · let i : Fin 11 := ⟨D.output,ho⟩
      rcases noWire i with hz | hz | hz
      · have ok := noGate witnessZ
        change (seed witnessZ).getD i.val false = _ at ok
        rw [readSeed,hz,outZ] at ok
        exact Bool.false_ne_true (show true = false from ok).symm
      · have ok := noGate witnessA
        change (seed witnessA).getD i.val false = _ at ok
        rw [readSeed,hz,outA] at ok
        contradiction
      · have ok := noGate witnessB
        change (seed witnessB).getD i.val false = _ at ok
        rw [readSeed,hz,outB] at ok
        contradiction
    · have ok := noGate witnessA
      rw [List.getD_eq_default _ _ (by rw [seedLength]; omega),outA] at ok
      contradiction
  | cons g gs =>
    let T : Circuit := ⟨gs,D.output⟩
    have fanT : FanInTwo T := by
      intro q hq
      exact fanD q (by rw [hg]; exact List.mem_cons_of_mem _ hq)
    have sizeT : T.size ≤ 17 := by
      change D.gates.length ≤ 18 at sizeD
      rw [hg,List.length_cons] at sizeD
      change gs.length ≤ 17
      omega
    have allowed : g.op = .and ∨ g.op = .or ∨ g.op = .not :=
      (fanD g (by rw [hg]; simp)).1
    have arity := (fanD g (by rw [hg]; simp)).2
    let val (x : Fin 10 → Bool) := g.op.eval (g.inputs.map fun j => (seed x).getD j false)
    have tailSolves (x : Fin 10 → Bool) : T.eval (seed x ++ [val x]) = target x := by
      have hx := solves x
      change (D.gates.foldl step (seed x)).getD D.output false = target x at hx
      rw [hg,List.foldl_cons] at hx
      exact hx
    have dropHere (a : Fin 13) (ha : ∀ x : Fin 10 → Bool, val x = (constants x).getD a.val false) : False :=
      excludeDrop T fanT sizeT a (fun x => (congrArg (fun b => T.eval (seed x ++ [b])) (ha x).symm).trans (tailSolves x))
    have readIn (x : Fin 10 → Bool) (a : ℕ) (ha : a < 11) :
        (seed x).getD a false = source x ⟨a,ha⟩ := readSeed x ⟨a,ha⟩
    have readOut (x : Fin 10 → Bool) (a : ℕ) (ha : ¬ a < 11) :
        (seed x).getD a false = false := List.getD_eq_default _ _ (by rw [seedLength]; omega)
    have handleBin (b : Bool) (a c : ℕ)
        (hv : ∀ x : Fin 10 → Bool, val x = bin b ((seed x).getD a false) ((seed x).getD c false)) : False := by
      by_cases ha : a < 11 <;> by_cases hc : c < 11
      · let i : Fin 11 := ⟨a,ha⟩
        let j : Fin 11 := ⟨c,hc⟩
        by_cases eq : i = j
        · apply dropHere ⟨a,by omega⟩
          intro x
          rw [hv,readIn x a ha,readIn x c hc]
          change bin b (source x i) (source x j) = _
          rw [← eq]
          have eq' := readConstant x i
          change (constants x).getD a false = source x i at eq'
          rw [eq']
          cases b <;> simp [bin]
        · by_cases mixed : complements i j
          · have evaluates (x : Fin 10 → Bool) : val x = b := by
              rw [hv,readIn x a ha,readIn x c hc]
              change bin b (source x i) (source x j) = b
              rcases mixed with ⟨first,last⟩ | ⟨first,last⟩
              · rw [first,last]
                change bin b (x 0) (!x 0) = b
                cases b <;> cases x 0 <;> rfl
              · rw [first,last]
                change bin b (!x 0) (x 0) = b
                cases b <;> cases x 0 <;> rfl
            cases b
            · apply dropHere 11
              intro x
              exact (evaluates x).trans (readFalse x).symm
            · apply dropHere 12
              intro x
              exact (evaluates x).trans (readTrue x).symm
          · apply excludeBin b T fanT sizeT i j eq mixed
            intro x
            have e := hv x
            rw [readIn x a ha,readIn x c hc] at e
            exact (congrArg (fun s => T.eval (seed x ++ [s])) e.symm).trans (tailSolves x)
      · cases b
        · apply dropHere 11
          intro x
          rw [hv,readOut x c hc,readFalse]
          simp [bin]
        · apply dropHere ⟨a,by omega⟩
          intro x
          rw [hv,readOut x c hc,readIn x a ha]
          have eq := readConstant x ⟨a,ha⟩
          rw [eq]
          simp [bin]
      · cases b
        · apply dropHere 11
          intro x
          rw [hv,readOut x a ha,readFalse]
          simp [bin]
        · apply dropHere ⟨c,by omega⟩
          intro x
          rw [hv,readOut x a ha,readIn x c hc]
          have eq := readConstant x ⟨c,hc⟩
          rw [eq]
          simp [bin]
      · apply dropHere 11
        intro x
        rw [hv,readOut x a ha,readOut x c hc,readFalse]
        cases b <;> rfl
    have handleNot (a : ℕ) (hv : ∀ x : Fin 10 → Bool, val x = !(seed x).getD a false) : False := by
      by_cases ha : a < 11
      · let i : Fin 11 := ⟨a,ha⟩
        by_cases atZero : i = 0
        · apply dropHere ⟨10,by decide⟩
          intro x
          rw [hv,readIn x a ha]
          change (!source x i) = (constants x).getD (10 : Fin 11).val false
          rw [atZero,readConstant]
          rfl
        · by_cases atHint : i = 10
          · apply dropHere ⟨0,by decide⟩
            intro x
            rw [hv,readIn x a ha]
            change (!source x i) = (constants x).getD (0 : Fin 11).val false
            rw [atHint,readConstant]
            change (!(!x 0)) = x 0
            simp
          · apply excludeNot T fanT sizeT i atZero atHint
            intro x
            have e := hv x
            rw [readIn x a ha] at e
            exact (congrArg (fun s => T.eval (seed x ++ [s])) e.symm).trans (tailSolves x)
      · apply dropHere 12
        intro x
        rw [hv,readOut x a ha,readTrue]
        rfl
    have emptyAnd : GateOp.and.eval [] = true := rfl
    have emptyOr : GateOp.or.eval [] = false := rfl
    have emptyNot : GateOp.not.eval [] = true := rfl
    have andCopy (u : Bool) : GateOp.and.eval [u] = bin false u u := by cases u <;> rfl
    have orCopy (u : Bool) : GateOp.or.eval [u] = bin true u u := by cases u <;> rfl
    have andPair (u v : Bool) : GateOp.and.eval [u,v] = bin false u v := by cases u <;> cases v <;> rfl
    have orPair (u v : Bool) : GateOp.or.eval [u,v] = bin true u v := by cases u <;> cases v <;> rfl
    have notHead (u : Bool) (l : List Bool) : GateOp.not.eval (u :: l) = !u := rfl
    rcases inp : g.inputs with _ | ⟨a,_ | ⟨b,_ | ⟨c,rest⟩⟩⟩
    · rcases allowed with op | op | op
      · apply dropHere 12
        intro x
        rw [readTrue]
        simp only [val,inp,op,List.map_nil,emptyAnd]
      · apply dropHere 11
        intro x
        rw [readFalse]
        simp only [val,inp,op,List.map_nil,emptyOr]
      · apply dropHere 12
        intro x
        rw [readTrue]
        simp only [val,inp,op,List.map_nil,emptyNot]
    · rcases allowed with op | op | op
      · apply handleBin false a a
        intro x
        simp only [val,inp,op,List.map_cons,List.map_nil,andCopy]
      · apply handleBin true a a
        intro x
        simp only [val,inp,op,List.map_cons,List.map_nil,orCopy]
      · exact handleNot a (by intro x; simp only [val,inp,op,List.map_cons,List.map_nil,notHead])
    · rcases allowed with op | op | op
      · apply handleBin false a b
        intro x
        simp only [val,inp,op,List.map_cons,List.map_nil,andPair]
      · apply handleBin true a b
        intro x
        simp only [val,inp,op,List.map_cons,List.map_nil,orPair]
      · exact handleNot a (by intro x; simp only [val,inp,op,List.map_cons,List.map_nil,notHead])
    · rw [inp] at arity
      simp at arity
