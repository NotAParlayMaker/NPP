import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm

set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.R_meta_4848_417
    (repair :
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      (∀ a b c,G.Adj a b → G.Adj b c → ¬G.Adj c a) → NoFourCycle G → circuitFun n C=graphFun G ∅ → ∀ j<C.size,(gateAt C j).op=.and →
      let D : Circuit := ⟨C.gates.set j ⟨.or,[]⟩,C.output⟩
      let V := fun (A : Circuit) (x : Fin n → Bool) (w : ℕ) => (A.wires (List.ofFn x)).getD w false
      ∀ u v p q : Fin n, ¬G.Adj u v → G.Adj p q →
      let x := pairInput u v
      let y := pairInput p q
      V C x (n+j)=true → circuitFun n D y=false →
      ∀ k<C.size,j<k → (gateAt C k).op=.and →
      (∃ a∈(gateAt C k).inputs, V C x a=true ∧ V C y a=true ∧ V D y a=false) →
      (∃ b∈(gateAt C k).inputs, V C x b=false ∧ V C y b=true ∧ V D y b=true) →
      ¬ IsMinimalMonoCircuit n C)
    (pivotal :
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      IsMinimalMonoCircuit n C → circuitFun n C=graphFun G ∅ → ∀ j<C.size,
      let D : Circuit := ⟨C.gates.set j ⟨.or,[]⟩,C.output⟩
      ∃ p q,G.Adj p q ∧ circuitFun n D (pairInput p q)=false)

    : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj], (∀ (x4 x5 x6 : Fin x1), x2.Adj x4 x5 → x2.Adj x5 x6 → ¬x2.Adj x6 x4) → PEqualNP.TopForm.NoFourCycle x2 → ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalMonoCircuit x1 x6 → PEqualNP.MetaComplexity.circuitFun x1 x6 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ → ∀ x9 < x6.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x6 x9).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ (x12 x13 : Fin x1), PEqualNP.EdgeOwnership.gateVal x1 x6 x9 (PEqualNP.EdgeOwnership.pairInput x12 x13) = Bool.true → x2.Adj x12 x13 := by
  classical
  have simulation : ∀ (n : ℕ) (C : Circuit), Monotone2 C → ∀ j<C.size,
    let D : Circuit := ⟨C.gates.set j ⟨.or,[]⟩,C.output⟩
    let V := fun (A : Circuit) (x : Fin n → Bool) (w : ℕ) => (A.wires (List.ofFn x)).getD w false
    (∀ x w,n+C.size≤ w → V C x w=false) ∧
    (∀ x w,w<n+j → V C x w=V D x w) ∧
    ∀ k<C.size,j<k → ∀ x w, (w=n+k) →
    let read := fun (A : Circuit) (i : ℕ) => decide (i<w) && V A x i
    ∀ A∈[C,D], V A x w=(gateAt C k).op.eval ((gateAt C k).inputs.map (read A)) := by
    let stepWire (w : List Bool) (g : Gate) : List Bool :=
      w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    have wires_eq_foldl (C : Circuit) (x : List Bool) :
        C.wires x = C.gates.foldl stepWire x := rfl
    have foldl_length (gs : List Gate) (w : List Bool) :
        (gs.foldl stepWire w).length = w.length + gs.length := by
      induction gs generalizing w with
      | nil => simp
      | cons g gs ih =>
        rw [List.foldl_cons, ih]
        simp [stepWire]
        omega
    have foldl_getD_lt2 (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
        (gs.foldl stepWire w).getD i false = w.getD i false := by
      induction gs generalizing w with
      | nil => rfl
      | cons g gs ih =>
        simp only [List.foldl_cons]
        have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
        rw [ih (stepWire w g) hlt]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
    have getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]
    have foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
        (gs.foldl stepWire w).getD (w.length + j) false =
          (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
            if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
      induction gs generalizing w j with
      | nil => simp at hj
      | cons g gs ih =>
        rw [List.foldl_cons]
        cases j with
        | zero =>
          have h1 : w.length < (stepWire w g).length := by simp [stepWire]
          rw [Nat.add_zero, foldl_getD_lt2 gs (stepWire w g) w.length h1]
          simp only [List.getElem_cons_zero]
          have h2 : (stepWire w g).getD w.length false =
              g.op.eval (g.inputs.map fun i => w.getD i false) := by
            simp [stepWire, List.getD_eq_getElem?_getD]
          rw [h2]
          congr 1
          apply List.map_congr_left
          intro i _
          by_cases hi : i < w.length
          · rw [if_pos hi, foldl_getD_lt2 gs (stepWire w g) i (by simp [stepWire]; omega)]
            simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
          · rw [if_neg hi]; exact getD_ge w i (by omega)
        | succ j =>
          have hj' : j < gs.length := by simpa using hj
          have key := ih (stepWire w g) j hj'
          have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
          rw [hl] at key
          have e : w.length + (j + 1) = w.length + 1 + j := by omega
          simp only [List.getElem_cons_succ]
          rw [e]
          exact key
    let val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false
    have gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
      change C.gates.getD j _ = C.gates[j]
      simp [List.getD_eq_getElem?_getD,hj]
    have val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
        val C x u = x.getD u false := by
      unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt2 _ _ _ (by omega)
    have val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
        (hu : n + C.gates.length ≤ u) : val C x u = false := by
      unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega
    have val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
        (hj : j < C.gates.length) :
        val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
          if i < n + j then val C x i else false) := by
      subst hx
      rw [gateAt_eq hj]
      exact foldl_getD_gate C.gates x j hj
    have val_prefix {n : ℕ} {C D : Circuit} {x : List Bool} (hx : x.length = n) {m : ℕ}
        (hmC : m ≤ C.gates.length) (hmD : m ≤ D.gates.length)
        (hg : ∀ k < m, gateAt D k = gateAt C k) : ∀ u, u < n + m → val D x u = val C x u := by
      intro u
      induction u using Nat.strong_induction_on with
      | _ u ih =>
        intro hu
        by_cases hun : u < n
        · rw [val_input hx hun, val_input hx hun]
        · obtain ⟨k, rfl⟩ : ∃ k, u = n + k := ⟨u - n, by omega⟩
          have hk : k < m := by omega
          rw [val_gate hx (by omega), val_gate hx (by omega), hg k hk]
          congr 1
          apply List.map_congr_left
          intro i _
          by_cases hi : i < n + k
          · rw [if_pos hi, if_pos hi]; exact ih i hi (by omega)
          · rw [if_neg hi, if_neg hi]
    let kill (C : Circuit) (j : ℕ) : Circuit := ⟨C.gates.set j ⟨.or,[]⟩,C.output⟩
    have size_kill (C : Circuit) (j : ℕ) : (kill C j).gates.length=C.gates.length := by simp [kill]
    have at_kill (C : Circuit) (j k : ℕ) (hk : k<C.gates.length) :
        gateAt (kill C j) k = if j=k then ⟨.or,[]⟩ else gateAt C k := by
      rw [gateAt_eq (by simpa only [size_kill] using hk),gateAt_eq hk]
      simp [kill,List.getElem_set]
    intro n C _ j hj
    dsimp only
    refine ⟨fun x w h => val_ge (by simp) h,?_,?_⟩
    · intro x w old
      apply Eq.symm
      apply val_prefix (C:=C) (D:=kill C j) (n:=n) (m:=j) (x:=List.ofFn x) (by simp)
        (Nat.le_of_lt hj) (by rw [size_kill];exact Nat.le_of_lt hj) _ w old
      intro k lt
      rw [at_kill C j k (lt.trans hj),if_neg (by omega)]
    · intro k hk lt x w eq A mem
      subst w
      simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
      have calcGate (B : Circuit) (kb : k<B.gates.length) (same : gateAt B k=gateAt C k) :
          val B (List.ofFn x) (n+k)=(gateAt C k).op.eval ((gateAt C k).inputs.map
            (fun i => decide (i<n+k) && val B (List.ofFn x) i)) := by
        rw [val_gate (by simp) kb,same]
        congr 1
        apply List.map_congr_left
        intro i _
        split_ifs with h <;> simp [h]
      rcases mem with rfl|rfl
      · exact calcGate _ hk rfl
      · apply calcGate (kill C j) (by rw [size_kill];exact hk)
        rw [at_kill C j k hk,if_neg (by omega)]
  intro n G _ tri square C least correct j hj andj u v source
  by_contra miss
  let D : Circuit := ⟨C.gates.set j ⟨.or,[]⟩,C.output⟩
  obtain ⟨p,q,edge,killed⟩ := pivotal n G C least correct j hj
  let x := pairInput u v
  let y := pairInput p q
  let V := fun (A : Circuit) (z : Fin n → Bool) (w : ℕ) => (A.wires (List.ofFn z)).getD w false
  obtain ⟨outside,before,step⟩ := simulation n C least.1 j hj
  have pairEval (a b : Fin n) : graphFun G ∅ (pairInput a b)=true ↔ G.Adj a b := by
    change (_ || decide (∃ s t,G.Adj s t ∧ decide (s=a ∨ s=b)=true ∧ decide (t=a ∨ t=b)=true))=true ↔ _
    simp only [Finset.notMem_empty,false_and,exists_false,decide_false,Bool.false_or,decide_eq_true_eq]
    constructor
    · rintro ⟨s,t,adj,rfl|rfl,rfl|rfl⟩ <;> first | exact adj | exact adj.symm | exact (adj.ne rfl).elim
    · intro adj
      exact ⟨a,b,adj,Or.inl rfl,Or.inr rfl⟩
  let cut := fun w => V C y w=true ∧ V D y w=false ∧ V C x w=false
  have root : cut C.output := by
    refine ⟨?_,killed,?_⟩
    · change circuitFun n C (pairInput p q)=true
      rw [correct];exact (pairEval p q).2 edge
    · change circuitFun n C (pairInput u v)=false
      rw [correct];exact Bool.eq_false_iff.mpr (fun h => miss ((pairEval u v).1 h))
  have ex : ∃ w,cut w := ⟨_,root⟩
  let w := Nat.find ex
  obtain ⟨wy,wd,wx⟩ := (show cut w from Nat.find_spec ex)
  have tooEarly (i) (lt : i<w) : ¬cut i := Nat.find_min ex lt
  have old : ¬w<n+j := by
    intro h
    have eq : V C y w=V D y w := before y _ h
    rw [wy,wd] at eq;contradiction
  have beyond : ¬n+C.size≤ w := by
    intro h
    have e : V C y w=false := outside y w h
    rw [wy] at e;contradiction
  have strict : n+j<w := by
    have ne : w≠n+j := by
      intro he
      change V C x (n+j)=true at source
      rw [he,source] at wx
      contradiction
    omega
  let k := w-n
  have kw : w=n+k := by dsimp [k];omega
  have kj : j<k := by omega
  have kl : k<C.size := by omega
  have cm : C∈[C,D] := by simp
  have dm : D∈[C,D] := by simp
  have eqy := step k kl kj y w kw C cm
  have eqd := step k kl kj y w kw D dm
  have eqx := step k kl kj x w kw C cm
  change V C y w = _ at eqy
  change V D y w = _ at eqd
  change V C x w = _ at eqx
  rw [wy] at eqy
  rw [wd] at eqd
  rw [wx] at eqx
  have mem : gateAt C k∈C.gates := by
    change C.gates.getD k _ ∈ C.gates
    have kk : k<C.gates.length := kl
    simp [List.getD_eq_getElem?_getD,kk]
  rcases (least.1 _ mem).1 with hand|hor
  · rw [hand] at eqy eqd eqx
    have isAll := eqy.symm
    have notD := eqd.symm
    have notX := eqx.symm
    change ((gateAt C k).inputs.map (fun i => decide (i<w) && V C y i)).all id=true at isAll
    simp only [List.all_map,List.all_eq_true,Function.comp_apply,id_eq,
      Bool.and_eq_true,decide_eq_true_eq] at isAll
    have missing (A : Circuit) (z : Fin n → Bool)
        (h : ((gateAt C k).inputs.map (fun i => decide (i<w) && V A z i)).all id=false) :
        ∃ i∈(gateAt C k).inputs,V A z i=false := by
      by_contra! all
      have pos : ((gateAt C k).inputs.map (fun i => decide (i<w) && V A z i)).all id=true := by
        simp only [List.all_map,List.all_eq_true,Function.comp_apply,id_eq,Bool.and_eq_true,decide_eq_true_eq]
        intro i hi
        exact ⟨(isAll i hi).1,by simpa using all i hi⟩
      rw [pos] at h
      contradiction
    obtain ⟨a,ha,ad⟩ := missing D y notD
    obtain ⟨b,hb,bx⟩ := missing C x notX
    have trueY (i) (hi : i∈(gateAt C k).inputs) : V C y i=true := (isAll i hi).2
    have ax : V C x a=true := by
      cases h : V C x a
      · exact (tooEarly a (isAll a ha).1 ⟨trueY a ha,ad,h⟩).elim
      · rfl
    have bd : V D y b=true := by
      cases h : V D y b
      · exact (tooEarly b (isAll b hb).1 ⟨trueY b hb,h,bx⟩).elim
      · rfl
    exact repair n G C tri square correct j hj andj u v p q miss edge source killed k kl kj hand
      ⟨a,ha,ax,trueY a ha,ad⟩ ⟨b,hb,bx,trueY b hb,bd⟩ least
  · rw [hor] at eqy eqd eqx
    have fire := eqy.symm
    change ((gateAt C k).inputs.map (fun i => decide (i<w) && V C y i)).any id=true at fire
    simp only [List.any_map,List.any_eq_true,Function.comp_apply,id_eq,Bool.and_eq_true,decide_eq_true_eq] at fire
    obtain ⟨a,ha,lt,ay⟩ := fire
    have off (A : Circuit) (z : Fin n → Bool)
        (h : ((gateAt C k).inputs.map (fun i => decide (i<w) && V A z i)).any id=false) : V A z a=false := by
      apply Bool.eq_false_iff.mpr
      intro atrue
      have pos : ((gateAt C k).inputs.map (fun i => decide (i<w) && V A z i)).any id=true := by
        simp only [List.any_map,List.any_eq_true,Function.comp_apply,id_eq,Bool.and_eq_true,decide_eq_true_eq]
        exact ⟨a,ha,lt,atrue⟩
      rw [pos] at h;contradiction
    exact tooEarly a lt ⟨ay,off D y eqd.symm,off C x eqx.symm⟩
