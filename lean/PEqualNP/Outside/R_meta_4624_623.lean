import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm

-- Gate evaluation follows L-meta-2668. Joining the two circuits preserves strict
-- cones by translating each component's gate wires while fixing input wires.
set_option maxHeartbeats 5000000 in
set_option maxRecDepth 4000 in
theorem PEqualNP.Outside.R_meta_4624_623
(connected : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ a b c,G.Adj a b → G.Adj b c → ¬G.Adj c a) → NoFourCycle G →
      (∃ a b,G.Adj a b) → (∀ u,G.degree u≠1) → (∀ a b,(∃ u,G.Adj a u) → (∃ v,G.Adj b v) → G.Reachable a b) → ∃ C : Circuit, IsMinimalMonoCircuit n C ∧ circuitFun n C=graphFun G ∅ ∧
  ∀ j<C.gates.length,(gateAt C j).op=.and → ∃ u v,G.Adj u v ∧ Owns n C j u v)
(lower : ∀ (n : ℕ) (H K : SimpleGraph (Fin n)) [DecidableRel H.Adj] [DecidableRel K.Adj]
      [DecidableRel (H⊔K).Adj], (∀ u v w,H.Adj u v → ¬K.Adj u w) → (∃ a b,H.Adj a b) → (∃ a b,K.Adj a b) →
      (∀ a b c,(H⊔K).Adj a b → (H⊔K).Adj b c → ¬(H⊔K).Adj c a) → NoFourCycle (H⊔K) →
      (∀ u,(H⊔K).degree u≠1) → ∀ D : Circuit, Monotone2 D → circuitFun n D=graphFun (H⊔K) ∅ →
      ∃ A B : Circuit,Monotone2 A ∧ circuitFun n A=graphFun H ∅ ∧ Monotone2 B ∧ circuitFun n B=graphFun K ∅ ∧
        A.size+B.size+1≤D.size) :
∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj], (∀ (x4 x5 x6 : Fin x1), x2.Adj x4 x5 → x2.Adj x5 x6 → ¬x2.Adj x6 x4) → PEqualNP.TopForm.NoFourCycle x2 → (∃ (x6 : Fin x1) (x7 : Fin x1), x2.Adj x6 x7) → (∀ (x7 : Fin x1), x2.degree x7 ≠ (1 : ℕ)) → ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalMonoCircuit x1 x8 ∧ PEqualNP.MetaComplexity.circuitFun x1 x8 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ ∧ ∀ x9 < x8.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x8 x9).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x12 : Fin x1) (x13 : Fin x1), x2.Adj x12 x13 ∧ PEqualNP.EdgeOwnership.Owns x1 x8 x9 x12 x13 := by
  classical
  have gateLookup (D : Circuit) (j : ℕ) : gateAt D j=D.gates.getD j ⟨.or,[]⟩ := rfl
  have sizeEq (D : Circuit) : D.size=D.gates.length := rfl
  have coneAt (n : ℕ) (cs : List (List ℕ)) (g : Gate) : coneStep n cs g=cs++[(g.inputs.filter (fun w => decide (n≤w ∧ w<n+cs.length))).flatMap (fun w => (w-n)::cs.getD (w-n) [])] := rfl
  have pairAt {n : ℕ} (u v i : Fin n) : pairInput u v i=decide (i=u ∨ i=v) := rfl
  have graphAt {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Fin n → Bool) : graphFun G ∅ x=(decide (∃ a ∈ (∅ : Finset _),x a=true) || decide (∃ u v,G.Adj u v ∧ x u=true ∧ x v=true)) := rfl
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
    simp [gateLookup, List.getD_eq_getElem?_getD, hj]
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
  have graph_true {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Fin n → Bool) :
      graphFun G ∅ x = true ↔ ∃ p l, G.Adj p l ∧ x p = true ∧ x l = true := by
    rw [graphAt]
    simp
  have pair_true {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (p l : Fin n)
      (hp : G.Adj p l) : graphFun G ∅ (PEqualNP.EdgeOwnership.pairInput p l) = true := by
    rw [graph_true]
    exact ⟨p, l, hp, by simp [pairAt], by simp [pairAt]⟩
  have cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
      (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
    induction gs generalizing cs with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp [coneAt]
      omega
  have cones_char (n : ℕ) (gs : List Gate) :
      ∀ i j, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
        j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
          (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) []) := by
    induction gs using List.reverseRecOn with
    | nil => intro i j; simp
    | append_singleton gs g ih =>
      intro i j
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hlen : (gs.foldl (coneStep n) []).length = gs.length := by
        rw [cones_len]; simp
      have key : ∀ k, k < gs.length →
          (coneStep n (gs.foldl (coneStep n) []) g).getD k [] =
            (gs.foldl (coneStep n) []).getD k [] := by
        intro k hk
        simp only [coneAt, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left (by omega)]
      rcases Nat.lt_trichotomy j gs.length with h | h | h
      · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
          simp only [List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_left h]
        rw [key j h, ih i j, e1]
        constructor
        · rintro ⟨_, w, hw, h1, h2, h3⟩
          refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
          rw [key (w - n) (by omega)]
          exact h3
        · rintro ⟨_, w, hw, h1, h2, h3⟩
          refine ⟨h, w, hw, h1, h2, ?_⟩
          rw [key (w - n) (by omega)] at h3
          exact h3
      · subst h
        have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
          simp [List.getD_eq_getElem?_getD]
        have e2 : (coneStep n (gs.foldl (coneStep n) []) g).getD gs.length [] =
            (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
              (fun w => (w - n) :: (gs.foldl (coneStep n) []).getD (w - n) []) := by
          simp only [coneAt, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen]
        rw [e2, e1]
        simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
        constructor
        · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
          refine ⟨by simp, w, hw, h1, h2, ?_⟩
          rw [key (w - n) (by omega)]
          exact h3
        · rintro ⟨_, w, hw, h1, h2, h3⟩
          rw [key (w - n) (by omega)] at h3
          exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
      · have e0 : (coneStep n (gs.foldl (coneStep n) []) g).getD j [] = [] := by
          simp only [coneAt, List.getD_eq_getElem?_getD]
          rw [List.getElem?_eq_none (by simp; omega)]
          rfl
        rw [e0]
        constructor
        · intro h0; simp at h0
        · rintro ⟨h0, _⟩
          simp at h0
          omega
  have coneIff (n : ℕ) (C : Circuit) (i j : ℕ) (hj : j<C.gates.length) :
   InCone n C i j ↔ ∃ w ∈ (gateAt C j).inputs,n≤w ∧ w<n+j ∧ (i=w-n ∨ InCone n C i (w-n)) := by
    change i ∈ (C.gates.foldl (coneStep n) []).getD j [] ↔ _
    rw [cones_char]
    exact and_iff_right hj
  let addOr (n : ℕ) (D : Circuit) (w : ℕ) : Circuit := ⟨D.gates++[⟨.or,[D.output,w]⟩],n+D.gates.length⟩
  have add_mono {n : ℕ} (D : Circuit) (w : ℕ) (m : Monotone2 D) : Monotone2 (addOr n D w) := by
    intro g hg
    rcases List.mem_append.mp hg with inside|last
    · exact m g inside
    · obtain rfl := List.mem_singleton.mp last;exact ⟨Or.inr rfl,le_rfl⟩
  let shift (n k w : ℕ) := if w<n then w else k+w
  let mapGate (n k : ℕ) (g : Gate) : Gate := ⟨g.op,g.inputs.map (shift n k)⟩
  let Rows (n : ℕ) (C D : Circuit) (k : ℕ) := k+C.gates.length≤D.gates.length ∧
    ∀ i<C.gates.length,gateAt D (k+i)=mapGate n k (gateAt C i)
  have shift_gate {n k : ℕ} (i : ℕ) : shift n k (n+i)=n+(k+i) := by simp [shift];omega
  have lt_gate {n k : ℕ} (w i : ℕ) : shift n k w<n+(k+i) ↔ w<n+i := by unfold shift;split <;> omega
  have values {n k : ℕ} {C D : Circuit} (rows : Rows n C D k) (x : Fin n → Bool) :
      ∀ w,w<n+C.gates.length → val D (List.ofFn x) (shift n k w)=val C (List.ofFn x) w := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro bound
      by_cases raw : w<n
      · simp only [shift,if_pos raw]
        exact (val_input (C:=D) (x:=List.ofFn x) (by simp) raw).trans (val_input (C:=C) (x:=List.ofFn x) (by simp) raw).symm
      let i := w-n
      have eq : w=n+i := by dsimp [i];omega
      have sub : i<C.gates.length := by omega
      have ins := rows.1
      rw [eq,shift_gate,val_gate (n:=n) (by simp) (show k+i<D.gates.length by omega),rows.2 i sub,
        val_gate (n:=n) (by simp) sub]
      change (gateAt C i).op.eval (((gateAt C i).inputs.map (shift n k)).map _)=(gateAt C i).op.eval _
      congr 1
      rw [List.map_map]
      apply List.map_congr_left
      intro u hu
      simp only [Function.comp_apply]
      by_cases b : u<n+i
      · rw [if_pos ((lt_gate u i).mpr b),if_pos b];exact ih u (by omega) (by omega)
      · rw [if_neg (fun h => b ((lt_gate u i).mp h)),if_neg b]
  have cones {n k : ℕ} {C D : Circuit} (rows : Rows n C D k) (i : ℕ) (hi : i<C.gates.length) (a : ℕ) (h : InCone n D a (k+i)) :
      ∃ b,a=k+b ∧ InCone n C b i := by
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      have lens := rows.1
      obtain ⟨w,mem,lo,lt,hit⟩ := (coneIff n D a (k+i) (by omega)).mp h
      rw [rows.2 i hi] at mem
      obtain ⟨u,hu,rfl⟩ := List.mem_map.mp mem
      have un : n≤u := by by_contra! u0;simp [shift,u0] at lo;omega
      have ul := (lt_gate u i).mp lt
      have wu : shift n k u-n=k+(u-n) := by simp [shift,not_lt.mpr un];omega
      rw [wu] at hit
      rcases hit with eq|rec
      · exact ⟨u-n,eq,(coneIff n C (u-n) i hi).mpr ⟨u,hu,un,ul,Or.inl rfl⟩⟩
      · obtain ⟨b,eq,bc⟩ := ih (u-n) (by omega) (by omega) rec
        exact ⟨b,eq,(coneIff n C b i hi).mpr ⟨u,hu,un,ul,Or.inr bc⟩⟩
  have owns {n k : ℕ} {C D : Circuit} (rows : Rows n C D k) {i p q} (h : Owns n C i p q) : Owns n D (k+i) p q := by
    obtain ⟨hi,op,on,off⟩ := h
    have len := rows.1
    have eq (j : ℕ) (hj : j<C.gates.length) : gateVal n D (k+j) (pairInput p q)=gateVal n C j (pairInput p q) := by
      have v := values rows (pairInput p q) (n+j) (by omega)
      rw [shift_gate] at v
      exact v
    refine ⟨by omega,by simpa [rows.2 i hi,mapGate] using op,(eq i hi).trans on,?_⟩
    intro a lt cone andA
    obtain ⟨b,rfl,bc⟩ := cones rows i hi a cone
    have hb : b<C.gates.length := by omega
    exact (eq b hb).trans (off b (by omega) bc (by simpa [rows.2 b hb,mapGate] using andA))
  let stage (n : ℕ) (A B : Circuit) : Circuit :=
    ⟨A.gates++B.gates.map (mapGate n A.gates.length),A.output⟩
  let join (n : ℕ) (A B : Circuit) : Circuit :=
    addOr n (stage n A B) (shift n A.gates.length B.output)
  have leftRows {n : ℕ} (A B : Circuit) : Rows n A (join n A B) 0 := by
    constructor
    · simp [join,addOr,stage]
    · intro i hi
      have small : i<(stage n A B).gates.length := by simp [stage];omega
      have eq (w : ℕ) : shift n 0 w=w := by simp [shift]
      simp [join,addOr,stage,gateLookup,List.getD_eq_getElem?_getD,List.getElem?_append_left small,List.getElem?_append_left hi,mapGate,funext eq]
  have rightRows {n : ℕ} (A B : Circuit) : Rows n B (join n A B) A.gates.length := by
    constructor
    · simp [join,addOr,stage]
    · intro i hi
      have small : A.gates.length+i<(A.gates++B.gates.map (mapGate n A.gates.length)).length := by simp;omega
      have big : A.gates.length≤A.gates.length+i := by omega
      simp [join,addOr,stage,gateLookup,List.getD_eq_getElem?_getD,List.getElem?_append_left small,List.getElem?_append_right big,List.getElem?_append_left (by simpa using hi : i<(B.gates.map (mapGate n A.gates.length)).length),hi]
  have lastGate {n : ℕ} (A B : Circuit) : gateAt (join n A B) (A.gates.length+B.gates.length) =
      ⟨.or,[A.output,shift n A.gates.length B.output]⟩ := by
    have h : A.gates.length+B.gates.length=(stage n A B).gates.length := by simp [stage]
    rw [h]
    simp [gateLookup,join,addOr,List.getD_eq_getElem?_getD,stage]
  have size_join {n : ℕ} (A B : Circuit) : (join n A B).size=A.size+B.size+1 := by
    simp [sizeEq,join,addOr,stage,Nat.add_assoc]
  have mono {n : ℕ} (A B : Circuit) (a : Monotone2 A) (b : Monotone2 B) : Monotone2 (join n A B) := by
    apply add_mono
    intro g hg
    rcases List.mem_append.mp hg with orig|copy
    · exact a g orig
    · obtain ⟨z,hz,rfl⟩ := List.mem_map.mp copy
      simpa [mapGate] using b z hz
  have sem {n : ℕ} (A B : Circuit) (ha : A.output<n+A.gates.length) (hb : B.output<n+B.gates.length) (x : Fin n → Bool) :
      circuitFun n (join n A B) x=(circuitFun n A x || circuitFun n B x) := by
    let E := join n A B
    let j := A.gates.length+B.gates.length
    have len : E.gates.length=j+1 := size_join A B
    have a := values (leftRows (n:=n) A B) x A.output ha
    have b := values (rightRows (n:=n) A B) x B.output hb
    have a0 : shift n 0 A.output=A.output := by simp [shift]
    rw [a0] at a
    have h1 : A.output<n+j := by dsimp [j];omega
    have h2 : shift n A.gates.length B.output<n+j := by
      have := (lt_gate (n:=n) (k:=A.gates.length) B.output B.gates.length).mpr hb
      exact this
    have out : E.output=n+j := by simp [E,j,join,addOr,stage]
    change val E (List.ofFn x) E.output=_
    rw [out,val_gate (n:=n) (by simp) (show j<E.gates.length by omega),lastGate]
    change ((GateOp.or).eval ([A.output,shift n A.gates.length B.output].map (fun i => if i<n+j then val E (List.ofFn x) i else false)))=_
    simp only [List.map_cons,List.map_nil,if_pos h1,if_pos h2]
    change (val E (List.ofFn x) A.output || (val E (List.ofFn x) (shift n A.gates.length B.output) || false))=_
    rw [Bool.or_false,a,b]
    rfl
  have owned_union {n : ℕ} (G H : SimpleGraph (Fin n)) [DecidableRel G.Adj] [DecidableRel H.Adj] (A B : Circuit)
      (oa : ∀ j<A.gates.length,(gateAt A j).op=.and → ∃ u v,G.Adj u v ∧ Owns n A j u v)
      (ob : ∀ j<B.gates.length,(gateAt B j).op=.and → ∃ u v,H.Adj u v ∧ Owns n B j u v) :
      ∀ j<(join n A B).gates.length,(gateAt (join n A B) j).op=.and → ∃ u v,(G⊔H).Adj u v ∧ Owns n (join n A B) j u v := by
    intro j hj op
    have len : (join n A B).gates.length=A.gates.length+B.gates.length+1 := size_join A B
    by_cases first : j<A.gates.length
    · have row := (leftRows (n:=n) A B).2 j first
      simp only [Nat.zero_add] at row
      obtain ⟨u,v,e,h⟩ := oa j first (by simpa [row,mapGate] using op)
      exact ⟨u,v,Or.inl e,by simpa using owns (leftRows (n:=n) A B) h⟩
    by_cases last : j=A.gates.length+B.gates.length
    · subst j;rw [lastGate] at op;contradiction
    let i := j-A.gates.length
    have sm : i<B.gates.length := by dsimp [i];omega
    have eq : j=A.gates.length+i := by dsimp [i];omega
    rw [eq] at op ⊢
    have row := (rightRows (n:=n) A B).2 i sm
    obtain ⟨u,v,e,h⟩ := ob i sm (by simpa [row,mapGate] using op)
    exact ⟨u,v,Or.inr e,owns (rightRows (n:=n) A B) h⟩
  let cut {n : ℕ} (G : SimpleGraph (Fin n)) (P : Fin n → Prop) : SimpleGraph (Fin n) := {
    Adj u v := G.Adj u v ∧ P u ∧ P v
    symm := ⟨fun _ _ h => ⟨h.1.symm,h.2.2,h.2.1⟩⟩
    loopless := ⟨fun _ h => G.irrefl h.1⟩ }
  have le {n : ℕ} (G : SimpleGraph (Fin n)) (P : Fin n → Prop) : cut G P ≤ G := fun _ _ h => h.1
  have degree {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (P : Fin n → Prop) [DecidableRel (cut G P).Adj]
      (closed : ∀ u v,G.Adj u v → P u → P v) (u : Fin n) :
      (cut G P).degree u=0 ∨ (cut G P).degree u=G.degree u := by
    by_cases h : P u
    · right
      have eq : (cut G P).neighborFinset u=G.neighborFinset u := by
        ext v;simp only [SimpleGraph.mem_neighborFinset]
        exact ⟨fun e => e.1,fun e => ⟨e,h,closed _ _ e h⟩⟩
      exact congrArg Finset.card eq
    · left
      have eq : (cut G P).neighborFinset u=∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro v hv;exact h ((SimpleGraph.mem_neighborFinset _ _ _).mp hv).2.1
      exact (congrArg Finset.card eq).trans rfl
  let ConnectedSupport {n : ℕ} (G : SimpleGraph (Fin n)) := ∀ a b, (∃ u,G.Adj a u) → (∃ v,G.Adj b v) → G.Reachable a b
  have split {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (nc : ¬ConnectedSupport G) (leaf : ∀ u,G.degree u≠1) :
      ∃ H K : SimpleGraph (Fin n), G=H⊔K ∧ H<G ∧ K<G ∧
        (∀ u v w,H.Adj u v → ¬K.Adj u w) ∧ (∃ a b,H.Adj a b) ∧ (∃ a b,K.Adj a b) ∧
        (∀ u,H.degree u≠1) ∧ (∀ u,K.degree u≠1) := by
    classical
    unfold ConnectedSupport at nc
    push Not at nc
    obtain ⟨a,b,⟨v,av⟩,⟨w,bw⟩,far⟩ := nc
    let P := fun u => G.Reachable a u
    let Q := fun u => ¬P u
    let H := cut G P
    let K := cut G Q
    have pclose (u t : Fin n) (e : G.Adj u t) (h : P u) : P t := h.trans e.reachable
    have qclose (u t : Fin n) (e : G.Adj u t) (h : Q u) : Q t := fun hit => h (pclose _ _ e.symm hit)
    have ha : P a := SimpleGraph.Reachable.refl a
    have h1 : H.Adj a v := ⟨av,ha,pclose _ _ av ha⟩
    have h2 : K.Adj b w := ⟨bw,far,qclose _ _ bw far⟩
    refine ⟨H,K,?_,lt_of_le_not_ge (le G P) ?_,lt_of_le_not_ge (le G Q) ?_,?_,⟨a,v,h1⟩,⟨b,w,h2⟩,?_,?_⟩
    · ext i j
      constructor
      · intro e
        by_cases h : P i
        · exact Or.inl ⟨e,h,pclose _ _ e h⟩
        · exact Or.inr ⟨e,h,qclose _ _ e h⟩
      · exact fun h => h.elim (fun e => e.1) (fun e => e.1)
    · intro bad;exact far (bad bw).2.1
    · intro bad;exact (bad av).2.1 ha
    · intro u v w h k;exact k.2.1 h.2.1
    · intro u bad
      letI : DecidableRel (cut G P).Adj := Classical.decRel _
      change (cut G P).degree u=1 at bad
      rcases degree G P pclose u with z|same
      · omega
      · exact leaf u (same.symm.trans bad)
    · intro u bad
      letI : DecidableRel (cut G Q).Adj := Classical.decRel _
      change (cut G Q).degree u=1 at bad
      rcases degree G Q qclose u with z|same
      · omega
      · exact leaf u (same.symm.trans bad)
  have out_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (edge : ∃ a b,G.Adj a b)
      (sem : circuitFun n C=graphFun G ∅) : C.output<n+C.gates.length := by
    by_contra! bad
    obtain ⟨u,v,e⟩ := edge
    have yes := (congrFun sem (pairInput u v)).trans (pair_true G u v e)
    have no := val_ge (C:=C) (x:=List.ofFn (pairInput u v)) (n:=n) (by simp) bad
    change val C (List.ofFn (pairInput u v)) C.output=true at yes
    rw [yes] at no;contradiction
  have union_fun {n : ℕ} (H K : SimpleGraph (Fin n)) [DecidableRel H.Adj] [DecidableRel K.Adj]
      [DecidableRel (H⊔K).Adj] (x : Fin n → Bool) :
      graphFun (H⊔K) ∅ x=(graphFun H ∅ x || graphFun K ∅ x) := by
    apply Bool.eq_iff_iff.mpr
    rw [Bool.or_eq_true_iff,graph_true,graph_true,graph_true]
    constructor
    · rintro ⟨u,v,adj,hu,hv⟩
      exact adj.elim (fun e => Or.inl ⟨u,v,e,hu,hv⟩) (fun e => Or.inr ⟨u,v,e,hu,hv⟩)
    · rintro (⟨u,v,e,hu,hv⟩|⟨u,v,e,hu,hv⟩)
      · exact ⟨u,v,Or.inl e,hu,hv⟩
      · exact ⟨u,v,Or.inr e,hu,hv⟩
  have sq_sub {n : ℕ} (G H : SimpleGraph (Fin n)) [DecidableRel G.Adj] [DecidableRel H.Adj] (le : H≤G) (s : NoFourCycle G) : NoFourCycle H := by
    intro a b diff
    apply le_trans (Finset.card_le_card (fun w h => Finset.mem_filter.mpr ⟨Finset.mem_univ _,le (Finset.mem_filter.mp h).2.1,le (Finset.mem_filter.mp h).2.2⟩)) (s a b diff)
  let Result {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : Prop := ∃ C : Circuit, IsMinimalMonoCircuit n C ∧ circuitFun n C=graphFun G ∅ ∧
    ∀ j<C.gates.length,(gateAt C j).op=.and → ∃ u v,G.Adj u v ∧ Owns n C j u v
  intro n
  have ind (m : ℕ) : ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], G.edgeFinset.card=m →
      (∀ a b c,G.Adj a b → G.Adj b c → ¬G.Adj c a) → NoFourCycle G →
      (∃ a b,G.Adj a b) → (∀ u,G.degree u≠1) → Result G := by
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro G inst card tri sq edge leaf
      by_cases conn : ConnectedSupport G
      · exact connected n G tri sq edge leaf conn
      obtain ⟨H,K,eq,hH,hK,dis,eH,eK,dH,dK⟩ := split G conn leaf
      let recurse (J : SimpleGraph (Fin n)) (sub : J<G) (ej : ∃ a b,J.Adj a b) (dj : ∀ u,J.degree u≠1) : Result J :=
        ih J.edgeFinset.card (card ▸ Finset.card_lt_card (SimpleGraph.edgeFinset_strict_mono sub)) J rfl
          (fun a b c ab bc ca => tri a b c (sub.le ab) (sub.le bc) (sub.le ca)) (sq_sub G J sub.le sq) ej dj
      obtain ⟨A,mA,fA,ownsA⟩ := recurse H hH eH dH
      obtain ⟨B,mB,fB,ownsB⟩ := recurse K hK eK dK
      subst G
      let E := join n A B
      have fE : circuitFun n E=graphFun (H⊔K) ∅ := by
        funext x
        rw [union_fun,←fA,←fB]
        exact sem A B (out_bound H A eH fA) (out_bound K B eK fB) x
      refine ⟨E,⟨mono A B mA.1 mB.1,?_⟩,fE,owned_union H K A B ownsA ownsB⟩
      intro D md fd
      obtain ⟨L,R,ml,fl,mr,fr,cost⟩ := lower n H K dis eH eK tri sq leaf D md (fd.trans fE)
      have l := mA.2 L ml (fl.trans fA.symm)
      have r := mB.2 R mr (fr.trans fB.symm)
      change (join n A B).size≤D.size
      rw [size_join]
      omega
  intro G inst
  exact ind _ G rfl
