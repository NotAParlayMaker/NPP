import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
open PEqualNP.HeptadCover PEqualNP.GenericRejection

-- The last gate is one of the two outputs and the other is an earlier gate.
-- Reading the earlier output inside the circuit is redundant for the union of the outputs.

set_option maxHeartbeats 4500000 in
set_option maxRecDepth 10000 in
theorem PEqualNP.Outside.R_meta_1872_587
    (flatCount : ∀ (C : Circuit) (a : ℕ), Monotone2 C → ReadsBack 26 C →
      26 ≤ a → a < C.output → C.output = 25 + C.size →
      (¬ (∃ i j, (gateAt C i).op = GateOp.and ∧ (gateAt C j).op = GateOp.and ∧ InCone 26 C i j)) →
      have W := fun (w : ℕ) (X Y : Finset (Fin 13)) => (C.wires (incidenceInput X Y)).getD w false
      (∀ p l : Fin 13, p ∈ singerLines3 l →
        W a {p} {l} = true ∨ W C.output {p} {l} = true) →
      (∀ Q, IsQuadrangle singerLines3 Q →
        W a Q (missLines singerLines3 Q) = false ∧ W C.output Q (missLines singerLines3 Q) = false) →
      (∃ p l : Fin 13, p ∈ singerLines3 l ∧ W a {p} {l} = true ∧ W C.output {p} {l} = false) →
      (∃ p l : Fin 13, p ∈ singerLines3 l ∧ W C.output {p} {l} = true ∧ W a {p} {l} = false) →
      63 ≤ C.size)
    (nestedIndependent : ∀ (C : Circuit) (a : ℕ), Monotone2 C → ReadsBack 26 C →
      26 ≤ a → a < C.output → C.output = 25 + C.size →
      ((∃ i j, (gateAt C i).op = GateOp.and ∧ (gateAt C j).op = GateOp.and ∧ InCone 26 C i j) ∧ ∀ g ∈ C.gates, a ∉ g.inputs) →
      have W := fun (w : ℕ) (X Y : Finset (Fin 13)) => (C.wires (incidenceInput X Y)).getD w false
      (∀ p l : Fin 13, p ∈ singerLines3 l →
        W a {p} {l} = true ∨ W C.output {p} {l} = true) →
      (∀ Q, IsQuadrangle singerLines3 Q →
        W a Q (missLines singerLines3 Q) = false ∧ W C.output Q (missLines singerLines3 Q) = false) →
      (∃ p l : Fin 13, p ∈ singerLines3 l ∧ W a {p} {l} = true ∧ W C.output {p} {l} = false) →
      (∃ p l : Fin 13, p ∈ singerLines3 l ∧ W C.output {p} {l} = true ∧ W a {p} {l} = false) →
      63 ≤ C.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 →     PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x1 →       x2 < (26 : ℕ) + x1.size →         x3 < (26 : ℕ) + x1.size →           have x8 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};           have x9 : Fin (13 : ℕ) → Fin (13 : ℕ) → List Bool := fun (x9 x10 : Fin (13 : ℕ)) => (List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 = x9)) ++ List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 = x10);           have x10 : Finset (Fin (13 : ℕ)) → List Bool := fun (x10 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 ∈ x10)) ++ List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (∀ x12 ∈ x10, x12 - x11 ∉ x8);           have x11 : Finset (Fin (13 : ℕ)) → Prop := fun (x11 : Finset (Fin (13 : ℕ))) => x11.card = (4 : ℕ) ∧ ∀ (x12 : Fin (13 : ℕ)), {x13 ∈ x11 | x13 - x12 ∈ x8}.card ≤ (2 : ℕ);           have x12 : ℕ → List Bool → Bool := fun (x12 : ℕ) (x13 : List Bool) => (x1.wires x13).getD x12 Bool.false;           (∀ (x13 x14 : Fin (13 : ℕ)), x13 - x14 ∈ x8 → x12 x2 (x9 x13 x14) = Bool.true ∨ x12 x3 (x9 x13 x14) = Bool.true) → (∀ (x14 : Finset (Fin (13 : ℕ))), x11 x14 → x12 x2 (x10 x14) = Bool.false ∧ x12 x3 (x10 x14) = Bool.false) → (∃ (x15 : Fin (13 : ℕ)) (x16 : Fin (13 : ℕ)), x15 - x16 ∈ x8 ∧ x12 x2 (x9 x15 x16) = Bool.true ∧ x12 x3 (x9 x15 x16) = Bool.false) → (∃ (x16 : Fin (13 : ℕ)) (x17 : Fin (13 : ℕ)), x16 - x17 ∈ x8 ∧ x12 x3 (x9 x16 x17) = Bool.true ∧ x12 x2 (x9 x16 x17) = Bool.false) → (63 : ℕ) ≤ x1.size := by
  intro C a b basis back aRange bRange S P N Good V accepted rejected aOnly bOnly
  have inc : ∀ p l : Fin 13, p-l ∈ ({0,1,3,9} : Finset (Fin 13)) ↔ p ∈ singerLines3 l := by
    decide +kernel
  have incidence (p l : Fin 13) : p-l ∈ S ↔ p ∈ singerLines3 l := inc p l
  have positiveInput (p l : Fin 13) : P p l = incidenceInput {p} {l} := by
    change ((List.ofFn fun q : Fin 13 => decide (q=p)) ++ (List.ofFn fun m : Fin 13 => decide (m=l))) =
      ((List.ofFn fun q : Fin 13 => decide (q∈({p} : Finset (Fin 13)))) ++
        (List.ofFn fun m : Fin 13 => decide (m∈({l} : Finset (Fin 13)))))
    simp only [Finset.mem_singleton]
  have negativeInput (Q : Finset (Fin 13)) : N Q = incidenceInput Q (missLines singerLines3 Q) := by
    have miss (l : Fin 13) : (∀ p ∈ Q, p-l ∉ S) ↔ l ∈ missLines singerLines3 Q := by
      change (∀ p ∈ Q, p-l ∉ S) ↔ l ∈ Finset.univ.filter
        (fun m : Fin 13 => Disjoint (singerLines3 m) Q)
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.disjoint_left]
      constructor
      · intro h p on inside
        exact h p inside ((incidence p l).mpr on)
      · intro h p inside on
        exact h ((incidence p l).mp on) inside
    have h : (fun l : Fin 13 => decide (∀ p ∈ Q, p-l ∉ S)) =
        (fun l : Fin 13 => decide (l ∈ missLines singerLines3 Q)) := by
      funext l
      exact decide_eq_decide.mpr (miss l)
    exact congrArg (fun right : Fin 13 → Bool =>
      List.ofFn (fun p : Fin 13 => decide (p ∈ Q)) ++ List.ofFn right) h
  have good (Q : Finset (Fin 13)) : Good Q ↔ IsQuadrangle singerLines3 Q := by
    have e (l : Fin 13) : (Q.filter (fun p => p-l ∈ S)) = Q ∩ singerLines3 l := by
      ext p
      simp only [Finset.mem_filter,Finset.mem_inter,incidence]
    change (Q.card=4 ∧ ∀ l,(Q.filter fun p => p-l∈S).card≤2) ↔
      (Q.card=4 ∧ ∀ l,(Q ∩ singerLines3 l).card≤2)
    simp only [e]
  let value (D : Circuit) (w : ℕ) (X Y : Finset (Fin 13)) := (D.wires (incidenceInput X Y)).getD w false
  have positive : ∀ p l : Fin 13, p ∈ singerLines3 l →
      value C a {p} {l} = true ∨ value C b {p} {l} = true := by
    intro p l hp
    have h := accepted p l ((incidence p l).mpr hp)
    rw [positiveInput] at h
    exact h
  have negative : ∀ Q, IsQuadrangle singerLines3 Q →
      value C a Q (missLines singerLines3 Q) = false ∧ value C b Q (missLines singerLines3 Q) = false := by
    intro Q hQ
    have h := rejected Q ((good Q).mpr hQ)
    rw [negativeInput] at h
    exact h
  have aWitness : ∃ p l : Fin 13, p∈singerLines3 l ∧ value C a {p} {l}=true ∧ value C b {p} {l}=false := by
    obtain ⟨p,l,h,hp,hl⟩ := aOnly
    rw [positiveInput] at hp hl
    exact ⟨p,l,(incidence p l).mp h,hp,hl⟩
  have bWitness : ∃ p l : Fin 13, p∈singerLines3 l ∧ value C b {p} {l}=true ∧ value C a {p} {l}=false := by
    obtain ⟨p,l,h,hp,hl⟩ := bOnly
    rw [positiveInput] at hp hl
    exact ⟨p,l,(incidence p l).mp h,hp,hl⟩
  have rawLit : ∀ i : Fin 26, ∃ j : Fin 13,
      have Q : Finset (Fin 13) := {j,j+1,j+2,j+5}
      IsQuadrangle singerLines3 Q ∧
        (incidenceInput Q (missLines singerLines3 Q)).getD i.val false = true := by
    decide +kernel
  have lenInputs (X Y : Finset (Fin 13)) : (incidenceInput X Y).length = 26 := by
    change ((List.ofFn fun p : Fin 13 => decide (p∈X)) ++
      (List.ofFn fun l : Fin 13 => decide (l∈Y))).length = 26
    simp
  let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have keep (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl step w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      change (gs.foldl step (step w g)).getD i false = _
      rw [ih _ (by simp [step]; omega)]
      exact List.getD_append _ _ _ _ hi
  have lengthRun (gs : List Gate) (w : List Bool) : (gs.foldl step w).length = w.length+gs.length := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      change (gs.foldl step (step w g)).length = _
      rw [ih]
      simp only [step,List.length_cons,List.length_nil,List.length_append]
      omega
  have atGate (u : ℕ)
      (sound : ∀ Q, IsQuadrangle singerLines3 Q →
        value C u Q (missLines singerLines3 Q) = false) : 26 ≤ u := by
    by_contra! raw
    obtain ⟨t,legal,lit⟩ := rawLit ⟨u,raw⟩
    let Q : Finset (Fin 13) := {t,t+1,t+2,t+5}
    have wire := sound Q legal
    change (C.gates.foldl step (incidenceInput Q (missLines singerLines3 Q))).getD u false = false at wire
    rw [keep _ _ _ (by rw [lenInputs]; exact raw)] at wire
    exact Bool.noConfusion (lit.symm.trans wire)
  have aGate : 26 ≤ a := atGate a (fun Q h => (negative Q h).1)
  have bGate : 26 ≤ b := atGate b (fun Q h => (negative Q h).2)
  have distinct : a ≠ b := by
    intro same
    obtain ⟨p,l,_,on,off⟩ := aWitness
    exact Bool.noConfusion (on.symm.trans (same.symm ▸ off))
  have ordered (u w : ℕ) (hu : 26≤u) (hw : 26≤w) (order : u<w) (topRange : w<26+C.size)
      (yes : ∀ p l : Fin 13, p∈singerLines3 l → value C u {p} {l}=true ∨ value C w {p} {l}=true)
      (no : ∀ Q, IsQuadrangle singerLines3 Q →
        value C u Q (missLines singerLines3 Q)=false ∧ value C w Q (missLines singerLines3 Q)=false)
      (uOnly : ∃ p l : Fin 13, p∈singerLines3 l ∧ value C u {p} {l}=true ∧ value C w {p} {l}=false)
      (wOnly : ∃ p l : Fin 13, p∈singerLines3 l ∧ value C w {p} {l}=true ∧ value C u {p} {l}=false) :
      63 ≤ C.size := by
    let k := w-26+1
    have kfit : k ≤ C.size := by dsimp [k]; omega
    let D : Circuit := ⟨C.gates.take k,w⟩
    have dSize : D.size = k := List.length_take_of_le kfit
    have dOut : D.output = 25+D.size := by
      change w = 25+D.size
      rw [dSize]
      dsimp [k]
      omega
    have dMono : Monotone2 D := by
      intro g hg
      exact basis g (List.mem_of_mem_take hg)
    have dBack : ReadsBack 26 D := by
      intro j hj i hi
      have hjC : j<C.gates.length := hj.trans_le (by rw [show D.gates.length = D.size from rfl,dSize]; exact kfit)
      have eq : gateAt D j = gateAt C j := by
        change D.gates.getD j ⟨GateOp.or,[]⟩ = C.gates.getD j ⟨GateOp.or,[]⟩
        rw [List.getD_eq_getElem _ _ hj,List.getD_eq_getElem _ _ hjC]
        exact List.getElem_take
      exact back j hjC i (eq ▸ hi)
    have dValue (z : ℕ) (hz : z ≤ w) (X Y : Finset (Fin 13)) : value D z X Y = value C z X Y := by
      let x := incidenceInput X Y
      change ((C.gates.take k).foldl step x).getD z false = (C.gates.foldl step x).getD z false
      have e : C.gates.foldl step x = (C.gates.drop k).foldl step ((C.gates.take k).foldl step x) := by
        rw [← List.foldl_append,List.take_append_drop]
      rw [e]
      exact (keep (C.gates.drop k) ((C.gates.take k).foldl step x) z (by
        rw [lengthRun,List.length_take_of_le kfit]
        have len : x.length=26 := lenInputs X Y
        rw [len]
        dsimp [k]
        omega)).symm
    have dYes : ∀ p l : Fin 13, p∈singerLines3 l →
        value D u {p} {l}=true ∨ value D w {p} {l}=true := by
      intro p l hp
      simpa only [dValue u order.le,dValue w le_rfl] using yes p l hp
    have dNo : ∀ Q, IsQuadrangle singerLines3 Q →
        value D u Q (missLines singerLines3 Q)=false ∧ value D w Q (missLines singerLines3 Q)=false := by
      intro Q hQ
      simpa only [dValue u order.le,dValue w le_rfl] using no Q hQ
    have du : ∃ p l : Fin 13, p∈singerLines3 l ∧ value D u {p} {l}=true ∧ value D w {p} {l}=false := by
      simpa only [dValue u order.le,dValue w le_rfl] using uOnly
    have dw : ∃ p l : Fin 13, p∈singerLines3 l ∧ value D w {p} {l}=true ∧ value D u {p} {l}=false := by
      simpa only [dValue u order.le,dValue w le_rfl] using wOnly

    classical
    let remove (g : Gate) : Gate :=
      if u ∈ g.inputs then
        if g.op = GateOp.and then ⟨.or,[]⟩
        else ⟨g.op,g.inputs.filter (fun i => decide (i ≠ u))⟩
      else g
    let E : Circuit := ⟨D.gates.map remove,D.output⟩
    have eSize : E.size = D.size := List.length_map ..
    have eOut : E.output = 25+E.size := by rw [eSize]; exact dOut
    have absent (g : Gate) : u ∉ (remove g).inputs := by
      unfold remove
      split <;> rename_i h
      · split
        · simp
        · simp only [List.mem_filter,decide_eq_true_eq,ne_eq,not_true_eq_false,and_false,not_false_eq_true]
      · exact h
    have subPins (g : Gate) (i : ℕ) (h : i ∈ (remove g).inputs) : i ∈ g.inputs := by
      unfold remove at h
      split at h
      · split at h
        · simp at h
        · exact (List.mem_filter.mp h).1
      · exact h
    have preserved (g : Gate) (h : u ∉ g.inputs) : remove g = g := by
      exact if_neg h
    have evalAnd (x : List Bool) : GateOp.and.eval x = x.all id := rfl
    have evalOr (x : List Bool) : GateOp.or.eval x = x.any id := rfl
    have eMono : Monotone2 E := by
      intro t ht
      obtain ⟨g,hg,rfl⟩ := List.mem_map.mp ht
      have h := dMono g hg
      unfold remove
      split
      · split
        · simp
        · exact ⟨h.1,(List.length_filter_le _ _).trans h.2⟩
      · exact h
    have eBack : ReadsBack 26 E := by
      intro j hj i hi
      have equalLen : E.gates.length = D.gates.length := List.length_map ..
      have hjD : j < D.gates.length := equalLen ▸ hj
      have same : gateAt E j = remove (gateAt D j) := by
        change E.gates.getD j ⟨GateOp.or,[]⟩ = remove (D.gates.getD j ⟨GateOp.or,[]⟩)
        rw [List.getD_eq_getElem _ _ hj,List.getD_eq_getElem _ _ hjD]
        change (D.gates.map remove)[j]'hj = _
        exact List.getElem_map _
      rw [same] at hi
      exact dBack j hjD i (subPins _ _ hi)
    have eAbsent : ∀ g ∈ E.gates, u ∉ g.inputs := by
      intro g hg
      obtain ⟨t,_,rfl⟩ := List.mem_map.mp hg
      exact absent t
    let leW (x y : List Bool) := ∀ i : ℕ, x.getD i false = true → y.getD i false = true
    have leAppend (x y : List Bool) (hLen : x.length=y.length) (h : leW x y) (v v' : Bool)
        (newest : v = true → v'=true) : leW (x++[v]) (y++[v']) := by
      intro i yes
      by_cases hOld : i<x.length
      · rw [List.getD_append _ _ _ _ hOld] at yes
        rw [List.getD_append _ _ _ _ (hLen ▸ hOld)]
        exact h i yes
      · rw [List.getD_append_right _ _ _ _ (by omega)] at yes
        rw [List.getD_append_right _ _ _ _ (by omega),← hLen]
        cases hOff : i-x.length with
        | zero => exact newest (by simpa [hOff] using yes)
        | succ k => simp [hOff] at yes
    have monoGate (g : Gate) (ops : g.op=GateOp.and ∨ g.op=GateOp.or)
        (x y : List Bool) (h : leW x y) :
        g.op.eval (g.inputs.map (fun i => x.getD i false)) = true →
          g.op.eval (g.inputs.map (fun i => y.getD i false)) = true := by
      rcases ops with andOp|orOp
      · rw [andOp,evalAnd,evalAnd]
        simp only [List.all_map,Function.comp_apply,id_eq,List.all_eq_true]
        exact fun yes i hi => h i (yes i hi)
      · rw [orOp,evalOr,evalOr]
        simp only [List.any_map,Function.comp_apply,id_eq,List.any_eq_true]
        rintro ⟨i,hi,on⟩
        exact ⟨i,hi,h i on⟩
    have cutEvaluator (g : Gate) (ops : g.op=GateOp.and ∨ g.op=GateOp.or) (x : List Bool) :
        ((remove g).op.eval ((remove g).inputs.map (fun i => x.getD i false)) = true →
          g.op.eval (g.inputs.map (fun i => x.getD i false)) = true) ∧
        (x.getD u false = false →
          (remove g).op.eval ((remove g).inputs.map (fun i => x.getD i false)) =
            g.op.eval (g.inputs.map (fun i => x.getD i false))) := by
      by_cases reader : u∈g.inputs
      · rcases ops with andOp | orOp
        · have q : remove g = ⟨.or,[]⟩ := by unfold remove; rw [if_pos reader,if_pos andOp]
          rw [q]
          constructor
          · intro impossible
            change false=true at impossible
            cases impossible
          · intro off
            change false = g.op.eval (g.inputs.map (fun i => x.getD i false))
            rw [andOp,evalAnd]
            apply Bool.eq_iff_iff.mpr
            simp only [List.all_map,Function.comp_apply,id_eq,List.all_eq_true]
            refine ⟨fun h => Bool.noConfusion h,fun h => ?_⟩
            exact Bool.noConfusion ((h u reader).symm.trans off)
        · have nonAnd : g.op ≠ GateOp.and := fun e => GateOp.noConfusion (orOp.symm.trans e)
          have q : remove g = ⟨.or,g.inputs.filter (fun i => decide (i ≠ u))⟩ := by
            unfold remove
            rw [if_pos reader,if_neg nonAnd,orOp]
          rw [q,orOp]
          change ((GateOp.or.eval ((g.inputs.filter _).map _)) = true →
            (GateOp.or.eval (g.inputs.map _)) = true) ∧ _
          constructor
          · simp only [evalOr,List.any_map,Function.comp_apply,id_eq,List.any_eq_true]
            rintro ⟨i,hi,on⟩
            exact ⟨i,(List.mem_filter.mp hi).1,on⟩
          · intro off
            apply Bool.eq_iff_iff.mpr
            simp only [evalOr,List.any_map,Function.comp_apply,id_eq,List.any_eq_true]
            constructor
            · rintro ⟨i,hi,on⟩
              exact ⟨i,(List.mem_filter.mp hi).1,on⟩
            · rintro ⟨i,hi,on⟩
              have ne : i ≠ u := fun e => Bool.noConfusion (on.symm.trans (e.symm ▸ off))
              exact ⟨i,List.mem_filter.mpr ⟨hi,decide_eq_true ne⟩,on⟩
      · rw [preserved g reader]
        exact ⟨id,fun _ => rfl⟩
    have runLe (gs : List Gate) (basis : ∀ g ∈ gs, g.op=GateOp.and ∨ g.op=GateOp.or)
        (x y : List Bool) (len : x.length=y.length) (cmp : leW x y) :
        leW ((gs.map remove).foldl step x) (gs.foldl step y) := by
      induction gs generalizing x y with
      | nil => exact cmp
      | cons g gs ih =>
        have ops := basis g (by simp)
        change leW ((gs.map remove).foldl step (step x (remove g))) (gs.foldl step (step y g))
        apply ih (fun t ht => basis t (List.mem_cons_of_mem _ ht)) _ _
        · simp [step,len]
        · apply leAppend x y len cmp
          intro on
          exact monoGate g ops x y cmp ((cutEvaluator g ops x).1 on)
    have runEq (gs : List Gate) (basis : ∀ g ∈ gs, g.op=GateOp.and ∨ g.op=GateOp.or)
        (x : List Bool) (off : (gs.foldl step x).getD u false = false) :
        (gs.map remove).foldl step x = gs.foldl step x := by
      induction gs generalizing x with
      | nil => rfl
      | cons g gs ih =>
        have xOff : x.getD u false = false := by
          by_cases h : u < x.length
          · exact (keep _ _ _ h).symm.trans off
          · exact List.getD_eq_default _ _ (by omega)
        have evalEq := (cutEvaluator g (basis g (by simp)) x).2 xOff
        have new : step x (remove g) = step x g := by unfold step; rw [evalEq]
        change (gs.map remove).foldl step (step x (remove g)) = gs.foldl step (step x g)
        rw [new]
        exact ih (fun t ht => basis t (List.mem_cons_of_mem _ ht)) _ off
    have ops (g : Gate) (hg : g ∈ D.gates) : g.op=GateOp.and ∨ g.op=GateOp.or := by
      simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using (dMono g hg).1
    have less (X Y : Finset (Fin 13)) : leW (E.wires (incidenceInput X Y)) (D.wires (incidenceInput X Y)) :=
      runLe D.gates ops _ _ rfl (fun _ h => h)
    have equalIfOff (X Y : Finset (Fin 13)) (off : value D u X Y = false) :
        E.wires (incidenceInput X Y) = D.wires (incidenceInput X Y) := runEq D.gates ops _ off
    have outsideOff (X Y : Finset (Fin 13)) (z : ℕ) (oldOff : value D z X Y=false) : value E z X Y=false := by
      cases h : value E z X Y with
      | false => rfl
      | true => exact (Bool.false_ne_true (oldOff.symm.trans (less X Y z h))).elim
    have earlierSame (X Y : Finset (Fin 13)) : value E u X Y = value D u X Y := by
      let t := u-26+1
      let G := D.gates.take t
      have limit : t≤D.size := by dsimp [t]; omega
      have fixed : G.map remove = G := by
        conv_rhs => rw [← List.map_id G]
        apply List.map_congr_left
        intro g hg
        change g∈D.gates.take t at hg
        obtain ⟨j,hj,he⟩ := List.mem_iff_getElem.mp hg
        have hjD : j<D.gates.length := by
          rw [List.length_take_of_le limit] at hj
          exact hj.trans_le limit
        have old : gateAt D j = g := by
          change D.gates.getD j ⟨GateOp.or,[]⟩ = g
          rw [List.getD_eq_getElem _ _ hjD,← he]
          exact List.getElem_take.symm
        apply preserved
        intro reads
        have earlier := dBack j hjD u (old.symm ▸ reads)
        rw [List.length_take_of_le limit] at hj
        dsimp [t] at hj
        omega
      let x := incidenceInput X Y
      have xLen : x.length=26 := lenInputs X Y
      have uOn : u < (G.foldl step x).length := by
        rw [lengthRun,xLen]
        change u < 26+(D.gates.take t).length
        rw [List.length_take_of_le limit]
        dsimp [t]
        omega
      have split : D.gates = G++D.gates.drop t := (List.take_append_drop t D.gates).symm
      change ((D.gates.map remove).foldl step x).getD u false = (D.gates.foldl step x).getD u false
      rw [split,List.map_append,fixed,List.foldl_append,List.foldl_append,keep _ _ _ uOn,keep _ _ _ uOn]
    have ePos (p l : Fin 13) (h : p∈singerLines3 l) :
        value E u {p} {l}=true ∨ value E E.output {p} {l}=true := by
      change value E u {p} {l}=true ∨ value E w {p} {l}=true
      cases ha : value D u {p} {l}
      · have hb := (dYes p l h).resolve_left (by simp [ha])
        have he := equalIfOff {p} {l} ha
        exact .inr (by change (E.wires _).getD w false = true; rw [he]; exact hb)
      · exact .inl ((earlierSame _ _).trans ha)
    have eNeg (Q : Finset (Fin 13)) (h : IsQuadrangle singerLines3 Q) :
        value E u Q (missLines singerLines3 Q)=false ∧ value E E.output Q (missLines singerLines3 Q)=false :=
      ⟨outsideOff _ _ _ (dNo Q h).1,outsideOff _ _ _ (dNo Q h).2⟩
    have eu : ∃ p l : Fin 13, p∈singerLines3 l ∧ value E u {p} {l}=true ∧ value E E.output {p} {l}=false := by
      obtain ⟨p,l,h,yes,no⟩ := du
      exact ⟨p,l,h,(earlierSame _ _).trans yes,outsideOff _ _ _ no⟩
    have ew : ∃ p l : Fin 13, p∈singerLines3 l ∧ value E E.output {p} {l}=true ∧ value E u {p} {l}=false := by
      obtain ⟨p,l,h,yes,no⟩ := dw
      refine ⟨p,l,h,?_,(earlierSame _ _).trans no⟩
      have e := equalIfOff {p} {l} no
      change (E.wires _).getD w false = true
      rw [e]
      exact yes
    have result : 63≤E.size := by
      by_cases h : ∃ i j, (gateAt E i).op = GateOp.and ∧ (gateAt E j).op = GateOp.and ∧ InCone 26 E i j
      · exact nestedIndependent E u eMono eBack hu order eOut ⟨h,eAbsent⟩ ePos eNeg eu ew
      · exact flatCount E u eMono eBack hu order eOut h ePos eNeg eu ew
    rw [eSize,dSize] at result
    exact result.trans kfit
  rcases lt_or_gt_of_ne distinct with h | h
  · exact ordered a b aGate bGate h bRange positive negative aWitness bWitness
  · exact ordered b a bGate aGate h aRange
      (fun p l hp => (positive p l hp).symm) (fun Q hQ => (negative Q hQ).symm) bWitness aWitness
