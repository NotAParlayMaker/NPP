import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm

-- Each wire records its values on the Fano boundary, the variables in its cone,
-- and the variables with singleton line-degree at least two.
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_4928_73
  (simulate : let act := fun (s : List ((Fin 58 → Bool) × Finset (Fin 14) × Finset (Fin 14))) (g : Bool × Fin 41 × Fin 41) =>
      let a := g.2.1.val
      let b := g.2.2.val
      let u := s.getD a (fun _ => false,∅,∅)
      let v := s.getD b (fun _ => false,∅,∅)
      if a=b ∨ s.length≤max a b then s else
        s ++ [(fun t => if g.1 then u.1 t && v.1 t else u.1 t || v.1 t,
          u.2.1∪v.2.1, (u.2.2∪v.2.2)∪(if g.1 then u.2.1∩v.2.1 else ∅))]
    ∀ (C : Circuit), C.size≤27 → IsAO2 14 C → (∀ g∈C.gates,g.inputs.Nodup) →
    C.output<14+C.size → ∀ (col : Fin 14 → Fin 58 → Bool),
    ∃ code : List (Bool × Fin 41 × Fin 41), code.length≤27 ∧
    ∃ z∈code.foldl act (List.ofFn (fun i : Fin 14 => (col i,({i} : Finset (Fin 14)),(∅ : Finset (Fin 14))))),
      (∀ t, z.1 t=C.eval (List.ofFn (fun i => col i t))) ∧
      ∀ i : Fin 14, i∈z.2.2 ↔ 2≤C.lineDeg 14 {i.val})
  (obstruct : let act := fun (s : List ((Fin 58 → Bool) × Finset (Fin 14) × Finset (Fin 14))) (g : Bool × Fin 41 × Fin 41) =>
      let a := g.2.1.val
      let b := g.2.2.val
      let u := s.getD a (fun _ => false,∅,∅)
      let v := s.getD b (fun _ => false,∅,∅)
      if a=b ∨ s.length≤max a b then s else
        s ++ [(fun t => if g.1 then u.1 t && v.1 t else u.1 t || v.1 t,
          u.2.1∪v.2.1, (u.2.2∪v.2.2)∪(if g.1 then u.2.1∩v.2.1 else ∅))]
    let col := fun (i : Fin 14) (t : Fin 58) => (([16771220242439,15270196031782968,58150373818816,94946423956573696,54820275478360064,3870282840506368,133412159488,182572334459126281,218716039641305168,189725234880873600,156548607028504576,229736628137050114,270286071509155872,288160007408582916] : List Nat).getD i.val 0).testBit t.val
    ∀ (code : List (Bool × Fin 41 × Fin 41)), code.length≤27 → ∀ z∈code.foldl act (List.ofFn (fun i : Fin 14 => (col i,({i} : Finset (Fin 14)),(∅ : Finset (Fin 14))))),
    (∀ t : Fin 58,z.1 t=decide (t.val<21)) →
    ∀ p l : Fin 7, (p=l ∨ p=l+1 ∨ p=l+3) →
      ¬(Fin.castAdd 7 p∈z.2.2 ∧ Fin.natAdd 7 l∈z.2.2)) :
have x1 : Fin (7 : ℕ) → Fin (7 : ℕ) → Prop := fun (x1 x2 : Fin (7 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (7 : ℕ)) ∨ x1 = x2 + (3 : Fin (7 : ℕ)); have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => x2.size ≤ (27 : ℕ) ∧ (∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x3]? = Option.some x4 → (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x4.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x6 : ℕ) (x7 : ℕ), x4.inputs = [x6, x7] ∧ x6 ≠ x7 ∧ x6 < (14 : ℕ) + x3 ∧ x7 < (14 : ℕ) + x3) ∧ ∀ (x3 : Fin (14 : ℕ) → Bool), x2.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (7 : ℕ)) (x5 : Fin (7 : ℕ)), x1 x4 x5 ∧ x3 (Fin.castAdd (7 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (7 : ℕ) x5) = Bool.true; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => (List.filter (fun (x4 : ℕ) => Decidable.decide ((14 : ℕ) ≤ x4)) (x3.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x3.gates)).Nodup; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 x6 : Fin (7 : ℕ)), x2 x4 → x1 x5 x6 → (2 : ℕ) ≤ x4.lineDeg (14 : ℕ) {↑x5} → (2 : ℕ) ≤ x4.lineDeg (14 : ℕ) {(7 : ℕ) + ↑x6} → (2 : ℕ) ≤ (PEqualNP.MetaComplexity.SingleLevel.andDepths x4 (14 : ℕ)).getD x4.output (0 : ℕ) → ¬x3 x4 → ∃ (x13 : PEqualNP.CircuitLowerBounds.Circuit), x2 x13 ∧ x3 x13 ∧ (2 : ℕ) ≤ x13.lineDeg (14 : ℕ) {↑x5} ∧ (2 : ℕ) ≤ x13.lineDeg (14 : ℕ) {(7 : ℕ) + ↑x6} := by
  intro inc valid tree C p l ok flag dp dl depth shared
  obtain ⟨limit,shape,truth⟩ := ok
  have gateInfo (g : Gate) (hg : g∈C.gates) : (g.op=.and ∨ g.op=.or) ∧ ∃ a b : Nat,g.inputs=[a,b] ∧ a≠b ∧ a<14+C.size ∧ b<14+C.size := by
    obtain ⟨j,hj,hg'⟩ := List.mem_iff_getElem.mp hg
    obtain ⟨op,a,b,pins,neq,ha,hb⟩ := shape j g (by simpa [List.getElem?_eq_getElem hj] using congrArg some hg')
    exact ⟨op,a,b,pins,neq,by change a<14+C.gates.length;omega,by change b<14+C.gates.length;omega⟩
  have ao : IsAO2 14 C := by
    refine ⟨fun g hg => (gateInfo g hg).1,?_,?_⟩
    · intro j hj w hw
      have eq : PEqualNP.MetaComplexity.NestedCover.gateAt C j=C.gates[j] := by
        change C.gates.getD j _ = _
        simp [List.getD_eq_getElem?_getD,hj]
      rw [eq] at hw
      obtain ⟨a,b,pins,_,ha,hb⟩ := (shape j C.gates[j] (List.getElem?_eq_getElem hj)).2
      rw [pins] at hw;simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
      rcases hw with rfl|rfl <;> assumption
    · intro g hg
      obtain ⟨a,b,h,_,_,_⟩ := (gateInfo g hg).2
      simp [h]
  have distinct : ∀g∈C.gates,g.inputs.Nodup := by
    intro g hg
    obtain ⟨a,b,h,d,_,_⟩ := (gateInfo g hg).2
    simp [h,d]
  have out : C.output<14+C.size := by
    have yes := (truth (fun _ => true)).mpr ⟨p,l,flag,rfl,rfl⟩
    by_contra! bad
    change (C.wires _).getD C.output false = true at yes
    rw [List.getD_eq_default] at yes
    · contradiction
    · let step (w : List Bool) (g : Gate) := w++[g.op.eval (g.inputs.map fun i => w.getD i false)]
      have len (gs : List Gate) (xs : List Bool) : (gs.foldl step xs).length = xs.length+gs.length := by
        induction gs generalizing xs with
        | nil => simp
        | cons g gs ih =>
          rw [List.foldl_cons,ih]
          simp [step]
          omega
      change (C.gates.foldl step (List.ofFn (fun _ : Fin 14 => true))).length ≤ C.output
      rw [len,List.length_ofFn]
      exact bad
  let col := fun (i : Fin 14) (t : Fin 58) => (([16771220242439,15270196031782968,58150373818816,94946423956573696,54820275478360064,3870282840506368,133412159488,182572334459126281,218716039641305168,189725234880873600,156548607028504576,229736628137050114,270286071509155872,288160007408582916] : List Nat).getD i.val 0).testBit t.val
  have table : ∀t : Fin 58,(∃ a b : Fin 7, (a=b ∨ a=b+1 ∨ a=b+3) ∧
      col (Fin.castAdd 7 a) t=true ∧ col (Fin.natAdd 7 b) t=true) ↔ t.val<21 := by
    dsimp only [col];decide +kernel
  obtain ⟨code,small,z,hz,values,degrees⟩ := simulate C limit ao distinct out col
  have hit : ∀ t : Fin 58, z.1 t=decide (t.val<21) := by
    intro t;rw [values];apply Bool.eq_iff_iff.mpr
    rw [decide_eq_true_iff]
    exact (truth _).trans (table t)
  exact False.elim (obstruct code small z hz hit p l flag
    ⟨(degrees (Fin.castAdd 7 p)).mpr dp,(degrees (Fin.natAdd 7 l)).mpr dl⟩)
