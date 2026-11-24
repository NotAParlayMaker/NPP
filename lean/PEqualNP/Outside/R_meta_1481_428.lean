import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.CleanedNonEdge

set_option maxRecDepth 12000 in
set_option maxHeartbeats 3000000 in
theorem PEqualNP.Outside.R_meta_1481_428
  (semantics : ∀ (C : Circuit) (n : ℕ),
    let W := fun (x : Fin n → Bool) (w : ℕ) => wireVal n C w x
    IsAO2 n C →
    (∀ w, Monotone (fun x => W x w)) ∧
    (∀ j a b, C.gates[j]? = some ⟨.and,[a,b]⟩ → ∀ x,
      W x (n+j) = (W x a && W x b)) ∧
    ∀ (base seed : Fin n → Bool), ∃ d : ℕ → Bool,
      (∀ i : Fin n, d i.val = seed i) ∧
      (∀ (j : ℕ) (g : Gate) (a b : ℕ), C.gates[j]? = some g → g.inputs = [a,b] →
        (g.op = .and → d (n+j) = ((W base a && d b) || (d a && W base b))) ∧
        (g.op = .or → d (n+j) = (d a || d b))))
  (search :
    let hit (x : Fin 26 → Bool) := ∃ p l : Fin 13,
      (p = l ∨ p = l+1 ∨ p = l+3 ∨ p = l+9) ∧
        x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true
    ∃ (C : Circuit) (j a b : ℕ) (u v : Fin 26), C.size ≤ 64 ∧ IsAO2 26 C ∧
      (∀ g ∈ C.gates, g.inputs.Nodup) ∧ C.output = 26+j ∧
      C.gates[j]? = some ⟨.and,[a,b]⟩ ∧
      (∀ x, C.eval (List.ofFn x) = true ↔ hit x) ∧
      wireVal 26 C a (fun i => decide (i = u)) = true ∧
      wireVal 26 C b (fun i => decide (i = v)) = true) : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, C.size ≤ 64 ∧ (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ a b : ℕ, g.inputs = [a, b] ∧ a ≠ b ∧ a < 26 + j ∧ b < 26 + j) ∧ (∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔ ∃ u t : Fin 13, (u = t ∨ u = t + 1 ∨ u = t + 3 ∨ u = t + 9) ∧ x (Fin.castAdd 13 u) = true ∧ x (Fin.natAdd 13 t) = true) ∧ ∃ p l : Fin 13, (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) ∧ (∃ v : ℕ → Bool, (∀ my : Fin 13, v my.val = false ∧ v (13 + my.val) = decide (my = l)) ∧ (∀ (ky : ℕ) (hy : PEqualNP.CircuitLowerBounds.Gate) (cy dy : ℕ), C.gates[ky]? = some hy → hy.inputs = [cy, dy] → (hy.op = PEqualNP.CircuitLowerBounds.GateOp.and → v (26 + ky) = (((C.wires (List.ofFn (fun iy : Fin 26 => decide (iy = Fin.castAdd 13 p)))).getD cy false && v dy) || (v cy && (C.wires (List.ofFn (fun ey : Fin 26 => decide (ey = Fin.castAdd 13 p)))).getD dy false))) ∧ (hy.op = PEqualNP.CircuitLowerBounds.GateOp.or → v (26 + ky) = (v cy || v dy))) ∧ v C.output = false) ∧ (∃ w : ℕ → Bool, (∀ mx : Fin 13, w mx.val = decide (mx = p) ∧ w (13 + mx.val) = false) ∧ (∀ (kx : ℕ) (hx : PEqualNP.CircuitLowerBounds.Gate) (cx dx : ℕ), C.gates[kx]? = some hx → hx.inputs = [cx, dx] → (hx.op = PEqualNP.CircuitLowerBounds.GateOp.and → w (26 + kx) = (((C.wires (List.ofFn (fun ix : Fin 26 => decide (ix = Fin.natAdd 13 l)))).getD cx false && w dx) || (w cx && (C.wires (List.ofFn (fun ex : Fin 26 => decide (ex = Fin.natAdd 13 l)))).getD dx false))) ∧ (hx.op = PEqualNP.CircuitLowerBounds.GateOp.or → w (26 + kx) = (w cx || w dx))) ∧ w C.output = false) := by
  let incident (p l : Fin 13) : Prop := p = l ∨ p = l+1 ∨ p = l+3 ∨ p = l+9
  let pt (p : Fin 13) : Fin 26 := Fin.castAdd 13 p
  let ln (l : Fin 13) : Fin 26 := Fin.natAdd 13 l
  let hit (x : Fin 26 → Bool) : Prop :=
    ∃ p l, incident p l ∧ x (pt p) = true ∧ x (ln l) = true
  let single (a : Fin 26) (i : Fin 26) : Bool := decide (i = a)
  let pair (a b : Fin 26) (i : Fin 26) : Bool := decide (i = a ∨ i = b)
  have disjoint (p l : Fin 13) : pt p ≠ ln l := by
    intro e
    have val : p.val = 13+l.val := congrArg Fin.val e
    have := p.isLt
    omega
  let adjacent (a b : Fin 26) : Bool :=
    Fin.addCases (fun p => Fin.addCases (fun _ : Fin 13 => false)
      (fun l : Fin 13 => decide (p = l ∨ p = l+1 ∨ p = l+3 ∨ p = l+9)) b)
      (fun l => Fin.addCases (fun p : Fin 13 => decide (p = l ∨ p = l+1 ∨ p = l+3 ∨ p = l+9))
        (fun _ : Fin 13 => false) b) a
  have onPair {a b : Fin 26} (h : hit (pair a b)) : adjacent a b = true := by
    obtain ⟨p,l,rel,hp,hl⟩ := h
    simp only [pair,decide_eq_true_eq] at hp hl
    rcases hp with ep | ep <;> rcases hl with el | el
    · exact (disjoint p l (ep.trans el.symm)).elim
    · subst a
      subst b
      simpa only [adjacent,pt,ln,Fin.addCases_left,Fin.addCases_right,decide_eq_true_eq,incident] using rel
    · subst a
      subst b
      simpa only [adjacent,pt,ln,Fin.addCases_left,Fin.addCases_right,decide_eq_true_eq,incident] using rel
    · exact (disjoint p l (ep.trans el.symm)).elim
  have diag : ((List.finRange 26).all fun a => (List.finRange 26).all fun b =>
      (List.finRange 13).any fun i => !adjacent a (pt i) && !adjacent a (ln i) &&
        !adjacent b (pt i) && !adjacent b (ln i)) = true := by decide +kernel
  obtain ⟨C,j,a,b,u,v,size,ao,noDup,out,root,computes,fromA,fromB⟩ := search
  obtain ⟨mono,andWire,derive⟩ := semantics C 26 ao
  have ru := List.all_eq_true.mp diag u (by simp)
  have rv := List.all_eq_true.mp ru v (by simp)
  obtain ⟨i,_,darkTable⟩ := List.any_eq_true.mp rv
  simp only [Bool.and_eq_true,Bool.not_eq_true'] at darkTable
  have noPair (t : Fin 26) (tMem : t = pt i ∨ t = ln i) :
      ¬ hit (pair u t) ∧ ¬ hit (pair v t) := by
    rcases tMem with rfl | rfl
    · exact ⟨fun h => Bool.noConfusion ((onPair h).symm.trans darkTable.1.1.1),
        fun h => Bool.noConfusion ((onPair h).symm.trans darkTable.1.2)⟩
    · exact ⟨fun h => Bool.noConfusion ((onPair h).symm.trans darkTable.1.1.2),
        fun h => Bool.noConfusion ((onPair h).symm.trans darkTable.2)⟩
  have leLeft (x y : Fin 26) : single x ≤ pair x y := by
    intro t
    by_cases eq : t = x <;> simp [single,pair,eq]
  have leRight (x y : Fin 26) : single y ≤ pair x y := by
    intro t
    by_cases eq : t = y <;> simp [single,pair,eq]
  have accepted (x : Fin 26 → Bool) (ha : wireVal 26 C a x = true) (hb : wireVal 26 C b x = true) :
      hit x := by
    apply (computes x).mp
    change wireVal 26 C C.output x = true
    have val : wireVal 26 C (26+j) x = (wireVal 26 C a x && wireVal 26 C b x) :=
      andWire j a b root x
    rw [out,val,ha,hb]
    rfl
  have dark (t : Fin 26) (tMem : t = pt i ∨ t = ln i) :
      wireVal 26 C a (single t) = false ∧ wireVal 26 C b (single t) = false := by
    have imp := noPair t tMem
    constructor
    · apply Bool.eq_false_iff.mpr
      intro ha
      have ma := mono a (leRight v t)
      have mb := mono b (leLeft v t)
      exact imp.2 (accepted (pair v t) (Bool.eq_true_of_true_le (ha ▸ ma))
        (Bool.eq_true_of_true_le (fromB ▸ mb)))
    · apply Bool.eq_false_iff.mpr
      intro hb
      have ma := mono a (leLeft u t)
      have mb := mono b (leRight u t)
      exact imp.1 (accepted (pair u t) (Bool.eq_true_of_true_le (fromA ▸ ma))
        (Bool.eq_true_of_true_le (hb ▸ mb)))
  have legal (k : ℕ) (g : Gate) (hg : C.gates[k]? = some g) :
      (g.op = .and ∨ g.op = .or) ∧ ∃ a b, g.inputs = [a,b] ∧ a ≠ b ∧ a < 26+k ∧ b < 26+k := by
    have mem := List.mem_iff_getElem?.2 ⟨k,hg⟩
    obtain ⟨a,b,shape⟩ := List.length_eq_two.mp (ao.2.2 g mem)
    have atGate : gateAt C k = g := by
      unfold gateAt
      simp [List.getD_eq_getElem?_getD,hg]
    have before := ao.2.1 k (List.getElem?_eq_some_iff.mp hg).1
    rw [atGate,shape] at before
    exact ⟨ao.1 _ mem,a,b,shape,by simpa [shape] using noDup g mem,before a (by simp),before b (by simp)⟩
  refine ⟨C,size,legal,computes,i,i,Or.inl rfl,?_,?_⟩
  · obtain ⟨d,init,step⟩ := derive (single (pt i)) (single (ln i))
    refine ⟨d,?_,step,?_⟩
    · intro t
      change d (pt t).val = false ∧ d (ln t).val = decide (t=i)
      rw [init (pt t), init (ln t)]
      constructor
      · exact decide_eq_false (disjoint t i)
      · have eq : ln t = ln i ↔ t = i := by
          refine ⟨fun h => Fin.ext ?_,congrArg ln⟩
          have vals : 13+t.val = 13+i.val := congrArg Fin.val h
          omega
        simp only [single,eq]
    · obtain ⟨da,db⟩ := dark (pt i) (Or.inl rfl)
      have rule : d (26+j) = ((wireVal 26 C a (single (pt i)) && d b) ||
          (d a && wireVal 26 C b (single (pt i)))) := (step j ⟨.and,[a,b]⟩ a b root rfl).1 rfl
      rw [out,rule,da,db]
      simp
  · obtain ⟨d,init,step⟩ := derive (single (ln i)) (single (pt i))
    refine ⟨d,?_,step,?_⟩
    · intro t
      change d (pt t).val = decide (t=i) ∧ d (ln t).val = false
      rw [init (pt t),init (ln t)]
      constructor
      · have eq : pt t = pt i ↔ t = i := by
          refine ⟨?_,congrArg pt⟩
          intro h
          have vals : (pt t).val = (pt i).val := congrArg Fin.val h
          exact Fin.ext vals
        simp only [single,eq]
      · exact decide_eq_false (Ne.symm (disjoint i t))
    · obtain ⟨da,db⟩ := dark (ln i) (Or.inr rfl)
      have rule : d (26+j) = ((wireVal 26 C a (single (ln i)) && d b) ||
          (d a && wireVal 26 C b (single (ln i)))) := (step j ⟨.and,[a,b]⟩ a b root rfl).1 rfl
      rw [out,rule,da,db]
      simp
