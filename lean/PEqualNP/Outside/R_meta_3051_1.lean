import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.GenericRejection

theorem PEqualNP.Outside.R_meta_3051_1
    (price : ∀ (N : ℕ) (F : Fin N → Finset (Fin N)) (C : Circuit), (∀ p r, p≠r → ∃! l, p∈F l ∧ r∈F l) → Monotone2 C →
    (∀ X Y, X.card≤1 → Y.card≤1 → IsFalseInput F X Y → C.eval (incidenceInput X Y)=false) →
    let cheap := fun (D : Circuit) => Finset.univ.filter (fun (z : Fin N × Fin N) =>
      let init := (List.range (N+N)).map (fun i => if i=z.1.val ∨ i=N+z.2.val then 1 else 3)
      let costs := D.gates.foldl (fun (v : List ℕ) (g : Gate) =>
        let a := g.inputs.map (fun i => v.getD i 3)
        v ++ List.cons (ite (g.op.eval [] = true) (List.sum a) (List.foldr Nat.min 3 a)) ([] : List ℕ)) init
      costs.getD D.output 3≤2)
    (cheap C).card≤6*C.size)
    (residual : ∀ (q N : ℕ) (F : Fin N→Finset (Fin N)), 300≤q → N=q^2+q+1 → (∀ l, (F l).card=q+1) → (∀ p r, p≠r → ∃! l, p∈F l ∧ r∈F l) →
    let ok := fun (D : Circuit) => Monotone2 D ∧ RightOnIncidentPairs F D ∧
      ∀ X Y, Y.card≤q → IsFalseInput F X Y → D.eval (incidenceInput X Y)=false
    let cheap := fun (D : Circuit) => Finset.univ.filter (fun (z : Fin N × Fin N) =>
      let init := (List.range (N+N)).map (fun i => if i=z.1.val ∨ i=N+z.2.val then 1 else 3)
      let costs := D.gates.foldl (fun (v : List ℕ) (g : Gate) =>
        let a := g.inputs.map (fun i => v.getD i 3)
        v ++ List.cons (ite (g.op.eval [] = true) (List.sum a) (List.foldr Nat.min 3 a)) ([] : List ℕ)) init
      costs.getD D.output 3≤2)
    ∀ C, ok C → (∀ D, ok D → C.size≤D.size) →
    100*(cheap C).card<6*(N*q) → N*q≤100*C.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (300 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.MetaComplexity.Monotone2 x5 → (∀ (x11 x12 : Fin x2), x3 x11 x12 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x14 : Fin (x2 + x2)) => Decidable.decide (x14 = Fin.castAdd x2 x11 ∨ x14 = Fin.natAdd x2 x12)) = Bool.true) → (∀ (x12 : Fin (x2 + x2) → Bool), Fintype.card { x13 : Fin x2 // x12 (Fin.natAdd x2 x13) = Bool.true } ≤ x1 → (¬∃ (x14 : Fin x2) (x15 : Fin x2), x3 x14 x15 ∧ x12 (Fin.castAdd x2 x14) = Bool.true ∧ x12 (Fin.natAdd x2 x15) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x12 = Bool.false) → x2 * x1 ≤ (100 : ℕ) * x5.size := by
  intro q N I inst C hq ord reg unique mono pos sound
  let F (l : Fin N) := Finset.univ.filter (fun p => I p l)
  have mem (p l : Fin N) : p∈F l ↔ I p l := by simp [F]
  have regular (l : Fin N) : (F l).card=q+1 := (Fintype.card_subtype (fun p => I p l)).symm.trans (reg l)
  have joins (p r : Fin N) (ne : p≠r) : ∃! l, p∈F l ∧ r∈F l := by simpa only [mem] using unique p r ne
  have pack (X Y : Finset (Fin N)) : incidenceInput X Y =
      List.ofFn (Fin.append (fun p : Fin N => decide (p∈X)) (fun l : Fin N => decide (l∈Y))) := by
    rw [List.ofFn_fin_append];rfl
  have right : RightOnIncidentPairs F C := by
    intro l p e
    rw [pack]
    let flag := Fin.append (fun z : Fin N => decide (z∈({p} : Finset (Fin N))))
      (fun z : Fin N => decide (z∈({l} : Finset (Fin N))))
    have eq : flag = (fun i : Fin (N+N) => decide (i=Fin.castAdd N p ∨ i=Fin.natAdd N l)) := by
      funext i
      refine Fin.addCases (m:=N) (n:=N) (motive:=fun k=>flag k=decide (k=Fin.castAdd N p ∨ k=Fin.natAdd N l)) ?_ ?_ i
      · intro u
        simp only [flag,Fin.append_left,Finset.mem_singleton,decide_eq_decide,Fin.ext_iff,Fin.val_castAdd,Fin.val_natAdd]
        omega
      · intro u
        simp only [flag,Fin.append_right,Finset.mem_singleton,decide_eq_decide,Fin.ext_iff,Fin.val_castAdd,Fin.val_natAdd]
        omega
    change circuitFun (N+N) C flag=true
    rw [eq]
    exact pos p l ((mem p l).mp e)
  have quiet (X Y : Finset (Fin N)) (hy : Y.card≤q) (dis : IsFalseInput F X Y) :
      C.eval (incidenceInput X Y)=false := by
    let row := Fin.append (fun p : Fin N => decide (p∈X)) (fun l : Fin N => decide (l∈Y))
    have left (p : Fin N) : row (Fin.castAdd N p)=decide (p∈X) := Fin.append_left _ _ _
    have line (l : Fin N) : row (Fin.natAdd N l)=decide (l∈Y) := Fin.append_right _ _ _
    have active : Fintype.card {l : Fin N // row (Fin.natAdd N l)=true}=Y.card := by
      let e : {l : Fin N // row (Fin.natAdd N l)=true} ≃ {l : Fin N // l∈Y} :=
        Equiv.subtypeEquivRight (fun l=>by rw [line,decide_eq_true_eq])
      exact (Fintype.card_congr e).trans (Fintype.card_coe Y)
    rw [pack]
    apply sound row (active.le.trans hy)
    rintro ⟨p,l,e,hp,hl⟩
    simp only [left,line,decide_eq_true_eq] at hp hl
    exact Finset.disjoint_left.mp (dis l hl) ((mem _ _).mpr e) hp
  classical
  let ok := fun (D : Circuit) => Monotone2 D ∧ RightOnIncidentPairs F D ∧
    ∀ X Y, Y.card≤q → IsFalseInput F X Y → D.eval (incidenceInput X Y)=false
  have okC : ok C := ⟨mono,right,quiet⟩
  have ex : ∃ n : ℕ, ∃ D, ok D ∧ D.size=n := ⟨C.size,C,okC,rfl⟩
  obtain ⟨D,good,size⟩ := Nat.find_spec ex
  have least (E : Circuit) (he : ok E) : D.size≤E.size := size ▸ Nat.find_min' ex ⟨E,he,rfl⟩
  let cheap := fun (D : Circuit) => Finset.univ.filter (fun (z : Fin N × Fin N) =>
    let init := (List.range (N+N)).map (fun i => if i=z.1.val ∨ i=N+z.2.val then 1 else 3)
    let costs := D.gates.foldl (fun (v : List ℕ) (g : Gate) =>
    let a := g.inputs.map (fun i => v.getD i 3)
    v ++ List.cons (ite (g.op.eval [] = true) (List.sum a) (List.foldr Nat.min 3 a)) ([] : List ℕ)) init
    costs.getD D.output 3≤2)
  have smallRows (X Y : Finset (Fin N)) (_ : X.card≤1) (hy : Y.card≤1) (neg : IsFalseInput F X Y) :
      D.eval (incidenceInput X Y)=false := good.2.2 X Y (hy.trans (by omega)) neg
  have cap : (cheap D).card≤6*D.size := price N F D joins good.1 smallRows
  have narrow : N*q≤100*D.size := by
    by_cases low : 100*(cheap D).card<6*(N*q)
    · exact residual q N F hq ord regular joins D good least low
    · omega
  exact narrow.trans (Nat.mul_le_mul_left _ (least C okC))
