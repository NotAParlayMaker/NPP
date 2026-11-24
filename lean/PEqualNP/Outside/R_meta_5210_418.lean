import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.CleanedNonEdge

theorem PEqualNP.Outside.R_meta_5210_418
    (normalize : ∀ (n : ℕ) (C : Circuit) (a b : ℕ),
      let M := fun (E : Circuit) => IsAO2 n E ∧ ∀ g∈E.gates,g.inputs.Nodup
      let V := fun (E : Circuit) (i : ℕ) => ((gateAt E i).op,gateVal n E i,fun t : Fin 2 => wireVal n E (opnd E i t))
      let R := fun i => n+i=C.output ∨ InCone n C i (C.output-n)
      M C → a≠b → ¬ InCone n C a b → ¬ InCone n C b a → R a → R b →
      ∃ D k,M D ∧ D.size=C.size ∧
        (∀ x : Fin n → Bool,D.eval (List.ofFn x)=C.eval (List.ofFn x)) ∧
        (∀ i<C.size,∃ j<D.size,V D j=V C i) ∧ V D k=V C a ∧ V D (k+1)=V C b ∧
        InCone n D k (D.output-n) ∧ InCone n D (k+1) (D.output-n) ∧
        k+2<D.size ∧ ∀ w∈(gateAt D (k+1)).inputs,w<n+k)
    (residual : ∀ (D : Circuit) (k : ℕ),
      let S : Finset (Fin 13) := {0,1,3,9}
      let q := fun (i j : Fin 26) => pairInput i j
      let active := fun j z => (gateAt D j).op=GateOp.and ∧ gateVal 26 D j (q 0 13)=true ∧
        ∀ t : Fin 2,wireVal 26 D (opnd D j t) z=false
      let cone := fun j => InCone 26 D j (D.output-26)
      D.size≤64 → k≤61 → IsAO2 26 D → (∀ g∈D.gates,g.inputs.Nodup) →
      (∀ x : Fin 26 → Bool,D.eval (List.ofFn x)=true ↔ ∃ p l : Fin 13,
        p-l∈S ∧ x (Fin.castAdd 13 p)=true ∧ x (Fin.natAdd 13 l)=true) →
      (∃ j<D.size,(gateAt D j).op=GateOp.and ∧ ∃ x,gateVal 26 D j x=true ∧ D.eval (List.ofFn x)=false) →
      cone k → cone (k+1) → (∀ w∈(gateAt D (k+1)).inputs,w<26+k) →
      active k (q 0 0) → active (k+1) (q 13 13) → False) :
    ¬∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),     have x2 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};     have x3 : PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.CircuitLowerBounds.GateOp.and;     have x4 : ℕ → ℕ → Prop := PEqualNP.EdgeOwnership.InCone (26 : ℕ) x1;     have x5 : ℕ → (Fin (26 : ℕ) → Bool) → Bool := PEqualNP.EdgeOwnership.gateVal (26 : ℕ) x1;     have x6 : Fin (26 : ℕ) → Bool := PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) (0 : Fin (26 : ℕ));     have x7 : Fin (26 : ℕ) → Bool := PEqualNP.EdgeOwnership.pairInput (13 : Fin (26 : ℕ)) (13 : Fin (26 : ℕ));     have x8 : Fin (26 : ℕ) → Bool := PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) (13 : Fin (26 : ℕ));     have x9 : ℕ → (Fin (26 : ℕ) → Bool) → Prop := fun (x9 : ℕ) (x10 : Fin (26 : ℕ) → Bool) => (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x9).op = x3 ∧ ((26 : ℕ) + x9 = x1.output ∨ x4 x9 (x1.output - (26 : ℕ))) ∧ x5 x9 x8 = Bool.true ∧ ∀ (x11 : Fin (2 : ℕ)), PEqualNP.CleanedNonEdge.wireVal (26 : ℕ) x1 (PEqualNP.TopForm.opnd x1 x9 x11) x10 = Bool.false;     x1.size ≤ (64 : ℕ) ∧ (∀ (x10 : ℕ) (x11 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x10]? = Option.some x11 → (x11.op = x3 ∨ x11.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x13 : ℕ) (x14 : ℕ), x11.inputs = [x13, x14] ∧ x13 ≠ x14 ∧ x13 < (26 : ℕ) + x10 ∧ x14 < (26 : ℕ) + x10) ∧ (∀ (x10 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x10) = Bool.true ↔ ∃ (x11 : Fin (13 : ℕ)) (x12 : Fin (13 : ℕ)), x11 - x12 ∈ x2 ∧ x10 (Fin.castAdd (13 : ℕ) x11) = Bool.true ∧ x10 (Fin.natAdd (13 : ℕ) x12) = Bool.true) ∧ (∃ x10 < x1.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x10).op = x3 ∧ ∃ (x11 : Fin (26 : ℕ) → Bool), x5 x10 x11 = Bool.true ∧ x1.eval (List.ofFn x11) = Bool.false) ∧ ∃ (x10 : ℕ) (x11 : ℕ), x10 ≠ x11 ∧ ¬x4 x10 x11 ∧ ¬x4 x11 x10 ∧ x9 x10 x6 ∧ x9 x11 x7 := by
  classical
  rintro ⟨C,bound,gates,computes,dirty,a,b,ne,ab,ba,ma,mb⟩
  let n : ℕ := 26
  let M := fun (E : Circuit) => IsAO2 n E ∧ ∀ g∈E.gates,g.inputs.Nodup
  let V := fun (E : Circuit) (i : ℕ) => ((gateAt E i).op,gateVal n E i,fun t : Fin 2 => wireVal n E (opnd E i t))
  have atC {j} (hj : j<C.gates.length) : gateAt C j=C.gates[j] := List.getD_eq_getElem _ _ hj
  have each (i) (hi : i<C.gates.length) := gates i C.gates[i] (List.getElem?_eq_getElem hi)
  have lift (P : Gate → Prop) (h : ∀ i (hi : i<C.gates.length),P C.gates[i]) : ∀ g∈C.gates,P g := by
    intro g hg
    obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hg
    exact h i hi
  have m : M C := by
    refine ⟨⟨lift _ (fun i hi => (each i hi).1),?_,lift _ (fun i hi => ?_)⟩,lift _ (fun i hi => ?_)⟩
    · intro i hi w hw
      obtain ⟨s,t,ins,_,hs,ht⟩ := (each i hi).2
      rw [atC hi,ins] at hw
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
      rcases hw with rfl|rfl
      · exact hs
      · exact ht
    · obtain ⟨_,_,ins,_⟩ := (each i hi).2;rw [ins];rfl
    · obtain ⟨s,t,ins,st,_⟩ := (each i hi).2;simp [ins,st]
  obtain ⟨D,k,md,sz,ev,all,va,vb,ca,cb,room,parents⟩ :=
    normalize n C a b m ne ab ba ma.2.1 mb.2.1
  change V D k=V C a at va
  change V D (k+1)=V C b at vb
  have transfer (i j : ℕ) (eq : V D j=V C i) (x y : Fin n → Bool)
      (op : (gateAt C i).op=GateOp.and) (on : gateVal n C i x=true)
      (off : ∀ t : Fin 2,wireVal n C (opnd C i t) y=false) :
      (gateAt D j).op=GateOp.and ∧ gateVal n D j x=true ∧
      ∀ t : Fin 2,wireVal n D (opnd D j t) y=false := by
    exact ⟨(congrArg Prod.fst eq).trans op,(congrArg (fun v => v.2.1 x) eq).trans on,
      fun t => (congrArg (fun v => v.2.2 t y) eq).trans (off t)⟩
  apply residual D k (sz ▸ bound) (by omega) md.1 md.2
  · intro x;rw [ev];exact computes x
  · obtain ⟨i,hi,op,x,on,no⟩ := dirty
    obtain ⟨j,hj,eq⟩ := all i hi
    change V D j=V C i at eq
    exact ⟨j,hj,(congrArg Prod.fst eq).trans op,x,(congrArg (fun v => v.2.1 x) eq).trans on,(ev x).trans no⟩
  · exact ca
  · exact cb
  · exact parents
  · exact transfer a k va _ _ ma.1 ma.2.2.1 ma.2.2.2
  · exact transfer b (k+1) vb _ _ mb.1 mb.2.2.1 mb.2.2.2
