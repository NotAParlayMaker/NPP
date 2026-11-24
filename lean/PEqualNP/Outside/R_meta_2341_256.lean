import Mathlib
import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
open PEqualNP.HeptadCover PEqualNP.GenericRejection PEqualNP.CleanedNonEdge PEqualNP.SplitCount

-- The counting argument for the second child adapts willakone's proof of
-- L-meta-2059 (PR 4283) to one omitted incidence and to local input probes.
set_option maxRecDepth 6000 in
theorem PEqualNP.Outside.R_meta_2341_256
  (pin : let d : Finset (Fin 13) := {0,1,3,9}
  ∀ (C : Circuit) (e : Fin 13 × Fin 13) (b : Bool),Monotone2 C →
  (∀ j : Fin C.gates.length,∀ w∈(C.gates.get j).inputs,w<27+j.val) →
  (∀ p l : Fin 13,p-l∈d → (p,l)≠e → C.eval (incidenceInput {p} {l}++[b])=true) →
  (∀ Q : Finset (Fin 13),Q.card=4 → (∀ l : Fin 13,(Q.filter fun p=>p-l∈d).card≤2) →
    C.eval (incidenceInput Q (Finset.univ.filter (fun l : Fin 13 => ∀p∈Q,p-l∉d))++[b])=false) →
  ∃ D : Circuit,Monotone2 D ∧ ReadsBack 26 D ∧ D.size=C.size ∧ (∀ p l : Fin 13,p∈singerLines3 l → (p,l)≠e → D.eval (incidenceInput {p} {l})=true) ∧ (∀ Q : Finset (Fin 13),IsQuadrangle singerLines3 Q → D.eval (incidenceInput Q (missLines singerLines3 Q))=false))
  (derive : ∀ (C : Circuit) (e : Fin 13 × Fin 13),Monotone2 C → ReadsBack 26 C →
  (∀ p l : Fin 13,p∈singerLines3 l → (p,l)≠e → C.eval (incidenceInput {p} {l})=true) →
  (∀ Q : Finset (Fin 13),IsQuadrangle singerLines3 Q → C.eval (incidenceInput Q (missLines singerLines3 Q))=false) →
C.size≤62 → let V := wireVal 26 C
  ∃ j w : ℕ,(gateAt C j).op=GateOp.and ∧ w∈(gateAt C j).inputs ∧
    (∃ i,(gateAt C i).op=GateOp.and ∧ (w=26+i ∨ 26≤w ∧ InCone 26 C i (w-26))) ∧
    (∀ y,V (26+j) y=true → V C.output y=true) ∧
    (∃ s t : Fin 26,gateVal 26 C j (pairInput s t)=true) ∧
    ∃ X : Finset (Fin 26),((X.card≤2 ∧ V (26+j) (fun u=>decide (u∈X))=true) ∨ X.card=22) ∧ V w (fun u=>decide (u∈X))=true ∧ ∀z∈X,V w (unitInput z)=false)
  (close : ∀ (C : Circuit) (e : Fin 13 × Fin 13),Monotone2 C → ReadsBack 26 C →
  (∀ p l : Fin 13,p∈singerLines3 l → (p,l)≠e → C.eval (incidenceInput {p} {l})=true) →
  (∀ Q : Finset (Fin 13),IsQuadrangle singerLines3 Q → C.eval (incidenceInput Q (missLines singerLines3 Q))=false) →
(let V := wireVal 26 C
  ∃ j w : ℕ,(gateAt C j).op=GateOp.and ∧ w∈(gateAt C j).inputs ∧
    (∃ i,(gateAt C i).op=GateOp.and ∧ (w=26+i ∨ 26≤w ∧ InCone 26 C i (w-26))) ∧
    (∀ y,V (26+j) y=true → V C.output y=true) ∧
    (∃ s t : Fin 26,gateVal 26 C j (pairInput s t)=true) ∧
    ∃ X : Finset (Fin 26),((X.card≤2 ∧ V (26+j) (fun u=>decide (u∈X))=true) ∨ X.card=22) ∧ V w (fun u=>decide (u∈X))=true ∧ ∀z∈X,V w (unitInput z)=false) → 63≤C.size) :
∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : Fin (13 : ℕ)) (x4 : Bool),   PEqualNP.MetaComplexity.Monotone2 x1 →     (∀ (x6 : Fin x1.gates.length), ∀ x7 ∈ (x1.gates.get x6).inputs, x7 < (27 : ℕ) + ↑x6) →       have x7 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};       have x8 : Fin (13 : ℕ) → Fin (13 : ℕ) → List Bool := fun (x8 x9 : Fin (13 : ℕ)) => (List.ofFn fun (x10 : Fin (13 : ℕ)) => Decidable.decide (x10 = x8)) ++ List.ofFn fun (x10 : Fin (13 : ℕ)) => Decidable.decide (x10 = x9);       have x9 : Finset (Fin (13 : ℕ)) → List Bool := fun (x9 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x10 : Fin (13 : ℕ)) => Decidable.decide (x10 ∈ x9)) ++ List.ofFn fun (x10 : Fin (13 : ℕ)) => Decidable.decide (∀ x11 ∈ x9, x11 - x10 ∉ x7);       have x10 : Finset (Fin (13 : ℕ)) → Prop := fun (x10 : Finset (Fin (13 : ℕ))) => x10.card = (4 : ℕ) ∧ ∀ (x11 : Fin (13 : ℕ)), {x12 ∈ x10 | x12 - x11 ∈ x7}.card ≤ (2 : ℕ);       (∀ (x11 x12 : Fin (13 : ℕ)), x11 - x12 ∈ x7 → x11 ≠ x2 ∨ x12 ≠ x3 → x1.eval (x8 x11 x12 ++ [x4]) = Bool.true) → (∀ (x12 : Finset (Fin (13 : ℕ))), x10 x12 → x1.eval (x9 x12 ++ [x4]) = Bool.false) → (63 : ℕ) ≤ x1.size := by
  intro C a b bit hm back
  dsimp only
  intro positive negative
  obtain ⟨D,md,bd,sz,pd,qd⟩ := pin C (a,b) bit hm back (by
    intro p l he hne
    change C.eval (((List.ofFn fun i : Fin 13=>decide (i∈({p} : Finset (Fin 13)))) ++
      List.ofFn (fun i : Fin 13=>decide (i∈({l} : Finset (Fin 13)))))++[bit])=true
    simp only [Finset.mem_singleton] 
    apply positive p l he
    by_contra! h
    exact hne (Prod.ext h.1 h.2)) (by
    intro Q h4 hq
    change C.eval (((List.ofFn fun i : Fin 13=>decide (i∈Q)) ++
      List.ofFn (fun l : Fin 13=>decide (l ∈ Finset.univ.filter (fun l : Fin 13 =>
        ∀p∈Q,p-l∉({0,1,3,9}:Finset (Fin 13))))))++[bit])=false
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    exact negative Q ⟨h4,hq⟩)
  by_contra! h
  have fail := derive D (a,b) md bd pd qd (by omega)
  have bound := close D (a,b) md bd pd qd fail
  omega
