import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.HeptadCover PEqualNP.GenericRejection PEqualNP.EdgeOwnership

-- A bottom nested AND either fires on nine quadrangles or on at least seventeen.
-- If it fires on fewer than twenty-four, at most four incident pairs can activate it.
set_option maxHeartbeats 1500000 in
theorem PEqualNP.Outside.R_meta_2063_877
    (selectBottom : let inner := fun (C : Circuit) j => (gateAt C j).op=.and ∧ ∃ k, (gateAt C k).op=.and ∧ InCone 26 C j k
      ∀ C : Circuit, (∃ j,inner C j) → ∃ j,inner C j ∧ j<C.size ∧ (∀ i, InCone 26 C i j → (gateAt C i).op≠.and))
    (classify : let qrow := fun Q => incidenceInput Q (missLines singerLines3 Q)
      let dirt := fun (C : Circuit) (j : ℕ) => ((quadrangles singerLines3).filter fun Q => (C.wires (qrow Q)).getD (26+j) false=true).card
      let flags := fun (C : Circuit) (j : ℕ) => ((incidences singerLines3).filter fun e => (C.wires (incidenceInput {e.1} {e.2})).getD (26+j) false=true).card
      ∀ (C : Circuit) (j : ℕ), Monotone2 C → ReadsBack 26 C → j<C.size → (gateAt C j).op=.and → (∀ i, InCone 26 C i j → (gateAt C i).op≠.and) → 0<dirt C j → (dirt C j=9 ∨ 17≤dirt C j) ∧ (24≤dirt C j ∨ flags C j≤4))
    (residual : let qrow := fun Q => incidenceInput Q (missLines singerLines3 Q)
      let inner := fun (C : Circuit) j => (gateAt C j).op=.and ∧ ∃ k, (gateAt C k).op=.and ∧ InCone 26 C j k
      let dirt := fun (C : Circuit) (j : ℕ) => ((quadrangles singerLines3).filter fun Q => (C.wires (qrow Q)).getD (26+j) false=true).card
      let valid := fun (C : Circuit) => Monotone2 C ∧ ReadsBack 26 C ∧ RightOnIncidentPairs singerLines3 C ∧ ∀ Q ∈ quadrangles singerLines3,C.eval (qrow Q)=false
      let flags := fun (C : Circuit) (j : ℕ) => ((incidences singerLines3).filter fun e => (C.wires (incidenceInput {e.1} {e.2})).getD (26+j) false=true).card
      ∀ C : Circuit, valid C → C.size<64 → (∀ j,inner C j → 0<dirt C j) →
      (∃ j,inner C j ∧ (dirt C j=9 ∨ 17≤dirt C j) ∧ (24≤dirt C j ∨ flags C j≤4)) → ∃ D : Circuit, valid D ∧ D.size<C.size)
    : have x1 : Fin (13 : ℕ) → Bool := fun (x1 : Fin (13 : ℕ)) => Decidable.decide (x1 = (0 : Fin (13 : ℕ)) ∨ x1 = (1 : Fin (13 : ℕ)) ∨ x1 = (3 : Fin (13 : ℕ)) ∨ x1 = (9 : Fin (13 : ℕ))); have x2 : Finset (Fin (13 : ℕ)) → Prop := fun (x2 : Finset (Fin (13 : ℕ))) => x2.card = (4 : ℕ) ∧ ∀ (x3 : Fin (13 : ℕ)), {x4 ∈ x2 | x1 (x4 - x3) = Bool.true}.card ≤ (2 : ℕ); have x3 : Finset (Fin (13 : ℕ)) → List Bool := fun (x3 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 ∈ x3)) ++ List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (∀ x5 ∈ x3, x1 (x5 - x4) = Bool.false); have x4 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) => (∀ (x5 x6 : Fin (13 : ℕ)), x1 (x5 - x6) = Bool.true → x4.eval ((List.ofFn fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 = x5)) ++ List.ofFn fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 = x6)) = Bool.true) ∧ ∀ (x5 : Finset (Fin (13 : ℕ))), x2 x5 → x4.eval (x3 x5) = Bool.false; ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x5 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x5 → x4 x5 → x5.size < (64 : ℕ) → (∀ (x10 x11 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x11).op = PEqualNP.CircuitLowerBounds.GateOp.and → PEqualNP.EdgeOwnership.InCone (26 : ℕ) x5 x10 x11 → ∃ (x15 : Finset (Fin (13 : ℕ))), x2 x15 ∧ (x5.wires (x3 x15)).getD ((26 : ℕ) + x10) Bool.false = Bool.true) → (∃ (x11 : ℕ) (x12 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x11).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x12).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x5 x11 x12) → ∃ (x12 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x12 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x12 ∧ x4 x12 ∧ x12.size < x5.size := by
  intro flag quad original accepts C hm back ok small leaks nested
  let S := singerLines3
  let qr := fun Q => incidenceInput Q (missLines S Q)
  let inner := fun (E : Circuit) j => (gateAt E j).op=.and ∧ ∃ k, (gateAt E k).op=.and ∧ InCone 26 E j k
  let T := quadrangles S
  let bad := fun (E : Circuit) (j : ℕ) => T.filter fun Q => (E.wires (qr Q)).getD (26+j) false=true
  have incidence : ∀ p l : Fin 13, p∈S l ↔ flag (p-l)=true := by decide +kernel
  have member (Q : Finset (Fin 13)) : Q∈T ↔ quad Q := by
    have line (l : Fin 13) : Q∩S l=Q.filter (fun p => flag (p-l)=true) := by
      ext p
      simp only [Finset.mem_inter,Finset.mem_filter,incidence]
    change (Q∈((Finset.univ.powersetCard 4).filter fun Z : Finset (Fin 13) => ∀ l, (Z∩S l).card≤2)) ↔ _
    simp only [Finset.mem_filter,Finset.mem_powersetCard,Finset.subset_univ,true_and,line]
    rfl
  have same (Q : Finset (Fin 13)) : qr Q=original Q := by
    apply congrArg (List.append (List.ofFn fun p : Fin 13 => decide (p∈Q)))
    apply congrArg List.ofFn
    funext l
    apply decide_eq_decide.mpr
    change (l∈(Finset.univ.filter fun w : Fin 13 => Disjoint (S w) Q)) ↔ _
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.disjoint_right,incidence]
    simp
  have hlen (Q : Finset (Fin 13)) : (qr Q).length=26 := by
    change (List.ofFn _ ++ List.ofFn _).length=26
    simp only [List.length_append,List.length_ofFn]
  have singleton (p l : Fin 13) : incidenceInput {p} {l} =
      List.ofFn (fun a : Fin 13 => decide (a=p)) ++ List.ofFn (fun a : Fin 13 => decide (a=l)) := by
    change (List.ofFn (fun a : Fin 13 => decide (a∈({p} : Finset (Fin 13)))) ++
      List.ofFn (fun a : Fin 13 => decide (a∈({l} : Finset (Fin 13))))) = _
    simp only [Finset.mem_singleton]
  have pos : RightOnIncidentPairs S C := by
    intro l p hp
    simpa only [singleton] using ok.1 p l ((incidence p l).mp hp)
  have neg : ∀ Q∈T, C.eval (qr Q)=false := fun Q h => same Q ▸ ok.2 Q ((member Q).mp h)
  have wet : ∀ i, inner C i → (bad C i).Nonempty := by
    rintro i ⟨hi,k,hk,below⟩
    obtain ⟨Q,hq,hot⟩ := leaks i k hi hk below
    exact ⟨Q,Finset.mem_filter.mpr ⟨(member _).mpr hq,by simpa [same] using hot⟩⟩
  obtain ⟨u,v,hu,hv,uv⟩ := nested
  obtain ⟨j,hj,hsize,hn⟩ := selectBottom C ⟨u,hu,v,hv,uv⟩
  have profile := classify C j hm back hsize hj.1 hn (Finset.card_pos.mpr (wet j hj))
  obtain ⟨E,he,smaller⟩ := residual C ⟨hm,back,pos,neg⟩ small
    (fun i h => Finset.card_pos.mpr (wet i h)) ⟨j,hj,profile⟩
  refine ⟨E,he.1,he.2.1,⟨?_,?_⟩,smaller⟩
  · intro p l h
    simpa only [singleton] using he.2.2.1 l p ((incidence p l).mpr h)
  · intro Z hz
    rw [←same Z]
    exact he.2.2.2 Z ((member Z).mpr hz)
