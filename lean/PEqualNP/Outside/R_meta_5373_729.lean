import Mathlib
import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_5373_729
    (choose : ∀ (n m : Nat) (E M : Finset (Fin n × Fin m)) (G : SimpleGraph (Fin (n+m))), (∀u v,G.Adj u v ↔ ∃e∈E,(u=Fin.castAdd m e.1 ∧ v=Fin.natAdd n e.2) ∨ (v=Fin.castAdd m e.1 ∧ u=Fin.natAdd n e.2)) → ¬G.IsAcyclic → (∀e∈M,∀d∈M,e.1=d.1 → e=d) → (∀e∈M,∀d∈M,e.2=d.2 → e=d) → ∃e∈E,e∉M)
    (sparse : ∀ (n m : Nat) (E : Finset (Fin n × Fin m)) (C : Circuit), (∀ S : Finset (Fin (n+m)),(E.filter (fun e => Fin.castAdd m e.1∈S ∧ Fin.natAdd n e.2∈S)).card≤S.card) → (∀p q l k,p≠q → l≠k → ¬((p,l)∈E ∧ (p,k)∈E ∧ (q,l)∈E ∧ (q,k)∈E)) → (IsAO2 (n+m) C ∧ ∀x,circuitFun (n+m) C x=decide (∃p l,(p,l)∈E ∧ x (Fin.castAdd m p)=true ∧ x (Fin.natAdd n l)=true)) → ∃ K : Finset (Fin (n+m)), (∀p l,(p,l)∈E → Fin.castAdd m p∈K ∨ Fin.natAdd n l∈K) ∧ E.card+K.card≤C.size+1)
    (construct : ∀ (n m : Nat) (F : Finset (Fin n × Fin m)) (K : Finset (Fin (n+m))), (∀p l,(p,l)∈F → Fin.castAdd m p∈K ∨ Fin.natAdd n l∈K) → ∃ D : Circuit, (IsAO2 (n+m) D ∧ ∀x,circuitFun (n+m) D x=decide (∃p l,(p,l)∈F ∧ x (Fin.castAdd m p)=true ∧ x (Fin.natAdd n l)=true)) ∧ D.size≤F.card+K.card-1)
    (residual : ∀ (n m : Nat) (E M : Finset (Fin n × Fin m)) (C : Circuit),
  let computes := fun (F : Finset (Fin n × Fin m)) (D : Circuit) => IsAO2 (n+m) D ∧ ∀x,circuitFun (n+m) D x=decide (∃p l,(p,l)∈F ∧ x (Fin.castAdd m p)=true ∧ x (Fin.natAdd n l)=true)
  let covers := fun (F : Finset (Fin n × Fin m)) (K : Finset (Fin (n+m))) => ∀p l,(p,l)∈F → Fin.castAdd m p∈K ∨ Fin.natAdd n l∈K
  (∀p q l k,p≠q → l≠k → ¬((p,l)∈E ∧ (p,k)∈E ∧ (q,l)∈E ∧ (q,k)∈E)) → computes E C → M⊆E → (∀e∈M,∀d∈M,e.1=d.1 → e=d) → (∀e∈M,∀d∈M,e.2=d.2 → e=d) → (∀e∈E,((∀d∈E,d.1=e.1 → d=e) ∨ (∀d∈E,d.2=e.2 → d=e)) → (E.erase e).Nonempty → e∈M) →
  (∃ S : Finset (Fin (n+m)), S.card < (E.filter (fun e => Fin.castAdd m e.1∈S ∧ Fin.natAdd n e.2∈S)).card) →
  (∀ D, computes E D → C.size≤D.size) →
  (∀e∈E,e∉M → ∀ K, covers (E.erase e) K → C.size≤(E.erase e).card+K.card-1) →
  ∃e∈E,e∉M ∧ ∃D : Circuit,D.size<C.size ∧ computes (E.erase e) D)
    : ∀ (x1 x2 : ℕ) (x3 x4 : Finset (Fin x1 × Fin x2)) (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : SimpleGraph (Fin (x1 + x2))), (∀ (x7 x8 : Fin (x1 + x2)), x6.Adj x7 x8 ↔ ∃ x9 ∈ x3, x7 = Fin.castAdd x2 x9.1 ∧ x8 = Fin.natAdd x1 x9.2 ∨ x8 = Fin.castAdd x2 x9.1 ∧ x7 = Fin.natAdd x1 x9.2) → ¬x6.IsAcyclic → (∀ (x9 x10 : Fin x1) (x11 x12 : Fin x2), x9 ≠ x10 → x11 ≠ x12 → ¬((x9, x11) ∈ x3 ∧ (x9, x12) ∈ x3 ∧ (x10, x11) ∈ x3 ∧ (x10, x12) ∈ x3)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x5 → (∀ (x11 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 x11 = Decidable.decide (∃ (x12 : Fin x1) (x13 : Fin x2), (x12, x13) ∈ x3 ∧ x11 (Fin.castAdd x2 x12) = Bool.true ∧ x11 (Fin.natAdd x1 x13) = Bool.true)) → x4 ⊆ x3 → (∀ x13 ∈ x4, ∀ x15 ∈ x4, x13.1 = x15.1 → x13 = x15) → (∀ x14 ∈ x4, ∀ x16 ∈ x4, x14.2 = x16.2 → x14 = x16) → (∀ x15 ∈ x3, ((∀ x17 ∈ x3, x17.1 = x15.1 → x17 = x15) ∨ ∀ x17 ∈ x3, x17.2 = x15.2 → x17 = x15) → (x3.erase x15).Nonempty → x15 ∈ x4) → ∃ x16 ∈ x3, x16 ∉ x4 ∧ ∃ (x17 : PEqualNP.CircuitLowerBounds.Circuit), x17.size < x5.size ∧ PEqualNP.TopForm.IsAO2 (x1 + x2) x17 ∧ ∀ (x18 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x17 x18 = Decidable.decide (∃ (x19 : Fin x1) (x20 : Fin x2), (x19, x20) ∈ x3.erase x16 ∧ x18 (Fin.castAdd x2 x19) = Bool.true ∧ x18 (Fin.natAdd x1 x20) = Bool.true) := by

  classical
  intro n m E M C G adj cyclic square ao corr sub row col privateEdges
  let computes := fun (F : Finset (Fin n × Fin m)) (D : Circuit) => IsAO2 (n+m) D ∧ ∀x,circuitFun (n+m) D x=decide (∃p l,(p,l)∈F ∧ x (Fin.castAdd m p)=true ∧ x (Fin.natAdd n l)=true)
  let covers := fun (F : Finset (Fin n × Fin m)) (K : Finset (Fin (n+m))) => ∀p l,(p,l)∈F → Fin.castAdd m p∈K ∨ Fin.natAdd n l∈K
  let least (s : Nat) := ∃ D : Circuit, computes E D ∧ D.size=s
  have existsSize : ∃s,least s := ⟨C.size,C,⟨ao,corr⟩,rfl⟩
  obtain ⟨D,good,sz⟩ := Nat.find_spec existsSize
  have minimum (B : Circuit) (hb : computes E B) : D.size≤B.size := by
    rw [sz]
    exact Nat.find_min' existsSize (show least B.size from ⟨B,hb,rfl⟩)
  have bound := minimum C ⟨ao,corr⟩
  obtain ⟨e,he,nm⟩ := choose n m E M G adj cyclic row col
  have useCover (d) (hd : d∈E) (dm : d∉M) (K) (cover : covers (E.erase d) K)
      (pay : (E.erase d).card+K.card-1<D.size) :
      ∃ e∈E,e∉M ∧ ∃ X : Circuit,X.size<C.size ∧ computes (E.erase e) X := by
    obtain ⟨X,ok,cost⟩ := construct n m (E.erase d) K cover
    exact ⟨d,hd,dm,X,by omega,ok⟩
  by_cases dense : ∃ S : Finset (Fin (n+m)), S.card < (E.filter (fun e => Fin.castAdd m e.1∈S ∧ Fin.natAdd n e.2∈S)).card
  · by_cases cheap : ∃d∈E,d∉M ∧ ∃K, covers (E.erase d) K ∧ (E.erase d).card+K.card-1<D.size
    · obtain ⟨d,hd,dm,K,cover,pay⟩ := cheap
      exact useCover d hd dm K cover pay
    · obtain ⟨d,hd,dm,X,smaller,ok⟩ := residual n m E M D square good sub row col privateEdges dense minimum (by
        intro d hd dm K cover
        exact Nat.le_of_not_gt (fun h => cheap ⟨d,hd,dm,K,cover,h⟩))
      exact ⟨d,hd,dm,X,by omega,ok⟩
  · obtain ⟨K,cover,cost⟩ := sparse n m E D (fun S => Nat.le_of_not_gt (fun h => dense ⟨S,h⟩)) square good
    have positive : 0<K.card := Finset.card_pos.mpr (by
      obtain left|right := cover e.1 e.2 he
      · exact ⟨_,left⟩
      · exact ⟨_,right⟩)
    have erase := Finset.card_erase_add_one he
    exact useCover e he nm K (fun p l h => cover p l (Finset.mem_of_mem_erase h)) (by omega)
