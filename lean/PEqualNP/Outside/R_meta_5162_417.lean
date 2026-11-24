import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.HeptadCover PEqualNP.GenericRejection

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.R_meta_5162_417
    (factor : ∀ C : Circuit, Monotone2 C → ReadsBack 26 C → andPairs 26 C=1 → RightOnIncidentPairs singerLines3 C →
    (∀ Q, IsQuadrangle singerLines3 Q → C.eval (incidenceInput Q (missLines singerLines3 Q))=false) →
    (∀ D : Circuit, Monotone2 D → ReadsBack 26 D → RightOnIncidentPairs singerLines3 D →
      (∀ Q, IsQuadrangle singerLines3 Q → D.eval (incidenceInput Q (missLines singerLines3 Q))=false) → C.size≤D.size) →
    ∃ (b : Bool) (m : Fin 13 → Finset (Fin 3)), ∀ X Y, C.eval (incidenceInput X Y)=true ↔
      incidenceFun singerLines3 X Y=true ∨ ∀ t : Fin 3, ∃ u∈(if b then X else Y), t∈m u)
    (compress : ∀ (b : Bool) (m : Fin 13 → Finset (Fin 3)),
    (∀ Q, IsQuadrangle singerLines3 Q → ∃ t : Fin 3, ∀ u∈(if b then Q else missLines singerLines3 Q), t∉m u) →
    ∃ F : Finset (Finset (Fin 13)), F.card≤2 ∧ (∀ T∈F,T.card=3) ∧
    (∃ v : Fin 13, ∀ T∈F, ∀ u∈T, if b then u∈singerLines3 v else v∈singerLines3 u) ∧
    ∀ X : Finset (Fin 13), (∀ t : Fin 3, ∃ u∈X, t∈m u) ↔ ∃ T∈F, T⊆X)
    (physical : ∀ (b : Bool) (F : Finset (Finset (Fin 13))),
    F.card≤2 → (∀ T∈F,T.card=3) →
    (∃ v : Fin 13, ∀ T∈F, ∀ u∈T, if b then u∈singerLines3 v else v∈singerLines3 u) →
    ∀ C : Circuit, Monotone2 C → ReadsBack 26 C → andPairs 26 C=1 →
    (∀ X Y, C.eval (incidenceInput X Y)=true ↔ incidenceFun singerLines3 X Y=true ∨
      ∃ T∈F, T⊆(if b then X else Y)) →
    (∀ D : Circuit, Monotone2 D → ReadsBack 26 D →
      (∀ X Y : Finset (Fin 13), D.eval (incidenceInput X Y)=C.eval (incidenceInput X Y)) → C.size≤D.size) →
    64≤C.size) :
have x1 : Finset (Fin (13 : ℕ)) → List Bool := fun (x1 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x2 : Fin (13 : ℕ)) => Decidable.decide (x2 ∈ x1)) ++ List.ofFn fun (x2 : Fin (13 : ℕ)) => Decidable.decide (x2 ∈ PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x1); have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.MetaComplexity.Monotone2 x2 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x2 ∧ (∀ (x3 x4 : Fin (13 : ℕ)), x3 ∈ PEqualNP.HeptadCover.singerLines3 x4 → x2.eval ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x4)) = Bool.true) ∧ ∀ (x3 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 x3 → x2.eval (x1 x3) = Bool.false; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), x2 x3 → (∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit), x2 x5 → x3.size ≤ x5.size) → PEqualNP.TopForm.andPairs (26 : ℕ) x3 = (1 : ℕ) → (64 : ℕ) ≤ x3.size := by
  classical
  dsimp only
  intro C good least one
  obtain ⟨mono,back,yes,no⟩ := good
  have pos : RightOnIncidentPairs singerLines3 C := by
    intro l p h
    change C.eval (List.ofFn (fun u : Fin 13 => decide (u∈({p} : Finset _))) ++ List.ofFn (fun v : Fin 13 => decide (v∈({l} : Finset _))))=true
    simpa only [Finset.mem_singleton] using yes p l h
  have optimal (D : Circuit) (dm : Monotone2 D) (db : ReadsBack 26 D) (dp : RightOnIncidentPairs singerLines3 D)
      (dn : ∀ Q, IsQuadrangle singerLines3 Q → D.eval (incidenceInput Q (missLines singerLines3 Q))=false) :
      C.size≤D.size := by
    apply least D
    refine ⟨dm,db,?_,dn⟩
    intro p l h
    have hh := dp l p h
    change D.eval (List.ofFn (fun u : Fin 13 => decide (u∈({p} : Finset _))) ++ List.ofFn (fun v : Fin 13 => decide (v∈({l} : Finset _))))=true at hh
    simpa only [Finset.mem_singleton] using hh
  obtain ⟨b,m,nf⟩ := factor C mono back one pos no optimal
  have safe (Q : Finset (Fin 13)) (hQ : IsQuadrangle singerLines3 Q) :
      ∃ t : Fin 3, ∀ u∈(if b then Q else missLines singerLines3 Q), t∉m u := by
    by_contra! all
    have pr := (nf Q (missLines singerLines3 Q)).2 (Or.inr all)
    exact Bool.false_ne_true ((no Q hQ).symm.trans pr)
  obtain ⟨F,small,triples,common,descr⟩ := compress b m safe
  apply physical b F small triples common C mono back one
  · intro X Y
    rw [nf,descr]
  · intro D dm db eqv
    apply least D
    refine ⟨dm,db,?_,?_⟩
    · intro p l h
      have hh := (eqv {p} {l}).trans (pos l p h)
      change D.eval (List.ofFn (fun u : Fin 13 => decide (u∈({p} : Finset _))) ++ List.ofFn (fun v : Fin 13 => decide (v∈({l} : Finset _))))=true at hh
      simpa only [Finset.mem_singleton] using hh
    · intro Q h
      exact (eqv Q (missLines singerLines3 Q)).trans (no Q h)
