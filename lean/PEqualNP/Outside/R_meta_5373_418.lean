import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm Finset
open scoped Classical

-- A counterexample must beat every vertex-cover star construction. In that regime
-- a single set of mandatory and profitable edges replaces the quantifier over matchings.
set_option maxRecDepth 12000 in
set_option maxHeartbeats 1600000 in
theorem PEqualNP.Outside.R_meta_5373_418
    (stars : ∀ (p l : ℕ) (F : Finset (Fin p × Fin l)) (P : Finset (Fin p)) (L : Finset (Fin l)),
      F.Nonempty → (∀ e ∈ F, e.1 ∈ P ∨ e.2 ∈ L) →
      ∃ D : Circuit, IsAO2 (p+l) D ∧ D.size+1 ≤ F.card+P.card+L.card ∧
        ∀ x : Fin (p+l) → Bool, circuitFun (p+l) D x=decide (∃ a b, (a,b)∈F ∧
          x (Fin.castAdd l a)=true ∧ x (Fin.natAdd p b)=true))
    (conflict : ∀ (p l : ℕ) (E : Finset (Fin p × Fin l)) (C : Circuit) (G : SimpleGraph (Fin (p+l))),
      (∀ u v, G.Adj u v ↔ ∃ e∈E, u=Fin.castAdd l e.1 ∧ v=Fin.natAdd p e.2 ∨
        v=Fin.castAdd l e.1 ∧ u=Fin.natAdd p e.2) → ¬G.IsAcyclic →
      (∀ a b : Fin p, ∀ u v : Fin l, a≠b → u≠v → ¬((a,u)∈E ∧ (a,v)∈E ∧ (b,u)∈E ∧ (b,v)∈E)) →
      let fn (F : Finset (Fin p × Fin l)) (x : Fin (p+l) → Bool) :=
        decide (∃ a b, (a,b)∈F ∧ x (Fin.castAdd l a)=true ∧ x (Fin.natAdd p b)=true)
      IsAO2 (p+l) C → (∀ x, circuitFun (p+l) C x=fn E x) →
      (∀ (P : Finset (Fin p)) (L : Finset (Fin l)), (∀ e∈E, e.1∈P ∨ e.2∈L) →
        C.size+1 < E.card+P.card+L.card) →
      let priority (e : Fin p × Fin l) :=
        (((∀ f∈E, f.1=e.1 → f=e) ∨ ∀ f∈E, f.2=e.2 → f=e) ∧ (E.erase e).Nonempty) ∨
        ∃ D : Circuit, D.size<C.size ∧ IsAO2 (p+l) D ∧ ∀ x, circuitFun (p+l) D x=fn (E.erase e) x
      ∃ e∈E, ∃ f∈E, e≠f ∧ (e.1=f.1 ∨ e.2=f.2) ∧ priority e ∧ priority f) :
    ∀ (x1 x2 : ℕ) (x3 x4 : Finset (Fin x1 × Fin x2)) (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : SimpleGraph (Fin (x1 + x2))), (∀ (x7 x8 : Fin (x1 + x2)), x6.Adj x7 x8 ↔ ∃ x9 ∈ x3, x7 = Fin.castAdd x2 x9.1 ∧ x8 = Fin.natAdd x1 x9.2 ∨ x8 = Fin.castAdd x2 x9.1 ∧ x7 = Fin.natAdd x1 x9.2) → ¬x6.IsAcyclic → (∀ (x9 x10 : Fin x1) (x11 x12 : Fin x2), x9 ≠ x10 → x11 ≠ x12 → ¬((x9, x11) ∈ x3 ∧ (x9, x12) ∈ x3 ∧ (x10, x11) ∈ x3 ∧ (x10, x12) ∈ x3)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x5 → (∀ (x11 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 x11 = Decidable.decide (∃ (x12 : Fin x1) (x13 : Fin x2), (x12, x13) ∈ x3 ∧ x11 (Fin.castAdd x2 x12) = Bool.true ∧ x11 (Fin.natAdd x1 x13) = Bool.true)) → x4 ⊆ x3 → (∀ x13 ∈ x4, ∀ x15 ∈ x4, x13.1 = x15.1 → x13 = x15) → (∀ x14 ∈ x4, ∀ x16 ∈ x4, x14.2 = x16.2 → x14 = x16) → (∀ x15 ∈ x3, ((∀ x17 ∈ x3, x17.1 = x15.1 → x17 = x15) ∨ ∀ x17 ∈ x3, x17.2 = x15.2 → x17 = x15) → (x3.erase x15).Nonempty → x15 ∈ x4) → ∃ x16 ∈ x3, x16 ∉ x4 ∧ ∃ (x17 : PEqualNP.CircuitLowerBounds.Circuit), x17.size < x5.size ∧ PEqualNP.TopForm.IsAO2 (x1 + x2) x17 ∧ ∀ (x18 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x17 x18 = Decidable.decide (∃ (x19 : Fin x1) (x20 : Fin x2), (x19, x20) ∈ x3.erase x16 ∧ x18 (Fin.castAdd x2 x19) = Bool.true ∧ x18 (Fin.natAdd x1 x20) = Bool.true) := by
  classical
  have cycle_fork {p l : ℕ} (E : Finset (Fin p × Fin l)) (G : SimpleGraph (Fin (p+l)))
      (adj : ∀ u v, G.Adj u v ↔ ∃ e ∈ E, u = Fin.castAdd l e.1 ∧ v = Fin.natAdd p e.2 ∨
        v = Fin.castAdd l e.1 ∧ u = Fin.natAdd p e.2) (cycle : ¬G.IsAcyclic) :
      ∃ e ∈ E, ∃ f ∈ E, e ≠ f ∧ (e.1=f.1 ∨ e.2=f.2) := by
    obtain ⟨u,c,hc⟩ := SimpleGraph.not_isAcyclic_iff_exists_isCycle.mp cycle
    have adj1 := (adj u c.snd).mp (c.adj_snd hc.not_nil)
    have adj2 := (adj u c.penultimate).mp (c.adj_penultimate hc.not_nil).symm
    obtain ⟨e,he,left⟩ := adj1
    obtain ⟨f,hf,right⟩ := adj2
    refine ⟨e,he,f,hf,?_,?_⟩
    · intro same
      subst f
      rcases left with ⟨ua,va⟩|⟨va,ua⟩ <;> rcases right with ⟨ub,vb⟩|⟨vb,ub⟩
      · exact hc.snd_ne_penultimate (va.trans vb.symm)
      · have h := congrArg Fin.val (ua.symm.trans ub); change e.1.val=p+e.2.val at h; omega
      · have h := congrArg Fin.val (ua.symm.trans ub); change p+e.2.val=e.1.val at h; omega
      · exact hc.snd_ne_penultimate (va.trans vb.symm)
    · rcases left with ⟨ua,_⟩|⟨_,ua⟩ <;> rcases right with ⟨ub,_⟩|⟨_,ub⟩
      · exact Or.inl (Fin.castAdd_injective p l (ua.symm.trans ub))
      · have h := congrArg Fin.val (ua.symm.trans ub); change e.1.val=p+f.2.val at h; omega
      · have h := congrArg Fin.val (ua.symm.trans ub); change p+e.2.val=f.1.val at h; omega
      · exact Or.inr (Fin.ext (Nat.add_left_cancel (congrArg Fin.val (ua.symm.trans ub))))
  intro p l E M C G adj cycle square shape computes sub ml mr force
  let fn (F : Finset (Fin p × Fin l)) (x : Fin (p+l) → Bool) :=
    decide (∃ a b, (a,b)∈F ∧ x (Fin.castAdd l a)=true ∧ x (Fin.natAdd p b)=true)
  let cheap (e : Fin p × Fin l) := ∃ D : Circuit, D.size<C.size ∧ IsAO2 (p+l) D ∧ ∀ x, circuitFun (p+l) D x=fn (E.erase e) x
  let must (e : Fin p × Fin l) := ((∀ f∈E, f.1=e.1 → f=e) ∨ ∀ f∈E, f.2=e.2 → f=e) ∧ (E.erase e).Nonempty
  have locked (e) (he : e ∈ E) (m : must e) : e ∈ M := force e he m.1 m.2
  have separate (e) (he : e ∈ M) (f) (hf : f ∈ M) (share : e.1=f.1 ∨ e.2=f.2) :=
    share.elim (ml e he f hf) (mr e he f hf)
  change ∃ e∈E, e∉M ∧ cheap e
  by_cases tight : ∀ (P : Finset (Fin p)) (L : Finset (Fin l)), (∀ e∈E, e.1∈P ∨ e.2∈L) →
      C.size+1 < E.card+P.card+L.card
  · obtain ⟨e,he,f,hf,ne,share,ep,fp⟩ := conflict p l E C G adj cycle square shape computes tight
    change must e ∨ cheap e at ep
    change must f ∨ cheap f at fp
    by_cases h : e ∈ M
    · have out : f ∉ M := fun hf' => ne (separate e h f hf' share)
      exact ⟨f,hf,out,fp.resolve_left (fun m => out (locked f hf m))⟩
    · exact ⟨e,he,h,ep.resolve_left (fun m => h (locked e he m))⟩
  · push_neg at tight
    obtain ⟨P,L,covers,budget⟩ := tight
    obtain ⟨e,he,f,hf,ne,share⟩ := cycle_fork E G adj cycle
    have drop (a) (ha : a∈E) (b) (hb : b∈E) (ab : b ≠ a) : cheap a := by
      have rem : (E.erase a).Nonempty := ⟨b,mem_erase.mpr ⟨ab,hb⟩⟩
      obtain ⟨D,good,cost,ok⟩ := stars p l (E.erase a) P L rem (fun g hg => covers g (mem_of_mem_erase hg))
      have cut := Finset.card_erase_add_one ha
      exact ⟨D,by omega,good,ok⟩
    by_cases h : e ∈ M
    · exact ⟨f,hf,fun hf' => ne (separate e h f hf' share),drop f hf e he ne⟩
    · exact ⟨e,he,h,drop e he f hf ne.symm⟩
