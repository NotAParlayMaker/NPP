import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.ReadTwo

theorem PEqualNP.Outside.R_meta_3241_661
    (assemble : ∀ (P L : ℕ) (E : Finset (Fin P × Fin L)) (c : ℕ),
      (∀ M : Finset (Fin P × Fin L), M⊆E →
        (∀ e∈M,∀ f∈M,e.1=f.1 → e=f) → (∀ e∈M,∀ f∈M,e.2=f.2 → e=f) →
        E.card+M.card≤c+1) →
      ∃ S : List (ℕ × List ℕ),
        (∀ s∈S,s.2 ≠ [] ∧ ((s.1 < P ∧ ∀ a∈s.2,P ≤ a ∧ a < P+L) ∨
          P ≤ s.1 ∧ s.1 < P+L ∧ ∀ a∈s.2,a < P)) ∧
        (∀ p : Fin P,∀ l : Fin L,(p,l)∈E ↔ ∃ s∈S,
          s.1=p.val ∧ P+l.val∈s.2 ∨ s.1=P+l.val ∧ p.val∈s.2) ∧
        (S.map (fun s=>s.2.length)).sum+S.length-1≤c)
    (normalize : ∀ (n : ℕ) (H : SimpleGraph (Fin n)) [DecidableRel H.Adj],
      ∃ D : Circuit, IsLeastAO H D ∧ TopForm H D)
    (one : ∀ (P L : ℕ) (E M : Finset (Fin P × Fin L)) (H : SimpleGraph (Fin (P+L)))
      [DecidableRel H.Adj] (C : Circuit),
      let R (w : ℕ) := ∃ p < P+L, orp C (P+L) p w
      let X (j : ℕ) := isOr C j ∧ (R (in0 C j) ↔ ¬ R (in1 C j))
      let live := ∀ j, isAnd C j → orp C (P+L) (P+L+j) C.output →
        R (in0 C j) ∧ R (in1 C j)
      Lin (fun p l => (p,l)∈E) → IsLeastAO H C → TopForm H C →
      (∀ u v, H.Adj u v ↔ ∃ e∈E, u=Fin.castAdd L e.1 ∧ v=Fin.natAdd P e.2 ∨
        v=Fin.castAdd L e.1 ∧ u=Fin.natAdd P e.2) →
      M⊆E → (∀ a∈M,∀ b∈M,a.1=b.1 → a=b) →
      (∀ a∈M,∀ b∈M,a.2=b.2 → a=b) → live → (∀ i j, X i → X j → i=j) → E.card+M.card≤C.size+1)
    (residual : ∀ (P L : ℕ) (E M : Finset (Fin P × Fin L)) (H : SimpleGraph (Fin (P+L)))
      [DecidableRel H.Adj] (C : Circuit),
      let R (w : ℕ) := ∃ p < P+L, orp C (P+L) p w
      let X (j : ℕ) := isOr C j ∧ (R (in0 C j) ↔ ¬ R (in1 C j))
      let live := ∀ j, isAnd C j → orp C (P+L) (P+L+j) C.output →
        R (in0 C j) ∧ R (in1 C j)
      Lin (fun p l => (p,l)∈E) → IsLeastAO H C → TopForm H C →
      (∀ u v, H.Adj u v ↔ ∃ e∈E, u=Fin.castAdd L e.1 ∧ v=Fin.natAdd P e.2 ∨
        v=Fin.castAdd L e.1 ∧ u=Fin.natAdd P e.2) →
      M⊆E → (∀ a∈M,∀ b∈M,a.1=b.1 → a=b) →
      (∀ a∈M,∀ b∈M,a.2=b.2 → a=b) → ¬(live ∧ (∀ i j, X i → X j → i=j)) → E.card+M.card≤C.size+1) :
  ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit),   let x6 : ℕ := x1 + x2;   (∀ (x7 x8 : Fin x1) (x9 x10 : Fin x2), x7 ≠ x8 → x9 ≠ x10 → ¬(x3 x7 x9 ∧ x3 x7 x10 ∧ x3 x8 x9 ∧ x3 x8 x10)) → PEqualNP.TopForm.IsAO2 x6 x5 → (∀ (x9 : Fin x6 → Bool), PEqualNP.MetaComplexity.circuitFun x6 x5 x9 = Decidable.decide (∃ (x10 : Fin x1) (x11 : Fin x2), x3 x10 x11 ∧ x9 (Fin.castAdd x2 x10) = Bool.true ∧ x9 (Fin.natAdd x1 x11) = Bool.true)) → ∃ (x10 : List (ℕ × List ℕ)), (∀ x11 ∈ x10, x11.2 ≠ [] ∧ ((x11.1 < x1 ∧ ∀ x13 ∈ x11.2, x1 ≤ x13 ∧ x13 < x6) ∨ x1 ≤ x11.1 ∧ x11.1 < x6 ∧ ∀ x13 ∈ x11.2, x13 < x1)) ∧ (∀ (x11 : Fin x1) (x12 : Fin x2), x3 x11 x12 ↔ ∃ x13 ∈ x10, x13.1 = ↑x11 ∧ x1 + ↑x12 ∈ x13.2 ∨ x13.1 = x1 + ↑x12 ∧ ↑x11 ∈ x13.2) ∧ (List.map (fun (x11 : ℕ × List ℕ) => x11.2.length) x10).sum + x10.length - (1 : ℕ) ≤ x5.size := by
  have lower : ∀ (x1 x2 : ℕ) (x3 x4 : Finset (Fin x1 × Fin x2)) (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x6 x7 : Fin x1) (x8 x9 : Fin x2), x6 ≠ x7 → x8 ≠ x9 → ¬((x6, x8) ∈ x3 ∧ (x6, x9) ∈ x3 ∧ (x7, x8) ∈ x3 ∧ (x7, x9) ∈ x3)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x5 → (∀ (x8 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 x8 = Decidable.decide (∃ (x9 : Fin x1) (x10 : Fin x2), (x9, x10) ∈ x3 ∧ x8 (Fin.castAdd x2 x9) = Bool.true ∧ x8 (Fin.natAdd x1 x10) = Bool.true)) → x4 ⊆ x3 → (∀ x10 ∈ x4, ∀ x12 ∈ x4, x10.1 = x12.1 → x10 = x12) → (∀ x11 ∈ x4, ∀ x13 ∈ x4, x11.2 = x13.2 → x11 = x13) → x3.card + x4.card ≤ x5.size + (1 : ℕ) := by
    classical
    intro P L E M C linear model correct sub onPoints onLines
    let n := P+L
    let rel (u v : Fin n) := ∃ e∈E, u=Fin.castAdd L e.1 ∧ v=Fin.natAdd P e.2
    let H := SimpleGraph.fromRel rel
    have sep (p : Fin P) (l : Fin L) : Fin.castAdd L p ≠ Fin.natAdd P l := by
      intro same
      have h := congrArg Fin.val same
      simp at h
      have := p.isLt
      omega
    have adj (u v : Fin n) :
        H.Adj u v ↔ ∃ e∈E,u=Fin.castAdd L e.1 ∧ v=Fin.natAdd P e.2 ∨
          v=Fin.castAdd L e.1 ∧ u=Fin.natAdd P e.2 := by
      rw [SimpleGraph.fromRel_adj]
      constructor
      · rintro ⟨_,⟨e,mem,fromWire,toWire⟩|⟨e,mem,fromWire,toWire⟩⟩
        · exact ⟨e,mem,.inl ⟨fromWire,toWire⟩⟩
        · exact ⟨e,mem,.inr ⟨fromWire,toWire⟩⟩
      · rintro ⟨e,mem,⟨rfl,rfl⟩|⟨rfl,rfl⟩⟩
        · exact ⟨sep _ _,.inl ⟨e,mem,rfl,rfl⟩⟩
        · exact ⟨(sep _ _).symm,.inr ⟨e,mem,rfl,rfl⟩⟩
    have graphEval : circuitFun n C=graphFun H ∅ := by
      funext x
      rw [correct x]
      change _ = (decide (∃ a ∈ (∅ : Finset (Fin n)), x a=true) ||
        decide (∃ u v, H.Adj u v ∧ x u=true ∧ x v=true))
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq, Finset.notMem_empty, false_and, exists_false,
        decide_false, Bool.false_or]
      constructor
      · rintro ⟨p,l,mem,hp,hl⟩
        exact ⟨_,_,(adj _ _).mpr ⟨(p,l),mem,.inl ⟨rfl,rfl⟩⟩,hp,hl⟩
      · rintro ⟨u,v,h,hu,hv⟩
        obtain ⟨e,mem,⟨rfl,rfl⟩|⟨rfl,rfl⟩⟩ := (adj _ _).mp h
        · exact ⟨e.1,e.2,mem,hu,hv⟩
        · exact ⟨e.1,e.2,mem,hv,hu⟩
    have lin : Lin (fun p l => (p,l)∈E) := by
      intro p p' l l' pn ln h
      exact linear p p' l l' pn ln ⟨h.1,h.2.2.1,h.2.1,h.2.2.2⟩
    obtain ⟨D,least,top⟩ := normalize n H
    have size := least.2.2 C model graphEval
    let R (w : ℕ) := ∃ p < n,orp D n p w
    let X (j : ℕ) := isOr D j ∧ (R (in0 D j) ↔ ¬ R (in1 D j))
    let live := ∀ j,isAnd D j → orp D n (n+j) D.output → R (in0 D j) ∧ R (in1 D j)
    have bounded : E.card+M.card≤D.size+1 := by
      by_cases good : live ∧ (∀ i j,X i → X j → i=j)
      · exact one P L E M H D lin least top adj sub onPoints onLines good.1 good.2
      · exact residual P L E M H D lin least top adj sub onPoints onLines good
    omega
  intro P L I inst C n linear model correct
  let E : Finset (Fin P × Fin L) := Finset.univ.filter (fun e=>I e.1 e.2)
  have inE (p : Fin P) (l : Fin L) : (p,l)∈E ↔ I p l := by simp [E]
  obtain ⟨S,typed,served,cost⟩ := assemble P L E C.size (by
    intro M sub onPoints onLines
    apply lower P L E M C _ model _ sub onPoints onLines
    · intro p q a b pn ln h
      exact linear p q a b pn ln ⟨(inE _ _).mp h.1,(inE _ _).mp h.2.1,
        (inE _ _).mp h.2.2.1,(inE _ _).mp h.2.2.2⟩
    · intro x
      rw [correct x]
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq,inE])
  exact ⟨S,typed,fun p l=>(inE p l).symm.trans (served p l),cost⟩
