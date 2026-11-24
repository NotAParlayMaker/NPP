import Mathlib
import PEqualNP.Defs

open PEqualNP.CleanedNonEdge PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadK PEqualNP.TopForm

set_option maxHeartbeats 1500000 in
theorem PEqualNP.Outside.R_meta_2583_903
    (stars : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I], 0<N → (∀ l : Fin N,Fintype.card {p : Fin N // I p l}=q+1) →
  let F := fun (x : Fin (N+N) → Bool) => decide (∃ p l : Fin N, I p l ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true)
  ∃ D : Circuit, IsAO2 (N+N) D ∧ circuitFun (N+N) D=F ∧ D.size+1=N*(q+2) ∧ IsReadK (N+N) D 1)
    (nested : ∀ (n : Nat) (C : Circuit) (S : Finset (Fin n)), IsAO2 n C →
  (∀ i, circuitFun n C (setInput {i})=false) → circuitFun n C (setInput S)=true →
  readsAtMost C n (setList S) 1=false →
  ∃ a h b : Nat,OrReaches n C C.output a ∧ ReadsAt n C a b h ∧ (gateAt C h).op=.and ∧
    gateVal n C a (setInput S)=true ∧ gateVal n C h (setInput S)=true)
    (repair : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I], 2≤q → N=q^2+q+1 → (∀ l : Fin N,Fintype.card {p : Fin N // I p l}=q+1) → (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) →
  let F := fun (x : Fin (N+N) → Bool) => decide (∃ p l : Fin N, I p l ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true)
  let good := fun (D : Circuit) => IsAO2 (N+N) D ∧ circuitFun (N+N) D=F
  let missed := fun (D : Circuit) => Finset.univ.filter (fun e : Fin N × Fin N =>
    I e.1 e.2 ∧ readsAtMost D (N+N)
      (setList {Fin.castAdd N e.1, Fin.natAdd N e.2}) 1 = false)
  ∀ B : Circuit, good B → (∀ D,good D → B.size≤D.size) → B.size+1<N*(q+2) →
    ∀ e∈missed B, let n:=N+N
      let x:=setInput ({Fin.castAdd N e.1,Fin.natAdd N e.2} : Finset (Fin n))
      (∃ a h b : Nat,OrReaches n B B.output a ∧ ReadsAt n B a b h ∧ (gateAt B h).op=.and ∧
        gateVal n B a x=true ∧ gateVal n B h x=true) →
      ∃ D : Circuit,good D ∧ D.size≤B.size ∧ e∉missed D ∧ missed D⊆missed B) :
  ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q → N = q ^ 2 + q + 1 → (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) → (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) → PEqualNP.TopForm.IsAO2 (N + N) C → (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 (N + N) D ∧ (∀ y : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) D y = decide (∃ p l : Fin N, I p l ∧ y (Fin.castAdd N p) = true ∧ y (Fin.natAdd N l) = true)) ∧ D.size ≤ C.size ∧ PEqualNP.ReadK.IsReadK (N + N) D 1 := by
  classical
  intro q N I dec C hq hN hd hu hm hf
  let F := fun (x : Fin (N+N) → Bool) => decide (∃ p l : Fin N, I p l ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true)
  let good := fun (D : Circuit) => IsAO2 (N+N) D ∧ circuitFun (N+N) D=F
  let missed := fun (D : Circuit) => Finset.univ.filter (fun e : Fin N × Fin N =>
    I e.1 e.2 ∧ readsAtMost D (N+N)
      (setList {Fin.castAdd N e.1, Fin.natAdd N e.2}) 1 = false)
  have subdegree (l : Fin N) : Fintype.card {p : Fin N // I p l}=q+1 :=
    (Fintype.card_subtype (fun p => I p l)).trans (hd l)
  have start : good C := ⟨hm,funext hf⟩
  have hasSize : ∃ k : Nat,∃ D : Circuit,good D ∧ D.size=k := ⟨C.size,C,start,rfl⟩
  let k := Nat.find hasSize
  obtain ⟨A,hA,sa⟩ : ∃ D : Circuit,good D ∧ D.size=k := Nat.find_spec hasSize
  have least (D : Circuit) (hD : good D) : k≤D.size := Nat.find_min' hasSize ⟨D,hD,rfl⟩
  have hasBad : ∃ b : Nat,∃ D : Circuit,good D ∧ D.size=k ∧ (missed D).card=b :=
    ⟨(missed A).card,A,hA,sa,rfl⟩
  obtain ⟨B,hB,sB,bB⟩ := Nat.find_spec hasBad
  have cost : B.size≤C.size := sB ▸ least C start
  by_cases high : N*(q+2)≤B.size+1
  · obtain ⟨D,hD,fD,sd,rD⟩ := stars q N I (by omega) subdegree
    exact ⟨D,hD,fun x=>congrFun fD x,by omega,rD⟩
  have empty : ¬(missed B).Nonempty := by
    rintro ⟨e,he⟩
    obtain ⟨_,heI,notRead⟩ := Finset.mem_filter.mp he
    let U : Finset (Fin (N+N)) := {Fin.castAdd N e.1,Fin.natAdd N e.2}
    have single (i : Fin (N+N)) : circuitFun (N+N) B (setInput {i})=false := by
      rw [hB.2]
      apply decide_eq_false
      rintro ⟨p,l,_,hp,hl⟩
      have ep : Fin.castAdd N p=i := Finset.mem_singleton.mp (of_decide_eq_true hp)
      have el : Fin.natAdd N l=i := Finset.mem_singleton.mp (of_decide_eq_true hl)
      have hn := congrArg Fin.val (ep.trans el.symm)
      change p.val=N+l.val at hn
      have := p.isLt
      omega
    have hit : circuitFun (N+N) B (setInput U)=true := by
      rw [hB.2]
      apply decide_eq_true
      exact ⟨e.1,e.2,heI,by change decide (_∈U)=true; simp [U],by change decide (_∈U)=true; simp [U]⟩
    have loc := nested _ B U hB.1 single hit notRead
    obtain ⟨D,hD,sD,fixed,sub⟩ := repair q N I hq hN subdegree hu B hB (fun D hD => sB ▸ least D hD) (by omega) e he loc
    change e∉missed D at fixed
    change missed D⊆missed B at sub
    have drop : (missed D).card < (missed B).card := Finset.card_lt_card
      (Finset.ssubset_iff_subset_ne.mpr ⟨sub,fun eq=>fixed (eq ▸ he)⟩)
    have eq : D.size=k := by have := least D hD;omega
    have low := Nat.find_min' hasBad (m := (missed D).card) ⟨D,hD,eq,rfl⟩
    exact (Nat.not_lt_of_ge (bB ▸ low)) drop
  refine ⟨B,hB.1,fun x=>congrFun hB.2 x,cost,?_⟩
  intro S prime
  have hit := prime.1
  rw [hB.2] at hit
  obtain ⟨p,l,hpl,px,lx⟩ := of_decide_eq_true hit
  let U : Finset (Fin (N+N)) := {Fin.castAdd N p, Fin.natAdd N l}
  have sub : U⊆S := by
    apply Finset.insert_subset
    · exact of_decide_eq_true px
    · apply Finset.singleton_subset_iff.mpr
      exact of_decide_eq_true lx
  have onU : circuitFun (N+N) B (setInput U)=true := by
    rw [hB.2]
    apply decide_eq_true
    exact ⟨p,l,hpl,by change decide (_∈U)=true; simp [U],by change decide (_∈U)=true; simp [U]⟩
  have equal : U=S := by
    by_contra neq
    have fail := prime.2 U (Finset.mem_ssubsets.mpr ((Finset.ssubset_iff_subset_ne).2 ⟨sub,neq⟩))
    exact Bool.noConfusion (onU.symm.trans fail)
  rw [←equal]
  apply Bool.eq_true_of_not_eq_false
  intro fail
  apply empty
  exact ⟨(p,l),Finset.mem_filter.mpr ⟨Finset.mem_univ _,hpl,fail⟩⟩
