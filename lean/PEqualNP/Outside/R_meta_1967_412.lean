import Mathlib
import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
open PEqualNP.TopForm PEqualNP.CleanedNonEdge PEqualNP.GenericRejection
theorem PEqualNP.Outside.R_meta_1967_412
    (hard : let Q := fun (C : Circuit) => C.size ≤ 27 ∧ IsAO2 14 C ∧ (∀ g∈C.gates,g.inputs.Nodup) ∧ ComputesIncidence fanoLines C
    let M := fun (C : Circuit) (j : Nat) (v : Fin 14) =>
    (gateAt C j).op = .and ∧ (14+j=C.output ∨ InCone 14 C j (C.output-14)) ∧
    gateVal 14 C j (pairInput 0 7)=true ∧ ∀ b : Fin 2, wireVal 14 C (opnd C j b) (pairInput v v)=false
    ∀ C, Q C → ∀ a b, InCone 14 C a b → M C a 0 → M C b 7 →
      (∀ k, a<k → k<b → (InCone 14 C k b → ¬M C k 0) ∧ (InCone 14 C a k → ¬M C k 7)) → False)
    (swap : let Q := fun (C : Circuit) => C.size ≤ 27 ∧ IsAO2 14 C ∧ (∀ g∈C.gates,g.inputs.Nodup) ∧ ComputesIncidence fanoLines C
    let M := fun (C : Circuit) (j : Nat) (v : Fin 14) =>
    (gateAt C j).op = .and ∧ (14+j=C.output ∨ InCone 14 C j (C.output-14)) ∧
    gateVal 14 C j (pairInput 0 7)=true ∧ ∀ b : Fin 2, wireVal 14 C (opnd C j b) (pairInput v v)=false
    ∀ C, Q C → ∃ D, Q D ∧ (∀ i j, InCone 14 C i j → InCone 14 D i j) ∧
      ∀ j, (M C j 0 → M D j 7) ∧ (M C j 7 → M D j 0)) :
¬∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.size ≤ (27 : ℕ) ∧ (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (14 : ℕ) + x2 ∧ x6 < (14 : ℕ) + x2) ∧ (∀ (x2 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x2) = Bool.true ↔ ∃ (x3 : Fin (7 : ℕ)) (x4 : Fin (7 : ℕ)), (x3 = x4 ∨ x3 = x4 + (1 : Fin (7 : ℕ)) ∨ x3 = x4 + (3 : Fin (7 : ℕ))) ∧ x2 (Fin.castAdd (7 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (7 : ℕ) x4) = Bool.true) ∧ ∃ (x2 : ℕ) (x3 : ℕ), (PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x2 x3 ∨ PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x3 x2) ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((14 : ℕ) + x2 = x1.output ∨ PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x2 (x1.output - (14 : ℕ))) ∧ PEqualNP.EdgeOwnership.gateVal (14 : ℕ) x1 x2 (PEqualNP.EdgeOwnership.pairInput (0 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ))) = Bool.true ∧ (∀ (x4 : Fin (2 : ℕ)), PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1 (PEqualNP.TopForm.opnd x1 x2 x4) (PEqualNP.EdgeOwnership.pairInput (0 : Fin (14 : ℕ)) (0 : Fin (14 : ℕ))) = Bool.false) ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x3).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((14 : ℕ) + x3 = x1.output ∨ PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x3 (x1.output - (14 : ℕ))) ∧ PEqualNP.EdgeOwnership.gateVal (14 : ℕ) x1 x3 (PEqualNP.EdgeOwnership.pairInput (0 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ))) = Bool.true ∧ ∀ (x4 : Fin (2 : ℕ)), PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1 (PEqualNP.TopForm.opnd x1 x3 x4) (PEqualNP.EdgeOwnership.pairInput (7 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ))) = Bool.false := by
  classical
  let Q := fun (C : Circuit) => C.size ≤ 27 ∧ IsAO2 14 C ∧ (∀ g∈C.gates,g.inputs.Nodup) ∧ ComputesIncidence fanoLines C
  let M := fun (C : Circuit) (j : Nat) (v : Fin 14) =>
    (gateAt C j).op = .and ∧ (14+j=C.output ∨ InCone 14 C j (C.output-14)) ∧
    gateVal 14 C j (pairInput 0 7)=true ∧ ∀ b : Fin 2, wireVal 14 C (opnd C j b) (pairInput v v)=false
  rintro ⟨C,size,legal,funC,a,b,cmp,wa,la,pa,sa,wb,lb,pb,sb⟩
  have qc : Q C := by
    refine ⟨size,⟨?_,?_,?_⟩,?_,?_⟩
    · intro g hg
      obtain ⟨i,hi⟩ := List.mem_iff_getElem?.mp hg
      exact (legal i g hi).1
    · intro i hi w hw
      have atI : gateAt C i = C.gates[i] := List.getD_eq_getElem .. 
      rw [atI] at hw
      obtain ⟨u,v,l,_,hu,hv⟩ := (legal i _ (List.getElem?_eq_getElem hi)).2
      rw [l] at hw
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
      rcases hw with rfl|rfl <;> assumption
    · intro g hg
      obtain ⟨i,h⟩ := List.mem_iff_getElem?.mp hg
      obtain ⟨u,v,l,_⟩ := (legal i g h).2
      simp [l]
    · intro g hg
      obtain ⟨i,h⟩ := List.mem_iff_getElem?.mp hg
      obtain ⟨u,v,l,ne,_⟩ := (legal i g h).2
      simp [l,ne]
    · intro X Y
      let x (i : Fin 14) := if i.val<7 then decide (Fin.ofNat 7 i.val ∈ X) else decide (Fin.ofNat 7 i.val ∈ Y)
      have row : incidenceInput X Y=List.ofFn x := rfl
      rw [row]
      apply Bool.eq_iff_iff.mpr
      rw [funC]
      have pt (p : Fin 7) : x (Fin.castAdd 7 p) = decide (p∈X) := by fin_cases p <;> rfl
      have ln (l : Fin 7) : x (Fin.natAdd 7 l) = decide (l∈Y) := by fin_cases l <;> rfl
      have inc : ∀ p l : Fin 7, p∈fanoLines l ↔ p=l ∨ p=l+1 ∨ p=l+3 := by decide
      change _ ↔ decide (∃ p ∈ X, ∃ l ∈ Y, p∈fanoLines l)=true
      simp only [decide_eq_true_eq,pt,ln,inc]
      constructor
      · rintro ⟨p,l,h,hp,hl⟩; exact ⟨p,hp,l,hl,h⟩
      · rintro ⟨p,hp,l,hl,h⟩; exact ⟨p,l,h,hp,hl⟩
  have ma : M C a 0 := ⟨wa,la,pa,sa⟩
  have mb : M C b 7 := ⟨wb,lb,pb,sb⟩
  have ordered : ∃ D i j, Q D ∧ InCone 14 D i j ∧ M D i 0 ∧ M D j 7 := by
    rcases cmp with h|h
    · exact ⟨C,a,b,qc,h,ma,mb⟩
    · obtain ⟨D,ok,cone,marks⟩ := swap C qc
      exact ⟨D,b,a,ok,cone b a h,(marks b).2 mb,(marks a).1 ma⟩
  obtain ⟨D,i,j,ok,con,mi,mj⟩ := ordered
  let P (d : Nat) := ∃ u v, InCone 14 D u v ∧ M D u 0 ∧ M D v 7 ∧ v-u=d
  have ex : ∃ d,P d := ⟨j-i,i,j,con,mi,mj,rfl⟩
  obtain ⟨u,v,uv,mu,mv,eq⟩ := Nat.find_spec ex
  apply hard D ok u v uv mu mv
  intro k uk kv
  constructor
  · intro kb mk
    have small : v-k < Nat.find ex := by omega
    exact (Nat.find_min ex small) ⟨k,v,kb,mk,mv,rfl⟩
  · intro ak mk
    have small : k-u < Nat.find ex := by omega
    exact (Nat.find_min ex small) ⟨u,k,ak,mu,mk,rfl⟩
