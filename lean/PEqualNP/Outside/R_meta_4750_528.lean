import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.EdgeOwnership

-- A binary AND frontier of a circuit of size 27 has at most fourteen non-raw leaves.
theorem PEqualNP.Outside.R_meta_4750_528
    (frontier :
      let F (x : Fin 14 → Bool) :=
        decide (∃ p l : Fin 7, (p=l ∨ p=l+1 ∨ p=l+3) ∧
          x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true)
      let val := PEqualNP.CleanedNonEdge.wireVal 14
      let gAt := gateAt
      let route (C : Circuit) (a b : ℕ) :=
        14 ≤ a ∧ (gAt C (a-14)).op = .and ∧ b ∈ (gAt C (a-14)).inputs
      let heavy (C : Circuit) := ∃ j<C.size, (gAt C j).op = .or ∧
        Relation.ReflTransGen (route C) C.output (14+j) ∧
        3 ≤ {x : Fin 14 → Bool | F x = false ∧ (∀ i, x i = false → F (Function.update x i true) = true) ∧
          val C (14+j) x = false}.ncard
      ∀ C : Circuit, C.size ≤ 27 → IsAO2 14 C → (∀ x, C.eval (List.ofFn x) = F x) → heavy C)
    (remaining :
      let F (x : Fin 14 → Bool) :=
        decide (∃ p l : Fin 7, (p=l ∨ p=l+1 ∨ p=l+3) ∧
          x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true)
      let val := PEqualNP.CleanedNonEdge.wireVal 14
      let gAt := gateAt
      let route (C : Circuit) (a b : ℕ) :=
        14 ≤ a ∧ (gAt C (a-14)).op = .and ∧ b ∈ (gAt C (a-14)).inputs
      let heavy (C : Circuit) := ∃ j<C.size, (gAt C j).op = .or ∧
        Relation.ReflTransGen (route C) C.output (14+j) ∧
        3 ≤ {x : Fin 14 → Bool | F x = false ∧ (∀ i, x i = false → F (Function.update x i true) = true) ∧
          val C (14+j) x = false}.ncard
      ¬∃ C : Circuit, C.size ≤ 27 ∧ IsAO2 14 C ∧
        (∀ g ∈ C.gates, g.inputs.getD 0 0 ≠ g.inputs.getD 1 0) ∧
        (∀ x, C.eval (List.ofFn x) = F x) ∧
        (∃ j, (gAt C j).op = .and ∧ 14+j=C.output ∧
          ∀ b : Fin 2,
          val C (opnd C j b) (pairInput 0 0) = false ∧ val C (opnd C j b) (pairInput 7 7) = false) ∧ heavy C) :
¬∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.size ≤ (27 : ℕ) ∧ (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (14 : ℕ) + x2 ∧ x6 < (14 : ℕ) + x2) ∧ (∀ (x2 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x2) = Bool.true ↔ ∃ (x3 : Fin (7 : ℕ)) (x4 : Fin (7 : ℕ)), (x3 = x4 ∨ x3 = x4 + (1 : Fin (7 : ℕ)) ∨ x3 = x4 + (3 : Fin (7 : ℕ))) ∧ x2 (Fin.castAdd (7 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (7 : ℕ) x4) = Bool.true) ∧ ∃ (x2 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (14 : ℕ) + x2 = x1.output ∧ PEqualNP.EdgeOwnership.gateVal (14 : ℕ) x1 x2 (PEqualNP.EdgeOwnership.pairInput (0 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ))) = Bool.true ∧ ∀ (x3 : Fin (2 : ℕ)), PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1 (PEqualNP.TopForm.opnd x1 x2 x3) (PEqualNP.EdgeOwnership.pairInput (0 : Fin (14 : ℕ)) (0 : Fin (14 : ℕ))) = Bool.false ∧ PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1 (PEqualNP.TopForm.opnd x1 x2 x3) (PEqualNP.EdgeOwnership.pairInput (7 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ))) = Bool.false := by
  intro candidate
  obtain ⟨C,size,normal,exactSpec,final⟩ := candidate
  let F (x : Fin 14 → Bool) :=
    decide (∃ p l : Fin 7, (p=l ∨ p=l+1 ∨ p=l+3) ∧
      x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true)
  let val := PEqualNP.CleanedNonEdge.wireVal 14
  let gAt := gateAt
  let route (C : Circuit) (a b : ℕ) :=
    14 ≤ a ∧ (gAt C (a-14)).op = .and ∧ b ∈ (gAt C (a-14)).inputs
  let heavy (C : Circuit) := ∃ j<C.size, (gAt C j).op = .or ∧
    Relation.ReflTransGen (route C) C.output (14+j) ∧
    3 ≤ {x : Fin 14 → Bool | F x = false ∧ (∀ i, x i = false → F (Function.update x i true) = true) ∧
      val C (14+j) x = false}.ncard
  have model : IsAO2 14 C := by
    refine ⟨?_,?_,?_⟩
    · intro g mem
      obtain ⟨j,found⟩ := List.mem_iff_getElem?.mp mem
      exact (normal j g found).1
    · intro j valid w read
      let g := C.gates[j]'valid
      have atJ : C.gates[j]? = some g := List.getElem?_eq_getElem valid
      have eq : gateAt C j = g := by
        unfold gateAt
        rw [List.getD_eq_getElem?_getD,atJ]
        rfl
      obtain ⟨_,a,b,ins,_,ha,hb⟩ := normal j g atJ
      rw [eq,ins] at read
      simp only [List.mem_cons,List.not_mem_nil,or_false] at read
      rcases read with rfl | rfl
      · exact ha
      · exact hb
    · intro g mem
      obtain ⟨j,found⟩ := List.mem_iff_getElem?.mp mem
      obtain ⟨_,a,b,ins,_,_,_⟩ := normal j g found
      rw [ins]
      rfl
  have distinct : ∀ g ∈ C.gates, g.inputs.getD 0 0 ≠ g.inputs.getD 1 0 := by
    intro g mem
    obtain ⟨j,found⟩ := List.mem_iff_getElem?.mp mem
    obtain ⟨_,a,b,ins,ne,_,_⟩ := normal j g found
    rw [ins]
    exact ne
  have equation (x : Fin 14 → Bool) : C.eval (List.ofFn x) = F x := by
    apply Bool.eq_iff_iff.mpr
    simp only [F,decide_eq_true_eq]
    exact exactSpec x
  obtain ⟨j,op,out,_,singletons⟩ := final
  exact remaining ⟨C,size,model,distinct,equation,⟨j,op,out,singletons⟩,frontier C size model equation⟩
