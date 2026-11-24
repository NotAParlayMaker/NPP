import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover

set_option maxHeartbeats 3000000 in
theorem PEqualNP.Outside.R_meta_3456_417
    (normalize : ∀ (n : ℕ) (C : Circuit), Monotone2 C → ReadsBack n C →
      circuitFun n C (fun _ => false) = false →
      ∃ D : Circuit, Monotone2 D ∧ ReadsBack n D ∧ D.size ≤ C.size ∧
        circuitFun n D = circuitFun n C ∧
        ∀ j < D.size, (gateAt D j).op = GateOp.and → ∃ a b, (gateAt D j).inputs = [a,b] ∧ a ≠ b)
    (rawOperand :
      let clean (n : ℕ) (C : Circuit) (j : ℕ) := ∀ i < j, (gateAt C i).op = GateOp.and →
        ∀ t : Fin n, gateVal n C i (fun k => decide (k = t)) = false
      let shape (C : Circuit) := ∀ j < C.size, (gateAt C j).op = GateOp.and →
        ∃ a b, (gateAt C j).inputs = [a,b] ∧ a ≠ b
      ∀ (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit) (j a b : ℕ),
        (∀ p p' l l', p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) →
        Monotone2 C → ReadsBack (N+N) C → shape C →
        (∀ z, circuitFun (N+N) C z = true ↔
          ∃ p l, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
        j < C.size → clean (N+N) C j → ¬ clean (N+N) C (j+1) →
        (gateAt C j).inputs = [a,b] → (a < N+N ∨ b < N+N) →
        ∃ D : Circuit, Monotone2 D ∧ ReadsBack (N+N) D ∧
          circuitFun (N+N) D = circuitFun (N+N) C ∧
          (D.size < C.size ∨ (D.size = C.size ∧ shape D ∧ clean (N+N) D (j+1))))
    (gateOperands :
      let clean (n : ℕ) (C : Circuit) (j : ℕ) := ∀ i < j, (gateAt C i).op = GateOp.and →
        ∀ t : Fin n, gateVal n C i (fun k => decide (k = t)) = false
      let shape (C : Circuit) := ∀ j < C.size, (gateAt C j).op = GateOp.and →
        ∃ a b, (gateAt C j).inputs = [a,b] ∧ a ≠ b
      ∀ (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit) (j a b : ℕ),
        (∀ p p' l l', p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) →
        Monotone2 C → ReadsBack (N+N) C → shape C →
        (∀ z, circuitFun (N+N) C z = true ↔
          ∃ p l, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
        j < C.size → clean (N+N) C j → ¬ clean (N+N) C (j+1) →
        (gateAt C j).inputs = [a,b] → (N+N ≤ a ∧ N+N ≤ b) →
        ∃ D : Circuit, Monotone2 D ∧ ReadsBack (N+N) D ∧
          circuitFun (N+N) D = circuitFun (N+N) C ∧
          (D.size < C.size ∨ (D.size = C.size ∧ shape D ∧ clean (N+N) D (j+1)))) :
    ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) C → (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = true ↔ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) D ∧ D.size ≤ C.size ∧ (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) D z = true ↔ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧ (∀ j < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∀ p : Fin N, (D.wires (List.ofFn (fun kc : Fin (N + N) => decide (kc = Fin.castAdd N p)))).getD (N + N + j) false = false) ∧ ∀ l : Fin N, (D.wires (List.ofFn (fun kd : Fin (N + N) => decide (kd = Fin.natAdd N l)))).getD (N + N + j) false = false) := by
  intro N I _ C noSquare mono back correct
  classical
  let n := N+N
  let solves (A : Circuit) := ∀ z, circuitFun n A z = true ↔
    ∃ p l, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true
  let clean (A : Circuit) (j : ℕ) := ∀ i < j, (gateAt A i).op = GateOp.and →
    ∀ t : Fin n, gateVal n A i (fun k => decide (k = t)) = false
  let shape (A : Circuit) := ∀ j < A.size, (gateAt A j).op = GateOp.and →
    ∃ a b, (gateAt A j).inputs = [a,b] ∧ a ≠ b
  let valid (A : Circuit) := Monotone2 A ∧ ReadsBack n A ∧ solves A
  let result (k : ℕ) := ∃ A : Circuit, valid A ∧ A.size ≤ k ∧ clean A A.size
  have zero (A : Circuit) (h : solves A) : circuitFun n A (fun _ => false) = false := by
    cases e : circuitFun n A (fun _ => false) with
    | false => rfl
    | true =>
      obtain ⟨p,l,inc,bad,_⟩ := (h _).mp e
      exact Bool.noConfusion bad
  have same {A B : Circuit} (h : solves A) (he : circuitFun n B = circuitFun n A) : solves B := by
    intro z
    rw [he]
    exact h z
  have weaken {k l : ℕ} (h : k ≤ l) (r : result k) : result l := by
    obtain ⟨A,ok,small,allClean⟩ := r
    exact ⟨A,ok,small.trans h,allClean⟩
  have solve : ∀ k, ∀ A : Circuit, A.size = k → valid A → shape A → result k := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k smaller =>
      have advance : ∀ m, ∀ A : Circuit, ∀ j ≤ k, k-j = m →
          A.size = k → valid A → shape A → clean A j → result k := by
        intro m
        induction m using Nat.strong_induction_on with
        | ind m later =>
          intro A j jle dist hsize hok hshape front
          by_cases done : clean A k
          · exact ⟨A,hok,hsize.le,hsize.symm ▸ done⟩
          have jlt : j < k := by
            by_contra! h
            obtain rfl : j = k := Nat.le_antisymm jle h
            exact done front
          by_cases next : clean A (j+1)
          · exact later (k-(j+1)) (by omega) A (j+1) (by omega) rfl hsize hok hshape next
          have hop : (gateAt A j).op = GateOp.and := by
            by_contra notAnd
            apply next
            intro i hi ha t
            by_cases ilt : i < j
            · exact front i ilt ha t
            · obtain rfl : i = j := by omega
              exact (notAnd ha).elim
          obtain ⟨a,b,inputs,_⟩ := hshape j (by omega) hop
          have repl : ∃ D : Circuit, Monotone2 D ∧ ReadsBack n D ∧
              circuitFun n D = circuitFun n A ∧
              (D.size < A.size ∨ (D.size = A.size ∧ shape D ∧ clean D (j+1))) := by
            by_cases raw : a < n ∨ b < n
            · exact rawOperand N I A j a b noSquare hok.1 hok.2.1 hshape hok.2.2
                (by omega) front next inputs raw
            · exact gateOperands N I A j a b noSquare hok.1 hok.2.1 hshape hok.2.2
                (by omega) front next inputs ⟨by omega,by omega⟩
          obtain ⟨D,dm,db,eq,smallerD | ⟨sizeD,shapeD,frontD⟩⟩ := repl
          have dsolves := same hok.2.2 eq
          · obtain ⟨E,em,eb,leE,eqE,shapeE⟩ := normalize n D dm db (zero D dsolves)
            have elt : E.size < k := by omega
            exact weaken elt.le (smaller E.size elt E rfl ⟨em,eb,same dsolves eqE⟩ shapeE)
          · exact later (k-(j+1)) (by omega) D (j+1) (by omega) rfl
              (sizeD.trans hsize) ⟨dm,db,same hok.2.2 eq⟩ shapeD frontD
      intro A hsize hok hshape
      exact advance k A 0 (Nat.zero_le _) (Nat.sub_zero k) hsize hok hshape
        (fun i hi => (Nat.not_lt_zero i hi).elim)
  obtain ⟨A,am,ab,leA,eqA,shapeA⟩ := normalize n C mono back (zero C correct)
  obtain ⟨D,⟨dm,db,dsolve⟩,leD,good⟩ :=
    weaken leA (solve A.size A rfl ⟨am,ab,same correct eqA⟩ shapeA)
  refine ⟨D,dm,db,leD,dsolve,?_⟩
  intro j hj hop
  exact ⟨fun p => good j hj hop (Fin.castAdd N p),fun l => good j hj hop (Fin.natAdd N l)⟩
