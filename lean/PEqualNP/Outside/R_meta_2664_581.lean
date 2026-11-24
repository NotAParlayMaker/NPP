import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.GenericRejection

theorem PEqualNP.Outside.R_meta_2664_581
    (straight :
      ∀ (q n : ℕ) (I : Fin n → Fin n → Prop) [DecidableRel I] (C : Circuit),
      let row := fun (b : Bool) (x : Fin n → Bool) (v : Bool) =>
        if b then List.ofFn x ++ List.replicate n v else List.replicate n v ++ List.ofFn x
      let bad := fun (g : Gate) => ∃ b : Bool, ∀ w ∈ g.inputs, ∃ x,
        (C.wires (row b x false)).getD w false ≠ (C.wires (row b x true)).getD w false
      199 ≤ q → n = q^2+q+1 →
      (∀ l, Fintype.card {p // I p l} = q+1) →
      (∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) → Monotone2 C → C.output < n+n+C.size →
      (∀ j g, C.gates[j]? = some g → ∃ a b, g.inputs = [a,b] ∧ a < b ∧ b < n+n+j) →
      (∀ p l, I p l → C.eval (incidenceInput {p} {l}) = true) →
      (∀ P L : Finset (Fin n), (∀ p ∈ P, ∀ l ∈ L, ¬ I p l) →
        C.eval (incidenceInput P L) = false) →
      (∀ g ∈ C.gates, g.op = .and → ¬ bad g) → n*(q+1) ≤ 3*C.size)
    (overlap :
      ∀ (q n : ℕ) (I : Fin n → Fin n → Prop) [DecidableRel I] (C : Circuit),
      let row := fun (b : Bool) (x : Fin n → Bool) (v : Bool) =>
        if b then List.ofFn x ++ List.replicate n v else List.replicate n v ++ List.ofFn x
      let bad := fun (g : Gate) => ∃ b : Bool, ∀ w ∈ g.inputs, ∃ x,
        (C.wires (row b x false)).getD w false ≠ (C.wires (row b x true)).getD w false
      199 ≤ q → n = q^2+q+1 →
      (∀ l, Fintype.card {p // I p l} = q+1) →
      (∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) → Monotone2 C → C.output < n+n+C.size →
      (∀ j g, C.gates[j]? = some g → ∃ a b, g.inputs = [a,b] ∧ a < b ∧ b < n+n+j) →
      (∀ p l, I p l → C.eval (incidenceInput {p} {l}) = true) →
      (∀ P L : Finset (Fin n), (∀ p ∈ P, ∀ l ∈ L, ¬ I p l) →
        C.eval (incidenceInput P L) = false) →
      (∃ g ∈ C.gates, g.op = .and ∧ bad g) → n*q ≤ 100*C.size) :
∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (199 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.MetaComplexity.Monotone2 x5 → x5.output < x2 + x2 + x5.size → (∀ (x12 : ℕ) (x13 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x12]? = Option.some x13 → ∃ (x15 : ℕ) (x16 : ℕ), x13.inputs = [x15, x16] ∧ x15 < x16 ∧ x16 < x2 + x2 + x12) → (∀ (x13 x14 : Fin x2), x3 x13 x14 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x16 : Fin (x2 + x2)) => Decidable.decide (x16 = Fin.castAdd x2 x13 ∨ x16 = Fin.natAdd x2 x14)) = Bool.true) → (∀ (x14 : Fin (x2 + x2) → Bool), (¬∃ (x15 : Fin x2) (x16 : Fin x2), x3 x15 x16 ∧ x14 (Fin.castAdd x2 x15) = Bool.true ∧ x14 (Fin.natAdd x2 x16) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x14 = Bool.false) → ∀ (x15 : Finset ℕ), (∀ (x16 : ℕ) (x17 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x16]? = Option.some x17 → x17.op = PEqualNP.CircuitLowerBounds.GateOp.and → x16 ∉ x15 → ¬((∀ x21 ∈ x17.inputs, ∃ (x23 : Fin x2 → Bool), (x5.wires (List.ofFn x23 ++ List.replicate x2 Bool.false)).getD x21 Bool.false ≠ (x5.wires (List.ofFn x23 ++ List.replicate x2 Bool.true)).getD x21 Bool.false) ∨ ∀ x21 ∈ x17.inputs, ∃ (x23 : Fin x2 → Bool), (x5.wires (List.replicate x2 Bool.false ++ List.ofFn x23)).getD x21 Bool.false ≠ (x5.wires (List.replicate x2 Bool.true ++ List.ofFn x23)).getD x21 Bool.false)) → (100 : ℕ) * x15.card < x2 * x1 → x2 * x1 ≤ (100 : ℕ) * x5.size := by
  intro q n I inst C big geom line unique mono valid shape pos neg marked covered small
  classical
  let bits (X Y : Finset (Fin n)) : Fin (n+n) → Bool :=
    Fin.addCases (fun p => decide (p ∈ X)) (fun l => decide (l ∈ Y))
  have trans (X Y : Finset (Fin n)) :
      C.eval (incidenceInput X Y) = circuitFun (n+n) C (bits X Y) :=
    congrArg C.eval (List.ofFn_fin_append _ _).symm
  have yes (p l : Fin n) (hit : I p l) : C.eval (incidenceInput {p} {l}) = true := by
    rw [trans]
    convert pos p l hit using 2
    funext i
    have sep (a b : Fin n) : Fin.castAdd n a ≠ Fin.natAdd n b := by
      intro e
      have value := congrArg Fin.val e
      change a.val = n+b.val at value
      omega
    refine Fin.addCases (fun a => ?_) (fun b => ?_) i
    · simp only [bits,Fin.addCases_left,Finset.mem_singleton,Fin.castAdd_inj,sep,or_false]
    · simp only [bits,Fin.addCases_right,Finset.mem_singleton,Fin.natAdd_inj,Ne.symm (sep _ _),false_or]
  have no (X Y : Finset (Fin n)) (avoid : ∀ p∈X, ∀ l∈Y, ¬I p l) :
      C.eval (incidenceInput X Y) = false := by
    rw [trans]
    apply neg
    rintro ⟨p,l,adj,hp,hl⟩
    exact avoid p (of_decide_eq_true (by simpa only [bits,Fin.addCases_left] using hp))
      l (of_decide_eq_true (by simpa only [bits,Fin.addCases_right] using hl)) adj
  let row := fun (b : Bool) (x : Fin n → Bool) (v : Bool) =>
    if b then List.ofFn x ++ List.replicate n v else List.replicate n v ++ List.ofFn x
  let hard := fun (g : Gate) => ∃ b : Bool, ∀ w ∈ g.inputs, ∃ x,
    (C.wires (row b x false)).getD w false ≠ (C.wires (row b x true)).getD w false
  by_cases ex : ∃ g ∈ C.gates, g.op = .and ∧ hard g
  · exact overlap q n I C big geom line unique mono valid shape yes no ex
  · have empty (g : Gate) (hg : g ∈ C.gates) (op : g.op = .and) : ¬hard g :=
      fun bad => ex ⟨g,hg,op,bad⟩
    have budget := straight q n I C big geom line unique mono valid shape yes no empty
    rw [Nat.mul_add,Nat.mul_one] at budget
    omega
