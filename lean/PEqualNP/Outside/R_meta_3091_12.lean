import Mathlib
import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
theorem PEqualNP.Outside.R_meta_3091_12
  (rank : ∀ C : Circuit, FanInTwo C → (∀ x : Fin 9 → Bool, (x 0 || x 3)=true → C.eval (List.ofFn x++[true])=(x 4 || (x 0 && (x 1 || x 5)) || (x 6 && (x 1 || x 8)) || (x 3 && (x 2 || x 8)) || (x 7 && (x 2 || x 5)))) →
      ∃ J : List ℕ, J.Nodup ∧ 12≤J.length ∧ ∀ j∈J, j<C.size ∧ (∀ i<10+j, ∀ b : Bool, ∃ x : Fin 9 → Bool, (x 0 || x 3)=true ∧
      (C.wires (List.ofFn x++[true])).getD (10+j) false ≠ Bool.xor ((C.wires (List.ofFn x++[true])).getD i false) b))
  (shape : ∀ (C : Circuit) (j : ℕ), FanInTwo C → j<C.size → (∀ i<10+j, ∀ b : Bool, ∃ x : Fin 9 → Bool, (x 0 || x 3)=true ∧
      (C.wires (List.ofFn x++[true])).getD (10+j) false ≠ Bool.xor ((C.wires (List.ofFn x++[true])).getD i false) b) → ∃ a b, a<10+j ∧ b<10+j ∧ a≠9 ∧ b≠9 ∧ a≠b ∧ (gateAt C j).inputs=[a,b] ∧ ((gateAt C j).op=.and ∨ (gateAt C j).op=.or))
  (mono : ∀ (C : Circuit) (J : List ℕ), FanInTwo C → C.size=14 →
    2≤List.count 9 (C.output::C.gates.flatMap Gate.inputs) → J.Nodup → 12≤J.length →
    (∀ j∈J, j<C.size ∧ (∀ i<10+j, ∀ b : Bool, ∃ x : Fin 9 → Bool, (x 0 || x 3)=true ∧
      (C.wires (List.ofFn x++[true])).getD (10+j) false ≠ Bool.xor ((C.wires (List.ofFn x++[true])).getD i false) b) ∧ (∃ a b, a<10+j ∧ b<10+j ∧ a≠9 ∧ b≠9 ∧ a≠b ∧ (gateAt C j).inputs=[a,b] ∧ ((gateAt C j).op=.and ∨ (gateAt C j).op=.or))) → (∀ g∈C.gates, g.op≠.not) →
    let rows := fun r : ℕ => fun i : Fin 9 => r.testBit i.val
    let ev := fun r => C.eval (List.ofFn (rows r)++[rows r 0 || rows r 3])
    (∃ r ∈ [3,6,12,17,24,33,66,132,160,264,288,320], ev r=false) ∨ (∃ r ∈ [42,50,69,104,116,138,201,208,261,276,385,402], ev r=true))
  (mixed : ∀ (C : Circuit) (J : List ℕ), FanInTwo C → C.size=14 →
    2≤List.count 9 (C.output::C.gates.flatMap Gate.inputs) → J.Nodup → 12≤J.length →
    (∀ j∈J, j<C.size ∧ (∀ i<10+j, ∀ b : Bool, ∃ x : Fin 9 → Bool, (x 0 || x 3)=true ∧
      (C.wires (List.ofFn x++[true])).getD (10+j) false ≠ Bool.xor ((C.wires (List.ofFn x++[true])).getD i false) b) ∧ (∃ a b, a<10+j ∧ b<10+j ∧ a≠9 ∧ b≠9 ∧ a≠b ∧ (gateAt C j).inputs=[a,b] ∧ ((gateAt C j).op=.and ∨ (gateAt C j).op=.or))) → (∃ g∈C.gates, g.op=.not) → ∃ x : Fin 9 → Bool,
    C.eval (List.ofFn x++[x 0 || x 3]) ≠ (fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any (fun e => x (Fin.ofNat 9 (e/10)) && x (Fin.ofNat 9 (e % 10)))) x) :
have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → x2.size = (14 : ℕ) → (x2.output ≤ (10 : ℕ) + x2.size ∧ ∀ x5 ∈ x2.gates, ∀ x7 ∈ x5.inputs, x7 ≤ (10 : ℕ) + x2.size) → (∀ x6 < (10 : ℕ) + x2.size, x6 ∈ x2.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x2.gates) → (9 : ℕ) + (List.filter (fun (x7 : PEqualNP.CircuitLowerBounds.Gate) => x7.op.eval [Bool.false] && !x7.op.eval [Bool.true]) x2.gates).length + ∑ x7 ∈ Finset.range ((10 : ℕ) + x2.size), (List.count x7 (x2.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x2.gates) - (1 : ℕ)) ≤ x2.size → (2 : ℕ) ≤ List.count (9 : ℕ) (x2.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x2.gates) → (∀ (x9 : Fin (9 : ℕ)), ∃ (x10 : Fin (9 : ℕ) → Bool), x2.eval (List.ofFn x10 ++ [x10 x9]) ≠ x1 x10) → ∃ (x10 : Fin (9 : ℕ) → Bool), x2.eval (List.ofFn x10 ++ [x10 (0 : Fin (9 : ℕ)) || x10 (3 : Fin (9 : ℕ))]) ≠ x1 x10 := by
  dsimp only
  intro C fan size _ _ _ inputs _
  by_contra! agree
  let F := fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any (fun e => x (Fin.ofNat 9 (e/10)) && x (Fin.ofNat 9 (e % 10)))
  have full (x : Fin 9 → Bool) : C.eval (List.ofFn x++[x 0 || x 3])=F x := by
    trans ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))
    · exact agree x
    · simp only [F,List.any_cons,List.any_nil,Bool.or_false,Bool.or_assoc]
      rfl
  have active (x : Fin 9 → Bool) (hh : (x 0 || x 3)=true) : C.eval (List.ofFn x++[true])=(x 4 || (x 0 && (x 1 || x 5)) || (x 6 && (x 1 || x 8)) || (x 3 && (x 2 || x 8)) || (x 7 && (x 2 || x 5))) := by
    have eq := agree x
    rw [hh] at eq
    rw [eq]
    clear eq
    generalize x 0=a at hh ⊢
    generalize x 1=b at hh ⊢
    generalize x 2=c at hh ⊢
    generalize x 3=d at hh ⊢
    generalize x 4=e at hh ⊢
    generalize x 5=f at hh ⊢
    generalize x 6=g at hh ⊢
    generalize x 7=h at hh ⊢
    generalize x 8=i at hh ⊢
    revert hh
    decide +revert
  obtain ⟨J,nd,card,members⟩ := rank C fan active
  have marked := fun (j : ℕ) (h : j∈J) =>
    And.intro (members j h).1 (And.intro (members j h).2 (shape C j fan (members j h).1 (members j h).2))
  by_cases neg : ∃ g∈C.gates, g.op=.not
  · obtain ⟨x,h⟩ := mixed C J fan size inputs nd card marked neg
    exact h (full x)
  · push Not at neg
    obtain h|h := mono C J fan size inputs nd card marked neg
    · obtain ⟨r,hr,fail⟩ := h
      have all : ([3,6,12,17,24,33,66,132,160,264,288,320] : List ℕ).all (fun r => F ((fun r : ℕ => fun i : Fin 9 => r.testBit i.val) r))=true := by decide +kernel
      have pos := List.all_eq_true.mp all r hr
      exact Bool.noConfusion (pos.symm.trans ((full ((fun r : ℕ => fun i : Fin 9 => r.testBit i.val) r)).symm.trans fail))
    · obtain ⟨r,hr,fail⟩ := h
      have all : ([42,50,69,104,116,138,201,208,261,276,385,402] : List ℕ).all (fun r => !F ((fun r : ℕ => fun i : Fin 9 => r.testBit i.val) r))=true := by decide +kernel
      have neg := List.all_eq_true.mp all r hr
      have yes := (full ((fun r : ℕ => fun i : Fin 9 => r.testBit i.val) r)).symm.trans fail
      rw [yes] at neg
      contradiction
