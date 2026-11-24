import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_2444_773
    (strip : ∀ (n : ℕ) (f : (Fin n → Bool) → Bool) (C : Circuit), FanInTwo C →
      (∃ x, f x = true) →
      (∀ x, (C.wires (List.ofFn x)).getD n false = f x) →
      ∃ D : Circuit, FanInTwo D ∧ D.size + 1 = C.size ∧
        ∀ x, D.eval (List.ofFn x ++ [f x]) = C.eval (List.ofFn x))
    (liveReaders :
      let F := fun x : Fin 9 → Bool =>
        (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
        (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
        (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
      ∀ (p : Fin 9 × Fin 9), p.1.val * 9 + p.2.val ∈ ([1,2,3,4,6,42] : List ℕ) →
      ∀ D : Circuit, (∀ x, D.eval (List.ofFn x ++ [x p.1 && x p.2]) = F x) →
        ∀ v : Fin 9, v ≠ p.1 → v ≠ p.2 → ∀ (c : Fin 10) (b : Bool),
          (c = p.1.castSucc ∨ c = p.2.castSucc ∨ c = Fin.last 9 ∧ b = false) →
          ∃ g ∈ D.gates, v.val ∈ g.inputs ∧
            (c.val ∈ g.inputs → g.op ≠ if b then GateOp.or else GateOp.and))
    (adjacent :
      let F := fun x : Fin 9 → Bool =>
        (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
        (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
        (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
      ∀ (p : Fin 9 × Fin 9), p.1.val * 9 + p.2.val ∈ ([1,4] : List ℕ) →
      ∀ D : Circuit, FanInTwo D → D.size ≤ 14 →
        (∀ x, D.eval (List.ofFn x ++ [x p.1 && x p.2]) = F x) →
        (∀ v : Fin 9, v ≠ p.1 → v ≠ p.2 → ∀ (c : Fin 10) (b : Bool),
          (c = p.1.castSucc ∨ c = p.2.castSucc ∨ c = Fin.last 9 ∧ b = false) →
          ∃ g ∈ D.gates, v.val ∈ g.inputs ∧
            (c.val ∈ g.inputs → g.op ≠ if b then GateOp.or else GateOp.and)) → False)
    (nonadjacent :
      let F := fun x : Fin 9 → Bool =>
        (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
        (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
        (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
      ∀ (p : Fin 9 × Fin 9), p.1.val * 9 + p.2.val ∈ ([2,3,6,42] : List ℕ) →
      ∀ D : Circuit, FanInTwo D → D.size ≤ 14 →
        (∀ x, D.eval (List.ofFn x ++ [x p.1 && x p.2]) = F x) →
        (∀ v : Fin 9, v ≠ p.1 → v ≠ p.2 → ∀ (c : Fin 10) (b : Bool),
          (c = p.1.castSucc ∨ c = p.2.castSucc ∨ c = Fin.last 9 ∧ b = false) →
          ∃ g ∈ D.gates, v.val ∈ g.inputs ∧
            (c.val ∈ g.inputs → g.op ≠ if b then GateOp.or else GateOp.and)) → False) :
    ∀ x1 ∈ [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)))], ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x3 → (∀ (x5 : Fin (9 : ℕ) → Bool), (x3.wires (List.ofFn x5)).getD (9 : ℕ) Bool.false = (x5 x1.1 && x5 x1.2)) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x3 = fun (x6 : Fin (9 : ℕ) → Bool) => x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) → (16 : ℕ) ≤ x3.size := by
  intro p hp C hC hHead hF
  by_contra smaller
  let F := fun x : Fin 9 → Bool =>
        (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
        (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
        (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
  let q := fun x : Fin 9 → Bool => x p.1 && x p.2
  obtain ⟨D, hD, hSize, eval⟩ := strip 9 q C hC ⟨fun _ => true, rfl⟩ hHead
  have budget : D.size ≤ 14 := by omega
  have hCorrect (x : Fin 9 → Bool) : D.eval (List.ofFn x ++ [q x]) = F x := by
    rw [eval]
    exact congrFun hF x
  have hCodes : p.1.val * 9 + p.2.val ∈ ([1,2,3,4,6,42] : List ℕ) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hLive := liveReaders p hCodes D hCorrect
  by_cases edge : p.1.val * 9 + p.2.val ∈ ([1,4] : List ℕ)
  · exact adjacent p edge D hD budget hCorrect hLive
  · have other : p.1.val * 9 + p.2.val ∈ ([2,3,6,42] : List ℕ) := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hCodes edge ⊢
      omega
    exact nonadjacent p other D hD budget hCorrect hLive
