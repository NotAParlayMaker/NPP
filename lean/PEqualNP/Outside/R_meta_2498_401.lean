import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Cut by the operation of the second gate (wire 10). FanInTwo leaves AND, OR and NOT.
-- A circuit with at most one gate cannot compute the edge function: its wires are the inputs
-- and the prescribed first gate, so that case is closed here by evaluation.
theorem PEqualNP.Outside.R_meta_2498_401
    (secondAnd : ∀ C : Circuit, FanInTwo C →
      (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x 0 || x 1)) →
      circuitFun 9 C = (fun x : Fin 9 → Bool =>
        ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] :
          List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)) →
      (∀ v ∈ ([0,1,2,3,5,8] : List (Fin 9)), ∀ S : Finset ℕ,
        (∀ j ∈ S, j < C.size ∧
          ((∃ b : Bool, ∀ x : Fin 9 → Bool, x v = false →
            (C.wires (List.ofFn x)).getD (9 + j) false = b) ∨
          (∃ i < 9 + j, ∀ x : Fin 9 → Bool, x v = false →
            (C.wires (List.ofFn x)).getD (9 + j) false =
              (C.wires (List.ofFn x)).getD i false))) →
        S.card ≤ 3) →
      Option.map (fun g : Gate => g.op) C.gates[1]? = some GateOp.and →
      16 ≤ C.size)
    (secondOr : ∀ C : Circuit, FanInTwo C →
      (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x 0 || x 1)) →
      circuitFun 9 C = (fun x : Fin 9 → Bool =>
        ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] :
          List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)) →
      (∀ v ∈ ([0,1,2,3,5,8] : List (Fin 9)), ∀ S : Finset ℕ,
        (∀ j ∈ S, j < C.size ∧
          ((∃ b : Bool, ∀ x : Fin 9 → Bool, x v = false →
            (C.wires (List.ofFn x)).getD (9 + j) false = b) ∨
          (∃ i < 9 + j, ∀ x : Fin 9 → Bool, x v = false →
            (C.wires (List.ofFn x)).getD (9 + j) false =
              (C.wires (List.ofFn x)).getD i false))) →
        S.card ≤ 3) →
      Option.map (fun g : Gate => g.op) C.gates[1]? = some GateOp.or →
      16 ≤ C.size)
    (secondNot : ∀ C : Circuit, FanInTwo C →
      (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x 0 || x 1)) →
      circuitFun 9 C = (fun x : Fin 9 → Bool =>
        ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] :
          List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)) →
      (∀ v ∈ ([0,1,2,3,5,8] : List (Fin 9)), ∀ S : Finset ℕ,
        (∀ j ∈ S, j < C.size ∧
          ((∃ b : Bool, ∀ x : Fin 9 → Bool, x v = false →
            (C.wires (List.ofFn x)).getD (9 + j) false = b) ∨
          (∃ i < 9 + j, ∀ x : Fin 9 → Bool, x v = false →
            (C.wires (List.ofFn x)).getD (9 + j) false =
              (C.wires (List.ofFn x)).getD i false))) →
        S.card ≤ 3) →
      Option.map (fun g : Gate => g.op) C.gates[1]? = some GateOp.not →
      16 ≤ C.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (0 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x5 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x4 x5.1 && x4 x5.2) → (∀ x5 ∈ [(0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))], ∀ (x7 : Finset ℕ), (∀ x8 ∈ x7, x8 < x1.size ∧ ((∃ (x10 : Bool), ∀ (x11 : Fin (9 : ℕ) → Bool), x11 x5 = Bool.false → (x1.wires (List.ofFn x11)).getD ((9 : ℕ) + x8) Bool.false = x10) ∨ ∃ x10 < (9 : ℕ) + x8, ∀ (x11 : Fin (9 : ℕ) → Bool), x11 x5 = Bool.false → (x1.wires (List.ofFn x11)).getD ((9 : ℕ) + x8) Bool.false = (x1.wires (List.ofFn x11)).getD x10 Bool.false)) → x7.card ≤ (3 : ℕ)) → (16 : ℕ) ≤ x1.size := by
  intro C hC first comp elim
  rcases hsec : C.gates[1]? with _ | g
  · exfalso
    rcases C with ⟨gates, o⟩
    have hlen : gates.length ≤ 1 := by
      simpa [List.getElem?_eq_none_iff] using hsec
    match gates, hlen with
    | [], _ =>
      have h := first (fun _ => true)
      simp [Circuit.wires] at h
    | [g0], _ =>
      have key : ∀ x : Fin 9 → Bool,
          (List.ofFn x ++ [x 0 || x 1]).getD o false =
          ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] :
            List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2) := by
        intro x
        have h1 := first x
        have h2 := congrFun comp x
        have hw : Circuit.wires ⟨[g0], o⟩ (List.ofFn x) =
            List.ofFn x ++ [g0.op.eval (g0.inputs.map fun i => (List.ofFn x).getD i false)] := rfl
        change (Circuit.wires ⟨[g0], o⟩ (List.ofFn x)).getD o false = _ at h2
        rw [hw] at h1 h2
        have hb : g0.op.eval (g0.inputs.map fun i => (List.ofFn x).getD i false) = (x 0 || x 1) := by
          simpa [List.getD_eq_getElem?_getD] using h1
        rw [hb] at h2
        exact h2
      by_cases ho : o < 10
      · interval_cases o
        all_goals first
          | exact absurd (key (fun i => decide (i = 0))) (by decide)
          | exact absurd (key (fun i => decide (i = 1))) (by decide)
          | exact absurd (key (fun i => decide (i = 2))) (by decide)
          | exact absurd (key (fun i => decide (i = 3))) (by decide)
          | exact absurd (key (fun i => decide (i = 4))) (by decide)
          | exact absurd (key (fun i => decide (i = 5))) (by decide)
          | exact absurd (key (fun i => decide (i = 6))) (by decide)
          | exact absurd (key (fun i => decide (i = 7))) (by decide)
          | exact absurd (key (fun i => decide (i = 8))) (by decide)
      · have h := key (fun _ => true)
        rw [List.getD_eq_default _ _ (by simp; omega)] at h
        exact absurd h (by decide)
  · have hg : g ∈ C.gates := List.mem_of_getElem? hsec
    have hop := (hC g hg).1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with hop | hop | hop
    · exact secondAnd C hC first comp elim (by simp [hsec, hop])
    · exact secondOr C hC first comp elim (by simp [hsec, hop])
    · exact secondNot C hC first comp elim (by simp [hsec, hop])
