import Mathlib.Data.List.Basic
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Prepending NOT x0 and OR(x4, xb) to the circuit gives a circuit on the nine plain inputs.
-- The binary-gate floor (fourteen non-NOT gates, as in L_meta_3440 binaryFloor) then forces
-- every gate of the 13-gate circuit to be an AND or OR: the residual is the monotone core.
theorem PEqualNP.Outside.R_meta_4984_1
    (binaryFloor : ∀ D : Circuit, FanInTwo D →
      (∀ x : Fin 9 → Bool, D.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) →
      14 ≤ D.gates.countP (fun g => GateOp.rec true true false (fun _ => true) true g.op))
    (monotoneCore : ∀ b ∈ ([1, 2, 3, 4, 6] : List (Fin 9)), ∀ C : Circuit,
      Monotone2 C → C.size = 13 →
      (∀ a c : Fin 9, a ≠ c → (⟨GateOp.and, [a.val, c.val]⟩ : Gate) ∉ C.gates) →
      ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [!x 0] ++ [x 4 || x b]) ≠ ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) :
    ∀ x1 ∈ [(1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))], ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x3 → x3.size ≤ (13 : ℕ) → (∀ (x6 x7 : Fin (9 : ℕ)), x6 ≠ x7 → { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [↑x6, ↑x7] : PEqualNP.CircuitLowerBounds.Gate } ∉ x3.gates) → ∃ (x7 : Fin (9 : ℕ) → Bool), x3.eval (List.ofFn x7 ++ [!x7 (0 : Fin (9 : ℕ))] ++ [x7 (4 : Fin (9 : ℕ)) || x7 x1]) ≠ (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ))) := by
  intro b hb C fan budget noRaw
  classical
  by_contra noWitness
  have correct (x : Fin 9 → Bool) :
      C.eval (List.ofFn x ++ [!x 0] ++ [x 4 || x b]) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) :=
    Classical.not_not.mp (fun wrong => noWitness ⟨x, wrong⟩)
  let first : Gate := ⟨.not, [0]⟩
  let second : Gate := ⟨.or, [4, b.val]⟩
  let D : Circuit := ⟨first :: second :: C.gates, C.output⟩
  have dfan : FanInTwo D := by
    intro g hg
    change g ∈ first :: second :: C.gates at hg
    rcases List.mem_cons.mp hg with rfl | h
    · simp [first]
    rcases List.mem_cons.mp h with rfl | h
    · simp [second]
    exact fan g h
  have dcorrect (x : Fin 9 → Bool) : D.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) := by
    let bits := List.ofFn x
    have read0 : bits.getD 0 false = x 0 := by
      dsimp only [bits]
      rw [List.getD_eq_getElem _ _ (by simp)]
      simp
    have read (j : Fin 9) : (bits ++ [!x 0]).getD j.val false = x j := by
      have hj : j.val < bits.length := by simp [bits]
      rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_left hj]
      exact List.getElem_ofFn hj
    have h4 := read (4 : Fin 9)
    change (bits ++ [!x 0]).getD 4 false = x 4 at h4
    let gate1 := first.op.eval (first.inputs.map fun j => bits.getD j false)
    have e1 : gate1 = !x 0 := by
      change (!bits.getD 0 false) = !x 0
      rw [read0]
    change C.eval ((bits ++ [gate1]) ++ [second.op.eval
      (second.inputs.map fun j => (bits ++ [gate1]).getD j false)]) = _
    rw [e1]
    change C.eval ((bits ++ [!x 0]) ++ [(bits ++ [!x 0]).getD 4 false ||
      ((bits ++ [!x 0]).getD b.val false || false)]) = _
    rw [Bool.or_false, h4, read b]
    exact correct x
  let binary (g : Gate) : Bool := GateOp.rec true true false (fun _ => true) true g.op
  have count := binaryFloor D dfan dcorrect
  change 14 ≤ (first :: second :: C.gates).countP binary at count
  have hn : binary first = false := rfl
  have ho : binary second = true := rfl
  simp [hn, ho] at count
  change C.gates.length ≤ 13 at budget
  have upper := List.countP_le_length (p := binary) (l := C.gates)
  have allBinary : C.gates.countP binary = C.gates.length := by omega
  have mono : Monotone2 C := by
    intro g hg
    obtain ⟨op, arity⟩ := fan g hg
    refine ⟨?_, arity⟩
    rcases op with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · have keep := List.countP_eq_length.mp allBinary g hg
      change g.op = .not at h
      simp [binary, h] at keep
  have exactSize : C.size = 13 := by change C.gates.length = 13; omega
  obtain ⟨x, wrong⟩ := monotoneCore b hb C mono exactSize noRaw
  exact wrong (correct x)
