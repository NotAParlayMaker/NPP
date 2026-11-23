import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1354

open PEqualNP.CircuitLowerBounds

-- The removed input is redirected to a wire beyond the end of the entire circuit.
def rewire (n limit wire : ℕ) : ℕ :=
  if wire < n then wire else if wire = n then limit else wire - 1

def restrictGate (n limit : ℕ) (gate : Gate) : Gate :=
  ⟨gate.op, gate.inputs.map (rewire n limit)⟩

def execute (gates : List Gate) (values : List Bool) : List Bool :=
  gates.foldl (fun ws g => ws ++ [g.op.eval (g.inputs.map fun w => ws.getD w false)]) values

lemma read_wire (inputs history : List Bool) (limit wire : ℕ)
    (bound : inputs.length + history.length ≤ limit) :
    (inputs ++ history).getD (rewire inputs.length limit wire) false =
      (inputs ++ false :: history).getD wire false := by
  unfold rewire
  by_cases below : wire < inputs.length
  · rw [ite_eq_left below, List.getD_append _ _ _ _ below, List.getD_append _ _ _ _ below]
  rw [ite_eq_right below]
  by_cases same : wire = inputs.length
  · subst wire
    rw [ite_eq_left rfl, List.getD_eq_default _ _ (by simpa using bound),
      List.getD_append_right _ _ _ _ (le_refl _)]
    simp
  · rw [ite_eq_right same, List.getD_append_right _ _ _ _ (by omega),
      List.getD_append_right _ _ _ _ (by omega)]
    have index : wire - inputs.length = (wire - 1 - inputs.length) + 1 := by omega
    rw [index, List.getD_cons_succ]

lemma histories (inputs : List Bool) (limit : ℕ) (gates : List Gate) (history : List Bool)
    (bound : inputs.length + history.length + gates.length ≤ limit) :
    ∃ result : List Bool,
      execute (gates.map (restrictGate inputs.length limit)) (inputs ++ history) = inputs ++ result ∧
      execute gates (inputs ++ false :: history) = inputs ++ false :: result := by
  induction gates generalizing history with
  | nil => exact ⟨history, rfl, rfl⟩
  | cons g gs ih =>
    let val := g.op.eval (g.inputs.map fun w => (inputs ++ false :: history).getD w false)
    have equalReads :
        (g.inputs.map (rewire inputs.length limit)).map (fun w => (inputs ++ history).getD w false) =
        g.inputs.map (fun w => (inputs ++ false :: history).getD w false) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro w _
      exact read_wire inputs history limit w (by simp only [List.length_cons] at bound; omega)
    obtain ⟨r, newRun, oldRun⟩ := ih (history ++ [val]) (by simp_all [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm])
    refine ⟨r, ?_, ?_⟩
    · change execute (gs.map (restrictGate inputs.length limit))
          ((inputs ++ history) ++ [g.op.eval _]) = inputs ++ r
      simp only [restrictGate] at *
      rw [equalReads, List.append_assoc]
      exact newRun
    · change execute gs ((inputs ++ false :: history) ++ [val]) = inputs ++ false :: r
      simpa only [List.append_assoc, List.cons_append] using oldRun

end PEqualNP.Outside.L_meta_1354

open PEqualNP.Outside.L_meta_1354

theorem PEqualNP.Outside.L_meta_1354 : ∀ (n : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate), ∃ gates' : List PEqualNP.CircuitLowerBounds.Gate, gates'.map PEqualNP.CircuitLowerBounds.Gate.op = gates.map PEqualNP.CircuitLowerBounds.Gate.op ∧ gates'.map (fun g => g.inputs.length) = gates.map (fun g => g.inputs.length) ∧ ∀ (j : ℕ) (x : Fin n → Bool), j < gates.length → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', n + j⟩ (List.ofFn x) = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + 1 + j⟩ (List.ofFn x ++ [false]) := by
  intro n gates
  let limit := n + gates.length
  refine ⟨gates.map (restrictGate n limit), ?_, ?_, ?_⟩
  · simp [List.map_map, Function.comp_def, restrictGate]
  · simp [List.map_map, Function.comp_def, restrictGate]
  · intro j x hj
    let inputs := List.ofFn x
    have len : inputs.length = n := List.length_ofFn
    obtain ⟨r, left, right⟩ := histories inputs limit gates [] (by simp [len, limit])
    simp only [List.append_nil, len] at left
    change (execute (gates.map (restrictGate n limit)) inputs).getD (n + j) false =
      (execute gates (inputs ++ [false])).getD (n + 1 + j) false
    rw [left, right, List.getD_append_right _ _ _ _ (by omega),
      List.getD_append_right _ _ _ _ (by omega)]
    have index : n + 1 + j - inputs.length = (n + j - inputs.length) + 1 := by omega
    rw [index, List.getD_cons_succ]
