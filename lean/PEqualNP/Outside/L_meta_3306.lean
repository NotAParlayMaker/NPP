import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

namespace PEqualNP.Outside.L_meta_3306

noncomputable def orientAnd (A B : Finset ℕ) (g : Gate) : Gate := by
  classical
  exact if g.op = .and ∧ ¬ (∃ a b, g.inputs = [a, b] ∧ a ∈ B ∧ b ∈ A) then
    { g with inputs := g.inputs.reverse }
  else g

theorem orientAnd_op (A B : Finset ℕ) (g : Gate) : (orientAnd A B g).op = g.op := by
  unfold orientAnd
  split <;> rfl

theorem orientAnd_inputs (A B : Finset ℕ) (g : Gate) (i : ℕ) :
    i ∈ (orientAnd A B g).inputs ↔ i ∈ g.inputs := by
  unfold orientAnd
  split <;> simp

theorem orientAnd_arity (A B : Finset ℕ) (g : Gate) :
    (orientAnd A B g).inputs.length = g.inputs.length := by
  unfold orientAnd
  split <;> simp

theorem orientAnd_or (A B : Finset ℕ) (g : Gate) (h : g.op = .or) :
    orientAnd A B g = g := by
  simp [orientAnd, h]

theorem orientAnd_value (A B : Finset ℕ) (g : Gate) (w : List Bool) :
    (orientAnd A B g).op.eval ((orientAnd A B g).inputs.map (fun i => w.getD i false)) =
      g.op.eval (g.inputs.map (fun i => w.getD i false)) := by
  unfold orientAnd
  split
  next swap =>
    simp [swap.1, GateOp.eval, List.map_reverse]
  next =>
    rfl

theorem orientAnd_fold (A B : Finset ℕ) (gs : List Gate) (w : List Bool) :
    (gs.map (orientAnd A B)).foldl
      (fun w g => w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]) w =
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]) w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons, List.foldl_cons, orientAnd_value]
    exact ih _

end PEqualNP.Outside.L_meta_3306

open PEqualNP.Outside.L_meta_3306

theorem PEqualNP.Outside.L_meta_3306 (n : ℕ) (C : Circuit) (A B : Finset ℕ)
    (model : IsAO2 n C)
    (cross : ∀ j < C.gates.length, (gateAt C j).op = .and →
      ∃ a b, (gateAt C j).inputs = [a, b] ∧
        ((a ∈ A ∧ b ∈ B) ∨ (a ∈ B ∧ b ∈ A))) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size = C.size ∧ circuitFun n D = circuitFun n C ∧
      (∀ j : ℕ, (gateAt D j).op = (gateAt C j).op) ∧
      (∀ j : ℕ, (gateAt C j).op = .or → gateAt D j = gateAt C j) ∧
      ∀ j < D.gates.length, (gateAt D j).op = .and →
        ∃ a b, (gateAt D j).inputs = [a, b] ∧ a ∈ B ∧ b ∈ A := by
  classical
  let D : Circuit := ⟨C.gates.map (orientAnd A B), C.output⟩
  have size : D.gates.length = C.gates.length := List.length_map _
  have atGate (j : ℕ) : gateAt D j = orientAnd A B (gateAt C j) := by
    unfold gateAt
    change (C.gates.map (orientAnd A B)).getD j ⟨.or, []⟩ =
      orientAnd A B (C.gates.getD j ⟨.or, []⟩)
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
    cases C.gates[j]? <;> simp [orientAnd]
  have op (j : ℕ) : (gateAt D j).op = (gateAt C j).op :=
    (congrArg Gate.op (atGate j)).trans (orientAnd_op A B _)
  have same : circuitFun n D = circuitFun n C := by
    funext x
    exact congrArg (fun w : List Bool => w.getD C.output false)
      (orientAnd_fold A B C.gates (List.ofFn x))
  refine ⟨D, ⟨?_, ?_, ?_⟩, size, same, op, ?_, ?_⟩
  · intro g belongs
    obtain ⟨h, old, rfl⟩ := List.mem_map.mp belongs
    rw [orientAnd_op]
    exact model.1 h old
  · intro j index w read
    rw [atGate] at read
    exact model.2.1 j (size ▸ index) w ((orientAnd_inputs A B _ w).mp read)
  · intro g belongs
    obtain ⟨h, old, rfl⟩ := List.mem_map.mp belongs
    rw [orientAnd_arity]
    exact model.2.2 h old
  · intro j isOr
    exact (atGate j).trans (orientAnd_or A B _ isOr)
  · intro j index isAnd
    have oldAnd : (gateAt C j).op = .and := (op j).symm.trans isAnd
    by_cases ready : ∃ a b, (gateAt C j).inputs = [a, b] ∧ a ∈ B ∧ b ∈ A
    · simp only [atGate, orientAnd, oldAnd, ready, not_true_eq_false, and_false, ite_false]
    · obtain ⟨a, b, pins, first | already⟩ := cross j (size ▸ index) oldAnd
      · refine ⟨b, a, ?_, first.2, first.1⟩
        have reversed : orientAnd A B (gateAt C j) =
            { gateAt C j with inputs := (gateAt C j).inputs.reverse } := by
          unfold orientAnd
          exact ite_eq_left ⟨oldAnd, ready⟩
        simp [atGate, reversed, pins]
      · exact (ready ⟨a, b, pins, already⟩).elim
