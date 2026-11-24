import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.R_meta_3136_1

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The edge function of the Petersen graph minus a vertex.
def edgeFun (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) ||
  (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)

def wiresOf (gs : List Gate) (x : Fin 9 → Bool) : List Bool :=
  (⟨gs, 0⟩ : Circuit).wires (List.ofFn x ++ [x 0 || x 3])

def pairNe (gs : List Gate) (a b : ℕ) : Prop :=
  ∃ x : Fin 9 → Bool,
    (wiresOf gs x).getD a false && (wiresOf gs x).getD b false ≠ edgeFun x

end PEqualNP.Outside.R_meta_3136_1

open PEqualNP.Outside.R_meta_3136_1
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_3136_1
    (hInputA : ∀ (gs : List Gate) (a b : ℕ), gs.length = 13 →
      FanInTwo (⟨gs, 0⟩ : Circuit) →
      gs.countP (fun g => g.op.eval [false]) ≤ 1 → a ≤ 24 → b ≤ 24 → a < 10 →
      pairNe gs a b)
    (hInputB : ∀ (gs : List Gate) (a b : ℕ), gs.length = 13 →
      FanInTwo (⟨gs, 0⟩ : Circuit) →
      gs.countP (fun g => g.op.eval [false]) ≤ 1 → a ≤ 24 → b ≤ 24 → b < 10 →
      pairNe gs a b)
    (hMonotone : ∀ (gs : List Gate) (a b : ℕ), gs.length = 13 →
      FanInTwo (⟨gs, 0⟩ : Circuit) →
      10 ≤ a → 10 ≤ b → (∀ g ∈ gs, g.op ≠ GateOp.not) →
      gs.countP (fun g => g.op.eval [false]) ≤ 1 → a ≤ 24 → b ≤ 24 →
      pairNe gs a b)
    (hNot : ∀ (gs : List Gate) (a b : ℕ), gs.length = 13 →
      FanInTwo (⟨gs, 0⟩ : Circuit) →
      10 ≤ a → 10 ≤ b → (∃ g ∈ gs, g.op = GateOp.not) →
      gs.countP (fun g => g.op.eval [false]) ≤ 1 → a ≤ 24 → b ≤ 24 →
      pairNe gs a b) :
    ∀ (gs : List Gate) (a b : ℕ), gs.length = 13 →
      FanInTwo (⟨gs, 0⟩ : Circuit) →
      gs.countP (fun g => g.op.eval [false]) ≤ 1 → a ≤ 24 → b ≤ 24 →
      pairNe gs a b := by
  intro gs a b hlen hfan hcount ha hb
  by_cases ha10 : a < 10
  · exact hInputA gs a b hlen hfan hcount ha hb ha10
  · have ha10' : 10 ≤ a := by omega
    by_cases hb10 : b < 10
    · exact hInputB gs a b hlen hfan hcount ha hb hb10
    · have hb10' : 10 ≤ b := by omega
      by_cases hnot : ∃ g ∈ gs, g.op = GateOp.not
      · exact hNot gs a b hlen hfan ha10' hb10' hnot hcount ha hb
      · exact hMonotone gs a b hlen hfan ha10' hb10'
          (fun g hg hgnot => hnot ⟨g, hg, hgnot⟩) hcount ha hb
