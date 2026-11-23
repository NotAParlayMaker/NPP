import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_632_aux

open PEqualNP.AndCount

abbrev V := Fin 11

def hood : V → ℕ := ![1536, 272, 1056, 192, 1282, 772, 1160, 584, 562, 417, 85]

abbrev adj (v w : V) := (hood v).testBit w.val = true

def graph : SimpleGraph V where
  Adj := adj
  symm := ⟨by decide +kernel⟩
  loopless := ⟨by decide +kernel⟩

def circuit : AndCountCircuit 11 where
  size := 6
  leftVars := ![{7, 10}, {2}, {0}, {8}, {4, 8}, {3}]
  leftGates := ![∅, ∅, ∅, {0}, ∅, ∅]
  rightVars := ![{6, 9}, {5, 10}, {9, 10}, {4, 5}, {1}, {6, 7}]
  rightGates := ![∅, {0}, ∅, ∅, {0}, ∅]
  outVars := ∅
  outGates := {1, 2, 3, 4, 5}

theorem wf : circuit.WellFormed := by
  unfold AndCountCircuit.WellFormed
  decide +kernel

set_option maxHeartbeats 4000000 in
theorem squareFree : ∀ a b c d : V, a ≠ c → b ≠ d →
    adj a b → adj b c → adj c d → ¬ adj d a := by decide +kernel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 16000 in
theorem boundary : ∀ I : Finset V, (∀ v ∈ I, ∀ w ∈ I, ¬ adj v w) →
    (∀ u, u ∉ I → ∃ v ∈ I, adj u v) →
    circuit.eval I = false ∧ ∀ u, u ∉ I → circuit.eval (insert u I) = true := by
  decide +kernel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 16000 in
theorem noCover : ∀ T : Finset V, T.card ≤ 6 → ¬ (∀ v w, adj v w → v ∈ T ∨ w ∈ T) := by
  decide +kernel

def seven : Finset V := {4, 5, 6, 7, 8, 9, 10}

theorem sevenCovers : seven.card = 7 ∧ ∀ v w, adj v w → v ∈ seven ∨ w ∈ seven := by
  decide +kernel

end PEqualNP.Outside.L_meta_632_aux

open PEqualNP.Outside.L_meta_632_aux in
theorem PEqualNP.Outside.L_meta_632 : ¬ (
∀ (n : ℕ) (G : SimpleGraph (Fin n)),
    (∀ a b c d : Fin n, a ≠ c → b ≠ d → G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a) →
    (∃ C : PEqualNP.AndCount.AndCountCircuit n, C.WellFormed ∧
      (∀ I : Finset (Fin n), (∀ v ∈ I, ∀ w ∈ I, ¬ G.Adj v w) → (∀ u, u ∉ I → ∃ v ∈ I, G.Adj u v) →
        C.eval I = false ∧ ∀ u, u ∉ I → C.eval (insert u I) = true) ∧
      ∀ T : Finset (Fin n), (∀ v w, G.Adj v w → v ∈ T ∨ w ∈ T) → C.size ≤ T.card) ∧
    (∀ C : PEqualNP.AndCount.AndCountCircuit n, C.WellFormed →
      (∀ I : Finset (Fin n), (∀ v ∈ I, ∀ w ∈ I, ¬ G.Adj v w) → (∀ u, u ∉ I → ∃ v ∈ I, G.Adj u v) →
        C.eval I = false ∧ ∀ u, u ∉ I → C.eval (insert u I) = true) →
      ∃ T : Finset (Fin n), (∀ v w, G.Adj v w → v ∈ T ∨ w ∈ T) ∧ T.card ≤ C.size)) := by
  intro asserted
  obtain ⟨T, hT, hs⟩ := (asserted 11 graph squareFree).2 circuit wf boundary
  exact noCover T hs hT
