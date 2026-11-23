import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_632_aux

open PEqualNP.AndCount

def nbr : Fin 11 → ℕ := ![912, 1312, 1600, 1152, 1025, 258, 516, 521, 35, 197, 30]

def adjB (a b : Fin 11) : Bool := (nbr a).testBit b.val

lemma adjB_symm : ∀ a b : Fin 11, adjB a b = true → adjB b a = true := by decide +kernel

lemma adjB_irrefl : ∀ a : Fin 11, ¬ adjB a a = true := by decide +kernel

def G : SimpleGraph (Fin 11) where
  Adj a b := adjB a b = true
  symm := ⟨fun a b h => adjB_symm a b h⟩
  loopless := ⟨fun a h => adjB_irrefl a h⟩

def C : AndCountCircuit 11 where
  size := 6
  leftVars := ![{4}, {5}, {8, 10}, {9}, {7, 10}, {6}]
  leftGates := ![∅, {0}, ∅, {2}, {2, 3}, {2, 4}]
  rightVars := ![{0, 10}, {1, 8}, {0, 1}, {2, 7}, {3}, {2, 9}]
  rightGates := ![∅, ∅, {1}, {1}, {3}, {4}]
  outVars := ∅
  outGates := {0, 1, 4, 5}

lemma c4free : ∀ a b c d : Fin 11, a ≠ c → b ≠ d → adjB a b = true → adjB b c = true →
    adjB c d = true → ¬ adjB d a = true := by decide +kernel

lemma wf : C.WellFormed := by
  unfold AndCountCircuit.WellFormed
  decide +kernel

set_option maxRecDepth 100000 in
lemma correct : ∀ I : Finset (Fin 11), (∀ v ∈ I, ∀ w ∈ I, ¬ adjB v w = true) →
    (∀ u, u ∉ I → ∃ v ∈ I, adjB u v = true) →
    C.eval I = false ∧ ∀ u, u ∉ I → C.eval (insert u I) = true := by decide +kernel

set_option maxRecDepth 100000 in
lemma cover_ge : ∀ T : Finset (Fin 11), (∀ v w, adjB v w = true → v ∈ T ∨ w ∈ T) → 7 ≤ T.card := by
  decide +kernel

end PEqualNP.Outside.L_meta_632_aux

theorem PEqualNP.Outside.L_meta_632 : ¬ (∀ (n : ℕ) (G : SimpleGraph (Fin n)),
    (∀ a b c d : Fin n, a ≠ c → b ≠ d → G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a) →
    (∃ C : PEqualNP.AndCount.AndCountCircuit n, C.WellFormed ∧
      (∀ I : Finset (Fin n), (∀ v ∈ I, ∀ w ∈ I, ¬ G.Adj v w) → (∀ u, u ∉ I → ∃ v ∈ I, G.Adj u v) →
        C.eval I = false ∧ ∀ u, u ∉ I → C.eval (insert u I) = true) ∧
      ∀ T : Finset (Fin n), (∀ v w, G.Adj v w → v ∈ T ∨ w ∈ T) → C.size ≤ T.card) ∧
    (∀ C : PEqualNP.AndCount.AndCountCircuit n, C.WellFormed →
      (∀ I : Finset (Fin n), (∀ v ∈ I, ∀ w ∈ I, ¬ G.Adj v w) → (∀ u, u ∉ I → ∃ v ∈ I, G.Adj u v) →
        C.eval I = false ∧ ∀ u, u ∉ I → C.eval (insert u I) = true) →
      ∃ T : Finset (Fin n), (∀ v w, G.Adj v w → v ∈ T ∨ w ∈ T) ∧ T.card ≤ C.size)) := by
  intro h
  obtain ⟨T, hT, hc⟩ := (h 11 PEqualNP.Outside.L_meta_632_aux.G PEqualNP.Outside.L_meta_632_aux.c4free).2
    PEqualNP.Outside.L_meta_632_aux.C PEqualNP.Outside.L_meta_632_aux.wf
    PEqualNP.Outside.L_meta_632_aux.correct
  have h7 : 7 ≤ T.card := PEqualNP.Outside.L_meta_632_aux.cover_ge T hT
  have hs : PEqualNP.Outside.L_meta_632_aux.C.size = 6 := rfl
  omega
