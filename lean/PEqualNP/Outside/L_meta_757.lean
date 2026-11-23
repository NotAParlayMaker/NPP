import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L104
import PEqualNP.MetaComplexity.L105

namespace PEqualNP.Outside.L_meta_757_aux

def A (i j : Fin 6) : Bool :=
  (i.val == 0 && (j.val == 1 || j.val == 2)) || (j.val == 0 && (i.val == 1 || i.val == 2)) ||
  (i.val == 3 && (j.val == 4 || j.val == 5)) || (j.val == 3 && (i.val == 4 || i.val == 5))

def G : SimpleGraph (Fin 6) where
  Adj i j := A i j = true
  symm := ⟨by decide⟩
  loopless := ⟨by decide⟩

instance : DecidableRel G.Adj := fun i j => inferInstanceAs (Decidable (A i j = true))

def p : Fin 6 → Fin 6 := ![1, 0, 2, 4, 3, 5]

def pe : Fin 6 ↪ Fin 6 := ⟨p, by decide⟩

theorem hle : G ≤ (SimpleGraph.pathGraph 6).comap pe := by
  intro u v h
  rw [SimpleGraph.comap_adj, SimpleGraph.pathGraph_adj]
  fin_cases u <;> fin_cases v <;> simp_all [G, A, pe, p]

theorem hacyc : G.IsAcyclic :=
  ((SimpleGraph.isAcyclic_pathGraph 6).of_comap pe).anti hle

theorem hcard : G.edgeFinset.card = 4 := by decide

theorem hf : (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4) || (x 3 && x 5)) =
    (fun x : Fin 6 → Bool => decide (∃ i j : Fin 6, G.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  revert x
  decide

theorem hcov : ∀ T : Finset (Fin 6), (∀ i j : Fin 6, G.Adj i j → i ∈ T ∨ j ∈ T) → 2 ≤ T.card := by
  intro T hT
  rcases hT 0 1 (by decide) with h | h <;> rcases hT 3 4 (by decide) with h' | h' <;>
    exact Finset.one_lt_card.mpr ⟨_, h, _, h', by decide⟩

theorem hcov2 : ∀ i j : Fin 6, G.Adj i j → i ∈ ({0, 3} : Finset (Fin 6)) ∨ j ∈ ({0, 3} : Finset (Fin 6)) := by
  decide

end PEqualNP.Outside.L_meta_757_aux

open PEqualNP.Outside.L_meta_757_aux in
theorem PEqualNP.Outside.L_meta_757 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4) || (x 3 && x 5)) s ↔ 5 ≤ s := by
  intro s
  rw [hf]
  constructor
  · intro h
    have := PEqualNP.MetaComplexity.L104 6 2 s G hacyc ⟨0, 1, by decide⟩ hcov h
    rw [hcard] at this
    omega
  · intro h
    obtain ⟨C, h1, h2, h3⟩ := PEqualNP.MetaComplexity.L105 6 G {0, 3} ⟨0, 1, by decide⟩ hcov2
    rw [hcard] at h2
    exact ⟨C, h1, by simp at h2; omega, h3⟩
