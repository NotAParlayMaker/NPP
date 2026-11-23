import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L104
import PEqualNP.MetaComplexity.L105

namespace PEqualNP.Outside.L_meta_763_aux

def e (i j : Fin 6) : Bool :=
  decide ((i.val = 0 ∧ j.val = 1) ∨ (i.val = 1 ∧ j.val = 0) ∨ (i.val = 0 ∧ j.val = 2) ∨
    (i.val = 2 ∧ j.val = 0) ∨ (i.val = 1 ∧ j.val = 3) ∨ (i.val = 3 ∧ j.val = 1) ∨
    (i.val = 4 ∧ j.val = 5) ∨ (i.val = 5 ∧ j.val = 4))

def G : SimpleGraph (Fin 6) where
  Adj i j := e i j = true
  symm := ⟨by decide⟩
  loopless := ⟨by decide⟩

instance instDecG : DecidableRel G.Adj := fun i j => inferInstanceAs (Decidable (e i j = true))

def m (i : Fin 6) : Fin 7 := ![1, 2, 0, 3, 5, 6] i

def hom : G →g SimpleGraph.pathGraph 7 where
  toFun := m
  map_rel' := by
    intro a b h
    rw [SimpleGraph.pathGraph_adj]
    revert a b
    decide

theorem acyc : G.IsAcyclic :=
  SimpleGraph.IsAcyclic.comap hom (by intro a b h; revert a b; decide) (SimpleGraph.isAcyclic_pathGraph 7)

theorem fun_eq : (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5)) =
    (fun x : Fin 6 → Bool => decide (∃ i j : Fin 6, G.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  revert x
  decide +kernel

theorem card_e : G.edgeFinset.card = 4 := by decide +kernel

theorem ex_e : ∃ i j : Fin 6, G.Adj i j := ⟨0, 1, by decide⟩

theorem cover_lb : ∀ T : Finset (Fin 6), (∀ i j : Fin 6, G.Adj i j → i ∈ T ∨ j ∈ T) → 3 ≤ T.card := by
  decide +kernel

theorem cover_ub : ∀ i j : Fin 6, G.Adj i j → i ∈ ({0, 1, 4} : Finset (Fin 6)) ∨ j ∈ ({0, 1, 4} : Finset (Fin 6)) := by
  decide +kernel

end PEqualNP.Outside.L_meta_763_aux

open PEqualNP.Outside.L_meta_763_aux in
theorem PEqualNP.Outside.L_meta_763 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5)) s ↔ 6 ≤ s := by
  intro s
  rw [fun_eq]
  constructor
  · intro h
    have := PEqualNP.MetaComplexity.L104 6 3 s G acyc ex_e cover_lb h
    rw [card_e] at this
    omega
  · intro hs
    obtain ⟨C, h1, h2, h3⟩ := PEqualNP.MetaComplexity.L105 6 G {0, 1, 4} ex_e cover_ub
    refine ⟨C, h1, ?_, h3⟩
    have hc : ({0, 1, 4} : Finset (Fin 6)).card = 3 := by decide
    rw [card_e, hc] at h2
    omega
