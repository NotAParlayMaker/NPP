import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L104
import PEqualNP.MetaComplexity.L105

namespace PEqualNP.Outside.L_meta_748_aux

open PEqualNP.MetaComplexity

def starFun (n : ℕ) (x : Fin (n+2) → Bool) : Bool :=
  decide (∃ i j : Fin (n+2), (SimpleGraph.starGraph 0).Adj i j ∧ x i = true ∧ x j = true)

theorem star_exact (n s : ℕ) : HasCircuitSize (n+2) (starFun n) s ↔ n+1 ≤ s := by
  let G : SimpleGraph (Fin (n+2)) := SimpleGraph.starGraph 0
  have hedge : ∃ i j : Fin (n+2), G.Adj i j := by
    refine ⟨⟨0, by omega⟩, ⟨1, by omega⟩, ?_⟩
    simp [G, SimpleGraph.starGraph_adj]
  have hcard : G.edgeFinset.card = n+1 := by
    have h := (SimpleGraph.isTree_starGraph (0 : Fin (n+2))).card_edgeFinset
    simp only [Fintype.card_fin] at h
    change G.edgeFinset.card + 1 = n+2 at h
    omega
  have hcover : ∀ a b : Fin (n+2), G.Adj a b → a ∈ ({0} : Finset _) ∨ b ∈ ({0} : Finset _) := by
    intro a b h
    simpa only [Finset.mem_singleton] using ((SimpleGraph.starGraph_adj.mp h).2)
  have hmin : ∀ T : Finset (Fin (n+2)), (∀ a b, G.Adj a b → a ∈ T ∨ b ∈ T) → 1 ≤ T.card := by
    intro T h
    obtain ⟨a,b,hab⟩ := hedge
    apply Finset.one_le_card.mpr
    rcases h a b hab with ha | hb
    · exact ⟨a,ha⟩
    · exact ⟨b,hb⟩
  constructor
  · intro h
    have hh := L104 (n+2) 1 s G (SimpleGraph.isAcyclic_starGraph 0) hedge hmin h
    rw [hcard] at hh
    omega
  · intro hs
    have hu := L105 (n+2) G {0} hedge hcover
    have hu' : HasCircuitSize (n+2) (starFun n) (n+1) := by
      unfold starFun
      simpa only [hcard, Finset.card_singleton, Nat.add_sub_cancel, G] using hu
    obtain ⟨C,hC,hsize,heval⟩ := hu'
    exact ⟨C,hC,hsize.trans hs,heval⟩

end PEqualNP.Outside.L_meta_748_aux

theorem PEqualNP.Outside.L_meta_748 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5)) s ↔ 5 ≤ s := by
  have hf : ∀ x : Fin 6 → Bool, (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5)) x = PEqualNP.Outside.L_meta_748_aux.starFun 4 x := by decide +kernel
  rw [funext hf]
  exact PEqualNP.Outside.L_meta_748_aux.star_exact 4
