import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L104
import PEqualNP.MetaComplexity.L105

namespace PEqualNP.Outside.L_meta_760_aux

def G : SimpleGraph (Fin 6) where
  Adj i j := i ≠ j ∧ i.val / 2 = j.val / 2
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance : DecidableRel G.Adj := fun i j => inferInstanceAs (Decidable (i ≠ j ∧ i.val / 2 = j.val / 2))

lemma hle : G ≤ SimpleGraph.pathGraph 6 := by
  intro a b h
  rw [SimpleGraph.pathGraph_adj]
  revert a b
  decide

lemma hacyc : G.IsAcyclic := (SimpleGraph.isAcyclic_pathGraph 6).anti hle

lemma hcard : G.edgeFinset.card = 3 := by decide

lemma hcover : ∀ T : Finset (Fin 6), (∀ i j : Fin 6, G.Adj i j → i ∈ T ∨ j ∈ T) → 3 ≤ T.card := by
  decide

lemma hf : (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 4 && x 5)) =
    (fun x : Fin 6 → Bool => decide (∃ i j : Fin 6, G.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  revert x
  decide

end PEqualNP.Outside.L_meta_760_aux

open PEqualNP.Outside.L_meta_760_aux in
theorem PEqualNP.Outside.L_meta_760 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 4 && x 5)) s ↔ 5 ≤ s := by
  intro s
  rw [hf]
  constructor
  · intro h
    have := PEqualNP.MetaComplexity.L104 6 3 s G hacyc ⟨0, 1, by decide⟩ hcover h
    rw [hcard] at this
    omega
  · intro hs
    have h5 := PEqualNP.MetaComplexity.L105 6 G {0, 2, 4} ⟨0, 1, by decide⟩ (by decide)
    rw [hcard] at h5
    obtain ⟨C, h1, h2, h3⟩ := h5
    refine ⟨C, h1, ?_, h3⟩
    have : ({0, 2, 4} : Finset (Fin 6)).card = 3 := by decide
    omega
