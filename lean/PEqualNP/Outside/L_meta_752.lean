import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L104
import PEqualNP.MetaComplexity.L105

namespace PEqualNP.Outside.L_meta_752_aux
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

def G : SimpleGraph (Fin 4) where
  Adj u v := (u=0 ∧ v=1) ∨ (u=1 ∧ v=0) ∨ (u=2 ∧ v=3) ∨ (u=3 ∧ v=2)
  symm := ⟨by intro u v h; tauto⟩
  loopless := ⟨by intro u h; fin_cases u <;> simp_all⟩

instance : DecidableRel G.Adj := by
  intro u v
  unfold G
  infer_instance

theorem edges : G.edgeFinset.card = 2 := by decide +kernel

theorem acyclic : G.IsAcyclic := by
  intro v c hc
  have hlow := hc.three_le_length
  have hupp := hc.isTrail.length_le_card_edgeFinset
  rw [edges] at hupp
  omega

theorem cover_lower : ∀ T : Finset (Fin 4),
    (∀ i j : Fin 4, G.Adj i j → i∈T ∨ j∈T) → 2 ≤ T.card := by decide +kernel

theorem semantics :
    (fun x : Fin 4 → Bool => decide (∃ i j : Fin 4, G.Adj i j ∧ x i=true ∧ x j=true)) =
    (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 2 && x 3)) := by
  funext x
  revert x
  decide +kernel

theorem exact_size (s : ℕ) :
    HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 2 && x 3)) s ↔ 3 ≤ s := by
  constructor
  · intro h
    have he : HasCircuitSize 4 (fun x : Fin 4 → Bool =>
        decide (∃ i j : Fin 4, G.Adj i j ∧ x i=true ∧ x j=true)) s := by
      rw [semantics]
      exact h
    have hb := PEqualNP.MetaComplexity.L104 4 2 s G acyclic ⟨0,1,by decide⟩ cover_lower he
    rw [edges] at hb
    omega
  · intro hs
    have h := PEqualNP.MetaComplexity.L105 4 G ({0,2} : Finset (Fin 4))
      ⟨0,1,by decide⟩ (by decide +kernel)
    rw [edges,semantics] at h
    have h3 : HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 2 && x 3)) 3 := by
      simpa using h
    obtain ⟨C,hC,hsize,hev⟩ := h3
    exact ⟨C,hC,hsize.trans hs,hev⟩

end PEqualNP.Outside.L_meta_752_aux

theorem PEqualNP.Outside.L_meta_752 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 4
      (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 2 && x 3)) s ↔ 3 ≤ s :=
  PEqualNP.Outside.L_meta_752_aux.exact_size
