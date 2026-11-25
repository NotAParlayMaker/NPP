import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_5697 : ∀ (x1 : SimpleGraph (Fin (26 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.junk x1 x3 = ∅ → ∀ x5 < x3.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x5).op = PEqualNP.CircuitLowerBounds.GateOp.and → PEqualNP.TopForm.BelowF x1 x3 x5 := by
  intro G _ C hj j hlt hop
  by_contra hb
  unfold PEqualNP.TopForm.BelowF at hb
  push_neg at hb
  obtain ⟨x, hx1, hx2⟩ := hb
  have hm : j ∈ PEqualNP.TopForm.junk G C := by
    simp only [PEqualNP.TopForm.junk, PEqualNP.TopForm.gatesWhere, Finset.mem_filter, Finset.mem_range]
    exact ⟨hlt, hop, hlt, x, hx1, by simpa using hx2⟩
  rw [hj] at hm
  exact absurd hm (Finset.notMem_empty _)
