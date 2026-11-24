import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.Core
open PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge

-- Empty junk is already clean. The one-junk paper removal and the
-- two-or-more shared-cone case are left as separate hypotheses.
theorem PEqualNP.Outside.R_meta_3754_1
    (hone : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : Circuit) (s : Fin n → Bool),
      (∀ u v : Fin n, G.Adj u v → s u ≠ s v) →
      NoFourCycle G → IsLeastAO G C → IsLiftFixedPoint G C →
      (junk G C).card = 1 →
      ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → BelowF G C k)
    (hmany : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : Circuit) (s : Fin n → Bool),
      (∀ u v : Fin n, G.Adj u v → s u ≠ s v) →
      NoFourCycle G → IsLeastAO G C → IsLiftFixedPoint G C →
      2 ≤ (junk G C).card →
      ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → BelowF G C k) :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin n → Bool),
  (∀ u v : Fin n, G.Adj u v → s u ≠ s v) → PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsLeastAO G C →
  PEqualNP.Core.IsLiftFixedPoint G C →
  ∀ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and →
    PEqualNP.TopForm.BelowF G C k := by
  intro n G _ C s hbi hC4 hleast hlift k hk hand
  have hmem : k ∈ junk G C ↔ IsDirtyAnd n G C k := by
    simp [junk, gatesWhere, Finset.mem_filter, Finset.mem_range, hk]
  have clean_of_empty (h0 : junk G C = ∅) : BelowF G C k := by
    have hn : ¬ IsDirtyAnd n G C k := by
      intro hd
      exact Finset.notMem_empty k (h0 ▸ hmem.mpr hd)
    have hnd : ¬ IsDirty n G C k := fun hd => hn ⟨hand, hd⟩
    intro x hx
    cases hFx : graphFun G ∅ x with
    | true => rfl
    | false => exact (hnd ⟨hk, x, hx, hFx⟩).elim
  rcases Nat.lt_trichotomy (junk G C).card 1 with hlt | heq | hgt
  · have h0 : junk G C = ∅ := by
      have : (junk G C).card = 0 := by omega
      exact Finset.card_eq_zero.mp this
    exact clean_of_empty h0
  · exact hone n G C s hbi hC4 hleast hlift heq k hk hand
  · have hge : 2 ≤ (junk G C).card := by omega
    exact hmany n G C s hbi hC4 hleast hlift hge k hk hand
