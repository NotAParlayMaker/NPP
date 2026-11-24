import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.Helpers.LowerPart

-- Zeroing the dirty AND. Every read of the dirty AND `g` becomes the constant false and `g` is
-- dropped; `FoldProg.redirect_lt` folds the result into a smaller `IsAO2` circuit. Wherever `F` is
-- false it asks for a super-solution of the rewired gate equations that is false at the output:
-- the old gate values, since zeroing only lowers a source. At every edge it asks for a sub-solution
-- that is true at the output: the old values, switched off on the OR-closure of `g` where `g` is
-- true. The last hypothesis (`Blocks`) keeps every true AND off that closure there (`free_opnd`).

namespace PEqualNP.Outside.L_meta_4747

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.MetaComplexity.FoldProg PEqualNP.MetaComplexity.LowerPart PEqualNP.TopForm
  PEqualNP.CleanedNonEdge
open PEqualNP.SplitCount (unitInput)
open PEqualNP.EdgeOwnership (gateVal pairInput)

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} {g : ℕ}

-- The step's last hypothesis: an AND with one operand reaching `g` through ORs and the other
-- holding the vertex `z` keeps `g` false on the edge `uz`.
def Blocks (n : ℕ) (G : SimpleGraph (Fin n)) (C : Circuit) (g : ℕ) : Prop :=
  ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → ∀ u z : Fin n, G.Adj u z →
    (OrReaches n C (opnd C k 0) g ∧ wireVal n C (opnd C k 1) (unitInput z) = true) ∨
    (OrReaches n C (opnd C k 1) g ∧ wireVal n C (opnd C k 0) (unitInput z) = true) →
    gateVal n C g (pairInput u z) = false

-- The new source of operand `b` of gate `k`: the old one, except that a read of `g` is false.
def zeroSrc (n : ℕ) (C : Circuit) (g k : ℕ) (b : Fin 2) : Src n ℕ :=
  if opnd C k b = n + g then none else srcOf n (opnd C k b)

-- Zeroing only lowers a source.
theorem zeroSrc_le (C : Circuit) (g k : ℕ) (b : Fin 2) (x : Fin n → Bool)
    (h : srcAt x (fun j => gateVal n C j x) (zeroSrc n C g k b) = true) :
    wireVal n C (opnd C k b) x = true := by
  unfold zeroSrc at h
  split_ifs at h
  · simp [srcAt] at h
  · rwa [srcAt_srcOf] at h

-- The cut value of wire `w` at `x`: its value, switched off where `g` is true and `w` reaches `g`
-- through ORs.
def cutVal (n : ℕ) (C : Circuit) (g : ℕ) (x : Fin n → Bool) (w : ℕ) : Bool :=
  wireVal n C w x && !(gateVal n C g x && decide (OrReaches n C w g))

-- Read through the new sources, the cut values of the gates give the cut values of the operands.
theorem srcAt_cut (C : Circuit) (g : ℕ) (x : Fin n → Bool) (w : ℕ) :
    srcAt x (fun j => cutVal n C g x (n + j)) (srcOf n w) = cutVal n C g x w := by
  unfold srcOf
  split_ifs with hw
  · simp [srcAt, cutVal, wireVal_lt C w hw, reach_input C w g hw]
  · show cutVal n C g x (n + (w - n)) = _
    rw [show n + (w - n) = w by omega]

theorem zeroSrc_cut (hC : IsAO2 n C) (hg : g < C.gates.length) (x : Fin n → Bool) (k : ℕ)
    (b : Fin 2) : srcAt x (fun j => cutVal n C g x (n + j)) (zeroSrc n C g k b) =
      cutVal n C g x (opnd C k b) := by
  unfold zeroSrc
  split_ifs with h
  · rw [h]
    show false = (gateVal n C g x && _)
    simp [(reach_gate C hC g g hg).2 (Or.inl rfl)]
  · exact srcAt_cut C g x _

-- Where `g` is true at an edge, no operand of a true AND reaches `g`: the other operand misses
-- `g`, so it holds an endpoint of the edge, and `Blocks` makes `g` false on that edge.
theorem free_opnd (H : OneDirty G C g) (hz : Blocks n G C g) {p q : Fin n} (hpq : G.Adj p q)
    (hgx : gateVal n C g (pairInput p q) = true) (k : ℕ) (hk : k < C.gates.length)
    (ho : (gateAt C k).op = GateOp.and) (hkx : gateVal n C k (pairInput p q) = true) (b : Fin 2) :
    ¬ OrReaches n C (opnd C k b) g := by
  obtain ⟨h0, h1⟩ := (val_and C H.ao k hk ho _).1 hkx
  have key : ∀ c, wireVal n C (opnd C k c) (pairInput p q) = true →
      ¬ OrReaches n C (opnd C k c) g → ∃ u y, G.Adj u y ∧
        wireVal n C (opnd C k c) (unitInput y) = true ∧ gateVal n C g (pairInput u y) = true := by
    intro c hx hc
    obtain ⟨y, hy, hyc⟩ := (pure_val H k hk ho c hc _).1 hx
    simp only [pairInput, decide_eq_true_eq] at hy
    rcases hy with rfl | rfl
    · refine ⟨q, y, hpq.symm, hyc, ?_⟩
      rwa [show pairInput q y = pairInput y q from funext fun _ => by simp [pairInput, or_comm]]
    · exact ⟨p, y, hpq, hyc, hgx⟩
  intro hr
  fin_cases b
  · obtain ⟨u, y, huy, hy, hgy⟩ := key 1 h1 fun h => not_both H k hk ho ⟨hr, h⟩
    simp [hz k hk ho u y huy (Or.inl ⟨hr, hy⟩)] at hgy
  · obtain ⟨u, y, huy, hy, hgy⟩ := key 0 h0 fun h => not_both H k hk ho ⟨h, hr⟩
    simp [hz k hk ho u y huy (Or.inr ⟨hr, hy⟩)] at hgy

-- The step: drop `g`, zero its reads, fold.
theorem shrink (H : OneDirty G C g) (hz : Blocks n G C g) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size < C.size ∧ circuitFun n D = graphFun G ∅ := by
  have hC := H.ao
  obtain ⟨o, hol, hout, hob⟩ := out_gate H
  have hK : ∀ k ∈ (Finset.range C.gates.length).erase g, k < C.gates.length :=
    fun k hk => Finset.mem_range.1 (Finset.mem_of_mem_erase hk)
  -- the output does not reach `g`, else `g` would be below `F`
  have hreach : ¬ OrReaches n C C.output g := fun h => H.dirty fun x hx => by
    rw [← H.comp]
    exact (reach_le C hC g _ (by omega) h).2 x hx
  refine redirect_lt G C _ hK (zeroSrc n C g) ?_ (srcOf n C.output) ?_
    (adj_of_AO G C hC H.comp (by omega)) ?_ ?_ ⟨g, H.hg, Or.inl (Finset.notMem_erase g _)⟩
  -- the kept gates read earlier kept gates, and the output is a kept gate
  · intro k hk b j h
    unfold zeroSrc at h
    split_ifs at h
    have := srcOf_inr _ j h
    have := opnd_lt C hC k (hK k hk) b
    have := hK k hk
    simp only [Finset.mem_erase, Finset.mem_range]
    omega
  · intro j h
    have := srcOf_inr _ j h
    have : o ≠ g := fun e => H.dirty (e ▸ hob)
    simp only [Finset.mem_erase, Finset.mem_range]
    omega
  -- off `F`: the old values
  · intro x hx
    refine ⟨fun j => gateVal n C j x,
      super_of_le C hC _ hK _ x fun k _ b => zeroSrc_le C g k b x, ?_⟩
    rw [srcAt_srcOf, ← hx, ← H.comp]
    rfl
  -- at an edge: the cut values
  · intro p q hpq
    set x := pairInput p q
    refine ⟨fun j => cutVal n C g x (n + j), fun k hk hu => ?_, ?_⟩
    · have hk' := hK k hk
      simp only [cutVal, Bool.and_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff,
        decide_eq_false_iff_not] at hu
      -- where `g` is true no operand of `k` reaches `g`: an OR `k` would reach it; an AND by
      -- `free_opnd`
      have hfree : ∀ b, gateVal n C g x = true → ¬ OrReaches n C (opnd C k b) g := by
        intro b hgx hr
        rcases LeafBound.ao_op hC hk' with ho | ho
        · exact free_opnd H hz hpq hgx k hk' ho hu.1 b hr
        · exact hu.2.resolve_left (by simp [hgx])
            ((reach_gate C hC k g hk').2 (Or.inr ⟨ho, b, hr⟩))
      have hval : ∀ b, cutVal n C g x (opnd C k b) = wireVal n C (opnd C k b) x := by
        intro b
        cases hgx : gateVal n C g x <;> simp [cutVal, hgx, hfree b]
      rw [zeroSrc_cut hC H.hg, zeroSrc_cut hC H.hg, hval, hval]
      exact (gate_eq C hC k hk' x).symm.trans hu.1
    · have hx : wireVal n C C.output x = true := by
        show circuitFun n C x = true
        rw [H.comp, graphFun_empty]
        exact ⟨p, q, hpq, by simp [x, pairInput], by simp [x, pairInput]⟩
      rw [srcAt_cut]
      simp [cutVal, hx, hreach]

end PEqualNP.Outside.L_meta_4747

theorem PEqualNP.Outside.L_meta_4747 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin n → Bool) (g : ℕ), (∀ u v : Fin n, G.Adj u v → s u ≠ s v) → PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C → PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ → PEqualNP.Core.IsLiftFixedPoint G C → (∀ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ t ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs, ¬ (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨C.gates, t⟩ (List.ofFn x) = true → PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = true)) → (∀ k < C.gates.length, PEqualNP.Core.InOutputCone n C k) → g < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = PEqualNP.CircuitLowerBounds.GateOp.and → ¬ PEqualNP.TopForm.BelowF G C g → (∀ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and → k ≠ g → PEqualNP.TopForm.BelowF G C k) → (∀ w : Fin n, PEqualNP.EdgeOwnership.gateVal n C g (PEqualNP.SplitCount.unitInput w) = false) → (∀ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ u z : Fin n, G.Adj u z → (PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C k 0) g ∧ PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C k 1) (PEqualNP.SplitCount.unitInput z) = true) ∨ (PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C k 1) g ∧ PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C k 0) (PEqualNP.SplitCount.unitInput z) = true) → PEqualNP.EdgeOwnership.gateVal n C g (PEqualNP.EdgeOwnership.pairInput u z) = false) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 n D ∧ D.size < C.size ∧ PEqualNP.MetaComplexity.circuitFun n D = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ := by
  intro n G _ C _ g _ _ hC hF hlift hand hcone hg hgand hdirty hothers _ hz
  exact PEqualNP.Outside.L_meta_4747.shrink ⟨hC, hF, hlift, hand, hcone, hg, hgand, hdirty, hothers⟩ hz
