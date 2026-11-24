import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.Helpers.LowerPart
import PEqualNP.MetaComplexity.Helpers.LowerPart2

-- Point every read of the dirty AND g at its operand a (all of whose variables are adjacent to m)
-- and delete g. Edges: every wire only goes up, so the old values are a sub-solution.
-- Non-edges: the old values with a ORed onto every wire that reaches g through ORs are a
-- super-solution that is false at the output.

namespace PEqualNP.Outside.L4742

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.MetaComplexity.FoldProg
open PEqualNP.MetaComplexity.LowerPart
open PEqualNP.TopForm
open PEqualNP.CleanedNonEdge
open PEqualNP.SplitCount (unitInput)
open PEqualNP.EdgeOwnership (gateVal pairInput)


theorem main {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} {g : ℕ} (m : Fin n)
    (H : OneDirty G C g)
    (hpz : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → ∀ z : Fin n, PZ C g k z → z = m)
    (c : Fin 2) (hc : ∀ y : Fin n, wireVal n C (opnd C g c) (unitInput y) = true → G.Adj y m) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size < C.size ∧ circuitFun n D = graphFun G ∅ := by
  classical
  have hAO := H.ao
  have hg := H.hg
  obtain ⟨o, hol, hoo, hob⟩ := out_gate H
  set a := opnd C g c with ha_def
  have hal : a < n + g := opnd_lt C hAO g hg c
  let r : ℕ → ℕ := fun u => if u = n + g then a else u
  have hrk : ∀ u, r u ≠ n + g ∧ r u ≤ u := by
    intro u
    simp only [r]
    split_ifs with h <;> omega
  have hog : o ≠ g := by
    rintro rfl
    exact H.dirty hob
  have hro : r C.output = C.output := by
    simp only [r]
    rw [ite_eq_right (by omega)]
  -- the output does not reach g through ORs
  have hnro : ¬ OrReaches n C C.output g := by
    intro h
    refine H.dirty fun x hx => hob x ?_
    have := (reach_le C hAO g _ (by omega) h).2 x hx
    rw [hoo] at this
    exact this
  -- g is below a
  have hga : ∀ x, gateVal n C g x = true → wireVal n C a x = true := by
    intro x hx
    have := (val_and' C hAO g hg H.gand x c).1 hx
    exact this.1
  refine redirect_lt G C ((Finset.range C.gates.length).erase g) ?_
    (fun j b => srcOf n (r (opnd C j b))) ?_ (srcOf n (r C.output)) ?_
    (adj_of_AO G C hAO H.comp (by omega)) ?_ ?_ ⟨g, hg, Or.inl (by simp)⟩
  · intro j hj
    exact Finset.mem_range.1 (Finset.mem_erase.1 hj).2
  · intro j hj b i hi
    have hjl := Finset.mem_range.1 (Finset.mem_erase.1 hj).2
    have hlt := opnd_lt C hAO j hjl b
    have hi' := srcOf_inr _ _ hi
    have := hrk (opnd C j b)
    exact ⟨Finset.mem_erase.2 ⟨by omega, Finset.mem_range.2 (by omega)⟩, by omega⟩
  · intro i hi
    have hi' := srcOf_inr _ _ hi
    have := hrk C.output
    exact Finset.mem_erase.2 ⟨by omega, Finset.mem_range.2 (by omega)⟩
  · intro x hx
    -- the super-solution
    let U : ℕ → Bool := fun w => wireVal n C w x || (decide (OrReaches n C w g) && wireVal n C a x)
    let u : ℕ → Bool := fun j => U (n + j)
    have hU : ∀ w, srcAt x u (srcOf n w) = U w := by
      intro w
      unfold srcOf
      split_ifs with hw
      · show x ⟨w, hw⟩ = U w
        simp only [U, wireVal_lt C w hw, reach_input C w g hw, decide_false, Bool.false_and,
          Bool.or_false]
      · show U (n + (w - n)) = U w
        rw [show n + (w - n) = w by omega]
    have hUa : U a = wireVal n C a x := by
      have : ¬ OrReaches n C a g := fun h => by
        have := (reach_le C hAO g a (by omega) h).1
        omega
      simp [U, this]
    -- value of a redirected source
    have hUr : ∀ w, U (r w) = true → wireVal n C w x = true ∨ (OrReaches n C w g ∧ wireVal n C a x = true) := by
      intro w h
      simp only [r] at h
      split_ifs at h with hw
      · rw [hUa] at h
        exact Or.inr ⟨by rw [hw]; exact reach_self C hAO g hg, h⟩
      · simp only [U, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
        exact h
    -- a and m together force F
    have ham : wireVal n C a x = true → x m = true → False := by
      intro h1 h2
      obtain ⟨y, hy, hyw⟩ := (opnd_val H c x).1 h1
      have hadj := hc y hyw
      have : graphFun G ∅ x = true :=
        (graphFun_empty G _).2 ⟨y, m, hadj, hy, h2⟩
      rw [hx] at this
      exact Bool.false_ne_true this
    refine ⟨u, ?_, ?_⟩
    · intro k hk hv
      have hkl := Finset.mem_range.1 (Finset.mem_erase.1 hk).2
      have hkg : k ≠ g := (Finset.mem_erase.1 hk).1
      simp only [progOf, hU] at hv
      show U (n + k) = true
      rcases LeafBound.ao_op hAO hkl with ho | ho
      · -- an AND other than g
        rw [ho] at hv
        simp only [isA, opv, ite_true, Bool.and_eq_true] at hv
        obtain ⟨h0, h1⟩ := hv
        have hand : ∀ b : Fin 2, (wireVal n C (opnd C k b) x = true ∨
            (OrReaches n C (opnd C k b) g ∧ wireVal n C a x = true)) := by
          intro b
          fin_cases b
          · exact hUr _ h0
          · exact hUr _ h1
        have hgood : wireVal n C (opnd C k 0) x = true ∧ wireVal n C (opnd C k 1) x = true := by
          by_contra hbad
          -- some operand only has the a-part
          obtain ⟨b, hbr, hba⟩ : ∃ b : Fin 2, OrReaches n C (opnd C k b) g ∧ wireVal n C a x = true := by
            rcases hand 0 with h | h
            · rcases hand 1 with h' | h'
              · exact absurd ⟨h, h'⟩ hbad
              · exact ⟨1, h'⟩
            · exact ⟨0, h⟩
          have hnr := not_both' H k hkl ho b hbr
          have hw' : wireVal n C (opnd C k (1 - b)) x = true := by
            rcases hand (1 - b) with h | h
            · exact h
            · exact absurd h.1 hnr
          obtain ⟨z, hz, hzw⟩ := (pure_val H k hkl ho (1 - b) hnr x).1 hw'
          have hzm := hpz k hkl ho z ((pz_iff C g k z).2 ⟨b, hbr, hzw⟩)
          subst hzm
          exact ham hba hz
        have : gateVal n C k x = true := (val_and C hAO k hkl ho x).2 hgood
        simp [U, show wireVal n C (n + k) x = gateVal n C k x from rfl, this]
      · -- an OR
        rw [ho] at hv
        simp only [isA, opv, Bool.false_eq_true, ite_false, Bool.or_eq_true] at hv
        have hb : ∃ b : Fin 2, U (r (opnd C k b)) = true := by
          rcases hv with h | h
          · exact ⟨0, h⟩
          · exact ⟨1, h⟩
        obtain ⟨b, hb⟩ := hb
        rcases hUr _ hb with h | ⟨h, ha⟩
        · have : gateVal n C k x = true := (val_or' C hAO k hkl ho x).2 ⟨b, h⟩
          simp [U, show wireVal n C (n + k) x = gateVal n C k x from rfl, this]
        · have : OrReaches n C (n + k) g := (reach_gate C hAO k g hkl).2 (Or.inr ⟨ho, b, h⟩)
          simp [U, this, ha]
    · rw [hU, hro]
      have hF : wireVal n C C.output x = false := by
        have : circuitFun n C x = false := by rw [H.comp]; exact hx
        exact this
      simp [U, hF, hnro]
  · intro p q hpq
    refine ⟨fun j => gateVal n C j (pairInput p q), ?_, ?_⟩
    · intro j hj h
      have hjl := Finset.mem_range.1 (Finset.mem_erase.1 hj).2
      simp only at h
      rw [gate_eq C hAO j hjl] at h
      simp only [progOf]
      rw [srcAt_srcOf, srcAt_srcOf]
      refine opv_mono _ _ _ _ _ ?_ ?_ h
      all_goals
        intro hw
        simp only [r]
        split_ifs with he
        · rw [he] at hw
          exact hga _ hw
        · exact hw
    · rw [srcAt_srcOf, hro]
      have : circuitFun n C (pairInput p q) = true := by
        rw [H.comp]
        exact (graphFun_empty G _).2 ⟨p, q, hpq, by simp [pairInput], by simp [pairInput]⟩
      exact this

end PEqualNP.Outside.L4742

theorem PEqualNP.Outside.L_meta_4742 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin n → Bool) (g : ℕ) (m : Fin n), (∀ u v : Fin n, G.Adj u v → s u ≠ s v) → PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C → PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ → PEqualNP.Core.IsLiftFixedPoint G C → (∀ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ t ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs, ¬ (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨C.gates, t⟩ (List.ofFn x) = true → PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = true)) → (∀ k < C.gates.length, PEqualNP.Core.InOutputCone n C k) → g < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = PEqualNP.CircuitLowerBounds.GateOp.and → ¬ PEqualNP.TopForm.BelowF G C g → (∀ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and → k ≠ g → PEqualNP.TopForm.BelowF G C k) → (∀ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ z : Fin n, (PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C k 0) g ∧ PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C k 1) (PEqualNP.SplitCount.unitInput z) = true) ∨ (PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C k 1) g ∧ PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C k 0) (PEqualNP.SplitCount.unitInput z) = true) → z = m) → ((∀ y : Fin n, PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C g 0) (PEqualNP.SplitCount.unitInput y) = true → G.Adj y m) ∨ (∀ y : Fin n, PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C g 1) (PEqualNP.SplitCount.unitInput y) = true → G.Adj y m)) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 n D ∧ D.size < C.size ∧ PEqualNP.MetaComplexity.circuitFun n D = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ := by
  intro n G _ C s g m _ _ hAO hF hL hAL hCo hg hgA hD hO hP hA
  have H : PEqualNP.MetaComplexity.LowerPart.OneDirty G C g := ⟨hAO, hF, hL, hAL, hCo, hg, hgA, hD, hO⟩
  rcases hA with hA | hA
  · exact PEqualNP.Outside.L4742.main m H (fun k hk ho z hz => hP k hk ho z hz) 0 hA
  · exact PEqualNP.Outside.L4742.main m H (fun k hk ho z hz => hP k hk ho z hz) 1 hA
