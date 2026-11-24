import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.Helpers.LowerPart

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.MetaComplexity.FoldProg PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.MetaComplexity.LowerPart
open PEqualNP.EdgeOwnership (gateVal pairInput)
open PEqualNP.SplitCount (unitInput)

theorem PEqualNP.Outside.L_meta_4742 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin n → Bool) (g : ℕ) (m : Fin n), (∀ u v : Fin n, G.Adj u v → s u ≠ s v) → PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C → PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ → PEqualNP.Core.IsLiftFixedPoint G C → (∀ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ t ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs, ¬ (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨C.gates, t⟩ (List.ofFn x) = true → PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = true)) → (∀ k < C.gates.length, PEqualNP.Core.InOutputCone n C k) → g < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = PEqualNP.CircuitLowerBounds.GateOp.and → ¬ PEqualNP.TopForm.BelowF G C g → (∀ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and → k ≠ g → PEqualNP.TopForm.BelowF G C k) → (∀ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ z : Fin n, (PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C k 0) g ∧ PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C k 1) (PEqualNP.SplitCount.unitInput z) = true) ∨ (PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C k 1) g ∧ PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C k 0) (PEqualNP.SplitCount.unitInput z) = true) → z = m) → ((∀ y : Fin n, PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C g 0) (PEqualNP.SplitCount.unitInput y) = true → G.Adj y m) ∨ (∀ y : Fin n, PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C g 1) (PEqualNP.SplitCount.unitInput y) = true → G.Adj y m)) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 n D ∧ D.size < C.size ∧ PEqualNP.MetaComplexity.circuitFun n D = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅
 := by
  intro n G _ C s g m _ _ hao hcomp hlift handLow hcone hg hgand hdirty hothers hreach ha
  have H : OneDirty G C g := ⟨hao, hcomp, hlift, handLow, hcone, hg, hgand, hdirty, hothers⟩
  obtain ⟨b0, hb0⟩ : ∃ b0 : Fin 2, ∀ y : Fin n,
      wireVal n C (opnd C g b0) (unitInput y) = true → G.Adj y m := by
    rcases ha with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  have hA : opnd C g b0 < n + g := opnd_lt C hao g hg b0
  have hAlow : Low G C (opnd C g b0) := low_opnd H g hg b0 (Or.inr hgand)
  obtain ⟨o', ho'lt, hout, hob⟩ := out_gate H
  have ho'g : o' ≠ g := fun h => hdirty (h ▸ hob)
  have V1 : ∀ (u : ℕ → Bool) (x : Fin n → Bool) (w : ℕ), w < n →
      srcAt x u (srcOf n w) = wireVal n C w x := by
    intro u x w hw
    rw [wireVal_lt C w hw x]
    simp [srcOf, hw, srcAt]
  have V2 : ∀ (u : ℕ → Bool) (x : Fin n → Bool) (j : ℕ), srcAt x u (srcOf n (n + j)) = u j := by
    intro u x j
    simp [srcOf, srcAt]
  obtain ⟨K, hKdef⟩ : ∃ K : Finset ℕ, K = (Finset.range C.gates.length).erase g := ⟨_, rfl⟩
  have hK : ∀ k ∈ K, k < C.gates.length := by
    intro k hk; rw [hKdef] at hk; exact Finset.mem_range.1 (Finset.mem_of_mem_erase hk)
  have hKg : ∀ k ∈ K, k ≠ g := by
    intro k hk; rw [hKdef] at hk; exact Finset.ne_of_mem_erase hk
  have memK : ∀ j, j < C.gates.length → j ≠ g → j ∈ K := by
    intro j h1 h2; rw [hKdef]; exact Finset.mem_erase.2 ⟨h2, Finset.mem_range.2 h1⟩
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℕ → Fin 2 → Src n ℕ, ∀ k b, ρ k b =
      if opnd C k b = n + g then srcOf n (opnd C g b0) else srcOf n (opnd C k b) :=
    ⟨_, fun _ _ => rfl⟩
  refine redirect_lt G C K hK ρ ?_ (srcOf n C.output) ?_ ?_ ?_ ?_ ⟨g, hg, Or.inl fun h => hKg g h rfl⟩
  · intro k hk b j hj
    have hkl := hK k hk
    have hw := opnd_lt C hao k hkl b
    rw [hρ] at hj
    split_ifs at hj with he
    · have := srcOf_inr _ j hj
      exact ⟨memK j (by omega) (by omega), by omega⟩
    · have := srcOf_inr _ j hj
      exact ⟨memK j (by omega) (fun h => he (by omega)), by omega⟩
  · intro j hj
    have := srcOf_inr _ j hj
    have hj' : j = o' := by omega
    subst hj'
    exact memK _ ho'lt ho'g
  · exact adj_of_AO G C hao hcomp (by omega)
  · intro x hFx
    have hF : ¬ graphFun G ∅ x = true := by rw [hFx]; decide
    obtain ⟨u, hu⟩ : ∃ u : ℕ → Bool, ∀ j, u j = if BelowF G C j then false else
        (gateVal n C j x || (decide (OrReaches n C (n + j) g) && wireVal n C (opnd C g b0) x)) :=
      ⟨_, fun _ => rfl⟩
    have hW : ∀ w < n + C.gates.length, Low G C w → (srcAt x u (srcOf n w) = true ↔
        wireVal n C w x = true ∨ (OrReaches n C w g ∧ wireVal n C (opnd C g b0) x = true)) := by
      intro w hw hl
      by_cases hwn : w < n
      · rw [V1 u x w hwn]
        have := reach_input C w g hwn
        tauto
      · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
        have hnb : ¬ BelowF G C j := hl
        rw [V2 u x j, hu j, if_neg hnb]
        simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
        exact Iff.rfl
    refine ⟨u, ?_, ?_⟩
    · intro k hk hform
      have hkl := hK k hk
      have hkg := hKg k hk
      change opv (isA (gateAt C k).op) (srcAt x u (ρ k 0)) (srcAt x u (ρ k 1)) = true at hform
      have hv : ∀ b : Fin 2, Low G C (opnd C k b) → srcAt x u (ρ k b) = true →
          wireVal n C (opnd C k b) x = true ∨
            (OrReaches n C (opnd C k b) g ∧ wireVal n C (opnd C g b0) x = true) := by
        intro b hlb hb
        have hwb := opnd_lt C hao k hkl b
        rw [hρ] at hb
        split_ifs at hb with he
        · right
          refine ⟨?_, ?_⟩
          · rw [he]; exact (reach_gate C hao g g hg).2 (Or.inl rfl)
          · rcases (hW _ (by omega) hAlow).1 hb with h | ⟨h, _⟩
            · exact h
            · exact absurd h (not_reach_opnd C hao g hg b0)
        · exact (hW _ (by omega) hlb).1 hb
      by_cases hbk : BelowF G C k
      · exfalso
        rcases LeafBound.ao_op hao hkl with hand | hor
        · rw [hand] at hform
          obtain ⟨f0, f1⟩ := (opv_and _ _).1 hform
          have nb := not_both H k hkl hand
          rcases hv 0 (low_opnd H k hkl 0 (Or.inr hand)) f0 with h0 | ⟨r0, a0⟩ <;>
            rcases hv 1 (low_opnd H k hkl 1 (Or.inr hand)) f1 with h1 | ⟨r1, a1⟩
          · exact hF (hbk x ((val_and C hao k hkl hand x).2 ⟨h0, h1⟩))
          · have nr0 : ¬ OrReaches n C (opnd C k 0) g := fun r0 => nb ⟨r0, r1⟩
            obtain ⟨z, hxz, hz⟩ := (pure_val H k hkl hand 0 nr0 x).1 h0
            have hzm : z = m := hreach k hkl hand z (Or.inr ⟨r1, hz⟩)
            obtain ⟨y, hxy, hy⟩ := (opnd_val H b0 x).1 a1
            exact hF ((graphFun_empty G x).2 ⟨y, m, hb0 y hy, hxy, hzm ▸ hxz⟩)
          · have nr1 : ¬ OrReaches n C (opnd C k 1) g := fun r1 => nb ⟨r0, r1⟩
            obtain ⟨z, hxz, hz⟩ := (pure_val H k hkl hand 1 nr1 x).1 h1
            have hzm : z = m := hreach k hkl hand z (Or.inl ⟨r0, hz⟩)
            obtain ⟨y, hxy, hy⟩ := (opnd_val H b0 x).1 a0
            exact hF ((graphFun_empty G x).2 ⟨y, m, hb0 y hy, hxy, hzm ▸ hxz⟩)
          · exact nb ⟨r0, r1⟩
        · have hz : ∀ b : Fin 2, srcAt x u (ρ k b) = false := by
            intro b
            have hbw : ∀ x', wireVal n C (opnd C k b) x' = true → graphFun G ∅ x' = true :=
              fun x' h => below_or hao k hkl hor hbk b x' h
            have hne : opnd C k b ≠ n + g := by
              intro he
              apply hdirty
              intro x' hx'
              exact hbw x' (by rw [he]; exact hx')
            rw [hρ, if_neg hne]
            have hwb := opnd_lt C hao k hkl b
            by_cases hwn : opnd C k b < n
            · rw [V1 u x _ hwn]
              cases hc : wireVal n C (opnd C k b) x
              · rfl
              · exact absurd (hbw x hc) hF
            · obtain ⟨j, hj⟩ : ∃ j, opnd C k b = n + j := ⟨opnd C k b - n, by omega⟩
              have hBj : BelowF G C j := fun x' hx' => hbw x' (by rw [hj]; exact hx')
              rw [hj, V2 u x j, hu j, if_pos hBj]
          rw [hor, hz 0, hz 1] at hform
          exact absurd hform (by decide)
      · rw [hu k, if_neg hbk]
        have hlk : Low G C (n + k) := hbk
        have hor : (gateAt C k).op = GateOp.or := by
          rcases LeafBound.ao_op hao hkl with h | h
          · exact absurd (low_and H k hkl h hlk) hkg
          · exact h
        rw [hor] at hform
        simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
        have step : ∀ b : Fin 2, srcAt x u (ρ k b) = true →
            gateVal n C k x = true ∨
              (OrReaches n C (n + k) g ∧ wireVal n C (opnd C g b0) x = true) := by
          intro b hb
          rcases hv b (low_opnd H k hkl b (Or.inl hlk)) hb with hw | ⟨hr, hax⟩
          · left
            fin_cases b
            · exact (val_or C hao k hkl hor x).2 (Or.inl hw)
            · exact (val_or C hao k hkl hor x).2 (Or.inr hw)
          · exact Or.inr ⟨(reach_gate C hao k g hkl).2 (Or.inr ⟨hor, b, hr⟩), hax⟩
        rcases (opv_or _ _).1 hform with h | h
        · exact step 0 h
        · exact step 1 h
    · rw [hout, V2 u x o', hu o', if_pos hob]
  · intro p q hpq
    refine ⟨fun j => gateVal n C j (pairInput p q), ?_, ?_⟩
    · intro k hk huk
      have hkl := hK k hk
      change gateVal n C k (pairInput p q) = true at huk
      rw [gate_eq C hao k hkl] at huk
      change opv (isA (gateAt C k).op) _ _ = true
      refine opv_mono _ _ _ _ _ ?_ ?_ huk <;>
      · intro hb
        rw [hρ]
        split_ifs with he
        · rw [srcAt_srcOf]
          rw [he] at hb
          change gateVal n C g (pairInput p q) = true at hb
          obtain ⟨h0, h1⟩ := (val_and C hao g hg hgand _).1 hb
          fin_cases b0
          · exact h0
          · exact h1
        · rw [srcAt_srcOf]; exact hb
    · rw [srcAt_srcOf]
      change circuitFun n C (pairInput p q) = true
      rw [hcomp]
      exact (graphFun_empty G _).2 ⟨p, q, hpq, by simp [pairInput], by simp [pairInput]⟩
