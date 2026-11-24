import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm

namespace PEqualNP.Outside.L_meta_3027

def inc : Fin 3 → Fin 2 → Prop :=
  fun p l => (p.val = 0 ∧ l.val = 0) ∨ (p.val = 2 ∧ l.val = 1)

instance : DecidableRel inc := by
  intro p l
  unfold inc
  infer_instance

def circ : Circuit :=
  ⟨[⟨GateOp.or, [0, 2]⟩,
    ⟨GateOp.or, [3, 4]⟩,
    ⟨GateOp.and, [5, 6]⟩,
    ⟨GateOp.or, [1, 7]⟩,
    ⟨GateOp.and, [3, 8]⟩,
    ⟨GateOp.and, [4, 8]⟩,
    ⟨GateOp.and, [0, 9]⟩,
    ⟨GateOp.and, [2, 10]⟩,
    ⟨GateOp.or, [11, 12]⟩], 13⟩

def edge (z : Fin 5 → Bool) : Bool :=
  decide (∃ p : Fin 3, ∃ l : Fin 2, inc p l ∧ z (Fin.castAdd 2 p) = true ∧ z (Fin.natAdd 3 l) = true)

instance (z : Fin 5 → Bool) : Decidable
    (∃ p : Fin 3, ∃ l : Fin 2, inc p l ∧ z (Fin.castAdd 2 p) = true ∧ z (Fin.natAdd 3 l) = true) :=
  decidable_of_iff (edge z = true) (by simp [edge, decide_eq_true_eq])

lemma agrees : ∀ z : Fin 5 → Bool, circuitFun 5 circ z = edge z := by
  decide

lemma ao : IsAO2 5 circ := by
  decide

lemma c4 : ∀ p p' : Fin 3, ∀ l l' : Fin 2, p ≠ p' → l ≠ l' →
    ¬ (inc p l ∧ inc p l' ∧ inc p' l ∧ inc p' l') := by
  decide

lemma live : ∀ j < circ.gates.length,
    (∃ z : Fin 5 → Bool, (circ.wires (List.ofFn z)).getD (5 + j) false = true) ∧
      (5 + j = circ.output ∨ ∃ k < circ.gates.length, 5 + j ∈ (gateAt circ k).inputs) := by
  decide

def sees (w : ℕ) : Prop :=
  ∀ z : Fin 5 → Bool, (circ.wires (List.ofFn z)).getD w false = true →
    ∃ p : Fin 3, ∃ l : Fin 2, inc p l ∧ z (Fin.castAdd 2 p) = true ∧ z (Fin.natAdd 3 l) = true

lemma no0 : ¬ sees 0 := by unfold sees; decide
lemma no1 : ¬ sees 1 := by unfold sees; decide
lemma no2 : ¬ sees 2 := by unfold sees; decide
lemma no3 : ¬ sees 3 := by unfold sees; decide
lemma no4 : ¬ sees 4 := by unfold sees; decide
lemma no5 : ¬ sees 5 := by unfold sees; decide
lemma no6 : ¬ sees 6 := by unfold sees; decide
lemma no7 : ¬ sees 7 := by unfold sees; decide
lemma no8 : ¬ sees 8 := by unfold sees; decide
lemma no9 : ¬ sees 9 := by unfold sees; decide
lemma no10 : ¬ sees 10 := by unfold sees; decide
lemma yes11 : sees 11 := by unfold sees; decide
lemma yes12 : sees 12 := by unfold sees; decide
lemma yes13 : sees 13 := by unfold sees; decide

lemma gateInputs : ∀ j < circ.gates.length,
    ((gateAt circ j).op = GateOp.and ∨
      ¬ (∀ z : Fin 5 → Bool, (circ.wires (List.ofFn z)).getD (5 + j) false = true →
          ∃ p : Fin 3, ∃ l : Fin 2, inc p l ∧ z (Fin.castAdd 2 p) = true ∧ z (Fin.natAdd 3 l) = true)) →
      ∀ w ∈ (gateAt circ j).inputs,
        ¬ (∀ z : Fin 5 → Bool, (circ.wires (List.ofFn z)).getD w false = true →
            ∃ p : Fin 3, ∃ l : Fin 2, inc p l ∧ z (Fin.castAdd 2 p) = true ∧ z (Fin.natAdd 3 l) = true) := by
  intro j hj h w hw
  have hj9 : j < 9 := by simpa [circ] using hj
  interval_cases j
  · have hw' : w = 0 ∨ w = 2 := by simpa [circ, gateAt] using hw
    rcases hw' with rfl | rfl
    · exact no0
    · exact no2
  · have hw' : w = 3 ∨ w = 4 := by simpa [circ, gateAt] using hw
    rcases hw' with rfl | rfl
    · exact no3
    · exact no4
  · have hw' : w = 5 ∨ w = 6 := by simpa [circ, gateAt] using hw
    rcases hw' with rfl | rfl
    · exact no5
    · exact no6
  · have hw' : w = 1 ∨ w = 7 := by simpa [circ, gateAt] using hw
    rcases hw' with rfl | rfl
    · exact no1
    · exact no7
  · have hw' : w = 3 ∨ w = 8 := by simpa [circ, gateAt] using hw
    rcases hw' with rfl | rfl
    · exact no3
    · exact no8
  · have hw' : w = 4 ∨ w = 8 := by simpa [circ, gateAt] using hw
    rcases hw' with rfl | rfl
    · exact no4
    · exact no8
  · have hw' : w = 0 ∨ w = 9 := by simpa [circ, gateAt] using hw
    rcases hw' with rfl | rfl
    · exact no0
    · exact no9
  · have hw' : w = 2 ∨ w = 10 := by simpa [circ, gateAt] using hw
    rcases hw' with rfl | rfl
    · exact no2
    · exact no10
  · exfalso
    simp only [circ, gateAt] at h
    cases h with
    | inl hop => cases hop
    | inr hbad => exact hbad yes13

lemma soundShape : ∀ j < circ.gates.length,
    (∀ z : Fin 5 → Bool, (circ.wires (List.ofFn z)).getD (5 + j) false = true →
        ∃ p : Fin 3, ∃ l : Fin 2, inc p l ∧ z (Fin.castAdd 2 p) = true ∧ z (Fin.natAdd 3 l) = true) →
      ((gateAt circ j).op = GateOp.or →
        ∀ w ∈ (gateAt circ j).inputs,
          (∀ z : Fin 5 → Bool, (circ.wires (List.ofFn z)).getD w false = true →
            ∃ p : Fin 3, ∃ l : Fin 2, inc p l ∧ z (Fin.castAdd 2 p) = true ∧ z (Fin.natAdd 3 l) = true)) ∧
      (5 + j ≠ circ.output →
        readsIn circ (Finset.range circ.gates.length) (5 + j) = 1 ∧
          ∀ k < circ.gates.length, 5 + j ∈ (gateAt circ k).inputs →
            (gateAt circ k).op = GateOp.or ∧
              (∀ z : Fin 5 → Bool, (circ.wires (List.ofFn z)).getD (5 + k) false = true →
                ∃ p : Fin 3, ∃ l : Fin 2, inc p l ∧ z (Fin.castAdd 2 p) = true ∧ z (Fin.natAdd 3 l) = true)) := by
  intro j hj hsnd
  have hj9 : j < 9 := by simpa [circ] using hj
  interval_cases j
  · exact (no5 hsnd).elim
  · exact (no6 hsnd).elim
  · exact (no7 hsnd).elim
  · exact (no8 hsnd).elim
  · exact (no9 hsnd).elim
  · exact (no10 hsnd).elim
  · refine And.intro ?_ ?_
    · intro hop
      simp [circ, gateAt] at hop
    · intro _
      refine And.intro (by decide) ?_
      intro k hk hin
      have hk9 : k < 9 := by simpa [circ] using hk
      interval_cases k
      · simp [circ, gateAt] at hin
      · simp [circ, gateAt] at hin
      · simp [circ, gateAt] at hin
      · simp [circ, gateAt] at hin
      · simp [circ, gateAt] at hin
      · simp [circ, gateAt] at hin
      · simp [circ, gateAt] at hin
      · simp [circ, gateAt] at hin
      · constructor
        · simp [circ, gateAt]
        · exact yes13
  · refine And.intro ?_ ?_
    · intro hop
      simp [circ, gateAt] at hop
    · intro _
      refine And.intro (by decide) ?_
      intro k hk hin
      have hk9 : k < 9 := by simpa [circ] using hk
      interval_cases k
      · simp [circ, gateAt] at hin
      · simp [circ, gateAt] at hin
      · simp [circ, gateAt] at hin
      · simp [circ, gateAt] at hin
      · simp [circ, gateAt] at hin
      · simp [circ, gateAt] at hin
      · simp [circ, gateAt] at hin
      · simp [circ, gateAt] at hin
      · constructor
        · simp [circ, gateAt]
        · exact yes13
  · refine And.intro ?_ ?_
    · intro _ w hw
      have hw' : w = 11 ∨ w = 12 := by simpa [circ, gateAt] using hw
      rcases hw' with rfl | rfl
      · exact yes11
      · exact yes12
    · intro hne
      simp [circ] at hne

lemma andUnique : ∀ j < circ.gates.length, ∀ k < circ.gates.length,
    (gateAt circ j).op = GateOp.and →
      (∀ z : Fin 5 → Bool, (circ.wires (List.ofFn z)).getD (5 + j) false = true →
          ∃ p : Fin 3, ∃ l : Fin 2, inc p l ∧ z (Fin.castAdd 2 p) = true ∧ z (Fin.natAdd 3 l) = true) →
        (gateAt circ k).op = GateOp.and →
          (∀ z : Fin 5 → Bool, (circ.wires (List.ofFn z)).getD (5 + k) false = true →
              ∃ p : Fin 3, ∃ l : Fin 2, inc p l ∧ z (Fin.castAdd 2 p) = true ∧ z (Fin.natAdd 3 l) = true) →
            ((gateAt circ j).inputs.Nodup ∧
              ∀ w ∈ (gateAt circ j).inputs, w ∈ (gateAt circ k).inputs → j = k) := by
  intro j hj k hk ha hja hb hka
  have hj9 : j < 9 := by simpa [circ] using hj
  have hk9 : k < 9 := by simpa [circ] using hk
  interval_cases j
  · exact (no5 hja).elim
  · exact (no6 hja).elim
  · exact (no7 hja).elim
  · exact (no8 hja).elim
  · exact (no9 hja).elim
  · exact (no10 hja).elim
  · interval_cases k
    · simp [circ, gateAt] at hb
    · simp [circ, gateAt] at hb
    · exact (no7 hka).elim
    · simp [circ, gateAt] at hb
    · exact (no9 hka).elim
    · exact (no10 hka).elim
    · simp [circ, gateAt]
    · simp [circ, gateAt]
    · simp [circ, gateAt] at hb
  · interval_cases k
    · simp [circ, gateAt] at hb
    · simp [circ, gateAt] at hb
    · exact (no7 hka).elim
    · simp [circ, gateAt] at hb
    · exact (no9 hka).elim
    · exact (no10 hka).elim
    · simp [circ, gateAt]
    · simp [circ, gateAt]
    · simp [circ, gateAt] at hb
  · simp [circ, gateAt] at ha

lemma index : 3 < circ.gates.length := by decide

lemma badGate : ¬ (∀ z : Fin 5 → Bool, (circ.wires (List.ofFn z)).getD (5 + 3) false = true →
    ∃ p : Fin 3, ∃ l : Fin 2, inc p l ∧ z (Fin.castAdd 2 p) = true ∧ z (Fin.natAdd 3 l) = true) := by
  decide

lemma cone0 : PEqualNP.SplitCount.InConeOrSelf 5 circ 0 3 := by decide
lemma cone1 : PEqualNP.SplitCount.InConeOrSelf 5 circ 1 3 := by decide
lemma cone2 : PEqualNP.SplitCount.InConeOrSelf 5 circ 2 3 := by decide
lemma cone3 : PEqualNP.SplitCount.InConeOrSelf 5 circ 3 3 := by decide
lemma ncone3 : ¬ InCone 5 circ 3 3 := by decide
lemma ncone4 : ¬ InCone 5 circ 4 3 := by decide
lemma ncone5 : ¬ InCone 5 circ 5 3 := by decide
lemma ncone6 : ¬ InCone 5 circ 6 3 := by decide
lemma ncone7 : ¬ InCone 5 circ 7 3 := by decide
lemma ncone8 : ¬ InCone 5 circ 8 3 := by decide

lemma privateCone : ∀ k < circ.gates.length, ¬ PEqualNP.SplitCount.InConeOrSelf 5 circ k 3 →
    ∀ g < circ.gates.length, InCone 5 circ g 3 → 5 + g ∉ (gateAt circ k).inputs := by
  intro k hk hnot g hg hin
  have hk9 : k < 9 := by simpa [circ] using hk
  have hg9 : g < 9 := by simpa [circ] using hg
  interval_cases k
  · exact False.elim (hnot cone0)
  · exact False.elim (hnot cone1)
  · exact False.elim (hnot cone2)
  · exact False.elim (hnot cone3)
  · interval_cases g
    · simp [circ, gateAt]
    · simp [circ, gateAt]
    · simp [circ, gateAt]
    · exact absurd hin ncone3
    · exact absurd hin ncone4
    · exact absurd hin ncone5
    · exact absurd hin ncone6
    · exact absurd hin ncone7
    · exact absurd hin ncone8
  · interval_cases g
    · simp [circ, gateAt]
    · simp [circ, gateAt]
    · simp [circ, gateAt]
    · exact absurd hin ncone3
    · exact absurd hin ncone4
    · exact absurd hin ncone5
    · exact absurd hin ncone6
    · exact absurd hin ncone7
    · exact absurd hin ncone8
  · interval_cases g
    · simp [circ, gateAt]
    · simp [circ, gateAt]
    · simp [circ, gateAt]
    · exact absurd hin ncone3
    · exact absurd hin ncone4
    · exact absurd hin ncone5
    · exact absurd hin ncone6
    · exact absurd hin ncone7
    · exact absurd hin ncone8
  · interval_cases g
    · simp [circ, gateAt]
    · simp [circ, gateAt]
    · simp [circ, gateAt]
    · exact absurd hin ncone3
    · exact absurd hin ncone4
    · exact absurd hin ncone5
    · exact absurd hin ncone6
    · exact absurd hin ncone7
    · exact absurd hin ncone8
  · interval_cases g
    · simp [circ, gateAt]
    · simp [circ, gateAt]
    · simp [circ, gateAt]
    · exact absurd hin ncone3
    · exact absurd hin ncone4
    · exact absurd hin ncone5
    · exact absurd hin ncone6
    · exact absurd hin ncone7
    · exact absurd hin ncone8

lemma oneSingleton : ∃ v : Fin 5,
    (circ.wires (List.ofFn (fun i : Fin 5 => decide (i = v)))).getD (5 + 3) false = true := by
  decide

def killed : Circuit := ⟨circ.gates.set 3 ⟨GateOp.or, []⟩, circ.output⟩

lemma someLost : ∃ p : Fin 3, ∃ l : Fin 2,
    inc p l ∧
      (circ.wires (List.ofFn (fun i : Fin 5 => decide (i = Fin.castAdd 2 p)))).getD (8) false = false ∧
      (circ.wires (List.ofFn (fun i : Fin 5 => decide (i = Fin.natAdd 3 l)))).getD (8) false = false ∧
      circuitFun 5 circ (fun i : Fin 5 => decide (i = Fin.castAdd 2 p ∨ i = Fin.natAdd 3 l)) = true ∧
      circuitFun 5 killed (fun i : Fin 5 => decide (i = Fin.castAdd 2 p ∨ i = Fin.natAdd 3 l)) = false := by
  decide

lemma tooBig :
    ¬ ((Finset.univ.filter fun v : Fin 5 =>
          (circ.wires (List.ofFn (fun i : Fin 5 => decide (i = v)))).getD 8 false = true).card +
        (Finset.univ.filter fun p : Fin 3 => ∃ l : Fin 2,
          inc p l ∧
            (circ.wires (List.ofFn (fun i : Fin 5 => decide (i = Fin.castAdd 2 p)))).getD 8 false = false ∧
            (circ.wires (List.ofFn (fun i : Fin 5 => decide (i = Fin.natAdd 3 l)))).getD 8 false = false ∧
            circuitFun 5 circ (fun i : Fin 5 => decide (i = Fin.castAdd 2 p ∨ i = Fin.natAdd 3 l)) = true ∧
            circuitFun 5 killed (fun i : Fin 5 => decide (i = Fin.castAdd 2 p ∨ i = Fin.natAdd 3 l)) = false).card +
        (Finset.univ.filter fun l : Fin 2 => ∃ p : Fin 3,
          inc p l ∧
            (circ.wires (List.ofFn (fun i : Fin 5 => decide (i = Fin.castAdd 2 p)))).getD 8 false = false ∧
            (circ.wires (List.ofFn (fun i : Fin 5 => decide (i = Fin.natAdd 3 l)))).getD 8 false = false ∧
            circuitFun 5 circ (fun i : Fin 5 => decide (i = Fin.castAdd 2 p ∨ i = Fin.natAdd 3 l)) = true ∧
            circuitFun 5 killed (fun i : Fin 5 => decide (i = Fin.castAdd 2 p ∨ i = Fin.natAdd 3 l)) = false).card
      ≤ ((Finset.range circ.gates.length).filter fun k => PEqualNP.SplitCount.InConeOrSelf 5 circ k 3).card) := by
  decide

end PEqualNP.Outside.L_meta_3027

open PEqualNP.Outside.L_meta_3027

set_option maxHeartbeats 800000 in
theorem PEqualNP.Outside.L_meta_3027 : ¬ (∀ (Np Nl : ℕ) (I : Fin Np → Fin Nl → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit) (c : ℕ), (∀ p p' : Fin Np, ∀ l l' : Fin Nl, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.TopForm.IsAO2 (Np + Nl) C → (∀ z : Fin (Np + Nl) → Bool, PEqualNP.MetaComplexity.circuitFun (Np + Nl) C z = decide (∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true)) → (∀ j1 < C.gates.length, (∃ z2 : Fin (Np + Nl) → Bool, (C.wires (List.ofFn z2)).getD ((Np + Nl) + j1) false = true) ∧ ((Np + Nl) + j1 = C.output ∨ ∃ k3 < C.gates.length, (Np + Nl) + j1 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k3).inputs)) → (∀ j4 < C.gates.length, ((PEqualNP.MetaComplexity.NestedCover.gateAt C j4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ ¬ (∀ z6 : Fin (Np + Nl) → Bool, (C.wires (List.ofFn z6)).getD ((Np + Nl) + j4) false = true → ∃ p7 : Fin Np, ∃ l8 : Fin Nl, I p7 l8 ∧ z6 (Fin.castAdd Nl p7) = true ∧ z6 (Fin.natAdd Np l8) = true)) → ∀ w5 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j4).inputs, ¬ (∀ z9 : Fin (Np + Nl) → Bool, (C.wires (List.ofFn z9)).getD (w5) false = true → ∃ p10 : Fin Np, ∃ l11 : Fin Nl, I p10 l11 ∧ z9 (Fin.castAdd Nl p10) = true ∧ z9 (Fin.natAdd Np l11) = true)) → (∀ j12 < C.gates.length, (∀ z15 : Fin (Np + Nl) → Bool, (C.wires (List.ofFn z15)).getD ((Np + Nl) + j12) false = true → ∃ p16 : Fin Np, ∃ l17 : Fin Nl, I p16 l17 ∧ z15 (Fin.castAdd Nl p16) = true ∧ z15 (Fin.natAdd Np l17) = true) → ((PEqualNP.MetaComplexity.NestedCover.gateAt C j12).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ w13 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j12).inputs, (∀ z18 : Fin (Np + Nl) → Bool, (C.wires (List.ofFn z18)).getD (w13) false = true → ∃ p19 : Fin Np, ∃ l20 : Fin Nl, I p19 l20 ∧ z18 (Fin.castAdd Nl p19) = true ∧ z18 (Fin.natAdd Np l20) = true)) ∧ ((Np + Nl) + j12 ≠ C.output → PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.gates.length) ((Np + Nl) + j12) = 1 ∧ ∀ k14 < C.gates.length, (Np + Nl) + j12 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k14).inputs → (PEqualNP.MetaComplexity.NestedCover.gateAt C k14).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (∀ z21 : Fin (Np + Nl) → Bool, (C.wires (List.ofFn z21)).getD ((Np + Nl) + k14) false = true → ∃ p22 : Fin Np, ∃ l23 : Fin Nl, I p22 l23 ∧ z21 (Fin.castAdd Nl p22) = true ∧ z21 (Fin.natAdd Np l23) = true))) → (∀ j24 < C.gates.length, ∀ k25 < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C j24).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∀ z28 : Fin (Np + Nl) → Bool, (C.wires (List.ofFn z28)).getD ((Np + Nl) + j24) false = true → ∃ p29 : Fin Np, ∃ l30 : Fin Nl, I p29 l30 ∧ z28 (Fin.castAdd Nl p29) = true ∧ z28 (Fin.natAdd Np l30) = true) → (PEqualNP.MetaComplexity.NestedCover.gateAt C k25).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∀ z31 : Fin (Np + Nl) → Bool, (C.wires (List.ofFn z31)).getD ((Np + Nl) + k25) false = true → ∃ p32 : Fin Np, ∃ l33 : Fin Nl, I p32 l33 ∧ z31 (Fin.castAdd Nl p32) = true ∧ z31 (Fin.natAdd Np l33) = true) → ((PEqualNP.MetaComplexity.NestedCover.gateAt C j24).inputs.Nodup ∧ ∀ w26 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j24).inputs, w26 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k25).inputs → j24 = k25)) → c < C.gates.length → ¬ (∀ z34 : Fin (Np + Nl) → Bool, (C.wires (List.ofFn z34)).getD ((Np + Nl) + c) false = true → ∃ p35 : Fin Np, ∃ l36 : Fin Nl, I p35 l36 ∧ z34 (Fin.castAdd Nl p35) = true ∧ z34 (Fin.natAdd Np l36) = true) → (∀ k37 < C.gates.length, ¬ PEqualNP.SplitCount.InConeOrSelf (Np + Nl) C k37 c → ∀ g38 < C.gates.length, PEqualNP.EdgeOwnership.InCone (Np + Nl) C g38 c → (Np + Nl) + g38 ∉ (PEqualNP.MetaComplexity.NestedCover.gateAt C k37).inputs) → (∃ v39 : Fin (Np + Nl), (C.wires (List.ofFn (fun i40 : Fin (Np + Nl) => decide (i40 = v39)))).getD ((Np + Nl) + c) false = true) → (∃ p41 : Fin Np, ∃ l42 : Fin Nl, (I p41 l42 ∧ (C.wires (List.ofFn (fun i43 : Fin (Np + Nl) => decide (i43 = Fin.castAdd Nl p41)))).getD ((Np + Nl) + c) false = false ∧ (C.wires (List.ofFn (fun i44 : Fin (Np + Nl) => decide (i44 = Fin.natAdd Np l42)))).getD ((Np + Nl) + c) false = false ∧ PEqualNP.MetaComplexity.circuitFun (Np + Nl) C (fun i45 : Fin (Np + Nl) => decide (i45 = Fin.castAdd Nl p41 ∨ i45 = Fin.natAdd Np l42)) = true ∧ PEqualNP.MetaComplexity.circuitFun (Np + Nl) (PEqualNP.CircuitLowerBounds.Circuit.mk (C.gates.set c (PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [])) C.output) (fun i46 : Fin (Np + Nl) => decide (i46 = Fin.castAdd Nl p41 ∨ i46 = Fin.natAdd Np l42)) = false)) → (Finset.univ.filter fun v47 : Fin (Np + Nl) => (C.wires (List.ofFn (fun i53 : Fin (Np + Nl) => decide (i53 = v47)))).getD ((Np + Nl) + c) false = true).card + (Finset.univ.filter fun p48 : Fin Np => ∃ l49 : Fin Nl, (I p48 l49 ∧ (C.wires (List.ofFn (fun i54 : Fin (Np + Nl) => decide (i54 = Fin.castAdd Nl p48)))).getD ((Np + Nl) + c) false = false ∧ (C.wires (List.ofFn (fun i55 : Fin (Np + Nl) => decide (i55 = Fin.natAdd Np l49)))).getD ((Np + Nl) + c) false = false ∧ PEqualNP.MetaComplexity.circuitFun (Np + Nl) C (fun i56 : Fin (Np + Nl) => decide (i56 = Fin.castAdd Nl p48 ∨ i56 = Fin.natAdd Np l49)) = true ∧ PEqualNP.MetaComplexity.circuitFun (Np + Nl) (PEqualNP.CircuitLowerBounds.Circuit.mk (C.gates.set c (PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [])) C.output) (fun i57 : Fin (Np + Nl) => decide (i57 = Fin.castAdd Nl p48 ∨ i57 = Fin.natAdd Np l49)) = false)).card + (Finset.univ.filter fun l51 : Fin Nl => ∃ p50 : Fin Np, (I p50 l51 ∧ (C.wires (List.ofFn (fun i58 : Fin (Np + Nl) => decide (i58 = Fin.castAdd Nl p50)))).getD ((Np + Nl) + c) false = false ∧ (C.wires (List.ofFn (fun i59 : Fin (Np + Nl) => decide (i59 = Fin.natAdd Np l51)))).getD ((Np + Nl) + c) false = false ∧ PEqualNP.MetaComplexity.circuitFun (Np + Nl) C (fun i60 : Fin (Np + Nl) => decide (i60 = Fin.castAdd Nl p50 ∨ i60 = Fin.natAdd Np l51)) = true ∧ PEqualNP.MetaComplexity.circuitFun (Np + Nl) (PEqualNP.CircuitLowerBounds.Circuit.mk (C.gates.set c (PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [])) C.output) (fun i61 : Fin (Np + Nl) => decide (i61 = Fin.castAdd Nl p50 ∨ i61 = Fin.natAdd Np l51)) = false)).card ≤ ((Finset.range C.gates.length).filter fun k52 => PEqualNP.SplitCount.InConeOrSelf (Np + Nl) C k52 c).card) := by
  intro H
  have step := H 3 2 inc circ 3 c4 ao agrees live gateInputs soundShape
    andUnique index badGate privateCone oneSingleton someLost
  exact tooBig step
