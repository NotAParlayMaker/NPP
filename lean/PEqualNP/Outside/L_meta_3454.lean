import Mathlib.Algebra.Order.BigOperators.Group.Finset
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_3454 :
    ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (F : Finset ℕ),
      PEqualNP.TopForm.IsAO2 n C → (∀ g ∈ F, g < C.gates.length) →
      ((F.biUnion (fun g => (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.toFinset)).filter
        (fun w => w < n)).card +
      ((F.biUnion (fun g => (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.toFinset)).filter
        (fun w => n ≤ w ∧ w - n ∉ F)).card +
      (F.filter (fun g => n + g ∈ F.biUnion
        (fun g' => (PEqualNP.MetaComplexity.NestedCover.gateAt C g').inputs.toFinset))).card ≤
      2 * F.card := by
  intro n C F hAO hGate
  let gateAt := PEqualNP.MetaComplexity.NestedCover.gateAt C
  let inputs (g : ℕ) := (gateAt g).inputs.toFinset
  let wires := F.biUnion inputs
  let upper := wires.filter fun w => n ≤ w
  let outside := upper.filter fun w => w - n ∉ F
  let inside := upper.filter fun w => w - n ∈ F
  let internalGates := F.filter fun g => n + g ∈ wires
  change (wires.filter fun w => w < n).card +
    (wires.filter fun w => n ≤ w ∧ w - n ∉ F).card + internalGates.card ≤ 2 * F.card
  have bound : wires.card ≤ F.card * 2 := by
    apply Finset.card_biUnion_le_card_mul
    intro g hg
    have hmem : gateAt g ∈ C.gates := by
      simp [gateAt, PEqualNP.MetaComplexity.NestedCover.gateAt, hGate g hg]
    exact (List.toFinset_card_le _).trans (le_of_eq (hAO.2.2 _ hmem))
  have splitAtInput : (wires.filter fun w => w < n).card + upper.card = wires.card := by
    simpa only [upper, not_lt] using
      (wires.card_filter_add_card_filter_not (fun w => w < n))
  have splitAtGate : outside.card + inside.card = upper.card := by
    simpa only [outside, inside, not_not] using
      (upper.card_filter_add_card_filter_not (fun w => w - n ∉ F))
  have outsideEq : outside = wires.filter (fun w => n ≤ w ∧ w - n ∉ F) := by
    simp only [outside, upper, Finset.filter_filter]
  let offset : ℕ ↪ ℕ := ⟨fun g => n + g, fun _ _ h => Nat.add_left_cancel h⟩
  have mapEq : internalGates.map offset = inside := by
    ext w
    simp only [internalGates, inside, upper, Finset.mem_map, Finset.mem_filter]
    constructor
    · rintro ⟨g, ⟨hg, hw⟩, he⟩
      change n + g = w at he
      subst w
      exact ⟨⟨hw, by omega⟩, by simpa using hg⟩
    · intro ⟨⟨hw, hn⟩, hg⟩
      refine ⟨w - n, ⟨hg, ?_⟩, ?_⟩
      · simpa only [Nat.add_sub_of_le hn] using hw
      · change n + (w - n) = w
        omega
  have insideCard : inside.card = internalGates.card := by
    rw [← mapEq, Finset.card_map]
  rw [← outsideEq]
  omega
