import Mathlib
import PEqualNP.Defs

-- Vary two disjoint groups of inputs independently. If each observed wire
-- reads just one group, the wires must distinguish every pair of row and
-- column profiles of the edge function.
theorem PEqualNP.Outside.R_meta_5054_823
    (grid : ∀ (f : (Fin 9 → Bool) → Bool) (S : Finset Nat) (obs : (Fin 9 → Bool) → Nat → Bool),
      S.card = 6 → ∀ m : Finset (Fin 9), let M := fun (a b : Fin 9 → Bool) => f (fun i => if i ∈ m then a i else b i);
      (∀ w ∈ S, DependsOn (fun x => obs x w) (m : Set (Fin 9)) ∨ DependsOn (fun x => obs x w) (m : Set (Fin 9))ᶜ) → 64 < (Set.range M).ncard * (Set.range (fun b a => M a b)).ncard →
      ∃ x y, f x ≠ f y ∧ ∀ w ∈ S, obs x w = obs y w)
    (bounded : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.FanInTwo x1 →     x1.size = (8 : ℕ) →       (∀ x4 ∈ x1.gates, x4.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) →         (∀ (x5 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x5)).getD (9 : ℕ) Bool.false = (x5 (0 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)))) →           have x6 : ℕ → ℕ → Prop := fun (x6 x7 : ℕ) => Relation.ReflTransGen (fun (x8 x9 : ℕ) => (10 : ℕ) ≤ x9 ∧ x9 < (17 : ℕ) ∧ x8 < x9 ∧ x8 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x9 - (9 : ℕ))).inputs) x6 x7;           have x7 : (Fin (9 : ℕ) → Bool) → Bool := fun (x7 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x8 : ℕ) => x7 (Fin.ofNat (9 : ℕ) (x8 / (10 : ℕ))) && x7 (Fin.ofNat (9 : ℕ) (x8 % (10 : ℕ)));           ∀ x8 ⊆ Finset.range (17 : ℕ), x8.card = (6 : ℕ) → (9 : ℕ) ∉ x8 → (∀ x12 < (9 : ℕ), ∃ x14 ∈ x8, x6 x12 x14) → (∃ (x13 : Finset ℕ), (3 : ℕ) ≤ x13.card ∧ ∀ x14 ∈ x13, (10 : ℕ) ≤ x14 ∧ x14 < (17 : ℕ) ∧ ∃ x16 ∈ x8, x6 x14 x16) → (∀ m : Finset (Fin 9), let M := fun (a b : Fin 9 → Bool) => x7 (fun i => if i ∈ m then a i else b i); (∀ w ∈ x8, DependsOn (fun x => (x1.wires (List.ofFn x)).getD w false) (m : Set (Fin 9)) ∨ DependsOn (fun x => (x1.wires (List.ofFn x)).getD w false) (m : Set (Fin 9))ᶜ) → (Set.range M).ncard * (Set.range (fun b a => M a b)).ncard ≤ 64) → ∃ (x14 : Fin (9 : ℕ) → Bool) (x15 : Fin (9 : ℕ) → Bool), x7 x14 ≠ x7 x15 ∧ ∀ x16 ∈ x8, (x1.wires (List.ofFn x14)).getD x16 Bool.false = (x1.wires (List.ofFn x15)).getD x16 Bool.false) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.FanInTwo x1 →     x1.size = (8 : ℕ) →       (∀ x4 ∈ x1.gates, x4.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) →         (∀ (x5 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x5)).getD (9 : ℕ) Bool.false = (x5 (0 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)))) →           have x6 : ℕ → ℕ → Prop := fun (x6 x7 : ℕ) => Relation.ReflTransGen (fun (x8 x9 : ℕ) => (10 : ℕ) ≤ x9 ∧ x9 < (17 : ℕ) ∧ x8 < x9 ∧ x8 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x9 - (9 : ℕ))).inputs) x6 x7;           have x7 : (Fin (9 : ℕ) → Bool) → Bool := fun (x7 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x8 : ℕ) => x7 (Fin.ofNat (9 : ℕ) (x8 / (10 : ℕ))) && x7 (Fin.ofNat (9 : ℕ) (x8 % (10 : ℕ)));           ∀ x8 ⊆ Finset.range (17 : ℕ), x8.card = (6 : ℕ) → (9 : ℕ) ∉ x8 → (∀ x12 < (9 : ℕ), ∃ x14 ∈ x8, x6 x12 x14) → (∃ (x13 : Finset ℕ), (3 : ℕ) ≤ x13.card ∧ ∀ x14 ∈ x13, (10 : ℕ) ≤ x14 ∧ x14 < (17 : ℕ) ∧ ∃ x16 ∈ x8, x6 x14 x16) → ∃ (x14 : Fin (9 : ℕ) → Bool) (x15 : Fin (9 : ℕ) → Bool), x7 x14 ≠ x7 x15 ∧ ∀ x16 ∈ x8, (x1.wires (List.ofFn x14)).getD x16 Bool.false = (x1.wires (List.ofFn x15)).getD x16 Bool.false := by
  classical
  intro C fan size positive first
  dsimp only
  intro S subset six excludes covers paths
  apply Classical.byContradiction
  intro no
  apply no
  apply bounded C fan size positive first S subset six excludes covers paths
  intro m
  dsimp only
  intro pure
  apply le_of_not_gt
  intro big
  exact no (grid _ S (fun x w => (C.wires (List.ofFn x)).getD w false) six m pure big)
