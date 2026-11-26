import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.HeptadCover

namespace PEqualNP.Outside.R_meta_5198_aux

def pairInput (p l : Fin 13) : List Bool :=
  List.ofFn (fun u : Fin 13 => decide (u = p)) ++
    List.ofFn (fun v : Fin 13 => decide (v = l))

def quadInput (lines : Fin 13 → Finset (Fin 13)) (Q : Finset (Fin 13)) : List Bool :=
  List.ofFn (fun u : Fin 13 => decide (u ∈ Q)) ++
    List.ofFn (fun v : Fin 13 => decide (v ∈ missLines lines Q))

def wireVal (C : Circuit) (j : ℕ) (x : List Bool) : Bool :=
  (C.wires x).getD j false

def nestedAnd (C : Circuit) (j : ℕ) : Prop :=
  (gateAt C j).op = GateOp.and ∧
    ∃ w ∈ (gateAt C j).inputs, 26 ≤ w ∧
      (gateAt C (w - 26)).op = GateOp.and

def HardSpec (lines : Fin 13 → Finset (Fin 13))
    (input : Finset (Fin 13) → Finset (Fin 13) → List Bool)
    (wire : Circuit → ℕ → List Bool → Bool)
    (special : Circuit → ℕ → Prop)
    (C : Circuit) (i j : ℕ) : Prop :=
  Monotone2 C ∧ ReadsBack 26 C ∧
  i < 26 + C.size ∧ j < 26 + C.size ∧
  (∀ p l : Fin 13, p ∈ lines l →
    wire C i (input {p} {l}) = true ∨ wire C j (input {p} {l}) = true) ∧
  (∀ Q : Finset (Fin 13), IsQuadrangle lines Q →
    wire C i (quadInput lines Q) = false ∧ wire C j (quadInput lines Q) = false) ∧
  (∃ p l : Fin 13, p ∈ lines l ∧
    wire C i (input {p} {l}) = true ∧ wire C j (input {p} {l}) = false) ∧
  (∃ p l : Fin 13, p ∈ lines l ∧
    wire C j (input {p} {l}) = true ∧ wire C i (input {p} {l}) = false) ∧
  (∀ k ∈ Finset.range C.size, ∀ m ∈ Finset.range C.size,
    special C k → special C m → k = m)

end PEqualNP.Outside.R_meta_5198_aux

open PEqualNP.Outside.R_meta_5198_aux


theorem PEqualNP.Outside.R_meta_5198_1
    (noNested : ∀ (lines : Fin 13 → Finset (Fin 13))
      (input : Finset (Fin 13) → Finset (Fin 13) → List Bool)
      (wire : Circuit → ℕ → List Bool → Bool) (special : Circuit → ℕ → Prop)
      (C : Circuit) (i j : ℕ), HardSpec lines input wire special C i j →
      (∀ k, ¬ special C k) → 63 ≤ C.size)
    (oneNested : ∀ (lines : Fin 13 → Finset (Fin 13))
      (input : Finset (Fin 13) → Finset (Fin 13) → List Bool)
      (wire : Circuit → ℕ → List Bool → Bool) (special : Circuit → ℕ → Prop)
      (C : Circuit) (i j : ℕ), HardSpec lines input wire special C i j →
      (∃ k, special C k) → 63 ≤ C.size) :
  have x1 : Fin (13 : ℕ) → Finset (Fin (13 : ℕ)) := PEqualNP.HeptadCover.singerLines3; have x2 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → List Bool := fun (x2 x3 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 ∈ x2)) ++ List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 ∈ x3); have x3 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → List Bool → Bool := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ) (x5 : List Bool) => (x3.wires x5).getD x4 Bool.false; have x4 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt; have x5 : PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.CircuitLowerBounds.GateOp.and; have x6 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Prop := fun (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 : ℕ) => (x4 x6 x7).op = x5 ∧ ∃ x8 ∈ (x4 x6 x7).inputs, (26 : ℕ) ≤ x8 ∧ (x4 x6 (x8 - (26 : ℕ))).op = x5; ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit) (x8 x9 : ℕ), PEqualNP.MetaComplexity.Monotone2 x7 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x7 → x8 < (26 : ℕ) + x7.size → x9 < (26 : ℕ) + x7.size → (∀ (x14 x15 : Fin (13 : ℕ)), x14 ∈ x1 x15 → x3 x7 x8 (x2 {x14} {x15}) = Bool.true ∨ x3 x7 x9 (x2 {x14} {x15}) = Bool.true) → (∀ (x15 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle x1 x15 → x3 x7 x8 (x2 x15 (PEqualNP.HeptadCover.missLines x1 x15)) = Bool.false ∧ x3 x7 x9 (x2 x15 (PEqualNP.HeptadCover.missLines x1 x15)) = Bool.false) → (∃ (x16 : Fin (13 : ℕ)) (x17 : Fin (13 : ℕ)), x16 ∈ x1 x17 ∧ x3 x7 x8 (x2 {x16} {x17}) = Bool.true ∧ x3 x7 x9 (x2 {x16} {x17}) = Bool.false) → (∃ (x17 : Fin (13 : ℕ)) (x18 : Fin (13 : ℕ)), x17 ∈ x1 x18 ∧ x3 x7 x9 (x2 {x17} {x18}) = Bool.true ∧ x3 x7 x8 (x2 {x17} {x18}) = Bool.false) → (∀ x18 ∈ Finset.range x7.size, ∀ x20 ∈ Finset.range x7.size, x6 x7 x18 → x6 x7 x20 → x18 = x20) → (63 : ℕ) ≤ x7.size := by
  intro lines input wire gateAtLocal andOp special C i j
    hMono hBack hi hj hEdges hQuads hI hJ hUnique
  have hSpec : HardSpec lines input wire special C i j :=
    ⟨hMono, hBack, hi, hj, hEdges, hQuads, hI, hJ, hUnique⟩
  by_cases h : ∃ k, special C k
  · exact oneNested lines input wire special C i j hSpec h
  · apply noNested lines input wire special C i j hSpec
    intro k hk
    exact h ⟨k, hk⟩
