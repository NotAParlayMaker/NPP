import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.CarriedProduct PEqualNP.CleanedNonEdge

-- Partition the edges of G by their unique carrier AND gate (the first AND gate
-- in evaluation order whose wire is live at the pair input 1_uv), then split
-- carriers into clean, dirty star, and dirty non-star carriers.
theorem PEqualNP.Outside.R_meta_606_47
    (carrierPartition : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
      ∀ D : Circuit, Monotone2 D →
      circuitFun n D = (fun x : Fin n → Bool => decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) →
      G.edgeFinset.card = ∑ j ∈ Finset.range D.gates.length, (carried n G D j).card)
    (cleanCarriers : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
      ∀ D : Circuit, Monotone2 D →
      circuitFun n D = (fun x : Fin n → Bool => decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) →
      ∑ j ∈ (Finset.range D.gates.length).filter (fun j => ¬ IsDirty n G D j),
        (carried n G D j).card ≤ D.size)
    (dirtyStarCarriers : ∃ k : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
      ∀ D : Circuit, Monotone2 D →
      circuitFun n D = (fun x : Fin n → Bool => decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) →
      ∑ j ∈ (Finset.range D.gates.length).filter (fun j => IsDirty n G D j ∧
          ∃ c : Fin n, ∀ e ∈ carried n G D j, e.1 = c ∨ e.2 = c),
        (carried n G D j).card ≤ k * (D.size + 1))
    (dirtyNonStarCarriers : ∃ k : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
      ∀ D : Circuit, Monotone2 D →
      circuitFun n D = (fun x : Fin n → Bool => decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) →
      ∑ j ∈ (Finset.range D.gates.length).filter (fun j => IsDirty n G D j ∧
          ¬ ∃ c : Fin n, ∀ e ∈ carried n G D j, e.1 = c ∨ e.2 = c),
        (carried n G D j).card ≤ k * (D.size + 1)) :
    ∃ c : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) → ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D → PEqualNP.MetaComplexity.circuitFun n D = (fun x : Fin n → Bool => decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) → G.edgeFinset.card ≤ c * (D.size + 1) := by
  obtain ⟨k₂, h₂⟩ := dirtyStarCarriers
  obtain ⟨k₃, h₃⟩ := dirtyNonStarCarriers
  refine ⟨k₂ + k₃ + 1, ?_⟩
  intro n G inst hG D hMon hFun
  classical
  have hPart := carrierPartition n G hG D hMon hFun
  have hClean := cleanCarriers n G hG D hMon hFun
  have hStar := h₂ n G hG D hMon hFun
  have hNonStar := h₃ n G hG D hMon hFun
  let W : ℕ → ℕ := fun j => (carried n G D j).card
  let P : ℕ → Prop := fun j => IsDirty n G D j
  let Q : ℕ → Prop := fun j => ∃ c : Fin n, ∀ e ∈ carried n G D j, e.1 = c ∨ e.2 = c
  have hSplit1 : ∑ j ∈ Finset.range D.gates.length, W j =
      (∑ j ∈ (Finset.range D.gates.length).filter P, W j) +
      (∑ j ∈ (Finset.range D.gates.length).filter (fun j => ¬ P j), W j) :=
    (Finset.sum_filter_add_sum_filter_not (Finset.range D.gates.length) P W).symm
  have hFiltB : (Finset.range D.gates.length).filter (fun j => P j ∧ Q j) =
      ((Finset.range D.gates.length).filter P).filter Q := by
    ext j
    exact ⟨fun hj => Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hj).1, (Finset.mem_filter.mp hj).2.1⟩, (Finset.mem_filter.mp hj).2.2⟩,
      fun hj => Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).1, (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).2, (Finset.mem_filter.mp hj).2⟩⟩
  have hFiltC : (Finset.range D.gates.length).filter (fun j => P j ∧ ¬ Q j) =
      ((Finset.range D.gates.length).filter P).filter (fun j => ¬ Q j) := by
    ext j
    exact ⟨fun hj => Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hj).1, (Finset.mem_filter.mp hj).2.1⟩, (Finset.mem_filter.mp hj).2.2⟩,
      fun hj => Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).1, (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).2, (Finset.mem_filter.mp hj).2⟩⟩
  have hSplit2 : ∑ j ∈ (Finset.range D.gates.length).filter P, W j =
      (∑ j ∈ (Finset.range D.gates.length).filter (fun j => P j ∧ Q j), W j) +
      (∑ j ∈ (Finset.range D.gates.length).filter (fun j => P j ∧ ¬ Q j), W j) := by
    rw [hFiltB, hFiltC]
    exact (Finset.sum_filter_add_sum_filter_not ((Finset.range D.gates.length).filter P) Q W).symm
  calc G.edgeFinset.card
      = ∑ j ∈ Finset.range D.gates.length, W j := hPart
    _ = (∑ j ∈ (Finset.range D.gates.length).filter (fun j => P j ∧ Q j), W j) +
        (∑ j ∈ (Finset.range D.gates.length).filter (fun j => P j ∧ ¬ Q j), W j) +
        (∑ j ∈ (Finset.range D.gates.length).filter (fun j => ¬ P j), W j) := by
          rw [hSplit1, hSplit2]
    _ ≤ k₂ * (D.size + 1) + k₃ * (D.size + 1) + (D.size + 1) :=
        Nat.add_le_add (Nat.add_le_add hStar hNonStar) (Nat.le_succ_of_le hClean)
    _ = (k₂ + k₃ + 1) * (D.size + 1) := by
        rw [Nat.add_mul, Nat.add_mul, Nat.one_mul]
