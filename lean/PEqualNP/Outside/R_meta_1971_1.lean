import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Cut the residual of L-meta-1745 by how many ordinary vertices are
-- under-read: either two or more vertices are read at most once, or some
-- vertex is read exactly twice, or the unique under-read vertex is the
-- only exception to a three-reader bound. The last case is the slot-count
-- argument; the first two need a count over several vertices.
theorem PEqualNP.Outside.R_meta_1971_1
    (twoLow :
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (f : (Fin n → Bool) → Bool)
        (C : PEqualNP.CircuitLowerBounds.Circuit),
        let readers := fun v : Fin n =>
          C.gates.filter fun g =>
            (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains (v : ℕ)
        (∀ v ∉ A, (G.neighborSet v).ncard = 3) →
        (∀ (v : Fin n) (w : G.Walk v v), w.IsCycle → 7 ≤ w.length) →
        (∀ u v : Fin n, G.Adj u v → u ∉ A) →
        (∃ u v : Fin n, G.Adj u v) →
        (∀ x : Fin n → Bool, f x = true ↔
          (∃ a ∈ A, x a = true) ∨ ∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true) →
        PEqualNP.MetaComplexity.FanInTwo C →
        PEqualNP.MetaComplexity.circuitFun n C = f →
        (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize n f s → C.size ≤ s) →
        (∀ v ∉ A, (readers v).length ≤ 3 ∧
          ((readers v).length = 3 → ∀ g ∈ readers v, g.op = PEqualNP.CircuitLowerBounds.GateOp.or)) →
        (∃ v ∉ A, (readers v).length ≤ 1) →
        (∃ u ∉ A, ∃ v ∉ A, u ≠ v ∧ (readers u).length ≤ 1 ∧ (readers v).length ≤ 1) →
        ∃ v ∉ A, ∃ s : ℕ, s + 4 ≤ C.size ∧
          PEqualNP.MetaComplexity.HasCircuitSize n (fun x => f (Function.update x v false)) s)
    (twoReads :
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (f : (Fin n → Bool) → Bool)
        (C : PEqualNP.CircuitLowerBounds.Circuit),
        let readers := fun v : Fin n =>
          C.gates.filter fun g =>
            (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains (v : ℕ)
        (∀ v ∉ A, (G.neighborSet v).ncard = 3) →
        (∀ (v : Fin n) (w : G.Walk v v), w.IsCycle → 7 ≤ w.length) →
        (∀ u v : Fin n, G.Adj u v → u ∉ A) →
        (∃ u v : Fin n, G.Adj u v) →
        (∀ x : Fin n → Bool, f x = true ↔
          (∃ a ∈ A, x a = true) ∨ ∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true) →
        PEqualNP.MetaComplexity.FanInTwo C →
        PEqualNP.MetaComplexity.circuitFun n C = f →
        (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize n f s → C.size ≤ s) →
        (∀ v ∉ A, (readers v).length ≤ 3 ∧
          ((readers v).length = 3 → ∀ g ∈ readers v, g.op = PEqualNP.CircuitLowerBounds.GateOp.or)) →
        (∃ v ∉ A, (readers v).length ≤ 1) →
        (∃ v ∉ A, (readers v).length = 2) →
        ∃ v ∉ A, ∃ s : ℕ, s + 4 ≤ C.size ∧
          PEqualNP.MetaComplexity.HasCircuitSize n (fun x => f (Function.update x v false)) s)
    (tight :
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (f : (Fin n → Bool) → Bool)
        (C : PEqualNP.CircuitLowerBounds.Circuit),
        let readers := fun v : Fin n =>
          C.gates.filter fun g =>
            (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains (v : ℕ)
        (∀ v ∉ A, (G.neighborSet v).ncard = 3) →
        (∀ (v : Fin n) (w : G.Walk v v), w.IsCycle → 7 ≤ w.length) →
        (∀ u v : Fin n, G.Adj u v → u ∉ A) →
        (∃ u v : Fin n, G.Adj u v) →
        (∀ x : Fin n → Bool, f x = true ↔
          (∃ a ∈ A, x a = true) ∨ ∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true) →
        PEqualNP.MetaComplexity.FanInTwo C →
        PEqualNP.MetaComplexity.circuitFun n C = f →
        (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize n f s → C.size ≤ s) →
        (∀ v ∉ A, (readers v).length ≤ 3 ∧
          ((readers v).length = 3 → ∀ g ∈ readers v, g.op = PEqualNP.CircuitLowerBounds.GateOp.or)) →
        (∃ v0 ∉ A, (readers v0).length ≤ 1 ∧
          ∀ a ∉ A, a ≠ v0 → (readers a).length = 3) →
        ∃ v ∉ A, ∃ s : ℕ, s + 4 ≤ C.size ∧
          PEqualNP.MetaComplexity.HasCircuitSize n (fun x => f (Function.update x v false)) s) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)) (x4 : (Fin x1 → Bool) → Bool) (x5 : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ x6 ∉ x3, (x2.neighborSet x6).ncard = (3 : ℕ)) →
      (∀ (x7 : Fin x1) (x8 : x2.Walk x7 x7), x8.IsCycle → (7 : ℕ) ≤ x8.length) →
      (∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → x8 ∉ x3) →
      (∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10) →
      (∀ (x10 : Fin x1 → Bool), x4 x10 = Bool.true ↔ (∃ x11 ∈ x3, x10 x11 = Bool.true) ∨
        ∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12 ∧ x10 x11 = Bool.true ∧ x10 x12 = Bool.true) →
      PEqualNP.MetaComplexity.FanInTwo x5 →
      PEqualNP.MetaComplexity.circuitFun x1 x5 = x4 →
      (∀ (x13 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x4 x13 → x5.size ≤ x13) →
      (∀ x14 ∉ x3,
        have x16 : List PEqualNP.CircuitLowerBounds.Gate :=
          List.filter (fun (x16 : PEqualNP.CircuitLowerBounds.Gate) =>
            (List.take (bif x16.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x16.inputs).contains ↑x14)
            x5.gates;
        x16.length ≤ (3 : ℕ) ∧ (x16.length = (3 : ℕ) → ∀ x18 ∈ x16, x18.op = PEqualNP.CircuitLowerBounds.GateOp.or)) →
      (∃ x15 ∉ x3,
        (List.filter (fun (x16 : PEqualNP.CircuitLowerBounds.Gate) =>
          (List.take (bif x16.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x16.inputs).contains ↑x15)
          x5.gates).length ≤ (1 : ℕ)) →
      ∃ x16 ∉ x3, ∃ (x17 : ℕ), x17 + (4 : ℕ) ≤ x5.size ∧
        PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x18 : Fin x1 → Bool) => x4 (Function.update x18 x16 Bool.false)) x17 := by
  intro n G A f C hdeg hgirth hc hE hf hC heval hmin hread hlow
  let readers : Fin n → List Gate := fun v =>
    C.gates.filter fun g =>
      (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains (v : ℕ)
  by_cases hTwo : ∃ u ∉ A, ∃ v ∉ A, u ≠ v ∧ (readers u).length ≤ 1 ∧ (readers v).length ≤ 1
  · exact twoLow n G A f C hdeg hgirth hc hE hf hC heval hmin hread hlow hTwo
  by_cases hEq2 : ∃ v ∉ A, (readers v).length = 2
  · exact twoReads n G A f C hdeg hgirth hc hE hf hC heval hmin hread hlow hEq2
  apply tight n G A f C hdeg hgirth hc hE hf hC heval hmin hread
  obtain ⟨v0, hv0A, hv0r⟩ := hlow
  have hv0r' : (readers v0).length ≤ 1 := by simpa [readers] using hv0r
  refine ⟨v0, hv0A, hv0r', ?_⟩
  intro a ha hne
  have hle : (readers a).length ≤ 3 := by simpa [readers] using (hread a ha).1
  have n2 : (readers a).length ≠ 2 := fun h => hEq2 ⟨a, ha, h⟩
  have n01 : ¬ (readers a).length ≤ 1 := by
    intro h
    exact hTwo ⟨v0, hv0A, a, ha, hne.symm, hv0r', h⟩
  revert hle n2 n01
  generalize hL : (readers a).length = L
  intro hle n2 n01
  match L with
  | 0 => exact (n01 (by decide)).elim
  | 1 => exact (n01 (by decide)).elim
  | 2 => exact (n2 rfl).elim
  | 3 => rfl
  | n + 4 => exact (Nat.not_succ_le_self 3 (by omega)).elim
