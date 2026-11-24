import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

-- Cut at the normal form where the nested AND reads an AND directly.
theorem PEqualNP.Outside.R_meta_1749_3
    (hNF : have E : Finset (Fin 13) := {0, 1, 3, 9};
have Cor : Circuit → Prop := fun C =>
  (∀ p q : Fin 13, p - q ∈ E → C.eval ((List.ofFn fun i => decide (i = p)) ++ List.ofFn fun i => decide (i = q)) = true) ∧
  ∀ S : Finset (Fin 13), S.card = 4 → (∀ r : Fin 13, {x ∈ S | x - r ∈ E}.card ≤ 2) →
    C.eval ((List.ofFn fun i => decide (i ∈ S)) ++ List.ofFn fun i => decide (∀ x ∈ S, x - i ∉ E)) = false;
have Dir : Circuit → Prop := fun C =>
  ∃ i j, (gateAt C i).op = GateOp.and ∧ (gateAt C j).op = GateOp.and ∧ 26 + i ∈ (gateAt C j).inputs;
∀ C : Circuit, Monotone2 C → ReadsBack 26 C → Cor C → C.size < 64 → (∃ i j, (gateAt C i).op = GateOp.and ∧ (gateAt C j).op = GateOp.and ∧ InCone 26 C i j) →
∃ C' : Circuit, Monotone2 C' ∧ ReadsBack 26 C' ∧ Cor C' ∧ C'.size = C.size ∧ Dir C')
    (hDirect : have E : Finset (Fin 13) := {0, 1, 3, 9};
have Cor : Circuit → Prop := fun C =>
  (∀ p q : Fin 13, p - q ∈ E → C.eval ((List.ofFn fun i => decide (i = p)) ++ List.ofFn fun i => decide (i = q)) = true) ∧
  ∀ S : Finset (Fin 13), S.card = 4 → (∀ r : Fin 13, {x ∈ S | x - r ∈ E}.card ≤ 2) →
    C.eval ((List.ofFn fun i => decide (i ∈ S)) ++ List.ofFn fun i => decide (∀ x ∈ S, x - i ∉ E)) = false;
have Dir : Circuit → Prop := fun C =>
  ∃ i j, (gateAt C i).op = GateOp.and ∧ (gateAt C j).op = GateOp.and ∧ 26 + i ∈ (gateAt C j).inputs;
∀ C : Circuit, Monotone2 C → ReadsBack 26 C → Cor C → C.size < 64 → Dir C →
∃ D : Circuit, Monotone2 D ∧ ReadsBack 26 D ∧ Cor D ∧ D.size < C.size) : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => (∀ (x3 x4 : Fin (13 : ℕ)), x3 - x4 ∈ x1 → x2.eval ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x4)) = Bool.true) ∧ ∀ (x3 : Finset (Fin (13 : ℕ))), x3.card = (4 : ℕ) → (∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x3 | x6 - x5 ∈ x1}.card ≤ (2 : ℕ)) → x2.eval ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 ∈ x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (∀ x7 ∈ x3, x7 - x6 ∉ x1)) = Bool.false; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => ∃ (x4 : ℕ) (x5 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x5).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x3 x4 x5; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x4 → x2 x4 → x4.size < (64 : ℕ) → x3 x4 → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x10 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x10 ∧ x2 x10 ∧ x10.size < x4.size := by
  intro y1 y2 y3 C hmon hback hcor hsize hnested
  obtain ⟨C', hmC', hbC', hcC', hsz, hdir⟩ := hNF C hmon hback hcor hsize hnested
  have hsize' : C'.size < 64 := by omega
  obtain ⟨D, hmD, hbD, hcD, hsmall⟩ := hDirect C' hmC' hbC' hcC' hsize' hdir
  exact ⟨D, hmD, hbD, hcD, by simpa [hsz] using hsmall⟩
