import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadTwo PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover

-- Every rejecting valuation extends to a rejecting valuation specified by at most
-- three points or three lines. An active AND stays active in the extension.
theorem PEqualNP.Outside.R_meta_4021_823
    (normalize : let shifts : Finset (Fin 13) := {0,1,3,9}; ∀ (C : Circuit), IsAO2 26 C → ∀ (w : Nat) (x : Fin 26 → Bool),
      fpl 13 (fun p l : Fin 13 => p-l ∈ shifts) x = false → wval C x w = true →
      ∃ S : Finset (Fin 13), S.card ≤ 3 ∧
        (wval C (Fin.append (fun p : Fin 13 => decide (p ∈ S)) (fun l : Fin 13 => decide (∀ p ∈ S, p-l ∉ shifts))) w = true ∨ wval C (Fin.append (fun p : Fin 13 => decide (∀ l ∈ S, p-l ∉ shifts)) (fun l : Fin 13 => decide (l ∈ S))) w = true))
    (points : let shifts : Finset (Fin 13) := {0,1,3,9}; ∀ C : Circuit,
      let step := fun (a : Fin 26) (u v : Nat) => ∃ (j : Nat) (g : Gate) (q : Nat),
        v = 26 + j ∧ C.gates[j]? = some g ∧ (g.inputs = [u,q] ∨ g.inputs = [q,u]) ∧
        (g.op = .or ∨ g.op = .and ∧ wval C (fun i : Fin 26 => decide (i=a)) q = true)
      C.size ≤ 64 → IsAO2 26 C → (∀ g ∈ C.gates, g.inputs.Nodup) →
      circuitFun 26 C = fpl 13 (fun p l : Fin 13 => p-l ∈ shifts) → 0 < andPairs 26 C →
      ∀ k < C.gates.length, (gateAt C k).op = .and → ∀ S : Finset (Fin 13), S.card ≤ 3 →
      wval C (Fin.append (fun p : Fin 13 => decide (p ∈ S)) (fun l : Fin 13 => decide (∀ p ∈ S, p-l ∉ shifts))) (26+k) = true → Relation.ReflTransGen (step 0) 13 C.output ∨ Relation.ReflTransGen (step 13) 0 C.output)
    (lines : let shifts : Finset (Fin 13) := {0,1,3,9}; ∀ C : Circuit,
      let step := fun (a : Fin 26) (u v : Nat) => ∃ (j : Nat) (g : Gate) (q : Nat),
        v = 26 + j ∧ C.gates[j]? = some g ∧ (g.inputs = [u,q] ∨ g.inputs = [q,u]) ∧
        (g.op = .or ∨ g.op = .and ∧ wval C (fun i : Fin 26 => decide (i=a)) q = true)
      C.size ≤ 64 → IsAO2 26 C → (∀ g ∈ C.gates, g.inputs.Nodup) →
      circuitFun 26 C = fpl 13 (fun p l : Fin 13 => p-l ∈ shifts) → 0 < andPairs 26 C →
      ∀ k < C.gates.length, (gateAt C k).op = .and → ∀ S : Finset (Fin 13), S.card ≤ 3 →
      wval C (Fin.append (fun p : Fin 13 => decide (∀ l ∈ S, p-l ∉ shifts)) (fun l : Fin 13 => decide (l ∈ S))) (26+k) = true → Relation.ReflTransGen (step 0) 13 C.output ∨ Relation.ReflTransGen (step 13) 0 C.output) :
    have x1 : PEqualNP.CircuitLowerBounds.Circuit → Fin (26 : ℕ) → ℕ → ℕ → Prop := fun (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (26 : ℕ)) (x3 x4 : ℕ) => ∃ (x5 : ℕ) (x6 : PEqualNP.CircuitLowerBounds.Gate) (x7 : ℕ), x4 = (26 : ℕ) + x5 ∧ x1.gates[x5]? = Option.some x6 ∧ (x6.inputs = [x3, x7] ∨ x6.inputs = [x7, x3]) ∧ (x6.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ x6.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x1.wires (List.ofFn fun (x8 : Fin (26 : ℕ)) => Decidable.decide (x8 = x2))).getD x7 Bool.false = Bool.true); have x2 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => x3.size ≤ (64 : ℕ) ∧ PEqualNP.TopForm.IsAO2 (26 : ℕ) x3 ∧ (∀ x4 ∈ x3.gates, x4.inputs.Nodup) ∧ (∀ (x4 : Fin (26 : ℕ) → Bool), x3.eval (List.ofFn x4) = Bool.true ↔ ∃ (x5 : Fin (13 : ℕ)) (x6 : Fin (13 : ℕ)), x5 - x6 ∈ x2 ∧ x4 (Fin.castAdd (13 : ℕ) x5) = Bool.true ∧ x4 (Fin.natAdd (13 : ℕ) x6) = Bool.true) ∧ (0 : ℕ) < PEqualNP.TopForm.andPairs (26 : ℕ) x3 ∧ ∃ x4 < x3.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ∃ (x5 : Fin (26 : ℕ) → Bool), (x3.wires (List.ofFn x5)).getD ((26 : ℕ) + x4) Bool.false = Bool.true ∧ x3.eval (List.ofFn x5) = Bool.false; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), x3 x4 → Relation.ReflTransGen (x1 x4 (0 : Fin (26 : ℕ))) (13 : ℕ) x4.output ∨ Relation.ReflTransGen (x1 x4 (13 : Fin (26 : ℕ))) (0 : ℕ) x4.output := by
  dsimp only
  intro C h
  obtain ⟨size,legal,nodup,correct,positive,k,hk,op,x,hgate,hfalse⟩ := h
  have computes : circuitFun 26 C = fpl 13 (fun p l : Fin 13 => p-l ∈ ({0,1,3,9} : Finset (Fin 13))) := by
    funext z
    apply Bool.eq_iff_iff.mpr
    exact (correct z).trans ⟨fun h => decide_eq_true h, fun h => of_decide_eq_true h⟩
  have neg : fpl 13 (fun p l : Fin 13 => p-l ∈ ({0,1,3,9} : Finset (Fin 13))) x = false := by
    rw [← computes]
    exact hfalse
  obtain ⟨S,small,hp | hl⟩ := normalize C legal (26+k) x neg hgate
  · exact points C size legal nodup computes positive k hk op S small hp
  · exact lines C size legal nodup computes positive k hk op S small hl
