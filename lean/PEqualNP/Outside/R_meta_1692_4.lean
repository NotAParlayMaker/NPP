import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.R_meta_1692_4 :
  (let D : Finset (Fin 13) := {0,1,3,9}
    let off := fun (T : Finset (Fin 13)) => Finset.univ.filter (fun p : Fin 13 => ∀ l ∈ T, p-l ∉ D)
    ∀ T : Finset (Fin 13), T.card = 3 → (¬ ∃ p : Fin 13, ∀ l ∈ T, p-l ∈ D) →
      (off T).card = 4 ∧ (∀ l : Fin 13, ((off T).filter fun p => p-l ∈ D).card ≤ 2) ∧
        ∀ l : Fin 13, (∀ p ∈ off T, p-l ∉ D) ↔ l ∈ T) →
  (let D : Finset (Fin 13) := {0,1,3,9}
    let off := fun (T : Finset (Fin 13)) => Finset.univ.filter (fun p : Fin 13 => ∀ l ∈ T, p-l ∉ D)
    ∀ C : Circuit, PEqualNP.MetaComplexity.Monotone2 C →
      (∀ j : Fin C.gates.length, ∀ i ∈ (C.gates.get j).inputs, i < 26+j.val) →
      (∀ p l : Fin 13, p-l ∈ D → C.eval ((List.ofFn fun i : Fin 13 => decide (i=p)) ++
        List.ofFn fun i : Fin 13 => decide (i=l)) = true) →
      (∀ T : Finset (Fin 13), T.card = 3 → (¬ ∃ p : Fin 13, ∀ l ∈ T, p-l ∈ D) →
        C.eval ((List.ofFn fun i : Fin 13 => decide (i ∈ off T)) ++
          List.ofFn fun i : Fin 13 => decide (i ∈ T)) = false) → 64 ≤ C.size) →
  ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < 26 + (i : ℕ)) → (∀ p l : Fin 13, p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out⟩ (List.ofFn (fun u1 : Fin 13 => decide (u1 = p)) ++ List.ofFn (fun v1 : Fin 13 => decide (v1 = l))) = true) → (∀ Q : Finset (Fin 13), Q.card = 4 → (∀ k : Fin 13, (Q.filter (fun u0 : Fin 13 => u0 - k ∈ ({0, 1, 3, 9} : Finset (Fin 13)))).card ≤ 2) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out⟩ (List.ofFn (fun u2 : Fin 13 => decide (u2 ∈ Q)) ++ List.ofFn (fun v2 : Fin 13 => decide (∀ r ∈ Q, r - v2 ∉ ({0, 1, 3, 9} : Finset (Fin 13))))) = false) → 64 ≤ gates.length := by
  intro geom bound gs out hm hw hp hn
  apply bound ⟨gs,out⟩ hm hw hp
  intro T ht nc
  obtain ⟨card, arc, recover⟩ := geom T ht nc
  simpa only [recover] using hn _ card arc
