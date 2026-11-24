import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm

-- First move each safe AND to the output layer on the given sample set.
-- The remaining transformation handles repeated line factors in that form.
theorem PEqualNP.Outside.R_meta_1692_7
    (cleanNormalize : let D : Finset (Fin 13) := {0, 1, 3, 9}
      let Quad := fun (Q : Finset (Fin 13)) =>
        Q.card = 4 ∧ ∀ k : Fin 13, (Q.filter (fun p => p - k ∈ D)).card ≤ 2
      let Neg := fun (Q : Finset (Fin 13)) =>
        Fin.append (fun p : Fin 13 => decide (p ∈ Q))
          (fun l : Fin 13 => decide (∀ p ∈ Q, p - l ∉ D))
      let Correct := fun C : Circuit =>
        (∀ p l : Fin 13, p - l ∈ D → C.eval (List.ofFn (Fin.append
          (fun u : Fin 13 => decide (u = p)) (fun v : Fin 13 => decide (v = l)))) = true) ∧
        (∀ Q : Finset (Fin 13), Quad Q → C.eval (List.ofFn (Neg Q)) = false)
      let CleanTop := fun C : Circuit => ∀ i j,
        (gateAt C i).op = GateOp.and → (gateAt C j).op = GateOp.and →
        (∀ Q, Quad Q → gateVal 26 C i (Neg Q) = false) → ¬ InCone 26 C i j
      ∀ C : Circuit, Monotone2 C → ReadsBack 26 C → Correct C →
        ∃ D : Circuit, IsAO2 26 D ∧ D.size ≤ C.size ∧ Correct D ∧ CleanTop D)
    (bound : let D : Finset (Fin 13) := {0, 1, 3, 9}
      let Quad := fun (Q : Finset (Fin 13)) =>
        Q.card = 4 ∧ ∀ k : Fin 13, (Q.filter (fun p => p - k ∈ D)).card ≤ 2
      let Neg := fun (Q : Finset (Fin 13)) =>
        Fin.append (fun p : Fin 13 => decide (p ∈ Q))
          (fun l : Fin 13 => decide (∀ p ∈ Q, p - l ∉ D))
      let Correct := fun C : Circuit =>
        (∀ p l : Fin 13, p - l ∈ D → C.eval (List.ofFn (Fin.append
          (fun u : Fin 13 => decide (u = p)) (fun v : Fin 13 => decide (v = l)))) = true) ∧
        (∀ Q : Finset (Fin 13), Quad Q → C.eval (List.ofFn (Neg Q)) = false)
      ∀ C : Circuit, Monotone2 C → Correct C →
        HasLineDegree 26 (Finset.Ico 13 26) C 1 → 64 ≤ C.size)
    (lineNormalize : let D : Finset (Fin 13) := {0, 1, 3, 9}
      let Quad := fun (Q : Finset (Fin 13)) =>
        Q.card = 4 ∧ ∀ k : Fin 13, (Q.filter (fun p => p - k ∈ D)).card ≤ 2
      let Neg := fun (Q : Finset (Fin 13)) =>
        Fin.append (fun p : Fin 13 => decide (p ∈ Q))
          (fun l : Fin 13 => decide (∀ p ∈ Q, p - l ∉ D))
      let Correct := fun C : Circuit =>
        (∀ p l : Fin 13, p - l ∈ D → C.eval (List.ofFn (Fin.append
          (fun u : Fin 13 => decide (u = p)) (fun v : Fin 13 => decide (v = l)))) = true) ∧
        (∀ Q : Finset (Fin 13), Quad Q → C.eval (List.ofFn (Neg Q)) = false)
      let CleanTop := fun C : Circuit => ∀ i j,
        (gateAt C i).op = GateOp.and → (gateAt C j).op = GateOp.and →
        (∀ Q, Quad Q → gateVal 26 C i (Neg Q) = false) → ¬ InCone 26 C i j
      ∀ C : Circuit, IsAO2 26 C → Correct C → CleanTop C → C.size < 64 →
        ∃ D : Circuit, Monotone2 D ∧ Correct D ∧
          HasLineDegree 26 (Finset.Ico 13 26) D 1 ∧ D.size ≤ C.size) :

    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < 26 + (i : ℕ)) → (∀ p l : Fin 13, p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out⟩ (List.ofFn (fun u1 : Fin 13 => decide (u1 = p)) ++ List.ofFn (fun v1 : Fin 13 => decide (v1 = l))) = true) → (∀ Q : Finset (Fin 13), Q.card = 4 → (∀ k : Fin 13, (Q.filter (fun u0 : Fin 13 => u0 - k ∈ ({0, 1, 3, 9} : Finset (Fin 13)))).card ≤ 2) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out⟩ (List.ofFn (fun u2 : Fin 13 => decide (u2 ∈ Q)) ++ List.ofFn (fun v2 : Fin 13 => decide (∀ r ∈ Q, r - v2 ∉ ({0, 1, 3, 9} : Finset (Fin 13))))) = false) → 64 ≤ gates.length := by
  intro gates out hops hreads hp hn
  let C : Circuit := ⟨gates, out⟩
  have hm : Monotone2 C := by
    change ∀ g ∈ gates, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hops
  have hr : ReadsBack 26 C := by
    intro j hj w hw
    have hj' : j < gates.length := hj
    change w ∈ (gates.getD j ⟨GateOp.or, []⟩).inputs at hw
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj'] at hw
    exact hreads ⟨j, hj'⟩ w hw
  have right_pos (p l : Fin 13) (h : p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13))) :
      C.eval (List.ofFn (Fin.append (fun u : Fin 13 => decide (u = p))
        (fun v : Fin 13 => decide (v = l)))) = true := by
    rw [List.ofFn_fin_append]
    exact hp p l h
  have right_neg (Q : Finset (Fin 13)) (hc : Q.card = 4)
      (ha : ∀ k : Fin 13, (Q.filter (fun p => p - k ∈ ({0, 1, 3, 9} : Finset (Fin 13)))).card ≤ 2) :
      C.eval (List.ofFn (Fin.append (fun p : Fin 13 => decide (p ∈ Q))
        (fun l : Fin 13 => decide (∀ p ∈ Q, p - l ∉ ({0, 1, 3, 9} : Finset (Fin 13)))))) = false := by
    rw [List.ofFn_fin_append]
    exact hn Q hc ha
  obtain ⟨T, htao, htsize, ht, htop⟩ :=
    cleanNormalize C hm hr ⟨right_pos, fun Q hQ => right_neg Q hQ.1 hQ.2⟩
  by_contra hsmall
  have hCsmall : C.size < 64 := Nat.lt_of_not_ge hsmall
  obtain ⟨E, hem, he, hedge, hesize⟩ :=
    lineNormalize T htao ht htop (htsize.trans_lt hCsmall)
  have hbound := bound E hem he hedge
  omega
