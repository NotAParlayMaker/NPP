import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.CircuitMoves

theorem PEqualNP.Outside.R_meta_1692_537
    (hErase : ∀ (C : Circuit) (j p : ℕ),
      Monotone2 C → ReadsBack 26 C → j < C.gates.length →
      (gateAt C j).op = GateOp.and → p ∈ (gateAt C j).inputs →
      let D := eraseGate 26 C j p
      Monotone2 D ∧ ReadsBack 26 D ∧ D.size < C.size ∧
      ∀ x : List Bool, x.length = 26 →
        (C.eval x = true → D.eval x = true) ∧
        ((C.wires x).getD (26+j) false = (C.wires x).getD p false → D.eval x = C.eval x))
    (hBound :
      let D : Finset (Fin 13) := {0, 1, 3, 9}
      let P (p l : Fin 13) := List.ofFn (fun u : Fin 13 => decide (u = p)) ++
        List.ofFn (fun v : Fin 13 => decide (v = l))
      let N (Q : Finset (Fin 13)) := List.ofFn (fun u : Fin 13 => decide (u ∈ Q)) ++
        List.ofFn (fun v : Fin 13 => decide (∀ r ∈ Q, r - v ∉ D))
      let Good (Q : Finset (Fin 13)) :=
        Q.card = 4 ∧ ∀ k : Fin 13, (Q.filter (fun u => u - k ∈ D)).card ≤ 2
      ∀ C : Circuit, Monotone2 C → ReadsBack 26 C →
        (∀ p l : Fin 13, p - l ∈ D → C.eval (P p l) = true) →
        (∀ Q : Finset (Fin 13), Good Q → C.eval (N Q) = false) →
        (∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
          ∀ p ∈ (gateAt C j).inputs, ∃ Q : Finset (Fin 13), Good Q ∧
            (C.wires (N Q)).getD (26+j) false ≠ (C.wires (N Q)).getD p false) →
        64 ≤ C.size) :
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < 26 + (i : ℕ)) → (∀ p l : Fin 13, p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out⟩ (List.ofFn (fun u1 : Fin 13 => decide (u1 = p)) ++ List.ofFn (fun v1 : Fin 13 => decide (v1 = l))) = true) → (∀ Q : Finset (Fin 13), Q.card = 4 → (∀ k : Fin 13, (Q.filter (fun u0 : Fin 13 => u0 - k ∈ ({0, 1, 3, 9} : Finset (Fin 13)))).card ≤ 2) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out⟩ (List.ofFn (fun u2 : Fin 13 => decide (u2 ∈ Q)) ++ List.ofFn (fun v2 : Fin 13 => decide (∀ r ∈ Q, r - v2 ∉ ({0, 1, 3, 9} : Finset (Fin 13))))) = false) → 64 ≤ gates.length := by
  intro gates out hOp hRead hPos hNeg
  let D : Finset (Fin 13) := {0, 1, 3, 9}
  let P (p l : Fin 13) := List.ofFn (fun u : Fin 13 => decide (u = p)) ++
    List.ofFn (fun v : Fin 13 => decide (v = l))
  let N (Q : Finset (Fin 13)) := List.ofFn (fun u : Fin 13 => decide (u ∈ Q)) ++
    List.ofFn (fun v : Fin 13 => decide (∀ r ∈ Q, r - v ∉ D))
  let Good (Q : Finset (Fin 13)) :=
    Q.card = 4 ∧ ∀ k : Fin 13, (Q.filter (fun u => u - k ∈ D)).card ≤ 2
  let Pos (C : Circuit) := ∀ p l : Fin 13, p - l ∈ D → C.eval (P p l) = true
  let Neg (C : Circuit) := ∀ Q : Finset (Fin 13), Good Q → C.eval (N Q) = false
  let Essential (C : Circuit) :=
    ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      ∀ p ∈ (gateAt C j).inputs, ∃ Q : Finset (Fin 13), Good Q ∧
        (C.wires (N Q)).getD (26+j) false ≠ (C.wires (N Q)).getD p false
  have lower : ∀ s : ℕ, ∀ C : Circuit, C.size = s →
      Monotone2 C → ReadsBack 26 C → Pos C → Neg C → 64 ≤ C.size := by
    intro s
    induction s using Nat.strong_induction_on with
    | ind s ih =>
      intro C hs hm hb hp hn
      by_cases he : Essential C
      · exact hBound C hm hb hp hn he
      · unfold Essential at he
        push_neg at he
        obtain ⟨j, hj, hop, p, hmem, hsame⟩ := he
        obtain ⟨hm', hb', hsmaller, hev⟩ := hErase C j p hm hb hj hop hmem
        let C' := eraseGate 26 C j p
        have hp' : Pos C' := by
          intro u v huv
          exact (hev (P u v) (by simp [P])).1 (hp u v huv)
        have hn' : Neg C' := by
          intro Q hQ
          exact ((hev (N Q) (by simp [N])).2 (hsame Q hQ)).trans (hn Q hQ)
        have hsmall : C'.size < s := hs ▸ hsmaller
        have hbnd := ih C'.size hsmall C' rfl hm' hb' hp' hn'
        omega
  let C : Circuit := ⟨gates, out⟩
  have hMono : Monotone2 C := by
    change ∀ g ∈ gates, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hOp
  have hBack : ReadsBack 26 C := by
    intro j hj w hw
    have hj' : j < gates.length := hj
    change w ∈ (gates.getD j ⟨GateOp.or, []⟩).inputs at hw
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj'] at hw
    exact hRead ⟨j, hj'⟩ w hw
  exact lower C.size C rfl hMono hBack hPos (fun Q hQ => hNeg Q hQ.1 hQ.2)
