import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_1665_1
    (tiny : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
      FanInTwo C →
        (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 0)) →
          circuitFun 9 C =
            (fun x : Fin 9 → Bool =>
              (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
                (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
                  (x 6 && x 8) || (x 8 && x 5)) →
            C.size ≤ (1 : ℕ) → False)
    (andCase : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
      FanInTwo C →
        (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 0)) →
          circuitFun 9 C =
            (fun x : Fin 9 → Bool =>
              (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
                (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
                  (x 6 && x 8) || (x 8 && x 5)) →
            (∃ g : Gate, C.gates[(1 : ℕ)]? = some g ∧ g.op = GateOp.and) → (16 : ℕ) ≤ C.size)
    (orCase : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
      FanInTwo C →
        (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 0)) →
          circuitFun 9 C =
            (fun x : Fin 9 → Bool =>
              (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
                (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
                  (x 6 && x 8) || (x 8 && x 5)) →
            (∃ g : Gate, C.gates[(1 : ℕ)]? = some g ∧ g.op = GateOp.or) → (16 : ℕ) ≤ C.size)
    (notCase : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
      FanInTwo C →
        (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 0)) →
          circuitFun 9 C =
            (fun x : Fin 9 → Bool =>
              (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
                (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
                  (x 6 && x 8) || (x 8 && x 5)) →
            (∃ g : Gate, C.gates[(1 : ℕ)]? = some g ∧ g.op = GateOp.not) → (16 : ℕ) ≤ C.size) :
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 0)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size := by
  intro C hfan hwire hfun
  by_cases hsz : C.size ≤ 1
  · exact (tiny C hfan hwire hfun hsz).elim
  · have h1 : 1 < C.gates.length := by
      simp [Circuit.size] at hsz
      omega
    obtain ⟨g, hg⟩ : ∃ g : Gate, C.gates[1]? = some g :=
      ⟨C.gates[1], List.getElem?_eq_getElem h1⟩
    have hmem : g ∈ C.gates := by
      have : C.gates[1] = g := (List.getElem?_eq_some_iff.mp hg).2
      simpa [this] using List.getElem_mem (n := 1) (l := C.gates) h1
    have hop := (hfan g hmem).1
    rcases hop with hand | hor | hnot
    · exact andCase C hfan hwire hfun ⟨g, hg, hand⟩
    · exact orCase C hfan hwire hfun ⟨g, hg, hor⟩
    · exact notCase C hfan hwire hfun ⟨g, hg, hnot⟩
