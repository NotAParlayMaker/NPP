import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_2744_1
    (andCase : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
      FanInTwo C →
        (∀ x : Fin (9 : ℕ) → Bool,
          (C.wires (List.ofFn x)).getD (9 : ℕ) Bool.false =
            (x (4 : Fin (9 : ℕ)) || x (6 : Fin (9 : ℕ)))) →
          circuitFun (9 : ℕ) C =
            (fun x : Fin (9 : ℕ) → Bool =>
              x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
                x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
                  x 6 && x 8 || x 8 && x 5) →
            (∃ g : Gate, C.gates[(1 : ℕ)]? = some g ∧ g.op = GateOp.and) →
              (16 : ℕ) ≤ C.size)
    (orCase : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
      FanInTwo C →
        (∀ x : Fin (9 : ℕ) → Bool,
          (C.wires (List.ofFn x)).getD (9 : ℕ) Bool.false =
            (x (4 : Fin (9 : ℕ)) || x (6 : Fin (9 : ℕ)))) →
          circuitFun (9 : ℕ) C =
            (fun x : Fin (9 : ℕ) → Bool =>
              x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
                x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
                  x 6 && x 8 || x 8 && x 5) →
            (∃ g : Gate, C.gates[(1 : ℕ)]? = some g ∧ g.op = GateOp.or) →
              (16 : ℕ) ≤ C.size)
    (notCase : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
      FanInTwo C →
        (∀ x : Fin (9 : ℕ) → Bool,
          (C.wires (List.ofFn x)).getD (9 : ℕ) Bool.false =
            (x (4 : Fin (9 : ℕ)) || x (6 : Fin (9 : ℕ)))) →
          circuitFun (9 : ℕ) C =
            (fun x : Fin (9 : ℕ) → Bool =>
              x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
                x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
                  x 6 && x 8 || x 8 && x 5) →
            (∃ g : Gate, C.gates[(1 : ℕ)]? = some g ∧ g.op = GateOp.not) →
              (16 : ℕ) ≤ C.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (4 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) → (∃ (x5 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[(1 : ℕ)]? = Option.some x5) → (16 : ℕ) ≤ x1.size := by
  intro C hfan hwire hfun ⟨g, hg⟩
  have hmem : g ∈ C.gates := by
    have h1 : 1 < C.gates.length := by
      have := List.getElem?_eq_some_iff.mp hg
      exact this.1
    have : C.gates[1] = g := by
      have := List.getElem?_eq_some_iff.mp hg
      exact this.2
    simpa [this] using List.getElem_mem (n := 1) (l := C.gates) h1
  have hop := (hfan g hmem).1
  rcases hop with hand | hor | hnot
  · exact andCase C hfan hwire hfun ⟨g, hg, hand⟩
  · exact orCase C hfan hwire hfun ⟨g, hg, hor⟩
  · exact notCase C hfan hwire hfun ⟨g, hg, hnot⟩
