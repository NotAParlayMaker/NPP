import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_2736_2
    (bound : ∀ D : Circuit, FanInTwo D → (∀ y : Fin 8 → Bool,
      D.eval (List.ofFn y ++ [y 0 && y 3]) =
      ((y 0 && y 1) || (y 1 && y 2) || (y 2 && y 3) || (y 0 && y 4) ||
       (y 1 && y 5) || (y 2 && y 6) || (y 3 && y 7) || (y 4 && y 6) ||
       (y 5 && y 7) || (y 7 && y 4))) → 13 ≤ D.size)
    (pin : ∀ B : Circuit, FanInTwo B → (∀ x : Fin 9 → Bool, B.eval (List.ofFn x ++ [x 0 && x 3]) =
        ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
         (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
         (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) →
      ∃ D : Circuit, FanInTwo D ∧ D.size + B.gates.countP (fun g =>
        g.inputs.head? == some 4 || g.op.eval [true,true] && g.inputs.contains 4) ≤ B.size ∧
        ∀ y : Fin 8 → Bool,
      D.eval (List.ofFn y ++ [y 0 && y 3]) =
      ((y 0 && y 1) || (y 1 && y 2) || (y 2 && y 3) || (y 0 && y 4) ||
       (y 1 && y 5) || (y 2 && y 6) || (y 3 && y 7) || (y 4 && y 6) ||
       (y 5 && y 7) || (y 7 && y 4)))
    (single : ∀ (B : Circuit), FanInTwo B → (∃ g∈B.gates.head?.toList, g.op=.or) →
      B.gates.countP (fun g => g.inputs.head? == some 4 || g.op.eval [true,true] && g.inputs.contains 4) ≤ 1 →
      (∀ x : Fin 9 → Bool, B.eval (List.ofFn x ++ [x 0 && x 3]) =
        ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
         (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
         (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) → 15 ≤ B.size) :
    have x1 : PEqualNP.CircuitLowerBounds.Circuit → ℕ := fun (x1 : PEqualNP.CircuitLowerBounds.Circuit) => List.countP (fun (x2 : PEqualNP.CircuitLowerBounds.Gate) => x2.inputs.head? == Option.some (4 : ℕ) || x2.op.eval [Bool.true, Bool.true] && x2.inputs.contains (4 : ℕ)) x1.gates; have x2 : PEqualNP.CircuitLowerBounds.Circuit → List (Fin (11 : ℕ)) → PEqualNP.CircuitLowerBounds.Circuit := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : List (Fin (11 : ℕ))) => { gates := { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [(0 : ℕ), (3 : ℕ)] : PEqualNP.CircuitLowerBounds.Gate } :: { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := List.map Fin.val x3 : PEqualNP.CircuitLowerBounds.Gate } :: x2.gates, output := x2.output : PEqualNP.CircuitLowerBounds.Circuit }; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : List (Fin (11 : ℕ))),   PEqualNP.MetaComplexity.FanInTwo x3 →     x4.length ≤ (2 : ℕ) →       (∀ (x7 : Fin (9 : ℕ) → Bool),           have x8 : List Bool := List.ofFn x7 ++ [x7 (0 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ))];           x3.eval (x8 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x9 : Fin (11 : ℕ)) => x8.getD (↑x9) Bool.false) x4)]) = (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)))) →         x1 (x2 x3 x4) ≤ (2 : ℕ) → (14 : ℕ) ≤ x3.size := by
  intro hits assembled C is fan ar computes _
  let g : Gate := ⟨.or,is.map Fin.val⟩
  let B : Circuit := ⟨g::C.gates,C.output⟩
  have ok : FanInTwo B := by
    intro h hm
    rcases List.mem_cons.mp hm with rfl|h'
    · exact ⟨by simp [g],by simpa [g] using ar⟩
    · exact fan _ h'
  let f (x : Fin 9 → Bool) := ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
         (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
         (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))
  have ev (x : Fin 9 → Bool) : B.eval (List.ofFn x ++ [x 0 && x 3]) = f x := by
    simpa [B,g,f,Circuit.eval,Circuit.wires,List.map_map,Function.comp_def] using computes x
  let cnt := B.gates.countP (fun h => h.inputs.head? == some 4 || h.op.eval [true,true] && h.inputs.contains 4)
  have sz : B.size=C.size+1 := rfl
  by_cases h : cnt ≤ 1
  · have := single B ok ⟨g,by simp [B],rfl⟩ h ev
    omega
  · obtain ⟨D,df,ds,de⟩ := pin B ok ev
    have := bound D df de
    change D.size + cnt ≤ B.size at ds
    omega
