import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3061_13
    (h1 : ∀ P S : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo P → PEqualNP.MetaComplexity.FanInTwo S →
      P.output+1 = 8+P.size →
      (∀ x : Fin 8 → Bool, S.eval (P.wires (List.ofFn x) ++ [PEqualNP.MetaComplexity.circuitFun 8 P x]) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4))) →
      13 ≤ P.size+S.size ∧ (P.size+S.size = 13 → 0 < P.size → ∀ a < P.output, ∃ x : Fin 8 → Bool, (P.wires (List.ofFn x)).getD a false ≠ PEqualNP.MetaComplexity.circuitFun 8 P x))
    (h2 : let f := fun x : Fin 8 → Bool => ([1,12,23,4,15,26,37,46,57,74] : List Nat).any (fun e => x (Fin.ofNat 8 (e/10)) && x (Fin.ofNat 8 (e%10)));
      ∀ (P S : PEqualNP.CircuitLowerBounds.Circuit) (b : Bool),
      PEqualNP.MetaComplexity.FanInTwo P → PEqualNP.MetaComplexity.FanInTwo S → P.output+1 = 8+P.size → P.size+S.size = 13 →
      (∀ a < P.output, ∃ x : Fin 8 → Bool, (P.wires (List.ofFn x)).getD a false ≠ PEqualNP.MetaComplexity.circuitFun 8 P x) →
      S.gates.countP (fun g => (if g.op.eval [false,false] then g.inputs.take 1 else g.inputs).contains (8+P.size)) ≤ 3 →
      ∃ x : Fin 8 → Bool, S.eval (P.wires (List.ofFn x) ++ [PEqualNP.MetaComplexity.circuitFun 8 P x]) ≠ f x ∨
      S.eval (P.wires (List.ofFn x) ++ [b]) ≠ (f x || x 0 || x 3)) : have x1 : (Fin (8 : ℕ) → Bool) → Bool := fun (x1 : Fin (8 : ℕ) → Bool) => x1 (0 : Fin (8 : ℕ)) && x1 (1 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (2 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (3 : Fin (8 : ℕ)) || x1 (0 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (5 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (3 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (4 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (5 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (7 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)); have x2 : (Fin (8 : ℕ) → Bool) → Bool := fun (x2 : Fin (8 : ℕ) → Bool) => x1 x2 || x2 (0 : Fin (8 : ℕ)) || x2 (3 : Fin (8 : ℕ)); ∀ (x3 x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : Bool), PEqualNP.MetaComplexity.FanInTwo x3 → PEqualNP.MetaComplexity.FanInTwo x4 → x3.output + (1 : ℕ) = (8 : ℕ) + x3.size → (10 : ℕ) + List.countP (fun (x9 : PEqualNP.CircuitLowerBounds.Gate) => (if x9.op.eval [Bool.false, Bool.false] = Bool.true then List.take (1 : ℕ) x9.inputs else x9.inputs).contains ((8 : ℕ) + x3.size)) x4.gates ≤ x3.size + x4.size → (∀ (x10 : Fin (8 : ℕ)), (PEqualNP.MetaComplexity.circuitFun (8 : ℕ) x3 ≠ fun (x11 : Fin (8 : ℕ) → Bool) => x11 x10) ∧ PEqualNP.MetaComplexity.circuitFun (8 : ℕ) x3 ≠ fun (x11 : Fin (8 : ℕ) → Bool) => !x11 x10) → (∀ (x11 : Fin (8 : ℕ) → Bool), x1 x11 ≠ x2 x11 → PEqualNP.MetaComplexity.circuitFun (8 : ℕ) x3 x11 = !x5) → (∀ (x12 : Fin (8 : ℕ) → Bool), x4.eval (x3.wires (List.ofFn x12) ++ [PEqualNP.MetaComplexity.circuitFun (8 : ℕ) x3 x12]) = x1 x12) → (∀ (x13 : Fin (8 : ℕ) → Bool), x4.eval (x3.wires (List.ofFn x13) ++ [x5]) = x2 x13) → (14 : ℕ) ≤ x3.size + x4.size := by
  dsimp only
  intro P S b hp hs ho hcount hlit _ hn hb
  by_contra small
  obtain ⟨lb, distinct⟩ := h1 P S hp hs ho hn
  have total : P.size + S.size = 13 := by omega
  have pos : 0 < P.size := by
    by_contra hz
    have z : P.size = 0 := by omega
    have emp : P.gates = [] := List.length_eq_zero_iff.mp z
    have idx : P.output = 7 := by omega
    apply (hlit 7).1
    funext x
    change (P.gates.foldl _ (List.ofFn x)).getD P.output false = x 7
    rw [emp,idx]
    rfl
  have count : S.gates.countP (fun g => (if g.op.eval [false,false] then g.inputs.take 1 else g.inputs).contains (8+P.size)) ≤ 3 := by omega
  obtain ⟨x,hx⟩ := h2 P S b hp hs ho total (distinct total pos) count
  have eqv : ∀ x : Fin 8 → Bool, (([1,12,23,4,15,26,37,46,57,74] : List Nat).any (fun e => x (Fin.ofNat 8 (e/10)) && x (Fin.ofNat 8 (e%10)))) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)) := by decide +kernel
  rcases hx with hx | hx
  · exact hx ((hn x).trans (eqv x).symm)
  · apply hx
    dsimp only
    rw [eqv]
    exact hb x
