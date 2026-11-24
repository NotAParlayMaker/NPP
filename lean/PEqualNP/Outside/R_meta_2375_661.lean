import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
theorem PEqualNP.Outside.R_meta_2375_661
    (late : ∀ (first : Gate) (tail : Circuit) (a b : ℕ),
      FanInTwo ⟨[first],0⟩ → FanInTwo tail → have target (x : Fin 10 → Bool) := ([3,6,12,24,17,33,66,132,264,528,160,640,576,320,288] : List ℕ).any (fun mask => decide (∀ i : Fin 10, mask.testBit i.val = true → x i = true));
      have wire (x : Fin 10 → Bool) (i : ℕ) :=
        (tail.wires ((⟨[first],0⟩ : Circuit).wires (List.ofFn x))).getD i false;
      (∃ x, wire x b = false) →
      (∃ x, wire x a = false) →
      (∀ x, target x = true → wire x a = true ∧ wire x b = true) →
      ¬ (∃ x, target x = false ∧ wire x a = true ∧ wire x b = true) → 14≤a ∧ 14≤b ∧ (18≤a∨18≤b) ∧ (first.op=GateOp.not → 15≤a ∧ 15≤b ∧ (19≤a∨19≤b)))
    (residual : ∀ (first : Gate) (tail : Circuit) (a b : ℕ),
      FanInTwo ⟨[first],0⟩ → FanInTwo tail → tail.size ≤ 17 → have target (x : Fin 10 → Bool) := ([3,6,12,24,17,33,66,132,264,528,160,640,576,320,288] : List ℕ).any (fun mask => decide (∀ i : Fin 10, mask.testBit i.val = true → x i = true));
      have wire (x : Fin 10 → Bool) (i : ℕ) :=
        (tail.wires ((⟨[first],0⟩ : Circuit).wires (List.ofFn x))).getD i false;
      (∃ x, wire x a = true ∧ wire x b = false) →
      (∃ x, wire x a = false ∧ wire x b = true) →
      (∀ x, target x = true → wire x a = true ∧ wire x b = true) →
      (14≤a ∧ 14≤b ∧ (18≤a∨18≤b) ∧ (first.op=GateOp.not → 15≤a ∧ 15≤b ∧ (19≤a∨19≤b))) → ∃ x, target x = false ∧ wire x a = true ∧ wire x b = true) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Gate) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),   PEqualNP.MetaComplexity.FanInTwo { gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →     PEqualNP.MetaComplexity.FanInTwo x2 →       x2.size ≤ (17 : ℕ) →         have x8 : (Fin (10 : ℕ) → Bool) → Bool := fun (x8 : Fin (10 : ℕ) → Bool) => x8 (0 : Fin (10 : ℕ)) && x8 (1 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (2 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (3 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (4 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (0 : Fin (10 : ℕ)) || x8 (0 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (5 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (7 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (9 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (6 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (8 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ));         have x9 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x9 : Fin (10 : ℕ) → Bool) (x10 : ℕ) => (x2.wires ({ gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x9))).getD x10 Bool.false;         (∃ (x10 : Fin (10 : ℕ) → Bool), x9 x10 x3 = Bool.true ∧ x9 x10 x4 = Bool.false) → (∃ (x11 : Fin (10 : ℕ) → Bool), x9 x11 x3 = Bool.false ∧ x9 x11 x4 = Bool.true) → (∀ (x12 : Fin (10 : ℕ) → Bool), x8 x12 = Bool.true → x9 x12 x3 = Bool.true ∧ x9 x12 x4 = Bool.true) → ∃ (x13 : Fin (10 : ℕ) → Bool), x8 x13 = Bool.false ∧ x9 x13 x3 = Bool.true ∧ x9 x13 x4 = Bool.true := by
  intro first tail a b firstFan fan small target wire leftOnly rightOnly positives
  let listed (x : Fin 10 → Bool) := ([3,6,12,24,17,33,66,132,264,528,160,640,576,320,288] : List ℕ).any (fun mask => decide (∀ i : Fin 10, mask.testBit i.val = true → x i = true))
  have same : ∀ x : Fin 10→Bool,target x=listed x := by
    dsimp only [target,listed]
    decide +kernel
  have trueRows (x : Fin 10 → Bool) (h : listed x = true) :
      wire x a = true ∧ wire x b = true := positives x ((same x).trans h)
  by_contra absent
  have none : ¬∃ x, listed x = false ∧ wire x a = true ∧ wire x b = true := by
    rintro ⟨x,off,onA,onB⟩
    exact absent ⟨x,(same x).trans off,onA,onB⟩
  have bOff : ∃ x,wire x b=false := leftOnly.imp (fun x h=>h.2)
  have aOff : ∃ x,wire x a=false := rightOnly.imp (fun x h=>h.1)
  have bounds := late first tail a b firstFan fan bOff aOff trueRows none
  exact none (residual first tail a b firstFan fan small leftOnly rightOnly trueRows bounds)
