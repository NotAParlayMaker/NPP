import Mathlib.Data.List.GetD
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2500000 in
theorem PEqualNP.Outside.R_meta_3553_417
    (restrictedLower : ¬PEqualNP.MetaComplexity.HasCircuitSize (7 : ℕ) (fun (x1 : Fin (7 : ℕ) → Bool) => x1 (0 : Fin (7 : ℕ)) && x1 (1 : Fin (7 : ℕ)) || x1 (1 : Fin (7 : ℕ)) && x1 (2 : Fin (7 : ℕ)) || x1 (0 : Fin (7 : ℕ)) && x1 (4 : Fin (7 : ℕ)) || x1 (1 : Fin (7 : ℕ)) && x1 (5 : Fin (7 : ℕ)) || x1 (2 : Fin (7 : ℕ)) && x1 (6 : Fin (7 : ℕ)) || x1 (3 : Fin (7 : ℕ)) && x1 (5 : Fin (7 : ℕ)) || x1 (4 : Fin (7 : ℕ)) && x1 (6 : Fin (7 : ℕ)) || x1 (6 : Fin (7 : ℕ)) && x1 (3 : Fin (7 : ℕ))) (10 : ℕ))
    (charge : ∀ C : Circuit, FanInTwo C →
      let hits := fun g : Gate => ([4,6,9] : List ℕ).any (fun w => (g.inputs[0]? == some w) || (g.op.eval [true] && g.inputs.contains w))
      let fixed := fun x : Fin 7 → Bool => List.ofFn (fun i : Fin 9 =>
        if i = 4 ∨ i = 6 then false else x (Fin.ofNat 7 (([0,4,6,3,0,1,0,2,5] : List ℕ).getD i.val 0))) ++ [false]
      4 ≤ C.gates.countP hits →
      (∃ x y : Fin 7 → Bool, C.eval (fixed x) ≠ C.eval (fixed y)) →
      ∃ B : Circuit, FanInTwo B ∧ B.size + C.gates.countP hits ≤ C.size ∧
        ∀ x : Fin 7 → Bool, B.eval (List.ofFn x) = C.eval (fixed x))
    (two : ∀ C : Circuit, FanInTwo C →
      let hits := fun g : Gate => ([4,6,9] : List ℕ).any (fun w => (g.inputs[0]? == some w) || (g.op.eval [true] && g.inputs.contains w))
      let used := fun (j : Fin C.gates.length) (w : ℕ) =>
        let g := C.gates.get j
        g.inputs[0]? = some w ∨ g.op ≠ GateOp.not ∧ w ∈ g.inputs
      (∃ a b : Fin C.gates.length, a < b ∧ used a 6 ∧ used b 4 ∧
        (∀ j, used j 6 → j = a) ∧ (∀ j, used j 4 → j = b)) →
      C.gates.countP hits ≤ 2 →
      (∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 4 || x 6]) = ([1,11,21,31,36,5,15,25,35,52,62,77] : List ℕ).any (fun e => x (Fin.ofNat 9 (e / 9)) && x (Fin.ofNat 9 (e % 9)))) →
      15 ≤ C.size)
    (three : ∀ C : Circuit, FanInTwo C →
      let hits := fun g : Gate => ([4,6,9] : List ℕ).any (fun w => (g.inputs[0]? == some w) || (g.op.eval [true] && g.inputs.contains w))
      let used := fun (j : Fin C.gates.length) (w : ℕ) =>
        let g := C.gates.get j
        g.inputs[0]? = some w ∨ g.op ≠ GateOp.not ∧ w ∈ g.inputs
      (∃ a b : Fin C.gates.length, a < b ∧ used a 6 ∧ used b 4 ∧
        (∀ j, used j 6 → j = a) ∧ (∀ j, used j 4 → j = b)) →
      C.gates.countP hits = 3 →
      (∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 4 || x 6]) = ([1,11,21,31,36,5,15,25,35,52,62,77] : List ℕ).any (fun e => x (Fin.ofNat 9 (e / 9)) && x (Fin.ofNat 9 (e % 9)))) →
      15 ≤ C.size) :
    ∀ (x1 : List PEqualNP.CircuitLowerBounds.Gate) (x2 : ℕ),   PEqualNP.MetaComplexity.FanInTwo { gates := x1, output := x2 : PEqualNP.CircuitLowerBounds.Circuit } →     (∀ (x4 : Fin (9 : ℕ) → Bool), { gates := x1, output := x2 : PEqualNP.CircuitLowerBounds.Circuit }.eval (List.ofFn x4 ++ [x4 (4 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ))]) = (fun (x5 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (11 : ℕ), (21 : ℕ), (31 : ℕ), (36 : ℕ), (5 : ℕ), (15 : ℕ), (25 : ℕ), (35 : ℕ), (52 : ℕ), (62 : ℕ), (77 : ℕ)].any fun (x6 : ℕ) => x5 (Fin.ofNat (9 : ℕ) (x6 / (9 : ℕ))) && x5 (Fin.ofNat (9 : ℕ) (x6 % (9 : ℕ)))) x4) →       (∃ (x5 : Fin x1.length) (x6 : Fin x1.length),           x5 < x6 ∧             (have x7 : PEqualNP.CircuitLowerBounds.Gate := x1.get x5;               x7.inputs[(0 : ℕ)]? = Option.some (6 : ℕ) ∨ x7.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ (6 : ℕ) ∈ x7.inputs) ∧               (have x7 : PEqualNP.CircuitLowerBounds.Gate := x1.get x6;                 x7.inputs[(0 : ℕ)]? = Option.some (4 : ℕ) ∨ x7.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ (4 : ℕ) ∈ x7.inputs) ∧                 (∀ (x7 : Fin x1.length),                     (have x8 : PEqualNP.CircuitLowerBounds.Gate := x1.get x7;                       x8.inputs[(0 : ℕ)]? = Option.some (6 : ℕ) ∨ x8.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ (6 : ℕ) ∈ x8.inputs) →                       x7 = x5) ∧                   ∀ (x7 : Fin x1.length),                     (have x8 : PEqualNP.CircuitLowerBounds.Gate := x1.get x7;                       x8.inputs[(0 : ℕ)]? = Option.some (4 : ℕ) ∨ x8.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ (4 : ℕ) ∈ x8.inputs) →                       x7 = x6) →         (15 : ℕ) ≤ x1.length := by
  intro gates out fan computes unique
  let C : Circuit := ⟨gates, out⟩
  let hits := fun g : Gate => ([4,6,9] : List ℕ).any (fun w => (g.inputs[0]? == some w) || (g.op.eval [true] && g.inputs.contains w))
  let f (x : Fin 9 → Bool) := ([1,11,21,31,36,5,15,25,35,52,62,77] : List ℕ).any (fun e => x (Fin.ofNat 9 (e / 9)) && x (Fin.ofNat 9 (e % 9)))
  let restricted (x : Fin 7 → Bool) := x 0 && x 1 || x 1 && x 2 || x 0 && x 4 || x 1 && x 5 || x 2 && x 6 || x 3 && x 5 || x 4 && x 6 || x 6 && x 3
  let place (x : Fin 7 → Bool) (i : Fin 9) :=
    if i = 4 ∨ i = 6 then false else x (Fin.ofNat 7 (([0,4,6,3,0,1,0,2,5] : List ℕ).getD i.val 0))
  let fixed (x : Fin 7 → Bool) := List.ofFn (place x) ++ [false]
  have graphRestrict : ∀ x : Fin 7 → Bool, f (place x) = restricted x := by decide +kernel
  have correctness (x : Fin 7 → Bool) : C.eval (fixed x) = restricted x := by
    have h : C.eval (List.ofFn (place x) ++ [place x 4 || place x 6]) = f (place x) := computes (place x)
    have z₄ : place x 4 = false := by simp [place]
    have z₆ : place x 6 = false := by simp [place]
    rw [z₄,z₆] at h
    exact h.trans (graphRestrict x)
  have varying : ∃ x y : Fin 7 → Bool, C.eval (fixed x) ≠ C.eval (fixed y) := by
    refine ⟨fun _ => false, fun _ => true, ?_⟩
    have h0 : C.eval (fixed (fun _ => false)) = false := correctness (fun _ => false)
    have h1 : C.eval (fixed (fun _ => true)) = true := correctness (fun _ => true)
    intro eq
    exact Bool.false_ne_true (h0.symm.trans (eq.trans h1))
  have combined : 15 ≤ C.size := by
    by_cases many : 4 ≤ C.gates.countP hits
    · by_contra! budget
      obtain ⟨B, fanB, cost, same⟩ := charge C fan many varying
      change B.size + C.gates.countP hits ≤ C.size at cost
      apply restrictedLower
      have small : B.size ≤ 10 := by omega
      exact ⟨B, fanB, small, fun x => (same x).trans (correctness x)⟩
    by_cases few : C.gates.countP hits ≤ 2
    · exact two C fan unique few computes
    · exact three C fan unique (by omega : C.gates.countP hits = 3) computes
  exact combined
