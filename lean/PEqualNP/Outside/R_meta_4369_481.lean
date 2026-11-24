import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_4369_481
    (negative :
      let f := fun (x : Fin 9 → Bool) => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))
      let seed := fun (x : Fin 9 → Bool) => List.ofFn x ++ [x 0 || x 3]
      ∀ C : Circuit, let u := C.output :: C.gates.flatMap Gate.inputs
      let n := (C.gates.filter fun g => g.op.eval [false] && !g.op.eval [true]).length
      FanInTwo C → C.size = 14 →
        (∀ i : Fin 9, ∃ x, C.eval (List.ofFn x ++ [x i]) ≠ f x) →
        9+n+∑ i ∈ Finset.range 24, (u.count i-1) ≤ 14 →
        2 ≤ u.count 9 → 0 < n → ∃ x, C.eval (seed x) ≠ f x)
    (monotone :
      let f := fun (x : Fin 9 → Bool) => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))
      let seed := fun (x : Fin 9 → Bool) => List.ofFn x ++ [x 0 || x 3]
      let allowed := fun (op : GateOp) => if op.eval [] then ([3,9,30,39,49] : List ℕ) else [2,4,8,31,34,35]
      ∀ C : Circuit, FanInTwo C → C.size = 14 →
        (C.gates.filter fun g => g.op.eval [false] && !g.op.eval [true]).length = 0 →
        2 ≤ (C.output :: C.gates.flatMap Gate.inputs).count 9 →
        ∀ R : Finset ℕ, R.card ≤ 4 →
        (∀ g ∈ C.gates, ∀ (a : Fin 9) (b : Fin 10),
          (g.inputs = [a.val,b.val] ∨ g.inputs = [b.val,a.val]) →
          (g.op = .and ∨ g.op = .or) → 10*a.val+b.val ∉ allowed g.op → a.val ∈ R) →
        ((⟨.and,[0,3]⟩ : Gate) ∈ C.gates ∨ ⟨.and,[3,0]⟩ ∈ C.gates → 0 ∈ R ∨ 3 ∈ R) →
        ∃ x, C.eval (seed x) ≠ f x) :
have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); have x2 : (Fin (9 : ℕ) → Bool) → List Bool := fun (x2 : Fin (9 : ℕ) → Bool) => List.ofFn x2 ++ [x2 (0 : Fin (9 : ℕ)) || x2 (3 : Fin (9 : ℕ))]; have x3 : PEqualNP.CircuitLowerBounds.GateOp → List ℕ := fun (x3 : PEqualNP.CircuitLowerBounds.GateOp) => if x3.eval [] = Bool.true then [(3 : ℕ), (9 : ℕ), (30 : ℕ), (39 : ℕ), (49 : ℕ)] else [(2 : ℕ), (4 : ℕ), (8 : ℕ), (31 : ℕ), (34 : ℕ), (35 : ℕ)]; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit),   have x5 : List ℕ := x4.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x4.gates;   have x6 : ℕ := (List.filter (fun (x6 : PEqualNP.CircuitLowerBounds.Gate) => x6.op.eval [Bool.false] && !x6.op.eval [Bool.true]) x4.gates).length;   PEqualNP.MetaComplexity.FanInTwo x4 → x4.size = (14 : ℕ) → (∀ x9 ∈ x5, x9 ≤ (24 : ℕ)) → (∀ x10 < (24 : ℕ), x10 ∈ x5) → (9 : ℕ) + x6 + ∑ x11 ∈ Finset.range (24 : ℕ), (List.count x11 x5 - (1 : ℕ)) ≤ (14 : ℕ) → (2 : ℕ) ≤ List.count (9 : ℕ) x5 → (∀ (x13 : Fin (9 : ℕ)), ∃ (x14 : Fin (9 : ℕ) → Bool), x4.eval (List.ofFn x14 ++ [x14 x13]) ≠ x1 x14) → ∀ (x14 : Finset ℕ), x14.card + x6 ≤ (4 : ℕ) → (∀ x16 ∈ x4.gates, ∀ (x18 : Fin (9 : ℕ)) (x19 : Fin (10 : ℕ)), x16.inputs = [↑x18, ↑x19] ∨ x16.inputs = [↑x19, ↑x18] → x16.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x16.op = PEqualNP.CircuitLowerBounds.GateOp.or → (10 : ℕ) * ↑x18 + ↑x19 ∉ x3 x16.op → ↑x18 ∈ x14) → ({ op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [(0 : ℕ), (3 : ℕ)] : PEqualNP.CircuitLowerBounds.Gate } ∈ x4.gates ∨ { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [(3 : ℕ), (0 : ℕ)] : PEqualNP.CircuitLowerBounds.Gate } ∈ x4.gates → (0 : ℕ) ∈ x14 ∨ (3 : ℕ) ∈ x14) → ∃ (x18 : Fin (9 : ℕ) → Bool), x4.eval (x2 x18) ≠ x1 x18 := by
  dsimp only
  intro C fan size _ _ overhead cache copies R budget raw special
  let n := (C.gates.filter fun g => g.op.eval [false] && !g.op.eval [true]).length
  by_cases zero : n = 0
  · exact monotone C fan size zero cache R (by omega) raw special
  · exact negative C fan size copies overhead cache (Nat.pos_of_ne_zero zero)
