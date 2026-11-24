import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_3250_67
    (position : let f := fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List Nat).any (fun e => x (Fin.ofNat 9 (e/10)) && x (Fin.ofNat 9 (e%10)));
      let row := fun x : Fin 9 → Bool => List.ofFn x ++ [x 0 || x 6];
      ∀ (i : Fin 9) (C : Circuit) (p : Nat) (d : Bool),
      let z := fun x : Fin 9 → Bool => (C.wires (row x)).getD p false; let value := fun x : Fin 9 → Bool => C.eval ((row x).set i.val (if d then x i || z x else x i && z x)); ∀ cut : Nat, FanInTwo C → C.size≤13 → 10≤p → p<cut → cut≤10+C.size →
      (∀ g∈C.gates.take (cut-10),i.val∉g.inputs) → (∀ x, value x=f x) → C.size=13 ∧ C.output=22 ∧ cut≤22)
    (forms : let f := fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List Nat).any (fun e => x (Fin.ofNat 9 (e/10)) && x (Fin.ofNat 9 (e%10)));
      let row := fun x : Fin 9 → Bool => List.ofFn x ++ [x 0 || x 6];
      ∀ (i : Fin 9) (C : Circuit) (d : Bool),
      let z := fun x : Fin 9 → Bool => (C.wires (row x)).getD 10 false; let value := fun x : Fin 9 → Bool => C.eval ((row x).set i.val (if d then x i || z x else x i && z x)); let choices := fun (a b : Fin 11) => let k := 10 * min a.val b.val + max a.val b.val; if d then i.val≠1 ∧ k=19 else (i.val,k)∈([(1,29),(4,3),(4,39),(7,25)] : List (Nat × Nat));
      i≠0 → i≠6 → FanInTwo C → C.size=13 → (∀ g∈C.gates.take 1,i.val∉g.inputs) →
      (∀ x : Fin 9 → Bool, let lo := Function.update x i false; f lo ≠ f (Function.update x i true) → z lo = !d) → (∀ x, value x=f x) → ∃ a b : Fin 11, choices a b ∧ ∀ x : Fin 9 → Bool,
        let r := row x; z x=(if d then r.getD a.val false && r.getD b.val false else r.getD a.val false || r.getD b.val false))
    (headCut : let f := fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List Nat).any (fun e => x (Fin.ofNat 9 (e/10)) && x (Fin.ofNat 9 (e%10)));
      let row := fun x : Fin 9 → Bool => List.ofFn x ++ [x 0 || x 6];
      ∀ (i : Fin 9) (C : Circuit) (d : Bool),
      let z := fun x : Fin 9 → Bool => (C.wires (row x)).getD 10 false; let value := fun x : Fin 9 → Bool => C.eval ((row x).set i.val (if d then x i || z x else x i && z x)); let choices := fun (a b : Fin 11) => let k := 10 * min a.val b.val + max a.val b.val; if d then i.val≠1 ∧ k=19 else (i.val,k)∈([(1,29),(4,3),(4,39),(7,25)] : List (Nat × Nat));
      i≠0 → i≠6 → FanInTwo C → C.size=13 → C.output=22 → (∃ a b : Fin 11, choices a b ∧ ∀ x : Fin 9 → Bool,
        let r := row x; z x=(if d then r.getD a.val false && r.getD b.val false else r.getD a.val false || r.getD b.val false)) → ∃ x, value x≠f x)
    (later : let f := fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List Nat).any (fun e => x (Fin.ofNat 9 (e/10)) && x (Fin.ofNat 9 (e%10)));
      let row := fun x : Fin 9 → Bool => List.ofFn x ++ [x 0 || x 6];
      ∀ (i : Fin 9) (C : Circuit) (p : Nat) (d : Bool),
      let z := fun x : Fin 9 → Bool => (C.wires (row x)).getD p false; let value := fun x : Fin 9 → Bool => C.eval ((row x).set i.val (if d then x i || z x else x i && z x));
      i≠0 → i≠6 → FanInTwo C → C.size=13 → C.output=22 → 11≤p → p<22 →
      (∀ g∈C.gates.take (p-9),i.val∉g.inputs) → (∀ x : Fin 9 → Bool, let lo := Function.update x i false; f lo ≠ f (Function.update x i true) → z lo = !d) → ∃ x, value x≠f x) : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x2 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x1 x2.1 && x1 x2.2; ∀ (x2 : Fin (9 : ℕ)) (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ) (x6 : Bool),   x2 ≠ (0 : Fin (9 : ℕ)) →     x2 ≠ (6 : Fin (9 : ℕ)) →       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size ≤ (13 : ℕ) →           (10 : ℕ) ≤ x5 →             x5 < x4 →               x4 ≤ (10 : ℕ) + x3.size →                 (∀ x14 ∈ List.take (x4 - (10 : ℕ)) x3.gates, ↑x2 ∉ x14.inputs) →                   (∀ (x15 : Fin (9 : ℕ) → Bool),                       have x16 : Fin (9 : ℕ) → Bool := Function.update x15 x2 Bool.false;                       x1 x16 ≠ x1 (Function.update x15 x2 Bool.true) → (x3.wires (List.ofFn x16 ++ [x16 (0 : Fin (9 : ℕ)) || x16 (6 : Fin (9 : ℕ))])).getD x5 Bool.false = !x6) →                     ∃ (x16 : Fin (9 : ℕ) → Bool),                       have x17 : List Bool := List.ofFn x16 ++ [x16 (0 : Fin (9 : ℕ)) || x16 (6 : Fin (9 : ℕ))];                       have x18 : Bool := (x3.wires x17).getD x5 Bool.false;                       x3.eval (x17.set (↑x2) (if x6 = Bool.true then x16 x2 || x18 else x16 x2 && x18)) ≠ x1 x16 := by
  dsimp only
  intro i C cut p d h0 h6 legal small lp pc cap avoid guard
  let f := fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List Nat).any (fun e => x (Fin.ofNat 9 (e/10)) && x (Fin.ofNat 9 (e%10)))
  let row := fun x : Fin 9 → Bool => List.ofFn x ++ [x 0 || x 6]
  let z := fun x => (C.wires (row x)).getD p false
  let value := fun x : Fin 9 → Bool => C.eval ((row x).set i.val (if d then x i || z x else x i && z x))
  have eqn : ∀ x : Fin 9 → Bool, f x = ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2) := by decide +kernel
  by_contra! ok
  have correct : ∀ x, value x=f x := fun x => (ok x).trans (eqn x).symm
  obtain ⟨size,out,ub⟩ := position i C p d cut legal small lp pc cap avoid correct
  have guarded (x : Fin 9 → Bool) (h : f (Function.update x i false) ≠ f (Function.update x i true)) :
      z (Function.update x i false)= !d := guard x (by simpa only [←eqn] using h)
  by_cases atHead : p=10
  · have a1 : ∀ g∈C.gates.take 1,i.val∉g.inputs := by
      intro g hg; apply avoid g
      apply List.mem_of_mem_take (i:=1)
      simpa [List.take_take,show min 1 (cut-10)=1 by omega] using hg
    have form := forms i C d h0 h6 legal size a1 (by simpa only [z,atHead] using guarded) (by simpa only [value,z,atHead] using correct)
    obtain ⟨x,bad⟩ := headCut i C d h0 h6 legal size out form
    exact bad (by simpa only [value,z,atHead] using correct x)
  · have smaller : ∀ g∈C.gates.take (p-9),i.val∉g.inputs := by
      intro g hg; apply avoid g
      apply List.mem_of_mem_take (i:=p-9)
      simpa [List.take_take,show min (p-9) (cut-10)=p-9 by omega] using hg
    obtain ⟨x,bad⟩ := later i C p d h0 h6 legal size out (by omega) (by omega) smaller guarded
    exact bad (correct x)
