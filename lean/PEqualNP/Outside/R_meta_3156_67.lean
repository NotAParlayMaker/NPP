import Mathlib
import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_3156_67
    (pair : let w (A : Circuit) (x : Fin 9 → Bool) := A.wires (List.ofFn x ++ [x 0 || x 2]); ∀ (pre post : List Gate) (g : Gate) (o : Nat), let C : Circuit := ⟨pre++g::post,o⟩; let F : Circuit := ⟨pre++⟨.or,[]⟩::post,o⟩; FanInTwo C → (∀ h ∈ pre++post, h.op ≠ .not) → g.op=.not → (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x 0 || x 2)) → C.size ≤ 15 → ∃ (A B : Circuit) (k : Nat), Monotone2 A ∧ Monotone2 B ∧ A.size+B.size ≤ 13 ∧ ∀ x, C.eval (List.ofFn x)=B.eval (w A x ++ [!((w A x).getD k false)]) ∧ F.eval (List.ofFn x)=B.eval (w A x ++ [false]))
    (edge : let f (x : Fin 9 → Bool) := ([1,12,23,34,40,5,16,27,38,57,68,85] : List Nat).any (fun e => x (Fin.ofNat 9 (e/10)) && x (Fin.ofNat 9 (e%10))); let y (m : Nat) (i : Fin 9) := m.testBit i.val; ∀ (pre post : List Gate) (g : Gate) (o : Nat), let C : Circuit := ⟨pre++g::post,o⟩; let F : Circuit := ⟨pre++⟨.or,[]⟩::post,o⟩; FanInTwo C → (∀ h ∈ pre++post, h.op ≠ .not) → circuitFun 9 C = f → ∀ v : Fin 9, (fun z => circuitFun 9 F (v.insertNth false z)) ≠ (fun z => f (v.insertNth false z)) → ∃ m ∈ [3,6,12,24,17,33,66,132,264,160,320,288], y m v=false ∧ circuitFun 9 F (y m)=false)
    (independent : let f (x : Fin 9 → Bool) := ([1,12,23,34,40,5,16,27,38,57,68,85] : List Nat).any (fun e => x (Fin.ofNat 9 (e/10)) && x (Fin.ofNat 9 (e%10))); let y (m : Nat) (i : Fin 9) := m.testBit i.val; let w (A : Circuit) (x : Fin 9 → Bool) := A.wires (List.ofFn x ++ [x 0 || x 2]); ∀ (A B : Circuit) (k : Nat), Monotone2 A → Monotone2 B → A.size+B.size ≤ 13 → (∀ x, B.eval (w A x ++ [!((w A x).getD k false)]) = f x) → (∃ m ∈ [42,50,69,104,116,138,201,208,261,276,385,402], (w A (y m)).getD k false = true ∧ B.eval (w A (y m) ++ [true]) = true))
    (core : let f (x : Fin 9 → Bool) := ([1,12,23,34,40,5,16,27,38,57,68,85] : List Nat).any (fun e => x (Fin.ofNat 9 (e/10)) && x (Fin.ofNat 9 (e%10))); let y (m : Nat) (i : Fin 9) := m.testBit i.val; let w (A : Circuit) (x : Fin 9 → Bool) := A.wires (List.ofFn x ++ [x 0 || x 2]); ∀ (A B : Circuit) (k : Nat), Monotone2 A → Monotone2 B → A.size+B.size ≤ 13 → (∃ H ∈ (([3,6,12,33,264,288] : List Nat).map (fun m => [m]) ++ [17,24].flatMap (fun a => [66,320,132,160].map (fun b => [a,b])) ++ [66,320].flatMap (fun a => [132,160].map (fun b => [a,b]))), ∀ m ∈ H, (w A (y m)).getD k false = false ∧ B.eval (w A (y m) ++ [false]) = false) → (∃ m ∈ [42,50,69,104,116,138,201,208,261,276,385,402], (w A (y m)).getD k false = true ∧ B.eval (w A (y m) ++ [true]) = true) → ∃ x, B.eval (w A x ++ [!((w A x).getD k false)]) ≠ f x) : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); ∀ (x2 x3 : List PEqualNP.CircuitLowerBounds.Gate) (x4 : PEqualNP.CircuitLowerBounds.Gate) (x5 : ℕ),   have x6 : PEqualNP.CircuitLowerBounds.Circuit := { gates := x2 ++ x4 :: x3, output := x5 : PEqualNP.CircuitLowerBounds.Circuit };   have x7 : (Fin (9 : ℕ) → Bool) → Bool := PEqualNP.MetaComplexity.circuitFun (9 : ℕ) { gates := x2 ++ { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] : PEqualNP.CircuitLowerBounds.Gate } :: x3, output := x5 : PEqualNP.CircuitLowerBounds.Circuit };   PEqualNP.MetaComplexity.FanInTwo x6 → (∀ x9 ∈ x2 ++ x3, x9.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) → x4.op = PEqualNP.CircuitLowerBounds.GateOp.not → PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x6 = x1 → (∀ (x12 : Fin (9 : ℕ) → Bool), (x6.wires (List.ofFn x12)).getD (9 : ℕ) Bool.false = (x12 (0 : Fin (9 : ℕ)) || x12 (2 : Fin (9 : ℕ)))) → (∀ (x13 : Fin (9 : ℕ)), x13 = (4 : Fin (9 : ℕ)) ∨ x13 = (6 : Fin (9 : ℕ)) ∨ x13 = (7 : Fin (9 : ℕ)) → (fun (x15 : Fin (8 : ℕ) → Bool) => x7 (x13.insertNth Bool.false x15)) ≠ fun (x15 : Fin (8 : ℕ) → Bool) => x1 (x13.insertNth Bool.false x15)) → (16 : ℕ) ≤ x6.size := by
  intro f pre post g o C F hf mono op exactF seed bad
  by_contra! short
  let y (m : Nat) (i : Fin 9) := m.testBit i.val
  let w (A : Circuit) (x : Fin 9 → Bool) := A.wires (List.ofFn x ++ [x 0 || x 2])
  obtain ⟨A,B,k,am,bm,sz,h⟩ := pair pre post g o hf mono op seed (show C.size ≤ 15 by omega)
  have eqn (x : Fin 9 → Bool) : B.eval (w A x ++ [!((w A x).getD k false)]) = f x :=
    (h x).1.symm.trans (congrFun exactF x)
  have witness (v : Fin 9) (hv : v=4 ∨ v=6 ∨ v=7) : ∃ m ∈ ([3,6,12,24,17,33,66,132,264,160,320,288] : List Nat), y m v=false ∧ (w A (y m)).getD k false=false ∧ B.eval (w A (y m) ++ [false])=false := by
    obtain ⟨m,hm,avoid,off⟩ := edge pre post g o hf mono exactF v (bad v hv)
    have fo : B.eval (w A (y m) ++ [false])=false := (h (y m)).2.symm.trans off
    have pe : ∀ n ∈ ([3,6,12,24,17,33,66,132,264,160,320,288] : List Nat), f (y n)=true := by decide +kernel
    have normal := (eqn (y m)).trans (pe m hm)
    refine ⟨m,hm,avoid,?_,fo⟩
    cases hk : (w A (y m)).getD k false with
    | false => rfl
    | true => rw [hk] at normal; exact False.elim (Bool.false_ne_true (fo.symm.trans normal))
  let groups := (([3,6,12,33,264,288] : List Nat).map (fun m => [m]) ++ [17,24].flatMap (fun a => [66,320,132,160].map (fun b => [a,b])) ++ [66,320].flatMap (fun a => [132,160].map (fun b => [a,b])))
  let P := ([3,6,12,24,17,33,66,132,264,160,320,288] : List Nat)
  have pack : ∀ a ∈ P, ∀ b ∈ P, ∀ c ∈ P, y a 4=false → y b 6=false → y c 7=false →
      ∃ H ∈ groups, ∀ m ∈ H, m=a ∨ m=b ∨ m=c := by decide +kernel
  obtain ⟨a,ha,va,wa⟩ := witness 4 (by decide)
  obtain ⟨b,hb,vb,wb⟩ := witness 6 (by decide)
  obtain ⟨c,hc,vc,wc⟩ := witness 7 (by decide)
  obtain ⟨H,hh,members⟩ := pack a ha b hb c hc va vb vc
  obtain ⟨x,hx⟩ := core A B k am bm sz (by
    refine ⟨H,hh,?_⟩; intro m hm
    rcases members m hm with rfl|rfl|rfl
    · exact wa
    · exact wb
    · exact wc) (independent A B k am bm sz eqn)
  exact hx (eqn x)
