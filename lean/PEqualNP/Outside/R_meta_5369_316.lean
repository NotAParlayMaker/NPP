import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
theorem PEqualNP.Outside.R_meta_5369_316
  (price : ∀ (C : Circuit) (v : Fin 10) (S : Finset Nat),FanInTwo C →
    let X := fun x : Fin 10 → Bool=>List.ofFn x++[!x 0]
    let W := fun (x : Fin 10 → Bool) (j : Nat)=>(C.wires (X x)).getD j false
    let P := fun x : Fin 10 → Bool => ([1,12,23,34,40,5,16,27,38,49,57,79,96,68,85] : List Nat).any fun t=>x (Fin.ofNat 10 (t / 10)) && x (Fin.ofNat 10 (t % 10))
    (∀x : Fin 10 → Bool,x v=false → C.eval (X x)=P x) →
    (∀j∈S,j<C.size ∧ ((∃b:Bool,∀x : Fin 10 → Bool,x v=false → W x (11+j)=b) ∨ ∃i<11+j,∀x : Fin 10 → Bool,x v=false → W x (11+j)=W x i)) → 15+S.card≤C.size)
  (remaining : ∀ (C : Circuit),FanInTwo C → C.size≤18 →
    (C.gates.countP (fun g=>let ports : List Nat := GateOp.rec g.inputs g.inputs (g.inputs.take 1) (fun _=>g.inputs) g.inputs g.op; ports.contains 0 || ports.contains 10))≤3 →
    let X := fun x : Fin 10 → Bool=>List.ofFn x++[!x 0]
    let W := fun (x : Fin 10 → Bool) (j : Nat)=>(C.wires (X x)).getD j false
    let P := fun x : Fin 10 → Bool => ([1,12,23,34,40,5,16,27,38,49,57,79,96,68,85] : List Nat).any fun t=>x (Fin.ofNat 10 (t / 10)) && x (Fin.ofNat 10 (t % 10))
    (∀ (v : Fin 10) (S : Finset Nat),(∀j∈S,j<C.size ∧ ((∃b:Bool,∀x : Fin 10 → Bool,x v=false → W x (11+j)=b) ∨ ∃i<11+j,∀x : Fin 10 → Bool,x v=false → W x (11+j)=W x i)) → 15+S.card≤C.size) →
    ∃x : Fin 10 → Bool,C.eval (X x)≠P x) :
∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.FanInTwo x1 →     x1.size ≤ (18 : ℕ) →       List.countP             (fun (x4 : PEqualNP.CircuitLowerBounds.Gate) =>               have x5 : List ℕ := PEqualNP.CircuitLowerBounds.GateOp.rec x4.inputs x4.inputs (List.take (1 : ℕ) x4.inputs) (fun (x5 : ℕ) => x4.inputs) x4.inputs x4.op;               x5.contains (0 : ℕ) || x5.contains (10 : ℕ))             x1.gates ≤           (3 : ℕ) →         ∃ (x5 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x5 ++ [!x5 (0 : Fin (10 : ℕ))]) ≠ (fun (x6 : Fin (10 : ℕ) → Bool) => x6 (0 : Fin (10 : ℕ)) && x6 (1 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (2 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (3 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (4 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (0 : Fin (10 : ℕ)) || x6 (0 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (5 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (7 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (9 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (6 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (8 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ))) x5 := by
  intro C fan cap rawCap
  by_contra! everything
  let X := fun x : Fin 10 → Bool=>List.ofFn x++[!x 0]
  let P := fun x : Fin 10 → Bool => ([1,12,23,34,40,5,16,27,38,49,57,79,96,68,85] : List Nat).any fun t=>x (Fin.ofNat 10 (t / 10)) && x (Fin.ofNat 10 (t % 10))
  have reads (x : Fin 10 → Bool) : C.eval (X x)=P x := by
    rw [show C.eval (X x)=(x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 || x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5) from everything x]
    change (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 || x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5)=(x 0 && x 1 || (x 1 && x 2 || (x 2 && x 3 || (x 3 && x 4 || (x 4 && x 0 || (x 0 && x 5 || (x 1 && x 6 || (x 2 && x 7 || (x 3 && x 8 || (x 4 && x 9 || (x 5 && x 7 || (x 7 && x 9 || (x 9 && x 6 || (x 6 && x 8 || (x 8 && x 5 || false)))))))))))))))
    simp only [Bool.or_false]
    ac_rfl
  obtain ⟨x, bad⟩ := remaining C fan cap rawCap (fun v S h => price C v S fan (fun x _ => reads x) h)
  exact bad (reads x)
