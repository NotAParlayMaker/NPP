import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
theorem PEqualNP.Outside.R_meta_4037_417
    (h₁ : ∀C : Circuit,FanInTwo C → (∀ x : Fin 10→Bool,C.eval (List.ofFn x++[!x 0])=([1,12,23,34,40,5,16,27,38,49,57,79,96,68,85] : List Nat).any (fun e => x (Fin.ofNat 10 (e / 10)) && x (Fin.ofNat 10 (e % 10)))) → (∃g∈C.gates,g.op=.or ∧ 0∈g.inputs) → (∃g∈C.gates,g.op=.and ∧ 10∈g.inputs) → 16+PEqualNP.NotBracket.notCount C≤C.size)
    (h₂ : ∀C : Circuit,Monotone2 C → (∀ x : Fin 10→Bool,C.eval (List.ofFn x++[!x 0])=([1,12,23,34,40,5,16,27,38,49,57,79,96,68,85] : List Nat).any (fun e => x (Fin.ofNat 10 (e / 10)) && x (Fin.ofNat 10 (e % 10)))) → ∀ a : Fin C.gates.length,(C.gates.get a).op=.or → (∀i : Fin C.gates.length,0∈(C.gates.get i).inputs → i=a) → (∀v∈(C.gates.get a).inputs,v=0 ∨ 11≤v) ∧ (∀y : Fin 9→Bool,let p := false::(List.ofFn y++[true]); C.eval p=false → ((y 1 && y 7 && y 8) || (y 2 && y 5 && y 6))=false → (C.gates.get a).op.eval ((C.gates.get a).inputs.map fun i=>(Circuit.wires ⟨C.gates.take a.val,0⟩ p).getD i false)=false))
    (h₃ : ∀C : Circuit,Monotone2 C → C.size=18 → (∀ x : Fin 10→Bool,C.eval (List.ofFn x++[!x 0])=([1,12,23,34,40,5,16,27,38,49,57,79,96,68,85] : List Nat).any (fun e => x (Fin.ofNat 10 (e / 10)) && x (Fin.ofNat 10 (e % 10)))) → ∀a b : Fin C.gates.length, (C.gates.get a).op=.or → 0∈(C.gates.get a).inputs → (C.gates.get b).op=.and → 10∈(C.gates.get b).inputs → (∀i : Fin C.gates.length,(0∈(C.gates.get i).inputs → i=a) ∧ (10∈(C.gates.get i).inputs → i=b)) → (∀v∈(C.gates.get a).inputs,v=0 ∨ 11≤v) → (∀y : Fin 9→Bool,let p := false::(List.ofFn y++[true]); C.eval p=false → ((y 1 && y 7 && y 8) || (y 2 && y 5 && y 6))=false → (C.gates.get a).op.eval ((C.gates.get a).inputs.map fun i=>(Circuit.wires ⟨C.gates.take a.val,0⟩ p).getD i false)=false) → False)
    (h₄ : ∀C : Circuit,FanInTwo C → C.size=18 → 0<PEqualNP.NotBracket.notCount C → PEqualNP.NotBracket.notCount C≤2 → (∀ x : Fin 10→Bool,C.eval (List.ofFn x++[!x 0])=([1,12,23,34,40,5,16,27,38,49,57,79,96,68,85] : List Nat).any (fun e => x (Fin.ofNat 10 (e / 10)) && x (Fin.ofNat 10 (e % 10)))) → ∀a b : Fin C.gates.length, (C.gates.get a).op=.or → 0∈(C.gates.get a).inputs → (C.gates.get b).op=.and → 10∈(C.gates.get b).inputs → (∀i : Fin C.gates.length,let g:=C.gates.get i;(g.op=.not → (g.inputs.head?=some 0 → i=a) ∧ (g.inputs.head?=some 10 → i=b)) ∧ (g.op≠.not → (0∈g.inputs → i=a) ∧ (10∈g.inputs → i=b))) → False)
    : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size = (18 : ℕ) → (∀ (x4 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x4 ++ [!x4 (0 : Fin (10 : ℕ))]) = (x4 (0 : Fin (10 : ℕ)) && x4 (1 : Fin (10 : ℕ)) || x4 (1 : Fin (10 : ℕ)) && x4 (2 : Fin (10 : ℕ)) || x4 (2 : Fin (10 : ℕ)) && x4 (3 : Fin (10 : ℕ)) || x4 (3 : Fin (10 : ℕ)) && x4 (4 : Fin (10 : ℕ)) || x4 (4 : Fin (10 : ℕ)) && x4 (0 : Fin (10 : ℕ)) || x4 (0 : Fin (10 : ℕ)) && x4 (5 : Fin (10 : ℕ)) || x4 (1 : Fin (10 : ℕ)) && x4 (6 : Fin (10 : ℕ)) || x4 (2 : Fin (10 : ℕ)) && x4 (7 : Fin (10 : ℕ)) || x4 (3 : Fin (10 : ℕ)) && x4 (8 : Fin (10 : ℕ)) || x4 (4 : Fin (10 : ℕ)) && x4 (9 : Fin (10 : ℕ)) || x4 (5 : Fin (10 : ℕ)) && x4 (7 : Fin (10 : ℕ)) || x4 (7 : Fin (10 : ℕ)) && x4 (9 : Fin (10 : ℕ)) || x4 (9 : Fin (10 : ℕ)) && x4 (6 : Fin (10 : ℕ)) || x4 (6 : Fin (10 : ℕ)) && x4 (8 : Fin (10 : ℕ)) || x4 (8 : Fin (10 : ℕ)) && x4 (5 : Fin (10 : ℕ)))) → ¬∃ (x5 : Fin x1.gates.length) (x6 : Fin x1.gates.length), x5 ≠ x6 ∧ (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (0 : ℕ) ∈ (x1.gates.get x5).inputs ∧ (x1.gates.get x6).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (10 : ℕ) ∈ (x1.gates.get x6).inputs ∧ ∀ x7 ∈ [((0 : ℕ), x5), ((10 : ℕ), x6)], ∀ (x9 : Fin x1.gates.length), ((x1.gates.get x9).op = PEqualNP.CircuitLowerBounds.GateOp.not → (x1.gates.get x9).inputs.head? = Option.some x7.1 → x9 = x7.2) ∧ ((x1.gates.get x9).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not → x7.1 ∈ (x1.gates.get x9).inputs → x9 = x7.2) := by
  let target := fun (x : Fin 10→Bool)=>([1,12,23,34,40,5,16,27,38,49,57,79,96,68,85] : List Nat).any (fun e => x (Fin.ofNat 10 (e / 10)) && x (Fin.ofNat 10 (e % 10)))
  have same : ∀x : Fin 10→Bool,target x=(x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 || x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5) := by decide +kernel
  letI : DecidableEq GateOp := lineDegreeGateOpDecEq
  intro C fan size computes witnesses
  have good (x : Fin 10→Bool) : C.eval (List.ofFn x++[!x 0])=target x := (computes x).trans (same x).symm
  obtain ⟨a,b,_,ao,ar,bo,br,sole⟩:=witnesses
  have bound:=h₁ C fan good ⟨_,List.get_mem _ a,ao,ar⟩ ⟨_,List.get_mem _ b,bo,br⟩
  have nots : PEqualNP.NotBracket.notCount C≤2 := by omega
  by_cases z : PEqualNP.NotBracket.notCount C=0
  · have mono : Monotone2 C := by
      intro g m
      obtain ⟨allowed,arity⟩:=fan g m
      refine ⟨?_,arity⟩
      have ng : g.op≠.not := by
        intro yes
        have keep : g∈(C.gates.filter fun v=>decide (v.op=.not)) := List.mem_filter.mpr ⟨m,decide_eq_true yes⟩
        change (C.gates.filter fun v=>decide (v.op=.not)).length=0 at z
        have nil:=List.length_eq_zero_iff.mp z
        rw [nil] at keep
        contradiction
      exact allowed.elim Or.inl (fun p=>p.elim Or.inr (fun n=>(ng n).elim))
    have uniq (i : Fin C.gates.length) : (0∈(C.gates.get i).inputs → i=a) ∧ (10∈(C.gates.get i).inputs → i=b) := by
      have n : (C.gates.get i).op≠.not := by rcases (mono _ (List.get_mem _ i)).1 with e|e <;> rw [e] <;> decide
      exact ⟨(sole (0,a) (by simp) i).2 n,(sole (10,b) (by simp) i).2 n⟩
    have shape:=h₂ C mono good a ao (fun i=>(uniq i).1)
    exact h₃ C mono size good a b ao ar bo br uniq shape.1 shape.2
  · apply h₄ C fan size (by omega) nots good a b ao ar bo br
    intro i
    exact ⟨fun n=>⟨(sole (0,a) (by simp) i).1 n,(sole (10,b) (by simp) i).1 n⟩,fun n=>⟨(sole (0,a) (by simp) i).2 n,(sole (10,b) (by simp) i).2 n⟩⟩
