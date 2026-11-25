import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
theorem PEqualNP.Outside.R_meta_3436_619
  (finite : let step := fun (w : List (BitVec 9 → Bool)) (g : Gate) =>
    w ++ [fun t => g.op.eval (g.inputs.map (fun j => (w.getD j (fun _ => false)) t))]
  let bank := (List.ofFn (fun i : Fin 9 => fun b : BitVec 9 => b.getLsbD i.val)) ++ [fun b => !(b.getLsbD 0)]
  ∀ (gs : List Gate) (o : Nat), FanInTwo ⟨gs,o⟩ → gs.length ≤ 14 → ∃ b : BitVec 9,
    ((gs.foldl step bank).getD o (fun _ => false)) b ≠ ([1,12,23,34,40,5,16,27,38,57,68,85] : List Nat).any
      (fun e => b.getLsbD (e / 10) && b.getLsbD (e % 10)))
  (physical : let step := fun (w : List (BitVec 9 → Bool)) (g : Gate) =>
    w ++ [fun t => g.op.eval (g.inputs.map (fun j => (w.getD j (fun _ => false)) t))]
  ∀ (C : Circuit) (ws : List (BitVec 9 → Bool)) (p q : Nat) (b : BitVec 9),
    let w := ws.map (fun f => f b)
    C.eval (w ++ [w.getD p false || w.getD q false]) =
      ((((⟨.or,[p,q]⟩ : Gate) :: C.gates).foldl step ws).getD C.output (fun _ => false)) b) :
∀ (x1 x2 : Fin (11 : ℕ)) (x3 : PEqualNP.CircuitLowerBounds.Circuit),   (11 : ℕ) * ↑x1 + ↑x2 ∈ [(1 : ℕ), (2 : ℕ), (3 : ℕ), (4 : ℕ), (6 : ℕ), (9 : ℕ), (13 : ℕ), (14 : ℕ), (15 : ℕ), (16 : ℕ), (17 : ℕ), (18 : ℕ), (19 : ℕ), (20 : ℕ), (25 : ℕ), (26 : ℕ), (28 : ℕ), (29 : ℕ), (30 : ℕ), (31 : ℕ), (37 : ℕ), (39 : ℕ), (42 : ℕ), (50 : ℕ), (53 : ℕ), (73 : ℕ), (75 : ℕ)] →     PEqualNP.MetaComplexity.FanInTwo x3 →       x3.size ≤ (13 : ℕ) →         ∃ (x7 : BitVec (9 : ℕ)),           have x8 : Fin (9 : ℕ) → Bool := fun (x8 : Fin (9 : ℕ)) => x7.getLsbD ↑x8;           have x9 : List Bool := List.ofFn x8 ++ [!x8 (0 : Fin (9 : ℕ))];           x3.eval (x9 ++ [x9.getD (↑x1) Bool.false || x9.getD (↑x2) Bool.false]) ≠ [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x10 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x8 x10.1 && x8 x10.2 := by
  intro p q C _ fan cap
  let bank := (List.ofFn (fun i : Fin 9 => fun b : BitVec 9 => b.getLsbD i.val)) ++ [fun b => !(b.getLsbD 0)]
  let g:Gate:=⟨.or,[p.val,q.val]⟩
  have legal:FanInTwo ⟨g::C.gates,C.output⟩ := by
    intro h hh
    rcases List.mem_cons.mp hh with rfl|hh
    · simp [g]
    · exact fan _ hh
  have lim:(g::C.gates).length≤14:=by change C.gates.length≤13 at cap; simp; omega
  obtain ⟨b,bad⟩:=finite (g::C.gates) C.output legal lim
  let x:Fin 9→Bool:=fun i=>b.getLsbD i.val
  have bm:bank.map (fun f=>f b)=List.ofFn x++[!x 0]:=by simp [bank,x,List.map_ofFn,Function.comp_def]
  have witnessed:=physical C bank p.val q.val b
  dsimp only at witnessed
  rw [bm] at witnessed
  refine ⟨b,?_⟩
  apply fun agree=>bad (witnessed.symm.trans ?_)
  exact agree
