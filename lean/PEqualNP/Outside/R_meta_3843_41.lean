import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_3843_41
    (hshape : ∀ (a b : Fin 9) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 13 → (∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 || x 4,x a || x b]) = ([(1 : Nat),12,23,34,40,5,16,27,38,57,68,85].any fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))) → (1 ≤ C.gates.countP (fun g => g.op.eval [false]) ∧ C.gates.countP (fun g => g.op.eval [false]) ≤ 2 ∧ ((a,b) ∈ ([(0,2),(0,3),(1,3),(1,5),(1,8),(2,8)] : List (Fin 9 × Fin 9)) → C.gates.countP (fun g => g.op.eval [false]) = 1)) ∧ (∀ g ∈ C.gates, (∀ k ∈ g.inputs, k < 10) → g.op ≠ .and) ∧ (∀ k < 10, (⟨.not,[k]⟩ : PEqualNP.CircuitLowerBounds.Gate) ∉ C.gates))
    (hOne : ∀ (a b : Fin 9) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 13 → (2305843017923426382 : Nat).testBit (9*a.val+b.val) = true → C.gates.countP (fun g => g.op.eval [false]) = 1 → ((∀ g ∈ C.gates, (∀ k ∈ g.inputs, k < 10) → g.op ≠ .and) ∧ (∀ k < 10, (⟨.not,[k]⟩ : PEqualNP.CircuitLowerBounds.Gate) ∉ C.gates)) → ¬ (∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 || x 4,x a || x b]) = ([(1 : Nat),12,23,34,40,5,16,27,38,57,68,85].any fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))))
    (hTwo : ∀ (a b : Fin 9) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 13 → (2305843017923426382 : Nat).testBit (9*a.val+b.val) = true → (a,b) ∉ ([(0,2),(0,3),(1,3),(1,5),(1,8),(2,8)] : List (Fin 9 × Fin 9)) → C.gates.countP (fun g => g.op.eval [false]) = 2 → ((∀ g ∈ C.gates, (∀ k ∈ g.inputs, k < 10) → g.op ≠ .and) ∧ (∀ k < 10, (⟨.not,[k]⟩ : PEqualNP.CircuitLowerBounds.Gate) ∉ C.gates)) → ¬ (∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 || x 4,x a || x b]) = ([(1 : Nat),12,23,34,40,5,16,27,38,57,68,85].any fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))))) :
have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); have x2 : Fin (26 : ℕ) → Fin (26 : ℕ) → Fin (26 : ℕ) → List (Fin (3 : ℕ) × Fin (26 : ℕ) × Fin (26 : ℕ)) → Prop := fun (x2 x3 x4 : Fin (26 : ℕ)) (x5 : List (Fin (3 : ℕ) × Fin (26 : ℕ) × Fin (26 : ℕ))) =>   ∀ x6 < (512 : ℕ),     have x8 : Fin (9 : ℕ) → Bool := fun (x8 : Fin (9 : ℕ)) => x6.testBit ↑x8;     have x9 : List Bool → Fin (26 : ℕ) → Bool := fun (x9 : List Bool) (x10 : Fin (26 : ℕ)) => if ↑x10 = (25 : ℕ) then Bool.true else x9.getD (↑x10) Bool.false;     have x10 : List Bool := List.foldl (fun (x10 : List Bool) (x11 : Fin (3 : ℕ) × Fin (26 : ℕ) × Fin (26 : ℕ)) => x10 ++ [if ↑x11.1 = (0 : ℕ) then x9 x10 x11.2.1 && x9 x10 x11.2.2 else if ↑x11.1 = (1 : ℕ) then x9 x10 x11.2.1 || x9 x10 x11.2.2 else !x9 x10 x11.2.1]) (List.ofFn x8 ++ [x8 (0 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ))]) (((1 : Fin (3 : ℕ)), x2, x3) :: x5);     x10.getD (↑x4) Bool.false = x1 x8; have x3 : Fin (26 : ℕ) → Fin (26 : ℕ) → Prop := fun (x3 x4 : Fin (26 : ℕ)) => ↑x3 < (9 : ℕ) ∧ ↑x4 < (9 : ℕ) ∧ Nat.testBit (2305843017923426382 : ℕ) ((9 : ℕ) * ↑x3 + ↑x4) = Bool.true; ∀ (x4 x5 x6 : Fin (26 : ℕ)) (x7 : List (Fin (3 : ℕ) × Fin (26 : ℕ) × Fin (26 : ℕ))), x7.length ≤ (13 : ℕ) → x3 x4 x5 → ¬x2 x4 x5 x6 x7 := by
  let V := Fin 9
  let W := Fin 26
  let Code := Fin 3 × W × W
  let edges : List Nat := [1,12,23,34,40,5,16,27,38,57,68,85]
  let target (x : V → Bool) := edges.any fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))
  let bits (n : Nat) (i : V) := n.testBit i.val
  let rd (w : List Bool) (i : W) := if i.val = 25 then true else w.getD i.val false
  let rawStep (w : List Bool) (g : Code) := w ++ [if g.1.val = 0 then rd w g.2.1 && rd w g.2.2 else if g.1.val = 1 then rd w g.2.1 || rd w g.2.2 else !rd w g.2.1]
  let rawGood (a b o : W) (gs : List Code) := ∀ n < 512, let x := bits n; ((((1 : Fin 3),a,b) :: gs).foldl rawStep (List.ofFn x ++ [x 0 || x 4])).getD o.val false = target x
  let decode (g : Code) : Gate := if g.1.val = 0 then
    ⟨.and,(if g.2.1.val = 25 then [] else [g.2.1.val]) ++ (if g.2.2.val = 25 then [] else [g.2.2.val])⟩
    else if g.1.val = 1 then
      if g.2.1.val = 25 ∨ g.2.2.val = 25 then ⟨.and,[]⟩ else ⟨.or,[g.2.1.val,g.2.2.val]⟩
    else if g.2.1.val = 25 then ⟨.or,[]⟩ else ⟨.not,[g.2.1.val]⟩
  let decoded (gs : List Code) (o : W) : Circuit := ⟨gs.map decode,o.val⟩
  have decode_ok (g : Code) : (decode g).op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ (decode g).inputs.length ≤ 2 := by
    unfold decode; split_ifs <;> simp
  have decoded_fan (gs : List Code) (o : W) : FanInTwo (decoded gs o) := by
    intro z hz; obtain ⟨g,_,rfl⟩ := List.mem_map.mp hz; exact decode_ok g
  have decode_step (w : List Bool) (g : Code) : w ++ [(decode g).op.eval ((decode g).inputs.map fun i => w.getD i false)] = rawStep w g := by
    rcases g with ⟨op,i,j⟩
    fin_cases op <;> by_cases a : i.val = 25 <;> by_cases b : j.val = 25 <;> simp [rawStep,rd,decode,a,b] <;> dsimp only [GateOp.eval] <;> simp
  have decode_fold (gs : List Code) (w : List Bool) : (gs.map decode).foldl (fun v (g : Gate) => v ++ [g.op.eval (g.inputs.map fun i => v.getD i false)]) w = gs.foldl rawStep w := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih => simp only [List.map_cons,List.foldl_cons,decode_step,ih]
  have represent (x : V → Bool) : ∃ n : Fin 512, bits n.val = x := by
    let w := BitVec.ofBoolListLE (List.ofFn x)
    refine ⟨⟨w.toNat,by simpa [w] using w.isLt⟩,?_⟩
    funext i
    change w.getLsbD i.val = x i
    rw [BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem _ _ (by simp),List.getElem_ofFn]
  have decoded_good (a b o : W) (ha : a.val < 9) (hb : b.val < 9) (gs : List Code) (good : rawGood a b o gs) (x : V → Bool) :
      (decoded gs o).eval (List.ofFn x ++ [x 0 || x 4,x ⟨a.val,ha⟩ || x ⟨b.val,hb⟩]) = target x := by
    obtain ⟨n,rfl⟩ := represent x
    have h := good n.val n.isLt
    have readRaw (i : W) (hi : i.val < 9) : rd (List.ofFn (bits n.val) ++ [bits n.val 0 || bits n.val 4]) i = bits n.val ⟨i.val,hi⟩ := by
      have h25 : i.val ≠ 25 := by omega
      simp only [rd,if_neg h25]
      rw [List.getD_append _ _ _ _ (by simpa using hi),List.getD_eq_getElem _ _ (by simpa using hi),List.getElem_ofFn]
    unfold Circuit.eval Circuit.wires decoded
    rw [decode_fold]
    simpa only [List.foldl_cons,rawStep,show (1 : Fin 3).val = 1 from rfl,if_neg (by decide : (1 : Nat) ≠ 0),ite_true,if_pos rfl,readRaw a ha,readRaw b hb,List.append_assoc,List.singleton_append] using h
  intro _F _good _pair a b o gs len hab good
  obtain ⟨ha,hb,hm⟩ := hab
  let i : V := ⟨a.val,ha⟩
  let j : V := ⟨b.val,hb⟩
  let C := decoded gs o
  have hf : FanInTwo C := decoded_fan gs o
  have hs : C.size ≤ 13 := by change (gs.map decode).length ≤ 13; simpa only [List.length_map] using len
  have he := decoded_good a b o ha hb gs good
  obtain ⟨⟨lo,hi,sharp⟩,form⟩ := hshape i j C hf hs he
  by_cases one : C.gates.countP (fun g => g.op.eval [false]) = 1
  · exact hOne i j C hf hs hm one form he
  · exact hTwo i j C hf hs hm (fun h => one (sharp h)) (by omega) form he
