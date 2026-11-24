import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Defs.LratEncoding

-- The first bound is the cofactor bound proved inside L_meta_3200.
-- It forces all thirteen remaining gates to be monotone.
-- Each negated literal gives two monotone slices. Keep their minimal edge inputs
-- and maximal independent inputs as rows of the finite encoding.
set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_3887_42
    (suffix : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x4 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x4)).getD (9 : ℕ) Bool.false = (x4 (0 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x5 : Fin (9 : ℕ) → Bool) => x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ))) → 13 ≤ (x1.gates.drop 1).countP (fun g => GateOp.rec (motive := fun _ => Bool) true true false (fun _ => true) true g.op))
    (encode : ∀ (C : Circuit) (g : Nat → Bool) (rows : List Nat),
      Monotone2 C → C.size ≤ 13 → (∀ r ∈ rows, r < 2048) →
      (∀ r ∈ rows, C.eval (List.ofFn (fun k : Fin 11 => r.testBit k.val)) = g r) →
      FormulaSat (enc2 11 13 g rows))
    (obstruction :
      let target := fun r : Nat => ([3,6,12,24,17,33,66,132,264,160,320,288] : List Nat).any fun e => r &&& e == e
      let lift := fun (i r : Nat) => r + (if r &&& 5 != 0 then 512 else 0) + (if r.testBit i then 0 else 1024)
      let rows := fun i : Nat => ((List.range 512).filter fun r =>
        (List.range 9).all fun b => decide (b = i) ||
          (if target r then !r.testBit b || !target (r ^^^ 2^b)
           else r.testBit b || target (r ^^^ 2^b))).map (lift i)
      ∀ i : Nat, (i = 1 ∨ i = 6 ∨ i = 8) → ¬FormulaSat (enc2 11 13 target (rows i))) :
    ∀ (x1 : Fin (11 : ℕ)),   x1 = (1 : Fin (11 : ℕ)) ∨ x1 = (6 : Fin (11 : ℕ)) ∨ x1 = (8 : Fin (11 : ℕ)) →     ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size ≤ (13 : ℕ) →           ∃ (x6 : Fin (9 : ℕ) → Bool),             have x7 : List Bool := List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ))];             x3.eval (x7 ++ [!x7.getD (↑x1) Bool.false]) ≠ [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x8 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x6 x8.1 && x6 x8.2 := by
  intro i hi C fan size
  let graph := fun x : Fin 9 → Bool => ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any fun e => x e.1 && x e.2
  let seed := fun x : Fin 9 → Bool => List.ofFn x ++ [x 0 || x 2]
  change ∃ x, C.eval (seed x ++ [!(seed x).getD i.val false]) ≠ graph x
  by_contra! correct
  let g : Gate := ⟨.or,[0,2]⟩
  let n : Gate := ⟨.not,[i.val]⟩
  let D : Circuit := ⟨g :: n :: C.gates,C.output⟩
  have fanD : FanInTwo D := by
    intro z hz
    rcases List.mem_cons.mp hz with rfl|hz
    · exact ⟨Or.inr (Or.inl rfl),by decide⟩
    rcases List.mem_cons.mp hz with rfl|hz
    · exact ⟨Or.inr (Or.inr rfl),by change 1 ≤ 2; decide⟩
    · exact fan z hz
  let step := fun (w : List Bool) (z : Gate) => w ++ [z.op.eval (z.inputs.map fun j => w.getD j false)]
  have head (x : Fin 9 → Bool) : step (List.ofFn x) g = seed x := by
    change List.ofFn x ++ [x 0 || (x 2 || false)] = _
    simp [seed]
  have neg (x : Fin 9 → Bool) : step (seed x) n = seed x ++ [!(seed x).getD i.val false] := rfl
  have stable (gs : List Gate) (w : List Bool) (j : Nat) (hj : j < w.length) :
      (gs.foldl step w).getD j false = w.getD j false := by
    induction gs generalizing w with
    | nil => rfl
    | cons z zs ih =>
      rw [List.foldl_cons,ih]
      · exact List.getD_append _ _ _ _ hj
      · simp [step]; omega
  have first (x : Fin 9 → Bool) : (D.wires (List.ofFn x)).getD 9 false = (x 0 || x 2) := by
    change ((n :: C.gates).foldl step (step (List.ofFn x) g)).getD 9 false = _
    rw [head,stable _ _ _ (by simp [seed])]
    change [x 0 || x 2].getD 0 false = _
    rfl
  have computes (x : Fin 9 → Bool) : D.eval (List.ofFn x) = graph x := by
    change (C.gates.foldl step (step (step (List.ofFn x) g) n)).getD C.output false = _
    rw [head,neg]
    exact correct x
  have lower := suffix D fanD first (by
    funext x
    change D.eval (List.ofFn x) = _
    rw [computes]
    simp only [graph,List.any_cons,List.any_nil,Bool.or_false]
    ac_rfl)
  let charged := fun z : Gate => GateOp.rec (motive := fun _ => Bool) true true false (fun _ => true) true z.op
  change 13 ≤ (n :: C.gates).countP charged at lower
  have nfree : charged n = false := rfl
  simp only [List.countP_cons,nfree,Bool.false_eq_true,ite_false,Nat.add_zero] at lower
  have all : ∀ z ∈ C.gates, charged z = true := by
    apply List.countP_eq_length.mp
    change C.gates.length ≤ 13 at size
    have le := List.countP_le_length (p := charged) (l := C.gates)
    omega
  have mono : Monotone2 C := by
    intro z hz
    have hf := fan z hz
    refine ⟨?_,hf.2⟩
    rcases hf.1 with h|h|h
    · exact Or.inl h
    · exact Or.inr h
    · change z.op = GateOp.not at h
      have bad := all z hz
      simp [charged,h] at bad
  let target := fun r : Nat => ([3,6,12,24,17,33,66,132,264,160,320,288] : List Nat).any fun e => r &&& e == e
  let lift := fun (i r : Nat) => r + (if r &&& 5 != 0 then 512 else 0) + (if r.testBit i then 0 else 1024)
  let rows := fun i : Nat => ((List.range 512).filter fun r =>
        (List.range 9).all fun b => decide (b = i) ||
          (if target r then !r.testBit b || !target (r ^^^ 2^b)
           else r.testBit b || target (r ^^^ 2^b))).map (lift i)
  have cert : ∀ (q : Fin 11) (r : Fin 512), (q = 1 ∨ q = 6 ∨ q = 8) →
      let x := fun k : Fin 9 => r.val.testBit k.val
      lift q r < 2048 ∧
      List.ofFn (fun k : Fin 11 => (lift q r).testBit k.val) = seed x ++ [!(seed x).getD q.val false] ∧
      target (lift q r) = graph x := by decide
  apply obstruction i.val (by rcases hi with rfl|rfl|rfl <;> decide)
  apply encode C target (rows i) mono size
  · intro r hr
    obtain ⟨m,hm,rfl⟩ := List.mem_map.mp hr
    have b : m < 512 := List.mem_range.mp (List.mem_filter.mp hm).1
    exact (cert i ⟨m,b⟩ hi).1
  · intro r hr
    obtain ⟨m,hm,rfl⟩ := List.mem_map.mp hr
    have b : m < 512 := List.mem_range.mp (List.mem_filter.mp hm).1
    obtain ⟨_,w,g⟩ := cert i ⟨m,b⟩ hi
    change List.ofFn (fun k : Fin 11 => (lift i.val m).testBit k.val) = _ at w
    change target (lift i.val m) = _ at g
    rw [w,g]
    exact correct _


