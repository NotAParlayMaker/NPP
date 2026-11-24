import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_3079_67
    (binary : ∀ C : Circuit, FanInTwo C → (∀ m < 512, let x : Fin 9 → Bool := fun j => m.testBit j.val
       C.eval (List.ofFn x) = ([1,12,23,34,40,5,16,27,38,57,68,85] : List Nat).any
         (fun z => x (Fin.ofNat 9 (z / 10)) && x (Fin.ofNat 9 (z % 10)))) → 13 ≤ C.gates.countP (fun g => (GateOp.rec (motive := fun _ => Bool) true true false (fun _ => true) true g.op)))
    (small : ∀ (x1 x2 x3 : Fin (26 : ℕ)) (x4 : List (Fin (3 : ℕ) × Fin (26 : ℕ) × Fin (26 : ℕ))),   x4.length ≤ (13 : ℕ) → x4.countP (fun g => decide (g.1.val = 2)) ≤ 2 →     ↑x1 ≠ (9 : ℕ) ∧ ↑x2 ≠ (9 : ℕ) →       ↑x1 ≠ (25 : ℕ) →         ↑x2 ≠ (25 : ℕ) →           (∀ x9 < (9 : ℕ), (∃ x11 ∈ x4, ↑x11.2.1 = x9 ∨ ↑x11.2.2 = x9) ∨ ↑x1 = x9 ∧ (↑x2 = x9 ∨ (10 : ℕ) ≤ ↑x2 ∨ (x9, ↑x2) ∈ [((0 : ℕ), (3 : ℕ)), ((4 : ℕ), (1 : ℕ)), ((4 : ℕ), (5 : ℕ))]) ∨ ↑x2 = x9 ∧ (↑x1 = x9 ∨ (10 : ℕ) ≤ ↑x1 ∨ (x9, ↑x1) ∈ [((0 : ℕ), (3 : ℕ)), ((4 : ℕ), (1 : ℕ)), ((4 : ℕ), (5 : ℕ))])) →             ∃ x10 < (512 : ℕ),               have x11 : Fin (9 : ℕ) → Bool := fun (x11 : Fin (9 : ℕ)) => x10.testBit ↑x11;               have x12 : List Bool → Fin (26 : ℕ) → Bool := fun (x12 : List Bool) (x13 : Fin (26 : ℕ)) => if ↑x13 = (25 : ℕ) then Bool.true else x12.getD (↑x13) Bool.false;               have x13 : List Bool := List.foldl (fun (x13 : List Bool) (x14 : Fin (3 : ℕ) × Fin (26 : ℕ) × Fin (26 : ℕ)) => x13 ++ [if ↑x14.1 = (0 : ℕ) then x12 x13 x14.2.1 && x12 x13 x14.2.2 else if ↑x14.1 = (1 : ℕ) then x12 x13 x14.2.1 || x12 x13 x14.2.2 else !x12 x13 x14.2.1]) (List.ofFn x11 ++ [x11 (0 : Fin (9 : ℕ)) || x11 (4 : Fin (9 : ℕ))]) (((1 : Fin (3 : ℕ)), x1, x2) :: x4);               x13.getD (↑x3) Bool.false ≠ [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x14 : ℕ) => x11 (Fin.ofNat (9 : ℕ) (x14 / (10 : ℕ))) && x11 (Fin.ofNat (9 : ℕ) (x14 % (10 : ℕ)))) :
    ∀ (x1 x2 x3 : Fin (26 : ℕ)) (x4 : List (Fin (3 : ℕ) × Fin (26 : ℕ) × Fin (26 : ℕ))),   x4.length ≤ (13 : ℕ) →     ↑x1 ≠ (9 : ℕ) ∧ ↑x2 ≠ (9 : ℕ) →       ↑x1 ≠ (25 : ℕ) →         ↑x2 ≠ (25 : ℕ) →           (∀ x9 < (9 : ℕ), (∃ x11 ∈ x4, ↑x11.2.1 = x9 ∨ ↑x11.2.2 = x9) ∨ ↑x1 = x9 ∧ (↑x2 = x9 ∨ (10 : ℕ) ≤ ↑x2 ∨ (x9, ↑x2) ∈ [((0 : ℕ), (3 : ℕ)), ((4 : ℕ), (1 : ℕ)), ((4 : ℕ), (5 : ℕ))]) ∨ ↑x2 = x9 ∧ (↑x1 = x9 ∨ (10 : ℕ) ≤ ↑x1 ∨ (x9, ↑x1) ∈ [((0 : ℕ), (3 : ℕ)), ((4 : ℕ), (1 : ℕ)), ((4 : ℕ), (5 : ℕ))])) →             ∃ x10 < (512 : ℕ),               have x11 : Fin (9 : ℕ) → Bool := fun (x11 : Fin (9 : ℕ)) => x10.testBit ↑x11;               have x12 : List Bool → Fin (26 : ℕ) → Bool := fun (x12 : List Bool) (x13 : Fin (26 : ℕ)) => if ↑x13 = (25 : ℕ) then Bool.true else x12.getD (↑x13) Bool.false;               have x13 : List Bool := List.foldl (fun (x13 : List Bool) (x14 : Fin (3 : ℕ) × Fin (26 : ℕ) × Fin (26 : ℕ)) => x13 ++ [if ↑x14.1 = (0 : ℕ) then x12 x13 x14.2.1 && x12 x13 x14.2.2 else if ↑x14.1 = (1 : ℕ) then x12 x13 x14.2.1 || x12 x13 x14.2.2 else !x12 x13 x14.2.1]) (List.ofFn x11 ++ [x11 (0 : Fin (9 : ℕ)) || x11 (4 : Fin (9 : ℕ))]) (((1 : Fin (3 : ℕ)), x1, x2) :: x4);               x13.getD (↑x3) Bool.false ≠ [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x14 : ℕ) => x11 (Fin.ofNat (9 : ℕ) (x14 / (10 : ℕ))) && x11 (Fin.ofNat (9 : ℕ) (x14 % (10 : ℕ))) := by
  intro a b o suffix hlen hseed ha hb hsupport
  by_cases few : suffix.countP (fun g => decide (g.1.val = 2)) ≤ 2
  · exact small a b o suffix hlen few hseed ha hb hsupport
  by_contra missing
  push_neg at missing
  let Wire := Fin 26
  let Op := Fin 3 × Wire × Wire
  let shift := fun i : Nat => if i < 9 then i else i+1
  let pin := fun i : Wire => if i.val = 25 then 9 else shift i.val
  let cv := fun g : Op =>
    if g.1.val = 0 then Gate.mk .and [pin g.2.1, pin g.2.2]
    else if g.1.val = 1 then Gate.mk .or [pin g.2.1, pin g.2.2]
    else Gate.mk .not [pin g.2.1]
  let ops : List Op := ((1 : Fin 3), a, b) :: suffix
  let circuit : Circuit := ⟨⟨.not, []⟩ :: ⟨.or, [0,4]⟩ :: ops.map cv, shift o.val⟩
  have cvLegal (g : Op) : (cv g).op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ (cv g).inputs.length ≤ 2 := by
    obtain ⟨op, v, w⟩ := g
    fin_cases op <;> simp [cv, Set.mem_insert_iff, Set.mem_singleton_iff]
  have legal : FanInTwo circuit := by
    intro g hg
    change g ∈ _ :: _ :: List.map cv ops at hg
    rcases List.mem_cons.mp hg with rfl | h
    · exact ⟨Or.inr (Or.inr rfl), by decide⟩
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨Or.inr (Or.inl rfl), by decide⟩
    obtain ⟨q, _, rfl⟩ := List.mem_map.mp h
    exact cvLegal q
  have computes (m : Nat) (hm : m < 512) := missing m hm
  have shifted (xs more : List Bool) (hx : xs.length = 9) (i : Nat) :
      (xs ++ (true :: more)).getD (shift i) false = (xs ++ more).getD i false := by
    by_cases h : i < 9
    · simp only [shift, if_pos h, List.getD_eq_getElem?_getD,
        List.getElem?_append_left (hx ▸ h)]
    · have h1 : xs.length ≤ i := by omega
      have h2 : xs.length ≤ i+1 := by omega
      have hs : i+1-xs.length = (i-xs.length)+1 := by omega
      simp only [shift, if_neg h, List.getD_eq_getElem?_getD, List.getElem?_append_right h1,
        List.getElem?_append_right h2, hs, List.getElem?_cons_succ]
  let read := fun (ws : List Bool) (i : Wire) => if i.val = 25 then true else ws.getD i.val false
  have pinned (xs more : List Bool) (hx : xs.length = 9) (i : Wire) :
      (xs ++ (true :: more)).getD (pin i) false = read (xs ++ more) i := by
    by_cases h : i.val = 25
    · simp only [pin, read, if_pos h, List.getD_eq_getElem?_getD, List.getElem?_append_right (show xs.length ≤ 9 by omega), hx]
      rfl
    · simpa only [pin, read, if_neg h] using shifted xs more hx i.val
  let val := fun (ws : List Bool) (q : Op) =>
    if q.1.val = 0 then read ws q.2.1 && read ws q.2.2
    else if q.1.val = 1 then read ws q.2.1 || read ws q.2.2 else !read ws q.2.1
  let tick := fun (l : List Bool) (g : Gate) => l ++ [g.op.eval (g.inputs.map fun j => l.getD j false)]
  have andEval (u v : Bool) : GateOp.and.eval [u,v] = (u && v) := by cases u <;> cases v <;> rfl
  have orEval (u v : Bool) : GateOp.or.eval [u,v] = (u || v) := by cases u <;> cases v <;> rfl
  have notEval (u : Bool) : GateOp.not.eval [u] = !u := rfl
  have trueGate : GateOp.not.eval [] = true := rfl
  have sim (xs : List Bool) (hx : xs.length = 9) (qs : List Op) (more : List Bool) :
      ∃ tail : List Bool,
        qs.foldl (fun l g => l ++ [val l g]) (xs ++ more) = xs ++ tail ∧
        (qs.map cv).foldl tick (xs ++ (true :: more)) = xs ++ (true :: tail) := by
    induction qs generalizing more with
    | nil => exact ⟨more,rfl,rfl⟩
    | cons g gs ih =>
      have eq : (cv g).op.eval ((cv g).inputs.map fun j => (xs ++ (true :: more)).getD j false) =
          val (xs ++ more) g := by
        by_cases h0 : g.1.val = 0 <;> by_cases h1 : g.1.val = 1 <;>
          simp only [cv, val, h0, h1, if_true, if_false, List.map_cons, List.map_nil, andEval,
            orEval, notEval, show ¬ (1 : Nat) = 0 by decide, pinned xs more hx]
      obtain ⟨t, he, hc⟩ := ih (more ++ [val (xs ++ more) g])
      refine ⟨t,?_,?_⟩
      · simpa only [List.foldl_cons, List.append_assoc] using he
      · simpa only [List.map_cons, List.foldl_cons, tick, eq, List.append_assoc, List.cons_append] using hc
  have verified (m : Nat) (hm : m < 512) : let x : Fin 9 → Bool := fun j => m.testBit j.val
       circuit.eval (List.ofFn x) = ([1,12,23,34,40,5,16,27,38,57,68,85] : List Nat).any
         (fun z => x (Fin.ofNat 9 (z / 10)) && x (Fin.ofNat 9 (z % 10))) := by
    let x : Fin 9 → Bool := fun j => m.testBit j.val
    let xs := List.ofFn x
    let u := x 0 || x 4
    have len : xs.length = 9 := by simp [xs]
    obtain ⟨t, ht, ct⟩ := sim xs len ops [u]
    have eq := computes m hm
    change ¬ ((List.foldl (fun l g => l ++ [val l g]) (xs ++ [u]) ops).getD o.val false ≠ _) at eq
    replace eq := Classical.not_not.mp eq
    rw [ht] at eq
    have init : tick (tick xs ⟨.not, []⟩) ⟨.or, [0,4]⟩ = xs ++ (true :: [u]) := by
      simp only [tick, List.map_cons, List.map_nil, trueGate, orEval]
      simp [xs, u, List.getD_eq_getElem?_getD]
    change (List.foldl tick (tick (tick xs ⟨.not, []⟩) ⟨.or, [0,4]⟩) (ops.map cv)).getD (shift o.val) false = _
    rw [init, ct, shifted xs t len o.val]
    exact eq
  have bound := binary circuit legal verified
  let nn := fun (g : Gate) => (GateOp.rec (motive := fun _ => Bool) true true false (fun _ => true) true g.op)
  let isN := fun (g : Op) => decide (g.1.val = 2)
  have complementary (g : Op) : nn (cv g) = !isN g := by
    obtain ⟨op, v, w⟩ := g
    fin_cases op <;> rfl
  have balance (qs : List Op) :
      (qs.map cv).countP nn + qs.countP isN = qs.length := by
    induction qs with
    | nil => rfl
    | cons g gs ih =>
      simp only [List.map_cons, List.countP_cons, List.length_cons, complementary]
      cases h : isN g <;> simp only [Bool.not_true, Bool.not_false, if_true, if_false,
        Bool.false_eq_true, reduceCtorEq] <;> omega
  have sum := balance suffix
  change 13 ≤ List.countP nn (_ :: _ :: cv ((1 : Fin 3),a,b) :: suffix.map cv) at bound
  simp only [List.countP_cons] at bound
  change 13 ≤ ((suffix.map cv).countP nn + 1) + 1 + 0 at bound
  change ¬ suffix.countP isN ≤ 2 at few
  omega
