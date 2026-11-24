import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem PEqualNP.Outside.R_meta_2341_739
    (geometry :
      let x1 : Type := Fin (13 : ℕ); let x2 : Type := Finset (Fin (26 : ℕ)); have x3 : Finset x1 := {(0 : x1), (1 : x1), (3 : x1), (9 : x1)}; have x4 : x1 → x1 → x2 := fun (x4 x5 : x1) => {Fin.castAdd (13 : ℕ) x4, Fin.natAdd (13 : ℕ) x5}; let x5 : Finset x1 → Prop := fun (x5 : Finset x1) => x5.card = (4 : ℕ) ∧ ∀ (x6 : x1), {x7 ∈ x5 | x7 - x6 ∈ x3}.card ≤ (2 : ℕ); have x6 : Finset x1 → Finset (Fin ((13 : ℕ) + (13 : ℕ))) := fun (x6 : Finset x1) => Finset.image (Fin.castAdd (13 : ℕ)) x6 ∪ Finset.image (Fin.natAdd (13 : ℕ)) {x7 : Fin (13 : ℕ) | ∀ x8 ∈ x6, x8 - x7 ∉ x3}; have x7 : x1 → x1 → Finset x2 := fun (x7 x8 : x1) => Finset.image (fun (x9 : x1 × x1) => x4 x9.1 x9.2) ({x9 ∈ Finset.univ.product Finset.univ | x9.1 - x9.2 ∈ x3 ∧ (x9.1 ≠ x7 ∨ x9.2 ≠ x8)}); have x8 : x1 → x1 → Finset x2 := fun (x8 x9 : x1) => x7 x8 x9 ∪ Finset.image x6 (Finset.filter x5 Finset.univ); have x9 : x1 → x1 → x2 → Prop := fun (x9 x10 : x1) (x11 : x2) => ∀ x12 ∈ Finset.powerset x11, x12.card ≤ (4 : ℕ) → ∃ x15 ∈ x8 x9 x10, x12 ⊆ x15; ∀ (x10 x11 : x1) (x12 : x2), x9 x10 x11 x12 → (∀ (x14 : Finset x1), x5 x14 → ¬x12 ⊆ x6 x14) → x12 ∈ x7 x10 x11)
    (program :
      let x1 : Type := Fin (13 : ℕ); let x2 : Type := Finset (Fin (26 : ℕ)); let x3 : Type := Finset x2; have x4 : Finset x1 := {(0 : x1), (1 : x1), (3 : x1), (9 : x1)}; have x5 : x1 → x1 → x2 := fun (x5 x6 : x1) => {Fin.castAdd (13 : ℕ) x5, Fin.natAdd (13 : ℕ) x6}; let x6 : Finset x1 → Prop := fun (x6 : Finset x1) => x6.card = (4 : ℕ) ∧ ∀ (x7 : x1), {x8 ∈ x6 | x8 - x7 ∈ x4}.card ≤ (2 : ℕ); have x7 : Finset x1 → Finset (Fin ((13 : ℕ) + (13 : ℕ))) := fun (x7 : Finset x1) => Finset.image (Fin.castAdd (13 : ℕ)) x7 ∪ Finset.image (Fin.natAdd (13 : ℕ)) {x8 : Fin (13 : ℕ) | ∀ x9 ∈ x7, x9 - x8 ∉ x4}; have x8 : x1 → x1 → Finset x2 := fun (x8 x9 : x1) => Finset.image (fun (x10 : x1 × x1) => x5 x10.1 x10.2) ({x10 ∈ Finset.univ.product Finset.univ | x10.1 - x10.2 ∈ x4 ∧ (x10.1 ≠ x8 ∨ x10.2 ≠ x9)}); have x9 : x1 → x1 → Finset x2 := fun (x9 x10 : x1) => x8 x9 x10 ∪ Finset.image x7 (Finset.filter x6 Finset.univ); let x10 : x1 → x1 → x2 → Prop := fun (x10 x11 : x1) (x12 : x2) => ∀ x13 ∈ Finset.powerset x12, x13.card ≤ (4 : ℕ) → ∃ x16 ∈ x9 x10 x11, x13 ⊆ x16; have x11 : x1 → x1 → x3 → x3 → Finset x2 := fun (x11 x12 : x1) (x13 x14 : x3) => Finset.filter (x10 x11 x12) (Finset.biUnion x13 fun (x15 : x2) => Finset.image (fun (x16 : x2) => x15 ∪ x16) x14); have x12 : List x3 := (List.ofFn fun (x12 : Fin (26 : ℕ)) => {{x12}}) ++ [∅, {∅}]; ∀ (x13 x14 : x1) (x15 : List x3), (∀ (x16 : Fin x15.length), have x17 : List x3 := x12 ++ List.take (↑x16) x15; ∃ x18 ∈ x17, ∃ x19 ∈ x17, x15.get x16 = x18 ∪ x19 ∨ x15.get x16 = x11 x13 x14 x18 x19) → x8 x13 x14 ∈ x12 ++ x15 → (63 : ℕ) ≤ x15.length) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : Fin (13 : ℕ)) (x4 : Bool),   PEqualNP.MetaComplexity.Monotone2 x1 →     (∀ (x6 : Fin x1.gates.length), ∀ x7 ∈ (x1.gates.get x6).inputs, x7 < (27 : ℕ) + ↑x6) →       have x7 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};       have x8 : Fin (13 : ℕ) → Fin (13 : ℕ) → List Bool := fun (x8 x9 : Fin (13 : ℕ)) => (List.ofFn fun (x10 : Fin (13 : ℕ)) => Decidable.decide (x10 = x8)) ++ List.ofFn fun (x10 : Fin (13 : ℕ)) => Decidable.decide (x10 = x9);       have x9 : Finset (Fin (13 : ℕ)) → List Bool := fun (x9 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x10 : Fin (13 : ℕ)) => Decidable.decide (x10 ∈ x9)) ++ List.ofFn fun (x10 : Fin (13 : ℕ)) => Decidable.decide (∀ x11 ∈ x9, x11 - x10 ∉ x7);       have x10 : Finset (Fin (13 : ℕ)) → Prop := fun (x10 : Finset (Fin (13 : ℕ))) => x10.card = (4 : ℕ) ∧ ∀ (x11 : Fin (13 : ℕ)), {x12 ∈ x10 | x12 - x11 ∈ x7}.card ≤ (2 : ℕ);       (∀ (x11 x12 : Fin (13 : ℕ)), x11 - x12 ∈ x7 → x11 ≠ x2 ∨ x12 ≠ x3 → x1.eval (x8 x11 x12 ++ [x4]) = Bool.true) → (∀ (x12 : Finset (Fin (13 : ℕ))), x10 x12 → x1.eval (x9 x12 ++ [x4]) = Bool.false) → (63 : ℕ) ≤ x1.size := by
  classical
  let M := Finset (Fin 26)
  let P := Finset M

  let D : Finset (Fin 13) := {0, 1, 3, 9}

  let pos (p l : Fin 13) : M :=
    {Fin.castAdd 13 p, Fin.natAdd 13 l}

  let quad (Q : Finset (Fin 13)) : Prop :=
    Q.card = 4 ∧ ∀ l : Fin 13, (Q.filter (fun p => p-l ∈ D)).card ≤ 2

  let neg (Q : Finset (Fin 13)) : M :=
    Q.image (Fin.castAdd 13) ∪
    (Finset.univ.filter (fun l : Fin 13 => ∀ p ∈ Q, p-l ∉ D)).image (Fin.natAdd 13)

  let target (a b : Fin 13) : P :=
    ((Finset.univ.product Finset.univ).filter
      (fun pl : Fin 13 × Fin 13 => pl.1-pl.2 ∈ D ∧ (pl.1 ≠ a ∨ pl.2 ≠ b))).image
      (fun pl => pos pl.1 pl.2)

  let tests (a b : Fin 13) : P :=
    target a b ∪ (Finset.univ.filter quad).image neg

  let keep (a b : Fin 13) (S : M) : Prop :=
    ∀ T ∈ S.powerset, T.card ≤ 4 → ∃ R ∈ tests a b, T ⊆ R

  let mul (a b : Fin 13) (A B : P) : P :=
    (A.biUnion (fun S => B.image (fun T => S ∪ T))).filter (keep a b)

  let basis : List P := (List.ofFn (fun i : Fin 26 => ({ {i} } : P))) ++ [∅, {∅}]

  let valid (a b : Fin 13) (t : List P) : Prop :=
    ∀ i : Fin t.length,
      let pool := basis ++ t.take i.val
      ∃ A ∈ pool, ∃ B ∈ pool, t.get i = A ∪ B ∨ t.get i = mul a b A B

  let Geometry : Prop :=
    ∀ a b : Fin 13, ∀ S : M, keep a b S →
      (∀ Q : Finset (Fin 13), quad Q → ¬ S ⊆ neg Q) → S ∈ target a b

  let ProgramBound : Prop :=
    ∀ a b : Fin 13, ∀ t : List P,
      valid a b t → target a b ∈ basis ++ t → 63 ≤ t.length

  let input (R : M) (c : Bool) : List Bool :=
    List.ofFn (fun i : Fin 26 => decide (i ∈ R)) ++ [c]

  let value (A : P) (R : M) : Bool := decide (∃ S ∈ A, S ⊆ R)


  have hGeometry : Geometry := geometry
  have hProgram : ProgramBound := program

  have keep_of_subset_test (a b : Fin 13) (S R : M)
      (hR : R ∈ tests a b) (hS : S ⊆ R) : keep a b S := by
    intro T hT _
    exact ⟨R, hR, (Finset.mem_powerset.mp hT).trans hS⟩

  have value_zero (R : M) : value ∅ R = false := by
    simp [value, M, P]

  have value_unit (R : M) : value {∅} R = true := by
    simp [value, M, P]

  have value_variable (i : Fin 26) (R : M) :
      value ({ {i} } : P) R = decide (i ∈ R) := by
    simp [value, M, P, Finset.singleton_subset_iff]

  have value_union (A B : P) (R : M) :
      value (A ∪ B) R = (value A R || value B R) := by
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.or_eq_true, value, decide_eq_true_eq]
    constructor
    · rintro ⟨S, hS, hR⟩
      rcases Finset.mem_union.mp hS with hS | hS
      · exact Or.inl ⟨S, hS, hR⟩
      · exact Or.inr ⟨S, hS, hR⟩
    · rintro (⟨S, hS, hR⟩ | ⟨S, hS, hR⟩)
      · exact ⟨S, Finset.mem_union_left _ hS, hR⟩
      · exact ⟨S, Finset.mem_union_right _ hS, hR⟩

  have value_mul (a b : Fin 13) (A B : P) (R : M)
      (hR : R ∈ tests a b) :
      value (mul a b A B) R = (value A R && value B R) := by
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, value, decide_eq_true_eq]
    constructor
    · rintro ⟨U, hU, hUR⟩
      obtain ⟨hU, _⟩ := Finset.mem_filter.mp hU
      obtain ⟨S, hS, hU⟩ := Finset.mem_biUnion.mp hU
      obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hU
      exact ⟨⟨S, hS, (Finset.subset_union_left).trans hUR⟩,
        ⟨T, hT, (Finset.subset_union_right).trans hUR⟩⟩
    · rintro ⟨⟨S, hS, hSR⟩, ⟨T, hT, hTR⟩⟩
      have hUR : S ∪ T ⊆ R := Finset.union_subset hSR hTR
      refine ⟨S ∪ T, Finset.mem_filter.mpr ⟨?_, keep_of_subset_test a b _ R hR hUR⟩, hUR⟩
      exact Finset.mem_biUnion.mpr ⟨S, hS, Finset.mem_image.mpr ⟨T, hT, rfl⟩⟩

  have mul_good (a b : Fin 13) (A B : P) :
      ∀ S ∈ mul a b A B, keep a b S := by
    intro S hS
    exact (Finset.mem_filter.mp hS).2

  have zero_in_basis : (∅ : P) ∈ basis := by
    simp [basis]

  have unit_in_basis : ({∅} : P) ∈ basis := by
    simp [basis]

  have variable_in_basis (i : Fin 26) : ({ {i} } : P) ∈ basis := by
    apply List.mem_append_left
    exact List.mem_ofFn.mpr ⟨i, rfl⟩

  let project (R : M) (W : List P) : List Bool := W.map (fun A => value A R)

  let initial (c : Bool) : List P :=
    List.ofFn (fun i : Fin 26 => ({ {i} } : P)) ++ [if c then {∅} else ∅]

  have project_initial (R : M) (c : Bool) : project R (initial c) = input R c := by
    cases c <;> simp [project, initial, input, value_variable, value_zero, value_unit]

  have initial_in_basis (c : Bool) : ∀ A ∈ initial c, A ∈ basis := by
    intro A hA
    rcases List.mem_append.mp hA with hA | hA
    · exact List.mem_append_left _ hA
    · have h := List.mem_singleton.mp hA
      rw [h]
      cases c
      · exact zero_in_basis
      · exact unit_in_basis

  have lookup_value (R : M) (W : List P) (i : ℕ) :
      (project R W).getD i false = value (W.getD i ∅) R := by
    simp only [project, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases W[i]? <;> simp [value_zero]


  let gatePoly (a b : Fin 13) (W : List P) (g : Gate) : P :=
    if g.inputs.length = 0 then
      if g.op = .and then {∅} else ∅
    else if g.inputs.length = 1 then
      W.getD (g.inputs.getD 0 0) ∅
    else if g.op = .and then
      mul a b (W.getD (g.inputs.getD 0 0) ∅) (W.getD (g.inputs.getD 1 0) ∅)
    else
      W.getD (g.inputs.getD 0 0) ∅ ∪ W.getD (g.inputs.getD 1 0) ∅

  let polyStep (a b : Fin 13) (W : List P) (g : Gate) : List P :=
    W ++ [gatePoly a b W g]

  let boolStep (W : List Bool) (g : Gate) : List Bool :=
    W ++ [g.op.eval (g.inputs.map (fun i => W.getD i false))]

  have gatePoly_value (a b : Fin 13) (R : M) (hR : R ∈ tests a b)
      (W : List P) (g : Gate)
      (allowed : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
      value (gatePoly a b W g) R =
        g.op.eval (g.inputs.map (fun i => (project R W).getD i false)) := by
    have op : g.op = .and ∨ g.op = .or := allowed.1
    have ae (l : List Bool) : GateOp.and.eval l = l.all id := rfl
    have oe (l : List Bool) : GateOp.or.eval l = l.any id := rfl
    have look (i : ℕ) : (project R W)[i]?.getD false = value (W[i]?.getD ∅) R := by
      simpa only [List.getD_eq_getElem?_getD] using lookup_value R W i
    cases h : g.inputs with
    | nil =>
      rcases op with e | e <;>
        simp [gatePoly, h, e, ae, oe, value_zero, value_unit]
    | cons i ks =>
      cases hk : ks with
      | nil =>
        rcases op with e | e <;>
          simp [gatePoly, h, hk, e, ae, oe, look]
      | cons j rest =>
        have tail : rest = [] := by
          have m := allowed.2
          rw [h, hk] at m
          simpa using m
        rcases op with e | e
        · simp [gatePoly, h, hk, tail, e, ae, oe, look, value_mul a b _ _ R hR]
        · simp [gatePoly, h, hk, tail, e, ae, oe, look, value_union]

  have fold_commute (a b : Fin 13) (R : M) (hR : R ∈ tests a b)
      (gs : List Gate)
      (hm : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
      (W : List P) :
      project R (gs.foldl (polyStep a b) W) = gs.foldl boolStep (project R W) := by
    induction gs generalizing W with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, List.foldl_cons, ih (fun g hg => hm g (List.mem_cons_of_mem _ hg))]
      apply congrArg (gs.foldl boolStep)
      change project R (W ++ [gatePoly a b W g]) =
        project R W ++ [g.op.eval (g.inputs.map (fun i => (project R W).getD i false))]
      rw [show project R (W ++ [gatePoly a b W g]) =
        project R W ++ [value (gatePoly a b W g) R] by
          exact List.map_append]
      rw [gatePoly_value a b R hR W g (hm g List.mem_cons_self)]

  have append_valid (a b : Fin 13) (t : List P) (ok : valid a b t) (z : P)
      (step : ∃ A ∈ basis ++ t, ∃ B ∈ basis ++ t,
        z = A ∪ B ∨ z = mul a b A B) : valid a b (t ++ [z]) := by
    intro i
    change ∃ A ∈ basis ++ (t ++ [z]).take i.val,
      ∃ B ∈ basis ++ (t ++ [z]).take i.val,
        (t ++ [z])[i.val] = A ∪ B ∨ (t ++ [z])[i.val] = mul a b A B
    by_cases lt : i.val < t.length
    · have h := ok ⟨i.val, lt⟩
      change ∃ A ∈ basis ++ t.take i.val, ∃ B ∈ basis ++ t.take i.val,
        t[i.val] = A ∪ B ∨ t[i.val] = mul a b A B at h
      simpa only [List.take_append_of_le_length lt.le, List.getElem_append_left lt] using h
    · have eq : i.val = t.length := by
        have hi := i.isLt
        simp only [List.length_append, List.length_singleton] at hi
        omega
      have atEnd : (t ++ [z])[i.val] = z := by
        rw [List.getElem_append_right (by omega)]
        simp [eq]
      rw [atEnd, List.take_left' eq.symm]
      exact step

  have read_pool (t W : List P) (old : ∀ A ∈ W, A ∈ basis ++ t) (i : ℕ) :
      W.getD i ∅ ∈ basis ++ t := by
    by_cases hi : i < W.length
    · rw [List.getD_eq_getElem _ _ hi]
      exact old _ (List.getElem_mem hi)
    · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hi)]
      exact List.mem_append_left _ zero_in_basis

  have gatePoly_step (a b : Fin 13) (g : Gate)
      (allowed : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
      (t W : List P) (old : ∀ A ∈ W, A ∈ basis ++ t) :
      ∃ A ∈ basis ++ t, ∃ B ∈ basis ++ t,
        gatePoly a b W g = A ∪ B ∨ gatePoly a b W g = mul a b A B := by
    have op : g.op = .and ∨ g.op = .or := allowed.1
    cases h : g.inputs with
    | nil =>
      rcases op with e | e
      · refine ⟨{∅}, List.mem_append_left _ unit_in_basis,
          {∅}, List.mem_append_left _ unit_in_basis, Or.inl ?_⟩
        simp [gatePoly, h, e]
      · refine ⟨∅, List.mem_append_left _ zero_in_basis,
          ∅, List.mem_append_left _ zero_in_basis, Or.inl ?_⟩
        simp [gatePoly, h, e]
    | cons i ks =>
      cases hk : ks with
      | nil =>
        refine ⟨W.getD i ∅, read_pool t W old i,
          W.getD i ∅, read_pool t W old i, Or.inl ?_⟩
        simp [gatePoly, h, hk]
      | cons j rest =>
        refine ⟨W.getD i ∅, read_pool t W old i,
          W.getD j ∅, read_pool t W old j, ?_⟩
        rcases op with e | e
        · exact Or.inr (by simp [gatePoly, h, hk, e])
        · exact Or.inl (by simp [gatePoly, h, hk, e])

  have gatePoly_good (a b : Fin 13) (g : Gate)
      (allowed : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
      (t W : List P) (old : ∀ A ∈ W, A ∈ basis ++ t)
      (good : ∀ A ∈ basis ++ t, ∀ S ∈ A, keep a b S) :
      ∀ S ∈ gatePoly a b W g, keep a b S := by
    obtain ⟨A, hA, B, hB, eq⟩ := gatePoly_step a b g allowed t W old
    rcases eq with eq | eq
    · rw [eq]
      intro S hS
      rcases Finset.mem_union.mp hS with hS | hS
      · exact good A hA S hS
      · exact good B hB S hS
    · rw [eq]
      exact mul_good a b A B

  have extract_fold (a b : Fin 13) (gs : List Gate)
      (hm : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
      (t W : List P) (ok : valid a b t)
      (old : ∀ A ∈ W, A ∈ basis ++ t)
      (good : ∀ A ∈ basis ++ t, ∀ S ∈ A, keep a b S) :
      ∃ T : List P, valid a b T ∧ T.length = t.length + gs.length ∧
        (∀ A ∈ gs.foldl (polyStep a b) W, A ∈ basis ++ T) ∧
        (∀ A ∈ basis ++ T, ∀ S ∈ A, keep a b S) := by
    induction gs generalizing t W with
    | nil => exact ⟨t, ok, by simp, old, good⟩
    | cons g gs ih =>
      let z := gatePoly a b W g
      have hg := hm g List.mem_cons_self
      have hq : valid a b (t ++ [z]) :=
        append_valid a b t ok z (gatePoly_step a b g hg t W old)
      have new : ∀ A ∈ polyStep a b W g, A ∈ basis ++ (t ++ [z]) := by
        intro A hA
        rcases List.mem_append.mp hA with hA | hA
        · rw [← List.append_assoc]
          exact List.mem_append_left _ (old A hA)
        · have eq : A = z := List.mem_singleton.mp hA
          rw [eq]
          simp
      have newgood : ∀ A ∈ basis ++ (t ++ [z]), ∀ S ∈ A, keep a b S := by
        intro A hA S hS
        rw [← List.append_assoc] at hA
        rcases List.mem_append.mp hA with hA | hA
        · exact good A hA S hS
        · have eq : A = z := List.mem_singleton.mp hA
          have hz : S ∈ z := by
            rw [← eq]
            exact hS
          exact gatePoly_good a b g hg t W old good S hz
      obtain ⟨T, hT, len, all, allgood⟩ :=
        ih (fun g hg => hm g (List.mem_cons_of_mem _ hg))
          (t ++ [z]) (polyStep a b W g) hq new newgood
      refine ⟨T, hT, ?_, ?_, allgood⟩
      · simp only [List.length_append, List.length_singleton, List.length_cons, List.length_nil] at *
        omega
      · simpa only [List.foldl_cons] using all


  have extract (a b : Fin 13) (C : Circuit) (c : Bool)
      (hm : Monotone2 C)
      (basisGood : ∀ A ∈ basis, ∀ S ∈ A, keep a b S) :
      ∃ t A, valid a b t ∧ t.length = C.size ∧ A ∈ basis ++ t ∧
        (∀ S ∈ A, keep a b S) ∧
        ∀ R ∈ tests a b, value A R = C.eval (input R c) := by
    have emptyValid : valid a b [] := by
      intro i
      exact Fin.elim0 i
    have old : ∀ A ∈ initial c, A ∈ basis ++ [] := by
      simpa only [List.append_nil] using initial_in_basis c
    have good : ∀ A ∈ basis ++ [], ∀ S ∈ A, keep a b S := by
      simpa only [List.append_nil] using basisGood
    obtain ⟨t, ht, len, all, allgood⟩ :=
      extract_fold a b C.gates hm [] (initial c) emptyValid old good
    let W := C.gates.foldl (polyStep a b) (initial c)
    let A := W.getD C.output ∅
    have hA : A ∈ basis ++ t := read_pool t W all C.output
    refine ⟨t, A, ht, ?_, hA, allgood A hA, ?_⟩
    · change t.length = C.gates.length
      simpa only [List.length_nil, zero_add] using len
    · intro R hR
      have eq := fold_commute a b R hR C.gates hm (initial c)
      have see := congrArg (fun v : List Bool => v.getD C.output false) eq
      rw [lookup_value, project_initial] at see
      exact see


  have label_facts :
      (∀ i j : Fin 13, Fin.castAdd 13 i = Fin.castAdd 13 j ↔ i = j) ∧
      (∀ i j : Fin 13, Fin.natAdd 13 i = Fin.natAdd 13 j ↔ i = j) ∧
      (∀ i j : Fin 13, Fin.castAdd 13 i ≠ Fin.natAdd 13 j) ∧
      (∀ i j : Fin 13, Fin.natAdd 13 i ≠ Fin.castAdd 13 j) := by
    decide +kernel

  have input_split (R : M) (c : Bool) :
      input R c =
        ((List.ofFn (fun i : Fin 13 => decide (Fin.castAdd 13 i ∈ R))) ++
         List.ofFn (fun i : Fin 13 => decide (Fin.natAdd 13 i ∈ R))) ++ [c] := by
    have hcast (i : Fin 13) :
        i.castLE (Nat.le_add_right 13 13) = Fin.castAdd 13 i := by
      apply Fin.ext
      rfl
    simpa only [input, hcast] using
      congrArg (fun xs : List Bool => xs ++ [c])
        (List.ofFn_add (n := 13) (m := 13) (f := fun i => decide (i ∈ R)))

  have input_pos (p l : Fin 13) (c : Bool) :
      input (pos p l) c =
        ((List.ofFn (fun i : Fin 13 => decide (i = p))) ++
         List.ofFn (fun i : Fin 13 => decide (i = l))) ++ [c] := by
    rw [input_split]
    simp only [pos, M, Finset.mem_insert, Finset.mem_singleton,
      label_facts.1, label_facts.2.1, label_facts.2.2.1,
      label_facts.2.2.2, or_false, false_or]

  have neg_left (Q : Finset (Fin 13)) (i : Fin 13) :
      Fin.castAdd 13 i ∈ neg Q ↔ i ∈ Q := by
    constructor
    · intro hi
      rcases Finset.mem_union.mp hi with hp | hl
      · obtain ⟨p, hp, hpi⟩ := Finset.mem_image.mp hp
        have heq : p = i := (label_facts.1 p i).mp hpi
        simpa only [heq] using hp
      · obtain ⟨l, _, hli⟩ := Finset.mem_image.mp hl
        exact False.elim (label_facts.2.2.2 l i hli)
    · intro hi
      exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩)

  have neg_right (Q : Finset (Fin 13)) (i : Fin 13) :
      Fin.natAdd 13 i ∈ neg Q ↔ ∀ p ∈ Q, p-i ∉ D := by
    constructor
    · intro hi
      rcases Finset.mem_union.mp hi with hp | hl
      · obtain ⟨p, _, hpi⟩ := Finset.mem_image.mp hp
        exact False.elim (label_facts.2.2.1 p i hpi)
      · obtain ⟨l, hl, hli⟩ := Finset.mem_image.mp hl
        have heq : l = i := (label_facts.2.1 l i).mp hli
        simpa only [heq] using (Finset.mem_filter.mp hl).2
    · intro hi
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr
        ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩, rfl⟩

  have input_neg (Q : Finset (Fin 13)) (c : Bool) :
      input (neg Q) c =
        ((List.ofFn (fun i : Fin 13 => decide (i ∈ Q))) ++
         List.ofFn (fun i : Fin 13 => decide (∀ p ∈ Q, p-i ∉ D))) ++ [c] := by
    rw [input_split]
    simp only [neg_left, neg_right]

  have pos_mem_target (a b p l : Fin 13)
      (hi : p-l ∈ D) (hne : p ≠ a ∨ l ≠ b) : pos p l ∈ target a b := by
    apply Finset.mem_image.mpr
    exact ⟨(p, l), by simp [hi, hne], rfl⟩

  have pos_mem_tests (a b p l : Fin 13)
      (hi : p-l ∈ D) (hne : p ≠ a ∨ l ≠ b) : pos p l ∈ tests a b := by
    exact Finset.mem_union_left _ (pos_mem_target a b p l hi hne)

  have neg_mem_tests (a b : Fin 13) (Q : Finset (Fin 13))
      (hQ : quad Q) : neg Q ∈ tests a b := by
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨Q, by simp [hQ], rfl⟩

  have pos_card (p l : Fin 13) : (pos p l).card = 2 := by
    exact Finset.card_pair (label_facts.2.2.1 p l)

  have target_card (a b : Fin 13) (S : M) (hS : S ∈ target a b) :
      S.card = 2 := by
    obtain ⟨⟨p, l⟩, _, rfl⟩ := Finset.mem_image.mp hS
    exact pos_card p l

  have target_subset_eq (a b : Fin 13) (S T : M)
      (hS : S ∈ target a b) (hT : T ∈ target a b) (hST : S ⊆ T) : S = T := by
    apply Finset.eq_of_subset_of_card_le hST
    exact le_of_eq ((target_card a b T hT).trans (target_card a b S hS).symm)

  have point_flag_choices : ∀ p : Fin 13,
      p-p ∈ D ∧ p-(p-1) ∈ D ∧ p-1 ≠ p := by
    decide +kernel

  have line_flag_choices : ∀ l : Fin 13,
      l-l ∈ D ∧ (l+1)-l ∈ D ∧ l+1 ≠ l := by
    decide +kernel

  have left_variable_in_test (a b p : Fin 13) :
      ∃ R ∈ tests a b, Fin.castAdd 13 p ∈ R := by
    by_cases h : p ≠ a ∨ p ≠ b
    · exact ⟨pos p p, pos_mem_tests a b p p (point_flag_choices p).1 h,
        by simp [pos, M]⟩
    · have hpb : p = b := by
        by_contra hpb
        exact h (Or.inr hpb)
      have hne : p-1 ≠ b := by
        simpa only [← hpb] using (point_flag_choices p).2.2
      exact ⟨pos p (p-1),
        pos_mem_tests a b p (p-1) (point_flag_choices p).2.1 (Or.inr hne),
        by simp [pos, M]⟩

  have right_variable_in_test (a b l : Fin 13) :
      ∃ R ∈ tests a b, Fin.natAdd 13 l ∈ R := by
    by_cases h : l ≠ a ∨ l ≠ b
    · exact ⟨pos l l, pos_mem_tests a b l l (line_flag_choices l).1 h,
        by simp [pos, M]⟩
    · have hla : l = a := by
        by_contra hla
        exact h (Or.inl hla)
      have hne : l+1 ≠ a := by
        simpa only [← hla] using (line_flag_choices l).2.2
      exact ⟨pos (l+1) l,
        pos_mem_tests a b (l+1) l (line_flag_choices l).2.1 (Or.inl hne),
        by simp [pos, M]⟩

  have variable_in_test (a b : Fin 13) (i : Fin 26) :
      ∃ R ∈ tests a b, i ∈ R := by
    by_cases hi : i.val < 13
    · let p : Fin 13 := ⟨i.val, hi⟩
      have heq : i = Fin.castAdd 13 p := by
        apply Fin.ext
        rfl
      rw [heq]
      exact left_variable_in_test a b p
    · let l : Fin 13 := ⟨i.val - 13, by omega⟩
      have heq : i = Fin.natAdd 13 l := by
        apply Fin.ext
        change i.val = 13 + (i.val - 13)
        omega
      rw [heq]
      exact right_variable_in_test a b l

  have basis_good (a b : Fin 13) (A : P) (hA : A ∈ basis)
      (S : M) (hS : S ∈ A) : keep a b S := by
    rcases List.mem_append.mp hA with hA | hA
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hA
      have heq : S = {i} := Finset.mem_singleton.mp hS
      subst S
      obtain ⟨R, hR, hi⟩ := variable_in_test a b i
      exact keep_of_subset_test a b {i} R hR (Finset.singleton_subset_iff.mpr hi)
    · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hA
      rcases hA with rfl | rfl
      · exfalso
        simpa [M, P] using hS
      · have heq : S = ∅ := Finset.mem_singleton.mp hS
        subst S
        obtain ⟨R, hR, _⟩ := variable_in_test a b 0
        exact keep_of_subset_test a b ∅ R hR (Finset.empty_subset R)

  have output_eq (hGeometry : Geometry) (a b : Fin 13) (A : P)
      (hkeep : ∀ S ∈ A, keep a b S)
      (hpos : ∀ p l : Fin 13, p-l ∈ D → p ≠ a ∨ l ≠ b →
        value A (pos p l) = true)
      (hneg : ∀ Q : Finset (Fin 13), quad Q → value A (neg Q) = false) :
      A = target a b := by
    have hout : ∀ S ∈ A, S ∈ target a b := by
      intro S hS
      apply hGeometry a b S (hkeep S hS)
      intro Q hQ hsub
      have hval : value A (neg Q) = true := by
        simp only [value, decide_eq_true_eq]
        exact ⟨S, hS, hsub⟩
      have hfalse : (true : Bool) = false := hval.symm.trans (hneg Q hQ)
      cases hfalse
    apply Finset.Subset.antisymm
    · exact hout
    · intro R hR
      obtain ⟨⟨p, l⟩, hpl, rfl⟩ := Finset.mem_image.mp hR
      have hcond : p-l ∈ D ∧ (p ≠ a ∨ l ≠ b) := (Finset.mem_filter.mp hpl).2
      have hval : ∃ S ∈ A, S ⊆ pos p l := by
        simpa only [value, decide_eq_true_eq] using hpos p l hcond.1 hcond.2
      obtain ⟨S, hS, hsub⟩ := hval
      have heq : S = pos p l :=
        target_subset_eq a b S (pos p l) (hout S hS)
          (pos_mem_target a b p l hcond.1 hcond.2) hsub
      simpa only [heq] using hS


  intro C a b c hm hw
  dsimp only
  intro hp hn
  obtain ⟨t, A, hv, hlen, hA, hkeep, heval⟩ := extract a b C c hm (basis_good a b)
  have hpos : ∀ p l : Fin 13, p-l ∈ D → p ≠ a ∨ l ≠ b → value A (pos p l) = true := by
    intro p l hi hne
    rw [heval _ (pos_mem_tests a b p l hi hne), input_pos]
    exact hp p l hi hne
  have hneg : ∀ Q : Finset (Fin 13), quad Q → value A (neg Q) = false := by
    intro Q hQ
    rw [heval _ (neg_mem_tests a b Q hQ), input_neg]
    exact hn Q hQ
  have heq : A = target a b := output_eq hGeometry a b A hkeep hpos hneg
  have bound := hProgram a b t hv (heq ▸ hA)
  simpa only [hlen] using bound
