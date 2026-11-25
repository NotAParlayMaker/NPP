import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Saturation of both OR channels gives a collision on {0,8,t}.
-- The complete proof of the first child is included as local declarations.
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 3000 in
theorem PEqualNP.Outside.R_meta_5196_683
    (closed :
    let F : (Fin 9 → Bool) → Bool := fun x =>
      ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
        (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
    let row := fun x : Fin 9 → Bool => List.ofFn x ++ [x 0 || x 6]
    let reads := fun (i : ℕ) (g : Gate) =>
      (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains i
    ∀ (v t : Fin 9) (C : Circuit) (w : ℕ) (b : Bool),
    v ≠ 6 → FanInTwo C → w ≠ 6 → (t = 2 ∨ t = 7 ∨ t = 8) → (t = 8 ∨ t ≠ v) →
    (∃ g : Gate, g.op = .or ∧ (g.inputs = [6,t.val] ∨ g.inputs = [t.val,6]) ∧
      C.gates.filter (reads 6) = [g]) →
    (∀ x y : Fin 9 → Bool, (∀ i, i ≠ v → x i = y i) → F x ≠ F y →
      (C.wires (row x)).getD w false = !b) →
    ∃ x : Fin 9 → Bool,
      C.eval ((row x).set v.val (if b then x v || (C.wires (row x)).getD w false
        else x v && (C.wires (row x)).getD w false)) ≠ F x)
    (remaining :
    let F : (Fin 9 → Bool) → Bool := fun x =>
      ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
        (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
    let row := fun x : Fin 9 → Bool => List.ofFn x ++ [x 0 || x 6]
    let reads := fun (i : ℕ) (g : Gate) =>
      (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains i
    ∀ (v : Fin 9) (C : Circuit) (w : ℕ) (b : Bool),
      v ≠ 0 → v ≠ 6 → FanInTwo C → C.size = 13 → 10 ≤ w → w < 23 →
      (∀ g ∈ C.gates.take (w+1-10), v.val ∉ g.inputs) →
      (∀ x y : Fin 9 → Bool, (∀ i, i ≠ v → x i = y i) → F x ≠ F y →
        (C.wires (row x)).getD w false = !b) →
      (∃ g ∈ C.gates, reads 9 g = true) →
      (∃ g : Gate, g.op = .or ∧
        (∃ t ∉ ([0,6,8,9] : List ℕ), (t = 2 ∨ t = 7 → t = v.val) ∧
          (g.inputs = [6,t] ∨ g.inputs = [t,6])) ∧ C.gates.filter (reads 6) = [g]) →
      (∃ x : Fin 9 → Bool, x 6 = false ∧ (C.wires (row x)).getD w false = b) →
      ∃ x : Fin 9 → Bool, let value := (C.wires (row x)).getD w false
        C.eval ((row x).set v.val (if b then x v || value else x v && value)) ≠ F x) :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); have x2 : (Fin (9 : ℕ) → Bool) → List Bool := fun (x2 : Fin (9 : ℕ) → Bool) => List.ofFn x2 ++ [x2 (0 : Fin (9 : ℕ)) || x2 (6 : Fin (9 : ℕ))]; have x3 : ℕ → PEqualNP.CircuitLowerBounds.Gate → Bool := fun (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x4.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x4.inputs).contains x3; ∀ (x4 : Fin (9 : ℕ)) (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : ℕ) (x7 : Bool),   x4 ≠ (0 : Fin (9 : ℕ)) →     x4 ≠ (6 : Fin (9 : ℕ)) →       PEqualNP.MetaComplexity.FanInTwo x5 →         x5.size = (13 : ℕ) →           (10 : ℕ) ≤ x6 →             x6 < (23 : ℕ) →               (∀ x14 ∈ List.take (x6 + (1 : ℕ) - (10 : ℕ)) x5.gates, ↑x4 ∉ x14.inputs) →                 (∀ (x15 x16 : Fin (9 : ℕ) → Bool), (∀ (x17 : Fin (9 : ℕ)), x17 ≠ x4 → x15 x17 = x16 x17) → x1 x15 ≠ x1 x16 → (x5.wires (x2 x15)).getD x6 Bool.false = !x7) →                   (∃ x16 ∈ x5.gates, x3 (9 : ℕ) x16 = Bool.true) →                     (∃ (x17 : PEqualNP.CircuitLowerBounds.Gate), x17.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (∃ x18 ∉ [(0 : ℕ), (6 : ℕ), (9 : ℕ)], x17.inputs = [(6 : ℕ), x18] ∨ x17.inputs = [x18, (6 : ℕ)]) ∧ List.filter (x3 (6 : ℕ)) x5.gates = [x17]) →                       (∃ (x18 : Fin (9 : ℕ) → Bool), x18 (6 : Fin (9 : ℕ)) = Bool.false ∧ (x5.wires (x2 x18)).getD x6 Bool.false = x7) →                         ∃ (x19 : Fin (9 : ℕ) → Bool),                           have x20 : Bool := (x5.wires (x2 x19)).getD x6 Bool.false;                           x5.eval ((x2 x19).set (↑x4) (if x7 = Bool.true then x19 x4 || x20 else x19 x4 && x20)) ≠ x1 x19 := by
  let reads (i : ℕ) (g : Gate) : Bool :=
    (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains i

  let step (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

  have gate_agrees (g : Gate) (fan : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
      (p : ℕ) (a b : List Bool) (agree : ∀ i, i ≠ p → a.getD i false = b.getD i false)
      (unused : reads p g = false) :
      g.op.eval (g.inputs.map fun i => a.getD i false) =
        g.op.eval (g.inputs.map fun i => b.getD i false) := by
    have ea (l : List Bool) : GateOp.and.eval l = l.all id := rfl
    have eo (l : List Bool) : GateOp.or.eval l = l.any id := rfl
    have en (l : List Bool) : GateOp.not.eval l = !(l.headD false) := rfl
    have eaf : GateOp.and.eval [false] = false := rfl
    have eof : GateOp.or.eval [false] = false := rfl
    have ct (l : List ℕ) (i : ℕ) : l.contains i = false ↔ i ∉ l := by simp
    rcases fan.1 with hop | hop | hop
    · have take : g.inputs.take 2 = g.inputs := List.take_of_length_le fan.2
      have no : p ∉ g.inputs := by simpa only [reads, hop, eaf, Bool.cond_false, take, ct] using unused
      rw [hop]; congr 1
      apply List.map_congr_left
      intro i hi
      exact agree i (fun h => no (h ▸ hi))
    · have take : g.inputs.take 2 = g.inputs := List.take_of_length_le fan.2
      have no : p ∉ g.inputs := by simpa only [reads, hop, eof, Bool.cond_false, take, ct] using unused
      rw [hop]; congr 1
      apply List.map_congr_left
      intro i hi
      exact agree i (fun h => no (h ▸ hi))
    · change g.op = GateOp.not at hop
      rw [hop]
      cases data : g.inputs with
      | nil => rfl
      | cons i rest =>
        have no : p ∉ [i] := by simpa only [reads, hop, en, List.headD_cons,
          Bool.not_false, Bool.cond_true, data, List.take_succ_cons, List.take_zero, ct] using unused
        simp only [en, List.map_cons, List.headD_cons]
        rw [agree i (fun h => no (h ▸ List.mem_cons_self))]

  -- A single OR channel carrying p becomes independent of p when its other raw
  -- input q is true. The statement permits missing and forward references.
  have saturated_reader (C : Circuit) (fan : FanInTwo C) (p q : ℕ)
      (shape : ∀ g ∈ C.gates, reads p g = true →
        g.op = .or ∧ (g.inputs = [p,q] ∨ g.inputs = [q,p]))
      (a b : List Bool) (len : a.length = b.length)
      (hp : p < a.length) (hq : q < a.length)
      (aq : a.getD q false = true) (bq : b.getD q false = true)
      (agree : ∀ i, i ≠ p → a.getD i false = b.getD i false) :
      ∀ i, i ≠ p → (C.wires a).getD i false = (C.wires b).getD i false := by
    have run : ∀ gs : List Gate,
        (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
        (∀ g ∈ gs, reads p g = true → g.op = .or ∧ (g.inputs = [p,q] ∨ g.inputs = [q,p])) →
        ∀ a b : List Bool, a.length = b.length → p < a.length → q < a.length →
        a.getD q false = true → b.getD q false = true →
        (∀ i, i ≠ p → a.getD i false = b.getD i false) →
        ∀ i, i ≠ p → (gs.foldl step a).getD i false = (gs.foldl step b).getD i false := by
      intro gs
      induction gs with
      | nil => intro _ _ a b _ _ _ _ _ eq i hi; exact eq i hi
      | cons g gs ih =>
        intro legal form a b len hp hq aq bq eq i hi
        have gate : g.op.eval (g.inputs.map fun j => a.getD j false) =
            g.op.eval (g.inputs.map fun j => b.getD j false) := by
          cases hr : reads p g with
          | false => exact gate_agrees g (legal g List.mem_cons_self) p a b eq hr
          | true =>
            obtain ⟨op, inputs⟩ := form g List.mem_cons_self hr
            have eo (u v : Bool) : GateOp.or.eval [u,v] = (u || v) := by cases u <;> cases v <;> rfl
            rcases inputs with inputs | inputs <;>
              simp only [op, inputs, List.map_cons, List.map_nil, eo, aq, bq, Bool.or_true, Bool.true_or]
        apply ih (fun h hh => legal h (List.mem_cons_of_mem _ hh))
          (fun h hh => form h (List.mem_cons_of_mem _ hh)) (step a g) (step b g)
          (by simp only [step, List.length_append, List.length_singleton, len])
          (by simp only [step, List.length_append, List.length_singleton]; omega)
          (by simp only [step, List.length_append, List.length_singleton]; omega)
          ((List.getD_append _ _ _ _ hq).trans aq)
          ((List.getD_append _ _ _ _ (by omega)).trans bq) ?_ i hi
        intro j hj
        rcases Nat.lt_trichotomy j a.length with lt | same | gt
        · change (a ++ [_]).getD j false = (b ++ [_]).getD j false
          rw [List.getD_append _ _ _ _ lt, List.getD_append _ _ _ _ (by omega)]
          exact eq j hj
        · subst j
          have snoc (xs : List Bool) (v : Bool) : (xs ++ [v]).getD xs.length false = v := by
            simp [List.getD_eq_getElem?_getD]
          change (a ++ [_]).getD a.length false = (b ++ [_]).getD a.length false
          rw [snoc, len, snoc]
          exact gate
        · rw [List.getD_eq_default, List.getD_eq_default] <;>
            simp only [step, List.length_append, List.length_singleton] <;> omega
    exact run C.gates fan shape a b len hp hq aq bq agree


  have wire_raw (C : Circuit) (xs : List Bool) (i : ℕ) (hi : i < xs.length) :
      (C.wires xs).getD i false = xs.getD i false := by
    obtain ⟨gs,o⟩ := C
    induction gs generalizing xs with
    | nil => rfl
    | cons g gs ih =>
      change ((Circuit.mk gs o).wires (step xs g)).getD i false = _
      rw [ih _ (by simp only [step, List.length_append, List.length_singleton]; omega)]
      exact List.getD_append _ _ _ _ hi

  let F (x : Fin 9 → Bool) : Bool :=
    ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
      (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
  let row (x : Fin 9 → Bool) : List Bool := List.ofFn x ++ [x 0 || x 6]
  let mask (b x w : Bool) : Bool := if b then x || w else x && w

  have row_len (x : Fin 9 → Bool) : (row x).length = 10 := by simp [row]
  have row_raw (x : Fin 9 → Bool) (i : Fin 9) : (row x).getD i.val false = x i := by
    rw [show row x = List.ofFn x ++ [x 0 || x 6] from rfl,
      List.getD_append _ _ _ _ (by simp)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, i.isLt, dite_true, Option.getD_some]

  have set_agrees (a b : List Bool) (len : a.length = b.length) (p v : ℕ)
      (val : Bool) (eq : ∀ i, i ≠ p → a.getD i false = b.getD i false) :
      ∀ i, i ≠ p → (a.set v val).getD i false = (b.set v val).getD i false := by
    intro i hi
    by_cases iv : i = v
    · subst i
      by_cases vl : v < a.length
      · simp only [List.getD_eq_getElem?_getD, List.getElem?_set_self vl,
          List.getElem?_set_self (show v < b.length by omega)]
      · rw [List.set_eq_of_length_le (by omega), List.set_eq_of_length_le (by omega)]
        exact eq v hi
    · simpa only [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm iv)] using eq i hi

  -- These three raw companions hide a change of x6 on the independent set
  -- {0,8,t}. If t is also the masked input, the proof applies for t=8;
  -- t=v=2 and t=v=7 remain open, as do all computed companions.
  have forbidden_raw_companion (v t : Fin 9) (C : Circuit) (w : ℕ) (b : Bool)
      (v6 : v ≠ 6) (fan : FanInTwo C) (w6 : w ≠ 6)
      (ht : t = 2 ∨ t = 7 ∨ t = 8) (exception : t = 8 ∨ t ≠ v)
      (shape : ∀ g ∈ C.gates, reads 6 g = true →
        g.op = .or ∧ (g.inputs = [6,t.val] ∨ g.inputs = [t.val,6]))
      (pivotal : ∀ x y : Fin 9 → Bool,
        (∀ i, i ≠ v → x i = y i) → F x ≠ F y →
        (C.wires (row x)).getD w false = !b) :
      ∃ x : Fin 9 → Bool,
        C.eval ((row x).set v.val (mask b (x v) ((C.wires (row x)).getD w false))) ≠ F x := by
    by_contra! correct
    let a : Fin 9 → Bool := fun i => decide (i = 0 ∨ i = 8 ∨ i = t)
    let z : Fin 9 → Bool := fun i => decide (i = 0 ∨ i = 8 ∨ i = t ∨ i = 6)
    have t6 : t ≠ 6 := by rcases ht with rfl | rfl | rfl <;> decide
    have aval : a t = true := by simp [a]
    have zval : z t = true := by simp [z]
    have graphA : F a = false := by rcases ht with rfl | rfl | rfl <;> decide
    have graphZ : F z = true := by rcases ht with rfl | rfl | rfl <;> decide
    have rows : row a = (row z).set 6 false := by
      rcases ht with rfl | rfl | rfl <;> decide
    have equal : ∀ i, i ≠ 6 → (row a).getD i false = (row z).getD i false := by
      intro i hi
      rw [rows]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hi)]
    have wires := saturated_reader C fan 6 t.val shape (row a) (row z)
      (by rw [row_len, row_len]) (by rw [row_len]; omega)
      (by rw [row_len]; have := t.isLt; omega)
      ((row_raw a t).trans aval) ((row_raw z t).trans zval) equal
    have eqw : (C.wires (row a)).getD w false = (C.wires (row z)).getD w false := wires w w6
    have eqv : a v = z v := by
      have h := equal v.val (fun e => v6 (Fin.ext e))
      simpa only [row_raw] using h
    let value := mask b (a v) ((C.wires (row a)).getD w false)
    have sameValue : mask b (z v) ((C.wires (row z)).getD w false) = value := by
      rw [← eqw, ← eqv]
    let aa := (row a).set v.val value
    let zz := (row z).set v.val value
    have agree : ∀ i, i ≠ 6 → aa.getD i false = zz.getD i false :=
      set_agrees (row a) (row z) (by rw [row_len,row_len]) 6 v.val value equal
    have aqt : aa.getD t.val false = true := by
      by_cases tv : t = v
      · have t8 : t = 8 := exception.resolve_right (by simpa [tv])
        have v8 : v = 8 := tv.symm.trans t8
        subst t
        subst v
        have force : (C.wires (row z)).getD w false = !b := by
          apply pivotal z (Function.update z 8 false)
          · intro i hi; simp [Function.update_of_ne hi]
          · decide
        have val : value = true := by
          change mask b (a 8) ((C.wires (row a)).getD w false) = true
          rw [eqw, force]
          have one : a 8 = true := by decide
          rw [one]
          cases b <;> rfl
        change ((row a).set 8 value).getD 8 false = true
        rw [val]
        simp only [List.getD_eq_getElem?_getD, List.getElem?_set_self (show 8 < (row a).length by rw [row_len]; omega), Option.getD_some]
      · have nv : v.val ≠ t.val := fun e => tv (Fin.ext e.symm)
        change ((row a).set v.val value).getD t.val false = true
        simpa only [List.getD_eq_getElem?_getD, List.getElem?_set_ne nv] using (row_raw a t).trans aval
    have zqt : zz.getD t.val false = true := (agree t.val (fun e => t6 (Fin.ext e))).symm.trans aqt
    have out6 : C.output ≠ 6 := by
      intro hout
      let u : Fin 9 → Bool := fun i => decide (i = 6)
      have h := correct u
      change (C.wires _).getD C.output false = F u at h
      rw [hout, wire_raw] at h
      · have nv : v.val ≠ 6 := fun e => v6 (Fin.ext e)
        have raw : ((row u).set v.val (mask b (u v) ((C.wires (row u)).getD w false))).getD 6 false = true := by
          have base : (row u).getD 6 false = true := by decide
          simpa only [List.getD_eq_getElem?_getD, List.getElem?_set_ne nv] using base
        rw [raw] at h
        have no : F u = false := by decide
        rw [no] at h
        contradiction
      · rw [List.length_set, row_len]; omega
    have final := saturated_reader C fan 6 t.val shape aa zz
      (by simp only [aa,zz,List.length_set,row_len])
      (by simp only [aa,List.length_set,row_len]; omega)
      (by simp only [aa,List.length_set,row_len]; have := t.isLt; omega) aqt zqt agree C.output out6
    have ca : C.eval aa = false := (correct a).trans graphA
    have cz : C.eval zz = true := by simpa only [zz, ← sameValue] using (correct z).trans graphZ
    change C.eval aa = C.eval zz at final
    rw [ca, cz] at final
    contradiction


  have forbidden_unique_raw_reader (v t : Fin 9) (C : Circuit) (w : ℕ) (b : Bool)
      (v6 : v ≠ 6) (fan : FanInTwo C) (w6 : w ≠ 6)
      (ht : t = 2 ∨ t = 7 ∨ t = 8) (exception : t = 8 ∨ t ≠ v)
      (unique : ∃ g : Gate, g.op = .or ∧
        (g.inputs = [6,t.val] ∨ g.inputs = [t.val,6]) ∧ C.gates.filter (reads 6) = [g])
      (pivotal : ∀ x y : Fin 9 → Bool,
        (∀ i, i ≠ v → x i = y i) → F x ≠ F y →
        (C.wires (row x)).getD w false = !b) :
      ∃ x : Fin 9 → Bool,
        C.eval ((row x).set v.val (mask b (x v) ((C.wires (row x)).getD w false))) ≠ F x := by
    obtain ⟨g,op,inputs,unique⟩ := unique
    apply forbidden_raw_companion v t C w b v6 fan w6 ht exception
    · intro h hh hr
      have mem : h ∈ C.gates.filter (reads 6) := List.mem_filter.mpr ⟨hh,hr⟩
      rw [unique] at mem
      have eq : h = g := List.mem_singleton.mp mem
      exact eq ▸ ⟨op,inputs⟩
    · exact pivotal

  dsimp only
  intro v C w b hv0 hv6 fan size lo hi pre dom seed unique nontrivial
  obtain ⟨g,op,⟨t,notIn,inputs⟩,filtered⟩ := unique
  by_cases allowed : t ≠ 8 ∧ (t = 2 ∨ t = 7 → t = v.val)
  · apply remaining v C w b hv0 hv6 fan size lo hi pre dom seed
    · refine ⟨g,op,⟨t,?_,allowed.2,inputs⟩,filtered⟩
      simp only [List.mem_cons, List.mem_singleton] at notIn ⊢
      tauto
    · exact nontrivial
  · have bad : t = 8 ∨ ((t = 2 ∨ t = 7) ∧ t ≠ v.val) := by tauto
    have small : t < 9 := by rcases bad with h | ⟨h|h,_⟩ <;> omega
    let tt : Fin 9 := ⟨t,small⟩
    have ht : tt = 2 ∨ tt = 7 ∨ tt = 8 := by
      rcases bad with h | ⟨h|h,_⟩
      · exact Or.inr (Or.inr (Fin.ext h))
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (Or.inl (Fin.ext h))
    have ex : tt = 8 ∨ tt ≠ v := by
      rcases bad with h | ⟨_,h⟩
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (fun eq => h (congrArg Fin.val eq))
    exact forbidden_unique_raw_reader v tt C w b hv6 fan (by omega) ht ex
      ⟨g,op,inputs,filtered⟩ dom
