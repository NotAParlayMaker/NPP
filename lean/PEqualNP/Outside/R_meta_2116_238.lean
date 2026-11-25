import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_2116_238
    (simulate : ∀ (n : ℕ) (a : Fin n) (P Q : List Gate) (g : Gate) (w o : ℕ),
      (∀ h ∈ P ++ Q, a.val ∉ h.inputs) → a.val ≠ o → a.val ≠ w →
      g.op = .or → (g.inputs = [a.val,w] ∨ g.inputs = [w,a.val]) →
      ∀ (x : Fin n → Bool) (v : Bool), x a = false →
        let z := (Circuit.mk P 0).wires (List.ofFn x)
        (Circuit.mk (P ++ g :: Q) o).eval (List.ofFn (Function.update x a v)) =
          (Circuit.mk Q o).eval (z ++ [v || z.getD w false]))
    (residual : ∀ (P Q : List Gate) (w o : ℕ), P.length + Q.length ≤ 14 →
      FanInTwo ⟨P ++ Q, o⟩ → Q ≠ [] → 9 ≤ w → w < 9 + P.length →
      (∀ g ∈ P ++ Q, 4 ∉ g.inputs) →
      (∀ g ∈ P ++ Q, 6 ∈ g.inputs ∨ 7 ∈ g.inputs → g.op = .or) →
      (∀ x : Fin 9 → Bool, x 4 = false →
        let z := (Circuit.mk P 0).wires (List.ofFn x)
        let out := fun t : Bool => (Circuit.mk Q o).eval (z ++ [t])
        let e := x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 0 && x 5 ||
          x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5
        out (z.getD w false) = e ∧ out true = (e || x 0 || x 3)) → False) :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)); have x2 : (x2 : PEqualNP.CircuitLowerBounds.Circuit) → Fin (9 : ℕ) → Finset (Fin x2.size) := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Fin (9 : ℕ)) => {x4 : Fin x2.size | ↑x3 ∈ (x2.gates.get x4).inputs}; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) =>   PEqualNP.MetaComplexity.IsMinimalCircuit (9 : ℕ) x3 ∧     x3.size ≤ (15 : ℕ) ∧       PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x3 = x1 ∧         (∀ (x4 : Fin x3.size),             have x5 : PEqualNP.CircuitLowerBounds.Gate := x3.gates.get x4;             (∀ x6 ∈ x5.inputs, x6 < (9 : ℕ) + ↑x4) ∧ x5.inputs.Nodup ∧ (x5.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ x5.inputs.length = (1 : ℕ) ∨ x5.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ x5.inputs.length = (2 : ℕ))) ∧           ∀ x4 ∈ [(4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))], (x2 x3 x4).Nonempty ∧ (x2 x3 x4).card ≤ (2 : ℕ) ∧ ((x2 x3 x4).card = (2 : ℕ) → ∀ x7 ∈ x2 x3 x4, (x3.gates.get x7).op = PEqualNP.CircuitLowerBounds.GateOp.or); ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), x3 x4 → (∀ x6 ∈ [(4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))], (x2 x4 x6).card = (1 : ℕ) ∧ ∀ x8 ∈ x2 x4 x6, (x4.gates.get x8).op = PEqualNP.CircuitLowerBounds.GateOp.or) → False := by
  classical
  dsimp only
  intro C model unique
  obtain ⟨minimal,budget,computes,shape,_⟩ := model
  obtain ⟨one, ops⟩ := unique 4 (by simp)
  let readers : Finset (Fin C.size) := Finset.univ.filter fun i => 4 ∈ (C.gates.get i).inputs
  change readers.card = 1 at one
  obtain ⟨i, eq⟩ := Finset.card_eq_one.mp one
  have hit (k : Fin C.size) : 4 ∈ (C.gates.get k).inputs ↔ k = i := by
    have e : k ∈ readers ↔ k = i := by rw [eq, Finset.mem_singleton]
    simpa [readers] using e
  have atI : 4 ∈ (C.gates.get i).inputs := (hit i).mpr rfl
  have isOR : (C.gates.get i).op = .or := ops i (by
    change i ∈ readers
    rw [eq]
    exact Finset.mem_singleton_self i)
  have pins2 : (C.gates.get i).inputs.length = 2 := by
    rcases (shape i).2.2 with hn | ha
    · rw [isOR] at hn
      cases hn.1
    · exact ha.2
  have only (k : Fin C.size) (hne : k ≠ i) : 4 ∉ (C.gates.get k).inputs :=
    fun h => hne ((hit k).mp h)
  obtain ⟨a,b,pins⟩ := List.length_eq_two.mp pins2
  have ab : a ≠ b := by simpa [pins] using (shape i).2.1
  have own : 4 = a ∨ 4 = b := by simpa [pins] using atI
  obtain ⟨w,pins',wd,wb⟩ : ∃ w : ℕ,
      ((C.gates.get i).inputs = [4,w] ∨ (C.gates.get i).inputs = [w,4]) ∧
      4 ≠ w ∧ w < 9+i.val := by
    rcases own with rfl | rfl
    · exact ⟨b, Or.inl pins, ab, (shape i).1 b (by simp [pins])⟩
    · exact ⟨a, Or.inr pins, Ne.symm ab, (shape i).1 a (by simp [pins])⟩
  let P := C.gates.take i.val
  let Q := C.gates.drop (i.val+1)
  have split : P ++ C.gates.get i :: Q = C.gates := by
    change C.gates.take i.val ++ C.gates[i.val] :: C.gates.drop (i.val+1) = _
    simp
  have hi : i.val < C.gates.length := i.isLt
  have plen : P.length = i.val := by simp [P, Nat.le_of_lt hi]
  have whereis {g : Gate} (h : g ∈ P ++ Q) :
      ∃ k : Fin C.size, k ≠ i ∧ C.gates.get k = g := by
    rcases List.mem_append.mp h with l | r
    · obtain ⟨j,hj,eqj⟩ := List.getElem_of_mem l
      have lt : j < i.val := by simpa [plen] using hj
      refine ⟨⟨j,lt_trans lt i.isLt⟩, fun e => (ne_of_lt lt) (congrArg Fin.val e), ?_⟩
      change C.gates[j] = g
      simpa [P] using eqj
    · obtain ⟨j,hj,eqj⟩ := List.getElem_of_mem r
      have len : i.val + 1 + j < C.size := by
        have hj' : j < C.gates.length - (i.val+1) := by simpa [Q] using hj
        change _ < C.gates.length
        have hi : i.val < C.gates.length := i.isLt
        omega
      refine ⟨⟨i.val+1+j,len⟩, fun e => ?_, ?_⟩
      · have := congrArg Fin.val e
        change i.val+1+j = i.val at this
        omega
      · change C.gates[i.val+1+j] = g
        have eqj' := eqj
        dsimp only [Q] at eqj'
        rw [List.getElem_drop] at eqj'
        convert eqj' using 1
  have absent : ∀ g ∈ P ++ Q, 4 ∉ g.inputs := by
    intro g h
    obtain ⟨k,ne,rfl⟩ := whereis h
    exact only k ne
  have outdiff : 4 ≠ C.output := by
    intro eqout
    let x : Fin 9 → Bool := fun j => decide (j = 4)
    have e := congrFun computes x
    have pre : (Circuit.mk C.gates C.output).eval (List.ofFn x) = true := by
      change (C.gates.foldl (fun ws g => ws ++ [g.op.eval (g.inputs.map fun k => ws.getD k false)])
        (List.ofFn x)).getD C.output false = true
      rw [← eqout]
      generalize hg : C.gates = gs
      have keep (l : List Gate) (ws : List Bool) (h : 4 < ws.length) :
          (l.foldl (fun z g => z ++ [g.op.eval (g.inputs.map fun k => z.getD k false)]) ws).getD 4 false =
            ws.getD 4 false := by
        induction l generalizing ws with
        | nil => rfl
        | cons g l ih =>
          rw [List.foldl_cons, ih _ (by simp; omega)]
          simp [List.getD_eq_getElem?_getD,List.getElem?_append_left h]
      rw [keep _ _ (by simp)]
      decide
    change (Circuit.mk C.gates C.output).eval (List.ofFn x) = _ at e
    rw [pre] at e
    exact Bool.noConfusion (show true = false from e)
  have lens := congrArg List.length split
  have b : P.length + Q.length ≤ 14 := by
    change C.gates.length ≤ 15 at budget
    simp only [List.length_append,List.length_cons] at lens
    omega
  let E (x : Fin 9 → Bool) := x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 0 && x 5 ||
    x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5
  let z (x : Fin 9 → Bool) := (Circuit.mk P 0).wires (List.ofFn x)
  let out (x : Fin 9 → Bool) (t : Bool) := (Circuit.mk Q C.output).eval (z x ++ [t])
  have pair (x : Fin 9 → Bool) (hx : x 4 = false) :
      out x ((z x).getD w false) = E x ∧ out x true = (E x || x 0 || x 3) := by
    dsimp only [out,z,E]
    have result (v : Bool) := simulate 9 4 P Q (C.gates.get i) w C.output absent outdiff wd isOR pins' x v hx
    have val (v : Bool) := congrFun computes (Function.update x 4 v)
    have r0 := (result false).symm
    have r1 := (result true).symm
    rw [split] at r0 r1
    constructor
    · simpa [Function.update, Bool.or_assoc] using r0.trans (val false)
    · have e := r1.trans (val true)
      simp [Function.update] at e
      convert e using 1
      · simp
      · ac_rfl
  have keepsInputs (x : Fin 9 → Bool) : List.ofFn x <+: z x := by
    have lemmaP (gs : List Gate) (init : List Bool) : init <+: (Circuit.mk gs 0).wires init := by
      induction gs generalizing init with
      | nil => exact List.prefix_refl _
      | cons g gs ih => exact (List.prefix_append init [_]).trans (ih _)
    exact lemmaP P _
  have raw (x : Fin 9 → Bool) (j : Fin 9) : (z x).getD j.val false = x j := by
    obtain ⟨t,h⟩ := keepsInputs x
    rw [← h]
    have lt : j.val < (List.ofFn x).length := by simp
    simp only [List.getD_eq_getElem?_getD,List.getElem?_append_left lt,List.getElem?_eq_getElem lt,Option.getD_some,List.getElem_ofFn]
  have derived : 9 ≤ w := by
    by_contra! small
    let j : Fin 9 := ⟨w,small⟩
    let probe (a : Fin 9) (k : Fin 9) :=
      decide (k = a ∨ k = (if a = 1 ∨ a = 5 then 3 else 0))
    have test : ∀ a : Fin 9, a ≠ 4 → probe a 4 = false ∧ probe a a = true ∧
        E (probe a) = false ∧ (probe a 0 || probe a 3) = true := by decide
    obtain ⟨h0,h1,he,ht⟩ := test j (fun h => wd (congrArg Fin.val h).symm)
    obtain ⟨low,high⟩ := pair (probe j) h0
    have hwire : (z (probe j)).getD w false = true := (raw (probe j) j).trans h1
    rw [hwire,he] at low
    rw [he,Bool.false_or,ht] at high
    exact Bool.noConfusion (low.symm.trans high)
  have nonempty : Q ≠ [] := by
    intro empty
    let u (j : Fin 9) := decide (j = 0)
    let v (_ : Fin 9) := false
    have sizez (x : Fin 9 → Bool) : (z x).length = 9 + P.length := by
      have len (gs : List Gate) (b : List Bool) : ((Circuit.mk gs 0).wires b).length = b.length + gs.length := by
        induction gs generalizing b with
        | nil => rfl
        | cons g gs ih =>
          change ((Circuit.mk gs 0).wires (b ++ [_])).length = _
          rw [ih]
          simp
          omega
      simpa [z] using len P (List.ofFn x)
    have output (x : Fin 9 → Bool) (t : Bool) : out x t = (z x ++ [t]).getD C.output false := by
      dsimp only [out]
      rw [empty]
      rfl
    have forced : C.output = 9 + P.length := by
      by_contra ne
      have same (t : Bool) : out u t = (z u).getD C.output false := by
        rw [output]
        by_cases l : C.output < (z u).length
        · simp [List.getD_eq_getElem?_getD,List.getElem?_append_left l]
        · have r : (z u).length < C.output := by rw [sizez] at l ⊢; omega
          have s : (z u ++ [t]).length ≤ C.output := by simp; omega
          rw [List.getD_eq_default _ _ s,List.getD_eq_default _ _ r.le]
      obtain ⟨l,h⟩ := pair u (by decide)
      rw [same] at l h
      exact Bool.noConfusion (show false = true from l.symm.trans h)
    have last := (pair v (by rfl)).2
    rw [output,forced,← sizez v] at last
    simp [E,v] at last
  apply residual P Q w C.output b _ nonempty derived (by simpa [plen] using wb) absent
  · intro g hg h
    obtain ⟨k,_,rfl⟩ := whereis hg
    have marked (v : Fin 9) (hv : v ∈ ([4,6,7] : List (Fin 9))) (reads : v.val ∈ (C.gates.get k).inputs) :
        (C.gates.get k).op = .or := (unique v hv).2 k (Finset.mem_filter.mpr ⟨Finset.mem_univ _,reads⟩)
    rcases h with h | h
    · exact marked 6 (by simp) h
    · exact marked 7 (by simp) h
  · exact pair
  · intro g hg
    obtain ⟨k,_,rfl⟩ := whereis hg
    exact minimal.1 _ (List.get_mem _ _)
