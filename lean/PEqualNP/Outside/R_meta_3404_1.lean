import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.NotBracket

set_option maxRecDepth 16000 in
set_option maxHeartbeats 7000000 in
set_option synthInstance.maxSize 512 in
theorem PEqualNP.Outside.R_meta_3404_1
    (unrestricted :
      let f (x : Fin 9 → Bool) : Bool :=
        ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
          (fun k => x (Fin.ofNat 9 (k / 10)) && x (Fin.ofNat 9 (k % 10)))
      ¬ HasCircuitSize 9 f 14)
    (withFour :
      let f (x : Fin 9 → Bool) : Bool :=
        ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
          (fun k => x (Fin.ofNat 9 (k / 10)) && x (Fin.ofNat 9 (k % 10)))
      ∀ (D : Circuit) (k : ℕ), k ∈ ([14,24,34,46] : List ℕ) →
        FanInTwo D → D.size = 13 → 1 ≤ notCount D → notCount D ≤ 2 →
        ¬ (∀ x : Fin 9 → Bool,
          D.eval (List.ofFn x ++ [x 0 || x 4, x (Fin.ofNat 9 (k / 10)) || x (Fin.ofNat 9 (k % 10))]) = f x))
    (withoutFour :
      let f (x : Fin 9 → Bool) : Bool :=
        ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
          (fun k => x (Fin.ofNat 9 (k / 10)) && x (Fin.ofNat 9 (k % 10)))
      ∀ (D : Circuit) (k : ℕ), k ∈ ([1,2,3,6,12,13,15,16,17,18,23,26,27,28,36,67] : List ℕ) →
        FanInTwo D → D.size = 13 → 1 ≤ notCount D → notCount D ≤ 2 →
        ¬ (∀ x : Fin 9 → Bool,
          D.eval (List.ofFn x ++ [x 0 || x 4, x (Fin.ofNat 9 (k / 10)) || x (Fin.ofNat 9 (k % 10))]) = f x)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Finset (Fin (9 : ℕ))), PEqualNP.MetaComplexity.FanInTwo x1 → x2.card ≤ (2 : ℕ) → (1 : ℕ) ≤ PEqualNP.NotBracket.notCount x1 → PEqualNP.NotBracket.notCount x1 ≤ (2 : ℕ) → (∀ (x7 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x7 ++ [x7 (0 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)), Decidable.decide (∃ x8 ∈ x2, x7 x8 = Bool.true)]) = [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x8 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x7 x8.1 && x7 x8.2) → (14 : ℕ) ≤ x1.size := by
  intro D A fan ac nlo nhi computes
  by_contra! small
  let graph (x : Fin 9 → Bool) : Bool :=
    ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
      (fun k => x (Fin.ofNat 9 (k / 10)) && x (Fin.ofNat 9 (k % 10)))
  let base (x : Fin 9 → Bool) := List.ofFn x ++ [x 0 || x 4]
  let step := fun (w : List Bool) (g : Gate) =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have graphEq : (fun x : Fin 9 → Bool =>
      ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] :
        List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)) = graph := by decide +kernel
  have good (x : Fin 9 → Bool) :
      D.eval (base x ++ [decide (∃ i ∈ A, x i = true)]) = graph x := by
    change D.eval ((List.ofFn x ++ [x 0 || x 4]) ++ [_]) = _
    rw [List.append_assoc,List.singleton_append]
    exact (computes x).trans (congrFun graphEq x)
  have raw (x : Fin 9 → Bool) (i : Fin 9) : (List.ofFn x).getD i.val false = x i := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    simp only [i.isLt, dite_true, Option.getD_some]
  let transform (m : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op,g.inputs.map m⟩
  have moveFan (m : ℕ → ℕ) :
      FanInTwo (⟨D.gates.map (transform m),m D.output⟩ : Circuit) := by
    intro g hg
    obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hg
    have f := fan h hh
    exact ⟨f.1, by simpa [transform] using f.2⟩
  have moveSize (m : ℕ → ℕ) :
      (⟨D.gates.map (transform m),m D.output⟩ : Circuit).size = D.size := List.length_map _
  have moveNot (m : ℕ → ℕ) :
      notCount (⟨D.gates.map (transform m),m D.output⟩ : Circuit) = notCount D := by
    change ((D.gates.map (transform m)).filter (fun (g : Gate) => @decide _ (lineDegreeGateOpDecEq g.op GateOp.not))).length =
      (D.gates.filter (fun (g : Gate) => @decide _ (lineDegreeGateOpDecEq g.op GateOp.not))).length
    rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter, List.countP_map]
    rfl
  have stable (w : List Bool) (b : Bool) (i : ℕ) (hne : i ≠ w.length) :
      (w ++ [b]).getD i false = w.getD i false := by
    by_cases within : i < w.length
    · exact List.getD_append _ _ _ _ within
    · rw [List.getD_eq_default _ _ (by simp; omega),
          List.getD_eq_default _ _ (by omega)]
  have simulate (m : ℕ → ℕ) (gs : List Gate) (w v : List Bool)
      (link : ∀ i, w.getD i false = v.getD (m i) false)
      (slot : ∀ i t, t < gs.length → (m i = v.length + t ↔ i = w.length + t)) :
      ∀ i, (gs.foldl step w).getD i false =
        ((gs.map (transform m)).foldl step v).getD (m i) false := by
    induction gs generalizing w v with
    | nil => exact link
    | cons g gs ih =>
      have inEq : (g.inputs.map fun i => w.getD i false) =
          (g.inputs.map m).map (fun j => v.getD j false) := by
        rw [List.map_map]
        exact List.map_congr_left (fun i _ => link i)
      have values :
          g.op.eval (g.inputs.map fun i => w.getD i false) =
          (transform m g).op.eval ((transform m g).inputs.map fun i => v.getD i false) :=
        congrArg g.op.eval inEq
      rw [List.map_cons, List.foldl_cons, List.foldl_cons]
      apply ih
      · intro i
        let b := g.op.eval (g.inputs.map fun j => w.getD j false)
        change (w ++ [b]).getD i false =
          (v ++ [(transform m g).op.eval ((transform m g).inputs.map fun j => v.getD j false)]).getD (m i) false
        rw [← values]
        by_cases same : i = w.length
        · have h : m i = v.length := by simpa using (slot i 0 (by simp)).2 (by simpa using same)
          rw [h, same]; simp [b]
        · have diff : m i ≠ v.length := fun hh => same (by simpa using (slot i 0 (by simp)).1 (by simpa using hh))
          rw [stable _ _ _ same, stable _ _ _ diff, link]
      · intro i t ht
        simpa [step, Nat.add_assoc, Nat.add_comm 1 t] using slot i (t + 1) (by simp; omega)
  let first : Gate := ⟨GateOp.or,[0,4]⟩
  have init (x : Fin 9 → Bool) : step (List.ofFn x) first = base x := by
    change List.ofFn x ++ [(List.ofFn x).getD 0 false ||
      ((List.ofFn x).getD 4 false || false)] = List.ofFn x ++ [x 0 || x 4]
    rw [show (List.ofFn x).getD 0 false = x 0 from raw x 0,
      show (List.ofFn x).getD 4 false = x 4 from raw x 4, Bool.or_false]
  have firstGood : first.op ∈ ({GateOp.and, GateOp.or,GateOp.not} : Set GateOp) ∧
      first.inputs.length ≤ 2 := by simp [first]
  have smallAlias (p : ℕ) (pvalid : p < 10 ∨ p = 23)
      (valueAt : ∀ x, decide (∃ i ∈ A, x i = true) = (base x).getD p false) : False := by
    let m (i : ℕ) := if i < 10 then i else if i = 10 then p else i - 1
    let K : Circuit := ⟨first :: D.gates.map (transform m),m D.output⟩
    apply unrestricted
    refine ⟨K, ?_, ?_, ?_⟩
    · intro g hg
      change g ∈ first :: D.gates.map (transform m) at hg
      rcases List.mem_cons.mp hg with eq | hg
      · exact eq.symm ▸ firstGood
      · exact moveFan m g hg
    · change (first :: D.gates.map (transform m)).length ≤ 14
      simp only [List.length_cons, List.length_map]
      change D.gates.length < 14 at small
      omega
    · intro x
      let b := decide (∃ i ∈ A, x i = true)
      have len : (base x).length = 10 := by simp [base]
      have link (i : ℕ) : (base x ++ [b]).getD i false = (base x).getD (m i) false := by
        by_cases i0 : i < 10
        · rw [List.getD_append _ _ _ _ (by omega)]
          simp [m,i0]
        · by_cases i1 : i = 10
          · subst i
            simpa [len,m,b] using valueAt x
          · have left := List.getD_eq_default (base x ++ [b]) false (n := i) (by simp [len]; omega)
            have right := List.getD_eq_default (base x) false (n := m i) (by simp [m,i0,i1,len]; omega)
            exact left.trans right.symm
      have slot (i t : ℕ) (ht : t < D.gates.length) :
          m i = (base x).length + t ↔ i = (base x ++ [b]).length + t := by
        rw [len]
        simp only [List.length_append, List.length_singleton, len]
        change D.gates.length < 14 at small
        unfold m
        split <;> (try split) <;> omega
      have e := simulate m D.gates (base x ++ [b]) (base x) link slot D.output
      change ((D.gates.map (transform m)).foldl step (step (List.ofFn x) first)).getD (m D.output) false = graph x
      rw [init, ← e]
      exact good x
  have pairValue (x : Fin 9 → Bool) (a b : Fin 9) :
      decide (∃ i ∈ ({a,b} : Finset (Fin 9)), x i = true) = (x a || x b) := by
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq, Bool.or_eq_true, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨i, rfl | rfl, h⟩
      · exact Or.inl h
      · exact Or.inr h
    · rintro (h | h)
      · exact ⟨a, Or.inl rfl, h⟩
      · exact ⟨b, Or.inr rfl, h⟩
  have exactSize (a b : Fin 9) (hA : A = {a,b}) : D.size = 13 := by
    by_contra wrong
    have tiny : D.gates.length ≤ 12 := by
      change D.gates.length < 14 at small
      change D.gates.length ≠ 13 at wrong
      omega
    let second : Gate := ⟨GateOp.or,[a.val,b.val]⟩
    let K : Circuit := ⟨first :: second :: D.gates,D.output⟩
    apply unrestricted
    refine ⟨K, ?_, ?_, ?_⟩
    · intro g hg
      change g ∈ first :: second :: D.gates at hg
      rcases List.mem_cons.mp hg with eq | hg
      · exact eq.symm ▸ firstGood
      rcases List.mem_cons.mp hg with eq | hg
      · subst g
        simp [second]
      · exact fan g hg
    · change (first :: second :: D.gates).length ≤ 14
      simp only [List.length_cons]
      omega
    · intro x
      have wire (u : Fin 9) : (base x).getD u.val false = x u := by
        rw [show base x = List.ofFn x ++ [x 0 || x 4] from rfl, List.getD_append _ _ _ _ (List.length_ofFn.symm ▸ u.isLt)]
        exact raw x u
      have e : step (base x) second = base x ++ [x a || x b] := by
        change base x ++ [(base x).getD a.val false || ((base x).getD b.val false || false)] = _
        rw [wire a,wire b,Bool.or_false]
      have h := good x
      rw [hA, pairValue] at h
      change (D.gates.foldl step (step (step (List.ofFn x) first) second)).getD D.output false = graph x
      rw [init,e]
      exact h
  by_cases zero : A.card = 0
  · have empty := Finset.card_eq_zero.mp zero
    apply smallAlias 23 (Or.inr rfl)
    intro x
    have len : (base x).length = 10 := by simp [base]
    rw [List.getD_eq_default _ _ (by rw [len]; decide), empty]
    simp
  by_cases one : A.card = 1
  · obtain ⟨a, equal⟩ := Finset.card_eq_one.mp one
    apply smallAlias a.val (Or.inl (by omega))
    intro x
    rw [show base x = List.ofFn x ++ [x 0 || x 4] from rfl, List.getD_append _ _ _ _ (List.length_ofFn.symm ▸ a.isLt)]
    rw [raw x a, equal]
    simp
  obtain ⟨a,b,distinct,hA⟩ := Finset.card_eq_two.mp (show A.card = 2 by omega)
  by_cases duplicate : A = {0,4}
  · apply smallAlias 9 (Or.inl (by decide))
    intro x
    rw [duplicate,pairValue]
    change (x 0 || x 4) = (List.ofFn x ++ [x 0 || x 4]).getD 9 false
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [List.length_ofFn]), List.length_ofFn]
    rfl
  have size := exactSize a b hA
  let r (i : Fin 9) : Fin 9 := ([0,5,8,3,4,1,7,6,2] : List (Fin 9)).getD i.val 0
  let near := ([14,24,34,46] : List ℕ)
  let far := ([1,2,3,6,12,13,15,16,17,18,23,26,27,28,36,67] : List ℕ)
  let lo (k : ℕ) := Fin.ofNat 9 (k / 10)
  let hi (k : ℕ) := Fin.ofNat 9 (k % 10)
  let code (u v : Fin 9) := min u.val v.val * 10 + max u.val v.val
  let enumerated (u v : Fin 9) := code u v ∈ near ++ far ∧
    ({u,v} : Finset (Fin 9)) = {lo (code u v),hi (code u v)}
  have reps : ∀ a b : Fin 9, a ≠ b → ({a,b} : Finset (Fin 9)) ≠ {0,4} →
      enumerated a b ∨ enumerated (r a) (r b) := by decide +kernel
  have symmetric : ∀ x : Fin 9 → Bool, graph (x ∘ r) = graph x := by decide +kernel
  have solve (B : Circuit) (j : ℕ) (hj : j ∈ near ++ far)
      (fb : FanInTwo B) (bs : B.size = 13)
      (n1 : 1 ≤ notCount B) (n2 : notCount B ≤ 2)
      (eval : ∀ x : Fin 9 → Bool, B.eval (List.ofFn x ++ [x 0 || x 4, x (lo j) || x (hi j)]) = graph x) : False := by
    rcases List.mem_append.mp hj with h | h
    · exact withFour B j h fb bs n1 n2 eval
    · exact withoutFour B j h fb bs n1 n2 eval
  have evalPair (x : Fin 9 → Bool) : D.eval (List.ofFn x ++ [x 0 || x 4, x a || x b]) = graph x := by
    have h := good x
    rw [hA,pairValue] at h
    simpa only [base,List.append_assoc,List.singleton_append] using h
  have conv (x : Fin 9 → Bool) (u v : Fin 9) (j : ℕ)
      (uv : ({u,v} : Finset (Fin 9)) = {lo j,hi j}) :
      (x u || x v) = (x (lo j) || x (hi j)) := by
    rw [← pairValue, ← pairValue, uv]
  rcases reps a b distinct (hA ▸ duplicate) with ⟨hk,equal⟩ | ⟨hk,equal⟩
  · apply solve D (code a b) hk fan size nlo nhi
    intro x
    rw [← conv x a b (code a b) equal]
    exact evalPair x
  · let k := code (r a) (r b)
    let m (i : ℕ) := if h : i < 9 then (r ⟨i,h⟩).val else i
    let B : Circuit := ⟨D.gates.map (transform m),m D.output⟩
    apply solve B k hk (moveFan m) ((moveSize m).trans size)
      (by simpa only [B, moveNot] using nlo) (by simpa only [B, moveNot] using nhi)
    intro x
    let bits := [x 0 || x 4, x (r a) || x (r b)]
    let old := List.ofFn (x ∘ r) ++ bits
    let new := List.ofFn x ++ bits
    have link (i : ℕ) : old.getD i false = new.getD (m i) false := by
      by_cases smallI : i < 9
      · have smallM : m i < 9 := by simp [m,smallI]
        rw [show old = List.ofFn (x ∘ r) ++ bits from rfl, show new = List.ofFn x ++ bits from rfl,
            List.getD_append _ _ _ _ (List.length_ofFn.symm ▸ smallI),
            List.getD_append _ _ _ _ (List.length_ofFn.symm ▸ smallM)]
        rw [raw (x ∘ r) ⟨i,smallI⟩, show m i = (r ⟨i,smallI⟩).val from dite_eq_left smallI,
          raw x (r ⟨i,smallI⟩)]
        rfl
      · simp only [old,new,m,dite_eq_right smallI,List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by simpa using Nat.le_of_not_gt smallI),
            List.getElem?_append_right (by simpa using Nat.le_of_not_gt smallI)]
        simp
    have slot (i t : ℕ) (_ : t < D.gates.length) :
        m i = new.length + t ↔ i = old.length + t := by
      have L : old.length = 11 := by simp [old,bits]
      have R : new.length = 11 := by simp [new,bits]
      rw [L,R]
      by_cases smallI : i < 9
      · simp only [m, dite_eq_left smallI]
        have bound := (r ⟨i,smallI⟩).isLt
        constructor <;> intro h <;> omega
      · simp [m, smallI]
    have e := simulate m D.gates old new link slot D.output
    change D.eval old = B.eval new at e
    have oldGood : D.eval old = graph x := (evalPair (x ∘ r)).trans (symmetric x)
    rw [← conv x (r a) (r b) k equal]
    exact e.symm.trans oldGood
