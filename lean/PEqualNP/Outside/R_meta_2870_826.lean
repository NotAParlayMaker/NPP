import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover PEqualNP.GenericRejection PEqualNP.EdgeOwnership

-- Complementary point inputs and their conversion to circuit coordinates follow R_meta_2475_271.
theorem PEqualNP.Outside.R_meta_2870_826
    (row : ∀ (n : ℕ) (S : Fin n → Finset (Fin n)) (C : Circuit), IsAO2 (n+n) C →
      0 < C.size → RightOnIncidentPairs S C →
      (∀ l, C.eval (incidenceInput (S l)ᶜ {l}) = false) →
      ∀ l, (S l).card ≤ 1 + Nat.card {j : Fin C.size //
        let V := fun (X Y : Finset (Fin n)) => wireValue C (incidenceInput X Y) (n+n+j.val)
        (gateAt C j.val).op = GateOp.or ∧ V (S l)ᶜ {l} = false ∧
        ∃ a b, (gateAt C j.val).inputs = [a,b] ∧ ∃ p ∈ S l, ∃ r ∈ S l,
        let A := fun (w : ℕ) (u : Fin n) => wireValue C (incidenceInput {u} {l}) w
        A a p = true ∧ A b p = false ∧ A a r = false ∧ A b r = true})
    (crowded : ∀ (q n : ℕ) (S : Fin n → Finset (Fin n)) (C : Circuit),
      100 < q → n = q^2+q+1 → (∀ l, (S l).card = q+1) →
      (∀ p r, p ≠ r → ∃! l, p ∈ S l ∧ r ∈ S l) →
      IsAO2 (n+n) C → RightOnIncidentPairs S C →
      (∀ X Y, Y.card ≤ q → IsFalseInput S X Y → C.eval (incidenceInput X Y) = false) →
      ∀ j < C.size, (gateAt C j).op = GateOp.or →
      let V := fun (X Y : Finset (Fin n)) => wireValue C (incidenceInput X Y) (n+n+j)
      ∀ L : Finset (Fin n), 100 < L.card →
      (∀ l ∈ L, V (S l)ᶜ {l} = false ∧
        ∃ a b, (gateAt C j).inputs = [a,b] ∧ ∃ p ∈ S l, ∃ r ∈ S l,
        let A := fun (w : ℕ) (u : Fin n) => wireValue C (incidenceInput {u} {l}) w
        A a p = true ∧ A b p = false ∧ A a r = false ∧ A b r = true) →
      (∀ p r : Fin n, V {p} ∅ = true → V {r} ∅ = true → p = r) →
      n*q ≤ 100*C.size) :
have x1 : ℕ → PEqualNP.CircuitLowerBounds.Circuit → PEqualNP.CircuitLowerBounds.Gate → Prop := fun (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : PEqualNP.CircuitLowerBounds.Gate) => x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((∀ x4 ∈ x3.inputs, ∃ (x6 : Fin x1 → Bool), (x2.wires (List.ofFn x6 ++ List.replicate x1 Bool.false)).getD x4 Bool.false ≠ (x2.wires (List.ofFn x6 ++ List.replicate x1 Bool.true)).getD x4 Bool.false) ∨ ∀ x4 ∈ x3.inputs, ∃ (x6 : Fin x1 → Bool), (x2.wires (List.replicate x1 Bool.false ++ List.ofFn x6)).getD x4 Bool.false ≠ (x2.wires (List.replicate x1 Bool.true ++ List.ofFn x6)).getD x4 Bool.false); ∀ (x2 x3 : ℕ) (x4 : Fin x3 → Fin x3 → Prop) [x5 : DecidableRel x4] (x6 : PEqualNP.CircuitLowerBounds.Circuit), (100 : ℕ) < x2 → x3 = x2 ^ (2 : ℕ) + x2 + (1 : ℕ) → (∀ (x9 : Fin x3), Fintype.card { x10 : Fin x3 // x4 x10 x9 } = x2 + (1 : ℕ)) → (∀ (x10 x11 : Fin x3), x10 ≠ x11 → ∃! x13 : Fin x3, x4 x10 x13 ∧ x4 x11 x13) → PEqualNP.MetaComplexity.Monotone2 x6 → x6.output < x3 + x3 + x6.size → (∀ (x13 : ℕ) (x14 : PEqualNP.CircuitLowerBounds.Gate), x6.gates[x13]? = Option.some x14 → ∃ (x16 : ℕ) (x17 : ℕ), x14.inputs = [x16, x17] ∧ x16 < x17 ∧ x17 < x3 + x3 + x13) → (∀ (x14 x15 : Fin x3), x4 x14 x15 → (PEqualNP.MetaComplexity.circuitFun (x3 + x3) x6 fun (x17 : Fin (x3 + x3)) => Decidable.decide (x17 = Fin.castAdd x3 x14 ∨ x17 = Fin.natAdd x3 x15)) = Bool.true) → (∀ (x15 : Fin (x3 + x3) → Bool), Fintype.card { x16 : Fin x3 // x15 (Fin.natAdd x3 x16) = Bool.true } ≤ x2 → (¬∃ (x17 : Fin x3) (x18 : Fin x3), x4 x17 x18 ∧ x15 (Fin.castAdd x3 x17) = Bool.true ∧ x15 (Fin.natAdd x3 x18) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x3 + x3) x6 x15 = Bool.false) → ∀ x16 ⊆ Finset.range x6.size, (1 : ℕ) ≤ x16.card → (∀ (x19 : ℕ) (x20 : PEqualNP.CircuitLowerBounds.Gate), x6.gates[x19]? = Option.some x20 → (x19 ∈ x16 ↔ x1 x3 x6 x20)) → (100 : ℕ) * x16.card < x3 * x2 → x3 * x2 ≤ (100 : ℕ) * x6.size := by
  classical
  dsimp only
  intro q n R dec C qLarge geom lines connects basis output order accept reject U urange nonempty exactU few
  let S (l : Fin n) := Finset.univ.filter fun p : Fin n => R p l
  have incident (p l : Fin n) : p ∈ S l ↔ R p l := by simp [S]
  have lineSize (l : Fin n) : (S l).card = q+1 := by
    rw [← Fintype.card_coe]
    exact (Fintype.card_congr (Equiv.subtypeEquivRight (fun p => incident p l))).trans (lines l)
  have through (p p' : Fin n) (unequal : p ≠ p') :
      ∃! l : Fin n, p ∈ S l ∧ p' ∈ S l := by
    simpa only [incident] using connects p p' unequal
  have gateSome (j : ℕ) (hj : j < C.gates.length) :
      C.gates[j]? = some (gateAt C j) := by
    have eq : gateAt C j = C.gates[j] := List.getD_eq_getElem _ _ hj
    rw [eq]
    exact List.getElem?_eq_getElem hj
  have model : IsAO2 (n+n) C := by
    refine ⟨?_, ?_, ?_⟩
    · intro g hg
      simpa using (basis g hg).1
    · intro j hj i hi
      obtain ⟨a,b,ab,lt,back⟩ := order j _ (gateSome j hj)
      rw [ab, List.mem_cons, List.mem_singleton] at hi
      rcases hi with rfl | rfl <;> omega
    · intro g hg
      obtain ⟨j,hj,eq⟩ := List.mem_iff_getElem.mp hg
      have get : C.gates[j]? = some g := by
        rw [List.getElem?_eq_getElem hj, eq]
      obtain ⟨a,b,ab,_,_⟩ := order j g get
      simp [ab]
  let vector (X Y : Finset (Fin n)) : Fin (n+n) → Bool :=
    Fin.addCases (fun p => decide (p ∈ X)) (fun l => decide (l ∈ Y))
  have listForm (X Y : Finset (Fin n)) : List.ofFn (vector X Y) = incidenceInput X Y :=
    List.ofFn_fin_append _ _
  have vp (X Y : Finset (Fin n)) (p : Fin n) : vector X Y (Fin.castAdd n p) = decide (p ∈ X) :=
    Fin.addCases_left ..
  have vl (X Y : Finset (Fin n)) (l : Fin n) : vector X Y (Fin.natAdd n l) = decide (l ∈ Y) :=
    Fin.addCases_right ..
  have diff (p l : Fin n) : Fin.castAdd n p ≠ Fin.natAdd n l := by
    intro equal
    have values := congrArg Fin.val equal
    simp only [Fin.val_castAdd, Fin.val_natAdd] at values
    have lt := p.isLt
    omega
  have pair (p l : Fin n) :
      vector {p} {l} = fun i => decide (i = Fin.castAdd n p ∨ i = Fin.natAdd n l) := by
    funext i
    refine Fin.addCases (motive := fun i => vector {p} {l} i =
      decide (i = Fin.castAdd n p ∨ i = Fin.natAdd n l)) ?_ ?_ i
    · intro a
      rw [vp]
      simp only [Finset.mem_singleton, Fin.castAdd_inj, diff a l, or_false]
    · intro b
      rw [vl]
      simp only [Finset.mem_singleton, Fin.natAdd_inj, Ne.symm (diff p b), false_or]
  have correct : RightOnIncidentPairs S C := by
    intro l p hp
    rw [← listForm, pair]
    exact accept p l ((incident p l).mp hp)
  have sound (X Y : Finset (Fin n)) (budget : Y.card ≤ q) (empty : IsFalseInput S X Y) :
      C.eval (incidenceInput X Y) = false := by
    have count : Fintype.card {l : Fin n // vector X Y (Fin.natAdd n l) = true} = Y.card := by
      rw [← Fintype.card_coe]
      apply Fintype.card_congr
      refine Equiv.subtypeEquivRight (fun l => ?_)
      simp only [vl, decide_eq_true_eq]
    have outside : ¬ ∃ (p l : Fin n), R p l ∧ vector X Y (Fin.castAdd n p) = true ∧
        vector X Y (Fin.natAdd n l) = true := by
      rintro ⟨p,l,h,px,ly⟩
      have pX : p ∈ X := of_decide_eq_true ((vp X Y p).symm.trans px)
      have lY : l ∈ Y := of_decide_eq_true ((vl X Y l).symm.trans ly)
      exact Finset.disjoint_left.mp (empty l lY) ((incident p l).mpr h) pX
    rw [← listForm]
    exact reject (vector X Y) (count.trans_le budget) outside
  have cpos : 0 < C.size := by
    have h := Finset.card_le_card urange
    rw [Finset.card_range] at h
    omega
  have cold (l : Fin n) : C.eval (incidenceInput (S l)ᶜ {l}) = false := by
    apply sound _ _ (by simp; omega)
    intro l' h
    obtain rfl := Finset.mem_singleton.mp h
    exact disjoint_compl_right
  let V (j : Fin C.size) (X Y : Finset (Fin n)) := wireValue C (incidenceInput X Y) (n+n+j.val)
  let hit (l : Fin n) (j : Fin C.size) : Prop := (gateAt C j.val).op = GateOp.or ∧
    V j (S l)ᶜ {l} = false ∧ ∃ a b, (gateAt C j.val).inputs = [a,b] ∧ ∃ p ∈ S l, ∃ r ∈ S l,
    let A := fun (w : ℕ) (u : Fin n) => wireValue C (incidenceInput {u} {l}) w
    A a p = true ∧ A b p = false ∧ A a r = false ∧ A b r = true
  let load (j : Fin C.size) := Finset.univ.filter fun l => hit l j
  by_contra! small
  have used (l : Fin n) : q ≤ ∑ j : Fin C.size, if hit l j then 1 else 0 := by
    have r := row n S C model cpos correct cold l
    change (S l).card ≤ 1 + Nat.card {j : Fin C.size // hit l j} at r
    rw [lineSize, Nat.card_eq_fintype_card, Fintype.card_subtype] at r
    simpa only [Finset.card_filter] using (show q ≤ (Finset.univ.filter fun j => hit l j).card by omega)
  have crowdedGate : ∃ j : Fin C.size, 100 < (load j).card := by
    by_contra! no
    have lo := Finset.sum_le_sum (s := Finset.univ) fun l _ => used l
    have hi := Finset.sum_le_sum (s := Finset.univ) fun j _ => no j
    rw [Finset.sum_comm] at lo
    have cols (j : Fin C.size) : (∑ l : Fin n, if hit l j then 1 else 0) = (load j).card := by
      exact (Finset.card_filter _ _).symm
    simp only [cols, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at lo hi
    omega
  obtain ⟨j,high⟩ := crowdedGate
  have take (l : Fin n) (hl : l ∈ load j) : hit l j := (Finset.mem_filter.mp hl).2
  obtain ⟨l₀,hl₀⟩ := Finset.card_pos.mp (show 0 < (load j).card by omega)
  apply small.not_ge (crowded q n S C qLarge geom lineSize through model correct sound j.val j.isLt
    (take l₀ hl₀).1 (load j) high (fun l hl => (take l hl).2) ?_)
  let wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w
  have getD_snoc_lt (l : List Bool) (x d : Bool) (i : ℕ) (hi : i < l.length) :
      (l ++ [x]).getD i d = l.getD i d := by
    simp [List.getD, List.getElem?_append_left hi]

  have getD_snoc_eq (l : List Bool) (x d : Bool) (i : ℕ) (hi : i = l.length) :
      (l ++ [x]).getD i d = x := by
    subst hi
    simp [List.getD]

  have getD_snoc_ne (l : List Bool) (x d : Bool) (i : ℕ) (hi : i ≠ l.length) :
      (l ++ [x]).getD i d = l.getD i d := by
    by_cases hlt : i < l.length
    · exact getD_snoc_lt l x d i hlt
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]
  let below (x y : List Bool) : Prop :=
    ∀ i, x.getD i false = true → y.getD i false = true

  have gateMono (g : Gate) (h : (g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)) (x y : List Bool) (hxy : below x y) :
      g.op.eval (g.inputs.map fun i => x.getD i false) = true →
      g.op.eval (g.inputs.map fun i => y.getD i false) = true := by
    have kind : g.op = GateOp.and ∨ g.op = GateOp.or := by simpa using h.1
    have andEq (xs : List Bool) : GateOp.and.eval xs = xs.all id := rfl
    have orEq (xs : List Bool) : GateOp.or.eval xs = xs.any id := rfl
    rcases kind with hg | hg
    · simpa [hg, andEq, List.all_eq_true] using
        (fun (hx : ∀ i ∈ g.inputs, x.getD i false = true) i hi => hxy i (hx i hi))
    · simp only [hg, orEq, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
      rintro ⟨i, hi, hx⟩
      exact ⟨i, hi, hxy i hx⟩

  have appendMono {x y : List Bool} (len : x.length = y.length) (hxy : below x y)
      {a b : Bool} (hab : a = true → b = true) : below (x ++ [a]) (y ++ [b]) := by
    intro i
    by_cases e : i = x.length
    · rwa [getD_snoc_eq _ _ _ _ e, getD_snoc_eq _ _ _ _ (e.trans len)]
    · rw [getD_snoc_ne _ _ _ _ e, getD_snoc_ne _ _ _ _ (by omega)]
      exact hxy i

  have runMono (gs : List Gate) (ok : ∀ g ∈ gs, (g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)) {x y : List Bool}
      (len : x.length = y.length) (hxy : below x y) : below (wiresFrom gs x) (wiresFrom gs y) := by
    induction gs generalizing x y with
    | nil => exact hxy
    | cons g gs ih =>
      apply ih (fun h hm => ok h (List.mem_cons_of_mem g hm)) (by simp [len])
      exact appendMono len hxy (gateMono g (ok g List.mem_cons_self) x y hxy)

  have rowsMono {n : ℕ} {x y : Fin n → Bool} (hxy : ∀ i, x i = true → y i = true) :
      below (List.ofFn x) (List.ofFn y) := by
    intro i
    by_cases hi : i < n
    · simpa [List.getD, List.getElem?_ofFn, hi] using hxy ⟨i, hi⟩
    · simp [List.getD, hi]
  intro p r hp hr
  by_contra ne
  have on (u : Fin n) (hh : V j {u} ∅ = true) : ∀ l ∈ load j, u ∈ S l := by
    intro l hl
    by_contra off
    have inp : ∀ i, vector {u} ∅ i = true → vector (S l)ᶜ {l} i = true := by
      intro i
      refine Fin.addCases (motive := fun i => vector {u} ∅ i = true → vector (S l)ᶜ {l} i = true) ?_ ?_ i
      · intro a
        rw [vp, vp]
        simpa using fun (eq : a = u) => eq.symm ▸ off
      · intro a
        simp only [vl, Finset.notMem_empty, decide_false, Bool.false_eq_true, false_implies]
    have coldWire := (take l hl).2.1
    change wireValue C (incidenceInput _ _) _ = true at hh
    change wireValue C (incidenceInput _ _) _ = false at coldWire
    rw [← listForm] at hh coldWire
    have le := runMono C.gates basis (by simp : (List.ofFn (vector {u} ∅)).length =
      (List.ofFn (vector (S l)ᶜ {l})).length) (rowsMono inp)
    exact Bool.noConfusion ((le _ hh).symm.trans coldWire)
  obtain ⟨k,_,uniq⟩ := through p r ne
  have sub : load j ⊆ {k} := by
    intro l hl
    exact Finset.mem_singleton.mpr (uniq l ⟨on p hp l hl,on r hr l hl⟩)
  have bound := Finset.card_le_card sub
  simp only [Finset.card_singleton] at bound
  omega
