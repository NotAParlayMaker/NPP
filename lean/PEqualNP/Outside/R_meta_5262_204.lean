import PEqualNP.Defs

open Finset PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.EdgeOwnership

-- Count a wire with at least two singleton inputs when it is false on all
-- nonneighbors of its center taken together. C4-freeness gives disjoint witness
-- wires and disjoint charged OR gates, one family of each per center.
-- The wire recurrences follow Nathan Pollock's L_meta_1942; the passage from
-- girth five to the common-neighbor bound follows jturcot42's PR 10231.
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_5262_204
    (builders : ∀ (n : Nat)
    (support : ℕ → Finset (Fin n)) (row isOr : ℕ → Bool) (r t : ℕ) (W : Finset ℕ)
    (_raw : ∀ i < r, (support i).card ≤ 1)
    (_gate : ∀ j < t, ∃ a < r + j, ∃ b < r + j,
      (if isOr j then support a ∪ support b else support a ∩ support b) = support (r + j) ∧
      (if isOr j then row a || row b else row a && row b) = row (r + j))
    (_hw : W ⊆ range (r + t)) (_off : ∀ w ∈ W, row w = false),
    (W.biUnion support).card ≤ W.card + ((range t).filter fun j =>
      isOr j && !row (r + j) && decide (2 ≤ (support (r + j)).card)).card)
    (rest : ∃ k : Nat, ∀ (n : Nat) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    (∀ v (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) → G.edgeFinset.Nonempty →
    ∀ C : Circuit, IsLeastAO G C → TopForm G C →
    let T := {e ∈ Ustar G C | (¬∃ u v : Fin n, e = s(u,v) ∧ ∃ h < C.gates.length, ∃ b : Fin 2,
        2 ≤ (orIn n C (n+h)).card ∧ (∀ z ∈ orIn n C (n+h), G.Adj u z) ∧
        orIn n C (opnd C h b) = {v}) ∧ ∃ a ∈ centreless G C, e ∈ gammaE G C a}
    let serves := fun (e : Sym2 (Fin n)) => ∃ c v : Fin n, e = s(c,v) ∧ ∃ j < C.size,
      gateVal n C j (fun z => decide (¬G.Adj c z)) = false ∧ gateVal n C j (pairInput v v) = true ∧
      ∃ u : Fin n, u ≠ v ∧ gateVal n C j (pairInput u u) = true
    (T.filter (fun e => ¬serves e)).card ≤ k * (C.size+1)) :
    ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [_x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) → x3.edgeFinset.Nonempty → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x3 x7 → PEqualNP.TopForm.TopForm x3 x7 → {x10 ∈ PEqualNP.TopForm.Ustar x3 x7 | (¬∃ (x11 : Fin x2) (x12 : Fin x2), x10 = s(x11, x12) ∧ ∃ x13 < x7.gates.length, ∃ (x14 : Fin (2 : ℕ)), (2 : ℕ) ≤ (PEqualNP.TopForm.orIn x2 x7 (x2 + x13)).card ∧ (∀ x15 ∈ PEqualNP.TopForm.orIn x2 x7 (x2 + x13), x3.Adj x11 x15) ∧ PEqualNP.TopForm.orIn x2 x7 (PEqualNP.TopForm.opnd x7 x13 x14) = {x12}) ∧ ∃ x11 ∈ PEqualNP.TopForm.centreless x3 x7, x10 ∈ PEqualNP.TopForm.gammaE x3 x7 x11}.card ≤ x1 * (x7.size + (1 : ℕ)) := by
  classical
  let serves {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : Circuit) (e : Sym2 (Fin n)) : Prop :=
    ∃ c v : Fin n, e = s(c,v) ∧ ∃ j < C.size,
      gateVal n C j (fun x => decide (¬ G.Adj c x)) = false ∧
      gateVal n C j (pairInput v v) = true ∧
      ∃ u : Fin n, u ≠ v ∧ gateVal n C j (pairInput u u) = true
  have charged {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : Circuit) (ao : IsAO2 n C) (c4 : NoFourCycle G)
      (E : Finset (Sym2 (Fin n))) (hE : ∀ e ∈ E, serves G C e) : E.card ≤ 2*C.size := by
    clear rest
    have disjoint_families {dim : Nat}
        (centres : Finset (Fin dim)) (N : Fin dim → Finset (Fin dim)) (family : Fin dim → Finset Nat) (singles : Nat → Finset (Fin dim))
        (c4 : ∀ a ∈ centres, ∀ b ∈ centres, a ≠ b → (N a ∩ N b).card ≤ 1)
        (localize : ∀ c ∈ centres, ∀ j ∈ family c, 2 ≤ (singles j).card ∧ singles j ⊆ N c) :
        (centres : Set (Fin dim)).PairwiseDisjoint family := by
      intro a ha b hb ne
      apply disjoint_left.mpr
      intro j ja jb
      obtain ⟨_, sa⟩ := localize a ha j ja
      obtain ⟨size, sb⟩ := localize b hb j jb
      have := (card_le_card (subset_inter sa sb)).trans (c4 a ha b hb ne)
      omega


    have families_le {q m n : Nat}
        (support : Nat → Finset (Fin q)) (rows : Fin q → Nat → Bool) (isOr : Nat → Bool)
        (N : Fin q → Finset (Fin q))
        (c4 : ∀ a b, a ≠ b → (N a ∩ N b).card ≤ 1)
        (loc : ∀ c w, w < n+m → rows c w = false → support w ⊆ N c)
        (raw : ∀ i < n, (support i).card ≤ 1)
        (gate : ∀ c j, j < m → ∃ a < n+j, ∃ b < n+j,
          (if isOr j then support a ∪ support b else support a ∩ support b) = support (n+j) ∧
          (if isOr j then rows c a || rows c b else rows c a && rows c b) = rows c (n+j))
        (W : Fin q → Finset Nat)
        (hw : ∀ c w, w ∈ W c → n ≤ w ∧ w < n+m ∧ rows c w = false ∧ 2 ≤ (support w).card) :
        ∑ c, ((W c).biUnion support).card ≤ 2*m := by
      classical
      let charge (c : Fin q) := (range m).filter fun j => isOr j && !(rows c (n+j)) && decide (2 ≤ (support (n+j)).card)
      have bound (c) : ((W c).biUnion support).card ≤ (W c).card + (charge c).card :=
        builders q support (rows c) isOr n m (W c) raw (gate c)
          (fun w h => mem_range.mpr (hw c _ h).2.1) (fun w h => (hw c _ h).2.2.1)
      have disjW := disjoint_families univ N W support (fun a _ b _ => c4 a b) (by
        intro c _ w h
        obtain ⟨_,lt,off,many⟩ := hw c w h
        exact ⟨many, loc c w lt off⟩)
      have disjC := disjoint_families univ N charge (fun j => support (n+j)) (fun a _ b _ => c4 a b) (by
        intro c _ j hj
        simp [charge] at hj
        exact ⟨hj.2.2,loc c (n+j) (by omega) hj.2.1.2⟩)
      have wc : ∑ c, (W c).card ≤ m := by
        rw [← card_biUnion disjW]
        have incl : univ.biUnion W ⊆ Ico n (n+m) := by
          intro w h
          obtain ⟨c,_,hw'⟩ := mem_biUnion.mp h
          exact mem_Ico.mpr ⟨(hw c w hw').1,(hw c w hw').2.1⟩
        simpa using card_le_card incl
      have cc : ∑ c, (charge c).card ≤ m := by
        rw [← card_biUnion disjC]
        have incl : univ.biUnion charge ⊆ range m := by
          intro j h
          obtain ⟨c,_,hj⟩ := mem_biUnion.mp h
          exact (filter_subset _ _) hj
        simpa using card_le_card incl
      have sum := sum_le_sum (s := univ) (fun c _ => bound c)
      rw [sum_add_distrib] at sum
      omega




    -- The generic wire recurrences and count-vector membership lemmas come from checked L-meta-1942.
    let evalFrom {α : Type} (d : α) (op : GateOp → List α → α) (gates : List Gate) (xs : List α) :
        List α :=
      gates.foldl (fun u g => u ++ [op g.op (g.inputs.map fun i => u.getD i d)]) xs

    have evAnd (xs : List Bool) : GateOp.and.eval xs = xs.all id := rfl
    have evOr (xs : List Bool) : GateOp.or.eval xs = xs.any id := rfl
    have pairSelf {n : Nat} (v : Fin n) : pairInput v v = fun i => decide (i = v ∨ i = v) := rfl

    have evalFrom_cons {α : Type} (d : α) (op : GateOp → List α → α) (g : Gate) (gs : List Gate)
        (xs : List α) :
        evalFrom d op (g :: gs) xs = evalFrom d op gs
          (xs ++ [op g.op (g.inputs.map fun i => xs.getD i d)]) := rfl

    have evalFrom_length {α : Type} (d : α) (op : GateOp → List α → α) (gs : List Gate)
        (xs : List α) : (evalFrom d op gs xs).length = xs.length + gs.length := by
      induction gs generalizing xs with
      | nil => simp [evalFrom]
      | cons g gs ih => rw [evalFrom_cons, ih]; simp; omega

    have evalFrom_input {α : Type} (d : α) (op : GateOp → List α → α) (gs : List Gate)
        (xs : List α) (i : ℕ) (hi : i < xs.length) :
        (evalFrom d op gs xs).getD i d = xs.getD i d := by
      induction gs generalizing xs with
      | nil => rfl
      | cons g gs ih =>
        rw [evalFrom_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hi]

    let row (C : Circuit) (k : Fin C.size) : Gate := C.gates[k.val]'k.isLt

    let operand (C : Circuit) (k : Fin C.size) (b : Fin 2) : ℕ :=
      (row C k).inputs.getD b.val 0

    let outWire (n : ℕ) {s : ℕ} (k : Fin s) : ℕ := n + k.val

    have inputs_two {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) (k : Fin C.size) :
        (row C k).inputs = [operand C k 0, operand C k 1] := by
      obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (h.2.2 (row C k) (List.getElem_mem _))
      simp [operand, hab]

    have op_kind {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) (k : Fin C.size) :
        (row C k).op = GateOp.and ∨ (row C k).op = GateOp.or :=
      h.1 (row C k) (List.getElem_mem _)

    have earlier {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
        (k : Fin C.size) (b : Fin 2) : operand C k b < outWire n k := by
      have he : gateAt C k.val = row C k := List.getD_eq_getElem _ _ k.isLt
      have hm : operand C k b ∈ (row C k).inputs := by
        rw [inputs_two h k]
        fin_cases b <;> simp
      exact h.2.1 k.val k.isLt (operand C k b) (by simpa only [he] using hm)

    have evalFrom_gate {α : Type} (d : α) (op : GateOp → List α → α) {n : ℕ}
        {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) (xs : List α) (hx : xs.length = n)
        (k : Fin C.size) :
        (evalFrom d op C.gates xs).getD (outWire n k) d =
          op (row C k).op ([(evalFrom d op C.gates xs).getD (operand C k 0) d,
            (evalFrom d op C.gates xs).getD (operand C k 1) d]) := by
      let front := evalFrom d op (C.gates.take k.val) xs
      have hf : front.length = outWire n k := by
        have hk : k.val ≤ C.gates.length := k.isLt.le
        simp [front, evalFrom_length, hx, outWire, Nat.min_eq_left hk]
      have hsplit : evalFrom d op C.gates xs =
          evalFrom d op (row C k :: C.gates.drop (k.val + 1)) front := by
        simp only [front, row, evalFrom, ← List.foldl_append, ← List.drop_eq_getElem_cons k.isLt,
          List.take_append_drop]
      have hread (i : ℕ) (hi : i < outWire n k) :
          (evalFrom d op C.gates xs).getD i d = front.getD i d := by
        rw [hsplit, evalFrom_input _ _ _ _ _ (by simpa only [hf] using hi)]
      change (evalFrom d op C.gates xs).getD (outWire n k) d = _
      rw [hread _ (earlier h k 0), hread _ (earlier h k 1), hsplit, evalFrom_cons]
      rw [evalFrom_input _ _ _ _ _ (by simp; omega)]
      rw [List.getD_append_right _ _ _ _ (by omega)]
      simp [hf, inputs_two h k]

    let circuitValue {n : ℕ} (C : Circuit) (z : Fin n → Bool) (w : ℕ) : Bool :=
      (evalFrom false GateOp.eval C.gates (List.ofFn z)).getD w false

    have value_input {n : ℕ} (C : Circuit) (z : Fin n → Bool) {w : ℕ} (hw : w < n) :
        circuitValue C z w = z ⟨w, hw⟩ := by
      have hi : w < (List.ofFn z).length := by simpa using hw
      unfold circuitValue
      rw [evalFrom_input _ _ _ _ _ hi, List.getD_eq_getElem _ _ hi]
      simp

    have value_gate {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
        (z : Fin n → Bool) (k : Fin C.size) :
        circuitValue C z (outWire n k) = (row C k).op.eval
          [circuitValue C z (operand C k 0), circuitValue C z (operand C k 1)] :=
      evalFrom_gate _ _ h _ List.length_ofFn k


    have served_edges {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
        (C : Circuit) (ao : IsAO2 n C) (c4 : NoFourCycle G)
        (E : Finset (Sym2 (Fin n))) (hE : ∀ e ∈ E, serves G C e) : E.card ≤ 2*C.size := by
      classical
      let val (w : Nat) (X : Finset (Fin n)) := circuitValue C (fun i => decide (i∈X)) w
      let support (w : Nat) := univ.filter fun v : Fin n => val w {v}
      let isOr (j : Nat) := decide ((gateAt C j).op = .or)
      let N (c : Fin n) := univ.filter fun v => G.Adj c v
      let rows (c : Fin n) (w : Nat) := val w (N c)ᶜ
      let W (c : Fin n) := (Ico n (n+C.size)).filter fun w => rows c w = false ∧ 2 ≤ (support w).card
      have raw (i : Nat) (hi : i<n) (X : Finset (Fin n)) : val i X = decide ((⟨i,hi⟩ : Fin n) ∈ X) :=
        value_input C _ hi
      have base (i : Nat) (hi : i<n) : (support i).card ≤ 1 := by
        have eqn : support i = {⟨i,hi⟩} := by
          ext v
          simp only [support, mem_filter, mem_univ, true_and, raw i hi, decide_eq_true_eq, mem_singleton]
          exact eq_comm
        simp [eqn]
      have gate (j : Nat) (hj : j < C.size) : ∃ a < n+j, ∃ b < n+j, ∀ X, val (n+j) X =
          if isOr j then val a X || val b X else val a X && val b X := by
        let k : Fin C.size := ⟨j,hj⟩
        refine ⟨operand C k 0, earlier ao k 0, operand C k 1, earlier ao k 1, ?_⟩
        intro X
        have he : gateAt C j = row C k := List.getD_eq_getElem _ _ hj
        have h := value_gate ao (fun i => decide (i∈X)) k
        change val (n+j) X = (row C k).op.eval [_,_] at h
        rcases op_kind ao k with kind | kind <;> rw [h, kind] <;> simp [isOr, he, kind, evAnd, evOr, val]
      have mono (w : Nat) (hw : w < n+C.size) (X Y : Finset (Fin n)) (incl : X ⊆ Y) :
          val w X = true → val w Y = true := by
        induction w using Nat.strong_induction_on with
        | ind w ih =>
          by_cases small : w < n
          · simpa [raw w small] using fun hx => incl hx
          · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt small)
            obtain ⟨a, ha, b, hb, eqn⟩ := gate j (by omega)
            have left := ih a ha (by omega)
            have right := ih b hb (by omega)
            cases ho : isOr j
            · simp only [eqn, ho, Bool.false_eq_true, ite_false, Bool.and_eq_true_iff]
              exact fun h => ⟨left h.1, right h.2⟩
            · simp only [eqn, ho, ite_true, Bool.or_eq_true]
              exact Or.imp left right
      have loc (c w) (hw : w<n+C.size) (off : rows c w = false) : support w ⊆ N c := by
        intro v hv
        by_contra no
        have inc : {v} ⊆ (N c)ᶜ := by simpa using no
        have on := mono w hw _ _ inc (mem_filter.mp hv).2
        exact Bool.false_ne_true (off.symm.trans on)
      have gates (c : Fin n) (j : Nat) (hj : j < C.size) : ∃ a < n+j, ∃ b < n+j,
          (if isOr j then support a ∪ support b else support a ∩ support b) = support (n+j) ∧
          (if isOr j then rows c a || rows c b else rows c a && rows c b) = rows c (n+j) := by
        obtain ⟨a,ha,b,hb,h⟩ := gate j hj
        refine ⟨a,ha,b,hb,?_,(h _).symm⟩
        ext v
        cases ho : isOr j <;> simp [support,h,ho]
      have size := families_le support rows isOr N (by
        intro a b hab
        have eqn : N a ∩ N b = univ.filter (fun w => G.Adj a w ∧ G.Adj b w) := by
          ext v
          simp [N]
        exact eqn ▸ c4 a b hab)
        loc base gates W (by
          intro c w hw
          obtain ⟨h,off,many⟩ := mem_filter.mp hw
          exact ⟨(mem_Ico.mp h).1,(mem_Ico.mp h).2,off,many⟩)
      let S (c : Fin n) := (W c).biUnion support
      have one (j : Nat) (v : Fin n) : gateVal n C j (pairInput v v) = val (n+j) {v} := by
        have bits : pairInput v v = fun i => decide (i ∈ ({v} : Finset (Fin n))) := by
          funext i
          simp [pairSelf]
        rw [bits]; rfl
      have outside (j : Nat) (c : Fin n) : gateVal n C j (fun x => decide (¬G.Adj c x)) = rows c (n+j) := by
        have bits : (fun x => decide (¬G.Adj c x)) = fun i => decide (i∈(N c)ᶜ) := by
          funext i; simp [N]
        rw [bits]; rfl
      have cover : E ⊆ univ.biUnion (fun c => (S c).image fun v => s(c,v)) := by
        intro e he
        obtain ⟨c,v,rfl,j,hj,off,hv,u,ne,hu⟩ := hE e he
        have member (w : Fin n) (on : gateVal n C j (pairInput w w) = true) : w ∈ support (n+j) :=
          mem_filter.mpr ⟨mem_univ _,(one j w) ▸ on⟩
        refine mem_biUnion.mpr ⟨c,mem_univ _,mem_image.mpr ⟨v,?_,rfl⟩⟩
        exact mem_biUnion.mpr ⟨n+j,mem_filter.mpr ⟨mem_Ico.mpr ⟨by omega,by omega⟩,(outside j c) ▸ off,
          one_lt_card.mpr ⟨u,member u hu,v,member v hv,ne⟩⟩,member v hv⟩
      calc
        E.card ≤ _ := card_le_card cover
        _ ≤ _ := card_biUnion_le
        _ ≤ ∑ c, (S c).card := sum_le_sum fun _ _ => card_image_le
        _ ≤ _ := size
    exact served_edges G C ao c4 E hE
  have no_four {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (girth : ∀ a : Fin n, ∀ p : G.Walk a a, p.IsCycle → 5 ≤ p.length) : NoFourCycle G := by
    clear rest builders
    intro a b ab
    by_contra t
    have two := Nat.lt_of_not_ge t
    obtain ⟨u, hu, v, hv, uv⟩ := Finset.one_lt_card.mp two
    obtain ⟨_, au, bu⟩ := Finset.mem_filter.mp hu
    obtain ⟨_, av, bv⟩ := Finset.mem_filter.mp hv
    let p := SimpleGraph.Walk.cons au (.cons bu.symm (.cons bv (.cons av.symm .nil)))
    have cyc : p.IsCycle := by
      dsimp [p]
      rw [SimpleGraph.Walk.cons_isCycle_iff]
      constructor
      · simp [SimpleGraph.Walk.cons_isPath_iff, ab.symm, uv, au.ne.symm, bu.ne.symm, av.ne.symm, bv.ne]
      · simp [ab, uv, au.ne, au.ne.symm, bu.ne.symm, av.ne]
    have bad := girth a p cyc
    simp [p] at bad


  obtain ⟨k, residual⟩ := rest
  refine ⟨k+2, ?_⟩
  intro n G inst girth edges C least top
  let T := {e ∈ Ustar G C | (¬∃ u v : Fin n, e = s(u,v) ∧ ∃ h < C.gates.length, ∃ b : Fin 2,
        2 ≤ (orIn n C (n+h)).card ∧ (∀ z ∈ orIn n C (n+h), G.Adj u z) ∧
        orIn n C (opnd C h b) = {v}) ∧ ∃ a ∈ centreless G C, e ∈ gammaE G C a}
  change T.card ≤ _
  let A := T.filter (serves G C)
  have small : A.card ≤ 2*C.size :=
    charged G C least.1 (no_four G girth) A (fun e he => (mem_filter.mp he).2)
  have hrest : (T.filter (fun e => ¬ serves G C e)).card ≤ k*(C.size+1) :=
    residual n G girth edges C least top
  have partition := T.card_filter_add_card_filter_not (serves G C)
  change A.card + _ = T.card at partition
  rw [← partition, Nat.add_mul, Nat.add_comm (k * (C.size+1))]
  exact Nat.add_le_add (small.trans (Nat.mul_le_mul_left 2 (Nat.le_succ _))) hrest
