import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.ReadK PEqualNP.ReadTwo

-- Use least top form and preserve size while finding short accepting paths for each edge.
theorem PEqualNP.Outside.R_meta_2584_2
    (normal : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : Circuit), G.edgeFinset.Nonempty → PEqualNP.TopForm.IsLeastAO G C →
      ∃ D : Circuit, PEqualNP.TopForm.IsLeastAO G D ∧ D.size = C.size ∧
        (PEqualNP.TopForm.junk G D).card = (PEqualNP.TopForm.junk G C).card ∧
        PEqualNP.TopForm.TopForm G D)
    (repair : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : Circuit), PEqualNP.TopForm.NoFourCycle G →
      (∃ color : Fin n → Bool, ∀ u v, G.Adj u v → color u ≠ color v) →
      G.edgeFinset.Nonempty → PEqualNP.TopForm.IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
      ¬ IsReadK n C 2 →
      ∃ D : Circuit, PEqualNP.TopForm.IsLeastAO G D ∧
        ∀ u v : Fin n, G.Adj u v →
        let path := orp D n
        let pair (w i j : ℕ) :=
          ∃ g a b, isAnd D g ∧ (gateAt D g).inputs = [a,b] ∧ path (n+g) w ∧
            path i a ∧ path j b
        let light (w : ℕ) :=
          path u.val w ∨ path v.val w ∨ pair w u.val v.val ∨ pair w v.val u.val
        let pure (w r : ℕ) := path r w ∨ pair w r r
        ∃ g a b, isAnd D g ∧ (gateAt D g).inputs = [a,b] ∧ path (n+g) D.output ∧
          ((light a ∧ light b) ∨ (pure a u.val ∧ pure b v.val) ∨
            (pure a v.val ∧ pure b u.val))) :
    ∀ (P L : ℕ) (I : Fin P → Fin L → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ p p' : Fin P, ∀ l l' : Fin L, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.TopForm.IsAO2 (P + L) C → (∀ z : Fin (P + L) → Bool, PEqualNP.MetaComplexity.circuitFun (P + L) C z = decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧ z (Fin.castAdd L p) = true ∧ z (Fin.natAdd P l) = true)) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 (P + L) D ∧ (∀ y : Fin (P + L) → Bool, PEqualNP.MetaComplexity.circuitFun (P + L) D y = decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧ y (Fin.castAdd L p) = true ∧ y (Fin.natAdd P l) = true)) ∧ D.size ≤ C.size ∧ PEqualNP.ReadK.IsReadK (P + L) D 2 := by
  classical
  -- The circuit fold and count-vector lemmas follow the evaluation in L_meta_1942.
  let evalFrom {α : Type} (d : α) (op : GateOp → List α → α) (gates : List Gate) (xs : List α) :
      List α :=
    gates.foldl (fun u g => u ++ [op g.op (g.inputs.map fun i => u.getD i d)]) xs

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


  have mem_insertNew (a v : List ℕ) (A : List (List ℕ)) :
      v ∈ insertNew A a ↔ v ∈ A ∨ v = a := by
    unfold insertNew
    by_cases ha : a ∈ A
    · simp [ha, or_iff_left_of_imp (fun (e : v = a) => e.symm ▸ ha)]
    · simp [ha]

  have mem_fold_insertNew (v : List ℕ) (B A : List (List ℕ)) :
      v ∈ B.foldl insertNew A ↔ v ∈ A ∨ v ∈ B := by
    induction B generalizing A with
    | nil => simp
    | cons b B ih => simp [ih, mem_insertNew, or_assoc]

  have mem_andStep_two (v : List ℕ) (A B : List (List ℕ)) :
      v ∈ andStep 2 A B ↔ ∃ u ∈ A, ∃ w ∈ B, v = capAdd 2 u w := by
    delta andStep
    simp [mem_fold_insertNew, List.mem_flatMap, List.mem_map, eq_comm]

  let encode (S t : List ℕ) : List ℕ :=
    S.map fun j => min (t.count j) 3

  have encode_nil (S : List ℕ) : encode S [] = S.map (fun _ => 0) := by
    simp [encode]

  have encode_append (S t u : List ℕ) :
      capAdd 2 (encode S t) (encode S u) = encode S (t ++ u) := by
    induction S with
    | nil => rfl
    | cons a S ih =>
      have cap_eq (x y : List ℕ) :
          capAdd 2 x y = List.zipWith (fun i j => min (i+j) 3) x y := rfl
      simp only [encode, cap_eq, List.map_cons, List.zipWith_cons_cons, List.count_append] at ih ⊢
      rw [ih]
      congr 1
      omega

  let readOp (S : List ℕ) (o : GateOp) (ins : List (List (List ℕ))) : List (List ℕ) :=
    GateOp.rec (ins.foldl (andStep 2) [S.map fun _ => 0])
      (ins.foldl (fun acc A => A.foldl insertNew acc) []) [] (fun _ => []) [] o

  let vecs (n : ℕ) (C : Circuit) (S : List ℕ) (w : ℕ) : List (List ℕ) :=
    ((readVectors C n S 2).getD w [])

  have vec_eval (n : ℕ) (C : Circuit) (S : List ℕ) (w : ℕ) :
      vecs n C S w =
        (evalFrom [] (readOp S) C.gates ((List.range n).map (leafVectors S 2))).getD w [] := by
      change (readVectors C n S 2).getD w [] = (C.gates.foldl
        (fun R g => R ++ [readOp S g.op (g.inputs.map fun i => R.getD i [])])
        ((List.range n).map (leafVectors S 2))).getD w []
      delta readVectors
      congr 2
      funext R g
      cases g with
      | mk op inputs => cases op <;> rfl

  have row_at (C : Circuit) (k : Fin C.size) :
      row C k = gateAt C k.val := by
    change C.gates[k.val] = C.gates.getD k.val ⟨.or,[]⟩
    exact (List.getD_eq_getElem _ _ k.isLt).symm

  have vec_gate {n : ℕ} {C : Circuit} (ao : PEqualNP.TopForm.IsAO2 n C)
      (S : List ℕ) (g a b : ℕ) (hg : g < C.size)
      (pins : (gateAt C g).inputs = [a,b]) :
      vecs n C S (n+g) = readOp S (gateAt C g).op [vecs n C S a, vecs n C S b] := by
    let k : Fin C.size := ⟨g,hg⟩
    have len : ((List.range n).map (leafVectors S 2)).length = n := by simp
    have e := evalFrom_gate [] (readOp S) ao _ len k
    simp only [← vec_eval] at e
    rw [e]
    simp [operand, row_at, k, pins]

  have vec_leaf {n : ℕ} {C : Circuit} (S : List ℕ) (i : Fin n) (hi : i.val ∈ S) :
      encode S [i.val] ∈ vecs n C S i.val := by
    have lt : i.val < ((List.range n).map (leafVectors S 2)).length := by simp
    rw [vec_eval, evalFrom_input _ _ _ _ _ lt, List.getD_eq_getElem _ _ lt]
    simp only [List.getElem_map, List.getElem_range]
    delta leafVectors
    simp only [hi, ite_true, List.mem_singleton]
    apply List.map_congr_left
    intro j _
    by_cases e : j = i.val
    · subst j
      simp
    · simp [e, Ne.symm e]

  have vec_and {n : ℕ} {C : Circuit} (ao : PEqualNP.TopForm.IsAO2 n C)
      (S : List ℕ) (g a b : ℕ) (hg : isAnd C g)
      (pins : (gateAt C g).inputs = [a,b]) {t u : List ℕ}
      (ht : encode S t ∈ vecs n C S a) (hu : encode S u ∈ vecs n C S b) :
      encode S (t ++ u) ∈ vecs n C S (n+g) := by
    rw [vec_gate ao S g a b hg.1 pins, hg.2]
    apply (mem_andStep_two _ _ _).mpr
    refine ⟨encode S t, (mem_andStep_two _ _ _).mpr ?_, encode S u, hu, (encode_append S t u).symm⟩
    exact ⟨encode S [],by simp [encode_nil],encode S t,ht,by rw [encode_append]; rfl⟩

  have vec_path {n : ℕ} {C : Circuit} (ao : PEqualNP.TopForm.IsAO2 n C)
      (S : List ℕ) {a b : ℕ} (path : orp C n a b) {v : List ℕ}
      (hv : v ∈ vecs n C S a) : v ∈ vecs n C S b := by
    induction path with
    | refl => exact hv
    | tail _ link ih =>
      obtain ⟨_,g,rfl,⟨hg, ho⟩, hi⟩ := link
      let k : Fin C.size := ⟨g,hg⟩
      let l := operand C k 0
      let r := operand C k 1
      have pins := inputs_two ao k
      rw [row_at] at pins
      change (gateAt C g).inputs = [l,r] at pins
      rw [vec_gate ao S g l r hg pins, ho]
      rw [pins] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      change v ∈ (vecs n C S r).foldl insertNew ((vecs n C S l).foldl insertNew [])
      rw [mem_fold_insertNew, mem_fold_insertNew]
      simp only [List.not_mem_nil, false_or]
      exact hi.elim (fun e => Or.inl (e ▸ ih)) (fun e => Or.inr (e ▸ ih))


  let Shape (n : ℕ) (D : Circuit) (u v : Fin n) : Prop :=
    let path := orp D n
    let pair (w i j : ℕ) :=
      ∃ g a b, isAnd D g ∧ (gateAt D g).inputs = [a,b] ∧ path (n+g) w ∧
        path i a ∧ path j b
    let light (w : ℕ) :=
      path u.val w ∨ path v.val w ∨ pair w u.val v.val ∨ pair w v.val u.val
    let pure (w r : ℕ) := path r w ∨ pair w r r
    ∃ g a b, isAnd D g ∧ (gateAt D g).inputs = [a,b] ∧ path (n+g) D.output ∧
      ((light a ∧ light b) ∨ (pure a u.val ∧ pure b v.val) ∨
        (pure a v.val ∧ pure b u.val))

  have shape_reads {n : ℕ} {D : Circuit} (ao : PEqualNP.TopForm.IsAO2 n D)
      (S : List ℕ) (u v : Fin n) (ne : u ≠ v)
      (hu : u.val ∈ S) (hv : v.val ∈ S) (shape : Shape n D u v) :
      readsAtMost D n S 2 = true := by
    have distinct : u.val ≠ v.val := fun e => ne (Fin.ext e)
    let path := orp D n
    let pair (w i j : ℕ) :=
      ∃ g a b, isAnd D g ∧ (gateAt D g).inputs = [a,b] ∧ path (n+g) w ∧
        path i a ∧ path j b
    let light (w : ℕ) :=
      path u.val w ∨ path v.val w ∨ pair w u.val v.val ∨ pair w v.val u.val
    let pure (w r : ℕ) := path r w ∨ pair w r r
    have atLeaf (i : Fin n) (hi : i.val ∈ S) {w : ℕ} (h : path i.val w) :
        encode S [i.val] ∈ vecs n D S w :=
      vec_path ao S h (vec_leaf S i hi)
    have atPair (i j : Fin n) (hi : i.val ∈ S) (hj : j.val ∈ S) {w : ℕ}
        (h : pair w i.val j.val) : encode S [i.val,j.val] ∈ vecs n D S w := by
      obtain ⟨g,a,b,hg,pins,up,left,right⟩ := h
      exact vec_path ao S up (vec_and ao S g a b hg pins (atLeaf i hi left) (atLeaf j hj right))
    have single (i j : ℕ) : [i].count j ≤ 1 := List.count_le_length
    have mixed {i j : ℕ} (d : i ≠ j) (k : ℕ) : [i,j].count k ≤ 1 := by
      by_cases h : k = i
      · subst k
        simp [d]
      · simp [List.count_cons, Ne.symm h]
        split <;> decide
    have pickLight (w : ℕ) (h : light w) :
        ∃ t, encode S t ∈ vecs n D S w ∧ ∀ i, t.count i ≤ 1 := by
      rcases h with h | h | h | h
      · exact ⟨[u.val],atLeaf u hu h,single _⟩
      · exact ⟨[v.val],atLeaf v hv h,single _⟩
      · exact ⟨[u.val,v.val],atPair u v hu hv h,mixed distinct⟩
      · exact ⟨[v.val,u.val],atPair v u hv hu h,mixed (Ne.symm distinct)⟩
    have pickPure (w : ℕ) (i : Fin n) (hi : i.val ∈ S) (h : pure w i.val) :
        ∃ t, encode S t ∈ vecs n D S w ∧ t.length ≤ 2 ∧ ∀ z ∈ t, z = i.val := by
      rcases h with h | h
      · exact ⟨[i.val],atLeaf i hi h,by simp,by simp⟩
      · exact ⟨[i.val,i.val],atPair i i hi hi h,by simp,by simp⟩
    have separated (t s : List ℕ) {i j : ℕ} (d : i ≠ j)
        (ht : t.length ≤ 2) (hs : s.length ≤ 2)
        (hi : ∀ z ∈ t, z = i) (hj : ∀ z ∈ s, z = j) (z : ℕ) :
        (t ++ s).count z ≤ 2 := by
      rw [List.count_append]
      by_cases e : z = i
      · have hz : z ∉ s := fun h => d (e.symm.trans (hj z h))
        rw [List.count_eq_zero_of_not_mem hz, Nat.add_zero]
        exact List.count_le_length.trans ht
      · have hz : z ∉ t := fun h => e (hi z h)
        rw [List.count_eq_zero_of_not_mem hz, Nat.zero_add]
        exact List.count_le_length.trans hs
    rcases shape with ⟨g,a,b,hg,pins,up,split⟩
    have finish (t s : List ℕ) (ht : encode S t ∈ vecs n D S a)
        (hs : encode S s ∈ vecs n D S b) (count : ∀ k, (t ++ s).count k ≤ 2) :
        readsAtMost D n S 2 = true := by
      unfold readsAtMost
      refine List.any_eq_true.mpr ⟨encode S (t ++ s),
        vec_path ao S up (vec_and ao S g a b hg pins ht hs),?_⟩
      apply List.all_eq_true.mpr
      intro c hc
      obtain ⟨k,_,rfl⟩ := List.mem_map.mp hc
      exact decide_eq_true (le_trans (min_le_left _ _) (count k))
    rcases split with split | split | split
    · obtain ⟨t,ht,bt⟩ := pickLight a split.1
      obtain ⟨s,hs,bs⟩ := pickLight b split.2
      exact finish t s ht hs (fun k => by rw [List.count_append]; have := bt k; have := bs k; omega)
    · obtain ⟨t,ht,bt,ot⟩ := pickPure a u hu split.1
      obtain ⟨s,hs,bs,os⟩ := pickPure b v hv split.2
      exact finish t s ht hs (separated t s distinct bt bs ot os)
    · obtain ⟨t,ht,bt,ot⟩ := pickPure a v hv split.1
      obtain ⟨s,hs,bs,os⟩ := pickPure b u hu split.2
      exact finish t s ht hs (separated t s (Ne.symm distinct) bt bs ot os)

  have graph_edge {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (z : Fin n → Bool) (h : graphFun G ∅ z = true) :
      ∃ u v, G.Adj u v ∧ z u = true ∧ z v = true := by
    delta graphFun at h
    simpa using h

  have graph_reads {n : ℕ} {D : Circuit} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (ao : PEqualNP.TopForm.IsAO2 n D) (computes : circuitFun n D = graphFun G ∅)
      (h : ∀ u v, G.Adj u v → Shape n D u v) : IsReadK n D 2 := by
    intro S prime
    have accepts : graphFun G ∅ (setInput S) = true := by
      rw [← computes]
      exact prime.1
    obtain ⟨u,v,e,hu,hv⟩ := graph_edge G _ accepts
    have mem_List (i : Fin n) (hi : setInput S i = true) : i.val ∈ setList S := by
      unfold setList
      exact List.mem_map.mpr ⟨i, List.mem_filter.mpr ⟨by simp, hi⟩, rfl⟩
    exact shape_reads ao _ u v (G.ne_of_adj e) (mem_List u hu) (mem_List v hv) (h u v e)

  let adjacent (P L : ℕ) (I : Fin P → Fin L → Prop) (u v : Fin (P + L)) : Prop :=
    Fin.addCases (fun p => Fin.addCases (fun _ => False) (I p) v)
      (fun l => Fin.addCases (fun p => I p l) (fun _ => False) v) u

  let graph (P L : ℕ) (I : Fin P → Fin L → Prop) : SimpleGraph (Fin (P + L)) :=
    { Adj := adjacent P L I
      symm := ⟨by
        intro u v h
        induction u using Fin.addCases <;> induction v using Fin.addCases <;>
          simp only [adjacent, Fin.addCases_left, Fin.addCases_right] at h ⊢ <;> exact h⟩
      loopless := ⟨by
        intro u
        induction u using Fin.addCases <;>
          simp only [adjacent, Fin.addCases_left, Fin.addCases_right, not_false_eq_true]⟩ }

  have vertexSide (P L : ℕ) (u : Fin (P + L)) :
      (∃ p : Fin P, u = Fin.castAdd L p) ∨ (∃ l : Fin L, u = Fin.natAdd P l) :=
    Fin.addCases (fun p => Or.inl ⟨p, rfl⟩) (fun l => Or.inr ⟨l, rfl⟩) u

  have pointNeighbor (P L : ℕ) (I : Fin P → Fin L → Prop) (p : Fin P)
      {u : Fin (P + L)} (h : (graph P L I).Adj (Fin.castAdd L p) u) :
      ∃ l : Fin L, u = Fin.natAdd P l ∧ I p l := by
    rcases vertexSide P L u with ⟨q, rfl⟩ | ⟨l, rfl⟩
    · simp [graph, adjacent, Fin.addCases_left] at h
    · exact ⟨l, rfl, by simpa [graph, adjacent, Fin.addCases_left, Fin.addCases_right] using h⟩

  have lineNeighbor (P L : ℕ) (I : Fin P → Fin L → Prop) (l : Fin L)
      {u : Fin (P + L)} (h : (graph P L I).Adj (Fin.natAdd P l) u) :
      ∃ p : Fin P, u = Fin.castAdd L p ∧ I p l := by
    rcases vertexSide P L u with ⟨p, rfl⟩ | ⟨m, rfl⟩
    · exact ⟨p, rfl, by simpa [graph, adjacent, Fin.addCases_left, Fin.addCases_right] using h⟩
    · simp [graph, adjacent, Fin.addCases_right] at h

  have graphFun_eq (P L : ℕ) (I : Fin P → Fin L → Prop) [DecidableRel I]
      (z : Fin (P + L) → Bool) :
      graphFun (graph P L I) ∅ z = decide (∃ p : Fin P, ∃ l : Fin L,
        I p l ∧ z (Fin.castAdd L p) = true ∧ z (Fin.natAdd P l) = true) := by
    delta graphFun
    simp only [Finset.notMem_empty, false_and, exists_false, decide_false,
      Bool.false_or, decide_eq_decide]
    constructor
    · rintro ⟨u, v, hadj, hu, hv⟩
      rcases vertexSide P L u with ⟨p, rfl⟩ | ⟨l, rfl⟩
      · obtain ⟨l, rfl, h⟩ := pointNeighbor P L I p hadj
        exact ⟨p, l, h, hu, hv⟩
      · obtain ⟨p, rfl, h⟩ := lineNeighbor P L I l hadj
        exact ⟨p, l, h, hv, hu⟩
    · rintro ⟨p, l, h, hp, hl⟩
      exact ⟨Fin.castAdd L p, Fin.natAdd P l,
        by simpa [graph, adjacent, Fin.addCases_left, Fin.addCases_right] using h, hp, hl⟩

  have noFourCycle (P L : ℕ) (I : Fin P → Fin L → Prop)
      (square : ∀ p q : Fin P, ∀ l m : Fin L,
        p ≠ q → l ≠ m → ¬ (I p l ∧ I p m ∧ I q l ∧ I q m)) :
      PEqualNP.TopForm.NoFourCycle (graph P L I) := by
    intro u v huv
    apply Finset.card_le_one.mpr
    intro a ha b hb
    have adjA := (Finset.mem_filter.mp ha).2
    have adjB := (Finset.mem_filter.mp hb).2
    rcases vertexSide P L u with ⟨p, rfl⟩ | ⟨l, rfl⟩ <;>
      rcases vertexSide P L v with ⟨q, rfl⟩ | ⟨m, rfl⟩
    · obtain ⟨l, rfl, hpl⟩ := pointNeighbor P L I p adjA.1
      obtain ⟨m, rfl, hpm⟩ := pointNeighbor P L I p adjB.1
      by_contra hne
      have hpq : p ≠ q := fun h => huv (congrArg (Fin.castAdd L) h)
      have hlm : l ≠ m := fun h => hne (congrArg (Fin.natAdd P) h)
      have hql : I q l := by simpa [graph, adjacent, Fin.addCases_left, Fin.addCases_right] using adjA.2
      have hqm : I q m := by simpa [graph, adjacent, Fin.addCases_left, Fin.addCases_right] using adjB.2
      exact square p q l m hpq hlm ⟨hpl, hpm, hql, hqm⟩
    · obtain ⟨l, rfl, _⟩ := pointNeighbor P L I p adjA.1
      have h := adjA.2
      simp [graph, adjacent, Fin.addCases_right] at h
    · obtain ⟨p, rfl, _⟩ := lineNeighbor P L I l adjA.1
      have h := adjA.2
      simp [graph, adjacent, Fin.addCases_left] at h
    · obtain ⟨p, rfl, hpl⟩ := lineNeighbor P L I l adjA.1
      obtain ⟨q, rfl, hql⟩ := lineNeighbor P L I l adjB.1
      by_contra hne
      have hpq : p ≠ q := fun h => hne (congrArg (Fin.castAdd L) h)
      have hlm : l ≠ m := fun h => huv (congrArg (Fin.natAdd P) h)
      have hpm : I p m := by simpa [graph, adjacent, Fin.addCases_left, Fin.addCases_right] using adjA.2
      have hqm : I q m := by simpa [graph, adjacent, Fin.addCases_left, Fin.addCases_right] using adjB.2
      exact square p q l m hpq hlm ⟨hpl, hpm, hql, hqm⟩

  let color (P L : ℕ) : Fin (P + L) → Bool :=
    Fin.addCases (fun _ => false) (fun _ => true)

  have bipartite (P L : ℕ) (I : Fin P → Fin L → Prop) :
      ∀ u v, (graph P L I).Adj u v → color P L u ≠ color P L v := by
    intro u v hadj
    rcases vertexSide P L u with ⟨p, rfl⟩ | ⟨l, rfl⟩ <;>
      rcases vertexSide P L v with ⟨q, rfl⟩ | ⟨m, rfl⟩
    · simp [graph, adjacent, Fin.addCases_left] at hadj
    · simp [color, Fin.addCases_left, Fin.addCases_right]
    · simp [color, Fin.addCases_left, Fin.addCases_right]
    · simp [graph, adjacent, Fin.addCases_right] at hadj

  intro P L I dec C hC4 ao computes
  let n := P + L
  let G := graph P L I
  have input_agrees : circuitFun n C = graphFun G ∅ := by
    funext z
    exact (computes z).trans (graphFun_eq P L I z).symm
  by_cases hasEdge : G.edgeFinset.Nonempty
  · let viable (k : ℕ) := ∃ D : Circuit, PEqualNP.TopForm.IsAO2 n D ∧
      circuitFun n D = graphFun G ∅ ∧ D.size = k
    have exists_ : ∃ k, viable k := ⟨C.size,C,ao,input_agrees,rfl⟩
    obtain ⟨A,ha,ca,sa⟩ := Nat.find_spec exists_
    have least : PEqualNP.TopForm.IsLeastAO G A := by
      refine ⟨ha,ca,?_⟩
      intro D hd cd
      rw [sa]
      exact Nat.find_min' exists_ (show viable D.size from ⟨D,hd,cd,rfl⟩)
    obtain ⟨B,best,_,_,top⟩ := normal n G A hasEdge least
    have deliver (D : Circuit) (leastD : PEqualNP.TopForm.IsLeastAO G D)
        (readD : IsReadK n D 2) :
        PEqualNP.TopForm.IsAO2 n D ∧
        (∀ y, circuitFun n D y = decide (∃ p : Fin P, ∃ l : Fin L,
          I p l ∧ y (Fin.castAdd L p) = true ∧ y (Fin.natAdd P l) = true)) ∧
        D.size ≤ C.size ∧ IsReadK n D 2 := by
      refine ⟨leastD.1,?_,leastD.2.2 C ao input_agrees,readD⟩
      intro y
      exact (congrFun leastD.2.1 y).trans (graphFun_eq P L I y)
    by_cases already : IsReadK n B 2
    · exact ⟨B,deliver B best already⟩
    · obtain ⟨D,leastD,pairs⟩ :=
        repair n G B (noFourCycle P L I hC4) ⟨color P L,bipartite P L I⟩ hasEdge best top already
      exact ⟨D,deliver D leastD (graph_reads G leastD.1 leastD.2.1 pairs)⟩
  · refine ⟨C,ao,computes,le_rfl,?_⟩
    intro S prime
    have accepts : graphFun G ∅ (setInput S) = true := by
      rw [← input_agrees]
      exact prime.1
    obtain ⟨u,v,e,_,_⟩ := graph_edge G _ accepts
    exact (hasEdge ⟨s(u,v),SimpleGraph.mem_edgeFinset.mpr e⟩).elim
