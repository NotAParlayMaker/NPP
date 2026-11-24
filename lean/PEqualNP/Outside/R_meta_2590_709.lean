import Mathlib
import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
-- The orbit table carries a checked relabeling for every possible pair of first-gate inputs.
-- The extra two input symbols stand for a missing wire and a neutral padding value.
set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_2590_709
    (and1 : ∀ (D : Circuit), Monotone2 D → D.size ≤ 18 →
      ∃ y : Bool, ∃ r ∈ (if y then [3,6,12,24,17,33,66,132,264,528,160,640,576,320,288] else [50,69,104,116,138,201,208,276,385,402,521,548,554,770,773] : List ℕ),
        D.eval (List.ofFn (fun i : Fin 11 => if i.val < 10 then r.testBit i.val else
          r.testBit 0 && r.testBit 1)) ≠ y)
    (or1 : ∀ (D : Circuit), Monotone2 D → D.size ≤ 18 →
      ∃ y : Bool, ∃ r ∈ (if y then [3,6,12,24,17,33,66,132,264,528,160,640,576,320,288] else [50,69,104,116,138,201,208,276,385,402,521,548,554,770,773] : List ℕ),
        D.eval (List.ofFn (fun i : Fin 11 => if i.val < 10 then r.testBit i.val else
          r.testBit 0 || r.testBit 1)) ≠ y)
    (or2 : ∀ (D : Circuit), Monotone2 D → D.size ≤ 18 →
      ∃ y : Bool, ∃ r ∈ (if y then [3,6,12,24,17,33,66,132,264,528,160,640,576,320,288] else [50,69,104,116,138,201,208,276,385,402,521,548,554,770,773] : List ℕ),
        D.eval (List.ofFn (fun i : Fin 11 => if i.val < 10 then r.testBit i.val else
          r.testBit 0 || r.testBit 2)) ≠ y) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → x1.size ≤ (19 : ℕ) → ¬∀ (x4 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x4) = (fun (x5 : Fin (10 : ℕ) → Bool) => x5 (0 : Fin (10 : ℕ)) && x5 (1 : Fin (10 : ℕ)) || x5 (1 : Fin (10 : ℕ)) && x5 (2 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ)) && x5 (3 : Fin (10 : ℕ)) || x5 (3 : Fin (10 : ℕ)) && x5 (4 : Fin (10 : ℕ)) || x5 (4 : Fin (10 : ℕ)) && x5 (0 : Fin (10 : ℕ)) || x5 (0 : Fin (10 : ℕ)) && x5 (5 : Fin (10 : ℕ)) || x5 (1 : Fin (10 : ℕ)) && x5 (6 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ)) && x5 (7 : Fin (10 : ℕ)) || x5 (3 : Fin (10 : ℕ)) && x5 (8 : Fin (10 : ℕ)) || x5 (4 : Fin (10 : ℕ)) && x5 (9 : Fin (10 : ℕ)) || x5 (5 : Fin (10 : ℕ)) && x5 (7 : Fin (10 : ℕ)) || x5 (7 : Fin (10 : ℕ)) && x5 (9 : Fin (10 : ℕ)) || x5 (9 : Fin (10 : ℕ)) && x5 (6 : Fin (10 : ℕ)) || x5 (6 : Fin (10 : ℕ)) && x5 (8 : Fin (10 : ℕ)) || x5 (8 : Fin (10 : ℕ)) && x5 (5 : Fin (10 : ℕ))) x4 := by
  have andEq (w : List Bool) : GateOp.and.eval w = w.all id := rfl
  have orEq (w : List Bool) : GateOp.or.eval w = w.any id := rfl
  let rd (w : List Bool) (j : ℕ ⊕ Bool) : Bool := j.elim (fun i => w.getD i false) id
  let refOnly (q : ℕ ⊕ Bool) : Option ℕ := q.elim some (fun _ => none)

  have allAux (w : List Bool) (l : List (ℕ ⊕ Bool)) :
      (l.map (rd w)).all id = if Sum.inr false ∈ l then false else
        ((l.filterMap refOnly).map fun i => w.getD i false).all id := by
    induction l with
    | nil => rfl
    | cons a l ih =>
      cases a with
      | inl j => by_cases h : Sum.inr false ∈ l <;> simp only [List.map_cons,List.all_cons,List.any_cons,List.filterMap_cons,rd,refOnly,Sum.elim_inl,Sum.elim_inr,id_eq,List.mem_cons,Sum.inr.injEq,reduceCtorEq,Bool.false_eq_true,Bool.true_eq_false,h,or_false,or_true,ite_true,ite_false,Bool.and_true,Bool.and_false,Bool.true_and,Bool.false_and,Bool.or_true,Bool.or_false,Bool.true_or,Bool.false_or] at ih ⊢ <;> rw [ih] <;> simp only [List.map_cons,List.all_cons,List.any_cons,id_eq,Bool.true_and,Bool.false_and,Bool.true_or,Bool.false_or,Bool.and_true,Bool.and_false,Bool.or_false,Bool.or_true]
      | inr c => cases c <;> by_cases h : Sum.inr false ∈ l <;> simp only [List.map_cons,List.all_cons,List.any_cons,List.filterMap_cons,rd,refOnly,Sum.elim_inl,Sum.elim_inr,id_eq,List.mem_cons,Sum.inr.injEq,reduceCtorEq,Bool.false_eq_true,Bool.true_eq_false,h,or_false,or_true,ite_true,ite_false,Bool.and_true,Bool.and_false,Bool.true_and,Bool.false_and,Bool.or_true,Bool.or_false,Bool.true_or,Bool.false_or] at ih ⊢ <;> rw [ih] <;> simp only [List.map_cons,List.all_cons,List.any_cons,id_eq,Bool.true_and,Bool.false_and,Bool.true_or,Bool.false_or,Bool.and_true,Bool.and_false,Bool.or_false,Bool.or_true]

  have anyAux (w : List Bool) (l : List (ℕ ⊕ Bool)) :
      (l.map (rd w)).any id = if Sum.inr true ∈ l then true else
        ((l.filterMap refOnly).map fun i => w.getD i false).any id := by
    induction l with
    | nil => rfl
    | cons a l ih =>
      cases a with
      | inl j => by_cases h : Sum.inr true ∈ l <;> simp only [List.map_cons,List.all_cons,List.any_cons,List.filterMap_cons,rd,refOnly,Sum.elim_inl,Sum.elim_inr,id_eq,List.mem_cons,Sum.inr.injEq,reduceCtorEq,Bool.false_eq_true,Bool.true_eq_false,h,or_false,or_true,ite_true,ite_false,Bool.and_true,Bool.and_false,Bool.true_and,Bool.false_and,Bool.or_true,Bool.or_false,Bool.true_or,Bool.false_or] at ih ⊢ <;> rw [ih] <;> simp only [List.map_cons,List.all_cons,List.any_cons,id_eq,Bool.true_and,Bool.false_and,Bool.true_or,Bool.false_or,Bool.and_true,Bool.and_false,Bool.or_false,Bool.or_true]
      | inr c => cases c <;> by_cases h : Sum.inr true ∈ l <;> simp only [List.map_cons,List.all_cons,List.any_cons,List.filterMap_cons,rd,refOnly,Sum.elim_inl,Sum.elim_inr,id_eq,List.mem_cons,Sum.inr.injEq,reduceCtorEq,Bool.false_eq_true,Bool.true_eq_false,h,or_false,or_true,ite_true,ite_false,Bool.and_true,Bool.and_false,Bool.true_and,Bool.false_and,Bool.or_true,Bool.or_false,Bool.true_or,Bool.false_or] at ih ⊢ <;> rw [ih] <;> simp only [List.map_cons,List.all_cons,List.any_cons,id_eq,Bool.true_and,Bool.false_and,Bool.true_or,Bool.false_or,Bool.and_true,Bool.and_false,Bool.or_false,Bool.or_true]

  let isAnd (q : GateOp) : Bool := GateOp.rec (motive := fun _ => Bool) true false false (fun _ => false) false q

  let gate (S : ℕ → ℕ ⊕ Bool) (g : Gate) : Gate :=
    let l := g.inputs.map S
    if isAnd g.op then
      if Sum.inr false ∈ l then ⟨.or,[]⟩ else ⟨.and,l.filterMap refOnly⟩
    else if Sum.inr true ∈ l then ⟨.and,[]⟩ else ⟨.or,l.filterMap refOnly⟩

  have gate_eval (S : ℕ → ℕ ⊕ Bool) (g : Gate) (w : List Bool) (hop : g.op = .and ∨ g.op = .or) :
      (gate S g).op.eval ((gate S g).inputs.map fun j => w.getD j false) =
        g.op.eval ((g.inputs.map S).map (rd w)) := by
    rcases hop with ha | ha
    · have yes : isAnd g.op = true := by rw [ha]
      by_cases h : Sum.inr false ∈ g.inputs.map S
      · have hg : gate S g = ⟨.or,[]⟩ := by simp only [gate,yes,ite_true,ite_eq_left h]
        rw [hg,ha]
        exact ((allAux w (g.inputs.map S)).trans (ite_eq_left h)).symm
      · have hg : gate S g = ⟨.and,(g.inputs.map S).filterMap refOnly⟩ := by simp only [gate,yes,ite_true,ite_eq_right h]
        rw [hg,ha]
        exact ((allAux w (g.inputs.map S)).trans (ite_eq_right h)).symm
    · have no : isAnd g.op = false := by rw [ha]
      by_cases h : Sum.inr true ∈ g.inputs.map S
      · have hg : gate S g = ⟨.and,[]⟩ := by simp only [gate,no,Bool.false_eq_true,ite_false,ite_eq_left h]
        rw [hg,ha]
        exact ((anyAux w (g.inputs.map S)).trans (ite_eq_left h)).symm
      · have hg : gate S g = ⟨.or,(g.inputs.map S).filterMap refOnly⟩ := by simp only [gate,no,Bool.false_eq_true,ite_false,ite_eq_right h]
        rw [hg,ha]
        exact ((anyAux w (g.inputs.map S)).trans (ite_eq_right h)).symm

  have gate_good (S : ℕ → ℕ ⊕ Bool) (g : Gate) (hl : g.inputs.length ≤ 2) :
      (gate S g).op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ (gate S g).inputs.length ≤ 2 := by
    have h := List.length_filterMap_le refOnly (g.inputs.map S)
    simp only [List.length_map] at h
    simp only [gate]
    split <;> split <;> constructor
    all_goals first | exact Or.inl rfl | exact Or.inr rfl | exact h.trans hl | decide

  let WMap {n m : ℕ} (s : Fin n → Fin m ⊕ Bool) (j : ℕ) : ℕ ⊕ Bool :=
    if h : j < n then (s ⟨j,h⟩).map Fin.val id else .inl (j-n+m)

  let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let Rel {n m : ℕ} (s : Fin n → Fin m ⊕ Bool) (v w : List Bool) : Prop :=
    n ≤ v.length ∧ w.length+n=v.length+m ∧ ∀ j, v.getD j false = rd w (WMap s j)

  have initial {n m : ℕ} (s : Fin n → Fin m ⊕ Bool) (x : Fin m → Bool) :
      Rel s (List.ofFn fun i => (s i).elim x id) (List.ofFn x) := by
    refine ⟨by simp, by simp [Nat.add_comm], ?_⟩
    intro j
    by_cases h : j < n
    · rw [List.getD_eq_getElem _ _ (by simpa using h), List.getElem_ofFn]
      cases he : s ⟨j,h⟩ with
      | inl q =>
        simp only [WMap,h, dite_true,he,Sum.map_inl,rd,Sum.elim_inl]
        rw [List.getD_eq_getElem _ _ (by simpa using q.isLt),List.getElem_ofFn]
      | inr b => simp [WMap,h,he,rd]
    · simp only [WMap,h,dite_false,rd,Sum.elim_inl]
      rw [List.getD_eq_default _ _ (by simp <;> omega),List.getD_eq_default _ _ (by simp <;> omega)]

  have next {n m : ℕ} (s : Fin n → Fin m ⊕ Bool) (v w : List Bool) (h : Rel s v w)
      (g : Gate) (hop : g.op = .and ∨ g.op = .or) :
      Rel s (step v g) (step w (gate (WMap s) g)) := by
    obtain ⟨h1,h2,h3⟩ := h
    let val := g.op.eval (g.inputs.map fun j => v.getD j false)
    have same : (gate (WMap s) g).op.eval ((gate (WMap s) g).inputs.map fun j => w.getD j false) = val := by
      rw [gate_eval _ _ _ hop]
      simp only [val,List.map_map]
      congr 1
      exact List.map_congr_left (fun j _ => (h3 j).symm)
    refine ⟨by simp [step]; omega, by simp [step];omega, ?_⟩
    intro j
    change (v ++ [val]).getD j false = rd (w ++ [_]) (WMap s j)
    rw [same]
    by_cases hj : j < n
    · rw [List.getD_append _ _ _ _ (by omega)]
      rw [h3]
      simp only [WMap,hj,dite_true]
      cases he : s ⟨j,hj⟩ with
      | inl q =>
        simp only [Sum.map_inl,rd,Sum.elim_inl]
        rw [List.getD_append _ _ _ _ (by have := q.isLt; omega)]
      | inr b => rfl
    · simp only [WMap,hj,dite_false,rd,Sum.elim_inl]
      rcases Nat.lt_trichotomy j v.length with hlt | heq | hgt
      · rw [List.getD_append _ _ _ _ hlt,List.getD_append _ _ _ _ (by omega)]
        simpa [WMap,hj,rd] using h3 j
      · have h' : j-n+m=w.length := by omega
        rw [h',heq]
        simp
      · rw [List.getD_eq_default _ _ (by simp <;> omega),List.getD_eq_default _ _ (by simp <;> omega)]

  have evalFold {n m : ℕ} (s : Fin n → Fin m ⊕ Bool) (gs : List Gate)
      (good : ∀ g ∈ gs, g.op = .and ∨ g.op = .or) :
      ∀ v w, Rel s v w → Rel s (gs.foldl step v) ((gs.map (gate (WMap s))).foldl step w) := by
    induction gs with
    | nil => exact fun _ _ h => h
    | cons g gs ih =>
      intro v w h
      exact ih (fun t ht => good t (by simp [ht])) _ _ (next s v w h g (good g (by simp)))

  have substInputs : ∀ (n m : ℕ) (D : Circuit) (s : Fin n → Fin m ⊕ Bool), Monotone2 D →
        let f := fun (x : Fin m → Bool) => D.eval (List.ofFn fun i => (s i).elim x id)
        (∃ x y, f x ≠ f y) → ∃ E : Circuit, Monotone2 E ∧ E.size ≤ D.size ∧
          ∀ x : Fin m → Bool, E.eval (List.ofFn x) = f x := by
    intro n m D s hm f hnc
    let gs := D.gates.map (gate (WMap s))
    have out (x : Fin m → Bool) : f x = rd (gs.foldl step (List.ofFn x)) (WMap s D.output) := by
      exact (evalFold s D.gates (fun g hg => by simpa using (hm g hg).1) _ _ (initial s x)).2.2 D.output
    cases he : WMap s D.output with
    | inl q =>
      refine ⟨⟨gs,q⟩,?_,?_,?_⟩
      · intro g hg
        obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hg
        exact gate_good _ _ (hm u hu).2
      · change (D.gates.map _).length ≤ D.gates.length
        rw [List.length_map]
      · intro x
        change (gs.foldl step (List.ofFn x)).getD q false = f x
        simpa only [he,rd,Sum.elim_inl] using (out x).symm
    | inr b =>
      obtain ⟨x,y,h⟩ := hnc
      exact (h (by simp [out,he,rd])).elim
  -- An AND of two nonadjacent vertices is false on every minimal positive row.
  -- Replacing that signal by false preserves the positives and only decreases negative outputs.
  have evaluation (D : Circuit) (hm : Monotone2 D) (u v : Fin 11 → Bool)
      (le : ∀ i, u i = true → v i = true) :
      D.eval (List.ofFn u) = true → D.eval (List.ofFn v) = true := by
    let Le (x y : List Bool) := ∀ j, x.getD j false = true → y.getD j false = true
    have snoc (xs : List Bool) (v : Bool) : (xs ++ [v]).getD xs.length false = v := by simp
    have stepLe (g : Gate) (hop : g.op = .and ∨ g.op = .or) (x y : List Bool) (hl : x.length = y.length) (h : Le x y) :
        Le (step x g) (step y g) := by
      intro j hj
      by_cases hlt : j < x.length
      · unfold step at hj ⊢
        rw [List.getD_append _ _ _ _ hlt] at hj
        rw [List.getD_append _ _ _ _ (hl ▸ hlt)]
        exact h j hj
      by_cases he : j = x.length
      · have hy : j = y.length := he.trans hl
        simp only [step,he,snoc] at hj
        simp only [step,hy,snoc]
        rcases hop with ho | ho <;> rw [ho] at hj ⊢ <;> simp [andEq,orEq] at hj ⊢
        · exact fun i hi => h i (hj i hi)
        · obtain ⟨i,hi,hv⟩ := hj
          exact ⟨i,hi,h i hv⟩
      · rw [List.getD_eq_default _ _ (by simp [step]; omega)] at hj
        contradiction
    have foldLe (gs : List Gate) (good : ∀ g ∈ gs, g.op = .and ∨ g.op = .or) :
        ∀ x y : List Bool, x.length = y.length → Le x y → Le (gs.foldl step x) (gs.foldl step y) := by
      induction gs with
      | nil => exact fun _ _ _ h => h
      | cons g gs ih =>
        intro x y hl h
        exact ih (fun t ht => good t (by simp [ht])) _ _ (by simp [step,hl]) (stepLe _ (good _ (by simp)) _ _ hl h)
    apply foldLe D.gates (fun g hg => by simpa using (hm g hg).1) _ _ (by simp) _ D.output
    intro j h
    by_cases hj : j < 11
    · rw [List.getD_eq_getElem _ _ (by simpa using hj),List.getElem_ofFn] at h ⊢
      exact le _ h
    · rw [List.getD_eq_default _ _ (by simp;omega)] at h
      contradiction
  have and2 : ∀ (D : Circuit), Monotone2 D → D.size ≤ 18 →
      ∃ y : Bool, ∃ r ∈ (if y then [3,6,12,24,17,33,66,132,264,528,160,640,576,320,288] else [50,69,104,116,138,201,208,276,385,402,521,548,554,770,773] : List ℕ),
        D.eval (List.ofFn (fun i : Fin 11 => if i.val < 10 then r.testBit i.val else
          r.testBit 0 && r.testBit 2)) ≠ y := by
    intro D hm hs
    let pos := ([3,6,12,24,17,33,66,132,264,528,160,640,576,320,288] : List ℕ)
    let neg := ([50,69,104,116,138,201,208,276,385,402,521,548,554,770,773] : List ℕ)
    let v (d r : ℕ) (i : Fin 11) := if i.val < 10 then r.testBit i.val else r.testBit 0 && r.testBit d
    let z (r : ℕ) (i : Fin 11) := if i.val < 10 then r.testBit i.val else false
    let s (i : Fin 11) : Fin 11 ⊕ Bool := if i.val < 10 then .inl i else .inr false
    by_contra! correct
    have correct' (y : Bool) (r : ℕ) (hr : r ∈ (if y then pos else neg)) : D.eval (List.ofFn (v 2 r)) = y := correct y r hr
    have cleaned (y : Bool) (r : ℕ) (hr : r ∈ (if y then pos else neg)) : D.eval (List.ofFn (z r)) = y := by
      cases y with
      | true =>
        have all0 : ∀ r ∈ pos, (r.testBit 0 && r.testBit 2) = false := by decide
        have eq : z r = v 2 r := by funext i; simp only [z,v,all0 r hr]
        rw [eq]
        exact correct' true r hr
      | false =>
        cases hh : D.eval (List.ofFn (z r)) with
        | false => rfl
        | true =>
          have le (i : Fin 11) : z r i = true → v 2 r i = true := by by_cases h : i.val < 10 <;> simp [z,v,h]
          have h := evaluation D hm _ _ le hh
          rw [correct' false r hr] at h
          contradiction
    have sub (d r : ℕ) : (fun i => (s i).elim (v d r) id) = z r := by
      funext i
      by_cases h : i.val < 10 <;> simp [s,v,z,h]
    have vary : ∃ x y : Fin 11 → Bool,
        D.eval (List.ofFn fun i => (s i).elim x id) ≠ D.eval (List.ofFn fun i => (s i).elim y id) := by
      refine ⟨v 1 3,v 1 50,?_⟩
      rw [sub,sub,cleaned true 3 (by decide),cleaned false 50 (by decide)]
      decide
    obtain ⟨E,hmE,hsE,he⟩ := substInputs 11 11 D s hm vary
    obtain ⟨y,r,hr,bad⟩ := and1 E hmE (hsE.trans hs)
    apply bad
    change E.eval (List.ofFn (v 1 r)) = y
    rw [he]
    change D.eval (List.ofFn fun i => (s i).elim (v 1 r) id) = y
    rw [sub]
    exact cleaned y r hr
  have fourSuffixes : ∀ (D : Circuit) (o : Bool) (d : Fin 10), Monotone2 D → D.size ≤ 18 → (d = 1 ∨ d = 2) →
      ∃ y : Bool, ∃ r ∈ (if y then [3,6,12,24,17,33,66,132,264,528,160,640,576,320,288] else [50,69,104,116,138,201,208,276,385,402,521,548,554,770,773] : List ℕ),
        D.eval (List.ofFn (fun i : Fin 11 => if i.val < 10 then r.testBit i.val else
          if o then r.testBit 0 && r.testBit d.val else r.testBit 0 || r.testBit d.val)) ≠ y := by
    intro D o d hm hs hd
    rcases hd with rfl | rfl <;> cases o
    · exact or1 D hm hs
    · exact and1 D hm hs
    · exact or2 D hm hs
    · exact and2 D hm hs
  let F := fun (x : Fin 10 → Bool) => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)
  let rows (y : Bool) := (if y then [3,6,12,24,17,33,66,132,264,528,160,640,576,320,288] else [50,69,104,116,138,201,208,276,385,402,521,548,554,770,773] : List ℕ)
  let P : List (List (Fin 10)) := [
    [0,1,2,3,4,5,6,7,8,9],
    [1,2,3,4,0,6,7,8,9,5],
    [1,2,3,8,6,0,7,4,5,9],
    [2,1,6,8,3,7,0,9,5,4],
    [2,3,4,0,1,7,8,9,5,6],
    [2,3,4,9,7,1,8,0,6,5],
    [2,3,8,5,7,1,4,6,0,9],
    [2,3,8,6,1,7,4,5,9,0],
    [3,4,0,1,2,8,9,5,6,7],
    [4,0,1,2,3,9,5,6,7,8],
    [3,2,1,6,8,4,7,0,9,5],
    [3,2,7,5,8,4,1,9,0,6],
    [3,2,7,9,4,8,1,5,6,0],
    [3,8,5,0,4,2,6,7,1,9],
    [3,8,5,7,2,4,6,0,9,1],
    [1,6,8,3,2,0,9,5,4,7],
    [3,4,0,5,8,2,9,1,7,6],
    [3,4,9,6,8,2,0,7,1,5],
    [3,4,9,7,2,8,0,6,5,1],
    [3,8,6,1,2,4,5,9,0,7],
    [3,8,6,9,4,2,5,1,7,0],
    [6,1,0,4,9,8,2,5,3,7],
    [6,8,3,2,1,9,5,4,7,0],
    [6,8,3,4,9,1,5,2,0,7],
    [8,3,2,1,6,5,4,7,0,9],
    [8,3,2,7,5,6,4,1,9,0],
    [8,3,4,0,5,6,2,9,1,7],
    [8,3,4,9,6,5,2,0,7,1],
    [8,6,1,0,5,3,9,2,4,7],
    [8,6,9,4,3,5,1,7,0,2]]
  let perm (p : Fin 30) (i : Fin 10) := (P.getD p.val []).getD i.val 0
  let T : List (Fin 30 × Fin 10 × Fin 13 × Fin 13) := [
    (0,1,0,0),(0,1,10,10),(0,2,10,10),(4,2,10,10),(1,1,10,10),(2,1,10,10),(3,2,10,10),(5,2,10,10),(6,2,10,10),(7,2,10,10),(0,1,11,0),(0,1,0,12),
    (0,1,10,10),(9,1,0,0),(9,1,10,10),(9,2,10,10),(1,2,10,10),(2,2,10,10),(3,1,10,10),(10,2,10,10),(11,2,10,10),(12,2,10,10),(9,1,11,0),(9,1,0,12),
    (0,2,10,10),(9,1,10,10),(8,1,0,0),(8,1,10,10),(8,2,10,10),(16,2,10,10),(21,2,10,10),(10,1,10,10),(24,2,10,10),(25,2,10,10),(8,1,11,0),(8,1,0,12),
    (4,2,10,10),(9,2,10,10),(8,1,10,10),(4,1,0,0),(4,1,10,10),(13,2,10,10),(26,2,10,10),(28,2,10,10),(13,1,10,10),(22,2,10,10),(4,1,11,0),(4,1,0,12),
    (1,1,10,10),(1,2,10,10),(8,2,10,10),(4,1,10,10),(1,1,0,0),(15,2,10,10),(18,2,10,10),(14,2,10,10),(19,2,10,10),(7,1,10,10),(1,1,11,0),(1,1,0,12),
    (2,1,10,10),(2,2,10,10),(16,2,10,10),(13,2,10,10),(15,2,10,10),(2,1,0,0),(17,2,10,10),(5,1,10,10),(6,1,10,10),(20,2,10,10),(2,1,11,0),(2,1,0,12),
    (3,2,10,10),(3,1,10,10),(21,2,10,10),(26,2,10,10),(18,2,10,10),(17,2,10,10),(3,1,0,0),(27,2,10,10),(11,1,10,10),(12,1,10,10),(3,1,11,0),(3,1,0,12),
    (5,2,10,10),(10,2,10,10),(10,1,10,10),(28,2,10,10),(14,2,10,10),(5,1,10,10),(27,2,10,10),(5,1,0,0),(23,2,10,10),(14,1,10,10),(5,1,11,0),(5,1,0,12),
    (6,2,10,10),(11,2,10,10),(24,2,10,10),(13,1,10,10),(19,2,10,10),(6,1,10,10),(11,1,10,10),(23,2,10,10),(6,1,0,0),(29,2,10,10),(6,1,11,0),(6,1,0,12),
    (7,2,10,10),(12,2,10,10),(25,2,10,10),(22,2,10,10),(7,1,10,10),(20,2,10,10),(12,1,10,10),(14,1,10,10),(29,2,10,10),(7,1,0,0),(7,1,11,0),(7,1,0,12),
    (0,1,11,0),(9,1,11,0),(8,1,11,0),(4,1,11,0),(1,1,11,0),(2,1,11,0),(3,1,11,0),(5,1,11,0),(6,1,11,0),(7,1,11,0),(0,1,11,11),(0,1,11,12),
    (0,1,0,12),(9,1,0,12),(8,1,0,12),(4,1,0,12),(1,1,0,12),(2,1,0,12),(3,1,0,12),(5,1,0,12),(6,1,0,12),(7,1,0,12),(0,1,11,12),(0,1,12,12)]
  let cert (a b : Fin 12) := T.getD (12*a.val+b.val) (0,1,0,0)
  let op (o u v : Bool) := if o then u && v else u || v
  let atom (x : Fin 10 → Bool) (i : Fin 12) := if hi : i.val < 10 then x ⟨i.val,hi⟩ else decide (i.val = 11)
  let vec (r : ℕ) (o : Bool) (d : Fin 10) (i : Fin 11) := if i.val < 10 then r.testBit i.val else op o (r.testBit 0) (r.testBit d.val)
  let sig (p : Fin 30) (k : Fin 13) (j : Fin 11) : Fin 11 ⊕ Bool :=
    if hj : j.val < 10 then .inl ⟨(perm p ⟨j.val,hj⟩).val, by have := (perm p ⟨j.val,hj⟩).isLt; omega⟩
    else if hk : k.val < 11 then .inl ⟨k.val,hk⟩ else .inr (decide (k.val = 12))
  have labels : ∀ p : Fin 30, ∀ y : Bool, ∀ r ∈ rows y, F (fun i => r.testBit (perm p i).val) = y := by decide +kernel
  have widths : ∀ a b, (cert a b).2.1 = 1 ∨ (cert a b).2.1 = 2 := by decide +kernel
  have encoding : ∀ (a b : Fin 12) (o : Bool) (y : Bool), ∀ r ∈ rows y,
      let t := cert a b
      let k := if o then t.2.2.1 else t.2.2.2
      let x : Fin 10 → Bool := fun i => r.testBit (perm t.1 i).val
      ((sig t.1 k 10).elim (vec r o t.2.1) id) = op o (atom x a) (atom x b) := by decide +kernel
  intro C mono size computes
  obtain ⟨gs,out⟩ := C
  cases gs with
  | nil =>
    have val (r : ℕ) := computes (fun i => r.testBit i.val)
    by_cases ho : out < 10
    · interval_cases out <;> first | exact (by decide : ¬ _) (val 3) | exact (by decide : ¬ _) (val 12)
    · have bad := val 3
      change (List.ofFn (fun i : Fin 10 => (3 : ℕ).testBit i.val)).getD out false = true at bad
      rw [List.getD_eq_default _ _ (by simpa using ho)] at bad
      contradiction
  | cons g gs =>
    let D : Circuit := ⟨gs,out⟩
    have hm : Monotone2 D := fun t ht => mono t (List.mem_cons_of_mem _ ht)
    have hs : D.size ≤ 18 := by
      change gs.length ≤ 18
      change (g :: gs).length ≤ 19 at size
      simp only [List.length_cons] at size
      omega
    obtain ⟨hop,hlen⟩ := mono g List.mem_cons_self
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    let o : Bool := GateOp.rec (motive := fun _ => Bool) true false false (fun _ => false) false g.op
    let sy (j : ℕ) : Fin 12 := if hj : j < 10 then ⟨j,by omega⟩ else 10
    let neutral : Fin 12 := if o then 11 else 10
    let a := (g.inputs.map sy).getD 0 neutral
    let b := (g.inputs.map sy).getD 1 neutral
    let t := cert a b
    let d := t.2.1
    let k := if o then t.2.2.1 else t.2.2.2
    let s := sig t.1 k
    have lookup (x : Fin 10 → Bool) (j : ℕ) :
        (List.ofFn x).getD j false = atom x (sy j) := by
      by_cases hj : j < 10
      · rw [List.getD_eq_getElem _ _ (by simpa using hj)]
        rw [List.getElem_ofFn]
        simp [atom,sy,hj]
      · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hj)]
        simp [atom,sy,hj]
    have first (x : Fin 10 → Bool) :
        g.op.eval (g.inputs.map fun j => (List.ofFn x).getD j false) =
          op o (atom x a) (atom x b) := by
      have shapes : g.inputs = [] ∨ (∃ j, g.inputs = [j]) ∨ ∃ j l, g.inputs = [j,l] := by
        cases he : g.inputs with
        | nil => simp
        | cons j js =>
          cases js with
          | nil => simp
          | cons l rest =>
            have hz : rest.length = 0 := by simpa [he] using hlen
            simp [List.length_eq_zero_iff.mp hz]
      rcases shapes with h | ⟨j,h⟩ | ⟨j,l,h⟩ <;> rcases hop with ha | ha <;>
        simp only [h,List.map_cons,List.map_nil,List.getD_cons_zero,List.getD_cons_succ,List.getD_nil,
          a,b,neutral,o,ha,op,andEq,orEq,List.all_cons,List.all_nil,List.any_cons,List.any_nil,
          lookup,id_eq,Bool.and_true,Bool.or_false] <;> simp [atom]
    have transported (y : Bool) (r : ℕ) (hr : r ∈ rows y) :
        D.eval (List.ofFn fun i => (s i).elim (vec r o d) id) = y := by
      let x : Fin 10 → Bool := fun i => r.testBit (perm t.1 i).val
      have endVal := encoding a b o y r hr
      change ((s 10).elim (vec r o d) id) = op o (atom x a) (atom x b) at endVal
      have eqInputs : (List.ofFn fun i => (s i).elim (vec r o d) id) =
          List.ofFn x ++ [g.op.eval (g.inputs.map fun j => (List.ofFn x).getD j false)] := by
        apply List.ext_getElem
        · simp
        · intro j hj hj'
          rw [List.getElem_ofFn]
          by_cases h : j < 10
          · rw [List.getElem_append_left (by simpa using h), List.getElem_ofFn]
            simp [s,sig,h,vec,x,show (perm t.1 ⟨j,h⟩).val < 10 from (perm t.1 ⟨j,h⟩).isLt]
          · have he : j = 10 := by simp at hj; omega
            subst j
            rw [List.getElem_append_right (by simp)]
            simp only [List.length_ofFn, Nat.sub_self, List.getElem_cons_zero, first]
            rw [show (⟨10,by decide⟩ : Fin 11) = 10 by decide]
            exact endVal
      rw [eqInputs]
      exact (computes x).trans (labels t.1 y r hr)
    have vary : ∃ x y : Fin 11 → Bool,
        D.eval (List.ofFn fun i => (s i).elim x id) ≠ D.eval (List.ofFn fun i => (s i).elim y id) := by
      refine ⟨vec 3 o d, vec 50 o d, ?_⟩
      rw [transported true 3 (by decide), transported false 50 (by decide)]
      decide
    obtain ⟨E, hmE, hsE, heq⟩ := substInputs 11 11 D s hm vary
    obtain ⟨y,r,hr,bad⟩ := fourSuffixes E o d hmE (hsE.trans hs) (widths a b)
    exact bad ((heq (vec r o d)).trans (transported y r hr))
