import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

-- The agreement and list lookup arguments adapt L_meta_1411 at upstream commit
-- 0a921b61a150ebbb31acd66d8470f49f08876459.
-- A finite separation property excludes every direct input as the second operand.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_3831_1
    (separate : let F : (Fin 9 → Bool) → Bool := fun x => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5;
    ∀ (b : Bool) (k : Fin 9), k ≠ 0 → ∃ x : Fin 9 → Bool,
      x 0 = false ∧ x k = b ∧ F x = false ∧ F (Function.update x 0 true) = true)
    (internal : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (14 : ℕ) → (List.filter (fun (x6 : PEqualNP.CircuitLowerBounds.Gate) => x6.inputs.contains (0 : ℕ)) x1.gates).length = (1 : ℕ) → x2 < x1.gates.length → (0 : ℕ) < x3 → (9 : ℕ) ≤ x3 → x3 < (9 : ℕ) + x2 → (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x2).op = PEqualNP.CircuitLowerBounds.GateOp.or → (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x2).inputs = [(0 : ℕ), x3] → ∃ (x12 : Fin (9 : ℕ) → Bool), (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 fun (x13 : Fin (9 : ℕ)) => if x13 = (0 : Fin (9 : ℕ)) then !x12 (0 : Fin (9 : ℕ)) else x12 x13) ≠ (x12 (0 : Fin (9 : ℕ)) && x12 (1 : Fin (9 : ℕ)) || x12 (1 : Fin (9 : ℕ)) && x12 (2 : Fin (9 : ℕ)) || x12 (2 : Fin (9 : ℕ)) && x12 (3 : Fin (9 : ℕ)) || x12 (3 : Fin (9 : ℕ)) && x12 (4 : Fin (9 : ℕ)) || x12 (4 : Fin (9 : ℕ)) && x12 (0 : Fin (9 : ℕ)) || x12 (0 : Fin (9 : ℕ)) && x12 (5 : Fin (9 : ℕ)) || x12 (1 : Fin (9 : ℕ)) && x12 (6 : Fin (9 : ℕ)) || x12 (2 : Fin (9 : ℕ)) && x12 (7 : Fin (9 : ℕ)) || x12 (3 : Fin (9 : ℕ)) && x12 (8 : Fin (9 : ℕ)) || x12 (5 : Fin (9 : ℕ)) && x12 (7 : Fin (9 : ℕ)) || x12 (6 : Fin (9 : ℕ)) && x12 (8 : Fin (9 : ℕ)) || x12 (8 : Fin (9 : ℕ)) && x12 (5 : Fin (9 : ℕ)))) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (14 : ℕ) → (List.filter (fun (x6 : PEqualNP.CircuitLowerBounds.Gate) => x6.inputs.contains (0 : ℕ)) x1.gates).length = (1 : ℕ) → x2 < x1.gates.length → (0 : ℕ) < x3 → x3 < (9 : ℕ) + x2 → (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x2).op = PEqualNP.CircuitLowerBounds.GateOp.or → (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x2).inputs = [(0 : ℕ), x3] → ∃ (x12 : Fin (9 : ℕ) → Bool), (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 fun (x13 : Fin (9 : ℕ)) => if x13 = (0 : Fin (9 : ℕ)) then !x12 (0 : Fin (9 : ℕ)) else x12 x13) ≠ (x12 (0 : Fin (9 : ℕ)) && x12 (1 : Fin (9 : ℕ)) || x12 (1 : Fin (9 : ℕ)) && x12 (2 : Fin (9 : ℕ)) || x12 (2 : Fin (9 : ℕ)) && x12 (3 : Fin (9 : ℕ)) || x12 (3 : Fin (9 : ℕ)) && x12 (4 : Fin (9 : ℕ)) || x12 (4 : Fin (9 : ℕ)) && x12 (0 : Fin (9 : ℕ)) || x12 (0 : Fin (9 : ℕ)) && x12 (5 : Fin (9 : ℕ)) || x12 (1 : Fin (9 : ℕ)) && x12 (6 : Fin (9 : ℕ)) || x12 (2 : Fin (9 : ℕ)) && x12 (7 : Fin (9 : ℕ)) || x12 (3 : Fin (9 : ℕ)) && x12 (8 : Fin (9 : ℕ)) || x12 (5 : Fin (9 : ℕ)) && x12 (7 : Fin (9 : ℕ)) || x12 (6 : Fin (9 : ℕ)) && x12 (8 : Fin (9 : ℕ)) || x12 (8 : Fin (9 : ℕ)) && x12 (5 : Fin (9 : ℕ))) := by
  let target (x : Fin 9 → Bool) : Bool :=
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
    x 6 && x 8 || x 8 && x 5
  let flip (x : Fin 9 → Bool) (i : Fin 9) : Bool := if i = 0 then !x 0 else x i
  have witnesses : ∀ (b : Bool) (k : Fin 9), k ≠ 0 →
      ∃ x : Fin 9 → Bool, x 0 = false ∧ x k = b ∧ target x = false ∧
        target (Function.update x 0 true) = true := separate
  let wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

  have wires_append (pre post : List Gate) (w : List Bool) :
      wiresFrom (pre ++ post) w = wiresFrom post (wiresFrom pre w) := by
    simp [wiresFrom,List.foldl_append]

  have wires_cons (g : Gate) (gs : List Gate) (w : List Bool) :
      wiresFrom (g :: gs) w = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

  have length_wires (gs : List Gate) (w : List Bool) :
      (wiresFrom gs w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp [wiresFrom]
    | cons g gs ih =>
      simp only [wiresFrom,List.foldl_cons] at ih ⊢
      rw [ih]
      simp
      omega

  have snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
      (L ++ [S]).getD j d = L.getD j d := by
    by_cases hj : j < L.length
    · exact List.getD_append _ _ _ _ hj
    · rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by omega)]

  have snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by simp

  have agree_except (k : ℕ) (gs : List Gate) : ∀ w w' : List Bool,
      (∀ g ∈ gs, k ∉ g.inputs) → w.length = w'.length →
      (∀ j, j ≠ k → w.getD j false = w'.getD j false) →
      ∀ j, j ≠ k → (wiresFrom gs w).getD j false = (wiresFrom gs w').getD j false := by
    induction gs with
    | nil => intro w w' _ _ h; exact h
    | cons g gs ih =>
      intro w w' hno hl h
      have hno' := hno g List.mem_cons_self
      have e : (g.inputs.map fun i => w.getD i false) = g.inputs.map fun i => w'.getD i false :=
        List.map_congr_left (fun a ha => h a (fun e => hno' (e ▸ ha)))
      apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
        (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg')) (by simp [hl])
      intro j hj
      by_cases hjl : j = w.length
      · rw [hjl,snoc_eq,hl,snoc_eq,e]
      · rw [snoc_ne _ _ _ _ hjl,snoc_ne _ _ _ _ (by omega)]
        exact h j hj

  let absorbing : GateOp → Bool := fun op => GateOp.rec false true false (fun _ => false) false op

  have masked_reader (pre post : List Gate) (g : Gate) (k o : ℕ)
      (hop : g.op = .and ∨ g.op = .or) (hin : g.inputs = [0,k])
      (hk : k ≠ 0) (ho : o ≠ 0)
      (hpre : ∀ h ∈ pre, 0 ∉ h.inputs) (hpost : ∀ h ∈ post, 0 ∉ h.inputs)
      (x y : List Bool) (hlen : x.length = y.length)
      (heq : ∀ j, j ≠ 0 → x.getD j false = y.getD j false)
      (hmask : (wiresFrom pre x).getD k false = absorbing g.op) :
      (wiresFrom (pre ++ g :: post) x).getD o false =
        (wiresFrom (pre ++ g :: post) y).getD o false := by
    have same := agree_except 0 pre x y hpre hlen heq
    have hy : (wiresFrom pre y).getD k false = absorbing g.op := (same k hk).symm.trans hmask
    have glen : (wiresFrom pre x).length = (wiresFrom pre y).length := by
      simp only [length_wires,hlen]
    have geq : g.op.eval (g.inputs.map fun j => (wiresFrom pre x).getD j false) =
        g.op.eval (g.inputs.map fun j => (wiresFrom pre y).getD j false) := by
      rcases hop with hop | hop
      · have hx : (wiresFrom pre x).getD k false = false := by simpa only [hop,absorbing] using hmask
        have hy' : (wiresFrom pre y).getD k false = false := by simpa only [hop,absorbing] using hy
        simp only [hin,List.map_cons,List.map_nil,hop]
        change (_ && (_ && true)) = (_ && (_ && true))
        rw [hx,hy']
        simp
      · have hx : (wiresFrom pre x).getD k false = true := by simpa only [hop,absorbing] using hmask
        have hy' : (wiresFrom pre y).getD k false = true := by simpa only [hop,absorbing] using hy
        simp only [hin,List.map_cons,List.map_nil,hop]
        change (_ || (_ || false)) = (_ || (_ || false))
        rw [hx,hy']
        simp
    rw [wires_append,wires_append,wires_cons,wires_cons]
    apply agree_except 0 post _ _ hpost (by simp [glen]) _ o ho
    intro j hj
    by_cases hjl : j = (wiresFrom pre x).length
    · rw [hjl,snoc_eq,glen,snoc_eq,geq]
    · rw [snoc_ne _ _ _ _ hjl,snoc_ne _ _ _ _ (by omega)]
      exact same j hj


  have split_at {α : Type} : ∀ (l : List α) (p : ℕ) (g : α), l[p]? = some g →
      ∃ pre post, l = pre ++ g :: post ∧ pre.length = p := by
    intro l
    induction l with
    | nil => intro p g h; simp at h
    | cons x l ih =>
      intro p g h
      cases p with
      | zero =>
        simp at h
        subst h
        exact ⟨[],l,rfl,rfl⟩
      | succ p =>
        simp at h
        obtain ⟨pre,post,rfl,rfl⟩ := ih p g h
        exact ⟨x :: pre,post,rfl,rfl⟩

  have unique_reader_split (gs : List Gate) (i : ℕ) (g : Gate)
      (hg : gs[i]? = some g) (hread : 0 ∈ g.inputs)
      (hcount : (gs.filter fun h => h.inputs.contains 0).length = 1) :
      ∃ pre post, gs = pre ++ g :: post ∧ pre.length = i ∧
        (∀ h ∈ pre, 0 ∉ h.inputs) ∧ (∀ h ∈ post, 0 ∉ h.inputs) := by
    obtain ⟨pre,post,rfl,hpre⟩ := split_at gs i g hg
    have hr : g.inputs.contains 0 = true := List.contains_iff_mem.mpr hread
    simp only [List.filter_append,List.filter_cons,hr,ite_true,List.length_append,List.length_cons] at hcount
    have hp : (pre.filter fun h => h.inputs.contains 0) = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hq : (post.filter fun h => h.inputs.contains 0) = [] := List.eq_nil_of_length_eq_zero (by omega)
    refine ⟨pre,post,rfl,hpre,?_,?_⟩
    · intro h hh hz
      have hm : h ∈ pre.filter (fun h => h.inputs.contains 0) :=
        List.mem_filter.mpr ⟨hh,List.contains_iff_mem.mpr hz⟩
      rw [hp] at hm
      exact List.not_mem_nil hm
    · intro h hh hz
      have hm : h ∈ post.filter (fun h => h.inputs.contains 0) :=
        List.mem_filter.mpr ⟨hh,List.contains_iff_mem.mpr hz⟩
      rw [hq] at hm
      exact List.not_mem_nil hm
  have original_value (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < w.length) :
      (wiresFrom gs w).getD j false = w.getD j false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [wires_cons,ih _ (by simp; omega)]
      exact List.getD_append _ _ _ _ hj

  have no_correct_raw_reader (C : Circuit) (i k : ℕ)
      (count : (C.gates.filter fun g => g.inputs.contains 0).length = 1)
      (hi : i < C.gates.length) (hk : 0 < k) (hk9 : k < 9)
      (hop : (gateAt C i).op = .and ∨ (gateAt C i).op = .or)
      (hin : (gateAt C i).inputs = [0,k])
      (correct : ∀ x : Fin 9 → Bool, circuitFun 9 C (flip x) = target x) : False := by
    have hget : C.gates[i]? = some (gateAt C i) := by
      change C.gates[i]? = some (C.gates.getD i ⟨GateOp.or,[]⟩)
      rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi]
      rfl
    obtain ⟨pre,post,hgates,hprelen,hpre,hpost⟩ :=
      unique_reader_split C.gates i (gateAt C i) hget (by simp [hin]) count
    have hkn : (⟨k,hk9⟩ : Fin 9) ≠ 0 := by intro h; have := congrArg Fin.val h; simp at this; omega
    obtain ⟨x,hx0,hxk,hfx,hfy⟩ := witnesses (absorbing (gateAt C i).op) ⟨k,hk9⟩ hkn
    let y := Function.update x 0 true
    let xx := List.ofFn (flip x)
    let yy := List.ofFn (flip y)
    have fx : (wiresFrom C.gates xx).getD C.output false = false := (correct x).trans hfx
    have fy : (wiresFrom C.gates yy).getD C.output false = true := (correct y).trans hfy
    have ho : C.output ≠ 0 := by
      intro h
      rw [h,original_value _ _ _ (by simp [xx])] at fx
      change (List.ofFn (flip x)).getD 0 false = false at fx
      rw [List.getD_eq_getElem _ _ (by simp)] at fx
      simp only [List.getElem_ofFn,flip,ite_true,hx0,Bool.not_false] at fx
      cases fx
    have hsame : ∀ j, j ≠ 0 → xx.getD j false = yy.getD j false := by
      intro j hj
      by_cases h9 : j < 9
      · have hne : (⟨j,h9⟩ : Fin 9) ≠ 0 := by intro h; exact hj (congrArg Fin.val h)
        rw [List.getD_eq_getElem _ _ (by simpa [xx] using h9),
          List.getD_eq_getElem _ _ (by simpa [yy] using h9)]
        simp only [xx,yy,List.getElem_ofFn,flip,if_neg hne,y,Function.update_of_ne hne]
      · rw [List.getD_eq_default _ _ (by simp [xx]; omega),
          List.getD_eq_default _ _ (by simp [yy]; omega)]
    have mask : (wiresFrom pre xx).getD k false = absorbing (gateAt C i).op := by
      rw [original_value _ _ _ (by simpa [xx] using hk9)]
      rw [List.getD_eq_getElem _ _ (by simpa [xx] using hk9)]
      simpa only [xx,List.getElem_ofFn,flip,if_neg hkn] using hxk
    have eq := masked_reader pre post (gateAt C i) k C.output hop hin (by omega) ho
      hpre hpost xx yy (by simp [xx,yy]) hsame mask
    rw [hgates] at fx fy
    rw [fx,fy] at eq
    cases eq

  have raw_reader_must_fail (C : Circuit) (i k : ℕ)
      (count : (C.gates.filter fun g => g.inputs.contains 0).length = 1)
      (hi : i < C.gates.length) (hk : 0 < k) (hk9 : k < 9)
      (hop : (gateAt C i).op = .and ∨ (gateAt C i).op = .or)
      (hin : (gateAt C i).inputs = [0,k]) :
      ∃ x : Fin 9 → Bool, circuitFun 9 C (flip x) ≠ target x := by
    by_contra h
    push_neg at h
    exact no_correct_raw_reader C i k count hi hk hk9 hop hin h
  intro C i k hfan hsize hcount hi hk hki hop hin
  by_cases small : k < 9
  · exact raw_reader_must_fail C i k hcount hi hk small hop hin
  · exact internal C i k hfan hsize hcount hi hk (by omega) hki hop hin
