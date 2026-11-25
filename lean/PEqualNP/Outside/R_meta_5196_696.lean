import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Insert the pivot mask at its causal position; the two distinguished raw
-- inputs then have singleton read channels. The seeded binary-gate bound
-- (L-meta-4308) leaves at most one NOT. On the 6=0 cofactor, L-meta-3143
-- leaves room to eliminate at most one gate, even with a free negated input.
-- Mask simulation adapted from the final simulation in meteorite6's PR #10524.
set_option maxRecDepth 3000 in
set_option maxHeartbeats 1800000 in
theorem PEqualNP.Outside.R_meta_5196_696
    (literal : ∀ (x1 : Fin (8 : ℕ)) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → (∀ (x4 : Fin (8 : ℕ) → Bool), x2.eval (List.ofFn x4 ++ [!x4 x1, Bool.true, Bool.false]) = (fun (x5 : Fin (8 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (4 : ℕ), (15 : ℕ), (26 : ℕ), (37 : ℕ), (46 : ℕ), (57 : ℕ), (74 : ℕ)].any fun (x6 : ℕ) => x5 (Fin.ofNat (8 : ℕ) (x6 / (10 : ℕ))) && x5 (Fin.ofNat (8 : ℕ) (x6 % (10 : ℕ)))) x4) → (13 : ℕ) ≤ x2.size)
    (binary : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x3 ++ [x3 (0 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ))]) = (x3 (0 : Fin (9 : ℕ)) && x3 (1 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (2 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (3 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (4 : Fin (9 : ℕ)) || x3 (4 : Fin (9 : ℕ)) && x3 (0 : Fin (9 : ℕ)) || x3 (0 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (6 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (5 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (8 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ)))) → (13 : ℕ) ≤ List.countP (fun (x4 : PEqualNP.CircuitLowerBounds.Gate) => !x4.op.eval [Bool.false]) x1.gates)
    (hard : ∀ (D : Circuit) (v : Fin 9) (k : ℕ),
      let w := fun (y : Fin 8 → Bool) (u : Bool) => [y 1,y 0,y 4,y 7,y 5,y 2,u,y 6,y 3,y 1 || u]
      let V := fun i y => (D.wires (w y false)).getD i false
      FanInTwo D → D.size = 14 → 12 < D.gates.countP (fun g => !g.op.eval [false]) →
      v ≠ 0 → v ≠ 6 → 10 ≤ k →
      (D.gates.filter (fun g => g.inputs.contains v.val)).map Gate.inputs = [[v.val,k]] →
      (D.gates.filter (fun (g : Gate) => (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains 6)).map Gate.op = [.or] →
      (∀ (t : Fin 8) (T : Finset ℕ), let z := fun y : Fin 8 → Bool => List.ofFn y ++ [!y t,true,false]
        (∀ i ∈ T, 10 ≤ i ∧ i < 24 ∧ ((∃ j < i, V i = V j) ∨ ∃ a, V i = fun y => (z y).getD a false)) → T.card ≤ 1) →
      ∃ (y : Fin 8 → Bool) (u : Bool), D.eval (w y u) ≠ ((115792089237316195379631272860981142487703928461450370304571918768505461864648 : ℕ).testBit (tableIndex y) || (u && (y 0 || y 3)))) :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); have x2 : (Fin (9 : ℕ) → Bool) → List Bool := fun (x2 : Fin (9 : ℕ) → Bool) => List.ofFn x2 ++ [x2 (0 : Fin (9 : ℕ)) || x2 (6 : Fin (9 : ℕ))]; have x3 : ℕ → PEqualNP.CircuitLowerBounds.Gate → Bool := fun (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x4.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x4.inputs).contains x3; ∀ (x4 : Fin (9 : ℕ)) (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : ℕ) (x7 : Bool),   x4 ≠ (0 : Fin (9 : ℕ)) →     x4 ≠ (6 : Fin (9 : ℕ)) →       PEqualNP.MetaComplexity.FanInTwo x5 →         x5.size = (13 : ℕ) →           (10 : ℕ) ≤ x6 →             x6 < (23 : ℕ) →               (∀ x14 ∈ List.take (x6 + (1 : ℕ) - (10 : ℕ)) x5.gates, ↑x4 ∉ x14.inputs) →                 (∀ (x15 x16 : Fin (9 : ℕ) → Bool), (∀ (x17 : Fin (9 : ℕ)), x17 ≠ x4 → x15 x17 = x16 x17) → x1 x15 ≠ x1 x16 → (x5.wires (x2 x15)).getD x6 Bool.false = !x7) →                   (∃ x16 ∈ x5.gates, x3 (9 : ℕ) x16 = Bool.true) →                     (∃ (x17 : PEqualNP.CircuitLowerBounds.Gate), x17.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (∃ x18 ∉ [(0 : ℕ), (6 : ℕ), (9 : ℕ)], x17.inputs = [(6 : ℕ), x18] ∨ x17.inputs = [x18, (6 : ℕ)]) ∧ List.filter (x3 (6 : ℕ)) x5.gates = [x17]) →                       (∃ (x18 : Fin (9 : ℕ) → Bool), x18 (6 : Fin (9 : ℕ)) = Bool.false ∧ (x5.wires (x2 x18)).getD x6 Bool.false = x7) →                         ∃ (x19 : Fin (9 : ℕ) → Bool),                           have x20 : Bool := (x5.wires (x2 x19)).getD x6 Bool.false;                           x5.eval ((x2 x19).set (↑x4) (if x7 = Bool.true then x19 x4 || x20 else x19 x4 && x20)) ≠ x1 x19 := by
  have compiler : ∀ (D : Circuit) (t : Fin 8) (T : Finset ℕ),
      let w := fun y : Fin 8 → Bool => [y 1,y 0,y 4,y 7,y 5,y 2,false,y 6,y 3,y 1]
      let z := fun y : Fin 8 → Bool => List.ofFn y ++ [!y t,true,false]
      let V := fun i y => (D.wires (w y)).getD i false
      FanInTwo D → (∀ i ∈ T, 10 ≤ i ∧ i < 10 + D.size ∧ ((∃ j < i, V i = V j) ∨ ∃ a, V i = fun y => (z y).getD a false)) →
      ∃ E : Circuit, FanInTwo E ∧ E.size + T.card ≤ D.size ∧
        ∀ y, E.eval (z y) = D.eval (w y) := by
    let X := Fin 8 → Bool
    let Row := X → List Bool
    let OK (g : Gate) := g.op ∈ ({.and,.or,.not} : Set GateOp) ∧ g.inputs.length ≤ 2
    let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    let run (gs : List Gate) (w : List Bool) := gs.foldl step w
    let atWire (w : Row) (i : ℕ) := fun x => (w x).getD i false
    let finish (gs : List Gate) (w : Row) := fun x => run gs (w x)
    let repr (w : Row) (m : ℕ) (f : X → Bool) := ∃ j < m, f = atWire w j
    have pref (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
        (run gs w).getD i false = w.getD i false := by
      induction gs generalizing w with
      | nil => rfl
      | cons g gs ih =>
        change (run gs (step w g)).getD i false = _
        rw [ih _ (by simp [step]; omega)]
        exact List.getD_append _ _ _ _ hi

    have compile (gs : List Gate) (z w d : Row) (n m : ℕ) (T : Finset ℕ)
        (legal : ∀ g ∈ gs, OK g)
        (hw : ∀ x, (w x).length = n) (hd : ∀ x, (d x).length = m)
        (bank : ∀ i, repr d m (atWire w i)) (base : ∀ i, repr d m (atWire z i))
        (nul : repr d m (fun _ => false))
        (dup : ∀ i ∈ T, n ≤ i ∧ i < n+gs.length ∧
          ((∃ j < i, atWire (finish gs w) i = atWire (finish gs w) j) ∨
            ∃ j, atWire (finish gs w) i = atWire z j)) :
        ∃ E : List Gate, (∀ g ∈ E, OK g) ∧ E.length + T.card ≤ gs.length ∧
          ∀ i, ∃ j, atWire (finish gs w) i = atWire (finish E d) j := by
      classical
      induction gs generalizing w d n m T with
      | nil =>
        have empty : T = ∅ := Finset.eq_empty_iff_forall_notMem.mpr fun i h => by
          have e := dup i h; simp at e; omega
        refine ⟨[],by simp,by simp [empty],?_⟩
        intro i
        obtain ⟨j,_,h⟩ := bank i
        exact ⟨j,h⟩
      | cons g gs ih =>
        let f := fun x => g.op.eval (g.inputs.map fun i => (w x).getD i false)
        let w' : Row := fun x => (w x) ++ [f x]
        have lw' : ∀ x, (w' x).length = n+1 := by simp [w',hw]
        have last : atWire (finish (g::gs) w) n = f := by
          funext x
          change (run gs (w' x)).getD n false = _
          rw [pref _ _ _ (by rw [lw']; omega)]
          simp [w',←hw x]
        have avoid (hn : n ∈ T) : repr d m f := by
          rcases (dup n hn).2.2 with ⟨j,hj,e⟩ | ⟨j,e⟩
          · have p : atWire (finish (g::gs) w) j = atWire w j :=
              funext fun x => pref _ _ _ (by simpa [hw] using hj)
            rw [←last,e,p]; exact bank j
          · rw [←last,e]; exact base j
        have saved : ∃ a : List Gate, (∀ q ∈ a, OK q) ∧
            a.length + (if n ∈ T then 1 else 0) ≤ 1 ∧ repr (finish a d) (m+a.length) f ∧
            (∀ x, (finish a d x).length = m+a.length) := by
          by_cases hn : n ∈ T
          · exact ⟨[],by simp,by simp [hn],avoid hn,hd⟩
          choose s hs he using bank
          let q : Gate := ⟨g.op,g.inputs.map s⟩
          have lq : OK q := ⟨(legal g List.mem_cons_self).1,by simpa [q] using (legal g List.mem_cons_self).2⟩
          refine ⟨[q],fun r h => List.mem_singleton.mp h ▸ lq,by simp [hn],⟨m,by simp,?_⟩,?_⟩
          · funext x
            change f x = ((d x) ++ [q.op.eval (q.inputs.map fun i => (d x).getD i false)]).getD m false
            rw [←hd x]; simp only [List.getD_append_right,le_refl,Nat.sub_self,List.getD_cons_zero]
            dsimp only [f,q]
            rw [List.map_map]
            congr 1
            exact List.map_congr_left fun i _ => congrFun (he i) x
          · intro x
            change ((d x) ++ [_]).length = _
            simp [hd]
        obtain ⟨a,legalA,budget,fa,la⟩ := saved
        have keep {v} (hv : repr d m v) : repr (finish a d) (m+a.length) v := by
          obtain ⟨j,hj,rfl⟩ := hv
          exact ⟨j,by omega,funext fun x => (pref a (d x) j (by simpa [hd] using hj)).symm⟩
        have next (i : ℕ) : repr (finish a d) (m+a.length) (atWire w' i) := by
          rcases lt_trichotomy i n with h|rfl|h
          · have e : atWire w' i = atWire w i :=
              funext fun x => List.getD_append _ _ _ _ (by simpa [hw] using h)
            rw [e]; exact keep (bank i)
          · have e : atWire w' i = f := funext fun x => by simp [atWire,w',←hw x]
            rw [e]; exact fa
          · have e : atWire w' i = fun _ => false :=
              funext fun x => List.getD_eq_default _ _ (by rw [lw']; omega)
            rw [e]; exact keep nul
        obtain ⟨tail,ltail,btail,out⟩ := ih w' (finish a d) (n+1) (m+a.length) (T.erase n)
          (fun q h => legal q (List.mem_cons_of_mem _ h)) lw' la next (fun i => keep (base i)) (keep nul)
          (by
            intro i hi
            obtain ⟨ne,hm⟩ := Finset.mem_erase.mp hi
            obtain ⟨low,high,same⟩ := dup i hm
            refine ⟨by omega,by simp at high; omega,same⟩)
        refine ⟨a++tail,?_,?_,?_⟩
        · intro q h
          rcases List.mem_append.mp h with h|h
          · exact legalA q h
          · exact ltail q h
        · simp only [List.length_append,List.length_cons]
          by_cases hn : n ∈ T
          · have := Finset.card_erase_add_one hn; rw [if_pos hn] at budget; omega
          · rw [Finset.erase_eq_of_notMem hn] at btail; rw [if_neg hn] at budget; omega
        · intro i
          obtain ⟨j,e⟩ := out i
          refine ⟨j,?_⟩
          change atWire (finish gs w') i = _
          rw [e]
          funext x
          change ((tail.foldl step (a.foldl step (d x))).getD j false) =
            (((a++tail).foldl step (d x)).getD j false)
          rw [List.foldl_append]

    intro D t T w z V legal dup
    have lz : ∀ x, (z x).length = 11 := by simp [z]
    have read (j : Fin 8) (x : X) : (z x).getD j.val false = x j := by
      rw [List.getD_append _ _ _ _ (by simpa using j.isLt : j.val < (List.ofFn x).length)]
      change (List.ofFn x).getD j.val false = x j
      rw [List.getD_eq_getElem _ _ (by simpa using j.isLt),List.getElem_ofFn]
    have zero (x : X) : (z x).getD 10 false = false := by
      rw [List.getD_append_right _ _ _ _ (by simp : (List.ofFn x).length ≤ 10)]
      simp
    have wn (i : ℕ) : repr z 11 (atWire w i) := by
      by_cases small : i < 10
      · interval_cases i
        all_goals first
          | exact ⟨10,by decide,funext fun x => (zero x).symm⟩
          | exact ⟨_,by decide,funext fun x => (read (1 : Fin 8) x).symm⟩
          | exact ⟨_,by decide,funext fun x => (read (0 : Fin 8) x).symm⟩
          | exact ⟨_,by decide,funext fun x => (read (4 : Fin 8) x).symm⟩
          | exact ⟨_,by decide,funext fun x => (read (7 : Fin 8) x).symm⟩
          | exact ⟨_,by decide,funext fun x => (read (5 : Fin 8) x).symm⟩
          | exact ⟨_,by decide,funext fun x => (read (2 : Fin 8) x).symm⟩
          | exact ⟨_,by decide,funext fun x => (read (6 : Fin 8) x).symm⟩
          | exact ⟨_,by decide,funext fun x => (read (3 : Fin 8) x).symm⟩
      · refine ⟨10,by decide,funext fun x => ?_⟩
        exact (List.getD_eq_default _ _ (by simp [w]; omega)).trans (zero x).symm
    have zn (i : ℕ) : repr z 11 (atWire z i) := by
      by_cases h : i < 11
      · exact ⟨i,h,rfl⟩
      · exact ⟨10,by decide,funext fun x => (List.getD_eq_default _ _ (by rw [lz]; omega)).trans (zero x).symm⟩
    obtain ⟨E,hE,sz,fin⟩ := compile D.gates z w z 10 11 T legal (by simp [w]) lz wn zn
      ⟨10,by decide,funext fun x => (zero x).symm⟩ dup
    obtain ⟨j,hj⟩ := fin D.output
    exact ⟨⟨E,j⟩,hE,sz,fun y => (congrFun hj y).symm⟩

  let row (x : Fin 9 → Bool) : List Bool := List.ofFn x ++ [x 0 || x 6]

  let emit (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

  let maskBit (x h disj : Bool) := if disj then x || h else x && h

  let redirect (v k i : ℕ) : ℕ := if i = v then k else if i < k then i else i+1

  let rename (f : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map f⟩

  have fold_size (gs : List Gate) (w : List Bool) : (gs.foldl emit w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih => rw [List.foldl_cons,ih]; simp [emit]; omega

  have fold_preserves (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl emit w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons,ih (emit w g) (by simp [emit]; omega)]
      exact List.getD_append _ _ _ _ hi

  have set_emit_avoid (g : Gate) (w : List Bool) (v : ℕ) (val : Bool)
      (hv : v < w.length) (avoid : v ∉ g.inputs) :
      emit (w.set v val) g = (emit w g).set v val := by
    have reads : ∀ i ∈ g.inputs, (w.set v val).getD i false = w.getD i false := by
      intro i hi
      have ne : v ≠ i := by intro eq; apply avoid; exact eq ▸ hi
      by_cases valid : i < w.length
      · rw [List.getD_eq_getElem _ _ (by simpa using valid),List.getD_eq_getElem _ _ valid,
          List.getElem_set_ne ne]
      · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt valid),
          List.getD_eq_default _ _ (Nat.le_of_not_gt valid)]
    unfold emit
    rw [List.map_congr_left reads,List.set_append_left v val hv]

  have fold_set_avoid (gs : List Gate) (w : List Bool) (v : ℕ) (val : Bool)
      (hv : v < w.length) (avoid : ∀ g ∈ gs, v ∉ g.inputs) :
      gs.foldl emit (w.set v val) = (gs.foldl emit w).set v val := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      simp only [List.foldl_cons]
      rw [set_emit_avoid g w v val hv (avoid g (by simp))]
      exact ih (emit w g) (by simp [emit]; omega) (fun a ha => avoid a (by simp [ha]))

  have append_other (w : List Bool) (b : Bool) (i : ℕ) (ne : i ≠ w.length) :
      (w++[b]).getD i false = w.getD i false := by
    by_cases small : i < w.length
    · exact List.getD_append _ _ _ _ small
    · rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by omega)]

  have suffix_shift (gs : List Gate) (v k : ℕ) (w y : List Bool)
      (hv : v < k) (hk : k ≤ w.length) (len : y.length = w.length + 1)
      (rel : ∀ i, y.getD (redirect v k i) false = w.getD i false) :
      ∀ i, ((gs.map (rename (redirect v k))).foldl emit y).getD (redirect v k i) false =
        (gs.foldl emit w).getD i false := by
    induction gs generalizing w y with
    | nil => exact rel
    | cons g gs ih =>
      simp only [List.map_cons,List.foldl_cons]
      let value := g.op.eval (g.inputs.map fun i => w.getD i false)
      have emitY : emit y (rename (redirect v k) g) = y ++ [value] := by
        change y ++ [g.op.eval ((g.inputs.map (redirect v k)).map fun i => y.getD i false)] = _
        simp only [List.map_map,Function.comp_def]
        rw [List.map_congr_left (fun i _ => rel i)]
      rw [emitY]
      apply ih (w++[value]) (y++[value])
      · simp; omega
      · simp [len]
      intro i
      have sameWire : redirect v k i = y.length ↔ i = w.length := by
        by_cases eq : i = v
        · simp only [redirect]
          rw [ite_eq_left eq]
          omega
        · simp only [redirect]
          rw [ite_eq_right eq]
          split <;> omega
      by_cases hi : i = w.length
      · rw [sameWire.mpr hi,hi]
        simp
      · rw [append_other _ _ _ (fun a => hi (sameWire.mp a)),append_other _ _ _ hi]
        exact rel i

  have append_with_mask (v : ℕ) (old : List Bool) (hv : v < old.length) (bit : Bool) :
      ∀ i, (old ++ [bit]).getD (redirect v old.length i) false = (old.set v bit).getD i false := by
    intro i
    by_cases piv : i = v
    · subst i
      simp only [redirect, ite_true]
      rw [List.getD_append_right _ _ _ _ le_rfl,Nat.sub_self,List.getD_cons_zero,
        List.getD_eq_getElem _ _ (by simp; exact hv)]
      simp
    simp only [redirect]
    rw [ite_eq_right piv]
    by_cases valid : i < old.length
    · rw [ite_eq_left valid,List.getD_append _ _ _ _ valid,List.getD_eq_getElem _ _ valid,
        List.getD_eq_getElem _ _ (by simpa using valid),List.getElem_set_ne (Ne.symm piv)]
    · rw [ite_eq_right valid,List.getD_eq_default _ _ (by simp; omega),
        List.getD_eq_default _ _ (by simp; omega)]

  have row_pivot (x : Fin 9 → Bool) (v : Fin 9) : (row x).getD v.val false = x v := by
    unfold row
    rw [List.getD_append _ _ _ _ (by simpa using v.isLt),
      List.getD_eq_getElem _ _ (by simpa using v.isLt),List.getElem_ofFn]

  have mask_value (x : Fin 9 → Bool) (v : Fin 9) (k : ℕ) (disj : Bool) (old : List Bool)
      (hv : v.val < old.length) (oldv : old.getD v.val false = x v) :
      emit old ⟨if disj then .or else .and,[v.val,k]⟩ =
        old ++ [maskBit (x v) (old.getD k false) disj] := by
    unfold emit maskBit
    cases disj
    · change old ++ [(old.getD v.val false && (old.getD k false && true))] =
        old ++ [x v && old.getD k false]
      rw [Bool.and_true,oldv]
    · change old ++ [(old.getD v.val false || (old.getD k false || false))] =
        old ++ [x v || old.getD k false]
      rw [Bool.or_false,oldv]

  let reads6 := fun (g : Gate) => (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains 6

  have insertMasked (C : Circuit) (v : Fin 9) (k : ℕ) (disj : Bool)
      (hv6 : v.val ≠ 6) (fan : FanInTwo C) (lo : 10 ≤ k) (hi : k < 10+C.size)
      (avoid : ∀ g ∈ C.gates.take (k+1-10), v.val ∉ g.inputs) :
      ∃ Q : Circuit, FanInTwo Q ∧ Q.size = C.size+1 ∧
        (Q.gates.filter (fun g => g.inputs.contains v.val) = [⟨if disj then .or else .and,[v.val,k]⟩]) ∧
        ((Q.gates.filter reads6).map Gate.op = (C.gates.filter reads6).map Gate.op) ∧
        ∀ x : Fin 9 → Bool, Q.eval (row x) = C.eval
          ((row x).set v.val (maskBit (x v) ((C.wires (row x)).getD k false) disj)) := by
    let pre := C.gates.take (k+1-10)
    let suf := C.gates.drop (k+1-10)
    let mask : Gate := ⟨if disj then .or else .and,[v.val,k]⟩
    let shift := rename (redirect v.val (k+1))
    let D : Circuit := ⟨(pre ++ mask :: suf.map shift),redirect v.val (k+1) C.output⟩
    have split : pre ++ suf = C.gates := List.take_append_drop _ _
    have maskLegal : mask.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ mask.inputs.length ≤ 2 := by
      cases disj <;> simp [mask]
    have legal : FanInTwo D := by
      intro g hg
      change g ∈ (pre ++ mask :: suf.map shift) at hg
      rcases List.mem_append.mp hg with hg | hg
      · exact fan g (by rw [← split]; exact List.mem_append_left _ hg)
      rcases List.mem_cons.mp hg with rfl | hg
      · exact maskLegal
      obtain ⟨g',hg',rfl⟩ := List.mem_map.mp hg
      obtain ⟨op,arity⟩ := fan g' (by rw [← split]; exact List.mem_append_right _ hg')
      exact ⟨op,by simpa [shift,rename] using arity⟩
    have hsize : D.size = C.size+1 := by
      have len := congrArg List.length split
      change ((pre ++ mask :: suf.map shift)).length = C.gates.length+1
      simp only [List.length_cons,List.length_append,List.length_map] at len ⊢
      omega
    have redirectV (i : ℕ) : redirect v.val (k+1) i ≠ v.val := by
      have h := v.isLt
      dsimp only [redirect]
      split <;> (first | omega | split <;> omega)
    have redirect6 (i : ℕ) : redirect v.val (k+1) i = 6 ↔ i = 6 := by
      dsimp only [redirect]
      split <;> (first | omega | split <;> omega)
    have hshift (g : Gate) : reads6 (shift g) = reads6 g := by
      dsimp only [reads6,shift,rename]
      rw [← List.map_take]
      apply Bool.eq_iff_iff.mpr
      simp only [List.contains_iff_mem,List.mem_map]
      constructor
      · rintro ⟨i,hi,h⟩
        exact (redirect6 i).mp h ▸ hi
      · exact fun h => ⟨6,h,(redirect6 6).mpr rfl⟩
    have vp : pre.filter (fun g => g.inputs.contains v.val) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro g hg
      simpa only [List.contains_iff_mem] using avoid g hg
    have vs : (suf.map shift).filter (fun g => g.inputs.contains v.val) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro g hg
      obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hg
      simp only [List.contains_iff_mem,shift,rename,List.mem_map]
      rintro ⟨i,hi,e⟩
      exact redirectV i e
    have sixMask : reads6 mask = false := by
      have ev : (v:ℕ) ≠ 6 := hv6
      have ek : k ≠ 6 := by omega
      cases disj <;> change ([v.val,k] : List ℕ).contains 6 = false <;> simp [Ne.symm ev,Ne.symm ek]
    have ss : ((suf.map shift).filter reads6).map Gate.op = (suf.filter reads6).map Gate.op := by
      suffices h : ∀ l : List Gate, ((l.map shift).filter reads6).map Gate.op = (l.filter reads6).map Gate.op from h suf
      intro l
      induction l with
      | nil => rfl
      | cons g l ih =>
        cases e : reads6 g <;> simp [List.filter_cons,hshift,e,shift,rename,ih]
    refine ⟨D,legal,hsize,?_,?_,?_⟩
    · change ((pre ++ mask :: suf.map shift).filter _) = _
      rw [List.filter_append,vp,List.filter_cons,vs]
      simp [mask]
    · change (((pre ++ mask :: suf.map shift).filter reads6).map Gate.op) = _
      rw [← split,List.filter_append,List.filter_append,List.filter_cons,sixMask]
      simp only [Bool.false_eq_true,↓reduceIte,List.map_append,ss]
    intro x
    let old := pre.foldl emit (row x)
    have kBound : k+1-10 ≤ C.gates.length := by change k < 10+C.gates.length at hi; omega
    have length : old.length = k+1 := by
      rw [show old = pre.foldl emit (row x) by rfl,fold_size]
      simp [pre,row,Nat.min_eq_left kBound]
      omega
    have vBound : v.val < old.length := by rw [length]; have := v.isLt; omega
    have saved : (C.wires (row x)).getD k false = old.getD k false := by
      change (C.gates.foldl emit (row x)).getD k false = _
      rw [← split,List.foldl_append]
      exact fold_preserves suf old k (by omega)
    have savedV : old.getD v.val false = x v := by
      rw [fold_preserves pre (row x) _ (by simp [row]; have := v.isLt; omega),row_pivot]
    let bit := maskBit (x v) (old.getD k false) disj
    have oldSet : pre.foldl emit ((row x).set v.val bit) = old.set v.val bit :=
      fold_set_avoid pre (row x) v.val bit (by simp [row]; have := v.isLt; omega) avoid
    have law (i : ℕ) : (old ++ [bit]).getD (redirect v.val (k+1) i) false =
        (old.set v.val bit).getD i false := by rw [← length]; exact append_with_mask v.val old vBound bit i
    have simulated := suffix_shift suf v.val (k+1) (old.set v.val bit) (old++[bit])
      (by have := v.isLt; omega) (by simp [length]) (by simp) law C.output
    change ((pre ++ mask :: suf.map shift).foldl emit (row x)).getD
        (redirect v.val (k+1) C.output) false =
      (C.gates.foldl emit ((row x).set v.val (maskBit (x v) ((C.wires (row x)).getD k false) disj))).getD C.output false
    rw [List.foldl_append, List.foldl_cons,mask_value x v k disj old vBound savedV,
      saved,← split,List.foldl_append,oldSet]
    exact simulated

  dsimp only
  intro v C k b v0 v6 fan size lo hi avoid _ _ chan _
  by_contra! correct
  obtain ⟨D,leg,dim,uniqueV,unique6,sim⟩ := insertMasked C v k b (fun e => v6 (Fin.ext e)) fan lo (by omega) avoid
  let F := fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
  let G := fun x : Fin 8 → Bool => ([1,12,23,4,15,26,37,46,57,74] : List ℕ).any (fun e => x (Fin.ofNat 8 (e / 10)) && x (Fin.ofNat 8 (e % 10)))
  let w := fun y : Fin 8 → Bool => [y 1,y 0,y 4,y 7,y 5,y 2,false,y 6,y 3,y 1]
  have hD : ∀ x, D.eval (row x) = F x := fun x => (sim x).trans (correct x)
  have hn := binary D leg (by
    intro x
    rw [show (List.ofFn x ++ [x 0 || x 6]) = row x by rfl,hD]
    simp only [F,List.any_cons,List.any_nil,Bool.or_false,Bool.or_assoc]
    rfl)
  obtain ⟨g,go,_,hg⟩ := chan
  change C.gates.filter reads6 = [g] at hg
  have onSlice (y : Fin 8 → Bool) : D.eval (w y) = G y := by
    let x : Fin 9 → Bool := ![y 1,y 0,y 4,y 7,y 5,y 2,false,y 6,y 3]
    have h : w y = row x := by
      change _ = List.ofFn x ++ [x 0 || x 6]
      simp only [List.ofFn_succ,List.ofFn_zero,List.cons_append,List.nil_append]
      change _ = [y 1,y 0,y 4,y 7,y 5,y 2,false,y 6,y 3,y 1 || false]
      rw [Bool.or_false]
    rw [h,hD]
    change ((y 1 && y 0) || ((y 0 && y 4) || ((y 4 && y 7) || ((y 7 && y 5) || ((y 5 && y 1) || ((y 1 && y 2) || ((y 0 && false) || ((y 4 && y 6) || ((y 7 && y 3) || ((y 2 && y 6) || ((false && y 3) || ((y 3 && y 2) || false)))))))))))) = _
    simp only [G,List.any_cons,List.any_nil,Bool.or_false,Bool.false_and,Bool.and_false]
    change _ = ((y 0 && y 1) || ((y 1 && y 2) || ((y 2 && y 3) || ((y 0 && y 4) || ((y 1 && y 5) || ((y 2 && y 6) || ((y 3 && y 7) || ((y 4 && y 6) || ((y 5 && y 7) || (y 7 && y 4))))))))))
    ac_rfl
  obtain ⟨y,u,hy⟩ := hard D v k leg (by omega) hn v0 v6 lo (by rw [uniqueV]; rfl)
    (by rw [unique6,hg]; simp [go]) (by
      intro t T
      dsimp only
      intro dup
      have dim14 : D.size = 14 := by omega
      obtain ⟨E,hE,sz,he⟩ := compiler D t T leg (by
        simpa only [Bool.or_false,dim14] using dup)
      have ub := literal t E hE (fun y => (he y).trans (onSlice y))
      omega)
  have tab : ∀ q : Fin 8 → Bool, G q = (115792089237316195379631272860981142487703928461450370304571918768505461864648 : ℕ).testBit (tableIndex q) := by decide
  rw [←tab]
    at hy
  cases u
  · apply hy
    simpa only [Bool.or_false,Bool.false_and] using onSlice y
  · apply hy
    let x : Fin 9 → Bool := ![y 1,y 0,y 4,y 7,y 5,y 2,true,y 6,y 3]
    have h : [y 1,y 0,y 4,y 7,y 5,y 2,true,y 6,y 3,y 1 || true] = row x := by
      change _ = List.ofFn x ++ [x 0 || x 6]
      simp only [List.ofFn_succ,List.ofFn_zero,List.cons_append,List.nil_append]
      rfl
    change D.eval [y 1,y 0,y 4,y 7,y 5,y 2,true,y 6,y 3,y 1 || true] = _
    rw [h,hD]
    change ((y 1 && y 0) || ((y 0 && y 4) || ((y 4 && y 7) || ((y 7 && y 5) || ((y 5 && y 1) || ((y 1 && y 2) || ((y 0 && true) || ((y 4 && y 6) || ((y 7 && y 3) || ((y 2 && y 6) || ((true && y 3) || ((y 3 && y 2) || false)))))))))))) = _
    simp only [G,List.any_cons,List.any_nil,Bool.or_false,Bool.true_and,Bool.and_true]
    change _ = (((y 0 && y 1) || ((y 1 && y 2) || ((y 2 && y 3) || ((y 0 && y 4) || ((y 1 && y 5) || ((y 2 && y 6) || ((y 3 && y 7) || ((y 4 && y 6) || ((y 5 && y 7) || (y 7 && y 4)))))))))) || (y 0 || y 3))
    ac_rfl
