import PEqualNP.Defs

-- Deleting either seed endpoint or any degree-two vertex leaves one of two
-- eight-variable graphs. At least eleven suffix gates must produce fresh
-- truth tables on each of these five restrictions. Repeated tables can be
-- bypassed while preserving both taps, including default values past the end.
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_3136_714
    (eight : ¬ HasCircuitSize 8 (fun x => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 1 && x 5 || x 2 && x 6 || x 3 && x 7 || x 5 && x 7) 11)
    (other : ¬ HasCircuitSize 8 (fun x => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 0 && x 4 || x 1 && x 5 || x 2 && x 6 || x 3 && x 7 || x 4 && x 6 || x 5 && x 7 || x 7 && x 4) 12)
    (residual : ∀ (gs : List Gate) (a b : ℕ), gs.length = 13 → FanInTwo ⟨gs, 0⟩ →
      gs.countP (fun g => g.op.eval [false]) ≤ 1 → a ≤ 24 → b ≤ 24 →
      let w (x : Fin 9 → Bool) := (Circuit.mk gs 0).wires (List.ofFn x ++ [x 0 || x 3])
      (∀ v ∈ ([0,3,4,6,7] : List (Fin 9)),
        11 ≤ (List.range gs.length).countP fun j => decide (∀ i : Fin (10+j),
          ∃ x : Fin 9 → Bool, x v = false ∧ (w x).getD i.val false ≠ (w x).getD (10+j) false)) →
      ∃ x : Fin 9 → Bool, ((w x).getD a false && (w x).getD b false) ≠ (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) :
  ∀ (x1 : List PEqualNP.CircuitLowerBounds.Gate) (x2 x3 : ℕ),   x1.length = (13 : ℕ) →     PEqualNP.MetaComplexity.FanInTwo { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →       List.countP (fun (x6 : PEqualNP.CircuitLowerBounds.Gate) => x6.op.eval [Bool.false]) x1 ≤ (1 : ℕ) →         x2 ≤ (24 : ℕ) →           x3 ≤ (24 : ℕ) →             ∃ (x9 : Fin (9 : ℕ) → Bool),               have x10 : List Bool := { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x9 ++ [x9 (0 : Fin (9 : ℕ)) || x9 (3 : Fin (9 : ℕ))]);               (x10.getD x2 Bool.false && x10.getD x3 Bool.false) ≠ (x9 (0 : Fin (9 : ℕ)) && x9 (1 : Fin (9 : ℕ)) || x9 (1 : Fin (9 : ℕ)) && x9 (2 : Fin (9 : ℕ)) || x9 (2 : Fin (9 : ℕ)) && x9 (3 : Fin (9 : ℕ)) || x9 (3 : Fin (9 : ℕ)) && x9 (4 : Fin (9 : ℕ)) || x9 (4 : Fin (9 : ℕ)) && x9 (0 : Fin (9 : ℕ)) || x9 (0 : Fin (9 : ℕ)) && x9 (5 : Fin (9 : ℕ)) || x9 (1 : Fin (9 : ℕ)) && x9 (6 : Fin (9 : ℕ)) || x9 (2 : Fin (9 : ℕ)) && x9 (7 : Fin (9 : ℕ)) || x9 (3 : Fin (9 : ℕ)) && x9 (8 : Fin (9 : ℕ)) || x9 (5 : Fin (9 : ℕ)) && x9 (7 : Fin (9 : ℕ)) || x9 (6 : Fin (9 : ℕ)) && x9 (8 : Fin (9 : ℕ)) || x9 (8 : Fin (9 : ℕ)) && x9 (5 : Fin (9 : ℕ))) := by
  have compress : ∀ (gs pre : List Gate) (raw : List ℕ) (a b : ℕ), FanInTwo ⟨gs, 0⟩ → FanInTwo ⟨pre, 0⟩ →
      let w := fun (x : Fin 8 → Bool) => (Circuit.mk gs 0).wires
        (raw.map fun i => ((Circuit.mk pre 0).wires (List.ofFn x)).getD i false)
      let k := (List.range gs.length).countP fun j => decide (∀ i : Fin (raw.length+j),
        ∃ x : Fin 8 → Bool, (w x).getD i.val false ≠ (w x).getD (raw.length+j) false)
      HasCircuitSize 8 (fun x => (w x).getD a false && (w x).getD b false) (pre.length+k+1) := by
    intro gs pre raw a b legal preLegal
    let run (p : List Gate) (u : List Bool) := (Circuit.mk p 0).wires u
    let inp (x : Fin 8 → Bool) := raw.map fun i => (run pre (List.ofFn x)).getD i false
    let v (p : List Gate) (x : Fin 8 → Bool) := run p (inp x)
    let w (p : List Gate) (x : Fin 8 → Bool) := run p (List.ofFn x)
    let fresh (p : List Gate) (j : ℕ) := decide (∀ i : Fin (raw.length+j),
      ∃ x : Fin 8 → Bool, (v p x).getD i.val false ≠ (v p x).getD (raw.length+j) false)
    let cost (p : List Gate) := (List.range p.length).countP (fresh p)
    let legalList (p : List Gate) := FanInTwo ⟨p, 0⟩
    let rep (p d : List Gate) := ∀ i, ∃ j, ∀ x, (w d x).getD j false = (v p x).getD i false
    have snoc (p : List Gate) (g : Gate) (u : List Bool) :
        run (p ++ [g]) u = run p u ++ [g.op.eval (g.inputs.map fun i => (run p u).getD i false)] := by
      change (p ++ [g]).foldl (fun z h => z ++ [h.op.eval (h.inputs.map fun i => z.getD i false)]) u = _
      rw [List.foldl_append]
      rfl
    have len (p : List Gate) (u : List Bool) : (run p u).length = u.length + p.length := by
      induction p using List.reverseRecOn with
      | nil => rfl
      | append_singleton p g ih => simp [snoc, ih]; omega
    have vlen (p : List Gate) (x : Fin 8 → Bool) : (v p x).length = raw.length + p.length := by
      simp [v,inp,len]
    have wlen (p : List Gate) (x : Fin 8 → Bool) : (w p x).length = 8 + p.length := by
      simp [w,len]
    have old (p : List Gate) (g : Gate) (x : Fin 8 → Bool) (i : ℕ) (h : i < raw.length + p.length) :
        (v (p ++ [g]) x).getD i false = (v p x).getD i false := by
      unfold v
      rw [snoc]
      exact List.getD_append _ _ _ _ (by simpa [len,inp] using h)
    have last (p : List Gate) (g : Gate) (u : List Bool) :
        (run (p ++ [g]) u).getD (u.length+p.length) false =
        g.op.eval (g.inputs.map fun i => (run p u).getD i false) := by
      rw [snoc,List.getD_append_right _ _ _ _ (by rw [len]),len]
      simp
    have grow (p : List Gate) (g : Gate) :
        cost (p ++ [g]) = cost p + (if fresh (p ++ [g]) p.length then 1 else 0) := by
      have same : (List.range p.length).countP (fresh (p ++ [g])) =
          (List.range p.length).countP (fresh p) := by
        apply List.countP_congr
        intro j hj
        have lt := List.mem_range.mp hj
        have smaller (i : Fin (raw.length+j)) : i.val < raw.length+p.length := by omega
        simp only [fresh, decide_eq_true_eq]
        constructor <;> intro h i <;> obtain ⟨x,hx⟩ := h i <;> refine ⟨x,?_⟩ <;>
          simpa only [old p g x i.val (smaller i),old p g x (raw.length+j) (by omega)] using hx
      simp only [cost,List.length_append,List.length_cons,List.length_nil,zero_add,List.range_succ,
        List.countP_append,List.countP_singleton,same]
    have build (p : List Gate) (ok : legalList p) :
        ∃ d : List Gate, legalList d ∧ d.length ≤ pre.length + cost p ∧ rep p d := by
      induction p using List.reverseRecOn with
      | nil =>
        refine ⟨pre, preLegal, Nat.le_add_right _ _, ?_⟩
        intro i
        by_cases inRange : i < raw.length
        · refine ⟨raw[i],fun x => ?_⟩
          change (w pre x).getD raw[i] false = (raw.map _).getD i false
          symm
          rw [List.getD_eq_getElem _ _ (by simpa using inRange),List.getElem_map]
        · refine ⟨8+pre.length,fun x => ?_⟩
          change (w pre x).getD (8+pre.length) false = (raw.map _).getD i false
          rw [List.getD_eq_default _ _ (by rw [wlen]),List.getD_eq_default _ _ (by simp; omega)]
      | append_singleton p g ih =>
        have prev : legalList p := fun t ht => ok t (List.mem_append_left _ ht)
        have gate := ok g (List.mem_append_right _ List.mem_cons_self)
        obtain ⟨d,dok,budget,covered⟩ := ih prev
        let j := raw.length + p.length
        let m := 8 + d.length
        have past (x : Fin 8 → Bool) (i : ℕ) (hi : j < i) :
            (v (p ++ [g]) x).getD i false = false :=
          List.getD_eq_default _ _ (by rw [vlen]; simp [j] at *; omega)
        by_cases new : fresh (p ++ [g]) p.length = true
        · classical
          choose redirect eq using covered
          let t : Gate := ⟨g.op,g.inputs.map redirect⟩
          have value (x : Fin 8 → Bool) :
              (w (d ++ [t]) x).getD m false = (v (p ++ [g]) x).getD j false := by
            have res := last d t (List.ofFn x)
            have src := last p g (inp x)
            rw [show (List.ofFn x).length = 8 by simp] at res
            rw [show (inp x).length = raw.length by simp [inp]] at src
            refine res.trans (Eq.trans ?_ src.symm)
            change g.op.eval ((g.inputs.map redirect).map _) = g.op.eval (g.inputs.map _)
            congr 1
            rw [List.map_map]
            exact List.map_congr_left fun z _ => eq z x
          refine ⟨d ++ [t],?_,?_,?_⟩
          · intro gate' hgate'
            rcases List.mem_append.mp hgate' with h | h
            · exact dok _ h
            · obtain rfl := List.mem_singleton.mp h
              exact ⟨gate.1,by simpa [t] using gate.2⟩
          · rw [grow]
            simpa [new,Nat.add_assoc] using Nat.add_le_add_right budget 1
          · intro i
            by_cases hi : i < j
            · by_cases real : redirect i < m
              · refine ⟨redirect i,fun x => ?_⟩
                change (run (d ++ [t]) _).getD _ _ = _
                rw [snoc,List.getD_append _ _ _ _ (by simpa [len,m] using real),old p g x i hi]
                exact eq i x
              · refine ⟨m+1,fun x => ?_⟩
                rw [List.getD_eq_default _ _ (by simp [wlen,m,Nat.add_assoc]),old p g x i hi,← eq i x,
                  List.getD_eq_default _ _ (by rw [wlen]; omega)]
            · by_cases hit : i = j
              · subst i
                exact ⟨m,value⟩
              · exact ⟨m+1,fun x => by rw [past x i (by omega),List.getD_eq_default _ _ (by simp [wlen,m,Nat.add_assoc])]⟩
        · have duplicate : ∃ i : Fin j, ∀ x : Fin 8 → Bool,
              (v (p ++ [g]) x).getD i.val false = (v (p ++ [g]) x).getD j false := by
            by_contra! h
            exact new (decide_eq_true h)
          obtain ⟨i,dup⟩ := duplicate
          refine ⟨d,dok,?_,?_⟩
          · simpa [grow,new] using budget
          · intro s
            by_cases hs : s < j
            · obtain ⟨r,hr⟩ := covered s
              exact ⟨r,fun x => (hr x).trans (old p g x s hs).symm⟩
            · by_cases hit : s = j
              · subst s
                obtain ⟨r,hr⟩ := covered i.val
                exact ⟨r,fun x => ((hr x).trans (old p g x _ i.isLt).symm).trans (dup x)⟩
              · exact ⟨m,fun x => by rw [past x s (by omega),List.getD_eq_default _ _ (by rw [wlen])]⟩
    obtain ⟨d,dok,budget,covered⟩ := build gs legal
    obtain ⟨i,ia⟩ := covered a
    obtain ⟨j,jb⟩ := covered b
    let t : Gate := ⟨.and,[i,j]⟩
    refine ⟨⟨d ++ [t],8 + d.length⟩,?_,?_,?_⟩
    · intro g hg
      rcases List.mem_append.mp hg with h | h
      · exact dok _ h
      · obtain rfl := List.mem_singleton.mp h
        simp [t]
    · change (d ++ [t]).length ≤ pre.length + cost gs + 1
      simpa using Nat.add_le_add_right budget 1
    · intro x
      have res := last d t (List.ofFn x)
      rw [show (List.ofFn x).length = 8 by simp] at res
      refine res.trans ?_
      change GateOp.and.eval [(w d x).getD i false,(w d x).getD j false] = _
      rw [ia x,jb x]
      change (_ && (_ && true)) = (_ && _)
      rw [Bool.and_true]
      rfl
  intro gs a b hlen fan count ha hb
  by_contra absent
  let source (x : Fin 9 → Bool) := List.ofFn x ++ [x 0 || x 3]
  let f (x : Fin 9 → Bool) := x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5
  let q (x : Fin 8 → Bool) := x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 1 && x 5 || x 2 && x 6 || x 3 && x 7 || x 5 && x 7
  have exactAt (x : Fin 9 → Bool) :
      (((Circuit.mk gs 0).wires (source x)).getD a false &&
       ((Circuit.mk gs 0).wires (source x)).getD b false) = f x := by
    by_contra miss
    exact absent ⟨x,miss⟩
  let q2 (x : Fin 8 → Bool) := x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 0 && x 4 || x 1 && x 5 || x 2 && x 6 || x 3 && x 7 || x 4 && x 6 || x 5 && x 7 || x 7 && x 4
  let out (x : Fin 9 → Bool) := (Circuit.mk gs 0).wires (source x)
  let enough (t : Fin 9) := 11 ≤ (List.range gs.length).countP fun j => decide (∀ i : Fin (10+j),
    ∃ x : Fin 9 → Bool, x t = false ∧ (out x).getD i.val false ≠ (out x).getD (10+j) false)
  let row (raw : List ℕ) (x : Fin 8 → Bool) (i : Fin 9) :=
    (List.ofFn x).getD (raw.getD i.val 9) false
  have prune (t : Fin 9) (pre : List Gate) (raw : List ℕ) (target : (Fin 8 → Bool) → Bool)
      (rawLen : raw.length = 10) (ok : FanInTwo ⟨pre,0⟩)
      (bound : ¬ HasCircuitSize 8 target (pre.length+11))
      (rows : ∀ x : Fin 8 → Bool, (row raw x) t = false ∧
        raw.map (fun i => ((Circuit.mk pre 0).wires (List.ofFn x)).getD i false) = source (row raw x) ∧
        f (row raw x) = target x) : enough t := by
    let w (x : Fin 8 → Bool) := (Circuit.mk gs 0).wires
      (raw.map fun i => ((Circuit.mk pre 0).wires (List.ofFn x)).getD i false)
    let k := (List.range gs.length).countP fun j => decide (∀ i : Fin (raw.length+j),
      ∃ x : Fin 8 → Bool, (w x).getD i.val false ≠ (w x).getD (raw.length+j) false)
    have agrees (x : Fin 8 → Bool) : w x = out (row raw x) := by
      unfold w out
      rw [(rows x).2.1]
    have same : (fun x => (w x).getD a false && (w x).getD b false) = target := by
      funext x
      rw [agrees]
      exact (exactAt _).trans (rows x).2.2
    have small := compress gs pre raw a b fan ok
    dsimp only at small
    change HasCircuitSize 8 (fun x => (w x).getD a false && (w x).getD b false) (pre.length+k+1) at small
    rw [same] at small
    have hk : 11 ≤ k := by
      by_contra! little
      obtain ⟨C, legal, size, computes⟩ := small
      exact bound ⟨C,legal,by omega,computes⟩
    apply hk.trans
    apply List.countP_mono_left
    intro j _ h
    simp only [decide_eq_true_eq] at h ⊢
    intro i
    let ii : Fin (raw.length+j) := ⟨i.val,by rw [rawLen]; exact i.isLt⟩
    obtain ⟨x,hx⟩ := h ii
    exact ⟨row raw x,(rows x).1,by simpa only [agrees,ii,rawLen] using hx⟩
  apply absent
  apply residual gs a b hlen fan count ha hb
  intro t ht
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · apply prune 0 [] [9, 0, 1, 2, 6, 7, 4, 5, 3, 2] q rfl (by intro g hg; cases hg) eight
    decide +kernel
  · apply prune 3 [] [2, 1, 0, 9, 6, 3, 5, 4, 7, 2] q rfl (by intro g hg; cases hg) eight
    decide +kernel
  · apply prune 4 [⟨.or,[0, 3]⟩] [0, 1, 2, 3, 9, 4, 5, 6, 7, 8] q2 rfl (by intro g hg; obtain rfl := List.mem_singleton.mp hg; exact ⟨Or.inr (Or.inl rfl),by decide⟩) other
    decide +kernel
  · apply prune 6 [⟨.or,[1, 7]⟩] [1, 0, 4, 7, 5, 2, 9, 6, 3, 8] q2 rfl (by intro g hg; obtain rfl := List.mem_singleton.mp hg; exact ⟨Or.inr (Or.inl rfl),by decide⟩) other
    decide +kernel
  · apply prune 7 [⟨.or,[2, 4]⟩] [2, 1, 0, 4, 6, 3, 5, 9, 7, 8] q2 rfl (by intro g hg; obtain rfl := List.mem_singleton.mp hg; exact ⟨Or.inr (Or.inl rfl),by decide⟩) other
    decide +kernel
