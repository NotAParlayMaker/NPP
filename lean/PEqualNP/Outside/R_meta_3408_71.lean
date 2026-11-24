import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_3408_71
    (hprefix : ∀ l : List (Fin 11), l.length ≤ 2 →
    ∃ c ∈ ([1, 2, 3, 4, 6, 13, 14, 15, 16, 17, 18, 19, 20, 25, 26, 28, 29, 30, 31, 37, 39, 42, 50, 73, 75, 120, 121] : List ℕ), ∃ (s : Bool) (j : Fin 11), ∀ y : Fin 9 → Bool,
      let x := if s then y ∘ (![0,5,8,3,4,1,7,6,2] : Fin 9 → Fin 9) else y
      let w := List.ofFn y ++ [y 0 || y 4]
      GateOp.and.eval (l.map (fun i => (List.ofFn x ++ [x 0 || x 4]).getD i.val false)) =
        (w ++ [if c = 121 then true else w.getD (c / 11) false && w.getD (c % 11) false]).getD j.val false)
    (normalize : ∀ P D : Circuit, Monotone2 P → FanInTwo D → P.size + D.size ≤ 12 →
      P.output ≤ 24 → D.output ≤ 24 → (∀ g ∈ P.gates ++ D.gates, ∀ i ∈ g.inputs, i ≤ 24) →
      ∃ C : Circuit, FanInTwo C ∧ C.size = 13 ∧ C.output ≤ 24 ∧
        (∃ g ∈ C.gates, g.op = .not) ∧ (∀ i : Fin C.gates.length, let g := C.gates.get i
          (∀ j ∈ g.inputs, j < 11 + i.val ∨ j = 24) ∧
          g.inputs.Pairwise (· ≤ ·) ∧ (g.op = .not → g.inputs.length = 1) ∧
          (g.op ≠ .not → g.inputs.length ≠ 1)) ∧
        ∀ w : List Bool, w.length = 11 → C.eval w = D.eval (P.wires w ++ [!(P.wires w).getD P.output false]))
    (search : ∀ (c : ℕ) (C : Circuit), c ∈ ([1, 2, 3, 4, 6, 13, 14, 15, 16, 17, 18, 19, 20, 25, 26, 28, 29, 30, 31, 37, 39, 42, 50, 73, 75, 120, 121] : List ℕ) →
      FanInTwo C → C.size = 13 → C.output ≤ 24 → (∃ g ∈ C.gates, g.op = .not) →
      (∀ i : Fin C.gates.length, let g := C.gates.get i
          (∀ j ∈ g.inputs, j < 11 + i.val ∨ j = 24) ∧
          g.inputs.Pairwise (· ≤ ·) ∧ (g.op = .not → g.inputs.length = 1) ∧
          (g.op ≠ .not → g.inputs.length ≠ 1)) →
      ∃ x : Fin 9 → Bool, let w := List.ofFn x ++ [x 0 || x 4]
        C.eval (w ++ [if c = 121 then true else w.getD (c / 11) false && w.getD (c % 11) false]) ≠ (([1,11,21,31,36,5,15,25,35,52,62,77] : List ℕ).foldl (fun a e => a || x (Fin.ofNat 9 (e / 9)) && x (Fin.ofNat 9 (e % 9))) false)) :
    ∀ (x1 : List (Fin (11 : ℕ))) (x2 x3 : PEqualNP.CircuitLowerBounds.Circuit),   x1.length ≤ (2 : ℕ) →     PEqualNP.MetaComplexity.Monotone2 x2 →       PEqualNP.MetaComplexity.FanInTwo x3 →         x2.size + x3.size ≤ (12 : ℕ) →           x2.output ≤ (24 : ℕ) →             x3.output ≤ (24 : ℕ) →               (∀ x10 ∈ x2.gates ++ x3.gates, ∀ x12 ∈ x10.inputs, x12 ≤ (24 : ℕ)) →                 ∃ (x11 : Fin (9 : ℕ) → Bool),                   have x12 : List Bool := List.ofFn x11 ++ [x11 (0 : Fin (9 : ℕ)) || x11 (4 : Fin (9 : ℕ))];                   have x13 : List Bool := x2.wires (x12 ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x13 : Fin (11 : ℕ)) => x12.getD (↑x13) Bool.false) x1)]);                   x3.eval (x13 ++ [!x13.getD x2.output Bool.false]) ≠ (x11 (0 : Fin (9 : ℕ)) && x11 (1 : Fin (9 : ℕ)) || x11 (1 : Fin (9 : ℕ)) && x11 (2 : Fin (9 : ℕ)) || x11 (2 : Fin (9 : ℕ)) && x11 (3 : Fin (9 : ℕ)) || x11 (3 : Fin (9 : ℕ)) && x11 (4 : Fin (9 : ℕ)) || x11 (4 : Fin (9 : ℕ)) && x11 (0 : Fin (9 : ℕ)) || x11 (0 : Fin (9 : ℕ)) && x11 (5 : Fin (9 : ℕ)) || x11 (1 : Fin (9 : ℕ)) && x11 (6 : Fin (9 : ℕ)) || x11 (2 : Fin (9 : ℕ)) && x11 (7 : Fin (9 : ℕ)) || x11 (3 : Fin (9 : ℕ)) && x11 (8 : Fin (9 : ℕ)) || x11 (5 : Fin (9 : ℕ)) && x11 (7 : Fin (9 : ℕ)) || x11 (6 : Fin (9 : ℕ)) && x11 (8 : Fin (9 : ℕ)) || x11 (8 : Fin (9 : ℕ)) && x11 (5 : Fin (9 : ℕ))) := by
  have hcore : ∀ (c : ℕ), c ∈ ([1, 2, 3, 4, 6, 13, 14, 15, 16, 17, 18, 19, 20, 25, 26, 28, 29, 30, 31, 37, 39, 42, 50, 73, 75, 120, 121] : List ℕ) → ∀ A B : Circuit,
    PEqualNP.MetaComplexity.Monotone2 A → PEqualNP.MetaComplexity.FanInTwo B →
    A.size + B.size ≤ 12 → A.output ≤ 24 → B.output ≤ 24 →
    (∀ g ∈ A.gates ++ B.gates, ∀ i ∈ g.inputs, i ≤ 24) →
    ∃ x : Fin 9 → Bool,
      let w := List.ofFn x ++ [x 0 || x 4]
      let t := A.wires (w ++ [if c = 121 then true else w.getD (c / 11) false && w.getD (c % 11) false])
      B.eval (t ++ [!t.getD A.output false]) ≠ (x (0 : Fin (9 : ℕ)) && x (1 : Fin (9 : ℕ)) || x (1 : Fin (9 : ℕ)) && x (2 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ)) && x (3 : Fin (9 : ℕ)) || x (3 : Fin (9 : ℕ)) && x (4 : Fin (9 : ℕ)) || x (4 : Fin (9 : ℕ)) && x (0 : Fin (9 : ℕ)) || x (0 : Fin (9 : ℕ)) && x (5 : Fin (9 : ℕ)) || x (1 : Fin (9 : ℕ)) && x (6 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ)) && x (7 : Fin (9 : ℕ)) || x (3 : Fin (9 : ℕ)) && x (8 : Fin (9 : ℕ)) || x (5 : Fin (9 : ℕ)) && x (7 : Fin (9 : ℕ)) || x (6 : Fin (9 : ℕ)) && x (8 : Fin (9 : ℕ)) || x (8 : Fin (9 : ℕ)) && x (5 : Fin (9 : ℕ))) := by
    intro c hc A B ha hb hs ho hp hw
    obtain ⟨C,hC,hlen,hout,hn,hnf,eqv⟩ := normalize A B ha hb hs ho hp hw
    obtain ⟨x,hx⟩ := search c C hc hC hlen hout hn hnf
    refine ⟨x,?_⟩
    let w := List.ofFn x ++ [x 0 || x 4]
    let u := w ++ [if c = 121 then true else w.getD (c / 11) false && w.getD (c % 11) false]
    have he := eqv u (by simp [u,w])
    change C.eval u ≠ _ at hx
    change B.eval (A.wires u ++ [!(A.wires u).getD A.output false]) ≠ _
    rw [← he]
    exact hx
  intro l A B hl hA hB hsize hAo hBo bounds
  obtain ⟨c, hc, s, j, hprefix⟩ := hprefix l hl
  let p : Fin 9 → Fin 9 := if s then ![0,5,8,3,4,1,7,6,2] else id
  let r (i : ℕ) : ℕ := if h : i < 9 then (p ⟨i,h⟩).val else if i = 10 then j.val else i
  have rsmall {i : ℕ} (hi : i < 11) : r i < 11 := by
    dsimp [r]
    split
    · have := (p ⟨i,by assumption⟩).isLt
      omega
    · split <;> omega
  have rlarge {i : ℕ} (hi : 11 ≤ i) : r i = i := by simp [r, show ¬ i < 9 by omega, show i ≠ 10 by omega]
  have rbounded {i : ℕ} (hi : i ≤ 24) : r i ≤ 24 := by
    by_cases h : i < 11
    · have := rsmall h
      omega
    · rwa [rlarge (by omega)]
  let gate (g : Gate) : Gate := ⟨g.op, g.inputs.map r⟩
  let ren (C : Circuit) : Circuit := ⟨C.gates.map gate,r C.output⟩
  let Rel (u v : List Bool) : Prop :=
    11 ≤ u.length ∧ u.length = v.length ∧ ∀ i, u.getD i false = v.getD (r i) false
  have ext {u v : List Bool} (hu : Rel u v) (b : Bool) : Rel (u ++ [b]) (v ++ [b]) := by
    obtain ⟨hu, hv, hget⟩ := hu
    refine ⟨by simp; omega, by simp [hv], ?_⟩
    intro i
    rcases Nat.lt_trichotomy i u.length with lt | eq | gt
    · have hri : r i < v.length := by
        by_cases hi : i < 11
        · have := rsmall hi
          omega
        · rwa [rlarge (by omega), ← hv]
      rw [List.getD_append _ _ _ _ lt,List.getD_append _ _ _ _ hri]
      exact hget i
    · rw [rlarge (by omega), eq]
      simp [hv]
    · rw [rlarge (by omega)]
      rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
  have wire (C : Circuit) (u v : List Bool) (h : Rel u v) : Rel (C.wires u) ((ren C).wires v) := by
    let st (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    have fold : ∀ gs : List Gate, ∀ u v : List Bool, Rel u v →
        Rel (gs.foldl st u) ((gs.map gate).foldl st v) := by
      intro gs
      induction gs with
      | nil => intro u v h; exact h
      | cons g gs ih =>
        intro u v h
        apply ih
        have same : (gate g).op.eval ((gate g).inputs.map (fun i => v.getD i false)) =
            g.op.eval (g.inputs.map (fun i => u.getD i false)) := by
          simp only [gate,List.map_map]
          congr 1
          apply List.map_congr_left
          exact fun i _ => (h.2.2 i).symm
        change Rel (u ++ [_]) (v ++ [_])
        rw [same]
        exact ext h _
    exact fold _ _ _ h
  have hm : PEqualNP.MetaComplexity.Monotone2 (ren A) := by
    intro g hg
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hg
    exact ⟨(hA z hz).1,by simpa [gate] using (hA z hz).2⟩
  have hf : PEqualNP.MetaComplexity.FanInTwo (ren B) := by
    intro g hg
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hg
    exact ⟨(hB z hz).1,by simpa [gate] using (hB z hz).2⟩
  have hb : ∀ g ∈ (ren A).gates ++ (ren B).gates, ∀ i ∈ g.inputs, i ≤ 24 := by
    intro g hg
    change g ∈ A.gates.map gate ++ B.gates.map gate at hg
    rw [← List.map_append] at hg
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hg
    intro i hi
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hi
    exact rbounded (bounds z hz k hk)
  have hrenSize : (ren A).size + (ren B).size ≤ 12 := by
    change (A.gates.map gate).length + (B.gates.map gate).length ≤ 12
    simpa only [List.length_map] using (show A.gates.length + B.gates.length ≤ 12 from hsize)
  obtain ⟨y,hy⟩ := hcore c hc (ren A) (ren B) hm hf hrenSize (rbounded hAo) (rbounded hBo) hb
  let x : Fin 9 → Bool := y ∘ p
  let g (x : Fin 9 → Bool) := (x (0 : Fin (9 : ℕ)) && x (1 : Fin (9 : ℕ)) || x (1 : Fin (9 : ℕ)) && x (2 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ)) && x (3 : Fin (9 : ℕ)) || x (3 : Fin (9 : ℕ)) && x (4 : Fin (9 : ℕ)) || x (4 : Fin (9 : ℕ)) && x (0 : Fin (9 : ℕ)) || x (0 : Fin (9 : ℕ)) && x (5 : Fin (9 : ℕ)) || x (1 : Fin (9 : ℕ)) && x (6 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ)) && x (7 : Fin (9 : ℕ)) || x (3 : Fin (9 : ℕ)) && x (8 : Fin (9 : ℕ)) || x (5 : Fin (9 : ℕ)) && x (7 : Fin (9 : ℕ)) || x (6 : Fin (9 : ℕ)) && x (8 : Fin (9 : ℕ)) || x (8 : Fin (9 : ℕ)) && x (5 : Fin (9 : ℕ)))
  have inv : ∀ (b : Bool) (y : Fin 9 → Bool),
      let x := y ∘ (if b then (![0,5,8,3,4,1,7,6,2] : Fin 9 → Fin 9) else id)
      (x 0 || x 4) = (y 0 || y 4) ∧ g x = g y := by
    intro b y
    cases b
    · exact ⟨rfl,rfl⟩
    · refine ⟨rfl, ?_⟩
      change (y 0 && y 5 || y 5 && y 8 || y 8 && y 3 || y 3 && y 4 || y 4 && y 0 || y 0 && y 1 || y 5 && y 7 || y 8 && y 6 || y 3 && y 2 || y 1 && y 6 || y 7 && y 2 || y 2 && y 1) = (y 0 && y 1 || y 1 && y 2 || y 2 && y 3 || y 3 && y 4 || y 4 && y 0 || y 0 && y 5 || y 1 && y 6 || y 2 && y 7 || y 3 && y 8 || y 5 && y 7 || y 6 && y 8 || y 8 && y 5)
      simp only [Bool.or_assoc,Bool.or_comm,Bool.or_left_comm,Bool.and_comm]
  have hinv := inv s y
  change (x 0 || x 4) = (y 0 || y 4) ∧ g x = g y at hinv
  let old := List.ofFn x ++ [x 0 || x 4]
  let new := List.ofFn y ++ [y 0 || y 4]
  let a := GateOp.and.eval (l.map fun i => old.getD i.val false)
  let b := if c = 121 then true else new.getD (c / 11) false && new.getD (c % 11) false
  have mid : a = (new ++ [b]).getD j.val false := by
    have t := hprefix y
    cases s <;> simpa [x,p,Function.comp,old,new,a,b] using t
  have base : Rel (old ++ [a]) (new ++ [b]) := by
    refine ⟨by simp [old], by simp [old,new], ?_⟩
    intro i
    by_cases h : i < 9
    · have hr : r i = (p ⟨i,h⟩).val := by simp [r,h]
      rw [hr]
      have xold : i < old.length := by simp [old]; omega
      have xnew : (p ⟨i,h⟩).val < new.length := by have := (p ⟨i,h⟩).isLt; simp [new]; omega
      rw [List.getD_append _ _ _ _ xold,List.getD_append _ _ _ _ xnew]
      dsimp only [old,new]
      rw [List.getD_append _ _ _ _ (by simpa using h),List.getD_append _ _ _ _ (by simp)]
      rw [List.getD_eq_getElem _ _ (by simpa using h),List.getD_eq_getElem _ _ (by simp)]
      simpa only [List.getElem_ofFn] using (show x ⟨i,h⟩ = y (p ⟨i,h⟩) from rfl)
    · by_cases q : i = 9
      · subst i
        have r9 : r 9 = 9 := by simp [r]
        rw [r9]
        have U (v : Fin 9 → Bool) (z : Bool) :
            ((List.ofFn v ++ [v 0 || v 4]) ++ [z]).getD 9 false = (v 0 || v 4) := by simp
        exact (U x a).trans (hinv.1.trans (U y b).symm)
      · by_cases t : i = 10
        · subst i
          have r10 : r 10 = j.val := by simp [r]
          rw [r10]
          have le : old.length = 10 := by simp [old]
          calc
            (old ++ [a]).getD 10 false = a := by
              simpa only [le] using (show (old ++ [a]).getD old.length false = a by simp)
            _ = _ := mid
        · rw [rlarge (by omega)]
          rw [List.getD_eq_default _ _ (by simp [old]; omega),List.getD_eq_default _ _ (by simp [new]; omega)]
  have hpre := wire A _ _ base
  have n := hpre.2.2 A.output
  have hend := wire B _ _ (ext hpre (!(A.wires (old ++ [a])).getD A.output false))
  change (A.wires (old ++ [a])).getD A.output false = ((ren A).wires (new ++ [b])).getD (ren A).output false at n
  have endval := hend.2.2 B.output
  simp only [n] at endval
  refine ⟨x, ?_⟩
  change B.eval ((A.wires (old ++ [a])) ++ [!(A.wires (old ++ [a])).getD A.output false]) ≠ g x
  change (ren B).eval (((ren A).wires (new ++ [b])) ++ [!((ren A).wires (new ++ [b])).getD (ren A).output false]) ≠ g y at hy
  intro contra
  apply hy
  rw [← hinv.2,← contra]
  unfold Circuit.eval
  simpa only [n] using endval.symm
