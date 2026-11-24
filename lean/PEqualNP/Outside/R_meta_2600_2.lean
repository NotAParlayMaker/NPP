import Mathlib.Tactic.FinCases
import PEqualNP.Defs

-- The known premise is the degree-one bound from L-meta-1500 in no-three-neighbors form.
-- Duality exchanges a point p with line -p and a line l with point -l.
-- This preserves the incidence predicate and exchanges the two marked sides.
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.R_meta_2600_2
    (known :
      let I := fun (p l : Fin 13) => p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9
      let F := fun (x : Fin 26 → Bool) => ∃ p l : Fin 13,
        I p l ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true
      let sparsePoints := fun (x : Fin 26 → Bool) =>
        ∀ l a b c : Fin 13,
          (I a l ∧ x (Fin.castAdd 13 a) = true) →
          (I b l ∧ x (Fin.castAdd 13 b) = true) →
          (I c l ∧ x (Fin.castAdd 13 c) = true) → a = b ∨ a = c ∨ b = c
      let pair := fun (p l : Fin 13) (i : Fin 26) =>
        decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l)
      ¬ ∃ E : Circuit, Monotone2 E ∧ E.size ≤ 63 ∧
        HasLineDegree 26 (Finset.Ico 13 26) E 1 ∧
        (∀ x : Fin 26 → Bool, sparsePoints x → E.eval (List.ofFn x) = true → F x) ∧
        ∀ p l : Fin 13, I p l → E.eval (List.ofFn (pair p l)) = true)
    (linearize :
      let I := fun (p l : Fin 13) => p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9
      let F := fun (x : Fin 26 → Bool) => ∃ p l : Fin 13,
        I p l ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true
      let side := fun (d : Bool) (i : Fin 13) =>
        if d then Fin.natAdd 13 i else Fin.castAdd 13 i
      let inc := fun (d : Bool) (u v : Fin 13) => if d then I v u else I u v
      let boundary := fun (d : Bool) (x : Fin 26 → Bool) =>
        (∀ v a b c : Fin 13,
          (inc d a v ∧ x (side d a) = true) →
          (inc d b v ∧ x (side d b) = true) →
          (inc d c v ∧ x (side d c) = true) → a = b ∨ a = c ∨ b = c) ∧
        ∀ v : Fin 13, x (side (!d) v) = true ↔
          ∀ u : Fin 13, inc d u v → x (side d u) = false
      let pair := fun (p l : Fin 13) (i : Fin 26) =>
        decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l)
      ∀ C : Circuit,
        PEqualNP.TopForm.IsAO2 26 C →
        (∀ g ∈ C.gates, g.inputs.Nodup) →
        (∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔ F x) →
        C.size ≤ 62 →
        ∃ (D : Circuit) (usePointDegree : Bool), Monotone2 D ∧ D.size ≤ C.size + 1 ∧
          HasLineDegree 26 (if usePointDegree then Finset.Ico 0 13 else Finset.Ico 13 26) D 1 ∧
          (∀ x : Fin 26 → Bool, boundary usePointDegree x → D.eval (List.ofFn x) = false) ∧
          ∀ p l : Fin 13, I p l → D.eval (List.ofFn (pair p l)) = true) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (26 : ℕ) + x2 ∧ x6 < (26 : ℕ) + x2) → (∀ (x3 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (13 : ℕ)) (x5 : Fin (13 : ℕ)), (x4 = x5 ∨ x4 = x5 + (1 : Fin (13 : ℕ)) ∨ x4 = x5 + (3 : Fin (13 : ℕ)) ∨ x4 = x5 + (9 : Fin (13 : ℕ))) ∧ x3 (Fin.castAdd (13 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (13 : ℕ) x5) = Bool.true) → (63 : ℕ) ≤ x1.size := by
  intro C legal computes
  by_contra budget
  have small : C.size ≤ 62 := by omega
  let I := fun (p l : Fin 13) => p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9
  let F := fun (x : Fin 26 → Bool) => ∃ p l : Fin 13,
    I p l ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true
  let sparsePoints := fun (x : Fin 26 → Bool) =>
    ∀ l a b c : Fin 13,
      (I a l ∧ x (Fin.castAdd 13 a) = true) →
      (I b l ∧ x (Fin.castAdd 13 b) = true) →
      (I c l ∧ x (Fin.castAdd 13 c) = true) → a = b ∨ a = c ∨ b = c
  let pair := fun (p l : Fin 13) (i : Fin 26) =>
    decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l)
  let sparseLines := fun (x : Fin 26 → Bool) =>
    ∀ p a b c : Fin 13,
      (I p a ∧ x (Fin.natAdd 13 a) = true) →
      (I p b ∧ x (Fin.natAdd 13 b) = true) →
      (I p c ∧ x (Fin.natAdd 13 c) = true) → a = b ∨ a = c ∨ b = c
  let flip := fun i : Fin 26 =>
    if i.val < 13 then Fin.natAdd 13 (-(Fin.ofNat 13 i.val))
    else Fin.castAdd 13 (-(Fin.ofNat 13 i.val))
  have flipPoint (p : Fin 13) : flip (Fin.castAdd 13 p) = Fin.natAdd 13 (-p) := by
    fin_cases p <;> decide +kernel
  have flipLine (l : Fin 13) : flip (Fin.natAdd 13 l) = Fin.castAdd 13 (-l) := by
    fin_cases l <;> decide +kernel
  have twice (i : Fin 26) : flip (flip i) = i := by
    fin_cases i <;> decide +kernel
  have preserves (p l : Fin 13) : I p l → I (-l) (-p) := by
    fin_cases p <;> fin_cases l <;> decide +kernel
  have switchMark (i : Fin 26) :
      i.val ∈ (Finset.Ico 0 13 : Finset ℕ) ↔ (flip i).val ∈ (Finset.Ico 13 26 : Finset ℕ) := by
    fin_cases i <;> decide +kernel
  let closedPoints := fun (x : Fin 26 → Bool) =>
    ∀ l : Fin 13, x (Fin.natAdd 13 l) = true ↔
      ∀ p : Fin 13, I p l → x (Fin.castAdd 13 p) = false
  let closedLines := fun (x : Fin 26 → Bool) =>
    ∀ p : Fin 13, x (Fin.castAdd 13 p) = true ↔
      ∀ l : Fin 13, I p l → x (Fin.natAdd 13 l) = false
  have shiftClosed (x : Fin 26 → Bool) (h : closedPoints x) : closedLines (x ∘ flip) := by
    intro p
    change (x ∘ flip) (Fin.castAdd 13 p) = true ↔
      ∀ l : Fin 13, I p l → (x ∘ flip) (Fin.natAdd 13 l) = false
    simp only [Function.comp_apply, flipPoint, flipLine]
    constructor
    · intro on l hit
      exact (h (-p)).mp on (-l) (preserves p l hit)
    · intro absent
      apply (h (-p)).mpr
      intro q hit
      have image : I p (-q) := by simpa only [neg_neg] using preserves q (-p) hit
      simpa only [neg_neg] using absent (-q) image
  have shiftPair (p l : Fin 13) : pair p l ∘ flip = pair (-l) (-p) := by
    have exchange (a b : Fin 26) : flip a = b ↔ a = flip b := by
      constructor
      · intro h
        rw [← h, twice]
      · intro h
        rw [h, twice]
    funext i
    have pEq : flip i = Fin.castAdd 13 p ↔ i = Fin.natAdd 13 (-p) := by
      rw [exchange, flipPoint]
    have lEq : flip i = Fin.natAdd 13 l ↔ i = Fin.castAdd 13 (-l) := by
      rw [exchange, flipLine]
    simp only [pair, Function.comp_apply, pEq, lEq, or_comm]
  have shiftSparse (x : Fin 26 → Bool) (sp : sparsePoints x) : sparseLines (x ∘ flip) := by
    rintro p a b c ⟨ia, va⟩ ⟨ib, vb⟩ ⟨ic, vc⟩
    simp only [Function.comp_apply, flipLine] at va vb vc
    have triple := sp (-p) (-a) (-b) (-c)
      ⟨preserves p a ia, va⟩ ⟨preserves p b ib, vb⟩ ⟨preserves p c ic, vc⟩
    have undo {i j : Fin 13} (h : -i = -j) : i = j := by
      simpa only [neg_neg] using congrArg (fun v : Fin 13 => -v) h
    exact triple.imp (fun h => undo h) (fun h => h.imp (fun e => undo e) (fun e => undo e))
  have transpose (D : Circuit) (legalD : Monotone2 D)
      (degreeD : HasLineDegree 26 (Finset.Ico 0 13) D 1) :
      ∃ E : Circuit, Monotone2 E ∧ E.size = D.size ∧
        HasLineDegree 26 (Finset.Ico 13 26) E 1 ∧
        ∀ x : Fin 26 → Bool, E.eval (List.ofFn x) = D.eval (List.ofFn (x ∘ flip)) := by
    let rename := fun i : ℕ => if h : i < 26 then (flip ⟨i, h⟩).val else i
    let move := fun g : Gate => (⟨g.op, g.inputs.map rename⟩ : Gate)
    let E : Circuit := ⟨D.gates.map move, rename D.output⟩
    let run := fun {T : Type} (d : T) (f : GateOp → List T → T) (w : List T) (g : Gate) =>
      w ++ [f g.op (g.inputs.map fun i => w.getD i d)]
    let related := fun {T : Type} (d : T) (u v : List T) =>
      26 ≤ u.length ∧ u.length = v.length ∧
        ∀ i, v.getD (rename i) d = u.getD i d
    have fixed (i : ℕ) (hi : 26 ≤ i) : rename i = i := dite_eq_right (Nat.not_lt_of_ge hi)
    have smallRename (i : ℕ) (hi : i < 26) : rename i < 26 := by
      simpa only [rename, dite_eq_left hi] using (flip ⟨i, hi⟩).isLt
    have step {T : Type} (d : T) (f : GateOp → List T → T)
        (u v : List T) (g : Gate) (r : related d u v) :
        related d (run d f u g) (run d f v (move g)) := by
      obtain ⟨min, len, values⟩ := r
      have gate : f (move g).op ((move g).inputs.map fun i => v.getD i d) =
          f g.op (g.inputs.map fun i => u.getD i d) := by
        simp only [move, List.map_map]
        congr 1
        exact List.map_congr_left (fun i _ => values i)
      refine ⟨by simp [run]; omega, by simp [run, len], ?_⟩
      intro i
      simp only [run, gate]
      rcases Nat.lt_trichotomy i u.length with before | ending | after
      · have other : rename i < v.length := by
          by_cases humble : i < 26
          · have := smallRename i humble
            omega
          · rw [fixed i (by omega)]
            omega
        rw [List.getD_append _ _ _ _ other, List.getD_append _ _ _ _ before]
        exact values i
      · have other : rename i = v.length := (fixed i (by omega)).trans (ending.trans len)
        rw [other, ending]
        simp
      · rw [fixed i (by omega)]
        rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    have fold {T : Type} (d : T) (f : GateOp → List T → T) (gs : List Gate)
        (u v : List T) (r : related d u v) :
        related d (gs.foldl (run d f) u) ((gs.map move).foldl (run d f) v) := by
      induction gs generalizing u v with
      | nil => exact r
      | cons g gs ih => exact ih _ _ (step d f _ _ _ r)
    have inputBit (x : Fin 26 → Bool) (i : Fin 26) :
        (List.ofFn x).getD i.val false = x i := by
      rw [List.getD_eq_getElem _ _ (by simp)]
      exact List.getElem_ofFn _
    have bits (x : Fin 26 → Bool) :
        related false (List.ofFn (x ∘ flip)) (List.ofFn x) := by
      refine ⟨by simp, by simp, ?_⟩
      intro i
      by_cases hi : i < 26
      · change (List.ofFn x).getD (rename i) false = (List.ofFn (x ∘ flip)).getD i false
        simp only [rename, dite_eq_left hi]
        rw [inputBit x (flip ⟨i, hi⟩)]
        exact (inputBit (x ∘ flip) ⟨i, hi⟩).symm
      · have large : 26 ≤ i := by omega
        rw [fixed i large, List.getD_eq_default _ _ (by simpa only [List.length_ofFn] using large),
          List.getD_eq_default _ _ (by simpa only [List.length_ofFn] using large)]
    let initial := fun M : Finset ℕ => (List.range 26).map fun i => if i ∈ M then 1 else 0
    have degValue (M : Finset ℕ) (i : ℕ) (hi : i < 26) :
        (initial M).getD i 0 = (if i ∈ M then 1 else 0) := by
      rw [List.getD_eq_getElem _ _ (by simpa [initial] using hi)]
      simp only [initial, List.getElem_map, List.getElem_range]
    have degrees : related 0 (initial (Finset.Ico 0 13)) (initial (Finset.Ico 13 26)) := by
      refine ⟨by simp [initial], by simp [initial], ?_⟩
      intro i
      by_cases hi : i < 26
      · change (initial (Finset.Ico 13 26)).getD (rename i) 0 =
          (initial (Finset.Ico 0 13)).getD i 0
        rw [degValue _ _ (smallRename i hi), degValue _ _ hi]
        simp only [rename, dite_eq_left hi, ← switchMark ⟨i, hi⟩]
      · have large : 26 ≤ i := by omega
        rw [fixed i large, List.getD_eq_default _ _ (by simpa [initial] using large),
          List.getD_eq_default _ _ (by simpa [initial] using large)]
    letI := lineDegreeGateOpDecEq
    let measure := fun (op : GateOp) (v : List ℕ) =>
      if op = .and then v.sum else v.foldr max 0
    have sameDeg : E.lineDeg 26 (Finset.Ico 13 26) = D.lineDeg 26 (Finset.Ico 0 13) :=
      (fold 0 measure D.gates _ _ degrees).2.2 D.output
    have sizeEq : E.size = D.size := by
      change (D.gates.map move).length = D.gates.length
      simp only [List.length_map]
    refine ⟨E, ?_, sizeEq, ?_, ?_⟩
    · intro g hg
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hg
      exact ⟨(legalD a ha).1, by simpa only [move, List.length_map] using (legalD a ha).2⟩
    · change E.lineDeg 26 (Finset.Ico 13 26) ≤ 1
      rw [sameDeg]
      exact degreeD
    · intro x
      exact (fold false GateOp.eval D.gates _ _ (bits x)).2.2 D.output

  have byMember (g : Gate) (hg : g ∈ C.gates) :
      (g.op = .and ∨ g.op = .or) ∧ ∃ a b : ℕ, g.inputs = [a, b] ∧ a ≠ b := by
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hg
    obtain ⟨op, a, b, pins, distinct, _⟩ := legal i g hi
    exact ⟨op, a, b, pins, distinct⟩
  have typed : PEqualNP.TopForm.IsAO2 26 C := by
    refine ⟨fun g hg => (byMember g hg).1, ?_, ?_⟩
    · intro i bound j hj
      let gate := PEqualNP.MetaComplexity.NestedCover.gateAt C i
      have atGate : C.gates[i]? = some gate := by
        change C.gates[i]? = some (C.gates.getD i ⟨.or, []⟩)
        rw [List.getElem?_eq_getElem bound, List.getD_eq_getElem _ _ bound]
      obtain ⟨_, a, b, pins, _, ha, hb⟩ := legal i gate atGate
      change j ∈ gate.inputs at hj
      rw [pins] at hj
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl <;> assumption
    · intro g hg
      obtain ⟨_, a, b, pins, _⟩ := byMember g hg
      rw [pins]
      rfl
  have distinct (g : Gate) (hg : g ∈ C.gates) : g.inputs.Nodup := by
    obtain ⟨_, a, b, pins, sep⟩ := byMember g hg
    simp [pins, sep]
  obtain ⟨D, byPoints, legalD, sizeD, degreeD, refuseD, pairsD⟩ :=
    linearize C typed distinct computes small
  have ready : ∃ E : Circuit, Monotone2 E ∧ E.size ≤ 63 ∧
      HasLineDegree 26 (Finset.Ico 13 26) E 1 ∧
      (∀ x : Fin 26 → Bool, sparsePoints x → closedPoints x → E.eval (List.ofFn x) = false) ∧
      ∀ p l : Fin 13, I p l → E.eval (List.ofFn (pair p l)) = true := by
    cases byPoints
    · refine ⟨D, legalD, by omega, degreeD, ?_, pairsD⟩
      exact fun x sp cp => refuseD x ⟨sp, cp⟩
    · obtain ⟨E, legalE, sizeE, degreeE, eval⟩ := transpose D legalD degreeD
      refine ⟨E, legalE, by omega, degreeE, ?_, ?_⟩
      · intro x sp cp
        rw [eval]
        exact refuseD _ ⟨shiftSparse x sp, shiftClosed x cp⟩
      · intro p l incident
        rw [eval, shiftPair]
        exact pairsD _ _ (preserves p l incident)
  obtain ⟨E, legalE, sizeE, degreeE, refuse, pairs⟩ := ready
  have mono (x y : Fin 26 → Bool) (le : ∀ i, x i = true → y i = true) :
      E.eval (List.ofFn x) = true → E.eval (List.ofFn y) = true := by
    let step := fun (w : List Bool) (g : Gate) =>
      w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    have andEval (l : List Bool) : GateOp.and.eval l = l.all id := rfl
    have orEval (l : List Bool) : GateOp.or.eval l = l.any id := rfl
    have propagate (gs : List Gate)
        (valid : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
        (a b : List Bool) (len : a.length = b.length)
        (sets : ∀ i, a.getD i false = true → b.getD i false = true) :
        ∀ i, (gs.foldl step a).getD i false = true → (gs.foldl step b).getD i false = true := by
      induction gs generalizing a b with
      | nil => exact sets
      | cons g gs ih =>
        rw [List.foldl_cons, List.foldl_cons]
        apply ih (fun g hg => valid g (List.mem_cons_of_mem _ hg))
          (step a g) (step b g) (by simp [step, len])
        have gate : g.op.eval (g.inputs.map (fun i => a.getD i false)) = true →
            g.op.eval (g.inputs.map (fun i => b.getD i false)) = true := by
          rcases valid g List.mem_cons_self with h | h
          · simp only [h, andEval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
            exact fun agree i hi => sets i (agree i hi)
          · simp only [h, orEval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
            rintro ⟨i, hi, good⟩
            exact ⟨i, hi, sets i good⟩
        intro i
        by_cases hi : i < a.length
        · simpa only [step, List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ (len ▸ hi)] using sets i
        · have ha : a.length ≤ i := Nat.le_of_not_gt hi
          simp only [step, List.getD_append_right _ _ _ _ ha,
            List.getD_append_right _ _ _ _ (len ▸ ha), ← len]
          cases i - a.length with
          | zero => exact gate
          | succ j => simp
    have initial (i : ℕ) : (List.ofFn x).getD i false = true → (List.ofFn y).getD i false = true := by
      by_cases hi : i < 26
      · rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using hi),
          List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using hi)]
        simp only [List.getElem_ofFn]
        exact le ⟨i, hi⟩
      · rw [List.getD_eq_default (List.ofFn x) _ (by simp; omega)]
        simp
    exact propagate E.gates (fun g hg => by simpa using (legalE g hg).1)
      (List.ofFn x) (List.ofFn y) (by simp) initial E.output
  apply known
  refine ⟨E, legalE, sizeE, degreeE, ?_, pairs⟩
  intro x sp accepted
  classical
  by_contra missed
  let y : Fin 26 → Bool := fun i => Fin.addCases (fun p => x (Fin.castAdd 13 p))
    (fun l => decide (∀ p : Fin 13, I p l → x (Fin.castAdd 13 p) = false)) i
  have sparse : sparsePoints y := by
    rintro l a b c ⟨ha, ax⟩ ⟨hb, bx⟩ ⟨hc, cx⟩
    simp only [y, Fin.addCases_left] at ax bx cx
    exact sp l a b c ⟨ha, ax⟩ ⟨hb, bx⟩ ⟨hc, cx⟩
  have closed : closedPoints y := by
    intro l
    simp only [y, Fin.addCases_left, Fin.addCases_right, decide_eq_true_eq]
  have dominates : ∀ i, x i = true → y i = true := by
    intro i
    refine Fin.addCases (m := 13) (n := 13) (motive := fun j => x j = true → y j = true) ?_ ?_ i
    · intro p hp
      simpa only [y, Fin.addCases_left] using hp
    · intro l hl
      simp only [y, Fin.addCases_right, decide_eq_true_eq]
      intro p hit
      cases seen : x (Fin.castAdd 13 p) with
      | false => rfl
      | true => exact (missed ⟨p, l, hit, seen, hl⟩).elim
  exact Bool.noConfusion ((mono x y dominates accepted).symm.trans (refuse y sparse closed))
