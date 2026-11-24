import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_3350_43
    (three : ∀ C : Circuit, FanInTwo C → circuitFun 9 C = (fun x : Fin 9 → Bool =>
        x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
        x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
        x 6 && x 8 || x 8 && x 5) →
      (∃ i j k : Fin C.gates.length, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
        (C.gates.get i).op = GateOp.not ∧ (C.gates.get j).op = GateOp.not ∧
        (C.gates.get k).op = GateOp.not) → 16 ≤ C.size)
    (raw : ∀ (D : Circuit) (v : Fin 9), v ∈ ([0,2,4,7] : List (Fin 9)) → FanInTwo D →
      (∀ i j : Fin D.gates.length, (D.gates.get i).op = GateOp.not →
        (D.gates.get j).op = GateOp.not → i = j) →
      (∀ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [x 4 || x 6, !x v]) =
        (fun x : Fin 9 → Bool =>
        x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
        x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
        x 6 && x 8 || x 8 && x 5) x) → 14 ≤ D.size)
    (inverse : ∀ (D : Circuit), FanInTwo D →
      (∀ i j : Fin D.gates.length, (D.gates.get i).op = GateOp.not →
        (D.gates.get j).op = GateOp.not → i = j) →
      (∀ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [x 4 || x 6, !(x 4 || x 6)]) =
        (fun x : Fin 9 → Bool =>
        x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
        x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
        x 6 && x 8 || x 8 && x 5) x) → 14 ≤ D.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (4 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) → Option.map (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => x5.op) x1.gates[(1 : ℕ)]? = Option.some PEqualNP.CircuitLowerBounds.GateOp.not → (16 : ℕ) ≤ x1.size := by
  intro C fan first complete second
  let f := (fun x : Fin 9 → Bool =>
        x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
        x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
        x 6 && x 8 || x 8 && x 5)
  change circuitFun 9 C = f at complete
  let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have keep (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl step w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      · simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · simp [step]; omega
  have notE (bs : List Bool) : GateOp.not.eval bs = !bs.headD false := rfl
  let perm (v i : Fin 9) : Fin 9 :=
    if v.val = 1 ∨ v.val = 5 ∨ v.val = 6 then ([1,0,5,8,6,2,4,7,3] : List (Fin 9)).getD i.val 0
    else if v.val = 3 then ([3,8,5,0,4,2,6,7,1] : List (Fin 9)).getD i.val 0
    else if v.val = 8 then ([8,3,2,1,6,5,4,7,0] : List (Fin 9)).getD i.val 0
    else i
  have seedClass : ∀ v, perm v v ∈ ([0,2,4,7] : List (Fin 9)) := by decide +kernel
  have firstInv : ∀ (v : Fin 9) (x : Fin 9 → Bool),
      (x (perm v 4) || x (perm v 6)) = (x 4 || x 6) := by decide +kernel
  have graphInv : ∀ (v : Fin 9) (x : Fin 9 → Bool), f (fun i => x (perm v i)) = f x := by decide +kernel
  have rawAll (A : Circuit) (v : Fin 9) (fanA : FanInTwo A)
      (uniqueA : ∀ i j : Fin A.gates.length, (A.gates.get i).op = GateOp.not →
        (A.gates.get j).op = GateOp.not → i = j)
      (correct : ∀ x : Fin 9 → Bool, A.eval (List.ofFn x ++ [x 4 || x 6, !x v]) = f x) :
      14 ≤ A.size := by
    let ren (j : ℕ) := if h : j < 9 then (perm v ⟨j,h⟩).val else j
    let rename (g : Gate) : Gate := ⟨g.op, g.inputs.map ren⟩
    let B : Circuit := ⟨A.gates.map rename, ren A.output⟩
    have fanB : FanInTwo B := by
      intro g hg
      obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hg
      obtain ⟨allowed,len⟩ := fanA q hq
      exact ⟨allowed, by simpa [rename] using len⟩
    have uniqueB : ∀ i j : Fin B.gates.length, (B.gates.get i).op = GateOp.not →
        (B.gates.get j).op = GateOp.not → i = j := by
      intro i j hi hj
      let narrow (k : Fin B.gates.length) : Fin A.gates.length := ⟨k.val, by simpa [B] using k.isLt⟩
      have atWire (k : Fin B.gates.length) : (B.gates.get k).op = (A.gates.get (narrow k)).op := by
        simp [B, rename, narrow, List.get_eq_getElem]
      have e := uniqueA _ _ ((atWire i).symm.trans hi) ((atWire j).symm.trans hj)
      exact Fin.ext (congrArg (fun k : Fin A.gates.length => k.val) e)
    have simulate (gs : List Gate) (w z : List Bool) (hl : w.length = z.length)
        (h9 : 9 ≤ w.length) (rel : ∀ j, w.getD j false = z.getD (ren j) false) :
        ∀ j, (gs.foldl step w).getD j false = ((gs.map rename).foldl step z).getD (ren j) false := by
      induction gs generalizing w z with
      | nil => exact rel
      | cons g gs ih =>
        simp only [List.map_cons, List.foldl_cons]
        have hz : (rename g).op.eval ((rename g).inputs.map fun i => z.getD i false) =
            g.op.eval (g.inputs.map fun i => w.getD i false) := by
          unfold rename
          simp only [List.map_map, Function.comp_def, rel]
        apply ih
        · simp [step, hl]
        · simp [step]; omega
        · intro j
          by_cases hj : j < w.length
          · have hr : ren j < z.length := by
              unfold ren; split
              next h => have := (perm v ⟨j,h⟩).isLt; omega
              next => omega
            simpa only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hj,
              List.getElem?_append_left hr] using rel j
          · have fixed : ren j = j := by simp [ren, show ¬j < 9 by omega]
            simp only [step, hz]
            simp only [fixed, List.getD_eq_getElem?_getD,
              List.getElem?_append_right (by omega : w.length ≤ j),
              List.getElem?_append_right (by omega : z.length ≤ j), hl, hz]
    have bound := raw B (perm v v) (seedClass v) fanB uniqueB (by
      intro x
      let y (i : Fin 9) := x (perm v i)
      let extra := [x 4 || x 6, !x (perm v v)]
      have rel (j : ℕ) : (List.ofFn y ++ extra).getD j false = (List.ofFn x ++ extra).getD (ren j) false := by
        by_cases hj : j < 9
        · have hr : ren j < 9 := by simpa [ren, hj] using (perm v ⟨j,hj⟩).isLt
          simp only [List.getD_eq_getElem?_getD,
            List.getElem?_append_left (by simpa using hj : j < (List.ofFn y).length),
            List.getElem?_append_left (by simpa using hr : ren j < (List.ofFn x).length),
            List.getElem?_ofFn, dite_eq_left hj, dite_eq_left hr]
          simp [ren, hj, y]
        · simp only [ren, dite_eq_right hj, List.getD_eq_getElem?_getD,
            List.getElem?_append_right (by simp; omega : (List.ofFn y).length ≤ j),
            List.getElem?_append_right (by simp; omega : (List.ofFn x).length ≤ j), List.length_ofFn]
      have hs := simulate A.gates (List.ofFn y ++ extra) (List.ofFn x ++ extra)
        (by simp) (by simp) rel A.output
      have ev := correct y
      change A.eval (List.ofFn y ++ [x (perm v 4) || x (perm v 6), !x (perm v v)]) = f y at ev
      rw [firstInv] at ev
      exact hs.symm.trans (ev.trans (graphInv v x)))
    change 14 ≤ (A.gates.map rename).length at bound
    change 14 ≤ A.gates.length
    simpa only [List.length_map] using bound
  have constant (A : Circuit) (fanA : FanInTwo A)
      (uniqueA : ∀ i j : Fin A.gates.length, (A.gates.get i).op = GateOp.not →
        (A.gates.get j).op = GateOp.not → i = j)
      (correct : ∀ x : Fin 9 → Bool, A.eval (List.ofFn x ++ [x 4 || x 6, true]) = f x) :
      14 ≤ A.size := by
    classical
    let fix (g : Gate) : Gate :=
      if 10 ∈ g.inputs then
        if g.op = .and then ⟨.and, g.inputs.filter (· != 10)⟩
        else if g.op = .or then ⟨.and, []⟩
        else if g.inputs.head? = some 10 then ⟨.or, []⟩ else g
      else g
    let B : Circuit := ⟨A.gates.map fix, A.output⟩
    have andE (l : List Bool) : GateOp.and.eval l = l.all id := rfl
    have orE (l : List Bool) : GateOp.or.eval l = l.any id := rfl
    have evalFix (g : Gate) (hg : g ∈ A.gates) (r s : ℕ → Bool)
        (ten : r 10 = true) (same : ∀ i, i ≠ 10 → r i = s i) :
        g.op.eval (g.inputs.map r) = (fix g).op.eval ((fix g).inputs.map s) := by
      have allowed := (fanA g hg).1
      have len := (fanA g hg).2
      rcases g with ⟨op,ins⟩
      change ins.length ≤ 2 at len
      change op = .and ∨ op = .or ∨ op = .not at allowed
      rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c,rest⟩⟩⟩
      · simp [fix]
      · by_cases ha : a = 10 <;> rcases allowed with rfl | rfl | rfl <;>
          simp [fix, andE, orE, notE, ha, ten, same, show (10 = a) ↔ a = 10 from eq_comm]
      · by_cases ha : a = 10 <;> by_cases hb : b = 10 <;> rcases allowed with rfl | rfl | rfl <;>
          simp [fix, andE, orE, notE, ha, hb, ten, same, show (10 = a) ↔ a = 10 from eq_comm, show (10 = b) ↔ b = 10 from eq_comm]
      · simp at len
    have fanB : FanInTwo B := by
      intro g hg
      obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hg
      have hf := fanA q hq
      unfold fix
      split
      · split
        · exact ⟨Or.inl rfl, (List.length_filter_le _ _).trans hf.2⟩
        · split
          · exact ⟨Or.inl rfl, by decide⟩
          · split
            · exact ⟨Or.inr (Or.inl rfl), by decide⟩
            · exact hf
      · exact hf
    have notBack (g : Gate) : (fix g).op = GateOp.not → g.op = GateOp.not := by
      unfold fix
      split <;> repeat' split
      all_goals simp
    have uniqueB : ∀ i j : Fin B.gates.length, (B.gates.get i).op = GateOp.not →
        (B.gates.get j).op = GateOp.not → i = j := by
      intro i j hi hj
      let narrow (k : Fin B.gates.length) : Fin A.gates.length := ⟨k.val, by simpa [B] using k.isLt⟩
      have atWire (k : Fin B.gates.length) : B.gates.get k = fix (A.gates.get (narrow k)) := by
        simp [B, narrow, List.get_eq_getElem]
      have e := uniqueA (narrow i) (narrow j) (notBack _ (atWire i ▸ hi)) (notBack _ (atWire j ▸ hj))
      exact Fin.ext (congrArg (fun k : Fin A.gates.length => k.val) e)
    have readSnoc (w : List Bool) (z : Bool) (i : ℕ) :
        (w ++ [z]).getD i false = if i < w.length then w.getD i false
          else if i = w.length then z else false := by
      by_cases h : i < w.length
      · simp [h, List.getD_eq_getElem?_getD, List.getElem?_append_left h]
      · by_cases he : i = w.length
        · subst i; simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]
        · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
          simp [h, he]
    have simulate (gs : List Gate) (valid : ∀ g ∈ gs, g ∈ A.gates) (w v : List Bool)
        (hl : w.length = v.length) (hw : 10 < w.length) (ht : w.getD 10 false = true)
        (rel : ∀ i, i ≠ 10 → w.getD i false = v.getD i false) :
        ∀ i, i ≠ 10 → (gs.foldl step w).getD i false =
          ((gs.map fix).foldl step v).getD i false := by
      induction gs generalizing w v with
      | nil => exact rel
      | cons g gs ih =>
        simp only [List.map_cons, List.foldl_cons]
        have ez := evalFix g (valid _ (by simp)) (fun i => w.getD i false) (fun i => v.getD i false) ht rel
        apply ih (fun q hq => valid q (by simp [hq]))
        · simp [step, hl]
        · simp [step]; omega
        · simpa only [step, readSnoc, ite_eq_left hw] using ht
        · intro i hi; simp only [step, readSnoc, hl, rel i hi, ez]
    have outputOk : A.output ≠ 10 := by
      intro he
      have e := correct (fun _ => false)
      change (A.gates.foldl step _).getD A.output false = false at e
      rw [he, keep _ _ _ (by simp)] at e
      contradiction
    have sizeB := rawAll B 0 fanB uniqueB (by
      intro x
      have h := simulate A.gates (fun _ h => h)
        (List.ofFn x ++ [x 4 || x 6, true]) (List.ofFn x ++ [x 4 || x 6, !x 0])
        (by simp) (by simp) (by rfl) (by
          intro i hi
          change ((List.ofFn x ++ [x 4 || x 6]) ++ [true]).getD i false =
            ((List.ofFn x ++ [x 4 || x 6]) ++ [!x 0]).getD i false
          simp only [readSnoc, List.length_append, List.length_ofFn, List.length_singleton]
          simp [hi]) A.output outputOk
      exact h.symm.trans (correct x))
    change 14 ≤ (A.gates.map fix).length at sizeB
    change 14 ≤ A.gates.length
    simpa only [List.length_map] using sizeB
  rcases C with ⟨gs, out⟩
  cases gs with
  | nil => cases second
  | cons g0 rest =>
    cases rest with
    | nil => cases second
    | cons g1 tail =>
      let C : Circuit := ⟨g0 :: g1 :: tail, out⟩
      let D : Circuit := ⟨tail, out⟩
      have op : g1.op = GateOp.not := Option.some.inj second
      have fanD : FanInTwo D := fun g hg =>
        fan g (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hg))
      by_cases many : ∃ i j : Fin tail.length,
          (tail.get i).op = GateOp.not ∧ (tail.get j).op = GateOp.not ∧ i ≠ j
      · obtain ⟨i,j,hi,hj,hij⟩ := many
        let lift (i : Fin tail.length) : Fin C.gates.length := ⟨i.val + 2, by simp [C]⟩
        let one : Fin C.gates.length := ⟨1, by simp [C]⟩
        apply three C fan complete
        refine ⟨one, lift i, lift j, ?_, ?_, ?_, op, ?_, ?_⟩
        · intro e; have h := congrArg Fin.val e; change 1 = i.val + 2 at h; omega
        · intro e; have h := congrArg Fin.val e; change 1 = j.val + 2 at h; omega
        · intro e; apply hij; apply Fin.ext
          have h := congrArg Fin.val e
          change i.val + 2 = j.val + 2 at h; omega
        · exact hi
        · exact hj
      have unique : ∀ i j : Fin D.gates.length, (D.gates.get i).op = GateOp.not →
          (D.gates.get j).op = GateOp.not → i = j := by
        intro i j hi hj
        by_contra hn
        exact many ⟨i,j,hi,hj,hn⟩
      let base (x : Fin 9 → Bool) := List.ofFn x ++ [x 4 || x 6]
      have head (x : Fin 9 → Bool) : step (List.ofFn x) g0 = base x := by
        have w9 := first x
        change ((g1 :: tail).foldl step (step (List.ofFn x) g0)).getD 9 false = _ at w9
        rw [keep _ _ _ (by simp [step])] at w9
        have eq : (step (List.ofFn x) g0).getD 9 false =
            g0.op.eval (g0.inputs.map fun i => (List.ofFn x).getD i false) := by
          simp [step, List.getD_eq_getElem?_getD, List.getElem?_append_right]
        rw [eq] at w9
        simp only [step, base, w9]
      have tailFun (x : Fin 9 → Bool) :
          D.eval (base x ++ [!((g1.inputs.map fun i => (base x).getD i false).headD false)]) = f x := by
        have hx := congrFun complete x
        change (tail.foldl step (step (step (List.ofFn x) g0) g1)).getD out false = f x at hx
        rw [head x] at hx
        change (tail.foldl step _).getD out false = f x
        simpa only [step, op, notE] using hx
      suffices bound : 14 ≤ D.size by
        change 14 ≤ tail.length at bound
        change 16 ≤ (g0 :: g1 :: tail).length
        simpa only [List.length_cons, Nat.add_le_add_iff_right] using Nat.succ_le_succ (Nat.succ_le_succ bound)
      cases ins : g1.inputs with
      | nil =>
        apply constant D fanD unique
        intro x
        simpa only [ins, List.map_nil, List.headD_nil, Bool.not_false, base, List.append_assoc,
          List.singleton_append] using tailFun x
      | cons a rest =>
        have values (x : Fin 9 → Bool) :
            D.eval (base x ++ [!(base x).getD a false]) = f x := by
          simpa only [ins, List.map_cons, List.headD_cons] using tailFun x
        by_cases ha : a < 9
        · apply rawAll D ⟨a,ha⟩ fanD unique
          intro x
          have eq : (base x).getD a false = x ⟨a,ha⟩ := by
            unfold base
            rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using ha), List.getElem?_ofFn]
            simp [ha]
          simpa only [eq, base, List.append_assoc, List.singleton_append] using values x
        · by_cases he : a = 9
          · apply inverse D fanD unique
            intro x
            subst a
            have eq : (base x).getD 9 false = (x 4 || x 6) := by rfl
            simpa only [eq, base, List.append_assoc, List.singleton_append] using values x
          · apply constant D fanD unique
            intro x
            have eq : (base x).getD a false = false := by
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [base]; omega)]; rfl
            simpa only [eq, Bool.not_false, base, List.append_assoc, List.singleton_append] using values x
