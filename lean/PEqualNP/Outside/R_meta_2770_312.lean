import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 3500000 in
set_option maxRecDepth 4096 in
theorem PEqualNP.Outside.R_meta_2770_312
    (hSmall : ∀ (B : BinaryCircuit) (P : Finset ℕ) (q : Bool), B.size ≤ 11 →
      (q = true → B.output ∈ P) →
      (∀ g ∈ B.gates, ∃ a b : Bool, (a = true → g.left ∈ P) ∧ (b = true → g.right ∈ P) ∧
        (g.op = (fun x y => (x != a) && (y != b)) ∨ g.op = (fun x y => (x != a) || (y != b)))) →
      ¬ (∀ x : Fin 9 → Bool, (B.eval (List.ofFn x ++ [x 0 || x 3, false]) != q) =
        ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
          (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))))
    (hTight : ∀ (B : BinaryCircuit) (P : Finset ℕ) (q : Bool), B.size = 12 → 10 ∈ P → P.card ≤ 3 →
      (q = true → B.output ∈ P) →
      (∀ g ∈ B.gates, ∃ a b : Bool, (a = true → g.left ∈ P) ∧ (b = true → g.right ∈ P) ∧
        (g.op = (fun x y => (x != a) && (y != b)) ∨ g.op = (fun x y => (x != a) || (y != b)))) →
      ¬ (∀ x : Fin 9 → Bool, (B.eval (List.ofFn x ++ [x 0 || x 3, false]) != q) =
        ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
          (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))))) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   (x1.gates.length = (15 : ℕ) ∧       x1.output = (23 : ℕ) ∧         x1.gates[(0 : ℕ)]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [(0 : ℕ), (3 : ℕ)] : PEqualNP.CircuitLowerBounds.Gate } ∧           ∀ (x2 : ℕ) (x3 : x2 < x1.gates.length),             have x4 : PEqualNP.CircuitLowerBounds.Gate := x1.gates[x2];             have x5 : ℕ → Prop := fun (x5 : ℕ) => x5 < (9 : ℕ) + x2 ∨ x5 = (24 : ℕ);             have x6 : ℕ → ℕ := fun (x6 : ℕ) => if x6 < (9 : ℕ) then x6 else if x6 = (24 : ℕ) then (9 : ℕ) else x6 + (1 : ℕ);             x4 = { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [] : PEqualNP.CircuitLowerBounds.Gate } ∨ (∃ (x7 : ℕ), x5 x7 ∧ x4 = { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [x7] : PEqualNP.CircuitLowerBounds.Gate }) ∨ ∃ (x7 : ℕ) (x8 : ℕ), x5 x7 ∧ x5 x8 ∧ x6 x7 ≤ x6 x8 ∧ (x4 = { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x7, x8] : PEqualNP.CircuitLowerBounds.Gate } ∨ x4 = { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [x7, x8] : PEqualNP.CircuitLowerBounds.Gate })) →     (2 : ℕ) ≤ List.countP (fun (x3 : PEqualNP.CircuitLowerBounds.Gate) => x3.op.eval [Bool.false]) x1.gates → PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 ≠ fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) := by
  classical
  intro C shaped many computes
  let f := fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
    (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
  let form := fun g : Gate => g = ⟨.and, []⟩ ∨ (∃ a, g = ⟨.not, [a]⟩) ∨
    ∃ a b, g = ⟨.and, [a,b]⟩ ∨ g = ⟨.or, [a,b]⟩
  let notG := fun g : Gate => g.op.eval [false]
  let raw := fun (w : List Bool) (g : Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let bit := fun (w : List Bool) (g : BinaryGate) =>
    w ++ [g.op (w.getD g.left false) (w.getD g.right false)]
  let describe := fun (rs : List (ℕ × Bool)) (j : ℕ) => rs.getD j (10,false)
  let read := fun (w : List Bool) (t : ℕ × Bool) => w.getD t.1 false != t.2
  let allowed := fun (P : Finset ℕ) (g : BinaryGate) => ∃ a b : Bool,
    (a = true → g.left ∈ P) ∧ (b = true → g.right ∈ P) ∧
    (g.op = (fun x y => (x != a) && (y != b)) ∨ g.op = (fun x y => (x != a) || (y != b)))
  let link := fun (old : List Gate) (rs : List (ℕ × Bool)) (bs : List BinaryGate) (P : Finset ℕ) =>
    rs.length = 10 + old.length ∧ 10 ∈ P ∧
    (∀ t ∈ rs, t.1 < 11 + bs.length ∧ (t.2 = true → t.1 ∈ P)) ∧
    (∀ g ∈ bs, allowed P g) ∧
    ∀ (w : List Bool), w.length = 10 → ∀ i,
      read (bs.foldl bit (w ++ [false])) (describe rs i) = (old.foldl raw w).getD i false
  have rLen (gs : List Gate) (w : List Bool) : (gs.foldl raw w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih => simp (config := {congrConsts := false}) only [List.foldl_cons, ih, raw, List.length_append, List.length_singleton, List.length_cons, List.length_nil]; omega
  have bLen (gs : List BinaryGate) (w : List Bool) : (gs.foldl bit w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih => simp (config := {congrConsts := false}) only [List.foldl_cons, ih, bit, List.length_append, List.length_singleton, List.length_cons, List.length_nil]; omega
  have keep (gs : List BinaryGate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl bit w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih _ (by simp (config := {congrConsts := false}) [bit]; omega)]
      exact List.getD_append _ _ _ _ hi
  have last {α : Type} (w : List α) (r d : α) : (w ++ [r]).getD w.length d = r := by
    simp (config := {congrConsts := false}) [List.getD_eq_getElem?_getD]
  have dummy (bs : List BinaryGate) (w : List Bool) (hw : w.length = 10) :
      (bs.foldl bit (w ++ [false])).getD 10 false = false := by
    rw [keep _ _ _ (by simp (config := {congrConsts := false}) [hw]), ← hw]
    exact last w false false
  have described (old : List Gate) (rs : List (ℕ × Bool)) (bs : List BinaryGate) (P : Finset ℕ)
      (h : link old rs bs P) (i : ℕ) :
      (describe rs i).1 < 11 + bs.length ∧ ((describe rs i).2 = true → (describe rs i).1 ∈ P) := by
    dsimp only [describe]
    by_cases hi : i < rs.length
    · rw [List.getD_eq_getElem _ _ hi]
      exact h.2.2.1 _ (List.getElem_mem hi)
    · rw [List.getD_eq_default _ _ (by omega)]
      exact ⟨by dsimp; omega, fun _ => h.2.1⟩
  have extend (old : List Gate) (rs : List (ℕ × Bool)) (bs : List BinaryGate) (P T : Finset ℕ)
      (g : Gate) (tail : List BinaryGate) (q : ℕ × Bool) (h : link old rs bs P)
      (hPT : P ⊆ T) (hq : q.1 < 11 + (bs++tail).length) (hqP : q.2 = true → q.1 ∈ T)
      (hTail : ∀ g ∈ tail, allowed T g)
      (newEq : ∀ w : List Bool, w.length = 10 →
        read ((bs++tail).foldl bit (w++[false])) q =
          g.op.eval (g.inputs.map fun i => (old.foldl raw w).getD i false)) :
      link (old++[g]) (rs++[q]) (bs++tail) T := by
    refine ⟨by simp (config := {congrConsts := false}) [h.1]; omega, hPT h.2.1, ?_, ?_, ?_⟩
    · intro t ht
      rcases List.mem_append.mp ht with hi | hi
      · obtain ⟨h0,h1⟩ := h.2.2.1 t hi
        exact ⟨by simp (config := {congrConsts := false}); omega, fun hh => hPT (h1 hh)⟩
      · have htq : t = q := List.mem_singleton.mp hi
        subst t
        exact ⟨hq,hqP⟩
    · intro e he
      rcases List.mem_append.mp he with he | he
      · obtain ⟨a,b,ha,hb,hop⟩ := h.2.2.2.1 e he
        exact ⟨a,b,fun h => hPT (ha h),fun h => hPT (hb h),hop⟩
      · exact hTail e he
    · intro w hw i
      have hl : (old.foldl raw w).length = rs.length := by rw [rLen, hw, h.1]
      have rawLast : (old++[g]).foldl raw w = raw (old.foldl raw w) g := by
        simp (config := {congrConsts := false}) only [List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [rawLast]
      change read ((bs++tail).foldl bit (w++[false])) ((rs++[q]).getD i (10,false)) =
        ((old.foldl raw w) ++ [_]).getD i false
      by_cases hi : i < rs.length
      · rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ (by omega)]
        change read ((bs++tail).foldl bit (w++[false])) (describe rs i) = _
        have hv := (described old rs bs P h i).1
        change (((bs++tail).foldl bit (w++[false])).getD (describe rs i).1 false != (describe rs i).2) = _
        rw [List.foldl_append, keep _ _ _ (by rw [bLen]; simp (config := {congrConsts := false}) [hw]; omega)]
        exact h.2.2.2.2 w hw i
      · by_cases he : i = rs.length
        · rw [he, last, ← hl, last]
          exact newEq w hw
        · rw [List.getD_eq_default _ _ (by simp (config := {congrConsts := false}); omega), List.getD_eq_default _ _ (by simp (config := {congrConsts := false}) [hl]; omega)]
          change (((bs++tail).foldl bit (w++[false])).getD 10 false != false) = false
          rw [dummy _ _ hw]
          rfl
  have emit (old : List Gate) (rs : List (ℕ × Bool)) (bs : List BinaryGate) (P : Finset ℕ)
      (h : link old rs bs P) (g : Gate) (hg : form g) : ∃ rs' bs' T,
      link (old++[g]) rs' bs' T ∧
      bs'.length ≤ bs.length + (if notG g then 0 else 1) ∧
      T.card ≤ P.card + (if notG g then 1 else 0) := by
    rcases hg with rfl | ⟨a,rfl⟩ | ⟨a,b,hop⟩
    · refine ⟨rs++[(10,true)],bs,P,?_,?_,?_⟩
      · have z := extend old rs bs P P ⟨.and,[]⟩ [] (10,true) h (fun _ h => h)
          (by simp (config := {congrConsts := false}); omega) (fun _ => h.2.1) (by simp (config := {congrConsts := false})) ?_
        · simpa (config := {congrConsts := false}) only [List.append_nil] using z
        · intro w hw
          change (((bs++[]).foldl bit (w++[false])).getD 10 false != true) = true
          rw [dummy _ _ hw]
          rfl
      · change bs.length ≤ bs.length + 1
        omega
      · change P.card ≤ P.card + 0
        omega
    · let q := describe rs a
      let T := insert q.1 P
      refine ⟨rs++[(q.1,!q.2)],bs,T,?_,?_,?_⟩
      · have z := extend old rs bs P T ⟨.not,[a]⟩ [] (q.1,!q.2) h
          (fun _ h => Finset.mem_insert_of_mem h) (by simp (config := {congrConsts := false}); exact (described old rs bs P h a).1)
          (fun _ => Finset.mem_insert_self _ _) (by simp (config := {congrConsts := false})) ?_
        · simpa (config := {congrConsts := false}) only [List.append_nil] using z
        · intro w hw
          have oldEq := h.2.2.2.2 w hw a
          rw [List.append_nil]
          change ((bs.foldl bit (w++[false])).getD q.1 false != (!q.2)) =
            !((old.foldl raw w).getD a false)
          rw [← oldEq]
          change ((bs.foldl bit (w++[false])).getD q.1 false != (!q.2)) =
            !((bs.foldl bit (w++[false])).getD q.1 false != q.2)
          cases (bs.foldl bit (w++[false])).getD q.1 false <;> cases q.2 <;> rfl
      · exact Nat.le_refl _
      · change (insert q.1 P).card ≤ P.card + 1
        exact Finset.card_insert_le _ _
    · have bin (isOr : Bool) : ∃ rs' bs' T,
          link (old++[⟨if isOr then .or else .and,[a,b]⟩]) rs' bs' T ∧
          bs'.length ≤ bs.length+1 ∧ T.card ≤ P.card := by
        let l := describe rs a
        let r := describe rs b
        let op := fun u v : Bool => if isOr then (u != l.2) || (v != r.2) else (u != l.2) && (v != r.2)
        let bp : BinaryGate := ⟨op,l.1,r.1⟩
        let out : ℕ × Bool := (11+bs.length,false)
        refine ⟨rs++[out],bs++[bp],P,?_,by simp (config := {congrConsts := false}),le_rfl⟩
        refine extend old rs bs P P _ [bp] out h (fun _ h => h) (by simp (config := {congrConsts := false}) [out]) (by simp (config := {congrConsts := false}) [out]) ?_ ?_
        · intro bg hbg
          obtain rfl := List.mem_singleton.mp hbg
          exact ⟨l.2,r.2,(described old rs bs P h a).2,(described old rs bs P h b).2,
            by cases isOr <;> first | exact Or.inl rfl | exact Or.inr rfl⟩
        · intro w hw
          let W := bs.foldl bit (w++[false])
          have hW : W.length = 11+bs.length := by dsimp [W]; rw [bLen]; simp (config := {congrConsts := false}) [hw]
          have ea := h.2.2.2.2 w hw a
          have eb := h.2.2.2.2 w hw b
          rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
          change ((W ++ [op (W.getD l.1 false) (W.getD r.1 false)]).getD (11+bs.length) false != false) = _
          rw [← hW,last]
          change (op (W.getD l.1 false) (W.getD r.1 false) != false) =
            (if isOr then GateOp.or else GateOp.and).eval
              [(old.foldl raw w).getD a false,(old.foldl raw w).getD b false]
          rw [← ea,← eb]
          change (op (W.getD l.1 false) (W.getD r.1 false) != false) =
            (if isOr then GateOp.or else GateOp.and).eval [W.getD l.1 false != l.2,W.getD r.1 false != r.2]
          dsimp only [op]
          cases isOr <;> cases (W.getD l.1 false != l.2) <;> cases (W.getD r.1 false != r.2) <;> rfl
      rcases hop with rfl | rfl
      · exact bin false
      · exact bin true
  have compile (gs : List Gate) (hg : ∀ g ∈ gs, form g) :
      ∀ (old : List Gate) (rs : List (ℕ × Bool)) (bs : List BinaryGate) (P : Finset ℕ),
        link old rs bs P → ∃ rs' bs' T, link (old++gs) rs' bs' T ∧
          bs'.length + gs.countP notG ≤ bs.length + gs.length ∧ T.card ≤ P.card + gs.countP notG := by
    induction gs with
    | nil =>
      intro old rs bs P h
      exact ⟨rs,bs,P,by simpa (config := {congrConsts := false}) only [List.append_nil] using h,by simp (config := {congrConsts := false}),by simp (config := {congrConsts := false})⟩
    | cons g gs ih =>
      intro old rs bs P h
      obtain ⟨mid,bm,M,hm,hbm,hM⟩ := emit old rs bs P h g (hg g (List.mem_cons_self))
      obtain ⟨rs',bs',T,h',hb,hT⟩ := ih (fun e he => hg e (List.mem_cons_of_mem _ he))
        (old++[g]) mid bm M hm
      refine ⟨rs',bs',T,by simpa (config := {congrConsts := false}) only [List.append_assoc,List.singleton_append] using h',?_,?_⟩
      · rw [List.countP_cons, List.length_cons]
        cases hg' : notG g <;> simp (config := {congrConsts := false}) only [hg',Bool.false_eq_true,ite_false,ite_true, ↓reduceIte] at hbm ⊢ <;> omega
      · rw [List.countP_cons]
        cases hg' : notG g <;> simp (config := {congrConsts := false}) only [hg',Bool.false_eq_true,ite_false,ite_true, ↓reduceIte] at hM ⊢ <;> omega
  let start : List (ℕ × Bool) := List.ofFn fun i : Fin 10 => (i.val,false)
  have hStart : link [] start [] {10} := by
    refine ⟨by simp (config := {congrConsts := false}) [start],by simp (config := {congrConsts := false}),?_,by simp (config := {congrConsts := false}),?_⟩
    · intro t ht
      obtain ⟨i,hi⟩ := List.mem_ofFn.mp ht
      rw [← hi]
      exact ⟨by have := i.isLt; dsimp; omega, by simp (config := {congrConsts := false})⟩
    · intro w hw i
      by_cases hi : i < 10
      · have hs : i < start.length := by simp (config := {congrConsts := false}) [start,hi]
        change ((w++[false]).getD (start.getD i (10,false)).1 false != (start.getD i (10,false)).2) = w.getD i false
        have sr : start.getD i (10,false) = (i,false) := by
          rw [List.getD_eq_getElem _ _ hs]
          change (List.ofFn (fun j : Fin 10 => (j.val,false)))[i] = (i,false)
          rw [List.getElem_ofFn]
        rw [sr, List.getD_append _ _ _ _ (by omega)]
        cases w.getD i false <;> rfl
      · change ((w++[false]).getD (start.getD i (10,false)).1 false != (start.getD i (10,false)).2) = w.getD i false
        have hd : start.getD i (10,false) = (10,false) :=
          List.getD_eq_default _ _ (by change (List.ofFn (fun j : Fin 10 => (j.val,false))).length ≤ i; simp (config := {congrConsts := false}); omega)
        rw [hd, List.getD_eq_default w false (by omega)]
        change ((w++[false]).getD 10 false != false) = false
        have dz : (w++[false]).getD 10 false = false := dummy [] w hw
        rw [dz]
        rfl
  obtain ⟨lengthC,outputC,headC,slots⟩ := shaped
  cases hc : C.gates with
  | nil => simp (config := {congrConsts := false}) [hc] at lengthC
  | cons first gs =>
    rw [hc] at headC
    have firstEq : first = ⟨.or,[0,3]⟩ := Option.some.inj headC
    have lenGS : gs.length = 14 := by rw [hc,List.length_cons] at lengthC; omega
    have hForm : ∀ g ∈ gs, form g := by
      intro g hg
      obtain ⟨i,hi,hg'⟩ := List.mem_iff_getElem.mp hg
      have hj : i+1 < C.gates.length := by rw [hc,List.length_cons]; omega
      have hh := slots (i+1) hj
      have cg : C.gates[i+1] = g := by simpa (config := {congrConsts := false}) only [hc,List.getElem_cons_succ] using hg'
      dsimp only at hh
      rw [cg] at hh
      rcases hh with h | ⟨a,_,h⟩ | ⟨a,b,_,_,_,h⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨a,h⟩)
      · exact Or.inr (Or.inr ⟨a,b,h⟩)
    have manyGS : 2 ≤ gs.countP notG := by
      rw [hc,List.countP_cons,firstEq] at many
      exact many
    obtain ⟨rs,bs,P,hs,hb,hP⟩ := compile gs hForm [] start [] {10} hStart
    have hs' : link gs rs bs P := by simpa (config := {congrConsts := false}) only [List.nil_append] using hs
    let q := describe rs 23
    let B : BinaryCircuit := ⟨bs,q.1⟩
    have hp : q.2 = true → B.output ∈ P := (described _ _ _ _ hs' 23).2
    have hB : ∀ g ∈ B.gates, allowed P g := hs'.2.2.2.1
    have hCorrect : ∀ x : Fin 9 → Bool, (B.eval (List.ofFn x ++ [x 0 || x 3, false]) != q.2) = f x := by
      intro x
      let w := List.ofFn x ++ [x 0 || x 3]
      have hw : w.length = 10 := by simp (config := {congrConsts := false}) [w]
      have equiv := hs'.2.2.2.2 w hw 23
      have before : raw (List.ofFn x) first = w := by
        rw [firstEq]
        change List.ofFn x ++ [GateOp.or.eval _] = _
        have readX (i : Fin 9) : (List.ofFn x).getD i.val false = x i := by
          rw [List.getD_eq_getElem _ _ (by simp (config := {congrConsts := false})), List.getElem_ofFn]
        have readZero : (List.ofFn x).getD 0 false = x 0 := readX 0
        have readThree : (List.ofFn x).getD 3 false = x 3 := readX 3
        change List.ofFn x ++ [((List.ofFn x).getD 0 false || ((List.ofFn x).getD 3 false || false))] = _
        simp (config := {congrConsts := false}) only [w,readZero,readThree,Bool.or_false]
      have correct := congrFun computes x
      change (C.gates.foldl raw (List.ofFn x)).getD C.output false = _ at correct
      rw [hc,List.foldl_cons,outputC,before] at correct
      have target : ∀ y : Fin 9 → Bool, f y = ((y 0 && y 1) || (y 1 && y 2) ||
          (y 2 && y 3) || (y 3 && y 4) || (y 4 && y 0) || (y 0 && y 5) || (y 1 && y 6) ||
          (y 2 && y 7) || (y 3 && y 8) || (y 5 && y 7) || (y 6 && y 8) || (y 8 && y 5)) := by decide
      have eq := equiv.trans (correct.trans (target x).symm)
      change ((bs.foldl bit (List.ofFn x ++ [x 0 || x 3, false])).getD q.1 false != q.2) = f x
      change ((bs.foldl bit ((List.ofFn x ++ [x 0 || x 3]) ++ [false])).getD q.1 false != q.2) = f x at eq
      simpa (config := {congrConsts := false}) only [List.append_assoc, List.singleton_append] using eq
    rw [lenGS] at hb
    simp (config := {congrConsts := false}) only [List.length_nil,Nat.zero_add] at hb
    have hsize : B.size ≤ 12 := by change bs.length ≤ 12; omega
    by_cases lo : B.size ≤ 11
    · exact hSmall B P q.2 lo hp hB hCorrect
    · have same : B.size = 12 := by omega
      have bound : P.card ≤ 3 := by
        have e : bs.length = 12 := same
        change P.card ≤ 1 + gs.countP notG at hP
        omega
      exact hTight B P q.2 same hs'.2.1 bound hp hB hCorrect
