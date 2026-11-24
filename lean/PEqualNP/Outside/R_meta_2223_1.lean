import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover
open PEqualNP.GenericRejection

-- First prune unused gates. An internal wire read twice then forces a cheap
-- incidence in the diagonal matching, since the circuit has at most 27 gates.
-- The local step only needs to decrease the number of excess internal reads. On every assignment where toggling point 0
-- changes the output, its partner must be true at AND and false at OR.
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8192 in
theorem PEqualNP.Outside.R_meta_2223_1
    (prune : ∀ (n : ℕ) (C : Circuit),
      let shape := fun D : Circuit => ∀ (j : ℕ) (g : Gate), D.gates[j]? = some g →
        (g.op = .and ∨ g.op = .or) ∧
        ∃ a b, g.inputs = [a,b] ∧ a ≠ b ∧ a < n+j ∧ b < n+j
      shape C → ∃ D : Circuit, D.size ≤ C.size ∧ shape D ∧
        (∀ j < D.size, n+j ∈ D.output :: D.gates.flatMap Gate.inputs) ∧
        (∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x)) ∧
        ∀ s : Finset ℕ, D.lineDeg n s = C.lineDeg n s)
    (improve : let refs := fun C : Circuit => C.output :: C.gates.flatMap Gate.inputs
      let extra := fun C : Circuit => ((refs C).filter (fun w => decide (14 ≤ w))).length - C.size
      let good := fun (C : Circuit) (p l : Fin 7) => C.size ≤ 27 ∧ IsAO2 14 C ∧
        (∀ g ∈ C.gates, g.inputs.Nodup) ∧ (∀ j < C.size, 14+j ∈ refs C) ∧
        ComputesIncidence fanoLines C ∧ 2 ≤ C.lineDeg 14 {p.val} ∧ 2 ≤ C.lineDeg 14 {7+l.val}
      ∀ (C : Circuit) (p l : Fin 7), good C p l → p ∈ fanoLines l →
        (refs C).count 0 = 1 → (refs C).count 7 ≤ 2 →
        (∃ j < C.size, ∃ w, 14 ≤ w ∧ ((gateAt C j).inputs = [0,w] ∨ (gateAt C j).inputs = [w,0]) ∧
          ∀ x y : Fin 14 → Bool, (∀ i ≠ 0, x i = y i) → C.eval (List.ofFn x) ≠ C.eval (List.ofFn y) →
            ((C.wires (List.ofFn x)).getD w false = true ↔ (gateAt C j).op = .and)) →
        0 < extra C → ∃ D, good D p l ∧ extra D < extra C) :
    have x1 : Fin (7 : ℕ) → Fin (7 : ℕ) → Prop := fun (x1 x2 : Fin (7 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (7 : ℕ)) ∨ x1 = x2 + (3 : Fin (7 : ℕ)); have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => x2.size ≤ (27 : ℕ) ∧ (∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x3]? = Option.some x4 → (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x4.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x6 : ℕ) (x7 : ℕ), x4.inputs = [x6, x7] ∧ x6 ≠ x7 ∧ x6 < (14 : ℕ) + x3 ∧ x7 < (14 : ℕ) + x3) ∧ ∀ (x3 : Fin (14 : ℕ) → Bool), x2.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (7 : ℕ)) (x5 : Fin (7 : ℕ)), x1 x4 x5 ∧ x3 (Fin.castAdd (7 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (7 : ℕ) x5) = Bool.true; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => (List.filter (fun (x4 : ℕ) => Decidable.decide ((14 : ℕ) ≤ x4)) (x3.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x3.gates)).Nodup; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 x6 : Fin (7 : ℕ)), x2 x4 → x1 x5 x6 → (2 : ℕ) ≤ x4.lineDeg (14 : ℕ) {↑x5} → (2 : ℕ) ≤ x4.lineDeg (14 : ℕ) {(7 : ℕ) + ↑x6} → ∃ (x11 : PEqualNP.CircuitLowerBounds.Circuit), x2 x11 ∧ x3 x11 ∧ (2 : ℕ) ≤ x11.lineDeg (14 : ℕ) {↑x5} ∧ (2 : ℕ) ≤ x11.lineDeg (14 : ℕ) {(7 : ℕ) + ↑x6} := by
  classical
  let P (u : Fin 7) : Fin 14 := Fin.castAdd 7 u
  let L (u : Fin 7) : Fin 14 := Fin.natAdd 7 u
  let inc (u v : Fin 7) := u = v ∨ u = v+1 ∨ u = v+3
  let F (x : Fin 14 → Bool) := ∃ u v, inc u v ∧ x (P u) = true ∧ x (L v) = true
  let correct (C : Circuit) := ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ F x
  let shape (C : Circuit) := ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g →
    (g.op = .and ∨ g.op = .or) ∧ ∃ a b, g.inputs = [a,b] ∧ a ≠ b ∧ a < 14+j ∧ b < 14+j
  let refs (C : Circuit) := C.output :: C.gates.flatMap Gate.inputs
  let internal (C : Circuit) := (refs C).filter fun w => decide (14 ≤ w)
  let extra (C : Circuit) := (internal C).length - C.size
  let live (C : Circuit) := ∀ j < C.size, 14+j ∈ refs C
  let good (C : Circuit) (p l : Fin 7) := C.size ≤ 27 ∧ shape C ∧ live C ∧ correct C ∧
    2 ≤ C.lineDeg 14 {p.val} ∧ 2 ≤ C.lineDeg 14 {7+l.val}
  have dataShape (C : Circuit) : shape C ↔ IsAO2 14 C ∧ ∀ g ∈ C.gates, g.inputs.Nodup := by
    constructor
    · intro h
      have gate (g : Gate) (hg : g ∈ C.gates) :
          (g.op = .and ∨ g.op = .or) ∧ ∃ a b, g.inputs = [a,b] ∧ a ≠ b ∧ a < 14+C.size ∧ b < 14+C.size := by
        obtain ⟨j,hj⟩ := List.mem_iff_getElem?.mp hg
        obtain ⟨hop,a,b,he,hn,ha,hb⟩ := h j g hj
        have hlt : j < C.size := (List.getElem?_eq_some_iff.mp hj).1
        exact ⟨hop,a,b,he,hn,by omega,by omega⟩
      refine ⟨⟨fun g hg => (gate g hg).1, ?_, ?_⟩, ?_⟩
      · intro j hj i hi
        have H : C.gates[j]? = some (gateAt C j) := by
          change C.gates[j]? = some ((C.gates[j]?).getD ⟨.or,[]⟩)
          rw [List.getElem?_eq_getElem hj]
          rfl
        obtain ⟨a,b,he,_,ha,hb⟩ := (h j _ H).2
        simp only [he,List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl | rfl <;> assumption
      · intro g hg
        obtain ⟨a,b,he,_⟩ := (gate g hg).2
        simp [he]
      · intro g hg
        obtain ⟨a,b,he,hn,_⟩ := (gate g hg).2
        simp [he,hn]
    · rintro ⟨⟨hop,back,two⟩,nd⟩ j g hj
      have hm := List.mem_iff_getElem?.mpr ⟨j,hj⟩
      obtain ⟨a,b,hab⟩ := List.length_eq_two.mp (two g hm)
      obtain ⟨hj',he⟩ := List.getElem?_eq_some_iff.mp hj
      have hg : gateAt C j = g := by
        change (C.gates[j]?).getD ⟨.or,[]⟩ = g
        rw [hj]
        rfl
      have hb := back j hj'
      rw [hg, hab] at hb
      refine ⟨hop g hm,a,b,hab,?_,hb a (by simp),hb b (by simp)⟩
      simpa [hab] using nd g hm
  have memF : ∀ u v : Fin 7, u ∈ fanoLines v ↔ inc u v := by decide
  have dataCorrect (C : Circuit) : correct C ↔ ComputesIncidence fanoLines C := by
    let vec (X Y : Finset (Fin 7)) := Fin.append (fun i => decide (i ∈ X)) (fun j => decide (j ∈ Y))
    have listVec (X Y : Finset (Fin 7)) : List.ofFn (vec X Y) = incidenceInput X Y :=
      List.ofFn_fin_append _ _
    have valVec (X Y : Finset (Fin 7)) : F (vec X Y) ↔ incidenceFun fanoLines X Y = true := by
      change F (vec X Y) ↔ decide (∃ p ∈ X, ∃ l ∈ Y, p ∈ fanoLines l) = true
      simp only [F,P,L,vec,Fin.append_left,Fin.append_right,decide_eq_true_eq,memF]
      constructor
      · rintro ⟨u,v,hi,hx,hy⟩
        exact ⟨u,hx,v,hy,hi⟩
      · rintro ⟨u,hx,v,hy,hi⟩
        exact ⟨u,v,hi,hx,hy⟩
    constructor
    · intro h X Y
      apply Bool.eq_iff_iff.mpr
      rw [← listVec, h, valVec]
    · intro h x
      let X := Finset.univ.filter fun u => x (P u) = true
      let Y := Finset.univ.filter fun v => x (L v) = true
      have hx : vec X Y = x := by
        unfold vec
        simpa [X,Y,P,L] using (Fin.append_castAdd_natAdd (m := 7) (n := 7) (f := x))
      rw [← hx,listVec,h,← valVec]
  -- Every gate wire occurs among the reads. An internal repetition leaves at most 27 input reads.
  have counting (C : Circuit) (hc : C.size ≤ 27) (hs : shape C) (hl : live C)
      (hn : ¬(internal C).Nodup) :
      0 < extra C ∧ ∃ i : Fin 7, (refs C).count i.val + (refs C).count (7+i.val) ≤ 3 := by
    have hcovers : C.size ≤ (internal C).toFinset.card := by
      have h := Finset.card_le_card_of_injOn (s := Finset.range C.size) (t := (internal C).toFinset)
        (fun j : ℕ => 14+j) (by
          intro j hj
          have hj' : j < C.size := Finset.mem_range.mp hj
          simp [internal,hl j hj'] ) (by intro a ha b hb he; simpa using he)
      simpa using h
    have hlt : (internal C).toFinset.card < (internal C).length := by
      have hle := (internal C).toFinset_card_le
      have hne : (internal C).toFinset.card ≠ (internal C).length := by
        intro he
        apply hn
        exact (Multiset.toFinset_card_eq_card_iff_nodup (m := (↑(internal C) : Multiset ℕ))).mp he
      omega
    have hsum (xs : List ℕ) :
        (xs.filter (fun w => decide (14 ≤ w))).length +
          (∑ i : Fin 7, (xs.count i.val + xs.count (7+i.val))) = xs.length := by
      induction xs with
      | nil => simp
      | cons x xs ih =>
        have index (i : Fin 7) :
            (x::xs).count i.val + (x::xs).count (7+i.val) =
              xs.count i.val + xs.count (7+i.val) +
                ((if x = i.val then 1 else 0) + (if x = 7+i.val then 1 else 0)) := by
          simp only [List.count_cons,beq_iff_eq]
          omega
        simp only [index,Finset.sum_add_distrib,List.length_cons]
        by_cases hx : x < 14
        · have small : ∀ k : Fin 14, (∑ i : Fin 7,
              ((if k.val = i.val then 1 else 0) + (if k.val = 7+i.val then 1 else 0)) : ℕ) = 1 := by decide
          have e := small ⟨x,hx⟩
          change (∑ i : Fin 7, ((if x = i.val then 1 else 0) + (if x = 7+i.val then 1 else 0)) : ℕ) = 1 at e
          simp only [Finset.sum_add_distrib] at ih e
          simp only [List.filter_cons, decide_eq_true_eq, ite_eq_right (by omega : ¬14 ≤ x)]
          omega
        · have he (i : Fin 7) : x ≠ i.val ∧ x ≠ 7+i.val := by have := i.isLt; omega
          simp [he,show 14 ≤ x by omega,List.filter_cons,Finset.sum_add_distrib] at *
          omega
    have nrefs : (refs C).length = 2*C.size+1 := by
      have len : ∀ g ∈ C.gates, g.inputs.length = 2 := (dataShape C |>.mp hs).1.2.2
      have aux (gs : List Gate) (h : ∀ g ∈ gs, g.inputs.length = 2) :
          (gs.flatMap Gate.inputs).length = 2*gs.length := by
        induction gs with
        | nil => simp
        | cons g gs ih =>
          simp only [List.flatMap_cons,List.length_append,List.length_cons,h g (by simp),
            ih (fun k hk => h k (by simp [hk]))]
          omega
      change (C.output :: C.gates.flatMap Gate.inputs).length = 2*C.gates.length+1
      rw [List.length_cons,aux C.gates len]
    refine ⟨by dsimp [extra]; omega, ?_⟩
    by_contra! hall
    have lower : (∑ _ : Fin 7, 4) ≤ (∑ i : Fin 7,
        ((refs C).count i.val + (refs C).count (7+i.val))) :=
      Finset.sum_le_sum fun i _ => hall i
    norm_num at lower
    have total := hsum (refs C)
    change (internal C).length + _ = _ at total
    omega
  -- Translations and point-line duality take the cheap matched pair to wires 0 and 7.
  let perm (t : Fin 7) (s : Bool) : Fin 14 → Fin 14 := Fin.append
    (fun u => if s then L (t-u) else P (u-t))
    (fun v => if s then P (t-v) else L (v-t))
  let back (t : Fin 7) (s : Bool) := if s then t else -t
  let flag (t : Fin 7) (s : Bool) (u v : Fin 7) : Fin 7 × Fin 7 :=
    if s then (t-v,t-u) else (u-t,v-t)
  have undo : ∀ t s i, perm (back t s) s (perm t s i) = i := by decide
  have undoB : ∀ t s, back (back t s) s = t := by decide
  have undoF : ∀ t s u v, flag (back t s) s (flag t s u v).1 (flag t s u v).2 = (u,v) := by decide
  have mapInc : ∀ t s u v, inc u v → inc (flag t s u v).1 (flag t s u v).2 := by decide
  have mapEnds : ∀ t s u v, ((perm t s (P u), perm t s (L v)) =
      if s then (L (flag t s u v).2, P (flag t s u v).1)
      else (P (flag t s u v).1, L (flag t s u v).2)) := by decide
  let M (t : Fin 7) (s : Bool) (w : ℕ) := if h : w < 14 then (perm t s ⟨w,h⟩).val else w
  have Mh (t : Fin 7) (s : Bool) (i : Fin 14) : M t s i.val = (perm t s i).val := by simp [M,i.isLt]
  have Mt (t : Fin 7) (s : Bool) (w : ℕ) (h : 14 ≤ w) : M t s w = w := by simp [M,show ¬ w<14 by omega]
  have Minj (t : Fin 7) (s : Bool) : Function.Injective (M t s) := by
    apply Function.LeftInverse.injective (g := M (back t s) s)
    intro w
    by_cases h : w < 14
    · let i : Fin 14 := ⟨w,h⟩
      change M (back t s) s (M t s i.val) = i.val
      rw [Mh,Mh,undo]
    · rw [Mt t s w (by omega),Mt (back t s) s w (by omega)]
  have Mlt (t : Fin 7) (s : Bool) (w k : ℕ) (hk : 14 ≤ k) : M t s w < k ↔ w < k := by
    by_cases hw : w < 14
    · have hp := (perm t s ⟨w,hw⟩).isLt
      simp only [M,dite_eq_left hw]
      omega
    · rw [Mt _ _ _ (by omega)]
  let gate (t : Fin 7) (s : Bool) (g : Gate) : Gate := ⟨g.op,g.inputs.map (M t s)⟩
  let ren (t : Fin 7) (s : Bool) (C : Circuit) : Circuit := ⟨C.gates.map (gate t s), M t s C.output⟩
  have sizeRen (t : Fin 7) (s : Bool) (C : Circuit) : (ren t s C).size = C.size := List.length_map _
  have refsRen (t : Fin 7) (s : Bool) (C : Circuit) : refs (ren t s C) = (refs C).map (M t s) := by
    simp [ren,refs,gate,List.flatMap_map,List.map_flatMap]
  have extraRen (t : Fin 7) (s : Bool) (C : Circuit) : extra (ren t s C) = extra C := by
    simp only [extra,internal,refsRen,sizeRen]
    congr 1
    rw [List.filter_map,List.length_map]
    congr 2
    funext w
    simp only [Function.comp_apply]
    apply Bool.decide_congr
    have := Mlt t s w 14 (by omega)
    omega
  have scanRen (α : Type) (d : α) (op : GateOp → List α → α) (t : Fin 7) (s : Bool)
      (gs : List Gate) (X Y : List α) (hX : 14 ≤ X.length) (hlen : Y.length = X.length)
      (hread : ∀ i, Y.getD (M t s i) d = X.getD i d) :
      let step := fun (xs : List α) (g : Gate) => xs ++ [op g.op (g.inputs.map (fun i => xs.getD i d))]
      ∀ i, ((gs.map (gate t s)).foldl step Y).getD (M t s i) d = (gs.foldl step X).getD i d := by
    induction gs generalizing X Y with
    | nil => exact hread
    | cons g gs ih =>
      let v := op g.op (g.inputs.map fun i => X.getD i d)
      have hv : op (gate t s g).op ((gate t s g).inputs.map (fun i => Y.getD i d)) = v := by
        simp only [v,gate,List.map_map,Function.comp_def,hread]
      dsimp only
      simp only [List.map_cons,List.foldl_cons,hv]
      apply ih (X ++ [v]) (Y ++ [v]) (by simp; omega) (by simp [hlen])
      intro i
      rcases lt_trichotomy i X.length with hi | hi | hi
      · rw [List.getD_append _ _ _ _ (hlen ▸ (Mlt t s i X.length hX).mpr hi),
          List.getD_append _ _ _ _ hi,hread]
      · rw [Mt t s i (by omega),List.getD_append_right _ _ _ _ (by omega),
          List.getD_append_right _ _ _ _ (by omega),hlen]
      · rw [Mt t s i (by omega),List.getD_eq_default _ _ (by simp; omega),
          List.getD_eq_default _ _ (by simp; omega)]
  have valRen (t : Fin 7) (s : Bool) (C : Circuit) (x : Fin 14 → Bool) :
      (ren t s C).eval (List.ofFn x) = C.eval (List.ofFn (x ∘ perm t s)) := by
    apply scanRen Bool false GateOp.eval t s C.gates _ _ (by simp) (by simp) _ C.output
    intro w
    by_cases h : w < 14
    · let i : Fin 14 := ⟨w,h⟩
      change (List.ofFn x).getD (M t s i.val) false = (List.ofFn (x ∘ perm t s)).getD i.val false
      rw [Mh, List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simp)]
      simp only [List.getElem_ofFn,Function.comp_apply]
    · rw [Mt _ _ _ (by omega),List.getD_eq_default _ _ (by simp; omega),
        List.getD_eq_default _ _ (by simp; omega)]
  have degRen (t : Fin 7) (s : Bool) (C : Circuit) (a : Fin 14) :
      (ren t s C).lineDeg 14 {(perm t s a).val} = C.lineDeg 14 {a.val} := by
    let op (o : GateOp) (ds : List ℕ) := @ite ℕ (o = .and) (lineDegreeGateOpDecEq o .and) ds.sum (ds.foldr max 0)
    let inp (b : Fin 14) := (List.range 14).map (fun i => if i ∈ ({b.val} : Finset ℕ) then 1 else 0)
    have ini (b i : Fin 14) : (inp b).getD i.val 0 = if i=b then 1 else 0 := by
      rw [List.getD_eq_getElem _ _ (by simp [inp])]
      simp [inp, Fin.ext_iff]
    have hw (w : ℕ) : (inp (perm t s a)).getD (M t s w) 0 = (inp a).getD w 0 := by
      by_cases h : w < 14
      · let i : Fin 14 := ⟨w,h⟩
        change (inp (perm t s a)).getD (M t s i.val) 0 = (inp a).getD i.val 0
        rw [Mh,ini,ini]
        congr 1
        exact propext ⟨fun e => by simpa only [undo] using congrArg (perm (back t s) s) e,
          congrArg _⟩
      · rw [Mt _ _ _ (by omega),List.getD_eq_default _ _ (by simp [inp]; omega),
          List.getD_eq_default _ _ (by simp [inp]; omega)]
    exact scanRen ℕ 0 op t s C.gates (inp a) (inp (perm t s a)) (by simp [inp]) (by simp [inp]) hw C.output
  have forwardF (t : Fin 7) (s : Bool) (x : Fin 14 → Bool) : F (x ∘ perm t s) → F x := by
    rintro ⟨u,v,hi,hp,hl⟩
    refine ⟨_,_,mapInc t s u v hi,?_⟩
    have hh := mapEnds t s u v
    cases s <;> simp only [Bool.false_eq_true,ite_false,ite_true,Prod.mk.injEq] at hh <;>
      simp only [Function.comp_apply,hh.1,hh.2] at hp hl <;> exact ⟨by assumption,by assumption⟩
  have renGood (t : Fin 7) (s : Bool) (C : Circuit) (u v : Fin 7) (h : good C u v) :
      good (ren t s C) (flag t s u v).1 (flag t s u v).2 := by
    obtain ⟨hsize,hs,hl,hf,hu,hv⟩ := h
    refine ⟨by simpa only [sizeRen] using hsize,?_,?_,?_,?_⟩
    · intro j g hj
      change (C.gates.map (gate t s))[j]? = some g at hj
      rw [List.getElem?_map] at hj
      obtain ⟨g',hg',rfl⟩ := Option.map_eq_some_iff.mp hj
      obtain ⟨hop,a,b,ha,hn,hx,hy⟩ := hs j g' hg'
      refine ⟨hop,M t s a,M t s b,by simp [gate,ha],(Minj t s).ne hn,
        (Mlt _ _ _ _ (by omega)).mpr hx,(Mlt _ _ _ _ (by omega)).mpr hy⟩
    · intro j hj
      rw [refsRen,← Mt t s (14+j) (by omega)]
      exact List.mem_map_of_mem (hl j ((sizeRen t s C) ▸ hj))
    · intro x
      rw [valRen,hf]
      refine ⟨forwardF t s x,?_⟩
      intro hx
      apply forwardF (back t s) s (x ∘ perm t s)
      have ecomp : (x ∘ perm t s) ∘ perm (back t s) s = x := by
        funext i
        exact congrArg x (by simpa only [undoB] using undo (back t s) s i)
      rwa [ecomp]
    · have hp := degRen t s C (P u)
      have hq := degRen t s C (L v)
      have hh := mapEnds t s u v
      cases s <;> simp only [Bool.false_eq_true,ite_false,ite_true,Prod.mk.injEq] at hh <;>
        rw [hh.1] at hp <;> rw [hh.2] at hq <;>
        simp only [P,L,Fin.val_castAdd,Fin.val_natAdd] at hp hq <;> omega
  -- A sole reader must pass every change in the output caused by toggling its input.
  let step (xs : List Bool) (g : Gate) := xs ++ [g.op.eval (g.inputs.map fun i => xs.getD i false)]
  have readInput (C : Circuit) (x : Fin 14 → Bool) (j : Fin 14) (ho : C.output = j.val) :
      C.eval (List.ofFn x) = x j := by
    have extendsRun (gs : List Gate) (w : List Bool) : ∃ tail, gs.foldl step w = w ++ tail := by
      induction gs generalizing w with
      | nil => exact ⟨[],by simp⟩
      | cons g gs ih =>
        obtain ⟨tail,he⟩ := ih (step w g)
        exact ⟨_,by simpa [List.foldl_cons,step,List.append_assoc] using he⟩
    obtain ⟨tail,ht⟩ := extendsRun C.gates (List.ofFn x)
    change (C.gates.foldl step (List.ofFn x)).getD C.output false = _
    rw [ht,ho,List.getD_append _ _ _ _ (by simp),List.getD_eq_getElem _ _ (by simp)]
    simp only [List.getElem_ofFn]
  have notInput (C : Circuit) (hc : correct C) (j : Fin 14) : C.output ≠ j.val := by
    intro he
    let x : Fin 14 → Bool := fun i => decide (i=j)
    have hf : F x := (hc x).mp (by rw [readInput C x j he]; simp [x])
    have none : ∀ j : Fin 14, ¬F (fun i => decide (i=j)) := by unfold F inc P L; decide
    exact none j hf
  have primary (z : Fin 14 → Bool) (hs : List Bool) (j : Fin 14) :
      (List.ofFn z ++ hs).getD j.val false = z j := by
    rw [List.getD_append _ _ _ _ (by simp),List.getD_eq_getElem _ _ (by simp)]
    simp only [List.getElem_ofFn]
  have same (t : Fin 14) (x y : Fin 14 → Bool) (hxy : ∀ j ≠ t, x j = y j)
      (hs : List Bool) (w : ℕ) (hw : w ≠ t.val) :
      (List.ofFn x ++ hs).getD w false = (List.ofFn y ++ hs).getD w false := by
    by_cases h : w < 14
    · exact (primary x hs ⟨w,h⟩).trans ((hxy ⟨w,h⟩ (fun e => hw (congrArg Fin.val e))).trans
        (primary y hs ⟨w,h⟩).symm)
    · rw [List.getD_append_right _ _ _ _ (by simp; omega),
        List.getD_append_right _ _ _ _ (by simp; omega),List.length_ofFn,List.length_ofFn]
  have common (t : Fin 14) (x y : Fin 14 → Bool) (hxy : ∀ j ≠ t, x j = y j)
      (gs : List Gate) (hn : t.val ∉ gs.flatMap Gate.inputs) (hist : List Bool) :
      ∃ out, gs.foldl step (List.ofFn x ++ hist) = List.ofFn x ++ out ∧
        gs.foldl step (List.ofFn y ++ hist) = List.ofFn y ++ out := by
    induction gs generalizing hist with
    | nil => exact ⟨hist,rfl,rfl⟩
    | cons g gs ih =>
      simp only [List.flatMap_cons,List.mem_append,not_or] at hn
      let read (z : Fin 14 → Bool) (i : ℕ) := (List.ofFn z ++ hist).getD i false
      have he : g.op.eval (g.inputs.map (read x)) = g.op.eval (g.inputs.map (read y)) := by
        congr 1
        exact List.map_congr_left fun w hw => same t x y hxy hist w (fun e => hn.1 (e ▸ hw))
      obtain ⟨out,hx,hy⟩ := ih hn.2 (hist ++ [g.op.eval (g.inputs.map (read y))])
      refine ⟨out,?_,?_⟩
      · rw [List.foldl_cons]
        change gs.foldl step ((List.ofFn x ++ hist) ++ [g.op.eval (g.inputs.map (read x))]) = _
        rwa [he,List.append_assoc]
      · simpa only [List.foldl_cons,step,List.append_assoc,read] using hy
  have allRead (C : Circuit) (hf : correct C) (t : Fin 14) : 0 < (refs C).count t.val := by
    apply List.count_pos_iff.mpr
    by_contra h
    have tests : ∀ t : Fin 14, ∃ j : Fin 14,
        F (fun i => decide (i=j ∨ i=t)) ∧ ¬F (fun i => decide (i=j)) := by unfold F inc P L; decide
    obtain ⟨j,h1,h0⟩ := tests t
    let x (i : Fin 14) := decide (i=j ∨ i=t)
    let y (i : Fin 14) := decide (i=j)
    have hxy : ∀ i ≠ t, x i = y i := by intro i hi; simp [x,y,hi]
    obtain ⟨out,hx,hy⟩ := common t x y hxy C.gates (fun hm => h (List.mem_cons_of_mem _ hm)) []
    simp only [List.append_nil] at hx hy
    have he : C.eval (List.ofFn x) = C.eval (List.ofFn y) := by
      change (C.gates.foldl step (List.ofFn x)).getD _ false = (C.gates.foldl step (List.ofFn y)).getD _ false
      rw [hx,hy]
      exact same t x y hxy out _ (notInput C hf t)
    exact h0 ((hf y).mp (he.symm.trans ((hf x).mpr h1)))
  let sensitive (C : Circuit) (g : Gate) (w : ℕ) := ∀ x y : Fin 14 → Bool,
    (∀ i ≠ 0, x i = y i) → C.eval (List.ofFn x) ≠ C.eval (List.ofFn y) →
    ((C.wires (List.ofFn x)).getD w false = true ↔ g.op = .and)
  have sole (C : Circuit) (hf : correct C) (hs : shape C) (h1 : (refs C).count 0 = 1) :
      ∃ j < C.size, ∃ w, 14 ≤ w ∧ ((gateAt C j).inputs = [0,w] ∨ (gateAt C j).inputs = [w,0]) ∧
        sensitive C (gateAt C j) w := by
    have ho : C.output ≠ 0 := notInput C hf 0
    have hc : (C.gates.flatMap Gate.inputs).count 0 = 1 := by simpa [refs,List.count_cons,ho] using h1
    obtain ⟨g,hg,hm⟩ := List.mem_flatMap.mp (List.count_pos_iff.mp (by omega : 0 < (C.gates.flatMap Gate.inputs).count 0))
    obtain ⟨pre,post,splitC,_⟩ := List.eq_append_cons_of_mem hg
    let j := pre.length
    have hj : C.gates[j]? = some g := by rw [splitC,List.getElem?_append_right (show pre.length ≤ j from le_rfl)]; simp [j]
    have hj' : j < C.size := (List.getElem?_eq_some_iff.mp hj).1
    have gat : gateAt C j = g := by
      change (C.gates[j]?).getD ⟨.or,[]⟩ = g
      rw [hj]
      rfl
    obtain ⟨hop,a,b,hab,hn,ha,hb⟩ := hs j g hj
    rw [splitC,List.flatMap_append,List.flatMap_cons,List.count_append,List.count_append] at hc
    have hpos := List.count_pos_iff.mpr hm
    have hpre : 0 ∉ pre.flatMap Gate.inputs := by intro h; have := List.count_pos_iff.mpr h; omega
    have hpost : 0 ∉ post.flatMap Gate.inputs := by intro h; have := List.count_pos_iff.mpr h; omega
    have and2 (u v : Bool) : GateOp.and.eval [u,v] = (u && v) := by cases u <;> cases v <;> rfl
    have or2 (u v : Bool) : GateOp.or.eval [u,v] = (u || v) := by cases u <;> cases v <;> rfl
    have window (w : ℕ) (hw : w ≠ 0) (early : w < 14+j) (hgates : g.inputs = [0,w] ∨ g.inputs = [w,0]) :
        sensitive C g w := by
      intro x y hxy hdiff
      obtain ⟨hist,hx,hy⟩ := common 0 x y hxy pre hpre []
      simp only [List.append_nil] at hx hy
      let read (z : Fin 14 → Bool) (i : ℕ) := (List.ofFn z ++ hist).getD i false
      have keep (gs : List Gate) (ws : List Bool) (i : ℕ) (hi : i < ws.length) :
          (gs.foldl step ws).getD i false = ws.getD i false := by
        induction gs generalizing ws with
        | nil => rfl
        | cons k ks ih =>
          rw [List.foldl_cons,ih _ (by simp [step]; omega)]
          exact List.getD_append _ _ _ _ hi
      have lens (gs : List Gate) (ws : List Bool) : (gs.foldl step ws).length = ws.length+gs.length := by
        induction gs generalizing ws with
        | nil => simp
        | cons k ks ih => simp only [List.foldl_cons,ih,step,List.length_append,List.length_cons,List.length_nil]; omega
      have hwires : (C.wires (List.ofFn x)).getD w false = read x w := by
        change (C.gates.foldl step (List.ofFn x)).getD w false = _
        rw [splitC,List.foldl_append,keep _ _ _ (by simpa only [lens,List.length_ofFn] using early),hx]
      rw [hwires]
      by_contra h
      have vw : read x w = read y w := same 0 x y hxy hist w hw
      have he : g.op.eval (g.inputs.map (read x)) = g.op.eval (g.inputs.map (read y)) := by
        rcases hop with op | op
        · have hval : read x w = false := by
            cases v : read x w <;> simp [v,op] at h ⊢
          have hval' := vw.symm.trans hval
          rcases hgates with inputs | inputs <;> simp [inputs,op,and2,hval,hval']
        · have hval : read x w = true := by
            cases v : read x w <;> simp [v,op] at h ⊢
          have hval' := vw.symm.trans hval
          rcases hgates with inputs | inputs <;> simp [inputs,op,or2,hval,hval']
      let val := g.op.eval (g.inputs.map (read y))
      obtain ⟨out,hx',hy'⟩ := common 0 x y hxy post hpost (hist ++ [val])
      apply hdiff
      change (C.gates.foldl step (List.ofFn x)).getD C.output false = (C.gates.foldl step (List.ofFn y)).getD C.output false
      simp only [splitC,List.foldl_append,hx,hy,List.foldl_cons]
      change (post.foldl step ((List.ofFn x ++ hist) ++ [g.op.eval (g.inputs.map (read x))])).getD C.output false =
        (post.foldl step ((List.ofFn y ++ hist) ++ [val])).getD C.output false
      rw [he,List.append_assoc,List.append_assoc,hx',hy']
      exact same 0 x y hxy out _ ho
    have partner (w : ℕ) (hw : w ≠ 0) (sense : sensitive C g w) : 14 ≤ w := by
      by_contra! hsmall
      let q : Fin 14 := ⟨w,hsmall⟩
      let test (q j : Fin 14) (sat toggle : Bool) (i : Fin 14) :=
        decide (i=j ∨ (sat=true ∧ i=q) ∨ (toggle=true ∧ i=0))
      have existsTest : ∀ q : Fin 14, q ≠ 0 → ∀ sat : Bool, ∃ j : Fin 14,
          test q j sat false q = sat ∧ ¬F (test q j sat false) ∧ F (test q j sat true) := by
        unfold test F inc P L
        decide
      let sat := decide (g.op = .or)
      obtain ⟨z,val,off,on⟩ := existsTest q (fun e => hw (congrArg Fin.val e)) sat
      have ne : C.eval (List.ofFn (test q z sat false)) ≠ C.eval (List.ofFn (test q z sat true)) :=
        fun eq => off ((hf _).mp (eq.trans ((hf _).mpr on)))
      have probe := sense _ _ (by intro k hk; simp [test,hk]) ne
      have hwires : (C.wires (List.ofFn (test q z sat false))).getD w false = test q z sat false q :=
        readInput (⟨C.gates,w⟩ : Circuit) _ q rfl
      rw [hwires,val] at probe
      rcases hop with h | h <;> simp [sat,h] at probe
    refine ⟨j,hj',?_⟩
    rw [gat]
    simp only [hab,List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with h | h
    · subst a
      have he := window b (Ne.symm hn) hb (Or.inl hab)
      exact ⟨b,partner b (Ne.symm hn) he,Or.inl hab,he⟩
    · subst b
      have he := window a hn ha (Or.inr hab)
      exact ⟨a,partner a hn he,Or.inr hab,he⟩
  -- Use strict descent after pruning, transporting each improvement back to the original marked flag.
  have normalize (k : ℕ) : ∀ (C : Circuit) (p l : Fin 7), good C p l → inc p l → extra C = k →
      ∃ D, good D p l ∧ (internal D).Nodup := by
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro C p l hC hi hk
      by_cases ht : (internal C).Nodup
      · exact ⟨C,hC,ht⟩
      obtain ⟨positive,t,small⟩ := counting C hC.1 hC.2.1 hC.2.2.1 ht
      have cp := allRead C hC.2.2.2.1 (P t)
      have cl := allRead C hC.2.2.2.1 (L t)
      change 0 < (refs C).count t.val at cp
      change 0 < (refs C).count (7+t.val) at cl
      let s : Bool := decide ((refs C).count t.val ≠ 1)
      have pin : ∀ (t : Fin 7) (s : Bool),
          M t s (if s then 7+t.val else t.val) = 0 ∧ M t s (if s then t.val else 7+t.val) = 7 := by decide
      have countR (w : ℕ) : (refs (ren t s C)).count (M t s w) = (refs C).count w := by
        rw [refsRen,List.count_map_of_injective _ _ (Minj t s)]
      have zero := countR (if s then 7+t.val else t.val)
      have seven := countR (if s then t.val else 7+t.val)
      rw [(pin t s).1] at zero
      rw [(pin t s).2] at seven
      have counts : (refs (ren t s C)).count 0 = 1 ∧ (refs (ren t s C)).count 7 ≤ 2 := by
        by_cases h : (refs C).count t.val = 1
        · have hfalse : s = false := by simp [s,h]
          simp only [hfalse,Bool.false_eq_true,ite_false] at zero seven ⊢
          omega
        · have htrue : s = true := by simp [s,h]
          simp only [htrue,ite_true] at zero seven ⊢
          omega
      let D := ren t s C
      let a := (flag t s p l).1
      let b := (flag t s p l).2
      have hd : good D a b := renGood t s C p l hC
      obtain ⟨sz,sh,li,funD,dp,dl⟩ := hd
      obtain ⟨ao,nd⟩ := (dataShape D).mp sh
      obtain ⟨E,⟨esz,eao,endup,eli,ef,ep,el⟩,less⟩ := improve D a b
        ⟨sz,ao,nd,li,(dataCorrect D).mp funD,dp,dl⟩ ((memF a b).mpr (mapInc t s p l hi))
        counts.1 counts.2 (sole D funD sh counts.1) (show 0 < extra D by simpa only [D,extraRen] using positive)
      have he : good E a b := ⟨esz,(dataShape E).mpr ⟨eao,endup⟩,eli,(dataCorrect E).mpr ef,ep,el⟩
      let B := ren (back t s) s E
      have hB : good B p l := by
        have h := renGood (back t s) s E a b he
        simpa only [B,a,b,undoF] using h
      have hlt : extra B < k := by
        change extra E < extra D at less
        simpa only [B,D,extraRen,hk] using less
      exact ih (extra B) hlt B p l hB hi rfl
  change ∀ (C : Circuit) (p l : Fin 7), (C.size ≤ 27 ∧ shape C ∧ correct C) → inc p l →
    2 ≤ C.lineDeg 14 {p.val} → 2 ≤ C.lineDeg 14 {7+l.val} →
    ∃ D, (D.size ≤ 27 ∧ shape D ∧ correct D) ∧ (internal D).Nodup ∧
      2 ≤ D.lineDeg 14 {p.val} ∧ 2 ≤ D.lineDeg 14 {7+l.val}
  rintro C p l ⟨sz,sh,hF⟩ hi hp hl
  obtain ⟨D,hsize,hshape,hread,eval,deg⟩ := prune 14 C sh
  have hd : good D p l := ⟨le_trans hsize sz,hshape,hread,fun x => by rw [eval,hF],
    by simpa only [deg] using hp,by simpa only [deg] using hl⟩
  obtain ⟨E,⟨bound,gates,_,func,dp,dl⟩,tree⟩ := normalize (extra D) D p l hd hi rfl
  exact ⟨E,⟨bound,gates,func⟩,tree,dp,dl⟩
