import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Relabel the plane by a Singer cycle and an incidence preserving involution.
-- Their action reduces the extra OR to four pairs after removing constant and duplicate inputs.
set_option maxRecDepth 12000 in
set_option maxHeartbeats 6000000 in
theorem PEqualNP.Outside.R_meta_2343_271
    (points : let D : Finset (Fin 13) := {0,1,3,9}
    let P := fun (p l : Fin 13) => List.ofFn (fun u : Fin 13 => decide (u = p)) ++
      List.ofFn (fun v : Fin 13 => decide (v = l))
    let N := fun (Q : Finset (Fin 13)) => List.ofFn (fun u : Fin 13 => decide (u ∈ Q)) ++
      List.ofFn (fun v : Fin 13 => decide (∀ u ∈ Q, u - v ∉ D))
    let Good := fun (Q : Finset (Fin 13)) => Q.card = 4 ∧
      ∀ l : Fin 13, (Q.filter (fun u => u - l ∈ D)).card ≤ 2
    let E := fun (x : List Bool) => x ++ [x.getD 0 false || x.getD 1 false]
    ∀ C : Circuit, Monotone2 C →
      (∀ j : Fin C.gates.length, ∀ i ∈ (C.gates.get j).inputs, i < 27 + j.val) →
      (∀ p l, p-l ∈ D → C.eval (E (P p l)) = true) →
      (∀ Q, Good Q → C.eval (E (N Q)) = false) → 63 ≤ C.size)
    (lines : let D : Finset (Fin 13) := {0,1,3,9}
    let P := fun (p l : Fin 13) => List.ofFn (fun u : Fin 13 => decide (u = p)) ++
      List.ofFn (fun v : Fin 13 => decide (v = l))
    let N := fun (Q : Finset (Fin 13)) => List.ofFn (fun u : Fin 13 => decide (u ∈ Q)) ++
      List.ofFn (fun v : Fin 13 => decide (∀ u ∈ Q, u - v ∉ D))
    let Good := fun (Q : Finset (Fin 13)) => Q.card = 4 ∧
      ∀ l : Fin 13, (Q.filter (fun u => u - l ∈ D)).card ≤ 2
    let E := fun (x : List Bool) => x ++ [x.getD 13 false || x.getD 14 false]
    ∀ C : Circuit, Monotone2 C →
      (∀ j : Fin C.gates.length, ∀ i ∈ (C.gates.get j).inputs, i < 27 + j.val) →
      (∀ p l, p-l ∈ D → C.eval (E (P p l)) = true) →
      (∀ Q, Good Q → C.eval (E (N Q)) = false) → 63 ≤ C.size)
    (incident : let D : Finset (Fin 13) := {0,1,3,9}
    let P := fun (p l : Fin 13) => List.ofFn (fun u : Fin 13 => decide (u = p)) ++
      List.ofFn (fun v : Fin 13 => decide (v = l))
    let N := fun (Q : Finset (Fin 13)) => List.ofFn (fun u : Fin 13 => decide (u ∈ Q)) ++
      List.ofFn (fun v : Fin 13 => decide (∀ u ∈ Q, u - v ∉ D))
    let Good := fun (Q : Finset (Fin 13)) => Q.card = 4 ∧
      ∀ l : Fin 13, (Q.filter (fun u => u - l ∈ D)).card ≤ 2
    let E := fun (x : List Bool) => x ++ [x.getD 0 false || x.getD 13 false]
    ∀ C : Circuit, Monotone2 C →
      (∀ j : Fin C.gates.length, ∀ i ∈ (C.gates.get j).inputs, i < 27 + j.val) →
      (∀ p l, p-l ∈ D → C.eval (E (P p l)) = true) →
      (∀ Q, Good Q → C.eval (E (N Q)) = false) → 63 ≤ C.size)
    (nonincident : let D : Finset (Fin 13) := {0,1,3,9}
    let P := fun (p l : Fin 13) => List.ofFn (fun u : Fin 13 => decide (u = p)) ++
      List.ofFn (fun v : Fin 13 => decide (v = l))
    let N := fun (Q : Finset (Fin 13)) => List.ofFn (fun u : Fin 13 => decide (u ∈ Q)) ++
      List.ofFn (fun v : Fin 13 => decide (∀ u ∈ Q, u - v ∉ D))
    let Good := fun (Q : Finset (Fin 13)) => Q.card = 4 ∧
      ∀ l : Fin 13, (Q.filter (fun u => u - l ∈ D)).card ≤ 2
    let E := fun (x : List Bool) => x ++ [x.getD 0 false || x.getD 14 false]
    ∀ C : Circuit, Monotone2 C →
      (∀ j : Fin C.gates.length, ∀ i ∈ (C.gates.get j).inputs, i < 27 + j.val) →
      (∀ p l, p-l ∈ D → C.eval (E (P p l)) = true) →
      (∀ Q, Good Q → C.eval (E (N Q)) = false) → 63 ≤ C.size)
    : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List ℕ),   x2.length ≤ (2 : ℕ) →     PEqualNP.MetaComplexity.Monotone2 x1 →       (∀ (x5 : Fin x1.gates.length), ∀ x6 ∈ (x1.gates.get x5).inputs, x6 < (27 : ℕ) + ↑x5) →         have x6 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};         have x7 : Fin (13 : ℕ) → Fin (13 : ℕ) → List Bool := fun (x7 x8 : Fin (13 : ℕ)) => (List.ofFn fun (x9 : Fin (13 : ℕ)) => Decidable.decide (x9 = x7)) ++ List.ofFn fun (x9 : Fin (13 : ℕ)) => Decidable.decide (x9 = x8);         have x8 : Finset (Fin (13 : ℕ)) → List Bool := fun (x8 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x9 : Fin (13 : ℕ)) => Decidable.decide (x9 ∈ x8)) ++ List.ofFn fun (x9 : Fin (13 : ℕ)) => Decidable.decide (∀ x10 ∈ x8, x10 - x9 ∉ x6);         have x9 : Finset (Fin (13 : ℕ)) → Prop := fun (x9 : Finset (Fin (13 : ℕ))) => x9.card = (4 : ℕ) ∧ ∀ (x10 : Fin (13 : ℕ)), {x11 ∈ x9 | x11 - x10 ∈ x6}.card ≤ (2 : ℕ);         have x10 : List Bool → List Bool := fun (x10 : List Bool) => x10 ++ [x2.any fun (x11 : ℕ) => x10.getD x11 Bool.false];         (∀ (x11 x12 : Fin (13 : ℕ)), x11 - x12 ∈ x6 → x1.eval (x10 (x7 x11 x12)) = Bool.true) → (∀ (x12 : Finset (Fin (13 : ℕ))), x9 x12 → x1.eval (x10 (x8 x12)) = Bool.false) → (63 : ℕ) ≤ x1.size := by
  let D : Finset (Fin 13) := {0,1,3,9}
  let P := fun (p l : Fin 13) => List.ofFn (fun u : Fin 13 => decide (u = p)) ++
      List.ofFn (fun v : Fin 13 => decide (v = l))
  let N := fun (Q : Finset (Fin 13)) => List.ofFn (fun u : Fin 13 => decide (u ∈ Q)) ++
      List.ofFn (fun v : Fin 13 => decide (∀ u ∈ Q, u - v ∉ D))
  let Good := fun (Q : Finset (Fin 13)) => Q.card = 4 ∧
      ∀ l : Fin 13, (Q.filter (fun u => u - l ∈ D)).card ≤ 2
  let B (a b : ℕ) : Prop :=
    let E := fun (x : List Bool) => x ++ [x.getD a false || x.getD b false]
    ∀ C : Circuit, Monotone2 C →
      (∀ j : Fin C.gates.length, ∀ i ∈ (C.gates.get j).inputs, i < 27 + j.val) →
      (∀ p l, p-l ∈ D → C.eval (E (P p l)) = true) →
      (∀ Q, Good Q → C.eval (E (N Q)) = false) → 63 ≤ C.size
  have sizeGates (C : Circuit) : C.size = C.gates.length := rfl
  have sameSide (a b : ℕ) (ha : a = 0 ∨ a = 13) (hb : b = a+1) : B a b := by
    subst b
    rcases ha with rfl | rfl
    · exact points
    · exact lines
  have mixed (a b : ℕ) (ha : a = 0) (hb : b = 13 ∨ b = 14) : B a b := by
    subst a
    rcases hb with rfl | rfl
    · exact incident
    · exact nonincident
  let E (a b : ℕ) (x : List Bool) := x ++ [x.getD a false || x.getD b false]
  let back (C : Circuit) := ∀ j : Fin C.gates.length, ∀ i ∈ (C.gates.get j).inputs, i < 27 + j.val
  let move (f h : Fin 13 → Fin 13) (i : ℕ) : ℕ :=
    if hi : i < 13 then (f ⟨i,hi⟩).val else
    if hj : i < 26 then 13 + (h ⟨i-13,by omega⟩).val else i
  have small (f h : Fin 13 → Fin 13) (i : ℕ) (hi : i < 26) : move f h i < 26 := by
    simp only [move]; split <;> rename_i h1
    · have := (f ⟨i,h1⟩).isLt; omega
    · have := (h ⟨i-13,by omega⟩).isLt; simp; omega
  have fixed (f h : Fin 13 → Fin 13) (i : ℕ) (hi : 26 ≤ i) : move f h i = i := by
    simp [move,show ¬i < 13 by omega,show ¬i < 26 by omega]
  have getFn (x : Fin 13 → Bool) (i : Fin 13) : (List.ofFn x).getD i.val false = x i := by
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
  let row (x y : Fin 13 → Bool) := List.ofFn x ++ List.ofFn y
  have rowMove (f h : Fin 13 → Fin 13) (x y u v : Fin 13 → Bool)
      (hx : ∀ k, x k = u (f k)) (hy : ∀ k, y k = v (h k)) (i : ℕ) :
      (row x y).getD i false = (row u v).getD (move f h i) false := by
    by_cases hi : i < 13
    · let k : Fin 13 := ⟨i,hi⟩
      rw [show move f h i = (f k).val by simp [move,hi,k]]
      change (row x y).getD k.val false = (row u v).getD (f k).val false
      unfold row
      rw [List.getD_append _ _ _ _ (by simp),
          List.getD_append _ _ _ _ (by simp),getFn,getFn,hx]
    · by_cases hj : i < 26
      · let k : Fin 13 := ⟨i-13,by omega⟩
        have m : move f h i = 13 + (h k).val := by simp [move,hi,hj,k]
        rw [m]; unfold row
        rw [List.getD_append_right _ _ _ _ (by simp; omega),
          List.getD_append_right _ _ _ _ (by simp)]
        simp only [List.length_ofFn,Nat.add_sub_cancel_left]
        exact (getFn y k).trans ((hy k).trans (getFn v (h k)).symm)
      · rw [fixed _ _ _ (by omega),List.getD_eq_default _ _ (by simp [row]; omega),
            List.getD_eq_default _ _ (by simp [row]; omega)]
  let gate (r : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op,g.inputs.map r⟩
  let ren (r : ℕ → ℕ) (C : Circuit) : Circuit := ⟨C.gates.map (gate r),r C.output⟩
  have mono (r : ℕ → ℕ) (C : Circuit) (hm : Monotone2 C) : Monotone2 (ren r C) := by
    intro g hg
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hg
    exact ⟨(hm q hq).1,by simpa [gate] using (hm q hq).2⟩
  have reads (f h : Fin 13 → Fin 13) (C : Circuit) (hb : back C) : back (ren (move f h) C) := by
    intro j i hi
    let k : Fin C.gates.length := ⟨j.val,by simpa [ren] using j.isLt⟩
    change i ∈ ((C.gates.map (gate (move f h)))[j.val]).inputs at hi
    rw [List.getElem_map] at hi
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hi
    have bound := hb k v hv
    by_cases hv' : v < 26
    · have := small f h v hv'; omega
    · rw [fixed f h v (by omega)]; exact bound
  let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let rel (r : ℕ → ℕ) (u v : List Bool) :=
    u.length = v.length ∧ 26 ≤ u.length ∧ ∀ i, u.getD i false = v.getD (r i) false
  have append (f h : Fin 13 → Fin 13) (u v : List Bool) (bit : Bool)
      (hu : rel (move f h) u v) : rel (move f h) (u++[bit]) (v++[bit]) := by
    obtain ⟨he,hl,hr⟩ := hu
    refine ⟨by simp [he],by simp; omega,fun i => ?_⟩
    by_cases hi : i < 26
    · have := small f h i hi
      rw [List.getD_append _ _ _ _ (by omega),List.getD_append _ _ _ _ (by omega)]
      exact hr i
    · rw [fixed _ _ _ (by omega)]
      by_cases hj : i < u.length
      · rw [List.getD_append _ _ _ _ hj,List.getD_append _ _ _ _ (by omega)]
        simpa only [fixed f h i (by omega)] using hr i
      · rw [List.getD_append_right _ _ _ _ (by omega),List.getD_append_right _ _ _ _ (by omega),he]
  have run (f h : Fin 13 → Fin 13) (gs : List Gate) (u v : List Bool) (hu : rel (move f h) u v) :
      rel (move f h) (gs.foldl step u) ((gs.map (gate (move f h))).foldl step v) := by
    induction gs generalizing u v with
    | nil => exact hu
    | cons g gs ih =>
      apply ih
      have he : (g.inputs.map fun i => u.getD i false) =
          ((gate (move f h) g).inputs.map fun i => v.getD i false) := by
        change _ = (g.inputs.map _).map _
        rw [List.map_map]
        exact List.map_congr_left (fun i _ => hu.2.2 i)
      unfold step; rw [he]; exact append f h u v _ hu
  have evalMove (f h : Fin 13 → Fin 13) (C : Circuit) (u v : List Bool) (a b : ℕ)
      (hu : rel (move f h) u v) :
      C.eval (E a b u) = (ren (move f h) C).eval (E (move f h a) (move f h b) v) := by
    apply (run f h C.gates _ _ ?_).2.2 C.output
    unfold E; rw [hu.2.2 a,hu.2.2 b]; exact append f h _ _ _ hu
  have transport (f h : Fin 13 ≃ Fin 13)
      (inc : ∀ p l, (p-l ∈ D) ↔ (f p - h l ∈ D)) (a b : ℕ)
      (hb : B (move f h a) (move f h b)) : B a b := by
    intro C hm hw hp hn
    apply le_trans (hb (ren (move f h) C) (mono _ C hm) (reads f h C hw) ?_ ?_)
    · simp [sizeGates,ren]
    · intro p l hi
      let u := f.symm p
      let v := h.symm l
      have hp' := hp u v ((inc u v).mpr (by simpa [u,v] using hi))
      have hrow : rel (move f h) (P u v) (P p l) := by
        refine ⟨by simp [P],by simp [P],rowMove f h _ _ _ _ ?_ ?_⟩
        · intro i; simp [u,Equiv.eq_symm_apply]
        · intro i; simp [v,Equiv.eq_symm_apply]
      exact (evalMove f h C _ _ a b hrow).symm.trans hp'
    · intro Q hQ
      let S := Q.map f.symm.toEmbedding
      have memS (i : Fin 13) : i ∈ S ↔ f i ∈ Q := by simp [S]
      have hS : Good S := by
        refine ⟨by simpa [S] using hQ.1,fun l => ?_⟩
        have he : (S.filter (fun i => i-l ∈ D)).map f.toEmbedding =
            Q.filter (fun i => i-h l ∈ D) := by
          ext i
          simp only [Finset.mem_map_equiv,Finset.mem_filter,memS,Equiv.apply_symm_apply]
          exact and_congr_right (fun _ => by simpa using inc (f.symm i) l)
        rw [← Finset.card_map (f := f.toEmbedding), he]
        exact hQ.2 (h l)
      have hrow : rel (move f h) (N S) (N Q) := by
        refine ⟨by simp [N],by simp [N],rowMove f h _ _ _ _ ?_ ?_⟩
        · intro i; simp only [memS]
        · intro l
          congr 1
          apply propext
          constructor
          · intro hs i hi hin
            apply hs (f.symm i) ((memS _).2 (by simpa using hi))
            exact (inc _ _).2 (by simpa using hin)
          · intro hq i hi hin; exact hq (f i) ((memS _).1 hi) ((inc _ _).1 hin)
      exact (evalMove f h C _ _ a b hrow).symm.trans (hn S hS)
  have single (k j : ℕ) (hk : k = 0 ∨ k = 13 ∨ k = 26) (hj : j = k) : B k j := by
    subst j
    classical
    have hkle : k ≤ 26 := by omega
    let r (i : ℕ) := if i = 26 then k else i
    let edit (g : Gate) : Gate := if k = 26 ∧ 26 ∈ g.inputs then
      if g.op = GateOp.and then ⟨GateOp.or,[]⟩ else ⟨g.op,g.inputs.filter (· != 26)⟩
      else gate r g
    have ok (g : Gate) (hg : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
        (edit g).op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ (edit g).inputs.length ≤ 2 := by
      dsimp only [edit]; split
      · split
        · simp
        · exact ⟨hg.1,(List.length_filter_le ..).trans hg.2⟩
      · exact ⟨hg.1,by simpa [gate] using hg.2⟩
    have valid (g : Gate) (n : ℕ) (hw : ∀ i ∈ g.inputs, i < 27+n) :
        ∀ i ∈ (edit g).inputs, i < 27+n := by
      intro i hi
      dsimp only [edit] at hi; split at hi
      · split at hi
        · simp at hi
        · exact hw i (List.mem_filter.mp hi).1
      · obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hi
        unfold r; split
        · omega
        · exact hw q hq
    let agrees (u v : List Bool) := u.length = v.length ∧ 27 ≤ u.length ∧
      u.getD 26 false = (if k = 26 then false else v.getD k false) ∧
      ∀ i, i ≠ 26 → u.getD i false = v.getD i false
    have appendEq (u v : List Bool) (z : Bool) (hr : agrees u v) :
        agrees (u++[z]) (v++[z]) := by
      obtain ⟨he,hl,ha,ho⟩ := hr
      refine ⟨by simp [he],by simp; omega,?_,?_⟩
      · rw [List.getD_append _ _ _ _ (by omega),List.getD_append _ _ _ _ (by omega)]
        exact ha
      · intro i hi
        by_cases hi' : i < u.length
        · rw [List.getD_append _ _ _ _ hi',List.getD_append _ _ _ _ (by omega)]
          exact ho i hi
        · rw [List.getD_append_right _ _ _ _ (by omega),List.getD_append_right _ _ _ _ (by omega),he]
    have andValue (bs : List Bool) : GateOp.and.eval bs = bs.all id := rfl
    have orValue (bs : List Bool) : GateOp.or.eval bs = bs.any id := rfl
    have gateEq (u v : List Bool) (hr : agrees u v) (g : Gate)
        (hg : g.op = GateOp.and ∨ g.op = GateOp.or) :
        g.op.eval (g.inputs.map fun i => u.getD i false) =
        (edit g).op.eval ((edit g).inputs.map fun i => v.getD i false) := by
      dsimp only [edit]; split
      · rename_i hd
        have hfalse : u.getD 26 false = false := by simpa only [ite_eq_left hd.1] using hr.2.2.1
        rcases hg with h | h
        · simp only [h,ite_true,andValue,orValue]
          apply List.all_eq_false.mpr
          exact ⟨false,List.mem_map.mpr ⟨26,hd.2,hfalse⟩,by decide⟩
        · have diff : GateOp.or ≠ GateOp.and := by intro he; cases he
          simp only [h,ite_eq_right diff,orValue,List.any_map,Function.comp_def]
          apply Bool.eq_iff_iff.mpr
          simp only [List.any_eq_true,List.mem_filter,bne_iff_ne, id_eq]
          constructor
          · rintro ⟨i,hi,hb⟩
            have hne : i ≠ 26 := fun eq => Bool.noConfusion (hfalse.symm.trans (eq ▸ hb))
            exact ⟨i,⟨hi,hne⟩,(hr.2.2.2 i hne).symm.trans hb⟩
          · rintro ⟨i,⟨hi,hne⟩,hb⟩
            exact ⟨i,hi,(hr.2.2.2 i hne).trans hb⟩
      · rename_i hd
        change g.op.eval _ = g.op.eval ((g.inputs.map r).map _)
        congr 1
        rw [List.map_map]
        apply List.map_congr_left
        intro i hi
        by_cases he : i = 26
        · subst i
          have hn : k ≠ 26 := fun e => hd ⟨e,hi⟩
          change u.getD 26 false = v.getD (r 26) false
          rw [show r 26 = k by simp [r]]
          simpa only [ite_eq_right hn] using hr.2.2.1
        · simpa only [r,ite_eq_right he,Function.comp_apply] using hr.2.2.2 i he
    have folds (gs : List Gate) (u v : List Bool) (hr : agrees u v)
        (hm : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
        agrees (gs.foldl step u) ((gs.map edit).foldl step v) := by
      induction gs generalizing u v with
      | nil => exact hr
      | cons g gs ih =>
        apply ih
        · change agrees (step u g) (step v (edit g))
          unfold step
          rw [gateEq u v hr g (hm g (by simp))]
          exact appendEq u v _ hr
        · intro q hq; exact hm q (List.mem_cons_of_mem _ hq)
    have lengthRun (gs : List Gate) (v : List Bool) :
        (gs.foldl step v).length = v.length + gs.length := by
      induction gs generalizing v with
      | nil => simp
      | cons g gs ih => rw [List.foldl_cons,ih]; simp [step]; omega
    intro C hm hw hp hn
    let output := if C.output = 26 ∧ k = 26 then 27 + C.size else r C.output
    let A : Circuit := ⟨C.gates.map edit,output⟩
    have am : Monotone2 A := by
      intro g hg
      obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hg
      exact ok q (hm q hq)
    have ab : back A := by
      intro t i hi
      let t' : Fin C.gates.length := ⟨t.val,by simpa [A] using t.isLt⟩
      change i ∈ ((C.gates.map edit)[t.val]).inputs at hi
      rw [List.getElem_map] at hi
      exact valid _ _ (hw t') i hi
    have evaluation (x : List Bool) (hx : x.length = 26) : C.eval (E k k x) = A.eval (E 0 1 x) := by
      have initial : agrees (E k k x) (E 0 1 x) := by
        refine ⟨by simp [E],by simp [E,hx],?_,?_⟩
        · unfold E
          rw [List.getD_append_right _ _ _ _ hx.le,hx,Nat.sub_self,List.getD_cons_zero,Bool.or_self]
          by_cases eq : k = 26
          · rw [ite_eq_left eq,eq,List.getD_eq_default x false hx.le]
          · rw [ite_eq_right eq,List.getD_append _ _ _ _ (by omega)]
        · intro i hi
          by_cases h : i < 26
          · unfold E
            rw [List.getD_append _ _ _ _ (by omega),List.getD_append _ _ _ _ (by omega)]
          · rw [List.getD_eq_default _ false (by simp [E,hx]; omega),
                List.getD_eq_default _ false (by simp [E,hx]; omega)]
      have fin := folds C.gates _ _ initial (fun g h => by
        simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using (hm g h).1)
      change (C.gates.foldl step _).getD C.output false =
        ((C.gates.map edit).foldl step (E 0 1 x)).getD output false
      by_cases ho : C.output = 26
      · rw [ho]
        by_cases he : k = 26
        · rw [show output = 27+C.size by simp [output,ho,he]]
          rw [List.getD_eq_default ((C.gates.map edit).foldl step (E 0 1 x)) false
            (by simp [lengthRun,E,hx,sizeGates] : ((C.gates.map edit).foldl step (E 0 1 x)).length ≤ 27+C.size)]
          simpa only [ite_eq_left he] using fin.2.2.1
        · simpa only [output,ho,he,and_false,ite_false,r,ite_eq_left rfl] using fin.2.2.1
      · simpa only [output,ho,false_and,ite_false,r] using fin.2.2.2 C.output ho
    apply le_trans (sameSide 0 1 (Or.inl rfl) rfl A am ab ?_ ?_)
    · simp [sizeGates,A]
    · intro p l hi; exact (evaluation (P p l) (by simp [P])).symm.trans (hp p l hi)
    · intro Q hQ; exact (evaluation (N Q) (by simp [N])).symm.trans (hn Q hQ)
  let rot : Fin 13 ≃ Fin 13 := Equiv.addRight 1
  let pMap : Fin 13 → Fin 13 := ![0, 1, 2, 3, 10, 11, 7, 6, 12, 9, 4, 5, 8]
  let lMap : Fin 13 → Fin 13 := ![0, 1, 2, 7, 10, 11, 6, 3, 9, 8, 4, 5, 12]
  have pinv : ∀ i, pMap (pMap i) = i := by decide
  have linv : ∀ i, lMap (lMap i) = i := by decide
  let pPerm : Fin 13 ≃ Fin 13 := ⟨pMap,pMap,pinv,pinv⟩
  let lPerm : Fin 13 ≃ Fin 13 := ⟨lMap,lMap,linv,linv⟩
  have rotInc : ∀ p l : Fin 13, p-l ∈ D ↔ rot p - rot l ∈ D := by decide
  have permInc : ∀ p l : Fin 13, p-l ∈ D ↔ pPerm p - lPerm l ∈ D := by
    change ∀ p l, p-l ∈ D ↔ pMap p - lMap l ∈ D
    decide
  let rotI : Fin 27 → Fin 27 := ![1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 0, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 13, 26]
  let permI : Fin 27 → Fin 27 := ![0, 1, 2, 3, 10, 11, 7, 6, 12, 9, 4, 5, 8, 13, 14, 15, 20, 23, 24, 19, 16, 22, 21, 17, 18, 25, 26]
  have hrI : ∀ a : Fin 27, (rotI a).val = move rot rot a.val := by decide
  have hpI : ∀ a : Fin 27, (permI a).val = move pMap lMap a.val := by decide
  -- Each entry counts moves to a representative using a swap or either permutation.
  let dist : List (List ℕ) := [
    [0, 0, 10, 8, 9, 10, 10, 9, 3, 9, 10, 10, 2, 0, 0, 10, 9, 9, 9, 9, 8, 9, 10, 10, 10, 10, 0],
    [1, 7, 7, 9, 7, 8, 9, 10, 8, 10, 8, 9, 9, 9, 7, 7, 9, 11, 8, 8, 8, 7, 8, 12, 9, 11, 7],
    [10, 8, 6, 6, 8, 6, 7, 8, 11, 7, 9, 7, 10, 10, 8, 6, 6, 11, 10, 7, 7, 7, 6, 12, 11, 10, 6],
    [9, 9, 7, 5, 5, 7, 5, 6, 7, 10, 6, 8, 8, 9, 9, 7, 5, 5, 10, 9, 6, 7, 7, 5, 11, 11, 5],
    [10, 8, 8, 6, 4, 4, 6, 4, 8, 6, 9, 7, 10, 10, 8, 8, 6, 4, 4, 9, 8, 6, 6, 6, 4, 10, 4],
    [9, 9, 7, 7, 5, 3, 8, 5, 3, 7, 5, 8, 8, 9, 9, 7, 7, 5, 3, 8, 12, 8, 5, 5, 5, 3, 3],
    [10, 8, 8, 6, 6, 9, 4, 7, 4, 8, 6, 4, 7, 10, 8, 8, 6, 6, 4, 7, 7, 13, 7, 4, 4, 4, 4],
    [10, 9, 7, 7, 5, 5, 8, 3, 6, 9, 7, 10, 3, 10, 9, 7, 8, 5, 5, 7, 6, 6, 12, 7, 3, 3, 3],
    [2, 9, 10, 6, 7, 4, 5, 7, 2, 5, 8, 8, 11, 2, 9, 9, 6, 10, 9, 9, 6, 5, 5, 11, 11, 2, 2],
    [10, 10, 8, 11, 5, 6, 8, 9, 6, 4, 4, 7, 7, 10, 10, 8, 8, 5, 9, 8, 8, 5, 4, 4, 10, 12, 4],
    [11, 9, 9, 7, 10, 6, 5, 7, 9, 5, 3, 3, 9, 11, 9, 9, 7, 7, 5, 8, 7, 7, 7, 3, 3, 11, 3],
    [10, 10, 8, 8, 6, 9, 5, 9, 7, 8, 4, 2, 2, 10, 10, 8, 11, 6, 6, 8, 7, 6, 9, 6, 2, 2, 2],
    [1, 10, 9, 7, 9, 9, 8, 4, 10, 6, 8, 3, 1, 1, 10, 10, 7, 10, 10, 9, 7, 6, 6, 11, 10, 1, 1],
    [1, 10, 11, 10, 11, 10, 11, 11, 3, 11, 12, 11, 2, 0, 0, 10, 9, 10, 9, 9, 8, 9, 10, 11, 10, 2, 0],
    [1, 8, 9, 10, 9, 10, 9, 10, 10, 11, 10, 11, 11, 1, 7, 7, 9, 10, 9, 8, 8, 7, 8, 11, 10, 12, 7],
    [11, 8, 7, 8, 9, 8, 9, 8, 10, 9, 10, 9, 11, 11, 8, 6, 6, 12, 9, 8, 7, 7, 6, 12, 10, 11, 6],
    [10, 10, 7, 6, 7, 8, 7, 9, 7, 9, 8, 12, 8, 10, 10, 7, 5, 5, 11, 8, 7, 8, 7, 5, 11, 10, 5],
    [10, 12, 12, 6, 5, 6, 7, 6, 11, 6, 8, 7, 11, 9, 9, 12, 6, 4, 4, 10, 7, 6, 7, 12, 4, 11, 4],
    [10, 9, 11, 11, 5, 4, 5, 6, 10, 10, 6, 7, 11, 10, 8, 8, 12, 5, 3, 8, 9, 8, 13, 6, 11, 3, 3],
    [10, 9, 8, 10, 10, 9, 8, 8, 10, 9, 9, 9, 10, 10, 9, 7, 7, 11, 9, 7, 7, 8, 7, 12, 10, 10, 7],
    [9, 9, 8, 7, 9, 13, 8, 7, 7, 9, 8, 8, 8, 9, 9, 8, 6, 6, 10, 8, 6, 6, 8, 6, 12, 11, 6],
    [10, 8, 8, 8, 7, 9, 14, 7, 6, 6, 8, 7, 7, 10, 8, 8, 7, 5, 9, 9, 7, 5, 5, 7, 12, 12, 5],
    [11, 9, 7, 8, 7, 6, 8, 13, 6, 5, 8, 10, 7, 11, 9, 7, 8, 6, 12, 8, 8, 6, 4, 4, 10, 11, 4],
    [11, 13, 13, 6, 7, 6, 5, 8, 12, 5, 4, 7, 12, 10, 10, 11, 6, 11, 5, 11, 7, 8, 5, 3, 3, 12, 3],
    [11, 10, 12, 12, 5, 6, 5, 4, 12, 11, 4, 3, 11, 11, 9, 9, 10, 5, 10, 9, 12, 13, 9, 4, 2, 2, 2],
    [11, 12, 11, 12, 11, 4, 5, 4, 3, 13, 12, 3, 2, 1, 11, 10, 11, 10, 4, 9, 10, 11, 12, 11, 3, 1, 1],
    [1, 8, 7, 6, 5, 4, 5, 4, 3, 5, 4, 3, 2, 1, 8, 7, 6, 5, 4, 8, 7, 6, 5, 4, 3, 2, 0]]
  let rank (a b : Fin 27) := (dist.getD a.val []).getD b.val 0
  let base (a b : Fin 27) := (a.val = 0 ∨ a.val = 13 ∨ a.val = 26) ∧ b = a ∨
    (a.val = 0 ∨ a.val = 13) ∧ b.val = a.val+1 ∨
    a.val = 0 ∧ (b.val = 13 ∨ b.val = 14) ∨ (a.val = 0 ∨ a.val = 13) ∧ b.val = 26
  have descent : ∀ a b : Fin 27, base a b ∨ rank b a < rank a b ∨
      rank (rotI a) (rotI b) < rank a b ∨ rank (permI a) (permI b) < rank a b := by
    unfold base
    decide +kernel
  have eqPins (a b c d : ℕ)
      (eqv : ∀ x : List Bool, x.length = 26 → (x.getD a false || x.getD b false) =
        (x.getD c false || x.getD d false)) (hc : B c d) : B a b := by
    intro C hm hw hp hn
    apply hc C hm hw
    · intro p l hi
      simpa only [← eqv (P p l) (by simp [P])] using hp p l hi
    · intro Q hQ
      simpa only [← eqv (N Q) (by simp [N])] using hn Q hQ
  have allPairs (n : ℕ) : ∀ a b : Fin 27, rank a b = n → B a.val b.val := by
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro a b hr
      rcases descent a b with h | hs | ht | hu
      · rcases h with ⟨ha,rfl⟩ | ⟨ha,hb⟩ | ⟨ha,hb⟩ | ⟨ha,hb⟩
        · exact single _ _ ha rfl
        · exact sameSide _ _ ha hb
        · exact mixed _ _ ha hb
        · apply eqPins a.val b.val a.val a.val _ (single a.val a.val (ha.elim Or.inl (fun e => Or.inr (Or.inl e))) rfl)
          intro x hx; rw [hb,List.getD_eq_default x false hx.le]
          simp
      · apply eqPins _ _ b.val a.val (fun _ _ => Bool.or_comm _ _)
        exact ih _ (hr ▸ hs) b a rfl
      · apply transport rot rot rotInc
        rw [← hrI,← hrI]
        exact ih _ (hr ▸ ht) _ _ rfl
      · apply transport pPerm lPerm permInc
        change B (move pMap lMap a.val) (move pMap lMap b.val)
        rw [← hpI,← hpI]
        exact ih _ (hr ▸ hu) _ _ rfl
  intro C s hs hm hw
  dsimp only
  intro hp hn
  let clamp (i : ℕ) : Fin 27 := ⟨min i 26,by omega⟩
  let a := clamp (s.getD 0 26)
  let b := clamp (s.getD 1 26)
  have same (x : List Bool) (hx : x.length = 26) :
      s.any (fun i => x.getD i false) = (x.getD a.val false || x.getD b.val false) := by
    have clip (i : ℕ) : x.getD (clamp i).val false = x.getD i false := by
      by_cases hi : i ≤ 26
      · simp [clamp,min_eq_left hi]
      · change x.getD (min i 26) false = _
        rw [min_eq_right (by omega),List.getD_eq_default x false hx.le,
          List.getD_eq_default x false (hx.le.trans (by omega))]
    simp only [a,b,clip]
    cases s with
    | nil =>
      change false = (x.getD 26 false || x.getD 26 false)
      rw [List.getD_eq_default x false hx.le]; rfl
    | cons i s =>
      cases s with
      | nil =>
        change (x.getD i false || false) = (x.getD i false || x.getD 26 false)
        rw [List.getD_eq_default x false hx.le]
      | cons j s =>
        cases s with
        | nil => simp [List.getD]
        | cons k s => simp at hs
  apply allPairs _ a b rfl C hm hw
  · intro p l hi
    simpa only [← same (P p l) (by simp [P])] using hp p l hi
  · intro Q hQ
    simpa only [← same (N Q) (by simp [N])] using hn Q hQ
