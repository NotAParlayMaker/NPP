import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Separate the jointly symmetric first two wires, degenerate second wires, and genuine two-pin continuations.
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_3231_5
    (contract : ∀ (C : Circuit) (k : Fin 9), (k = 4 ∨ k = 6) → FanInTwo C →
      C.size ≤ 13 → (∃ g ∈ C.gates, k.val ∈ g.inputs ∧
        (g.op = .not → g.inputs.headD 100 = k.val)) →
      ∃ D : Circuit, FanInTwo D ∧ D.size ≤ 12 ∧ ∀ x : Fin 9 → Bool,
        let y := Function.update x k false
        circuitFun 9 D x = C.eval (List.ofFn y ++ [y 4 || y 6, false]))
    (minor : ∀ k : Fin 9, (k = 4 ∨ k = 6) → ¬ HasCircuitSize 9
      (fun x => let x := Function.update x k false; (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
          (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
          (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) 12)
    (trivial : ∀ (r : Bool ⊕ Fin 10) (C : Circuit), FanInTwo C → C.size ≤ 13 →
      ∃ x : Fin 9 → Bool,
        let w := List.ofFn x ++ [x 4 || x 6]
        C.eval (w ++ [r.elim id fun i => w.getD i.val false]) ≠ ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
          (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
          (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)))
    (proper : ∀ (a b : Fin 10), a ≠ b →
      ¬ List.Perm [a.val,b.val] [4,6] →
      ¬ List.Perm [a.val,b.val] [4,9] →
      ¬ List.Perm [a.val,b.val] [6,9] →
      [a.val,b.val] ≤ [a.val,b.val].map (fun i => ([1,0,5,8,6,2,4,7,3] : List ℕ).getD i i) →
      ∀ C : Circuit, FanInTwo C → C.size ≤ 13 → ∃ x : Fin 9 → Bool,
        let w := List.ofFn x ++ [x 4 || x 6]
        C.eval (w ++ [w.getD a.val false && w.getD b.val false]) ≠ ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
          (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
          (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (4 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) → ∀ (x5 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[(1 : ℕ)]? = Option.some x5 → x5.op = PEqualNP.CircuitLowerBounds.GateOp.and → x5.inputs ≤ List.map (fun (x8 : ℕ) => [(1 : ℕ), (0 : ℕ), (5 : ℕ), (8 : ℕ), (6 : ℕ), (2 : ℕ), (4 : ℕ), (7 : ℕ), (3 : ℕ)].getD x8 x8) x5.inputs → (16 : ℕ) ≤ x1.size := by
  classical
  let edge (x : Fin 9 → Bool) : Bool := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
          (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
          (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
  let step (w : List Bool) (g : Gate) :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let base (x : Fin 9 → Bool) := List.ofFn x ++ [x 4 || x 6]
  let eff (g : Gate) (i : ℕ) := i ∈ g.inputs ∧
    (g.op = .not → g.inputs.headD 100 = i)
  have readLast (w : List Bool) (t : Bool) : (w ++ [t]).getD w.length false = t := by
    rw [List.getD_append_right _ _ _ _ (Nat.le_refl _)]
    simp
  have readOld (w : List Bool) (t : Bool) (i : ℕ) (hi : i ≠ w.length) :
      (w ++ [t]).getD i false = w.getD i false := by
    by_cases h : i < w.length
    · exact List.getD_append _ _ _ _ h
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]
  have keep (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl step w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih _ (by simp [step]; omega)]
      exact readOld _ _ _ (by omega)
  have agrees (g : Gate) (w v : List Bool)
      (hv : ∀ i, eff g i → w.getD i false = v.getD i false) :
      g.op.eval (g.inputs.map fun i => w.getD i false) =
        g.op.eval (g.inputs.map fun i => v.getD i false) := by
    rcases g with ⟨op,pins⟩
    cases op with
    | not =>
      cases pins with
      | nil => rfl
      | cons p pins =>
        have eq := hv p (by simp [eff])
        change Bool.not (w.getD p false) = Bool.not (v.getD p false)
        rw [eq]
    | and | or | mod | maj =>
      congr 1
      exact List.map_congr_left (fun i hi => hv i (by simpa [eff] using hi))
  have sweep (gs : List Gate) (w v : List Bool) (len : w.length = v.length)
      (none : ∀ g ∈ gs, ¬ eff g 4 ∧ ¬ eff g 6)
      (rel : ∀ i, i ≠ 4 → i ≠ 6 → w.getD i false = v.getD i false) :
      ∀ i, i ≠ 4 → i ≠ 6 →
        (gs.foldl step w).getD i false = (gs.foldl step v).getD i false := by
    induction gs generalizing w v with
    | nil => exact rel
    | cons g gs ih =>
      rw [List.foldl_cons, List.foldl_cons]
      apply ih _ _ (by simp [step, len]) (fun q hq => none q (by simp [hq]))
      intro i h4 h6
      by_cases hi : i = w.length
      · have eq := agrees g w v (fun j hj => rel j
          (fun h => (none g (by simp)).1 (h ▸ hj))
          (fun h => (none g (by simp)).2 (h ▸ hj)))
        subst i
        have right := readLast v (g.op.eval (g.inputs.map fun j => v.getD j false))
        rw [← len] at right
        exact (readLast _ _).trans (eq.trans right.symm)
      · have hj : i ≠ v.length := fun h => hi (h.trans len.symm)
        change (w ++ [_]).getD i false = (v ++ [_]).getD i false
        rw [readOld _ _ _ hi, readOld _ _ _ hj]
        exact rel i h4 h6
  have baseLen (x : Fin 9 → Bool) : (base x).length = 10 := by simp [base]
  have base4 (x : Fin 9 → Bool) : (base x).getD 4 false = x 4 := by
    simp [base, List.getD_eq_getElem?_getD]
  have base6 (x : Fin 9 → Bool) : (base x).getD 6 false = x 6 := by
    simp [base, List.getD_eq_getElem?_getD]
  have base9 (x : Fin 9 → Bool) : (base x).getD 9 false = (x 4 || x 6) := by
    simp [base, List.getD_eq_getElem?_getD]
  intro C hFan hFirst hFun second hSecond hOp hOrder
  by_contra hn
  rcases C with ⟨gs,out⟩
  cases gs with
  | nil => simp at hSecond
  | cons first rest =>
    cases rest with
    | nil => simp at hSecond
    | cons g tail =>
      have hg : g = second := by simpa using hSecond
      subst g
      let T : Circuit := ⟨tail,out⟩
      have hTFan : FanInTwo T := fun q hq => hFan q (by simpa [T] using
        (List.mem_cons_of_mem first (List.mem_cons_of_mem second hq)))
      have hTSize : T.size ≤ 13 := by
        change ¬ 16 ≤ (first :: second :: tail).length at hn
        simp only [List.length_cons] at hn
        change tail.length ≤ 13
        omega
      have arity : second.inputs.length ≤ 2 := (hFan second (by simp)).2
      have firstStep (x : Fin 9 → Bool) : step (List.ofFn x) first = base x := by
        have hh := hFirst x
        change ((second :: tail).foldl step (step (List.ofFn x) first)).getD 9 false = _ at hh
        rw [keep _ _ _ (by simp [step])] at hh
        have hh' : (step (List.ofFn x) first).getD (List.ofFn x).length false =
            (x 4 || x 6) := by simpa using hh
        have eq := (readLast (List.ofFn x) (first.op.eval
          (first.inputs.map fun i => (List.ofFn x).getD i false))).symm.trans hh'
        simp only [step, base, eq]
      have correct (x : Fin 9 → Bool) :
          T.eval (base x ++ [GateOp.and.eval (second.inputs.map fun i =>
            (base x).getD i false)]) = edge x := by
        have h := congrFun hFun x
        change (tail.foldl step (step (step (List.ofFn x) first) second)).getD out false = edge x at h
        rw [firstStep] at h
        change T.eval (base x ++ [second.op.eval (second.inputs.map fun i =>
          (base x).getD i false)]) = edge x at h
        rw [hOp] at h
        exact h
      have secondAs (r : Bool ⊕ Fin 10)
          (eq : ∀ x : Fin 9 → Bool, GateOp.and.eval
            (second.inputs.map fun i => (base x).getD i false) =
              r.elim id (fun i => (base x).getD i.val false)) : False := by
        obtain ⟨x,hx⟩ := trivial r T hTFan hTSize
        exact hx (by rw [← eq]; exact correct x)
      have pair46 (eq : ∀ x : Fin 9 → Bool, GateOp.and.eval
          (second.inputs.map fun i => (base x).getD i false) = (x 4 && x 6)) : False := by
        have joint (x : Fin 9 → Bool) :
            T.eval (base x ++ [x 4 && x 6]) = edge x := by rw [← eq]; exact correct x
        have noOut (k : Fin 9) (hk : k = 4 ∨ k = 6) : out ≠ k.val := by
          intro ho
          let x (i : Fin 9) := decide (i = k)
          have z : edge x = false := by
            rcases hk with rfl | rfl <;> decide +kernel
          have h := joint x
          change (tail.foldl step (base x ++ [x 4 && x 6])).getD out false = edge x at h
          rw [z,ho,keep _ _ _ (by simp [baseLen]; omega)] at h
          have hlt : k.val < (base x).length := by rw [baseLen]; omega
          rw [List.getD_append _ _ _ _ hlt] at h
          rcases hk with rfl | rfl
          · change (base x).getD 4 false = false at h
            rw [base4] at h
            exact Bool.noConfusion (show true = false from h)
          · change (base x).getD 6 false = false at h
            rw [base6] at h
            exact Bool.noConfusion (show true = false from h)
        have reader : ∃ k : Fin 9, (k = 4 ∨ k = 6) ∧
            ∃ q ∈ T.gates, eff q k.val := by
          by_contra! none
          have dead (q : Gate) (hq : q ∈ tail) : ¬ eff q 4 ∧ ¬ eff q 6 := by
            constructor
            · exact none 4 (Or.inl rfl) q hq
            · exact none 6 (Or.inr rfl) q hq
          let a (i : Fin 9) := decide (i = 0 ∨ i = 4)
          let b (i : Fin 9) := decide (i = 0 ∨ i = 6)
          let w := base a ++ [a 4 && a 6]
          let v := base b ++ [b 4 && b 6]
          have rel (i : ℕ) (i4 : i ≠ 4) (i6 : i ≠ 6) :
              w.getD i false = v.getD i false := by
            by_cases h : i < 11
            · have tab : ∀ j : Fin 11, j.val ≠ 4 → j.val ≠ 6 →
                  w.getD j.val false = v.getD j.val false := by decide +kernel
              exact tab ⟨i,h⟩ i4 i6
            · rw [List.getD_eq_default _ _ (by simp [w,baseLen]; omega),
                List.getD_eq_default _ _ (by simp [v,baseLen]; omega)]
          have same := sweep tail w v (by simp [w,v,baseLen]) dead rel out
            (noOut 4 (Or.inl rfl)) (noOut 6 (Or.inr rfl))
          change T.eval w = T.eval v at same
          have az : edge a = true := by decide +kernel
          have bz : edge b = false := by decide +kernel
          have bad : true = false := az.symm.trans ((joint a).symm.trans
            (same.trans ((joint b).trans bz)))
          exact Bool.noConfusion bad
        obtain ⟨k,hk,hread⟩ := reader
        obtain ⟨D,hDf,hDs,hDe⟩ := contract T k hk hTFan hTSize hread
        apply minor k hk
        refine ⟨D,hDf,hDs,?_⟩
        intro x
        let y := Function.update x k false
        have low : (y 4 && y 6) = false := by
          rcases hk with rfl | rfl <;> simp [y]
        change circuitFun 9 D x = edge y
        exact (hDe x).trans (by simpa only [base,low,List.append_assoc,List.cons_append,List.nil_append] using joint y)
      have baseFar (x : Fin 9 → Bool) (i : ℕ) (hi : ¬ i < 10) :
          (base x).getD i false = false :=
        List.getD_eq_default _ _ (by rw [baseLen]; omega)
      cases pins : second.inputs with
      | nil => exact secondAs (.inl true) (fun x => by rw [pins]; rfl)
      | cons i is =>
        cases is with
        | nil =>
          by_cases hi : i < 10
          · exact secondAs (.inr ⟨i,hi⟩) (fun x => by
              rw [pins]
              change ((base x).getD i false && true) = (base x).getD i false
              exact Bool.and_true _)
          · exact secondAs (.inl false) (fun x => by
              rw [pins]
              change ((base x).getD i false && true) = false
              simp only [baseFar x i hi,Bool.false_and])
        | cons j js =>
          cases js with
          | cons k ks =>
            simp only [pins,List.length_cons] at arity
            omega
          | nil =>
            by_cases hi : i < 10
            · by_cases hj : j < 10
              · by_cases same : i = j
                · exact secondAs (.inr ⟨i,hi⟩) (fun x => by
                    rw [pins]
                    change ((base x).getD i false && ((base x).getD j false && true)) =
                      (base x).getD i false
                    simp only [same,Bool.and_true,Bool.and_self])
                · let a : Fin 10 := ⟨i,hi⟩
                  let b : Fin 10 := ⟨j,hj⟩
                  have core (x : Fin 9 → Bool) : GateOp.and.eval
                      (second.inputs.map fun k => (base x).getD k false) =
                      ((base x).getD i false && (base x).getD j false) := by
                    rw [pins]
                    change ((base x).getD i false && ((base x).getD j false && true)) = _
                    simp only [Bool.and_true]
                  have pinPair {a b : ℕ} (hh : a ≠ b) (hp : [i,j].Perm [a,b]) :
                      (i=a ∧ j=b) ∨ (i=b ∧ j=a) := by
                    have e1 := hp.mem_iff.mpr (by simp : a ∈ [a,b])
                    have e2 := hp.mem_iff.mpr (by simp : b ∈ [a,b])
                    simp only [List.mem_cons, List.not_mem_nil, or_false] at e1 e2
                    omega
                  by_cases h46 : [i,j].Perm [4,6]
                  · apply pair46
                    intro x
                    rw [core]
                    rcases pinPair (by decide) h46 with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
                    · rw [base4,base6]
                    · rw [base4,base6,Bool.and_comm]
                  by_cases h49 : [i,j].Perm [4,9]
                  · apply secondAs (.inr ⟨4,by decide⟩)
                    intro x
                    rw [core]
                    rcases pinPair (by decide) h49 with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
                      change _ = (base x).getD 4 false <;> simp only [base4,base9] <;>
                      cases e4 : x 4 <;> cases e6 : x 6 <;> rfl
                  by_cases h69 : [i,j].Perm [6,9]
                  · apply secondAs (.inr ⟨6,by decide⟩)
                    intro x
                    rw [core]
                    rcases pinPair (by decide) h69 with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
                      change _ = (base x).getD 6 false <;> simp only [base6,base9] <;>
                      cases e4 : x 4 <;> cases e6 : x 6 <;> rfl
                  obtain ⟨x,hx⟩ := proper a b (fun e => same (congrArg Fin.val e))
                    h46 h49 h69 (by simpa only [pins] using hOrder) T hTFan hTSize
                  exact hx (by rw [← core]; exact correct x)
              · exact secondAs (.inl false) (fun x => by
                  rw [pins]
                  change ((base x).getD i false && ((base x).getD j false && true)) = false
                  simp only [baseFar x j hj,Bool.false_and,Bool.and_false])
            · exact secondAs (.inl false) (fun x => by
                rw [pins]
                change ((base x).getD i false && ((base x).getD j false && true)) = false
                simp only [baseFar x i hi,Bool.false_and])
