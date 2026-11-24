import Mathlib
import PEqualNP.Defs

open PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_3919_52
    (distinguish : let E := fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)); let canSkip := fun (v h : Fin 9) (d : Bool) => (v = 0 ∧ ((h = 1 ∧ d = true) ∨ ((h = 2 ∨ h = 6) ∧ d = false))) ∨ (v = 1 ∧ ((h = 0 ∧ d = true) ∨ ((h = 4 ∨ h = 5) ∧ d = false))); ∀ (a b : Fin 9), a < b → ∀ (p q : Bool) (i j : Fin 9), (i < j ∨ (i = j ∧ ¬ ((i = a ∧ canSkip i b q) ∨ (i = b ∧ canSkip i a p)))) → ∃ x y : Fin 9 → Bool, (∀ k, k ≠ i → k ≠ j → x k = y k) ∧ (x 0 || x 1) = (y 0 || y 1) ∧ ((x a == p) && (x b == q)) = ((y a == p) && (y b == q)) ∧ E x ≠ E y)
    (sharing : let E := fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)); ∀ (a b : Fin 9), a < b → ∀ (p q s : Bool) (D : PEqualNP.MetaComplexity.BinaryCircuit), (∀ g ∈ D.gates, ∃ u v : Bool, g.op = fun l r => (l == u) && (r == v)) → (∀ x, (D.eval (List.ofFn x ++ [x 0 || x 1, (x a == p) && (x b == q)]) != s) = E x) → ¬ (D.gates.flatMap fun g => [g.left,g.right]).Nodup)
    (lower : let E := fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)); let canSkip := fun (v h : Fin 9) (d : Bool) => (v = 0 ∧ ((h = 1 ∧ d = true) ∨ ((h = 2 ∨ h = 6) ∧ d = false))) ∨ (v = 1 ∧ ((h = 0 ∧ d = true) ∨ ((h = 4 ∨ h = 5) ∧ d = false))); ∀ (a b : Fin 9), a < b → ∀ (p q s : Bool) (D : PEqualNP.MetaComplexity.BinaryCircuit), (∀ g ∈ D.gates, ∃ u v : Bool, g.op = fun l r => (l == u) && (r == v)) → (∀ t : Fin D.size, (D.gates.get t).left < (D.gates.get t).right ∧ (D.gates.get t).right < 11+t.val) → D.output = 11 + D.size - 1 → (∀ i j : Fin 9, (i < j ∨ (i = j ∧ ¬ ((i = a ∧ canSkip i b q) ∨ (i = b ∧ canSkip i a p)))) → ∃ g ∈ D.gates, g.left = i.val ∨ g.right = i.val ∨ g.left = j.val ∨ g.right = j.val) → (∀ x, (D.eval (List.ofFn x ++ [x 0 || x 1, (x a == p) && (x b == q)]) != s) = E x) → ¬ (D.gates.flatMap fun g => [g.left,g.right]).Nodup → 13 ≤ D.size) : have x1 : PEqualNP.MetaComplexity.BinaryCircuit → Prop := fun (x1 : PEqualNP.MetaComplexity.BinaryCircuit) => ∀ x2 ∈ x1.gates, ∃ (x4 : Bool) (x5 : Bool), x2.op = fun (x6 x7 : Bool) => x6 == x4 && x7 == x5; have x2 : ℕ → PEqualNP.MetaComplexity.BinaryCircuit → Prop := fun (x2 : ℕ) (x3 : PEqualNP.MetaComplexity.BinaryCircuit) => ∀ (x4 : Fin x3.size), (x3.gates.get x4).left < (x3.gates.get x4).right ∧ (x3.gates.get x4).right < x2 + ↑x4; have x3 : (Fin (9 : ℕ) → Bool) → Bool := fun (x3 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x4 : ℕ) => x3 (Fin.ofNat (9 : ℕ) (x4 / (10 : ℕ))) && x3 (Fin.ofNat (9 : ℕ) (x4 % (10 : ℕ))); ∀ (x4 : PEqualNP.MetaComplexity.BinaryCircuit) (x5 : Bool) (x6 : (0 : ℕ) < x4.size), x1 x4 → x2 (10 : ℕ) x4 → x4.output = (10 : ℕ) + x4.size - (1 : ℕ) → (x4.gates.get (⟨(0 : ℕ), x6⟩ : Fin x4.gates.length)).right < (9 : ℕ) → (∀ (x11 : Fin (9 : ℕ) → Bool), (x4.eval (List.ofFn x11 ++ [x11 (0 : Fin (9 : ℕ)) || x11 (1 : Fin (9 : ℕ))]) != x5) = x3 x11) → (14 : ℕ) ≤ x4.size := by
  classical
  dsimp only
  intro C s pos normal ordered output raw computes
  obtain ⟨gs,o⟩ := C
  cases gs with
  | nil => exact False.elim (Nat.not_lt_zero _ pos)
  | cons g gs =>
    let D : BinaryCircuit := ⟨gs,o⟩
    change g.right < 9 at raw
    have ord := ordered ⟨0,pos⟩
    change g.left < g.right ∧ _ at ord
    let a : Fin 9 := ⟨g.left,by omega⟩
    let b : Fin 9 := ⟨g.right,raw⟩
    have ab : a < b := ord.1
    obtain ⟨p,q,op⟩ := normal g (by simp)
    let base := fun x : Fin 9 → Bool => List.ofFn x ++ [x 0 || x 1]
    let start := fun x : Fin 9 → Bool => List.ofFn x ++ [x 0 || x 1,(x a == p) && (x b == q)]
    let edge := fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
      fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))
    let step := fun (w : List Bool) (gate : BinaryGate) =>
      w ++ [gate.op (w.getD gate.left false) (w.getD gate.right false)]
    have input (x : Fin 9 → Bool) (k : Fin 9) (l : List Bool) :
        (List.ofFn x ++ l).getD k.val false = x k := by
      rw [List.getD_append _ _ _ _ (by simp),List.getD_eq_getElem _ _ (by simp),List.getElem_ofFn]
    have first (x : Fin 9 → Bool) : step (base x) g = start x := by
      change (List.ofFn x ++ [x 0 || x 1]) ++ [g.op ((base x).getD a.val false) ((base x).getD b.val false)] = _
      rw [show (base x).getD a.val false = x a from input x a _,
          show (base x).getD b.val false = x b from input x b _,op,List.append_assoc]
      rfl
    have shifted (x : Fin 9 → Bool) : (D.eval (start x) != s) = edge x := by
      have h := computes x
      change (((gs.foldl step (step (base x) g)).getD o false) != s) = edge x at h
      rw [first] at h
      exact h
    let canSkip := fun (v h : Fin 9) (d : Bool) => (v = 0 ∧ ((h = 1 ∧ d = true) ∨ ((h = 2 ∨ h = 6) ∧ d = false))) ∨ (v = 1 ∧ ((h = 0 ∧ d = true) ∨ ((h = 4 ∨ h = 5) ∧ d = false)))
    have usePair (i j : Fin 9) (ij : i < j ∨ (i = j ∧ ¬ ((i = a ∧ canSkip i b q) ∨ (i = b ∧ canSkip i a p)))) : ∃ z ∈ gs,
        z.left = i.val ∨ z.right = i.val ∨ z.left = j.val ∨ z.right = j.val := by
      by_contra missing
      obtain ⟨x,y,same,aux,bit,diff⟩ := distinguish a b ab p q i j ij
      have equalRaw (k : ℕ) (ki : k ≠ i.val) (kj : k ≠ j.val) :
          (start x).getD k false = (start y).getD k false := by
        by_cases hk : k < 9
        · let t : Fin 9 := ⟨k,hk⟩
          exact (input x t _).trans ((same t (fun h => ki (congrArg Fin.val h))
              (fun h => kj (congrArg Fin.val h))).trans (input y t _).symm)
        · change (List.ofFn x ++ _).getD k false = (List.ofFn y ++ _).getD k false
          rw [List.getD_append_right _ _ _ _ (by simp; omega),
              List.getD_append_right _ _ _ _ (by simp; omega),List.length_ofFn,List.length_ofFn,aux,bit]
      have transfer (tail : List BinaryGate) (inside : ∀ z ∈ tail, z ∈ gs) (w v : List Bool)
          (lengths : w.length = v.length)
          (agree : ∀ k : ℕ, k ≠ i.val → k ≠ j.val → w.getD k false = v.getD k false) :
          ∀ k : ℕ, k ≠ i.val → k ≠ j.val →
            (tail.foldl step w).getD k false = (tail.foldl step v).getD k false := by
        induction tail generalizing w v with
        | nil => exact agree
        | cons z rest ih =>
          have avoids : ¬ (z.left = i.val ∨ z.right = i.val ∨ z.left = j.val ∨ z.right = j.val) :=
            fun hz => missing ⟨z,inside z (by simp),hz⟩
          have zl := agree z.left (fun h => avoids (Or.inl h)) (fun h => avoids (Or.inr (Or.inr (Or.inl h))))
          have zr := agree z.right (fun h => avoids (Or.inr (Or.inl h))) (fun h => avoids (Or.inr (Or.inr (Or.inr h))))
          apply ih (fun z hz => inside z (List.mem_cons_of_mem _ hz)) (step w z) (step v z) (by simp [step,lengths])
          intro k ki kj
          change (w ++ [_]).getD k false = (v ++ [_]).getD k false
          by_cases h : k < w.length
          · rw [List.getD_append _ _ _ _ h,List.getD_append _ _ _ _ (lengths ▸ h)]
            exact agree k ki kj
          · rw [List.getD_append_right _ _ _ _ (by omega),List.getD_append_right _ _ _ _ (by omega),lengths,zl,zr]
      have big : 10 ≤ o := by
        change o = 10 + (g :: gs).length - 1 at output
        simp only [List.length_cons] at output
        omega
      have equal := transfer gs (fun _ h => h) (start x) (start y) (by simp [start]) equalRaw o
          (by have := i.isLt; omega) (by have := j.isLt; omega)
      change D.eval (start x) = D.eval (start y) at equal
      exact diff ((shifted x).symm.trans ((congrArg (fun r : Bool => r != s) equal).trans (shifted y)))
    have tailOrder (t : Fin D.size) : (D.gates.get t).left < (D.gates.get t).right ∧ (D.gates.get t).right < 11+t.val := by
      have h := ordered ⟨t.val+1,Nat.succ_lt_succ t.isLt⟩
      change (gs.get t).left < (gs.get t).right ∧ (gs.get t).right < 10 + (t.val+1) at h
      exact ⟨h.1,by change (gs.get t).right < 11+t.val; omega⟩
    have tailOut : D.output = 11 + D.size - 1 := by
      change o = 10 + (g :: gs).length - 1 at output
      change o = 11 + gs.length - 1
      simp only [List.length_cons] at output
      omega
    have gatesNormal : ∀ z ∈ D.gates, ∃ u v : Bool, z.op = fun l r => (l == u) && (r == v) :=
      fun z hz => normal z (List.mem_cons_of_mem g hz)
    have repeated := sharing a b ab p q s D gatesNormal shifted
    have bound := lower a b ab p q s D gatesNormal tailOrder tailOut usePair shifted repeated
    change 13 ≤ gs.length at bound
    change 14 ≤ (g :: gs).length
    simp only [List.length_cons]
    omega
