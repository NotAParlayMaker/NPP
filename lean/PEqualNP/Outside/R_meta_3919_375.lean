import Mathlib
import PEqualNP.Defs

open PEqualNP.MetaComplexity

-- Remove the first signed gate. Pairs of input rows force the remaining circuit
-- to read every original input except in the explicitly listed cases.
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_3919_375
    (allRead : ∀ (D : BinaryCircuit) (a b : Fin 9) (u v c : Bool), a < b →
      (∀ g ∈ D.gates, ∃ (c d : Bool), g.op = fun s t => (s == c) && (t == d)) →
      (∀ k : Fin D.size, (D.gates.get k).left < (D.gates.get k).right ∧ (D.gates.get k).right < 11 + k.val) →
      D.output = 11 + D.size - 1 →
      (∀ i : Fin 9, ∃ g ∈ D.gates, g.left = i.val ∨ g.right = i.val) →
      (∀ x : Fin 9 → Bool, (D.eval (List.ofFn x ++ [x 0 || x 1,(x a == u) && (x b == v)]) != c) =
        [1,12,23,34,40,5,16,27,38,57,68,85].any fun (e : Nat) => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))) → 13 ≤ D.size)
    (omitted : ∀ (D : BinaryCircuit) (i j : Fin 9) (u c : Bool), i.val < 2 →
      j ∈ (if i = 0 then [2,6,1] else [4,5,0] : List (Fin 9)) →
      (∀ g ∈ D.gates, ∃ (c d : Bool), g.op = fun s t => (s == c) && (t == d)) →
      (∀ k : Fin D.size, (D.gates.get k).left < (D.gates.get k).right ∧ (D.gates.get k).right < 11 + k.val) →
      D.output = 11 + D.size - 1 →
      (∀ x : Fin 9 → Bool, (D.eval (List.ofFn (fun k => if k = i then false else x k) ++
          [x 0 || x 1,(x i == u) && (x j == decide (j.val < 2))]) != c) =
        [1,12,23,34,40,5,16,27,38,57,68,85].any fun (e : Nat) => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))) → 13 ≤ D.size) :
    have x1 : PEqualNP.MetaComplexity.BinaryCircuit → Prop := fun (x1 : PEqualNP.MetaComplexity.BinaryCircuit) => ∀ x2 ∈ x1.gates, ∃ (x4 : Bool) (x5 : Bool), x2.op = fun (x6 x7 : Bool) => x6 == x4 && x7 == x5; have x2 : ℕ → PEqualNP.MetaComplexity.BinaryCircuit → Prop := fun (x2 : ℕ) (x3 : PEqualNP.MetaComplexity.BinaryCircuit) => ∀ (x4 : Fin x3.size), (x3.gates.get x4).left < (x3.gates.get x4).right ∧ (x3.gates.get x4).right < x2 + ↑x4; have x3 : (Fin (9 : ℕ) → Bool) → Bool := fun (x3 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x4 : ℕ) => x3 (Fin.ofNat (9 : ℕ) (x4 / (10 : ℕ))) && x3 (Fin.ofNat (9 : ℕ) (x4 % (10 : ℕ))); ∀ (x4 : PEqualNP.MetaComplexity.BinaryCircuit) (x5 : Bool) (x6 : (0 : ℕ) < x4.size), x1 x4 → x2 (10 : ℕ) x4 → x4.output = (10 : ℕ) + x4.size - (1 : ℕ) → (x4.gates.get (⟨(0 : ℕ), x6⟩ : Fin x4.gates.length)).right < (9 : ℕ) → (∀ (x11 : Fin (9 : ℕ) → Bool), (x4.eval (List.ofFn x11 ++ [x11 (0 : Fin (9 : ℕ)) || x11 (1 : Fin (9 : ℕ))]) != x5) = x3 x11) → (14 : ℕ) ≤ x4.size := by
  let edge (x : Fin 9 → Bool) :=
    [1,12,23,34,40,5,16,27,38,57,68,85].any fun (e : Nat) =>
      x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))

  let selected (a b : Fin 9) (u v : Bool) (x : Fin 9 → Bool) :=
    (x a == u) && (x b == v)

  let miss (a b : Fin 9) (u v : Bool) (i : Fin 9) : Bool :=
    (i == 0 && ((a == 0 && b == 1 && v) || (a == 0 && (b == 2 || b == 6) && !v))) ||
    (i == 1 && ((a == 0 && b == 1 && u) || (a == 1 && (b == 4 || b == 5) && !v)))

  let contexts (i : Fin 9) : List Nat :=
    [[2,402,42],[1,201,261],[2,201,50,258],[4,402,69,36],[1,42,69,385],
     [1,402,69,9],[2,261,42,146],[4,42,69,276],[8,116,137,10]].getD i.val []

  let row (r : Nat) (i : Fin 9) := r.testBit i.val
  let flip (i : Fin 9) (x : Fin 9 → Bool) (j : Fin 9) := if j=i then !x j else x j
  let seed (x : Fin 9 → Bool) := x 0 || x 1

  let test (a b : Fin 9) (u v : Bool) (i : Fin 9) (r : Nat) :=
    let x := row r
    let y := flip i x
    (edge x != edge y) && (seed x == seed y) && (selected a b u v x == selected a b u v y)

  have checked : ∀ (a b : Fin 9) (u v : Bool) (i : Fin 9), a < b →
      miss a b u v i = false → (contexts i).any (test a b u v i) = true := by
    dsimp only [miss,contexts,test,flip,seed,selected,edge,row]
    decide +kernel

  let step (w : List Bool) (g : BinaryGate) :=
    w ++ [g.op (w.getD g.left false) (w.getD g.right false)]

  let reads (gs : List BinaryGate) (i : Nat) := ∃ g ∈ gs, g.left = i ∨ g.right = i

  have invisible (gs : List BinaryGate) (i : Nat) (unread : ¬ reads gs i)
      (w z : List Bool) (len : w.length = z.length)
      (same : ∀ j, j ≠ i → w.getD j false = z.getD j false) :
      ∀ j, j ≠ i → (gs.foldl step w).getD j false = (gs.foldl step z).getD j false := by
    induction gs generalizing w z with
    | nil => exact same
    | cons g gs ih =>
      have hgl : g.left ≠ i := fun h => unread ⟨g,by simp,Or.inl h⟩
      have hgr : g.right ≠ i := fun h => unread ⟨g,by simp,Or.inr h⟩
      have tail : ¬ reads gs i := by
        rintro ⟨q,hq,h⟩
        exact unread ⟨q,List.mem_cons_of_mem _ hq,h⟩
      simp only [List.foldl_cons]
      apply ih tail
      · simp [step,len]
      · intro j hj
        dsimp only [step]
        rw [same _ hgl,same _ hgr]
        simp only [List.getD_eq_getElem?_getD,List.getElem?_append]
        by_cases small : j < w.length
        · have small' : j < z.length := len ▸ small
          simpa [small,small',List.getD_eq_getElem?_getD] using same j hj
        · have large : ¬ j < z.length := len ▸ small
          simp [small,large,len]

  let bank (a b : Fin 9) (u v : Bool) (x : Fin 9 → Bool) :=
    List.ofFn x ++ [seed x,selected a b u v x]

  have forced (a b : Fin 9) (u v : Bool) (ab : a < b) (D : BinaryCircuit) (out : 9 ≤ D.output)
      (c : Bool) (sem : ∀ x : Fin 9 → Bool, (D.eval (bank a b u v x) != c) = edge x)
      (i : Fin 9) (hi : miss a b u v i = false) : reads D.gates i.val := by
    obtain ⟨r,_,hr⟩ := List.any_eq_true.mp (checked a b u v i ab hi)
    let x := row r
    let y := flip i x
    change ((edge x != edge y) && (seed x == seed y) && (selected a b u v x == selected a b u v y)) = true at hr
    simp only [Bool.and_eq_true,bne_iff_ne,beq_iff_eq] at hr
    by_contra unread
    have same (j : Nat) (hj : j ≠ i.val) :
        (bank a b u v x).getD j false = (bank a b u v y).getD j false := by
      by_cases h : j < 9
      · have neq : (⟨j,h⟩ : Fin 9) ≠ i := fun eq => hj (congrArg Fin.val eq)
        simp only [bank,List.getD_eq_getElem?_getD,List.getElem?_append,List.length_ofFn,h,if_true,List.getElem?_ofFn,dif_pos,Option.getD_some,y,flip,if_neg neq]
      · simp only [bank,List.getD_eq_getElem?_getD,List.getElem?_append,List.length_ofFn,h,if_false,hr.1.2,hr.2]
    have eq := invisible D.gates i.val unread _ _ (by simp [bank]) same D.output (by omega)
    change D.eval (bank a b u v x) = D.eval (bank a b u v y) at eq
    exact hr.1.1 ((sem x).symm.trans ((congrArg (· != c) eq).trans (sem y)))

  dsimp only
  intro C c pos ops order out first sem
  rcases C with ⟨gs,o⟩
  cases gs with
  | nil => exact False.elim (Nat.lt_irrefl 0 pos)
  | cons g gs =>
    let D : BinaryCircuit := ⟨gs,o⟩
    have ord := order ⟨0,pos⟩
    change g.left < g.right ∧ g.right < 10+0 at ord
    change g.right < 9 at first
    let a : Fin 9 := ⟨g.left,by omega⟩
    let b : Fin 9 := ⟨g.right,first⟩
    have ab : a < b := ord.1
    obtain ⟨u,v,hg⟩ := ops g (by simp)
    have hops : ∀ t ∈ D.gates, ∃ (q s : Bool), t.op = fun l r => (l == q) && (r == s) :=
      fun t ht => ops t (List.mem_cons_of_mem g ht)
    have ordering (k : Fin D.size) : (D.gates.get k).left < (D.gates.get k).right ∧
        (D.gates.get k).right < 11 + k.val := by
      have h := order (⟨k.val+1,by have := k.isLt; change k.val < gs.length at this;
                                    change k.val+1 < (g::gs).length; simp; omega⟩)
      change (gs.get k).left < (gs.get k).right ∧ (gs.get k).right < 10 + (k.val+1) at h
      exact ⟨h.1,by have := h.2; change (gs.get k).right < 11+k.val; omega⟩
    have output : D.output = 11 + D.size - 1 := by
      change o = 10 + (g::gs).length - 1 at out
      change o = 11 + gs.length - 1
      simp only [List.length_cons] at out
      omega
    have out9 : 9 ≤ D.output := by omega
    have tailSem (x : Fin 9 → Bool) : (D.eval (bank a b u v x) != c) = edge x := by
      have get (i : Fin 9) : (List.ofFn x ++ [seed x]).getD i.val false = x i := by
        simp only [List.getD_eq_getElem?_getD,List.getElem?_append,List.length_ofFn,i.isLt,if_true,
          List.getElem?_ofFn,dif_pos,Option.getD_some]
      have h := sem x
      change ((gs.foldl step (step (List.ofFn x ++ [seed x]) g)).getD o false != c) = edge x at h
      have hw : step (List.ofFn x ++ [seed x]) g = bank a b u v x := by
        change (List.ofFn x ++ [seed x]) ++ [g.op ((List.ofFn x ++ [seed x]).getD a.val false)
          ((List.ofFn x ++ [seed x]).getD b.val false)] = _
        rw [hg,get,get]
        simp only [bank,selected,List.append_assoc,List.singleton_append]
      rw [hw] at h
      exact h
    suffices h : 13 ≤ D.size by
      change 13 ≤ gs.length at h
      change 14 ≤ (g::gs).length
      simp only [List.length_cons]
      omega
    by_cases all : ∀ i : Fin 9, reads D.gates i.val
    · exact allRead D a b u v c ab hops ordering output all tailSem
    · push_neg at all
      obtain ⟨i,absent⟩ := all
      have may : miss a b u v i = true := by
        cases e : miss a b u v i
        · exact False.elim (absent (forced a b u v ab D out9 c tailSem i e))
        · rfl
      have choices : ∀ (a b : Fin 9) (u v : Bool) (i : Fin 9), a < b → miss a b u v i = true →
          i.val < 2 ∧ ∃ (j : Fin 9) (s : Bool),
            j ∈ (if i = 0 then [2,6,1] else [4,5,0] : List (Fin 9)) ∧
            ((i=a ∧ j=b ∧ s=u ∧ decide (j.val<2)=v) ∨ (i=b ∧ j=a ∧ s=v ∧ decide (j.val<2)=u)) := by
        dsimp only [miss]
        decide +kernel
      obtain ⟨hi,j,s,hj,orient⟩ := choices a b u v i ab may
      apply omitted D i j s c hi hj hops ordering output
      intro x
      let z : Fin 9 → Bool := fun k => if k=i then false else x k
      have factor : (x i == s && (x j == decide (j.val<2))) = selected a b u v x := by
        rcases orient with ⟨e1,e2,e3,e4⟩|⟨e1,e2,e3,e4⟩
        · simpa only [selected,e1,e2,e3,e2 ▸ e4]
        · simpa only [selected,e1,e2,e3,e2 ▸ e4,Bool.and_comm]
      rw [factor]
      let aux := [seed x, selected a b u v x]
      have eq := invisible D.gates i.val absent (List.ofFn z ++ aux) (List.ofFn x ++ aux) (by simp)
        (by
          intro k hk
          by_cases h : k < 9
          · have ne : (⟨k,h⟩ : Fin 9) ≠ i := fun e => hk (congrArg Fin.val e)
            simp only [List.getD_eq_getElem?_getD,List.getElem?_append,List.length_ofFn,h,if_true,
              List.getElem?_ofFn,dif_pos,Option.getD_some,z,if_neg ne]
          · simp only [List.getD_eq_getElem?_getD,List.getElem?_append,List.length_ofFn,h,if_false])
        D.output (by omega)
      exact (congrArg (· != c) eq).trans (tailSem x)
