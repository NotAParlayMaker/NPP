import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.GetD
import Mathlib.Tactic.Push
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The reflection and diagonal argument follow R_meta_2762_612.
-- Reflection fixes vertex zero and exchanges the pairs one/five, two/eight and six/seven.
-- The diagonal uses the general lower bound with an extra false input, checked in L-meta-2317.
set_option maxHeartbeats 800000 in
theorem PEqualNP.Outside.R_meta_2762_920
    (base : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x3 ++ [Bool.false]) = (x3 (0 : Fin (9 : ℕ)) && x3 (1 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (2 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (3 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (4 : Fin (9 : ℕ)) || x3 (4 : Fin (9 : ℕ)) && x3 (0 : Fin (9 : ℕ)) || x3 (0 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (6 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (5 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (8 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ)))) → (15 : ℕ) ≤ x1.size)
    (binaryLower :
      let f := fun (x : Fin 9 → Bool) =>
        ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
          fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))
      ∀ C : Circuit, FanInTwo C → (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = f x) →
        13 ≤ C.gates.countP (fun g => !(g.op.eval [false])))
    (off : let f := fun (x : Fin 9 → Bool) =>
             ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
               fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))
           ∀ k ∈ ([12,13,15,18,23,28] : List ℕ), ∀ C : Circuit, FanInTwo C → C.size ≤ 13 →
             C.gates.countP (fun g => g.op.eval [false]) ≤ 1 →
             ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++
               [!x 0, x (Fin.ofNat 9 (k / 10)) || x (Fin.ofNat 9 (k % 10))]) ≠ f x) :
    ∀ (x1 : List ℕ),   x1.length = (2 : ℕ) →     (∀ x3 ∈ x1, x3 = (1 : ℕ) ∨ x3 = (2 : ℕ) ∨ x3 = (3 : ℕ) ∨ x3 = (5 : ℕ) ∨ x3 = (8 : ℕ)) →       ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit),         PEqualNP.MetaComplexity.FanInTwo x4 →           x4.size ≤ (13 : ℕ) →             ∃ (x7 : Fin (9 : ℕ) → Bool),               have x8 : List Bool := List.ofFn x7 ++ [!x7 (0 : Fin (9 : ℕ))];               x4.eval (x8 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x9 : ℕ) => x8.getD x9 Bool.false) x1)]) ≠ (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ))) := by
  intro ops hlen allowed C hf hs
  obtain ⟨a, b, rfl⟩ : ∃ a b, ops = [a,b] := by
    cases ops with
    | nil => simp at hlen
    | cons a t =>
      cases t with
      | nil => simp at hlen
      | cons b t =>
        cases t with
        | nil => exact ⟨_, _, rfl⟩
        | cons => simp at hlen
  have ha := allowed a (by simp)
  have hb := allowed b (by simp)
  let A : Fin 9 := ⟨a, by omega⟩
  let B : Fin 9 := ⟨b, by omega⟩
  let f := fun (x : Fin 9 → Bool) =>
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
    x 6 && x 8 || x 8 && x 5
  let w := fun (x : Fin 9 → Bool) => List.ofFn x ++ [!x 0, x A || x B]
  have read (x : Fin 9 → Bool) (extra : List Bool) (i : Fin 9) :
      (List.ofFn x ++ extra).getD i.val false = x i := by
    have hi : i.val < (List.ofFn x).length := by simpa only [List.length_ofFn] using i.isLt
    rw [List.getD_append _ _ _ _ hi, List.getD_eq_getElem _ _ hi, List.getElem_ofFn]
  by_contra! agree
  have correct (x : Fin 9 → Bool) : C.eval (w x) = f x := by
    have e := Classical.not_not.mp (agree x)
    change C.eval ((List.ofFn x ++ [!x 0]) ++
      [((List.ofFn x ++ [!x 0]).getD A.val false || ((List.ofFn x ++ [!x 0]).getD B.val false || false))]) = _ at e
    simpa only [w, read, Bool.or_false, List.append_assoc, List.cons_append, List.nil_append] using e
  let move := fun (r : ℕ → ℕ) (g : Gate) => Gate.mk g.op (g.inputs.map r)
  let relabel := fun (r : ℕ → ℕ) => Circuit.mk (C.gates.map (move r)) (r C.output)
  have fan (r : ℕ → ℕ) : FanInTwo (relabel r) := by
    intro g hg
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hg
    exact ⟨(hf t ht).1, by simpa [move] using (hf t ht).2⟩
  have transport (r : ℕ → ℕ) (low : ∀ i < 11, r i < 11) (high : ∀ i, 11 ≤ i → r i = i)
      (u v : List Bool) (hu : u.length = 11) (hv : v.length = 11)
      (h : ∀ i, v.getD (r i) false = u.getD i false) : (relabel r).eval v = C.eval u := by
    let step := fun (t : List Bool) (g : Gate) => t ++ [g.op.eval (g.inputs.map fun j => t.getD j false)]
    have loop (gs : List Gate) (u v : List Bool) (heq : v.length = u.length) (large : 11 ≤ u.length)
        (inv : ∀ i, v.getD (r i) false = u.getD i false) (i : ℕ) :
        ((gs.map (move r)).foldl step v).getD (r i) false = (gs.foldl step u).getD i false := by
      induction gs generalizing u v with
      | nil => exact inv i
      | cons g gs ih =>
        change ((gs.map (move r)).foldl step (step v (move r g))).getD (r i) false =
          (gs.foldl step (step u g)).getD i false
        have ins : ((move r g).inputs.map fun j => v.getD j false) = (g.inputs.map fun j => u.getD j false) := by
          simp only [move, List.map_map, Function.comp_def, inv]
        apply ih _ _ (by simp [step, heq]) (by simp [step]; omega)
        intro j
        by_cases jl : j < u.length
        · have rj : r j < v.length := by
            by_cases hh : j < 11
            · have hh' := low j hh
              omega
            · rw [high j (by omega), heq]
              exact jl
          exact (List.getD_append _ _ _ _ rj).trans ((inv j).trans (List.getD_append _ _ _ _ jl).symm)
        · rw [high j (by omega)]
          simp only [step, move, List.getD, List.getElem?_append, heq, ite_eq_right jl]
          change ([g.op.eval ((move r g).inputs.map fun j => v.getD j false)][j-u.length]?).getD false = _
          rw [ins]
          rfl
    exact loop C.gates u v (hv.trans hu.symm) hu.ge h C.output
  let edgeList := fun x : Fin 9 → Bool =>
    ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
      fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))
  have edgeList_eq : ∀ x : Fin 9 → Bool, f x = edgeList x := by decide +kernel
  let prefixed := Circuit.mk (Gate.mk .not [0] :: Gate.mk .or [A.val, B.val] :: C.gates) C.output
  have prefixed_fan : FanInTwo prefixed := by
    intro g hg
    change g ∈ Gate.mk .not [0] :: Gate.mk .or [A.val, B.val] :: C.gates at hg
    simp only [List.mem_cons] at hg
    rcases hg with rfl | rfl | hg
    · simp
    · simp
    · exact hf g hg
  have prefixed_eq (x : Fin 9 → Bool) : prefixed.eval (List.ofFn x) = C.eval (w x) := by
    have first : (List.ofFn x).getD 0 false = x 0 := by
      have fromEmpty := read x [] (0 : Fin 9)
      rwa [List.append_nil] at fromEmpty
    let initialWires := List.ofFn x ++ [!((List.ofFn x).getD 0 false)]
    change C.eval (initialWires ++
      [initialWires.getD A.val false || (initialWires.getD B.val false || false)]) = C.eval (w x)
    have boundary : initialWires = List.ofFn x ++ [!x 0] := by
      dsimp only [initialWires]
      rw [first]
    rw [boundary, read x [!x 0] A, read x [!x 0] B]
    simp only [Bool.or_false, w, List.append_assoc, List.cons_append, List.nil_append]
  have countLower := binaryLower prefixed prefixed_fan
    (fun x => (prefixed_eq x).trans ((correct x).trans (edgeList_eq x)))
  change 13 ≤ (Gate.mk .not [0] :: Gate.mk .or [A.val, B.val] :: C.gates).countP
    (fun g => !(g.op.eval [false])) at countLower
  simp only [List.countP_cons] at countLower
  have budget : C.gates.countP (fun g => g.op.eval [false]) ≤ 1 := by
    change 13 ≤ C.gates.countP (fun g => !(g.op.eval [false])) + 1 at countLower
    have total :
        C.gates.length = C.gates.countP (fun g => g.op.eval [false]) +
          C.gates.countP (fun g => !(g.op.eval [false])) := by
      rw [List.length_eq_countP_add_countP (fun g => g.op.eval [false])]
      congr 1
    change C.gates.length ≤ 13 at hs
    omega
  by_cases eq : A = B
  · let r := fun i : ℕ => if i = 9 then 10 else if i = 10 then A.val else i
    let D := relabel r
    let E := Circuit.mk (Gate.mk .not [0] :: D.gates) D.output
    have ef : FanInTwo E := by
      intro g hg
      change g ∈ Gate.mk .not [0] :: D.gates at hg
      rcases List.mem_cons.mp hg with rfl | ht
      · exact ⟨Or.inr (Or.inr rfl), by decide⟩
      · exact fan r g ht
    have bound := base E ef (by
      intro x
      let u := w x
      let v := List.ofFn x ++ [false, !x 0]
      have tr := transport r (by intro i hi; dsimp only [r]; split <;> first | decide | split <;> omega)
        (by intro i hi; simp [r, show i ≠ 9 by omega, show i ≠ 10 by omega])
        u v (by simp [u, w]) (by simp [v]) (by
        intro i
        by_cases hi : i < 9
        · have ri : r i = i := by simp [r, show i ≠ 9 by omega, show i ≠ 10 by omega]
          rw [ri]
          exact (read x _ ⟨i,hi⟩).trans (read x _ ⟨i,hi⟩).symm
        · by_cases h9 : i = 9
          · subst i
            simp [r, u, v, w, List.getD]
          · by_cases h10 : i = 10
            · subst i
              change v.getD A.val false = (w x).getD 10 false
              rw [show v.getD A.val false = x A from read x _ A]
              simp [w, eq, List.getD]
            · have h11 : 11 ≤ i := by omega
              rw [List.getD_eq_default _ _ (by simp [r, h9, h10, v]; omega),
                  List.getD_eq_default _ _ (by simp [u, w]; omega)])
      have start : (List.ofFn x ++ [false]) ++
          [GateOp.not.eval ([0].map fun j => (List.ofFn x ++ [false]).getD j false)] = v := by
        change (List.ofFn x ++ [false]) ++ [!((List.ofFn x ++ [false]).getD 0 false)] = v
        simp [v, List.getD]
      change D.eval ((List.ofFn x ++ [false]) ++ [_]) = _
      rw [start]
      exact tr.trans (correct x))
    change 15 ≤ (_ :: C.gates.map (move r)).length at bound
    simp only [List.length_cons, List.length_map] at bound
    change C.gates.length ≤ 13 at hs
    omega
  · let perm := fun (s : Bool) (i : Fin 9) => if s then (![0,5,8,3,4,1,7,6,2] : Fin 9 → Fin 9) i else i
    let V := ([1,2,3,5,8] : List (Fin 9))
    let codes := ([12,13,15,18,23,28] : List ℕ)
    have reps : ∀ a ∈ V, ∀ b ∈ V, a ≠ b →
        ∃ k ∈ codes, ∃ s : Bool,
          ((perm s a, perm s b) = (Fin.ofNat 9 (k / 10), Fin.ofNat 9 (k % 10)) ∨
           (perm s b, perm s a) = (Fin.ofNat 9 (k / 10), Fin.ofNat 9 (k % 10))) := by
      decide +kernel
    have aV : A ∈ V := by simpa [V, A, Fin.ext_iff] using ha
    have bV : B ∈ V := by simpa [V, B, Fin.ext_iff] using hb
    obtain ⟨k, hk, s, hab⟩ := reps A aV B bV eq
    let r := fun i : ℕ => if h : i < 9 then (perm s ⟨i,h⟩).val else i
    have fixes : perm s 0 = 0 := by cases s <;> decide
    have symm : ∀ s : Bool, ∀ x : Fin 9 → Bool, f (x ∘ perm s) = f x := by decide +kernel
    have relabel_budget : (relabel r).gates.countP (fun g => g.op.eval [false]) ≤ 1 := by
      change (C.gates.map (move r)).countP (fun g => g.op.eval [false]) ≤ 1
      rw [List.countP_map]
      exact budget
    obtain ⟨x, hx⟩ := off k hk (relabel r) (fan r)
      (by change (C.gates.map (move r)).length ≤ 13; rw [List.length_map]; exact hs) relabel_budget
    let y := x ∘ perm s
    let v := List.ofFn x ++ [!x 0, x (Fin.ofNat 9 (k / 10)) || x (Fin.ofNat 9 (k % 10))]
    have hor : (y A || y B) = (x (Fin.ofNat 9 (k / 10)) || x (Fin.ofNat 9 (k % 10))) := by
      rcases hab with h | h
      · cases Prod.mk.inj h with | intro h1 h2 => simp [y, Function.comp_def, h1, h2]
      · cases Prod.mk.inj h with | intro h1 h2 => simp [y, Function.comp_def, h1, h2, Bool.or_comm]
    have tr := transport r (by
      intro i hi
      by_cases h : i < 9
      · simpa [r,h] using (show (perm s ⟨i,h⟩).val < 11 by have := (perm s ⟨i,h⟩).isLt; omega)
      · simpa [r,h] using hi)
      (by intro i hi; simp [r, show ¬i < 9 by omega]) (w y) v (by simp [w]) (by simp [v]) (by
      intro i
      by_cases h : i < 9
      · rw [show r i = (perm s ⟨i,h⟩).val by simp [r,h]]
        exact (read x _ (perm s ⟨i,h⟩)).trans (read y _ ⟨i,h⟩).symm
      · simp only [v, w, r, dite_eq_right h, List.getD, List.getElem?_append, List.length_ofFn, ite_eq_right h, hor, show y 0 = x 0 by simp [y, fixes]])
    have table : ∀ x : Fin 9 → Bool, f x = (([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
      fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))) := by decide +kernel
    exact hx (tr.trans ((correct y).trans ((symm s x).trans (table x))))
