import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Count distinct gate functions after removing one vertex or the ends of an edge.
-- The general compression statement follows the formulation of eyeb0l in pull request 7140.
set_option maxRecDepth 16000 in
set_option maxHeartbeats 6000000 in
theorem PEqualNP.Outside.R_meta_4139_828
    (compress : ∀ (n m : ℕ) (C : Circuit) (a : Fin m→(Fin n→Bool)→Bool),
    let A:=((Finset.univ.image (fun i : Fin n=>fun x : Fin n→Bool=>x i)) ∪ {fun _=>false,fun _=>true} : Finset ((Fin n→Bool)→Bool))
    let w:=fun (j : ℕ) (x : Fin n→Bool)=>(C.wires (List.ofFn (fun k=>a k x))).getD (m+j) false
    let f:=fun x : Fin n→Bool=>C.eval (List.ofFn (fun k=>a k x))
    (∀i,a i∈A) → (∃x y,f x≠f y) → FanInTwo C →
      HasCircuitSize n f ((((Finset.range C.size).image w) \ A).card))
    (single : ¬ HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) 14)
    (pair : ¬ HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)) 12)
    (remaining : ∀ C : Circuit,
    let edges : List ℕ := [1,12,23,34,40,5,16,27,38,49,57,79,96,68,85]
    let A := ((Finset.univ.image (fun i : Fin 10 => fun x : Fin 10 → Bool => x i)) ∪
      {fun _ => false, fun _ => true} : Finset ((Fin 10 → Bool) → Bool))
    let width := fun (p q : Fin 10) =>
      (((Finset.range (C.size+1)).image (fun j => fun x : Fin 10 → Bool =>
        let y := fun i => if i=p ∨ i=q then false else x i
        (C.wires (List.ofFn y ++ [y 0 || y 1])).getD (10+j) false)) \ A).card
    FanInTwo C → C.size ≤ 18 → (∀ p, 15 ≤ width p p) →
    (∀ e ∈ edges, 13 ≤ width (Fin.ofNat 10 (e/10)) (Fin.ofNat 10 (e % 10))) →
    ¬ (∀ x : Fin 10 → Bool, C.eval (List.ofFn x ++ [x 0 || x 1]) =
      edges.any (fun e => x (Fin.ofNat 10 (e/10)) && x (Fin.ofNat 10 (e % 10)))))
    : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) → ∃ (x4 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x4 ++ [x4 (0 : Fin (10 : ℕ)) || x4 (1 : Fin (10 : ℕ))]) ≠ (fun (x5 : Fin (10 : ℕ) → Bool) => x5 (0 : Fin (10 : ℕ)) && x5 (1 : Fin (10 : ℕ)) || x5 (1 : Fin (10 : ℕ)) && x5 (2 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ)) && x5 (3 : Fin (10 : ℕ)) || x5 (3 : Fin (10 : ℕ)) && x5 (4 : Fin (10 : ℕ)) || x5 (4 : Fin (10 : ℕ)) && x5 (0 : Fin (10 : ℕ)) || x5 (0 : Fin (10 : ℕ)) && x5 (5 : Fin (10 : ℕ)) || x5 (1 : Fin (10 : ℕ)) && x5 (6 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ)) && x5 (7 : Fin (10 : ℕ)) || x5 (3 : Fin (10 : ℕ)) && x5 (8 : Fin (10 : ℕ)) || x5 (4 : Fin (10 : ℕ)) && x5 (9 : Fin (10 : ℕ)) || x5 (5 : Fin (10 : ℕ)) && x5 (7 : Fin (10 : ℕ)) || x5 (7 : Fin (10 : ℕ)) && x5 (9 : Fin (10 : ℕ)) || x5 (9 : Fin (10 : ℕ)) && x5 (6 : Fin (10 : ℕ)) || x5 (6 : Fin (10 : ℕ)) && x5 (8 : Fin (10 : ℕ)) || x5 (8 : Fin (10 : ℕ)) && x5 (5 : Fin (10 : ℕ))) x4 := by
  intro C legal small
  classical
  by_contra noneBad
  let F := (fun x : Fin 10 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5))
  let G := (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))
  let H := (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4))
  let E : List ℕ := [1,12,23,34,40,5,16,27,38,49,57,79,96,68,85]
  have eq (x : Fin 10 → Bool) : C.eval (List.ofFn x ++ [x 0 || x 1]) = F x :=
    Classical.not_not.mp (fun bad => noneBad ⟨x, bad⟩)
  let Q : Circuit := ⟨⟨GateOp.or, [0,1]⟩ :: C.gates, C.output⟩
  have qlaw : FanInTwo Q := by
    intro g hg
    rcases List.mem_cons.mp hg with rfl | h
    · simp
    · exact legal g h
  have wireQ (x : Fin 10 → Bool) : Q.wires (List.ofFn x) = C.wires (List.ofFn x ++ [x 0 || x 1]) := by
    change C.gates.foldl _ _ = C.gates.foldl _ _
    congr 1
    change List.ofFn x ++ [((List.ofFn x).getD 0 false || ((List.ofFn x).getD 1 false || false))] =
      List.ofFn x ++ [x 0 || x 1]
    simp [List.getD_eq_getElem?_getD]
  have qval (x : Fin 10 → Bool) : Q.eval (List.ofFn x) = F x := by
    change (Q.wires _).getD C.output false = _
    rw [wireQ]
    exact eq x
  let base (n : ℕ) := ((Finset.univ.image (fun i : Fin n => fun x : Fin n → Bool => x i)) ∪
    {fun _ => false,fun _ => true} : Finset ((Fin n → Bool) → Bool))
  let pin (p q : Fin 10) (x : Fin 10 → Bool) := fun i => if i=p ∨ i=q then false else x i
  let W (p q : Fin 10) := (((Finset.range Q.size).image (fun j => fun x : Fin 10 → Bool =>
    (Q.wires (List.ofFn (pin p q x))).getD (10+j) false)) \ base 10).card
  have project (n : ℕ) (p q : Fin 10) (r : Fin 10 → Option (Fin n))
      (rp : r p = Option.none) (rq : r q = Option.none)
      (f : (Fin n → Bool) → Bool) (varies : ∃ x y, f x ≠ f y)
      (pattern : ∀ x, F (fun i => (r i).elim false x) = f x) :
      HasCircuitSize n f (W p q) := by
    let lift (x : Fin n → Bool) := fun i => (r i).elim false x
    have fix (x) : pin p q (lift x) = lift x := by
      funext i
      by_cases h : i=p ∨ i=q
      · rcases h with rfl | rfl <;> simp [pin,lift,rp,rq]
      · simp only [pin,if_neg h]
    let a (i : Fin 10) (x : Fin 10 → Bool) := pin p q x i
    have raw (i) : a i ∈ base 10 := by
      by_cases h : i=p ∨ i=q
      · have hfun : a i = fun _ => false := by funext x; simp only [a,pin,if_pos h]
        rw [hfun]
        simp [base]
      · have hfun : a i = fun x => x i := by funext x; simp only [a,pin,if_neg h]
        exact hfun ▸ Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
    have same (x : Fin n → Bool) : Q.eval (List.ofFn (fun i => a i (lift x))) = f x := by
      change Q.eval (List.ofFn (pin p q (lift x))) = _
      rw [fix,qval]
      exact pattern x
    obtain ⟨x,y,dis⟩ := varies
    obtain ⟨D,dl,ds,sem⟩ := compress 10 10 Q a raw ⟨lift x,lift y,by simpa only [same] using dis⟩ qlaw
    let b (i : Fin 10) (z : Fin n → Bool) := lift z i
    have input (i) : b i ∈ base n := by
      cases h : r i with
      | none => simp [b,lift,h,base]
      | some j =>
        have hfun : b i = fun z => z j := by funext z; simp [b,lift,h]
        exact hfun ▸ Finset.mem_union_left _ (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩)
    have dsem (z : Fin n → Bool) : D.eval (List.ofFn (fun i => b i z)) = f z :=
      (sem (lift z)).trans (same z)
    obtain ⟨B,bl,bs,ev⟩ := compress n 10 D b input ⟨x,y,by simpa only [dsem] using dis⟩ dl
    have bound : (((Finset.range D.size).image (fun j => fun z : Fin n → Bool =>
      (D.wires (List.ofFn (fun i => b i z))).getD (10+j) false)) \ base n).card ≤ D.size :=
      (Finset.card_le_card Finset.sdiff_subset).trans (Finset.card_image_le.trans (by simp))
    exact ⟨B,bl,bs.trans (bound.trans ds),fun z => (ev z).trans (dsem z)⟩
  let oneMap : Fin 10 → Fin 10 → Option (Fin 9) :=
    ![![none, some 4, some 0, some 1, some 6, some 7, some 3, some 5, some 2, some 8],
    ![some 4, none, some 6, some 1, some 0, some 3, some 7, some 8, some 2, some 5],
    ![some 0, some 4, none, some 6, some 1, some 5, some 3, some 7, some 8, some 2],
    ![some 0, some 1, some 6, none, some 4, some 5, some 2, some 8, some 7, some 3],
    ![some 4, some 0, some 1, some 6, none, some 3, some 5, some 2, some 8, some 7],
    ![some 4, some 0, some 1, some 2, some 3, none, some 5, some 6, some 7, some 8],
    ![some 0, some 4, some 3, some 2, some 1, some 5, none, some 8, some 7, some 6],
    ![some 0, some 1, some 6, some 8, some 5, some 4, some 2, none, some 3, some 7],
    ![some 0, some 1, some 2, some 7, some 5, some 4, some 6, some 3, none, some 8],
    ![some 0, some 1, some 2, some 3, some 4, some 5, some 6, some 7, some 8, none]]
  let twoMap : Fin 15 → Fin 10 → Option (Fin 8) :=
    ![![none, none, some 0, some 1, some 5, some 6, some 3, some 4, some 2, some 7],
    ![some 0, none, none, some 5, some 1, some 4, some 3, some 6, some 7, some 2],
    ![some 1, some 0, none, none, some 5, some 2, some 4, some 3, some 6, some 7],
    ![some 0, some 1, some 5, none, none, some 4, some 2, some 7, some 6, some 3],
    ![none, some 0, some 1, some 5, none, some 3, some 4, some 2, some 7, some 6],
    ![none, some 0, some 1, some 2, some 3, none, some 4, some 5, some 6, some 7],
    ![some 0, none, some 3, some 2, some 1, some 4, none, some 7, some 6, some 5],
    ![some 1, some 0, none, some 3, some 2, some 5, some 4, none, some 7, some 6],
    ![some 1, some 2, some 3, none, some 0, some 5, some 6, some 7, none, some 4],
    ![some 0, some 1, some 2, some 3, none, some 4, some 5, some 6, some 7, none],
    ![some 0, some 1, some 5, some 7, some 4, none, some 2, none, some 3, some 6],
    ![some 1, some 2, some 3, some 7, some 5, some 0, some 6, none, some 4, none],
    ![some 1, some 0, some 4, some 7, some 5, some 2, none, some 6, some 3, none],
    ![some 1, some 0, some 4, some 6, some 2, some 5, none, some 7, none, some 3],
    ![some 0, some 1, some 2, some 6, some 4, none, some 5, some 3, none, some 7]]
  let es : Fin 15 → ℕ := ![1,12,23,34,40,5,16,27,38,49,57,79,96,68,85]
  have leftGone : ∀ p, oneMap p p = none := by decide +kernel
  have twoGone : ∀ k, twoMap k (Fin.ofNat 10 (es k/10)) = none ∧
      twoMap k (Fin.ofNat 10 (es k % 10)) = none := by decide +kernel
  have shapes1 : ∀ k (x : Fin 9 → Bool), F (fun i => (oneMap k i).elim false x) = G x := by
    intro k; fin_cases k <;> intro x
    · change ((false && x 4) || (x 4 && x 0) || (x 0 && x 1) || (x 1 && x 6) || (x 6 && false) || (false && x 7) || (x 4 && x 3) || (x 0 && x 5) || (x 1 && x 2) || (x 6 && x 8) || (x 7 && x 5) || (x 5 && x 8) || (x 8 && x 3) || (x 3 && x 2) || (x 2 && x 7)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))
      simp only [Bool.false_and,Bool.and_false,Bool.false_or,Bool.or_false]
      ac_rfl
    · change ((x 4 && false) || (false && x 6) || (x 6 && x 1) || (x 1 && x 0) || (x 0 && x 4) || (x 4 && x 3) || (false && x 7) || (x 6 && x 8) || (x 1 && x 2) || (x 0 && x 5) || (x 3 && x 8) || (x 8 && x 5) || (x 5 && x 7) || (x 7 && x 2) || (x 2 && x 3)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))
      simp only [Bool.false_and,Bool.and_false,Bool.false_or,Bool.or_false]
      ac_rfl
    · change ((x 0 && x 4) || (x 4 && false) || (false && x 6) || (x 6 && x 1) || (x 1 && x 0) || (x 0 && x 5) || (x 4 && x 3) || (false && x 7) || (x 6 && x 8) || (x 1 && x 2) || (x 5 && x 7) || (x 7 && x 2) || (x 2 && x 3) || (x 3 && x 8) || (x 8 && x 5)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))
      simp only [Bool.false_and,Bool.and_false,Bool.or_false]
      ac_rfl
    · change ((x 0 && x 1) || (x 1 && x 6) || (x 6 && false) || (false && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 2) || (x 6 && x 8) || (false && x 7) || (x 4 && x 3) || (x 5 && x 8) || (x 8 && x 3) || (x 3 && x 2) || (x 2 && x 7) || (x 7 && x 5)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))
      simp only [Bool.false_and,Bool.and_false,Bool.or_false]
      ac_rfl
    · change ((x 4 && x 0) || (x 0 && x 1) || (x 1 && x 6) || (x 6 && false) || (false && x 4) || (x 4 && x 3) || (x 0 && x 5) || (x 1 && x 2) || (x 6 && x 8) || (false && x 7) || (x 3 && x 2) || (x 2 && x 7) || (x 7 && x 5) || (x 5 && x 8) || (x 8 && x 3)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))
      simp only [Bool.false_and,Bool.and_false,Bool.or_false]
      ac_rfl
    · change ((x 4 && x 0) || (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && false) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (false && x 6) || (x 6 && x 8) || (x 8 && x 5) || (x 5 && x 7) || (x 7 && false)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))
      simp only [Bool.false_and,Bool.and_false,Bool.or_false]
      ac_rfl
    · change ((x 0 && x 4) || (x 4 && x 3) || (x 3 && x 2) || (x 2 && x 1) || (x 1 && x 0) || (x 0 && x 5) || (x 4 && false) || (x 3 && x 8) || (x 2 && x 7) || (x 1 && x 6) || (x 5 && x 8) || (x 8 && x 6) || (x 6 && false) || (false && x 7) || (x 7 && x 5)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))
      simp only [Bool.false_and,Bool.and_false,Bool.or_false]
      ac_rfl
    · change ((x 0 && x 1) || (x 1 && x 6) || (x 6 && x 8) || (x 8 && x 5) || (x 5 && x 0) || (x 0 && x 4) || (x 1 && x 2) || (x 6 && false) || (x 8 && x 3) || (x 5 && x 7) || (x 4 && false) || (false && x 7) || (x 7 && x 2) || (x 2 && x 3) || (x 3 && x 4)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))
      simp only [Bool.false_and,Bool.and_false,Bool.or_false]
      ac_rfl
    · change ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 7) || (x 7 && x 5) || (x 5 && x 0) || (x 0 && x 4) || (x 1 && x 6) || (x 2 && x 3) || (x 7 && false) || (x 5 && x 8) || (x 4 && x 3) || (x 3 && x 8) || (x 8 && x 6) || (x 6 && false) || (false && x 4)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))
      simp only [Bool.false_and,Bool.and_false,Bool.or_false]
      ac_rfl
    · change ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && false) || (x 5 && x 7) || (x 7 && false) || (false && x 6) || (x 6 && x 8) || (x 8 && x 5)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))
      simp only [Bool.false_and,Bool.and_false,Bool.or_false]
  have shapes2 : ∀ k (x : Fin 8 → Bool), F (fun i => (twoMap k i).elim false x) = H x := by
    intro k; fin_cases k <;> intro x
    · change ((false && false) || (false && x 0) || (x 0 && x 1) || (x 1 && x 5) || (x 5 && false) || (false && x 6) || (false && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 5 && x 7) || (x 6 && x 4) || (x 4 && x 7) || (x 7 && x 3) || (x 3 && x 2) || (x 2 && x 6)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4))
      simp only [Bool.false_and,Bool.and_false,Bool.false_or,Bool.or_false]
      ac_rfl
    · change ((x 0 && false) || (false && false) || (false && x 5) || (x 5 && x 1) || (x 1 && x 0) || (x 0 && x 4) || (false && x 3) || (false && x 6) || (x 5 && x 7) || (x 1 && x 2) || (x 4 && x 6) || (x 6 && x 2) || (x 2 && x 3) || (x 3 && x 7) || (x 7 && x 4)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4))
      simp only [Bool.false_and,Bool.and_false,Bool.false_or,Bool.or_false]
      ac_rfl
    · change ((x 1 && x 0) || (x 0 && false) || (false && false) || (false && x 5) || (x 5 && x 1) || (x 1 && x 2) || (x 0 && x 4) || (false && x 3) || (false && x 6) || (x 5 && x 7) || (x 2 && x 3) || (x 3 && x 7) || (x 7 && x 4) || (x 4 && x 6) || (x 6 && x 2)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4))
      simp only [Bool.false_and,Bool.and_false,Bool.or_false]
      ac_rfl
    · change ((x 0 && x 1) || (x 1 && x 5) || (x 5 && false) || (false && false) || (false && x 0) || (x 0 && x 4) || (x 1 && x 2) || (x 5 && x 7) || (false && x 6) || (false && x 3) || (x 4 && x 7) || (x 7 && x 3) || (x 3 && x 2) || (x 2 && x 6) || (x 6 && x 4)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4))
      simp only [Bool.false_and,Bool.and_false,Bool.or_false]
      ac_rfl
    · change ((false && x 0) || (x 0 && x 1) || (x 1 && x 5) || (x 5 && false) || (false && false) || (false && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 5 && x 7) || (false && x 6) || (x 3 && x 2) || (x 2 && x 6) || (x 6 && x 4) || (x 4 && x 7) || (x 7 && x 3)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4))
      simp only [Bool.false_and,Bool.and_false,Bool.false_or,Bool.or_false]
      ac_rfl
    · change ((false && x 0) || (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && false) || (false && false) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (false && x 5) || (x 5 && x 7) || (x 7 && x 4) || (x 4 && x 6) || (x 6 && false)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4))
      simp only [Bool.false_and,Bool.and_false,Bool.false_or,Bool.or_false]
      ac_rfl
    · change ((x 0 && false) || (false && x 3) || (x 3 && x 2) || (x 2 && x 1) || (x 1 && x 0) || (x 0 && x 4) || (false && false) || (x 3 && x 7) || (x 2 && x 6) || (x 1 && x 5) || (x 4 && x 7) || (x 7 && x 5) || (x 5 && false) || (false && x 6) || (x 6 && x 4)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4))
      simp only [Bool.false_and,Bool.and_false,Bool.false_or,Bool.or_false]
      ac_rfl
    · change ((x 1 && x 0) || (x 0 && false) || (false && x 3) || (x 3 && x 2) || (x 2 && x 1) || (x 1 && x 5) || (x 0 && x 4) || (false && false) || (x 3 && x 7) || (x 2 && x 6) || (x 5 && false) || (false && x 6) || (x 6 && x 4) || (x 4 && x 7) || (x 7 && x 5)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4))
      simp only [Bool.false_and,Bool.and_false,Bool.or_false]
      ac_rfl
    · change ((x 1 && x 2) || (x 2 && x 3) || (x 3 && false) || (false && x 0) || (x 0 && x 1) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (false && false) || (x 0 && x 4) || (x 5 && x 7) || (x 7 && x 4) || (x 4 && x 6) || (x 6 && false) || (false && x 5)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4))
      simp only [Bool.false_and,Bool.and_false,Bool.or_false]
      ac_rfl
    · change ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && false) || (false && x 0) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (false && false) || (x 4 && x 6) || (x 6 && false) || (false && x 5) || (x 5 && x 7) || (x 7 && x 4)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4))
      simp only [Bool.false_and,Bool.and_false,Bool.or_false]
    · change ((x 0 && x 1) || (x 1 && x 5) || (x 5 && x 7) || (x 7 && x 4) || (x 4 && x 0) || (x 0 && false) || (x 1 && x 2) || (x 5 && false) || (x 7 && x 3) || (x 4 && x 6) || (false && false) || (false && x 6) || (x 6 && x 2) || (x 2 && x 3) || (x 3 && false)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4))
      simp only [Bool.false_and,Bool.and_false,Bool.or_false]
      ac_rfl
    · change ((x 1 && x 2) || (x 2 && x 3) || (x 3 && x 7) || (x 7 && x 5) || (x 5 && x 1) || (x 1 && x 0) || (x 2 && x 6) || (x 3 && false) || (x 7 && x 4) || (x 5 && false) || (x 0 && false) || (false && false) || (false && x 6) || (x 6 && x 4) || (x 4 && x 0)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4))
      simp only [Bool.false_and,Bool.and_false,Bool.or_false]
      ac_rfl
    · change ((x 1 && x 0) || (x 0 && x 4) || (x 4 && x 7) || (x 7 && x 5) || (x 5 && x 1) || (x 1 && x 2) || (x 0 && false) || (x 4 && x 6) || (x 7 && x 3) || (x 5 && false) || (x 2 && x 6) || (x 6 && false) || (false && false) || (false && x 3) || (x 3 && x 2)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4))
      simp only [Bool.false_and,Bool.and_false,Bool.or_false]
      ac_rfl
    · change ((x 1 && x 0) || (x 0 && x 4) || (x 4 && x 6) || (x 6 && x 2) || (x 2 && x 1) || (x 1 && x 5) || (x 0 && false) || (x 4 && x 7) || (x 6 && false) || (x 2 && x 3) || (x 5 && x 7) || (x 7 && x 3) || (x 3 && false) || (false && false) || (false && x 5)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4))
      simp only [Bool.false_and,Bool.and_false,Bool.or_false]
      ac_rfl
    · change ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 6) || (x 6 && x 4) || (x 4 && x 0) || (x 0 && false) || (x 1 && x 5) || (x 2 && x 3) || (x 6 && false) || (x 4 && x 7) || (false && x 3) || (x 3 && x 7) || (x 7 && x 5) || (x 5 && false) || (false && false)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4))
      simp only [Bool.false_and,Bool.and_false,Bool.or_false]
      ac_rfl
  have distinctG : G (fun _ => false) ≠ G (fun _ => true) := by decide +kernel
  have distinctH : H (fun _ => false) ≠ H (fun _ => true) := by decide +kernel
  let width (p q : Fin 10) := (((Finset.range (C.size+1)).image (fun j => fun x : Fin 10 → Bool =>
    (C.wires (List.ofFn (pin p q x) ++ [pin p q x 0 || pin p q x 1])).getD (10+j) false)) \ base 10).card
  have fullWidth (p q) : W p q = width p q := by
    have qs : Q.size=C.size+1 := rfl
    simp only [W,width,qs,wireQ]
  apply remaining C legal small
  · intro p
    change 15 ≤ width p p
    rw [← fullWidth]
    obtain ⟨D,dl,ds,ev⟩ := project 9 p p (oneMap p) (leftGone p) (leftGone p) G
      ⟨(fun _ => false),(fun _ => true),distinctG⟩ (shapes1 p)
    by_contra! h
    exact single ⟨D,dl,by omega,ev⟩
  · intro e he
    have listed : ∃ k : Fin 15, es k=e := by
      have all : ∀ a ∈ E, ∃ k : Fin 15, es k=a := by decide +kernel
      exact all e he
    obtain ⟨k,rfl⟩ := listed
    let p := Fin.ofNat 10 (es k/10)
    let q := Fin.ofNat 10 (es k % 10)
    change 13 ≤ width p q
    rw [← fullWidth]
    obtain ⟨D,dl,ds,ev⟩ := project 8 p q (twoMap k) (twoGone k).1 (twoGone k).2 H
      ⟨(fun _ => false),(fun _ => true),distinctH⟩ (shapes2 k)
    by_contra! h
    exact pair ⟨D,dl,by omega,ev⟩
  · intro x
    apply (eq x).trans
    change ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)) = ((x 0 && x 1) || ((x 1 && x 2) || ((x 2 && x 3) || ((x 3 && x 4) || ((x 4 && x 0) || ((x 0 && x 5) || ((x 1 && x 6) || ((x 2 && x 7) || ((x 3 && x 8) || ((x 4 && x 9) || ((x 5 && x 7) || ((x 7 && x 9) || ((x 9 && x 6) || ((x 6 && x 8) || ((x 8 && x 5) || false)))))))))))))))
    simp only [Bool.or_false]
    ac_rfl
