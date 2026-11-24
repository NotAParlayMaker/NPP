import Mathlib.Data.List.GetD
import Mathlib.Data.List.Basic
import PEqualNP.Defs

open PEqualNP.MetaComplexity

set_option maxHeartbeats 1200000 in
theorem PEqualNP.Outside.R_meta_2828_417
    (conjunction : ∀ (C : BinaryCircuit) (i j : ℕ) (a d : Bool),
      (∀ g ∈ C.gates, ∃ c e : Bool, g.op = fun u v => u == c && v == e) →
      C.size ≤ 12 → 11 ≤ i → i < j → j + 1 = 11 + C.size →
      (∀ x : Fin 9 → Bool,
        ((C.wires (List.ofFn x ++ [x 0 || x 1, false])).getD i false == a && (C.wires (List.ofFn x ++ [x 0 || x 1, false])).getD j false == d) =
          (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) → False)
    (disjunction : ∀ (C : BinaryCircuit) (i j : ℕ) (a d : Bool),
      (∀ g ∈ C.gates, ∃ c e : Bool, g.op = fun u v => u == c && v == e) →
      C.size ≤ 12 → 11 ≤ i → i < j → j + 1 = 11 + C.size →
      (∀ x : Fin 9 → Bool,
        ((C.wires (List.ofFn x ++ [x 0 || x 1, false])).getD i false != a || (C.wires (List.ofFn x ++ [x 0 || x 1, false])).getD j false != d) =
          (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) → False) :
    ∀ (x1 : PEqualNP.MetaComplexity.BinaryCircuit) (x2 : Bool), (∀ x3 ∈ x1.gates, ∃ (x5 : Bool) (x6 : Bool), x3.op = fun (x7 x8 : Bool) => x7 == x5 && x8 == x6) → (∀ (x4 : Fin (9 : ℕ) → Bool), (x1.eval (List.ofFn x4 ++ [x4 (0 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)), Bool.false]) != x2) = (x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)))) → (14 : ℕ) ≤ x1.size := by
  classical
  let base (x : Fin 9 → Bool) := List.ofFn x ++ [x 0 || x 1, false]
  let f (x : Fin 9 → Bool) := x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5
  let bad (k : ℕ) := ∃ (C : BinaryCircuit) (b : Bool), C.size = k ∧
    (∀ g ∈ C.gates, ∃ a d : Bool, g.op = fun u v => u == a && v == d) ∧
    ∀ x, (C.eval (base x) != b) = f x
  intro C b signed computes
  by_contra! short
  have existsBad : ∃ k, bad k := ⟨C.size, C, b, rfl, signed, computes⟩
  -- A minimum counterexample lets us discard unused gates and contract redundant output operands.
  obtain ⟨D, p, hsize, ops, sem⟩ := Nat.find_spec existsBad
  have bound : D.size ≤ 13 := by
    have h := Nat.find_min' existsBad (show bad C.size from ⟨C,b,rfl,signed,computes⟩)
    omega
  have minimal (B : BinaryCircuit) (q : Bool) (small : B.size < D.size)
      (hs : ∀ g ∈ B.gates, ∃ a d : Bool, g.op = fun u v => u == a && v == d)
      (hf : ∀ x, (B.eval (base x) != q) = f x) : False := by
    have h := Nat.find_min' existsBad (show bad B.size from ⟨B,q,rfl,hs,hf⟩)
    omega
  let step (W : List Bool) (g : BinaryGate) := W ++ [g.op (W.getD g.left false) (W.getD g.right false)]
  have baseLen (x : Fin 9 → Bool) : (base x).length = 11 := by simp [base]
  have length (gs : List BinaryGate) (W : List Bool) : (gs.foldl step W).length = W.length + gs.length := by
    induction gs generalizing W with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp [step, Nat.add_left_comm, Nat.add_comm]
  have retain (gs : List BinaryGate) (W : List Bool) (i : ℕ) (hi : i < W.length) :
      (gs.foldl step W).getD i false = W.getD i false := by
    induction gs generalizing W with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih _ (by simp [step]; omega)]
      exact List.getD_append _ _ _ _ hi
  -- Each primary wire takes both values on each fibre of the graph function.
  let witness (y : Bool) (i : Fin 10) (a : Bool) (v : Fin 9) :=
    ((if y then [3, 6, 3, 12, 6, 3, 11, 3, 17, 3, 33, 3, 66, 3, 131, 3, 259, 3, 3, 12] else [1, 0, 2, 0, 4, 0, 8, 0, 16, 0, 32, 0, 64, 0, 128, 0, 256, 0, 1, 0] : List ℕ).getD (2 * i.val + a.toNat) 0).testBit v.val
  have contrast : ∀ (y : Bool) (i : Fin 10) (a : Bool),
      f (witness y i a) = y ∧ (base (witness y i a)).getD i.val false ≠ a := by decide +kernel
  have zero : f (fun _ => false) = false := rfl
  have unit : f (fun _ => true) = true := rfl
  have nonconstant (q : Bool) : ¬ ∀ x, q = f x := by
    intro h
    have l := h (fun _ => false)
    have r := h (fun _ => true)
    rw [zero] at l
    rw [unit] at r
    cases q <;> contradiction
  have hbaseZero (x : Fin 9 → Bool) : (base x).getD 10 false = false := by
    change ((List.ofFn x) ++ [x 0 || x 1, false]).getD 10 false = false
    rw [List.getD_append_right _ _ _ _ (by simp), List.length_ofFn]
    rfl
  have forces : ∀ u v a d q : Bool, (((u == a && v == d) != q) = !q) → u = a ∧ v = d := by decide
  have differs : ∀ u q : Bool, (u != q) = true → u = !q := by decide
  have contract : ∀ v d q : Bool, ((v == d) != q) = (v != (d == q)) := by decide
  have deMorgan : ∀ u v a d : Bool, ((u == a && v == d) != true) = (u != a || v != d) := by decide
  have empty (hd : D.gates = []) : False := by
    by_cases h : D.output < 10
    · let i : Fin 10 := ⟨D.output, h⟩
      have v := contrast true i (!p)
      have eq := sem (witness true i (!p))
      change ((D.gates.foldl step (base (witness true i (!p)))).getD D.output false != p) = _ at eq
      rw [hd, List.foldl_nil, v.1] at eq
      exact v.2 (differs _ _ eq)
    · apply nonconstant p
      intro x
      have eq := sem x
      change ((D.gates.foldl step (base x)).getD D.output false != p) = _ at eq
      rw [hd, List.foldl_nil] at eq
      by_cases he : D.output = 10
      · rw [he, hbaseZero] at eq
        cases p <;> simpa using eq
      · have ge : (base x).length ≤ D.output := by rw [baseLen]; omega
        rw [List.getD_eq_default _ _ ge] at eq
        cases p <;> simpa using eq
  rcases D.gates.eq_nil_or_concat' with hgs | ⟨gs, g, hgs⟩
  · exact empty hgs
  · let P : BinaryCircuit := ⟨gs, 0⟩
    let W (x : Fin 9 → Bool) := gs.foldl step (base x)
    have wLen (x : Fin 9 → Bool) : (W x).length = 11 + gs.length := (length gs (base x)).trans (by rw [baseLen])
    have hDs : D.size = gs.length + 1 := by change D.gates.length = _; simp [hgs]
    have smaller (o : ℕ) : (BinaryCircuit.mk gs o).size < D.size := by change gs.length < D.size; omega
    have good (o : ℕ) : ∀ q ∈ (BinaryCircuit.mk gs o).gates,
        ∃ a d : Bool, q.op = fun u v => u == a && v == d := by
      intro q hq
      apply ops q
      rw [hgs]
      exact List.mem_append_left _ hq
    have unfolded (x : Fin 9 → Bool) :
        (((step (W x) g).getD D.output false) != p) = f x := by
      have eq := sem x
      change ((D.gates.foldl step (base x)).getD D.output false != p) = _ at eq
      rw [hgs, List.foldl_append, List.foldl_cons, List.foldl_nil] at eq
      exact eq
    have out : D.output = 11 + gs.length := by
      by_contra neq
      by_cases h : D.output < 11 + gs.length
      · apply minimal ⟨gs, D.output⟩ p (smaller _) (good _)
        intro x
        have eq := unfolded x
        change (((W x ++ [_]).getD D.output false) != p) = _ at eq
        rw [List.getD_append _ _ _ _ (by rwa [wLen])] at eq
        exact eq
      · apply nonconstant p
        intro x
        have eq := unfolded x
        have ge : (step (W x) g).length ≤ D.output := by simp [step, wLen]; omega
        rw [List.getD_eq_default _ _ ge] at eq
        cases p <;> simpa using eq
    obtain ⟨a,d,oper⟩ := ops g (by rw [hgs]; exact List.mem_append_right _ (by simp))
    have combine (x : Fin 9 → Bool) :
        ((((W x).getD g.left false == a) && ((W x).getD g.right false == d)) != p) = f x := by
      have eq := unfolded x
      rw [out, ← wLen x] at eq
      change (((W x ++ [_]).getD (W x).length false) != p) = _ at eq
      rw [List.getD_append_right _ _ _ _ (Nat.le_refl _), Nat.sub_self, oper] at eq
      exact eq
    have both (x : Fin 9 → Bool) (hx : f x = !p) :
        (W x).getD g.left false = a ∧ (W x).getD g.right false = d :=
      forces _ _ _ _ _ ((combine x).trans hx)
    have rawExclusion (i : ℕ) (s : Bool) (h : ∀ x, f x = !p → (W x).getD i false = s) : 10 ≤ i := by
      by_contra! hlt
      let j : Fin 10 := ⟨i, hlt⟩
      have hobs := contrast (!p) j s
      have eq := h _ hobs.1
      rw [retain gs (base _) i (by rw [baseLen]; omega)] at eq
      exact hobs.2 eq
    have alwaysFalse (i : ℕ) (lo : 10 ≤ i) (hi : ¬ (11 ≤ i ∧ i < 11 + gs.length)) :
        ∀ x, (W x).getD i false = false := by
      intro x
      by_cases atZero : i = 10
      · subst i
        change (gs.foldl step (base x)).getD 10 false = false
        rw [retain gs (base x) 10 (by rw [baseLen]; omega), hbaseZero]
      · have ge : (W x).length ≤ i := by rw [wLen]; omega
        exact List.getD_eq_default _ _ ge
    have collapse (i : ℕ) (s : Bool) (hf : ∀ x, (((W x).getD i false == s) != p) = f x) : False := by
      apply minimal ⟨gs,i⟩ (s == p) (smaller _) (good _)
      intro x
      exact (contract _ _ _).symm.trans (hf x)
    have falseEq : (false == false) = true := rfl
    have hl : 11 ≤ g.left ∧ g.left < 11 + gs.length := by
      by_contra h
      have eq := alwaysFalse g.left (rawExclusion _ _ fun x hx => (both x hx).1) h
      have a0 : a = false := by
        have hv := contrast (!p) (0 : Fin 10) false
        exact ((both _ hv.1).1.symm).trans (eq _)
      apply collapse g.right d
      intro x
      simpa only [eq x, a0, falseEq, Bool.true_and] using combine x
    have hr : 11 ≤ g.right ∧ g.right < 11 + gs.length := by
      by_contra h
      have eq := alwaysFalse g.right (rawExclusion _ _ fun x hx => (both x hx).2) h
      have d0 : d = false := by
        have hv := contrast (!p) (0 : Fin 10) false
        exact ((both _ hv.1).2.symm).trans (eq _)
      apply collapse g.left a
      intro x
      simpa only [eq x, d0, falseEq, Bool.and_true] using combine x
    have distinct : g.left ≠ g.right := by
      intro eq
      have same : a = d := by
        have hv := contrast (!p) (0 : Fin 10) false
        have l := (both _ hv.1).1
        rw [eq] at l
        exact l.symm.trans (both _ hv.1).2
      apply collapse g.left a
      intro x
      simpa [← eq, ← same] using combine x
    have usesLast : g.left + 1 = 11 + gs.length ∨ g.right + 1 = 11 + gs.length := by
      by_contra! skip
      have nonempty : gs ≠ [] := by
        intro h
        simp only [h, List.length_nil, Nat.add_zero] at hl
        omega
      let ts := gs.dropLast
      let t := gs.getLast nonempty
      have pre : ts ++ [t] = gs := List.dropLast_append_getLast nonempty
      have preLen : gs.length = ts.length + 1 := by
        rw [← pre, List.length_append, List.length_singleton]
      let B : BinaryCircuit := ⟨ts ++ [g], 11 + ts.length⟩
      have shortB : B.size < D.size := by
        change (ts ++ [g]).length < D.size
        simp only [List.length_append, List.length_singleton]
        omega
      have goodB : ∀ q ∈ B.gates, ∃ c e : Bool, q.op = fun u v => u == c && v == e := by
        intro q hq
        apply ops q
        rw [hgs, ← pre, List.mem_append, List.mem_append]
        rcases List.mem_append.mp hq with ht | hg
        · exact Or.inl (Or.inl ht)
        · exact Or.inr hg
      apply minimal B p shortB goodB
      intro x
      let U := ts.foldl step (base x)
      have uLen : U.length = 11 + ts.length := (length ts (base x)).trans (by rw [baseLen])
      have fromPrefix (i : ℕ) (hi : i < 11 + ts.length) : (W x).getD i false = U.getD i false := by
        change (gs.foldl step (base x)).getD i false = U.getD i false
        rw [← pre, List.foldl_append]
        exact retain [t] U i (by rwa [uLen])
      change (((ts ++ [g]).foldl step (base x)).getD (11 + ts.length) false != p) = f x
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      change (((U ++ [_]).getD (11 + ts.length) false) != p) = f x
      rw [← uLen, List.getD_append_right _ _ _ _ (Nat.le_refl _), Nat.sub_self]
      change (g.op (U.getD g.left false) (U.getD g.right false) != p) = f x
      rw [← fromPrefix g.left (by omega), ← fromPrefix g.right (by omega), oper]
      exact combine x
    have pSize : P.size ≤ 12 := by change gs.length ≤ 12; omega
    have reject (i j : ℕ) (ai dj : Bool) (low : 11 ≤ i) (order : i < j)
        (last : j + 1 = 11 + P.size)
        (eval : ∀ x, ((((W x).getD i false == ai) && ((W x).getD j false == dj)) != p) = f x) : False := by
      cases p
      · exact conjunction P i j ai dj (good _) pSize low order last
          (fun x => by
            change (((W x).getD i false == ai) && ((W x).getD j false == dj)) = f x
            exact (Bool.bne_false _).symm.trans (eval x))
      · exact disjunction P i j ai dj (good _) pSize low order last
          (fun x => (deMorgan _ _ _ _).symm.trans (eval x))
    rcases usesLast with left | right
    · apply reject g.right g.left d a hr.1 (by omega : g.right < g.left) left
      intro x
      simpa only [Bool.and_comm] using combine x
    · exact reject g.left g.right a d hl.1 (by omega : g.left < g.right) right combine
