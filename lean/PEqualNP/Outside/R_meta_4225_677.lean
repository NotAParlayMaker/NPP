import Mathlib.Data.Finset.Card
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_4225_677
    (erase : ∀ (n : ℕ) (v : Fin n) (a : ℕ) (C : Circuit) (pre post : List Gate) (g : Gate),
      C.gates = pre ++ g :: post → g.op = GateOp.or →
      (g.inputs = [v.val,a] ∨ g.inputs = [a,v.val]) → a < n + pre.length →
      (∀ h ∈ pre ++ post, v.val ∉ h.inputs) → C.output ≠ v.val → FanInTwo C →
      ∃ D : Circuit, FanInTwo D ∧ D.size + 1 = C.size ∧
        D.gates.take pre.length = pre ∧
        ((∃ h ∈ C.gates, h.op = GateOp.not) → ∃ h ∈ D.gates, h.op = GateOp.not) ∧
        (∀ w < n, w ≠ v.val → w ≠ a →
          (D.gates.filter (fun h => h.inputs.contains w)).map Gate.op =
            (C.gates.filter (fun h => h.inputs.contains w)).map Gate.op) ∧
        ∀ x : Fin n → Bool,
          let t := (D.wires (List.ofFn x)).getD a false
          D.eval (List.ofFn (Function.update x v (x v || t))) = C.eval (List.ofFn x))
    (remaining : ∀ (D : Circuit) (a k : ℕ), FanInTwo D → D.size ≤ 14 → 9 ≤ a → a < 9+k → k ≤ D.size →
      (∃ g ∈ D.gates, g.op = GateOp.not) →
      (∀ g ∈ D.gates.take k, 4 ∉ g.inputs) →
      (∀ w ∈ ([6,7] : List ℕ), (D.gates.filter (fun g => g.inputs.contains w)).map Gate.op = [GateOp.or]) →
      let f := fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
        (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
      ∃ x : Fin 9 → Bool,
        let t := (D.wires (List.ofFn x)).getD a false
        D.eval (List.ofFn (Function.update x 4 (x 4 || t))) ≠ f x) :

∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalCircuit (9 : ℕ) x1 → x1.size ≤ (15 : ℕ) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x5 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x4 x5.1 && x4 x5.2) → (∀ (x5 : Fin x1.size), (∀ x6 ∈ (x1.gates.get x5).inputs, x6 < (9 : ℕ) + ↑x5) ∧ (x1.gates.get x5).inputs.Nodup ∧ ((x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (x1.gates.get x5).inputs.length = (1 : ℕ) ∨ (x1.gates.get x5).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ (x1.gates.get x5).inputs.length = (2 : ℕ))) → (∀ x6 ∈ [(4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))], ∃ (x8 : Fin x1.size), (∀ (x9 : Fin x1.size), ↑x6 ∈ (x1.gates.get x9).inputs ↔ x9 = x8) ∧ (x1.gates.get x8).op = PEqualNP.CircuitLowerBounds.GateOp.or) → (∀ (x7 : Fin x1.size), ∀ x8 ∈ (x1.gates.get x7).inputs, ∀ x10 ∈ (x1.gates.get x7).inputs, x8 ∈ [(4 : ℕ), (6 : ℕ), (7 : ℕ)] → x10 ∈ [(4 : ℕ), (6 : ℕ), (7 : ℕ)] → x8 = x10) → (∃ (x8 : Fin x1.size), (x1.gates.get x8).op = PEqualNP.CircuitLowerBounds.GateOp.not) → False := by
  intro C minC budget hfun norm readers _ hn
  let f := fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
    (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
  have formula (x : Fin 9 → Bool) : C.eval (List.ofFn x) = f x := by
    change circuitFun 9 C x = f x
    rw [hfun] <;>
      (simp only [f, List.any_cons, List.any_nil, Bool.or_false] <;> rfl)
  let step (u : List Bool) (g : Gate) := u ++ [g.op.eval (g.inputs.map fun j => u.getD j false)]
  have stable (gs : List Gate) (u : List Bool) (i : ℕ) (hi : i < u.length) :
      (gs.foldl step u).getD i false = u.getD i false := by
    induction gs generalizing u with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih _ (by simp [step]; omega)]
      exact List.getD_append _ _ _ _ hi
  have raw (A : Circuit) (x : Fin 9 → Bool) (i : Fin 9) :
      (A.wires (List.ofFn x)).getD i.val false = x i := by
    change (A.gates.foldl step (List.ofFn x)).getD i.val false = x i
    have h : i.val < (List.ofFn x).length := by simpa only [List.length_ofFn] using i.isLt
    rw [stable _ _ _ h, List.getD_eq_getElem _ _ h, List.getElem_ofFn]
  have out : C.output ≠ 4 := by
    intro eq
    let x : Fin 9 → Bool := fun i => decide (i = 4)
    have h : C.eval (List.ofFn x) = x 4 := by
      change (C.wires (List.ofFn x)).getD C.output false = x 4
      rw [eq]
      exact raw C x 4
    rw [formula] at h
    exact (by decide : f x ≠ x 4) h
  have split_at (i : Fin C.size) :
      C.gates = C.gates.take i.val ++ C.gates.get i :: C.gates.drop (i.val+1) := by
    have hi : i.val < C.gates.length := i.isLt
    change C.gates = C.gates.take i.val ++ C.gates[i.val]'hi :: C.gates.drop (i.val+1)
    rw [← List.drop_eq_getElem_cons hi, List.take_append_drop]
  have misses (v : Fin 9) (i : Fin C.size)
      (unique : ∀ j : Fin C.size, v.val ∈ (C.gates.get j).inputs ↔ j = i) :
      ∀ q ∈ C.gates.take i.val ++ C.gates.drop (i.val+1), v.val ∉ q.inputs := by
    intro q hq hv
    rcases List.mem_append.1 hq with hp | hs
    · obtain ⟨j,hj,eq⟩ := List.mem_iff_getElem.1 hp
      have hj' : j < i.val := by rw [List.length_take] at hj; omega
      rw [List.getElem_take] at eq
      have h := (unique ⟨j,by have := i.isLt; omega⟩).1 (eq.symm ▸ hv)
      have := congrArg Fin.val h
      simp only at this
      omega
    · obtain ⟨j,hj,eq⟩ := List.mem_iff_getElem.1 hs
      rw [List.length_drop] at hj
      rw [List.getElem_drop] at eq
      have hl : i.val + 1 + j < C.gates.length := by omega
      have read : v.val ∈ (C.gates.get ⟨i.val+1+j,hl⟩).inputs := by
        change v.val ∈ (C.gates[i.val+1+j]'hl).inputs
        rw [eq]
        exact hv
      have h := (unique ⟨i.val+1+j,hl⟩).1 read
      have := congrArg Fin.val h
      simp only at this
      omega
  have filtered_nil (v : ℕ) (gs : List Gate) (h : ∀ g ∈ gs, v ∉ g.inputs) :
      gs.filter (fun g => g.inputs.contains v) = [] := by
    induction gs with
    | nil => rfl
    | cons q gs ih =>
      have neg : q.inputs.contains v = false :=
        Bool.eq_false_iff.mpr (fun p => h q (by simp) (List.contains_iff_mem.1 p))
      have hs := ih (fun r hr => h r (by simp [hr]))
      simp only [List.filter_cons, neg, Bool.false_eq_true, ite_false, hs]
  have one (v : Fin 9) (hv : v ∈ ([4,6,7] : List (Fin 9))) :
      (C.gates.filter (fun q => q.inputs.contains v.val)).map Gate.op = [GateOp.or] := by
    obtain ⟨i, unique, hop⟩ := readers v hv
    have hdel := misses v i unique
    have p := filtered_nil v.val (C.gates.take i.val) (fun q h => hdel q (List.mem_append_left _ h))
    have s := filtered_nil v.val (C.gates.drop (i.val+1)) (fun q h => hdel q (List.mem_append_right _ h))
    have hit := List.contains_iff_mem.2 ((unique i).2 rfl)
    conv_lhs => rw [split_at i]
    simp only [List.filter_append, List.filter_cons, p, s, hit, ite_true, List.nil_append,
      List.map_cons, List.map_nil, hop]
  obtain ⟨r, only4, hor⟩ := readers 4 (by simp)
  let pre := C.gates.take r.val
  let post := C.gates.drop (r.val+1)
  let g := C.gates.get r
  have hp : pre.length = r.val := by
    change (C.gates.take r.val).length = r.val
    rw [List.length_take, Nat.min_eq_left (show r.val ≤ C.gates.length from r.isLt.le)]
  have member : 4 ∈ g.inputs := (only4 r).2 rfl
  have len : g.inputs.length = 2 := by
    rcases (norm r).2.2 with hn | hn
    · rw [hor] at hn
      cases hn.1
    · exact hn.2
  have two (ls : List ℕ) (h : ls.length = 2) (hv : 4 ∈ ls) :
      ∃ a, ls = [4,a] ∨ ls = [a,4] := by
    rcases ls with _ | ⟨i, _ | ⟨j, _ | ⟨l, rest⟩⟩⟩
    · simp at h
    · simp at h
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
      rcases hv with rfl | rfl
      · exact ⟨j,Or.inl rfl⟩
      · exact ⟨i,Or.inr rfl⟩
    · simp at h
  obtain ⟨a, args⟩ := two g.inputs len member
  have harg : a ∈ g.inputs := by rcases args with h | h <;> simp [h]
  have a4 : a ≠ 4 := by
    intro eq
    subst a
    have nd := (norm r).2.1
    change g.inputs.Nodup at nd
    rcases args with h | h <;> simp [h] at nd
  have aBound : a < 9 + pre.length := by rw [hp]; exact (norm r).1 a harg
  have absent := misses 4 r only4
  obtain ⟨D, fanD, sz, prefixD, notD, keep, eval⟩ := erase 9 4 a C pre post g
    (split_at r) hor args aBound absent out minC.1
  have hnot : ∃ q ∈ D.gates, q.op = GateOp.not := by
    apply notD
    obtain ⟨j,hj⟩ := hn
    exact ⟨C.gates.get j, List.get_mem _ _, hj⟩
  have computes (x : Fin 9 → Bool) :
      D.eval (List.ofFn (Function.update x 4
        (x 4 || (D.wires (List.ofFn x)).getD a false))) = f x :=
    (eval x).trans (formula x)
  have internal : 9 ≤ a := by
    by_contra h
    have ha : a < 9 := by omega
    let w : Fin 9 := ⟨a,ha⟩
    have crit : ∀ w : Fin 9, w ≠ 4 → ∃ u : Fin 9, u ≠ 4 ∧
        f (fun i => decide (i = w ∨ i = u)) = false ∧
        f (fun i => decide (i = 4 ∨ i = w ∨ i = u)) = true := by decide +kernel
    have w4 : w ≠ 4 := fun e => a4 (congrArg Fin.val e)
    obtain ⟨u,u4,h0,h1⟩ := crit w w4
    let x : Fin 9 → Bool := fun i => decide (i = w ∨ i = u)
    let y := Function.update x 4 true
    have hy : y = (fun i => decide (i = 4 ∨ i = w ∨ i = u)) := by
      funext i
      by_cases h : i = 4 <;> simp [y,x,h]
    have wa : (D.wires (List.ofFn x)).getD a false = true := by
      rw [show a = w.val by rfl, raw]
      simp [x]
    have wb : (D.wires (List.ofFn y)).getD a false = true := by
      rw [show a = w.val by rfl, raw, hy]
      simp
    have ex := computes x
    have ey := computes y
    rw [wa, Bool.or_true] at ex
    rw [wb, Bool.or_true] at ey
    change D.eval (List.ofFn (Function.update y 4 true)) = f y at ey
    rw [show Function.update y 4 true = y by simp [y,Function.update_idem], hy] at ey
    change D.eval (List.ofFn y) = f x at ex
    rw [h0] at ex
    rw [h1, ← hy, ex] at ey
    cases ey
  have prefixSize : pre.length ≤ D.size := by
    change pre.length ≤ D.gates.length
    have e := congrArg List.length prefixD
    simp only [List.length_take] at e
    omega
  have noFour : ∀ q ∈ D.gates.take pre.length, 4 ∉ q.inputs := by
    rw [prefixD]
    intro q hq
    exact absent q (List.mem_append_left _ hq)
  have others : ∀ w ∈ ([6,7] : List ℕ),
      (D.gates.filter (fun q => q.inputs.contains w)).map Gate.op = [GateOp.or] := by
    intro w hw
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl | rfl
    · rw [keep 6 (by decide) (by decide) (by omega)]
      exact one 6 (by simp)
    · rw [keep 7 (by decide) (by decide) (by omega)]
      exact one 7 (by simp)
  obtain ⟨x,hx⟩ := remaining D a pre.length fanD (by omega) internal aBound prefixSize hnot noFour others
  exact hx (computes x)
