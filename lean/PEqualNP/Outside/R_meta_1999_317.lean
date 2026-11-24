import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The first child follows from L-meta-1511 by evaluating the gate recursor. The second
-- compresses the active inputs and pads the two shores. The last child counts
-- only incidences whose cheapest proof needs more than two line occurrences.
theorem PEqualNP.Outside.R_meta_1999_317
    (low : ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : PEqualNP.CircuitLowerBounds.Circuit) (echo : Fin N → Fin N → WithTop ℕ),
    (∀ (p w : Fin N), echo p w = (C.gates.foldl (fun acc g => acc ++ [GateOp.rec (motive := fun _ => WithTop ℕ) (g.inputs.map fun i => acc.getD i ⊤).sum ((g.inputs.map fun i => acc.getD i ⊤).foldr min ⊤) ⊤ (fun _ => ⊤) ⊤ g.op]) (List.ofFn (fun k : Fin (N + N) => if k = Fin.castAdd N p then (0 : WithTop ℕ) else if k = Fin.natAdd N w then (1 : WithTop ℕ) else ⊤))).getD C.output ⊤) →
    (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) →
    PEqualNP.MetaComplexity.Monotone2 C →
    (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = true →
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
    (((List.finRange N).toFinset.product (List.finRange N).toFinset).filter (fun e : Fin N × Fin N =>
      I e.1 e.2 ∧ 1 ≤ echo e.1 e.2 ∧ echo e.1 e.2 ≤ 2 ∧
      PEqualNP.MetaComplexity.circuitFun (N + N) C
        (fun k => decide (k = Fin.castAdd N e.1 ∨ k = Fin.natAdd N e.2)) = true)).card
      ≤ 432 * C.size + 2 * N + 48)
    (compact : ∀ (m n : ℕ) (R : Fin m → Fin n → Prop) [∀ i j, Decidable (R i j)]
      (C : Circuit), Monotone2 C →
      (∀ i, (Finset.univ.filter (R i)).card = 0 ∨ 3 ≤ (Finset.univ.filter (R i)).card) →
      (∀ j, (Finset.univ.filter (Function.swap R j)).card = 0 ∨ 3 ≤ (Finset.univ.filter (Function.swap R j)).card) →
      (∀ i k u v, R i u → R k u → R i v → R k v → i = k ∨ u = v) →
      (∀ x y, C.eval (List.ofFn x ++ List.ofFn y) = decide (∃ i j, R i j ∧ x i = true ∧ y j = true)) →
      ∃ (N : ℕ) (I : Fin N → Fin N → Bool) (D : Circuit),
        N ≤ 2*(C.size+1) ∧ D.size ≤ C.size ∧ Monotone2 D ∧
        (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) ∧
        (∀ z : Fin (N+N) → Bool, circuitFun (N+N) D z = true ↔
          ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧
        (∑ i, (Finset.univ.filter (R i)).card) = (((List.finRange N).toFinset.product (List.finRange N).toFinset).filter (fun e : Fin N × Fin N => I e.1 e.2)).card)
    (high : ∃ c : ℕ, ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (D : Circuit),
      (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) →
      IsMinimalMonoCircuit (N+N) D →
      (∀ z : Fin (N+N) → Bool, circuitFun (N+N) D z = true ↔
        ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
      (((List.finRange N).toFinset.product (List.finRange N).toFinset).filter (fun e : Fin N × Fin N => I e.1 e.2 ∧
        2 < (fun (p w : Fin N) => (D.gates.foldl (fun acc g => acc ++ [GateOp.rec (motive := fun _ => WithTop ℕ) (g.inputs.map fun i => acc.getD i ⊤).sum ((g.inputs.map fun i => acc.getD i ⊤).foldr min ⊤) ⊤ (fun _ => ⊤) ⊤ g.op]) (List.ofFn (fun k : Fin (N + N) => if k = Fin.castAdd N p then (0 : WithTop ℕ) else if k = Fin.natAdd N w then (1 : WithTop ℕ) else ⊤))).getD D.output ⊤) e.1 e.2)).card ≤ c * (D.size+1)) :
    ∃ (x1 : ℕ), ∀ (x2 x3 : ℕ) (x4 : Fin x2 → Fin x3 → Prop) [x5 : (x5 : Fin x2) → (x6 : Fin x3) → Decidable (x4 x5 x6)], (∀ (x6 : Fin x2), (Finset.filter (x4 x6) Finset.univ).card = (0 : ℕ) ∨ (3 : ℕ) ≤ (Finset.filter (x4 x6) Finset.univ).card) → (∀ (x7 : Fin x3), (Finset.filter (Function.swap x4 x7) Finset.univ).card = (0 : ℕ) ∨ (3 : ℕ) ≤ (Finset.filter (Function.swap x4 x7) Finset.univ).card) → (∀ (x8 x9 : Fin x2) (x10 x11 : Fin x3), x4 x8 x10 → x4 x9 x10 → x4 x8 x11 → x4 x9 x11 → x8 = x9 ∨ x10 = x11) → ∀ (x9 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x9 → (∀ (x11 : Fin x2 → Bool) (x12 : Fin x3 → Bool), x9.eval (List.ofFn x11 ++ List.ofFn x12) = Decidable.decide (∃ (x13 : Fin x2) (x14 : Fin x3), x4 x13 x14 ∧ x11 x13 = Bool.true ∧ x12 x14 = Bool.true)) → ∑ x12 : Fin x2, (Finset.filter (x4 x12) Finset.univ).card ≤ x1 * (x9.size + (1 : ℕ)) := by
  classical
  have evalAnd (xs : List Bool) : GateOp.and.eval xs = xs.all id := rfl
  have evalOr (xs : List Bool) : GateOp.or.eval xs = xs.any id := rfl
  let step (ws : List (WithTop ℕ)) (g : Gate) : List (WithTop ℕ) := by
    classical
    exact ws ++ [GateOp.rec (motive := fun _ => WithTop ℕ) (g.inputs.map fun i => ws.getD i ⊤).sum ((g.inputs.map fun i => ws.getD i ⊤).foldr min ⊤) ⊤ (fun _ => ⊤) ⊤ g.op]

  let bit (x : (WithTop ℕ)) : Bool := decide (x = 0)

  have getD_map (xs : List (WithTop ℕ)) (i : ℕ) :
      (xs.map bit).getD i false = bit (xs.getD i ⊤) := by
    simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
    cases xs[i]? <;> rfl

  have bit_sum (xs : List (WithTop ℕ)) : bit xs.sum = (xs.map bit).all id := by
    induction xs with
    | nil => simp [bit]
    | cons x xs ih =>
      simp only [List.sum_cons, List.map_cons, List.all_cons, id_eq, ← ih]
      simp [bit]

  have bit_minimum (xs : List (WithTop ℕ)) : bit (xs.foldr min ⊤) = (xs.map bit).any id := by
    induction xs with
    | nil => simp [bit]
    | cons x xs ih =>
      simp only [List.foldr_cons, List.map_cons, List.any_cons, id_eq, ← ih]
      by_cases h : x ≤ xs.foldr min ⊤
      · rw [min_eq_left h]
        by_cases hx : x = 0
        · simp [bit,hx]
        · have hy : xs.foldr min ⊤ ≠ 0 := by intro e; rw [e] at h; exact hx (le_antisymm h zero_le)
          simp [bit,hx,hy]
      · rw [min_eq_right (le_of_not_ge h)]
        have hx : x ≠ 0 := by intro e; rw [e] at h; exact h zero_le
        simp [bit,hx]

  have fold_bits (gs : List Gate) (ws : List (WithTop ℕ))
      (hops : ∀ g ∈ gs, g.op = .and ∨ g.op = .or) :
      (gs.foldl step ws).map bit = gs.foldl
        (fun (vs : List Bool) (g : Gate) => vs ++ [g.op.eval (g.inputs.map (fun i => vs.getD i false))])
        (ws.map bit) := by
    induction gs generalizing ws with
    | nil => rfl
    | cons g gs ih =>
      simp only [List.foldl_cons]
      rw [ih _ (fun a ha => hops a (List.mem_cons_of_mem g ha))]
      congr 1
      have inputs : (g.inputs.map fun i => (ws.map bit).getD i false) =
          (g.inputs.map fun i => ws.getD i ⊤).map bit := by
        simp only [getD_map,List.map_map,Function.comp_def]
      rw [inputs]
      rcases hops g (List.mem_cons_self) with hg|hg <;>
        simp [step,hg,evalAnd,evalOr,bit_sum,bit_minimum]

  have one_le_of_nonzero (x : WithTop ℕ) (h : x ≠ 0) : 1 ≤ x := by
    cases x using WithTop.recTopCoe with
    | top => exact le_top
    | coe k =>
      have hk : k ≠ 0 := by intro z; subst k; apply h; rfl
      exact WithTop.coe_le_coe.mpr (Nat.one_le_iff_ne_zero.mpr hk)

  -- A zero-cost proof on the pair would already accept the point-only input.
  have positive_echo (N : ℕ) (I : Fin N → Fin N → Prop) (D : Circuit)
      (hmono : Monotone2 D)
      (hs : ∀ z : Fin (N+N) → Bool, circuitFun (N+N) D z = true →
        ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)
      (p w : Fin N) : 1 ≤ (D.gates.foldl (fun acc g => acc ++ [GateOp.rec (motive := fun _ => WithTop ℕ) (g.inputs.map fun i => acc.getD i ⊤).sum ((g.inputs.map fun i => acc.getD i ⊤).foldr min ⊤) ⊤ (fun _ => ⊤) ⊤ g.op]) (List.ofFn (fun k : Fin (N + N) => if k = Fin.castAdd N p then (0 : WithTop ℕ) else if k = Fin.natAdd N w then (1 : WithTop ℕ) else ⊤))).getD D.output ⊤ := by
    classical
    let init := List.ofFn (fun k : Fin (N+N) => if k = Fin.castAdd N p then (0 : (WithTop ℕ))
      else if k = Fin.natAdd N w then 1 else ⊤)
    let e := (D.gates.foldl step init).getD D.output ⊤
    change 1 ≤ e
    have zeroImpossible : e ≠ 0 := by
      intro bad
      have eq := congrArg (fun bs : List Bool => bs.getD D.output false)
        (fold_bits D.gates init (fun g hg => by simpa using (hmono g hg).1))
      rw [getD_map] at eq
      have inp : init.map bit = List.ofFn (fun i : Fin (N+N) => decide (i = Fin.castAdd N p)) := by
        rw [show init = _ from rfl, List.map_ofFn]
        congr 1
        funext i
        change bit (if i = Fin.castAdd N p then 0 else if i = Fin.natAdd N w then 1 else ⊤) = _
        by_cases h : i = Fin.castAdd N p
        · rw [if_pos h, decide_eq_true h]; rfl
        · rw [if_neg h,decide_eq_false h]; split <;> rfl
      rw [inp] at eq
      change bit e = circuitFun (N+N) D _ at eq
      have hit := hs _ (eq.symm.trans (by simp [bit,bad]))
      obtain ⟨a,b,_,_,hb⟩ := hit
      have hh : Fin.natAdd N b = Fin.castAdd N p := of_decide_eq_true hb
      have hv := congrArg Fin.val hh
      simp only [Fin.val_natAdd,Fin.val_castAdd] at hv
      omega
    exact one_le_of_nonzero _ zeroImpossible
  obtain ⟨c,hc⟩ := high
  refine ⟨c+484,?_⟩
  intro m n R inst hr hcol rect C hm hf
  obtain ⟨N,ib,B,hN,hBsize,hBMon,hrect,hBcomp,count⟩ := compact m n R C hm hr hcol rect hf
  let I := fun p l : Fin N => ib p l = true
  let attainable (k : ℕ) := ∃ E : Circuit, E.size = k ∧ Monotone2 E ∧
    circuitFun (N+N) E = circuitFun (N+N) B
  have base : attainable B.size := ⟨B,rfl,hBMon,rfl⟩
  have existsSize : ∃ k, attainable k := ⟨_,base⟩
  obtain ⟨D,hDsize,hMon,hSame⟩ := Nat.find_spec existsSize
  have hsize : D.size ≤ C.size := (hDsize.trans_le (Nat.find_min' existsSize base)).trans hBsize
  have hmin : IsMinimalMonoCircuit (N+N) D := by
    refine ⟨hMon,?_⟩
    intro E hE same
    exact hDsize.trans_le (Nat.find_min' existsSize ⟨E,rfl,hE,same.trans hSame⟩)
  have hcomp (z : Fin (N+N) → Bool) := (congrArg (fun f : (Fin (N+N) → Bool) → Bool => f z) hSame)
  have hcomp' (z : Fin (N+N) → Bool) : circuitFun (N+N) D z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true := by
    rw [hcomp z]; exact hBcomp z
  let echo := fun p w : Fin N => (D.gates.foldl (fun acc g => acc ++ [GateOp.rec (motive := fun _ => WithTop ℕ) (g.inputs.map fun i => acc.getD i ⊤).sum ((g.inputs.map fun i => acc.getD i ⊤).foldr min ⊤) ⊤ (fun _ => ⊤) ⊤ g.op]) (List.ofFn (fun k : Fin (N + N) => if k = Fin.castAdd N p then (0 : WithTop ℕ) else if k = Fin.natAdd N w then (1 : WithTop ℕ) else ⊤))).getD D.output ⊤
  have hlow := low N I D echo (fun _ _ => rfl) hrect hMon (fun z => (hcomp' z).mp)
  have hhigh := hc N I D hrect hmin hcomp'
  have pos := positive_echo N I D hMon (fun z => (hcomp' z).mp)
  let edges := ((List.finRange N).toFinset.product (List.finRange N).toFinset).filter (fun e : Fin N × Fin N => I e.1 e.2)
  have partition := Finset.card_filter_add_card_filter_not (s:=edges) (fun e => echo e.1 e.2 ≤ 2)
  have small : (edges.filter (fun e => echo e.1 e.2 ≤ 2)).card ≤ 432*D.size + 2*N+48 := by
    apply le_trans (Finset.card_le_card ?_) hlow
    intro e he
    simp only [edges,List.toFinset_finRange,Finset.mem_product,Finset.mem_filter,Finset.mem_univ,true_and] at he ⊢
    exact ⟨he.1.1,he.1.2,pos e.1 e.2,he.2,(hcomp' _).mpr ⟨e.1,e.2,he.1.2,by simp,by simp⟩⟩
  have large : (edges.filter (fun e => ¬ echo e.1 e.2 ≤ 2)).card ≤ c*(D.size+1) := by
    apply le_trans (Finset.card_le_card ?_) hhigh
    intro e he
    simp only [edges,List.toFinset_finRange,Finset.mem_product,Finset.mem_filter,Finset.mem_univ,true_and] at he ⊢
    exact ⟨he.1.1,he.1.2,lt_of_not_ge he.2⟩
  have scaled := Nat.mul_le_mul_left c (Nat.add_le_add_right hsize 1)
  rw [count]
  change edges.card ≤ _
  rw [Nat.add_mul]
  omega
