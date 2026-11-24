import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- A conjunction of two original input wires can be evaluated first.
-- Every pair meeting a degree-two vertex falls into one of the three checked leading conjunction cases.
set_option maxHeartbeats 6000000 in
theorem PEqualNP.Outside.R_meta_2498_169
    (known : ∀ (C : Circuit) (a b : Fin 9), a ≠ b →
      (a ∈ ([4, 6, 7] : List (Fin 9)) ∨ b ∈ ([4, 6, 7] : List (Fin 9))) →
      FanInTwo C → (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x a && x b)) →
      circuitFun 9 C = (fun x : Fin 9 → Bool =>
        ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] :
          List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)) → 16 ≤ C.size)
    (residual :
      let W := fun (C : Circuit) (i : ℕ) (x : Fin 9 → Bool) => (C.wires (List.ofFn x)).getD i false
      ∀ C : Circuit, FanInTwo C →
      (∀ x : Fin 9 → Bool, W C 9 x = (x 0 || x 1)) →
      circuitFun 9 C = (fun x : Fin 9 → Bool =>
        ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] :
          List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)) →
      (∀ v ∈ ([0,1,2,3,5,8] : List (Fin 9)), ∀ S : Finset ℕ,
        (∀ j ∈ S, j < C.size ∧
          ((∃ b : Bool, ∀ x : Fin 9 → Bool, x v = false →
            W C (9+j) x = b) ∨
          (∃ i < 9+j, ∀ x : Fin 9 → Bool, x v = false →
            W C (9+j) x = W C i x))) → S.card ≤ 3) →
      (∀ a b : Fin 9, a ≠ b →
        (a ∈ ([4, 6, 7] : List (Fin 9)) ∨ b ∈ ([4, 6, 7] : List (Fin 9))) →
        (⟨GateOp.and, [a.val, b.val]⟩ : Gate) ∉ C.gates) → 16 ≤ C.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (0 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x5 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x4 x5.1 && x4 x5.2) → (∀ x5 ∈ [(0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))], ∀ (x7 : Finset ℕ), (∀ x8 ∈ x7, x8 < x1.size ∧ ((∃ (x10 : Bool), ∀ (x11 : Fin (9 : ℕ) → Bool), x11 x5 = Bool.false → (x1.wires (List.ofFn x11)).getD ((9 : ℕ) + x8) Bool.false = x10) ∨ ∃ x10 < (9 : ℕ) + x8, ∀ (x11 : Fin (9 : ℕ) → Bool), x11 x5 = Bool.false → (x1.wires (List.ofFn x11)).getD ((9 : ℕ) + x8) Bool.false = (x1.wires (List.ofFn x11)).getD x10 Bool.false)) → x7.card ≤ (3 : ℕ)) → (16 : ℕ) ≤ x1.size := by
  intro C fan first correct few
  have rawMove (n : ℕ) (C : Circuit) (g : Gate) (hg : g ∈ C.gates)
      (raw : ∀ i ∈ g.inputs, i < n) (fan : FanInTwo C) :
      ∃ D : Circuit, FanInTwo D ∧ D.size = C.size ∧ circuitFun n D = circuitFun n C ∧
        ∀ x : Fin n → Bool, (D.wires (List.ofFn x)).getD n false =
          g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false) := by
    obtain ⟨before, after, hC⟩ := List.append_of_mem hg
    let value (w : List Bool) (a : Gate) := a.op.eval (a.inputs.map fun i => w.getD i false)
    let emit (w : List Bool) (a : Gate) := w ++ [value w a]
    let shift (i : ℕ) := if i < n then i else i + 1
    let cut := n + before.length
    let move (i : ℕ) := if i < n then i else if i < cut then i + 1 else if i = cut then n else i
    let rename (ρ : ℕ → ℕ) (a : Gate) : Gate := ⟨a.op, a.inputs.map ρ⟩
    let D : Circuit :=
      ⟨g :: (before.map (rename shift) ++ after.map (rename move)), move C.output⟩
    have appendRead (w : List Bool) (b : Bool) (i : ℕ) :
        (w ++ [b]).getD i false = if i < w.length then w.getD i false
          else if i = w.length then b else false := by
      by_cases h : i < w.length
      · simp only [ite_eq_left h, List.getD_append _ _ _ _ h]
      · simp only [ite_eq_right h]
        by_cases he : i = w.length
        · subst i
          simp
        · rw [ite_eq_right he, List.getD_eq_default _ _ (by simp; omega)]
    have lengthOf (gs : List Gate) (w : List Bool) :
        (gs.foldl emit w).length = w.length + gs.length := by
      induction gs generalizing w with
      | nil => simp
      | cons a as ih => simp [ih, emit]; omega
    have keeps (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
        (gs.foldl emit w).getD i false = w.getD i false := by
      induction gs generalizing w with
      | nil => rfl
      | cons a as ih =>
          rw [List.foldl_cons, ih]
          · exact List.getD_append _ _ _ _ hi
          · simp [emit]; omega
    have run (ρ : ℕ → ℕ) (base shiftBy : ℕ)
        (low : ∀ i < base, ρ i < base + shiftBy)
        (top : ∀ i, base ≤ i → ρ i = i + shiftBy)
        (gs : List Gate) (old fresh : List Bool) (oldLen : base ≤ old.length)
        (sizes : fresh.length = old.length + shiftBy)
        (same : ∀ i, fresh.getD (ρ i) false = old.getD i false) :
        ∀ i, ((gs.map (rename ρ)).foldl emit fresh).getD (ρ i) false =
          (gs.foldl emit old).getD i false := by
      induction gs generalizing old fresh with
      | nil => exact same
      | cons a as ih =>
          have vEq : value fresh (rename ρ a) = value old a := by
            change a.op.eval ((a.inputs.map ρ).map fun i => fresh.getD i false) =
              a.op.eval (a.inputs.map fun i => old.getD i false)
            rw [List.map_map]
            congr 1
            exact List.map_congr_left fun i _ => same i
          have next : ∀ i, (emit fresh (rename ρ a)).getD (ρ i) false =
              (emit old a).getD i false := by
            intro i
            have lt : ρ i < fresh.length ↔ i < old.length := by
              by_cases h : i < base
              · have h' := low i h
                omega
              · have h' := top i (by omega)
                omega
            have eq : ρ i = fresh.length ↔ i = old.length := by
              by_cases h : i < base
              · have h' := low i h
                omega
              · have h' := top i (by omega)
                omega
            simp only [emit, appendRead, lt, eq, same, vEq]
          simp only [List.map_cons, List.foldl_cons]
          exact ih _ _ (by simp [emit]; omega) (by simp [emit]; omega) next
    have sound (x : Fin n → Bool) (i : ℕ) :
        (D.wires (List.ofFn x)).getD (move i) false =
          (C.wires (List.ofFn x)).getD i false := by
      let w := List.ofFn x
      let a := before.foldl emit w
      let b := (before.map (rename shift)).foldl emit (emit w g)
      have hw : w.length = n := by simp [w]
      have ha : a.length = cut := by simp [a, lengthOf, cut, hw]
      have hb : b.length = cut + 1 := by simp [b, lengthOf, emit, cut, hw]; omega
      have ncut : n ≤ cut := by simp [cut]
      have baseRel (j : ℕ) : (emit w g).getD (shift j) false = w.getD j false := by
        by_cases h : j < n
        · rw [show shift j = j by simp [shift, h]]
          exact List.getD_append _ _ _ _ (hw.symm ▸ h)
        · rw [List.getD_eq_default _ _ (by simp [emit, hw, shift, h]; omega),
            List.getD_eq_default _ _ (by omega)]
      have onFront : ∀ j, b.getD (shift j) false = a.getD j false :=
        run shift n 1 (by intro j hj; simp [shift, hj]; omega)
          (by intro j hj; simp [shift, Nat.not_lt.mpr hj]) before w (emit w g)
          (by omega) (by simp [emit]) baseRel
      have bFirst : b.getD n false = value w g := by
        dsimp [b]
        rw [keeps _ _ _ (by simp [emit, hw])]
        simp [emit, hw]
      have gValue : value a g = value w g := by
        unfold value
        congr 1
        apply List.map_congr_left
        intro j hj
        exact keeps before w j (hw.symm ▸ raw j hj)
      have afterMove (j : ℕ) : b.getD (move j) false = (emit a g).getD j false := by
        by_cases h : j < cut
        · have em : move j = shift j := by simp [move, shift, h]
          rw [em, onFront]
          exact (List.getD_append _ _ _ _ (ha.symm ▸ h)).symm
        · by_cases he : j = cut
          · subst j
            have em : move cut = n := by simp [move, Nat.not_lt.mpr ncut]
            rw [em, bFirst, gValue.symm]
            simp [emit, ha]
          · have em : move j = j := by simp [move, h, he, show ¬j < n by omega]
            rw [em, List.getD_eq_default _ _ (by omega),
              List.getD_eq_default _ _ (by simp [emit, ha]; omega)]
      have finish := run move (cut + 1) 0
        (by
          intro j hj
          by_cases ht : j < n
          · simp [move, ht, hj]
          · by_cases hc : j < cut
            · simpa only [move, ite_eq_right ht, ite_eq_left hc, Nat.add_zero] using
                Nat.succ_lt_succ hc
            · have eq : j = cut := by omega
              subst j
              rw [show move cut = n by simp [move, Nat.not_lt.mpr ncut], Nat.add_zero]
              exact Nat.lt_succ_of_le ncut)
        (by intro j hj; simp [move, show ¬j < n by omega, show ¬j < cut by omega,
            show j ≠ cut by omega])
        after (emit a g) b (by simp [emit, ha]) (by simp [emit, ha, hb]) afterMove i
      change ((g :: (before.map (rename shift) ++ after.map (rename move))).foldl emit w).getD
          (move i) false = (C.gates.foldl emit w).getD i false
      rw [hC, List.foldl_cons, List.foldl_append, List.foldl_append, List.foldl_cons]
      exact finish
    refine ⟨D, ?_, ?_, ?_, ?_⟩
    · intro a ha
      have maps (ρ : ℕ → ℕ) (q : Gate) (hq : q ∈ C.gates) :
          (rename ρ q).op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
          (rename ρ q).inputs.length ≤ 2 := by
        simpa [rename] using fan q hq
      change a ∈ g :: (before.map (rename shift) ++ after.map (rename move)) at ha
      rcases List.mem_cons.mp ha with eq | ha
      · rw [eq]
        exact fan g hg
      rcases List.mem_append.mp ha with ha | ha
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ha
        apply maps shift q
        simp [hC, hq]
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ha
        apply maps move q
        simp [hC, hq]
    · change (g :: (before.map (rename shift) ++ after.map (rename move))).length = C.gates.length
      rw [hC]
      simp only [List.length_cons, List.length_append, List.length_map]
      omega
    · funext x
      exact sound x C.output
    · intro x
      let w := List.ofFn x
      have hw : w.length = n := by simp [w]
      change ((g :: (before.map (rename shift) ++ after.map (rename move))).foldl emit w).getD
        n false = value w g
      rw [List.foldl_cons, keeps _ _ _ (by simp [emit, hw])]
      simp [emit, hw]

  by_cases h : ∃ a b : Fin 9, a ≠ b ∧
      (a ∈ ([4, 6, 7] : List (Fin 9)) ∨ b ∈ ([4, 6, 7] : List (Fin 9))) ∧
      (⟨GateOp.and, [a.val, b.val]⟩ : Gate) ∈ C.gates
  · obtain ⟨a, b, distinct, degree, member⟩ := h
    let g : Gate := ⟨GateOp.and, [a.val, b.val]⟩
    have raw : ∀ i ∈ g.inputs, i < 9 := by
      intro i hi
      simp [g] at hi
      rcases hi with rfl | rfl
      · exact a.isLt
      · exact b.isLt
    obtain ⟨D, fanD, sizeD, correctD, leadD⟩ := rawMove 9 C g member raw fan
    have lead (x : Fin 9 → Bool) :
        (D.wires (List.ofFn x)).getD 9 false = (x a && x b) := by
      have read (v : Fin 9) : (List.ofFn x).getD v.val false = x v := by
        rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using v.isLt)]
        simp only [List.getElem_ofFn]
      have andEval (w : List Bool) : GateOp.and.eval w = w.all id := rfl
      rw [leadD x]
      simp only [g, andEval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
        id_eq, Bool.and_true, read]
    have bound := known D a b distinct degree fanD lead (correctD.trans correct)
    rwa [sizeD] at bound
  · apply residual C fan first correct few
    intro a b distinct degree member
    exact h ⟨a, b, distinct, degree, member⟩
