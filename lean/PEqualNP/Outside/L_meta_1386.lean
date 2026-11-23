import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1386

open PEqualNP.CircuitLowerBounds

lemma fold_prefix (gs : List Gate) (w : List Bool) :
    ∃ t : List Bool,
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w
        = w ++ t ∧ t.length = gs.length := by
  induction gs generalizing w with
  | nil => exact ⟨[], by simp, rfl⟩
  | cons g gs ih =>
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, ?_⟩
    · rw [List.foldl_cons, ht]
      simp
    · simp [hl]

lemma getD_app_len (W l : List Bool) :
    (W ++ l).getD W.length false = l.getD 0 false := by
  rw [List.getD_append_right _ _ _ _ (by omega)]
  simp

lemma getD_app_lt (W l : List Bool) (i : ℕ) (h : i < W.length) :
    (W ++ l).getD i false = W.getD i false :=
  List.getD_append _ _ _ _ h

def wv (gs : List Gate) (x : List Bool) (i : ℕ) : Bool :=
  (Circuit.wires ⟨gs, 0⟩ x).getD i false

lemma eval_wv (gs : List Gate) (o : ℕ) (x : List Bool) : Circuit.eval ⟨gs, o⟩ x = wv gs x o := rfl

lemma wv_input (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    wv gs x i = x.getD i false := by
  unfold wv Circuit.wires
  dsimp only
  obtain ⟨t, ht, _⟩ := fold_prefix gs x
  rw [ht, getD_app_lt _ _ _ hi]

lemma wv_mid (pre post : List Gate) (g : Gate) (x : List Bool)
    (hin : ∀ i ∈ g.inputs, i < x.length + pre.length) :
    wv (pre ++ g :: post) x (x.length + pre.length) =
      g.op.eval (g.inputs.map fun i => wv (pre ++ g :: post) x i) := by
  unfold wv Circuit.wires
  dsimp only
  rw [List.foldl_append, List.foldl_cons]
  obtain ⟨t1, h1, l1⟩ := fold_prefix pre x
  rw [h1]
  obtain ⟨t2, h2, _⟩ := fold_prefix post
    (x ++ t1 ++ [g.op.eval (g.inputs.map fun i => (x ++ t1).getD i false)])
  rw [h2]
  have hlen : (x ++ t1).length = x.length + pre.length := by simp [l1]
  rw [List.append_assoc (x ++ t1), ← hlen, getD_app_len]
  simp only [List.singleton_append, List.getD_cons_zero]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [getD_app_lt (x ++ t1) _ i (by rw [hlen]; exact hin i hi)]

lemma wv_at (gs : List Gate) (x : List Bool) (n j : ℕ) (g : Gate) (hx : x.length = n)
    (hg : gs[j]? = some g) (hin : ∀ i ∈ g.inputs, i < n + j) :
    wv gs x (n + j) = g.op.eval (g.inputs.map fun i => wv gs x i) := by
  obtain ⟨hj, hgj⟩ := List.getElem?_eq_some_iff.1 hg
  have hs : gs = gs.take j ++ g :: gs.drop (j + 1) := by
    rw [← hgj]
    simp
  have hl : (gs.take j).length = j := by simp; omega
  have h := wv_mid (gs.take j) (gs.drop (j + 1)) g x (by rw [hl, hx]; exact hin)
  rw [← hs, hl, hx] at h
  exact h

lemma ofFnN (x : Fin (7 + 7) → Bool) : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13] := by
  simp [List.ofFn_succ]


end PEqualNP.Outside.L_meta_1386

theorem PEqualNP.Outside.L_meta_1386 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = { gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [18, 16] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [19, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [3, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [4, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [5, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 21] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [24, 22] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [25, 23] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [20, 26] }], output := 27 } → PEqualNP.MetaComplexity.Monotone2 C ∧ C.size = 14 ∧ PEqualNP.CircuitLowerBounds.HasLineDegree (7 + 7) (Finset.Ico 7 (7 + 7)) C 2 ∧ (C.lineDegrees (7 + 7) (Finset.Ico 7 (7 + 7))).getD 20 0 ≤ 1 ∧ (C.lineDegrees (7 + 7) (Finset.Ico 7 (7 + 7))).getD 26 0 ≤ 1 ∧ (∀ z : Fin (7 + 7) → Bool, PEqualNP.MetaComplexity.circuitFun (7 + 7) C z = true → ∃ p l : Fin 7, (l.val = p.val ∨ (l.val + 1) % 7 = p.val ∨ (l.val + 3) % 7 = p.val) ∧ z (Fin.castAdd 7 p) = true ∧ z (Fin.natAdd 7 l) = true) ∧ (C.wires (List.ofFn (fun v : Fin (7 + 7) => if v = Fin.castAdd 7 0 then true else if v = Fin.natAdd 7 0 then true else false))).getD 20 false = true ∧ (C.wires (List.ofFn (fun v : Fin (7 + 7) => if v = Fin.castAdd 7 0 then true else if v = Fin.natAdd 7 0 then true else false))).getD 26 false = true ∧ (C.wires (List.ofFn (fun u : Fin (7 + 7) => decide (u = Fin.castAdd 7 0)))).getD 20 false = false ∧ (C.wires (List.ofFn (fun u : Fin (7 + 7) => decide (u = Fin.castAdd 7 0)))).getD 26 false = false ∧ (∀ l1 : Fin 7, ∃ z1 : Fin (7 + 7) → Bool, (∀ p1 : Fin 7, (l1.val = p1.val ∨ (l1.val + 1) % 7 = p1.val ∨ (l1.val + 3) % 7 = p1.val) → z1 (Fin.castAdd 7 p1) = false) ∧ (C.wires (List.ofFn z1)).getD 20 false = true ∧ ¬ ∃ q1 m1 : Fin 7, (m1.val = q1.val ∨ (m1.val + 1) % 7 = q1.val ∨ (m1.val + 3) % 7 = q1.val) ∧ z1 (Fin.castAdd 7 q1) = true ∧ z1 (Fin.natAdd 7 m1) = true) ∧ (∀ l2 : Fin 7, ∃ z2 : Fin (7 + 7) → Bool, (∀ p2 : Fin 7, (l2.val = p2.val ∨ (l2.val + 1) % 7 = p2.val ∨ (l2.val + 3) % 7 = p2.val) → z2 (Fin.castAdd 7 p2) = false) ∧ (C.wires (List.ofFn z2)).getD 26 false = true ∧ ¬ ∃ q2 m2 : Fin 7, (m2.val = q2.val ∨ (m2.val + 1) % 7 = q2.val ∨ (m2.val + 3) % 7 = q2.val) ∧ z2 (Fin.castAdd 7 q2) = true ∧ z2 (Fin.natAdd 7 m2) = true) := by
  intro C hC
  have sound : ∀ z : Fin (7 + 7) → Bool, PEqualNP.MetaComplexity.circuitFun (7 + 7) C z = true →
      ∃ p l : Fin 7, (l.val = p.val ∨ (l.val + 1) % 7 = p.val ∨ (l.val + 3) % 7 = p.val) ∧
        z (Fin.castAdd 7 p) = true ∧ z (Fin.natAdd 7 l) = true := by
    intro z hz
    have hz2 : PEqualNP.Outside.L_meta_1386.wv C.gates (List.ofFn z) 27 = true := by
      have h27 : C.output = 27 := by rw [hC]
      have e : PEqualNP.CircuitLowerBounds.Circuit.eval C (List.ofFn z) =
          PEqualNP.Outside.L_meta_1386.wv C.gates (List.ofFn z) C.output := rfl
      rw [← h27, ← e]
      exact hz
    have e14 : PEqualNP.Outside.L_meta_1386.wv C.gates (List.ofFn z) 14 = (PEqualNP.Outside.L_meta_1386.wv C.gates (List.ofFn z) 0 && PEqualNP.Outside.L_meta_1386.wv C.gates (List.ofFn z) 7) := by
      have h := PEqualNP.Outside.L_meta_1386.wv_at C.gates (List.ofFn z) 14 0 ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 7]⟩ (by simp) (by rw [hC]; rfl) (by decide)
      simpa [PEqualNP.CircuitLowerBounds.GateOp.eval] using h
    have e15 : PEqualNP.Outside.L_meta_1386.wv C.gates (List.ofFn z) 15 = (PEqualNP.Outside.L_meta_1386.wv C.gates (List.ofFn z) 0 && PEqualNP.Outside.L_meta_1386.wv C.gates (List.ofFn z) 8) := by
      have h := PEqualNP.Outside.L_meta_1386.wv_at C.gates (List.ofFn z) 14 1 ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 8]⟩ (by simp) (by rw [hC]; rfl) (by decide)
      simpa [PEqualNP.CircuitLowerBounds.GateOp.eval] using h
    have e16 : PEqualNP.Outside.L_meta_1386.wv C.gates (List.ofFn z) 16 = (PEqualNP.Outside.L_meta_1386.wv C.gates (List.ofFn z) 1 && PEqualNP.Outside.L_meta_1386.wv C.gates (List.ofFn z) 9) := by
      have h := PEqualNP.Outside.L_meta_1386.wv_at C.gates (List.ofFn z) 14 2 ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 9]⟩ (by simp) (by rw [hC]; rfl) (by decide)
      simpa [PEqualNP.CircuitLowerBounds.GateOp.eval] using h
    have e17 : PEqualNP.Outside.L_meta_1386.wv C.gates (List.ofFn z) 17 = (PEqualNP.Outside.L_meta_1386.wv C.gates (List.ofFn z) 2 && PEqualNP.Outside.L_meta_1386.wv C.gates (List.ofFn z) 10) := by
      have h := PEqualNP.Outside.L_meta_1386.wv_at C.gates (List.ofFn z) 14 3 ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 10]⟩ (by simp) (by rw [hC]; rfl) (by decide)
      simpa [PEqualNP.CircuitLowerBounds.GateOp.eval] using h
    have e18 : PEqualNP.Outside.L_meta_1386.wv C.gates (List.ofFn z) 18 = (PEqualNP.Outside.L_meta_1386.wv C.gates (List.ofFn z) 14 || PEqualNP.Outside.L_meta_1386.wv C.gates (List.ofFn z) 15) := by
      have h := PEqualNP.Outside.L_meta_1386.wv_at C.gates (List.ofFn z) 14 4 ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 15]⟩ (by simp) (by rw [hC]; rfl) (by decide)
      simpa [PEqualNP.CircuitLowerBounds.GateOp.eval] using h
    have e19 : PEqualNP.Outside.L_meta_1386.wv C.gates (List.ofFn z) 19 = (PEqualNP.Outside.L_meta_1386.wv C.gates (List.ofFn z) 18 || PEqualNP.Outside.L_meta_1386.wv C.gates (List.ofFn z) 16) := by
      have h := PEqualNP.Outside.L_meta_1386.wv_at C.gates (List.ofFn z) 14 5 ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [18, 16]⟩ (by simp) (by rw [hC]; rfl) (by decide)
      simpa [PEqualNP.CircuitLowerBounds.GateOp.eval] using h
    have e20 : PEqualNP.Outside.L_meta_1386.wv C.gates (List.ofFn z) 20 = (PEqualNP.Outside.L_meta_1386.wv C.gates (List.ofFn z) 19 || PEqualNP.Outside.L_meta_1386.wv C.gates (List.ofFn z) 17) := by
      have h := PEqualNP.Outside.L_meta_1386.wv_at C.gates (List.ofFn z) 14 6 ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [19, 17]⟩ (by simp) (by rw [hC]; rfl) (by decide)
      simpa [PEqualNP.CircuitLowerBounds.GateOp.eval] using h
    have e21 : PEqualNP.Outside.L_meta_1386.wv C.gates (List.ofFn z) 21 = (PEqualNP.Outside.L_meta_1386.wv C.gates (List.ofFn z) 3 && PEqualNP.Outside.L_meta_1386.wv C.gates (List.ofFn z) 11) := by
      have h := PEqualNP.Outside.L_meta_1386.wv_at C.gates (List.ofFn z) 14 7 ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 11]⟩ (by simp) (by rw [hC]; rfl) (by decide)
      simpa [PEqualNP.CircuitLowerBounds.GateOp.eval] using h
    have e22 : PEqualNP.Outside.L_meta_1386.wv C.gates (List.ofFn z) 22 = (PEqualNP.Outside.L_meta_1386.wv C.gates (List.ofFn z) 4 && PEqualNP.Outside.L_meta_1386.wv C.gates (List.ofFn z) 7) := by
      have h := PEqualNP.Outside.L_meta_1386.wv_at C.gates (List.ofFn z) 14 8 ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 7]⟩ (by simp) (by rw [hC]; rfl) (by decide)
      simpa [PEqualNP.CircuitLowerBounds.GateOp.eval] using h
    have e23 : PEqualNP.Outside.L_meta_1386.wv C.gates (List.ofFn z) 23 = (PEqualNP.Outside.L_meta_1386.wv C.gates (List.ofFn z) 5 && PEqualNP.Outside.L_meta_1386.wv C.gates (List.ofFn z) 13) := by
      have h := PEqualNP.Outside.L_meta_1386.wv_at C.gates (List.ofFn z) 14 9 ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 13]⟩ (by simp) (by rw [hC]; rfl) (by decide)
      simpa [PEqualNP.CircuitLowerBounds.GateOp.eval] using h
    have e24 : PEqualNP.Outside.L_meta_1386.wv C.gates (List.ofFn z) 24 = (PEqualNP.Outside.L_meta_1386.wv C.gates (List.ofFn z) 14 || PEqualNP.Outside.L_meta_1386.wv C.gates (List.ofFn z) 21) := by
      have h := PEqualNP.Outside.L_meta_1386.wv_at C.gates (List.ofFn z) 14 10 ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 21]⟩ (by simp) (by rw [hC]; rfl) (by decide)
      simpa [PEqualNP.CircuitLowerBounds.GateOp.eval] using h
    have e25 : PEqualNP.Outside.L_meta_1386.wv C.gates (List.ofFn z) 25 = (PEqualNP.Outside.L_meta_1386.wv C.gates (List.ofFn z) 24 || PEqualNP.Outside.L_meta_1386.wv C.gates (List.ofFn z) 22) := by
      have h := PEqualNP.Outside.L_meta_1386.wv_at C.gates (List.ofFn z) 14 11 ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [24, 22]⟩ (by simp) (by rw [hC]; rfl) (by decide)
      simpa [PEqualNP.CircuitLowerBounds.GateOp.eval] using h
    have e26 : PEqualNP.Outside.L_meta_1386.wv C.gates (List.ofFn z) 26 = (PEqualNP.Outside.L_meta_1386.wv C.gates (List.ofFn z) 25 || PEqualNP.Outside.L_meta_1386.wv C.gates (List.ofFn z) 23) := by
      have h := PEqualNP.Outside.L_meta_1386.wv_at C.gates (List.ofFn z) 14 12 ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [25, 23]⟩ (by simp) (by rw [hC]; rfl) (by decide)
      simpa [PEqualNP.CircuitLowerBounds.GateOp.eval] using h
    have e27 : PEqualNP.Outside.L_meta_1386.wv C.gates (List.ofFn z) 27 = (PEqualNP.Outside.L_meta_1386.wv C.gates (List.ofFn z) 20 && PEqualNP.Outside.L_meta_1386.wv C.gates (List.ofFn z) 26) := by
      have h := PEqualNP.Outside.L_meta_1386.wv_at C.gates (List.ofFn z) 14 13 ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [20, 26]⟩ (by simp) (by rw [hC]; rfl) (by decide)
      simpa [PEqualNP.CircuitLowerBounds.GateOp.eval] using h
    have i0 : PEqualNP.Outside.L_meta_1386.wv C.gates (List.ofFn z) 0 = z 0 := by
      rw [PEqualNP.Outside.L_meta_1386.wv_input _ _ _ (by simp), PEqualNP.Outside.L_meta_1386.ofFnN]
      rfl
    have i1 : PEqualNP.Outside.L_meta_1386.wv C.gates (List.ofFn z) 1 = z 1 := by
      rw [PEqualNP.Outside.L_meta_1386.wv_input _ _ _ (by simp), PEqualNP.Outside.L_meta_1386.ofFnN]
      rfl
    have i2 : PEqualNP.Outside.L_meta_1386.wv C.gates (List.ofFn z) 2 = z 2 := by
      rw [PEqualNP.Outside.L_meta_1386.wv_input _ _ _ (by simp), PEqualNP.Outside.L_meta_1386.ofFnN]
      rfl
    have i3 : PEqualNP.Outside.L_meta_1386.wv C.gates (List.ofFn z) 3 = z 3 := by
      rw [PEqualNP.Outside.L_meta_1386.wv_input _ _ _ (by simp), PEqualNP.Outside.L_meta_1386.ofFnN]
      rfl
    have i4 : PEqualNP.Outside.L_meta_1386.wv C.gates (List.ofFn z) 4 = z 4 := by
      rw [PEqualNP.Outside.L_meta_1386.wv_input _ _ _ (by simp), PEqualNP.Outside.L_meta_1386.ofFnN]
      rfl
    have i5 : PEqualNP.Outside.L_meta_1386.wv C.gates (List.ofFn z) 5 = z 5 := by
      rw [PEqualNP.Outside.L_meta_1386.wv_input _ _ _ (by simp), PEqualNP.Outside.L_meta_1386.ofFnN]
      rfl
    have i7 : PEqualNP.Outside.L_meta_1386.wv C.gates (List.ofFn z) 7 = z 7 := by
      rw [PEqualNP.Outside.L_meta_1386.wv_input _ _ _ (by simp), PEqualNP.Outside.L_meta_1386.ofFnN]
      rfl
    have i8 : PEqualNP.Outside.L_meta_1386.wv C.gates (List.ofFn z) 8 = z 8 := by
      rw [PEqualNP.Outside.L_meta_1386.wv_input _ _ _ (by simp), PEqualNP.Outside.L_meta_1386.ofFnN]
      rfl
    have i9 : PEqualNP.Outside.L_meta_1386.wv C.gates (List.ofFn z) 9 = z 9 := by
      rw [PEqualNP.Outside.L_meta_1386.wv_input _ _ _ (by simp), PEqualNP.Outside.L_meta_1386.ofFnN]
      rfl
    have i10 : PEqualNP.Outside.L_meta_1386.wv C.gates (List.ofFn z) 10 = z 10 := by
      rw [PEqualNP.Outside.L_meta_1386.wv_input _ _ _ (by simp), PEqualNP.Outside.L_meta_1386.ofFnN]
      rfl
    have i11 : PEqualNP.Outside.L_meta_1386.wv C.gates (List.ofFn z) 11 = z 11 := by
      rw [PEqualNP.Outside.L_meta_1386.wv_input _ _ _ (by simp), PEqualNP.Outside.L_meta_1386.ofFnN]
      rfl
    have i13 : PEqualNP.Outside.L_meta_1386.wv C.gates (List.ofFn z) 13 = z 13 := by
      rw [PEqualNP.Outside.L_meta_1386.wv_input _ _ _ (by simp), PEqualNP.Outside.L_meta_1386.ofFnN]
      rfl
    rw [e27, e20, e26, e19, e25, e18, e24, e14, e15, e16, e17, e21, e22, e23, i0, i1, i2, i3, i4, i5, i7, i8, i9, i10, i11, i13] at hz2
    simp only [Bool.and_eq_true, Bool.or_eq_true] at hz2
    rcases hz2 with ⟨(((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩), (((⟨g1, g2⟩ | ⟨g1, g2⟩) | ⟨g1, g2⟩) | ⟨g1, g2⟩)⟩
    all_goals first
      | exact ⟨0, 0, by decide, h1, h2⟩
      | exact ⟨0, 0, by decide, h1, g2⟩
      | exact ⟨0, 0, by decide, g1, h2⟩
      | exact ⟨0, 0, by decide, g1, g2⟩
      | exact ⟨0, 4, by decide, h1, g2⟩
      | exact ⟨3, 0, by decide, g1, h2⟩
      | exact ⟨0, 6, by decide, h1, g2⟩
      | exact ⟨4, 1, by decide, g1, h2⟩
      | exact ⟨1, 0, by decide, h1, g2⟩
      | exact ⟨3, 2, by decide, g1, h2⟩
      | exact ⟨5, 2, by decide, g1, h2⟩
      | exact ⟨3, 3, by decide, g1, h2⟩
      | exact ⟨4, 3, by decide, g1, h2⟩
      | exact ⟨2, 6, by decide, h1, g2⟩
  subst hC
  refine ⟨?_, rfl, by decide +kernel, by decide +kernel, by decide +kernel, sound,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_⟩
  · intro g hg
    fin_cases hg <;> simp
  · intro l
    fin_cases l
    · exact ⟨(fun v : Fin (7 + 7) => decide (v = Fin.castAdd 7 2 ∨ v = Fin.natAdd 7 3)), by decide +kernel, by decide +kernel, by decide +kernel⟩
    · exact ⟨(fun v : Fin (7 + 7) => decide (v = Fin.castAdd 7 0 ∨ v = Fin.natAdd 7 1)), by decide +kernel, by decide +kernel, by decide +kernel⟩
    · exact ⟨(fun v : Fin (7 + 7) => decide (v = Fin.castAdd 7 0 ∨ v = Fin.natAdd 7 1)), by decide +kernel, by decide +kernel, by decide +kernel⟩
    · exact ⟨(fun v : Fin (7 + 7) => decide (v = Fin.castAdd 7 0 ∨ v = Fin.natAdd 7 1)), by decide +kernel, by decide +kernel, by decide +kernel⟩
    · exact ⟨(fun v : Fin (7 + 7) => decide (v = Fin.castAdd 7 1 ∨ v = Fin.natAdd 7 2)), by decide +kernel, by decide +kernel, by decide +kernel⟩
    · exact ⟨(fun v : Fin (7 + 7) => decide (v = Fin.castAdd 7 0 ∨ v = Fin.natAdd 7 1)), by decide +kernel, by decide +kernel, by decide +kernel⟩
    · exact ⟨(fun v : Fin (7 + 7) => decide (v = Fin.castAdd 7 1 ∨ v = Fin.natAdd 7 2)), by decide +kernel, by decide +kernel, by decide +kernel⟩
  · intro l
    fin_cases l
    · exact ⟨(fun v : Fin (7 + 7) => decide (v = Fin.castAdd 7 4 ∨ v = Fin.natAdd 7 0)), by decide +kernel, by decide +kernel, by decide +kernel⟩
    · exact ⟨(fun v : Fin (7 + 7) => decide (v = Fin.castAdd 7 3 ∨ v = Fin.natAdd 7 4)), by decide +kernel, by decide +kernel, by decide +kernel⟩
    · exact ⟨(fun v : Fin (7 + 7) => decide (v = Fin.castAdd 7 4 ∨ v = Fin.natAdd 7 0)), by decide +kernel, by decide +kernel, by decide +kernel⟩
    · exact ⟨(fun v : Fin (7 + 7) => decide (v = Fin.castAdd 7 5 ∨ v = Fin.natAdd 7 6)), by decide +kernel, by decide +kernel, by decide +kernel⟩
    · exact ⟨(fun v : Fin (7 + 7) => decide (v = Fin.castAdd 7 3 ∨ v = Fin.natAdd 7 4)), by decide +kernel, by decide +kernel, by decide +kernel⟩
    · exact ⟨(fun v : Fin (7 + 7) => decide (v = Fin.castAdd 7 3 ∨ v = Fin.natAdd 7 4)), by decide +kernel, by decide +kernel, by decide +kernel⟩
    · exact ⟨(fun v : Fin (7 + 7) => decide (v = Fin.castAdd 7 3 ∨ v = Fin.natAdd 7 4)), by decide +kernel, by decide +kernel, by decide +kernel⟩
