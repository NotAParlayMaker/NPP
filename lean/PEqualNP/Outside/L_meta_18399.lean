import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18399_aux

open PEqualNP.CircuitLowerBounds

theorem getD_zip (w1 w2 : List Bool) (h : w1.length = w2.length) (i : ℕ) :
    (List.zipWith (fun a b => a || b) w1 w2).getD i false = (w1.getD i false || w2.getD i false) := by
  induction w1 generalizing w2 i with
  | nil => cases w2 <;> simp_all
  | cons a t ih =>
    cases w2 with
    | nil => simp at h
    | cons b s =>
      cases i with
      | zero => simp
      | succ i => simp only [List.zipWith_cons_cons, List.getD_cons_succ]; exact ih s (by simpa using h) i

theorem any_or (l : List ℕ) (f g : ℕ → Bool) :
    (l.map fun i => f i || g i).any id = ((l.map f).any id || (l.map g).any id) := by
  induction l with
  | nil => simp
  | cons a t ih => simp only [List.map_cons, List.any_cons, ih, id]; cases f a <;> cases g a <;> simp

theorem fold_hom (gs : List Gate) (hg : ∀ g ∈ gs, g.op = GateOp.or) (w1 w2 : List Bool)
    (h : w1.length = w2.length) :
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (List.zipWith (fun a b => a || b) w1 w2) =
    List.zipWith (fun a b => a || b)
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w1)
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w2) := by
  induction gs generalizing w1 w2 with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hop : g.op = GateOp.or := hg g (by simp)
    have e : (List.zipWith (fun a b => a || b) w1 w2 ++
        [g.op.eval (g.inputs.map fun i => (List.zipWith (fun a b => a || b) w1 w2).getD i false)]) =
        List.zipWith (fun a b => a || b) (w1 ++ [g.op.eval (g.inputs.map fun i => w1.getD i false)])
          (w2 ++ [g.op.eval (g.inputs.map fun i => w2.getD i false)]) := by
      rw [List.zipWith_append h]
      simp only [getD_zip w1 w2 h, hop, GateOp.eval, any_or, List.zipWith_cons_cons, List.zipWith_nil_left]
    rw [e]
    exact ih (fun g' hg' => hg g' (by simp [hg'])) _ _ (by simp [h])

theorem len_fold (gs : List Gate) (w : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).length =
      w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp only [List.foldl_cons, ih, List.length_append, List.length_cons]; simp; omega

theorem eval_hom (C : Circuit) (hg : ∀ g ∈ C.gates, g.op = GateOp.or) {n : ℕ} (a b : Fin n → Bool) :
    C.eval (List.ofFn fun i => a i || b i) = (C.eval (List.ofFn a) || C.eval (List.ofFn b)) := by
  have hz : (List.ofFn fun i => a i || b i) = List.zipWith (fun a b => a || b) (List.ofFn a) (List.ofFn b) := by
    apply List.ext_getElem <;> simp
  unfold Circuit.eval Circuit.wires
  rw [hz, fold_hom C.gates hg _ _ (by simp), getD_zip]
  rw [len_fold, len_fold]; simp

end PEqualNP.Outside.L_meta_18399_aux

open PEqualNP.Outside.L_meta_18399_aux in
theorem PEqualNP.Outside.L_meta_18399 : ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x5 x6 : Fin x1) (x7 x8 : Fin x2), x5 ≠ x6 → x7 ≠ x8 → ¬((x5, x7) ∈ x3 ∧ (x5, x8) ∈ x3 ∧ (x6, x7) ∈ x3 ∧ (x6, x8) ∈ x3)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x4 → (∀ (x7 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x4 x7 = Decidable.decide (∃ (x8 : Fin x1) (x9 : Fin x2), (x8, x9) ∈ x3 ∧ x7 (Fin.castAdd x2 x8) = Bool.true ∧ x7 (Fin.natAdd x1 x9) = Bool.true)) → (¬∃ (x8 : Fin x4.gates.length), (x4.gates.get x8).op = PEqualNP.CircuitLowerBounds.GateOp.and) → ∃ (x9 : Finset (Fin x1)) (x10 : Finset (Fin x2)), (∀ x11 ∈ x3, x11.1 ∈ x9 ∨ x11.2 ∈ x10) ∧ x3.card + x9.card + x10.card ≤ x4.size + (1 : ℕ) := by
  intro a b E C _ hao hf hna
  have hg : ∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.or := by
    intro g hgm
    have h1 := hao.1 g hgm
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hgm
    rcases h1 with h1 | h1
    · exact absurd ⟨i, h1⟩ hna
    · exact h1
  have hE : E = ∅ := by
    by_contra hne
    obtain ⟨⟨i, j⟩, hij⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    have h1 := hf (fun k => decide (k = Fin.castAdd b i) || decide (k = Fin.natAdd a j))
    have h2 := hf (fun k => decide (k = Fin.castAdd b i))
    have h3 := hf (fun k => decide (k = Fin.natAdd a j))
    unfold PEqualNP.MetaComplexity.circuitFun at h1 h2 h3
    rw [eval_hom C hg, h2, h3] at h1
    have t1 : (∃ (x8 : Fin a) (x9 : Fin b), (x8, x9) ∈ E ∧ decide (Fin.castAdd b x8 = Fin.castAdd b i) = true ∧ decide (Fin.natAdd a x9 = Fin.castAdd b i) = true) = False := by
      simp only [decide_eq_true_eq, eq_iff_iff, iff_false]
      rintro ⟨x, y, -, -, h⟩
      have := congrArg Fin.val h; simp at this; omega
    have t2 : (∃ (x8 : Fin a) (x9 : Fin b), (x8, x9) ∈ E ∧ decide (Fin.castAdd b x8 = Fin.natAdd a j) = true ∧ decide (Fin.natAdd a x9 = Fin.natAdd a j) = true) = False := by
      simp only [decide_eq_true_eq, eq_iff_iff, iff_false]
      rintro ⟨x, y, -, h, -⟩
      have := congrArg Fin.val h; simp at this; omega
    simp only [t1, t2, decide_false, Bool.false_or] at h1
    have : (∃ (x8 : Fin a) (x9 : Fin b), (x8, x9) ∈ E ∧ (decide (Fin.castAdd b x8 = Fin.castAdd b i) || decide (Fin.castAdd b x8 = Fin.natAdd a j)) = true ∧ (decide (Fin.natAdd a x9 = Fin.castAdd b i) || decide (Fin.natAdd a x9 = Fin.natAdd a j)) = true) := ⟨i, j, hij, by simp, by simp⟩
    rw [eq_comm, decide_eq_false_iff_not] at h1
    exact h1 this
  subst hE
  exact ⟨∅, ∅, by simp, by simp⟩
