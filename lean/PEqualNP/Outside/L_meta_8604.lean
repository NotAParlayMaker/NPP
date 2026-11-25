import Mathlib
import PEqualNP.Defs

-- Regrouping AND(AND(a, rest), b) as AND(AND(a, b), rest) does not change any wire other than
-- the inner gate, which only the outer gate reads. The getD_snoc helper is taken from
-- L-meta-4069.
namespace PEqualNP.Outside.L_meta_8604

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def W (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = W C.gates x := rfl

lemma W_cons (g : Gate) (gs : List Gate) (w : List Bool) : W (g :: gs) w = W gs (step w g) := rfl

lemma W_append (a b : List Gate) (w : List Bool) : W (a ++ b) w = W b (W a w) := by
  simp [W, List.foldl_append]

lemma step_length (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

lemma W_length : ∀ (gs : List Gate) (w : List Bool), (W gs w).length = w.length + gs.length
  | [], w => by simp [W]
  | g :: gs, w => by rw [W_cons, W_length gs, step_length]; simp; omega

lemma getD_snoc (l : List Bool) (v : Bool) (i : Nat) :
    (l ++ [v]).getD i false =
      if i < l.length then l.getD i false else if i = l.length then v else false := by
  split_ifs with h1 h2
  · exact List.getD_append _ _ _ _ h1
  · subst h2
    rw [List.getD_append_right _ _ _ _ (le_refl _)]
    simp
  · rw [List.getD_eq_default]
    simp
    omega

lemma W_prefix : ∀ (gs : List Gate) (w : List Bool) (i : ℕ), i < w.length →
    (W gs w).getD i false = w.getD i false
  | [], _, _, _ => rfl
  | g :: gs, w, i, h => by
    rw [W_cons, W_prefix gs _ i (by rw [step_length]; omega)]
    simp only [step]
    rw [getD_snoc, if_pos h]

def Ag (k : ℕ) (l1 l2 : List Bool) : Prop :=
  l1.length = l2.length ∧ ∀ i, i ≠ k → l1.getD i false = l2.getD i false

lemma ag_snoc {k : ℕ} {l1 l2 : List Bool} {v1 v2 : Bool} (hk : k < l1.length) (h : Ag k l1 l2)
    (hv : v1 = v2) : Ag k (l1 ++ [v1]) (l2 ++ [v2]) := by
  refine ⟨by simp [h.1], fun i hi => ?_⟩
  rw [getD_snoc, getD_snoc, ← h.1]
  split_ifs with h1 h2
  · exact h.2 i hi
  · exact hv
  · rfl

lemma ag_last (l : List Bool) (v1 v2 : Bool) : Ag l.length (l ++ [v1]) (l ++ [v2]) := by
  refine ⟨by simp, fun i hi => ?_⟩
  rw [getD_snoc, getD_snoc]
  simp [hi]

lemma step_ag {k : ℕ} {l1 l2 : List Bool} {g : Gate} (hk : k < l1.length) (h : Ag k l1 l2)
    (hg : k ∉ g.inputs) : Ag k (step l1 g) (step l2 g) := by
  unfold step
  apply ag_snoc hk h
  congr 1
  apply List.map_congr_left
  intro i hi
  exact h.2 i (fun e => hg (e ▸ hi))

lemma W_ag : ∀ (gs : List Gate) {k : ℕ} {l1 l2 : List Bool}, (∀ g ∈ gs, k ∉ g.inputs) →
    k < l1.length → Ag k l1 l2 → Ag k (W gs l1) (W gs l2)
  | [], _, _, _, _, _, h => h
  | g :: gs, k, l1, l2, hg, hk, h => by
    rw [W_cons, W_cons]
    exact W_ag gs (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg'))
      (by rw [step_length]; omega) (step_ag hk h (hg g (by simp)))

lemma all_perm (f : ℕ → Bool) (l m : List ℕ) (hl : l.Perm m) :
    (l.map f).all id = (m.map f).all id := by
  rw [Bool.eq_iff_iff]
  simp only [List.all_eq_true, List.mem_map, id]
  constructor
  · rintro h b ⟨a, ha, rfl⟩
    exact h _ ⟨a, hl.mem_iff.mpr ha, rfl⟩
  · rintro h b ⟨a, ha, rfl⟩
    exact h _ ⟨a, hl.mem_iff.mp ha, rfl⟩

end PEqualNP.Outside.L_meta_8604

open PEqualNP.Outside.L_meta_8604 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_8604 : ∀ (x1 : ℕ) (x2 x3 x4 : List PEqualNP.CircuitLowerBounds.Gate) (x5 x6 : List ℕ) (x7 x8 : ℕ),   have x9 : ℕ := x1 + x2.length;   have x10 : List ℕ → List ℕ → PEqualNP.CircuitLowerBounds.Circuit := fun (x10 x11 : List ℕ) => { gates := x2 ++ { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := x10 : PEqualNP.CircuitLowerBounds.Gate } :: (x3 ++ { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := x11 : PEqualNP.CircuitLowerBounds.Gate } :: x4), output := x8 : PEqualNP.CircuitLowerBounds.Circuit };   x6.Perm [x9, x7] → x7 < x9 → (∀ x13 ∈ x5, x13 < x9) → x8 ≠ x9 → (∀ x15 ∈ x3 ++ x4, x9 ∉ x15.inputs) → PEqualNP.MetaComplexity.circuitFun x1 (x10 (List.take (1 : ℕ) x5 ++ [x7]) (x9 :: List.drop (1 : ℕ) x5)) = PEqualNP.MetaComplexity.circuitFun x1 (x10 x5 x6) := by
  dsimp only
  intro n g2 g3 g4 x5 x6 x7 x8 hperm h7 h5 h8 hno
  funext xv
  simp only [PEqualNP.MetaComplexity.circuitFun, Circuit.eval, wires_eq, W_append, W_cons]
  have hlen : (W g2 (List.ofFn xv)).length = n + g2.length := by
    rw [W_length, List.length_ofFn]
  generalize W g2 (List.ofFn xv) = w0 at hlen ⊢
  generalize hk : n + g2.length = k at hlen h7 h5 h8 hno hperm ⊢
  have hu : ∀ l : List ℕ, k < (step w0 ⟨GateOp.and, l⟩).length := by
    intro l; rw [step_length]; omega
  have hA : Ag k (step w0 ⟨GateOp.and, x5.take 1 ++ [x7]⟩) (step w0 ⟨GateOp.and, x5⟩) := by
    unfold step; rw [← hlen]; exact ag_last _ _ _
  have hno3 : ∀ g ∈ g3, k ∉ g.inputs := fun g hg => hno g (List.mem_append_left _ hg)
  have hno4 : ∀ g ∈ g4, k ∉ g.inputs := fun g hg => hno g (List.mem_append_right _ hg)
  have hv := W_ag g3 hno3 (hu _) hA
  have vk : ∀ l : List ℕ, (W g3 (step w0 ⟨GateOp.and, l⟩)).getD k false
      = (l.map fun i => w0.getD i false).all id := by
    intro l
    rw [W_prefix _ _ _ (hu l)]
    simp only [step]
    rw [getD_snoc, if_neg (by omega), if_pos hlen.symm]
    rfl
  have vlt : ∀ (l : List ℕ) (i : ℕ), i < k → (W g3 (step w0 ⟨GateOp.and, l⟩)).getD i false
      = w0.getD i false := by
    intro l i hi
    rw [W_prefix _ _ _ (by have := hu l; omega)]
    simp only [step]
    rw [getD_snoc, if_pos (by omega)]
  have hlenv : k < (W g3 (step w0 ⟨GateOp.and, x5.take 1 ++ [x7]⟩)).length := by
    rw [W_length]; have := hu (x5.take 1 ++ [x7]); omega
  have hB := W_ag g4 hno4 (by rw [step_length]; omega)
    (step_ag (g := ⟨GateOp.and, []⟩) hlenv hv (by simp))
  -- the two outer gates agree
  have hval : GateOp.and.eval ((k :: x5.drop 1).map fun i =>
        (W g3 (step w0 ⟨GateOp.and, x5.take 1 ++ [x7]⟩)).getD i false)
      = GateOp.and.eval (x6.map fun i => (W g3 (step w0 ⟨GateOp.and, x5⟩)).getD i false) := by
    simp only [GateOp.eval]
    rw [all_perm _ x6 [k, x7] hperm]
    simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id, Bool.and_true]
    rw [vk, vk, vlt _ _ h7]
    have hd : (x5.drop 1).map (fun i => (W g3 (step w0 ⟨GateOp.and, x5.take 1 ++ [x7]⟩)).getD i false)
        = (x5.drop 1).map (fun i => w0.getD i false) := by
      apply List.map_congr_left
      intro i hi
      exact vlt _ _ (h5 i (List.mem_of_mem_drop hi))
    rw [hd]
    have hs : x5.map (fun i => w0.getD i false)
        = (x5.take 1).map (fun i => w0.getD i false) ++ (x5.drop 1).map (fun i => w0.getD i false) := by
      rw [← List.map_append, List.take_append_drop]
    rw [hs]
    simp only [List.map_append, List.map_cons, List.map_nil, List.all_append, List.all_cons,
      List.all_nil, id, Bool.and_true]
    cases ((x5.take 1).map fun i => w0.getD i false).all id <;>
      cases ((x5.drop 1).map fun i => w0.getD i false).all id <;> cases w0.getD x7 false <;> rfl
  have hfin : Ag k
      (W g4 (step (W g3 (step w0 ⟨GateOp.and, x5.take 1 ++ [x7]⟩)) ⟨GateOp.and, k :: x5.drop 1⟩))
      (W g4 (step (W g3 (step w0 ⟨GateOp.and, x5⟩)) ⟨GateOp.and, x6⟩)) :=
    W_ag g4 hno4 (by rw [step_length]; omega) (ag_snoc hlenv hv hval)
  exact hfin.2 x8 h8
