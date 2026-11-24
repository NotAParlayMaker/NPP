import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5399

open PEqualNP.CircuitLowerBounds

-- Appending folds keep their prefix.
theorem fold_getD {α : Type} (h : List Bool → α → Bool) (gs : List α) (w : List Bool) (i : ℕ)
    (hi : i < w.length) :
    (gs.foldl (fun d g => d ++ [h d g]) w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g rest ih =>
    rw [List.foldl_cons, ih _ (by simp; omega)]
    exact List.getD_append _ _ _ _ hi

theorem fold_length {α : Type} (h : List Bool → α → Bool) (gs : List α) (w : List Bool) :
    (gs.foldl (fun d g => d ++ [h d g]) w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g rest ih => rw [List.foldl_cons, ih]; simp; omega

theorem getD_snoc_eq (w : List Bool) (b : Bool) : (w ++ [b]).getD w.length false = b := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_snoc_big (w : List Bool) (b : Bool) (i : ℕ) (hi : w.length < i) :
    (w ++ [b]).getD i false = false := by
  apply List.getD_eq_default
  simp; omega

theorem getD_big (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false :=
  List.getD_eq_default _ _ hi

-- Wires of a circuit with only AND and OR gates grow with the input.
theorem mono_fold (gs : List Gate) (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (w1 w2 : List Bool) (hlen : w1.length = w2.length) (hle :∀ i, w1.getD i false = true → w2.getD i false = true) :
    ∀ i, (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w1).getD
        i false = true →
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w2).getD
        i false = true := by
  induction gs generalizing w1 w2 with
  | nil => exact hle
  | cons g rest ih =>
    simp only [List.foldl_cons]
    have hop := hg g List.mem_cons_self
    have hv : g.op.eval (g.inputs.map fun i => w1.getD i false) = true →
        g.op.eval (g.inputs.map fun i => w2.getD i false) = true := by
      rcases hop with hop | hop
      · rw [hop]
        simp only [GateOp.eval, List.all_eq_true, List.mem_map, id]
        intro h1 x hx
        obtain ⟨j, hj, rfl⟩ := hx
        exact hle j (h1 _ ⟨j, hj, rfl⟩)
      · rw [hop]
        simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
        rintro ⟨x, ⟨j, hj, rfl⟩, hx⟩
        exact ⟨_, ⟨j, hj, rfl⟩, hle j hx⟩
    apply ih (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg'))
    · simp; omega
    intro i hi
    by_cases h1 : i < w1.length
    · rw [List.getD_append _ _ _ _ (by omega)]
      rw [List.getD_append _ _ _ _ h1] at hi
      exact hle i hi
    · by_cases h3 : i = w1.length
      · subst h3
        rw [getD_snoc_eq] at hi
        rw [hlen, getD_snoc_eq]
        exact hv hi
      · rw [getD_snoc_big w1 _ i (by omega)] at hi
        exact absurd hi (by simp)

-- A wire not reached from the flipped inputs along paths avoiding wire X keeps its value,
-- if X keeps its value.
theorem agree_fold (X : ℕ) (gs : List Gate) (w1 w2 r : List Bool)
    (h1 : w1.length = r.length) (h2 : w2.length = r.length)
    (hinv : ∀ i, r.getD i false = false → i ≠ X → w1.getD i false = w2.getD i false)
    (hX : (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w1).getD
        X false =
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w2).getD
        X false) :
    ∀ i, (gs.foldl (fun d g => d ++ [decide (d.length ≠ X) && g.inputs.any fun i => d.getD i false])
        r).getD i false = false → i ≠ X →
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w1).getD
        i false =
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w2).getD
        i false := by
  induction gs generalizing w1 w2 r with
  | nil => exact hinv
  | cons g rest ih =>
    simp only [List.foldl_cons] at hX ⊢
    -- the value of wire X now
    have hXnow : w1.getD X false = w2.getD X false := by
      by_cases hXl : X < w1.length
      · have e1 := fold_getD (fun w g => g.op.eval (g.inputs.map fun i => w.getD i false)) rest
          (w1 ++ [g.op.eval (g.inputs.map fun i => w1.getD i false)]) X (by simp; omega)
        have e2 := fold_getD (fun w g => g.op.eval (g.inputs.map fun i => w.getD i false)) rest
          (w2 ++ [g.op.eval (g.inputs.map fun i => w2.getD i false)]) X (by simp; omega)
        rw [e1, e2, List.getD_append _ _ _ _ hXl, List.getD_append _ _ _ _ (by omega)] at hX
        exact hX
      · rw [getD_big w1 X (by omega), getD_big w2 X (by omega)]
    apply ih _ _ _ (by simp; omega) (by simp; omega) _ hX
    intro i hi hiX
    by_cases hl : i < r.length
    · rw [List.getD_append _ _ _ _ hl] at hi
      rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
      exact hinv i hi hiX
    · by_cases he : i = r.length
      · subst he
        rw [getD_snoc_eq] at hi
        rw [← h1, getD_snoc_eq, show w1.length = w2.length by omega, getD_snoc_eq]
        have hne : decide (r.length ≠ X) = true := by simpa using hiX
        rw [hne, Bool.true_and, Bool.eq_false_iff] at hi
        have hall : ∀ j ∈ g.inputs, w1.getD j false = w2.getD j false := by
          intro j hj
          by_cases hjX : j = X
          · subst hjX; exact hXnow
          · apply hinv j _ hjX
            by_contra hc
            apply hi
            exact List.any_eq_true.mpr ⟨j, hj, by simpa using hc⟩
        congr 1
        exact List.map_congr_left hall
      · rw [getD_snoc_big r _ i (by omega)] at hi
        rw [getD_snoc_big w1 _ i (by omega), getD_snoc_big w2 _ i (by omega)]

theorem ofFn_getD {n : ℕ} (f : Fin n → Bool) (i : ℕ) :
    (List.ofFn f).getD i false = if h : i < n then f ⟨i, h⟩ else false := by
  split_ifs with h
  · simp [List.getD_eq_getElem?_getD, h]
  · exact List.getD_eq_default _ _ (by simp; omega)

end PEqualNP.Outside.L_meta_5399

open PEqualNP.Outside.L_meta_5399 in
theorem PEqualNP.Outside.L_meta_5399 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (a c : Fin n) (X : ℕ), PEqualNP.ReadK.AndOrFanInTwo C → PEqualNP.MetaComplexity.NestedCover.ReadsBack n C → PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ → G.Adj a c → (C.gates.foldl (fun (d : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) => d ++ [decide (d.length ≠ X) && g.inputs.any fun i => d.getD i false]) (List.ofFn fun i : Fin n => decide (i = a ∧ i.val ≠ X))).getD C.output false = false → ∀ J : Finset (Fin n), (∀ u ∈ J, ∀ v ∈ J, ¬ G.Adj u v) → c ∈ J → PEqualNP.CleanedNonEdge.wireVal n C X (PEqualNP.ReadK.setInput J) = false ∧ PEqualNP.CleanedNonEdge.wireVal n C X (PEqualNP.ReadK.setInput (insert a J)) = true := by
  intro n G _ C a c X hC _ hf hac hcut J hJ hc
  have hac' : a ≠ c := G.ne_of_adj hac
  -- the output at J and at J with a
  have hlo : PEqualNP.MetaComplexity.circuitFun n C (PEqualNP.ReadK.setInput J) = false := by
    rw [hf]
    simp only [PEqualNP.MetaComplexity.NestedCover.graphFun, PEqualNP.ReadK.setInput]
    simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or,
      decide_eq_false_iff_not, not_exists, not_and, decide_eq_true_eq]
    intro u v huv hu hv
    exact hJ u hu v hv huv
  have hhi : PEqualNP.MetaComplexity.circuitFun n C (PEqualNP.ReadK.setInput (insert a J)) =
      true := by
    rw [hf]
    simp only [PEqualNP.MetaComplexity.NestedCover.graphFun, PEqualNP.ReadK.setInput]
    simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or,
      decide_eq_true_eq]
    exact ⟨a, c, hac, by simp, by simp [hc]⟩
  -- the two wire lists
  have hdiff : PEqualNP.CleanedNonEdge.wireVal n C X (PEqualNP.ReadK.setInput J) ≠
      PEqualNP.CleanedNonEdge.wireVal n C X (PEqualNP.ReadK.setInput (insert a J)) := by
    intro hX
    have hout := agree_fold X C.gates (List.ofFn (PEqualNP.ReadK.setInput J))
      (List.ofFn (PEqualNP.ReadK.setInput (insert a J)))
      (List.ofFn fun i : Fin n => decide (i = a ∧ i.val ≠ X)) (by simp) (by simp) (by
        intro i hi hiX
        rw [ofFn_getD, ofFn_getD]
        rw [ofFn_getD] at hi
        split_ifs at hi ⊢ with h
        · have hia : (⟨i, h⟩ : Fin n) ≠ a := by
            intro hia
            rw [hia] at hi
            simp at hi
            apply hiX
            rw [← hi, ← hia]
          simp [PEqualNP.ReadK.setInput, Finset.mem_insert, hia]
        · rfl) hX C.output hcut
    have hsame : ∀ x : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n C x =
        PEqualNP.CleanedNonEdge.wireVal n C C.output x := fun x => rfl
    by_cases hoX : C.output = X
    · rw [hsame, hoX] at hhi hlo
      rw [hlo, hhi] at hX
      exact absurd hX (by simp)
    · have e := hout hoX
      rw [hsame] at hhi hlo
      simp only [PEqualNP.CleanedNonEdge.wireVal, PEqualNP.CircuitLowerBounds.Circuit.wires] at hhi hlo
      rw [hlo, hhi] at e
      exact absurd e (by simp)
  have hmono : PEqualNP.CleanedNonEdge.wireVal n C X (PEqualNP.ReadK.setInput J) = true →
      PEqualNP.CleanedNonEdge.wireVal n C X (PEqualNP.ReadK.setInput (insert a J)) = true := by
    apply mono_fold C.gates hC.1 _ _ (by simp)
    intro i hi
    rw [ofFn_getD] at hi ⊢
    split_ifs at hi ⊢ with h
    simp only [PEqualNP.ReadK.setInput, decide_eq_true_eq] at hi ⊢
    exact Finset.mem_insert_of_mem hi
  revert hmono hdiff
  generalize PEqualNP.CleanedNonEdge.wireVal n C X (PEqualNP.ReadK.setInput J) = p
  generalize PEqualNP.CleanedNonEdge.wireVal n C X (PEqualNP.ReadK.setInput (insert a J)) = q
  cases p <;> cases q <;> simp
