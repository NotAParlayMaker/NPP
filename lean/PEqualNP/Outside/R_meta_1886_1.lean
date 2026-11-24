import Mathlib
import PEqualNP.Defs

-- The relabeling of the ten inputs is removed: every gate reads wire p i instead of input wire i.
-- No bijectivity is needed. What is left is one plain statement per first-gate operation.
theorem PEqualNP.Outside.R_meta_1886_1
    (firstAnd : ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D → D.size ≤ 18 →
      ∃ x : Fin 10 → Bool, D.eval (List.ofFn x ++ [x 0 && x 1]) ≠
        (fun x : Fin 10 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)) x)
    (firstOr : ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D → D.size ≤ 18 →
      ∃ x : Fin 10 → Bool, D.eval (List.ofFn x ++ [x 0 || x 1]) ≠
        (fun x : Fin 10 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)) x)
    :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (10 : ℕ) → Fin (10 : ℕ)) (x3 : Bool), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) → ∃ (x6 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn (x6 ∘ x2) ++ [if x3 = Bool.true then x6 (0 : Fin (10 : ℕ)) && x6 (1 : Fin (10 : ℕ)) else x6 (0 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ))]) ≠ (fun (x7 : Fin (10 : ℕ) → Bool) => x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (2 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (3 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (4 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (0 : Fin (10 : ℕ)) || x7 (0 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (5 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (7 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (9 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (6 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (8 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ))) x6 := by
  intro C p b hC hs
  -- Input wire i (below ten) is read as wire p i; every other wire keeps its index.
  let r : ℕ → ℕ := fun i => if h : i < 10 then ((p ⟨i, h⟩ : Fin 10) : ℕ) else i
  let D : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨C.gates.map (fun g => ⟨g.op, g.inputs.map r⟩), r C.output⟩
  have hD : PEqualNP.MetaComplexity.FanInTwo D := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
    obtain ⟨h1, h2⟩ := hC g0 hg0
    exact ⟨h1, by simpa using h2⟩
  have hsD : D.size ≤ 18 := by
    simpa [D, PEqualNP.CircuitLowerBounds.Circuit.size] using hs
  have snoc : ∀ (l : List Bool) (v : Bool) (i : ℕ),
      (l ++ [v]).getD i false = if i < l.length then l.getD i false
        else if i = l.length then v else false := by
    intro l v i
    split_ifs with h1 h2
    · exact List.getD_append _ _ _ _ h1
    · subst h2; simp
    · rw [List.getD_append_right _ _ _ _ (by omega)]
      obtain ⟨k, hk⟩ : ∃ k, i - l.length = k + 1 := ⟨i - l.length - 1, by omega⟩
      rw [hk]; simp
  -- The relabeled circuit sees on wire r i what the original sees on wire i.
  have step : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w' w : List Bool),
      w'.length = w.length → 10 ≤ w.length →
      (∀ i, w'.getD (r i) false = w.getD i false) →
      ∀ i, ((gs.map (fun g => (⟨g.op, g.inputs.map r⟩ : PEqualNP.CircuitLowerBounds.Gate))).foldl
          (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w').getD (r i) false =
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD i
          false := by
    intro gs
    induction gs with
    | nil => intro w' w _ _ hinv; exact hinv
    | cons g gs ih =>
      intro w' w hlen h10 hinv
      simp only [List.map_cons, List.foldl_cons]
      have hv : g.op.eval ((g.inputs.map r).map fun i => w'.getD i false) =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        rw [List.map_map]
        congr 1
        exact List.map_congr_left (fun i _ => hinv i)
      rw [hv]
      apply ih
      · simp [hlen]
      · simp; omega
      · intro i
        rw [snoc, snoc, hlen]
        by_cases hi : i < 10
        · have hr : r i = ((p ⟨i, hi⟩ : Fin 10) : ℕ) := by simp [r, hi]
          have hpi : ((p ⟨i, hi⟩ : Fin 10) : ℕ) < w.length := by omega
          rw [hr]
          simp only [hpi, show i < w.length by omega, ite_true]
          rw [← hr]
          exact hinv i
        · have hr : r i = i := by simp [r, hi]
          have hi' := hinv i
          rw [hr] at hi' ⊢
          split_ifs <;> first | exact hi' | rfl
  have key : ∀ (x : Fin 10 → Bool) (e : Bool),
      D.eval (List.ofFn x ++ [e]) = C.eval (List.ofFn (x ∘ p) ++ [e]) := by
    intro x e
    apply step C.gates
    · simp
    · simp
    · intro i
      by_cases hi : i < 10
      · have hr : r i = ((p ⟨i, hi⟩ : Fin 10) : ℕ) := by simp [r, hi]
        rw [hr, List.getD_append _ _ _ _ (by simp), List.getD_append _ _ _ _ (by simpa using hi),
          List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simpa using hi)]
        simp only [List.getElem_ofFn, Function.comp_apply, Fin.eta]
      · have hr : r i = i := by simp [r, hi]
        rw [hr, List.getD_append_right _ _ _ _ (by simp; omega),
          List.getD_append_right _ _ _ _ (by simp; omega)]
        simp
  cases b with
  | true =>
    obtain ⟨x, hx⟩ := firstAnd D hD hsD
    refine ⟨x, ?_⟩
    change C.eval (List.ofFn (x ∘ p) ++ [x 0 && x 1]) ≠ _
    rw [← key]
    exact hx
  | false =>
    obtain ⟨x, hx⟩ := firstOr D hD hsD
    refine ⟨x, ?_⟩
    change C.eval (List.ofFn (x ∘ p) ++ [x 0 || x 1]) ≠ _
    rw [← key]
    exact hx
