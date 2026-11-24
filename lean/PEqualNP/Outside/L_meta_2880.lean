import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.L_meta_2880 :
  ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → ∀ (x4 : (Fin x1 → Bool) → Prop), (∀ (x5 : Fin x1 → Bool), Minimal x4 x5 → x2.eval (List.ofFn x5) = Bool.true) → (∀ (x6 : Fin x1 → Bool), Maximal (fun (x7 : Fin x1 → Bool) => ¬x4 x7) x6 → x2.eval (List.ofFn x6) = Bool.false) → ∀ (x7 : Fin x1 → Bool), x2.eval (List.ofFn x7) = Bool.true ↔ x4 x7 := by
  classical
  intro n C hC P accept reject x
  let advance (w : List Bool) (g : Gate) :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let ordered (a b : List Bool) := a.length = b.length ∧
    ∀ i, a.getD i false ≤ b.getD i false
  have extend (a b : List Bool) (h : ordered a b) (u v : Bool) (huv : u ≤ v) :
      ordered (a ++ [u]) (b ++ [v]) := by
    refine ⟨by simp only [List.length_append, List.length_singleton, h.1], ?_⟩
    intro i
    by_cases hi : i < a.length
    · have hj : i < b.length := h.1 ▸ hi
      simpa only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi,
        List.getElem?_append_left hj] using h.2 i
    · have hj : b.length ≤ i := h.1 ▸ Nat.le_of_not_lt hi
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_of_not_lt hi),
        List.getElem?_append_right hj, ← h.1]
      cases i - a.length
      · simpa using huv
      · simp
  have gateMono (g : Gate) (hop : g.op = .and ∨ g.op = .or)
      (a b : List Bool) (h : ordered a b) : ordered (advance a g) (advance b g) := by
    apply extend a b h
    apply Bool.le_iff_imp.mpr
    rcases hop with hop | hop
    · rw [hop]
      change (g.inputs.map (fun i => a.getD i false)).all id = true →
        (g.inputs.map (fun i => b.getD i false)).all id = true
      intro ha
      apply List.all_eq_true.mpr
      intro t ht
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ht
      exact (Bool.le_iff_imp.mp (h.2 i))
        (List.all_eq_true.mp ha _ (List.mem_map.mpr ⟨i, hi, rfl⟩))
    · rw [hop]
      change (g.inputs.map (fun i => a.getD i false)).any id = true →
        (g.inputs.map (fun i => b.getD i false)).any id = true
      intro ha
      obtain ⟨t, ht, htrue⟩ := List.any_eq_true.mp ha
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ht
      exact List.any_eq_true.mpr
        ⟨_, List.mem_map.mpr ⟨i, hi, rfl⟩, Bool.le_iff_imp.mp (h.2 i) htrue⟩
  have foldMono (gs : List Gate) (a b : List Bool)
      (h : ordered a b) (ops : ∀ g ∈ gs, g.op = .and ∨ g.op = .or) :
      ordered (gs.foldl advance a) (gs.foldl advance b) := by
    induction gs generalizing a b with
    | nil => exact h
    | cons g gs ih =>
      exact ih _ _ (gateMono g (ops g (by simp)) a b h)
        (fun v hv => ops v (List.mem_cons_of_mem g hv))
  have evalMono : Monotone (fun y : Fin n → Bool => C.eval (List.ofFn y)) := by
    intro a b hab
    have init : ordered (List.ofFn a) (List.ofFn b) := by
      refine ⟨by simp, ?_⟩
      intro i
      by_cases hi : i < n
      · have ha : i < (List.ofFn a).length := by simpa using hi
        have hb : i < (List.ofFn b).length := by simpa using hi
        simpa only [List.getD_eq_getElem _ _ ha, List.getD_eq_getElem _ _ hb,
          List.getElem_ofFn] using hab ⟨i, hi⟩
      · have ha : (List.ofFn a).length ≤ i := by simpa using Nat.le_of_not_lt hi
        have hb : (List.ofFn b).length ≤ i := by simpa using Nat.le_of_not_lt hi
        simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none ha,
          List.getElem?_eq_none hb, Option.getD_none, le_refl]
    exact (foldMono C.gates _ _ init (fun g hg => by
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using (hC g hg).1)).2 C.output
  constructor
  · intro hx
    by_contra hPx
    let S : Set (Fin n → Bool) := {y | ¬ P y ∧ x ≤ y}
    obtain ⟨y, hy⟩ := (Set.toFinite S).exists_maximal ⟨x, hPx, le_rfl⟩
    have hyGlobal : Maximal (fun y => ¬ P y) y :=
      ⟨hy.1.1, fun z hz hyz => hy.2 ⟨hz, hy.1.2.trans hyz⟩ hyz⟩
    have hyTrue : C.eval (List.ofFn y) = true :=
      (Bool.le_iff_imp.mp (evalMono hy.1.2)) hx
    rw [reject y hyGlobal] at hyTrue
    cases hyTrue
  · intro hPx
    let S : Set (Fin n → Bool) := {y | P y ∧ y ≤ x}
    obtain ⟨y, hy⟩ := (Set.toFinite S).exists_minimal ⟨x, hPx, le_rfl⟩
    have hyGlobal : Minimal P y :=
      ⟨hy.1.1, fun z hz hzy => hy.2 ⟨hz, hzy.trans hy.1.2⟩ hzy⟩
    exact (Bool.le_iff_imp.mp (evalMono hy.1.2)) (accept y hyGlobal)
