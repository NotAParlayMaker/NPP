import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1354_aux

open PEqualNP.CircuitLowerBounds

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def fm (n c i : ℕ) : ℕ := if i < n then i else if i = n then c else i - 1

def remap (n c : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (fm n c)⟩

theorem getD_big (l : List Bool) (i : ℕ) (h : l.length ≤ i) : l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem getD_app_lt (l l' : List Bool) (i : ℕ) (h : i < l.length) :
    (l ++ l').getD i false = l.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_app_ge (l l' : List Bool) (i : ℕ) (h : l.length ≤ i) :
    (l ++ l').getD i false = l'.getD (i - l.length) false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

theorem fold_rel (n c : ℕ) (gs : List Gate) : ∀ (w w' : List Bool),
    w'.length + 1 = w.length → n ≤ w'.length → w'.length + gs.length ≤ c →
    (∀ i, w.getD i false = w'.getD (fm n c i) false) →
    ∀ i, (gs.foldl stp w).getD i false =
      ((gs.map (remap n c)).foldl stp w').getD (fm n c i) false := by
  induction gs with
  | nil =>
    intro w w' _ _ _ hB i
    simpa using hB i
  | cons g gs ih =>
    intro w w' hA hD hC hB
    simp only [List.foldl_cons, List.map_cons]
    have hv : (remap n c g).op.eval ((remap n c g).inputs.map fun i => w'.getD i false) =
        g.op.eval (g.inputs.map fun i => w.getD i false) := by
      simp only [remap, List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      simp only [Function.comp_apply]
      exact (hB i).symm
    have hst : stp w' (remap n c g) = w' ++ [g.op.eval (g.inputs.map fun i => w.getD i false)] := by
      simp only [stp, hv]
    have hst2 : stp w g = w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)] := rfl
    rw [hst, hst2]
    generalize g.op.eval (g.inputs.map fun i => w.getD i false) = v
    simp only [List.length_cons] at hC
    apply ih
    · simp [hA]
    · simp; omega
    · simp; omega
    · intro i
      by_cases h1 : i < n
      · have hf : fm n c i = i := by simp [fm, h1]
        have hb := hB i
        rw [hf] at hb ⊢
        rw [getD_app_lt w _ i (by omega), getD_app_lt w' _ i (by omega)]
        exact hb
      · by_cases h2 : i = n
        · have hf : fm n c i = c := by simp [fm, h2]
          have hb := hB i
          rw [hf] at hb ⊢
          rw [getD_app_lt w _ i (by omega)]
          rw [hb, getD_big w' c (by omega), getD_big (w' ++ [v]) c (by simp; omega)]
        · have hf : fm n c i = i - 1 := by simp [fm, h1, h2]
          have hb := hB i
          rw [hf] at hb ⊢
          by_cases h3 : i < w.length
          · rw [getD_app_lt w _ i h3, getD_app_lt w' _ (i - 1) (by omega)]
            exact hb
          · by_cases h4 : i = w.length
            · rw [getD_app_ge w _ i (by omega), getD_app_ge w' _ (i - 1) (by omega)]
              have e1 : i - w.length = 0 := by omega
              have e2 : i - 1 - w'.length = 0 := by omega
              rw [e1, e2]
            · rw [getD_big (w ++ [v]) i (by simp; omega),
                getD_big (w' ++ [v]) (i - 1) (by simp; omega)]

end PEqualNP.Outside.L_meta_1354_aux

open PEqualNP.Outside.L_meta_1354_aux

theorem PEqualNP.Outside.L_meta_1354 : ∀ (n : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate), ∃ gates' : List PEqualNP.CircuitLowerBounds.Gate, gates'.map PEqualNP.CircuitLowerBounds.Gate.op = gates.map PEqualNP.CircuitLowerBounds.Gate.op ∧ gates'.map (fun g => g.inputs.length) = gates.map (fun g => g.inputs.length) ∧ ∀ (j : ℕ) (x : Fin n → Bool), j < gates.length → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', n + j⟩ (List.ofFn x) = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + 1 + j⟩ (List.ofFn x ++ [false]) := by
  intro n gates
  refine ⟨gates.map (remap n (n + gates.length)), ?_, ?_, ?_⟩
  · simp [List.map_map, remap, Function.comp_def]
  · simp [List.map_map, remap, Function.comp_def]
  · intro j x hj
    have hB : ∀ i, (List.ofFn x ++ [false]).getD i false =
        (List.ofFn x).getD (fm n (n + gates.length) i) false := by
      intro i
      by_cases h1 : i < n
      · have hf : fm n (n + gates.length) i = i := by simp [fm, h1]
        rw [hf, getD_app_lt _ _ i (by simp [h1])]
      · by_cases h2 : i = n
        · have hf : fm n (n + gates.length) i = n + gates.length := by simp [fm, h2]
          rw [hf, getD_big (List.ofFn x) _ (by simp), getD_app_ge _ _ i (by simp; omega)]
          simp [h2]
        · have hf : fm n (n + gates.length) i = i - 1 := by simp [fm, h1, h2]
          rw [hf, getD_big (List.ofFn x) _ (by simp; omega),
            getD_app_ge _ _ i (by simp; omega)]
          have : 1 ≤ i - n := by omega
          rw [getD_big [false] _ (by simpa using this)]
    have key := fold_rel n (n + gates.length) gates (List.ofFn x ++ [false]) (List.ofFn x)
      (by simp) (by simp) (by simp) hB (n + 1 + j)
    have hf : fm n (n + gates.length) (n + 1 + j) = n + j := by
      unfold fm
      split_ifs <;> omega
    rw [hf] at key
    exact key.symm
