import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4934
open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega

theorem wf_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wf (g :: gs) w = wf gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

theorem getD_ofFn {n : ℕ} (f : Fin n → Bool) (i : Fin n) :
    (List.ofFn f).getD (i : ℕ) false = f i := by
  simp

def rgp (r : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map r⟩

theorem pkey (n : ℕ) (r : ℕ → ℕ) (hlt : ∀ v, v < n → r v < n) (hge : ∀ v, n ≤ v → r v = v) :
    ∀ (gs : List Gate) (U U' : List Bool), U.length = U'.length → n ≤ U.length →
      (∀ v, U'.getD v false = U.getD (r v) false) →
      ∀ v, (wf gs U').getD v false = (wf (gs.map (rgp r)) U).getD (r v) false := by
  intro gs
  induction gs with
  | nil => intro U U' _ _ h v; exact h v
  | cons g gs ih =>
    intro U U' hlen hn h v
    rw [List.map_cons, wf_cons, wf_cons]
    have hv : g.op.eval (g.inputs.map fun i => U'.getD i false)
        = (rgp r g).op.eval ((rgp r g).inputs.map fun i => U.getD i false) := by
      show _ = g.op.eval ((g.inputs.map r).map fun i => U.getD i false)
      rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      exact h i
    rw [← hv]
    refine ih _ _ (by simp [hlen]) (by simp; omega) ?_ v
    intro t
    rcases Nat.lt_trichotomy t U'.length with ht | ht | ht
    · have h1 : r t < U.length := by
        by_cases htn : t < n
        · have := hlt t htn; omega
        · rw [hge t (by omega)]; omega
      rw [getD_snoc_lt _ _ _ ht, getD_snoc_lt _ _ _ h1]
      exact h t
    · subst ht
      rw [hge _ (by omega), getD_snoc_eq, ← hlen, getD_snoc_eq]
    · rw [hge _ (by omega), getD_snoc_gt _ _ _ ht, getD_snoc_gt _ _ _ (by omega)]

def clipK (K : ℕ) (g : Gate) : Gate := { op := g.op, inputs := g.inputs.map (fun i => min i K) }

theorem clipK_get (K : ℕ) (X : List Bool) (hX : X.length ≤ K) (i : ℕ) :
    X.getD (min i K) false = X.getD i false := by
  by_cases h : i ≤ K
  · rw [Nat.min_eq_left h]
  · rw [Nat.min_eq_right (by omega), List.getD_eq_default _ _ hX,
      List.getD_eq_default _ _ (by omega)]

theorem clipKw (K : ℕ) : ∀ (gs : List Gate) (X : List Bool), X.length + gs.length ≤ K →
    wf (gs.map (clipK K)) X = wf gs X := by
  intro gs
  induction gs with
  | nil => intro X _; rfl
  | cons g gs ih =>
    intro X hX
    rw [List.length_cons] at hX
    have hv : (clipK K g).op.eval ((clipK K g).inputs.map fun i => X.getD i false)
        = g.op.eval (g.inputs.map fun i => X.getD i false) := by
      show g.op.eval ((g.inputs.map (fun i => min i K)).map fun i => X.getD i false) = _
      rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      exact clipK_get K X (by omega) i
    show wf (gs.map (clipK K)) (X ++ [(clipK K g).op.eval ((clipK K g).inputs.map fun i => X.getD i false)])
      = wf gs (X ++ [g.op.eval (g.inputs.map fun i => X.getD i false)])
    rw [hv]
    apply ih
    rw [List.length_append]
    simp
    omega

end PEqualNP.Outside.L_meta_4934

open PEqualNP.Outside.L_meta_4934 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_4934 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (10 : ℕ) → Fin (10 : ℕ)), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) → ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x5 ∧ x5.size = x1.size ∧ x5.output ≤ (29 : ℕ) ∧ (∀ x6 ∈ x5.gates, ∀ x8 ∈ x6.inputs, x8 ≤ (29 : ℕ)) ∧ ∀ (x6 : Fin (10 : ℕ) → Bool) (x7 : Bool), x5.eval (List.ofFn x6 ++ [x7]) = x1.eval (List.ofFn (x6 ∘ x2) ++ [x7]) := by
  intro C σ hF hsz
  have hsz' : C.gates.length ≤ 18 := hsz
  obtain ⟨r, hr⟩ : ∃ r : ℕ → ℕ, r = fun i => if h : i < 10 then ((σ ⟨i, h⟩ : Fin 10) : ℕ) else i := ⟨_, rfl⟩
  have hlt : ∀ v (h : v < 10), r v = ((σ ⟨v, h⟩ : Fin 10) : ℕ) := by
    intro v h; rw [hr]; simp [h]
  have hge : ∀ v, 10 ≤ v → r v = v := by
    intro v h; rw [hr]; simp [Nat.not_lt.mpr h]
  have hlt' : ∀ v, v < 10 → r v < 10 := by
    intro v h; rw [hlt v h]; exact (σ ⟨v, h⟩).isLt
  refine ⟨⟨(C.gates.map (rgp r)).map (clipK 29), min (r C.output) 29⟩, ?_, ?_, Nat.min_le_right _ _, ?_, ?_⟩
  · intro g hg
    obtain ⟨g1, hg1, rfl⟩ := List.mem_map.1 hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg1
    refine ⟨(hF g0 hg0).1, ?_⟩
    show ((g0.inputs.map r).map _).length ≤ 2
    rw [List.length_map, List.length_map]; exact (hF g0 hg0).2
  · show ((C.gates.map (rgp r)).map (clipK 29)).length = C.gates.length
    rw [List.length_map, List.length_map]
  · intro g hg i hi
    obtain ⟨g1, hg1, rfl⟩ := List.mem_map.1 hg
    obtain ⟨i0, _, rfl⟩ := List.mem_map.1 hi
    exact Nat.min_le_right _ _
  · intro x b
    show (wf ((C.gates.map (rgp r)).map (clipK 29)) (List.ofFn x ++ [b])).getD (min (r C.output) 29) false
      = (wf C.gates (List.ofFn (x ∘ σ) ++ [b])).getD C.output false
    have hU : (List.ofFn x ++ [b]).length = 11 := by simp
    rw [clipKw 29 _ _ (by rw [hU, List.length_map]; omega),
      clipK_get 29 _ (by rw [wf_len, hU, List.length_map]; omega)]
    refine (pkey 10 r hlt' hge C.gates (List.ofFn x ++ [b]) (List.ofFn (x ∘ σ) ++ [b])
      (by simp) (by simp) ?_ C.output).symm
    intro v
    by_cases hv : v < 10
    · rw [hlt v hv, List.getD_append _ _ _ _ (by simp; exact hv),
        List.getD_append _ _ _ _ (by simp)]
      have e1 := getD_ofFn (x ∘ σ) ⟨v, hv⟩
      have e2 := getD_ofFn x (σ ⟨v, hv⟩)
      rw [e2]
      exact e1
    · rw [hge v (by omega)]
      by_cases hv2 : v = 10
      · rw [hv2]
        have a1 : (List.ofFn (x ∘ σ) ++ [b]).getD 10 false = b := by
          have := getD_snoc_eq (List.ofFn (x ∘ σ)) b
          rw [List.length_ofFn] at this
          exact this
        have a2 : (List.ofFn x ++ [b]).getD 10 false = b := by
          have := getD_snoc_eq (List.ofFn x) b
          rw [List.length_ofFn] at this
          exact this
        rw [a1, a2]
      · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
