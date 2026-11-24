import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4934

/-- Rewiring of a read: input `i < 10` is read from input `x2 i`, input `10` stays, a wire
`10 <= i <= 28` stays, and every other index reads the never-existing wire `29`. -/
def tau (x2 : Fin 10 → Fin 10) (i : ℕ) : ℕ :=
  if h : i < 10 then ((x2 ⟨i, h⟩ : Fin 10) : ℕ) else if i ≤ 28 then i else 29

def mapGate (x2 : Fin 10 → Fin 10) (g : PEqualNP.CircuitLowerBounds.Gate) :
    PEqualNP.CircuitLowerBounds.Gate :=
  ⟨g.op, g.inputs.map (tau x2)⟩

lemma tau_le (x2 : Fin 10 → Fin 10) (i : ℕ) : tau x2 i ≤ 29 := by
  unfold tau
  split_ifs with h1 h2
  · have := (x2 ⟨i, h1⟩).isLt
    omega
  · omega
  · omega

lemma tau_lt10 (x2 : Fin 10 → Fin 10) (i : ℕ) (h : i < 10) : tau x2 i < 10 := by
  unfold tau
  rw [dif_pos h]
  exact (x2 ⟨i, h⟩).isLt

lemma getD_snoc (w : List Bool) (a : Bool) (k : ℕ) :
    (w ++ [a]).getD k false = if k < w.length then w.getD k false
      else if k = w.length then a else false := by
  rcases lt_trichotomy k w.length with h | h | h
  · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h, h]
  · subst h
    simp [List.getD_eq_getElem?_getD]
  · have h1 : ¬ k < w.length := by omega
    have h2 : ¬ k = w.length := by omega
    rw [if_neg h1, if_neg h2]
    exact List.getD_eq_default _ _ (by simp only [List.length_append, List.length_singleton]; omega)

lemma getD_ofFn_snoc (f : Fin 10 → Bool) (b : Bool) (k : ℕ) :
    (List.ofFn f ++ [b]).getD k false =
      if h : k < 10 then f ⟨k, h⟩ else if k = 10 then b else false := by
  rw [getD_snoc, List.length_ofFn]
  by_cases h : k < 10
  · rw [if_pos h, dif_pos h, List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos h]
    rfl
  · rw [if_neg h, dif_neg h]

lemma step_H2 (x2 : Fin 10 → Fin 10) (g : PEqualNP.CircuitLowerBounds.Gate)
    (w1 w5 : List Bool) (hlen : w5.length = w1.length) (h11 : 11 ≤ w1.length)
    (hL : w1.length ≤ 28) (H : ∀ i, w5.getD (tau x2 i) false = w1.getD i false) :
    ∀ i, (w5 ++ [(mapGate x2 g).op.eval ((mapGate x2 g).inputs.map fun k => w5.getD k false)]).getD
        (tau x2 i) false
      = (w1 ++ [g.op.eval (g.inputs.map fun k => w1.getD k false)]).getD i false := by
  intro i
  have hab : (mapGate x2 g).op.eval ((mapGate x2 g).inputs.map fun k => w5.getD k false)
      = g.op.eval (g.inputs.map fun k => w1.getD k false) := by
    simp only [mapGate, List.map_map, Function.comp_def]
    congr 1
    apply List.map_congr_left
    intro k _
    exact H k
  rw [getD_snoc, getD_snoc, hab]
  rcases (show i < 10 ∨ (10 ≤ i ∧ i ≤ 28) ∨ 29 ≤ i by omega) with hi | hi | hi
  · have ht := tau_lt10 x2 i hi
    rw [if_pos (by omega : tau x2 i < w5.length), if_pos (by omega : i < w1.length), H i]
  · have e : tau x2 i = i := by unfold tau; rw [dif_neg (by omega), if_pos hi.2]
    have H' := H i
    rw [e] at H' ⊢
    simp only [hlen]
    split_ifs <;> first | exact H' | rfl | (exfalso; omega) | simp_all
  · have e : tau x2 i = 29 := by unfold tau; rw [dif_neg (by omega), if_neg (by omega)]
    have c1 : ¬ (29 < w5.length) := by omega
    have c2 : ¬ (29 = w5.length) := by omega
    have c3 : ¬ (i < w1.length) := by omega
    have c4 : ¬ (i = w1.length) := by omega
    rw [e, if_neg c1, if_neg c2, if_neg c3, if_neg c4]

lemma key (x2 : Fin 10 → Fin 10) : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate)
    (w1 w5 : List Bool), w5.length = w1.length → 11 ≤ w1.length → w1.length + gs.length ≤ 29 →
    (∀ i, w5.getD (tau x2 i) false = w1.getD i false) → ∀ j,
    ((gs.map (mapGate x2)).foldl
        (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w5).getD
        (tau x2 j) false
      = (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w1).getD
        j false := by
  intro gs
  induction gs with
  | nil =>
    intro w1 w5 _ _ _ H j
    simpa using H j
  | cons g gs ih =>
    intro w1 w5 hlen h11 hb H
    simp only [List.length_cons] at hb
    simp only [List.map_cons, List.foldl_cons]
    refine ih _ _ ?_ ?_ ?_ (step_H2 x2 g w1 w5 hlen h11 (by omega) H)
    · simp [hlen]
    · simp only [List.length_append, List.length_singleton]; omega
    · simp only [List.length_append, List.length_singleton]; omega

lemma init_H2 (x2 : Fin 10 → Fin 10) (x6 : Fin 10 → Bool) (x7 : Bool) :
    ∀ i, (List.ofFn x6 ++ [x7]).getD (tau x2 i) false
      = (List.ofFn (x6 ∘ x2) ++ [x7]).getD i false := by
  intro i
  rw [getD_ofFn_snoc, getD_ofFn_snoc]
  by_cases hi : i < 10
  · have e : tau x2 i = ((x2 ⟨i, hi⟩ : Fin 10) : ℕ) := by unfold tau; rw [dif_pos hi]
    have ht := (x2 ⟨i, hi⟩).isLt
    simp only [e, dif_pos ht, dif_pos hi]
    rfl
  · by_cases h28 : i ≤ 28
    · have e : tau x2 i = i := by unfold tau; rw [dif_neg hi, if_pos h28]
      by_cases h10 : i = 10
      · subst h10
        simp [e]
      · simp [e, hi, h10]
    · have e : tau x2 i = 29 := by unfold tau; rw [dif_neg hi, if_neg h28]
      simp [e, hi, show i ≠ 10 by omega]

end PEqualNP.Outside.L_meta_4934

theorem PEqualNP.Outside.L_meta_4934 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (10 : ℕ) → Fin (10 : ℕ)), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) → ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x5 ∧ x5.size = x1.size ∧ x5.output ≤ (29 : ℕ) ∧ (∀ x6 ∈ x5.gates, ∀ x8 ∈ x6.inputs, x8 ≤ (29 : ℕ)) ∧ ∀ (x6 : Fin (10 : ℕ) → Bool) (x7 : Bool), x5.eval (List.ofFn x6 ++ [x7]) = x1.eval (List.ofFn (x6 ∘ x2) ++ [x7]) := by
  intro x1 x2 hF hs
  have hgates : x1.gates.length ≤ 18 := hs
  refine ⟨⟨x1.gates.map (PEqualNP.Outside.L_meta_4934.mapGate x2),
    PEqualNP.Outside.L_meta_4934.tau x2 x1.output⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
    have h := hF g' hg'
    exact ⟨h.1, by simp [PEqualNP.Outside.L_meta_4934.mapGate, h.2]⟩
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size]
  · exact PEqualNP.Outside.L_meta_4934.tau_le x2 _
  · intro g hg x8 hx8
    obtain ⟨g', _, rfl⟩ := List.mem_map.1 hg
    simp only [PEqualNP.Outside.L_meta_4934.mapGate, List.mem_map] at hx8
    obtain ⟨a, _, rfl⟩ := hx8
    exact PEqualNP.Outside.L_meta_4934.tau_le x2 a
  · intro x6 x7
    simp only [PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires]
    have hlen : (List.ofFn x6 ++ [x7]).length = (List.ofFn (x6 ∘ x2) ++ [x7]).length := by simp
    have h11 : 11 ≤ (List.ofFn (x6 ∘ x2) ++ [x7]).length := by simp
    have hb : (List.ofFn (x6 ∘ x2) ++ [x7]).length + x1.gates.length ≤ 29 := by simp; omega
    exact PEqualNP.Outside.L_meta_4934.key x2 x1.gates _ _ hlen h11 hb
      (PEqualNP.Outside.L_meta_4934.init_H2 x2 x6 x7) x1.output
