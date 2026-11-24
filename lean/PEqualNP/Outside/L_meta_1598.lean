import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1598

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_stepWire_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_stepWire_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]

def W (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD u false

lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

lemma W_gate (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length) :
    W n C x (n + k) = (gateAt C k).op.eval ((gateAt C k).inputs.map fun i =>
      if i < n + k then W n C x i else false) := by
  obtain ⟨pre, post, gj, hgs, hpre_len, hgj⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gj := by rw [gateAt_eq C k hk]; exact hgj
  rw [hga]
  let w0 := pre.foldl stepWire (List.ofFn x)
  have hw0_len : w0.length = n + k := by
    simp [w0, foldl_stepWire_length, hpre_len]
  have hCj : W n C x (n + k) = gj.op.eval (gj.inputs.map fun i => w0.getD i false) := by
    simp only [W]
    rw [wires_eq_foldl, hgs, List.foldl_append, List.foldl_cons]
    rw [foldl_stepWire_getD_lt post (stepWire w0 gj) (n + k) (by simp [stepWire]; omega)]
    simp [stepWire, List.getD_eq_getElem?_getD, hw0_len]
  rw [hCj]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  by_cases hi : i < n + k
  · simp only [hi, ↓reduceIte]
    simp only [W]
    rw [wires_eq_foldl, hgs, List.foldl_append]
    exact (foldl_stepWire_getD_lt (gj :: post) w0 i (by omega)).symm
  · simp only [hi, ↓reduceIte]
    exact getD_ge_length w0 i (by omega)

lemma W_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    W n C x u = x ⟨u, hu⟩ := by
  simp only [W]
  rw [wires_eq_foldl, foldl_stepWire_getD_lt C.gates (List.ofFn x) u (by simpa using hu)]
  simp [List.getD_eq_getElem?_getD, hu]

open PEqualNP.CleanedNonEdge in
lemma cnFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

open PEqualNP.CleanedNonEdge in
lemma cnStep_mem_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) (x : ℕ) :
    x ∈ (orStep n cs g).getD cs.length [] ↔ x = cs.length ∨ (g.op = GateOp.or ∧
      ∃ w ∈ g.inputs, n ≤ w ∧ w < n + cs.length ∧ x ∈ cs.getD (w - n) []) := by
  by_cases hop : g.op = GateOp.or
  · simp only [orStep, hop, ↓reduceIte, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (le_refl cs.length), Nat.sub_self, List.getElem?_cons_zero,
      Option.getD_some, List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq,
      true_and]
    constructor
    · rintro (h | ⟨w, ⟨hw, hn, hlt⟩, h⟩)
      · exact Or.inl h
      · exact Or.inr ⟨w, hw, hn, hlt, h⟩
    · rintro (h | ⟨w, hw, hn, hlt, h⟩)
      · exact Or.inl h
      · exact Or.inr ⟨w, ⟨hw, hn, hlt⟩, h⟩
  · simp only [orStep, hop, ↓reduceIte, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (le_refl cs.length), Nat.sub_self, List.getElem?_cons_zero,
      Option.getD_some, List.mem_cons, List.not_mem_nil, or_false, false_and]

open PEqualNP.CleanedNonEdge in
lemma cnStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
    (orStep n cs g).getD m [] = cs.getD m [] := by
  simp [orStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]

open PEqualNP.CleanedNonEdge in
lemma cnFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
    (hk : k < cs.length) :
    (gs.foldl (orStep n) cs).getD k [] = cs.getD k [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (orStep n cs g) (by simp [orStep]; omega)]
    exact cnStep_getD_lt n cs g k hk

open PEqualNP.CleanedNonEdge in
lemma orSets_iff (n : ℕ) (C : Circuit) (g k : ℕ) (hk : k < C.gates.length) :
    g ∈ (orSets n C).getD k [] ↔ g = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧ g ∈ (orSets n C).getD (w - n) []) := by
  obtain ⟨pre, post, gk, hgs, hpre_len, hgk⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gk := by rw [gateAt_eq C k hk]; exact hgk
  rw [hga]
  have hc : orSets n C = post.foldl (orStep n) (orStep n (pre.foldl (orStep n) []) gk) := by
    simp only [orSets]
    rw [hgs, List.foldl_append, List.foldl_cons]
  have hl0 : (pre.foldl (orStep n) []).length = k := by
    rw [cnFold_length]; simp [hpre_len]
  have hl1 : (orStep n (pre.foldl (orStep n) []) gk).length = k + 1 := by
    simp [orStep, hl0]
  have h1 : (orSets n C).getD k [] = (orStep n (pre.foldl (orStep n) []) gk).getD k [] := by
    rw [hc, cnFold_getD_lt n post _ k (by omega)]
  have h2 : ∀ m, m < k → (orSets n C).getD m [] = (pre.foldl (orStep n) []).getD m [] := by
    intro m hm
    rw [hc, cnFold_getD_lt n post _ m (by omega)]
    exact cnStep_getD_lt n _ gk m (by omega)
  have h3 := cnStep_mem_last n (pre.foldl (orStep n) []) gk g
  rw [hl0] at h3
  rw [h1, h3]
  constructor
  · rintro (h | ⟨hop, w, hw, hn, hlt, h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hop, w, hw, hn, hlt, by rw [h2 (w - n) (by omega)]; exact h⟩
  · rintro (h | ⟨hop, w, hw, hn, hlt, h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hop, w, hw, hn, hlt, by rw [← h2 (w - n) (by omega)]; exact h⟩

lemma wires_length (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  rw [wires_eq_foldl, foldl_stepWire_length, List.length_ofFn]

open PEqualNP.CleanedNonEdge PEqualNP.EdgeOwnership in
lemma key (n : ℕ) (C : Circuit) (hAO : AndOrOnly C) (U : Finset (Fin n)) :
    ∀ w : ℕ, W n C (fun k : Fin n => decide (k ∈ U)) w = true →
      (∀ g : ℕ, OrReaches n C w g → (gateAt C g).op = GateOp.and →
        EdgeOwnership.gateVal n C g (fun l : Fin n => decide (l ∈ U)) = false) →
      ∃ i ∈ U, W n C (fun r : Fin n => decide (r = i)) w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hcl
    by_cases hlt : w < n
    · rw [W_input n C _ w hlt] at hw
      refine ⟨⟨w, hlt⟩, by simpa using hw, ?_⟩
      rw [W_input n C _ w hlt]
      simp
    · by_cases hge : n + C.gates.length ≤ w
      · exfalso
        have : W n C (fun k : Fin n => decide (k ∈ U)) w = false := by
          simp only [W]
          exact getD_ge_length _ w (by rw [wires_length]; omega)
        rw [this] at hw
        exact absurd hw (by simp)
      · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
        have hk : k < C.gates.length := by omega
        have hself : OrReaches n C (n + k) k := by
          refine ⟨by omega, ?_⟩
          rw [show n + k - n = k by omega, orSets_iff n C k k hk]
          exact Or.inl rfl
        have hop : (gateAt C k).op = GateOp.or := by
          have hmem : gateAt C k ∈ C.gates := by
            rw [gateAt_eq C k hk]
            exact List.getElem_mem hk
          rcases hAO _ hmem with h | h
          · exfalso
            have := hcl k hself h
            have e : EdgeOwnership.gateVal n C k (fun l : Fin n => decide (l ∈ U)) =
                W n C (fun k : Fin n => decide (k ∈ U)) (n + k) := rfl
            rw [e, hw] at this
            exact absurd this (by simp)
          · exact h
        rw [W_gate n C _ k hk, hop] at hw
        simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq] at hw
        obtain ⟨i, hi, hiv⟩ := hw
        by_cases hik : i < n + k
        · simp only [hik, ite_true] at hiv
          have hcl' : ∀ g : ℕ, OrReaches n C i g → (gateAt C g).op = GateOp.and →
              EdgeOwnership.gateVal n C g (fun l : Fin n => decide (l ∈ U)) = false := by
            intro g hg hg2
            apply hcl g _ hg2
            refine ⟨by omega, ?_⟩
            rw [show n + k - n = k by omega, orSets_iff n C g k hk]
            exact Or.inr ⟨hop, i, hi, hg.1, hik, hg.2⟩
          obtain ⟨j, hjU, hj⟩ := ih i hik hiv hcl'
          refine ⟨j, hjU, ?_⟩
          rw [W_gate n C _ k hk, hop]
          simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
          exact ⟨i, hi, by simp only [hik, ite_true]; exact hj⟩
        · simp [hik] at hiv


end PEqualNP.Outside.L_meta_1598

open PEqualNP.Outside.L_meta_1598 in
theorem PEqualNP.Outside.L_meta_1598 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.EdgeOwnership.AndOrOnly C → ∀ (U : Finset (Fin n)) (w : ℕ), PEqualNP.CleanedNonEdge.wireVal n C w (fun k : Fin n => decide (k ∈ U)) = true → (∀ g : ℕ, PEqualNP.CleanedNonEdge.OrReaches n C w g → (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = PEqualNP.CircuitLowerBounds.GateOp.and → PEqualNP.EdgeOwnership.gateVal n C g (fun l : Fin n => decide (l ∈ U)) = false) → ∃ i ∈ U, PEqualNP.CleanedNonEdge.wireVal n C w (fun r : Fin n => decide (r = i)) = true := by
  intro n C hAO U w hw hcl
  exact key n C hAO U w hw hcl
