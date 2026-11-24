import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2234

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

lemma wires_length (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  rw [wires_eq_foldl, foldl_stepWire_length, List.length_ofFn]

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

lemma W_or (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.or) (a b : ℕ) (hin : (gateAt C k).inputs = [a, b])
    (ha : a < n + k) (hb : b < n + k) :
    W n C x (n + k) = (W n C x a || W n C x b) := by
  rw [W_gate n C x k hk, hop, hin]
  simp [GateOp.eval, ha, hb]

lemma W_and (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.and) (a b : ℕ) (hin : (gateAt C k).inputs = [a, b])
    (ha : a < n + k) (hb : b < n + k) :
    W n C x (n + k) = (W n C x a && W n C x b) := by
  rw [W_gate n C x k hk, hop, hin]
  simp [GateOp.eval, ha, hb]

def AO (n : ℕ) (C : Circuit) : Prop :=
  ∀ k < C.gates.length, ((gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or) ∧
    ∃ a b, (gateAt C k).inputs = [a, b] ∧ a < n + k ∧ b < n + k

def OrStep (n : ℕ) (C : Circuit) (u v : ℕ) : Prop :=
  ∃ k, u = n + k ∧ k < C.gates.length ∧ (gateAt C k).op = GateOp.or ∧ v ∈ (gateAt C k).inputs

def OrR (n : ℕ) (C : Circuit) : ℕ → ℕ → Prop := Relation.ReflTransGen (OrStep n C)

lemma orStep_lt (n : ℕ) (C : Circuit) (hA : AO n C) (u v : ℕ) (h : OrStep n C u v) : v < u := by
  obtain ⟨k, rfl, hk, _, hv⟩ := h
  obtain ⟨_, a, b, hin, ha, hb⟩ := hA k hk
  rw [hin] at hv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  omega

lemma orR_le (n : ℕ) (C : Circuit) (hA : AO n C) (u v : ℕ) (h : OrR n C u v) : v ≤ u := by
  induction h with
  | refl => exact le_rfl
  | tail _ h2 ih => have := orStep_lt n C hA _ _ h2; omega

lemma orStep_mono (n : ℕ) (C : Circuit) (hA : AO n C) (x : Fin n → Bool) (u v : ℕ)
    (h : OrStep n C u v) (hv : W n C x v = true) : W n C x u = true := by
  obtain ⟨k, rfl, hk, hop, hin⟩ := h
  obtain ⟨_, a, b, hab, ha, hb⟩ := hA k hk
  rw [W_or n C x k hk hop a b hab ha hb]
  rw [hab] at hin
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
  rcases hin with rfl | rfl
  · simp [hv]
  · simp [hv]

lemma orR_mono (n : ℕ) (C : Circuit) (hA : AO n C) (x : Fin n → Bool) (u v : ℕ)
    (h : OrR n C u v) (hv : W n C x v = true) : W n C x u = true := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact hv
  | head h1 _ ih => exact orStep_mono n C hA x _ _ h1 ih

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

open PEqualNP.CleanedNonEdge in
lemma orSets_len (n : ℕ) (C : Circuit) : (orSets n C).length = C.gates.length := by
  simp only [orSets]
  rw [cnFold_length]
  simp

open PEqualNP.CleanedNonEdge in
lemma reaches_to (n : ℕ) (C : Circuit) :
    ∀ k g, g ∈ (orSets n C).getD k [] → g < C.gates.length ∧ OrR n C (n + k) (n + g) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro g hg
    have hk : k < C.gates.length := by
      by_contra hk
      have hnone : (orSets n C)[k]? = none :=
        List.getElem?_eq_none (by rw [orSets_len]; omega)
      rw [List.getD_eq_getElem?_getD, hnone] at hg
      simp at hg
    rw [orSets_iff n C g k hk] at hg
    rcases hg with rfl | ⟨hop, w, hw, hn, hlt, h⟩
    · exact ⟨hk, Relation.ReflTransGen.refl⟩
    · obtain ⟨h4, h5⟩ := ih (w - n) (by omega) g h
      have hw' : n + (w - n) = w := by omega
      rw [hw'] at h5
      exact ⟨h4, Relation.ReflTransGen.head ⟨k, rfl, hk, hop, hw⟩ h5⟩

open PEqualNP.CleanedNonEdge in
lemma orReaches_iff (n : ℕ) (C : Circuit) (hA : AO n C) (w g : ℕ) :
    OrReaches n C w g ↔ (n ≤ w ∧ g < C.gates.length ∧ OrR n C w (n + g)) := by
  constructor
  · rintro ⟨hn, h⟩
    obtain ⟨h1, h2⟩ := reaches_to n C (w - n) g h
    have hw' : n + (w - n) = w := by omega
    rw [hw'] at h2
    exact ⟨hn, h1, h2⟩
  · rintro ⟨hn, hg, h⟩
    refine ⟨hn, ?_⟩
    clear hn
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl =>
      have he : n + g - n = g := by omega
      rw [he, orSets_iff n C g g hg]
      exact Or.inl rfl
    | head h1 h2 ih =>
      rename_i u c
      have hle := orR_le n C hA _ _ h2
      have hlt := orStep_lt n C hA _ _ h1
      obtain ⟨k, rfl, hk, hop, hin⟩ := h1
      have he : n + k - n = k := by omega
      rw [he, orSets_iff n C g k hk]
      exact Or.inr ⟨hop, c, hin, by omega, hlt, ih⟩

lemma orIn_iff (n : ℕ) (C : Circuit) (hA : AO n C) (w : ℕ) (u : Fin n) :
    u ∈ PEqualNP.TopForm.orIn n C w ↔ OrR n C w u.val := by
  simp only [PEqualNP.TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (h | ⟨k, hk, hr, hop, hin⟩)
    · rw [h]
      exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.tail ((orReaches_iff n C hA w k).mp hr).2.2 ⟨k, rfl, hk, hop, hin⟩
  · intro h
    rcases Relation.ReflTransGen.cases_tail h with h1 | ⟨c, h1, ⟨k, rfl, hk, hop, hin⟩⟩
    · exact Or.inl h1
    · have hle := orR_le n C hA _ _ h1
      exact Or.inr ⟨k, hk, (orReaches_iff n C hA w k).mpr ⟨by omega, hk, h1⟩, hop, hin⟩

lemma ao_of (n : ℕ) (C : Circuit) (h : PEqualNP.TopForm.IsAO2 n C) : AO n C := by
  obtain ⟨h1, h2, h3⟩ := h
  intro k hk
  have hmem : gateAt C k ∈ C.gates := by
    rw [gateAt_eq C k hk]
    exact List.getElem_mem hk
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (h3 _ hmem)
  refine ⟨h1 _ hmem, a, b, hab, ?_, ?_⟩
  · exact h2 k hk a (by rw [hab]; simp)
  · exact h2 k hk b (by rw [hab]; simp)

theorem cone_count {α : Type*} [DecidableEq α] (n : ℕ) (S : ℕ → Finset α) (Rc : ℕ → ℕ → Prop)
    (h1 : ∀ w < n, (S w).card ≤ 1)
    (h2 : ∀ t, 2 ≤ (S (n + t)).card → ∃ p q, p < n + t ∧ q < n + t ∧ S (n + t) ⊆ S p ∪ S q ∧
      Rc (n + t) t ∧ ∀ g, Rc p g ∨ Rc q g → Rc (n + t) g) :
    ∀ t (W : Finset ℕ), (∀ w ∈ W, w < n + t) → ∀ R : Finset ℕ,
      (∀ g < t, 2 ≤ (S (n + g)).card → (∃ w ∈ W, Rc w g) → g ∈ R) →
      (W.biUnion S).card ≤ R.card + W.card := by
  intro t
  induction t with
  | zero =>
    intro W hW R _
    have e1 : (W.biUnion S).card ≤ ∑ w ∈ W, (S w).card := Finset.card_biUnion_le
    have e2 : ∑ w ∈ W, (S w).card ≤ ∑ w ∈ W, 1 :=
      Finset.sum_le_sum (fun w hw => h1 w (by have := hW w hw; omega))
    have e3 : ∑ w ∈ W, 1 = W.card := by simp
    omega
  | succ t ih =>
    intro W hW R hR
    by_cases hmem : n + t ∈ W
    · have hpos : 0 < W.card := Finset.card_pos.mpr ⟨_, hmem⟩
      have e3 := Finset.card_erase_of_mem hmem
      by_cases hc : 2 ≤ (S (n + t)).card
      · obtain ⟨p, q, hp, hq, hsub, hself, hreach⟩ := h2 t hc
        have htR : t ∈ R := hR t (by omega) hc ⟨n + t, hmem, hself⟩
        have hW2 : ∀ w ∈ insert p (insert q (W.erase (n + t))), w < n + t := by
          intro w hw
          simp only [Finset.mem_insert, Finset.mem_erase] at hw
          rcases hw with rfl | rfl | ⟨hne, hw⟩
          · exact hp
          · exact hq
          · have := hW w hw
            omega
        have hR2 : ∀ g < t, 2 ≤ (S (n + g)).card →
            (∃ w ∈ insert p (insert q (W.erase (n + t))), Rc w g) → g ∈ R.erase t := by
          intro g hg hcg hex
          obtain ⟨w, hw, hr⟩ := hex
          rw [Finset.mem_erase]
          refine ⟨by omega, hR g (by omega) hcg ?_⟩
          simp only [Finset.mem_insert, Finset.mem_erase] at hw
          rcases hw with rfl | rfl | ⟨hne, hw⟩
          · exact ⟨n + t, hmem, hreach g (Or.inl hr)⟩
          · exact ⟨n + t, hmem, hreach g (Or.inr hr)⟩
          · exact ⟨w, hw, hr⟩
        have key := ih (insert p (insert q (W.erase (n + t)))) hW2 (R.erase t) hR2
        have hU : W.biUnion S ⊆ (insert p (insert q (W.erase (n + t)))).biUnion S := by
          intro x hx
          rw [Finset.mem_biUnion] at hx ⊢
          obtain ⟨w, hw, hxw⟩ := hx
          by_cases hwt : w = n + t
          · subst hwt
            rcases Finset.mem_union.mp (hsub hxw) with h | h
            · exact ⟨p, by simp, h⟩
            · exact ⟨q, by simp, h⟩
          · exact ⟨w, by simp [hwt, hw], hxw⟩
        have e1 := Finset.card_insert_le p (insert q (W.erase (n + t)))
        have e2 := Finset.card_insert_le q (W.erase (n + t))
        have hc2 : (R.erase t).card + 1 = R.card := Finset.card_erase_add_one htR
        have e4 := Finset.card_le_card hU
        omega
      · have hW2 : ∀ w ∈ W.erase (n + t), w < n + t := by
          intro w hw
          have h5 := hW w (Finset.mem_of_mem_erase hw)
          have h6 := Finset.ne_of_mem_erase hw
          omega
        have hR2 : ∀ g < t, 2 ≤ (S (n + g)).card → (∃ w ∈ W.erase (n + t), Rc w g) → g ∈ R := by
          intro g hg hcg hex
          obtain ⟨w, hw, hr⟩ := hex
          exact hR g (by omega) hcg ⟨w, Finset.mem_of_mem_erase hw, hr⟩
        have key := ih (W.erase (n + t)) hW2 R hR2
        have hU : W.biUnion S ⊆ (W.erase (n + t)).biUnion S ∪ S (n + t) := by
          intro x hx
          rw [Finset.mem_biUnion] at hx
          obtain ⟨w, hw, hxw⟩ := hx
          rw [Finset.mem_union, Finset.mem_biUnion]
          by_cases hwt : w = n + t
          · subst hwt
            exact Or.inr hxw
          · exact Or.inl ⟨w, Finset.mem_erase.mpr ⟨hwt, hw⟩, hxw⟩
        have e4 := Finset.card_le_card hU
        have e5 := Finset.card_union_le ((W.erase (n + t)).biUnion S) (S (n + t))
        omega
    · have hW2 : ∀ w ∈ W, w < n + t := by
        intro w hw
        have h5 := hW w hw
        have h6 : w ≠ n + t := fun h => hmem (h ▸ hw)
        omega
      exact ih W hW2 R (fun g hg hcg hex => hR g (by omega) hcg hex)

lemma orIn_small (n : ℕ) (C : Circuit) (hA : AO n C) (w : ℕ) (hw : w < n) :
    (PEqualNP.TopForm.orIn n C w).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  have h : ∀ u : Fin n, u ∈ PEqualNP.TopForm.orIn n C w → u.val = w := by
    intro u hu
    rcases Relation.ReflTransGen.cases_head ((orIn_iff n C hA w u).mp hu) with h | ⟨c, ⟨k, hk, _⟩, _⟩
    · exact h.symm
    · omega
  exact Fin.ext ((h a ha).trans (h b hb).symm)

lemma orIn_big (n : ℕ) (C : Circuit) (hA : AO n C) (t : ℕ)
    (hc : 2 ≤ (PEqualNP.TopForm.orIn n C (n + t)).card) :
    t < C.gates.length ∧ (gateAt C t).op = GateOp.or ∧ ∃ p q, p < n + t ∧ q < n + t ∧
      PEqualNP.TopForm.orIn n C (n + t) ⊆
        PEqualNP.TopForm.orIn n C p ∪ PEqualNP.TopForm.orIn n C q ∧
      PEqualNP.CleanedNonEdge.OrReaches n C (n + t) t ∧
      ∀ g, PEqualNP.CleanedNonEdge.OrReaches n C p g ∨ PEqualNP.CleanedNonEdge.OrReaches n C q g →
        PEqualNP.CleanedNonEdge.OrReaches n C (n + t) g := by
  obtain ⟨u, hu⟩ : (PEqualNP.TopForm.orIn n C (n + t)).Nonempty := Finset.card_pos.mp (by omega)
  have hstep : ∀ v : Fin n, OrR n C (n + t) v.val →
      ∃ c, OrStep n C (n + t) c ∧ OrR n C c v.val := by
    intro v hv
    rcases Relation.ReflTransGen.cases_head hv with h | h
    · have := v.isLt
      omega
    · exact h
  obtain ⟨c0, ⟨k, hk, hklen, hop, hin0⟩, _⟩ := hstep u ((orIn_iff n C hA _ u).mp hu)
  have hkt : k = t := by omega
  rw [hkt] at hklen hop
  obtain ⟨_, a, b, hab, ha, hb⟩ := hA t hklen
  refine ⟨hklen, hop, a, b, ha, hb, ?_, ?_, ?_⟩
  · intro v hv
    obtain ⟨c, ⟨k2, hk2, _, _, hin⟩, hr⟩ := hstep v ((orIn_iff n C hA _ v).mp hv)
    have hk2t : k2 = t := by omega
    rw [hk2t, hab] at hin
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
    rw [Finset.mem_union]
    rcases hin with rfl | rfl
    · exact Or.inl ((orIn_iff n C hA _ v).mpr hr)
    · exact Or.inr ((orIn_iff n C hA _ v).mpr hr)
  · exact (orReaches_iff n C hA _ _).mpr ⟨by omega, hklen, Relation.ReflTransGen.refl⟩
  · intro g hg
    rcases hg with hg | hg
    · obtain ⟨_, hgl, hr⟩ := (orReaches_iff n C hA _ _).mp hg
      exact (orReaches_iff n C hA _ _).mpr ⟨by omega, hgl,
        Relation.ReflTransGen.head ⟨t, rfl, hklen, hop, by rw [hab]; simp⟩ hr⟩
    · obtain ⟨_, hgl, hr⟩ := (orReaches_iff n C hA _ _).mp hg
      exact (orReaches_iff n C hA _ _).mpr ⟨by omega, hgl,
        Relation.ReflTransGen.head ⟨t, rfl, hklen, hop, by rw [hab]; simp⟩ hr⟩

lemma orIn_sub (n : ℕ) (C : Circuit) (hA : AO n C) (w g : ℕ)
    (h : PEqualNP.CleanedNonEdge.OrReaches n C w g) :
    PEqualNP.TopForm.orIn n C (n + g) ⊆ PEqualNP.TopForm.orIn n C w := by
  intro u hu
  obtain ⟨_, _, hr⟩ := (orReaches_iff n C hA w g).mp h
  exact (orIn_iff n C hA w u).mpr
    (Relation.ReflTransGen.trans hr ((orIn_iff n C hA _ u).mp hu))

lemma out_true (n : ℕ) (C : Circuit) (hA : AO n C) (i : ℕ) (b : Fin n)
    (hr : PEqualNP.CleanedNonEdge.OrReaches n C C.output i)
    (hb : b ∈ PEqualNP.TopForm.orIn n C (n + i)) :
    PEqualNP.MetaComplexity.circuitFun n C (fun k1 => decide (k1 = b)) = true := by
  have h1 := orIn_sub n C hA _ _ hr hb
  have h2 := (orIn_iff n C hA _ b).mp h1
  have h3 := orR_mono n C hA (fun k1 => decide (k1 = b)) _ _ h2
    (by rw [W_input n C _ b.val b.isLt]; simp)
  exact h3

theorem part2 (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (F : Finset ℕ)
    (ctr : ℕ → Fin n) (lf : ℕ → ℕ) (hN : PEqualNP.TopForm.NoFourCycle G)
    (hI : PEqualNP.TopForm.IsAO2 n C)
    (hlf : ∀ j ∈ F, ∀ b : Fin n, b ∈ PEqualNP.TopForm.orIn n C (lf j) → G.Adj (ctr j) b)
    (U : Fin n → Finset (Fin n))
    (hU : ∀ c b, b ∈ U c → ∃ j ∈ F, ctr j = c ∧ b ∈ PEqualNP.TopForm.orIn n C (lf j)) :
    ∑ c : Fin n, (U c).card ≤ Set.ncard {i2 : ℕ | i2 < C.gates.length ∧
      (gateAt C i2).op = GateOp.or ∧ 2 ≤ (PEqualNP.TopForm.orIn n C (n + i2)).card ∧
      ∃ j3 ∈ F, PEqualNP.CleanedNonEdge.OrReaches n C (lf j3) i2} + F.card := by
  classical
  have hA := ao_of n C hI
  obtain ⟨T, hT⟩ : ∃ T, T = F.sup lf + 1 := ⟨_, rfl⟩
  obtain ⟨Rs, hRs⟩ : ∃ Rs : Fin n → Finset ℕ, ∀ c g, g ∈ Rs c ↔
      (g < T ∧ 2 ≤ (PEqualNP.TopForm.orIn n C (n + g)).card ∧
        ∃ w ∈ (F.filter (fun j => ctr j = c)).image lf,
          PEqualNP.CleanedNonEdge.OrReaches n C w g) :=
    ⟨fun c => (Finset.range T).filter (fun g =>
      2 ≤ (PEqualNP.TopForm.orIn n C (n + g)).card ∧
        ∃ w ∈ (F.filter (fun j => ctr j = c)).image lf,
          PEqualNP.CleanedNonEdge.OrReaches n C w g),
      fun c g => by rw [Finset.mem_filter, Finset.mem_range]⟩
  have hper : ∀ c, (U c).card ≤ (Rs c).card + (F.filter (fun j => ctr j = c)).card := by
    intro c
    have hW : ∀ w ∈ (F.filter (fun j => ctr j = c)).image lf, w < n + T := by
      intro w hw
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hw
      have h5 := Finset.le_sup (f := lf) (Finset.mem_filter.mp hj).1
      omega
    have hR : ∀ g < T, 2 ≤ (PEqualNP.TopForm.orIn n C (n + g)).card →
        (∃ w ∈ (F.filter (fun j => ctr j = c)).image lf,
          PEqualNP.CleanedNonEdge.OrReaches n C w g) → g ∈ Rs c := by
      intro g hg hcg hex
      exact (hRs c g).mpr ⟨hg, hcg, hex⟩
    have hcc := cone_count n (PEqualNP.TopForm.orIn n C) (PEqualNP.CleanedNonEdge.OrReaches n C)
      (fun w hw => orIn_small n C hA w hw)
      (fun t hc => (orIn_big n C hA t hc).2.2) T
      ((F.filter (fun j => ctr j = c)).image lf) hW (Rs c) hR
    have hsub : U c ⊆ ((F.filter (fun j => ctr j = c)).image lf).biUnion
        (PEqualNP.TopForm.orIn n C) := by
      intro b hb
      obtain ⟨j, hj, hcj, hbj⟩ := hU c b hb
      exact Finset.mem_biUnion.mpr
        ⟨lf j, Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨hj, hcj⟩, rfl⟩, hbj⟩
    have h3 := Finset.card_le_card hsub
    have h4 : ((F.filter (fun j => ctr j = c)).image lf).card ≤
        (F.filter (fun j => ctr j = c)).card := Finset.card_image_le
    omega
  have hdisj : ((Finset.univ : Finset (Fin n)) : Set (Fin n)).PairwiseDisjoint Rs := by
    intro c _ c2 _ hne
    show Disjoint (Rs c) (Rs c2)
    rw [Finset.disjoint_left]
    intro g hg hg2
    obtain ⟨_, hcg, w, hw, hr⟩ := (hRs c g).mp hg
    obtain ⟨_, _, w2, hw2, hr2⟩ := (hRs c2 g).mp hg2
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨j2, hj2, rfl⟩ := Finset.mem_image.mp hw2
    obtain ⟨hjF, hjc⟩ := Finset.mem_filter.mp hj
    obtain ⟨hjF2, hjc2⟩ := Finset.mem_filter.mp hj2
    have hadj : ∀ b ∈ PEqualNP.TopForm.orIn n C (n + g), G.Adj c b ∧ G.Adj c2 b := by
      intro b hb
      have h5 := hlf j hjF b (orIn_sub n C hA _ _ hr hb)
      have h6 := hlf j2 hjF2 b (orIn_sub n C hA _ _ hr2 hb)
      rw [hjc] at h5
      rw [hjc2] at h6
      exact ⟨h5, h6⟩
    have h7 : (PEqualNP.TopForm.orIn n C (n + g)).card ≤ 1 :=
      le_trans (Finset.card_le_card (fun b hb =>
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadj b hb⟩)) (hN c c2 hne)
    omega
  have hsumR : ∑ c : Fin n, (Rs c).card ≤ Set.ncard {i2 : ℕ | i2 < C.gates.length ∧
      (gateAt C i2).op = GateOp.or ∧ 2 ≤ (PEqualNP.TopForm.orIn n C (n + i2)).card ∧
      ∃ j3 ∈ F, PEqualNP.CleanedNonEdge.OrReaches n C (lf j3) i2} := by
    rw [← Finset.card_biUnion hdisj, ← Set.ncard_coe_finset]
    apply Set.ncard_le_ncard
    · intro g hg
      rw [Finset.mem_coe, Finset.mem_biUnion] at hg
      obtain ⟨c, _, hg⟩ := hg
      obtain ⟨_, hcg, w, hw, hr⟩ := (hRs c g).mp hg
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hw
      obtain ⟨hl, hop, _⟩ := orIn_big n C hA g hcg
      rw [Set.mem_setOf_eq]
      exact ⟨hl, hop, hcg, j, (Finset.mem_filter.mp hj).1, hr⟩
    · exact (Set.finite_lt_nat C.gates.length).subset (fun i hi => hi.1)
  have hsumF : ∑ c : Fin n, (F.filter (fun j => ctr j = c)).card = F.card :=
    (Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _))).symm
  have hsum : ∑ c : Fin n, (U c).card ≤
      ∑ c : Fin n, ((Rs c).card + (F.filter (fun j => ctr j = c)).card) :=
    Finset.sum_le_sum (fun c _ => hper c)
  rw [Finset.sum_add_distrib, hsumF] at hsum
  omega

end PEqualNP.Outside.L_meta_2234

theorem PEqualNP.Outside.L_meta_2234 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (F : Finset ℕ) (ctr : ℕ → Fin n) (lf : ℕ → ℕ), PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C → (∀ a1 : Fin n, PEqualNP.MetaComplexity.circuitFun n C (fun k1 => decide (k1 = a1)) = false) → (∀ j ∈ F, ∀ b : Fin n, b ∈ PEqualNP.TopForm.orIn n C (lf j) → G.Adj (ctr j) b) → (∀ i < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.or → 2 ≤ (PEqualNP.TopForm.orIn n C (n + i)).card → (∃ j1 ∈ F, PEqualNP.CleanedNonEdge.OrReaches n C (lf j1) i) → ¬ PEqualNP.CleanedNonEdge.OrReaches n C C.output i) ∧ ∑ c : Fin n, (Finset.univ.filter (fun b2 : Fin n => ∃ j2 ∈ F, ctr j2 = c ∧ b2 ∈ PEqualNP.TopForm.orIn n C (lf j2))).card ≤ Set.ncard {i2 : ℕ | i2 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i2).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ 2 ≤ (PEqualNP.TopForm.orIn n C (n + i2)).card ∧ ∃ j3 ∈ F, PEqualNP.CleanedNonEdge.OrReaches n C (lf j3) i2} + F.card := by
  intro n G _ C F ctr lf hN hI h1 hlf
  refine ⟨fun i _ _ hc _ hout => ?_, ?_⟩
  · obtain ⟨b, hb⟩ : (PEqualNP.TopForm.orIn n C (n + i)).Nonempty :=
      Finset.card_pos.mp (by omega)
    exact Bool.false_ne_true ((h1 b).symm.trans
      (PEqualNP.Outside.L_meta_2234.out_true n C (PEqualNP.Outside.L_meta_2234.ao_of n C hI) i b hout hb))
  · exact PEqualNP.Outside.L_meta_2234.part2 n G C F ctr lf hN hI hlf _
      (fun c b hb => (Finset.mem_filter.mp hb).2)
