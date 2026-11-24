import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2480

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.CleanedNonEdge PEqualNP.TopForm

lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]

lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
  simp [wf, List.foldl_append]

theorem wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i (by simp; omega)
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem wf_pre (pre post : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length + pre.length) :
    (wf (pre ++ post) w).getD i false = (wf pre w).getD i false := by
  have : wf (pre ++ post) w = wf post (wf pre w) := by simp [wf, List.foldl_append]
  rw [this]
  exact wf_keep post _ i (by rw [wf_len]; exact hi)

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem wire_take (gates : List Gate) (X : List Bool) (k i : ℕ) (hi : i < X.length + k)
    (hk : k ≤ gates.length) :
    (wf gates X).getD i false = (wf (gates.take k) X).getD i false := by
  conv_lhs => rw [← List.take_append_drop k gates]
  exact wf_pre _ _ _ _ (by rw [List.length_take, Nat.min_eq_left hk]; exact hi)

theorem gate_val (gates : List Gate) (X : List Bool) (k : ℕ) (hk : k < gates.length) :
    (wf gates X).getD (X.length + k) false
      = gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false) := by
  rw [wire_take gates X (k + 1) _ (by omega) hk, List.take_succ_eq_append_getElem hk, wf_snoc]
  have := getD_snoc_eq (wf (gates.take k) X)
    (gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false))
  rw [wf_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)] at this
  exact this

def val (gates : List Gate) {n : ℕ} (w : ℕ) (x : Fin n → Bool) : Bool :=
  (wf gates (List.ofFn x)).getD w false

theorem iv_eq (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k ≤ gates.length)
    (i : ℕ) : (wf (gates.take k) (List.ofFn x)).getD i false = true ↔
      i < n + k ∧ val gates i x = true := by
  by_cases hi : i < n + k
  · rw [val, wire_take gates (List.ofFn x) k i (by simpa using hi) hk]
    simp [hi]
  · rw [List.getD_eq_default _ _ (by rw [wf_len, List.length_take, Nat.min_eq_left hk]; simp; omega)]
    simp [hi]

theorem val_or (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gates.length)
    (hop : gates[k].op = GateOp.or) :
    val gates (n + k) x = true ↔ ∃ i ∈ gates[k].inputs, i < n + k ∧ val gates i x = true := by
  have := gate_val gates (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
  constructor
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gates x k (Nat.le_of_lt hk) i).1 h⟩
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gates x k (Nat.le_of_lt hk) i).2 h⟩

theorem val_input (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    val gates w x = x ⟨w, hw⟩ := by
  rw [val, wf_keep gates _ w (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

lemma val_or2 (C : Circuit) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.or) (u1 u2 : ℕ) (hin : (gateAt C k).inputs = [u1, u2])
    (u : ℕ) (hu : u = u1 ∨ u = u2) (hlt : u < n + k) (hv : val C.gates u x = true) :
    val C.gates (n + k) x = true := by
  rw [gateAt_eq C k hk] at hop hin
  exact (val_or C.gates x k hk hop).mpr ⟨u, by rw [hin]; simpa using hu, hlt, hv⟩

lemma orFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

lemma orStep_mem_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) (x : ℕ) :
    x ∈ (orStep n cs g).getD cs.length [] ↔ x = cs.length ∨ (g.op = GateOp.or ∧
      ∃ w, (w ∈ g.inputs ∧ n ≤ w ∧ w < n + cs.length) ∧ x ∈ cs.getD (w - n) []) := by
  by_cases hop : g.op = GateOp.or
  · simp [orStep, List.getD_eq_getElem?_getD, hop]
  · simp [orStep, List.getD_eq_getElem?_getD, hop]

lemma orStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
    (orStep n cs g).getD m [] = cs.getD m [] := by
  simp [orStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]

lemma orFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
    (hk : k < cs.length) :
    (gs.foldl (orStep n) cs).getD k [] = cs.getD k [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (orStep n cs g) (by simp [orStep]; omega)]
    exact orStep_getD_lt n cs g k hk

lemma orReaches_iff (n : ℕ) (C : Circuit) (g k : ℕ) (hk : k < C.gates.length) :
    OrReaches n C (n + k) g ↔ g = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧ OrReaches n C w g) := by
  obtain ⟨pre, post, gk, hgs, hpre_len, hgk⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gk := by rw [gateAt_eq C k hk]; exact hgk
  rw [hga]
  have hc : orSets n C = post.foldl (orStep n) (orStep n (pre.foldl (orStep n) []) gk) := by
    simp only [orSets]
    rw [hgs, List.foldl_append, List.foldl_cons]
  have hl0 : (pre.foldl (orStep n) []).length = k := by
    rw [orFold_length]; simp [hpre_len]
  have hl1 : (orStep n (pre.foldl (orStep n) []) gk).length = k + 1 := by
    simp [orStep, hl0]
  have h1 : ∀ x, x ∈ (orSets n C).getD k [] ↔ x = k ∨ (gk.op = GateOp.or ∧
      ∃ w, (w ∈ gk.inputs ∧ n ≤ w ∧ w < n + k) ∧
        x ∈ (pre.foldl (orStep n) []).getD (w - n) []) := by
    intro x
    rw [hc, orFold_getD_lt n post _ k (by omega)]
    have h := orStep_mem_last n (pre.foldl (orStep n) []) gk x
    rw [hl0] at h
    exact h
  have h2 : ∀ m, m < k → (orSets n C).getD m [] = (pre.foldl (orStep n) []).getD m [] := by
    intro m hm
    rw [hc, orFold_getD_lt n post _ m (by omega)]
    exact orStep_getD_lt n _ gk m (by omega)
  have e : n + k - n = k := by omega
  unfold OrReaches
  rw [e, h1 g]
  constructor
  · rintro ⟨_, h | ⟨hop, w, ⟨hw, hn, hlt⟩, h⟩⟩
    · exact Or.inl h
    · right
      refine ⟨hop, w, hw, hn, hlt, hn, ?_⟩
      rw [h2 (w - n) (by omega)]
      exact h
  · rintro (h | ⟨hop, w, hw, hn, hlt, _, h⟩)
    · exact ⟨by omega, Or.inl h⟩
    · refine ⟨by omega, Or.inr ⟨hop, w, ⟨hw, hn, hlt⟩, ?_⟩⟩
      rw [← h2 (w - n) (by omega)]
      exact h

theorem snoc_rel {α : Type} (R : α → α → Prop) (z : α) (hz : R z z) {l l' : List α} {a b : α}
    (hl : l.length = l'.length) (h : ∀ i, R (l.getD i z) (l'.getD i z)) (hab : R a b) (i : ℕ) :
    R ((l ++ [a]).getD i z) ((l' ++ [b]).getD i z) := by
  by_cases hi : i < l'.length
  · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ hi]
    exact h i
  · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), hl]
    by_cases h0 : i - l'.length = 0
    · rw [h0]
      simp only [List.getD_cons_zero]
      exact hab
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
      exact hz

theorem all_mono (w w' : List Bool) (h : ∀ i, w.getD i false = true → w'.getD i false = true) (ins : List ℕ) :
    (ins.map fun i => w.getD i false).all id = true → (ins.map fun i => w'.getD i false).all id = true := by
  induction ins with
  | nil => intro _; rfl
  | cons a t ih =>
    simp only [List.map_cons, List.all_cons, Bool.and_eq_true, id_eq]
    exact fun hh => ⟨h a hh.1, ih hh.2⟩

theorem any_mono (w w' : List Bool) (h : ∀ i, w.getD i false = true → w'.getD i false = true) (ins : List ℕ) :
    (ins.map fun i => w.getD i false).any id = true → (ins.map fun i => w'.getD i false).any id = true := by
  induction ins with
  | nil => intro hh; exact hh
  | cons a t ih =>
    simp only [List.map_cons, List.any_cons, Bool.or_eq_true, id_eq]
    exact fun hh => hh.elim (fun h1 => Or.inl (h a h1)) (fun h2 => Or.inr (ih h2))

def evg (g : Gate) (w : List Bool) : Bool := g.op.eval (g.inputs.map fun i => w.getD i false)

def runW (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem evg_mono (w w' : List Bool) (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or)
    (h : ∀ i, w.getD i false = true → w'.getD i false = true) :
    evg g w = true → evg g w' = true := by
  rcases hg with hg | hg
  · unfold evg
    rw [hg]
    exact all_mono w w' h g.inputs
  · unfold evg
    rw [hg]
    exact any_mono w w' h g.inputs

theorem run_mono : ∀ (gs : List Gate) (w w' : List Bool),
    w.length = w'.length → (∀ i, w.getD i false = true → w'.getD i false = true) →
      (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
        ∀ i, (runW gs w).getD i false = true → (runW gs w').getD i false = true
  | [], _, _, _, h, _ => h
  | g :: gs, w, w', hl, h, hg => by
    have h1 := evg_mono w w' g (hg g (by simp)) h
    exact run_mono gs (w ++ [evg g w]) (w' ++ [evg g w'])
      (by simp [hl]) (snoc_rel (fun a b : Bool => a = true → b = true) false (fun hh => hh) hl h h1)
      (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg'))

theorem wires_mono (C : Circuit) (hC : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    {n : ℕ} (x y : Fin n → Bool) (h : ∀ k, x k = true → y k = true) (i : ℕ) :
    (C.wires (List.ofFn x)).getD i false = true → (C.wires (List.ofFn y)).getD i false = true := by
  refine run_mono C.gates (List.ofFn x) (List.ofFn y) (by simp) ?_ hC i
  intro k
  by_cases hk : k < n
  · have e : ∀ z : Fin n → Bool, (List.ofFn z).getD k false = z ⟨k, hk⟩ := fun z => by
      simp [List.getD_eq_getElem?_getD, hk]
    rw [e x, e y]
    exact h _
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    intro hh
    exact (Bool.false_ne_true hh).elim

lemma orSets_len (n : ℕ) (C : Circuit) : (orSets n C).length = C.gates.length := by
  unfold orSets
  rw [orFold_length]
  simp

lemma reach_up (n : ℕ) (C : Circuit) (x : Fin n → Bool) (g : ℕ)
    (hg : val C.gates (n + g) x = true) :
    ∀ m w, w < m → OrReaches n C w g → val C.gates w x = true := by
  intro m
  induction m with
  | zero => intro w hw; omega
  | succ m ih =>
    intro w hw hr
    have hn : n ≤ w := hr.1
    have hk : w - n < C.gates.length := by
      by_contra hc
      have h2 := hr.2
      rw [List.getD_eq_default _ _ (by rw [orSets_len]; omega)] at h2
      simp at h2
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    have hk2 : k < C.gates.length := by omega
    rcases (orReaches_iff n C g k hk2).1 hr with h | ⟨hop, w2, hw2, _, hlt, hr2⟩
    · rw [← h]; exact hg
    · rw [gateAt_eq C k hk2] at hop hw2
      exact (val_or C.gates x k hk2 hop).2 ⟨w2, hw2, hlt, ih w2 (by omega) hr2⟩

lemma orIn_true (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) (i : Fin n)
    (hi : i ∈ orIn n C w) (hx : x i = true) : val C.gates w x = true := by
  simp only [orIn, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  rcases hi with h | ⟨k, hk, hr, hop, hin⟩
  · rw [← h, val_input _ _ _ i.isLt]; exact hx
  · apply reach_up n C x k ?_ (w + 1) w (by omega) hr
    rw [gateAt_eq C k hk] at hop hin
    exact (val_or C.gates x k hk hop).2
      ⟨i.val, hin, by omega, by rw [val_input _ _ _ i.isLt]; exact hx⟩

lemma wireVal_eq (n : ℕ) (C : Circuit) (w : ℕ) (x : Fin n → Bool) :
    PEqualNP.CleanedNonEdge.wireVal n C w x = val C.gates w x := rfl

end PEqualNP.Outside.L_meta_2480

theorem PEqualNP.Outside.L_meta_2480 : ∀ (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (C : PEqualNP.CircuitLowerBounds.Circuit) (l : Fin M) (K F1 F2 : ℕ), PEqualNP.TopForm.IsAO2 n C → (Function.Injective pw ∧ Function.Injective lw ∧ (∀ p_1 l_1, pw p_1 ≠ lw l_1) ∧ (∀ p_2, pw p_2 < n) ∧ (∀ l_2, lw l_2 < n)) → (∀ (P_1 : Finset (Fin N)) (Y_1 : Finset (Fin M)), P_1.card ≤ 1 → Y_1.card ≤ 2 → (∀ p_3 ∈ P_1, ∀ l_3 ∈ Y_1, ¬ I p_3 l_3) → PEqualNP.MetaComplexity.circuitFun n C (fun k_1 : Fin n => decide (k_1.val ∈ P_1.image pw ∪ Y_1.image lw)) = false) → (∀ z_1 : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n C (K) z_1 = true → PEqualNP.CleanedNonEdge.wireVal n C (F1) z_1 = true → PEqualNP.CleanedNonEdge.wireVal n C (F2) z_1 = true → PEqualNP.MetaComplexity.circuitFun n C z_1 = true) → (∃ i_1 : Fin n, i_1.val = lw l ∧ i_1 ∈ PEqualNP.TopForm.orIn n C (F1)) → (∃ i_2 : Fin n, i_2.val = lw l ∧ i_2 ∈ PEqualNP.TopForm.orIn n C (F2)) → {a_1 | PEqualNP.CleanedNonEdge.wireVal n C (K) (fun k_2 : Fin n => decide (k_2.val = pw a_1)) = true} ⊆ {p_4 | I p_4 l} := by
  intro n N M pw lw I C l K F1 F2 hC _ hS hdom h1 h2 a ha
  obtain ⟨i1, hi1, hm1⟩ := h1
  obtain ⟨i2, hi2, hm2⟩ := h2
  show I a l
  by_contra hna
  have ha2 : (C.wires (List.ofFn (fun k_2 : Fin n => decide (k_2.val = pw a)))).getD K false = true := ha
  have hz := hS {a} {l} (by simp) (by simp) (by
    intro p3 hp3 l3 hl3
    rw [Finset.mem_singleton] at hp3 hl3
    rw [hp3, hl3]
    exact hna)
  have hK := PEqualNP.Outside.L_meta_2480.wires_mono C hC.1
    (fun k_2 : Fin n => decide (k_2.val = pw a))
    (fun k_1 : Fin n => decide (k_1.val ∈ ({a} : Finset (Fin N)).image pw ∪ ({l} : Finset (Fin M)).image lw))
    (by
      intro k hk
      have hk2 : k.val = pw a := by simpa using hk
      simp [hk2]) K ha2
  have hF1 := PEqualNP.Outside.L_meta_2480.orIn_true n C
    (fun k_1 : Fin n => decide (k_1.val ∈ ({a} : Finset (Fin N)).image pw ∪ ({l} : Finset (Fin M)).image lw))
    F1 i1 hm1 (by simp [hi1])
  have hF2 := PEqualNP.Outside.L_meta_2480.orIn_true n C
    (fun k_1 : Fin n => decide (k_1.val ∈ ({a} : Finset (Fin N)).image pw ∪ ({l} : Finset (Fin M)).image lw))
    F2 i2 hm2 (by simp [hi2])
  have h := hdom (fun k_1 : Fin n => decide (k_1.val ∈ ({a} : Finset (Fin N)).image pw ∪ ({l} : Finset (Fin M)).image lw)) hK hF1 hF2
  rw [hz] at h
  exact Bool.false_ne_true h
