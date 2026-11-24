import Mathlib
import PEqualNP.Defs

namespace PEqualNP.CircuitLowerBounds.L_meta_3266_aux

def rd (g : Gate) : Finset ℕ :=
  match g.op with
  | GateOp.not => (g.inputs.take 1).toFinset
  | _ => g.inputs.toFinset

def dep (d : List (Finset ℕ)) (g : Gate) : Finset ℕ := (rd g).biUnion (fun i => d.getD i ∅)

def stepD (d : List (Finset ℕ)) (g : Gate) : List (Finset ℕ) := d ++ [dep d g]

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem getD_snoc_lt {α : Type} (l : List α) (a d : α) (j : ℕ) (h : j < l.length) :
    (l ++ [a]).getD j d = l.getD j d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq {α : Type} (l : List α) (a d : α) : (l ++ [a]).getD l.length d = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_ge {α : Type} (l : List α) (d : α) (j : ℕ) (h : l.length ≤ j) : l.getD j d = d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem stepW_lt (w : List Bool) (g : Gate) (j : ℕ) (h : j < w.length) :
    (stepW w g).getD j false = w.getD j false := getD_snoc_lt _ _ _ _ h

theorem stepW_eq (w : List Bool) (g : Gate) :
    (stepW w g).getD w.length false = g.op.eval (g.inputs.map fun i => w.getD i false) :=
  getD_snoc_eq _ _ _

theorem stepW_ge (w : List Bool) (g : Gate) (j : ℕ) (h : w.length + 1 ≤ j) :
    (stepW w g).getD j false = false := getD_ge _ _ _ (by simp [stepW]; omega)

theorem stepD_lt (d : List (Finset ℕ)) (g : Gate) (j : ℕ) (h : j < d.length) :
    (stepD d g).getD j ∅ = d.getD j ∅ := getD_snoc_lt _ _ _ _ h

theorem stepD_eq (d : List (Finset ℕ)) (g : Gate) : (stepD d g).getD d.length ∅ = dep d g :=
  getD_snoc_eq _ _ _

theorem stepD_ge (d : List (Finset ℕ)) (g : Gate) (j : ℕ) (h : d.length + 1 ≤ j) :
    (stepD d g).getD j ∅ = ∅ := getD_ge _ _ _ (by simp [stepD]; omega)

theorem len_W (gs : List Gate) (x : List Bool) : (gs.foldl stepW x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp
  | cons g t ih => simp [List.foldl_cons, ih, stepW]; omega

theorem len_D (gs : List Gate) (x : List (Finset ℕ)) : (gs.foldl stepD x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp
  | cons g t ih => simp [List.foldl_cons, ih, stepD]; omega

theorem eval_congr (g : Gate) (w1 w2 : List Bool)
    (h : ∀ i ∈ rd g, w1.getD i false = w2.getD i false) :
    g.op.eval (g.inputs.map fun i => w1.getD i false) =
      g.op.eval (g.inputs.map fun i => w2.getD i false) := by
  obtain ⟨op, inputs⟩ := g
  cases op with
  | not =>
    cases inputs with
    | nil => rfl
    | cons i t =>
      have := h i (by simp [rd])
      simp only [GateOp.eval, List.map_cons, List.headD_cons]
      rw [this]
  | _ =>
    congr 1
    apply List.map_congr_left
    intro i hi
    exact h i (by simpa [rd] using hi)

theorem sem (gs : List Gate) (x5 x6 : List Bool) (d0 : List (Finset ℕ))
    (hl5 : x5.length = d0.length) (hl6 : x6.length = d0.length)
    (h0 : ∀ j, (∀ i ∈ d0.getD j ∅, x5.getD i false = x6.getD i false) →
      x5.getD j false = x6.getD j false) :
    ∀ j, (∀ i ∈ (gs.foldl stepD d0).getD j ∅, x5.getD i false = x6.getD i false) →
      (gs.foldl stepW x5).getD j false = (gs.foldl stepW x6).getD j false := by
  induction gs using List.reverseRecOn with
  | nil => simpa using h0
  | append_singleton l g ih =>
    intro j hj
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil] at hj ⊢
    have e1 : (l.foldl stepW x5).length = (l.foldl stepD d0).length := by
      rw [len_W, len_D, hl5]
    have e2 : (l.foldl stepW x6).length = (l.foldl stepD d0).length := by
      rw [len_W, len_D, hl6]
    rcases lt_trichotomy j (l.foldl stepD d0).length with hlt | heq | hgt
    · rw [stepW_lt _ _ _ (by omega), stepW_lt _ _ _ (by omega)]
      rw [stepD_lt _ _ _ hlt] at hj
      exact ih j hj
    · subst heq
      rw [stepD_eq] at hj
      rw [← e1, stepW_eq, e1, ← e2, stepW_eq]
      apply eval_congr
      intro i hi
      apply ih i
      intro i' hi'
      apply hj
      simp only [dep, Finset.mem_biUnion]
      exact ⟨i, hi, hi'⟩
    · rw [stepW_ge _ _ _ (by omega), stepW_ge _ _ _ (by omega)]

theorem count_step (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    (rd g).card ≤ (if (!g.op.eval [false]) = true then 1 else 0) + 1 := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with h | h | h <;> subst h
  · simp only [rd, GateOp.eval]
    have := List.toFinset_card_le inputs
    simp at hlen ⊢; omega
  · simp only [rd, GateOp.eval]
    have := List.toFinset_card_le inputs
    simp at hlen ⊢; omega
  · simp only [rd, GateOp.eval]
    have := List.toFinset_card_le (inputs.take 1)
    have := List.length_take_le 1 inputs
    simp; omega

theorem card_inv (gs : List Gate) (d0 : List (Finset ℕ)) (h0 : ∀ j, (d0.getD j ∅).card ≤ 1)
    (hF : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      g.inputs.length ≤ 2) :
    ∀ W : Finset ℕ, (W.biUnion fun w => (gs.foldl stepD d0).getD w ∅).card ≤
      W.card + gs.countP (fun g : Gate => !g.op.eval [false]) := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro W
    simp only [List.foldl_nil, List.countP_nil, add_zero]
    calc (W.biUnion fun w => d0.getD w ∅).card ≤ ∑ w ∈ W, (d0.getD w ∅).card :=
          Finset.card_biUnion_le
      _ ≤ W.card • 1 := Finset.sum_le_card_nsmul _ _ _ (fun w _ => h0 w)
      _ = W.card := by simp
  | append_singleton l g ih =>
    intro W
    have hl : ∀ g' ∈ l, _ := fun g' hg' => hF g' (List.mem_append_left _ hg')
    have hg := hF g (by simp)
    have ih' := ih hl
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, List.countP_append]
    set d := l.foldl stepD d0 with hd
    set c := l.countP (fun g : Gate => !g.op.eval [false])
    have hc := count_step g hg
    have hsing : List.countP (fun g : Gate => !g.op.eval [false]) [g] =
        (if (!g.op.eval [false]) = true then 1 else 0) := by
      simp [List.countP_cons]
    rw [hsing]
    by_cases hW : d.length ∈ W
    · have hsub : (W.biUnion fun w => (stepD d g).getD w ∅) ⊆
          ((W.erase d.length) ∪ rd g).biUnion (fun w => d.getD w ∅) := by
        intro x hx
        simp only [Finset.mem_biUnion] at hx ⊢
        obtain ⟨w, hw, hxw⟩ := hx
        rcases lt_trichotomy w d.length with hlt | heq | hgt
        · refine ⟨w, ?_, ?_⟩
          · exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨by omega, hw⟩)
          · rwa [stepD_lt _ _ _ hlt] at hxw
        · subst heq
          rw [stepD_eq] at hxw
          simp only [dep, Finset.mem_biUnion] at hxw
          obtain ⟨i, hi, hxi⟩ := hxw
          exact ⟨i, Finset.mem_union_right _ hi, hxi⟩
        · rw [stepD_ge _ _ _ (by omega)] at hxw
          simp at hxw
      have h1 := Finset.card_le_card hsub
      have h2 := ih' ((W.erase d.length) ∪ rd g)
      have h3 := Finset.card_union_le (W.erase d.length) (rd g)
      have h4 := Finset.card_erase_of_mem hW
      have h5 : 1 ≤ W.card := Finset.card_pos.mpr ⟨_, hW⟩
      omega
    · have hsub : (W.biUnion fun w => (stepD d g).getD w ∅) ⊆
          W.biUnion (fun w => d.getD w ∅) := by
        intro x hx
        simp only [Finset.mem_biUnion] at hx ⊢
        obtain ⟨w, hw, hxw⟩ := hx
        refine ⟨w, hw, ?_⟩
        rcases lt_trichotomy w d.length with hlt | heq | hgt
        · rwa [stepD_lt _ _ _ hlt] at hxw
        · exact absurd (heq ▸ hw) hW
        · rw [stepD_ge _ _ _ (by omega)] at hxw
          simp at hxw
      have h1 := Finset.card_le_card hsub
      have h2 := ih' W
      split_ifs <;> omega

theorem d0_getD (n j : ℕ) :
    ((List.range n).map (fun i => ({i} : Finset ℕ))).getD j ∅ = if j < n then {j} else ∅ := by
  split_ifs with h
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, h]

end PEqualNP.CircuitLowerBounds.L_meta_3266_aux

theorem PEqualNP.Outside.L_meta_3266 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → ∃ (x4 : Finset ℕ), x4.card ≤ List.countP (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => !x5.op.eval [Bool.false]) x2.gates + (1 : ℕ) ∧ ∀ (x5 x6 : List Bool), x5.length = x1 → x6.length = x1 → (∀ x9 ∈ x4, x5.getD x9 Bool.false = x6.getD x9 Bool.false) → x2.eval x5 = x2.eval x6 := by
  intro n C hC
  refine ⟨(C.gates.foldl PEqualNP.CircuitLowerBounds.L_meta_3266_aux.stepD ((List.range n).map (fun i => ({i} : Finset ℕ)))).getD C.output ∅,
    ?_, ?_⟩
  · have h0 : ∀ j, (((List.range n).map (fun i => ({i} : Finset ℕ))).getD j ∅).card ≤ 1 := by
      intro j; rw [PEqualNP.CircuitLowerBounds.L_meta_3266_aux.d0_getD]; split_ifs <;> simp
    have := PEqualNP.CircuitLowerBounds.L_meta_3266_aux.card_inv C.gates _ h0 hC {C.output}
    simpa [add_comm] using this
  · intro x5 x6 h5 h6 hag
    have hb : ∀ j, (∀ i ∈ ((List.range n).map (fun i => ({i} : Finset ℕ))).getD j ∅,
        x5.getD i false = x6.getD i false) → x5.getD j false = x6.getD j false := by
      intro j hj
      rw [PEqualNP.CircuitLowerBounds.L_meta_3266_aux.d0_getD] at hj
      split_ifs at hj with h
      · exact hj j (by simp)
      · rw [PEqualNP.CircuitLowerBounds.L_meta_3266_aux.getD_ge _ _ _ (by omega),
          PEqualNP.CircuitLowerBounds.L_meta_3266_aux.getD_ge _ _ _ (by omega)]
    exact PEqualNP.CircuitLowerBounds.L_meta_3266_aux.sem C.gates x5 x6 _ (by simp [h5]) (by simp [h6]) hb C.output hag
