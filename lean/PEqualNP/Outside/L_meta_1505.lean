import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

namespace PEqualNP.Outside.L_meta_1505

/-- One evaluation step of `Circuit.wires`. -/
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

theorem foldl_step_length (G : List Gate) (w : List Bool) :
    (G.foldl step w).length = w.length + G.length := by
  induction G generalizing w with
  | nil => simp
  | cons g G ih => rw [List.foldl_cons, ih]; simp [step]; omega

theorem getD_append_lt (l l' : List Bool) (i : ℕ) (hi : i < l.length) :
    (l ++ l').getD i false = l.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem getD_of_length_le (l : List Bool) (i : ℕ) (hi : l.length ≤ i) : l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

theorem foldl_step_getD (G : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (G.foldl step w).getD i false = w.getD i false := by
  induction G generalizing w with
  | nil => rfl
  | cons g G ih =>
    rw [List.foldl_cons, ih _ (by simp [step]; omega)]
    exact getD_append_lt _ _ _ hi

/-- The value of the gate at position `t` of `G` as read in the wires. -/
theorem foldl_step_getD_gate (G : List Gate) (w : List Bool) (t : ℕ) (ht : t < G.length) :
    (G.foldl step w).getD (w.length + t) false =
      (G[t]).op.eval ((G[t]).inputs.map fun i => ((G.take t).foldl step w).getD i false) := by
  have hsplit : G = G.take t ++ G[t] :: G.drop (t + 1) := by
    simp [List.take_append_drop]
  conv_lhs => rw [hsplit, List.foldl_append, List.foldl_cons]
  rw [foldl_step_getD _ _ _ (by simp only [step, List.length_append, List.length_singleton, foldl_step_length, List.length_take, Nat.min_eq_left ht.le]; omega)]
  simp only [step]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp only [foldl_step_length, List.length_take, Nat.min_eq_left ht.le]; omega)]
  simp [foldl_step_length, Nat.min_eq_left ht.le]

/-- The wires a gate's value depends on: all inputs, or the head for `NOT`. -/
def deps (g : Gate) : List ℕ :=
  match g.op with
  | GateOp.not => g.inputs.head?.toList
  | _ => g.inputs

theorem eval_congr (g : Gate) (f f' : ℕ → Bool) (h : ∀ i ∈ deps g, f i = f' i) :
    g.op.eval (g.inputs.map f) = g.op.eval (g.inputs.map f') := by
  obtain ⟨op, l⟩ := g
  cases op with
  | not =>
    cases l with
    | nil => rfl
    | cons a l =>
      simp only [deps, List.head?_cons, Option.toList_some, List.mem_singleton, forall_eq] at h
      simp [GateOp.eval, h]
  | _ =>
    simp only [deps] at h
    rw [List.map_congr_left h]

theorem getD_eraseIdx_lt (l : List Bool) (p i : ℕ) (hi : i < p) :
    (l.eraseIdx p).getD i false = l.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eraseIdx_of_lt hi]

theorem getD_eraseIdx_ge (l : List Bool) (p i : ℕ) (hi : p ≤ i) :
    (l.eraseIdx p).getD i false = l.getD (i + 1) false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eraseIdx_of_ge hi]

/-- Renaming of wire indices after the wire `p` is deleted, its readers sent to `r`. -/
def ren (p r i : ℕ) : ℕ := if i < p then i else if i = p then r else i - 1

def renG (p r : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (ren p r)⟩

/-- The gates with gate `t` (wire `p`) deleted and the later gates renamed. -/
def del (G : List Gate) (t p r : ℕ) : List Gate := G.take t ++ (G.drop (t + 1)).map (renG p r)

theorem deps_renG (p r : ℕ) (g : Gate) : deps (renG p r g) = (deps g).map (ren p r) := by
  obtain ⟨op, l⟩ := g
  cases op <;> cases l <;> simp [deps, renG]

theorem del_foldl_aux (W : List Bool) (p r : ℕ) (hr : r < p ∨ W.length ≤ r) :
    ∀ (L : List Gate) (v : List Bool), L.foldl step v = W → p < v.length →
      (∀ g ∈ L, p ∈ deps g → W.getD p false = W.getD r false) →
      (L.map (renG p r)).foldl step (v.eraseIdx p) = W.eraseIdx p := by
  intro L
  induction L with
  | nil =>
    intro v hW _ _
    simp only [List.foldl_nil] at hW
    subst hW
    rfl
  | cons g L ih =>
    intro v hW hp hv
    rw [List.foldl_cons] at hW
    rw [List.map_cons, List.foldl_cons]
    have hvW : ∀ i, i < v.length → v.getD i false = W.getD i false := fun i hi => by
      rw [← hW, foldl_step_getD _ _ _ (by simp only [step, List.length_append, List.length_singleton]; omega)]
      exact (getD_append_lt _ _ _ hi).symm
    have hWlen : v.length + 1 + L.length = W.length := by
      have := congrArg List.length hW
      rw [foldl_step_length] at this
      simp only [step, List.length_append, List.length_singleton] at this
      omega
    have hstep : step (v.eraseIdx p) (renG p r g) = (step v g).eraseIdx p := by
      simp only [step, renG, List.map_map]
      rw [List.eraseIdx_append_of_lt_length hp]
      congr 2
      apply eval_congr
      intro i hi
      simp only [Function.comp, ren]
      split_ifs with h1 h2
      · exact getD_eraseIdx_lt _ _ _ h1
      · subst h2
        rcases hr with hr | hr
        · rw [getD_eraseIdx_lt _ _ _ hr, hvW _ (by omega), hvW _ hp]
          exact (hv g (by simp) hi).symm
        · rw [getD_of_length_le _ _ (by rw [List.length_eraseIdx_of_lt hp]; omega), hvW _ hp,
            hv g (by simp) hi, getD_of_length_le _ _ hr]
      · rw [getD_eraseIdx_ge _ _ _ (by omega), Nat.sub_add_cancel (by omega)]
    rw [hstep]
    exact ih _ hW (by simp only [step, List.length_append, List.length_singleton]; omega)
      (fun g' hg' => hv g' (List.mem_cons_of_mem _ hg'))

theorem del_foldl (G : List Gate) (x : List Bool) (t r : ℕ) (ht : t < G.length)
    (hr : r < x.length + t ∨ x.length + G.length ≤ r)
    (hv : ∀ g ∈ G.drop (t + 1), x.length + t ∈ deps g →
      (G.foldl step x).getD (x.length + t) false = (G.foldl step x).getD r false) :
    (del G t (x.length + t) r).foldl step x = (G.foldl step x).eraseIdx (x.length + t) := by
  have hsplit : G = G.take t ++ G[t] :: G.drop (t + 1) := by simp
  have hWlen : (G.foldl step x).length = x.length + G.length := foldl_step_length _ _
  have hW' : (G.drop (t + 1)).foldl step (step ((G.take t).foldl step x) G[t]) = G.foldl step x := by
    conv_rhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
  have hlen : ((G.take t).foldl step x).length = x.length + t := by
    rw [foldl_step_length, List.length_take, Nat.min_eq_left ht.le]
  have hv0 : (G.take t).foldl step x = (step ((G.take t).foldl step x) G[t]).eraseIdx (x.length + t) := by
    simp only [step]
    rw [List.eraseIdx_append_of_length_le (by omega)]
    simp [hlen]
  unfold del
  rw [List.foldl_append, hv0]
  exact del_foldl_aux _ (x.length + t) r (by rwa [hWlen]) _ _ hW'
    (by simp only [step, List.length_append, List.length_singleton, hlen]; omega) hv

theorem del_eval (G : List Gate) (o : ℕ) (x : List Bool) (t r : ℕ) (ht : t < G.length)
    (hr : r < x.length + t ∨ x.length + G.length ≤ r)
    (hv : ∀ g ∈ G.drop (t + 1), x.length + t ∈ deps g →
      (G.foldl step x).getD (x.length + t) false = (G.foldl step x).getD r false)
    (ho : o = x.length + t → (G.foldl step x).getD (x.length + t) false = (G.foldl step x).getD r false) :
    Circuit.eval ⟨del G t (x.length + t) r, ren (x.length + t) r o⟩ x = Circuit.eval ⟨G, o⟩ x := by
  simp only [Circuit.eval, wires_eq]
  rw [del_foldl G x t r ht hr hv]
  unfold ren
  split_ifs with h1 h2
  · exact getD_eraseIdx_lt _ _ _ h1
  · subst h2
    rcases hr with hr | hr
    · rw [getD_eraseIdx_lt _ _ _ hr]
      exact (ho rfl).symm
    · rw [getD_of_length_le _ _ (by rw [List.length_eraseIdx_of_lt (by rw [foldl_step_length]; omega), foldl_step_length]; omega),
        ho rfl, getD_of_length_le _ _ (by rw [foldl_step_length]; exact hr)]
  · rw [getD_eraseIdx_ge _ _ _ (by omega), Nat.sub_add_cancel (by omega)]

theorem del_length (G : List Gate) (t p r : ℕ) (ht : t < G.length) :
    (del G t p r).length = G.length - 1 := by
  simp only [del, List.length_append, List.length_take, List.length_map, List.length_drop]
  omega
theorem foldl_take_getD (G : List Gate) (w : List Bool) (t i : ℕ)
    (hi : i < ((G.take t).foldl step w).length) :
    (G.foldl step w).getD i false = ((G.take t).foldl step w).getD i false := by
  conv_lhs => rw [← List.take_append_drop t G, List.foldl_append]
  exact foldl_step_getD _ _ _ hi

/-- The value of gate `t`: its operation on the wires it reads, among those that exist. -/
theorem gate_value (G : List Gate) (w : List Bool) (t : ℕ) (ht : t < G.length) :
    (G.foldl step w).getD (w.length + t) false =
      (G[t]).op.eval ((G[t]).inputs.map fun i =>
        if i < w.length + t then (G.foldl step w).getD i false else false) := by
  rw [foldl_step_getD_gate G w t ht]
  congr 1
  apply List.map_congr_left
  intro i _
  have hlen : ((G.take t).foldl step w).length = w.length + t := by
    rw [foldl_step_length, List.length_take, Nat.min_eq_left ht.le]
  split_ifs with h
  · exact (foldl_take_getD G w t i (by rw [hlen]; exact h)).symm
  · exact getD_of_length_le _ _ (by rw [hlen]; omega)

theorem del_getElem_lt (G : List Gate) (t p r t' : ℕ) (h : t' < t) (ht : t < G.length) :
    (del G t p r)[t']'(by rw [del_length G t p r ht]; omega) = G[t']'(by omega) := by
  simp only [del]
  rw [List.getElem_append_left (by simp [List.length_take]; omega), List.getElem_take]

theorem del_getElem_ge (G : List Gate) (t p r t' : ℕ) (h : t ≤ t') (ht : t' + 1 < G.length) :
    (del G t p r)[t']'(by rw [del_length G t p r (by omega)]; omega) = renG p r (G[t' + 1]'ht) := by
  simp only [del]
  rw [List.getElem_append_right (by simp [List.length_take]; omega), List.getElem_map, List.getElem_drop]
  congr 2
  simp [List.length_take]
  omega

section gfold
variable {α β : Type} (H : List α → β → α)

theorem gfold_len (gs : List β) (cs : List α) :
    (gs.foldl (fun cs g => cs ++ [H cs g]) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih => rw [List.foldl_cons, ih]; simp; omega

theorem gfold_getD_lt (gs : List β) (cs : List α) (i : ℕ) (d : α) (hi : i < cs.length) :
    (gs.foldl (fun cs g => cs ++ [H cs g]) cs).getD i d = cs.getD i d := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp; omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem gfold_prefix (gs : List β) (i j : ℕ) (d : α) (hij : i < j) (hj : j ≤ gs.length) :
    ((gs.take j).foldl (fun cs g => cs ++ [H cs g]) []).getD i d =
      (gs.foldl (fun cs g => cs ++ [H cs g]) []).getD i d := by
  conv_rhs => rw [← List.take_append_drop j gs, List.foldl_append]
  rw [gfold_getD_lt H (gs.drop j) _ i d (by rw [gfold_len, List.length_take]; simp; omega)]

theorem gfold_at (gs : List β) (j : ℕ) (d : α) (hj : j < gs.length) :
    (gs.foldl (fun cs g => cs ++ [H cs g]) []).getD j d =
      H ((gs.take j).foldl (fun cs g => cs ++ [H cs g]) []) gs[j] := by
  have hsplit : gs = gs.take j ++ gs[j] :: gs.drop (j + 1) := by simp
  conv_lhs => rw [hsplit, List.foldl_append, List.foldl_cons]
  have hlen : ((gs.take j).foldl (fun cs g => cs ++ [H cs g]) []).length = j := by
    rw [gfold_len, List.length_take]; simp; omega
  rw [gfold_getD_lt _ _ _ _ _ (by simp [hlen])]
  simp [List.getD_eq_getElem?_getD, hlen]

theorem gfold_ge (gs : List β) (j : ℕ) (d : α) (hj : gs.length ≤ j) :
    (gs.foldl (fun cs g => cs ++ [H cs g]) []).getD j d = d := by
  simp [List.getD_eq_getElem?_getD, gfold_len, hj]

theorem gfold_take_len (gs : List β) (j : ℕ) (hj : j ≤ gs.length) :
    ((gs.take j).foldl (fun cs g => cs ++ [H cs g]) []).length = j := by
  rw [gfold_len, List.length_take]; simp; omega
end gfold

theorem gateAt_eq (C : Circuit) (j : ℕ) (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]

/-- The new entry `orStep` appends. -/
def Hor (n : ℕ) (cs : List (List ℕ)) (g : Gate) : List ℕ := ((orStep n cs g).drop cs.length).headD []

theorem orStep_eq (n : ℕ) : orStep n = fun cs g => cs ++ [Hor n cs g] := by
  funext cs g
  simp [Hor, orStep]

theorem mem_Hor (n : ℕ) (cs : List (List ℕ)) (g : Gate) (k : ℕ) :
    k ∈ Hor n cs g ↔ k = cs.length ∨ (g.op = GateOp.or ∧
      ∃ w ∈ g.inputs, n ≤ w ∧ w < n + cs.length ∧ k ∈ cs.getD (w - n) []) := by
  simp only [Hor, orStep, List.drop_left', List.headD_cons, List.mem_cons]
  apply or_congr Iff.rfl
  split_ifs with hor
  · simp only [hor, true_and, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro ⟨w, ⟨hw, h1, h2⟩, hk⟩; exact ⟨w, hw, h1, h2, hk⟩
    · rintro ⟨w, hw, h1, h2, hk⟩; exact ⟨w, ⟨hw, h1, h2⟩, hk⟩
  · simp [hor]

theorem mem_orSets (n : ℕ) (C : Circuit) (j k : ℕ) (hj : j < C.gates.length) :
    k ∈ (orSets n C).getD j [] ↔ k = j ∨ ((gateAt C j).op = GateOp.or ∧
      ∃ w ∈ (gateAt C j).inputs, n ≤ w ∧ w < n + j ∧ k ∈ (orSets n C).getD (w - n) []) := by
  have e : orSets n C = C.gates.foldl (fun cs g => cs ++ [Hor n cs g]) [] := by
    rw [← orStep_eq]; rfl
  rw [e, gfold_at _ _ _ _ hj, mem_Hor, gfold_take_len _ _ _ hj.le, ← gateAt_eq C j hj]
  apply or_congr Iff.rfl
  apply and_congr Iff.rfl
  constructor
  · rintro ⟨w, hw, h1, h2, hk⟩
    exact ⟨w, hw, h1, h2, by rwa [gfold_prefix _ _ _ _ _ (by omega) hj.le] at hk⟩
  · rintro ⟨w, hw, h1, h2, hk⟩
    exact ⟨w, hw, h1, h2, by rwa [gfold_prefix _ _ _ _ _ (by omega) hj.le]⟩

theorem orSets_ge (n : ℕ) (C : Circuit) (j : ℕ) (hj : C.gates.length ≤ j) :
    (orSets n C).getD j [] = [] := by
  have e : orSets n C = C.gates.foldl (fun cs g => cs ++ [Hor n cs g]) [] := by
    rw [← orStep_eq]; rfl
  rw [e]; exact gfold_ge _ _ _ _ hj

theorem mem_cones (n : ℕ) (C : Circuit) (i j : ℕ) (hj : j < C.gates.length) :
    i ∈ (cones n C).getD j [] ↔
      ∃ w ∈ (gateAt C j).inputs, n ≤ w ∧ w < n + j ∧ (i = w - n ∨ i ∈ (cones n C).getD (w - n) []) := by
  have e : cones n C = C.gates.foldl (fun cs g => cs ++ [(g.inputs.filter
    (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
      (fun w => (w - n) :: cs.getD (w - n) [])]) [] := rfl
  rw [e, gfold_at _ _ _ _ hj, gfold_take_len _ _ _ hj.le, ← gateAt_eq C j hj]
  simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_cons]
  constructor
  · rintro ⟨w, ⟨hw, h1, h2⟩, hk⟩
    exact ⟨w, hw, h1, h2, by rwa [gfold_prefix _ _ _ _ _ (by omega) hj.le] at hk⟩
  · rintro ⟨w, hw, h1, h2, hk⟩
    exact ⟨w, ⟨hw, h1, h2⟩, by rwa [gfold_prefix _ _ _ _ _ (by omega) hj.le]⟩

/-- OR closure of a gate wire. -/
theorem orR_gate (n : ℕ) (C : Circuit) (j k : ℕ) (hj : j < C.gates.length) :
    OrReaches n C (n + j) k ↔ k = j ∨ ((gateAt C j).op = GateOp.or ∧
      ∃ i ∈ (gateAt C j).inputs, n ≤ i ∧ i < n + j ∧ OrReaches n C i k) := by
  unfold OrReaches
  rw [Nat.add_sub_cancel_left, mem_orSets n C j k hj]
  simp only [le_add_iff_nonneg_right, zero_le, true_and]
  constructor
  · rintro (h | ⟨h1, w, hw, h2, h3, h4⟩)
    · exact Or.inl h
    · exact Or.inr ⟨h1, w, hw, h2, h3, h2, h4⟩
  · rintro (h | ⟨h1, w, hw, h2, h3, _, h4⟩)
    · exact Or.inl h
    · exact Or.inr ⟨h1, w, hw, h2, h3, h4⟩

theorem orR_lt (n : ℕ) (C : Circuit) (w k : ℕ) (h : OrReaches n C w k) :
    n ≤ w ∧ w - n < C.gates.length := by
  refine ⟨h.1, ?_⟩
  by_contra hc
  have := h.2
  rw [orSets_ge n C _ (by omega)] at this
  simp at this

theorem reach_le (n : ℕ) (C : Circuit) (k : ℕ) : ∀ v, OrReaches n C v k →
    n ≤ v ∧ v - n < C.gates.length ∧ k ≤ v - n := by
  intro v
  induction v using Nat.strong_induction_on with
  | _ v ih =>
    intro h
    obtain ⟨hn, hL⟩ := orR_lt n C v k h
    obtain ⟨j, rfl⟩ : ∃ j, v = n + j := ⟨v - n, by omega⟩
    rw [Nat.add_sub_cancel_left] at hL ⊢
    refine ⟨hn, hL, ?_⟩
    rcases (orR_gate n C j k hL).1 h with h1 | ⟨_, i, _, hin, hlt, hr⟩
    · omega
    · have := (ih i hlt hr).2.2; omega

theorem reach_cone (n : ℕ) (C : Circuit) (k : ℕ) : ∀ v, OrReaches n C v k →
    k = v - n ∨ InCone n C k (v - n) := by
  intro v
  induction v using Nat.strong_induction_on with
  | _ v ih =>
    intro h
    obtain ⟨hn, hL⟩ := orR_lt n C v k h
    obtain ⟨j, rfl⟩ : ∃ j, v = n + j := ⟨v - n, by omega⟩
    rw [Nat.add_sub_cancel_left] at hL ⊢
    rcases (orR_gate n C j k hL).1 h with h1 | ⟨_, i, hi, hin, hlt, hr⟩
    · exact Or.inl h1
    · right
      unfold InCone
      exact (mem_cones n C k j hL).2 ⟨i, hi, hin, hlt, ih i hlt hr⟩

theorem wire_gate {n : ℕ} (C : Circuit) (hRB : ReadsBack n C) (j : ℕ) (hj : j < C.gates.length)
    (x : Fin n → Bool) :
    wireVal n C (n + j) x = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => wireVal n C i x) := by
  unfold wireVal
  rw [wires_eq]
  have h := gate_value C.gates (List.ofFn x) j hj
  rw [List.length_ofFn] at h
  rw [h, gateAt_eq C j hj]
  congr 1
  apply List.map_congr_left
  intro i hi
  have := hRB j hj i (by rw [gateAt_eq C j hj]; exact hi)
  simp [this]

theorem orIn_input {n : ℕ} (C : Circuit) (i : ℕ) (hi : i < n) : (orIn n C i).Nonempty :=
  ⟨⟨i, hi⟩, by simp [orIn]⟩

theorem orIn_sub {n : ℕ} (C : Circuit) (i v : ℕ) (hi : n ≤ i)
    (hsub : ∀ k, OrReaches n C i k → OrReaches n C v k) : orIn n C i ⊆ orIn n C v := by
  intro t ht
  simp only [orIn, Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
  rcases ht with h | ⟨k, hk, hr, ho, hm⟩
  · exact absurd h (by have := t.isLt; omega)
  · exact Or.inr ⟨k, hk, hsub k hr, ho, hm⟩

theorem andOr_at {n : ℕ} (C : Circuit) (hAO : IsAO2 n C) (j : ℕ) (hj : j < C.gates.length) :
    ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) ∧ (gateAt C j).inputs.length = 2 := by
  rw [gateAt_eq C j hj]
  exact ⟨hAO.1 _ (List.getElem_mem hj), hAO.2.2 _ (List.getElem_mem hj)⟩

theorem and_ne_or : GateOp.and ≠ GateOp.or := fun h => GateOp.noConfusion h

/-- A gate wire whose OR closure has no input and whose only AND gate is `g` carries `g`. -/
theorem pure_val {n : ℕ} (C : Circuit) (hAO : IsAO2 n C) (g : ℕ) (x : Fin n → Bool) : ∀ v, n ≤ v →
    v < n + C.gates.length → (∀ k, OrReaches n C v k → (gateAt C k).op = GateOp.and → k = g) →
    orIn n C v = ∅ → wireVal n C v x = wireVal n C (n + g) x := by
  intro v
  induction v using Nat.strong_induction_on with
  | _ v ih =>
    intro hn hv hand hempty
    obtain ⟨j, rfl⟩ : ∃ j, v = n + j := ⟨v - n, by omega⟩
    have hj : j < C.gates.length := by omega
    have hself : OrReaches n C (n + j) j := (orR_gate n C j j hj).2 (Or.inl rfl)
    obtain ⟨hop, hlen⟩ := andOr_at C hAO j hj
    rcases hop with hop | hop
    · rw [hand j hself hop]
    · have key : ∀ i ∈ (gateAt C j).inputs, wireVal n C i x = wireVal n C (n + g) x := by
        intro i hi
        have hlt : i < n + j := hAO.2.1 j hj i hi
        have hin : n ≤ i := by
          by_contra hc
          have : ⟨i, by omega⟩ ∈ orIn n C (n + j) := by
            simp only [orIn, Finset.mem_filter, Finset.mem_univ, true_and]
            exact Or.inr ⟨j, hj, hself, hop, hi⟩
          rw [hempty] at this; simp at this
        have hsub : ∀ k, OrReaches n C i k → OrReaches n C (n + j) k := fun k hk =>
          (orR_gate n C j k hj).2 (Or.inr ⟨hop, i, hi, hin, hlt, hk⟩)
        exact ih i hlt hin (by omega) (fun k hk ho => hand k (hsub k hk) ho)
          (Finset.subset_empty.1 (hempty ▸ orIn_sub C i _ hin hsub))
      rw [wire_gate C hAO.2.1 j hj, hop]
      obtain ⟨i0, i1, he⟩ := List.length_eq_two.1 hlen
      rw [he] at key
      have h0 := key i0 (by simp)
      have h1 := key i1 (by simp)
      rw [he]
      simp [GateOp.eval, h0, h1]

/-- In a least circuit no gate carries the same function as an earlier wire. -/
theorem no_dup {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hL : IsLeastAO G C) (m r : ℕ) (hm : m < C.gates.length) (hr : r < n + m)
    (heq : ∀ x : Fin n → Bool, wireVal n C (n + m) x = wireVal n C r x) : False := by
  obtain ⟨hAO, hfun, hmin⟩ := hL
  let C' : Circuit := ⟨del C.gates m (n + m) r, ren (n + m) r C.output⟩
  have hlen : C'.gates.length = C.gates.length - 1 := del_length C.gates m (n + m) r hm
  have hfun' : circuitFun n C' = graphFun G ∅ := by
    rw [← hfun]
    funext x
    have h := del_eval C.gates C.output (List.ofFn x) m r hm
      (by rw [List.length_ofFn]; exact Or.inl hr)
      (fun _ _ _ => by rw [List.length_ofFn]; exact heq x)
      (fun _ => by rw [List.length_ofFn]; exact heq x)
    simp only [List.length_ofFn] at h
    exact h
  have hAO' : IsAO2 n C' := by
    refine ⟨?_, ?_, ?_⟩
    · intro g hg
      simp only [C', del, List.mem_append, List.mem_map] at hg
      rcases hg with hg | ⟨g', hg', rfl⟩
      · exact hAO.1 g (List.mem_of_mem_take hg)
      · exact hAO.1 g' (List.mem_of_mem_drop hg')
    · intro j hj i hi
      rw [gateAt_eq C' j hj] at hi
      by_cases hjm : j < m
      · change i ∈ ((del C.gates m (n + m) r)[j]'hj).inputs at hi
        rw [del_getElem_lt C.gates m (n + m) r j hjm hm] at hi
        exact hAO.2.1 j (by omega) i (by rw [gateAt_eq C j (by omega)]; exact hi)
      · have hj1 : j + 1 < C.gates.length := by
          have : j < C.gates.length - 1 := hlen ▸ hj
          omega
        change i ∈ ((del C.gates m (n + m) r)[j]'hj).inputs at hi
        rw [del_getElem_ge C.gates m (n + m) r j (by omega) hj1] at hi
        simp only [renG, List.mem_map] at hi
        obtain ⟨i', hi', rfl⟩ := hi
        have := hAO.2.1 (j + 1) hj1 i' (by rw [gateAt_eq C (j + 1) hj1]; exact hi')
        unfold ren
        split_ifs <;> omega
    · intro g hg
      simp only [C', del, List.mem_append, List.mem_map] at hg
      rcases hg with hg | ⟨g', hg', rfl⟩
      · exact hAO.2.2 g (List.mem_of_mem_take hg)
      · simpa [renG] using hAO.2.2 g' (List.mem_of_mem_drop hg')
  have := hmin C' hAO' hfun'
  simp only [Circuit.size] at this
  omega

theorem orIn_and {n : ℕ} (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.and) : orIn n C (n + j) = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro t ht
  simp only [orIn, Finset.mem_filter, Finset.mem_univ, true_and] at ht
  rcases ht with h | ⟨k, _, hr, ho, _⟩
  · have := t.isLt; omega
  · rcases (orR_gate n C j k hj).1 hr with rfl | ⟨h2, _⟩
    · exact and_ne_or (hop.symm.trans ho)
    · exact and_ne_or (hop.symm.trans h2)

theorem opnd_mem (C : Circuit) (a : ℕ) (b : Fin 2) (h2 : (gateAt C a).inputs.length = 2) :
    opnd C a b ∈ (gateAt C a).inputs := by
  unfold opnd
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
  simp

theorem main {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hL : IsLeastAO G C) (hT : TopForm G C) (g : ℕ) (hJ : junk G C = {g})
    (a : ℕ) (ha : a ∈ tops G C) (b : Fin 2)
    (hrg : OrReaches n C (opnd C a b) g) (hne : (side (n := n) C a b).Nonempty) :
    ∃ m ∈ mixing G C, OrReaches n C (opnd C a b) m ∧ n + g ∈ (gateAt C m).inputs := by
  have hAO := hL.1
  set w := opnd C a b with hw
  -- facts about g
  have hgJ : g ∈ junk G C := by rw [hJ]; simp
  simp only [junk, gatesWhere, Finset.mem_filter, Finset.mem_range] at hgJ
  obtain ⟨hgL, hgop, -, x0, hx0, hF0⟩ := hgJ
  -- facts about a
  simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] at ha
  obtain ⟨haL, haop, -⟩ := ha
  have hwmem : w ∈ (gateAt C a).inputs := opnd_mem C a b (andOr_at C hAO a haL).2
  have hwlt : w < n + a := hAO.2.1 a haL w hwmem
  -- every AND gate in the closure of w is g
  have hand : ∀ k, OrReaches n C w k → (gateAt C k).op = GateOp.and → k = g := by
    intro k hk hkop
    obtain ⟨hwn, _, hkle⟩ := reach_le n C k w hk
    have hkL : k < C.gates.length := by omega
    have hcone : InCone n C k a := by
      unfold InCone
      exact (mem_cones n C k a haL).2 ⟨w, hwmem, hwn, hwlt, reach_cone n C k w hk⟩
    have hnb : ¬ BelowF G C k := fun hb => hT k hkL a haL hkop hb haop hcone
    have hkJ : k ∈ junk G C := by
      simp only [junk, gatesWhere, Finset.mem_filter, Finset.mem_range]
      refine ⟨hkL, hkop, hkL, ?_⟩
      simp only [BelowF, not_forall] at hnb
      obtain ⟨x, hx, hF⟩ := hnb
      exact ⟨x, hx, by simpa using hF⟩
    rw [hJ] at hkJ; simpa using hkJ
  have hgE : orIn n C (n + g) = ∅ := orIn_and C g hgL hgop
  -- the induction
  suffices H : ∀ v, n ≤ v → (∀ k, OrReaches n C v k → OrReaches n C w k) → OrReaches n C v g →
      (orIn n C v).Nonempty → ∃ m ∈ mixing G C, OrReaches n C v m ∧ n + g ∈ (gateAt C m).inputs from
    H w hrg.1 (fun _ h => h) hrg hne
  intro v
  induction v using Nat.strong_induction_on with
  | _ v ih =>
    intro hn hsub hvg hvne
    obtain ⟨-, hL', -⟩ := reach_le n C g v hvg
    obtain ⟨j, rfl⟩ : ∃ j, v = n + j := ⟨v - n, by omega⟩
    rw [Nat.add_sub_cancel_left] at hL'
    have hself : OrReaches n C (n + j) j := (orR_gate n C j j hL').2 (Or.inl rfl)
    obtain ⟨hop, hlen⟩ := andOr_at C hAO j hL'
    rcases hop with hop | hop
    · rw [orIn_and C j hL' hop] at hvne; simp at hvne
    have hsubi : ∀ i ∈ (gateAt C j).inputs, n ≤ i → ∀ k, OrReaches n C i k → OrReaches n C (n + j) k :=
      fun i hi hin k hk => (orR_gate n C j k hL').2 (Or.inr ⟨hop, i, hi, hin, hAO.2.1 j hL' i hi, hk⟩)
    -- an operand with empty orIn carries g
    have hpure : ∀ i ∈ (gateAt C j).inputs, orIn n C i = ∅ → ∀ x, wireVal n C i x = wireVal n C (n + g) x := by
      intro i hi hiE x
      have hin : n ≤ i := by
        by_contra hc
        have := orIn_input (n := n) C i (by omega)
        rw [hiE] at this; simp at this
      have hlt := hAO.2.1 j hL' i hi
      exact pure_val C hAO g x i hin (show i < n + C.gates.length by omega)
        (fun k hk ho => hand k (hsub k (hsubi i hi hin k hk)) ho) hiE
    by_cases hgin : n + g ∈ (gateAt C j).inputs
    · refine ⟨j, ?_, hself, hgin⟩
      have hgj : n + g < n + j := hAO.2.1 j hL' _ hgin
      obtain ⟨i0, i1, he⟩ := List.length_eq_two.1 hlen
      have hval : ∀ x, wireVal n C (n + j) x = (wireVal n C i0 x || wireVal n C i1 x) := by
        intro x; rw [wire_gate C hAO.2.1 j hL', hop, he]; simp [GateOp.eval]
      simp only [mixing, orN, gatesWhere, Finset.mem_filter, Finset.mem_range]
      refine ⟨⟨hL', hop, ?_⟩, ?_⟩
      · intro hb
        have h1 : gateVal n C j x0 = true := by
          show wireVal n C (n + j) x0 = true
          rw [wire_gate C hAO.2.1 j hL', hop]
          simp only [GateOp.eval, List.any_map, List.any_eq_true]
          exact ⟨n + g, hgin, hx0⟩
        exact absurd (hb x0 h1) (by rw [hF0]; decide)
      · have o0 : opnd C j 0 = i0 := by simp [opnd, he]
        have o1 : opnd C j 1 = i1 := by simp [opnd, he]
        rw [o0, o1]
        intro heqE
        have hboth : orIn n C i0 = ∅ ∧ orIn n C i1 = ∅ := by
          rw [he] at hgin
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hgin
          rcases hgin with h | h
          · subst h; exact ⟨hgE, Eq.mp heqE hgE⟩
          · subst h; exact ⟨Eq.mpr heqE hgE, hgE⟩
        refine no_dup G C hL j (n + g) hL' hgj (fun x => ?_)
        rw [hval, hpure i0 (by simp [he]) hboth.1, hpure i1 (by simp [he]) hboth.2, Bool.or_self]
    · rcases (orR_gate n C j g hL').1 hvg with h | ⟨_, i, hi, hin, hlt, hig⟩
      · rw [h] at hgop; exact absurd (hgop.symm.trans hop) and_ne_or
      have hine : i ≠ n + g := fun h => hgin (h ▸ hi)
      have hiNE : (orIn n C i).Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro hiE
        obtain ⟨-, hiL, hgle⟩ := reach_le n C g i hig
        refine no_dup G C hL (i - n) (n + g) hiL (by omega) (fun x => ?_)
        rw [show n + (i - n) = i by omega]
        exact hpure i hi hiE x
      obtain ⟨m, hm, hrm, hgm⟩ := ih i hlt hin (fun k hk => hsub k (hsubi i hi hin k hk)) hig hiNE
      exact ⟨m, hm, hsubi i hi hin m hrm, hgm⟩

end PEqualNP.Outside.L_meta_1505

theorem PEqualNP.Outside.L_meta_1505 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit),
  PEqualNP.TopForm.NoFourCycle G → G.edgeFinset.Nonempty → PEqualNP.TopForm.IsLeastAO G C →
  PEqualNP.TopForm.TopForm G C → ∀ (g : ℕ), PEqualNP.TopForm.junk G C = {g} →
    (∀ a ∈ PEqualNP.TopForm.tops G C, ∀ b : Fin 2,
      PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C a b) g →
      (PEqualNP.TopForm.side (n := n) C a b).Nonempty →
      ∃ m ∈ PEqualNP.TopForm.mixing G C,
        PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C a b) m ∧
        n + g ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C m).inputs) := by
  intro n G _ C _ _ hL hT g hJ a ha b hrg hne
  exact PEqualNP.Outside.L_meta_1505.main G C hL hT g hJ a ha b hrg hne
