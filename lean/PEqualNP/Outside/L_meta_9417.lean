import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9417

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

theorem run_length (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega

theorem getD_lt (l : List Bool) (b : Bool) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t false = l.getD t false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_ltz {α : Type} (z : α) (l : List α) (b : α) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t z = l.getD t z := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at' {α : Type} (z : α) (l : List α) (b : α) : (l ++ [b]).getD l.length z = b := by
  simp [List.getD_eq_getElem?_getD]

theorem run_prefix (gs hs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length + gs.length) :
    (run (gs ++ hs) x).getD i false = (run gs x).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, run_snoc, getD_ltz false _ _ _ (by
      rw [run_length, List.length_append]; omega), ih]

theorem run_input (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  have := run_prefix [] gs x i (by simpa using hi)
  simpa [run] using this

theorem run_gate (gs : List Gate) (x : List Bool) : ∀ (j : ℕ) (hj : j < gs.length),
    (run gs x).getD (x.length + j) false = gs[j].op.eval (gs[j].inputs.map fun i =>
      if i < x.length + j then (run gs x).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    have hlen : (run gs x).length = x.length + gs.length := run_length gs x
    have same : ∀ (k : ℕ), k ≤ gs.length → ∀ l : List ℕ,
        (l.map fun i => if i < x.length + k then (run (gs ++ [g]) x).getD i false else false) =
        l.map fun i => if i < x.length + k then (run gs x).getD i false else false := by
      intro k hk l
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · exact run_prefix gs [g] x i (by omega)
      · rfl
    rcases Nat.lt_or_ge j gs.length with h | h
    · rw [List.getElem_append_left h, same j (by omega), run_prefix gs [g] x _ (by omega)]
      exact ih j h
    · have hjj : j = gs.length := by simp at hj; omega
      subst hjj
      have hg : (gs ++ [g])[gs.length] = g := by simp
      rw [hg, same _ le_rfl, run_snoc, ← hlen, getD_at']
      congr 1
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · rfl
      · exact List.getD_eq_default _ _ (by omega)




open PEqualNP.MetaComplexity.NestedCover

theorem orS (n : ℕ) (gs : List Gate) :
    (gs.foldl (CleanedNonEdge.orStep n) []).length = gs.length ∧
    ∀ j (hj : j < gs.length) d, d ∈ (gs.foldl (CleanedNonEdge.orStep n) []).getD j [] ↔
      (d = j ∨ (gs[j].op = GateOp.or ∧ ∃ w ∈ gs[j].inputs, n ≤ w ∧ w < n + j ∧
        d ∈ (gs.foldl (CleanedNonEdge.orStep n) []).getD (w - n) [])) := by
  induction gs using List.reverseRecOn with
  | nil => exact ⟨rfl, fun j hj => by simp at hj⟩
  | append_singleton gs g ih =>
    obtain ⟨h1, h2⟩ := ih
    rw [List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    set r := gs.foldl (CleanedNonEdge.orStep n) [] with hr
    have hold : ∀ i, i < gs.length → (CleanedNonEdge.orStep n r g).getD i [] = r.getD i [] := by
      intro i hi
      exact getD_ltz _ _ _ _ (by omega)
    refine ⟨by simp [CleanedNonEdge.orStep, h1], fun j hj d => ?_⟩
    by_cases hlt : j < gs.length
    · rw [hold j hlt, h2 j hlt d, List.getElem_append_left hlt]
      refine or_congr_right (and_congr_right fun _ => exists_congr fun w =>
        and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun hw => ?_)
      rw [hold _ (by omega)]
    · have hje : j = gs.length := by simp at hj; omega
      subst hje
      have e : (gs ++ [g])[gs.length] = g := by simp
      rw [e]
      have e2 : (CleanedNonEdge.orStep n r g).getD gs.length [] = r.length ::
          (@ite _ (g.op = GateOp.or) (Classical.dec _)
            ((g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + r.length))).flatMap
              (fun w => r.getD (w - n) [])) []) := by
        rw [← h1]
        unfold CleanedNonEdge.orStep
        rw [getD_at']
        congr 1
        split_ifs <;> rfl
      rw [e2, List.mem_cons, h1]
      refine or_congr_right ?_
      split_ifs with ho
      · simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq, ho, true_and]
        refine exists_congr fun w => ?_
        constructor
        · rintro ⟨⟨q1, q2, q3⟩, q4⟩
          exact ⟨q1, q2, q3, by rw [hold _ (by omega)]; exact q4⟩
        · rintro ⟨q1, q2, q3, q4⟩
          rw [hold _ (by omega)] at q4
          exact ⟨⟨q1, q2, q3⟩, q4⟩
      · simp [ho]

theorem gate2 {n : ℕ} {C : Circuit} (h : TopForm.IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) :
    C.gates[j] = gateAt C j ∧ (gateAt C j).inputs = [TopForm.opnd C j 0, TopForm.opnd C j 1] ∧
    TopForm.opnd C j 0 < n + j ∧ TopForm.opnd C j 1 < n + j ∧
    ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) := by
  have e : gateAt C j = C.gates[j] := List.getD_eq_getElem _ _ hj
  have hm : gateAt C j ∈ C.gates := by rw [e]; exact List.getElem_mem hj
  have hl := h.2.2 _ hm
  obtain ⟨s, t, hst⟩ := List.length_eq_two.1 hl
  have hb := h.2.1 j hj
  rw [hst] at hb
  have e0 : TopForm.opnd C j 0 = s := by unfold TopForm.opnd; rw [hst]; rfl
  have e1 : TopForm.opnd C j 1 = t := by unfold TopForm.opnd; rw [hst]; rfl
  refine ⟨e.symm, by rw [hst, e0, e1], by rw [e0]; exact hb s (by simp),
    by rw [e1]; exact hb t (by simp), h.1 _ hm⟩

theorem coneI (n : ℕ) (gs : List Gate) :
    (gs.foldl (EdgeOwnership.coneStep n) []).length = gs.length ∧
    ∀ j (hj : j < gs.length) d, d ∈ (gs.foldl (EdgeOwnership.coneStep n) []).getD j [] ↔
      (∃ w ∈ gs[j].inputs, n ≤ w ∧ w < n + j ∧ (d = w - n ∨
        d ∈ (gs.foldl (EdgeOwnership.coneStep n) []).getD (w - n) [])) := by
  induction gs using List.reverseRecOn with
  | nil => exact ⟨rfl, fun j hj => by simp at hj⟩
  | append_singleton gs g ih =>
    obtain ⟨h1, h2⟩ := ih
    rw [List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    set r := gs.foldl (EdgeOwnership.coneStep n) [] with hr
    have hold : ∀ i, i < gs.length → (EdgeOwnership.coneStep n r g).getD i [] = r.getD i [] := by
      intro i hi
      exact getD_ltz _ _ _ _ (by omega)
    refine ⟨by simp [EdgeOwnership.coneStep, h1], fun j hj d => ?_⟩
    by_cases hlt : j < gs.length
    · rw [hold j hlt, h2 j hlt d, List.getElem_append_left hlt]
      refine exists_congr fun w => and_congr_right fun _ => and_congr_right fun _ =>
        and_congr_right fun hw => ?_
      rw [hold _ (by omega)]
    · have hje : j = gs.length := by simp at hj; omega
      subst hje
      have e : (gs ++ [g])[gs.length] = g := by simp
      rw [e]
      have e2 : (EdgeOwnership.coneStep n r g).getD gs.length [] =
            (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + r.length))).flatMap
              (fun w => (w - n) :: r.getD (w - n) []) := by
        rw [← h1]
        exact getD_at' _ _ _
      rw [e2, List.mem_flatMap]
      simp only [List.mem_filter, decide_eq_true_eq, h1, List.mem_cons]
      refine exists_congr fun w => ?_
      constructor
      · rintro ⟨⟨q1, q2, q3⟩, q4⟩
        exact ⟨q1, q2, q3, by rw [hold _ (by omega)]; exact q4⟩
      · rintro ⟨q1, q2, q3, q4⟩
        rw [hold _ (by omega)] at q4
        exact ⟨⟨q1, q2, q3⟩, q4⟩

theorem cone_trans (n : ℕ) (C : Circuit) : ∀ j, j < C.gates.length → ∀ r i,
    EdgeOwnership.InCone n C r j → EdgeOwnership.InCone n C i r →
    EdgeOwnership.InCone n C i j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj r i hr hi
    obtain ⟨w, q1, q2, q3, q4⟩ := (((coneI n C.gates).2 j hj r)).1 hr
    refine (((coneI n C.gates).2 j hj i)).2 ⟨w, q1, q2, q3, Or.inr ?_⟩
    rcases q4 with rfl | q4
    · exact hi
    · exact ih (w - n) (by omega) (by omega) r i q4 hi

theorem cone_one (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) (d : ℕ) (hd : d < j)
    (h : n + d ∈ (gateAt C j).inputs) : EdgeOwnership.InCone n C d j := by
  have e : gateAt C j = C.gates[j] := List.getD_eq_getElem _ _ hj
  rw [e] at h
  exact (((coneI n C.gates).2 j hj d)).2 ⟨n + d, h, by omega, by omega, Or.inl (by omega)⟩


theorem inI {N : ℕ} (C : Circuit) (i j : Fin N) : j ∈ TopForm.orIn N C i ↔ j = i := by
  simp only [TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (h | ⟨k, _, hr, _⟩)
    · exact Fin.ext h
    · have := hr.1; have := i.isLt; omega
  · intro h; left; rw [h]

theorem inO {N : ℕ} {C : Circuit} (h : TopForm.IsAO2 N C) (j : ℕ) (hj : j < C.gates.length) (ho : (gateAt C j).op = GateOp.or) (i : Fin N) :
    i ∈ TopForm.orIn N C (N + j) ↔ ∃ t : Fin 2, i ∈ TopForm.orIn N C (TopForm.opnd C j t) := by
  obtain ⟨e, hin, h0, h1, _⟩ := gate2 h hj
  obtain ⟨l1, l2⟩ := orS N C.gates
  have mem : ∀ k, CleanedNonEdge.OrReaches N C (N + j) k ↔ k = j ∨ ∃ t : Fin 2, CleanedNonEdge.OrReaches N C (TopForm.opnd C j t) k := by
    intro k
    unfold CleanedNonEdge.OrReaches CleanedNonEdge.orSets
    rw [Nat.add_sub_cancel_left, l2 j hj k, e, hin]
    constructor
    · rintro ⟨_, h | ⟨_, w, hw, h2, h3, h4⟩⟩
      · exact Or.inl h
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl
        · exact Or.inr ⟨0, h2, h4⟩
        · exact Or.inr ⟨1, h2, h4⟩
    · rintro (h | ⟨t, h2, h4⟩)
      · exact ⟨by omega, Or.inl h⟩
      · refine ⟨by omega, Or.inr ⟨ho, TopForm.opnd C j t, ?_, h2, ?_, h4⟩⟩
        · fin_cases t <;> simp
        · fin_cases t <;> assumption
  simp only [TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and, mem]
  constructor
  · rintro (h | ⟨k, hk, rfl | ⟨t, ht⟩, hko, hi⟩)
    · have := i.isLt; omega
    · rw [hin] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with hi | hi
      · exact ⟨0, Or.inl hi⟩
      · exact ⟨1, Or.inl hi⟩
    · exact ⟨t, Or.inr ⟨k, hk, ht, hko, hi⟩⟩
  · rintro ⟨t, h | ⟨k, hk, hr, hko, hi⟩⟩
    · refine Or.inr ⟨j, hj, Or.inl rfl, ho, ?_⟩
      rw [hin, h]
      fin_cases t <;> simp
    · exact Or.inr ⟨k, hk, Or.inr ⟨t, hr⟩, hko, hi⟩

theorem inA {N : ℕ} {C : Circuit} (h : TopForm.IsAO2 N C) (j : ℕ) (hj : j < C.gates.length) (ho : (gateAt C j).op = GateOp.and) (i : Fin N) :
    i ∉ TopForm.orIn N C (N + j) := by
  obtain ⟨e, _⟩ := gate2 h hj
  obtain ⟨l1, l2⟩ := orS N C.gates
  intro hi
  simp only [TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  rcases hi with hi | ⟨k, hk, ⟨_, hr⟩, hko, _⟩
  · have := i.isLt; omega
  · unfold CleanedNonEdge.orSets at hr
    rw [Nat.add_sub_cancel_left, l2 j hj k, e] at hr
    rcases hr with rfl | ⟨h2, _⟩
    · rw [ho] at hko; cases hko
    · rw [ho] at h2; cases h2

theorem opl {N : ℕ} {C : Circuit} (h : TopForm.IsAO2 N C) (j : ℕ) (hj : j < C.gates.length) (t : Fin 2) : TopForm.opnd C j t < N + j := by
  obtain ⟨_, _, h0, h1, _⟩ := gate2 h hj
  fin_cases t <;> assumption

theorem gval {N : ℕ} {C : Circuit} (h : TopForm.IsAO2 N C) (x : List Bool) (hx : x.length = N) (j : ℕ) (hj : j < C.gates.length) :
    PEqualNP.CircuitLowerBounds.wireValue C x (N + j) = (gateAt C j).op.eval [PEqualNP.CircuitLowerBounds.wireValue C x (TopForm.opnd C j 0), PEqualNP.CircuitLowerBounds.wireValue C x (TopForm.opnd C j 1)] := by
  obtain ⟨e, hin, h0, h1, _⟩ := gate2 h hj
  have := run_gate C.gates x j hj
  rw [hx, e, hin] at this
  simp only [List.map_cons, List.map_nil, if_pos h0, if_pos h1] at this
  exact this

theorem or_val {N : ℕ} {C : Circuit} (h : TopForm.IsAO2 N C) (x : List Bool) (hx : x.length = N) (i : Fin N) (hi : x.getD i false = true) :
    ∀ w, w < N + C.gates.length → i ∈ TopForm.orIn N C w → PEqualNP.CircuitLowerBounds.wireValue C x w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hm
    by_cases hwN : w < N
    · have : i = ⟨w, hwN⟩ := (inI C ⟨w, hwN⟩ i).1 hm
      subst this
      exact (run_input C.gates x w (by omega)).trans hi
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_lt hwN)
      have hj : j < C.gates.length := by omega
      obtain ⟨_, _, _, _, ho⟩ := gate2 h hj
      rcases ho with ho | ho
      · exact absurd hm (inA h j hj ho i)
      · obtain ⟨t, ht⟩ := (inO h j hj ho i).1 hm
        have h2 := ih _ (opl h j hj t) (by have := opl h j hj t; omega) ht
        rw [gval h x hx j hj, ho]
        fin_cases t
        · have h2 : PEqualNP.CircuitLowerBounds.wireValue C x (TopForm.opnd C j 0) = true := h2
          simp [GateOp.eval, h2]
        · have h2 : PEqualNP.CircuitLowerBounds.wireValue C x (TopForm.opnd C j 1) = true := h2
          simp [GateOp.eval, h2]


theorem orM {N : ℕ} {C : Circuit} (h : TopForm.IsAO2 N C) (j : ℕ) (hj : j < C.gates.length) (k : ℕ) :
    CleanedNonEdge.OrReaches N C (N + j) k ↔ k = j ∨ ((gateAt C j).op = GateOp.or ∧ ∃ t : Fin 2, CleanedNonEdge.OrReaches N C (TopForm.opnd C j t) k) := by
  obtain ⟨e, hin, h0, h1, _⟩ := gate2 h hj
  obtain ⟨l1, l2⟩ := orS N C.gates
  unfold CleanedNonEdge.OrReaches CleanedNonEdge.orSets
  rw [Nat.add_sub_cancel_left, l2 j hj k, e, hin]
  constructor
  · rintro ⟨_, h | ⟨ho, w, hw, h2, h3, h4⟩⟩
    · exact Or.inl h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact Or.inr ⟨ho, 0, h2, h4⟩
      · exact Or.inr ⟨ho, 1, h2, h4⟩
  · rintro (h | ⟨ho, t, h2, h4⟩)
    · exact ⟨by omega, Or.inl h⟩
    · refine ⟨by omega, Or.inr ⟨ho, TopForm.opnd C j t, ?_, h2, ?_, h4⟩⟩
      · fin_cases t <;> simp
      · fin_cases t <;> assumption

theorem dec {N : ℕ} {C : Circuit} (h : TopForm.IsAO2 N C) (x : List Bool) (hx : x.length = N) :
    ∀ w, w < N + C.gates.length → PEqualNP.CircuitLowerBounds.wireValue C x w = true →
      (∃ i ∈ TopForm.orIn N C w, x.getD i.val false = true) ∨
      ∃ k < C.gates.length, CleanedNonEdge.OrReaches N C w k ∧ (gateAt C k).op = GateOp.and ∧ PEqualNP.CircuitLowerBounds.wireValue C x (N + k) = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hv
    by_cases hwN : w < N
    · exact Or.inl ⟨⟨w, hwN⟩, (inI C ⟨w, hwN⟩ _).2 rfl, (run_input C.gates x w (by omega)).symm.trans hv⟩
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_lt hwN)
      have hj : j < C.gates.length := by omega
      obtain ⟨_, _, _, _, ho⟩ := gate2 h hj
      rcases ho with ho | ho
      · exact Or.inr ⟨j, hj, (orM h j hj j).2 (Or.inl rfl), ho, hv⟩
      · have hv2 := hv
        rw [gval h x hx j hj, ho] at hv2
        have : ∃ t : Fin 2, PEqualNP.CircuitLowerBounds.wireValue C x (TopForm.opnd C j t) = true := by
          simp only [GateOp.eval, List.any_cons, List.any_nil, id, Bool.or_false, Bool.or_eq_true] at hv2
          rcases hv2 with hv2 | hv2
          · exact ⟨0, hv2⟩
          · exact ⟨1, hv2⟩
        obtain ⟨t, ht⟩ := this
        have hl := opl h j hj t
        rcases ih _ hl (by omega) ht with ⟨i, hi, hxi⟩ | ⟨k, hk, hr, hka, hkv⟩
        · exact Or.inl ⟨i, (inO h j hj ho i).2 ⟨t, hi⟩, hxi⟩
        · exact Or.inr ⟨k, hk, (orM h j hj k).2 (Or.inr ⟨ho, t, hr⟩), hka, hkv⟩

theorem reach {N : ℕ} {C : Circuit} (h : TopForm.IsAO2 N C) (x : List Bool) (hx : x.length = N) (k : ℕ)
    (hv : PEqualNP.CircuitLowerBounds.wireValue C x (N + k) = true) :
    ∀ w, w < N + C.gates.length → CleanedNonEdge.OrReaches N C w k → PEqualNP.CircuitLowerBounds.wireValue C x w = true ∧ (k = w - N ∨ EdgeOwnership.InCone N C k (w - N)) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hr
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hr.1
    have hj : j < C.gates.length := by omega
    rcases (orM h j hj k).1 hr with rfl | ⟨ho, t, hr2⟩
    · exact ⟨hv, Or.inl (by omega)⟩
    · have hl := opl h j hj t
      obtain ⟨q1, q2⟩ := ih _ hl (by omega) hr2
      obtain ⟨_, hin, _, _, _⟩ := gate2 h hj
      constructor
      · rw [gval h x hx j hj, ho]
        fin_cases t
        · have q1 : PEqualNP.CircuitLowerBounds.wireValue C x (TopForm.opnd C j 0) = true := q1
          simp [GateOp.eval, q1]
        · have q1 : PEqualNP.CircuitLowerBounds.wireValue C x (TopForm.opnd C j 1) = true := q1
          simp [GateOp.eval, q1]
      · right
        rw [Nat.add_sub_cancel_left]
        have hn := hr2.1
        have c1 : EdgeOwnership.InCone N C (TopForm.opnd C j t - N) j := by
          refine cone_one N C j hj _ (by omega) ?_
          rw [hin, show N + (TopForm.opnd C j t - N) = TopForm.opnd C j t by omega]
          fin_cases t <;> simp
        rcases q2 with rfl | q2
        · exact c1
        · exact cone_trans N C j hj _ _ c1 q2

theorem coneA {N : ℕ} {C : Circuit} (h : TopForm.IsAO2 N C) (a : ℕ) (ha : a < C.gates.length) (t : Fin 2) (k : ℕ)
    (hc : k = TopForm.opnd C a t - N ∨ EdgeOwnership.InCone N C k (TopForm.opnd C a t - N)) (hn : N ≤ TopForm.opnd C a t) : EdgeOwnership.InCone N C k a := by
  have hl := opl h a ha t
  obtain ⟨_, hin, _, _, _⟩ := gate2 h ha
  have c1 : EdgeOwnership.InCone N C (TopForm.opnd C a t - N) a := by
    refine cone_one N C a ha _ (by omega) ?_
    rw [hin, show N + (TopForm.opnd C a t - N) = TopForm.opnd C a t by omega]
    fin_cases t <;> simp
  rcases hc with rfl | hc
  · exact c1
  · exact cone_trans N C a ha _ _ c1 hc

theorem aux : True := trivial

end PEqualNP.Outside.L_meta_9417

theorem PEqualNP.Outside.L_meta_9417 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x4 → PEqualNP.TopForm.TopForm x2 x4 → ∀ x7 ∈ PEqualNP.TopForm.tops x2 x4, ∀ (x9 x10 : Fin x1), PEqualNP.EdgeOwnership.gateVal x1 x4 x7 (PEqualNP.EdgeOwnership.pairInput x9 x10) = Bool.true → (∀ x12 ∈ PEqualNP.TopForm.side x4 x7 (0 : Fin (2 : ℕ)) ∪ PEqualNP.TopForm.side x4 x7 (1 : Fin (2 : ℕ)), x12 ∉ s(x9, x10)) → ∃ x13 ∈ PEqualNP.TopForm.junk x2 x4, ∃ x14 ∈ PEqualNP.TopForm.junk x2 x4, x13 ≠ x14 ∧ PEqualNP.CleanedNonEdge.OrReaches x1 x4 (PEqualNP.TopForm.opnd x4 x7 (0 : Fin (2 : ℕ))) x13 ∧ PEqualNP.CleanedNonEdge.OrReaches x1 x4 (PEqualNP.TopForm.opnd x4 x7 (1 : Fin (2 : ℕ))) x14 ∧ ¬PEqualNP.CleanedNonEdge.OrReaches x1 x4 (PEqualNP.TopForm.opnd x4 x7 (1 : Fin (2 : ℕ))) x13 ∧ ¬PEqualNP.CleanedNonEdge.OrReaches x1 x4 (PEqualNP.TopForm.opnd x4 x7 (0 : Fin (2 : ℕ))) x14 ∧ PEqualNP.EdgeOwnership.gateVal x1 x4 x13 (PEqualNP.EdgeOwnership.pairInput x9 x10) = Bool.true ∧ PEqualNP.EdgeOwnership.gateVal x1 x4 x14 (PEqualNP.EdgeOwnership.pairInput x9 x10) = Bool.true := by
  intro n G inst C hA hT a ha u v hv hside
  simp only [PEqualNP.TopForm.tops, PEqualNP.TopForm.gatesWhere, Finset.mem_filter, Finset.mem_range] at ha
  obtain ⟨hal, haop, haF⟩ := ha
  have hlx : ∀ x : Fin n → Bool, (List.ofFn x).length = n := fun x => List.length_ofFn
  have hv' : PEqualNP.CircuitLowerBounds.wireValue C (List.ofFn (PEqualNP.EdgeOwnership.pairInput u v)) (n + a) = true := hv
  rw [PEqualNP.Outside.L_meta_9417.gval hA _ (hlx _) a hal, haop] at hv'
  simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.all_cons, List.all_nil, id, Bool.and_true, Bool.and_eq_true] at hv'
  have step : ∀ t : Fin 2, PEqualNP.CircuitLowerBounds.wireValue C (List.ofFn (PEqualNP.EdgeOwnership.pairInput u v)) (PEqualNP.TopForm.opnd C a t) = true →
      ∃ k ∈ PEqualNP.TopForm.junk G C, PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C a t) k ∧ PEqualNP.EdgeOwnership.gateVal n C k (PEqualNP.EdgeOwnership.pairInput u v) = true := by
    intro t ht
    have hl := PEqualNP.Outside.L_meta_9417.opl hA a hal t
    rcases PEqualNP.Outside.L_meta_9417.dec hA _ (hlx _) _ (by omega) ht with ⟨i, hi, hxi⟩ | ⟨k, hk, hr, hka, hkv⟩
    · exfalso
      refine hside i ?_ ?_
      · fin_cases t
        · exact Finset.mem_union_left _ hi
        · exact Finset.mem_union_right _ hi
      · rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact i.isLt), List.getElem_ofFn] at hxi
        simpa [PEqualNP.EdgeOwnership.pairInput] using hxi
    · have hc := PEqualNP.Outside.L_meta_9417.coneA hA a hal t k (PEqualNP.Outside.L_meta_9417.reach hA _ (hlx _) k hkv _ (by omega) hr).2 hr.1
      have hnb : ¬ PEqualNP.TopForm.BelowF G C k := fun hb => hT k hk a hal hka hb haop hc
      refine ⟨k, ?_, hr, hkv⟩
      simp only [PEqualNP.TopForm.junk, PEqualNP.TopForm.gatesWhere, Finset.mem_filter, Finset.mem_range]
      refine ⟨hk, hka, hk, ?_⟩
      unfold PEqualNP.TopForm.BelowF at hnb
      push Not at hnb
      obtain ⟨x, h1, h2⟩ := hnb
      exact ⟨x, h1, by simpa using h2⟩
  obtain ⟨j, hj, hjr, hje⟩ := step 0 hv'.1
  obtain ⟨k, hk, hkr, hke⟩ := step 1 hv'.2
  have nob : ∀ j ∈ PEqualNP.TopForm.junk G C, PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C a 0) j → ¬ PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C a 1) j := by
    intro j hj hjr hkr
    simp only [PEqualNP.TopForm.junk, PEqualNP.TopForm.gatesWhere, Finset.mem_filter, Finset.mem_range] at hj
    obtain ⟨_, _, _, x, hx1, hx2⟩ := hj
    have hx1' : PEqualNP.CircuitLowerBounds.wireValue C (List.ofFn x) (n + j) = true := hx1
    have l0 := PEqualNP.Outside.L_meta_9417.opl hA a hal 0
    have l1 := PEqualNP.Outside.L_meta_9417.opl hA a hal 1
    have w0 := (PEqualNP.Outside.L_meta_9417.reach hA _ (hlx x) j hx1' _ (by omega) hjr).1
    have w1 := (PEqualNP.Outside.L_meta_9417.reach hA _ (hlx x) j hx1' _ (by omega) hkr).1
    have hat : PEqualNP.CircuitLowerBounds.wireValue C (List.ofFn x) (n + a) = true := by
      rw [PEqualNP.Outside.L_meta_9417.gval hA _ (hlx _) a hal, haop, w0, w1]; rfl
    have := haF x hat
    rw [hx2] at this
    cases this
  exact ⟨j, hj, k, hk, fun h => nob j hj hjr (h ▸ hkr), hjr, hkr, nob j hj hjr, fun h => nob k hk h hkr, hje, hke⟩
