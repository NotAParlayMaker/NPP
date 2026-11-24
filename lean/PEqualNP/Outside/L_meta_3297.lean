import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3297

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
  PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.FactorSubst

-- A fold that appends one entry per gate.
theorem fs_all {α : Type} (f : List α → Gate → List α) (h : List α → Gate → α)
    (hf : ∀ cs g, f cs g = cs ++ [h cs g]) (x : List α) : ∀ gs : List Gate,
    (gs.foldl f x).length = x.length + gs.length ∧
    (∀ k, k < x.length → (gs.foldl f x)[k]? = x[k]?) ∧
    (∀ k (hk : k < gs.length), (gs.foldl f x)[x.length + k]? =
      some (h ((gs.foldl f x).take (x.length + k)) gs[k])) := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil => simp
  | append_singleton gs g ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil, hf]
    generalize gs.foldl f x = L at h1 h2 h3 ⊢
    refine ⟨?_, ?_, ?_⟩
    · simp [h1]
      omega
    · intro k hk
      rw [List.getElem?_append_left (by omega)]
      exact h2 k hk
    · intro k hk
      simp only [List.length_append, List.length_singleton] at hk
      by_cases hk' : k < gs.length
      · rw [List.getElem?_append_left (by omega), h3 k hk',
          List.take_append_of_le_length (by omega)]
        simp [List.getElem_append_left hk']
      · have e : k = gs.length := by omega
        subst e
        rw [List.getElem?_append_right (by omega)]
        have e2 : x.length + gs.length - L.length = 0 := by omega
        rw [e2, ← h1]
        simp

theorem fs_getD_gate {α : Type} (f : List α → Gate → List α) (h : List α → Gate → α)
    (hf : ∀ cs g, f cs g = cs ++ [h cs g]) (x : List α) (gs : List Gate) (k : ℕ)
    (hk : k < gs.length) (d : α) :
    (gs.foldl f x).getD (x.length + k) d = h ((gs.foldl f x).take (x.length + k)) gs[k] := by
  rw [List.getD_eq_getElem?_getD, (fs_all f h hf x gs).2.2 k hk]
  rfl

theorem fs_getD_in {α : Type} (f : List α → Gate → List α) (h : List α → Gate → α)
    (hf : ∀ cs g, f cs g = cs ++ [h cs g]) (x : List α) (gs : List Gate) (k : ℕ)
    (hk : k < x.length) (d : α) :
    (gs.foldl f x).getD k d = x.getD k d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, (fs_all f h hf x gs).2.1 k hk]

theorem fs_getD_out {α : Type} (f : List α → Gate → List α) (h : List α → Gate → α)
    (hf : ∀ cs g, f cs g = cs ++ [h cs g]) (x : List α) (gs : List Gate) (k : ℕ)
    (hk : x.length + gs.length ≤ k) (d : α) :
    (gs.foldl f x).getD k d = d := by
  rw [List.getD_eq_getElem?_getD,
    List.getElem?_eq_none (by rw [(fs_all f h hf x gs).1]; exact hk)]
  rfl

theorem getD_take {α : Type} (L : List α) (m i : ℕ) (d : α) :
    (L.take m).getD i d = if i < m then L.getD i d else d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take]
  split_ifs <;> rfl

def wstep (w : List Bool) (g : Gate) : Bool := g.op.eval (g.inputs.map fun i => w.getD i false)

theorem wires_eq (C : Circuit) (X : List Bool) :
    C.wires X = C.gates.foldl (fun w g => w ++ [wstep w g]) X := rfl

theorem gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) :
    gateAt C k = C.gates[k] := by
  unfold gateAt
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
  rfl

theorem wv_gate (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length) :
    wireVal n C (n + k) x = (gateAt C k).op.eval ((gateAt C k).inputs.map fun i =>
      if i < n + k then wireVal n C i x else false) := by
  have e := fs_getD_gate (fun w g => w ++ [wstep w g]) wstep (fun _ _ => rfl) (List.ofFn x)
    C.gates k hk false
  rw [List.length_ofFn] at e
  unfold wireVal
  rw [wires_eq, e, gateAt_eq C k hk]
  unfold wstep
  congr 1
  apply List.map_congr_left
  intro i _
  rw [getD_take]

theorem wv_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    wireVal n C i x = x ⟨i, hi⟩ := by
  have e := fs_getD_in (fun w g => w ++ [wstep w g]) wstep (fun _ _ => rfl) (List.ofFn x)
    C.gates i (by simpa using hi) false
  unfold wireVal
  rw [wires_eq, e]
  simp [List.getD_eq_getElem?_getD, hi]

theorem wv_out (n : ℕ) (C : Circuit) (x : Fin n → Bool) (i : ℕ)
    (hi : n + C.gates.length ≤ i) : wireVal n C i x = false := by
  have e := fs_getD_out (fun w g => w ++ [wstep w g]) wstep (fun _ _ => rfl) (List.ofFn x)
    C.gates i (by simpa using hi) false
  unfold wireVal
  rw [wires_eq, e]

theorem wv_rb (n : ℕ) (C : Circuit) (x : Fin n → Bool) (hRB : ReadsBack n C) (k : ℕ)
    (hk : k < C.gates.length) :
    wireVal n C (n + k) x = (gateAt C k).op.eval ((gateAt C k).inputs.map fun i =>
      wireVal n C i x) := by
  rw [wv_gate n C x k hk]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [if_pos (hRB k hk i hi)]

def ostep (n : ℕ) (cs : List (List ℕ)) (g : Gate) : List ℕ := (orStep n cs g).getD cs.length []

theorem ostep_eq (n : ℕ) (cs : List (List ℕ)) (g : Gate) :
    orStep n cs g = cs ++ [ostep n cs g] := by
  unfold ostep orStep
  simp [List.getD_eq_getElem?_getD]

theorem ostep_mem (n : ℕ) (cs : List (List ℕ)) (g : Gate) (i : ℕ) : i ∈ ostep n cs g ↔
    i = cs.length ∨ (g.op = GateOp.or ∧ ∃ v ∈ g.inputs, (n ≤ v ∧ v < n + cs.length) ∧
      i ∈ cs.getD (v - n) []) := by
  unfold ostep orStep
  by_cases hop : g.op = GateOp.or
  · simp [hop, List.getD_eq_getElem?_getD, List.mem_flatMap, and_assoc]
  · simp [hop, List.getD_eq_getElem?_getD]

theorem os_mem (n : ℕ) (C : Circuit) (w g : ℕ) : g ∈ (orSets n C).getD w [] ↔
    w < C.gates.length ∧ (g = w ∨ ((gateAt C w).op = GateOp.or ∧ ∃ v ∈ (gateAt C w).inputs,
      (n ≤ v ∧ v < n + w) ∧ g ∈ (orSets n C).getD (v - n) [])) := by
  have hO : orSets n C = C.gates.foldl (orStep n) [] := rfl
  have hall := fs_all (orStep n) (ostep n) (ostep_eq n) [] C.gates
  simp only [List.length_nil, zero_add] at hall
  by_cases hw : w < C.gates.length
  · have e := fs_getD_gate (orStep n) (ostep n) (ostep_eq n) [] C.gates w hw []
    simp only [List.length_nil, zero_add] at e
    have hlen : ((C.gates.foldl (orStep n) []).take w).length = w := by
      rw [List.length_take, hall.1]
      omega
    rw [gateAt_eq C w hw, hO, e, ostep_mem, hlen]
    constructor
    · rintro (h | ⟨hop, v, hv, hr, hm⟩)
      · exact ⟨hw, Or.inl h⟩
      · refine ⟨hw, Or.inr ⟨hop, v, hv, hr, ?_⟩⟩
        rwa [getD_take, if_pos (by omega)] at hm
    · rintro ⟨_, h | ⟨hop, v, hv, hr, hm⟩⟩
      · exact Or.inl h
      · refine Or.inr ⟨hop, v, hv, hr, ?_⟩
        rwa [getD_take, if_pos (by omega)]
  · have e := fs_getD_out (orStep n) (ostep n) (ostep_eq n) [] C.gates w (by simp; omega) []
    rw [hO, e]
    simp [hw]

def cstep (n : ℕ) (cs : List (List ℕ)) (g : Gate) : List ℕ :=
  (coneStep n cs g).getD cs.length []

theorem cstep_eq (n : ℕ) (cs : List (List ℕ)) (g : Gate) :
    coneStep n cs g = cs ++ [cstep n cs g] := by
  unfold cstep coneStep
  simp [List.getD_eq_getElem?_getD]

theorem cstep_mem (n : ℕ) (cs : List (List ℕ)) (g : Gate) (i : ℕ) : i ∈ cstep n cs g ↔
    ∃ v ∈ g.inputs, (n ≤ v ∧ v < n + cs.length) ∧ (i = v - n ∨ i ∈ cs.getD (v - n) []) := by
  unfold cstep coneStep
  simp [List.getD_eq_getElem?_getD, List.mem_flatMap, and_assoc]

theorem cn_mem (n : ℕ) (C : Circuit) (j i : ℕ) : i ∈ (cones n C).getD j [] ↔
    j < C.gates.length ∧ ∃ v ∈ (gateAt C j).inputs, (n ≤ v ∧ v < n + j) ∧
      (i = v - n ∨ i ∈ (cones n C).getD (v - n) []) := by
  have hO : cones n C = C.gates.foldl (coneStep n) [] := rfl
  have hall := fs_all (coneStep n) (cstep n) (cstep_eq n) [] C.gates
  simp only [List.length_nil, zero_add] at hall
  by_cases hw : j < C.gates.length
  · have e := fs_getD_gate (coneStep n) (cstep n) (cstep_eq n) [] C.gates j hw []
    simp only [List.length_nil, zero_add] at e
    have hlen : ((C.gates.foldl (coneStep n) []).take j).length = j := by
      rw [List.length_take, hall.1]
      omega
    rw [gateAt_eq C j hw, hO, e, cstep_mem, hlen]
    constructor
    · rintro ⟨v, hv, hr, hm⟩
      refine ⟨hw, v, hv, hr, ?_⟩
      rcases hm with hm | hm
      · exact Or.inl hm
      · rw [getD_take, if_pos (by omega)] at hm
        exact Or.inr hm
    · rintro ⟨_, v, hv, hr, hm⟩
      refine ⟨v, hv, hr, ?_⟩
      rcases hm with hm | hm
      · exact Or.inl hm
      · rw [getD_take, if_pos (by omega)]
        exact Or.inr hm
  · have e := fs_getD_out (coneStep n) (cstep n) (cstep_eq n) [] C.gates j (by simp; omega) []
    rw [hO, e]
    simp [hw]

theorem sub_len (C : Circuit) (n c : ℕ) (sigma : ℕ → ℕ) :
    (substReads C n c sigma).gates.length = C.gates.length := by
  simp [substReads]

theorem sub_gate (C : Circuit) (n c : ℕ) (sigma : ℕ → ℕ) (k : ℕ) (hk : k < C.gates.length) :
    gateAt (substReads C n c sigma) k = ⟨(gateAt C k).op, (gateAt C k).inputs.map
      fun i => if i = n + c then sigma k else i⟩ := by
  rw [gateAt_eq _ k (by rw [sub_len]; exact hk), gateAt_eq C k hk]
  simp [substReads]

theorem sub_inputs (C : Circuit) (n c : ℕ) (sigma : ℕ → ℕ) (k : ℕ) (hk : k < C.gates.length) :
    (gateAt (substReads C n c sigma) k).inputs = (gateAt C k).inputs.map
      fun i => if i = n + c then sigma k else i := by
  rw [sub_gate C n c sigma k hk]

theorem sub_op (C : Circuit) (n c : ℕ) (sigma : ℕ → ℕ) (k : ℕ) (hk : k < C.gates.length) :
    (gateAt (substReads C n c sigma) k).op = (gateAt C k).op := by
  rw [sub_gate C n c sigma k hk]

theorem wv_sub (n : ℕ) (C : Circuit) (c : ℕ) (sigma : ℕ → ℕ) (x : Fin n → Bool) (k : ℕ)
    (hk : k < C.gates.length) :
    wireVal n (substReads C n c sigma) (n + k) x = (gateAt C k).op.eval ((gateAt C k).inputs.map
      fun i => if (if i = n + c then sigma k else i) < n + k then
        wireVal n (substReads C n c sigma) (if i = n + c then sigma k else i) x else false) := by
  rw [wv_gate n _ x k (by rw [sub_len]; exact hk), sub_op C n c sigma k hk,
    sub_inputs C n c sigma k hk, List.map_map]
  rfl

theorem memO (n : ℕ) (C : Circuit) (c w : ℕ) : w ∈ orClosure n C c ↔
    w < C.gates.length ∧ w ≠ c ∧ c ∈ (orSets n C).getD w [] := by
  simp only [orClosure, Finset.mem_filter, Finset.mem_range, OrReaches, Nat.add_sub_cancel_left,
    Nat.le_add_right, true_and]

theorem memR (n : ℕ) (C : Circuit) (c r : ℕ) : r ∈ readers n C c ↔
    r < C.gates.length ∧ n + c ∈ (gateAt C r).inputs := by
  simp only [readers, Finset.mem_filter, Finset.mem_range]

theorem memF (n : ℕ) (C : Circuit) (c k : ℕ) : k ∈ frontier n C c ↔
    k < C.gates.length ∧ k ≠ c ∧ k ∉ orClosure n C c ∧
      ∃ w ∈ insert c (orClosure n C c), n + w ∈ (gateAt C k).inputs := by
  simp only [FactorSubst.frontier, Finset.mem_filter, Finset.mem_range]

theorem orR (n : ℕ) (C : Circuit) (w g : ℕ) :
    OrReaches n C (n + w) g ↔ g ∈ (orSets n C).getD w [] := by
  unfold OrReaches
  rw [Nat.add_sub_cancel_left]
  exact ⟨fun h => h.2, fun h => ⟨Nat.le_add_right _ _, h⟩⟩

theorem os_le (n : ℕ) (C : Circuit) : ∀ w g, g ∈ (orSets n C).getD w [] → g ≤ w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro g hg
    rw [os_mem] at hg
    rcases hg with ⟨_, rfl | ⟨_, v, _, ⟨h1, h2⟩, hm⟩⟩
    · exact le_refl _
    · have := ih (v - n) (by omega) g hm
      omega

theorem os_val (n : ℕ) (C : Circuit) (x : Fin n → Bool) (hRB : ReadsBack n C) :
    ∀ w g, g ∈ (orSets n C).getD w [] → wireVal n C (n + g) x = true →
      wireVal n C (n + w) x = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro g hg hv
    rw [os_mem] at hg
    rcases hg with ⟨hw, rfl | ⟨hop, v, hvin, ⟨h1, h2⟩, hm⟩⟩
    · exact hv
    · have h3 := ih (v - n) (by omega) g hm hv
      have e : n + (v - n) = v := by omega
      rw [e] at h3
      rw [wv_rb n C x hRB w hw, hop]
      simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id]
      exact ⟨v, hvin, h3⟩

theorem bool1 : ∀ p q y : Bool, (y = true → q = true) → (p && y) = ((p && q) && y) := by
  decide

theorem bool2 : ∀ p q y : Bool, (y = true → p = true) → (q && y) = ((p && q) && y) := by
  decide

theorem vals (n : ℕ) (C : Circuit) (c a b : ℕ) (sigma : ℕ → ℕ)
    (hAnd : AndOrOnly C) (hRB : ReadsBack n C) (h2 : ∀ g ∈ C.gates, g.inputs.length = 2)
    (hc : c < C.gates.length) (hop : (gateAt C c).op = GateOp.and)
    (hin : (gateAt C c).inputs = [a, b])
    (hsig : ∀ r ∈ readers n C c, sigma r = a ∨ sigma r = b)
    (hfront : ∀ g ∈ frontier n C c, (gateAt C g).op = GateOp.and → ∀ u y : ℕ,
      ((gateAt C g).inputs = [u, y] ∨ (gateAt C g).inputs = [y, u]) →
      (∃ w ∈ insert c (orClosure n C c), u = n + w) →
      (∀ w' ∈ insert c (orClosure n C c), y ≠ n + w') ∧ ∀ r ∈ readers n C c,
        (r = g ∨ OrReaches n C u r) →
        (sigma r = b → ∀ x : Fin n → Bool, wireVal n C y x = true → wireVal n C a x = true) ∧
        (sigma r = a → ∀ x' : Fin n → Bool, wireVal n C y x' = true →
          wireVal n C b x' = true))
    (x : Fin n → Bool) : ∀ i,
    ((∀ w ∈ orClosure n C c, i ≠ n + w) →
      wireVal n (substReads C n c sigma) i x = wireVal n C i x) ∧
    (∀ w ∈ orClosure n C c, i = n + w →
      (wireVal n C i x = true → wireVal n (substReads C n c sigma) i x = true) ∧
      (wireVal n (substReads C n c sigma) i x = true → wireVal n C i x = true ∨
        ∃ r ∈ readers n C c, OrReaches n C i r ∧ wireVal n C (sigma r) x = true)) := by
  have ha : a < n + c := hRB c hc a (by rw [hin]; simp)
  have hb : b < n + c := hRB c hc b (by rw [hin]; simp)
  have cval : wireVal n C (n + c) x = (wireVal n C a x && wireVal n C b x) := by
    rw [wv_rb n C x hRB c hc, hop, hin]
    simp [GateOp.eval]
  have Ogt : ∀ w ∈ orClosure n C c, c < w := by
    intro w hw
    rw [memO] at hw
    have := os_le n C w c hw.2.2
    omega
  have rdr : ∀ r ∈ readers n C c, c < r ∧ sigma r < n + c := by
    intro r hr
    have hr' := (memR n C c r).mp hr
    have := hRB r hr'.1 (n + c) hr'.2
    refine ⟨by omega, ?_⟩
    rcases hsig r hr with e | e <;> rw [e] <;> assumption
  have cfire : ∀ r ∈ readers n C c, ∀ y : ℕ, wireVal n C (sigma r) x = true →
      wireVal n C y x = true →
      ((sigma r = b → ∀ x : Fin n → Bool, wireVal n C y x = true → wireVal n C a x = true) ∧
       (sigma r = a → ∀ x' : Fin n → Bool, wireVal n C y x' = true →
          wireVal n C b x' = true)) →
      wireVal n C (n + c) x = true := by
    intro r hr y hs hy hh
    rw [cval]
    rcases hsig r hr with e | e
    · rw [e] at hs
      rw [hs, hh.2 e x hy]
      rfl
    · rw [e] at hs
      rw [hs, hh.1 e x hy]
      rfl
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    by_cases hi1 : i < n
    · refine ⟨fun _ => by rw [wv_input n _ x i hi1, wv_input n C x i hi1], fun w _ e => by omega⟩
    by_cases hi2 : n + C.gates.length ≤ i
    · refine ⟨fun _ => by rw [wv_out n _ x i (by rw [sub_len]; exact hi2), wv_out n C x i hi2],
        fun w hw e => ?_⟩
      have := ((memO n C c w).mp hw).1
      omega
    obtain ⟨k, rfl⟩ : ∃ k, i = n + k := ⟨i - n, by omega⟩
    have hk : k < C.gates.length := by omega
    have eC := wv_rb n C x hRB k hk
    have eC' := wv_sub n C c sigma x k hk
    have hRBk : ∀ j ∈ (gateAt C k).inputs, j < n + k := hRB k hk
    by_cases hkO : k ∈ orClosure n C c
    · have hkO' := (memO n C c k).mp hkO
      have hopk : (gateAt C k).op = GateOp.or := by
        rcases ((os_mem n C k c).mp hkO'.2.2).2 with e | ⟨e, _⟩
        · exact absurd e.symm hkO'.2.1
        · exact e
      refine ⟨fun hno => absurd rfl (hno k hkO), fun w _ _ => ?_⟩
      rw [eC, eC', hopk]
      simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id]
      constructor
      · rintro ⟨j, hj, hVj⟩
        refine ⟨j, hj, ?_⟩
        by_cases hjc : j = n + c
        · have hkr : k ∈ readers n C c := (memR n C c k).mpr ⟨hk, by rw [← hjc]; exact hj⟩
          obtain ⟨_, hsl⟩ := rdr k hkr
          rw [if_pos hjc, if_pos (by omega),
            (ih (sigma k) (by omega)).1 (fun w hw e => by have := Ogt w hw; omega)]
          rw [hjc, cval] at hVj
          simp only [Bool.and_eq_true] at hVj
          rcases hsig k hkr with e | e
          · rw [e]; exact hVj.1
          · rw [e]; exact hVj.2
        · rw [if_neg hjc, if_pos (hRBk j hj)]
          by_cases hjO : ∃ w ∈ orClosure n C c, j = n + w
          · obtain ⟨w', hw', e⟩ := hjO
            exact ((ih j (hRBk j hj)).2 w' hw' e).1 hVj
          · push_neg at hjO
            rw [(ih j (hRBk j hj)).1 hjO]
            exact hVj
      · rintro ⟨j, hj, hV'j⟩
        by_cases hjc : j = n + c
        · have hkr : k ∈ readers n C c := (memR n C c k).mpr ⟨hk, by rw [← hjc]; exact hj⟩
          obtain ⟨_, hsl⟩ := rdr k hkr
          rw [if_pos hjc, if_pos (by omega),
            (ih (sigma k) (by omega)).1 (fun w hw e => by have := Ogt w hw; omega)] at hV'j
          right
          exact ⟨k, hkr, (orR n C k k).mpr ((os_mem n C k k).mpr ⟨hk, Or.inl rfl⟩), hV'j⟩
        · rw [if_neg hjc, if_pos (hRBk j hj)] at hV'j
          by_cases hjO : ∃ w ∈ orClosure n C c, j = n + w
          · obtain ⟨w', hw', e⟩ := hjO
            rcases ((ih j (hRBk j hj)).2 w' hw' e).2 hV'j with h | ⟨r, hr, hor, hs⟩
            · left
              exact ⟨j, hj, h⟩
            · right
              refine ⟨r, hr, ?_, hs⟩
              rw [orR]
              rw [e, orR] at hor
              have hjlt := hRBk j hj
              exact (os_mem n C k r).mpr ⟨hk, Or.inr ⟨hopk, j, hj, ⟨by omega, hjlt⟩,
                by rw [e, Nat.add_sub_cancel_left]; exact hor⟩⟩
          · push_neg at hjO
            rw [(ih j (hRBk j hj)).1 hjO] at hV'j
            left
            exact ⟨j, hj, hV'j⟩
    · refine ⟨fun _ => ?_, fun w hw e => absurd (show k ∈ orClosure n C c by
        have : k = w := by omega
        rw [this]; exact hw) hkO⟩
      rw [eC', eC]
      by_cases hread : ∃ j ∈ (gateAt C k).inputs, ∃ w ∈ insert c (orClosure n C c), j = n + w
      · obtain ⟨u, hu, w, hw, hwu⟩ := hread
        have hkc : k ≠ c := by
          intro hkc
          rw [hkc, hin] at hu
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
          rcases Finset.mem_insert.mp hw with e | e
          · rcases hu with hu | hu <;> omega
          · have := Ogt w e
            rcases hu with hu | hu <;> omega
        have hcw : c ∈ (orSets n C).getD w [] := by
          rcases Finset.mem_insert.mp hw with e | e
          · rw [e]
            exact (os_mem n C c c).mpr ⟨hc, Or.inl rfl⟩
          · exact ((memO n C c w).mp e).2.2
        have hmemk : gateAt C k ∈ C.gates := by
          rw [gateAt_eq C k hk]
          exact List.getElem_mem hk
        have hopk : (gateAt C k).op = GateOp.and := by
          rcases hAnd (gateAt C k) hmemk with e | e
          · exact e
          · exfalso
            apply hkO
            rw [memO]
            refine ⟨hk, hkc, (os_mem n C k c).mpr ⟨hk, Or.inr ⟨e, u, hu,
              ⟨by omega, hRBk u hu⟩, by rw [hwu, Nat.add_sub_cancel_left]; exact hcw⟩⟩⟩
        have hkF : k ∈ frontier n C c :=
          (memF n C c k).mpr ⟨hk, hkc, hkO, w, hw, by rw [← hwu]; exact hu⟩
        have hlen2 := h2 (gateAt C k) hmemk
        obtain ⟨p, q, hpq⟩ := List.length_eq_two.mp hlen2
        obtain ⟨y, hshape⟩ : ∃ y, (gateAt C k).inputs = [u, y] ∨
            (gateAt C k).inputs = [y, u] := by
          rw [hpq] at hu
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
          rcases hu with hu | hu
          · rw [← hu] at hpq
            exact ⟨q, Or.inl hpq⟩
          · rw [← hu] at hpq
            exact ⟨p, Or.inr hpq⟩
        obtain ⟨hy, hR⟩ := hfront k hkF hopk u y hshape ⟨w, hw, hwu⟩
        have hyin : y ∈ (gateAt C k).inputs := by
          rcases hshape with e | e <;> rw [e] <;> simp
        have hyc : y ≠ n + c := hy c (Finset.mem_insert_self _ _)
        have hyv : (if (if y = n + c then sigma k else y) < n + k then
            wireVal n (substReads C n c sigma) (if y = n + c then sigma k else y) x else false) =
            wireVal n C y x := by
          rw [if_neg hyc, if_pos (hRBk y hyin)]
          exact (ih y (hRBk y hyin)).1 (fun w' hw' => hy w' (Finset.mem_insert_of_mem hw'))
        have huv : ((if (if u = n + c then sigma k else u) < n + k then
            wireVal n (substReads C n c sigma) (if u = n + c then sigma k else u) x else false) &&
            wireVal n C y x) = (wireVal n C u x && wireVal n C y x) := by
          rcases Finset.mem_insert.mp hw with e | e
          · have huc : u = n + c := by rw [hwu, e]
            have hkr : k ∈ readers n C c := (memR n C c k).mpr ⟨hk, by rw [← huc]; exact hu⟩
            obtain ⟨_, hsl⟩ := rdr k hkr
            rw [if_pos huc, if_pos (by omega),
              (ih (sigma k) (by omega)).1 (fun w' hw' e' => by have := Ogt w' hw'; omega),
              huc, cval]
            have hh := hR k hkr (Or.inl rfl)
            rcases hsig k hkr with e2 | e2
            · rw [e2]
              exact bool1 _ _ _ (hh.2 e2 x)
            · rw [e2]
              exact bool2 _ _ _ (hh.1 e2 x)
          · have huc : u ≠ n + c := by
              have := Ogt w e
              omega
            rw [if_neg huc, if_pos (hRBk u hu)]
            have hb' := (ih u (hRBk u hu)).2 w e hwu
            cases hVy : wireVal n C y x
            · simp
            · cases hVu : wireVal n C u x
              · cases hV'u : wireVal n (substReads C n c sigma) u x
                · rfl
                · exfalso
                  rcases hb'.2 hV'u with h | ⟨r, hr, hor, hs⟩
                  · rw [hVu] at h
                    exact Bool.false_ne_true h
                  · have hcf := cfire r hr y hs hVy (hR r hr (Or.inr hor))
                    have := os_val n C x hRB w c hcw hcf
                    rw [← hwu, hVu] at this
                    exact Bool.false_ne_true this
              · rw [hb'.1 hVu]
        rw [hopk]
        rcases hshape with e | e
        · rw [e]
          simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id,
            Bool.and_true]
          rw [hyv]
          exact huv
        · rw [e]
          simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id,
            Bool.and_true]
          rw [hyv, Bool.and_comm, huv]
          exact Bool.and_comm _ _
      · push_neg at hread
        congr 1
        apply List.map_congr_left
        intro j hj
        have hjc : j ≠ n + c := hread j hj c (Finset.mem_insert_self _ _)
        rw [if_neg hjc, if_pos (hRBk j hj)]
        exact (ih j (hRBk j hj)).1 (fun w hw => hread j hj w (Finset.mem_insert_of_mem hw))

theorem cone_sub (n : ℕ) (C : Circuit) (c a b : ℕ) (sigma : ℕ → ℕ) (hRB : ReadsBack n C)
    (hc : c < C.gates.length) (hin : (gateAt C c).inputs = [a, b])
    (hsig : ∀ r ∈ readers n C c, sigma r = a ∨ sigma r = b) :
    ∀ j i, InCone n (substReads C n c sigma) i j → InCone n C i j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro i h
    unfold InCone at h ⊢
    rw [cn_mem] at h ⊢
    obtain ⟨hj, v', hv', ⟨h1, h2⟩, hm⟩ := h
    rw [sub_len] at hj
    rw [sub_inputs C n c sigma j hj] at hv'
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hv'
    by_cases hvc : v = n + c
    · rw [if_pos hvc] at h1 h2 hm
      have hv2 : n + c ∈ (gateAt C j).inputs := by rw [← hvc]; exact hv
      have hjr : j ∈ readers n C c := (memR n C c j).mpr ⟨hj, hv2⟩
      have hsc : sigma j ∈ (gateAt C c).inputs := by
        rw [hin]
        rcases hsig j hjr with e | e <;> rw [e] <;> simp
      have hslt : sigma j < n + c := hRB c hc _ hsc
      have hm' : i = sigma j - n ∨ i ∈ (cones n C).getD (sigma j - n) [] := by
        rcases hm with e | e
        · exact Or.inl e
        · exact Or.inr (ih (sigma j - n) (by omega) i e)
      have hic : i ∈ (cones n C).getD c [] :=
        (cn_mem n C c i).mpr ⟨hc, sigma j, hsc, ⟨h1, hslt⟩, hm'⟩
      have hcj : n + c < n + j := hRB j hj (n + c) hv2
      refine ⟨hj, n + c, hv2, ⟨by omega, hcj⟩, Or.inr ?_⟩
      rw [Nat.add_sub_cancel_left]
      exact hic
    · rw [if_neg hvc] at h1 h2 hm
      rcases hm with e | e
      · exact ⟨hj, v, hv, ⟨h1, h2⟩, Or.inl e⟩
      · exact ⟨hj, v, hv, ⟨h1, h2⟩, Or.inr (ih (v - n) (by omega) i e)⟩

theorem cone_noc (n : ℕ) (C : Circuit) (c a b : ℕ) (sigma : ℕ → ℕ) (hRB : ReadsBack n C)
    (hc : c < C.gates.length) (hin : (gateAt C c).inputs = [a, b])
    (hsig : ∀ r ∈ readers n C c, sigma r = a ∨ sigma r = b) :
    ∀ j, ¬ InCone n (substReads C n c sigma) c j := by
  have ha : a < n + c := hRB c hc a (by rw [hin]; simp)
  have hb : b < n + c := hRB c hc b (by rw [hin]; simp)
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    unfold InCone at h
    rw [cn_mem] at h
    obtain ⟨hj, v', hv', ⟨h1, h2⟩, hm⟩ := h
    rw [sub_len] at hj
    rw [sub_inputs C n c sigma j hj] at hv'
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hv'
    by_cases hvc : v = n + c
    · rw [if_pos hvc] at h1 h2 hm
      have hjr : j ∈ readers n C c := (memR n C c j).mpr ⟨hj, by rw [← hvc]; exact hv⟩
      have hslt : sigma j < n + c := by
        rcases hsig j hjr with e | e <;> rw [e] <;> assumption
      rcases hm with e | e
      · omega
      · exact ih (sigma j - n) (by omega) e
    · rw [if_neg hvc] at h1 h2 hm
      rcases hm with e | e
      · exact hvc (by omega)
      · exact ih (v - n) (by omega) e

theorem main : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (c a b : ℕ) (sigma : ℕ → ℕ), PEqualNP.TopForm.IsAO2 n C → c < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C c).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.MetaComplexity.NestedCover.gateAt C c).inputs = [a, b] → (∀ r ∈ PEqualNP.TopForm.readers n C c, sigma r = a ∨ sigma r = b) → (∀ g ∈ PEqualNP.FactorSubst.frontier n C c, (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ u y : ℕ, ((PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs = [u, y] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs = [y, u]) → (∃ w ∈ insert c (PEqualNP.FactorSubst.orClosure n C c), u = n + w) → (∀ w' ∈ insert c (PEqualNP.FactorSubst.orClosure n C c), y ≠ n + w') ∧ ∀ r ∈ PEqualNP.TopForm.readers n C c, (r = g ∨ PEqualNP.CleanedNonEdge.OrReaches n C u r) → (sigma r = b → ∀ x : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n C y x = true → PEqualNP.CleanedNonEdge.wireVal n C a x = true) ∧ (sigma r = a → ∀ x' : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n C y x' = true → PEqualNP.CleanedNonEdge.wireVal n C b x' = true)) → (∀ g2 ∈ PEqualNP.FactorSubst.frontier n C c, ∀ u2 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C g2).inputs, ∀ r1 ∈ PEqualNP.TopForm.readers n C c, ∀ r2 ∈ PEqualNP.TopForm.readers n C c, PEqualNP.CleanedNonEdge.OrReaches n C u2 r1 → PEqualNP.CleanedNonEdge.OrReaches n C u2 r2 → sigma r1 = sigma r2) → (∀ w3 ∈ insert c (PEqualNP.FactorSubst.orClosure n C c), C.output ≠ n + w3) → c ∈ PEqualNP.FactorSubst.liveGates n C → (∀ k < C.gates.length, k ≠ c → k ∉ PEqualNP.FactorSubst.orClosure n C c → ∀ z : Fin n → Bool, PEqualNP.EdgeOwnership.gateVal n (PEqualNP.FactorSubst.substReads C n c sigma) k z = PEqualNP.EdgeOwnership.gateVal n C k z) ∧ PEqualNP.FactorSubst.liveSize n (PEqualNP.FactorSubst.substReads C n c sigma) + 1 ≤ PEqualNP.FactorSubst.liveSize n C := by
  intro n C c a b sigma hAO hc hop hin hsig hfront hcons hout hlive
  obtain ⟨hAnd, hRB, h2⟩ : AndOrOnly C ∧ ReadsBack n C ∧ ∀ g ∈ C.gates, g.inputs.length = 2 :=
    hAO
  refine ⟨?_, ?_⟩
  · intro k hk hkc hkO z
    exact (vals n C c a b sigma hAnd hRB h2 hc hop hin hsig hfront z (n + k)).1
      (fun w hw e => hkO (by
        have : k = w := by omega
        rw [this]
        exact hw))
  · have hout' : (substReads C n c sigma).output = C.output := rfl
    have hsub : liveGates n (substReads C n c sigma) ⊆ (liveGates n C).erase c := by
      intro j hj
      simp only [liveGates, Finset.mem_filter, Finset.mem_range, Finset.mem_erase, sub_len,
        hout'] at hj ⊢
      obtain ⟨hj1, hj2, hj3⟩ := hj
      refine ⟨?_, hj1, hj2, ?_⟩
      · intro hjc
        rw [hjc] at hj3
        rcases hj3 with e | e
        · exact hout c (Finset.mem_insert_self _ _) (by omega)
        · exact cone_noc n C c a b sigma hRB hc hin hsig _ e
      · rcases hj3 with e | e
        · exact Or.inl e
        · exact Or.inr (cone_sub n C c a b sigma hRB hc hin hsig _ _ e)
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem hlive] at h1
    have hpos : 0 < (liveGates n C).card := Finset.card_pos.mpr ⟨c, hlive⟩
    unfold liveSize
    omega

end PEqualNP.Outside.L_meta_3297

theorem PEqualNP.Outside.L_meta_3297 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (c a b : ℕ) (sigma : ℕ → ℕ), PEqualNP.TopForm.IsAO2 n C → c < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C c).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.MetaComplexity.NestedCover.gateAt C c).inputs = [a, b] → (∀ r ∈ PEqualNP.TopForm.readers n C c, sigma r = a ∨ sigma r = b) → (∀ g ∈ PEqualNP.FactorSubst.frontier n C c, (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ u y : ℕ, ((PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs = [u, y] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs = [y, u]) → (∃ w ∈ insert c (PEqualNP.FactorSubst.orClosure n C c), u = n + w) → (∀ w' ∈ insert c (PEqualNP.FactorSubst.orClosure n C c), y ≠ n + w') ∧ ∀ r ∈ PEqualNP.TopForm.readers n C c, (r = g ∨ PEqualNP.CleanedNonEdge.OrReaches n C u r) → (sigma r = b → ∀ x : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n C y x = true → PEqualNP.CleanedNonEdge.wireVal n C a x = true) ∧ (sigma r = a → ∀ x' : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n C y x' = true → PEqualNP.CleanedNonEdge.wireVal n C b x' = true)) → (∀ g2 ∈ PEqualNP.FactorSubst.frontier n C c, ∀ u2 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C g2).inputs, ∀ r1 ∈ PEqualNP.TopForm.readers n C c, ∀ r2 ∈ PEqualNP.TopForm.readers n C c, PEqualNP.CleanedNonEdge.OrReaches n C u2 r1 → PEqualNP.CleanedNonEdge.OrReaches n C u2 r2 → sigma r1 = sigma r2) → (∀ w3 ∈ insert c (PEqualNP.FactorSubst.orClosure n C c), C.output ≠ n + w3) → c ∈ PEqualNP.FactorSubst.liveGates n C → (∀ k < C.gates.length, k ≠ c → k ∉ PEqualNP.FactorSubst.orClosure n C c → ∀ z : Fin n → Bool, PEqualNP.EdgeOwnership.gateVal n (PEqualNP.FactorSubst.substReads C n c sigma) k z = PEqualNP.EdgeOwnership.gateVal n C k z) ∧ PEqualNP.FactorSubst.liveSize n (PEqualNP.FactorSubst.substReads C n c sigma) + 1 ≤ PEqualNP.FactorSubst.liveSize n C :=
  PEqualNP.Outside.L_meta_3297.main
