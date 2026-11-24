import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2479

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.CleanedNonEdge

def fd {α : Type} (st : List α → Gate → α) (gs : List Gate) (w : List α) : List α :=
  gs.foldl (fun w g => w ++ [st w g]) w

theorem fd_snoc {α : Type} (st : List α → Gate → α) (gs : List Gate) (g : Gate) (w : List α) :
    fd st (gs ++ [g]) w = fd st gs w ++ [st (fd st gs w) g] := by
  simp [fd, List.foldl_append]

theorem fd_len {α : Type} (st : List α → Gate → α) (gs : List Gate) :
    ∀ w : List α, (fd st gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [fd]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [st w g])
    simp only [fd, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem fd_keep {α : Type} (st : List α → Gate → α) (d : α) (gs : List Gate) :
    ∀ (w : List α) (i : ℕ), i < w.length → (fd st gs w).getD i d = w.getD i d := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [st w g]) i (by simp; omega)
    simp only [fd, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem fd_take {α : Type} (st : List α → Gate → α) (d : α) (gs : List Gate) (X : List α)
    (k i : ℕ) (hi : i < X.length + k) (hk : k ≤ gs.length) :
    (fd st gs X).getD i d = (fd st (gs.take k) X).getD i d := by
  have h1 : fd st gs X = fd st (gs.drop k) (fd st (gs.take k) X) := by
    unfold fd
    rw [← List.foldl_append, List.take_append_drop]
  rw [h1]
  exact fd_keep st d _ _ i (by rw [fd_len, List.length_take, Nat.min_eq_left hk]; exact hi)

theorem fd_gate {α : Type} (st : List α → Gate → α) (d : α) (gs : List Gate) (X : List α)
    (k : ℕ) (hk : k < gs.length) :
    (fd st gs X).getD (X.length + k) d = st (fd st (gs.take k) X) gs[k] := by
  rw [fd_take st d gs X (k + 1) _ (by omega) hk, List.take_succ_eq_append_getElem hk, fd_snoc]
  have hl : (fd st (gs.take k) X).length = X.length + k := by
    rw [fd_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)]
  rw [← hl]
  simp [List.getD_eq_getElem?_getD]

def stB (w : List Bool) (g : Gate) : Bool := g.op.eval (g.inputs.map fun i => w.getD i false)

def val (gs : List Gate) {n : ℕ} (w : ℕ) (x : Fin n → Bool) : Bool :=
  (fd stB gs (List.ofFn x)).getD w false

theorem wires_eq (n : ℕ) (C : Circuit) (w : ℕ) (x : Fin n → Bool) :
    wireVal n C w x = val C.gates w x := rfl

theorem iv_eq (gs : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k ≤ gs.length)
    (i : ℕ) : (fd stB (gs.take k) (List.ofFn x)).getD i false = true ↔
      i < n + k ∧ val gs i x = true := by
  by_cases hi : i < n + k
  · rw [val, fd_take stB false gs (List.ofFn x) k i (by simpa using hi) hk]
    simp [hi]
  · rw [List.getD_eq_default _ _ (by rw [fd_len, List.length_take, Nat.min_eq_left hk]; simp; omega)]
    simp [hi]

theorem val_and (gs : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gs.length)
    (hop : gs[k].op = GateOp.and) :
    val gs (n + k) x = true ↔ ∀ i ∈ gs[k].inputs, i < n + k ∧ val gs i x = true := by
  have := fd_gate stB false gs (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this]
  show (gs[k].op.eval _) = true ↔ _
  rw [hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
  constructor
  · intro h i hi; exact (iv_eq gs x k (Nat.le_of_lt hk) i).1 (h i hi)
  · intro h i hi; exact (iv_eq gs x k (Nat.le_of_lt hk) i).2 (h i hi)

theorem val_or (gs : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gs.length)
    (hop : gs[k].op = GateOp.or) :
    val gs (n + k) x = true ↔ ∃ i ∈ gs[k].inputs, i < n + k ∧ val gs i x = true := by
  have := fd_gate stB false gs (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this]
  show (gs[k].op.eval _) = true ↔ _
  rw [hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
  constructor
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gs x k (Nat.le_of_lt hk) i).1 h⟩
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gs x k (Nat.le_of_lt hk) i).2 h⟩

theorem gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

theorem orSets_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

theorem orSets_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (orStep n) []).getD j [] ↔
      j < gs.length ∧ (i = j ∨ ((gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
        ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
          i ∈ (gs.foldl (orStep n) []).getD (w - n) [])) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (orStep n) []).length = gs.length := by
      rw [orSets_len]; simp
    have key : ∀ k, k < gs.length →
        (orStep n (gs.foldl (orStep n) []) g).getD k [] =
          (gs.foldl (orStep n) []).getD k [] := by
      intro k hk
      simp only [orStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, h3⟩
        refine ⟨by simp; omega, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · refine Or.inr ⟨hop, w, hw, h1, h2, ?_⟩
          rw [key (w - n) (by omega)]
          exact h3
      · rintro ⟨_, h3⟩
        refine ⟨h, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · rw [key (w - n) (by omega)] at h3
          exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [e1]
      by_cases hop : g.op = GateOp.or
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] =
            gs.length :: (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
              (fun w => (gs.foldl (orStep n) []).getD (w - n) []) := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
        constructor
        · rintro (h3 | ⟨w, ⟨hw, h1, h2⟩, h3⟩)
          · exact ⟨by simp, Or.inl h3⟩
          · refine ⟨by simp, Or.inr ⟨hop, w, hw, h1, h2, ?_⟩⟩
            rw [key (w - n) (by omega)]
            exact h3
        · rintro ⟨_, h3 | ⟨_, w, hw, h1, h2, h3⟩⟩
          · exact Or.inl h3
          · rw [key (w - n) (by omega)] at h3
            exact Or.inr ⟨w, ⟨hw, h1, h2⟩, h3⟩
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] = [gs.length] := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_singleton]
        constructor
        · intro h3
          exact ⟨by simp, Or.inl h3⟩
        · rintro ⟨_, h3 | ⟨hop2, _⟩⟩
          · exact h3
          · exact (hop hop2).elim
    · have e0 : (orStep n (gs.foldl (orStep n) []) g).getD j [] = [] := by
        simp only [orStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

theorem orReaches_iff (n : ℕ) (C : Circuit) (k g : ℕ) :
    OrReaches n C (n + k) g ↔ k < C.gates.length ∧ (g = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ i ∈ (gateAt C k).inputs, i < n + k ∧ OrReaches n C i g)) := by
  have h := orSets_char n C.gates g k
  unfold OrReaches orSets gateAt
  have e : n + k - n = k := by omega
  rw [e, h]
  constructor
  · rintro ⟨_, hk, h3⟩
    refine ⟨hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h2, h1, h3⟩
  · rintro ⟨hk, h3⟩
    refine ⟨by omega, hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h2, h1, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩

theorem reach_up (n : ℕ) (C : Circuit) (x : Fin n → Bool) (j : ℕ) :
    ∀ b : ℕ, OrReaches n C b j → val C.gates (n + j) x = true → val C.gates b x = true := by
  intro b
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    intro h hv
    have hnb : n ≤ b := h.1
    obtain ⟨k, hbk⟩ : ∃ k, b = n + k := ⟨b - n, by omega⟩
    rw [hbk] at h ⊢
    obtain ⟨hk, h3⟩ := (orReaches_iff n C k j).1 h
    rcases h3 with h3 | ⟨hop, i, hi, hlt, hr⟩
    · rw [h3] at hv
      exact hv
    · rw [gateAt_eq C k hk] at hop hi
      exact (val_or C.gates x k hk hop).2 ⟨i, hi, hlt, ih i (by omega) hr hv⟩

theorem mem_filter' {α : Type} (p : α → Prop) (inst : DecidablePred p) (s : Finset α) (a : α) :
    a ∈ @Finset.filter α p inst s ↔ a ∈ s ∧ p a := Finset.mem_filter

theorem orIn_up (n : ℕ) (C : Circuit) (x : Fin n → Bool) (b : ℕ) (i : Fin n)
    (hi : i ∈ orIn n C b) (hv : val C.gates i.val x = true) : val C.gates b x = true := by
  have hi2 : (i : ℕ) = b ∨ ∃ k < C.gates.length,
      OrReaches n C b k ∧ (gateAt C k).op = GateOp.or ∧ (i : ℕ) ∈ (gateAt C k).inputs :=
    ((mem_filter' _ _ _ _).mp hi).2
  rcases hi2 with h1 | ⟨k, hk, hr, hop, hin⟩
  · rw [h1] at hv
    exact hv
  · rw [gateAt_eq C k hk] at hop hin
    have hlt : i.val < n + k := by
      have := i.isLt
      omega
    exact reach_up n C x k b hr ((val_or C.gates x k hk hop).2 ⟨i.val, hin, hlt, hv⟩)

theorem or_up (n : ℕ) (C : Circuit) (x : Fin n → Bool) (a b : ℕ)
    (h : (∃ i_1 : Fin n, i_1.val = a ∧ i_1 ∈ orIn n C b) ∨
      (∃ j_1 : ℕ, a = n + j_1 ∧ OrReaches n C b j_1))
    (hv : val C.gates a x = true) : val C.gates b x = true := by
  rcases h with ⟨i, hia, hi⟩ | ⟨j, haj, hr⟩
  · rw [← hia] at hv
    exact orIn_up n C x b i hi hv
  · rw [haj] at hv
    exact reach_up n C x j b hr hv

theorem and2 (n : ℕ) (C : Circuit) (hC : IsAO2 n C) (x : Fin n → Bool) (j s t : ℕ)
    (hj : j < C.gates.length ∧ (gateAt C j).op = GateOp.and ∧
      ((gateAt C j).inputs = [s, t] ∨ (gateAt C j).inputs = [t, s]))
    (hs : val C.gates s x = true) (ht : val C.gates t x = true) :
    val C.gates (n + j) x = true := by
  obtain ⟨hlt, hop, hin⟩ := hj
  have hrbj := hC.2.1 j hlt
  rw [gateAt_eq C j hlt] at hop hin hrbj
  apply (val_and C.gates x j hlt hop).2
  intro i hi
  refine ⟨hrbj i hi, ?_⟩
  have hi2 : i = s ∨ i = t := by
    rcases hin with e | e
    · rw [e] at hi
      simpa using hi
    · rw [e] at hi
      have : i = t ∨ i = s := by simpa using hi
      exact this.symm
  rcases hi2 with h2 | h2
  · rw [h2]
    exact hs
  · rw [h2]
    exact ht

theorem out_up (n : ℕ) (C : Circuit) (x : Fin n → Bool) (j : ℕ)
    (hr : OrReaches n C C.output j) (hv : val C.gates (n + j) x = true) :
    circuitFun n C x = true := by
  show val C.gates C.output x = true
  exact reach_up n C x j C.output hr hv

theorem type0 (n : ℕ) (C : Circuit) (hC : IsAO2 n C) (x : Fin n → Bool) (j s t : ℕ)
    (hj : j < C.gates.length ∧ (gateAt C j).op = GateOp.and ∧
      ((gateAt C j).inputs = [s, t] ∨ (gateAt C j).inputs = [t, s]))
    (hr : OrReaches n C C.output j)
    (hs : wireVal n C s x = true) (ht : wireVal n C t x = true) :
    circuitFun n C x = true :=
  out_up n C x j hr (and2 n C hC x j s t hj hs ht)

theorem link_up (n : ℕ) (C : Circuit) (x : Fin n → Bool) (a b : ℕ)
    (h : (∃ i_1 : Fin n, i_1.val = a ∧ i_1 ∈ orIn n C b) ∨
      (∃ j_1 : ℕ, a = n + j_1 ∧ OrReaches n C b j_1))
    (hv : wireVal n C a x = true) : wireVal n C b x = true :=
  or_up n C x a b h hv

theorem and_wire (n : ℕ) (C : Circuit) (hC : IsAO2 n C) (x : Fin n → Bool) (j s t u : ℕ)
    (hj : j < C.gates.length ∧ (gateAt C j).op = GateOp.and ∧
      ((gateAt C j).inputs = [s, t] ∨ (gateAt C j).inputs = [t, s]))
    (hr : OrReaches n C u j)
    (hs : wireVal n C s x = true) (ht : wireVal n C t x = true) :
    wireVal n C u x = true :=
  reach_up n C x j u hr (and2 n C hC x j s t hj hs ht)

end PEqualNP.Outside.L_meta_2479

theorem PEqualNP.Outside.L_meta_2479 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 n C → (∀ (j K F : ℕ), (j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs = [K, F] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs = [F, K])) → PEqualNP.CleanedNonEdge.OrReaches n C (C.output) j → (∀ z_1 : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n C (K) z_1 = true → PEqualNP.CleanedNonEdge.wireVal n C (F) z_1 = true → PEqualNP.CleanedNonEdge.wireVal n C (F) z_1 = true → PEqualNP.MetaComplexity.circuitFun n C z_1 = true)) ∧ (∀ (j1 j2 K1 F1 V F2 h : ℕ), (j1 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j1).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j1).inputs = [K1, F1] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j1).inputs = [F1, K1])) → PEqualNP.CleanedNonEdge.OrReaches n C (h) j1 → ((∃ i_1 : Fin n, i_1.val = h ∧ i_1 ∈ PEqualNP.TopForm.orIn n C (V)) ∨ (∃ j_1 : ℕ, h = n + j_1 ∧ PEqualNP.CleanedNonEdge.OrReaches n C (V) j_1)) → (j2 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j2).inputs = [V, F2] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j2).inputs = [F2, V])) → PEqualNP.CleanedNonEdge.OrReaches n C (C.output) j2 → (∀ z_2 : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n C (K1) z_2 = true → PEqualNP.CleanedNonEdge.wireVal n C (F1) z_2 = true → PEqualNP.CleanedNonEdge.wireVal n C (F2) z_2 = true → PEqualNP.MetaComplexity.circuitFun n C z_2 = true) ∧ (∀ z_3 : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n C (h) z_3 = true → PEqualNP.CleanedNonEdge.wireVal n C (F2) z_3 = true → PEqualNP.CleanedNonEdge.wireVal n C (F2) z_3 = true → PEqualNP.MetaComplexity.circuitFun n C z_3 = true)) ∧ (∀ (j3 j4 F3 F4 U K2 : ℕ), (j3 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j3).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j3).inputs = [F3, F4] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j3).inputs = [F4, F3])) → PEqualNP.CleanedNonEdge.OrReaches n C (U) j3 → (j4 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j4).inputs = [K2, U] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j4).inputs = [U, K2])) → PEqualNP.CleanedNonEdge.OrReaches n C (C.output) j4 → (∀ z_4 : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n C (K2) z_4 = true → PEqualNP.CleanedNonEdge.wireVal n C (F3) z_4 = true → PEqualNP.CleanedNonEdge.wireVal n C (F4) z_4 = true → PEqualNP.MetaComplexity.circuitFun n C z_4 = true) ∧ (∀ z_5 : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n C (K2) z_5 = true → PEqualNP.CleanedNonEdge.wireVal n C (U) z_5 = true → PEqualNP.CleanedNonEdge.wireVal n C (U) z_5 = true → PEqualNP.MetaComplexity.circuitFun n C z_5 = true)) := by
  intro n C hC
  refine ⟨?_, ?_, ?_⟩
  · intro j K F hj hr z hK hF _
    exact PEqualNP.Outside.L_meta_2479.type0 n C hC z j K F hj hr hK hF
  · intro j1 j2 K1 F1 V F2 h hj1 hr1 hV hj2 hr2
    refine ⟨?_, ?_⟩
    · intro z hK hF1 hF2
      have hh := PEqualNP.Outside.L_meta_2479.and_wire n C hC z j1 K1 F1 h hj1 hr1 hK hF1
      have hv := PEqualNP.Outside.L_meta_2479.link_up n C z h V hV hh
      exact PEqualNP.Outside.L_meta_2479.type0 n C hC z j2 V F2 hj2 hr2 hv hF2
    · intro z hh hF2 _
      have hv := PEqualNP.Outside.L_meta_2479.link_up n C z h V hV hh
      exact PEqualNP.Outside.L_meta_2479.type0 n C hC z j2 V F2 hj2 hr2 hv hF2
  · intro j3 j4 F3 F4 U K2 hj3 hr3 hj4 hr4
    refine ⟨?_, ?_⟩
    · intro z hK hF3 hF4
      have hU := PEqualNP.Outside.L_meta_2479.and_wire n C hC z j3 F3 F4 U hj3 hr3 hF3 hF4
      exact PEqualNP.Outside.L_meta_2479.type0 n C hC z j4 K2 U hj4 hr4 hK hU
    · intro z hK hU _
      exact PEqualNP.Outside.L_meta_2479.type0 n C hC z j4 K2 U hj4 hr4 hK hU
