import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4791

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.TwoColour

lemma orSets_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

lemma orSets_char (n : ℕ) (gs : List Gate) :
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

lemma orReaches_iff (n : ℕ) (C : Circuit) (k g : ℕ) :
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

def phi (n w : ℕ) : ℕ := if w < n then w else n + 2 * (w - n) + 1

def gA (n : ℕ) (g : Gate) : Gate :=
  ⟨GateOp.and, [phi n (g.inputs.getD 0 0), phi n (g.inputs.getD 0 0)]⟩

def gB (n j : ℕ) (g : Gate) : Gate :=
  ⟨g.op, [n + 2 * j, phi n (g.inputs.getD 1 0)]⟩

def tr (n : ℕ) : ℕ → List Gate → List Gate
  | _, [] => []
  | j, g :: gs => gA n g :: gB n j g :: tr n (j + 1) gs

lemma tr_length (n : ℕ) : ∀ (gs : List Gate) (j : ℕ), (tr n j gs).length = 2 * gs.length := by
  intro gs
  induction gs with
  | nil => intro j; simp [tr]
  | cons g gs ih => intro j; simp [tr, ih]; omega

lemma tr_getD (n : ℕ) (d : Gate) : ∀ (gs : List Gate) (j i : ℕ), i < gs.length →
    (tr n j gs).getD (2 * i) d = gA n (gs.getD i d) ∧
    (tr n j gs).getD (2 * i + 1) d = gB n (j + i) (gs.getD i d) := by
  intro gs
  induction gs with
  | nil => intro j i hi; simp at hi
  | cons g gs ih =>
    intro j i hi
    cases i with
    | zero => simp [tr]
    | succ i =>
      have h := ih (j + 1) i (by simpa using hi)
      have e1 : 2 * (i + 1) = 2 * i + 1 + 1 := by ring
      have e3 : j + 1 + i = j + (i + 1) := by ring
      rw [e1]
      simp only [tr, List.getD_cons_succ]
      rw [← e3]
      exact h

lemma mem_tr (n : ℕ) : ∀ (gs : List Gate) (j : ℕ) (g' : Gate), g' ∈ tr n j gs →
    ∃ g ∈ gs, g' = gA n g ∨ ∃ i, g' = gB n i g := by
  intro gs
  induction gs with
  | nil => intro j g' h; simp [tr] at h
  | cons g gs ih =>
    intro j g' h
    simp only [tr, List.mem_cons] at h
    rcases h with h | h | h
    · exact ⟨g, by simp, Or.inl h⟩
    · exact ⟨g, by simp, Or.inr ⟨j, h⟩⟩
    · obtain ⟨g0, hg0, h0⟩ := ih (j + 1) g' h
      exact ⟨g0, by simp [hg0], h0⟩

lemma phi_lt (n i w : ℕ) (h : w < n + i) : phi n w < n + 2 * i := by
  unfold phi; split_ifs <;> omega

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stepWire x := rfl

lemma getD_snoc_lt (l : List Bool) (a : Bool) (i : ℕ) (h : i < l.length) :
    (l ++ [a]).getD i false = l.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma getD_snoc_eq (l : List Bool) (a : Bool) : (l ++ [a]).getD l.length false = a := by
  simp [List.getD_eq_getElem?_getD]

lemma getD_ge (l : List Bool) (i : ℕ) (h : l.length ≤ i) : l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

lemma and_self_eval (b : Bool) : GateOp.and.eval [b, b] = b := by
  cases b <;> rfl

lemma step (n j : ℕ) (W W' : List Bool) (g : Gate) (u v : ℕ) (huv : g.inputs = [u, v])
    (hW : W.length = n + j) (hW' : W'.length = n + 2 * j)
    (h : ∀ w, W'.getD (phi n w) false = W.getD w false) :
    ∀ w, (stepWire (stepWire W' (gA n g)) (gB n j g)).getD (phi n w) false =
      (stepWire W g).getD w false := by
  have ha : stepWire W' (gA n g) = W' ++ [W.getD u false] := by
    simp only [stepWire, gA, huv, List.map_cons, List.map_nil, List.getD_cons_zero]
    rw [and_self_eval, h u]
  have hv : (W' ++ [W.getD u false]).getD (phi n v) false = W.getD v false := by
    by_cases hlt : phi n v < n + 2 * j
    · rw [getD_snoc_lt _ _ _ (by omega)]; exact h v
    · have h1 : n + 2 * j + 1 ≤ phi n v := by
        unfold phi at hlt ⊢; split_ifs at hlt ⊢ <;> omega
      have h2 : n + j ≤ v := by
        unfold phi at h1; split_ifs at h1 <;> omega
      rw [getD_ge _ _ (by simp; omega), getD_ge _ _ (by omega)]
  have hu : (W' ++ [W.getD u false]).getD (n + 2 * j) false = W.getD u false := by
    rw [← hW']; exact getD_snoc_eq _ _
  have hb : stepWire (W' ++ [W.getD u false]) (gB n j g) =
      (W' ++ [W.getD u false]) ++ [g.op.eval [W.getD u false, W.getD v false]] := by
    simp only [stepWire, gB, huv, List.map_cons, List.map_nil, List.getD_cons_zero,
      List.getD_cons_succ]
    rw [hv, hu]
  have hc : stepWire W g = W ++ [g.op.eval [W.getD u false, W.getD v false]] := by
    simp [stepWire, huv]
  rw [ha, hb, hc]
  intro w
  rcases Nat.lt_trichotomy w (n + j) with hw | hw | hw
  · have h1 : phi n w < n + 2 * j := phi_lt n j w hw
    rw [getD_snoc_lt _ _ _ (by simp; omega), getD_snoc_lt _ _ _ (by omega),
      getD_snoc_lt _ _ _ (by omega)]
    exact h w
  · have h1 : phi n w = (W' ++ [W.getD u false]).length := by
      simp only [List.length_append, List.length_cons, List.length_nil, hW']
      unfold phi; split_ifs <;> omega
    have h2 : w = W.length := by omega
    rw [h1, getD_snoc_eq, h2, getD_snoc_eq]
  · have h1 : n + 2 * j + 2 ≤ phi n w := by
      unfold phi; split_ifs <;> omega
    rw [getD_ge _ _ (by simp; omega), getD_ge _ _ (by simp; omega)]

lemma sim (n : ℕ) : ∀ (gs : List Gate) (j : ℕ) (W W' : List Bool),
    (∀ g ∈ gs, g.inputs.length = 2) → W.length = n + j → W'.length = n + 2 * j →
    (∀ w, W'.getD (phi n w) false = W.getD w false) →
    ∀ w, ((tr n j gs).foldl stepWire W').getD (phi n w) false =
      (gs.foldl stepWire W).getD w false := by
  intro gs
  induction gs with
  | nil => intro j W W' _ _ _ h; simpa [tr] using h
  | cons g gs ih =>
    intro j W W' hl hW hW' h
    obtain ⟨u, v, huv⟩ := List.length_eq_two.mp (hl g (by simp))
    simp only [tr, List.foldl_cons]
    refine ih (j + 1) (stepWire W g) (stepWire (stepWire W' (gA n g)) (gB n j g))
      (fun g0 hg0 => hl g0 (by simp [hg0])) ?_ ?_ (step n j W W' g u v huv hW hW' h)
    · simp [stepWire, hW]; omega
    · simp [stepWire, hW']; omega

lemma gateAt_even (n o : ℕ) (C : Circuit) (i : ℕ) (hi : i < C.gates.length) :
    gateAt ⟨tr n 0 C.gates, o⟩ (2 * i) = gA n (gateAt C i) := by
  unfold gateAt
  exact (tr_getD n _ C.gates 0 i hi).1

lemma gateAt_odd (n o : ℕ) (C : Circuit) (i : ℕ) (hi : i < C.gates.length) :
    gateAt ⟨tr n 0 C.gates, o⟩ (2 * i + 1) = gB n i (gateAt C i) := by
  unfold gateAt
  have h := (tr_getD n ⟨GateOp.or, []⟩ C.gates 0 i hi).2
  rw [Nat.zero_add] at h
  exact h

lemma of_mem_filter {α : Type} (s : Finset α) (P : α → Prop) (inst : DecidablePred P) (a : α)
    (h : a ∈ @Finset.filter α P inst s) : P a := by
  classical
  exact (Finset.mem_filter.mp h).2

lemma dich (n o : ℕ) (C : Circuit) (i : ℕ) (hi : i < C.gates.length) (k a : ℕ)
    (hr : OrReaches n ⟨tr n 0 C.gates, o⟩ (n + (2 * i + 1)) k)
    (hop : (gateAt ⟨tr n 0 C.gates, o⟩ k).op = GateOp.or)
    (ha : a ∈ (gateAt ⟨tr n 0 C.gates, o⟩ k).inputs) (han : a < n) :
    (a = phi n ((gateAt C i).inputs.getD 1 0) ∧ phi n ((gateAt C i).inputs.getD 1 0) < n) ∨
    ∃ i', i' < i ∧ phi n ((gateAt C i).inputs.getD 1 0) = n + (2 * i' + 1) ∧
      OrReaches n ⟨tr n 0 C.gates, o⟩ (n + (2 * i' + 1)) k := by
  rw [orReaches_iff] at hr
  obtain ⟨_, hk | ⟨_, w, hw, hwlt, hrw⟩⟩ := hr
  · subst hk
    rw [gateAt_odd n o C i hi] at ha
    simp only [gB, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with h | h
    · omega
    · left; exact ⟨h, by omega⟩
  · rw [gateAt_odd n o C i hi] at hw
    simp only [gB, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with h | h
    · subst h
      rw [orReaches_iff] at hrw
      obtain ⟨_, hk | ⟨hop2, _⟩⟩ := hrw
      · subst hk
        rw [gateAt_even n o C i hi] at hop
        simp [gA] at hop
      · rw [gateAt_even n o C i hi] at hop2
        simp [gA] at hop2
    · right
      have hn : n ≤ w := hrw.1
      rw [h] at hn hwlt hrw
      have hv : ¬ (gateAt C i).inputs.getD 1 0 < n := by
        intro hv
        unfold phi at hn
        split_ifs at hn
        omega
      have e : phi n ((gateAt C i).inputs.getD 1 0) =
          n + (2 * ((gateAt C i).inputs.getD 1 0 - n) + 1) := by
        unfold phi; split_ifs; omega
      refine ⟨(gateAt C i).inputs.getD 1 0 - n, ?_, e, ?_⟩
      · rw [e] at hwlt; omega
      · rw [e] at hrw; exact hrw

lemma uniq (n o : ℕ) (C : Circuit) : ∀ i, i < C.gates.length → ∀ k1 k2 a1 a2 : ℕ,
    OrReaches n ⟨tr n 0 C.gates, o⟩ (n + (2 * i + 1)) k1 →
    (gateAt ⟨tr n 0 C.gates, o⟩ k1).op = GateOp.or →
    a1 ∈ (gateAt ⟨tr n 0 C.gates, o⟩ k1).inputs → a1 < n →
    OrReaches n ⟨tr n 0 C.gates, o⟩ (n + (2 * i + 1)) k2 →
    (gateAt ⟨tr n 0 C.gates, o⟩ k2).op = GateOp.or →
    a2 ∈ (gateAt ⟨tr n 0 C.gates, o⟩ k2).inputs → a2 < n → a1 = a2 := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi k1 k2 a1 a2 hr1 ho1 hm1 hn1 hr2 ho2 hm2 hn2
    rcases dich n o C i hi k1 a1 hr1 ho1 hm1 hn1 with ⟨e1, l1⟩ | ⟨i1, hi1, e1, r1⟩
    · rcases dich n o C i hi k2 a2 hr2 ho2 hm2 hn2 with ⟨e2, _⟩ | ⟨i2, _, e2, _⟩
      · exact e1.trans e2.symm
      · omega
    · rcases dich n o C i hi k2 a2 hr2 ho2 hm2 hn2 with ⟨_, l2⟩ | ⟨i2, _, e2, r2⟩
      · omega
      · have e : i1 = i2 := by omega
        subst e
        exact ih i1 hi1 (by omega) k1 k2 a1 a2 r1 ho1 hm1 hn1 r2 ho2 hm2 hn2

end PEqualNP.Outside.L_meta_4791

theorem PEqualNP.Outside.L_meta_4791 : ∀ (p l : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (p + l) C → 1 ≤ C.size → (∀ i : Fin (p + l), PEqualNP.MetaComplexity.circuitFun (p + l) C (fun k => decide (k = i)) = false) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 (p + l) D ∧ D.size + 4 ≤ 6 * C.size ∧ PEqualNP.MetaComplexity.circuitFun (p + l) D = PEqualNP.MetaComplexity.circuitFun (p + l) C ∧ PEqualNP.TwoColour.tCount (p + l) D (fun i => decide (p ≤ i)) = 0 := by
  intro p l C hC hs _
  obtain ⟨hAO, hRB, hLen⟩ := hC
  refine ⟨⟨PEqualNP.Outside.L_meta_4791.tr (p + l) 0 C.gates,
    PEqualNP.Outside.L_meta_4791.phi (p + l) C.output⟩, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro g' hg'
    obtain ⟨g, hg, h | ⟨i, h⟩⟩ := PEqualNP.Outside.L_meta_4791.mem_tr (p + l) C.gates 0 g' hg'
    · left; rw [h]; rfl
    · rw [h]; exact hAO g hg
  · intro k hk a ha
    have hk' : k < 2 * C.gates.length := by
      rw [← PEqualNP.Outside.L_meta_4791.tr_length (p + l) C.gates 0]; exact hk
    obtain ⟨u, v, huv⟩ := List.length_eq_two.mp
      (hLen (PEqualNP.MetaComplexity.NestedCover.gateAt C (k / 2))
        (by unfold PEqualNP.MetaComplexity.NestedCover.gateAt
            rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _))
    have hu := hRB (k / 2) (by omega) u (by rw [huv]; simp)
    have hv := hRB (k / 2) (by omega) v (by rw [huv]; simp)
    rcases Nat.even_or_odd' k with ⟨i, hi | hi⟩
    · subst hi
      have e : 2 * i / 2 = i := by omega
      rw [e] at huv hu hv
      rw [PEqualNP.Outside.L_meta_4791.gateAt_even (p + l) _ C i (by omega)] at ha
      simp only [PEqualNP.Outside.L_meta_4791.gA, huv, List.getD_cons_zero, List.mem_cons,
        List.not_mem_nil, or_false, or_self] at ha
      rw [ha]
      exact PEqualNP.Outside.L_meta_4791.phi_lt (p + l) i u hu
    · subst hi
      have e : (2 * i + 1) / 2 = i := by omega
      rw [e] at huv hu hv
      rw [PEqualNP.Outside.L_meta_4791.gateAt_odd (p + l) _ C i (by omega)] at ha
      simp only [PEqualNP.Outside.L_meta_4791.gB, huv, List.getD_cons_zero, List.getD_cons_succ,
        List.mem_cons, List.not_mem_nil, or_false] at ha
      have := PEqualNP.Outside.L_meta_4791.phi_lt (p + l) i v hv
      rcases ha with ha | ha <;> omega
  · intro g' hg'
    obtain ⟨g, hg, h | ⟨i, h⟩⟩ := PEqualNP.Outside.L_meta_4791.mem_tr (p + l) C.gates 0 g' hg'
    · rw [h]; rfl
    · rw [h]; rfl
  · have := PEqualNP.Outside.L_meta_4791.tr_length (p + l) C.gates 0
    simp only [PEqualNP.CircuitLowerBounds.Circuit.size] at hs ⊢
    omega
  · funext x
    unfold PEqualNP.MetaComplexity.circuitFun PEqualNP.CircuitLowerBounds.Circuit.eval
    rw [PEqualNP.Outside.L_meta_4791.wires_eq, PEqualNP.Outside.L_meta_4791.wires_eq]
    refine PEqualNP.Outside.L_meta_4791.sim (p + l) C.gates 0 (List.ofFn x) (List.ofFn x) hLen
      (by simp) (by simp) ?_ C.output
    intro w
    unfold PEqualNP.Outside.L_meta_4791.phi
    split_ifs with hw
    · rfl
    · rw [PEqualNP.Outside.L_meta_4791.getD_ge _ _ (by simp; omega),
        PEqualNP.Outside.L_meta_4791.getD_ge _ _ (by simp; omega)]
  · unfold PEqualNP.TwoColour.tCount PEqualNP.TwoColour.twoColour
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro g hg htc
    obtain ⟨hlt, hop, ⟨i1, hi1, hl1⟩, ⟨i2, hi2, hl2⟩⟩ := htc
    have hlt' : g < 2 * C.gates.length := by
      rw [← PEqualNP.Outside.L_meta_4791.tr_length (p + l) C.gates 0]; exact hlt
    unfold PEqualNP.TopForm.orIn at hi1 hi2
    have hj1 := PEqualNP.Outside.L_meta_4791.of_mem_filter _ _ _ _ hi1
    have hj2 := PEqualNP.Outside.L_meta_4791.of_mem_filter _ _ _ _ hi2
    rcases Nat.even_or_odd' g with ⟨i, hi | hi⟩
    · subst hi
      rw [PEqualNP.Outside.L_meta_4791.gateAt_even (p + l) _ C i (by omega)] at hop
      simp [PEqualNP.Outside.L_meta_4791.gA] at hop
    · subst hi
      rcases hj1 with h1 | ⟨k1, _, r1, o1, m1⟩
      · have := i1.isLt; omega
      · rcases hj2 with h2 | ⟨k2, _, r2, o2, m2⟩
        · have := i2.isLt; omega
        · have e := PEqualNP.Outside.L_meta_4791.uniq (p + l) _ C i (by omega) k1 k2 i1 i2
            r1 o1 m1 i1.isLt r2 o2 m2 i2.isLt
          rw [e] at hl1
          rw [hl1] at hl2
          exact Bool.noConfusion hl2
