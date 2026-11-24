import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4295

open PEqualNP.CircuitLowerBounds PEqualNP.CircuitMoves

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stepW x := rfl

lemma foldl_len (gs : List Gate) : ∀ w : List Bool,
    (gs.foldl stepW w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp
  | cons g gs ih =>
    intro w
    simp only [List.foldl_cons, ih, stepW, List.length_append, List.length_cons,
      List.length_nil]
    omega

lemma foldl_ext (gs : List Gate) : ∀ w : List Bool, ∃ t, gs.foldl stepW w = w ++ t := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht⟩ := ih (stepW w g)
    refine ⟨[g.op.eval (g.inputs.map fun i => w.getD i false)] ++ t, ?_⟩
    simp only [List.foldl_cons]
    rw [ht]
    simp [stepW]

lemma foldl_getD (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < w.length) :
    (gs.foldl stepW w).getD k false = w.getD k false := by
  obtain ⟨t, ht⟩ := foldl_ext gs w
  rw [ht, List.getD_append _ _ _ _ hk]

def ren (n m p : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (eraseRedirect n m p)⟩

lemma erase_sim (n m p : ℕ) (hp : p < n + m) (B : List Gate) :
    ∀ V0 V' : List Bool, V0.length = V'.length + 1 → n + m < V0.length →
      (∀ i, V'.getD (eraseRedirect n m p i) false = V0.getD i false) →
      ∀ i, ((B.map (ren n m p)).foldl stepW V').getD (eraseRedirect n m p i) false =
        (B.foldl stepW V0).getD i false := by
  induction B with
  | nil => intro V0 V' _ _ hinv i; exact hinv i
  | cons g B ih =>
    intro V0 V' hlen hnm hinv
    apply ih
    · simp [stepW, hlen]
    · simp [stepW]; omega
    · intro i
      have hv : (g.inputs.map (eraseRedirect n m p)).map (fun j => V'.getD j false) =
          g.inputs.map (fun j => V0.getD j false) := by
        rw [List.map_map]
        exact List.map_congr_left (fun j _ => hinv j)
      simp only [stepW, ren]
      rw [hv]
      by_cases hi : i < V0.length
      · have hr : eraseRedirect n m p i < V'.length := by
          unfold eraseRedirect; split_ifs <;> omega
        rw [List.getD_append _ _ _ _ hr, List.getD_append _ _ _ _ hi]
        exact hinv i
      · by_cases hie : i = V0.length
        · have hr : eraseRedirect n m p i = V'.length := by
            unfold eraseRedirect; split_ifs <;> omega
          rw [hr, hie, List.getD_append_right _ _ _ _ (le_refl _),
            List.getD_append_right _ _ _ _ (le_refl _)]
          simp
        · have hr : V'.length + 1 ≤ eraseRedirect n m p i := by
            unfold eraseRedirect; split_ifs <;> omega
          rw [List.getD_eq_default _ _ (by simp; omega),
            List.getD_eq_default _ _ (by simp; omega)]

lemma op_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (ins : List ℕ)
    (f0 f : ℕ → Bool) (c : Bool) (h1 : ∀ i, f0 i = true → f i = true)
    (h2 : ∀ i, f i = true → f0 i = true ∨ c = true) :
    (op.eval (ins.map f0) = true → op.eval (ins.map f) = true) ∧
    (op.eval (ins.map f) = true → op.eval (ins.map f0) = true ∨ c = true) := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
    refine ⟨fun h i hi => h1 i (h i hi), fun h => ?_⟩
    by_cases hc : c = true
    · exact Or.inr hc
    · left
      intro i hi
      rcases h2 i (h i hi) with h' | h'
      · exact h'
      · exact absurd h' hc
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
    refine ⟨fun ⟨i, hi, h⟩ => ⟨i, hi, h1 i h⟩, fun ⟨i, hi, h⟩ => ?_⟩
    rcases h2 i h with h' | h'
    · exact Or.inl ⟨i, hi, h'⟩
    · exact Or.inr h'

lemma mono_sim (B : List Gate) (hB : ∀ g ∈ B, g.op = GateOp.and ∨ g.op = GateOp.or)
    (c : Bool) : ∀ V0 V : List Bool,
      (∀ i, V0.getD i false = true → V.getD i false = true) →
      (∀ i, V.getD i false = true → V0.getD i false = true ∨ c = true) →
      V0.length = V.length →
      (∀ i, (B.foldl stepW V0).getD i false = true → (B.foldl stepW V).getD i false = true) ∧
      (∀ i, (B.foldl stepW V).getD i false = true →
        (B.foldl stepW V0).getD i false = true ∨ c = true) := by
  induction B with
  | nil => intro V0 V h1 h2 _; exact ⟨h1, h2⟩
  | cons g B ih =>
    intro V0 V h1 h2 hl
    have hop := op_mono g.op (hB g (by simp)) g.inputs (fun j => V0.getD j false)
      (fun j => V.getD j false) c h1 h2
    apply ih (fun g' hg' => hB g' (by simp [hg']))
    · intro i hi
      simp only [stepW] at hi ⊢
      by_cases hil : i < V0.length
      · rw [List.getD_append _ _ _ _ hil] at hi
        rw [List.getD_append _ _ _ _ (by omega)]
        exact h1 i hi
      · by_cases hie : i = V0.length
        · subst hie
          rw [List.getD_append_right _ _ _ _ (le_refl _)] at hi
          rw [hl, List.getD_append_right _ _ _ _ (le_refl _)]
          simp only [Nat.sub_self, List.getD_cons_zero] at hi ⊢
          exact hop.1 hi
        · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
          exact absurd hi (by simp)
    · intro i hi
      simp only [stepW] at hi ⊢
      by_cases hil : i < V.length
      · rw [List.getD_append _ _ _ _ hil] at hi
        rw [List.getD_append _ _ _ _ (by omega)]
        exact h2 i hi
      · by_cases hie : i = V.length
        · subst hie
          rw [List.getD_append_right _ _ _ _ (le_refl _)] at hi
          rw [← hl, List.getD_append_right _ _ _ _ (le_refl _)]
          simp only [Nat.sub_self, List.getD_cons_zero] at hi ⊢
          exact hop.2 hi
        · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
          exact absurd hi (by simp)
    · simp [stepW, hl]

lemma gates_decomp (gs : List Gate) (m : ℕ) (hm : m < gs.length) :
    gs = gs.take m ++ gs[m] :: gs.drop (m + 1) := by
  conv_lhs => rw [← List.take_append_drop m gs]
  rw [List.drop_eq_getElem_cons hm]

lemma erase_gates (n : ℕ) (C : Circuit) (m p : ℕ) (hm : m < C.gates.length) :
    (eraseGate n C m p).gates = C.gates.take m ++ (C.gates.drop (m + 1)).map (ren n m p) ∧
    (eraseGate n C m p).output = eraseRedirect n m p C.output := by
  unfold eraseGate
  rw [if_pos hm]
  exact ⟨rfl, rfl⟩

lemma lift_facts (n : ℕ) (C : Circuit) (m p h : ℕ) (hm : m < C.gates.length)
    (hp : p < n + m) (hh : h < n + m)
    (hg : C.gates[m] = ⟨GateOp.or, [p, h]⟩ ∨ C.gates[m] = ⟨GateOp.or, [h, p]⟩)
    (hAO : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x : List Bool) (hx : x.length = n) :
    ∃ W0 : List Bool,
      (∀ i < n + C.gates.length,
        ((liftAt n C m p h).wires x).getD (eraseRedirect n m p i) false = W0.getD i false) ∧
      (∀ i, W0.getD i false = true → (C.wires x).getD i false = true) ∧
      (∀ i, (C.wires x).getD i false = true →
        W0.getD i false = true ∨ (C.wires x).getD h false = true) ∧
      (liftAt n C m p h).eval x =
        (W0.getD C.output false || (C.wires x).getD h false) := by
  set A := C.gates.take m with hA
  set B := C.gates.drop (m + 1) with hB
  set U := A.foldl stepW x with hU
  have hUl : U.length = n + m := by
    rw [hU, foldl_len, hx, hA, List.length_take]; omega
  have hdec := gates_decomp C.gates m hm
  obtain ⟨hEg, hEo⟩ := erase_gates n C m p hm
  set V0 := U ++ [U.getD p false] with hV0
  have hred_lt : ∀ i, i < n + m → eraseRedirect n m p i = i := by
    intro i hi; unfold eraseRedirect; split_ifs <;> omega
  have hbase : ∀ i, U.getD (eraseRedirect n m p i) false = V0.getD i false := by
    intro i
    rw [hV0]
    by_cases hi : i < n + m
    · rw [hred_lt i hi, List.getD_append _ _ _ _ (by omega)]
    · by_cases hie : i = n + m
      · have : eraseRedirect n m p i = p := by unfold eraseRedirect; simp [hie]
        rw [this, hie, ← hUl, List.getD_append_right _ _ _ _ (le_refl _)]
        simp
      · have : eraseRedirect n m p i = i - 1 := by
          unfold eraseRedirect; split_ifs <;> omega
        rw [this, List.getD_eq_default _ _ (by omega),
          List.getD_eq_default _ _ (by simp; omega)]
  set Ew := (B.map (ren n m p)).foldl stepW U with hEw
  have hsim := erase_sim n m p hp B V0 U (by simp [hV0]) (by simp [hV0]; omega) hbase
  have hEwl : Ew.length = n + m + B.length := by
    rw [hEw, foldl_len, hUl, List.length_map]
  have hBl : B.length = C.gates.length - (m + 1) := by rw [hB, List.length_drop]
  have hEwires : (eraseGate n C m p).gates.foldl stepW x = Ew := by
    rw [hEg, List.foldl_append]
  have hval : stepW U C.gates[m] = U ++ [U.getD p false || U.getD h false] := by
    rcases hg with hg | hg <;> rw [hg] <;> simp [stepW, GateOp.eval, Bool.or_comm]
  have hW : C.wires x = B.foldl stepW (U ++ [U.getD p false || U.getD h false]) := by
    rw [wires_eq, ← hval]
    conv_lhs => rw [hdec]
    rw [List.foldl_append, List.foldl_cons]
  have hWh : (C.wires x).getD h false = U.getD h false := by
    rw [hW, foldl_getD _ _ _ (by simp; omega), List.getD_append _ _ _ _ (by omega)]
  have hLw : (liftAt n C m p h).wires x =
      Ew ++ [Ew.getD (eraseRedirect n m p C.output) false || Ew.getD h false] := by
    unfold liftAt
    rw [wires_eq, List.foldl_append, hEwires, hEo]
    simp [stepW, GateOp.eval]
  have hmono := mono_sim B (fun g hg' => hAO g (List.mem_of_mem_drop hg')) (U.getD h false)
    V0 (U ++ [U.getD p false || U.getD h false])
    (by
      intro i hi
      rw [hV0] at hi
      by_cases hil : i < U.length
      · rw [List.getD_append _ _ _ _ hil] at hi; rw [List.getD_append _ _ _ _ hil]; exact hi
      · by_cases hie : i = U.length
        · subst hie
          rw [List.getD_append_right _ _ _ _ (le_refl _)] at hi
          rw [List.getD_append_right _ _ _ _ (le_refl _)]
          simp at hi ⊢; exact Or.inl hi
        · rw [List.getD_eq_default _ _ (by simp; omega)] at hi; exact absurd hi (by simp))
    (by
      intro i hi
      rw [hV0]
      by_cases hil : i < U.length
      · rw [List.getD_append _ _ _ _ hil] at hi; rw [List.getD_append _ _ _ _ hil]; exact Or.inl hi
      · by_cases hie : i = U.length
        · subst hie
          rw [List.getD_append_right _ _ _ _ (le_refl _)] at hi
          rw [List.getD_append_right _ _ _ _ (le_refl _)]
          simpa using hi
        · rw [List.getD_eq_default _ _ (by simp; omega)] at hi; exact absurd hi (by simp))
    (by simp [hV0])
  have hW0h : (B.foldl stepW V0).getD h false = U.getD h false := by
    rw [foldl_getD _ _ _ (by simp [hV0]; omega), hV0, List.getD_append _ _ _ _ (by omega)]
  refine ⟨B.foldl stepW V0, ?_, ?_, ?_, ?_⟩
  · intro i hi
    have hr : eraseRedirect n m p i < Ew.length := by
      rw [hEwl, hBl]; unfold eraseRedirect; split_ifs <;> omega
    rw [hLw, List.getD_append _ _ _ _ hr, hsim i]
  · intro i hi
    rw [hW]; exact hmono.1 i hi
  · intro i hi
    rw [hW] at hi
    rw [hWh]
    exact hmono.2 i hi
  · have hEh : Ew.getD h false = U.getD h false := by
      have := hsim h
      rw [hred_lt h hh] at this
      rw [this, hW0h]
    unfold Circuit.eval
    rw [hLw]
    have hlen : (liftAt n C m p h).output = Ew.length := by
      rw [hEwl, hBl]
      unfold liftAt
      simp only [hEg, List.length_append, List.length_map, List.length_take, List.length_drop]
      omega
    rw [hlen, List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self]
    simp only [List.getD_cons_zero]
    rw [hsim, hEh, hWh]

lemma lift_eval (n : ℕ) (C : Circuit) (m p h : ℕ) (hm : m < C.gates.length)
    (hp : p < n + m) (hh : h < n + m)
    (hg : C.gates[m] = ⟨GateOp.or, [p, h]⟩ ∨ C.gates[m] = ⟨GateOp.or, [h, p]⟩)
    (hAO : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hbelow : WireBelowOutput n C h) (x : Fin n → Bool) :
    (liftAt n C m p h).eval (List.ofFn x) = C.eval (List.ofFn x) := by
  obtain ⟨W0, -, h2, h3, h4⟩ := lift_facts n C m p h hm hp hh hg hAO (List.ofFn x) (by simp)
  rw [h4]
  by_cases hc : (C.wires (List.ofFn x)).getD h false = true
  · rw [hc, hbelow x hc]; simp
  · have hcf : (C.wires (List.ofFn x)).getD h false = false := by simpa using hc
    rw [hcf, Bool.or_false]
    unfold Circuit.eval
    cases hw0 : W0.getD C.output false
    · cases hw : (C.wires (List.ofFn x)).getD C.output false
      · rfl
      · rcases h3 _ hw with h' | h'
        · rw [hw0] at h'; exact absurd h' (by simp)
        · exact absurd h' hc
    · exact (h2 _ hw0).symm

lemma lift_below (n : ℕ) (C : Circuit) (m p h : ℕ) (hm : m < C.gates.length)
    (hp : p < n + m) (hh : h < n + m)
    (hg : C.gates[m] = ⟨GateOp.or, [p, h]⟩ ∨ C.gates[m] = ⟨GateOp.or, [h, p]⟩)
    (hAO : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hbelow : WireBelowOutput n C h) (i : ℕ) (hi : i < n + C.gates.length) :
    WireBelowOutput n (liftAt n C m p h) (eraseRedirect n m p i) ↔ WireBelowOutput n C i := by
  constructor
  · intro hL x hx
    obtain ⟨W0, h1, h2, h3, -⟩ := lift_facts n C m p h hm hp hh hg hAO (List.ofFn x) (by simp)
    rcases h3 i hx with h' | h'
    · rw [← lift_eval n C m p h hm hp hh hg hAO hbelow x]
      apply hL x
      rw [h1 i hi]; exact h'
    · exact hbelow x h'
  · intro hC x hx
    obtain ⟨W0, h1, h2, -, -⟩ := lift_facts n C m p h hm hp hh hg hAO (List.ofFn x) (by simp)
    rw [lift_eval n C m p h hm hp hh hg hAO hbelow x]
    rw [h1 i hi] at hx
    exact hC x (h2 i hx)

lemma lift_gates (n : ℕ) (C : Circuit) (m p h : ℕ) (hm : m < C.gates.length) :
    (liftAt n C m p h).gates = C.gates.take m ++ (C.gates.drop (m + 1)).map (ren n m p) ++
      [⟨GateOp.or, [eraseRedirect n m p C.output, h]⟩] := by
  obtain ⟨hEg, hEo⟩ := erase_gates n C m p hm
  unfold liftAt
  rw [hEg, hEo]

lemma lift_len (n : ℕ) (C : Circuit) (m p h : ℕ) (hm : m < C.gates.length) :
    (liftAt n C m p h).gates.length = C.gates.length := by
  rw [lift_gates n C m p h hm]
  simp only [List.length_append, List.length_take, List.length_map, List.length_drop,
    List.length_singleton]
  omega

lemma lift_output (n : ℕ) (C : Circuit) (m p h : ℕ) (hm : m < C.gates.length) :
    (liftAt n C m p h).output = n + (C.gates.length - 1) := by
  obtain ⟨hEg, -⟩ := erase_gates n C m p hm
  unfold liftAt
  rw [hEg]
  simp only [List.length_append, List.length_take, List.length_map, List.length_drop]
  omega

lemma lift_get_lt (n : ℕ) (C : Circuit) (m p h : ℕ) (hm : m < C.gates.length) (j : ℕ)
    (hj : j < m) : (liftAt n C m p h).gates[j]? = C.gates[j]? := by
  rw [lift_gates n C m p h hm, List.append_assoc,
    List.getElem?_append_left (by simp; omega), List.getElem?_take]
  simp [hj]

lemma lift_get_mid (n : ℕ) (C : Circuit) (m p h : ℕ) (hm : m < C.gates.length) (j : ℕ)
    (hj : m ≤ j) (hj2 : j + 1 < C.gates.length) :
    (liftAt n C m p h).gates[j]? = (C.gates[j + 1]?).map (ren n m p) := by
  rw [lift_gates n C m p h hm, List.append_assoc,
    List.getElem?_append_right (by simp; omega),
    List.getElem?_append_left (by simp; omega)]
  simp only [List.length_take, List.getElem?_map, List.getElem?_drop]
  congr 2
  omega

lemma lift_get_last (n : ℕ) (C : Circuit) (m p h : ℕ) (hm : m < C.gates.length) :
    (liftAt n C m p h).gates[C.gates.length - 1]? =
      some ⟨GateOp.or, [eraseRedirect n m p C.output, h]⟩ := by
  rw [lift_gates n C m p h hm, List.getElem?_append_right (by simp; omega)]
  simp only [List.length_append, List.length_take, List.length_map, List.length_drop]
  have : C.gates.length - 1 - (min m C.gates.length + (C.gates.length - (m + 1))) = 0 := by
    omega
  rw [this]
  rfl

lemma red_lt (n m p i k : ℕ) (hp : p < n + m) (hmk : m ≤ k) (hi : i < n + k + 1) :
    eraseRedirect n m p i < n + k := by
  unfold eraseRedirect; split_ifs <;> omega

lemma gateAt_eq (C : Circuit) (j : ℕ) (g : Gate) (h : C.gates[j]? = some g) :
    PEqualNP.MetaComplexity.NestedCover.gateAt C j = g := by
  unfold PEqualNP.MetaComplexity.NestedCover.gateAt
  rw [List.getD_eq_getElem?_getD, h]
  rfl

lemma get_of_lt (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    C.gates[j]? = some (PEqualNP.MetaComplexity.NestedCover.gateAt C j) := by
  rw [gateAt_eq C j C.gates[j] (List.getElem?_eq_getElem hj)]
  exact List.getElem?_eq_getElem hj

lemma lift_AO2 (n : ℕ) (C : Circuit) (m p h : ℕ) (hm : m < C.gates.length)
    (hp : p < n + m) (hh : h < n + m) (hC : PEqualNP.TopForm.IsAO2 n C)
    (hout : C.output < n + C.gates.length) :
    PEqualNP.TopForm.IsAO2 n (liftAt n C m p h) := by
  obtain ⟨hAO, hRB, h2⟩ := hC
  have hmem : ∀ g ∈ (liftAt n C m p h).gates, (g ∈ C.gates) ∨
      (∃ g0 ∈ C.gates, g = ren n m p g0) ∨ g = ⟨GateOp.or, [eraseRedirect n m p C.output, h]⟩ := by
    intro g hg
    rw [lift_gates n C m p h hm] at hg
    simp only [List.mem_append, List.mem_map, List.mem_singleton] at hg
    rcases hg with (hg | ⟨g0, hg0, rfl⟩) | hg
    · exact Or.inl (List.mem_of_mem_take hg)
    · exact Or.inr (Or.inl ⟨g0, List.mem_of_mem_drop hg0, rfl⟩)
    · exact Or.inr (Or.inr hg)
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    rcases hmem g hg with hg | ⟨g0, hg0, rfl⟩ | rfl
    · exact hAO g hg
    · exact hAO g0 hg0
    · exact Or.inr rfl
  · intro j hj i hi
    rw [lift_len n C m p h hm] at hj
    by_cases hjm : j < m
    · have hget := lift_get_lt n C m p h hm j hjm
      rw [get_of_lt C j (by omega)] at hget
      rw [gateAt_eq _ j _ hget] at hi
      exact hRB j (by omega) i hi
    · by_cases hjl : j + 1 < C.gates.length
      · have hget := lift_get_mid n C m p h hm j (by omega) hjl
        rw [get_of_lt C (j + 1) hjl] at hget
        rw [gateAt_eq _ j _ hget] at hi
        simp only [Option.map_some, ren, List.mem_map] at hi
        obtain ⟨i0, hi0, rfl⟩ := hi
        exact red_lt n m p i0 j hp (by omega) (by have := hRB (j + 1) hjl i0 hi0; omega)
      · have hjeq : j = C.gates.length - 1 := by omega
        have hget := lift_get_last n C m p h hm
        rw [← hjeq] at hget
        rw [gateAt_eq _ j _ hget] at hi
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl
        · exact red_lt n m p C.output j hp (by omega) (by omega)
        · omega
  · intro g hg
    rcases hmem g hg with hg | ⟨g0, hg0, rfl⟩ | rfl
    · exact h2 g hg
    · simp [ren, h2 g0 hg0]
    · rfl

def BadAt (n : ℕ) (C : Circuit) (j : ℕ) : Prop :=
  ∃ a b : ℕ, C.gates[j]? = some ⟨GateOp.or, [a, b]⟩ ∧
    ((n ≤ b ∧ WireBelowOutput n C b ∧ ¬ WireBelowOutput n C a) ∨
      (n ≤ a ∧ WireBelowOutput n C a ∧ ¬ WireBelowOutput n C b))

open Classical in
noncomputable def badSet (n : ℕ) (C : Circuit) : Finset ℕ :=
  (Finset.range C.gates.length).filter (BadAt n C)

lemma mem_badSet (n : ℕ) (C : Circuit) (j : ℕ) :
    j ∈ badSet n C ↔ j < C.gates.length ∧ BadAt n C j := by
  unfold badSet
  simp [Finset.mem_filter, Finset.mem_range]

lemma inputs_two (C : Circuit) (j : ℕ) (g : Gate) (hg : C.gates[j]? = some g)
    (h2 : ∀ g ∈ C.gates, g.inputs.length = 2) : ∃ a b, g.inputs = [a, b] := by
  have : g ∈ C.gates := List.mem_of_getElem? hg
  exact List.length_eq_two.1 (h2 g this)

lemma lift_bad_lt (n : ℕ) (C : Circuit) (m p h : ℕ) (hm : m < C.gates.length)
    (hp : p < n + m) (hh : h < n + m)
    (hg : C.gates[m] = ⟨GateOp.or, [p, h]⟩ ∨ C.gates[m] = ⟨GateOp.or, [h, p]⟩)
    (hC : PEqualNP.TopForm.IsAO2 n C) (hout : C.output < n + C.gates.length)
    (hbelow : WireBelowOutput n C h) (hmbad : m ∈ badSet n C) :
    (badSet n (liftAt n C m p h)).card < (badSet n C).card := by
  obtain ⟨hAO, hRB, h2⟩ := hC
  have hT := lift_below n C m p h hm hp hh hg hAO hbelow
  let φ : ℕ → ℕ := fun j => if j < m then j else j + 1
  have hle : (badSet n (liftAt n C m p h)).card ≤ ((badSet n C).erase m).card := by
    apply Finset.card_le_card_of_injOn φ
    · intro j hj
      rw [Finset.mem_coe, mem_badSet, lift_len n C m p h hm] at hj
      obtain ⟨hjl, a', b', hget, hcond⟩ := hj
      rw [Finset.mem_coe, Finset.mem_erase, mem_badSet]
      by_cases hjm : j < m
      · have hφ : φ j = j := by simp [φ, hjm]
        rw [hφ]
        rw [lift_get_lt n C m p h hm j hjm] at hget
        have hab : a' < n + j ∧ b' < n + j := by
          have := hRB j (by omega)
          rw [gateAt_eq C j _ hget] at this
          exact ⟨this a' (by simp), this b' (by simp)⟩
        have ra : eraseRedirect n m p a' = a' := by unfold eraseRedirect; split_ifs <;> omega
        have rb : eraseRedirect n m p b' = b' := by unfold eraseRedirect; split_ifs <;> omega
        have ta := hT a' (by omega); rw [ra] at ta
        have tb := hT b' (by omega); rw [rb] at tb
        refine ⟨by omega, by omega, a', b', hget, ?_⟩
        rw [← ta, ← tb]; exact hcond
      · by_cases hjl2 : j + 1 < C.gates.length
        · have hφ : φ j = j + 1 := by simp [φ, hjm]
          rw [hφ]
          rw [lift_get_mid n C m p h hm j (by omega) hjl2] at hget
          obtain ⟨g0, hg0, hren⟩ := Option.map_eq_some_iff.1 hget
          obtain ⟨a0, b0, hab0⟩ := inputs_two C (j + 1) g0 hg0 h2
          simp only [ren, hab0, List.map_cons, List.map_nil, Gate.mk.injEq,
            List.cons.injEq, and_true] at hren
          obtain ⟨hop, ha, hb⟩ := hren
          have hg0' : C.gates[j + 1]? = some ⟨GateOp.or, [a0, b0]⟩ := by
            rw [hg0]; cases g0; simp_all
          have hlt : a0 < n + (j + 1) ∧ b0 < n + (j + 1) := by
            have := hRB (j + 1) hjl2
            rw [gateAt_eq C (j + 1) _ hg0] at this
            rw [hab0] at this
            exact ⟨this a0 (by simp), this b0 (by simp)⟩
          have ta := hT a0 (by omega); rw [ha] at ta
          have tb := hT b0 (by omega); rw [hb] at tb
          have gn : ∀ c, n ≤ eraseRedirect n m p c → n ≤ c := by
            intro c hc; unfold eraseRedirect at hc; split_ifs at hc <;> omega
          refine ⟨by omega, hjl2, a0, b0, hg0', ?_⟩
          rw [← ta, ← tb]
          rcases hcond with ⟨h1, h2', h3⟩ | ⟨h1, h2', h3⟩
          · exact Or.inl ⟨gn b0 (by rw [hb]; exact h1), h2', h3⟩
          · exact Or.inr ⟨gn a0 (by rw [ha]; exact h1), h2', h3⟩
        · exfalso
          have hjeq : j = C.gates.length - 1 := by omega
          rw [hjeq, lift_get_last n C m p h hm] at hget
          simp only [Option.some.injEq, Gate.mk.injEq, List.cons.injEq, and_true,
            true_and] at hget
          obtain ⟨rfl, rfl⟩ := hget
          have hbo : WireBelowOutput n (liftAt n C m p h) (eraseRedirect n m p C.output) := by
            intro x hx
            obtain ⟨W0, h1, -, -, h4⟩ := lift_facts n C m p h hm hp hh hg hAO (List.ofFn x)
              (by simp)
            rw [h1 C.output hout] at hx
            rw [h4, hx]; rfl
          have hbh : WireBelowOutput n (liftAt n C m p h) h := by
            have := hT h (by omega)
            have rh : eraseRedirect n m p h = h := by unfold eraseRedirect; split_ifs <;> omega
            rw [rh] at this
            exact this.2 hbelow
          rcases hcond with ⟨-, -, h3⟩ | ⟨-, -, h3⟩
          · exact h3 hbo
          · exact h3 hbh
    · intro a _ b _ hab
      simp only [φ] at hab
      split_ifs at hab <;> omega
  have hcard := Finset.card_erase_of_mem hmbad
  have hpos : 0 < (badSet n C).card := Finset.card_pos.2 ⟨m, hmbad⟩
  omega

theorem main (n : ℕ) : ∀ k : ℕ, ∀ C : Circuit, (badSet n C).card = k →
    PEqualNP.TopForm.IsAO2 n C → C.output < n + C.gates.length →
    ∃ C5 : Circuit, Relation.ReflTransGen (Lift n) C C5 ∧
      ∀ x6 < C5.gates.length, ∀ x8 x9 : ℕ,
        C5.gates[x6]? = some ⟨GateOp.or, [x8, x9]⟩ →
        (n ≤ x9 → WireBelowOutput n C5 x9 → WireBelowOutput n C5 x8) ∧
        (n ≤ x8 → WireBelowOutput n C5 x8 → WireBelowOutput n C5 x9) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro C hk hC hout
    by_cases hempty : badSet n C = ∅
    · refine ⟨C, Relation.ReflTransGen.refl, ?_⟩
      intro x6 hx6 x8 x9 hget
      have hnot : ¬ BadAt n C x6 := by
        intro hb
        have : x6 ∈ badSet n C := (mem_badSet n C x6).2 ⟨hx6, hb⟩
        rw [hempty] at this
        simp at this
      refine ⟨fun h1 h2 => ?_, fun h1 h2 => ?_⟩
      · by_contra h3; exact hnot ⟨x8, x9, hget, Or.inl ⟨h1, h2, h3⟩⟩
      · by_contra h3; exact hnot ⟨x8, x9, hget, Or.inr ⟨h1, h2, h3⟩⟩
    · obtain ⟨m, hmbad⟩ := Finset.nonempty_iff_ne_empty.2 hempty
      have hmb := hmbad
      rw [mem_badSet] at hmb
      obtain ⟨hm, a, b, hget, hcond⟩ := hmb
      have hRB := hC.2.1
      have hab : a < n + m ∧ b < n + m := by
        have := hRB m hm
        rw [gateAt_eq C m _ hget] at this
        exact ⟨this a (by simp), this b (by simp)⟩
      have hgm : C.gates[m] = ⟨GateOp.or, [a, b]⟩ := by
        rw [List.getElem?_eq_getElem hm] at hget
        exact Option.some.inj hget
      rcases hcond with ⟨hbn, hbb, -⟩ | ⟨han, hab', -⟩
      · have hL : Lift n C (liftAt n C m a b) :=
          ⟨m, hm, a, hab.1, b, hab.2, hbn, Or.inl hget, hbb, rfl⟩
        have hlt := lift_bad_lt n C m a b hm hab.1 hab.2 (Or.inl hgm) hC hout hbb hmbad
        obtain ⟨C5, hr, hgoal⟩ := ih _ (hk ▸ hlt) (liftAt n C m a b) rfl
          (lift_AO2 n C m a b hm hab.1 hab.2 hC hout)
          (by rw [lift_output n C m a b hm, lift_len n C m a b hm]; omega)
        exact ⟨C5, Relation.ReflTransGen.head hL hr, hgoal⟩
      · have hL : Lift n C (liftAt n C m b a) :=
          ⟨m, hm, b, hab.2, a, hab.1, han, Or.inr hget, hab', rfl⟩
        have hlt := lift_bad_lt n C m b a hm hab.2 hab.1 (Or.inr hgm) hC hout hab' hmbad
        obtain ⟨C5, hr, hgoal⟩ := ih _ (hk ▸ hlt) (liftAt n C m b a) rfl
          (lift_AO2 n C m b a hm hab.2 hab.1 hC hout)
          (by rw [lift_output n C m b a hm, lift_len n C m b a hm]; omega)
        exact ⟨C5, Relation.ReflTransGen.head hL hr, hgoal⟩

end PEqualNP.Outside.L_meta_4295

theorem PEqualNP.Outside.L_meta_4295 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x2 → x2.output < x1 + x2.gates.length → ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), Relation.ReflTransGen (PEqualNP.CircuitMoves.Lift x1) x2 x5 ∧ ∀ x6 < x5.gates.length, ∀ (x8 x9 : ℕ), x5.gates[x6]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [x8, x9] : PEqualNP.CircuitLowerBounds.Gate } → (x1 ≤ x9 → PEqualNP.CircuitMoves.WireBelowOutput x1 x5 x9 → PEqualNP.CircuitMoves.WireBelowOutput x1 x5 x8) ∧ (x1 ≤ x8 → PEqualNP.CircuitMoves.WireBelowOutput x1 x5 x8 → PEqualNP.CircuitMoves.WireBelowOutput x1 x5 x9) := by
  intro n C hC hout
  exact PEqualNP.Outside.L_meta_4295.main n _ C rfl hC hout
