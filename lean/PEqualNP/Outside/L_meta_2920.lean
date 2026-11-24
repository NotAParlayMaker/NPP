import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2920_aux

open PEqualNP.CircuitLowerBounds

/-- The wire-fold step of `Circuit.wires`, named so the fold lemmas below can
talk about it. -/
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl step x := rfl

/-- The fold appends exactly one wire per gate. -/
lemma foldl_length : ∀ (gs : List Gate) (x : List Bool),
    (gs.foldl step x).length = x.length + gs.length := by
  intro gs
  induction gs with
  | nil => intro x; simp
  | cons g gs ih =>
    intro x
    have h1 : (step x g).length = x.length + 1 := by simp [step]
    simp only [List.foldl_cons]
    rw [ih, h1]
    simp only [List.length_cons]
    omega

/-- Reading a wire list at an index below its length is unaffected by the fold:
the fold only appends. -/
lemma foldl_getD_of_lt : ∀ (gs : List Gate) (x : List Bool) (i : ℕ),
    i < x.length → (gs.foldl step x).getD i false = x.getD i false := by
  intro gs
  induction gs with
  | nil => intro x i _; rfl
  | cons g gs ih =>
    intro x i hi
    simp only [List.foldl_cons]
    rw [ih _ i (by
      have h1 : (step x g).length = x.length + 1 := by simp [step]
      omega : i < (step x g).length)]
    show (x ++ [_]).getD i false = x.getD i false
    rw [List.getD_eq_getElem?_getD, List.getElem?_append]
    simp [hi, List.getD_eq_getElem?_getD]

/-- The trichotomy for reading an appended list. -/
lemma getD_append_single (x : List Bool) (v : Bool) (i : ℕ) :
    (x ++ [v]).getD i false = if i = x.length then v else x.getD i false := by
  rcases lt_trichotomy i x.length with h | h | h
  · have h1 : (x ++ [v]).getD i false = x.getD i false := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_append]
      simp [h, List.getD_eq_getElem?_getD]
    rw [h1, if_neg (Nat.ne_of_lt h)]
  · subst h
    rw [if_pos rfl, List.getD_eq_getElem?_getD, List.getElem?_append]
    simp
  · have hle : (x ++ [v]).length ≤ i := by simp; omega
    have h1 : (x ++ [v]).getD i false = false := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hle]
      rfl
    have h2 : x.getD i false = false := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_lt h)]
      rfl
    rw [h1, h2, if_neg (Nat.ne_of_gt h)]

/-- One fold step over two wire lists that agree off two special indices, where
the gate reads neither special index, appends the same value to both. -/
lemma step_agree {s₁ s₂ : ℕ} {x y : List Bool} {g : Gate}
    (hlen : x.length = y.length)
    (hagree : ∀ i, i ≠ s₁ → i ≠ s₂ → x.getD i false = y.getD i false)
    (hg : s₁ ∉ g.inputs ∧ s₂ ∉ g.inputs) :
    (step x g).length = (step y g).length ∧
    (∀ i, i ≠ s₁ → i ≠ s₂ → (step x g).getD i false = (step y g).getD i false) := by
  have hval : g.op.eval (g.inputs.map fun i => x.getD i false)
      = g.op.eval (g.inputs.map fun i => y.getD i false) := by
    congr 1
    apply List.map_congr_left
    intro t ht
    exact hagree t (fun h => hg.1 (h ▸ ht)) (fun h => hg.2 (h ▸ ht))
  constructor
  · simp [step, hlen]
  · intro i hi₁ hi₂
    show (x ++ [_]).getD i false = (y ++ [_]).getD i false
    rw [getD_append_single, getD_append_single, hval]
    by_cases hi : i = x.length
    · rw [if_pos hi, if_pos (show i = y.length by omega)]
    · rw [if_neg hi, if_neg (show ¬ i = y.length by omega)]
      exact hagree i hi₁ hi₂

/-- Folding the *same* gates over two wire lists that agree off two special
indices preserves the agreement, when no gate reads a special index. -/
lemma foldl_agree {s₁ s₂ : ℕ} : ∀ (gs : List Gate) (x y : List Bool),
    x.length = y.length →
    (∀ i, i ≠ s₁ → i ≠ s₂ → x.getD i false = y.getD i false) →
    (∀ g ∈ gs, s₁ ∉ g.inputs ∧ s₂ ∉ g.inputs) →
    (gs.foldl step x).length = (gs.foldl step y).length ∧
    (∀ i, i ≠ s₁ → i ≠ s₂ →
      (gs.foldl step x).getD i false = (gs.foldl step y).getD i false) := by
  intro gs
  induction gs with
  | nil => intro x y hlen hagree _; exact ⟨hlen, hagree⟩
  | cons g gs ih =>
    intro x y hlen hagree hg
    simp only [List.foldl_cons]
    have hstep := step_agree hlen hagree (hg g List.mem_cons_self)
    exact ih _ _ hstep.1 hstep.2
      (fun g' hg' => hg g' (List.mem_cons_of_mem g hg'))

/-- The value at gate `k`'s own wire, in terms of the prefix fold before `k`. -/
lemma foldl_getD_gate : ∀ (k : ℕ) (gs : List Gate) (x : List Bool) (g : Gate),
    gs[k]? = some g →
    (gs.foldl step x).getD (x.length + k) false
      = g.op.eval (g.inputs.map fun i => ((gs.take k).foldl step x).getD i false) := by
  intro k
  induction k with
  | zero =>
    intro gs x g hg
    cases gs with
    | nil => simp at hg
    | cons g₀ gs =>
      simp only [List.getElem?_cons_zero] at hg
      injection hg with hg
      subst hg
      simp only [List.foldl_cons, List.take_zero, List.foldl_nil, Nat.add_zero]
      rw [foldl_getD_of_lt gs (step x g₀) x.length (by simp [step])]
      show (x ++ [_]).getD x.length false = _
      rw [getD_append_single]
      simp
  | succ k ih =>
    intro gs x g hg
    cases gs with
    | nil => simp at hg
    | cons g₀ gs =>
      have hg' : gs[k]? = some g := by simpa using hg
      have hstep : (step x g₀).length = x.length + 1 := by simp [step]
      have h := ih gs (step x g₀) g hg'
      rw [hstep] at h
      simp only [List.foldl_cons, List.take_succ_cons]
      have hidx : x.length + 1 + k = x.length + (k + 1) := by omega
      rw [hidx] at h
      exact h

/-- The value at gate `k`'s wire, in terms of the full wire list, when all the
gate's inputs are earlier wires. -/
lemma wires_gate_value (gs : List Gate) (x : List Bool) (k : ℕ) (g : Gate)
    (hg : gs[k]? = some g) (hinputs : ∀ t ∈ g.inputs, t < x.length + k) :
    (gs.foldl step x).getD (x.length + k) false
      = g.op.eval (g.inputs.map fun i => (gs.foldl step x).getD i false) := by
  have hk : k < gs.length := by
    by_contra h
    rw [List.getElem?_eq_none (Nat.le_of_not_lt h)] at hg
    simp at hg
  have hsplit : gs.foldl step x
      = (gs.drop k).foldl step ((gs.take k).foldl step x) := by
    conv_lhs => rw [← List.take_append_drop k gs]
    rw [List.foldl_append]
  rw [foldl_getD_gate k gs x g hg]
  congr 1
  apply List.map_congr_left
  intro t ht
  have hlen : ((gs.take k).foldl step x).length = x.length + k := by
    rw [foldl_length, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)]
  rw [hsplit]
  exact (foldl_getD_of_lt _ _ _ (by rw [hlen]; exact hinputs t ht)).symm

/-- Splitting a list after `p + 1` elements. -/
lemma take_succ' : ∀ (l : List Gate) (p : ℕ) (h : p < l.length),
    l.take (p + 1) = l.take p ++ [l[p]] := by
  intro l
  induction l with
  | nil => intro p h; simp at h
  | cons g l ih =>
    intro p h
    cases p with
    | zero => simp
    | succ p =>
      have h' : p < l.length := by
        simpa [List.length_cons] using h
      simp only [List.take_succ_cons, List.getElem_cons_succ]
      rw [ih p h', List.cons_append]

end PEqualNP.Outside.L_meta_2920_aux

open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_2920_aux

theorem PEqualNP.Outside.L_meta_2920 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (j is iv iw a b c z : ℕ)
    (op1 op2 : PEqualNP.CircuitLowerBounds.GateOp),
  ((op1 = PEqualNP.CircuitLowerBounds.GateOp.and ∧ op2 = PEqualNP.CircuitLowerBounds.GateOp.or) ∨
    (op1 = PEqualNP.CircuitLowerBounds.GateOp.or ∧ op2 = PEqualNP.CircuitLowerBounds.GateOp.and)) →
  C.gates[is]? = some { op := op2, inputs := [a, b] } →
  C.gates[iv]? = some { op := op2, inputs := [a, c] } →
  C.gates[iw]? = some { op := op1, inputs := [n + iv, z] } →
  (C.gates[j]? = some { op := op1, inputs := [n + is, n + iw] } ∨
    C.gates[j]? = some { op := op1, inputs := [n + iw, n + is] }) →
  is < j → iv < iw → iw < j →
  a < n + is → b < n + is → a < n + iv → b < n + iv → c < n + iv →
  z < n + iw → z ≠ n + iv →
  (∀ (k : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[k]? = some g → k ≠ iw → n + iv ∉ g.inputs) →
  (∀ (k : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[k]? = some g → k ≠ j → n + iw ∉ g.inputs) →
  C.output ≠ n + iv → C.output ≠ n + iw →
  PEqualNP.MetaComplexity.circuitFun n
      { gates := ((C.gates.set iv { op := op1, inputs := [b, c] }).set iw
            { op := op2, inputs := [a, n + iv] }).set j { op := op1, inputs := [n + iw, z] },
        output := C.output } =
    PEqualNP.MetaComplexity.circuitFun n C ∧
  (((C.gates.set iv { op := op1, inputs := [b, c] }).set iw
        { op := op2, inputs := [a, n + iv] }).set j { op := op1, inputs := [n + iw, z] }).length =
    C.gates.length := by
  intro n C j is iv iw a b c z op1 op2 hop his hiv hiw hj h_isj h_iviw h_iwj
    ha_is hb_is ha_iv hb_iv hc_iv hz_iw hz_ne hread1 hread2 hout1 hout2
  set G := C.gates with hGdef
  set G' := ((G.set iv { op := op1, inputs := [b, c] }).set iw
      { op := op2, inputs := [a, n + iv] }).set j
      { op := op1, inputs := [n + iw, z] } with hG'def
  have hlen' : G'.length = G.length := by simp [hG'def]
  have hiv_len : iv < G.length := by
    by_contra h
    rw [List.getElem?_eq_none (Nat.le_of_not_lt h)] at hiv
    simp at hiv
  have hiw_len : iw < G.length := by
    by_contra h
    rw [List.getElem?_eq_none (Nat.le_of_not_lt h)] at hiw
    simp at hiw
  have hj_len : j < G.length := by
    by_contra h
    rw [List.getElem?_eq_none (Nat.le_of_not_lt h)] at hj
    rcases hj with hj | hj <;> simp at hj
  have his_len : is < G.length := by
    by_contra h
    rw [List.getElem?_eq_none (Nat.le_of_not_lt h)] at his
    simp at his
  have hG'iv : G'[iv]? = some { op := op1, inputs := [b, c] } := by
    simp [hG'def, hiv_len, show j ≠ iv by omega, show iw ≠ iv by omega]
  have hG'iw : G'[iw]? = some { op := op2, inputs := [a, n + iv] } := by
    simp [hG'def, hiw_len, show j ≠ iw by omega]
  have hG'j : G'[j]? = some { op := op1, inputs := [n + iw, z] } := by
    simp [hG'def, hj_len]
  have hG'gen : ∀ p : ℕ, p ≠ iv → p ≠ iw → p ≠ j → G'[p]? = G[p]? := by
    intro p hp1 hp2 hp3
    simp [hG'def, show j ≠ p by omega, show iw ≠ p by omega, show iv ≠ p by omega]
  have hident : ∀ A B Cc Z : Bool,
      op1.eval [op2.eval [A, B], op1.eval [op2.eval [A, Cc], Z]]
        = op1.eval [op2.eval [A, op1.eval [B, Cc]], Z] := by
    intro A B Cc Z
    rcases hop with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      cases A <;> cases B <;> cases Cc <;> cases Z <;> rfl
  have hcomm : ∀ X Y : Bool, op1.eval [X, Y] = op1.eval [Y, X] := by
    intro X Y
    rcases hop with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> cases X <;> cases Y <;> rfl
  refine ⟨?_, hlen'⟩
  funext x
  have key : ∀ (x₀ : List Bool), x₀.length = n → ∀ p, p ≤ G.length →
      ((G.take p).foldl step x₀).length = ((G'.take p).foldl step x₀).length ∧
      (∀ i, i ≠ n + iv → i ≠ n + iw →
        ((G.take p).foldl step x₀).getD i false
          = ((G'.take p).foldl step x₀).getD i false) ∧
      (iv < p → ((G'.take p).foldl step x₀).getD (n + iv) false
        = op1.eval [((G.take p).foldl step x₀).getD b false,
                    ((G.take p).foldl step x₀).getD c false]) ∧
      (iw < p → ((G'.take p).foldl step x₀).getD (n + iw) false
        = op2.eval [((G.take p).foldl step x₀).getD a false,
                    ((G'.take p).foldl step x₀).getD (n + iv) false]) ∧
      (j < p → ((G.take p).foldl step x₀).getD (n + j) false
        = ((G'.take p).foldl step x₀).getD (n + j) false) := by
    intro x₀ hx₀ p
    induction p with
    | zero =>
      intro _
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp
      · intro i _ _
        simp
      · intro h; exact (Nat.not_lt_zero _ h).elim
      · intro h; exact (Nat.not_lt_zero _ h).elim
      · intro h; exact (Nat.not_lt_zero _ h).elim
    | succ p ih =>
      intro hp
      have hpG : p < G.length := hp
      have hpG' : p < G'.length := hlen' ▸ hpG
      obtain ⟨ihlen, ih2, ih3, ih4, ih5⟩ := ih (Nat.le_of_lt hpG)
      set W := (G.take p).foldl step x₀ with hW
      set W' := (G'.take p).foldl step x₀ with hW'
      have hWp : W.length = n + p := by
        rw [hW, foldl_length, hx₀, List.length_take, Nat.min_eq_left (Nat.le_of_lt hpG)]
      have hWp' : W'.length = n + p := by
        rw [hW', foldl_length, hx₀, List.length_take, Nat.min_eq_left (Nat.le_of_lt hpG')]
      have hstepW : (G.take (p + 1)).foldl step x₀ = step W G[p] := by
        rw [take_succ' G p hpG, List.foldl_append]
        rfl
      have hstepW' : (G'.take (p + 1)).foldl step x₀ = step W' G'[p] := by
        rw [take_succ' G' p hpG', List.foldl_append]
        rfl
      rw [hstepW, hstepW']
      by_cases hcase : p = iv ∨ p = iw ∨ p = j
      · rcases hcase with h | h | h
        · -- p = iv: gate iv is overwritten
          rw [h] at hWp hWp'
          have hgiv : G[p] = { op := op2, inputs := [a, c] } := by
            have h1 : G[p]? = some G[p] := List.getElem?_eq_getElem hpG
            have h2 : G[p]? = some { op := op2, inputs := [a, c] } := by
              rw [h]; exact hiv
            rw [h1] at h2
            exact Option.some.inj h2
          have hgiv' : G'[p] = { op := op1, inputs := [b, c] } := by
            have h1 : G'[p]? = some G'[p] := List.getElem?_eq_getElem hpG'
            have h2 : G'[p]? = some { op := op1, inputs := [b, c] } := by
              rw [h]; exact hG'iv
            rw [h1] at h2
            exact Option.some.inj h2
          rw [hgiv, hgiv']
          refine ⟨?_, ?_, ?_, ?_, ?_⟩
          · show (W ++ [_]).length = (W' ++ [_]).length
            simp [hWp, hWp']
          · intro i hi1 hi2
            show (W ++ [_]).getD i false = (W' ++ [_]).getD i false
            rw [getD_append_single, getD_append_single, hWp, hWp',
              if_neg hi1, if_neg hi1]
            exact ih2 i hi1 hi2
          · intro _
            show (W' ++ [_]).getD (n + iv) false
              = op1.eval [(W ++ [_]).getD b false, (W ++ [_]).getD c false]
            rw [getD_append_single, getD_append_single, getD_append_single,
              hWp, hWp', if_pos rfl,
              if_neg (show b ≠ n + iv by omega), if_neg (show c ≠ n + iv by omega),
              ih2 b (by omega) (by omega), ih2 c (by omega) (by omega)]
            rfl
          · intro h
            exact (by omega : False).elim
          · intro h
            exact (by omega : False).elim
        · -- p = iw: gate iw is overwritten
          rw [h] at hWp hWp'
          have hgiw : G[p] = { op := op1, inputs := [n + iv, z] } := by
            have h1 : G[p]? = some G[p] := List.getElem?_eq_getElem hpG
            have h2 : G[p]? = some { op := op1, inputs := [n + iv, z] } := by
              rw [h]; exact hiw
            rw [h1] at h2
            exact Option.some.inj h2
          have hgiw' : G'[p] = { op := op2, inputs := [a, n + iv] } := by
            have h1 : G'[p]? = some G'[p] := List.getElem?_eq_getElem hpG'
            have h2 : G'[p]? = some { op := op2, inputs := [a, n + iv] } := by
              rw [h]; exact hG'iw
            rw [h1] at h2
            exact Option.some.inj h2
          rw [hgiw, hgiw']
          refine ⟨?_, ?_, ?_, ?_, ?_⟩
          · show (W ++ [_]).length = (W' ++ [_]).length
            simp [hWp, hWp']
          · intro i hi1 hi2
            show (W ++ [_]).getD i false = (W' ++ [_]).getD i false
            rw [getD_append_single, getD_append_single, hWp, hWp',
              if_neg hi2, if_neg hi2]
            exact ih2 i hi1 hi2
          · intro _
            show (W' ++ [_]).getD (n + iv) false
              = op1.eval [(W ++ [_]).getD b false, (W ++ [_]).getD c false]
            rw [getD_append_single, getD_append_single, getD_append_single,
              hWp, hWp', if_neg (show n + iv ≠ n + iw by omega),
              if_neg (show b ≠ n + iw by omega), if_neg (show c ≠ n + iw by omega)]
            exact ih3 (by omega)
          · intro _
            show (W' ++ [_]).getD (n + iw) false
              = op2.eval [(W ++ [_]).getD a false, (W' ++ [_]).getD (n + iv) false]
            rw [getD_append_single, getD_append_single, getD_append_single,
              hWp, hWp', if_pos rfl,
              if_neg (show a ≠ n + iw by omega),
              if_neg (show n + iv ≠ n + iw by omega),
              ih2 a (by omega) (by omega)]
            rfl
          · intro h
            exact (by omega : False).elim
        · -- p = j: gate j is overwritten; the distributivity step
          rw [h] at hWp hWp' hW hW'
          have hgj : G[p] = { op := op1, inputs := [n + is, n + iw] }
              ∨ G[p] = { op := op1, inputs := [n + iw, n + is] } := by
            have h1 : G[p]? = some G[p] := List.getElem?_eq_getElem hpG
            have h2 : G[p]? = some { op := op1, inputs := [n + is, n + iw] }
                ∨ G[p]? = some { op := op1, inputs := [n + iw, n + is] } := by
              rw [h]; exact hj
            rw [h1] at h2
            rcases h2 with h2 | h2
            · exact Or.inl (Option.some.inj h2)
            · exact Or.inr (Option.some.inj h2)
          have hgj' : G'[p] = { op := op1, inputs := [n + iw, z] } := by
            have h1 : G'[p]? = some G'[p] := List.getElem?_eq_getElem hpG'
            have h2 : G'[p]? = some { op := op1, inputs := [n + iw, z] } := by
              rw [h]; exact hG'j
            rw [h1] at h2
            exact Option.some.inj h2
          have hWis : W.getD (n + is) false
              = op2.eval [W.getD a false, W.getD b false] := by
            have h1 : (G.take j)[is]? = some { op := op2, inputs := [a, b] } := by
              rw [List.getElem?_take_of_lt h_isj]; exact his
            have h2 := wires_gate_value (G.take j) x₀ is
              { op := op2, inputs := [a, b] } h1 (by
                intro t ht
                change t ∈ [a, b] at ht
                simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil,
                  or_false] at ht
                rcases ht with rfl | rfl
                · rw [hx₀]; exact ha_is
                · rw [hx₀]; exact hb_is)
            rw [hx₀, ← hW] at h2
            exact h2
          have hWiv : W.getD (n + iv) false
              = op2.eval [W.getD a false, W.getD c false] := by
            have h1 : (G.take j)[iv]? = some { op := op2, inputs := [a, c] } := by
              rw [List.getElem?_take_of_lt (by omega)]; exact hiv
            have h2 := wires_gate_value (G.take j) x₀ iv
              { op := op2, inputs := [a, c] } h1 (by
                intro t ht
                change t ∈ [a, c] at ht
                simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil,
                  or_false] at ht
                rcases ht with rfl | rfl
                · rw [hx₀]; exact ha_iv
                · rw [hx₀]; exact hc_iv)
            rw [hx₀, ← hW] at h2
            exact h2
          have hWiw : W.getD (n + iw) false
              = op1.eval [W.getD (n + iv) false, W.getD z false] := by
            have h1 : (G.take j)[iw]? = some { op := op1, inputs := [n + iv, z] } := by
              rw [List.getElem?_take_of_lt h_iwj]; exact hiw
            have h2 := wires_gate_value (G.take j) x₀ iw
              { op := op1, inputs := [n + iv, z] } h1 (by
                intro t ht
                change t ∈ [n + iv, z] at ht
                simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil,
                  or_false] at ht
                rcases ht with rfl | rfl
                · rw [hx₀]; omega
                · rw [hx₀]; exact hz_iw)
            rw [hx₀, ← hW] at h2
            exact h2
          have hvaleq : op1.eval [W.getD (n + is) false, W.getD (n + iw) false]
              = op1.eval [W'.getD (n + iw) false, W'.getD z false] := by
            rw [hWis, hWiw, hWiv, ih4 (by omega), ih3 (by omega),
              (ih2 z hz_ne (by omega)).symm]
            exact hident _ _ _ _
          have holdval : (step W G[p]).getD (n + j) false
              = op1.eval [W.getD (n + is) false, W.getD (n + iw) false] := by
            rcases hgj with hgj | hgj
            · rw [hgj]
              show (W ++ [op1.eval [W.getD (n + is) false,
                W.getD (n + iw) false]]).getD (n + j) false = _
              rw [getD_append_single, hWp, if_pos rfl]
            · rw [hgj]
              show (W ++ [op1.eval [W.getD (n + iw) false,
                W.getD (n + is) false]]).getD (n + j) false = _
              rw [getD_append_single, hWp, if_pos rfl]
              exact hcomm _ _
          have hnewval : (step W' G'[p]).getD (n + j) false
              = op1.eval [W'.getD (n + iw) false, W'.getD z false] := by
            rw [hgj']
            show (W' ++ [op1.eval [W'.getD (n + iw) false,
              W'.getD z false]]).getD (n + j) false = _
            rw [getD_append_single, hWp', if_pos rfl]
          refine ⟨?_, ?_, ?_, ?_, ?_⟩
          · show (W ++ [_]).length = (W' ++ [_]).length
            simp [hWp, hWp']
          · intro i hi1 hi2
            by_cases hii : i = n + j
            · subst hii
              rw [holdval, hnewval]
              exact hvaleq
            · show (W ++ [_]).getD i false = (W' ++ [_]).getD i false
              rw [getD_append_single, getD_append_single, hWp, hWp',
                if_neg hii, if_neg hii]
              exact ih2 i hi1 hi2
          · intro _
            show (W' ++ [_]).getD (n + iv) false
              = op1.eval [(W ++ [_]).getD b false, (W ++ [_]).getD c false]
            rw [getD_append_single, getD_append_single, getD_append_single,
              hWp, hWp', if_neg (show n + iv ≠ n + j by omega),
              if_neg (show b ≠ n + j by omega), if_neg (show c ≠ n + j by omega)]
            exact ih3 (by omega)
          · intro _
            show (W' ++ [_]).getD (n + iw) false
              = op2.eval [(W ++ [_]).getD a false, (W' ++ [_]).getD (n + iv) false]
            rw [getD_append_single, getD_append_single, getD_append_single,
              hWp, hWp', if_neg (show n + iw ≠ n + j by omega),
              if_neg (show a ≠ n + j by omega),
              if_neg (show n + iv ≠ n + j by omega)]
            exact ih4 (by omega)
          · intro _
            rw [holdval, hnewval]
            exact hvaleq
      · -- generic step: the gate is the same in both circuits
        push_neg at hcase
        obtain ⟨hpiv, hpiw, hpj⟩ := hcase
        have hg_eq : G'[p] = G[p] := by
          have h1 : G'[p]? = some G'[p] := List.getElem?_eq_getElem hpG'
          have h2 : G[p]? = some G[p] := List.getElem?_eq_getElem hpG
          rw [hG'gen p hpiv hpiw hpj, h2] at h1
          exact (Option.some.inj h1).symm
        have hread : n + iv ∉ G[p].inputs ∧ n + iw ∉ G[p].inputs :=
          ⟨hread1 p G[p] (List.getElem?_eq_getElem hpG) (by omega),
           hread2 p G[p] (List.getElem?_eq_getElem hpG) hpj⟩
        have hstep := step_agree ihlen ih2 hread
        rw [hg_eq]
        refine ⟨hstep.1, hstep.2, ?_, ?_, ?_⟩
        · intro h
          have hivp : iv < p := by omega
          show (W' ++ [_]).getD (n + iv) false
            = op1.eval [(W ++ [_]).getD b false, (W ++ [_]).getD c false]
          rw [getD_append_single, getD_append_single, getD_append_single,
            hWp, hWp', if_neg (show n + iv ≠ n + p by omega),
            if_neg (show b ≠ n + p by omega), if_neg (show c ≠ n + p by omega)]
          exact ih3 hivp
        · intro h
          have hiwp : iw < p := by omega
          show (W' ++ [_]).getD (n + iw) false
            = op2.eval [(W ++ [_]).getD a false, (W' ++ [_]).getD (n + iv) false]
          rw [getD_append_single, getD_append_single, getD_append_single,
            hWp, hWp', if_neg (show n + iw ≠ n + p by omega),
            if_neg (show a ≠ n + p by omega),
            if_neg (show n + iv ≠ n + p by omega)]
          exact ih4 hiwp
        · intro h
          have hjp : j < p := by omega
          show (W ++ [_]).getD (n + j) false = (W' ++ [_]).getD (n + j) false
          rw [getD_append_single, getD_append_single, hWp, hWp',
            if_neg (show n + j ≠ n + p by omega),
            if_neg (show n + j ≠ n + p by omega)]
          exact ih5 hjp
  have hfin := (key (List.ofFn x) List.length_ofFn G.length (le_refl _)).2.1
    C.output hout1 hout2
  rw [List.take_of_length_le (le_refl _),
    show G'.take G.length = G' from by
      rw [← hlen']; exact List.take_of_length_le (le_refl _)] at hfin
  show ((⟨G', C.output⟩ : Circuit).wires (List.ofFn x)).getD C.output false
    = (C.wires (List.ofFn x)).getD C.output false
  exact hfin.symm
