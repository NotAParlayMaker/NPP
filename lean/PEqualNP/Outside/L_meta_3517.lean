import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3517

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

def wireStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_wireStep_length (gs : List Gate) (init : List Bool) :
    (gs.foldl wireStep init).length = init.length + gs.length := by
  induction gs generalizing init with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih (wireStep init g)]
    simp only [wireStep, List.length_append, List.length_cons, List.length_nil]
    omega

lemma getD_append_left {α : Type} (l₁ l₂ : List α) (i : ℕ) (d : α) (hi : i < l₁.length) :
    (l₁ ++ l₂).getD i d = l₁.getD i d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_append_right_singleton {α : Type} (l : List α) (v d : α) :
    (l ++ [v]).getD l.length d = v := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_concat_length, Option.getD_some]

lemma getD_of_length_le {α : Type} (l : List α) (i : ℕ) (d : α) (hi : l.length ≤ i) :
    l.getD i d = d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi, Option.getD_none]

lemma getD_eq_getElem {α : Type} (l : List α) (i : ℕ) (d : α) (hi : i < l.length) :
    l.getD i d = l[i] := by
  simp [List.getD_eq_getElem?_getD, hi]

lemma nodup_pair {α : Type} (x y : α) (h : x ≠ y) : [x, y].Nodup := by
  simp [h]

lemma wireStep_length (w : List Bool) (g : Gate) :
    (wireStep w g).length = w.length + 1 := by
  simp [wireStep]

lemma wireStep_getD_lt (w : List Bool) (g : Gate) (i : ℕ) (hi : i < w.length) :
    (wireStep w g).getD i false = w.getD i false := by
  exact getD_append_left w _ i false hi

lemma foldl_wireStep_getD_lt (gs : List Gate) (init : List Bool) (i : ℕ) (hi : i < init.length) :
    (gs.foldl wireStep init).getD i false = init.getD i false := by
  induction gs generalizing init with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlen : i < (wireStep init g).length := by
      rw [wireStep_length]
      omega
    rw [ih (wireStep init g) hlen]
    exact wireStep_getD_lt init g i hi

lemma wireStep_getD_self_or (w : List Bool) (a b : ℕ) :
    (wireStep w ⟨GateOp.or, [a, b]⟩).getD w.length false = (w.getD a false || w.getD b false) := by
  dsimp only [wireStep]
  rw [getD_append_right_singleton]
  simp [GateOp.eval]

lemma eval_or_pair (a b : Bool) : GateOp.or.eval [a, b] = (a || b) := by
  simp [GateOp.eval]

lemma eval_and_pair (a b : Bool) : GateOp.and.eval [a, b] = (a && b) := by
  simp [GateOp.eval]

def idxList : List (Fin 14) :=
  [(0 : Fin 14), (1 : Fin 14), (2 : Fin 14), (3 : Fin 14), (5 : Fin 14),
    (6 : Fin 14), (7 : Fin 14), (8 : Fin 14), (9 : Fin 14), (12 : Fin 14)]

def remapWire (w : ℕ) : ℕ :=
  if w < 10 then (idxList.getD w (0 : Fin 14)).val else w + 4

lemma remapWire_lt_14 (w : ℕ) (hw : w < 10) : remapWire w < 14 := by
  simp only [remapWire, hw, ↓reduceIte]
  exact (idxList.getD w (0 : Fin 14)).isLt

lemma remapWire_lt (w j : ℕ) (hw : w < 10 + j) : remapWire w < 14 + j := by
  by_cases h : w < 10
  · have := remapWire_lt_14 w h
    omega
  · simp only [remapWire, h, ↓reduceIte]
    omega

lemma idxList_inj_lt : ∀ a < 10, ∀ b < 10,
    (idxList.getD a (0 : Fin 14)).val = (idxList.getD b (0 : Fin 14)).val → a = b := by
  decide

lemma remapWire_injective : Function.Injective remapWire := by
  intro a b hab
  by_cases ha : a < 10 <;> by_cases hb : b < 10
  · simp only [remapWire, ha, hb, ↓reduceIte] at hab
    exact idxList_inj_lt a ha b hb hab
  · have hlt := remapWire_lt_14 a ha
    rw [hab] at hlt
    simp only [remapWire, hb, ↓reduceIte] at hlt
    omega
  · have hlt := remapWire_lt_14 b hb
    rw [← hab] at hlt
    simp only [remapWire, ha, ↓reduceIte] at hlt
    omega
  · simp only [remapWire, ha, hb, ↓reduceIte] at hab
    omega

def remapGate (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map remapWire⟩

lemma foldl_wireStep_take_succ (gs : List Gate) (init : List Bool) (k : ℕ) (hk : k < gs.length) :
    (gs.take (k + 1)).foldl wireStep init = wireStep ((gs.take k).foldl wireStep init) gs[k] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some, List.foldl_append]
  rfl

lemma remap_wire_agree (x1 : Circuit) (hao : IsAO2 10 x1) (x5 : Fin 14 → Bool) :
    ∀ k ≤ x1.gates.length,
      ((x1.gates.take k).foldl wireStep (List.ofFn fun x6 : Fin 10 => x5 (idxList.getD x6.val (0 : Fin 14)))).length = 10 + k ∧
      (((x1.gates.map remapGate).take k).foldl wireStep (List.ofFn x5)).length = 14 + k ∧
      ∀ u < 10 + k,
        (((x1.gates.map remapGate).take k).foldl wireStep (List.ofFn x5)).getD (remapWire u) false =
          ((x1.gates.take k).foldl wireStep (List.ofFn fun x6 : Fin 10 => x5 (idxList.getD x6.val (0 : Fin 14)))).getD u false := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨?_, ?_, ?_⟩
    · simp
    · simp
    · intro u hu
      simp only [List.take_zero, List.foldl_nil]
      have hrm : remapWire u = (idxList.getD u (0 : Fin 14)).val := by
        simp [remapWire, hu]
      have hlt : remapWire u < (List.ofFn x5).length := by
        rw [List.length_ofFn]
        exact remapWire_lt_14 u hu
      have hlt0 : u < (List.ofFn fun x6 : Fin 10 => x5 (idxList.getD x6.val (0 : Fin 14))).length := by
        rw [List.length_ofFn]
        exact hu
      rw [getD_eq_getElem _ _ false hlt, getD_eq_getElem _ _ false hlt0,
        List.getElem_ofFn, List.getElem_ofFn]
      congr 1
      exact Fin.ext hrm
  | succ k ih =>
    intro hkle
    have hklt : k < x1.gates.length := Nat.lt_of_succ_le hkle
    rcases ih (Nat.le_of_lt hklt) with ⟨hlen0, hlen1, hagree⟩
    set w₀ := (x1.gates.take k).foldl wireStep (List.ofFn fun x6 : Fin 10 => x5 (idxList.getD x6.val (0 : Fin 14)))
    set w₁ := ((x1.gates.map remapGate).take k).foldl wireStep (List.ofFn x5)
    have hsucc0 : (x1.gates.take (k + 1)).foldl wireStep
        (List.ofFn fun x6 : Fin 10 => x5 (idxList.getD x6.val (0 : Fin 14))) = wireStep w₀ x1.gates[k] :=
      foldl_wireStep_take_succ x1.gates _ k hklt
    have hklt_map : k < (x1.gates.map remapGate).length := by
      simp [hklt]
    have hsucc1 : ((x1.gates.map remapGate).take (k + 1)).foldl wireStep (List.ofFn x5) =
        wireStep w₁ (remapGate x1.gates[k]) := by
      have h := foldl_wireStep_take_succ (x1.gates.map remapGate) (List.ofFn x5) k hklt_map
      rw [List.getElem_map] at h
      exact h
    rw [hsucc0, hsucc1]
    refine ⟨?_, ?_, ?_⟩
    · rw [wireStep_length, hlen0]
      omega
    · rw [wireStep_length, hlen1]
      omega
    · intro u hu
      by_cases hult : u < 10 + k
      · have hrm : remapWire u < 14 + k := remapWire_lt u k hult
        rw [wireStep_getD_lt w₁ _ (remapWire u) (by omega),
          wireStep_getD_lt w₀ _ u (by omega)]
        exact hagree u hult
      · have hueq : u = 10 + k := by omega
        have hrmeq : remapWire u = 14 + k := by
          simp only [remapWire, hueq]
          have hge : ¬ (10 + k < 10) := by omega
          simp [hge]
          omega
        rw [hrmeq, hueq, ← hlen1, ← hlen0]
        dsimp only [wireStep]
        rw [getD_append_right_singleton, getD_append_right_singleton]
        have hrb : ∀ i ∈ x1.gates[k].inputs, i < 10 + k := by
          intro i hi
          have h := hao.2.1 k hklt i
          have hgate : gateAt x1 k = x1.gates[k] := by
            simp [gateAt, hklt]
          rw [hgate] at h
          exact h hi
        have hmaps : (remapGate x1.gates[k]).inputs.map (fun i => w₁.getD i false) =
            x1.gates[k].inputs.map (fun i => w₀.getD i false) := by
          dsimp only [remapGate]
          rw [List.map_map]
          apply List.map_congr_left
          intro i hi
          exact hagree i (hrb i hi)
        dsimp only [remapGate] at *
        rw [hmaps]

lemma foldl_bin_step (w w0 : List Bool) (op : GateOp) (a c : ℕ) (va vc : Bool)
    (m b : ℕ) (gs : List Gate) (P : List Bool → Prop)
    (hm : w.length = m) (hb : b ≤ m)
    (h0 : ∀ i < b, w.getD i false = w0.getD i false)
    (ha : w.getD a false = va) (hc : w.getD c false = vc)
    (h : ∀ w', w'.length = m + 1 →
      (∀ i < b, w'.getD i false = w0.getD i false) →
      (∀ i < m, w'.getD i false = w.getD i false) →
      w'.getD m false = op.eval [va, vc] →
      P (gs.foldl wireStep w')) :
    P ((⟨op, [a, c]⟩ :: gs).foldl wireStep w) := by
  simp only [List.foldl_cons]
  apply h (wireStep w ⟨op, [a, c]⟩)
  · rw [wireStep_length, hm]
  · intro i hi
    rw [wireStep_getD_lt w _ i (by omega), h0 i hi]
  · intro i hi
    exact wireStep_getD_lt w _ i (by omega)
  · dsimp only [wireStep]
    rw [← hm, getD_append_right_singleton, List.map_cons, List.map_cons, List.map_nil, ha, hc]

def extra11 (b : ℕ) : List Gate :=
  [⟨GateOp.or, [0, 4]⟩,
   ⟨GateOp.or, [b, 5]⟩,
   ⟨GateOp.and, [10, b + 1]⟩,
   ⟨GateOp.or, [3, 4]⟩,
   ⟨GateOp.or, [b + 3, 6]⟩,
   ⟨GateOp.and, [11, b + 4]⟩,
   ⟨GateOp.or, [1, 2]⟩,
   ⟨GateOp.or, [b + 6, 4]⟩,
   ⟨GateOp.and, [13, b + 7]⟩,
   ⟨GateOp.or, [b + 2, b + 5]⟩,
   ⟨GateOp.or, [b + 9, b + 8]⟩]

lemma extra11_eval (w : List Bool) (b : ℕ) (hb14 : 14 ≤ b) (hlen : w.length = b)
    (x5 : Fin 14 → Bool) (hin : ∀ i : Fin 14, w.getD i.val false = x5 i) :
    ((extra11 b).foldl wireStep w).length = b + 11 ∧
    (∀ i < b, ((extra11 b).foldl wireStep w).getD i false = w.getD i false) ∧
    ((extra11 b).foldl wireStep w).getD (b + 10) false =
      (((x5 10 && ((x5 0 || x5 4) || x5 5)) ||
        (x5 11 && ((x5 3 || x5 4) || x5 6))) ||
        (x5 13 && ((x5 1 || x5 2) || x5 4))) := by
  let P : List Bool → Prop := fun res =>
    res.length = b + 11 ∧
    (∀ i < b, res.getD i false = w.getD i false) ∧
    res.getD (b + 10) false =
      (((x5 10 && ((x5 0 || x5 4) || x5 5)) ||
        (x5 11 && ((x5 3 || x5 4) || x5 6))) ||
        (x5 13 && ((x5 1 || x5 2) || x5 4)))
  change P ((extra11 b).foldl wireStep w)
  dsimp only [extra11]
  apply foldl_bin_step w w GateOp.or 0 4 (x5 0) (x5 4) b b _ P hlen le_rfl (fun _ _ => rfl) (hin 0) (hin 4)
  intro s0 l0 h0_0 _ hv0
  rw [eval_or_pair] at hv0
  apply foldl_bin_step s0 w GateOp.or b 5 (x5 0 || x5 4) (x5 5) (b + 1) b _ P l0 (by omega) h0_0 hv0
    (by rw [h0_0 5 (by omega)]; exact hin 5)
  intro s1 l1 h1_0 _ hv1
  rw [eval_or_pair] at hv1
  apply foldl_bin_step s1 w GateOp.and 10 (b + 1) (x5 10) ((x5 0 || x5 4) || x5 5) (b + 2) b _ P l1 (by omega) h1_0
    (by rw [h1_0 10 (by omega)]; exact hin 10) hv1
  intro s2 l2 h2_0 _ hv2
  rw [eval_and_pair] at hv2
  apply foldl_bin_step s2 w GateOp.or 3 4 (x5 3) (x5 4) (b + 3) b _ P l2 (by omega) h2_0
    (by rw [h2_0 3 (by omega)]; exact hin 3) (by rw [h2_0 4 (by omega)]; exact hin 4)
  intro s3 l3 h3_0 hp3 hv3
  rw [eval_or_pair] at hv3
  apply foldl_bin_step s3 w GateOp.or (b + 3) 6 (x5 3 || x5 4) (x5 6) (b + 4) b _ P l3 (by omega) h3_0 hv3
    (by rw [h3_0 6 (by omega)]; exact hin 6)
  intro s4 l4 h4_0 hp4 hv4
  rw [eval_or_pair] at hv4
  apply foldl_bin_step s4 w GateOp.and 11 (b + 4) (x5 11) ((x5 3 || x5 4) || x5 6) (b + 5) b _ P l4 (by omega) h4_0
    (by rw [h4_0 11 (by omega)]; exact hin 11) hv4
  intro s5 l5 h5_0 hp5 hv5
  rw [eval_and_pair] at hv5
  apply foldl_bin_step s5 w GateOp.or 1 2 (x5 1) (x5 2) (b + 6) b _ P l5 (by omega) h5_0
    (by rw [h5_0 1 (by omega)]; exact hin 1) (by rw [h5_0 2 (by omega)]; exact hin 2)
  intro s6 l6 h6_0 hp6 hv6
  rw [eval_or_pair] at hv6
  apply foldl_bin_step s6 w GateOp.or (b + 6) 4 (x5 1 || x5 2) (x5 4) (b + 7) b _ P l6 (by omega) h6_0 hv6
    (by rw [h6_0 4 (by omega)]; exact hin 4)
  intro s7 l7 h7_0 hp7 hv7
  rw [eval_or_pair] at hv7
  apply foldl_bin_step s7 w GateOp.and 13 (b + 7) (x5 13) ((x5 1 || x5 2) || x5 4) (b + 8) b _ P l7 (by omega) h7_0
    (by rw [h7_0 13 (by omega)]; exact hin 13) hv7
  intro s8 l8 h8_0 hp8 hv8
  rw [eval_and_pair] at hv8
  have hs8_b2 : s8.getD (b + 2) false = (x5 10 && ((x5 0 || x5 4) || x5 5)) := by
    rw [hp8 (b + 2) (by omega), hp7 (b + 2) (by omega), hp6 (b + 2) (by omega),
      hp5 (b + 2) (by omega), hp4 (b + 2) (by omega), hp3 (b + 2) (by omega), hv2]
  have hs8_b5 : s8.getD (b + 5) false = (x5 11 && ((x5 3 || x5 4) || x5 6)) := by
    rw [hp8 (b + 5) (by omega), hp7 (b + 5) (by omega), hp6 (b + 5) (by omega), hv5]
  apply foldl_bin_step s8 w GateOp.or (b + 2) (b + 5)
    (x5 10 && ((x5 0 || x5 4) || x5 5)) (x5 11 && ((x5 3 || x5 4) || x5 6))
    (b + 9) b _ P l8 (by omega) h8_0 hs8_b2 hs8_b5
  intro s9 l9 h9_0 hp9 hv9
  rw [eval_or_pair] at hv9
  have hs9_b8 : s9.getD (b + 8) false = (x5 13 && ((x5 1 || x5 2) || x5 4)) := by
    rw [hp9 (b + 8) (by omega), hv8]
  apply foldl_bin_step s9 w GateOp.or (b + 9) (b + 8)
    ((x5 10 && ((x5 0 || x5 4) || x5 5)) || (x5 11 && ((x5 3 || x5 4) || x5 6)))
    (x5 13 && ((x5 1 || x5 2) || x5 4)) (b + 10) b _ P l9 (by omega) h9_0 hv9 hs9_b8
  intro s10 l10 h10_0 _ hv10
  rw [eval_or_pair] at hv10
  simp only [List.foldl_nil]
  exact ⟨l10, h10_0, hv10⟩

lemma extraBool_eq_decide (x5 : Fin 14 → Bool) :
    (((x5 10 && ((x5 0 || x5 4) || x5 5)) || (x5 11 && ((x5 3 || x5 4) || x5 6))) ||
      (x5 13 && ((x5 1 || x5 2) || x5 4))) =
      Decidable.decide (∃ (x6 : Fin 14) (x7 : Fin 14),
        (x6.val, x7.val) ∈ [((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (13 : ℕ)),
          ((3 : ℕ), (11 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)),
          ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((6 : ℕ), (11 : ℕ))] ∧
          x5 x6 = Bool.true ∧ x5 x7 = Bool.true) := by
  rw [Bool.eq_iff_iff, decide_eq_true_eq]
  constructor
  · intro h
    simp only [Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with (⟨h10, h04 | h5⟩ | ⟨h11, h34 | h6⟩) | ⟨h13, h12 | h4⟩
    · rcases h04 with h0 | h4
      · exact ⟨0, 10, by decide, h0, h10⟩
      · exact ⟨4, 10, by decide, h4, h10⟩
    · exact ⟨5, 10, by decide, h5, h10⟩
    · rcases h34 with h3 | h4
      · exact ⟨3, 11, by decide, h3, h11⟩
      · exact ⟨4, 11, by decide, h4, h11⟩
    · exact ⟨6, 11, by decide, h6, h11⟩
    · rcases h12 with h1 | h2
      · exact ⟨1, 13, by decide, h1, h13⟩
      · exact ⟨2, 13, by decide, h2, h13⟩
    · exact ⟨4, 13, by decide, h4, h13⟩
  · rintro ⟨u, v, hmem, hu, hv⟩
    simp only [Bool.or_eq_true, Bool.and_eq_true]
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hmem
    rcases hmem with ⟨hu0, hv0⟩ | ⟨hu0, hv0⟩ | ⟨hu0, hv0⟩ | ⟨hu0, hv0⟩ | ⟨hu0, hv0⟩ |
        ⟨hu0, hv0⟩ | ⟨hu0, hv0⟩ | ⟨hu0, hv0⟩ | ⟨hu0, hv0⟩
    · have hu' : u = 0 := Fin.ext hu0
      have hv' : v = 10 := Fin.ext hv0
      subst hu' hv'
      exact Or.inl (Or.inl ⟨hv, Or.inl (Or.inl hu)⟩)
    · have hu' : u = 1 := Fin.ext hu0
      have hv' : v = 13 := Fin.ext hv0
      subst hu' hv'
      exact Or.inr ⟨hv, Or.inl (Or.inl hu)⟩
    · have hu' : u = 2 := Fin.ext hu0
      have hv' : v = 13 := Fin.ext hv0
      subst hu' hv'
      exact Or.inr ⟨hv, Or.inl (Or.inr hu)⟩
    · have hu' : u = 3 := Fin.ext hu0
      have hv' : v = 11 := Fin.ext hv0
      subst hu' hv'
      exact Or.inl (Or.inr ⟨hv, Or.inl (Or.inl hu)⟩)
    · have hu' : u = 4 := Fin.ext hu0
      have hv' : v = 10 := Fin.ext hv0
      subst hu' hv'
      exact Or.inl (Or.inl ⟨hv, Or.inl (Or.inr hu)⟩)
    · have hu' : u = 4 := Fin.ext hu0
      have hv' : v = 11 := Fin.ext hv0
      subst hu' hv'
      exact Or.inl (Or.inr ⟨hv, Or.inl (Or.inr hu)⟩)
    · have hu' : u = 4 := Fin.ext hu0
      have hv' : v = 13 := Fin.ext hv0
      subst hu' hv'
      exact Or.inr ⟨hv, Or.inr hu⟩
    · have hu' : u = 5 := Fin.ext hu0
      have hv' : v = 10 := Fin.ext hv0
      subst hu' hv'
      exact Or.inl (Or.inl ⟨hv, Or.inr hu⟩)
    · have hu' : u = 6 := Fin.ext hu0
      have hv' : v = 11 := Fin.ext hv0
      subst hu' hv'
      exact Or.inl (Or.inr ⟨hv, Or.inr hu⟩)

lemma extra11_ao2_props (b : ℕ) (hb14 : 14 ≤ b) :
    (∀ g ∈ extra11 b, g.op = GateOp.and ∨ g.op = GateOp.or) ∧
    (∀ g ∈ extra11 b, g.inputs.length = 2) ∧
    (∀ g ∈ extra11 b, g.inputs.Nodup) ∧
    (∀ (t : ℕ) (ht : t < (extra11 b).length), ∀ i ∈ (extra11 b)[t].inputs, i < b + t) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [extra11, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | exact Or.inl rfl | exact Or.inr rfl
  · intro g hg
    simp only [extra11, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · intro g hg
    simp only [extra11, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact nodup_pair _ _ (by omega)
  · intro t ht i hi
    have hlt11 : t < 11 := ht
    rcases t with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | t'
    · simp only [extra11, List.getElem_cons_zero, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> omega
    · simp only [extra11, List.getElem_cons_succ, List.getElem_cons_zero,
        List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> omega
    · simp only [extra11, List.getElem_cons_succ, List.getElem_cons_zero,
        List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> omega
    · simp only [extra11, List.getElem_cons_succ, List.getElem_cons_zero,
        List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> omega
    · simp only [extra11, List.getElem_cons_succ, List.getElem_cons_zero,
        List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> omega
    · simp only [extra11, List.getElem_cons_succ, List.getElem_cons_zero,
        List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> omega
    · simp only [extra11, List.getElem_cons_succ, List.getElem_cons_zero,
        List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> omega
    · simp only [extra11, List.getElem_cons_succ, List.getElem_cons_zero,
        List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> omega
    · simp only [extra11, List.getElem_cons_succ, List.getElem_cons_zero,
        List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> omega
    · simp only [extra11, List.getElem_cons_succ, List.getElem_cons_zero,
        List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> omega
    · simp only [extra11, List.getElem_cons_succ, List.getElem_cons_zero,
        List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> omega
    · omega

lemma prefix_readsBack (x1 : Circuit) (hao : IsAO2 10 x1) (tail : List Gate) (out : ℕ)
    (htail : ∀ (t : ℕ) (ht : t < tail.length), ∀ i ∈ tail[t].inputs, i < (14 + x1.gates.length) + t) :
    ReadsBack 14 ⟨x1.gates.map remapGate ++ tail, out⟩ := by
  intro j hj i hi
  simp only [List.length_append, List.length_map] at hj
  have hjlen : j < (x1.gates.map remapGate ++ tail).length := by
    simp only [List.length_append, List.length_map]
    exact hj
  have hgate : gateAt ⟨x1.gates.map remapGate ++ tail, out⟩ j = (x1.gates.map remapGate ++ tail)[j] := by
    dsimp only [gateAt]
    exact getD_eq_getElem _ j _ hjlen
  rw [hgate] at hi
  by_cases hjm : j < x1.gates.length
  · have hm : j < (x1.gates.map remapGate).length := by simpa using hjm
    rw [List.getElem_append_left hm, List.getElem_map] at hi
    dsimp only [remapGate] at hi
    rw [List.mem_map] at hi
    rcases hi with ⟨u, hu, rfl⟩
    have hrb := hao.2.1 j hjm u
    have hg1 : gateAt x1 j = x1.gates[j] := by simp [gateAt, hjm]
    rw [hg1] at hrb
    exact remapWire_lt u j (hrb hu)
  · have hge : (x1.gates.map remapGate).length ≤ j := by
      simp only [List.length_map]
      omega
    rw [List.getElem_append_right hge] at hi
    simp only [List.length_map] at hge hi ⊢
    have htlt : j - x1.gates.length < tail.length := by omega
    have h := htail (j - x1.gates.length) htlt i hi
    omega

lemma remap_foldl_eval (x1 : Circuit) (hao : IsAO2 10 x1) (x5 : Fin 14 → Bool) :
    ((x1.gates.map remapGate).foldl wireStep (List.ofFn x5)).length = 14 + x1.gates.length ∧
    (∀ i : Fin 14,
      ((x1.gates.map remapGate).foldl wireStep (List.ofFn x5)).getD i.val false = x5 i) ∧
    (∀ u < 10 + x1.gates.length,
      ((x1.gates.map remapGate).foldl wireStep (List.ofFn x5)).getD (remapWire u) false =
        (x1.wires (List.ofFn fun x6 : Fin 10 => x5 (idxList.getD x6.val (0 : Fin 14)))).getD u false) := by
  have hrep := remap_wire_agree x1 hao x5 x1.gates.length le_rfl
  have ht0 : x1.gates.take x1.gates.length = x1.gates := List.take_length
  have ht1 : (x1.gates.map remapGate).take x1.gates.length = x1.gates.map remapGate := by
    rw [List.take_of_length_le]
    simp
  rw [ht0, ht1] at hrep
  refine ⟨hrep.2.1, ?_, hrep.2.2⟩
  intro i
  have hlt : i.val < (List.ofFn x5).length := by simp
  rw [foldl_wireStep_getD_lt _ _ i.val hlt, getD_eq_getElem _ _ false hlt, List.getElem_ofFn]

lemma solve : ∀ (x1 : Circuit), IsAO2 10 x1 → (∀ x3 ∈ x1.gates, x3.inputs.Nodup) →
    ∃ (x4 : Circuit), IsAO2 14 x4 ∧ (∀ x5 ∈ x4.gates, x5.inputs.Nodup) ∧
      2 ≤ x4.size ∧ x4.size ≤ x1.size + 12 ∧
      ∀ (x5 : Fin 14 → Bool), x4.eval (List.ofFn x5) =
        (x1.eval (List.ofFn fun x6 : Fin 10 => x5 (idxList.getD ↑x6 (0 : Fin 14))) ||
          Decidable.decide (∃ (x6 : Fin 14) (x7 : Fin 14),
            (↑x6, ↑x7) ∈ [((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (13 : ℕ)),
              ((3 : ℕ), (11 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)),
              ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((6 : ℕ), (11 : ℕ))] ∧
              x5 x6 = Bool.true ∧ x5 x7 = Bool.true)) := by
  intro x1 hao hnodup
  set b := 14 + x1.gates.length
  have hb14 : 14 ≤ b := by omega
  have hex := extra11_ao2_props b hb14
  by_cases hout : x1.output < 10 + x1.gates.length
  · let gLast : Gate := ⟨GateOp.or, [remapWire x1.output, b + 10]⟩
    set x4 : Circuit :=
      ⟨x1.gates.map remapGate ++ (extra11 b ++ [gLast]), b + 11⟩
    refine ⟨x4, ?_, ?_, ?_, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_⟩
      · intro g hg
        simp only [x4, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with ⟨g0, hg0, rfl⟩ | hg | rfl
        · exact hao.1 g0 hg0
        · exact hex.1 g hg
        · exact Or.inr rfl
      · dsimp only [x4]
        refine prefix_readsBack x1 hao (extra11 b ++ [gLast]) (b + 11) ?_
        intro t ht i hi
        simp only [List.length_append, List.length_cons, List.length_nil] at ht
        by_cases ht11 : t < (extra11 b).length
        · rw [List.getElem_append_left ht11] at hi
          exact hex.2.2.2 t ht11 i hi
        · have hlen11 : (extra11 b).length = 11 := rfl
          rw [List.getElem_append_right (by omega)] at hi
          have hsub : t - (extra11 b).length = 0 := by omega
          simp only [hsub, List.getElem_cons_zero, gLast, List.mem_cons, List.not_mem_nil, or_false] at hi
          have hrm : remapWire x1.output < b := remapWire_lt x1.output x1.gates.length hout
          rcases hi with rfl | rfl <;> omega
      · intro g hg
        simp only [x4, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with ⟨g0, hg0, rfl⟩ | hg | rfl
        · simp [remapGate, hao.2.2 g0 hg0]
        · exact hex.2.1 g hg
        · rfl
    · intro g hg
      simp only [x4, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with ⟨g0, hg0, rfl⟩ | hg | rfl
      · exact (hnodup g0 hg0).map remapWire_injective
      · exact hex.2.2.1 g hg
      · have hrm : remapWire x1.output < b := remapWire_lt x1.output x1.gates.length hout
        dsimp only [gLast]
        exact nodup_pair _ _ (by omega)
    · simp [x4, Circuit.size, extra11]
    · simp [x4, Circuit.size, extra11]
    · intro x5
      rcases remap_foldl_eval x1 hao x5 with ⟨hwMid_len, hwMid_in, hwMid_out⟩
      set wMid := (x1.gates.map remapGate).foldl wireStep (List.ofFn x5)
      rcases extra11_eval wMid b hb14 hwMid_len x5 hwMid_in with ⟨hwAfter_len, hwAfter_old, hwAfter_b10⟩
      set wAfter := (extra11 b).foldl wireStep wMid
      have heval : x4.eval (List.ofFn x5) = (wireStep wAfter gLast).getD (b + 11) false := by
        dsimp only [x4, Circuit.eval, Circuit.wires]
        change ((x1.gates.map remapGate ++ (extra11 b ++ [gLast])).foldl wireStep (List.ofFn x5)).getD
          (b + 11) false = _
        rw [List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hgLast : gLast = ⟨GateOp.or, [remapWire x1.output, b + 10]⟩ := rfl
      rw [heval, hgLast, ← hwAfter_len, wireStep_getD_self_or]
      have hrm : remapWire x1.output < b := remapWire_lt x1.output x1.gates.length hout
      rw [hwAfter_old (remapWire x1.output) hrm, hwAfter_b10, hwMid_out x1.output hout, extraBool_eq_decide]
      rfl
  · set x4 : Circuit := ⟨x1.gates.map remapGate ++ extra11 b, b + 10⟩
    refine ⟨x4, ?_, ?_, ?_, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_⟩
      · intro g hg
        simp only [x4, List.mem_append, List.mem_map] at hg
        rcases hg with ⟨g0, hg0, rfl⟩ | hg
        · exact hao.1 g0 hg0
        · exact hex.1 g hg
      · exact prefix_readsBack x1 hao (extra11 b) (b + 10) hex.2.2.2
      · intro g hg
        simp only [x4, List.mem_append, List.mem_map] at hg
        rcases hg with ⟨g0, hg0, rfl⟩ | hg
        · simp [remapGate, hao.2.2 g0 hg0]
        · exact hex.2.1 g hg
    · intro g hg
      simp only [x4, List.mem_append, List.mem_map] at hg
      rcases hg with ⟨g0, hg0, rfl⟩ | hg
      · exact (hnodup g0 hg0).map remapWire_injective
      · exact hex.2.2.1 g hg
    · simp [x4, Circuit.size, extra11]
    · simp [x4, Circuit.size, extra11]
    · intro x5
      rcases remap_foldl_eval x1 hao x5 with ⟨hwMid_len, hwMid_in, hwMid_out⟩
      set wMid := (x1.gates.map remapGate).foldl wireStep (List.ofFn x5)
      rcases extra11_eval wMid b hb14 hwMid_len x5 hwMid_in with ⟨hwAfter_len, hwAfter_old, hwAfter_b10⟩
      set wAfter := (extra11 b).foldl wireStep wMid
      have heval : x4.eval (List.ofFn x5) = wAfter.getD (b + 10) false := by
        dsimp only [x4, Circuit.eval, Circuit.wires]
        change ((x1.gates.map remapGate ++ extra11 b).foldl wireStep (List.ofFn x5)).getD (b + 10) false = _
        rw [List.foldl_append]
      rw [heval, hwAfter_b10, extraBool_eq_decide]
      have hx1len : (x1.wires (List.ofFn fun x6 : Fin 10 => x5 (idxList.getD ↑x6 (0 : Fin 14)))).length =
          10 + x1.gates.length := by
        change (x1.gates.foldl wireStep (List.ofFn fun x6 : Fin 10 => x5 (idxList.getD ↑x6 (0 : Fin 14)))).length = _
        rw [foldl_wireStep_length, List.length_ofFn]
      have hx1false : x1.eval (List.ofFn fun x6 : Fin 10 => x5 (idxList.getD ↑x6 (0 : Fin 14))) = false := by
        dsimp only [Circuit.eval]
        exact getD_of_length_le _ _ false (by omega)
      rw [hx1false, Bool.false_or]

end PEqualNP.Outside.L_meta_3517

theorem PEqualNP.Outside.L_meta_3517 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (10 : ℕ) x1 → (∀ x3 ∈ x1.gates, x3.inputs.Nodup) → ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (14 : ℕ) x4 ∧ (∀ x5 ∈ x4.gates, x5.inputs.Nodup) ∧ (2 : ℕ) ≤ x4.size ∧ x4.size ≤ x1.size + (12 : ℕ) ∧ ∀ (x5 : Fin (14 : ℕ) → Bool), x4.eval (List.ofFn x5) = (x1.eval (List.ofFn fun (x6 : Fin (10 : ℕ)) => x5 ([(0 : Fin (14 : ℕ)), (1 : Fin (14 : ℕ)), (2 : Fin (14 : ℕ)), (3 : Fin (14 : ℕ)), (5 : Fin (14 : ℕ)), (6 : Fin (14 : ℕ)), (7 : Fin (14 : ℕ)), (8 : Fin (14 : ℕ)), (9 : Fin (14 : ℕ)), (12 : Fin (14 : ℕ))].getD ↑x6 (0 : Fin (14 : ℕ)))) || Decidable.decide (∃ (x6 : Fin (14 : ℕ)) (x7 : Fin (14 : ℕ)), (↑x6, ↑x7) ∈ [((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((6 : ℕ), (11 : ℕ))] ∧ x5 x6 = Bool.true ∧ x5 x7 = Bool.true)) := PEqualNP.Outside.L_meta_3517.solve
