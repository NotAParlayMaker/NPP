import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3166

open PEqualNP.CircuitLowerBounds

def remap (idx v i : ℕ) : ℕ :=
  if i < 9 then i
  else if i = 9 then 0
  else if i < 10 + idx then i - 1
  else if i = 10 + idx then v
  else i - 2

def mapGate (idx v : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (remap idx v)⟩

def wireStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma filter_eq_singleton {α : Type*} (p : α → Bool) :
    ∀ {l : List α} {a : α}, l.filter p = [a] →
      ∃ pre post : List α, l = pre ++ a :: post ∧
        p a = true ∧ (∀ x ∈ pre, p x = false) ∧ (∀ x ∈ post, p x = false)
  | [], _, h => by simp at h
  | x :: xs, a, h => by
    simp only [List.filter_cons] at h
    cases hpx : p x with
    | true =>
      simp only [hpx, ite_true] at h
      injection h with hxa hrest
      subst hxa
      refine ⟨[], xs, rfl, hpx, by simp, ?_⟩
      intro y hy
      by_contra hpy
      have hpy' : p y = true := by cases h' : p y <;> simp_all
      have : y ∈ xs.filter p := List.mem_filter.mpr ⟨hy, hpy'⟩
      rw [hrest] at this
      simp at this
    | false =>
      simp only [hpx, Bool.false_eq_true, ite_false] at h
      obtain ⟨pre, post, heq, hpa, hpre, hpost⟩ := filter_eq_singleton p h
      refine ⟨x :: pre, post, by rw [heq]; rfl, hpa, ?_, hpost⟩
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy'
      · exact hpx
      · exact hpre y hy'

lemma foldl_wireStep_len (gs : List Gate) (w : List Bool) :
    (gs.foldl wireStep w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp only [wireStep, List.length_append, List.length_cons, List.length_nil]
    omega

lemma getD_append_left {w : List Bool} {b : Bool} {i : ℕ} (hi : i < w.length) :
    (w ++ [b]).getD i false = w.getD i false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_append_end (w : List Bool) (b : Bool) :
    (w ++ [b]).getD w.length false = b := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl w.length)]
  simp

lemma foldl_wireStep_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl wireStep w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons]
    have hlt : i < (wireStep w g).length := by
      simp only [wireStep, List.length_append, List.length_cons, List.length_nil]; omega
    rw [ih (wireStep w g) hlt]
    exact getD_append_left hi

lemma getD_ofFn_fin (x : Fin 9 → Bool) (j : Fin 9) :
    (List.ofFn x).getD j.val false = x j := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp), Option.getD_some,
    List.getElem_ofFn]

lemma step_pre (idx v : ℕ) (gs : List Gate) :
    ∀ (k : ℕ) (wOld wNew : List Bool),
      k + gs.length ≤ idx →
      wOld.length = 10 + k →
      wNew.length = 9 + k →
      (∀ i < 10 + k, i ≠ 9 → wNew.getD (remap idx v i) false = wOld.getD i false) →
      (∀ (j : ℕ) (hj : j < gs.length), ∀ i ∈ gs[j].inputs, i < 10 + k + j ∧ i ≠ 9) →
      ∀ i < 10 + (k + gs.length), i ≠ 9 →
        ((gs.map (mapGate idx v)).foldl wireStep wNew).getD (remap idx v i) false =
          (gs.foldl wireStep wOld).getD i false := by
  induction gs with
  | nil =>
    intro k wOld wNew _ _ _ hinv _ i hi hne
    simpa using hinv i (by simpa using hi) hne
  | cons g gs ih =>
    intro k wOld wNew hle hlo hln hinv hrb
    have hg_rb : ∀ i ∈ g.inputs, i < 10 + k ∧ i ≠ 9 := by
      intro i hi
      simpa using hrb 0 (by simp) i hi
    have hval : (mapGate idx v g).op.eval ((mapGate idx v g).inputs.map fun i => wNew.getD i false) =
        g.op.eval (g.inputs.map fun i => wOld.getD i false) := by
      simp only [mapGate, List.map_map, Function.comp_def]
      congr 1
      apply List.map_congr_left
      intro i hi
      obtain ⟨hlt, hne⟩ := hg_rb i hi
      exact hinv i hlt hne
    have hlo' : (wireStep wOld g).length = 10 + (k + 1) := by
      simp only [wireStep, List.length_append, List.length_cons, List.length_nil]; omega
    have hln' : (wireStep wNew (mapGate idx v g)).length = 9 + (k + 1) := by
      simp only [wireStep, List.length_append, List.length_cons, List.length_nil]; omega
    have hinv' : ∀ i < 10 + (k + 1), i ≠ 9 →
        (wireStep wNew (mapGate idx v g)).getD (remap idx v i) false =
          (wireStep wOld g).getD i false := by
      intro i hi hne
      by_cases hlt : i < 10 + k
      · have hne_rem : remap idx v i < wNew.length := by
          unfold remap
          split_ifs <;> omega
        rw [wireStep, getD_append_left hne_rem, wireStep, getD_append_left (by omega)]
        exact hinv i hlt hne
      · have heq : i = 10 + k := by omega
        subst heq
        have hrem : remap idx v (10 + k) = 9 + k := by
          unfold remap
          have hk : k < idx := by simp only [List.length_cons] at hle; omega
          simp [show ¬ 10 + k < 9 by omega, show ¬ 10 + k = 9 by omega,
            show 10 + k < 10 + idx by omega]
        rw [hrem, wireStep, ← hln, getD_append_end, wireStep, ← hlo, getD_append_end]
        exact hval
    have hrb' : ∀ (j : ℕ) (hj : j < gs.length), ∀ i ∈ gs[j].inputs, i < 10 + (k + 1) + j ∧ i ≠ 9 := by
      intro j hj i hi
      have h := hrb (j + 1) (by simp only [List.length_cons]; omega) i (by simpa using hi)
      exact ⟨by omega, h.2⟩
    intro i hi hne
    simp only [List.map_cons, List.foldl_cons]
    have hle' : k + 1 + gs.length ≤ idx := by simp only [List.length_cons] at hle; omega
    have hi' : i < 10 + (k + 1 + gs.length) := by simp only [List.length_cons] at hi; omega
    exact ih (k + 1) (wireStep wOld g) (wireStep wNew (mapGate idx v g)) hle' hlo' hln' hinv' hrb' i hi' hne

lemma step_post (idx v : ℕ) (hv : v < 9) (gs : List Gate) :
    ∀ (k : ℕ) (wOld wNew : List Bool),
      wOld.length = 10 + idx + 1 + k →
      wNew.length = 9 + idx + k →
      (∀ i < 10 + idx + 1 + k, i ≠ 9 → wNew.getD (remap idx v i) false = wOld.getD i false) →
      (∀ (j : ℕ) (hj : j < gs.length), ∀ i ∈ gs[j].inputs, i < 10 + idx + 1 + k + j ∧ i ≠ 9) →
      ∀ i < 10 + idx + 1 + (k + gs.length), i ≠ 9 →
        ((gs.map (mapGate idx v)).foldl wireStep wNew).getD (remap idx v i) false =
          (gs.foldl wireStep wOld).getD i false := by
  induction gs with
  | nil =>
    intro k wOld wNew _ _ hinv _ i hi hne
    simpa using hinv i (by simpa using hi) hne
  | cons g gs ih =>
    intro k wOld wNew hlo hln hinv hrb
    have hg_rb : ∀ i ∈ g.inputs, i < 10 + idx + 1 + k ∧ i ≠ 9 := by
      intro i hi
      simpa using hrb 0 (by simp) i hi
    have hval : (mapGate idx v g).op.eval ((mapGate idx v g).inputs.map fun i => wNew.getD i false) =
        g.op.eval (g.inputs.map fun i => wOld.getD i false) := by
      simp only [mapGate, List.map_map, Function.comp_def]
      congr 1
      apply List.map_congr_left
      intro i hi
      obtain ⟨hlt, hne⟩ := hg_rb i hi
      exact hinv i hlt hne
    have hlo' : (wireStep wOld g).length = 10 + idx + 1 + (k + 1) := by
      simp only [wireStep, List.length_append, List.length_cons, List.length_nil]; omega
    have hln' : (wireStep wNew (mapGate idx v g)).length = 9 + idx + (k + 1) := by
      simp only [wireStep, List.length_append, List.length_cons, List.length_nil]; omega
    have hinv' : ∀ i < 10 + idx + 1 + (k + 1), i ≠ 9 →
        (wireStep wNew (mapGate idx v g)).getD (remap idx v i) false =
          (wireStep wOld g).getD i false := by
      intro i hi hne
      by_cases hlt : i < 10 + idx + 1 + k
      · have hne_rem : remap idx v i < wNew.length := by
          unfold remap
          split_ifs <;> omega
        rw [wireStep, getD_append_left hne_rem, wireStep, getD_append_left (by omega)]
        exact hinv i hlt hne
      · have heq : i = 10 + idx + 1 + k := by omega
        subst heq
        have hrem : remap idx v (10 + idx + 1 + k) = 9 + idx + k := by
          unfold remap
          simp only [show ¬ 10 + idx + 1 + k < 9 by omega,
            show ¬ 10 + idx + 1 + k = 9 by omega,
            show ¬ 10 + idx + 1 + k < 10 + idx by omega,
            show ¬ 10 + idx + 1 + k = 10 + idx by omega, ite_false]
          omega
        rw [hrem, wireStep, ← hln, getD_append_end, wireStep, ← hlo, getD_append_end]
        exact hval
    have hrb' : ∀ (j : ℕ) (hj : j < gs.length), ∀ i ∈ gs[j].inputs, i < 10 + idx + 1 + (k + 1) + j ∧ i ≠ 9 := by
      intro j hj i hi
      have h := hrb (j + 1) (by simp only [List.length_cons]; omega) i (by simpa using hi)
      exact ⟨by omega, h.2⟩
    intro i hi hne
    simp only [List.map_cons, List.foldl_cons]
    have hi' : i < 10 + idx + 1 + (k + 1 + gs.length) := by simp only [List.length_cons] at hi; omega
    exact ih (k + 1) (wireStep wOld g) (wireStep wNew (mapGate idx v g)) hlo' hln' hinv' hrb' i hi' hne

lemma main_proof :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate),
      x2 = 0 ∨ x2 = 2 →
      PEqualNP.MetaComplexity.FanInTwo x1 →
      PEqualNP.MetaComplexity.NestedCover.ReadsBack 10 x1 →
      x1.output ≠ 9 →
      List.filter (fun x8 => decide (9 ∈ x8.inputs)) x1.gates = [x3] →
      x3.op = GateOp.or →
      x3.inputs = [9, x2] ∨ x3.inputs = [x2, 9] →
      ∃ x11 : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.FanInTwo x11 ∧
        x11.size + 1 = x1.size ∧
        ∀ x12 : Fin 9 → Bool, x11.eval (List.ofFn x12) = x1.eval (List.ofFn x12 ++ [x12 0 && x12 2]) := by
  intro C v g hv hfan hrb hout hfilt hop hinp
  obtain ⟨pre, post, hsplit, _, hpre_no9, hpost_no9⟩ :=
    filter_eq_singleton (fun h : Gate => decide (9 ∈ h.inputs)) hfilt
  let idx := pre.length
  let C' : Circuit := ⟨(pre ++ post).map (mapGate idx v), remap idx v C.output⟩
  refine ⟨C', ?_, ?_, ?_⟩
  · intro h hh
    obtain ⟨h0, hh0, rfl⟩ := List.mem_map.mp hh
    have hmem : h0 ∈ C.gates := by
      rw [hsplit]
      rcases List.mem_append.mp hh0 with h1 | h2
      · exact List.mem_append_left _ h1
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ h2)
    obtain ⟨hop0, hlen0⟩ := hfan h0 hmem
    exact ⟨hop0, by simp [mapGate, hlen0]⟩
  · change ((pre ++ post).map (mapGate idx v)).length + 1 = C.gates.length
    rw [hsplit]
    simp only [List.length_map, List.length_append, List.length_cons]
    omega
  · intro x
    let w0New : List Bool := List.ofFn x
    let w0Old : List Bool := List.ofFn x ++ [x 0 && x 2]
    have hw0New_len : w0New.length = 9 := by simp [w0New]
    have hw0Old_len : w0Old.length = 10 := by simp [w0Old]
    have hinv0 : ∀ i < 10 + 0, i ≠ 9 → w0New.getD (remap idx v i) false = w0Old.getD i false := by
      intro i hi hne
      have hi9 : i < 9 := by omega
      have hrem : remap idx v i = i := by simp [remap, hi9]
      rw [hrem]
      exact (getD_append_left (by omega : i < w0New.length)).symm
    have hrb_pre : ∀ (j : ℕ) (hj : j < pre.length), ∀ i ∈ pre[j].inputs, i < 10 + 0 + j ∧ i ≠ 9 := by
      intro j hj i hi
      have hltC : j < C.gates.length := by rw [hsplit]; simp; omega
      have hget : PEqualNP.MetaComplexity.NestedCover.gateAt C j = pre[j] := by
        simp only [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD, hsplit,
          List.getElem?_append_left hj, List.getElem?_eq_getElem hj, Option.getD_some]
      have h1 : i < 10 + j := by
        have := hrb j hltC i
        rw [hget] at this
        exact this hi
      have h2 : i ≠ 9 := by
        intro heq
        subst heq
        have hf := hpre_no9 pre[j] (List.getElem_mem hj)
        simp [hi] at hf
      exact ⟨by omega, h2⟩
    let wPreOld := pre.foldl wireStep w0Old
    let wPreNew := (pre.map (mapGate idx v)).foldl wireStep w0New
    have hinvPre : ∀ i < 10 + idx, i ≠ 9 → wPreNew.getD (remap idx v i) false = wPreOld.getD i false := by
      intro i hi hne
      exact step_pre idx v pre 0 w0Old w0New (by omega) (by omega) (by omega) hinv0 hrb_pre i (by omega) hne
    have hwPreOld_len : wPreOld.length = 10 + idx := by
      rw [foldl_wireStep_len, hw0Old_len]
    have hwPreNew_len : wPreNew.length = 9 + idx := by
      rw [foldl_wireStep_len, List.length_map, hw0New_len]
    have hv_lt : v < 9 := by rcases hv with rfl | rfl <;> omega
    have hget_lt9 : ∀ j : Fin 9, wPreOld.getD j.val false = x j := by
      intro j
      rw [foldl_wireStep_getD_lt pre w0Old j.val (by omega)]
      rw [getD_append_left (by omega : j.val < w0New.length)]
      exact getD_ofFn_fin x j
    have hget_9 : wPreOld.getD 9 false = (x 0 && x 2) := by
      rw [foldl_wireStep_getD_lt pre w0Old 9 (by omega)]
      have := getD_append_end w0New (x 0 && x 2)
      rw [hw0New_len] at this
      exact this
    have hg_val : g.op.eval (g.inputs.map fun i => wPreOld.getD i false) = x ⟨v, hv_lt⟩ := by
      rw [hop]
      have hgv := hget_lt9 ⟨v, hv_lt⟩
      rcases hinp with h | h <;> rw [h] <;>
        simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil,
          Bool.or_false, id_eq, hget_9, hgv] <;>
        rcases hv with rfl | rfl
      · change ((x 0 && x 2) || x 0) = x 0; cases x 0 <;> cases x 2 <;> rfl
      · change ((x 0 && x 2) || x 2) = x 2; cases x 0 <;> cases x 2 <;> rfl
      · change (x 0 || (x 0 && x 2)) = x 0; cases x 0 <;> cases x 2 <;> rfl
      · change (x 2 || (x 0 && x 2)) = x 2; cases x 0 <;> cases x 2 <;> rfl
    let wMidOld := wireStep wPreOld g
    have hwMidOld_len : wMidOld.length = 10 + idx + 1 := by
      simp only [wMidOld, wireStep, List.length_append, List.length_cons, List.length_nil, hwPreOld_len]
    have hinvMid : ∀ i < 10 + idx + 1 + 0, i ≠ 9 →
        wPreNew.getD (remap idx v i) false = wMidOld.getD i false := by
      intro i hi hne
      by_cases hlt : i < 10 + idx
      · dsimp only [wMidOld, wireStep]
        rw [getD_append_left (by omega)]
        exact hinvPre i hlt hne
      · have heq : i = 10 + idx := by omega
        subst heq
        have hrem : remap idx v (10 + idx) = v := by
          unfold remap
          simp only [show ¬ 10 + idx < 9 by omega, show ¬ 10 + idx = 9 by omega,
            show ¬ 10 + idx < 10 + idx by omega, ite_false, ite_true]
        rw [hrem]
        dsimp only [wMidOld, wireStep]
        rw [← hwPreOld_len, getD_append_end, hg_val]
        rw [foldl_wireStep_getD_lt _ w0New v (by omega)]
        exact getD_ofFn_fin x ⟨v, hv_lt⟩
    have hrb_post : ∀ (j : ℕ) (hj : j < post.length), ∀ i ∈ post[j].inputs, i < 10 + idx + 1 + 0 + j ∧ i ≠ 9 := by
      intro j hj i hi
      have hltC : idx + 1 + j < C.gates.length := by rw [hsplit]; simp [idx]; omega
      have hget : PEqualNP.MetaComplexity.NestedCover.gateAt C (idx + 1 + j) = post[j] := by
        simp only [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD, hsplit]
        rw [List.getElem?_append_right (by omega : pre.length ≤ idx + 1 + j)]
        have hsub : idx + 1 + j - pre.length = j + 1 := by omega
        rw [hsub]
        simp [hj]
      have h1 : i < 10 + (idx + 1 + j) := by
        have := hrb (idx + 1 + j) hltC i
        rw [hget] at this
        exact this hi
      have h2 : i ≠ 9 := by
        intro heq
        subst heq
        have hf := hpost_no9 post[j] (List.getElem_mem hj)
        simp [hi] at hf
      exact ⟨by omega, h2⟩
    have hinvEnd := step_post idx v hv_lt post 0 wMidOld wPreNew
      (by omega) (by omega) hinvMid hrb_post
    change (C'.wires w0New).getD (remap idx v C.output) false = (C.wires w0Old).getD C.output false
    have hwNew_eq : C'.wires w0New = (post.map (mapGate idx v)).foldl wireStep wPreNew := by
      change ((pre ++ post).map (mapGate idx v)).foldl wireStep w0New = _
      rw [List.map_append, List.foldl_append]
    have hwOld_eq : C.wires w0Old = post.foldl wireStep wMidOld := by
      change C.gates.foldl wireStep w0Old = _
      rw [hsplit, List.foldl_append, List.foldl_cons]
    rw [hwNew_eq, hwOld_eq]
    by_cases hlt : C.output < 10 + idx + 1 + (0 + post.length)
    · exact hinvEnd C.output hlt hout
    · have hlenOld : (post.foldl wireStep wMidOld).length = 10 + idx + 1 + post.length := by
        rw [foldl_wireStep_len, hwMidOld_len]
      have hlenNew : ((post.map (mapGate idx v)).foldl wireStep wPreNew).length = 9 + idx + post.length := by
        rw [foldl_wireStep_len, List.length_map, hwPreNew_len]
      have hrem_ge : 9 + idx + post.length ≤ remap idx v C.output := by
        unfold remap
        have hgt : ¬ C.output < 9 := by omega
        have hne9 : ¬ C.output = 9 := by omega
        have hgt1 : ¬ C.output < 10 + idx := by omega
        have hne1 : ¬ C.output = 10 + idx := by omega
        simp only [hgt, hne9, hgt1, hne1, ite_false]
        omega
      rw [List.getD_eq_default _ false (by omega), List.getD_eq_default _ false (by omega)]

end PEqualNP.Outside.L_meta_3166

theorem PEqualNP.Outside.L_meta_3166 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x2 = (0 : ℕ) ∨ x2 = (2 : ℕ) → PEqualNP.MetaComplexity.FanInTwo x1 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (10 : ℕ) x1 → x1.output ≠ (9 : ℕ) → List.filter (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => Decidable.decide ((9 : ℕ) ∈ x8.inputs)) x1.gates = [x3] → x3.op = PEqualNP.CircuitLowerBounds.GateOp.or → x3.inputs = [(9 : ℕ), x2] ∨ x3.inputs = [x2, (9 : ℕ)] → ∃ (x11 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x11 ∧ x11.size + (1 : ℕ) = x1.size ∧ ∀ (x12 : Fin (9 : ℕ) → Bool), x11.eval (List.ofFn x12) = x1.eval (List.ofFn x12 ++ [x12 (0 : Fin (9 : ℕ)) && x12 (2 : Fin (9 : ℕ))]) :=
  PEqualNP.Outside.L_meta_3166.main_proof
