import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.LMeta571

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def wiresStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private lemma foldl_wiresStep_length (gs : List Gate) (w : List Bool) :
    (gs.foldl wiresStep w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, wiresStep, List.length_append, List.length_cons, List.length_nil]
    omega

private lemma wires_length (C : Circuit) (xs : List Bool) :
    (C.wires xs).length = xs.length + C.gates.length :=
  foldl_wiresStep_length C.gates xs

private lemma foldl_wiresStep_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length) :
    (gs.foldl wiresStep w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (wiresStep w g).length := by
      simp only [wiresStep, List.length_append, List.length_singleton]
      omega
    rw [ih (wiresStep w g) hlt]
    simp only [wiresStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private lemma getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

private lemma getD_append_last (w : List Bool) (b : Bool) :
    (w ++ [b]).getD w.length false = b := by
  simp [List.getD_eq_getElem?_getD]

private lemma getD_ofFn {m : ℕ} (x : Fin m → Bool) (i : ℕ) (hi : i < m) :
    (List.ofFn x).getD i false = x ⟨i, hi⟩ := by
  simp [List.getD_eq_getElem?_getD, hi]

private def remapIdx (m M lim dead : ℕ) (f : ℕ → ℕ) (i : ℕ) : ℕ :=
  if i < m then f i else if i < m + lim then M + (i - m) else dead

private def embedGates (m M dead : ℕ) (f : ℕ → ℕ) (gs : List Gate) : List Gate :=
  gs.zipIdx.map fun p => ⟨p.1.op, p.1.inputs.map (remapIdx m M p.2 dead f)⟩

private lemma embedGates_length (m M dead : ℕ) (f : ℕ → ℕ) (gs : List Gate) :
    (embedGates m M dead f gs).length = gs.length := by
  simp [embedGates]

private lemma embedGates_fanInTwo (m M dead : ℕ) (f : ℕ → ℕ) (C : Circuit) (out : ℕ)
    (hF : FanInTwo C) :
    FanInTwo ⟨embedGates m M dead f C.gates, out⟩ := by
  intro g hg
  simp only [embedGates, List.mem_map] at hg
  obtain ⟨⟨g0, j⟩, hmem, rfl⟩ := hg
  have hg0 : g0 ∈ C.gates := by
    rw [List.mem_iff_getElem] at hmem
    obtain ⟨k, hk, hkg⟩ := hmem
    have hk' : k < C.gates.length := by simpa using hk
    have hg0eq : g0 = C.gates[k] := by
      have := congrArg Prod.fst hkg
      simpa using this.symm
    rw [hg0eq]
    exact List.getElem_mem hk'
  obtain ⟨hop, hlen⟩ := hF g0 hg0
  exact ⟨hop, by simp [hlen]⟩

private lemma embedGates_append (m M dead : ℕ) (f : ℕ → ℕ) (gs : List Gate) (g : Gate) :
    embedGates m M dead f (gs ++ [g]) =
      embedGates m M dead f gs ++ [⟨g.op, g.inputs.map (remapIdx m M gs.length dead f)⟩] := by
  unfold embedGates
  rw [List.zipIdx_append, List.map_append]
  simp

private lemma embedGates_wires (m M dead : ℕ) (f : ℕ → ℕ) (gs : List Gate)
    (xs ys : List Bool) (hxs : xs.length = m) (hys : ys.length = M)
    (hf : ∀ i < m, f i < M ∧ ys.getD (f i) false = xs.getD i false)
    (hdead : M + gs.length ≤ dead) :
    ∀ j < gs.length,
      ((embedGates m M dead f gs).foldl wiresStep ys).getD (M + j) false =
        (gs.foldl wiresStep xs).getD (m + j) false := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro j hj
    exact absurd hj (Nat.not_lt_zero _)
  | append_singleton gs g ih =>
    have hdead' : M + gs.length ≤ dead := by simp only [List.length_append, List.length_singleton] at hdead; omega
    have ih' := ih hdead'
    rw [embedGates_append, List.foldl_append, List.foldl_append,
      List.foldl_cons, List.foldl_nil, List.foldl_cons, List.foldl_nil]
    set w1 := gs.foldl wiresStep xs
    set w2 := (embedGates m M dead f gs).foldl wiresStep ys
    have hw1 : w1.length = m + gs.length := by
      rw [foldl_wiresStep_length, hxs]
    have hw2 : w2.length = M + gs.length := by
      rw [foldl_wiresStep_length, hys, embedGates_length]
    have hmap : ∀ i : ℕ,
        w2.getD (remapIdx m M gs.length dead f i) false = w1.getD i false := by
      intro i
      unfold remapIdx
      by_cases hi1 : i < m
      · rw [if_pos hi1]
        have hfi := hf i hi1
        have h1 : w1.getD i false = xs.getD i false :=
          foldl_wiresStep_getD_lt gs xs i (by omega)
        have h2 : w2.getD (f i) false = ys.getD (f i) false :=
          foldl_wiresStep_getD_lt (embedGates m M dead f gs) ys (f i) (by omega)
        rw [h1, h2, hfi.2]
      · rw [if_neg hi1]
        by_cases hi2 : i < m + gs.length
        · rw [if_pos hi2]
          have hsub : m + (i - m) = i := by omega
          have := ih' (i - m) (by omega)
          rwa [hsub] at this
        · rw [if_neg hi2]
          rw [getD_ge_length w2 dead (by omega), getD_ge_length w1 i (by omega)]
    have hval : g.op.eval ((g.inputs.map (remapIdx m M gs.length dead f)).map fun i => w2.getD i false) =
        g.op.eval (g.inputs.map fun i => w1.getD i false) := by
      congr 1
      rw [List.map_map]
      refine List.map_congr_left fun i _ => ?_
      exact hmap i
    intro j hj
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hlt : j < gs.length
    · have h1 : (wiresStep w1 g).getD (m + j) false = w1.getD (m + j) false := by
        simp only [wiresStep, List.getD_eq_getElem?_getD,
          List.getElem?_append_left (by omega : m + j < w1.length)]
      have h2 : (wiresStep w2 ⟨g.op, g.inputs.map (remapIdx m M gs.length dead f)⟩).getD (M + j) false =
          w2.getD (M + j) false := by
        simp only [wiresStep, List.getD_eq_getElem?_getD,
          List.getElem?_append_left (by omega : M + j < w2.length)]
      rw [h1, h2]
      exact ih' j hlt
    · have heq : j = gs.length := by omega
      subst heq
      have h1 : (wiresStep w1 g).getD (m + gs.length) false =
          g.op.eval (g.inputs.map fun i => w1.getD i false) := by
        rw [← hw1]
        exact getD_append_last w1 _
      have h2 : (wiresStep w2 ⟨g.op, g.inputs.map (remapIdx m M gs.length dead f)⟩).getD (M + gs.length) false =
          g.op.eval ((g.inputs.map (remapIdx m M gs.length dead f)).map fun i => w2.getD i false) := by
        rw [← hw2]
        exact getD_append_last w2 _
      rw [h1, h2, hval]

private def embedCircuit (m M dead : ℕ) (f : ℕ → ℕ) (C : Circuit) : Circuit :=
  ⟨embedGates m M dead f C.gates, remapIdx m M C.gates.length dead f C.output⟩

private lemma embedCircuit_eval (m M dead : ℕ) (f : ℕ → ℕ) (C : Circuit)
    (xs ys : List Bool) (hxs : xs.length = m) (hys : ys.length = M)
    (hf : ∀ i < m, f i < M ∧ ys.getD (f i) false = xs.getD i false)
    (hdead : M + C.gates.length ≤ dead) :
    (embedCircuit m M dead f C).eval ys = C.eval xs := by
  unfold Circuit.eval Circuit.wires embedCircuit
  change ((embedGates m M dead f C.gates).foldl wiresStep ys).getD
      (remapIdx m M C.gates.length dead f C.output) false =
    (C.gates.foldl wiresStep xs).getD C.output false
  unfold remapIdx
  by_cases h1 : C.output < m
  · rw [if_pos h1]
    have hfi := hf C.output h1
    rw [foldl_wiresStep_getD_lt _ ys (f C.output) (by omega),
      foldl_wiresStep_getD_lt _ xs C.output (by omega), hfi.2]
  · rw [if_neg h1]
    by_cases h2 : C.output < m + C.gates.length
    · rw [if_pos h2]
      have hw := embedGates_wires m M dead f C.gates xs ys hxs hys hf hdead (C.output - m) (by omega)
      have hsub : m + (C.output - m) = C.output := by omega
      rwa [hsub] at hw
    · rw [if_neg h2]
      rw [getD_ge_length _ dead (by rw [foldl_wiresStep_length, hys, embedGates_length]; omega),
        getD_ge_length _ C.output (by rw [foldl_wiresStep_length, hxs]; omega)]

private def addStar (M a b c : ℕ) (C : Circuit) : Circuit :=
  let cur := M + C.gates.length
  ⟨C.gates ++ [⟨GateOp.or, [b, c]⟩, ⟨GateOp.and, [a, cur]⟩, ⟨GateOp.or, [C.output, cur + 1]⟩],
    cur + 2⟩

private lemma addStar_fanInTwo (M a b c : ℕ) (C : Circuit) (hF : FanInTwo C) :
    FanInTwo (addStar M a b c C) := by
  intro g hg
  simp only [addStar, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | rfl | rfl | rfl
  · exact hF g h
  · exact ⟨by simp, by simp⟩
  · exact ⟨by simp, by simp⟩
  · exact ⟨by simp, by simp⟩

private lemma addStar_eval (M a b c : ℕ) (C : Circuit) (ys : List Bool)
    (hys : ys.length = M) (ha : a < M) (hb : b < M) (hc : c < M)
    (hout : C.output < M + C.gates.length ∨ M + C.gates.length + 3 ≤ C.output) :
    (addStar M a b c C).eval ys =
      (C.eval ys || (ys.getD a false && (ys.getD b false || ys.getD c false))) := by
  unfold Circuit.eval Circuit.wires addStar
  change ((C.gates ++ [Gate.mk GateOp.or [b, c], Gate.mk GateOp.and [a, M + C.gates.length],
    Gate.mk GateOp.or [C.output, M + C.gates.length + 1]]).foldl wiresStep ys).getD
      (M + C.gates.length + 2) false =
    ((C.gates.foldl wiresStep ys).getD C.output false ||
      (ys.getD a false && (ys.getD b false || ys.getD c false)))
  rw [List.foldl_append]
  set w0 := C.gates.foldl wiresStep ys
  have hw0 : w0.length = M + C.gates.length := by
    rw [foldl_wiresStep_length, hys]
  have hb0 : w0.getD b false = ys.getD b false :=
    foldl_wiresStep_getD_lt C.gates ys b (by omega)
  have hc0 : w0.getD c false = ys.getD c false :=
    foldl_wiresStep_getD_lt C.gates ys c (by omega)
  have ha0 : w0.getD a false = ys.getD a false :=
    foldl_wiresStep_getD_lt C.gates ys a (by omega)
  simp only [List.foldl_cons, List.foldl_nil]
  set v1 : Bool := ys.getD b false || ys.getD c false
  have hs1 : wiresStep w0 ⟨GateOp.or, [b, c]⟩ = w0 ++ [v1] := by
    rw [wiresStep]
    simp only [List.map_cons, List.map_nil, hb0, hc0]
    simp [GateOp.eval, v1]
  rw [hs1]
  set w1 := w0 ++ [v1]
  have hw1 : w1.length = M + C.gates.length + 1 := by simp [w1, hw0]
  have ha1 : w1.getD a false = ys.getD a false := by
    simp only [w1, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : a < w0.length)]
    exact ha0
  have hv1 : w1.getD (M + C.gates.length) false = v1 := by
    rw [← hw0]
    exact getD_append_last w0 v1
  set v2 : Bool := ys.getD a false && v1
  have hs2 : wiresStep w1 ⟨GateOp.and, [a, M + C.gates.length]⟩ = w1 ++ [v2] := by
    rw [wiresStep]
    simp only [List.map_cons, List.map_nil, ha1, hv1]
    simp [GateOp.eval, v2]
  rw [hs2]
  set w2 := w1 ++ [v2]
  have hw2 : w2.length = M + C.gates.length + 2 := by simp [w2, hw1]
  have hout2 : w2.getD C.output false = w0.getD C.output false := by
    rcases hout with hlt | hge
    · have h1 : w2.getD C.output false = w1.getD C.output false := by
        simp only [w2, List.getD_eq_getElem?_getD,
          List.getElem?_append_left (by omega : C.output < w1.length)]
      have h2 : w1.getD C.output false = w0.getD C.output false := by
        simp only [w1, List.getD_eq_getElem?_getD,
          List.getElem?_append_left (by omega : C.output < w0.length)]
      rw [h1, h2]
    · rw [getD_ge_length w2 C.output (by omega), getD_ge_length w0 C.output (by omega)]
  have hv2 : w2.getD (M + C.gates.length + 1) false = v2 := by
    rw [← hw1]
    exact getD_append_last w1 v2
  have hs3 : wiresStep w2 ⟨GateOp.or, [C.output, M + C.gates.length + 1]⟩ =
      w2 ++ [w0.getD C.output false || v2] := by
    rw [wiresStep]
    simp only [List.map_cons, List.map_nil, hout2, hv2]
    simp [GateOp.eval]
  rw [hs3, ← hw2]
  exact getD_append_last w2 _

private def addStars (M : ℕ) : List (ℕ × ℕ × ℕ) → Circuit → Circuit
  | [], C => C
  | (a, b, c) :: rest, C => addStars M rest (addStar M a b c C)

private lemma addStars_size (M : ℕ) (stars : List (ℕ × ℕ × ℕ)) (C : Circuit) :
    (addStars M stars C).size = C.size + 3 * stars.length := by
  induction stars generalizing C with
  | nil => simp [addStars]
  | cons t rest ih =>
    rcases t with ⟨a, b, c⟩
    rw [addStars, ih]
    simp only [Circuit.size, addStar, List.length_append, List.length_cons, List.length_nil]
    omega

private lemma addStars_fanInTwo (M : ℕ) (stars : List (ℕ × ℕ × ℕ)) (C : Circuit)
    (hF : FanInTwo C) : FanInTwo (addStars M stars C) := by
  induction stars generalizing C with
  | nil => exact hF
  | cons t rest ih =>
    rcases t with ⟨a, b, c⟩
    exact ih _ (addStar_fanInTwo M a b c C hF)

private lemma addStars_eval (M : ℕ) (stars : List (ℕ × ℕ × ℕ)) (C : Circuit) (ys : List Bool)
    (hys : ys.length = M)
    (hstars : ∀ t ∈ stars, t.1 < M ∧ t.2.1 < M ∧ t.2.2 < M)
    (hout : C.output < M + C.gates.length ∨ M + C.gates.length + 3 * stars.length ≤ C.output) :
    (addStars M stars C).eval ys =
      (C.eval ys || stars.any (fun t =>
        ys.getD t.1 false && (ys.getD t.2.1 false || ys.getD t.2.2 false))) := by
  induction stars generalizing C with
  | nil => simp [addStars]
  | cons t rest ih =>
    rcases t with ⟨a, b, c⟩
    have ht := hstars (a, b, c) (by simp)
    have hrest : ∀ s ∈ rest, s.1 < M ∧ s.2.1 < M ∧ s.2.2 < M :=
      fun s hs => hstars s (by simp [hs])
    have hout1 : C.output < M + C.gates.length ∨ M + C.gates.length + 3 ≤ C.output := by
      simp only [List.length_cons] at hout
      omega
    have hout2 : (addStar M a b c C).output < M + (addStar M a b c C).gates.length ∨
        M + (addStar M a b c C).gates.length + 3 * rest.length ≤ (addStar M a b c C).output := by
      left
      simp only [addStar, List.length_append, List.length_cons, List.length_nil]
      omega
    simp only [addStars]
    rw [ih (addStar M a b c C) hrest hout2, addStar_eval M a b c C ys hys ht.1 ht.2.1 ht.2.2 hout1]
    simp [Bool.or_assoc]

private lemma path_equiv_left {N h : ℕ} (hh : 3 ≤ h) (u v : Fin N) (x : Fin (N + 2 * h) → Bool) :
    ((x (Fin.castAdd (2 * h) u) && x (Fin.natAdd N ⟨0, by omega⟩)) ||
      ((List.range h).map fun k =>
        (N + 2 * k + 1, N + 2 * k, if k + 1 < h then N + 2 * k + 2 else v.val)).any
        (fun t => (List.ofFn x).getD t.1 false &&
          ((List.ofFn x).getD t.2.1 false || (List.ofFn x).getD t.2.2 false))) =
    decide (∃ i : Fin (2 * h), x (Fin.natAdd N i) = true ∧
      ((i.val = 0 ∧ x (Fin.castAdd (2 * h) u) = true) ∨
       (i.val + 1 = 2 * h ∧ x (Fin.castAdd (2 * h) v) = true) ∨
       ∃ j : Fin (2 * h), j.val = i.val + 1 ∧ x (Fin.natAdd N j) = true)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.or_eq_true, Bool.and_eq_true, List.any_eq_true, List.mem_map, List.mem_range,
    decide_eq_true_eq]
  constructor
  · rintro (⟨hu, hz0⟩ | ⟨_, ⟨k, hk, rfl⟩, ha, hb | hc⟩)
    · exact ⟨⟨0, by omega⟩, hz0, Or.inl ⟨rfl, hu⟩⟩
    · rw [getD_ofFn x (N + 2 * k + 1) (by omega)] at ha
      rw [getD_ofFn x (N + 2 * k) (by omega)] at hb
      refine ⟨⟨2 * k, by omega⟩, ?_, Or.inr (Or.inr ⟨⟨2 * k + 1, by omega⟩, rfl, ?_⟩)⟩
      · convert hb using 2
        ext
        simp only [Fin.val_natAdd]
      · convert ha using 2
        ext
        simp only [Fin.val_natAdd]
        omega
    · rw [getD_ofFn x (N + 2 * k + 1) (by omega)] at ha
      by_cases hkn : k + 1 < h
      · rw [if_pos hkn, getD_ofFn x (N + 2 * k + 2) (by omega)] at hc
        refine ⟨⟨2 * k + 1, by omega⟩, ?_, Or.inr (Or.inr ⟨⟨2 * k + 2, by omega⟩, rfl, ?_⟩)⟩
        · convert ha using 2
          ext
          simp only [Fin.val_natAdd]
          omega
        · convert hc using 2
          ext
          simp only [Fin.val_natAdd]
          omega
      · rw [if_neg hkn, getD_ofFn x v.val (by omega)] at hc
        refine ⟨⟨2 * k + 1, by omega⟩, ?_, Or.inr (Or.inl ⟨by simp; omega, ?_⟩)⟩
        · convert ha using 2
          ext
          simp only [Fin.val_natAdd]
          omega
        · convert hc using 2
          ext
          simp only [Fin.val_castAdd]
  · rintro ⟨i, hi, ⟨hi0, hu⟩ | ⟨hilast, hv⟩ | ⟨j, hj, hxj⟩⟩
    · left
      refine ⟨hu, ?_⟩
      convert hi using 2
      ext
      simp only [Fin.val_natAdd]
      omega
    · right
      refine ⟨_, ⟨h - 1, by omega, rfl⟩, ?_, Or.inr ?_⟩
      · rw [getD_ofFn x (N + 2 * (h - 1) + 1) (by omega)]
        convert hi using 2
        ext
        simp only [Fin.val_natAdd]
        omega
      · rw [if_neg (by omega), getD_ofFn x v.val (by omega)]
        convert hv using 2
        ext
        simp only [Fin.val_castAdd]
    · right
      by_cases heven : i.val % 2 = 0
      · refine ⟨_, ⟨i.val / 2, by omega, rfl⟩, ?_, Or.inl ?_⟩
        · rw [getD_ofFn x (N + 2 * (i.val / 2) + 1) (by omega)]
          convert hxj using 2
          ext
          simp only [Fin.val_natAdd]
          omega
        · rw [getD_ofFn x (N + 2 * (i.val / 2)) (by omega)]
          convert hi using 2
          ext
          simp only [Fin.val_natAdd]
          omega
      · refine ⟨_, ⟨i.val / 2, by omega, rfl⟩, ?_, Or.inr ?_⟩
        · rw [getD_ofFn x (N + 2 * (i.val / 2) + 1) (by omega)]
          convert hi using 2
          ext
          simp only [Fin.val_natAdd]
          omega
        · rw [if_pos (by omega), getD_ofFn x (N + 2 * (i.val / 2) + 2) (by omega)]
          convert hxj using 2
          ext
          simp only [Fin.val_natAdd]
          omega

private lemma path_equiv_right {N h : ℕ} (hh : 3 ≤ h) (u v : Fin N) (x : Fin (N + 2 * h) → Bool) :
    ((x (Fin.castAdd (2 * h) v) && x (Fin.natAdd N ⟨2 * h - 1, by omega⟩)) ||
      ((List.range h).map fun k =>
        (N + 2 * k, if k = 0 then u.val else N + 2 * k - 1, N + 2 * k + 1)).any
        (fun t => (List.ofFn x).getD t.1 false &&
          ((List.ofFn x).getD t.2.1 false || (List.ofFn x).getD t.2.2 false))) =
    decide (∃ i : Fin (2 * h), x (Fin.natAdd N i) = true ∧
      ((i.val = 0 ∧ x (Fin.castAdd (2 * h) u) = true) ∨
       (i.val + 1 = 2 * h ∧ x (Fin.castAdd (2 * h) v) = true) ∨
       ∃ j : Fin (2 * h), j.val = i.val + 1 ∧ x (Fin.natAdd N j) = true)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.or_eq_true, Bool.and_eq_true, List.any_eq_true, List.mem_map, List.mem_range,
    decide_eq_true_eq]
  constructor
  · rintro (⟨hv, hzl⟩ | ⟨_, ⟨k, hk, rfl⟩, ha, hb | hc⟩)
    · exact ⟨⟨2 * h - 1, by omega⟩, hzl, Or.inr (Or.inl ⟨by simp; omega, hv⟩)⟩
    · rw [getD_ofFn x (N + 2 * k) (by omega)] at ha
      by_cases hk0 : k = 0
      · subst hk0
        rw [if_pos rfl, getD_ofFn x u.val (by omega)] at hb
        refine ⟨⟨0, by omega⟩, ?_, Or.inl ⟨rfl, ?_⟩⟩
        · convert ha using 2
          ext
          simp only [Fin.val_natAdd]
        · convert hb using 2
          ext
          simp only [Fin.val_castAdd]
      · rw [if_neg hk0, getD_ofFn x (N + 2 * k - 1) (by omega)] at hb
        refine ⟨⟨2 * k - 1, by omega⟩, ?_, Or.inr (Or.inr ⟨⟨2 * k, by omega⟩, by simp; omega, ?_⟩)⟩
        · convert hb using 2
          ext
          simp only [Fin.val_natAdd]
          omega
        · convert ha using 2
          ext
          simp only [Fin.val_natAdd]
    · rw [getD_ofFn x (N + 2 * k) (by omega)] at ha
      rw [getD_ofFn x (N + 2 * k + 1) (by omega)] at hc
      refine ⟨⟨2 * k, by omega⟩, ?_, Or.inr (Or.inr ⟨⟨2 * k + 1, by omega⟩, rfl, ?_⟩)⟩
      · convert ha using 2
        ext
        simp only [Fin.val_natAdd]
      · convert hc using 2
        ext
        simp only [Fin.val_natAdd]
        omega
  · rintro ⟨i, hi, ⟨hi0, hu⟩ | ⟨hilast, hv⟩ | ⟨j, hj, hxj⟩⟩
    · right
      refine ⟨_, ⟨0, by omega, rfl⟩, ?_, Or.inl ?_⟩
      · rw [getD_ofFn x (N + 2 * 0) (by omega)]
        convert hi using 2
        ext
        simp only [Fin.val_natAdd]
        omega
      · rw [if_pos rfl, getD_ofFn x u.val (by omega)]
        convert hu using 2
        ext
        simp only [Fin.val_castAdd]
    · left
      refine ⟨hv, ?_⟩
      convert hi using 2
      ext
      simp only [Fin.val_natAdd]
      omega
    · right
      by_cases heven : i.val % 2 = 0
      · refine ⟨_, ⟨i.val / 2, by omega, rfl⟩, ?_, Or.inr ?_⟩
        · rw [getD_ofFn x (N + 2 * (i.val / 2)) (by omega)]
          convert hi using 2
          ext
          simp only [Fin.val_natAdd]
          omega
        · rw [getD_ofFn x (N + 2 * (i.val / 2) + 1) (by omega)]
          convert hxj using 2
          ext
          simp only [Fin.val_natAdd]
          omega
      · refine ⟨_, ⟨i.val / 2 + 1, by omega, rfl⟩, ?_, Or.inl ?_⟩
        · rw [getD_ofFn x (N + 2 * (i.val / 2 + 1)) (by omega)]
          convert hxj using 2
          ext
          simp only [Fin.val_natAdd]
          omega
        · rw [if_neg (by omega), getD_ofFn x (N + 2 * (i.val / 2 + 1) - 1) (by omega)]
          convert hi using 2
          ext
          simp only [Fin.val_natAdd]
          omega

end PEqualNP.Outside.LMeta571

theorem PEqualNP.Outside.L_meta_571 : ∀ (N h : ℕ) (u v : Fin N) (g : (Fin N → Bool) → Bool), u ≠ v → 3 ≤ h → g (fun _ : Fin N => false) = false → (∃ x : Fin N → Bool, x u = true ∧ g x = false) → (∃ x : Fin N → Bool, x v = true ∧ g x = false) → ∀ s : ℕ, (PEqualNP.MetaComplexity.HasCircuitSize (N + 1) (fun x : Fin (N + 1) → Bool => g (fun i : Fin N => x i.castSucc) || (x u.castSucc && x (Fin.last N))) s → PEqualNP.MetaComplexity.HasCircuitSize (N + 2 * h) (fun x : Fin (N + 2 * h) → Bool => g (fun i : Fin N => x (Fin.castAdd (2 * h) i)) || decide (∃ i : Fin (2 * h), x (Fin.natAdd N i) = true ∧ ((i.val = 0 ∧ x (Fin.castAdd (2 * h) u) = true) ∨ (i.val + 1 = 2 * h ∧ x (Fin.castAdd (2 * h) v) = true) ∨ ∃ j : Fin (2 * h), j.val = i.val + 1 ∧ x (Fin.natAdd N j) = true))) (3 * h + s)) ∧ (PEqualNP.MetaComplexity.HasCircuitSize (N + 1) (fun x : Fin (N + 1) → Bool => g (fun i : Fin N => x i.castSucc) || (x v.castSucc && x (Fin.last N))) s → PEqualNP.MetaComplexity.HasCircuitSize (N + 2 * h) (fun x : Fin (N + 2 * h) → Bool => g (fun i : Fin N => x (Fin.castAdd (2 * h) i)) || decide (∃ i : Fin (2 * h), x (Fin.natAdd N i) = true ∧ ((i.val = 0 ∧ x (Fin.castAdd (2 * h) u) = true) ∨ (i.val + 1 = 2 * h ∧ x (Fin.castAdd (2 * h) v) = true) ∨ ∃ j : Fin (2 * h), j.val = i.val + 1 ∧ x (Fin.natAdd N j) = true))) (3 * h + s)) := by
  intro N h u v g _ hh _ _ _ s
  constructor
  · rintro ⟨C, hF, hsize, heval⟩
    let M := N + 2 * h
    let dead := M + C.gates.length + 3 * h + 1
    let f : ℕ → ℕ := fun i => if i < N then i else N
    let C0 := PEqualNP.Outside.LMeta571.embedCircuit (N + 1) M dead f C
    let stars := (List.range h).map fun k =>
      (N + 2 * k + 1, N + 2 * k, if k + 1 < h then N + 2 * k + 2 else v.val)
    refine ⟨PEqualNP.Outside.LMeta571.addStars M stars C0, ?_, ?_, ?_⟩
    · exact PEqualNP.Outside.LMeta571.addStars_fanInTwo M stars C0
        (PEqualNP.Outside.LMeta571.embedGates_fanInTwo (N + 1) M dead f C _ hF)
    · rw [PEqualNP.Outside.LMeta571.addStars_size]
      have hlen : stars.length = h := by simp [stars]
      have hc0 : C0.size = C.size := PEqualNP.Outside.LMeta571.embedGates_length (N + 1) M dead f C.gates
      rw [hlen, hc0]
      omega
    · intro x
      have hstars : ∀ t ∈ stars, t.1 < M ∧ t.2.1 < M ∧ t.2.2 < M := by
        intro t ht
        simp only [stars, List.mem_map, List.mem_range] at ht
        obtain ⟨k, hk, rfl⟩ := ht
        refine ⟨by dsimp only; omega, by dsimp only; omega, ?_⟩
        dsimp only
        split_ifs
        · omega
        · have hv := v.isLt; omega
      have hout : C0.output < M + C0.gates.length ∨ M + C0.gates.length + 3 * stars.length ≤ C0.output := by
        have hlen : stars.length = h := by simp [stars]
        have hc0 : C0.gates.length = C.gates.length :=
          PEqualNP.Outside.LMeta571.embedGates_length (N + 1) M dead f C.gates
        rw [hlen, hc0]
        dsimp only [C0, PEqualNP.Outside.LMeta571.embedCircuit, PEqualNP.Outside.LMeta571.remapIdx]
        split_ifs
        · left; dsimp only [f]; split_ifs <;> omega
        · left; omega
        · right; omega
      rw [PEqualNP.Outside.LMeta571.addStars_eval M stars C0 (List.ofFn x) (List.length_ofFn) hstars hout]
      let x0 : Fin (N + 1) → Bool := fun i =>
        if hi : i.val < N then x (Fin.castAdd (2 * h) ⟨i.val, hi⟩)
        else x (Fin.natAdd N ⟨0, by omega⟩)
      have hf : ∀ i < N + 1, f i < M ∧ (List.ofFn x).getD (f i) false = (List.ofFn x0).getD i false := by
        intro i hi
        by_cases hiN : i < N
        · refine ⟨by simp [f, hiN, M]; omega, ?_⟩
          have hfi : f i = i := by simp [f, hiN]
          rw [hfi, PEqualNP.Outside.LMeta571.getD_ofFn x i (by omega),
            PEqualNP.Outside.LMeta571.getD_ofFn x0 i hi]
          simp [x0, hiN]
        · refine ⟨by simp [f, hiN, M]; omega, ?_⟩
          have hfi : f i = N := by simp [f, hiN]
          rw [hfi, PEqualNP.Outside.LMeta571.getD_ofFn x N (by omega),
            PEqualNP.Outside.LMeta571.getD_ofFn x0 i hi]
          simp [x0, hiN]
      have hc0eval : C0.eval (List.ofFn x) = C.eval (List.ofFn x0) :=
        PEqualNP.Outside.LMeta571.embedCircuit_eval (N + 1) M dead f C (List.ofFn x0) (List.ofFn x)
          List.length_ofFn List.length_ofFn hf (by omega)
      rw [hc0eval, heval x0]
      have hx0g : (fun i : Fin N => x0 i.castSucc) = (fun i : Fin N => x (Fin.castAdd (2 * h) i)) := by
        funext i
        simp only [x0, Fin.val_castSucc, i.isLt, dite_true]
      have hx0u : x0 u.castSucc = x (Fin.castAdd (2 * h) u) := by
        simp only [x0, Fin.val_castSucc, u.isLt, dite_true]
      have hx0last : x0 (Fin.last N) = x (Fin.natAdd N ⟨0, by omega⟩) := by
        simp [x0]
      dsimp only [stars]
      rw [hx0g, hx0u, hx0last, Bool.or_assoc, PEqualNP.Outside.LMeta571.path_equiv_left hh u v x]
  · rintro ⟨C, hF, hsize, heval⟩
    let M := N + 2 * h
    let dead := M + C.gates.length + 3 * h + 1
    let f : ℕ → ℕ := fun i => if i < N then i else N + (2 * h - 1)
    let C0 := PEqualNP.Outside.LMeta571.embedCircuit (N + 1) M dead f C
    let stars := (List.range h).map fun k =>
      (N + 2 * k, if k = 0 then u.val else N + 2 * k - 1, N + 2 * k + 1)
    refine ⟨PEqualNP.Outside.LMeta571.addStars M stars C0, ?_, ?_, ?_⟩
    · exact PEqualNP.Outside.LMeta571.addStars_fanInTwo M stars C0
        (PEqualNP.Outside.LMeta571.embedGates_fanInTwo (N + 1) M dead f C _ hF)
    · rw [PEqualNP.Outside.LMeta571.addStars_size]
      have hlen : stars.length = h := by simp [stars]
      have hc0 : C0.size = C.size := PEqualNP.Outside.LMeta571.embedGates_length (N + 1) M dead f C.gates
      rw [hlen, hc0]
      omega
    · intro x
      have hstars : ∀ t ∈ stars, t.1 < M ∧ t.2.1 < M ∧ t.2.2 < M := by
        intro t ht
        simp only [stars, List.mem_map, List.mem_range] at ht
        obtain ⟨k, hk, rfl⟩ := ht
        refine ⟨by dsimp only; omega, ?_, by dsimp only; omega⟩
        dsimp only
        split_ifs
        · have hu := u.isLt; omega
        · omega
      have hout : C0.output < M + C0.gates.length ∨ M + C0.gates.length + 3 * stars.length ≤ C0.output := by
        have hlen : stars.length = h := by simp [stars]
        have hc0 : C0.gates.length = C.gates.length :=
          PEqualNP.Outside.LMeta571.embedGates_length (N + 1) M dead f C.gates
        rw [hlen, hc0]
        dsimp only [C0, PEqualNP.Outside.LMeta571.embedCircuit, PEqualNP.Outside.LMeta571.remapIdx]
        split_ifs
        · left; dsimp only [f]; split_ifs <;> omega
        · left; omega
        · right; omega
      rw [PEqualNP.Outside.LMeta571.addStars_eval M stars C0 (List.ofFn x) (List.length_ofFn) hstars hout]
      let x0 : Fin (N + 1) → Bool := fun i =>
        if hi : i.val < N then x (Fin.castAdd (2 * h) ⟨i.val, hi⟩)
        else x (Fin.natAdd N ⟨2 * h - 1, by omega⟩)
      have hf : ∀ i < N + 1, f i < M ∧ (List.ofFn x).getD (f i) false = (List.ofFn x0).getD i false := by
        intro i hi
        by_cases hiN : i < N
        · refine ⟨by simp [f, hiN, M]; omega, ?_⟩
          have hfi : f i = i := by simp [f, hiN]
          rw [hfi, PEqualNP.Outside.LMeta571.getD_ofFn x i (by omega),
            PEqualNP.Outside.LMeta571.getD_ofFn x0 i hi]
          simp [x0, hiN]
        · refine ⟨by simp [f, hiN, M]; omega, ?_⟩
          have hfi : f i = N + (2 * h - 1) := by simp [f, hiN]
          rw [hfi, PEqualNP.Outside.LMeta571.getD_ofFn x (N + (2 * h - 1)) (by omega),
            PEqualNP.Outside.LMeta571.getD_ofFn x0 i hi]
          simp [x0, hiN]
      have hc0eval : C0.eval (List.ofFn x) = C.eval (List.ofFn x0) :=
        PEqualNP.Outside.LMeta571.embedCircuit_eval (N + 1) M dead f C (List.ofFn x0) (List.ofFn x)
          List.length_ofFn List.length_ofFn hf (by omega)
      rw [hc0eval, heval x0]
      have hx0g : (fun i : Fin N => x0 i.castSucc) = (fun i : Fin N => x (Fin.castAdd (2 * h) i)) := by
        funext i
        simp only [x0, Fin.val_castSucc, i.isLt, dite_true]
      have hx0v : x0 v.castSucc = x (Fin.castAdd (2 * h) v) := by
        simp only [x0, Fin.val_castSucc, v.isLt, dite_true]
      have hx0last : x0 (Fin.last N) = x (Fin.natAdd N ⟨2 * h - 1, by omega⟩) := by
        simp [x0]
      dsimp only [stars]
      rw [hx0g, hx0v, hx0last, Bool.or_assoc, PEqualNP.Outside.LMeta571.path_equiv_right hh u v x]
