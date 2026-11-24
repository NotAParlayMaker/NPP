import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3264

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wiresFrom (gs ++ [g]) w = wiresFrom gs w ++
      [g.op.eval (g.inputs.map fun i => (wiresFrom gs w).getD i false)] := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [wiresFrom]
  | append_singleton gs g ih => rw [wiresFrom_snoc, List.length_append, ih]; simp; omega

theorem wiresFrom_getD_lt (gs : List Gate) (g : Gate) (w : List Bool) (i : ℕ)
    (hi : i < (wiresFrom gs w).length) :
    (wiresFrom (gs ++ [g]) w).getD i false = (wiresFrom gs w).getD i false := by
  rw [wiresFrom_snoc, List.getD_append _ _ _ _ hi]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl


theorem wiresFrom_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wiresFrom (g :: gs) w = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) :=
  rfl

theorem wiresFrom_append (gs hs : List Gate) (w : List Bool) :
    wiresFrom (gs ++ hs) w = wiresFrom hs (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  induction gs using List.reverseRecOn with
  | nil => rfl
  | append_singleton gs g ih =>
    rw [wiresFrom_snoc, List.getD_append _ _ _ _ (by rw [wiresFrom_length]; omega), ih]

def chain (acc idx : ℕ) : List ℕ → List Gate
  | [] => []
  | w :: ws => ⟨GateOp.or, [acc, w]⟩ :: chain idx (idx + 1) ws

def chainOut (acc idx : ℕ) : List ℕ → ℕ
  | [] => acc
  | _ :: ws => chainOut idx (idx + 1) ws

theorem chain_length (acc idx : ℕ) (ws : List ℕ) : (chain acc idx ws).length = ws.length := by
  induction ws generalizing acc idx with
  | nil => rfl
  | cons w ws ih => simp [chain, ih]

theorem chain_eval (ws : List ℕ) : ∀ (acc : ℕ) (V : List Bool), acc < V.length →
    (∀ w ∈ ws, w < V.length) →
    (wiresFrom (chain acc V.length ws) V).getD (chainOut acc V.length ws) false =
      (V.getD acc false || ws.any (fun w => V.getD w false)) := by
  induction ws with
  | nil => intro acc V hacc _; simp [chain, chainOut, wiresFrom]
  | cons w ws ih =>
    intro acc V hacc hws
    simp only [chain, chainOut, wiresFrom_cons]
    set V' := V ++ [GateOp.or.eval ([acc, w].map fun i => V.getD i false)] with hV'
    have hl : V'.length = V.length + 1 := by simp [hV']
    have h := ih V.length V' (by omega) (fun u hu => by have := hws u (by simp [hu]); omega)
    rw [show V.length + 1 = V'.length by omega, h]
    have e1 : V'.getD V.length false = (V.getD acc false || V.getD w false) := by
      rw [hV', List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero]
      simp [GateOp.eval]
    have e2 : ∀ u ∈ ws, V'.getD u false = V.getD u false := by
      intro u hu
      rw [hV', List.getD_append _ _ _ _ (hws u (by simp [hu]))]
    have e3 : ws.any (fun u => V'.getD u false) = ws.any (fun u => V.getD u false) := by
      rw [Bool.eq_iff_iff]
      simp only [List.any_eq_true]
      constructor
      · rintro ⟨u, hu, h⟩
        exact ⟨u, hu, by rw [← e2 u hu]; exact h⟩
      · rintro ⟨u, hu, h⟩
        exact ⟨u, hu, by rw [e2 u hu]; exact h⟩
    rw [e1, e3, List.any_cons]
    cases V.getD acc false <;> cases V.getD w false <;> simp


theorem gate_val (gs : List Gate) (y : List Bool) (j : ℕ) (hj : j < gs.length)
    (hrb : ∀ u ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, u < y.length + j) :
    (wiresFrom gs y).getD (y.length + j) false = (gs.getD j ⟨GateOp.or, []⟩).op.eval
      ((gs.getD j ⟨GateOp.or, []⟩).inputs.map fun u => (wiresFrom gs y).getD u false) := by
  have hsplit : gs = gs.take j ++ [gs.getD j ⟨GateOp.or, []⟩] ++ gs.drop (j + 1) := by
    rw [List.getD_eq_getElem _ _ hj, List.append_assoc, List.singleton_append,
      ← List.drop_eq_getElem_cons hj, List.take_append_drop]
  have hlt : ∀ u, u < y.length + j + 1 → (wiresFrom gs y).getD u false =
      (wiresFrom (gs.take j ++ [gs.getD j ⟨GateOp.or, []⟩]) y).getD u false := by
    intro u hu
    conv_lhs => rw [hsplit]
    rw [wiresFrom_append, wiresFrom_prefix _ _ _ (by rw [wiresFrom_length]; simp <;> omega)]
  rw [hlt _ (by omega), wiresFrom_snoc, List.getD_append_right _ _ _ _
    (by rw [wiresFrom_length]; simp <;> omega)]
  have hl : (wiresFrom (gs.take j) y).length = y.length + j := by
    rw [wiresFrom_length, List.length_take, min_eq_left hj.le]
  rw [hl, Nat.sub_self, List.getD_cons_zero]
  congr 1
  apply List.map_congr_left
  intro u hu
  rw [hlt u (by have := hrb u hu; omega), wiresFrom_snoc,
    List.getD_append _ _ _ _ (by rw [hl]; exact hrb u hu)]

theorem chain_shape (ws : List ℕ) : ∀ (acc idx : ℕ), acc < idx → (∀ w ∈ ws, w < idx) →
    ∀ k < ws.length, ((chain acc idx ws).getD k ⟨GateOp.or, []⟩).op = GateOp.or ∧
      ((chain acc idx ws).getD k ⟨GateOp.or, []⟩).inputs.length = 2 ∧
      ∀ u ∈ ((chain acc idx ws).getD k ⟨GateOp.or, []⟩).inputs, u < idx + k := by
  induction ws with
  | nil => intro _ _ _ _ k hk; simp at hk
  | cons w ws ih =>
    intro acc idx hacc hws k hk
    cases k with
    | zero =>
      simp only [chain, List.getD_cons_zero]
      refine ⟨by simp, by simp, ?_⟩
      intro u hu
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl
      · omega
      · have := hws u (by simp); omega
    | succ k =>
      simp only [chain, List.getD_cons_succ]
      have h := ih idx (idx + 1) (by omega) (fun u hu => by have := hws u (by simp [hu]); omega) k
        (by simp at hk; omega)
      refine ⟨h.1, h.2.1, fun u hu => by have := h.2.2 u hu; omega⟩

theorem chain_mem (ws : List ℕ) : ∀ (acc idx : ℕ), ∀ g ∈ chain acc idx ws,
    g.op = GateOp.or ∧ g.inputs.length = 2 := by
  induction ws with
  | nil => intro _ _ g hg; simp [chain] at hg
  | cons w ws ih =>
    intro acc idx g hg
    simp only [chain, List.mem_cons] at hg
    rcases hg with rfl | hg
    · exact ⟨rfl, rfl⟩
    · exact ih idx (idx + 1) g hg

theorem chainOut_lt (ws : List ℕ) : ∀ (acc idx : ℕ), acc < idx →
    chainOut acc idx ws < idx + ws.length := by
  induction ws with
  | nil => intro acc idx h; simp [chainOut]; omega
  | cons w ws ih => intro acc idx h; simp only [chainOut, List.length_cons]; have := ih idx (idx + 1) (by omega); omega
def rho (x1 n w : ℕ) : ℕ := if w < x1 then w else w + n

def relab (x1 n : ℕ) (gs : List Gate) : List Gate :=
  gs.map (fun g => (⟨g.op, g.inputs.map (rho x1 n)⟩ : Gate))

def ands (n : ℕ) (ps : List (ℕ × ℕ)) : List Gate :=
  ps.map (fun p => (⟨GateOp.and, [p.1, n + p.2]⟩ : Gate))

def wsOf (n len k : ℕ) : List ℕ := (List.range k).map (fun i => n + n + len + i)

def build (x1 n : ℕ) (C : Circuit) (ps : List (ℕ × ℕ)) : Circuit :=
  ⟨relab x1 n C.gates ++ ands n ps ++
      chain (rho x1 n C.output) (n + n + C.gates.length + ps.length) (wsOf n C.gates.length ps.length),
    chainOut (rho x1 n C.output) (n + n + C.gates.length + ps.length) (wsOf n C.gates.length ps.length)⟩

theorem relab_length (x1 n : ℕ) (gs : List Gate) : (relab x1 n gs).length = gs.length := by
  simp [relab]

theorem ands_length (n : ℕ) (ps : List (ℕ × ℕ)) : (ands n ps).length = ps.length := by
  simp [ands]

theorem wsOf_length (n len k : ℕ) : (wsOf n len k).length = k := by
  simp [wsOf]

theorem relab_getD (x1 n : ℕ) (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    (relab x1 n gs).getD j ⟨GateOp.or, []⟩ =
      ⟨(gs.getD j ⟨GateOp.or, []⟩).op, (gs.getD j ⟨GateOp.or, []⟩).inputs.map (rho x1 n)⟩ := by
  unfold relab
  rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getD_eq_getElem _ _ hj, List.getElem_map]

theorem ands_getD (n : ℕ) (ps : List (ℕ × ℕ)) (i : ℕ) (hi : i < ps.length) :
    (ands n ps).getD i ⟨GateOp.or, []⟩ = ⟨GateOp.and, [ps[i].1, n + ps[i].2]⟩ := by
  unfold ands
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map]

theorem rho_lt (x1 n w j : ℕ) (hw : w < n + j) : rho x1 n w < n + n + j := by
  unfold rho; split_ifs <;> omega

theorem relab_eval (x1 n : ℕ) (gs : List Gate) (Y Z : List Bool) (hx : x1 ≤ n)
    (hZ : Z.length = n) (hY : Y.length = n + n)
    (hrb : ∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < n + j)
    (hin : ∀ w < n, Y.getD (rho x1 n w) false = Z.getD w false) :
    ∀ w, w < n + gs.length →
      (wiresFrom (relab x1 n gs) Y).getD (rho x1 n w) false = (wiresFrom gs Z).getD w false := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hwn : w < n
    · have h1 : rho x1 n w < Y.length := by rw [hY]; unfold rho; split_ifs <;> omega
      rw [wiresFrom_prefix _ _ _ h1, wiresFrom_prefix _ _ _ (by omega), hin w hwn]
    · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      have hj : j < gs.length := by omega
      have hr : rho x1 n (n + j) = Y.length + j := by
        unfold rho; rw [if_neg (by omega), hY]; omega
      have hrb' : ∀ u ∈ ((relab x1 n gs).getD j ⟨GateOp.or, []⟩).inputs, u < Y.length + j := by
        rw [relab_getD _ _ _ _ hj]
        intro u hu
        simp only [List.mem_map] at hu
        obtain ⟨i, hi, rfl⟩ := hu
        rw [hY]
        exact rho_lt x1 n i j (hrb j hj i hi)
      rw [hr, gate_val (relab x1 n gs) Y j (by rw [relab_length]; exact hj) hrb',
        show n + j = Z.length + j by rw [hZ], gate_val gs Z j hj (by rw [hZ]; exact hrb j hj),
        relab_getD _ _ _ _ hj]
      dsimp only
      congr 1
      rw [List.map_map]
      apply List.map_congr_left
      intro i hi
      have := hrb j hj i hi
      exact ih i (by omega) (by omega)

theorem build_size (x1 n : ℕ) (C : Circuit) (ps : List (ℕ × ℕ)) :
    (build x1 n C ps).size = C.size + 2 * ps.length := by
  simp only [build, Circuit.size, List.length_append, relab_length, ands_length, chain_length,
    wsOf_length]
  omega

theorem build_getD_lt (x1 n : ℕ) (C : Circuit) (ps : List (ℕ × ℕ)) (j : ℕ) (hj : j < C.gates.length) :
    (build x1 n C ps).gates.getD j ⟨GateOp.or, []⟩ = (relab x1 n C.gates).getD j ⟨GateOp.or, []⟩ := by
  simp only [build]
  rw [List.getD_append _ _ _ _ (by simp [relab_length, ands_length]; omega),
    List.getD_append _ _ _ _ (by rw [relab_length]; exact hj)]

theorem build_getD_mid (x1 n : ℕ) (C : Circuit) (ps : List (ℕ × ℕ)) (i : ℕ) (hi : i < ps.length) :
    (build x1 n C ps).gates.getD (C.gates.length + i) ⟨GateOp.or, []⟩ = (ands n ps).getD i ⟨GateOp.or, []⟩ := by
  simp only [build]
  rw [List.getD_append _ _ _ _ (by simp [relab_length, ands_length]; omega),
    List.getD_append_right _ _ _ _ (by rw [relab_length]; omega), relab_length]
  congr 1
  omega

theorem build_getD_hi (x1 n : ℕ) (C : Circuit) (ps : List (ℕ × ℕ)) (t : ℕ) :
    (build x1 n C ps).gates.getD (C.gates.length + ps.length + t) ⟨GateOp.or, []⟩ =
      (chain (rho x1 n C.output) (n + n + C.gates.length + ps.length)
        (wsOf n C.gates.length ps.length)).getD t ⟨GateOp.or, []⟩ := by
  simp only [build]
  rw [List.getD_append_right _ _ _ _ (by simp [relab_length, ands_length])]
  congr 1
  simp [relab_length, ands_length]

theorem build_ao2 (x1 n : ℕ) (C : Circuit) (ps : List (ℕ × ℕ)) (hx : x1 ≤ n)
    (hAO : PEqualNP.TopForm.IsAO2 n C) (hout : C.output < n + C.gates.length)
    (hps : ∀ p ∈ ps, p.1 < n ∧ p.2 < n) :
    PEqualNP.TopForm.IsAO2 (n + n) (build x1 n C ps) := by
  obtain ⟨hA, hR, hL⟩ := hAO
  have hacc : rho x1 n C.output < n + n + C.gates.length + ps.length := by
    have := rho_lt x1 n C.output C.gates.length hout; omega
  have hws : ∀ w ∈ wsOf n C.gates.length ps.length, w < n + n + C.gates.length + ps.length := by
    intro w hw
    simp only [wsOf, List.mem_map, List.mem_range] at hw
    obtain ⟨i, hi, rfl⟩ := hw
    omega
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    simp only [build, List.mem_append] at hg
    rcases hg with (hg | hg) | hg
    · simp only [relab, List.mem_map] at hg
      obtain ⟨g0, hg0, rfl⟩ := hg
      exact hA g0 hg0
    · simp only [ands, List.mem_map] at hg
      obtain ⟨p, _, rfl⟩ := hg
      exact Or.inl rfl
    · exact Or.inr (chain_mem _ _ _ g hg).1
  · intro j hj i hi
    simp only [PEqualNP.MetaComplexity.NestedCover.gateAt] at hi
    have hlen : (build x1 n C ps).gates.length = C.gates.length + ps.length + ps.length := by
      simp [build, relab_length, ands_length, chain_length, wsOf_length]; omega
    rw [hlen] at hj
    by_cases h1 : j < C.gates.length
    · rw [build_getD_lt _ _ _ _ _ h1, relab_getD _ _ _ _ h1] at hi
      simp only [List.mem_map] at hi
      obtain ⟨u, hu, rfl⟩ := hi
      exact rho_lt x1 n u j (hR j h1 u (by simpa [PEqualNP.MetaComplexity.NestedCover.gateAt] using hu))
    · by_cases h2 : j < C.gates.length + ps.length
      · obtain ⟨k, rfl⟩ : ∃ k, j = C.gates.length + k := ⟨j - C.gates.length, by omega⟩
        rw [build_getD_mid _ _ _ _ _ (by omega), ands_getD _ _ _ (by omega)] at hi
        have hp := hps ps[k] (List.getElem_mem _)
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl <;> omega
      · obtain ⟨t, rfl⟩ : ∃ t, j = C.gates.length + ps.length + t := ⟨j - C.gates.length - ps.length, by omega⟩
        rw [build_getD_hi] at hi
        have := (chain_shape _ _ _ hacc hws t (by rw [wsOf_length]; omega)).2.2 i hi
        omega
  · intro g hg
    simp only [build, List.mem_append] at hg
    rcases hg with (hg | hg) | hg
    · simp only [relab, List.mem_map] at hg
      obtain ⟨g0, hg0, rfl⟩ := hg
      simp [hL g0 hg0]
    · simp only [ands, List.mem_map] at hg
      obtain ⟨p, _, rfl⟩ := hg
      rfl
    · exact (chain_mem _ _ _ g hg).2

theorem build_eval (x1 n : ℕ) (C : Circuit) (ps : List (ℕ × ℕ)) (hx : x1 ≤ n)
    (hR : PEqualNP.MetaComplexity.NestedCover.ReadsBack n C) (hout : C.output < n + C.gates.length)
    (hps : ∀ p ∈ ps, p.1 < n ∧ p.2 < n) (Y Z : List Bool) (hZ : Z.length = n) (hY : Y.length = n + n)
    (hin : ∀ w < n, Y.getD (rho x1 n w) false = Z.getD w false) :
    (build x1 n C ps).eval Y =
      (C.eval Z || ps.any (fun p => Y.getD p.1 false && Y.getD (n + p.2) false)) := by
  have hrb : ∀ j < C.gates.length, ∀ i ∈ (C.gates.getD j ⟨GateOp.or, []⟩).inputs, i < n + j := by
    intro j hj i hi
    exact hR j hj i (by simpa [PEqualNP.MetaComplexity.NestedCover.gateAt] using hi)
  set R := relab x1 n C.gates with hRdef
  set A := ands n ps with hAdef
  set V := wiresFrom (R ++ A) Y with hVdef
  have hVlen : V.length = n + n + C.gates.length + ps.length := by
    rw [hVdef, wiresFrom_length, List.length_append, hRdef, hAdef, relab_length, ands_length, hY]
    omega
  have hacc : rho x1 n C.output < V.length := by
    have := rho_lt x1 n C.output C.gates.length hout; omega
  have hws : ∀ w ∈ wsOf n C.gates.length ps.length, w < V.length := by
    intro w hw
    simp only [wsOf, List.mem_map, List.mem_range] at hw
    obtain ⟨i, hi, rfl⟩ := hw
    omega
  have hev : (build x1 n C ps).eval Y = (wiresFrom (chain (rho x1 n C.output) V.length
      (wsOf n C.gates.length ps.length)) V).getD
        (chainOut (rho x1 n C.output) V.length (wsOf n C.gates.length ps.length)) false := by
    simp only [Circuit.eval, build, wires_eq]
    rw [wiresFrom_append, hVlen]
  rw [hev, chain_eval _ _ _ hacc hws]
  have hRlen : (wiresFrom R Y).length = n + n + C.gates.length := by
    rw [wiresFrom_length, hRdef, relab_length, hY]
  have e1 : V.getD (rho x1 n C.output) false = C.eval Z := by
    rw [hVdef, wiresFrom_append, wiresFrom_prefix _ _ _ (by rw [hRlen]; exact rho_lt x1 n _ _ hout),
      hRdef, relab_eval x1 n C.gates Y Z hx hZ hY hrb hin C.output hout]
    rfl
  have e2 : ∀ i (hi : i < ps.length), V.getD (n + n + C.gates.length + i) false =
      (Y.getD ps[i].1 false && Y.getD (n + ps[i].2) false) := by
    intro i hi
    have hp := hps ps[i] (List.getElem_mem _)
    have hga : (R ++ A).getD (C.gates.length + i) ⟨GateOp.or, []⟩ = ⟨GateOp.and, [ps[i].1, n + ps[i].2]⟩ := by
      rw [List.getD_append_right _ _ _ _ (by rw [hRdef, relab_length]; omega), hRdef, relab_length,
        show C.gates.length + i - C.gates.length = i by omega, hAdef, ands_getD _ _ _ hi]
    have hlenRA : C.gates.length + i < (R ++ A).length := by
      rw [List.length_append, hRdef, hAdef, relab_length, ands_length]; omega
    have key := gate_val (R ++ A) Y (C.gates.length + i) hlenRA (by
      rw [hga]; intro u hu
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl <;> omega)
    rw [show n + n + C.gates.length + i = Y.length + (C.gates.length + i) by rw [hY]; omega, ← hVdef] at *
    rw [key, hga]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id, Bool.and_true]
    rw [hVdef, wiresFrom_prefix _ _ _ (by omega), wiresFrom_prefix _ _ _ (by omega)]
  rw [e1]
  congr 1
  rw [Bool.eq_iff_iff]
  simp only [wsOf, List.any_map, List.any_eq_true, List.mem_range, Function.comp]
  constructor
  · rintro ⟨i, hi, h⟩
    rw [e2 i hi] at h
    exact ⟨ps[i], List.getElem_mem _, h⟩
  · rintro ⟨p, hp, h⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hp
    exact ⟨i, hi, by rw [e2 i hi]; exact h⟩

theorem getD_ofFn {m : ℕ} (f : Fin m → Bool) (i : ℕ) (hi : i < m) :
    (List.ofFn f).getD i false = f ⟨i, hi⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_ofFn]

end PEqualNP.Outside.L_meta_3264

open PEqualNP.Outside.L_meta_3264 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_3264 : ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   x3.Nonempty →     PEqualNP.TopForm.IsAO2 (x1 + x2) x4 →       (∀ (x7 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x4 x7 = Decidable.decide (∃ (x8 : Fin x1) (x9 : Fin x2), (x8, x9) ∈ x3 ∧ x7 (Fin.castAdd x2 x8) = Bool.true ∧ x7 (Fin.natAdd x1 x9) = Bool.true)) →         let x8 : ℕ := x1 + x2;         have x9 : Finset (Fin (x1 + x2) × Fin (x1 + x2)) := Finset.image (fun (x9 : Fin x1 × Fin x2) => (Fin.castAdd x2 x9.1, Fin.natAdd x1 x9.2)) x3;         ∀ (x10 : Finset (Fin x8 × Fin x8)), ∃ (x11 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (x8 + x8) x11 ∧ x11.size ≤ x4.size + (2 : ℕ) * x10.card ∧ ∀ (x12 : Fin (x8 + x8) → Bool), PEqualNP.MetaComplexity.circuitFun (x8 + x8) x11 x12 = Decidable.decide (∃ (x13 : Fin (x1 + x2)) (x14 : Fin (x1 + x2)), (x13, x14) ∈ x9 ∪ x10 ∧ x12 (Fin.castAdd (x1 + x2) x13) = Bool.true ∧ x12 (Fin.natAdd (x1 + x2) x14) = Bool.true) := by
  intro x1 x2 x3 x4 hne hAO hF
  dsimp only
  have hout : x4.output < (x1 + x2) + x4.gates.length := by
    by_contra hge
    obtain ⟨⟨p, l⟩, hpl⟩ := hne
    have h := hF (fun v => decide (v = Fin.castAdd x2 p ∨ v = Fin.natAdd x1 l))
    have hl : (x4.wires (List.ofFn (fun v : Fin (x1 + x2) => decide (v = Fin.castAdd x2 p ∨ v = Fin.natAdd x1 l)))).length
        = (x1 + x2) + x4.gates.length := by
      rw [wires_eq, wiresFrom_length, List.length_ofFn]
    have hge' : (x4.wires (List.ofFn (fun v : Fin (x1 + x2) => decide (v = Fin.castAdd x2 p ∨ v = Fin.natAdd x1 l)))).length ≤ x4.output := by
      rw [hl]; omega
    simp only [PEqualNP.MetaComplexity.circuitFun, Circuit.eval] at h
    rw [List.getD_eq_default _ _ hge'] at h
    have : (∃ (x9 : Fin x1) (x10 : Fin x2), (x9, x10) ∈ x3 ∧
        decide (Fin.castAdd x2 x9 = Fin.castAdd x2 p ∨ Fin.castAdd x2 x9 = Fin.natAdd x1 l) = true ∧
        decide (Fin.natAdd x1 x10 = Fin.castAdd x2 p ∨ Fin.natAdd x1 x10 = Fin.natAdd x1 l) = true) :=
      ⟨p, l, hpl, by simp, by simp⟩
    rw [decide_eq_true this] at h
    exact Bool.false_ne_true h
  set n := x1 + x2 with hn
  have hx : x1 ≤ n := by omega
  intro x10
  set ps : List (ℕ × ℕ) := x10.toList.map (fun pr => (pr.1.val, pr.2.val)) with hps
  have hpsb : ∀ p ∈ ps, p.1 < n ∧ p.2 < n := by
    intro p hp
    simp only [hps, List.mem_map] at hp
    obtain ⟨pr, _, rfl⟩ := hp
    exact ⟨pr.1.isLt, pr.2.isLt⟩
  refine ⟨build x1 n x4 ps, build_ao2 x1 n x4 ps hx hAO hout hpsb, ?_, ?_⟩
  · rw [build_size, hps, List.length_map, Finset.length_toList]
  · intro y
    have hrhoN : ∀ v : Fin n, rho x1 n v.val < n + n := fun v => by
      have := rho_lt x1 n v.val 0 (by omega); omega
    set z : Fin n → Bool := fun v => y ⟨rho x1 n v.val, hrhoN v⟩ with hz
    have hin : ∀ w < n, (List.ofFn y).getD (rho x1 n w) false = (List.ofFn z).getD w false := by
      intro w hw
      rw [getD_ofFn _ _ (hrhoN ⟨w, hw⟩), getD_ofFn _ _ hw]
    have hE := build_eval x1 n x4 ps hx hAO.2.1 hout hpsb (List.ofFn y) (List.ofFn z)
      (List.length_ofFn) (List.length_ofFn) hin
    simp only [PEqualNP.MetaComplexity.circuitFun]
    rw [hE]
    have hFz := hF z
    simp only [PEqualNP.MetaComplexity.circuitFun] at hFz
    rw [hFz]
    rw [Bool.eq_iff_iff]
    simp only [Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true, Bool.and_eq_true, hps,
      List.mem_map, Finset.mem_toList, Finset.mem_union, Finset.mem_image]
    have zc : ∀ p : Fin x1, z (Fin.castAdd x2 p) = y (Fin.castAdd n (Fin.castAdd x2 p)) := by
      intro p; simp only [hz]; congr 1; ext; simp [rho, p.isLt]
    have zn : ∀ l : Fin x2, z (Fin.natAdd x1 l) = y (Fin.natAdd n (Fin.natAdd x1 l)) := by
      intro l; simp only [hz]; congr 1; ext; simp [rho]; omega
    have yl : ∀ a : Fin n, (List.ofFn y).getD a.val false = y (Fin.castAdd n a) := by
      intro a; rw [getD_ofFn _ _ (by omega)]; rfl
    have yr : ∀ b : Fin n, (List.ofFn y).getD (n + b.val) false = y (Fin.natAdd n b) := by
      intro b; rw [getD_ofFn _ _ (by omega)]; rfl
    constructor
    · rintro (⟨p, l, hpl, h1, h2⟩ | ⟨q, ⟨pr, hpr, rfl⟩, h1, h2⟩)
      · exact ⟨Fin.castAdd x2 p, Fin.natAdd x1 l, Or.inl ⟨(p, l), hpl, rfl⟩, by rw [← zc]; exact h1,
          by rw [← zn]; exact h2⟩
      · exact ⟨pr.1, pr.2, Or.inr hpr, by rw [← yl]; exact h1, by rw [← yr]; exact h2⟩
    · rintro ⟨a, b, hab, h1, h2⟩
      rcases hab with ⟨⟨p, l⟩, hpl, he⟩ | hab
      · simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        exact Or.inl ⟨p, l, hpl, by rw [zc]; exact h1, by rw [zn]; exact h2⟩
      · exact Or.inr ⟨(a.val, b.val), ⟨(a, b), hab, rfl⟩, by rw [yl]; exact h1, by rw [yr]; exact h2⟩
