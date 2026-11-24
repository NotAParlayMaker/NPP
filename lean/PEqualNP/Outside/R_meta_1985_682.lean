import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_1985_682
    (clean : ∀ C : Circuit, Monotone2 C →
      (∀ i < C.gates.length, (gateAt C i).op = .and → ∀ u v : Fin 14,
        gateVal 14 C i (pairInput u v) = true → C.eval (List.ofFn (pairInput u v)) = true) →
      (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔
        ∃ u v : Fin 14, 14 * u.val + v.val ∈
          ([7,8,10,21,23,27,36,40,41,49,53,54,66,67,69,79,80,82,92,93,95] : List ℕ) ∧
          x u = true ∧ x v = true) → 27 ≤ C.size)
    (blocked : ∀ C : Circuit, Monotone2 C → ReadsBack 14 C →
      (∃ (i j : ℕ) (u v : Fin 14),
        (gateAt C i).op = .and ∧ (gateAt C j).op = .and ∧ InCone 14 C i j ∧
        (j = C.output - 14 ∨ InCone 14 C j (C.output - 14)) ∧
        gateVal 14 C i (pairInput u v) = true ∧ gateVal 14 C j (pairInput u v) = false ∧
        C.eval (List.ofFn (pairInput u v)) = false) →
      (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔
        ∃ u v : Fin 14, 14 * u.val + v.val ∈
          ([7,8,10,21,23,27,36,40,41,49,53,54,66,67,69,79,80,82,92,93,95] : List ℕ) ∧
          x u = true ∧ x v = true) → 27 ≤ C.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (14 : ℕ) x1 → (∃ (x4 : ℕ) (x5 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x5).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x4 x5) → (∀ (x5 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (14 : ℕ)) (x7 : Fin (14 : ℕ)), (↑x6, ↑x7) ∈ [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (7 : ℕ)), ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))] ∧ x5 x6 = Bool.true ∧ x5 x7 = Bool.true) → (27 : ℕ) ≤ x1.size := by
  let wF (gs : List Gate) (w : List Bool) : List Bool :=
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

  have wF_append (gs gs' : List Gate) (w : List Bool) :
      wF (gs ++ gs') w = wF gs' (wF gs w) := by
    simp [wF, List.foldl_append]

  have wF_start (gs : List Gate) : ∀ w : List Bool,
      ∃ t : List Bool, wF gs w = w ++ t ∧ t.length = gs.length := by
    induction gs with
    | nil => intro w; exact ⟨[], by simp [wF], rfl⟩
    | cons g gs ih =>
      intro w
      obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
      have : wF (g :: gs) w
          = wF gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
      rw [this, ht]; simp

  have length_wF (gs : List Gate) (w : List Bool) :
      (wF gs w).length = w.length + gs.length := by
    obtain ⟨t, ht, hl⟩ := wF_start gs w
    rw [ht]; simp [hl]

  have getD_wF (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
      (wF gs w).getD i false = w.getD i false := by
    obtain ⟨t, ht, _⟩ := wF_start gs w
    rw [ht, List.getD_append _ _ _ _ h]

  have getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
      (L ++ [S]).getD k d = S := by
    subst h; simp

  have split_at {α : Type} : ∀ (l : List α) (p : ℕ) (g : α), l[p]? = some g →
      ∃ pre post, l = pre ++ g :: post ∧ pre.length = p := by
    intro l
    induction l with
    | nil => intro p g h; simp at h
    | cons x l ih =>
      intro p g h
      cases p with
      | zero =>
        simp at h
        subst h
        exact ⟨[], l, rfl, rfl⟩
      | succ p =>
        simp at h
        obtain ⟨pre, post, rfl, rfl⟩ := ih p g h
        exact ⟨x :: pre, post, rfl, rfl⟩

  have wire_at (n : ℕ) (pre post : List Gate) (g : Gate) (X : List Bool) (hX : X.length = n) :
      (wF (pre ++ g :: post) X).getD (n + pre.length) false
        = g.op.eval (g.inputs.map fun i => (wF pre X).getD i false) := by
    have h1 : wF (pre ++ g :: post) X = wF post
        (wF pre X ++ [g.op.eval (g.inputs.map fun i => (wF pre X).getD i false)]) := by
      rw [wF_append]; rfl
    have hl : (wF pre X).length = n + pre.length := by
      rw [length_wF]; omega
    rw [h1, getD_wF _ _ _ (by simp [hl]), getD_snoc_len _ _ _ _ hl]

  -- The value of wire w.
  let V (gs : List Gate) (x : List Bool) (w : ℕ) : Bool := (wF gs x).getD w false

  have eval_eq (gs : List Gate) (out : ℕ) (x : List Bool) :
      Circuit.eval ⟨gs, out⟩ x = V gs x out := rfl

  have V_prefix (pre post : List Gate) (x : List Bool) (w : ℕ) (h : w < x.length + pre.length) :
      V (pre ++ post) x w = V pre x w := by
    unfold V
    rw [wF_append, getD_wF _ _ _ (by rw [length_wF]; exact h)]

  have gate_val_aux (gs : List Gate) (x : List Bool) (hx : x.length = 14) (i : ℕ) (g : Gate)
      (hg : gs[i]? = some g) (hw : ∀ w ∈ g.inputs, w < 14 + i) :
      V gs x (14 + i) = g.op.eval (g.inputs.map (V gs x)) := by
    obtain ⟨pre, post, hsplit, hlen⟩ := split_at gs i g hg
    subst hsplit
    subst hlen
    have h1 : V (pre ++ g :: post) x (14 + pre.length)
        = g.op.eval (g.inputs.map fun w => (wF pre x).getD w false) :=
      wire_at 14 pre post g x hx
    rw [h1]
    congr 1
    apply List.map_congr_left
    intro w hwm
    exact (V_prefix pre (g :: post) x w (by rw [hx]; exact hw w hwm)).symm

  have getD_ofFn {α : Type} (m : ℕ) (F : Fin m → α) (d : α) (j : ℕ) (h : j < m) :
      (List.ofFn F).getD j d = F ⟨j, h⟩ := by
    simp [List.getD_eq_getElem?_getD, h]


  have V_out (gs : List Gate) (x : List Bool) (w : ℕ) (h : x.length + gs.length ≤ w) :
      V gs x w = false := by
    unfold V
    exact List.getD_eq_default _ _ (by rw [length_wF]; exact h)

  have V_in (gs gs' : List Gate) (x : List Bool) (w : ℕ) (h : w < x.length) :
      V gs x w = V gs' x w := by
    unfold V
    rw [getD_wF _ _ _ h, getD_wF _ _ _ h]

  have V_gate_some (gs : List Gate) (x : List Bool) (hx : x.length = 14) (i : ℕ)
      (h : V gs x (14 + i) = true) : ∃ g, gs[i]? = some g := by
    have hi : i < gs.length := by
      by_contra hi
      rw [V_out gs x (14 + i) (by rw [hx]; omega)] at h
      exact Bool.false_ne_true h
    exact ⟨gs[i], List.getElem?_eq_getElem hi⟩

  have orN (gs : List Gate) (x : List Bool) (hx : x.length = 14) (i : ℕ) (g : Gate)
      (hg : gs[i]? = some g) (hw : ∀ w ∈ g.inputs, w < 14 + i) (hop : g.op = GateOp.or) :
      V gs x (14 + i) = true ↔ ∃ w ∈ g.inputs, V gs x w = true := by
    rw [gate_val_aux gs x hx i g hg hw, hop]
    change (g.inputs.map (V gs x)).any id = true ↔ _
    simp

  -- Cone lemmas, from the merged file L_meta_1600.lean.
  have split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
      ∃ (pre post : List Gate) (gj : Gate),
        gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
    refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
    rw [List.cons_getElem_drop_succ, List.take_append_drop]

  have gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
    change C.gates.getD k ⟨.or, []⟩ = C.gates[k]
    exact List.getD_eq_getElem _ _ hk

  have coneStep_eq (n : ℕ) (cs : List (List ℕ)) (g : Gate) :
      coneStep n cs g = cs ++ [(g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => (w - n) :: cs.getD (w - n) [])] := rfl

  have coneFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
      (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
    induction gs generalizing cs with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp [coneStep_eq]
      omega

  have coneStep_getD_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) :
      (coneStep n cs g).getD cs.length [] =
        (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
          (fun w => (w - n) :: cs.getD (w - n) []) := by
    simp [coneStep_eq, List.getD_eq_getElem?_getD]

  have coneStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
      (coneStep n cs g).getD m [] = cs.getD m [] := by
    simp [coneStep_eq, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]

  have coneFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
      (hk : k < cs.length) :
      (gs.foldl (coneStep n) cs).getD k [] = cs.getD k [] := by
    induction gs generalizing cs with
    | nil => rfl
    | cons g gs ih =>
      simp only [List.foldl_cons]
      rw [ih (coneStep n cs g) (by simp [coneStep_eq]; omega)]
      exact coneStep_getD_lt n cs g k hk

  have inCone_iff (n : ℕ) (C : Circuit) (i k : ℕ) (hk : k < C.gates.length) :
      InCone n C i k ↔ ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧
        (i = w - n ∨ InCone n C i (w - n)) := by
    obtain ⟨pre, post, gk, hgs, hpre_len, hgk⟩ := split_gates C.gates k hk
    have hga : gateAt C k = gk := by rw [gateAt_eq C k hk]; exact hgk
    rw [hga]
    have hc : cones n C = post.foldl (coneStep n) (coneStep n (pre.foldl (coneStep n) []) gk) := by
      change C.gates.foldl (coneStep n) [] = _
      rw [hgs, List.foldl_append, List.foldl_cons]
    have hl0 : (pre.foldl (coneStep n) []).length = k := by
      rw [coneFold_length]; simp [hpre_len]
    have hl1 : (coneStep n (pre.foldl (coneStep n) []) gk).length = k + 1 := by
      simp [coneStep_eq, hl0]
    have h1 : (cones n C).getD k [] =
        (gk.inputs.filter (fun w => decide (n ≤ w ∧ w < n + k))).flatMap
          (fun w => (w - n) :: (pre.foldl (coneStep n) []).getD (w - n) []) := by
      rw [hc, coneFold_getD_lt n post _ k (by omega)]
      have h := coneStep_getD_last n (pre.foldl (coneStep n) []) gk
      rw [hl0] at h
      exact h
    have h2 : ∀ m, m < k → (cones n C).getD m [] = (pre.foldl (coneStep n) []).getD m [] := by
      intro m hm
      rw [hc, coneFold_getD_lt n post _ m (by omega)]
      exact coneStep_getD_lt n _ gk m (by omega)
    change i ∈ (cones n C).getD k [] ↔ _
    rw [h1]
    simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_cons]
    constructor
    · rintro ⟨w, ⟨hw, hn, hlt⟩, h⟩
      refine ⟨w, hw, hn, hlt, ?_⟩
      rcases h with h | h
      · exact Or.inl h
      · right
        change i ∈ (cones n C).getD (w - n) []
        rw [h2 (w - n) (by omega)]
        exact h
    · rintro ⟨w, hw, hn, hlt, h⟩
      refine ⟨w, ⟨hw, hn, hlt⟩, ?_⟩
      rcases h with h | h
      · exact Or.inl h
      · right
        rw [← h2 (w - n) (by omega)]
        exact h


  let hL : List (ℕ × ℕ) := [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (7 : ℕ)), ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))]
  have noLoop : ∀ a : Fin 14, (a.1, a.1) ∉ hL := by
    dsimp only [hL]
    decide +kernel
  let newG (C : Circuit) (o : ℕ) : List Gate :=
    C.gates.mapIdx (fun j g => if j = o ∨ InCone 14 C j o then g else ⟨GateOp.or, []⟩)

  have newG_len (C : Circuit) (o : ℕ) : (newG C o).length = C.gates.length := by
    simp [newG]

  have newG_get (C : Circuit) (o i : ℕ) (g : Gate) (hg : C.gates[i]? = some g) :
      (newG C o)[i]? = some (if i = o ∨ InCone 14 C i o then g else ⟨GateOp.or, []⟩) := by
    simp [newG, List.getElem?_mapIdx, hg]

  have newG_inv (C : Circuit) (o i : ℕ) (g' : Gate) (hg : (newG C o)[i]? = some g') :
      ∃ g, C.gates[i]? = some g ∧
        g' = if i = o ∨ InCone 14 C i o then g else ⟨GateOp.or, []⟩ := by
    have hi : i < C.gates.length := by
      have := (List.getElem?_eq_some_iff.1 hg).1
      rw [newG_len] at this
      exact this
    refine ⟨C.gates[i], List.getElem?_eq_getElem hi, ?_⟩
    have h2 := newG_get C o i C.gates[i] (List.getElem?_eq_getElem hi)
    rw [hg] at h2
    exact Option.some.inj h2

  have inCone_trans (C : Circuit) (i j : ℕ) (hij : InCone 14 C i j) :
      ∀ m, m < C.gates.length → InCone 14 C j m → InCone 14 C i m := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro hm hjm
      obtain ⟨w, hw, h1, h2, h3⟩ := (inCone_iff 14 C j m hm).1 hjm
      refine (inCone_iff 14 C i m hm).2 ⟨w, hw, h1, h2, Or.inr ?_⟩
      rcases h3 with h3 | h3
      · rw [← h3]; exact hij
      · exact ih (w - 14) (by omega) (by omega) h3

  have gate_some (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
      C.gates[j]? = some (gateAt C j) := by
    rw [gateAt_eq C j hj]; exact List.getElem?_eq_getElem hj

  have same_val (C : Circuit) (hRB : ReadsBack 14 C) (o : ℕ) (ho : o < C.gates.length)
      (x : List Bool) (hx : x.length = 14) :
      ∀ j, j < C.gates.length → (j = o ∨ InCone 14 C j o) →
        V (newG C o) x (14 + j) = V C.gates x (14 + j) := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro hj hk
      have hg := gate_some C j hj
      have hr := hRB j hj
      have hg' : (newG C o)[j]? = some (gateAt C j) := by
        rw [newG_get C o j _ hg, ite_eq_left_of_eq_true _ _ (eq_true hk)]
      rw [gate_val_aux (newG C o) x hx j _ hg' hr, gate_val_aux C.gates x hx j _ hg hr]
      congr 1
      apply List.map_congr_left
      intro w hw
      have hwlt := hr w hw
      by_cases h14 : w < 14
      · exact V_in _ _ x w (by omega)
      · have hw' : w = 14 + (w - 14) := by omega
        have hc : InCone 14 C (w - 14) j :=
          (inCone_iff 14 C _ j hj).2 ⟨w, hw, by omega, hwlt, Or.inl rfl⟩
        rw [hw']
        refine ih (w - 14) (by omega) (by omega) (Or.inr ?_)
        rcases hk with hk | hk
        · rw [← hk]; exact hc
        · exact inCone_trans C _ j hc o ho hk


  have edge_code : ∀ u v : Fin 14, (u.val, v.val) ∈ hL ↔ 14 * u.val + v.val ∈
      ([7,8,10,21,23,27,36,40,41,49,53,54,66,67,69,79,80,82,92,93,95] : List ℕ) := by
    dsimp only [hL]
    decide +kernel


  have output_gate (C : Circuit)
      (hf : ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔
        ∃ u v : Fin 14, (u.val, v.val) ∈ hL ∧ x u = true ∧ x v = true) :
      ∃ o, o < C.gates.length ∧ C.output = 14 + o := by
    by_cases h1 : C.output < 14
    · exfalso
      have h := (hf (fun z => decide (z.val = C.output))).1 (by
        change V C.gates (List.ofFn (fun z : Fin 14 => decide (z.val = C.output))) C.output = true
        unfold V
        rw [getD_wF _ _ _ (by simpa using h1), getD_ofFn 14 _ _ _ h1]
        simp)
      obtain ⟨u, v, huv, hu, hv⟩ := h
      have hu' : u.val = C.output := by simpa using hu
      have hv' : v.val = C.output := by simpa using hv
      have heq : u = v := Fin.ext (hu'.trans hv'.symm)
      subst v
      exact noLoop u huv
    · by_cases h2 : C.output < 14 + C.gates.length
      · exact ⟨C.output - 14, by omega, by omega⟩
      · exfalso
        have h := (hf (fun _ => true)).2 ⟨0, 7, by decide, rfl, rfl⟩
        change V C.gates (List.ofFn (fun _ : Fin 14 => true)) C.output = true at h
        rw [V_out _ _ _ (by simpa using Nat.le_of_not_gt h2)] at h
        exact Bool.false_ne_true h

  have blocked_and (C : Circuit) (hmono : Monotone2 C) (hback : ReadsBack 14 C)
      (x : List Bool) (hx : x.length = 14) (i : ℕ) (hi : V C.gates x (14 + i) = true) :
      ∀ j, j < C.gates.length → InCone 14 C i j → V C.gates x (14 + j) = false →
        ∃ k, (gateAt C k).op = .and ∧ InCone 14 C i k ∧ (k = j ∨ InCone 14 C k j) ∧
          V C.gates x (14 + k) = false := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro hj hc hjFalse
      have hsome := gate_some C j hj
      rcases (hmono _ (List.mem_of_getElem? hsome)).1 with hand | hor
      · exact ⟨j, hand, hc, Or.inl rfl, hjFalse⟩
      · obtain ⟨w, hw, hl, hr, hstep⟩ := (inCone_iff 14 C i j hj).1 hc
        have hwEq : w = 14 + (w - 14) := by omega
        have hwFalse : V C.gates x (14 + (w - 14)) = false := by
          cases hwv : V C.gates x (14 + (w - 14))
          · rfl
          · have hjTrue := (orN C.gates x hx j _ hsome (hback j hj) hor).2
              ⟨w, hw, by rwa [hwEq]⟩
            rw [hjTrue] at hjFalse
            contradiction
        rcases hstep with heq | hstep
        · rw [← heq, hi] at hwFalse
          contradiction
        · obtain ⟨k, hk, hik, hkj, hkFalse⟩ := ih (w - 14) (by omega) (by omega) hstep hwFalse
          exact ⟨k, hk, hik, Or.inr ((inCone_iff 14 C k j hj).2 ⟨w, hw, hl, hr, hkj⟩), hkFalse⟩

  classical
  intro C hmono hback _ hfun
  obtain ⟨o, ho, hout⟩ := output_gate C hfun
  have hcode := fun x : Fin 14 → Bool => hfun x
  change (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔
    ∃ u v : Fin 14, (u.val, v.val) ∈ hL ∧ x u = true ∧ x v = true) at hcode
  simp_rw [edge_code] at hcode
  by_cases hclean : ∀ i < C.gates.length, (i = o ∨ InCone 14 C i o) →
      (gateAt C i).op = .and → ∀ u v : Fin 14,
        gateVal 14 C i (pairInput u v) = true → C.eval (List.ofFn (pairInput u v)) = true
  · let D : Circuit := ⟨newG C o, C.output⟩
    have hsize : D.size = C.size := newG_len C o
    have hn j (hj : j < D.gates.length) : j < C.gates.length := by
      exact lt_of_lt_of_eq hj hsize
    have heval (x : Fin 14 → Bool) : D.eval (List.ofFn x) = C.eval (List.ofFn x) := by
      change V (newG C o) (List.ofFn x) C.output = V C.gates (List.ofFn x) C.output
      rw [hout]
      exact same_val C hback o ho _ (by simp) o ho (Or.inl rfl)
    have hdMono : Monotone2 D := by
      intro g hg
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hg
      obtain ⟨g0, hg0, he⟩ := newG_inv C o i _ (List.getElem?_eq_getElem hi)
      rw [he]
      have hm := hmono g0 (List.mem_of_getElem? hg0)
      split_ifs
      · exact hm
      · simp
    have hdClean : ∀ i < D.gates.length, (gateAt D i).op = .and → ∀ u v : Fin 14,
        gateVal 14 D i (pairInput u v) = true → D.eval (List.ofFn (pairInput u v)) = true := by
      intro i hi hand u v hv
      have hAt := newG_get C o i (gateAt C i) (gate_some C i (hn i hi))
      change D.gates[i]? = _ at hAt
      rw [gate_some D i hi] at hAt
      have hAt' := Option.some.inj hAt
      split_ifs at hAt' with hCone
      · rw [hAt'] at hand
        have hSame := same_val C hback o ho (List.ofFn (pairInput u v)) (by simp) i (hn i hi) hCone
        change gateVal 14 D i (pairInput u v) = gateVal 14 C i (pairInput u v) at hSame
        rw [hSame] at hv
        rw [heval]
        exact hclean i (hn i hi) hCone hand u v hv
      · rw [hAt'] at hand
        contradiction
    exact hsize ▸ clean D hdMono hdClean (fun x => by rw [heval]; exact hcode x)
  · push Not at hclean
    obtain ⟨i, hi, hic, hand, u, v, htrue, hfalse⟩ := hclean
    have hfalse := Bool.eq_false_of_not_eq_true hfalse
    have hc : InCone 14 C i o := by
      rcases hic with heq | h
      · exfalso
        have h : C.eval (List.ofFn (pairInput u v)) = true := by
          change V C.gates (List.ofFn (pairInput u v)) C.output = true
          rw [hout, ← heq]
          exact htrue
        rw [hfalse] at h
        contradiction
      · exact h
    have hoFalse : V C.gates (List.ofFn (pairInput u v)) (14 + o) = false := by
      rw [← hout]
      exact hfalse
    obtain ⟨j, hOp, hIj, hOut, hFalseJ⟩ := blocked_and C hmono hback
      (List.ofFn (pairInput u v)) (by simp) i htrue o ho hc hoFalse
    have hOut' : j = C.output - 14 ∨ InCone 14 C j (C.output - 14) := by
      simpa [hout] using hOut
    exact blocked C hmono hback ⟨i, j, u, v, hand, hOp, hIj, hOut', htrue, hFalseJ, hfalse⟩ hcode
