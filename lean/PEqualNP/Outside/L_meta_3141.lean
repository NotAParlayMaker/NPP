import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3141

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def gval (g : Gate) (w : List Bool) : Bool := g.op.eval (g.inputs.map fun i => w.getD i false)

def step (w : List Bool) (g : Gate) : List Bool := w ++ [gval g w]

def wf (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = wf C.gates x := rfl

lemma wf_cons (g : Gate) (gs : List Gate) (w : List Bool) : wf (g :: gs) w = wf gs (step w g) := rfl

lemma wf_append (gs hs : List Gate) (w : List Bool) : wf (gs ++ hs) w = wf hs (wf gs w) := by
  simp [wf, List.foldl_append]

lemma wf_length (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih => intro w; rw [wf_cons, ih]; simp [step]; omega

lemma getD_big (w : List Bool) (i : ℕ) (h : w.length ≤ i) : w.getD i false = false :=
  List.getD_eq_default _ _ h

lemma getD_app (w v : List Bool) (i : ℕ) (h : i < w.length) : (w ++ v).getD i false = w.getD i false :=
  List.getD_append _ _ _ _ h

lemma getD_last (w : List Bool) (a : Bool) : (w ++ [a]).getD w.length false = a := by
  simp [List.getD_eq_getElem?_getD]

lemma wf_prefix (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    rw [wf_cons, ih _ _ (by simp [step]; omega)]
    exact getD_app _ _ _ hi

lemma take_succ_wf (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    wf (gs.take (j + 1)) w = step (wf (gs.take j) w) gs[j] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some, wf_append]
  rfl

lemma wf_take_prefix (gs : List Gate) (w : List Bool) (j i : ℕ) (hj : j ≤ gs.length)
    (hi : i < w.length + j) : (wf gs w).getD i false = (wf (gs.take j) w).getD i false := by
  conv_lhs => rw [← List.take_append_drop j gs, wf_append]
  apply wf_prefix
  rw [wf_length, List.length_take]; omega

lemma wire_gate (gs : List Gate) (x : List Bool) (j : ℕ) (hj : j < gs.length) :
    (wf gs x).getD (x.length + j) false = gval gs[j] (wf (gs.take j) x) := by
  rw [wf_take_prefix gs x (j + 1) (x.length + j) (by omega) (by omega), take_succ_wf _ _ _ hj,
    step]
  have : (wf (List.take j gs) x).length = x.length + j := by
    rw [wf_length, List.length_take]; omega
  rw [← this, getD_last]

def mapG (φ : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map φ⟩

lemma sim (φ : ℕ → ℕ) (gs : List Gate) : ∀ (w w' : List Bool),
    (∀ m, w'.getD (φ m) false = w.getD m false) →
    (∀ k, (∀ m, m < w.length + k → φ m < w'.length + k) ∧ φ (w.length + k) = w'.length + k ∧
      (∀ m, w.length + k < m → w'.length + k < φ m)) →
    ∀ m, (wf (gs.map (mapG φ)) w').getD (φ m) false = (wf gs w).getD m false := by
  induction gs with
  | nil => intro w w' hR _ m; exact hR m
  | cons g gs ih =>
    intro w w' hR hφ
    simp only [List.map_cons, wf_cons]
    apply ih
    · intro m
      have hv : gval (mapG φ g) w' = gval g w := by
        simp only [gval, mapG, List.map_map]
        congr 1
        apply List.map_congr_left
        intro i _
        exact hR i
      obtain ⟨h1, h2, h3⟩ := hφ 0
      simp only [add_zero] at h1 h2 h3
      rcases lt_trichotomy m w.length with hm | hm | hm
      · rw [step, step, getD_app _ _ _ (h1 m hm), getD_app _ _ _ hm]; exact hR m
      · subst hm; rw [h2, step, step, getD_last, getD_last, hv]
      · have h4 := h3 m hm
        rw [step, step, getD_big _ _ (by simp; omega), getD_big _ _ (by simp; omega)]
    · intro k
      obtain ⟨h1, h2, h3⟩ := hφ (k + 1)
      simp only [step, List.length_append, List.length_singleton]
      refine ⟨fun m hm => by have := h1 m (by omega); omega, by rw [show w.length + 1 + k = w.length + (k + 1) by omega, h2]; omega, fun m hm => by have := h3 m (by omega); omega⟩

def mapC (φ : ℕ → ℕ) (C : Circuit) : Circuit := ⟨C.gates.map (mapG φ), φ C.output⟩

def phi (n j r m : ℕ) : ℕ := if m < n + j then m else if m = n + j then r else m - 1

def rem (C : Circuit) (n j r : ℕ) : Circuit :=
  ⟨C.gates.take j ++ (C.gates.drop (j + 1)).map (mapG (phi n j r)), phi n j r C.output⟩

lemma rem_rel (C : Circuit) (n j r : ℕ) (x : List Bool) (hx : x.length = n)
    (hj : j < C.gates.length) (hr : r < n + j)
    (hv : (C.wires x).getD (n + j) false = (C.wires x).getD r false) :
    ∀ m, ((rem C n j r).wires x).getD (phi n j r m) false = (C.wires x).getD m false := by
  set W := wf (C.gates.take j) x with hW
  have hWl : W.length = n + j := by rw [hW, wf_length, List.length_take]; omega
  have hsplit : C.gates = C.gates.take j ++ (C.gates[j] :: C.gates.drop (j + 1)) := by
    rw [← List.drop_eq_getElem_cons hj, List.take_append_drop]
  have hval : gval C.gates[j] W = W.getD r false := by
    have e1 := wire_gate C.gates x j hj
    have e2 := wf_take_prefix C.gates x j r hj.le (by omega)
    rw [← wires_eq, hx] at e1
    rw [← wires_eq] at e2
    rw [← e1, hv, e2]
  have hC : C.wires x = wf (C.gates.drop (j + 1)) (step W C.gates[j]) := by
    rw [wires_eq]
    conv_lhs => rw [hsplit]
    rw [wf_append, wf_cons]
  have hD : (rem C n j r).wires x = wf ((C.gates.drop (j + 1)).map (mapG (phi n j r))) W := by
    rw [wires_eq]; simp only [rem]; rw [wf_append]
  intro m
  rw [hC, hD]
  apply sim
  · intro m
    simp only [step]
    unfold phi
    split_ifs with h1 h2
    · rw [getD_app _ _ _ (by omega)]
    · subst h2; rw [← hWl, getD_last, hval]
    · rw [getD_big _ _ (by omega), getD_big _ _ (by simp; omega)]
  · intro k
    simp only [step, List.length_append, List.length_singleton, hWl]
    refine ⟨fun m hm => ?_, ?_, fun m hm => ?_⟩ <;> unfold phi <;> split_ifs <;> omega

lemma rem_len (C : Circuit) (n j r : ℕ) (hj : j < C.gates.length) :
    (rem C n j r).gates.length = C.gates.length - 1 := by
  simp [rem, List.length_take, List.length_drop]; omega

lemma rem_eval (C : Circuit) (n j r : ℕ) (x : List Bool) (hx : x.length = n)
    (hj : j < C.gates.length) (hr : r < n + j)
    (hv : (C.wires x).getD (n + j) false = (C.wires x).getD r false) :
    (rem C n j r).eval x = C.eval x := by
  have := rem_rel C n j r x hx hj hr hv C.output
  simpa [Circuit.eval, rem] using this

lemma fan_mapC (φ : ℕ → ℕ) (C : Circuit) (hF : FanInTwo C) : FanInTwo (mapC φ C) := by
  intro g hg
  obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
  exact ⟨(hF g0 hg0).1, by simpa [mapG] using (hF g0 hg0).2⟩

lemma fan_rem (C : Circuit) (n j r : ℕ) (hF : FanInTwo C) : FanInTwo (rem C n j r) := by
  intro g hg
  rcases List.mem_append.1 hg with h | h
  · exact hF g (List.mem_of_mem_take h)
  · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 h
    have := hF g0 (List.mem_of_mem_drop hg0)
    exact ⟨this.1, by simpa [mapG] using this.2⟩

lemma getD_last' (w : List Bool) (a : Bool) (i : ℕ) (h : w.length = i) :
    (w ++ [a]).getD i false = a := by
  subst h; exact getD_last w a

def effReads (g : Gate) (c : ℕ) : Prop :=
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ c ∈ g.inputs) ∨
    (g.op = GateOp.not ∧ g.inputs.head? = some c)

lemma gval_congr (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (A : ℕ → Prop) (hA : ∀ c, A c → ¬ effReads g c) (w w' : List Bool)
    (hw : ∀ m, ¬ A m → w.getD m false = w'.getD m false) : gval g w = gval g w' := by
  obtain ⟨op, ins⟩ := g
  simp only at hop
  rcases hop with h | h | h
  · subst h
    simp only [gval]
    congr 1
    apply List.map_congr_left
    intro i hi
    exact hw i (fun hAi => hA i hAi (Or.inl ⟨Or.inl rfl, hi⟩))
  · subst h
    simp only [gval]
    congr 1
    apply List.map_congr_left
    intro i hi
    exact hw i (fun hAi => hA i hAi (Or.inl ⟨Or.inr rfl, hi⟩))
  · subst h
    cases ins with
    | nil => rfl
    | cons a t =>
      simp only [gval, List.map_cons, GateOp.eval, List.headD_cons]
      rw [hw a (fun hAa => hA a hAa (Or.inr ⟨rfl, rfl⟩))]

lemma agree (gs : List Gate)
    (hop : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (A : ℕ → Prop) (u v : List Bool) (hl : u.length = v.length)
    (hin : ∀ m, ¬ A m → u.getD m false = v.getD m false)
    (hg : ∀ j (hj : j < gs.length), ¬ A (u.length + j) →
      (∀ c, A c → ¬ effReads gs[j] c) ∨
        (wf gs u).getD (u.length + j) false = (wf gs v).getD (u.length + j) false) :
    ∀ m, ¬ A m → (wf gs u).getD m false = (wf gs v).getD m false := by
  have key : ∀ j, j ≤ gs.length → ∀ m, ¬ A m →
      (wf (gs.take j) u).getD m false = (wf (gs.take j) v).getD m false := by
    intro j
    induction j with
    | zero => intro _ m hm; simpa [wf] using hin m hm
    | succ j ih =>
      intro hj m hm
      have hj' : j < gs.length := by omega
      have lu : (wf (gs.take j) u).length = u.length + j := by
        rw [wf_length, List.length_take]; omega
      have lv : (wf (gs.take j) v).length = u.length + j := by
        rw [wf_length, List.length_take, ← hl]; omega
      rw [take_succ_wf _ _ _ hj', take_succ_wf _ _ _ hj', step, step]
      rcases lt_trichotomy m (u.length + j) with h | h | h
      · rw [getD_app _ _ _ (by omega), getD_app _ _ _ (by omega)]; exact ih hj'.le m hm
      · subst h
        rw [getD_last' _ _ _ lu, getD_last' _ _ _ lv]
        rcases hg j hj' hm with h1 | h1
        · exact gval_congr _ (hop _ (List.getElem_mem hj')) A h1 _ _ (ih hj'.le)
        · have e1 := wire_gate gs u j hj'
          have e2 := wire_gate gs v j hj'
          rw [← hl] at e2
          rw [← e1, ← e2]; exact h1
      · rw [getD_big _ _ (by simp; omega), getD_big _ _ (by simp; omega)]
  intro m hm
  have := key gs.length le_rfl m hm
  rwa [List.take_length] at this

lemma triv (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (hlen : g.inputs.length ≤ 2) (c : ℕ) (β : Bool) (hc : effReads g c) :
    ∃ r, (r = 9 ∨ r = 10 ∨ r ∈ g.inputs) ∧ ∀ w : List Bool, w.getD 9 false = true →
      w.getD 10 false = false → w.getD c false = β → gval g w = w.getD r false := by
  obtain ⟨op, ins⟩ := g
  simp only at hop hlen
  unfold effReads at hc
  simp only at hc
  match ins, hlen with
  | [], _ => simp at hc
  | [a], _ =>
    rcases hop with h | h | h <;> subst h
    · exact ⟨a, by simp, fun w _ _ _ => by simp [gval, GateOp.eval]⟩
    · exact ⟨a, by simp, fun w _ _ _ => by simp [gval, GateOp.eval]⟩
    · have hca : c = a := by simpa [eq_comm] using hc
      subst hca
      cases β
      · refine ⟨9, by simp, fun w h9 h10 hcw => ?_⟩
        rw [List.getD_eq_getElem?_getD] at h9 h10 hcw
        simp [gval, GateOp.eval, hcw, h9]
      · refine ⟨10, by simp, fun w h9 h10 hcw => ?_⟩
        rw [List.getD_eq_getElem?_getD] at h9 h10 hcw
        simp [gval, GateOp.eval, hcw, h10]
  | [a, b], _ =>
    rcases hop with h | h | h <;> subst h
    · have hc' : c = a ∨ c = b := by simpa using hc
      cases β
      · refine ⟨10, by simp, fun w h9 h10 hcw => ?_⟩
        rw [List.getD_eq_getElem?_getD] at h9 h10 hcw
        rcases hc' with rfl | rfl <;> simp [gval, GateOp.eval, hcw, h10]
      · rcases hc' with rfl | rfl
        · refine ⟨b, by simp, fun w h9 h10 hcw => ?_⟩
          rw [List.getD_eq_getElem?_getD] at h9 h10 hcw
          simp [gval, GateOp.eval, hcw]
        · refine ⟨a, by simp, fun w h9 h10 hcw => ?_⟩
          rw [List.getD_eq_getElem?_getD] at h9 h10 hcw
          simp [gval, GateOp.eval, hcw]
    · have hc' : c = a ∨ c = b := by simpa using hc
      cases β
      · rcases hc' with rfl | rfl
        · refine ⟨b, by simp, fun w h9 h10 hcw => ?_⟩
          rw [List.getD_eq_getElem?_getD] at h9 h10 hcw
          simp [gval, GateOp.eval, hcw]
        · refine ⟨a, by simp, fun w h9 h10 hcw => ?_⟩
          rw [List.getD_eq_getElem?_getD] at h9 h10 hcw
          simp [gval, GateOp.eval, hcw]
      · refine ⟨9, by simp, fun w h9 h10 hcw => ?_⟩
        rw [List.getD_eq_getElem?_getD] at h9 h10 hcw
        rcases hc' with rfl | rfl <;> simp [gval, GateOp.eval, hcw, h9]
    · have hca : c = a := by simpa [eq_comm] using hc
      subst hca
      cases β
      · refine ⟨9, by simp, fun w h9 h10 hcw => ?_⟩
        rw [List.getD_eq_getElem?_getD] at h9 h10 hcw
        simp [gval, GateOp.eval, hcw, h9]
      · refine ⟨10, by simp, fun w h9 h10 hcw => ?_⟩
        rw [List.getD_eq_getElem?_getD] at h9 h10 hcw
        simp [gval, GateOp.eval, hcw, h10]
  | _ :: _ :: _ :: _, h => simp at h

def inX (y : Fin 8 → Bool) (k : Fin 8) : List Bool := List.ofFn y ++ [!y k, true, false]

def inZ (y : Fin 8 → Bool) : List Bool := List.ofFn (Fin.insertNth (4 : Fin 9) false y)

lemma inX_eq (y : Fin 8 → Bool) (k : Fin 8) :
    inX y k = [y 0, y 1, y 2, y 3, y 4, y 5, y 6, y 7, !y k, true, false] := rfl

lemma inZ_eq (y : Fin 8 → Bool) :
    inZ y = [y 0, y 1, y 2, y 3, false, y 4, y 5, y 6, y 7] := rfl

lemma inX_len (y : Fin 8 → Bool) (k : Fin 8) : (inX y k).length = 11 := by simp [inX]

lemma inZ_len (y : Fin 8 → Bool) : (inZ y).length = 9 := by simp [inZ]

def sig (m : ℕ) : ℕ := if m < 4 then m else if m = 4 then 10 else if m < 9 then m - 1 else m + 2

lemma base_sig (y : Fin 8 → Bool) (k : Fin 8) :
    ∀ m, (inX y k).getD (sig m) false = (inZ y).getD m false := by
  intro m
  rw [inX_eq, inZ_eq]
  rcases (show m < 9 ∨ 9 ≤ m by omega) with h | h
  · interval_cases m <;> simp [sig]
  · rw [getD_big _ _ (by simp; unfold sig; split_ifs <;> omega), getD_big _ _ (by simp; omega)]

lemma relD (C : Circuit) (y : Fin 8 → Bool) (k : Fin 8) :
    ∀ m, ((mapC sig C).wires (inX y k)).getD (sig m) false = (C.wires (inZ y)).getD m false := by
  intro m
  rw [wires_eq, wires_eq]
  apply sim sig C.gates (inZ y) (inX y k) (base_sig y k)
  intro k'
  rw [inZ_len, inX_len]
  refine ⟨fun m hm => ?_, ?_, fun m hm => ?_⟩ <;> unfold sig <;> split_ifs <;> omega

lemma gate1 (C : Circuit) (h9 : ∀ y : Fin 8 → Bool, (C.wires (inZ y)).getD 9 false = y 0)
    (g1 : Gate) (h1lt : 1 < C.gates.length) (hg1e : C.gates[1] = g1)
    (hg1op : g1.op = GateOp.not) :
    ∃ (k : Fin 8) (r1 : ℕ), (r1 = 8 ∨ r1 = 9) ∧
      ∀ y, (C.wires (inZ y)).getD 10 false = (inX y k).getD r1 false := by
  have hv : ∀ y, (C.wires (inZ y)).getD 10 false =
      !((g1.inputs.map fun i => (wf (C.gates.take 1) (inZ y)).getD i false).headD false) := by
    intro y
    have := wire_gate C.gates (inZ y) 1 h1lt
    rw [inZ_len, hg1e] at this
    rw [wires_eq, this, gval, hg1op, GateOp.eval]
  have hW9 : ∀ y, (wf (C.gates.take 1) (inZ y)).getD 9 false = y 0 := by
    intro y
    rw [← wf_take_prefix C.gates (inZ y) 1 9 h1lt.le (by rw [inZ_len]; omega), ← wires_eq]
    exact h9 y
  have hWlen : ∀ y, (wf (C.gates.take 1) (inZ y)).length = 10 := by
    intro y; rw [wf_length, inZ_len, List.length_take]; omega
  have hWlow : ∀ y a, a < 9 → (wf (C.gates.take 1) (inZ y)).getD a false = (inZ y).getD a false := by
    intro y a ha; exact wf_prefix _ _ _ (by rw [inZ_len]; omega)
  obtain ⟨op, ins⟩ := g1
  simp only at hv hg1op
  cases ins with
  | nil =>
    refine ⟨0, 9, Or.inr rfl, fun y => ?_⟩
    rw [hv y, inX_eq]; simp
  | cons a t =>
    simp only [List.map_cons, List.headD_cons] at hv
    by_cases h4 : a = 4
    · subst h4
      refine ⟨0, 9, Or.inr rfl, fun y => ?_⟩
      rw [hv y, hWlow y 4 (by omega), inZ_eq, inX_eq]; simp
    by_cases h9a : a = 9
    · subst h9a
      refine ⟨0, 8, Or.inl rfl, fun y => ?_⟩
      rw [hv y, hW9 y, inX_eq]; simp
    by_cases hbig : 10 ≤ a
    · refine ⟨0, 9, Or.inr rfl, fun y => ?_⟩
      rw [hv y, getD_big _ _ (by rw [hWlen y]; omega), inX_eq]; simp
    have ha : a < 9 := by omega
    refine ⟨⟨sig a, by unfold sig; split_ifs <;> omega⟩, 8, Or.inl rfl, fun y => ?_⟩
    rw [hv y, hWlow y a ha]
    interval_cases a <;> first | exact absurd rfl h4 | rfl

lemma eff_map (g : Gate) (c : ℕ) (h : effReads g c) : effReads (mapG sig g) (sig c) := by
  unfold effReads at h ⊢
  simp only [mapG]
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h1, List.mem_map_of_mem h2⟩
  · exact Or.inr ⟨h1, by simp [List.head?_map, h2]⟩

lemma third (C : Circuit) (hF : FanInTwo C)
    (h9 : ∀ y : Fin 8 → Bool, (C.wires (inZ y)).getD 9 false = y 0)
    (g1 : Gate) (h1lt : 1 < C.gates.length) (hg1e : C.gates[1] = g1)
    (hg1op : g1.op = GateOp.not)
    (hsz : C.gates.length ≤ 15) (j : ℕ) (hj : j < C.gates.length) (h2j : 2 ≤ j)
    (c : ℕ) (hcj : c < 9 + j) (β : Bool) (hread : effReads C.gates[j] c)
    (hβ : ∀ y, (C.wires (inZ y)).getD c false = β) :
    ∃ (k : Fin 8) (C' : Circuit), FanInTwo C' ∧ C'.size ≤ 12 ∧
      ∀ y : Fin 8 → Bool, C'.eval (inX y k) = C.eval (inZ y) := by
  obtain ⟨k, r1, hr1, hk⟩ := gate1 C h9 g1 h1lt hg1e hg1op
  set D := mapC sig C with hDdef
  have hDl : D.gates.length = C.gates.length := by simp [hDdef, mapC]
  have hjD : j < D.gates.length := by omega
  have hDj : D.gates[j] = mapG sig C.gates[j] := by simp [hDdef, mapC]
  have hFj := hF C.gates[j] (List.getElem_mem hj)
  have hopj : C.gates[j].op = GateOp.and ∨ C.gates[j].op = GateOp.or ∨
      C.gates[j].op = GateOp.not := by simpa using hFj.1
  obtain ⟨r, -, hr⟩ := triv (mapG sig C.gates[j]) (by simpa [mapG] using hopj)
    (by simpa [mapG] using hFj.2) (sig c) β (eff_map _ _ hread)
  set r3 := if r < 11 + j then r else 10 with hr3def
  have hr3 : r3 < 11 + j := by rw [hr3def]; split_ifs <;> omega
  have hsc : sig c < 11 + j := by unfold sig; split_ifs <;> omega
  have hv3 : ∀ y, (D.wires (inX y k)).getD (11 + j) false = (D.wires (inX y k)).getD r3 false := by
    intro y
    set W := wf (D.gates.take j) (inX y k) with hW
    have hWl : W.length = 11 + j := by rw [hW, wf_length, inX_len, List.length_take]; omega
    have e1 := wire_gate D.gates (inX y k) j hjD
    rw [inX_len, ← wires_eq, hDj] at e1
    rw [e1]
    rw [← hDj]
    have a9 : W.getD 9 false = true := by
      rw [hW, wf_prefix _ _ _ (by rw [inX_len]; omega), inX_eq]; simp
    have a10 : W.getD 10 false = false := by
      rw [hW, wf_prefix _ _ _ (by rw [inX_len]; omega), inX_eq]; simp
    have ac : W.getD (sig c) false = β := by
      rw [hW, ← wf_take_prefix D.gates (inX y k) j (sig c) hjD.le (by rw [inX_len]; omega),
        ← wires_eq, hDdef, relD C y k c, hβ y]
    rw [hDj, hr W a9 a10 ac]
    rw [hr3def]
    split_ifs with hrl
    · rw [hW, ← wf_take_prefix D.gates (inX y k) j r hjD.le (by rw [inX_len]; omega), ← wires_eq]
    · rw [getD_big _ _ (by omega), wires_eq, wf_prefix _ _ _ (by rw [inX_len]; omega), inX_eq]
      simp
  set D1 := rem D 11 j r3 with hD1def
  have R1 : ∀ y m, (D1.wires (inX y k)).getD (phi 11 j r3 m) false = (D.wires (inX y k)).getD m false :=
    fun y => rem_rel D 11 j r3 (inX y k) (inX_len y k) hjD hr3 (hv3 y)
  have hD1l : D1.gates.length = C.gates.length - 1 := by rw [hD1def, rem_len _ _ _ _ hjD, hDl]
  have p12 : phi 11 j r3 12 = 12 := by unfold phi; split_ifs <;> omega
  have p11 : phi 11 j r3 11 = 11 := by unfold phi; split_ifs <;> omega
  have p0 : phi 11 j r3 0 = 0 := by unfold phi; split_ifs <;> omega
  have pr1 : phi 11 j r3 r1 = r1 := by unfold phi; split_ifs <;> omega
  have hv1 : ∀ y, (D1.wires (inX y k)).getD (11 + 1) false = (D1.wires (inX y k)).getD r1 false := by
    intro y
    rw [show 11 + 1 = 12 by rfl, ← p12, R1 y 12, ← pr1, R1 y r1]
    have e : (D.wires (inX y k)).getD 12 false = (C.wires (inZ y)).getD 10 false := by
      have := relD C y k 10
      rwa [show sig 10 = 12 by rfl] at this
    rw [e, hk y, wires_eq, wf_prefix _ _ _ (by rw [inX_len]; omega)]
  have h1D1 : 1 < D1.gates.length := by omega
  set D2 := rem D1 11 1 r1 with hD2def
  have R2 : ∀ y m, (D2.wires (inX y k)).getD (phi 11 1 r1 m) false = (D1.wires (inX y k)).getD m false :=
    fun y => rem_rel D1 11 1 r1 (inX y k) (inX_len y k) h1D1 (by omega) (hv1 y)
  have hD2l : D2.gates.length = C.gates.length - 2 := by
    rw [hD2def, rem_len _ _ _ _ h1D1, hD1l]; omega
  have q11 : phi 11 1 r1 11 = 11 := by unfold phi; split_ifs <;> omega
  have q0 : phi 11 1 r1 0 = 0 := by unfold phi; split_ifs <;> omega
  have hv0 : ∀ y, (D2.wires (inX y k)).getD (11 + 0) false = (D2.wires (inX y k)).getD 0 false := by
    intro y
    rw [show 11 + 0 = 11 by rfl, ← q11, R2 y 11, ← q0, R2 y 0, ← p11, R1 y 11, ← p0, R1 y 0]
    have e : (D.wires (inX y k)).getD 11 false = (C.wires (inZ y)).getD 9 false := by
      have := relD C y k 9
      rwa [show sig 9 = 11 by rfl] at this
    rw [e, h9 y, wires_eq, wf_prefix _ _ _ (by rw [inX_len]; omega), inX_eq]
    rfl
  have h0D2 : 0 < D2.gates.length := by omega
  set D3 := rem D2 11 0 0 with hD3def
  refine ⟨k, D3, ?_, ?_, fun y => ?_⟩
  · exact fan_rem _ _ _ _ (fan_rem _ _ _ _ (fan_rem _ _ _ _ (fan_mapC _ _ hF)))
  · show D3.gates.length ≤ 12
    rw [hD3def, rem_len _ _ _ _ h0D2, hD2l]; omega
  · rw [hD3def, rem_eval _ _ _ _ _ (inX_len y k) h0D2 (by omega) (hv0 y),
      hD2def, rem_eval _ _ _ _ _ (inX_len y k) h1D1 (by omega) (hv1 y),
      hD1def, rem_eval _ _ _ _ _ (inX_len y k) hjD hr3 (hv3 y)]
    have := relD C y k C.output
    simpa [Circuit.eval, hDdef, mapC] using this

lemma wire10 (C : Circuit) (g1 : Gate) (h1lt : 1 < C.gates.length) (hg1e : C.gates[1] = g1)
    (hg1op : g1.op = GateOp.not) (hh : g1.inputs.head? = some 4) :
    ∀ y, (C.wires (inZ y)).getD 10 false = true := by
  intro y
  have := wire_gate C.gates (inZ y) 1 h1lt
  rw [inZ_len, hg1e] at this
  rw [wires_eq, this, gval, hg1op, GateOp.eval]
  obtain ⟨op, ins⟩ := g1
  cases ins with
  | nil => simp at hh
  | cons a t =>
    simp only [List.head?_cons, Option.some.injEq] at hh
    subst hh
    simp only [List.map_cons, List.headD_cons]
    rw [wf_prefix _ _ _ (by rw [inZ_len]; omega), inZ_eq]
    rfl

lemma main (x1 : PEqualNP.CircuitLowerBounds.Circuit)
    (hF : PEqualNP.MetaComplexity.FanInTwo x1)
    (h9' : ∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false =
      (x3 (0 : Fin (9 : ℕ)) || x3 (4 : Fin (9 : ℕ))))
    (h1 : Option.map PEqualNP.CircuitLowerBounds.Gate.op x1.gates[(1 : ℕ)]? =
      Option.some PEqualNP.CircuitLowerBounds.GateOp.not)
    (hsz : x1.size ≤ (15 : ℕ))
    (hne : x1.eval [Bool.true, Bool.false, Bool.false, Bool.false, Bool.true, Bool.false,
      Bool.false, Bool.false, Bool.false] ≠ x1.eval [Bool.true, Bool.false, Bool.false,
      Bool.false, Bool.false, Bool.false, Bool.false, Bool.false, Bool.false]) :
    ∃ (k : Fin 8) (C' : Circuit), FanInTwo C' ∧ C'.size ≤ 12 ∧
      ∀ y : Fin 8 → Bool, C'.eval (inX y k) = x1.eval (inZ y) := by
  set C := x1 with hCdef
  have hsz' : C.gates.length ≤ 15 := hsz
  have hop : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not :=
    fun g hg => by simpa using (hF g hg).1
  have h9 : ∀ y : Fin 8 → Bool, (C.wires (inZ y)).getD 9 false = y 0 := by
    intro y
    have := h9' (Fin.insertNth (4 : Fin 9) false y)
    have e0 : (Fin.insertNth (4 : Fin 9) false y : Fin 9 → Bool) 0 = y 0 := rfl
    have e4 : (Fin.insertNth (4 : Fin 9) false y : Fin 9 → Bool) 4 = false := rfl
    rw [e0, e4, Bool.or_false] at this
    exact this
  obtain ⟨g1, hq, hg1op⟩ : ∃ g1, C.gates[1]? = some g1 ∧ g1.op = GateOp.not := by
    cases hq : C.gates[1]? with
    | none => rw [hq] at h1; cases h1
    | some g1 => rw [hq] at h1; exact ⟨g1, rfl, Option.some.inj h1⟩
  have h1lt : 1 < C.gates.length := by
    by_contra h
    rw [List.getElem?_eq_none (by omega)] at hq
    cases hq
  have hg1e : C.gates[1] = g1 := by
    rw [List.getElem?_eq_getElem h1lt] at hq; exact Option.some.inj hq
  set u : List Bool := [true, false, false, false, true, false, false, false, false] with hu
  set v : List Bool := [true, false, false, false, false, false, false, false, false] with hv
  have hu9 : (wf C.gates u).getD 9 false = true := by
    have := h9' ![true, false, false, false, true, false, false, false, false]
    have e : List.ofFn ![true, false, false, false, true, false, false, false, false] = u := rfl
    rw [e] at this
    rw [← wires_eq, this]; rfl
  have hv9 : (wf C.gates v).getD 9 false = true := by
    have := h9' ![true, false, false, false, false, false, false, false, false]
    have e : List.ofFn ![true, false, false, false, false, false, false, false, false] = v := rfl
    rw [e] at this
    rw [← wires_eq, this]; rfl
  have hne' : (wf C.gates u).getD C.output false ≠ (wf C.gates v).getD C.output false := hne
  have hul : u.length = 9 := rfl
  by_cases hA : ∃ j, ∃ hj : j < C.gates.length, 2 ≤ j ∧ effReads C.gates[j] 4
  · obtain ⟨j, hj, h2j, hread⟩ := hA
    exact third C hF h9 g1 h1lt hg1e hg1op hsz' j hj h2j 4 (by omega) false hread (fun y => by
      rw [wires_eq, wf_prefix _ _ _ (by rw [inZ_len]; omega), inZ_eq]; rfl)
  have hA' : ∀ j (hj : j < C.gates.length), 2 ≤ j → ¬ effReads C.gates[j] 4 :=
    fun j hj h2j hr => hA ⟨j, hj, h2j, hr⟩
  by_cases hB : effReads g1 4
  · have hh : g1.inputs.head? = some 4 := by
      rcases hB with ⟨h, _⟩ | ⟨_, h⟩
      · rw [hg1op] at h; rcases h with h | h <;> cases h
      · exact h
    have h10 := wire10 C g1 h1lt hg1e hg1op hh
    by_cases hC : ∃ j, ∃ hj : j < C.gates.length, 2 ≤ j ∧ effReads C.gates[j] 10
    · obtain ⟨j, hj, h2j, hread⟩ := hC
      exact third C hF h9 g1 h1lt hg1e hg1op hsz' j hj h2j 10 (by omega) true hread h10
    have hC' : ∀ j (hj : j < C.gates.length), 2 ≤ j → ¬ effReads C.gates[j] 10 :=
      fun j hj h2j hr => hC ⟨j, hj, h2j, hr⟩
    have hag := agree C.gates hop (fun m => m = 4 ∨ m = 10) u v rfl
      (by
        intro m hm
        rcases (show m < 9 ∨ 9 ≤ m by omega) with h | h
        · interval_cases m <;> simp_all
        · rw [getD_big _ _ (by rw [hul]; omega), getD_big _ _ (by rw [hv]; simp; omega)])
      (by
        intro j hj hnot
        rw [hul] at hnot ⊢
        rcases (show j = 0 ∨ j = 1 ∨ 2 ≤ j by omega) with rfl | rfl | h2
        · right; rw [hu9, hv9]
        · exact absurd (Or.inr rfl) hnot
        · left
          rintro c (rfl | rfl)
          · exact hA' j hj h2
          · exact hC' j hj h2)
    have hout : C.output = 4 ∨ C.output = 10 := by
      by_contra hno
      exact hne' (hag C.output hno)
    rcases hout with ho | ho
    · refine ⟨0, ⟨[], 10⟩, fun g hg => by simp at hg, by simp [Circuit.size], fun y => ?_⟩
      show (inX y 0).getD 10 false = (C.wires (inZ y)).getD C.output false
      rw [ho, wires_eq, wf_prefix _ _ _ (by rw [inZ_len]; omega), inZ_eq, inX_eq]; rfl
    · refine ⟨0, ⟨[], 9⟩, fun g hg => by simp at hg, by simp [Circuit.size], fun y => ?_⟩
      show (inX y 0).getD 9 false = (C.wires (inZ y)).getD C.output false
      rw [ho, h10 y, inX_eq]; rfl
  · have hag := agree C.gates hop (fun m => m = 4) u v rfl
      (by
        intro m hm
        rcases (show m < 9 ∨ 9 ≤ m by omega) with h | h
        · interval_cases m <;> simp_all
        · rw [getD_big _ _ (by rw [hul]; omega), getD_big _ _ (by rw [hv]; simp; omega)])
      (by
        intro j hj hnot
        rw [hul] at hnot ⊢
        rcases (show j = 0 ∨ j = 1 ∨ 2 ≤ j by omega) with rfl | rfl | h2
        · right; rw [hu9, hv9]
        · left
          rintro c rfl
          rw [hg1e]; exact hB
        · left
          rintro c rfl
          exact hA' j hj h2)
    have hout : C.output = 4 := by
      by_contra hno
      exact hne' (hag C.output hno)
    refine ⟨0, ⟨[], 10⟩, fun g hg => by simp at hg, by simp [Circuit.size], fun y => ?_⟩
    show (inX y 0).getD 10 false = (C.wires (inZ y)).getD C.output false
    rw [hout, wires_eq, wf_prefix _ _ _ (by rw [inZ_len]; omega), inZ_eq, inX_eq]; rfl

end PEqualNP.Outside.L_meta_3141

theorem PEqualNP.Outside.L_meta_3141 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (0 : Fin (9 : ℕ)) || x3 (4 : Fin (9 : ℕ)))) → Option.map PEqualNP.CircuitLowerBounds.Gate.op x1.gates[(1 : ℕ)]? = Option.some PEqualNP.CircuitLowerBounds.GateOp.not → x1.size ≤ (15 : ℕ) → x1.eval [Bool.true, Bool.false, Bool.false, Bool.false, Bool.true, Bool.false, Bool.false, Bool.false, Bool.false] ≠ x1.eval [Bool.true, Bool.false, Bool.false, Bool.false, Bool.false, Bool.false, Bool.false, Bool.false, Bool.false] → ∃ (x7 : Fin (8 : ℕ)) (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x8 ∧ x8.size ≤ (12 : ℕ) ∧ ∀ (x9 : Fin (8 : ℕ) → Bool), x8.eval (List.ofFn x9 ++ [!x9 x7, Bool.true, Bool.false]) = x1.eval (List.ofFn (Fin.insertNth (4 : Fin (9 : ℕ)) Bool.false x9)) := by
  intro x1 hF h9 h1 hsz hne
  obtain ⟨k, C', hF', hs', he⟩ := PEqualNP.Outside.L_meta_3141.main x1 hF h9 h1 hsz hne
  exact ⟨k, C', hF', hs', fun y => he y⟩
