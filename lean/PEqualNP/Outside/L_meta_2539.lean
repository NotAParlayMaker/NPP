import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_2539

def eff (g : Gate) : List ℕ :=
  if g.op.eval [false] = true then List.take 1 g.inputs else g.inputs

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def phi (k : ℕ) : ℕ := if k = 9 then 0 else if k < 9 then k else k - 1

def F (b : Bool) (w : List Bool) : List Bool :=
  (b != w.getD 0 false) :: ((w.take 9).drop 1 ++ w.drop 10)

def constOf : GateOp → Gate
  | GateOp.and => ⟨GateOp.or, []⟩
  | _ => ⟨GateOp.and, []⟩

lemma constOf_inputs (o : GateOp) : (constOf o).inputs = [] := by
  cases o <;> rfl

def tr (g : Gate) : Gate :=
  if 0 ∈ eff g ∧ 9 ∈ eff g then constOf g.op else ⟨g.op, (eff g).map phi⟩

lemma getD_app (w l : List Bool) (k : ℕ) (hk : k < w.length) :
    (w ++ l).getD k false = w.getD k false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hk]

lemma foldl_step_getD (T : List Gate) (w : List Bool) (k : ℕ) (hk : k < w.length) :
    (T.foldl step w).getD k false = w.getD k false := by
  induction T generalizing w with
  | nil => rfl
  | cons g T ih =>
    rw [List.foldl_cons, ih _ (by simp [step]; omega)]
    exact getD_app _ _ _ hk

lemma foldl_step_length (T : List Gate) (w : List Bool) :
    (T.foldl step w).length = w.length + T.length := by
  induction T generalizing w with
  | nil => simp
  | cons g T ih => rw [List.foldl_cons, ih]; simp [step]; omega

lemma eval_eff (g : Gate)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) (f : ℕ → Bool) :
    g.op.eval (g.inputs.map f) = g.op.eval ((eff g).map f) := by
  rcases g with ⟨op, ins⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with rfl | rfl | rfl
  · simp [eff, GateOp.eval]
  · simp [eff, GateOp.eval]
  · cases ins <;> simp [eff, GateOp.eval]

lemma getD_F (b : Bool) (w : List Bool) (hw : 10 ≤ w.length) (k : ℕ) (h0 : k ≠ 0)
    (h9 : k ≠ 9) : (F b w).getD (phi k) false = w.getD k false := by
  unfold F phi
  rw [if_neg h9]
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1
  · rw [List.getElem?_cons_succ, List.getElem?_append_left (by simp; omega)]
    simp [h1]
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + 9 := ⟨j - 9, by omega⟩
    rw [show i + 9 + 1 - 1 = (i + 8) + 1 by omega, List.getElem?_cons_succ,
      List.getElem?_append_right (by simp)]
    simp only [List.length_drop, List.length_take, List.getElem?_drop]
    congr 2
    omega

lemma F_append (b : Bool) (w : List Bool) (v : Bool) (hw : 10 ≤ w.length) :
    F b (w ++ [v]) = F b w ++ [v] := by
  unfold F
  rw [getD_app w [v] 0 (by omega), List.take_append_of_le_length (by omega : 9 ≤ w.length),
    List.drop_append_of_le_length (by omega : 10 ≤ w.length)]
  simp

lemma gate_ok (b : Bool) (w : List Bool) (hw : 10 ≤ w.length)
    (h9 : w.getD 9 false = !w.getD 0 false) (g : Gate)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hb0 : 0 ∈ eff g → 9 ∉ eff g → b = false) (hb9 : 9 ∈ eff g → 0 ∉ eff g → b = true) :
    (tr g).op.eval ((tr g).inputs.map fun i => (F b w).getD i false) =
      g.op.eval (g.inputs.map fun i => w.getD i false) := by
  rw [eval_eff g hop]
  by_cases hboth : 0 ∈ eff g ∧ 9 ∈ eff g
  · rw [tr, if_pos hboth]
    rcases g with ⟨op, ins⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with rfl | rfl | rfl
    · simp only [constOf, GateOp.eval, List.map_nil, List.any_nil]
      symm
      rw [List.all_eq_false]
      cases hc : w.getD 0 false
      · exact ⟨false, List.mem_map.2 ⟨0, hboth.1, hc⟩, by simp⟩
      · exact ⟨false, List.mem_map.2 ⟨9, hboth.2, by rw [h9, hc]; rfl⟩, by simp⟩
    · simp only [constOf, GateOp.eval, List.map_nil, List.all_nil]
      symm
      rw [List.any_eq_true]
      cases hc : w.getD 0 false
      · exact ⟨true, List.mem_map.2 ⟨9, hboth.2, by rw [h9, hc]; rfl⟩, rfl⟩
      · exact ⟨true, List.mem_map.2 ⟨0, hboth.1, hc⟩, rfl⟩
    · exfalso
      cases ins with
      | nil => simp [eff, GateOp.eval] at hboth
      | cons a l => simp [eff, GateOp.eval] at hboth; omega
  · rw [tr, if_neg hboth, List.map_map]
    congr 1
    apply List.map_congr_left
    intro k hk
    simp only [Function.comp]
    by_cases k0 : k = 0
    · subst k0
      have hb := hb0 hk (fun h => hboth ⟨hk, h⟩)
      subst hb
      simp [phi, F]
    by_cases k9 : k = 9
    · subst k9
      have hb := hb9 hk (fun h => hboth ⟨h, hk⟩)
      subst hb
      rw [h9]
      simp [phi, F]
    exact getD_F b w hw k k0 k9

lemma sim (b : Bool) (T : List Gate)
    (hop : ∀ g ∈ T, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hb0 : ∀ g ∈ T, 0 ∈ eff g → 9 ∉ eff g → b = false)
    (hb9 : ∀ g ∈ T, 9 ∈ eff g → 0 ∉ eff g → b = true) :
    ∀ w : List Bool, 10 ≤ w.length → w.getD 9 false = !w.getD 0 false →
    (T.map tr).foldl step (F b w) = F b (T.foldl step w) := by
  induction T with
  | nil => intro w _ _; rfl
  | cons g T ih =>
    intro w hw h9
    simp only [List.map_cons, List.foldl_cons]
    have hstep : step (F b w) (tr g) = F b (step w g) := by
      unfold step
      rw [F_append b w _ hw, gate_ok b w hw h9 g (hop g (by simp)) (hb0 g (by simp))
        (hb9 g (by simp))]
    rw [hstep]
    apply ih (fun g hg => hop g (by simp [hg])) (fun g hg => hb0 g (by simp [hg]))
      (fun g hg => hb9 g (by simp [hg]))
    · simp [step]; omega
    · unfold step
      rw [getD_app _ _ 9 (by omega), getD_app _ _ 0 (by omega)]
      exact h9

lemma two_le {α : Type} (l : List α) (a c : α) (ha : a ∈ l) (hc : c ∈ l) (hne : a ≠ c) :
    2 ≤ l.length := by
  rcases l with _ | ⟨x, _ | ⟨y, l⟩⟩
  · simp at ha
  · simp at ha hc
    exact absurd (ha.trans hc.symm) hne
  · simp

lemma filt_le {α β γ : Type} (l : List α) (f : α → β) (h : α → γ) (q : β → Bool)
    (p : γ → Bool) (H : ∀ a, q (f a) = true → p (h a) = true) :
    ((l.map f).filter q).length ≤ ((l.map h).filter p).length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.filter_cons]
    by_cases hq : q (f a) = true
    · simp [hq, H a hq]; omega
    · by_cases hp : p (h a) = true
      · simp [hq, hp]; omega
      · simp [hq, hp]; omega

end PEqualNP.Outside.L_meta_2539

theorem PEqualNP.Outside.L_meta_2539 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   have x2 : List PEqualNP.CircuitLowerBounds.Gate := List.map (fun (x2 : PEqualNP.CircuitLowerBounds.Gate) => { op := x2.op, inputs := if x2.op.eval [Bool.false] = Bool.true then List.take (1 : ℕ) x2.inputs else x2.inputs : PEqualNP.CircuitLowerBounds.Gate }) (List.drop (1 : ℕ) x1.gates);   PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x4 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x4)).getD (9 : ℕ) Bool.false = !x4 (0 : Fin (9 : ℕ))) → (List.filter (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => [(0 : ℕ), (9 : ℕ)].any fun (x6 : ℕ) => x5.inputs.contains x6) x2).length ≤ (1 : ℕ) → ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 : Bool), PEqualNP.MetaComplexity.FanInTwo x6 ∧ x6.size < x1.size ∧ (List.filter (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => x8.inputs.contains (0 : ℕ)) x6.gates).length ≤ (1 : ℕ) ∧ ∀ (x8 : Fin (9 : ℕ) → Bool), PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 x8 = PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x6 fun (x9 : Fin (9 : ℕ)) => if x9 = (0 : Fin (9 : ℕ)) then x7 != x8 (0 : Fin (9 : ℕ)) else x8 x9 := by
  intro C x2 hF hw hcount
  simp only [x2] at hcount
  obtain ⟨g0, T, hgs⟩ : ∃ g0 T, C.gates = g0 :: T := by
    cases h : C.gates with
    | nil =>
      exfalso
      have := hw (fun _ => false)
      simp [Circuit.wires, h] at this
    | cons g0 T => exact ⟨g0, T, rfl⟩
  rw [hgs, List.drop_one, List.tail_cons] at hcount
  have hgs' : ∀ g ∈ T, g ∈ C.gates := fun g hg => by
    rw [hgs]; exact List.mem_cons_of_mem _ hg
  have hop : ∀ g ∈ T, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) :=
    fun g hg => (hF g (hgs' g hg)).1
  have hwires : ∀ x : Fin 9 → Bool,
      C.wires (List.ofFn x) = T.foldl L_meta_2539.step (L_meta_2539.step (List.ofFn x) g0) := by
    intro x
    unfold Circuit.wires
    rw [hgs]
    rfl
  have hlen0 : ∀ x : Fin 9 → Bool, (L_meta_2539.step (List.ofFn x) g0).length = 10 := by
    intro x
    simp [L_meta_2539.step]
  have hzero : ∀ x : Fin 9 → Bool, (L_meta_2539.step (List.ofFn x) g0).getD 0 false = x 0 := by
    intro x
    simp [L_meta_2539.step, List.ofFn_succ]
  have hnine : ∀ x : Fin 9 → Bool,
      (L_meta_2539.step (List.ofFn x) g0).getD 9 false = !x 0 := by
    intro x
    have h := hw x
    rw [hwires, L_meta_2539.foldl_step_getD _ _ 9 (by rw [hlen0]; omega)] at h
    exact h
  by_cases ho : C.output = 0 ∨ C.output = 9
  · refine ⟨⟨[], 0⟩, decide (C.output = 9), ?_, ?_, ?_, ?_⟩
    · intro g hg
      simp at hg
    · simp [Circuit.size, hgs]
    · simp
    · intro x
      simp only [circuitFun, Circuit.eval]
      rw [hwires]
      rcases ho with h | h
      · rw [h, L_meta_2539.foldl_step_getD _ _ 0 (by rw [hlen0]; omega), hzero]
        simp [Circuit.wires]
      · rw [h, L_meta_2539.foldl_step_getD _ _ 9 (by rw [hlen0]; omega), hnine]
        simp [Circuit.wires]
  · simp only [not_or] at ho
    obtain ⟨b, hbdef⟩ : ∃ b, b = T.any (fun g => (L_meta_2539.eff g).contains 9) := ⟨_, rfl⟩
    have hb9 : ∀ g ∈ T, 9 ∈ L_meta_2539.eff g → 0 ∉ L_meta_2539.eff g → b = true := by
      intro g hg h _
      rw [hbdef, List.any_eq_true]
      exact ⟨g, hg, by simpa using h⟩
    have hb0 : ∀ g ∈ T, 0 ∈ L_meta_2539.eff g → 9 ∉ L_meta_2539.eff g → b = false := by
      intro g hg h0 h9
      by_contra hb
      rw [Bool.not_eq_false, hbdef, List.any_eq_true] at hb
      obtain ⟨g2, hg2, h9'⟩ := hb
      have h9'' : 9 ∈ L_meta_2539.eff g2 := by simpa using h9'
      have hle := L_meta_2539.two_le
        ((T.map fun g => (⟨g.op, L_meta_2539.eff g⟩ : Gate)).filter
          (fun x5 => [0, 9].any fun x6 => x5.inputs.contains x6))
        ⟨g.op, L_meta_2539.eff g⟩ ⟨g2.op, L_meta_2539.eff g2⟩
        (List.mem_filter.2 ⟨List.mem_map.2 ⟨g, hg, rfl⟩, by simp [h0]⟩)
        (List.mem_filter.2 ⟨List.mem_map.2 ⟨g2, hg2, rfl⟩, by simp [h9'']⟩)
        (by
          intro h
          have := congrArg Gate.inputs h
          simp only at this
          rw [this] at h9
          exact h9 h9'')
      exact absurd (le_trans hle hcount) (by norm_num)
    refine ⟨⟨T.map L_meta_2539.tr, L_meta_2539.phi C.output⟩, b, ?_, ?_, ?_, ?_⟩
    · intro g' hg'
      obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hg'
      obtain ⟨hop', hlen⟩ := hF g (hgs' g hg)
      unfold L_meta_2539.tr
      split_ifs
      · rw [L_meta_2539.constOf_inputs]
        refine ⟨?_, by simp⟩
        cases g.op <;> simp [L_meta_2539.constOf]
      · refine ⟨hop', ?_⟩
        simp only [List.length_map, L_meta_2539.eff]
        split_ifs
        · simp only [List.length_take]; omega
        · exact hlen
    · simp [Circuit.size, hgs]
    · refine le_trans (L_meta_2539.filt_le T L_meta_2539.tr
        (fun g => (⟨g.op, L_meta_2539.eff g⟩ : Gate)) (fun g => g.inputs.contains 0)
        (fun x5 => [0, 9].any fun x6 => x5.inputs.contains x6) ?_) hcount
      intro g h
      unfold L_meta_2539.tr at h
      split_ifs at h with hboth
      · simp [L_meta_2539.constOf_inputs] at h
      · simp only [List.contains_iff_mem, List.mem_map] at h
        obtain ⟨k, hk, hk0⟩ := h
        have : k = 0 ∨ k = 9 := by
          unfold L_meta_2539.phi at hk0
          split_ifs at hk0 <;> omega
        rcases this with rfl | rfl <;> simp [hk]
    · intro x
      simp only [circuitFun, Circuit.eval]
      rw [hwires]
      have e2 : List.ofFn (fun i : Fin 9 => if i = 0 then b != x 0 else x i) =
          L_meta_2539.F b (L_meta_2539.step (List.ofFn x) g0) := by
        simp [L_meta_2539.F, L_meta_2539.step, List.ofFn_succ]
      have hsim := L_meta_2539.sim b T hop hb0 hb9 (L_meta_2539.step (List.ofFn x) g0)
        (by rw [hlen0]) (by rw [hnine, hzero])
      show _ = ((T.map L_meta_2539.tr).foldl L_meta_2539.step _).getD _ _
      rw [e2, hsim, L_meta_2539.getD_F b _
        (by rw [L_meta_2539.foldl_step_length, hlen0]; omega) _ ho.1 ho.2]
