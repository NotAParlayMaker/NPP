import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4161

open PEqualNP.CircuitLowerBounds

-- a symbolic wire value: a wire of the new circuit, or a constant
def sv (W : List Bool) : Sum ℕ Bool → Bool
  | Sum.inl w => W.getD w false
  | Sum.inr c => c

def look (σ : List (Sum ℕ Bool)) (i : ℕ) : Sum ℕ Bool := σ.getD i (Sum.inr false)

def eff (g : Gate) : List ℕ :=
  if g.op.eval [false, false] = true then List.take 1 g.inputs else g.inputs

def sAnd (k : ℕ) : List (Sum ℕ Bool) → Sum ℕ Bool × Option (List ℕ)
  | [] => (Sum.inr true, none)
  | [a] => (a, none)
  | [Sum.inr c, b] => if c then (b, none) else (Sum.inr false, none)
  | [Sum.inl w, Sum.inr c] => if c then (Sum.inl w, none) else (Sum.inr false, none)
  | [Sum.inl w1, Sum.inl w2] => (Sum.inl k, some [w1, w2])
  | _ :: _ :: _ :: _ => (Sum.inr false, none)

def sOr (k : ℕ) : List (Sum ℕ Bool) → Sum ℕ Bool × Option (List ℕ)
  | [] => (Sum.inr false, none)
  | [a] => (a, none)
  | [Sum.inr c, b] => if c then (Sum.inr true, none) else (b, none)
  | [Sum.inl w, Sum.inr c] => if c then (Sum.inr true, none) else (Sum.inl w, none)
  | [Sum.inl w1, Sum.inl w2] => (Sum.inl k, some [w1, w2])
  | _ :: _ :: _ :: _ => (Sum.inr false, none)

def sNot (k : ℕ) : List (Sum ℕ Bool) → Sum ℕ Bool × Option (List ℕ)
  | [] => (Sum.inr true, none)
  | Sum.inr c :: _ => (Sum.inr (!c), none)
  | Sum.inl w :: _ => (Sum.inl k, some [w])

def mk (op : GateOp) (p : Sum ℕ Bool × Option (List ℕ)) : Sum ℕ Bool × Option Gate :=
  (p.1, p.2.map fun l => ⟨op, l⟩)

def stepG (g : Gate) (σ : List (Sum ℕ Bool)) (k : ℕ) : Sum ℕ Bool × Option Gate :=
  match g.op with
  | GateOp.and => mk GateOp.and (sAnd k ((eff g).map (look σ)))
  | GateOp.or => mk GateOp.or (sOr k ((eff g).map (look σ)))
  | GateOp.not => mk GateOp.not (sNot k ((eff g).map (look σ)))
  | _ => (Sum.inr false, none)

def tr : List Gate → List (Sum ℕ Bool) → List Gate → List (Sum ℕ Bool) × List Gate
  | [], σ, NG => (σ, NG)
  | g :: gs, σ, NG => tr gs (σ ++ [(stepG g σ (8 + NG.length)).1])
      (NG ++ (stepG g σ (8 + NG.length)).2.toList)

def wstep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def Ok (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2

-- List facts

theorem getD_app_lt (l l' : List Bool) (i : ℕ) (h : i < l.length) :
    (l ++ l').getD i false = l.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_ge (l : List Bool) (i : ℕ) (h : l.length ≤ i) : l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem getD_last (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

theorem look_app_lt (σ τ : List (Sum ℕ Bool)) (i : ℕ) (h : i < σ.length) :
    look (σ ++ τ) i = look σ i := by
  simp [look, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem look_ge (σ : List (Sum ℕ Bool)) (i : ℕ) (h : σ.length ≤ i) :
    look σ i = Sum.inr false := by
  simp [look, List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem look_last (σ : List (Sum ℕ Bool)) (r : Sum ℕ Bool) : look (σ ++ [r]) σ.length = r := by
  simp [look, List.getD_eq_getElem?_getD]

theorem sv_app (W V : List Bool) (s : Sum ℕ Bool) (h : ∀ w, s = Sum.inl w → w < W.length) :
    sv (W ++ V) s = sv W s := by
  cases s with
  | inl w => exact getD_app_lt W V w (h w rfl)
  | inr c => rfl

-- The three simplifiers

theorem sAnd_none (W : List Bool) (k : ℕ) (ins : List (Sum ℕ Bool)) (hl : ins.length ≤ 2)
    (h : (sAnd k ins).2 = none) : sv W (sAnd k ins).1 = (ins.map (sv W)).all id := by
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · rfl
  · simp [sAnd]
  · rcases a with w1 | c1 <;> rcases b with w2 | c2
    · simp [sAnd] at h
    · cases c2 <;> simp [sAnd, sv]
    · cases c1 <;> simp [sAnd, sv]
    · cases c1 <;> cases c2 <;> simp [sAnd, sv]
  · simp at hl

theorem sAnd_some (W : List Bool) (k : ℕ) (ins : List (Sum ℕ Bool)) (l : List ℕ)
    (h : (sAnd k ins).2 = some l) :
    (sAnd k ins).1 = Sum.inl k ∧ (l.map fun i => W.getD i false).all id = (ins.map (sv W)).all id ∧
      l.length ≤ 2 ∧ ∀ s ∈ ins, ∃ w, s = Sum.inl w := by
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · simp [sAnd] at h
  · simp [sAnd] at h
  · rcases a with w1 | c1 <;> rcases b with w2 | c2
    · simp only [sAnd, Option.some.injEq] at h
      subst h
      simp [sAnd, sv]
    · cases c2 <;> simp [sAnd] at h
    · cases c1 <;> simp [sAnd] at h
    · cases c1 <;> cases c2 <;> simp [sAnd] at h
  · simp [sAnd] at h

theorem sAnd_src (k : ℕ) (ins : List (Sum ℕ Bool)) (h : (sAnd k ins).2 = none) (w : ℕ)
    (hw : (sAnd k ins).1 = Sum.inl w) : Sum.inl w ∈ ins := by
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · simp [sAnd] at hw
  · simp [sAnd] at hw; simp [hw]
  · rcases a with w1 | c1 <;> rcases b with w2 | c2
    · simp [sAnd] at h
    · cases c2 <;> simp [sAnd] at hw; simp [hw]
    · cases c1 <;> simp [sAnd] at hw; simp [hw]
    · cases c1 <;> cases c2 <;> simp [sAnd] at hw
  · simp [sAnd] at hw

theorem sOr_none (W : List Bool) (k : ℕ) (ins : List (Sum ℕ Bool)) (hl : ins.length ≤ 2)
    (h : (sOr k ins).2 = none) : sv W (sOr k ins).1 = (ins.map (sv W)).any id := by
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · rfl
  · simp [sOr]
  · rcases a with w1 | c1 <;> rcases b with w2 | c2
    · simp [sOr] at h
    · cases c2 <;> simp [sOr, sv]
    · cases c1 <;> simp [sOr, sv]
    · cases c1 <;> cases c2 <;> simp [sOr, sv]
  · simp at hl

theorem sOr_some (W : List Bool) (k : ℕ) (ins : List (Sum ℕ Bool)) (l : List ℕ)
    (h : (sOr k ins).2 = some l) :
    (sOr k ins).1 = Sum.inl k ∧ (l.map fun i => W.getD i false).any id = (ins.map (sv W)).any id ∧
      l.length ≤ 2 ∧ ∀ s ∈ ins, ∃ w, s = Sum.inl w := by
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · simp [sOr] at h
  · simp [sOr] at h
  · rcases a with w1 | c1 <;> rcases b with w2 | c2
    · simp only [sOr, Option.some.injEq] at h
      subst h
      simp [sOr, sv]
    · cases c2 <;> simp [sOr] at h
    · cases c1 <;> simp [sOr] at h
    · cases c1 <;> cases c2 <;> simp [sOr] at h
  · simp [sOr] at h

theorem sOr_src (k : ℕ) (ins : List (Sum ℕ Bool)) (h : (sOr k ins).2 = none) (w : ℕ)
    (hw : (sOr k ins).1 = Sum.inl w) : Sum.inl w ∈ ins := by
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · simp [sOr] at hw
  · simp [sOr] at hw; simp [hw]
  · rcases a with w1 | c1 <;> rcases b with w2 | c2
    · simp [sOr] at h
    · cases c2 <;> simp [sOr] at hw; simp [hw]
    · cases c1 <;> simp [sOr] at hw; simp [hw]
    · cases c1 <;> cases c2 <;> simp [sOr] at hw
  · simp [sOr] at hw

theorem sOr_true (k : ℕ) (ins : List (Sum ℕ Bool)) (hl : ins.length ≤ 2)
    (ht : Sum.inr true ∈ ins) : (sOr k ins).1 = Sum.inr true := by
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · simp at ht
  · simp at ht; subst ht; rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with ht | ht
    · subst ht; simp [sOr]
    · subst ht
      rcases a with w1 | c1
      · simp [sOr]
      · cases c1 <;> simp [sOr]
  · simp at hl

theorem sNot_none (W : List Bool) (k : ℕ) (ins : List (Sum ℕ Bool))
    (h : (sNot k ins).2 = none) : sv W (sNot k ins).1 = !((ins.map (sv W)).headD false) := by
  rcases ins with _ | ⟨a, rest⟩
  · rfl
  · rcases a with w | c
    · simp [sNot] at h
    · simp [sNot, sv]

theorem sNot_some (W : List Bool) (k : ℕ) (ins : List (Sum ℕ Bool)) (l : List ℕ)
    (hl : ins.length ≤ 1) (h : (sNot k ins).2 = some l) :
    (sNot k ins).1 = Sum.inl k ∧ (!((l.map fun i => W.getD i false).headD false)) =
      (!((ins.map (sv W)).headD false)) ∧ l.length ≤ 2 ∧ ∀ s ∈ ins, ∃ w, s = Sum.inl w := by
  rcases ins with _ | ⟨a, _ | ⟨b, rest⟩⟩
  · simp [sNot] at h
  · rcases a with w | c
    · simp only [sNot, Option.some.injEq] at h
      subst h
      simp [sNot, sv]
    · simp [sNot] at h
  · simp at hl

theorem sNot_src (k : ℕ) (ins : List (Sum ℕ Bool)) (h : (sNot k ins).2 = none) (w : ℕ)
    (hw : (sNot k ins).1 = Sum.inl w) : Sum.inl w ∈ ins := by
  rcases ins with _ | ⟨a, rest⟩
  · simp [sNot] at hw
  · rcases a with w' | c
    · simp [sNot] at h
    · simp [sNot] at hw

-- One gate

theorem eff_and (g : Gate) (h : g.op = GateOp.and) : eff g = g.inputs := by
  simp [eff, h, GateOp.eval]

theorem eff_or (g : Gate) (h : g.op = GateOp.or) : eff g = g.inputs := by
  simp [eff, h, GateOp.eval]

theorem eff_not (g : Gate) (h : g.op = GateOp.not) : eff g = List.take 1 g.inputs := by
  simp [eff, h, GateOp.eval]

theorem not_eval_take (l : List Bool) :
    GateOp.not.eval l = !((List.take 1 l).headD false) := by
  cases l <;> simp [GateOp.eval]

theorem step_none (g : Gate) (σ : List (Sum ℕ Bool)) (k : ℕ) (W : List Bool) (hg : Ok g)
    (h : (stepG g σ k).2 = none) :
    sv W (stepG g σ k).1 = g.op.eval (g.inputs.map fun i => sv W (look σ i)) := by
  obtain ⟨hop, hl⟩ := hg
  rcases hop with hop | hop | hop
  · have e := eff_and g hop
    simp only [stepG, hop, mk] at h ⊢
    rw [e] at h ⊢
    rw [sAnd_none W k _ (by simpa using hl) (by simpa using h)]
    simp [GateOp.eval, List.map_map, Function.comp_def]
  · have e := eff_or g hop
    simp only [stepG, hop, mk] at h ⊢
    rw [e] at h ⊢
    rw [sOr_none W k _ (by simpa using hl) (by simpa using h)]
    simp [GateOp.eval, List.map_map, Function.comp_def]
  · have e := eff_not g hop
    simp only [stepG, hop, mk] at h ⊢
    rw [e] at h ⊢
    rw [sNot_none W k _ (by simpa using h)]
    cases g.inputs with
    | nil => rfl
    | cons a rest => simp [GateOp.eval]

theorem step_some (g : Gate) (σ : List (Sum ℕ Bool)) (k : ℕ) (W : List Bool) (hg : Ok g)
    (h' : Gate) (h : (stepG g σ k).2 = some h') :
    (stepG g σ k).1 = Sum.inl k ∧
      h'.op.eval (h'.inputs.map fun i => W.getD i false) =
        g.op.eval (g.inputs.map fun i => sv W (look σ i)) ∧ Ok h' := by
  obtain ⟨hop, hl⟩ := hg
  rcases hop with hop | hop | hop
  · have e := eff_and g hop
    simp only [stepG, hop, mk] at h ⊢
    rw [e] at h ⊢
    obtain ⟨l, hl', rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨h1, h2, h3, _⟩ := sAnd_some W k _ l hl'
    refine ⟨h1, ?_, ⟨Or.inl rfl, h3⟩⟩
    simp only [GateOp.eval] at h2 ⊢
    rw [h2]
    simp [List.map_map, Function.comp_def]
  · have e := eff_or g hop
    simp only [stepG, hop, mk] at h ⊢
    rw [e] at h ⊢
    obtain ⟨l, hl', rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨h1, h2, h3, _⟩ := sOr_some W k _ l hl'
    refine ⟨h1, ?_, ⟨Or.inr (Or.inl rfl), h3⟩⟩
    simp only [GateOp.eval] at h2 ⊢
    rw [h2]
    simp [List.map_map, Function.comp_def]
  · have e := eff_not g hop
    simp only [stepG, hop, mk] at h ⊢
    rw [e] at h ⊢
    obtain ⟨l, hl', rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨h1, h2, h3, _⟩ := sNot_some W k _ l (by simp) hl'
    refine ⟨h1, ?_, ⟨Or.inr (Or.inr rfl), h3⟩⟩
    simp only [GateOp.eval]
    rw [h2]
    cases g.inputs with
    | nil => rfl
    | cons a rest => simp

theorem step_src (g : Gate) (σ : List (Sum ℕ Bool)) (k : ℕ) (h : (stepG g σ k).2 = none)
    (w : ℕ) (hw : (stepG g σ k).1 = Sum.inl w) : ∃ j, look σ j = Sum.inl w := by
  cases hop : g.op <;> simp only [stepG, hop, mk] at h hw
  · obtain ⟨j, _, hj⟩ := List.mem_map.mp (sAnd_src k _ (by simpa using h) w hw)
    exact ⟨j, hj⟩
  · obtain ⟨j, _, hj⟩ := List.mem_map.mp (sOr_src k _ (by simpa using h) w hw)
    exact ⟨j, hj⟩
  · obtain ⟨j, _, hj⟩ := List.mem_map.mp (sNot_src k _ (by simpa using h) w hw)
    exact ⟨j, hj⟩
  all_goals simp at hw

theorem step_const (g : Gate) (σ : List (Sum ℕ Bool)) (k : ℕ) (j : ℕ) (hj : j ∈ eff g) (c : Bool)
    (hc : look σ j = Sum.inr c) : (stepG g σ k).2 = none := by
  cases h : (stepG g σ k).2 with
  | none => rfl
  | some h' =>
    exfalso
    cases hop : g.op <;> simp only [stepG, hop, mk] at h
    · obtain ⟨l, hl', _⟩ := Option.map_eq_some_iff.mp (by simpa [mk] using h)
      obtain ⟨_, _, _, h4⟩ := sAnd_some [] k _ l hl'
      obtain ⟨w, hw⟩ := h4 _ (List.mem_map.mpr ⟨j, hj, rfl⟩)
      rw [hc] at hw; cases hw
    · obtain ⟨l, hl', _⟩ := Option.map_eq_some_iff.mp (by simpa [mk] using h)
      obtain ⟨_, _, _, h4⟩ := sOr_some [] k _ l hl'
      obtain ⟨w, hw⟩ := h4 _ (List.mem_map.mpr ⟨j, hj, rfl⟩)
      rw [hc] at hw; cases hw
    · obtain ⟨l, hl', _⟩ := Option.map_eq_some_iff.mp (by simpa [mk] using h)
      have hlen : ((eff g).map (look σ)).length ≤ 1 := by
        rw [eff_not g hop]; simp
      obtain ⟨_, _, _, h4⟩ := sNot_some [] k _ l hlen hl'
      obtain ⟨w, hw⟩ := h4 _ (List.mem_map.mpr ⟨j, hj, rfl⟩)
      rw [hc] at hw; cases hw
    all_goals simp at h

theorem step_ok (g : Gate) (σ : List (Sum ℕ Bool)) (k : ℕ) (h' : Gate)
    (h : (stepG g σ k).2 = some h') : Ok h' := by
  cases hop : g.op <;> simp only [stepG, hop, mk] at h
  · obtain ⟨l, hl', rfl⟩ := Option.map_eq_some_iff.mp (by simpa [mk] using h)
    exact ⟨Or.inl rfl, (sAnd_some [] k _ l hl').2.2.1⟩
  · obtain ⟨l, hl', rfl⟩ := Option.map_eq_some_iff.mp (by simpa [mk] using h)
    exact ⟨Or.inr (Or.inl rfl), (sOr_some [] k _ l hl').2.2.1⟩
  · obtain ⟨l, hl', rfl⟩ := Option.map_eq_some_iff.mp (by simpa [mk] using h)
    have hlen : ((eff g).map (look σ)).length ≤ 1 := by
      rw [eff_not g hop]; simp
    exact ⟨Or.inr (Or.inr rfl), (sNot_some [] k _ l hlen hl').2.2.1⟩
  all_goals simp at h

theorem step_or_true (g : Gate) (σ : List (Sum ℕ Bool)) (k : ℕ) (hop : g.op = GateOp.or)
    (hl : g.inputs.length ≤ 2) (j : ℕ) (hj : j ∈ g.inputs) (hc : look σ j = Sum.inr true) :
    (stepG g σ k).1 = Sum.inr true := by
  simp only [stepG, hop, mk]
  rw [eff_or g hop]
  exact sOr_true k _ (by simpa using hl) (List.mem_map.mpr ⟨j, hj, hc⟩)

-- The whole list

theorem tr_append (a b : List Gate) (σ : List (Sum ℕ Bool)) (NG : List Gate) :
    tr (a ++ b) σ NG = tr b (tr a σ NG).1 (tr a σ NG).2 := by
  induction a generalizing σ NG with
  | nil => rfl
  | cons g gs ih => simp only [List.cons_append, tr]; exact ih _ _

theorem tr_fst (gs : List Gate) (σ : List (Sum ℕ Bool)) (NG : List Gate) :
    ∃ τ, (tr gs σ NG).1 = σ ++ τ ∧ τ.length = gs.length := by
  induction gs generalizing σ NG with
  | nil => exact ⟨[], by simp [tr]⟩
  | cons g gs ih =>
    obtain ⟨τ, h1, h2⟩ := ih (σ ++ [(stepG g σ (8 + NG.length)).1])
      (NG ++ (stepG g σ (8 + NG.length)).2.toList)
    refine ⟨(stepG g σ (8 + NG.length)).1 :: τ, ?_, by simp [h2]⟩
    simp only [tr]
    rw [h1]; simp

theorem tr_ok (gs : List Gate) (σ : List (Sum ℕ Bool)) (NG : List Gate) (h : ∀ g ∈ NG, Ok g) :
    ∀ g ∈ (tr gs σ NG).2, Ok g := by
  induction gs generalizing σ NG with
  | nil => simpa [tr] using h
  | cons g gs ih =>
    simp only [tr]
    apply ih
    intro h' hh
    rcases List.mem_append.mp hh with hh | hh
    · exact h h' hh
    · cases e : (stepG g σ (8 + NG.length)).2 with
      | none => rw [e] at hh; simp at hh
      | some h'' =>
        rw [e] at hh
        simp at hh
        rw [hh]
        exact step_ok g σ _ h'' e

theorem tr_count (P : Gate → Bool) (gs : List Gate) (σ : List (Sum ℕ Bool)) (NG : List Gate)
    (hP : ∀ g ∈ gs, P g = true → ∀ τ k, (stepG g (σ ++ τ) k).2 = none) :
    (tr gs σ NG).2.length + (gs.filter P).length ≤ NG.length + gs.length := by
  induction gs generalizing σ NG with
  | nil => simp [tr]
  | cons g gs ih =>
    simp only [tr]
    have ih' := ih (σ ++ [(stepG g σ (8 + NG.length)).1])
      (NG ++ (stepG g σ (8 + NG.length)).2.toList) (by
        intro g' hg' hp τ k
        rw [List.append_assoc]
        exact hP g' (List.mem_cons_of_mem g hg') hp _ k)
    have hle : (stepG g σ (8 + NG.length)).2.toList.length ≤ 1 := by
      cases (stepG g σ (8 + NG.length)).2 <;> simp
    rw [List.length_append] at ih'
    by_cases hp : P g = true
    · have hn := hP g (List.mem_cons_self ..) hp [] (8 + NG.length)
      rw [List.append_nil] at hn
      rw [hn] at ih' ⊢
      rw [List.filter_cons_of_pos hp]
      simp only [Option.toList_none, List.length_nil, List.length_cons] at ih' ⊢
      omega
    · rw [List.filter_cons_of_neg hp]
      simp only [List.length_cons]
      omega

def Inv (σ : List (Sum ℕ Bool)) (OW W : List Bool) : Prop :=
  σ.length = OW.length ∧ (∀ i, OW.getD i false = sv W (look σ i)) ∧
    ∀ i w, look σ i = Sum.inl w → w < W.length

theorem tr_inv (N0 : List Bool) (gs : List Gate) (σ : List (Sum ℕ Bool)) (NG : List Gate)
    (OW : List Bool) (hg : ∀ g ∈ gs, Ok g) (hinv : Inv σ OW (NG.foldl wstep N0))
    (hlen : (NG.foldl wstep N0).length = 8 + NG.length) :
    Inv (tr gs σ NG).1 (gs.foldl wstep OW) ((tr gs σ NG).2.foldl wstep N0) := by
  induction gs generalizing σ NG OW with
  | nil => simpa [tr] using hinv
  | cons g gs ih =>
    simp only [tr, List.foldl_cons]
    set W := NG.foldl wstep N0 with hW
    set p := stepG g σ (8 + NG.length) with hp
    have hgok := hg g (List.mem_cons_self ..)
    obtain ⟨hl, hv, hb⟩ := hinv
    -- the old gate value in terms of the symbolic values
    have hold : g.op.eval (g.inputs.map fun i => OW.getD i false) =
        g.op.eval (g.inputs.map fun i => sv W (look σ i)) := by
      congr 1; exact List.map_congr_left (fun i _ => hv i)
    have hW' : (NG ++ p.2.toList).foldl wstep N0 =
        W ++ (p.2.toList.map fun h => h.op.eval (h.inputs.map fun i => W.getD i false)) := by
      rw [List.foldl_append]
      cases p.2 with
      | none => simp [hW]
      | some h => simp [wstep, hW]
    apply ih
    · exact fun g' hg' => hg g' (List.mem_cons_of_mem g hg')
    · rw [hW']
      refine ⟨by simp [wstep, hl], ?_, ?_⟩
      · intro i
        rcases lt_trichotomy i OW.length with hi | hi | hi
        · rw [show wstep OW g = OW ++ _ from rfl, getD_app_lt _ _ _ hi,
            look_app_lt _ _ _ (by omega), hv i, sv_app _ _ _ (hb i)]
        · subst hi
          rw [show wstep OW g = OW ++ _ from rfl, getD_last, ← hl, look_last, hold]
          cases e : p.2 with
          | none =>
            simp only [Option.toList_none, List.map_nil, List.append_nil]
            exact (step_none g σ _ W hgok e).symm
          | some h' =>
            obtain ⟨h1, h2, _⟩ := step_some g σ _ W hgok h' e
            rw [h1]
            simp only [Option.toList_some, List.map_cons, List.map_nil, sv]
            rw [← hlen, getD_last, h2]
            rfl
        · rw [getD_ge _ _ (by simp [wstep]; omega), look_ge _ _ (by simp; omega)]
          rfl
      · intro i w hiw
        simp only [List.length_append, List.length_map]
        rcases lt_trichotomy i σ.length with hi | hi | hi
        · rw [look_app_lt _ _ _ hi] at hiw
          have := hb i w hiw; omega
        · subst hi
          rw [look_last] at hiw
          cases e : p.2 with
          | none =>
            obtain ⟨j, hj⟩ := step_src g σ _ e w hiw
            have := hb j w hj; omega
          | some h' =>
            obtain ⟨h1, _, _⟩ := step_some g σ _ W hgok h' e
            rw [h1] at hiw
            cases hiw
            simp; omega
        · rw [look_ge _ _ (by simp; omega)] at hiw; cases hiw
    · rw [hW', List.length_append, hlen]
      cases p.2 <;> simp <;> omega

theorem look_mid (A B : List (Sum ℕ Bool)) (r : Sum ℕ Bool) : look (A ++ [r] ++ B) A.length = r := by
  simp [look, List.getD_eq_getElem?_getD]

def inp (x1 : Bool) (x2 : Fin 8 → Bool) : List Bool := [x2 (1 : Fin (8 : ℕ)), x2 (0 : Fin (8 : ℕ)), x2 (4 : Fin (8 : ℕ)), x2 (7 : Fin (8 : ℕ)), x2 (5 : Fin (8 : ℕ)), x2 (2 : Fin (8 : ℕ)), x1, x2 (6 : Fin (8 : ℕ)), x2 (3 : Fin (8 : ℕ)), x2 (1 : Fin (8 : ℕ)) || x1]

def σ0 : List (Sum ℕ Bool) := [Sum.inl 1, Sum.inl 0, Sum.inl 4, Sum.inl 7, Sum.inl 5, Sum.inl 2,
  Sum.inr true, Sum.inl 6, Sum.inl 3, Sum.inr true]

theorem inv0 (x : Fin 8 → Bool) : Inv σ0 (inp true x) (([] : List Gate).foldl wstep (List.ofFn x)) := by
  refine ⟨rfl, ?_, ?_⟩
  · intro i
    by_cases hi : i < 10
    · interval_cases i <;> simp [inp, σ0, look, sv, List.getD_eq_getElem?_getD]
    · rw [getD_ge _ _ (by simp [inp]; omega), look_ge _ _ (by simp [σ0]; omega)]
      rfl
  · intro i w hw
    by_cases hi : i < 10
    · interval_cases i <;> simp [σ0, look, List.getD_eq_getElem?_getD] at hw <;> subst hw <;> simp
    · rw [look_ge _ _ (by simp [σ0]; omega)] at hw
      cases hw

theorem core (x3 x4 : List Gate) (x5 : Gate) (x6 : ℕ)
    (hfan : PEqualNP.MetaComplexity.FanInTwo (⟨x3 ++ x5 :: x4, x6⟩ : Circuit))
    (hop : x5.op = GateOp.or)
    (h6 : ((eff x5).any fun (x10 : ℕ) => Decidable.decide (x10 = (6 : ℕ))) = Bool.true) :
    PEqualNP.MetaComplexity.HasCircuitSize 8
      (fun x => (⟨x3 ++ x5 :: x4, x6⟩ : Circuit).eval (inp true x))
      (max 1 (x3.length + x4.length - ((x3.filter fun g => (eff g).contains 9).length +
        (x4.filter fun g => (eff g).contains 9 || (eff g).contains (10 + x3.length)).length))) := by
  have hok : ∀ g ∈ x3 ++ x5 :: x4, Ok g := fun g hg => by
    obtain ⟨h1, h2⟩ := hfan g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
    exact ⟨h1, h2⟩
  obtain ⟨τ3, hτ3, hτ3l⟩ := tr_fst x3 σ0 []
  have h3 := tr_count (fun g => (eff g).contains 9) x3 σ0 [] (by
    intro g _ hp τ k
    have h9 : 9 ∈ eff g := by simpa using hp
    exact step_const g (σ0 ++ τ) k 9 h9 true (by rw [look_app_lt _ _ _ (by simp [σ0])]; rfl))
  have h6' : 6 ∈ x5.inputs := by
    rw [← eff_or x5 hop]; simpa using h6
  have hx5ok := hok x5 (by simp)
  have hl6 : look (tr x3 σ0 []).1 6 = Sum.inr true := by
    rw [hτ3, look_app_lt _ _ _ (by simp [σ0])]; rfl
  have e5n : (stepG x5 (tr x3 σ0 []).1 (8 + (tr x3 σ0 []).2.length)).2 = none :=
    step_const x5 _ _ 6 (by rw [eff_or x5 hop]; exact h6') true hl6
  have e5r : (stepG x5 (tr x3 σ0 []).1 (8 + (tr x3 σ0 []).2.length)).1 = Sum.inr true :=
    step_or_true x5 _ _ hop hx5ok.2 6 h6' hl6
  have htr : tr (x3 ++ x5 :: x4) σ0 [] =
      tr x4 ((tr x3 σ0 []).1 ++ [Sum.inr true]) (tr x3 σ0 []).2 := by
    rw [tr_append]; simp only [tr]; rw [e5n, e5r]; simp
  have h4 := tr_count (fun g => (eff g).contains 9 || (eff g).contains (10 + x3.length)) x4
    ((tr x3 σ0 []).1 ++ [Sum.inr true]) (tr x3 σ0 []).2 (by
      intro g _ hp τ k
      simp only [Bool.or_eq_true, List.contains_iff_mem] at hp
      rcases hp with hp | hp
      · refine step_const g _ k 9 hp true ?_
        rw [hτ3, List.append_assoc, List.append_assoc, look_app_lt _ _ _ (by simp [σ0])]; rfl
      · refine step_const g _ k _ hp true ?_
        rw [hτ3, show 10 + x3.length = (σ0 ++ τ3).length by simp [σ0, hτ3l]; omega]
        exact look_mid _ _ _)
  have hcount : (tr (x3 ++ x5 :: x4) σ0 []).2.length + ((x3.filter fun g => (eff g).contains 9).length +
      (x4.filter fun g => (eff g).contains 9 || (eff g).contains (10 + x3.length)).length) ≤
      x3.length + x4.length := by
    have hnil : ([] : List Gate).length = 0 := rfl
    rw [htr]; omega
  have hinv := fun x => tr_inv (List.ofFn x) (x3 ++ x5 :: x4) σ0 [] (inp true x) hok (inv0 x)
    (by simp)
  have hgok := tr_ok (x3 ++ x5 :: x4) σ0 [] (by simp)
  have hold : ∀ x, (⟨x3 ++ x5 :: x4, x6⟩ : Circuit).eval (inp true x) =
      sv ((tr (x3 ++ x5 :: x4) σ0 []).2.foldl wstep (List.ofFn x)) (look (tr (x3 ++ x5 :: x4) σ0 []).1 x6) :=
    fun x => (hinv x).2.1 x6
  rcases hout : look (tr (x3 ++ x5 :: x4) σ0 []).1 x6 with w | c
  · refine ⟨⟨(tr (x3 ++ x5 :: x4) σ0 []).2, w⟩, ?_, ?_, ?_⟩
    · intro g hg
      obtain ⟨h1, h2⟩ := hgok g hg
      refine ⟨?_, h2⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      exact h1
    · exact le_max_of_le_right (Nat.le_sub_of_add_le hcount)
    · intro x
      beta_reduce
      rw [hold x, hout]
      rfl
  · cases c
    · refine ⟨⟨[], 8⟩, ?_, ?_, ?_⟩
      · intro g hg; simp at hg
      · exact le_max_of_le_right (Nat.zero_le _)
      · intro x
        beta_reduce
        rw [hold x, hout]
        simp [Circuit.eval, Circuit.wires, sv, List.getD_eq_getElem?_getD]
    · refine ⟨⟨[⟨GateOp.and, []⟩], 8⟩, ?_, ?_, ?_⟩
      · intro g hg
        simp only [List.mem_singleton] at hg
        subst hg
        exact ⟨by simp, by simp⟩
      · exact le_max_left _ _
      · intro x
        beta_reduce
        rw [hold x, hout]
        simp [Circuit.eval, Circuit.wires, sv, GateOp.eval, List.getD_eq_getElem?_getD]

end PEqualNP.Outside.L_meta_4161

theorem PEqualNP.Outside.L_meta_4161 : have x1 : Bool → (Fin (8 : ℕ) → Bool) → List Bool := fun (x1 : Bool) (x2 : Fin (8 : ℕ) → Bool) => [x2 (1 : Fin (8 : ℕ)), x2 (0 : Fin (8 : ℕ)), x2 (4 : Fin (8 : ℕ)), x2 (7 : Fin (8 : ℕ)), x2 (5 : Fin (8 : ℕ)), x2 (2 : Fin (8 : ℕ)), x1, x2 (6 : Fin (8 : ℕ)), x2 (3 : Fin (8 : ℕ)), x2 (1 : Fin (8 : ℕ)) || x1]; have x2 : PEqualNP.CircuitLowerBounds.Gate → List ℕ := fun (x2 : PEqualNP.CircuitLowerBounds.Gate) => if x2.op.eval [Bool.false, Bool.false] = Bool.true then List.take (1 : ℕ) x2.inputs else x2.inputs; ∀ (x3 x4 : List PEqualNP.CircuitLowerBounds.Gate) (x5 : PEqualNP.CircuitLowerBounds.Gate) (x6 : ℕ),   have x7 : PEqualNP.CircuitLowerBounds.Circuit := { gates := x3 ++ x5 :: x4, output := x6 : PEqualNP.CircuitLowerBounds.Circuit };   PEqualNP.MetaComplexity.FanInTwo x7 → x5.op = PEqualNP.CircuitLowerBounds.GateOp.or → ((x2 x5).any fun (x10 : ℕ) => Decidable.decide (x10 = (6 : ℕ))) = Bool.true → PEqualNP.MetaComplexity.HasCircuitSize (8 : ℕ) (fun (x11 : Fin (8 : ℕ) → Bool) => x7.eval (x1 Bool.true x11)) (Max.max (1 : ℕ) (x3.length + x4.length - ((List.filter (fun (x11 : PEqualNP.CircuitLowerBounds.Gate) => (x2 x11).contains (9 : ℕ)) x3).length + (List.filter (fun (x11 : PEqualNP.CircuitLowerBounds.Gate) => (x2 x11).contains (9 : ℕ) || (x2 x11).contains ((10 : ℕ) + x3.length)) x4).length))) := by
  dsimp only
  intro x3 x4 x5 x6 hfan hop h6
  exact PEqualNP.Outside.L_meta_4161.core x3 x4 x5 x6 hfan hop h6
