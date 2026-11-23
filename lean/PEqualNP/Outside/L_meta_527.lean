import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_527_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

private lemma wiresFrom_nil (w : List Bool) : wiresFrom [] w = w := rfl

private lemma wiresFrom_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wiresFrom (g :: gs) w =
      wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

private lemma wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
  induction gs₁ generalizing w with
  | nil => rfl
  | cons g gs ih => simp only [List.cons_append, wiresFrom_cons, ih]

private lemma wiresFrom_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [wiresFrom]
  | cons g gs ih =>
    rw [wiresFrom_cons, ih]
    simp
    omega

private lemma getD_snoc_lt {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i < l.length) :
    (l ++ [x]).getD i d = l.getD i d := by
  simp [List.getD, List.getElem?_append_left hi]

private lemma getD_snoc_eq {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i = l.length) :
    (l ++ [x]).getD i d = x := by
  subst hi
  simp [List.getD]

private lemma getD_snoc_ne {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i ≠ l.length) :
    (l ++ [x]).getD i d = l.getD i d := by
  by_cases hlt : i < l.length
  · exact getD_snoc_lt l x d i hlt
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

private lemma ofFn_getD_lt {α : Type*} {m : ℕ} (f : Fin m → α) (d : α) (i : ℕ) (hi : i < m) :
    (List.ofFn f).getD i d = f ⟨i, hi⟩ := by
  simp [List.getD, hi]

private lemma wiresFrom_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [wiresFrom_cons, ih _ (by simp; omega)]
    exact getD_snoc_lt _ _ _ _ hi

private lemma wiresFrom_agree (gs : List Gate) (S : Set ℕ) (w₁ w₂ : List Bool)
    (hlen : w₁.length = w₂.length)
    (hS : ∀ u ∈ S, u < w₁.length)
    (hag : ∀ i, i ∉ S → w₁.getD i false = w₂.getD i false)
    (hno : ∀ g ∈ gs, ∀ i ∈ g.inputs, i ∉ S) :
    (wiresFrom gs w₁).length = (wiresFrom gs w₂).length ∧
      ∀ i, i ∉ S → (wiresFrom gs w₁).getD i false = (wiresFrom gs w₂).getD i false := by
  induction gs generalizing w₁ w₂ with
  | nil => exact ⟨hlen, hag⟩
  | cons g gs ih =>
    have hmap : (g.inputs.map fun i => w₁.getD i false) =
        (g.inputs.map fun i => w₂.getD i false) := by
      apply List.map_congr_left
      intro i hi
      exact hag i (hno g (by simp) i hi)
    rw [wiresFrom_cons, wiresFrom_cons, hmap]
    apply ih
    · simp [hlen]
    · intro u hu; simp; have := hS u hu; omega
    · intro i hi
      by_cases hlt : i < w₁.length
      · rw [getD_snoc_lt _ _ _ _ hlt, getD_snoc_lt _ _ _ _ (by omega)]
        exact hag i hi
      · by_cases heq : i = w₁.length
        · rw [getD_snoc_eq _ _ _ _ heq, getD_snoc_eq _ _ _ _ (by omega)]
        · rw [List.getD_eq_default _ _ (by simp; omega),
              List.getD_eq_default _ _ (by simp; omega)]
    · intro g' hg' i hi
      exact hno g' (by simp [hg']) i hi

private def OkGate (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

private def NOkGate (g : Gate) : Prop :=
  OkGate g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

private def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

private lemma normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

private lemma normGate_nok (g : Gate) (h : OkGate g) : NOkGate (normGate g) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := h
  rcases hop with h | h | h
  · subst h; exact ⟨⟨Or.inl rfl, hlen⟩, by simp [normGate]⟩
  · subst h; exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [normGate]⟩
  · subst h
    refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩
    · simp [normGate]
    · simp [normGate]

private lemma wiresFrom_norm (gs : List Gate) (w : List Bool) :
    wiresFrom (gs.map normGate) w = wiresFrom gs w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.map_cons, wiresFrom_cons, wiresFrom_cons, normGate_eval, ih]

private def statVal (w : List Bool) : Bool ⊕ ℕ → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

private def statValid (m : ℕ) : Bool ⊕ ℕ → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

private def simpNot (m : ℕ) : List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ)
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

private def simpAnd (m : ℕ) : List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ)
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] =>
      if j = k then (none, Sum.inr j) else (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

private def simpOr (m : ℕ) : List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ)
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] =>
      if j = k then (none, Sum.inr j) else (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

private def simplifyGate (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ)) :
    Option Gate × (Bool ⊕ ℕ) :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

private lemma simplifyGate_ok (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ)) :
    ∀ g ∈ (simplifyGate op m ins).1, OkGate g := by
  intro g hg
  cases op <;> simp only [simplifyGate] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    split_ifs at hg
    simp only [Option.mem_def, Option.some.injEq] at hg; subst hg; simp [OkGate]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    split_ifs at hg
    simp only [Option.mem_def, Option.some.injEq] at hg; subst hg; simp [OkGate]
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg
    subst hg; simp [OkGate]
  · simp at hg
  · simp at hg

private lemma simplifyGate_op_eq (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ)) :
    ∀ g ∈ (simplifyGate op m ins).1, g.op = op := by
  intro g hg
  cases op <;> simp only [simplifyGate] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    split_ifs at hg
    simp only [Option.mem_def, Option.some.injEq] at hg; subst hg; rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    split_ifs at hg
    simp only [Option.mem_def, Option.some.injEq] at hg; subst hg; rfl
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;> simp [simpNot] at hg
    subst hg; rfl
  · simp at hg
  · simp at hg

private lemma simplifyGate_none_of_const (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ))
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Sum.inl c ∈ ins) :
    (simplifyGate op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplifyGate, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplifyGate, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplifyGate, simpNot]

private lemma simplifyGate_and_false (m : ℕ) (ins : List (Bool ⊕ ℕ))
    (hlen : ins.length ≤ 2) (hf : Sum.inl false ∈ ins) :
    simplifyGate GateOp.and m ins = (none, Sum.inl false) := by
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
  · simp at hf
  · cases a <;> simp_all [simplifyGate, simpAnd]
  · cases a with
    | inl c =>
      cases b with
      | inl d => cases c <;> cases d <;> simp_all [simplifyGate, simpAnd]
      | inr j => cases c <;> simp_all [simplifyGate, simpAnd]
    | inr i =>
      cases b with
      | inl d => cases d <;> simp_all [simplifyGate, simpAnd]
      | inr j => simp at hf
  · simp at hlen

private lemma simplifyGate_or_true (m : ℕ) (ins : List (Bool ⊕ ℕ))
    (hlen : ins.length ≤ 2) (ht : Sum.inl true ∈ ins) :
    simplifyGate GateOp.or m ins = (none, Sum.inl true) := by
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
  · simp at ht
  · cases a <;> simp_all [simplifyGate, simpOr]
  · cases a with
    | inl c =>
      cases b with
      | inl d => cases c <;> cases d <;> simp_all [simplifyGate, simpOr]
      | inr j => cases c <;> simp_all [simplifyGate, simpOr]
    | inr i =>
      cases b with
      | inl d => cases d <;> simp_all [simplifyGate, simpOr]
      | inr j => simp at ht
  · simp at hlen

private lemma simplifyGate_not_const (m : ℕ) (c : Bool) :
    simplifyGate GateOp.not m [Sum.inl c] = (none, Sum.inl (!c)) := rfl

private lemma simplifyGate_sound (op : GateOp)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List (Bool ⊕ ℕ)) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, statValid w.length s) :
    statValid (w.length + (simplifyGate op w.length ins).1.toList.length)
      (simplifyGate op w.length ins).2 ∧
    statVal (wiresFrom (simplifyGate op w.length ins).1.toList w)
      (simplifyGate op w.length ins).2 = op.eval (ins.map (statVal w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplifyGate, simpAnd, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a with
      | inl c =>
        cases b with
        | inl d => simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval]
        | inr j => cases c <;> simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
      | inr i =>
        cases b with
        | inl d => cases d <;> simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
        | inr j =>
          by_cases heq : i = j
          · subst heq; simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
          · simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplifyGate, simpOr, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a with
      | inl c =>
        cases b with
        | inl d => simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval]
        | inr j => cases c <;> simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
      | inr i =>
        cases b with
        | inl d => cases d <;> simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
        | inr j =>
          by_cases heq : i = j
          · subst heq; simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
          · simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplifyGate, simpNot, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplifyGate, simpNot, statValid, statVal, GateOp.eval, wiresFrom]

private def elimStep (m : ℕ) (acc : List (Bool ⊕ ℕ) × List Gate) (g : Gate) :
    List (Bool ⊕ ℕ) × List Gate :=
  let r := simplifyGate g.op (m + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Sum.inl false))
  (acc.1 ++ [r.2], acc.2 ++ r.1.toList)

private def elimPass (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) :
    List (Bool ⊕ ℕ) × List Gate :=
  gs.foldl (elimStep m) acc

private lemma elimPass_nil (m : ℕ) (acc : List (Bool ⊕ ℕ) × List Gate) :
    elimPass m [] acc = acc := rfl

private lemma elimPass_cons (m : ℕ) (g : Gate) (gs : List Gate)
    (acc : List (Bool ⊕ ℕ) × List Gate) :
    elimPass m (g :: gs) acc = elimPass m gs (elimStep m acc g) := rfl

private lemma elimPass_append (m : ℕ) (gs₁ gs₂ : List Gate)
    (acc : List (Bool ⊕ ℕ) × List Gate) :
    elimPass m (gs₁ ++ gs₂) acc = elimPass m gs₂ (elimPass m gs₁ acc) := by
  induction gs₁ generalizing acc with
  | nil => rfl
  | cons g gs ih => simp only [List.cons_append, elimPass_cons, ih]

private lemma elimPass_fst_len (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) :
    (elimPass m gs acc).1.length = acc.1.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp [elimPass]
  | cons g gs ih =>
    rw [elimPass_cons, ih]
    simp [elimStep]
    omega

private lemma elimPass_getD_lt (m k : ℕ) (d : Bool ⊕ ℕ) (gs : List Gate)
    (acc : List (Bool ⊕ ℕ) × List Gate) (hk : k < acc.1.length) :
    (elimPass m gs acc).1.getD k d = acc.1.getD k d := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    rw [elimPass_cons, ih _ (by simp [elimStep]; omega)]
    exact getD_snoc_lt _ _ _ _ hk

private lemma toList_opt_len_le {α : Type*} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

private lemma elimPass_ok (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (h : ∀ g ∈ acc.2, OkGate g) : ∀ g ∈ (elimPass m gs acc).2, OkGate g := by
  induction gs generalizing acc with
  | nil => exact h
  | cons g gs ih =>
    rw [elimPass_cons]
    apply ih
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplifyGate_ok _ _ _ g' (by simpa using h1)

private lemma elimPass_len (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) :
    (elimPass m gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp [elimPass]
  | cons g gs ih =>
    rw [elimPass_cons]
    have h1 := ih (elimStep m acc g)
    have h2 : (elimStep m acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      have := toList_opt_len_le (simplifyGate g.op (m + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
      omega
    simp only [List.length_cons]
    omega

private lemma elimPass_len_lt (m w : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (hnok : ∀ g ∈ gs, NOkGate g) (hw : w < acc.1.length)
    (hc : ∃ c, acc.1.getD w (Sum.inl false) = Sum.inl c)
    (hex : ∃ g ∈ gs, w ∈ g.inputs) :
    (elimPass m gs acc).2.length + 1 ≤ acc.2.length + gs.length := by
  induction gs generalizing acc with
  | nil => rcases hex with ⟨g, hg, _⟩; simp at hg
  | cons g gs ih =>
    rw [elimPass_cons]
    by_cases hwg : w ∈ g.inputs
    · have hok := hnok g (by simp)
      obtain ⟨c, hcw⟩ := hc
      have hnone : (simplifyGate g.op (m + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        apply simplifyGate_none_of_const
        · exact hok.1.1
        · simp; exact hok.1.2
        · intro hnot; simp; exact hok.2 hnot
        · exact ⟨c, List.mem_map.2 ⟨w, hwg, hcw⟩⟩
      have h1 := elimPass_len m gs (elimStep m acc g)
      have hstep : (elimStep m acc g).2.length = acc.2.length := by
        simp only [elimStep, hnone, Option.toList_none, List.append_nil]
      simp only [List.length_cons]
      omega
    · have hex' : ∃ g' ∈ gs, w ∈ g'.inputs := by
        rcases hex with ⟨g', hg', hmem⟩
        rcases List.mem_cons.1 hg' with rfl | hg'
        · exact absurd hmem hwg
        · exact ⟨g', hg', hmem⟩
      have h1 := ih (elimStep m acc g) (fun g' hg' => hnok g' (by simp [hg']))
        (by simp [elimStep]; omega)
        (by
          obtain ⟨c, hcw⟩ := hc
          exact ⟨c, by simp only [elimStep]; rw [getD_snoc_lt _ _ _ _ hw, hcw]⟩)
        hex'
      have h2 : (elimStep m acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_opt_len_le (simplifyGate g.op (m + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      simp only [List.length_cons]
      omega

private lemma elimPass_len_two (m w : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (hnok : ∀ g ∈ gs, NOkGate g) (hw : w < acc.1.length)
    (hc : ∃ c, acc.1.getD w (Sum.inl false) = Sum.inl c)
    (htwo : 2 ≤ (gs.filter fun g => decide (w ∈ g.inputs)).length) :
    (elimPass m gs acc).2.length + 2 ≤ acc.2.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp at htwo
  | cons g gs ih =>
    rw [elimPass_cons]
    by_cases hwg : w ∈ g.inputs
    · have hok := hnok g (by simp)
      obtain ⟨c, hcw⟩ := hc
      have hnone : (simplifyGate g.op (m + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        apply simplifyGate_none_of_const
        · exact hok.1.1
        · simp; exact hok.1.2
        · intro hnot; simp; exact hok.2 hnot
        · exact ⟨c, List.mem_map.2 ⟨w, hwg, hcw⟩⟩
      have hstep : (elimStep m acc g).2.length = acc.2.length := by
        simp only [elimStep, hnone, Option.toList_none, List.append_nil]
      have h1 : 1 ≤ (gs.filter fun g => decide (w ∈ g.inputs)).length := by
        simp only [List.filter_cons, decide_eq_true hwg, ↓reduceIte, List.length_cons] at htwo
        omega
      have hne : (gs.filter fun g => decide (w ∈ g.inputs)) ≠ [] := by
        intro he; rw [he] at h1; simp at h1
      obtain ⟨g', hg'⟩ := List.exists_mem_of_ne_nil _ hne
      have hg'm : g' ∈ gs ∧ w ∈ g'.inputs := by
        have := List.mem_filter.1 hg'
        exact ⟨this.1, of_decide_eq_true this.2⟩
      have hlt := elimPass_len_lt m w gs (elimStep m acc g)
        (fun g'' hg'' => hnok g'' (by simp [hg'']))
        (by simp [elimStep]; omega)
        ⟨c, by simp only [elimStep]; rw [getD_snoc_lt _ _ _ _ hw, hcw]⟩
        ⟨g', hg'm.1, hg'm.2⟩
      simp only [List.length_cons]
      omega
    · have htwo' : 2 ≤ (gs.filter fun g => decide (w ∈ g.inputs)).length := by
        simpa [hwg] using htwo
      have h1 := ih (elimStep m acc g) (fun g' hg' => hnok g' (by simp [hg']))
        (by simp [elimStep]; omega)
        (by
          obtain ⟨c, hcw⟩ := hc
          exact ⟨c, by simp only [elimStep]; rw [getD_snoc_lt _ _ _ _ hw, hcw]⟩)
        htwo'
      have h2 : (elimStep m acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_opt_len_le (simplifyGate g.op (m + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      simp only [List.length_cons]
      omega

private def ElimInv (m : ℕ) (xorig xnew : List Bool) (acc : List (Bool ⊕ ℕ) × List Gate) : Prop :=
  xorig.length = m ∧
  acc.1.length = xnew.length ∧
  ∀ i, statValid (m + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
    statVal (wiresFrom acc.2 xorig) (acc.1.getD i (Sum.inl false)) = xnew.getD i false

private lemma elimInv_step (m : ℕ) (xorig xnew : List Bool)
    (acc : List (Bool ⊕ ℕ) × List Gate) (g : Gate) (hok : OkGate g)
    (hinv : ElimInv m xorig xnew acc) :
    ElimInv m xorig
      (xnew ++ [g.op.eval (g.inputs.map fun i => xnew.getD i false)])
      (elimStep m acc g) := by
  obtain ⟨hxlen, hlen, hall⟩ := hinv
  set w := wiresFrom acc.2 xorig with hw
  have hwlen : w.length = m + acc.2.length := by
    rw [hw, wiresFrom_length, hxlen]
  set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
  have hins_val : ∀ s ∈ ins, statValid w.length s := by
    intro s hs
    obtain ⟨i, _, rfl⟩ := List.mem_map.1 hs
    rw [hwlen]
    exact (hall i).1
  have hins_map : ins.map (statVal w) = g.inputs.map (fun i => xnew.getD i false) := by
    rw [hins, List.map_map]
    apply List.map_congr_left
    intro i _
    exact (hall i).2
  have hsnd := simplifyGate_sound g.op hok.1 w ins (by simp [hins]; exact hok.2) hins_val
  set r := simplifyGate g.op (m + acc.2.length) ins with hr
  have hr_eq : simplifyGate g.op w.length ins = r := by rw [hwlen, hr]
  rw [hr_eq] at hsnd
  refine ⟨hxlen, by simp [elimStep, hlen], ?_⟩
  intro i
  by_cases hi : i < acc.1.length
  · have hget1 : (elimStep m acc g).1.getD i (Sum.inl false) = acc.1.getD i (Sum.inl false) := by
      simp only [elimStep]
      exact getD_snoc_lt _ _ _ _ hi
    rw [hget1, getD_snoc_lt _ _ _ _ (by omega)]
    have hvi := (hall i).1
    have hval := (hall i).2
    refine ⟨?_, ?_⟩
    · cases hs : acc.1.getD i (Sum.inl false) with
      | inl c => trivial
      | inr j =>
        rw [hs] at hvi
        simp only [statValid, elimStep, List.length_append] at hvi ⊢
        omega
    · cases hs : acc.1.getD i (Sum.inl false) with
      | inl c =>
        rw [hs] at hval
        simpa [statVal] using hval
      | inr j =>
        rw [hs] at hvi hval
        simp only [statValid] at hvi
        simp only [statVal, elimStep, wiresFrom_append, ← hw]
        rw [wiresFrom_getD_lt _ _ _ (by omega)]
        exact hval
  · by_cases heq : i = acc.1.length
    · have hget1 : (elimStep m acc g).1.getD i (Sum.inl false) = r.2 := by
        simp only [elimStep, ← hins, ← hr]
        exact getD_snoc_eq _ _ _ _ heq
      rw [hget1, getD_snoc_eq _ _ _ _ (by omega)]
      refine ⟨?_, ?_⟩
      · simpa [elimStep, hwlen, Nat.add_assoc, hr, hins] using hsnd.1
      · simp only [elimStep, wiresFrom_append, ← hw, ← hins, ← hr]
        rw [hsnd.2, hins_map]
    · rw [List.getD_eq_default _ _ (by simp [elimStep]; omega),
          List.getD_eq_default _ _ (by simp; omega)]
      exact ⟨trivial, rfl⟩

private lemma elimInv_pass (m : ℕ) (xorig : List Bool) (gs : List Gate)
    (xnew : List Bool) (acc : List (Bool ⊕ ℕ) × List Gate)
    (hok : ∀ g ∈ gs, OkGate g) (hinv : ElimInv m xorig xnew acc) :
    ElimInv m xorig (wiresFrom gs xnew) (elimPass m gs acc) := by
  induction gs generalizing xnew acc with
  | nil => exact hinv
  | cons g gs ih =>
    rw [wiresFrom_cons, elimPass_cons]
    exact ih _ _ (fun g' hg' => hok g' (by simp [hg']))
      (elimInv_step m xorig xnew acc g (hok g (by simp)) hinv)

private def initId (m : ℕ) : List (Bool ⊕ ℕ) :=
  List.ofFn fun i : Fin m => Sum.inr (i : ℕ)

private def initVar (m : ℕ) (v : Fin m) (b : Bool) : List (Bool ⊕ ℕ) :=
  List.ofFn fun i : Fin m => if i = v then Sum.inl b else Sum.inr (i : ℕ)

private lemma elimInv_initId (m : ℕ) (x : Fin m → Bool) :
    ElimInv m (List.ofFn x) (List.ofFn x) (initId m, []) := by
  refine ⟨by simp, by simp [initId], ?_⟩
  intro i
  by_cases hi : i < m
  · rw [initId, ofFn_getD_lt _ _ _ hi]
    simp [statValid, statVal, wiresFrom_nil, hi]
  · rw [List.getD_eq_default _ _ (by simp [initId]; omega),
        List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

private lemma elimInv_initVar (m : ℕ) (v : Fin m) (b : Bool) (x : Fin m → Bool) :
    ElimInv m (List.ofFn x) (List.ofFn (Function.update x v b)) (initVar m v b, []) := by
  refine ⟨by simp, by simp [initVar], ?_⟩
  intro i
  by_cases hi : i < m
  · have hget : (initVar m v b).getD i (Sum.inl false) =
        if (⟨i, hi⟩ : Fin m) = v then Sum.inl b else Sum.inr i := by
      rw [initVar, ofFn_getD_lt _ _ _ hi]
    rw [hget]
    by_cases heq : (⟨i, hi⟩ : Fin m) = v
    · simp only [heq, ↓reduceIte, statValid, statVal]
      rw [ofFn_getD_lt _ _ _ hi, heq, Function.update_self]
      exact ⟨trivial, rfl⟩
    · simp only [heq, ↓reduceIte, statValid, statVal, wiresFrom_nil]
      refine ⟨by omega, ?_⟩
      rw [ofFn_getD_lt _ _ _ hi, ofFn_getD_lt _ _ _ hi, Function.update_of_ne heq]
  · rw [List.getD_eq_default _ _ (by simp [initVar]; omega),
        List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

private lemma list_split_unique_filter {α : Type*} (p : α → Bool) (l : List α)
    (h : (l.filter p).length = 1) :
    ∃ l₁ a l₂, l = l₁ ++ [a] ++ l₂ ∧ p a = true ∧
      (∀ x ∈ l₁, p x = false) ∧ (∀ x ∈ l₂, p x = false) := by
  induction l with
  | nil => simp at h
  | cons x xs ih =>
    cases hpx : p x with
    | true =>
      have h0 : (xs.filter p).length = 0 := by
        simp only [List.filter_cons, hpx, ↓reduceIte, List.length_cons] at h
        omega
      have hnil : xs.filter p = [] := List.eq_nil_of_length_eq_zero h0
      refine ⟨[], x, xs, rfl, hpx, by simp, ?_⟩
      intro y hy
      by_contra hpy
      have hpyt : p y = true := by cases hp : p y <;> simp_all
      have : y ∈ xs.filter p := List.mem_filter.2 ⟨hy, hpyt⟩
      rw [hnil] at this
      simp at this
    | false =>
      have h1 : (xs.filter p).length = 1 := by simpa [hpx] using h
      obtain ⟨l₁, a, l₂, rfl, hpa, hl₁, hl₂⟩ := ih h1
      refine ⟨x :: l₁, a, l₂, by simp, hpa, ?_, hl₂⟩
      intro y hy
      rcases List.mem_cons.1 hy with rfl | hy'
      · exact hpx
      · exact hl₁ y hy'

private def DependsOn (F : (Fin 6 → Bool) → Bool) (v : Fin 6) : Prop :=
  ∃ x : Fin 6 → Bool, F (Function.update x v false) ≠ F (Function.update x v true)

private def NonConst (F : (Fin 6 → Bool) → Bool) : Prop :=
  ∃ x y : Fin 6 → Bool, F x ≠ F y

private def Restrict (F : (Fin 6 → Bool) → Bool) (v : Fin 6) (b : Bool) : (Fin 6 → Bool) → Bool :=
  fun x => F (Function.update x v b)

private def IsMin (F : (Fin 6 → Bool) → Bool) (C : Circuit) : Prop :=
  FanInTwo C ∧ (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = F x) ∧
    ∀ C' : Circuit, FanInTwo C' → (∀ x : Fin 6 → Bool, C'.eval (List.ofFn x) = F x) → C.size ≤ C'.size

private lemma exists_min_of_hasCircuitSize {F : (Fin 6 → Bool) → Bool} {s : ℕ}
    (h : HasCircuitSize 6 F s) : ∃ C : Circuit, IsMin F C ∧ C.size ≤ s := by
  classical
  have hex : ∃ n, HasCircuitSize 6 F n := ⟨s, h⟩
  let n0 := Nat.find hex
  have hn0 : HasCircuitSize 6 F n0 := Nat.find_spec hex
  have hle : n0 ≤ s := Nat.find_min' hex h
  obtain ⟨C, hok, hsz, hev⟩ := hn0
  refine ⟨C, ⟨hok, hev, ?_⟩, le_trans hsz hle⟩
  intro C' hok' hev'
  have hmin : n0 ≤ C'.size := Nat.find_min' hex ⟨C', hok', le_refl _, hev'⟩
  omega

private lemma elim_one_var {s : ℕ} {F : (Fin 6 → Bool) → Bool} (v : Fin 6) (b : Bool)
    (hC : HasCircuitSize 6 F s) (hdep : DependsOn F v) (hnc : NonConst (Restrict F v b)) :
    1 ≤ s ∧ HasCircuitSize 6 (Restrict F v b) (s - 1) := by
  obtain ⟨C, hok, hsz, hev⟩ := hC
  set gs := C.gates.map normGate with hgs
  have hnok : ∀ g ∈ gs, NOkGate g := by
    intro g hg; obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg; exact normGate_nok g0 (hok g0 hg0)
  have hout_ne : C.output ≠ (v : ℕ) := by
    intro heq
    obtain ⟨x, x', hne⟩ := hnc
    have h1 := hev (Function.update x v b)
    have h2 := hev (Function.update x' v b)
    have hw : ∀ z : Fin 6 → Bool,
        (C.wires (List.ofFn (Function.update z v b))).getD (v : ℕ) false = b := by
      intro z
      show (wiresFrom C.gates (List.ofFn (Function.update z v b))).getD (v : ℕ) false = b
      rw [wiresFrom_getD_lt _ _ _ (by simp), ofFn_getD_lt _ _ _ v.isLt]
      simp
    have e1 : F (Function.update x v b) = b := by
      rw [← h1]; show (C.wires _).getD C.output false = b; rw [heq]; exact hw x
    have e2 : F (Function.update x' v b) = b := by
      rw [← h2]; show (C.wires _).getD C.output false = b; rw [heq]; exact hw x'
    exact hne (e1.trans e2.symm)
  have hex : ∃ g ∈ gs, (v : ℕ) ∈ g.inputs := by
    by_contra hno
    have hno' : ∀ g ∈ gs, (v : ℕ) ∉ g.inputs := fun g hg hv => hno ⟨g, hg, hv⟩
    obtain ⟨x, hne⟩ := hdep
    have hag := wiresFrom_agree gs {(v : ℕ)}
      (List.ofFn (Function.update x v false))
      (List.ofFn (Function.update x v true))
      (by simp) (by intro u hu; simp at hu; subst hu; simp)
      (by
        intro i hi; simp at hi
        by_cases hlt : i < 6
        · have hne' : (⟨i, hlt⟩ : Fin 6) ≠ v := by intro h; apply hi; exact congrArg Fin.val h
          rw [ofFn_getD_lt _ _ _ hlt, ofFn_getD_lt _ _ _ hlt,
              Function.update_of_ne hne', Function.update_of_ne hne']
        · rw [List.getD_eq_default _ _ (by simp; omega),
              List.getD_eq_default _ _ (by simp; omega)])
      (by intro g hg i hi hmem; simp at hmem; subst hmem; exact hno' g hg hi)
    have hEq := hag.2 C.output (by simpa using hout_ne)
    rw [hgs, wiresFrom_norm, wiresFrom_norm] at hEq
    exact hne ((hev _).symm.trans (hEq.trans (hev _)))
  set acc := elimPass 6 gs (initVar 6 v b, []) with hacc
  have hlen : acc.2.length + 1 ≤ gs.length := by
    have := elimPass_len_lt 6 (v : ℕ) gs (initVar 6 v b, []) hnok
      (by simp [initVar]) ⟨b, by rw [initVar, ofFn_getD_lt _ _ _ v.isLt]; simp⟩ hex
    rw [← hacc] at this; simpa using this
  have hgs_len : gs.length = C.gates.length := by simp [hgs]
  have hsz' : C.gates.length ≤ s := hsz
  have hval : ∀ x : Fin 6 → Bool,
      statVal (wiresFrom acc.2 (List.ofFn x)) (acc.1.getD C.output (Sum.inl false)) =
        Restrict F v b x := by
    intro x
    have hinv := elimInv_pass 6 (List.ofFn x) gs _ (initVar 6 v b, [])
      (fun g hg => (hnok g hg).1) (elimInv_initVar 6 v b x)
    rw [← hacc] at hinv
    rw [(hinv.2.2 C.output).2, hgs, wiresFrom_norm]
    exact hev (Function.update x v b)
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    obtain ⟨x, x', hne⟩ := hnc
    have hx := hval x; have hx' := hval x'
    rw [hst] at hx hx'
    exact absurd (hx.symm.trans hx') hne
  | inr j =>
    refine ⟨by omega, ⟨acc.2, j⟩, elimPass_ok 6 gs _ (by simp), ?_, ?_⟩
    · show acc.2.length ≤ s - 1; omega
    · intro x; have := hval x; rw [hst] at this; exact this


private def CleanGate (k : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or →
    ∃ a b, g.inputs = [a, b] ∧ a < 6 + k ∧ b < 6 + k ∧ a ≠ b) ∧
  (g.op = GateOp.not → ∃ a, g.inputs = [a] ∧ a < 6 + k) ∧
  NOkGate g

private def CleanCircuit (F : (Fin 6 → Bool) → Bool) (gs : List Gate) (out : ℕ) : Prop :=
  (∀ k (hk : k < gs.length), CleanGate k gs[k]) ∧
  out < 6 + gs.length ∧
  (∀ x : Fin 6 → Bool, (wiresFrom gs (List.ofFn x)).getD out false = F x) ∧
  (∀ k, k < gs.length → 6 + k ≠ out → ∃ j, ∃ hj : j < gs.length, 6 + k ∈ gs[j].inputs) ∧
  (∀ v : Fin 6, ¬ DependsOn F v → ∀ g ∈ gs, (v : ℕ) ∉ g.inputs) ∧
  (∀ v : Fin 6, DependsOn F v → out ≠ (v : ℕ) → ∃ g ∈ gs, (v : ℕ) ∈ g.inputs) ∧
  (∀ C' : Circuit, FanInTwo C' → (∀ x : Fin 6 → Bool, C'.eval (List.ofFn x) = F x) → gs.length ≤ C'.size)

private lemma elimPass_id_eq (gs : List Gate) (hnok : ∀ g ∈ gs, NOkGate g)
    (heq : (elimPass 6 gs (initId 6, [])).2.length = gs.length) :
    ∀ k (hk : k < gs.length), CleanGate k gs[k] := by
  have hgen : ∀ (l₁ : List Gate) (l₂ : List Gate),
      (∀ g ∈ l₁ ++ l₂, NOkGate g) →
      (elimPass 6 (l₁ ++ l₂) (initId 6, [])).2.length = (l₁ ++ l₂).length →
      (elimPass 6 l₁ (initId 6, [])).2.length = l₁.length ∧
      (∀ i < 6 + l₁.length, (elimPass 6 l₁ (initId 6, [])).1.getD i (Sum.inl false) = Sum.inr i) ∧
      (∀ k (hk : k < l₁.length), CleanGate k l₁[k]) := by
    intro l₁
    induction l₁ using List.reverseRecOn with
    | nil =>
      intro l₂ _ _
      refine ⟨rfl, ?_, by intro k hk; simp at hk⟩
      intro i hi
      simp only [List.length_nil, add_zero] at hi
      rw [elimPass_nil, initId, ofFn_getD_lt _ _ _ hi]
    | append_singleton l₁ g ih =>
      intro l₂ hnok' heq'
      have hre : (l₁ ++ [g]) ++ l₂ = l₁ ++ (g :: l₂) := by simp
      rw [hre] at hnok' heq'
      have ⟨hlen1, hid1, hclean1⟩ := ih (g :: l₂) hnok' heq'
      set acc₁ := elimPass 6 l₁ (initId 6, []) with hacc₁
      set acc₂ := elimStep 6 acc₁ g with hacc₂
      have hacc₁_fst : acc₁.1.length = 6 + l₁.length := by
        rw [hacc₁, elimPass_fst_len]; simp [initId]
      have hlen_tail := elimPass_len 6 l₂ acc₂
      have hstep_le : acc₂.2.length ≤ acc₁.2.length + 1 := by
        simp only [hacc₂, elimStep, List.length_append]
        have := toList_opt_len_le (simplifyGate g.op (6 + acc₁.2.length)
          (g.inputs.map fun i => acc₁.1.getD i (Sum.inl false))).1
        omega
      have htot : (elimPass 6 l₂ acc₂).2.length = l₁.length + 1 + l₂.length := by
        have : elimPass 6 (l₁ ++ (g :: l₂)) (initId 6, []) = elimPass 6 l₂ acc₂ := by
          rw [elimPass_append, ← hacc₁, elimPass_cons, ← hacc₂]
        rw [← this, heq']; simp; omega
      have hstep_eq : acc₂.2.length = l₁.length + 1 := by omega
      have hsome : (simplifyGate g.op (6 + acc₁.2.length)
          (g.inputs.map fun i => acc₁.1.getD i (Sum.inl false))).1.isSome = true := by
        cases hopt : (simplifyGate g.op (6 + acc₁.2.length)
            (g.inputs.map fun i => acc₁.1.getD i (Sum.inl false))).1 with
        | none =>
          have : acc₂.2.length = acc₁.2.length := by
            simp only [hacc₂, elimStep, hopt, Option.toList_none, List.append_nil]
          omega
        | some _ => rfl
      have hnokg : NOkGate g := hnok' g (by simp)
      have hget : ∀ i, acc₁.1.getD i (Sum.inl false) =
          if i < 6 + l₁.length then Sum.inr i else Sum.inl false := by
        intro i
        by_cases hi : i < 6 + l₁.length
        · simp only [hi, ↓reduceIte]; exact hid1 i hi
        · simp only [hi, ↓reduceIte]; exact List.getD_eq_default _ _ (by omega)
      have hclean_g : CleanGate l₁.length g := by
        refine ⟨?_, ?_, hnokg⟩
        · intro hop
          rcases hgi : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
          · rcases hop with h | h <;> rw [h, hgi] at hsome <;> simp [simplifyGate, simpAnd, simpOr] at hsome
          · rcases hop with h | h <;> rw [h, hgi] at hsome <;>
              simp only [List.map_cons, List.map_nil, hget, simplifyGate, simpAnd, simpOr] at hsome <;>
              split_ifs at hsome <;> simp at hsome
          · rcases hop with h | h
            · rw [h, hgi] at hsome
              simp only [List.map_cons, List.map_nil, hget, simplifyGate, simpAnd] at hsome
              by_cases ha : a < 6 + l₁.length
              · by_cases hb : b < 6 + l₁.length
                · simp only [ha, hb, ↓reduceIte] at hsome
                  by_cases hab : a = b
                  · simp [hab] at hsome
                  · exact ⟨a, b, rfl, ha, hb, hab⟩
                · simp only [ha, hb, ↓reduceIte] at hsome; simp at hsome
              · simp only [ha, ↓reduceIte] at hsome; split_ifs at hsome <;> simp at hsome
            · rw [h, hgi] at hsome
              simp only [List.map_cons, List.map_nil, hget, simplifyGate, simpOr] at hsome
              by_cases ha : a < 6 + l₁.length
              · by_cases hb : b < 6 + l₁.length
                · simp only [ha, hb, ↓reduceIte] at hsome
                  by_cases hab : a = b
                  · simp [hab] at hsome
                  · exact ⟨a, b, rfl, ha, hb, hab⟩
                · simp only [ha, hb, ↓reduceIte] at hsome; simp at hsome
              · simp only [ha, ↓reduceIte] at hsome; split_ifs at hsome <;> simp at hsome
          · have := hnokg.1.2; rw [hgi] at this; simp at this
        · intro hnot
          have hlen1 := hnokg.2 hnot
          rcases hgi : g.inputs with _ | ⟨a, _ | ⟨b, rest⟩⟩
          · rw [hnot, hgi] at hsome; simp [simplifyGate, simpNot] at hsome
          · rw [hnot, hgi] at hsome
            simp only [List.map_cons, List.map_nil, hget, simplifyGate, simpNot] at hsome
            by_cases ha : a < 6 + l₁.length
            · exact ⟨a, rfl, ha⟩
            · simp [ha] at hsome
          · rw [hgi] at hlen1; simp at hlen1
      have hr2 : (simplifyGate g.op (6 + acc₁.2.length)
          (g.inputs.map fun i => acc₁.1.getD i (Sum.inl false))).2 = Sum.inr (6 + l₁.length) := by
        rcases hnokg.1.1 with hop | hop | hop
        · obtain ⟨a, b, hgi, ha, hb, hab⟩ := hclean_g.1 (Or.inl hop)
          have hop' : g.op = GateOp.and := hop
          rw [hop', hgi, hlen1]
          simp only [List.map_cons, List.map_nil, hget, ha, hb, ↓reduceIte, simplifyGate, simpAnd, hab]
        · obtain ⟨a, b, hgi, ha, hb, hab⟩ := hclean_g.1 (Or.inr hop)
          have hop' : g.op = GateOp.or := hop
          rw [hop', hgi, hlen1]
          simp only [List.map_cons, List.map_nil, hget, ha, hb, ↓reduceIte, simplifyGate, simpOr, hab]
        · obtain ⟨a, hgi, ha⟩ := hclean_g.2.1 hop
          have hop' : g.op = GateOp.not := hop
          rw [hop', hgi, hlen1]
          simp only [List.map_cons, List.map_nil, hget, ha, ↓reduceIte, simplifyGate, simpNot]
      have heq_acc2 : elimPass 6 (l₁ ++ [g]) (initId 6, []) = acc₂ := by
        rw [elimPass_append, ← hacc₁, elimPass_cons, elimPass_nil, ← hacc₂]
      refine ⟨by rw [heq_acc2, hstep_eq]; simp, ?_, ?_⟩
      · intro i hi
        rw [heq_acc2]
        simp only [List.length_append, List.length_singleton] at hi
        by_cases hlt : i < 6 + l₁.length
        · simp only [hacc₂, elimStep]
          rw [getD_snoc_lt _ _ _ _ (by omega)]
          exact hid1 i hlt
        · have heqi : i = 6 + l₁.length := by omega
          subst heqi
          simp only [hacc₂, elimStep]
          rw [getD_snoc_eq _ _ _ _ hacc₁_fst.symm, hr2]
      · intro k hk
        simp only [List.length_append, List.length_singleton] at hk
        by_cases hlt : k < l₁.length
        · rw [List.getElem_append_left hlt]; exact hclean1 k hlt
        · have hk' : k = l₁.length := by omega
          subst hk'
          simp [hclean_g]
  have := hgen gs [] (by simpa using hnok) (by simpa using heq)
  exact this.2.2

private lemma clean_of_min {F : (Fin 6 → Bool) → Bool} {C : Circuit}
    (hmin : IsMin F C) (hnc : NonConst F) :
    CleanCircuit F (C.gates.map normGate) C.output := by
  obtain ⟨hok, hev, hle⟩ := hmin
  set gs := C.gates.map normGate with hgs
  have hnok : ∀ g ∈ gs, NOkGate g := by
    intro g hg; obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg; exact normGate_nok g0 (hok g0 hg0)
  have hgs_len : gs.length = C.size := by simp [hgs, Circuit.size]
  have hev_gs : ∀ x : Fin 6 → Bool, (wiresFrom gs (List.ofFn x)).getD C.output false = F x := by
    intro x; rw [hgs, wiresFrom_norm]; exact hev x
  have hout_lt : C.output < 6 + gs.length := by
    by_contra hge
    obtain ⟨x, y, hxy⟩ := hnc
    have hx : F x = false := by
      rw [← hev_gs x, List.getD_eq_default _ _ (by rw [wiresFrom_length]; simp; omega)]
    have hy : F y = false := by
      rw [← hev_gs y, List.getD_eq_default _ _ (by rw [wiresFrom_length]; simp; omega)]
    exact hxy (hx.trans hy.symm)
  have hacc_len : (elimPass 6 gs (initId 6, [])).2.length = gs.length := by
    set acc := elimPass 6 gs (initId 6, []) with hacc
    have hle1 : acc.2.length ≤ gs.length := by
      have := elimPass_len 6 gs (initId 6, []); rw [← hacc] at this; simpa using this
    have hval : ∀ x : Fin 6 → Bool,
        statVal (wiresFrom acc.2 (List.ofFn x)) (acc.1.getD C.output (Sum.inl false)) = F x := by
      intro x
      have hinv := elimInv_pass 6 (List.ofFn x) gs _ (initId 6, [])
        (fun g hg => (hnok g hg).1) (elimInv_initId 6 x)
      rw [← hacc] at hinv; rw [(hinv.2.2 C.output).2]; exact hev_gs x
    cases hst : acc.1.getD C.output (Sum.inl false) with
    | inl c =>
      obtain ⟨x, y, hxy⟩ := hnc
      have hx := hval x; have hy := hval y; rw [hst] at hx hy
      exact absurd (hx.symm.trans hy) hxy
    | inr j =>
      have hge1 : C.size ≤ acc.2.length :=
        hle ⟨acc.2, j⟩ (elimPass_ok 6 gs _ (by simp)) (fun x => by have := hval x; rw [hst] at this; exact this)
      omega
  have hclean_gates := elimPass_id_eq gs hnok hacc_len
  refine ⟨hclean_gates, hout_lt, hev_gs, ?_, ?_, ?_, ?_⟩
  · intro k hk hne_out
    by_contra hno
    have hno' : ∀ j (hj : j < gs.length), 6 + k ∉ gs[j].inputs := fun j hj hm => hno ⟨j, hj, hm⟩
    set gs' := gs.set k ⟨GateOp.or, []⟩ with hgs'
    have hgs'_len : gs'.length = gs.length := by simp [hgs']
    have hgs'_ok : ∀ g ∈ gs', NOkGate g := by
      intro g hg
      rw [hgs'] at hg
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hg
      by_cases hjk : j = k
      · subst hjk; simp [NOkGate, OkGate]
      · simp only [List.getElem_set_ne (Ne.symm hjk)]; exact hnok _ (List.getElem_mem _)
    have hgs'_ev : ∀ x : Fin 6 → Bool, (wiresFrom gs' (List.ofFn x)).getD C.output false = F x := by
      intro x
      have hsp1 : gs = gs.take k ++ gs[k] :: gs.drop (k + 1) := by
        conv_lhs => rw [← List.take_append_drop k gs]
        rw [List.drop_eq_getElem_cons hk]
      have hsp2 : gs' = gs.take k ++ ⟨GateOp.or, []⟩ :: gs.drop (k + 1) := by
        rw [hgs', List.set_eq_take_cons_drop _ hk]
      rw [hsp2, wiresFrom_append]
      set w0 := wiresFrom (gs.take k) (List.ofFn x)
      have hw0_len : w0.length = 6 + k := by
        simp [w0, wiresFrom_length, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)]
      have hag := wiresFrom_agree (gs.drop (k + 1)) {6 + k}
        (wiresFrom [⟨GateOp.or, []⟩] w0) (wiresFrom [gs[k]] w0)
        (by simp [wiresFrom_length])
        (by intro u hu; simp at hu; subst hu; simp [wiresFrom_length, hw0_len])
        (by
          intro i hi; simp at hi
          simp only [wiresFrom_cons, wiresFrom_nil]
          rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)])
        (by
          intro g hg i hi hmem; simp at hmem; subst hmem
          obtain ⟨d, hd, rfl⟩ := List.mem_iff_getElem.1 hg
          have hidx : k + 1 + d < gs.length := by simp at hd; omega
          have hget : (gs.drop (k + 1))[d] = gs[k + 1 + d] := by simp
          rw [hget] at hi
          exact hno' (k + 1 + d) hidx hi)
      have hEq := hag.2 C.output (by simpa using hne_out.symm)
      have hlhs : wiresFrom (gs.drop (k + 1)) (wiresFrom [⟨GateOp.or, []⟩] w0) =
          wiresFrom (⟨GateOp.or, []⟩ :: gs.drop (k + 1)) w0 := by
        rw [← wiresFrom_append]; rfl
      have hrhs : wiresFrom (gs.drop (k + 1)) (wiresFrom [gs[k]] w0) =
          wiresFrom (gs[k] :: gs.drop (k + 1)) w0 := by
        rw [← wiresFrom_append]; rfl
      rw [hlhs, hrhs] at hEq
      rw [hEq, ← wiresFrom_append, ← hsp1]
      exact hev_gs x
    set acc' := elimPass 6 gs' (initId 6, []) with hacc'
    have hlt_acc' : acc'.2.length + 1 ≤ gs'.length := by
      have hsp2 : gs' = gs.take k ++ ⟨GateOp.or, []⟩ :: gs.drop (k + 1) := by
        rw [hgs', List.set_eq_take_cons_drop _ hk]
      have h1 : (elimPass 6 (gs.take k) (initId 6, [])).2.length ≤ (gs.take k).length := by
        have := elimPass_len 6 (gs.take k) (initId 6, []); simpa using this
      set a1 := elimPass 6 (gs.take k) (initId 6, [])
      have hstep : (elimStep 6 a1 ⟨GateOp.or, []⟩).2.length = a1.2.length := by
        simp [elimStep, simplifyGate, simpOr]
      have h2 := elimPass_len 6 (gs.drop (k + 1)) (elimStep 6 a1 ⟨GateOp.or, []⟩)
      have hacc'_eq : acc' = elimPass 6 (gs.drop (k + 1)) (elimStep 6 a1 ⟨GateOp.or, []⟩) := by
        rw [hacc', hsp2, elimPass_append, elimPass_cons]
      rw [hacc'_eq]
      have hlen_sp : gs'.length = (gs.take k).length + 1 + (gs.drop (k + 1)).length := by
        rw [hsp2]; simp; omega
      omega
    have hval' : ∀ x : Fin 6 → Bool,
        statVal (wiresFrom acc'.2 (List.ofFn x)) (acc'.1.getD C.output (Sum.inl false)) = F x := by
      intro x
      have hinv := elimInv_pass 6 (List.ofFn x) gs' _ (initId 6, [])
        (fun g hg => (hgs'_ok g hg).1) (elimInv_initId 6 x)
      rw [← hacc'] at hinv; rw [(hinv.2.2 C.output).2]; exact hgs'_ev x
    cases hst : acc'.1.getD C.output (Sum.inl false) with
    | inl c =>
      obtain ⟨x, y, hxy⟩ := hnc
      have hx := hval' x; have hy := hval' y; rw [hst] at hx hy
      exact hxy (hx.symm.trans hy)
    | inr j =>
      have hge1 : C.size ≤ acc'.2.length :=
        hle ⟨acc'.2, j⟩ (elimPass_ok 6 gs' _ (by simp)) (fun x => by have := hval' x; rw [hst] at this; exact this)
      omega
  · intro v hndep g hg hv
    have hrf : ∀ x : Fin 6 → Bool, Restrict F v false x = F x := by
      intro x
      have heq : F (Function.update x v false) = F (Function.update x v true) := by
        by_contra hne; exact hndep ⟨x, hne⟩
      cases hxv : x v with
      | false =>
        have hupd : Function.update x v false = x := by
          funext i; by_cases hi : i = v
          · subst hi; simp [hxv]
          · simp [Function.update_of_ne hi]
        simp only [Restrict, hupd]
      | true =>
        have hupd : Function.update x v true = x := by
          funext i; by_cases hi : i = v
          · subst hi; simp [hxv]
          · simp [Function.update_of_ne hi]
        rw [Restrict, heq, hupd]
    set acc := elimPass 6 gs (initVar 6 v false, []) with hacc
    have hlen : acc.2.length + 1 ≤ gs.length := by
      have := elimPass_len_lt 6 (v : ℕ) gs (initVar 6 v false, []) hnok
        (by simp [initVar]) ⟨false, by rw [initVar, ofFn_getD_lt _ _ _ v.isLt]; simp⟩ ⟨g, hg, hv⟩
      rw [← hacc] at this; simpa using this
    have hval : ∀ x : Fin 6 → Bool,
        statVal (wiresFrom acc.2 (List.ofFn x)) (acc.1.getD C.output (Sum.inl false)) = F x := by
      intro x
      have hinv := elimInv_pass 6 (List.ofFn x) gs _ (initVar 6 v false, [])
        (fun g' hg' => (hnok g' hg').1) (elimInv_initVar 6 v false x)
      rw [← hacc] at hinv; rw [(hinv.2.2 C.output).2, hev_gs]; exact hrf x
    cases hst : acc.1.getD C.output (Sum.inl false) with
    | inl c =>
      obtain ⟨x, y, hxy⟩ := hnc
      have hx := hval x; have hy := hval y; rw [hst] at hx hy
      exact hxy (hx.symm.trans hy)
    | inr j =>
      have hge1 : C.size ≤ acc.2.length :=
        hle ⟨acc.2, j⟩ (elimPass_ok 6 gs _ (by simp)) (fun x => by have := hval x; rw [hst] at this; exact this)
      omega
  · intro v hdep hout_ne
    by_contra hno
    have hno' : ∀ g ∈ gs, (v : ℕ) ∉ g.inputs := fun g hg hv => hno ⟨g, hg, hv⟩
    obtain ⟨x, hne⟩ := hdep
    have hag := wiresFrom_agree gs {(v : ℕ)}
      (List.ofFn (Function.update x v false)) (List.ofFn (Function.update x v true))
      (by simp) (by intro u hu; simp at hu; subst hu; simp)
      (by
        intro i hi; simp at hi
        by_cases hlt : i < 6
        · have hne' : (⟨i, hlt⟩ : Fin 6) ≠ v := by intro h; apply hi; exact congrArg Fin.val h
          rw [ofFn_getD_lt _ _ _ hlt, ofFn_getD_lt _ _ _ hlt,
              Function.update_of_ne hne', Function.update_of_ne hne']
        · rw [List.getD_eq_default _ _ (by simp; omega),
              List.getD_eq_default _ _ (by simp; omega)])
      (by intro g hg i hi hmem; simp at hmem; subst hmem; exact hno' g hg hi)
    have hEq := hag.2 C.output (by simpa using hout_ne)
    exact hne ((hev_gs _).symm.trans (hEq.trans (hev_gs _)))
  · intro C' hok' hev'
    rw [hgs_len]; exact hle C' hok' hev'

private lemma clean_out_ge6 {F : (Fin 6 → Bool) → Bool} {gs : List Gate} {out : ℕ}
    (hcl : CleanCircuit F gs out) {v₁ v₂ : Fin 6} (hne : v₁ ≠ v₂)
    (h1 : DependsOn F v₁) (h2 : DependsOn F v₂) : 6 ≤ out := by
  by_contra hlt
  have hlt8 : out < 6 := by omega
  let w : Fin 6 := ⟨out, hlt8⟩
  have hpick : ∃ v : Fin 6, DependsOn F v ∧ v ≠ w := by
    by_cases h1w : v₁ = w
    · exact ⟨v₂, h2, by intro h; exact hne (h1w.trans h.symm)⟩
    · exact ⟨v₁, h1, h1w⟩
  obtain ⟨v, ⟨x, hx⟩, hvw⟩ := hpick
  have hev0 := hcl.2.2.1 (Function.update x v false)
  have hev1 := hcl.2.2.1 (Function.update x v true)
  rw [wiresFrom_getD_lt _ _ _ (by simp; omega), ofFn_getD_lt _ _ _ hlt8,
      Function.update_of_ne hvw.symm] at hev0 hev1
  exact hx (hev0.symm.trans hev1)

private def usedWires (gs : List Gate) : List ℕ :=
  gs.flatMap fun g => g.inputs

private def isNotOp : GateOp → Bool
  | GateOp.not => true
  | _ => false

private lemma isNotOp_eq_true (op : GateOp) : isNotOp op = true ↔ op = GateOp.not := by
  cases op <;> simp [isNotOp]

private lemma list_nodup_of_toFinset_card {α : Type*} [DecidableEq α] (l : List α)
    (h : l.toFinset.card = l.length) : l.Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons a rest ih =>
    rw [List.nodup_cons]
    by_cases ha : a ∈ rest
    · have hsub : (a :: rest).toFinset = rest.toFinset := by
        ext x; simp only [List.mem_toFinset, List.mem_cons]
        exact ⟨fun hx => hx.elim (fun e => e ▸ ha) id, fun hx => Or.inr hx⟩
      have hle : rest.toFinset.card ≤ rest.length := List.toFinset_card_le rest
      rw [hsub, List.length_cons] at h
      omega
    · refine ⟨ha, ih ?_⟩
      have hcard : (a :: rest).toFinset.card = rest.toFinset.card + 1 := by
        rw [List.toFinset_cons, Finset.card_insert_of_notMem (by simpa using ha)]
      rw [hcard, List.length_cons] at h
      omega

private lemma clean_usedWires_len {F : (Fin 6 → Bool) → Bool} {gs : List Gate} {out : ℕ}
    (hcl : CleanCircuit F gs out) :
    (usedWires gs).length + (gs.filter fun g => isNotOp g.op).length = 2 * gs.length := by
  have hgen : ∀ (l : List Gate),
      (∀ g ∈ l, (g.op = GateOp.not → g.inputs.length = 1) ∧
                (g.op ≠ GateOp.not → g.inputs.length = 2)) →
      (l.flatMap fun g => g.inputs).length + (l.filter fun g => isNotOp g.op).length =
        2 * l.length := by
    intro l hl
    induction l with
    | nil => simp
    | cons g rest ih =>
      have hg := hl g (by simp)
      have hih := ih (fun g' hg' => hl g' (by simp [hg']))
      cases hno : isNotOp g.op with
      | true =>
        have hn : g.op = GateOp.not := (isNotOp_eq_true g.op).1 hno
        simp only [List.flatMap_cons, List.length_append, List.filter_cons,
          hno, ↓reduceIte, List.length_cons, hg.1 hn]
        omega
      | false =>
        have hnn : g.op ≠ GateOp.not := fun h => by rw [(isNotOp_eq_true g.op).2 h] at hno; simp at hno
        simp only [List.flatMap_cons, List.length_append, List.filter_cons,
          hno, Bool.false_eq_true, ↓reduceIte, List.length_cons, hg.2 hnn]
        omega
  apply hgen
  intro g hg
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hg
  have hcg := hcl.1 k hk
  refine ⟨fun hn => ?_, fun hnn => ?_⟩
  · obtain ⟨a, ha, _⟩ := hcg.2.1 hn; simp [ha]
  · rcases hcg.2.2.1.1 with hop | hop | hop
    · obtain ⟨a, b, hab, _⟩ := hcg.1 (Or.inl hop); simp [hab]
    · obtain ⟨a, b, hab, _⟩ := hcg.1 (Or.inr hop); simp [hab]
    · exact absurd hop hnn

private lemma clean_slot_count {F : (Fin 6 → Bool) → Bool} {gs : List Gate} {out : ℕ}
    (hcl : CleanCircuit F gs out) (hout : 6 ≤ out) (S : Finset (Fin 6))
    (hS : ∀ v ∈ S, DependsOn F v) :
    S.card + (gs.filter fun g => isNotOp g.op).length ≤ gs.length + 1 ∧
    (S.card + (gs.filter fun g => isNotOp g.op).length = gs.length + 1 →
      (usedWires gs).Nodup) := by
  have hpos : 1 ≤ gs.length := by have := hcl.2.1; omega
  let W1 : Finset ℕ := S.image Fin.val
  let W2 : Finset ℕ := ((Finset.range gs.length).image (· + 6)).erase out
  have hdisj : Disjoint W1 W2 := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.1 hx1
    have hx2' := Finset.mem_of_mem_erase hx2
    obtain ⟨k, _, hk⟩ := Finset.mem_image.1 hx2'
    omega
  have hW1_card : W1.card = S.card := Finset.card_image_of_injective _ Fin.val_injective
  have hout_in : out ∈ (Finset.range gs.length).image (· + 6) := by
    refine Finset.mem_image.2 ⟨out - 6, Finset.mem_range.2 (by have := hcl.2.1; omega), by omega⟩
  have hW2_card : W2.card = gs.length - 1 := by
    rw [Finset.card_erase_of_mem hout_in,
        Finset.card_image_of_injective _ (fun a b h => by omega), Finset.card_range]
  have hsub : W1 ∪ W2 ⊆ (usedWires gs).toFinset := by
    intro w hw
    rw [List.mem_toFinset, usedWires, List.mem_flatMap]
    rcases Finset.mem_union.1 hw with hw1 | hw2
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hw1
      exact hcl.2.2.2.2.2.1 v (hS v hv) (by omega)
    · have hne : w ≠ out := (Finset.mem_erase.1 hw2).1
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 (Finset.mem_of_mem_erase hw2)
      obtain ⟨j, hj, hmem⟩ := hcl.2.2.2.1 k (Finset.mem_range.1 hk) (by omega)
      exact ⟨gs[j], List.getElem_mem hj, by simpa [Nat.add_comm] using hmem⟩
  have hcard_le : (W1 ∪ W2).card ≤ (usedWires gs).toFinset.card := Finset.card_le_card hsub
  have htofin_le : (usedWires gs).toFinset.card ≤ (usedWires gs).length := List.toFinset_card_le _
  have hunion_card : (W1 ∪ W2).card = S.card + (gs.length - 1) := by
    rw [Finset.card_union_of_disjoint hdisj, hW1_card, hW2_card]
  have hlen := clean_usedWires_len hcl
  refine ⟨by omega, ?_⟩
  intro heq
  have hcard_eq : (usedWires gs).toFinset.card = (usedWires gs).length := by omega
  exact list_nodup_of_toFinset_card _ hcard_eq

private lemma ess_le_size_add_one {F : (Fin 6 → Bool) → Bool} {s : ℕ}
    (hC : HasCircuitSize 6 F s) (S : Finset (Fin 6)) (hS : ∀ v ∈ S, DependsOn F v)
    (h2 : 2 ≤ S.card) : S.card ≤ s + 1 := by
  obtain ⟨v₁, hv₁, v₂, hv₂, hne⟩ := Finset.one_lt_card.1 (by omega : 1 < S.card)
  have hnc : NonConst F := by
    obtain ⟨x, hx⟩ := hS v₁ hv₁
    exact ⟨Function.update x v₁ false, Function.update x v₁ true, hx⟩
  obtain ⟨C, hmin, hle⟩ := exists_min_of_hasCircuitSize hC
  have hcl := clean_of_min hmin hnc
  have hout := clean_out_ge6 hcl hne (hS v₁ hv₁) (hS v₂ hv₂)
  have hslot := (clean_slot_count hcl hout S hS).1
  have hlen : (C.gates.map normGate).length = C.size := by simp [Circuit.size]
  omega

private lemma nodup_flatMap_ne {α β : Type*} {l : List α} {f : α → List β}
    (hnd : (l.flatMap f).Nodup) {i j : ℕ} (hi : i < l.length) (hj : j < l.length)
    (hne : i ≠ j) {x : β} (hxi : x ∈ f l[i]) (hxj : x ∈ f l[j]) : False := by
  have hgen : ∀ (l : List α), (l.flatMap f).Nodup →
      ∀ i j, (hi : i < l.length) → (hj : j < l.length) → i < j →
        x ∈ f l[i] → x ∈ f l[j] → False := by
    intro l
    induction l with
    | nil => intro _ i _ hi; simp at hi
    | cons a rest ih =>
      intro hnd i j hi hj hlt hxi hxj
      rw [List.flatMap_cons, List.nodup_append] at hnd
      cases i with
      | zero =>
        cases j with
        | zero => omega
        | succ j' =>
          have hj' : j' < rest.length := by simp at hj; omega
          have hmem : x ∈ rest.flatMap f :=
            List.mem_flatMap.2 ⟨rest[j']'hj', List.getElem_mem hj', by simpa using hxj⟩
          exact hnd.2.2 x (by simpa using hxi) x hmem rfl
      | succ i' =>
        cases j with
        | zero => omega
        | succ j' =>
          exact ih hnd.2.1 i' j' (by simp at hi; omega) (by simp at hj; omega) (by omega)
            (by simpa using hxi) (by simpa using hxj)
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · exact hgen l hnd i j hi hj hlt hxi hxj
  · exact hgen l hnd j i hj hi hgt hxj hxi

private def treeWiresList (gs : List Gate) : List (Finset ℕ) :=
  gs.foldl (fun acc g =>
    let k := acc.length
    let sub := g.inputs.foldl (fun s i => s ∪ acc.getD i ∅) ∅
    acc ++ [insert k sub]) ((List.range 6).map fun i => ({i} : Finset ℕ))

private lemma treeWiresList_length (gs : List Gate) :
    (treeWiresList gs).length = 6 + gs.length := by
  have h : ∀ (l : List Gate) (acc : List (Finset ℕ)),
      (l.foldl (fun acc g =>
        let k := acc.length
        let sub := g.inputs.foldl (fun s i => s ∪ acc.getD i ∅) ∅
        acc ++ [insert k sub]) acc).length = acc.length + l.length := by
    intro l
    induction l with
    | nil => intro acc; simp
    | cons g rest ih =>
      intro acc
      simp only [List.foldl_cons, ih, List.length_append, List.length_cons, List.length_nil]
      omega
  simpa [treeWiresList] using h gs ((List.range 6).map fun i => ({i} : Finset ℕ))

private lemma treeWiresList_getD_lt (gs : List Gate) (acc : List (Finset ℕ)) (i : ℕ) (hi : i < acc.length) :
    (gs.foldl (fun acc g =>
      let k := acc.length
      let sub := g.inputs.foldl (fun s i => s ∪ acc.getD i ∅) ∅
      acc ++ [insert k sub]) acc).getD i ∅ = acc.getD i ∅ := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g rest ih =>
    simp only [List.foldl_cons]
    rw [ih _ (by simp; omega)]
    exact getD_snoc_lt _ _ _ _ hi

private lemma treeWires_lt8 (gs : List Gate) (i : ℕ) (hi : i < 6) :
    (treeWiresList gs).getD i ∅ = {i} := by
  rw [treeWiresList, treeWiresList_getD_lt _ _ _ (by simp; exact hi)]
  simp [List.getD, hi]

private lemma treeWires_step (gs : List Gate) (k : ℕ) (hk : k < gs.length)
    (hall : ∀ i ∈ gs[k].inputs, i < 6 + k) :
    (treeWiresList gs).getD (6 + k) ∅ =
      insert (6 + k) (gs[k].inputs.foldl (fun s i => s ∪ (treeWiresList gs).getD i ∅) ∅) := by
  have hsp : gs = gs.take k ++ gs[k] :: gs.drop (k + 1) := by
    conv_lhs => rw [← List.take_append_drop k gs]
    rw [List.drop_eq_getElem_cons hk]
  set f : List (Finset ℕ) → Gate → List (Finset ℕ) := fun acc g =>
    let m := acc.length
    let sub := g.inputs.foldl (fun s i => s ∪ acc.getD i ∅) ∅
    acc ++ [insert m sub]
  set init := (List.range 6).map fun i => ({i} : Finset ℕ)
  set a1 := (gs.take k).foldl f init with ha1
  have ha1_len : a1.length = 6 + k := by
    have := treeWiresList_length (gs.take k)
    simpa [treeWiresList, ha1, f, init, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)] using this
  have hfold : treeWiresList gs = (gs.drop (k + 1)).foldl f (f a1 gs[k]) := by
    conv_lhs => rw [treeWiresList, hsp, List.foldl_append, List.foldl_cons]
  have hsub_eq : ∀ (l : List ℕ) (s : Finset ℕ),
      (∀ i ∈ l, i < 6 + k) →
      l.foldl (fun s i => s ∪ a1.getD i ∅) s =
      l.foldl (fun s i => s ∪ (treeWiresList gs).getD i ∅) s := by
    intro l
    induction l with
    | nil => intro s _; rfl
    | cons i rest ih =>
      intro s hl
      simp only [List.foldl_cons]
      have hi : i < a1.length := by rw [ha1_len]; exact hl i (by simp)
      have hgi : (treeWiresList gs).getD i ∅ = a1.getD i ∅ := by
        rw [hfold, treeWiresList_getD_lt _ _ _ (by simp [f]; omega)]
        exact getD_snoc_lt _ _ _ _ hi
      rw [hgi]
      exact ih _ (fun j hj => hl j (by simp [hj]))
  conv_lhs => rw [hfold, treeWiresList_getD_lt _ _ _ (by simp [f, ha1_len])]
  simp only [f]
  rw [getD_snoc_eq _ _ _ _ ha1_len.symm, ha1_len]
  congr 1
  change gs[k].inputs.foldl (fun s i => s ∪ a1.getD i ∅) ∅ = _
  exact hsub_eq gs[k].inputs ∅ hall

private lemma clean_inputs_lt {F : (Fin 6 → Bool) → Bool} {gs : List Gate} {out : ℕ}
    (hcl : CleanCircuit F gs out) (k : ℕ) (hk : k < gs.length) :
    ∀ i ∈ gs[k].inputs, i < 6 + k := by
  have hcg := hcl.1 k hk
  rcases hcg.2.2.1.1 with hop | hop | hop
  · obtain ⟨a, b, hgi, ha, hb, _⟩ := hcg.1 (Or.inl hop)
    rw [hgi]; intro i hi; simp at hi; rcases hi with rfl | rfl <;> assumption
  · obtain ⟨a, b, hgi, ha, hb, _⟩ := hcg.1 (Or.inr hop)
    rw [hgi]; intro i hi; simp at hi; rcases hi with rfl | rfl <;> assumption
  · obtain ⟨a, hgi, ha⟩ := hcg.2.1 hop
    rw [hgi]; intro i hi; simp at hi; subst hi; exact ha

private lemma foldl_union_eq {α : Type*} [DecidableEq α] (f : ℕ → Finset α) (l : List ℕ) (s : Finset α) :
    ∀ x, x ∈ l.foldl (fun s i => s ∪ f i) s ↔ x ∈ s ∨ ∃ i ∈ l, x ∈ f i := by
  induction l generalizing s with
  | nil => intro x; simp
  | cons a rest ih =>
    intro x
    simp only [List.foldl_cons, ih, Finset.mem_union, List.mem_cons]
    constructor
    · rintro ((hx | hx) | ⟨i, hi, hxi⟩)
      · exact Or.inl hx
      · exact Or.inr ⟨a, Or.inl rfl, hx⟩
      · exact Or.inr ⟨i, Or.inr hi, hxi⟩
    · rintro (hx | ⟨i, rfl | hi, hxi⟩)
      · exact Or.inl (Or.inl hx)
      · exact Or.inl (Or.inr hxi)
      · exact Or.inr ⟨i, hi, hxi⟩

private lemma clean_treeWires_props {F : (Fin 6 → Bool) → Bool} {gs : List Gate} {out : ℕ}
    (hcl : CleanCircuit F gs out) :
    ∀ w < 6 + gs.length,
      w ∈ (treeWiresList gs).getD w ∅ ∧
      (∀ u ∈ (treeWiresList gs).getD w ∅, u ≤ w) ∧
      (∀ u ∈ (treeWiresList gs).getD w ∅, u ≠ w →
        ∃ j, ∃ hj : j < gs.length, 6 + j ∈ (treeWiresList gs).getD w ∅ ∧ u ∈ gs[j].inputs) ∧
      (∃ v : Fin 6, (v : ℕ) ∈ (treeWiresList gs).getD w ∅) ∧
      (∀ u ∈ (treeWiresList gs).getD w ∅, u < 6 → u ≠ w → ∃ g ∈ gs, u ∈ g.inputs) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hw8 : w < 6
    · rw [treeWires_lt8 gs w hw8]
      refine ⟨by simp, by intro u hu; simp at hu; omega,
        by intro u hu hne; simp at hu; exact absurd hu hne,
        ⟨⟨w, hw8⟩, by simp⟩, by intro u hu _ hne; simp at hu; exact absurd hu hne⟩
    · have hk : w - 6 < gs.length := by omega
      have hw_eq : w = 6 + (w - 6) := by omega
      set k := w - 6
      have hstep := treeWires_step gs k hk (clean_inputs_lt hcl k hk)
      rw [← hw_eq] at hstep
      have hne_ins : ∃ a, a ∈ gs[k].inputs := by
        have hcg := hcl.1 k hk
        rcases hcg.2.2.1.1 with hop | hop | hop
        · obtain ⟨a, b, hgi, _⟩ := hcg.1 (Or.inl hop); exact ⟨a, by simp [hgi]⟩
        · obtain ⟨a, b, hgi, _⟩ := hcg.1 (Or.inr hop); exact ⟨a, by simp [hgi]⟩
        · obtain ⟨a, hgi, _⟩ := hcg.2.1 hop; exact ⟨a, by simp [hgi]⟩
      refine ⟨by rw [hstep]; simp, ?_, ?_, ?_, ?_⟩
      · intro u hu
        rw [hstep, Finset.mem_insert, foldl_union_eq] at hu
        rcases hu with rfl | h0 | ⟨i, hi, hui⟩
        · exact le_refl _
        · simp at h0
        · have hilt : i < w := by rw [hw_eq]; exact clean_inputs_lt hcl k hk i hi
          have hle := (ih i hilt (by omega)).2.1 u hui
          omega
      · intro u hu hne
        rw [hstep, Finset.mem_insert, foldl_union_eq] at hu
        rcases hu with rfl | h0 | ⟨i, hi, hui⟩
        · exact absurd rfl hne
        · simp at h0
        · have hilt : i < w := by rw [hw_eq]; exact clean_inputs_lt hcl k hk i hi
          by_cases hui_eq : u = i
          · subst hui_eq
            exact ⟨k, hk, by rw [← hw_eq, hstep]; simp, hi⟩
          · obtain ⟨j, hj, hjmem, huj⟩ := (ih i hilt (by omega)).2.2.1 u hui hui_eq
            refine ⟨j, hj, ?_, huj⟩
            rw [hstep, Finset.mem_insert, foldl_union_eq]
            exact Or.inr (Or.inr ⟨i, hi, hjmem⟩)
      · obtain ⟨a, ha⟩ := hne_ins
        have halt : a < w := by rw [hw_eq]; exact clean_inputs_lt hcl k hk a ha
        obtain ⟨v, hv⟩ := (ih a halt (by omega)).2.2.2.1
        refine ⟨v, ?_⟩
        rw [hstep, Finset.mem_insert, foldl_union_eq]
        exact Or.inr (Or.inr ⟨a, ha, hv⟩)
      · intro u hu hu8 _
        have hne_u : u ≠ w := by omega
        rw [hstep, Finset.mem_insert, foldl_union_eq] at hu
        rcases hu with rfl | h0 | ⟨i, hi, hui⟩
        · exact absurd rfl hne_u
        · simp at h0
        · have hilt : i < w := by rw [hw_eq]; exact clean_inputs_lt hcl k hk i hi
          by_cases hui_eq : u = i
          · subst hui_eq; exact ⟨gs[k], List.getElem_mem hk, hi⟩
          · exact (ih i hilt (by omega)).2.2.2.2 u hui hu8 hui_eq

private lemma wiresFrom_getD_eq {gs : List Gate} (k : ℕ) (hk : k < gs.length) (x : Fin 6 → Bool)
    (hall : ∀ i ∈ gs[k].inputs, i < 6 + k) :
    (wiresFrom gs (List.ofFn x)).getD (6 + k) false =
      gs[k].op.eval (gs[k].inputs.map fun i => (wiresFrom gs (List.ofFn x)).getD i false) := by
  have hsp : gs = gs.take k ++ gs[k] :: gs.drop (k + 1) := by
    conv_lhs => rw [← List.take_append_drop k gs]
    rw [List.drop_eq_getElem_cons hk]
  set w0 := wiresFrom (gs.take k) (List.ofFn x) with hw0
  have hw0_len : w0.length = 6 + k := by
    simp [hw0, wiresFrom_length, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)]
  have hfold : wiresFrom gs (List.ofFn x) =
      wiresFrom (gs.drop (k + 1)) (w0 ++ [gs[k].op.eval (gs[k].inputs.map fun i => w0.getD i false)]) := by
    conv_lhs => rw [hsp, wiresFrom_append, wiresFrom_cons]
  have hmap : (gs[k].inputs.map fun i => (wiresFrom gs (List.ofFn x)).getD i false) =
      (gs[k].inputs.map fun i => w0.getD i false) := by
    apply List.map_congr_left
    intro i hi
    have hilt := hall i hi
    rw [hfold, wiresFrom_getD_lt _ _ _ (by simp; omega), getD_snoc_lt _ _ _ _ (by omega)]
  rw [hmap, hfold, wiresFrom_getD_lt _ _ _ (by simp; omega), getD_snoc_eq _ _ _ _ hw0_len.symm]

private lemma clean_wire_depends_on_tree {F : (Fin 6 → Bool) → Bool} {gs : List Gate} {out : ℕ}
    (hcl : CleanCircuit F gs out) :
    ∀ w < 6 + gs.length, ∀ x y : Fin 6 → Bool,
      (∀ v : Fin 6, (v : ℕ) ∈ (treeWiresList gs).getD w ∅ → x v = y v) →
      (wiresFrom gs (List.ofFn x)).getD w false = (wiresFrom gs (List.ofFn y)).getD w false := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw x y hxy
    by_cases hw8 : w < 6
    · rw [wiresFrom_getD_lt _ _ _ (by simp; omega), wiresFrom_getD_lt _ _ _ (by simp; omega),
          ofFn_getD_lt _ _ _ hw8, ofFn_getD_lt _ _ _ hw8]
      apply hxy ⟨w, hw8⟩
      rw [treeWires_lt8 gs w hw8]; simp
    · set k := w - 6
      have hk : k < gs.length := by omega
      have hw_eq : w = 6 + k := by omega
      rw [hw_eq, wiresFrom_getD_eq k hk x (clean_inputs_lt hcl k hk),
          wiresFrom_getD_eq k hk y (clean_inputs_lt hcl k hk)]
      congr 1
      apply List.map_congr_left
      intro i hi
      have hilt : i < 6 + k := clean_inputs_lt hcl k hk i hi
      apply ih i (by omega) (by omega) x y
      intro v hv
      apply hxy v
      rw [hw_eq, treeWires_step gs k hk (clean_inputs_lt hcl k hk), Finset.mem_insert, foldl_union_eq]
      exact Or.inr (Or.inr ⟨i, hi, hv⟩)

private lemma clean_disjoint_of_nodup {F : (Fin 6 → Bool) → Bool} {gs : List Gate} {out : ℕ}
    (hcl : CleanCircuit F gs out) (hnd : (usedWires gs).Nodup)
    (k : ℕ) (hk : k < gs.length) {a b : ℕ} (hins : gs[k].inputs = [a, b])
    (ha : a < 6 + k) (hb : b < 6 + k) (hab : a ≠ b) :
    Disjoint ((treeWiresList gs).getD a ∅) ((treeWiresList gs).getD b ∅) := by
  rw [Finset.disjoint_left]
  intro x hxa hxb
  have hne : ((treeWiresList gs).getD a ∅ ∩ (treeWiresList gs).getD b ∅).Nonempty :=
    ⟨x, Finset.mem_inter.2 ⟨hxa, hxb⟩⟩
  set u := ((treeWiresList gs).getD a ∅ ∩ (treeWiresList gs).getD b ∅).max' hne with hu
  have hu_mem : u ∈ (treeWiresList gs).getD a ∅ ∩ (treeWiresList gs).getD b ∅ := Finset.max'_mem _ hne
  have hua : u ∈ (treeWiresList gs).getD a ∅ := (Finset.mem_inter.1 hu_mem).1
  have hub : u ∈ (treeWiresList gs).getD b ∅ := (Finset.mem_inter.1 hu_mem).2
  have hpa := clean_treeWires_props hcl a (by omega)
  have hpb := clean_treeWires_props hcl b (by omega)
  by_cases heqa : u = a
  · rw [heqa] at hub
    obtain ⟨j, hj, hjb, haj⟩ := hpb.2.2.1 a hub hab
    have hjlt : 6 + j ≤ b := hpb.2.1 (6 + j) hjb
    exact nodup_flatMap_ne hnd hk hj (by omega) (by simp [hins]) haj
  · by_cases heqb : u = b
    · rw [heqb] at hua
      obtain ⟨j, hj, hja, hbj⟩ := hpa.2.2.1 b hua hab.symm
      have hjlt : 6 + j ≤ a := hpa.2.1 (6 + j) hja
      exact nodup_flatMap_ne hnd hk hj (by omega) (by simp [hins]) hbj
    · obtain ⟨j₁, hj₁, hj₁a, huj₁⟩ := hpa.2.2.1 u hua heqa
      obtain ⟨j₂, hj₂, hj₂b, huj₂⟩ := hpb.2.2.1 u hub heqb
      by_cases hjeq : j₁ = j₂
      · subst hjeq
        have hu_lt : u < 6 + j₁ := clean_inputs_lt hcl j₁ hj₁ u huj₁
        have hmem_j : 6 + j₁ ∈ (treeWiresList gs).getD a ∅ ∩ (treeWiresList gs).getD b ∅ :=
          Finset.mem_inter.2 ⟨hj₁a, hj₂b⟩
        have hle_u : 6 + j₁ ≤ u := Finset.le_max' _ _ hmem_j
        omega
      · exact nodup_flatMap_ne hnd hj₁ hj₂ hjeq huj₁ huj₂

private def NotFactorable (F : (Fin 6 → Bool) → Bool) (S : Finset (Fin 6)) : Prop :=
  ∀ A : Finset (Fin 6), A ⊆ S → A.Nonempty → (S \ A).Nonempty →
    (∃ x₁ x₂ x₃ y₁₂ y₁₃ y₂₃ : Fin 6 → Bool,
      F (fun v => if v ∈ A then x₁ v else y₁₂ v) ≠ F (fun v => if v ∈ A then x₂ v else y₁₂ v) ∧
      F (fun v => if v ∈ A then x₁ v else y₁₃ v) ≠ F (fun v => if v ∈ A then x₃ v else y₁₃ v) ∧
      F (fun v => if v ∈ A then x₂ v else y₂₃ v) ≠ F (fun v => if v ∈ A then x₃ v else y₂₃ v)) ∨
    (∃ y₁ y₂ y₃ x₁₂ x₁₃ x₂₃ : Fin 6 → Bool,
      F (fun v => if v ∈ A then x₁₂ v else y₁ v) ≠ F (fun v => if v ∈ A then x₁₂ v else y₂ v) ∧
      F (fun v => if v ∈ A then x₁₃ v else y₁ v) ≠ F (fun v => if v ∈ A then x₁₃ v else y₃ v) ∧
      F (fun v => if v ∈ A then x₂₃ v else y₂ v) ≠ F (fun v => if v ∈ A then x₂₃ v else y₃ v))

private lemma not_read_once_of_notFactorable {F : (Fin 6 → Bool) → Bool} {gs : List Gate} {out : ℕ}
    (hcl : CleanCircuit F gs out) (hnd : (usedWires gs).Nodup)
    (S : Finset (Fin 6)) (hS_iff : ∀ v : Fin 6, DependsOn F v ↔ v ∈ S)
    (hS2 : 2 ≤ S.card) (hnf : NotFactorable F S) : False := by
  have hwalk : ∀ w < 6 + gs.length, ∀ flip : Bool,
      (∀ x : Fin 6 → Bool, (wiresFrom gs (List.ofFn x)).getD w false =
        if flip then !F x else F x) → False := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw flip hev
      by_cases hw8 : w < 6
      · obtain ⟨v₁, hv₁, v₂, hv₂, hne⟩ := Finset.one_lt_card.1 (by omega : 1 < S.card)
        let wfin : Fin 6 := ⟨w, hw8⟩
        have hpick : ∃ v ∈ S, v ≠ wfin := by
          by_cases h1 : v₁ = wfin
          · exact ⟨v₂, hv₂, fun h => hne (h1.trans h.symm)⟩
          · exact ⟨v₁, hv₁, h1⟩
        obtain ⟨v, hvS, hvw⟩ := hpick
        obtain ⟨x, hx⟩ := (hS_iff v).2 hvS
        have e0 := hev (Function.update x v false)
        have e1 := hev (Function.update x v true)
        rw [wiresFrom_getD_lt _ _ _ (by simp; omega), ofFn_getD_lt _ _ _ hw8,
            Function.update_of_ne hvw.symm] at e0 e1
        have heq : (if flip then !F (Function.update x v false) else F (Function.update x v false)) =
            (if flip then !F (Function.update x v true) else F (Function.update x v true)) :=
          e0.symm.trans e1
        cases flip
        · simp only [Bool.false_eq_true, ↓reduceIte] at heq; exact hx heq
        · simp only [↓reduceIte, Bool.not_inj_iff] at heq; exact hx heq
      · set k := w - 6
        have hk : k < gs.length := by omega
        have hw_eq : w = 6 + k := by omega
        have hcg := hcl.1 k hk
        have hbin : ∀ (op : Bool → Bool → Bool),
            (∃ a b, gs[k].inputs = [a, b] ∧ a < 6 + k ∧ b < 6 + k ∧ a ≠ b ∧
              ∀ z : Fin 6 → Bool, (if flip then !F z else F z) =
                op ((wiresFrom gs (List.ofFn z)).getD a false)
                   ((wiresFrom gs (List.ofFn z)).getD b false)) → False := by
          rintro op ⟨a, b, hgi, ha, hb, hab, heval⟩
          have hdisj := clean_disjoint_of_nodup hcl hnd k hk hgi ha hb hab
          let A : Finset (Fin 6) := S.filter fun v => (v : ℕ) ∈ (treeWiresList gs).getD a ∅
          have hA_sub : A ⊆ S := Finset.filter_subset _ _
          have hA_ne : A.Nonempty := by
            obtain ⟨v, hv⟩ := (clean_treeWires_props hcl a (by omega)).2.2.2.1
            have hv_used : ∃ g ∈ gs, (v : ℕ) ∈ g.inputs := by
              by_cases hva : (v : ℕ) = a
              · exact ⟨gs[k], List.getElem_mem hk, by simp [hgi, hva]⟩
              · exact (clean_treeWires_props hcl a (by omega)).2.2.2.2 (v : ℕ) hv v.isLt hva
            have hv_dep : DependsOn F v := by
              by_contra hndep
              obtain ⟨g, hg, hvg⟩ := hv_used
              exact hcl.2.2.2.2.1 v hndep g hg hvg
            exact ⟨v, Finset.mem_filter.2 ⟨(hS_iff v).1 hv_dep, hv⟩⟩
          have hB_ne : (S \ A).Nonempty := by
            obtain ⟨v, hv⟩ := (clean_treeWires_props hcl b (by omega)).2.2.2.1
            have hv_used : ∃ g ∈ gs, (v : ℕ) ∈ g.inputs := by
              by_cases hvb : (v : ℕ) = b
              · exact ⟨gs[k], List.getElem_mem hk, by simp [hgi, hvb]⟩
              · exact (clean_treeWires_props hcl b (by omega)).2.2.2.2 (v : ℕ) hv v.isLt hvb
            have hv_dep : DependsOn F v := by
              by_contra hndep
              obtain ⟨g, hg, hvg⟩ := hv_used
              exact hcl.2.2.2.2.1 v hndep g hg hvg
            refine ⟨v, Finset.mem_sdiff.2 ⟨(hS_iff v).1 hv_dep, ?_⟩⟩
            intro hmem
            exact Finset.disjoint_left.1 hdisj (Finset.mem_filter.1 hmem).2 hv
          have ha_indep : ∀ x y : Fin 6 → Bool,
              (wiresFrom gs (List.ofFn (fun v => if v ∈ A then x v else y v))).getD a false =
              (wiresFrom gs (List.ofFn x)).getD a false := by
            intro x y
            apply clean_wire_depends_on_tree hcl a (by omega)
            intro v hv
            have hv_used : ∃ g ∈ gs, (v : ℕ) ∈ g.inputs := by
              by_cases hva : (v : ℕ) = a
              · exact ⟨gs[k], List.getElem_mem hk, by simp [hgi, hva]⟩
              · exact (clean_treeWires_props hcl a (by omega)).2.2.2.2 (v : ℕ) hv v.isLt hva
            have hv_dep : DependsOn F v := by
              by_contra hndep
              obtain ⟨g, hg, hvg⟩ := hv_used
              exact hcl.2.2.2.2.1 v hndep g hg hvg
            have hvA : v ∈ A := Finset.mem_filter.2 ⟨(hS_iff v).1 hv_dep, hv⟩
            simp [hvA]
          have hb_indep : ∀ x y : Fin 6 → Bool,
              (wiresFrom gs (List.ofFn (fun v => if v ∈ A then x v else y v))).getD b false =
              (wiresFrom gs (List.ofFn y)).getD b false := by
            intro x y
            apply clean_wire_depends_on_tree hcl b (by omega)
            intro v hv
            have hnotA : v ∉ A := by
              intro hmem
              exact Finset.disjoint_left.1 hdisj (Finset.mem_filter.1 hmem).2 hv
            simp [hnotA]
          have hF_eq : ∀ x₁ x₂ y : Fin 6 → Bool,
              (wiresFrom gs (List.ofFn x₁)).getD a false = (wiresFrom gs (List.ofFn x₂)).getD a false →
              F (fun v => if v ∈ A then x₁ v else y v) = F (fun v => if v ∈ A then x₂ v else y v) := by
            intro x₁ x₂ y hEq
            have e1 := heval (fun v => if v ∈ A then x₁ v else y v)
            have e2 := heval (fun v => if v ∈ A then x₂ v else y v)
            rw [ha_indep, hb_indep] at e1 e2
            rw [hEq] at e1
            have e := e1.trans e2.symm
            cases flip
            · simpa using e
            · simpa [Bool.not_inj_iff] using e
          have hF_eqB : ∀ x y₁ y₂ : Fin 6 → Bool,
              (wiresFrom gs (List.ofFn y₁)).getD b false = (wiresFrom gs (List.ofFn y₂)).getD b false →
              F (fun v => if v ∈ A then x v else y₁ v) = F (fun v => if v ∈ A then x v else y₂ v) := by
            intro x y₁ y₂ hEq
            have e1 := heval (fun v => if v ∈ A then x v else y₁ v)
            have e2 := heval (fun v => if v ∈ A then x v else y₂ v)
            rw [ha_indep, hb_indep] at e1 e2
            rw [hEq] at e1
            have e := e1.trans e2.symm
            cases flip
            · simpa using e
            · simpa [Bool.not_inj_iff] using e
          rcases hnf A hA_sub hA_ne hB_ne with
            ⟨x₁, x₂, x₃, y₁₂, y₁₃, y₂₃, h12, h13, h23⟩ |
            ⟨y₁, y₂, y₃, x₁₂, x₁₃, x₂₃, h12, h13, h23⟩
          · cases h1 : (wiresFrom gs (List.ofFn x₁)).getD a false <;>
            cases h2 : (wiresFrom gs (List.ofFn x₂)).getD a false <;>
            cases h3 : (wiresFrom gs (List.ofFn x₃)).getD a false
            · exact h12 (hF_eq x₁ x₂ y₁₂ (h1.trans h2.symm))
            · exact h12 (hF_eq x₁ x₂ y₁₂ (h1.trans h2.symm))
            · exact h13 (hF_eq x₁ x₃ y₁₃ (h1.trans h3.symm))
            · exact h23 (hF_eq x₂ x₃ y₂₃ (h2.trans h3.symm))
            · exact h23 (hF_eq x₂ x₃ y₂₃ (h2.trans h3.symm))
            · exact h13 (hF_eq x₁ x₃ y₁₃ (h1.trans h3.symm))
            · exact h12 (hF_eq x₁ x₂ y₁₂ (h1.trans h2.symm))
            · exact h12 (hF_eq x₁ x₂ y₁₂ (h1.trans h2.symm))
          · cases h1 : (wiresFrom gs (List.ofFn y₁)).getD b false <;>
            cases h2 : (wiresFrom gs (List.ofFn y₂)).getD b false <;>
            cases h3 : (wiresFrom gs (List.ofFn y₃)).getD b false
            · exact h12 (hF_eqB x₁₂ y₁ y₂ (h1.trans h2.symm))
            · exact h12 (hF_eqB x₁₂ y₁ y₂ (h1.trans h2.symm))
            · exact h13 (hF_eqB x₁₃ y₁ y₃ (h1.trans h3.symm))
            · exact h23 (hF_eqB x₂₃ y₂ y₃ (h2.trans h3.symm))
            · exact h23 (hF_eqB x₂₃ y₂ y₃ (h2.trans h3.symm))
            · exact h13 (hF_eqB x₁₃ y₁ y₃ (h1.trans h3.symm))
            · exact h12 (hF_eqB x₁₂ y₁ y₂ (h1.trans h2.symm))
            · exact h12 (hF_eqB x₁₂ y₁ y₂ (h1.trans h2.symm))
        rcases hcg.2.2.1.1 with hop | hop | hop
        · obtain ⟨a, b, hgi, ha, hb, hab⟩ := hcg.1 (Or.inl hop)
          refine hbin (· && ·) ⟨a, b, hgi, ha, hb, hab, fun z => ?_⟩
          have h1 := hev z
          rw [hw_eq, wiresFrom_getD_eq k hk z (clean_inputs_lt hcl k hk)] at h1
          have hop' : gs[k].op = GateOp.and := hop
          rw [hop', hgi] at h1
          simpa [GateOp.eval] using h1.symm
        · obtain ⟨a, b, hgi, ha, hb, hab⟩ := hcg.1 (Or.inr hop)
          refine hbin (· || ·) ⟨a, b, hgi, ha, hb, hab, fun z => ?_⟩
          have h1 := hev z
          rw [hw_eq, wiresFrom_getD_eq k hk z (clean_inputs_lt hcl k hk)] at h1
          have hop' : gs[k].op = GateOp.or := hop
          rw [hop', hgi] at h1
          simpa [GateOp.eval] using h1.symm
        · obtain ⟨a, hgi, ha⟩ := hcg.2.1 hop
          apply ih a (by omega) (by omega) (!flip)
          intro z
          have h1 := hev z
          rw [hw_eq, wiresFrom_getD_eq k hk z (clean_inputs_lt hcl k hk)] at h1
          have hop' : gs[k].op = GateOp.not := hop
          rw [hop', hgi] at h1
          simp only [GateOp.eval, List.map_cons, List.map_nil, List.headD_cons] at h1
          cases flip
          · simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false] at h1 ⊢
            have h2 := congrArg Bool.not h1
            simpa using h2
          · simp only [↓reduceIte, Bool.not_true, Bool.false_eq_true] at h1 ⊢
            exact Bool.not_inj h1
  exact hwalk out hcl.2.1 false (by intro x; simpa using hcl.2.2.1 x)

private def stateAt (gs : List Gate) (init : List (Bool ⊕ ℕ)) (k : ℕ) :
    List (Bool ⊕ ℕ) × List Gate :=
  elimPass 6 (gs.take k) (init, [])

private def isDropped (gs : List Gate) (init : List (Bool ⊕ ℕ)) (k : ℕ) : Bool :=
  let acc := stateAt gs init k
  let g := gs.getD k ⟨GateOp.or, []⟩
  (simplifyGate g.op (6 + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.isNone

private lemma elimPass_dropped_card (gs : List Gate) (init : List (Bool ⊕ ℕ)) :
    (elimPass 6 gs (init, [])).2.length +
      ((Finset.range gs.length).filter fun k => isDropped gs init k = true).card = gs.length ∧
    (∀ k (hk : k < gs.length), isDropped gs init k = false →
      ∃ g' ∈ (elimPass 6 gs (init, [])).2, g'.op = gs[k].op) := by
  have hgen : ∀ (l₁ l₂ : List Gate),
      (elimPass 6 l₁ (init, [])).2.length +
        ((Finset.range l₁.length).filter fun k => isDropped (l₁ ++ l₂) init k = true).card =
          l₁.length ∧
      (∀ k (hk : k < l₁.length), isDropped (l₁ ++ l₂) init k = false →
        ∃ g' ∈ (elimPass 6 l₁ (init, [])).2, g'.op = l₁[k].op) := by
    intro l₁
    induction l₁ using List.reverseRecOn with
    | nil => intro l₂; simp [elimPass]
    | append_singleton l₁ g ih =>
      intro l₂
      have hre : (l₁ ++ [g]) ++ l₂ = l₁ ++ (g :: l₂) := by simp
      have hih := ih (g :: l₂)
      rw [← hre] at hih
      set gs' := (l₁ ++ [g]) ++ l₂ with hgs'
      have hst_eq : stateAt gs' init l₁.length = elimPass 6 l₁ (init, []) := by
        simp [stateAt, hgs', hre]
      have hget_eq : gs'.getD l₁.length ⟨GateOp.or, []⟩ = g := by
        simp [hgs', hre, List.getD]
      have hacc_eq : elimPass 6 (l₁ ++ [g]) (init, []) = elimStep 6 (elimPass 6 l₁ (init, [])) g := by
        rw [elimPass_append, elimPass_cons, elimPass_nil]
      set r := simplifyGate g.op (6 + (elimPass 6 l₁ (init, [])).2.length)
        (g.inputs.map fun i => (elimPass 6 l₁ (init, [])).1.getD i (Sum.inl false)) with hr
      have hdrop_last : isDropped gs' init l₁.length = r.1.isNone := by
        simp only [isDropped, hst_eq, hget_eq, hr]
      have hlen_app : (l₁ ++ [g]).length = l₁.length + 1 := by simp
      have hfilt : (Finset.range (l₁ ++ [g]).length).filter (fun k => isDropped gs' init k = true) =
          if isDropped gs' init l₁.length = true then
            insert l₁.length ((Finset.range l₁.length).filter (fun k => isDropped gs' init k = true))
          else
            (Finset.range l₁.length).filter (fun k => isDropped gs' init k = true) := by
        rw [hlen_app, Finset.range_add_one, Finset.filter_insert]
      have hnotmem : l₁.length ∉ (Finset.range l₁.length).filter (fun k => isDropped gs' init k = true) := by
        simp
      refine ⟨?_, ?_⟩
      · rw [hacc_eq, hfilt, hlen_app]
        cases hr1 : r.1 with
        | none =>
          have hd : isDropped gs' init l₁.length = true := by rw [hdrop_last, hr1]; rfl
          simp only [hd, ↓reduceIte, Finset.card_insert_of_notMem hnotmem, elimStep, ← hr, hr1,
            Option.toList_none, List.append_nil]
          omega
        | some g' =>
          have hd : isDropped gs' init l₁.length = false := by rw [hdrop_last, hr1]; rfl
          simp only [hd, Bool.false_eq_true, ↓reduceIte, elimStep, ← hr, hr1,
            Option.toList_some, List.length_append, List.length_singleton]
          omega
      · intro k hk hnd
        rw [hacc_eq]
        simp only [List.length_append, List.length_singleton] at hk
        by_cases hlt : k < l₁.length
        · obtain ⟨g', hg', hop'⟩ := hih.2 k hlt hnd
          refine ⟨g', ?_, ?_⟩
          · simp only [elimStep, List.mem_append]; exact Or.inl hg'
          · rw [List.getElem_append_left hlt]; exact hop'
        · have hk' : k = l₁.length := by omega
          subst hk'
          rw [hdrop_last] at hnd
          cases hr1 : r.1 with
          | none => rw [hr1] at hnd; simp at hnd
          | some g' =>
            refine ⟨g', ?_, ?_⟩
            · simp only [elimStep, ← hr, hr1, Option.toList_some, List.mem_append, List.mem_singleton]
              exact Or.inr trivial
            · have hmem : g' ∈ r.1 := by rw [Option.mem_def]; exact hr1
              have hop' := simplifyGate_op_eq g.op _ _ g' hmem
              simpa using hop'
  simpa using hgen gs []

private lemma stateAt_getD (gs : List Gate) (init : List (Bool ⊕ ℕ)) (k i : ℕ)
    (hi : i < init.length + k) (hk : k ≤ gs.length) :
    (stateAt gs init k).1.getD i (Sum.inl false) =
      (elimPass 6 gs (init, [])).1.getD i (Sum.inl false) := by
  have hsp : gs = gs.take k ++ gs.drop k := (List.take_append_drop k gs).symm
  have hlen : (stateAt gs init k).1.length = init.length + k := by
    rw [stateAt, elimPass_fst_len, List.length_take, Nat.min_eq_left hk]
  conv_rhs => rw [hsp, elimPass_append]
  exact (elimPass_getD_lt 6 i (Sum.inl false) (gs.drop k) (stateAt gs init k) (by omega)).symm

private lemma isDropped_of_const_in {gs : List Gate} {init : List (Bool ⊕ ℕ)}
    (hinit : init.length = 6) (hnok : ∀ g ∈ gs, NOkGate g)
    {k : ℕ} (hk : k < gs.length) {w : ℕ} (hw : w ∈ gs[k].inputs) (hwlt : w < 6 + k)
    {c : Bool} (hc : (elimPass 6 gs (init, [])).1.getD w (Sum.inl false) = Sum.inl c) :
    isDropped gs init k = true := by
  have hget : gs.getD k ⟨GateOp.or, []⟩ = gs[k] := by simp [List.getD, hk]
  have hwst : (stateAt gs init k).1.getD w (Sum.inl false) = Sum.inl c := by
    rw [stateAt_getD gs init k w (by omega) (Nat.le_of_lt hk), hc]
  have hok := hnok gs[k] (List.getElem_mem hk)
  have hnone : (simplifyGate gs[k].op (6 + (stateAt gs init k).2.length)
      (gs[k].inputs.map fun i => (stateAt gs init k).1.getD i (Sum.inl false))).1 = none := by
    apply simplifyGate_none_of_const
    · exact hok.1.1
    · simp; exact hok.1.2
    · intro hnot; simp; exact hok.2 hnot
    · exact ⟨c, List.mem_map.2 ⟨w, hw, hwst⟩⟩
  simp only [isDropped, hget, hnone, Option.isNone_none]

private lemma elimPass_getD_gate (gs : List Gate) (init : List (Bool ⊕ ℕ))
    (hinit : init.length = 6) {k : ℕ} (hk : k < gs.length) :
    (elimPass 6 gs (init, [])).1.getD (6 + k) (Sum.inl false) =
      (simplifyGate gs[k].op (6 + (stateAt gs init k).2.length)
        (gs[k].inputs.map fun i => (stateAt gs init k).1.getD i (Sum.inl false))).2 := by
  have hsp : gs = gs.take k ++ gs[k] :: gs.drop (k + 1) := by
    conv_lhs => rw [← List.take_append_drop k gs]
    rw [List.drop_eq_getElem_cons hk]
  have hlen : (stateAt gs init k).1.length = 6 + k := by
    rw [stateAt, elimPass_fst_len, hinit, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)]
  conv_lhs => rw [hsp, elimPass_append, elimPass_cons]
  have hlen1 : 6 + k < (elimStep 6 (stateAt gs init k) gs[k]).1.length := by
    simp only [elimStep, List.length_append, List.length_singleton, hlen]; omega
  change (elimPass 6 (gs.drop (k + 1)) (elimStep 6 (stateAt gs init k) gs[k])).1.getD (6 + k) (Sum.inl false) = _
  rw [elimPass_getD_lt 6 (6 + k) (Sum.inl false) (gs.drop (k + 1)) _ hlen1]
  simp only [elimStep, stateAt]
  exact getD_snoc_eq _ _ _ _ hlen.symm

private lemma hasCircuitSize_comp {F : (Fin 6 → Bool) → Bool} {s : ℕ}
    (π : Fin 6 → Fin 6) (hC : HasCircuitSize 6 F s) :
    HasCircuitSize 6 (fun x => F (x ∘ π)) s := by
  obtain ⟨C, hok, hsz, hev⟩ := hC
  let rwW (w : ℕ) : ℕ := if h : w < 6 then (π ⟨w, h⟩ : ℕ) else w
  let gs' : List Gate := C.gates.map fun g => ⟨g.op, g.inputs.map rwW⟩
  refine ⟨⟨gs', rwW C.output⟩, ?_, by simpa [gs', Circuit.size] using hsz, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact ⟨(hok g0 hg0).1, by simp [(hok g0 hg0).2]⟩
  · intro x
    have hinv : ∀ (gs : List Gate) (w₁ w₂ : List Bool),
        w₁.length = w₂.length → 6 ≤ w₁.length →
        (∀ i, w₂.getD (rwW i) false = w₁.getD i false) →
        (wiresFrom (gs.map fun g => ⟨g.op, g.inputs.map rwW⟩) w₂).getD (rwW C.output) false =
          (wiresFrom gs w₁).getD C.output false := by
      intro gs
      induction gs with
      | nil => intro w₁ w₂ _ _ hag; exact hag C.output
      | cons g rest ih =>
        intro w₁ w₂ hlen hge hag
        simp only [List.map_cons, wiresFrom_cons]
        have hmap : ((g.inputs.map rwW).map fun i => w₂.getD i false) =
            (g.inputs.map fun i => w₁.getD i false) := by
          rw [List.map_map]
          apply List.map_congr_left
          intro i _
          exact hag i
        rw [hmap]
        apply ih
        · simp [hlen]
        · simp; omega
        · intro i
          by_cases hi6 : i < 6
          · have hpi : rwW i < 6 := by simp [rwW, hi6]
            rw [getD_snoc_lt _ _ _ _ (by omega), getD_snoc_lt _ _ _ _ (by omega)]
            exact hag i
          · have hrw : rwW i = i := by simp [rwW, hi6]
            rw [hrw]
            by_cases hlt : i < w₁.length
            · rw [getD_snoc_lt _ _ _ _ (by omega), getD_snoc_lt _ _ _ _ hlt]
              have := hag i; rwa [hrw] at this
            · by_cases heq : i = w₁.length
              · rw [getD_snoc_eq _ _ _ _ (by omega), getD_snoc_eq _ _ _ _ heq]
              · rw [List.getD_eq_default _ _ (by simp; omega),
                    List.getD_eq_default _ _ (by simp; omega)]
    have hinit : ∀ i, (List.ofFn x).getD (rwW i) false = (List.ofFn (x ∘ π)).getD i false := by
      intro i
      by_cases hi6 : i < 6
      · simp only [rwW, hi6, ↓reduceDIte]
        rw [ofFn_getD_lt _ _ _ (π ⟨i, hi6⟩).isLt, ofFn_getD_lt _ _ _ hi6]
        rfl
      · simp only [rwW, hi6, ↓reduceDIte]
        rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    have hEq := hinv C.gates (List.ofFn (x ∘ π)) (List.ofFn x) (by simp) (by simp) hinit
    exact hEq.trans (hev (x ∘ π))



private def fP4 (x : Fin 6 → Bool) : Bool :=
  (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4)

private def fC5 (x : Fin 6 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 0 && x 4)

private def fC5L (x : Fin 6 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 0 && x 4) || (x 0 && x 5)

private def maskToFn (m : ℕ) (v : Fin 6) : Bool := m.testBit v.val

private def fnToMask (f : Fin 6 → Bool) : ℕ :=
  (if f 0 then 1 else 0) + (if f 1 then 2 else 0) + (if f 2 then 4 else 0) +
  (if f 3 then 8 else 0) + (if f 4 then 16 else 0) + (if f 5 then 32 else 0)

private lemma fnToMask_lt (f : Fin 6 → Bool) : fnToMask f < 64 := by
  dsimp only [fnToMask]
  cases f 0 <;> cases f 1 <;> cases f 2 <;> cases f 3 <;> cases f 4 <;> cases f 5 <;> decide

private lemma fnToMask_testBit (f : Fin 6 → Bool) (v : Fin 6) :
    (fnToMask f).testBit v.val = f v := by
  have h : ∀ (b0 b1 b2 b3 b4 b5 : Bool) (i : Fin 6),
      (((if b0 then 1 else 0) + (if b1 then 2 else 0) + (if b2 then 4 else 0) +
        (if b3 then 8 else 0) + (if b4 then 16 else 0) + (if b5 then 32 else 0)).testBit i.val) =
        match i with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3 | 4 => b4 | 5 => b5 := by decide
  have h1 := h (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) v
  fin_cases v <;> exact h1

private def setToMask (S : Finset (Fin 6)) : ℕ :=
  fnToMask (fun v => decide (v ∈ S))

private lemma setToMask_lt (S : Finset (Fin 6)) : setToMask S < 64 :=
  fnToMask_lt _

private lemma setToMask_testBit (S : Finset (Fin 6)) (v : Fin 6) :
    (setToMask S).testBit v.val = decide (v ∈ S) :=
  fnToMask_testBit _ v

private def checkNFMask (F : (Fin 6 → Bool) → Bool) (sMask aMask : ℕ) : Bool :=
  let subs := List.range 64
  let xs := subs.filter fun x => (x &&& aMask) == x
  let ys := subs.filter fun y => (y &&& sMask) == y && (y &&& aMask) == 0
  let comb (x y : ℕ) (v : Fin 6) : Bool := if aMask.testBit v.val then x.testBit v.val else y.testBit v.val
  (xs.any fun x₁ => xs.any fun x₂ => xs.any fun x₃ =>
    ys.any (fun y₁₂ => F (comb x₁ y₁₂) != F (comb x₂ y₁₂)) &&
    ys.any (fun y₁₃ => F (comb x₁ y₁₃) != F (comb x₃ y₁₃)) &&
    ys.any (fun y₂₃ => F (comb x₂ y₂₃) != F (comb x₃ y₂₃))) ||
  (ys.any fun y₁ => ys.any fun y₂ => ys.any fun y₃ =>
    xs.any (fun x₁₂ => F (comb x₁₂ y₁) != F (comb x₁₂ y₂)) &&
    xs.any (fun x₁₃ => F (comb x₁₃ y₁) != F (comb x₁₃ y₃)) &&
    xs.any (fun x₂₃ => F (comb x₂₃ y₂) != F (comb x₂₃ y₃)))

private def checkNF (F : (Fin 6 → Bool) → Bool) (sMask : ℕ) : Bool :=
  (List.range 64).all fun aMask =>
    if (aMask &&& sMask) == aMask && aMask != 0 && aMask != sMask then
      checkNFMask F sMask aMask
    else true

private lemma notFactorable_of_checkNF {F : (Fin 6 → Bool) → Bool} {S : Finset (Fin 6)}
    (hchk : checkNF F (setToMask S) = true) : NotFactorable F S := by
  intro A hAS hAne hBne
  set sMask := setToMask S with hsMask
  set aMask := setToMask A with haMask
  have ha_lt : aMask < 64 := setToMask_lt A
  have ha_and : (aMask &&& sMask) = aMask := by
    apply Nat.eq_of_testBit_eq; intro i
    rw [Nat.testBit_and]
    by_cases hi6 : i < 6
    · let v : Fin 6 := ⟨i, hi6⟩
      have h1 := setToMask_testBit A v
      have h2 := setToMask_testBit S v
      change aMask.testBit i = decide (v ∈ A) at h1
      change sMask.testBit i = decide (v ∈ S) at h2
      rw [h1, h2]
      by_cases hv : v ∈ A
      · simp [hv, hAS hv]
      · simp [hv]
    · have h6 : 64 ≤ 2 ^ i := by
        have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (show 6 ≤ i by omega)
        norm_num at this ⊢; exact this
      rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le ha_lt h6)]; simp
  have ha_ne0 : aMask ≠ 0 := by
    intro h0
    obtain ⟨v, hv⟩ := hAne
    have := setToMask_testBit A v
    rw [← haMask, h0, Nat.zero_testBit] at this
    simp [hv] at this
  have ha_nes : aMask ≠ sMask := by
    intro hEq
    obtain ⟨v, hv⟩ := hBne
    have hvS := (Finset.mem_sdiff.1 hv).1
    have hvA := (Finset.mem_sdiff.1 hv).2
    have h1 := setToMask_testBit A v
    have h2 := setToMask_testBit S v
    rw [← haMask, hEq, hsMask, h2] at h1
    simp [hvS, hvA] at h1
  have hmem : aMask ∈ List.range 64 := List.mem_range.2 ha_lt
  have hall := List.all_eq_true.1 hchk aMask hmem
  have hcond : ((aMask &&& sMask) == aMask && aMask != 0 && aMask != sMask) = true := by
    simp [ha_and, ha_ne0, ha_nes]
  simp only [hcond, ↓reduceIte] at hall
  have hcomb : ∀ x y : ℕ,
      (fun v : Fin 6 => if v ∈ A then maskToFn x v else maskToFn y v) =
      (fun v : Fin 6 => if aMask.testBit v.val then x.testBit v.val else y.testBit v.val) := by
    intro x y; funext v
    have htb := setToMask_testBit A v
    rw [← haMask] at htb
    by_cases hv : v ∈ A
    · have h1 : aMask.testBit v.val = true := by simpa [hv] using htb
      simp [hv, h1, maskToFn]
    · have h0 : aMask.testBit v.val = false := by simpa [hv] using htb
      simp [hv, h0, maskToFn]
  simp only [checkNFMask, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, bne_iff_ne] at hall
  rcases hall with
    ⟨x₁, _, x₂, _, x₃, _, ⟨⟨y₁₂, _, h12⟩, ⟨y₁₃, _, h13⟩⟩, ⟨y₂₃, _, h23⟩⟩ |
    ⟨y₁, _, y₂, _, y₃, _, ⟨⟨x₁₂, _, h12⟩, ⟨x₁₃, _, h13⟩⟩, ⟨x₂₃, _, h23⟩⟩
  · exact Or.inl ⟨maskToFn x₁, maskToFn x₂, maskToFn x₃, maskToFn y₁₂, maskToFn y₁₃, maskToFn y₂₃,
      by rw [hcomb, hcomb]; exact h12, by rw [hcomb, hcomb]; exact h13, by rw [hcomb, hcomb]; exact h23⟩
  · exact Or.inr ⟨maskToFn y₁, maskToFn y₂, maskToFn y₃, maskToFn x₁₂, maskToFn x₁₃, maskToFn x₂₃,
      by rw [hcomb, hcomb]; exact h12, by rw [hcomb, hcomb]; exact h13, by rw [hcomb, hcomb]; exact h23⟩

private def sP4 : Finset (Fin 6) := {1, 2, 3, 4}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
private lemma notFactorable_fP4 : NotFactorable fP4 sP4 := by
  apply notFactorable_of_checkNF
  have hm : setToMask sP4 = 30 := by decide
  rw [hm]
  decide +kernel

private lemma dep_of_mask {F : (Fin 6 → Bool) → Bool} (v : Fin 6) (m : ℕ)
    (h : F (Function.update (maskToFn m) v false) ≠ F (Function.update (maskToFn m) v true)) :
    DependsOn F v := ⟨maskToFn m, h⟩

private lemma nonConst_of_masks {F : (Fin 6 → Bool) → Bool} (m₁ m₂ : ℕ)
    (h : F (maskToFn m₁) ≠ F (maskToFn m₂)) : NonConst F := ⟨maskToFn m₁, maskToFn m₂, h⟩

private lemma dep_iff_fP4 (v : Fin 6) : DependsOn fP4 v ↔ v ∈ sP4 := by
  constructor
  · intro ⟨x, hx⟩
    fin_cases v
    · exfalso; apply hx; simp [fP4, Function.update]
    · simp [sP4]
    · simp [sP4]
    · simp [sP4]
    · simp [sP4]
    · exfalso; apply hx; simp [fP4, Function.update]
  · intro hv
    simp only [sP4, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact dep_of_mask 1 4 (by decide)
    · exact dep_of_mask 2 2 (by decide)
    · exact dep_of_mask 3 4 (by decide)
    · exact dep_of_mask 4 8 (by decide)

private lemma size_P4_ge (s : ℕ) (h : HasCircuitSize 6 fP4 s) : 4 ≤ s := by
  by_contra hlt
  have hnc : NonConst fP4 := nonConst_of_masks 0 6 (by decide)
  obtain ⟨C, hmin, hle⟩ := exists_min_of_hasCircuitSize h
  have hcl := clean_of_min hmin hnc
  have hout := clean_out_ge6 hcl (by decide : (1 : Fin 6) ≠ 2)
    ((dep_iff_fP4 1).2 (by decide)) ((dep_iff_fP4 2).2 (by decide))
  have hslot := clean_slot_count hcl hout sP4 (fun v hv => (dep_iff_fP4 v).2 hv)
  have hcard : sP4.card = 4 := by decide
  have hlen : (C.gates.map normGate).length = C.size := by simp [Circuit.size]
  have heq : sP4.card + ((C.gates.map normGate).filter fun g => isNotOp g.op).length =
      (C.gates.map normGate).length + 1 := by omega
  exact not_read_once_of_notFactorable hcl (hslot.2 heq) sP4 dep_iff_fP4 (by omega) notFactorable_fP4

private lemma clean_no_equiv_wire {F : (Fin 6 → Bool) → Bool} {gs : List Gate} {out : ℕ}
    (hcl : CleanCircuit F gs out) (hnc : NonConst F) {j w : ℕ}
    (hj : j < gs.length) (hw : w < 6 + j)
    (heqv : ∀ x : Fin 6 → Bool,
      (wiresFrom gs (List.ofFn x)).getD (6 + j) false =
      (wiresFrom gs (List.ofFn x)).getD w false) : False := by
  have hsp : gs = gs.take j ++ gs[j] :: gs.drop (j + 1) := by
    conv_lhs => rw [← List.take_append_drop j gs]
    rw [List.drop_eq_getElem_cons hj]
  set initJ : List (Bool ⊕ ℕ) := (List.range (6 + j)).map Sum.inr ++ [Sum.inr w] with hinitJ
  set acc := elimPass 6 (gs.drop (j + 1)) (initJ, gs.take j) with hacc
  have hok_take : ∀ g ∈ gs.take j, OkGate g := by
    intro g hg
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hg
    have hk' : k < gs.length := by simp at hk; omega
    have hgt : (gs.take j)[k] = gs[k] := by simp
    rw [hgt]; exact (hcl.1 k hk').2.2.1
  have hok_drop : ∀ g ∈ gs.drop (j + 1), OkGate g := by
    intro g hg
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hg
    have hk' : j + 1 + k < gs.length := by simp at hk; omega
    have hgt : (gs.drop (j + 1))[k] = gs[j + 1 + k] := by simp
    rw [hgt]; exact (hcl.1 (j + 1 + k) hk').2.2.1
  have hlen : acc.2.length + 1 ≤ gs.length := by
    have h1 := elimPass_len 6 (gs.drop (j + 1)) (initJ, gs.take j)
    rw [← hacc] at h1
    simp only [List.length_take, List.length_drop, Nat.min_eq_left (Nat.le_of_lt hj)] at h1
    omega
  have hinv_init : ∀ x : Fin 6 → Bool,
      ElimInv 6 (List.ofFn x) (wiresFrom (gs.take j ++ [gs[j]]) (List.ofFn x)) (initJ, gs.take j) := by
    intro x
    set w0 := wiresFrom (gs.take j) (List.ofFn x) with hw0
    have hw0_len : w0.length = 6 + j := by
      simp [hw0, wiresFrom_length, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
    have hw1_len : (wiresFrom (gs.take j ++ [gs[j]]) (List.ofFn x)).length = 6 + j + 1 := by
      simp [wiresFrom_length, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]; omega
    refine ⟨by simp, ?_, ?_⟩
    · simp only [hinitJ, List.length_append, List.length_map, List.length_range,
        List.length_singleton, hw1_len]
    intro i
    by_cases hilt : i < 6 + j
    · have hget : initJ.getD i (Sum.inl false) = Sum.inr i := by
        rw [hinitJ, getD_snoc_lt _ _ _ _ (by simp; omega)]
        simp [List.getD, hilt]
      rw [hget]
      refine ⟨by simp [statValid, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj), hilt], ?_⟩
      simp only [statVal, wiresFrom_append, ← hw0, wiresFrom_cons, wiresFrom_nil]
      rw [getD_snoc_lt _ _ _ _ (by omega)]
    · by_cases heq : i = 6 + j
      · subst heq
        have hget : initJ.getD (6 + j) (Sum.inl false) = Sum.inr w := by
          rw [hinitJ, getD_snoc_eq _ _ _ _ (by simp)]
        rw [hget]
        refine ⟨by simp [statValid, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj), hw], ?_⟩
        simp only [statVal, ← hw0]
        have h1 : (wiresFrom gs (List.ofFn x)).getD (6 + j) false =
            (wiresFrom (gs.take j ++ [gs[j]]) (List.ofFn x)).getD (6 + j) false := by
          have hsp' : gs = (gs.take j ++ [gs[j]]) ++ gs.drop (j + 1) := by simpa using hsp
          conv_lhs => rw [hsp', wiresFrom_append]
          exact wiresFrom_getD_lt _ _ _ (by omega)
        have h2 : (wiresFrom gs (List.ofFn x)).getD w false = w0.getD w false := by
          conv_lhs => rw [hsp, wiresFrom_append]
          rw [← hw0]
          exact wiresFrom_getD_lt _ _ _ (by omega)
        rw [← h1, heqv x, h2]
      · rw [List.getD_eq_default _ _ (by simp [hinitJ]; omega),
            List.getD_eq_default _ _ (by omega)]
        exact ⟨trivial, rfl⟩
  have hval : ∀ x : Fin 6 → Bool,
      statVal (wiresFrom acc.2 (List.ofFn x)) (acc.1.getD out (Sum.inl false)) = F x := by
    intro x
    have hinv := elimInv_pass 6 (List.ofFn x) (gs.drop (j + 1)) _ (initJ, gs.take j)
      hok_drop (hinv_init x)
    rw [← hacc] at hinv
    have hcat : wiresFrom (gs.drop (j + 1)) (wiresFrom (gs.take j ++ [gs[j]]) (List.ofFn x)) =
        wiresFrom gs (List.ofFn x) := by
      rw [← wiresFrom_append]
      have hsp' : (gs.take j ++ [gs[j]]) ++ gs.drop (j + 1) = gs := by simpa using hsp.symm
      rw [hsp']
    rw [(hinv.2.2 out).2, hcat]
    exact hcl.2.2.1 x
  cases hst : acc.1.getD out (Sum.inl false) with
  | inl c =>
    obtain ⟨x, y, hxy⟩ := hnc
    have hx := hval x; have hy := hval y; rw [hst] at hx hy
    exact hxy (hx.symm.trans hy)
  | inr o =>
    have hge : gs.length ≤ acc.2.length :=
      hcl.2.2.2.2.2.2 ⟨acc.2, o⟩ (elimPass_ok 6 _ _ hok_take)
        (fun x => by have := hval x; rw [hst] at this; exact this)
    omega

private lemma antitone_of_only_first_not {gs : List Gate} {a : Fin 6} {out : ℕ}
    (hout : out ≠ (a : ℕ)) (h0 : gs ≠ [])
    (hg0 : gs.head h0 = ⟨GateOp.not, [(a : ℕ)]⟩)
    (hrest : ∀ g ∈ gs.tail, (a : ℕ) ∉ g.inputs ∧ (g.op = GateOp.and ∨ g.op = GateOp.or))
    (x : Fin 6 → Bool) :
    (wiresFrom gs (List.ofFn (Function.update x a true))).getD out false = true →
    (wiresFrom gs (List.ofFn (Function.update x a false))).getD out false = true := by
  have hmono : ∀ (l : List Gate) (w₁ w₂ : List Bool),
      w₁.length = w₂.length → 6 ≤ w₁.length →
      (∀ g ∈ l, (a : ℕ) ∉ g.inputs ∧ (g.op = GateOp.and ∨ g.op = GateOp.or)) →
      (∀ i, i ≠ (a : ℕ) → w₁.getD i false = true → w₂.getD i false = true) →
      ∀ i, i ≠ (a : ℕ) → (wiresFrom l w₁).getD i false = true →
        (wiresFrom l w₂).getD i false = true := by
    intro l
    induction l with
    | nil => intro w₁ w₂ _ _ _ hle i hi; exact hle i hi
    | cons g rest ih =>
      intro w₁ w₂ hlen h8 hok hle
      have hg := hok g (by simp)
      have hstep : g.op.eval (g.inputs.map fun i => w₁.getD i false) = true →
          g.op.eval (g.inputs.map fun i => w₂.getD i false) = true := by
        intro ht
        rcases hg.2 with hop | hop
        · rw [hop] at ht ⊢
          simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq] at ht ⊢
          rintro _ ⟨i, hi, rfl⟩
          exact hle i (fun h => hg.1 (h ▸ hi)) (ht _ ⟨i, hi, rfl⟩)
        · rw [hop] at ht ⊢
          simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at ht ⊢
          rcases ht with ⟨_, ⟨i, hi, rfl⟩, h1⟩
          exact ⟨_, ⟨i, hi, rfl⟩, hle i (fun h => hg.1 (h ▸ hi)) h1⟩
      rw [wiresFrom_cons, wiresFrom_cons]
      apply ih _ _ (by simp [hlen]) (by simp; omega) (fun g' hg' => hok g' (by simp [hg']))
      intro i hi h1
      by_cases hlt : i < w₁.length
      · rw [getD_snoc_lt _ _ _ _ hlt] at h1
        rw [getD_snoc_lt _ _ _ _ (by omega)]
        exact hle i hi h1
      · by_cases heq : i = w₁.length
        · rw [getD_snoc_eq _ _ _ _ heq] at h1
          rw [getD_snoc_eq _ _ _ _ (by omega)]
          exact hstep h1
        · rw [List.getD_eq_default _ _ (by simp; omega)] at h1
          simp at h1
  rcases gs with _ | ⟨g, rest⟩
  · exact absurd rfl h0
  · simp only [List.head_cons] at hg0
    subst hg0
    simp only [List.tail_cons] at hrest
    rw [wiresFrom_cons, wiresFrom_cons]
    apply hmono rest _ _ (by simp) (by simp) hrest _ out hout
    intro i hi h1
    by_cases hi6 : i < 6
    · rw [getD_snoc_lt _ _ _ _ (by simp; exact hi6)] at h1 ⊢
      rw [ofFn_getD_lt _ _ _ hi6] at h1 ⊢
      have hne : (⟨i, hi6⟩ : Fin 6) ≠ a := fun h => hi (congrArg Fin.val h)
      rw [Function.update_of_ne hne] at h1 ⊢
      exact h1
    · by_cases heq6 : i = 6
      · subst heq6
        rw [getD_snoc_eq _ _ _ _ (by simp)] at h1 ⊢
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.headD_cons,
          ofFn_getD_lt _ _ _ a.isLt, Fin.eta, Function.update_self, Bool.not_true] at h1
        exact absurd h1 (by decide)
      · rw [List.getD_eq_default _ _ (by simp; omega)] at h1
        simp at h1



private lemma dep_iff_fC5 (v : Fin 6) : DependsOn fC5 v ↔ v.val < 5 := by
  constructor
  · intro ⟨x, hx⟩
    fin_cases v
    · decide
    · decide
    · decide
    · decide
    · decide
    · exfalso; apply hx; simp [fC5, Function.update]
  · intro hv
    fin_cases v <;> dsimp only at hv ⊢
    · exact dep_of_mask 0 2 (by decide)
    · exact dep_of_mask 1 1 (by decide)
    · exact dep_of_mask 2 2 (by decide)
    · exact dep_of_mask 3 4 (by decide)
    · exact dep_of_mask 4 8 (by decide)
    · omega

private def p4FromC5 (v : Fin 5) (i : Fin 6) : Fin 6 :=
  if i.val < 5 then
    let d := (i.val + 5 - v.val) % 5
    match d with
    | 1 => 1
    | 2 => 2
    | 3 => 3
    | 4 => 4
    | _ => 0
  else 5

private lemma size_C5_restrict_false (v : Fin 5) (s : ℕ)
    (h : HasCircuitSize 6 (Restrict fC5 ⟨v.val, by omega⟩ false) s) : 4 ≤ s := by
  have hcomp := hasCircuitSize_comp (p4FromC5 v) h
  have heq : (fun x => Restrict fC5 ⟨v.val, by omega⟩ false (x ∘ p4FromC5 v)) = fP4 := by
    funext x
    fin_cases v <;>
      (simp [Restrict, fC5, fP4, Function.comp_apply, p4FromC5, Function.update]
       try (cases x 1 <;> cases x 2 <;> cases x 3 <;> cases x 4 <;> decide))
  rw [heq] at hcomp
  exact size_P4_ge s hcomp

private lemma fC5_S'_card (v : Fin 5) :
    (({0, 1, 2, 3, 4} : Finset (Fin 6)).erase ⟨v.val, by omega⟩).card = 4 := by
  fin_cases v <;> decide

private lemma fC5_S'_dep (v : Fin 5) :
    ∀ w ∈ (({0, 1, 2, 3, 4} : Finset (Fin 6)).erase ⟨v.val, by omega⟩),
      DependsOn (Restrict fC5 ⟨v.val, by omega⟩ true) w := by
  intro w hw
  fin_cases v <;> fin_cases w
  all_goals dsimp only at hw ⊢
  all_goals
    try (simp at hw)
    try exact dep_of_mask _ 0 (by decide)
    try exact dep_of_mask _ 1 (by decide)
    try exact dep_of_mask _ 2 (by decide)
    try exact dep_of_mask _ 4 (by decide)
    try exact dep_of_mask _ 8 (by decide)
    try exact dep_of_mask _ 16 (by decide)

private lemma fC5_anti_witness (v : Fin 5) :
    ∃ x : Fin 6 → Bool,
      fC5 (Function.update x ⟨v.val, by omega⟩ true) = true ∧
      fC5 (Function.update x ⟨v.val, by omega⟩ false) = false := by
  fin_cases v
  · exact ⟨maskToFn 2, by decide, by decide⟩
  · exact ⟨maskToFn 4, by decide, by decide⟩
  · exact ⟨maskToFn 8, by decide, by decide⟩
  · exact ⟨maskToFn 16, by decide, by decide⟩
  · exact ⟨maskToFn 1, by decide, by decide⟩

private lemma size_C5_restrict_true (v : Fin 5) (s : ℕ)
    (h : HasCircuitSize 6 (Restrict fC5 ⟨v.val, by omega⟩ true) s) : 3 ≤ s := by
  have hcard := fC5_S'_card v
  have := ess_le_size_add_one h _ (fC5_S'_dep v) (by omega)
  omega

private lemma fC5_nc_false (v : Fin 5) : NonConst (Restrict fC5 ⟨v.val, by omega⟩ false) := by
  fin_cases v
  · exact nonConst_of_masks 0 6 (by decide)
  · exact nonConst_of_masks 0 12 (by decide)
  · exact nonConst_of_masks 0 24 (by decide)
  · exact nonConst_of_masks 0 3 (by decide)
  · exact nonConst_of_masks 0 3 (by decide)

private lemma fC5_nc_true (v : Fin 5) : NonConst (Restrict fC5 ⟨v.val, by omega⟩ true) := by
  fin_cases v
  · exact nonConst_of_masks 0 2 (by decide)
  · exact nonConst_of_masks 0 1 (by decide)
  · exact nonConst_of_masks 0 2 (by decide)
  · exact nonConst_of_masks 0 4 (by decide)
  · exact nonConst_of_masks 0 8 (by decide)

private lemma fC5_dep_pair_false (a b : Fin 5) (hab : a ≠ b) :
    ∃ x : Fin 6 → Bool,
      fC5 (Function.update (Function.update x ⟨b.val, by omega⟩ false) ⟨a.val, by omega⟩ false) ≠
      fC5 (Function.update (Function.update x ⟨b.val, by omega⟩ false) ⟨a.val, by omega⟩ true) := by
  fin_cases a <;> fin_cases b
  all_goals
    try (exfalso; exact hab rfl)
    try exact ⟨maskToFn 1, by decide⟩
    try exact ⟨maskToFn 2, by decide⟩
    try exact ⟨maskToFn 4, by decide⟩
    try exact ⟨maskToFn 8, by decide⟩
    try exact ⟨maskToFn 16, by decide⟩

private lemma fC5_dep_pair_true (a b : Fin 5) (hab : a ≠ b) :
    ∃ x : Fin 6 → Bool,
      fC5 (Function.update (Function.update x ⟨b.val, by omega⟩ true) ⟨a.val, by omega⟩ false) ≠
      fC5 (Function.update (Function.update x ⟨b.val, by omega⟩ true) ⟨a.val, by omega⟩ true) := by
  fin_cases a <;> fin_cases b
  all_goals
    try (exfalso; exact hab rfl)
    try exact ⟨maskToFn 0, by decide⟩
    try exact ⟨maskToFn 1, by decide⟩
    try exact ⟨maskToFn 2, by decide⟩
    try exact ⟨maskToFn 4, by decide⟩
    try exact ⟨maskToFn 8, by decide⟩
    try exact ⟨maskToFn 16, by decide⟩

private lemma elimPass_gives_circuit {F : (Fin 6 → Bool) → Bool} {gs : List Gate} {out : ℕ}
    (hcl : CleanCircuit F gs out) (v : Fin 6) (b : Bool) (hnc : NonConst (Restrict F v b)) :
    ∃ o : ℕ, (elimPass 6 gs (initVar 6 v b, [])).1.getD out (Sum.inl false) = Sum.inr o ∧
      FanInTwo ⟨(elimPass 6 gs (initVar 6 v b, [])).2, o⟩ ∧
      (∀ x : Fin 6 → Bool, (⟨(elimPass 6 gs (initVar 6 v b, [])).2, o⟩ : Circuit).eval (List.ofFn x) =
        Restrict F v b x) := by
  set acc := elimPass 6 gs (initVar 6 v b, []) with hacc
  have hok_gs : ∀ g ∈ gs, OkGate g := by
    intro g hg; obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hg; exact (hcl.1 k hk).2.2.1
  have hval : ∀ x : Fin 6 → Bool,
      statVal (wiresFrom acc.2 (List.ofFn x)) (acc.1.getD out (Sum.inl false)) =
        Restrict F v b x := by
    intro x
    have hinv := elimInv_pass 6 (List.ofFn x) gs _ (initVar 6 v b, []) hok_gs (elimInv_initVar 6 v b x)
    rw [← hacc] at hinv
    rw [(hinv.2.2 out).2]
    exact hcl.2.2.1 (Function.update x v b)
  cases hst : acc.1.getD out (Sum.inl false) with
  | inl c =>
    obtain ⟨x, y, hxy⟩ := hnc
    have hx := hval x; have hy := hval y; rw [hst] at hx hy
    exact absurd (hx.symm.trans hy) hxy
  | inr o =>
    refine ⟨o, rfl, elimPass_ok 6 gs _ (by simp), fun x => ?_⟩
    have := hval x; rw [hst] at this; exact this

private lemma elim_gate_and_false {gs : List Gate} {init : List (Bool ⊕ ℕ)}
    (hinit : init.length = 6) {k w : ℕ} (hk : k < gs.length)
    (hop : gs[k].op = GateOp.and) (hlen : gs[k].inputs.length ≤ 2)
    (hw : w ∈ gs[k].inputs) (hwlt : w < 6 + k)
    (hc : (elimPass 6 gs (init, [])).1.getD w (Sum.inl false) = Sum.inl false) :
    (elimPass 6 gs (init, [])).1.getD (6 + k) (Sum.inl false) = Sum.inl false := by
  have h1 := elimPass_getD_gate gs init hinit hk
  rw [hop] at h1
  have hst : (stateAt gs init k).1.getD w (Sum.inl false) = Sum.inl false := by
    rw [stateAt_getD gs init k w (by omega) (Nat.le_of_lt hk), hc]
  have hmem : Sum.inl false ∈ (gs[k].inputs.map fun i => (stateAt gs init k).1.getD i (Sum.inl false)) :=
    List.mem_map.2 ⟨w, hw, hst⟩
  have hsf := simplifyGate_and_false (6 + (stateAt gs init k).2.length) _ (by simp; exact hlen) hmem
  rw [hsf] at h1
  exact h1

private lemma elim_gate_or_true {gs : List Gate} {init : List (Bool ⊕ ℕ)}
    (hinit : init.length = 6) {k w : ℕ} (hk : k < gs.length)
    (hop : gs[k].op = GateOp.or) (hlen : gs[k].inputs.length ≤ 2)
    (hw : w ∈ gs[k].inputs) (hwlt : w < 6 + k)
    (hc : (elimPass 6 gs (init, [])).1.getD w (Sum.inl false) = Sum.inl true) :
    (elimPass 6 gs (init, [])).1.getD (6 + k) (Sum.inl false) = Sum.inl true := by
  have h1 := elimPass_getD_gate gs init hinit hk
  rw [hop] at h1
  have hst : (stateAt gs init k).1.getD w (Sum.inl false) = Sum.inl true := by
    rw [stateAt_getD gs init k w (by omega) (Nat.le_of_lt hk), hc]
  have hmem : Sum.inl true ∈ (gs[k].inputs.map fun i => (stateAt gs init k).1.getD i (Sum.inl false)) :=
    List.mem_map.2 ⟨w, hw, hst⟩
  have hsf := simplifyGate_or_true (6 + (stateAt gs init k).2.length) _ (by simp; exact hlen) hmem
  rw [hsf] at h1
  exact h1

private lemma elim_gate_not_const {gs : List Gate} {init : List (Bool ⊕ ℕ)}
    (hinit : init.length = 6) {k w : ℕ} (hk : k < gs.length)
    (hop : gs[k].op = GateOp.not) (hins : gs[k].inputs = [w]) (hwlt : w < 6 + k)
    {c : Bool} (hc : (elimPass 6 gs (init, [])).1.getD w (Sum.inl false) = Sum.inl c) :
    (elimPass 6 gs (init, [])).1.getD (6 + k) (Sum.inl false) = Sum.inl (!c) := by
  have h1 := elimPass_getD_gate gs init hinit hk
  rw [hop, hins] at h1
  have hst : (stateAt gs init k).1.getD w (Sum.inl false) = Sum.inl c := by
    rw [stateAt_getD gs init k w (by omega) (Nat.le_of_lt hk), hc]
  simp only [List.map_cons, List.map_nil, hst, simplifyGate_not_const] at h1
  exact h1

private lemma elim_gate_both_const {gs : List Gate} {init : List (Bool ⊕ ℕ)}
    (hinit : init.length = 6) {k u w : ℕ} (hk : k < gs.length)
    (hcg : CleanGate k gs[k]) (h1in : u ∈ gs[k].inputs) (h2in : w ∈ gs[k].inputs)
    (huw : u ≠ w) (hult : u < 6 + k) (hwlt : w < 6 + k) {c₁ c₂ : Bool}
    (hc₁ : (elimPass 6 gs (init, [])).1.getD u (Sum.inl false) = Sum.inl c₁)
    (hc₂ : (elimPass 6 gs (init, [])).1.getD w (Sum.inl false) = Sum.inl c₂) :
    ∃ c, (elimPass 6 gs (init, [])).1.getD (6 + k) (Sum.inl false) = Sum.inl c := by
  have h1 := elimPass_getD_gate gs init hinit hk
  have hst₁ : (stateAt gs init k).1.getD u (Sum.inl false) = Sum.inl c₁ := by
    rw [stateAt_getD gs init k u (by omega) (Nat.le_of_lt hk), hc₁]
  have hst₂ : (stateAt gs init k).1.getD w (Sum.inl false) = Sum.inl c₂ := by
    rw [stateAt_getD gs init k w (by omega) (Nat.le_of_lt hk), hc₂]
  rcases hcg.2.2.1.1 with hop | hop | hop
  · obtain ⟨a, b, hgi, _, _, _⟩ := hcg.1 (Or.inl hop)
    have hset : (a = u ∧ b = w) ∨ (a = w ∧ b = u) := by
      rw [hgi] at h1in h2in; simp at h1in h2in
      rcases h1in with rfl | rfl <;> rcases h2in with h | h <;>
        first | exact Or.inl ⟨rfl, h.symm⟩ | exact Or.inr ⟨h.symm, rfl⟩ | exact absurd h huw | exact absurd h.symm huw
    have hop' : gs[k].op = GateOp.and := hop
    rw [hop', hgi] at h1
    rcases hset with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp only [List.map_cons, List.map_nil, hst₁, hst₂, simplifyGate, simpAnd] at h1
      exact ⟨c₁ && c₂, h1⟩
    · simp only [List.map_cons, List.map_nil, hst₁, hst₂, simplifyGate, simpAnd] at h1
      exact ⟨c₂ && c₁, h1⟩
  · obtain ⟨a, b, hgi, _, _, _⟩ := hcg.1 (Or.inr hop)
    have hset : (a = u ∧ b = w) ∨ (a = w ∧ b = u) := by
      rw [hgi] at h1in h2in; simp at h1in h2in
      rcases h1in with rfl | rfl <;> rcases h2in with h | h <;>
        first | exact Or.inl ⟨rfl, h.symm⟩ | exact Or.inr ⟨h.symm, rfl⟩ | exact absurd h huw | exact absurd h.symm huw
    have hop' : gs[k].op = GateOp.or := hop
    rw [hop', hgi] at h1
    rcases hset with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp only [List.map_cons, List.map_nil, hst₁, hst₂, simplifyGate, simpOr] at h1
      exact ⟨c₁ || c₂, h1⟩
    · simp only [List.map_cons, List.map_nil, hst₁, hst₂, simplifyGate, simpOr] at h1
      exact ⟨c₂ || c₁, h1⟩
  · obtain ⟨a, hgi, _⟩ := hcg.2.1 hop
    rw [hgi] at h1in h2in; simp at h1in h2in
    exact absurd (h1in.trans h2in.symm) huw

private lemma elimPass_initVar_self (gs : List Gate) (v : Fin 6) (b : Bool) :
    (elimPass 6 gs (initVar 6 v b, [])).1.getD (v : ℕ) (Sum.inl false) = Sum.inl b := by
  have hlt : (v : ℕ) < (initVar 6 v b, ([] : List Gate)).1.length := by simp [initVar]
  rw [elimPass_getD_lt 6 (v : ℕ) (Sum.inl false) gs _ hlt, initVar, ofFn_getD_lt _ _ _ v.isLt]
  simp


private lemma size_C5_ge (s : ℕ) (h : HasCircuitSize 6 fC5 s) : 7 ≤ s := by
  by_contra hlt
  have hnc : NonConst fC5 := nonConst_of_masks 0 3 (by decide)
  obtain ⟨C, hmin, hle⟩ := exists_min_of_hasCircuitSize h
  have hcl := clean_of_min hmin hnc
  set gs := C.gates.map normGate with hgs
  set out := C.output with hout_def
  have hgs_len : gs.length = C.size := by simp [hgs, Circuit.size]
  have hgs_le : gs.length ≤ 6 := by omega
  have hgs_ge : 4 ≤ gs.length := by
    have h5 := ess_le_size_add_one ⟨C, hmin.1, le_refl _, hmin.2.1⟩
      {0, 1, 2, 3, 4} (fun v hv => (dep_iff_fC5 v).2 (by fin_cases v <;> simp at hv ⊢)) (by decide)
    have hc : ({0, 1, 2, 3, 4} : Finset (Fin 6)).card = 5 := by decide
    omega
  have hpos : 0 < gs.length := by omega
  have hnok_gs : ∀ g ∈ gs, NOkGate g := by
    intro g hg; obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hg; exact (hcl.1 k hk).2.2
  have hvar_lt5 : ∀ i ∈ gs[0].inputs, i < 5 := by
    intro i hi
    have hi6 : i < 6 := clean_inputs_lt hcl 0 hpos i hi
    by_contra hge5
    have hndep : ¬ DependsOn fC5 ⟨i, hi6⟩ := by rw [dep_iff_fC5]; omega
    exact hcl.2.2.2.2.1 ⟨i, hi6⟩ hndep gs[0] (List.getElem_mem hpos) hi
  have hout_ge6 : 6 ≤ out :=
    clean_out_ge6 hcl (by decide : (0 : Fin 6) ≠ 1)
      ((dep_iff_fC5 0).2 (by omega)) ((dep_iff_fC5 1).2 (by omega))
  have hdrop_le_false : ∀ a : Fin 5,
      ((Finset.range gs.length).filter fun k =>
        isDropped gs (initVar 6 ⟨a.val, by omega⟩ false) k = true).card ≤ 2 := by
    intro a
    obtain ⟨o, _, hok', hev'⟩ := elimPass_gives_circuit hcl ⟨a.val, by omega⟩ false (fC5_nc_false a)
    have h4 := size_C5_restrict_false a (elimPass 6 gs (initVar 6 ⟨a.val, by omega⟩ false, [])).2.length
      ⟨⟨_, o⟩, hok', le_refl _, hev'⟩
    have hcard := (elimPass_dropped_card gs (initVar 6 ⟨a.val, by omega⟩ false)).1
    omega
  have hdrop_le_true : ∀ a : Fin 5,
      ((Finset.range gs.length).filter fun k =>
        isDropped gs (initVar 6 ⟨a.val, by omega⟩ true) k = true).card ≤ 3 := by
    intro a
    obtain ⟨o, _, hok', hev'⟩ := elimPass_gives_circuit hcl ⟨a.val, by omega⟩ true (fC5_nc_true a)
    have h3 := size_C5_restrict_true a (elimPass 6 gs (initVar 6 ⟨a.val, by omega⟩ true, [])).2.length
      ⟨⟨_, o⟩, hok', le_refl _, hev'⟩
    have hcard := (elimPass_dropped_card gs (initVar 6 ⟨a.val, by omega⟩ true)).1
    omega
  have hcontra3F : ∀ (a : Fin 5) (k₁ k₂ k₃ : ℕ),
      k₁ < gs.length → k₂ < gs.length → k₃ < gs.length →
      k₁ ≠ k₂ → k₁ ≠ k₃ → k₂ ≠ k₃ →
      isDropped gs (initVar 6 ⟨a.val, by omega⟩ false) k₁ = true →
      isDropped gs (initVar 6 ⟨a.val, by omega⟩ false) k₂ = true →
      isDropped gs (initVar 6 ⟨a.val, by omega⟩ false) k₃ = true → False := by
    intro a k₁ k₂ k₃ hk₁ hk₂ hk₃ h12 h13 h23 hd₁ hd₂ hd₃
    have hsub : ({k₁, k₂, k₃} : Finset ℕ) ⊆
        (Finset.range gs.length).filter (fun i => isDropped gs (initVar 6 ⟨a.val, by omega⟩ false) i = true) := by
      intro i hi; simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl | rfl
      · exact Finset.mem_filter.2 ⟨Finset.mem_range.2 hk₁, hd₁⟩
      · exact Finset.mem_filter.2 ⟨Finset.mem_range.2 hk₂, hd₂⟩
      · exact Finset.mem_filter.2 ⟨Finset.mem_range.2 hk₃, hd₃⟩
    have h3 : ({k₁, k₂, k₃} : Finset ℕ).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [h12, h13]),
          Finset.card_insert_of_notMem (by simp [h23]), Finset.card_singleton]
    have := Finset.card_le_card hsub
    have := hdrop_le_false a
    omega
  have hcontra4T : ∀ (a : Fin 5) (k₁ k₂ k₃ k₄ : ℕ),
      k₁ < gs.length → k₂ < gs.length → k₃ < gs.length → k₄ < gs.length →
      k₁ ≠ k₂ → k₁ ≠ k₃ → k₁ ≠ k₄ → k₂ ≠ k₃ → k₂ ≠ k₄ → k₃ ≠ k₄ →
      isDropped gs (initVar 6 ⟨a.val, by omega⟩ true) k₁ = true →
      isDropped gs (initVar 6 ⟨a.val, by omega⟩ true) k₂ = true →
      isDropped gs (initVar 6 ⟨a.val, by omega⟩ true) k₃ = true →
      isDropped gs (initVar 6 ⟨a.val, by omega⟩ true) k₄ = true → False := by
    intro a k₁ k₂ k₃ k₄ hk₁ hk₂ hk₃ hk₄ h12 h13 h14 h23 h24 h34 hd₁ hd₂ hd₃ hd₄
    have hsub : ({k₁, k₂, k₃, k₄} : Finset ℕ) ⊆
        (Finset.range gs.length).filter (fun i => isDropped gs (initVar 6 ⟨a.val, by omega⟩ true) i = true) := by
      intro i hi; simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl | rfl | rfl
      · exact Finset.mem_filter.2 ⟨Finset.mem_range.2 hk₁, hd₁⟩
      · exact Finset.mem_filter.2 ⟨Finset.mem_range.2 hk₂, hd₂⟩
      · exact Finset.mem_filter.2 ⟨Finset.mem_range.2 hk₃, hd₃⟩
      · exact Finset.mem_filter.2 ⟨Finset.mem_range.2 hk₄, hd₄⟩
    have h4 : ({k₁, k₂, k₃, k₄} : Finset ℕ).card = 4 := by
      rw [Finset.card_insert_of_notMem (by simp [h12, h13, h14]),
          Finset.card_insert_of_notMem (by simp [h23, h24]),
          Finset.card_insert_of_notMem (by simp [h34]), Finset.card_singleton]
    have := Finset.card_le_card hsub
    have := hdrop_le_true a
    omega
  have hcg0 := hcl.1 0 hpos
  rcases hcg0.2.2.1.1 with hop0 | hop0 | hop0
  · obtain ⟨a, b, hgi0, ha6, hb6, hab⟩ := hcg0.1 (Or.inl hop0)
    have ha5 : a < 5 := hvar_lt5 a (by simp [hgi0])
    have hb5 : b < 5 := hvar_lt5 b (by simp [hgi0])
    let af : Fin 5 := ⟨a, ha5⟩
    let bf : Fin 5 := ⟨b, hb5⟩
    let av : Fin 6 := ⟨a, by omega⟩
    let bv : Fin 6 := ⟨b, by omega⟩
    set initF := initVar 6 av false with hinitF
    have hinitF_len : initF.length = 6 := by simp [hinitF, initVar]
    have hinitF_a : (elimPass 6 gs (initF, [])).1.getD a (Sum.inl false) = Sum.inl false :=
      elimPass_initVar_self gs av false
    have hg0_const : (elimPass 6 gs (initF, [])).1.getD 6 (Sum.inl false) = Sum.inl false :=
      elim_gate_and_false hinitF_len hpos hop0 (by simp [hgi0]) (by simp [hgi0]) ha6 hinitF_a
    have hdrop0 : isDropped gs initF 0 = true :=
      isDropped_of_const_in hinitF_len hnok_gs hpos (by simp [hgi0]) ha6 hinitF_a
    have hout_ne6 : out ≠ 6 := by
      intro heq; obtain ⟨o, ho, _, _⟩ := elimPass_gives_circuit hcl av false (fC5_nc_false af)
      rw [heq, ← hinitF, hg0_const] at ho; simp at ho
    obtain ⟨j, hj, h6j⟩ := hcl.2.2.2.1 0 hpos hout_ne6.symm
    have hj_pos : 0 < j := by
      by_contra h0; have hj0 : j = 0 := by omega
      subst hj0; have := clean_inputs_lt hcl 0 hpos 6 h6j; omega
    have hdropj : isDropped gs initF j = true :=
      isDropped_of_const_in hinitF_len hnok_gs hj h6j (by omega) hg0_const
    by_cases ha_later : ∃ k, ∃ hk : k < gs.length, 0 < k ∧ a ∈ gs[k].inputs
    · obtain ⟨k, hk, hk_pos, hak⟩ := ha_later
      have hdropk : isDropped gs initF k = true :=
        isDropped_of_const_in hinitF_len hnok_gs hk hak (by omega) hinitF_a
      by_cases hkj : k = j
      · subst hkj
        obtain ⟨c, hc⟩ := elim_gate_both_const hinitF_len hk (hcl.1 k hk) hak h6j (by omega) (by omega) (by omega) hinitF_a hg0_const
        have hout_nek : out ≠ 6 + k := by
          intro heq; obtain ⟨o, ho, _, _⟩ := elimPass_gives_circuit hcl av false (fC5_nc_false af)
          rw [heq, ← hinitF, hc] at ho; simp at ho
        obtain ⟨m, hm, hkm⟩ := hcl.2.2.2.1 k hk hout_nek.symm
        have hm_gt : k < m := by by_contra hle_m; have := clean_inputs_lt hcl m hm (6 + k) hkm; omega
        have hdropm : isDropped gs initF m = true :=
          isDropped_of_const_in hinitF_len hnok_gs hm hkm (by omega) hc
        exact hcontra3F af 0 k m hpos hk hm (by omega) (by omega) (by omega) hdrop0 hdropk hdropm
      · exact hcontra3F af 0 j k hpos hj hk (by omega) (by omega) (Ne.symm hkj) hdrop0 hdropj hdropk
    · obtain ⟨x, hx⟩ := fC5_dep_pair_false af bf (fun h => hab (congrArg Fin.val h))
      set x0 := Function.update (Function.update x bv false) av false
      set x1 := Function.update (Function.update x bv false) av true
      have hsp : gs = gs[0] :: gs.drop 1 := by
        conv_lhs => rw [← List.drop_zero (l := gs)]
        exact List.drop_eq_getElem_cons hpos
      have hg0_eq : gs[0].op.eval (gs[0].inputs.map fun i => (List.ofFn x0).getD i false) =
          gs[0].op.eval (gs[0].inputs.map fun i => (List.ofFn x1).getD i false) := by
        have hop0' : gs[0].op = GateOp.and := hop0
        rw [hop0', hgi0]
        simp only [List.map_cons, List.map_nil, ofFn_getD_lt _ _ _ ha6, ofFn_getD_lt _ _ _ hb6,
          GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true]
        have hxb0 : x0 bv = false := by
          simp [x0, Function.update_of_ne (show bv ≠ av from fun h => hab (congrArg Fin.val h).symm)]
        have hxb1 : x1 bv = false := by
          simp [x1, Function.update_of_ne (show bv ≠ av from fun h => hab (congrArg Fin.val h).symm)]
        change (x0 av && x0 bv) = (x1 av && x1 bv)
        rw [hxb0, hxb1]; simp
      have hag := wiresFrom_agree (gs.drop 1) {a}
        (List.ofFn x0 ++ [gs[0].op.eval (gs[0].inputs.map fun i => (List.ofFn x0).getD i false)])
        (List.ofFn x1 ++ [gs[0].op.eval (gs[0].inputs.map fun i => (List.ofFn x1).getD i false)])
        (by simp) (by intro u hu; simp at hu; subst hu; simp; omega)
        (by
          intro i hi; simp at hi
          by_cases hi6 : i < 6
          · rw [getD_snoc_lt _ _ _ _ (by simp; exact hi6), getD_snoc_lt _ _ _ _ (by simp; exact hi6),
                ofFn_getD_lt _ _ _ hi6, ofFn_getD_lt _ _ _ hi6]
            have hne : (⟨i, hi6⟩ : Fin 6) ≠ av := fun h => hi (congrArg Fin.val h)
            simp [x0, x1, Function.update_of_ne hne]
          · by_cases heq6 : i = 6
            · subst heq6
              rw [getD_snoc_eq _ _ _ _ (by simp), getD_snoc_eq _ _ _ _ (by simp), hg0_eq]
            · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)])
        (by
          intro g hg i hi hmem; simp at hmem; subst hmem
          obtain ⟨d, hd, rfl⟩ := List.mem_iff_getElem.1 hg
          have hidx : 1 + d < gs.length := by simp at hd; omega
          have hget : (gs.drop 1)[d] = gs[1 + d] := List.getElem_drop
          rw [hget] at hi
          exact ha_later ⟨1 + d, hidx, by omega, hi⟩)
      have hEq := hag.2 out (by simp; omega)
      have hev0 := hcl.2.2.1 x0
      have hev1 := hcl.2.2.1 x1
      rw [hsp, wiresFrom_cons] at hev0 hev1
      exact hx (hev0.symm.trans (hEq.trans hev1))
  · obtain ⟨a, b, hgi0, ha6, hb6, hab⟩ := hcg0.1 (Or.inr hop0)
    have ha5 : a < 5 := hvar_lt5 a (by simp [hgi0])
    have hb5 : b < 5 := hvar_lt5 b (by simp [hgi0])
    let af : Fin 5 := ⟨a, ha5⟩
    let bf : Fin 5 := ⟨b, hb5⟩
    let av : Fin 6 := ⟨a, by omega⟩
    let bv : Fin 6 := ⟨b, by omega⟩
    have ha_later : ∃ k, ∃ hk : k < gs.length, 0 < k ∧ a ∈ gs[k].inputs := by
      by_contra hno
      obtain ⟨x, hx⟩ := fC5_dep_pair_true af bf (fun h => hab (congrArg Fin.val h))
      set x0 := Function.update (Function.update x bv true) av false
      set x1 := Function.update (Function.update x bv true) av true
      have hsp : gs = gs[0] :: gs.drop 1 := by
        conv_lhs => rw [← List.drop_zero (l := gs)]
        exact List.drop_eq_getElem_cons hpos
      have hg0_eq : gs[0].op.eval (gs[0].inputs.map fun i => (List.ofFn x0).getD i false) =
          gs[0].op.eval (gs[0].inputs.map fun i => (List.ofFn x1).getD i false) := by
        have hop0' : gs[0].op = GateOp.or := hop0
        rw [hop0', hgi0]
        simp only [List.map_cons, List.map_nil, ofFn_getD_lt _ _ _ ha6, ofFn_getD_lt _ _ _ hb6,
          GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
        have hxb0 : x0 bv = true := by
          simp [x0, Function.update_of_ne (show bv ≠ av from fun h => hab (congrArg Fin.val h).symm)]
        have hxb1 : x1 bv = true := by
          simp [x1, Function.update_of_ne (show bv ≠ av from fun h => hab (congrArg Fin.val h).symm)]
        change (x0 av || x0 bv) = (x1 av || x1 bv)
        rw [hxb0, hxb1]; simp
      have hag := wiresFrom_agree (gs.drop 1) {a}
        (List.ofFn x0 ++ [gs[0].op.eval (gs[0].inputs.map fun i => (List.ofFn x0).getD i false)])
        (List.ofFn x1 ++ [gs[0].op.eval (gs[0].inputs.map fun i => (List.ofFn x1).getD i false)])
        (by simp) (by intro u hu; simp at hu; subst hu; simp; omega)
        (by
          intro i hi; simp at hi
          by_cases hi6 : i < 6
          · rw [getD_snoc_lt _ _ _ _ (by simp; exact hi6), getD_snoc_lt _ _ _ _ (by simp; exact hi6),
                ofFn_getD_lt _ _ _ hi6, ofFn_getD_lt _ _ _ hi6]
            have hne : (⟨i, hi6⟩ : Fin 6) ≠ av := fun h => hi (congrArg Fin.val h)
            simp [x0, x1, Function.update_of_ne hne]
          · by_cases heq6 : i = 6
            · subst heq6
              rw [getD_snoc_eq _ _ _ _ (by simp), getD_snoc_eq _ _ _ _ (by simp), hg0_eq]
            · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)])
        (by
          intro g hg i hi hmem; simp at hmem; subst hmem
          obtain ⟨d, hd, rfl⟩ := List.mem_iff_getElem.1 hg
          have hidx : 1 + d < gs.length := by simp at hd; omega
          have hget : (gs.drop 1)[d] = gs[1 + d] := List.getElem_drop
          rw [hget] at hi
          exact hno ⟨1 + d, hidx, by omega, hi⟩)
      have hEq := hag.2 out (by simp; omega)
      have hev0 := hcl.2.2.1 x0
      have hev1 := hcl.2.2.1 x1
      rw [hsp, wiresFrom_cons] at hev0 hev1
      exact hx (hev0.symm.trans (hEq.trans hev1))
    obtain ⟨j, hj, hj_pos, haj⟩ := ha_later
    set initF := initVar 6 av false with hinitF
    have hinitF_len : initF.length = 6 := by simp [hinitF, initVar]
    have hinitF_a : (elimPass 6 gs (initF, [])).1.getD a (Sum.inl false) = Sum.inl false :=
      elimPass_initVar_self gs av false
    have hdrop0F : isDropped gs initF 0 = true :=
      isDropped_of_const_in hinitF_len hnok_gs hpos (by simp [hgi0]) ha6 hinitF_a
    have hdropjF : isDropped gs initF j = true :=
      isDropped_of_const_in hinitF_len hnok_gs hj haj (by omega) hinitF_a
    have hj_or : gs[j].op = GateOp.or := by
      have hcgj := hcl.1 j hj
      rcases hcgj.2.2.1.1 with hopj | hopj | hopj
      · exfalso
        have hj_const : (elimPass 6 gs (initF, [])).1.getD (6 + j) (Sum.inl false) = Sum.inl false :=
          elim_gate_and_false hinitF_len hj hopj hcgj.2.2.1.2 haj (by omega) hinitF_a
        have hout_nej : out ≠ 6 + j := by
          intro heq; obtain ⟨o, ho, _, _⟩ := elimPass_gives_circuit hcl av false (fC5_nc_false af)
          rw [heq, ← hinitF, hj_const] at ho; simp at ho
        obtain ⟨m, hm, hjm⟩ := hcl.2.2.2.1 j hj hout_nej.symm
        have hm_gt : j < m := by by_contra hle_m; have := clean_inputs_lt hcl m hm (6 + j) hjm; omega
        have hdropm : isDropped gs initF m = true :=
          isDropped_of_const_in hinitF_len hnok_gs hm hjm (by omega) hj_const
        exact hcontra3F af 0 j m hpos hj hm (by omega) (by omega) (by omega) hdrop0F hdropjF hdropm
      · exact hopj
      · exfalso
        obtain ⟨u, hgj, _⟩ := hcgj.2.1 hopj
        have hua : u = a := by rw [hgj] at haj; simp at haj; exact haj.symm
        subst hua
        have hj_const : (elimPass 6 gs (initF, [])).1.getD (6 + j) (Sum.inl false) = Sum.inl true :=
          elim_gate_not_const hinitF_len hj hopj hgj (by omega) hinitF_a
        have hout_nej : out ≠ 6 + j := by
          intro heq; obtain ⟨o, ho, _, _⟩ := elimPass_gives_circuit hcl av false (fC5_nc_false af)
          rw [heq, ← hinitF, hj_const] at ho; simp at ho
        obtain ⟨m, hm, hjm⟩ := hcl.2.2.2.1 j hj hout_nej.symm
        have hm_gt : j < m := by by_contra hle_m; have := clean_inputs_lt hcl m hm (6 + j) hjm; omega
        have hdropm : isDropped gs initF m = true :=
          isDropped_of_const_in hinitF_len hnok_gs hm hjm (by omega) hj_const
        exact hcontra3F af 0 j m hpos hj hm (by omega) (by omega) (by omega) hdrop0F hdropjF hdropm
    have h6_not_in_j : 6 ∉ gs[j].inputs := by
      intro h6j
      have hcgj := hcl.1 j hj
      obtain ⟨u, w, hgj, _, _, _⟩ := hcgj.1 (Or.inr hj_or)
      have hset : (u = a ∧ w = 6) ∨ (u = 6 ∧ w = a) := by
        rw [hgj] at haj h6j; simp at haj h6j
        rcases haj with rfl | rfl <;> rcases h6j with h | h <;> first | exact Or.inl ⟨rfl, h.symm⟩ | exact Or.inr ⟨h.symm, rfl⟩ | omega
      apply clean_no_equiv_wire hcl hnc hj (by omega : 6 < 6 + j)
      intro x
      rw [wiresFrom_getD_eq j hj x (clean_inputs_lt hcl j hj), hj_or, hgj]
      have h6val : (wiresFrom gs (List.ofFn x)).getD 6 false = (x av || x bv) := by
        rw [wiresFrom_getD_eq 0 hpos x (clean_inputs_lt hcl 0 hpos)]
        have hop0' : gs[0].op = GateOp.or := hop0
        rw [hop0', hgi0]
        simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
        rw [wiresFrom_getD_lt _ _ _ (by simp; exact ha6), wiresFrom_getD_lt _ _ _ (by simp; exact hb6),
            ofFn_getD_lt _ _ _ ha6, ofFn_getD_lt _ _ _ hb6]
      have haval : (wiresFrom gs (List.ofFn x)).getD a false = x av := by
        rw [wiresFrom_getD_lt _ _ _ (by simp; omega), ofFn_getD_lt _ _ _ ha6]
      rcases hset with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq,
          Bool.or_false, haval, h6val]
        cases x av <;> cases x bv <;> rfl
      · simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq,
          Bool.or_false, haval, h6val]
        cases x av <;> cases x bv <;> rfl
    set initT := initVar 6 av true with hinitT
    have hinitT_len : initT.length = 6 := by simp [hinitT, initVar]
    have hinitT_a : (elimPass 6 gs (initT, [])).1.getD a (Sum.inl false) = Sum.inl true :=
      elimPass_initVar_self gs av true
    have hg0_T : (elimPass 6 gs (initT, [])).1.getD 6 (Sum.inl false) = Sum.inl true :=
      elim_gate_or_true hinitT_len hpos hop0 (by simp [hgi0]) (by simp [hgi0]) ha6 hinitT_a
    have hgj_T : (elimPass 6 gs (initT, [])).1.getD (6 + j) (Sum.inl false) = Sum.inl true :=
      elim_gate_or_true hinitT_len hj hj_or (hcl.1 j hj).2.2.1.2 haj (by omega) hinitT_a
    have hdrop0T : isDropped gs initT 0 = true :=
      isDropped_of_const_in hinitT_len hnok_gs hpos (by simp [hgi0]) ha6 hinitT_a
    have hdropjT : isDropped gs initT j = true :=
      isDropped_of_const_in hinitT_len hnok_gs hj haj (by omega) hinitT_a
    have hout_ne6T : out ≠ 6 := by
      intro heq; obtain ⟨o, ho, _, _⟩ := elimPass_gives_circuit hcl av true (fC5_nc_true af)
      rw [heq, ← hinitT, hg0_T] at ho; simp at ho
    have hout_nejT : out ≠ 6 + j := by
      intro heq; obtain ⟨o, ho, _, _⟩ := elimPass_gives_circuit hcl av true (fC5_nc_true af)
      rw [heq, ← hinitT, hgj_T] at ho; simp at ho
    obtain ⟨h₁, hh₁, h6h₁⟩ := hcl.2.2.2.1 0 hpos hout_ne6T.symm
    obtain ⟨h₂, hh₂, hjh₂⟩ := hcl.2.2.2.1 j hj hout_nejT.symm
    have hh₁_pos : 0 < h₁ := by by_contra h0; have := clean_inputs_lt hcl h₁ hh₁ 6 h6h₁; omega
    have hh₁_nej : h₁ ≠ j := by intro heq; subst heq; exact h6_not_in_j h6h₁
    have hh₂_gtj : j < h₂ := by by_contra hle_h; have := clean_inputs_lt hcl h₂ hh₂ (6 + j) hjh₂; omega
    have hdroph1 : isDropped gs initT h₁ = true :=
      isDropped_of_const_in hinitT_len hnok_gs hh₁ h6h₁ (by omega) hg0_T
    have hdroph2 : isDropped gs initT h₂ = true :=
      isDropped_of_const_in hinitT_len hnok_gs hh₂ hjh₂ (by omega) hgj_T
    by_cases hh12 : h₁ = h₂
    · subst hh12
      obtain ⟨c, hc⟩ := elim_gate_both_const hinitT_len hh₁ (hcl.1 h₁ hh₁) h6h₁ hjh₂ (by omega) (by omega) (by omega) hg0_T hgj_T
      have hout_neh1 : out ≠ 6 + h₁ := by
        intro heq; obtain ⟨o, ho, _, _⟩ := elimPass_gives_circuit hcl av true (fC5_nc_true af)
        rw [heq, ← hinitT, hc] at ho; simp at ho
      obtain ⟨m, hm, hh1m⟩ := hcl.2.2.2.1 h₁ hh₁ hout_neh1.symm
      have hm_gt : h₁ < m := by by_contra hle_m; have := clean_inputs_lt hcl m hm (6 + h₁) hh1m; omega
      have hdropm : isDropped gs initT m = true :=
        isDropped_of_const_in hinitT_len hnok_gs hm hh1m (by omega) hc
      exact hcontra4T af 0 j h₁ m hpos hj hh₁ hm (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hdrop0T hdropjT hdroph1 hdropm
    · exact hcontra4T af 0 j h₁ h₂ hpos hj hh₁ hh₂ (by omega) (by omega) (by omega) (Ne.symm hh₁_nej) (by omega) hh12 hdrop0T hdropjT hdroph1 hdroph2
  · obtain ⟨a, hgi0, ha6⟩ := hcg0.2.1 hop0
    have ha5 : a < 5 := hvar_lt5 a (by simp [hgi0])
    let af : Fin 5 := ⟨a, ha5⟩
    let av : Fin 6 := ⟨a, by omega⟩
    set initF := initVar 6 av false with hinitF
    have hinitF_len : initF.length = 6 := by simp [hinitF, initVar]
    have hinitF_a : (elimPass 6 gs (initF, [])).1.getD a (Sum.inl false) = Sum.inl false :=
      elimPass_initVar_self gs av false
    have hg0_F : (elimPass 6 gs (initF, [])).1.getD 6 (Sum.inl false) = Sum.inl true :=
      elim_gate_not_const hinitF_len hpos hop0 hgi0 ha6 hinitF_a
    have hdrop0F : isDropped gs initF 0 = true :=
      isDropped_of_const_in hinitF_len hnok_gs hpos (by simp [hgi0]) ha6 hinitF_a
    have hout_ne6F : out ≠ 6 := by
      intro heq; obtain ⟨o, ho, _, _⟩ := elimPass_gives_circuit hcl av false (fC5_nc_false af)
      rw [heq, ← hinitF, hg0_F] at ho; simp at ho
    obtain ⟨h₁, hh₁, h6h₁⟩ := hcl.2.2.2.1 0 hpos hout_ne6F.symm
    have hh₁_pos : 0 < h₁ := by by_contra h0; have := clean_inputs_lt hcl h₁ hh₁ 6 h6h₁; omega
    have hdroph1F : isDropped gs initF h₁ = true :=
      isDropped_of_const_in hinitF_len hnok_gs hh₁ h6h₁ (by omega) hg0_F
    have ha_only0 : ∀ k, (hk : k < gs.length) → 0 < k → a ∉ gs[k].inputs := by
      intro k hk hk_pos hak
      have hdropkF : isDropped gs initF k = true :=
        isDropped_of_const_in hinitF_len hnok_gs hk hak (by omega) hinitF_a
      by_cases hkh : k = h₁
      · subst hkh
        obtain ⟨c, hc⟩ := elim_gate_both_const hinitF_len hk (hcl.1 k hk) hak h6h₁ (by omega) (by omega) (by omega) hinitF_a hg0_F
        have hout_nek : out ≠ 6 + k := by
          intro heq; obtain ⟨o, ho, _, _⟩ := elimPass_gives_circuit hcl av false (fC5_nc_false af)
          rw [heq, ← hinitF, hc] at ho; simp at ho
        obtain ⟨m, hm, hkm⟩ := hcl.2.2.2.1 k hk hout_nek.symm
        have hm_gt : k < m := by by_contra hle_m; have := clean_inputs_lt hcl m hm (6 + k) hkm; omega
        have hdropm : isDropped gs initF m = true :=
          isDropped_of_const_in hinitF_len hnok_gs hm hkm (by omega) hc
        exact hcontra3F af 0 k m hpos hk hm (by omega) (by omega) (by omega) hdrop0F hdropkF hdropm
      · exact hcontra3F af 0 h₁ k hpos hh₁ hk (by omega) (by omega) (Ne.symm hkh) hdrop0F hdroph1F hdropkF
    have hh₁_and : gs[h₁].op = GateOp.and := by
      have hcgh := hcl.1 h₁ hh₁
      rcases hcgh.2.2.1.1 with hoph | hoph | hoph
      · exact hoph
      · exfalso
        have hh1_const : (elimPass 6 gs (initF, [])).1.getD (6 + h₁) (Sum.inl false) = Sum.inl true :=
          elim_gate_or_true hinitF_len hh₁ hoph hcgh.2.2.1.2 h6h₁ (by omega) hg0_F
        have hout_neh : out ≠ 6 + h₁ := by
          intro heq; obtain ⟨o, ho, _, _⟩ := elimPass_gives_circuit hcl av false (fC5_nc_false af)
          rw [heq, ← hinitF, hh1_const] at ho; simp at ho
        obtain ⟨m, hm, hh1m⟩ := hcl.2.2.2.1 h₁ hh₁ hout_neh.symm
        have hm_gt : h₁ < m := by by_contra hle_m; have := clean_inputs_lt hcl m hm (6 + h₁) hh1m; omega
        have hdropm : isDropped gs initF m = true :=
          isDropped_of_const_in hinitF_len hnok_gs hm hh1m (by omega) hh1_const
        exact hcontra3F af 0 h₁ m hpos hh₁ hm (by omega) (by omega) (by omega) hdrop0F hdroph1F hdropm
      · exfalso
        obtain ⟨u, hgh, _⟩ := hcgh.2.1 hoph
        have hu8 : u = 6 := by rw [hgh] at h6h₁; simp at h6h₁; exact h6h₁.symm
        subst hu8
        have hh1_const : (elimPass 6 gs (initF, [])).1.getD (6 + h₁) (Sum.inl false) = Sum.inl false :=
          elim_gate_not_const hinitF_len hh₁ hoph hgh (by omega) hg0_F
        have hout_neh : out ≠ 6 + h₁ := by
          intro heq; obtain ⟨o, ho, _, _⟩ := elimPass_gives_circuit hcl av false (fC5_nc_false af)
          rw [heq, ← hinitF, hh1_const] at ho; simp at ho
        obtain ⟨m, hm, hh1m⟩ := hcl.2.2.2.1 h₁ hh₁ hout_neh.symm
        have hm_gt : h₁ < m := by by_contra hle_m; have := clean_inputs_lt hcl m hm (6 + h₁) hh1m; omega
        have hdropm : isDropped gs initF m = true :=
          isDropped_of_const_in hinitF_len hnok_gs hm hh1m (by omega) hh1_const
        exact hcontra3F af 0 h₁ m hpos hh₁ hm (by omega) (by omega) (by omega) hdrop0F hdroph1F hdropm
    set initT := initVar 6 av true with hinitT
    have hinitT_len : initT.length = 6 := by simp [hinitT, initVar]
    have hinitT_a : (elimPass 6 gs (initT, [])).1.getD a (Sum.inl false) = Sum.inl true :=
      elimPass_initVar_self gs av true
    have hg0_T : (elimPass 6 gs (initT, [])).1.getD 6 (Sum.inl false) = Sum.inl false :=
      elim_gate_not_const hinitT_len hpos hop0 hgi0 ha6 hinitT_a
    have hh1_T : (elimPass 6 gs (initT, [])).1.getD (6 + h₁) (Sum.inl false) = Sum.inl false :=
      elim_gate_and_false hinitT_len hh₁ hh₁_and (hcl.1 h₁ hh₁).2.2.1.2 h6h₁ (by omega) hg0_T
    have hdrop0T : isDropped gs initT 0 = true :=
      isDropped_of_const_in hinitT_len hnok_gs hpos (by simp [hgi0]) ha6 hinitT_a
    have hdroph1T : isDropped gs initT h₁ = true :=
      isDropped_of_const_in hinitT_len hnok_gs hh₁ h6h₁ (by omega) hg0_T
    have hout_nehT : out ≠ 6 + h₁ := by
      intro heq; obtain ⟨o, ho, _, _⟩ := elimPass_gives_circuit hcl av true (fC5_nc_true af)
      rw [heq, ← hinitT, hh1_T] at ho; simp at ho
    obtain ⟨m, hm, hh1m⟩ := hcl.2.2.2.1 h₁ hh₁ hout_nehT.symm
    have hm_gt : h₁ < m := by by_contra hle_m; have := clean_inputs_lt hcl m hm (6 + h₁) hh1m; omega
    have hdropmT : isDropped gs initT m = true :=
      isDropped_of_const_in hinitT_len hnok_gs hm hh1m (by omega) hh1_T
    have hsub3 : ({0, h₁, m} : Finset ℕ) ⊆
        (Finset.range gs.length).filter (fun i => isDropped gs initT i = true) := by
      intro i hi; simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl | rfl
      · exact Finset.mem_filter.2 ⟨Finset.mem_range.2 hpos, hdrop0T⟩
      · exact Finset.mem_filter.2 ⟨Finset.mem_range.2 hh₁, hdroph1T⟩
      · exact Finset.mem_filter.2 ⟨Finset.mem_range.2 hm, hdropmT⟩
    have h3_card : ({0, h₁, m} : Finset ℕ).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp; omega),
          Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
    have hle3 := hdrop_le_true af
    have h3_le := Finset.card_le_card hsub3
    have hle3' : ((Finset.range gs.length).filter (fun i => isDropped gs initT i = true)).card ≤ 3 := hle3
    have hcard_eq : ((Finset.range gs.length).filter (fun i => isDropped gs initT i = true)).card = 3 := by omega
    have hset_eq : (Finset.range gs.length).filter (fun i => isDropped gs initT i = true) = {0, h₁, m} :=
      (Finset.eq_of_subset_of_card_le hsub3 (by omega)).symm
    have hm_or : gs[m].op = GateOp.or := by
      have hcgm := hcl.1 m hm
      rcases hcgm.2.2.1.1 with hopm | hopm | hopm
      · exfalso
        have hm_const : (elimPass 6 gs (initT, [])).1.getD (6 + m) (Sum.inl false) = Sum.inl false :=
          elim_gate_and_false hinitT_len hm hopm hcgm.2.2.1.2 hh1m (by omega) hh1_T
        have hout_nem : out ≠ 6 + m := by
          intro heq; obtain ⟨o, ho, _, _⟩ := elimPass_gives_circuit hcl av true (fC5_nc_true af)
          rw [heq, ← hinitT, hm_const] at ho; simp at ho
        obtain ⟨r, hr, hmr⟩ := hcl.2.2.2.1 m hm hout_nem.symm
        have hr_gt : m < r := by by_contra hle_r; have := clean_inputs_lt hcl r hr (6 + m) hmr; omega
        have hdropr : isDropped gs initT r = true :=
          isDropped_of_const_in hinitT_len hnok_gs hr hmr (by omega) hm_const
        exact hcontra4T af 0 h₁ m r hpos hh₁ hm hr (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hdrop0T hdroph1T hdropmT hdropr
      · exact hopm
      · exfalso
        obtain ⟨u, hgm, _⟩ := hcgm.2.1 hopm
        have huh : u = 6 + h₁ := by rw [hgm] at hh1m; simp at hh1m; exact hh1m.symm
        subst huh
        have hm_const : (elimPass 6 gs (initT, [])).1.getD (6 + m) (Sum.inl false) = Sum.inl true :=
          elim_gate_not_const hinitT_len hm hopm hgm (by omega) hh1_T
        have hout_nem : out ≠ 6 + m := by
          intro heq; obtain ⟨o, ho, _, _⟩ := elimPass_gives_circuit hcl av true (fC5_nc_true af)
          rw [heq, ← hinitT, hm_const] at ho; simp at ho
        obtain ⟨r, hr, hmr⟩ := hcl.2.2.2.1 m hm hout_nem.symm
        have hr_gt : m < r := by by_contra hle_r; have := clean_inputs_lt hcl r hr (6 + m) hmr; omega
        have hdropr : isDropped gs initT r = true :=
          isDropped_of_const_in hinitT_len hnok_gs hr hmr (by omega) hm_const
        exact hcontra4T af 0 h₁ m r hpos hh₁ hm hr (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hdrop0T hdroph1T hdropmT hdropr
    obtain ⟨o, _, hokT, hevT⟩ := elimPass_gives_circuit hcl av true (fC5_nc_true af)
    set C' : Circuit := ⟨(elimPass 6 gs (initT, [])).2, o⟩
    have hC'_sz : C'.size = 3 := by
      have htot := (elimPass_dropped_card gs initT).1
      have h3 := size_C5_restrict_true af C'.size ⟨C', hokT, le_refl _, hevT⟩
      have hlen_c' : C'.size = (elimPass 6 gs (initT, [])).2.length := rfl
      omega
    have hC'_min : IsMin (Restrict fC5 av true) C' := by
      refine ⟨hokT, hevT, fun C'' hok'' hev'' => ?_⟩
      have h3 := size_C5_restrict_true af C''.size ⟨C'', hok'', le_refl _, hev''⟩
      omega
    have hcl' := clean_of_min hC'_min (fC5_nc_true af)
    let S' : Finset (Fin 6) := ({0, 1, 2, 3, 4} : Finset (Fin 6)).erase av
    have hS'_card : S'.card = 4 := fC5_S'_card af
    have hS'_dep : ∀ w ∈ S', DependsOn (Restrict fC5 av true) w := fC5_S'_dep af
    obtain ⟨v₁, hv₁, v₂, hv₂, hvne⟩ := Finset.one_lt_card.1 (by omega : 1 < S'.card)
    have hout' := clean_out_ge6 hcl' hvne (hS'_dep v₁ hv₁) (hS'_dep v₂ hv₂)
    have hslot' := (clean_slot_count hcl' hout' S' hS'_dep).1
    have hlen' : (C'.gates.map normGate).length = 3 := by rw [List.length_map]; exact hC'_sz
    have hno_not' : ∀ g' ∈ C'.gates, g'.op ≠ GateOp.not := by
      intro g' hg' hnot
      have hmem : normGate g' ∈ (C'.gates.map normGate).filter (fun g => isNotOp g.op) := by
        refine List.mem_filter.2 ⟨List.mem_map.2 ⟨g', hg', rfl⟩, ?_⟩
        simp [normGate, hnot, isNotOp]
      have hpos' := List.length_pos_of_mem hmem
      omega
    have hrest_mono : ∀ g ∈ gs.tail, a ∉ g.inputs ∧ (g.op = GateOp.and ∨ g.op = GateOp.or) := by
      intro g hg
      obtain ⟨d, hd, rfl⟩ := List.mem_iff_getElem.1 hg
      have hd1 : d + 1 < gs.length := by simp at hd; omega
      have hgt : gs.tail[d] = gs[d + 1] := by simp
      rw [hgt]
      refine ⟨ha_only0 (d + 1) hd1 (by omega), ?_⟩
      by_cases h1 : d + 1 = h₁
      · have hge : gs[d + 1] = gs[h₁] := by congr 1
        rw [hge]; exact Or.inl hh₁_and
      · by_cases h2 : d + 1 = m
        · have hge : gs[d + 1] = gs[m] := by congr 1
          rw [hge]; exact Or.inr hm_or
        · have hnotdrop : isDropped gs initT (d + 1) = false := by
            cases hdt : isDropped gs initT (d + 1) with
            | false => rfl
            | true =>
              exfalso
              have hmem : d + 1 ∈ ({0, h₁, m} : Finset ℕ) := by
                rw [← hset_eq]; exact Finset.mem_filter.2 ⟨Finset.mem_range.2 hd1, hdt⟩
              simp at hmem; omega
          obtain ⟨g', hg', hop'⟩ := (elimPass_dropped_card gs initT).2 (d + 1) hd1 hnotdrop
          have hnn : gs[d + 1].op ≠ GateOp.not := by
            rw [← hop']; exact hno_not' g' hg'
          rcases (hcl.1 (d + 1) hd1).2.2.1.1 with h | h | h
          · exact Or.inl h
          · exact Or.inr h
          · exact absurd h hnn
    have hanti : ∀ x : Fin 6 → Bool,
        fC5 (Function.update x av true) = true → fC5 (Function.update x av false) = true := by
      intro x ht
      have hne0 : gs ≠ [] := List.ne_nil_of_length_pos hpos
      have hhead : gs.head hne0 = ⟨GateOp.not, [a]⟩ := by
        rw [List.head_eq_getElem_zero]
        have hop0' : gs[0].op = GateOp.not := hop0
        cases h0eq : gs[0] with
        | mk op ins =>
          simp only [h0eq] at hop0' hgi0
          rw [hop0', hgi0]
      have h1 := antitone_of_only_first_not (by omega : out ≠ (av : ℕ)) hne0 hhead hrest_mono x
      rw [hcl.2.2.1, hcl.2.2.1] at h1
      exact h1 ht
    obtain ⟨x, hx1, hx0⟩ := fC5_anti_witness af
    have := hanti x hx1
    rw [hx0] at this; simp at this



private lemma size_C5L_ge (s : ℕ) (h : HasCircuitSize 6 fC5L s) : 8 ≤ s := by
  have hres : Restrict fC5L 5 false = fC5 := by
    funext x; simp [Restrict, fC5L, fC5, Function.update]
  have h1 := elim_one_var 5 false h (dep_of_mask 5 1 (by decide))
    (by rw [hres]; exact nonConst_of_masks 0 3 (by decide))
  rw [hres] at h1
  have := size_C5_ge (s - 1) h1.2
  omega

end PEqualNP.Outside.L_meta_527_aux

theorem PEqualNP.Outside.L_meta_527 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6
      (fun x : Fin 6 → Bool =>
        (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 0 && x 4) || (x 0 && x 5))
      s → 8 ≤ s :=
  PEqualNP.Outside.L_meta_527_aux.size_C5L_ge
