import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_14102.CircuitHelpers

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def gvBool (w : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

def execBool (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [gvBool w g]) w

def agreeExcept (p : ℕ) (w w' : List Bool) : Prop :=
  w.length = w'.length ∧ ∀ i ≠ p, w.getD i false = w'.getD i false

theorem agreeExcept_append_same {p : ℕ} {w w' : List Bool} (h : agreeExcept p w w') (b : Bool) :
    agreeExcept p (w ++ [b]) (w' ++ [b]) := by
  refine ⟨by simpa using h.1, ?_⟩
  intro i hi
  simp only [List.getD_eq_getElem?_getD]
  by_cases hit : i < w.length
  · rw [List.getElem?_append_left hit, List.getElem?_append_left (h.1 ▸ hit)]
    exact h.2 i hi
  · have hw := Nat.le_of_not_gt hit
    rw [List.getElem?_append_right hw, List.getElem?_append_right (h.1 ▸ hw), h.1]

theorem agreeExcept_append_here (w : List Bool) (b b' : Bool) :
    agreeExcept w.length (w ++ [b]) (w ++ [b']) := by
  refine ⟨by simp, ?_⟩
  intro i hi
  simp only [List.getD_eq_getElem?_getD]
  by_cases hit : i < w.length
  · rw [List.getElem?_append_left hit, List.getElem?_append_left hit]
  · have out : w.length + 1 ≤ i := by omega
    have out' : (w ++ [b]).length ≤ i := by simpa using out
    have out'' : (w ++ [b']).length ≤ i := by simpa using out
    rw [List.getElem?_eq_none out', List.getElem?_eq_none out'']

theorem agreeExcept_exec {p : ℕ} {gs : List Gate} (hn : ∀ g ∈ gs, p ∉ g.inputs)
    {w w' : List Bool} (ha : agreeExcept p w w') :
    agreeExcept p (execBool gs w) (execBool gs w') := by
  induction gs generalizing w w' with
  | nil => exact ha
  | cons g gs ih =>
    have hg : gvBool w g = gvBool w' g := by
      unfold gvBool
      congr 1
      apply List.map_congr_left
      intro i hi
      exact ha.2 i (by rintro rfl; exact hn g (by simp) hi)
    simp only [execBool, List.foldl_cons]
    rw [← hg]
    exact ih (fun j hj => hn j (List.mem_cons_of_mem _ hj)) (agreeExcept_append_same ha _)

theorem execBool_length (gs : List Gate) (w : List Bool) :
    (execBool gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [execBool]
  | cons g gs ih =>
    change (execBool gs (w ++ [gvBool w g])).length = _
    rw [ih]
    simp
    omega

theorem execBool_append (pre post : List Gate) (xs : List Bool) :
    execBool (pre ++ post) xs = execBool post (execBool pre xs) := by
  simp only [execBool, List.foldl_append]

theorem execBool_cons (g : Gate) (gs : List Gate) (xs : List Bool) :
    execBool (g :: gs) xs = execBool gs (xs ++ [gvBool xs g]) :=
  rfl

end PEqualNP.Outside.L_meta_14102.CircuitHelpers

namespace PEqualNP.Outside.L_meta_14102.Restriction

namespace CircuitProof

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_initial_segment (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_initial_segment gs w
  rw [ht]; simp [hl]

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

end CircuitProof

namespace CircuitProof

open PEqualNP.CircuitLowerBounds

variable {n : ℕ}

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

end CircuitProof

namespace CircuitProof

open PEqualNP.CircuitLowerBounds

def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

abbrev Stat := Sum Bool ℕ

def Stat.val (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def Stat.Valid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] =>
    if j = k then (none, Sum.inr j) else (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] =>
    if j = k then (none, Sum.inr j) else (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

theorem simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, Stat.Valid w.length s) :
    Stat.Valid (w.length + (simplify op w.length ins).1.toList.length) (simplify op w.length ins).2 ∧
    Stat.val (wiresFrom (simplify op w.length ins).1.toList w) (simplify op w.length ins).2
      = op.eval (ins.map (Stat.val w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a with
      | inl a =>
        cases b with
        | inl b => cases a <;> cases b <;> simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval]
        | inr k => cases a <;> simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
      | inr j =>
        cases b with
        | inl b => cases b <;> simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
        | inr k =>
          by_cases e : j = k
          · subst k
            simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
          · simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a with
      | inl a =>
        cases b with
        | inl b => cases a <;> cases b <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval]
        | inr k => cases a <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
      | inr j =>
        cases b with
        | inl b => cases b <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
        | inr k =>
          by_cases e : j = k
          · subst k
            simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
          · simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

theorem toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

theorem elim_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    have h1 := ih (elimStep n acc g)
    have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      have := toList_length_le (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
      omega
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]; omega

theorem Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, Stat.Valid m s → Stat.Valid m' s
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

theorem Stat.val_append (w t : List Bool) : ∀ s : Stat, Stat.Valid w.length s →
    Stat.val (w ++ t) s = Stat.val w s
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    Stat.Valid (n + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
    Stat.val (wiresFrom acc.2 y) (acc.1.getD i (Sum.inl false)) = w.getD i false

theorem inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      Inv n y (wiresFrom gs w) (elim n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := h
    set w' := wiresFrom acc.2 y with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hy]
    set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (Stat.val w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, htl⟩ := wiresFrom_initial_segment r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show Stat.Valid (n + (acc.2 ++ r.1.toList).length) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) ∧
      Stat.val (wiresFrom (acc.2 ++ r.1.toList) y) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨Stat.valid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, Stat.val_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

def CleanGate (m : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.not ∧ ∃ j, j < m ∧ g.inputs = [j]) ∨
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ j k, j < m ∧ k < m ∧ g.inputs = [j, k])

def CleanL (m : ℕ) (gs : List Gate) : Prop :=
  ∀ (p : ℕ) (g : Gate), gs[p]? = some g → CleanGate (m + p) g

theorem CleanGate.nok {m : ℕ} {g : Gate} (h : CleanGate m g) : NOk g := by
  rcases h with ⟨h1, j, _, h2⟩ | ⟨h1 | h1, j, k, _, _, h2⟩
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inr (Or.inr rfl)
    · rw [h2]; simp
    · intro _; rw [h2]; simp
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inl rfl
    · rw [h2]; simp
    · intro h; rw [h1] at h; cases h
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inr (Or.inl rfl)
    · rw [h2]; simp
    · intro h; rw [h1] at h; cases h

theorem clean_nok (m : ℕ) (gs : List Gate) (h : CleanL m gs) : ∀ g ∈ gs, NOk g := by
  intro g hg
  obtain ⟨p, hp⟩ := List.mem_iff_getElem?.1 hg
  exact (h p g hp).nok

theorem simplify_clean (op : GateOp) (m : ℕ) (ins : List Stat) (hv : ∀ s ∈ ins, Stat.Valid m s) :
    ∀ g ∈ (simplify op m ins).1, CleanGate m g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    split at hg
    · simp at hg
    simp at hg
    subst hg
    refine Or.inr ⟨Or.inl rfl, _, _, ?_, ?_, rfl⟩
    · exact hv _ List.mem_cons_self
    · exact hv _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    split at hg
    · simp at hg
    simp at hg
    subst hg
    refine Or.inr ⟨Or.inr rfl, _, _, ?_, ?_, rfl⟩
    · exact hv _ List.mem_cons_self
    · exact hv _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;> simp [simpNot] at hg
    subst hg
    refine Or.inl ⟨rfl, _, ?_, rfl⟩
    exact hv _ List.mem_cons_self
  · simp at hg
  · simp at hg

theorem toList_getElem? {α : Type} (o : Option α) (k : ℕ) (a : α)
    (h : o.toList[k]? = some a) : k = 0 ∧ a ∈ o := by
  cases o with
  | none => simp at h
  | some b =>
    cases k with
    | zero => simp at h; simp [h]
    | succ k => simp at h

theorem clean_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      CleanL n acc.2 → CleanL n (elim n gs acc).2 := by
  induction gs with
  | nil => intro w acc _ _ h; exact h
  | cons g gs ih =>
    intro w acc hok hinv hcl
    have hinv' : Inv n y (wiresFrom [g] w) (elimStep n acc g) :=
      inv_elim n y hy [g] w acc (fun g' hg' => hok g' (by simp at hg'; simp [hg'])) hinv
    refine ih _ (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg')) hinv' ?_
    intro p g' hp
    have hp' : (acc.2 ++ (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)[p]? = some g' := hp
    by_cases hlt : p < acc.2.length
    · rw [List.getElem?_append_left hlt] at hp'
      exact hcl p g' hp'
    · rw [List.getElem?_append_right (by omega)] at hp'
      obtain ⟨h0, hmem⟩ := toList_getElem? _ _ _ hp'
      have hpl : p = acc.2.length := by omega
      rw [hpl]
      exact simplify_clean _ _ _ (fun s hs => by
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        exact (hinv.2 a).1) g' hmem

open PEqualNP.MetaComplexity

abbrev Acc := List Stat × List Gate

theorem elim_append (n : ℕ) (gs hs : List Gate) (init : Acc) :
    elim n (gs ++ hs) init = elim n hs (elim n gs init) := by
  simp [elim, List.foldl_append]

def decision (n : ℕ) (acc : Acc) (g : Gate) : Option Gate × Stat :=
  simplify g.op (n + acc.2.length) (g.inputs.map fun i => acc.1.getD i (Sum.inl false))

theorem split_gate {gs : List Gate} {p : ℕ} {g : Gate} (hp : gs[p]? = some g) :
    ∃ pre post, gs = pre ++ g :: post ∧ pre.length = p := by
  induction gs generalizing p with
  | nil => simp at hp
  | cons h gs ih =>
    cases p with
    | zero =>
      simp at hp
      subst g
      exact ⟨[], gs, rfl, rfl⟩
    | succ p =>
      simp at hp
      obtain ⟨pre, post, rfl, rfl⟩ := ih hp
      exact ⟨h :: pre, post, rfl, rfl⟩

def zeroGate : Gate := ⟨.or, []⟩

end CircuitProof

end PEqualNP.Outside.L_meta_14102.Restriction

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_14102.BranchData

namespace CircuitProof

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_initial_segment (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_initial_segment gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_initial_segment gs w
  rw [ht, List.getD_append _ _ _ _ h]

end CircuitProof

namespace CircuitProof

open PEqualNP.CircuitLowerBounds

variable {n : ℕ}

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

end CircuitProof

namespace CircuitProof

open PEqualNP.CircuitLowerBounds

theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

def isNotGate (op : GateOp) : Bool :=
  match op with
  | .not => true
  | _ => false

end CircuitProof

namespace CircuitProof

open PEqualNP.CircuitLowerBounds

def CleanGate (m : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.not ∧ ∃ j, j < m ∧ g.inputs = [j]) ∨
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ j k, j < m ∧ k < m ∧ g.inputs = [j, k])

def CleanL (m : ℕ) (gs : List Gate) : Prop :=
  ∀ (p : ℕ) (g : Gate), gs[p]? = some g → CleanGate (m + p) g

theorem CleanGate.lt {m : ℕ} {g : Gate} (h : CleanGate m g) : ∀ a ∈ g.inputs, a < m := by
  intro a ha
  rcases h with ⟨_, j, hj, h2⟩ | ⟨_, j, k, hj, hk, h2⟩
  · rw [h2] at ha
    simp at ha
    subst ha; exact hj
  · rw [h2] at ha
    simp at ha
    rcases ha with rfl | rfl
    · exact hj
    · exact hk

theorem getD_ofFn {α : Type} (m : ℕ) (F : Fin m → α) (d : α) (j : Fin m) :
    (List.ofFn F).getD j d = F j := by
  simp

theorem split_at {α : Type} : ∀ (l : List α) (p : ℕ) (g : α), l[p]? = some g →
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

end CircuitProof

namespace CircuitProof

open PEqualNP.CircuitLowerBounds

def vl {k : ℕ} (gs : List Gate) (u : Fin k → Bool) (j : ℕ) : Bool :=
  (wiresFrom gs (List.ofFn u)).getD j false

theorem vl_input {k : ℕ} (gs : List Gate) (u : Fin k → Bool) (j : ℕ) (h : j < k) :
    vl gs u j = u ⟨j, h⟩ := by
  unfold vl
  rw [getD_wiresFrom gs _ j (by simpa using h)]
  exact getD_ofFn k u false ⟨j, h⟩

theorem vl_gate {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u : Fin k → Bool) (p : ℕ)
    (g : Gate) (hp : gs[p]? = some g) :
    vl gs u (k + p) = g.op.eval (g.inputs.map (vl gs u)) := by
  have hlt := (hcl p g hp).lt
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hp
  have hwl : (wiresFrom pre (List.ofFn u)).length = k + pre.length := by
    rw [length_wiresFrom]; simp
  have e : wiresFrom (pre ++ g :: post) (List.ofFn u)
      = wiresFrom post (wiresFrom pre (List.ofFn u) ++
        [g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn u)).getD i false)]) := by
    rw [wiresFrom_append]; rfl
  have full : ∀ j, j < k + pre.length →
      (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD j false
        = (wiresFrom pre (List.ofFn u)).getD j false := by
    intro j hj
    rw [e, getD_wiresFrom _ _ j (by simp [hwl]; omega), getD_snoc_ne _ _ _ _ (by omega)]
  have top : (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD (k + pre.length) false
      = g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn u)).getD i false) := by
    rw [e, getD_wiresFrom _ _ _ (by simp [hwl]), getD_snoc_len _ _ _ _ hwl]
  show (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD (k + pre.length) false
    = g.op.eval (g.inputs.map fun j => (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD j false)
  rw [top]
  congr 1
  apply List.map_congr_left
  intro a ha
  exact (full a (hlt a ha)).symm

theorem vl_congr {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u u' : Fin k → Bool) (p : ℕ)
    (g : Gate) (hp : gs[p]? = some g) (h : ∀ a ∈ g.inputs, vl gs u a = vl gs u' a) :
    vl gs u (k + p) = vl gs u' (k + p) := by
  rw [vl_gate gs hcl u p g hp, vl_gate gs hcl u' p g hp]
  congr 1
  exact List.map_congr_left h

end CircuitProof

namespace CutTrace

open PEqualNP.CircuitLowerBounds

open CircuitProof

def avoid {W : Type} (edge : W → W → Prop) (cut : W) (a b : W) : Prop :=
  edge a b ∧ a ≠ cut ∧ b ≠ cut

theorem difference_traces {W : Type} (rank : W → Nat) (input : W → Prop)
    (edge : W → W → Prop) (cut : W) (x y : W → Bool)
    (order : ∀ a b, edge a b → rank a < rank b)
    (localStep : ∀ b, ¬ input b → x b ≠ y b → ∃ a, edge a b ∧ x a ≠ y a)
    (sameCut : x cut = y cut) {out : W} (different : x out ≠ y out) :
    ∃ a, input a ∧ x a ≠ y a ∧ Relation.ReflTransGen (avoid edge cut) a out := by
  classical
  have track : ∀ k b, rank b = k → x b ≠ y b →
      ∃ a, input a ∧ x a ≠ y a ∧ Relation.ReflTransGen (avoid edge cut) a b := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro b hb diff
      by_cases hInput : input b
      · exact ⟨b, hInput, diff, Relation.ReflTransGen.refl⟩
      · obtain ⟨p, hp, dp⟩ := localStep b hInput diff
        have earlier : rank p < k := (order p b hp).trans_eq hb
        obtain ⟨a, ha, da, path⟩ := ih (rank p) earlier p rfl dp
        have pOff : p ≠ cut := by rintro rfl; exact dp sameCut
        have bOff : b ≠ cut := by rintro rfl; exact diff sameCut
        exact ⟨a, ha, da, path.tail ⟨hp, pOff, bOff⟩⟩
  exact track (rank out) out rfl different

theorem cut_agreement {W : Type} (rank : W → Nat) (input : W → Prop)
    (edge : W → W → Prop) (cut out : W) (x y : W → Bool)
    (order : ∀ a b, edge a b → rank a < rank b)
    (localStep : ∀ b, ¬ input b → x b ≠ y b → ∃ a, edge a b ∧ x a ≠ y a)
    (sameCut : x cut = y cut)
    (blocked : ∀ a, input a → x a ≠ y a →
      ¬ Relation.ReflTransGen (avoid edge cut) a out) : x out = y out := by
  by_contra different
  obtain ⟨a, ha, da, reaches⟩ := difference_traces rank input edge cut x y
    order localStep sameCut different
  exact blocked a ha da reaches

theorem unary_factor {A : Type} (w f : A → Bool)
    (h : ∀ x y, w x = w y → f x = f y) :
    ∃ outer : Bool → Bool, ∀ x, outer (w x) = f x := by
  classical
  let outer (b : Bool) := if hb : ∃ a, w a = b then f (Classical.choose hb) else false
  refine ⟨outer, fun x => ?_⟩
  have hx : ∃ a, w a = w x := ⟨x, rfl⟩
  unfold outer
  rw [dite_eq_left hx]
  exact h _ _ (Classical.choose_spec hx)

def inputWire {n : Nat} (gs : List Gate) (v : Fin n) : Fin (n + gs.length) :=
  v.castLE (Nat.le_add_right n gs.length)

def readEdge {n : Nat} (gs : List Gate) (a b : Fin (n + gs.length)) : Prop :=
  ∃ (p : Nat) (g : Gate), gs[p]? = some g ∧ b.val = n + p ∧ a.val ∈ g.inputs

theorem read_order {n : Nat} {gs : List Gate} (hcl : CleanL n gs)
    {a b : Fin (n + gs.length)} (edge : readEdge gs a b) : a.val < b.val := by
  obtain ⟨p, g, hpg, hb, ha⟩ := edge
  rw [hb]
  exact (hcl p g hpg).lt _ ha

private theorem gate_difference {n : Nat} {gs : List Gate} (hcl : CleanL n gs)
    (x y : Fin n → Bool) (b : Fin (n + gs.length)) (notInput : ¬ b.val < n)
    (diff : vl gs x b.val ≠ vl gs y b.val) :
    ∃ a : Fin (n + gs.length), readEdge gs a b ∧ vl gs x a.val ≠ vl gs y a.val := by
  let p := b.val - n
  have hb : b.val = n + p := by dsimp [p]; omega
  have hp : p < gs.length := by have := b.isLt; omega
  let g := gs[p]
  have hpg : gs[p]? = some g := List.getElem?_eq_getElem hp
  have differingRead : ∃ a ∈ g.inputs, vl gs x a ≠ vl gs y a := by
    classical
    by_contra none
    apply diff
    rw [hb]
    exact vl_congr gs hcl x y p g hpg (fun a ha => by
      by_contra da
      exact none ⟨a, ha, da⟩)
  obtain ⟨a, ha, da⟩ := differingRead
  have ha' := (hcl p g hpg).lt a ha
  refine ⟨⟨a, by have := b.isLt; omega⟩, ⟨p, g, hpg, hb, ha⟩, da⟩

theorem circuit_cut_agreement {n : Nat} {gs : List Gate} (hcl : CleanL n gs)
    (cut out : Fin (n + gs.length)) (x y : Fin n → Bool)
    (sameCut : vl gs x cut.val = vl gs y cut.val)
    (blocked : ∀ i : Fin n, x i ≠ y i →
      ¬ Relation.ReflTransGen (avoid (readEdge gs) cut) (inputWire gs i) out) :
    vl gs x out.val = vl gs y out.val := by
  apply cut_agreement Fin.val (fun v => v.val < n) (readEdge gs) cut out
    (fun v => vl gs x v.val) (fun v => vl gs y v.val)
  · exact fun _ _ e => read_order hcl e
  · exact gate_difference hcl x y
  · exact sameCut
  · intro a ha diff
    let i : Fin n := ⟨a.val, ha⟩
    have sameWire : inputWire gs i = a := Fin.ext rfl
    have di : x i ≠ y i := by
      rw [vl_input gs x a.val ha, vl_input gs y a.val ha] at diff
      exact diff
    rw [← sameWire]
    exact blocked i di

theorem circuit_cut_factors {n : Nat} {gs : List Gate} (hcl : CleanL n gs)
    (cut out : Fin (n + gs.length)) (group : Fin n → Prop) (base : Fin n → Bool)
    (blocked : ∀ i : Fin n, group i →
      ¬ Relation.ReflTransGen (avoid (readEdge gs) cut) (inputWire gs i) out) :
    ∃ outer : Bool → Bool, ∀ x : Fin n → Bool, (∀ i, ¬ group i → x i = base i) →
      outer (vl gs x cut.val) = vl gs x out.val := by
  let Fiber := {x : Fin n → Bool // ∀ i, ¬ group i → x i = base i}
  obtain ⟨outer, ho⟩ := unary_factor
    (fun x : Fiber => vl gs x.val cut.val) (fun x : Fiber => vl gs x.val out.val) (by
      intro x y sameCut
      apply circuit_cut_agreement hcl cut out x.val y.val sameCut
      intro i diff
      apply blocked i
      by_contra notGroup
      exact diff ((x.property i notGroup).trans (y.property i notGroup).symm))
  exact ⟨outer, fun x agrees => ho ⟨x, agrees⟩⟩

end CutTrace

namespace CircuitProof.Readers

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity CircuitProof

def Reads (gs : List Gate) (p w : ℕ) : Prop := ∃ g, gs[p]? = some g ∧ w ∈ g.inputs

end CircuitProof.Readers

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

open CircuitProof CircuitProof.Readers

namespace CutTrace

open PEqualNP.CircuitLowerBounds

open CircuitProof CircuitProof.Readers

def predecessors {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (b : Fin (n + gs.length)) : List (Fin (n + gs.length)) :=
  if gate : n ≤ b.val then
    let slot := b.val - n
    have hs : slot < gs.length := by have := b.isLt; omega
    let g := gs[slot]'hs
    g.inputs.attach.map fun a => ⟨a.val, by
      have atSlot : gs[slot]? = some g := List.getElem?_eq_getElem hs
      have before := (clean slot g atSlot).lt a.val a.property
      omega⟩
  else []

theorem predecessors_values {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (b : Fin (n + gs.length)) (internal : n ≤ b.val) :
    (predecessors clean b).map Fin.val =
      (gs[b.val - n]'(by have := b.isLt; omega)).inputs := by
  simp [predecessors, internal, List.map_map, Function.comp_def]

theorem predecessors_nil_input {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (b : Fin (n + gs.length)) (primary : b.val < n) : predecessors clean b = [] := by
  simp [predecessors, show ¬ n ≤ b.val by omega]

theorem predecessors_val_gate {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (b : Fin (n + gs.length)) {p : Nat} {g : Gate} (atSlot : gs[p]? = some g) (bWire : b.val = n + p) :
    (predecessors clean b).map Fin.val = g.inputs := by
  have isGate : n ≤ b.val := by omega
  have which : b.val - n = p := by omega
  have located := (List.getElem?_eq_some_iff.mp atSlot).2
  simpa [which, located] using predecessors_values clean b isGate

theorem predecessors_mem {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (a b : Fin (n + gs.length)) : a ∈ predecessors clean b ↔ readEdge gs a b := by
  by_cases internal : n ≤ b.val
  · let slot := b.val - n
    have hs : slot < gs.length := by have := b.isLt; dsimp [slot]; omega
    let g := gs[slot]'hs
    have wire : b.val = n + slot := by dsimp [slot]; omega
    have atSlot : gs[slot]? = some g := List.getElem?_eq_getElem hs
    have valList : (predecessors clean b).map Fin.val = g.inputs :=
      predecessors_values clean b internal
    constructor
    · intro mem
      refine ⟨slot, g, atSlot, wire, ?_⟩
      rw [← valList]
      exact List.mem_map.mpr ⟨a, mem, rfl⟩
    · rintro ⟨q, h, atQ, wireQ, inside⟩
      have same : q = slot := by omega
      subst q
      have gateSame : h = g := Option.some.inj (atQ.symm.trans atSlot)
      subst h
      rw [← valList] at inside
      obtain ⟨a', mem, equal⟩ := List.mem_map.mp inside
      exact (Fin.ext equal : a' = a) ▸ mem
  · have empty : predecessors clean b = [] := by simp [predecessors, internal]
    rw [empty]
    constructor
    · simp
    · rintro ⟨slot, g, _, wire, _⟩
      omega

end CutTrace

namespace PairFormula

open PEqualNP.MetaComplexity

def occurrences {n : ℕ} (i : Fin n) : DMFormula n → ℕ
  | .lit k _ => if k = i then 1 else 0
  | .and p q => occurrences i p + occurrences i q
  | .or p q => occurrences i p + occurrences i q

def hasPair {n : ℕ} (i j : Fin n) (p : DMFormula n) : Prop :=
  0 < occurrences i p ∨ 0 < occurrences j p

def pairInput {n : ℕ} (i j : Fin n) (base : Fin n → Bool) (a b : Bool) (k : Fin n) : Bool :=
  if k = i then a else if k = j then b else base k

def pairValue {n : ℕ} (i j : Fin n) (base : Fin n → Bool) (p : DMFormula n) :
    Bool → Bool → Bool :=
  fun a b => p.eval (pairInput i j base a b)

def binOp (conj : Bool) (a b : Bool) : Bool :=
  if conj then a && b else a || b

noncomputable def combine {n : ℕ} (conj : Bool) (i j : Fin n) (p q : DMFormula n)
    (P Q : Bool → Bool → Bool) : Bool → Bool → Bool := by
  classical
  exact if hasPair i j p then
    if hasPair i j q then fun a b => binOp conj (P a b) (Q a b) else P
    else Q

noncomputable def pairKernel {n : ℕ} (i j : Fin n) : DMFormula n → Bool → Bool → Bool
  | .lit k sign => fun a b =>
    let bit := if k = i then a else if k = j then b else false
    if sign then bit else !bit
  | .and p q => combine true i j p q (pairKernel i j p) (pairKernel i j q)
  | .or p q => combine false i j p q (pairKernel i j p) (pairKernel i j q)

private theorem eval_agree {n : ℕ} (p : DMFormula n) {x y : Fin n → Bool}
    (h : ∀ k, 0 < occurrences k p → x k = y k) : p.eval x = p.eval y := by
  induction p with
  | lit k s =>
    have e := h k (by simp [occurrences])
    simp [DMFormula.eval, e]
  | and p q ihp ihq =>
    simp only [DMFormula.eval]
    rw [ihp (fun k hk => h k (by simp only [occurrences]; omega)),
      ihq (fun k hk => h k (by simp only [occurrences]; omega))]
  | or p q ihp ihq =>
    simp only [DMFormula.eval]
    rw [ihp (fun k hk => h k (by simp only [occurrences]; omega)),
      ihq (fun k hk => h k (by simp only [occurrences]; omega))]

private theorem absent_left {n : ℕ} {i j : Fin n} {base : Fin n → Bool} {p : DMFormula n}
    (h : occurrences i p = 0) (a a' b : Bool) :
    pairValue i j base p a b = pairValue i j base p a' b := by
  apply eval_agree
  intro k hk
  have ne : k ≠ i := by rintro rfl; omega
  simp [pairInput, ne]

private theorem absent_right {n : ℕ} {i j : Fin n} {base : Fin n → Bool} {p : DMFormula n}
    (h : occurrences j p = 0) (a b b' : Bool) :
    pairValue i j base p a b = pairValue i j base p a b' := by
  apply eval_agree
  intro k hk
  have ne : k ≠ j := by rintro rfl; omega
  simp [pairInput, ne]

def changes (f : Bool → Bool → Bool) : Prop :=
  ∃ b, f false b ≠ f true b

private theorem changes_left {op : Bool → Bool → Bool} {P Q : Bool → Bool → Bool}
    (h : changes fun a b => op (P a b) (Q a b))
    (hQ : ∀ b, Q false b = Q true b) : changes P := by
  obtain ⟨b, hb⟩ := h
  exact ⟨b, fun hp => hb (by
    change op (P false b) (Q false b) = op (P true b) (Q true b)
    rw [hp, hQ])⟩

private theorem changes_right {op : Bool → Bool → Bool} {P Q : Bool → Bool → Bool}
    (h : changes fun a b => op (P a b) (Q a b))
    (hP : ∀ b, P false b = P true b) : changes Q := by
  obtain ⟨b, hb⟩ := h
  exact ⟨b, fun hq => hb (by
    change op (P false b) (Q false b) = op (P true b) (Q true b)
    rw [hq, hP])⟩

private theorem constant_pair {n : ℕ} {i j : Fin n} {base : Fin n → Bool} {p : DMFormula n}
    (h : ¬ hasPair i j p) (a b : Bool) :
    pairValue i j base p a b = pairValue i j base p false false := by
  have hi : occurrences i p = 0 := by
    by_contra e
    exact h (Or.inl (by omega))
  have hj : occurrences j p = 0 := by
    by_contra e
    exact h (Or.inr (by omega))
  exact (absent_left hi a false b).trans (absent_right hj false b false)

private theorem neutral_right (conj c : Bool) (P : Bool → Bool → Bool)
    (h : ∃ a b a' b', binOp conj (P a b) c ≠ binOp conj (P a' b') c) :
    ∀ a b, binOp conj (P a b) c = P a b := by
  cases conj <;> cases c <;> simp [binOp] at h ⊢

private theorem bin_comm (conj a b : Bool) : binOp conj a b = binOp conj b a := by
  cases conj <;> cases a <;> cases b <;> rfl

private theorem combine_stable {n : ℕ} (i j : Fin n) (base : Fin n → Bool)
    (conj : Bool) (p q : DMFormula n)
    (hi : occurrences i p + occurrences i q ≤ 1)
    (hj : occurrences j p + occurrences j q ≤ 1)
    (present : hasPair i j p ∨ hasPair i j q)
    (dep_i : 0 < occurrences i p + occurrences i q →
      changes fun a b => binOp conj (pairValue i j base p a b) (pairValue i j base q a b))
    (dep_j : 0 < occurrences j p + occurrences j q →
      changes fun b a => binOp conj (pairValue i j base p a b) (pairValue i j base q a b))
    (ihp : occurrences i p ≤ 1 → occurrences j p ≤ 1 → hasPair i j p →
      (0 < occurrences i p → changes (pairValue i j base p)) →
      (0 < occurrences j p → changes fun b a => pairValue i j base p a b) →
      ∀ a b, pairValue i j base p a b = pairKernel i j p a b)
    (ihq : occurrences i q ≤ 1 → occurrences j q ≤ 1 → hasPair i j q →
      (0 < occurrences i q → changes (pairValue i j base q)) →
      (0 < occurrences j q → changes fun b a => pairValue i j base q a b) →
      ∀ a b, pairValue i j base q a b = pairKernel i j q a b)
    (a b : Bool) :
    binOp conj (pairValue i j base p a b) (pairValue i j base q a b) =
      combine conj i j p q (pairKernel i j p) (pairKernel i j q) a b := by
  classical
  have pl : hasPair i j p → ∀ a b, pairValue i j base p a b = pairKernel i j p a b := by
    intro hp
    apply ihp (by omega) (by omega) hp
    · intro h
      exact changes_left (dep_i (by omega)) (fun b => absent_left (by omega) false true b)
    · intro h
      exact changes_left (dep_j (by omega)) (fun a => absent_right (by omega) a false true)
  have ql : hasPair i j q → ∀ a b, pairValue i j base q a b = pairKernel i j q a b := by
    intro hq
    apply ihq (by omega) (by omega) hq
    · intro h
      exact changes_right (dep_i (by omega)) (fun b => absent_left (by omega) false true b)
    · intro h
      exact changes_right (dep_j (by omega)) (fun a => absent_right (by omega) a false true)
  have nonconst : ∃ a b a' b',
      binOp conj (pairValue i j base p a b) (pairValue i j base q a b) ≠
        binOp conj (pairValue i j base p a' b') (pairValue i j base q a' b') := by
    unfold hasPair at present
    rcases present with (h | h) | (h | h)
    · obtain ⟨b, h⟩ := dep_i (by omega)
      exact ⟨false, b, true, b, h⟩
    · obtain ⟨a, h⟩ := dep_j (by omega)
      exact ⟨a, false, a, true, h⟩
    · obtain ⟨b, h⟩ := dep_i (by omega)
      exact ⟨false, b, true, b, h⟩
    · obtain ⟨a, h⟩ := dep_j (by omega)
      exact ⟨a, false, a, true, h⟩
  by_cases hp : hasPair i j p
  · by_cases hq : hasPair i j q
    · simp [combine, hp, hq, pl hp, ql hq]
    · rw [constant_pair hq a b]
      have hn := nonconst
      simp_rw [constant_pair hq] at hn
      rw [neutral_right conj _ _ hn a b, pl hp]
      simp [combine, hp, hq]
  · have hq := present.resolve_left hp
    rw [constant_pair hp a b, bin_comm]
    have hn := nonconst
    simp_rw [constant_pair hp, bin_comm conj (pairValue i j base p false false)] at hn
    rw [neutral_right conj _ _ hn a b, ql hq]
    simp [combine, hp]

private theorem stable_pair {n : ℕ} (i j : Fin n) (base : Fin n → Bool) (p : DMFormula n)
    (hi : occurrences i p ≤ 1) (hj : occurrences j p ≤ 1) (present : hasPair i j p)
    (dep_i : 0 < occurrences i p → changes (pairValue i j base p))
    (dep_j : 0 < occurrences j p → changes fun b a => pairValue i j base p a b) :
    ∀ a b, pairValue i j base p a b = pairKernel i j p a b := by
  induction p with
  | lit k s =>
    intro a b
    by_cases hki : k = i
    · simp [pairValue, pairKernel, DMFormula.eval, pairInput, hki]
    · have hkj : k = j := by
        by_contra h
        simp [hasPair, occurrences, hki, h] at present
      simp [pairValue, pairKernel, DMFormula.eval, pairInput, hkj]
  | and p q ihp ihq =>
    have present' : hasPair i j p ∨ hasPair i j q := by
      unfold hasPair at *
      simp only [occurrences] at present
      omega
    exact combine_stable i j base true p q hi hj present' dep_i dep_j ihp ihq
  | or p q ihp ihq =>
    have present' : hasPair i j p ∨ hasPair i j q := by
      unfold hasPair at *
      simp only [occurrences] at present
      omega
    exact combine_stable i j base false p q hi hj present' dep_i dep_j ihp ihq

theorem fixed_pair_invariant {n : ℕ} (i j : Fin n) (p : DMFormula n)
    (hi : occurrences i p ≤ 1) (hj : occurrences j p ≤ 1)
    (baseA baseO : Fin n → Bool) (outerA outerO : Bool → Bool)
    (hA : ∀ a b, outerA (pairValue i j baseA p a b) = (a && b))
    (hO : ∀ a b, outerO (pairValue i j baseO p a b) = (a || b)) : False := by
  have depAi : changes (pairValue i j baseA p) := by
    refine ⟨true, fun h => ?_⟩
    have e := congrArg outerA h
    rw [hA, hA] at e
    cases e
  have depAj : changes fun b a => pairValue i j baseA p a b := by
    refine ⟨true, fun h => ?_⟩
    have e := congrArg outerA h
    rw [hA, hA] at e
    cases e
  have depOi : changes (pairValue i j baseO p) := by
    refine ⟨false, fun h => ?_⟩
    have e := congrArg outerO h
    rw [hO, hO] at e
    cases e
  have depOj : changes fun b a => pairValue i j baseO p a b := by
    refine ⟨false, fun h => ?_⟩
    have e := congrArg outerO h
    rw [hO, hO] at e
    cases e
  have present : hasPair i j p := by
    left
    by_contra! h
    obtain ⟨b, hb⟩ := depAi
    exact hb (absent_left (by omega) false true b)
  have stableA := stable_pair i j baseA p hi hj present (fun _ => depAi) (fun _ => depAj)
  have stableO := stable_pair i j baseO p hi hj present (fun _ => depOi) (fun _ => depOj)
  simp_rw [stableA] at hA
  simp_rw [stableO] at hO
  have ne : pairKernel i j p false false ≠ pairKernel i j p false true := by
    intro e
    have f := congrArg outerO e
    rw [hO, hO] at f
    cases f
  have zeros := hA false false
  have other := hA false true
  have one := hA true true
  cases hk : pairKernel i j p false false <;>
    cases hl : pairKernel i j p false true <;>
    cases hm : pairKernel i j p true true <;>
    simp_all

end PairFormula

namespace CutFormula

open PEqualNP.CircuitLowerBounds

open PEqualNP.MetaComplexity

open CircuitProof

open PairFormula

def negFormula {n : Nat} : DMFormula n → DMFormula n
  | .lit i sign => .lit i (!sign)
  | .and a b => .or (negFormula a) (negFormula b)
  | .or a b => .and (negFormula a) (negFormula b)

theorem negFormula_eval {n : Nat} (p : DMFormula n) (x : Fin n → Bool) :
    (negFormula p).eval x = !(p.eval x) := by
  induction p with
  | lit i s =>
    cases s <;> cases e : x i <;> simp [negFormula, DMFormula.eval, e]
  | and a b iha ihb =>
    simp only [negFormula, DMFormula.eval, iha, ihb]
    cases a.eval x <;> cases b.eval x <;> rfl
  | or a b iha ihb =>
    simp only [negFormula, DMFormula.eval, iha, ihb]
    cases a.eval x <;> cases b.eval x <;> rfl

theorem negFormula_occurrences {n : Nat} (i : Fin n) (p : DMFormula n) :
    occurrences i (negFormula p) = occurrences i p := by
  induction p with
  | lit i s => rfl
  | and a b iha ihb => simp [negFormula, occurrences, iha, ihb]
  | or a b iha ihb => simp [negFormula, occurrences, iha, ihb]

def wireFormula {n : Nat} (fallback : Fin n) (gs : List Gate) (w : Nat) : DMFormula n :=
  if hw : w < n then
    .lit ⟨w, hw⟩ true
  else
    match gs[w - n]? with
    | none => .lit fallback true
    | some g =>
      match g.op, g.inputs with
      | .not, [a] =>
        if _ha : a < w then negFormula (wireFormula fallback gs a) else .lit fallback true
      | .and, [a, b] =>
        if _ha : a < w then
          if _hb : b < w then .and (wireFormula fallback gs a) (wireFormula fallback gs b)
          else .lit fallback true
        else .lit fallback true
      | .or, [a, b] =>
        if _ha : a < w then
          if _hb : b < w then .or (wireFormula fallback gs a) (wireFormula fallback gs b)
          else .lit fallback true
        else .lit fallback true
      | _, _ => .lit fallback true
termination_by w
decreasing_by all_goals assumption

theorem wireFormula_input {n : Nat} (fallback : Fin n) (gs : List Gate) (i : Fin n) :
    wireFormula fallback gs i.val = .lit i true := by
  rw [wireFormula]
  simp [i.isLt]

private theorem wireFormula_not {n : Nat} (fallback : Fin n) {gs : List Gate}
    {p a : Nat} {g : Gate} (hg : gs[p]? = some g) (op : g.op = .not)
    (inputs : g.inputs = [a]) (ha : a < n + p) :
    wireFormula fallback gs (n + p) = negFormula (wireFormula fallback gs a) := by
  have hn : ¬ n + p < n := by omega
  have hp : n + p - n = p := by omega
  conv_lhs => rw [wireFormula]
  simp [hn, hp, hg, op, inputs, ha]

private theorem wireFormula_and {n : Nat} (fallback : Fin n) {gs : List Gate}
    {p a b : Nat} {g : Gate} (hg : gs[p]? = some g) (op : g.op = .and)
    (inputs : g.inputs = [a, b]) (ha : a < n + p) (hb : b < n + p) :
    wireFormula fallback gs (n + p) = .and (wireFormula fallback gs a) (wireFormula fallback gs b) := by
  have hn : ¬ n + p < n := by omega
  have hp : n + p - n = p := by omega
  conv_lhs => rw [wireFormula]
  simp [hn, hp, hg, op, inputs, ha, hb]

private theorem wireFormula_or {n : Nat} (fallback : Fin n) {gs : List Gate}
    {p a b : Nat} {g : Gate} (hg : gs[p]? = some g) (op : g.op = .or)
    (inputs : g.inputs = [a, b]) (ha : a < n + p) (hb : b < n + p) :
    wireFormula fallback gs (n + p) = .or (wireFormula fallback gs a) (wireFormula fallback gs b) := by
  have hn : ¬ n + p < n := by omega
  have hp : n + p - n = p := by omega
  conv_lhs => rw [wireFormula]
  simp [hn, hp, hg, op, inputs, ha, hb]

theorem wireFormula_eval {n : Nat} (fallback : Fin n) {gs : List Gate} (hcl : CleanL n gs)
    (x : Fin n → Bool) (w : Nat) (hw : w < n + gs.length) :
    (wireFormula fallback gs w).eval x = vl gs x w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hi : w < n
    · rw [wireFormula_input fallback gs ⟨w, hi⟩, vl_input gs x w hi]
      rfl
    · obtain ⟨p, rfl⟩ : ∃ p, w = n + p := ⟨w - n, by omega⟩
      have hp : p < gs.length := by omega
      let g := gs[p]
      have hg : gs[p]? = some g := List.getElem?_eq_getElem hp
      rcases hcl p g hg with ⟨op, a, ha, inputs⟩ | ⟨op | op, a, b, ha, hb, inputs⟩
      · rw [wireFormula_not fallback hg op inputs ha, negFormula_eval, ih a ha (by omega),
          vl_gate gs hcl x p g hg]
        simp [op, inputs, GateOp.eval]
      · rw [wireFormula_and fallback hg op inputs ha hb]
        simp only [DMFormula.eval]
        rw [ih a ha (by omega), ih b hb (by omega), vl_gate gs hcl x p g hg]
        simp [op, inputs, GateOp.eval]
      · rw [wireFormula_or fallback hg op inputs ha hb]
        simp only [DMFormula.eval]
        rw [ih a ha (by omega), ih b hb (by omega), vl_gate gs hcl x p g hg]
        simp [op, inputs, GateOp.eval]

theorem wireFormula_count_input {n : Nat} (fallback : Fin n) (gs : List Gate) (chosen i : Fin n) :
    occurrences chosen (wireFormula fallback gs i.val) = if i = chosen then 1 else 0 := by
  rw [wireFormula_input]
  rfl

theorem wireFormula_count_gate {n : Nat} (fallback : Fin n) {gs : List Gate} (hcl : CleanL n gs)
    (chosen : Fin n) {p : Nat} {g : Gate} (hg : gs[p]? = some g) :
    occurrences chosen (wireFormula fallback gs (n + p)) =
      (g.inputs.map fun a => occurrences chosen (wireFormula fallback gs a)).sum := by
  rcases hcl p g hg with ⟨op, a, ha, inputs⟩ | ⟨op | op, a, b, ha, hb, inputs⟩
  · simp [wireFormula_not fallback hg op inputs ha, inputs, negFormula_occurrences]
  · simp [wireFormula_and fallback hg op inputs ha hb, inputs, occurrences]
  · simp [wireFormula_or fallback hg op inputs ha hb, inputs, occurrences]

theorem wireFormula_count_gate_fin {n : Nat} (fallback chosen : Fin n) {gs : List Gate}
    (hcl : CleanL n gs) {p : Nat} {g : Gate} (hg : gs[p]? = some g)
    {b : Fin (n + gs.length)} (hb : b.val = n + p)
    (parents : List (Fin (n + gs.length))) (parentsVal : parents.map Fin.val = g.inputs) :
    occurrences chosen (wireFormula fallback gs b.val) =
      (parents.map fun a => occurrences chosen (wireFormula fallback gs a.val)).sum := by
  rw [hb, wireFormula_count_gate fallback hcl chosen hg, ← parentsVal, List.map_map]
  rfl

end CutFormula

namespace CutIndependent

open PEqualNP.CircuitLowerBounds

open CircuitProof

open CutFormula CutTrace PairFormula

theorem wireFormula_count_input_fin {n : Nat} {gs : List Gate} (fallback chosen : Fin n)
    (a : Fin (n + gs.length)) (ha : a.val < n) :
    occurrences chosen (wireFormula fallback gs a.val) =
      if a = inputWire gs chosen then 1 else 0 := by
  let i : Fin n := ⟨a.val, ha⟩
  have e : i = chosen ↔ a = inputWire gs chosen := by
    constructor
    · intro h
      exact Fin.ext (congrArg (fun k : Fin n => k.val) h)
    · intro h
      exact Fin.ext (congrArg (fun k : Fin (n + gs.length) => k.val) h)
  change occurrences chosen (wireFormula fallback gs i.val) = _
  simp only [wireFormula_count_input, e]

theorem cut_factors {n : Nat} {gs : List Gate} (hcl : CleanL n gs)
    (cut out : Fin (n + gs.length)) (group : Fin n → Prop) (base : Fin n → Bool)
    (controlled : cut = out ∨ ∀ i : Fin n, group i →
      ¬ Relation.ReflTransGen (avoid (readEdge gs) cut) (inputWire gs i) out) :
    ∃ outer : Bool → Bool, ∀ x : Fin n → Bool, (∀ i, ¬ group i → x i = base i) →
      outer (vl gs x cut.val) = vl gs x out.val := by
  rcases controlled with rfl | blocked
  · exact ⟨id, fun _ _ => rfl⟩
  · exact circuit_cut_factors hcl cut out group base blocked

end CutIndependent

namespace FirstBranchRoute

open Relation

variable {m : Nat} (reads : Fin m → Fin m → Prop) (output : Fin m)

def Branches (v : Fin m) : Prop := ∃ a b, reads v a ∧ reads v b ∧ a ≠ b

def Terminal (v : Fin m) : Prop := v = output ∨ Branches reads v

def Follow (v w : Fin m) : Prop := reads v w ∧ ¬ Terminal reads output v

lemma follow_unique {v a b : Fin m} (first : Follow reads output v a) (next : Follow reads output v b) :
    a = b := by
  by_contra separate
  exact first.2 (Or.inr ⟨a, b, first.1, next.1, separate⟩)

variable (forward : ∀ {v w : Fin m}, reads v w → v < w)

variable (live : ∀ v : Fin m, v ≠ output → ∃ w, reads v w)

include forward live in

theorem exists_boundary (v : Fin m) :
    ∃ root : Fin m, Terminal reads output root ∧ ReflTransGen (Follow reads output) v root := by
  let distance (w : Fin m) := m - w.val
  induction v using (measure distance).wf.induction with
  | h v ih =>
    by_cases terminal : Terminal reads output v
    · exact ⟨v, terminal, ReflTransGen.refl⟩
    obtain ⟨next, edge⟩ := live v (fun e => terminal (Or.inl e))
    have increase := forward edge
    have closer : distance next < distance v := by
      dsimp [distance]
      have bounds := next.isLt
      change v.val < next.val at increase
      omega
    obtain ⟨root, stopped, route⟩ := ih next closer
    exact ⟨root, stopped, route.head ⟨edge, terminal⟩⟩

include forward in

theorem boundary_unique {v a b : Fin m} (terminalA : Terminal reads output a)
    (terminalB : Terminal reads output b) (routeA : ReflTransGen (Follow reads output) v a)
    (routeB : ReflTransGen (Follow reads output) v b) : a = b := by
  let distance (w : Fin m) := m - w.val
  induction v using (measure distance).wf.induction generalizing a b with
  | h v ih =>
    rcases routeA.cases_head with h | ⟨next, edge, tailA⟩
    · subst a
      rcases routeB.cases_head with h | ⟨_, edgeB, _⟩
      · exact h
      · exact (edgeB.2 terminalA).elim
    · rcases routeB.cases_head with h | ⟨nextB, edgeB, tailB⟩
      · subst b
        exact (edge.2 terminalB).elim
      have equal := follow_unique reads output edge edgeB
      subst nextB
      have increase := forward edge.1
      have closer : distance next < distance v := by
        dsimp [distance]
        have bounds := next.isLt
        change v.val < next.val at increase
        omega
      exact ih next closer terminalA terminalB tailA tailB

noncomputable def first (v : Fin m) : Fin m :=
  Classical.choose (exists_boundary reads output forward live v)

theorem first_stops (v : Fin m) : Terminal reads output (first reads output forward live v) :=
  (Classical.choose_spec (exists_boundary reads output forward live v)).1

theorem first_path (v : Fin m) : ReflTransGen (Follow reads output) v (first reads output forward live v) :=
  (Classical.choose_spec (exists_boundary reads output forward live v)).2

theorem first_of_terminal {v : Fin m} (stopped : Terminal reads output v) :
    first reads output forward live v = v :=
  boundary_unique reads output forward (first_stops reads output forward live v) stopped
    (first_path reads output forward live v) ReflTransGen.refl

theorem first_of_follows {v w : Fin m} (step : Follow reads output v w) :
    first reads output forward live v = first reads output forward live w :=
  boundary_unique reads output forward (first_stops reads output forward live v)
    (first_stops reads output forward live w) (first_path reads output forward live v)
    ((first_path reads output forward live w).head step)

include forward in

theorem path_forward {v w : Fin m} (route : ReflTransGen reads v w) : v ≤ w := by
  induction route with
  | refl => exact le_rfl
  | tail _ edge ih => exact le_trans ih (le_of_lt (forward edge))

lemma follows_is_read_path {v w : Fin m} (route : ReflTransGen (Follow reads output) v w) :
    ReflTransGen reads v w := by
  induction route with
  | refl => exact ReflTransGen.refl
  | tail _ edge ih => exact ih.tail edge.1

theorem first_forward (v : Fin m) : v ≤ first reads output forward live v :=
  path_forward reads forward (follows_is_read_path reads output (first_path reads output forward live v))

theorem read_before {v w : Fin m} (route : ReflTransGen reads v w)
    (before : w ≤ first reads output forward live v) :
    ReflTransGen (Follow reads output) v w ∧ first reads output forward live w = first reads output forward live v := by
  induction route with
  | refl => exact ⟨ReflTransGen.refl, rfl⟩
  | tail _ edge ih =>
    have predecessorBefore := lt_of_lt_of_le (forward edge) before
    obtain ⟨tracked, label⟩ := ih (le_of_lt predecessorBefore)
    have step : Follow reads output _ _ := ⟨edge, fun stopped => by
      have self := first_of_terminal reads output forward live stopped
      rw [self] at label
      exact (ne_of_lt predecessorBefore) label⟩
    exact ⟨tracked.tail step, (first_of_follows reads output forward live step).symm.trans label⟩

theorem ancestor_first_le {v w : Fin m} (route : ReflTransGen reads v w)
    (stopped : Terminal reads output w) : first reads output forward live v ≤ w := by
  by_contra tooLate
  have earlier := lt_of_not_ge tooLate
  have same := (read_before reads output forward live route (le_of_lt earlier)).2
  rw [first_of_terminal reads output forward live stopped] at same
  exact (ne_of_lt earlier) same

theorem edge_before {v a b : Fin m} (route : ReflTransGen reads v a) (edge : reads a b)
    (bound : b ≤ first reads output forward live v) : Follow reads output a b := by
  have earlier := lt_of_lt_of_le (forward edge) bound
  have same := (read_before reads output forward live route (le_of_lt earlier)).2
  refine ⟨edge, fun stopped => ?_⟩
  rw [first_of_terminal reads output forward live stopped] at same
  exact (ne_of_lt earlier) same

def Avoid (cut v w : Fin m) : Prop := reads v w ∧ v ≠ cut

lemma avoiding_is_read_path (cut : Fin m) {v w : Fin m} (route : ReflTransGen (Avoid reads cut) v w) :
    ReflTransGen reads v w := by
  induction route with
  | refl => exact ReflTransGen.refl
  | tail _ edge ih => exact ih.tail edge.1

theorem avoiding_stays_before {v w : Fin m}
    (route : ReflTransGen (Avoid reads (first reads output forward live v)) v w) :
    w ≤ first reads output forward live v := by
  induction route with
  | refl => exact first_forward reads output forward live v
  | tail prior edge ih =>
    have label := (read_before reads output forward live (avoiding_is_read_path reads _ prior) ih).2
    have earlier := lt_of_le_of_ne ih edge.2
    have following : Follow reads output _ _ := ⟨edge.1, fun terminal => by
      rw [first_of_terminal reads output forward live terminal] at label
      exact (ne_of_lt earlier) label⟩
    have same := (first_of_follows reads output forward live following).symm.trans label
    rw [← same]
    exact first_forward reads output forward live _

theorem no_avoiding_after {v w : Fin m} (after : first reads output forward live v < w) :
    ¬ ReflTransGen (Avoid reads (first reads output forward live v)) v w :=
  fun route => (not_lt_of_ge (avoiding_stays_before reads output forward live route)) after

include forward in

theorem unique_follow_predecessor {source a b goal : Fin m}
    (routeA : ReflTransGen (Follow reads output) source a) (edgeA : Follow reads output a goal)
    (routeB : ReflTransGen (Follow reads output) source b) (edgeB : Follow reads output b goal) : a = b := by
  let distance (w : Fin m) := m - w.val
  induction source using (measure distance).wf.induction generalizing a b with
  | h source ih =>
    rcases routeA.cases_head with aHere | ⟨nextA, stepA, laterA⟩
    · subst a
      rcases routeB.cases_head with bHere | ⟨next, stepB, later⟩
      · exact bHere
      have equal : next = goal := follow_unique reads output stepB edgeA
      subst next
      have increasing := path_forward reads forward (follows_is_read_path reads output later)
      exact (not_lt_of_ge increasing (forward edgeB.1)).elim
    · rcases routeB.cases_head with bHere | ⟨nextB, stepB, laterB⟩
      · subst b
        have equal : nextA = goal := follow_unique reads output stepA edgeB
        subst nextA
        have increasing := path_forward reads forward (follows_is_read_path reads output laterA)
        exact (not_lt_of_ge increasing (forward edgeA.1)).elim
      have equal := follow_unique reads output stepA stepB
      subst nextB
      have increase := forward stepA.1
      have closer : distance nextA < distance source := by
        dsimp [distance]
        have bounds := nextA.isLt
        change source.val < nextA.val at increase
        omega
      exact ih nextA closer laterA edgeA laterB edgeB

theorem unique_predecessor_before {source a b goal : Fin m}
    (bound : goal ≤ first reads output forward live source)
    (routeA : ReflTransGen reads source a) (edgeA : reads a goal)
    (routeB : ReflTransGen reads source b) (edgeB : reads b goal) : a = b := by
  have aBound := le_trans (le_of_lt (forward edgeA)) bound
  have bBound := le_trans (le_of_lt (forward edgeB)) bound
  exact unique_follow_predecessor reads output forward
    (read_before reads output forward live routeA aBound).1
    (edge_before reads output forward live routeA edgeA bound)
    (read_before reads output forward live routeB bBound).1
    (edge_before reads output forward live routeB edgeB bound)

lemma witness_of_positive_sum {α : Type*} (weight : α → Nat) (xs : List α)
    (positive : 0 < (xs.map weight).sum) : ∃ a ∈ xs, 0 < weight a := by
  induction xs with
  | nil => simp at positive
  | cons a rest ih =>
    by_cases h : 0 < weight a
    · exact ⟨a, by simp, h⟩
    have hr : 0 < (rest.map weight).sum := by
      simp only [List.map_cons, List.sum_cons] at positive
      omega
    obtain ⟨b, hb, hbPos⟩ := ih hr
    exact ⟨b, by simp [hb], hbPos⟩

lemma sum_le_one_of_unique_positive {α : Type*} (weight : α → Nat) (xs : List α)
    (distinct : xs.Nodup) (small : ∀ a ∈ xs, weight a ≤ 1)
    (unique : ∀ a ∈ xs, ∀ b ∈ xs, 0 < weight a → 0 < weight b → a = b) :
    (xs.map weight).sum ≤ 1 := by
  induction xs with
  | nil => simp
  | cons a rest ih =>
    simp only [List.nodup_cons] at distinct
    simp only [List.map_cons, List.sum_cons]
    by_cases h : weight a = 0
    · rw [h, Nat.zero_add]
      exact ih distinct.2 (fun b hb => small b (by simp [hb]))
        (fun b hb c hc => unique b (by simp [hb]) c (by simp [hc]))
    have restZero : (rest.map weight).sum = 0 := by
      by_contra some
      obtain ⟨b, hb, hbPos⟩ := witness_of_positive_sum weight rest (by omega)
      have equal := unique a (by simp) b (by simp [hb]) (by omega) hbPos
      exact distinct.1 (by simpa [equal] using hb)
    rw [restZero, Nat.add_zero]
    exact small a (by simp)

section Count

variable (parents : Fin m → List (Fin m))

variable (reads_parent : ∀ a b : Fin m, reads a b ↔ a ∈ parents b)

variable (weight : Fin m → Nat) (source : Fin m)

variable (other_weight : ∀ v : Fin m, v ≠ source → weight v = ((parents v).map weight).sum)

include forward reads_parent other_weight in

theorem weight_positive_path {v : Fin m} (positive : 0 < weight v) : ReflTransGen reads source v := by
  revert positive
  induction v using (measure (fun w : Fin m => w.val)).wf.induction with
  | h v ih =>
    intro positive
    by_cases isSource : v = source
    · subst v
      exact ReflTransGen.refl
    rw [other_weight v isSource] at positive
    obtain ⟨a, member, hp⟩ := witness_of_positive_sum weight (parents v) positive
    have edge := (reads_parent a v).mpr member
    have earlier := forward edge
    exact (ih a earlier hp).tail edge

include reads_parent other_weight in

theorem weight_before_le_one (rootWeight : weight source = 1) (distinct : ∀ v, (parents v).Nodup)
    {v : Fin m} (bound : v ≤ first reads output forward live source) : weight v ≤ 1 := by
  revert bound
  induction v using (measure (fun w : Fin m => w.val)).wf.induction with
  | h v ih =>
    intro bound
    by_cases isSource : v = source
    · subst v
      exact le_of_eq rootWeight
    rw [other_weight v isSource]
    apply sum_le_one_of_unique_positive weight (parents v) (distinct v)
    · intro a member
      have earlier := forward ((reads_parent a v).mpr member)
      exact ih a earlier (le_trans (le_of_lt earlier) bound)
    · intro a ma b mb ha hb
      exact unique_predecessor_before reads output forward live bound
        (weight_positive_path reads forward parents reads_parent weight source other_weight ha)
        ((reads_parent a v).mpr ma)
        (weight_positive_path reads forward parents reads_parent weight source other_weight hb)
        ((reads_parent b v).mpr mb)

end Count

end FirstBranchRoute

namespace InputBoundary

open PEqualNP.CircuitLowerBounds

open CircuitProof

open CutFormula CutIndependent CutTrace PairFormula

noncomputable def firstInputBoundary {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (i : Fin n) : Fin (n + gs.length) :=
  FirstBranchRoute.first (readEdge gs) out (read_order clean) live (inputWire gs i)

noncomputable def firstInputGroup {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (cut : Fin (n + gs.length)) : Finset (Fin n) :=
  Finset.univ.filter fun i => firstInputBoundary clean out live i = cut

theorem mem_firstInputGroup {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (cut : Fin (n + gs.length)) (i : Fin n) :
    i ∈ firstInputGroup clean out live cut ↔ firstInputBoundary clean out live i = cut := by
  simp [firstInputGroup]

theorem wire_le_output {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (w : Fin (n + gs.length)) : w ≤ out := by
  let last : Fin (n + gs.length) := ⟨n + gs.length - 1, by have := out.isLt; omega⟩
  have top (v : Fin (n + gs.length)) : v ≤ last := by
    change v.val ≤ n + gs.length - 1
    have := v.isLt
    omega
  have lastOut : last = out := by
    by_contra notOutput
    obtain ⟨v, e⟩ := live last notOutput
    exact (not_lt_of_ge (top v)) (read_order clean e)
  exact lastOut ▸ top w

theorem firstInputBoundary_occurrences_le_one {n : Nat} {gs : List Gate}
    (clean : CleanL n gs) (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (distinct : ∀ w, (predecessors clean w).Nodup)
    (fallback chosen : Fin n) :
    occurrences chosen (wireFormula fallback gs (firstInputBoundary clean out live chosen).val)
      ≤ 1 := by
  let weight (a : Fin (n + gs.length)) := occurrences chosen (wireFormula fallback gs a.val)
  have sourcePrimary : (inputWire gs chosen).val < n := chosen.isLt
  have atSource : weight (inputWire gs chosen) = 1 := by
    dsimp [weight]
    rw [wireFormula_count_input_fin fallback chosen _ sourcePrimary, ite_eq_left rfl]
  have otherWeight : ∀ w : Fin (n + gs.length), w ≠ inputWire gs chosen →
      weight w = ((predecessors clean w).map weight).sum := by
    intro w other
    by_cases primary : w.val < n
    · simp [weight, wireFormula_count_input_fin fallback chosen w primary, other,
        predecessors_nil_input clean w primary]
    · let p := w.val - n
      have hp : p < gs.length := by have := w.isLt; dsimp [p]; omega
      have hw : w.val = n + p := by dsimp [p]; omega
      let g := gs[p]
      have atSlot : gs[p]? = some g := List.getElem?_eq_getElem hp
      exact wireFormula_count_gate_fin fallback chosen clean atSlot hw _
        (predecessors_val_gate clean w atSlot hw)
  exact FirstBranchRoute.weight_before_le_one (readEdge gs) out (read_order clean) live
    (predecessors clean) (fun a b => (predecessors_mem clean a b).symm) weight
    (inputWire gs chosen) otherWeight atSource distinct le_rfl

theorem firstInputGroup_controlled {n : Nat} {gs : List Gate}
    (clean : CleanL n gs) (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (cut : Fin (n + gs.length)) :
    cut = out ∨ ∀ k : Fin n, k ∈ firstInputGroup clean out live cut →
      ¬ Relation.ReflTransGen (avoid (readEdge gs) cut) (inputWire gs k) out := by
  by_cases terminal : cut = out
  · exact Or.inl terminal
  right
  intro k member path
  have before : cut < out := lt_of_le_of_ne (wire_le_output clean out live cut) terminal
  have firstHere := (mem_firstInputGroup clean out live cut k).mp member
  have after : firstInputBoundary clean out live k < out := by rwa [firstHere]
  have blocked := FirstBranchRoute.no_avoiding_after (readEdge gs) out
    (read_order clean) live after
  apply blocked
  change Relation.ReflTransGen (FirstBranchRoute.Avoid (readEdge gs)
    (firstInputBoundary clean out live k)) (inputWire gs k) out
  rw [firstHere]
  exact Relation.ReflTransGen.mono (fun _ _ e => ⟨e.1, e.2.1⟩) _ _ path

end InputBoundary

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

open CircuitProof CircuitProof.Readers

open scoped BigOperators

def operands (gs : List Gate) : List Nat := gs.flatMap Gate.inputs

def notGateCount (gs : List Gate) : Nat := (gs.filter fun g => isNotGate g.op).length

theorem operand_mem_of_read {gs : List Gate} {slot wire : Nat} (read : Reads gs slot wire) :
    wire ∈ operands gs := by
  obtain ⟨g, gAt, before⟩ := read
  exact List.mem_flatMap.mpr ⟨g, List.mem_iff_getElem?.mpr ⟨slot, gAt⟩, before⟩

theorem two_readers_operand_count {gs : List Gate} {wire p q : Nat}
    (neq : p ≠ q) (first : Reads gs p wire) (second : Reads gs q wire) :
    2 ≤ (operands gs).count wire := by
  induction gs generalizing p q with
  | nil =>
    rcases first with ⟨g, atGate, _⟩
    simp at atGate
  | cons a rest ih =>
    simp only [operands, List.flatMap_cons, List.count_append]
    cases p with
    | zero =>
      cases q with
      | zero => exact (neq rfl).elim
      | succ q =>
        have atA : wire ∈ a.inputs := by simpa [Reads] using first
        have later : Reads rest q wire := by simpa [Reads] using second
        have aPos : 0 < a.inputs.count wire := List.count_pos_iff.mpr atA
        have restPos : 0 < (operands rest).count wire := List.count_pos_iff.mpr (operand_mem_of_read later)
        simp only [operands] at restPos
        omega
    | succ p =>
      cases q with
      | zero =>
        have atA : wire ∈ a.inputs := by simpa [Reads] using second
        have later : Reads rest p wire := by simpa [Reads] using first
        have aPos : 0 < a.inputs.count wire := List.count_pos_iff.mpr atA
        have restPos : 0 < (operands rest).count wire := List.count_pos_iff.mpr (operand_mem_of_read later)
        simp only [operands] at restPos
        omega
      | succ q =>
        have early : Reads rest p wire := by simpa [Reads] using first
        have late : Reads rest q wire := by simpa [Reads] using second
        have different : p ≠ q := fun eq => neq (congrArg Nat.succ eq)
        have count := ih different early late
        simp only [operands] at count
        omega

theorem operands_count_length (gs : List Gate)
    (arity : ∀ g ∈ gs, g.inputs.length + (if isNotGate g.op then 1 else 0) = 2) :
    (operands gs).length + notGateCount gs = 2 * gs.length := by
  induction gs with
  | nil => simp [operands, notGateCount]
  | cons g gs ih =>
    have gArity := arity g (by simp)
    have rest := ih (fun q hq => arity q (List.mem_cons_of_mem _ hq))
    cases h : isNotGate g.op
    · simp [h] at gArity
      simp [operands, notGateCount, h] at rest ⊢
      omega
    · simp [h] at gArity
      simp [operands, notGateCount, h] at rest ⊢
      omega

theorem clean_gate_arity {n : Nat} {gs : List Gate} (h : CleanL n gs) :
    ∀ g ∈ gs, g.inputs.length + (if isNotGate g.op then 1 else 0) = 2 := by
  intro g gMem
  obtain ⟨p, atGate⟩ := List.mem_iff_getElem?.mp gMem
  rcases h p g atGate with ⟨op, a, _, args⟩ | ⟨ops, a, b, _, _, args⟩
  · simp [op, args, isNotGate]
  · rcases ops with op | op <;> simp [op, args, isNotGate]

theorem branch_card_add_wire_card_le_operands (gs : List Gate) (branches : Finset Nat)
    (twice : ∀ w ∈ branches, 2 ≤ (operands gs).count w) :
    branches.card + (operands gs).toFinset.card ≤ (operands gs).length := by
  classical
  let W := (operands gs).toFinset
  have subset : branches ⊆ W := by
    intro w wm
    have t := twice w wm
    exact List.mem_toFinset.mpr (List.count_pos_iff.mp (by omega))
  have aux : (∑ w ∈ W, if w ∈ branches then (1 : Nat) else 0) = branches.card := by
    have same : (∑ w ∈ W, if w ∈ branches then (1 : Nat) else 0) =
        ∑ w ∈ branches, if w ∈ branches then (1 : Nat) else 0 := by
      symm
      apply Finset.sum_subset subset
      intro w _ notBranch
      simp [notBranch]
    rw [same]
    simp
  have total : (∑ w ∈ W, (operands gs).count w) = (operands gs).length :=
    List.sum_toFinset_count_eq_length _
  have bound : (∑ w ∈ W, ((if w ∈ branches then (1 : Nat) else 0) + 1)) ≤
      ∑ w ∈ W, (operands gs).count w := by
    apply Finset.sum_le_sum
    intro w wIn
    by_cases b : w ∈ branches
    · simpa [b] using twice w b
    · have pos : 0 < (operands gs).count w := List.count_pos_iff.mpr (List.mem_toFinset.mp wIn)
      simpa [b] using pos
  rw [Finset.sum_add_distrib, aux, total] at bound
  simpa [W] using bound

theorem branching_budget {n out : Nat} {gs : List Gate} (clean : CleanL n gs)
    (outValid : out < n + gs.length)
    (everyNonoutputUsed : ∀ w < n + gs.length, w ≠ out → ∃ p, Reads gs p w)
    (branches : Finset Nat)
    (twoReaders : ∀ w ∈ branches, ∃ p q, p ≠ q ∧ Reads gs p w ∧ Reads gs q w) :
    branches.card + (n + gs.length - 1) + notGateCount gs ≤ 2 * gs.length := by
  let W := (operands gs).toFinset
  let required := (Finset.range (n + gs.length)).erase out
  have requiredUsed : required ⊆ W := by
    intro w inSet
    have spec := Finset.mem_erase.mp inSet
    obtain ⟨p, read⟩ := everyNonoutputUsed w (Finset.mem_range.mp spec.2) spec.1
    exact List.mem_toFinset.mpr (operand_mem_of_read read)
  have numRequired : required.card = n + gs.length - 1 := by
    change ((Finset.range (n + gs.length)).erase out).card = _
    rw [Finset.card_erase_of_mem (Finset.mem_range.mpr outValid), Finset.card_range]
  have twice : ∀ w ∈ branches, 2 ≤ (operands gs).count w := by
    intro w mem
    obtain ⟨p, q, different, pReads, qReads⟩ := twoReaders w mem
    exact two_readers_operand_count different pReads qReads
  have up := branch_card_add_wire_card_le_operands gs branches twice
  have used := Finset.card_le_card requiredUsed
  rw [numRequired] at used
  have total := operands_count_length gs (clean_gate_arity clean)
  change n + gs.length - 1 ≤ (operands gs).toFinset.card at used
  omega

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

open CircuitProof CircuitProof.Readers

open CutTrace

theorem branch_slots_of_read_edges {n : Nat} {gs : List Gate} {w : Fin (n + gs.length)}
    (fork : FirstBranchRoute.Branches (readEdge gs) w) :
    ∃ p q, p ≠ q ∧ Reads gs p w.val ∧ Reads gs q w.val := by
  obtain ⟨first, next, pRead, qRead, separate⟩ := fork
  obtain ⟨p, g, atP, src, ap⟩ := pRead
  obtain ⟨q, h, atQ, dst, aq⟩ := qRead
  refine ⟨p, q, ?_, ⟨g, atP, ap⟩, ⟨h, atQ, aq⟩⟩
  intro same
  subst q
  exact separate (Fin.ext (src.trans dst.symm))

noncomputable def circuitBranchWires {n : Nat} (gs : List Gate) : Finset (Fin (n + gs.length)) := by
  classical
  exact (Finset.univ).filter fun w => FirstBranchRoute.Branches (readEdge gs) w

theorem in_circuit_branches {n : Nat} {gs : List Gate} {w : Fin (n + gs.length)} :
    w ∈ circuitBranchWires gs ↔ FirstBranchRoute.Branches (readEdge gs) w := by
  classical
  simp [circuitBranchWires]

namespace CutTrace

open PEqualNP.CircuitLowerBounds CircuitProof

open Relation

theorem agree_on_input_ancestors {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (x y : Fin n → Bool) (w : Fin (n + gs.length))
    (agrees : ∀ i, ReflTransGen (readEdge gs) (inputWire gs i) w → x i = y i) :
    vl gs x w.val = vl gs y w.val := by
  revert agrees
  induction w using (measure (fun a : Fin (n + gs.length) => a.val)).wf.induction with
  | h w earlier =>
    intro agree
    by_cases input : w.val < n
    · let i : Fin n := ⟨w.val, input⟩
      have name : inputWire gs i = w := Fin.ext rfl
      have atInput : ReflTransGen (readEdge gs) (inputWire gs i) w := by
        simpa only [name] using (ReflTransGen.refl : ReflTransGen (readEdge gs) w w)
      have a := agree i atInput
      simpa only [vl_input gs x w.val input, vl_input gs y w.val input] using a
    · let p := w.val - n
      have pLt : p < gs.length := by have := w.isLt; dsimp [p]; omega
      have gateWire : w.val = n + p := by dsimp [p]; omega
      let g := gs[p]'pLt
      have atGate : gs[p]? = some g := List.getElem?_eq_getElem pLt
      rw [gateWire]
      apply vl_congr gs clean x y p g atGate
      intro a inGate
      have readBefore := (clean p g atGate).lt a inGate
      let wire : Fin (n + gs.length) := ⟨a, by have := w.isLt; omega⟩
      have read : readEdge gs wire w := ⟨p, g, atGate, gateWire, inGate⟩
      apply earlier wire (show wire.val < w.val by change a < w.val; omega)
      intro i path
      exact agree i (path.tail read)

end CutTrace

open PEqualNP.CircuitLowerBounds

open CircuitProof

open CutTrace Relation

open PEqualNP.CircuitLowerBounds CircuitProof

open CutTrace

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

open CircuitProof CircuitProof.Readers

open CutTrace InputBoundary

end PEqualNP.Outside.L_meta_14102.BranchData

namespace PEqualNP.Outside.L_meta_14102.Normal

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

open PEqualNP.Outside.L_meta_14102.Restriction.CircuitProof

open PEqualNP.Outside.L_meta_14102.CircuitHelpers

open PEqualNP.Outside.L_meta_14102.BranchData (notGateCount)

open PEqualNP.Outside.L_meta_14102.BranchData.CutTrace (readEdge
  agree_on_input_ancestors inputWire)

open Relation

private theorem simplify_choice {op : GateOp} {m : ℕ} {ins : List Stat} {g : Gate}
    (h : (simplify op m ins).1 = some g) : g.op = op ∧ g.inputs.Nodup := by
  cases op <;> simp only [simplify] at h
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c,l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at h
    split at h
    · simp at h
    next distinct =>
      simp at h
      subst g
      simp [distinct]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c,l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at h
    split at h
    · simp at h
    next distinct =>
      simp at h
      subst g
      simp [distinct]
  · rcases ins with _ | ⟨a,l⟩ <;> (try cases a) <;> simp [simpNot] at h
    subst g
    simp
  · simp at h
  · simp at h

private theorem count_append (a b : List Gate) :
    notGateCount (a ++ b) = notGateCount a + notGateCount b := by
  simp [notGateCount]

private theorem elim_properties (n : ℕ) (gs : List Gate) (init : Acc)
    (nodup : ∀ g ∈ init.2, g.inputs.Nodup) :
    (∀ g ∈ (elim n gs init).2, g.inputs.Nodup) ∧
      notGateCount (elim n gs init).2 ≤ notGateCount init.2 + notGateCount gs := by
  induction gs generalizing init with
  | nil => exact ⟨nodup, by simp [elim,notGateCount]⟩
  | cons g gs ih =>
    let op := (decision n init g).1
    have eqGates : (elimStep n init g).2 = init.2 ++ op.toList := rfl
    have emitted (g' : Gate) (h : g' ∈ op.toList) : g'.op = g.op ∧ g'.inputs.Nodup := by
      have eq : op = some g' := by simpa using h
      exact simplify_choice eq
    have cleanStep (a : Gate) (ha : a ∈ (elimStep n init g).2) : a.inputs.Nodup := by
      rw [eqGates,List.mem_append] at ha
      exact ha.elim (nodup a) (fun h => (emitted a h).2)
    have noExcess : notGateCount op.toList ≤ notGateCount [g] := by
      cases eq : op with
      | none => simp [notGateCount]
      | some a =>
        have aOp := (emitted a (by simp [eq])).1
        cases bit : PEqualNP.Outside.L_meta_14102.BranchData.CircuitProof.isNotGate g.op <;>
          simp [notGateCount,List.filter,aOp,bit]
    have step := ih (elimStep n init g) cleanStep
    change _ ∧ notGateCount (elim n gs (elimStep n init g)).2 ≤ _ at ⊢
    refine ⟨step.1, ?_⟩
    rw [eqGates,count_append] at step
    have append := count_append [g] gs
    change notGateCount (g :: gs) = notGateCount [g] + notGateCount gs at append
    rw [append]
    omega

def idInit (n : ℕ) : Acc := (List.ofFn (fun i : Fin n => Sum.inr i.val), [])

private theorem identity_inv {n : ℕ} (x : Fin n → Bool) :
    Inv n (List.ofFn x) (List.ofFn x) (idInit n) := by
  refine ⟨by simp [idInit],?_⟩
  intro i
  by_cases valid : i < n
  · have eq : (idInit n).1.getD i (Sum.inl false) = Sum.inr i := by
      unfold idInit
      rw [List.getD_eq_getElem _ _ (by simpa using valid),List.getElem_ofFn]
    rw [eq]
    simpa [idInit,Stat.Valid,Stat.val,wiresFrom] using valid
  · rw [List.getD_eq_default _ _ (by simp [idInit]; omega)]
    refine ⟨trivial,?_⟩
    simp [Stat.val,List.getD_eq_getElem?_getD,valid]

private theorem normalize_for_trace {n : ℕ} (C : Circuit) (hf : FanInTwo C)
    (nonconst : ∃ x y : Fin n → Bool, circuitFun n C x ≠ circuitFun n C y) :
    ∃ D : Circuit,
      D.gates = (elim n C.gates (idInit n)).2 ∧
      D.size ≤ C.size ∧ notGateCount D.gates ≤ notGateCount C.gates ∧
      PEqualNP.Outside.L_meta_14102.BranchData.CircuitProof.CleanL n D.gates ∧
      (∀ g ∈ D.gates, g.inputs.Nodup) ∧ D.output < n + D.size ∧
      ∀ x : Fin n → Bool, circuitFun n D x = circuitFun n C x := by
  let acc := elim n C.gates (idInit n)
  have proper (x : Fin n → Bool) := inv_elim n (List.ofFn x) (by simp) C.gates
    (List.ofFn x) (idInit n) hf (identity_inv x)
  let res := acc.1.getD C.output (Sum.inl false)
  have compatible (x : Fin n → Bool) :
      Stat.val (wiresFrom acc.2 (List.ofFn x)) res = circuitFun n C x :=
    (proper x).2 C.output |>.2
  cases outEq : res with
  | inl c =>
    obtain ⟨x,y,ne⟩ := nonconst
    have a := compatible x
    have b := compatible y
    rw [outEq] at a b
    exact (ne (a.symm.trans b)).elim
  | inr o =>
    have clean : CleanL n acc.2 :=
      clean_elim n (List.ofFn (fun _ : Fin n => false)) (by simp) C.gates
        _ _ hf (identity_inv _) (by simp [idInit,CleanL])
    have valid := (proper (fun _ => false)).2 C.output |>.1
    change Stat.Valid (n + acc.2.length) res at valid
    rw [outEq] at valid
    have properties := elim_properties n C.gates (idInit n) (by simp [idInit])
    refine ⟨⟨acc.2,o⟩,rfl,by simpa [acc,idInit,Circuit.size] using elim_len n C.gates (idInit n),
      by simpa [acc,idInit,notGateCount] using properties.2,clean,properties.1,valid,?_⟩
    intro x
    have result := compatible x
    rw [outEq] at result
    exact result

private theorem zero_removed (n : ℕ) (pre post : List Gate) :
    (elim n (pre ++ zeroGate :: post) (idInit n)).2.length ≤ pre.length + post.length := by
  rw [elim_append]
  let acc := elim n pre (idInit n)
  have preCount : acc.2.length ≤ pre.length := by
    simpa [acc,idInit] using elim_len n pre (idInit n)
  have postCount := elim_len n post (elimStep n acc zeroGate)
  have ep : (elimStep n acc zeroGate).2 = acc.2 := by simp [elimStep,zeroGate,simplify,simpOr]
  rw [ep] at postCount
  exact postCount.trans (Nat.add_le_add_right preCount _)

theorem normal_live {n : ℕ} {F : (Fin n → Bool) → Bool} (positive : 0 < n)
    (essential : ∀ i : Fin n, ∃ x y : Fin n → Bool, (∀ j ≠ i, x j = y j) ∧ F x ≠ F y)
    (C : Circuit) (hf : FanInTwo C) (he : ∀ x, circuitFun n C x = F x) :
    ∃ D : Circuit, ∃ valid : D.output < n + D.size,
      D.size ≤ C.size ∧ notGateCount D.gates ≤ notGateCount C.gates ∧
      PEqualNP.Outside.L_meta_14102.BranchData.CircuitProof.CleanL n D.gates ∧
      (∀ g ∈ D.gates, g.inputs.Nodup) ∧ (∀ x, circuitFun n D x = F x) ∧
      ∀ w : Fin (n + D.size), w ≠ ⟨D.output,valid⟩ → ∃ v, readEdge D.gates w v := by
  classical
  have nc : ∃ x y, F x ≠ F y := by
    obtain ⟨x,y,_,e⟩ := essential ⟨0,positive⟩
    exact ⟨x,y,e⟩
  have nonconst {D : Circuit} (agree : ∀ x, circuitFun n D x = F x) :
      ∃ x y, circuitFun n D x ≠ circuitFun n D y := by
    obtain ⟨x,y,diff⟩ := nc
    exact ⟨x,y,by simpa only [agree] using diff⟩
  let admissible (s : ℕ) : Prop :=
    ∃ D : Circuit, D.size = s ∧ notGateCount D.gates ≤ notGateCount C.gates ∧
      PEqualNP.Outside.L_meta_14102.BranchData.CircuitProof.CleanL n D.gates ∧
      (∀ g ∈ D.gates, g.inputs.Nodup) ∧ D.output < n + D.size ∧
      (∀ x, circuitFun n D x = F x)
  obtain ⟨D0,_,dsz,dn,dc,dd,dv,dcomp⟩ := normalize_for_trace C hf (nonconst he)
  have existsOne : ∃ s, admissible s := ⟨D0.size,D0,rfl,dn,dc,dd,dv,
    fun x => (dcomp x).trans (he x)⟩
  obtain ⟨D,dSize,dNots,dClean,dDistinct,valid,dEval⟩ := Nat.find_spec existsOne
  have allowedSize : D.size ≤ C.size := dSize ▸ ((Nat.find_min' existsOne (show admissible D0.size from
    ⟨D0,rfl,dn,dc,dd,dv,fun x => (dcomp x).trans (he x)⟩)).trans dsz)
  refine ⟨D,valid,allowedSize,dNots,dClean,dDistinct,dEval,?_⟩
  intro w away
  by_contra! unused
  let out : Fin (n + D.size) := ⟨D.output,valid⟩
  by_cases raw : w.val < n
  · let i : Fin n := ⟨w.val,raw⟩
    have atI : inputWire D.gates i = w := Fin.ext rfl
    obtain ⟨x,y,same,diff⟩ := essential i
    have closed : PEqualNP.Outside.L_meta_14102.BranchData.CircuitProof.vl D.gates x out.val =
        PEqualNP.Outside.L_meta_14102.BranchData.CircuitProof.vl D.gates y out.val := by
      apply agree_on_input_ancestors dClean
      intro j path
      by_cases off : j ≠ i
      · exact same _ off
      · have eq : j = i := by simpa using off
        subst j
        rw [atI] at path
        obtain ⟨v,go,_⟩ := path.cases_head.resolve_left away
        exact (unused v go).elim
    have one : circuitFun n D x = circuitFun n D y := closed
    exact diff (by simpa only [dEval] using one)
  · let p := w.val - n
    have pFound : n + p = w.val := by dsimp [p]; omega
    have pBound : p < D.gates.length := by
      have bound := w.isLt
      change w.val < n + D.gates.length at bound
      omega
    let g := D.gates[p]
    have atG : D.gates[p]? = some g := List.getElem?_eq_getElem pBound
    obtain ⟨pre,post,decomp,plen⟩ := split_gate atG
    have noRead : ∀ k ∈ post, w.val ∉ k.inputs := by
      intro k hk reads
      obtain ⟨j,atJ⟩ := List.mem_iff_getElem?.mp hk
      let j' := pre.length + 1 + j
      have atQ : D.gates[j']? = some k := by
        rw [decomp,List.getElem?_append_right (by dsimp [j']; omega)]
        rw [show j' - pre.length = j+1 by dsimp [j']; omega]
        exact atJ
      have bound := (List.getElem?_eq_some_iff.mp atQ).1
      exact unused ⟨n+j',by omega⟩ ⟨j',k,atQ,rfl,reads⟩
    let tweak : Circuit := ⟨pre ++ zeroGate :: post,D.output⟩
    have tweakFan : FanInTwo tweak := by
      have clean : CleanL n D.gates := dClean
      intro k hk
      change k ∈ pre ++ zeroGate :: post at hk
      rw [List.mem_append,List.mem_cons] at hk
      rcases hk with before | rfl | after
      · exact (clean_nok n D.gates clean k (by rw [decomp]; simp [before])).1
      · simp [zeroGate]
      · exact (clean_nok n D.gates clean k (by rw [decomp]; simp [after])).1
    have tweakEval (x : Fin n → Bool) : circuitFun n tweak x = F x := by
      rw [← dEval x]
      change (execBool (pre ++ zeroGate :: post) (List.ofFn x)).getD D.output false =
        (execBool D.gates (List.ofFn x)).getD D.output false
      rw [decomp,execBool_append,execBool_append,execBool_cons,execBool_cons]
      let base := execBool pre (List.ofFn x)
      have fullLen : base.length = w.val := by simp [base,execBool_length,plen,pFound]
      have initial : agreeExcept w.val (base ++ [gvBool base zeroGate]) (base ++ [gvBool base g]) := by
        rw [← fullLen]
        exact agreeExcept_append_here _ _ _
      have outUnequal : D.output ≠ w.val := fun eq => away (Fin.ext eq.symm)
      exact (agreeExcept_exec noRead initial).2 D.output outUnequal
    obtain ⟨D',dList,_,nots,clean,distinct,ok,correct⟩ :=
      normalize_for_trace tweak tweakFan (nonconst tweakEval)
    have improve : D'.size < D.size := by
      have cleanCount := zero_removed n pre post
      change D'.gates.length < D.gates.length
      rw [dList,decomp]
      change (elim n (pre ++ zeroGate :: post) (idInit n)).2.length < _
      simp only [List.length_append,List.length_cons]
      omega
    have tweakNot : notGateCount tweak.gates ≤ notGateCount D.gates := by
      change notGateCount (pre ++ zeroGate :: post) ≤ _
      rw [decomp,count_append,count_append]
      have c1 := count_append [zeroGate] post
      have c2 := count_append [g] post
      change notGateCount (zeroGate :: post) = _ at c1
      change notGateCount (g :: post) = _ at c2
      have c0 : notGateCount [zeroGate] = 0 := rfl
      rw [c1,c2,c0]
      omega
    have fits : admissible D'.size :=
      ⟨D',rfl,nots.trans (tweakNot.trans dNots),clean,distinct,ok,
        fun x => (correct x).trans (tweakEval x)⟩
    have lower := Nat.find_min' existsOne fits
    omega

end PEqualNP.Outside.L_meta_14102.Normal

namespace PEqualNP.Outside.L_meta_14102.Budget

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

open PEqualNP.Outside.L_meta_14102.BranchData

open CircuitProof CircuitProof.Readers CutTrace

theorem branching_budget_fin {n : ℕ} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length)) (live : ∀ w, w ≠ out → ∃ v, readEdge gs w v) :
    (circuitBranchWires (n := n) gs).card + (n + gs.length - 1) + notGateCount gs ≤
      2 * gs.length := by
  classical
  let branches := (circuitBranchWires (n := n) gs).image Fin.val
  have every (w : ℕ) (valid : w < n + gs.length) (different : w ≠ out.val) :
      ∃ p, Reads gs p w := by
    obtain ⟨v,p,g,atG,_,mem⟩ :=
      live ⟨w,valid⟩ (fun e => different (congrArg Fin.val e))
    exact ⟨p,g,atG,mem⟩
  have twice : ∀ w ∈ branches, ∃ p q, p ≠ q ∧ Reads gs p w ∧ Reads gs q w := by
    intro w m
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp m
    exact branch_slots_of_read_edges (in_circuit_branches.mp ha)
  have bound := branching_budget clean out.isLt every branches twice
  have count : branches.card = (circuitBranchWires (n := n) gs).card :=
    Finset.card_image_of_injective _ Fin.val_injective
  rw [count] at bound
  exact bound

theorem monotone_of_zero {n : ℕ} (D : Circuit) (clean : CleanL n D.gates)
    (zero : notGateCount D.gates = 0) :
    Monotone2 D := by
  intro g found
  obtain ⟨p,h⟩ := List.mem_iff_getElem?.mp found
  rcases clean p g h with ⟨op,_,_,_⟩ | ⟨op,_,_,_,_,args⟩
  · have mem : g ∈ D.gates.filter (fun a => isNotGate a.op) := by simp [found,op,isNotGate]
    have empty : D.gates.filter (fun a => isNotGate a.op) = [] := List.length_eq_zero_iff.mp zero
    rw [empty] at mem
    exact (List.not_mem_nil mem).elim
  · exact ⟨by simpa using op,by simp [args]⟩

end PEqualNP.Outside.L_meta_14102.Budget

namespace PEqualNP.Outside.L_meta_14102

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

open PEqualNP.Outside.L_meta_14102.BranchData

open CircuitProof CutTrace

theorem replacement {F : (Fin 8 → Bool) → Bool}
    (essential : ∀ i : Fin 8, ∃ x y : Fin 8 → Bool, (∀ j ≠ i, x j = y j) ∧ F x ≠ F y)
    (upper : ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 11 ∧ ∀ x, circuitFun 8 C x = F x)
    (_lower : ∀ {gs : List Gate} (clean : CleanL 8 gs) (out : Fin (8 + gs.length)),
      (∀ w, w ≠ out → ∃ v, readEdge gs w v) →
      (∀ w, (predecessors clean w).Nodup) →
      (∀ x, vl gs x out.val = F x) →
      3 ≤ (circuitBranchWires (n := 8) gs).card)
    (C : Circuit) (valid : FanInTwo C) (evaluates : ∀ x, circuitFun 8 C x = F x) :
    ∃ D : Circuit, Monotone2 D ∧ D.size ≤ C.size ∧ ∀ x, circuitFun 8 D x = F x := by
  by_cases large : 11 ≤ C.size
  · obtain ⟨D, legal, small, computes⟩ := upper
    exact ⟨D, legal, small.trans large, computes⟩
  obtain ⟨D, fits, size, _, clean, distinct, computes, live⟩ :=
    Normal.normal_live (by decide) essential C valid evaluates
  let out : Fin (8 + D.gates.length) := ⟨D.output, fits⟩
  have noDup (w : Fin (8 + D.gates.length)) : (predecessors clean w).Nodup := by
    by_cases internal : 8 ≤ w.val
    · apply List.Nodup.of_map Fin.val
      rw [predecessors_values clean w internal]
      exact distinct _ (List.getElem_mem (by have hk := w.isLt; omega))
    · simp [predecessors, internal]
  have zero : notGateCount D.gates = 0 := by
    have lower := _lower clean out live noDup computes
    have budget := Budget.branching_budget_fin clean out live
    change D.gates.length ≤ C.size at size
    omega
  exact ⟨D, Budget.monotone_of_zero D clean zero, size, computes⟩

end PEqualNP.Outside.L_meta_14102

namespace PEqualNP.Outside.L_meta_14102

open PEqualNP.CircuitLowerBounds

def edgeDatum : List ℕ := [0, 4, 0, 5, 1, 5, 0, 6, 1, 6, 5, 6, 0, 7, 2, 7, 3, 7]

def edgeValue (x : Fin 8 → Bool) : Bool :=
  decide (∃ i < edgeDatum.length / 2,
    (List.ofFn x).getD (edgeDatum.getD (2*i) 0) false = true ∧
      (List.ofFn x).getD (edgeDatum.getD (2*i+1) 0) false = true)

def edgesDirect (x : Fin 8 → Bool) : Bool :=
  (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 5) ||
    (x 0 && x 6) || (x 1 && x 6) || (x 5 && x 6) ||
    (x 0 && x 7) || (x 2 && x 7) || (x 3 && x 7)

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem exact_edge_table : ∀ x : Fin 8 → Bool, edgeValue x = edgesDirect x := by
  decide +kernel

def upper : List Gate := [
  ⟨.or,[0,1]⟩, ⟨.or,[5,6]⟩, ⟨.and,[5,6]⟩, ⟨.and,[8,9]⟩, ⟨.or,[10,11]⟩,
  ⟨.and,[0,4]⟩, ⟨.or,[12,13]⟩,
  ⟨.or,[2,3]⟩, ⟨.or,[0,15]⟩, ⟨.and,[7,16]⟩, ⟨.or,[14,17]⟩]

theorem upper_length : upper.length = 11 := rfl

theorem upper_ops : ∀ g ∈ upper, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [upper,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨by first | exact Or.inl rfl | exact Or.inr rfl, by decide⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem upper_runs : ∀ x : Fin 8 → Bool,
    Circuit.eval ⟨upper,18⟩ (List.ofFn x) = edgesDirect x := by
  decide +kernel

theorem upper_correct (x : Fin 8 → Bool) :
    Circuit.eval ⟨upper,18⟩ (List.ofFn x) = edgeValue x :=
  (upper_runs x).trans (exact_edge_table x).symm

def witnessNeighbour (i : Fin 8) : Fin 8 :=
  (![4,5,7,7,0,0,0,0] : Fin 8 → Fin 8) i

def witnessRow (i : Fin 8) (on : Bool) (j : Fin 8) : Bool :=
  decide (j = witnessNeighbour i) || (decide (j = i) && on)

theorem witness_same (i j : Fin 8) (ne : j ≠ i) :
    witnessRow i false j = witnessRow i true j := by
  simp [witnessRow,ne]

theorem witness_values : ∀ i : Fin 8,
    edgesDirect (witnessRow i false) = false ∧ edgesDirect (witnessRow i true) = true := by
  decide +kernel

theorem all_inputs_essential (i : Fin 8) :
    ∃ a b : Fin 8 → Bool, (∀ j, j ≠ i → a j = b j) ∧ edgeValue a ≠ edgeValue b := by
  refine ⟨witnessRow i false,witnessRow i true,witness_same i,?_⟩
  rw [exact_edge_table,exact_edge_table,(witness_values i).1,(witness_values i).2]
  decide

end PEqualNP.Outside.L_meta_14102

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

open PEqualNP.Outside.L_meta_14102.BranchData

namespace PEqualNP.Outside.L_meta_14102

open CircuitProof CutTrace

theorem staged (lower : ∀ {gs : List Gate} (clean : CleanL 8 gs) (out : Fin (8 + gs.length)),
    (∀ w, w ≠ out → ∃ v, readEdge gs w v) →
    (∀ w, (predecessors clean w).Nodup) →
    (∀ x, vl gs x out.val = edgesDirect x) →
    3 ≤ (circuitBranchWires (n := 8) gs).card) :
    (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 0, 5, 1, 5, 0, 6, 1, 6, 5, 6, 0, 7, 2, 7, 3, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 0, 6, 1, 6, 5, 6, 0, 7, 2, 7, 3, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 0, 6, 1, 6, 5, 6, 0, 7, 2, 7, 3, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 0, 5, 1, 5, 0, 6, 1, 6, 5, 6, 0, 7, 2, 7, 3, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 0, 6, 1, 6, 5, 6, 0, 7, 2, 7, 3, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 0, 6, 1, 6, 5, 6, 0, 7, 2, 7, 3, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) := by
  intro gates o legal _one computes
  let C : Circuit := ⟨gates, o⟩
  have fan : FanInTwo C := by
    intro g found
    obtain ⟨op,arity⟩ := legal g found
    exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using op, arity⟩
  have exactC (x : Fin 8 → Bool) : circuitFun 8 C x = edgesDirect x :=
    (computes x).trans (exact_edge_table x)
  have essential (i : Fin 8) : ∃ x y : Fin 8 → Bool,
      (∀ j ≠ i, x j = y j) ∧ edgesDirect x ≠ edgesDirect y := by
    obtain ⟨x,y,same,different⟩ := all_inputs_essential i
    refine ⟨x,y,same,?_⟩
    simpa only [exact_edge_table] using different
  have upperWitness : ∃ D : Circuit, Monotone2 D ∧ D.size ≤ 11 ∧
      ∀ x, circuitFun 8 D x = edgesDirect x := by
    refine ⟨⟨upper,18⟩, ?_, upper_length.le, fun x =>
      (upper_correct x).trans (exact_edge_table x)⟩
    intro g found
    obtain ⟨op,arity⟩ := upper_ops g found
    exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using op, arity⟩
  obtain ⟨D,mono,small,value⟩ :=
    replacement essential upperWitness lower C fan exactC
  refine ⟨D.gates, D.output, ?_, small, fun x => (value x).trans (exact_edge_table x).symm⟩
  intro g found
  obtain ⟨op,arity⟩ := mono g found
  exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using op, arity⟩

end PEqualNP.Outside.L_meta_14102

namespace PEqualNP.Outside.L_meta_14102.Branch

open PEqualNP.CircuitLowerBounds Relation

open PEqualNP.Outside.L_meta_14102.BranchData

open CircuitProof CutTrace PairFormula CutFormula CutIndependent InputBoundary

def table (x : Fin 8 → Bool) : Bool :=
  (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 5) ||
    (x 0 && x 6) || (x 1 && x 6) || (x 5 && x 6) ||
    (x 0 && x 7) || (x 2 && x 7) || (x 3 && x 7)

private abbrev conflict (i j : Fin 8) : Prop :=
  (i = 0 ∧ j = 5) ∨ (i = 0 ∧ j = 6) ∨ (i = 0 ∧ j = 7) ∨
    (i = 1 ∧ j = 5) ∨ (i = 1 ∧ j = 6) ∨ (i = 5 ∧ j = 6)

private def witnessBase (i j : Fin 8) (k : Fin 8) : Bool :=
  if j = 5 then decide (k = 6)
  else if j = 7 then decide (k = 2) || decide (k = 4)
  else if i = 5 then decide (k = 0) else decide (k = 5)

private theorem conflict_rows {i j : Fin 8} (h : conflict i j) :
    (∀ a b, table (pairInput i j (fun _ => false) a b) = (a && b)) ∧
    (∀ a b, table (pairInput i j (witnessBase i j) a b) = (a || b)) := by
  rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> decide

private theorem controls_pair {gs : List Gate} (clean : CleanL 8 gs)
    (out : Fin (8 + gs.length))
    (live : ∀ w : Fin (8 + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (cut : Fin (8 + gs.length)) (i j : Fin 8)
    (sameI : firstInputBoundary clean out live i = cut)
    (sameJ : firstInputBoundary clean out live j = cut) :
    cut = out ∨ ∀ k : Fin 8, (k = i ∨ k = j) →
      ¬ ReflTransGen (avoid (readEdge gs) cut) (inputWire gs k) out := by
  rcases firstInputGroup_controlled clean out live cut with stopped | blocked
  · exact Or.inl stopped
  · right
    intro k hk
    apply blocked k
    apply (mem_firstInputGroup clean out live cut k).mpr
    rcases hk with rfl | rfl
    · exact sameI
    · exact sameJ

private theorem different_boundaries {gs : List Gate} (clean : CleanL 8 gs)
    (out : Fin (8 + gs.length))
    (live : ∀ w : Fin (8 + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (distinct : ∀ w, (predecessors clean w).Nodup)
    (computes : ∀ x, vl gs x out.val = table x)
    (i j : Fin 8) (h : conflict i j) :
    firstInputBoundary clean out live i ≠ firstInputBoundary clean out live j := by
  intro same
  let cut := firstInputBoundary clean out live i
  have iCount := firstInputBoundary_occurrences_le_one clean out live distinct i i
  have jCount := firstInputBoundary_occurrences_le_one clean out live distinct i j
  rw [← same] at jCount
  have factor (base : Fin 8 → Bool) : ∃ outer : Bool → Bool, ∀ a b,
      outer (pairValue i j base (wireFormula i gs cut.val) a b) =
        table (pairInput i j base a b) := by
    obtain ⟨outer, houter⟩ := cut_factors clean cut out (fun k => k = i ∨ k = j) base
      (controls_pair clean out live cut i j rfl same.symm)
    refine ⟨outer, fun a b => ?_⟩
    have agree (k : Fin 8) (hk : ¬ (k = i ∨ k = j)) : pairInput i j base a b k = base k := by
      simp [pairInput, show k ≠ i from fun e => hk (Or.inl e),
        show k ≠ j from fun e => hk (Or.inr e)]
    unfold pairValue
    rw [wireFormula_eval i clean _ cut.val cut.isLt]
    exact (houter _ agree).trans (computes _)
  obtain ⟨outerA, hA⟩ := factor (fun _ => false)
  obtain ⟨outerO, hO⟩ := factor (witnessBase i j)
  exact fixed_pair_invariant i j (wireFormula i gs cut.val) iCount jCount _ _ outerA outerO
    (fun a b => (hA a b).trans ((conflict_rows h).1 a b))
    (fun a b => (hO a b).trans ((conflict_rows h).2 a b))

private theorem pair_pivot_bound {gs : List Gate} (clean : CleanL 8 gs)
    (out : Fin (8 + gs.length))
    (live : ∀ w : Fin (8 + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (computes : ∀ x, vl gs x out.val = table x)
    (i j k : Fin 8) (base : Bool → Fin 8 → Bool)
    (unchanged : ∀ v t, t ≠ k → base v t = base false t)
    (cofactor : ∀ v a b, table (pairInput i j (base v) a b) = (if v then a || b else a))
    (same : firstInputBoundary clean out live j = firstInputBoundary clean out live i) :
    firstInputBoundary clean out live k ≤ firstInputBoundary clean out live i := by
  let cut := firstInputBoundary clean out live i
  by_contra! later
  have terminal : FirstBranchRoute.Terminal (readEdge gs) out cut :=
    FirstBranchRoute.first_stops (readEdge gs) out (read_order clean) live (inputWire gs i)
  have notAncestor : ¬ ReflTransGen (readEdge gs) (inputWire gs k) cut := by
    intro path
    exact (not_lt_of_ge (FirstBranchRoute.ancestor_first_le (readEdge gs) out
      (read_order clean) live path terminal)) later
  let code (a b : Bool) := vl gs (pairInput i j (base false) a b) cut.val
  have stable (v a b : Bool) : vl gs (pairInput i j (base v) a b) cut.val = code a b := by
    apply agree_on_input_ancestors clean
    intro t path
    have other : t ≠ k := by
      rintro rfl
      exact notAncestor path
    simp [pairInput, unchanged v t other]
  have factor (v : Bool) : ∃ outer : Bool → Bool, ∀ a b,
      outer (code a b) = (if v then a || b else a) := by
    obtain ⟨outer, h⟩ := cut_factors clean cut out (fun t => t = i ∨ t = j) (base v)
      (controls_pair clean out live cut i j rfl same)
    refine ⟨outer, fun a b => ?_⟩
    rw [← stable v a b, ← cofactor v a b, ← computes]
    apply h
    intro t neither
    simp [pairInput, show t ≠ i from fun eq => neither (Or.inl eq),
      show t ≠ j from fun eq => neither (Or.inr eq)]
  obtain ⟨asZero, hz⟩ := factor false
  obtain ⟨asOne, ho⟩ := factor true
  have diff1 : code false false ≠ code false true := by
    intro eq
    have h := congrArg asOne eq
    rw [ho, ho] at h
    cases h
  have diff2 : code false false ≠ code true false := by
    intro eq
    have h := congrArg asZero eq
    rw [hz, hz] at h
    cases h
  have diff3 : code false true ≠ code true false := by
    intro eq
    have h := congrArg asZero eq
    rw [hz, hz] at h
    cases h
  cases e0 : code false false <;> cases e1 : code false true <;> cases e2 : code true false <;>
    simp_all

private def pivotBase (k leaf : Fin 8) (v : Bool) (t : Fin 8) : Bool :=
  if t = k then v else decide (t = leaf)

private theorem pivot_fixed (k leaf : Fin 8) (v : Bool) (t : Fin 8) (h : t ≠ k) :
    pivotBase k leaf v t = pivotBase k leaf false t := by simp [pivotBase,h]

private theorem four_boundaries {gs : List Gate} (clean : CleanL 8 gs)
    (out : Fin (8 + gs.length))
    (live : ∀ w : Fin (8 + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (a b c d : Fin 8)
    (hab : firstInputBoundary clean out live a ≠ firstInputBoundary clean out live b)
    (hac : firstInputBoundary clean out live a ≠ firstInputBoundary clean out live c)
    (had : firstInputBoundary clean out live a ≠ firstInputBoundary clean out live d)
    (hbc : firstInputBoundary clean out live b ≠ firstInputBoundary clean out live c)
    (hbd : firstInputBoundary clean out live b ≠ firstInputBoundary clean out live d)
    (hcd : firstInputBoundary clean out live c ≠ firstInputBoundary clean out live d) :
    3 ≤ (circuitBranchWires (n := 8) gs).card := by
  classical
  let label := firstInputBoundary clean out live
  let branches := circuitBranchWires (n := 8) gs
  let used : Finset (Fin (8 + gs.length)) := {label a, label b, label c, label d}
  have notA : label a ∉ ({label b, label c, label d} : Finset _) := by
    simp [label, hab, hac, had]
  have notB : label b ∉ ({label c, label d} : Finset _) := by
    simp [label, hbc, hbd]
  have notC : label c ∉ ({label d} : Finset _) := by
    simp [label, hcd]
  have usedCount : used.card = 4 := by
    simp only [used, Finset.card_insert_of_notMem notA, Finset.card_insert_of_notMem notB,
      Finset.card_insert_of_notMem notC, Finset.card_singleton]
  have every (i : Fin 8) : label i ∈ insert out branches := by
    rcases FirstBranchRoute.first_stops (readEdge gs) out (read_order clean) live (inputWire gs i) with
      equal | branch
    · exact Finset.mem_insert.mpr (Or.inl equal)
    · exact Finset.mem_insert_of_mem (in_circuit_branches.mpr branch)
  have included : used ⊆ insert out branches := by
    intro w hw
    simp only [used,Finset.mem_insert,Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl | rfl
    · exact every a
    · exact every b
    · exact every c
    · exact every d
  have lower := Finset.card_le_card included
  rw [usedCount] at lower
  have upper := Finset.card_insert_le out branches
  change 3 ≤ branches.card
  omega

theorem branch_card_ge_three {gs : List Gate} (clean : CleanL 8 gs)
    (out : Fin (8 + gs.length))
    (live : ∀ w : Fin (8 + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (distinct : ∀ w, (predecessors clean w).Nodup)
    (computes : ∀ x, vl gs x out.val = table x) :
    3 ≤ (circuitBranchWires (n := 8) gs).card := by
  let label := firstInputBoundary clean out live
  have sep (i j : Fin 8) (h : conflict i j) :
      label i ≠ label j := different_boundaries clean out live distinct computes i j h
  have h05 : label 0 ≠ label 5 := sep 0 5 (by decide)
  have h06 : label 0 ≠ label 6 := sep 0 6 (by decide)
  have h07 : label 0 ≠ label 7 := sep 0 7 (by decide)
  have h15 : label 1 ≠ label 5 := sep 1 5 (by decide)
  have h16 : label 1 ≠ label 6 := sep 1 6 (by decide)
  have h56 : label 5 ≠ label 6 := sep 5 6 (by decide)
  by_cases equal : label 1 = label 0
  · have h50 : label 5 < label 0 := lt_of_le_of_ne
      (pair_pivot_bound clean out live computes 0 1 5 (pivotBase 5 4)
        (pivot_fixed 5 4) (by decide) equal) h05.symm
    have h60 : label 6 < label 0 := lt_of_le_of_ne
      (pair_pivot_bound clean out live computes 0 1 6 (pivotBase 6 4)
        (pivot_fixed 6 4) (by decide) equal) h06.symm
    have h57 : label 5 ≠ label 7 := by
      intro h
      have h07' : label 0 ≤ label 7 :=
        pair_pivot_bound clean out live computes 7 5 0 (pivotBase 0 2)
          (pivot_fixed 0 2) (by decide) h
      exact (not_le_of_gt h50) (h.symm ▸ h07')
    have h67 : label 6 ≠ label 7 := by
      intro h
      have h07' : label 0 ≤ label 7 :=
        pair_pivot_bound clean out live computes 7 6 0 (pivotBase 0 2)
          (pivot_fixed 0 2) (by decide) h
      exact (not_le_of_gt h60) (h.symm ▸ h07')
    exact four_boundaries clean out live 0 5 6 7 h05 h06 h07 h56 h57 h67
  · exact four_boundaries clean out live 0 1 5 6 (fun h => equal h.symm) h05 h06 h15 h16 h56

end PEqualNP.Outside.L_meta_14102.Branch

open PEqualNP.Outside.L_meta_14102

theorem PEqualNP.Outside.L_meta_14102 :
    (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 0, 5, 1, 5, 0, 6, 1, 6, 5, 6, 0, 7, 2, 7, 3, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 0, 6, 1, 6, 5, 6, 0, 7, 2, 7, 3, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 0, 6, 1, 6, 5, 6, 0, 7, 2, 7, 3, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 0, 5, 1, 5, 0, 6, 1, 6, 5, 6, 0, 7, 2, 7, 3, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 0, 6, 1, 6, 5, 6, 0, 7, 2, 7, 3, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 0, 6, 1, 6, 5, 6, 0, 7, 2, 7, 3, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) :=
  staged (fun clean out live distinct agrees =>
    Branch.branch_card_ge_three clean out live distinct agrees)
