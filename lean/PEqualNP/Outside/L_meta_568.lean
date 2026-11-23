import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace Gap568

-- The constant-propagation pass follows L_meta_468.

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

private lemma wiresFrom_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [wiresFrom_cons, ih _ (by simp; omega)]
    exact getD_snoc_lt _ _ _ _ hi

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
  · have : op = GateOp.and := h
    subst this
    exact ⟨⟨Or.inl rfl, hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.or := h
    subst this
    exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.not := h
    subst this
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
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

private def simpOr (m : ℕ) : List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ)
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
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
    subst hg; simp [OkGate]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg; simp [OkGate]
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg
    subst hg; simp [OkGate]
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
        | inr j => simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
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
        | inr j => simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
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
    rw [elimPass_cons, List.length_cons]
    have h1 := ih (elimStep m acc g)
    have h2 : (elimStep m acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      have := toList_opt_len_le (simplifyGate g.op (m + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
      omega
    omega

private lemma elimPass_len_lt (m k : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (hok : ∀ g ∈ gs, NOkGate g) (hk : k < acc.1.length)
    (hc : ∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c)
    (hex : ∃ g ∈ gs, k ∈ g.inputs) :
    (elimPass m gs acc).2.length + 1 ≤ acc.2.length + gs.length := by
  induction gs generalizing acc with
  | nil => obtain ⟨g, hg, _⟩ := hex; simp at hg
  | cons g gs ih =>
    rw [elimPass_cons, List.length_cons]
    by_cases hkg : k ∈ g.inputs
    · obtain ⟨c, hc⟩ := hc
      have hnok := hok g List.mem_cons_self
      have hnone : (simplifyGate g.op (m + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        apply simplifyGate_none_of_const
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep m acc g).2.length = acc.2.length := by
        simp only [elimStep, hnone, Option.toList_none, List.append_nil]
      have := elimPass_len m gs (elimStep m acc g)
      omega
    · have hex' : ∃ g' ∈ gs, k ∈ g'.inputs := by
        obtain ⟨g', hg', hk'⟩ := hex
        rcases List.mem_cons.1 hg' with rfl | h
        · exact absurd hk' hkg
        · exact ⟨g', h, hk'⟩
      have h1 := ih (elimStep m acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (by simp [elimStep]; omega)
        (by
          obtain ⟨c, hc⟩ := hc
          exact ⟨c, by simp only [elimStep]; rw [getD_snoc_lt _ _ _ _ hk]; exact hc⟩)
        hex'
      have h2 : (elimStep m acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_opt_len_le (simplifyGate g.op (m + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      omega

private lemma elimPass_len_two (m k : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (hok : ∀ g ∈ gs, NOkGate g) (hk : k < acc.1.length)
    (hc : ∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c)
    (htwo : 2 ≤ (gs.filter (fun g => decide (k ∈ g.inputs))).length) :
    (elimPass m gs acc).2.length + 2 ≤ acc.2.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp at htwo
  | cons g gs ih =>
    rw [elimPass_cons, List.length_cons]
    by_cases hkg : k ∈ g.inputs
    · obtain ⟨c, hc⟩ := hc
      have hnok := hok g List.mem_cons_self
      have hnone : (simplifyGate g.op (m + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        apply simplifyGate_none_of_const
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep m acc g).2.length = acc.2.length := by
        simp only [elimStep, hnone, Option.toList_none, List.append_nil]
      have hfilt : 1 ≤ (gs.filter (fun g => decide (k ∈ g.inputs))).length := by
        simp [hkg] at htwo
        omega
      have hex' : ∃ g' ∈ gs, k ∈ g'.inputs := by
        have hne : gs.filter (fun g => decide (k ∈ g.inputs)) ≠ [] := by
          intro hnil; rw [hnil] at hfilt; simp at hfilt
        obtain ⟨g', hg'⟩ := List.exists_mem_of_ne_nil _ hne
        rw [List.mem_filter] at hg'
        exact ⟨g', hg'.1, of_decide_eq_true hg'.2⟩
      have h1 := elimPass_len_lt m k gs (elimStep m acc g)
        (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (by simp [elimStep]; omega)
        ⟨c, by simp only [elimStep]; rw [getD_snoc_lt _ _ _ _ hk]; exact hc⟩
        hex'
      omega
    · have htwo' : 2 ≤ (gs.filter (fun g => decide (k ∈ g.inputs))).length := by
        simpa [hkg] using htwo
      have h1 := ih (elimStep m acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (by simp [elimStep]; omega)
        (by
          obtain ⟨c, hc⟩ := hc
          exact ⟨c, by simp only [elimStep]; rw [getD_snoc_lt _ _ _ _ hk]; exact hc⟩)
        htwo'
      have h2 : (elimStep m acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_opt_len_le (simplifyGate g.op (m + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      omega

private def ElimInv (m : ℕ) (w_in w_old : List Bool)
    (acc : List (Bool ⊕ ℕ) × List Gate) : Prop :=
  w_in.length = m ∧
  acc.1.length = w_old.length ∧
  ∀ i : ℕ,
    statValid (m + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
    statVal (wiresFrom acc.2 w_in) (acc.1.getD i (Sum.inl false)) = w_old.getD i false

private lemma elimInv_step (m : ℕ) (w_in w_old : List Bool)
    (acc : List (Bool ⊕ ℕ) × List Gate) (g : Gate) (hok : OkGate g)
    (hinv : ElimInv m w_in w_old acc) :
    ElimInv m w_in (w_old ++ [g.op.eval (g.inputs.map fun i => w_old.getD i false)])
      (elimStep m acc g) := by
  obtain ⟨hwin, hlen, hi⟩ := hinv
  set w_new := wiresFrom acc.2 w_in with hw_new
  have hw_len : w_new.length = m + acc.2.length := by
    rw [hw_new, wiresFrom_length, hwin]
  set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
  have hins_len : ins.length ≤ 2 := by simp [hins]; exact hok.2
  have hins_val : ∀ s ∈ ins, statValid w_new.length s := by
    intro s hs
    obtain ⟨idx, _, rfl⟩ := List.mem_map.1 hs
    rw [hw_len]
    exact (hi idx).1
  have hsound := simplifyGate_sound g.op hok.1 w_new ins hins_len hins_val
  rw [hw_len] at hsound
  refine ⟨hwin, by simp [elimStep, hlen], ?_⟩
  intro i
  simp only [elimStep]
  by_cases hieq : i = acc.1.length
  · rw [getD_snoc_eq _ _ _ _ hieq, getD_snoc_eq _ _ _ _ (by omega)]
    refine ⟨?_, ?_⟩
    · rw [List.length_append, ← Nat.add_assoc]
      exact hsound.1
    · rw [wiresFrom_append, ← hw_new, hsound.2]
      congr 1
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro idx _
      exact (hi idx).2
  · rw [getD_snoc_ne _ _ _ _ hieq, getD_snoc_ne _ _ _ _ (by omega)]
    have ⟨hv, hval⟩ := hi i
    refine ⟨?_, ?_⟩
    · cases hst : acc.1.getD i (Sum.inl false) with
      | inl c => trivial
      | inr j =>
        rw [hst] at hv
        simp only [statValid, List.length_append] at hv ⊢
        omega
    · cases hst : acc.1.getD i (Sum.inl false) with
      | inl c =>
        rw [hst] at hval
        exact hval
      | inr j =>
        rw [hst] at hv hval
        simp only [statValid] at hv
        simp only [statVal] at hval ⊢
        rw [wiresFrom_append, ← hw_new, wiresFrom_getD_lt _ _ _ (by omega)]
        exact hval

private lemma elimInv_pass (m : ℕ) (w_in : List Bool) (gs : List Gate)
    (w_old : List Bool) (acc : List (Bool ⊕ ℕ) × List Gate)
    (hok : ∀ g ∈ gs, OkGate g) (hinv : ElimInv m w_in w_old acc) :
    ElimInv m w_in (wiresFrom gs w_old) (elimPass m gs acc) := by
  induction gs generalizing w_old acc with
  | nil => exact hinv
  | cons g gs ih =>
    rw [wiresFrom_cons, elimPass_cons]
    exact ih _ _ (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (elimInv_step m w_in w_old acc g (hok g List.mem_cons_self) hinv)

private lemma ofFn_getD_lt {α : Type*} {m : ℕ} (f : Fin m → α) (d : α) (i : ℕ) (hi : i < m) :
    (List.ofFn f).getD i d = f ⟨i, hi⟩ := by
  rw [List.getD_eq_getElem _ _ (by simp; exact hi), List.getElem_ofFn]

private def initVar (m : ℕ) (v : Fin m) (b : Bool) : List (Bool ⊕ ℕ) :=
  List.ofFn fun i : Fin m => if i = v then Sum.inl b else Sum.inr (i : ℕ)

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

private def finishGate (w : ℕ) : Bool ⊕ ℕ → Gate
  | .inl true => ⟨.and, []⟩
  | .inl false => ⟨.or, [w, w]⟩
  | .inr j => ⟨.or, [w, j]⟩

private lemma finishGate_ok (w : ℕ) (out : Bool ⊕ ℕ) : OkGate (finishGate w out) := by
  rcases out with b|j
  · cases b <;> simp [finishGate, OkGate]
  · simp [finishGate, OkGate]

private lemma finishGate_val (w : ℕ) (out : Bool ⊕ ℕ) (u : List Bool) :
    (finishGate w out).op.eval ((finishGate w out).inputs.map fun i => u.getD i false) =
      (u.getD w false || statVal u out) := by
  rcases out with b|j
  · cases b <;> simp [finishGate, GateOp.eval, statVal]
  · simp [finishGate, GateOp.eval, statVal]

private lemma false_input_inv {m : ℕ} (u : List Bool) (v : Fin m)
    (hlen : u.length = m) (hfalse : u.getD v.val false = false) :
    ElimInv m u u (initVar m v false, []) := by
  let y := fun i : Fin m => u.getD i.val false
  have hy : List.ofFn y = u := by
    apply List.ext_getElem
    · simp [hlen]
    · intro i hi hj
      simp only [List.getElem_ofFn, y, List.getD_eq_getElem _ _ hj]
  have hfix : Function.update y v false = y := by
    funext i
    by_cases he : i = v
    · subst i; rw [Function.update_self]; exact hfalse.symm
    · rw [Function.update_of_ne he]
  have h := elimInv_initVar m v false y
  rwa [hfix,hy] at h

private lemma safe_wire_savings {n w o : ℕ} (pre post : List Gate)
    (hmin : IsMinimalCircuit n ⟨pre ++ post, o⟩) (hw : w < n + pre.length)
    (hsafe : ∀ x : Fin n → Bool, (wiresFrom pre (List.ofFn x)).getD w false = true →
      (wiresFrom (pre ++ post) (List.ofFn x)).getD o false = true) :
    post.length ≤ (elimPass (n + pre.length) (post.map normGate)
      (initVar (n + pre.length) ⟨w,hw⟩ false, [])).2.length + 1 := by
  let m := n + pre.length
  let v : Fin m := ⟨w,hw⟩
  let gs := post.map normGate
  have hgood : ∀ g ∈ gs, NOkGate g := by
    intro g hg
    obtain ⟨g0,hg0,rfl⟩ := List.mem_map.mp hg
    exact normGate_nok g0 (hmin.1 g0 (List.mem_append_right _ hg0))
  let acc := elimPass m gs (initVar m v false, [])
  let out := acc.1.getD o (.inl false)
  let D : Circuit := ⟨(pre ++ acc.2) ++ [finishGate w out], m + acc.2.length⟩
  have hd : FanInTwo D := by
    intro g hg
    change g ∈ (pre ++ acc.2) ++ [finishGate w out] at hg
    rcases List.mem_append.mp hg with hg|hg
    · rcases List.mem_append.mp hg with hg|hg
      · exact hmin.1 g (List.mem_append_left _ hg)
      · exact elimPass_ok m gs _ (by simp) g hg
    · obtain rfl := List.mem_singleton.mp hg
      exact finishGate_ok w out
  have heq : circuitFun n D = circuitFun n ⟨pre ++ post,o⟩ := by
    funext x
    let u := wiresFrom pre (List.ofFn x)
    have hu : u.length = m := by simp [u, m, wiresFrom_length]
    have hlen : m + acc.2.length = (wiresFrom acc.2 u).length := by simp [wiresFrom_length,hu]
    change (wiresFrom ((pre ++ acc.2) ++ [finishGate w out]) _).getD _ false =
      (wiresFrom (pre ++ post) (List.ofFn x)).getD o false
    rw [wiresFrom_append, wiresFrom_append, wiresFrom_cons, wiresFrom_nil]
    change ((wiresFrom acc.2 u) ++ [_]).getD _ false = _
    rw [getD_snoc_eq _ _ _ _ hlen, finishGate_val, wiresFrom_getD_lt acc.2 u w (hu.symm ▸ hw)]
    cases h : u.getD w false with
    | true => rw [hsafe x h]; rfl
    | false =>
      simp only [Bool.false_or]
      have hi := elimInv_pass m u gs u (initVar m v false, []) (fun g hg => (hgood g hg).1)
        (false_input_inv u v hu h)
      have hv := (hi.2.2 o).2
      rw [show gs = post.map normGate from rfl, wiresFrom_norm] at hv
      rw [wiresFrom_append]
      exact hv
  have hle := hmin.2 D hd heq
  change (pre ++ post).length ≤ ((pre ++ acc.2) ++ [_]).length at hle
  simp only [List.length_append, List.length_singleton] at hle
  change post.length ≤ acc.2.length + 1
  omega

private lemma safe_wire_shortcut {n w o : ℕ} (pre post : List Gate)
    (hmin : IsMinimalCircuit n ⟨pre ++ post, o⟩) (hw : w < n + pre.length)
    (hsafe : ∀ x : Fin n → Bool, (wiresFrom pre (List.ofFn x)).getD w false = true →
      (wiresFrom (pre ++ post) (List.ofFn x)).getD o false = true) :
    (post.map normGate |>.filter fun g => decide (w ∈ g.inputs)).length ≤ 1 := by
  by_contra! hmuch
  let m := n + pre.length
  let v : Fin m := ⟨w,hw⟩
  let gs := post.map normGate
  have hgood : ∀ g ∈ gs, NOkGate g := by
    intro g hg
    obtain ⟨g0,hg0,rfl⟩ := List.mem_map.mp hg
    exact normGate_nok g0 (hmin.1 g0 (List.mem_append_right _ hg0))
  let acc := elimPass m gs (initVar m v false, [])
  have saved : acc.2.length + 2 ≤ post.length := by
    have hcut := elimPass_len_two m w gs (initVar m v false, []) hgood
      (by simpa [initVar] using hw)
      ⟨false, by rw [initVar, ofFn_getD_lt _ _ _ hw]; simp [v]⟩ hmuch
    simpa [acc, gs] using hcut
  have bound := safe_wire_savings pre post hmin hw hsafe
  change post.length ≤ acc.2.length + 1 at bound
  omega

private lemma safe_reader_op {n w o : ℕ} (pre post a b : List Gate) (g : Gate)
    (hmin : IsMinimalCircuit n ⟨pre ++ post, o⟩) (hw : w < n + pre.length)
    (hsafe : ∀ x : Fin n → Bool, (wiresFrom pre (List.ofFn x)).getD w false = true →
      (wiresFrom (pre ++ post) (List.ofFn x)).getD o false = true)
    (hsplit : post.map normGate = a ++ g :: b) (hread : w ∈ g.inputs)
    (hnext : ∃ t ∈ b, n + pre.length + a.length ∈ t.inputs) : g.op = GateOp.or := by
  by_contra hn
  let m := n + pre.length
  let v : Fin m := ⟨w,hw⟩
  let init := (initVar m v false, ([] : List Gate))
  let first := elimPass m a init
  let middle := elimStep m first g
  have good : ∀ t ∈ a ++ g :: b, NOkGate t := by
    rw [← hsplit]
    intro t ht
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp ht
    exact normGate_nok z (hmin.1 z (List.mem_append_right _ hz))
  have hg := good g (by simp)
  have hprelen : first.1.length = m + a.length := by simp [first,elimPass_fst_len,init,initVar]
  have hinter : first.1.getD w (.inl false) = .inl false := by
    unfold first
    rw [elimPass_getD_lt m w _ a init (by simpa [init,initVar] using hw)]
    simp only [init, initVar, ofFn_getD_lt _ _ _ hw]
    simp [v]
  have hmem : Sum.inl false ∈ (g.inputs.map fun i => first.1.getD i (Sum.inl false)) :=
    List.mem_map.mpr ⟨w, hread, hinter⟩
  have hconst : ∃ c : Bool, simplifyGate g.op (m + first.2.length)
      (g.inputs.map fun i => first.1.getD i (.inl false)) = (none,.inl c) := by
    rcases hg.1.1 with h | h | h
    · have h' : g.op = GateOp.and := h
      rw [h']
      exact ⟨false,simplifyGate_and_false _ _ (by simpa using hg.1.2) hmem⟩
    · exact False.elim (hn h)
    · have h' : g.op = GateOp.not := h
      have hlen := hg.2 h'
      have hs : g.inputs = [w] := by
        rcases he : g.inputs with _ | ⟨x, _ | ⟨y,ys⟩⟩
        · simp [he] at hread
        · rw [he] at hread
          simp at hread
          simp [hread]
        · simp [he] at hlen
      rw [h',hs,List.map_singleton,hinter]
      exact ⟨true,simplifyGate_not_const _ false⟩
  obtain ⟨c,hc⟩ := hconst
  have hlen : middle.2.length = first.2.length := by simp only [middle,elimStep,hc]; simp
  have hval : middle.1.getD (m + a.length) (.inl false) = .inl c := by
    simp only [middle,elimStep,hc]
    exact getD_snoc_eq _ _ _ _ hprelen.symm
  have h1 := elimPass_len m a init
  change first.2.length ≤ 0 + a.length at h1
  have h2 := elimPass_len_lt m (m + a.length) b middle
    (fun t ht => good t (by simp [ht]))
    (by simp [middle,elimStep,hprelen]) ⟨c,hval⟩ hnext
  have h3 := safe_wire_savings pre post hmin hw hsafe
  change post.length ≤ (elimPass m (post.map normGate) init).2.length + 1 at h3
  rw [hsplit,elimPass_append,elimPass_cons] at h3
  change post.length ≤ (elimPass m b middle).2.length + 1 at h3
  have h4 := congrArg List.length hsplit
  simp only [List.length_map,List.length_append,List.length_cons] at h4
  omega


private def Forces (n w o : ℕ) (pre post : List Gate) : Prop :=
  ∀ x : Fin n → Bool, (wiresFrom post ((wiresFrom pre (List.ofFn x)).set w true)).getD o false = true

private lemma forcing_safe {n w o : ℕ} (pre post : List Gate) (hw : w < n + pre.length)
    (h : Forces n w o pre post) (x : Fin n → Bool)
    (ht : (wiresFrom pre (List.ofFn x)).getD w false = true) :
    (wiresFrom (pre ++ post) (List.ofFn x)).getD o false = true := by
  let u := wiresFrom pre (List.ofFn x)
  have hw' : w < u.length := by simpa [u,wiresFrom_length] using hw
  change u.getD w false = true at ht
  rw [List.getD_eq_getElem _ _ hw'] at ht
  have hh := h x
  change (wiresFrom post (u.set w true)).getD o false = true at hh
  have hset : u.set w true = u := by rw [← ht,List.set_getElem_self hw']
  rw [hset] at hh
  exact wiresFrom_append pre post (List.ofFn x) ▸ hh

private lemma wiresFrom_set_unread (gs : List Gate) (u : List Bool) (w : ℕ)
    (hw : w < u.length) (hr : ∀ g ∈ gs, w ∉ g.inputs) :
    wiresFrom gs (u.set w true) = (wiresFrom gs u).set w true := by
  induction gs generalizing u with
  | nil => rfl
  | cons g gs ih =>
    rw [wiresFrom_cons, wiresFrom_cons]
    have hval : g.inputs.map (fun i => (u.set w true).getD i false) =
        g.inputs.map (fun i => u.getD i false) := by
      apply List.map_congr_left
      intro i hi
      have hne : w ≠ i := fun he => hr g (by simp) (he ▸ hi)
      simp [List.getD,List.getElem?_set_ne hne]
    rw [hval, ← List.set_append_left _ _ hw, ih _ (by simp; omega)]
    exact fun a ha => hr a (by simp [ha])

private lemma forcing_input (n o : ℕ) (gs : List Gate) (H : (Fin n → Bool) → Bool)
    (hf : ∀ x : Fin (n+1) → Bool, (wiresFrom gs (List.ofFn x)).getD o false =
      (x (Fin.last n) || H (fun i => x i.castSucc))) :
    Forces (n+1) n o [] gs := by
  intro x
  let x' := Function.update x (Fin.last n) true
  have hx : (List.ofFn x).set n true = List.ofFn x' := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      by_cases he : n = i
      · subst i
        rw [List.getElem_set_self hi,List.getElem_ofFn]
        exact (Function.update_self (Fin.last n) true x).symm
      · simp only [List.getElem_set_ne he,List.getElem_ofFn]
        apply Eq.symm
        apply Function.update_of_ne
        intro hh
        have := congrArg Fin.val hh
        exact he this.symm
  change (wiresFrom gs ((List.ofFn x).set n true)).getD o false = true
  rw [hx,hf]
  simp [x']

private lemma forcing_or_step {n w o : ℕ} (pre a b : List Gate) (g : Gate)
    (hw : w < n + pre.length) (hne : w ≠ o)
    (ha : ∀ t ∈ a, w ∉ t.inputs) (hb : ∀ t ∈ b, w ∉ t.inputs)
    (hop : g.op = GateOp.or) (hread : w ∈ g.inputs)
    (h : Forces n w o pre (a ++ g :: b)) :
    Forces n (n + pre.length + a.length) o (pre ++ a ++ [g]) b := by
  intro x
  let u := wiresFrom pre (List.ofFn x)
  let v := wiresFrom a u
  have huw : w < u.length := by simpa [u,wiresFrom_length] using hw
  have hvlen : v.length = n + pre.length + a.length := by simp [v,u,wiresFrom_length]
  have hvw : w < v.length := by omega
  have hvset : g.op.eval (g.inputs.map fun i => (v.set w true).getD i false) = true := by
    rw [hop]
    change (g.inputs.map fun i => (v.set w true).getD i false).any id = true
    apply List.any_eq_true.mpr
    exact ⟨true,List.mem_map.mpr ⟨w,hread,by simp [List.getD,hvw]⟩,rfl⟩
  have h1 := h x
  change (wiresFrom (a ++ g :: b) (u.set w true)).getD o false = true at h1
  rw [wiresFrom_append,wiresFrom_set_unread a u w huw ha] at h1
  change (wiresFrom b (v.set w true ++ [_])).getD o false = true at h1
  rw [hvset, ← List.set_append_left _ _ hvw,
      wiresFrom_set_unread b (v ++ [true]) w (by simp; omega) hb] at h1
  simp only [List.getD,List.getElem?_set_ne hne] at h1
  change (wiresFrom b ((wiresFrom ((pre ++ a) ++ [g]) (List.ofFn x)).set _ true)).getD o false = true
  rw [wiresFrom_append,wiresFrom_append]
  change (wiresFrom b ((v ++ [_]).set _ true)).getD o false = true
  rw [← hvlen,List.set_append_right _ _ (by omega)]
  simpa using h1


private lemma forced_nonor_alias (g : Gate) (u : List Bool) (w : ℕ)
    (hg : NOkGate g) (hw : w < u.length) (hr : w ∈ g.inputs) (ho : g.op ≠ GateOp.or)
    (ht : g.op.eval (g.inputs.map fun i => (u.set w true).getD i false) = true) :
    g.op.eval (g.inputs.map fun i => u.getD i false) = u.getD w false := by
  cases hval : u.getD w false with
  | true =>
    rw [List.getD_eq_getElem _ _ hw] at hval
    have hset : u.set w true = u := by rw [← hval,List.set_getElem_self hw]
    rwa [hset] at ht
  | false =>
    rcases hg.1.1 with h | h | h
    · have hop : g.op = GateOp.and := h
      rw [hop]
      apply Bool.eq_false_iff.mpr
      intro ha
      have hh := List.all_eq_true.mp ha false (List.mem_map.mpr ⟨w,hr,hval⟩)
      exact Bool.false_ne_true hh
    · exact False.elim (ho h)
    · have hop : g.op = GateOp.not := h
      have hl := hg.2 hop
      have hs : g.inputs = [w] := by
        rcases he : g.inputs with _ | ⟨j,_ | ⟨k,ks⟩⟩
        · simp [he] at hr
        · rw [he] at hr
          simp at hr
          simp [hr]
        · simp [he] at hl
      simp [hop,hs,GateOp.eval,List.getD,hw] at ht

private lemma forcing_terminal_or {n w : ℕ} (pre a : List Gate) (g : Gate)
    (hw : w < n + pre.length) (ha : ∀ t ∈ a, w ∉ t.inputs)
    (hg : NOkGate g) (hr : w ∈ g.inputs)
    (h : Forces n w (n + pre.length + a.length) pre (a ++ [g]))
    (hmin : IsMinimalCircuit n ⟨(pre ++ a) ++ [g],n + pre.length + a.length⟩) :
    g.op = GateOp.or := by
  by_contra hn
  let D : Circuit := ⟨pre ++ a,w⟩
  have hd : FanInTwo D := fun t ht => hmin.1 t (List.mem_append_left _ ht)
  have heq : circuitFun n D = circuitFun n ⟨(pre ++ a) ++ [g],n + pre.length + a.length⟩ := by
    funext x
    let u := wiresFrom pre (List.ofFn x)
    let v := wiresFrom a u
    have hvlen : v.length = n + pre.length + a.length := by simp [v,u,wiresFrom_length]
    have huw : w < u.length := by simpa [u,wiresFrom_length] using hw
    have hvw : w < v.length := by omega
    have ht := h x
    change (wiresFrom (a ++ [g]) (u.set w true)).getD _ false = true at ht
    rw [wiresFrom_append,wiresFrom_set_unread a u w huw ha] at ht
    change (v.set w true ++ [_]).getD _ false = true at ht
    rw [getD_snoc_eq _ _ _ _ (by simp [hvlen])] at ht
    change (wiresFrom (pre ++ a) (List.ofFn x)).getD w false =
      (wiresFrom ((pre ++ a) ++ [g]) (List.ofFn x)).getD _ false
    rw [wiresFrom_append (pre ++ a),wiresFrom_append pre a]
    change v.getD w false = (v ++ [_]).getD _ false
    rw [getD_snoc_eq _ _ _ _ hvlen.symm]
    exact (forced_nonor_alias g v w hg hvw hr hn ht).symm
  have hsize := hmin.2 D hd heq
  change ((pre ++ a) ++ [g]).length ≤ (pre ++ a).length at hsize
  simp at hsize


private def ForcesAt (m w o : ℕ) (gs : List Gate) : Prop :=
  Forces m w o (gs.take (w+1-m)) (gs.drop (w+1-m))

private lemma unfiltered {w : ℕ} (a : List Gate)
    (h : (a.filter fun g => decide (w ∈ g.inputs)).length = 0) :
    ∀ g ∈ a, w ∉ g.inputs := by
  intro g hg hr
  have : 0 < (a.filter fun t => decide (w ∈ t.inputs)).length :=
    List.length_filter_pos_iff.mpr ⟨g,hg,by simpa using hr⟩
  omega

private lemma index_mem_drop {α} (gs : List α) (k : Fin gs.length) {c : ℕ} (hc : c ≤ k.val) :
    gs.get k ∈ gs.drop c := by
  apply List.mem_drop_iff_getElem.mpr
  refine ⟨k.val - c,by omega,?_⟩
  change gs[c+(k.val-c)] = gs[k.val]
  congr 1
  omega

private lemma index_mem_interval {α} (gs : List α) (k : Fin gs.length) {c j : ℕ}
    (hc : c ≤ k.val) (hj : k.val < j) :
    gs.get k ∈ (gs.take j).drop c := by
  apply List.mem_drop_iff_getElem.mpr
  refine ⟨k.val - c,by simp; omega,?_⟩
  rw [List.getElem_take]
  change gs[c+(k.val-c)] = gs[k.val]
  congr 1
  omega

private lemma forcing_transfer {m w o : ℕ} (gs : List Gate)
    (hmin : IsMinimalCircuit m ⟨gs,o⟩) (hnorm : ∀ t ∈ gs, normGate t = t)
    (hproper : ∀ (j : Fin gs.length) (s : ℕ), s ∈ (gs.get j).inputs → s < m+j.val)
    (hout : o+1 = m+gs.length)
    (hlive : ∀ j : Fin gs.length, m+j.val ≠ o →
      ∃ k : Fin gs.length, m+j.val ∈ (gs.get k).inputs)
    (hforce : ForcesAt m w o gs) (j : Fin gs.length) (hread : w ∈ (gs.get j).inputs) :
    (∀ k : Fin gs.length, w ∈ (gs.get k).inputs → k=j) ∧
      (gs.get j).op = GateOp.or ∧ ForcesAt m (m+j.val) o gs := by
  let c := w+1-m
  let pre := gs.take c
  let a := (gs.take j.val).drop c
  let g := gs.get j
  let b := gs.drop (j.val+1)
  let post := gs.drop c
  have hwp := hproper j w hread
  have hcle : c ≤ j.val := by unfold c; omega
  have hp : pre.length = c := by simp [pre,Nat.min_eq_left (by omega : c ≤ gs.length)]
  have hw : w < m + pre.length := by rw [hp]; unfold c; omega
  have hal : a.length = j.val - c := by simp [a]
  have hidx : m+pre.length+a.length = m+j.val := by omega
  have hprepost : pre ++ post = gs := List.take_append_drop .. 
  have hprea : pre ++ a = gs.take j.val := by
    have h := List.take_append_drop c (gs.take j.val)
    rw [List.take_take,Nat.min_eq_left hcle] at h
    exact h
  have hsplit : post = a ++ g :: b := by
    apply List.append_cancel_left (as := pre)
    rw [hprepost,← List.append_assoc,hprea]
    have h := List.take_append_drop j.val gs
    rw [List.drop_eq_getElem_cons j.isLt] at h
    exact h.symm
  have hnormpost : post.map normGate = post := by
    calc
      post.map normGate = post.map id := List.map_congr_left (fun t ht => hnorm t (hprepost ▸ List.mem_append_right pre ht))
      _ = post := by simp
  have hm : IsMinimalCircuit m ⟨pre ++ post,o⟩ := hprepost.symm ▸ hmin
  have hs := forcing_safe pre post hw hforce
  have hbudget := safe_wire_shortcut pre post hm hw hs
  rw [hnormpost,hsplit,List.filter_append,List.filter_cons_of_pos (by simpa [g] using hread)] at hbudget
  simp only [List.length_append,List.length_cons] at hbudget
  have hna : ∀ t ∈ a, w ∉ t.inputs := unfiltered a (by omega)
  have hnb : ∀ t ∈ b, w ∉ t.inputs := unfiltered b (by omega)
  have hsplitF : Forces m w o pre (a++g::b) := hsplit ▸ hforce
  have hop : g.op = GateOp.or := by
    by_cases hterm : m+j.val = o
    · have hj : gs.length ≤ j.val+1 := by omega
      have hbn : b = [] := List.drop_eq_nil_iff.mpr hj
      have hg := normGate_nok g (hmin.1 g (List.get_mem gs j))
      rw [hnorm g (List.get_mem gs j)] at hg
      have hcir : (pre ++ a) ++ [g] = gs := by
        rw [← hprepost,hsplit,hbn,List.append_assoc]
      rw [hbn] at hsplitF
      apply forcing_terminal_or pre a g hw hna hg hread
      · rwa [hidx,hterm]
      · rwa [hcir,hidx,hterm]
    · obtain ⟨k,hk⟩ := hlive j hterm
      have hlt := hproper k (m+j.val) hk
      apply safe_reader_op pre post a b g hm hw hs (hnormpost.trans hsplit) hread
      exact ⟨gs.get k,index_mem_drop gs k (by omega),hidx.symm ▸ hk⟩
  refine ⟨?_,hop,?_⟩
  · intro k hk
    have hkw := hproper k w hk
    have hkc : c ≤ k.val := by unfold c; omega
    by_contra he
    rcases lt_or_gt_of_ne (show k.val ≠ j.val from fun h => he (Fin.ext h)) with h | h
    · exact hna _ (index_mem_interval gs k hkc h) hk
    · exact hnb _ (index_mem_drop gs k (by omega)) hk
  · have hnwo : w ≠ o := by omega
    have hh := forcing_or_step pre a b g hw hnwo hna hnb hop hread hsplitF
    rw [hidx,hprea] at hh
    change Forces m (m+j.val) o (gs.take j.val ++ [gs[j.val]]) b at hh
    rw [← List.take_succ_eq_append_getElem j.isLt] at hh
    simpa [ForcesAt,show m+j.val+1-m = j.val+1 by omega,b] using hh


private def rawRead (C : Circuit) (j : Fin C.gates.length) (w : ℕ) : Prop :=
  (C.gates.get j).op = GateOp.not ∧ (C.gates.get j).inputs.head? = some w ∨
  (C.gates.get j).op ≠ GateOp.not ∧ w ∈ (C.gates.get j).inputs

private def rawEdge (n : ℕ) (C : Circuit) (a b : ℕ) : Prop :=
  ∃ j : Fin C.gates.length, b = n+1+j.val ∧ rawRead C j a

private lemma normGate_idem (g : Gate) : normGate (normGate g) = normGate g := by
  obtain ⟨op,ins⟩ := g
  cases op <;> simp [normGate]

private lemma normGate_op (g : Gate) : (normGate g).op = g.op := by
  obtain ⟨op,ins⟩ := g
  cases op <;> rfl

private lemma normGate_read (C : Circuit) (j : Fin C.gates.length) (w : ℕ) :
    w ∈ (normGate (C.gates.get j)).inputs ↔ rawRead C j w := by
  unfold rawRead
  generalize C.gates.get j = g
  obtain ⟨op,ins⟩ := g
  cases op <;> simp [normGate]
  cases ins <;> simp [eq_comm]

private theorem raw_semantic_facts (n : ℕ) (C : Circuit) (H : (Fin n → Bool) → Bool)
    (hmin : IsMinimalCircuit (n+1) C)
    (hf : ∀ x : Fin (n+1) → Bool, circuitFun (n+1) C x =
      (x (Fin.last n) || H (fun i => x i.castSucc)))
    (hout : C.output+1 = n+1+C.gates.length)
    (hproper : ∀ (j : Fin C.gates.length) (w : ℕ), rawRead C j w → w < n+1+j.val)
    (hlive : ∀ j : Fin C.gates.length, n+1+j.val ≠ C.output →
      ∃ k : Fin C.gates.length, rawRead C k (n+1+j.val)) :
    ∀ w : ℕ, (w=n ∨ Relation.TransGen (rawEdge n C) n w) →
      ∀ j : Fin C.gates.length, rawRead C j w →
        (∀ k : Fin C.gates.length, rawRead C k w → k=j) ∧ (C.gates.get j).op=GateOp.or := by
  let gs := C.gates.map normGate
  let m := n+1
  have hlen : gs.length=C.gates.length := List.length_map normGate
  let raw (j : Fin gs.length) : Fin C.gates.length := ⟨j.val,hlen ▸ j.isLt⟩
  let idx (j : Fin C.gates.length) : Fin gs.length := ⟨j.val,hlen.symm ▸ j.isLt⟩
  have gate (j : Fin gs.length) : gs.get j = normGate (C.gates.get (raw j)) := by
    simp [gs,raw]
  have reads (j : Fin gs.length) (w : ℕ) : w ∈ (gs.get j).inputs ↔ rawRead C (raw j) w := by
    rw [gate]; exact normGate_read C (raw j) w
  have hn (g : Gate) (hg : g∈gs) : normGate g=g := by
    obtain ⟨t,_,rfl⟩ := List.mem_map.mp hg
    exact normGate_idem t
  have heq : circuitFun m ⟨gs,C.output⟩ = circuitFun m C := by
    funext x
    change (wiresFrom (C.gates.map normGate) (List.ofFn x)).getD C.output false = _
    rw [wiresFrom_norm]
    rfl
  have hm : IsMinimalCircuit m ⟨gs,C.output⟩ := by
    constructor
    · intro g hg
      obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hg
      exact (normGate_nok t (hmin.1 t ht)).1
    · intro D hd hD
      have hz := hmin.2 D hd (hD.trans heq)
      simpa [Circuit.size,gs] using hz
  have proper (j : Fin gs.length) (w : ℕ) (hr : w ∈ (gs.get j).inputs) : w < m+j.val :=
    hproper (raw j) w ((reads _ _).mp hr)
  have live (j : Fin gs.length) (ho : m+j.val ≠ C.output) :
      ∃ k : Fin gs.length, m+j.val ∈ (gs.get k).inputs := by
    obtain ⟨k,hk⟩ := hlive (raw j) ho
    exact ⟨idx k,(reads _ _).mpr hk⟩
  have start : ForcesAt m n C.output gs := by
    have hh := forcing_input n C.output gs H (fun x => by rw [← hf x,← heq]; rfl)
    simpa [ForcesAt,m] using hh
  have step (w : ℕ) (fw : ForcesAt m w C.output gs) (j : Fin C.gates.length)
      (hr : rawRead C j w) :
      (∀ k : Fin C.gates.length, rawRead C k w → k=j) ∧
      (C.gates.get j).op=GateOp.or ∧ ForcesAt m (n+1+j.val) C.output gs := by
    have hz := forcing_transfer gs hm hn proper (by simpa [m,hlen] using hout) live fw
      (idx j) ((reads _ _).mpr hr)
    refine ⟨?_,?_,hz.2.2⟩
    · intro k hk
      have hi := hz.1 (idx k) ((reads _ _).mpr hk)
      exact Fin.ext (congrArg (fun a : Fin gs.length => a.val) hi)
    · have hop := hz.2.1
      rw [gate,normGate_op] at hop
      exact hop
  have path {w : ℕ} (hr : Relation.TransGen (rawEdge n C) n w) : ForcesAt m w C.output gs := by
    induction hr with
    | single h =>
      obtain ⟨j,rfl,hj⟩ := h
      exact (step n start j hj).2.2
    | tail _ h ih =>
      obtain ⟨j,rfl,hj⟩ := h
      exact (step _ ih j hj).2.2
  intro w hw j hj
  have fw := hw.elim (fun he => he.symm ▸ start) path
  have h := step w fw j hj
  exact ⟨h.1,h.2.1⟩

end Gap568

namespace Gap568

-- Removing a gate that computes a constant or an available wire is strictly cheaper.
private def spliceInit (m : ℕ) (q : Bool ⊕ ℕ) : List (Bool ⊕ ℕ) :=
  (List.ofFn fun i : Fin m => Sum.inr i.val) ++ [q]

private lemma splice_invariant (m : ℕ) (q : Bool ⊕ ℕ) (hq : statValid m q)
    (u : List Bool) (hu : u.length = m) :
    ElimInv m u (u ++ [statVal u q]) (spliceInit m q, []) := by
  refine ⟨hu, by simp [spliceInit, hu], ?_⟩
  intro i
  by_cases hi : i < m
  · rw [show (spliceInit m q).getD i (.inl false) = Sum.inr i from by
          unfold spliceInit
          rw [getD_snoc_lt _ _ _ _ (by simpa using hi), ofFn_getD_lt _ _ _ hi]]
    rw [getD_snoc_lt _ _ _ _ (hu.symm ▸ hi)]
    exact ⟨hi, rfl⟩
  · by_cases he : i = m
    · subst i
      rw [show (spliceInit m q).getD m (.inl false) = q from
          getD_snoc_eq _ _ _ _ (by simp), getD_snoc_eq _ _ _ _ hu.symm]
      exact ⟨hq,rfl⟩
    · rw [List.getD_eq_default _ _ (by simp [spliceInit]; omega),
          List.getD_eq_default _ _ (by simp [hu]; omega)]
      exact ⟨trivial,rfl⟩

private lemma no_splice {n o : ℕ} (pre tail : List Gate) (g : Gate)
    (hmin : IsMinimalCircuit n ⟨pre ++ g :: tail, o⟩)
    (hnc : ∃ x y, circuitFun n ⟨pre ++ g :: tail,o⟩ x ≠ circuitFun n ⟨pre ++ g :: tail,o⟩ y)
    (q : Bool ⊕ ℕ) (hq : statValid (n+pre.length) q)
    (he : ∀ u : List Bool, u.length = n+pre.length →
      statVal u q = g.op.eval (g.inputs.map fun i => u.getD i false)) : False := by
  let m := n+pre.length
  let acc := elimPass m tail (spliceInit m q, [])
  let out := acc.1.getD o (.inl false)
  have htail : ∀ g' ∈ tail, OkGate g' :=
    fun g' hg' => hmin.1 g' (List.mem_append_right _ (List.mem_cons_of_mem _ hg'))
  have hv (x : Fin n → Bool) : statVal (wiresFrom (pre ++ acc.2) (List.ofFn x)) out =
      circuitFun n ⟨pre ++ g :: tail,o⟩ x := by
    let u := wiresFrom pre (List.ofFn x)
    have hu : u.length = m := by simp [u,m,wiresFrom_length]
    have hf := elimInv_pass m u tail (u ++ [statVal u q]) (spliceInit m q,[]) htail
      (splice_invariant m q hq u hu)
    have hz := (hf.2.2 o).2
    rw [he u hu] at hz
    rw [wiresFrom_append]
    change statVal (wiresFrom acc.2 u) out = (wiresFrom (pre ++ g :: tail) (List.ofFn x)).getD o false
    rw [wiresFrom_append, wiresFrom_cons]
    exact hz
  cases hout : out with
  | inl c =>
    obtain ⟨x,y,hxy⟩ := hnc
    exact hxy (by rw [← hv x, ← hv y, hout]; rfl)
  | inr w =>
    let D : Circuit := ⟨pre ++ acc.2,w⟩
    have hd : FanInTwo D := by
      intro g' hg'
      rcases List.mem_append.mp hg' with hp|ha
      · exact hmin.1 g' (List.mem_append_left _ hp)
      · exact elimPass_ok m tail _ (by simp) g' ha
    have heq : circuitFun n D = circuitFun n ⟨pre ++ g :: tail,o⟩ := by
      funext x
      have := hv x
      rw [hout] at this
      exact this
    have hle := hmin.2 D hd heq
    have hlen : acc.2.length ≤ tail.length := by
      simpa [acc] using elimPass_len m tail (spliceInit m q,[])
    change (pre ++ g :: tail).length ≤ (pre ++ acc.2).length at hle
    simp only [List.length_append,List.length_cons] at hle
    omega

private def gateShape (m : ℕ) (g : Gate) : Prop := by
  classical
  exact if g.op = GateOp.not then ∃ w, g.inputs.head? = some w ∧ w<m
  else ∃ a b, g.inputs=[a,b] ∧ a≠b ∧ a<m ∧ b<m

private def replacement (m : ℕ) (a : ℕ) : Bool ⊕ ℕ :=
  if a<m then .inr a else .inl false

private lemma replacement_valid (m a : ℕ) : statValid m (replacement m a) := by
  by_cases h : a<m <;> simp [replacement,h,statValid]

private lemma replacement_val (m a : ℕ) (u : List Bool) (hu : u.length = m) :
    statVal u (replacement m a) = u.getD a false := by
  by_cases h : a<m
  · simp [replacement,h,statVal]
  · unfold replacement
    simp only [h, ite_false]
    rw [List.getD_eq_default u false (by omega)]
    rfl

private lemma invalid_lookup {m w : ℕ} (u : List Bool) (hu : u.length = m)
    (hw : ¬w<m) : u[w]?.getD false = false :=
  List.getD_eq_default u false (by omega)

private lemma bad_shape_splices (m : ℕ) (g : Gate) (hok : OkGate g) (hbad : ¬gateShape m g) :
    ∃ q, statValid m q ∧ ∀ u : List Bool, u.length = m →
      statVal u q = g.op.eval (g.inputs.map fun i => u.getD i false) := by
  obtain ⟨op,ins⟩ := g
  obtain ⟨hop,hlen⟩ := hok
  change ins.length ≤ 2 at hlen
  rcases hop with e|e|e
  all_goals change op = _ at e
  all_goals subst op
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨k,rest⟩⟩⟩
    · exact ⟨.inl true,trivial,fun u _ => rfl⟩
    · exact ⟨replacement m a, replacement_valid _ _,fun u hu => by
        simp [replacement_val m a u hu,GateOp.eval]⟩
    · by_cases hab : a=b
      · subst b
        exact ⟨replacement m a, replacement_valid _ _,fun u hu => by
          simp [replacement_val m a u hu,GateOp.eval]⟩
      · by_cases ha : a<m
        · by_cases hb : b<m
          · exact (hbad (by simp [gateShape, hab, ha, hb])).elim
          · exact ⟨.inl false,trivial,fun u hu => by
              simp [statVal, GateOp.eval, invalid_lookup u hu hb]⟩
        · exact ⟨.inl false,trivial,fun u hu => by
            simp [statVal, GateOp.eval, invalid_lookup u hu ha]⟩
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨k,rest⟩⟩⟩
    · exact ⟨.inl false,trivial,fun u _ => rfl⟩
    · exact ⟨replacement m a, replacement_valid _ _,fun u hu => by
        simp [replacement_val m a u hu,GateOp.eval]⟩
    · by_cases hab : a=b
      · subst b
        exact ⟨replacement m a, replacement_valid _ _,fun u hu => by
          simp [replacement_val m a u hu,GateOp.eval]⟩
      · by_cases ha : a<m
        · by_cases hb : b<m
          · exact (hbad (by simp [gateShape, hab, ha, hb])).elim
          · exact ⟨replacement m a,replacement_valid _ _,fun u hu => by
              simp [replacement_val m a u hu, GateOp.eval, invalid_lookup u hu hb]⟩
        · exact ⟨replacement m b,replacement_valid _ _,fun u hu => by
            simp [replacement_val m b u hu, GateOp.eval, invalid_lookup u hu ha]⟩
    · simp at hlen
  · rcases ins with _ | ⟨a,tail⟩
    · exact ⟨.inl true,trivial,fun u _ => rfl⟩
    · have ha : ¬a<m := by simpa [gateShape] using hbad
      exact ⟨.inl true,trivial,fun u hu => by
        simp [statVal, GateOp.eval, invalid_lookup u hu ha]⟩

private lemma minimal_gate_shape {m : ℕ} {C : Circuit} (hmin : IsMinimalCircuit m C)
    (hnc : ∃ x y, circuitFun m C x ≠ circuitFun m C y)
    (j : Fin C.gates.length) : gateShape (m+j.val) (C.gates.get j) := by
  by_contra hbad
  have hg := hmin.1 (C.gates.get j) (List.get_mem _ _)
  obtain ⟨q,hq,he⟩ := bad_shape_splices _ _ hg hbad
  let pre := C.gates.take j.val
  let tail := C.gates.drop (j.val+1)
  have hp : pre.length = j.val := by simp [pre]
  have hgs : pre ++ C.gates.get j :: tail = C.gates := by
    change C.gates.take j.val ++ C.gates[j.val] :: C.gates.drop (j.val+1) = C.gates
    rw [List.getElem_cons_drop j.isLt, List.take_append_drop]
  have hc : (⟨pre ++ C.gates.get j :: tail, C.output⟩ : Circuit)=C := by
    rw [hgs]
  apply no_splice pre tail (C.gates.get j) (o:=C.output) (by rw [hc]; exact hmin) (by rw [hc]; exact hnc) q
  · simpa [hp] using hq
  · simpa [hp] using he

private lemma minimal_binary_inputs {m : ℕ} {C : Circuit} (hmin : IsMinimalCircuit m C)
    (hnc : ∃ x y, circuitFun m C x ≠ circuitFun m C y) (j : Fin C.gates.length)
    (hop : (C.gates.get j).op ≠ .not) :
    ∃ a b, (C.gates.get j).inputs=[a,b] ∧ a≠b ∧ a<m+j.val ∧ b<m+j.val := by
  simpa only [gateShape,hop,ite_false] using minimal_gate_shape hmin hnc j

private lemma minimal_material_lt {m : ℕ} {C : Circuit} (hmin : IsMinimalCircuit m C)
    (hnc : ∃ x y, circuitFun m C x ≠ circuitFun m C y) (j : Fin C.gates.length) (w : ℕ)
    (hr : (C.gates.get j).op = .not ∧ (C.gates.get j).inputs.head?=some w ∨
      (C.gates.get j).op ≠ .not ∧ w ∈ (C.gates.get j).inputs) : w < m+j.val := by
  rcases hr with ⟨hop,hhead⟩|⟨hop,hw⟩
  · have h := minimal_gate_shape hmin hnc j
    simp only [gateShape,hop,ite_true] at h
    obtain ⟨v,hv,hlt⟩ := h
    have he : v=w := Option.some.inj (hv.symm.trans hhead)
    exact he ▸ hlt
  · obtain ⟨a,b,hab,_,ha,hb⟩ := minimal_binary_inputs hmin hnc j hop
    rw [hab] at hw
    rcases List.mem_cons.mp hw with rfl|hw
    · exact ha
    · simpa [List.mem_singleton.mp hw] using hb

end Gap568

namespace Structure568
open PEqualNP.CircuitLowerBounds

private def rd (C : Circuit) (j : Fin C.gates.length) (w : ℕ) : Prop :=
 (C.gates.get j).op = GateOp.not ∧ (C.gates.get j).inputs.head? = some w ∨
 (C.gates.get j).op ≠ GateOp.not ∧ w ∈ (C.gates.get j).inputs

private def edge (n : ℕ) (C : Circuit) (a b : ℕ) : Prop :=
 ∃ j : Fin C.gates.length, b = n + 1 + j.val ∧ rd C j a

private theorem trace_of_path {R : ℕ → ℕ → Prop} {a b : ℕ} (h : Relation.TransGen R a b) :
    ∃ (k : ℕ) (f : ℕ → ℕ), f 0 = a ∧ f (k+1) = b ∧
      ∀ i ≤ k, R (f i) (f (i+1)) := by
  induction h with
  | @single b h =>
    refine ⟨0, (fun i => if i = 0 then a else b), by simp, by simp, ?_⟩
    intro i hi
    have hi0 : i = 0 := by omega
    subst i
    simpa using h
  | @tail b c _ step ih =>
    obtain ⟨k, f, hs, he, hf⟩ := ih
    refine ⟨k+1, fun i => if i ≤ k+1 then f i else c, by simpa using hs, by simp, ?_⟩
    intro i hi
    by_cases hi' : i ≤ k
    · simpa [show i ≤ k+1 by omega, show i+1 ≤ k+1 by omega] using hf i hi'
    · have : i = k+1 := by omega
      subst i
      simpa [he] using step

private theorem reachable_at {R : ℕ → ℕ → Prop} {k : ℕ} {f : ℕ → ℕ}
    (hf : ∀ i ≤ k, R (f i) (f (i+1))) :
    ∀ i ≤ k, Relation.TransGen R (f 0) (f (i+1)) := by
  intro i hi
  induction i with
  | zero => exact .single (hf 0 hi)
  | succ i ih => exact .tail (ih (by omega)) (hf (i+1) hi)

private theorem trace_range {R : ℕ → ℕ → Prop} {k : ℕ} {f : ℕ → ℕ}
    (hu : ∀ i ≤ k, ∀ w, R (f i) w → w = f (i+1))
    (ht : ∀ w, ¬ R (f (k+1)) w) {w : ℕ} (h : Relation.TransGen R (f 0) w) :
    ∃ i ≤ k, f (i+1) = w := by
  induction h with
  | single h => exact ⟨0, Nat.zero_le _, (hu 0 (Nat.zero_le _) _ h).symm⟩
  | tail _ step ih =>
    obtain ⟨i, hi, rfl⟩ := ih
    by_cases hi' : i < k
    · exact ⟨i+1, by omega, (hu (i+1) (by omega) _ step).symm⟩
    · have : i = k := by omega
      subst i
      exact False.elim (ht _ step)

private def localOK (n : ℕ) (C : Circuit) (j : Fin C.gates.length) : Prop :=
  (C.gates.get j).op = GateOp.or ∧ ∃ u v : ℕ,
   (C.gates.get j).inputs = [u,v] ∧ u ≠ v ∧ u < n+1+j.val ∧ v < n+1+j.val

private theorem localOK_mem {n : ℕ} {C : Circuit} {j : Fin C.gates.length}
    (h : localOK n C j) {w : ℕ} (hr : rd C j w) :
    w ∈ (C.gates.get j).inputs ∧ w < n+1+j.val ∧
    ∃ v ∈ (C.gates.get j).inputs, v ≠ w ∧ v < n+1+j.val := by
  obtain ⟨hop, u, v, hi, hne, hlu, hlv⟩ := h
  unfold rd at hr
  rw [hop, hi] at hr
  simp at hr
  rcases hr with rfl | rfl
  · exact ⟨by rw [hi]; simp, hlu, v, by rw [hi]; simp, hne.symm, hlv⟩
  · exact ⟨by rw [hi]; simp, hlv, u, by rw [hi]; simp, hne, hlu⟩

private theorem assemble (n : ℕ) (C : Circuit)
    (jLast : Fin C.gates.length) (hlast : jLast.val + 1 = C.gates.length)
    (hout : C.output = n+1+jLast.val)
    (hreach : Relation.TransGen (edge n C) n (n+1+jLast.val))
    (huni : ∀ w : ℕ, (w=n ∨ Relation.TransGen (edge n C) n w) →
      ∀ j j' : Fin C.gates.length, rd C j w → rd C j' w → j=j')
    (hloc : ∀ w : ℕ, (w=n ∨ Relation.TransGen (edge n C) n w) →
      ∀ j : Fin C.gates.length, rd C j w → localOK n C j) :
      ∃ (k : ℕ) (c : Fin (k + 1) → Fin C.gates.length), StrictMono c ∧ (c (Fin.last k)).val + 1 = C.gates.length ∧ C.output = n + 1 + (c (Fin.last k)).val ∧ (∀ i : Fin (k + 1), (C.gates.get (c i)).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (C.gates.get (c i)).inputs.length = 2) ∧ n ∈ (C.gates.get (c 0)).inputs ∧ (∀ i : Fin k, n + 1 + (c i.castSucc).val ∈ (C.gates.get (c i.succ)).inputs) ∧ (∀ j : Fin C.gates.length, ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some n ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ n ∈ (C.gates.get j).inputs) → j = c 0) ∧ (∀ (i : Fin k) (j : Fin C.gates.length), ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some (n + 1 + (c i.castSucc).val) ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ (n + 1 + (c i.castSucc).val) ∈ (C.gates.get j).inputs) → j = c i.succ) ∧ (∀ j : Fin C.gates.length, Relation.TransGen (fun a b : ℕ => ∃ j : Fin C.gates.length, b = n + 1 + j.val ∧ ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some a ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ a ∈ (C.gates.get j).inputs)) n (n + 1 + j.val) ↔ ∃ i : Fin (k + 1), c i = j) ∧ (∃ w ∈ (C.gates.get (c 0)).inputs, w ≠ n ∧ w < n + 1 + (c 0).val ∧ ¬ Relation.TransGen (fun a b : ℕ => ∃ j : Fin C.gates.length, b = n + 1 + j.val ∧ ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some a ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ a ∈ (C.gates.get j).inputs)) n w) ∧ (∀ i : Fin k, ∃ w ∈ (C.gates.get (c i.succ)).inputs, w ≠ n + 1 + (c i.castSucc).val ∧ w ≠ n ∧ w < n + 1 + (c i.succ).val ∧ ¬ Relation.TransGen (fun a b : ℕ => ∃ j : Fin C.gates.length, b = n + 1 + j.val ∧ ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some a ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ a ∈ (C.gates.get j).inputs)) n w) := by
  classical
  obtain ⟨k,f,hs,he,hstep⟩ := trace_of_path hreach
  have source (i : ℕ) (hi : i ≤ k+1) :
      f i = n ∨ Relation.TransGen (edge n C) n (f i) := by
    cases i with
    | zero => exact Or.inl hs
    | succ i => exact Or.inr (hs ▸ reachable_at hstep i (by omega))
  choose c heq hrd using (fun i : Fin (k+1) => hstep i.val (by omega))
  have loc (i : Fin (k+1)) := hloc _ (source i.val (by omega)) (c i) (hrd i)
  have side (i : Fin (k+1)) := localOK_mem (loc i) (hrd i)
  have hinc (i : Fin (k+1)) : f i.val < f (i.val+1) := by
    rw [heq i]
    exact (side i).2.1
  have hmono : StrictMono c := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    have h := hinc i.succ
    have h1 := heq i.castSucc
    have h2 := heq i.succ
    change f (i.val+1) < f (i.val+1+1) at h
    change f (i.val+1) = _ at h1
    change f (i.val+1+1) = _ at h2
    rw [h1,h2] at h
    exact (show (c i.castSucc).val < (c i.succ).val by omega)
  have lastEq : c (Fin.last k) = jLast := by
    have t := heq (Fin.last k)
    change f (k+1) = _ at t
    apply Fin.ext
    omega
  have only (i : Fin (k+1)) (j : Fin C.gates.length) (h : rd C j (f i.val)) : j = c i :=
    huni _ (source i.val (by omega)) _ _ h (hrd i)
  have deterministic (i : ℕ) (hi : i ≤ k) (w : ℕ) (h : edge n C (f i) w) :
      w = f (i+1) := by
    obtain ⟨j,hj,hr⟩ := h
    let I : Fin (k+1) := ⟨i, by omega⟩
    exact hj.trans ((congrArg (fun z : Fin C.gates.length => n+1+z.val) (only I j hr)).trans (heq I).symm)
  have terminal (w : ℕ) (h : edge n C (f (k+1)) w) : False := by
    obtain ⟨j,_,hr⟩ := h
    have hh := (localOK_mem (hloc _ (source (k+1) le_rfl) _ hr) hr).2.1
    have := j.isLt
    omega
  have cover {w : ℕ} (h : Relation.TransGen (edge n C) n w) : ∃ i : Fin (k+1), f (i.val+1) = w := by
    have hr : Relation.TransGen (edge n C) (f 0) w := by rw [hs]; exact h
    obtain ⟨i, hi, hi'⟩ := trace_range deterministic terminal hr
    exact ⟨⟨i, by omega⟩, hi'⟩
  have blocked (i : Fin (k+1)) {v : ℕ} (hv : rd C (c i) v) (hne : v ≠ f i.val) :
      v ≠ n ∧ ¬ Relation.TransGen (edge n C) n v := by
    constructor
    · intro hvn
      have h0 : c i = c 0 := only 0 _ (by simpa only [Fin.val_zero, hs, hvn] using hv)
      have hi : i = 0 := hmono.injective h0
      apply hne
      rw [hi]
      exact hvn.trans hs.symm
    · intro hR
      obtain ⟨j, hj⟩ := cover hR
      by_cases ht : j.val = k
      · apply terminal (n+1+(c i).val)
        refine ⟨c i, rfl, ?_⟩
        rw [ht] at hj
        rwa [hj]
      · let J : Fin (k+1) := ⟨j.val+1, by omega⟩
        have hh : c i = c J := only J _ (by show rd C (c i) (f (j.val+1)); rwa [hj])
        have hI := hmono.injective hh
        exact hne (by rw [hI]; exact hj.symm)
  have mkSide (i : Fin (k+1)) : ∃ v ∈ (C.gates.get (c i)).inputs, v ≠ f i.val ∧
      v < n+1+(c i).val ∧ v ≠ n ∧ ¬ Relation.TransGen (edge n C) n v := by
    obtain ⟨v,hv,hd,hl⟩ := (side i).2.2
    have hnot : (C.gates.get (c i)).op ≠ GateOp.not := by rw [(loc i).1]; intro e; cases e
    have hr : rd C (c i) v := Or.inr ⟨hnot,hv⟩
    exact ⟨v,hv,hd,hl,blocked i hr hd⟩
  have hprev (i : Fin k) : f (i.val+1) = n+1+(c i.castSucc).val := heq i.castSucc
  refine ⟨k,c,hmono,lastEq.symm ▸ hlast,lastEq.symm ▸ hout,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro i
    obtain ⟨hop,u,v,hins,-⟩ := loc i
    exact ⟨hop, by rw [hins]; rfl⟩
  · simpa only [Fin.val_zero, hs] using (side 0).1
  · intro i
    have hm := (side i.succ).1
    change f (i.val+1) ∈ _ at hm
    rwa [hprev i] at hm
  · intro j h
    apply only 0
    change rd C j n at h
    change rd C j (f 0)
    rwa [hs]
  · intro i j h
    apply only i.succ
    change rd C j (f (i.val+1))
    rw [hprev i]
    exact h
  · intro j
    constructor
    · intro h
      obtain ⟨i,hi⟩ := cover h
      exact ⟨i, Fin.ext (by have hh := heq i; omega)⟩
    · rintro ⟨i,rfl⟩
      have h := reachable_at hstep i.val (by omega)
      rwa [hs,heq i] at h
  · obtain ⟨v,hv,hd,hl,_,hx⟩ := mkSide 0
    exact ⟨v,hv, by simpa only [Fin.val_zero, hs] using hd,hl,hx⟩
  · intro i
    obtain ⟨v,hv,hd,hl,hn,hx⟩ := mkSide i.succ
    change v ≠ f (i.val+1) at hd
    exact ⟨v,hv, by simpa only [hprev i] using hd,hn,hl,hx⟩

end Structure568

namespace Structure568

open Gap568 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private theorem rd_congr {C : Circuit} {j : Fin C.gates.length} {p q : ℕ → Bool}
    (h : ∀ w, rd C j w → p w = q w) :
    (C.gates.get j).op.eval ((C.gates.get j).inputs.map p) =
    (C.gates.get j).op.eval ((C.gates.get j).inputs.map q) := by
  set g := C.gates.get j with hg
  by_cases hn : g.op = GateOp.not
  · rw [hn]
    cases hi : g.inputs with
    | nil => rfl
    | cons a l =>
      have ha := h a (Or.inl ⟨hn, by change g.inputs.head? = _; rw [hi]; rfl⟩)
      simp [GateOp.eval,ha]
  · congr 1
    apply List.map_congr_left
    intro a ha
    exact h a (Or.inr ⟨hn,ha⟩)

private theorem witness_reach_aux (n : ℕ) (C : Circuit) (pre tail : List Gate)
    (hlist : C.gates = pre ++ tail) (u v : List Bool)
    (hu : u.length = n+1+pre.length) (hv : v.length = n+1+pre.length)
    (hbefore : ∀ a, u.getD a false ≠ v.getD a false →
        a = n ∨ Relation.TransGen (edge n C) n a) :
    ∀ a, (wiresFrom tail u).getD a false ≠ (wiresFrom tail v).getD a false →
        a = n ∨ Relation.TransGen (edge n C) n a := by
  induction tail generalizing pre u v with
  | nil => exact hbefore
  | cons g tail ih =>
    let z := n+1+pre.length
    have hid : pre.length < C.gates.length := by rw [hlist]; simp
    let j : Fin C.gates.length := ⟨pre.length, hid⟩
    have hgj : C.gates.get j = g := by
      change C.gates[pre.length] = g
      simp [hlist, List.getElem_append_right]
    apply ih (pre ++ [g]) (by simpa using hlist)
    · simp [hu]; omega
    · simp [hv]; omega
    intro a hdiff
    by_cases ha : a = z
    · subst a
      rw [getD_snoc_eq _ _ _ _ hu.symm,getD_snoc_eq _ _ _ _ hv.symm] at hdiff
      have hex : ∃ w, rd C j w ∧ u.getD w false ≠ v.getD w false := by
        by_contra! h
        exact hdiff (hgj ▸ rd_congr h)
      obtain ⟨w,hw,hd⟩ := hex
      have e : edge n C w z := ⟨j, rfl, hw⟩
      refine Or.inr ?_
      rcases hbefore w hd with he | hr
      · subst w; exact .single e
      · exact hr.tail e
    · rw [getD_snoc_ne _ _ _ _ (by simpa only [hu] using ha),
        getD_snoc_ne _ _ _ _ (by simpa only [hv] using ha)] at hdiff
      exact hbefore a hdiff

private theorem endpoint (n : ℕ) (C : Circuit) (H : (Fin n → Bool) → Bool)
    (hmin : IsMinimalCircuit (n+1) C) (hnc : ∃ y y', H y ≠ H y')
    (hspec : ∀ x : Fin (n+1) → Bool, circuitFun (n+1) C x =
        (x (Fin.last n) || H (fun i : Fin n => x i.castSucc))) :
    ∃ jLast : Fin C.gates.length, jLast.val+1 = C.gates.length ∧
      C.output = n+1+jLast.val ∧ Relation.TransGen (edge n C) n C.output := by
  obtain ⟨y0, h0⟩ : ∃ y0, H y0 = false := by
    obtain ⟨a,b,h⟩ := hnc
    cases ha : H a <;> cases hb : H b <;> simp_all
    all_goals aesop
  obtain ⟨y1, h1⟩ : ∃ y1, H y1 = true := by
    obtain ⟨a,b,h⟩ := hnc
    cases ha : H a <;> cases hb : H b <;> simp_all
    all_goals aesop
  let x (b : Bool) : Fin (n+1) → Bool := Fin.snoc y0 b
  have he (b : Bool) : circuitFun (n+1) C (x b) = b := by
    rw [hspec]
    simp [x,h0,Fin.snoc_castSucc,Fin.snoc_last]
  have hd : (wiresFrom C.gates (List.ofFn (x false))).getD C.output false ≠
      (wiresFrom C.gates (List.ofFn (x true))).getD C.output false := by
    change circuitFun (n+1) C (x false) ≠ circuitFun (n+1) C (x true)
    rw [he, he]; decide
  have hs : ∀ a, (List.ofFn (x false)).getD a false ≠ (List.ofFn (x true)).getD a false →
      a = n ∨ Relation.TransGen (edge n C) n a := by
    intro a h
    by_cases ha : a < n
    · have h1 := ofFn_getD_lt (x false) false a (by omega)
      have h2 := ofFn_getD_lt (x true) false a (by omega)
      have hf : (⟨a, by omega⟩ : Fin (n+1)) = (⟨a, ha⟩ : Fin n).castSucc := rfl
      apply False.elim (h ?_)
      rw [h1,h2]
      change Fin.snoc (α := fun _ => Bool) y0 false ((⟨a,ha⟩ : Fin n).castSucc) = Fin.snoc (α := fun _ => Bool) y0 true ((⟨a,ha⟩ : Fin n).castSucc)
      rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
    · by_cases hh : a = n
      · exact Or.inl hh
      · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)] at h
        exact (h rfl).elim
  have hr := witness_reach_aux n C [] C.gates (by simp) _ _ (by simp) (by simp) hs _ hd
  have hne : C.output ≠ n := by
    intro ho
    let y : Fin (n+1) → Bool := Fin.snoc y1 false
    have hy : circuitFun (n+1) C y = true := by
      rw [hspec]; simp [y,h1,Fin.snoc_castSucc,Fin.snoc_last]
    change (wiresFrom C.gates (List.ofFn y)).getD C.output false = true at hy
    rw [ho, wiresFrom_getD_lt _ _ _ (by simp),ofFn_getD_lt _ _ _ (by omega)] at hy
    have hfl : (⟨n, by omega⟩ : Fin (n+1)) = Fin.last n := rfl
    rw [hfl] at hy
    simp [y,Fin.snoc_last] at hy
  have hpath := hr.resolve_left hne
  obtain ⟨j,hw⟩ : ∃ j : Fin C.gates.length, C.output = n+1+j.val := by
    cases hpath with
    | single h => obtain ⟨j,hj,-⟩ := h; exact ⟨j,hj⟩
    | tail _ h => obtain ⟨j,hj,-⟩ := h; exact ⟨j,hj⟩
  refine ⟨j,?_,hw,hpath⟩
  by_contra hn
  obtain hnil | ⟨pre,g,hgs⟩ := List.eq_nil_or_concat' C.gates
  · have := j.isLt; simp [hnil] at this
  have ht : j.val < pre.length := by
    have := j.isLt
    have hlen : C.gates.length = pre.length + 1 := by rw [hgs]; simp
    omega
  let D : Circuit := ⟨pre,C.output⟩
  have hgood : FanInTwo D := by
    intro g hg
    apply hmin.1 g
    rw [hgs]; exact List.mem_append_left _ hg
  have hsame : circuitFun (n+1) D = circuitFun (n+1) C := by
    funext x
    change (wiresFrom pre (List.ofFn x)).getD C.output false =
      (wiresFrom C.gates (List.ofFn x)).getD C.output false
    rw [hgs,wiresFrom_append]
    apply Eq.symm (wiresFrom_getD_lt [g] _ _ ?_)
    rw [wiresFrom_length,List.length_ofFn,hw]; omega
  have hle := hmin.2 D hgood hsame
  change C.gates.length ≤ pre.length at hle
  rw [hgs,List.length_append,List.length_singleton] at hle
  omega

end Structure568

namespace Structure568

open Gap568 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def reads (g : Gate) (w : ℕ) : Prop :=
  g.op = GateOp.not ∧ g.inputs.head? = some w ∨ g.op ≠ GateOp.not ∧ w ∈ g.inputs

private def afterErase (k w : ℕ) : ℕ := if w < k then w else w-1

private def rewire (k : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (afterErase k)⟩

private theorem gate_eq_if_agree (g : Gate) (p q : ℕ → Bool)
    (hag : ∀ a, reads g a → p a = q a) : g.op.eval (g.inputs.map p) = g.op.eval (g.inputs.map q) := by
  by_cases hn : g.op = GateOp.not
  · rw [hn]
    cases hi : g.inputs with
    | nil => rfl
    | cons a l =>
      have h := hag a (Or.inl ⟨hn, by rw [hi]; rfl⟩)
      simp [GateOp.eval,h]
  · apply congrArg g.op.eval
    apply List.map_congr_left
    exact fun a ha => hag a (Or.inr ⟨hn,ha⟩)

private theorem rewire_correct (k : ℕ) (tail : List Gate) (u v : List Bool)
    (hu : k ≤ u.length) (hv : v.length = u.length+1)
    (hread : ∀ g ∈ tail, ¬ reads g k)
    (hag : ∀ a, a ≠ k → u.getD (afterErase k a) false = v.getD a false) :
    ∀ a, a ≠ k →
      (wiresFrom (tail.map (rewire k)) u).getD (afterErase k a) false =
      (wiresFrom tail v).getD a false := by
  induction tail generalizing u v with
  | nil => exact hag
  | cons g tail ih =>
    let va := (rewire k g).op.eval ((rewire k g).inputs.map (fun i => u.getD i false))
    let vb := g.op.eval (g.inputs.map (fun i => v.getD i false))
    have heq : va = vb := by
      change g.op.eval ((g.inputs.map (afterErase k)).map _) = _
      rw [List.map_map]
      apply gate_eq_if_agree
      intro a ha
      exact hag a (fun h => hread g List.mem_cons_self (h ▸ ha))
    apply ih (u ++ [va]) (v ++ [vb])
    · simp; omega
    · simp [hv]
    · exact fun x hx => hread x (List.mem_cons_of_mem _ hx)
    intro a ha
    by_cases hlast : a = v.length
    · have hre : afterErase k a = u.length := by unfold afterErase; split <;> omega
      rw [getD_snoc_eq _ _ _ _ hre, getD_snoc_eq _ _ _ _ hlast]
      exact heq
    · have hre : afterErase k a ≠ u.length := by unfold afterErase; split <;> omega
      rw [getD_snoc_ne _ _ _ _ hre,getD_snoc_ne _ _ _ _ hlast]
      exact hag a ha

private theorem drop_rewire (m : ℕ) (pre post : List Gate) (g : Gate) (o : ℕ)
    (hmin : IsMinimalCircuit m ⟨pre ++ (g::post),o⟩) (hne : o ≠ m+pre.length) :
    ∃ a ∈ post, reads a (m+pre.length) := by
  by_contra! hno
  let k := m+pre.length
  let D : Circuit := ⟨pre ++ post.map (rewire k), afterErase k o⟩
  have hd : FanInTwo D := by
    intro g' hg'
    change g' ∈ pre ++ post.map (rewire k) at hg'
    rcases List.mem_append.mp hg' with h | h
    · exact hmin.1 g' (List.mem_append_left _ h)
    · obtain ⟨x,hx,rfl⟩ := List.mem_map.mp h
      obtain ⟨ho, hl⟩ := hmin.1 x (List.mem_append_right _ (List.mem_cons_of_mem _ hx))
      exact ⟨ho, by simpa only [rewire,List.length_map] using hl⟩
  have he : circuitFun m D = circuitFun m ⟨pre ++ (g::post),o⟩ := by
    funext x
    let u := wiresFrom pre (List.ofFn x)
    let b := g.op.eval (g.inputs.map fun i => u.getD i false)
    have hu : u.length = k := by simp [u,wiresFrom_length,k]
    change (wiresFrom (pre ++ _) _).getD _ false = (wiresFrom (pre ++ _) _).getD _ false
    rw [wiresFrom_append,wiresFrom_append,wiresFrom_cons]
    apply rewire_correct k post u (u ++ [b]) (by omega) (by simp) hno _ o hne
    intro a ha
    by_cases ha' : a < k
    · rw [getD_snoc_lt _ _ _ _ (by omega)]
      simp [afterErase,ha']
    · rw [List.getD_eq_default _ _ (by rw [hu]; unfold afterErase; split <;> omega),
          List.getD_eq_default _ _ (by simp [hu]; omega)]
  have hs := hmin.2 D hd he
  change (pre ++ g::post).length ≤ (pre ++ post.map (rewire k)).length at hs
  simp at hs

private theorem liveness (m : ℕ) (C : Circuit) (hmin : IsMinimalCircuit m C)
    (j : Fin C.gates.length) (hne : m+j.val ≠ C.output) :
    ∃ k : Fin C.gates.length, rd C k (m+j.val) := by
  let pre := C.gates.take j.val
  let post := C.gates.drop (j.val+1)
  have hlist : C.gates = pre ++ (C.gates.get j :: post) := by
    unfold pre post
    rw [List.cons_get_drop_succ,List.take_append_drop]
  have hlen : pre.length = j.val := by simp [pre]
  have hC : (⟨pre ++ C.gates.get j :: post,C.output⟩ : Circuit) = C := by
    rw [← hlist]
  obtain ⟨g,hg,hread⟩ := drop_rewire m pre post (C.gates.get j) C.output (hC.symm ▸ hmin) (by rwa [hlen,ne_comm])
  have hmem : g ∈ C.gates := by
    have hh : g ∈ pre ++ (C.gates.get j :: post) := List.mem_append_right _ (List.mem_cons_of_mem _ hg)
    exact (congrArg (fun l : List Gate => g ∈ l) hlist).mpr hh
  obtain ⟨k,hk⟩ := List.mem_iff_get.mp hmem
  refine ⟨k,?_⟩
  change reads (C.gates.get k) (m+j.val)
  rwa [hk,← hlen]

end Structure568

theorem PEqualNP.Outside.L_meta_568 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (H : (Fin n → Bool) → Bool), PEqualNP.MetaComplexity.IsMinimalCircuit (n + 1) C → (∃ y y' : Fin n → Bool, H y ≠ H y') → (∀ x : Fin (n + 1) → Bool, PEqualNP.MetaComplexity.circuitFun (n + 1) C x = (x (Fin.last n) || H (fun i : Fin n => x i.castSucc))) → ∃ (k : ℕ) (c : Fin (k + 1) → Fin C.gates.length), StrictMono c ∧ (c (Fin.last k)).val + 1 = C.gates.length ∧ C.output = n + 1 + (c (Fin.last k)).val ∧ (∀ i : Fin (k + 1), (C.gates.get (c i)).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (C.gates.get (c i)).inputs.length = 2) ∧ n ∈ (C.gates.get (c 0)).inputs ∧ (∀ i : Fin k, n + 1 + (c i.castSucc).val ∈ (C.gates.get (c i.succ)).inputs) ∧ (∀ j : Fin C.gates.length, ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some n ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ n ∈ (C.gates.get j).inputs) → j = c 0) ∧ (∀ (i : Fin k) (j : Fin C.gates.length), ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some (n + 1 + (c i.castSucc).val) ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ (n + 1 + (c i.castSucc).val) ∈ (C.gates.get j).inputs) → j = c i.succ) ∧ (∀ j : Fin C.gates.length, Relation.TransGen (fun a b : ℕ => ∃ j : Fin C.gates.length, b = n + 1 + j.val ∧ ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some a ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ a ∈ (C.gates.get j).inputs)) n (n + 1 + j.val) ↔ ∃ i : Fin (k + 1), c i = j) ∧ (∃ w ∈ (C.gates.get (c 0)).inputs, w ≠ n ∧ w < n + 1 + (c 0).val ∧ ¬ Relation.TransGen (fun a b : ℕ => ∃ j : Fin C.gates.length, b = n + 1 + j.val ∧ ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some a ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ a ∈ (C.gates.get j).inputs)) n w) ∧ (∀ i : Fin k, ∃ w ∈ (C.gates.get (c i.succ)).inputs, w ≠ n + 1 + (c i.castSucc).val ∧ w ≠ n ∧ w < n + 1 + (c i.succ).val ∧ ¬ Relation.TransGen (fun a b : ℕ => ∃ j : Fin C.gates.length, b = n + 1 + j.val ∧ ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some a ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ a ∈ (C.gates.get j).inputs)) n w) := by
  intro n C H hmin hn hf
  obtain ⟨a,b,hab⟩ := hn
  have hnH : ∃ x y, H x ≠ H y := ⟨a,b,hab⟩
  have nonconstant : ∃ x y, circuitFun (n+1) C x ≠ circuitFun (n+1) C y := by
    refine ⟨Fin.snoc a false, Fin.snoc b false, ?_⟩
    rw [hf, hf]
    simpa [Fin.snoc_castSucc, Fin.snoc_last] using hab
  obtain ⟨last, hlast, hout, hreach⟩ := Structure568.endpoint n C H hmin hnH hf
  have semantic := Gap568.raw_semantic_facts n C H hmin hf (by omega)
    (Gap568.minimal_material_lt hmin nonconstant) (Structure568.liveness (n+1) C hmin)
  apply Structure568.assemble n C last hlast hout (hout ▸ hreach)
  · intro w hw j k hr hs
    exact (semantic w hw k hs).1 j hr
  · intro w hw j hr
    have hor := (semantic w hw j hr).2
    exact ⟨hor, Gap568.minimal_binary_inputs hmin nonconstant j (by rw [hor]; intro h; cases h)⟩
