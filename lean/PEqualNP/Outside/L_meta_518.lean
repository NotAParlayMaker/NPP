import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.Meta518

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

private lemma ofFn_getD_lt {α : Type*} {n : ℕ} (f : Fin n → α) (d : α) (i : ℕ) (hi : i < n) :
    (List.ofFn f).getD i d = f ⟨i, hi⟩ := by
  rw [List.getD_eq_getElem _ _ (by simp [hi])]
  simp

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
    exact ⟨⟨Or.inr (Or.inr rfl), by simp [normGate]⟩, fun _ => by simp [normGate]⟩

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

private def elimGate (m : ℕ) (st : List (Bool ⊕ ℕ)) (out : List Gate) (g : Gate) :
    List (Bool ⊕ ℕ) × List Gate :=
  let args := g.inputs.map (fun i => st.getD i (Sum.inl false))
  let res :=
    match g.op with
    | GateOp.not => simpNot (m + out.length) args
    | GateOp.and => simpAnd (m + out.length) args
    | GateOp.or => simpOr (m + out.length) args
    | _ => (none, Sum.inl false)
  match res.1 with
  | none => (st ++ [res.2], out)
  | some g' => (st ++ [res.2], out ++ [g'])

private def elimPass (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) :
    List (Bool ⊕ ℕ) × List Gate :=
  gs.foldl (fun a g => elimGate m a.1 a.2 g) acc

private lemma elimGate_st_len (m : ℕ) (st : List (Bool ⊕ ℕ)) (out : List Gate) (g : Gate) :
    (elimGate m st out g).1.length = st.length + 1 := by
  unfold elimGate
  dsimp only
  split <;> simp

private lemma elimGate_out_le (m : ℕ) (st : List (Bool ⊕ ℕ)) (out : List Gate) (g : Gate) :
    (elimGate m st out g).2.length ≤ out.length + 1 := by
  unfold elimGate
  dsimp only
  split <;> simp

private lemma elimGate_ok (m : ℕ) (st : List (Bool ⊕ ℕ)) (out : List Gate) (g : Gate)
    (hout : ∀ g' ∈ out, OkGate g') :
    ∀ g' ∈ (elimGate m st out g).2, OkGate g' := by
  unfold elimGate
  dsimp only
  set args := g.inputs.map (fun i => st.getD i (Sum.inl false))
  cases hop : g.op with
  | not =>
    cases args with
    | nil => simpa [simpNot] using hout
    | cons a l =>
      cases a with
      | inl c => simpa [simpNot] using hout
      | inr j =>
        intro g' hg'
        simp only [simpNot, List.mem_append, List.mem_singleton] at hg'
        rcases hg' with hg' | rfl
        · exact hout g' hg'
        · simp [OkGate]
  | and =>
    rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
    · simpa [simpAnd] using hout
    · cases a <;> simpa [simpAnd] using hout
    · cases a <;> cases b <;> try (simpa [simpAnd] using hout)
      intro g' hg'
      simp only [simpAnd, List.mem_append, List.mem_singleton] at hg'
      rcases hg' with hg' | rfl
      · exact hout g' hg'
      · simp [OkGate]
    · simpa [simpAnd] using hout
  | or =>
    rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
    · simpa [simpOr] using hout
    · cases a <;> simpa [simpOr] using hout
    · cases a <;> cases b <;> try (simpa [simpOr] using hout)
      intro g' hg'
      simp only [simpOr, List.mem_append, List.mem_singleton] at hg'
      rcases hg' with hg' | rfl
      · exact hout g' hg'
      · simp [OkGate]
    · simpa [simpOr] using hout
  | mod _ => simpa using hout
  | maj => simpa using hout

private lemma elimPass_ok (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (hout : ∀ g' ∈ acc.2, OkGate g') :
    ∀ g' ∈ (elimPass m gs acc).2, OkGate g' := by
  induction gs generalizing acc with
  | nil => exact hout
  | cons g gs ih =>
    exact ih (elimGate m acc.1 acc.2 g) (elimGate_ok m acc.1 acc.2 g hout)

private lemma elimGate_out_le_same (m : ℕ) (st : List (Bool ⊕ ℕ)) (out : List Gate) (g : Gate)
    (hnone : ∃ i ∈ g.inputs, ∃ c : Bool, st.getD i (Sum.inl false) = Sum.inl c)
    (hnok : NOkGate g) :
    (elimGate m st out g).2.length = out.length := by
  obtain ⟨⟨hop, hlen⟩, hnotlen⟩ := hnok
  obtain ⟨i, hi, c, hc⟩ := hnone
  unfold elimGate
  dsimp only
  have hmem : Sum.inl c ∈ g.inputs.map (fun k => st.getD k (Sum.inl false)) :=
    List.mem_map.2 ⟨i, hi, hc⟩
  set args := g.inputs.map (fun k => st.getD k (Sum.inl false)) with hargs
  have hal : args.length = g.inputs.length := by simp [hargs]
  rcases hop with h | h | h
  · have : g.op = GateOp.and := h
    rw [this]
    rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simpAnd]
    · cases a <;> simp [simpAnd]
    · cases a <;> cases b <;> simp [simpAnd] at hmem ⊢
    · simp at hal; omega
  · have : g.op = GateOp.or := h
    rw [this]
    rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simpOr]
    · cases a <;> simp [simpOr]
    · cases a <;> cases b <;> simp [simpOr] at hmem ⊢
    · simp at hal; omega
  · have : g.op = GateOp.not := h
    rw [this]
    have hnl := hnotlen this
    rcases args with _ | ⟨a, _ | ⟨b, l⟩⟩
    · simp [simpNot]
    · cases a <;> simp [simpNot] at hmem ⊢
    · simp at hal; omega

private lemma elimGate_st_getD_lt (m : ℕ) (st : List (Bool ⊕ ℕ)) (out : List Gate) (g : Gate)
    (i : ℕ) (hi : i < st.length) :
    (elimGate m st out g).1.getD i (Sum.inl false) = st.getD i (Sum.inl false) := by
  unfold elimGate
  dsimp only
  split <;> exact getD_snoc_lt st _ _ i hi

private lemma elimPass_len_le (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) :
    (elimPass m gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp [elimPass]
  | cons g gs ih =>
    have h1 := ih (elimGate m acc.1 acc.2 g)
    have h2 := elimGate_out_le m acc.1 acc.2 g
    simp only [elimPass, List.foldl_cons, List.length_cons] at h1 ⊢
    omega

private def ElimInv (m : ℕ) (x : List Bool) (w : List Bool)
    (st : List (Bool ⊕ ℕ)) (out : List Gate) : Prop :=
  x.length = m ∧ st.length = w.length ∧
  ∀ i : ℕ, statValid (m + out.length) (st.getD i (Sum.inl false)) ∧
    statVal (wiresFrom out x) (st.getD i (Sum.inl false)) = w.getD i false

private lemma elimInv_gate (m : ℕ) (x w : List Bool) (st : List (Bool ⊕ ℕ)) (out : List Gate)
    (g : Gate) (hok : OkGate g) (hinv : ElimInv m x w st out) :
    ElimInv m x (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (elimGate m st out g).1 (elimGate m st out g).2 := by
  obtain ⟨hxlen, hstlen, hval⟩ := hinv
  have hwl : (wiresFrom out x).length = m + out.length := by
    rw [wiresFrom_length, hxlen]
  have harg : ∀ k, statVal (wiresFrom out x) (st.getD k (Sum.inl false)) = w.getD k false :=
    fun k => (hval k).2
  have hvalid : ∀ k, statValid (m + out.length) (st.getD k (Sum.inl false)) :=
    fun k => (hval k).1
  refine ⟨hxlen, ?_, ?_⟩
  · rw [elimGate_st_len, hstlen]; simp
  · intro i
    unfold elimGate
    dsimp only
    set args := g.inputs.map (fun k => st.getD k (Sum.inl false)) with hargs
    have heval_map : g.inputs.map (fun k => w.getD k false) =
        args.map (statVal (wiresFrom out x)) := by
      simp only [hargs, List.map_map]
      apply List.map_congr_left
      intro k _
      exact (harg k).symm
    have hargs_valid : ∀ a ∈ args, statValid (m + out.length) a := by
      intro a ha
      obtain ⟨k, _, rfl⟩ := List.mem_map.1 ha
      exact hvalid k
    have hnone_step : ∀ (r : Bool ⊕ ℕ), statValid (m + out.length) r →
        statVal (wiresFrom out x) r = g.op.eval (g.inputs.map fun k => w.getD k false) →
        statValid (m + out.length) ((st ++ [r]).getD i (Sum.inl false)) ∧
        statVal (wiresFrom out x) ((st ++ [r]).getD i (Sum.inl false)) =
          (w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]).getD i false := by
      intro r hrv hre
      by_cases hi : i = st.length
      · rw [getD_snoc_eq st r _ i hi, getD_snoc_eq w _ _ i (by omega)]
        exact ⟨hrv, hre⟩
      · rw [getD_snoc_ne st r _ i hi, getD_snoc_ne w _ _ i (by omega)]
        exact hval i
    have hsome_step : ∀ (g' : Gate),
        g'.op.eval (g'.inputs.map fun k => (wiresFrom out x).getD k false) =
          g.op.eval (g.inputs.map fun k => w.getD k false) →
        statValid (m + (out ++ [g']).length) ((st ++ [Sum.inr (m + out.length)]).getD i (Sum.inl false)) ∧
        statVal (wiresFrom (out ++ [g']) x) ((st ++ [Sum.inr (m + out.length)]).getD i (Sum.inl false)) =
          (w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]).getD i false := by
      intro g' hg'
      have hwf : wiresFrom (out ++ [g']) x =
          wiresFrom out x ++ [g'.op.eval (g'.inputs.map fun k => (wiresFrom out x).getD k false)] := by
        rw [wiresFrom_append, wiresFrom_cons, wiresFrom_nil]
      by_cases hi : i = st.length
      · rw [getD_snoc_eq st _ _ i hi, getD_snoc_eq w _ _ i (by omega)]
        refine ⟨by simp [statValid], ?_⟩
        simp only [statVal, hwf]
        rw [getD_snoc_eq _ _ _ _ hwl.symm, hg']
      · rw [getD_snoc_ne st _ _ i hi, getD_snoc_ne w _ _ i (by omega)]
        obtain ⟨hvi, hve⟩ := hval i
        cases hs : st.getD i (Sum.inl false) with
        | inl c =>
          rw [hs] at hve
          exact ⟨trivial, hve⟩
        | inr j =>
          rw [hs] at hvi hve
          refine ⟨by simp [statValid] at hvi ⊢; omega, ?_⟩
          simp only [statVal, hwf]
          rw [getD_snoc_lt _ _ _ j (by rw [hwl]; exact hvi)]
          exact hve
    obtain ⟨hop, hlen⟩ := hok
    have hal : args.length = g.inputs.length := by simp [hargs]
    rcases hop with h | h | h
    · have hg : g.op = GateOp.and := h
      rw [hg] at hnone_step hsome_step ⊢
      rcases hargs_eq : args with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
      · simpa [simpAnd] using hnone_step (Sum.inl true) trivial (by rw [heval_map, hargs_eq]; simp [GateOp.eval, statVal])
      · cases a with
        | inl ca =>
          simpa [simpAnd] using hnone_step (Sum.inl ca) trivial (by rw [heval_map, hargs_eq]; simp [GateOp.eval, statVal])
        | inr ja =>
          have hv : statValid (m + out.length) (Sum.inr ja) := hargs_valid _ (by rw [hargs_eq]; simp)
          simpa [simpAnd] using hnone_step (Sum.inr ja) hv (by rw [heval_map, hargs_eq]; simp [GateOp.eval, statVal])
      · cases a with
        | inl ca =>
          cases b with
          | inl cb =>
            simpa [simpAnd] using hnone_step (Sum.inl (ca && cb)) trivial (by rw [heval_map, hargs_eq]; simp [GateOp.eval, statVal])
          | inr jb =>
            have hv : statValid (m + out.length) (Sum.inr jb) := hargs_valid _ (by rw [hargs_eq]; simp)
            cases ca
            · simpa [simpAnd] using hnone_step (Sum.inl false) trivial (by rw [heval_map, hargs_eq]; simp [GateOp.eval, statVal])
            · simpa [simpAnd] using hnone_step (Sum.inr jb) hv (by rw [heval_map, hargs_eq]; simp [GateOp.eval, statVal])
        | inr ja =>
          cases b with
          | inl cb =>
            have hv : statValid (m + out.length) (Sum.inr ja) := hargs_valid _ (by rw [hargs_eq]; simp)
            cases cb
            · simpa [simpAnd] using hnone_step (Sum.inl false) trivial (by rw [heval_map, hargs_eq]; simp [GateOp.eval, statVal])
            · simpa [simpAnd] using hnone_step (Sum.inr ja) hv (by rw [heval_map, hargs_eq]; simp [GateOp.eval, statVal])
          | inr jb =>
            simpa [simpAnd] using hsome_step ⟨GateOp.and, [ja, jb]⟩
              (by rw [heval_map, hargs_eq]; simp [GateOp.eval, statVal])
      · rw [hargs_eq] at hal; simp at hal; omega
    · have hg : g.op = GateOp.or := h
      rw [hg] at hnone_step hsome_step ⊢
      rcases hargs_eq : args with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
      · simpa [simpOr] using hnone_step (Sum.inl false) trivial (by rw [heval_map, hargs_eq]; simp [GateOp.eval, statVal])
      · cases a with
        | inl ca =>
          simpa [simpOr] using hnone_step (Sum.inl ca) trivial (by rw [heval_map, hargs_eq]; simp [GateOp.eval, statVal])
        | inr ja =>
          have hv : statValid (m + out.length) (Sum.inr ja) := hargs_valid _ (by rw [hargs_eq]; simp)
          simpa [simpOr] using hnone_step (Sum.inr ja) hv (by rw [heval_map, hargs_eq]; simp [GateOp.eval, statVal])
      · cases a with
        | inl ca =>
          cases b with
          | inl cb =>
            simpa [simpOr] using hnone_step (Sum.inl (ca || cb)) trivial (by rw [heval_map, hargs_eq]; simp [GateOp.eval, statVal])
          | inr jb =>
            have hv : statValid (m + out.length) (Sum.inr jb) := hargs_valid _ (by rw [hargs_eq]; simp)
            cases ca
            · simpa [simpOr] using hnone_step (Sum.inr jb) hv (by rw [heval_map, hargs_eq]; simp [GateOp.eval, statVal])
            · simpa [simpOr] using hnone_step (Sum.inl true) trivial (by rw [heval_map, hargs_eq]; simp [GateOp.eval, statVal])
        | inr ja =>
          cases b with
          | inl cb =>
            have hv : statValid (m + out.length) (Sum.inr ja) := hargs_valid _ (by rw [hargs_eq]; simp)
            cases cb
            · simpa [simpOr] using hnone_step (Sum.inr ja) hv (by rw [heval_map, hargs_eq]; simp [GateOp.eval, statVal])
            · simpa [simpOr] using hnone_step (Sum.inl true) trivial (by rw [heval_map, hargs_eq]; simp [GateOp.eval, statVal])
          | inr jb =>
            simpa [simpOr] using hsome_step ⟨GateOp.or, [ja, jb]⟩
              (by rw [heval_map, hargs_eq]; simp [GateOp.eval, statVal])
      · rw [hargs_eq] at hal; simp at hal; omega
    · have hg : g.op = GateOp.not := h
      rw [hg] at hnone_step hsome_step ⊢
      rcases hargs_eq : args with _ | ⟨a, l⟩
      · simpa [simpNot] using hnone_step (Sum.inl true) trivial (by rw [heval_map, hargs_eq]; simp [GateOp.eval, statVal])
      · cases a with
        | inl ca =>
          simpa [simpNot] using hnone_step (Sum.inl (!ca)) trivial (by rw [heval_map, hargs_eq]; simp [GateOp.eval, statVal])
        | inr ja =>
          simpa [simpNot] using hsome_step ⟨GateOp.not, [ja]⟩
            (by rw [heval_map, hargs_eq]; simp [GateOp.eval, statVal])

private lemma elimInv_pass (m : ℕ) (x : List Bool) (gs : List Gate) (w : List Bool)
    (acc : List (Bool ⊕ ℕ) × List Gate)
    (hok : ∀ g ∈ gs, OkGate g)
    (hinv : ElimInv m x w acc.1 acc.2) :
    ElimInv m x (wiresFrom gs w) (elimPass m gs acc).1 (elimPass m gs acc).2 := by
  induction gs generalizing w acc with
  | nil => exact hinv
  | cons g gs ih =>
    rw [wiresFrom_cons]
    exact ih _ (elimGate m acc.1 acc.2 g) (fun g' hg' => hok g' (List.mem_cons_of_mem g hg'))
      (elimInv_gate m x w acc.1 acc.2 g (hok g (List.mem_cons_self ..)) hinv)

private def initAssign (m : ℕ) (a : Fin m → Option Bool) : List (Bool ⊕ ℕ) :=
  List.ofFn (fun i : Fin m => match a i with | some b => Sum.inl b | none => Sum.inr i.val)

private def applyAssign {m : ℕ} (a : Fin m → Option Bool) (x : Fin m → Bool) : Fin m → Bool :=
  fun i => match a i with | some b => b | none => x i

private lemma elimInv_initAssign (m : ℕ) (a : Fin m → Option Bool) (x : Fin m → Bool) :
    ElimInv m (List.ofFn x) (List.ofFn (applyAssign a x)) (initAssign m a) [] := by
  refine ⟨by simp, by simp [initAssign], fun i => ?_⟩
  by_cases hi : i < m
  · rw [initAssign, ofFn_getD_lt _ _ i hi, ofFn_getD_lt _ _ i hi]
    dsimp only [applyAssign]
    cases ha : a ⟨i, hi⟩ with
    | none =>
      refine ⟨by simp [statValid, hi], ?_⟩
      simp [statVal, wiresFrom, hi]
    | some b =>
      exact ⟨trivial, rfl⟩
  · rw [List.getD_eq_default _ _ (by simp [initAssign]; omega),
        List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

private def singleAssign {m : ℕ} (v : Fin m) (b : Bool) : Fin m → Option Bool :=
  fun i => if i = v then some b else none

private lemma applyAssign_single {m : ℕ} (v : Fin m) (b : Bool) (x : Fin m → Bool) :
    applyAssign (singleAssign v b) x = Function.update x v b := by
  ext i
  by_cases h : i = v
  · subst h; simp [applyAssign, singleAssign]
  · simp [applyAssign, singleAssign, h]

private lemma wiresFrom_agree (gs : List Gate) (S : Set ℕ) (w₁ w₂ : List Bool)
    (hlen : w₁.length = w₂.length)
    (hS : ∀ u ∈ S, u < w₁.length)
    (hinit : ∀ i, i ∉ S → w₁.getD i false = w₂.getD i false)
    (hno : ∀ g ∈ gs, ∀ i ∈ g.inputs, i ∉ S) :
    (wiresFrom gs w₁).length = (wiresFrom gs w₂).length ∧
    ∀ i, i ∉ S → (wiresFrom gs w₁).getD i false = (wiresFrom gs w₂).getD i false := by
  induction gs generalizing w₁ w₂ with
  | nil => exact ⟨hlen, hinit⟩
  | cons g gs ih =>
    have hmap : g.inputs.map (fun i => w₁.getD i false) =
        g.inputs.map (fun i => w₂.getD i false) := by
      apply List.map_congr_left
      intro i hi
      exact hinit i (hno g (List.mem_cons_self ..) i hi)
    have hlen' : (w₁ ++ [g.op.eval (g.inputs.map fun i => w₁.getD i false)]).length =
        (w₂ ++ [g.op.eval (g.inputs.map fun i => w₂.getD i false)]).length := by
      simp [hlen]
    have hS' : ∀ u ∈ S, u < (w₁ ++ [g.op.eval (g.inputs.map fun i => w₁.getD i false)]).length :=
      fun u hu => by simp; have := hS u hu; omega
    have hinit' : ∀ i, i ∉ S →
        (w₁ ++ [g.op.eval (g.inputs.map fun i => w₁.getD i false)]).getD i false =
        (w₂ ++ [g.op.eval (g.inputs.map fun i => w₂.getD i false)]).getD i false := by
      intro i hi
      by_cases he : i = w₁.length
      · rw [getD_snoc_eq _ _ _ i he, getD_snoc_eq _ _ _ i (by omega), hmap]
      · rw [getD_snoc_ne _ _ _ i he, getD_snoc_ne _ _ _ i (by omega)]
        exact hinit i hi
    exact ih _ _ hlen' hS' hinit' (fun g' hg' => hno g' (List.mem_cons_of_mem g hg'))

private def MinimalCircuit (m : ℕ) (F : (Fin m → Bool) → Bool) (C : Circuit) : Prop :=
  (∀ g ∈ C.gates, NOkGate g) ∧
  (∀ x : Fin m → Bool, C.eval (List.ofFn x) = F x) ∧
  (∀ s < C.gates.length, ¬ HasCircuitSize m F s)

private lemma exists_minimal_circuit {m s : ℕ} {F : (Fin m → Bool) → Bool}
    (h : HasCircuitSize m F s) :
    ∃ C : Circuit, MinimalCircuit m F C ∧ C.gates.length ≤ s := by
  classical
  have hex : ∃ t : ℕ, HasCircuitSize m F t := ⟨s, h⟩
  set t := Nat.find hex with ht
  have ht_le : t ≤ s := Nat.find_min' hex h
  obtain ⟨C₀, hok, hsz, hev⟩ := Nat.find_spec hex
  let C : Circuit := ⟨C₀.gates.map normGate, C₀.output⟩
  have hlen : C.gates.length = C₀.gates.length := by simp [C]
  have hnok : ∀ g ∈ C.gates, NOkGate g := by
    intro g hg
    obtain ⟨g₀, hg₀, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g₀ (hok g₀ hg₀)
  have hev' : ∀ x : Fin m → Bool, C.eval (List.ofFn x) = F x := by
    intro x
    show (wiresFrom (C₀.gates.map normGate) (List.ofFn x)).getD C₀.output false = F x
    rw [wiresFrom_norm]
    exact hev x
  have hmin : ∀ r < C.gates.length, ¬ HasCircuitSize m F r := by
    intro r hr hhas
    have htr : t ≤ r := Nat.find_min' hex hhas
    have hsz' : C₀.gates.length ≤ t := hsz
    omega
  exact ⟨C, ⟨hnok, hev', hmin⟩, by have : C₀.gates.length ≤ t := hsz; omega⟩

private def wireFn {m : ℕ} (C : Circuit) (w : ℕ) (x : Fin m → Bool) : Bool :=
  (C.wires (List.ofFn x)).getD w false

private lemma minimal_replace_gate_elim {m : ℕ} {F : (Fin m → Bool) → Bool} {C : Circuit}
    (hmin : MinimalCircuit m F C)
    (hnc : ∃ x x' : Fin m → Bool, F x ≠ F x')
    (j : ℕ) (hj : j < C.gates.length)
    (rep : Bool ⊕ ℕ) (hrep_valid : statValid (m + j) rep)
    (hrep_ok : (∀ x : Fin m → Bool,
      statVal (wiresFrom (C.gates.take j) (List.ofFn x)) rep = wireFn C (m + j) x) ∨
      (C.output ≠ m + j ∧ ∀ k, j < k → ∀ hk : k < C.gates.length,
        m + j ∉ C.gates[k].inputs)) : False := by
  obtain ⟨hnok, hev, hsmall⟩ := hmin
  let pref := C.gates.take j
  let g := C.gates[j]
  let suff := C.gates.drop (j + 1)
  have hsplit : C.gates = pref ++ [g] ++ suff := by
    have h1 := List.take_append_drop j C.gates
    have h2 : C.gates.drop j = g :: suff := List.drop_eq_getElem_cons hj
    rw [h2] at h1
    rw [← h1]
    simp [pref, List.append_assoc]
  have hpref_len : pref.length = j := List.length_take_of_le (Nat.le_of_lt hj)
  have hsuff_len : suff.length = C.gates.length - (j + 1) := by simp [suff]
  have hpref_ok : ∀ g' ∈ pref, OkGate g' := fun g' hg' =>
    (hnok g' (List.mem_of_mem_take hg')).1
  have hsuff_ok : ∀ g' ∈ suff, OkGate g' := fun g' hg' =>
    (hnok g' (List.mem_of_mem_drop hg')).1
  let st₀ : List (Bool ⊕ ℕ) := List.ofFn (fun i : Fin (m + j) => Sum.inr i.val) ++ [rep]
  set acc := elimPass m suff (st₀, pref) with hacc
  have hacc_ok : ∀ g' ∈ acc.2, OkGate g' := elimPass_ok m suff (st₀, pref) hpref_ok
  have hacc_len : acc.2.length < C.gates.length := by
    have hle := elimPass_len_le m suff (st₀, pref)
    rw [← hacc] at hle
    dsimp only at hle
    rw [hpref_len, hsuff_len] at hle
    omega
  rcases hrep_ok with hsem | ⟨hout_ne, hunused⟩
  · have hinv0 : ∀ x : Fin m → Bool,
        ElimInv m (List.ofFn x) (wiresFrom (pref ++ [g]) (List.ofFn x)) st₀ pref := by
      intro x
      have hwl : (wiresFrom pref (List.ofFn x)).length = m + j := by
        rw [wiresFrom_length, List.length_ofFn, hpref_len]
      have hwl1 : (wiresFrom (pref ++ [g]) (List.ofFn x)).length = m + j + 1 := by
        rw [wiresFrom_length, List.length_ofFn, List.length_append, hpref_len]; simp; omega
      refine ⟨by simp, by simp [st₀, hwl1], fun i => ?_⟩
      by_cases hi : i < m + j
      · rw [getD_snoc_lt _ _ _ i (by simp; exact hi)]
        rw [ofFn_getD_lt _ _ i hi]
        refine ⟨by simp [statValid, hpref_len, hi], ?_⟩
        simp only [statVal]
        rw [wiresFrom_append, wiresFrom_cons, wiresFrom_nil, getD_snoc_lt _ _ _ i (by omega)]
      · by_cases heq : i = m + j
        · subst heq
          rw [getD_snoc_eq _ _ _ (m + j) (by simp)]
          refine ⟨by simpa [hpref_len] using hrep_valid, ?_⟩
          rw [hsem x]
          simp only [wireFn, Circuit.wires]
          show (wiresFrom C.gates (List.ofFn x)).getD (m + j) false =
            (wiresFrom (pref ++ [g]) (List.ofFn x)).getD (m + j) false
          rw [hsplit, wiresFrom_append, wiresFrom_getD_lt _ _ _ (by omega)]
        · rw [List.getD_eq_default _ _ (by simp [st₀]; omega),
              List.getD_eq_default _ _ (by omega)]
          exact ⟨trivial, rfl⟩
    have hval : ∀ x : Fin m → Bool,
        statVal (wiresFrom acc.2 (List.ofFn x)) (acc.1.getD C.output (Sum.inl false)) = F x := by
      intro x
      have hinv := elimInv_pass m (List.ofFn x) suff _ (st₀, pref) hsuff_ok (hinv0 x)
      rw [← hacc] at hinv
      have hwf : wiresFrom suff (wiresFrom (pref ++ [g]) (List.ofFn x)) = C.wires (List.ofFn x) := by
        show wiresFrom suff (wiresFrom (pref ++ [g]) (List.ofFn x)) = wiresFrom C.gates (List.ofFn x)
        conv_rhs => rw [hsplit, wiresFrom_append]
      rw [(hinv.2.2 C.output).2, hwf]
      exact hev x
    cases hst : acc.1.getD C.output (Sum.inl false) with
    | inl c =>
      obtain ⟨x, x', hne⟩ := hnc
      have hx := hval x; have hx' := hval x'
      rw [hst] at hx hx'
      exact hne (hx.symm.trans hx')
    | inr outw =>
      apply hsmall acc.2.length hacc_len
      refine ⟨⟨acc.2, outw⟩, hacc_ok, le_rfl, fun x => ?_⟩
      have := hval x; rw [hst] at this; exact this
  · let w₂ (x : Fin m → Bool) := wiresFrom pref (List.ofFn x) ++ [false]
    have hinv0 : ∀ x : Fin m → Bool,
        ElimInv m (List.ofFn x) (w₂ x) (List.ofFn (fun i : Fin (m + j) => Sum.inr i.val) ++ [Sum.inl false]) pref := by
      intro x
      have hwl : (wiresFrom pref (List.ofFn x)).length = m + j := by
        rw [wiresFrom_length, List.length_ofFn, hpref_len]
      refine ⟨by simp, by simp [w₂, hwl], fun i => ?_⟩
      by_cases hi : i < m + j
      · rw [getD_snoc_lt _ _ _ i (by simp; exact hi), ofFn_getD_lt _ _ i hi]
        refine ⟨by simp [statValid, hpref_len, hi], ?_⟩
        simp only [statVal, w₂]
        rw [getD_snoc_lt _ _ _ i (by omega)]
      · by_cases heq : i = m + j
        · subst heq
          rw [getD_snoc_eq _ _ _ (m + j) (by simp)]
          simp only [w₂, statVal, statValid, true_and]
          rw [getD_snoc_eq _ _ _ _ hwl.symm]
        · rw [List.getD_eq_default _ _ (by simp; omega),
              List.getD_eq_default _ _ (by simp [w₂, hwl]; omega)]
          exact ⟨trivial, rfl⟩
    let st₁ := List.ofFn (fun i : Fin (m + j) => Sum.inr i.val) ++ [Sum.inl false]
    set acc₁ := elimPass m suff (st₁, pref) with hacc₁
    have hacc₁_ok : ∀ g' ∈ acc₁.2, OkGate g' := elimPass_ok m suff (st₁, pref) hpref_ok
    have hacc₁_len : acc₁.2.length < C.gates.length := by
      have hle := elimPass_len_le m suff (st₁, pref)
      rw [← hacc₁] at hle
      dsimp only at hle
      rw [hpref_len, hsuff_len] at hle
      omega
    have hsuff_no : ∀ g' ∈ suff, ∀ i ∈ g'.inputs, i ∉ ({m + j} : Set ℕ) := by
      intro g' hg' i hi hmem
      simp only [Set.mem_singleton_iff] at hmem
      subst hmem
      obtain ⟨k, hk, hgk⟩ := List.mem_iff_getElem.1 hg'
      have hkj : j + 1 + k < C.gates.length := by simp [suff] at hk; omega
      have hget : C.gates[j + 1 + k] = g' := by
        rw [← hgk]; simp [suff]
      exact hunused (j + 1 + k) (by omega) hkj (hget.symm ▸ hi)
    have hval : ∀ x : Fin m → Bool,
        statVal (wiresFrom acc₁.2 (List.ofFn x)) (acc₁.1.getD C.output (Sum.inl false)) = F x := by
      intro x
      have hinv := elimInv_pass m (List.ofFn x) suff (w₂ x) (st₁, pref) hsuff_ok (hinv0 x)
      rw [← hacc₁] at hinv
      rw [(hinv.2.2 C.output).2]
      have hwl : (wiresFrom pref (List.ofFn x)).length = m + j := by
        rw [wiresFrom_length, List.length_ofFn, hpref_len]
      have hag := wiresFrom_agree suff {m + j} (w₂ x) (wiresFrom (pref ++ [g]) (List.ofFn x))
        (by rw [wiresFrom_append, wiresFrom_cons, wiresFrom_nil]; simp [w₂])
        (by intro u hu; simp at hu; subst hu; simp [w₂, hwl])
        (by
          intro i hi
          simp only [Set.mem_singleton_iff] at hi
          rw [wiresFrom_append, wiresFrom_cons, wiresFrom_nil]
          simp only [w₂]
          rw [getD_snoc_ne _ _ _ i (by omega), getD_snoc_ne _ _ _ i (by omega)])
        hsuff_no
      have hEq := hag.2 C.output (by simpa using hout_ne)
      rw [hEq]
      have hwf : wiresFrom suff (wiresFrom (pref ++ [g]) (List.ofFn x)) = C.wires (List.ofFn x) := by
        show wiresFrom suff (wiresFrom (pref ++ [g]) (List.ofFn x)) = wiresFrom C.gates (List.ofFn x)
        conv_rhs => rw [hsplit, wiresFrom_append]
      rw [hwf]
      exact hev x
    cases hst : acc₁.1.getD C.output (Sum.inl false) with
    | inl c =>
      obtain ⟨x, x', hne⟩ := hnc
      have hx := hval x; have hx' := hval x'
      rw [hst] at hx hx'
      exact hne (hx.symm.trans hx')
    | inr outw =>
      apply hsmall acc₁.2.length hacc₁_len
      refine ⟨⟨acc₁.2, outw⟩, hacc₁_ok, le_rfl, fun x => ?_⟩
      have := hval x; rw [hst] at this; exact this

private lemma minimal_wire_nonconst {m : ℕ} {F : (Fin m → Bool) → Bool} {C : Circuit}
    (hmin : MinimalCircuit m F C)
    (hnc : ∃ x x' : Fin m → Bool, F x ≠ F x')
    (j : ℕ) (hj : j < C.gates.length) (c : Bool) :
    ∃ x : Fin m → Bool, wireFn C (m + j) x ≠ c := by
  by_contra hall
  push Not at hall
  exact minimal_replace_gate_elim hmin hnc j hj (Sum.inl c) trivial
    (Or.inl (fun x => (hall x).symm))

private lemma minimal_wire_ne_earlier {m : ℕ} {F : (Fin m → Bool) → Bool} {C : Circuit}
    (hmin : MinimalCircuit m F C)
    (hnc : ∃ x x' : Fin m → Bool, F x ≠ F x')
    (j : ℕ) (hj : j < C.gates.length) (w : ℕ) (hw : w < m + j) :
    ∃ x : Fin m → Bool, wireFn C (m + j) x ≠ wireFn C w x := by
  by_contra hall
  push Not at hall
  apply minimal_replace_gate_elim hmin hnc j hj (Sum.inr w) hw (Or.inl ?_)
  intro x
  rw [hall x]
  simp only [statVal, wireFn, Circuit.wires]
  have hsplit : C.gates = C.gates.take j ++ C.gates.drop j := (List.take_append_drop j C.gates).symm
  have hpref_len : (C.gates.take j).length = j := List.length_take_of_le (Nat.le_of_lt hj)
  have hwl : (wiresFrom (C.gates.take j) (List.ofFn x)).length = m + j := by
    rw [wiresFrom_length, List.length_ofFn, hpref_len]
  show (wiresFrom (C.gates.take j) (List.ofFn x)).getD w false =
    (wiresFrom C.gates (List.ofFn x)).getD w false
  conv_rhs => rw [hsplit, wiresFrom_append]
  exact (wiresFrom_getD_lt (C.gates.drop j) (wiresFrom (C.gates.take j) (List.ofFn x)) w (by omega)).symm

private lemma minimal_gate_used {m : ℕ} {F : (Fin m → Bool) → Bool} {C : Circuit}
    (hmin : MinimalCircuit m F C)
    (hnc : ∃ x x' : Fin m → Bool, F x ≠ F x')
    (j : ℕ) (hj : j < C.gates.length) (hout : C.output ≠ m + j) :
    ∃ k, j < k ∧ ∃ hk : k < C.gates.length, m + j ∈ C.gates[k].inputs := by
  by_contra hno
  push Not at hno
  exact minimal_replace_gate_elim hmin hnc j hj (Sum.inl false) trivial
    (Or.inr ⟨hout, fun k hjk hk => hno k hjk hk⟩)

private lemma wireFn_gate {m : ℕ} (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
    (x : Fin m → Bool) :
    wireFn C (m + j) x =
      C.gates[j].op.eval (C.gates[j].inputs.map fun i => if i < m + j then wireFn C i x else false) := by
  have hsplit : C.gates = C.gates.take j ++ [C.gates[j]] ++ C.gates.drop (j + 1) := by
    have h1 := List.take_append_drop j C.gates
    have h2 : C.gates.drop j = C.gates[j] :: C.gates.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [h2] at h1
    exact h1.symm.trans (by simp)
  have hpref_len : (C.gates.take j).length = j := List.length_take_of_le (Nat.le_of_lt hj)
  have hwl : (wiresFrom (C.gates.take j) (List.ofFn x)).length = m + j := by
    rw [wiresFrom_length, List.length_ofFn, hpref_len]
  simp only [wireFn, Circuit.wires]
  show (wiresFrom C.gates (List.ofFn x)).getD (m + j) false = _
  conv_lhs => rw [hsplit, wiresFrom_append, wiresFrom_append, wiresFrom_cons, wiresFrom_nil]
  rw [wiresFrom_getD_lt _ _ (m + j) (by simp [hwl]), getD_snoc_eq _ _ _ (m + j) hwl.symm]
  congr 1
  apply List.map_congr_left
  intro i _
  by_cases hi : i < m + j
  · simp only [hi, ↓reduceIte]
    show (wiresFrom (C.gates.take j) (List.ofFn x)).getD i false =
      (wiresFrom C.gates (List.ofFn x)).getD i false
    have hsplit2 : C.gates = C.gates.take j ++ C.gates.drop j := (List.take_append_drop j C.gates).symm
    conv_rhs => rw [hsplit2, wiresFrom_append]
    exact (wiresFrom_getD_lt (C.gates.drop j) (wiresFrom (C.gates.take j) (List.ofFn x)) i (by omega)).symm
  · simp only [hi, ↓reduceIte]
    exact List.getD_eq_default _ _ (by omega)

private lemma minimal_gate_shape {m : ℕ} {F : (Fin m → Bool) → Bool} {C : Circuit}
    (hmin : MinimalCircuit m F C)
    (hnc : ∃ x x' : Fin m → Bool, F x ≠ F x')
    (j : ℕ) (hj : j < C.gates.length) :
    (C.gates[j].op = GateOp.not ∧ ∃ a < m + j, C.gates[j].inputs = [a]) ∨
    ((C.gates[j].op = GateOp.and ∨ C.gates[j].op = GateOp.or) ∧
      ∃ a b, a < m + j ∧ b < m + j ∧ a ≠ b ∧ C.gates[j].inputs = [a, b]) := by
  have hnok := hmin.1 C.gates[j] (List.getElem_mem hj)
  obtain ⟨⟨hop, hlen⟩, hnotlen⟩ := hnok
  rcases hop with h | h | h
  · have hop_and : C.gates[j].op = GateOp.and := h
    rcases hin : C.gates[j].inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
    · exfalso
      obtain ⟨x, hx⟩ := minimal_wire_nonconst hmin hnc j hj true
      rw [wireFn_gate C j hj x, hop_and, hin] at hx
      exact hx rfl
    · exfalso
      by_cases ha : a < m + j
      · obtain ⟨x, hx⟩ := minimal_wire_ne_earlier hmin hnc j hj a ha
        rw [wireFn_gate C j hj x, hop_and, hin] at hx
        simp [GateOp.eval, ha] at hx
      · obtain ⟨x, hx⟩ := minimal_wire_nonconst hmin hnc j hj false
        rw [wireFn_gate C j hj x, hop_and, hin] at hx
        simp [GateOp.eval, ha] at hx
    · by_cases ha : a < m + j
      · by_cases hb : b < m + j
        · by_cases hab : a = b
          · exfalso
            subst hab
            obtain ⟨x, hx⟩ := minimal_wire_ne_earlier hmin hnc j hj a ha
            rw [wireFn_gate C j hj x, hop_and, hin] at hx
            simp [GateOp.eval, ha] at hx
          · exact Or.inr ⟨Or.inl hop_and, a, b, ha, hb, hab, rfl⟩
        · exfalso
          obtain ⟨x, hx⟩ := minimal_wire_nonconst hmin hnc j hj false
          rw [wireFn_gate C j hj x, hop_and, hin] at hx
          simp [GateOp.eval, hb] at hx
      · exfalso
        obtain ⟨x, hx⟩ := minimal_wire_nonconst hmin hnc j hj false
        rw [wireFn_gate C j hj x, hop_and, hin] at hx
        simp [GateOp.eval, ha] at hx
    · rw [hin] at hlen; simp at hlen
  · have hop_or : C.gates[j].op = GateOp.or := h
    rcases hin : C.gates[j].inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
    · exfalso
      obtain ⟨x, hx⟩ := minimal_wire_nonconst hmin hnc j hj false
      rw [wireFn_gate C j hj x, hop_or, hin] at hx
      exact hx rfl
    · exfalso
      by_cases ha : a < m + j
      · obtain ⟨x, hx⟩ := minimal_wire_ne_earlier hmin hnc j hj a ha
        rw [wireFn_gate C j hj x, hop_or, hin] at hx
        simp [GateOp.eval, ha] at hx
      · obtain ⟨x, hx⟩ := minimal_wire_nonconst hmin hnc j hj false
        rw [wireFn_gate C j hj x, hop_or, hin] at hx
        simp [GateOp.eval, ha] at hx
    · by_cases ha : a < m + j
      · by_cases hb : b < m + j
        · by_cases hab : a = b
          · exfalso
            subst hab
            obtain ⟨x, hx⟩ := minimal_wire_ne_earlier hmin hnc j hj a ha
            rw [wireFn_gate C j hj x, hop_or, hin] at hx
            simp [GateOp.eval, ha] at hx
          · exact Or.inr ⟨Or.inr hop_or, a, b, ha, hb, hab, rfl⟩
        · exfalso
          obtain ⟨x, hx⟩ := minimal_wire_ne_earlier hmin hnc j hj a ha
          rw [wireFn_gate C j hj x, hop_or, hin] at hx
          simp [GateOp.eval, ha, hb] at hx
      · exfalso
        by_cases hb : b < m + j
        · obtain ⟨x, hx⟩ := minimal_wire_ne_earlier hmin hnc j hj b hb
          rw [wireFn_gate C j hj x, hop_or, hin] at hx
          simp [GateOp.eval, ha, hb] at hx
        · obtain ⟨x, hx⟩ := minimal_wire_nonconst hmin hnc j hj false
          rw [wireFn_gate C j hj x, hop_or, hin] at hx
          simp [GateOp.eval, ha, hb] at hx
    · rw [hin] at hlen; simp at hlen
  · have hop_not : C.gates[j].op = GateOp.not := h
    have hnl := hnotlen hop_not
    rcases hin : C.gates[j].inputs with _ | ⟨a, _ | ⟨b, l⟩⟩
    · exfalso
      obtain ⟨x, hx⟩ := minimal_wire_nonconst hmin hnc j hj true
      rw [wireFn_gate C j hj x, hop_not, hin] at hx
      exact hx rfl
    · by_cases ha : a < m + j
      · exact Or.inl ⟨hop_not, a, ha, rfl⟩
      · exfalso
        obtain ⟨x, hx⟩ := minimal_wire_nonconst hmin hnc j hj true
        rw [wireFn_gate C j hj x, hop_not, hin] at hx
        simp [GateOp.eval, ha] at hx
    · rw [hin] at hnl; simp at hnl

private def runAt (m : ℕ) (gs : List Gate) (st₀ : List (Bool ⊕ ℕ)) (k : ℕ) :
    List (Bool ⊕ ℕ) × List Gate :=
  elimPass m (gs.take k) (st₀, [])

private lemma runAt_zero (m : ℕ) (gs : List Gate) (st₀ : List (Bool ⊕ ℕ)) :
    runAt m gs st₀ 0 = (st₀, []) := rfl

private lemma elimPass_append (m : ℕ) (gs₁ gs₂ : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) :
    elimPass m (gs₁ ++ gs₂) acc = elimPass m gs₂ (elimPass m gs₁ acc) := by
  simp [elimPass, List.foldl_append]

private lemma runAt_succ (m : ℕ) (gs : List Gate) (st₀ : List (Bool ⊕ ℕ))
    (k : ℕ) (hk : k < gs.length) :
    runAt m gs st₀ (k + 1) =
      elimGate m (runAt m gs st₀ k).1 (runAt m gs st₀ k).2 gs[k] := by
  unfold runAt
  rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some, elimPass_append]
  rfl

private lemma runAt_st_len (m : ℕ) (gs : List Gate) (st₀ : List (Bool ⊕ ℕ)) (k : ℕ)
    (hk : k ≤ gs.length) :
    (runAt m gs st₀ k).1.length = st₀.length + k := by
  induction k with
  | zero => simp [runAt_zero]
  | succ k ih =>
    rw [runAt_succ m gs st₀ k (by omega), elimGate_st_len, ih (by omega)]
    omega

private lemma runAt_st_getD_mono (m : ℕ) (gs : List Gate) (st₀ : List (Bool ⊕ ℕ))
    (k₁ k₂ : ℕ) (hk₁₂ : k₁ ≤ k₂) (hk₂ : k₂ ≤ gs.length) (w : ℕ) (hw : w < st₀.length + k₁) :
    (runAt m gs st₀ k₂).1.getD w (Sum.inl false) =
      (runAt m gs st₀ k₁).1.getD w (Sum.inl false) := by
  induction k₂ with
  | zero =>
    have h0 : k₁ = 0 := by omega
    subst h0; rfl
  | succ k ih =>
    by_cases hle : k₁ ≤ k
    · rw [runAt_succ m gs st₀ k (by omega), elimGate_st_getD_lt]
      · exact ih hle (by omega)
      · rw [runAt_st_len m gs st₀ k (by omega)]; omega
    · have heq : k₁ = k + 1 := by omega
      subst heq; rfl

private def finalSt (m : ℕ) (gs : List Gate) (st₀ : List (Bool ⊕ ℕ)) (w : ℕ) : Bool ⊕ ℕ :=
  (runAt m gs st₀ gs.length).1.getD w (Sum.inl false)

private lemma runAt_st_getD_eq_finalSt (m : ℕ) (gs : List Gate) (st₀ : List (Bool ⊕ ℕ))
    (k : ℕ) (hk : k ≤ gs.length) (w : ℕ) (hw : w < st₀.length + k) :
    (runAt m gs st₀ k).1.getD w (Sum.inl false) = finalSt m gs st₀ w :=
  (runAt_st_getD_mono m gs st₀ k gs.length hk le_rfl w hw).symm

private lemma finalSt_init (m : ℕ) (gs : List Gate) (st₀ : List (Bool ⊕ ℕ))
    (w : ℕ) (hw : w < st₀.length) :
    finalSt m gs st₀ w = st₀.getD w (Sum.inl false) := by
  rw [← runAt_st_getD_eq_finalSt m gs st₀ 0 (Nat.zero_le _) w (by omega)]
  rfl

private def isElim (m : ℕ) (gs : List Gate) (st₀ : List (Bool ⊕ ℕ)) (k : Fin gs.length) : Bool :=
  decide ((runAt m gs st₀ (k.val + 1)).2.length = (runAt m gs st₀ k.val).2.length)

private lemma elimGate_out_len_cases (m : ℕ) (st : List (Bool ⊕ ℕ)) (out : List Gate) (g : Gate) :
    (elimGate m st out g).2.length = out.length ∨
    (elimGate m st out g).2.length = out.length + 1 := by
  unfold elimGate
  dsimp only
  split <;> simp

private lemma runAt_out_step (m : ℕ) (gs : List Gate) (st₀ : List (Bool ⊕ ℕ))
    (k : Fin gs.length) :
    (runAt m gs st₀ (k.val + 1)).2.length =
      (runAt m gs st₀ k.val).2.length + (if isElim m gs st₀ k = true then 0 else 1) := by
  unfold isElim
  rw [runAt_succ m gs st₀ k.val k.isLt]
  rcases elimGate_out_len_cases m (runAt m gs st₀ k.val).1 (runAt m gs st₀ k.val).2 gs[k.val] with h | h <;>
    simp [h]

private lemma elim_card_add_len (m : ℕ) (gs : List Gate) (st₀ : List (Bool ⊕ ℕ)) :
    (runAt m gs st₀ gs.length).2.length +
      (Finset.univ.filter (fun k : Fin gs.length => isElim m gs st₀ k = true)).card =
      gs.length := by
  have haux : ∀ n (hn : n ≤ gs.length),
      (runAt m gs st₀ n).2.length +
        (Finset.univ.filter (fun k : Fin gs.length => k.val < n ∧ isElim m gs st₀ k = true)).card = n := by
    intro n
    induction n with
    | zero =>
      intro _
      simp [runAt_zero]
    | succ n ih =>
      intro hn
      have hstep := runAt_out_step m gs st₀ ⟨n, by omega⟩
      have hfil : Finset.univ.filter (fun k : Fin gs.length => k.val < n + 1 ∧ isElim m gs st₀ k = true) =
          (if isElim m gs st₀ ⟨n, by omega⟩ = true then
            insert ⟨n, by omega⟩ (Finset.univ.filter (fun k : Fin gs.length => k.val < n ∧ isElim m gs st₀ k = true))
          else
            Finset.univ.filter (fun k : Fin gs.length => k.val < n ∧ isElim m gs st₀ k = true)) := by
        split_ifs with he
        · ext k
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
          constructor
          · intro ⟨hlt, hke⟩
            by_cases hkn : k.val = n
            · exact Or.inl hkn
            · exact Or.inr ⟨by omega, hke⟩
          · rintro (hkn | ⟨hlt, hke⟩)
            · refine ⟨by omega, ?_⟩
              have : k = ⟨n, by omega⟩ := Fin.ext hkn
              rw [this]; exact he
            · exact ⟨by omega, hke⟩
        · ext k
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · intro ⟨hlt, hke⟩
            refine ⟨?_, hke⟩
            by_contra hge
            have hkn : k = ⟨n, by omega⟩ := Fin.ext (by show k.val = n; omega)
            rw [hkn] at hke
            exact he hke
          · intro ⟨hlt, hke⟩
            exact ⟨by omega, hke⟩
      rw [hfil]
      have hstep' : (runAt m gs st₀ (n + 1)).2.length =
          (runAt m gs st₀ n).2.length + (if isElim m gs st₀ ⟨n, by omega⟩ = true then 0 else 1) := hstep
      rw [hstep']
      have hih := ih (by omega)
      cases he : isElim m gs st₀ ⟨n, by omega⟩
      · simp only [Bool.false_eq_true, ↓reduceIte]
        omega
      · simp only [↓reduceIte]
        rw [Finset.card_insert_of_notMem (by simp)]
        omega
  have htop := haux gs.length le_rfl
  have heq : Finset.univ.filter (fun k : Fin gs.length => k.val < gs.length ∧ isElim m gs st₀ k = true) =
      Finset.univ.filter (fun k : Fin gs.length => isElim m gs st₀ k = true) := by
    ext k; simp
  rw [heq] at htop
  exact htop

private lemma runAt_step_not (m : ℕ) (gs : List Gate) (st₀ : List (Bool ⊕ ℕ))
    (hst₀ : st₀.length = m) (k : Fin gs.length)
    (a : ℕ) (ha : a < m + k.val) (hg : gs[k.val] = ⟨GateOp.not, [a]⟩) :
    match finalSt m gs st₀ a with
    | Sum.inl c =>
      isElim m gs st₀ k = true ∧ finalSt m gs st₀ (m + k.val) = Sum.inl (!c)
    | Sum.inr ja =>
      isElim m gs st₀ k = false ∧
      finalSt m gs st₀ (m + k.val) = Sum.inr (m + (runAt m gs st₀ k.val).2.length) ∧
      (runAt m gs st₀ (k.val + 1)).2 = (runAt m gs st₀ k.val).2 ++ [⟨GateOp.not, [ja]⟩] := by
  have hfa : (runAt m gs st₀ k.val).1.getD a (Sum.inl false) = finalSt m gs st₀ a :=
    runAt_st_getD_eq_finalSt m gs st₀ k.val (Nat.le_of_lt k.isLt) a (by omega)
  have hfk : finalSt m gs st₀ (m + k.val) = (runAt m gs st₀ (k.val + 1)).1.getD (m + k.val) (Sum.inl false) :=
    (runAt_st_getD_eq_finalSt m gs st₀ (k.val + 1) k.isLt (m + k.val) (by omega)).symm
  have hlen : (runAt m gs st₀ k.val).1.length = m + k.val := by
    rw [runAt_st_len m gs st₀ k.val (Nat.le_of_lt k.isLt), hst₀]
  cases h : finalSt m gs st₀ a with
  | inl c =>
    rw [h] at hfa
    dsimp only
    constructor
    · unfold isElim
      rw [runAt_succ m gs st₀ k.val k.isLt, hg]
      simp only [elimGate, List.map_cons, List.map_nil, hfa, simpNot]; simp
    · rw [hfk, runAt_succ m gs st₀ k.val k.isLt, hg]
      simp only [elimGate, List.map_cons, List.map_nil, hfa, simpNot]
      exact getD_snoc_eq _ _ _ (m + k.val) hlen.symm
  | inr ja =>
    rw [h] at hfa
    dsimp only
    refine ⟨?_, ?_, ?_⟩
    · unfold isElim
      rw [runAt_succ m gs st₀ k.val k.isLt, hg]
      simp only [elimGate, List.map_cons, List.map_nil, hfa, simpNot]; simp
    · rw [hfk, runAt_succ m gs st₀ k.val k.isLt, hg]
      simp only [elimGate, List.map_cons, List.map_nil, hfa, simpNot]
      exact getD_snoc_eq _ _ _ (m + k.val) hlen.symm
    · rw [runAt_succ m gs st₀ k.val k.isLt, hg]
      simp only [elimGate, List.map_cons, List.map_nil, hfa, simpNot]

private lemma runAt_step_and (m : ℕ) (gs : List Gate) (st₀ : List (Bool ⊕ ℕ))
    (hst₀ : st₀.length = m) (k : Fin gs.length)
    (a b : ℕ) (ha : a < m + k.val) (hb : b < m + k.val) (hg : gs[k.val] = ⟨GateOp.and, [a, b]⟩) :
    match finalSt m gs st₀ a, finalSt m gs st₀ b with
    | Sum.inl ca, Sum.inl cb =>
      isElim m gs st₀ k = true ∧ finalSt m gs st₀ (m + k.val) = Sum.inl (ca && cb)
    | Sum.inl ca, Sum.inr jb =>
      isElim m gs st₀ k = true ∧
      finalSt m gs st₀ (m + k.val) = (bif ca then Sum.inr jb else Sum.inl false)
    | Sum.inr ja, Sum.inl cb =>
      isElim m gs st₀ k = true ∧
      finalSt m gs st₀ (m + k.val) = (bif cb then Sum.inr ja else Sum.inl false)
    | Sum.inr ja, Sum.inr jb =>
      isElim m gs st₀ k = false ∧
      finalSt m gs st₀ (m + k.val) = Sum.inr (m + (runAt m gs st₀ k.val).2.length) ∧
      (runAt m gs st₀ (k.val + 1)).2 = (runAt m gs st₀ k.val).2 ++ [⟨GateOp.and, [ja, jb]⟩] := by
  have hfa : (runAt m gs st₀ k.val).1.getD a (Sum.inl false) = finalSt m gs st₀ a :=
    runAt_st_getD_eq_finalSt m gs st₀ k.val (Nat.le_of_lt k.isLt) a (by omega)
  have hfb : (runAt m gs st₀ k.val).1.getD b (Sum.inl false) = finalSt m gs st₀ b :=
    runAt_st_getD_eq_finalSt m gs st₀ k.val (Nat.le_of_lt k.isLt) b (by omega)
  have hfk : finalSt m gs st₀ (m + k.val) = (runAt m gs st₀ (k.val + 1)).1.getD (m + k.val) (Sum.inl false) :=
    (runAt_st_getD_eq_finalSt m gs st₀ (k.val + 1) k.isLt (m + k.val) (by omega)).symm
  have hlen : (runAt m gs st₀ k.val).1.length = m + k.val := by
    rw [runAt_st_len m gs st₀ k.val (Nat.le_of_lt k.isLt), hst₀]
  cases h1 : finalSt m gs st₀ a <;> cases h2 : finalSt m gs st₀ b
  · rw [h1] at hfa; rw [h2] at hfb; dsimp only
    constructor
    · unfold isElim; rw [runAt_succ m gs st₀ k.val k.isLt, hg]
      simp only [elimGate, List.map_cons, List.map_nil, hfa, hfb, simpAnd]; simp
    · rw [hfk, runAt_succ m gs st₀ k.val k.isLt, hg]
      simp only [elimGate, List.map_cons, List.map_nil, hfa, hfb, simpAnd]
      exact getD_snoc_eq _ _ _ (m + k.val) hlen.symm
  · rw [h1] at hfa; rw [h2] at hfb; dsimp only
    constructor
    · unfold isElim; rw [runAt_succ m gs st₀ k.val k.isLt, hg]
      simp only [elimGate, List.map_cons, List.map_nil, hfa, hfb, simpAnd]; simp
    · rw [hfk, runAt_succ m gs st₀ k.val k.isLt, hg]
      simp only [elimGate, List.map_cons, List.map_nil, hfa, hfb, simpAnd]
      exact getD_snoc_eq _ _ _ (m + k.val) hlen.symm
  · rw [h1] at hfa; rw [h2] at hfb; dsimp only
    constructor
    · unfold isElim; rw [runAt_succ m gs st₀ k.val k.isLt, hg]
      simp only [elimGate, List.map_cons, List.map_nil, hfa, hfb, simpAnd]; simp
    · rw [hfk, runAt_succ m gs st₀ k.val k.isLt, hg]
      simp only [elimGate, List.map_cons, List.map_nil, hfa, hfb, simpAnd]
      exact getD_snoc_eq _ _ _ (m + k.val) hlen.symm
  · rw [h1] at hfa; rw [h2] at hfb; dsimp only
    refine ⟨?_, ?_, ?_⟩
    · unfold isElim; rw [runAt_succ m gs st₀ k.val k.isLt, hg]
      simp only [elimGate, List.map_cons, List.map_nil, hfa, hfb, simpAnd]; simp
    · rw [hfk, runAt_succ m gs st₀ k.val k.isLt, hg]
      simp only [elimGate, List.map_cons, List.map_nil, hfa, hfb, simpAnd]
      exact getD_snoc_eq _ _ _ (m + k.val) hlen.symm
    · rw [runAt_succ m gs st₀ k.val k.isLt, hg]
      simp only [elimGate, List.map_cons, List.map_nil, hfa, hfb, simpAnd]

private lemma runAt_step_or (m : ℕ) (gs : List Gate) (st₀ : List (Bool ⊕ ℕ))
    (hst₀ : st₀.length = m) (k : Fin gs.length)
    (a b : ℕ) (ha : a < m + k.val) (hb : b < m + k.val) (hg : gs[k.val] = ⟨GateOp.or, [a, b]⟩) :
    match finalSt m gs st₀ a, finalSt m gs st₀ b with
    | Sum.inl ca, Sum.inl cb =>
      isElim m gs st₀ k = true ∧ finalSt m gs st₀ (m + k.val) = Sum.inl (ca || cb)
    | Sum.inl ca, Sum.inr jb =>
      isElim m gs st₀ k = true ∧
      finalSt m gs st₀ (m + k.val) = (bif ca then Sum.inl true else Sum.inr jb)
    | Sum.inr ja, Sum.inl cb =>
      isElim m gs st₀ k = true ∧
      finalSt m gs st₀ (m + k.val) = (bif cb then Sum.inl true else Sum.inr ja)
    | Sum.inr ja, Sum.inr jb =>
      isElim m gs st₀ k = false ∧
      finalSt m gs st₀ (m + k.val) = Sum.inr (m + (runAt m gs st₀ k.val).2.length) ∧
      (runAt m gs st₀ (k.val + 1)).2 = (runAt m gs st₀ k.val).2 ++ [⟨GateOp.or, [ja, jb]⟩] := by
  have hfa : (runAt m gs st₀ k.val).1.getD a (Sum.inl false) = finalSt m gs st₀ a :=
    runAt_st_getD_eq_finalSt m gs st₀ k.val (Nat.le_of_lt k.isLt) a (by omega)
  have hfb : (runAt m gs st₀ k.val).1.getD b (Sum.inl false) = finalSt m gs st₀ b :=
    runAt_st_getD_eq_finalSt m gs st₀ k.val (Nat.le_of_lt k.isLt) b (by omega)
  have hfk : finalSt m gs st₀ (m + k.val) = (runAt m gs st₀ (k.val + 1)).1.getD (m + k.val) (Sum.inl false) :=
    (runAt_st_getD_eq_finalSt m gs st₀ (k.val + 1) k.isLt (m + k.val) (by omega)).symm
  have hlen : (runAt m gs st₀ k.val).1.length = m + k.val := by
    rw [runAt_st_len m gs st₀ k.val (Nat.le_of_lt k.isLt), hst₀]
  cases h1 : finalSt m gs st₀ a <;> cases h2 : finalSt m gs st₀ b
  · rw [h1] at hfa; rw [h2] at hfb; dsimp only
    constructor
    · unfold isElim; rw [runAt_succ m gs st₀ k.val k.isLt, hg]
      simp only [elimGate, List.map_cons, List.map_nil, hfa, hfb, simpOr]; simp
    · rw [hfk, runAt_succ m gs st₀ k.val k.isLt, hg]
      simp only [elimGate, List.map_cons, List.map_nil, hfa, hfb, simpOr]
      exact getD_snoc_eq _ _ _ (m + k.val) hlen.symm
  · rw [h1] at hfa; rw [h2] at hfb; dsimp only
    constructor
    · unfold isElim; rw [runAt_succ m gs st₀ k.val k.isLt, hg]
      simp only [elimGate, List.map_cons, List.map_nil, hfa, hfb, simpOr]; simp
    · rw [hfk, runAt_succ m gs st₀ k.val k.isLt, hg]
      simp only [elimGate, List.map_cons, List.map_nil, hfa, hfb, simpOr]
      exact getD_snoc_eq _ _ _ (m + k.val) hlen.symm
  · rw [h1] at hfa; rw [h2] at hfb; dsimp only
    constructor
    · unfold isElim; rw [runAt_succ m gs st₀ k.val k.isLt, hg]
      simp only [elimGate, List.map_cons, List.map_nil, hfa, hfb, simpOr]; simp
    · rw [hfk, runAt_succ m gs st₀ k.val k.isLt, hg]
      simp only [elimGate, List.map_cons, List.map_nil, hfa, hfb, simpOr]
      exact getD_snoc_eq _ _ _ (m + k.val) hlen.symm
  · rw [h1] at hfa; rw [h2] at hfb; dsimp only
    refine ⟨?_, ?_, ?_⟩
    · unfold isElim; rw [runAt_succ m gs st₀ k.val k.isLt, hg]
      simp only [elimGate, List.map_cons, List.map_nil, hfa, hfb, simpOr]; simp
    · rw [hfk, runAt_succ m gs st₀ k.val k.isLt, hg]
      simp only [elimGate, List.map_cons, List.map_nil, hfa, hfb, simpOr]
      exact getD_snoc_eq _ _ _ (m + k.val) hlen.symm
    · rw [runAt_succ m gs st₀ k.val k.isLt, hg]
      simp only [elimGate, List.map_cons, List.map_nil, hfa, hfb, simpOr]

private lemma elim_const_input {m : ℕ} {F : (Fin m → Bool) → Bool} {C : Circuit}
    (hmin : MinimalCircuit m F C)
    (hnc : ∃ x x' : Fin m → Bool, F x ≠ F x')
    (st₀ : List (Bool ⊕ ℕ)) (hst₀ : st₀.length = m)
    (k : Fin C.gates.length) (w : ℕ) (hw : w ∈ C.gates[k.val].inputs)
    (hc : ∃ c : Bool, finalSt m C.gates st₀ w = Sum.inl c) :
    isElim m C.gates st₀ k = true := by
  obtain ⟨c, hc⟩ := hc
  rcases minimal_gate_shape hmin hnc k.val k.isLt with
    ⟨hop, a, ha, hin⟩ | ⟨hop, a, b, ha, hb, _, hin⟩
  · have hg : C.gates[k.val] = ⟨GateOp.not, [a]⟩ := by
      cases h : C.gates[k.val]; simp_all
    rw [hin] at hw; simp at hw; subst hw
    have hs := runAt_step_not m C.gates st₀ hst₀ k w ha hg
    rw [hc] at hs
    exact hs.1
  · rcases hop with hop | hop
    · have hg : C.gates[k.val] = ⟨GateOp.and, [a, b]⟩ := by
        cases h : C.gates[k.val]; simp_all
      rw [hin] at hw; simp at hw
      have hs := runAt_step_and m C.gates st₀ hst₀ k a b ha hb hg
      rcases hw with rfl | rfl
      · rw [hc] at hs; cases hb' : finalSt m C.gates st₀ b <;> rw [hb'] at hs <;> exact hs.1
      · rw [hc] at hs; cases ha' : finalSt m C.gates st₀ a <;> rw [ha'] at hs <;> exact hs.1
    · have hg : C.gates[k.val] = ⟨GateOp.or, [a, b]⟩ := by
        cases h : C.gates[k.val]; simp_all
      rw [hin] at hw; simp at hw
      have hs := runAt_step_or m C.gates st₀ hst₀ k a b ha hb hg
      rcases hw with rfl | rfl
      · rw [hc] at hs; cases hb' : finalSt m C.gates st₀ b <;> rw [hb'] at hs <;> exact hs.1
      · rw [hc] at hs; cases ha' : finalSt m C.gates st₀ a <;> rw [ha'] at hs <;> exact hs.1

private lemma elim_run_circuit {m : ℕ} {F : (Fin m → Bool) → Bool} {C : Circuit}
    (hmin : MinimalCircuit m F C)
    (a : Fin m → Option Bool)
    (hnc' : ∃ x x' : Fin m → Bool, F (applyAssign a x) ≠ F (applyAssign a x')) :
    ∃ outw : ℕ,
      let C' : Circuit := ⟨(runAt m C.gates (initAssign m a) C.gates.length).2, outw⟩
      FanInTwo C' ∧
      (∀ g ∈ C'.gates, NOkGate g) ∧
      (∀ x : Fin m → Bool, C'.eval (List.ofFn x) = F (applyAssign a x)) ∧
      finalSt m C.gates (initAssign m a) C.output = Sum.inr outw := by
  have htake : C.gates.take C.gates.length = C.gates := List.take_length
  have hval : ∀ x : Fin m → Bool,
      statVal (wiresFrom (runAt m C.gates (initAssign m a) C.gates.length).2 (List.ofFn x))
        (finalSt m C.gates (initAssign m a) C.output) = F (applyAssign a x) := by
    intro x
    have hinv := elimInv_pass m (List.ofFn x) C.gates (List.ofFn (applyAssign a x))
      (initAssign m a, []) (fun g hg => (hmin.1 g hg).1) (elimInv_initAssign m a x)
    unfold finalSt runAt
    rw [htake]
    rw [(hinv.2.2 C.output).2]
    exact hmin.2.1 (applyAssign a x)
  cases hout : finalSt m C.gates (initAssign m a) C.output with
  | inl c =>
    obtain ⟨x, x', hne⟩ := hnc'
    have hx := hval x; have hx' := hval x'
    rw [hout] at hx hx'
    exact absurd (hx.symm.trans hx') hne
  | inr outw =>
    have hok : ∀ g ∈ (runAt m C.gates (initAssign m a) C.gates.length).2, OkGate g := by
      unfold runAt; rw [htake]
      exact elimPass_ok m C.gates (initAssign m a, []) (by simp)
    have hnok' : ∀ g ∈ (runAt m C.gates (initAssign m a) C.gates.length).2, NOkGate g := by
      have haux : ∀ gs (acc : List (Bool ⊕ ℕ) × List Gate),
          (∀ g ∈ acc.2, NOkGate g) → ∀ g ∈ (elimPass m gs acc).2, NOkGate g := by
        intro gs
        induction gs with
        | nil => intro acc h; exact h
        | cons g gs ih =>
          intro acc h
          apply ih
          intro g' hg'
          unfold elimGate at hg'
          dsimp only at hg'
          generalize g.inputs.map (fun i => acc.1.getD i (Sum.inl false)) = args at hg'
          cases hop : g.op with
          | not =>
            rw [hop] at hg'
            cases args with
            | nil => exact h g' (by simpa [simpNot] using hg')
            | cons u l =>
              cases u with
              | inl _ => exact h g' (by simpa [simpNot] using hg')
              | inr j =>
                simp only [simpNot, List.mem_append, List.mem_singleton] at hg'
                rcases hg' with hg' | rfl
                · exact h g' hg'
                · exact ⟨⟨Or.inr (Or.inr rfl), by simp⟩, fun _ => by simp⟩
          | and =>
            rw [hop] at hg'
            rcases args with _ | ⟨u, _ | ⟨v, _ | ⟨w, l⟩⟩⟩
            · exact h g' (by simpa [simpAnd] using hg')
            · cases u <;> exact h g' (by simpa [simpAnd] using hg')
            · cases u <;> cases v <;> try exact h g' (by simpa [simpAnd] using hg')
              simp only [simpAnd, List.mem_append, List.mem_singleton] at hg'
              rcases hg' with hg' | rfl
              · exact h g' hg'
              · exact ⟨⟨Or.inl rfl, by simp⟩, by simp⟩
            · exact h g' (by simpa [simpAnd] using hg')
          | or =>
            rw [hop] at hg'
            rcases args with _ | ⟨u, _ | ⟨v, _ | ⟨w, l⟩⟩⟩
            · exact h g' (by simpa [simpOr] using hg')
            · cases u <;> exact h g' (by simpa [simpOr] using hg')
            · cases u <;> cases v <;> try exact h g' (by simpa [simpOr] using hg')
              simp only [simpOr, List.mem_append, List.mem_singleton] at hg'
              rcases hg' with hg' | rfl
              · exact h g' hg'
              · exact ⟨⟨Or.inr (Or.inl rfl), by simp⟩, by simp⟩
            · exact h g' (by simpa [simpOr] using hg')
          | mod _ => rw [hop] at hg'; exact h g' (by simpa using hg')
          | maj => rw [hop] at hg'; exact h g' (by simpa using hg')
      unfold runAt; rw [htake]
      exact haux C.gates (initAssign m a, []) (by simp)
    refine ⟨outw, hok, hnok', fun x => ?_, rfl⟩
    have := hval x; rw [hout] at this; exact this

private lemma elim_size_of_card {m : ℕ} {F : (Fin m → Bool) → Bool} {C : Circuit}
    (hmin : MinimalCircuit m F C)
    (a : Fin m → Option Bool)
    (hnc' : ∃ x x' : Fin m → Bool, F (applyAssign a x) ≠ F (applyAssign a x'))
    (K : Finset (Fin C.gates.length))
    (hK : ∀ k ∈ K, isElim m C.gates (initAssign m a) k = true) :
    K.card ≤ C.gates.length ∧
      HasCircuitSize m (fun x => F (applyAssign a x)) (C.gates.length - K.card) := by
  obtain ⟨outw, hok, _, hev, _⟩ := elim_run_circuit hmin a hnc'
  have hsum := elim_card_add_len m C.gates (initAssign m a)
  have hsub : K ⊆ Finset.univ.filter (fun k : Fin C.gates.length =>
      isElim m C.gates (initAssign m a) k = true) := by
    intro k hk; exact Finset.mem_filter.2 ⟨Finset.mem_univ k, hK k hk⟩
  have hle : K.card ≤ (Finset.univ.filter (fun k : Fin C.gates.length =>
      isElim m C.gates (initAssign m a) k = true)).card := Finset.card_le_card hsub
  refine ⟨by omega, ⟨_, outw⟩, hok, ?_, hev⟩
  show (runAt m C.gates (initAssign m a) C.gates.length).2.length ≤ C.gates.length - K.card
  omega

private lemma var_has_consumer {m : ℕ} {F : (Fin m → Bool) → Bool} {C : Circuit}
    (hmin : MinimalCircuit m F C)
    (v : Fin m)
    (hdep : ∃ x : Fin m → Bool, F (Function.update x v false) ≠ F (Function.update x v true))
    (hout_ne : C.output ≠ v.val) :
    ∃ k : Fin C.gates.length, v.val ∈ C.gates[k.val].inputs := by
  by_contra hno
  push Not at hno
  obtain ⟨x, hne⟩ := hdep
  have hag := wiresFrom_agree C.gates {v.val}
    (List.ofFn (Function.update x v false))
    (List.ofFn (Function.update x v true))
    (by simp)
    (by intro u hu; simp at hu; subst hu; simp [v.isLt])
    (by
      intro i hi
      simp at hi
      by_cases hlt : i < m
      · have hne' : (⟨i, hlt⟩ : Fin m) ≠ v := fun h => hi (congrArg Fin.val h)
        rw [ofFn_getD_lt _ _ i hlt, ofFn_getD_lt _ _ i hlt,
            Function.update_of_ne hne', Function.update_of_ne hne']
      · rw [List.getD_eq_default _ _ (by simp; omega),
            List.getD_eq_default _ _ (by simp; omega)])
    (by
      intro g hg i hi hmem
      simp only [Set.mem_singleton_iff] at hmem
      subst hmem
      obtain ⟨k, hk, hgk⟩ := List.mem_iff_getElem.1 hg
      exact hno ⟨k, hk⟩ (hgk.symm ▸ hi))
  have hEq := hag.2 C.output (by simpa using hout_ne)
  exact hne ((hmin.2.1 _).symm.trans (hEq.trans (hmin.2.1 _)))

private lemma output_ne_of_nonconst_update {m : ℕ} {F : (Fin m → Bool) → Bool} {C : Circuit}
    (hmin : MinimalCircuit m F C) (v : Fin m) (b : Bool)
    (hnc : ∃ x x' : Fin m → Bool, F (Function.update x v b) ≠ F (Function.update x' v b)) :
    C.output ≠ v.val := by
  intro heq
  obtain ⟨x, x', hne⟩ := hnc
  have h1 := hmin.2.1 (Function.update x v b)
  have h2 := hmin.2.1 (Function.update x' v b)
  have hw (y : Fin m → Bool) :
      (C.wires (List.ofFn (Function.update y v b))).getD v.val false = b := by
    show (wiresFrom C.gates (List.ofFn (Function.update y v b))).getD v.val false = b
    rw [wiresFrom_getD_lt _ _ _ (by simp [v.isLt]), ofFn_getD_lt _ _ _ v.isLt]
    simp
  have e1 : F (Function.update x v b) = b := by
    rw [← h1]; show (C.wires _).getD C.output false = b; rw [heq]; exact hw x
  have e2 : F (Function.update x' v b) = b := by
    rw [← h2]; show (C.wires _).getD C.output false = b; rw [heq]; exact hw x'
  exact hne (e1.trans e2.symm)

private lemma elim_one_var {m s : ℕ} {F : (Fin m → Bool) → Bool} (v : Fin m) (b : Bool)
    (hC : HasCircuitSize m F s)
    (hdep : ∃ x : Fin m → Bool, F (Function.update x v false) ≠ F (Function.update x v true))
    (hnc : ∃ x x' : Fin m → Bool, F (Function.update x v b) ≠ F (Function.update x' v b)) :
    1 ≤ s ∧ HasCircuitSize m (fun x => F (Function.update x v b)) (s - 1) := by
  obtain ⟨C, hmin, hlen⟩ := exists_minimal_circuit hC
  have hncF : ∃ x x' : Fin m → Bool, F x ≠ F x' := by
    obtain ⟨x, hne⟩ := hdep; exact ⟨_, _, hne⟩
  have hout_ne := output_ne_of_nonconst_update hmin v b hnc
  obtain ⟨k, hk⟩ := var_has_consumer hmin v hdep hout_ne
  have hnc' : ∃ x x' : Fin m → Bool,
      F (applyAssign (singleAssign v b) x) ≠ F (applyAssign (singleAssign v b) x') := by
    simpa [applyAssign_single] using hnc
  have hst₀ : (initAssign m (singleAssign v b)).length = m := by simp [initAssign]
  have hfv : finalSt m C.gates (initAssign m (singleAssign v b)) v.val = Sum.inl b := by
    rw [finalSt_init m C.gates _ v.val (by omega), initAssign, ofFn_getD_lt _ _ v.val v.isLt]
    simp [singleAssign]
  have helim : isElim m C.gates (initAssign m (singleAssign v b)) k = true :=
    elim_const_input hmin hncF _ hst₀ k v.val hk ⟨b, hfv⟩
  obtain ⟨h1, hsz⟩ := elim_size_of_card hmin (singleAssign v b) hnc' {k} (by simpa using helim)
  simp only [Finset.card_singleton] at h1 hsz
  have hrew : (fun x => F (applyAssign (singleAssign v b) x)) =
      (fun x => F (Function.update x v b)) := by
    ext x; rw [applyAssign_single]
  rw [hrew] at hsz
  obtain ⟨C', hok', hsz', hev'⟩ := hsz
  exact ⟨by omega, C', hok', by show C'.gates.length ≤ s - 1; change C'.gates.length ≤ C.gates.length - 1 at hsz'; omega, hev'⟩

private lemma elim_two_var {m s : ℕ} {F : (Fin m → Bool) → Bool} (v : Fin m)
    (hC : HasCircuitSize m F s)
    (hdep : ∃ x : Fin m → Bool, F (Function.update x v false) ≠ F (Function.update x v true))
    (hnc0 : ∃ x x' : Fin m → Bool, F (Function.update x v false) ≠ F (Function.update x' v false))
    (hnc1 : ∃ x x' : Fin m → Bool, F (Function.update x v true) ≠ F (Function.update x' v true)) :
    2 ≤ s ∧ (HasCircuitSize m (fun x => F (Function.update x v false)) (s - 2) ∨
      HasCircuitSize m (fun x => F (Function.update x v true)) (s - 2)) := by
  obtain ⟨C, hmin, hlen⟩ := exists_minimal_circuit hC
  have hncF : ∃ x x' : Fin m → Bool, F x ≠ F x' := by
    obtain ⟨x, hne⟩ := hdep; exact ⟨_, _, hne⟩
  have hout_ne := output_ne_of_nonconst_update hmin v false hnc0
  obtain ⟨k₁, hk₁⟩ := var_has_consumer hmin v hdep hout_ne
  have hfinish : ∀ (b : Bool) (hncb : ∃ x x', F (Function.update x v b) ≠ F (Function.update x' v b))
      (k₂ : Fin C.gates.length), k₂ ≠ k₁ →
      isElim m C.gates (initAssign m (singleAssign v b)) k₁ = true →
      isElim m C.gates (initAssign m (singleAssign v b)) k₂ = true →
      2 ≤ s ∧ HasCircuitSize m (fun x => F (Function.update x v b)) (s - 2) := by
    intro b hncb k₂ hne he1 he2
    have hnc' : ∃ x x' : Fin m → Bool,
        F (applyAssign (singleAssign v b) x) ≠ F (applyAssign (singleAssign v b) x') := by
      simpa [applyAssign_single] using hncb
    obtain ⟨h2, hsz⟩ := elim_size_of_card hmin (singleAssign v b) hnc' {k₁, k₂} (by
      intro k hk; simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl <;> assumption)
    rw [Finset.card_pair hne.symm] at h2 hsz
    have hrew : (fun x => F (applyAssign (singleAssign v b) x)) =
        (fun x => F (Function.update x v b)) := by ext x; rw [applyAssign_single]
    rw [hrew] at hsz
    obtain ⟨C', hok', hsz', hev'⟩ := hsz
    exact ⟨by omega, C', hok', by show C'.gates.length ≤ s - 2; change C'.gates.length ≤ C.gates.length - 2 at hsz'; omega, hev'⟩
  by_cases htwo : ∃ k₂ : Fin C.gates.length, k₂ ≠ k₁ ∧ v.val ∈ C.gates[k₂.val].inputs
  · obtain ⟨k₂, hne, hk₂⟩ := htwo
    have hst₀ : (initAssign m (singleAssign v false)).length = m := by simp [initAssign]
    have hfv : finalSt m C.gates (initAssign m (singleAssign v false)) v.val = Sum.inl false := by
      rw [finalSt_init m C.gates _ v.val (by omega), initAssign, ofFn_getD_lt _ _ v.val v.isLt]
      simp [singleAssign]
    have he1 := elim_const_input hmin hncF _ hst₀ k₁ v.val hk₁ ⟨false, hfv⟩
    have he2 := elim_const_input hmin hncF _ hst₀ k₂ v.val hk₂ ⟨false, hfv⟩
    have ⟨h2, hsz⟩ := hfinish false hnc0 k₂ hne he1 he2
    exact ⟨h2, Or.inl hsz⟩
  · have hconst_choice : ∃ b : Bool, ∃ c : Bool,
        finalSt m C.gates (initAssign m (singleAssign v b)) (m + k₁.val) = Sum.inl c ∧
        isElim m C.gates (initAssign m (singleAssign v b)) k₁ = true := by
      have hst₀ (b : Bool) : (initAssign m (singleAssign v b)).length = m := by simp [initAssign]
      have hfv (b : Bool) : finalSt m C.gates (initAssign m (singleAssign v b)) v.val = Sum.inl b := by
        rw [finalSt_init m C.gates _ v.val (by rw [hst₀ b]; exact v.isLt), initAssign, ofFn_getD_lt _ _ v.val v.isLt]
        simp [singleAssign]
      rcases minimal_gate_shape hmin hncF k₁.val k₁.isLt with
        ⟨hop, a, ha, hin⟩ | ⟨hop, a, b', ha, hb', _, hin⟩
      · have hg : C.gates[k₁.val] = ⟨GateOp.not, [a]⟩ := by cases h : C.gates[k₁.val]; simp_all
        rw [hin] at hk₁; simp at hk₁; subst hk₁
        have hs := runAt_step_not m C.gates _ (hst₀ false) k₁ v.val ha hg
        rw [hfv false] at hs
        exact ⟨false, true, hs.2, hs.1⟩
      · rcases hop with hop | hop
        · have hg : C.gates[k₁.val] = ⟨GateOp.and, [a, b']⟩ := by cases h : C.gates[k₁.val]; simp_all
          rw [hin] at hk₁; simp at hk₁
          have hs := runAt_step_and m C.gates _ (hst₀ false) k₁ a b' ha hb' hg
          rcases hk₁ with rfl | rfl
          · rw [hfv false] at hs
            cases hfb : finalSt m C.gates _ b' <;> rw [hfb] at hs
            · exact ⟨false, false, by simpa using hs.2, hs.1⟩
            · exact ⟨false, false, by simpa using hs.2, hs.1⟩
          · rw [hfv false] at hs
            cases hfa : finalSt m C.gates _ a <;> rw [hfa] at hs
            · exact ⟨false, false, by simpa using hs.2, hs.1⟩
            · exact ⟨false, false, by simpa using hs.2, hs.1⟩
        · have hg : C.gates[k₁.val] = ⟨GateOp.or, [a, b']⟩ := by cases h : C.gates[k₁.val]; simp_all
          rw [hin] at hk₁; simp at hk₁
          have hs := runAt_step_or m C.gates _ (hst₀ true) k₁ a b' ha hb' hg
          rcases hk₁ with rfl | rfl
          · rw [hfv true] at hs
            cases hfb : finalSt m C.gates _ b' <;> rw [hfb] at hs
            · exact ⟨true, true, by simpa using hs.2, hs.1⟩
            · exact ⟨true, true, by simpa using hs.2, hs.1⟩
          · rw [hfv true] at hs
            cases hfa : finalSt m C.gates _ a <;> rw [hfa] at hs
            · exact ⟨true, true, by simpa using hs.2, hs.1⟩
            · exact ⟨true, true, by simpa using hs.2, hs.1⟩
    obtain ⟨b, c, hfc, he1⟩ := hconst_choice
    have hncb : ∃ x x' : Fin m → Bool, F (Function.update x v b) ≠ F (Function.update x' v b) := by
      cases b; exact hnc0; exact hnc1
    have hout_ne_k₁ : C.output ≠ m + k₁.val := by
      intro heq
      obtain ⟨_, _, _, _, hout_eq⟩ := elim_run_circuit hmin (singleAssign v b) (by simpa [applyAssign_single] using hncb)
      rw [heq, hfc] at hout_eq
      exact Sum.inl_ne_inr hout_eq
    obtain ⟨k₂, hk₁₂, hk₂lt, hk₂mem⟩ := minimal_gate_used hmin hncF k₁.val k₁.isLt hout_ne_k₁
    have hst₀ : (initAssign m (singleAssign v b)).length = m := by simp [initAssign]
    have he2 := elim_const_input hmin hncF _ hst₀ ⟨k₂, hk₂lt⟩ (m + k₁.val) hk₂mem ⟨c, hfc⟩
    have hne : (⟨k₂, hk₂lt⟩ : Fin C.gates.length) ≠ k₁ := fun h => by
      have hval : k₂ = k₁.val := congrArg Fin.val h
      omega
    have ⟨h2, hsz⟩ := hfinish b hncb ⟨k₂, hk₂lt⟩ hne he1 he2
    cases b
    · exact ⟨h2, Or.inl hsz⟩
    · exact ⟨h2, Or.inr hsz⟩

private def HasExactParentOrder {n : ℕ} (G : SimpleGraph (Fin n)) (p : Fin n → Fin n) (d : Fin n → ℕ) : Prop :=
  ∀ u v : Fin n, G.Adj u v → (v = p u ∧ d u = d v + 1) ∨ (u = p v ∧ d v = d u + 1)

private lemma parentOrder_anti {n : ℕ} {G H : SimpleGraph (Fin n)} {p : Fin n → Fin n} {d : Fin n → ℕ}
    (hle : H ≤ G) (h : HasExactParentOrder G p d) : HasExactParentOrder H p d :=
  fun u v huv => h u v (hle huv)

private lemma leaf_cases_of_parentOrder {n : ℕ} (G : SimpleGraph (Fin n))
    (p : Fin n → Fin n) (d : Fin n → ℕ) (hord : HasExactParentOrder G p d)
    (hEdge : ∃ u v : Fin n, G.Adj u v) :
    ∃ ℓ p₀ : Fin n, G.Adj ℓ p₀ ∧ (∀ w, G.Adj ℓ w → w = p₀) ∧
      ((∃ ℓ' : Fin n, ℓ' ≠ ℓ ∧ G.Adj ℓ' p₀ ∧ ∀ w, G.Adj ℓ' w → w = p₀) ∨
       (∀ w, G.Adj p₀ w → w = ℓ) ∨
       (∃ q : Fin n, q ≠ ℓ ∧ G.Adj p₀ q ∧ ∀ w, G.Adj p₀ w → w = ℓ ∨ w = q)) := by
  classical
  let S : Finset (Fin n) := Finset.univ.filter (fun u => ∃ v, G.Adj u v)
  have hSne : S.Nonempty := by
    obtain ⟨u, v, huv⟩ := hEdge
    exact ⟨u, Finset.mem_filter.2 ⟨Finset.mem_univ u, v, huv⟩⟩
  obtain ⟨ℓ, hℓS, hℓmax⟩ := Finset.exists_max_image S d hSne
  have hℓ_adj : ∃ v, G.Adj ℓ v := (Finset.mem_filter.1 hℓS).2
  obtain ⟨p₀, hℓp⟩ := hℓ_adj
  have hℓ_dir : p₀ = p ℓ ∧ d ℓ = d p₀ + 1 := by
    rcases hord ℓ p₀ hℓp with h | ⟨_, hd⟩
    · exact h
    · have hpS : p₀ ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ p₀, ℓ, hℓp.symm⟩
      have hle := hℓmax p₀ hpS
      omega
  have hleaf_of_max : ∀ x : Fin n, d x = d ℓ → G.Adj x p₀ → ∀ w, G.Adj x w → w = p₀ := by
    intro x hdx hxp w hxw
    have hx_dir : p₀ = p x ∧ d x = d p₀ + 1 := by
      rcases hord x p₀ hxp with h | ⟨_, hd⟩
      · exact h
      · omega
    rcases hord x w hxw with ⟨rfl, _⟩ | ⟨_, hd⟩
    · exact hx_dir.1.symm
    · have hwS : w ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ w, x, hxw.symm⟩
      have hle := hℓmax w hwS
      omega
  have hℓleaf : ∀ w, G.Adj ℓ w → w = p₀ := hleaf_of_max ℓ rfl hℓp
  refine ⟨ℓ, p₀, hℓp, hℓleaf, ?_⟩
  by_cases htwin : ∃ ℓ' : Fin n, ℓ' ≠ ℓ ∧ G.Adj ℓ' p₀ ∧ d ℓ' = d p₀ + 1
  · obtain ⟨ℓ', hne, hℓ'p, hd'⟩ := htwin
    exact Or.inl ⟨ℓ', hne, hℓ'p, hleaf_of_max ℓ' (by omega) hℓ'p⟩
  · push Not at htwin
    by_cases hpar : ∃ q : Fin n, G.Adj p₀ q ∧ q = p p₀ ∧ d p₀ = d q + 1
    · obtain ⟨q, hpq, hqp, hdq⟩ := hpar
      have hqne : q ≠ ℓ := by intro h; subst h; omega
      refine Or.inr (Or.inr ⟨q, hqne, hpq, fun w hpw => ?_⟩)
      rcases hord p₀ w hpw with ⟨rfl, _⟩ | ⟨_, hdw⟩
      · exact Or.inr hqp.symm
      · by_cases hwℓ : w = ℓ
        · exact Or.inl hwℓ
        · exfalso; exact htwin w hwℓ hpw.symm hdw
    · push Not at hpar
      refine Or.inr (Or.inl fun w hpw => ?_)
      rcases hord p₀ w hpw with ⟨hwp, hdw⟩ | ⟨_, hdw⟩
      · exfalso; exact hpar w hpw hwp hdw
      · by_contra hwℓ; exact htwin w hwℓ hpw.symm hdw

private def IsVC {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : Prop :=
  ∀ u v : Fin n, G.Adj u v → u ∈ S ∨ v ∈ S

private def HasMinVC {n : ℕ} (G : SimpleGraph (Fin n)) (t : ℕ) : Prop :=
  (∃ S : Finset (Fin n), IsVC G S ∧ S.card = t) ∧
  (∀ S : Finset (Fin n), IsVC G S → t ≤ S.card)

private lemma hasMinVC_exists {n : ℕ} (G : SimpleGraph (Fin n)) : ∃ t : ℕ, HasMinVC G t := by
  classical
  have hex : ∃ k : ℕ, ∃ S : Finset (Fin n), IsVC G S ∧ S.card = k :=
    ⟨(Finset.univ : Finset (Fin n)).card, Finset.univ, fun u _ _ => Or.inl (Finset.mem_univ u), rfl⟩
  refine ⟨Nat.find hex, Nat.find_spec hex, fun S hS => Nat.find_min' hex ⟨S, hS, rfl⟩⟩

private lemma hasMinVC_empty {n t : ℕ} (G : SimpleGraph (Fin n))
    (hempty : ∀ u v : Fin n, ¬ G.Adj u v) (hvc : HasMinVC G t) : t = 0 := by
  have hle : t ≤ (∅ : Finset (Fin n)).card := hvc.2 ∅ (fun u v h => absurd h (hempty u v))
  simpa using hle

private def deleteVertexEdges {n : ℕ} (G : SimpleGraph (Fin n)) (p : Fin n) :
    SimpleGraph (Fin n) where
  Adj u v := G.Adj u v ∧ u ≠ p ∧ v ≠ p
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun v h => G.loopless.irrefl v h.1⟩

private lemma deleteVertexEdges_le {n : ℕ} (G : SimpleGraph (Fin n)) (p : Fin n) :
    deleteVertexEdges G p ≤ G := fun _ _ h => h.1

private lemma hasMinVC_deleteEdge {n t t₁ : ℕ} (G : SimpleGraph (Fin n)) (ℓ p : Fin n)
    (hvc : HasMinVC G t) (hvc₁ : HasMinVC (G.deleteEdges {s(ℓ, p)}) t₁) :
    t₁ ≤ t ∧ t ≤ t₁ + 1 := by
  obtain ⟨⟨S, hS, hSc⟩, hmin⟩ := hvc
  obtain ⟨⟨S₁, hS₁, hS₁c⟩, hmin₁⟩ := hvc₁
  constructor
  · rw [← hSc]; exact hmin₁ S (fun u v h => hS u v h.1)
  · have hcov : IsVC G (insert p S₁) := by
      intro u v huv
      by_cases hmem : s(u, v) = s(ℓ, p)
      · rw [Sym2.eq_iff] at hmem
        rcases hmem with ⟨_, rfl⟩ | ⟨rfl, _⟩
        · exact Or.inr (Finset.mem_insert_self _ S₁)
        · exact Or.inl (Finset.mem_insert_self _ S₁)
      · rcases hS₁ u v (SimpleGraph.deleteEdges_adj.2 ⟨huv, by simpa using hmem⟩) with hu | hv
        · exact Or.inl (Finset.mem_insert_of_mem hu)
        · exact Or.inr (Finset.mem_insert_of_mem hv)
    have hle := hmin (insert p S₁) hcov
    have hcard := Finset.card_insert_le p S₁
    omega

private lemma hasMinVC_deleteLeafEdge_eq {n t t₁ : ℕ} (G : SimpleGraph (Fin n)) (ℓ ℓ' p : Fin n)
    (hℓ'ne : ℓ' ≠ ℓ) (hℓ'p : G.Adj ℓ' p) (hℓ'leaf : ∀ w, G.Adj ℓ' w → w = p)
    (hvc : HasMinVC G t) (hvc₁ : HasMinVC (G.deleteEdges {s(ℓ, p)}) t₁) :
    t₁ = t := by
  have hle : t₁ ≤ t := (hasMinVC_deleteEdge G ℓ p hvc hvc₁).1
  obtain ⟨⟨S₁, hS₁, hS₁c⟩, _⟩ := hvc₁
  have hge : t ≤ t₁ := by
    by_cases hp : p ∈ S₁
    · have hcov : IsVC G S₁ := by
        intro u v huv
        by_cases hmem : s(u, v) = s(ℓ, p)
        · rw [Sym2.eq_iff] at hmem
          rcases hmem with ⟨_, rfl⟩ | ⟨rfl, _⟩
          · exact Or.inr hp
          · exact Or.inl hp
        · exact hS₁ u v (SimpleGraph.deleteEdges_adj.2 ⟨huv, by simpa using hmem⟩)
      rw [← hS₁c]; exact hvc.2 S₁ hcov
    · have hℓ'in : ℓ' ∈ S₁ := by
        have hne_edge : s(ℓ', p) ≠ s(ℓ, p) := by
          intro heq; rw [Sym2.eq_iff] at heq
          rcases heq with ⟨h1, _⟩ | ⟨h1, _⟩
          · exact hℓ'ne h1
          · exact hℓ'p.ne h1
        rcases hS₁ ℓ' p (SimpleGraph.deleteEdges_adj.2 ⟨hℓ'p, by simpa using hne_edge⟩) with h | h
        · exact h
        · exact absurd h hp
      set S' := insert p (S₁.erase ℓ')
      have hcov : IsVC G S' := by
        intro u v huv
        by_cases hmem : s(u, v) = s(ℓ, p)
        · rw [Sym2.eq_iff] at hmem
          rcases hmem with ⟨_, rfl⟩ | ⟨rfl, _⟩
          · exact Or.inr (Finset.mem_insert_self _ _)
          · exact Or.inl (Finset.mem_insert_self _ _)
        · rcases hS₁ u v (SimpleGraph.deleteEdges_adj.2 ⟨huv, by simpa using hmem⟩) with hu | hv
          · by_cases huℓ : u = ℓ'
            · subst huℓ; exact Or.inr (hℓ'leaf v huv ▸ Finset.mem_insert_self p _)
            · exact Or.inl (Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨huℓ, hu⟩))
          · by_cases hvℓ : v = ℓ'
            · subst hvℓ; exact Or.inl (hℓ'leaf u huv.symm ▸ Finset.mem_insert_self p _)
            · exact Or.inr (Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hvℓ, hv⟩))
      have hcard : S'.card = S₁.card := by
        have hp_not : p ∉ S₁.erase ℓ' := fun h => hp (Finset.mem_of_mem_erase h)
        rw [Finset.card_insert_of_notMem hp_not, Finset.card_erase_of_mem hℓ'in]
        have hpos : 1 ≤ S₁.card := Finset.one_le_card.2 ⟨ℓ', hℓ'in⟩
        omega
      have := hvc.2 S' hcov
      omega
  omega

private lemma hasMinVC_deleteVertex {n t t' : ℕ} (G : SimpleGraph (Fin n)) (ℓ p : Fin n)
    (hlp : G.Adj ℓ p) (hleaf : ∀ w, G.Adj ℓ w → w = p)
    (hvc : HasMinVC G t) (hvc' : HasMinVC (deleteVertexEdges G p) t') :
    t' + 1 = t := by
  obtain ⟨⟨S, hS, hSc⟩, hmin⟩ := hvc
  obtain ⟨⟨S', hS', hS'c⟩, hmin'⟩ := hvc'
  have hle : t ≤ t' + 1 := by
    have hcov : IsVC G (insert p S') := by
      intro u v huv
      by_cases hup : u = p
      · exact Or.inl (hup ▸ Finset.mem_insert_self p S')
      · by_cases hvp : v = p
        · exact Or.inr (hvp ▸ Finset.mem_insert_self p S')
        · rcases hS' u v ⟨huv, hup, hvp⟩ with hu | hv
          · exact Or.inl (Finset.mem_insert_of_mem hu)
          · exact Or.inr (Finset.mem_insert_of_mem hv)
    have := hmin (insert p S') hcov
    have := Finset.card_insert_le p S'
    omega
  have hge : t' + 1 ≤ t := by
    by_cases hp : p ∈ S
    · have hcov : IsVC (deleteVertexEdges G p) (S.erase p) := by
        intro u v huv
        rcases hS u v huv.1 with hu | hv
        · exact Or.inl (Finset.mem_erase.2 ⟨huv.2.1, hu⟩)
        · exact Or.inr (Finset.mem_erase.2 ⟨huv.2.2, hv⟩)
      have h1 := hmin' (S.erase p) hcov
      have h2 := Finset.card_erase_of_mem hp
      have hpos : 1 ≤ S.card := Finset.one_le_card.2 ⟨p, hp⟩
      omega
    · have hℓ : ℓ ∈ S := by
        rcases hS ℓ p hlp with h | h
        · exact h
        · exact absurd h hp
      have hcov : IsVC (deleteVertexEdges G p) (S.erase ℓ) := by
        intro u v huv
        rcases hS u v huv.1 with hu | hv
        · have huℓ : u ≠ ℓ := by intro h; subst h; exact huv.2.2 (hleaf v huv.1)
          exact Or.inl (Finset.mem_erase.2 ⟨huℓ, hu⟩)
        · have hvℓ : v ≠ ℓ := by intro h; subst h; exact huv.2.1 (hleaf u huv.1.symm)
          exact Or.inr (Finset.mem_erase.2 ⟨hvℓ, hv⟩)
      have h1 := hmin' (S.erase ℓ) hcov
      have h2 := Finset.card_erase_of_mem hℓ
      have hpos : 1 ≤ S.card := Finset.one_le_card.2 ⟨ℓ, hℓ⟩
      omega
  omega

private lemma edgeFinset_card_deleteEdge {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (ℓ p : Fin n) (hlp : G.Adj ℓ p) [DecidableRel (G.deleteEdges {s(ℓ, p)}).Adj] :
    (G.deleteEdges {s(ℓ, p)}).edgeFinset.card + 1 = G.edgeFinset.card := by
  have heq : (G.deleteEdges {s(ℓ, p)}).edgeFinset = G.edgeFinset.erase s(ℓ, p) := by
    ext e
    induction e using Sym2.ind with
    | _ u v =>
      simp only [SimpleGraph.mem_edgeFinset, Finset.mem_erase, SimpleGraph.edgeSet_deleteEdges,
        Set.mem_sdiff, Set.mem_singleton_iff]
      tauto
  rw [heq]
  have hmem : s(ℓ, p) ∈ G.edgeFinset := by rw [SimpleGraph.mem_edgeFinset]; exact hlp
  have hpos : 1 ≤ G.edgeFinset.card := Finset.one_le_card.2 ⟨s(ℓ, p), hmem⟩
  rw [Finset.card_erase_of_mem hmem]
  omega

private lemma edgeFinset_card_deleteVertex_deg1 {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (ℓ p : Fin n) (hlp : G.Adj ℓ p)
    (hpdeg : ∀ w, G.Adj p w → w = ℓ) [DecidableRel (deleteVertexEdges G p).Adj] :
    (deleteVertexEdges G p).edgeFinset.card + 1 = G.edgeFinset.card := by
  have heq : (deleteVertexEdges G p).edgeFinset = G.edgeFinset.erase s(ℓ, p) := by
    ext e
    induction e using Sym2.ind with
    | _ u v =>
      simp only [SimpleGraph.mem_edgeFinset, Finset.mem_erase, SimpleGraph.mem_edgeSet]
      change (G.Adj u v ∧ u ≠ p ∧ v ≠ p) ↔ s(u, v) ≠ s(ℓ, p) ∧ G.Adj u v
      simp only [ne_eq, Sym2.eq_iff]
      constructor
      · rintro ⟨huv, hup, hvp⟩
        refine ⟨?_, huv⟩
        rintro (⟨_, rfl⟩ | ⟨rfl, _⟩) <;> contradiction
      · rintro ⟨hne, huv⟩
        refine ⟨huv, ?_, ?_⟩
        · intro hup; subst hup; exact hne (Or.inr ⟨rfl, hpdeg v huv⟩)
        · intro hvp; subst hvp; exact hne (Or.inl ⟨hpdeg u huv.symm, rfl⟩)
  rw [heq]
  have hmem : s(ℓ, p) ∈ G.edgeFinset := by rw [SimpleGraph.mem_edgeFinset]; exact hlp
  have hpos : 1 ≤ G.edgeFinset.card := Finset.one_le_card.2 ⟨s(ℓ, p), hmem⟩
  rw [Finset.card_erase_of_mem hmem]
  omega

private lemma edgeFinset_card_deleteVertex_deg2 {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (ℓ p q : Fin n) (hlp : G.Adj ℓ p) (hpq : G.Adj p q) (hqne : q ≠ ℓ)
    (hpdeg : ∀ w, G.Adj p w → w = ℓ ∨ w = q) [DecidableRel (deleteVertexEdges G p).Adj] :
    (deleteVertexEdges G p).edgeFinset.card + 2 = G.edgeFinset.card := by
  have heq : (deleteVertexEdges G p).edgeFinset = (G.edgeFinset.erase s(ℓ, p)).erase s(p, q) := by
    ext e
    induction e using Sym2.ind with
    | _ u v =>
      simp only [SimpleGraph.mem_edgeFinset, Finset.mem_erase, SimpleGraph.mem_edgeSet]
      change (G.Adj u v ∧ u ≠ p ∧ v ≠ p) ↔ s(u, v) ≠ s(p, q) ∧ s(u, v) ≠ s(ℓ, p) ∧ G.Adj u v
      simp only [ne_eq, Sym2.eq_iff]
      constructor
      · rintro ⟨huv, hup, hvp⟩
        refine ⟨?_, ?_, huv⟩
        · rintro (⟨rfl, _⟩ | ⟨_, rfl⟩) <;> contradiction
        · rintro (⟨_, rfl⟩ | ⟨rfl, _⟩) <;> contradiction
      · rintro ⟨hne1, hne2, huv⟩
        refine ⟨huv, ?_, ?_⟩
        · intro hup; subst hup
          rcases hpdeg v huv with rfl | rfl
          · exact hne2 (Or.inr ⟨rfl, rfl⟩)
          · exact hne1 (Or.inl ⟨rfl, rfl⟩)
        · intro hvp; subst hvp
          rcases hpdeg u huv.symm with rfl | rfl
          · exact hne2 (Or.inl ⟨rfl, rfl⟩)
          · exact hne1 (Or.inr ⟨rfl, rfl⟩)
  rw [heq]
  have hmem1 : s(ℓ, p) ∈ G.edgeFinset := by rw [SimpleGraph.mem_edgeFinset]; exact hlp
  have hne : s(p, q) ≠ s(ℓ, p) := by
    intro h; rw [Sym2.eq_iff] at h
    rcases h with ⟨h1, _⟩ | ⟨_, h2⟩
    · exact hlp.ne h1.symm
    · exact hqne h2
  have hmem2 : s(p, q) ∈ G.edgeFinset.erase s(ℓ, p) :=
    Finset.mem_erase.2 ⟨hne, by rw [SimpleGraph.mem_edgeFinset]; exact hpq⟩
  have hpos1 : 1 ≤ G.edgeFinset.card := Finset.one_le_card.2 ⟨s(ℓ, p), hmem1⟩
  have hpos2 : 1 ≤ (G.edgeFinset.erase s(ℓ, p)).card := Finset.one_le_card.2 ⟨s(p, q), hmem2⟩
  rw [Finset.card_erase_of_mem hmem2, Finset.card_erase_of_mem hmem1] at *
  omega

private noncomputable def graphOrFun {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n))
    (x : Fin n → Bool) : Bool :=
  open Classical in
  decide ((∃ a ∈ A, x a = true) ∨ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)

private lemma graphOrFun_nonconst {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n))
    (hne : A.Nonempty ∨ ∃ u v : Fin n, G.Adj u v) :
    ∃ x x' : Fin n → Bool, graphOrFun G A x ≠ graphOrFun G A x' := by
  classical
  refine ⟨fun _ => false, fun _ => true, ?_⟩
  have h0 : graphOrFun G A (fun _ => false) = false := by
    simp [graphOrFun]
  have h1 : graphOrFun G A (fun _ => true) = true := by
    simp only [graphOrFun, decide_eq_true_eq]
    rcases hne with ⟨a, ha⟩ | ⟨u, v, huv⟩
    · exact Or.inl ⟨a, ha, trivial⟩
    · exact Or.inr ⟨u, v, huv, trivial, trivial⟩
  rw [h0, h1]; decide

private lemma graphOrFun_dep_A {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n))
    (a : Fin n) (ha : a ∈ A) :
    ∃ x : Fin n → Bool, graphOrFun G A (Function.update x a false) ≠
      graphOrFun G A (Function.update x a true) := by
  classical
  refine ⟨fun _ => false, ?_⟩
  have h0 : graphOrFun G A (Function.update (fun _ => false) a false) = false := by
    simp [graphOrFun]
  have h1 : graphOrFun G A (Function.update (fun _ => false) a true) = true := by
    simp only [graphOrFun, decide_eq_true_eq]
    exact Or.inl ⟨a, ha, by simp⟩
  rw [h0, h1]; decide

private lemma graphOrFun_update_A {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n))
    (a : Fin n) (hiso : ∀ v : Fin n, ¬ G.Adj a v) :
    (fun x => graphOrFun G A (Function.update x a false)) = graphOrFun G (A.erase a) := by
  classical
  ext x
  simp only [graphOrFun, decide_eq_decide]
  constructor
  · rintro (⟨b, hb, hxb⟩ | ⟨u, v, huv, hu, hv⟩)
    · by_cases hba : b = a
      · subst hba; simp at hxb
      · rw [Function.update_of_ne hba] at hxb
        exact Or.inl ⟨b, Finset.mem_erase.2 ⟨hba, hb⟩, hxb⟩
    · have hua : u ≠ a := fun h => hiso v (h ▸ huv)
      have hva : v ≠ a := fun h => hiso u (h ▸ huv.symm)
      rw [Function.update_of_ne hua] at hu
      rw [Function.update_of_ne hva] at hv
      exact Or.inr ⟨u, v, huv, hu, hv⟩
  · rintro (⟨b, hb, hxb⟩ | ⟨u, v, huv, hu, hv⟩)
    · obtain ⟨hba, hbA⟩ := Finset.mem_erase.1 hb
      exact Or.inl ⟨b, hbA, by rw [Function.update_of_ne hba]; exact hxb⟩
    · have hua : u ≠ a := fun h => hiso v (h ▸ huv)
      have hva : v ≠ a := fun h => hiso u (h ▸ huv.symm)
      exact Or.inr ⟨u, v, huv, by rw [Function.update_of_ne hua]; exact hu,
        by rw [Function.update_of_ne hva]; exact hv⟩

private lemma graphOrFun_dep_edge {n : ℕ} (G : SimpleGraph (Fin n))
    (ℓ p : Fin n) (hlp : G.Adj ℓ p) :
    ∃ x : Fin n → Bool, graphOrFun G ∅ (Function.update x ℓ false) ≠
      graphOrFun G ∅ (Function.update x ℓ true) := by
  classical
  refine ⟨fun i => decide (i = p), ?_⟩
  have h0 : graphOrFun G ∅ (Function.update (fun i => decide (i = p)) ℓ false) = false := by
    simp only [graphOrFun, Finset.notMem_empty, false_and, exists_false, false_or, decide_eq_false_iff_not]
    rintro ⟨u, v, huv, hu, hv⟩
    have hu_eq : u = p := by
      by_cases h : u = ℓ
      · subst h; simp at hu
      · rw [Function.update_of_ne h] at hu; simpa using hu
    have hv_eq : v = p := by
      by_cases h : v = ℓ
      · subst h; simp at hv
      · rw [Function.update_of_ne h] at hv; simpa using hv
    subst hu_eq; subst hv_eq
    exact G.loopless.irrefl _ huv
  have h1 : graphOrFun G ∅ (Function.update (fun i => decide (i = p)) ℓ true) = true := by
    simp only [graphOrFun, decide_eq_true_eq]
    exact Or.inr ⟨ℓ, p, hlp, by simp, by rw [Function.update_of_ne hlp.ne.symm]; simp⟩
  rw [h0, h1]; decide

private lemma graphOrFun_update_leaf_false {n : ℕ} (G : SimpleGraph (Fin n))
    (ℓ p : Fin n) (hleaf : ∀ w, G.Adj ℓ w → w = p) :
    (fun x => graphOrFun G ∅ (Function.update x ℓ false)) =
      graphOrFun (G.deleteEdges {s(ℓ, p)}) ∅ := by
  classical
  ext x
  simp only [graphOrFun, Finset.notMem_empty, false_and, exists_false, false_or, decide_eq_decide]
  constructor
  · rintro ⟨u, v, huv, hu, hv⟩
    have huℓ : u ≠ ℓ := by intro h; subst h; simp at hu
    have hvℓ : v ≠ ℓ := by intro h; subst h; simp at hv
    rw [Function.update_of_ne huℓ] at hu
    rw [Function.update_of_ne hvℓ] at hv
    refine ⟨u, v, SimpleGraph.deleteEdges_adj.2 ⟨huv, ?_⟩, hu, hv⟩
    simp only [Set.mem_singleton_iff, Sym2.eq_iff]
    rintro (⟨rfl, _⟩ | ⟨_, rfl⟩) <;> contradiction
  · rintro ⟨u, v, huv, hu, hv⟩
    have ⟨huv', hne⟩ := SimpleGraph.deleteEdges_adj.1 huv
    have huℓ : u ≠ ℓ := by
      intro h; subst h
      have hvp := hleaf v huv'
      subst hvp; exact hne (by simp)
    have hvℓ : v ≠ ℓ := by
      intro h; subst h
      have hup := hleaf u huv'.symm
      subst hup; exact hne (by simp [Sym2.eq_swap])
    exact ⟨u, v, huv', by rw [Function.update_of_ne huℓ]; exact hu,
      by rw [Function.update_of_ne hvℓ]; exact hv⟩

private lemma graphOrFun_update_leaf_true {n : ℕ} (G : SimpleGraph (Fin n))
    (ℓ p : Fin n) (hlp : G.Adj ℓ p) (hleaf : ∀ w, G.Adj ℓ w → w = p) :
    (fun x => graphOrFun G ∅ (Function.update x ℓ true)) =
      graphOrFun (deleteVertexEdges G p) {p} := by
  classical
  ext x
  simp only [graphOrFun, Finset.notMem_empty, false_and, exists_false, false_or,
    Finset.mem_singleton, exists_eq_left, decide_eq_decide]
  constructor
  · rintro ⟨u, v, huv, hu, hv⟩
    by_cases hup : u = p
    · subst hup
      rw [Function.update_of_ne hlp.ne.symm] at hu
      exact Or.inl hu
    · by_cases hvp : v = p
      · subst hvp
        rw [Function.update_of_ne hlp.ne.symm] at hv
        exact Or.inl hv
      · have huℓ : u ≠ ℓ := fun h => hvp (hleaf v (h ▸ huv))
        have hvℓ : v ≠ ℓ := fun h => hup (hleaf u (h ▸ huv.symm))
        rw [Function.update_of_ne huℓ] at hu
        rw [Function.update_of_ne hvℓ] at hv
        exact Or.inr ⟨u, v, ⟨huv, hup, hvp⟩, hu, hv⟩
  · rintro (hp | ⟨u, v, ⟨huv, hup, hvp⟩, hu, hv⟩)
    · exact ⟨ℓ, p, hlp, by simp, by rw [Function.update_of_ne hlp.ne.symm]; exact hp⟩
    · have huℓ : u ≠ ℓ := fun h => hvp (hleaf v (h ▸ huv))
      have hvℓ : v ≠ ℓ := fun h => hup (hleaf u (h ▸ huv.symm))
      exact ⟨u, v, huv, by rw [Function.update_of_ne huℓ]; exact hu,
        by rw [Function.update_of_ne hvℓ]; exact hv⟩

private lemma forest_lower {n : ℕ} (p : Fin n → Fin n) (d : Fin n → ℕ) :
    ∀ (s : ℕ) {t : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n)),
      HasExactParentOrder G p d →
      (∀ a ∈ A, ∀ v : Fin n, ¬ G.Adj a v) →
      (A.Nonempty ∨ ∃ u v : Fin n, G.Adj u v) →
      HasMinVC G t →
      HasCircuitSize n (graphOrFun G A) s →
      A.card + G.edgeFinset.card + t - 1 ≤ s := by
  intro s
  induction s using Nat.strong_induction_on with
  | ind s ih =>
    intro t G _ A hord hA_iso hne hvc hC
    by_cases hAne : A.Nonempty
    · obtain ⟨a, ha⟩ := hAne
      by_cases hrem : (A.erase a).Nonempty ∨ ∃ u v : Fin n, G.Adj u v
      · have hdep := graphOrFun_dep_A G A a ha
        have hrew := graphOrFun_update_A G A a (hA_iso a ha)
        have hnc : ∃ x x',
            graphOrFun G A (Function.update x a false) ≠
            graphOrFun G A (Function.update x' a false) := by
          simpa only [← congrFun hrew] using graphOrFun_nonconst G (A.erase a) hrem
        obtain ⟨hs1, hC'⟩ := elim_one_var a false hC hdep hnc
        rw [hrew] at hC'
        have hih := ih (s - 1) (by omega) G (A.erase a) hord
          (fun b hb => hA_iso b (Finset.mem_of_mem_erase hb)) hrem hvc hC'
        have hcard : (A.erase a).card + 1 = A.card := by
          have hpos : 1 ≤ A.card := Finset.one_le_card.2 ⟨a, ha⟩
          rw [Finset.card_erase_of_mem ha]; omega
        have hpos_sum : 1 ≤ (A.erase a).card + G.edgeFinset.card + t := by
          rcases hrem with ⟨b, hb⟩ | ⟨u, v, huv⟩
          · have : 1 ≤ (A.erase a).card := Finset.one_le_card.2 ⟨b, hb⟩; omega
          · have : 1 ≤ G.edgeFinset.card := Finset.one_le_card.2 ⟨s(u, v), by rw [SimpleGraph.mem_edgeFinset]; exact huv⟩
            omega
        omega
      · push Not at hrem
        have hA1 : A.card = 1 := by
          have h0 : (A.erase a).card = 0 := by rw [hrem.1]; simp
          have hpos : 1 ≤ A.card := Finset.one_le_card.2 ⟨a, ha⟩
          rw [Finset.card_erase_of_mem ha] at h0; omega
        have ht0 : t = 0 := hasMinVC_empty G hrem.2 hvc
        have he0 : G.edgeFinset.card = 0 := by
          apply Finset.card_eq_zero.2; ext e
          induction e using Sym2.ind with
          | _ u v => simp [SimpleGraph.mem_edgeFinset, hrem.2 u v]
        omega
    · have hAempty : A = ∅ := Finset.not_nonempty_iff_eq_empty.1 hAne
      subst hAempty
      have hEdge : ∃ u v : Fin n, G.Adj u v := by
        rcases hne with h | h
        · simp at h
        · exact h
      obtain ⟨ℓ, p₀, hlp, hleaf, hcases⟩ := leaf_cases_of_parentOrder G p d hord hEdge
      rcases hcases with ⟨ℓ', hℓ'ne, hℓ'p, hℓ'leaf⟩ | hpdeg1 | ⟨q, hqne, hpq, hpdeg2⟩
      · classical
        obtain ⟨t₁, hvc₁⟩ := hasMinVC_exists (G.deleteEdges {s(ℓ, p₀)})
        have ht₁ := hasMinVC_deleteLeafEdge_eq G ℓ ℓ' p₀ hℓ'ne hℓ'p hℓ'leaf hvc hvc₁
        have hrem_e : ∃ u v : Fin n, (G.deleteEdges {s(ℓ, p₀)}).Adj u v := by
          refine ⟨ℓ', p₀, SimpleGraph.deleteEdges_adj.2 ⟨hℓ'p, ?_⟩⟩
          simp only [Set.mem_singleton_iff, Sym2.eq_iff]
          rintro (⟨h1, _⟩ | ⟨h1, _⟩)
          · exact hℓ'ne h1
          · exact hℓ'p.ne h1
        have hdep := graphOrFun_dep_edge G ℓ p₀ hlp
        have hrew := graphOrFun_update_leaf_false G ℓ p₀ hleaf
        have hnc : ∃ x x',
            graphOrFun G ∅ (Function.update x ℓ false) ≠
            graphOrFun G ∅ (Function.update x' ℓ false) := by
          simpa only [← congrFun hrew] using graphOrFun_nonconst _ ∅ (Or.inr hrem_e)
        obtain ⟨hs1, hC'⟩ := elim_one_var ℓ false hC hdep hnc
        rw [hrew] at hC'
        have hih := ih (s - 1) (by omega) (G.deleteEdges {s(ℓ, p₀)}) ∅
          (parentOrder_anti (SimpleGraph.deleteEdges_le _) hord) (by simp) (Or.inr hrem_e) hvc₁ hC'
        have hedge := edgeFinset_card_deleteEdge G ℓ p₀ hlp
        have hpos_e : 1 ≤ (G.deleteEdges {s(ℓ, p₀)}).edgeFinset.card := by
          obtain ⟨u, v, huv⟩ := hrem_e
          exact Finset.one_le_card.2 ⟨s(u, v), by rw [SimpleGraph.mem_edgeFinset]; exact huv⟩
        simp only [Finset.card_empty, zero_add] at hih ⊢
        omega
      · classical
        obtain ⟨t', hvc'⟩ := hasMinVC_exists (deleteVertexEdges G p₀)
        have ht' := hasMinVC_deleteVertex G ℓ p₀ hlp hleaf hvc hvc'
        have hdep := graphOrFun_dep_edge G ℓ p₀ hlp
        have hrew := graphOrFun_update_leaf_true G ℓ p₀ hlp hleaf
        have hnc : ∃ x x',
            graphOrFun G ∅ (Function.update x ℓ true) ≠
            graphOrFun G ∅ (Function.update x' ℓ true) := by
          simpa only [← congrFun hrew] using graphOrFun_nonconst (deleteVertexEdges G p₀) {p₀} (Or.inl (Finset.singleton_nonempty p₀))
        obtain ⟨hs1, hC'⟩ := elim_one_var ℓ true hC hdep hnc
        rw [hrew] at hC'
        have hih := ih (s - 1) (by omega) (deleteVertexEdges G p₀) {p₀}
          (parentOrder_anti (deleteVertexEdges_le G p₀) hord)
          (by intro a ha v h; simp at ha; subst ha; exact h.2.1 rfl)
          (Or.inl (Finset.singleton_nonempty p₀)) hvc' hC'
        have hedge := edgeFinset_card_deleteVertex_deg1 G ℓ p₀ hlp hpdeg1
        simp only [Finset.card_singleton, Finset.card_empty, zero_add] at hih ⊢
        omega
      · classical
        have hrem_e : ∃ u v : Fin n, (G.deleteEdges {s(ℓ, p₀)}).Adj u v := by
          refine ⟨p₀, q, SimpleGraph.deleteEdges_adj.2 ⟨hpq, ?_⟩⟩
          simp only [Set.mem_singleton_iff, Sym2.eq_iff]
          rintro (⟨h1, _⟩ | ⟨_, h2⟩)
          · exact hlp.ne h1.symm
          · exact hqne h2
        have hdep := graphOrFun_dep_edge G ℓ p₀ hlp
        have hrew0 := graphOrFun_update_leaf_false G ℓ p₀ hleaf
        have hrew1 := graphOrFun_update_leaf_true G ℓ p₀ hlp hleaf
        have hnc0 : ∃ x x',
            graphOrFun G ∅ (Function.update x ℓ false) ≠
            graphOrFun G ∅ (Function.update x' ℓ false) := by
          simpa only [← congrFun hrew0] using graphOrFun_nonconst _ ∅ (Or.inr hrem_e)
        have hnc1 : ∃ x x',
            graphOrFun G ∅ (Function.update x ℓ true) ≠
            graphOrFun G ∅ (Function.update x' ℓ true) := by
          simpa only [← congrFun hrew1] using graphOrFun_nonconst (deleteVertexEdges G p₀) {p₀} (Or.inl (Finset.singleton_nonempty p₀))
        obtain ⟨hs2, hC0 | hC1⟩ := elim_two_var ℓ hC hdep hnc0 hnc1
        · rw [hrew0] at hC0
          obtain ⟨t₁, hvc₁⟩ := hasMinVC_exists (G.deleteEdges {s(ℓ, p₀)})
          have ht₁ := (hasMinVC_deleteEdge G ℓ p₀ hvc hvc₁).2
          have hih := ih (s - 2) (by omega) (G.deleteEdges {s(ℓ, p₀)}) ∅
            (parentOrder_anti (SimpleGraph.deleteEdges_le _) hord) (by simp) (Or.inr hrem_e) hvc₁ hC0
          have hedge := edgeFinset_card_deleteEdge G ℓ p₀ hlp
          have hpos_e : 1 ≤ (G.deleteEdges {s(ℓ, p₀)}).edgeFinset.card := by
            obtain ⟨u, v, huv⟩ := hrem_e
            exact Finset.one_le_card.2 ⟨s(u, v), by rw [SimpleGraph.mem_edgeFinset]; exact huv⟩
          simp only [Finset.card_empty, zero_add] at hih ⊢
          omega
        · rw [hrew1] at hC1
          obtain ⟨t', hvc'⟩ := hasMinVC_exists (deleteVertexEdges G p₀)
          have ht' := hasMinVC_deleteVertex G ℓ p₀ hlp hleaf hvc hvc'
          have hih := ih (s - 2) (by omega) (deleteVertexEdges G p₀) {p₀}
            (parentOrder_anti (deleteVertexEdges_le G p₀) hord)
            (by intro a ha v h; simp at ha; subst ha; exact h.2.1 rfl)
            (Or.inl (Finset.singleton_nonempty p₀)) hvc' hC1
          have hedge := edgeFinset_card_deleteVertex_deg2 G ℓ p₀ q hlp hpq hqne hpdeg2
          simp only [Finset.card_singleton, Finset.card_empty, zero_add] at hih ⊢
          omega

private lemma hasMinVC_of_cover_matching {n : ℕ} (G : SimpleGraph (Fin n))
    (S : Finset (Fin n)) (hS : IsVC G S)
    (M : List (Fin n × Fin n))
    (hM_adj : ∀ e ∈ M, G.Adj e.1 e.2)
    (hM_disj : (M.flatMap (fun e => [e.1, e.2])).Nodup)
    (hcard : S.card = M.length) :
    HasMinVC G M.length := by
  refine ⟨⟨S, hS, hcard⟩, ?_⟩
  intro T hT
  have haux : ∀ (L : List (Fin n × Fin n)),
      (∀ e ∈ L, G.Adj e.1 e.2) →
      (L.flatMap (fun e => [e.1, e.2])).Nodup →
      L.length ≤ (T.filter (fun v => v ∈ L.flatMap (fun e => [e.1, e.2]))).card := by
    intro L
    induction L with
    | nil => intro _ _; simp
    | cons e L ih =>
      intro hadj hnd
      simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.nodup_cons,
        List.mem_cons, List.mem_flatMap, not_or] at hnd
      obtain ⟨⟨hne, h1not⟩, h2not, hndL⟩ := hnd
      have hih := ih (fun e' he' => hadj e' (List.mem_cons_of_mem e he')) hndL
      have he_adj := hadj e (List.mem_cons_self ..)
      obtain h1 | h2 := hT e.1 e.2 he_adj
      · have hsub : insert e.1 (T.filter (fun v => v ∈ L.flatMap (fun e' => [e'.1, e'.2]))) ⊆
            T.filter (fun v => v ∈ (e :: L).flatMap (fun e' => [e'.1, e'.2])) := by
          intro v hv
          simp only [Finset.mem_insert, Finset.mem_filter, List.flatMap_cons, List.cons_append,
            List.nil_append, List.mem_cons] at hv ⊢
          rcases hv with rfl | ⟨hvT, hvL⟩
          · exact ⟨h1, Or.inl rfl⟩
          · exact ⟨hvT, Or.inr (Or.inr hvL)⟩
        have hnotmem : e.1 ∉ T.filter (fun v => v ∈ L.flatMap (fun e' => [e'.1, e'.2])) := by
          simp only [Finset.mem_filter, not_and]
          intro _ h
          rw [List.mem_flatMap] at h
          exact h1not (by simpa [List.mem_cons] using h)
        have hle := Finset.card_le_card hsub
        rw [Finset.card_insert_of_notMem hnotmem] at hle
        simp only [List.length_cons]
        omega
      · have hsub : insert e.2 (T.filter (fun v => v ∈ L.flatMap (fun e' => [e'.1, e'.2]))) ⊆
            T.filter (fun v => v ∈ (e :: L).flatMap (fun e' => [e'.1, e'.2])) := by
          intro v hv
          simp only [Finset.mem_insert, Finset.mem_filter, List.flatMap_cons, List.cons_append,
            List.nil_append, List.mem_cons] at hv ⊢
          rcases hv with rfl | ⟨hvT, hvL⟩
          · exact ⟨h2, Or.inr (Or.inl rfl)⟩
          · exact ⟨hvT, Or.inr (Or.inr hvL)⟩
        have hnotmem : e.2 ∉ T.filter (fun v => v ∈ L.flatMap (fun e' => [e'.1, e'.2])) := by
          simp only [Finset.mem_filter, not_and]
          intro _ h
          rw [List.mem_flatMap] at h
          exact h2not (by simpa [List.mem_cons] using h)
        have hle := Finset.card_le_card hsub
        rw [Finset.card_insert_of_notMem hnotmem] at hle
        simp only [List.length_cons]
        omega
  have h1 := haux M hM_adj hM_disj
  have h2 : (T.filter (fun v => v ∈ M.flatMap (fun e => [e.1, e.2]))).card ≤ T.card :=
    Finset.card_le_card (Finset.filter_subset _ T)
  omega

private def mkGraph10 (es : List (Fin 10 × Fin 10)) : SimpleGraph (Fin 10) where
  Adj u v := u ≠ v ∧ ((u, v) ∈ es ∨ (v, u) ∈ es)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

private lemma concrete_forest_lower (es : List (Fin 10 × Fin 10)) (A : Finset (Fin 10))
    (p : Fin 10 → Fin 10) (d : Fin 10 → ℕ)
    (S : Finset (Fin 10)) (M : List (Fin 10 × Fin 10))
    (k : ℕ)
    (hes_lt : ∀ e ∈ es, e.1 < e.2)
    (hes_nd : es.Nodup)
    (hord : HasExactParentOrder (mkGraph10 es) p d)
    (hiso : ∀ a ∈ A, ∀ v : Fin 10, ¬ (mkGraph10 es).Adj a v)
    (hne : A.Nonempty ∨ ∃ u v : Fin 10, (mkGraph10 es).Adj u v)
    (hS : IsVC (mkGraph10 es) S)
    (hM_adj : ∀ e ∈ M, (mkGraph10 es).Adj e.1 e.2)
    (hM_disj : (M.flatMap (fun e => [e.1, e.2])).Nodup)
    (hScard : S.card = M.length)
    (hbound : k ≤ A.card + es.length + M.length - 1)
    {s : ℕ} (hC : HasCircuitSize 10 (graphOrFun (mkGraph10 es) A) s) :
    k ≤ s := by
  classical
  have hedge_card : (mkGraph10 es).edgeFinset.card = es.length := by
    have hbij : (mkGraph10 es).edgeFinset = es.toFinset.image (fun e => s(e.1, e.2)) := by
      ext e
      induction e using Sym2.ind with
      | _ u v =>
        simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, Finset.mem_image,
          List.mem_toFinset, Sym2.eq_iff]
        change (u ≠ v ∧ ((u, v) ∈ es ∨ (v, u) ∈ es)) ↔ _
        constructor
        · rintro ⟨_, h | h⟩
          · exact ⟨(u, v), h, Or.inl ⟨rfl, rfl⟩⟩
          · exact ⟨(v, u), h, Or.inr ⟨rfl, rfl⟩⟩
        · rintro ⟨⟨a, b⟩, hab, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
          · exact ⟨(hes_lt _ hab).ne, Or.inl hab⟩
          · exact ⟨(hes_lt _ hab).ne.symm, Or.inr hab⟩
    rw [hbij, Finset.card_image_of_injOn, List.toFinset_card_of_nodup hes_nd]
    intro e₁ he₁ e₂ he₂ heq
    have h1 := hes_lt e₁ (List.mem_toFinset.1 (Finset.mem_coe.1 he₁))
    have h2 := hes_lt e₂ (List.mem_toFinset.1 (Finset.mem_coe.1 he₂))
    rw [Sym2.eq_iff] at heq
    rcases heq with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact Prod.ext ha hb
    · omega
  have hvc : HasMinVC (mkGraph10 es) M.length :=
    hasMinVC_of_cover_matching (mkGraph10 es) S hS M hM_adj hM_disj hScard
  have hlow := forest_lower p d s (mkGraph10 es) A hord hiso hne hvc hC
  omega

private lemma hasCircuitSize_comp_equiv {m s : ℕ} {f : (Fin m → Bool) → Bool}
    (e : Fin m ≃ Fin m) (h : HasCircuitSize m f s) :
    HasCircuitSize m (fun x => f (fun i => x (e i))) s := by
  obtain ⟨C, hok, hsz, hev⟩ := h
  let remapWire (w : ℕ) : ℕ :=
    if hw : w < m then (e ⟨w, hw⟩).val else w
  let remapGate (g : Gate) : Gate :=
    ⟨g.op, g.inputs.map remapWire⟩
  let C' : Circuit := ⟨C.gates.map remapGate, remapWire C.output⟩
  have hok' : FanInTwo C' := by
    intro g hg
    obtain ⟨g₀, hg₀, rfl⟩ := List.mem_map.1 hg
    exact ⟨(hok g₀ hg₀).1, by simp [remapGate]; exact (hok g₀ hg₀).2⟩
  have hsz' : C'.size ≤ s := by simpa [Circuit.size, C'] using hsz
  refine ⟨C', hok', hsz', fun x => ?_⟩
  have hwires : ∀ (gs : List Gate) (w₁ w₂ : List Bool),
      w₁.length = w₂.length → m ≤ w₁.length →
      (∀ i (hi : i < m), w₁.getD i false = w₂.getD (e ⟨i, hi⟩).val false) →
      (∀ i, m ≤ i → w₁.getD i false = w₂.getD i false) →
      (wiresFrom gs w₁).length = (wiresFrom (gs.map remapGate) w₂).length ∧
      (∀ i (hi : i < m), (wiresFrom gs w₁).getD i false =
        (wiresFrom (gs.map remapGate) w₂).getD (e ⟨i, hi⟩).val false) ∧
      (∀ i, m ≤ i → (wiresFrom gs w₁).getD i false =
        (wiresFrom (gs.map remapGate) w₂).getD i false) := by
    intro gs
    induction gs with
    | nil => intro w₁ w₂ hlen _ hlt hge; exact ⟨hlen, hlt, hge⟩
    | cons g gs ih =>
      intro w₁ w₂ hlen hm hlt hge
      rw [List.map_cons, wiresFrom_cons, wiresFrom_cons]
      have harg : g.inputs.map (fun i => w₁.getD i false) =
          (remapGate g).inputs.map (fun i => w₂.getD i false) := by
        simp only [remapGate, List.map_map]
        apply List.map_congr_left
        intro i _
        simp only [Function.comp_apply, remapWire]
        by_cases hi : i < m
        · simp only [hi, ↓reduceDIte]; exact hlt i hi
        · simp only [hi, ↓reduceDIte]; exact hge i (by omega)
      rw [harg]
      apply ih
      · simp [hlen]
      · simp; omega
      · intro i hi
        rw [getD_snoc_lt _ _ _ i (by omega), getD_snoc_lt _ _ _ (e ⟨i, hi⟩).val (by have := (e ⟨i, hi⟩).isLt; omega)]
        exact hlt i hi
      · intro i hi
        by_cases heq : i = w₁.length
        · rw [getD_snoc_eq _ _ _ i heq, getD_snoc_eq _ _ _ i (by omega)]
        · rw [getD_snoc_ne _ _ _ i heq, getD_snoc_ne _ _ _ i (by omega)]
          exact hge i hi
  have h0 := hwires C.gates (List.ofFn (fun i => x (e i))) (List.ofFn x)
    (by simp) (by simp)
    (fun i hi => by rw [ofFn_getD_lt _ _ i hi, ofFn_getD_lt _ _ (e ⟨i, hi⟩).val (e ⟨i, hi⟩).isLt])
    (fun i hi => by
      rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)])
  show (wiresFrom (C.gates.map remapGate) (List.ofFn x)).getD (remapWire C.output) false = f (fun i => x (e i))
  rw [← hev (fun i => x (e i))]
  show (wiresFrom (C.gates.map remapGate) (List.ofFn x)).getD (remapWire C.output) false =
    (wiresFrom C.gates (List.ofFn (fun i => x (e i)))).getD C.output false
  dsimp only [remapWire]
  by_cases ho : C.output < m
  · simp only [ho, ↓reduceDIte]
    exact (h0.2.1 C.output ho).symm
  · simp only [ho, ↓reduceDIte]
    exact (h0.2.2 C.output (by omega)).symm

private def gateUses (C : Circuit) (w : ℕ) : Finset (Fin C.gates.length) :=
  Finset.univ.filter (fun k : Fin C.gates.length => w ∈ C.gates[k.val].inputs)

private lemma mem_gateUses {C : Circuit} {w : ℕ} {k : Fin C.gates.length} :
    k ∈ gateUses C w ↔ w ∈ C.gates[k.val].inputs := by
  simp [gateUses]

private lemma consumer_gt_of_minimal {m : ℕ} {F : (Fin m → Bool) → Bool} {C : Circuit}
    (hmin : MinimalCircuit m F C)
    (hnc : ∃ x x' : Fin m → Bool, F x ≠ F x')
    (k₁ k₂ : Fin C.gates.length)
    (hmem : m + k₁.val ∈ C.gates[k₂.val].inputs) :
    k₁.val < k₂.val := by
  rcases minimal_gate_shape hmin hnc k₂.val k₂.isLt with
    ⟨_, a, ha, hin⟩ | ⟨_, a, b, ha, hb, _, hin⟩
  · rw [hin] at hmem; simp at hmem; omega
  · rw [hin] at hmem; simp at hmem; rcases hmem with rfl | rfl <;> omega

private lemma gate_const_has_consumer {m : ℕ} {F : (Fin m → Bool) → Bool} {C : Circuit}
    (hmin : MinimalCircuit m F C)
    (hnc : ∃ x x' : Fin m → Bool, F x ≠ F x')
    (a : Fin m → Option Bool)
    (hnc' : ∃ x x' : Fin m → Bool, F (applyAssign a x) ≠ F (applyAssign a x'))
    (k : Fin C.gates.length) (c : Bool)
    (hc : finalSt m C.gates (initAssign m a) (m + k.val) = Sum.inl c) :
    ∃ k' : Fin C.gates.length, k.val < k'.val ∧ m + k.val ∈ C.gates[k'.val].inputs ∧
      isElim m C.gates (initAssign m a) k' = true := by
  have hout_ne : C.output ≠ m + k.val := by
    intro heq
    obtain ⟨_, _, _, _, hout_eq⟩ := elim_run_circuit hmin a hnc'
    rw [heq, hc] at hout_eq
    exact Sum.inl_ne_inr hout_eq
  obtain ⟨k', hklt, hk'lt, hk'mem⟩ := minimal_gate_used hmin hnc k.val k.isLt hout_ne
  have hst₀ : (initAssign m a).length = m := by simp [initAssign]
  have helim := elim_const_input hmin hnc _ hst₀ ⟨k', hk'lt⟩ (m + k.val) hk'mem ⟨c, hc⟩
  exact ⟨⟨k', hk'lt⟩, hklt, hk'mem, helim⟩

private lemma wireFn_input {m : ℕ} (C : Circuit) (i : Fin m) (x : Fin m → Bool) :
    wireFn C i.val x = x i := by
  simp only [wireFn, Circuit.wires]
  show (wiresFrom C.gates (List.ofFn x)).getD i.val false = x i
  rw [wiresFrom_getD_lt _ _ i.val (by simp [i.isLt]), ofFn_getD_lt _ _ i.val i.isLt]

private lemma minimal_no_not_and_same_var {m : ℕ} {F : (Fin m → Bool) → Bool} {C : Circuit}
    (hmin : MinimalCircuit m F C)
    (hnc : ∃ x x' : Fin m → Bool, F x ≠ F x')
    (k₁ k₂ : Fin C.gates.length) (w : ℕ) (hw : w < m + k₁.val)
    (hg₁ : C.gates[k₁.val] = ⟨GateOp.not, [w]⟩)
    (hmem₁ : w ∈ C.gates[k₂.val].inputs)
    (hmem₂ : m + k₁.val ∈ C.gates[k₂.val].inputs) : False := by
  have hklt := consumer_gt_of_minimal hmin hnc k₁ k₂ hmem₂
  rcases minimal_gate_shape hmin hnc k₂.val k₂.isLt with
    ⟨_, a, _, hin⟩ | ⟨hop, a, b, ha, hb, _, hin⟩
  · rw [hin] at hmem₁ hmem₂; simp at hmem₁ hmem₂; omega
  · have hpair : (a = w ∧ b = m + k₁.val) ∨ (a = m + k₁.val ∧ b = w) := by
      rw [hin] at hmem₁ hmem₂; simp at hmem₁ hmem₂
      rcases hmem₁ with rfl | rfl <;> rcases hmem₂ with h | h <;> first | exact Or.inl ⟨rfl, h.symm⟩ | exact Or.inr ⟨h.symm, rfl⟩ | omega
    have hfn1 : ∀ x : Fin m → Bool, wireFn C (m + k₁.val) x = !wireFn C w x := by
      intro x
      rw [wireFn_gate C k₁.val k₁.isLt x, hg₁]
      simp [GateOp.eval, hw]
    rcases hop with hop | hop
    · obtain ⟨x, hx⟩ := minimal_wire_nonconst hmin hnc k₂.val k₂.isLt false
      rw [wireFn_gate C k₂.val k₂.isLt x, hop, hin] at hx
      rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        simp [GateOp.eval, ha, hb, hfn1 x] at hx
    · obtain ⟨x, hx⟩ := minimal_wire_nonconst hmin hnc k₂.val k₂.isLt true
      rw [wireFn_gate C k₂.val k₂.isLt x, hop, hin] at hx
      rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        simp [GateOp.eval, ha, hb, hfn1 x] at hx

private lemma minimal_no_absorb {m : ℕ} {F : (Fin m → Bool) → Bool} {C : Circuit}
    (hmin : MinimalCircuit m F C)
    (hnc : ∃ x x' : Fin m → Bool, F x ≠ F x')
    (k₁ k₂ : Fin C.gates.length) (w : ℕ) (hw : w < m + k₁.val)
    (hbin : C.gates[k₁.val].op = GateOp.and ∨ C.gates[k₁.val].op = GateOp.or)
    (hw₁ : w ∈ C.gates[k₁.val].inputs)
    (hmem₁ : w ∈ C.gates[k₂.val].inputs)
    (hmem₂ : m + k₁.val ∈ C.gates[k₂.val].inputs) : False := by
  have hklt := consumer_gt_of_minimal hmin hnc k₁ k₂ hmem₂
  rcases minimal_gate_shape hmin hnc k₁.val k₁.isLt with
    ⟨hop1, _, _, _⟩ | ⟨hop1, a₁, b₁, ha₁, hb₁, _, hin₁⟩
  · rcases hbin with h | h <;> rw [hop1] at h <;> cases h
  · rcases minimal_gate_shape hmin hnc k₂.val k₂.isLt with
      ⟨_, a₂, _, hin₂⟩ | ⟨hop2, a₂, b₂, ha₂, hb₂, _, hin₂⟩
    · rw [hin₂] at hmem₁ hmem₂; simp at hmem₁ hmem₂; omega
    · have hpair : (a₂ = w ∧ b₂ = m + k₁.val) ∨ (a₂ = m + k₁.val ∧ b₂ = w) := by
        rw [hin₂] at hmem₁ hmem₂; simp at hmem₁ hmem₂
        rcases hmem₁ with rfl | rfl <;> rcases hmem₂ with h | h <;> first | exact Or.inl ⟨rfl, h.symm⟩ | exact Or.inr ⟨h.symm, rfl⟩ | omega
      rw [hin₁] at hw₁; simp at hw₁
      rcases hop1 with hop1 | hop1 <;> rcases hop2 with hop2 | hop2
      · obtain ⟨x, hx⟩ := minimal_wire_ne_earlier hmin hnc k₂.val k₂.isLt (m + k₁.val) (by omega)
        rw [wireFn_gate C k₂.val k₂.isLt x, hop2, hin₂] at hx
        have h1x := wireFn_gate C k₁.val k₁.isLt x
        rw [hop1, hin₁] at h1x
        rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hw₁ with rfl | rfl <;>
          (simp [GateOp.eval, ha₁, hb₁, ha₂, hb₂] at h1x hx; rw [h1x] at hx; grind)
      · obtain ⟨x, hx⟩ := minimal_wire_ne_earlier hmin hnc k₂.val k₂.isLt w (by omega)
        rw [wireFn_gate C k₂.val k₂.isLt x, hop2, hin₂] at hx
        have h1x := wireFn_gate C k₁.val k₁.isLt x
        rw [hop1, hin₁] at h1x
        rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hw₁ with rfl | rfl <;>
          (simp [GateOp.eval, ha₁, hb₁, ha₂, hb₂] at h1x hx; rw [h1x] at hx; grind)
      · obtain ⟨x, hx⟩ := minimal_wire_ne_earlier hmin hnc k₂.val k₂.isLt w (by omega)
        rw [wireFn_gate C k₂.val k₂.isLt x, hop2, hin₂] at hx
        have h1x := wireFn_gate C k₁.val k₁.isLt x
        rw [hop1, hin₁] at h1x
        rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hw₁ with rfl | rfl <;>
          (simp [GateOp.eval, ha₁, hb₁, ha₂, hb₂] at h1x hx; rw [h1x] at hx; grind)
      · obtain ⟨x, hx⟩ := minimal_wire_ne_earlier hmin hnc k₂.val k₂.isLt (m + k₁.val) (by omega)
        rw [wireFn_gate C k₂.val k₂.isLt x, hop2, hin₂] at hx
        have h1x := wireFn_gate C k₁.val k₁.isLt x
        rw [hop1, hin₁] at h1x
        rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hw₁ with rfl | rfl <;>
          (simp [GateOp.eval, ha₁, hb₁, ha₂, hb₂] at h1x hx; rw [h1x] at hx; grind)

private lemma minimal_no_double_not {m : ℕ} {F : (Fin m → Bool) → Bool} {C : Circuit}
    (hmin : MinimalCircuit m F C)
    (hnc : ∃ x x' : Fin m → Bool, F x ≠ F x')
    (k₁ k₂ : Fin C.gates.length) (w : ℕ) (hw : w < m + k₁.val)
    (hg₁ : C.gates[k₁.val] = ⟨GateOp.not, [w]⟩)
    (hg₂ : C.gates[k₂.val] = ⟨GateOp.not, [m + k₁.val]⟩) : False := by
  have hklt : k₁.val < k₂.val :=
    consumer_gt_of_minimal hmin hnc k₁ k₂ (by rw [hg₂]; simp)
  obtain ⟨x, hx⟩ := minimal_wire_ne_earlier hmin hnc k₂.val k₂.isLt w (by omega)
  have h1 := wireFn_gate C k₁.val k₁.isLt x
  have h2 := wireFn_gate C k₂.val k₂.isLt x
  rw [hg₁] at h1; rw [hg₂] at h2
  simp only [GateOp.eval, List.map_cons, List.map_nil, List.headD_cons, hw, ↓reduceIte,
    show m + k₁.val < m + k₂.val by omega] at h1 h2
  rw [h2, h1, Bool.not_not] at hx
  exact hx rfl

private lemma not_gate_structure {m L₀ : ℕ} {F : (Fin m → Bool) → Bool} {C : Circuit}
    (hmin : MinimalCircuit m F C)
    (hnc : ∃ x x' : Fin m → Bool, F x ≠ F x')
    (v : Fin m)
    (hnc0 : ∃ x x' : Fin m → Bool, F (Function.update x v false) ≠ F (Function.update x' v false))
    (hlow0 : ∀ s, HasCircuitSize m (fun x => F (Function.update x v false)) s → L₀ ≤ s)
    (hsz : C.gates.length ≤ L₀ + 2)
    (k₀ : Fin C.gates.length) (hk₀ : C.gates[k₀.val] = ⟨GateOp.not, [v.val]⟩) :
    gateUses C v.val = {k₀} ∧
    ∃ k₁ : Fin C.gates.length, gateUses C (m + k₀.val) = {k₁} ∧ C.gates[k₁.val].op = GateOp.and := by
  have hst₀ : (initAssign m (singleAssign v false)).length = m := by simp [initAssign]
  have hnc0' : ∃ x x' : Fin m → Bool,
      F (applyAssign (singleAssign v false) x) ≠ F (applyAssign (singleAssign v false) x') := by
    simpa [applyAssign_single] using hnc0
  have hfv : finalSt m C.gates (initAssign m (singleAssign v false)) v.val = Sum.inl false := by
    rw [finalSt_init m C.gates _ v.val (by rw [hst₀]; exact v.isLt), initAssign, ofFn_getD_lt _ _ v.val v.isLt]
    simp [singleAssign]
  have hs0 := runAt_step_not m C.gates (initAssign m (singleAssign v false)) hst₀ k₀ v.val (by have := v.isLt; omega) hk₀
  rw [hfv] at hs0
  obtain ⟨he0, hf0⟩ := hs0
  have hno3 : ∀ (K : Finset (Fin C.gates.length)),
      (∀ k ∈ K, isElim m C.gates (initAssign m (singleAssign v false)) k = true) → K.card ≤ 2 := by
    intro K hK
    obtain ⟨hle, hcs⟩ := elim_size_of_card hmin (singleAssign v false) hnc0' K hK
    have hrew : (fun x => F (applyAssign (singleAssign v false) x)) =
        (fun x => F (Function.update x v false)) := by ext x; rw [applyAssign_single]
    rw [hrew] at hcs
    have := hlow0 _ hcs
    omega
  obtain ⟨k₁, hk₀₁, hk₁mem, he1⟩ := gate_const_has_consumer hmin hnc (singleAssign v false) hnc0' k₀ true hf0
  have hk₁ne : k₁ ≠ k₀ := fun h => by have := congrArg Fin.val h; omega
  have hv_uses : gateUses C v.val = {k₀} := by
    ext k
    simp only [mem_gateUses, Finset.mem_singleton]
    constructor
    · intro hkv
      by_contra hne
      have hek := elim_const_input hmin hnc _ hst₀ k v.val hkv ⟨false, hfv⟩
      have hkne1 : k ≠ k₁ := by
        intro heq; subst heq
        exact minimal_no_not_and_same_var hmin hnc k₀ k v.val (by have := v.isLt; omega) hk₀ hkv hk₁mem
      have hcard3 : ({k₀, k₁, k} : Finset (Fin C.gates.length)).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp [hk₁ne.symm, Ne.symm hne]),
            Finset.card_pair hkne1.symm]
      have hle2 := hno3 {k₀, k₁, k} (by
        intro j hj; simp only [Finset.mem_insert, Finset.mem_singleton] at hj
        rcases hj with rfl | rfl | rfl <;> assumption)
      omega
    · rintro rfl; rw [hk₀]; simp
  have hk₀_uses : gateUses C (m + k₀.val) = {k₁} := by
    ext k
    simp only [mem_gateUses, Finset.mem_singleton]
    constructor
    · intro hkm
      by_contra hne
      have hek := elim_const_input hmin hnc _ hst₀ k (m + k₀.val) hkm ⟨true, hf0⟩
      have hkne0 : k ≠ k₀ := fun h => by
        have hlt := consumer_gt_of_minimal hmin hnc k₀ k hkm
        have := congrArg Fin.val h; omega
      have hcard3 : ({k₀, k₁, k} : Finset (Fin C.gates.length)).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp [hk₁ne.symm, hkne0.symm]),
            Finset.card_pair (Ne.symm hne)]
      have hle2 := hno3 {k₀, k₁, k} (by
        intro j hj; simp only [Finset.mem_insert, Finset.mem_singleton] at hj
        rcases hj with rfl | rfl | rfl <;> assumption)
      omega
    · rintro rfl; exact hk₁mem
  have hk₁_and : C.gates[k₁.val].op = GateOp.and := by
    rcases minimal_gate_shape hmin hnc k₁.val k₁.isLt with
      ⟨hop, a, _, hin⟩ | ⟨hop, a, b, ha, hb, _, hin⟩
    · exfalso
      rw [hin] at hk₁mem; simp at hk₁mem; subst hk₁mem
      have hg1 : C.gates[k₁.val] = ⟨GateOp.not, [m + k₀.val]⟩ := by cases h : C.gates[k₁.val]; simp_all
      exact minimal_no_double_not hmin hnc k₀ k₁ v.val (by have := v.isLt; omega) hk₀ hg1
    · rcases hop with hop | hop
      · exact hop
      · exfalso
        have hg1 : C.gates[k₁.val] = ⟨GateOp.or, [a, b]⟩ := by cases h : C.gates[k₁.val]; simp_all
        rw [hin] at hk₁mem; simp at hk₁mem
        have hs1 := runAt_step_or m C.gates (initAssign m (singleAssign v false)) hst₀ k₁ a b ha hb hg1
        have hf1 : finalSt m C.gates (initAssign m (singleAssign v false)) (m + k₁.val) = Sum.inl true := by
          rcases hk₁mem with rfl | rfl
          · rw [hf0] at hs1; cases hfb : finalSt m C.gates _ b <;> rw [hfb] at hs1 <;> simpa using hs1.2
          · rw [hf0] at hs1; cases hfa : finalSt m C.gates _ a <;> rw [hfa] at hs1 <;> simpa using hs1.2
        obtain ⟨k₂, hk₁₂, _, he2⟩ := gate_const_has_consumer hmin hnc (singleAssign v false) hnc0' k₁ true hf1
        have hne20 : k₂ ≠ k₀ := fun h => by have := congrArg Fin.val h; omega
        have hne21 : k₂ ≠ k₁ := fun h => by have := congrArg Fin.val h; omega
        have hcard3 : ({k₀, k₁, k₂} : Finset (Fin C.gates.length)).card = 3 := by
          rw [Finset.card_insert_of_notMem (by simp [hk₁ne.symm, hne20.symm]),
              Finset.card_pair hne21.symm]
        have hle2 := hno3 {k₀, k₁, k₂} (by
          intro j hj; simp only [Finset.mem_insert, Finset.mem_singleton] at hj
          rcases hj with rfl | rfl | rfl <;> assumption)
        omega
  exact ⟨hv_uses, k₁, hk₀_uses, hk₁_and⟩

private lemma var_fanout_one_of_bounds {m L₀ L₁ : ℕ} {F : (Fin m → Bool) → Bool} {C : Circuit}
    (hmin : MinimalCircuit m F C)
    (v : Fin m)
    (hdep : ∃ x : Fin m → Bool, F (Function.update x v false) ≠ F (Function.update x v true))
    (hnc0 : ∃ x x' : Fin m → Bool, F (Function.update x v false) ≠ F (Function.update x' v false))
    (hnc1 : ∃ x x' : Fin m → Bool, F (Function.update x v true) ≠ F (Function.update x' v true))
    (hlow0 : ∀ s, HasCircuitSize m (fun x => F (Function.update x v false)) s → L₀ ≤ s)
    (hlow1 : ∀ s, HasCircuitSize m (fun x => F (Function.update x v true)) s → L₁ ≤ s)
    (hsz0 : C.gates.length ≤ L₀ + 2)
    (hsz1 : C.gates.length ≤ L₁ + 3) :
    ∃ k₀ : Fin C.gates.length, gateUses C v.val = {k₀} := by
  have hnc : ∃ x x' : Fin m → Bool, F x ≠ F x' := by obtain ⟨x, hne⟩ := hdep; exact ⟨_, _, hne⟩
  have hout_ne := output_ne_of_nonconst_update hmin v false hnc0
  obtain ⟨k₁, hk₁⟩ := var_has_consumer hmin v hdep hout_ne
  have hst₀ (b : Bool) : (initAssign m (singleAssign v b)).length = m := by simp [initAssign]
  have hfv (b : Bool) : finalSt m C.gates (initAssign m (singleAssign v b)) v.val = Sum.inl b := by
    rw [finalSt_init m C.gates _ v.val (by rw [hst₀ b]; exact v.isLt), initAssign, ofFn_getD_lt _ _ v.val v.isLt]
    simp [singleAssign]
  have hnc0' : ∃ x x', F (applyAssign (singleAssign v false) x) ≠ F (applyAssign (singleAssign v false) x') := by
    simpa [applyAssign_single] using hnc0
  have hnc1' : ∃ x x', F (applyAssign (singleAssign v true) x) ≠ F (applyAssign (singleAssign v true) x') := by
    simpa [applyAssign_single] using hnc1
  have hno3_0 : ∀ K : Finset (Fin C.gates.length),
      (∀ k ∈ K, isElim m C.gates (initAssign m (singleAssign v false)) k = true) → K.card ≤ 2 := by
    intro K hK
    obtain ⟨hle, hcs⟩ := elim_size_of_card hmin (singleAssign v false) hnc0' K hK
    have hrew : (fun x => F (applyAssign (singleAssign v false) x)) =
        (fun x => F (Function.update x v false)) := by ext x; rw [applyAssign_single]
    rw [hrew] at hcs
    have := hlow0 _ hcs; omega
  have hno4_1 : ∀ K : Finset (Fin C.gates.length),
      (∀ k ∈ K, isElim m C.gates (initAssign m (singleAssign v true)) k = true) → K.card ≤ 3 := by
    intro K hK
    obtain ⟨hle, hcs⟩ := elim_size_of_card hmin (singleAssign v true) hnc1' K hK
    have hrew : (fun x => F (applyAssign (singleAssign v true) x)) =
        (fun x => F (Function.update x v true)) := by ext x; rw [applyAssign_single]
    rw [hrew] at hcs
    have := hlow1 _ hcs; omega
  by_cases hother : ∃ k₂ : Fin C.gates.length, k₂ ≠ k₁ ∧ v.val ∈ C.gates[k₂.val].inputs
  · exfalso
    obtain ⟨k₂, hne12, hk₂⟩ := hother
    have hpair_or : ∀ (a b : Fin C.gates.length), a ≠ b →
        v.val ∈ C.gates[a.val].inputs → v.val ∈ C.gates[b.val].inputs →
        C.gates[a.val].op = GateOp.or := by
      intro a b hab ha hb
      have hea0 := elim_const_input hmin hnc _ (hst₀ false) a v.val ha ⟨false, hfv false⟩
      have heb0 := elim_const_input hmin hnc _ (hst₀ false) b v.val hb ⟨false, hfv false⟩
      rcases minimal_gate_shape hmin hnc a.val a.isLt with
        ⟨hop, u, hu, hin⟩ | ⟨hop, u, w, hu, hw, _, hin⟩
      · exfalso
        rw [hin] at ha; simp at ha; subst ha
        have hga : C.gates[a.val] = ⟨GateOp.not, [v.val]⟩ := by cases h : C.gates[a.val]; simp_all
        have hst := not_gate_structure hmin hnc v hnc0 hlow0 hsz0 a hga
        have hmem : b ∈ gateUses C v.val := mem_gateUses.2 hb
        rw [hst.1, Finset.mem_singleton] at hmem
        exact hab hmem.symm
      · rcases hop with hop | hop
        · exfalso
          have hga : C.gates[a.val] = ⟨GateOp.and, [u, w]⟩ := by cases h : C.gates[a.val]; simp_all
          rw [hin] at ha; simp at ha
          have hs := runAt_step_and m C.gates (initAssign m (singleAssign v false)) (hst₀ false) a u w hu hw hga
          have hfa : finalSt m C.gates (initAssign m (singleAssign v false)) (m + a.val) = Sum.inl false := by
            rcases ha with rfl | rfl
            · rw [hfv false] at hs; cases hfw : finalSt m C.gates _ w <;> rw [hfw] at hs <;> simpa using hs.2
            · rw [hfv false] at hs; cases hfu : finalSt m C.gates _ u <;> rw [hfu] at hs <;> simpa using hs.2
          obtain ⟨c, hac, hcmem, hec⟩ := gate_const_has_consumer hmin hnc (singleAssign v false) hnc0' a false hfa
          have hca : c ≠ a := fun h => by have := congrArg Fin.val h; omega
          have hcb : c ≠ b := by
            intro heq; subst heq
            exact minimal_no_absorb hmin hnc a c v.val (by have := v.isLt; omega)
              (Or.inl hop) (by rw [hin]; simp [ha]) hb hcmem
          have hcard3 : ({a, b, c} : Finset (Fin C.gates.length)).card = 3 := by
            rw [Finset.card_insert_of_notMem (by simp [hab, hca.symm]),
                Finset.card_pair hcb.symm]
          have hle2 := hno3_0 {a, b, c} (by
            intro j hj; simp only [Finset.mem_insert, Finset.mem_singleton] at hj
            rcases hj with rfl | rfl | rfl <;> assumption)
          omega
        · exact hop
    have hop1 : C.gates[k₁.val].op = GateOp.or := hpair_or k₁ k₂ hne12.symm hk₁ hk₂
    have hop2 : C.gates[k₂.val].op = GateOp.or := hpair_or k₂ k₁ hne12 hk₂ hk₁
    have hconst1 : ∀ (k : Fin C.gates.length), C.gates[k.val].op = GateOp.or →
        v.val ∈ C.gates[k.val].inputs →
        isElim m C.gates (initAssign m (singleAssign v true)) k = true ∧
        finalSt m C.gates (initAssign m (singleAssign v true)) (m + k.val) = Sum.inl true := by
      intro k hopk hkv
      rcases minimal_gate_shape hmin hnc k.val k.isLt with
        ⟨hnot, _, _, _⟩ | ⟨_, u, w, hu, hw, _, hin⟩
      · rw [hopk] at hnot; cases hnot
      · have hgk : C.gates[k.val] = ⟨GateOp.or, [u, w]⟩ := by cases h : C.gates[k.val]; simp_all
        rw [hin] at hkv; simp at hkv
        have hs := runAt_step_or m C.gates (initAssign m (singleAssign v true)) (hst₀ true) k u w hu hw hgk
        rcases hkv with rfl | rfl
        · rw [hfv true] at hs; cases hfw : finalSt m C.gates _ w <;> rw [hfw] at hs <;> exact ⟨hs.1, by simpa using hs.2⟩
        · rw [hfv true] at hs; cases hfu : finalSt m C.gates _ u <;> rw [hfu] at hs <;> exact ⟨hs.1, by simpa using hs.2⟩
    obtain ⟨he1, hf1⟩ := hconst1 k₁ hop1 hk₁
    obtain ⟨he2, hf2⟩ := hconst1 k₂ hop2 hk₂
    obtain ⟨h₁, hk₁h₁, hh₁mem, heh₁⟩ := gate_const_has_consumer hmin hnc (singleAssign v true) hnc1' k₁ true hf1
    obtain ⟨h₂, hk₂h₂, hh₂mem, heh₂⟩ := gate_const_has_consumer hmin hnc (singleAssign v true) hnc1' k₂ true hf2
    have hh₁ne1 : h₁ ≠ k₁ := fun h => by have := congrArg Fin.val h; omega
    have hh₂ne2 : h₂ ≠ k₂ := fun h => by have := congrArg Fin.val h; omega
    have hh₁ne2 : h₁ ≠ k₂ := by
      intro heq; subst heq
      exact minimal_no_absorb hmin hnc k₁ h₁ v.val (by have := v.isLt; omega) (Or.inr hop1) hk₁ hk₂ hh₁mem
    have hh₂ne1 : h₂ ≠ k₁ := by
      intro heq; subst heq
      exact minimal_no_absorb hmin hnc k₂ h₂ v.val (by have := v.isLt; omega) (Or.inr hop2) hk₂ hk₁ hh₂mem
    by_cases hsame : h₁ = h₂
    · subst hsame
      have hfh1 : ∃ c : Bool, finalSt m C.gates (initAssign m (singleAssign v true)) (m + h₁.val) = Sum.inl c := by
        rcases minimal_gate_shape hmin hnc h₁.val h₁.isLt with
          ⟨hnot, a, ha, hin⟩ | ⟨hop, a, b, ha, hb, _, hin⟩
        · rw [hin] at hh₁mem; simp at hh₁mem; subst hh₁mem
          have hgh : C.gates[h₁.val] = ⟨GateOp.not, [m + k₁.val]⟩ := by cases h : C.gates[h₁.val]; simp_all
          have hs := runAt_step_not m C.gates (initAssign m (singleAssign v true)) (hst₀ true) h₁ (m + k₁.val) ha hgh
          rw [hf1] at hs; exact ⟨false, hs.2⟩
        · have hpair : (a = m + k₁.val ∧ b = m + k₂.val) ∨ (a = m + k₂.val ∧ b = m + k₁.val) := by
            rw [hin] at hh₁mem hh₂mem; simp at hh₁mem hh₂mem
            have hne_val : m + k₁.val ≠ m + k₂.val := fun h => hne12 (Fin.ext (by omega)).symm
            rcases hh₁mem with rfl | rfl <;> rcases hh₂mem with h | h <;>
              first | exact Or.inl ⟨rfl, h.symm⟩ | exact Or.inr ⟨h.symm, rfl⟩ | exact absurd h.symm hne_val
          rcases hop with hop | hop
          · have hgh : C.gates[h₁.val] = ⟨GateOp.and, [a, b]⟩ := by cases h : C.gates[h₁.val]; simp_all
            have hs := runAt_step_and m C.gates (initAssign m (singleAssign v true)) (hst₀ true) h₁ a b ha hb hgh
            rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rw [hf1, hf2] at hs <;> exact ⟨true, hs.2⟩
          · have hgh : C.gates[h₁.val] = ⟨GateOp.or, [a, b]⟩ := by cases h : C.gates[h₁.val]; simp_all
            have hs := runAt_step_or m C.gates (initAssign m (singleAssign v true)) (hst₀ true) h₁ a b ha hb hgh
            rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rw [hf1, hf2] at hs <;> exact ⟨true, hs.2⟩
      obtain ⟨c, hfc⟩ := hfh1
      obtain ⟨h₃, hh₁₃, _, heh₃⟩ := gate_const_has_consumer hmin hnc (singleAssign v true) hnc1' h₁ c hfc
      have hh₃ne1 : h₃ ≠ k₁ := fun h => by have := congrArg Fin.val h; omega
      have hh₃ne2 : h₃ ≠ k₂ := fun h => by have := congrArg Fin.val h; omega
      have hh₃neh : h₃ ≠ h₁ := fun h => by have := congrArg Fin.val h; omega
      have hcard4 : ({k₁, k₂, h₁, h₃} : Finset (Fin C.gates.length)).card = 4 := by
        rw [Finset.card_insert_of_notMem (by simp [hne12.symm, hh₁ne1.symm, hh₃ne1.symm]),
            Finset.card_insert_of_notMem (by simp [hh₁ne2.symm, hh₃ne2.symm]),
            Finset.card_pair hh₃neh.symm]
      have hle3 := hno4_1 {k₁, k₂, h₁, h₃} (by
        intro j hj; simp only [Finset.mem_insert, Finset.mem_singleton] at hj
        rcases hj with rfl | rfl | rfl | rfl <;> assumption)
      omega
    · have hcard4 : ({k₁, k₂, h₁, h₂} : Finset (Fin C.gates.length)).card = 4 := by
        rw [Finset.card_insert_of_notMem (by simp [hne12.symm, hh₁ne1.symm, hh₂ne1.symm]),
            Finset.card_insert_of_notMem (by simp [hh₁ne2.symm, hh₂ne2.symm]),
            Finset.card_pair hsame]
      have hle3 := hno4_1 {k₁, k₂, h₁, h₂} (by
        intro j hj; simp only [Finset.mem_insert, Finset.mem_singleton] at hj
        rcases hj with rfl | rfl | rfl | rfl <;> assumption)
      omega
  · push Not at hother
    refine ⟨k₁, ?_⟩
    ext k
    simp only [mem_gateUses, Finset.mem_singleton]
    constructor
    · intro hkv; by_contra hne; exact hother k hne hkv
    · rintro rfl; exact hk₁

private lemma fanout1_bin_dep_contradiction {m : ℕ} {F : (Fin m → Bool) → Bool} {C : Circuit}
    (hmin : MinimalCircuit m F C)
    (v_a v_b : Fin m)
    (c_b : Bool)
    (hdep : ∃ x : Fin m → Bool,
      F (Function.update (Function.update x v_b c_b) v_a false) ≠
      F (Function.update (Function.update x v_b c_b) v_a true))
    (S : Set ℕ) (hSa : v_a.val ∈ S) (hSout : C.output ∉ S)
    (hS_gate : ∀ j (hj : j < C.gates.length), m + j ∉ S →
      (∀ i ∈ C.gates[j].inputs, i ∉ S) ∨
      (∀ x : Fin m → Bool,
        wireFn C (m + j) (Function.update (Function.update x v_b c_b) v_a false) =
        wireFn C (m + j) (Function.update (Function.update x v_b c_b) v_a true))) : False := by
  obtain ⟨x, hne_F⟩ := hdep
  let x₀ := Function.update (Function.update x v_b c_b) v_a false
  let x₁ := Function.update (Function.update x v_b c_b) v_a true
  have hall : ∀ k (hk : k ≤ C.gates.length),
      ∀ w < m + k, w ∉ S →
        (wiresFrom (C.gates.take k) (List.ofFn x₀)).getD w false =
        (wiresFrom (C.gates.take k) (List.ofFn x₁)).getD w false := by
    intro k
    induction k with
    | zero =>
      intro _ w hw hwS
      simp only [List.take_zero, wiresFrom_nil]
      have hwm : w < m := by omega
      rw [ofFn_getD_lt _ _ w hwm, ofFn_getD_lt _ _ w hwm]
      have hwne : (⟨w, hwm⟩ : Fin m) ≠ v_a := fun h => hwS (by rw [← congrArg Fin.val h] at hSa; exact hSa)
      simp only [x₀, x₁, Function.update_of_ne hwne]
    | succ k ih =>
      intro hk w hw hwS
      have hlt : k < C.gates.length := by omega
      have htake : C.gates.take (k + 1) = C.gates.take k ++ [C.gates[k]] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hlt, Option.toList_some]
      have hlen0 : (wiresFrom (C.gates.take k) (List.ofFn x₀)).length = m + k := by
        rw [wiresFrom_length, List.length_ofFn, List.length_take_of_le (by omega)]
      have hlen1 : (wiresFrom (C.gates.take k) (List.ofFn x₁)).length = m + k := by
        rw [wiresFrom_length, List.length_ofFn, List.length_take_of_le (by omega)]
      simp only [htake, wiresFrom_append, wiresFrom_cons, wiresFrom_nil]
      by_cases hwk : w < m + k
      · rw [getD_snoc_lt _ _ _ w (by omega), getD_snoc_lt _ _ _ w (by omega)]
        exact ih (by omega) w hwk hwS
      · have hweq : w = m + k := by omega
        subst hweq
        rw [getD_snoc_eq _ _ _ (m + k) hlen0.symm, getD_snoc_eq _ _ _ (m + k) hlen1.symm]
        rcases hS_gate k hlt hwS with hnoS | hsame
        · congr 1
          apply List.map_congr_left
          intro i hi
          by_cases himk : i < m + k
          · exact ih (by omega) i himk (hnoS i hi)
          · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
        · have hwf (y : Fin m → Bool) :
              (wiresFrom (C.gates.take k) (List.ofFn y) ++
                [C.gates[k].op.eval (C.gates[k].inputs.map fun i => (wiresFrom (C.gates.take k) (List.ofFn y)).getD i false)]).getD (m + k) false =
              wireFn C (m + k) y := by
            have hsplit : C.gates = C.gates.take (k + 1) ++ C.gates.drop (k + 1) := (List.take_append_drop (k + 1) C.gates).symm
            have hly : (wiresFrom (C.gates.take k) (List.ofFn y)).length = m + k := by
              rw [wiresFrom_length, List.length_ofFn, List.length_take_of_le (by omega)]
            simp only [wireFn, Circuit.wires]
            show _ = (wiresFrom C.gates (List.ofFn y)).getD (m + k) false
            conv_rhs => rw [hsplit, wiresFrom_append]
            rw [wiresFrom_getD_lt _ _ (m + k) (by rw [htake, wiresFrom_append, wiresFrom_cons, wiresFrom_nil]; simp [hly])]
            rw [htake, wiresFrom_append, wiresFrom_cons, wiresFrom_nil]
          have h0 := hwf x₀
          have h1 := hwf x₁
          rw [getD_snoc_eq _ _ _ (m + k) hlen0.symm] at h0
          rw [getD_snoc_eq _ _ _ (m + k) hlen1.symm] at h1
          rw [h0, h1]
          exact hsame x
  have hout_eq : C.eval (List.ofFn x₀) = C.eval (List.ofFn x₁) := by
    by_cases ho : C.output < m + C.gates.length
    · have h := hall C.gates.length le_rfl C.output ho hSout
      rw [List.take_length] at h
      exact h
    · show (wiresFrom C.gates (List.ofFn x₀)).getD C.output false =
        (wiresFrom C.gates (List.ofFn x₁)).getD C.output false
      rw [List.getD_eq_default _ _ (by rw [wiresFrom_length, List.length_ofFn]; omega),
          List.getD_eq_default _ _ (by rw [wiresFrom_length, List.length_ofFn]; omega)]
  exact hne_F ((hmin.2.1 x₀).symm.trans (hout_eq.trans (hmin.2.1 x₁)))

private lemma first_non_not_gate {m : ℕ} {F : (Fin m → Bool) → Bool} {C : Circuit}
    (hmin : MinimalCircuit m F C)
    (hnc : ∃ x x' : Fin m → Bool, F x ≠ F x')
    (hnotlit : ∀ i : Fin m, (∃ x, F x ≠ x i) ∧ (∃ x, F x ≠ !x i)) :
    ∃ k : Fin C.gates.length,
      (C.gates[k.val].op = GateOp.and ∨ C.gates[k.val].op = GateOp.or) ∧
      (∀ j : Fin C.gates.length, j.val < k.val →
        ∃ i : Fin m, C.gates[j.val] = ⟨GateOp.not, [i.val]⟩) := by
  classical
  have hex : ∃ n : ℕ, ∃ hn : n < C.gates.length, C.gates[n].op ≠ GateOp.not := by
    by_contra hall
    push Not at hall
    have hall_not : ∀ j (hj : j < C.gates.length), ∃ i : Fin m, C.gates[j] = ⟨GateOp.not, [i.val]⟩ := by
      intro j hj
      have hop := hall j hj
      rcases minimal_gate_shape hmin hnc j hj with ⟨_, a, ha, hin⟩ | ⟨hbin, _, _, _, _, _, _⟩
      · by_cases ham : a < m
        · exact ⟨⟨a, ham⟩, by cases h : C.gates[j]; simp_all⟩
        · exfalso
          have hlt : a - m < C.gates.length := by omega
          have hop' := hall (a - m) hlt
          rcases minimal_gate_shape hmin hnc (a - m) hlt with ⟨_, b, hb, hin'⟩ | ⟨hbin', _, _, _, _, _, _⟩
          · have hg1 : C.gates[a - m] = ⟨GateOp.not, [b]⟩ := by cases h : C.gates[a - m]; simp_all
            have hg2 : C.gates[j] = ⟨GateOp.not, [m + (a - m)]⟩ := by
              have hma : m + (a - m) = a := by omega
              rw [hma]; cases h : C.gates[j]; simp_all
            exact minimal_no_double_not hmin hnc ⟨a - m, hlt⟩ ⟨j, hj⟩ b hb hg1 hg2
          · rcases hbin' with h | h <;> rw [hop'] at h <;> cases h
      · rcases hbin with h | h <;> rw [hop] at h <;> cases h
    by_cases ho : C.output < m
    · obtain ⟨x, hx⟩ := (hnotlit ⟨C.output, ho⟩).1
      have hev := hmin.2.1 x
      have hw : C.eval (List.ofFn x) = x ⟨C.output, ho⟩ := by
        show (wiresFrom C.gates (List.ofFn x)).getD C.output false = x ⟨C.output, ho⟩
        rw [wiresFrom_getD_lt _ _ C.output (by simp [ho]), ofFn_getD_lt _ _ C.output ho]
      exact hx (hev.symm.trans hw)
    · by_cases ho2 : C.output < m + C.gates.length
      · obtain ⟨i, hgi⟩ := hall_not (C.output - m) (by omega)
        obtain ⟨x, hx⟩ := (hnotlit i).2
        have hev := hmin.2.1 x
        have hwf : wireFn C (m + (C.output - m)) x = !x i := by
          rw [wireFn_gate C (C.output - m) (by omega) x, hgi]
          simp [GateOp.eval, show i.val < m + (C.output - m) by have := i.isLt; omega, wireFn_input]
        have hceq : m + (C.output - m) = C.output := by omega
        rw [hceq] at hwf
        exact hx (hev.symm.trans hwf)
      · obtain ⟨x, x', hne⟩ := hnc
        have hev (y : Fin m → Bool) : F y = false := by
          rw [← hmin.2.1 y]
          show (wiresFrom C.gates (List.ofFn y)).getD C.output false = false
          exact List.getD_eq_default _ _ (by rw [wiresFrom_length, List.length_ofFn]; omega)
        exact hne ((hev x).trans (hev x').symm)
  set n := Nat.find hex with hn_def
  obtain ⟨hn_lt, hn_ne⟩ := Nat.find_spec hex
  refine ⟨⟨n, hn_lt⟩, ?_, ?_⟩
  · rcases minimal_gate_shape hmin hnc n hn_lt with ⟨hop, _, _, _⟩ | ⟨hbin, _, _, _, _, _, _⟩
    · exact absurd hop hn_ne
    · exact hbin
  · intro j hjk
    have hjkn : j.val < n := hjk
    have hnot : C.gates[j.val].op = GateOp.not := by
      by_contra hne
      have hle := Nat.find_min' hex ⟨j.isLt, hne⟩
      rw [← hn_def] at hle
      omega
    rcases minimal_gate_shape hmin hnc j.val j.isLt with ⟨_, a, ha, hin⟩ | ⟨hbin, _, _, _, _, _, _⟩
    · by_cases ham : a < m
      · exact ⟨⟨a, ham⟩, by cases h : C.gates[j.val]; simp_all⟩
      · exfalso
        have hlt : a - m < C.gates.length := by omega
        have hnot' : C.gates[a - m].op = GateOp.not := by
          by_contra hne'
          have hle := Nat.find_min' hex ⟨hlt, hne'⟩
          rw [← hn_def] at hle
          omega
        rcases minimal_gate_shape hmin hnc (a - m) hlt with ⟨_, b, hb, hin'⟩ | ⟨hbin', _, _, _, _, _, _⟩
        · have hg1 : C.gates[a - m] = ⟨GateOp.not, [b]⟩ := by cases h : C.gates[a - m]; simp_all
          have hg2 : C.gates[j.val] = ⟨GateOp.not, [m + (a - m)]⟩ := by
            have hma : m + (a - m) = a := by omega
            rw [hma]; cases h : C.gates[j.val]; simp_all
          exact minimal_no_double_not hmin hnc ⟨a - m, hlt⟩ j b hb hg1 hg2
        · rcases hbin' with h | h <;> rw [hnot'] at h <;> cases h
    · rcases hbin with h | h <;> rw [hnot] at h <;> cases h

private lemma bin_gate_kills_dep {m : ℕ} {F : (Fin m → Bool) → Bool} {C : Circuit}
    (hmin : MinimalCircuit m F C)
    (v_a v_b : Fin m) (hne : v_a ≠ v_b)
    (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (k_star : Fin C.gates.length) (wa wb : ℕ)
    (hk_star : C.gates[k_star.val] = ⟨op, [wa, wb]⟩ ∨ C.gates[k_star.val] = ⟨op, [wb, wa]⟩)
    (hwa : (wa = v_a.val ∧ gateUses C v_a.val = {k_star}) ∨
      ∃ k_a : Fin C.gates.length, wa = m + k_a.val ∧
        C.gates[k_a.val] = ⟨GateOp.not, [v_a.val]⟩ ∧
        gateUses C v_a.val = {k_a} ∧ gateUses C (m + k_a.val) = {k_star})
    (hwb : wb = v_b.val ∨ ∃ k_b : Fin C.gates.length, wb = m + k_b.val ∧
      C.gates[k_b.val] = ⟨GateOp.not, [v_b.val]⟩)
    (hnotlit_a : (∃ x, F x ≠ x v_a) ∧ (∃ x, F x ≠ !x v_a))
    (hdep0 : ∃ x : Fin m → Bool,
      F (Function.update (Function.update x v_b false) v_a false) ≠
      F (Function.update (Function.update x v_b false) v_a true))
    (hdep1 : ∃ x : Fin m → Bool,
      F (Function.update (Function.update x v_b true) v_a false) ≠
      F (Function.update (Function.update x v_b true) v_a true)) : False := by
  have hnc : ∃ x x' : Fin m → Bool, F x ≠ F x' := by obtain ⟨x, hx⟩ := hdep0; exact ⟨_, _, hx⟩
  have hwa_lt : wa < m + k_star.val := by
    rcases minimal_gate_shape hmin hnc k_star.val k_star.isLt with ⟨hnot, _, _, _⟩ | ⟨_, a, b, ha, hb, _, hin⟩
    · rcases hk_star with h | h <;> rw [h] at hnot <;> rcases hop with rfl | rfl <;> cases hnot
    · rcases hk_star with h | h <;> rw [h] at hin <;> simp at hin <;> rcases hin with ⟨rfl, rfl⟩ <;> assumption
  have hwb_lt : wb < m + k_star.val := by
    rcases minimal_gate_shape hmin hnc k_star.val k_star.isLt with ⟨hnot, _, _, _⟩ | ⟨_, a, b, ha, hb, _, hin⟩
    · rcases hk_star with h | h <;> rw [h] at hnot <;> rcases hop with rfl | rfl <;> cases hnot
    · rcases hk_star with h | h <;> rw [h] at hin <;> simp at hin <;> rcases hin with ⟨rfl, rfl⟩ <;> assumption
  let ctrl : Bool := match op with | GateOp.and => false | _ => true
  have hctrl_val : ∃ c_b : Bool, ∀ x : Fin m → Bool,
      wireFn C wb (Function.update x v_b c_b) = ctrl := by
    rcases hwb with rfl | ⟨k_b, rfl, hkb⟩
    · refine ⟨ctrl, fun x => ?_⟩
      rw [wireFn_input]; simp
    · refine ⟨!ctrl, fun x => ?_⟩
      rw [wireFn_gate C k_b.val k_b.isLt, hkb]
      simp [GateOp.eval, show v_b.val < m + k_b.val by have := v_b.isLt; omega, wireFn_input]
  obtain ⟨c_b, hcb⟩ := hctrl_val
  have hdep_cb : ∃ x : Fin m → Bool,
      F (Function.update (Function.update x v_b c_b) v_a false) ≠
      F (Function.update (Function.update x v_b c_b) v_a true) := by
    cases c_b; exact hdep0; exact hdep1
  have hk_star_const : ∀ x : Fin m → Bool,
      wireFn C (m + k_star.val) (Function.update (Function.update x v_b c_b) v_a false) =
      wireFn C (m + k_star.val) (Function.update (Function.update x v_b c_b) v_a true) := by
    intro x
    have hwb0 : wireFn C wb (Function.update (Function.update x v_b c_b) v_a false) = ctrl := by
      rw [Function.update_comm hne.symm]; exact hcb _
    have hwb1 : wireFn C wb (Function.update (Function.update x v_b c_b) v_a true) = ctrl := by
      rw [Function.update_comm hne.symm]; exact hcb _
    rw [wireFn_gate C k_star.val k_star.isLt, wireFn_gate C k_star.val k_star.isLt]
    rcases hop with rfl | rfl <;> rcases hk_star with h | h <;> rw [h] <;>
      simp [GateOp.eval, hwa_lt, hwb_lt, hwb0, hwb1, ctrl]
  have hout_ne_va : C.output ≠ v_a.val := by
    intro heq
    obtain ⟨x, hx⟩ := hnotlit_a.1
    have h1 := hmin.2.1 x
    have h2 : C.eval (List.ofFn x) = x v_a := by
      show (wiresFrom C.gates (List.ofFn x)).getD C.output false = x v_a
      rw [heq]; exact wireFn_input C v_a x
    exact hx (h1.symm.trans h2)
  rcases hwa with ⟨rfl, huses⟩ | ⟨k_a, rfl, hka, huses_va, huses_ka⟩
  · apply fanout1_bin_dep_contradiction hmin v_a v_b c_b hdep_cb {v_a.val}
      (Set.mem_singleton _) (by simpa using hout_ne_va)
    intro j hj _
    by_cases hjk : j = k_star.val
    · subst hjk; exact Or.inr hk_star_const
    · left
      intro i hi hmem
      simp only [Set.mem_singleton_iff] at hmem
      subst hmem
      have h1 : (⟨j, hj⟩ : Fin C.gates.length) ∈ gateUses C v_a.val := mem_gateUses.2 hi
      rw [huses, Finset.mem_singleton] at h1
      exact hjk (congrArg Fin.val h1)
  · have hout_ne_ka : C.output ≠ m + k_a.val := by
      intro heq
      obtain ⟨x, hx⟩ := hnotlit_a.2
      have h1 := hmin.2.1 x
      have h2 : C.eval (List.ofFn x) = !x v_a := by
        show wireFn C C.output x = !x v_a
        rw [heq, wireFn_gate C k_a.val k_a.isLt, hka]
        simp [GateOp.eval, show v_a.val < m + k_a.val by have := v_a.isLt; omega, wireFn_input]
      exact hx (h1.symm.trans h2)
    apply fanout1_bin_dep_contradiction hmin v_a v_b c_b hdep_cb {v_a.val, m + k_a.val}
      (Set.mem_insert _ _) (by simp [hout_ne_va, hout_ne_ka])
    intro j hj hjnot
    by_cases hjk : j = k_star.val
    · subst hjk; exact Or.inr hk_star_const
    · left
      intro i hi hmem
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
      rcases hmem with rfl | rfl
      · have h1 : (⟨j, hj⟩ : Fin C.gates.length) ∈ gateUses C v_a.val := mem_gateUses.2 hi
        rw [huses_va, Finset.mem_singleton] at h1
        have hjeq : j = k_a.val := congrArg Fin.val h1
        exact hjnot (Or.inr (by subst hjeq; rfl))
      · have h1 : (⟨j, hj⟩ : Fin C.gates.length) ∈ gateUses C (m + k_a.val) := mem_gateUses.2 hi
        rw [huses_ka, Finset.mem_singleton] at h1
        exact hjk (congrArg Fin.val h1)

private def fG (x : Fin 10 → Bool) : Bool :=
  (x 0 && x 1) || (x 0 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) ||
  (x 5 && x 6) || (x 6 && x 7) || (x 7 && x 1) || (x 0 && x 8) || (x 1 && x 9)

private def fC8 (x : Fin 10 → Bool) : Bool :=
  (x 0 && x 1) || (x 0 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) ||
  (x 5 && x 6) || (x 6 && x 7) || (x 7 && x 1)

private def fH (x : Fin 10 → Bool) : Bool :=
  (x 0 && x 1) || (x 0 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) ||
  (x 5 && x 6) || (x 6 && x 7) || (x 7 && x 1) || (x 1 && x 9)

private def fP6 (x : Fin 10 → Bool) : Bool :=
  (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 7)

private lemma graphOrFun_mkGraph10_eq (es : List (Fin 10 × Fin 10)) (A : Finset (Fin 10))
    (x : Fin 10 → Bool) :
    graphOrFun (mkGraph10 es) A x =
      decide ((∃ a ∈ A, x a = true) ∨ es.any (fun e => decide (e.1 ≠ e.2) && x e.1 && x e.2) = true) := by
  classical
  simp only [graphOrFun, decide_eq_decide, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro (hA | ⟨u, v, ⟨huv, hmem⟩, hu, hv⟩)
    · exact Or.inl hA
    · rcases hmem with hmem | hmem
      · exact Or.inr ⟨(u, v), hmem, ⟨huv, hu⟩, hv⟩
      · exact Or.inr ⟨(v, u), hmem, ⟨huv.symm, hv⟩, hu⟩
  · rintro (hA | ⟨⟨u, v⟩, hmem, ⟨huv, hu⟩, hv⟩)
    · exact Or.inl hA
    · exact Or.inr ⟨u, v, ⟨huv, Or.inl hmem⟩, hu, hv⟩

private def fin10Fun (v : List ℕ) (i : Fin 10) : ℕ := v.getD i.val 0
private def fin10Fin (v : List (Fin 10)) (i : Fin 10) : Fin 10 := v.getD i.val 0

private lemma C8_x0_0_lower {s : ℕ} (h : HasCircuitSize 10 (fun x => fC8 (Function.update x 0 false)) s) : 8 ≤ s := by
  have heq : (fun x => fC8 (Function.update x 0 false)) =
      graphOrFun (mkGraph10 [(1,7),(2,3),(3,4),(4,5),(5,6),(6,7)]) ∅ := by
    ext x
    rw [graphOrFun_mkGraph10_eq]
    simp [fC8, Function.update]
    grind
  rw [heq] at h
  exact concrete_forest_lower [(1,7),(2,3),(3,4),(4,5),(5,6),(6,7)] ∅
    (fin10Fin [0,7,2,2,3,4,5,6,8,9]) (fin10Fun [0,6,0,1,2,3,4,5,0,0])
    {3,5,7} [(2,3),(4,5),(6,7)] 8
    (by decide) (by decide)
    (by unfold HasExactParentOrder mkGraph10; decide)
    (by unfold mkGraph10; decide)
    (by unfold mkGraph10; decide)
    (by unfold IsVC mkGraph10; decide)
    (by unfold mkGraph10; decide)
    (by decide) (by decide) (by decide) h

private lemma C8_x0_1_lower {s : ℕ} (h : HasCircuitSize 10 (fun x => fC8 (Function.update x 0 true)) s) : 7 ≤ s := by
  have heq : (fun x => fC8 (Function.update x 0 true)) =
      graphOrFun (mkGraph10 [(3,4),(4,5),(5,6),(6,7)]) {1, 2} := by
    ext x
    rw [graphOrFun_mkGraph10_eq]
    simp [fC8, Function.update]
    grind
  rw [heq] at h
  exact concrete_forest_lower [(3,4),(4,5),(5,6),(6,7)] {1, 2}
    (fin10Fin [0,1,2,3,3,4,5,6,8,9]) (fin10Fun [0,0,0,0,1,2,3,4,0,0])
    {4,6} [(3,4),(5,6)] 7
    (by decide) (by decide)
    (by unfold HasExactParentOrder mkGraph10; decide)
    (by unfold mkGraph10; decide)
    (by unfold mkGraph10; decide)
    (by unfold IsVC mkGraph10; decide)
    (by unfold mkGraph10; decide)
    (by decide) (by decide) (by decide) h

private def c8RotFun (i : Fin 10) : Fin 10 :=
  fin10Fin [2, 0, 3, 4, 5, 6, 7, 1, 8, 9] i

private def c8RotInvFun (i : Fin 10) : Fin 10 :=
  fin10Fin [1, 7, 0, 2, 3, 4, 5, 6, 8, 9] i

private def c8Rot : Fin 10 ≃ Fin 10 where
  toFun := c8RotFun
  invFun := c8RotInvFun
  left_inv := by decide
  right_inv := by decide

private lemma fC8_rot (x : Fin 10 → Bool) : fC8 (fun i => x (c8Rot i)) = fC8 x := by
  have h0 : c8Rot 0 = 2 := by decide
  have h1 : c8Rot 1 = 0 := by decide
  have h2 : c8Rot 2 = 3 := by decide
  have h3 : c8Rot 3 = 4 := by decide
  have h4 : c8Rot 4 = 5 := by decide
  have h5 : c8Rot 5 = 6 := by decide
  have h6 : c8Rot 6 = 7 := by decide
  have h7 : c8Rot 7 = 1 := by decide
  simp only [fC8, h0, h1, h2, h3, h4, h5, h6, h7]
  grind

private lemma C8_var_equiv (v : Fin 10) (hv : v.val < 8) :
    ∃ e : Fin 10 ≃ Fin 10, e 0 = v ∧ ∀ x : Fin 10 → Bool, fC8 (fun i => x (e i)) = fC8 x := by
  have hiter : ∀ k : ℕ, ∃ e : Fin 10 ≃ Fin 10,
      e 0 = (c8RotFun^[k]) 0 ∧ ∀ x : Fin 10 → Bool, fC8 (fun i => x (e i)) = fC8 x := by
    intro k
    induction k with
    | zero => exact ⟨Equiv.refl _, rfl, fun _ => rfl⟩
    | succ k ih =>
      obtain ⟨e, he0, hef⟩ := ih
      refine ⟨e.trans c8Rot, ?_, fun x => ?_⟩
      · simp only [Equiv.trans_apply, Function.iterate_succ_apply']
        rw [he0]; rfl
      · exact (hef (fun j => x (c8Rot j))).trans (fC8_rot x)
  have hreach : ∃ k < 8, (c8RotFun^[k]) 0 = v := by
    fin_cases v
    · exact ⟨0, by omega, by decide⟩
    · exact ⟨7, by omega, by decide⟩
    · exact ⟨1, by omega, by decide⟩
    · exact ⟨2, by omega, by decide⟩
    · exact ⟨3, by omega, by decide⟩
    · exact ⟨4, by omega, by decide⟩
    · exact ⟨5, by omega, by decide⟩
    · exact ⟨6, by omega, by decide⟩
    · simp at hv
    · simp at hv
  obtain ⟨k, _, hk⟩ := hreach
  obtain ⟨e, he0, hef⟩ := hiter k
  exact ⟨e, he0.trans hk, hef⟩

private lemma C8_update_lower (v : Fin 10) (hv : v.val < 8) (b : Bool) {s : ℕ}
    (h : HasCircuitSize 10 (fun x => fC8 (Function.update x v b)) s) :
    (if b then 7 else 8) ≤ s := by
  obtain ⟨e, he0, hef⟩ := C8_var_equiv v hv
  have hcomp := hasCircuitSize_comp_equiv e.symm h
  have hrew : (fun x => fC8 (Function.update (fun i => x (e.symm i)) v b)) =
      (fun x => fC8 (Function.update x 0 b)) := by
    ext x
    have hef_symm : ∀ y : Fin 10 → Bool, fC8 (fun i => y (e.symm i)) = fC8 y := by
      intro y
      have := hef (fun i => y (e.symm i))
      simpa using this.symm
    rw [← hef_symm (Function.update x 0 b)]
    congr 1
    ext i
    by_cases hi : i = v
    · subst hi
      rw [Function.update_self, ← he0, e.symm_apply_apply, Function.update_self]
    · have hne0 : e.symm i ≠ 0 := fun h0 => hi (by rw [← he0, ← h0, e.apply_symm_apply])
      rw [Function.update_of_ne hi, Function.update_of_ne hne0]
  rw [hrew] at hcomp
  cases b
  · exact C8_x0_0_lower hcomp
  · exact C8_x0_1_lower hcomp

private lemma fC8_indep_ge8 (v : Fin 10) (hv : 8 ≤ v.val) (x : Fin 10 → Bool) (b : Bool) :
    fC8 (Function.update x v b) = fC8 x := by
  have hne : ∀ i : Fin 10, i.val < 8 → i ≠ v := fun i hi h => by subst h; omega
  simp only [fC8, Function.update_of_ne (hne 0 (by decide)),
    Function.update_of_ne (hne 1 (by decide)),
    Function.update_of_ne (hne 2 (by decide)),
    Function.update_of_ne (hne 3 (by decide)),
    Function.update_of_ne (hne 4 (by decide)),
    Function.update_of_ne (hne 5 (by decide)),
    Function.update_of_ne (hne 6 (by decide)),
    Function.update_of_ne (hne 7 (by decide))]

private lemma fC8_dep_pair (u v : Fin 10) (hu : u.val < 8) (hv : v.val < 8) (hne : u ≠ v) (c : Bool) :
    ∃ x : Fin 10 → Bool,
      fC8 (Function.update (Function.update x v c) u false) ≠
      fC8 (Function.update (Function.update x v c) u true) := by
  have hall : ∀ a b : Fin 10, a.val < 8 → b.val < 8 → a ≠ b → ∀ cb : Bool,
      ∃ w : Fin 10,
        fC8 (Function.update (Function.update (fun i => decide (i = w)) b cb) a false) ≠
        fC8 (Function.update (Function.update (fun i => decide (i = w)) b cb) a true) := by
    decide
  obtain ⟨w, hw⟩ := hall u v hu hv hne c
  exact ⟨fun i => decide (i = w), hw⟩

private lemma C8_lower {s : ℕ} (hC : HasCircuitSize 10 fC8 s) : 11 ≤ s := by
  by_contra hlt
  have hs10 : s ≤ 10 := by omega
  obtain ⟨C, hmin, hlen⟩ := exists_minimal_circuit hC
  have hC10 : C.gates.length ≤ 10 := by omega
  have hnc : ∃ x x' : Fin 10 → Bool, fC8 x ≠ fC8 x' :=
    ⟨fun _ => false, fun _ => true, by decide⟩
  have hnotlit : ∀ i : Fin 10, (∃ x, fC8 x ≠ x i) ∧ (∃ x, fC8 x ≠ !x i) := by
    intro i
    constructor
    · refine ⟨fun j => decide (j = i), ?_⟩
      fin_cases i <;> decide
    · refine ⟨fun _ => false, ?_⟩
      fin_cases i <;> decide
  have hno_ge8 : ∀ (v : Fin 10), 8 ≤ v.val → gateUses C v.val = ∅ := by
    intro v hv
    by_contra hne
    obtain ⟨k, hk⟩ := Finset.nonempty_iff_ne_empty.2 hne
    rw [mem_gateUses] at hk
    have hst₀ : (initAssign 10 (singleAssign v false)).length = 10 := by simp [initAssign]
    have hfv : finalSt 10 C.gates (initAssign 10 (singleAssign v false)) v.val = Sum.inl false := by
      rw [finalSt_init 10 C.gates _ v.val (by rw [hst₀]; exact v.isLt), initAssign, ofFn_getD_lt _ _ v.val v.isLt]
      simp [singleAssign]
    have hek := elim_const_input hmin hnc _ hst₀ k v.val hk ⟨false, hfv⟩
    have hrew : (fun x => fC8 (applyAssign (singleAssign v false) x)) = fC8 := by
      ext x; rw [applyAssign_single, fC8_indep_ge8 v hv]
    have hnc' : ∃ x x', fC8 (applyAssign (singleAssign v false) x) ≠ fC8 (applyAssign (singleAssign v false) x') := by
      obtain ⟨x, x', hx⟩ := hnc
      exact ⟨x, x', by rw [congrFun hrew x, congrFun hrew x']; exact hx⟩
    obtain ⟨h1, hcs⟩ := elim_size_of_card hmin (singleAssign v false) hnc' {k} (by simpa using hek)
    rw [hrew] at hcs
    rw [Finset.card_singleton] at h1 hcs
    exact hmin.2.2 (C.gates.length - 1) (by omega) hcs
  have hnc_upd (v : Fin 10) (hv : v.val < 8) (b : Bool) :
      ∃ x x' : Fin 10 → Bool, fC8 (Function.update x v b) ≠ fC8 (Function.update x' v b) := by
    have hv2 : ∃ u : Fin 10, u.val < 8 ∧ u ≠ v := by
      by_cases h0 : v = 0
      · exact ⟨1, by decide, by rw [h0]; decide⟩
      · exact ⟨0, by decide, Ne.symm h0⟩
    obtain ⟨u, hu, huv⟩ := hv2
    obtain ⟨x, hx⟩ := fC8_dep_pair u v hu hv huv b
    exact ⟨Function.update x u false, Function.update x u true, by
      rw [Function.update_comm huv, Function.update_comm huv]; exact hx⟩
  obtain ⟨k_star, hbin, hprev⟩ := first_non_not_gate hmin hnc hnotlit
  rcases minimal_gate_shape hmin hnc k_star.val k_star.isLt with
    ⟨hnot, _, _, _⟩ | ⟨hop, wa, wb, hwa_lt, hwb_lt, hwne, hin⟩
  · rcases hbin with h | h <;> rw [hnot] at h <;> cases h
  · have hlit_of_mem : ∀ w : ℕ, w < 10 + k_star.val → w ∈ C.gates[k_star.val].inputs →
        (∃ v : Fin 10, v.val < 8 ∧ w = v.val) ∨
        (∃ v : Fin 10, ∃ k_n : Fin C.gates.length, v.val < 8 ∧ w = 10 + k_n.val ∧
          C.gates[k_n.val] = ⟨GateOp.not, [v.val]⟩) := by
      intro w hw hmem
      by_cases hwm : w < 10
      · left
        have hvlt : (⟨w, hwm⟩ : Fin 10).val < 8 := by
          by_contra hge
          have hem := hno_ge8 ⟨w, hwm⟩ (by omega)
          have hk : k_star ∈ gateUses C w := mem_gateUses.2 hmem
          rw [hem] at hk; simp at hk
        exact ⟨⟨w, hwm⟩, hvlt, rfl⟩
      · right
        have hklt : w - 10 < k_star.val := by omega
        have hklen : w - 10 < C.gates.length := by omega
        obtain ⟨v, hgv⟩ := hprev ⟨w - 10, hklen⟩ hklt
        have hvlt : v.val < 8 := by
          by_contra hge
          have hem := hno_ge8 v (by omega)
          have hk : (⟨w - 10, hklen⟩ : Fin C.gates.length) ∈ gateUses C v.val := by
            rw [mem_gateUses, hgv]; simp
          rw [hem] at hk; simp at hk
        exact ⟨v, ⟨w - 10, hklen⟩, hvlt, by show w = 10 + (w - 10); omega, hgv⟩
    have hfa_lit := hlit_of_mem wa hwa_lt (by rw [hin]; simp)
    have hfb_lit := hlit_of_mem wb hwb_lt (by rw [hin]; simp)
    have hv_fanout1 : ∀ v : Fin 10, v.val < 8 →
        ∃ k₀ : Fin C.gates.length, gateUses C v.val = {k₀} := by
      intro v hv
      have hdep_v : ∃ x, fC8 (Function.update x v false) ≠ fC8 (Function.update x v true) := by
        have hv2 : ∃ u : Fin 10, u.val < 8 ∧ u ≠ v := by
          by_cases h0 : v = 0
          · exact ⟨1, by decide, by rw [h0]; decide⟩
          · exact ⟨0, by decide, Ne.symm h0⟩
        obtain ⟨u, hu, huv⟩ := hv2
        obtain ⟨x, hx⟩ := fC8_dep_pair v u hv hu huv.symm false
        exact ⟨Function.update x u false, hx⟩
      exact var_fanout_one_of_bounds hmin v hdep_v (hnc_upd v hv false) (hnc_upd v hv true)
        (fun s hs => by simpa using C8_update_lower v hv false hs)
        (fun s hs => by simpa using C8_update_lower v hv true hs)
        (by omega) (by omega)
    have hwa_full : ∃ v_a : Fin 10, v_a.val < 8 ∧
        ((wa = v_a.val ∧ gateUses C v_a.val = {k_star}) ∨
          ∃ k_a : Fin C.gates.length, wa = 10 + k_a.val ∧
            C.gates[k_a.val] = ⟨GateOp.not, [v_a.val]⟩ ∧
            gateUses C v_a.val = {k_a} ∧ gateUses C (10 + k_a.val) = {k_star}) := by
      rcases hfa_lit with ⟨v_a, hva, rfl⟩ | ⟨v_a, k_a, hva, rfl, hka⟩
      · obtain ⟨k₀, hk₀⟩ := hv_fanout1 v_a hva
        have hmem : k_star ∈ gateUses C v_a.val := by rw [mem_gateUses, hin]; simp
        rw [hk₀, Finset.mem_singleton] at hmem
        subst hmem
        exact ⟨v_a, hva, Or.inl ⟨rfl, hk₀⟩⟩
      · obtain ⟨hv_u, k₁, hk₁_u, _⟩ := not_gate_structure hmin hnc v_a (hnc_upd v_a hva false)
          (fun s hs => by simpa using C8_update_lower v_a hva false hs) (by omega) k_a hka
        have hmem : k_star ∈ gateUses C (10 + k_a.val) := by rw [mem_gateUses, hin]; simp
        rw [hk₁_u, Finset.mem_singleton] at hmem
        subst hmem
        exact ⟨v_a, hva, Or.inr ⟨k_a, rfl, hka, hv_u, hk₁_u⟩⟩
    obtain ⟨v_a, hva, hwa_spec⟩ := hwa_full
    obtain ⟨v_b, hvb, hwb_spec⟩ : ∃ v_b : Fin 10, v_b.val < 8 ∧
        (wb = v_b.val ∨ ∃ k_b : Fin C.gates.length, wb = 10 + k_b.val ∧
          C.gates[k_b.val] = ⟨GateOp.not, [v_b.val]⟩) := by
      rcases hfb_lit with ⟨v_b, hvb, rfl⟩ | ⟨v_b, k_b, hvb, rfl, hkb⟩
      · exact ⟨v_b, hvb, Or.inl rfl⟩
      · exact ⟨v_b, hvb, Or.inr ⟨k_b, rfl, hkb⟩⟩
    have hvne : v_a ≠ v_b := by
      intro heq; subst heq
      rcases hwa_spec with ⟨rfl, huses⟩ | ⟨k_a, rfl, hka, huses_va, _⟩
      · rcases hwb_spec with rfl | ⟨k_b, rfl, hkb⟩
        · exact hwne rfl
        · exact minimal_no_not_and_same_var hmin hnc k_b k_star v_a.val
            (by have := v_a.isLt; omega) hkb (by rw [hin]; simp) (by rw [hin]; simp)
      · rcases hwb_spec with rfl | ⟨k_b, rfl, hkb⟩
        · exact minimal_no_not_and_same_var hmin hnc k_a k_star v_a.val
            (by have := v_a.isLt; omega) hka (by rw [hin]; simp) (by rw [hin]; simp)
        · have hmem : k_b ∈ gateUses C v_a.val := by rw [mem_gateUses, hkb]; simp
          rw [huses_va, Finset.mem_singleton] at hmem
          subst hmem
          exact hwne rfl
    have hk_eq : C.gates[k_star.val] = ⟨C.gates[k_star.val].op, [wa, wb]⟩ := by
      cases h : C.gates[k_star.val]; simp_all
    exact bin_gate_kills_dep hmin v_a v_b hvne C.gates[k_star.val].op hop k_star wa wb
      (Or.inl hk_eq) hwa_spec hwb_spec (hnotlit v_a)
      (fC8_dep_pair v_a v_b hva hvb hvne false)
      (fC8_dep_pair v_a v_b hva hvb hvne true)

private lemma H_lower {s : ℕ} (h : HasCircuitSize 10 fH s) : 12 ≤ s := by
  have hdep : ∃ x : Fin 10 → Bool,
      fH (Function.update x 9 false) ≠ fH (Function.update x 9 true) :=
    ⟨fun i => decide (i = 1), by decide⟩
  have hrew : (fun x => fH (Function.update x 9 false)) = fC8 := by
    ext x
    simp only [fH, fC8, Function.update]
    grind
  have hnc : ∃ x x' : Fin 10 → Bool,
      fH (Function.update x 9 false) ≠ fH (Function.update x' 9 false) :=
    ⟨fun _ => false, fun _ => true, by decide⟩
  obtain ⟨hs1, hC'⟩ := elim_one_var 9 false h hdep hnc
  rw [hrew] at hC'
  have h11 := C8_lower hC'
  omega

private def gSymFun (i : Fin 10) : Fin 10 :=
  fin10Fin [1, 0, 7, 6, 5, 4, 3, 2, 9, 8] i

private def gSym : Fin 10 ≃ Fin 10 where
  toFun := gSymFun
  invFun := gSymFun
  left_inv := by decide
  right_inv := by decide

private lemma fG_sym (x : Fin 10 → Bool) : fG (fun i => x (gSym i)) = fG x := by
  have h0 : gSym 0 = 1 := by decide
  have h1 : gSym 1 = 0 := by decide
  have h2 : gSym 2 = 7 := by decide
  have h3 : gSym 3 = 6 := by decide
  have h4 : gSym 4 = 5 := by decide
  have h5 : gSym 5 = 4 := by decide
  have h6 : gSym 6 = 3 := by decide
  have h7 : gSym 7 = 2 := by decide
  have h8 : gSym 8 = 9 := by decide
  have h9 : gSym 9 = 8 := by decide
  simp only [fG, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
  grind

private lemma fP6_sym (x : Fin 10 → Bool) : fP6 (fun i => x (gSym i)) = fP6 x := by
  have h2 : gSym 2 = 7 := by decide
  have h3 : gSym 3 = 6 := by decide
  have h4 : gSym 4 = 5 := by decide
  have h5 : gSym 5 = 4 := by decide
  have h6 : gSym 6 = 3 := by decide
  have h7 : gSym 7 = 2 := by decide
  simp only [fP6, h2, h3, h4, h5, h6, h7]
  grind

private lemma hasCircuitSize_sym_update {f : (Fin 10 → Bool) → Bool}
    (hsym : ∀ x, f (fun i => x (gSym i)) = f x)
    (v : Fin 10) (b : Bool) {s : ℕ}
    (h : HasCircuitSize 10 (fun x => f (Function.update x v b)) s) :
    HasCircuitSize 10 (fun x => f (Function.update x (gSym v) b)) s := by
  have hcomp := hasCircuitSize_comp_equiv gSym h
  have hrew : (fun x => f (Function.update (fun i => x (gSym i)) v b)) =
      (fun x => f (Function.update x (gSym v) b)) := by
    ext x
    rw [← hsym (Function.update x (gSym v) b)]
    congr 1; ext i
    by_cases hi : i = v
    · subst hi; simp
    · have hne : gSym i ≠ gSym v := fun h => hi (gSym.injective h)
      rw [Function.update_of_ne hi, Function.update_of_ne hne]
  rw [← hrew]; exact hcomp

private lemma G_x8_0_lower {s : ℕ} (h : HasCircuitSize 10 (fun x => fG (Function.update x 8 false)) s) : 12 ≤ s := by
  have heq : (fun x => fG (Function.update x 8 false)) = fH := by
    ext x; simp [fG, fH, Function.update]
  rw [heq] at h; exact H_lower h

private lemma G_x9_0_lower {s : ℕ} (h : HasCircuitSize 10 (fun x => fG (Function.update x 9 false)) s) : 12 ≤ s := by
  have h8 : gSym 9 = 8 := by decide
  exact G_x8_0_lower (h8 ▸ hasCircuitSize_sym_update fG_sym 9 false h)

private lemma G_x8_1_lower {s : ℕ} (h : HasCircuitSize 10 (fun x => fG (Function.update x 8 true)) s) : 11 ≤ s := by
  have heq : (fun x => fG (Function.update x 8 true)) =
      graphOrFun (mkGraph10 [(1,7),(1,9),(2,3),(3,4),(4,5),(5,6),(6,7)]) {0} := by
    ext x; rw [graphOrFun_mkGraph10_eq]; simp [fG, Function.update]; grind
  rw [heq] at h
  exact concrete_forest_lower [(1,7),(1,9),(2,3),(3,4),(4,5),(5,6),(6,7)] {0}
    (fin10Fin [0,7,2,2,3,4,5,6,8,1]) (fin10Fun [0,6,0,1,2,3,4,5,0,7])
    {3,5,7,1} [(2,3),(4,5),(6,7),(1,9)] 11
    (by decide) (by decide)
    (by unfold HasExactParentOrder mkGraph10; decide)
    (by unfold mkGraph10; decide)
    (by unfold mkGraph10; decide)
    (by unfold IsVC mkGraph10; decide)
    (by unfold mkGraph10; decide)
    (by decide) (by decide) (by decide) h

private lemma G_x9_1_lower {s : ℕ} (h : HasCircuitSize 10 (fun x => fG (Function.update x 9 true)) s) : 11 ≤ s := by
  have h8 : gSym 9 = 8 := by decide
  exact G_x8_1_lower (h8 ▸ hasCircuitSize_sym_update fG_sym 9 true h)

private lemma G_x3_0_lower {s : ℕ} (h : HasCircuitSize 10 (fun x => fG (Function.update x 3 false)) s) : 11 ≤ s := by
  have heq : (fun x => fG (Function.update x 3 false)) =
      graphOrFun (mkGraph10 [(0,1),(0,2),(0,8),(1,7),(1,9),(4,5),(5,6),(6,7)]) ∅ := by
    ext x; rw [graphOrFun_mkGraph10_eq]; simp [fG, Function.update]; grind
  rw [heq] at h
  exact concrete_forest_lower [(0,1),(0,2),(0,8),(1,7),(1,9),(4,5),(5,6),(6,7)] ∅
    (fin10Fin [0,0,0,3,5,6,7,1,0,1]) (fin10Fun [0,1,1,0,5,4,3,2,1,2])
    {0,1,6,4} [(0,8),(1,9),(6,7),(4,5)] 11
    (by decide) (by decide)
    (by unfold HasExactParentOrder mkGraph10; decide)
    (by unfold mkGraph10; decide)
    (by unfold mkGraph10; decide)
    (by unfold IsVC mkGraph10; decide)
    (by unfold mkGraph10; decide)
    (by decide) (by decide) (by decide) h

private lemma G_x3_1_lower {s : ℕ} (h : HasCircuitSize 10 (fun x => fG (Function.update x 3 true)) s) : 10 ≤ s := by
  have heq : (fun x => fG (Function.update x 3 true)) =
      graphOrFun (mkGraph10 [(0,1),(0,8),(1,7),(1,9),(5,6),(6,7)]) {2, 4} := by
    ext x; rw [graphOrFun_mkGraph10_eq]; simp [fG, Function.update]; grind
  rw [heq] at h
  exact concrete_forest_lower [(0,1),(0,8),(1,7),(1,9),(5,6),(6,7)] {2, 4}
    (fin10Fin [0,0,2,3,4,6,7,1,0,1]) (fin10Fun [0,1,0,0,0,4,3,2,1,2])
    {0,1,6} [(0,8),(1,9),(5,6)] 10
    (by decide) (by decide)
    (by unfold HasExactParentOrder mkGraph10; decide)
    (by unfold mkGraph10; decide)
    (by unfold mkGraph10; decide)
    (by unfold IsVC mkGraph10; decide)
    (by unfold mkGraph10; decide)
    (by decide) (by decide) (by decide) h

private lemma G_x4_0_lower {s : ℕ} (h : HasCircuitSize 10 (fun x => fG (Function.update x 4 false)) s) : 11 ≤ s := by
  have heq : (fun x => fG (Function.update x 4 false)) =
      graphOrFun (mkGraph10 [(0,1),(0,2),(0,8),(1,7),(1,9),(2,3),(5,6),(6,7)]) ∅ := by
    ext x; rw [graphOrFun_mkGraph10_eq]; simp [fG, Function.update]; grind
  rw [heq] at h
  exact concrete_forest_lower [(0,1),(0,2),(0,8),(1,7),(1,9),(2,3),(5,6),(6,7)] ∅
    (fin10Fin [0,0,0,2,4,6,7,1,0,1]) (fin10Fun [0,1,1,2,0,4,3,2,1,2])
    {2,0,1,6} [(2,3),(0,8),(1,9),(5,6)] 11
    (by decide) (by decide)
    (by unfold HasExactParentOrder mkGraph10; decide)
    (by unfold mkGraph10; decide)
    (by unfold mkGraph10; decide)
    (by unfold IsVC mkGraph10; decide)
    (by unfold mkGraph10; decide)
    (by decide) (by decide) (by decide) h

private lemma G_x4_1_lower {s : ℕ} (h : HasCircuitSize 10 (fun x => fG (Function.update x 4 true)) s) : 10 ≤ s := by
  have heq : (fun x => fG (Function.update x 4 true)) =
      graphOrFun (mkGraph10 [(0,1),(0,2),(0,8),(1,7),(1,9),(6,7)]) {3, 5} := by
    ext x; rw [graphOrFun_mkGraph10_eq]; simp [fG, Function.update]; grind
  rw [heq] at h
  exact concrete_forest_lower [(0,1),(0,2),(0,8),(1,7),(1,9),(6,7)] {3, 5}
    (fin10Fin [0,0,0,3,4,5,7,1,0,1]) (fin10Fun [0,1,1,0,0,0,3,2,1,2])
    {0,1,7} [(0,8),(1,9),(6,7)] 10
    (by decide) (by decide)
    (by unfold HasExactParentOrder mkGraph10; decide)
    (by unfold mkGraph10; decide)
    (by unfold mkGraph10; decide)
    (by unfold IsVC mkGraph10; decide)
    (by unfold mkGraph10; decide)
    (by decide) (by decide) (by decide) h

private lemma G_core_update_lower (v : Fin 10) (hv : v ∈ ({3, 4, 5, 6} : Finset (Fin 10))) (b : Bool) {s : ℕ}
    (h : HasCircuitSize 10 (fun x => fG (Function.update x v b)) s) :
    (if b then 10 else 11) ≤ s := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl | rfl
  · cases b; exact G_x3_0_lower h; exact G_x3_1_lower h
  · cases b; exact G_x4_0_lower h; exact G_x4_1_lower h
  · have h5 : gSym 5 = 4 := by decide
    have h' := h5 ▸ hasCircuitSize_sym_update fG_sym 5 b h
    cases b; exact G_x4_0_lower h'; exact G_x4_1_lower h'
  · have h6 : gSym 6 = 3 := by decide
    have h' := h6 ▸ hasCircuitSize_sym_update fG_sym 6 b h
    cases b; exact G_x3_0_lower h'; exact G_x3_1_lower h'

private def f11 (x : Fin 10 → Bool) : Bool := x 0 || x 1 || fP6 x
private def f01 (x : Fin 10 → Bool) : Bool := x 1 || fP6 x

private lemma f11_lower {s : ℕ} (h : HasCircuitSize 10 f11 s) : 9 ≤ s := by
  have heq : f11 = graphOrFun (mkGraph10 [(2,3),(3,4),(4,5),(5,6),(6,7)]) {0, 1} := by
    ext x; rw [graphOrFun_mkGraph10_eq]; simp [f11, fP6]; grind
  rw [heq] at h
  exact concrete_forest_lower [(2,3),(3,4),(4,5),(5,6),(6,7)] {0, 1}
    (fin10Fin [0,1,2,2,3,4,5,6,8,9]) (fin10Fun [0,0,0,1,2,3,4,5,0,0])
    {3,5,7} [(2,3),(4,5),(6,7)] 9
    (by decide) (by decide)
    (by unfold HasExactParentOrder mkGraph10; decide)
    (by unfold mkGraph10; decide)
    (by unfold mkGraph10; decide)
    (by unfold IsVC mkGraph10; decide)
    (by unfold mkGraph10; decide)
    (by decide) (by decide) (by decide) h

private lemma f01_lower {s : ℕ} (h : HasCircuitSize 10 f01 s) : 8 ≤ s := by
  have heq : f01 = graphOrFun (mkGraph10 [(2,3),(3,4),(4,5),(5,6),(6,7)]) {1} := by
    ext x; rw [graphOrFun_mkGraph10_eq]; simp [f01, fP6]; grind
  rw [heq] at h
  exact concrete_forest_lower [(2,3),(3,4),(4,5),(5,6),(6,7)] {1}
    (fin10Fin [0,1,2,2,3,4,5,6,8,9]) (fin10Fun [0,0,0,1,2,3,4,5,0,0])
    {3,5,7} [(2,3),(4,5),(6,7)] 8
    (by decide) (by decide)
    (by unfold HasExactParentOrder mkGraph10; decide)
    (by unfold mkGraph10; decide)
    (by unfold mkGraph10; decide)
    (by unfold IsVC mkGraph10; decide)
    (by unfold mkGraph10; decide)
    (by decide) (by decide) (by decide) h

private lemma fP6_lower {s : ℕ} (h : HasCircuitSize 10 fP6 s) : 7 ≤ s := by
  have heq : fP6 = graphOrFun (mkGraph10 [(2,3),(3,4),(4,5),(5,6),(6,7)]) ∅ := by
    ext x; rw [graphOrFun_mkGraph10_eq]; simp [fP6]; grind
  rw [heq] at h
  exact concrete_forest_lower [(2,3),(3,4),(4,5),(5,6),(6,7)] ∅
    (fin10Fin [0,1,2,2,3,4,5,6,8,9]) (fin10Fun [0,0,0,1,2,3,4,5,0,0])
    {3,5,7} [(2,3),(4,5),(6,7)] 7
    (by decide) (by decide)
    (by unfold HasExactParentOrder mkGraph10; decide)
    (by unfold mkGraph10; decide)
    (by unfold mkGraph10; decide)
    (by unfold IsVC mkGraph10; decide)
    (by unfold mkGraph10; decide)
    (by decide) (by decide) (by decide) h

private lemma P6_x2_0_lower {s : ℕ} (h : HasCircuitSize 10 (fun x => fP6 (Function.update x 2 false)) s) : 5 ≤ s := by
  have heq : (fun x => fP6 (Function.update x 2 false)) =
      graphOrFun (mkGraph10 [(3,4),(4,5),(5,6),(6,7)]) ∅ := by
    ext x; rw [graphOrFun_mkGraph10_eq]; simp [fP6, Function.update]; grind
  rw [heq] at h
  exact concrete_forest_lower [(3,4),(4,5),(5,6),(6,7)] ∅
    (fin10Fin [0,1,2,3,3,4,5,6,8,9]) (fin10Fun [0,0,0,0,1,2,3,4,0,0])
    {4,6} [(3,4),(5,6)] 5
    (by decide) (by decide)
    (by unfold HasExactParentOrder mkGraph10; decide)
    (by unfold mkGraph10; decide)
    (by unfold mkGraph10; decide)
    (by unfold IsVC mkGraph10; decide)
    (by unfold mkGraph10; decide)
    (by decide) (by decide) (by decide) h

private lemma P6_x2_1_lower {s : ℕ} (h : HasCircuitSize 10 (fun x => fP6 (Function.update x 2 true)) s) : 5 ≤ s := by
  have heq : (fun x => fP6 (Function.update x 2 true)) =
      graphOrFun (mkGraph10 [(4,5),(5,6),(6,7)]) {3} := by
    ext x; rw [graphOrFun_mkGraph10_eq]; simp [fP6, Function.update]; grind
  rw [heq] at h
  exact concrete_forest_lower [(4,5),(5,6),(6,7)] {3}
    (fin10Fin [0,1,2,3,4,4,5,6,8,9]) (fin10Fun [0,0,0,0,0,1,2,3,0,0])
    {5,7} [(4,5),(6,7)] 5
    (by decide) (by decide)
    (by unfold HasExactParentOrder mkGraph10; decide)
    (by unfold mkGraph10; decide)
    (by unfold mkGraph10; decide)
    (by unfold IsVC mkGraph10; decide)
    (by unfold mkGraph10; decide)
    (by decide) (by decide) (by decide) h

private lemma P6_end_lower (v : Fin 10) (hv : v = 2 ∨ v = 7) (b : Bool) {s : ℕ}
    (h : HasCircuitSize 10 (fun x => fP6 (Function.update x v b)) s) : 5 ≤ s := by
  rcases hv with rfl | rfl
  · cases b; exact P6_x2_0_lower h; exact P6_x2_1_lower h
  · have h7 : gSym 7 = 2 := by decide
    have h' := h7 ▸ hasCircuitSize_sym_update fP6_sym 7 b h
    cases b; exact P6_x2_0_lower h'; exact P6_x2_1_lower h'

private def GoodVar (C : Circuit) (v : Fin 10) : Prop :=
  (∀ k₁ k₂ : Fin C.gates.length, v.val ∈ C.gates[k₁.val].inputs → v.val ∈ C.gates[k₂.val].inputs → k₁ = k₂) ∧
  (∀ k₀ : Fin C.gates.length, C.gates[k₀.val] = ⟨GateOp.not, [v.val]⟩ →
    ∀ k₁ k₂ : Fin C.gates.length, 10 + k₀.val ∈ C.gates[k₁.val].inputs →
      10 + k₀.val ∈ C.gates[k₂.val].inputs → k₁ = k₂)

private lemma runAt_out_mono {m : ℕ} (gs : List Gate) (st₀ : List (Bool ⊕ ℕ))
    {k₁ k₂ : ℕ} (hle : k₁ ≤ k₂) (hk₂ : k₂ ≤ gs.length) :
    (runAt m gs st₀ k₁).2.length ≤ (runAt m gs st₀ k₂).2.length := by
  induction k₂ with
  | zero =>
    have h0 : k₁ = 0 := by omega
    subst h0; exact le_rfl
  | succ k ih =>
    by_cases h : k₁ ≤ k
    · have h1 := ih h (by omega)
      have h2 := runAt_out_step m gs st₀ ⟨k, by omega⟩
      dsimp only at h2
      omega
    · have h1 : k₁ = k + 1 := by omega
      subst h1; exact le_rfl

private lemma runAt_out_getElem_mono {m : ℕ} (gs : List Gate) (st₀ : List (Bool ⊕ ℕ))
    {k₁ k₂ : ℕ} (hle : k₁ ≤ k₂) (hk₂ : k₂ ≤ gs.length)
    (j : ℕ) (hj : j < (runAt m gs st₀ k₁).2.length) :
    (runAt m gs st₀ k₂).2[j]'(lt_of_lt_of_le hj (runAt_out_mono gs st₀ hle hk₂)) =
      (runAt m gs st₀ k₁).2[j]'hj := by
  induction k₂ with
  | zero =>
    have h0 : k₁ = 0 := by omega
    subst h0; rfl
  | succ k ih =>
    by_cases h : k₁ ≤ k
    · have hlt_k : j < (runAt m gs st₀ k).2.length :=
        lt_of_lt_of_le hj (runAt_out_mono gs st₀ h (by omega))
      have hstep : (runAt m gs st₀ (k + 1)).2 = (runAt m gs st₀ k).2 ∨
          ∃ g', (runAt m gs st₀ (k + 1)).2 = (runAt m gs st₀ k).2 ++ [g'] := by
        rw [runAt_succ m gs st₀ k (by omega)]
        unfold elimGate; dsimp only
        split
        · exact Or.inl rfl
        · exact Or.inr ⟨_, rfl⟩
      rcases hstep with heq | ⟨g', heq⟩
      · simp only [heq]
        exact ih h (by omega)
      · simp only [heq]
        rw [List.getElem_append_left hlt_k]
        exact ih h (by omega)
    · have h1 : k₁ = k + 1 := by omega
      subst h1; rfl

private lemma runAt_out_source {m : ℕ} {F : (Fin m → Bool) → Bool} {C : Circuit}
    (hmin : MinimalCircuit m F C)
    (hnc : ∃ x x' : Fin m → Bool, F x ≠ F x')
    (st₀ : List (Bool ⊕ ℕ)) (hst₀ : st₀.length = m) :
    ∀ n, n ≤ C.gates.length → ∀ (j : ℕ) (hj : j < (runAt m C.gates st₀ n).2.length),
      ∃ k : Fin C.gates.length, k.val < n ∧
        isElim m C.gates st₀ k = false ∧
        (runAt m C.gates st₀ k.val).2.length = j ∧
        ((runAt m C.gates st₀ n).2[j]'hj).op = C.gates[k.val].op ∧
        (∀ i' ∈ ((runAt m C.gates st₀ n).2[j]'hj).inputs,
          ∃ i ∈ C.gates[k.val].inputs, i < m + k.val ∧ finalSt m C.gates st₀ i = Sum.inr i') ∧
        (((runAt m C.gates st₀ n).2[j]'hj).op = GateOp.not →
          ∃ a a', C.gates[k.val] = ⟨GateOp.not, [a]⟩ ∧ a < m + k.val ∧
            finalSt m C.gates st₀ a = Sum.inr a' ∧
            (runAt m C.gates st₀ n).2[j]'hj = ⟨GateOp.not, [a']⟩) := by
  intro n
  induction n with
  | zero => intro _ j hj; simp [runAt_zero] at hj
  | succ n ih =>
    intro hn j hj
    have hnlt : n < C.gates.length := by omega
    by_cases hjold : j < (runAt m C.gates st₀ n).2.length
    · obtain ⟨k, hkn, hkeep, hlen, hop, hins, hnot⟩ := ih (by omega) j hjold
      have hsame := runAt_out_getElem_mono C.gates st₀ (Nat.le_succ n) hn j hjold
      refine ⟨k, by omega, hkeep, hlen, by rw [hsame]; exact hop,
        by rw [hsame]; exact hins, by rw [hsame]; exact hnot⟩
    · have hjeq : j = (runAt m C.gates st₀ n).2.length := by
        have hstep := runAt_out_step m C.gates st₀ ⟨n, hnlt⟩
        dsimp only at hstep
        cases he : isElim m C.gates st₀ ⟨n, hnlt⟩ <;> rw [he] at hstep <;> simp at hstep <;> omega
      rcases minimal_gate_shape hmin hnc n hnlt with
        ⟨hop, a, ha, hin⟩ | ⟨hop, a, b, ha, hb, _, hin⟩
      · have hg : C.gates[n] = ⟨GateOp.not, [a]⟩ := by cases h : C.gates[n]; simp_all
        have hs := runAt_step_not m C.gates st₀ hst₀ ⟨n, hnlt⟩ a ha hg
        cases hfa : finalSt m C.gates st₀ a with
        | inl c =>
          rw [hfa] at hs
          have hstep := runAt_out_step m C.gates st₀ ⟨n, hnlt⟩
          dsimp only at hstep; rw [hs.1] at hstep; simp at hstep; omega
        | inr ja =>
          rw [hfa] at hs
          have hget : (runAt m C.gates st₀ (n + 1)).2[j]'hj = ⟨GateOp.not, [ja]⟩ := by
            simp only [hs.2.2]
            rw [List.getElem_append_right (by omega)]
            simp [show j - (runAt m C.gates st₀ n).2.length = 0 by omega]
          refine ⟨⟨n, hnlt⟩, by show n < n + 1; omega, hs.1, hjeq.symm, by rw [hget, hg], ?_, ?_⟩
          · intro i' hi'; rw [hget] at hi'; simp at hi'; subst hi'
            exact ⟨a, by rw [hg]; simp, ha, hfa⟩
          · intro _; exact ⟨a, ja, hg, ha, hfa, hget⟩
      · rcases hop with hop | hop
        · have hg : C.gates[n] = ⟨GateOp.and, [a, b]⟩ := by cases h : C.gates[n]; simp_all
          have hs := runAt_step_and m C.gates st₀ hst₀ ⟨n, hnlt⟩ a b ha hb hg
          cases hfa : finalSt m C.gates st₀ a with
          | inl ca =>
            rw [hfa] at hs
            have hel : isElim m C.gates st₀ ⟨n, hnlt⟩ = true := by
              cases hfb : finalSt m C.gates st₀ b <;> rw [hfb] at hs <;> exact hs.1
            have hstep := runAt_out_step m C.gates st₀ ⟨n, hnlt⟩
            dsimp only at hstep; rw [hel] at hstep; simp at hstep; omega
          | inr ja =>
            rw [hfa] at hs
            cases hfb : finalSt m C.gates st₀ b with
            | inl cb =>
              rw [hfb] at hs
              have hstep := runAt_out_step m C.gates st₀ ⟨n, hnlt⟩
              dsimp only at hstep; rw [hs.1] at hstep; simp at hstep; omega
            | inr jb =>
              rw [hfb] at hs
              have hget : (runAt m C.gates st₀ (n + 1)).2[j]'hj = ⟨GateOp.and, [ja, jb]⟩ := by
                simp only [hs.2.2]
                rw [List.getElem_append_right (by omega)]
                simp [show j - (runAt m C.gates st₀ n).2.length = 0 by omega]
              refine ⟨⟨n, hnlt⟩, by show n < n + 1; omega, hs.1, hjeq.symm, by rw [hget, hg], ?_, ?_⟩
              · intro i' hi'; rw [hget] at hi'; simp at hi'
                rcases hi' with rfl | rfl
                · exact ⟨a, by rw [hg]; simp, ha, hfa⟩
                · exact ⟨b, by rw [hg]; simp, hb, hfb⟩
              · intro hnot; rw [hget] at hnot; cases hnot
        · have hg : C.gates[n] = ⟨GateOp.or, [a, b]⟩ := by cases h : C.gates[n]; simp_all
          have hs := runAt_step_or m C.gates st₀ hst₀ ⟨n, hnlt⟩ a b ha hb hg
          cases hfa : finalSt m C.gates st₀ a with
          | inl ca =>
            rw [hfa] at hs
            have hel : isElim m C.gates st₀ ⟨n, hnlt⟩ = true := by
              cases hfb : finalSt m C.gates st₀ b <;> rw [hfb] at hs <;> exact hs.1
            have hstep := runAt_out_step m C.gates st₀ ⟨n, hnlt⟩
            dsimp only at hstep; rw [hel] at hstep; simp at hstep; omega
          | inr ja =>
            rw [hfa] at hs
            cases hfb : finalSt m C.gates st₀ b with
            | inl cb =>
              rw [hfb] at hs
              have hstep := runAt_out_step m C.gates st₀ ⟨n, hnlt⟩
              dsimp only at hstep; rw [hs.1] at hstep; simp at hstep; omega
            | inr jb =>
              rw [hfb] at hs
              have hget : (runAt m C.gates st₀ (n + 1)).2[j]'hj = ⟨GateOp.or, [ja, jb]⟩ := by
                simp only [hs.2.2]
                rw [List.getElem_append_right (by omega)]
                simp [show j - (runAt m C.gates st₀ n).2.length = 0 by omega]
              refine ⟨⟨n, hnlt⟩, by show n < n + 1; omega, hs.1, hjeq.symm, by rw [hget, hg], ?_, ?_⟩
              · intro i' hi'; rw [hget] at hi'; simp at hi'
                rcases hi' with rfl | rfl
                · exact ⟨a, by rw [hg]; simp, ha, hfa⟩
                · exact ⟨b, by rw [hg]; simp, hb, hfb⟩
              · intro hnot; rw [hget] at hnot; cases hnot

private lemma finalSt_elim_inr_from_input {m : ℕ} {F : (Fin m → Bool) → Bool} {C : Circuit}
    (hmin : MinimalCircuit m F C)
    (hnc : ∃ x x' : Fin m → Bool, F x ≠ F x')
    (st₀ : List (Bool ⊕ ℕ)) (hst₀ : st₀.length = m)
    (k : Fin C.gates.length) (he : isElim m C.gates st₀ k = true)
    (w' : ℕ) (hf : finalSt m C.gates st₀ (m + k.val) = Sum.inr w') :
    ∃ i ∈ C.gates[k.val].inputs, i < m + k.val ∧ finalSt m C.gates st₀ i = Sum.inr w' := by
  rcases minimal_gate_shape hmin hnc k.val k.isLt with
    ⟨hop, a, ha, hin⟩ | ⟨hop, a, b, ha, hb, _, hin⟩
  · have hg : C.gates[k.val] = ⟨GateOp.not, [a]⟩ := by cases h : C.gates[k.val]; simp_all
    have hs := runAt_step_not m C.gates st₀ hst₀ k a ha hg
    cases hfa : finalSt m C.gates st₀ a with
    | inl c => rw [hfa] at hs; rw [hs.2] at hf; exact absurd hf Sum.inl_ne_inr
    | inr ja => rw [hfa] at hs; rw [hs.1] at he; cases he
  · rcases hop with hop | hop
    · have hg : C.gates[k.val] = ⟨GateOp.and, [a, b]⟩ := by cases h : C.gates[k.val]; simp_all
      have hs := runAt_step_and m C.gates st₀ hst₀ k a b ha hb hg
      cases hfa : finalSt m C.gates st₀ a with
      | inl ca =>
        rw [hfa] at hs
        cases hfb : finalSt m C.gates st₀ b with
        | inl cb => rw [hfb] at hs; rw [hs.2] at hf; exact absurd hf Sum.inl_ne_inr
        | inr jb =>
          rw [hfb] at hs; rw [hs.2] at hf
          cases ca
          · simp at hf
          · simp at hf; subst hf; exact ⟨b, by rw [hg]; simp, hb, hfb⟩
      | inr ja =>
        rw [hfa] at hs
        cases hfb : finalSt m C.gates st₀ b with
        | inl cb =>
          rw [hfb] at hs; rw [hs.2] at hf
          cases cb
          · simp at hf
          · simp at hf; subst hf; exact ⟨a, by rw [hg]; simp, ha, hfa⟩
        | inr jb => rw [hfb] at hs; rw [hs.1] at he; cases he
    · have hg : C.gates[k.val] = ⟨GateOp.or, [a, b]⟩ := by cases h : C.gates[k.val]; simp_all
      have hs := runAt_step_or m C.gates st₀ hst₀ k a b ha hb hg
      cases hfa : finalSt m C.gates st₀ a with
      | inl ca =>
        rw [hfa] at hs
        cases hfb : finalSt m C.gates st₀ b with
        | inl cb => rw [hfb] at hs; rw [hs.2] at hf; exact absurd hf Sum.inl_ne_inr
        | inr jb =>
          rw [hfb] at hs; rw [hs.2] at hf
          cases ca
          · simp at hf; subst hf; exact ⟨b, by rw [hg]; simp, hb, hfb⟩
          · simp at hf
      | inr ja =>
        rw [hfa] at hs
        cases hfb : finalSt m C.gates st₀ b with
        | inl cb =>
          rw [hfb] at hs; rw [hs.2] at hf
          cases cb
          · simp at hf; subst hf; exact ⟨a, by rw [hg]; simp, ha, hfa⟩
          · simp at hf
        | inr jb => rw [hfb] at hs; rw [hs.1] at he; cases he

private lemma finalSt_keep_val {m : ℕ} {F : (Fin m → Bool) → Bool} {C : Circuit}
    (hmin : MinimalCircuit m F C)
    (hnc : ∃ x x' : Fin m → Bool, F x ≠ F x')
    (st₀ : List (Bool ⊕ ℕ)) (hst₀ : st₀.length = m)
    (k : Fin C.gates.length) (hkeep : isElim m C.gates st₀ k = false) :
    finalSt m C.gates st₀ (m + k.val) = Sum.inr (m + (runAt m C.gates st₀ k.val).2.length) := by
  rcases minimal_gate_shape hmin hnc k.val k.isLt with
    ⟨hop, a, ha, hin⟩ | ⟨hop, a, b, ha, hb, _, hin⟩
  · have hg : C.gates[k.val] = ⟨GateOp.not, [a]⟩ := by cases h : C.gates[k.val]; simp_all
    have hs := runAt_step_not m C.gates st₀ hst₀ k a ha hg
    cases hfa : finalSt m C.gates st₀ a <;> rw [hfa] at hs
    · rw [hs.1] at hkeep; cases hkeep
    · exact hs.2.1
  · rcases hop with hop | hop
    · have hg : C.gates[k.val] = ⟨GateOp.and, [a, b]⟩ := by cases h : C.gates[k.val]; simp_all
      have hs := runAt_step_and m C.gates st₀ hst₀ k a b ha hb hg
      cases hfa : finalSt m C.gates st₀ a <;> rw [hfa] at hs <;>
        cases hfb : finalSt m C.gates st₀ b <;> rw [hfb] at hs
      · rw [hs.1] at hkeep; cases hkeep
      · rw [hs.1] at hkeep; cases hkeep
      · rw [hs.1] at hkeep; cases hkeep
      · exact hs.2.1
    · have hg : C.gates[k.val] = ⟨GateOp.or, [a, b]⟩ := by cases h : C.gates[k.val]; simp_all
      have hs := runAt_step_or m C.gates st₀ hst₀ k a b ha hb hg
      cases hfa : finalSt m C.gates st₀ a <;> rw [hfa] at hs <;>
        cases hfb : finalSt m C.gates st₀ b <;> rw [hfb] at hs
      · rw [hs.1] at hkeep; cases hkeep
      · rw [hs.1] at hkeep; cases hkeep
      · rw [hs.1] at hkeep; cases hkeep
      · exact hs.2.1

private lemma keep_len_inj {m : ℕ} (gs : List Gate) (st₀ : List (Bool ⊕ ℕ))
    (k₁ k₂ : Fin gs.length) (h1 : isElim m gs st₀ k₁ = false) (h2 : isElim m gs st₀ k₂ = false)
    (heq : (runAt m gs st₀ k₁.val).2.length = (runAt m gs st₀ k₂.val).2.length) : k₁ = k₂ := by
  apply Fin.ext
  rcases lt_trichotomy k₁.val k₂.val with hlt | he | hgt
  · have hs := runAt_out_step m gs st₀ k₁
    rw [h1] at hs; simp only [Bool.false_eq_true, ↓reduceIte] at hs
    have hm := runAt_out_mono (m := m) gs st₀ (Nat.succ_le_of_lt hlt) (Nat.le_of_lt k₂.isLt)
    rw [Nat.succ_eq_add_one] at hm
    omega
  · exact he
  · have hs := runAt_out_step m gs st₀ k₂
    rw [h2] at hs; simp only [Bool.false_eq_true, ↓reduceIte] at hs
    have hm := runAt_out_mono (m := m) gs st₀ (Nat.succ_le_of_lt hgt) (Nat.le_of_lt k₁.isLt)
    rw [Nat.succ_eq_add_one] at hm
    omega

private lemma elim_step_preserve_goodVar {F : (Fin 10 → Bool) → Bool} {C : Circuit}
    (hmin : MinimalCircuit 10 F C)
    (hnc : ∃ x x' : Fin 10 → Bool, F x ≠ F x')
    (a : Fin 10 → Option Bool) (outw : ℕ)
    (v : Fin 10)
    (hgood : GoodVar C v)
    (hno_v : ∀ k : Fin C.gates.length, isElim 10 C.gates (initAssign 10 a) k = true →
      v.val ∉ C.gates[k.val].inputs)
    (hno_not : ∀ k₀ : Fin C.gates.length, C.gates[k₀.val] = ⟨GateOp.not, [v.val]⟩ →
      ∀ k : Fin C.gates.length, isElim 10 C.gates (initAssign 10 a) k = true →
        10 + k₀.val ∉ C.gates[k.val].inputs) :
    GoodVar ⟨(runAt 10 C.gates (initAssign 10 a) C.gates.length).2, outw⟩ v := by
  let st₀ := initAssign 10 a
  have hst₀ : st₀.length = 10 := by simp [st₀, initAssign]
  have hclean_v : ∀ u, u < 10 + C.gates.length →
      finalSt 10 C.gates st₀ u = Sum.inr v.val → u = v.val := by
    intro u
    induction u using Nat.strong_induction_on with
    | ind u ih =>
      intro hu hf
      by_cases hum : u < 10
      · rw [finalSt_init 10 C.gates st₀ u (by omega)] at hf
        simp only [st₀, initAssign, ofFn_getD_lt _ _ u hum] at hf
        cases ha : a ⟨u, hum⟩ with
        | some b => rw [ha] at hf; exact absurd hf Sum.inl_ne_inr
        | none => rw [ha] at hf; exact Sum.inr.inj hf
      · have hklt : u - 10 < C.gates.length := by omega
        have hueq : u = 10 + (u - 10) := by omega
        cases he : isElim 10 C.gates st₀ ⟨u - 10, hklt⟩ with
        | false =>
          have hkv := finalSt_keep_val hmin hnc st₀ hst₀ ⟨u - 10, hklt⟩ he
          rw [← hueq] at hkv
          rw [hkv] at hf
          have := Sum.inr.inj hf
          have := v.isLt; omega
        | true =>
          rw [hueq] at hf
          obtain ⟨i, hi, hilt, hfi⟩ := finalSt_elim_inr_from_input hmin hnc st₀ hst₀ ⟨u - 10, hklt⟩ he v.val hf
          have hilt' : i < u := by dsimp only at hilt; omega
          have hieq := ih i hilt' (by omega) hfi
          subst hieq
          exact absurd hi (hno_v ⟨u - 10, hklt⟩ he)
  constructor
  · intro j₁ j₂ h1 h2
    obtain ⟨k₁, _, hkeep1, hlen1, _, hins1, _⟩ :=
      runAt_out_source hmin hnc st₀ hst₀ C.gates.length le_rfl j₁.val j₁.isLt
    obtain ⟨k₂, _, hkeep2, hlen2, _, hins2, _⟩ :=
      runAt_out_source hmin hnc st₀ hst₀ C.gates.length le_rfl j₂.val j₂.isLt
    obtain ⟨i₁, hi₁, hilt1, hfi1⟩ := hins1 v.val h1
    obtain ⟨i₂, hi₂, hilt2, hfi2⟩ := hins2 v.val h2
    have he1 := hclean_v i₁ (by omega) hfi1
    have he2 := hclean_v i₂ (by omega) hfi2
    subst he1; subst he2
    have hk_eq := hgood.1 k₁ k₂ hi₁ hi₂
    subst hk_eq
    exact Fin.ext (hlen1.symm.trans hlen2)
  · intro j₀ hj₀ j₁ j₂ h1 h2
    obtain ⟨k₀, _, hkeep0, hlen0, hop0, _, hnot0⟩ :=
      runAt_out_source hmin hnc st₀ hst₀ C.gates.length le_rfl j₀.val j₀.isLt
    obtain ⟨a₀, a₀', hgk₀, ha₀lt, hfa₀, hj₀eq⟩ := hnot0 (by rw [hj₀])
    have ha₀' : a₀' = v.val := by rw [hj₀] at hj₀eq; simpa using hj₀eq.symm
    subst ha₀'
    have ha₀_eq := hclean_v a₀ (by omega) hfa₀
    subst ha₀_eq
    have hclean_k₀ : ∀ u, u < 10 + C.gates.length →
        finalSt 10 C.gates st₀ u = Sum.inr (10 + j₀.val) → u = 10 + k₀.val := by
      intro u
      induction u using Nat.strong_induction_on with
      | ind u ih =>
        intro hu hf
        by_cases hum : u < 10
        · rw [finalSt_init 10 C.gates st₀ u (by omega)] at hf
          simp only [st₀, initAssign, ofFn_getD_lt _ _ u hum] at hf
          cases ha : a ⟨u, hum⟩ with
          | some b => rw [ha] at hf; exact absurd hf Sum.inl_ne_inr
          | none =>
            rw [ha] at hf
            have := Sum.inr.inj hf; omega
        · have hklt : u - 10 < C.gates.length := by omega
          have hueq : u = 10 + (u - 10) := by omega
          cases he : isElim 10 C.gates st₀ ⟨u - 10, hklt⟩ with
          | false =>
            have hkv := finalSt_keep_val hmin hnc st₀ hst₀ ⟨u - 10, hklt⟩ he
            dsimp only at hkv
            rw [← hueq] at hkv
            rw [hkv] at hf
            have hlen_eq : (runAt 10 C.gates st₀ (u - 10)).2.length = (runAt 10 C.gates st₀ k₀.val).2.length := by
              have := Sum.inr.inj hf; omega
            have hkeq := keep_len_inj C.gates st₀ ⟨u - 10, hklt⟩ k₀ he hkeep0 hlen_eq
            have hveq : u - 10 = k₀.val := congrArg Fin.val hkeq
            omega
          | true =>
            rw [hueq] at hf
            obtain ⟨i, hi, hilt, hfi⟩ := finalSt_elim_inr_from_input hmin hnc st₀ hst₀ ⟨u - 10, hklt⟩ he (10 + j₀.val) hf
            have hilt' : i < u := by dsimp only at hilt; omega
            have hieq := ih i hilt' (by omega) hfi
            subst hieq
            exact absurd hi (hno_not k₀ hgk₀ ⟨u - 10, hklt⟩ he)
    obtain ⟨k₁, _, hkeep1, hlen1, _, hins1, _⟩ :=
      runAt_out_source hmin hnc st₀ hst₀ C.gates.length le_rfl j₁.val j₁.isLt
    obtain ⟨k₂, _, hkeep2, hlen2, _, hins2, _⟩ :=
      runAt_out_source hmin hnc st₀ hst₀ C.gates.length le_rfl j₂.val j₂.isLt
    obtain ⟨i₁, hi₁, hilt1, hfi1⟩ := hins1 (10 + j₀.val) h1
    obtain ⟨i₂, hi₂, hilt2, hfi2⟩ := hins2 (10 + j₀.val) h2
    have he1 := hclean_k₀ i₁ (by omega) hfi1
    have he2 := hclean_k₀ i₂ (by omega) hfi2
    subst he1; subst he2
    have hk_eq := hgood.2 k₀ hgk₀ k₁ k₂ hi₁ hi₂
    subst hk_eq
    exact Fin.ext (hlen1.symm.trans hlen2)

private lemma fin10_unused_of_not_active (v : Fin 10)
    (h : v ∉ ({2, 3, 4, 5, 6, 7} : Finset (Fin 10))) :
    v ∈ ({0, 1, 8, 9} : Finset (Fin 10)) := by revert v; decide

private lemma fin10_end_of_mem (v : Fin 10)
    (h1 : v ∈ ({2, 3, 4, 5, 6, 7} : Finset (Fin 10)))
    (h2 : v ∉ ({3, 4, 5, 6} : Finset (Fin 10))) :
    v = 2 ∨ v = 7 := by revert v; decide

private lemma fin10_leaf_ne_core (lv v : Fin 10) (hlv : lv = 8 ∨ lv = 9)
    (hv : v ∈ ({3, 4, 5, 6} : Finset (Fin 10))) : lv ≠ v := by revert lv v; decide

private lemma P6_no_good_circuit (C : Circuit)
    (hmin : MinimalCircuit 10 fP6 C) (hlen : C.gates.length ≤ 7)
    (hgood : ∀ v ∈ ({3, 4, 5, 6} : Finset (Fin 10)), GoodVar C v) : False := by
  have hnc : ∃ x x' : Fin 10 → Bool, fP6 x ≠ fP6 x' :=
    ⟨fun _ => false, fun _ => true, by decide⟩
  have hnotlit : ∀ i : Fin 10, (∃ x, fP6 x ≠ x i) ∧ (∃ x, fP6 x ≠ !x i) := by
    intro i
    constructor
    · refine ⟨fun j => decide (j = i), ?_⟩; fin_cases i <;> decide
    · refine ⟨fun _ => false, ?_⟩; fin_cases i <;> decide
  have hindep : ∀ (v : Fin 10), v ∈ ({0, 1, 8, 9} : Finset (Fin 10)) →
      ∀ x b, fP6 (Function.update x v b) = fP6 x := by
    intro v hv x b
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl | rfl <;> simp [fP6, Function.update]
  have hno_unused : ∀ (v : Fin 10), v ∈ ({0, 1, 8, 9} : Finset (Fin 10)) → gateUses C v.val = ∅ := by
    intro v hv
    by_contra hne
    obtain ⟨k, hk⟩ := Finset.nonempty_iff_ne_empty.2 hne
    rw [mem_gateUses] at hk
    have hst₀ : (initAssign 10 (singleAssign v false)).length = 10 := by simp [initAssign]
    have hfv : finalSt 10 C.gates (initAssign 10 (singleAssign v false)) v.val = Sum.inl false := by
      rw [finalSt_init 10 C.gates _ v.val (by rw [hst₀]; exact v.isLt), initAssign, ofFn_getD_lt _ _ v.val v.isLt]
      simp [singleAssign]
    have hek := elim_const_input hmin hnc _ hst₀ k v.val hk ⟨false, hfv⟩
    have hrew : (fun x => fP6 (applyAssign (singleAssign v false) x)) = fP6 := by
      ext x; rw [applyAssign_single, hindep v hv]
    have hnc' : ∃ x x', fP6 (applyAssign (singleAssign v false) x) ≠ fP6 (applyAssign (singleAssign v false) x') := by
      obtain ⟨x, x', hx⟩ := hnc; exact ⟨x, x', by rw [congrFun hrew x, congrFun hrew x']; exact hx⟩
    obtain ⟨h1, hcs⟩ := elim_size_of_card hmin (singleAssign v false) hnc' {k} (by simpa using hek)
    rw [hrew] at hcs
    rw [Finset.card_singleton] at h1 hcs
    exact hmin.2.2 (C.gates.length - 1) (by omega) hcs
  have hdep_core : ∀ a b : Fin 10, a ∈ ({3, 4, 5, 6} : Finset (Fin 10)) →
      b ∈ ({2, 3, 4, 5, 6, 7} : Finset (Fin 10)) → a ≠ b → ∀ cb : Bool,
      ∃ x : Fin 10 → Bool,
        fP6 (Function.update (Function.update x b cb) a false) ≠
        fP6 (Function.update (Function.update x b cb) a true) := by
    have hall : ∀ a b : Fin 10, a ∈ ({3, 4, 5, 6} : Finset (Fin 10)) →
        b ∈ ({2, 3, 4, 5, 6, 7} : Finset (Fin 10)) → a ≠ b → ∀ cb : Bool,
        ∃ w : Fin 10,
          fP6 (Function.update (Function.update (fun i => decide (i = w)) b cb) a false) ≠
          fP6 (Function.update (Function.update (fun i => decide (i = w)) b cb) a true) := by
      decide
    intro a b ha hb hne cb
    obtain ⟨w, hw⟩ := hall a b ha hb hne cb
    exact ⟨fun i => decide (i = w), hw⟩
  have hdep_ends : ∀ a b : Fin 10, (a = 2 ∧ b = 7 ∨ a = 7 ∧ b = 2) → ∀ cb : Bool,
      ∃ x : Fin 10 → Bool,
        fP6 (Function.update (Function.update x b cb) a false) ≠
        fP6 (Function.update (Function.update x b cb) a true) := by
    have hall : ∀ a b : Fin 10, (a = 2 ∧ b = 7 ∨ a = 7 ∧ b = 2) → ∀ cb : Bool,
        ∃ w : Fin 10,
          fP6 (Function.update (Function.update (fun i => decide (i = w)) b cb) a false) ≠
          fP6 (Function.update (Function.update (fun i => decide (i = w)) b cb) a true) := by
      decide
    intro a b hab cb
    obtain ⟨w, hw⟩ := hall a b hab cb
    exact ⟨fun i => decide (i = w), hw⟩
  obtain ⟨k_star, hbin, hprev⟩ := first_non_not_gate hmin hnc hnotlit
  rcases minimal_gate_shape hmin hnc k_star.val k_star.isLt with
    ⟨hnot, _, _, _⟩ | ⟨hop, wa, wb, hwa_lt, hwb_lt, hwne, hin⟩
  · rcases hbin with h | h <;> rw [hnot] at h <;> cases h
  · have hlit : ∀ w : ℕ, w < 10 + k_star.val → w ∈ C.gates[k_star.val].inputs →
        ∃ v : Fin 10, v ∈ ({2, 3, 4, 5, 6, 7} : Finset (Fin 10)) ∧
          (w = v.val ∨ ∃ k_n : Fin C.gates.length, w = 10 + k_n.val ∧
            C.gates[k_n.val] = ⟨GateOp.not, [v.val]⟩) := by
      intro w hw hmem
      have hmem_active : ∀ v : Fin 10, (∃ k : Fin C.gates.length, v.val ∈ C.gates[k.val].inputs) →
          v ∈ ({2, 3, 4, 5, 6, 7} : Finset (Fin 10)) := by
        intro v ⟨k, hk⟩
        by_contra hnot
        have hv0 : v ∈ ({0, 1, 8, 9} : Finset (Fin 10)) := fin10_unused_of_not_active v hnot
        have hem := hno_unused v hv0
        have : k ∈ gateUses C v.val := mem_gateUses.2 hk
        rw [hem] at this; simp at this
      by_cases hwm : w < 10
      · exact ⟨⟨w, hwm⟩, hmem_active ⟨w, hwm⟩ ⟨k_star, hmem⟩, Or.inl rfl⟩
      · have hklt : w - 10 < k_star.val := by omega
        have hklen : w - 10 < C.gates.length := by omega
        obtain ⟨v, hgv⟩ := hprev ⟨w - 10, hklen⟩ hklt
        exact ⟨v, hmem_active v ⟨⟨w - 10, hklen⟩, by rw [hgv]; simp⟩,
          Or.inr ⟨⟨w - 10, hklen⟩, by show w = 10 + (w - 10); omega, hgv⟩⟩
    obtain ⟨v_a, hva_mem, hwa_lit⟩ := hlit wa hwa_lt (by rw [hin]; simp)
    obtain ⟨v_b, hvb_mem, hwb_lit⟩ := hlit wb hwb_lt (by rw [hin]; simp)
    have hkill_core : ∀ (u v : Fin 10) (wu wv : ℕ),
        u ∈ ({3, 4, 5, 6} : Finset (Fin 10)) →
        v ∈ ({2, 3, 4, 5, 6, 7} : Finset (Fin 10)) →
        (C.gates[k_star.val] = ⟨C.gates[k_star.val].op, [wu, wv]⟩ ∨
         C.gates[k_star.val] = ⟨C.gates[k_star.val].op, [wv, wu]⟩) →
        wu ≠ wv →
        (wu = u.val ∨ ∃ k_u : Fin C.gates.length, wu = 10 + k_u.val ∧
          C.gates[k_u.val] = ⟨GateOp.not, [u.val]⟩) →
        (wv = v.val ∨ ∃ k_v : Fin C.gates.length, wv = 10 + k_v.val ∧
          C.gates[k_v.val] = ⟨GateOp.not, [v.val]⟩) → False := by
      intro u v wu wv hu hv hk_or hne_w hwu hwv
      have hgu := hgood u hu
      have hwu_spec : (wu = u.val ∧ gateUses C u.val = {k_star}) ∨
          ∃ k_u : Fin C.gates.length, wu = 10 + k_u.val ∧
            C.gates[k_u.val] = ⟨GateOp.not, [u.val]⟩ ∧
            gateUses C u.val = {k_u} ∧ gateUses C (10 + k_u.val) = {k_star} := by
        rcases hwu with rfl | ⟨k_u, rfl, hku⟩
        · left; refine ⟨rfl, ?_⟩
          ext k; simp only [mem_gateUses, Finset.mem_singleton]
          have hks : u.val ∈ C.gates[k_star.val].inputs := by
            rcases hk_or with h | h <;> rw [h] <;> simp
          exact ⟨fun hk => hgu.1 k k_star hk hks, fun h => h ▸ hks⟩
        · right; refine ⟨k_u, rfl, hku, ?_, ?_⟩
          · ext k; simp only [mem_gateUses, Finset.mem_singleton]
            have hks : u.val ∈ C.gates[k_u.val].inputs := by rw [hku]; simp
            exact ⟨fun hk => hgu.1 k k_u hk hks, fun h => h ▸ hks⟩
          · ext k; simp only [mem_gateUses, Finset.mem_singleton]
            have hks : 10 + k_u.val ∈ C.gates[k_star.val].inputs := by
              rcases hk_or with h | h <;> rw [h] <;> simp
            exact ⟨fun hk => hgu.2 k_u hku k k_star hk hks, fun h => h ▸ hks⟩
      have huv_ne : u ≠ v := by
        intro heq; subst heq
        rcases hwu_spec with ⟨rfl, _⟩ | ⟨k_u, rfl, hku, huses_u, _⟩
        · rcases hwv with rfl | ⟨k_v, rfl, hkv⟩
          · exact hne_w rfl
          · have hm1 : u.val ∈ C.gates[k_star.val].inputs := by rcases hk_or with h | h <;> rw [h] <;> simp
            have hm2 : 10 + k_v.val ∈ C.gates[k_star.val].inputs := by rcases hk_or with h | h <;> rw [h] <;> simp
            exact minimal_no_not_and_same_var hmin hnc k_v k_star u.val (by have := u.isLt; omega) hkv hm1 hm2
        · rcases hwv with rfl | ⟨k_v, rfl, hkv⟩
          · have hm1 : u.val ∈ C.gates[k_star.val].inputs := by rcases hk_or with h | h <;> rw [h] <;> simp
            have hm2 : 10 + k_u.val ∈ C.gates[k_star.val].inputs := by rcases hk_or with h | h <;> rw [h] <;> simp
            exact minimal_no_not_and_same_var hmin hnc k_u k_star u.val (by have := u.isLt; omega) hku hm1 hm2
          · have hmem : k_v ∈ gateUses C u.val := by rw [mem_gateUses, hkv]; simp
            rw [huses_u, Finset.mem_singleton] at hmem; subst hmem
            exact hne_w rfl
      exact bin_gate_kills_dep hmin u v huv_ne C.gates[k_star.val].op hop k_star wu wv
        hk_or hwu_spec hwv (hnotlit u)
        (hdep_core u v hu hv huv_ne false) (hdep_core u v hu hv huv_ne true)
    have hk_eq : C.gates[k_star.val] = ⟨C.gates[k_star.val].op, [wa, wb]⟩ := by
      cases h : C.gates[k_star.val]; simp_all
    by_cases ha_core : v_a ∈ ({3, 4, 5, 6} : Finset (Fin 10))
    · exact hkill_core v_a v_b wa wb ha_core hvb_mem (Or.inl hk_eq) hwne hwa_lit hwb_lit
    · by_cases hb_core : v_b ∈ ({3, 4, 5, 6} : Finset (Fin 10))
      · exact hkill_core v_b v_a wb wa hb_core hva_mem (Or.inr hk_eq) hwne.symm hwb_lit hwa_lit
      · have hva_end : v_a = 2 ∨ v_a = 7 := fin10_end_of_mem v_a hva_mem ha_core
        have hvb_end : v_b = 2 ∨ v_b = 7 := fin10_end_of_mem v_b hvb_mem hb_core
        have hnc_end (b : Bool) : ∃ x x' : Fin 10 → Bool,
            fP6 (Function.update x v_a b) ≠ fP6 (Function.update x' v_a b) := by
          rcases hva_end with rfl | rfl <;> cases b
          · exact ⟨fun _ => false, fun _ => true, by decide⟩
          · exact ⟨fun _ => false, fun _ => true, by decide⟩
          · exact ⟨fun _ => false, fun _ => true, by decide⟩
          · exact ⟨fun _ => false, fun _ => true, by decide⟩
        have hvne_ab : v_a ≠ v_b := by
          intro heq; subst heq
          rcases hwa_lit with rfl | ⟨k_a, rfl, hka⟩
          · rcases hwb_lit with rfl | ⟨k_b, rfl, hkb⟩
            · exact hwne rfl
            · exact minimal_no_not_and_same_var hmin hnc k_b k_star v_a.val
                (by have := v_a.isLt; omega) hkb (by rw [hin]; simp) (by rw [hin]; simp)
          · rcases hwb_lit with rfl | ⟨k_b, rfl, hkb⟩
            · exact minimal_no_not_and_same_var hmin hnc k_a k_star v_a.val
                (by have := v_a.isLt; omega) hka (by rw [hin]; simp) (by rw [hin]; simp)
            · have hst := not_gate_structure hmin hnc v_a (hnc_end false)
                (fun s hs => P6_end_lower v_a hva_end false hs) (by omega) k_a hka
              have hmem : k_b ∈ gateUses C v_a.val := by rw [mem_gateUses, hkb]; simp
              rw [hst.1, Finset.mem_singleton] at hmem; subst hmem
              exact hwne rfl
        have hab_pair : v_a = 2 ∧ v_b = 7 ∨ v_a = 7 ∧ v_b = 2 := by
          rcases hva_end with rfl | rfl <;> rcases hvb_end with rfl | rfl
          · exact absurd rfl hvne_ab
          · exact Or.inl ⟨rfl, rfl⟩
          · exact Or.inr ⟨rfl, rfl⟩
          · exact absurd rfl hvne_ab
        rcases hwa_lit with rfl | ⟨k_a, rfl, hka⟩
        · by_cases hfan2 : ∃ k' : Fin C.gates.length, k' ≠ k_star ∧ v_a.val ∈ C.gates[k'.val].inputs
          · obtain ⟨k', hne', hk'⟩ := hfan2
            let ctrl : Bool := match C.gates[k_star.val].op with | GateOp.and => false | _ => true
            have hst₀ : (initAssign 10 (singleAssign v_a ctrl)).length = 10 := by simp [initAssign]
            have hfv : finalSt 10 C.gates (initAssign 10 (singleAssign v_a ctrl)) v_a.val = Sum.inl ctrl := by
              rw [finalSt_init 10 C.gates _ v_a.val (by rw [hst₀]; exact v_a.isLt), initAssign, ofFn_getD_lt _ _ v_a.val v_a.isLt]
              simp [singleAssign]
            have hek' := elim_const_input hmin hnc _ hst₀ k' v_a.val hk' ⟨ctrl, hfv⟩
            have hks_const : isElim 10 C.gates (initAssign 10 (singleAssign v_a ctrl)) k_star = true ∧
                finalSt 10 C.gates (initAssign 10 (singleAssign v_a ctrl)) (10 + k_star.val) = Sum.inl ctrl := by
              rcases hop with hop_eq | hop_eq
              · have hctrl : ctrl = false := by simp [ctrl, hop_eq]
                rw [hctrl] at hst₀ hfv ⊢
                have hgk : C.gates[k_star.val] = ⟨GateOp.and, [v_a.val, wb]⟩ := by rw [hk_eq, hop_eq]
                have hs := runAt_step_and 10 C.gates _ hst₀ k_star v_a.val wb hwa_lt hwb_lt hgk
                rw [hfv] at hs
                cases hfb : finalSt 10 C.gates _ wb <;> rw [hfb] at hs <;> exact ⟨hs.1, by simpa using hs.2⟩
              · have hctrl : ctrl = true := by simp [ctrl, hop_eq]
                rw [hctrl] at hst₀ hfv ⊢
                have hgk : C.gates[k_star.val] = ⟨GateOp.or, [v_a.val, wb]⟩ := by rw [hk_eq, hop_eq]
                have hs := runAt_step_or 10 C.gates _ hst₀ k_star v_a.val wb hwa_lt hwb_lt hgk
                rw [hfv] at hs
                cases hfb : finalSt 10 C.gates _ wb <;> rw [hfb] at hs <;> exact ⟨hs.1, by simpa using hs.2⟩
            have hnc_ctrl' : ∃ x x',
                fP6 (applyAssign (singleAssign v_a ctrl) x) ≠ fP6 (applyAssign (singleAssign v_a ctrl) x') := by
              simpa [applyAssign_single] using hnc_end ctrl
            obtain ⟨h_c, hk_hc, hh_mem, hehc⟩ :=
              gate_const_has_consumer hmin hnc (singleAssign v_a ctrl) hnc_ctrl' k_star ctrl hks_const.2
            have hhc_ne_ks : h_c ≠ k_star := fun h => by have := congrArg Fin.val h; omega
            have hhc_ne_k' : h_c ≠ k' := by
              intro heq; subst heq
              exact minimal_no_absorb hmin hnc k_star h_c v_a.val (by have := v_a.isLt; omega)
                hop (by rw [hin]; simp) hk' hh_mem
            have hcard3 : ({k_star, k', h_c} : Finset (Fin C.gates.length)).card = 3 := by
              rw [Finset.card_insert_of_notMem (by simp [hne'.symm, hhc_ne_ks.symm]),
                  Finset.card_pair hhc_ne_k'.symm]
            obtain ⟨h3le, hcs⟩ := elim_size_of_card hmin (singleAssign v_a ctrl) hnc_ctrl' {k_star, k', h_c} (by
              intro j hj; simp only [Finset.mem_insert, Finset.mem_singleton] at hj
              rcases hj with rfl | rfl | rfl
              · exact hks_const.1
              · exact hek'
              · exact hehc)
            rw [hcard3] at h3le hcs
            have hrew : (fun x => fP6 (applyAssign (singleAssign v_a ctrl) x)) =
                (fun x => fP6 (Function.update x v_a ctrl)) := by ext x; rw [applyAssign_single]
            rw [hrew] at hcs
            have h5 := P6_end_lower v_a hva_end ctrl hcs
            omega
          · push Not at hfan2
            have huses : gateUses C v_a.val = {k_star} := by
              ext k; simp only [mem_gateUses, Finset.mem_singleton]
              constructor
              · intro hk; by_contra hne; exact hfan2 k hne hk
              · rintro rfl; rw [hin]; simp
            exact bin_gate_kills_dep hmin v_a v_b hvne_ab C.gates[k_star.val].op hop k_star v_a.val wb
              (Or.inl hk_eq) (Or.inl ⟨rfl, huses⟩) hwb_lit (hnotlit v_a)
              (hdep_ends v_a v_b hab_pair false) (hdep_ends v_a v_b hab_pair true)
        · obtain ⟨hv_u, k₁, hk₁_u, _⟩ := not_gate_structure hmin hnc v_a (hnc_end false)
            (fun s hs => P6_end_lower v_a hva_end false hs) (by omega) k_a hka
          have hmem : k_star ∈ gateUses C (10 + k_a.val) := by rw [mem_gateUses, hin]; simp
          rw [hk₁_u, Finset.mem_singleton] at hmem; subst hmem
          exact bin_gate_kills_dep hmin v_a v_b hvne_ab C.gates[k_star.val].op hop k_star (10 + k_a.val) wb
            (Or.inl hk_eq) (Or.inr ⟨k_a, rfl, hka, hv_u, hk₁_u⟩) hwb_lit (hnotlit v_a)
            (hdep_ends v_a v_b hab_pair false) (hdep_ends v_a v_b hab_pair true)

private lemma leaf_structure_G {C : Circuit}
    (hmin : MinimalCircuit 10 fG C) (hlen : C.gates.length ≤ 13)
    (lv : Fin 10) (hlv : lv = 8 ∨ lv = 9) :
    ∃ g_l h_l : Fin C.gates.length,
      gateUses C lv.val = {g_l} ∧
      C.gates[g_l.val].op = GateOp.or ∧
      gateUses C (10 + g_l.val) = {h_l} ∧
      C.gates[h_l.val].op = GateOp.and := by
  have hnc : ∃ x x' : Fin 10 → Bool, fG x ≠ fG x' := ⟨fun _ => false, fun _ => true, by decide⟩
  have hdep : ∃ x : Fin 10 → Bool, fG (Function.update x lv false) ≠ fG (Function.update x lv true) := by
    rcases hlv with rfl | rfl
    · exact ⟨fun i => decide (i = 0), by decide⟩
    · exact ⟨fun i => decide (i = 1), by decide⟩
  have hnc0 : ∃ x x' : Fin 10 → Bool, fG (Function.update x lv false) ≠ fG (Function.update x' lv false) := by
    rcases hlv with rfl | rfl <;> exact ⟨fun _ => false, fun _ => true, by decide⟩
  have hnc1 : ∃ x x' : Fin 10 → Bool, fG (Function.update x lv true) ≠ fG (Function.update x' lv true) := by
    rcases hlv with rfl | rfl <;> exact ⟨fun _ => false, fun _ => true, by decide⟩
  have hlow0 : ∀ s, HasCircuitSize 10 (fun x => fG (Function.update x lv false)) s → 12 ≤ s := by
    rcases hlv with rfl | rfl
    · exact fun _ h => G_x8_0_lower h
    · exact fun _ h => G_x9_0_lower h
  have hlow1 : ∀ s, HasCircuitSize 10 (fun x => fG (Function.update x lv true)) s → 11 ≤ s := by
    rcases hlv with rfl | rfl
    · exact fun _ h => G_x8_1_lower h
    · exact fun _ h => G_x9_1_lower h
  have hst₀ (b : Bool) : (initAssign 10 (singleAssign lv b)).length = 10 := by simp [initAssign]
  have hfv (b : Bool) : finalSt 10 C.gates (initAssign 10 (singleAssign lv b)) lv.val = Sum.inl b := by
    rw [finalSt_init 10 C.gates _ lv.val (by rw [hst₀ b]; exact lv.isLt), initAssign, ofFn_getD_lt _ _ lv.val lv.isLt]
    simp [singleAssign]
  have hnc0' : ∃ x x', fG (applyAssign (singleAssign lv false) x) ≠ fG (applyAssign (singleAssign lv false) x') := by
    simpa [applyAssign_single] using hnc0
  have hnc1' : ∃ x x', fG (applyAssign (singleAssign lv true) x) ≠ fG (applyAssign (singleAssign lv true) x') := by
    simpa [applyAssign_single] using hnc1
  have hno2_0 : ∀ K : Finset (Fin C.gates.length),
      (∀ k ∈ K, isElim 10 C.gates (initAssign 10 (singleAssign lv false)) k = true) → K.card ≤ 1 := by
    intro K hK
    obtain ⟨_, hcs⟩ := elim_size_of_card hmin (singleAssign lv false) hnc0' K hK
    have hrew : (fun x => fG (applyAssign (singleAssign lv false) x)) =
        (fun x => fG (Function.update x lv false)) := by ext x; rw [applyAssign_single]
    rw [hrew] at hcs
    have := hlow0 _ hcs; omega
  have hno3_1 : ∀ K : Finset (Fin C.gates.length),
      (∀ k ∈ K, isElim 10 C.gates (initAssign 10 (singleAssign lv true)) k = true) → K.card ≤ 2 := by
    intro K hK
    obtain ⟨_, hcs⟩ := elim_size_of_card hmin (singleAssign lv true) hnc1' K hK
    have hrew : (fun x => fG (applyAssign (singleAssign lv true) x)) =
        (fun x => fG (Function.update x lv true)) := by ext x; rw [applyAssign_single]
    rw [hrew] at hcs
    have := hlow1 _ hcs; omega
  have hout_ne := output_ne_of_nonconst_update hmin lv false hnc0
  obtain ⟨g_l, hgl⟩ := var_has_consumer hmin lv hdep hout_ne
  have hg_uses : gateUses C lv.val = {g_l} := by
    ext k; simp only [mem_gateUses, Finset.mem_singleton]
    constructor
    · intro hk
      by_contra hne
      have he1 := elim_const_input hmin hnc _ (hst₀ false) g_l lv.val hgl ⟨false, hfv false⟩
      have he2 := elim_const_input hmin hnc _ (hst₀ false) k lv.val hk ⟨false, hfv false⟩
      have hcard2 := Finset.card_pair (Ne.symm hne)
      have hle1 := hno2_0 {g_l, k} (by
        intro j hj; simp only [Finset.mem_insert, Finset.mem_singleton] at hj
        rcases hj with rfl | rfl <;> assumption)
      omega
    · rintro rfl; exact hgl
  have hg_or : C.gates[g_l.val].op = GateOp.or := by
    rcases minimal_gate_shape hmin hnc g_l.val g_l.isLt with
      ⟨hop, a, ha, hin⟩ | ⟨hop, a, b, ha, hb, _, hin⟩
    · exfalso
      rw [hin] at hgl; simp at hgl; subst hgl
      have hgg : C.gates[g_l.val] = ⟨GateOp.not, [lv.val]⟩ := by cases h : C.gates[g_l.val]; simp_all
      have hs := runAt_step_not 10 C.gates _ (hst₀ false) g_l lv.val ha hgg
      rw [hfv false] at hs
      obtain ⟨k', hklt, _, he'⟩ := gate_const_has_consumer hmin hnc (singleAssign lv false) hnc0' g_l true hs.2
      have hne : g_l ≠ k' := fun h => by have := congrArg Fin.val h; omega
      have hcard2 := Finset.card_pair hne
      have hle1 := hno2_0 {g_l, k'} (by
        intro j hj; simp only [Finset.mem_insert, Finset.mem_singleton] at hj
        rcases hj with rfl | rfl; exact hs.1; exact he')
      omega
    · rcases hop with hop | hop
      · exfalso
        have hgg : C.gates[g_l.val] = ⟨GateOp.and, [a, b]⟩ := by cases h : C.gates[g_l.val]; simp_all
        rw [hin] at hgl; simp at hgl
        have hs := runAt_step_and 10 C.gates _ (hst₀ false) g_l a b ha hb hgg
        have hfc : isElim 10 C.gates (initAssign 10 (singleAssign lv false)) g_l = true ∧
            finalSt 10 C.gates (initAssign 10 (singleAssign lv false)) (10 + g_l.val) = Sum.inl false := by
          rcases hgl with rfl | rfl
          · rw [hfv false] at hs; cases hfb : finalSt 10 C.gates _ b <;> rw [hfb] at hs <;> exact ⟨hs.1, by simpa using hs.2⟩
          · rw [hfv false] at hs; cases hfa : finalSt 10 C.gates _ a <;> rw [hfa] at hs <;> exact ⟨hs.1, by simpa using hs.2⟩
        obtain ⟨k', hklt, _, he'⟩ := gate_const_has_consumer hmin hnc (singleAssign lv false) hnc0' g_l false hfc.2
        have hne : g_l ≠ k' := fun h => by have := congrArg Fin.val h; omega
        have hcard2 := Finset.card_pair hne
        have hle1 := hno2_0 {g_l, k'} (by
          intro j hj; simp only [Finset.mem_insert, Finset.mem_singleton] at hj
          rcases hj with rfl | rfl; exact hfc.1; exact he')
        omega
      · exact hop
  have hgl_true : isElim 10 C.gates (initAssign 10 (singleAssign lv true)) g_l = true ∧
      finalSt 10 C.gates (initAssign 10 (singleAssign lv true)) (10 + g_l.val) = Sum.inl true := by
    rcases minimal_gate_shape hmin hnc g_l.val g_l.isLt with
      ⟨hnot, _, _, _⟩ | ⟨_, a, b, ha, hb, _, hin⟩
    · rw [hg_or] at hnot; cases hnot
    · have hgg : C.gates[g_l.val] = ⟨GateOp.or, [a, b]⟩ := by cases h : C.gates[g_l.val]; simp_all
      rw [hin] at hgl; simp at hgl
      have hs := runAt_step_or 10 C.gates _ (hst₀ true) g_l a b ha hb hgg
      rcases hgl with rfl | rfl
      · rw [hfv true] at hs; cases hfb : finalSt 10 C.gates _ b <;> rw [hfb] at hs <;> exact ⟨hs.1, by simpa using hs.2⟩
      · rw [hfv true] at hs; cases hfa : finalSt 10 C.gates _ a <;> rw [hfa] at hs <;> exact ⟨hs.1, by simpa using hs.2⟩
  obtain ⟨h_l, hgl_hl, hhl_mem, he_hl⟩ :=
    gate_const_has_consumer hmin hnc (singleAssign lv true) hnc1' g_l true hgl_true.2
  have hne_gh : h_l ≠ g_l := fun h => by have := congrArg Fin.val h; omega
  have hhl_uses : gateUses C (10 + g_l.val) = {h_l} := by
    ext k; simp only [mem_gateUses, Finset.mem_singleton]
    constructor
    · intro hk
      by_contra hne
      have hek := elim_const_input hmin hnc _ (hst₀ true) k (10 + g_l.val) hk ⟨true, hgl_true.2⟩
      have hne_kg : k ≠ g_l := fun h => by
        have hlt := consumer_gt_of_minimal hmin hnc g_l k hk
        have := congrArg Fin.val h; omega
      have hcard3 : ({g_l, h_l, k} : Finset (Fin C.gates.length)).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp [hne_gh.symm, hne_kg.symm]),
            Finset.card_pair (Ne.symm hne)]
      have hle2 := hno3_1 {g_l, h_l, k} (by
        intro j hj; simp only [Finset.mem_insert, Finset.mem_singleton] at hj
        rcases hj with rfl | rfl | rfl
        · exact hgl_true.1
        · exact he_hl
        · exact hek)
      omega
    · rintro rfl; exact hhl_mem
  have hhl_and : C.gates[h_l.val].op = GateOp.and := by
    rcases minimal_gate_shape hmin hnc h_l.val h_l.isLt with
      ⟨hop, a, ha, hin⟩ | ⟨hop, a, b, ha, hb, _, hin⟩
    · exfalso
      rw [hin] at hhl_mem; simp at hhl_mem; subst hhl_mem
      have hgh : C.gates[h_l.val] = ⟨GateOp.not, [10 + g_l.val]⟩ := by cases h : C.gates[h_l.val]; simp_all
      have hs := runAt_step_not 10 C.gates _ (hst₀ true) h_l (10 + g_l.val) ha hgh
      rw [hgl_true.2] at hs
      obtain ⟨k', hklt, _, he'⟩ := gate_const_has_consumer hmin hnc (singleAssign lv true) hnc1' h_l false hs.2
      have hne_kg : k' ≠ g_l := fun h => by have := congrArg Fin.val h; omega
      have hne_kh : k' ≠ h_l := fun h => by have := congrArg Fin.val h; omega
      have hcard3 : ({g_l, h_l, k'} : Finset (Fin C.gates.length)).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp [hne_gh.symm, hne_kg.symm]),
            Finset.card_pair hne_kh.symm]
      have hle2 := hno3_1 {g_l, h_l, k'} (by
        intro j hj; simp only [Finset.mem_insert, Finset.mem_singleton] at hj
        rcases hj with rfl | rfl | rfl
        · exact hgl_true.1
        · exact he_hl
        · exact he')
      omega
    · rcases hop with hop | hop
      · exact hop
      · exfalso
        have hgh : C.gates[h_l.val] = ⟨GateOp.or, [a, b]⟩ := by cases h : C.gates[h_l.val]; simp_all
        rw [hin] at hhl_mem; simp at hhl_mem
        have hs := runAt_step_or 10 C.gates _ (hst₀ true) h_l a b ha hb hgh
        have hfh : finalSt 10 C.gates (initAssign 10 (singleAssign lv true)) (10 + h_l.val) = Sum.inl true := by
          rcases hhl_mem with rfl | rfl
          · rw [hgl_true.2] at hs; cases hfb : finalSt 10 C.gates _ b <;> rw [hfb] at hs <;> simpa using hs.2
          · rw [hgl_true.2] at hs; cases hfa : finalSt 10 C.gates _ a <;> rw [hfa] at hs <;> simpa using hs.2
        obtain ⟨k', hklt, _, he'⟩ := gate_const_has_consumer hmin hnc (singleAssign lv true) hnc1' h_l true hfh
        have hne_kg : k' ≠ g_l := fun h => by have := congrArg Fin.val h; omega
        have hne_kh : k' ≠ h_l := fun h => by have := congrArg Fin.val h; omega
        have hcard3 : ({g_l, h_l, k'} : Finset (Fin C.gates.length)).card = 3 := by
          rw [Finset.card_insert_of_notMem (by simp [hne_gh.symm, hne_kg.symm]),
              Finset.card_pair hne_kh.symm]
        have hle2 := hno3_1 {g_l, h_l, k'} (by
          intro j hj; simp only [Finset.mem_insert, Finset.mem_singleton] at hj
          rcases hj with rfl | rfl | rfl
          · exact hgl_true.1
          · exact he_hl
          · exact he')
        omega
  exact ⟨g_l, h_l, hg_uses, hg_or, hhl_uses, hhl_and⟩

private lemma step_elim_or_lit {L : ℕ} {F : (Fin 10 → Bool) → Bool} {C : Circuit}
    (hmin : MinimalCircuit 10 F C) (hlen : C.gates.length = L + 1)
    (u : Fin 10) (hu_not_core : u ∉ ({3, 4, 5, 6} : Finset (Fin 10)))
    (hdep : ∃ x : Fin 10 → Bool, F (Function.update x u false) ≠ F (Function.update x u true))
    (hnc0 : ∃ x x' : Fin 10 → Bool, F (Function.update x u false) ≠ F (Function.update x' u false))
    (hlow0 : ∀ s, HasCircuitSize 10 (fun x => F (Function.update x u false)) s → L ≤ s)
    (hnotlit_u : (∃ x, F x ≠ x u) ∧ (∃ x, F x ≠ !x u))
    (hdep_core : ∀ v ∈ ({3, 4, 5, 6} : Finset (Fin 10)), ∀ b : Bool,
      ∃ x : Fin 10 → Bool,
        F (Function.update (Function.update x v b) u false) ≠
        F (Function.update (Function.update x v b) u true))
    (hgood : ∀ v ∈ ({3, 4, 5, 6} : Finset (Fin 10)), GoodVar C v) :
    ∃ C' : Circuit, MinimalCircuit 10 (fun x => F (Function.update x u false)) C' ∧
      C'.gates.length = L ∧
      ∀ v ∈ ({3, 4, 5, 6} : Finset (Fin 10)), GoodVar C' v := by
  have hnc : ∃ x x' : Fin 10 → Bool, F x ≠ F x' := by obtain ⟨x, hx⟩ := hdep; exact ⟨_, _, hx⟩
  have hst₀ : (initAssign 10 (singleAssign u false)).length = 10 := by simp [initAssign]
  have hfu : finalSt 10 C.gates (initAssign 10 (singleAssign u false)) u.val = Sum.inl false := by
    rw [finalSt_init 10 C.gates _ u.val (by rw [hst₀]; exact u.isLt), initAssign, ofFn_getD_lt _ _ u.val u.isLt]
    simp [singleAssign]
  have hnc0' : ∃ x x', F (applyAssign (singleAssign u false) x) ≠ F (applyAssign (singleAssign u false) x') := by
    simpa [applyAssign_single] using hnc0
  have hout_ne := output_ne_of_nonconst_update hmin u false hnc0
  obtain ⟨k_u, hku⟩ := var_has_consumer hmin u hdep hout_ne
  have he_ku := elim_const_input hmin hnc _ hst₀ k_u u.val hku ⟨false, hfu⟩
  obtain ⟨outw, hok', hnok', hev', _⟩ := elim_run_circuit hmin (singleAssign u false) hnc0'
  let C' : Circuit := ⟨(runAt 10 C.gates (initAssign 10 (singleAssign u false)) C.gates.length).2, outw⟩
  have hrew : (fun x => F (applyAssign (singleAssign u false) x)) =
      (fun x => F (Function.update x u false)) := by ext x; rw [applyAssign_single]
  have hev_upd : ∀ x, C'.eval (List.ofFn x) = F (Function.update x u false) := by
    intro x; rw [hev' x, applyAssign_single]
  have hsum := elim_card_add_len 10 C.gates (initAssign 10 (singleAssign u false))
  have hLle : L ≤ C'.gates.length := hlow0 C'.gates.length ⟨C', hok', le_rfl, hev_upd⟩
  have hmem_el : k_u ∈ Finset.univ.filter (fun k : Fin C.gates.length =>
      isElim 10 C.gates (initAssign 10 (singleAssign u false)) k = true) :=
    Finset.mem_filter.2 ⟨Finset.mem_univ _, he_ku⟩
  have hcard_ge1 : 1 ≤ (Finset.univ.filter (fun k : Fin C.gates.length =>
      isElim 10 C.gates (initAssign 10 (singleAssign u false)) k = true)).card :=
    Finset.one_le_card.2 ⟨k_u, hmem_el⟩
  have hC'_len : C'.gates.length = L := by
    have hC'eq : C'.gates.length =
        (runAt 10 C.gates (initAssign 10 (singleAssign u false)) C.gates.length).2.length := rfl
    omega
  have helim_eq : Finset.univ.filter (fun k : Fin C.gates.length =>
      isElim 10 C.gates (initAssign 10 (singleAssign u false)) k = true) = {k_u} := by
    apply Finset.eq_singleton_iff_unique_mem.2 ⟨hmem_el, fun k hk => ?_⟩
    by_contra hne
    have hsub : {k_u, k} ⊆ Finset.univ.filter (fun j : Fin C.gates.length =>
        isElim 10 C.gates (initAssign 10 (singleAssign u false)) j = true) := by
      intro j hj; simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      rcases hj with rfl | rfl; exact hmem_el; exact hk
    have h2 := Finset.card_le_card hsub
    rw [Finset.card_pair (Ne.symm hne)] at h2
    change (runAt 10 C.gates (initAssign 10 (singleAssign u false)) C.gates.length).2.length = L at hC'_len
    omega
  have huses_u : gateUses C u.val = {k_u} := by
    ext k; simp only [mem_gateUses, Finset.mem_singleton]
    constructor
    · intro hk
      have hek := elim_const_input hmin hnc _ hst₀ k u.val hk ⟨false, hfu⟩
      have hmk : k ∈ Finset.univ.filter (fun j : Fin C.gates.length =>
          isElim 10 C.gates (initAssign 10 (singleAssign u false)) j = true) :=
        Finset.mem_filter.2 ⟨Finset.mem_univ _, hek⟩
      rw [helim_eq, Finset.mem_singleton] at hmk; exact hmk
    · rintro rfl; exact hku
  have hku_or : C.gates[k_u.val].op = GateOp.or := by
    rcases minimal_gate_shape hmin hnc k_u.val k_u.isLt with
      ⟨hop, a, ha, hin⟩ | ⟨hop, a, b, ha, hb, _, hin⟩
    · exfalso
      rw [hin] at hku; simp at hku; subst hku
      have hgk : C.gates[k_u.val] = ⟨GateOp.not, [u.val]⟩ := by cases h : C.gates[k_u.val]; simp_all
      have hs := runAt_step_not 10 C.gates _ hst₀ k_u u.val ha hgk
      rw [hfu] at hs
      obtain ⟨k', hklt, _, he'⟩ := gate_const_has_consumer hmin hnc (singleAssign u false) hnc0' k_u true hs.2
      have hmk : k' ∈ Finset.univ.filter (fun j : Fin C.gates.length =>
          isElim 10 C.gates (initAssign 10 (singleAssign u false)) j = true) :=
        Finset.mem_filter.2 ⟨Finset.mem_univ _, he'⟩
      rw [helim_eq, Finset.mem_singleton] at hmk
      have := congrArg Fin.val hmk; omega
    · rcases hop with hop | hop
      · exfalso
        have hgk : C.gates[k_u.val] = ⟨GateOp.and, [a, b]⟩ := by cases h : C.gates[k_u.val]; simp_all
        rw [hin] at hku; simp at hku
        have hs := runAt_step_and 10 C.gates _ hst₀ k_u a b ha hb hgk
        have hfc : finalSt 10 C.gates (initAssign 10 (singleAssign u false)) (10 + k_u.val) = Sum.inl false := by
          rcases hku with rfl | rfl
          · rw [hfu] at hs; cases hfb : finalSt 10 C.gates _ b <;> rw [hfb] at hs <;> simpa using hs.2
          · rw [hfu] at hs; cases hfa : finalSt 10 C.gates _ a <;> rw [hfa] at hs <;> simpa using hs.2
        obtain ⟨k', hklt, _, he'⟩ := gate_const_has_consumer hmin hnc (singleAssign u false) hnc0' k_u false hfc
        have hmk : k' ∈ Finset.univ.filter (fun j : Fin C.gates.length =>
            isElim 10 C.gates (initAssign 10 (singleAssign u false)) j = true) :=
          Finset.mem_filter.2 ⟨Finset.mem_univ _, he'⟩
        rw [helim_eq, Finset.mem_singleton] at hmk
        have := congrArg Fin.val hmk; omega
      · exact hop
  have hmin' : MinimalCircuit 10 (fun x => F (Function.update x u false)) C' :=
    ⟨hnok', hev_upd, fun r hr hcs => by have := hlow0 r hcs; omega⟩
  refine ⟨C', hmin', hC'_len, fun v hv => ?_⟩
  have huv : u ≠ v := fun h => hu_not_core (h ▸ hv)
  apply elim_step_preserve_goodVar hmin hnc (singleAssign u false) outw v (hgood v hv)
  · intro k he hvk
    have hkeq : k = k_u := by
      have hm : k ∈ Finset.univ.filter (fun j : Fin C.gates.length =>
          isElim 10 C.gates (initAssign 10 (singleAssign u false)) j = true) :=
        Finset.mem_filter.2 ⟨Finset.mem_univ _, he⟩
      rw [helim_eq, Finset.mem_singleton] at hm; exact hm
    subst k
    rcases minimal_gate_shape hmin hnc k_u.val k_u.isLt with
      ⟨hnot, _, _, _⟩ | ⟨_, a, b, _, _, _, hin⟩
    · rw [hku_or] at hnot; cases hnot
    · have hpair : (a = u.val ∧ b = v.val) ∨ (a = v.val ∧ b = u.val) := by
        rw [hin] at hku hvk; simp at hku hvk
        have hne_val : u.val ≠ v.val := fun h => huv (Fin.ext h)
        rcases hku with rfl | rfl <;> rcases hvk with h | h <;>
          first | exact Or.inl ⟨rfl, h.symm⟩ | exact Or.inr ⟨h.symm, rfl⟩ | exact absurd h.symm hne_val
      have hgk : C.gates[k_u.val] = ⟨GateOp.or, [u.val, v.val]⟩ ∨
          C.gates[k_u.val] = ⟨GateOp.or, [v.val, u.val]⟩ := by
        rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inl (by cases h : C.gates[k_u.val]; simp_all)
        · exact Or.inr (by cases h : C.gates[k_u.val]; simp_all)
      exact bin_gate_kills_dep hmin u v huv GateOp.or (Or.inr rfl) k_u u.val v.val
        hgk (Or.inl ⟨rfl, huses_u⟩) (Or.inl rfl) hnotlit_u
        (hdep_core v hv false) (hdep_core v hv true)
  · intro k₀ hk₀ k he hk0_mem
    have hkeq : k = k_u := by
      have hm : k ∈ Finset.univ.filter (fun j : Fin C.gates.length =>
          isElim 10 C.gates (initAssign 10 (singleAssign u false)) j = true) :=
        Finset.mem_filter.2 ⟨Finset.mem_univ _, he⟩
      rw [helim_eq, Finset.mem_singleton] at hm; exact hm
    subst k
    rcases minimal_gate_shape hmin hnc k_u.val k_u.isLt with
      ⟨hnot, _, _, _⟩ | ⟨_, a, b, _, _, _, hin⟩
    · rw [hku_or] at hnot; cases hnot
    · have hpair : (a = u.val ∧ b = 10 + k₀.val) ∨ (a = 10 + k₀.val ∧ b = u.val) := by
        rw [hin] at hku hk0_mem; simp at hku hk0_mem
        have hne_val : u.val ≠ 10 + k₀.val := by have := u.isLt; omega
        rcases hku with rfl | rfl <;> rcases hk0_mem with h | h <;>
          first | exact Or.inl ⟨rfl, h.symm⟩ | exact Or.inr ⟨h.symm, rfl⟩ | exact absurd h.symm hne_val
      have hgk : C.gates[k_u.val] = ⟨GateOp.or, [u.val, 10 + k₀.val]⟩ ∨
          C.gates[k_u.val] = ⟨GateOp.or, [10 + k₀.val, u.val]⟩ := by
        rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inl (by cases h : C.gates[k_u.val]; simp_all)
        · exact Or.inr (by cases h : C.gates[k_u.val]; simp_all)
      exact bin_gate_kills_dep hmin u v huv GateOp.or (Or.inr rfl) k_u u.val (10 + k₀.val)
        hgk (Or.inl ⟨rfl, huses_u⟩) (Or.inr ⟨k₀, rfl, hk₀⟩) hnotlit_u
        (hdep_core v hv false) (hdep_core v hv true)

set_option maxHeartbeats 800000 in
private lemma G_lower {s : ℕ} (hC : HasCircuitSize 10 fG s) : 14 ≤ s := by
  by_contra hlt
  have hs13 : s ≤ 13 := by omega
  obtain ⟨C, hmin, hlen⟩ := exists_minimal_circuit hC
  have hC13 : C.gates.length ≤ 13 := by omega
  have hnc : ∃ x x' : Fin 10 → Bool, fG x ≠ fG x' := ⟨fun _ => false, fun _ => true, by decide⟩
  have hnotlit_G : ∀ i : Fin 10, (∃ x, fG x ≠ x i) ∧ (∃ x, fG x ≠ !x i) := by
    intro i; constructor
    · refine ⟨fun j => decide (j = i), ?_⟩; fin_cases i <;> decide
    · refine ⟨fun _ => false, ?_⟩; fin_cases i <;> decide
  obtain ⟨g8, h8, hg8_u, hg8_or, hh8_u, hh8_and⟩ := leaf_structure_G hmin hC13 8 (Or.inl rfl)
  obtain ⟨g9, h9, hg9_u, hg9_or, hh9_u, hh9_and⟩ := leaf_structure_G hmin hC13 9 (Or.inr rfl)
  have hcore_good : ∀ v ∈ ({3, 4, 5, 6} : Finset (Fin 10)),
      GoodVar C v ∧
      ∀ k₀ : Fin C.gates.length, C.gates[k₀.val] = ⟨GateOp.not, [v.val]⟩ →
        ∃ k₁ : Fin C.gates.length, gateUses C (10 + k₀.val) = {k₁} ∧ C.gates[k₁.val].op = GateOp.and := by
    intro v hv
    have hdep_v : ∃ x, fG (Function.update x v false) ≠ fG (Function.update x v true) := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl | rfl
      · exact ⟨fun i => decide (i = 2), by decide⟩
      · exact ⟨fun i => decide (i = 3), by decide⟩
      · exact ⟨fun i => decide (i = 4), by decide⟩
      · exact ⟨fun i => decide (i = 5), by decide⟩
    have hnc_v (b : Bool) : ∃ x x', fG (Function.update x v b) ≠ fG (Function.update x' v b) := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl | rfl <;> cases b <;> exact ⟨fun _ => false, fun _ => true, by decide⟩
    obtain ⟨kv, hkv⟩ := var_fanout_one_of_bounds hmin v hdep_v (hnc_v false) (hnc_v true)
      (fun s hs => by simpa using G_core_update_lower v hv false hs)
      (fun s hs => by simpa using G_core_update_lower v hv true hs)
      (by omega) (by omega)
    have hnot_v : ∀ k₀ : Fin C.gates.length, C.gates[k₀.val] = ⟨GateOp.not, [v.val]⟩ →
        ∃ k₁ : Fin C.gates.length, gateUses C (10 + k₀.val) = {k₁} ∧ C.gates[k₁.val].op = GateOp.and := by
      intro k₀ hk₀
      exact (not_gate_structure hmin hnc v (hnc_v false)
        (fun s hs => by simpa using G_core_update_lower v hv false hs) (by omega) k₀ hk₀).2
    refine ⟨⟨fun k₁ k₂ h1 h2 => ?_, fun k₀ hk₀ k₁ k₂ h1 h2 => ?_⟩, hnot_v⟩
    · have m1 : k₁ ∈ gateUses C v.val := mem_gateUses.2 h1
      have m2 : k₂ ∈ gateUses C v.val := mem_gateUses.2 h2
      rw [hkv, Finset.mem_singleton] at m1 m2; exact m1.trans m2.symm
    · obtain ⟨k₁', hk₁', _⟩ := hnot_v k₀ hk₀
      have m1 : k₁ ∈ gateUses C (10 + k₀.val) := mem_gateUses.2 h1
      have m2 : k₂ ∈ gateUses C (10 + k₀.val) := mem_gateUses.2 h2
      rw [hk₁', Finset.mem_singleton] at m1 m2; exact m1.trans m2.symm
  have hdep_leaf_core : ∀ lv : Fin 10, (lv = 8 ∨ lv = 9) →
      ∀ v ∈ ({3, 4, 5, 6} : Finset (Fin 10)), ∀ b : Bool,
        ∃ x : Fin 10 → Bool,
          fG (Function.update (Function.update x v b) lv false) ≠
          fG (Function.update (Function.update x v b) lv true) := by
    have hall : ∀ lv : Fin 10, (lv = 8 ∨ lv = 9) →
        ∀ v ∈ ({3, 4, 5, 6} : Finset (Fin 10)), ∀ b : Bool,
          ∃ w : Fin 10,
            fG (Function.update (Function.update (fun i => decide (i = w)) v b) lv false) ≠
            fG (Function.update (Function.update (fun i => decide (i = w)) v b) lv true) := by
      decide
    intro lv hlv v hv b
    obtain ⟨w, hw⟩ := hall lv hlv v hv b
    exact ⟨fun i => decide (i = w), hw⟩
  have hg8_ne_g9 : g8 ≠ g9 := by
    intro heq; subst heq
    rcases minimal_gate_shape hmin hnc g8.val g8.isLt with
      ⟨hnot, _, _, _⟩ | ⟨_, a, b, _, _, _, hin⟩
    · rw [hg8_or] at hnot; cases hnot
    · have h8m : (8 : ℕ) ∈ C.gates[g8.val].inputs := by
        have : g8 ∈ gateUses C (8 : Fin 10).val := by rw [hg8_u]; simp
        exact mem_gateUses.1 this
      have h9m : (9 : ℕ) ∈ C.gates[g8.val].inputs := by
        have : g8 ∈ gateUses C (9 : Fin 10).val := by rw [hg9_u]; simp
        exact mem_gateUses.1 this
      have hpair : (a = 8 ∧ b = 9) ∨ (a = 9 ∧ b = 8) := by
        rw [hin] at h8m h9m; simp at h8m h9m
        rcases h8m with rfl | rfl <;> rcases h9m with h | h <;>
          first | exact Or.inl ⟨rfl, h.symm⟩ | exact Or.inr ⟨h.symm, rfl⟩ | omega
      have hgg : C.gates[g8.val] = ⟨GateOp.or, [8, 9]⟩ ∨ C.gates[g8.val] = ⟨GateOp.or, [9, 8]⟩ := by
        rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inl (by cases h : C.gates[g8.val]; simp_all)
        · exact Or.inr (by cases h : C.gates[g8.val]; simp_all)
      exact bin_gate_kills_dep hmin 8 9 (by decide) GateOp.or (Or.inr rfl) g8 8 9
        hgg (Or.inl ⟨rfl, hg8_u⟩) (Or.inl rfl) (hnotlit_G 8)
        ⟨fun i => decide (i = 0), by decide⟩ ⟨fun i => decide (i = 0), by decide⟩
  let a11 : Fin 10 → Option Bool := fun i => if i = 8 then some true else if i = 9 then some true else none
  have hst11 : (initAssign 10 a11).length = 10 := by simp [initAssign]
  have hf8_11 : finalSt 10 C.gates (initAssign 10 a11) 8 = Sum.inl true := by
    rw [finalSt_init 10 C.gates _ 8 (by omega), initAssign, ofFn_getD_lt _ _ 8 (by decide)]
    simp [a11]
  have hf9_11 : finalSt 10 C.gates (initAssign 10 a11) 9 = Sum.inl true := by
    rw [finalSt_init 10 C.gates _ 9 (by omega), initAssign, ofFn_getD_lt _ _ 9 (by decide)]
    simp [a11]
  have hrew11 : (fun x => fG (applyAssign a11 x)) = f11 := by
    ext x; simp [fG, f11, fP6, applyAssign, a11]; grind
  have hnc11' : ∃ x x', fG (applyAssign a11 x) ≠ fG (applyAssign a11 x') := by
    obtain ⟨x, x', hx⟩ : ∃ x x', f11 x ≠ f11 x' := ⟨fun _ => false, fun _ => true, by decide⟩
    exact ⟨x, x', by rw [congrFun hrew11 x, congrFun hrew11 x']; exact hx⟩
  have hleaf_elim11 : ∀ (lv : Fin 10) (gl hl : Fin C.gates.length),
      finalSt 10 C.gates (initAssign 10 a11) lv.val = Sum.inl true →
      gateUses C lv.val = {gl} → C.gates[gl.val].op = GateOp.or →
      gateUses C (10 + gl.val) = {hl} →
      isElim 10 C.gates (initAssign 10 a11) gl = true ∧
      finalSt 10 C.gates (initAssign 10 a11) (10 + gl.val) = Sum.inl true ∧
      isElim 10 C.gates (initAssign 10 a11) hl = true := by
    intro lv gl hl hflv hgu hgor hhu
    have hmem : lv.val ∈ C.gates[gl.val].inputs := mem_gateUses.1 (by rw [hgu]; simp)
    have hmem_h : 10 + gl.val ∈ C.gates[hl.val].inputs := mem_gateUses.1 (by rw [hhu]; simp)
    rcases minimal_gate_shape hmin hnc gl.val gl.isLt with
      ⟨hnot, _, _, _⟩ | ⟨_, a, b, ha, hb, _, hin⟩
    · rw [hgor] at hnot; cases hnot
    · have hgg : C.gates[gl.val] = ⟨GateOp.or, [a, b]⟩ := by cases h : C.gates[gl.val]; simp_all
      rw [hin] at hmem; simp at hmem
      have hs := runAt_step_or 10 C.gates (initAssign 10 a11) hst11 gl a b ha hb hgg
      have hres : isElim 10 C.gates (initAssign 10 a11) gl = true ∧
          finalSt 10 C.gates (initAssign 10 a11) (10 + gl.val) = Sum.inl true := by
        rcases hmem with rfl | rfl
        · rw [hflv] at hs; cases hfb : finalSt 10 C.gates _ b <;> rw [hfb] at hs <;> exact ⟨hs.1, by simpa using hs.2⟩
        · rw [hflv] at hs; cases hfa : finalSt 10 C.gates _ a <;> rw [hfa] at hs <;> exact ⟨hs.1, by simpa using hs.2⟩
      exact ⟨hres.1, hres.2, elim_const_input hmin hnc _ hst11 hl (10 + gl.val) hmem_h ⟨true, hres.2⟩⟩
  obtain ⟨he_g8, hfg8, he_h8⟩ := hleaf_elim11 8 g8 h8 hf8_11 hg8_u hg8_or hh8_u
  obtain ⟨he_g9, hfg9, he_h9⟩ := hleaf_elim11 9 g9 h9 hf9_11 hg9_u hg9_or hh9_u
  have hne_h8g8 : h8 ≠ g8 := fun h => by
    have hlt := consumer_gt_of_minimal hmin hnc g8 h8 (mem_gateUses.1 (by rw [hh8_u]; simp))
    have := congrArg Fin.val h; omega
  have hne_h9g9 : h9 ≠ g9 := fun h => by
    have hlt := consumer_gt_of_minimal hmin hnc g9 h9 (mem_gateUses.1 (by rw [hh9_u]; simp))
    have := congrArg Fin.val h; omega
  have hne_h8g9 : h8 ≠ g9 := fun h => by rw [h, hg9_or] at hh8_and; cases hh8_and
  have hne_h9g8 : h9 ≠ g8 := fun h => by rw [h, hg8_or] at hh9_and; cases hh9_and
  obtain ⟨out11, hok11, hnok11, hev11, _⟩ := elim_run_circuit hmin a11 hnc11'
  let C11 : Circuit := ⟨(runAt 10 C.gates (initAssign 10 a11) C.gates.length).2, out11⟩
  have hev11_f : ∀ x, C11.eval (List.ofFn x) = f11 x := fun x => (hev11 x).trans (congrFun hrew11 x)
  have h9le : 9 ≤ C11.gates.length := f11_lower ⟨C11, hok11, le_rfl, hev11_f⟩
  have hsum11 := elim_card_add_len 10 C.gates (initAssign 10 a11)
  let elimSet11 := Finset.univ.filter (fun k : Fin C.gates.length => isElim 10 C.gates (initAssign 10 a11) k = true)
  have hno_core_in_leaf_or : ∀ (lv : Fin 10) (hlv : lv = 8 ∨ lv = 9) (gl : Fin C.gates.length),
      gateUses C lv.val = {gl} → C.gates[gl.val].op = GateOp.or →
      ∀ v ∈ ({3, 4, 5, 6} : Finset (Fin 10)),
        v.val ∉ C.gates[gl.val].inputs ∧
        ∀ k₀ : Fin C.gates.length, C.gates[k₀.val] = ⟨GateOp.not, [v.val]⟩ →
          10 + k₀.val ∉ C.gates[gl.val].inputs := by
    intro lv hlv gl hgu hgor v hv
    constructor
    · intro hvm
      rcases minimal_gate_shape hmin hnc gl.val gl.isLt with
        ⟨hnot, _, _, _⟩ | ⟨_, a, b, _, _, _, hin⟩
      · rw [hgor] at hnot; cases hnot
      · have hlvm : lv.val ∈ C.gates[gl.val].inputs := mem_gateUses.1 (by rw [hgu]; simp)
        have hne_lv : lv ≠ v := fin10_leaf_ne_core lv v hlv hv
        have hne_val : lv.val ≠ v.val := fun h => hne_lv (Fin.ext h)
        have hpair : (a = lv.val ∧ b = v.val) ∨ (a = v.val ∧ b = lv.val) := by
          rw [hin] at hlvm hvm; simp at hlvm hvm
          rcases hlvm with rfl | rfl <;> rcases hvm with h | h <;>
            first | exact Or.inl ⟨rfl, h.symm⟩ | exact Or.inr ⟨h.symm, rfl⟩ | exact absurd h.symm hne_val
        have hgg : C.gates[gl.val] = ⟨GateOp.or, [lv.val, v.val]⟩ ∨
            C.gates[gl.val] = ⟨GateOp.or, [v.val, lv.val]⟩ := by
          rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact Or.inl (by cases h : C.gates[gl.val]; simp_all)
          · exact Or.inr (by cases h : C.gates[gl.val]; simp_all)
        exact bin_gate_kills_dep hmin lv v hne_lv GateOp.or (Or.inr rfl) gl lv.val v.val
          hgg (Or.inl ⟨rfl, hgu⟩) (Or.inl rfl) (hnotlit_G lv)
          (hdep_leaf_core lv hlv v hv false) (hdep_leaf_core lv hlv v hv true)
    · intro k₀ hk₀ hk0m
      obtain ⟨k₁, hk₁_u, hk₁_and⟩ := (hcore_good v hv).2 k₀ hk₀
      have hm : gl ∈ gateUses C (10 + k₀.val) := mem_gateUses.2 hk0m
      rw [hk₁_u, Finset.mem_singleton] at hm
      rw [← hm, hgor] at hk₁_and; cases hk₁_and
  have hno_core_in_and_chain : ∀ (lv : Fin 10) (hlv : lv = 8 ∨ lv = 9)
      (S : Set ℕ) (hSlv : lv.val ∈ S) (hSout : C.output ∉ S)
      (k_end : Fin C.gates.length) (hk_not_S : 10 + k_end.val ∉ S)
      (hk_and : C.gates[k_end.val].op = GateOp.and)
      (hS_closed : ∀ j (hj : j < C.gates.length), 10 + j ∉ S → j ≠ k_end.val →
        ∀ i ∈ C.gates[j].inputs, i ∉ S),
      ∀ v ∈ ({3, 4, 5, 6} : Finset (Fin 10)),
        v.val ∉ C.gates[k_end.val].inputs ∧
        ∀ k₀ : Fin C.gates.length, C.gates[k₀.val] = ⟨GateOp.not, [v.val]⟩ →
          10 + k₀.val ∉ C.gates[k_end.val].inputs := by
    intro lv hlv S hSlv hSout k_end hk_not_S hk_and hS_closed v hv
    have hne_lv : lv ≠ v := fin10_leaf_ne_core lv v hlv hv
    have hkill : ∀ (w_c : ℕ) (c_v : Bool),
        w_c ∈ C.gates[k_end.val].inputs →
        (∀ x : Fin 10 → Bool, wireFn C w_c (Function.update x v c_v) = false) → False := by
      intro w_c c_v hwm hwf
      rcases minimal_gate_shape hmin hnc k_end.val k_end.isLt with
        ⟨hnot, _, _, _⟩ | ⟨_, a, b, ha, hb, _, hin⟩
      · rw [hk_and] at hnot; cases hnot
      · apply fanout1_bin_dep_contradiction hmin lv v c_v (hdep_leaf_core lv hlv v hv c_v) S hSlv hSout
        intro j hj hjnot
        by_cases hjeq : j = k_end.val
        · subst hjeq
          right; intro x
          have hw0 : wireFn C w_c (Function.update (Function.update x v c_v) lv false) = false := by
            rw [Function.update_comm hne_lv.symm]; exact hwf _
          have hw1 : wireFn C w_c (Function.update (Function.update x v c_v) lv true) = false := by
            rw [Function.update_comm hne_lv.symm]; exact hwf _
          rw [wireFn_gate C k_end.val k_end.isLt, wireFn_gate C k_end.val k_end.isLt, hk_and, hin]
          rw [hin] at hwm; simp at hwm
          rcases hwm with rfl | rfl <;> simp [GateOp.eval, ha, hb, hw0, hw1]
        · exact Or.inl (hS_closed j hj hjnot hjeq)
    constructor
    · intro hvm
      exact hkill v.val false hvm (fun x => by rw [wireFn_input]; simp)
    · intro k₀ hk₀ hk0m
      exact hkill (10 + k₀.val) true hk0m (fun x => by
        rw [wireFn_gate C k₀.val k₀.isLt, hk₀]
        simp [GateOp.eval, show v.val < 10 + k₀.val by have := v.isLt; omega, wireFn_input])
  have hout_ne_lv : ∀ lv : Fin 10, (lv = 8 ∨ lv = 9) → C.output ≠ lv.val := by
    intro lv hlv heq
    obtain ⟨x, hx⟩ := (hnotlit_G lv).1
    have h1 := hmin.2.1 x
    have h2 : C.eval (List.ofFn x) = x lv := by
      show wireFn C C.output x = x lv; rw [heq]; exact wireFn_input C lv x
    exact hx (h1.symm.trans h2)
  have hout_ne_gl : ∀ gl : Fin C.gates.length,
      finalSt 10 C.gates (initAssign 10 a11) (10 + gl.val) = Sum.inl true → C.output ≠ 10 + gl.val := by
    intro gl hfg heq
    obtain ⟨_, _, _, _, hout_eq⟩ := elim_run_circuit hmin a11 hnc11'
    rw [heq, hfg] at hout_eq
    exact Sum.inl_ne_inr hout_eq
  have hC11_props : C11.gates.length = 9 ∧ ∀ v ∈ ({3, 4, 5, 6} : Finset (Fin 10)), GoodVar C11 v := by
    by_cases hh_eq : h8 = h9
    · subst hh_eq
      have hfh8 : finalSt 10 C.gates (initAssign 10 a11) (10 + h8.val) = Sum.inl true := by
        rcases minimal_gate_shape hmin hnc h8.val h8.isLt with
          ⟨hnot, _, _, _⟩ | ⟨_, a, b, ha, hb, _, hin⟩
        · rw [hh8_and] at hnot; cases hnot
        · have m8 : 10 + g8.val ∈ C.gates[h8.val].inputs := mem_gateUses.1 (by rw [hh8_u]; simp)
          have m9 : 10 + g9.val ∈ C.gates[h8.val].inputs := mem_gateUses.1 (by rw [hh9_u]; simp)
          have hne_val : 10 + g8.val ≠ 10 + g9.val := fun h => hg8_ne_g9 (Fin.ext (by omega))
          have hpair : (a = 10 + g8.val ∧ b = 10 + g9.val) ∨ (a = 10 + g9.val ∧ b = 10 + g8.val) := by
            rw [hin] at m8 m9; simp at m8 m9
            rcases m8 with rfl | rfl <;> rcases m9 with h | h <;>
              first | exact Or.inl ⟨rfl, h.symm⟩ | exact Or.inr ⟨h.symm, rfl⟩ | exact absurd h.symm hne_val
          have hgh : C.gates[h8.val] = ⟨GateOp.and, [a, b]⟩ := by cases h : C.gates[h8.val]; simp_all
          have hs := runAt_step_and 10 C.gates (initAssign 10 a11) hst11 h8 a b ha hb hgh
          rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rw [hfg8, hfg9] at hs <;> exact hs.2
      obtain ⟨k_c, hh8_kc, hkc_mem, he_kc⟩ := gate_const_has_consumer hmin hnc a11 hnc11' h8 true hfh8
      have hne_kcg8 : k_c ≠ g8 := fun h => by
        have hlt := consumer_gt_of_minimal hmin hnc g8 h8 (mem_gateUses.1 (by rw [hh8_u]; simp))
        have := congrArg Fin.val h; omega
      have hne_kcg9 : k_c ≠ g9 := fun h => by
        have hlt := consumer_gt_of_minimal hmin hnc g9 h8 (mem_gateUses.1 (by rw [hh9_u]; simp))
        have := congrArg Fin.val h; omega
      have hne_kch8 : k_c ≠ h8 := fun h => by have := congrArg Fin.val h; omega
      have hK4 : ({g8, g9, h8, k_c} : Finset (Fin C.gates.length)).card = 4 := by
        rw [Finset.card_insert_of_notMem (by simp [hg8_ne_g9, hne_h8g8.symm, hne_kcg8.symm]),
            Finset.card_insert_of_notMem (by simp [hne_h8g9.symm, hne_kcg9.symm]),
            Finset.card_pair hne_kch8.symm]
      have hsub : {g8, g9, h8, k_c} ⊆ elimSet11 := by
        intro j hj; simp only [Finset.mem_insert, Finset.mem_singleton] at hj
        simp only [elimSet11, Finset.mem_filter, Finset.mem_univ, true_and]
        rcases hj with rfl | rfl | rfl | rfl <;> assumption
      have h4le : 4 ≤ elimSet11.card := hK4 ▸ Finset.card_le_card hsub
      have hC11_eq : C11.gates.length = (runAt 10 C.gates (initAssign 10 a11) C.gates.length).2.length := rfl
      have helim_card_eq : elimSet11.card = (Finset.univ.filter (fun k : Fin C.gates.length =>
          isElim 10 C.gates (initAssign 10 a11) k = true)).card := rfl
      have hlen9 : C11.gates.length = 9 := by omega
      have helim_eq : elimSet11 = {g8, g9, h8, k_c} :=
        (Finset.eq_of_subset_of_card_le hsub (by rw [hK4]; omega)).symm
      have hh8_u_kc : gateUses C (10 + h8.val) = {k_c} := by
        ext j; simp only [mem_gateUses, Finset.mem_singleton]
        constructor
        · intro hj
          have hej := elim_const_input hmin hnc _ hst11 j (10 + h8.val) hj ⟨true, hfh8⟩
          have hmj : j ∈ elimSet11 := Finset.mem_filter.2 ⟨Finset.mem_univ _, hej⟩
          rw [helim_eq] at hmj
          simp only [Finset.mem_insert, Finset.mem_singleton] at hmj
          have hlt := consumer_gt_of_minimal hmin hnc h8 j hj
          have hlt8 := consumer_gt_of_minimal hmin hnc g8 h8 (mem_gateUses.1 (by rw [hh8_u]; simp))
          have hlt9 := consumer_gt_of_minimal hmin hnc g9 h8 (mem_gateUses.1 (by rw [hh9_u]; simp))
          rcases hmj with rfl | rfl | rfl | rfl
          · omega
          · omega
          · omega
          · rfl
        · rintro rfl; exact hkc_mem
      have hkc_and : C.gates[k_c.val].op = GateOp.and := by
        rcases minimal_gate_shape hmin hnc k_c.val k_c.isLt with
          ⟨hop, a, ha, hin⟩ | ⟨hop, a, b, ha, hb, _, hin⟩
        · exfalso
          rw [hin] at hkc_mem; simp at hkc_mem; subst hkc_mem
          have hgk : C.gates[k_c.val] = ⟨GateOp.not, [10 + h8.val]⟩ := by cases h : C.gates[k_c.val]; simp_all
          have hs := runAt_step_not 10 C.gates _ hst11 k_c (10 + h8.val) ha hgk
          rw [hfh8] at hs
          obtain ⟨k', hklt, _, he'⟩ := gate_const_has_consumer hmin hnc a11 hnc11' k_c false hs.2
          have hm : k' ∈ elimSet11 := Finset.mem_filter.2 ⟨Finset.mem_univ _, he'⟩
          rw [helim_eq] at hm; simp only [Finset.mem_insert, Finset.mem_singleton] at hm
          have hlt8 := consumer_gt_of_minimal hmin hnc g8 h8 (mem_gateUses.1 (by rw [hh8_u]; simp))
          have hlt9 := consumer_gt_of_minimal hmin hnc g9 h8 (mem_gateUses.1 (by rw [hh9_u]; simp))
          rcases hm with rfl | rfl | rfl | rfl <;> omega
        · rcases hop with hop | hop
          · exact hop
          · exfalso
            have hgk : C.gates[k_c.val] = ⟨GateOp.or, [a, b]⟩ := by cases h : C.gates[k_c.val]; simp_all
            rw [hin] at hkc_mem; simp at hkc_mem
            have hs := runAt_step_or 10 C.gates _ hst11 k_c a b ha hb hgk
            have hfkc : finalSt 10 C.gates (initAssign 10 a11) (10 + k_c.val) = Sum.inl true := by
              rcases hkc_mem with rfl | rfl
              · rw [hfh8] at hs; cases hfb : finalSt 10 C.gates _ b <;> rw [hfb] at hs <;> simpa using hs.2
              · rw [hfh8] at hs; cases hfa : finalSt 10 C.gates _ a <;> rw [hfa] at hs <;> simpa using hs.2
            obtain ⟨k', hklt, _, he'⟩ := gate_const_has_consumer hmin hnc a11 hnc11' k_c true hfkc
            have hm : k' ∈ elimSet11 := Finset.mem_filter.2 ⟨Finset.mem_univ _, he'⟩
            rw [helim_eq] at hm; simp only [Finset.mem_insert, Finset.mem_singleton] at hm
            have hlt8 := consumer_gt_of_minimal hmin hnc g8 h8 (mem_gateUses.1 (by rw [hh8_u]; simp))
            have hlt9 := consumer_gt_of_minimal hmin hnc g9 h8 (mem_gateUses.1 (by rw [hh9_u]; simp))
            rcases hm with rfl | rfl | rfl | rfl <;> omega
      have hkc_no_core := hno_core_in_and_chain 8 (Or.inl rfl) {8, 10 + g8.val, 10 + h8.val}
        (by simp) (by
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
          exact ⟨hout_ne_lv 8 (Or.inl rfl), hout_ne_gl g8 hfg8, hout_ne_gl h8 hfh8⟩)
        k_c (by
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
          exact ⟨by omega, fun h => hne_kcg8 (Fin.ext (by omega)), fun h => hne_kch8 (Fin.ext (by omega))⟩)
        hkc_and (by
          intro j hj hjnot hjeq i hi hmem
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
          rcases hmem with rfl | rfl | rfl
          · have hm : (⟨j, hj⟩ : Fin C.gates.length) ∈ gateUses C (8 : Fin 10).val := mem_gateUses.2 hi
            rw [hg8_u, Finset.mem_singleton] at hm
            have h1 : j = g8.val := congrArg Fin.val hm
            exact hjnot (Or.inr (Or.inl (by omega)))
          · have hm : (⟨j, hj⟩ : Fin C.gates.length) ∈ gateUses C (10 + g8.val) := mem_gateUses.2 hi
            rw [hh8_u, Finset.mem_singleton] at hm
            have h1 : j = h8.val := congrArg Fin.val hm
            exact hjnot (Or.inr (Or.inr (Set.mem_singleton_iff.2 (by omega))))
          · have hm : (⟨j, hj⟩ : Fin C.gates.length) ∈ gateUses C (10 + h8.val) := mem_gateUses.2 hi
            rw [hh8_u_kc, Finset.mem_singleton] at hm
            exact hjeq (congrArg Fin.val hm))
      have hh8_inputs_only : ∀ w ∈ C.gates[h8.val].inputs, w = 10 + g8.val ∨ w = 10 + g9.val := by
        rcases minimal_gate_shape hmin hnc h8.val h8.isLt with
          ⟨hnot, _, _, _⟩ | ⟨_, a, b, _, _, _, hin⟩
        · rw [hh8_and] at hnot; cases hnot
        · have m8 : 10 + g8.val ∈ C.gates[h8.val].inputs := mem_gateUses.1 (by rw [hh8_u]; simp)
          have m9 : 10 + g9.val ∈ C.gates[h8.val].inputs := mem_gateUses.1 (by rw [hh9_u]; simp)
          have hne_val : 10 + g8.val ≠ 10 + g9.val := fun h => hg8_ne_g9 (Fin.ext (by omega))
          intro w hw
          rw [hin] at m8 m9 hw; simp at m8 m9 hw
          rcases m8 with rfl | rfl <;> rcases m9 with h | h <;> rcases hw with rfl | rfl <;>
            first | exact Or.inl rfl | exact Or.inr h.symm | exact absurd h.symm hne_val
      refine ⟨hlen9, fun v hv => ?_⟩
      have hg8_nc := hno_core_in_leaf_or 8 (Or.inl rfl) g8 hg8_u hg8_or v hv
      have hg9_nc := hno_core_in_leaf_or 9 (Or.inr rfl) g9 hg9_u hg9_or v hv
      have hkc_nc := hkc_no_core v hv
      apply elim_step_preserve_goodVar hmin hnc a11 out11 v (hcore_good v hv).1
      · intro k he hvk
        have hmk : k ∈ elimSet11 := Finset.mem_filter.2 ⟨Finset.mem_univ _, he⟩
        rw [helim_eq] at hmk; simp only [Finset.mem_insert, Finset.mem_singleton] at hmk
        rcases hmk with rfl | rfl | rfl | rfl
        · exact hg8_nc.1 hvk
        · exact hg9_nc.1 hvk
        · rcases hh8_inputs_only v.val hvk with h | h <;> have := v.isLt <;> omega
        · exact hkc_nc.1 hvk
      · intro k₀ hk₀ k he hk0m
        have hmk : k ∈ elimSet11 := Finset.mem_filter.2 ⟨Finset.mem_univ _, he⟩
        rw [helim_eq] at hmk; simp only [Finset.mem_insert, Finset.mem_singleton] at hmk
        rcases hmk with rfl | rfl | rfl | rfl
        · exact hg8_nc.2 k₀ hk₀ hk0m
        · exact hg9_nc.2 k₀ hk₀ hk0m
        · rcases hh8_inputs_only (10 + k₀.val) hk0m with h | h
          · have hkeq : k₀ = g8 := Fin.ext (by omega)
            rw [hkeq] at hk₀
            have hop := congrArg Gate.op hk₀
            rw [hg8_or] at hop; cases hop
          · have hkeq : k₀ = g9 := Fin.ext (by omega)
            rw [hkeq] at hk₀
            have hop := congrArg Gate.op hk₀
            rw [hg9_or] at hop; cases hop
        · exact hkc_nc.2 k₀ hk₀ hk0m
    · have hK4 : ({g8, h8, g9, h9} : Finset (Fin C.gates.length)).card = 4 := by
        rw [Finset.card_insert_of_notMem (by simp [hne_h8g8.symm, hg8_ne_g9, hne_h9g8.symm]),
            Finset.card_insert_of_notMem (by simp [hne_h8g9, hh_eq]),
            Finset.card_pair hne_h9g9.symm]
      have hsub : {g8, h8, g9, h9} ⊆ elimSet11 := by
        intro j hj; simp only [Finset.mem_insert, Finset.mem_singleton] at hj
        simp only [elimSet11, Finset.mem_filter, Finset.mem_univ, true_and]
        rcases hj with rfl | rfl | rfl | rfl <;> assumption
      have h4le : 4 ≤ elimSet11.card := hK4 ▸ Finset.card_le_card hsub
      have hC11_eq : C11.gates.length = (runAt 10 C.gates (initAssign 10 a11) C.gates.length).2.length := rfl
      have helim_card_eq : elimSet11.card = (Finset.univ.filter (fun k : Fin C.gates.length =>
          isElim 10 C.gates (initAssign 10 a11) k = true)).card := rfl
      have hlen9 : C11.gates.length = 9 := by omega
      have helim_eq : elimSet11 = {g8, h8, g9, h9} :=
        (Finset.eq_of_subset_of_card_le hsub (by rw [hK4]; omega)).symm
      have hh8_no_core := hno_core_in_and_chain 8 (Or.inl rfl) {8, 10 + g8.val}
        (by simp) (by
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
          exact ⟨hout_ne_lv 8 (Or.inl rfl), hout_ne_gl g8 hfg8⟩)
        h8 (by
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
          exact ⟨by omega, fun h => hne_h8g8 (Fin.ext (by omega))⟩)
        hh8_and (by
          intro j hj hjnot hjeq i hi hmem
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
          rcases hmem with rfl | rfl
          · have hm : (⟨j, hj⟩ : Fin C.gates.length) ∈ gateUses C (8 : Fin 10).val := mem_gateUses.2 hi
            rw [hg8_u, Finset.mem_singleton] at hm
            have h1 : j = g8.val := congrArg Fin.val hm
            exact hjnot (Or.inr (Set.mem_singleton_iff.2 (by omega)))
          · have hm : (⟨j, hj⟩ : Fin C.gates.length) ∈ gateUses C (10 + g8.val) := mem_gateUses.2 hi
            rw [hh8_u, Finset.mem_singleton] at hm
            exact hjeq (congrArg Fin.val hm))
      have hh9_no_core := hno_core_in_and_chain 9 (Or.inr rfl) {9, 10 + g9.val}
        (by simp) (by
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
          exact ⟨hout_ne_lv 9 (Or.inr rfl), hout_ne_gl g9 hfg9⟩)
        h9 (by
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
          exact ⟨by omega, fun h => hne_h9g9 (Fin.ext (by omega))⟩)
        hh9_and (by
          intro j hj hjnot hjeq i hi hmem
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
          rcases hmem with rfl | rfl
          · have hm : (⟨j, hj⟩ : Fin C.gates.length) ∈ gateUses C (9 : Fin 10).val := mem_gateUses.2 hi
            rw [hg9_u, Finset.mem_singleton] at hm
            have h1 : j = g9.val := congrArg Fin.val hm
            exact hjnot (Or.inr (Set.mem_singleton_iff.2 (by omega)))
          · have hm : (⟨j, hj⟩ : Fin C.gates.length) ∈ gateUses C (10 + g9.val) := mem_gateUses.2 hi
            rw [hh9_u, Finset.mem_singleton] at hm
            exact hjeq (congrArg Fin.val hm))
      refine ⟨hlen9, fun v hv => ?_⟩
      have hg8_nc := hno_core_in_leaf_or 8 (Or.inl rfl) g8 hg8_u hg8_or v hv
      have hg9_nc := hno_core_in_leaf_or 9 (Or.inr rfl) g9 hg9_u hg9_or v hv
      have hh8_nc := hh8_no_core v hv
      have hh9_nc := hh9_no_core v hv
      apply elim_step_preserve_goodVar hmin hnc a11 out11 v (hcore_good v hv).1
      · intro k he hvk
        have hmk : k ∈ elimSet11 := Finset.mem_filter.2 ⟨Finset.mem_univ _, he⟩
        rw [helim_eq] at hmk; simp only [Finset.mem_insert, Finset.mem_singleton] at hmk
        rcases hmk with rfl | rfl | rfl | rfl
        · exact hg8_nc.1 hvk
        · exact hh8_nc.1 hvk
        · exact hg9_nc.1 hvk
        · exact hh9_nc.1 hvk
      · intro k₀ hk₀ k he hk0m
        have hmk : k ∈ elimSet11 := Finset.mem_filter.2 ⟨Finset.mem_univ _, he⟩
        rw [helim_eq] at hmk; simp only [Finset.mem_insert, Finset.mem_singleton] at hmk
        rcases hmk with rfl | rfl | rfl | rfl
        · exact hg8_nc.2 k₀ hk₀ hk0m
        · exact hh8_nc.2 k₀ hk₀ hk0m
        · exact hg9_nc.2 k₀ hk₀ hk0m
        · exact hh9_nc.2 k₀ hk₀ hk0m
  obtain ⟨hC11_len, hC11_good⟩ := hC11_props
  have hmin11 : MinimalCircuit 10 f11 C11 :=
    ⟨hnok11, hev11_f, fun r hr hcs => by have := f11_lower hcs; omega⟩
  have hrew01 : (fun x => f11 (Function.update x 0 false)) = f01 := by
    ext x; simp [f11, f01, fP6, Function.update]
  obtain ⟨C01, hmin01, hC01_len, hC01_good⟩ := step_elim_or_lit hmin11 hC11_len 0 (by decide)
    ⟨fun _ => false, by decide⟩
    ⟨fun _ => false, fun _ => true, by decide⟩
    (fun s hs => by rw [hrew01] at hs; exact f01_lower hs)
    ⟨⟨fun i => decide (i = 1), by decide⟩, ⟨fun _ => false, by decide⟩⟩
    (fun v hv b => ⟨fun _ => false, by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl | rfl <;> cases b <;> decide⟩)
    hC11_good
  rw [hrew01] at hmin01
  have hrew00 : (fun x => f01 (Function.update x 1 false)) = fP6 := by
    ext x; simp [f01, fP6, Function.update]
  obtain ⟨C00, hmin00, hC00_len, hC00_good⟩ := step_elim_or_lit hmin01 hC01_len 1 (by decide)
    ⟨fun _ => false, by decide⟩
    ⟨fun _ => false, fun _ => true, by decide⟩
    (fun s hs => by rw [hrew00] at hs; exact fP6_lower hs)
    ⟨⟨fun i => decide (i = 2) || decide (i = 3), by decide⟩, ⟨fun _ => false, by decide⟩⟩
    (fun v hv b => ⟨fun _ => false, by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl | rfl <;> cases b <;> decide⟩)
    hC01_good
  rw [hrew00] at hmin00
  exact P6_no_good_circuit C00 hmin00 (by omega) hC00_good

end PEqualNP.Outside.Meta518

theorem PEqualNP.Outside.L_meta_518 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 10 (fun x : Fin 10 → Bool =>
      (x 0 && x 1) || (x 0 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) ||
      (x 5 && x 6) || (x 6 && x 7) || (x 7 && x 1) || (x 0 && x 8) || (x 1 && x 9)) s →
      14 ≤ s :=
  fun _ h => PEqualNP.Outside.Meta518.G_lower h
