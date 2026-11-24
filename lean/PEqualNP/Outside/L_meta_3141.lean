import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_3141

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

private lemma simplifyGate_nok (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ)) :
    ∀ g ∈ (simplifyGate op m ins).1, NOkGate g := by
  intro g hg
  cases op <;> simp only [simplifyGate] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg; exact ⟨⟨Or.inl rfl, by simp⟩, by simp⟩
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg; exact ⟨⟨Or.inr (Or.inl rfl), by simp⟩, by simp⟩
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg
    subst hg; exact ⟨⟨Or.inr (Or.inr rfl), by simp⟩, by simp⟩
  · simp at hg
  · simp at hg

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

private lemma elimPass_nil (m : ℕ) (acc : List (Bool ⊕ ℕ) × List Gate) :
    elimPass m [] acc = acc := rfl

private lemma elimPass_cons (m : ℕ) (g : Gate) (gs : List Gate)
    (acc : List (Bool ⊕ ℕ) × List Gate) :
    elimPass m (g :: gs) acc = elimPass m gs (elimStep m acc g) := rfl

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

private def valG (w : List Bool) (g : Gate) := g.op.eval (g.inputs.map fun i => w.getD i false)

private def DiffConst (A B : List Bool) (tab : List (Bool ⊕ ℕ)) : Prop :=
  ∀ i, A.getD i false ≠ B.getD i false → ∃ c, tab.getD i (.inl false) = .inl c

private lemma pass_le (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) :
    (elimPass 11 gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp [elimPass]
  | cons g gs ih =>
    have h := ih (elimStep 11 acc g)
    rw [elimPass_cons]
    simp only [elimStep, List.length_append] at h ⊢
    have ht := toList_opt_len_le (simplifyGate g.op (11 + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (.inl false))).1
    simp only [List.length_cons]
    omega

private lemma diff_pass (gs : List Gate) (A B : List Bool) (acc : List (Bool ⊕ ℕ) × List Gate)
    (hg : ∀ g ∈ gs, NOkGate g) (ha : A.length = acc.1.length)
    (hb : B.length = acc.1.length) (hd : DiffConst A B acc.1) :
    (elimPass 11 gs acc).2.length < acc.2.length + gs.length ∨
      DiffConst (wiresFrom gs A) (wiresFrom gs B) (elimPass 11 gs acc).1 := by
  induction gs generalizing A B acc with
  | nil => exact Or.inr hd
  | cons g gs ih =>
    let next := elimStep 11 acc g
    let part := simplifyGate g.op (11 + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (.inl false))
    have hn : next.2.length = acc.2.length + part.1.toList.length := List.length_append
    have hlen := toList_opt_len_le part.1
    change (elimPass 11 gs next).2.length < acc.2.length + (gs.length + 1) ∨
      DiffConst (wiresFrom gs (A ++ [valG A g])) (wiresFrom gs (B ++ [valG B g]))
        (elimPass 11 gs next).1
    by_cases hv : valG A g = valG B g
    · have hd' : DiffConst (A ++ [valG A g]) (B ++ [valG B g]) next.1 := by
        intro i hi
        by_cases he : i = acc.1.length
        · rw [getD_snoc_eq _ _ _ _ (by omega), getD_snoc_eq _ _ _ _ (by omega)] at hi
          contradiction
        · rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)] at hi
          change ∃ c, (acc.1 ++ [part.2]).getD i (.inl false) = .inl c
          rw [getD_snoc_ne _ _ _ _ he]
          exact hd i hi
      rcases ih _ _ next (fun g' h => hg g' (List.mem_cons_of_mem _ h))
        (by simp [next, elimStep, ha]) (by simp [next, elimStep, hb]) hd' with h | h
      · exact Or.inl (by omega)
      · exact Or.inr h
    · have hw : ∃ i ∈ g.inputs, A.getD i false ≠ B.getD i false := by
        by_contra! h
        apply hv
        exact congrArg g.op.eval (List.map_congr_left h)
      obtain ⟨i, hi, hne⟩ := hw
      obtain ⟨c, hc⟩ := hd i hne
      have hok := hg g List.mem_cons_self
      have hno : part.1 = none := simplifyGate_none_of_const _ _ _ hok.1.1
        (by simpa using hok.1.2) (fun e => by simpa using hok.2 e)
        ⟨c, List.mem_map.mpr ⟨i, hi, hc⟩⟩
      rw [hno] at hn
      simp at hn
      exact Or.inl (by have := pass_le gs next; omega)

private def firstTen (x : Fin 9 → Bool) := List.ofFn x ++ [x 0 || x 4]

private def pre (x : Fin 9 → Bool) (p : ℕ) :=
  firstTen x ++ [!(firstTen x).getD p false]

private def testIn (b : Bool) (i : Fin 9) :=
  if i = 0 then true else if i = 4 then b else false

private def cut (x : Fin 8 → Bool) : Fin 9 → Bool := Fin.insertNth (4 : Fin 9) false x

private def pick (p : ℕ) : Fin 8 :=
  ([0,1,2,3,0,4,5,6,7,0] : List (Fin 8)).getD p 0

private def negStat (p : ℕ) : Bool ⊕ ℕ :=
  if p = 4 ∨ 10 ≤ p then .inl true else .inr 8

private def initTab (p : ℕ) : List (Bool ⊕ ℕ) :=
  [.inr 0,.inr 1,.inr 2,.inr 3,.inl false,.inr 4,.inr 5,.inr 6,.inr 7,.inr 0,negStat p]

private def newIn (p : ℕ) (x : Fin 8 → Bool) := List.ofFn x ++ [!x (pick p),true,false]

private lemma cutTen (x : Fin 8 → Bool) : firstTen (cut x) =
    [x 0,x 1,x 2,x 3,false,x 4,x 5,x 6,x 7,x 0] := by
  apply List.ext_getElem
  · simp [firstTen]
  · intro i hi _
    have h : i < 10 := by simpa [firstTen] using hi
    interval_cases i <;> first | rfl | exact Bool.or_false _

private lemma tenTest (b : Bool) : firstTen (testIn b) =
    [true,false,false,false,b,false,false,false,false,true] := by
  rfl

private lemma neg_ok (p : ℕ) (x : Fin 8 → Bool) :
    statValid 11 (negStat p) ∧ statVal (newIn p x) (negStat p) = !(firstTen (cut x)).getD p false := by
  by_cases h : p < 10
  · rw [cutTen]
    interval_cases p <;> simp [negStat,statValid,statVal,newIn,pick,List.getD_eq_getElem?_getD]
  · have hp : 10 ≤ p := by omega
    rw [List.getD_eq_default _ _ (by simp [firstTen]; omega)]
    simp [negStat,hp,statValid,statVal]

private lemma start_ok (p : ℕ) (x : Fin 8 → Bool) :
    ElimInv 11 (newIn p x) (pre (cut x) p) (initTab p, []) := by
  refine ⟨by simp [newIn], by simp [initTab,pre,firstTen], ?_⟩
  intro i
  by_cases hi : i < 10
  · rw [show pre (cut x) p = firstTen (cut x) ++ [!(firstTen (cut x)).getD p false] from rfl,
      getD_snoc_lt _ _ _ _ (by simpa [firstTen] using hi), cutTen]
    interval_cases i <;> simp [initTab,statValid,statVal,wiresFrom_nil,newIn,List.getD_eq_getElem?_getD]
  · by_cases he : i = 10
    · subst i
      change statValid 11 (negStat p) ∧ statVal (newIn p x) (negStat p) = _
      unfold pre
      rw [getD_snoc_eq _ _ _ _ (by simp [firstTen])]
      exact neg_ok p x
    · change statValid 11 ((initTab p).getD i (.inl false)) ∧
        statVal (newIn p x) ((initTab p).getD i (.inl false)) = _
      rw [List.getD_eq_default _ _ (by simp [initTab]; omega),
        List.getD_eq_default _ _ (by simp [pre,firstTen]; omega)]
      exact ⟨trivial,rfl⟩

private lemma start_diff (p : ℕ) : DiffConst (pre (testIn true) p) (pre (testIn false) p) (initTab p) := by
  intro i hi
  simp only [pre,tenTest] at hi
  by_cases h : i < 10
  · rw [getD_snoc_lt _ _ _ _ h, getD_snoc_lt _ _ _ _ h] at hi
    interval_cases i <;> first | exact ⟨false,rfl⟩ | exact (hi rfl).elim
  · by_cases he : i = 10
    · subst i
      change (!([true,false,false,false,true,false,false,false,false,true] : List Bool).getD p false) ≠
        (!([true,false,false,false,false,false,false,false,false,true] : List Bool).getD p false) at hi
      by_cases hp : p < 10
      · interval_cases p <;> first | exact ⟨true,rfl⟩ | exact (hi rfl).elim
      · rw [List.getD_eq_default _ _ (by change 10 ≤ p; omega),
          List.getD_eq_default _ _ (by change 10 ≤ p; omega)] at hi
        exact (hi rfl).elim
    · exact (hi ((List.getD_eq_default _ _ (by simp; omega)).trans
          (List.getD_eq_default _ _ (by simp; omega)).symm)).elim

private lemma prefix_eval (g k : Gate) (gs : List Gate) (o : ℕ) (hk : k.op = .not)
    (h9 : ∀ x : Fin 9 → Bool, (Circuit.wires ⟨g :: k :: gs,o⟩ (List.ofFn x)).getD 9 false =
      (x 0 || x 4)) (x : Fin 9 → Bool) :
    Circuit.eval ⟨g :: k :: gs,o⟩ (List.ofFn x) =
      (wiresFrom (gs.map normGate) (pre x (k.inputs.headD 10))).getD o false := by
  let w := List.ofFn x
  have hh := h9 x
  change (wiresFrom (k :: gs) (w ++ [valG w g])).getD 9 false = _ at hh
  rw [wiresFrom_getD_lt _ _ _ (by simp [w]), getD_snoc_eq _ _ _ _ (by simp [w])] at hh
  have hw : w ++ [valG w g] = firstTen x := by rw [hh]; rfl
  change (wiresFrom gs ((w ++ [valG w g]) ++ [valG (w ++ [valG w g]) k])).getD o false = _
  rw [hw,wiresFrom_norm]
  have hval : valG (firstTen x) k = !(firstTen x).getD (k.inputs.headD 10) false := by
    simp only [valG,hk,GateOp.eval]
    cases he : k.inputs with
    | nil =>
      change (!false) = !(firstTen x).getD 10 false
      rw [List.getD_eq_default _ _ (by simp [firstTen])]
    | cons a as => rfl
  rw [hval]
  rfl

private def constWire (b : Bool) : ℕ := if b then 9 else 10

private lemma const_eval (b : Bool) (p : ℕ) (x : Fin 8 → Bool) :
    Circuit.eval ⟨[],constWire b⟩ (newIn p x) = b := by
  change (newIn p x).getD (constWire b) false = b
  cases b <;> simp [newIn,constWire,List.getD_eq_getElem?_getD]

end PEqualNP.Outside.L_meta_3141

open PEqualNP.Outside.L_meta_3141 in
theorem PEqualNP.Outside.L_meta_3141 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (0 : Fin (9 : ℕ)) || x3 (4 : Fin (9 : ℕ)))) → Option.map PEqualNP.CircuitLowerBounds.Gate.op x1.gates[(1 : ℕ)]? = Option.some PEqualNP.CircuitLowerBounds.GateOp.not → x1.size ≤ (15 : ℕ) → x1.eval [Bool.true, Bool.false, Bool.false, Bool.false, Bool.true, Bool.false, Bool.false, Bool.false, Bool.false] ≠ x1.eval [Bool.true, Bool.false, Bool.false, Bool.false, Bool.false, Bool.false, Bool.false, Bool.false, Bool.false] → ∃ (x7 : Fin (8 : ℕ)) (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x8 ∧ x8.size ≤ (12 : ℕ) ∧ ∀ (x9 : Fin (8 : ℕ) → Bool), x8.eval (List.ofFn x9 ++ [!x9 x7, Bool.true, Bool.false]) = x1.eval (List.ofFn (Fin.insertNth (4 : Fin (9 : ℕ)) Bool.false x9)) := by
  intro C hfan h9 hn hsize hdiff
  obtain ⟨gs,o⟩ := C
  rcases gs with _ | ⟨g, _ | ⟨k, tail⟩⟩
  · simp at hn
  · simp at hn
  have hk : k.op = .not := by simpa using hn
  let p := k.inputs.headD 10
  let gs := tail.map normGate
  let acc := elimPass 11 gs (initTab p, [])
  have hok : ∀ a ∈ gs, NOkGate a := by
    intro a ha
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
    exact normGate_nok b (hfan b (by simp [hb]))
  have he (x : Fin 9 → Bool) := prefix_eval g k tail o hk h9 x
  have hh : (wiresFrom gs (pre (testIn true) p)).getD o false ≠
      (wiresFrom gs (pre (testIn false) p)).getD o false := by
    rw [← he, ← he]
    exact hdiff
  have hval (x : Fin 8 → Bool) :
      statVal (wiresFrom acc.2 (newIn p x)) (acc.1.getD o (.inl false)) =
        Circuit.eval ⟨g :: k :: tail,o⟩ (List.ofFn (cut x)) := by
    rw [he]
    exact ((elimInv_pass 11 _ gs _ _ (fun a ha => (hok a ha).1) (start_ok p x)).2.2 o).2
  refine ⟨pick p, ?_⟩
  cases ho : acc.1.getD o (.inl false) with
  | inl c =>
    refine ⟨⟨[],constWire c⟩, by simp [FanInTwo], Nat.zero_le _, ?_⟩
    intro x
    have hv := hval x
    rw [ho] at hv
    exact (const_eval c p x).trans hv
  | inr j =>
    have hlt : acc.2.length < gs.length := by
      rcases diff_pass gs _ _ (initTab p, []) hok
        (show (pre (testIn true) p).length = _ by simp [pre,firstTen,initTab])
        (show (pre (testIn false) p).length = _ by simp [pre,firstTen,initTab])
        (start_diff p) with hs | hs
      · simpa [acc] using hs
      · obtain ⟨c,hc⟩ := hs o hh
        change acc.1.getD o (.inl false) = .inl c at hc
        rw [ho] at hc
        contradiction
    refine ⟨⟨acc.2,j⟩, elimPass_ok 11 gs _ (by simp), ?_, ?_⟩
    · change acc.2.length ≤ 12
      change (g :: k :: tail).length ≤ 15 at hsize
      simp only [List.length_cons] at hsize
      have ht : gs.length = tail.length := List.length_map _
      omega
    · intro x
      have hv := hval x
      rw [ho] at hv
      exact hv
