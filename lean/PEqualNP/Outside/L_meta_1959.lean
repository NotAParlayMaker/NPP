import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover

namespace PEqualNP.Outside.L_meta_1959_aux

-- The wire-table invariants and constant simplification are adapted from L-meta-551.
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

private lemma simplifyGate_mem_inputs_of_some (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ))
    (g : Gate) (hg : (simplifyGate op m ins).1 = some g) (w : ℕ) (hw : w ∈ g.inputs) :
    Sum.inr w ∈ ins := by
  cases op <;> simp only [simplifyGate] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg; simp at hw; rcases hw with rfl | rfl <;> simp
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg; simp at hw; rcases hw with rfl | rfl <;> simp
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg
    subst hg; simp at hw; subst hw; simp
  · simp at hg
  · simp at hg

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


private lemma simplifyGate_mono (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ))
    (hop : op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) :
    ∀ g ∈ (simplifyGate op m ins).1.toList,
      g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  have h : op = .and ∨ op = .or := by simpa using hop
  intro g hg
  rcases h with rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simplifyGate, simpAnd] at hg
    subst g
    simp
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simplifyGate, simpOr] at hg
    subst g
    simp

private lemma as_allowed (C : Circuit) (h : Monotone2 C) :
    ∀ g ∈ C.gates, OkGate g := by
  intro g hg
  obtain ⟨hop, hlen⟩ := h g hg
  refine ⟨?_, hlen⟩
  have hs : g.op = .and ∨ g.op = .or := by simpa using hop
  rcases hs with hs | hs <;> simp [hs]

private lemma elimPass_mono (n : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (h : Monotone2 ⟨gs, 0⟩) (ha : Monotone2 ⟨acc.2, 0⟩) :
    Monotone2 ⟨(elimPass n gs acc).2, 0⟩ := by
  induction gs generalizing acc with
  | nil => exact ha
  | cons g gs ih =>
    rw [elimPass_cons]
    apply ih
    · exact fun a ha => h a (List.mem_cons_of_mem _ ha)
    · intro a ham
      change a ∈ acc.2 ++ _ at ham
      rcases List.mem_append.mp ham with hh | hh
      · exact ha a hh
      · exact simplifyGate_mono _ _ _ (h g List.mem_cons_self).1 a hh

private lemma append_back (n : ℕ) (gs : List Gate) (o : Option Gate)
    (h : ReadsBack n ⟨gs, 0⟩)
    (ho : ∀ g ∈ o.toList, ∀ i ∈ g.inputs, i < n + gs.length) :
    ReadsBack n ⟨gs ++ o.toList, 0⟩ := by
  cases o with
  | none => simpa using h
  | some g =>
    intro j hj i hi
    change j < (gs ++ [g]).length at hj
    change i ∈ ((gs ++ [g]).getD j ⟨.or, []⟩).inputs at hi
    by_cases hj' : j < gs.length
    · rw [List.getD_append _ _ _ _ hj'] at hi
      exact h j hj' i hi
    · have he : j = gs.length := by simp at hj; omega
      subst j
      rw [getD_snoc_eq _ _ _ _ rfl] at hi
      exact ho g (by simp) i hi

private lemma elimPass_back (n : ℕ) (gs : List Gate) (win w : List Bool)
    (acc : List (Bool ⊕ ℕ) × List Gate) (hok : ∀ g ∈ gs, OkGate g)
    (hinv : ElimInv n win w acc) (ha : ReadsBack n ⟨acc.2, 0⟩) :
    ReadsBack n ⟨(elimPass n gs acc).2, 0⟩ := by
  induction gs generalizing w acc with
  | nil => exact ha
  | cons g gs ih =>
    rw [elimPass_cons]
    apply ih _ _ (fun a hap => hok a (List.mem_cons_of_mem _ hap))
      (elimInv_step _ _ _ _ _ (hok g List.mem_cons_self) hinv)
    unfold elimStep
    apply append_back _ _ _ ha
    intro a ham i hi
    have he : (simplifyGate g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = some a := by
      simpa using ham
    obtain ⟨j, _, hj⟩ := List.mem_map.mp (simplifyGate_mem_inputs_of_some _ _ _ a he i hi)
    have hv := (hinv.2.2 j).1
    rw [hj] at hv
    exact hv

private def shorten (g : Gate) : Gate :=
  match g.inputs with
  | [a,b] => if a = b then ⟨g.op, [a]⟩ else g
  | _ => g

private lemma shorten_op (g : Gate) : (shorten g).op = g.op := by
  unfold shorten
  split
  · split <;> rfl
  · rfl

private lemma shorten_len (g : Gate) : (shorten g).inputs.length ≤ g.inputs.length := by
  unfold shorten
  split
  · split <;> simp_all
  · exact le_rfl

private lemma shorten_reduces (g : Gate) (hl : g.inputs.length ≤ 2)
    (h : g.inputs.length < 2 ∨ g.inputs.getD 0 0 = g.inputs.getD 1 0) :
    (shorten g).inputs.length < 2 := by
  obtain ⟨op, ins⟩ := g
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
  · simp [shorten]
  · simp [shorten]
  · have h' : a = b := by simpa using h
    simp [shorten, h']
  · simp at hl

private lemma shorten_value (g : Gate) (h : g.op = .and ∨ g.op = .or) (w : List Bool) :
    (shorten g).op.eval ((shorten g).inputs.map fun i => w.getD i false) =
      g.op.eval (g.inputs.map fun i => w.getD i false) := by
  obtain ⟨op, ins⟩ := g
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
  · rfl
  · rfl
  · by_cases hab : a = b
    · subst b
      rcases h with rfl | rfl <;> simp [shorten, GateOp.eval]
    · simp [shorten, hab]
  · rfl

private lemma shorten_run (gs : List Gate) (w : List Bool) (h : Monotone2 ⟨gs, 0⟩) :
    wiresFrom (gs.map shorten) w = wiresFrom gs w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    have hop := (h g List.mem_cons_self).1
    rw [List.map_cons, wiresFrom_cons, wiresFrom_cons, shorten_value g (by simpa using hop)]
    exact ih _ (fun a ha => h a (List.mem_cons_of_mem _ ha))

private lemma elimPass_strict (n : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (h : Monotone2 ⟨gs, 0⟩) (hshort : ∃ g ∈ gs, g.inputs.length < 2) :
    (elimPass n gs acc).2.length < acc.2.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp at hshort
  | cons g gs ih =>
    rw [elimPass_cons, List.length_cons]
    have ht : Monotone2 ⟨gs, 0⟩ := fun a ha => h a (List.mem_cons_of_mem _ ha)
    let ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false)
    have hbound : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
      change (acc.2 ++ (simplifyGate g.op (n + acc.2.length) ins).1.toList).length ≤ _
      rw [List.length_append]
      exact Nat.add_le_add_left (toList_opt_len_le _) _
    obtain ⟨a, ha, hsa⟩ := hshort
    rcases List.mem_cons.mp ha with heq | ha
    · subst a
      have hlen : ins.length < 2 := by simpa [ins] using hsa
      have hop : g.op = .and ∨ g.op = .or := by simpa using (h g List.mem_cons_self).1
      have hn : (simplifyGate g.op (n + acc.2.length) ins).1 = none := by
        rcases hop with h' | h' <;>
          rcases ins with _ | ⟨b, _ | ⟨c, l⟩⟩ <;>
          (try cases b) <;> simp_all [simplifyGate, simpAnd, simpOr]
      have he : (elimStep n acc g).2.length = acc.2.length := by
        change (acc.2 ++ (simplifyGate g.op (n + acc.2.length) ins).1.toList).length = _
        simp [hn]
      have hb := elimPass_len n gs (elimStep n acc g)
      omega
    · have hb := ih (elimStep n acc g) ht ⟨a, ha, hsa⟩
      omega

private lemma elimInv_init (n : ℕ) (w : List Bool) (hw : w.length = n) :
    ElimInv n w w (List.ofFn (fun i : Fin n => Sum.inr (i : ℕ)), []) := by
  refine ⟨hw, by simp [hw], ?_⟩
  intro i
  by_cases hi : i < n
  · rw [ofFn_getD_lt _ _ _ hi]
    exact ⟨by simpa [statValid] using hi, rfl⟩
  · rw [List.getD_eq_default _ _ (by simp; omega),
        List.getD_eq_default _ _ (by omega)]
    exact ⟨trivial, rfl⟩

private theorem reduce {n : ℕ} (C : Circuit) (h : Monotone2 C)
    (hshort : ∃ g ∈ C.gates, g.inputs.length < 2 ∨ g.inputs.getD 0 0 = g.inputs.getD 1 0)
    (hnc : ∃ x y : Fin n → Bool, C.eval (List.ofFn x) ≠ C.eval (List.ofFn y)) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack n D ∧ D.size < C.size ∧
      ∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x) := by
  let gs := C.gates.map shorten
  have hm : Monotone2 ⟨gs, 0⟩ := by
    intro g hg
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hg
    exact ⟨by rw [shorten_op]; exact (h a ha).1, (shorten_len a).trans (h a ha).2⟩
  have hs : ∃ g ∈ gs, g.inputs.length < 2 := by
    obtain ⟨g, hg, hbad⟩ := hshort
    exact ⟨shorten g, List.mem_map_of_mem hg, shorten_reduces g (h g hg).2 hbad⟩
  let init : List (Bool ⊕ ℕ) × List Gate :=
    (List.ofFn (fun i : Fin n => Sum.inr (i : ℕ)), [])
  let acc := elimPass n gs init
  have hval (x : Fin n → Bool) :
      statVal (wiresFrom acc.2 (List.ofFn x)) (acc.1.getD C.output (Sum.inl false)) =
        C.eval (List.ofFn x) := by
    have hv := ((elimInv_pass n (List.ofFn x) gs _ init (as_allowed ⟨gs, 0⟩ hm)
      (elimInv_init n _ List.length_ofFn)).2.2 C.output).2
    change _ = (wiresFrom C.gates (List.ofFn x)).getD C.output false
    rw [← shorten_run C.gates _ (show Monotone2 ⟨C.gates, 0⟩ from h)]
    exact hv
  cases ho : acc.1.getD C.output (Sum.inl false) with
  | inl b =>
    obtain ⟨x, y, hxy⟩ := hnc
    have hx := hval x
    have hy := hval y
    rw [ho] at hx hy
    exact (hxy (hx.symm.trans hy)).elim
  | inr i =>
    refine ⟨⟨acc.2, i⟩, ?_, ?_, ?_, ?_⟩
    · exact elimPass_mono n gs init hm (by intro g hg; simp [init] at hg)
    · exact elimPass_back n gs (List.replicate n false) _ init (as_allowed ⟨gs, 0⟩ hm)
        (elimInv_init n _ (by simp)) (by intro j hj; simp [init] at hj)
    · simpa [Circuit.size, acc, gs, init] using elimPass_strict n gs init hm hs
    · intro x
      have hx := hval x
      rw [ho] at hx
      exact hx

private lemma asInput (w : List Bool) {n : ℕ} (hw : w.length = n) :
    ∃ x : Fin n → Bool, List.ofFn x = w := by
  subst n
  exact ⟨w.get, List.ofFn_get w⟩

end PEqualNP.Outside.L_meta_1959_aux


theorem PEqualNP.Outside.L_meta_1959 :
    have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => (∀ (x3 x4 : Fin (13 : ℕ)), x3 - x4 ∈ x1 → x2.eval ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x4)) = Bool.true) ∧ ∀ (x3 : Finset (Fin (13 : ℕ))), x3.card = (4 : ℕ) → (∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x3 | x6 - x5 ∈ x1}.card ≤ (2 : ℕ)) → x2.eval ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 ∈ x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (∀ x7 ∈ x3, x7 - x6 ∉ x1)) = Bool.false; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => ∃ (x4 : ℕ) (x5 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x5).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x3 x4 x5; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x4 → x2 x4 → x4.size < (64 : ℕ) → x3 x4 → (∃ x10 ∈ x4.gates, x10.inputs.length < (2 : ℕ) ∨ x10.inputs.getD (0 : ℕ) (0 : ℕ) = x10.inputs.getD (1 : ℕ) (0 : ℕ)) → ∃ (x11 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x11 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x11 ∧ x2 x11 ∧ x11.size < x4.size := by
  intro δ Fits _ C hmono _ hfit _ _ hshort
  let q : Finset (Fin 13) := {0, 1, 2, 5}
  let yes := List.ofFn (fun p : Fin 13 => decide (p = 0)) ++
    List.ofFn (fun l : Fin 13 => decide (l = 0))
  let no := List.ofFn (fun p : Fin 13 => decide (p ∈ q)) ++
    List.ofFn (fun l : Fin 13 => decide (∀ p ∈ q, p - l ∉ δ))
  have htrue : C.eval yes = true := hfit.1 0 0 (by decide)
  have hfalse : C.eval no = false := hfit.2 q (by decide) (by decide)
  have hnc : ∃ x y : Fin 26 → Bool, C.eval (List.ofFn x) ≠ C.eval (List.ofFn y) := by
    obtain ⟨x, hx⟩ := L_meta_1959_aux.asInput yes (by simp [yes] : yes.length = 26)
    obtain ⟨y, hy⟩ := L_meta_1959_aux.asInput no (by simp [no] : no.length = 26)
    exact ⟨x, y, by rw [hx, hy, htrue, hfalse]; decide⟩
  obtain ⟨D, hD, hback, hlt, heval⟩ := L_meta_1959_aux.reduce C hmono hshort hnc
  have he (w : List Bool) (hw : w.length = 26) : D.eval w = C.eval w := by
    obtain ⟨x, hx⟩ := L_meta_1959_aux.asInput w hw
    rw [← hx]
    exact heval x
  refine ⟨D, hD, hback, ⟨?_, ?_⟩, hlt⟩
  · intro p l hp
    rw [he _ (by simp)]
    exact hfit.1 p l hp
  · intro S hS hline
    rw [he _ (by simp)]
    exact hfit.2 S hS hline

