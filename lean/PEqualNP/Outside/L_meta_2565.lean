import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2565_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Constant propagation follows L_meta_468 and L_meta_2315.
-- Both the raw input at position four and the supplied product at position nine become false.
-- Two distinct normalized gates read these wires and disappear after the restriction.

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

def normGate (g : Gate) : Gate :=
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

private lemma ofFn_getD_lt {α : Type*} {m : ℕ} (f : Fin m → α) (d : α) (i : ℕ) (hi : i < m) :
    (List.ofFn f).getD i d = f ⟨i, hi⟩ := by
  rw [List.getD_eq_getElem _ _ (by simp; exact hi), List.getElem_ofFn]


private abbrev readsClamped (g : Gate) := decide (4 ∈ g.inputs ∨ 9 ∈ g.inputs)

private theorem savedCount (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (hok : ∀ g ∈ gs, NOkGate g)
    (h4 : acc.1.getD 4 (.inl false) = .inl false)
    (h9 : acc.1.getD 9 (.inl false) = .inl false)
    (hlen : 9 < acc.1.length) :
    (elimPass 8 gs acc).2.length + (gs.filter readsClamped).length ≤ acc.2.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp [elimPass]
  | cons g gs ih =>
    let next := elimStep 8 acc g
    have keeps (j : ℕ) (hj : j < acc.1.length) :
        next.1.getD j (.inl false) = acc.1.getD j (.inl false) := by
      exact getD_snoc_lt _ _ _ _ hj
    have bound := ih next (fun k hk => hok k (List.mem_cons_of_mem _ hk))
      ((keeps 4 (by omega)).trans h4) ((keeps 9 hlen).trans h9)
      (by simp [next, elimStep]; omega)
    rw [elimPass_cons]
    change (elimPass 8 gs next).2.length + _ ≤ _
    have valid := hok g List.mem_cons_self
    by_cases hits : 4 ∈ g.inputs ∨ 9 ∈ g.inputs
    · have gone : (simplifyGate g.op (8 + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (.inl false))).1 = none := by
        apply simplifyGate_none_of_const _ _ _ valid.1.1 (by simpa using valid.1.2)
          (fun h => by simpa using valid.2 h)
        refine ⟨false, List.mem_map.mpr ?_⟩
        rcases hits with h|h
        · exact ⟨4,h,h4⟩
        · exact ⟨9,h,h9⟩
      have stepLen : next.2.length = acc.2.length := by simp only [next, elimStep, gone, Option.toList_none, List.append_nil]
      simp only [List.filter_cons, readsClamped, hits, decide_true, ↓reduceIte,
        List.length_cons] at *
      omega
    · have stepLen : next.2.length ≤ acc.2.length + 1 := by
        simp only [next, elimStep, List.length_append]
        exact Nat.add_le_add_left (toList_opt_len_le _) _
      simp only [List.filter_cons, readsClamped, hits, decide_false, Bool.false_eq_true,
        ↓reduceIte, List.length_cons] at *
      omega

def insertFalse (x : Fin 8 → Bool) : Fin 9 → Bool :=
  ![x 0,x 1,x 2,x 3,false,x 4,x 5,x 6,x 7]

private def seedRefs : List (Bool ⊕ ℕ) :=
  [.inr 0,.inr 1,.inr 2,.inr 3,.inl false,.inr 4,.inr 5,.inr 6,.inr 7,.inl false]

private theorem initial (x : Fin 8 → Bool) :
    ElimInv 8 (List.ofFn x) (List.ofFn (insertFalse x) ++ [false]) (seedRefs, []) := by
  refine ⟨by simp, by simp [seedRefs], ?_⟩
  intro i
  by_cases h : i < 10
  · have finiteCase (k : Fin 10) : statValid 8 (seedRefs.getD k.val (.inl false)) ∧
        statVal (List.ofFn x) (seedRefs.getD k.val (.inl false)) =
          (List.ofFn (insertFalse x) ++ [false]).getD k.val false := by
      fin_cases k <;> refine ⟨?_, rfl⟩ <;> first | exact True.intro | (change _ < (8 : ℕ); decide)
    exact finiteCase ⟨i,h⟩
  · rw [List.getD_eq_default seedRefs _ (by simpa [seedRefs] using Nat.le_of_not_gt h),
        List.getD_eq_default (List.ofFn (insertFalse x) ++ [false]) _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

theorem eliminateTwo (C : Circuit) (fan : FanInTwo C)
    (F : (Fin 8 → Bool) → Bool)
    (ev : ∀ x, C.eval (List.ofFn (insertFalse x) ++ [false]) = F x)
    (nonconstant : ∃ x y, F x ≠ F y)
    (two : 2 ≤ ((C.gates.map normGate).filter (fun g => decide (4 ∈ g.inputs ∨ 9 ∈ g.inputs))).length) :
    HasCircuitSize 8 F (C.size - 2) := by
  let gs := C.gates.map normGate
  have valid : ∀ g ∈ gs, NOkGate g := by
    intro g hg
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hg
    exact normGate_nok k (fan k hk)
  let acc := elimPass 8 gs (seedRefs, [])
  have saved := savedCount gs (seedRefs,[]) valid rfl rfl (by decide)
  change acc.2.length + (gs.filter readsClamped).length ≤ 0 + gs.length at saved
  change 2 ≤ (gs.filter readsClamped).length at two
  have len : gs.length = C.size := by simp [gs, Circuit.size]
  have hval (x : Fin 8 → Bool) :
      statVal (wiresFrom acc.2 (List.ofFn x)) (acc.1.getD C.output (.inl false)) = F x := by
    have inv := elimInv_pass 8 (List.ofFn x) gs _ (seedRefs,[])
      (fun g hg => (valid g hg).1) (initial x)
    rw [(inv.2.2 C.output).2]
    dsimp only [gs]
    rw [wiresFrom_norm]
    exact ev x
  cases e : acc.1.getD C.output (.inl false) with
  | inl b =>
    obtain ⟨x,y,ne⟩ := nonconstant
    have hx := hval x
    have hy := hval y
    rw [e] at hx hy
    exact False.elim (ne (hx.symm.trans hy))
  | inr k =>
    refine ⟨⟨acc.2,k⟩, elimPass_ok 8 gs _ (by simp), ?_, ?_⟩
    · show acc.2.length ≤ C.size - 2
      omega
    · intro x
      have h := hval x
      rw [e] at h
      exact h

abbrev sourceEdge (x : Fin 9 → Bool) :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 ||
  x 5 && x 7 || x 6 && x 8 || x 8 && x 5

abbrev targetEdge (x : Fin 8 → Bool) :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 0 && x 4 ||
  x 1 && x 5 || x 2 && x 6 || x 3 && x 7 || x 4 && x 6 ||
  x 5 && x 7 || x 7 && x 4



private lemma agree_except_four (gs : List Gate)
    (all4 : ∀ g ∈ gs, 4 ∈ g.inputs → g.op = GateOp.and ∧ 9 ∈ g.inputs)
    (u v : List Bool) (len : u.length = v.length) (long : 9 < u.length)
    (z : u.getD 9 false = false) (z' : v.getD 9 false = false)
    (agree : ∀ i : ℕ, i ≠ 4 → u.getD i false = v.getD i false) :
    ∀ i : ℕ, i ≠ 4 → (wiresFrom gs u).getD i false = (wiresFrom gs v).getD i false := by
  induction gs generalizing u v with
  | nil => exact agree
  | cons g gs ih =>
    let run (w : List Bool) := g.op.eval (g.inputs.map fun i => w.getD i false)
    have same : run u = run v := by
      by_cases h4 : 4 ∈ g.inputs
      · obtain ⟨hop,h9⟩ := all4 g (by simp) h4
        have zero (w : List Bool) (hz : w.getD 9 false = false) : run w = false := by
          rw [show run w = GateOp.and.eval (g.inputs.map fun i => w.getD i false) by simp [run, hop]]
          simp only [GateOp.eval, List.all_map]
          apply Bool.eq_false_iff.mpr
          intro h
          have t := (List.all_eq_true.mp h) 9 h9
          change w.getD 9 false = true at t
          rw [hz] at t
          contradiction
        rw [zero u z, zero v z']
      · have heq : (g.inputs.map fun i => u.getD i false) = (g.inputs.map fun i => v.getD i false) := by
          apply List.map_congr_left
          intro i hi
          exact agree i (fun eq => h4 (eq ▸ hi))
        exact congrArg g.op.eval heq
    change ∀ i, i ≠ 4 → (wiresFrom gs (u ++ [run u])).getD i false = (wiresFrom gs (v ++ [run v])).getD i false
    apply ih (fun q h => all4 q (by simp [h])) _ _ (by simp [len]) (by simp; omega)
       (by rw [getD_snoc_lt _ _ _ _ long]; exact z)
       (by rw [getD_snoc_lt _ _ _ _ (by omega)]; exact z')
    intro i h
    rw [same]
    by_cases lo : i < u.length
    · rw [getD_snoc_lt _ _ _ _ lo, getD_snoc_lt _ _ _ _ (by omega)]
      exact agree i h
    · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), len]

private lemma count_forced_readers (C : Circuit)
    (hand : ∃ g ∈ C.gates, g.op = GateOp.and ∧ 9 ∈ g.inputs)
    (correct : ∀ (x4 : Fin (9 : ℕ) → Bool), C.eval (List.ofFn x4 ++ [x4 (4 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ))]) = (x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)))) :
    2 ≤ ((C.gates.map normGate).filter (fun g => decide (4 ∈ g.inputs ∨ 9 ∈ g.inputs))).length := by
  let seed (x : Fin 9 → Bool) := List.ofFn x ++ [x 4 && x 6]
  let l : Fin 9 → Bool := fun i => decide (i = 3)
  let h : Fin 9 → Bool := fun i => decide (i = 3 ∨ i = 4)
  let s : Fin 9 → Bool := fun i => decide (i = 4)
  have elim0 : C.eval (seed l) = false := (correct l).trans (by decide)
  have elim1 : C.eval (seed h) = true := (correct h).trans (by decide)
  have elimS : C.eval (seed s) = false := (correct s).trans (by decide)
  have hout : C.output ≠ 4 := by
    intro heq
    change (wiresFrom C.gates (seed s)).getD C.output false = false at elimS
    rw [heq, wiresFrom_getD_lt _ _ _ (by decide)] at elimS
    exact (by decide : (seed s).getD 4 false ≠ false) elimS
  let gs := C.gates.map normGate
  have pick : ∃ q ∈ gs, 4 ∈ q.inputs ∧ ¬(q.op = GateOp.and ∧ 9 ∈ q.inputs) := by
    by_contra! no
    have ag := agree_except_four gs (fun g hg h4 => by simpa [not_and_or] using no g hg h4)
      (seed l) (seed h) (by decide) (by decide)
      (by decide) (by decide) (by
        intro i hi
        by_cases lt : i < 10
        · have z : ∀ t : Fin 10, t.val ≠ 4 → (seed l).getD t.val false = (seed h).getD t.val false := by decide
          exact z ⟨i, lt⟩ hi
        · rw [List.getD_eq_default _ _ (by simp [seed]; omega), List.getD_eq_default _ _ (by simp [seed]; omega)])
      C.output hout
    change (wiresFrom (C.gates.map normGate) (seed l)).getD C.output false = (wiresFrom (C.gates.map normGate) (seed h)).getD C.output false at ag
    rw [wiresFrom_norm, wiresFrom_norm] at ag
    change C.eval (seed l) = C.eval (seed h) at ag
    rw [elim0,elim1] at ag
    contradiction
  obtain ⟨v, hv, read4, notAnd⟩ := pick
  obtain ⟨g, hg, op, read9⟩ := hand
  have heq : normGate g = g := by simp [normGate,op]
  have included : g ∈ gs := by
    change g ∈ C.gates.map normGate
    exact List.mem_map.mpr ⟨g,hg,heq⟩
  let filtered := gs.filter (fun g => decide (4 ∈ g.inputs ∨ 9 ∈ g.inputs))
  have a : g ∈ filtered := List.mem_filter.mpr ⟨included, decide_eq_true (.inr read9)⟩
  have b : v ∈ filtered := List.mem_filter.mpr ⟨hv, decide_eq_true (.inl read4)⟩
  have diff : g ≠ v := fun eq => notAnd (eq ▸ And.intro op read9)
  have two {xs : List Gate} {x y : Gate} (a : x ∈ xs) (b : y ∈ xs) (ne : x ≠ y) : 2 ≤ xs.length := by
    cases xs with
    | nil => simp at a
    | cons head tl =>
      cases tl with
      | nil =>
        simp only [List.mem_singleton] at a b
        exact (ne (a.trans b.symm)).elim
      | cons next rest => simp
  exact two a b diff

theorem restrictedEdge (C : Circuit)
    (correct : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 4 && x 6]) = sourceEdge x)
    (x : Fin 8 → Bool) : C.eval (List.ofFn (insertFalse x) ++ [false]) = targetEdge x := by
  have h := correct (insertFalse x)
  change C.eval (List.ofFn (insertFalse x) ++ [false]) = _ at h
  rw [h]
  change (((((((((((x 0 && x 1 || x 1 && x 2) || x 2 && x 3) || x 3 && false) ||
    false && x 0) || x 0 && x 4) || x 1 && x 5) || x 2 && x 6) || x 3 && x 7) ||
    x 4 && x 6) || x 5 && x 7) || x 7 && x 4) = _
  simp only [Bool.and_false, Bool.false_and, Bool.or_false]

theorem restrictedNonconstant : ∃ x y : Fin 8 → Bool, targetEdge x ≠ targetEdge y := by
  exact ⟨fun _ => false, fun _ => true, by decide⟩


end PEqualNP.Outside.L_meta_2565_aux

theorem PEqualNP.Outside.L_meta_2565 :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∃ x3 ∈ x1.gates, x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (9 : ℕ) ∈ x3.inputs) → (∀ (x4 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x4 ++ [x4 (4 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ))]) = (x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)))) → PEqualNP.MetaComplexity.HasCircuitSize (8 : ℕ) (fun (x5 : Fin (8 : ℕ) → Bool) => x5 (0 : Fin (8 : ℕ)) && x5 (1 : Fin (8 : ℕ)) || x5 (1 : Fin (8 : ℕ)) && x5 (2 : Fin (8 : ℕ)) || x5 (2 : Fin (8 : ℕ)) && x5 (3 : Fin (8 : ℕ)) || x5 (0 : Fin (8 : ℕ)) && x5 (4 : Fin (8 : ℕ)) || x5 (1 : Fin (8 : ℕ)) && x5 (5 : Fin (8 : ℕ)) || x5 (2 : Fin (8 : ℕ)) && x5 (6 : Fin (8 : ℕ)) || x5 (3 : Fin (8 : ℕ)) && x5 (7 : Fin (8 : ℕ)) || x5 (4 : Fin (8 : ℕ)) && x5 (6 : Fin (8 : ℕ)) || x5 (5 : Fin (8 : ℕ)) && x5 (7 : Fin (8 : ℕ)) || x5 (7 : Fin (8 : ℕ)) && x5 (4 : Fin (8 : ℕ))) (x1.size - (2 : ℕ)) := by
  intro C fan hand correct
  exact PEqualNP.Outside.L_meta_2565_aux.eliminateTwo C fan PEqualNP.Outside.L_meta_2565_aux.targetEdge
    (PEqualNP.Outside.L_meta_2565_aux.restrictedEdge C correct)
    PEqualNP.Outside.L_meta_2565_aux.restrictedNonconstant
    (PEqualNP.Outside.L_meta_2565_aux.count_forced_readers C hand correct)
