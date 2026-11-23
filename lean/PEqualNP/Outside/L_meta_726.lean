import Mathlib
import PEqualNP.Defs

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

private def MonoGate (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

private lemma monoGate_nok (g : Gate) (h : MonoGate g) : NOkGate g := by
  rcases g with ⟨op, inputs⟩
  simp only [MonoGate, Set.mem_insert_iff, Set.mem_singleton_iff] at h
  rcases h with ⟨(rfl | rfl), hlen⟩
  · exact ⟨⟨by simp [OkGate], hlen⟩, by simp⟩
  · exact ⟨⟨by simp [OkGate], hlen⟩, by simp⟩

private lemma monoGate_ok (g : Gate) (h : MonoGate g) : OkGate g := (monoGate_nok g h).1

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

private lemma simplifyGate_mono (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ))
    (hop : op = GateOp.and ∨ op = GateOp.or) :
    ∀ g ∈ (simplifyGate op m ins).1.toList, MonoGate g := by
  intro g hg
  rcases hop with rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simplifyGate, simpAnd] at hg
    subst hg
    simp [MonoGate]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simplifyGate, simpOr] at hg
    subst hg
    simp [MonoGate]

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

private lemma elimPass_mono (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (h : ∀ g ∈ acc.2, MonoGate g) (hgs : ∀ g ∈ gs, MonoGate g) :
    ∀ g ∈ (elimPass m gs acc).2, MonoGate g := by
  induction gs generalizing acc with
  | nil => exact h
  | cons g gs ih =>
      rw [elimPass_cons]
      apply ih
      · intro g' hg'
        simp only [elimStep] at hg'
        rcases List.mem_append.1 hg' with h1 | h1
        · exact h g' h1
        · have hgmono := hgs g List.mem_cons_self
          have hop : g.op = GateOp.and ∨ g.op = GateOp.or := by
            simpa [MonoGate, Set.mem_insert_iff, Set.mem_singleton_iff] using hgmono.1
          exact simplifyGate_mono g.op (m + acc.2.length)
            (g.inputs.map fun i => acc.1.getD i (Sum.inl false)) hop g' h1
      · intro g' hg'
        exact hgs g' (List.mem_cons_of_mem _ hg')

private lemma elimPass_len_const (m k : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (hok : ∀ g ∈ gs, NOkGate g) (hk : k < acc.1.length)
    (hc : ∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c) :
    (elimPass m gs acc).2.length + (gs.filter (fun g => decide (k ∈ g.inputs))).length ≤
      acc.2.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp [elimPass]
  | cons g gs ih =>
      rw [elimPass_cons]
      simp only [List.length_cons]
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
        have h1 := ih (elimStep m acc g)
          (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
          (by simp [elimStep]; omega)
          ⟨c, by simp only [elimStep]; rw [getD_snoc_lt _ _ _ _ hk]; exact hc⟩
        simp [hkg]
        omega
      · have h2 : (elimStep m acc g).2.length ≤ acc.2.length + 1 := by
          simp only [elimStep, List.length_append]
          have := toList_opt_len_le (simplifyGate g.op (m + acc.2.length)
            (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
          omega
        have h1 := ih (elimStep m acc g)
          (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
          (by simp [elimStep]; omega)
          (by
            obtain ⟨c, hc⟩ := hc
            exact ⟨c, by simp only [elimStep]; rw [getD_snoc_lt _ _ _ _ hk]; exact hc⟩)
        simp [hkg]
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

private lemma card_filter_get {α : Type*} (p : α → Prop) [DecidablePred p]
    (l : List α) :
    (Finset.univ.filter (fun j : Fin l.length => p (l.get j))).card =
      (l.filter (fun a => decide (p a))).length := by
  induction l with
  | nil => simp
  | cons a l ih =>
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
      simp only [List.length_cons]
      rw [Fin.sum_univ_succ]
      simp_rw [show ∀ i : Fin l.length, (a :: l).get i.succ = l.get i by intro i; simp]
      have ihsum : (∑ i : Fin l.length, if p (l.get i) then 1 else 0) =
          (l.filter (fun a => decide (p a))).length := by
        rw [← Finset.sum_filter, ← Finset.card_eq_sum_ones]
        exact ih
      rw [ihsum]
      by_cases hpa : p a <;> simp [List.filter, hpa, Nat.add_comm]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem L_meta_726 :
    ∀ (n : ℕ) (C : Circuit) (v : Fin n) (b : Bool), Monotone2 C →
      (∃ y : Fin n → Bool, C.eval (List.ofFn (Function.update y v b)) = false) →
      ∃ D : Circuit, Monotone2 D ∧
        D.size + (Finset.univ.filter (fun j : Fin C.gates.length => v.val ∈ (C.gates.get j).inputs)).card ≤ C.size ∧
        ∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn (Function.update x v b)) := by
  intro n C v b hmono hex
  classical
  have hgmono : ∀ g ∈ C.gates, MonoGate g := by
    intro g hg
    exact hmono g hg
  have hnok : ∀ g ∈ C.gates, NOkGate g := by
    intro g hg
    exact monoGate_nok g (hgmono g hg)
  set acc := elimPass n C.gates (initVar n v b, []) with hacc
  have hklt : v.val < (initVar n v b).length := by simp [initVar]
  have hcst : ∃ c, (initVar n v b).getD v.val (Sum.inl false) = Sum.inl c := by
    refine ⟨b, ?_⟩
    rw [initVar, ofFn_getD_lt _ _ _ v.isLt]
    simp
  have hlen : acc.2.length + (C.gates.filter (fun g => decide (v.val ∈ g.inputs))).length ≤ C.gates.length := by
    have := elimPass_len_const n v.val C.gates (initVar n v b, []) hnok hklt hcst
    rw [← hacc] at this
    simpa using this
  have hval : ∀ x : Fin n → Bool,
      statVal (wiresFrom acc.2 (List.ofFn x)) (acc.1.getD C.output (Sum.inl false)) =
        C.eval (List.ofFn (Function.update x v b)) := by
    intro x
    have hinv := elimInv_pass n (List.ofFn x) C.gates (List.ofFn (Function.update x v b))
      (initVar n v b, [])
      (fun g hg => monoGate_ok g (hgmono g hg))
      (elimInv_initVar n v b x)
    rw [← hacc] at hinv
    rw [(hinv.2.2 C.output).2]
    rfl
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
      have hcfalse : c = false := by
        obtain ⟨y, hy⟩ := hex
        have hyval := hval y
        rw [hst] at hyval
        simpa [statVal] using hyval.trans hy
      refine ⟨{ gates := [], output := n }, ?_, ?_, ?_⟩
      · intro g hg
        simp at hg
      · simp only [Circuit.size, List.length_nil, Nat.zero_add]
        rw [card_filter_get (fun g : Gate => v.val ∈ g.inputs) C.gates]
        omega
      · intro x
        have hxval := hval x
        rw [hst] at hxval
        have hxfalse : C.eval (List.ofFn (Function.update x v b)) = false := by
          simpa [statVal, hcfalse] using hxval.symm
        have hDfalse : ({ gates := [], output := n } : Circuit).eval (List.ofFn x) = false := by
          simp [Circuit.eval, Circuit.wires, List.getD]
        rw [hDfalse, hxfalse]
  | inr j =>
      refine ⟨{ gates := acc.2, output := j }, ?_, ?_, ?_⟩
      · have hmono_acc : ∀ g ∈ acc.2, MonoGate g := by
          rw [hacc]
          exact elimPass_mono n C.gates (initVar n v b, []) (by simp) hgmono
        simpa [Monotone2, MonoGate] using hmono_acc
      · simp only [Circuit.size]
        rw [card_filter_get (fun g : Gate => v.val ∈ g.inputs) C.gates]
        simpa using hlen
      · intro x
        have hxval := hval x
        rw [hst] at hxval
        simpa [statVal, Circuit.eval, Circuit.wires, wiresFrom] using hxval
