import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_529_aux

open PEqualNP.CircuitLowerBounds

private def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

private lemma wiresFrom_nil (w : List Bool) : wiresFrom [] w = w := rfl

private lemma wiresFrom_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wiresFrom (g :: gs) w =
      wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

private lemma wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) :=
  List.foldl_append

private lemma wiresFrom_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [wiresFrom]
  | cons g gs ih =>
    rw [wiresFrom_cons, ih]
    simp; omega

private lemma getD_snoc_lt {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i < l.length) :
    (l ++ [x]).getD i d = l.getD i d :=
  List.getD_append l [x] d i hi

private lemma getD_snoc_eq {α : Type*} (l : List α) (x d : α) :
    (l ++ [x]).getD l.length d = x := by
  simp

private lemma getD_snoc_gt {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : l.length < i) :
    (l ++ [x]).getD i d = d := by
  rw [List.getD_eq_default]
  simp; omega

private lemma wiresFrom_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [wiresFrom_cons, ih _ (by simp; omega), getD_snoc_lt _ _ _ _ hi]

private lemma wiresFrom_take_getD {gs : List Gate} {w : List Bool} {k i : ℕ}
    (hi : i < w.length + k) :
    (wiresFrom (gs.take k) w).getD i false = (wiresFrom gs w).getD i false := by
  by_cases hk : k ≤ gs.length
  · have hsplit : gs = gs.take k ++ gs.drop k := (List.take_append_drop k gs).symm
    conv_rhs => rw [hsplit, wiresFrom_append]
    symm
    rw [wiresFrom_getD_lt]
    rw [wiresFrom_length, List.length_take]
    omega
  · rw [List.take_of_length_le (by omega)]

private def MonGate (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

private def isBinAnd (g : Gate) : Bool :=
  match g.op, g.inputs with
  | GateOp.and, [_, _] => true
  | _, _ => false

private def isBinOr (g : Gate) : Bool :=
  match g.op, g.inputs with
  | GateOp.or, [_, _] => true
  | _, _ => false

private lemma gate_eval_mono {g : Gate} (hg : MonGate g) {f₁ f₂ : ℕ → Bool}
    (hle : ∀ i, f₁ i = true → f₂ i = true) :
    g.op.eval (g.inputs.map f₁) = true → g.op.eval (g.inputs.map f₂) = true := by
  rcases hg.1 with hop | hop
  · rw [hop]
    simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq]
    intro h b hb
    rcases hb with ⟨i, hi, rfl⟩
    exact hle i (h (f₁ i) ⟨i, hi, rfl⟩)
  · rw [hop]
    simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
    rintro ⟨_, ⟨i, hi, rfl⟩, h1⟩
    exact ⟨f₂ i, ⟨i, hi, rfl⟩, hle i h1⟩

private lemma wiresFrom_mono {gs : List Gate} (hgs : ∀ g ∈ gs, MonGate g)
    {w₁ w₂ : List Bool} (hlen : w₁.length = w₂.length)
    (hle : ∀ i, w₁.getD i false = true → w₂.getD i false = true) :
    ∀ i, (wiresFrom gs w₁).getD i false = true → (wiresFrom gs w₂).getD i false = true := by
  induction gs generalizing w₁ w₂ with
  | nil => exact hle
  | cons g gs ih =>
    have hg : MonGate g := hgs g (List.mem_cons_self ..)
    have hgs' : ∀ g' ∈ gs, MonGate g' := fun g' hg' => hgs g' (List.mem_cons_of_mem g hg')
    apply ih hgs' (by simp [hlen])
    intro i hi
    rcases lt_trichotomy i w₁.length with hlt | rfl | hgt
    · rw [getD_snoc_lt _ _ _ _ hlt] at hi
      rw [getD_snoc_lt _ _ _ _ (by omega)]
      exact hle i hi
    · rw [getD_snoc_eq] at hi
      rw [hlen, getD_snoc_eq]
      exact gate_eval_mono hg hle hi
    · rw [getD_snoc_gt _ _ _ _ hgt] at hi
      cases hi

private lemma wiresFrom_replace_le {gs₁ gs₂ : List Gate} {g g' : Gate}
    (hgs₂ : ∀ h ∈ gs₂, MonGate h) {w : List Bool}
    (hle : g'.op.eval (g'.inputs.map fun i => (wiresFrom gs₁ w).getD i false) = true →
           g.op.eval (g.inputs.map fun i => (wiresFrom gs₁ w).getD i false) = true) :
    ∀ i, (wiresFrom (gs₁ ++ g' :: gs₂) w).getD i false = true →
         (wiresFrom (gs₁ ++ g :: gs₂) w).getD i false = true := by
  rw [wiresFrom_append, wiresFrom_append, wiresFrom_cons, wiresFrom_cons]
  apply wiresFrom_mono hgs₂ (by simp)
  intro i hi
  rcases lt_trichotomy i (wiresFrom gs₁ w).length with hlt | rfl | hgt
  · rw [getD_snoc_lt _ _ _ _ hlt] at hi ⊢; exact hi
  · rw [getD_snoc_eq] at hi ⊢; exact hle hi
  · rw [getD_snoc_gt _ _ _ _ hgt] at hi; cases hi

private lemma wiresFrom_replace_eq {gs₁ gs₂ : List Gate} {g g' : Gate} {w : List Bool}
    (heq : g'.op.eval (g'.inputs.map fun i => (wiresFrom gs₁ w).getD i false) =
           g.op.eval (g.inputs.map fun i => (wiresFrom gs₁ w).getD i false)) :
    wiresFrom (gs₁ ++ g' :: gs₂) w = wiresFrom (gs₁ ++ g :: gs₂) w := by
  rw [wiresFrom_append, wiresFrom_append, wiresFrom_cons, wiresFrom_cons, heq]

private def wireVal {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (wiresFrom gs (List.ofFn x)).getD i false

private def zeroIn (n : ℕ) : Fin n → Bool := fun _ => false

private def unitIn {n : ℕ} (v : Fin n) : Fin n → Bool := fun u => decide (u = v)

private def maxZero {n : ℕ} (T : Finset (Fin n)) : Fin n → Bool := fun u => decide (u ∉ T)

private def supp (n : ℕ) (gs : List Gate) (i : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun v => wireVal gs (unitIn v) i = true)

private lemma ofFn_getD_lt {n : ℕ} (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    (List.ofFn x).getD i false = x ⟨i, hi⟩ := by
  rw [List.getD_eq_getElem _ _ (by simp; exact hi), List.getElem_ofFn]

private lemma wireVal_input {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    wireVal gs x i = x ⟨i, hi⟩ := by
  rw [wireVal, wiresFrom_getD_lt _ _ _ (by simp; exact hi), ofFn_getD_lt x i hi]

private lemma wireVal_ge {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ)
    (hi : n + gs.length ≤ i) :
    wireVal gs x i = false := by
  rw [wireVal, List.getD_eq_default]
  rw [wiresFrom_length, List.length_ofFn]
  exact hi

private lemma wireVal_mono {n : ℕ} {gs : List Gate} (hgs : ∀ g ∈ gs, MonGate g)
    {x y : Fin n → Bool} (hxy : ∀ v, x v = true → y v = true) (i : ℕ) :
    wireVal gs x i = true → wireVal gs y i = true := by
  apply wiresFrom_mono hgs (by simp)
  intro j hj
  by_cases hlt : j < n
  · rw [ofFn_getD_lt x j hlt] at hj
    rw [ofFn_getD_lt y j hlt]
    exact hxy ⟨j, hlt⟩ hj
  · rw [List.getD_eq_default _ _ (by simp; omega)] at hj
    cases hj

private lemma wireVal_take {n : ℕ} (gs : List Gate) (x : Fin n → Bool) {k i : ℕ}
    (hi : i < n + k) :
    wireVal (gs.take k) x i = wireVal gs x i := by
  unfold wireVal
  exact wiresFrom_take_getD (by simp; exact hi)

private lemma supp_take {n : ℕ} (gs : List Gate) {k i : ℕ} (hi : i < n + k) :
    supp n (gs.take k) i = supp n gs i := by
  ext v
  simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and, wireVal_take gs _ hi]

private lemma wireVal_snoc_last {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) :
    wireVal (gs ++ [g]) x (n + gs.length) =
      g.op.eval (g.inputs.map fun i => wireVal gs x i) := by
  unfold wireVal
  rw [wiresFrom_append, wiresFrom_cons, wiresFrom_nil]
  have hlen : (wiresFrom gs (List.ofFn x)).length = n + gs.length := by
    rw [wiresFrom_length, List.length_ofFn]
  rw [← hlen, getD_snoc_eq]

private lemma wireVal_snoc_lt {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool)
    {i : ℕ} (hi : i < n + gs.length) :
    wireVal (gs ++ [g]) x i = wireVal gs x i := by
  unfold wireVal
  rw [wiresFrom_append, wiresFrom_cons, wiresFrom_nil]
  have hlen : (wiresFrom gs (List.ofFn x)).length = n + gs.length := by
    rw [wiresFrom_length, List.length_ofFn]
  rw [getD_snoc_lt _ _ _ _ (by omega)]

private lemma mem_supp_iff {n : ℕ} (gs : List Gate) (i : ℕ) (v : Fin n) :
    v ∈ supp n gs i ↔ wireVal gs (unitIn v) i = true := by
  simp [supp]

private lemma orOnly_wire_char {n : ℕ} :
    ∀ (gs : List Gate), (∀ g ∈ gs, MonGate g ∧ isBinAnd g = false) →
      ∀ i : ℕ,
        (wireVal gs (zeroIn n) i = true ∧ ∀ x : Fin n → Bool, wireVal gs x i = true) ∨
        (wireVal gs (zeroIn n) i = false ∧
          ∀ x : Fin n → Bool, wireVal gs x i = decide (∃ v ∈ supp n gs i, x v = true)) := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil =>
    intro _ i
    right
    by_cases hi : i < n
    · refine ⟨by rw [wireVal_input [] (zeroIn n) i hi]; rfl, fun x => ?_⟩
      rw [wireVal_input [] x i hi]
      have hsupp : supp n [] i = {⟨i, hi⟩} := by
        ext v
        rw [mem_supp_iff, wireVal_input [] (unitIn v) i hi, Finset.mem_singleton]
        simp [unitIn, eq_comm]
      rw [hsupp]
      simp
    · refine ⟨wireVal_ge [] (zeroIn n) i (by simp; omega), fun x => ?_⟩
      rw [wireVal_ge [] x i (by simp; omega)]
      have hsupp : supp n [] i = ∅ := by
        ext v
        rw [mem_supp_iff, wireVal_ge [] (unitIn v) i (by simp; omega)]
        simp
      rw [hsupp]
      simp
  | append_singleton gs g ih =>
    intro hgs i
    have hgs0 : ∀ h ∈ gs, MonGate h ∧ isBinAnd h = false :=
      fun h hh => hgs h (List.mem_append_left _ hh)
    have hg : MonGate g ∧ isBinAnd g = false := hgs g (by simp)
    rcases lt_trichotomy i (n + gs.length) with hlt | rfl | hgt
    · have hih := ih hgs0 i
      have hsupp : supp n (gs ++ [g]) i = supp n gs i := by
        ext v; simp only [mem_supp_iff, wireVal_snoc_lt gs g _ hlt]
      simp only [wireVal_snoc_lt gs g _ hlt, hsupp]
      exact hih
    · have hchar : ∀ u, (wireVal gs (zeroIn n) u = true ∧ ∀ x, wireVal gs x u = true) ∨
          (wireVal gs (zeroIn n) u = false ∧
            ∀ x, wireVal gs x u = decide (∃ v ∈ supp n gs u, x v = true)) := ih hgs0
      rcases g with ⟨op, ins⟩
      have hlen : ins.length ≤ 2 := hg.1.2
      rcases hg.1.1 with rfl | rfl
      · -- op = GateOp.and, isBinAnd = false, so ins = [] or ins = [a]
        rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩
        · left
          refine ⟨by rw [wireVal_snoc_last]; rfl, fun x => by rw [wireVal_snoc_last]; rfl⟩
        · have hev : ∀ x : Fin n → Bool, wireVal (gs ++ [⟨GateOp.and, [a]⟩]) x (n + gs.length) = wireVal gs x a := by
            intro x; rw [wireVal_snoc_last]; simp [GateOp.eval]
          have hsupp : supp n (gs ++ [⟨GateOp.and, [a]⟩]) (n + gs.length) = supp n gs a := by
            ext v; simp only [mem_supp_iff, hev]
          simp only [hev, hsupp]
          exact hchar a
        · rcases l with _ | ⟨c, l'⟩
          · simp [isBinAnd] at hg
          · simp at hlen
      · -- op = GateOp.or, ins.length ≤ 2
        rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩
        · right
          have hev : ∀ x : Fin n → Bool, wireVal (gs ++ [⟨GateOp.or, []⟩]) x (n + gs.length) = false := by
            intro x; rw [wireVal_snoc_last]; rfl
          have hsupp : supp n (gs ++ [⟨GateOp.or, []⟩]) (n + gs.length) = ∅ := by
            ext v; simp [mem_supp_iff, hev]
          simp [hev, hsupp]
        · have hev : ∀ x : Fin n → Bool, wireVal (gs ++ [⟨GateOp.or, [a]⟩]) x (n + gs.length) = wireVal gs x a := by
            intro x; rw [wireVal_snoc_last]; simp [GateOp.eval]
          have hsupp : supp n (gs ++ [⟨GateOp.or, [a]⟩]) (n + gs.length) = supp n gs a := by
            ext v; simp only [mem_supp_iff, hev]
          simp only [hev, hsupp]
          exact hchar a
        · rcases l with _ | ⟨c, l'⟩
          · have hev : ∀ x : Fin n → Bool, wireVal (gs ++ [⟨GateOp.or, [a, b]⟩]) x (n + gs.length) =
                (wireVal gs x a || wireVal gs x b) := by
              intro x; rw [wireVal_snoc_last]; simp [GateOp.eval]
            rcases hchar a with ⟨ha0, haT⟩ | ⟨ha0, haF⟩
            · left
              exact ⟨by rw [hev, ha0]; rfl, fun x => by rw [hev, haT x]; rfl⟩
            · rcases hchar b with ⟨hb0, hbT⟩ | ⟨hb0, hbF⟩
              · left
                exact ⟨by rw [hev, hb0]; simp, fun x => by rw [hev, hbT x]; simp⟩
              · right
                have hsupp : supp n (gs ++ [⟨GateOp.or, [a, b]⟩]) (n + gs.length) =
                    supp n gs a ∪ supp n gs b := by
                  ext v
                  simp only [mem_supp_iff, hev, Bool.or_eq_true, Finset.mem_union]
                refine ⟨by rw [hev, ha0, hb0]; rfl, fun x => ?_⟩
                rw [hev, haF x, hbF x, hsupp, ← Bool.decide_or]
                apply decide_eq_decide.mpr
                constructor
                · rintro (⟨v, hv, hxv⟩ | ⟨v, hv, hxv⟩)
                  · exact ⟨v, Finset.mem_union_left _ hv, hxv⟩
                  · exact ⟨v, Finset.mem_union_right _ hv, hxv⟩
                · rintro ⟨v, hv, hxv⟩
                  rcases Finset.mem_union.1 hv with hv | hv
                  · exact Or.inl ⟨v, hv, hxv⟩
                  · exact Or.inr ⟨v, hv, hxv⟩
          · simp at hlen
    · right
      have hge : n + (gs ++ [g]).length ≤ i := by simp; omega
      have hsupp : supp n (gs ++ [g]) i = ∅ := by
        ext v; simp [mem_supp_iff, wireVal_ge _ _ _ hge]
      simp [wireVal_ge _ _ _ hge, hsupp]

private lemma list_split_first_true {α : Type*} (p : α → Bool) (l : List α)
    (h : 0 < l.countP p) :
    ∃ l₁ a l₂, l = l₁ ++ a :: l₂ ∧ (∀ x ∈ l₁, p x = false) ∧ p a = true := by
  induction l with
  | nil => simp at h
  | cons x xs ih =>
    cases hpx : p x with
    | true => exact ⟨[], x, xs, rfl, by simp, hpx⟩
    | false =>
      have h' : 0 < xs.countP p := by
        simp only [List.countP_cons, hpx, Bool.false_eq_true, ↓reduceIte, add_zero] at h
        exact h
      obtain ⟨l₁, a, l₂, rfl, hl₁, ha⟩ := ih h'
      exact ⟨x :: l₁, a, l₂, rfl, fun y hy => by
        rcases List.mem_cons.1 hy with rfl | hy'
        · exact hpx
        · exact hl₁ y hy', ha⟩

private lemma elim_one_binAnd {n m : ℕ} (S : Fin m → Finset (Fin n))
    (hS : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (out : Fin m → ℕ) (gs : List Gate)
    (hmon : ∀ g ∈ gs, MonGate g)
    (heval : ∀ (w : Fin m) (x : Fin n → Bool),
      wireVal gs x (out w) = decide (∃ v ∈ S w, x v = true))
    (hand : 0 < gs.countP isBinAnd) :
    ∃ gs' : List Gate,
      gs'.length = gs.length ∧
      gs'.countP isBinAnd + 1 = gs.countP isBinAnd ∧
      (∀ g ∈ gs', MonGate g) ∧
      (∀ (w : Fin m) (x : Fin n → Bool),
        wireVal gs' x (out w) = decide (∃ v ∈ S w, x v = true)) := by
  obtain ⟨gs₁, g, gs₂, hsplit, hpre, hg_and⟩ := list_split_first_true isBinAnd gs hand
  have hgs₁_mon : ∀ h ∈ gs₁, MonGate h ∧ isBinAnd h = false :=
    fun h hh => ⟨hmon h (by rw [hsplit]; simp [hh]), hpre h hh⟩
  have hgs₂_mon : ∀ h ∈ gs₂, MonGate h :=
    fun h hh => hmon h (by rw [hsplit]; simp [hh])
  have hg_shape : ∃ a b, g = ⟨GateOp.and, [a, b]⟩ := by
    rcases g with ⟨op, ins⟩
    cases op <;> simp [isBinAnd] at hg_and
    rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> simp at hg_and
    exact ⟨a, b, rfl⟩
  obtain ⟨a, b, rfl⟩ := hg_shape
  have hstep_same : ∀ (g' : Gate), MonGate g' → isBinAnd g' = false →
      (∀ x : Fin n → Bool, g'.op.eval (g'.inputs.map fun i => wireVal gs₁ x i) =
            (wireVal gs₁ x a && wireVal gs₁ x b)) →
      ∃ gs' : List Gate,
        gs'.length = gs.length ∧
        gs'.countP isBinAnd + 1 = gs.countP isBinAnd ∧
        (∀ h ∈ gs', MonGate h) ∧
        (∀ (w : Fin m) (x : Fin n → Bool),
          wireVal gs' x (out w) = decide (∃ v ∈ S w, x v = true)) := by
    intro g' hg' hg'not heq
    refine ⟨gs₁ ++ g' :: gs₂, by rw [hsplit]; simp, ?_, ?_, ?_⟩
    · have h1 : isBinAnd ⟨GateOp.and, [a, b]⟩ = true := rfl
      rw [hsplit, List.countP_append, List.countP_append, List.countP_cons, List.countP_cons,
        hg'not, h1]
      simp; omega
    · intro h hh
      simp only [List.mem_append, List.mem_cons] at hh
      rcases hh with h1 | rfl | h2
      · exact (hgs₁_mon h h1).1
      · exact hg'
      · exact hgs₂_mon h h2
    · intro w x
      rw [← heval w x, hsplit]
      unfold wireVal
      have hEq : (⟨GateOp.and, [a, b]⟩ : Gate).op.eval
            ((⟨GateOp.and, [a, b]⟩ : Gate).inputs.map fun i => (wiresFrom gs₁ (List.ofFn x)).getD i false) =
          (wireVal gs₁ x a && wireVal gs₁ x b) := by simp [GateOp.eval, wireVal]
      rw [wiresFrom_replace_eq (g := ⟨GateOp.and, [a, b]⟩) ((heq x).trans hEq.symm)]
  -- Check if a or b is constant true on gs₁
  rcases orOnly_wire_char gs₁ hgs₁_mon a with ⟨_, haT⟩ | ⟨ha0, haF⟩
  · exact hstep_same ⟨GateOp.or, [b]⟩ ⟨Or.inr rfl, by simp⟩ rfl
      (fun x => by rw [haT x]; simp [GateOp.eval])
  rcases orOnly_wire_char gs₁ hgs₁_mon b with ⟨_, hbT⟩ | ⟨hb0, hbF⟩
  · exact hstep_same ⟨GateOp.or, [a]⟩ ⟨Or.inr rfl, by simp⟩ rfl
      (fun x => by rw [hbT x]; simp [GateOp.eval])
  -- Now both a and b are exact disjunctions over supp n gs₁ a and supp n gs₁ b
  set A := supp n gs₁ a with hA
  set B := supp n gs₁ b with hB
  set K := A ∩ B with hK
  have hbelow : ∀ (g' : Gate), MonGate g' → isBinAnd g' = false →
      (∀ x : Fin n → Bool, g'.op.eval (g'.inputs.map fun i => wireVal gs₁ x i) = true →
            (wireVal gs₁ x a && wireVal gs₁ x b) = true) →
      (∀ v : Fin n, g'.op.eval (g'.inputs.map fun i => wireVal gs₁ (unitIn v) i) =
            (wireVal gs₁ (unitIn v) a && wireVal gs₁ (unitIn v) b)) →
      ∃ gs' : List Gate,
        gs'.length = gs.length ∧
        gs'.countP isBinAnd + 1 = gs.countP isBinAnd ∧
        (∀ h ∈ gs', MonGate h) ∧
        (∀ (w : Fin m) (x : Fin n → Bool),
          wireVal gs' x (out w) = decide (∃ v ∈ S w, x v = true)) := by
    intro g' hg' hg'not hle hunit
    have hmon' : ∀ h ∈ gs₁ ++ g' :: gs₂, MonGate h := by
      intro h hh
      simp only [List.mem_append, List.mem_cons] at hh
      rcases hh with h1 | rfl | h2
      · exact (hgs₁_mon h h1).1
      · exact hg'
      · exact hgs₂_mon h h2
    refine ⟨gs₁ ++ g' :: gs₂, by rw [hsplit]; simp, ?_, hmon', ?_⟩
    · have h1 : isBinAnd ⟨GateOp.and, [a, b]⟩ = true := rfl
      rw [hsplit, List.countP_append, List.countP_append, List.countP_cons, List.countP_cons,
        hg'not, h1]
      simp; omega
    intro w x
    have hle_out : wireVal (gs₁ ++ g' :: gs₂) x (out w) = true →
        wireVal gs x (out w) = true := by
      rw [hsplit]
      have hEq : GateOp.and.eval ([a, b].map fun i => (wiresFrom gs₁ (List.ofFn x)).getD i false) =
          (wireVal gs₁ x a && wireVal gs₁ x b) := by simp [GateOp.eval, wireVal]
      exact wiresFrom_replace_le hgs₂_mon (fun h => hEq.symm ▸ hle x h) (out w)
    have hunit_out : ∀ v : Fin n, wireVal (gs₁ ++ g' :: gs₂) (unitIn v) (out w) =
        wireVal gs (unitIn v) (out w) := by
      intro v
      rw [hsplit]
      unfold wireVal
      have hEq : (⟨GateOp.and, [a, b]⟩ : Gate).op.eval
            ((⟨GateOp.and, [a, b]⟩ : Gate).inputs.map fun i => (wiresFrom gs₁ (List.ofFn (unitIn v))).getD i false) =
          (wireVal gs₁ (unitIn v) a && wireVal gs₁ (unitIn v) b) := by simp [GateOp.eval, wireVal]
      rw [wiresFrom_replace_eq (g := ⟨GateOp.and, [a, b]⟩) ((hunit v).trans hEq.symm)]
    cases hf : decide (∃ v ∈ S w, x v = true) with
    | false =>
      cases hcur : wireVal (gs₁ ++ g' :: gs₂) x (out w) with
      | false => rfl
      | true =>
        have h1 := hle_out hcur
        rw [heval w x, hf] at h1
        cases h1
    | true =>
      have hex : ∃ v ∈ S w, x v = true := of_decide_eq_true hf
      obtain ⟨v, hvS, hxv⟩ := hex
      have huv : wireVal (gs₁ ++ g' :: gs₂) (unitIn v) (out w) = true := by
        rw [hunit_out v, heval w (unitIn v)]
        exact decide_eq_true ⟨v, hvS, by simp [unitIn]⟩
      exact wireVal_mono hmon' (fun u hu => by
        simp only [unitIn, decide_eq_true_eq] at hu; subst hu; exact hxv) (out w) huv
  have habove : ∀ (g' : Gate), MonGate g' → isBinAnd g' = false →
      (∀ x : Fin n → Bool, (wireVal gs₁ x a && wireVal gs₁ x b) = true →
            g'.op.eval (g'.inputs.map fun i => wireVal gs₁ x i) = true) →
      (∀ w : Fin m, g'.op.eval (g'.inputs.map fun i => wireVal gs₁ (maxZero (S w)) i) =
            (wireVal gs₁ (maxZero (S w)) a && wireVal gs₁ (maxZero (S w)) b)) →
      ∃ gs' : List Gate,
        gs'.length = gs.length ∧
        gs'.countP isBinAnd + 1 = gs.countP isBinAnd ∧
        (∀ h ∈ gs', MonGate h) ∧
        (∀ (w : Fin m) (x : Fin n → Bool),
          wireVal gs' x (out w) = decide (∃ v ∈ S w, x v = true)) := by
    intro g' hg' hg'not hge hmz
    have hmon' : ∀ h ∈ gs₁ ++ g' :: gs₂, MonGate h := by
      intro h hh
      simp only [List.mem_append, List.mem_cons] at hh
      rcases hh with h1 | rfl | h2
      · exact (hgs₁_mon h h1).1
      · exact hg'
      · exact hgs₂_mon h h2
    refine ⟨gs₁ ++ g' :: gs₂, by rw [hsplit]; simp, ?_, hmon', ?_⟩
    · have h1 : isBinAnd ⟨GateOp.and, [a, b]⟩ = true := rfl
      rw [hsplit, List.countP_append, List.countP_append, List.countP_cons, List.countP_cons,
        hg'not, h1]
      simp; omega
    intro w x
    have hge_out : wireVal gs x (out w) = true →
        wireVal (gs₁ ++ g' :: gs₂) x (out w) = true := by
      rw [hsplit]
      have hEq : GateOp.and.eval ([a, b].map fun i => (wiresFrom gs₁ (List.ofFn x)).getD i false) =
          (wireVal gs₁ x a && wireVal gs₁ x b) := by simp [GateOp.eval, wireVal]
      exact wiresFrom_replace_le hgs₂_mon (fun h => hge x (hEq ▸ h)) (out w)
    have hmz_out : wireVal (gs₁ ++ g' :: gs₂) (maxZero (S w)) (out w) = false := by
      have heq' : wireVal (gs₁ ++ g' :: gs₂) (maxZero (S w)) (out w) =
          wireVal gs (maxZero (S w)) (out w) := by
        rw [hsplit]
        unfold wireVal
        have hEq : (⟨GateOp.and, [a, b]⟩ : Gate).op.eval
              ((⟨GateOp.and, [a, b]⟩ : Gate).inputs.map fun i => (wiresFrom gs₁ (List.ofFn (maxZero (S w)))).getD i false) =
            (wireVal gs₁ (maxZero (S w)) a && wireVal gs₁ (maxZero (S w)) b) := by simp [GateOp.eval, wireVal]
        rw [wiresFrom_replace_eq (g := ⟨GateOp.and, [a, b]⟩) ((hmz w).trans hEq.symm)]
      rw [heq', heval w (maxZero (S w))]
      simp [maxZero]
    cases hf : decide (∃ v ∈ S w, x v = true) with
    | true =>
      apply hge_out
      rw [heval w x, hf]
    | false =>
      have hno : ∀ v ∈ S w, x v = false := by
        intro v hv
        cases hxv : x v with
        | false => rfl
        | true =>
          have : decide (∃ v ∈ S w, x v = true) = true := decide_eq_true ⟨v, hv, hxv⟩
          rw [this] at hf; cases hf
      have hxmz : ∀ u, x u = true → maxZero (S w) u = true := by
        intro u hxu
        simp only [maxZero, decide_eq_true_eq]
        intro huS
        have := hno u huS
        rw [hxu] at this; cases this
      cases hcur : wireVal (gs₁ ++ g' :: gs₂) x (out w) with
      | false => rfl
      | true =>
        have h1 := wireVal_mono hmon' hxmz (out w) hcur
        rw [hmz_out] at h1
        cases h1
  -- Case split on K.card
  by_cases hK0 : K.card = 0
  · have hKemp : K = ∅ := Finset.card_eq_zero.1 hK0
    apply hbelow ⟨GateOp.or, []⟩ ⟨Or.inr rfl, by simp⟩ rfl
    · intro x h; simp [GateOp.eval] at h
    · intro v
      simp only [GateOp.eval, List.map_nil, List.any_nil]
      cases h1 : wireVal gs₁ (unitIn v) a <;> cases h2 : wireVal gs₁ (unitIn v) b <;> simp
      have hvK : v ∈ K := Finset.mem_inter.2 ⟨(mem_supp_iff gs₁ a v).2 h1, (mem_supp_iff gs₁ b v).2 h2⟩
      rw [hKemp] at hvK; exact absurd hvK (Finset.notMem_empty v)
  · by_cases hK1 : K.card = 1
    · obtain ⟨v₀, hv₀⟩ := Finset.card_eq_one.1 hK1
      have hv₀A : v₀ ∈ A := (Finset.mem_inter.1 (hv₀ ▸ Finset.mem_singleton_self v₀)).1
      have hv₀B : v₀ ∈ B := (Finset.mem_inter.1 (hv₀ ▸ Finset.mem_singleton_self v₀)).2
      apply hbelow ⟨GateOp.or, [v₀.val]⟩ ⟨Or.inr rfl, by simp⟩ rfl
      · intro x h
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
          id_eq, Bool.or_false, wireVal_input gs₁ x v₀.val v₀.isLt] at h
        rw [haF x, hbF x]
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨⟨v₀, hv₀A, h⟩, ⟨v₀, hv₀B, h⟩⟩
      · intro v
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
          id_eq, Bool.or_false, wireVal_input gs₁ (unitIn v) v₀.val v₀.isLt, unitIn]
        by_cases heq : v₀ = v
        · subst heq
          have h1 : wireVal gs₁ (unitIn v₀) a = true := (mem_supp_iff gs₁ a v₀).1 hv₀A
          have h2 : wireVal gs₁ (unitIn v₀) b = true := (mem_supp_iff gs₁ b v₀).1 hv₀B
          simp [h1, h2]
        · simp only [heq, decide_false]
          cases h1 : wireVal gs₁ (unitIn v) a <;> cases h2 : wireVal gs₁ (unitIn v) b <;> simp
          have hvK : v ∈ K := Finset.mem_inter.2 ⟨(mem_supp_iff gs₁ a v).2 h1, (mem_supp_iff gs₁ b v).2 h2⟩
          rw [hv₀, Finset.mem_singleton] at hvK
          exact absurd hvK.symm heq
    · have hKge2 : 2 ≤ K.card := by omega
      have huniq : ∀ w₁ w₂ : Fin m, K ⊆ S w₁ → K ⊆ S w₂ → w₁ = w₂ := by
        intro w₁ w₂ h1 h2
        by_contra hne
        have hsub : K ⊆ S w₁ ∩ S w₂ := Finset.subset_inter h1 h2
        have hle := Finset.card_le_card hsub
        have hcap := hS w₁ w₂ hne
        omega
      have hmz_iff_a : ∀ w : Fin m, wireVal gs₁ (maxZero (S w)) a = false ↔ A ⊆ S w := by
        intro w
        rw [haF (maxZero (S w))]
        simp only [decide_eq_false_iff_not, not_exists, not_and, maxZero, decide_eq_true_eq,
          not_not]
        rfl
      have hmz_iff_b : ∀ w : Fin m, wireVal gs₁ (maxZero (S w)) b = false ↔ B ⊆ S w := by
        intro w
        rw [hbF (maxZero (S w))]
        simp only [decide_eq_false_iff_not, not_exists, not_and, maxZero, decide_eq_true_eq,
          not_not]
        rfl
      by_cases hsubA : ∃ w₀ : Fin m, A ⊆ S w₀
      · obtain ⟨w₀, hw₀⟩ := hsubA
        have hKw₀ : K ⊆ S w₀ := Finset.inter_subset_left.trans hw₀
        apply habove ⟨GateOp.or, [a]⟩ ⟨Or.inr rfl, by simp⟩ rfl
        · intro x h
          simp only [Bool.and_eq_true] at h
          simp [GateOp.eval, h.1]
        · intro w
          simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
            id_eq, Bool.or_false]
          by_cases hww : w = w₀
          · subst hww
            have ha' : wireVal gs₁ (maxZero (S w)) a = false := (hmz_iff_a w).2 hw₀
            simp [ha']
          · have hnotK : ¬ K ⊆ S w := fun hKw => hww (huniq w w₀ hKw hKw₀)
            have hnotA : ¬ A ⊆ S w := fun hAw => hnotK (Finset.inter_subset_left.trans hAw)
            have hnotB : ¬ B ⊆ S w := fun hBw => hnotK (Finset.inter_subset_right.trans hBw)
            have ha' : wireVal gs₁ (maxZero (S w)) a = true := by
              cases h : wireVal gs₁ (maxZero (S w)) a
              · exact absurd ((hmz_iff_a w).1 h) hnotA
              · rfl
            have hb' : wireVal gs₁ (maxZero (S w)) b = true := by
              cases h : wireVal gs₁ (maxZero (S w)) b
              · exact absurd ((hmz_iff_b w).1 h) hnotB
              · rfl
            simp [ha', hb']
      · by_cases hsubB : ∃ w₀ : Fin m, B ⊆ S w₀
        · obtain ⟨w₀, hw₀⟩ := hsubB
          have hKw₀ : K ⊆ S w₀ := Finset.inter_subset_right.trans hw₀
          apply habove ⟨GateOp.or, [b]⟩ ⟨Or.inr rfl, by simp⟩ rfl
          · intro x h
            simp only [Bool.and_eq_true] at h
            simp [GateOp.eval, h.2]
          · intro w
            simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
              id_eq, Bool.or_false]
            by_cases hww : w = w₀
            · subst hww
              have hb' : wireVal gs₁ (maxZero (S w)) b = false := (hmz_iff_b w).2 hw₀
              simp [hb']
            · have hnotK : ¬ K ⊆ S w := fun hKw => hww (huniq w w₀ hKw hKw₀)
              have hnotA : ¬ A ⊆ S w := fun hAw => hnotK (Finset.inter_subset_left.trans hAw)
              have hnotB : ¬ B ⊆ S w := fun hBw => hnotK (Finset.inter_subset_right.trans hBw)
              have ha' : wireVal gs₁ (maxZero (S w)) a = true := by
                cases h : wireVal gs₁ (maxZero (S w)) a
                · exact absurd ((hmz_iff_a w).1 h) hnotA
                · rfl
              have hb' : wireVal gs₁ (maxZero (S w)) b = true := by
                cases h : wireVal gs₁ (maxZero (S w)) b
                · exact absurd ((hmz_iff_b w).1 h) hnotB
                · rfl
              simp [ha', hb']
        · apply habove ⟨GateOp.and, []⟩ ⟨Or.inl rfl, by simp⟩ rfl
          · intro x _; rfl
          · intro w
            have hnotA : ¬ A ⊆ S w := fun hAw => hsubA ⟨w, hAw⟩
            have hnotB : ¬ B ⊆ S w := fun hBw => hsubB ⟨w, hBw⟩
            have ha' : wireVal gs₁ (maxZero (S w)) a = true := by
              cases h : wireVal gs₁ (maxZero (S w)) a
              · exact absurd ((hmz_iff_a w).1 h) hnotA
              · rfl
            have hb' : wireVal gs₁ (maxZero (S w)) b = true := by
              cases h : wireVal gs₁ (maxZero (S w)) b
              · exact absurd ((hmz_iff_b w).1 h) hnotB
              · rfl
            simp [GateOp.eval, ha', hb']

private lemma elim_all_binAnd {n m : ℕ} (S : Fin m → Finset (Fin n))
    (hS : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (out : Fin m → ℕ) :
    ∀ (k : ℕ) (gs : List Gate),
      gs.countP isBinAnd = k →
      (∀ g ∈ gs, MonGate g) →
      (∀ (w : Fin m) (x : Fin n → Bool),
        wireVal gs x (out w) = decide (∃ v ∈ S w, x v = true)) →
      ∃ gs' : List Gate,
        gs'.length = gs.length ∧
        (∀ g ∈ gs', MonGate g ∧ isBinAnd g = false) ∧
        (∀ (w : Fin m) (x : Fin n → Bool),
          wireVal gs' x (out w) = decide (∃ v ∈ S w, x v = true)) := by
  intro k
  induction k with
  | zero =>
    intro gs hk hmon heval
    refine ⟨gs, rfl, fun g hg => ⟨hmon g hg, ?_⟩, heval⟩
    cases h : isBinAnd g with
    | false => rfl
    | true =>
      have hpos : 0 < gs.countP isBinAnd := List.countP_pos_iff.2 ⟨g, hg, h⟩
      omega
  | succ k ih =>
    intro gs hk hmon heval
    obtain ⟨gs₁, hlen₁, hcnt₁, hmon₁, heval₁⟩ :=
      elim_one_binAnd S hS out gs hmon heval (by omega)
    obtain ⟨gs', hlen', hmon', heval'⟩ := ih gs₁ (by omega) hmon₁ heval₁
    exact ⟨gs', hlen'.trans hlen₁, hmon', heval'⟩

private lemma card_image_merge {α : Type*} [DecidableEq α] (T : Finset α)
    (f : α → ℕ) (c₁ c₂ : ℕ) :
    (T.image f).card ≤ (T.image (fun x => if f x = c₂ then c₁ else f x)).card + 1 := by
  set f' : α → ℕ := fun x => if f x = c₂ then c₁ else f x
  have hsub : T.image f ⊆ insert c₂ (T.image f') := by
    intro y hy
    rcases Finset.mem_image.1 hy with ⟨x, hx, rfl⟩
    by_cases hfx : f x = c₂
    · exact Finset.mem_insert.2 (Or.inl hfx)
    · refine Finset.mem_insert.2 (Or.inr (Finset.mem_image.2 ⟨x, hx, ?_⟩))
      simp [f', hfx]
  calc (T.image f).card
      ≤ (insert c₂ (T.image f')).card := Finset.card_le_card hsub
    _ ≤ (T.image f').card + 1 := Finset.card_insert_le _ _

private lemma single_output_or_bound {n : ℕ} (T : Finset (Fin n)) (out : ℕ)
    (gs : List Gate)
    (hgs : ∀ g ∈ gs, MonGate g ∧ isBinAnd g = false)
    (heval : ∀ x : Fin n → Bool, wireVal gs x out = decide (∃ v ∈ T, x v = true)) :
    T.card - 1 ≤ ((Finset.range gs.length).filter (fun t =>
      wireVal gs (zeroIn n) (n + t) = false ∧
      supp n gs (n + t) ⊆ T ∧
      2 ≤ (supp n gs (n + t)).card)).card := by
  classical
  set G : Finset ℕ := (Finset.range gs.length).filter (fun t =>
    wireVal gs (zeroIn n) (n + t) = false ∧
    supp n gs (n + t) ⊆ T ∧
    2 ≤ (supp n gs (n + t)).card) with hG
  have hstep : ∀ k : ℕ, k ≤ gs.length →
      ∃ comp : Fin n → ℕ,
        T.card ≤ (T.image comp).card + (G.filter (· < k)).card ∧
        ∀ i < n + k, wireVal gs (zeroIn n) i = false → supp n gs i ⊆ T →
          ∀ u ∈ supp n gs i, ∀ v ∈ supp n gs i, comp u = comp v := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨fun v => v.val, ?_, ?_⟩
      · have hcard : (T.image (fun v : Fin n => v.val)).card = T.card :=
          Finset.card_image_of_injective T Fin.val_injective
        simp [hcard]
      · intro i hi _ _ u hu v hv
        rw [mem_supp_iff, wireVal_input gs (unitIn u) i hi] at hu
        rw [mem_supp_iff, wireVal_input gs (unitIn v) i hi] at hv
        simp only [unitIn, decide_eq_true_eq] at hu hv
        have : u = v := hu.symm.trans hv
        rw [this]
    | succ k ih =>
      intro hk
      obtain ⟨comp, hcard, hconst⟩ := ih (by omega)
      have hklt : k < gs.length := by omega
      have hgk : gs[k] ∈ gs := List.getElem_mem hklt
      have hg_mon := hgs gs[k] hgk
      have htake : gs.take (k + 1) = gs.take k ++ [gs[k]] :=
        List.take_succ_eq_append_getElem hklt
      have htake_len : (gs.take k).length = k := List.length_take_of_le (by omega)
      have hval_k : ∀ x : Fin n → Bool, wireVal gs x (n + k) =
          gs[k].op.eval (gs[k].inputs.map fun i => wireVal (gs.take k) x i) := by
        intro x
        rw [← wireVal_take gs x (k := k + 1) (by omega), htake]
        have := wireVal_snoc_last (gs.take k) gs[k] x
        simpa [htake_len] using this
      have hfilt_le : (G.filter (· < k)).card ≤ (G.filter (· < k + 1)).card :=
        Finset.card_le_card (fun t ht => by
          simp only [Finset.mem_filter] at ht ⊢; exact ⟨ht.1, by omega⟩)
      have hconst_noop : (∀ u ∈ supp n gs (n + k), ∀ v ∈ supp n gs (n + k), comp u = comp v) →
          ∃ comp' : Fin n → ℕ,
            T.card ≤ (T.image comp').card + (G.filter (· < k + 1)).card ∧
            ∀ i < n + (k + 1), wireVal gs (zeroIn n) i = false → supp n gs i ⊆ T →
              ∀ u ∈ supp n gs i, ∀ v ∈ supp n gs i, comp' u = comp' v := by
        intro hk_const
        refine ⟨comp, by omega, ?_⟩
        intro i hi h0 hsub
        rcases Nat.lt_succ_iff_lt_or_eq.1 (show i < (n + k) + 1 by omega) with hlt | rfl
        · exact hconst i hlt h0 hsub
        · exact hk_const
      -- If wire n + k is not eligible (either zeroIn = true, or supp n not ⊆ T, or card ≤ 1), comp stays unchanged
      by_cases helig : wireVal gs (zeroIn n) (n + k) = false ∧ supp n gs (n + k) ⊆ T ∧
          2 ≤ (supp n gs (n + k)).card
      · have hmemG : k ∈ G := by
          simp only [hG, Finset.mem_filter, Finset.mem_range]
          exact ⟨hklt, helig⟩
        have hfilt_succ : (G.filter (· < k + 1)).card = (G.filter (· < k)).card + 1 := by
          have heq : G.filter (· < k + 1) = insert k (G.filter (· < k)) := by
            ext t
            simp only [Finset.mem_filter, Finset.mem_insert]
            constructor
            · rintro ⟨htG, htlt⟩
              rcases Nat.lt_succ_iff_lt_or_eq.1 htlt with h | rfl
              · exact Or.inr ⟨htG, h⟩
              · exact Or.inl rfl
            · rintro (htk | ⟨htG, htlt⟩)
              · exact ⟨htk.symm ▸ hmemG, by omega⟩
              · exact ⟨htG, by omega⟩
          rw [heq, Finset.card_insert_of_notMem (by simp)]
        rcases hgk_eq : gs[k] with ⟨op, ins⟩
        rw [hgk_eq] at hg_mon hval_k
        have hlen : ins.length ≤ 2 := hg_mon.1.2
        rcases hg_mon.1.1 with rfl | rfl
        · -- op = and, isBinAnd = false => ins = [] or [a]
          rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩
          · have h0 := hval_k (zeroIn n)
            simp [GateOp.eval] at h0
            rw [helig.1] at h0; cases h0
          · apply hconst_noop
            have hval_a : ∀ x : Fin n → Bool, wireVal gs x (n + k) = wireVal (gs.take k) x a := by
              intro x; rw [hval_k x]; simp [GateOp.eval]
            by_cases ha : a < n + k
            · have hsupp_eq : supp n gs (n + k) = supp n gs a := by
                ext v; simp [mem_supp_iff, hval_a, wireVal_take gs _ ha]
              have ha0 : wireVal gs (zeroIn n) a = false := by
                rw [← wireVal_take gs _ ha, ← hval_a]; exact helig.1
              rw [hsupp_eq]
              exact hconst a ha ha0 (hsupp_eq ▸ helig.2.1)
            · have hsupp_emp : supp n gs (n + k) = ∅ := by
                ext v
                simp [mem_supp_iff, hval_a, wireVal_ge (gs.take k) (unitIn v) a (by rw [htake_len]; omega)]
              rw [hsupp_emp]; simp
          · rcases l with _ | ⟨c, l'⟩
            · simp [isBinAnd] at hg_mon
            · simp at hlen
        · -- op = or, ins.length ≤ 2
          rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩
          · apply hconst_noop
            have hsupp_emp : supp n gs (n + k) = ∅ := by
              ext v; simp [mem_supp_iff, hval_k, GateOp.eval]
            rw [hsupp_emp]; simp
          · apply hconst_noop
            have hval_a : ∀ x : Fin n → Bool, wireVal gs x (n + k) = wireVal (gs.take k) x a := by
              intro x; rw [hval_k x]; simp [GateOp.eval]
            by_cases ha : a < n + k
            · have hsupp_eq : supp n gs (n + k) = supp n gs a := by
                ext v; simp [mem_supp_iff, hval_a, wireVal_take gs _ ha]
              have ha0 : wireVal gs (zeroIn n) a = false := by
                rw [← wireVal_take gs _ ha, ← hval_a]; exact helig.1
              rw [hsupp_eq]
              exact hconst a ha ha0 (hsupp_eq ▸ helig.2.1)
            · have hsupp_emp : supp n gs (n + k) = ∅ := by
                ext v
                simp [mem_supp_iff, hval_a, wireVal_ge (gs.take k) (unitIn v) a (by rw [htake_len]; omega)]
              rw [hsupp_emp]; simp
          · rcases l with _ | ⟨c, l'⟩
            · have hval_ab : ∀ x : Fin n → Bool, wireVal gs x (n + k) =
                  (wireVal (gs.take k) x a || wireVal (gs.take k) x b) := by
                intro x; rw [hval_k x]; simp [GateOp.eval]
              have hsupp_union : supp n gs (n + k) = supp n (gs.take k) a ∪ supp n (gs.take k) b := by
                ext v; simp [mem_supp_iff, hval_ab, Bool.or_eq_true, Finset.mem_union]
              have h0ab := hval_ab (zeroIn n)
              rw [helig.1] at h0ab
              have ha0' : wireVal (gs.take k) (zeroIn n) a = false := by
                cases h : wireVal (gs.take k) (zeroIn n) a <;> simp [h] at h0ab ⊢
              have hb0' : wireVal (gs.take k) (zeroIn n) b = false := by
                cases h : wireVal (gs.take k) (zeroIn n) b <;> simp [h] at h0ab ⊢
              have hconst_a : ∀ u ∈ supp n (gs.take k) a, ∀ v ∈ supp n (gs.take k) a,
                  comp u = comp v := by
                by_cases ha : a < n + k
                · rw [supp_take gs ha]
                  have ha0 : wireVal gs (zeroIn n) a = false := by
                    rw [← wireVal_take gs _ ha]; exact ha0'
                  have hsubA : supp n gs a ⊆ T := by
                    rw [← supp_take gs ha]
                    exact (Finset.subset_union_left.trans (hsupp_union ▸ helig.2.1))
                  exact hconst a ha ha0 hsubA
                · have hemp : supp n (gs.take k) a = ∅ := by
                    ext v; simp [mem_supp_iff, wireVal_ge (gs.take k) (unitIn v) a (by rw [htake_len]; omega)]
                  rw [hemp]; simp
              have hconst_b : ∀ u ∈ supp n (gs.take k) b, ∀ v ∈ supp n (gs.take k) b,
                  comp u = comp v := by
                by_cases hb : b < n + k
                · rw [supp_take gs hb]
                  have hb0 : wireVal gs (zeroIn n) b = false := by
                    rw [← wireVal_take gs _ hb]; exact hb0'
                  have hsubB : supp n gs b ⊆ T := by
                    rw [← supp_take gs hb]
                    exact (Finset.subset_union_right.trans (hsupp_union ▸ helig.2.1))
                  exact hconst b hb hb0 hsubB
                · have hemp : supp n (gs.take k) b = ∅ := by
                    ext v; simp [mem_supp_iff, wireVal_ge (gs.take k) (unitIn v) b (by rw [htake_len]; omega)]
                  rw [hemp]; simp
              by_cases hAne : (supp n (gs.take k) a).Nonempty
              · by_cases hBne : (supp n (gs.take k) b).Nonempty
                · obtain ⟨u₀, hu₀⟩ := hAne
                  obtain ⟨v₀, hv₀⟩ := hBne
                  let comp' : Fin n → ℕ := fun x =>
                    if comp x = comp v₀ then comp u₀ else comp x
                  have hmerge : (T.image comp).card ≤ (T.image comp').card + 1 :=
                    card_image_merge T comp (comp u₀) (comp v₀)
                  refine ⟨comp', by omega, ?_⟩
                  intro i hi h0 hsub
                  rcases Nat.lt_succ_iff_lt_or_eq.1 (show i < (n + k) + 1 by omega) with hlt | rfl
                  · intro u hu v hv
                    have heq := hconst i hlt h0 hsub u hu v hv
                    simp [comp', heq]
                  · intro u hu v hv
                    rw [hsupp_union, Finset.mem_union] at hu hv
                    have hval_u : comp' u = comp u₀ := by
                      rcases hu with huA | huB
                      · have : comp u = comp u₀ := hconst_a u huA u₀ hu₀
                        simp only [comp', this]; split_ifs with h <;> simp [h]
                      · have : comp u = comp v₀ := hconst_b u huB v₀ hv₀
                        simp [comp', this]
                    have hval_v : comp' v = comp u₀ := by
                      rcases hv with hvA | hvB
                      · have : comp v = comp u₀ := hconst_a v hvA u₀ hu₀
                        simp only [comp', this]; split_ifs with h <;> simp [h]
                      · have : comp v = comp v₀ := hconst_b v hvB v₀ hv₀
                        simp [comp', this]
                    exact hval_u.trans hval_v.symm
                · apply hconst_noop
                  have hBemp : supp n (gs.take k) b = ∅ := Finset.not_nonempty_iff_eq_empty.1 hBne
                  rw [hsupp_union, hBemp, Finset.union_empty]
                  exact hconst_a
              · apply hconst_noop
                have hAemp : supp n (gs.take k) a = ∅ := Finset.not_nonempty_iff_eq_empty.1 hAne
                rw [hsupp_union, hAemp, Finset.empty_union]
                exact hconst_b
            · simp at hlen
      · refine ⟨comp, by omega, ?_⟩
        intro i hi h0 hsub
        rcases Nat.lt_succ_iff_lt_or_eq.1 (show i < (n + k) + 1 by omega) with hlt | rfl
        · exact hconst i hlt h0 hsub
        · have hle1 : (supp n gs (n + k)).card ≤ 1 := by
            by_contra hgt
            exact helig ⟨h0, hsub, by omega⟩
          intro u hu v hv
          have heq : u = v := Finset.card_le_one.1 hle1 u hu v hv
          rw [heq]
  obtain ⟨comp, hcard, hconst⟩ := hstep gs.length le_rfl
  have hfilt_all : G.filter (· < gs.length) = G := by
    ext t
    simp only [Finset.mem_filter, and_iff_left_iff_imp]
    intro ht
    simp only [hG, Finset.mem_filter, Finset.mem_range] at ht
    exact ht.1
  rw [hfilt_all] at hcard
  by_cases hTne : T.Nonempty
  · have hout_lt : out < n + gs.length := by
      by_contra hge
      obtain ⟨v, hv⟩ := hTne
      have h1 := heval (unitIn v)
      rw [wireVal_ge gs (unitIn v) out (by omega)] at h1
      have h2 : decide (∃ u ∈ T, unitIn v u = true) = true :=
        decide_eq_true ⟨v, hv, by simp [unitIn]⟩
      rw [h2] at h1; cases h1
    have hout_zero : wireVal gs (zeroIn n) out = false := by
      rw [heval (zeroIn n)]; simp [zeroIn]
    have hout_supp : supp n gs out = T := by
      ext v
      rw [mem_supp_iff, heval (unitIn v)]
      simp only [unitIn, decide_eq_true_eq]
      constructor
      · rintro ⟨u, huT, huv⟩; subst huv; exact huT
      · intro hvT; exact ⟨v, hvT, rfl⟩
    obtain ⟨v₀, hv₀⟩ := hTne
    have himg : T.image comp = {comp v₀} := by
      ext c
      simp only [Finset.mem_image, Finset.mem_singleton]
      constructor
      · rintro ⟨u, huT, rfl⟩
        exact hconst out hout_lt hout_zero (hout_supp ▸ Finset.Subset.refl T)
          u (hout_supp ▸ huT) v₀ (hout_supp ▸ hv₀)
      · rintro rfl
        exact ⟨v₀, hv₀, rfl⟩
    rw [himg, Finset.card_singleton] at hcard
    omega
  · have hTemp : T = ∅ := Finset.not_nonempty_iff_eq_empty.1 hTne
    rw [hTemp]
    simp

end PEqualNP.Outside.L_meta_529_aux

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_529_aux in
theorem PEqualNP.Outside.L_meta_529 : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (w : Fin m) (x : Fin n → Bool), (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x)) = decide (∃ v ∈ S w, x v = true)) → ∑ w, ((S w).card - 1) ≤ gates.length := by
  classical
  intro n m S hS gates out hmon heval
  have heval' : ∀ (w : Fin m) (x : Fin n → Bool),
      wireVal gates x (out w) = decide (∃ v ∈ S w, x v = true) := heval
  obtain ⟨gs', hlen', hgs', heval''⟩ :=
    elim_all_binAnd S hS out (gates.countP isBinAnd) gates rfl hmon heval'
  let G : Fin m → Finset ℕ := fun w =>
    (Finset.range gs'.length).filter (fun t =>
      wireVal gs' (zeroIn n) (n + t) = false ∧
      supp n gs' (n + t) ⊆ S w ∧
      2 ≤ (supp n gs' (n + t)).card)
  have hbound : ∀ w : Fin m, (S w).card - 1 ≤ (G w).card := fun w =>
    single_output_or_bound (S w) (out w) gs' hgs' (heval'' w)
  have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin m))) G := by
    intro w₁ _ w₂ _ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro t ht₁ ht₂
    simp only [G, Finset.mem_filter] at ht₁ ht₂
    have hsub : supp n gs' (n + t) ⊆ S w₁ ∩ S w₂ := Finset.subset_inter ht₁.2.2.1 ht₂.2.2.1
    have hle := Finset.card_le_card hsub
    have hcap := hS w₁ w₂ hne
    omega
  have hsum_le : ∑ w : Fin m, ((S w).card - 1) ≤ ∑ w : Fin m, (G w).card :=
    Finset.sum_le_sum (fun w _ => hbound w)
  have hsum_eq : ∑ w : Fin m, (G w).card = (Finset.univ.biUnion G).card :=
    (Finset.card_biUnion (fun w₁ hw₁ w₂ hw₂ hne => hdisj hw₁ hw₂ hne)).symm
  have hsub_range : Finset.univ.biUnion G ⊆ Finset.range gs'.length := by
    intro t ht
    rw [Finset.mem_biUnion] at ht
    rcases ht with ⟨w, _, htw⟩
    exact (Finset.mem_filter.1 htw).1
  have hcard_le : (Finset.univ.biUnion G).card ≤ gs'.length := by
    calc (Finset.univ.biUnion G).card
        ≤ (Finset.range gs'.length).card := Finset.card_le_card hsub_range
      _ = gs'.length := Finset.card_range _
  omega
