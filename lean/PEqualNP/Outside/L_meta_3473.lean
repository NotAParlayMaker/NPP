import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3473

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.ReadK

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def stepLP (w : List (Bool × Bool)) (g : Gate) : List (Bool × Bool) :=
  let ins := g.inputs.map fun i => w.getD i (false, false)
  w ++ [match g.op with
    | GateOp.or => (ins.any (·.1), ins.any (·.2))
    | GateOp.and => ins.foldl (fun (acc : Bool × Bool) p =>
          (acc.1 && p.1, (acc.1 && p.2) || (acc.2 && p.1))) (true, false)
    | _ => (false, false)]

def initLP (n : ℕ) (isLine : ℕ → Bool) (q r : ℕ) : List (Bool × Bool) :=
  (((List.range n).map fun i => i == q || i == r).zipIdx).map
    fun (b, i) => if isLine i then (false, b) else (b, false)

lemma initLP_length (n : ℕ) (isLine : ℕ → Bool) (q r : ℕ) :
    (initLP n isLine q r).length = n := by
  simp [initLP]

lemma stepW_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepW w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp [List.foldl_cons, stepW, ih]; omega

lemma stepLP_length (gs : List Gate) (w : List (Bool × Bool)) :
    (gs.foldl stepLP w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp [List.foldl_cons, stepLP, ih]; omega

lemma getD_append_left {α : Type*} (l1 l2 : List α) (i : ℕ) (d : α) (hi : i < l1.length) :
    (l1 ++ l2).getD i d = l1.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_append_self {α : Type*} (l : List α) (a d : α) :
    (l ++ [a]).getD l.length d = a := by
  simp [List.getD_eq_getElem?_getD]

lemma getD_ge {α : Type*} (l : List α) (i : ℕ) (d : α) (hi : l.length ≤ i) :
    l.getD i d = d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma getD_forall2_le {w1 w2 : List Bool} (h : List.Forall₂ (fun a b => a ≤ b) w1 w2) (i : ℕ) :
    w1.getD i false ≤ w2.getD i false := by
  induction h generalizing i with
  | nil => simp
  | cons hab _ ih =>
    cases i with
    | zero => simpa using hab
    | succ i => simpa using ih i

def pinGate (n : ℕ) (st : List Gate × List (Option ℕ)) (g : Gate) :
    List Gate × List (Option ℕ) :=
  let gs := st.1
  let m := st.2
  let a := g.inputs.getD 0 0
  let b := g.inputs.getD 1 0
  let sa := m.getD a none
  let sb := m.getD b none
  match g.op with
  | GateOp.and =>
    match sa, sb with
    | some u, some v => (gs ++ [⟨GateOp.and, [u, v]⟩], m ++ [some (n + gs.length)])
    | _, _ => (gs, m ++ [none])
  | GateOp.or =>
    match sa, sb with
    | some u, some v => (gs ++ [⟨GateOp.or, [u, v]⟩], m ++ [some (n + gs.length)])
    | some u, none => (gs, m ++ [some u])
    | none, some v => (gs, m ++ [some v])
    | none, none => (gs, m ++ [none])
  | _ => (gs, m ++ [none])

def initMap (n p : ℕ) : List (Option ℕ) :=
  (List.range n).map fun i => if i = p then none else some i

lemma initMap_length (n p : ℕ) : (initMap n p).length = n := by
  simp [initMap]

lemma initMap_getD_lt (n p i : ℕ) (hi : i < n) :
    (initMap n p).getD i none = if i = p then none else some i := by
  simp [initMap, List.getD_eq_getElem?_getD, hi]

def GoodState (n : ℕ) (k : ℕ) (st : List Gate × List (Option ℕ)) : Prop :=
  st.2.length = n + k ∧
  st.1.length ≤ k ∧
  IsAO2 n ⟨st.1, 0⟩ ∧
  ∀ i u : ℕ, st.2.getD i none = some u → u < n + st.1.length

lemma pinGate_good (n k : ℕ) (st : List Gate × List (Option ℕ)) (g : Gate)
    (hg : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hst : GoodState n k st) :
    GoodState n (k + 1) (pinGate n st g) := by
  rcases hst with ⟨hlen, hsz, hAO, hbound⟩
  rcases hAO with ⟨hao, hrb, hlen2⟩
  rcases hg with ⟨hop, _⟩
  have hbound_append : ∀ s : Option ℕ, (∀ u, s = some u → u < n + st.1.length) →
      ∀ i u, (st.2 ++ [s]).getD i none = some u → u < n + st.1.length := by
    intro s hs i u hi
    by_cases hil : i < st.2.length
    · rw [getD_append_left _ _ _ _ hil] at hi; exact hbound i u hi
    · by_cases heq : i = st.2.length
      · subst heq; rw [getD_append_self] at hi; exact hs u hi
      · rw [getD_ge _ _ _ (by simp; omega)] at hi; cases hi
  rcases hop with hop | hop <;> simp only [pinGate, hop]
  · cases h0 : st.2.getD (g.inputs.getD 0 0) none with
    | none =>
      refine ⟨by simp [hlen]; omega, by simp; omega, ⟨hao, hrb, hlen2⟩,
        hbound_append none (fun _ h => by cases h)⟩
    | some u =>
      cases h2 : st.2.getD (g.inputs.getD 1 0) none with
      | none =>
        refine ⟨by simp [hlen]; omega, by simp; omega, ⟨hao, hrb, hlen2⟩,
          hbound_append none (fun _ h => by cases h)⟩
      | some v =>
        have hu := hbound _ u h0
        have hv := hbound _ v h2
        refine ⟨by simp [hlen]; omega, by simp; omega, ⟨?_, ?_, ?_⟩, ?_⟩
        · intro x hx
          simp only [List.mem_append, List.mem_singleton] at hx
          rcases hx with hx | rfl
          · exact hao x hx
          · exact Or.inl rfl
        · intro j hj a ha
          simp only [List.length_append, List.length_singleton] at hj
          by_cases hjl : j < st.1.length
          · have he : (st.1 ++ [⟨GateOp.and, [u, v]⟩])[j]? = st.1[j]? := by
              rw [List.getElem?_append_left hjl]
            simp only [gateAt, List.getD_eq_getElem?_getD, he] at ha
            exact hrb j hjl a (by simpa [gateAt, List.getD_eq_getElem?_getD] using ha)
          · have heq : j = st.1.length := by omega
            subst heq
            simp only [gateAt, List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl,
              Nat.sub_self, List.getElem?_cons_zero, Option.getD_some, List.mem_cons,
              List.not_mem_nil, or_false] at ha
            rcases ha with rfl | rfl <;> omega
        · intro x hx
          simp only [List.mem_append, List.mem_singleton] at hx
          rcases hx with hx | rfl
          · exact hlen2 x hx
          · rfl
        · intro i w hi
          simp only [List.length_append, List.length_singleton]
          by_cases hil : i < st.2.length
          · rw [getD_append_left _ _ _ _ hil] at hi
            have hw := hbound i w hi
            omega
          · by_cases heq : i = st.2.length
            · subst heq; rw [getD_append_self] at hi; cases hi; omega
            · rw [getD_ge _ _ _ (by simp; omega)] at hi; cases hi
  · cases h0 : st.2.getD (g.inputs.getD 0 0) none with
    | none =>
      cases h2 : st.2.getD (g.inputs.getD 1 0) none with
      | none =>
        refine ⟨by simp [hlen]; omega, by simp; omega, ⟨hao, hrb, hlen2⟩,
          hbound_append none (fun _ h => by cases h)⟩
      | some v =>
        refine ⟨by simp [hlen]; omega, by simp; omega, ⟨hao, hrb, hlen2⟩,
          hbound_append (some v) (fun w hw => by cases hw; exact hbound _ v h2)⟩
    | some u =>
      cases h2 : st.2.getD (g.inputs.getD 1 0) none with
      | none =>
        refine ⟨by simp [hlen]; omega, by simp; omega, ⟨hao, hrb, hlen2⟩,
          hbound_append (some u) (fun w hw => by cases hw; exact hbound _ u h0)⟩
      | some v =>
        have hu := hbound _ u h0
        have hv := hbound _ v h2
        refine ⟨by simp [hlen]; omega, by simp; omega, ⟨?_, ?_, ?_⟩, ?_⟩
        · intro x hx
          simp only [List.mem_append, List.mem_singleton] at hx
          rcases hx with hx | rfl
          · exact hao x hx
          · exact Or.inr rfl
        · intro j hj a ha
          simp only [List.length_append, List.length_singleton] at hj
          by_cases hjl : j < st.1.length
          · have he : (st.1 ++ [⟨GateOp.or, [u, v]⟩])[j]? = st.1[j]? := by
              rw [List.getElem?_append_left hjl]
            simp only [gateAt, List.getD_eq_getElem?_getD, he] at ha
            exact hrb j hjl a (by simpa [gateAt, List.getD_eq_getElem?_getD] using ha)
          · have heq : j = st.1.length := by omega
            subst heq
            simp only [gateAt, List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl,
              Nat.sub_self, List.getElem?_cons_zero, Option.getD_some, List.mem_cons,
              List.not_mem_nil, or_false] at ha
            rcases ha with rfl | rfl <;> omega
        · intro x hx
          simp only [List.mem_append, List.mem_singleton] at hx
          rcases hx with hx | rfl
          · exact hlen2 x hx
          · rfl
        · intro i w hi
          simp only [List.length_append, List.length_singleton]
          by_cases hil : i < st.2.length
          · rw [getD_append_left _ _ _ _ hil] at hi
            have hw := hbound i w hi
            omega
          · by_cases heq : i = st.2.length
            · subst heq; rw [getD_append_self] at hi; cases hi; omega
            · rw [getD_ge _ _ _ (by simp; omega)] at hi; cases hi

lemma foldl_pinGate_good (n : ℕ) (gs : List Gate)
    (hao : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hlen : ∀ g ∈ gs, g.inputs.length = 2) :
    ∀ k st, GoodState n k st → GoodState n (k + gs.length) (gs.foldl (pinGate n) st) := by
  induction gs with
  | nil => intro k st hst; simpa using hst
  | cons g gs ih =>
    intro k st hst
    simp only [List.foldl_cons, List.length_cons]
    have hst' := pinGate_good n k st g ⟨hao g List.mem_cons_self, hlen g List.mem_cons_self⟩ hst
    have hres := ih (fun x hx => hao x (List.mem_cons_of_mem _ hx))
      (fun x hx => hlen x (List.mem_cons_of_mem _ hx)) (k + 1) _ hst'
    rwa [show k + (gs.length + 1) = k + 1 + gs.length by omega]

def Agree {α : Type*} (d : α) (old_l new_l : List α) (m : List (Option ℕ)) : Prop :=
  ∀ i : ℕ, match m.getD i none with
    | none => old_l.getD i d = d
    | some u => old_l.getD i d = new_l.getD u d

lemma agree_no_emit {α : Type*} (d : α) (old_l new_l : List α) (m : List (Option ℕ))
    (old_x : α) (s : Option ℕ)
    (hm : m.length = old_l.length)
    (hag : Agree d old_l new_l m)
    (hstep : match s with | none => old_x = d | some u => old_x = new_l.getD u d) :
    Agree d (old_l ++ [old_x]) new_l (m ++ [s]) := by
  intro i
  by_cases hil : i < m.length
  · rw [getD_append_left _ _ _ _ hil]
    have hgi := hag i
    cases hm_i : m.getD i none with
    | none => rw [hm_i] at hgi; dsimp only at hgi ⊢; rw [getD_append_left _ _ _ _ (by omega)]; exact hgi
    | some q => rw [hm_i] at hgi; dsimp only at hgi ⊢; rw [getD_append_left _ _ _ _ (by omega)]; exact hgi
  · by_cases heq : i = m.length
    · subst heq
      rw [getD_append_self, hm, getD_append_self]
      exact hstep
    · rw [getD_ge _ i none (by simp; omega)]
      exact getD_ge _ i d (by simp; omega)

lemma agree_emit {α : Type*} (d : α) (old_l new_l : List α) (m : List (Option ℕ))
    (old_x new_x : α) (n : ℕ) (k : ℕ)
    (hm : m.length = old_l.length)
    (hnew : new_l.length = n + k)
    (hbound : ∀ i u : ℕ, m.getD i none = some u → u < n + k)
    (hag : Agree d old_l new_l m)
    (hstep : old_x = new_x) :
    Agree d (old_l ++ [old_x]) (new_l ++ [new_x]) (m ++ [some (n + k)]) := by
  intro i
  by_cases hil : i < m.length
  · rw [getD_append_left _ _ _ _ hil]
    have hgi := hag i
    cases hm_i : m.getD i none with
    | none => rw [hm_i] at hgi; dsimp only at hgi ⊢; rw [getD_append_left _ _ _ _ (by omega)]; exact hgi
    | some q =>
      rw [hm_i] at hgi; dsimp only at hgi ⊢
      have hq : q < new_l.length := by have := hbound i q hm_i; omega
      rw [getD_append_left _ _ _ _ (by omega), getD_append_left _ _ _ _ hq]
      exact hgi
  · by_cases heq : i = m.length
    · subst heq
      rw [getD_append_self, hm, getD_append_self, ← hnew]
      dsimp only
      rw [getD_append_self]
      exact hstep
    · rw [getD_ge _ i none (by simp; omega)]
      exact getD_ge _ i d (by simp; omega)

lemma agreeW_init (n : ℕ) (p : Fin n) (x : Fin n → Bool) :
    Agree false (List.ofFn (Function.update x p false)) (List.ofFn x) (initMap n p.val) := by
  intro i
  by_cases hin : i < n
  · rw [initMap_getD_lt n p.val i hin]
    split_ifs with hip
    · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hin, dite_eq_left, Option.getD_some]
      have hpe : (⟨i, hin⟩ : Fin n) = p := Fin.ext hip
      rw [hpe, Function.update_self]
    · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hin, dite_eq_left, Option.getD_some]
      have hne : (⟨i, hin⟩ : Fin n) ≠ p := fun h => hip (congrArg Fin.val h)
      rw [Function.update_of_ne hne]
  · rw [getD_ge _ i none (by rw [initMap_length]; omega)]
    exact getD_ge _ i false (by simp; omega)

lemma agreeLP_init (n : ℕ) (p : Fin n) (isLine : ℕ → Bool) (q r : ℕ)
    (hpq : p.val ≠ q) (hpr : p.val ≠ r) :
    Agree (false, false) (initLP n isLine q r) (initLP n isLine q r) (initMap n p.val) := by
  intro i
  by_cases hin : i < n
  · rw [initMap_getD_lt n p.val i hin]
    split_ifs with hip
    · simp only [initLP, List.getD_eq_getElem?_getD]
      have hget : ((((List.range n).map fun i => i == q || i == r).zipIdx).map
          fun (b, i) => if isLine i then (false, b) else (b, false))[i]? = some (false, false) := by
        rw [List.getElem?_eq_getElem (by simp; omega)]
        congr 1
        simp only [List.getElem_map, List.getElem_zipIdx, List.getElem_range, zero_add]
        have hb : (i == q || i == r) = false := by
          simp [hip, hpq, hpr]
        simp [hb]
      simp [hget]
    · rfl
  · rw [getD_ge _ i none (by rw [initMap_length]; omega)]
    exact getD_ge _ i (false, false) (by rw [initLP_length]; omega)

lemma eval_and2 (w : List Bool) (a b : ℕ) :
    GateOp.and.eval ([a, b].map fun i => w.getD i false) = (w.getD a false && w.getD b false) := by
  simp [GateOp.eval]

lemma eval_or2 (w : List Bool) (a b : ℕ) :
    GateOp.or.eval ([a, b].map fun i => w.getD i false) = (w.getD a false || w.getD b false) := by
  simp [GateOp.eval]

lemma evalLP_and2 (w : List (Bool × Bool)) (a b : ℕ) :
    let ins := [a, b].map fun i => w.getD i (false, false)
    ins.foldl (fun (acc : Bool × Bool) p =>
      (acc.1 && p.1, (acc.1 && p.2) || (acc.2 && p.1))) (true, false) =
      let x := w.getD a (false, false)
      let y := w.getD b (false, false)
      (x.1 && y.1, (x.1 && y.2) || (x.2 && y.1)) := by
  simp

lemma evalLP_or2 (w : List (Bool × Bool)) (a b : ℕ) :
    let ins := [a, b].map fun i => w.getD i (false, false)
    (ins.any (·.1), ins.any (·.2)) =
      let x := w.getD a (false, false)
      let y := w.getD b (false, false)
      (x.1 || y.1, x.2 || y.2) := by
  simp

lemma pinGate_agreeW (n k : ℕ) (st : List Gate × List (Option ℕ)) (g : Gate)
    (hg : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hst : GoodState n k st)
    (w_old w_new : List Bool) (hw_old : w_old.length = n + k) (hw_new : w_new.length = n + st.1.length)
    (hag : Agree false w_old w_new st.2) :
    Agree false (stepW w_old g) ((pinGate n st g).1.drop st.1.length |>.foldl stepW w_new) (pinGate n st g).2 := by
  rcases hst with ⟨hlen, _, _, hbound⟩
  rcases hg with ⟨hop, hgin⟩
  obtain ⟨a, b, hgab⟩ := List.length_eq_two.mp hgin
  have hdrop_nil : (st.1.drop st.1.length) = [] := List.drop_of_length_le le_rfl
  have hdrop_snoc : ∀ x : Gate, (st.1 ++ [x]).drop st.1.length = [x] := fun x => by simp
  have ha_ag := hag a
  have hb_ag := hag b
  have hm_eq : st.2.length = w_old.length := by omega
  rcases hop with hop | hop <;> dsimp only [pinGate] <;> rw [hop, hgab] <;>
    simp only [List.getD_cons_zero, List.getD_cons_succ]
  · cases h0 : st.2.getD a none with
    | none =>
      rw [h0] at ha_ag; dsimp only at ha_ag
      simp only [hdrop_nil, List.foldl_nil]
      exact agree_no_emit false w_old w_new st.2 _ none hm_eq hag
        (by rw [hop, hgab, eval_and2, ha_ag]; rfl)
    | some u =>
      cases h2 : st.2.getD b none with
      | none =>
        rw [h2] at hb_ag; dsimp only at hb_ag
        simp only [hdrop_nil, List.foldl_nil]
        exact agree_no_emit false w_old w_new st.2 _ none hm_eq hag
          (by rw [hop, hgab, eval_and2, hb_ag, Bool.and_false])
      | some v =>
        rw [h0] at ha_ag; rw [h2] at hb_ag; dsimp only at ha_ag hb_ag
        rw [hdrop_snoc, List.foldl_cons, List.foldl_nil]
        exact agree_emit false w_old w_new st.2 _ _ n st.1.length hm_eq hw_new hbound hag
          (by simp only [hop, hgab, eval_and2, ha_ag, hb_ag])
  · cases h0 : st.2.getD a none with
    | none =>
      rw [h0] at ha_ag; dsimp only at ha_ag
      cases h2 : st.2.getD b none with
      | none =>
        rw [h2] at hb_ag; dsimp only at hb_ag
        simp only [hdrop_nil, List.foldl_nil]
        exact agree_no_emit false w_old w_new st.2 _ none hm_eq hag
          (by rw [hop, hgab, eval_or2, ha_ag, hb_ag]; rfl)
      | some v =>
        rw [h2] at hb_ag; dsimp only at hb_ag
        simp only [hdrop_nil, List.foldl_nil]
        exact agree_no_emit false w_old w_new st.2 _ (some v) hm_eq hag
          (by dsimp only; rw [hop, hgab, eval_or2, ha_ag, hb_ag, Bool.false_or])
    | some u =>
      rw [h0] at ha_ag; dsimp only at ha_ag
      cases h2 : st.2.getD b none with
      | none =>
        rw [h2] at hb_ag; dsimp only at hb_ag
        simp only [hdrop_nil, List.foldl_nil]
        exact agree_no_emit false w_old w_new st.2 _ (some u) hm_eq hag
          (by dsimp only; rw [hop, hgab, eval_or2, ha_ag, hb_ag, Bool.or_false])
      | some v =>
        rw [h2] at hb_ag; dsimp only at hb_ag
        rw [hdrop_snoc, List.foldl_cons, List.foldl_nil]
        exact agree_emit false w_old w_new st.2 _ _ n st.1.length hm_eq hw_new hbound hag
          (by simp only [hop, hgab, eval_or2, ha_ag, hb_ag])

lemma pinGate_agreeLP (n k : ℕ) (st : List Gate × List (Option ℕ)) (g : Gate)
    (hg : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hst : GoodState n k st)
    (lp_old lp_new : List (Bool × Bool)) (hlp_old : lp_old.length = n + k) (hlp_new : lp_new.length = n + st.1.length)
    (hag : Agree (false, false) lp_old lp_new st.2) :
    Agree (false, false) (stepLP lp_old g) ((pinGate n st g).1.drop st.1.length |>.foldl stepLP lp_new) (pinGate n st g).2 := by
  rcases hst with ⟨hlen, _, _, hbound⟩
  rcases hg with ⟨hop, hgin⟩
  obtain ⟨a, b, hgab⟩ := List.length_eq_two.mp hgin
  have hdrop_nil : (st.1.drop st.1.length) = [] := List.drop_of_length_le le_rfl
  have hdrop_snoc : ∀ x : Gate, (st.1 ++ [x]).drop st.1.length = [x] := fun x => by simp
  have ha_ag := hag a
  have hb_ag := hag b
  have hm_eq : st.2.length = lp_old.length := by omega
  rcases hop with hop | hop <;> dsimp only [pinGate] <;> rw [hop, hgab] <;>
    simp only [List.getD_cons_zero, List.getD_cons_succ]
  · cases h0 : st.2.getD a none with
    | none =>
      rw [h0] at ha_ag; dsimp only at ha_ag
      simp only [hdrop_nil, List.foldl_nil]
      exact agree_no_emit (false, false) lp_old lp_new st.2 _ none hm_eq hag
        (by dsimp only; rw [hop, hgab, evalLP_and2, ha_ag]; simp)
    | some u =>
      cases h2 : st.2.getD b none with
      | none =>
        rw [h2] at hb_ag; dsimp only at hb_ag
        simp only [hdrop_nil, List.foldl_nil]
        exact agree_no_emit (false, false) lp_old lp_new st.2 _ none hm_eq hag
          (by dsimp only; rw [hop, hgab, evalLP_and2, hb_ag]; simp)
      | some v =>
        rw [h0] at ha_ag; rw [h2] at hb_ag; dsimp only at ha_ag hb_ag
        rw [hdrop_snoc, List.foldl_cons, List.foldl_nil]
        exact agree_emit (false, false) lp_old lp_new st.2 _ _ n st.1.length hm_eq hlp_new hbound hag
          (by dsimp only; rw [hop, hgab]; simp only [evalLP_and2, ha_ag, hb_ag])
  · cases h0 : st.2.getD a none with
    | none =>
      rw [h0] at ha_ag; dsimp only at ha_ag
      cases h2 : st.2.getD b none with
      | none =>
        rw [h2] at hb_ag; dsimp only at hb_ag
        simp only [hdrop_nil, List.foldl_nil]
        exact agree_no_emit (false, false) lp_old lp_new st.2 _ none hm_eq hag
          (by dsimp only; rw [hop, hgab, evalLP_or2, ha_ag, hb_ag]; simp)
      | some v =>
        rw [h2] at hb_ag; dsimp only at hb_ag
        simp only [hdrop_nil, List.foldl_nil]
        exact agree_no_emit (false, false) lp_old lp_new st.2 _ (some v) hm_eq hag
          (by dsimp only; rw [hop, hgab, evalLP_or2, ha_ag, hb_ag]; simp)
    | some u =>
      rw [h0] at ha_ag; dsimp only at ha_ag
      cases h2 : st.2.getD b none with
      | none =>
        rw [h2] at hb_ag; dsimp only at hb_ag
        simp only [hdrop_nil, List.foldl_nil]
        exact agree_no_emit (false, false) lp_old lp_new st.2 _ (some u) hm_eq hag
          (by dsimp only; rw [hop, hgab, evalLP_or2, ha_ag, hb_ag]; simp)
      | some v =>
        rw [h2] at hb_ag; dsimp only at hb_ag
        rw [hdrop_snoc, List.foldl_cons, List.foldl_nil]
        exact agree_emit (false, false) lp_old lp_new st.2 _ _ n st.1.length hm_eq hlp_new hbound hag
          (by dsimp only; rw [hop, hgab]; simp only [evalLP_or2, ha_ag, hb_ag])

lemma pinGate_prefix (n : ℕ) (st : List Gate × List (Option ℕ)) (g : Gate) :
    st.1 = (pinGate n st g).1.take st.1.length := by
  rcases h : g.op with _ | _ | _ | _ | _ <;> simp only [pinGate, h]
  · cases st.2.getD (g.inputs.getD 0 0) none <;> cases st.2.getD (g.inputs.getD 1 0) none <;> simp
  · cases st.2.getD (g.inputs.getD 0 0) none <;> cases st.2.getD (g.inputs.getD 1 0) none <;> simp
  all_goals simp

lemma foldl_pinGate_prefix (n : ℕ) (gs : List Gate) (st : List Gate × List (Option ℕ)) :
    st.1 = (gs.foldl (pinGate n) st).1.take st.1.length := by
  induction gs generalizing st with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have h1 := pinGate_prefix n st g
    have h2 := ih (pinGate n st g)
    have hle : st.1.length ≤ (pinGate n st g).1.length := by
      have := congrArg List.length h1
      rw [List.length_take] at this
      omega
    calc
      st.1 = (pinGate n st g).1.take st.1.length := h1
      _ = ((gs.foldl (pinGate n) (pinGate n st g)).1.take (pinGate n st g).1.length).take st.1.length := by
        rw [← h2]
      _ = (gs.foldl (pinGate n) (pinGate n st g)).1.take st.1.length := by
        rw [List.take_take, Nat.min_eq_left hle]

lemma pinGate_len_le (n : ℕ) (st : List Gate × List (Option ℕ)) (g : Gate) :
    (pinGate n st g).1.length ≤ st.1.length + 1 := by
  rcases h : g.op with _ | _ | _ | _ | _ <;> simp only [pinGate, h]
  · cases st.2.getD (g.inputs.getD 0 0) none <;> cases st.2.getD (g.inputs.getD 1 0) none <;> simp
  · cases st.2.getD (g.inputs.getD 0 0) none <;> cases st.2.getD (g.inputs.getD 1 0) none <;> simp
  all_goals simp

lemma foldl_pinGate_len_le (n : ℕ) (gs : List Gate) (st : List Gate × List (Option ℕ)) :
    (gs.foldl (pinGate n) st).1.length ≤ st.1.length + gs.length := by
  induction gs generalizing st with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, List.length_cons]
    have h1 := pinGate_len_le n st g
    have h2 := ih (pinGate n st g)
    omega

lemma foldl_pinGate_agreeW (n : ℕ) (gs : List Gate)
    (hao : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hlen : ∀ g ∈ gs, g.inputs.length = 2) :
    ∀ k st w_old w_new,
      GoodState n k st →
      w_old.length = n + k →
      w_new.length = n + st.1.length →
      Agree false w_old w_new st.2 →
      Agree false (gs.foldl stepW w_old)
        (((gs.foldl (pinGate n) st).1.drop st.1.length).foldl stepW w_new)
        (gs.foldl (pinGate n) st).2 := by
  induction gs with
  | nil => intro k st w_old w_new _ _ _ hag; simpa using hag
  | cons g gs ih =>
    intro k st w_old w_new hst hw_old hw_new hag
    simp only [List.foldl_cons]
    have hst' := pinGate_good n k st g ⟨hao g List.mem_cons_self, hlen g List.mem_cons_self⟩ hst
    have hag' := pinGate_agreeW n k st g ⟨hao g List.mem_cons_self, hlen g List.mem_cons_self⟩ hst
      w_old w_new hw_old hw_new hag
    have hpref := foldl_pinGate_prefix n gs (pinGate n st g)
    have hsplit : (gs.foldl (pinGate n) (pinGate n st g)).1.drop st.1.length =
        ((pinGate n st g).1.drop st.1.length) ++
        ((gs.foldl (pinGate n) (pinGate n st g)).1.drop (pinGate n st g).1.length) := by
      have hp1 := pinGate_prefix n st g
      have hle : st.1.length ≤ (pinGate n st g).1.length := by
        have := congrArg List.length hp1; rw [List.length_take] at this; omega
      have hsub : (gs.foldl (pinGate n) (pinGate n st g)).1 =
          ((gs.foldl (pinGate n) (pinGate n st g)).1.take (pinGate n st g).1.length) ++
          ((gs.foldl (pinGate n) (pinGate n st g)).1.drop (pinGate n st g).1.length) :=
        (List.take_append_drop _ _).symm
      rw [← hpref] at hsub
      conv_lhs => rw [hsub]
      rw [List.drop_append_of_le_length hle]
    rw [hsplit, List.foldl_append]
    apply ih (fun x hx => hao x (List.mem_cons_of_mem _ hx))
      (fun x hx => hlen x (List.mem_cons_of_mem _ hx))
      (k + 1) (pinGate n st g) (stepW w_old g) _ hst'
    · simp [stepW, hw_old]; omega
    · rw [stepW_length, hw_new]
      have hp1 := pinGate_prefix n st g
      have hle : st.1.length ≤ (pinGate n st g).1.length := by
        have := congrArg List.length hp1; rw [List.length_take] at this; omega
      simp [List.length_drop]; omega
    · exact hag'

lemma foldl_pinGate_agreeLP (n : ℕ) (gs : List Gate)
    (hao : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hlen : ∀ g ∈ gs, g.inputs.length = 2) :
    ∀ k st lp_old lp_new,
      GoodState n k st →
      lp_old.length = n + k →
      lp_new.length = n + st.1.length →
      Agree (false, false) lp_old lp_new st.2 →
      Agree (false, false) (gs.foldl stepLP lp_old)
        (((gs.foldl (pinGate n) st).1.drop st.1.length).foldl stepLP lp_new)
        (gs.foldl (pinGate n) st).2 := by
  induction gs with
  | nil => intro k st lp_old lp_new _ _ _ hag; simpa using hag
  | cons g gs ih =>
    intro k st lp_old lp_new hst hlp_old hlp_new hag
    simp only [List.foldl_cons]
    have hst' := pinGate_good n k st g ⟨hao g List.mem_cons_self, hlen g List.mem_cons_self⟩ hst
    have hag' := pinGate_agreeLP n k st g ⟨hao g List.mem_cons_self, hlen g List.mem_cons_self⟩ hst
      lp_old lp_new hlp_old hlp_new hag
    have hpref := foldl_pinGate_prefix n gs (pinGate n st g)
    have hsplit : (gs.foldl (pinGate n) (pinGate n st g)).1.drop st.1.length =
        ((pinGate n st g).1.drop st.1.length) ++
        ((gs.foldl (pinGate n) (pinGate n st g)).1.drop (pinGate n st g).1.length) := by
      have hp1 := pinGate_prefix n st g
      have hle : st.1.length ≤ (pinGate n st g).1.length := by
        have := congrArg List.length hp1; rw [List.length_take] at this; omega
      have hsub : (gs.foldl (pinGate n) (pinGate n st g)).1 =
          ((gs.foldl (pinGate n) (pinGate n st g)).1.take (pinGate n st g).1.length) ++
          ((gs.foldl (pinGate n) (pinGate n st g)).1.drop (pinGate n st g).1.length) :=
        (List.take_append_drop _ _).symm
      rw [← hpref] at hsub
      conv_lhs => rw [hsub]
      rw [List.drop_append_of_le_length hle]
    rw [hsplit, List.foldl_append]
    apply ih (fun x hx => hao x (List.mem_cons_of_mem _ hx))
      (fun x hx => hlen x (List.mem_cons_of_mem _ hx))
      (k + 1) (pinGate n st g) (stepLP lp_old g) _ hst'
    · simp [stepLP, hlp_old]; omega
    · rw [stepLP_length, hlp_new]
      have hp1 := pinGate_prefix n st g
      have hle : st.1.length ≤ (pinGate n st g).1.length := by
        have := congrArg List.length hp1; rw [List.length_take] at this; omega
      simp [List.length_drop]; omega
    · exact hag'

lemma stepW_mono (gs : List Gate) (hao : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ w1 w2 : List Bool, List.Forall₂ (fun a b => a ≤ b) w1 w2 →
      List.Forall₂ (fun a b => a ≤ b) (gs.foldl stepW w1) (gs.foldl stepW w2) := by
  induction gs with
  | nil => intro w1 w2 h; exact h
  | cons g gs ih =>
    intro w1 w2 h
    simp only [List.foldl_cons]
    apply ih (fun x hx => hao x (List.mem_cons_of_mem _ hx))
    refine List.rel_append h (List.Forall₂.cons ?_ List.Forall₂.nil)
    have hget := getD_forall2_le h
    rcases hao g List.mem_cons_self with hop | hop <;> simp only [hop, GateOp.eval]
    · cases h1 : (g.inputs.map fun i => w1.getD i false).all id with
      | false => simp
      | true =>
        simp only [List.all_eq_true, id_eq, List.mem_map] at h1
        have h2 : (g.inputs.map fun i => w2.getD i false).all id = true := by
          simp only [List.all_eq_true, id_eq, List.mem_map]
          rintro _ ⟨i, hi, rfl⟩
          have hgi := hget i
          have hi1 := h1 _ ⟨i, hi, rfl⟩
          rw [hi1] at hgi
          cases hw2 : w2.getD i false
          · exfalso; rw [hw2] at hgi; exact Bool.false_ne_true (Bool.eq_true_of_true_le hgi)
          · rfl
        change true ≤ (g.inputs.map fun i => w2.getD i false).all id
        rw [h2]
    · cases h1 : (g.inputs.map fun i => w1.getD i false).any id with
      | false => simp
      | true =>
        simp only [List.any_eq_true, id_eq, List.mem_map] at h1
        obtain ⟨_, ⟨i, hi, rfl⟩, hi1⟩ := h1
        have hgi := hget i
        rw [hi1] at hgi
        have hi2 : w2.getD i false = true := by
          cases hw2 : w2.getD i false
          · exfalso; rw [hw2] at hgi; exact Bool.false_ne_true (Bool.eq_true_of_true_le hgi)
          · rfl
        have h2 : (g.inputs.map fun i => w2.getD i false).any id = true := by
          simp only [List.any_eq_true, id_eq, List.mem_map]
          exact ⟨true, ⟨i, hi, hi2⟩, rfl⟩
        change true ≤ (g.inputs.map fun i => w2.getD i false).any id
        rw [h2]

def SameOff (w1 w2 : List Bool) (m : List (Option ℕ)) : Prop :=
  ∀ i : ℕ, m.getD i none ≠ none → w1.getD i false = w2.getD i false

lemma pinGate_full_size_step (n : ℕ) (st : List Gate × List (Option ℕ)) (g : Gate)
    (hg : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hlen_eq : (pinGate n st g).1.length = st.1.length + 1)
    (w1 w2 : List Bool) (hw1 : w1.length = st.2.length) (hw2 : w2.length = st.2.length)
    (hsame : SameOff w1 w2 st.2) :
    SameOff (stepW w1 g) (stepW w2 g) (pinGate n st g).2 := by
  rcases hg with ⟨hop, hgin⟩
  obtain ⟨a, b, hgab⟩ := List.length_eq_two.mp hgin
  have step_eq : ∀ u v : ℕ, st.2.getD a none = some u → st.2.getD b none = some v →
      (stepW w1 g).getD w1.length false = (stepW w2 g).getD w2.length false := by
    intro u v hu hv
    have ha := hsame a (by rw [hu]; simp)
    have hb := hsame b (by rw [hv]; simp)
    simp only [stepW, getD_append_self, hgab, List.map_cons, List.map_nil]
    rw [ha, hb]
  rcases hop with hop | hop <;>
    dsimp only [pinGate] at hlen_eq ⊢ <;>
    rw [hop, hgab] at hlen_eq ⊢ <;>
    simp only [List.getD_cons_zero, List.getD_cons_succ] at hlen_eq ⊢
  · cases h0 : st.2.getD a none with
    | none => rw [h0] at hlen_eq; simp at hlen_eq
    | some u =>
      cases h2 : st.2.getD b none with
      | none => rw [h0, h2] at hlen_eq; simp at hlen_eq
      | some v =>
        intro i hi
        by_cases hil : i < st.2.length
        · rw [getD_append_left _ _ _ _ hil] at hi
          dsimp only [stepW]
          rw [getD_append_left _ _ _ _ (by omega), getD_append_left _ _ _ _ (by omega)]
          exact hsame i hi
        · by_cases heq : i = st.2.length
          · subst heq; rw [← hw1]; nth_rw 2 [hw1]; rw [← hw2]; exact step_eq u v h0 h2
          · rw [getD_ge _ i none (by simp; omega)] at hi
            exact False.elim (hi rfl)
  · cases h0 : st.2.getD a none with
    | none =>
      cases h2 : st.2.getD b none with
      | none => rw [h0, h2] at hlen_eq; simp at hlen_eq
      | some v => rw [h0, h2] at hlen_eq; simp at hlen_eq
    | some u =>
      cases h2 : st.2.getD b none with
      | none => rw [h0, h2] at hlen_eq; simp at hlen_eq
      | some v =>
        intro i hi
        by_cases hil : i < st.2.length
        · rw [getD_append_left _ _ _ _ hil] at hi
          dsimp only [stepW]
          rw [getD_append_left _ _ _ _ (by omega), getD_append_left _ _ _ _ (by omega)]
          exact hsame i hi
        · by_cases heq : i = st.2.length
          · subst heq; rw [← hw1]; nth_rw 2 [hw1]; rw [← hw2]; exact step_eq u v h0 h2
          · rw [getD_ge _ i none (by simp; omega)] at hi
            exact False.elim (hi rfl)

lemma foldl_pinGate_full_size (n : ℕ) (gs : List Gate)
    (hao : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hlen : ∀ g ∈ gs, g.inputs.length = 2) :
    ∀ k st w1 w2,
      GoodState n k st →
      w1.length = st.2.length →
      w2.length = st.2.length →
      SameOff w1 w2 st.2 →
      (gs.foldl (pinGate n) st).1.length = st.1.length + gs.length →
      SameOff (gs.foldl stepW w1) (gs.foldl stepW w2) (gs.foldl (pinGate n) st).2 := by
  induction gs with
  | nil => intro k st w1 w2 _ _ _ hsame _; simpa using hsame
  | cons g gs ih =>
    intro k st w1 w2 hst hw1 hw2 hsame hfull
    simp only [List.foldl_cons, List.length_cons] at hfull ⊢
    have h1 := pinGate_len_le n st g
    have h2 := foldl_pinGate_len_le n gs (pinGate n st g)
    have heq1 : (pinGate n st g).1.length = st.1.length + 1 := by omega
    have heq2 : (gs.foldl (pinGate n) (pinGate n st g)).1.length = (pinGate n st g).1.length + gs.length := by omega
    have hst' := pinGate_good n k st g ⟨hao g List.mem_cons_self, hlen g List.mem_cons_self⟩ hst
    have hsame' := pinGate_full_size_step n st g ⟨hao g List.mem_cons_self, hlen g List.mem_cons_self⟩
      heq1 w1 w2 hw1 hw2 hsame
    exact ih (fun x hx => hao x (List.mem_cons_of_mem _ hx))
      (fun x hx => hlen x (List.mem_cons_of_mem _ hx))
      (k + 1) (pinGate n st g) (stepW w1 g) (stepW w2 g) hst'
      (by simp [stepW, hw1, hst.1, hst'.1]; omega) (by simp [stepW, hw2, hst.1, hst'.1]; omega) hsame' heq2

lemma foldl_pinGate_full_map (n p : ℕ) (gs : List Gate)
    (hao : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hlen : ∀ g ∈ gs, g.inputs.length = 2) :
    ∀ k st,
      GoodState n k st →
      (∀ i, i < n + k → i ≠ p → st.2.getD i none ≠ none) →
      (gs.foldl (pinGate n) st).1.length = st.1.length + gs.length →
      ∀ i, i < n + k + gs.length → i ≠ p → (gs.foldl (pinGate n) st).2.getD i none ≠ none := by
  induction gs with
  | nil => intro k st _ h _ i hi hip; simpa using h i hi hip
  | cons g gs ih =>
    intro k st hst hmap hfull i hi hip
    simp only [List.foldl_cons, List.length_cons] at hfull hi ⊢
    have h1 := pinGate_len_le n st g
    have h2 := foldl_pinGate_len_le n gs (pinGate n st g)
    have heq1 : (pinGate n st g).1.length = st.1.length + 1 := by omega
    have heq2 : (gs.foldl (pinGate n) (pinGate n st g)).1.length = (pinGate n st g).1.length + gs.length := by omega
    have hst' := pinGate_good n k st g ⟨hao g List.mem_cons_self, hlen g List.mem_cons_self⟩ hst
    have hstlen : st.2.length = n + k := hst.1
    have hmap' : ∀ j, j < n + (k + 1) → j ≠ p → (pinGate n st g).2.getD j none ≠ none := by
      intro j hj hjp
      by_cases hjl : j < st.2.length
      · have hpin : (pinGate n st g).2.take st.2.length = st.2 := by
          rcases hao g List.mem_cons_self with hop | hop <;> simp only [pinGate, hop]
          · cases st.2.getD (g.inputs.getD 0 0) none <;> cases st.2.getD (g.inputs.getD 1 0) none <;> simp
          · cases st.2.getD (g.inputs.getD 0 0) none <;> cases st.2.getD (g.inputs.getD 1 0) none <;> simp
        have hget : (pinGate n st g).2.getD j none = st.2.getD j none := by
          have := congrArg (fun l : List (Option ℕ) => l.getD j none) hpin
          simpa [List.getD_eq_getElem?_getD, hjl] using this
        rw [hget]
        exact hmap j (by omega) hjp
      · have hjeq : j = st.2.length := by omega
        subst hjeq
        obtain ⟨a, b, hgab⟩ := List.length_eq_two.mp (hlen g List.mem_cons_self)
        rcases hao g List.mem_cons_self with hop | hop <;>
          dsimp only [pinGate] at heq1 ⊢ <;>
          rw [hop, hgab] at heq1 ⊢ <;>
          simp only [List.getD_cons_zero, List.getD_cons_succ] at heq1 ⊢
        · cases h0 : st.2.getD a none with
          | none => rw [h0] at heq1; simp at heq1
          | some u =>
            cases h2 : st.2.getD b none with
            | none => rw [h0, h2] at heq1; simp at heq1
            | some v => simp
        · cases h0 : st.2.getD a none with
          | none =>
            cases h2 : st.2.getD b none with
            | none => rw [h0, h2] at heq1; simp at heq1
            | some v => rw [h0, h2] at heq1; simp at heq1
          | some u =>
            cases h2 : st.2.getD b none with
            | none => rw [h0, h2] at heq1; simp at heq1
            | some v => simp
    exact ih (fun x hx => hao x (List.mem_cons_of_mem _ hx))
      (fun x hx => hlen x (List.mem_cons_of_mem _ hx))
      (k + 1) (pinGate n st g) hst' hmap' heq2 i (by omega) hip

lemma foldl_stepW_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepW w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp [stepW]; omega)]
    exact getD_append_left w _ i false hi

lemma main_proof (x1 : ℕ) (x2 : Circuit) (x3 : Fin x1)
    (hAO : IsAO2 x1 x2)
    (hdep : ∃ (x5 x6 : Fin x1 → Bool), (∀ x7, x7 ≠ x3 → x5 x7 = x6 x7) ∧
      circuitFun x1 x2 x5 ≠ circuitFun x1 x2 x6)
    (hsing : circuitFun x1 x2 (fun x6 => decide (x6 = x3)) = false) :
    ∃ (x7 : Circuit), IsAO2 x1 x7 ∧ x7.size < x2.size ∧
      (∀ x8, circuitFun x1 x7 x8 = true → circuitFun x1 x2 x8 = true) ∧
      (∀ x8, x8 x3 = false → circuitFun x1 x7 x8 = circuitFun x1 x2 x8) ∧
      ∀ (x8 : ℕ → Bool) (x9 x10 : ℕ), ↑x3 ≠ x9 → ↑x3 ≠ x10 →
        lineSingle x7 x1 x8 x9 x10 = lineSingle x2 x1 x8 x9 x10 := by
  rcases hAO with ⟨hao, hrb, hlen2⟩
  let st0 : List Gate × List (Option ℕ) := ([], initMap x1 x3.val)
  let stf := x2.gates.foldl (pinGate x1) st0
  have hst0 : GoodState x1 0 st0 := by
    refine ⟨by simp [st0, initMap_length], le_rfl, ?_, ?_⟩
    · refine ⟨fun _ h => by simp [st0] at h, fun _ h => by simp [st0] at h, fun _ h => by simp [st0] at h⟩
    · intro i u hi
      by_cases hin : i < x1
      · have hinit := initMap_getD_lt x1 x3.val i hin
        dsimp only [st0] at hi
        rw [hinit] at hi
        by_cases hip : i = x3.val
        · simp [hip] at hi
        · simp [hip] at hi
          cases hi; simp only [st0, List.length_nil, Nat.add_zero]; exact hin
      · rw [getD_ge _ i none (by simp [st0, initMap_length]; omega)] at hi
        cases hi
  have hstf : GoodState x1 x2.gates.length stf := by
    simpa [stf] using foldl_pinGate_good x1 x2.gates hao hlen2 0 st0 hst0
  have hsz_le : stf.1.length ≤ x2.gates.length := hstf.2.1
  have hsz_lt : stf.1.length < x2.gates.length := by
    by_contra hge
    have hfull : stf.1.length = st0.1.length + x2.gates.length := by simp [st0]; omega
    obtain ⟨x5, x6, hagree, hdiff⟩ := hdep
    have hsame0 : SameOff (List.ofFn x5) (List.ofFn x6) st0.2 := by
      intro i hi
      by_cases hin : i < x1
      · simp only [st0, initMap_getD_lt x1 x3.val i hin] at hi
        split_ifs at hi with hip
        · exact False.elim (hi rfl)
        · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hin, dite_eq_left, Option.getD_some]
          exact hagree ⟨i, hin⟩ (fun heq => hip (congrArg Fin.val heq))
      · rw [getD_ge _ i none (by simp [st0, initMap_length]; omega)] at hi
        exact False.elim (hi rfl)
    have hsamef := foldl_pinGate_full_size x1 x2.gates hao hlen2 0 st0 (List.ofFn x5) (List.ofFn x6)
      hst0 (by simp [st0, initMap_length]) (by simp [st0, initMap_length]) hsame0 hfull
    have hmap0 : ∀ i, i < x1 + 0 → i ≠ x3.val → st0.2.getD i none ≠ none := by
      intro i hi hip
      simp only [st0, initMap_getD_lt x1 x3.val i (by omega)]
      simp [hip]
    have hmapf := foldl_pinGate_full_map x1 x3.val x2.gates hao hlen2 0 st0 hst0 hmap0 hfull
    by_cases hout_lt : x2.output < x1 + x2.gates.length
    · have hout_ne : x2.output ≠ x3.val := by
        intro heq
        let z : Fin x1 → Bool := fun i => decide (i = x3)
        have hz : (x2.gates.foldl stepW (List.ofFn z)).getD x3.val false = z x3 := by
          rw [foldl_stepW_lt _ _ _ (by simp)]
          simp [z, List.getD_eq_getElem?_getD]
        have htrue : circuitFun x1 x2 z = true := by
          change (x2.gates.foldl stepW (List.ofFn z)).getD x2.output false = true
          rw [heq, hz]
          simp [z]
        rw [hsing] at htrue
        cases htrue
      apply hdiff
      change (x2.gates.foldl stepW (List.ofFn x5)).getD x2.output false =
        (x2.gates.foldl stepW (List.ofFn x6)).getD x2.output false
      exact hsamef x2.output (hmapf x2.output (by omega) hout_ne)
    · apply hdiff
      change (x2.gates.foldl stepW (List.ofFn x5)).getD x2.output false =
        (x2.gates.foldl stepW (List.ofFn x6)).getD x2.output false
      have hwf5 : (x2.gates.foldl stepW (List.ofFn x5)).length = x1 + x2.gates.length := by
        simpa using stepW_length x2.gates (List.ofFn x5)
      have hwf6 : (x2.gates.foldl stepW (List.ofFn x6)).length = x1 + x2.gates.length := by
        simpa using stepW_length x2.gates (List.ofFn x6)
      rw [getD_ge _ _ _ (by omega), getD_ge _ _ _ (by omega)]
  let out' : ℕ := match stf.2.getD x2.output none with
    | some w => w
    | none => x1 + stf.1.length
  let D : Circuit := ⟨stf.1, out'⟩
  have hD_AO : IsAO2 x1 D := ⟨hstf.2.2.1.1, hstf.2.2.1.2.1, hstf.2.2.1.2.2⟩
  have hD_eval (x8 : Fin x1 → Bool) :
      circuitFun x1 D x8 = circuitFun x1 x2 (Function.update x8 x3 false) := by
    have hag := foldl_pinGate_agreeW x1 x2.gates hao hlen2 0 st0
      (List.ofFn (Function.update x8 x3 false)) (List.ofFn x8) hst0
      (by simp) (by simp [st0]) (agreeW_init x1 x3 x8)
    simp only [st0, List.length_nil, List.drop_zero] at hag
    have h := hag x2.output
    change (stf.1.foldl stepW (List.ofFn x8)).getD out' false =
      (x2.gates.foldl stepW (List.ofFn (Function.update x8 x3 false))).getD x2.output false
    cases hm : stf.2.getD x2.output none with
    | none =>
      rw [hm] at h
      have hlenD : (stf.1.foldl stepW (List.ofFn x8)).length = x1 + stf.1.length := by
        simpa using stepW_length stf.1 (List.ofFn x8)
      have houtD : out' = x1 + stf.1.length := by dsimp [out']; rw [hm]
      rw [houtD, getD_ge _ _ _ (by omega), h]
    | some w =>
      rw [hm] at h
      have houtD : out' = w := by dsimp [out']; rw [hm]
      rw [houtD, h]
  refine ⟨D, hD_AO, hsz_lt, ?_, ?_, ?_⟩
  · intro x8 hx8
    rw [hD_eval x8] at hx8
    have hle : List.Forall₂ (fun a b => a ≤ b) (List.ofFn (Function.update x8 x3 false)) (List.ofFn x8) := by
      rw [List.forall₂_iff_get]
      refine ⟨by simp, fun i h1 h2 => ?_⟩
      simp only [List.get_eq_getElem, List.getElem_ofFn]
      by_cases hix : (⟨i, by simpa using h1⟩ : Fin x1) = x3
      · rw [hix, Function.update_self]; exact Bool.false_le _
      · rw [Function.update_of_ne hix]
    have hget := getD_forall2_le (stepW_mono x2.gates hao _ _ hle) x2.output
    change (x2.gates.foldl stepW (List.ofFn (Function.update x8 x3 false))).getD x2.output false = true at hx8
    change (x2.gates.foldl stepW (List.ofFn x8)).getD x2.output false = true
    rw [hx8] at hget
    cases h : (x2.gates.foldl stepW (List.ofFn x8)).getD x2.output false
    · rw [h] at hget; contradiction
    · rfl
  · intro x8 hx8
    rw [hD_eval x8]
    have hu : Function.update x8 x3 false = x8 := by
      funext j
      by_cases hj : j = x3
      · subst hj; simp [hx8]
      · simp [Function.update_of_ne hj]
    rw [hu]
  · intro x8 x9 x10 h9 h10
    have hag := foldl_pinGate_agreeLP x1 x2.gates hao hlen2 0 st0
      (initLP x1 x8 x9 x10) (initLP x1 x8 x9 x10) hst0
      (by simp [initLP_length]) (by simp [st0, initLP_length])
      (agreeLP_init x1 x3 x8 x9 x10 h9 h10)
    simp only [st0, List.length_nil, List.drop_zero] at hag
    have h := hag x2.output
    have hlp_D : linearParts D x8 ((List.range x1).map fun i => i == x9 || i == x10) =
        stf.1.foldl stepLP (initLP x1 x8 x9 x10) := rfl
    have hlp_C : linearParts x2 x8 ((List.range x1).map fun i => i == x9 || i == x10) =
        x2.gates.foldl stepLP (initLP x1 x8 x9 x10) := rfl
    simp only [lineSingle, hlp_D, hlp_C]
    cases hm : stf.2.getD x2.output none with
    | none =>
      rw [hm] at h
      have hlenD : (stf.1.foldl stepLP (initLP x1 x8 x9 x10)).length = x1 + stf.1.length := by
        rw [stepLP_length, initLP_length]
      have houtD : D.output = x1 + stf.1.length := by dsimp [D, out']; rw [hm]
      rw [houtD, getD_ge _ _ _ (by omega), h]
    | some w =>
      rw [hm] at h
      have houtD : D.output = w := by dsimp [D, out']; rw [hm]
      rw [houtD, h]

end PEqualNP.Outside.L_meta_3473

theorem PEqualNP.Outside.L_meta_3473 :
    ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Fin x1), PEqualNP.TopForm.IsAO2 x1 x2 → (∃ (x5 : Fin x1 → Bool) (x6 : Fin x1 → Bool), (∀ (x7 : Fin x1), x7 ≠ x3 → x5 x7 = x6 x7) ∧ PEqualNP.MetaComplexity.circuitFun x1 x2 x5 ≠ PEqualNP.MetaComplexity.circuitFun x1 x2 x6) → (PEqualNP.MetaComplexity.circuitFun x1 x2 fun (x6 : Fin x1) => Decidable.decide (x6 = x3)) = Bool.false → ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x7 ∧ x7.size < x2.size ∧ (∀ (x8 : Fin x1 → Bool), PEqualNP.MetaComplexity.circuitFun x1 x7 x8 = Bool.true → PEqualNP.MetaComplexity.circuitFun x1 x2 x8 = Bool.true) ∧ (∀ (x8 : Fin x1 → Bool), x8 x3 = Bool.false → PEqualNP.MetaComplexity.circuitFun x1 x7 x8 = PEqualNP.MetaComplexity.circuitFun x1 x2 x8) ∧ ∀ (x8 : ℕ → Bool) (x9 x10 : ℕ), ↑x3 ≠ x9 → ↑x3 ≠ x10 → PEqualNP.ReadK.lineSingle x7 x1 x8 x9 x10 = PEqualNP.ReadK.lineSingle x2 x1 x8 x9 x10 := PEqualNP.Outside.L_meta_3473.main_proof
