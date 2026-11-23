import PEqualNP.Defs
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Paths

namespace PEqualNP.Outside.L_meta_599_aux

open PEqualNP.CircuitLowerBounds

inductive MGate where
  | cFalse
  | cTrue
  | copy (a : ℕ)
  | and (a b : ℕ)
  | or (a b : ℕ)

def MGate.isOr : MGate → Bool
  | MGate.or _ _ => true
  | _ => false

def evalWire (n : ℕ) (gs : List MGate) (x : Fin n → Bool) : ℕ → Bool
  | w =>
    if h : w < n then
      x ⟨w, h⟩
    else
      match gs[w - n]? with
      | none => false
      | some MGate.cFalse => false
      | some MGate.cTrue => true
      | some (MGate.copy a) =>
          if a < w then evalWire n gs x a else false
      | some (MGate.and a b) =>
          (if a < w then evalWire n gs x a else false) &&
          (if b < w then evalWire n gs x b else false)
      | some (MGate.or a b) =>
          (if a < w then evalWire n gs x a else false) ||
          (if b < w then evalWire n gs x b else false)
termination_by w => w

def WF (n : ℕ) (gs : List MGate) : Prop :=
  ∀ (j : ℕ) (g : MGate), gs[j]? = some g →
    match g with
    | MGate.cFalse => True
    | MGate.cTrue => True
    | MGate.copy a => a < n + j
    | MGate.and a b => a < n + j ∧ b < n + j
    | MGate.or a b => a < n + j ∧ b < n + j

lemma evalWire_lt (n : ℕ) (gs : List MGate) (x : Fin n → Bool) (w : ℕ) (h : w < n) :
    evalWire n gs x w = x ⟨w, h⟩ := by
  rw [evalWire]; simp [h]

lemma evalWire_none (n : ℕ) (gs : List MGate) (x : Fin n → Bool) (w : ℕ)
    (h : ¬ w < n) (hg : gs[w - n]? = none) :
    evalWire n gs x w = false := by
  rw [evalWire]; simp [h, hg]

lemma evalWire_cFalse (n : ℕ) (gs : List MGate) (x : Fin n → Bool) (w : ℕ)
    (h : ¬ w < n) (hg : gs[w - n]? = some MGate.cFalse) :
    evalWire n gs x w = false := by
  rw [evalWire]; simp [h, hg]

lemma evalWire_cTrue (n : ℕ) (gs : List MGate) (x : Fin n → Bool) (w : ℕ)
    (h : ¬ w < n) (hg : gs[w - n]? = some MGate.cTrue) :
    evalWire n gs x w = true := by
  rw [evalWire]; simp [h, hg]

lemma evalWire_copy (n : ℕ) (gs : List MGate) (x : Fin n → Bool) (w a : ℕ)
    (h : ¬ w < n) (hg : gs[w - n]? = some (MGate.copy a)) (ha : a < w) :
    evalWire n gs x w = evalWire n gs x a := by
  rw [evalWire]; simp [h, hg, ha]

lemma evalWire_and (n : ℕ) (gs : List MGate) (x : Fin n → Bool) (w a b : ℕ)
    (h : ¬ w < n) (hg : gs[w - n]? = some (MGate.and a b)) (ha : a < w) (hb : b < w) :
    evalWire n gs x w = (evalWire n gs x a && evalWire n gs x b) := by
  rw [evalWire]; simp [h, hg, ha, hb]

lemma evalWire_or (n : ℕ) (gs : List MGate) (x : Fin n → Bool) (w a b : ℕ)
    (h : ¬ w < n) (hg : gs[w - n]? = some (MGate.or a b)) (ha : a < w) (hb : b < w) :
    evalWire n gs x w = (evalWire n gs x a || evalWire n gs x b) := by
  rw [evalWire]; simp [h, hg, ha, hb]

lemma evalWire_mono (n : ℕ) (gs : List MGate) (x y : Fin n → Bool)
    (hxy : ∀ i : Fin n, x i = true → y i = true) :
    ∀ w : ℕ, evalWire n gs x w = true → evalWire n gs y w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hx
    by_cases hw : w < n
    · rw [evalWire_lt n gs x w hw] at hx
      rw [evalWire_lt n gs y w hw]
      exact hxy ⟨w, hw⟩ hx
    · cases hg : gs[w - n]? with
      | none => rw [evalWire_none n gs x w hw hg] at hx; cases hx
      | some g =>
        cases g with
        | cFalse => rw [evalWire_cFalse n gs x w hw hg] at hx; cases hx
        | cTrue => exact evalWire_cTrue n gs y w hw hg
        | copy a =>
          rw [evalWire] at hx ⊢
          simp only [hw, ↓reduceDIte, hg] at hx ⊢
          by_cases ha : a < w <;> simp_all
        | and a b =>
          rw [evalWire] at hx ⊢
          simp only [hw, ↓reduceDIte, hg, Bool.and_eq_true] at hx ⊢
          by_cases ha : a < w <;> by_cases hb : b < w <;> simp_all
        | or a b =>
          rw [evalWire] at hx ⊢
          simp only [hw, ↓reduceDIte, hg, Bool.or_eq_true] at hx ⊢
          by_cases ha : a < w <;> by_cases hb : b < w <;> simp_all
          exact hx.elim (fun h1 => Or.inl (ih a ha h1)) (fun h2 => Or.inr (ih b hb h2))

def ofGateAt (w : ℕ) (g : Gate) : MGate :=
  match g.op, g.inputs with
  | GateOp.and, [] => MGate.cTrue
  | GateOp.and, [a] => if a < w then MGate.copy a else MGate.cFalse
  | GateOp.and, [a, b] => if a < w ∧ b < w then MGate.and a b else MGate.cFalse
  | GateOp.or, [] => MGate.cFalse
  | GateOp.or, [a] => if a < w then MGate.copy a else MGate.cFalse
  | GateOp.or, [a, b] =>
      if a < w then (if b < w then MGate.or a b else MGate.copy a)
      else (if b < w then MGate.copy b else MGate.cFalse)
  | _, _ => MGate.cFalse

def translateGates (n : ℕ) (gs : List Gate) : List MGate :=
  gs.mapIdx (fun j g => ofGateAt (n + j) g)

lemma translateGates_length (n : ℕ) (gs : List Gate) :
    (translateGates n gs).length = gs.length := by
  simp [translateGates]

lemma translateGates_getElem? (n : ℕ) (gs : List Gate) (j : ℕ) :
    (translateGates n gs)[j]? = (gs[j]?).map (ofGateAt (n + j)) := by
  simp [translateGates, List.getElem?_mapIdx]

lemma translateGates_wf (n : ℕ) (gs : List Gate) : WF n (translateGates n gs) := by
  intro j mg hmg
  rw [translateGates_getElem?] at hmg
  cases hg : gs[j]? with
  | none => simp [hg] at hmg
  | some g =>
    simp [hg] at hmg
    subst hmg
    unfold ofGateAt
    cases g.op with
    | and =>
      cases g.inputs with
      | nil => trivial
      | cons a l =>
        cases l with
        | nil => dsimp only []; split_ifs with ha <;> simp [ha]
        | cons b l2 =>
          cases l2 with
          | nil => dsimp only []; split_ifs with hab <;> simp [hab]
          | cons c l3 => trivial
    | or =>
      cases g.inputs with
      | nil => trivial
      | cons a l =>
        cases l with
        | nil => dsimp only []; split_ifs with ha <;> simp [ha]
        | cons b l2 =>
          cases l2 with
          | nil => dsimp only []; split_ifs <;> simp_all
          | cons c l3 => trivial
    | not => trivial
    | mod m => trivial
    | maj => trivial

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    change wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) = _
    rw [ht]; simp

lemma length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

lemma getD_wiresFrom_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ hi]

lemma evalWire_take (n : ℕ) (gs : List MGate) (x : Fin n → Bool) (k : ℕ) :
    ∀ w : ℕ, w < n + k → evalWire n (gs.take k) x w = evalWire n gs x w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hwk
    by_cases hw : w < n
    · rw [evalWire_lt n _ x w hw, evalWire_lt n _ x w hw]
    · have hlt : w - n < k := by omega
      have hget : (gs.take k)[w - n]? = gs[w - n]? := List.getElem?_take_of_lt hlt
      rw [evalWire, evalWire]
      simp only [hw, ↓reduceDIte, hget]
      cases gs[w - n]? with
      | none => rfl
      | some g =>
        cases g with
        | cFalse => rfl
        | cTrue => rfl
        | copy a =>
          dsimp only []
          split_ifs with ha
          · exact ih a ha (by omega)
          · rfl
        | and a b =>
          dsimp only []
          congr 1
          · split_ifs with ha
            · exact ih a ha (by omega)
            · rfl
          · split_ifs with hb
            · exact ih b hb (by omega)
            · rfl
        | or a b =>
          dsimp only []
          congr 1
          · split_ifs with ha
            · exact ih a ha (by omega)
            · rfl
          · split_ifs with hb
            · exact ih b hb (by omega)
            · rfl

lemma translateGates_take (n : ℕ) (gs : List Gate) (k : ℕ) :
    translateGates n (gs.take k) = (translateGates n gs).take k := by
  apply List.ext_getElem?
  intro j
  rw [translateGates_getElem?, List.getElem?_take]
  split_ifs with hj
  · rw [List.getElem?_take_of_lt hj, translateGates_getElem?]
  · rw [List.getElem?_eq_none (by simp; omega)]
    rfl

lemma wiresFrom_eq_evalWire (n : ℕ) (gs : List Gate)
    (hmono : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (x : Fin n → Bool) :
    ∀ w : ℕ, (wiresFrom gs (List.ofFn x)).getD w false =
      evalWire n (translateGates n gs) x w := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro w
    simp only [wiresFrom, List.foldl_nil, translateGates, List.mapIdx_nil]
    by_cases hw : w < n
    · rw [evalWire_lt n [] x w hw]
      simp [hw]
    · rw [evalWire_none n [] x w hw (by simp)]
      rw [List.getD_eq_default _ _ (by simp; omega)]
  | append_singleton gs g ih =>
    have hmono_gs : ∀ g' ∈ gs,
        g'.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g'.inputs.length ≤ 2 :=
      fun g' hg' => hmono g' (List.mem_append_left _ hg')
    have hmono_g : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 :=
      hmono g (List.mem_append_right _ (by simp))
    have ih' := ih hmono_gs
    set ws := wiresFrom gs (List.ofFn x) with hws
    have hws_len : ws.length = n + gs.length := by
      rw [hws, length_wiresFrom, List.length_ofFn]
    have hstep : wiresFrom (gs ++ [g]) (List.ofFn x) =
        ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)] := by
      rw [wiresFrom_append, ← hws]; rfl
    have htake : (translateGates n (gs ++ [g])).take gs.length = translateGates n gs := by
      rw [← translateGates_take]
      congr 1
      simp
    intro w
    rw [hstep]
    by_cases hlt : w < n + gs.length
    · rw [List.getD_append _ _ _ _ (by omega), ih' w, ← htake, evalWire_take n _ x gs.length w hlt]
    · by_cases heq : w = n + gs.length
      · subst heq
        have hgetD : (ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]).getD
            (n + gs.length) false = g.op.eval (g.inputs.map fun i => ws.getD i false) := by
          rw [← hws_len]; simp
        rw [hgetD]
        have hnotlt : ¬ (n + gs.length < n) := by omega
        have hsub : n + gs.length - n = gs.length := by omega
        have hmg : (translateGates n (gs ++ [g]))[n + gs.length - n]? =
            some (ofGateAt (n + gs.length) g) := by
          rw [hsub, translateGates_getElem?]
          simp
        have hread : ∀ a : ℕ, ws.getD a false =
            if a < n + gs.length then evalWire n (translateGates n (gs ++ [g])) x a else false := by
          intro a
          split_ifs with ha
          · rw [ih' a, ← htake, evalWire_take n _ x gs.length a ha]
          · rw [List.getD_eq_default _ _ (by omega)]
        rw [evalWire]
        simp only [hnotlt, ↓reduceDIte, hmg]
        rcases hmono_g with ⟨hop, hlen⟩
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
        rcases hop with hop | hop
        · rw [hop]
          unfold ofGateAt
          rw [hop]
          cases h_in : g.inputs with
          | nil => simp [GateOp.eval]
          | cons a l =>
            cases l with
            | nil =>
              simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
                id_eq, Bool.and_true, hread a]
              split_ifs <;> simp_all
            | cons b l2 =>
              cases l2 with
              | nil =>
                simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
                  id_eq, Bool.and_true, hread a, hread b]
                split_ifs with h1 h2 h3 <;> simp_all
              | cons c l3 => simp [h_in] at hlen
        · rw [hop]
          unfold ofGateAt
          rw [hop]
          cases h_in : g.inputs with
          | nil => simp [GateOp.eval]
          | cons a l =>
            cases l with
            | nil =>
              simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
                id_eq, Bool.or_false, hread a]
              split_ifs <;> simp_all
            | cons b l2 =>
              cases l2 with
              | nil =>
                simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
                  id_eq, Bool.or_false, hread a, hread b]
                split_ifs with h1 h2 <;> simp_all
              | cons c l3 => simp [h_in] at hlen
      · have hgt : n + gs.length < w := by omega
        rw [List.getD_eq_default _ _ (by simp [hws_len]; omega)]
        rw [evalWire_none n _ x w (by omega)]
        rw [List.getElem?_eq_none (by rw [translateGates_length]; simp; omega)]

def orIndices (gs : List MGate) : Finset ℕ :=
  (Finset.range gs.length).filter (fun j => (gs[j]?.map MGate.isOr).getD false = true)

lemma mem_orIndices {gs : List MGate} {j : ℕ} :
    j ∈ orIndices gs ↔ ∃ a b : ℕ, gs[j]? = some (MGate.or a b) := by
  simp only [orIndices, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨_, h⟩
    cases hg : gs[j]? with
    | none => simp [hg] at h
    | some g =>
      cases g <;> simp [hg, MGate.isOr] at h
      exact ⟨_, _, rfl⟩
  · rintro ⟨a, b, hg⟩
    refine ⟨?_, by simp [hg, MGate.isOr]⟩
    by_contra hlt
    rw [List.getElem?_eq_none (by omega)] at hg
    cases hg

lemma orIndices_translate_subset (n : ℕ) (C : Circuit) (A : Finset ℕ)
    (hA : ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → g.op = GateOp.or → j ∈ A) :
    orIndices (translateGates n C.gates) ⊆ A := by
  intro j hj
  obtain ⟨a, b, hab⟩ := mem_orIndices.mp hj
  rw [translateGates_getElem?] at hab
  cases hg : C.gates[j]? with
  | none => simp [hg] at hab
  | some g =>
    simp [hg] at hab
    apply hA j g hg
    unfold ofGateAt at hab
    cases hop : g.op with
    | or => rfl
    | and =>
      simp only [hop] at hab
      cases h_in : g.inputs with
      | nil => simp [h_in] at hab
      | cons x l =>
        cases l with
        | nil => simp [h_in] at hab; split_ifs at hab
        | cons y l2 =>
          cases l2 with
          | nil => simp [h_in] at hab; split_ifs at hab
          | cons z l3 => simp [h_in] at hab
    | not => simp [hop] at hab
    | mod m => simp [hop] at hab
    | maj => simp [hop] at hab

-- Weight-<=2 inputs and predicates

def zeroIn (n : ℕ) : Fin n → Bool := fun _ => false
def singleIn {n : ℕ} (u : Fin n) : Fin n → Bool := fun i => decide (i = u)
def pairIn {n : ℕ} (u v : Fin n) : Fin n → Bool := fun i => decide (i = u ∨ i = v)
def setFalse {n : ℕ} (v : Fin n) (x : Fin n → Bool) : Fin n → Bool :=
  fun i => if i = v then false else x i
def setTrue {n : ℕ} (v : Fin n) (x : Fin n → Bool) : Fin n → Bool :=
  fun i => if i = v then true else x i

def WtLe2 {n : ℕ} (x : Fin n → Bool) : Prop :=
  (Finset.univ.filter (fun i : Fin n => x i = true)).card ≤ 2

lemma wtLe2_zeroIn (n : ℕ) : WtLe2 (zeroIn n) := by
  simp [WtLe2, zeroIn]

lemma wtLe2_singleIn {n : ℕ} (u : Fin n) : WtLe2 (singleIn u) := by
  have h : Finset.univ.filter (fun i : Fin n => singleIn u i = true) = {u} := by
    ext i; simp [singleIn]
  rw [WtLe2, h]; simp

lemma wtLe2_pairIn {n : ℕ} (u v : Fin n) : WtLe2 (pairIn u v) := by
  have h : Finset.univ.filter (fun i : Fin n => pairIn u v i = true) = {u, v} := by
    ext i; simp [pairIn]
  rw [WtLe2, h]
  exact Finset.card_le_two

lemma wtLe2_setFalse {n : ℕ} (v : Fin n) (x : Fin n → Bool) (hx : WtLe2 x) :
    WtLe2 (setFalse v x) := by
  refine le_trans (Finset.card_le_card ?_) hx
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  dsimp only [setFalse] at hi
  by_cases hiv : i = v
  · simp [hiv] at hi
  · simpa [hiv] using hi

def ZeroV (n : ℕ) (gs : List MGate) (v : Fin n) (w : ℕ) : Prop :=
  ∀ x : Fin n → Bool, WtLe2 x → x v = false → evalWire n gs x w = false

lemma zeroV_input_self (n : ℕ) (gs : List MGate) (v : Fin n) : ZeroV n gs v v.val := by
  intro x _ hxv
  rw [evalWire_lt n gs x v.val v.isLt]
  exact hxv

lemma not_zeroV_input_ne (n : ℕ) (gs : List MGate) (v u : Fin n) (huv : u ≠ v) :
    ¬ ZeroV n gs v u.val := by
  intro h
  have h1 := h (singleIn u) (wtLe2_singleIn u) (by simp [singleIn, huv.symm])
  rw [evalWire_lt n gs (singleIn u) u.val u.isLt] at h1
  simp [singleIn] at h1

lemma zeroV_copy {n : ℕ} {gs : List MGate} {v : Fin n} {w a : ℕ}
    (hw : ¬ w < n) (hg : gs[w - n]? = some (MGate.copy a)) (ha : a < w)
    (hza : ZeroV n gs v a) : ZeroV n gs v w := by
  intro x hx hxv
  rw [evalWire_copy n gs x w a hw hg ha]
  exact hza x hx hxv

lemma zeroV_and_left {n : ℕ} {gs : List MGate} {v : Fin n} {w a b : ℕ}
    (hw : ¬ w < n) (hg : gs[w - n]? = some (MGate.and a b)) (ha : a < w) (hb : b < w)
    (hza : ZeroV n gs v a) : ZeroV n gs v w := by
  intro x hx hxv
  rw [evalWire_and n gs x w a b hw hg ha hb, hza x hx hxv]
  rfl

lemma zeroV_and_right {n : ℕ} {gs : List MGate} {v : Fin n} {w a b : ℕ}
    (hw : ¬ w < n) (hg : gs[w - n]? = some (MGate.and a b)) (ha : a < w) (hb : b < w)
    (hzb : ZeroV n gs v b) : ZeroV n gs v w := by
  intro x hx hxv
  rw [evalWire_and n gs x w a b hw hg ha hb, hzb x hx hxv]
  simp

lemma zeroV_or {n : ℕ} {gs : List MGate} {v : Fin n} {w a b : ℕ}
    (hw : ¬ w < n) (hg : gs[w - n]? = some (MGate.or a b)) (ha : a < w) (hb : b < w)
    (hza : ZeroV n gs v a) (hzb : ZeroV n gs v b) : ZeroV n gs v w := by
  intro x hx hxv
  rw [evalWire_or n gs x w a b hw hg ha hb, hza x hx hxv, hzb x hx hxv]
  rfl

noncomputable def killedOrs (n : ℕ) (gs : List MGate) (v : Fin n) : Finset ℕ :=
  open Classical in
  (Finset.range gs.length).filter (fun j =>
    match gs[j]? with
    | some (MGate.or a b) => ZeroV n gs v (n + j) ∨ ZeroV n gs v a ∨ ZeroV n gs v b
    | _ => false)

lemma mem_killedOrs {n : ℕ} {gs : List MGate} {v : Fin n} {j : ℕ} :
    j ∈ killedOrs n gs v ↔
      ∃ a b : ℕ, gs[j]? = some (MGate.or a b) ∧
        (ZeroV n gs v (n + j) ∨ ZeroV n gs v a ∨ ZeroV n gs v b) := by
  classical
  simp only [killedOrs, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨_, h⟩
    cases hg : gs[j]? with
    | none => simp [hg] at h
    | some g =>
      cases g <;> simp [hg] at h
      exact ⟨_, _, rfl, h⟩
  · rintro ⟨a, b, hg, h⟩
    refine ⟨?_, by simp [hg, h]⟩
    by_contra hlt
    rw [List.getElem?_eq_none (by omega)] at hg
    cases hg

lemma killedOrs_subset_orIndices (n : ℕ) (gs : List MGate) (v : Fin n) :
    killedOrs n gs v ⊆ orIndices gs := by
  intro j hj
  obtain ⟨a, b, hg, _⟩ := mem_killedOrs.mp hj
  exact mem_orIndices.mpr ⟨a, b, hg⟩

-- Restriction of circuit by setting v := false and folding all ZeroV wires

noncomputable def restrictGate (n : ℕ) (gs : List MGate) (v : Fin n) (j : ℕ) (g : MGate) : MGate :=
  open Classical in
  if ZeroV n gs v (n + j) then MGate.cFalse
  else
    match g with
    | MGate.or a b =>
        if ZeroV n gs v a then MGate.copy b
        else if ZeroV n gs v b then MGate.copy a
        else MGate.or a b
    | g => g

noncomputable def restrictZero (n : ℕ) (gs : List MGate) (v : Fin n) : List MGate :=
  gs.mapIdx (restrictGate n gs v)

lemma restrictZero_length (n : ℕ) (gs : List MGate) (v : Fin n) :
    (restrictZero n gs v).length = gs.length := by
  simp [restrictZero]

lemma restrictZero_getElem? (n : ℕ) (gs : List MGate) (v : Fin n) (j : ℕ) :
    (restrictZero n gs v)[j]? = (gs[j]?).map (restrictGate n gs v j) := by
  simp [restrictZero, List.getElem?_mapIdx]

lemma restrictZero_wf (n : ℕ) (gs : List MGate) (v : Fin n) (hwf : WF n gs) :
    WF n (restrictZero n gs v) := by
  classical
  intro j mg hmg
  rw [restrictZero_getElem?] at hmg
  cases hg : gs[j]? with
  | none => simp [hg] at hmg
  | some g =>
    simp [hg] at hmg
    subst hmg
    have hwfj := hwf j g hg
    unfold restrictGate
    split_ifs with h0
    · trivial
    · cases g with
      | cFalse => trivial
      | cTrue => trivial
      | copy a => exact hwfj
      | and a b => exact hwfj
      | or a b =>
        simp only []
        split_ifs with h1 h2
        · exact hwfj.2
        · exact hwfj.1
        · exact hwfj

lemma orIndices_restrictZero_subset (n : ℕ) (gs : List MGate) (v : Fin n) :
    orIndices (restrictZero n gs v) ⊆ orIndices gs \ killedOrs n gs v := by
  classical
  intro j hj
  obtain ⟨a, b, hab⟩ := mem_orIndices.mp hj
  rw [restrictZero_getElem?] at hab
  cases hg : gs[j]? with
  | none => simp [hg] at hab
  | some g =>
    simp [hg] at hab
    unfold restrictGate at hab
    split_ifs at hab with hz
    cases g <;> simp at hab
    split_ifs at hab with hza hzb
    rcases hab with ⟨rfl, rfl⟩
    rw [Finset.mem_sdiff]
    refine ⟨mem_orIndices.mpr ⟨a, b, hg⟩, ?_⟩
    intro hk
    obtain ⟨a', b', hg', hor⟩ := mem_killedOrs.mp hk
    rw [hg] at hg'
    cases hg'
    rcases hor with hz' | hza' | hzb'
    · exact hz hz'
    · exact hza hza'
    · exact hzb hzb'

lemma evalWire_restrictZero (n : ℕ) (gs : List MGate) (v : Fin n) (hwf : WF n gs)
    (x : Fin n → Bool) (hx : WtLe2 x) :
    ∀ w : ℕ, ¬ ZeroV n gs v w →
      evalWire n (restrictZero n gs v) x w = evalWire n gs (setFalse v x) w := by
  classical
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hnz
    have hx' : WtLe2 (setFalse v x) := wtLe2_setFalse v x hx
    have hxv' : setFalse v x v = false := by simp [setFalse]
    by_cases hw : w < n
    · rw [evalWire_lt n _ x w hw, evalWire_lt n _ (setFalse v x) w hw]
      have hne : (⟨w, hw⟩ : Fin n) ≠ v := by
        intro heq
        apply hnz
        have : w = v.val := congrArg Fin.val heq
        rw [this]
        exact zeroV_input_self n gs v
      simp [setFalse, hne]
    · cases hg : gs[w - n]? with
      | none =>
        rw [evalWire_none n gs (setFalse v x) w hw hg]
        rw [evalWire_none n (restrictZero n gs v) x w hw (by rw [restrictZero_getElem?, hg]; rfl)]
      | some g =>
        have hwfj := hwf (w - n) g hg
        have hwn : n + (w - n) = w := by omega
        rw [hwn] at hwfj
        have hrg : (restrictZero n gs v)[w - n]? = some (restrictGate n gs v (w - n) g) := by
          rw [restrictZero_getElem?, hg]; rfl
        have hnz' : ¬ ZeroV n gs v (n + (w - n)) := by rw [hwn]; exact hnz
        cases g with
        | cFalse =>
          exfalso; apply hnz
          intro y _ _; exact evalWire_cFalse n gs y w hw hg
        | cTrue =>
          rw [evalWire_cTrue n gs (setFalse v x) w hw hg]
          rw [evalWire_cTrue n (restrictZero n gs v) x w hw]
          rw [hrg]; simp [restrictGate, hnz']
        | copy a =>
          have hnza : ¬ ZeroV n gs v a := fun hza => hnz (zeroV_copy hw hg hwfj hza)
          rw [evalWire_copy n gs (setFalse v x) w a hw hg hwfj]
          rw [evalWire_copy n (restrictZero n gs v) x w a hw (by rw [hrg]; simp [restrictGate, hnz']) hwfj]
          exact ih a hwfj hnza
        | and a b =>
          have hnza : ¬ ZeroV n gs v a := fun hza => hnz (zeroV_and_left hw hg hwfj.1 hwfj.2 hza)
          have hnzb : ¬ ZeroV n gs v b := fun hzb => hnz (zeroV_and_right hw hg hwfj.1 hwfj.2 hzb)
          rw [evalWire_and n gs (setFalse v x) w a b hw hg hwfj.1 hwfj.2]
          rw [evalWire_and n (restrictZero n gs v) x w a b hw (by rw [hrg]; simp [restrictGate, hnz']) hwfj.1 hwfj.2]
          rw [ih a hwfj.1 hnza, ih b hwfj.2 hnzb]
        | or a b =>
          rw [evalWire_or n gs (setFalse v x) w a b hw hg hwfj.1 hwfj.2]
          by_cases hza : ZeroV n gs v a
          · have hnzb : ¬ ZeroV n gs v b := fun hzb => hnz (zeroV_or hw hg hwfj.1 hwfj.2 hza hzb)
            rw [evalWire_copy n (restrictZero n gs v) x w b hw
              (by rw [hrg]; simp [restrictGate, hnz', hza]) hwfj.2]
            rw [hza (setFalse v x) hx' hxv', Bool.false_or, ih b hwfj.2 hnzb]
          · by_cases hzb : ZeroV n gs v b
            · rw [evalWire_copy n (restrictZero n gs v) x w a hw
                (by rw [hrg]; simp [restrictGate, hnz', hza, hzb]) hwfj.1]
              rw [hzb (setFalse v x) hx' hxv', Bool.or_false, ih a hwfj.1 hza]
            · rw [evalWire_or n (restrictZero n gs v) x w a b hw
                (by rw [hrg]; simp [restrictGate, hnz', hza, hzb]) hwfj.1 hwfj.2]
              rw [ih a hwfj.1 hza, ih b hwfj.2 hzb]

-- Escape lemma: if no OR gate <= w is in killedOrs v, then non-ZeroV wires <= w don't see v

lemma escape_lemma (n : ℕ) (gs : List MGate) (v : Fin n) (hwf : WF n gs)
    (x y : Fin n → Bool) (hxy : ∀ i : Fin n, i ≠ v → x i = y i)
    (bound : ℕ) (hno : ∀ j ∈ killedOrs n gs v, bound < n + j) :
    ∀ w : ℕ, w ≤ bound → ¬ ZeroV n gs v w →
      evalWire n gs x w = evalWire n gs y w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hwb hnz
    by_cases hw : w < n
    · rw [evalWire_lt n gs x w hw, evalWire_lt n gs y w hw]
      apply hxy ⟨w, hw⟩
      intro heq
      apply hnz
      have : w = v.val := congrArg Fin.val heq
      rw [this]
      exact zeroV_input_self n gs v
    · cases hg : gs[w - n]? with
      | none =>
        rw [evalWire_none n gs x w hw hg, evalWire_none n gs y w hw hg]
      | some g =>
        have hwfj := hwf (w - n) g hg
        have hwn : n + (w - n) = w := by omega
        rw [hwn] at hwfj
        cases g with
        | cFalse => rw [evalWire_cFalse n gs x w hw hg, evalWire_cFalse n gs y w hw hg]
        | cTrue => rw [evalWire_cTrue n gs x w hw hg, evalWire_cTrue n gs y w hw hg]
        | copy a =>
          have hnza : ¬ ZeroV n gs v a := fun hza => hnz (zeroV_copy hw hg hwfj hza)
          rw [evalWire_copy n gs x w a hw hg hwfj, evalWire_copy n gs y w a hw hg hwfj]
          exact ih a hwfj (by omega) hnza
        | and a b =>
          have hnza : ¬ ZeroV n gs v a := fun hza => hnz (zeroV_and_left hw hg hwfj.1 hwfj.2 hza)
          have hnzb : ¬ ZeroV n gs v b := fun hzb => hnz (zeroV_and_right hw hg hwfj.1 hwfj.2 hzb)
          rw [evalWire_and n gs x w a b hw hg hwfj.1 hwfj.2,
              evalWire_and n gs y w a b hw hg hwfj.1 hwfj.2]
          rw [ih a hwfj.1 (by omega) hnza, ih b hwfj.2 (by omega) hnzb]
        | or a b =>
          have hnotk : w - n ∉ killedOrs n gs v := by
            intro hk
            have := hno (w - n) hk
            omega
          have hnza : ¬ ZeroV n gs v a := fun hza =>
            hnotk (mem_killedOrs.mpr ⟨a, b, hg, Or.inr (Or.inl hza)⟩)
          have hnzb : ¬ ZeroV n gs v b := fun hzb =>
            hnotk (mem_killedOrs.mpr ⟨a, b, hg, Or.inr (Or.inr hzb)⟩)
          rw [evalWire_or n gs x w a b hw hg hwfj.1 hwfj.2,
              evalWire_or n gs y w a b hw hg hwfj.1 hwfj.2]
          rw [ih a hwfj.1 (by omega) hnza, ih b hwfj.2 (by omega) hnzb]

-- Unique-gate agreement lemma: if killedOrs v = {j*} and at g* = n + j* the two inputs give
-- the same value (or if every OR gate with ¬ ZeroV g has ¬ ZeroV inputs except at j*),
-- then all non-ZeroV wires agree on x and y.

lemma agree_outside_unique (n : ℕ) (gs : List MGate) (v : Fin n) (hwf : WF n gs)
    (j0 : ℕ) (huniq : ∀ j ∈ killedOrs n gs v, j = j0)
    (x y : Fin n → Bool) (hxy : ∀ i : Fin n, i ≠ v → x i = y i)
    (hgate : ¬ ZeroV n gs v (n + j0) →
      (∀ w < n + j0, ¬ ZeroV n gs v w → evalWire n gs x w = evalWire n gs y w) →
      evalWire n gs x (n + j0) = evalWire n gs y (n + j0)) :
    ∀ w : ℕ, ¬ ZeroV n gs v w → evalWire n gs x w = evalWire n gs y w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hnz
    by_cases hw : w < n
    · rw [evalWire_lt n gs x w hw, evalWire_lt n gs y w hw]
      apply hxy ⟨w, hw⟩
      intro heq
      apply hnz
      have : w = v.val := congrArg Fin.val heq
      rw [this]
      exact zeroV_input_self n gs v
    · by_cases hj0 : w = n + j0
      · subst hj0
        exact hgate hnz ih
      · cases hg : gs[w - n]? with
        | none =>
          rw [evalWire_none n gs x w hw hg, evalWire_none n gs y w hw hg]
        | some g =>
          have hwfj := hwf (w - n) g hg
          have hwn : n + (w - n) = w := by omega
          rw [hwn] at hwfj
          cases g with
          | cFalse => rw [evalWire_cFalse n gs x w hw hg, evalWire_cFalse n gs y w hw hg]
          | cTrue => rw [evalWire_cTrue n gs x w hw hg, evalWire_cTrue n gs y w hw hg]
          | copy a =>
            have hnza : ¬ ZeroV n gs v a := fun hza => hnz (zeroV_copy hw hg hwfj hza)
            rw [evalWire_copy n gs x w a hw hg hwfj, evalWire_copy n gs y w a hw hg hwfj]
            exact ih a hwfj hnza
          | and a b =>
            have hnza : ¬ ZeroV n gs v a := fun hza => hnz (zeroV_and_left hw hg hwfj.1 hwfj.2 hza)
            have hnzb : ¬ ZeroV n gs v b := fun hzb => hnz (zeroV_and_right hw hg hwfj.1 hwfj.2 hzb)
            rw [evalWire_and n gs x w a b hw hg hwfj.1 hwfj.2,
                evalWire_and n gs y w a b hw hg hwfj.1 hwfj.2]
            rw [ih a hwfj.1 hnza, ih b hwfj.2 hnzb]
          | or a b =>
            have hnotk : w - n ∉ killedOrs n gs v := by
              intro hk
              have := huniq (w - n) hk
              omega
            have hnza : ¬ ZeroV n gs v a := fun hza =>
              hnotk (mem_killedOrs.mpr ⟨a, b, hg, Or.inr (Or.inl hza)⟩)
            have hnzb : ¬ ZeroV n gs v b := fun hzb =>
              hnotk (mem_killedOrs.mpr ⟨a, b, hg, Or.inr (Or.inr hzb)⟩)
            rw [evalWire_or n gs x w a b hw hg hwfj.1 hwfj.2,
                evalWire_or n gs y w a b hw hg hwfj.1 hwfj.2]
            rw [ih a hwfj.1 hnza, ih b hwfj.2 hnzb]

-- Replacing gate j0 = or a b with copy c (where c is a or b)

def replaceWithCopy (gs : List MGate) (j0 c : ℕ) : List MGate :=
  gs.mapIdx (fun j g => if j = j0 then MGate.copy c else g)

lemma replaceWithCopy_getElem? (gs : List MGate) (j0 c j : ℕ) :
    (replaceWithCopy gs j0 c)[j]? =
      (gs[j]?).map (fun g => if j = j0 then MGate.copy c else g) := by
  simp [replaceWithCopy, List.getElem?_mapIdx]

lemma replaceWithCopy_wf (n : ℕ) (gs : List MGate) (j0 c : ℕ) (hwf : WF n gs)
    (hc : c < n + j0) : WF n (replaceWithCopy gs j0 c) := by
  intro j mg hmg
  rw [replaceWithCopy_getElem?] at hmg
  cases hg : gs[j]? with
  | none => simp [hg] at hmg
  | some g =>
    simp [hg] at hmg
    subst hmg
    split_ifs with hj
    · subst hj; exact hc
    · exact hwf j g hg

lemma orIndices_replaceWithCopy_subset (gs : List MGate) (j0 c : ℕ) :
    orIndices (replaceWithCopy gs j0 c) ⊆ (orIndices gs).erase j0 := by
  intro j hj
  obtain ⟨a, b, hab⟩ := mem_orIndices.mp hj
  rw [replaceWithCopy_getElem?] at hab
  cases hg : gs[j]? with
  | none => simp [hg] at hab
  | some g =>
    simp [hg] at hab
    by_cases hjj : j = j0
    · simp [hjj] at hab
    · simp [hjj] at hab
      subst hab
      exact Finset.mem_erase.mpr ⟨hjj, mem_orIndices.mpr ⟨a, b, hg⟩⟩

lemma evalWire_replaceWithCopy_le (n : ℕ) (gs : List MGate) (j0 c a b : ℕ) (hwf : WF n gs)
    (hj0 : gs[j0]? = some (MGate.or a b)) (hc : c = a ∨ c = b) (x : Fin n → Bool) :
    ∀ w : ℕ, evalWire n (replaceWithCopy gs j0 c) x w = true → evalWire n gs x w = true := by
  have hwf0 := hwf j0 (MGate.or a b) hj0
  have hclt : c < n + j0 := by rcases hc with rfl | rfl; exact hwf0.1; exact hwf0.2
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro htrue
    by_cases hw : w < n
    · rw [evalWire_lt n _ x w hw] at htrue ⊢; exact htrue
    · by_cases heq : w = n + j0
      · subst heq
        have hrg : (replaceWithCopy gs j0 c)[n + j0 - n]? = some (MGate.copy c) := by
          rw [Nat.add_sub_cancel_left, replaceWithCopy_getElem?, hj0]; simp
        rw [evalWire_copy n _ x (n + j0) c hw hrg hclt] at htrue
        rw [evalWire_or n gs x (n + j0) a b hw (by rw [Nat.add_sub_cancel_left]; exact hj0) hwf0.1 hwf0.2]
        have h1 := ih c hclt htrue
        rcases hc with rfl | rfl
        · simp [h1]
        · simp [h1]
      · cases hg : gs[w - n]? with
        | none =>
          rw [evalWire_none n _ x w hw (by rw [replaceWithCopy_getElem?, hg]; rfl)] at htrue
          cases htrue
        | some g =>
          have hne : w - n ≠ j0 := by omega
          have hrg : (replaceWithCopy gs j0 c)[w - n]? = some g := by
            rw [replaceWithCopy_getElem?, hg]; simp [hne]
          have hwfj := hwf (w - n) g hg
          have hwn : n + (w - n) = w := by omega
          rw [hwn] at hwfj
          cases g with
          | cFalse => rw [evalWire_cFalse n _ x w hw hrg] at htrue; cases htrue
          | cTrue => exact evalWire_cTrue n gs x w hw hg
          | copy d =>
            rw [evalWire_copy n _ x w d hw hrg hwfj] at htrue
            rw [evalWire_copy n gs x w d hw hg hwfj]
            exact ih d hwfj htrue
          | and d e =>
            rw [evalWire_and n _ x w d e hw hrg hwfj.1 hwfj.2, Bool.and_eq_true] at htrue
            rw [evalWire_and n gs x w d e hw hg hwfj.1 hwfj.2, Bool.and_eq_true]
            exact ⟨ih d hwfj.1 htrue.1, ih e hwfj.2 htrue.2⟩
          | or d e =>
            rw [evalWire_or n _ x w d e hw hrg hwfj.1 hwfj.2, Bool.or_eq_true] at htrue
            rw [evalWire_or n gs x w d e hw hg hwfj.1 hwfj.2, Bool.or_eq_true]
            rcases htrue with h1 | h2
            · exact Or.inl (ih d hwfj.1 h1)
            · exact Or.inr (ih e hwfj.2 h2)

lemma evalWire_replaceWithCopy_eq (n : ℕ) (gs : List MGate) (j0 c : ℕ) (hwf : WF n gs)
    (hj0 : gs[j0]?.isSome) (hclt : c < n + j0) (x : Fin n → Bool)
    (hmatch : evalWire n gs x (n + j0) = evalWire n gs x c) :
    ∀ w : ℕ, evalWire n (replaceWithCopy gs j0 c) x w = evalWire n gs x w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hw : w < n
    · rw [evalWire_lt n _ x w hw, evalWire_lt n _ x w hw]
    · by_cases heq : w = n + j0
      · subst heq
        obtain ⟨g0, hg0⟩ := Option.isSome_iff_exists.mp hj0
        have hrg : (replaceWithCopy gs j0 c)[n + j0 - n]? = some (MGate.copy c) := by
          rw [Nat.add_sub_cancel_left, replaceWithCopy_getElem?, hg0]; simp
        rw [evalWire_copy n _ x (n + j0) c hw hrg hclt, ih c hclt, ← hmatch]
      · cases hg : gs[w - n]? with
        | none =>
          rw [evalWire_none n _ x w hw (by rw [replaceWithCopy_getElem?, hg]; rfl),
              evalWire_none n gs x w hw hg]
        | some g =>
          have hne : w - n ≠ j0 := by omega
          have hrg : (replaceWithCopy gs j0 c)[w - n]? = some g := by
            rw [replaceWithCopy_getElem?, hg]; simp [hne]
          have hwfj := hwf (w - n) g hg
          have hwn : n + (w - n) = w := by omega
          rw [hwn] at hwfj
          cases g with
          | cFalse => rw [evalWire_cFalse n _ x w hw hrg, evalWire_cFalse n gs x w hw hg]
          | cTrue => rw [evalWire_cTrue n _ x w hw hrg, evalWire_cTrue n gs x w hw hg]
          | copy d =>
            rw [evalWire_copy n _ x w d hw hrg hwfj, evalWire_copy n gs x w d hw hg hwfj]
            exact ih d hwfj
          | and d e =>
            rw [evalWire_and n _ x w d e hw hrg hwfj.1 hwfj.2,
                evalWire_and n gs x w d e hw hg hwfj.1 hwfj.2]
            rw [ih d hwfj.1, ih e hwfj.2]
          | or d e =>
            rw [evalWire_or n _ x w d e hw hrg hwfj.1 hwfj.2,
                evalWire_or n gs x w d e hw hg hwfj.1 hwfj.2]
            rw [ih d hwfj.1, ih e hwfj.2]

-- Graph predicates and vertex deletion

def ComputesW2 {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List MGate) (out : ℕ) : Prop :=
  evalWire n gs (zeroIn n) out = false ∧
  (∀ u : Fin n, evalWire n gs (singleIn u) out = false) ∧
  (∀ u v : Fin n, u ≠ v → (evalWire n gs (pairIn u v) out = true ↔ G.Adj u v))

def Uni {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  open Classical in
  ∀ S : Finset (Fin n),
    (G.edgeFinset.filter (fun e => ∀ v ∈ e, v ∈ S)).card ≤ S.card

def NoC4 {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∀ v w u₁ u₂ : Fin n, v ≠ w → u₁ ≠ u₂ →
    G.Adj v u₁ → G.Adj v u₂ → G.Adj w u₁ → G.Adj w u₂ → False

def delVert {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) : SimpleGraph (Fin n) where
  Adj a b := G.Adj a b ∧ a ≠ v ∧ b ≠ v
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun a h => G.loopless.irrefl a h.1⟩

lemma delVert_le {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) : delVert G v ≤ G :=
  fun _ _ h => h.1

lemma uni_of_le {n : ℕ} {G H : SimpleGraph (Fin n)} (hGH : G ≤ H) (hH : Uni H) : Uni G := by
  classical
  intro S
  refine le_trans (Finset.card_le_card ?_) (hH S)
  intro e he
  simp only [Finset.mem_filter, SimpleGraph.mem_edgeFinset] at he ⊢
  exact ⟨SimpleGraph.edgeSet_mono hGH he.1, he.2⟩

lemma noC4_of_le {n : ℕ} {G H : SimpleGraph (Fin n)} (hGH : G ≤ H) (hH : NoC4 H) : NoC4 G :=
  fun v w u₁ u₂ hvw hu h1 h2 h3 h4 => hH v w u₁ u₂ hvw hu (hGH h1) (hGH h2) (hGH h3) (hGH h4)

lemma delVert_edgeFinset_card {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) :
    open Classical in
    (delVert G v).edgeFinset.card + G.degree v = G.edgeFinset.card := by
  classical
  have hdisj : Disjoint (delVert G v).edgeFinset (G.incidenceFinset v) := by
    rw [Finset.disjoint_left]
    intro e he1 he2
    rw [SimpleGraph.mem_edgeFinset] at he1
    rw [SimpleGraph.mem_incidenceFinset] at he2
    induction e using Sym2.ind with
    | _ a b =>
      simp only [SimpleGraph.mem_edgeSet, delVert] at he1
      simp only [SimpleGraph.incidenceSet, Set.mem_ofPred_eq, Sym2.mem_iff] at he2
      rcases he2.2 with rfl | rfl
      · exact he1.2.1 rfl
      · exact he1.2.2 rfl
  have hunion : (delVert G v).edgeFinset ∪ G.incidenceFinset v = G.edgeFinset := by
    ext e
    simp only [Finset.mem_union, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_incidenceFinset]
    induction e using Sym2.ind with
    | _ a b =>
      simp only [SimpleGraph.incidenceSet, Set.mem_ofPred_eq, SimpleGraph.mem_edgeSet, delVert,
        Sym2.mem_iff]
      tauto
  rw [← G.card_incidenceFinset_eq_degree v, ← Finset.card_union_of_disjoint hdisj, hunion]

lemma computesW2_restrictZero {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List MGate) (out : ℕ)
    (v : Fin n) (hwf : WF n gs) (hcomp : ComputesW2 G gs out)
    (hnz : ¬ ZeroV n gs v out) :
    ComputesW2 (delVert G v) (restrictZero n gs v) out := by
  refine ⟨?_, ?_, ?_⟩
  · rw [evalWire_restrictZero n gs v hwf (zeroIn n) (wtLe2_zeroIn n) out hnz]
    have h0 : setFalse v (zeroIn n) = zeroIn n := by
      funext i; simp [setFalse, zeroIn]
    rw [h0]
    exact hcomp.1
  · intro u
    rw [evalWire_restrictZero n gs v hwf (singleIn u) (wtLe2_singleIn u) out hnz]
    by_cases huv : u = v
    · subst huv
      have h0 : setFalse u (singleIn u) = zeroIn n := by
        funext i; by_cases hi : i = u <;> simp [setFalse, singleIn, zeroIn, hi]
      rw [h0]; exact hcomp.1
    · have h1 : setFalse v (singleIn u) = singleIn u := by
        funext i; by_cases hi : i = v <;> simp [setFalse, singleIn, hi, Ne.symm huv]
      rw [h1]; exact hcomp.2.1 u
  · intro a b hab
    rw [evalWire_restrictZero n gs v hwf (pairIn a b) (wtLe2_pairIn a b) out hnz]
    by_cases hav : a = v
    · subst hav
      have h1 : setFalse a (pairIn a b) = singleIn b := by
        funext i; by_cases hi : i = a <;> simp [setFalse, pairIn, singleIn, hi, hab]
      rw [h1, hcomp.2.1 b]
      simp [delVert]
    · by_cases hbv : b = v
      · subst hbv
        have h1 : setFalse b (pairIn a b) = singleIn a := by
          funext i; by_cases hi : i = b <;> simp [setFalse, pairIn, singleIn, hi, Ne.symm hab]
        rw [h1, hcomp.2.1 a]
        simp [delVert]
      · have h1 : setFalse v (pairIn a b) = pairIn a b := by
          funext i; by_cases hi : i = v <;> simp [setFalse, pairIn, hi, Ne.symm hav, Ne.symm hbv]
        rw [h1, hcomp.2.2 a b hab]
        simp [delVert, hav, hbv]

lemma not_zeroV_out_of_delVert_pos {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List MGate) (out : ℕ)
    (v : Fin n) (hcomp : ComputesW2 G gs out)
    (hpos : open Classical in 0 < (delVert G v).edgeFinset.card) :
    ¬ ZeroV n gs v out := by
  classical
  obtain ⟨e, he⟩ := Finset.card_pos.mp hpos
  rw [SimpleGraph.mem_edgeFinset] at he
  induction e using Sym2.ind with
  | _ a b =>
    simp only [SimpleGraph.mem_edgeSet, delVert] at he
    intro hz
    have h1 := hz (pairIn a b) (wtLe2_pairIn a b)
      (by simp [pairIn, Ne.symm he.2.1, Ne.symm he.2.2])
    have h2 := (hcomp.2.2 a b he.1.ne).mpr he.1
    rw [h1] at h2
    cases h2

lemma killedOrs_nonempty_of_adj {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List MGate) (out : ℕ)
    (v u : Fin n) (hwf : WF n gs) (hcomp : ComputesW2 G gs out)
    (hadj : G.Adj v u) (hnz : ¬ ZeroV n gs v out) :
    (killedOrs n gs v).Nonempty := by
  by_contra hemp
  rw [Finset.not_nonempty_iff_eq_empty] at hemp
  have heq := escape_lemma n gs v hwf (pairIn v u) (singleIn u)
    (fun i hi => by simp [pairIn, singleIn, hi])
    out (by intro j hj; rw [hemp] at hj; cases hj) out le_rfl hnz
  rw [(hcomp.2.2 v u hadj.ne).mpr hadj, hcomp.2.1 u] at heq
  cases heq

-- Subclaims for the minimal unique-killed gate

lemma subclaim_5B {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List MGate) (out : ℕ)
    (hwf : WF n gs) (hcomp : ComputesW2 G gs out)
    (v u : Fin n) (hadj : G.Adj v u) (hnz_out : ¬ ZeroV n gs v out)
    (j0 : ℕ) (huniq : ∀ j ∈ killedOrs n gs v, j = j0)
    (inZ inNZ : ℕ)
    (hgate_eval : ∀ x : Fin n → Bool,
      evalWire n gs x (n + j0) = (evalWire n gs x inZ || evalWire n gs x inNZ))
    (hinNZ_lt : inNZ < n + j0) (hza : ZeroV n gs v inZ) (hnzb : ¬ ZeroV n gs v inNZ) :
    evalWire n gs (pairIn v u) inZ = true := by
  by_contra hfalse
  have hf : evalWire n gs (pairIn v u) inZ = false := by
    cases h : evalWire n gs (pairIn v u) inZ
    · rfl
    · exact absurd h hfalse
  have hf_u : evalWire n gs (singleIn u) inZ = false :=
    hza (singleIn u) (wtLe2_singleIn u) (by simp [singleIn, hadj.ne])
  have heq := agree_outside_unique n gs v hwf j0 huniq (pairIn v u) (singleIn u)
    (fun i hi => by simp [pairIn, singleIn, hi])
    (fun _ hlt => by
      rw [hgate_eval, hgate_eval, hf, hf_u, Bool.false_or, Bool.false_or]
      exact hlt inNZ hinNZ_lt hnzb)
    out hnz_out
  rw [(hcomp.2.2 v u hadj.ne).mpr hadj, hcomp.2.1 u] at heq
  cases heq

lemma find_nonZero_witness {n : ℕ} (gs : List MGate) (v u₁ u₂ : Fin n) (hwf : WF n gs)
    (j0 : ℕ) (hno_or_below : ∀ j ∈ killedOrs n gs v, j0 ≤ j) :
    ∀ w : ℕ, w < n + j0 → ZeroV n gs v w →
      evalWire n gs (singleIn v) w = false →
      evalWire n gs (pairIn v u₁) w = true →
      evalWire n gs (pairIn v u₂) w = true →
      ∃ h : ℕ, h < w ∧ ¬ ZeroV n gs v h ∧
        evalWire n gs (singleIn v) h = false ∧
        evalWire n gs (pairIn v u₁) h = true ∧
        evalWire n gs (pairIn v u₂) h = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hlt hzw hfv ht1 ht2
    by_cases hw : w < n
    · rw [evalWire_lt n gs (singleIn v) w hw] at hfv
      have hne : (⟨w, hw⟩ : Fin n) ≠ v := by
        intro heq; rw [heq] at hfv; simp [singleIn] at hfv
      exact absurd hzw (not_zeroV_input_ne n gs v ⟨w, hw⟩ hne)
    · cases hg : gs[w - n]? with
      | none => rw [evalWire_none n gs (pairIn v u₁) w hw hg] at ht1; cases ht1
      | some g =>
        have hwfj := hwf (w - n) g hg
        have hwn : n + (w - n) = w := by omega
        rw [hwn] at hwfj
        cases g with
        | cFalse => rw [evalWire_cFalse n gs (pairIn v u₁) w hw hg] at ht1; cases ht1
        | cTrue =>
          exfalso
          have h0 := hzw (zeroIn n) (wtLe2_zeroIn n) rfl
          rw [evalWire_cTrue n gs (zeroIn n) w hw hg] at h0
          cases h0
        | copy a =>
          rw [evalWire_copy n gs (singleIn v) w a hw hg hwfj] at hfv
          rw [evalWire_copy n gs (pairIn v u₁) w a hw hg hwfj] at ht1
          rw [evalWire_copy n gs (pairIn v u₂) w a hw hg hwfj] at ht2
          by_cases hza : ZeroV n gs v a
          · obtain ⟨h, hhlt, hrest⟩ := ih a hwfj (by omega) hza hfv ht1 ht2
            exact ⟨h, lt_trans hhlt hwfj, hrest⟩
          · exact ⟨a, hwfj, hza, hfv, ht1, ht2⟩
        | and a b =>
          rw [evalWire_and n gs (singleIn v) w a b hw hg hwfj.1 hwfj.2, Bool.and_eq_false_iff] at hfv
          rw [evalWire_and n gs (pairIn v u₁) w a b hw hg hwfj.1 hwfj.2, Bool.and_eq_true] at ht1
          rw [evalWire_and n gs (pairIn v u₂) w a b hw hg hwfj.1 hwfj.2, Bool.and_eq_true] at ht2
          rcases hfv with hfva | hfvb
          · by_cases hza : ZeroV n gs v a
            · obtain ⟨h, hhlt, hrest⟩ := ih a hwfj.1 (by omega) hza hfva ht1.1 ht2.1
              exact ⟨h, lt_trans hhlt hwfj.1, hrest⟩
            · exact ⟨a, hwfj.1, hza, hfva, ht1.1, ht2.1⟩
          · by_cases hzb : ZeroV n gs v b
            · obtain ⟨h, hhlt, hrest⟩ := ih b hwfj.2 (by omega) hzb hfvb ht1.2 ht2.2
              exact ⟨h, lt_trans hhlt hwfj.2, hrest⟩
            · exact ⟨b, hwfj.2, hzb, hfvb, ht1.2, ht2.2⟩
        | or a b =>
          exfalso
          have hk : w - n ∈ killedOrs n gs v :=
            mem_killedOrs.mpr ⟨a, b, hg, Or.inl (by rw [hwn]; exact hzw)⟩
          have := hno_or_below (w - n) hk
          omega

lemma subclaim_5C {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List MGate) (out : ℕ)
    (hwf : WF n gs) (hcomp : ComputesW2 G gs out)
    (v u₁ u₂ : Fin n) (hu : u₁ ≠ u₂) (h1 : G.Adj v u₁) (h2 : G.Adj v u₂)
    (hnz_out : ¬ ZeroV n gs v out)
    (j0 : ℕ) (huniq_v : ∀ j ∈ killedOrs n gs v, j = j0)
    (hmin_u1 : ∀ j ∈ killedOrs n gs u₁, j0 ≤ j)
    (inZ inNZ : ℕ)
    (hgate_eval : ∀ x : Fin n → Bool,
      evalWire n gs x (n + j0) = (evalWire n gs x inZ || evalWire n gs x inNZ))
    (hinZ_lt : inZ < n + j0) (hinNZ_lt : inNZ < n + j0)
    (hza : ZeroV n gs v inZ) (hnzb : ¬ ZeroV n gs v inNZ) :
    evalWire n gs (singleIn v) inZ = true := by
  have ht1 := subclaim_5B G gs out hwf hcomp v u₁ h1 hnz_out j0 huniq_v inZ inNZ
    hgate_eval hinNZ_lt hza hnzb
  have ht2 := subclaim_5B G gs out hwf hcomp v u₂ h2 hnz_out j0 huniq_v inZ inNZ
    hgate_eval hinNZ_lt hza hnzb
  by_contra hfalse
  have hfv : evalWire n gs (singleIn v) inZ = false := by
    cases h : evalWire n gs (singleIn v) inZ
    · rfl
    · exact absurd h hfalse
  obtain ⟨h, hhlt, hnzh, hhfv, hht1, hht2⟩ := find_nonZero_witness gs v u₁ u₂ hwf j0
    (fun j hj => le_of_eq (huniq_v j hj).symm) inZ hinZ_lt hza hfv ht1 ht2
  have hlt_j0 : h < n + j0 := lt_trans hhlt hinZ_lt
  have hno_v : ∀ j ∈ killedOrs n gs v, h < n + j := fun j hj => by
    have := huniq_v j hj; omega
  have hh0 : evalWire n gs (zeroIn n) h = false := by
    have heq := escape_lemma n gs v hwf (zeroIn n) (singleIn v)
      (fun i hi => by simp [zeroIn, singleIn, hi]) h hno_v h le_rfl hnzh
    rw [heq, hhfv]
  have hhu1 : evalWire n gs (singleIn u₁) h = true := by
    have heq := escape_lemma n gs v hwf (singleIn u₁) (pairIn v u₁)
      (fun i hi => by simp [singleIn, pairIn, hi]) h hno_v h le_rfl hnzh
    rw [heq, hht1]
  have hhu2 : evalWire n gs (singleIn u₂) h = true := by
    have heq := escape_lemma n gs v hwf (singleIn u₂) (pairIn v u₂)
      (fun i hi => by simp [singleIn, pairIn, hi]) h hno_v h le_rfl hnzh
    rw [heq, hht2]
  have hnzh_u1 : ¬ ZeroV n gs u₁ h := by
    intro hzu1
    have hfalse2 := hzu1 (singleIn u₂) (wtLe2_singleIn u₂) (by simp [singleIn, hu])
    rw [hhu2] at hfalse2
    cases hfalse2
  have hno_u1 : ∀ j ∈ killedOrs n gs u₁, h < n + j := fun j hj => by
    have := hmin_u1 j hj; omega
  have hcontr := escape_lemma n gs u₁ hwf (singleIn u₁) (zeroIn n)
    (fun i hi => by simp [singleIn, zeroIn, hi]) h hno_u1 h le_rfl hnzh_u1
  rw [hhu1, hh0] at hcontr
  cases hcontr

-- Main inductive bound

lemma degree_two_neighbors {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n)
    (hdeg : open Classical in G.degree v = 2) :
    ∃ u₁ u₂ : Fin n, u₁ ≠ u₂ ∧ G.Adj v u₁ ∧ G.Adj v u₂ := by
  classical
  have hcard : (G.neighborFinset v).card = 2 := by
    rwa [SimpleGraph.card_neighborFinset_eq_degree]
  obtain ⟨u₁, u₂, hne, hset⟩ := Finset.card_eq_two.mp hcard
  refine ⟨u₁, u₂, hne, ?_, ?_⟩
  · have : u₁ ∈ G.neighborFinset v := by rw [hset]; simp
    exact (SimpleGraph.mem_neighborFinset G v u₁).mp this
  · have : u₂ ∈ G.neighborFinset v := by rw [hset]; simp
    exact (SimpleGraph.mem_neighborFinset G v u₂).mp this

lemma degree_one_neighbor {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n)
    (hdeg : open Classical in G.degree v = 1) :
    ∃ u : Fin n, G.Adj v u := by
  classical
  have hpos : 0 < (G.neighborFinset v).card := by
    rw [SimpleGraph.card_neighborFinset_eq_degree, hdeg]; omega
  obtain ⟨u, hu⟩ := Finset.card_pos.mp hpos
  exact ⟨u, (SimpleGraph.mem_neighborFinset G v u).mp hu⟩

theorem main_bound (r : ℕ) :
    ∀ {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List MGate) (out : ℕ),
      WF n gs →
      Uni G →
      NoC4 G →
      ComputesW2 G gs out →
      (orIndices gs).card ≤ r →
      open Classical in G.edgeFinset.card ≤ r + 1 := by
  classical
  induction r using Nat.strong_induction_on with
  | ind r ih =>
    intro n G gs out hwf huni hnoC4 hcomp hor
    by_cases hE1 : G.edgeFinset.card ≤ 1
    · omega
    have hE2 : 2 ≤ G.edgeFinset.card := by omega
    -- Case 1: there is a vertex of degree 1
    by_cases hleaf : ∃ v : Fin n, G.degree v = 1
    · obtain ⟨v, hdv⟩ := hleaf
      obtain ⟨u, hadj⟩ := degree_one_neighbor G v hdv
      have hdel_card : (delVert G v).edgeFinset.card + 1 = G.edgeFinset.card := by
        have := delVert_edgeFinset_card G v; omega
      have hnz_out : ¬ ZeroV n gs v out :=
        not_zeroV_out_of_delVert_pos G gs out v hcomp (by omega)
      have hk_ne : (killedOrs n gs v).Nonempty :=
        killedOrs_nonempty_of_adj G gs out v u hwf hcomp hadj hnz_out
      have hk_pos : 1 ≤ (killedOrs n gs v).card := Finset.card_pos.mpr hk_ne
      have hk_sub : killedOrs n gs v ⊆ orIndices gs := killedOrs_subset_orIndices n gs v
      have hk_le : (killedOrs n gs v).card ≤ (orIndices gs).card := Finset.card_le_card hk_sub
      have hr1 : 1 ≤ r := by omega
      have hor' : (orIndices (restrictZero n gs v)).card ≤ r - 1 := by
        have hsub := orIndices_restrictZero_subset n gs v
        have hcard := Finset.card_le_card hsub
        rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hk_sub] at hcard
        omega
      have hih := ih (r - 1) (by omega) (delVert G v) (restrictZero n gs v) out
        (restrictZero_wf n gs v hwf)
        (uni_of_le (delVert_le G v) huni)
        (noC4_of_le (delVert_le G v) hnoC4)
        (computesW2_restrictZero G gs out v hwf hcomp hnz_out)
        hor'
      omega
    -- Case 2: no vertex has degree 1 -> every non-isolated vertex has degree 2
    · push Not at hleaf
      set S : Finset (Fin n) := Finset.univ.filter (fun v : Fin n => 0 < G.degree v)
      have hdeg_ge2 : ∀ v ∈ S, 2 ≤ G.degree v := by
        intro v hv
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hv
        have hne1 := hleaf v
        omega
      have hfilt : G.edgeFinset.filter (fun e => ∀ v ∈ e, v ∈ S) = G.edgeFinset := by
        apply Finset.filter_true_of_mem
        intro e he v hve
        rw [SimpleGraph.mem_edgeFinset] at he
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [← G.card_incidenceFinset_eq_degree v]
        exact Finset.card_pos.mpr ⟨e, by rw [SimpleGraph.mem_incidenceFinset]; exact ⟨he, hve⟩⟩
      have hES : G.edgeFinset.card ≤ S.card := by
        have := huni S; rwa [hfilt] at this
      have hsum_eq : ∑ v ∈ S, G.degree v = 2 * G.edgeFinset.card := by
        rw [← SimpleGraph.sum_degrees_eq_twice_card_edges G]
        apply Finset.sum_subset (Finset.subset_univ S)
        intro v _ hv
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_lt, Nat.le_zero] at hv
        exact hv
      have hsum_ge : 2 * S.card ≤ ∑ v ∈ S, G.degree v := by
        calc 2 * S.card = ∑ _v ∈ S, 2 := by simp [mul_comm]
          _ ≤ ∑ v ∈ S, G.degree v := Finset.sum_le_sum hdeg_ge2
      have hES_eq : G.edgeFinset.card = S.card := by omega
      have hdeg2 : ∀ v ∈ S, G.degree v = 2 := by
        intro v hv
        by_contra hne2
        have hge3 : 3 ≤ G.degree v := by have := hdeg_ge2 v hv; omega
        have hsum_lt : 2 * S.card < ∑ w ∈ S, G.degree w := by
          calc 2 * S.card = ∑ _w ∈ S, 2 := by simp [mul_comm]
            _ < ∑ w ∈ S, G.degree w :=
              Finset.sum_lt_sum hdeg_ge2 ⟨v, hv, by omega⟩
        omega
      have hS_ne : S.Nonempty := Finset.card_pos.mp (by omega)
      have hE3 : 3 ≤ G.edgeFinset.card := by
        obtain ⟨v0, hv0⟩ := hS_ne
        obtain ⟨u₁, u₂, hu12, hadj1, hadj2⟩ := degree_two_neighbors G v0 (hdeg2 v0 hv0)
        have hu1S : u₁ ∈ S := by
          simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
          rw [← SimpleGraph.card_neighborFinset_eq_degree]
          exact Finset.card_pos.mpr ⟨v0, (SimpleGraph.mem_neighborFinset G u₁ v0).mpr hadj1.symm⟩
        have hu2S : u₂ ∈ S := by
          simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
          rw [← SimpleGraph.card_neighborFinset_eq_degree]
          exact Finset.card_pos.mpr ⟨v0, (SimpleGraph.mem_neighborFinset G u₂ v0).mpr hadj2.symm⟩
        have hsub : ({v0, u₁, u₂} : Finset (Fin n)) ⊆ S := by
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl | rfl <;> assumption
        have h3 : ({v0, u₁, u₂} : Finset (Fin n)).card = 3 := by
          rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
          · simp [hu12]
          · simp [hadj1.ne, hadj2.ne]
        have := Finset.card_le_card hsub
        omega
      -- Every v in S has ¬ ZeroV v out and killedOrs v nonempty
      have hnz_out_S : ∀ v ∈ S, ¬ ZeroV n gs v out := by
        intro v hv
        have hdel := delVert_edgeFinset_card G v
        have hdv := hdeg2 v hv
        exact not_zeroV_out_of_delVert_pos G gs out v hcomp (by omega)
      have hk_pos_S : ∀ v ∈ S, 1 ≤ (killedOrs n gs v).card := by
        intro v hv
        obtain ⟨u₁, _, _, hadj1, _⟩ := degree_two_neighbors G v (hdeg2 v hv)
        exact Finset.card_pos.mpr
          (killedOrs_nonempty_of_adj G gs out v u₁ hwf hcomp hadj1 (hnz_out_S v hv))
      -- Case 2a: some v in S kills >= 2 OR gates
      by_cases hkill2 : ∃ v ∈ S, 2 ≤ (killedOrs n gs v).card
      · obtain ⟨v, hv, hk2⟩ := hkill2
        have hdel_card : (delVert G v).edgeFinset.card + 2 = G.edgeFinset.card := by
          have := delVert_edgeFinset_card G v
          have := hdeg2 v hv
          omega
        have hk_sub : killedOrs n gs v ⊆ orIndices gs := killedOrs_subset_orIndices n gs v
        have hk_le : (killedOrs n gs v).card ≤ (orIndices gs).card := Finset.card_le_card hk_sub
        have hr2 : 2 ≤ r := by omega
        have hor' : (orIndices (restrictZero n gs v)).card ≤ r - 2 := by
          have hsub := orIndices_restrictZero_subset n gs v
          have hcard := Finset.card_le_card hsub
          rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hk_sub] at hcard
          omega
        have hih := ih (r - 2) (by omega) (delVert G v) (restrictZero n gs v) out
          (restrictZero_wf n gs v hwf)
          (uni_of_le (delVert_le G v) huni)
          (noC4_of_le (delVert_le G v) hnoC4)
          (computesW2_restrictZero G gs out v hwf hcomp (hnz_out_S v hv))
          hor'
        omega
      -- Case 2b: every v in S kills EXACTLY 1 OR gate
      · push Not at hkill2
        have hk_eq1 : ∀ v ∈ S, (killedOrs n gs v).card = 1 := by
          intro v hv; have := hk_pos_S v hv; have := hkill2 v hv; omega
        -- Define uniqueGate v for v in S
        let uGate (v : Fin n) : ℕ :=
          if hv : v ∈ S then (Finset.card_eq_one.mp (hk_eq1 v hv)).choose else 0
        have huGate_spec : ∀ v ∈ S, killedOrs n gs v = {uGate v} := by
          intro v hv
          simp only [uGate, hv, ↓reduceDIte]
          exact (Finset.card_eq_one.mp (hk_eq1 v hv)).choose_spec
        have huGate_mem : ∀ v ∈ S, uGate v ∈ killedOrs n gs v := fun v hv => by
          rw [huGate_spec v hv]; simp
        have huGate_uniq : ∀ v ∈ S, ∀ j ∈ killedOrs n gs v, j = uGate v := fun v hv j hj => by
          rw [huGate_spec v hv] at hj; exact Finset.mem_singleton.mp hj
        -- Pick v* in S minimizing uGate
        obtain ⟨vStar, hvStarS, hminStar⟩ := Finset.exists_min_image S uGate hS_ne
        set jStar := uGate vStar
        have hjStar_mem : jStar ∈ killedOrs n gs vStar := huGate_mem vStar hvStarS
        obtain ⟨a, b, hgjStar, hor_cond⟩ := mem_killedOrs.mp hjStar_mem
        have hwfStar := hwf jStar (MGate.or a b) hgjStar
        have hmin_all : ∀ v ∈ S, ∀ j ∈ killedOrs n gs v, jStar ≤ j := by
          intro v hv j hj
          rw [huGate_uniq v hv j hj]
          exact hminStar v hv
        -- First show ¬ ZeroV vStar (n + jStar)
        obtain ⟨u₁, u₂, hu12, hadj1, hadj2⟩ := degree_two_neighbors G vStar (hdeg2 vStar hvStarS)
        have hnz_gStar : ¬ ZeroV n gs vStar (n + jStar) := by
          intro hz_g
          have heq := agree_outside_unique n gs vStar hwf jStar (huGate_uniq vStar hvStarS)
            (pairIn vStar u₁) (singleIn u₁)
            (fun i hi => by simp [pairIn, singleIn, hi])
            (fun hnz _ => absurd hz_g hnz)
            out (hnz_out_S vStar hvStarS)
          rw [(hcomp.2.2 vStar u₁ hadj1.ne).mpr hadj1, hcomp.2.1 u₁] at heq
          cases heq
        have hgate_ab : ∀ x : Fin n → Bool,
            evalWire n gs x (n + jStar) = (evalWire n gs x a || evalWire n gs x b) := by
          intro x
          exact evalWire_or n gs x (n + jStar) a b (by omega)
            (by rw [Nat.add_sub_cancel_left]; exact hgjStar) hwfStar.1 hwfStar.2
        have hgate_ba : ∀ x : Fin n → Bool,
            evalWire n gs x (n + jStar) = (evalWire n gs x b || evalWire n gs x a) := by
          intro x; rw [hgate_ab x, Bool.or_comm]
        -- Helper to finish given inZ, inNZ (symmetric in a, b)
        have finish_case : ∀ (inZ inNZ : ℕ),
            (inZ = a ∧ inNZ = b ∨ inZ = b ∧ inNZ = a) →
            ZeroV n gs vStar inZ → ¬ ZeroV n gs vStar inNZ →
            G.edgeFinset.card ≤ r + 1 := by
          intro inZ inNZ hpair hzZ hnzNZ
          have hinZ_lt : inZ < n + jStar := by
            rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩; exact hwfStar.1; exact hwfStar.2
          have hinNZ_lt : inNZ < n + jStar := by
            rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩; exact hwfStar.2; exact hwfStar.1
          have hgeval : ∀ x : Fin n → Bool,
              evalWire n gs x (n + jStar) = (evalWire n gs x inZ || evalWire n gs x inNZ) := by
            rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact hgate_ab
            · exact hgate_ba
          have hu1S : u₁ ∈ S := by
            simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
            rw [← SimpleGraph.card_neighborFinset_eq_degree]
            exact Finset.card_pos.mpr ⟨vStar, (SimpleGraph.mem_neighborFinset G u₁ vStar).mpr hadj1.symm⟩
          -- Subclaim 5C: evalWire inZ (singleIn vStar) = true
          have hinZ_vStar : evalWire n gs (singleIn vStar) inZ = true :=
            subclaim_5C G gs out hwf hcomp vStar u₁ u₂ hu12 hadj1 hadj2
              (hnz_out_S vStar hvStarS) jStar (huGate_uniq vStar hvStarS)
              (hmin_all u₁ hu1S) inZ inNZ hgeval hinZ_lt hinNZ_lt hzZ hnzNZ
          -- Case 6A: exists w ≠ vStar with evalWire inNZ (singleIn w) = true -> C4 contradiction
          by_cases hw1 : ∃ w : Fin n, w ≠ vStar ∧ evalWire n gs (singleIn w) inNZ = true
          · exfalso
            obtain ⟨w, hwne, hbw⟩ := hw1
            have hadj_of_u : ∀ u : Fin n, G.Adj vStar u → w ≠ u ∧ G.Adj w u := by
              intro u hadju
              set y : Fin n → Bool := pairIn w u
              set yPlus : Fin n → Bool := setTrue vStar y
              have hby : evalWire n gs y inNZ = true :=
                evalWire_mono n gs (singleIn w) y
                  (fun i hi => by simp [singleIn, y, pairIn] at hi ⊢; left; exact hi) inNZ hbw
              have hayp : evalWire n gs yPlus inZ = true :=
                evalWire_mono n gs (singleIn vStar) yPlus
                  (fun i hi => by simp [singleIn] at hi; subst hi; simp [yPlus, setTrue]) inZ hinZ_vStar
              have hg_eq : evalWire n gs y (n + jStar) = evalWire n gs yPlus (n + jStar) := by
                rw [hgeval y, hgeval yPlus, hby, hayp, Bool.or_true, Bool.true_or]
              have hout_eq : evalWire n gs y out = evalWire n gs yPlus out :=
                agree_outside_unique n gs vStar hwf jStar (huGate_uniq vStar hvStarS) y yPlus
                  (fun i hi => by simp [yPlus, setTrue, hi])
                  (fun _ _ => hg_eq) out (hnz_out_S vStar hvStarS)
              have hout_yp : evalWire n gs yPlus out = true :=
                evalWire_mono n gs (pairIn vStar u) yPlus
                  (fun i hi => by
                    simp only [pairIn, decide_eq_true_eq] at hi
                    rcases hi with rfl | rfl
                    · simp [yPlus, setTrue]
                    · simp [yPlus, setTrue, y, pairIn])
                  out ((hcomp.2.2 vStar u hadju.ne).mpr hadju)
              have hout_y : evalWire n gs y out = true := by rw [hout_eq, hout_yp]
              have hwu : w ≠ u := by
                intro heq
                subst heq
                have hy_eq : y = singleIn w := by funext i; simp [y, pairIn, singleIn]
                rw [hy_eq, hcomp.2.1 w] at hout_y
                cases hout_y
              exact ⟨hwu, (hcomp.2.2 w u hwu).mp hout_y⟩
            obtain ⟨_, hw1adj⟩ := hadj_of_u u₁ hadj1
            obtain ⟨_, hw2adj⟩ := hadj_of_u u₂ hadj2
            exact hnoC4 vStar w u₁ u₂ hwne.symm hu12 hadj1 hadj2 hw1adj hw2adj
          -- Case 6B: inNZ is false on every singleIn w (for w ≠ vStar, and hence also w = vStar)
          · push Not at hw1
            have hnz_w1_ne : ∀ w : Fin n, w ≠ vStar → evalWire n gs (singleIn w) inNZ = false := by
              intro w hwne
              cases h : evalWire n gs (singleIn w) inNZ
              · rfl
              · exact absurd h (hw1 w hwne)
            have hnz_vStar : evalWire n gs (singleIn vStar) inNZ = false := by
              have hno_v : ∀ j ∈ killedOrs n gs vStar, inNZ < n + j := fun j hj => by
                rw [huGate_uniq vStar hvStarS j hj]; exact hinNZ_lt
              have heq0 := escape_lemma n gs vStar hwf (singleIn vStar) (zeroIn n)
                (fun i hi => by simp [singleIn, zeroIn, hi]) inNZ hno_v inNZ le_rfl hnzNZ
              rw [heq0]
              cases h0 : evalWire n gs (zeroIn n) inNZ
              · rfl
              · exfalso
                have h1 := evalWire_mono n gs (zeroIn n) (singleIn u₁)
                  (fun i hi => by simp [zeroIn] at hi) inNZ h0
                rw [hnz_w1_ne u₁ hadj1.ne.symm] at h1
                cases h1
            have hnz_w1 : ∀ w : Fin n, evalWire n gs (singleIn w) inNZ = false := by
              intro w
              by_cases hwv : w = vStar
              · subst hwv; exact hnz_vStar
              · exact hnz_w1_ne w hwv
            -- Subcase 6B-2: exists edge (p, q) not touching vStar with evalWire inNZ (pairIn p q) = true
            by_cases hedge : ∃ p q : Fin n, p ≠ vStar ∧ q ≠ vStar ∧ G.Adj p q ∧
                evalWire n gs (pairIn p q) inNZ = true
            · exfalso
              obtain ⟨p, q, hpv, hqv, hpq, hbpq⟩ := hedge
              have hpS : p ∈ S := by
                simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
                rw [← SimpleGraph.card_neighborFinset_eq_degree]
                exact Finset.card_pos.mpr ⟨q, (SimpleGraph.mem_neighborFinset G p q).mpr hpq⟩
              by_cases hzp : ZeroV n gs p inNZ
              · -- Then jStar ∈ killedOrs p, so uGate p = jStar (minimal!), contradicting hnz_w1 p!
                have hjk : jStar ∈ killedOrs n gs p := by
                  refine mem_killedOrs.mpr ⟨a, b, hgjStar, ?_⟩
                  rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                  · exact Or.inr (Or.inr hzp)
                  · exact Or.inr (Or.inl hzp)
                have hup_eq : uGate p = jStar := (huGate_uniq p hpS jStar hjk).symm
                have huniq_p : ∀ j ∈ killedOrs n gs p, j = jStar := fun j hj => by
                  rw [huGate_uniq p hpS j hj, hup_eq]
                have hnz_inZ_p : ¬ ZeroV n gs p inZ := by
                  intro hzz
                  have h0 := hzz (singleIn vStar) (wtLe2_singleIn vStar) (by simp [singleIn, hpv])
                  rw [hinZ_vStar] at h0
                  cases h0
                obtain ⟨w₁, w₂, hw12, hpw1, hpw2⟩ := degree_two_neighbors G p (hdeg2 p hpS)
                have hw1S : w₁ ∈ S := by
                  simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
                  rw [← SimpleGraph.card_neighborFinset_eq_degree]
                  exact Finset.card_pos.mpr ⟨p, (SimpleGraph.mem_neighborFinset G w₁ p).mpr hpw1.symm⟩
                have hgeval_sw : ∀ x : Fin n → Bool,
                    evalWire n gs x (n + jStar) = (evalWire n gs x inNZ || evalWire n gs x inZ) := by
                  intro x; rw [hgeval x, Bool.or_comm]
                have hbp_true := subclaim_5C G gs out hwf hcomp p w₁ w₂ hw12 hpw1 hpw2
                  (hnz_out_S p hpS) jStar huniq_p (hmin_all w₁ hw1S)
                  inNZ inZ hgeval_sw hinNZ_lt hinZ_lt hzp hnz_inZ_p
                rw [hnz_w1 p] at hbp_true
                cases hbp_true
              · -- ¬ ZeroV p inNZ -> escape_lemma gives a killed OR gate for p strictly before jStar!
                have hno_p : ∀ j ∈ killedOrs n gs p, inNZ < n + j := fun j hj => by
                  have := hmin_all p hpS j hj; omega
                have hcontr := escape_lemma n gs p hwf (pairIn p q) (singleIn q)
                  (fun i hi => by simp [pairIn, singleIn, hi]) inNZ hno_p inNZ le_rfl hzp
                rw [hbpq, hnz_w1 q] at hcontr
                cases hcontr
            -- Subcase 6B-1: on every edge (p, q) not touching vStar, evalWire inNZ (pairIn p q) = false
            -- Replace gate jStar with copy inZ!
            · push Not at hedge
              set gs' := replaceWithCopy gs jStar inZ
              have hwf' : WF n gs' := replaceWithCopy_wf n gs jStar inZ hwf hinZ_lt
              have hc_ab : inZ = a ∨ inZ = b := by
                rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                · exact Or.inl rfl
                · exact Or.inr rfl
              have hjStar_in : jStar ∈ orIndices gs :=
                mem_orIndices.mpr ⟨a, b, hgjStar⟩
              have hr1 : 1 ≤ r := by
                have := Finset.card_pos.mpr ⟨jStar, hjStar_in⟩; omega
              have hor' : (orIndices gs').card ≤ r - 1 := by
                have hsub : orIndices gs' ⊆ (orIndices gs).erase jStar :=
                  orIndices_replaceWithCopy_subset gs jStar inZ
                have hcard := Finset.card_le_card hsub
                rw [Finset.card_erase_of_mem hjStar_in] at hcard
                omega
              have hcomp' : ComputesW2 G gs' out := by
                refine ⟨?_, ?_, ?_⟩
                · cases h0 : evalWire n gs' (zeroIn n) out
                  · rfl
                  · exfalso
                    have := evalWire_replaceWithCopy_le n gs jStar inZ a b hwf hgjStar hc_ab
                      (zeroIn n) out h0
                    rw [hcomp.1] at this; cases this
                · intro u
                  cases h0 : evalWire n gs' (singleIn u) out
                  · rfl
                  · exfalso
                    have := evalWire_replaceWithCopy_le n gs jStar inZ a b hwf hgjStar hc_ab
                      (singleIn u) out h0
                    rw [hcomp.2.1 u] at this; cases this
                · intro p q hpq
                  constructor
                  · intro ht
                    exact (hcomp.2.2 p q hpq).mp
                      (evalWire_replaceWithCopy_le n gs jStar inZ a b hwf hgjStar hc_ab
                        (pairIn p q) out ht)
                  · intro hadjpq
                    have hmatch : evalWire n gs (pairIn p q) (n + jStar) =
                        evalWire n gs (pairIn p q) inZ := by
                      rw [hgeval (pairIn p q)]
                      by_cases hpv : p = vStar
                      · subst hpv
                        have ht := evalWire_mono n gs (singleIn p) (pairIn p q)
                          (fun i hi => by simp [singleIn, pairIn] at hi ⊢; left; exact hi)
                          inZ hinZ_vStar
                        rw [ht]; simp
                      · by_cases hqv : q = vStar
                        · subst hqv
                          have ht := evalWire_mono n gs (singleIn q) (pairIn p q)
                            (fun i hi => by simp [singleIn, pairIn] at hi ⊢; right; exact hi)
                            inZ hinZ_vStar
                          rw [ht]; simp
                        · have hf : evalWire n gs (pairIn p q) inNZ = false := by
                            cases h : evalWire n gs (pairIn p q) inNZ
                            · rfl
                            · exact absurd h (hedge p q hpv hqv hadjpq)
                          rw [hf, Bool.or_false]
                    rw [evalWire_replaceWithCopy_eq n gs jStar inZ hwf
                      (by rw [hgjStar]; rfl) hinZ_lt (pairIn p q) hmatch out]
                    exact (hcomp.2.2 p q hpq).mpr hadjpq
              have hih := ih (r - 1) (by omega) G gs' out hwf' huni hnoC4 hcomp' hor'
              omega
        -- Split on whether ZeroV vStar a or ZeroV vStar b
        rcases hor_cond with hz_g | hza | hzb
        · exact absurd hz_g hnz_gStar
        · have hnzb : ¬ ZeroV n gs vStar b := fun hzb =>
            hnz_gStar (zeroV_or (by omega) (by rw [Nat.add_sub_cancel_left]; exact hgjStar)
              hwfStar.1 hwfStar.2 hza hzb)
          exact finish_case a b (Or.inl ⟨rfl, rfl⟩) hza hnzb
        · have hnza : ¬ ZeroV n gs vStar a := fun hza =>
            hnz_gStar (zeroV_or (by omega) (by rw [Nat.add_sub_cancel_left]; exact hgjStar)
              hwfStar.1 hwfStar.2 hza hzb)
          exact finish_case b a (Or.inr ⟨rfl, rfl⟩) hzb hnza

-- Convert hypotheses of L_meta_599 to Uni and NoC4

lemma uni_of_ncard {n : ℕ} (G : SimpleGraph (Fin n))
    (h : ∀ S : Finset (Fin n),
      {e : Sym2 (Fin n) | e ∈ G.edgeSet ∧ ∀ v ∈ e, v ∈ S}.ncard ≤ S.card) :
    Uni G := by
  classical
  intro S
  have hset : (↑(G.edgeFinset.filter (fun e => ∀ v ∈ e, v ∈ S)) : Set (Sym2 (Fin n))) =
      {e : Sym2 (Fin n) | e ∈ G.edgeSet ∧ ∀ v ∈ e, v ∈ S} := by
    ext e; simp [SimpleGraph.mem_edgeFinset]
  rw [← Set.ncard_coe_finset, hset]
  exact h S

lemma noC4_of_no_cycle4 {n : ℕ} (G : SimpleGraph (Fin n))
    (h : ∀ (v : Fin n) (c : G.Walk v v), c.IsCycle → c.length ≠ 4) :
    NoC4 G := by
  intro v w u₁ u₂ hvw hu12 h1 h2 h3 h4
  have hvu1 : v ≠ u₁ := h1.ne
  have hvu2 : v ≠ u₂ := h2.ne
  have hwu1 : w ≠ u₁ := h3.ne
  have hwu2 : w ≠ u₂ := h4.ne
  let c : G.Walk v v :=
    SimpleGraph.Walk.cons h1
      (SimpleGraph.Walk.cons h3.symm
        (SimpleGraph.Walk.cons h4
          (SimpleGraph.Walk.cons h2.symm SimpleGraph.Walk.nil)))
  have hlen : c.length = 4 := rfl
  have hcyc : c.IsCycle := by
    refine ⟨⟨⟨?_⟩, ?_⟩, ?_⟩
    · simp only [c, SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil, List.nodup_cons,
        List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil, and_true, not_or]
      refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩ <;>
        simp [hvw, hvw.symm, hu12, hvu1, hvu1.symm, hvu2, hvu2.symm, hwu1.symm, hwu2]
    · simp [c]
    · simp [c, hwu1.symm, hu12, hvu1.symm, hwu2, hvw.symm, hvu2.symm]
  exact h v c hcyc hlen

end PEqualNP.Outside.L_meta_599_aux

theorem PEqualNP.Outside.L_meta_599 :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (A : Finset ℕ),
      (∀ S : Finset (Fin n), {e : Sym2 (Fin n) | e ∈ G.edgeSet ∧ ∀ v ∈ e, v ∈ S}.ncard ≤ S.card) →
      (∀ (v : Fin n) (c : G.Walk v v), c.IsCycle → c.length ≠ 4) →
      PEqualNP.MetaComplexity.Monotone2 C →
      (∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) →
      (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.or → j ∈ A) →
      G.edgeSet.ncard ≤ A.card + 1 := by
  classical
  intro n G C A huni_raw hnoC4_raw hmono heval hA
  open PEqualNP.Outside.L_meta_599_aux in
  have hgs_eq : ∀ x : Fin n → Bool,
      evalWire n (translateGates n C.gates) x C.output = C.eval (List.ofFn x) := by
    intro x
    exact (wiresFrom_eq_evalWire n C.gates hmono x C.output).symm
  have hcomp : PEqualNP.Outside.L_meta_599_aux.ComputesW2 G
      (PEqualNP.Outside.L_meta_599_aux.translateGates n C.gates) C.output := by
    refine ⟨?_, ?_, ?_⟩
    · cases h0 : PEqualNP.Outside.L_meta_599_aux.evalWire n
          (PEqualNP.Outside.L_meta_599_aux.translateGates n C.gates)
          (PEqualNP.Outside.L_meta_599_aux.zeroIn n) C.output
      · rfl
      · exfalso
        rw [hgs_eq, heval] at h0
        obtain ⟨u, v, _, hu, _⟩ := h0
        simp [PEqualNP.Outside.L_meta_599_aux.zeroIn] at hu
    · intro u
      cases h0 : PEqualNP.Outside.L_meta_599_aux.evalWire n
          (PEqualNP.Outside.L_meta_599_aux.translateGates n C.gates)
          (PEqualNP.Outside.L_meta_599_aux.singleIn u) C.output
      · rfl
      · exfalso
        rw [hgs_eq, heval] at h0
        obtain ⟨a, b, hab, ha, hb⟩ := h0
        simp [PEqualNP.Outside.L_meta_599_aux.singleIn] at ha hb
        subst ha; subst hb
        exact G.loopless.irrefl _ hab
    · intro u v huv
      rw [hgs_eq, heval]
      constructor
      · rintro ⟨a, b, hab, ha, hb⟩
        simp only [PEqualNP.Outside.L_meta_599_aux.pairIn, decide_eq_true_eq] at ha hb
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
        · exact absurd hab (G.loopless.irrefl _)
        · exact hab
        · exact hab.symm
        · exact absurd hab (G.loopless.irrefl _)
      · intro hadj
        exact ⟨u, v, hadj, by simp [PEqualNP.Outside.L_meta_599_aux.pairIn],
          by simp [PEqualNP.Outside.L_meta_599_aux.pairIn]⟩
  have hcard_eq : G.edgeSet.ncard = G.edgeFinset.card := by
    rw [← Set.ncard_coe_finset, SimpleGraph.coe_edgeFinset]
  rw [hcard_eq]
  exact PEqualNP.Outside.L_meta_599_aux.main_bound A.card G
    (PEqualNP.Outside.L_meta_599_aux.translateGates n C.gates) C.output
    (PEqualNP.Outside.L_meta_599_aux.translateGates_wf n C.gates)
    (PEqualNP.Outside.L_meta_599_aux.uni_of_ncard G huni_raw)
    (PEqualNP.Outside.L_meta_599_aux.noC4_of_no_cycle4 G hnoC4_raw)
    hcomp
    (Finset.card_le_card (PEqualNP.Outside.L_meta_599_aux.orIndices_translate_subset n C A hA))
