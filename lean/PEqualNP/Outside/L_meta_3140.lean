import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3140_aux

open PEqualNP.CircuitLowerBounds

-- step, val, val_snoc, val_ge, val_lt, val_gate: copied from the merged L_meta_1406.lean

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def val {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (gs.foldl step (List.ofFn x)).getD i false

lemma fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_cons]
    simp only [step, List.length_append, List.length_cons, List.length_nil]
    omega

lemma val_nil {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    val [] x i = if h : i < n then x ⟨i, h⟩ else false := by
  unfold val
  by_cases h : i < n
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, h]

lemma val_snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) (i : ℕ) :
    val (gs ++ [g]) x i =
      if i = n + gs.length then g.op.eval (g.inputs.map fun j => val gs x j)
      else val gs x i := by
  unfold val
  rw [List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, step]
  have hl : (gs.foldl step (List.ofFn x)).length = n + gs.length := by
    rw [fold_length]
    simp
  rcases lt_trichotomy i (n + gs.length) with h | h | h
  · rw [if_neg (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by omega)]
  · rw [if_pos h]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega)]
    simp [hl, h]
  · rw [if_neg (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

lemma val_ge {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) (hi : n + gs.length ≤ i) :
    val gs x i = false := by
  unfold val
  have hl : (gs.foldl step (List.ofFn x)).length = n + gs.length := by
    rw [fold_length]
    simp
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
  rfl

lemma val_lt {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    val gs x i = x ⟨i, hi⟩ := by
  induction gs using List.reverseRecOn with
  | nil =>
    rw [val_nil]
    simp [hi]
  | append_singleton gs g ih =>
    rw [val_snoc, if_neg (by omega)]
    exact ih

lemma val_gate {n : ℕ} (gs : List Gate) (x : Fin n → Bool) :
    ∀ (k : ℕ) (hk : k < gs.length), val gs x (n + k) =
      gs[k].op.eval (gs[k].inputs.map fun j => if j < n + k then val gs x j else false) := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro k hk
    simp at hk
  | append_singleton gs g ih =>
    intro k hk
    by_cases hkl : k = gs.length
    · subst hkl
      have hgl : (gs ++ [g])[gs.length]'hk = g := by simp
      rw [hgl, val_snoc, if_pos rfl]
      congr 1
      apply List.map_congr_left
      intro j _
      by_cases hj : j < n + gs.length
      · rw [if_pos hj, val_snoc, if_neg (by omega)]
      · rw [if_neg hj, val_ge gs x j (by omega)]
    · have hk' : k < gs.length + 1 := by simpa using hk
      have hk2 : k < gs.length := by omega
      have hget : (gs ++ [g])[k]'hk = gs[k] := List.getElem_append_left hk2
      rw [hget, val_snoc, if_neg (by omega), ih k hk2]
      congr 1
      apply List.map_congr_left
      intro j _
      by_cases hj : j < n + k
      · rw [if_pos hj, if_pos hj, val_snoc, if_neg (by omega)]
      · rw [if_neg hj, if_neg hj]


lemma ev_mono (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (f f' : ℕ → Bool)
    (h : ∀ i ∈ g.inputs, f i = true → f' i = true) :
    g.op.eval (g.inputs.map f) = true → g.op.eval (g.inputs.map f') = true := by
  rcases hop with hop | hop
  · rw [hop]
    simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
    intro h1 i hi
    exact h i hi (h1 i hi)
  · rw [hop]
    simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
    rintro ⟨i, hi, h1⟩
    exact ⟨i, hi, h i hi h1⟩

lemma mono2 {n : ℕ} (gs : List Gate) (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x x' : Fin n → Bool) (hle : ∀ v, x v = true → x' v = true) :
    ∀ i, val gs x i = true → val gs x' i = true := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    by_cases h1 : i < n
    · rw [val_lt gs x i h1] at hi
      rw [val_lt gs x' i h1]
      exact hle _ hi
    · by_cases h2 : n + gs.length ≤ i
      · rw [val_ge gs x i h2] at hi
        exact absurd hi (by simp)
      · obtain ⟨k, rfl⟩ : ∃ k, i = n + k := ⟨i - n, by omega⟩
        have hk : k < gs.length := by omega
        rw [val_gate gs x k hk] at hi
        rw [val_gate gs x' k hk]
        refine ev_mono _ (hg _ (List.getElem_mem hk)) _ _ ?_ hi
        intro a _ ha
        by_cases hlt : a < n + k
        · rw [if_pos hlt] at ha ⊢
          exact ih a hlt ha
        · rw [if_neg hlt] at ha
          exact absurd ha (by simp)

lemma v0_j {n : ℕ} (gs : List Gate) (j : ℕ) (hj : j < gs.length) (x : Fin n → Bool) :
    val (gs.set j ⟨GateOp.or, []⟩) x (n + j) = false := by
  have hk0 : j < (gs.set j ⟨GateOp.or, []⟩).length := by simpa using hj
  rw [val_gate _ x j hk0, List.getElem_set_self]
  simp [GateOp.eval]

lemma cmp_le {n : ℕ} (gs : List Gate) (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (j : ℕ) (x : Fin n → Bool) :
    ∀ i, val (gs.set j ⟨GateOp.or, []⟩) x i = true → val gs x i = true := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    by_cases h1 : i < n
    · rw [val_lt _ x i h1] at hi
      rw [val_lt gs x i h1]
      exact hi
    · by_cases h2 : n + gs.length ≤ i
      · rw [val_ge _ x i (by simpa using h2)] at hi
        exact absurd hi (by simp)
      · obtain ⟨k, rfl⟩ : ∃ k, i = n + k := ⟨i - n, by omega⟩
        have hk : k < gs.length := by omega
        have hk0 : k < (gs.set j ⟨GateOp.or, []⟩).length := by simpa using hk
        by_cases hkj : k = j
        · subst hkj
          rw [v0_j gs k hk x] at hi
          exact absurd hi (by simp)
        · rw [val_gate _ x k hk0, List.getElem_set_ne (Ne.symm hkj)] at hi
          rw [val_gate gs x k hk]
          refine ev_mono _ (hg _ (List.getElem_mem hk)) _ _ ?_ hi
          intro a _ ha
          by_cases hlt : a < n + k
          · rw [if_pos hlt] at ha ⊢
            exact ih a hlt ha
          · rw [if_neg hlt] at ha
            exact absurd ha (by simp)

lemma cmp_eq {n : ℕ} (gs : List Gate) (j : ℕ) (x : Fin n → Bool)
    (hj : val gs x (n + j) = false) :
    ∀ i, val (gs.set j ⟨GateOp.or, []⟩) x i = val gs x i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    by_cases h1 : i < n
    · rw [val_lt _ x i h1, val_lt gs x i h1]
    · by_cases h2 : n + gs.length ≤ i
      · rw [val_ge _ x i (by simpa using h2), val_ge gs x i h2]
      · obtain ⟨k, rfl⟩ : ∃ k, i = n + k := ⟨i - n, by omega⟩
        have hk : k < gs.length := by omega
        have hk0 : k < (gs.set j ⟨GateOp.or, []⟩).length := by simpa using hk
        by_cases hkj : k = j
        · subst hkj
          rw [hj, v0_j gs k hk x]
        · rw [val_gate _ x k hk0, val_gate gs x k hk, List.getElem_set_ne (Ne.symm hkj)]
          congr 1
          apply List.map_congr_left
          intro a _
          by_cases hlt : a < n + k
          · rw [if_pos hlt, if_pos hlt]
            exact ih a hlt
          · rw [if_neg hlt, if_neg hlt]

lemma getD_get (gs : List Gate) (i : ℕ) (hi : i < gs.length) :
    gs.getD i ⟨GateOp.or, []⟩ = gs[i] := by
  simp [List.getD_eq_getElem?_getD, hi]

lemma dep {n : ℕ} (gs : List Gate) (K : Finset ℕ) (hK : ∀ i ∈ K, i < gs.length)
    (hcl : ∀ i ∈ K, ∀ w ∈ (gs.getD i ⟨GateOp.or, []⟩).inputs, n ≤ w → w - n ∈ K)
    (x x' : Fin n → Bool)
    (hag : ∀ u : Fin n, (∃ i ∈ K, u.val ∈ (gs.getD i ⟨GateOp.or, []⟩).inputs) → x u = x' u) :
    ∀ i, i ∈ K → val gs x (n + i) = val gs x' (n + i) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    have hk := hK i hi
    have hgd := getD_get gs i hk
    rw [val_gate gs x i hk, val_gate gs x' i hk]
    congr 1
    apply List.map_congr_left
    intro w hw
    by_cases hlt : w < n + i
    · rw [if_pos hlt, if_pos hlt]
      by_cases hwn : w < n
      · rw [val_lt gs x w hwn, val_lt gs x' w hwn]
        exact hag ⟨w, hwn⟩ ⟨i, hi, by rw [hgd]; exact hw⟩
      · have hm := hcl i hi w (by rw [hgd]; exact hw) (by omega)
        have h3 := ih (w - n) (by omega) hm
        rwa [show n + (w - n) = w by omega] at h3
    · rw [if_neg hlt, if_neg hlt]

lemma val_app_lt {n : ℕ} (B G : List Gate) (x : Fin n → Bool) (w : ℕ) (hw : w < n + B.length) :
    val (B ++ G) x w = val B x w := by
  induction G using List.reverseRecOn with
  | nil => simp
  | append_singleton G g ih =>
    rw [← List.append_assoc, val_snoc, if_neg (by simp; omega)]
    exact ih

/-- Gates of a block placed at wire offset `off` read only earlier wires. -/
def RB (off : ℕ) (G : List Gate) : Prop :=
  ∀ t < G.length, ∀ i ∈ (G.getD t ⟨GateOp.or, []⟩).inputs, i < off + t

lemma RB_app (off : ℕ) (A B : List Gate) (hA : RB off A) (hB : RB (off + A.length) B) :
    RB off (A ++ B) := by
  intro t ht i hi
  by_cases h : t < A.length
  · have e : (A ++ B).getD t ⟨GateOp.or, []⟩ = A.getD t ⟨GateOp.or, []⟩ := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
    rw [e] at hi
    exact hA t h i hi
  · have e : (A ++ B).getD t ⟨GateOp.or, []⟩ = B.getD (t - A.length) ⟨GateOp.or, []⟩ := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_of_not_lt h)]
    rw [e] at hi
    have h2 := hB (t - A.length) (by simp at ht; omega) i hi
    omega

lemma RB_one (off : ℕ) (op : GateOp) (u v : ℕ) (hu : u < off) (hv : v < off) :
    RB off [⟨op, [u, v]⟩] := by
  intro t ht i hi
  have : t = 0 := by simpa using ht
  subst this
  simp at hi
  omega

/-- value of an optional wire: no wire is the constant false -/
def ov {n : ℕ} (gs : List Gate) (x : Fin n → Bool) : Option ℕ → Bool
  | none => false
  | some u => val gs x u

lemma ov_snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) (o : Option ℕ)
    (h : ∀ u, o = some u → u < n + gs.length) : ov (gs ++ [g]) x o = ov gs x o := by
  cases o with
  | none => rfl
  | some u =>
    have := h u rfl
    simp only [ov]
    rw [val_snoc, if_neg (by omega)]

def isAnd : GateOp → Bool
  | GateOp.and => true
  | _ => false

/-- One step of constant elimination: gates of `K` vanish, a gate reading a vanished wire
is absorbed. -/
def stp (n : ℕ) (K : Finset ℕ) (m : ℕ) (g : Gate) (s : List Gate × (ℕ → Option ℕ)) :
    List Gate × (ℕ → Option ℕ) :=
  if m ∈ K then s
  else match s.2 (g.inputs.getD 0 0), s.2 (g.inputs.getD 1 0) with
    | some u, some v =>
      (s.1 ++ [⟨g.op, [u, v]⟩], Function.update s.2 (n + m) (some (n + s.1.length)))
    | some u, none => (s.1, Function.update s.2 (n + m) (if isAnd g.op then none else some u))
    | none, some v => (s.1, Function.update s.2 (n + m) (if isAnd g.op then none else some v))
    | none, none => s

def run (n : ℕ) (K : Finset ℕ) (gs : List Gate) : ℕ → List Gate × (ℕ → Option ℕ)
  | 0 => ([], fun w => if w < n then some w else none)
  | m + 1 => stp n K m (gs.getD m ⟨GateOp.or, []⟩) (run n K gs m)

structure Inv (n : ℕ) (K : Finset ℕ) (gs : List Gate) (j m : ℕ)
    (s : List Gate × (ℕ → Option ℕ)) : Prop where
  ao : ∀ g ∈ s.1, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2
  rb : RB n s.1
  bd : ∀ w u, s.2 w = some u → u < n + s.1.length
  hi : ∀ w, n + m ≤ w → s.2 w = none
  jn : s.2 (n + j) = none
  sm : ∀ (x : Fin n → Bool) (w : ℕ), w < n + m → (w < n ∨ w - n ∉ K ∨ w = n + j) →
    ov s.1 x (s.2 w) = val (gs.set j ⟨GateOp.or, []⟩) x w
  cnt : s.1.length + ((Finset.range m).filter
    (fun i => i ∈ K ∨ n + j ∈ (gs.getD i ⟨GateOp.or, []⟩).inputs)).card ≤ m

lemma cnt_pos (P : ℕ → Prop) [DecidablePred P] (m : ℕ) (h : P m) :
    ((Finset.range (m + 1)).filter P).card = ((Finset.range m).filter P).card + 1 := by
  rw [Finset.range_add_one, Finset.filter_insert, if_pos h, Finset.card_insert_of_notMem (by simp)]

lemma cnt_neg (P : ℕ → Prop) [DecidablePred P] (m : ℕ) (h : ¬ P m) :
    ((Finset.range (m + 1)).filter P).card = ((Finset.range m).filter P).card := by
  rw [Finset.range_add_one, Finset.filter_insert, if_neg h]

lemma cnt_le (P : ℕ → Prop) [DecidablePred P] (m : ℕ) :
    ((Finset.range (m + 1)).filter P).card ≤ ((Finset.range m).filter P).card + 1 := by
  by_cases h : P m
  · rw [cnt_pos P m h]
  · rw [cnt_neg P m h]
    omega

lemma inv_K (n : ℕ) (K : Finset ℕ) (gs : List Gate) (j m : ℕ)
    (s : List Gate × (ℕ → Option ℕ)) (g : Gate) (IH : Inv n K gs j m s) (hmK : m ∈ K)
    (hj : j < gs.length) :
    Inv n K gs j (m + 1) (stp n K m g s) := by
  have e : stp n K m g s = s := if_pos hmK
  rw [e]
  refine ⟨IH.ao, IH.rb, IH.bd, fun w hw => IH.hi w (by omega), IH.jn, ?_, ?_⟩
  · intro x w hw hc
    by_cases h : w < n + m
    · exact IH.sm x w h hc
    · have hwm : w = n + m := by omega
      have hmj : m = j := by
        rcases hc with hc | hc | hc
        · omega
        · exact absurd (by rw [hwm]; simpa using hmK) hc
        · omega
      rw [hwm, hmj, IH.jn, v0_j gs j hj x]
      rfl
  · rw [cnt_pos _ m (Or.inl hmK)]
    have := IH.cnt
    omega

lemma inv_step (n : ℕ) (K : Finset ℕ) (gs : List Gate) (j m : ℕ)
    (s : List Gate × (ℕ → Option ℕ)) (IH : Inv n K gs j m s) (hmK : m ∉ K) (hmj : m ≠ j)
    (op : GateOp) (w1 w2 : ℕ) (hop : op = GateOp.and ∨ op = GateOp.or)
    (hw1 : w1 < n + m) (hw2 : w2 < n + m)
    (c1 : w1 < n ∨ w1 - n ∉ K ∨ w1 = n + j) (c2 : w2 < n ∨ w2 - n ∉ K ∨ w2 = n + j)
    (hgv : ∀ x : Fin n → Bool, val (gs.set j ⟨GateOp.or, []⟩) x (n + m) =
      op.eval [val (gs.set j ⟨GateOp.or, []⟩) x w1, val (gs.set j ⟨GateOp.or, []⟩) x w2])
    (hin : (gs.getD m ⟨GateOp.or, []⟩).inputs = [w1, w2]) :
    Inv n K gs j (m + 1) (stp n K m ⟨op, [w1, w2]⟩ s) := by
  have e1 := fun x => IH.sm x w1 hw1 c1
  have e2 := fun x => IH.sm x w2 hw2 c2
  have hjm : n + j ≠ n + m := by omega
  have hold : ∀ (x : Fin n → Bool) (w : ℕ), w < n + (m + 1) → w ≠ n + m →
      (w < n ∨ w - n ∉ K ∨ w = n + j) →
      ov s.1 x (s.2 w) = val (gs.set j ⟨GateOp.or, []⟩) x w :=
    fun x w hw hne hc => IH.sm x w (by omega) hc
  unfold stp
  rw [if_neg hmK]
  show Inv n K gs j (m + 1) (match s.2 w1, s.2 w2 with
    | some u, some v =>
      (s.1 ++ [⟨op, [u, v]⟩], Function.update s.2 (n + m) (some (n + s.1.length)))
    | some u, none => (s.1, Function.update s.2 (n + m) (if isAnd op then none else some u))
    | none, some v => (s.1, Function.update s.2 (n + m) (if isAnd op then none else some v))
    | none, none => s)
  rcases hs1 : s.2 w1 with _ | u <;> rcases hs2 : s.2 w2 with _ | v
  · -- none, none
    refine ⟨IH.ao, IH.rb, IH.bd, fun w hw => IH.hi w (by omega), IH.jn, ?_, ?_⟩
    · intro x w hw hc
      by_cases hne : w = n + m
      · rw [hne, IH.hi (n + m) le_rfl, hgv x, ← e1 x, ← e2 x, hs1, hs2]
        rcases hop with rfl | rfl <;> simp [ov, GateOp.eval]
      · exact hold x w hw hne hc
    · have h1 := IH.cnt
      have h2 := cnt_le (fun i => i ∈ K ∨ n + j ∈ (gs.getD i ⟨GateOp.or, []⟩).inputs) m
      show s.1.length + _ ≤ m + 1
      omega
  · -- none, some v
    refine ⟨IH.ao, IH.rb, ?_, ?_, ?_, ?_, ?_⟩
    · intro w u' hu
      by_cases hne : w = n + m
      · rw [hne] at hu
        simp only [Function.update_self] at hu
        by_cases hA : isAnd op = true
        · simp [hA] at hu
        · simp only [hA] at hu
          have : v = u' := by simpa using hu
          rw [← this]
          exact IH.bd w2 v hs2
      · simp only [Function.update_of_ne hne] at hu
        exact IH.bd w u' hu
    · intro w hw
      simp only [Function.update_of_ne (show w ≠ n + m by omega)]
      exact IH.hi w (by omega)
    · simp only [Function.update_of_ne hjm]
      exact IH.jn
    · intro x w hw hc
      by_cases hne : w = n + m
      · rw [hne]
        simp only [Function.update_self]
        rw [hgv x, ← e1 x, ← e2 x, hs1, hs2]
        rcases hop with rfl | rfl <;> simp [ov, GateOp.eval, isAnd]
      · simp only [Function.update_of_ne hne]
        exact hold x w hw hne hc
    · have h1 := IH.cnt
      have h2 := cnt_le (fun i => i ∈ K ∨ n + j ∈ (gs.getD i ⟨GateOp.or, []⟩).inputs) m
      show s.1.length + _ ≤ m + 1
      omega
  · -- some u, none
    refine ⟨IH.ao, IH.rb, ?_, ?_, ?_, ?_, ?_⟩
    · intro w u' hu
      by_cases hne : w = n + m
      · rw [hne] at hu
        simp only [Function.update_self] at hu
        by_cases hA : isAnd op = true
        · simp [hA] at hu
        · simp only [hA] at hu
          have : u = u' := by simpa using hu
          rw [← this]
          exact IH.bd w1 u hs1
      · simp only [Function.update_of_ne hne] at hu
        exact IH.bd w u' hu
    · intro w hw
      simp only [Function.update_of_ne (show w ≠ n + m by omega)]
      exact IH.hi w (by omega)
    · simp only [Function.update_of_ne hjm]
      exact IH.jn
    · intro x w hw hc
      by_cases hne : w = n + m
      · rw [hne]
        simp only [Function.update_self]
        rw [hgv x, ← e1 x, ← e2 x, hs1, hs2]
        rcases hop with rfl | rfl <;> simp [ov, GateOp.eval, isAnd]
      · simp only [Function.update_of_ne hne]
        exact hold x w hw hne hc
    · have h1 := IH.cnt
      have h2 := cnt_le (fun i => i ∈ K ∨ n + j ∈ (gs.getD i ⟨GateOp.or, []⟩).inputs) m
      show s.1.length + _ ≤ m + 1
      omega
  · -- some u, some v
    have hu := IH.bd w1 u hs1
    have hv := IH.bd w2 v hs2
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro g hg
      rcases List.mem_append.1 hg with h | h
      · exact IH.ao g h
      · have : g = ⟨op, [u, v]⟩ := by simpa using h
        rw [this]
        exact ⟨hop, rfl⟩
    · exact RB_app n s.1 _ IH.rb (RB_one _ op u v hu hv)
    · intro w u' hu'
      by_cases hne : w = n + m
      · rw [hne] at hu'
        simp only [Function.update_self] at hu'
        have : n + s.1.length = u' := by simpa using hu'
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      · simp only [Function.update_of_ne hne] at hu'
        have := IH.bd w u' hu'
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
    · intro w hw
      simp only [Function.update_of_ne (show w ≠ n + m by omega)]
      exact IH.hi w (by omega)
    · simp only [Function.update_of_ne hjm]
      exact IH.jn
    · intro x w hw hc
      by_cases hne : w = n + m
      · rw [hne]
        simp only [Function.update_self, ov]
        rw [val_snoc, if_pos rfl, hgv x, ← e1 x, ← e2 x, hs1, hs2]
        simp [ov]
      · simp only [Function.update_of_ne hne]
        rw [ov_snoc _ _ _ _ (fun u' hu' => IH.bd w u' hu')]
        exact hold x w hw hne hc
    · have h1 := IH.cnt
      have hnot : ¬ (m ∈ K ∨ n + j ∈ (gs.getD m ⟨GateOp.or, []⟩).inputs) := by
        rintro (h | h)
        · exact hmK h
        · rw [hin] at h
          have h3 : n + j = w1 ∨ n + j = w2 := by simpa using h
          rcases h3 with h3 | h3
          · rw [← h3, IH.jn] at hs1
            exact absurd hs1 (by simp)
          · rw [← h3, IH.jn] at hs2
            exact absurd hs2 (by simp)
      have h2 := cnt_neg (fun i => i ∈ K ∨ n + j ∈ (gs.getD i ⟨GateOp.or, []⟩).inputs) m hnot
      show (s.1 ++ [_]).length + _ ≤ m + 1
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega

lemma inv_run (n : ℕ) (K : Finset ℕ) (gs : List Gate) (j : ℕ)
    (hao : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hrb : ∀ k < gs.length, ∀ i ∈ (gs.getD k ⟨GateOp.or, []⟩).inputs, i < n + k)
    (hj : j < gs.length) (hjK : j ∈ K)
    (hpriv : ∀ k < gs.length, k ∉ K → ∀ w ∈ (gs.getD k ⟨GateOp.or, []⟩).inputs, n ≤ w →
      w - n ∈ K → w = n + j) :
    ∀ m, m ≤ gs.length → Inv n K gs j m (run n K gs m) := by
  intro m
  induction m with
  | zero =>
    intro _
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro g hg
      simp [run] at hg
    · intro t ht
      simp [run] at ht
    · intro w u hu
      simp only [run] at hu
      by_cases h : w < n
      · rw [if_pos h] at hu
        have : w = u := by simpa using hu
        simp only [run, List.length_nil]
        omega
      · rw [if_neg h] at hu
        exact absurd hu (by simp)
    · intro w hw
      simp only [run]
      rw [if_neg (by omega)]
    · simp only [run]
      rw [if_neg (by omega)]
    · intro x w hw _
      have h : w < n := by omega
      simp only [run]
      rw [if_pos h]
      simp only [ov]
      rw [val_lt _ x w h, val_lt _ x w h]
    · simp [run]
  | succ m ih =>
    intro hm
    have IH := ih (by omega)
    have hml : m < gs.length := by omega
    show Inv n K gs j (m + 1) (stp n K m (gs.getD m ⟨GateOp.or, []⟩) (run n K gs m))
    by_cases hmK : m ∈ K
    · exact inv_K n K gs j m _ _ IH hmK hj
    · have hgd := getD_get gs m hml
      obtain ⟨hop, hlen⟩ := hao gs[m] (List.getElem_mem hml)
      obtain ⟨w1, w2, hin⟩ := List.length_eq_two.1 hlen
      have hmj : m ≠ j := fun h => hmK (h ▸ hjK)
      have hin' : (gs.getD m ⟨GateOp.or, []⟩).inputs = [w1, w2] := by rw [hgd]; exact hin
      have hw1 : w1 < n + m := hrb m hml w1 (by rw [hin']; simp)
      have hw2 : w2 < n + m := hrb m hml w2 (by rw [hin']; simp)
      have cc : ∀ w ∈ (gs.getD m ⟨GateOp.or, []⟩).inputs, w < n ∨ w - n ∉ K ∨ w = n + j := by
        intro w hw
        by_cases h1 : w < n
        · exact Or.inl h1
        · by_cases h2 : w - n ∈ K
          · exact Or.inr (Or.inr (hpriv m hml hmK w hw (by omega) h2))
          · exact Or.inr (Or.inl h2)
      have hgv : ∀ x : Fin n → Bool, val (gs.set j ⟨GateOp.or, []⟩) x (n + m) =
          gs[m].op.eval [val (gs.set j ⟨GateOp.or, []⟩) x w1,
            val (gs.set j ⟨GateOp.or, []⟩) x w2] := by
        intro x
        have hk0 : m < (gs.set j ⟨GateOp.or, []⟩).length := by simpa using hml
        rw [val_gate _ x m hk0, List.getElem_set_ne (Ne.symm hmj), hin]
        simp [hw1, hw2]
      have hge : gs.getD m ⟨GateOp.or, []⟩ = ⟨gs[m].op, [w1, w2]⟩ := by
        rw [hgd, ← hin]
      rw [hge]
      exact inv_step n K gs j m _ IH hmK hmj gs[m].op w1 w2 hop hw1 hw2
        (cc w1 (by rw [hin']; simp)) (cc w2 (by rw [hin']; simp)) hgv hin'

/-- AND/OR formulas over existing wires; `bin true` is AND, `bin false` is OR. -/
inductive Fm where
  | var : ℕ → Fm
  | bin : Bool → Fm → Fm → Fm

def fsem (ρ : ℕ → Bool) : Fm → Bool
  | Fm.var w => ρ w
  | Fm.bin c f g => if c then (fsem ρ f && fsem ρ g) else (fsem ρ f || fsem ρ g)

def lv : Fm → List ℕ
  | Fm.var w => [w]
  | Fm.bin _ f g => lv f ++ lv g

def gop (c : Bool) : GateOp := if c then GateOp.and else GateOp.or

def comp (off : ℕ) : Fm → List Gate × ℕ
  | Fm.var w => ([], w)
  | Fm.bin c f g =>
    ((comp off f).1 ++ (comp (off + (comp off f).1.length) g).1 ++
      [⟨gop c, [(comp off f).2, (comp (off + (comp off f).1.length) g).2]⟩],
      off + (comp off f).1.length + (comp (off + (comp off f).1.length) g).1.length)

lemma fsem_congr (ρ ρ' : ℕ → Bool) (f : Fm) (h : ∀ w ∈ lv f, ρ w = ρ' w) :
    fsem ρ f = fsem ρ' f := by
  induction f with
  | var w => exact h w (by simp [lv])
  | bin c f g ihf ihg =>
    simp only [fsem]
    rw [ihf (fun w hw => h w (by simp [lv, hw])), ihg (fun w hw => h w (by simp [lv, hw]))]

lemma comp_spec (n : ℕ) : ∀ (f : Fm) (B : List Gate), (∀ w ∈ lv f, w < n + B.length) →
    (comp (n + B.length) f).2 < n + B.length + (comp (n + B.length) f).1.length ∧
    (comp (n + B.length) f).1.length + 1 = (lv f).length ∧
    (∀ x : Fin n → Bool, val (B ++ (comp (n + B.length) f).1) x (comp (n + B.length) f).2 =
      fsem (val B x) f) ∧
    (∀ g ∈ (comp (n + B.length) f).1,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∧
    RB (n + B.length) (comp (n + B.length) f).1 := by
  intro f
  induction f with
  | var w =>
    intro B hl
    have hw := hl w (by simp [lv])
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp only [comp, List.length_nil]
      omega
    · simp [comp, lv]
    · intro x
      simp [comp, fsem]
    · intro g hg
      simp [comp] at hg
    · intro t ht
      simp [comp] at ht
  | bin c f g ihf ihg =>
    intro B hl
    obtain ⟨hr1, a2, a3, a4, a5⟩ := ihf B (fun w hw => hl w (by simp [lv, hw]))
    have e : n + (B ++ (comp (n + B.length) f).1).length =
        n + B.length + (comp (n + B.length) f).1.length := by
      simp only [List.length_append]
      omega
    have hg' := ihg (B ++ (comp (n + B.length) f).1) (fun w hw => by
      have := hl w (by simp [lv, hw])
      simp only [List.length_append]
      omega)
    rw [e] at hg'
    obtain ⟨hr2, b2, b3, b4, b5⟩ := hg'
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp only [comp, List.length_append, List.length_cons, List.length_nil]
      omega
    · simp only [comp, lv, List.length_append, List.length_cons, List.length_nil]
      omega
    · intro x
      simp only [comp]
      rw [← List.append_assoc, ← List.append_assoc, val_snoc, if_pos (by
        simp only [List.length_append]
        omega)]
      simp only [List.map_cons, List.map_nil]
      rw [b3 x, val_app_lt _ _ x _ (by simp only [List.length_append]; omega), a3 x,
        fsem_congr (val (B ++ (comp (n + B.length) f).1) x) (val B x) g (fun w hw =>
          val_app_lt _ _ x w (hl w (by simp [lv, hw])))]
      cases c <;> simp [gop, GateOp.eval, fsem]
    · intro q hq
      simp only [comp] at hq
      rcases List.mem_append.1 hq with h | h
      · rcases List.mem_append.1 h with h | h
        · exact a4 q h
        · exact b4 q h
      · have : q = ⟨gop c, [(comp (n + B.length) f).2,
            (comp (n + B.length + (comp (n + B.length) f).1.length) g).2]⟩ := by simpa using h
        rw [this]
        refine ⟨?_, rfl⟩
        cases c <;> simp [gop]
    · simp only [comp]
      refine RB_app _ _ _ (RB_app _ _ _ a5 b5) (RB_one _ _ _ _ ?_ ?_)
      · simp only [List.length_append]
        omega
      · simp only [List.length_append]
        omega

def oOr : Option Fm → Option Fm → Option Fm
  | none, o => o
  | some f, none => some f
  | some f, some g => some (Fm.bin false f g)

def oAnd : Option Fm → Option Fm → Option Fm
  | some f, some g => some (Fm.bin true f g)
  | _, _ => none

def semO (ρ : ℕ → Bool) : Option Fm → Bool
  | none => false
  | some f => fsem ρ f

def lvO : Option Fm → List ℕ
  | none => []
  | some f => lv f

lemma semO_oOr (ρ : ℕ → Bool) (o1 o2 : Option Fm) :
    semO ρ (oOr o1 o2) = (semO ρ o1 || semO ρ o2) := by
  cases o1 <;> cases o2 <;> simp [oOr, semO, fsem]

lemma semO_oAnd (ρ : ℕ → Bool) (o1 o2 : Option Fm) :
    semO ρ (oAnd o1 o2) = (semO ρ o1 && semO ρ o2) := by
  cases o1 <;> cases o2 <;> simp [oAnd, semO, fsem]

lemma lvO_oOr (o1 o2 : Option Fm) : lvO (oOr o1 o2) = lvO o1 ++ lvO o2 := by
  cases o1 <;> cases o2 <;> simp [oOr, lvO, lv]

def bigOr {α : Type} (l : List α) (f : α → Option Fm) : Option Fm :=
  l.foldr (fun x acc => oOr (f x) acc) none

lemma semO_bigOr {α : Type} (ρ : ℕ → Bool) (l : List α) (f : α → Option Fm) :
    semO ρ (bigOr l f) = true ↔ ∃ x ∈ l, semO ρ (f x) = true := by
  induction l with
  | nil => simp [bigOr, semO]
  | cons y l ih =>
    have e : bigOr (y :: l) f = oOr (f y) (bigOr l f) := rfl
    rw [e, semO_oOr, Bool.or_eq_true, ih]
    simp

lemma lvO_bigOr {α : Type} (l : List α) (f : α → Option Fm) :
    lvO (bigOr l f) = l.flatMap (fun x => lvO (f x)) := by
  induction l with
  | nil => simp [bigOr, lvO]
  | cons y l ih =>
    have e : bigOr (y :: l) f = oOr (f y) (bigOr l f) := rfl
    rw [e, lvO_oOr, ih]
    simp

lemma lv_ne (f : Fm) : ∃ w, w ∈ lv f := by
  induction f with
  | var w => exact ⟨w, by simp [lv]⟩
  | bin c f g ihf _ =>
    obtain ⟨w, hw⟩ := ihf
    exact ⟨w, by simp [lv, hw]⟩

/-- selecting some elements of a list as leaves -/
def sel {α : Type} (L : List α) (c : α → Bool) (e : α → ℕ) : Option Fm :=
  bigOr L (fun x => if c x then some (Fm.var (e x)) else none)

lemma sel_mem {α : Type} (L : List α) (c : α → Bool) (e : α → ℕ) (w : ℕ) :
    w ∈ lvO (sel L c e) ↔ ∃ x ∈ L, c x = true ∧ w = e x := by
  rw [sel, lvO_bigOr, List.mem_flatMap]
  constructor
  · rintro ⟨x, hx, hw⟩
    by_cases h : c x = true
    · rw [if_pos h] at hw
      exact ⟨x, hx, h, by simpa [lvO, lv] using hw⟩
    · rw [if_neg h] at hw
      simp [lvO] at hw
  · rintro ⟨x, hx, h, rfl⟩
    exact ⟨x, hx, by rw [if_pos h]; simp [lvO, lv]⟩

lemma sel_nodup {α : Type} (L : List α) (hL : L.Nodup) (c : α → Bool) (e : α → ℕ)
    (he : ∀ x y, e x = e y → x = y) : (lvO (sel L c e)).Nodup := by
  rw [sel, lvO_bigOr]
  induction L with
  | nil => simp
  | cons y L ih =>
    rw [List.flatMap_cons]
    have hL' := List.nodup_cons.1 hL
    have ih' := ih hL'.2
    by_cases h : c y = true
    · rw [if_pos h]
      simp only [lvO, lv, List.singleton_append]
      refine List.nodup_cons.2 ⟨?_, ih'⟩
      intro hm
      obtain ⟨x, hx, hw⟩ := List.mem_flatMap.1 hm
      by_cases h2 : c x = true
      · rw [if_pos h2] at hw
        have : e y = e x := by simpa [lvO, lv] using hw
        rw [he y x this] at hL'
        exact hL'.1 hx
      · rw [if_neg h2] at hw
        simp [lvO] at hw
    · rw [if_neg h]
      simpa [lvO] using ih'

lemma sel_sem {α : Type} (ρ : ℕ → Bool) (L : List α) (c : α → Bool) (e : α → ℕ) :
    semO ρ (sel L c e) = true ↔ ∃ x ∈ L, c x = true ∧ ρ (e x) = true := by
  rw [sel, semO_bigOr]
  constructor
  · rintro ⟨x, hx, hw⟩
    by_cases h : c x = true
    · rw [if_pos h] at hw
      exact ⟨x, hx, h, by simpa [semO, fsem] using hw⟩
    · rw [if_neg h] at hw
      simp [semO] at hw
  · rintro ⟨x, hx, h, hr⟩
    exact ⟨x, hx, by rw [if_pos h]; simpa [semO, fsem] using hr⟩

/-- a star: centre wire `cw` and the selected leaves -/
def star {α : Type} (cw : ℕ) (L : List α) (c : α → Bool) (e : α → ℕ) : Option Fm :=
  oAnd (some (Fm.var cw)) (sel L c e)

lemma star_mem {α : Type} (cw : ℕ) (L : List α) (c : α → Bool) (e : α → ℕ) (w : ℕ)
    (hw : w ∈ lvO (star cw L c e)) :
    (w = cw ∧ ∃ x ∈ L, c x = true) ∨ ∃ x ∈ L, c x = true ∧ w = e x := by
  unfold star at hw
  have hm := sel_mem L c e
  cases hs : sel L c e with
  | none =>
    rw [hs] at hw
    simp [oAnd, lvO] at hw
  | some g =>
    rw [hs] at hw hm
    simp only [oAnd, lvO, lv, List.singleton_append, List.mem_cons] at hw
    rcases hw with h | h
    · left
      obtain ⟨w', hw'⟩ := lv_ne g
      obtain ⟨x, hx, hc, _⟩ := (hm w').1 hw'
      exact ⟨h, x, hx, hc⟩
    · right
      exact (hm w).1 h

lemma star_nodup {α : Type} (cw : ℕ) (L : List α) (hL : L.Nodup) (c : α → Bool) (e : α → ℕ)
    (he : ∀ x y, e x = e y → x = y) (hc : ∀ x, e x ≠ cw) : (lvO (star cw L c e)).Nodup := by
  unfold star
  have hm := sel_mem L c e
  have hn := sel_nodup L hL c e he
  cases hs : sel L c e with
  | none => simp [oAnd, lvO]
  | some g =>
    rw [hs] at hm hn
    simp only [oAnd, lvO, lv, List.singleton_append]
    refine List.nodup_cons.2 ⟨?_, hn⟩
    intro h
    obtain ⟨x, _, _, hx⟩ := (hm cw).1 h
    exact hc x hx.symm

lemma star_sem {α : Type} (ρ : ℕ → Bool) (cw : ℕ) (L : List α) (c : α → Bool) (e : α → ℕ) :
    semO ρ (star cw L c e) = true ↔ ρ cw = true ∧ ∃ x ∈ L, c x = true ∧ ρ (e x) = true := by
  unfold star
  rw [semO_oAnd, Bool.and_eq_true, sel_sem]
  simp [semO, fsem]

/-- all stars: centred at points with the leaves chosen by `A`, centred at lines with the
leaves chosen by `Bm` -/
def SS (a b : ℕ) (A Bm : Fin a → Fin b → Bool) : Option Fm :=
  oOr (bigOr (List.finRange a) (fun p => star p.val (List.finRange b) (fun l => A p l)
      (fun l => a + l.val)))
    (bigOr (List.finRange b) (fun l => star (a + l.val) (List.finRange a) (fun p => Bm p l)
      (fun p => p.val)))

lemma SS_sem (ρ : ℕ → Bool) (a b : ℕ) (A Bm : Fin a → Fin b → Bool) :
    semO ρ (SS a b A Bm) = true ↔ ∃ (p : Fin a) (l : Fin b),
      (A p l = true ∨ Bm p l = true) ∧ ρ p.val = true ∧ ρ (a + l.val) = true := by
  unfold SS
  rw [semO_oOr, Bool.or_eq_true, semO_bigOr, semO_bigOr]
  constructor
  · rintro (⟨p, _, h⟩ | ⟨l, _, h⟩)
    · obtain ⟨h1, l, _, h2, h3⟩ := (star_sem ρ _ _ _ _).1 h
      exact ⟨p, l, Or.inl h2, h1, h3⟩
    · obtain ⟨h1, p, _, h2, h3⟩ := (star_sem ρ _ _ _ _).1 h
      exact ⟨p, l, Or.inr h2, h3, h1⟩
  · rintro ⟨p, l, h | h, h1, h2⟩
    · exact Or.inl ⟨p, List.mem_finRange p, (star_sem ρ _ _ _ _).2
        ⟨h1, l, List.mem_finRange l, h, h2⟩⟩
    · exact Or.inr ⟨l, List.mem_finRange l, (star_sem ρ _ _ _ _).2
        ⟨h2, p, List.mem_finRange p, h, h1⟩⟩

lemma SS_mem (a b : ℕ) (A Bm : Fin a → Fin b → Bool) (w : ℕ)
    (hw : w ∈ lvO (SS a b A Bm)) :
    ∃ (p : Fin a) (l : Fin b), (A p l = true ∨ Bm p l = true) ∧ (w = p.val ∨ w = a + l.val) := by
  unfold SS at hw
  rw [lvO_oOr, lvO_bigOr, lvO_bigOr, List.mem_append, List.mem_flatMap, List.mem_flatMap] at hw
  rcases hw with ⟨p, _, h⟩ | ⟨l, _, h⟩
  · rcases star_mem _ _ _ _ w h with ⟨h1, l, _, h2⟩ | ⟨l, _, h2, h3⟩
    · exact ⟨p, l, Or.inl h2, Or.inl h1⟩
    · exact ⟨p, l, Or.inl h2, Or.inr h3⟩
  · rcases star_mem _ _ _ _ w h with ⟨h1, p, _, h2⟩ | ⟨p, _, h2, h3⟩
    · exact ⟨p, l, Or.inr h2, Or.inr h1⟩
    · exact ⟨p, l, Or.inr h2, Or.inl h3⟩

lemma flat_nodup {α : Type} (L : List α) (hL : L.Nodup) (f : α → List ℕ)
    (h1 : ∀ x, (f x).Nodup) (h2 : ∀ x y w, x ≠ y → w ∈ f x → w ∈ f y → False) :
    (L.flatMap f).Nodup := by
  induction L with
  | nil => simp
  | cons y L ih =>
    rw [List.flatMap_cons]
    have hL' := List.nodup_cons.1 hL
    refine List.Nodup.append (h1 y) (ih hL'.2) ?_
    intro w hw1 hw2
    obtain ⟨x, hx, hw⟩ := List.mem_flatMap.1 hw2
    refine h2 y x w ?_ hw1 hw
    rintro rfl
    exact hL'.1 hx

lemma SS_nodup (a b : ℕ) (A Bm : Fin a → Fin b → Bool)
    (hA1 : ∀ p p' l, A p l = true → A p' l = true → p = p')
    (hB1 : ∀ p l l', Bm p l = true → Bm p l' = true → l = l')
    (hX1 : ∀ p l l', A p l = true → Bm p l' = true → False)
    (hX2 : ∀ p p' l, A p l = true → Bm p' l = true → False) :
    (lvO (SS a b A Bm)).Nodup := by
  unfold SS
  rw [lvO_oOr, lvO_bigOr, lvO_bigOr]
  refine List.Nodup.append ?_ ?_ ?_
  · refine flat_nodup _ (List.nodup_finRange a) _ ?_ ?_
    · intro p
      refine star_nodup _ _ (List.nodup_finRange b) _ _ ?_ ?_
      · intro x y h
        exact Fin.ext (by omega)
      · intro x
        have := p.isLt
        omega
    · intro p p' w hne h h'
      rcases star_mem _ _ _ _ w h with ⟨h1, l, _, h2⟩ | ⟨l, _, h2, h3⟩
      · rcases star_mem _ _ _ _ w h' with ⟨h1', l', _, h2'⟩ | ⟨l', _, h2', h3'⟩
        · exact hne (Fin.ext (by omega))
        · have := p.isLt
          omega
      · rcases star_mem _ _ _ _ w h' with ⟨h1', l', _, h2'⟩ | ⟨l', _, h2', h3'⟩
        · have := p'.isLt
          omega
        · have hl : l = l' := Fin.ext (by omega)
          subst hl
          exact hne (hA1 p p' l h2 h2')
  · refine flat_nodup _ (List.nodup_finRange b) _ ?_ ?_
    · intro l
      refine star_nodup _ _ (List.nodup_finRange a) _ _ ?_ ?_
      · intro x y h
        exact Fin.ext h
      · intro x
        have := x.isLt
        omega
    · intro l l' w hne h h'
      rcases star_mem _ _ _ _ w h with ⟨h1, p, _, h2⟩ | ⟨p, _, h2, h3⟩
      · rcases star_mem _ _ _ _ w h' with ⟨h1', p', _, h2'⟩ | ⟨p', _, h2', h3'⟩
        · exact hne (Fin.ext (by omega))
        · have := p'.isLt
          omega
      · rcases star_mem _ _ _ _ w h' with ⟨h1', p', _, h2'⟩ | ⟨p', _, h2', h3'⟩
        · have := p.isLt
          omega
        · have hp : p = p' := Fin.ext (by omega)
          subst hp
          exact hne (hB1 p l l' h2 h2')
  · intro w hw1 hw2
    obtain ⟨p, _, h⟩ := List.mem_flatMap.1 hw1
    obtain ⟨l, _, h'⟩ := List.mem_flatMap.1 hw2
    rcases star_mem _ _ _ _ w h with ⟨h1, l1, _, h2⟩ | ⟨l1, _, h2, h3⟩
    · rcases star_mem _ _ _ _ w h' with ⟨h1', p', _, h2'⟩ | ⟨p', _, h2', h3'⟩
      · have := p.isLt
        omega
      · have hp : p = p' := Fin.ext (by omega)
        subst hp
        exact hX1 p l1 l h2 h2'
    · rcases star_mem _ _ _ _ w h' with ⟨h1', p', _, h2'⟩ | ⟨p', _, h2', h3'⟩
      · have hl : l1 = l := Fin.ext (by omega)
        subst hl
        exact hX2 p p' l1 h2 h2'
      · have := p'.isLt
        omega

lemma semO_map {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (o : Option ℕ) :
    semO (val gs x) (o.map Fm.var) = ov gs x o := by
  cases o <;> rfl

lemma lvO_map_len (o : Option ℕ) : (lvO (o.map Fm.var)).length ≤ 1 := by
  cases o <;> simp [lvO, lv]

lemma lvO_map_mem (o : Option ℕ) (w : ℕ) (h : w ∈ lvO (o.map Fm.var)) : o = some w := by
  cases o with
  | none => simp [lvO] at h
  | some u =>
    have : w = u := by simpa [lvO, lv] using h
    rw [this]

lemma rin_card (n : ℕ) (gs : List Gate) (K : Finset ℕ) (j : ℕ)
    (hlen : ∀ i ∈ K, (gs.getD i ⟨GateOp.or, []⟩).inputs.length = 2)
    (hjK : j ∈ K)
    (hrd : ∀ i ∈ K, i ≠ j → ∃ k ∈ K, n + i ∈ (gs.getD k ⟨GateOp.or, []⟩).inputs) :
    ((K.biUnion (fun i => (gs.getD i ⟨GateOp.or, []⟩).inputs.toFinset)).filter
      (fun w => w < n)).card ≤ K.card + 1 := by
  have h1 : (K.biUnion (fun i => (gs.getD i ⟨GateOp.or, []⟩).inputs.toFinset)).card ≤
      2 * K.card := by
    calc (K.biUnion (fun i => (gs.getD i ⟨GateOp.or, []⟩).inputs.toFinset)).card
        ≤ ∑ i ∈ K, ((gs.getD i ⟨GateOp.or, []⟩).inputs.toFinset).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _i ∈ K, 2 := Finset.sum_le_sum (fun i hi => by
          have h := List.toFinset_card_le (gs.getD i ⟨GateOp.or, []⟩).inputs
          rw [hlen i hi] at h
          exact h)
      _ = 2 * K.card := by simp [mul_comm]
  have h2 : ((K.erase j).image (fun i => n + i)) ⊆
      (K.biUnion (fun i => (gs.getD i ⟨GateOp.or, []⟩).inputs.toFinset)).filter
        (fun w => ¬ w < n) := by
    intro w hw
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hw
    obtain ⟨hij, hiK⟩ := Finset.mem_erase.1 hi
    obtain ⟨k, hk, hmem⟩ := hrd i hiK hij
    exact Finset.mem_filter.2 ⟨Finset.mem_biUnion.2 ⟨k, hk, List.mem_toFinset.2 hmem⟩,
      by omega⟩
  have h3 : ((K.erase j).image (fun i => n + i)).card = K.card - 1 := by
    rw [Finset.card_image_of_injective _ (fun x y h => by simpa using h),
      Finset.card_erase_of_mem hjK]
  have h4 := Finset.card_le_card h2
  have h5 : ∀ R : Finset ℕ, (R.filter (fun w => w < n)).card +
      (R.filter (fun w => ¬ w < n)).card = R.card := by
    intro R
    exact Finset.card_filter_add_card_filter_not (s := R) (fun w => w < n)
  have h5 := h5 (K.biUnion (fun i => (gs.getD i ⟨GateOp.or, []⟩).inputs.toFinset))
  have h6 : 0 < K.card := Finset.card_pos.2 ⟨j, hjK⟩
  omega

def pr (a b : ℕ) (p : Fin a) (l : Fin b) : Fin (a + b) → Bool :=
  fun e => decide (e = Fin.castAdd b p ∨ e = Fin.natAdd a l)

def Lost (a b : ℕ) (I : Fin a → Fin b → Prop) (gs : List Gate) (j o : ℕ) (p : Fin a)
    (l : Fin b) : Prop :=
  I p l ∧ val (gs.set j ⟨GateOp.or, []⟩) (pr a b p l) o = false

theorem main : ∀ (a b : ℕ) (I : Fin a → Fin b → Prop) (C : PEqualNP.CircuitLowerBounds.Circuit) (j : ℕ) (K : Finset ℕ), (∀ (p p' : Fin a) (l l' : Fin b), p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → PEqualNP.MetaComplexity.NestedCover.ReadsBack (a + b) C → (∀ z : Fin (a + b) → Bool, PEqualNP.MetaComplexity.circuitFun (a + b) C z = true ↔ ∃ (p : Fin a) (l : Fin b), I p l ∧ z (Fin.castAdd b p) = true ∧ z (Fin.natAdd a l) = true) → j < C.gates.length → (∀ v : Fin (a + b), (C.wires (List.ofFn (fun u : Fin (a + b) => decide (u = v)))).getD (a + b + j) false = false) → (∃ k k' : ℕ, k ≠ k' ∧ k < C.gates.length ∧ k' < C.gates.length ∧ a + b + j ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs ∧ a + b + j ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k').inputs) → j ∈ K → (∀ i ∈ K, i ≤ j) → (∀ i ∈ K, ∀ w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).inputs, a + b ≤ w → w - (a + b) ∈ K) → (∀ i ∈ K, i ≠ j → ∃ k ∈ K, a + b + i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs) → (∀ k < C.gates.length, k ∉ K → ∀ w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs, a + b ≤ w → w - (a + b) ∈ K → w = a + b + j) → ¬ (a + b ≤ C.output ∧ C.output - (a + b) ∈ K) → (∀ (p p' : Fin a) (l l' : Fin b), (I p l ∧ PEqualNP.MetaComplexity.circuitFun (a + b) (PEqualNP.CircuitLowerBounds.Circuit.mk (C.gates.set j (PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [])) C.output) (fun e1 : Fin (a + b) => decide (e1 = Fin.castAdd b p ∨ e1 = Fin.natAdd a l)) = false) → (I p' l ∧ PEqualNP.MetaComplexity.circuitFun (a + b) (PEqualNP.CircuitLowerBounds.Circuit.mk (C.gates.set j (PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [])) C.output) (fun e2 : Fin (a + b) => decide (e2 = Fin.castAdd b p' ∨ e2 = Fin.natAdd a l)) = false) → (I p l' ∧ PEqualNP.MetaComplexity.circuitFun (a + b) (PEqualNP.CircuitLowerBounds.Circuit.mk (C.gates.set j (PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [])) C.output) (fun e3 : Fin (a + b) => decide (e3 = Fin.castAdd b p ∨ e3 = Fin.natAdd a l')) = false) → p' = p ∨ l' = l) → ∃ C' : PEqualNP.CircuitLowerBounds.Circuit, (∀ g ∈ C'.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (a + b) C' ∧ C'.size < C.size ∧ (∀ z : Fin (a + b) → Bool, PEqualNP.MetaComplexity.circuitFun (a + b) C' z = true ↔ ∃ (p : Fin a) (l : Fin b), I p l ∧ z (Fin.castAdd b p) = true ∧ z (Fin.natAdd a l) = true) := by
  intro a b I C j K _ hao hrb hf hj hoh hrd2 hjK hKle hcl hrd hpriv hout hstar
  classical
  have hf' : ∀ z : Fin (a + b) → Bool, val C.gates z C.output = true ↔
      ∃ (p : Fin a) (l : Fin b), I p l ∧ z (Fin.castAdd b p) = true ∧
        z (Fin.natAdd a l) = true := hf
  have hoh' : ∀ v : Fin (a + b),
      val C.gates (fun u : Fin (a + b) => decide (u = v)) (a + b + j) = false := hoh
  have hstar' : ∀ (p p' : Fin a) (l l' : Fin b), Lost a b I C.gates j C.output p l →
      Lost a b I C.gates j C.output p' l → Lost a b I C.gates j C.output p l' →
      p' = p ∨ l' = l := hstar
  have hgo : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := fun g hg => (hao g hg).1
  have hgo0 : ∀ g ∈ C.gates.set j ⟨GateOp.or, []⟩, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    rcases List.mem_or_eq_of_mem_set hg with h | h
    · exact hgo g h
    · rw [h]
      exact Or.inr rfl
  have hKlt : ∀ i ∈ K, i < C.gates.length := fun i hi => lt_of_le_of_lt (hKle i hi) hj
  have hInv := inv_run (a + b) K C.gates j hao hrb hj hjK hpriv C.gates.length le_rfl
  generalize run (a + b) K C.gates C.gates.length = s at hInv
  have hbase : ∀ x : Fin (a + b) → Bool,
      ov s.1 x (s.2 C.output) = val (C.gates.set j ⟨GateOp.or, []⟩) x C.output := by
    intro x
    by_cases h : C.output < a + b + C.gates.length
    · refine hInv.sm x C.output h ?_
      by_cases h1 : C.output < a + b
      · exact Or.inl h1
      · exact Or.inr (Or.inl (fun h2 => hout ⟨by omega, h2⟩))
    · rw [hInv.hi C.output (by omega), val_ge _ x _ (by simp; omega)]
      rfl
  obtain ⟨k, k', hkk, hk, hk', hkr, hkr'⟩ := hrd2
  have hbl : s.1.length + K.card + 2 ≤ C.gates.length := by
    have hc := hInv.cnt
    have hkj : j < k := by
      have := hrb k hk _ hkr
      omega
    have hkj' : j < k' := by
      have := hrb k' hk' _ hkr'
      omega
    have hkK : k ∉ K := fun h => by
      have := hKle k h
      omega
    have hkK' : k' ∉ K := fun h => by
      have := hKle k' h
      omega
    have hsub : insert k (insert k' K) ⊆ (Finset.range C.gates.length).filter
        (fun i => i ∈ K ∨ a + b + j ∈ (C.gates.getD i ⟨GateOp.or, []⟩).inputs) := by
      intro i hi
      rw [Finset.mem_insert, Finset.mem_insert] at hi
      rw [Finset.mem_filter, Finset.mem_range]
      rcases hi with rfl | rfl | hi
      · exact ⟨hk, Or.inr hkr⟩
      · exact ⟨hk', Or.inr hkr'⟩
      · exact ⟨hKlt i hi, Or.inl hi⟩
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem (by simp [hkk, hkK]),
      Finset.card_insert_of_notMem hkK'] at hcard
    omega
  have hrin := rin_card (a + b) C.gates K j (fun i hi => by
    rw [getD_get _ i (hKlt i hi)]
    exact (hao _ (List.getElem_mem _)).2) hjK hrd
  have hlostj : ∀ p l, Lost a b I C.gates j C.output p l →
      val C.gates (pr a b p l) (a + b + j) = true := by
    rintro p l ⟨hI, hl⟩
    by_contra hne
    have hne' : val C.gates (pr a b p l) (a + b + j) = false := by simpa using hne
    rw [cmp_eq C.gates j _ hne' C.output] at hl
    have h3 : val C.gates (pr a b p l) C.output = true :=
      (hf' _).2 ⟨p, l, hI, by simp [pr], by simp [pr]⟩
    rw [h3] at hl
    exact absurd hl (by simp)
  have hreadP : ∀ p l, Lost a b I C.gates j C.output p l →
      ∃ i ∈ K, p.val ∈ (C.gates.getD i ⟨GateOp.or, []⟩).inputs := by
    intro p l hL
    by_contra hno
    have h1 := hlostj p l hL
    have h2 := dep C.gates K hKlt hcl (pr a b p l)
      (fun u : Fin (a + b) => decide (u = Fin.natAdd a l)) (by
        intro u hu
        have hup : u ≠ Fin.castAdd b p := by
          rintro rfl
          exact hno hu
        simp [pr, hup]) j hjK
    rw [h2, hoh' (Fin.natAdd a l)] at h1
    exact absurd h1 (by simp)
  have hreadQ : ∀ p l, Lost a b I C.gates j C.output p l →
      ∃ i ∈ K, a + l.val ∈ (C.gates.getD i ⟨GateOp.or, []⟩).inputs := by
    intro p l hL
    by_contra hno
    have h1 := hlostj p l hL
    have h2 := dep C.gates K hKlt hcl (pr a b p l)
      (fun u : Fin (a + b) => decide (u = Fin.castAdd b p)) (by
        intro u hu
        have hup : u ≠ Fin.natAdd a l := by
          rintro rfl
          exact hno hu
        simp [pr, hup]) j hjK
    rw [h2, hoh' (Fin.castAdd b p)] at h1
    exact absurd h1 (by simp)
  obtain ⟨A, hA⟩ : ∃ A : Fin a → Fin b → Bool, ∀ p l, A p l = true ↔
      (Lost a b I C.gates j C.output p l ∧
        ∀ p', Lost a b I C.gates j C.output p' l → p' = p) :=
    ⟨fun p l => decide (Lost a b I C.gates j C.output p l ∧
        ∀ p', Lost a b I C.gates j C.output p' l → p' = p), fun p l => decide_eq_true_iff⟩
  obtain ⟨Bm, hB⟩ : ∃ Bm : Fin a → Fin b → Bool, ∀ p l, Bm p l = true ↔
      (Lost a b I C.gates j C.output p l ∧
        ¬ ∀ p', Lost a b I C.gates j C.output p' l → p' = p) :=
    ⟨fun p l => decide (Lost a b I C.gates j C.output p l ∧
        ¬ ∀ p', Lost a b I C.gates j C.output p' l → p' = p), fun p l => decide_eq_true_iff⟩
  have hAB : ∀ p l, (A p l = true ∨ Bm p l = true) ↔ Lost a b I C.gates j C.output p l := by
    intro p l
    rw [hA, hB]
    constructor
    · rintro (h | h) <;> exact h.1
    · intro h
      by_cases hu : ∀ p', Lost a b I C.gates j C.output p' l → p' = p
      · exact Or.inl ⟨h, hu⟩
      · exact Or.inr ⟨h, hu⟩
  have hA1 : ∀ p p' l, A p l = true → A p' l = true → p = p' := by
    intro p p' l h h'
    exact ((hA p' l).1 h').2 p ((hA p l).1 h).1
  have hB1 : ∀ p l l', Bm p l = true → Bm p l' = true → l = l' := by
    intro p l l' h h'
    obtain ⟨hL, hn⟩ := (hB p l).1 h
    obtain ⟨hL', _⟩ := (hB p l').1 h'
    rw [not_forall] at hn
    obtain ⟨p', hp'⟩ := hn
    rw [Classical.not_imp] at hp'
    rcases hstar' p p' l l' hL hp'.1 hL' with h3 | h3
    · exact absurd h3 hp'.2
    · exact h3.symm
  have hX1 : ∀ p l l', A p l = true → Bm p l' = true → False := by
    intro p l l' h h'
    obtain ⟨hL, hu⟩ := (hA p l).1 h
    obtain ⟨hL', hn⟩ := (hB p l').1 h'
    rw [not_forall] at hn
    obtain ⟨p', hp'⟩ := hn
    rw [Classical.not_imp] at hp'
    rcases hstar' p p' l' l hL' hp'.1 hL with h3 | h3
    · exact hp'.2 h3
    · rw [h3] at hu
      exact hp'.2 (hu p' hp'.1)
  have hX2 : ∀ p p' l, A p l = true → Bm p' l = true → False := by
    intro p p' l h h'
    obtain ⟨hL, hu⟩ := (hA p l).1 h
    obtain ⟨hL', hn⟩ := (hB p' l).1 h'
    apply hn
    intro p'' hp''
    rw [hu p'' hp'', hu p' hL']
  have hSn := SS_nodup a b A Bm hA1 hB1 hX1 hX2
  have hSlt : ∀ w ∈ lvO (SS a b A Bm), w < a + b := by
    intro w hw
    obtain ⟨p, l, _, hw'⟩ := SS_mem a b A Bm w hw
    have := p.isLt
    have := l.isLt
    omega
  have hSlen : (lvO (SS a b A Bm)).length ≤ K.card + 1 := by
    have hsub : (lvO (SS a b A Bm)).toFinset ⊆
        (K.biUnion (fun i => (C.gates.getD i ⟨GateOp.or, []⟩).inputs.toFinset)).filter
          (fun w => w < a + b) := by
      intro w hw
      have hw2 := List.mem_toFinset.1 hw
      obtain ⟨p, l, hab, hw'⟩ := SS_mem a b A Bm w hw2
      have hL := (hAB p l).1 hab
      rw [Finset.mem_filter, Finset.mem_biUnion]
      refine ⟨?_, hSlt w hw2⟩
      rcases hw' with rfl | rfl
      · obtain ⟨i, hi, hm⟩ := hreadP p l hL
        exact ⟨i, hi, List.mem_toFinset.2 hm⟩
      · obtain ⟨i, hi, hm⟩ := hreadQ p l hL
        exact ⟨i, hi, List.mem_toFinset.2 hm⟩
    have h := Finset.card_le_card hsub
    rw [List.toFinset_card_of_nodup hSn] at h
    omega
  have hSsem : ∀ z : Fin (a + b) → Bool, semO (val s.1 z) (SS a b A Bm) = true ↔
      ∃ (p : Fin a) (l : Fin b), Lost a b I C.gates j C.output p l ∧
        z (Fin.castAdd b p) = true ∧ z (Fin.natAdd a l) = true := by
    intro z
    rw [SS_sem]
    have e1 : ∀ p : Fin a, val s.1 z p.val = z (Fin.castAdd b p) := by
      intro p
      rw [val_lt s.1 z p.val (by have := p.isLt; omega)]
      rfl
    have e2 : ∀ l : Fin b, val s.1 z (a + l.val) = z (Fin.natAdd a l) := by
      intro l
      rw [val_lt s.1 z (a + l.val) (by have := l.isLt; omega)]
      rfl
    simp only [e1, e2, hAB]
  have hT : ∀ z : Fin (a + b) → Bool,
      semO (val s.1 z) (oOr ((s.2 C.output).map Fm.var) (SS a b A Bm)) = true ↔
      ∃ (p : Fin a) (l : Fin b), I p l ∧ z (Fin.castAdd b p) = true ∧
        z (Fin.natAdd a l) = true := by
    intro z
    rw [semO_oOr, Bool.or_eq_true, semO_map, hbase z, hSsem z]
    constructor
    · rintro (h | ⟨p, l, hL, h1, h2⟩)
      · exact (hf' z).1 (cmp_le C.gates hgo j z _ h)
      · exact ⟨p, l, hL.1, h1, h2⟩
    · rintro ⟨p, l, hI, h1, h2⟩
      by_cases hL : Lost a b I C.gates j C.output p l
      · exact Or.inr ⟨p, l, hL, h1, h2⟩
      · left
        have h3 : val (C.gates.set j ⟨GateOp.or, []⟩) (pr a b p l) C.output = true := by
          by_contra h4
          exact hL ⟨hI, by simpa using h4⟩
        refine mono2 _ hgo0 (pr a b p l) z ?_ _ h3
        intro v hv
        simp only [pr, decide_eq_true_eq] at hv
        rcases hv with rfl | rfl
        · exact h1
        · exact h2
  cases hFo : oOr ((s.2 C.output).map Fm.var) (SS a b A Bm) with
  | none =>
    refine ⟨⟨s.1, a + b + s.1.length⟩, hInv.ao, hInv.rb, ?_, ?_⟩
    · show s.1.length < C.gates.length
      omega
    · intro z
      have h := hT z
      rw [hFo] at h
      rw [← h]
      show val s.1 z (a + b + s.1.length) = true ↔ _
      rw [val_ge s.1 z _ le_rfl]
      simp [semO]
  | some F =>
    have hlv : lv F = lvO ((s.2 C.output).map Fm.var) ++ lvO (SS a b A Bm) := by
      rw [← lvO_oOr, hFo]
      rfl
    have hleaf : ∀ w ∈ lv F, w < a + b + s.1.length := by
      intro w hw
      rw [hlv] at hw
      rcases List.mem_append.1 hw with h | h
      · exact hInv.bd _ w (lvO_map_mem _ w h)
      · have := hSlt w h
        omega
    obtain ⟨_, c2, c3, c4, c5⟩ := comp_spec (a + b) F s.1 hleaf
    refine ⟨⟨s.1 ++ (comp (a + b + s.1.length) F).1, (comp (a + b + s.1.length) F).2⟩,
      ?_, ?_, ?_, ?_⟩
    · intro g hg
      rcases List.mem_append.1 hg with h | h
      · exact hInv.ao g h
      · exact c4 g h
    · exact RB_app _ _ _ hInv.rb c5
    · show (s.1 ++ (comp (a + b + s.1.length) F).1).length < C.gates.length
      have h1 := lvO_map_len (s.2 C.output)
      rw [hlv, List.length_append] at c2
      rw [List.length_append]
      omega
    · intro z
      have h := hT z
      rw [hFo] at h
      rw [← h]
      show val (s.1 ++ (comp (a + b + s.1.length) F).1) z (comp (a + b + s.1.length) F).2 =
        true ↔ _
      rw [c3 z]
      rfl

end PEqualNP.Outside.L_meta_3140_aux

theorem PEqualNP.Outside.L_meta_3140 : ∀ (a b : ℕ) (I : Fin a → Fin b → Prop) (C : PEqualNP.CircuitLowerBounds.Circuit) (j : ℕ) (K : Finset ℕ), (∀ (p p' : Fin a) (l l' : Fin b), p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → PEqualNP.MetaComplexity.NestedCover.ReadsBack (a + b) C → (∀ z : Fin (a + b) → Bool, PEqualNP.MetaComplexity.circuitFun (a + b) C z = true ↔ ∃ (p : Fin a) (l : Fin b), I p l ∧ z (Fin.castAdd b p) = true ∧ z (Fin.natAdd a l) = true) → j < C.gates.length → (∀ v : Fin (a + b), (C.wires (List.ofFn (fun u : Fin (a + b) => decide (u = v)))).getD (a + b + j) false = false) → (∃ k k' : ℕ, k ≠ k' ∧ k < C.gates.length ∧ k' < C.gates.length ∧ a + b + j ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs ∧ a + b + j ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k').inputs) → j ∈ K → (∀ i ∈ K, i ≤ j) → (∀ i ∈ K, ∀ w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).inputs, a + b ≤ w → w - (a + b) ∈ K) → (∀ i ∈ K, i ≠ j → ∃ k ∈ K, a + b + i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs) → (∀ k < C.gates.length, k ∉ K → ∀ w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs, a + b ≤ w → w - (a + b) ∈ K → w = a + b + j) → ¬ (a + b ≤ C.output ∧ C.output - (a + b) ∈ K) → (∀ (p p' : Fin a) (l l' : Fin b), (I p l ∧ PEqualNP.MetaComplexity.circuitFun (a + b) (PEqualNP.CircuitLowerBounds.Circuit.mk (C.gates.set j (PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [])) C.output) (fun e1 : Fin (a + b) => decide (e1 = Fin.castAdd b p ∨ e1 = Fin.natAdd a l)) = false) → (I p' l ∧ PEqualNP.MetaComplexity.circuitFun (a + b) (PEqualNP.CircuitLowerBounds.Circuit.mk (C.gates.set j (PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [])) C.output) (fun e2 : Fin (a + b) => decide (e2 = Fin.castAdd b p' ∨ e2 = Fin.natAdd a l)) = false) → (I p l' ∧ PEqualNP.MetaComplexity.circuitFun (a + b) (PEqualNP.CircuitLowerBounds.Circuit.mk (C.gates.set j (PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [])) C.output) (fun e3 : Fin (a + b) => decide (e3 = Fin.castAdd b p ∨ e3 = Fin.natAdd a l')) = false) → p' = p ∨ l' = l) → ∃ C' : PEqualNP.CircuitLowerBounds.Circuit, (∀ g ∈ C'.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (a + b) C' ∧ C'.size < C.size ∧ (∀ z : Fin (a + b) → Bool, PEqualNP.MetaComplexity.circuitFun (a + b) C' z = true ↔ ∃ (p : Fin a) (l : Fin b), I p l ∧ z (Fin.castAdd b p) = true ∧ z (Fin.natAdd a l) = true) := by
  exact PEqualNP.Outside.L_meta_3140_aux.main
