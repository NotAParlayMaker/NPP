import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1701

open PEqualNP.CircuitLowerBounds

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem eval_eq (C : Circuit) (x : List Bool) :
    C.eval x = (C.gates.foldl stp x).getD C.output false := rfl

theorem getD_snoc {α : Type} (W : List α) (v d : α) (i : ℕ) :
    (W ++ [v]).getD i d = if i = W.length then v else W.getD i d := by
  rcases lt_trichotomy i W.length with h | h | h
  · rw [if_neg (by omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · subst h
    simp [List.getD_eq_getElem?_getD]
  · rw [if_neg (by omega)]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

theorem ev_and (g : Gate) (f : ℕ → Bool) (h : g.op = GateOp.and) :
    (g.op.eval (g.inputs.map f) = true ↔ ∀ i ∈ g.inputs, f i = true) := by
  rw [h]
  simp [GateOp.eval]

theorem ev_or (g : Gate) (f : ℕ → Bool) (h : g.op = GateOp.or) :
    (g.op.eval (g.inputs.map f) = true ↔ ∃ i ∈ g.inputs, f i = true) := by
  rw [h]
  simp [GateOp.eval]

theorem mono : ∀ (gs : List Gate) (W1 W2 : List Bool), W1.length = W2.length →
    (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
    (∀ i, W1.getD i false = true → W2.getD i false = true) →
    ∀ i, (gs.foldl stp W1).getD i false = true → (gs.foldl stp W2).getD i false = true := by
  intro gs
  induction gs with
  | nil => intro W1 W2 _ _ H; simpa using H
  | cons g gs ih =>
    intro W1 W2 hl hop H
    rw [List.foldl_cons, List.foldl_cons]
    apply ih (stp W1 g) (stp W2 g) (by simp [stp, hl])
      (fun g' hg' => hop g' (List.mem_cons_of_mem _ hg'))
    intro i
    simp only [stp, getD_snoc, hl]
    split_ifs
    · rcases hop g List.mem_cons_self with ha | ho
      · rw [ev_and g _ ha, ev_and g _ ha]
        intro h k hk
        exact H k (h k hk)
      · rw [ev_or g _ ho, ev_or g _ ho]
        rintro ⟨k, hk, h⟩
        exact ⟨k, hk, H k h⟩
    · exact H i

theorem ofFn_getD {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    (List.ofFn x).getD i false = if h : i < n then x ⟨i, h⟩ else false := by
  rw [List.getD_eq_getElem?_getD]
  split_ifs with h
  · rw [List.getElem?_eq_getElem (by simpa using h)]
    simp
  · rw [List.getElem?_eq_none (by simpa using h)]
    rfl

theorem eval_mono_fn {n : ℕ} (gates : List Gate)
    (hg : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : Fin n → Bool) (hxy : ∀ v, x v = true → y v = true) (o : ℕ)
    (h : Circuit.eval ⟨gates, o⟩ (List.ofFn x) = true) :
    Circuit.eval ⟨gates, o⟩ (List.ofFn y) = true := by
  rw [eval_eq] at h ⊢
  refine mono gates _ _ (by simp) hg ?_ o h
  intro i
  rw [ofFn_getD, ofFn_getD]
  split_ifs with hi
  · exact hxy _
  · exact id

def isAO : GateOp → Bool
  | GateOp.and => true
  | GateOp.or => true
  | _ => false

theorem isAO_iff (o : GateOp) (h : isAO o = true) : o = GateOp.and ∨ o = GateOp.or := by
  cases o <;> simp [isAO] at h ⊢

def gw (M : ℕ) (w : List ℕ) (g : Gate) : ℕ :=
  match g.op with
  | GateOp.and => (g.inputs.map fun i => w.getD i 0).foldr (fun a b => a &&& b) M
  | GateOp.or => (g.inputs.map fun i => w.getD i 0).foldr (fun a b => a ||| b) 0
  | _ => 0

def bstp (M : ℕ) (w : List ℕ) (g : Gate) : List ℕ := w ++ [gw M w g]

theorem foldr_land (M j : ℕ) (hM : M.testBit j = true) (f : ℕ → ℕ) (l : List ℕ) :
    ((l.map f).foldr (fun a b => a &&& b) M).testBit j =
      (l.map fun i => (f i).testBit j).all id := by
  induction l with
  | nil => simpa using hM
  | cons a l ih =>
    simp only [List.map_cons, List.foldr_cons, Nat.testBit_and, ih, List.all_cons, id]

theorem foldr_lor (j : ℕ) (f : ℕ → ℕ) (l : List ℕ) :
    ((l.map f).foldr (fun a b => a ||| b) 0).testBit j =
      (l.map fun i => (f i).testBit j).any id := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.foldr_cons, Nat.testBit_or, ih, List.any_cons, id]

theorem gw_bit (M j : ℕ) (hM : M.testBit j = true) (W : List ℕ) (w : List Bool)
    (H : ∀ i, (W.getD i 0).testBit j = w.getD i false) (g : Gate)
    (hg : g.op = GateOp.and ∨ g.op = GateOp.or) :
    (gw M W g).testBit j = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  obtain ⟨op, ins⟩ := g
  rcases hg with h | h
  · simp only at h
    subst h
    simp only [gw, GateOp.eval]
    rw [foldr_land M j hM]
    simp only [H]
  · simp only at h
    subst h
    simp only [gw, GateOp.eval]
    rw [foldr_lor j]
    simp only [H]

theorem bp (M j : ℕ) (hM : M.testBit j = true) : ∀ (gs : List Gate) (W : List ℕ) (w : List Bool),
    W.length = w.length → (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
    (∀ i, (W.getD i 0).testBit j = w.getD i false) →
    ∀ i, ((gs.foldl (bstp M) W).getD i 0).testBit j = (gs.foldl stp w).getD i false := by
  intro gs
  induction gs with
  | nil => intro W w _ _ H; simpa using H
  | cons g gs ih =>
    intro W w hl hop H
    rw [List.foldl_cons, List.foldl_cons]
    apply ih (bstp M W g) (stp w g) (by simp [bstp, stp, hl])
      (fun g' hg' => hop g' (List.mem_cons_of_mem _ hg'))
    intro i
    simp only [bstp, stp, getD_snoc, hl]
    split_ifs
    · exact gw_bit M j hM W w H g (hop g List.mem_cons_self)
    · exact H i

theorem bp_eval (M j : ℕ) (hM : M.testBit j = true) (gs : List Gate)
    (hop : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) (X : List ℕ) (o : ℕ) :
    Circuit.eval ⟨gs, o⟩ (X.map fun n => n.testBit j) =
      ((gs.foldl (bstp M) X).getD o 0).testBit j := by
  rw [eval_eq]
  refine (bp M j hM gs X _ (by simp) hop (fun i => ?_) o).symm
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases X[i]? <;> simp

theorem two (x : Fin 16 → Bool)
    (hc : (Finset.univ.filter (fun p : Fin 16 => x p = true)).card ≤ 2) :
    (∀ p, x p = false) ∨ ∃ a b, x a = true ∧ x b = true ∧ ∀ p, x p = true → p = a ∨ p = b := by
  by_cases h0 : ∀ p, x p = false
  · exact Or.inl h0
  · right
    have h0' : ∃ a, x a = true := by
      by_contra hn
      exact h0 (fun p => by
        cases hp : x p
        · rfl
        · exact absurd ⟨p, hp⟩ hn)
    obtain ⟨a, ha⟩ := h0'
    by_cases h1 : ∀ p, x p = true → p = a
    · exact ⟨a, a, ha, ha, fun p hp => Or.inl (h1 p hp)⟩
    · have h1' : ∃ b, x b = true ∧ b ≠ a := by
        by_contra hn
        exact h1 (fun p hp => by
          by_contra hpa
          exact hn ⟨p, hp, hpa⟩)
      obtain ⟨b, hb, hba⟩ := h1'
      refine ⟨a, b, ha, hb, fun p hp => ?_⟩
      by_contra hn
      have hpa : p ≠ a := fun h => hn (Or.inl h)
      have hpb : p ≠ b := fun h => hn (Or.inr h)
      have hsub : ({a, b, p} : Finset (Fin 16)) ⊆
          Finset.univ.filter (fun p : Fin 16 => x p = true) := by
        intro q hq
        simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rcases hq with rfl | rfl | rfl <;> assumption
      have h3 : ({a, b, p} : Finset (Fin 16)).card = 3 :=
        Finset.card_eq_three.mpr ⟨a, b, p, hba.symm, hpa.symm, hpb.symm, rfl⟩
      have := Finset.card_le_card hsub
      omega

theorem red (gs : List Gate) (o : ℕ) (hop : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (Ib : Fin 16 → Fin 16 → Bool)
    (hT : ∀ p l : Fin 16, Ib p l = true →
      Circuit.eval ⟨gs, o⟩ (List.ofFn (fun q : Fin 16 => decide (q = p)) ++
        List.ofFn (fun m : Fin 16 => decide (m = l))) = true)
    (hF0 : Circuit.eval ⟨gs, o⟩ (List.ofFn (fun _ : Fin 16 => false) ++
        List.ofFn (fun _ : Fin 16 => true)) = false)
    (hF2 : ∀ a b : Fin 16, Circuit.eval ⟨gs, o⟩
      (List.ofFn (fun q : Fin 16 => decide (q = a ∨ q = b)) ++
        List.ofFn (fun m : Fin 16 => !Ib a m && !Ib b m)) = false)
    (x y : Fin 16 → Bool)
    (hc : (Finset.univ.filter (fun p : Fin 16 => x p = true)).card ≤ 2) :
    (Circuit.eval ⟨gs, o⟩ (List.ofFn x ++ List.ofFn y) = true ↔
      ∃ p l : Fin 16, Ib p l = true ∧ x p = true ∧ y l = true) := by
  have mn : ∀ (x y x' y' : Fin 16 → Bool), (∀ p, x p = true → x' p = true) →
      (∀ l, y l = true → y' l = true) →
      Circuit.eval ⟨gs, o⟩ (List.ofFn x ++ List.ofFn y) = true →
      Circuit.eval ⟨gs, o⟩ (List.ofFn x' ++ List.ofFn y') = true := by
    intro x y x' y' h1 h2 h
    rw [← List.ofFn_fin_append] at h ⊢
    refine eval_mono_fn gs hop _ _ (fun v => ?_) o h
    refine Fin.addCases (fun i => ?_) (fun i => ?_) v
    · rw [Fin.append_left, Fin.append_left]; exact h1 i
    · rw [Fin.append_right, Fin.append_right]; exact h2 i
  constructor
  · intro h
    by_contra hne
    rcases two x hc with h0 | ⟨a, b, ha, hb, hab⟩
    · have h' := mn x y (fun _ => false) (fun _ => true)
        (fun p hp => by rw [h0 p] at hp; exact hp) (fun _ _ => rfl) h
      rw [hF0] at h'
      exact Bool.false_ne_true h'
    · have hy : ∀ l, y l = true → (!Ib a l && !Ib b l) = true := by
        intro l hl
        have h1 : Ib a l ≠ true := fun hI => hne ⟨a, l, hI, ha, hl⟩
        have h2 : Ib b l ≠ true := fun hI => hne ⟨b, l, hI, hb, hl⟩
        revert h1 h2
        cases Ib a l <;> cases Ib b l <;> simp
      have h' := mn x y (fun q => decide (q = a ∨ q = b)) (fun m => !Ib a m && !Ib b m)
        (fun p hp => decide_eq_true (hab p hp)) hy h
      rw [hF2] at h'
      exact Bool.false_ne_true h'
  · rintro ⟨p, l, hI, hp, hl⟩
    exact mn (fun q => decide (q = p)) (fun m => decide (m = l)) x y
      (fun q hq => by rw [of_decide_eq_true hq]; exact hp)
      (fun m hm => by rw [of_decide_eq_true hm]; exact hl) (hT p l hI)

def G0 : List Gate := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [32, 33] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [35, 36] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [9, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [38, 39] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [11, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [41, 42] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [44, 45] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [12, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [47, 48] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [9, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [50, 51] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [13, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [53, 54] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [56, 57] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [12, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [59, 60] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [62, 63] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [9, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [13, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [65, 66] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [68, 69] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [12, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [71, 72] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [74, 75] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [77, 78] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [80, 81] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [12, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [83, 84] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [86, 87] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [89, 90] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [92, 93] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [95, 96] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [98, 99] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [12, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [101, 102] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [34, 46] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [104, 58] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [105, 70] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [106, 82] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [107, 94] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [40, 52] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [109, 64] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [110, 70] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [111, 82] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [112, 94] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [37, 46] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [114, 58] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [115, 76] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [116, 88] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [117, 94] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [43, 52] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [119, 64] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [120, 76] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [121, 88] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [122, 94] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [34, 49] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [124, 58] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [125, 73] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [126, 82] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [127, 100] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [40, 55] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [129, 64] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [130, 73] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [131, 82] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [132, 100] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [37, 49] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [134, 58] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [135, 79] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [136, 88] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [137, 100] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [43, 55] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [139, 64] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [140, 79] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [141, 88] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [142, 100] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [34, 46] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [144, 61] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [145, 70] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [146, 85] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [147, 97] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [40, 52] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [149, 67] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [150, 70] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [151, 85] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [152, 97] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [37, 46] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [154, 61] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [155, 76] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [156, 91] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [157, 97] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [43, 52] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [159, 67] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [160, 76] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [161, 91] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [162, 97] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [34, 49] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [164, 61] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [165, 73] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [166, 85] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [167, 103] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [40, 55] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [169, 67] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [170, 73] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [171, 85] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [172, 103] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [37, 49] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [174, 61] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [175, 79] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [176, 91] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [177, 103] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [43, 55] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [179, 67] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [180, 79] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [181, 91] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [182, 103] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [108, 128] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [148, 168] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [184, 185] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [16, 186] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [113, 133] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [153, 173] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [188, 189] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [17, 190] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [118, 138] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [158, 178] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [192, 193] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [18, 194] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [123, 143] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [163, 183] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [196, 197] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [19, 198] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [108, 133] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [158, 183] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [200, 201] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [20, 202] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [113, 128] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [163, 178] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [204, 205] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [21, 206] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [118, 143] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [148, 173] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [208, 209] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [22, 210] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [123, 138] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [153, 168] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [212, 213] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [23, 214] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [108, 138] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [163, 173] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [216, 217] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [24, 218] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [113, 143] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [158, 168] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [220, 221] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [25, 222] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [118, 128] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [153, 183] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [224, 225] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [26, 226] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [123, 133] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [148, 178] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [228, 229] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [27, 230] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [108, 143] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [153, 178] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [232, 233] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [28, 234] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [113, 138] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [148, 183] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [236, 237] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [29, 238] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [118, 133] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [163, 168] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [240, 241] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [30, 242] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [123, 128] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [158, 173] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [244, 245] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [31, 246] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [187, 191] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [195, 199] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [203, 207] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [211, 215] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [219, 223] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [227, 231] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [235, 239] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [243, 247] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [248, 249] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [250, 251] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [252, 253] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [254, 255] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [256, 257] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [258, 259] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [260, 261] }]

def Ib (p l : Fin 16) : Bool := decide (((p : ℕ), (l : ℕ)) ∈ ([(0, 0), (4, 0), (8, 0), (12, 0), (1, 1), (5, 1), (9, 1), (13, 1), (2, 2), (6, 2), (10, 2), (14, 2), (3, 3), (7, 3), (11, 3), (15, 3), (0, 4), (5, 4), (10, 4), (15, 4), (1, 5), (4, 5), (11, 5), (14, 5), (2, 6), (7, 6), (8, 6), (13, 6), (3, 7), (6, 7), (9, 7), (12, 7), (0, 8), (6, 8), (11, 8), (13, 8), (1, 9), (7, 9), (10, 9), (12, 9), (2, 10), (4, 10), (9, 10), (15, 10), (3, 11), (5, 11), (8, 11), (14, 11), (0, 12), (7, 12), (9, 12), (14, 12), (1, 13), (6, 13), (8, 13), (15, 13), (2, 14), (5, 14), (11, 14), (12, 14), (3, 15), (4, 15), (10, 15), (13, 15)] : List (ℕ × ℕ)))

def M : ℕ := 2 ^ 513 - 1

def X : List ℕ := [15176869138101907759303882901839635580133665027048831909633479611441055553053392895, 994631295718856304550448210865288123282449768927539186687280137550018956598645173977090, 65184156596230735194373447365149543098970433676230637872614906175313511575528557589207187460, 4271908886690577461235296957069276220575429405016690674479158245735507965552311308535334399639560, 279963820798153684499515495055913180063159424093301062521847833728031510353778150712116712529239998480, 18347708959827799867360247482131681010806559073543790687876777994638144081065851549480354796462014021500960, 1202435454391274692107321178988978141433903030129878196945201412573332286238768685904810839258551707536233332800, 78802809938986578221945400786221671469601688351341069739661568792185738164695428341233270950435024631062055733952640, 5164420952161424390353413785925823461431801426632225845202909894062720096028387051183068844301056482005636971780200464640, 338455491520851108846201325874434766368394538266127230466215391715937820284435701892348765252604860311639739392283604542292480, 22181019092310498269344650092506956848719104459808854891188841906473498276952919649595760378045010665790867734461007597311063229440, 1453655267233660814579770988462535924037655229878033114030382653082637138672960028360670471978694629244381957986097612728781749744568320, 95266751593425195144299871499880754317731773145286778161094920413843507499982284710309114934344046933953447912051593467710351904376728064000, 6243401832426713588976836378616185114966869484849514293565516703767370947118797148156445796560093634215225204378581678219334295342284100188774400, 409167582489917101767185948908990307694468758559097768743109702698097473836056468965342491013995374318423486319301732999397264917345611251033881722880, 26815206686059207181414298347699588805064704560929031372348437476022516043422659160490215451557522307137586791605174979317474947646132441443078169356697600, 409180069579388024706615548888558667200102718260239364544855770007530755700279787409513207880610879873659566526854102493708182532988257431435961303040, 818360139158776049413231097777117334400205436520478729089711540015061511168975396321029862218946148158038998943914062708112786487971281433073991867869, 1636720278317552098826462195554234668800410873040957458179423080030123022106365318546080318169238633948988049799931067919934163815990823145608962620347, 3273440556635104197652924391108469337600821746081914916358846160060246043927113566171564670721955965250756275613500885701985836537794818876766560941943, 6546881113270208395305848782216938675201643492163829832717692320120492087738434248961506437975710200141918001241515466467882202913926495272577175257088, 13093762226540416790611697564433877350403286984327659665435384640240984175444266692924249344214211517213784100037462624010626172095095893216129198372845, 26187524453080833581223395128867754700806573968655319330870769280481968350706989618560477823106478713355831528927433264054485900830915566952462390386299, 52375048906161667162446790257735509401613147937310638661741538560963936701204445646526885424435355370294553911079540516385997412137305739019648652275127, 104750097812323334324893580515471018803226295874621277323483077121927873402175637418602664987796688837649754557624086052807516380753359252127314482167808, 209500195624646668649787161030942037606452591749242554646966154243855746804146829843802233439346256570940113125972626241979534905394162296681006020750205, 419000391249293337299574322061884075212905183498485109293932308487711493607964836466223593332965489206561068748506408807247504866429676873400597451865579, 838000782498586674599148644123768150425810366996970218587864616975422987215900198418445433069293369966492527235491285497998646272013223898618967606410967, 1676001564997173349198297288247536300851620733993940437175729233950845974431597675872046213419254501999900393116257660126770666251433910060392339388366848, 3352003129994346698396594576495072601703241467987880874351458467901691948862908141027319216391584485696005667120877975716083416960210331284066196825079485, 6704006259988693396793189152990145203406482935975761748702916935803383897725805361023705455412690485703257307854290256633425136964607746194260084406347739, 13408012519977386793586378305980290406812965871951523497405833871606767795451384650515871546433694210041415765423480022663854504590855495789899475730291687]

def E : ℕ := 3780804740084575427170986147131601227887623559335948356643771363510366018365604134140484184658482321366452962097285102768551277576695962221329579927142400

theorem hop0 : ∀ g ∈ G0, g.op = GateOp.and ∨ g.op = GateOp.or := by
  intro g hg
  have h : G0.all (fun g => isAO g.op) = true := by decide +kernel
  exact isAO_iff _ (List.all_eq_true.mp h g hg)

theorem hMj (j : ℕ) (hj : j < 513) : M.testBit j = true := by
  unfold M
  rw [Nat.testBit_two_pow_sub_one]
  exact decide_eq_true hj

theorem outE : (G0.foldl (bstp M) X).getD 262 0 = E := by decide +kernel

theorem rowsT : ∀ p l : Fin 16, (X.map fun n => n.testBit (257 + 16 * p.val + l.val)) =
    List.ofFn (fun q : Fin 16 => decide (q = p)) ++
      List.ofFn (fun m : Fin 16 => decide (m = l)) := by
  decide +kernel

theorem rowF0 : (X.map fun n => n.testBit 256) =
    List.ofFn (fun _ : Fin 16 => false) ++ List.ofFn (fun _ : Fin 16 => true) := by
  decide +kernel

theorem rowsF : ∀ a b : Fin 16, (X.map fun n => n.testBit (16 * a.val + b.val)) =
    List.ofFn (fun q : Fin 16 => decide (q = a ∨ q = b)) ++
      List.ofFn (fun m : Fin 16 => !Ib a m && !Ib b m) := by
  decide +kernel

theorem bitsT : ∀ p l : Fin 16, Ib p l = true →
    E.testBit (257 + 16 * p.val + l.val) = true := by
  decide +kernel

theorem bitF0 : E.testBit 256 = false := by decide +kernel

theorem bitsF : ∀ a b : Fin 16, E.testBit (16 * a.val + b.val) = false := by decide +kernel

theorem main (x y : Fin 16 → Bool)
    (hc : (Finset.univ.filter (fun p : Fin 16 => x p = true)).card ≤ 2) :
    (Circuit.eval ⟨G0, 262⟩ (List.ofFn x ++ List.ofFn y) = true ↔
      ∃ p l : Fin 16, Ib p l = true ∧ x p = true ∧ y l = true) := by
  refine red G0 262 hop0 Ib ?_ ?_ ?_ x y hc
  · intro p l hI
    have e := bp_eval M (257 + 16 * p.val + l.val) (hMj _ (by omega)) G0 hop0 X 262
    rw [rowsT p l, outE] at e
    rw [e]
    exact bitsT p l hI
  · have e := bp_eval M 256 (hMj _ (by omega)) G0 hop0 X 262
    rw [rowF0, outE] at e
    rw [e]
    exact bitF0
  · intro a b
    have e := bp_eval M (16 * a.val + b.val) (hMj _ (by omega)) G0 hop0 X 262
    rw [rowsF a b, outE] at e
    rw [e]
    exact bitsF a b

end PEqualNP.Outside.L_meta_1701

theorem PEqualNP.Outside.L_meta_1701 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [32, 33] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [35, 36] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [9, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [38, 39] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [11, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [41, 42] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [44, 45] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [12, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [47, 48] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [9, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [50, 51] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [13, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [53, 54] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [56, 57] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [12, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [59, 60] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [62, 63] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [9, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [13, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [65, 66] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [68, 69] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [12, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [71, 72] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [74, 75] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [77, 78] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [80, 81] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [12, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [83, 84] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [86, 87] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [89, 90] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [92, 93] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [95, 96] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [98, 99] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [12, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [101, 102] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [34, 46] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [104, 58] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [105, 70] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [106, 82] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [107, 94] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [40, 52] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [109, 64] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [110, 70] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [111, 82] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [112, 94] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [37, 46] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [114, 58] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [115, 76] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [116, 88] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [117, 94] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [43, 52] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [119, 64] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [120, 76] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [121, 88] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [122, 94] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [34, 49] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [124, 58] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [125, 73] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [126, 82] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [127, 100] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [40, 55] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [129, 64] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [130, 73] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [131, 82] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [132, 100] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [37, 49] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [134, 58] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [135, 79] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [136, 88] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [137, 100] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [43, 55] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [139, 64] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [140, 79] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [141, 88] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [142, 100] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [34, 46] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [144, 61] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [145, 70] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [146, 85] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [147, 97] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [40, 52] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [149, 67] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [150, 70] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [151, 85] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [152, 97] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [37, 46] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [154, 61] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [155, 76] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [156, 91] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [157, 97] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [43, 52] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [159, 67] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [160, 76] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [161, 91] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [162, 97] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [34, 49] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [164, 61] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [165, 73] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [166, 85] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [167, 103] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [40, 55] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [169, 67] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [170, 73] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [171, 85] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [172, 103] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [37, 49] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [174, 61] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [175, 79] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [176, 91] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [177, 103] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [43, 55] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [179, 67] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [180, 79] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [181, 91] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [182, 103] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [108, 128] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [148, 168] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [184, 185] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [16, 186] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [113, 133] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [153, 173] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [188, 189] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [17, 190] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [118, 138] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [158, 178] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [192, 193] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [18, 194] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [123, 143] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [163, 183] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [196, 197] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [19, 198] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [108, 133] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [158, 183] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [200, 201] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [20, 202] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [113, 128] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [163, 178] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [204, 205] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [21, 206] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [118, 143] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [148, 173] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [208, 209] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [22, 210] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [123, 138] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [153, 168] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [212, 213] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [23, 214] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [108, 138] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [163, 173] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [216, 217] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [24, 218] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [113, 143] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [158, 168] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [220, 221] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [25, 222] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [118, 128] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [153, 183] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [224, 225] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [26, 226] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [123, 133] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [148, 178] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [228, 229] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [27, 230] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [108, 143] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [153, 178] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [232, 233] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [28, 234] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [113, 138] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [148, 183] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [236, 237] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [29, 238] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [118, 133] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [163, 168] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [240, 241] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [30, 242] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [123, 128] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [158, 173] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [244, 245] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [31, 246] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [187, 191] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [195, 199] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [203, 207] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [211, 215] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [219, 223] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [227, 231] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [235, 239] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [243, 247] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [248, 249] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [250, 251] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [252, 253] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [254, 255] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [256, 257] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [258, 259] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [260, 261] }], output := 262 } : PEqualNP.CircuitLowerBounds.Circuit) →
  C.gates.length = 231 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (16 + 16) C ∧ ∀ (x y : Fin 16 → Bool), (Finset.univ.filter (fun p : Fin 16 => x p = true)).card ≤ 2 →
    C.eval (List.ofFn x ++ List.ofFn y) = decide (∃ p : Fin 16, ∃ l : Fin 16, ((p : ℕ), (l : ℕ)) ∈ ([(0, 0), (4, 0), (8, 0), (12, 0), (1, 1), (5, 1), (9, 1), (13, 1), (2, 2), (6, 2), (10, 2), (14, 2), (3, 3), (7, 3), (11, 3), (15, 3), (0, 4), (5, 4), (10, 4), (15, 4), (1, 5), (4, 5), (11, 5), (14, 5), (2, 6), (7, 6), (8, 6), (13, 6), (3, 7), (6, 7), (9, 7), (12, 7), (0, 8), (6, 8), (11, 8), (13, 8), (1, 9), (7, 9), (10, 9), (12, 9), (2, 10), (4, 10), (9, 10), (15, 10), (3, 11), (5, 11), (8, 11), (14, 11), (0, 12), (7, 12), (9, 12), (14, 12), (1, 13), (6, 13), (8, 13), (15, 13), (2, 14), (5, 14), (11, 14), (12, 14), (3, 15), (4, 15), (10, 15), (13, 15)] : List (ℕ × ℕ)) ∧ x p = true ∧ y l = true) := by
  intro C hC
  subst hC
  refine ⟨rfl, ?_, ?_⟩
  · decide +kernel
  · intro x y hc
    rw [Bool.eq_iff_iff, decide_eq_true_eq]
    refine (PEqualNP.Outside.L_meta_1701.main x y hc).trans ?_
    simp only [PEqualNP.Outside.L_meta_1701.Ib, decide_eq_true_eq]
