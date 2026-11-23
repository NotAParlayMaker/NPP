import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_950

open PEqualNP.AndCount

def slot : Fin 6 → Fin 6 → Nat :=
  ![![15,0,1,2,3,4], ![0,15,5,6,7,8], ![1,5,15,9,10,11],
    ![2,6,9,15,12,13], ![3,7,10,12,15,14], ![4,8,11,13,14,15]]

abbrev Adjacent (g : Nat) (a b : Fin 6) : Prop :=
  g.testBit (slot a b) = true ∧ a ≠ b

def Fits (g : Nat) (C : AndCountCircuit 6) : Prop :=
  ∀ I : Finset (Fin 6), (∀ v ∈ I, ∀ w ∈ I, ¬ Adjacent g v w) →
    (∀ u, u ∉ I → ∃ v ∈ I, Adjacent g u v) →
    C.eval I = false ∧ ∀ u, u ∉ I → C.eval (insert u I) = true

def Cover (g k : Nat) : Prop :=
  ∃ X Y : Fin k → Finset (Fin 6),
    (∀ i : Fin k, ∀ a ∈ X i, ∀ b ∈ Y i, Adjacent g a b) ∧
    (∀ a b : Fin 6, Adjacent g a b → ∃ i : Fin k,
      (a ∈ X i ∧ b ∈ Y i) ∨ (b ∈ X i ∧ a ∈ Y i))

def Solves (g : Nat) : Prop :=
  ∀ C : AndCountCircuit 6, C.WellFormed → Fits g C → ∃ k, k ≤ C.size ∧ Cover g k

def Relabel (G : SimpleGraph (Fin 6)) (e : Equiv.Perm (Fin 6)) (g : Nat) : Prop :=
  ∀ a b, Adjacent g a b ↔ G.Adj (e a) (e b)

open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit

theorem sideTrue_congr {n k : ℕ} (U B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
    (v w : Fin k → Bool) (h : ∀ j, j < i → v j = w j) :
    sideTrue U B F i v = sideTrue U B F i w := by
  unfold sideTrue
  congr 1
  apply propext
  constructor
  · rintro (h1 | ⟨j, hj, hji, hv⟩)
    · exact Or.inl h1
    · exact Or.inr ⟨j, hj, hji, by rw [← h j hji]; exact hv⟩
  · rintro (h1 | ⟨j, hj, hji, hv⟩)
    · exact Or.inl h1
    · exact Or.inr ⟨j, hj, hji, by rw [h j hji]; exact hv⟩

theorem sideTrue_iff {n k : ℕ} (U B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
    (v : Fin k → Bool) :
    sideTrue U B F i v = true ↔ ((∃ x ∈ B, x ∈ U) ∨ ∃ j ∈ F, j < i ∧ v j = true) := by
  unfold sideTrue
  exact decide_eq_true_iff

theorem fuel_succ {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    ∀ d : ℕ, ∀ i : Fin C.size, i.val < d →
      gateValFuel C U (d + 1) i = gateValFuel C U d i := by
  intro d
  induction d with
  | zero => intro i hi; exact absurd hi (Nat.not_lt_zero _)
  | succ d ih =>
    intro i hi
    show (sideTrue U (C.leftVars i) (C.leftGates i) i (gateValFuel C U (d + 1)) &&
        sideTrue U (C.rightVars i) (C.rightGates i) i (gateValFuel C U (d + 1))) =
      (sideTrue U (C.leftVars i) (C.leftGates i) i (gateValFuel C U d) &&
        sideTrue U (C.rightVars i) (C.rightGates i) i (gateValFuel C U d))
    have hc : ∀ j : Fin C.size, j < i → gateValFuel C U (d + 1) j = gateValFuel C U d j := by
      intro j hji
      apply ih
      have : j.val < i.val := hji
      omega
    rw [sideTrue_congr U (C.leftVars i) (C.leftGates i) i _ _ hc,
      sideTrue_congr U (C.rightVars i) (C.rightGates i) i _ _ hc]

theorem gateVal_rec {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) (i : Fin C.size) :
    C.gateVal U i = (sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateVal U) &&
      sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateVal U)) := by
  have h := fuel_succ C U C.size i i.isLt
  exact h.symm

theorem eval_iff {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    C.eval U = true ↔
      ((∃ v ∈ C.outVars, v ∈ U) ∨ ∃ j ∈ C.outGates, C.gateVal U j = true) := by
  unfold AndCountCircuit.eval
  exact decide_eq_true_iff

def sideVars {n : ℕ} (C : AndCountCircuit n) (o : Fin C.size → Bool) (i : Fin C.size) :=
  cond (o i) (C.rightVars i) (C.leftVars i)

def sideGates {n : ℕ} (C : AndCountCircuit n) (o : Fin C.size → Bool) (i : Fin C.size) :=
  cond (o i) (C.rightGates i) (C.leftGates i)

def excFuel {n : ℕ} (C : AndCountCircuit n) (o : Fin C.size → Bool) (v : Fin n) :
    ℕ → Fin C.size → Bool
  | 0, _ => false
  | d + 1, i => decide (v ∈ sideVars C o i ∨
      ∃ j ∈ sideGates C o i, j < i ∧ excFuel C o v d j = true)

def excluded {n : ℕ} (C : AndCountCircuit n) (o : Fin C.size → Bool) (v : Fin n) : Bool :=
  decide (v ∈ C.outVars ∨ ∃ j ∈ C.outGates, excFuel C o v C.size j = true)

def orientAt {n : ℕ} (C : AndCountCircuit n) (I : Finset (Fin n)) (i : Fin C.size) : Bool :=
  sideTrue I (C.leftVars i) (C.leftGates i) i (C.gateVal I)

theorem orientAt_val {n : ℕ} (C : AndCountCircuit n) (I : Finset (Fin n)) (i : Fin C.size) :
    sideTrue I (sideVars C (orientAt C I) i) (sideGates C (orientAt C I) i) i (C.gateVal I) =
      C.gateVal I i := by
  rw [gateVal_rec C I i]
  cases h : sideTrue I (C.leftVars i) (C.leftGates i) i (C.gateVal I) <;>
    simp [orientAt, sideVars, sideGates, h]

theorem excFuel_at {n : ℕ} (C : AndCountCircuit n) (I : Finset (Fin n)) (v : Fin n)
    (hv : v ∈ I) (d : ℕ) (i : Fin C.size) :
    excFuel C (orientAt C I) v d i = true → C.gateVal I i = true := by
  induction d generalizing i with
  | zero => simp [excFuel]
  | succ d ih =>
    intro he
    rw [excFuel, decide_eq_true_eq] at he
    rw [← orientAt_val, sideTrue_iff]
    rcases he with bare | ⟨j, hj, hji, h⟩
    · exact Or.inl ⟨v, bare, hv⟩
    · exact Or.inr ⟨j, hj, hji, ih j h⟩

theorem gate_selects {n : ℕ} (C : AndCountCircuit n) (o : Fin C.size → Bool)
    (U : Finset (Fin n)) (d : ℕ) (i : Fin C.size) :
    C.gateValFuel U d i = true → ∃ v ∈ U, excFuel C o v d i = true := by
  induction d generalizing i with
  | zero => simp [gateValFuel]
  | succ d ih =>
    intro hg
    change (_ && _) = true at hg
    rw [Bool.and_eq_true] at hg
    have hs : sideTrue U (sideVars C o i) (sideGates C o i) i (C.gateValFuel U d) = true := by
      cases h : o i
      · simpa [sideVars, sideGates, h] using hg.1
      · simpa [sideVars, sideGates, h] using hg.2
    rw [sideTrue_iff] at hs
    rcases hs with ⟨v, hb, hu⟩ | ⟨j, hj, hji, h⟩
    · exact ⟨v, hu, (decide_eq_true_iff).2 (Or.inl hb)⟩
    · obtain ⟨v, hu, hv⟩ := ih j h
      exact ⟨v, hu, (decide_eq_true_iff).2 (Or.inr ⟨j, hj, hji, hv⟩)⟩

theorem eval_selects {n : ℕ} (C : AndCountCircuit n) (o : Fin C.size → Bool)
    (U : Finset (Fin n)) (h : C.eval U = true) : ∃ v ∈ U, excluded C o v = true := by
  rw [eval_iff] at h
  rcases h with ⟨v, hb, hu⟩ | ⟨j, hj, h⟩
  · exact ⟨v, hu, (decide_eq_true_iff).2 (Or.inl hb)⟩
  · obtain ⟨v, hu, hv⟩ := gate_selects C o U C.size j h
    exact ⟨v, hu, (decide_eq_true_iff).2 (Or.inr ⟨j, hj, hv⟩)⟩

theorem orientCert {n : ℕ} (C : AndCountCircuit n) (I : Finset (Fin n))
    (neg : C.eval I = false) (pos : ∀ v, v ∉ I → C.eval (insert v I) = true) :
    ∃ o : Fin C.size → Bool, ∀ v : Fin n, excluded C o v = decide (v ∉ I) := by
  have notHit : ∀ v ∈ I, excluded C (orientAt C I) v ≠ true := by
    intro v hv he
    rw [excluded, decide_eq_true_eq] at he
    have hg : C.eval I = true := (eval_iff C I).2 (by
      rcases he with hb | ⟨j, hj, h⟩
      · exact Or.inl ⟨v, hb, hv⟩
      · exact Or.inr ⟨j, hj, excFuel_at C I v hv C.size j h⟩)
    rw [neg] at hg
    contradiction
  refine ⟨orientAt C I, fun v => ?_⟩
  by_cases hv : v ∈ I
  · simpa [hv] using notHit v hv
  · obtain ⟨w, hw, h⟩ := eval_selects C (orientAt C I) (insert v I) (pos v hv)
    rcases Finset.mem_insert.mp hw with rfl | hw
    · simpa [hv] using h
    · exact (notHit w hw h).elim

open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit

-- The generic counting argument is adapted from the checked L-meta-906.
theorem rowCount_sideTrue_congr {n k : ℕ} (U B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
    (v w : Fin k → Bool) (h : ∀ j, j < i → v j = w j) :
    sideTrue U B F i v = sideTrue U B F i w := by
  unfold sideTrue
  congr 1
  apply propext
  constructor
  · rintro (h1 | ⟨j, hj, hji, hv⟩)
    · exact Or.inl h1
    · exact Or.inr ⟨j, hj, hji, by rw [← h j hji]; exact hv⟩
  · rintro (h1 | ⟨j, hj, hji, hv⟩)
    · exact Or.inl h1
    · exact Or.inr ⟨j, hj, hji, by rw [h j hji]; exact hv⟩

theorem rowCount_sideTrue_iff {n k : ℕ} (U B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
    (v : Fin k → Bool) :
    sideTrue U B F i v = true ↔ ((∃ x ∈ B, x ∈ U) ∨ ∃ j ∈ F, j < i ∧ v j = true) := by
  unfold sideTrue
  exact decide_eq_true_iff

theorem rowCount_sideTrue_mono {n k : ℕ} (U U' B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
    (v w : Fin k → Bool) (hU : U ⊆ U') (h : ∀ j, j < i → v j = true → w j = true)
    (hs : sideTrue U B F i v = true) : sideTrue U' B F i w = true := by
  rw [rowCount_sideTrue_iff] at hs ⊢
  rcases hs with ⟨x, hx, hxU⟩ | ⟨j, hj, hji, hv⟩
  · exact Or.inl ⟨x, hx, hU hxU⟩
  · exact Or.inr ⟨j, hj, hji, h j hji hv⟩

theorem rowCount_fuel_succ {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    ∀ d : ℕ, ∀ i : Fin C.size, i.val < d →
      gateValFuel C U (d + 1) i = gateValFuel C U d i := by
  intro d
  induction d with
  | zero => intro i hi; exact absurd hi (Nat.not_lt_zero _)
  | succ d ih =>
    intro i hi
    show (sideTrue U (C.leftVars i) (C.leftGates i) i (gateValFuel C U (d + 1)) &&
        sideTrue U (C.rightVars i) (C.rightGates i) i (gateValFuel C U (d + 1))) =
      (sideTrue U (C.leftVars i) (C.leftGates i) i (gateValFuel C U d) &&
        sideTrue U (C.rightVars i) (C.rightGates i) i (gateValFuel C U d))
    have hc : ∀ j : Fin C.size, j < i → gateValFuel C U (d + 1) j = gateValFuel C U d j := by
      intro j hji
      apply ih
      have : j.val < i.val := hji
      omega
    rw [rowCount_sideTrue_congr U (C.leftVars i) (C.leftGates i) i _ _ hc,
      rowCount_sideTrue_congr U (C.rightVars i) (C.rightGates i) i _ _ hc]

theorem rowCount_gateVal_rec {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) (i : Fin C.size) :
    C.gateVal U i = (sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateVal U) &&
      sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateVal U)) := by
  have h := rowCount_fuel_succ C U C.size i i.isLt
  exact h.symm

theorem rowCount_gateVal_iff {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) (i : Fin C.size) :
    C.gateVal U i = true ↔
      (((∃ x ∈ C.leftVars i, x ∈ U) ∨ ∃ j ∈ C.leftGates i, j < i ∧ C.gateVal U j = true) ∧
       ((∃ x ∈ C.rightVars i, x ∈ U) ∨ ∃ j ∈ C.rightGates i, j < i ∧ C.gateVal U j = true)) := by
  rw [rowCount_gateVal_rec, Bool.and_eq_true, rowCount_sideTrue_iff, rowCount_sideTrue_iff]

theorem rowCount_eval_iff {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    C.eval U = true ↔
      ((∃ v ∈ C.outVars, v ∈ U) ∨ ∃ j ∈ C.outGates, C.gateVal U j = true) := by
  unfold AndCountCircuit.eval
  exact decide_eq_true_iff

theorem rowCount_fuel_mono {n : ℕ} (C : AndCountCircuit n) (U U' : Finset (Fin n)) (hU : U ⊆ U') :
    ∀ d : ℕ, ∀ i : Fin C.size, gateValFuel C U d i = true → gateValFuel C U' d i = true := by
  intro d
  induction d with
  | zero => intro i h; exact absurd h (by simp [gateValFuel])
  | succ d ih =>
    intro i h
    have h' : (sideTrue U (C.leftVars i) (C.leftGates i) i (gateValFuel C U d) &&
        sideTrue U (C.rightVars i) (C.rightGates i) i (gateValFuel C U d)) = true := h
    show (sideTrue U' (C.leftVars i) (C.leftGates i) i (gateValFuel C U' d) &&
        sideTrue U' (C.rightVars i) (C.rightGates i) i (gateValFuel C U' d)) = true
    rw [Bool.and_eq_true] at h' ⊢
    exact ⟨rowCount_sideTrue_mono U U' _ _ i _ _ hU (fun j _ => ih j) h'.1,
      rowCount_sideTrue_mono U U' _ _ i _ _ hU (fun j _ => ih j) h'.2⟩

theorem rowCount_gateVal_mono {n : ℕ} (C : AndCountCircuit n) (U U' : Finset (Fin n)) (hU : U ⊆ U')
    (i : Fin C.size) (h : C.gateVal U i = true) : C.gateVal U' i = true :=
  rowCount_fuel_mono C U U' hU C.size i h

theorem rowCount_eval_mono {n : ℕ} (C : AndCountCircuit n) (U U' : Finset (Fin n)) (hU : U ⊆ U')
    (h : C.eval U = true) : C.eval U' = true := by
  rw [rowCount_eval_iff] at h ⊢
  rcases h with ⟨v, hv, hvU⟩ | ⟨j, hj, hg⟩
  · exact Or.inl ⟨v, hv, hU hvU⟩
  · exact Or.inr ⟨j, hj, rowCount_gateVal_mono C U U' hU j hg⟩

def rowCount_sv {n : ℕ} (C : AndCountCircuit n) (X : Finset (Fin n)) (i : Fin C.size) (s : Bool) : Bool :=
  sideTrue X (cond s (C.rightVars i) (C.leftVars i)) (cond s (C.rightGates i) (C.leftGates i)) i
    (C.gateVal X)

theorem rowCount_gate_false_iff {n : ℕ} (C : AndCountCircuit n) (X : Finset (Fin n)) (i : Fin C.size) :
    C.gateVal X i = false ↔ (rowCount_sv C X i false = false ∨ rowCount_sv C X i true = false) := by
  rw [rowCount_gateVal_rec, Bool.and_eq_false_iff]
  rfl

theorem rowCount_sv_hit {n : ℕ} (C : AndCountCircuit n) (U X : Finset (Fin n)) (hU : U ⊆ X)
    (i : Fin C.size) (s : Bool)
    (h : ¬ Disjoint (cond s (C.rightVars i) (C.leftVars i)) U) : rowCount_sv C X i s = true := by
  rw [Finset.not_disjoint_iff] at h
  obtain ⟨x, hx, hxU⟩ := h
  exact (rowCount_sideTrue_iff _ _ _ _ _).2 (Or.inl ⟨x, hx, hU hxU⟩)

theorem rowCount_sv_merge {n : ℕ} (C : AndCountCircuit n) (X Y : Finset (Fin n)) (i : Fin C.size)
    (s : Bool) (hX : rowCount_sv C X i s = false) (hY : rowCount_sv C Y i s = false)
    (ih : ∀ j : Fin C.size, j < i → C.gateVal X j = false → C.gateVal Y j = false →
      C.gateVal (X ∪ Y) j = false) : rowCount_sv C (X ∪ Y) i s = false := by
  rw [← Bool.not_eq_true] at hX hY ⊢
  unfold rowCount_sv at hX hY ⊢
  rw [rowCount_sideTrue_iff] at hX hY ⊢
  rintro (⟨x, hx, hxU⟩ | ⟨j, hj, hji, hv⟩)
  · rcases Finset.mem_union.1 hxU with h | h
    · exact hX (Or.inl ⟨x, hx, h⟩)
    · exact hY (Or.inl ⟨x, hx, h⟩)
  · have h1 : C.gateVal X j = false := by
      rw [← Bool.not_eq_true]
      exact fun hh => hX (Or.inr ⟨j, hj, hji, hh⟩)
    have h2 : C.gateVal Y j = false := by
      rw [← Bool.not_eq_true]
      exact fun hh => hY (Or.inr ⟨j, hj, hji, hh⟩)
    rw [ih j hji h1 h2] at hv
    exact Bool.noConfusion hv

def rowCount_code {n : ℕ} (C : AndCountCircuit n) (U X : Finset (Fin n)) (i : Fin C.size) : Bool :=
  if ¬ Disjoint (C.leftVars i) U then true
  else if ¬ Disjoint (C.rightVars i) U then false
  else rowCount_sv C X i false

theorem rowCount_code_ok {n : ℕ} (C : AndCountCircuit n) (U X : Finset (Fin n)) (hU : U ⊆ X)
    (i : Fin C.size) (h : C.gateVal X i = false) : rowCount_sv C X i (rowCount_code C U X i) = false := by
  rw [rowCount_gate_false_iff] at h
  unfold rowCount_code
  by_cases hl : ¬ Disjoint (C.leftVars i) U
  · rw [ite_eq_left hl]
    have := rowCount_sv_hit C U X hU i false hl
    rcases h with h | h
    · rw [this] at h; exact Bool.noConfusion h
    · exact h
  · rw [ite_eq_right hl]
    by_cases hr : ¬ Disjoint (C.rightVars i) U
    · rw [ite_eq_left hr]
      have := rowCount_sv_hit C U X hU i true hr
      rcases h with h | h
      · exact h
      · rw [this] at h; exact Bool.noConfusion h
    · rw [ite_eq_right hr]
      cases hb : rowCount_sv C X i false with
      | false => exact hb
      | true =>
        rcases h with h | h
        · rw [hb] at h; exact Bool.noConfusion h
        · exact h

theorem rowCount_code_hit {n : ℕ} (C : AndCountCircuit n) (U X Y : Finset (Fin n)) (i : Fin C.size)
    (h : ¬ Disjoint (C.leftVars i ∪ C.rightVars i) U) : rowCount_code C U X i = rowCount_code C U Y i := by
  unfold rowCount_code
  by_cases hl : ¬ Disjoint (C.leftVars i) U
  · rw [ite_eq_left hl, ite_eq_left hl]
  · rw [ite_eq_right hl, ite_eq_right hl]
    by_cases hr : ¬ Disjoint (C.rightVars i) U
    · rw [ite_eq_left hr, ite_eq_left hr]
    · exfalso
      apply h
      rw [Finset.disjoint_union_left]
      exact ⟨not_not.1 hl, not_not.1 hr⟩

theorem rowCount_merge_gate {n : ℕ} (C : AndCountCircuit n) (U X Y : Finset (Fin n)) (hX : U ⊆ X)
    (hY : U ⊆ Y) (hc : ∀ i, rowCount_code C U X i = rowCount_code C U Y i) :
    ∀ i : Fin C.size, C.gateVal X i = false → C.gateVal Y i = false →
      C.gateVal (X ∪ Y) i = false := by
  have key : ∀ m : ℕ, ∀ i : Fin C.size, i.val < m → C.gateVal X i = false →
      C.gateVal Y i = false → C.gateVal (X ∪ Y) i = false := by
    intro m
    induction m with
    | zero => intro i hi; exact absurd hi (Nat.not_lt_zero _)
    | succ m ih =>
      intro i hi h1 h2
      have ih' : ∀ j : Fin C.size, j < i → C.gateVal X j = false → C.gateVal Y j = false →
          C.gateVal (X ∪ Y) j = false := by
        intro j hji
        apply ih
        have : j.val < i.val := hji
        omega
      have c1 := rowCount_code_ok C U X hX i h1
      have c2 := rowCount_code_ok C U Y hY i h2
      rw [← hc i] at c2
      have hm := rowCount_sv_merge C X Y i _ c1 c2 ih'
      rw [rowCount_gate_false_iff]
      cases hb : rowCount_code C U X i with
      | false => rw [hb] at hm; exact Or.inl hm
      | true => rw [hb] at hm; exact Or.inr hm
  intro i
  exact key (i.val + 1) i (Nat.lt_succ_self _)

theorem rowCount_merge_eval {n : ℕ} (C : AndCountCircuit n) (U X Y : Finset (Fin n)) (hX : U ⊆ X)
    (hY : U ⊆ Y) (hc : ∀ i, rowCount_code C U X i = rowCount_code C U Y i)
    (h1 : C.eval X = false) (h2 : C.eval Y = false) : C.eval (X ∪ Y) = false := by
  rw [← Bool.not_eq_true, rowCount_eval_iff] at h1 h2 ⊢
  rintro (⟨x, hx, hxU⟩ | ⟨j, hj, hv⟩)
  · rcases Finset.mem_union.1 hxU with h | h
    · exact h1 (Or.inl ⟨x, hx, h⟩)
    · exact h2 (Or.inl ⟨x, hx, h⟩)
  · have g1 : C.gateVal X j = false := by
      rw [← Bool.not_eq_true]
      exact fun hh => h1 (Or.inr ⟨j, hj, hh⟩)
    have g2 : C.gateVal Y j = false := by
      rw [← Bool.not_eq_true]
      exact fun hh => h2 (Or.inr ⟨j, hj, hh⟩)
    rw [rowCount_merge_gate C U X Y hX hY hc j g1 g2] at hv
    exact Bool.noConfusion hv

theorem rowCount_proj_count {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) (m : ℕ)
    (M : Fin m → Finset (Fin n)) (hU : ∀ a, U ⊆ M a) (h0 : ∀ a, C.eval (M a) = false)
    (h1 : ∀ a b, a ≠ b → C.eval (M a ∪ M b) = true) :
    m ≤ 2 ^ (Finset.univ.filter
      (fun i : Fin C.size => Disjoint (C.leftVars i ∪ C.rightVars i) U)).card := by
  let f : Fin m → ({i : Fin C.size // Disjoint (C.leftVars i ∪ C.rightVars i) U} → Bool) :=
    fun a i => rowCount_code C U (M a) i.1
  have hf : Function.Injective f := by
    intro a b hab
    by_contra hne
    have hc : ∀ i, rowCount_code C U (M a) i = rowCount_code C U (M b) i := by
      intro i
      by_cases hi : Disjoint (C.leftVars i ∪ C.rightVars i) U
      · exact congrFun hab ⟨i, hi⟩
      · exact rowCount_code_hit C U _ _ i hi
    have := rowCount_merge_eval C U (M a) (M b) (hU a) (hU b) hc (h0 a) (h0 b)
    rw [h1 a b hne] at this
    exact Bool.noConfusion this
  have hcard := Fintype.card_le_of_injective f hf
  rw [Fintype.card_fin, Fintype.card_fun, Fintype.card_bool, Fintype.card_subtype] at hcard
  exact hcard



theorem rowCount_familyBound {n m} (C : AndCountCircuit n) (M : Fin m → Finset (Fin n))
    (apart : ∀ i j, i ≠ j → ∃ v ∈ M j, v ∉ M i)
    (h : ∀ i, C.eval (M i) = false ∧ ∀ v, v ∉ M i → C.eval (insert v (M i)) = true) :
    m ≤ 2^C.size := by
  have a := rowCount_proj_count C ∅ m M (by simp) (fun i => (h i).1) (by
    intro i j ne
    obtain ⟨v,hv,hn⟩ := apart i j ne
    exact rowCount_eval_mono C (insert v (M i)) (M i ∪ M j)
      (Finset.insert_subset (Finset.mem_union_right _ hv) Finset.subset_union_left) ((h i).2 v hn))
  simpa using a

theorem lowerFromRows {g m k : Nat} (C : AndCountCircuit 6) (fit : Fits g C)
    (M : Fin m → Finset (Fin 6)) (enough : 2 ^ k < m)
    (apart : ∀ i j, i ≠ j → ∃ v ∈ M j, v ∉ M i)
    (good : ∀ i, (∀ v ∈ M i, ∀ w ∈ M i, ¬ Adjacent g v w) ∧
      (∀ u, u ∉ M i → ∃ v ∈ M i, Adjacent g u v)) : k + 1 ≤ C.size := by
  have h := rowCount_familyBound C M apart (fun i => fit (M i) (good i).1 (good i).2)
  by_contra! small
  have le : C.size ≤ k := by omega
  exact (Nat.not_lt_of_ge (h.trans (Nat.pow_le_pow_right (by decide : 0 < 2) le))) enough

theorem easy_0 (C : AndCountCircuit 6) (_ : Fits 0 C) : 0 ≤ C.size := Nat.zero_le _

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_1 (C : AndCountCircuit 6) (fit : Fits 1 C) : 1 ≤ C.size := by
  apply lowerFromRows (k := 0) C fit (![{0, 2, 3, 4, 5}, {1, 2, 3, 4, 5}] : Fin 2 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_3 (C : AndCountCircuit 6) (fit : Fits 3 C) : 1 ≤ C.size := by
  apply lowerFromRows (k := 0) C fit (![{0, 3, 4, 5}, {1, 2, 3, 4, 5}] : Fin 2 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_7 (C : AndCountCircuit 6) (fit : Fits 7 C) : 1 ≤ C.size := by
  apply lowerFromRows (k := 0) C fit (![{0, 4, 5}, {1, 2, 3, 4, 5}] : Fin 2 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_15 (C : AndCountCircuit 6) (fit : Fits 15 C) : 1 ≤ C.size := by
  apply lowerFromRows (k := 0) C fit (![{0, 5}, {1, 2, 3, 4, 5}] : Fin 2 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_31 (C : AndCountCircuit 6) (fit : Fits 31 C) : 1 ≤ C.size := by
  apply lowerFromRows (k := 0) C fit (![{0}, {1, 2, 3, 4, 5}] : Fin 2 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_35 (C : AndCountCircuit 6) (fit : Fits 35 C) : 2 ≤ C.size := by
  apply lowerFromRows (k := 1) C fit (![{0, 3, 4, 5}, {1, 3, 4, 5}, {2, 3, 4, 5}] : Fin 3 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_36 (C : AndCountCircuit 6) (fit : Fits 36 C) : 2 ≤ C.size := by
  apply lowerFromRows (k := 1) C fit (![{0, 1, 4, 5}, {0, 2, 4, 5}, {1, 3, 4, 5}] : Fin 3 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_37 (C : AndCountCircuit 6) (fit : Fits 37 C) : 2 ≤ C.size := by
  apply lowerFromRows (k := 1) C fit (![{0, 2, 4, 5}, {1, 3, 4, 5}, {2, 3, 4, 5}] : Fin 3 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_39 (C : AndCountCircuit 6) (fit : Fits 39 C) : 2 ≤ C.size := by
  apply lowerFromRows (k := 1) C fit (![{0, 4, 5}, {1, 3, 4, 5}, {2, 3, 4, 5}] : Fin 3 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_44 (C : AndCountCircuit 6) (fit : Fits 44 C) : 2 ≤ C.size := by
  apply lowerFromRows (k := 1) C fit (![{0, 1, 5}, {0, 2, 5}, {1, 3, 4, 5}] : Fin 3 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_45 (C : AndCountCircuit 6) (fit : Fits 45 C) : 2 ≤ C.size := by
  apply lowerFromRows (k := 1) C fit (![{0, 2, 5}, {1, 3, 4, 5}, {2, 3, 4, 5}] : Fin 3 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_47 (C : AndCountCircuit 6) (fit : Fits 47 C) : 2 ≤ C.size := by
  apply lowerFromRows (k := 1) C fit (![{0, 5}, {1, 3, 4, 5}, {2, 3, 4, 5}] : Fin 3 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_60 (C : AndCountCircuit 6) (fit : Fits 60 C) : 2 ≤ C.size := by
  apply lowerFromRows (k := 1) C fit (![{0, 1}, {0, 2}, {1, 3, 4, 5}] : Fin 3 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_61 (C : AndCountCircuit 6) (fit : Fits 61 C) : 2 ≤ C.size := by
  apply lowerFromRows (k := 1) C fit (![{0, 2}, {1, 3, 4, 5}, {2, 3, 4, 5}] : Fin 3 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_63 (C : AndCountCircuit 6) (fit : Fits 63 C) : 2 ≤ C.size := by
  apply lowerFromRows (k := 1) C fit (![{0}, {1, 3, 4, 5}, {2, 3, 4, 5}] : Fin 3 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_102 (C : AndCountCircuit 6) (fit : Fits 102 C) : 1 ≤ C.size := by
  apply lowerFromRows (k := 0) C fit (![{0, 1, 4, 5}, {2, 3, 4, 5}] : Fin 2 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_103 (C : AndCountCircuit 6) (fit : Fits 103 C) : 2 ≤ C.size := by
  apply lowerFromRows (k := 1) C fit (![{0, 4, 5}, {1, 4, 5}, {2, 3, 4, 5}] : Fin 3 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_106 (C : AndCountCircuit 6) (fit : Fits 106 C) : 2 ≤ C.size := by
  apply lowerFromRows (k := 1) C fit (![{0, 1, 5}, {0, 3, 5}, {1, 4, 5}] : Fin 3 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_107 (C : AndCountCircuit 6) (fit : Fits 107 C) : 2 ≤ C.size := by
  apply lowerFromRows (k := 1) C fit (![{0, 3, 5}, {1, 4, 5}, {2, 3, 4, 5}] : Fin 3 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_110 (C : AndCountCircuit 6) (fit : Fits 110 C) : 2 ≤ C.size := by
  apply lowerFromRows (k := 1) C fit (![{0, 1, 5}, {1, 4, 5}, {2, 3, 4, 5}] : Fin 3 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_111 (C : AndCountCircuit 6) (fit : Fits 111 C) : 2 ≤ C.size := by
  apply lowerFromRows (k := 1) C fit (![{0, 5}, {1, 4, 5}, {2, 3, 4, 5}] : Fin 3 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_120 (C : AndCountCircuit 6) (fit : Fits 120 C) : 2 ≤ C.size := by
  apply lowerFromRows (k := 1) C fit (![{0, 1}, {0, 2, 3}, {1, 4, 5}] : Fin 3 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_121 (C : AndCountCircuit 6) (fit : Fits 121 C) : 2 ≤ C.size := by
  apply lowerFromRows (k := 1) C fit (![{0, 2, 3}, {1, 4, 5}, {2, 3, 4, 5}] : Fin 3 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_122 (C : AndCountCircuit 6) (fit : Fits 122 C) : 2 ≤ C.size := by
  apply lowerFromRows (k := 1) C fit (![{0, 1}, {0, 3}, {1, 4, 5}] : Fin 3 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_123 (C : AndCountCircuit 6) (fit : Fits 123 C) : 2 ≤ C.size := by
  apply lowerFromRows (k := 1) C fit (![{0, 3}, {1, 4, 5}, {2, 3, 4, 5}] : Fin 3 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_126 (C : AndCountCircuit 6) (fit : Fits 126 C) : 2 ≤ C.size := by
  apply lowerFromRows (k := 1) C fit (![{0, 1}, {1, 4, 5}, {2, 3, 4, 5}] : Fin 3 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_127 (C : AndCountCircuit 6) (fit : Fits 127 C) : 2 ≤ C.size := by
  apply lowerFromRows (k := 1) C fit (![{0}, {1, 4, 5}, {2, 3, 4, 5}] : Fin 3 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_238 (C : AndCountCircuit 6) (fit : Fits 238 C) : 1 ≤ C.size := by
  apply lowerFromRows (k := 0) C fit (![{0, 1, 5}, {2, 3, 4, 5}] : Fin 2 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_239 (C : AndCountCircuit 6) (fit : Fits 239 C) : 2 ≤ C.size := by
  apply lowerFromRows (k := 1) C fit (![{0, 5}, {1, 5}, {2, 3, 4, 5}] : Fin 3 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_246 (C : AndCountCircuit 6) (fit : Fits 246 C) : 2 ≤ C.size := by
  apply lowerFromRows (k := 1) C fit (![{0, 1}, {0, 4}, {1, 5}] : Fin 3 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_247 (C : AndCountCircuit 6) (fit : Fits 247 C) : 2 ≤ C.size := by
  apply lowerFromRows (k := 1) C fit (![{0, 4}, {1, 5}, {2, 3, 4, 5}] : Fin 3 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_254 (C : AndCountCircuit 6) (fit : Fits 254 C) : 2 ≤ C.size := by
  apply lowerFromRows (k := 1) C fit (![{0, 1}, {1, 5}, {2, 3, 4, 5}] : Fin 3 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_255 (C : AndCountCircuit 6) (fit : Fits 255 C) : 2 ≤ C.size := by
  apply lowerFromRows (k := 1) C fit (![{0}, {1, 5}, {2, 3, 4, 5}] : Fin 3 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_510 (C : AndCountCircuit 6) (fit : Fits 510 C) : 1 ≤ C.size := by
  apply lowerFromRows (k := 0) C fit (![{0, 1}, {2, 3, 4, 5}] : Fin 2 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_511 (C : AndCountCircuit 6) (fit : Fits 511 C) : 2 ≤ C.size := by
  apply lowerFromRows (k := 1) C fit (![{0}, {1}, {2, 3, 4, 5}] : Fin 3 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_615 (C : AndCountCircuit 6) (fit : Fits 615 C) : 2 ≤ C.size := by
  apply lowerFromRows (k := 1) C fit (![{0, 4, 5}, {1, 4, 5}, {2, 4, 5}] : Fin 3 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_616 (C : AndCountCircuit 6) (fit : Fits 616 C) : 3 ≤ C.size := by
  apply lowerFromRows (k := 2) C fit (![{0, 1, 5}, {0, 2, 5}, {0, 3, 5}, {1, 4, 5}, {2, 4, 5}] : Fin 5 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_617 (C : AndCountCircuit 6) (fit : Fits 617 C) : 3 ≤ C.size := by
  apply lowerFromRows (k := 2) C fit (![{0, 2, 5}, {0, 3, 5}, {1, 4, 5}, {2, 4, 5}, {3, 4, 5}] : Fin 5 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem count_619 (C : AndCountCircuit 6) (fit : Fits 619 C) : 2 ≤ C.size := by
  apply lowerFromRows (k := 1) C fit (![{0, 3, 5}, {1, 4, 5}, {2, 4, 5}] : Fin 3 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem count_623 (C : AndCountCircuit 6) (fit : Fits 623 C) : 2 ≤ C.size := by
  apply lowerFromRows (k := 1) C fit (![{0, 5}, {1, 4, 5}, {2, 4, 5}] : Fin 3 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_632 (C : AndCountCircuit 6) (fit : Fits 632 C) : 3 ≤ C.size := by
  apply lowerFromRows (k := 2) C fit (![{0, 1}, {0, 2}, {0, 3}, {1, 4, 5}, {2, 4, 5}] : Fin 5 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_633 (C : AndCountCircuit 6) (fit : Fits 633 C) : 3 ≤ C.size := by
  apply lowerFromRows (k := 2) C fit (![{0, 2}, {0, 3}, {1, 4, 5}, {2, 4, 5}, {3, 4, 5}] : Fin 5 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem count_635 (C : AndCountCircuit 6) (fit : Fits 635 C) : 2 ≤ C.size := by
  apply lowerFromRows (k := 1) C fit (![{0, 3}, {1, 4, 5}, {2, 4, 5}] : Fin 3 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem count_639 (C : AndCountCircuit 6) (fit : Fits 639 C) : 2 ≤ C.size := by
  apply lowerFromRows (k := 1) C fit (![{0}, {1, 4, 5}, {2, 4, 5}] : Fin 3 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_655 (C : AndCountCircuit 6) (fit : Fits 655 C) : 3 ≤ C.size := by
  apply lowerFromRows (k := 2) C fit (![{0, 5}, {1, 2, 5}, {1, 3, 5}, {2, 4, 5}, {3, 4, 5}] : Fin 5 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_656 (C : AndCountCircuit 6) (fit : Fits 656 C) : 3 ≤ C.size := by
  apply lowerFromRows (k := 2) C fit (![{0, 1, 2}, {0, 1, 3}, {0, 2, 4}, {0, 3, 4}, {1, 2, 5}] : Fin 5 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_657 (C : AndCountCircuit 6) (fit : Fits 657 C) : 3 ≤ C.size := by
  apply lowerFromRows (k := 2) C fit (![{0, 2, 4}, {0, 3, 4}, {1, 2, 5}, {1, 3, 5}, {2, 4, 5}] : Fin 5 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_659 (C : AndCountCircuit 6) (fit : Fits 659 C) : 3 ≤ C.size := by
  apply lowerFromRows (k := 2) C fit (![{0, 3, 4}, {1, 2, 5}, {1, 3, 5}, {2, 4, 5}, {3, 4, 5}] : Fin 5 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_662 (C : AndCountCircuit 6) (fit : Fits 662 C) : 3 ≤ C.size := by
  apply lowerFromRows (k := 2) C fit (![{0, 1}, {0, 4}, {1, 2, 5}, {1, 3, 5}, {2, 4, 5}] : Fin 5 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_663 (C : AndCountCircuit 6) (fit : Fits 663 C) : 3 ≤ C.size := by
  apply lowerFromRows (k := 2) C fit (![{0, 4}, {1, 2, 5}, {1, 3, 5}, {2, 4, 5}, {3, 4, 5}] : Fin 5 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_671 (C : AndCountCircuit 6) (fit : Fits 671 C) : 3 ≤ C.size := by
  apply lowerFromRows (k := 2) C fit (![{0}, {1, 2, 5}, {1, 3, 5}, {2, 4, 5}, {3, 4, 5}] : Fin 5 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_684 (C : AndCountCircuit 6) (fit : Fits 684 C) : 3 ≤ C.size := by
  apply lowerFromRows (k := 2) C fit (![{0, 1, 5}, {0, 2, 5}, {1, 3, 5}, {2, 4, 5}, {3, 4, 5}] : Fin 5 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_685 (C : AndCountCircuit 6) (fit : Fits 685 C) : 2 ≤ C.size := by
  apply lowerFromRows (k := 1) C fit (![{0, 2, 5}, {1, 3, 5}, {2, 4, 5}] : Fin 3 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_687 (C : AndCountCircuit 6) (fit : Fits 687 C) : 2 ≤ C.size := by
  apply lowerFromRows (k := 1) C fit (![{0, 5}, {1, 3, 5}, {2, 4, 5}] : Fin 3 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem count_691 (C : AndCountCircuit 6) (fit : Fits 691 C) : 2 ≤ C.size := by
  apply lowerFromRows (k := 1) C fit (![{0, 3, 4}, {1, 3, 5}, {2, 4, 5}] : Fin 3 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_692 (C : AndCountCircuit 6) (fit : Fits 692 C) : 3 ≤ C.size := by
  apply lowerFromRows (k := 2) C fit (![{0, 1}, {0, 2, 4}, {1, 3, 5}, {2, 4, 5}, {3, 4, 5}] : Fin 5 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem count_693 (C : AndCountCircuit 6) (fit : Fits 693 C) : 2 ≤ C.size := by
  apply lowerFromRows (k := 1) C fit (![{0, 2, 4}, {1, 3, 5}, {2, 4, 5}] : Fin 3 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_694 (C : AndCountCircuit 6) (fit : Fits 694 C) : 3 ≤ C.size := by
  apply lowerFromRows (k := 2) C fit (![{0, 1}, {0, 4}, {1, 3, 5}, {2, 4, 5}, {3, 4, 5}] : Fin 5 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem count_695 (C : AndCountCircuit 6) (fit : Fits 695 C) : 2 ≤ C.size := by
  apply lowerFromRows (k := 1) C fit (![{0, 4}, {1, 3, 5}, {2, 4, 5}] : Fin 3 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_700 (C : AndCountCircuit 6) (fit : Fits 700 C) : 3 ≤ C.size := by
  apply lowerFromRows (k := 2) C fit (![{0, 1}, {0, 2}, {1, 3, 5}, {2, 4, 5}, {3, 4, 5}] : Fin 5 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem count_701 (C : AndCountCircuit 6) (fit : Fits 701 C) : 2 ≤ C.size := by
  apply lowerFromRows (k := 1) C fit (![{0, 2}, {1, 3, 5}, {2, 4, 5}] : Fin 3 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem count_703 (C : AndCountCircuit 6) (fit : Fits 703 C) : 2 ≤ C.size := by
  apply lowerFromRows (k := 1) C fit (![{0}, {1, 3, 5}, {2, 4, 5}] : Fin 3 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_750 (C : AndCountCircuit 6) (fit : Fits 750 C) : 2 ≤ C.size := by
  apply lowerFromRows (k := 1) C fit (![{0, 1, 5}, {2, 4, 5}, {3, 4, 5}] : Fin 3 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_751 (C : AndCountCircuit 6) (fit : Fits 751 C) : 2 ≤ C.size := by
  apply lowerFromRows (k := 1) C fit (![{0, 5}, {1, 5}, {2, 4, 5}] : Fin 3 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_758 (C : AndCountCircuit 6) (fit : Fits 758 C) : 3 ≤ C.size := by
  apply lowerFromRows (k := 2) C fit (![{0, 1}, {0, 4}, {1, 5}, {2, 4, 5}, {3, 4, 5}] : Fin 5 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem count_759 (C : AndCountCircuit 6) (fit : Fits 759 C) : 2 ≤ C.size := by
  apply lowerFromRows (k := 1) C fit (![{0, 4}, {1, 5}, {2, 4, 5}] : Fin 3 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_760 (C : AndCountCircuit 6) (fit : Fits 760 C) : 3 ≤ C.size := by
  apply lowerFromRows (k := 2) C fit (![{0, 1}, {0, 2}, {0, 3}, {1, 5}, {2, 4, 5}] : Fin 5 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_761 (C : AndCountCircuit 6) (fit : Fits 761 C) : 3 ≤ C.size := by
  apply lowerFromRows (k := 2) C fit (![{0, 2}, {0, 3}, {1, 5}, {2, 4, 5}, {3, 4, 5}] : Fin 5 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_762 (C : AndCountCircuit 6) (fit : Fits 762 C) : 3 ≤ C.size := by
  apply lowerFromRows (k := 2) C fit (![{0, 1}, {0, 3}, {1, 5}, {2, 4, 5}, {3, 4, 5}] : Fin 5 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem count_763 (C : AndCountCircuit 6) (fit : Fits 763 C) : 2 ≤ C.size := by
  apply lowerFromRows (k := 1) C fit (![{0, 3}, {1, 5}, {2, 4, 5}] : Fin 3 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem count_766 (C : AndCountCircuit 6) (fit : Fits 766 C) : 2 ≤ C.size := by
  apply lowerFromRows (k := 1) C fit (![{0, 1}, {1, 5}, {2, 4, 5}] : Fin 3 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem count_767 (C : AndCountCircuit 6) (fit : Fits 767 C) : 2 ≤ C.size := by
  apply lowerFromRows (k := 1) C fit (![{0}, {1, 5}, {2, 4, 5}] : Fin 3 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_920 (C : AndCountCircuit 6) (fit : Fits 920 C) : 2 ≤ C.size := by
  apply lowerFromRows (k := 1) C fit (![{0, 1, 2}, {0, 1, 3}, {2, 4, 5}] : Fin 3 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_921 (C : AndCountCircuit 6) (fit : Fits 921 C) : 3 ≤ C.size := by
  apply lowerFromRows (k := 2) C fit (![{0, 2}, {1, 2}, {0, 3}, {1, 3}, {2, 4, 5}] : Fin 5 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_922 (C : AndCountCircuit 6) (fit : Fits 922 C) : 2 ≤ C.size := by
  apply lowerFromRows (k := 1) C fit (![{1, 2}, {0, 1, 3}, {2, 4, 5}] : Fin 3 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_923 (C : AndCountCircuit 6) (fit : Fits 923 C) : 3 ≤ C.size := by
  apply lowerFromRows (k := 2) C fit (![{1, 2}, {0, 3}, {1, 3}, {2, 4, 5}, {3, 4, 5}] : Fin 5 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_926 (C : AndCountCircuit 6) (fit : Fits 926 C) : 3 ≤ C.size := by
  apply lowerFromRows (k := 2) C fit (![{0, 1}, {1, 2}, {1, 3}, {2, 4, 5}, {3, 4, 5}] : Fin 5 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_927 (C : AndCountCircuit 6) (fit : Fits 927 C) : 3 ≤ C.size := by
  apply lowerFromRows (k := 2) C fit (![{0}, {1, 2}, {1, 3}, {2, 4, 5}, {3, 4, 5}] : Fin 5 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_954 (C : AndCountCircuit 6) (fit : Fits 954 C) : 2 ≤ C.size := by
  apply lowerFromRows (k := 1) C fit (![{0, 1, 3}, {2, 4, 5}, {3, 4, 5}] : Fin 3 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem count_955 (C : AndCountCircuit 6) (fit : Fits 955 C) : 2 ≤ C.size := by
  apply lowerFromRows (k := 1) C fit (![{0, 3}, {1, 3}, {2, 4, 5}] : Fin 3 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_956 (C : AndCountCircuit 6) (fit : Fits 956 C) : 3 ≤ C.size := by
  apply lowerFromRows (k := 2) C fit (![{0, 1}, {0, 2}, {1, 3}, {2, 4, 5}, {3, 4, 5}] : Fin 5 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_957 (C : AndCountCircuit 6) (fit : Fits 957 C) : 2 ≤ C.size := by
  apply lowerFromRows (k := 1) C fit (![{0, 2}, {1, 3}, {2, 4, 5}] : Fin 3 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_958 (C : AndCountCircuit 6) (fit : Fits 958 C) : 2 ≤ C.size := by
  apply lowerFromRows (k := 1) C fit (![{0, 1}, {1, 3}, {2, 4, 5}] : Fin 3 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_959 (C : AndCountCircuit 6) (fit : Fits 959 C) : 2 ≤ C.size := by
  apply lowerFromRows (k := 1) C fit (![{0}, {1, 3}, {2, 4, 5}] : Fin 3 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_1022 (C : AndCountCircuit 6) (fit : Fits 1022 C) : 2 ≤ C.size := by
  apply lowerFromRows (k := 1) C fit (![{0, 1}, {2, 4, 5}, {3, 4, 5}] : Fin 3 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_1023 (C : AndCountCircuit 6) (fit : Fits 1023 C) : 2 ≤ C.size := by
  apply lowerFromRows (k := 1) C fit (![{0}, {1}, {2, 4, 5}] : Fin 3 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_1743 (C : AndCountCircuit 6) (fit : Fits 1743 C) : 2 ≤ C.size := by
  apply lowerFromRows (k := 1) C fit (![{0, 5}, {1, 2, 5}, {3, 4, 5}] : Fin 3 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_1749 (C : AndCountCircuit 6) (fit : Fits 1749 C) : 2 ≤ C.size := by
  apply lowerFromRows (k := 1) C fit (![{0, 2}, {0, 4}, {1, 2, 5}] : Fin 3 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_1751 (C : AndCountCircuit 6) (fit : Fits 1751 C) : 2 ≤ C.size := by
  apply lowerFromRows (k := 1) C fit (![{0, 4}, {1, 2, 5}, {3, 4, 5}] : Fin 3 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_1759 (C : AndCountCircuit 6) (fit : Fits 1759 C) : 2 ≤ C.size := by
  apply lowerFromRows (k := 1) C fit (![{0}, {1, 2, 5}, {3, 4, 5}] : Fin 3 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_1775 (C : AndCountCircuit 6) (fit : Fits 1775 C) : 2 ≤ C.size := by
  apply lowerFromRows (k := 1) C fit (![{0, 5}, {1, 5}, {2, 5}] : Fin 3 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_1780 (C : AndCountCircuit 6) (fit : Fits 1780 C) : 3 ≤ C.size := by
  apply lowerFromRows (k := 2) C fit (![{0, 1}, {0, 2}, {0, 4}, {1, 5}, {2, 5}] : Fin 5 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_1781 (C : AndCountCircuit 6) (fit : Fits 1781 C) : 3 ≤ C.size := by
  apply lowerFromRows (k := 2) C fit (![{0, 2}, {0, 4}, {1, 5}, {2, 5}, {3, 4, 5}] : Fin 5 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem count_1783 (C : AndCountCircuit 6) (fit : Fits 1783 C) : 2 ≤ C.size := by
  apply lowerFromRows (k := 1) C fit (![{0, 4}, {1, 5}, {2, 5}] : Fin 3 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_1788 (C : AndCountCircuit 6) (fit : Fits 1788 C) : 3 ≤ C.size := by
  apply lowerFromRows (k := 2) C fit (![{0, 1}, {0, 2}, {1, 5}, {2, 5}, {3, 4, 5}] : Fin 5 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem count_1789 (C : AndCountCircuit 6) (fit : Fits 1789 C) : 2 ≤ C.size := by
  apply lowerFromRows (k := 1) C fit (![{0, 2}, {1, 5}, {2, 5}] : Fin 3 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem count_1791 (C : AndCountCircuit 6) (fit : Fits 1791 C) : 2 ≤ C.size := by
  apply lowerFromRows (k := 1) C fit (![{0}, {1, 5}, {2, 5}] : Fin 3 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_1880 (C : AndCountCircuit 6) (fit : Fits 1880 C) : 3 ≤ C.size := by
  apply lowerFromRows (k := 2) C fit (![{0, 1, 2}, {0, 3}, {1, 4}, {2, 5}, {3, 4, 5}] : Fin 5 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_1881 (C : AndCountCircuit 6) (fit : Fits 1881 C) : 3 ≤ C.size := by
  apply lowerFromRows (k := 2) C fit (![{0, 2}, {1, 2}, {0, 3}, {1, 4}, {2, 5}] : Fin 5 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_1883 (C : AndCountCircuit 6) (fit : Fits 1883 C) : 3 ≤ C.size := by
  apply lowerFromRows (k := 2) C fit (![{1, 2}, {0, 3}, {1, 4}, {2, 5}, {3, 4, 5}] : Fin 5 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_1884 (C : AndCountCircuit 6) (fit : Fits 1884 C) : 2 ≤ C.size := by
  apply lowerFromRows (k := 1) C fit (![{0, 1, 2}, {1, 4}, {2, 5}] : Fin 3 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_1885 (C : AndCountCircuit 6) (fit : Fits 1885 C) : 3 ≤ C.size := by
  apply lowerFromRows (k := 2) C fit (![{0, 2}, {1, 2}, {1, 4}, {2, 5}, {3, 4, 5}] : Fin 5 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_1887 (C : AndCountCircuit 6) (fit : Fits 1887 C) : 3 ≤ C.size := by
  apply lowerFromRows (k := 2) C fit (![{0}, {1, 2}, {1, 4}, {2, 5}, {3, 4, 5}] : Fin 5 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem count_1915 (C : AndCountCircuit 6) (fit : Fits 1915 C) : 2 ≤ C.size := by
  apply lowerFromRows (k := 1) C fit (![{0, 3}, {1, 4}, {2, 5}] : Fin 3 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_1916 (C : AndCountCircuit 6) (fit : Fits 1916 C) : 3 ≤ C.size := by
  apply lowerFromRows (k := 2) C fit (![{0, 1}, {0, 2}, {1, 4}, {2, 5}, {3, 4, 5}] : Fin 5 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_1917 (C : AndCountCircuit 6) (fit : Fits 1917 C) : 2 ≤ C.size := by
  apply lowerFromRows (k := 1) C fit (![{0, 2}, {1, 4}, {2, 5}] : Fin 3 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_1919 (C : AndCountCircuit 6) (fit : Fits 1919 C) : 2 ≤ C.size := by
  apply lowerFromRows (k := 1) C fit (![{0}, {1, 4}, {2, 5}] : Fin 3 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_2012 (C : AndCountCircuit 6) (fit : Fits 2012 C) : 2 ≤ C.size := by
  apply lowerFromRows (k := 1) C fit (![{0, 1, 2}, {2, 5}, {3, 4, 5}] : Fin 3 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem count_2013 (C : AndCountCircuit 6) (fit : Fits 2013 C) : 2 ≤ C.size := by
  apply lowerFromRows (k := 1) C fit (![{0, 2}, {1, 2}, {2, 5}] : Fin 3 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_2014 (C : AndCountCircuit 6) (fit : Fits 2014 C) : 2 ≤ C.size := by
  apply lowerFromRows (k := 1) C fit (![{0, 1}, {1, 2}, {2, 5}] : Fin 3 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_2015 (C : AndCountCircuit 6) (fit : Fits 2015 C) : 2 ≤ C.size := by
  apply lowerFromRows (k := 1) C fit (![{0}, {1, 2}, {2, 5}] : Fin 3 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_2046 (C : AndCountCircuit 6) (fit : Fits 2046 C) : 2 ≤ C.size := by
  apply lowerFromRows (k := 1) C fit (![{0, 1}, {2, 5}, {3, 4, 5}] : Fin 3 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_2047 (C : AndCountCircuit 6) (fit : Fits 2047 C) : 2 ≤ C.size := by
  apply lowerFromRows (k := 1) C fit (![{0}, {1}, {2, 5}] : Fin 3 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_4060 (C : AndCountCircuit 6) (fit : Fits 4060 C) : 1 ≤ C.size := by
  apply lowerFromRows (k := 0) C fit (![{0, 1, 2}, {3, 4, 5}] : Fin 2 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_4061 (C : AndCountCircuit 6) (fit : Fits 4061 C) : 2 ≤ C.size := by
  apply lowerFromRows (k := 1) C fit (![{0, 2}, {1, 2}, {3, 4, 5}] : Fin 3 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_4063 (C : AndCountCircuit 6) (fit : Fits 4063 C) : 2 ≤ C.size := by
  apply lowerFromRows (k := 1) C fit (![{0}, {1, 2}, {3, 4, 5}] : Fin 3 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_4095 (C : AndCountCircuit 6) (fit : Fits 4095 C) : 2 ≤ C.size := by
  apply lowerFromRows (k := 1) C fit (![{0}, {1}, {2}] : Fin 3 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_5871 (C : AndCountCircuit 6) (fit : Fits 5871 C) : 3 ≤ C.size := by
  apply lowerFromRows (k := 2) C fit (![{0, 5}, {1, 5}, {2, 5}, {3, 5}, {4, 5}] : Fin 5 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_5872 (C : AndCountCircuit 6) (fit : Fits 5872 C) : 3 ≤ C.size := by
  apply lowerFromRows (k := 2) C fit (![{0, 1}, {0, 2}, {0, 3}, {0, 4}, {1, 5}] : Fin 5 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_5873 (C : AndCountCircuit 6) (fit : Fits 5873 C) : 3 ≤ C.size := by
  apply lowerFromRows (k := 2) C fit (![{0, 2}, {0, 3}, {0, 4}, {1, 5}, {2, 5}] : Fin 5 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_5875 (C : AndCountCircuit 6) (fit : Fits 5875 C) : 3 ≤ C.size := by
  apply lowerFromRows (k := 2) C fit (![{0, 3}, {0, 4}, {1, 5}, {2, 5}, {3, 5}] : Fin 5 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_5879 (C : AndCountCircuit 6) (fit : Fits 5879 C) : 3 ≤ C.size := by
  apply lowerFromRows (k := 2) C fit (![{0, 4}, {1, 5}, {2, 5}, {3, 5}, {4, 5}] : Fin 5 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_5887 (C : AndCountCircuit 6) (fit : Fits 5887 C) : 3 ≤ C.size := by
  apply lowerFromRows (k := 2) C fit (![{0}, {1, 5}, {2, 5}, {3, 5}, {4, 5}] : Fin 5 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_5905 (C : AndCountCircuit 6) (fit : Fits 5905 C) : 4 ≤ C.size := by
  apply lowerFromRows (k := 3) C fit (![{0, 2}, {1, 2}, {0, 3}, {1, 3}, {0, 4}, {1, 4}, {2, 5}, {3, 5}, {4, 5}] : Fin 9 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem count_5907 (C : AndCountCircuit 6) (fit : Fits 5907 C) : 3 ≤ C.size := by
  apply lowerFromRows (k := 2) C fit (![{1, 2}, {0, 3}, {1, 3}, {0, 4}, {1, 4}] : Fin 5 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem count_5911 (C : AndCountCircuit 6) (fit : Fits 5911 C) : 3 ≤ C.size := by
  apply lowerFromRows (k := 2) C fit (![{1, 2}, {1, 3}, {0, 4}, {1, 4}, {2, 5}] : Fin 5 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem count_5919 (C : AndCountCircuit 6) (fit : Fits 5919 C) : 3 ≤ C.size := by
  apply lowerFromRows (k := 2) C fit (![{0}, {1, 2}, {1, 3}, {1, 4}, {2, 5}] : Fin 5 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_5941 (C : AndCountCircuit 6) (fit : Fits 5941 C) : 3 ≤ C.size := by
  apply lowerFromRows (k := 2) C fit (![{0, 2}, {1, 3}, {0, 4}, {1, 4}, {2, 5}] : Fin 5 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_5943 (C : AndCountCircuit 6) (fit : Fits 5943 C) : 3 ≤ C.size := by
  apply lowerFromRows (k := 2) C fit (![{1, 3}, {0, 4}, {1, 4}, {2, 5}, {3, 5}] : Fin 5 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem count_5948 (C : AndCountCircuit 6) (fit : Fits 5948 C) : 3 ≤ C.size := by
  apply lowerFromRows (k := 2) C fit (![{0, 1}, {0, 2}, {1, 3}, {1, 4}, {2, 5}] : Fin 5 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_5949 (C : AndCountCircuit 6) (fit : Fits 5949 C) : 3 ≤ C.size := by
  apply lowerFromRows (k := 2) C fit (![{0, 2}, {1, 3}, {1, 4}, {2, 5}, {3, 5}] : Fin 5 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_5950 (C : AndCountCircuit 6) (fit : Fits 5950 C) : 3 ≤ C.size := by
  apply lowerFromRows (k := 2) C fit (![{0, 1}, {1, 3}, {1, 4}, {2, 5}, {3, 5}] : Fin 5 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_5951 (C : AndCountCircuit 6) (fit : Fits 5951 C) : 3 ≤ C.size := by
  apply lowerFromRows (k := 2) C fit (![{0}, {1, 3}, {1, 4}, {2, 5}, {3, 5}] : Fin 5 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_6007 (C : AndCountCircuit 6) (fit : Fits 6007 C) : 3 ≤ C.size := by
  apply lowerFromRows (k := 2) C fit (![{0, 4}, {1, 4}, {2, 5}, {3, 5}, {4, 5}] : Fin 5 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_6010 (C : AndCountCircuit 6) (fit : Fits 6010 C) : 3 ≤ C.size := by
  apply lowerFromRows (k := 2) C fit (![{0, 1}, {0, 3}, {1, 4}, {2, 5}, {3, 5}] : Fin 5 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_6011 (C : AndCountCircuit 6) (fit : Fits 6011 C) : 3 ≤ C.size := by
  apply lowerFromRows (k := 2) C fit (![{0, 3}, {1, 4}, {2, 5}, {3, 5}, {4, 5}] : Fin 5 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_6014 (C : AndCountCircuit 6) (fit : Fits 6014 C) : 3 ≤ C.size := by
  apply lowerFromRows (k := 2) C fit (![{0, 1}, {1, 4}, {2, 5}, {3, 5}, {4, 5}] : Fin 5 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_6015 (C : AndCountCircuit 6) (fit : Fits 6015 C) : 3 ≤ C.size := by
  apply lowerFromRows (k := 2) C fit (![{0}, {1, 4}, {2, 5}, {3, 5}, {4, 5}] : Fin 5 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem count_6142 (C : AndCountCircuit 6) (fit : Fits 6142 C) : 2 ≤ C.size := by
  apply lowerFromRows (k := 1) C fit (![{0, 1}, {2, 5}, {3, 5}] : Fin 3 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_6143 (C : AndCountCircuit 6) (fit : Fits 6143 C) : 3 ≤ C.size := by
  apply lowerFromRows (k := 2) C fit (![{0}, {1}, {2, 5}, {3, 5}, {4, 5}] : Fin 5 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_6654 (C : AndCountCircuit 6) (fit : Fits 6654 C) : 3 ≤ C.size := by
  apply lowerFromRows (k := 2) C fit (![{0, 1}, {2, 3}, {2, 4}, {3, 5}, {4, 5}] : Fin 5 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_6655 (C : AndCountCircuit 6) (fit : Fits 6655 C) : 3 ≤ C.size := by
  apply lowerFromRows (k := 2) C fit (![{0}, {1}, {2, 3}, {2, 4}, {3, 5}] : Fin 5 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_7071 (C : AndCountCircuit 6) (fit : Fits 7071 C) : 3 ≤ C.size := by
  apply lowerFromRows (k := 2) C fit (![{0}, {1, 2}, {1, 3}, {2, 4}, {3, 5}] : Fin 5 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_7100 (C : AndCountCircuit 6) (fit : Fits 7100 C) : 3 ≤ C.size := by
  apply lowerFromRows (k := 2) C fit (![{0, 1}, {0, 2}, {1, 3}, {2, 4}, {3, 5}] : Fin 5 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_7101 (C : AndCountCircuit 6) (fit : Fits 7101 C) : 3 ≤ C.size := by
  apply lowerFromRows (k := 2) C fit (![{0, 2}, {1, 3}, {2, 4}, {3, 5}, {4, 5}] : Fin 5 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_7103 (C : AndCountCircuit 6) (fit : Fits 7103 C) : 3 ≤ C.size := by
  apply lowerFromRows (k := 2) C fit (![{0}, {1, 3}, {2, 4}, {3, 5}, {4, 5}] : Fin 5 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_7166 (C : AndCountCircuit 6) (fit : Fits 7166 C) : 2 ≤ C.size := by
  apply lowerFromRows (k := 1) C fit (![{0, 1}, {2, 4}, {3, 5}] : Fin 3 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_7167 (C : AndCountCircuit 6) (fit : Fits 7167 C) : 3 ≤ C.size := by
  apply lowerFromRows (k := 2) C fit (![{0}, {1}, {2, 4}, {3, 5}, {4, 5}] : Fin 5 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_8157 (C : AndCountCircuit 6) (fit : Fits 8157 C) : 2 ≤ C.size := by
  apply lowerFromRows (k := 1) C fit (![{0, 2}, {1, 2}, {3, 5}] : Fin 3 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_8159 (C : AndCountCircuit 6) (fit : Fits 8159 C) : 2 ≤ C.size := by
  apply lowerFromRows (k := 1) C fit (![{0}, {1, 2}, {3, 5}] : Fin 3 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_8191 (C : AndCountCircuit 6) (fit : Fits 8191 C) : 3 ≤ C.size := by
  apply lowerFromRows (k := 2) C fit (![{0}, {1}, {2}, {3, 5}, {4, 5}] : Fin 5 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_15870 (C : AndCountCircuit 6) (fit : Fits 15870 C) : 2 ≤ C.size := by
  apply lowerFromRows (k := 1) C fit (![{0, 1}, {2, 3}, {4, 5}] : Fin 3 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_15871 (C : AndCountCircuit 6) (fit : Fits 15871 C) : 2 ≤ C.size := by
  apply lowerFromRows (k := 1) C fit (![{0}, {1}, {2, 3}] : Fin 3 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_16383 (C : AndCountCircuit 6) (fit : Fits 16383 C) : 3 ≤ C.size := by
  apply lowerFromRows (k := 2) C fit (![{0}, {1}, {2}, {3}, {4, 5}] : Fin 5 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem easy_32767 (C : AndCountCircuit 6) (fit : Fits 32767 C) : 3 ≤ C.size := by
  apply lowerFromRows (k := 2) C fit (![{0}, {1}, {2}, {3}, {4}] : Fin 5 → Finset (Fin 6))
  · decide
  · decide +kernel
  · decide +kernel

def rowFits (p : Fin 6 → Nat) (rm : Nat × Nat) : Prop :=
  ∀ v : Fin 6, rm.1.testBit v = (rm.2 &&& p v == 0)

def forbiddenAt (v : Fin 6) : List (Nat × Nat) → Nat
  | [] => 0
  | (r,m) :: rest =>
    if r.testBit v then m ||| forbiddenAt v rest else forbiddenAt v rest

theorem forbidden_disjoint (p : Fin 6 → Nat) (hist : List (Nat × Nat))
    (h : ∀ rm ∈ hist, rowFits p rm) (v : Fin 6) : forbiddenAt v hist &&& p v = 0 := by
  induction hist with
  | nil => simp [forbiddenAt]
  | cons rm tail ih =>
    rcases rm with ⟨r,m⟩
    have hv := h (r,m) (by simp) v
    have ht := ih (fun q hq => h q (by simp [hq]))
    cases e : r.testBit v with
    | false => simp [forbiddenAt, e, ht]
    | true =>
      change r.testBit v = (m &&& p v == 0) at hv
      have hm : m &&& p v = 0 := by simpa [e] using hv.symm
      simp [forbiddenAt, e, Nat.and_or_distrib_right, hm, ht]

def viable (hist : List (Nat × Nat)) : Bool :=
  (List.finRange 6).all fun v =>
    let denied := forbiddenAt v hist
    hist.all fun rm => rm.1.testBit v || (rm.2 &&& denied != rm.2)

theorem viable_of_fit (p : Fin 6 → Nat) (hist : List (Nat × Nat))
    (h : ∀ rm ∈ hist, rowFits p rm) : viable hist = true := by
  apply List.all_eq_true.mpr
  intro v _
  apply List.all_eq_true.mpr
  intro rm hr
  have hrow := h rm hr v
  cases e : rm.1.testBit v with
  | true => simp
  | false =>
    simp only [Bool.false_or, bne_iff_ne]
    intro absurdMask
    have hd := forbidden_disjoint p hist h v
    have hz : rm.2 &&& p v = 0 := by
      calc rm.2 &&& p v = (rm.2 &&& forbiddenAt v hist) &&& p v := congrArg (· &&& p v) absurdMask.symm
           _ = 0 := by rw [Nat.and_assoc, hd, Nat.and_zero]
    simp [e, hz] at hrow

def canAssign (masks : List Nat) : List Nat → List (Nat × Nat) → Bool
  | [], hist => viable hist
  | r :: rest, hist => viable hist && masks.any (fun m => canAssign masks rest ((r,m)::hist))

theorem canAssign_of_fit (masks todo : List Nat) (hist : List (Nat × Nat)) (p : Fin 6 → Nat)
    (h : ∀ rm ∈ hist, rowFits p rm) (next : ∀ r ∈ todo, ∃ m ∈ masks, rowFits p (r,m)) :
    canAssign masks todo hist = true := by
  induction todo generalizing hist with
  | nil => exact viable_of_fit p hist h
  | cons r rest ih =>
    obtain ⟨m, hm, hr⟩ := next r (by simp)
    simp only [canAssign, viable_of_fit p hist h, Bool.true_and, List.any_eq_true]
    refine ⟨m, hm, ih _ ?_ (fun q hq => next q (by simp [hq]))⟩
    intro q hq
    rcases List.mem_cons.mp hq with rfl | ht
    · exact hr
    · exact h q ht



def rowDistinct (rows : List Nat) : Bool :=
  decide (rows.Pairwise (fun a b => ∃ v : Fin 6, a.testBit v ≠ b.testBit v))

theorem fitLength (masks rows : List Nat) (p : Fin 6 → Nat) (hd : rowDistinct rows = true)
    (hn : ∀ r ∈ rows, ∃ m ∈ masks, rowFits p (r,m)) : rows.length ≤ masks.length := by
  classical
  let f (r : Nat) : Nat := if hr : r ∈ rows then (hn r hr).choose else 0
  have works (r : Nat) (hr : r ∈ rows) : f r ∈ masks ∧ rowFits p (r, f r) := by
    simpa [f, hr] using (hn r hr).choose_spec
  have pairs := of_decide_eq_true hd
  change rows.Pairwise (fun a b => ∃ v : Fin 6, a.testBit v ≠ b.testBit v) at pairs
  have no : (rows.map f).Nodup := by
    apply List.pairwise_map.mpr
    apply pairs.imp_of_mem
    intro a b ha hb witness
    obtain ⟨v,hv⟩ := witness
    intro same
    apply hv
    rw [(works a ha).2 v, (works b hb).2 v]
    exact congrArg (fun m => (m &&& p v == 0)) same
  have sub : rows.map f ⊆ masks := by
    intro m hm
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hm
    exact (works r hr).1
  simpa using no.length_le_of_subset sub

def checkedAssignment (masks rows : List Nat) : Bool :=
  decide (rows.length ≤ masks.length) && canAssign masks rows []

theorem firstMasksFail {masks tail : List Nat} {r : Nat}
    (none : masks.any (fun m => canAssign masks tail [(r,m)]) = false) :
    checkedAssignment masks (r :: tail) = false := by
  simp [checkedAssignment, canAssign, none]

theorem checkedAssignment_of_fit (masks rows : List Nat) (p : Fin 6 → Nat)
    (hd : rowDistinct rows = true) (hn : ∀ r ∈ rows, ∃ m ∈ masks, rowFits p (r,m)) :
    checkedAssignment masks rows = true := by
  simp [checkedAssignment, fitLength masks rows p hd hn,
    canAssign_of_fit masks rows [] p (by simp) hn]




def bitsVal : List Bool → Nat
  | [] => 0
  | b :: bs => b.toNat + 2 * bitsVal bs

def rawMask2 (a0 a1 s0 s1 : Bool) : Nat :=
  bitsVal [a0 && !s0, a0 && s0, a1 && !s1, a1 && s1, true]

set_option maxHeartbeats 0 in
theorem rawHit2 : ∀ a0 a1 s0 s1 x0 y0 x1 y1 z : Bool,
    (rawMask2 a0 a1 s0 s1 &&& bitsVal [x0, y0, x1, y1, z] != 0) =
      ((a0 && cond s0 y0 x0) || (a1 && cond s1 y1 x1) || z) := by decide +kernel

def foot2 (l10 r10 z0 z1 s0 s1 : Bool) : Nat :=
  let a1 := z1
  let a0 := z0 || (a1 && cond s1 r10 l10)
  rawMask2 a0 a1 s0 s1

def measures2 (l10 r10 z0 z1 : Bool) : List Nat :=
  [foot2 l10 r10 z0 z1 false false, foot2 l10 r10 z0 z1 true false, foot2 l10 r10 z0 z1 false true, foot2 l10 r10 z0 z1 true true]

theorem footMem2 (l10 r10 z0 z1 s0 s1 : Bool) :
    foot2 l10 r10 z0 z1 s0 s1 ∈ measures2 l10 r10 z0 z1 := by
  cases s0 <;> cases s1 <;> simp [measures2]

def families2 : List (List Nat) :=
  [[16],
   [17, 18],
   [20, 24],
   [21, 22, 24],
   [20, 25, 26],
   [21, 22, 25, 26]]

set_option maxHeartbeats 0 in
theorem familyCovers2 : ∀ l10 r10 z0 z1 : Bool,
    ∃ ms ∈ families2, (measures2 l10 r10 z0 z1).all (fun m => ms.contains m) = true := by
  decide +kernel

def rawMask3 (a0 a1 a2 s0 s1 s2 : Bool) : Nat :=
  bitsVal [a0 && !s0, a0 && s0, a1 && !s1, a1 && s1, a2 && !s2, a2 && s2, true]

set_option maxHeartbeats 0 in
theorem rawHit3 : ∀ a0 a1 a2 s0 s1 s2 x0 y0 x1 y1 x2 y2 z : Bool,
    (rawMask3 a0 a1 a2 s0 s1 s2 &&& bitsVal [x0, y0, x1, y1, x2, y2, z] != 0) =
      ((a0 && cond s0 y0 x0) || (a1 && cond s1 y1 x1) || (a2 && cond s2 y2 x2) || z) := by decide +kernel

def foot3 (l10 r10 l20 r20 l21 r21 z0 z1 z2 s0 s1 s2 : Bool) : Nat :=
  let a2 := z2
  let a1 := z1 || (a2 && cond s2 r21 l21)
  let a0 := z0 || (a1 && cond s1 r10 l10) || (a2 && cond s2 r20 l20)
  rawMask3 a0 a1 a2 s0 s1 s2

def measures3 (l10 r10 l20 r20 l21 r21 z0 z1 z2 : Bool) : List Nat :=
  [foot3 l10 r10 l20 r20 l21 r21 z0 z1 z2 false false false, foot3 l10 r10 l20 r20 l21 r21 z0 z1 z2 true false false, foot3 l10 r10 l20 r20 l21 r21 z0 z1 z2 false true false, foot3 l10 r10 l20 r20 l21 r21 z0 z1 z2 true true false, foot3 l10 r10 l20 r20 l21 r21 z0 z1 z2 false false true, foot3 l10 r10 l20 r20 l21 r21 z0 z1 z2 true false true, foot3 l10 r10 l20 r20 l21 r21 z0 z1 z2 false true true, foot3 l10 r10 l20 r20 l21 r21 z0 z1 z2 true true true]

theorem footMem3 (l10 r10 l20 r20 l21 r21 z0 z1 z2 s0 s1 s2 : Bool) :
    foot3 l10 r10 l20 r20 l21 r21 z0 z1 z2 s0 s1 s2 ∈ measures3 l10 r10 l20 r20 l21 r21 z0 z1 z2 := by
  cases s0 <;> cases s1 <;> cases s2 <;> simp [measures3]

def families3 : List (List Nat) :=
  [[64],
   [65, 66],
   [68, 72],
   [69, 70, 72],
   [68, 73, 74],
   [69, 70, 73, 74],
   [80, 96],
   [81, 82, 96],
   [80, 97, 98],
   [81, 82, 97, 98],
   [84, 88, 96],
   [85, 86, 88, 96],
   [84, 89, 90, 96],
   [85, 86, 89, 90, 96],
   [84, 88, 97, 98],
   [85, 86, 88, 97, 98],
   [84, 89, 90, 97, 98],
   [85, 86, 89, 90, 97, 98],
   [80, 100, 104],
   [80, 101, 102, 104],
   [80, 100, 105, 106],
   [80, 101, 102, 105, 106],
   [81, 82, 100, 104],
   [81, 82, 101, 102, 104],
   [81, 82, 100, 105, 106],
   [81, 82, 101, 102, 105, 106],
   [84, 88, 100, 104],
   [85, 86, 88, 101, 102, 104],
   [84, 89, 90, 100, 105, 106],
   [85, 86, 89, 90, 101, 102, 105, 106],
   [85, 86, 89, 90, 100, 104],
   [85, 86, 89, 90, 101, 102, 104],
   [85, 86, 89, 90, 100, 105, 106],
   [84, 88, 101, 102, 105, 106],
   [85, 86, 88, 101, 102, 105, 106],
   [84, 89, 90, 101, 102, 105, 106]]

set_option maxHeartbeats 0 in
theorem familyCovers3 : ∀ l10 r10 l20 r20 l21 r21 z0 z1 z2 : Bool,
    ∃ ms ∈ families3, (measures3 l10 r10 l20 r20 l21 r21 z0 z1 z2).all (fun m => ms.contains m) = true := by
  decide +kernel



open PEqualNP.AndCount

abbrev mkSC (k : Nat) (lv : Fin k → Finset (Fin 6)) (lg : Fin k → Finset (Fin k))
    (rv : Fin k → Finset (Fin 6)) (rg : Fin k → Finset (Fin k)) (ov : Finset (Fin 6))
    (og : Finset (Fin k)) : AndCountCircuit 6 := ⟨k, lv, lg, rv, rg, ov, og⟩

def supportRow (r : Nat) : Finset (Fin 6) := Finset.univ.filter (fun v => r.testBit v)

def goodRow (g r : Nat) : Bool :=
  let I := supportRow r
  decide ((∀ v ∈ I, ∀ w ∈ I, ¬ Adjacent g v w) ∧ (∀ u, u ∉ I → ∃ v ∈ I, Adjacent g u v))

theorem bitsCert {g r : Nat} {C : AndCountCircuit 6} (fit : Fits g C) (good : goodRow g r = true) :
    ∃ o : Fin C.size → Bool, ∀ v : Fin 6, excluded C o v = !r.testBit v := by
  obtain ⟨ind, dom⟩ := of_decide_eq_true good
  obtain ⟨neg,pos⟩ := fit (supportRow r) ind dom
  obtain ⟨o,ho⟩ := orientCert C (supportRow r) neg pos
  refine ⟨o, fun v => ?_⟩
  simpa [supportRow] using ho v

set_option maxHeartbeats 4000000 in
theorem decodeExc2 (lv : Fin 2 → Finset (Fin 6)) (lg : Fin 2 → Finset (Fin 2))
    (rv : Fin 2 → Finset (Fin 6)) (rg : Fin 2 → Finset (Fin 2))
    (ov : Finset (Fin 6)) (og : Finset (Fin 2))
    (o : Fin 2 → Bool) (v : Fin 6) :
    excluded (mkSC 2 lv lg rv rg ov og) o v = (foot2 (decide (0 ∈ lg 1)) (decide (0 ∈ rg 1)) (decide (0 ∈ og)) (decide (1 ∈ og)) (o 0) (o 1) &&& bitsVal [decide (v ∈ lv 0), decide (v ∈ rv 0), decide (v ∈ lv 1), decide (v ∈ rv 1), decide (v ∈ ov)] != 0) := by
  simp only [foot2, rawHit2]
  apply Bool.eq_iff_iff.mpr
  cases h0 : o 0 <;> cases h1 : o 1 <;>
    simp [excluded, excFuel, sideVars, sideGates, mkSC, h0, h1] <;>
    tauto

theorem orientImpossible2 (g : Nat) (rows : List Nat) (C : AndCountCircuit 6)
    (fit : Fits g C) (sz : C.size = 2) (good : rows.all (goodRow g) = true)
    (rd : rowDistinct rows = true)
    (block : (families2.any (fun ms => checkedAssignment ms rows)) = false) : False := by
  rcases C with ⟨sz0,lv,lg,rv,rg,ov,og⟩
  change sz0 = 2 at sz
  subst sz0
  obtain ⟨ms, hm, hall⟩ := familyCovers2 (decide (0 ∈ lg 1)) (decide (0 ∈ rg 1)) (decide (0 ∈ og)) (decide (1 ∈ og))
  let p (v : Fin 6) : Nat := bitsVal [decide (v ∈ lv 0), decide (v ∈ rv 0), decide (v ∈ lv 1), decide (v ∈ rv 1), decide (v ∈ ov)]
  have ht : checkedAssignment ms rows = true := by
    apply checkedAssignment_of_fit ms rows p rd
    intro r hr
    obtain ⟨o,ho⟩ := bitsCert fit (List.all_eq_true.mp good r hr)
    let m := foot2 (decide (0 ∈ lg 1)) (decide (0 ∈ rg 1)) (decide (0 ∈ og)) (decide (1 ∈ og)) (o 0) (o 1)
    have hmem : m ∈ ms := by
      simpa using List.all_eq_true.mp hall m (footMem2 (decide (0 ∈ lg 1)) (decide (0 ∈ rg 1)) (decide (0 ∈ og)) (decide (1 ∈ og)) (o 0) (o 1))
    refine ⟨m, hmem, fun v => ?_⟩
    have hd := decodeExc2 lv lg rv rg ov og o v
    change excluded (mkSC 2 lv lg rv rg ov og) o v = (m &&& p v != 0) at hd
    have hz := ho v
    change excluded (mkSC 2 lv lg rv rg ov og) o v = !r.testBit v at hz
    change r.testBit v = (m &&& p v == 0)
    rw [hd] at hz
    cases e : r.testBit v <;> simp_all
  have hyes : (families2.any (fun ms => checkedAssignment ms rows)) = true :=
    List.any_eq_true.mpr ⟨ms,hm,ht⟩
  simp [hyes] at block

theorem exGate3 (P : Fin 3 → Prop) : (∃ i, P i) ↔ P 0 ∨ P 1 ∨ P 2 := by
  constructor
  · rintro ⟨i, h⟩
    fin_cases i <;> simp_all
  · rintro (h | h | h)
    · exact ⟨0,h⟩
    · exact ⟨1,h⟩
    · exact ⟨2,h⟩

set_option maxHeartbeats 4000000 in
theorem decodeExc3 (lv : Fin 3 → Finset (Fin 6)) (lg : Fin 3 → Finset (Fin 3))
    (rv : Fin 3 → Finset (Fin 6)) (rg : Fin 3 → Finset (Fin 3))
    (ov : Finset (Fin 6)) (og : Finset (Fin 3))
    (o : Fin 3 → Bool) (v : Fin 6) :
    excluded (mkSC 3 lv lg rv rg ov og) o v = (foot3 (decide (0 ∈ lg 1)) (decide (0 ∈ rg 1)) (decide (0 ∈ lg 2)) (decide (0 ∈ rg 2)) (decide (1 ∈ lg 2)) (decide (1 ∈ rg 2)) (decide (0 ∈ og)) (decide (1 ∈ og)) (decide (2 ∈ og)) (o 0) (o 1) (o 2) &&& bitsVal [decide (v ∈ lv 0), decide (v ∈ rv 0), decide (v ∈ lv 1), decide (v ∈ rv 1), decide (v ∈ lv 2), decide (v ∈ rv 2), decide (v ∈ ov)] != 0) := by
  simp only [foot3, rawHit3]
  apply Bool.eq_iff_iff.mpr
  cases h0 : o 0 <;> cases h1 : o 1 <;> cases h2 : o 2 <;>
    simp [excluded, excFuel, sideVars, sideGates, mkSC, exGate3, h0, h1, h2] <;>
    tauto

theorem orientImpossible3 (g : Nat) (rows : List Nat) (C : AndCountCircuit 6)
    (fit : Fits g C) (sz : C.size = 3) (good : rows.all (goodRow g) = true)
    (rd : rowDistinct rows = true)
    (block : (families3.any (fun ms => checkedAssignment ms rows)) = false) : False := by
  rcases C with ⟨sz0,lv,lg,rv,rg,ov,og⟩
  change sz0 = 3 at sz
  subst sz0
  obtain ⟨ms, hm, hall⟩ := familyCovers3 (decide (0 ∈ lg 1)) (decide (0 ∈ rg 1)) (decide (0 ∈ lg 2)) (decide (0 ∈ rg 2)) (decide (1 ∈ lg 2)) (decide (1 ∈ rg 2)) (decide (0 ∈ og)) (decide (1 ∈ og)) (decide (2 ∈ og))
  let p (v : Fin 6) : Nat := bitsVal [decide (v ∈ lv 0), decide (v ∈ rv 0), decide (v ∈ lv 1), decide (v ∈ rv 1), decide (v ∈ lv 2), decide (v ∈ rv 2), decide (v ∈ ov)]
  have ht : checkedAssignment ms rows = true := by
    apply checkedAssignment_of_fit ms rows p rd
    intro r hr
    obtain ⟨o,ho⟩ := bitsCert fit (List.all_eq_true.mp good r hr)
    let m := foot3 (decide (0 ∈ lg 1)) (decide (0 ∈ rg 1)) (decide (0 ∈ lg 2)) (decide (0 ∈ rg 2)) (decide (1 ∈ lg 2)) (decide (1 ∈ rg 2)) (decide (0 ∈ og)) (decide (1 ∈ og)) (decide (2 ∈ og)) (o 0) (o 1) (o 2)
    have hmem : m ∈ ms := by
      simpa using List.all_eq_true.mp hall m (footMem3 (decide (0 ∈ lg 1)) (decide (0 ∈ rg 1)) (decide (0 ∈ lg 2)) (decide (0 ∈ rg 2)) (decide (1 ∈ lg 2)) (decide (1 ∈ rg 2)) (decide (0 ∈ og)) (decide (1 ∈ og)) (decide (2 ∈ og)) (o 0) (o 1) (o 2))
    refine ⟨m, hmem, fun v => ?_⟩
    have hd := decodeExc3 lv lg rv rg ov og o v
    change excluded (mkSC 3 lv lg rv rg ov og) o v = (m &&& p v != 0) at hd
    have hz := ho v
    change excluded (mkSC 3 lv lg rv rg ov og) o v = !r.testBit v at hz
    change r.testBit v = (m &&& p v == 0)
    rw [hd] at hz
    cases e : r.testBit v <;> simp_all
  have hyes : (families3.any (fun ms => checkedAssignment ms rows)) = true :=
    List.any_eq_true.mpr ⟨ms,hm,ht⟩
  simp [hyes] at block


theorem noMatch_619_3 : checkedAssignment [21, 22, 25, 26] [41, 50, 52, 56] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem blocked_619 : (families2.any (fun ms => checkedAssignment ms [41, 50, 52, 56])) = false := by
  simp only [families2,List.any_cons,List.any_nil,noMatch_619_3,Bool.or_false]
  decide +kernel

theorem noMatch_623_3 : checkedAssignment [21, 22, 25, 26] [33, 50, 52, 56] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem blocked_623 : (families2.any (fun ms => checkedAssignment ms [33, 50, 52, 56])) = false := by
  simp only [families2,List.any_cons,List.any_nil,noMatch_623_3,Bool.or_false]
  decide +kernel

theorem noMatch_635_3 : checkedAssignment [21, 22, 25, 26] [9, 50, 52, 56] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem blocked_635 : (families2.any (fun ms => checkedAssignment ms [9, 50, 52, 56])) = false := by
  simp only [families2,List.any_cons,List.any_nil,noMatch_635_3,Bool.or_false]
  decide +kernel

theorem noMatch_639_3 : checkedAssignment [21, 22, 25, 26] [1, 50, 52, 56] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem blocked_639 : (families2.any (fun ms => checkedAssignment ms [1, 50, 52, 56])) = false := by
  simp only [families2,List.any_cons,List.any_nil,noMatch_639_3,Bool.or_false]
  decide +kernel

theorem noMatch_691_3 : checkedAssignment [21, 22, 25, 26] [25, 42, 52, 56] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem blocked_691 : (families2.any (fun ms => checkedAssignment ms [25, 42, 52, 56])) = false := by
  simp only [families2,List.any_cons,List.any_nil,noMatch_691_3,Bool.or_false]
  decide +kernel

theorem noMatch_693_3 : checkedAssignment [21, 22, 25, 26] [21, 42, 52, 56] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem blocked_693 : (families2.any (fun ms => checkedAssignment ms [21, 42, 52, 56])) = false := by
  simp only [families2,List.any_cons,List.any_nil,noMatch_693_3,Bool.or_false]
  decide +kernel

theorem noMatch_695_3 : checkedAssignment [21, 22, 25, 26] [17, 42, 52, 56] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem blocked_695 : (families2.any (fun ms => checkedAssignment ms [17, 42, 52, 56])) = false := by
  simp only [families2,List.any_cons,List.any_nil,noMatch_695_3,Bool.or_false]
  decide +kernel

theorem noMatch_701_3 : checkedAssignment [21, 22, 25, 26] [5, 42, 52, 56] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem blocked_701 : (families2.any (fun ms => checkedAssignment ms [5, 42, 52, 56])) = false := by
  simp only [families2,List.any_cons,List.any_nil,noMatch_701_3,Bool.or_false]
  decide +kernel

theorem noMatch_703_3 : checkedAssignment [21, 22, 25, 26] [1, 42, 52, 56] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem blocked_703 : (families2.any (fun ms => checkedAssignment ms [1, 42, 52, 56])) = false := by
  simp only [families2,List.any_cons,List.any_nil,noMatch_703_3,Bool.or_false]
  decide +kernel

theorem noMatch_759_3 : checkedAssignment [21, 22, 25, 26] [17, 34, 52, 56] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem blocked_759 : (families2.any (fun ms => checkedAssignment ms [17, 34, 52, 56])) = false := by
  simp only [families2,List.any_cons,List.any_nil,noMatch_759_3,Bool.or_false]
  decide +kernel

theorem noMatch_763_3 : checkedAssignment [21, 22, 25, 26] [9, 34, 52, 56] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem blocked_763 : (families2.any (fun ms => checkedAssignment ms [9, 34, 52, 56])) = false := by
  simp only [families2,List.any_cons,List.any_nil,noMatch_763_3,Bool.or_false]
  decide +kernel

theorem noMatch_766_3 : checkedAssignment [21, 22, 25, 26] [3, 34, 52, 56] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem blocked_766 : (families2.any (fun ms => checkedAssignment ms [3, 34, 52, 56])) = false := by
  simp only [families2,List.any_cons,List.any_nil,noMatch_766_3,Bool.or_false]
  decide +kernel

theorem noMatch_767_3 : checkedAssignment [21, 22, 25, 26] [1, 34, 52, 56] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem blocked_767 : (families2.any (fun ms => checkedAssignment ms [1, 34, 52, 56])) = false := by
  simp only [families2,List.any_cons,List.any_nil,noMatch_767_3,Bool.or_false]
  decide +kernel

theorem noMatch_955_3 : checkedAssignment [21, 22, 25, 26] [9, 10, 52, 56] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem blocked_955 : (families2.any (fun ms => checkedAssignment ms [9, 10, 52, 56])) = false := by
  simp only [families2,List.any_cons,List.any_nil,noMatch_955_3,Bool.or_false]
  decide +kernel

theorem noMatch_1783_3 : checkedAssignment [21, 22, 25, 26] [17, 34, 36, 56] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem blocked_1783 : (families2.any (fun ms => checkedAssignment ms [17, 34, 36, 56])) = false := by
  simp only [families2,List.any_cons,List.any_nil,noMatch_1783_3,Bool.or_false]
  decide +kernel

theorem noMatch_1789_3 : checkedAssignment [21, 22, 25, 26] [5, 34, 36, 56] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem blocked_1789 : (families2.any (fun ms => checkedAssignment ms [5, 34, 36, 56])) = false := by
  simp only [families2,List.any_cons,List.any_nil,noMatch_1789_3,Bool.or_false]
  decide +kernel

theorem noMatch_1791_3 : checkedAssignment [21, 22, 25, 26] [1, 34, 36, 56] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem blocked_1791 : (families2.any (fun ms => checkedAssignment ms [1, 34, 36, 56])) = false := by
  simp only [families2,List.any_cons,List.any_nil,noMatch_1791_3,Bool.or_false]
  decide +kernel

theorem noMatch_1915_3 : checkedAssignment [21, 22, 25, 26] [9, 18, 36, 56] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem blocked_1915 : (families2.any (fun ms => checkedAssignment ms [9, 18, 36, 56])) = false := by
  simp only [families2,List.any_cons,List.any_nil,noMatch_1915_3,Bool.or_false]
  decide +kernel

theorem noMatch_2013_3 : checkedAssignment [21, 22, 25, 26] [5, 6, 36, 56] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem blocked_2013 : (families2.any (fun ms => checkedAssignment ms [5, 6, 36, 56])) = false := by
  simp only [families2,List.any_cons,List.any_nil,noMatch_2013_3,Bool.or_false]
  decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5907_7_85 : canAssign [85, 86, 89, 90, 101, 102, 105, 106] [9, 10, 17, 18, 36, 40, 48] [(6,85)] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5907_7_86 : canAssign [85, 86, 89, 90, 101, 102, 105, 106] [9, 10, 17, 18, 36, 40, 48] [(6,86)] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5907_7_89 : canAssign [85, 86, 89, 90, 101, 102, 105, 106] [9, 10, 17, 18, 36, 40, 48] [(6,89)] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5907_7_90 : canAssign [85, 86, 89, 90, 101, 102, 105, 106] [9, 10, 17, 18, 36, 40, 48] [(6,90)] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5907_7_101 : canAssign [85, 86, 89, 90, 101, 102, 105, 106] [9, 10, 17, 18, 36, 40, 48] [(6,101)] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5907_7_102 : canAssign [85, 86, 89, 90, 101, 102, 105, 106] [9, 10, 17, 18, 36, 40, 48] [(6,102)] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5907_7_105 : canAssign [85, 86, 89, 90, 101, 102, 105, 106] [9, 10, 17, 18, 36, 40, 48] [(6,105)] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5907_7_106 : canAssign [85, 86, 89, 90, 101, 102, 105, 106] [9, 10, 17, 18, 36, 40, 48] [(6,106)] = false := by decide +kernel

theorem noMatch_5907_7 : checkedAssignment [85, 86, 89, 90, 101, 102, 105, 106] [6, 9, 10, 17, 18, 36, 40, 48] = false := by
  apply firstMasksFail
  simp only [List.any_cons,List.any_nil,noMatch_5907_7_85,noMatch_5907_7_86,noMatch_5907_7_89,noMatch_5907_7_90,noMatch_5907_7_101,noMatch_5907_7_102,noMatch_5907_7_105,noMatch_5907_7_106,Bool.or_false]

set_option maxHeartbeats 0 in
theorem blocked_5907 : (families3.any (fun ms => checkedAssignment ms [6, 9, 10, 17, 18, 36, 40, 48])) = false := by
  simp only [families3,List.any_cons,List.any_nil,noMatch_5907_7,Bool.false_or,Bool.or_false]
  decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5911_7_85 : canAssign [85, 86, 89, 90, 101, 102, 105, 106] [10, 17, 18, 36, 40, 48] [(6,85)] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5911_7_86 : canAssign [85, 86, 89, 90, 101, 102, 105, 106] [10, 17, 18, 36, 40, 48] [(6,86)] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5911_7_89 : canAssign [85, 86, 89, 90, 101, 102, 105, 106] [10, 17, 18, 36, 40, 48] [(6,89)] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5911_7_90 : canAssign [85, 86, 89, 90, 101, 102, 105, 106] [10, 17, 18, 36, 40, 48] [(6,90)] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5911_7_101 : canAssign [85, 86, 89, 90, 101, 102, 105, 106] [10, 17, 18, 36, 40, 48] [(6,101)] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5911_7_102 : canAssign [85, 86, 89, 90, 101, 102, 105, 106] [10, 17, 18, 36, 40, 48] [(6,102)] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5911_7_105 : canAssign [85, 86, 89, 90, 101, 102, 105, 106] [10, 17, 18, 36, 40, 48] [(6,105)] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5911_7_106 : canAssign [85, 86, 89, 90, 101, 102, 105, 106] [10, 17, 18, 36, 40, 48] [(6,106)] = false := by decide +kernel

theorem noMatch_5911_7 : checkedAssignment [85, 86, 89, 90, 101, 102, 105, 106] [6, 10, 17, 18, 36, 40, 48] = false := by
  apply firstMasksFail
  simp only [List.any_cons,List.any_nil,noMatch_5911_7_85,noMatch_5911_7_86,noMatch_5911_7_89,noMatch_5911_7_90,noMatch_5911_7_101,noMatch_5911_7_102,noMatch_5911_7_105,noMatch_5911_7_106,Bool.or_false]

set_option maxHeartbeats 0 in
theorem noMatch_5911_22_84 : canAssign [84, 89, 90, 101, 102, 105, 106] [10, 17, 18, 36, 40, 48] [(6,84)] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5911_22_89 : canAssign [84, 89, 90, 101, 102, 105, 106] [10, 17, 18, 36, 40, 48] [(6,89)] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5911_22_90 : canAssign [84, 89, 90, 101, 102, 105, 106] [10, 17, 18, 36, 40, 48] [(6,90)] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5911_22_101 : canAssign [84, 89, 90, 101, 102, 105, 106] [10, 17, 18, 36, 40, 48] [(6,101)] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5911_22_102 : canAssign [84, 89, 90, 101, 102, 105, 106] [10, 17, 18, 36, 40, 48] [(6,102)] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5911_22_105 : canAssign [84, 89, 90, 101, 102, 105, 106] [10, 17, 18, 36, 40, 48] [(6,105)] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5911_22_106 : canAssign [84, 89, 90, 101, 102, 105, 106] [10, 17, 18, 36, 40, 48] [(6,106)] = false := by decide +kernel

theorem noMatch_5911_22 : checkedAssignment [84, 89, 90, 101, 102, 105, 106] [6, 10, 17, 18, 36, 40, 48] = false := by
  apply firstMasksFail
  simp only [List.any_cons,List.any_nil,noMatch_5911_22_84,noMatch_5911_22_89,noMatch_5911_22_90,noMatch_5911_22_101,noMatch_5911_22_102,noMatch_5911_22_105,noMatch_5911_22_106,Bool.or_false]

set_option maxHeartbeats 0 in
theorem noMatch_5911_24_85 : canAssign [85, 86, 89, 90, 100, 105, 106] [10, 17, 18, 36, 40, 48] [(6,85)] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5911_24_86 : canAssign [85, 86, 89, 90, 100, 105, 106] [10, 17, 18, 36, 40, 48] [(6,86)] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5911_24_89 : canAssign [85, 86, 89, 90, 100, 105, 106] [10, 17, 18, 36, 40, 48] [(6,89)] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5911_24_90 : canAssign [85, 86, 89, 90, 100, 105, 106] [10, 17, 18, 36, 40, 48] [(6,90)] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5911_24_100 : canAssign [85, 86, 89, 90, 100, 105, 106] [10, 17, 18, 36, 40, 48] [(6,100)] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5911_24_105 : canAssign [85, 86, 89, 90, 100, 105, 106] [10, 17, 18, 36, 40, 48] [(6,105)] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5911_24_106 : canAssign [85, 86, 89, 90, 100, 105, 106] [10, 17, 18, 36, 40, 48] [(6,106)] = false := by decide +kernel

theorem noMatch_5911_24 : checkedAssignment [85, 86, 89, 90, 100, 105, 106] [6, 10, 17, 18, 36, 40, 48] = false := by
  apply firstMasksFail
  simp only [List.any_cons,List.any_nil,noMatch_5911_24_85,noMatch_5911_24_86,noMatch_5911_24_89,noMatch_5911_24_90,noMatch_5911_24_100,noMatch_5911_24_105,noMatch_5911_24_106,Bool.or_false]

set_option maxHeartbeats 0 in
theorem noMatch_5911_30_85 : canAssign [85, 86, 88, 101, 102, 105, 106] [10, 17, 18, 36, 40, 48] [(6,85)] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5911_30_86 : canAssign [85, 86, 88, 101, 102, 105, 106] [10, 17, 18, 36, 40, 48] [(6,86)] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5911_30_88 : canAssign [85, 86, 88, 101, 102, 105, 106] [10, 17, 18, 36, 40, 48] [(6,88)] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5911_30_101 : canAssign [85, 86, 88, 101, 102, 105, 106] [10, 17, 18, 36, 40, 48] [(6,101)] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5911_30_102 : canAssign [85, 86, 88, 101, 102, 105, 106] [10, 17, 18, 36, 40, 48] [(6,102)] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5911_30_105 : canAssign [85, 86, 88, 101, 102, 105, 106] [10, 17, 18, 36, 40, 48] [(6,105)] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5911_30_106 : canAssign [85, 86, 88, 101, 102, 105, 106] [10, 17, 18, 36, 40, 48] [(6,106)] = false := by decide +kernel

theorem noMatch_5911_30 : checkedAssignment [85, 86, 88, 101, 102, 105, 106] [6, 10, 17, 18, 36, 40, 48] = false := by
  apply firstMasksFail
  simp only [List.any_cons,List.any_nil,noMatch_5911_30_85,noMatch_5911_30_86,noMatch_5911_30_88,noMatch_5911_30_101,noMatch_5911_30_102,noMatch_5911_30_105,noMatch_5911_30_106,Bool.or_false]

set_option maxHeartbeats 0 in
theorem noMatch_5911_32_85 : canAssign [85, 86, 89, 90, 101, 102, 104] [10, 17, 18, 36, 40, 48] [(6,85)] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5911_32_86 : canAssign [85, 86, 89, 90, 101, 102, 104] [10, 17, 18, 36, 40, 48] [(6,86)] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5911_32_89 : canAssign [85, 86, 89, 90, 101, 102, 104] [10, 17, 18, 36, 40, 48] [(6,89)] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5911_32_90 : canAssign [85, 86, 89, 90, 101, 102, 104] [10, 17, 18, 36, 40, 48] [(6,90)] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5911_32_101 : canAssign [85, 86, 89, 90, 101, 102, 104] [10, 17, 18, 36, 40, 48] [(6,101)] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5911_32_102 : canAssign [85, 86, 89, 90, 101, 102, 104] [10, 17, 18, 36, 40, 48] [(6,102)] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5911_32_104 : canAssign [85, 86, 89, 90, 101, 102, 104] [10, 17, 18, 36, 40, 48] [(6,104)] = false := by decide +kernel

theorem noMatch_5911_32 : checkedAssignment [85, 86, 89, 90, 101, 102, 104] [6, 10, 17, 18, 36, 40, 48] = false := by
  apply firstMasksFail
  simp only [List.any_cons,List.any_nil,noMatch_5911_32_85,noMatch_5911_32_86,noMatch_5911_32_89,noMatch_5911_32_90,noMatch_5911_32_101,noMatch_5911_32_102,noMatch_5911_32_104,Bool.or_false]

set_option maxHeartbeats 0 in
theorem blocked_5911 : (families3.any (fun ms => checkedAssignment ms [6, 10, 17, 18, 36, 40, 48])) = false := by
  simp only [families3,List.any_cons,List.any_nil,noMatch_5911_7,noMatch_5911_22,noMatch_5911_24,noMatch_5911_30,noMatch_5911_32,Bool.false_or,Bool.or_false]
  decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5919_7_85 : canAssign [85, 86, 89, 90, 101, 102, 105, 106] [6, 10, 18, 36, 40, 48] [(1,85)] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5919_7_86 : canAssign [85, 86, 89, 90, 101, 102, 105, 106] [6, 10, 18, 36, 40, 48] [(1,86)] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5919_7_89 : canAssign [85, 86, 89, 90, 101, 102, 105, 106] [6, 10, 18, 36, 40, 48] [(1,89)] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5919_7_90 : canAssign [85, 86, 89, 90, 101, 102, 105, 106] [6, 10, 18, 36, 40, 48] [(1,90)] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5919_7_101 : canAssign [85, 86, 89, 90, 101, 102, 105, 106] [6, 10, 18, 36, 40, 48] [(1,101)] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5919_7_102 : canAssign [85, 86, 89, 90, 101, 102, 105, 106] [6, 10, 18, 36, 40, 48] [(1,102)] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5919_7_105 : canAssign [85, 86, 89, 90, 101, 102, 105, 106] [6, 10, 18, 36, 40, 48] [(1,105)] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5919_7_106 : canAssign [85, 86, 89, 90, 101, 102, 105, 106] [6, 10, 18, 36, 40, 48] [(1,106)] = false := by decide +kernel

theorem noMatch_5919_7 : checkedAssignment [85, 86, 89, 90, 101, 102, 105, 106] [1, 6, 10, 18, 36, 40, 48] = false := by
  apply firstMasksFail
  simp only [List.any_cons,List.any_nil,noMatch_5919_7_85,noMatch_5919_7_86,noMatch_5919_7_89,noMatch_5919_7_90,noMatch_5919_7_101,noMatch_5919_7_102,noMatch_5919_7_105,noMatch_5919_7_106,Bool.or_false]

set_option maxHeartbeats 0 in
theorem noMatch_5919_22_84 : canAssign [84, 89, 90, 101, 102, 105, 106] [6, 10, 18, 36, 40, 48] [(1,84)] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5919_22_89 : canAssign [84, 89, 90, 101, 102, 105, 106] [6, 10, 18, 36, 40, 48] [(1,89)] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5919_22_90 : canAssign [84, 89, 90, 101, 102, 105, 106] [6, 10, 18, 36, 40, 48] [(1,90)] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5919_22_101 : canAssign [84, 89, 90, 101, 102, 105, 106] [6, 10, 18, 36, 40, 48] [(1,101)] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5919_22_102 : canAssign [84, 89, 90, 101, 102, 105, 106] [6, 10, 18, 36, 40, 48] [(1,102)] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5919_22_105 : canAssign [84, 89, 90, 101, 102, 105, 106] [6, 10, 18, 36, 40, 48] [(1,105)] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5919_22_106 : canAssign [84, 89, 90, 101, 102, 105, 106] [6, 10, 18, 36, 40, 48] [(1,106)] = false := by decide +kernel

theorem noMatch_5919_22 : checkedAssignment [84, 89, 90, 101, 102, 105, 106] [1, 6, 10, 18, 36, 40, 48] = false := by
  apply firstMasksFail
  simp only [List.any_cons,List.any_nil,noMatch_5919_22_84,noMatch_5919_22_89,noMatch_5919_22_90,noMatch_5919_22_101,noMatch_5919_22_102,noMatch_5919_22_105,noMatch_5919_22_106,Bool.or_false]

set_option maxHeartbeats 0 in
theorem noMatch_5919_24_85 : canAssign [85, 86, 89, 90, 100, 105, 106] [6, 10, 18, 36, 40, 48] [(1,85)] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5919_24_86 : canAssign [85, 86, 89, 90, 100, 105, 106] [6, 10, 18, 36, 40, 48] [(1,86)] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5919_24_89 : canAssign [85, 86, 89, 90, 100, 105, 106] [6, 10, 18, 36, 40, 48] [(1,89)] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5919_24_90 : canAssign [85, 86, 89, 90, 100, 105, 106] [6, 10, 18, 36, 40, 48] [(1,90)] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5919_24_100 : canAssign [85, 86, 89, 90, 100, 105, 106] [6, 10, 18, 36, 40, 48] [(1,100)] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5919_24_105 : canAssign [85, 86, 89, 90, 100, 105, 106] [6, 10, 18, 36, 40, 48] [(1,105)] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5919_24_106 : canAssign [85, 86, 89, 90, 100, 105, 106] [6, 10, 18, 36, 40, 48] [(1,106)] = false := by decide +kernel

theorem noMatch_5919_24 : checkedAssignment [85, 86, 89, 90, 100, 105, 106] [1, 6, 10, 18, 36, 40, 48] = false := by
  apply firstMasksFail
  simp only [List.any_cons,List.any_nil,noMatch_5919_24_85,noMatch_5919_24_86,noMatch_5919_24_89,noMatch_5919_24_90,noMatch_5919_24_100,noMatch_5919_24_105,noMatch_5919_24_106,Bool.or_false]

set_option maxHeartbeats 0 in
theorem noMatch_5919_30_85 : canAssign [85, 86, 88, 101, 102, 105, 106] [6, 10, 18, 36, 40, 48] [(1,85)] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5919_30_86 : canAssign [85, 86, 88, 101, 102, 105, 106] [6, 10, 18, 36, 40, 48] [(1,86)] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5919_30_88 : canAssign [85, 86, 88, 101, 102, 105, 106] [6, 10, 18, 36, 40, 48] [(1,88)] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5919_30_101 : canAssign [85, 86, 88, 101, 102, 105, 106] [6, 10, 18, 36, 40, 48] [(1,101)] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5919_30_102 : canAssign [85, 86, 88, 101, 102, 105, 106] [6, 10, 18, 36, 40, 48] [(1,102)] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5919_30_105 : canAssign [85, 86, 88, 101, 102, 105, 106] [6, 10, 18, 36, 40, 48] [(1,105)] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5919_30_106 : canAssign [85, 86, 88, 101, 102, 105, 106] [6, 10, 18, 36, 40, 48] [(1,106)] = false := by decide +kernel

theorem noMatch_5919_30 : checkedAssignment [85, 86, 88, 101, 102, 105, 106] [1, 6, 10, 18, 36, 40, 48] = false := by
  apply firstMasksFail
  simp only [List.any_cons,List.any_nil,noMatch_5919_30_85,noMatch_5919_30_86,noMatch_5919_30_88,noMatch_5919_30_101,noMatch_5919_30_102,noMatch_5919_30_105,noMatch_5919_30_106,Bool.or_false]

set_option maxHeartbeats 0 in
theorem noMatch_5919_32_85 : canAssign [85, 86, 89, 90, 101, 102, 104] [6, 10, 18, 36, 40, 48] [(1,85)] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5919_32_86 : canAssign [85, 86, 89, 90, 101, 102, 104] [6, 10, 18, 36, 40, 48] [(1,86)] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5919_32_89 : canAssign [85, 86, 89, 90, 101, 102, 104] [6, 10, 18, 36, 40, 48] [(1,89)] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5919_32_90 : canAssign [85, 86, 89, 90, 101, 102, 104] [6, 10, 18, 36, 40, 48] [(1,90)] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5919_32_101 : canAssign [85, 86, 89, 90, 101, 102, 104] [6, 10, 18, 36, 40, 48] [(1,101)] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5919_32_102 : canAssign [85, 86, 89, 90, 101, 102, 104] [6, 10, 18, 36, 40, 48] [(1,102)] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5919_32_104 : canAssign [85, 86, 89, 90, 101, 102, 104] [6, 10, 18, 36, 40, 48] [(1,104)] = false := by decide +kernel

theorem noMatch_5919_32 : checkedAssignment [85, 86, 89, 90, 101, 102, 104] [1, 6, 10, 18, 36, 40, 48] = false := by
  apply firstMasksFail
  simp only [List.any_cons,List.any_nil,noMatch_5919_32_85,noMatch_5919_32_86,noMatch_5919_32_89,noMatch_5919_32_90,noMatch_5919_32_101,noMatch_5919_32_102,noMatch_5919_32_104,Bool.or_false]

set_option maxHeartbeats 0 in
theorem blocked_5919 : (families3.any (fun ms => checkedAssignment ms [1, 6, 10, 18, 36, 40, 48])) = false := by
  simp only [families3,List.any_cons,List.any_nil,noMatch_5919_7,noMatch_5919_22,noMatch_5919_24,noMatch_5919_30,noMatch_5919_32,Bool.false_or,Bool.or_false]
  decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5948_7_85 : canAssign [85, 86, 89, 90, 101, 102, 105, 106] [5, 10, 18, 36, 40, 48] [(3,85)] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5948_7_86 : canAssign [85, 86, 89, 90, 101, 102, 105, 106] [5, 10, 18, 36, 40, 48] [(3,86)] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5948_7_89 : canAssign [85, 86, 89, 90, 101, 102, 105, 106] [5, 10, 18, 36, 40, 48] [(3,89)] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5948_7_90 : canAssign [85, 86, 89, 90, 101, 102, 105, 106] [5, 10, 18, 36, 40, 48] [(3,90)] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5948_7_101 : canAssign [85, 86, 89, 90, 101, 102, 105, 106] [5, 10, 18, 36, 40, 48] [(3,101)] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5948_7_102 : canAssign [85, 86, 89, 90, 101, 102, 105, 106] [5, 10, 18, 36, 40, 48] [(3,102)] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5948_7_105 : canAssign [85, 86, 89, 90, 101, 102, 105, 106] [5, 10, 18, 36, 40, 48] [(3,105)] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5948_7_106 : canAssign [85, 86, 89, 90, 101, 102, 105, 106] [5, 10, 18, 36, 40, 48] [(3,106)] = false := by decide +kernel

theorem noMatch_5948_7 : checkedAssignment [85, 86, 89, 90, 101, 102, 105, 106] [3, 5, 10, 18, 36, 40, 48] = false := by
  apply firstMasksFail
  simp only [List.any_cons,List.any_nil,noMatch_5948_7_85,noMatch_5948_7_86,noMatch_5948_7_89,noMatch_5948_7_90,noMatch_5948_7_101,noMatch_5948_7_102,noMatch_5948_7_105,noMatch_5948_7_106,Bool.or_false]

set_option maxHeartbeats 0 in
theorem noMatch_5948_22_84 : canAssign [84, 89, 90, 101, 102, 105, 106] [5, 10, 18, 36, 40, 48] [(3,84)] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5948_22_89 : canAssign [84, 89, 90, 101, 102, 105, 106] [5, 10, 18, 36, 40, 48] [(3,89)] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5948_22_90 : canAssign [84, 89, 90, 101, 102, 105, 106] [5, 10, 18, 36, 40, 48] [(3,90)] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5948_22_101 : canAssign [84, 89, 90, 101, 102, 105, 106] [5, 10, 18, 36, 40, 48] [(3,101)] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5948_22_102 : canAssign [84, 89, 90, 101, 102, 105, 106] [5, 10, 18, 36, 40, 48] [(3,102)] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5948_22_105 : canAssign [84, 89, 90, 101, 102, 105, 106] [5, 10, 18, 36, 40, 48] [(3,105)] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5948_22_106 : canAssign [84, 89, 90, 101, 102, 105, 106] [5, 10, 18, 36, 40, 48] [(3,106)] = false := by decide +kernel

theorem noMatch_5948_22 : checkedAssignment [84, 89, 90, 101, 102, 105, 106] [3, 5, 10, 18, 36, 40, 48] = false := by
  apply firstMasksFail
  simp only [List.any_cons,List.any_nil,noMatch_5948_22_84,noMatch_5948_22_89,noMatch_5948_22_90,noMatch_5948_22_101,noMatch_5948_22_102,noMatch_5948_22_105,noMatch_5948_22_106,Bool.or_false]

set_option maxHeartbeats 0 in
theorem noMatch_5948_24_85 : canAssign [85, 86, 89, 90, 100, 105, 106] [5, 10, 18, 36, 40, 48] [(3,85)] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5948_24_86 : canAssign [85, 86, 89, 90, 100, 105, 106] [5, 10, 18, 36, 40, 48] [(3,86)] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5948_24_89 : canAssign [85, 86, 89, 90, 100, 105, 106] [5, 10, 18, 36, 40, 48] [(3,89)] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5948_24_90 : canAssign [85, 86, 89, 90, 100, 105, 106] [5, 10, 18, 36, 40, 48] [(3,90)] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5948_24_100 : canAssign [85, 86, 89, 90, 100, 105, 106] [5, 10, 18, 36, 40, 48] [(3,100)] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5948_24_105 : canAssign [85, 86, 89, 90, 100, 105, 106] [5, 10, 18, 36, 40, 48] [(3,105)] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5948_24_106 : canAssign [85, 86, 89, 90, 100, 105, 106] [5, 10, 18, 36, 40, 48] [(3,106)] = false := by decide +kernel

theorem noMatch_5948_24 : checkedAssignment [85, 86, 89, 90, 100, 105, 106] [3, 5, 10, 18, 36, 40, 48] = false := by
  apply firstMasksFail
  simp only [List.any_cons,List.any_nil,noMatch_5948_24_85,noMatch_5948_24_86,noMatch_5948_24_89,noMatch_5948_24_90,noMatch_5948_24_100,noMatch_5948_24_105,noMatch_5948_24_106,Bool.or_false]

set_option maxHeartbeats 0 in
theorem noMatch_5948_30_85 : canAssign [85, 86, 88, 101, 102, 105, 106] [5, 10, 18, 36, 40, 48] [(3,85)] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5948_30_86 : canAssign [85, 86, 88, 101, 102, 105, 106] [5, 10, 18, 36, 40, 48] [(3,86)] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5948_30_88 : canAssign [85, 86, 88, 101, 102, 105, 106] [5, 10, 18, 36, 40, 48] [(3,88)] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5948_30_101 : canAssign [85, 86, 88, 101, 102, 105, 106] [5, 10, 18, 36, 40, 48] [(3,101)] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5948_30_102 : canAssign [85, 86, 88, 101, 102, 105, 106] [5, 10, 18, 36, 40, 48] [(3,102)] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5948_30_105 : canAssign [85, 86, 88, 101, 102, 105, 106] [5, 10, 18, 36, 40, 48] [(3,105)] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5948_30_106 : canAssign [85, 86, 88, 101, 102, 105, 106] [5, 10, 18, 36, 40, 48] [(3,106)] = false := by decide +kernel

theorem noMatch_5948_30 : checkedAssignment [85, 86, 88, 101, 102, 105, 106] [3, 5, 10, 18, 36, 40, 48] = false := by
  apply firstMasksFail
  simp only [List.any_cons,List.any_nil,noMatch_5948_30_85,noMatch_5948_30_86,noMatch_5948_30_88,noMatch_5948_30_101,noMatch_5948_30_102,noMatch_5948_30_105,noMatch_5948_30_106,Bool.or_false]

set_option maxHeartbeats 0 in
theorem noMatch_5948_32_85 : canAssign [85, 86, 89, 90, 101, 102, 104] [5, 10, 18, 36, 40, 48] [(3,85)] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5948_32_86 : canAssign [85, 86, 89, 90, 101, 102, 104] [5, 10, 18, 36, 40, 48] [(3,86)] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5948_32_89 : canAssign [85, 86, 89, 90, 101, 102, 104] [5, 10, 18, 36, 40, 48] [(3,89)] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5948_32_90 : canAssign [85, 86, 89, 90, 101, 102, 104] [5, 10, 18, 36, 40, 48] [(3,90)] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5948_32_101 : canAssign [85, 86, 89, 90, 101, 102, 104] [5, 10, 18, 36, 40, 48] [(3,101)] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5948_32_102 : canAssign [85, 86, 89, 90, 101, 102, 104] [5, 10, 18, 36, 40, 48] [(3,102)] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem noMatch_5948_32_104 : canAssign [85, 86, 89, 90, 101, 102, 104] [5, 10, 18, 36, 40, 48] [(3,104)] = false := by decide +kernel

theorem noMatch_5948_32 : checkedAssignment [85, 86, 89, 90, 101, 102, 104] [3, 5, 10, 18, 36, 40, 48] = false := by
  apply firstMasksFail
  simp only [List.any_cons,List.any_nil,noMatch_5948_32_85,noMatch_5948_32_86,noMatch_5948_32_89,noMatch_5948_32_90,noMatch_5948_32_101,noMatch_5948_32_102,noMatch_5948_32_104,Bool.or_false]

set_option maxHeartbeats 0 in
theorem blocked_5948 : (families3.any (fun ms => checkedAssignment ms [3, 5, 10, 18, 36, 40, 48])) = false := by
  simp only [families3,List.any_cons,List.any_nil,noMatch_5948_7,noMatch_5948_22,noMatch_5948_24,noMatch_5948_30,noMatch_5948_32,Bool.false_or,Bool.or_false]
  decide +kernel

theorem noMatch_6142_3 : checkedAssignment [21, 22, 25, 26] [3, 36, 40, 48] = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem blocked_6142 : (families2.any (fun ms => checkedAssignment ms [3, 36, 40, 48])) = false := by
  simp only [families2,List.any_cons,List.any_nil,noMatch_6142_3,Bool.or_false]
  decide +kernel

open PEqualNP.AndCount

set_option maxHeartbeats 0 in
theorem hard_619 (C : AndCountCircuit 6) (_wf : C.WellFormed) (fit : Fits 619 C) : 3 ≤ C.size := by
  have low := count_619 C fit
  by_contra! h
  exact orientImpossible2 619 [41, 50, 52, 56] C fit (by omega) (by decide +kernel) (by decide +kernel) blocked_619

set_option maxHeartbeats 0 in
theorem hard_623 (C : AndCountCircuit 6) (_wf : C.WellFormed) (fit : Fits 623 C) : 3 ≤ C.size := by
  have low := count_623 C fit
  by_contra! h
  exact orientImpossible2 623 [33, 50, 52, 56] C fit (by omega) (by decide +kernel) (by decide +kernel) blocked_623

set_option maxHeartbeats 0 in
theorem hard_635 (C : AndCountCircuit 6) (_wf : C.WellFormed) (fit : Fits 635 C) : 3 ≤ C.size := by
  have low := count_635 C fit
  by_contra! h
  exact orientImpossible2 635 [9, 50, 52, 56] C fit (by omega) (by decide +kernel) (by decide +kernel) blocked_635

set_option maxHeartbeats 0 in
theorem hard_639 (C : AndCountCircuit 6) (_wf : C.WellFormed) (fit : Fits 639 C) : 3 ≤ C.size := by
  have low := count_639 C fit
  by_contra! h
  exact orientImpossible2 639 [1, 50, 52, 56] C fit (by omega) (by decide +kernel) (by decide +kernel) blocked_639

set_option maxHeartbeats 0 in
theorem hard_691 (C : AndCountCircuit 6) (_wf : C.WellFormed) (fit : Fits 691 C) : 3 ≤ C.size := by
  have low := count_691 C fit
  by_contra! h
  exact orientImpossible2 691 [25, 42, 52, 56] C fit (by omega) (by decide +kernel) (by decide +kernel) blocked_691

set_option maxHeartbeats 0 in
theorem hard_693 (C : AndCountCircuit 6) (_wf : C.WellFormed) (fit : Fits 693 C) : 3 ≤ C.size := by
  have low := count_693 C fit
  by_contra! h
  exact orientImpossible2 693 [21, 42, 52, 56] C fit (by omega) (by decide +kernel) (by decide +kernel) blocked_693

set_option maxHeartbeats 0 in
theorem hard_695 (C : AndCountCircuit 6) (_wf : C.WellFormed) (fit : Fits 695 C) : 3 ≤ C.size := by
  have low := count_695 C fit
  by_contra! h
  exact orientImpossible2 695 [17, 42, 52, 56] C fit (by omega) (by decide +kernel) (by decide +kernel) blocked_695

set_option maxHeartbeats 0 in
theorem hard_701 (C : AndCountCircuit 6) (_wf : C.WellFormed) (fit : Fits 701 C) : 3 ≤ C.size := by
  have low := count_701 C fit
  by_contra! h
  exact orientImpossible2 701 [5, 42, 52, 56] C fit (by omega) (by decide +kernel) (by decide +kernel) blocked_701

set_option maxHeartbeats 0 in
theorem hard_703 (C : AndCountCircuit 6) (_wf : C.WellFormed) (fit : Fits 703 C) : 3 ≤ C.size := by
  have low := count_703 C fit
  by_contra! h
  exact orientImpossible2 703 [1, 42, 52, 56] C fit (by omega) (by decide +kernel) (by decide +kernel) blocked_703

set_option maxHeartbeats 0 in
theorem hard_759 (C : AndCountCircuit 6) (_wf : C.WellFormed) (fit : Fits 759 C) : 3 ≤ C.size := by
  have low := count_759 C fit
  by_contra! h
  exact orientImpossible2 759 [17, 34, 52, 56] C fit (by omega) (by decide +kernel) (by decide +kernel) blocked_759

set_option maxHeartbeats 0 in
theorem hard_763 (C : AndCountCircuit 6) (_wf : C.WellFormed) (fit : Fits 763 C) : 3 ≤ C.size := by
  have low := count_763 C fit
  by_contra! h
  exact orientImpossible2 763 [9, 34, 52, 56] C fit (by omega) (by decide +kernel) (by decide +kernel) blocked_763

set_option maxHeartbeats 0 in
theorem hard_766 (C : AndCountCircuit 6) (_wf : C.WellFormed) (fit : Fits 766 C) : 3 ≤ C.size := by
  have low := count_766 C fit
  by_contra! h
  exact orientImpossible2 766 [3, 34, 52, 56] C fit (by omega) (by decide +kernel) (by decide +kernel) blocked_766

set_option maxHeartbeats 0 in
theorem hard_767 (C : AndCountCircuit 6) (_wf : C.WellFormed) (fit : Fits 767 C) : 3 ≤ C.size := by
  have low := count_767 C fit
  by_contra! h
  exact orientImpossible2 767 [1, 34, 52, 56] C fit (by omega) (by decide +kernel) (by decide +kernel) blocked_767

set_option maxHeartbeats 0 in
theorem hard_955 (C : AndCountCircuit 6) (_wf : C.WellFormed) (fit : Fits 955 C) : 3 ≤ C.size := by
  have low := count_955 C fit
  by_contra! h
  exact orientImpossible2 955 [9, 10, 52, 56] C fit (by omega) (by decide +kernel) (by decide +kernel) blocked_955

set_option maxHeartbeats 0 in
theorem hard_1783 (C : AndCountCircuit 6) (_wf : C.WellFormed) (fit : Fits 1783 C) : 3 ≤ C.size := by
  have low := count_1783 C fit
  by_contra! h
  exact orientImpossible2 1783 [17, 34, 36, 56] C fit (by omega) (by decide +kernel) (by decide +kernel) blocked_1783

set_option maxHeartbeats 0 in
theorem hard_1789 (C : AndCountCircuit 6) (_wf : C.WellFormed) (fit : Fits 1789 C) : 3 ≤ C.size := by
  have low := count_1789 C fit
  by_contra! h
  exact orientImpossible2 1789 [5, 34, 36, 56] C fit (by omega) (by decide +kernel) (by decide +kernel) blocked_1789

set_option maxHeartbeats 0 in
theorem hard_1791 (C : AndCountCircuit 6) (_wf : C.WellFormed) (fit : Fits 1791 C) : 3 ≤ C.size := by
  have low := count_1791 C fit
  by_contra! h
  exact orientImpossible2 1791 [1, 34, 36, 56] C fit (by omega) (by decide +kernel) (by decide +kernel) blocked_1791

set_option maxHeartbeats 0 in
theorem hard_1915 (C : AndCountCircuit 6) (_wf : C.WellFormed) (fit : Fits 1915 C) : 3 ≤ C.size := by
  have low := count_1915 C fit
  by_contra! h
  exact orientImpossible2 1915 [9, 18, 36, 56] C fit (by omega) (by decide +kernel) (by decide +kernel) blocked_1915

set_option maxHeartbeats 0 in
theorem hard_2013 (C : AndCountCircuit 6) (_wf : C.WellFormed) (fit : Fits 2013 C) : 3 ≤ C.size := by
  have low := count_2013 C fit
  by_contra! h
  exact orientImpossible2 2013 [5, 6, 36, 56] C fit (by omega) (by decide +kernel) (by decide +kernel) blocked_2013

set_option maxHeartbeats 0 in
theorem hard_5907 (C : AndCountCircuit 6) (_wf : C.WellFormed) (fit : Fits 5907 C) : 4 ≤ C.size := by
  have low := count_5907 C fit
  by_contra! h
  exact orientImpossible3 5907 [6, 9, 10, 17, 18, 36, 40, 48] C fit (by omega) (by decide +kernel) (by decide +kernel) blocked_5907

set_option maxHeartbeats 0 in
theorem hard_5911 (C : AndCountCircuit 6) (_wf : C.WellFormed) (fit : Fits 5911 C) : 4 ≤ C.size := by
  have low := count_5911 C fit
  by_contra! h
  exact orientImpossible3 5911 [6, 10, 17, 18, 36, 40, 48] C fit (by omega) (by decide +kernel) (by decide +kernel) blocked_5911

set_option maxHeartbeats 0 in
theorem hard_5919 (C : AndCountCircuit 6) (_wf : C.WellFormed) (fit : Fits 5919 C) : 4 ≤ C.size := by
  have low := count_5919 C fit
  by_contra! h
  exact orientImpossible3 5919 [1, 6, 10, 18, 36, 40, 48] C fit (by omega) (by decide +kernel) (by decide +kernel) blocked_5919

set_option maxHeartbeats 0 in
theorem hard_5948 (C : AndCountCircuit 6) (_wf : C.WellFormed) (fit : Fits 5948 C) : 4 ≤ C.size := by
  have low := count_5948 C fit
  by_contra! h
  exact orientImpossible3 5948 [3, 5, 10, 18, 36, 40, 48] C fit (by omega) (by decide +kernel) (by decide +kernel) blocked_5948

set_option maxHeartbeats 0 in
theorem hard_6142 (C : AndCountCircuit 6) (_wf : C.WellFormed) (fit : Fits 6142 C) : 3 ≤ C.size := by
  have low := count_6142 C fit
  by_contra! h
  exact orientImpossible2 6142 [3, 36, 40, 48] C fit (by omega) (by decide +kernel) (by decide +kernel) blocked_6142

open PEqualNP.AndCount

def repList : List Nat := [0,1,3,7,15,31,35,36,37,39,44,45,47,60,61,63,102,103,106,107,110,111,120,121,122,123,126,127,238,239,246,247,254,255,510,511,615,616,617,619,623,632,633,635,639,655,656,657,659,662,663,671,684,685,687,691,692,693,694,695,700,701,703,750,751,758,759,760,761,762,763,766,767,920,921,922,923,926,927,954,955,956,957,958,959,1022,1023,1743,1749,1751,1759,1775,1780,1781,1783,1788,1789,1791,1880,1881,1883,1884,1885,1887,1915,1916,1917,1919,2012,2013,2014,2015,2046,2047,4060,4061,4063,4095,5871,5872,5873,5875,5879,5887,5905,5907,5911,5919,5941,5943,5948,5949,5950,5951,6007,6010,6011,6014,6015,6142,6143,6654,6655,7071,7100,7101,7103,7166,7167,8157,8159,8191,15870,15871,16383,32767]

theorem cover_0 : Cover 0 0 := by
  refine ⟨Fin.elim0, Fin.elim0, ?_⟩
  decide +kernel

theorem cover_1 : Cover 1 1 := by
  refine ⟨![{1}], ![{0}], ?_⟩
  decide +kernel

theorem cover_3 : Cover 3 1 := by
  refine ⟨![{1, 2}], ![{0}], ?_⟩
  decide +kernel

theorem cover_7 : Cover 7 1 := by
  refine ⟨![{1, 2, 3}], ![{0}], ?_⟩
  decide +kernel

theorem cover_15 : Cover 15 1 := by
  refine ⟨![{1, 2, 3, 4}], ![{0}], ?_⟩
  decide +kernel

theorem cover_31 : Cover 31 1 := by
  refine ⟨![{1, 2, 3, 4, 5}], ![{0}], ?_⟩
  decide +kernel

theorem cover_35 : Cover 35 2 := by
  refine ⟨![{0, 2}, {2}], ![{1}, {0, 1}], ?_⟩
  decide +kernel

theorem cover_36 : Cover 36 2 := by
  refine ⟨![{3}, {2}], ![{0}, {1}], ?_⟩
  decide +kernel

theorem cover_37 : Cover 37 2 := by
  refine ⟨![{0, 2}, {1, 3}], ![{1}, {0}], ?_⟩
  decide +kernel

theorem cover_39 : Cover 39 2 := by
  refine ⟨![{0, 2}, {1, 2, 3}], ![{1}, {0}], ?_⟩
  decide +kernel

theorem cover_44 : Cover 44 2 := by
  refine ⟨![{3, 4}, {2}], ![{0}, {1}], ?_⟩
  decide +kernel

theorem cover_45 : Cover 45 2 := by
  refine ⟨![{0, 2}, {1, 3, 4}], ![{1}, {0}], ?_⟩
  decide +kernel

theorem cover_47 : Cover 47 2 := by
  refine ⟨![{0, 2}, {1, 2, 3, 4}], ![{1}, {0}], ?_⟩
  decide +kernel

theorem cover_60 : Cover 60 2 := by
  refine ⟨![{3, 4, 5}, {2}], ![{0}, {1}], ?_⟩
  decide +kernel

theorem cover_61 : Cover 61 2 := by
  refine ⟨![{0, 2}, {1, 3, 4, 5}], ![{1}, {0}], ?_⟩
  decide +kernel

theorem cover_63 : Cover 63 2 := by
  refine ⟨![{0, 2}, {1, 2, 3, 4, 5}], ![{1}, {0}], ?_⟩
  decide +kernel

theorem cover_102 : Cover 102 1 := by
  refine ⟨![{2, 3}], ![{0, 1}], ?_⟩
  decide +kernel

theorem cover_103 : Cover 103 2 := by
  refine ⟨![{0, 2, 3}, {2, 3}], ![{1}, {0, 1}], ?_⟩
  decide +kernel

theorem cover_106 : Cover 106 2 := by
  refine ⟨![{2, 4}, {2, 3}], ![{0}, {1}], ?_⟩
  decide +kernel

theorem cover_107 : Cover 107 2 := by
  refine ⟨![{0, 2, 3}, {1, 2, 4}], ![{1}, {0}], ?_⟩
  decide +kernel

theorem cover_110 : Cover 110 2 := by
  refine ⟨![{2, 3}, {2, 3, 4}], ![{0, 1}, {0}], ?_⟩
  decide +kernel

theorem cover_111 : Cover 111 2 := by
  refine ⟨![{0, 2, 3}, {1, 2, 3, 4}], ![{1}, {0}], ?_⟩
  decide +kernel

theorem cover_120 : Cover 120 2 := by
  refine ⟨![{4, 5}, {2, 3}], ![{0}, {1}], ?_⟩
  decide +kernel

theorem cover_121 : Cover 121 2 := by
  refine ⟨![{0, 2, 3}, {1, 4, 5}], ![{1}, {0}], ?_⟩
  decide +kernel

theorem cover_122 : Cover 122 2 := by
  refine ⟨![{2, 4, 5}, {2, 3}], ![{0}, {1}], ?_⟩
  decide +kernel

theorem cover_123 : Cover 123 2 := by
  refine ⟨![{0, 2, 3}, {1, 2, 4, 5}], ![{1}, {0}], ?_⟩
  decide +kernel

theorem cover_126 : Cover 126 2 := by
  refine ⟨![{2, 3}, {2, 3, 4, 5}], ![{0, 1}, {0}], ?_⟩
  decide +kernel

theorem cover_127 : Cover 127 2 := by
  refine ⟨![{0, 2, 3}, {1, 2, 3, 4, 5}], ![{1}, {0}], ?_⟩
  decide +kernel

theorem cover_238 : Cover 238 1 := by
  refine ⟨![{2, 3, 4}], ![{0, 1}], ?_⟩
  decide +kernel

theorem cover_239 : Cover 239 2 := by
  refine ⟨![{0, 2, 3, 4}, {2, 3, 4}], ![{1}, {0, 1}], ?_⟩
  decide +kernel

theorem cover_246 : Cover 246 2 := by
  refine ⟨![{2, 3, 5}, {2, 3, 4}], ![{0}, {1}], ?_⟩
  decide +kernel

theorem cover_247 : Cover 247 2 := by
  refine ⟨![{0, 2, 3, 4}, {1, 2, 3, 5}], ![{1}, {0}], ?_⟩
  decide +kernel

theorem cover_254 : Cover 254 2 := by
  refine ⟨![{2, 3, 4}, {2, 3, 4, 5}], ![{0, 1}, {0}], ?_⟩
  decide +kernel

theorem cover_255 : Cover 255 2 := by
  refine ⟨![{0, 2, 3, 4}, {1, 2, 3, 4, 5}], ![{1}, {0}], ?_⟩
  decide +kernel

theorem cover_510 : Cover 510 1 := by
  refine ⟨![{2, 3, 4, 5}], ![{0, 1}], ?_⟩
  decide +kernel

theorem cover_511 : Cover 511 2 := by
  refine ⟨![{0, 2, 3, 4, 5}, {2, 3, 4, 5}], ![{1}, {0, 1}], ?_⟩
  decide +kernel

theorem cover_615 : Cover 615 2 := by
  refine ⟨![{0, 3}, {1, 3}], ![{1, 2}, {0, 2}], ?_⟩
  decide +kernel

theorem cover_616 : Cover 616 3 := by
  refine ⟨![{4}, {1, 3}, {3}], ![{0}, {2}, {1, 2}], ?_⟩
  decide +kernel

theorem cover_617 : Cover 617 3 := by
  refine ⟨![{0, 2, 3}, {1, 4}, {3}], ![{1}, {0}, {1, 2}], ?_⟩
  decide +kernel

theorem cover_619 : Cover 619 3 := by
  refine ⟨![{0, 3}, {1, 2, 4}, {0, 1, 3}], ![{1, 2}, {0}, {2}], ?_⟩
  decide +kernel

theorem cover_623 : Cover 623 3 := by
  refine ⟨![{0, 3}, {1, 3}, {1, 2, 3, 4}], ![{1, 2}, {0, 2}, {0}], ?_⟩
  decide +kernel

theorem cover_632 : Cover 632 3 := by
  refine ⟨![{4, 5}, {1, 3}, {3}], ![{0}, {2}, {1, 2}], ?_⟩
  decide +kernel

theorem cover_633 : Cover 633 3 := by
  refine ⟨![{0, 2, 3}, {1, 4, 5}, {3}], ![{1}, {0}, {1, 2}], ?_⟩
  decide +kernel

theorem cover_635 : Cover 635 3 := by
  refine ⟨![{0, 3}, {1, 2, 4, 5}, {0, 1, 3}], ![{1, 2}, {0}, {2}], ?_⟩
  decide +kernel

theorem cover_639 : Cover 639 3 := by
  refine ⟨![{0, 3}, {1, 3}, {1, 2, 3, 4, 5}], ![{1, 2}, {0, 2}, {0}], ?_⟩
  decide +kernel

theorem cover_655 : Cover 655 3 := by
  refine ⟨![{0, 4}, {0, 3}, {1, 2, 3, 4}], ![{1}, {2}, {0}], ?_⟩
  decide +kernel

theorem cover_656 : Cover 656 3 := by
  refine ⟨![{5}, {4}, {3}], ![{0}, {1}, {2}], ?_⟩
  decide +kernel

theorem cover_657 : Cover 657 3 := by
  refine ⟨![{0, 4}, {1, 5}, {3}], ![{1}, {0}, {2}], ?_⟩
  decide +kernel

theorem cover_659 : Cover 659 3 := by
  refine ⟨![{0, 4}, {0, 3}, {1, 2, 5}], ![{1}, {2}, {0}], ?_⟩
  decide +kernel

theorem cover_662 : Cover 662 3 := by
  refine ⟨![{0, 3}, {2, 3, 5}, {4}], ![{2}, {0}, {1}], ?_⟩
  decide +kernel

theorem cover_663 : Cover 663 3 := by
  refine ⟨![{0, 4}, {0, 3}, {1, 2, 3, 5}], ![{1}, {2}, {0}], ?_⟩
  decide +kernel

theorem cover_671 : Cover 671 3 := by
  refine ⟨![{0, 4}, {0, 3}, {1, 2, 3, 4, 5}], ![{1}, {2}, {0}], ?_⟩
  decide +kernel

theorem cover_684 : Cover 684 3 := by
  refine ⟨![{3}, {4}, {1, 3}], ![{0, 2}, {0, 1}, {2}], ?_⟩
  decide +kernel

theorem cover_685 : Cover 685 2 := by
  refine ⟨![{1, 3}, {4}], ![{0, 2}, {0, 1}], ?_⟩
  decide +kernel

theorem cover_687 : Cover 687 2 := by
  refine ⟨![{1, 3}, {2, 4}], ![{0, 2}, {0, 1}], ?_⟩
  decide +kernel

theorem cover_691 : Cover 691 3 := by
  refine ⟨![{0, 2, 4}, {0, 1, 3}, {1, 2, 5}], ![{1}, {2}, {0}], ?_⟩
  decide +kernel

theorem cover_692 : Cover 692 3 := by
  refine ⟨![{3}, {3, 5}, {2, 4}], ![{0, 2}, {0}, {1}], ?_⟩
  decide +kernel

theorem cover_693 : Cover 693 3 := by
  refine ⟨![{1, 3}, {1, 3, 5}, {0, 2, 4}], ![{0, 2}, {0}, {1}], ?_⟩
  decide +kernel

theorem cover_694 : Cover 694 3 := by
  refine ⟨![{0, 1, 3}, {2, 3, 5}, {2, 4}], ![{2}, {0}, {1}], ?_⟩
  decide +kernel

theorem cover_695 : Cover 695 3 := by
  refine ⟨![{1, 3}, {1, 2, 3, 5}, {0, 2, 4}], ![{0, 2}, {0}, {1}], ?_⟩
  decide +kernel

theorem cover_700 : Cover 700 3 := by
  refine ⟨![{3}, {3, 4, 5}, {2, 4}], ![{0, 2}, {0}, {1}], ?_⟩
  decide +kernel

theorem cover_701 : Cover 701 3 := by
  refine ⟨![{1, 3}, {4}, {1, 3, 4, 5}], ![{0, 2}, {0, 1}, {0}], ?_⟩
  decide +kernel

theorem cover_703 : Cover 703 3 := by
  refine ⟨![{1, 3}, {2, 4}, {1, 2, 3, 4, 5}], ![{0, 2}, {0, 1}, {0}], ?_⟩
  decide +kernel

theorem cover_750 : Cover 750 2 := by
  refine ⟨![{0, 1, 3}, {2, 3, 4}], ![{2}, {0, 1}], ?_⟩
  decide +kernel

theorem cover_751 : Cover 751 2 := by
  refine ⟨![{0, 3}, {2, 3, 4}], ![{1, 2}, {0, 1}], ?_⟩
  decide +kernel

theorem cover_758 : Cover 758 3 := by
  refine ⟨![{0, 1, 3}, {2, 3, 5}, {2, 3, 4}], ![{2}, {0}, {1}], ?_⟩
  decide +kernel

theorem cover_759 : Cover 759 3 := by
  refine ⟨![{0, 3}, {1, 2, 3, 5}, {0, 2, 3, 4}], ![{1, 2}, {0}, {1}], ?_⟩
  decide +kernel

theorem cover_760 : Cover 760 3 := by
  refine ⟨![{4, 5}, {1, 3}, {2, 3, 4}], ![{0}, {2}, {1}], ?_⟩
  decide +kernel

theorem cover_761 : Cover 761 3 := by
  refine ⟨![{0, 2, 3, 4}, {1, 4, 5}, {3}], ![{1}, {0}, {1, 2}], ?_⟩
  decide +kernel

theorem cover_762 : Cover 762 3 := by
  refine ⟨![{0, 1, 3}, {2, 4, 5}, {2, 3, 4}], ![{2}, {0}, {1}], ?_⟩
  decide +kernel

theorem cover_763 : Cover 763 3 := by
  refine ⟨![{0, 3}, {2, 4}, {1, 2, 4, 5}], ![{1, 2}, {0, 1}, {0}], ?_⟩
  decide +kernel

theorem cover_766 : Cover 766 3 := by
  refine ⟨![{0, 1, 3}, {2, 3, 4}, {2, 3, 4, 5}], ![{2}, {0, 1}, {0}], ?_⟩
  decide +kernel

theorem cover_767 : Cover 767 3 := by
  refine ⟨![{0, 3}, {2, 3, 4}, {1, 2, 3, 4, 5}], ![{1, 2}, {0, 1}, {0}], ?_⟩
  decide +kernel

theorem cover_920 : Cover 920 2 := by
  refine ⟨![{4, 5}, {3}], ![{0, 1}, {2}], ?_⟩
  decide +kernel

theorem cover_921 : Cover 921 3 := by
  refine ⟨![{0, 4, 5}, {4, 5}, {3}], ![{1}, {0, 1}, {2}], ?_⟩
  decide +kernel

theorem cover_922 : Cover 922 2 := by
  refine ⟨![{0, 3}, {4, 5}], ![{2}, {0, 1}], ?_⟩
  decide +kernel

theorem cover_923 : Cover 923 3 := by
  refine ⟨![{0, 4, 5}, {0, 3}, {4, 5}], ![{1}, {2}, {0, 1}], ?_⟩
  decide +kernel

theorem cover_926 : Cover 926 3 := by
  refine ⟨![{0, 3}, {3}, {4, 5}], ![{2}, {0, 2}, {0, 1}], ?_⟩
  decide +kernel

theorem cover_927 : Cover 927 3 := by
  refine ⟨![{0, 4, 5}, {0, 3}, {1, 2, 3, 4, 5}], ![{1}, {2}, {0}], ?_⟩
  decide +kernel

theorem cover_954 : Cover 954 2 := by
  refine ⟨![{0, 1, 3}, {2, 4, 5}], ![{2}, {0, 1}], ?_⟩
  decide +kernel

theorem cover_955 : Cover 955 3 := by
  refine ⟨![{0, 2, 4, 5}, {0, 1, 3}, {2, 4, 5}], ![{1}, {2}, {0, 1}], ?_⟩
  decide +kernel

theorem cover_956 : Cover 956 3 := by
  refine ⟨![{3}, {4, 5}, {1, 3}], ![{0, 2}, {0, 1}, {2}], ?_⟩
  decide +kernel

theorem cover_957 : Cover 957 2 := by
  refine ⟨![{1, 3}, {4, 5}], ![{0, 2}, {0, 1}], ?_⟩
  decide +kernel

theorem cover_958 : Cover 958 2 := by
  refine ⟨![{2, 4, 5}, {3}], ![{0, 1}, {0, 2}], ?_⟩
  decide +kernel

theorem cover_959 : Cover 959 2 := by
  refine ⟨![{1, 3}, {2, 4, 5}], ![{0, 2}, {0, 1}], ?_⟩
  decide +kernel

theorem cover_1022 : Cover 1022 2 := by
  refine ⟨![{0, 1, 3}, {2, 3, 4, 5}], ![{2}, {0, 1}], ?_⟩
  decide +kernel

theorem cover_1023 : Cover 1023 2 := by
  refine ⟨![{0, 3}, {2, 3, 4, 5}], ![{1, 2}, {0, 1}], ?_⟩
  decide +kernel

theorem cover_1743 : Cover 1743 2 := by
  refine ⟨![{0, 3, 4}, {3, 4}], ![{1, 2}, {0, 1, 2}], ?_⟩
  decide +kernel

theorem cover_1749 : Cover 1749 2 := by
  refine ⟨![{1, 3, 5}, {3, 4}], ![{0}, {1, 2}], ?_⟩
  decide +kernel

theorem cover_1751 : Cover 1751 2 := by
  refine ⟨![{0, 3, 4}, {1, 2, 3, 5}], ![{1, 2}, {0}], ?_⟩
  decide +kernel

theorem cover_1759 : Cover 1759 2 := by
  refine ⟨![{0, 3, 4}, {1, 2, 3, 4, 5}], ![{1, 2}, {0}], ?_⟩
  decide +kernel

theorem cover_1775 : Cover 1775 2 := by
  refine ⟨![{0, 3, 4}, {1, 3, 4}], ![{1, 2}, {0, 2}], ?_⟩
  decide +kernel

theorem cover_1780 : Cover 1780 3 := by
  refine ⟨![{3, 5}, {1, 3, 4}, {3, 4}], ![{0}, {2}, {1, 2}], ?_⟩
  decide +kernel

theorem cover_1781 : Cover 1781 3 := by
  refine ⟨![{1, 3}, {1, 3, 5}, {3, 4}], ![{0, 2}, {0}, {1, 2}], ?_⟩
  decide +kernel

theorem cover_1783 : Cover 1783 3 := by
  refine ⟨![{1, 3}, {0, 3, 4}, {1, 2, 3, 5}], ![{0, 2}, {1, 2}, {0}], ?_⟩
  decide +kernel

theorem cover_1788 : Cover 1788 3 := by
  refine ⟨![{3, 4}, {3, 4, 5}, {1, 3, 4}], ![{0, 1, 2}, {0}, {2}], ?_⟩
  decide +kernel

theorem cover_1789 : Cover 1789 3 := by
  refine ⟨![{1, 3, 4}, {1, 3, 4, 5}, {3, 4}], ![{0, 2}, {0}, {0, 1, 2}], ?_⟩
  decide +kernel

theorem cover_1791 : Cover 1791 3 := by
  refine ⟨![{0, 3, 4}, {1, 3, 4}, {1, 2, 3, 4, 5}], ![{1, 2}, {0, 2}, {0}], ?_⟩
  decide +kernel

theorem cover_1880 : Cover 1880 3 := by
  refine ⟨![{4}, {5}, {3}], ![{0, 2}, {0, 1}, {1, 2}], ?_⟩
  decide +kernel

theorem cover_1881 : Cover 1881 3 := by
  refine ⟨![{0, 3, 5}, {1, 4, 5}, {3, 4}], ![{1}, {0}, {2}], ?_⟩
  decide +kernel

theorem cover_1883 : Cover 1883 3 := by
  refine ⟨![{0, 3}, {4}, {5}], ![{1, 2}, {0, 2}, {0, 1}], ?_⟩
  decide +kernel

theorem cover_1884 : Cover 1884 2 := by
  refine ⟨![{3, 4}, {3, 5}], ![{0, 2}, {0, 1}], ?_⟩
  decide +kernel

theorem cover_1885 : Cover 1885 3 := by
  refine ⟨![{0, 3, 5}, {3, 4}, {3, 5}], ![{1}, {0, 2}, {0, 1}], ?_⟩
  decide +kernel

theorem cover_1887 : Cover 1887 3 := by
  refine ⟨![{0, 3}, {3, 4}, {3, 5}], ![{1, 2}, {0, 2}, {0, 1}], ?_⟩
  decide +kernel

theorem cover_1915 : Cover 1915 3 := by
  refine ⟨![{0, 3}, {1, 4}, {2, 5}], ![{1, 2}, {0, 2}, {0, 1}], ?_⟩
  decide +kernel

theorem cover_1916 : Cover 1916 3 := by
  refine ⟨![{3, 4}, {3, 5}, {1, 3, 4}], ![{0, 2}, {0, 1}, {2}], ?_⟩
  decide +kernel

theorem cover_1917 : Cover 1917 2 := by
  refine ⟨![{1, 3, 4}, {3, 5}], ![{0, 2}, {0, 1}], ?_⟩
  decide +kernel

theorem cover_1919 : Cover 1919 2 := by
  refine ⟨![{1, 3, 4}, {2, 3, 5}], ![{0, 2}, {0, 1}], ?_⟩
  decide +kernel

theorem cover_2012 : Cover 2012 2 := by
  refine ⟨![{3, 4}, {3, 4, 5}], ![{0, 1, 2}, {0, 1}], ?_⟩
  decide +kernel

theorem cover_2013 : Cover 2013 3 := by
  refine ⟨![{0, 3, 4, 5}, {3, 4}, {3, 4, 5}], ![{1}, {0, 1, 2}, {0, 1}], ?_⟩
  decide +kernel

theorem cover_2014 : Cover 2014 2 := by
  refine ⟨![{0, 3, 4}, {3, 4, 5}], ![{2}, {0, 1}], ?_⟩
  decide +kernel

theorem cover_2015 : Cover 2015 2 := by
  refine ⟨![{0, 3, 4}, {3, 4, 5}], ![{1, 2}, {0, 1}], ?_⟩
  decide +kernel

theorem cover_2046 : Cover 2046 2 := by
  refine ⟨![{0, 1, 3, 4}, {2, 3, 4, 5}], ![{2}, {0, 1}], ?_⟩
  decide +kernel

theorem cover_2047 : Cover 2047 2 := by
  refine ⟨![{0, 3, 4}, {2, 3, 4, 5}], ![{1, 2}, {0, 1}], ?_⟩
  decide +kernel

theorem cover_4060 : Cover 4060 1 := by
  refine ⟨![{3, 4, 5}], ![{0, 1, 2}], ?_⟩
  decide +kernel

theorem cover_4061 : Cover 4061 2 := by
  refine ⟨![{0, 3, 4, 5}, {3, 4, 5}], ![{1}, {0, 1, 2}], ?_⟩
  decide +kernel

theorem cover_4063 : Cover 4063 2 := by
  refine ⟨![{0, 3, 4, 5}, {3, 4, 5}], ![{1, 2}, {0, 1, 2}], ?_⟩
  decide +kernel

theorem cover_4095 : Cover 4095 2 := by
  refine ⟨![{0, 3, 4, 5}, {1, 3, 4, 5}], ![{1, 2}, {0, 2}], ?_⟩
  decide +kernel

theorem cover_5871 : Cover 5871 3 := by
  refine ⟨![{0, 4}, {1, 4}, {2, 4}], ![{1, 2, 3}, {0, 2, 3}, {0, 1, 3}], ?_⟩
  decide +kernel

theorem cover_5872 : Cover 5872 3 := by
  refine ⟨![{5}, {1, 4}, {2, 4}], ![{0}, {2, 3}, {1, 3}], ?_⟩
  decide +kernel

theorem cover_5873 : Cover 5873 3 := by
  refine ⟨![{1, 5}, {1, 4}, {2, 4}], ![{0}, {2, 3}, {1, 3}], ?_⟩
  decide +kernel

theorem cover_5875 : Cover 5875 3 := by
  refine ⟨![{0, 3, 4}, {1, 2, 5}, {1, 4}], ![{1, 2}, {0}, {2, 3}], ?_⟩
  decide +kernel

theorem cover_5879 : Cover 5879 3 := by
  refine ⟨![{0, 2, 4}, {0, 1, 4}, {1, 2, 3, 5}], ![{1, 3}, {2, 3}, {0}], ?_⟩
  decide +kernel

theorem cover_5887 : Cover 5887 3 := by
  refine ⟨![{1, 4}, {2, 4}, {1, 2, 3, 4, 5}], ![{0, 2, 3}, {0, 1, 3}, {0}], ?_⟩
  decide +kernel

theorem cover_5905 : Cover 5905 4 := by
  refine ⟨![{0, 5}, {5}, {2, 4}, {4}], ![{1}, {0, 1}, {3}, {2, 3}], ?_⟩
  decide +kernel

theorem cover_5907 : Cover 5907 4 := by
  refine ⟨![{0, 5}, {0, 3, 4}, {5}, {4}], ![{1}, {2}, {0, 1}, {2, 3}], ?_⟩
  decide +kernel

theorem cover_5911 : Cover 5911 4 := by
  refine ⟨![{0, 5}, {0, 4}, {5}, {0, 2, 4}], ![{1}, {2, 3}, {0, 1}, {3}], ?_⟩
  decide +kernel

theorem cover_5919 : Cover 5919 4 := by
  refine ⟨![{0, 5}, {0, 4}, {2, 4}, {5}], ![{1}, {2, 3}, {0, 3}, {0, 1}], ?_⟩
  decide +kernel

theorem cover_5941 : Cover 5941 3 := by
  refine ⟨![{1, 3}, {5}, {4}], ![{0, 2}, {0, 1}, {2, 3}], ?_⟩
  decide +kernel

theorem cover_5943 : Cover 5943 3 := by
  refine ⟨![{1, 3}, {0, 4}, {2, 5}], ![{0, 2}, {2, 3}, {0, 1}], ?_⟩
  decide +kernel

theorem cover_5948 : Cover 5948 4 := by
  refine ⟨![{0, 2, 4}, {4}, {5}, {1, 3, 4}], ![{3}, {0, 2, 3}, {0, 1}, {2}], ?_⟩
  decide +kernel

theorem cover_5949 : Cover 5949 3 := by
  refine ⟨![{1, 3, 4}, {5}, {4}], ![{0, 2}, {0, 1}, {0, 2, 3}], ?_⟩
  decide +kernel

theorem cover_5950 : Cover 5950 3 := by
  refine ⟨![{0, 4}, {2, 4}, {2, 5}], ![{2, 3}, {0, 3}, {0, 1}], ?_⟩
  decide +kernel

theorem cover_5951 : Cover 5951 3 := by
  refine ⟨![{1, 3, 4}, {0, 4}, {2, 5}], ![{0, 2}, {2, 3}, {0, 1}], ?_⟩
  decide +kernel

theorem cover_6007 : Cover 6007 3 := by
  refine ⟨![{0, 3}, {0, 1, 4}, {2, 3, 5}], ![{1, 2}, {2, 3}, {0, 1}], ?_⟩
  decide +kernel

theorem cover_6010 : Cover 6010 3 := by
  refine ⟨![{2, 4}, {2, 5}, {1, 4}], ![{0, 3}, {0, 1}, {2, 3}], ?_⟩
  decide +kernel

theorem cover_6011 : Cover 6011 3 := by
  refine ⟨![{1, 4}, {1, 2, 4}, {2, 5}], ![{0, 2, 3}, {0, 3}, {0, 1}], ?_⟩
  decide +kernel

theorem cover_6014 : Cover 6014 3 := by
  refine ⟨![{0, 1, 4}, {2, 4}, {2, 3, 5}], ![{2, 3}, {0, 3}, {0, 1}], ?_⟩
  decide +kernel

theorem cover_6015 : Cover 6015 3 := by
  refine ⟨![{1, 4}, {1, 2, 4}, {2, 3, 5}], ![{0, 2, 3}, {0, 3}, {0, 1}], ?_⟩
  decide +kernel

theorem cover_6142 : Cover 6142 3 := by
  refine ⟨![{0, 1, 4}, {2, 4}, {2, 3, 4, 5}], ![{2, 3}, {0, 1, 3}, {0, 1}], ?_⟩
  decide +kernel

theorem cover_6143 : Cover 6143 3 := by
  refine ⟨![{0, 4}, {2, 4}, {2, 3, 4, 5}], ![{1, 2, 3}, {0, 1, 3}, {0, 1}], ?_⟩
  decide +kernel

theorem cover_6654 : Cover 6654 3 := by
  refine ⟨![{0, 1, 5}, {0, 1, 4}, {2, 3, 4, 5}], ![{2}, {3}, {0, 1}], ?_⟩
  decide +kernel

theorem cover_6655 : Cover 6655 3 := by
  refine ⟨![{0, 4}, {0, 5}, {2, 3, 4, 5}], ![{1, 3}, {1, 2}, {0, 1}], ?_⟩
  decide +kernel

theorem cover_7071 : Cover 7071 3 := by
  refine ⟨![{0, 4}, {2, 4}, {5}], ![{1, 3}, {0, 3}, {0, 1, 2}], ?_⟩
  decide +kernel

theorem cover_7100 : Cover 7100 3 := by
  refine ⟨![{0, 2, 4}, {4, 5}, {1, 3, 5}], ![{3}, {0, 1}, {2}], ?_⟩
  decide +kernel

theorem cover_7101 : Cover 7101 3 := by
  refine ⟨![{0, 2, 4}, {4}, {5}], ![{1, 3}, {0, 1, 3}, {0, 1, 2}], ?_⟩
  decide +kernel

theorem cover_7103 : Cover 7103 3 := by
  refine ⟨![{0, 2, 4}, {2, 4}, {5}], ![{1, 3}, {0, 1, 3}, {0, 1, 2}], ?_⟩
  decide +kernel

theorem cover_7166 : Cover 7166 2 := by
  refine ⟨![{2, 4}, {3, 5}], ![{0, 1, 3}, {0, 1, 2}], ?_⟩
  decide +kernel

theorem cover_7167 : Cover 7167 3 := by
  refine ⟨![{0, 2, 4}, {2, 4}, {3, 5}], ![{1, 3}, {0, 1, 3}, {0, 1, 2}], ?_⟩
  decide +kernel

theorem cover_8157 : Cover 8157 2 := by
  refine ⟨![{0, 4}, {3, 4, 5}], ![{1, 3}, {0, 1, 2}], ?_⟩
  decide +kernel

theorem cover_8159 : Cover 8159 2 := by
  refine ⟨![{0, 4}, {3, 4, 5}], ![{1, 2, 3}, {0, 1, 2}], ?_⟩
  decide +kernel

theorem cover_8191 : Cover 8191 3 := by
  refine ⟨![{0, 4}, {1, 4}, {3, 4, 5}], ![{1, 2, 3}, {0, 2, 3}, {0, 1, 2}], ?_⟩
  decide +kernel

theorem cover_15870 : Cover 15870 2 := by
  refine ⟨![{0, 1, 4, 5}, {4, 5}], ![{2, 3}, {0, 1, 2, 3}], ?_⟩
  decide +kernel

theorem cover_15871 : Cover 15871 2 := by
  refine ⟨![{0, 4, 5}, {1, 4, 5}], ![{1, 2, 3}, {0, 2, 3}], ?_⟩
  decide +kernel

theorem cover_16383 : Cover 16383 3 := by
  refine ⟨![{0, 4, 5}, {1, 4, 5}, {2, 4, 5}], ![{1, 2, 3}, {0, 2, 3}, {0, 1, 3}], ?_⟩
  decide +kernel

theorem cover_32767 : Cover 32767 3 := by
  refine ⟨![{0, 5}, {1, 2, 5}, {1, 3, 5}], ![{1, 2, 3, 4}, {0, 3, 4}, {0, 2, 4}], ?_⟩
  decide +kernel

theorem repCons {a : Nat} {xs : List Nat} (ha : Solves a)
    (ht : ∀ g ∈ xs, Solves g) : ∀ g ∈ a :: xs, Solves g := by
  intro g hg
  rcases List.mem_cons.mp hg with rfl | h
  · exact ha
  · exact ht g h

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
theorem solveRep : ∀ g ∈ repList, Solves g := by
  unfold repList
  refine repCons (fun C _ fit => ⟨0, easy_0 C fit, cover_0⟩) ?_
  refine repCons (fun C _ fit => ⟨1, easy_1 C fit, cover_1⟩) ?_
  refine repCons (fun C _ fit => ⟨1, easy_3 C fit, cover_3⟩) ?_
  refine repCons (fun C _ fit => ⟨1, easy_7 C fit, cover_7⟩) ?_
  refine repCons (fun C _ fit => ⟨1, easy_15 C fit, cover_15⟩) ?_
  refine repCons (fun C _ fit => ⟨1, easy_31 C fit, cover_31⟩) ?_
  refine repCons (fun C _ fit => ⟨2, easy_35 C fit, cover_35⟩) ?_
  refine repCons (fun C _ fit => ⟨2, easy_36 C fit, cover_36⟩) ?_
  refine repCons (fun C _ fit => ⟨2, easy_37 C fit, cover_37⟩) ?_
  refine repCons (fun C _ fit => ⟨2, easy_39 C fit, cover_39⟩) ?_
  refine repCons (fun C _ fit => ⟨2, easy_44 C fit, cover_44⟩) ?_
  refine repCons (fun C _ fit => ⟨2, easy_45 C fit, cover_45⟩) ?_
  refine repCons (fun C _ fit => ⟨2, easy_47 C fit, cover_47⟩) ?_
  refine repCons (fun C _ fit => ⟨2, easy_60 C fit, cover_60⟩) ?_
  refine repCons (fun C _ fit => ⟨2, easy_61 C fit, cover_61⟩) ?_
  refine repCons (fun C _ fit => ⟨2, easy_63 C fit, cover_63⟩) ?_
  refine repCons (fun C _ fit => ⟨1, easy_102 C fit, cover_102⟩) ?_
  refine repCons (fun C _ fit => ⟨2, easy_103 C fit, cover_103⟩) ?_
  refine repCons (fun C _ fit => ⟨2, easy_106 C fit, cover_106⟩) ?_
  refine repCons (fun C _ fit => ⟨2, easy_107 C fit, cover_107⟩) ?_
  refine repCons (fun C _ fit => ⟨2, easy_110 C fit, cover_110⟩) ?_
  refine repCons (fun C _ fit => ⟨2, easy_111 C fit, cover_111⟩) ?_
  refine repCons (fun C _ fit => ⟨2, easy_120 C fit, cover_120⟩) ?_
  refine repCons (fun C _ fit => ⟨2, easy_121 C fit, cover_121⟩) ?_
  refine repCons (fun C _ fit => ⟨2, easy_122 C fit, cover_122⟩) ?_
  refine repCons (fun C _ fit => ⟨2, easy_123 C fit, cover_123⟩) ?_
  refine repCons (fun C _ fit => ⟨2, easy_126 C fit, cover_126⟩) ?_
  refine repCons (fun C _ fit => ⟨2, easy_127 C fit, cover_127⟩) ?_
  refine repCons (fun C _ fit => ⟨1, easy_238 C fit, cover_238⟩) ?_
  refine repCons (fun C _ fit => ⟨2, easy_239 C fit, cover_239⟩) ?_
  refine repCons (fun C _ fit => ⟨2, easy_246 C fit, cover_246⟩) ?_
  refine repCons (fun C _ fit => ⟨2, easy_247 C fit, cover_247⟩) ?_
  refine repCons (fun C _ fit => ⟨2, easy_254 C fit, cover_254⟩) ?_
  refine repCons (fun C _ fit => ⟨2, easy_255 C fit, cover_255⟩) ?_
  refine repCons (fun C _ fit => ⟨1, easy_510 C fit, cover_510⟩) ?_
  refine repCons (fun C _ fit => ⟨2, easy_511 C fit, cover_511⟩) ?_
  refine repCons (fun C _ fit => ⟨2, easy_615 C fit, cover_615⟩) ?_
  refine repCons (fun C _ fit => ⟨3, easy_616 C fit, cover_616⟩) ?_
  refine repCons (fun C _ fit => ⟨3, easy_617 C fit, cover_617⟩) ?_
  refine repCons (fun C wf fit => ⟨3, hard_619 C wf fit, cover_619⟩) ?_
  refine repCons (fun C wf fit => ⟨3, hard_623 C wf fit, cover_623⟩) ?_
  refine repCons (fun C _ fit => ⟨3, easy_632 C fit, cover_632⟩) ?_
  refine repCons (fun C _ fit => ⟨3, easy_633 C fit, cover_633⟩) ?_
  refine repCons (fun C wf fit => ⟨3, hard_635 C wf fit, cover_635⟩) ?_
  refine repCons (fun C wf fit => ⟨3, hard_639 C wf fit, cover_639⟩) ?_
  refine repCons (fun C _ fit => ⟨3, easy_655 C fit, cover_655⟩) ?_
  refine repCons (fun C _ fit => ⟨3, easy_656 C fit, cover_656⟩) ?_
  refine repCons (fun C _ fit => ⟨3, easy_657 C fit, cover_657⟩) ?_
  refine repCons (fun C _ fit => ⟨3, easy_659 C fit, cover_659⟩) ?_
  refine repCons (fun C _ fit => ⟨3, easy_662 C fit, cover_662⟩) ?_
  refine repCons (fun C _ fit => ⟨3, easy_663 C fit, cover_663⟩) ?_
  refine repCons (fun C _ fit => ⟨3, easy_671 C fit, cover_671⟩) ?_
  refine repCons (fun C _ fit => ⟨3, easy_684 C fit, cover_684⟩) ?_
  refine repCons (fun C _ fit => ⟨2, easy_685 C fit, cover_685⟩) ?_
  refine repCons (fun C _ fit => ⟨2, easy_687 C fit, cover_687⟩) ?_
  refine repCons (fun C wf fit => ⟨3, hard_691 C wf fit, cover_691⟩) ?_
  refine repCons (fun C _ fit => ⟨3, easy_692 C fit, cover_692⟩) ?_
  refine repCons (fun C wf fit => ⟨3, hard_693 C wf fit, cover_693⟩) ?_
  refine repCons (fun C _ fit => ⟨3, easy_694 C fit, cover_694⟩) ?_
  refine repCons (fun C wf fit => ⟨3, hard_695 C wf fit, cover_695⟩) ?_
  refine repCons (fun C _ fit => ⟨3, easy_700 C fit, cover_700⟩) ?_
  refine repCons (fun C wf fit => ⟨3, hard_701 C wf fit, cover_701⟩) ?_
  refine repCons (fun C wf fit => ⟨3, hard_703 C wf fit, cover_703⟩) ?_
  refine repCons (fun C _ fit => ⟨2, easy_750 C fit, cover_750⟩) ?_
  refine repCons (fun C _ fit => ⟨2, easy_751 C fit, cover_751⟩) ?_
  refine repCons (fun C _ fit => ⟨3, easy_758 C fit, cover_758⟩) ?_
  refine repCons (fun C wf fit => ⟨3, hard_759 C wf fit, cover_759⟩) ?_
  refine repCons (fun C _ fit => ⟨3, easy_760 C fit, cover_760⟩) ?_
  refine repCons (fun C _ fit => ⟨3, easy_761 C fit, cover_761⟩) ?_
  refine repCons (fun C _ fit => ⟨3, easy_762 C fit, cover_762⟩) ?_
  refine repCons (fun C wf fit => ⟨3, hard_763 C wf fit, cover_763⟩) ?_
  refine repCons (fun C wf fit => ⟨3, hard_766 C wf fit, cover_766⟩) ?_
  refine repCons (fun C wf fit => ⟨3, hard_767 C wf fit, cover_767⟩) ?_
  refine repCons (fun C _ fit => ⟨2, easy_920 C fit, cover_920⟩) ?_
  refine repCons (fun C _ fit => ⟨3, easy_921 C fit, cover_921⟩) ?_
  refine repCons (fun C _ fit => ⟨2, easy_922 C fit, cover_922⟩) ?_
  refine repCons (fun C _ fit => ⟨3, easy_923 C fit, cover_923⟩) ?_
  refine repCons (fun C _ fit => ⟨3, easy_926 C fit, cover_926⟩) ?_
  refine repCons (fun C _ fit => ⟨3, easy_927 C fit, cover_927⟩) ?_
  refine repCons (fun C _ fit => ⟨2, easy_954 C fit, cover_954⟩) ?_
  refine repCons (fun C wf fit => ⟨3, hard_955 C wf fit, cover_955⟩) ?_
  refine repCons (fun C _ fit => ⟨3, easy_956 C fit, cover_956⟩) ?_
  refine repCons (fun C _ fit => ⟨2, easy_957 C fit, cover_957⟩) ?_
  refine repCons (fun C _ fit => ⟨2, easy_958 C fit, cover_958⟩) ?_
  refine repCons (fun C _ fit => ⟨2, easy_959 C fit, cover_959⟩) ?_
  refine repCons (fun C _ fit => ⟨2, easy_1022 C fit, cover_1022⟩) ?_
  refine repCons (fun C _ fit => ⟨2, easy_1023 C fit, cover_1023⟩) ?_
  refine repCons (fun C _ fit => ⟨2, easy_1743 C fit, cover_1743⟩) ?_
  refine repCons (fun C _ fit => ⟨2, easy_1749 C fit, cover_1749⟩) ?_
  refine repCons (fun C _ fit => ⟨2, easy_1751 C fit, cover_1751⟩) ?_
  refine repCons (fun C _ fit => ⟨2, easy_1759 C fit, cover_1759⟩) ?_
  refine repCons (fun C _ fit => ⟨2, easy_1775 C fit, cover_1775⟩) ?_
  refine repCons (fun C _ fit => ⟨3, easy_1780 C fit, cover_1780⟩) ?_
  refine repCons (fun C _ fit => ⟨3, easy_1781 C fit, cover_1781⟩) ?_
  refine repCons (fun C wf fit => ⟨3, hard_1783 C wf fit, cover_1783⟩) ?_
  refine repCons (fun C _ fit => ⟨3, easy_1788 C fit, cover_1788⟩) ?_
  refine repCons (fun C wf fit => ⟨3, hard_1789 C wf fit, cover_1789⟩) ?_
  refine repCons (fun C wf fit => ⟨3, hard_1791 C wf fit, cover_1791⟩) ?_
  refine repCons (fun C _ fit => ⟨3, easy_1880 C fit, cover_1880⟩) ?_
  refine repCons (fun C _ fit => ⟨3, easy_1881 C fit, cover_1881⟩) ?_
  refine repCons (fun C _ fit => ⟨3, easy_1883 C fit, cover_1883⟩) ?_
  refine repCons (fun C _ fit => ⟨2, easy_1884 C fit, cover_1884⟩) ?_
  refine repCons (fun C _ fit => ⟨3, easy_1885 C fit, cover_1885⟩) ?_
  refine repCons (fun C _ fit => ⟨3, easy_1887 C fit, cover_1887⟩) ?_
  refine repCons (fun C wf fit => ⟨3, hard_1915 C wf fit, cover_1915⟩) ?_
  refine repCons (fun C _ fit => ⟨3, easy_1916 C fit, cover_1916⟩) ?_
  refine repCons (fun C _ fit => ⟨2, easy_1917 C fit, cover_1917⟩) ?_
  refine repCons (fun C _ fit => ⟨2, easy_1919 C fit, cover_1919⟩) ?_
  refine repCons (fun C _ fit => ⟨2, easy_2012 C fit, cover_2012⟩) ?_
  refine repCons (fun C wf fit => ⟨3, hard_2013 C wf fit, cover_2013⟩) ?_
  refine repCons (fun C _ fit => ⟨2, easy_2014 C fit, cover_2014⟩) ?_
  refine repCons (fun C _ fit => ⟨2, easy_2015 C fit, cover_2015⟩) ?_
  refine repCons (fun C _ fit => ⟨2, easy_2046 C fit, cover_2046⟩) ?_
  refine repCons (fun C _ fit => ⟨2, easy_2047 C fit, cover_2047⟩) ?_
  refine repCons (fun C _ fit => ⟨1, easy_4060 C fit, cover_4060⟩) ?_
  refine repCons (fun C _ fit => ⟨2, easy_4061 C fit, cover_4061⟩) ?_
  refine repCons (fun C _ fit => ⟨2, easy_4063 C fit, cover_4063⟩) ?_
  refine repCons (fun C _ fit => ⟨2, easy_4095 C fit, cover_4095⟩) ?_
  refine repCons (fun C _ fit => ⟨3, easy_5871 C fit, cover_5871⟩) ?_
  refine repCons (fun C _ fit => ⟨3, easy_5872 C fit, cover_5872⟩) ?_
  refine repCons (fun C _ fit => ⟨3, easy_5873 C fit, cover_5873⟩) ?_
  refine repCons (fun C _ fit => ⟨3, easy_5875 C fit, cover_5875⟩) ?_
  refine repCons (fun C _ fit => ⟨3, easy_5879 C fit, cover_5879⟩) ?_
  refine repCons (fun C _ fit => ⟨3, easy_5887 C fit, cover_5887⟩) ?_
  refine repCons (fun C _ fit => ⟨4, easy_5905 C fit, cover_5905⟩) ?_
  refine repCons (fun C wf fit => ⟨4, hard_5907 C wf fit, cover_5907⟩) ?_
  refine repCons (fun C wf fit => ⟨4, hard_5911 C wf fit, cover_5911⟩) ?_
  refine repCons (fun C wf fit => ⟨4, hard_5919 C wf fit, cover_5919⟩) ?_
  refine repCons (fun C _ fit => ⟨3, easy_5941 C fit, cover_5941⟩) ?_
  refine repCons (fun C _ fit => ⟨3, easy_5943 C fit, cover_5943⟩) ?_
  refine repCons (fun C wf fit => ⟨4, hard_5948 C wf fit, cover_5948⟩) ?_
  refine repCons (fun C _ fit => ⟨3, easy_5949 C fit, cover_5949⟩) ?_
  refine repCons (fun C _ fit => ⟨3, easy_5950 C fit, cover_5950⟩) ?_
  refine repCons (fun C _ fit => ⟨3, easy_5951 C fit, cover_5951⟩) ?_
  refine repCons (fun C _ fit => ⟨3, easy_6007 C fit, cover_6007⟩) ?_
  refine repCons (fun C _ fit => ⟨3, easy_6010 C fit, cover_6010⟩) ?_
  refine repCons (fun C _ fit => ⟨3, easy_6011 C fit, cover_6011⟩) ?_
  refine repCons (fun C _ fit => ⟨3, easy_6014 C fit, cover_6014⟩) ?_
  refine repCons (fun C _ fit => ⟨3, easy_6015 C fit, cover_6015⟩) ?_
  refine repCons (fun C wf fit => ⟨3, hard_6142 C wf fit, cover_6142⟩) ?_
  refine repCons (fun C _ fit => ⟨3, easy_6143 C fit, cover_6143⟩) ?_
  refine repCons (fun C _ fit => ⟨3, easy_6654 C fit, cover_6654⟩) ?_
  refine repCons (fun C _ fit => ⟨3, easy_6655 C fit, cover_6655⟩) ?_
  refine repCons (fun C _ fit => ⟨3, easy_7071 C fit, cover_7071⟩) ?_
  refine repCons (fun C _ fit => ⟨3, easy_7100 C fit, cover_7100⟩) ?_
  refine repCons (fun C _ fit => ⟨3, easy_7101 C fit, cover_7101⟩) ?_
  refine repCons (fun C _ fit => ⟨3, easy_7103 C fit, cover_7103⟩) ?_
  refine repCons (fun C _ fit => ⟨2, easy_7166 C fit, cover_7166⟩) ?_
  refine repCons (fun C _ fit => ⟨3, easy_7167 C fit, cover_7167⟩) ?_
  refine repCons (fun C _ fit => ⟨2, easy_8157 C fit, cover_8157⟩) ?_
  refine repCons (fun C _ fit => ⟨2, easy_8159 C fit, cover_8159⟩) ?_
  refine repCons (fun C _ fit => ⟨3, easy_8191 C fit, cover_8191⟩) ?_
  refine repCons (fun C _ fit => ⟨2, easy_15870 C fit, cover_15870⟩) ?_
  refine repCons (fun C _ fit => ⟨2, easy_15871 C fit, cover_15871⟩) ?_
  refine repCons (fun C _ fit => ⟨3, easy_16383 C fit, cover_16383⟩) ?_
  refine repCons (fun C _ fit => ⟨3, easy_32767 C fit, cover_32767⟩) ?_
  simp

open PEqualNP.AndCount

def packBits : List Bool → Nat
  | [] => 0
  | b :: bs => Nat.bit b (packBits bs)

theorem bit_read (bs : List Bool) (i : Nat) : (packBits bs).testBit i = bs.getD i false := by
  induction bs generalizing i with
  | nil => simp [packBits, List.getD]
  | cons b bs ih =>
    cases i with
    | zero => simp [packBits, List.getD]
    | succ i => simpa [packBits, Nat.testBit_bit_succ, List.getD] using ih i

theorem pack_lt (bs : List Bool) : packBits bs < 2 ^ bs.length := by
  induction bs with
  | nil => decide
  | cons b bs ih => simpa [packBits, List.length_cons, Nat.bit_lt_two_pow_succ_iff] using ih

def raw (f : Fin 6 → Fin 6 → Bool) : Nat := packBits [f 0 1, f 0 2, f 0 3, f 0 4, f 0 5, f 1 2, f 1 3, f 1 4, f 1 5, f 2 3, f 2 4, f 2 5, f 3 4, f 3 5, f 4 5]

noncomputable def encode (G : SimpleGraph (Fin 6)) (e : Equiv.Perm (Fin 6)) : Nat := by
  classical exact raw (fun a b => decide (G.Adj (e a) (e b)))

theorem raw_lt (f : Fin 6 → Fin 6 → Bool) : raw f < 32768 := by
  unfold raw
  apply Nat.lt_of_lt_of_eq (pack_lt [f 0 1, f 0 2, f 0 3, f 0 4, f 0 5, f 1 2, f 1 3, f 1 4, f 1 5, f 2 3, f 2 4, f 2 5, f 3 4, f 3 5, f 4 5])
  change (2:Nat)^15 = 32768
  decide

theorem encode_lt (G : SimpleGraph (Fin 6)) (e : Equiv.Perm (Fin 6)) : encode G e < 32768 := by
  unfold encode
  apply raw_lt

theorem encode_rel (G : SimpleGraph (Fin 6)) (e : Equiv.Perm (Fin 6)) : Relabel G e (encode G e) := by
  classical
  intro a b
  simp only [Adjacent, encode, raw, bit_read]
  fin_cases a <;> fin_cases b <;>
    simp [slot, List.getD] <;>
    exact G.adj_comm _ _

def move (g : Nat) (p : Fin 6 → Fin 6) : Nat := raw (fun a b => decide (Adjacent g (p a) (p b)))

theorem move_spec (G : SimpleGraph (Fin 6)) (e p : Equiv.Perm (Fin 6)) :
    move (encode G e) p = encode G (p.trans e) := by
  classical
  change raw _ = raw _
  congr 1
  funext a b
  change decide (Adjacent (encode G e) (p a) (p b)) = decide (G.Adj (e (p a)) (e (p b)))
  exact decide_eq_decide.mpr (encode_rel G e (p a) (p b))

def permOf (p q : Fin 6 → Fin 6) (hl : ∀ i, q (p i) = i) (hr : ∀ i, p (q i) = i) :
    Equiv.Perm (Fin 6) := ⟨p,q,hl,hr⟩

def perm0 : Equiv.Perm (Fin 6) := permOf ![0,2,3,4,5,1] ![0,5,1,2,3,4] (by decide) (by decide)

def perm1 : Equiv.Perm (Fin 6) := permOf ![1,0,2,3,4,5] ![1,0,2,3,4,5] (by decide) (by decide)

def perm2 : Equiv.Perm (Fin 6) := permOf ![0,1,2,3,5,4] ![0,1,2,3,5,4] (by decide) (by decide)

def perm3 : Equiv.Perm (Fin 6) := permOf ![0,1,2,4,3,5] ![0,1,2,4,3,5] (by decide) (by decide)

def perm4 : Equiv.Perm (Fin 6) := permOf ![0,3,1,2,5,4] ![0,2,3,1,5,4] (by decide) (by decide)

def perm5 : Equiv.Perm (Fin 6) := permOf ![0,2,1,4,3,5] ![0,2,1,4,3,5] (by decide) (by decide)

def perm6 : Equiv.Perm (Fin 6) := permOf ![0,1,3,2,4,5] ![0,1,3,2,4,5] (by decide) (by decide)

def perm7 : Equiv.Perm (Fin 6) := permOf ![0,2,1,3,5,4] ![0,2,1,3,5,4] (by decide) (by decide)

def perm8 : Equiv.Perm (Fin 6) := permOf ![1,0,3,2,5,4] ![1,0,3,2,5,4] (by decide) (by decide)

def perm9 : Equiv.Perm (Fin 6) := permOf ![5,4,2,0,3,1] ![3,5,2,4,1,0] (by decide) (by decide)

def perm10 : Equiv.Perm (Fin 6) := permOf ![1,2,0,4,5,3] ![2,0,1,5,3,4] (by decide) (by decide)

def perm11 : Equiv.Perm (Fin 6) := permOf ![0,3,4,2,1,5] ![0,4,3,1,2,5] (by decide) (by decide)

def perm12 : Equiv.Perm (Fin 6) := permOf ![0,1,3,2,5,4] ![0,1,3,2,5,4] (by decide) (by decide)

def perm13 : Equiv.Perm (Fin 6) := permOf ![1,0,2,4,3,5] ![1,0,2,4,3,5] (by decide) (by decide)

def perm14 : Equiv.Perm (Fin 6) := permOf ![2,3,0,1,5,4] ![2,3,0,1,5,4] (by decide) (by decide)

def perm15 : Equiv.Perm (Fin 6) := permOf ![0,2,1,3,4,5] ![0,2,1,3,4,5] (by decide) (by decide)

def perm16 : Equiv.Perm (Fin 6) := permOf ![3,4,5,0,1,2] ![3,4,5,0,1,2] (by decide) (by decide)

def smaller (g : Nat) : Bool :=
  decide (move g perm0 < g) ||
  decide (move g perm1 < g) ||
  decide (move g perm2 < g) ||
  decide (move g perm3 < g) ||
  decide (move g perm4 < g) ||
  decide (move g perm5 < g) ||
  decide (move g perm6 < g) ||
  decide (move g perm7 < g) ||
  decide (move g perm8 < g) ||
  decide (move g perm9 < g) ||
  decide (move g perm10 < g) ||
  decide (move g perm11 < g) ||
  decide (move g perm12 < g) ||
  decide (move g perm13 < g) ||
  decide (move g perm14 < g) ||
  decide (move g perm15 < g) ||
  decide (move g perm16 < g)

theorem minimal_ok (G : SimpleGraph (Fin 6)) (e : Equiv.Perm (Fin 6))
    (h : ∀ p : Equiv.Perm (Fin 6), encode G e ≤ encode G (p.trans e)) : smaller (encode G e) = false := by
  simp [smaller, move_spec, Nat.not_lt_of_ge, h]

def orbitCheck (g : Nat) : Bool := smaller g || repList.contains g

theorem representative (checked : ∀ g : Fin 32768, orbitCheck g.val = true)
    (G : SimpleGraph (Fin 6)) : ∃ g ∈ repList, ∃ e : Equiv.Perm (Fin 6), Relabel G e g := by
  classical
  let P := fun g : Nat => ∃ e : Equiv.Perm (Fin 6), encode G e = g
  have ex : ∃ g, P g := ⟨_, Equiv.refl _, rfl⟩
  obtain ⟨e, he⟩ := Nat.find_spec ex
  have minimal (p : Equiv.Perm (Fin 6)) : encode G e ≤ encode G (p.trans e) := by
    rw [he]
    exact Nat.find_min' ex ⟨p.trans e, rfl⟩
  have h := checked ⟨encode G e, encode_lt G e⟩
  change smaller (encode G e) || repList.contains (encode G e) = true at h
  rw [minimal_ok G e minimal] at h
  exact ⟨encode G e, by simpa using h, e, encode_rel G e⟩

def column (j : Nat) : Nat → Nat
  | 0 => 0
  | d + 1 => if j = d then (2 ^ (2 ^ d) - 1) <<< (2 ^ d)
      else (column j d % (2 ^ (2 ^ d))) ||| (column j d <<< (2 ^ d))

theorem column_read (d j i : Nat) (hj : j < d) (hi : i < 2 ^ d) :
    (column j d).testBit i = i.testBit j := by
  induction d generalizing j i with
  | zero => omega
  | succ d ih =>
    rw [column]
    by_cases h : j = d
    · subst j
      simp only [ite_true, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
      by_cases htop : 2 ^ d ≤ i
      · have ha : i - 2 ^ d < 2 ^ d := by rw [Nat.pow_succ] at hi; omega
        simp [htop, ha, Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt htop hi]
      · simp [htop, Nat.testBit_lt_two_pow (Nat.lt_of_not_ge htop)]
    · have hj' : j < d := by omega
      simp only [ite_eq_right h, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_mod_two_pow]
      by_cases hl : i < 2 ^ d
      · simp [hl, Nat.not_le.mpr hl, ih j i hj' hl]
      · have htop := Nat.le_of_not_gt hl
        have ha : i - 2 ^ d < 2 ^ d := by rw [Nat.pow_succ] at hi; omega
        have hq := Nat.testBit_two_pow_add_gt hj' (i - 2 ^ d)
        rw [Nat.add_sub_of_le htop] at hq
        simp [hl, htop, ih j _ hj' ha, hq]

def fullColumn : Nat := 2 ^ 32768 - 1

def cmpNum (low : Bool) (x y : Nat) : Bool :=
  if low then decide (x ≤ y) else decide (x < y)

theorem cmp_bit (a b low : Bool) (x y : Nat) :
    cmpNum low (Nat.bit a x) (Nat.bit b y) =
      cmpNum ((!a && b) || (!(a ^^ b) && low)) x y := by
  apply Bool.eq_iff_iff.mpr
  cases a <;> cases b <;> cases low <;> simp [cmpNum, Nat.bit] <;> omega

def cmpColumn (xs : List (Nat × Nat)) (low : Nat) : Nat :=
  match xs with
  | [] => low
  | (a,b) :: t => cmpColumn t (((fullColumn ^^^ a) &&& b) ||| ((fullColumn ^^^ (a ^^^ b)) &&& low))

theorem cmpColumn_read (xs : List (Nat × Nat)) (low i : Nat) (hi : i < 32768) :
    (cmpColumn xs low).testBit i = cmpNum (low.testBit i)
      (packBits (xs.map (fun p => p.1.testBit i))) (packBits (xs.map (fun p => p.2.testBit i))) := by
  induction xs generalizing low with
  | nil => cases h : low.testBit i <;> simp [cmpColumn, cmpNum, packBits, h]
  | cons p t ih =>
    rcases p with ⟨a,b⟩
    rw [cmpColumn, ih]
    simp only [List.map_cons, packBits, cmp_bit, fullColumn, Nat.testBit_or,
      Nat.testBit_and, Nat.testBit_xor, Nat.testBit_two_pow_sub_one, decide_eq_true hi]
    cases a.testBit i <;> cases b.testBit i <;> rfl

def pointsColumn : List Nat → Nat
  | [] => 0
  | a :: t => (2 ^ a) ||| pointsColumn t

theorem pointsColumn_read (xs : List Nat) (i : Nat) :
    (pointsColumn xs).testBit i = xs.contains i := by
  induction xs with
  | nil => simp [pointsColumn]
  | cons a t ih => simp [pointsColumn, Nat.testBit_two_pow, ih, eq_comm]


theorem orbitInputBits (g : Nat) (hg : g < 32768) : packBits [g.testBit 0, g.testBit 1, g.testBit 2, g.testBit 3, g.testBit 4, g.testBit 5, g.testBit 6, g.testBit 7, g.testBit 8, g.testBit 9, g.testBit 10, g.testBit 11, g.testBit 12, g.testBit 13, g.testBit 14] = g := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [bit_read]
  by_cases hi : i < 15
  · interval_cases i <;> rfl
  · rw [List.getD_eq_default, Nat.testBit_lt_two_pow]
    · exact lt_of_lt_of_le hg (Nat.pow_le_pow_right (by decide) (Nat.le_of_not_gt hi) : 2^15 ≤ 2^i)
    · exact Nat.le_of_not_gt hi

def indexCompare (xs : List (Fin 15 × Fin 15)) : Nat :=
  cmpColumn (xs.map (fun p => (column p.1.val 15, column p.2.val 15))) 0

theorem indexRead (xs : List (Fin 15 × Fin 15)) (g : Nat) (hg : g < 32768) :
    (indexCompare xs).testBit g = decide (packBits (xs.map (fun p => g.testBit p.1.val)) <
      packBits (xs.map (fun p => g.testBit p.2.val))) := by
  have hv (j : Fin 15) : (column j.val 15).testBit g = g.testBit j.val := column_read 15 _ _ j.isLt hg
  simp [indexCompare, cmpColumn_read _ _ _ hg, List.map_map, Function.comp_def, hv, cmpNum]

def columnOrder0 : List (Fin 15 × Fin 15) := [(1,0),(2,1),(3,2),(4,3),(0,4),(9,5),(10,6),(11,7),(5,8),(12,9),(13,10),(6,11),(14,12),(7,13),(8,14)]

theorem orderRead0 (g : Nat) (hg : g < 32768) : (indexCompare columnOrder0).testBit g = decide (move g perm0 < g) := by
  rw [indexRead _ _ hg]
  change decide (packBits [g.testBit 1, g.testBit 2, g.testBit 3, g.testBit 4, g.testBit 0, g.testBit 9, g.testBit 10, g.testBit 11, g.testBit 5, g.testBit 12, g.testBit 13, g.testBit 6, g.testBit 14, g.testBit 7, g.testBit 8] < packBits [g.testBit 0, g.testBit 1, g.testBit 2, g.testBit 3, g.testBit 4, g.testBit 5, g.testBit 6, g.testBit 7, g.testBit 8, g.testBit 9, g.testBit 10, g.testBit 11, g.testBit 12, g.testBit 13, g.testBit 14]) = decide (packBits [decide (g.testBit 1 = true ∧ (0 : Fin 6) ≠ 2), decide (g.testBit 2 = true ∧ (0 : Fin 6) ≠ 3), decide (g.testBit 3 = true ∧ (0 : Fin 6) ≠ 4), decide (g.testBit 4 = true ∧ (0 : Fin 6) ≠ 5), decide (g.testBit 0 = true ∧ (0 : Fin 6) ≠ 1), decide (g.testBit 9 = true ∧ (2 : Fin 6) ≠ 3), decide (g.testBit 10 = true ∧ (2 : Fin 6) ≠ 4), decide (g.testBit 11 = true ∧ (2 : Fin 6) ≠ 5), decide (g.testBit 5 = true ∧ (2 : Fin 6) ≠ 1), decide (g.testBit 12 = true ∧ (3 : Fin 6) ≠ 4), decide (g.testBit 13 = true ∧ (3 : Fin 6) ≠ 5), decide (g.testBit 6 = true ∧ (3 : Fin 6) ≠ 1), decide (g.testBit 14 = true ∧ (4 : Fin 6) ≠ 5), decide (g.testBit 7 = true ∧ (4 : Fin 6) ≠ 1), decide (g.testBit 8 = true ∧ (5 : Fin 6) ≠ 1)] < g)
  rw [orbitInputBits _ hg]
  simp

def columnOrder1 : List (Fin 15 × Fin 15) := [(0,0),(5,1),(6,2),(7,3),(8,4),(1,5),(2,6),(3,7),(4,8),(9,9),(10,10),(11,11),(12,12),(13,13),(14,14)]

theorem orderRead1 (g : Nat) (hg : g < 32768) : (indexCompare columnOrder1).testBit g = decide (move g perm1 < g) := by
  rw [indexRead _ _ hg]
  change decide (packBits [g.testBit 0, g.testBit 5, g.testBit 6, g.testBit 7, g.testBit 8, g.testBit 1, g.testBit 2, g.testBit 3, g.testBit 4, g.testBit 9, g.testBit 10, g.testBit 11, g.testBit 12, g.testBit 13, g.testBit 14] < packBits [g.testBit 0, g.testBit 1, g.testBit 2, g.testBit 3, g.testBit 4, g.testBit 5, g.testBit 6, g.testBit 7, g.testBit 8, g.testBit 9, g.testBit 10, g.testBit 11, g.testBit 12, g.testBit 13, g.testBit 14]) = decide (packBits [decide (g.testBit 0 = true ∧ (1 : Fin 6) ≠ 0), decide (g.testBit 5 = true ∧ (1 : Fin 6) ≠ 2), decide (g.testBit 6 = true ∧ (1 : Fin 6) ≠ 3), decide (g.testBit 7 = true ∧ (1 : Fin 6) ≠ 4), decide (g.testBit 8 = true ∧ (1 : Fin 6) ≠ 5), decide (g.testBit 1 = true ∧ (0 : Fin 6) ≠ 2), decide (g.testBit 2 = true ∧ (0 : Fin 6) ≠ 3), decide (g.testBit 3 = true ∧ (0 : Fin 6) ≠ 4), decide (g.testBit 4 = true ∧ (0 : Fin 6) ≠ 5), decide (g.testBit 9 = true ∧ (2 : Fin 6) ≠ 3), decide (g.testBit 10 = true ∧ (2 : Fin 6) ≠ 4), decide (g.testBit 11 = true ∧ (2 : Fin 6) ≠ 5), decide (g.testBit 12 = true ∧ (3 : Fin 6) ≠ 4), decide (g.testBit 13 = true ∧ (3 : Fin 6) ≠ 5), decide (g.testBit 14 = true ∧ (4 : Fin 6) ≠ 5)] < g)
  rw [orbitInputBits _ hg]
  simp

def columnOrder2 : List (Fin 15 × Fin 15) := [(0,0),(1,1),(2,2),(4,3),(3,4),(5,5),(6,6),(8,7),(7,8),(9,9),(11,10),(10,11),(13,12),(12,13),(14,14)]

theorem orderRead2 (g : Nat) (hg : g < 32768) : (indexCompare columnOrder2).testBit g = decide (move g perm2 < g) := by
  rw [indexRead _ _ hg]
  change decide (packBits [g.testBit 0, g.testBit 1, g.testBit 2, g.testBit 4, g.testBit 3, g.testBit 5, g.testBit 6, g.testBit 8, g.testBit 7, g.testBit 9, g.testBit 11, g.testBit 10, g.testBit 13, g.testBit 12, g.testBit 14] < packBits [g.testBit 0, g.testBit 1, g.testBit 2, g.testBit 3, g.testBit 4, g.testBit 5, g.testBit 6, g.testBit 7, g.testBit 8, g.testBit 9, g.testBit 10, g.testBit 11, g.testBit 12, g.testBit 13, g.testBit 14]) = decide (packBits [decide (g.testBit 0 = true ∧ (0 : Fin 6) ≠ 1), decide (g.testBit 1 = true ∧ (0 : Fin 6) ≠ 2), decide (g.testBit 2 = true ∧ (0 : Fin 6) ≠ 3), decide (g.testBit 4 = true ∧ (0 : Fin 6) ≠ 5), decide (g.testBit 3 = true ∧ (0 : Fin 6) ≠ 4), decide (g.testBit 5 = true ∧ (1 : Fin 6) ≠ 2), decide (g.testBit 6 = true ∧ (1 : Fin 6) ≠ 3), decide (g.testBit 8 = true ∧ (1 : Fin 6) ≠ 5), decide (g.testBit 7 = true ∧ (1 : Fin 6) ≠ 4), decide (g.testBit 9 = true ∧ (2 : Fin 6) ≠ 3), decide (g.testBit 11 = true ∧ (2 : Fin 6) ≠ 5), decide (g.testBit 10 = true ∧ (2 : Fin 6) ≠ 4), decide (g.testBit 13 = true ∧ (3 : Fin 6) ≠ 5), decide (g.testBit 12 = true ∧ (3 : Fin 6) ≠ 4), decide (g.testBit 14 = true ∧ (5 : Fin 6) ≠ 4)] < g)
  rw [orbitInputBits _ hg]
  simp

def columnOrder3 : List (Fin 15 × Fin 15) := [(0,0),(1,1),(3,2),(2,3),(4,4),(5,5),(7,6),(6,7),(8,8),(10,9),(9,10),(11,11),(12,12),(14,13),(13,14)]

theorem orderRead3 (g : Nat) (hg : g < 32768) : (indexCompare columnOrder3).testBit g = decide (move g perm3 < g) := by
  rw [indexRead _ _ hg]
  change decide (packBits [g.testBit 0, g.testBit 1, g.testBit 3, g.testBit 2, g.testBit 4, g.testBit 5, g.testBit 7, g.testBit 6, g.testBit 8, g.testBit 10, g.testBit 9, g.testBit 11, g.testBit 12, g.testBit 14, g.testBit 13] < packBits [g.testBit 0, g.testBit 1, g.testBit 2, g.testBit 3, g.testBit 4, g.testBit 5, g.testBit 6, g.testBit 7, g.testBit 8, g.testBit 9, g.testBit 10, g.testBit 11, g.testBit 12, g.testBit 13, g.testBit 14]) = decide (packBits [decide (g.testBit 0 = true ∧ (0 : Fin 6) ≠ 1), decide (g.testBit 1 = true ∧ (0 : Fin 6) ≠ 2), decide (g.testBit 3 = true ∧ (0 : Fin 6) ≠ 4), decide (g.testBit 2 = true ∧ (0 : Fin 6) ≠ 3), decide (g.testBit 4 = true ∧ (0 : Fin 6) ≠ 5), decide (g.testBit 5 = true ∧ (1 : Fin 6) ≠ 2), decide (g.testBit 7 = true ∧ (1 : Fin 6) ≠ 4), decide (g.testBit 6 = true ∧ (1 : Fin 6) ≠ 3), decide (g.testBit 8 = true ∧ (1 : Fin 6) ≠ 5), decide (g.testBit 10 = true ∧ (2 : Fin 6) ≠ 4), decide (g.testBit 9 = true ∧ (2 : Fin 6) ≠ 3), decide (g.testBit 11 = true ∧ (2 : Fin 6) ≠ 5), decide (g.testBit 12 = true ∧ (4 : Fin 6) ≠ 3), decide (g.testBit 14 = true ∧ (4 : Fin 6) ≠ 5), decide (g.testBit 13 = true ∧ (3 : Fin 6) ≠ 5)] < g)
  rw [orbitInputBits _ hg]
  simp

def columnOrder4 : List (Fin 15 × Fin 15) := [(2,0),(0,1),(1,2),(4,3),(3,4),(6,5),(9,6),(13,7),(12,8),(5,9),(8,10),(7,11),(11,12),(10,13),(14,14)]

theorem orderRead4 (g : Nat) (hg : g < 32768) : (indexCompare columnOrder4).testBit g = decide (move g perm4 < g) := by
  rw [indexRead _ _ hg]
  change decide (packBits [g.testBit 2, g.testBit 0, g.testBit 1, g.testBit 4, g.testBit 3, g.testBit 6, g.testBit 9, g.testBit 13, g.testBit 12, g.testBit 5, g.testBit 8, g.testBit 7, g.testBit 11, g.testBit 10, g.testBit 14] < packBits [g.testBit 0, g.testBit 1, g.testBit 2, g.testBit 3, g.testBit 4, g.testBit 5, g.testBit 6, g.testBit 7, g.testBit 8, g.testBit 9, g.testBit 10, g.testBit 11, g.testBit 12, g.testBit 13, g.testBit 14]) = decide (packBits [decide (g.testBit 2 = true ∧ (0 : Fin 6) ≠ 3), decide (g.testBit 0 = true ∧ (0 : Fin 6) ≠ 1), decide (g.testBit 1 = true ∧ (0 : Fin 6) ≠ 2), decide (g.testBit 4 = true ∧ (0 : Fin 6) ≠ 5), decide (g.testBit 3 = true ∧ (0 : Fin 6) ≠ 4), decide (g.testBit 6 = true ∧ (3 : Fin 6) ≠ 1), decide (g.testBit 9 = true ∧ (3 : Fin 6) ≠ 2), decide (g.testBit 13 = true ∧ (3 : Fin 6) ≠ 5), decide (g.testBit 12 = true ∧ (3 : Fin 6) ≠ 4), decide (g.testBit 5 = true ∧ (1 : Fin 6) ≠ 2), decide (g.testBit 8 = true ∧ (1 : Fin 6) ≠ 5), decide (g.testBit 7 = true ∧ (1 : Fin 6) ≠ 4), decide (g.testBit 11 = true ∧ (2 : Fin 6) ≠ 5), decide (g.testBit 10 = true ∧ (2 : Fin 6) ≠ 4), decide (g.testBit 14 = true ∧ (5 : Fin 6) ≠ 4)] < g)
  rw [orbitInputBits _ hg]
  simp

def columnOrder5 : List (Fin 15 × Fin 15) := [(1,0),(0,1),(3,2),(2,3),(4,4),(5,5),(10,6),(9,7),(11,8),(7,9),(6,10),(8,11),(12,12),(14,13),(13,14)]

theorem orderRead5 (g : Nat) (hg : g < 32768) : (indexCompare columnOrder5).testBit g = decide (move g perm5 < g) := by
  rw [indexRead _ _ hg]
  change decide (packBits [g.testBit 1, g.testBit 0, g.testBit 3, g.testBit 2, g.testBit 4, g.testBit 5, g.testBit 10, g.testBit 9, g.testBit 11, g.testBit 7, g.testBit 6, g.testBit 8, g.testBit 12, g.testBit 14, g.testBit 13] < packBits [g.testBit 0, g.testBit 1, g.testBit 2, g.testBit 3, g.testBit 4, g.testBit 5, g.testBit 6, g.testBit 7, g.testBit 8, g.testBit 9, g.testBit 10, g.testBit 11, g.testBit 12, g.testBit 13, g.testBit 14]) = decide (packBits [decide (g.testBit 1 = true ∧ (0 : Fin 6) ≠ 2), decide (g.testBit 0 = true ∧ (0 : Fin 6) ≠ 1), decide (g.testBit 3 = true ∧ (0 : Fin 6) ≠ 4), decide (g.testBit 2 = true ∧ (0 : Fin 6) ≠ 3), decide (g.testBit 4 = true ∧ (0 : Fin 6) ≠ 5), decide (g.testBit 5 = true ∧ (2 : Fin 6) ≠ 1), decide (g.testBit 10 = true ∧ (2 : Fin 6) ≠ 4), decide (g.testBit 9 = true ∧ (2 : Fin 6) ≠ 3), decide (g.testBit 11 = true ∧ (2 : Fin 6) ≠ 5), decide (g.testBit 7 = true ∧ (1 : Fin 6) ≠ 4), decide (g.testBit 6 = true ∧ (1 : Fin 6) ≠ 3), decide (g.testBit 8 = true ∧ (1 : Fin 6) ≠ 5), decide (g.testBit 12 = true ∧ (4 : Fin 6) ≠ 3), decide (g.testBit 14 = true ∧ (4 : Fin 6) ≠ 5), decide (g.testBit 13 = true ∧ (3 : Fin 6) ≠ 5)] < g)
  rw [orbitInputBits _ hg]
  simp

def columnOrder6 : List (Fin 15 × Fin 15) := [(0,0),(2,1),(1,2),(3,3),(4,4),(6,5),(5,6),(7,7),(8,8),(9,9),(12,10),(13,11),(10,12),(11,13),(14,14)]

theorem orderRead6 (g : Nat) (hg : g < 32768) : (indexCompare columnOrder6).testBit g = decide (move g perm6 < g) := by
  rw [indexRead _ _ hg]
  change decide (packBits [g.testBit 0, g.testBit 2, g.testBit 1, g.testBit 3, g.testBit 4, g.testBit 6, g.testBit 5, g.testBit 7, g.testBit 8, g.testBit 9, g.testBit 12, g.testBit 13, g.testBit 10, g.testBit 11, g.testBit 14] < packBits [g.testBit 0, g.testBit 1, g.testBit 2, g.testBit 3, g.testBit 4, g.testBit 5, g.testBit 6, g.testBit 7, g.testBit 8, g.testBit 9, g.testBit 10, g.testBit 11, g.testBit 12, g.testBit 13, g.testBit 14]) = decide (packBits [decide (g.testBit 0 = true ∧ (0 : Fin 6) ≠ 1), decide (g.testBit 2 = true ∧ (0 : Fin 6) ≠ 3), decide (g.testBit 1 = true ∧ (0 : Fin 6) ≠ 2), decide (g.testBit 3 = true ∧ (0 : Fin 6) ≠ 4), decide (g.testBit 4 = true ∧ (0 : Fin 6) ≠ 5), decide (g.testBit 6 = true ∧ (1 : Fin 6) ≠ 3), decide (g.testBit 5 = true ∧ (1 : Fin 6) ≠ 2), decide (g.testBit 7 = true ∧ (1 : Fin 6) ≠ 4), decide (g.testBit 8 = true ∧ (1 : Fin 6) ≠ 5), decide (g.testBit 9 = true ∧ (3 : Fin 6) ≠ 2), decide (g.testBit 12 = true ∧ (3 : Fin 6) ≠ 4), decide (g.testBit 13 = true ∧ (3 : Fin 6) ≠ 5), decide (g.testBit 10 = true ∧ (2 : Fin 6) ≠ 4), decide (g.testBit 11 = true ∧ (2 : Fin 6) ≠ 5), decide (g.testBit 14 = true ∧ (4 : Fin 6) ≠ 5)] < g)
  rw [orbitInputBits _ hg]
  simp

def columnOrder7 : List (Fin 15 × Fin 15) := [(1,0),(0,1),(2,2),(4,3),(3,4),(5,5),(9,6),(11,7),(10,8),(6,9),(8,10),(7,11),(13,12),(12,13),(14,14)]

theorem orderRead7 (g : Nat) (hg : g < 32768) : (indexCompare columnOrder7).testBit g = decide (move g perm7 < g) := by
  rw [indexRead _ _ hg]
  change decide (packBits [g.testBit 1, g.testBit 0, g.testBit 2, g.testBit 4, g.testBit 3, g.testBit 5, g.testBit 9, g.testBit 11, g.testBit 10, g.testBit 6, g.testBit 8, g.testBit 7, g.testBit 13, g.testBit 12, g.testBit 14] < packBits [g.testBit 0, g.testBit 1, g.testBit 2, g.testBit 3, g.testBit 4, g.testBit 5, g.testBit 6, g.testBit 7, g.testBit 8, g.testBit 9, g.testBit 10, g.testBit 11, g.testBit 12, g.testBit 13, g.testBit 14]) = decide (packBits [decide (g.testBit 1 = true ∧ (0 : Fin 6) ≠ 2), decide (g.testBit 0 = true ∧ (0 : Fin 6) ≠ 1), decide (g.testBit 2 = true ∧ (0 : Fin 6) ≠ 3), decide (g.testBit 4 = true ∧ (0 : Fin 6) ≠ 5), decide (g.testBit 3 = true ∧ (0 : Fin 6) ≠ 4), decide (g.testBit 5 = true ∧ (2 : Fin 6) ≠ 1), decide (g.testBit 9 = true ∧ (2 : Fin 6) ≠ 3), decide (g.testBit 11 = true ∧ (2 : Fin 6) ≠ 5), decide (g.testBit 10 = true ∧ (2 : Fin 6) ≠ 4), decide (g.testBit 6 = true ∧ (1 : Fin 6) ≠ 3), decide (g.testBit 8 = true ∧ (1 : Fin 6) ≠ 5), decide (g.testBit 7 = true ∧ (1 : Fin 6) ≠ 4), decide (g.testBit 13 = true ∧ (3 : Fin 6) ≠ 5), decide (g.testBit 12 = true ∧ (3 : Fin 6) ≠ 4), decide (g.testBit 14 = true ∧ (5 : Fin 6) ≠ 4)] < g)
  rw [orbitInputBits _ hg]
  simp

def columnOrder8 : List (Fin 15 × Fin 15) := [(0,0),(6,1),(5,2),(8,3),(7,4),(2,5),(1,6),(4,7),(3,8),(9,9),(13,10),(12,11),(11,12),(10,13),(14,14)]

theorem orderRead8 (g : Nat) (hg : g < 32768) : (indexCompare columnOrder8).testBit g = decide (move g perm8 < g) := by
  rw [indexRead _ _ hg]
  change decide (packBits [g.testBit 0, g.testBit 6, g.testBit 5, g.testBit 8, g.testBit 7, g.testBit 2, g.testBit 1, g.testBit 4, g.testBit 3, g.testBit 9, g.testBit 13, g.testBit 12, g.testBit 11, g.testBit 10, g.testBit 14] < packBits [g.testBit 0, g.testBit 1, g.testBit 2, g.testBit 3, g.testBit 4, g.testBit 5, g.testBit 6, g.testBit 7, g.testBit 8, g.testBit 9, g.testBit 10, g.testBit 11, g.testBit 12, g.testBit 13, g.testBit 14]) = decide (packBits [decide (g.testBit 0 = true ∧ (1 : Fin 6) ≠ 0), decide (g.testBit 6 = true ∧ (1 : Fin 6) ≠ 3), decide (g.testBit 5 = true ∧ (1 : Fin 6) ≠ 2), decide (g.testBit 8 = true ∧ (1 : Fin 6) ≠ 5), decide (g.testBit 7 = true ∧ (1 : Fin 6) ≠ 4), decide (g.testBit 2 = true ∧ (0 : Fin 6) ≠ 3), decide (g.testBit 1 = true ∧ (0 : Fin 6) ≠ 2), decide (g.testBit 4 = true ∧ (0 : Fin 6) ≠ 5), decide (g.testBit 3 = true ∧ (0 : Fin 6) ≠ 4), decide (g.testBit 9 = true ∧ (3 : Fin 6) ≠ 2), decide (g.testBit 13 = true ∧ (3 : Fin 6) ≠ 5), decide (g.testBit 12 = true ∧ (3 : Fin 6) ≠ 4), decide (g.testBit 11 = true ∧ (2 : Fin 6) ≠ 5), decide (g.testBit 10 = true ∧ (2 : Fin 6) ≠ 4), decide (g.testBit 14 = true ∧ (5 : Fin 6) ≠ 4)] < g)
  rw [orbitInputBits _ hg]
  simp

def columnOrder9 : List (Fin 15 × Fin 15) := [(14,0),(11,1),(4,2),(13,3),(8,4),(10,5),(3,6),(12,7),(7,8),(1,9),(9,10),(5,11),(2,12),(0,13),(6,14)]

theorem orderRead9 (g : Nat) (hg : g < 32768) : (indexCompare columnOrder9).testBit g = decide (move g perm9 < g) := by
  rw [indexRead _ _ hg]
  change decide (packBits [g.testBit 14, g.testBit 11, g.testBit 4, g.testBit 13, g.testBit 8, g.testBit 10, g.testBit 3, g.testBit 12, g.testBit 7, g.testBit 1, g.testBit 9, g.testBit 5, g.testBit 2, g.testBit 0, g.testBit 6] < packBits [g.testBit 0, g.testBit 1, g.testBit 2, g.testBit 3, g.testBit 4, g.testBit 5, g.testBit 6, g.testBit 7, g.testBit 8, g.testBit 9, g.testBit 10, g.testBit 11, g.testBit 12, g.testBit 13, g.testBit 14]) = decide (packBits [decide (g.testBit 14 = true ∧ (5 : Fin 6) ≠ 4), decide (g.testBit 11 = true ∧ (5 : Fin 6) ≠ 2), decide (g.testBit 4 = true ∧ (5 : Fin 6) ≠ 0), decide (g.testBit 13 = true ∧ (5 : Fin 6) ≠ 3), decide (g.testBit 8 = true ∧ (5 : Fin 6) ≠ 1), decide (g.testBit 10 = true ∧ (4 : Fin 6) ≠ 2), decide (g.testBit 3 = true ∧ (4 : Fin 6) ≠ 0), decide (g.testBit 12 = true ∧ (4 : Fin 6) ≠ 3), decide (g.testBit 7 = true ∧ (4 : Fin 6) ≠ 1), decide (g.testBit 1 = true ∧ (2 : Fin 6) ≠ 0), decide (g.testBit 9 = true ∧ (2 : Fin 6) ≠ 3), decide (g.testBit 5 = true ∧ (2 : Fin 6) ≠ 1), decide (g.testBit 2 = true ∧ (0 : Fin 6) ≠ 3), decide (g.testBit 0 = true ∧ (0 : Fin 6) ≠ 1), decide (g.testBit 6 = true ∧ (3 : Fin 6) ≠ 1)] < g)
  rw [orbitInputBits _ hg]
  simp

def columnOrder10 : List (Fin 15 × Fin 15) := [(5,0),(0,1),(7,2),(8,3),(6,4),(1,5),(10,6),(11,7),(9,8),(3,9),(4,10),(2,11),(14,12),(12,13),(13,14)]

theorem orderRead10 (g : Nat) (hg : g < 32768) : (indexCompare columnOrder10).testBit g = decide (move g perm10 < g) := by
  rw [indexRead _ _ hg]
  change decide (packBits [g.testBit 5, g.testBit 0, g.testBit 7, g.testBit 8, g.testBit 6, g.testBit 1, g.testBit 10, g.testBit 11, g.testBit 9, g.testBit 3, g.testBit 4, g.testBit 2, g.testBit 14, g.testBit 12, g.testBit 13] < packBits [g.testBit 0, g.testBit 1, g.testBit 2, g.testBit 3, g.testBit 4, g.testBit 5, g.testBit 6, g.testBit 7, g.testBit 8, g.testBit 9, g.testBit 10, g.testBit 11, g.testBit 12, g.testBit 13, g.testBit 14]) = decide (packBits [decide (g.testBit 5 = true ∧ (1 : Fin 6) ≠ 2), decide (g.testBit 0 = true ∧ (1 : Fin 6) ≠ 0), decide (g.testBit 7 = true ∧ (1 : Fin 6) ≠ 4), decide (g.testBit 8 = true ∧ (1 : Fin 6) ≠ 5), decide (g.testBit 6 = true ∧ (1 : Fin 6) ≠ 3), decide (g.testBit 1 = true ∧ (2 : Fin 6) ≠ 0), decide (g.testBit 10 = true ∧ (2 : Fin 6) ≠ 4), decide (g.testBit 11 = true ∧ (2 : Fin 6) ≠ 5), decide (g.testBit 9 = true ∧ (2 : Fin 6) ≠ 3), decide (g.testBit 3 = true ∧ (0 : Fin 6) ≠ 4), decide (g.testBit 4 = true ∧ (0 : Fin 6) ≠ 5), decide (g.testBit 2 = true ∧ (0 : Fin 6) ≠ 3), decide (g.testBit 14 = true ∧ (4 : Fin 6) ≠ 5), decide (g.testBit 12 = true ∧ (4 : Fin 6) ≠ 3), decide (g.testBit 13 = true ∧ (5 : Fin 6) ≠ 3)] < g)
  rw [orbitInputBits _ hg]
  simp

def columnOrder11 : List (Fin 15 × Fin 15) := [(2,0),(3,1),(1,2),(0,3),(4,4),(12,5),(9,6),(6,7),(13,8),(10,9),(7,10),(14,11),(5,12),(11,13),(8,14)]

theorem orderRead11 (g : Nat) (hg : g < 32768) : (indexCompare columnOrder11).testBit g = decide (move g perm11 < g) := by
  rw [indexRead _ _ hg]
  change decide (packBits [g.testBit 2, g.testBit 3, g.testBit 1, g.testBit 0, g.testBit 4, g.testBit 12, g.testBit 9, g.testBit 6, g.testBit 13, g.testBit 10, g.testBit 7, g.testBit 14, g.testBit 5, g.testBit 11, g.testBit 8] < packBits [g.testBit 0, g.testBit 1, g.testBit 2, g.testBit 3, g.testBit 4, g.testBit 5, g.testBit 6, g.testBit 7, g.testBit 8, g.testBit 9, g.testBit 10, g.testBit 11, g.testBit 12, g.testBit 13, g.testBit 14]) = decide (packBits [decide (g.testBit 2 = true ∧ (0 : Fin 6) ≠ 3), decide (g.testBit 3 = true ∧ (0 : Fin 6) ≠ 4), decide (g.testBit 1 = true ∧ (0 : Fin 6) ≠ 2), decide (g.testBit 0 = true ∧ (0 : Fin 6) ≠ 1), decide (g.testBit 4 = true ∧ (0 : Fin 6) ≠ 5), decide (g.testBit 12 = true ∧ (3 : Fin 6) ≠ 4), decide (g.testBit 9 = true ∧ (3 : Fin 6) ≠ 2), decide (g.testBit 6 = true ∧ (3 : Fin 6) ≠ 1), decide (g.testBit 13 = true ∧ (3 : Fin 6) ≠ 5), decide (g.testBit 10 = true ∧ (4 : Fin 6) ≠ 2), decide (g.testBit 7 = true ∧ (4 : Fin 6) ≠ 1), decide (g.testBit 14 = true ∧ (4 : Fin 6) ≠ 5), decide (g.testBit 5 = true ∧ (2 : Fin 6) ≠ 1), decide (g.testBit 11 = true ∧ (2 : Fin 6) ≠ 5), decide (g.testBit 8 = true ∧ (1 : Fin 6) ≠ 5)] < g)
  rw [orbitInputBits _ hg]
  simp

def columnOrder12 : List (Fin 15 × Fin 15) := [(0,0),(2,1),(1,2),(4,3),(3,4),(6,5),(5,6),(8,7),(7,8),(9,9),(13,10),(12,11),(11,12),(10,13),(14,14)]

theorem orderRead12 (g : Nat) (hg : g < 32768) : (indexCompare columnOrder12).testBit g = decide (move g perm12 < g) := by
  rw [indexRead _ _ hg]
  change decide (packBits [g.testBit 0, g.testBit 2, g.testBit 1, g.testBit 4, g.testBit 3, g.testBit 6, g.testBit 5, g.testBit 8, g.testBit 7, g.testBit 9, g.testBit 13, g.testBit 12, g.testBit 11, g.testBit 10, g.testBit 14] < packBits [g.testBit 0, g.testBit 1, g.testBit 2, g.testBit 3, g.testBit 4, g.testBit 5, g.testBit 6, g.testBit 7, g.testBit 8, g.testBit 9, g.testBit 10, g.testBit 11, g.testBit 12, g.testBit 13, g.testBit 14]) = decide (packBits [decide (g.testBit 0 = true ∧ (0 : Fin 6) ≠ 1), decide (g.testBit 2 = true ∧ (0 : Fin 6) ≠ 3), decide (g.testBit 1 = true ∧ (0 : Fin 6) ≠ 2), decide (g.testBit 4 = true ∧ (0 : Fin 6) ≠ 5), decide (g.testBit 3 = true ∧ (0 : Fin 6) ≠ 4), decide (g.testBit 6 = true ∧ (1 : Fin 6) ≠ 3), decide (g.testBit 5 = true ∧ (1 : Fin 6) ≠ 2), decide (g.testBit 8 = true ∧ (1 : Fin 6) ≠ 5), decide (g.testBit 7 = true ∧ (1 : Fin 6) ≠ 4), decide (g.testBit 9 = true ∧ (3 : Fin 6) ≠ 2), decide (g.testBit 13 = true ∧ (3 : Fin 6) ≠ 5), decide (g.testBit 12 = true ∧ (3 : Fin 6) ≠ 4), decide (g.testBit 11 = true ∧ (2 : Fin 6) ≠ 5), decide (g.testBit 10 = true ∧ (2 : Fin 6) ≠ 4), decide (g.testBit 14 = true ∧ (5 : Fin 6) ≠ 4)] < g)
  rw [orbitInputBits _ hg]
  simp

def columnOrder13 : List (Fin 15 × Fin 15) := [(0,0),(5,1),(7,2),(6,3),(8,4),(1,5),(3,6),(2,7),(4,8),(10,9),(9,10),(11,11),(12,12),(14,13),(13,14)]

theorem orderRead13 (g : Nat) (hg : g < 32768) : (indexCompare columnOrder13).testBit g = decide (move g perm13 < g) := by
  rw [indexRead _ _ hg]
  change decide (packBits [g.testBit 0, g.testBit 5, g.testBit 7, g.testBit 6, g.testBit 8, g.testBit 1, g.testBit 3, g.testBit 2, g.testBit 4, g.testBit 10, g.testBit 9, g.testBit 11, g.testBit 12, g.testBit 14, g.testBit 13] < packBits [g.testBit 0, g.testBit 1, g.testBit 2, g.testBit 3, g.testBit 4, g.testBit 5, g.testBit 6, g.testBit 7, g.testBit 8, g.testBit 9, g.testBit 10, g.testBit 11, g.testBit 12, g.testBit 13, g.testBit 14]) = decide (packBits [decide (g.testBit 0 = true ∧ (1 : Fin 6) ≠ 0), decide (g.testBit 5 = true ∧ (1 : Fin 6) ≠ 2), decide (g.testBit 7 = true ∧ (1 : Fin 6) ≠ 4), decide (g.testBit 6 = true ∧ (1 : Fin 6) ≠ 3), decide (g.testBit 8 = true ∧ (1 : Fin 6) ≠ 5), decide (g.testBit 1 = true ∧ (0 : Fin 6) ≠ 2), decide (g.testBit 3 = true ∧ (0 : Fin 6) ≠ 4), decide (g.testBit 2 = true ∧ (0 : Fin 6) ≠ 3), decide (g.testBit 4 = true ∧ (0 : Fin 6) ≠ 5), decide (g.testBit 10 = true ∧ (2 : Fin 6) ≠ 4), decide (g.testBit 9 = true ∧ (2 : Fin 6) ≠ 3), decide (g.testBit 11 = true ∧ (2 : Fin 6) ≠ 5), decide (g.testBit 12 = true ∧ (4 : Fin 6) ≠ 3), decide (g.testBit 14 = true ∧ (4 : Fin 6) ≠ 5), decide (g.testBit 13 = true ∧ (3 : Fin 6) ≠ 5)] < g)
  rw [orbitInputBits _ hg]
  simp

def columnOrder14 : List (Fin 15 × Fin 15) := [(9,0),(1,1),(5,2),(11,3),(10,4),(2,5),(6,6),(13,7),(12,8),(0,9),(4,10),(3,11),(8,12),(7,13),(14,14)]

theorem orderRead14 (g : Nat) (hg : g < 32768) : (indexCompare columnOrder14).testBit g = decide (move g perm14 < g) := by
  rw [indexRead _ _ hg]
  change decide (packBits [g.testBit 9, g.testBit 1, g.testBit 5, g.testBit 11, g.testBit 10, g.testBit 2, g.testBit 6, g.testBit 13, g.testBit 12, g.testBit 0, g.testBit 4, g.testBit 3, g.testBit 8, g.testBit 7, g.testBit 14] < packBits [g.testBit 0, g.testBit 1, g.testBit 2, g.testBit 3, g.testBit 4, g.testBit 5, g.testBit 6, g.testBit 7, g.testBit 8, g.testBit 9, g.testBit 10, g.testBit 11, g.testBit 12, g.testBit 13, g.testBit 14]) = decide (packBits [decide (g.testBit 9 = true ∧ (2 : Fin 6) ≠ 3), decide (g.testBit 1 = true ∧ (2 : Fin 6) ≠ 0), decide (g.testBit 5 = true ∧ (2 : Fin 6) ≠ 1), decide (g.testBit 11 = true ∧ (2 : Fin 6) ≠ 5), decide (g.testBit 10 = true ∧ (2 : Fin 6) ≠ 4), decide (g.testBit 2 = true ∧ (3 : Fin 6) ≠ 0), decide (g.testBit 6 = true ∧ (3 : Fin 6) ≠ 1), decide (g.testBit 13 = true ∧ (3 : Fin 6) ≠ 5), decide (g.testBit 12 = true ∧ (3 : Fin 6) ≠ 4), decide (g.testBit 0 = true ∧ (0 : Fin 6) ≠ 1), decide (g.testBit 4 = true ∧ (0 : Fin 6) ≠ 5), decide (g.testBit 3 = true ∧ (0 : Fin 6) ≠ 4), decide (g.testBit 8 = true ∧ (1 : Fin 6) ≠ 5), decide (g.testBit 7 = true ∧ (1 : Fin 6) ≠ 4), decide (g.testBit 14 = true ∧ (5 : Fin 6) ≠ 4)] < g)
  rw [orbitInputBits _ hg]
  simp

def columnOrder15 : List (Fin 15 × Fin 15) := [(1,0),(0,1),(2,2),(3,3),(4,4),(5,5),(9,6),(10,7),(11,8),(6,9),(7,10),(8,11),(12,12),(13,13),(14,14)]

theorem orderRead15 (g : Nat) (hg : g < 32768) : (indexCompare columnOrder15).testBit g = decide (move g perm15 < g) := by
  rw [indexRead _ _ hg]
  change decide (packBits [g.testBit 1, g.testBit 0, g.testBit 2, g.testBit 3, g.testBit 4, g.testBit 5, g.testBit 9, g.testBit 10, g.testBit 11, g.testBit 6, g.testBit 7, g.testBit 8, g.testBit 12, g.testBit 13, g.testBit 14] < packBits [g.testBit 0, g.testBit 1, g.testBit 2, g.testBit 3, g.testBit 4, g.testBit 5, g.testBit 6, g.testBit 7, g.testBit 8, g.testBit 9, g.testBit 10, g.testBit 11, g.testBit 12, g.testBit 13, g.testBit 14]) = decide (packBits [decide (g.testBit 1 = true ∧ (0 : Fin 6) ≠ 2), decide (g.testBit 0 = true ∧ (0 : Fin 6) ≠ 1), decide (g.testBit 2 = true ∧ (0 : Fin 6) ≠ 3), decide (g.testBit 3 = true ∧ (0 : Fin 6) ≠ 4), decide (g.testBit 4 = true ∧ (0 : Fin 6) ≠ 5), decide (g.testBit 5 = true ∧ (2 : Fin 6) ≠ 1), decide (g.testBit 9 = true ∧ (2 : Fin 6) ≠ 3), decide (g.testBit 10 = true ∧ (2 : Fin 6) ≠ 4), decide (g.testBit 11 = true ∧ (2 : Fin 6) ≠ 5), decide (g.testBit 6 = true ∧ (1 : Fin 6) ≠ 3), decide (g.testBit 7 = true ∧ (1 : Fin 6) ≠ 4), decide (g.testBit 8 = true ∧ (1 : Fin 6) ≠ 5), decide (g.testBit 12 = true ∧ (3 : Fin 6) ≠ 4), decide (g.testBit 13 = true ∧ (3 : Fin 6) ≠ 5), decide (g.testBit 14 = true ∧ (4 : Fin 6) ≠ 5)] < g)
  rw [orbitInputBits _ hg]
  simp

def columnOrder16 : List (Fin 15 × Fin 15) := [(12,0),(13,1),(2,2),(6,3),(9,4),(14,5),(3,6),(7,7),(10,8),(4,9),(8,10),(11,11),(0,12),(1,13),(5,14)]

theorem orderRead16 (g : Nat) (hg : g < 32768) : (indexCompare columnOrder16).testBit g = decide (move g perm16 < g) := by
  rw [indexRead _ _ hg]
  change decide (packBits [g.testBit 12, g.testBit 13, g.testBit 2, g.testBit 6, g.testBit 9, g.testBit 14, g.testBit 3, g.testBit 7, g.testBit 10, g.testBit 4, g.testBit 8, g.testBit 11, g.testBit 0, g.testBit 1, g.testBit 5] < packBits [g.testBit 0, g.testBit 1, g.testBit 2, g.testBit 3, g.testBit 4, g.testBit 5, g.testBit 6, g.testBit 7, g.testBit 8, g.testBit 9, g.testBit 10, g.testBit 11, g.testBit 12, g.testBit 13, g.testBit 14]) = decide (packBits [decide (g.testBit 12 = true ∧ (3 : Fin 6) ≠ 4), decide (g.testBit 13 = true ∧ (3 : Fin 6) ≠ 5), decide (g.testBit 2 = true ∧ (3 : Fin 6) ≠ 0), decide (g.testBit 6 = true ∧ (3 : Fin 6) ≠ 1), decide (g.testBit 9 = true ∧ (3 : Fin 6) ≠ 2), decide (g.testBit 14 = true ∧ (4 : Fin 6) ≠ 5), decide (g.testBit 3 = true ∧ (4 : Fin 6) ≠ 0), decide (g.testBit 7 = true ∧ (4 : Fin 6) ≠ 1), decide (g.testBit 10 = true ∧ (4 : Fin 6) ≠ 2), decide (g.testBit 4 = true ∧ (5 : Fin 6) ≠ 0), decide (g.testBit 8 = true ∧ (5 : Fin 6) ≠ 1), decide (g.testBit 11 = true ∧ (5 : Fin 6) ≠ 2), decide (g.testBit 0 = true ∧ (0 : Fin 6) ≠ 1), decide (g.testBit 1 = true ∧ (0 : Fin 6) ≠ 2), decide (g.testBit 5 = true ∧ (1 : Fin 6) ≠ 2)] < g)
  rw [orbitInputBits _ hg]
  simp

def orbitColumn : Nat := (indexCompare columnOrder0 ||| indexCompare columnOrder1 ||| indexCompare columnOrder2 ||| indexCompare columnOrder3 ||| indexCompare columnOrder4 ||| indexCompare columnOrder5 ||| indexCompare columnOrder6 ||| indexCompare columnOrder7 ||| indexCompare columnOrder8 ||| indexCompare columnOrder9 ||| indexCompare columnOrder10 ||| indexCompare columnOrder11 ||| indexCompare columnOrder12 ||| indexCompare columnOrder13 ||| indexCompare columnOrder14 ||| indexCompare columnOrder15 ||| indexCompare columnOrder16) ||| pointsColumn repList

theorem orbitColumn_read (g : Nat) (hg : g < 32768) : orbitColumn.testBit g = orbitCheck g := by
  simp only [orbitColumn, orbitCheck, smaller, Nat.testBit_or, pointsColumn_read, orderRead0 _ hg, orderRead1 _ hg, orderRead2 _ hg, orderRead3 _ hg, orderRead4 _ hg, orderRead5 _ hg, orderRead6 _ hg, orderRead7 _ hg, orderRead8 _ hg, orderRead9 _ hg, orderRead10 _ hg, orderRead11 _ hg, orderRead12 _ hg, orderRead13 _ hg, orderRead14 _ hg, orderRead15 _ hg, orderRead16 _ hg]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
theorem orbitColumn_full : orbitColumn = fullColumn := by decide +kernel

theorem orbitCertified (g : Fin 32768) : orbitCheck g.val = true := by
  rw [← orbitColumn_read _ g.isLt, orbitColumn_full, fullColumn, Nat.testBit_two_pow_sub_one]
  exact decide_eq_true g.isLt

open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit

abbrev pullCircuit (e : Equiv.Perm (Fin 6)) (C : AndCountCircuit 6) : AndCountCircuit 6 where
  size := C.size
  leftVars i := (C.leftVars i).map e.symm.toEmbedding
  leftGates := C.leftGates
  rightVars i := (C.rightVars i).map e.symm.toEmbedding
  rightGates := C.rightGates
  outVars := C.outVars.map e.symm.toEmbedding
  outGates := C.outGates

theorem pullMeet (e : Equiv.Perm (Fin 6)) (I B : Finset (Fin 6)) :
    (∃ v ∈ B.map e.symm.toEmbedding, v ∈ I) ↔ ∃ v ∈ B, v ∈ I.map e.toEmbedding := by
  constructor
  · rintro ⟨v, hb, hv⟩
    exact ⟨e v, Finset.mem_map_equiv.mp hb, Finset.mem_map.mpr ⟨v, hv, rfl⟩⟩
  · rintro ⟨v, hb, hv⟩
    exact ⟨e.symm v, Finset.mem_map.mpr ⟨v, hb, rfl⟩, Finset.mem_map_equiv.mp hv⟩

theorem pullSide {k : ℕ} (e : Equiv.Perm (Fin 6)) (I B : Finset (Fin 6))
    (F : Finset (Fin k)) (i : Fin k) (w : Fin k → Bool) :
    sideTrue I (B.map e.symm.toEmbedding) F i w = sideTrue (I.map e.toEmbedding) B F i w := by
  simp only [sideTrue, pullMeet]

theorem pullFuel (e : Equiv.Perm (Fin 6)) (C : AndCountCircuit 6) (I : Finset (Fin 6)) (d : ℕ) :
    (pullCircuit e C).gateValFuel I d = C.gateValFuel (I.map e.toEmbedding) d := by
  induction d with
  | zero => rfl
  | succ d ih =>
    funext i
    change (sideTrue I ((C.leftVars i).map e.symm.toEmbedding) (C.leftGates i) i
        ((pullCircuit e C).gateValFuel I d) && sideTrue I ((C.rightVars i).map e.symm.toEmbedding)
          (C.rightGates i) i ((pullCircuit e C).gateValFuel I d)) = _
    rw [ih, pullSide, pullSide]
    rfl

theorem pullEval (e : Equiv.Perm (Fin 6)) (C : AndCountCircuit 6) (I : Finset (Fin 6)) :
    (pullCircuit e C).eval I = C.eval (I.map e.toEmbedding) := by
  change decide ((∃ v ∈ C.outVars.map e.symm.toEmbedding, v ∈ I) ∨
      ∃ j ∈ C.outGates, (pullCircuit e C).gateValFuel I C.size j = true) =
    decide ((∃ v ∈ C.outVars, v ∈ I.map e.toEmbedding) ∨
      ∃ j ∈ C.outGates, C.gateValFuel (I.map e.toEmbedding) C.size j = true)
  simp only [pullMeet, pullFuel]

theorem solveRelabel (G : SimpleGraph (Fin 6)) (e : Equiv.Perm (Fin 6)) (g : Nat)
    (rel : Relabel G e g) (sol : Solves g) (C : AndCountCircuit 6)
    (hC : C.WellFormed ∧ (∀ I : Finset (Fin 6), (∀ v ∈ I, ∀ w ∈ I, ¬ G.Adj v w) →
      (∀ u, u ∉ I → ∃ v ∈ I, G.Adj u v) → C.eval I = false ∧
        ∀ u, u ∉ I → C.eval (insert u I) = true)) :
    ∃ (k : ℕ) (X Y : Fin k → Finset (Fin 6)), k ≤ C.size ∧
      (∀ i : Fin k, ∀ a ∈ X i, ∀ b ∈ Y i, G.Adj a b) ∧
      (∀ a b : Fin 6, G.Adj a b → ∃ i : Fin k,
        (a ∈ X i ∧ b ∈ Y i) ∨ (b ∈ X i ∧ a ∈ Y i)) := by
  have fit : Fits g (pullCircuit e C) := by
    intro I ind dom
    have ind' : ∀ a ∈ I.map e.toEmbedding, ∀ b ∈ I.map e.toEmbedding, ¬ G.Adj a b := by
      intro a ha b hb hadj
      apply ind (e.symm a) (Finset.mem_map_equiv.mp ha) (e.symm b) (Finset.mem_map_equiv.mp hb)
      exact (rel _ _).2 (by simpa using hadj)
    have dom' : ∀ a, a ∉ I.map e.toEmbedding → ∃ b ∈ I.map e.toEmbedding, G.Adj a b := by
      intro a ha
      obtain ⟨v, hv, hadj⟩ := dom (e.symm a) (fun h => ha (Finset.mem_map_equiv.mpr h))
      refine ⟨e v, Finset.mem_map.mpr ⟨v, hv, rfl⟩, ?_⟩
      simpa using (rel _ _).1 hadj
    obtain ⟨hneg, hpos⟩ := hC.2 (I.map e.toEmbedding) ind' dom'
    constructor
    · rwa [pullEval]
    · intro u hu
      rw [pullEval, Finset.map_insert]
      apply hpos
      simpa only [Finset.mem_map_equiv, Equiv.toEmbedding_apply, Equiv.symm_apply_apply] using hu
  obtain ⟨k, hsize, X, Y, cross, cover⟩ := sol (pullCircuit e C) hC.1 fit
  refine ⟨k, fun i => (X i).map e.toEmbedding, fun i => (Y i).map e.toEmbedding, hsize, ?_, ?_⟩
  · intro i a ha b hb
    have h := cross i (e.symm a) (Finset.mem_map_equiv.mp ha) (e.symm b) (Finset.mem_map_equiv.mp hb)
    simpa using (rel _ _).1 h
  · intro a b hab
    obtain ⟨i, h⟩ := cover (e.symm a) (e.symm b) ((rel _ _).2 (by simpa using hab))
    exact ⟨i, by simpa only [Finset.mem_map_equiv] using h⟩

end PEqualNP.Outside.L_meta_950

open PEqualNP.Outside.L_meta_950

theorem PEqualNP.Outside.L_meta_950 : ∀ (G : SimpleGraph (Fin 6)) (C : PEqualNP.AndCount.AndCountCircuit 6), C.WellFormed ∧ (∀ I : Finset (Fin 6), (∀ v ∈ I, ∀ w ∈ I, ¬ G.Adj v w) → (∀ u, u ∉ I → ∃ v ∈ I, G.Adj u v) → C.eval I = false ∧ ∀ u, u ∉ I → C.eval (insert u I) = true) → ∃ (k : ℕ) (X Y : Fin k → Finset (Fin 6)), k ≤ C.size ∧ (∀ i : Fin k, ∀ a ∈ X i, ∀ b ∈ Y i, G.Adj a b) ∧ (∀ a b : Fin 6, G.Adj a b → ∃ i : Fin k, (a ∈ X i ∧ b ∈ Y i) ∨ (b ∈ X i ∧ a ∈ Y i)) := by
  intro G C hC
  obtain ⟨g, hg, e, rel⟩ := representative orbitCertified G
  exact solveRelabel G e g rel (solveRep g hg) C hC
