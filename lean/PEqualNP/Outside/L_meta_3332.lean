import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_3332 :
  ∀ (x1 : (Fin (9 : ℕ) → Bool) → Bool),   (∀ (x2 : Fin (9 : ℕ)) (x3 : Bool), (x1 fun (x4 : Fin (9 : ℕ)) => Decidable.decide (x4 = x2) && x3) = Bool.false ∧ (x1 fun (x4 : Fin (9 : ℕ)) => !Decidable.decide (x4 = x2) || x3) = Bool.true) →     ∀ (x3 : ℕ) (x4 : Fin x3 → Bool) (x5 x6 : Fin x3 → ℕ × Bool) (x7 : ℕ × Bool) (x8 : (Fin (9 : ℕ) → Bool) → ℕ → Bool),       x7.1 < (10 : ℕ) + x3 →         (∀ (x10 : Fin (9 : ℕ) → Bool) (x11 : Fin (9 : ℕ)), x8 x10 ↑x11 = x10 x11) →           (∀ (x11 : Fin (9 : ℕ) → Bool), x8 x11 (9 : ℕ) = Bool.false) →             (∀ (x12 : Fin (9 : ℕ) → Bool) (x13 : Fin x3),                 have x14 : ℕ × Bool → Bool := fun (x14 : ℕ × Bool) => x8 x12 x14.1 ^^ x14.2;                 x8 x12 ((10 : ℕ) + ↑x13) = if x4 x13 = Bool.true then x14 (x5 x13) && x14 (x6 x13) else x14 (x5 x13) || x14 (x6 x13)) →               (∀ (x13 : Fin (9 : ℕ) → Bool), (x8 x13 x7.1 ^^ x7.2) = x1 x13) → ∃ (x14 : Fin x3), x7.1 = (10 : ℕ) + ↑x14 ∧ (9 : ℕ) ≤ (x5 x14).1 ∧ (9 : ℕ) ≤ (x6 x14).1 := by
  intro f hf n op l r out w hout_lt hbase h9 hgate hout
  classical
  let zero : Fin 9 → Bool := fun _ => false
  let unit : Fin 9 → Fin 9 → Bool := fun i j => decide (j = i)
  let counit : Fin 9 → Fin 9 → Bool := fun i j => !decide (j = i)
  let one : Fin 9 → Bool := fun _ => true
  have hf_zero : f zero = false := by
    have hfun : (fun j : Fin 9 => decide (j = (0 : Fin 9)) && false) = zero := by
      funext j; simp [zero]
    rw [← hfun]
    exact (hf (0 : Fin 9) false).1
  have hf_unit (a : Fin 9) : f (unit a) = false := by
    have hfun : (fun j : Fin 9 => decide (j = a) && true) = unit a := by
      funext j; simp [unit]
    rw [← hfun]
    exact (hf a true).1
  have hf_counit (a : Fin 9) : f (counit a) = true := by
    have hfun : (fun j : Fin 9 => !decide (j = a) || false) = counit a := by
      funext j; simp [counit]
    rw [← hfun]
    exact (hf a false).2
  have hf_one : f one = true := by
    have hfun : (fun j : Fin 9 => !decide (j = (0 : Fin 9)) || true) = one := by
      funext j; simp [one]
    rw [← hfun]
    exact (hf (0 : Fin 9) true).2
  have hout_ge : 10 ≤ out.1 := by
    by_contra hnot
    have hlt : out.1 < 10 := by omega
    have hle : out.1 ≤ 9 := by omega
    rcases lt_or_eq_of_le hle with hk | hk9
    · let k : Fin 9 := ⟨out.1, hk⟩
      have hwz : w zero out.1 = false := by
        have h := hbase zero k
        simpa [zero, k] using h
      have hzu := hout zero
      rw [hwz, hf_zero] at hzu
      have hphase : out.2 = false := by
        cases hb : out.2
        · rfl
        · simp [hb] at hzu
      have hwu : w (unit k) out.1 = true := by
        have h := hbase (unit k) k
        simpa [unit, k] using h
      have huu := hout (unit k)
      rw [hwu, hf_unit k, hphase] at huu
      exact Bool.false_ne_true (by simpa using huu.symm)
    · have hwz : w zero 9 = false := h9 zero
      have hzu := hout zero
      rw [hk9, hwz, hf_zero] at hzu
      have hphase : out.2 = false := by
        cases hb : out.2
        · rfl
        · simp [hb] at hzu
      have hwc : w (counit (0 : Fin 9)) 9 = false := h9 (counit (0 : Fin 9))
      have hcu := hout (counit (0 : Fin 9))
      rw [hk9, hwc, hf_counit (0 : Fin 9), hphase] at hcu
      simp at hcu
  have hout_sub : out.1 - 10 < n := by omega
  let i : Fin n := ⟨out.1 - 10, hout_sub⟩
  have hout_eq : out.1 = 10 + (i : ℕ) := by
    dsimp [i]
    omega
  have hout' (x : Fin 9 → Bool) : (w x (10 + (i : ℕ)) ^^ out.2) = f x := by
    simpa [hout_eq] using hout x
  have hg (x : Fin 9 → Bool) : w x (10 + (i : ℕ)) =
      if op i = true then (w x (l i).1 ^^ (l i).2) && (w x (r i).1 ^^ (r i).2)
      else (w x (l i).1 ^^ (l i).2) || (w x (r i).1 ^^ (r i).2) := by
    have h := hgate x i
    dsimp only at h
    exact h
  have prim_contra (a : ℕ) (ha : a < 9) (pa : Bool) (o : ℕ × Bool)
      (gate : ∀ x : Fin 9 → Bool, w x (10 + (i : ℕ)) =
        if op i = true then (w x a ^^ pa) && (w x o.1 ^^ o.2)
        else (w x a ^^ pa) || (w x o.1 ^^ o.2)) : False := by
    let ai : Fin 9 := ⟨a, ha⟩
    have hbase_a (x : Fin 9 → Bool) : w x a = x ai := by
      have h := hbase x ai
      simpa [ai] using h
    have key (x y : Fin 9 → Bool) (hxy : w x (10 + (i : ℕ)) = w y (10 + (i : ℕ))) :
        f x = f y := by
      rw [← hout' x, ← hout' y, hxy]
    cases pa
    · cases hop : op i
      · have hx : w (unit ai) (10 + (i : ℕ)) = true := by
          rw [gate (unit ai)]
          simp [hop, hbase_a (unit ai), unit]
        have hy : w one (10 + (i : ℕ)) = true := by
          rw [gate one]
          simp [hop, hbase_a one, one]
        have hff : f (unit ai) = f one := key (unit ai) one (by rw [hx, hy])
        rw [hf_unit ai, hf_one] at hff
        exact Bool.false_ne_true hff
      · have hx : w zero (10 + (i : ℕ)) = false := by
          rw [gate zero]
          simp [hop, hbase_a zero, zero]
        have hy : w (counit ai) (10 + (i : ℕ)) = false := by
          rw [gate (counit ai)]
          simp [hop, hbase_a (counit ai), counit]
        have hff : f zero = f (counit ai) := key zero (counit ai) (by rw [hx, hy])
        rw [hf_zero, hf_counit ai] at hff
        exact Bool.false_ne_true hff
    · cases hop : op i
      · have hx : w zero (10 + (i : ℕ)) = true := by
          rw [gate zero]
          simp [hop, hbase_a zero, zero]
        have hy : w (counit ai) (10 + (i : ℕ)) = true := by
          rw [gate (counit ai)]
          simp [hop, hbase_a (counit ai), counit]
        have hff : f zero = f (counit ai) := key zero (counit ai) (by rw [hx, hy])
        rw [hf_zero, hf_counit ai] at hff
        exact Bool.false_ne_true hff
      · have hx : w (unit ai) (10 + (i : ℕ)) = false := by
          rw [gate (unit ai)]
          simp [hop, hbase_a (unit ai), unit]
        have hy : w one (10 + (i : ℕ)) = false := by
          rw [gate one]
          simp [hop, hbase_a one, one]
        have hff : f (unit ai) = f one := key (unit ai) one (by rw [hx, hy])
        rw [hf_unit ai, hf_one] at hff
        exact Bool.false_ne_true hff
  have hinputs : 9 ≤ (l i).1 ∧ 9 ≤ (r i).1 := by
    constructor
    · by_contra hlt
      have ha : (l i).1 < 9 := by omega
      have gate : ∀ x : Fin 9 → Bool, w x (10 + (i : ℕ)) =
          if op i = true then (w x (l i).1 ^^ (l i).2) && (w x (r i).1 ^^ (r i).2)
          else (w x (l i).1 ^^ (l i).2) || (w x (r i).1 ^^ (r i).2) := by
        intro x; exact hg x
      exact prim_contra (l i).1 ha (l i).2 (r i) gate
    · by_contra hlt
      have hb : (r i).1 < 9 := by omega
      have gate : ∀ x : Fin 9 → Bool, w x (10 + (i : ℕ)) =
          if op i = true then (w x (r i).1 ^^ (r i).2) && (w x (l i).1 ^^ (l i).2)
          else (w x (r i).1 ^^ (r i).2) || (w x (l i).1 ^^ (l i).2) := by
        intro x
        rw [hg x]
        cases op i <;> simp [Bool.and_comm, Bool.or_comm]
      exact prim_contra (r i).1 hb (r i).2 (l i) gate
  exact ⟨i, hout_eq, hinputs.1, hinputs.2⟩
