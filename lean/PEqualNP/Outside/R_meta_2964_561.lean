import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2964_561
    (lower : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C →
      (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) =
        ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] :
          List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)) →
      13 ≤ C.gates.countP (fun g => PEqualNP.CircuitLowerBounds.GateOp.rec
        (motive := fun _ => Bool) true true false (fun _ => true) true g.op))
    (realize : ∀ (n : ℕ) (op : Fin n → Bool) (l r : Fin n → ℕ × Bool)
      (out : ℕ × Bool) (w : (Fin 9 → Bool) → ℕ → Bool),
      (∀ i : Fin n, (l i).1 < 10 + i.val ∧ (r i).1 < 10 + i.val) →
      out.1 < 10 + n →
      (∀ (x : Fin 9 → Bool) (i : Fin 9), w x i.val = x i) →
      (∀ x : Fin 9 → Bool, w x 9 = false) →
      (∀ (x : Fin 9 → Bool) (i : Fin n),
        let read := fun p : ℕ × Bool => w x p.1 ^^ p.2
        w x (10 + i.val) = if op i = true then read (l i) && read (r i) else read (l i) || read (r i)) →
      ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧
        C.gates.countP (fun g => PEqualNP.CircuitLowerBounds.GateOp.rec
          (motive := fun _ => Bool) true true false (fun _ => true) true g.op) ≤ n ∧
        ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = (w x out.1 ^^ out.2)) :
    ∀ (x1 : ℕ) (x2 : Fin x1 → Bool) (x3 x4 : Fin x1 → ℕ × Bool) (x5 : ℕ × Bool)
      (x6 : Finset ℕ) (x7 : (Fin (9 : ℕ) → Bool) → ℕ → Bool),
      x6.card ≤ (3 : ℕ) → x1 + x6.card ≤ (14 : ℕ) →
      (∀ (x10 : Fin x1), (x3 x10).1 < (10 : ℕ) + ↑x10 ∧ (x4 x10).1 < (10 : ℕ) + ↑x10) →
      x5.1 < (10 : ℕ) + x1 → x5.2 = Bool.true →
      (have x13 : ℕ × Bool → Prop := fun (x13 : ℕ × Bool) =>
        x13.2 = Bool.true → x13.1 = (0 : ℕ) ∨ x13.1 = (9 : ℕ) ∨ x13.1 ∈ x6;
        x13 x5 ∧ ∀ (x14 : Fin x1), x13 (x3 x14) ∧ x13 (x4 x14)) →
      (∀ (x14 : Fin (9 : ℕ) → Bool) (x15 : Fin (9 : ℕ)), x7 x14 ↑x15 = x14 x15) →
      (∀ (x15 : Fin (9 : ℕ) → Bool), x7 x15 (9 : ℕ) = Bool.false) →
      (∀ (x16 : Fin (9 : ℕ) → Bool) (x17 : Fin x1),
        have x18 : ℕ × Bool → Bool := fun (x18 : ℕ × Bool) => x7 x16 x18.1 ^^ x18.2;
        x7 x16 ((10 : ℕ) + ↑x17) =
          if x2 x17 = Bool.true then x18 (x3 x17) && x18 (x4 x17) else x18 (x3 x17) || x18 (x4 x17)) →
      ∃ (x17 : Fin (9 : ℕ) → Bool), (x7 x17 x5.1 ^^ x5.2) ≠
        (x17 (0 : Fin (9 : ℕ)) && x17 (1 : Fin (9 : ℕ)) ||
         x17 (1 : Fin (9 : ℕ)) && x17 (2 : Fin (9 : ℕ)) ||
         x17 (2 : Fin (9 : ℕ)) && x17 (3 : Fin (9 : ℕ)) ||
         x17 (3 : Fin (9 : ℕ)) && x17 (4 : Fin (9 : ℕ)) ||
         x17 (4 : Fin (9 : ℕ)) && x17 (0 : Fin (9 : ℕ)) ||
         x17 (0 : Fin (9 : ℕ)) && x17 (5 : Fin (9 : ℕ)) ||
         x17 (1 : Fin (9 : ℕ)) && x17 (6 : Fin (9 : ℕ)) ||
         x17 (2 : Fin (9 : ℕ)) && x17 (7 : Fin (9 : ℕ)) ||
         x17 (3 : Fin (9 : ℕ)) && x17 (8 : Fin (9 : ℕ)) ||
         x17 (5 : Fin (9 : ℕ)) && x17 (7 : Fin (9 : ℕ)) ||
         x17 (6 : Fin (9 : ℕ)) && x17 (8 : Fin (9 : ℕ)) ||
         x17 (8 : Fin (9 : ℕ)) && x17 (5 : Fin (9 : ℕ))) := by
  intro n op l r out paid w _ budget back outBound outNeg allowed raw zero gateValue
  let target (x : Fin 9 → Bool) :=
    ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] :
      List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)
  let permitted (p : ℕ × Bool) := p.2 = true → p.1 = 0 ∨ p.1 = 9 ∨ p.1 ∈ paid
  change permitted out ∧ (∀ i, permitted (l i) ∧ permitted (r i)) at allowed
  have gateEq (x : Fin 9 → Bool) (i : Fin n) : w x (10 + i.val) =
      (if op i = true then (w x (l i).1 ^^ (l i).2) && (w x (r i).1 ^^ (r i).2)
        else (w x (l i).1 ^^ (l i).2) || (w x (r i).1 ^^ (r i).2)) := gateValue x i
  by_contra noWitness
  have agrees (x : Fin 9 → Bool) : (w x out.1 ^^ out.2) = target x := by
    by_contra different
    apply noWitness
    exact ⟨x, by simpa only [target, List.any_cons, List.any_nil, Bool.or_false, Bool.or_assoc] using different⟩
  by_cases twoPaid : 2 ≤ paid.card
  · obtain ⟨C, fan, count, eval⟩ := realize n op l r out w back outBound raw zero gateValue
    have required := lower C fan (fun x => (eval x).trans (agrees x))
    omega
  · let a (i : Fin 9) := decide (i = 2)
    let b (i : Fin 9) := decide (i = 2 ∨ i = 1)
    have targetA : target a = false := by decide +kernel
    have targetB : target b = true := by decide +kernel
    have sameZero : a 0 = b 0 := rfl
    have rawLe : ∀ i, a i ≤ b i := by decide +kernel
    have rootA : w a out.1 = true := by
      have h := agrees a
      rw [outNeg, targetA] at h
      cases e : w a out.1 <;> simp [e] at h ⊢
    have rootB : w b out.1 = false := by
      have h := agrees b
      rw [outNeg, targetB] at h
      cases e : w b out.1 <;> simp [e] at h ⊢
    have out0 : out.1 ≠ 0 := by
      intro eq
      have h : w a 0 = false := raw a 0
      rw [eq, h] at rootA
      cases rootA
    have out9 : out.1 ≠ 9 := by
      intro eq
      rw [eq, zero] at rootA
      cases rootA
    have outPaid : out.1 ∈ paid := ((allowed.1 outNeg).resolve_left out0).resolve_left out9
    have onlyOut (m : ℕ) (hm : m ∈ paid) : m = out.1 :=
      Finset.card_le_one.mp (by omega : paid.card ≤ 1) m hm out.1 outPaid
    have gateMono : ∀ (t a1 b1 a2 b2 : Bool), a1 ≤ b1 → a2 ≤ b2 →
        (if t = true then a1 && a2 else a1 || a2) ≤ (if t = true then b1 && b2 else b1 || b2) := by
      decide +kernel
    have monotoneBefore : ∀ m ≤ out.1, w a m ≤ w b m := by
      intro m
      induction m using Nat.strong_induction_on with
      | ind m ih =>
        intro hm
        by_cases bound : m < 9
        · let j : Fin 9 := ⟨m, bound⟩
          change w a j.val ≤ w b j.val
          rw [raw a j, raw b j]
          exact rawLe j
        · by_cases isNine : m = 9
          · simp only [isNine, zero, le_refl]
          · let i : Fin n := ⟨m - 10, by omega⟩
            have atGate : m = 10 + i.val := by dsimp [i]; omega
            have readLe (p : ℕ × Bool) (before : p.1 < m) (hp : permitted p) :
                (w a p.1 ^^ p.2) ≤ (w b p.1 ^^ p.2) := by
              cases neg : p.2 with
              | false =>
                simpa only [neg, Bool.xor_false] using ih p.1 before (by omega)
              | true =>
                rcases hp neg with h | h | h
                · have ha : w a 0 = a 0 := raw a 0
                  have hb : w b 0 = b 0 := raw b 0
                  simp only [h, ha, hb, sameZero, le_refl]
                · simp only [h, zero a, zero b, le_refl]
                · have eq := onlyOut p.1 h
                  omega
            have left := readLe (l i) (by rw [atGate]; exact (back i).1) (allowed.2 i).1
            have right := readLe (r i) (by rw [atGate]; exact (back i).2) (allowed.2 i).2
            rw [atGate, gateEq a i, gateEq b i]
            exact gateMono (op i) _ _ _ _ left right
    have impossible := monotoneBefore out.1 (le_refl _)
    rw [rootA, rootB] at impossible
    exact (by decide : ¬ (true ≤ false)) impossible
