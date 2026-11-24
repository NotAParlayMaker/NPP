import Mathlib.Data.Finset.Card
import PEqualNP.Defs

-- With two charged earlier gates the output charge uses the rest of the budget.
-- Trim the signed program at the actual output and retain only those two earlier charges.
theorem PEqualNP.Outside.R_meta_2964_1
    (single :
    let f := (fun x : Fin 9 → Bool =>
      ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
        (fun k => x (Fin.ofNat 9 (k / 10)) && x (Fin.ofNat 9 (k % 10))))
    ∀ (n : ℕ) (op : Fin n → Bool) (l r : Fin n → ℕ × Bool) (out : ℕ × Bool)
      (paid : Finset ℕ) (w : (Fin 9 → Bool) → ℕ → Bool),
      paid.card ≤ 3 → n + paid.card ≤ 14 →
      (∀ j, (l j).1 < 10+j.val ∧ (r j).1 < 10+j.val) →
      out.1 < 10+n → out.2 = true →
      (let ok := fun (p : ℕ × Bool) => p.2 = true → p.1 = 0 ∨ p.1 = 9 ∨ p.1 ∈ paid
       ok out ∧ ∀ j, ok (l j) ∧ ok (r j)) →
      (∀ x (i : Fin 9), w x i.val = x i) → (∀ x, w x 9 = false) →
      (∀ x j, let val := fun p : ℕ × Bool => w x p.1 ^^ p.2
         w x (10+j.val) = if op j then val (l j) && val (r j) else val (l j) || val (r j)) →
      (paid.filter (fun t => 10 ≤ t ∧ t < out.1)).card ≤ 1 →
      (∀ x, (w x out.1 ^^ out.2) = f x) → PEqualNP.MetaComplexity.HasCircuitSize 9 f 14)
    (lower :
    let f := (fun x : Fin 9 → Bool =>
      ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
        (fun k => x (Fin.ofNat 9 (k / 10)) && x (Fin.ofNat 9 (k % 10))))
    ¬ PEqualNP.MetaComplexity.HasCircuitSize 9 f 14)
    (double : ∀ (n : ℕ) (op : Fin n → Bool) (l r : Fin n → ℕ × Bool) (a b : ℕ)
      (w : (Fin 9 → Bool) → ℕ → Bool),
      n ≤ 11 → 10 ≤ a → 10 ≤ b → a < 9+n → b < 9+n → a ≠ b →
      (∀ j, (l j).1 < 10+j.val ∧ (r j).1 < 10+j.val) →
      (let ok := fun (p : ℕ × Bool) => p.2 = true → p.1 = 0 ∨ p.1 = 9 ∨ p.1 = a ∨ p.1 = b
       ∀ j, ok (l j) ∧ ok (r j)) →
      (∀ x (i : Fin 9), w x i.val = x i) → (∀ x, w x 9 = false) →
      (∀ x j, let p := fun k : ℕ × Bool => w x k.1 ^^ k.2
         w x (10+j.val) = if op j then p (l j) && p (r j) else p (l j) || p (r j)) →
      ∃ x : Fin 9 → Bool, (w x (9+n) ^^ true) ≠
        ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
        (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
        (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) :
    ∀ (n : ℕ) (op : Fin n → Bool) (l r : Fin n → ℕ × Bool) (out : ℕ × Bool)
      (paid : Finset ℕ) (w : (Fin 9 → Bool) → ℕ → Bool),
      paid.card ≤ 3 → n + paid.card ≤ 14 →
      (∀ j, (l j).1 < 10+j.val ∧ (r j).1 < 10+j.val) →
      out.1 < 10+n → out.2 = true →
      (let ok := fun (p : ℕ × Bool) => p.2 = true → p.1 = 0 ∨ p.1 = 9 ∨ p.1 ∈ paid
       ok out ∧ ∀ j, ok (l j) ∧ ok (r j)) →
      (∀ x (i : Fin 9), w x i.val = x i) → (∀ x, w x 9 = false) →
      (∀ x j, let val := fun p : ℕ × Bool => w x p.1 ^^ p.2
         w x (10+j.val) = if op j then val (l j) && val (r j) else val (l j) || val (r j)) →
      ∃ x : Fin 9 → Bool, (w x out.1 ^^ out.2) ≠ ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
        (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
        (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) := by
  intro n op l r out paid w size cost order bound sign ok raw zero equations
  let used := paid.filter fun t => 10 ≤ t ∧ t < out.1
  by_contra! equal
  by_cases few : used.card ≤ 1
  · apply lower (single n op l r out paid w size cost order bound sign ok raw zero equations few ?_)
    intro x
    rw [equal x]
    simp only [List.any_cons,List.any_nil,Bool.or_false,Bool.or_assoc]
    rfl
  have outLow : 10 ≤ out.1 := by
    have val := equal (fun _ => false)
    rw [sign] at val
    change (w (fun _ => false) out.1 ^^ true) = false at val
    by_contra! small
    by_cases h : out.1 < 9
    · have ev : w (fun _ => false) out.1 = false := raw _ ⟨out.1,h⟩
      rw [ev] at val
      contradiction
    · have eq : out.1 = 9 := by omega
      rw [eq,zero] at val
      contradiction
  have mem : out.1 ∈ paid := by
    rcases ok.1 sign with h | h | h
    · omega
    · omega
    · exact h
  obtain ⟨a,ha,b,hb,ne⟩ := Finset.one_lt_card.mp (show 1 < used.card by omega)
  obtain ⟨aM,aL,aH⟩ := Finset.mem_filter.mp ha
  obtain ⟨bM,bL,bH⟩ := Finset.mem_filter.mp hb
  have triple : ({a,b,out.1} : Finset ℕ).card = 3 :=
    Finset.card_triple_eq_three_iff.mpr ⟨ne,by omega,by omega⟩
  have sub : ({a,b,out.1} : Finset ℕ) ⊆ paid := by
    intro t ht
    simp only [Finset.mem_insert,Finset.mem_singleton] at ht
    rcases ht with h | h | h
    · rwa [h]
    · rwa [h]
    · rwa [h]
  have full := Finset.eq_of_subset_of_card_le sub (by omega)
  have p3 : paid.card = 3 := full ▸ triple
  let m := out.1-9
  have last : 9+m = out.1 := by dsimp [m]; omega
  have fit : m ≤ n := by omega
  let cast : Fin m → Fin n := Fin.castLE fit
  have legal (p : ℕ × Bool) (lt : p.1 < out.1)
      (original : p.2 = true → p.1 = 0 ∨ p.1 = 9 ∨ p.1 ∈ paid) :
      p.2 = true → p.1 = 0 ∨ p.1 = 9 ∨ p.1 = a ∨ p.1 = b := by
    intro h
    rcases original h with k | k | k
    · exact Or.inl k
    · exact Or.inr (Or.inl k)
    · rw [← full] at k
      simp only [Finset.mem_insert,Finset.mem_singleton] at k
      rcases k with k | k | k
      · exact Or.inr (Or.inr (Or.inl k))
      · exact Or.inr (Or.inr (Or.inr k))
      · omega
  obtain ⟨x,bad⟩ := double m (op ∘ cast) (l ∘ cast) (r ∘ cast) a b w
    (by omega) aL bL (by omega) (by omega) ne (fun j => order (cast j))
    (by
      intro allowed j
      have less : 10+(cast j).val ≤ out.1 := by
        have jLt := j.isLt
        change 10+j.val ≤ out.1
        omega
      exact ⟨legal (l (cast j)) (lt_of_lt_of_le (order (cast j)).1 less) (ok.2 (cast j)).1,
        legal (r (cast j)) (lt_of_lt_of_le (order (cast j)).2 less) (ok.2 (cast j)).2⟩)
    raw zero (fun x j => equations x (cast j))
  rw [last] at bad
  exact bad (by simpa only [sign] using equal x)
