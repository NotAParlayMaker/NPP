import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6824

def inc (p l : Nat) : Bool := Nat.testBit 523 ((p + 13 - l) % 13)

def R : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]

def allR (f : Nat → Bool) : Bool := R.all f

def anyR (f : Nat → Bool) : Bool := R.any f

theorem memR : ∀ i : Fin 13, i.val ∈ R := by decide

theorem ltR : ∀ x ∈ R, x < 13 := by decide

theorem allR_iff (f : Nat → Bool) : allR f = true ↔ ∀ i : Fin 13, f i.val = true := by
  unfold allR
  rw [List.all_eq_true]
  exact ⟨fun h i => h _ (memR i), fun h x hx => h ⟨x, ltR x hx⟩⟩

theorem anyR_iff (f : Nat → Bool) : anyR f = true ↔ ∃ i : Fin 13, f i.val = true := by
  unfold anyR
  rw [List.any_eq_true]
  exact ⟨fun ⟨x, hx, h⟩ => ⟨⟨x, ltR x hx⟩, h⟩, fun ⟨i, h⟩ => ⟨_, memR i, h⟩⟩

def mk : Nat → (Nat → Bool) → Nat
  | 0, _ => 0
  | n + 1, g => Nat.bit (g 0) (mk n (fun i => g (i + 1)))

theorem mk_lt : ∀ (n : Nat) (g : Nat → Bool), mk n g < 2 ^ n
  | 0, _ => by simp [mk]
  | n + 1, g => by
    have h := mk_lt n (fun i => g (i + 1))
    show Nat.bit (g 0) (mk n (fun i => g (i + 1))) < 2 ^ (n + 1)
    rw [Nat.bit_val, pow_succ]
    cases g 0 <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega

theorem mk_tb : ∀ (n : Nat) (g : Nat → Bool) (i : Nat), i < n → Nat.testBit (mk n g) i = g i
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, g, 0, _ => by
    show Nat.testBit (Nat.bit (g 0) (mk n (fun i => g (i + 1)))) 0 = g 0
    rw [Nat.testBit_bit_zero]
  | n + 1, g, i + 1, h => by
    show Nat.testBit (Nat.bit (g 0) (mk n (fun j => g (j + 1)))) (i + 1) = g (i + 1)
    rw [Nat.testBit_bit_succ]
    exact mk_tb n _ i (by omega)

def allM : Nat → (Nat → Bool) → Bool
  | 0, k => k 0
  | n + 1, k => allM n (fun m => k (2 * m)) && allM n (fun m => k (2 * m + 1))

theorem allM_spec : ∀ (n : Nat) (k : Nat → Bool), allM n k = true → ∀ m, m < 2 ^ n → k m = true
  | 0, k, h, m, hm => by
    have h0 : m = 0 := by
      rw [pow_zero] at hm
      omega
    subst h0
    exact h
  | n + 1, k, h, m, hm => by
    simp only [allM, Bool.and_eq_true] at h
    rw [pow_succ] at hm
    rcases Nat.mod_two_eq_zero_or_one m with h0 | h1
    · have h2 := allM_spec n _ h.1 (m / 2) (by omega)
      have e : 2 * (m / 2) = m := by omega
      rw [← e]
      exact h2
    · have h2 := allM_spec n _ h.2 (m / 2) (by omega)
      have e : 2 * (m / 2) + 1 = m := by omega
      rw [← e]
      exact h2

theorem incL : ∀ x l : Fin 13, (x - l ∈ ({(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))} : Finset (Fin (13 : ℕ)))) ↔ inc x.val l.val = true := by
  decide +kernel

def av (s l : Nat) : Bool := allR fun y => !(Nat.testBit s y && inc y l)

def sizeB (s : Nat) : Bool :=
  (anyR fun a => anyR fun c => allR fun x => !Nat.testBit s x || (x == a || x == c))
  || ((anyR fun a => anyR fun c => allR fun l => !av s l || (l == a || l == c))
  || (anyR fun a => anyR fun c => anyR fun e => (!(a == c) && (!(a == e) && !(c == e))) && ((allR fun x => Nat.testBit s x == (x == a || (x == c || x == e))) && anyR fun l => inc a l && (inc c l && inc e l))))

theorem av_link (s : Nat) (S : Finset (Fin 13)) (hS : ∀ x : Fin 13, x ∈ S ↔ s.testBit x.val = true) (l : Fin 13) :
    av s l.val = true ↔ ∀ y ∈ S, ¬ (y - l ∈ ({(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))} : Finset (Fin (13 : ℕ)))) := by
  unfold av
  rw [allR_iff]
  constructor
  · intro h y hy hI
    have h1 := h y
    rw [(hS y).mp hy, (incL y l).mp hI] at h1
    exact absurd h1 (by decide)
  · intro h y
    by_cases hy : s.testBit y.val = true
    · have h1 := h y ((hS y).mpr hy)
      rw [incL] at h1
      rw [hy]
      simpa using h1
    · rw [Bool.not_eq_true] at hy
      rw [hy]
      rfl

theorem size_link (s : Nat) (S : Finset (Fin 13)) (hS : ∀ x : Fin 13, x ∈ S ↔ s.testBit x.val = true) (h : sizeB s = true) :
    S.card ≤ 2 ∨ Nat.card {l : Fin 13 // ∀ y ∈ S, ¬ (y - l ∈ ({(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))} : Finset (Fin (13 : ℕ))))} ≤ 2 ∨ (S.card = 3 ∧ ∃ l : Fin 13, ∀ x ∈ S, x - l ∈ ({(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))} : Finset (Fin (13 : ℕ)))) := by
  unfold sizeB at h
  rw [Bool.or_eq_true, Bool.or_eq_true] at h
  rcases h with h | h | h
  · left
    simp only [anyR_iff, allR_iff] at h
    obtain ⟨a, c, h⟩ := h
    refine (Finset.card_le_card ?_).trans (Finset.card_le_two (a := a) (b := c))
    intro x hx
    have h1 := h x
    rw [(hS x).mp hx] at h1
    simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true, beq_iff_eq] at h1
    rw [Finset.mem_insert, Finset.mem_singleton]
    exact h1.imp Fin.ext Fin.ext
  · right
    left
    simp only [anyR_iff, allR_iff] at h
    obtain ⟨a, c, h⟩ := h
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    refine (Finset.card_le_card ?_).trans (Finset.card_le_two (a := a) (b := c))
    intro l hl
    rw [Finset.mem_filter] at hl
    have h1 := h l
    rw [(av_link s S hS l).mpr hl.2] at h1
    simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true, beq_iff_eq] at h1
    rw [Finset.mem_insert, Finset.mem_singleton]
    exact h1.imp Fin.ext Fin.ext
  · right
    right
    simp only [anyR_iff, allR_iff, Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq] at h
    obtain ⟨a, c, e, ⟨hac, hae, hce⟩, hx, l, hla, hlc, hle⟩ := h
    have hSe : S = {a, c, e} := by
      ext x
      rw [hS x, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]
      have h1 := hx x
      rw [beq_iff_eq] at h1
      rw [h1]
      simp only [Bool.or_eq_true, beq_iff_eq, Fin.val_inj]
    refine ⟨?_, l, ?_⟩
    · rw [hSe]
      exact Finset.card_eq_three.mpr ⟨a, c, e, fun h => hac (congrArg Fin.val h), fun h => hae (congrArg Fin.val h), fun h => hce (congrArg Fin.val h), rfl⟩
    · intro x hx'
      rw [hSe, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hx'
      rcases hx' with h2 | h2 | h2
      · rw [h2]
        exact (incL _ _).mpr hla
      · rw [h2]
        exact (incL _ _).mpr hlc
      · rw [h2]
        exact (incL _ _).mpr hle

def sOf (b : Nat) : Nat := mk 13 fun x => allR fun l => !(Nat.testBit b l && inc x l)

theorem core (A B : Finset (Fin 13)) (b : Nat)
    (hA : ∀ x ∈ A, ∀ l : Fin 13, b.testBit l.val = true → ¬ (x - l ∈ ({(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))} : Finset (Fin (13 : ℕ)))))
    (hB : ∀ l ∈ B, b.testBit l.val = true) (hs : sizeB (sOf b) = true) :
    ∃ (x8 : Finset (Fin (13 : ℕ))), (∀ x9 ∉ x8, ∃ (x11 : Fin (13 : ℕ)), (∀ x5 ∈ x8, ¬ (x5 - x11 ∈ ({(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))} : Finset (Fin (13 : ℕ))))) ∧ x9 - x11 ∈ ({(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))} : Finset (Fin (13 : ℕ)))) ∧ (x8.card ≤ (2 : ℕ) ∨ Nat.card { x9 : Fin (13 : ℕ) // ∀ x5 ∈ x8, ¬ (x5 - x9 ∈ ({(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))} : Finset (Fin (13 : ℕ)))) } ≤ (2 : ℕ) ∨ x8.card = (3 : ℕ) ∧ ∃ (x9 : Fin (13 : ℕ)), ∀ x10 ∈ x8, x10 - x9 ∈ ({(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))} : Finset (Fin (13 : ℕ)))) ∧ A ⊆ x8 ∧ ∀ x9 ∈ B, ∀ x5 ∈ x8, ¬ (x5 - x9 ∈ ({(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))} : Finset (Fin (13 : ℕ)))) := by
  have hco : ∀ x : Fin 13, (sOf b).testBit x.val = true ↔ ∀ l : Fin 13, b.testBit l.val = true → ¬ (x - l ∈ ({(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))} : Finset (Fin (13 : ℕ)))) := by
    intro x
    unfold sOf
    rw [mk_tb 13 _ x.val x.isLt, allR_iff]
    refine forall_congr' fun l => ?_
    rw [incL]
    cases b.testBit l.val <;> cases inc x.val l.val <;> simp
  obtain ⟨S, hmem⟩ : ∃ S : Finset (Fin 13), ∀ x : Fin 13, x ∈ S ↔ (sOf b).testBit x.val = true :=
    ⟨Finset.univ.filter (fun x : Fin 13 => (sOf b).testBit x.val = true), fun x => by
      rw [Finset.mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩⟩
  refine ⟨S, ?_, size_link _ S hmem hs, ?_, ?_⟩
  · intro x hx
    rw [hmem, hco] at hx
    push_neg at hx
    obtain ⟨l, hl, hI⟩ := hx
    exact ⟨l, fun y hy => (hco y).mp ((hmem y).mp hy) l hl, hI⟩
  · intro x hx
    exact (hmem x).mpr ((hco x).mpr (hA x hx))
  · intro l hl y hy
    exact (hco y).mp ((hmem y).mp hy) l (hB l hl)

def gOf (A : Finset (Fin 13)) : Nat → Bool := fun i => if h : i < 13 then decide ((⟨i, h⟩ : Fin 13) ∈ A) else false

theorem mask_ex (A : Finset (Fin 13)) : ∃ m, m < 2 ^ 13 ∧ ∀ x : Fin 13, m.testBit x.val = true ↔ x ∈ A :=
  ⟨mk 13 (gOf A), mk_lt _ _, fun x => by
    rw [mk_tb 13 _ x.val x.isLt]
    simp [gOf]⟩

def chk1 (m : Nat) : Bool :=
  !(anyR fun l => allR fun x => !Nat.testBit m x || inc x l) || sizeB (sOf (mk 13 fun l => allR fun x => !(Nat.testBit m x && inc x l)))

def chk2 (b : Nat) : Bool :=
  !(anyR fun p => allR fun l => !Nat.testBit b l || inc p l) || sizeB (sOf b)

set_option maxRecDepth 100000 in
theorem K1 : allM 13 chk1 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem K2 : allM 13 chk2 = true := by decide +kernel

theorem main : ∀ (x4 x5 : Finset (Fin (13 : ℕ))), (∀ x6 ∈ x4, ∀ x8 ∈ x5, ¬ (x6 - x8 ∈ ({(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))} : Finset (Fin (13 : ℕ))))) → ((∃ (x7 : Fin (13 : ℕ)), ∀ x8 ∈ x4, x8 - x7 ∈ ({(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))} : Finset (Fin (13 : ℕ)))) ∨ ∃ (x7 : Fin (13 : ℕ)), ∀ x8 ∈ x5, x7 - x8 ∈ ({(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))} : Finset (Fin (13 : ℕ)))) → ∃ (x8 : Finset (Fin (13 : ℕ))), (∀ x9 ∉ x8, ∃ (x11 : Fin (13 : ℕ)), (∀ x5 ∈ x8, ¬ (x5 - x11 ∈ ({(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))} : Finset (Fin (13 : ℕ))))) ∧ x9 - x11 ∈ ({(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))} : Finset (Fin (13 : ℕ)))) ∧ (x8.card ≤ (2 : ℕ) ∨ Nat.card { x9 : Fin (13 : ℕ) // ∀ x5 ∈ x8, ¬ (x5 - x9 ∈ ({(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))} : Finset (Fin (13 : ℕ)))) } ≤ (2 : ℕ) ∨ x8.card = (3 : ℕ) ∧ ∃ (x9 : Fin (13 : ℕ)), ∀ x10 ∈ x8, x10 - x9 ∈ ({(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))} : Finset (Fin (13 : ℕ)))) ∧ x4 ⊆ x8 ∧ ∀ x9 ∈ x5, ∀ x5 ∈ x8, ¬ (x5 - x9 ∈ ({(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))} : Finset (Fin (13 : ℕ)))) := by
  intro A B h0 h1
  rcases h1 with ⟨l0, hl0⟩ | ⟨p0, hp0⟩
  · obtain ⟨m, hm, hmA⟩ := mask_ex A
    have hk := allM_spec 13 chk1 K1 m hm
    unfold chk1 at hk
    rw [Bool.or_eq_true] at hk
    rcases hk with hk | hk
    · exfalso
      rw [Bool.not_eq_true', ← Bool.not_eq_true] at hk
      apply hk
      simp only [anyR_iff, allR_iff]
      refine ⟨l0, fun x => ?_⟩
      by_cases hx : x ∈ A
      · rw [(incL x l0).mp (hl0 x hx)]
        simp
      · have h2 : m.testBit x.val = false := by
          rw [← Bool.not_eq_true, hmA]
          exact hx
        rw [h2]
        rfl
    · refine core A B _ ?_ ?_ hk
      · intro x hx l hl
        rw [mk_tb 13 _ l.val l.isLt, allR_iff] at hl
        have h2 := hl x
        rw [(hmA x).mpr hx] at h2
        intro hI
        rw [(incL x l).mp hI] at h2
        exact absurd h2 (by decide)
      · intro l hl
        rw [mk_tb 13 _ l.val l.isLt, allR_iff]
        intro x
        by_cases hx : x ∈ A
        · have h2 := h0 x hx l hl
          rw [incL, Bool.not_eq_true] at h2
          rw [h2]
          simp
        · have h2 : m.testBit x.val = false := by
            rw [← Bool.not_eq_true, hmA]
            exact hx
          rw [h2]
          rfl
  · obtain ⟨b, hb, hbB⟩ := mask_ex B
    have hk := allM_spec 13 chk2 K2 b hb
    unfold chk2 at hk
    rw [Bool.or_eq_true] at hk
    rcases hk with hk | hk
    · exfalso
      rw [Bool.not_eq_true', ← Bool.not_eq_true] at hk
      apply hk
      simp only [anyR_iff, allR_iff]
      refine ⟨p0, fun l => ?_⟩
      by_cases hl : l ∈ B
      · rw [(incL p0 l).mp (hp0 l hl)]
        simp
      · have h2 : b.testBit l.val = false := by
          rw [← Bool.not_eq_true, hbB]
          exact hl
        rw [h2]
        rfl
    · exact core A B b (fun x hx l hl => h0 x hx l ((hbB l).mp hl)) (fun l hl => (hbB l).mpr hl) hk

end PEqualNP.Outside.L_meta_6824

theorem PEqualNP.Outside.L_meta_6824 : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x2 x3 : Fin (13 : ℕ)) => x2 - x3 ∈ x1; have x3 : Finset (Fin (13 : ℕ)) → Fin (13 : ℕ) → Prop := fun (x3 : Finset (Fin (13 : ℕ))) (x4 : Fin (13 : ℕ)) => ∀ x5 ∈ x3, ¬x2 x5 x4; ∀ (x4 x5 : Finset (Fin (13 : ℕ))), (∀ x6 ∈ x4, ∀ x8 ∈ x5, ¬x2 x6 x8) → ((∃ (x7 : Fin (13 : ℕ)), ∀ x8 ∈ x4, x2 x8 x7) ∨ ∃ (x7 : Fin (13 : ℕ)), ∀ x8 ∈ x5, x2 x7 x8) → ∃ (x8 : Finset (Fin (13 : ℕ))), (∀ x9 ∉ x8, ∃ (x11 : Fin (13 : ℕ)), x3 x8 x11 ∧ x2 x9 x11) ∧ (x8.card ≤ (2 : ℕ) ∨ Nat.card { x9 : Fin (13 : ℕ) // x3 x8 x9 } ≤ (2 : ℕ) ∨ x8.card = (3 : ℕ) ∧ ∃ (x9 : Fin (13 : ℕ)), ∀ x10 ∈ x8, x2 x10 x9) ∧ x4 ⊆ x8 ∧ ∀ x9 ∈ x5, x3 x8 x9 := by
  intro x1 x2 x3
  exact PEqualNP.Outside.L_meta_6824.main
