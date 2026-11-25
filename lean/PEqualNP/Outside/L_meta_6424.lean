import Mathlib.Data.Finset.Card
import Mathlib.Tactic.IntervalCases

-- The choice of four distinct elements of the first set follows L-meta-6424 PR 11576 (MiguelTorresPerez).
-- Here the finite check runs on 13-bit masks: bit y of mask a says that a + y avoids 0, 1, 3, 9 mod 13.
namespace PEqualNP.Outside.L_meta_6424

def mask : Nat → Nat
  | 0 => 7668
  | 1 => 3834
  | 2 => 1917
  | 3 => 5054
  | 4 => 2527
  | 5 => 5359
  | 6 => 6775
  | 7 => 7483
  | 8 => 7837
  | 9 => 8014
  | 10 => 4007
  | 11 => 6099
  | 12 => 7145
  | _ => 0

def okB (a y : Nat) : Bool :=
  (a + y) % 13 != 0 && (a + y) % 13 != 1 && (a + y) % 13 != 3 && (a + y) % 13 != 9

theorem mask_ok : ∀ a < 13, ∀ y < 13, okB a y = true → (mask a).testBit y = true := by
  decide +kernel

def pc (m : Nat) : Nat := ((List.range 13).filter (fun y => m.testBit y)).length

theorem pc_card (m : Nat) : ((Finset.range 13).filter (fun y => m.testBit y = true)).card = pc m := by
  rfl

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
theorem key0 : ∀ b < 13, ∀ c < 13, ∀ d < 13, 0 ≠ b → 0 ≠ c → 0 ≠ d → b ≠ c → b ≠ d →
    c ≠ d → pc (mask 0 &&& mask b &&& mask c &&& mask d) ≤ 3 := by
  decide +kernel

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
theorem key1 : ∀ b < 13, ∀ c < 13, ∀ d < 13, 1 ≠ b → 1 ≠ c → 1 ≠ d → b ≠ c → b ≠ d →
    c ≠ d → pc (mask 1 &&& mask b &&& mask c &&& mask d) ≤ 3 := by
  decide +kernel

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
theorem key2 : ∀ b < 13, ∀ c < 13, ∀ d < 13, 2 ≠ b → 2 ≠ c → 2 ≠ d → b ≠ c → b ≠ d →
    c ≠ d → pc (mask 2 &&& mask b &&& mask c &&& mask d) ≤ 3 := by
  decide +kernel

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
theorem key3 : ∀ b < 13, ∀ c < 13, ∀ d < 13, 3 ≠ b → 3 ≠ c → 3 ≠ d → b ≠ c → b ≠ d →
    c ≠ d → pc (mask 3 &&& mask b &&& mask c &&& mask d) ≤ 3 := by
  decide +kernel

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
theorem key4 : ∀ b < 13, ∀ c < 13, ∀ d < 13, 4 ≠ b → 4 ≠ c → 4 ≠ d → b ≠ c → b ≠ d →
    c ≠ d → pc (mask 4 &&& mask b &&& mask c &&& mask d) ≤ 3 := by
  decide +kernel

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
theorem key5 : ∀ b < 13, ∀ c < 13, ∀ d < 13, 5 ≠ b → 5 ≠ c → 5 ≠ d → b ≠ c → b ≠ d →
    c ≠ d → pc (mask 5 &&& mask b &&& mask c &&& mask d) ≤ 3 := by
  decide +kernel

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
theorem key6 : ∀ b < 13, ∀ c < 13, ∀ d < 13, 6 ≠ b → 6 ≠ c → 6 ≠ d → b ≠ c → b ≠ d →
    c ≠ d → pc (mask 6 &&& mask b &&& mask c &&& mask d) ≤ 3 := by
  decide +kernel

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
theorem key7 : ∀ b < 13, ∀ c < 13, ∀ d < 13, 7 ≠ b → 7 ≠ c → 7 ≠ d → b ≠ c → b ≠ d →
    c ≠ d → pc (mask 7 &&& mask b &&& mask c &&& mask d) ≤ 3 := by
  decide +kernel

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
theorem key8 : ∀ b < 13, ∀ c < 13, ∀ d < 13, 8 ≠ b → 8 ≠ c → 8 ≠ d → b ≠ c → b ≠ d →
    c ≠ d → pc (mask 8 &&& mask b &&& mask c &&& mask d) ≤ 3 := by
  decide +kernel

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
theorem key9 : ∀ b < 13, ∀ c < 13, ∀ d < 13, 9 ≠ b → 9 ≠ c → 9 ≠ d → b ≠ c → b ≠ d →
    c ≠ d → pc (mask 9 &&& mask b &&& mask c &&& mask d) ≤ 3 := by
  decide +kernel

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
theorem key10 : ∀ b < 13, ∀ c < 13, ∀ d < 13, 10 ≠ b → 10 ≠ c → 10 ≠ d → b ≠ c → b ≠ d →
    c ≠ d → pc (mask 10 &&& mask b &&& mask c &&& mask d) ≤ 3 := by
  decide +kernel

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
theorem key11 : ∀ b < 13, ∀ c < 13, ∀ d < 13, 11 ≠ b → 11 ≠ c → 11 ≠ d → b ≠ c → b ≠ d →
    c ≠ d → pc (mask 11 &&& mask b &&& mask c &&& mask d) ≤ 3 := by
  decide +kernel

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
theorem key12 : ∀ b < 13, ∀ c < 13, ∀ d < 13, 12 ≠ b → 12 ≠ c → 12 ≠ d → b ≠ c → b ≠ d →
    c ≠ d → pc (mask 12 &&& mask b &&& mask c &&& mask d) ≤ 3 := by
  decide +kernel

theorem key : ∀ a < 13, ∀ b < 13, ∀ c < 13, ∀ d < 13, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d →
    c ≠ d → pc (mask a &&& mask b &&& mask c &&& mask d) ≤ 3 := by
  intro a ha
  interval_cases a
  · exact key0
  · exact key1
  · exact key2
  · exact key3
  · exact key4
  · exact key5
  · exact key6
  · exact key7
  · exact key8
  · exact key9
  · exact key10
  · exact key11
  · exact key12

theorem okB_of (a y : Fin 13) (h : (a.val + y.val) % 13 ∉ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]) :
    okB a.val y.val = true := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  simp [okB, h.1, h.2.1, h.2.2.1, h.2.2.2]

theorem bound (A B : Finset (Fin 13))
    (h : ∀ x ∈ A, ∀ y ∈ B, (x.val + y.val) % 13 ∉ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)])
    (a b c d : Fin 13) (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) (hd : d ∈ A)
    (n1 : a ≠ b) (n2 : a ≠ c) (n3 : a ≠ d) (n4 : b ≠ c) (n5 : b ≠ d) (n6 : c ≠ d) :
    B.card ≤ 3 := by
  have hk := key a.val a.isLt b.val b.isLt c.val c.isLt d.val d.isLt (Fin.val_ne_of_ne n1)
    (Fin.val_ne_of_ne n2) (Fin.val_ne_of_ne n3) (Fin.val_ne_of_ne n4) (Fin.val_ne_of_ne n5)
    (Fin.val_ne_of_ne n6)
  have hsub : B.image Fin.val ⊆ (Finset.range 13).filter
      (fun y => (mask a.val &&& mask b.val &&& mask c.val &&& mask d.val).testBit y = true) := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨z.isLt, ?_⟩
    simp only [Nat.testBit_and, Bool.and_eq_true]
    exact ⟨⟨⟨mask_ok _ a.isLt _ z.isLt (okB_of a z (h a ha z hz)),
      mask_ok _ b.isLt _ z.isLt (okB_of b z (h b hb z hz))⟩,
      mask_ok _ c.isLt _ z.isLt (okB_of c z (h c hc z hz))⟩,
      mask_ok _ d.isLt _ z.isLt (okB_of d z (h d hd z hz))⟩
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ (fun x y (e : Fin.val x = Fin.val y) => Fin.ext e)] at h1
  rw [pc_card] at h1
  omega

end PEqualNP.Outside.L_meta_6424

theorem PEqualNP.Outside.L_meta_6424 : ∀ (x1 x2 : Finset (Fin (13 : ℕ))), (∀ x3 ∈ x1, ∀ x5 ∈ x2, (↑x3 + ↑x5) % (13 : ℕ) ∉ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]) → x1.card ≤ (3 : ℕ) ∨ x2.card ≤ (3 : ℕ) := by
  intro A B h
  by_contra hc
  rw [not_or, not_le, not_le] at hc
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (show 0 < A.card by omega)
  obtain ⟨b, hb⟩ := Finset.card_pos.mp (show 0 < (A.erase a).card by
    rw [Finset.card_erase_of_mem ha]; omega)
  have hb1 := Finset.mem_erase.mp hb
  obtain ⟨c, hc1⟩ := Finset.card_pos.mp (show 0 < ((A.erase a).erase b).card by
    rw [Finset.card_erase_of_mem hb, Finset.card_erase_of_mem ha]; omega)
  have hc2 := Finset.mem_erase.mp hc1
  have hc3 := Finset.mem_erase.mp hc2.2
  obtain ⟨d, hd1⟩ := Finset.card_pos.mp (show 0 < (((A.erase a).erase b).erase c).card by
    rw [Finset.card_erase_of_mem hc1, Finset.card_erase_of_mem hb,
      Finset.card_erase_of_mem ha]; omega)
  have hd2 := Finset.mem_erase.mp hd1
  have hd3 := Finset.mem_erase.mp hd2.2
  have hd4 := Finset.mem_erase.mp hd3.2
  have := PEqualNP.Outside.L_meta_6424.bound A B h a b c d ha hb1.2 hc3.2 hd4.2
    (Ne.symm hb1.1) (Ne.symm hc3.1) (Ne.symm hd4.1) (Ne.symm hc2.1) (Ne.symm hd3.1) (Ne.symm hd2.1)
  omega
