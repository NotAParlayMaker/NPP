import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3771_aux

def q (a y : Nat) : Bool := !((a + y) % 13 == 0 || (a + y) % 13 == 1 || (a + y) % 13 == 3 || (a + y) % 13 == 9)

def cq (a b c d y : Nat) : Bool := q a y && q b y && q c y && q d y

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem keyb : (List.range 13).all (fun a => (List.range 13).all (fun b => (List.range 13).all (fun c =>
    (List.range 13).all (fun d => a == b || a == c || a == d || b == c || b == d || c == d ||
      decide (((Finset.range 13).filter (fun y => cq a b c d y = true)).card ≤ 3))))) = true := by
  decide +kernel

theorem key (a b c d : Nat) (ha : a < 13) (hb : b < 13) (hc : c < 13) (hd : d < 13)
    (h1 : a ≠ b) (h2 : a ≠ c) (h3 : a ≠ d) (h4 : b ≠ c) (h5 : b ≠ d) (h6 : c ≠ d) :
    ((Finset.range 13).filter (fun y => cq a b c d y = true)).card ≤ 3 := by
  have := keyb
  simp only [List.all_eq_true, List.mem_range] at this
  have := this a ha b hb c hc d hd
  simpa [h1, h2, h3, h4, h5, h6] using this

end PEqualNP.Outside.L_meta_3771_aux

theorem PEqualNP.Outside.L_meta_3771 : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; ∀ (x2 x3 : Finset (Fin (13 : ℕ))), (∀ x4 ∈ x2, ∀ x6 ∈ x3, x4 + x6 ∉ x1) → x2.card ≤ (3 : ℕ) ∨ x3.card ≤ (3 : ℕ) := by
  show ∀ (x2 x3 : Finset (Fin 13)), (∀ x4 ∈ x2, ∀ x6 ∈ x3, x4 + x6 ∉ ({0, 1, 3, 9} : Finset (Fin 13))) → x2.card ≤ 3 ∨ x3.card ≤ 3
  intro x2 x3 h
  by_contra hc
  push_neg at hc
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < x2.card)
  have h2 : 2 < (x2.erase a).card := by rw [Finset.card_erase_of_mem ha]; omega
  obtain ⟨b, c, d, hb, hc', hd, hbc, hbd, hcd⟩ := Finset.two_lt_card_iff.mp h2
  rw [Finset.mem_erase] at hb hc' hd
  have hsub : x3.image Fin.val ⊆ (Finset.range 13).filter
      (fun y => PEqualNP.Outside.L_meta_3771_aux.cq a.val b.val c.val d.val y = true) := by
    intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    have e1 := h a ha z hz
    have e2 := h b hb.2 z hz
    have e3 := h c hc'.2 z hz
    have e4 := h d hd.2 z hz
    simp [Fin.ext_iff, Fin.val_add] at e1 e2 e3 e4
    simp [PEqualNP.Outside.L_meta_3771_aux.cq, PEqualNP.Outside.L_meta_3771_aux.q]
    omega
  have hk := PEqualNP.Outside.L_meta_3771_aux.key a.val b.val c.val d.val a.isLt b.isLt c.isLt d.isLt
    (Fin.val_injective.ne hb.1.symm) (Fin.val_injective.ne hc'.1.symm) (Fin.val_injective.ne hd.1.symm)
    (Fin.val_injective.ne hbc) (Fin.val_injective.ne hbd) (Fin.val_injective.ne hcd)
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ Fin.val_injective] at hcard
  omega
