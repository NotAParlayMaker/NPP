import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4980

theorem point_deg {q N : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I]
    (hq : 0 < q) (hN : N = q ^ 2 + q + 1)
    (hline : ∀ l : Fin N, Fintype.card { p : Fin N // I p l } = q + 1)
    (huniq : ∀ p1 p2 : Fin N, p1 ≠ p2 → ∃! l : Fin N, I p1 l ∧ I p2 l)
    (p : Fin N) :
    Fintype.card { l : Fin N // I p l } = q + 1 := by
  have hsum : ∑ l ∈ Finset.univ.filter (fun l : Fin N => I p l),
      (Finset.univ.filter (fun p' : Fin N => p' ≠ p ∧ I p' l)).card =
      (Finset.univ.filter (fun p' : Fin N => p' ≠ p)).card := by
    rw [← Finset.card_biUnion]
    · congr 1; ext p'
      simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨l, _, hne, _⟩; exact hne
      · intro hne
        obtain ⟨l, ⟨hpl, hp'l⟩, _⟩ := huniq p p' (Ne.symm hne)
        exact ⟨l, hpl, hne, hp'l⟩
    · intro l1 hl1 l2 hl2 hne
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro p' h1 h2
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hl1 hl2 h1 h2
      obtain ⟨l0, _, huniq0⟩ := huniq p p' (Ne.symm h1.1)
      have e1 : l1 = l0 := huniq0 l1 ⟨hl1, h1.2⟩
      have e2 : l2 = l0 := huniq0 l2 ⟨hl2, h2.2⟩
      exact hne (e1.trans e2.symm)
  have hterm : ∀ l ∈ Finset.univ.filter (fun l : Fin N => I p l),
      (Finset.univ.filter (fun p' : Fin N => p' ≠ p ∧ I p' l)).card = q := by
    intro l hl
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
    have hcard : (Finset.univ.filter (fun p' : Fin N => I p' l)).card = q + 1 := by
      simpa [Fintype.card_subtype] using hline l
    have hmem : p ∈ Finset.univ.filter (fun p' : Fin N => I p' l) := by simp [hl]
    have heq : Finset.univ.filter (fun p' : Fin N => p' ≠ p ∧ I p' l) =
        (Finset.univ.filter (fun p' : Fin N => I p' l)).erase p := by
      ext p'; simp [and_comm]
    rw [heq, Finset.card_erase_of_mem hmem, hcard]; omega
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, smul_eq_mul] at hsum
  have hrhs : (Finset.univ.filter (fun p' : Fin N => p' ≠ p)).card = N - 1 := by
    have heq : Finset.univ.filter (fun p' : Fin N => p' ≠ p) = Finset.univ.erase p := by
      ext p'; simp
    rw [heq, Finset.card_erase_of_mem (Finset.mem_univ p), Finset.card_univ, Fintype.card_fin]
  have hsum' : (Finset.univ.filter (fun l : Fin N => I p l)).card * q = q ^ 2 + q := by omega
  have hcard_eq : Fintype.card { l : Fin N // I p l } =
      (Finset.univ.filter (fun l : Fin N => I p l)).card := Fintype.card_subtype _
  rw [hcard_eq]
  have hmul : (Finset.univ.filter (fun l : Fin N => I p l)).card * q = (q + 1) * q := by
    rw [hsum', Nat.add_mul, Nat.one_mul, sq]
  exact Nat.eq_of_mul_eq_mul_right (by omega) hmul

theorem main {q N : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I]
    (hq : 0 < q) (hN : N = q ^ 2 + q + 1)
    (hline : ∀ l : Fin N, Fintype.card { p : Fin N // I p l } = q + 1)
    (huniq : ∀ p1 p2 : Fin N, p1 ≠ p2 → ∃! l : Fin N, I p1 l ∧ I p2 l) :
    ∃ (aff : Fin (q * q) ↪ Fin N) (ln : Fin (q + 1) × Fin q ↪ Fin N)
      (f : Fin (q + 1) → Fin (q * q) → Fin q),
      (∀ c c' : Fin (q + 1), c ≠ c' → Function.Bijective fun p => (f c p, f c' p)) ∧
      ∀ (p : Fin (q * q)) (c : Fin (q + 1)) (j : Fin q),
        I (aff p) (ln (c, j)) ↔ f c p = j := by
  have hNpos : 0 < N := by omega
  let L0 : Fin N := ⟨0, hNpos⟩
  have hc1 : Fintype.card { p : Fin N // I p L0 } = q + 1 := hline L0
  let e1 : Fin (q + 1) ≃ { p : Fin N // I p L0 } := (Fintype.equivFinOfCardEq hc1).symm
  have hc2 : Fintype.card { p : Fin N // ¬ I p L0 } = q * q := by
    rw [Fintype.card_subtype_compl, hc1, Fintype.card_fin, hN]
    apply Nat.sub_eq_of_eq_add
    ring
  let e2 : Fin (q * q) ≃ { p : Fin N // ¬ I p L0 } := (Fintype.equivFinOfCardEq hc2).symm
  have hc3 : ∀ c : Fin (q + 1), Fintype.card { l : Fin N // I (e1 c).1 l ∧ l ≠ L0 } = q := by
    intro c
    have h := point_deg hq hN hline huniq (e1 c).1
    rw [Fintype.card_subtype] at h ⊢
    have hs : (Finset.univ.filter fun l => I (e1 c).1 l ∧ l ≠ L0) =
        (Finset.univ.filter fun l => I (e1 c).1 l).erase L0 := by
      ext l; simp [and_comm]
    rw [hs, Finset.card_erase_of_mem (by simpa using (e1 c).2), h]
    simp
  let e3 : ∀ c : Fin (q + 1), Fin q ≃ { l : Fin N // I (e1 c).1 l ∧ l ≠ L0 } :=
    fun c => (Fintype.equivFinOfCardEq (hc3 c)).symm
  have hne : ∀ (p : Fin (q * q)) (c : Fin (q + 1)), (e2 p).1 ≠ (e1 c).1 := by
    intro p c h
    exact (e2 p).2 (h ▸ (e1 c).2)
  let g : Fin (q * q) → Fin (q + 1) → Fin N :=
    fun p c => Classical.choose (huniq _ _ (hne p c))
  have hg : ∀ p c, I (e2 p).1 (g p c) ∧ I (e1 c).1 (g p c) :=
    fun p c => (Classical.choose_spec (huniq _ _ (hne p c))).1
  have hgu : ∀ p c l, I (e2 p).1 l → I (e1 c).1 l → l = g p c :=
    fun p c l h1 h2 => (Classical.choose_spec (huniq _ _ (hne p c))).2 l ⟨h1, h2⟩
  have hgne : ∀ p c, g p c ≠ L0 := by
    intro p c h
    have h1 := (hg p c).1
    rw [h] at h1
    exact (e2 p).2 h1
  let f : Fin (q + 1) → Fin (q * q) → Fin q :=
    fun c p => (e3 c).symm ⟨g p c, (hg p c).2, hgne p c⟩
  have hf : ∀ c p j, f c p = j ↔ g p c = ((e3 c) j).1 := by
    intro c p j
    constructor
    · intro h
      subst h
      simp [f]
    · intro h
      simp only [f]
      rw [Equiv.symm_apply_eq]
      exact Subtype.ext h
  have hfg : ∀ c p p', f c p = f c p' → g p c = g p' c := by
    intro c p p' h
    have h' := (e3 c).symm.injective h
    exact congrArg Subtype.val h'
  let aff : Fin (q * q) ↪ Fin N :=
    ⟨fun p => (e2 p).1, fun a b h => e2.injective (Subtype.ext h)⟩
  let ln : Fin (q + 1) × Fin q ↪ Fin N := ⟨fun cj => ((e3 cj.1) cj.2).1, by
    rintro ⟨c, j⟩ ⟨c', j'⟩ h
    simp only at h
    have hcc : c = c' := by
      by_contra hcc
      obtain ⟨l0, _, hu⟩ :=
        huniq (e1 c).1 (e1 c').1 (fun h' => hcc (e1.injective (Subtype.ext h')))
      have h1 := ((e3 c) j).2
      have h2 := ((e3 c') j').2
      rw [← h] at h2
      exact h1.2 ((hu _ ⟨h1.1, h2.1⟩).trans (hu L0 ⟨(e1 c).2, (e1 c').2⟩).symm)
    subst hcc
    have hj : j = j' := (e3 c).injective (Subtype.ext h)
    rw [hj]⟩
  refine ⟨aff, ln, f, ?_, ?_⟩
  · intro c c' hcc
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨?_, by simp⟩
    intro p p' h
    simp only [Prod.mk.injEq] at h
    by_contra hpp
    have hq1 : (e2 p).1 ≠ (e2 p').1 := fun h' => hpp (e2.injective (Subtype.ext h'))
    obtain ⟨m, _, hm⟩ := huniq _ _ hq1
    have hA : g p c = g p c' := by
      have k1 := hm (g p c) ⟨(hg p c).1, by rw [hfg c p p' h.1]; exact (hg p' c).1⟩
      have k2 := hm (g p c') ⟨(hg p c').1, by rw [hfg c' p p' h.2]; exact (hg p' c').1⟩
      exact k1.trans k2.symm
    have hcc' : (e1 c).1 ≠ (e1 c').1 := fun h' => hcc (e1.injective (Subtype.ext h'))
    obtain ⟨m2, _, hm2⟩ := huniq _ _ hcc'
    exact hgne p c ((hm2 _ ⟨(hg p c).2, by rw [hA]; exact (hg p c').2⟩).trans
      (hm2 L0 ⟨(e1 c).2, (e1 c').2⟩).symm)
  · intro p c j
    show I (e2 p).1 ((e3 c) j).1 ↔ f c p = j
    rw [hf]
    constructor
    · intro h
      exact (hgu p c _ h ((e3 c) j).2.1).symm
    · intro h
      rw [← h]
      exact (hg p c).1

end PEqualNP.Outside.L_meta_4980

theorem PEqualNP.Outside.L_meta_4980 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3], (0 : ℕ) < x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) → ∃ (x9 : Fin (x1 * x1) ↪ Fin x2) (x10 : Fin (x1 + (1 : ℕ)) × Fin x1 ↪ Fin x2) (x11 : Fin (x1 + (1 : ℕ)) → Fin (x1 * x1) → Fin x1), (∀ (x12 x13 : Fin (x1 + (1 : ℕ))), x12 ≠ x13 → Function.Bijective fun (x15 : Fin (x1 * x1)) => (x11 x12 x15, x11 x13 x15)) ∧ ∀ (x12 : Fin (x1 * x1)) (x13 : Fin (x1 + (1 : ℕ))) (x14 : Fin x1), x3 (x9 x12) (x10 (x13, x14)) ↔ x11 x13 x12 = x14 := by
  intro x1 x2 x3 x4 hq hN hline huniq
  exact PEqualNP.Outside.L_meta_4980.main hq hN hline huniq
