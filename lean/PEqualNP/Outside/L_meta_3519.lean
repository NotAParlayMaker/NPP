import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3519

lemma sum_filter_ne_nil (l : List (ℕ × List ℕ)) :
    ((l.filter (fun s => s.2 ≠ [])).map (fun s => s.2.length)).sum =
      (l.map (fun s => s.2.length)).sum := by
  induction l with
  | nil => simp
  | cons s t ih =>
    rw [List.filter_cons]
    split <;> simp_all

lemma point_sum {x1 x2 : ℕ} (x3 : Finset (Fin x1 × Fin x2)) (x4 : Finset (Fin x1)) :
    ∑ a ∈ x4, (x3.filter (fun e => e.1 = a)).card = (x3.filter (fun e => e.1 ∈ x4)).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst)
    (s := x3.filter (fun e => e.1 ∈ x4)) (t := x4)
    (by
      intro e he
      rw [Finset.mem_coe, Finset.mem_filter] at he
      exact Finset.mem_coe.mpr he.2)]
  refine Finset.sum_congr rfl (fun a ha => ?_)
  congr 1
  ext e
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h1, h2 ▸ ha⟩, h2⟩
  · rintro ⟨⟨h1, -⟩, h2⟩
    exact ⟨h1, h2⟩

lemma line_sum {x1 x2 : ℕ} (x3 : Finset (Fin x1 × Fin x2)) (x4 : Finset (Fin x1))
    (x5 : Finset (Fin x2)) (hcov : ∀ e ∈ x3, e.1 ∈ x4 ∨ e.2 ∈ x5) :
    ∑ b ∈ x5, (x3.filter (fun e => e.2 = b ∧ e.1 ∉ x4)).card =
      (x3.filter (fun e => ¬ e.1 ∈ x4)).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.snd)
    (s := x3.filter (fun e => ¬ e.1 ∈ x4)) (t := x5)
    (by
      intro e he
      rw [Finset.mem_coe, Finset.mem_filter] at he
      exact Finset.mem_coe.mpr ((hcov e he.1).resolve_left he.2))]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  congr 1
  ext e
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, h3⟩, h2⟩
  · rintro ⟨⟨h1, h3⟩, h2⟩
    exact ⟨h1, h2, h3⟩

end PEqualNP.Outside.L_meta_3519

theorem PEqualNP.Outside.L_meta_3519 : ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : Finset (Fin x1)) (x5 : Finset (Fin x2)), (∀ x6 ∈ x3, x6.1 ∈ x4 ∨ x6.2 ∈ x5) → ∃ (x7 : List (ℕ × List ℕ)), (∀ x8 ∈ x7, x8.2 ≠ [] ∧ ((x8.1 < x1 ∧ ∀ x10 ∈ x8.2, x1 ≤ x10 ∧ x10 < x1 + x2) ∨ x1 ≤ x8.1 ∧ x8.1 < x1 + x2 ∧ ∀ x10 ∈ x8.2, x10 < x1)) ∧ (∀ (x8 : Fin x1) (x9 : Fin x2), (x8, x9) ∈ x3 ↔ ∃ x10 ∈ x7, x10.1 = ↑x8 ∧ x1 + ↑x9 ∈ x10.2 ∨ x10.1 = x1 + ↑x9 ∧ ↑x8 ∈ x10.2) ∧ (List.map (fun (x8 : ℕ × List ℕ) => x8.2.length) x7).sum + x7.length - (1 : ℕ) ≤ x3.card + x4.card + x5.card - (1 : ℕ) := by
  intro x1 x2 x3 x4 x5 hcov
  let lp : Fin x1 → List ℕ := fun a =>
    (x3.filter (fun e => e.1 = a)).toList.map (fun e => x1 + (e.2 : ℕ))
  let ll : Fin x2 → List ℕ := fun b =>
    (x3.filter (fun e => e.2 = b ∧ e.1 ∉ x4)).toList.map (fun e => (e.1 : ℕ))
  let A : List (ℕ × List ℕ) := x4.toList.map (fun (a : Fin x1) => ((a : ℕ), lp a))
  let B : List (ℕ × List ℕ) := x5.toList.map (fun (b : Fin x2) => (x1 + (b : ℕ), ll b))
  refine ⟨(A ++ B).filter (fun s => s.2 ≠ []), ?_, ?_, ?_⟩
  · intro s hs
    rw [List.mem_filter] at hs
    obtain ⟨hs, hne⟩ := hs
    refine ⟨by simpa using hne, ?_⟩
    rcases List.mem_append.mp hs with h | h
    · obtain ⟨a, -, rfl⟩ := List.mem_map.mp h
      left
      refine ⟨a.isLt, ?_⟩
      intro t ht
      obtain ⟨e, -, rfl⟩ := List.mem_map.mp ht
      exact ⟨Nat.le_add_right _ _, Nat.add_lt_add_left e.2.isLt _⟩
    · obtain ⟨b, -, rfl⟩ := List.mem_map.mp h
      right
      refine ⟨Nat.le_add_right _ _, Nat.add_lt_add_left b.isLt _, ?_⟩
      intro t ht
      obtain ⟨e, -, rfl⟩ := List.mem_map.mp ht
      exact e.1.isLt
  · intro a b
    constructor
    · intro hab
      by_cases ha : a ∈ x4
      · have hmem : x1 + (b : ℕ) ∈ lp a :=
          List.mem_map.mpr ⟨(a, b), by simp [hab], rfl⟩
        refine ⟨((a : ℕ), lp a), ?_, Or.inl ⟨rfl, hmem⟩⟩
        rw [List.mem_filter]
        refine ⟨List.mem_append_left _ (List.mem_map.mpr ⟨a, Finset.mem_toList.mpr ha, rfl⟩), ?_⟩
        simpa using List.ne_nil_of_mem hmem
      · have hb : b ∈ x5 := (hcov (a, b) hab).resolve_left ha
        have hmem : (a : ℕ) ∈ ll b :=
          List.mem_map.mpr ⟨(a, b), by simp [hab, ha], rfl⟩
        refine ⟨(x1 + (b : ℕ), ll b), ?_, Or.inr ⟨rfl, hmem⟩⟩
        rw [List.mem_filter]
        refine ⟨List.mem_append_right _ (List.mem_map.mpr ⟨b, Finset.mem_toList.mpr hb, rfl⟩), ?_⟩
        simpa using List.ne_nil_of_mem hmem
    · rintro ⟨s, hs, h⟩
      rw [List.mem_filter] at hs
      rcases List.mem_append.mp hs.1 with hA | hB
      · obtain ⟨a', -, rfl⟩ := List.mem_map.mp hA
        rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · have h1' : (a' : ℕ) = a := h1
          have haa : a' = a := Fin.ext h1'
          subst haa
          obtain ⟨e, he, heq⟩ := List.mem_map.mp h2
          rw [Finset.mem_toList, Finset.mem_filter] at he
          have hb : e.2 = b := Fin.ext (Nat.add_left_cancel heq)
          have hee : e = (a', b) := Prod.ext he.2 hb
          rw [← hee]
          exact he.1
        · exfalso
          have := a'.isLt
          have h1' : (a' : ℕ) = x1 + b := h1
          omega
      · obtain ⟨b', -, rfl⟩ := List.mem_map.mp hB
        rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exfalso
          have := a.isLt
          have h1' : x1 + (b' : ℕ) = a := h1
          omega
        · have h1' : x1 + (b' : ℕ) = x1 + b := h1
          have hbb : b' = b := Fin.ext (Nat.add_left_cancel h1')
          subst hbb
          obtain ⟨e, he, heq⟩ := List.mem_map.mp h2
          rw [Finset.mem_toList, Finset.mem_filter] at he
          have hee : e = (a, b') := Prod.ext (Fin.ext heq) he.2.1
          rw [← hee]
          exact he.1
  · apply Nat.sub_le_sub_right
    have hsum := PEqualNP.Outside.L_meta_3519.sum_filter_ne_nil (A ++ B)
    have hlen : ((A ++ B).filter (fun s => s.2 ≠ [])).length ≤ (A ++ B).length :=
      List.length_filter_le _ _
    have hAB : (A ++ B).length = x4.card + x5.card := by
      simp [A, B]
    have happ : ((A ++ B).map (fun s => s.2.length)).sum =
        (A.map (fun s => s.2.length)).sum + (B.map (fun s => s.2.length)).sum := by
      rw [List.map_append, List.sum_append]
    have hsA : (A.map (fun s => s.2.length)).sum =
        (x3.filter (fun e => e.1 ∈ x4)).card := by
      rw [← PEqualNP.Outside.L_meta_3519.point_sum x3 x4, ← Finset.sum_map_toList]
      simp [A, lp, Function.comp_def]
    have hsB : (B.map (fun s => s.2.length)).sum =
        (x3.filter (fun e => ¬ e.1 ∈ x4)).card := by
      rw [← PEqualNP.Outside.L_meta_3519.line_sum x3 x4 x5 hcov, ← Finset.sum_map_toList]
      simp [B, ll, Function.comp_def]
    have hsplit := Finset.card_filter_add_card_filter_not (s := x3)
      (fun e : Fin x1 × Fin x2 => e.1 ∈ x4)
    omega
