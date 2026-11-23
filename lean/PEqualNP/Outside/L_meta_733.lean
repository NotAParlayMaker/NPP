import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_733_aux

lemma lhs_to_rhs {n : ℕ} (G : SimpleGraph (Fin n)) (X : Set (Fin n))
    (hbip : ∀ u v, G.Adj u v → (u ∈ X ↔ v ∉ X))
    (I : Set (Fin n))
    (hind : ∀ u ∈ I, ∀ v ∈ I, ¬ G.Adj u v)
    (hdom : ∀ v, v ∉ I → ∃ u ∈ I, G.Adj v u) :
    ∃ B : Set (Fin n), (∀ b ∈ B, b ∉ X) ∧
      (∀ y, y ∉ X → ((∀ x, G.Adj y x → ∃ b ∈ B, G.Adj x b) ↔ y ∈ B)) ∧
      ∀ v, v ∈ I ↔ (v ∈ B ∨ (v ∈ X ∧ ∀ b ∈ B, ¬ G.Adj v b)) := by
  let B : Set (Fin n) := {v ∈ I | v ∉ X}
  refine ⟨B, ?_, ?_, ?_⟩
  · intro b hb
    exact hb.2
  · intro y hy
    constructor
    · intro hy_all
      by_contra hy_not_B
      have hy_not_I : y ∉ I := by
        intro hyI
        exact hy_not_B ⟨hyI, hy⟩
      obtain ⟨u, huI, hadj_yu⟩ := hdom y hy_not_I
      have huX : u ∈ X := by
        have := hbip y u hadj_yu
        tauto
      obtain ⟨b, hbB, hadj_ub⟩ := hy_all u hadj_yu
      exact hind u huI b hbB.1 hadj_ub
    · intro hyB x hadj_yx
      exact ⟨y, hyB, hadj_yx.symm⟩
  · intro v
    constructor
    · intro hvI
      by_cases hvX : v ∈ X
      · right
        refine ⟨hvX, ?_⟩
        intro b hb hadj_vb
        exact hind v hvI b hb.1 hadj_vb
      · left
        exact ⟨hvI, hvX⟩
    · rintro (⟨hvI, _⟩ | ⟨hvX, hnone⟩)
      · exact hvI
      · by_contra hv_not_I
        obtain ⟨u, huI, hadj_vu⟩ := hdom v hv_not_I
        have hu_not_X : u ∉ X := by
          have := hbip v u hadj_vu
          tauto
        have huB : u ∈ B := ⟨huI, hu_not_X⟩
        exact hnone u huB hadj_vu

lemma rhs_to_lhs {n : ℕ} (G : SimpleGraph (Fin n)) (X : Set (Fin n))
    (hbip : ∀ u v, G.Adj u v → (u ∈ X ↔ v ∉ X))
    (I : Set (Fin n))
    (hB : ∃ B : Set (Fin n), (∀ b ∈ B, b ∉ X) ∧
      (∀ y, y ∉ X → ((∀ x, G.Adj y x → ∃ b ∈ B, G.Adj x b) ↔ y ∈ B)) ∧
      ∀ v, v ∈ I ↔ (v ∈ B ∨ (v ∈ X ∧ ∀ b ∈ B, ¬ G.Adj v b))) :
    (∀ u ∈ I, ∀ v ∈ I, ¬ G.Adj u v) ∧ (∀ v, v ∉ I → ∃ u ∈ I, G.Adj v u) := by
  obtain ⟨B, hBX, hB_sat, hI_def⟩ := hB
  constructor
  · intro u hu v hv hadj_uv
    have hcases := hbip u v hadj_uv
    by_cases huX : u ∈ X
    · have hvX : v ∉ X := by tauto
      have hu_spec : ∀ b ∈ B, ¬ G.Adj u b := by
        have hu_cases := (hI_def u).mp hu
        rcases hu_cases with huB | ⟨_, hu_spec⟩
        · exact False.elim (hBX u huB huX)
        · exact hu_spec
      have hvB : v ∈ B := by
        have hv_cases := (hI_def v).mp hv
        rcases hv_cases with hvB | ⟨hvX', _⟩
        · exact hvB
        · exact False.elim (hvX hvX')
      exact hu_spec v hvB hadj_uv
    · have hvX : v ∈ X := by tauto
      have hv_spec : ∀ b ∈ B, ¬ G.Adj v b := by
        have hv_cases := (hI_def v).mp hv
        rcases hv_cases with hvB | ⟨_, hv_spec⟩
        · exact False.elim (hBX v hvB hvX)
        · exact hv_spec
      have huB : u ∈ B := by
        have hu_cases := (hI_def u).mp hu
        rcases hu_cases with huB | ⟨huX', _⟩
        · exact huB
        · exact False.elim (huX huX')
      exact hv_spec u huB hadj_uv.symm
  · intro v hv_not_I
    have hv_not_B : v ∉ B := by
      intro hvB
      exact hv_not_I ((hI_def v).mpr (Or.inl hvB))
    by_cases hvX : v ∈ X
    · have h_ex_adj : ¬ (∀ b ∈ B, ¬ G.Adj v b) := by
        intro hnone
        exact hv_not_I ((hI_def v).mpr (Or.inr ⟨hvX, hnone⟩))
      push_neg at h_ex_adj
      obtain ⟨b, hbB, hadj_vb⟩ := h_ex_adj
      have hbI : b ∈ I := (hI_def b).mpr (Or.inl hbB)
      exact ⟨b, hbI, hadj_vb⟩
    · have h_not_sat : ¬ (∀ x, G.Adj v x → ∃ b ∈ B, G.Adj x b) := by
        intro h_sat
        exact hv_not_B ((hB_sat v hvX).mp h_sat)
      push_neg at h_not_sat
      obtain ⟨x, hadj_vx, hx_none⟩ := h_not_sat
      have hxX : x ∈ X := by
        have := hbip v x hadj_vx
        tauto
      have hxI : x ∈ I := by
        apply (hI_def x).mpr
        right
        exact ⟨hxX, fun b hb hadj_xb => hx_none b hb hadj_xb⟩
      exact ⟨x, hxI, hadj_vx.symm⟩

end PEqualNP.Outside.L_meta_733_aux

theorem PEqualNP.Outside.L_meta_733 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (X : Set (Fin n)),
  (∀ u v, G.Adj u v → (u ∈ X ↔ v ∉ X)) →
  ∀ I : Set (Fin n),
    ((∀ u ∈ I, ∀ v ∈ I, ¬ G.Adj u v) ∧ (∀ v, v ∉ I → ∃ u ∈ I, G.Adj v u)) ↔
    ∃ B : Set (Fin n), (∀ b ∈ B, b ∉ X) ∧
      (∀ y, y ∉ X → ((∀ x, G.Adj y x → ∃ b ∈ B, G.Adj x b) ↔ y ∈ B)) ∧
      ∀ v, v ∈ I ↔ (v ∈ B ∨ (v ∈ X ∧ ∀ b ∈ B, ¬ G.Adj v b)) := by
  intro n G X hbip I
  constructor
  · rintro ⟨hind, hdom⟩
    exact PEqualNP.Outside.L_meta_733_aux.lhs_to_rhs G X hbip I hind hdom
  · intro hB
    exact PEqualNP.Outside.L_meta_733_aux.rhs_to_lhs G X hbip I hB
