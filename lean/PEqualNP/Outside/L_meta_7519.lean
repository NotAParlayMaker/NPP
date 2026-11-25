import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7519_aux

def Prog (a l : List ℕ) : Prop :=
  ∀ (x3 : Fin l.length), ∃ x4 ∈ a ++ List.take (↑x3) l, ∃ x5 ∈ a ++ List.take (↑x3) l,
    l.get x3 = x4 &&& x5 ∨ l.get x3 = x4 ||| x5

theorem snoc (a l : List ℕ) (v : ℕ) :
    Prog a (l ++ [v]) ↔ Prog a l ∧ ∃ x ∈ a ++ l, ∃ y ∈ a ++ l, v = x &&& y ∨ v = x ||| y := by
  constructor
  · intro h
    refine ⟨fun i => ?_, ?_⟩
    · have := h ⟨i.1, by simp⟩
      simpa [List.take_append_of_le_length (Nat.le_of_lt i.2), List.getElem_append_left i.2] using this
    · have := h ⟨l.length, by simp⟩
      simpa using this
  · rintro ⟨h1, h2⟩ ⟨i, hi0⟩
    rcases Nat.lt_or_ge i l.length with hi | hi
    · have := h1 ⟨i, hi⟩
      simpa [List.take_append_of_le_length (Nat.le_of_lt hi), List.getElem_append_left hi] using this
    · have hi2 : i = l.length := by simp at hi0; omega
      subst hi2
      simpa using h2

theorem mem_of_forall2 {R : ℕ → ℕ → Prop} {l m : List ℕ} (h : List.Forall₂ R l m) :
    ∀ x ∈ l, ∃ y ∈ m, R x y := by
  induction h with
  | nil => simp
  | cons hab _ ih =>
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨_, List.mem_cons_self, hab⟩
    · obtain ⟨y, hy, hr⟩ := ih x hx
      exact ⟨y, List.mem_cons_of_mem _ hy, hr⟩

theorem main (x2 x3 : List ℕ) (R : ℕ → ℕ → Prop) (h1 : ∀ x5 ∈ x2, ∃ x7 ∈ x3, R x5 x7)
    (h2 : ∀ (x6 x7 x8 x9 : ℕ), R x6 x8 → R x7 x9 → R (x6 &&& x7) (x8 &&& x9) ∧ R (x6 ||| x7) (x8 ||| x9)) :
    ∀ x7 : List ℕ, Prog x2 x7 → ∃ x9, List.Forall₂ R x7 x9 ∧ Prog x3 x9 := by
  intro x7
  induction x7 using List.reverseRecOn with
  | nil => exact fun _ => ⟨[], .nil, fun i => i.elim0⟩
  | append_singleton l v ih =>
    intro h
    rw [snoc] at h
    obtain ⟨hl, x, hx, y, hy, hv⟩ := h
    obtain ⟨m, hm, hp⟩ := ih hl
    have key : ∀ x ∈ x2 ++ l, ∃ x' ∈ x3 ++ m, R x x' := by
      intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · obtain ⟨z, hz, hr⟩ := h1 x hx
        exact ⟨z, List.mem_append_left _ hz, hr⟩
      · obtain ⟨z, hz, hr⟩ := mem_of_forall2 hm x hx
        exact ⟨z, List.mem_append_right _ hz, hr⟩
    obtain ⟨x', hx', rx⟩ := key x hx
    obtain ⟨y', hy', ry⟩ := key y hy
    rcases hv with hv | hv
    · exact ⟨m ++ [x' &&& y'], List.rel_append hm (.cons (hv ▸ (h2 _ _ _ _ rx ry).1) .nil),
        (snoc _ _ _).2 ⟨hp, x', hx', y', hy', Or.inl rfl⟩⟩
    · exact ⟨m ++ [x' ||| y'], List.rel_append hm (.cons (hv ▸ (h2 _ _ _ _ rx ry).2) .nil),
        (snoc _ _ _).2 ⟨hp, x', hx', y', hy', Or.inr rfl⟩⟩

end PEqualNP.Outside.L_meta_7519_aux

theorem PEqualNP.Outside.L_meta_7519 : have x1 : List ℕ → List ℕ → Prop := fun (x1 x2 : List ℕ) => ∀ (x3 : Fin x2.length), ∃ x4 ∈ x1 ++ List.take (↑x3) x2, ∃ x5 ∈ x1 ++ List.take (↑x3) x2, x2.get x3 = x4 &&& x5 ∨ x2.get x3 = x4 ||| x5; ∀ (x2 x3 : List ℕ) (x4 : ℕ → ℕ → Prop), (∀ x5 ∈ x2, ∃ x7 ∈ x3, x4 x5 x7) → (∀ (x6 x7 x8 x9 : ℕ), x4 x6 x8 → x4 x7 x9 → x4 (x6 &&& x7) (x8 &&& x9) ∧ x4 (x6 ||| x7) (x8 ||| x9)) → ∀ (x7 : List ℕ), x1 x2 x7 → ∃ (x9 : List ℕ), x9.length = x7.length ∧ x1 x3 x9 ∧ ∀ x10 ∈ x7, ∃ x12 ∈ x9, x4 x10 x12 := by
  intro x1 x2 x3 x4 h1 h2 x7 h7
  obtain ⟨x9, hf, hp⟩ := PEqualNP.Outside.L_meta_7519_aux.main x2 x3 x4 h1 h2 x7 h7
  exact ⟨x9, hf.length_eq.symm, hp, PEqualNP.Outside.L_meta_7519_aux.mem_of_forall2 hf⟩
