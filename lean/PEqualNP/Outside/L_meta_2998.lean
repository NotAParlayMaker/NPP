import Mathlib.Tactic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2998

def Valid {P : Type} (n : ℕ) (V : ℕ → Set P) (i : ℕ) (A : Set (Finset ℕ)) : Prop :=
  (∀ a ∈ A, ∀ j ∈ a, j < n) ∧
    ∀ p, p ∉ V i ↔ ∃ a ∈ A, ∀ j ∈ a, p ∉ V j

def Join (A B : Set (Finset ℕ)) : Set (Finset ℕ) :=
  Set.image2 (fun a b => a ∪ b) A B

def Step (A B C : Set (Finset ℕ)) : Prop :=
  C = Join A B ∨ C = A ∨ C = {∅} ∨ C = A ∪ B

lemma valid_join {P : Type} {n a b i : ℕ} {V : ℕ → Set P} {A B : Set (Finset ℕ)}
    (ha : Valid n V a A) (hb : Valid n V b B) (hi : V i = V a ∪ V b) :
    Valid n V i (Join A B) := by
  constructor
  · rintro c ⟨u, hu, v, hv, rfl⟩ j hj
    rcases Finset.mem_union.mp hj with hj | hj
    · exact ha.1 u hu j hj
    · exact hb.1 v hv j hj
  · intro p
    rw [hi]
    change ¬ (p ∈ V a ∨ p ∈ V b) ↔ _
    rw [not_or]
    constructor
    · rintro ⟨hp, hq⟩
      obtain ⟨u, hu, hpu⟩ := (ha.2 p).mp hp
      obtain ⟨v, hv, hpv⟩ := (hb.2 p).mp hq
      refine ⟨u ∪ v, ⟨u, hu, v, hv, rfl⟩, ?_⟩
      intro j hj
      rcases Finset.mem_union.mp hj with hj | hj
      · exact hpu j hj
      · exact hpv j hj
    · rintro ⟨c, ⟨u, hu, v, hv, rfl⟩, hc⟩
      exact ⟨(ha.2 p).mpr ⟨u, hu, fun j hj => hc j (Finset.mem_union_left _ hj)⟩,
        (hb.2 p).mpr ⟨v, hv, fun j hj => hc j (Finset.mem_union_right _ hj)⟩⟩

lemma valid_empty {P : Type} {n i : ℕ} {V : ℕ → Set P} (hi : V i = ∅) :
    Valid n V i {∅} := by
  constructor
  · rintro a (rfl : a = ∅) j hj
    exact (Finset.notMem_empty j hj).elim
  · intro p
    rw [hi]
    simp

lemma valid_union {P : Type} {n a b i : ℕ} {V : ℕ → Set P} {A B : Set (Finset ℕ)}
    (ha : Valid n V a A) (hb : Valid n V b B) (hi : V i = V a ∩ V b) :
    Valid n V i (A ∪ B) := by
  classical
  constructor
  · intro c hc j hj
    rcases hc with hc | hc
    · exact ha.1 c hc j hj
    · exact hb.1 c hc j hj
  · intro p
    rw [hi]
    change ¬ (p ∈ V a ∧ p ∈ V b) ↔ _
    rw [not_and_or]
    constructor
    · rintro (hp | hp)
      · obtain ⟨c, hc, h⟩ := (ha.2 p).mp hp
        exact ⟨c, Or.inl hc, h⟩
      · obtain ⟨c, hc, h⟩ := (hb.2 p).mp hp
        exact ⟨c, Or.inr hc, h⟩
    · rintro ⟨c, hc, h⟩
      rcases hc with hc | hc
      · exact Or.inl ((ha.2 p).mpr ⟨c, hc, h⟩)
      · exact Or.inr ((hb.2 p).mpr ⟨c, hc, h⟩)

lemma build {P : Type} (n s : ℕ) (V : ℕ → Set P)
    (h : ∀ k < s, ∃ a < n + k, ∃ b < n + k,
      V (n+k) = V a ∪ V b ∨ V (n+k) = V a ∨ V (n+k) = ∅ ∨ V (n+k) = V a ∩ V b) :
    ∃ F : ℕ → Set (Finset ℕ),
      (∀ i < n, F i = {{i}}) ∧
      (∀ k < s, ∃ a < n + k, ∃ b < n + k, Step (F a) (F b) (F (n+k))) ∧
      ∀ i < n + s, Valid n V i (F i) := by
  induction s with
  | zero =>
    refine ⟨fun i => {{i}}, fun _ _ => rfl, ?_, ?_⟩
    · intro k hk
      omega
    · intro i hi
      have hin : i < n := by omega
      constructor
      · intro a ha j hj
        have he : a = {i} := Set.mem_singleton_iff.mp ha
        subst a
        exact (Finset.mem_singleton.mp hj).symm ▸ hin
      · intro p
        constructor
        · intro hp
          refine ⟨{i}, rfl, ?_⟩
          intro j hj
          rw [Finset.mem_singleton.mp hj]
          exact hp
        · rintro ⟨a, ha, h⟩
          have he : a = {i} := Set.mem_singleton_iff.mp ha
          subst a
          exact h i (Finset.mem_singleton_self i)
  | succ s ih =>
    obtain ⟨F, hbase, hstep, hvalid⟩ := ih (fun k hk => h k (by omega))
    obtain ⟨a, ha, b, hb, hop⟩ := h s (by omega)
    have extend (R : Set (Finset ℕ)) (hr : Step (F a) (F b) R)
        (hv : Valid n V (n+s) R) :
        ∃ G : ℕ → Set (Finset ℕ),
          (∀ i < n, G i = {{i}}) ∧
          (∀ k < s+1, ∃ a < n+k, ∃ b < n+k, Step (G a) (G b) (G (n+k))) ∧
          ∀ i < n+(s+1), Valid n V i (G i) := by
      let G := Function.update F (n+s) R
      have same (i : ℕ) (hi : i < n+s) : G i = F i :=
        Function.update_of_ne (Nat.ne_of_lt hi) R F
      refine ⟨G, fun i hi => (same i (by omega)).trans (hbase i hi), ?_, ?_⟩
      · intro k hk
        by_cases hk' : k < s
        · obtain ⟨u, hu, v, hv', hstep'⟩ := hstep k hk'
          refine ⟨u, hu, v, hv', ?_⟩
          simpa only [same u (by omega), same v (by omega), same (n+k) (by omega)] using hstep'
        · have he : k = s := by omega
          subst k
          refine ⟨a, ha, b, hb, ?_⟩
          rw [same a ha, same b hb]
          simpa only [G, Function.update_self] using hr
      · intro i hi
        by_cases hi' : i < n+s
        · rw [same i hi']
          exact hvalid i hi'
        · have he : i = n+s := by omega
          subst i
          simpa only [G, Function.update_self] using hv
    rcases hop with hu | hc | he | hm
    · exact extend (Join (F a) (F b)) (Or.inl rfl)
        (valid_join (hvalid a ha) (hvalid b hb) hu)
    · exact extend (F a) (Or.inr (Or.inl rfl))
        ⟨(hvalid a ha).1, fun p => by rw [hc]; exact (hvalid a ha).2 p⟩
    · exact extend {∅} (Or.inr (Or.inr (Or.inl rfl))) (valid_empty he)
    · exact extend (F a ∪ F b) (Or.inr (Or.inr (Or.inr rfl)))
        (valid_union (hvalid a ha) (hvalid b hb) hm)

end PEqualNP.Outside.L_meta_2998

theorem PEqualNP.Outside.L_meta_2998 : ∀ (x1 : Type) (x2 x3 : ℕ) (x4 : ℕ → Set x1), (∀ x5 < x3, ∃ x7 < x2 + x5, ∃ x8 < x2 + x5, x4 (x2 + x5) = x4 x7 ∪ x4 x8 ∨ x4 (x2 + x5) = x4 x7 ∨ x4 (x2 + x5) = ∅ ∨ x4 (x2 + x5) = x4 x7 ∩ x4 x8) → ∃ (x6 : ℕ → Set (Finset ℕ)), (∀ x7 < x2, x6 x7 = {{x7}}) ∧ (∀ x7 < x3, ∃ x9 < x2 + x7, ∃ x10 < x2 + x7, x6 (x2 + x7) = Set.image2 (fun (x11 x12 : Finset ℕ) => x11 ∪ x12) (x6 x9) (x6 x10) ∨ x6 (x2 + x7) = x6 x9 ∨ x6 (x2 + x7) = {∅} ∨ x6 (x2 + x7) = x6 x9 ∪ x6 x10) ∧ ∀ x7 < x2 + x3, (∀ x9 ∈ x6 x7, ∀ x11 ∈ x9, x11 < x2) ∧ ∀ (x9 : x1), x9 ∉ x4 x7 ↔ ∃ x10 ∈ x6 x7, ∀ x11 ∈ x10, x9 ∉ x4 x11 := by
  intro P n s V h
  exact PEqualNP.Outside.L_meta_2998.build n s V h
