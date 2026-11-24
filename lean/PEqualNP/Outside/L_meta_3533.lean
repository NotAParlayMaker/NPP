import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3533_aux

-- q is the AND or the OR of two members of L
def Op (L : List ℕ) (q : ℕ) : Prop :=
  ∃ a ∈ L, ∃ b ∈ L, q = a &&& b ∨ q = a ||| b

-- every entry of Q is an Op of the base list and the entries before it
def V : List ℕ → List ℕ → Prop
  | _, [] => True
  | acc, q :: Q => Op acc q ∧ V (acc ++ [q]) Q

theorem V_iff (Q : List ℕ) : ∀ acc : List ℕ, V acc Q ↔
    ∀ i : Fin Q.length, Op (acc ++ List.take (↑i) Q) (Q.get i) := by
  induction Q with
  | nil => intro acc; simp [V]
  | cons q Q ih =>
    intro acc
    rw [V, ih]
    refine Iff.trans ?_ (Fin.forall_fin_succ (P := fun i : Fin (Q.length + 1) =>
      Op (acc ++ List.take (↑i) (q :: Q)) ((q :: Q).get i))).symm
    simp [List.append_assoc]

theorem V_append (S : List ℕ) : ∀ acc T : List ℕ, V acc (S ++ T) ↔ V acc S ∧ V (acc ++ S) T := by
  induction S with
  | nil => intro acc T; simp [V]
  | cons s S ih =>
    intro acc T
    simp only [List.cons_append, V, ih, List.append_assoc, List.nil_append, and_assoc]

theorem V_snoc (B S : List ℕ) (q : ℕ) : V B (S ++ [q]) ↔ V B S ∧ Op (B ++ S) q := by
  rw [V_append]; simp [V]

theorem Op_mono {L M : List ℕ} {q : ℕ} (h : ∀ a ∈ L, a ∈ M) (hq : Op L q) : Op M q := by
  obtain ⟨a, ha, b, hb, h'⟩ := hq
  exact ⟨a, h a ha, b, h b hb, h'⟩

theorem prune (Q : List ℕ) : ∀ (A B S : List ℕ), (∀ a ∈ A, a ∈ B ∨ a ∈ S) → V A Q → V B S →
    S.Nodup → (∀ s ∈ S, s ∉ B) →
    ∃ R : List ℕ, R.length ≤ S.length + Q.length ∧ V B R ∧ R.Nodup ∧ (∀ r ∈ R, r ∉ B) ∧
      (∀ q ∈ Q, q ∈ B ∨ q ∈ R) ∧ (∀ s ∈ S, s ∈ R) := by
  induction Q with
  | nil =>
    intro A B S _ _ hS hN hD
    exact ⟨S, by simp, hS, hN, hD, by simp, fun s hs => hs⟩
  | cons q Q ih =>
    intro A B S hA hV hS hN hD
    rw [V] at hV
    obtain ⟨hq, hV⟩ := hV
    by_cases hc : q ∈ B ∨ q ∈ S
    · obtain ⟨R, hl, hR, hRN, hRD, hRQ, hRS⟩ := ih (A ++ [q]) B S (by
        intro a ha
        rcases List.mem_append.mp ha with h | h
        · exact hA a h
        · rw [List.mem_singleton] at h; subst h; exact hc) hV hS hN hD
      refine ⟨R, by simp at hl ⊢; omega, hR, hRN, hRD, ?_, hRS⟩
      intro x hx
      rcases List.mem_cons.mp hx with h | h
      · subst h
        rcases hc with h | h
        · exact Or.inl h
        · exact Or.inr (hRS x h)
      · exact hRQ x h
    · obtain ⟨hqB, hqS⟩ := not_or.mp hc
      obtain ⟨R, hl, hR, hRN, hRD, hRQ, hRS⟩ := ih (A ++ [q]) B (S ++ [q]) (by
        intro a ha
        rcases List.mem_append.mp ha with h | h
        · rcases hA a h with h' | h'
          · exact Or.inl h'
          · exact Or.inr (List.mem_append_left _ h')
        · rw [List.mem_singleton] at h; subst h; exact Or.inr (by simp)) hV
        ((V_snoc B S q).mpr ⟨hS, Op_mono (fun a ha => by
          rcases hA a ha with h | h
          · exact List.mem_append_left _ h
          · exact List.mem_append_right _ h) hq⟩)
        (List.nodup_append.mpr ⟨hN, (List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩), by
          intro a ha b hb; rw [List.mem_singleton] at hb; subst hb; intro h; subst h; exact hqS ha⟩)
        (by
          intro s hs
          rcases List.mem_append.mp hs with h | h
          · exact hD s h
          · rw [List.mem_singleton] at h; subst h; exact hqB)
      refine ⟨R, by simp at hl ⊢; omega, hR, hRN, hRD, ?_, fun s hs => hRS s (List.mem_append_left _ hs)⟩
      intro x hx
      rcases List.mem_cons.mp hx with h | h
      · subst h; exact Or.inr (hRS x (by simp))
      · exact hRQ x h

end PEqualNP.Outside.L_meta_3533_aux

theorem PEqualNP.Outside.L_meta_3533 : ∀ (x1 x2 : List ℕ), ∀ x3 ∉ x1, x3 ∈ x2 → (∀ (x6 : Fin x2.length), ∃ x7 ∈ x1 ++ List.take (↑x6) x2, ∃ x8 ∈ x1 ++ List.take (↑x6) x2, x2.get x6 = x7 &&& x8 ∨ x2.get x6 = x7 ||| x8) → ∃ (x7 : List ℕ), x7.length ≤ x2.length ∧ x7.Nodup ∧ (∀ x8 ∈ x7, x8 ∉ x1) ∧ x3 ∈ x7 ∧ ∀ (x8 : Fin x7.length), ∃ x9 ∈ x1 ++ List.take (↑x8) x7, ∃ x10 ∈ x1 ++ List.take (↑x8) x7, x7.get x8 = x9 &&& x10 ∨ x7.get x8 = x9 ||| x10 := by
  intro x1 x2 x3 hx3 hmem hprog
  have hV : PEqualNP.Outside.L_meta_3533_aux.V x1 x2 := (PEqualNP.Outside.L_meta_3533_aux.V_iff x2 x1).mpr hprog
  obtain ⟨R, hl, hR, hRN, hRD, hRQ, _⟩ := PEqualNP.Outside.L_meta_3533_aux.prune x2 x1 x1 [] (fun a ha => Or.inl ha) hV
    (by simp [PEqualNP.Outside.L_meta_3533_aux.V]) List.nodup_nil (by simp)
  refine ⟨R, by simpa using hl, hRN, hRD, ?_, (PEqualNP.Outside.L_meta_3533_aux.V_iff R x1).mp hR⟩
  rcases hRQ x3 hmem with h | h
  · exact absurd h hx3
  · exact h
