import PEqualNP.Defs

set_option maxHeartbeats 800000 in
theorem PEqualNP.Outside.R_meta_5086_317
    (charge :
      ∀ (n s o q : ℕ) (H : ℕ → Fin n → Set (Fin n)),
        o < n+n+s → (∀ i < n+n, ∀ l, (H i l).ncard ≤ 1) →
        (∀ j < s, ∃ a b, a < b ∧ b < n+n+j ∧ ∀ l, H (n+n+j) l ⊆ H a l ∪ H b l) →
        (∀ l, q+1 ≤ (H o l).ncard) →
        n*q ≤ ∑ j : Fin s, {l : Fin n | n+n+j.val ≤ o ∧ 1 < (H (n+n+j.val) l).ncard ∧
          ∀ k < n+n+j.val, ¬ H (n+n+j.val) l ⊆ H k l}.ncard
    )
    (fork :
      ∀ (n : ℕ) (I : Fin n → Fin n → Prop)
        (X A B : Set (Fin n × Fin n)) (Y D F : Set (Finset (Fin n))) (V : Fin n → Finset (Fin n)),
        X ×ˢ Y ⊆ (A ×ˢ D) ∪ (B ×ˢ F) →
        let H := fun (Z : Set (Fin n × Fin n)) (W : Set (Finset (Fin n))) (l : Fin n) =>
          {p : Fin n | I p l ∧ (p,l) ∈ Z ∧ V l ∈ W}
        ∀ l, ¬ H X Y l ⊆ H A D l → ¬ H X Y l ⊆ H B F l →
          Y ⊆ D ∩ F ∧ V l ∈ Y ∧
          (∃ p, I p l ∧ (p,l) ∈ X \ A) ∧ (∃ r, I r l ∧ (r,l) ∈ X \ B)
    )
    (hard :
      ∀ (q n : ℕ) (I : Fin n → Fin n → Prop) [DecidableRel I],
        250 ≤ q → n = q^2+q+1 → (∀ l, Fintype.card {p // I p l} = q+1) →
        (∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) →
        ∀ (s o : ℕ) (R : ℕ → Set (Fin n × Fin n) × Set (Finset (Fin n))),
        let box := fun w => (R w).1 ×ˢ (R w).2
        o < n+n+s →
        (∀ (i : Fin (n+n)) p l T, ((p,l),T) ∈ box i →
          (i = Fin.castAdd n p ∧ ∃ t ∈ T, I p t) ∨ (i = Fin.natAdd n l ∧ l ∉ T)) →
        (∀ j < s, ∃ a b, a < b ∧ b < n+n+j ∧ box (n+n+j) ⊆ box a ∪ box b) →
        {e | I e.1 e.2} ×ˢ {T | T.card ≤ q} ⊆ box o →
        (∀ V : Fin n → Finset (Fin n), (∀ l, l ∈ V l ∧ (V l).card ≤ q) →
          let active (w : ℕ) := {l : Fin n | V l ∈ (R w).2 ∧
            ∀ k < w, V l ∈ (R k).2 → ∃ p, I p l ∧ (p,l) ∈ (R w).1 \ (R k).1}
          ∀ t : ℕ, 0 < t → t ≤ 100 →
            q*(100-t) < 100 * {j : Fin s | let w := n+n+j.val
              w ≤ o ∧ t < (active w).ncard ∧ ∃ a b, a < b ∧ b < w ∧
                box w ⊆ box a ∪ box b ∧ (R w).2 ⊆ (R a).2 ∩ (R b).2}.ncard) →
        n*q ≤ 100*s
    )
  : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3],   (250 : ℕ) ≤ x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) →         (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) →           ∀ (x9 x10 : ℕ) (x11 : ℕ → Set (Fin x2 × Fin x2) × Set (Finset (Fin x2))),             have x12 : ℕ → Set ((Fin x2 × Fin x2) × Finset (Fin x2)) := fun (x12 : ℕ) => (x11 x12).1 ×ˢ (x11 x12).2;             x10 < x2 + x2 + x9 → (∀ (x14 : Fin (x2 + x2)) (x15 x16 : Fin x2) (x17 : Finset (Fin x2)), ((x15, x16), x17) ∈ x12 ↑x14 → (x14 = Fin.castAdd x2 x15 ∧ ∃ x19 ∈ x17, x3 x15 x19) ∨ x14 = Fin.natAdd x2 x16 ∧ x16 ∉ x17) → (∀ x15 < x9, ∃ (x17 : ℕ) (x18 : ℕ), x17 < x18 ∧ x18 < x2 + x2 + x15 ∧ x12 (x2 + x2 + x15) ⊆ x12 x17 ∪ x12 x18) → {x16 : Fin x2 × Fin x2 | x3 x16.1 x16.2} ×ˢ {x16 : Finset (Fin x2) | x16.card ≤ x1} ⊆ x12 x10 → x2 * x1 ≤ (100 : ℕ) * x9 := by
  classical
  intro q n I inst hq hn deg uniq s o R box ho raw gate output
  by_contra loss
  apply loss
  apply hard q n I hq hn deg uniq s o R ho raw gate output
  intro V hV active t ht ht100
  let H (w : ℕ) (l : Fin n) := {p : Fin n | I p l ∧ (p,l) ∈ (R w).1 ∧ V l ∈ (R w).2}
  have small (i : ℕ) (hi : i < n+n) (l : Fin n) : (H i l).ncard ≤ 1 := by
    apply Set.ncard_le_one_iff_subsingleton.mpr
    intro p hp r hr
    have only (t : Fin n) (ht : t ∈ H i l) : (⟨i,hi⟩ : Fin (n+n)) = Fin.castAdd n t := by
      rcases raw ⟨i,hi⟩ t l (V l) ⟨ht.2.1,ht.2.2⟩ with h | h
      · exact h.1
      · exact False.elim (h.2 (hV l).1)
    exact Fin.ext (congrArg (fun v : Fin (n+n) => v.val) ((only p hp).symm.trans (only r hr)))
  have grow (j : ℕ) (hj : j < s) : ∃ a b, a < b ∧ b < n+n+j ∧
      ∀ l, H (n+n+j) l ⊆ H a l ∪ H b l := by
    obtain ⟨a,b,hab,hb,cover⟩ := gate j hj
    refine ⟨a,b,hab,hb,?_⟩
    intro l p hp
    rcases cover (show ((p,l),(V l)) ∈ box (n+n+j) from ⟨hp.2.1,hp.2.2⟩) with hh | hh
    · exact Or.inl ⟨hp.1,hh.1,hh.2⟩
    · exact Or.inr ⟨hp.1,hh.1,hh.2⟩
  have large (l : Fin n) : q+1 ≤ (H o l).ncard := by
    have all : {p : Fin n | I p l} ⊆ H o l := by
      intro p hp
      have hit := output (show ((p,l),(V l)) ∈
          {e : Fin n × Fin n | I e.1 e.2} ×ˢ {T : Finset (Fin n) | T.card ≤ q} from
        ⟨hp, (hV l).2⟩)
      exact ⟨hp,hit.1,hit.2⟩
    have d : {p : Fin n | I p l}.ncard = q+1 := by
      rw [Set.ncard_eq_toFinset_card', Set.toFinset_card]
      exact deg l
    rw [← d]
    exact Set.ncard_le_ncard all
  have budget := charge n s o q H ho small grow large
  let fresh (j : Fin s) := {l : Fin n | n+n+j.val ≤ o ∧ 1 < (H (n+n+j.val) l).ncard ∧
      ∀ k < n+n+j.val, ¬ H (n+n+j.val) l ⊆ H k l}
  change n*q ≤ ∑ j : Fin s, (fresh j).ncard at budget
  let heavy := {j : Fin s | let w := n+n+j.val
    w ≤ o ∧ t < (active w).ncard ∧ ∃ a b, a < b ∧ b < w ∧
      box w ⊆ box a ∪ box b ∧ (R w).2 ⊆ (R a).2 ∩ (R b).2}
  have member (j : Fin s) (many : t < (fresh j).ncard) : j ∈ heavy := by
    obtain ⟨a,b,hab,hbw,cover⟩ := gate j j.isLt
    let w := n+n+j.val
    have split (l : Fin n) (hl : l ∈ fresh j) : (R w).2 ⊆ (R a).2 ∩ (R b).2 ∧
        V l ∈ (R w).2 ∧ (∃ p, I p l ∧ (p,l) ∈ (R w).1 \ (R a).1) ∧
        (∃ r, I r l ∧ (r,l) ∈ (R w).1 \ (R b).1) := by
      exact fork n I (R w).1 (R a).1 (R b).1 (R w).2 (R a).2 (R b).2 V cover l
        (hl.2.2 a (hab.trans hbw)) (hl.2.2 b hbw)
    have nonempty : (fresh j).Nonempty := (Set.ncard_pos (Set.toFinite _)).mp (by omega)
    obtain ⟨l,hl⟩ := nonempty
    refine ⟨hl.1,many.trans_le ?_,a,b,hab,hbw,cover,(split l hl).1⟩
    apply Set.ncard_le_ncard _ (Set.toFinite _)
    intro m hm
    refine ⟨(split m hm).2.1,?_⟩
    intro k hk hcol
    obtain ⟨p,hp,hpk⟩ := Set.not_subset.mp (hm.2.2 k hk)
    exact ⟨p,hp.1,hp.2.1,fun hrow => hpk ⟨hp.1,hrow,hcol⟩⟩
  have bound (j : Fin s) : (fresh j).ncard ≤ t + (if j ∈ heavy then n else 0) := by
    by_cases h : j ∈ heavy
    · simp only [h, ite_true]
      have : (fresh j).ncard ≤ n := by simpa using (Set.ncard_le_card (fresh j))
      omega
    · simp only [h, ite_false, Nat.add_zero]
      exact Nat.le_of_not_gt (fun h' => h (member j h'))
  have total : n*q ≤ t*s + heavy.ncard*n := by
    apply budget.trans
    calc
      (∑ j : Fin s, (fresh j).ncard) ≤ ∑ j : Fin s, (t + (if j ∈ heavy then n else 0)) :=
        Finset.sum_le_sum fun j _ => bound j
      _ = t*s + heavy.ncard*n := by
        rw [Finset.sum_add_distrib, ← Finset.sum_filter]
        simp [Set.ncard_eq_toFinset_card', Nat.mul_comm]
  change q*(100-t) < 100*heavy.ncard
  have npos : 0 < n := by omega
  have short : 100*s < n*q := Nat.lt_of_not_ge loss
  have lt := Nat.mul_lt_mul_of_pos_left short ht
  have le := Nat.mul_le_mul_left 100 total
  have hsub : 100 - t + t = 100 := Nat.sub_add_cancel ht100
  apply Nat.lt_of_mul_lt_mul_left (a := n)
  nlinarith [congrArg (fun k => n*q*k) hsub]
