import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4867_aux

open PEqualNP.HeptadCover

-- membership of a difference in the Singer difference set, as a Boolean
def dB (d : ℕ) : Bool := d == 0 || d == 1 || d == 3 || d == 9

-- incidence of point p with line l, as a Boolean
def I (p l : Fin 13) : Bool := dB ((p.val + 13 - l.val) % 13)

theorem mem_iff {p l : Fin 13} : p ∈ singerLines3 l ↔ I p l = true := by
  simp [singerLines3, I, dB, or_assoc]

theorem mem_miss (l : Fin 13) (P : Finset (Fin 13)) :
    l ∈ missLines singerLines3 P ↔ ∀ x ∈ P, I x l = false := by
  simp only [missLines, Finset.mem_filter, Finset.mem_univ, true_and, Finset.disjoint_right,
    mem_iff, Bool.not_eq_true]

-- incidence is invariant under the cyclic shift
theorem tr : ∀ c p l : Fin 13, I (p + c) (l + c) = I p l := by decide +kernel

theorem offPt : ∀ l1 l2 l3 : Fin 13, ∃ p : Fin 13,
    I p l1 = false ∧ I p l2 = false ∧ I p l3 = false := by decide +kernel

theorem offLine : ∀ p1 p2 p3 : Fin 13, ∃ l : Fin 13,
    I p1 l = false ∧ I p2 l = false ∧ I p3 l = false := by decide +kernel

def Hyp (p1 p2 p3 l1 l2 l3 : Fin 13) : Prop :=
  (∀ l : Fin 13, ¬ (p1 ≠ p2 ∧ p1 ≠ p3 ∧ p2 ≠ p3 ∧ I p1 l = true ∧ I p2 l = true ∧ I p3 l = true)) ∧
  (∀ p : Fin 13, ¬ (l1 ≠ l2 ∧ l1 ≠ l3 ∧ l2 ≠ l3 ∧ I p l1 = true ∧ I p l2 = true ∧ I p l3 = true)) ∧
  (I p1 l1 = false ∧ I p2 l1 = false ∧ I p3 l1 = false) ∧
  (I p1 l2 = false ∧ I p2 l2 = false ∧ I p3 l2 = false) ∧
  (I p1 l3 = false ∧ I p2 l3 = false ∧ I p3 l3 = false)

def Good (p1 p2 p3 l1 l2 l3 p : Fin 13) : Prop :=
  I p l1 = false ∧ I p l2 = false ∧ I p l3 = false ∧ p ≠ p1 ∧ p ≠ p2 ∧ p ≠ p3 ∧
  ∀ l : Fin 13, I p l = true →
    ((I p1 l = true ∧ I p2 l = true → p1 = p2) ∧ (I p1 l = true ∧ I p3 l = true → p1 = p3) ∧
      (I p2 l = true ∧ I p3 l = true → p2 = p3))

def H1b (q2 q3 : Fin 13) : Bool :=
  decide (∀ l : Fin 13, ¬ ((0 : Fin 13) ≠ q2 ∧ (0 : Fin 13) ≠ q3 ∧ q2 ≠ q3 ∧
      I 0 l = true ∧ I q2 l = true ∧ I q3 l = true))

def H2b (m1 m2 m3 : Fin 13) : Bool :=
  decide (∀ p : Fin 13, ¬ (m1 ≠ m2 ∧ m1 ≠ m3 ∧ m2 ≠ m3 ∧
      I p m1 = true ∧ I p m2 = true ∧ I p m3 = true))

def Gb (q2 q3 m1 m2 m3 : Fin 13) : Bool :=
  decide (∃ p : Fin 13, I p m1 = false ∧ I p m2 = false ∧ I p m3 = false ∧
      p ≠ 0 ∧ p ≠ q2 ∧ p ≠ q3 ∧
      ∀ l : Fin 13, I p l = true →
        ((I 0 l = true ∧ I q2 l = true → (0 : Fin 13) = q2) ∧
          (I 0 l = true ∧ I q3 l = true → (0 : Fin 13) = q3) ∧
          (I q2 l = true ∧ I q3 l = true → q2 = q3)))

-- the finite check, with the first point shifted to 0
set_option maxHeartbeats 0 in
theorem core0 : ∀ q2 q3 : Fin 13, H1b q2 q3 = true →
    ∀ m1 : Fin 13, I 0 m1 = false → I q2 m1 = false → I q3 m1 = false →
    ∀ m2 : Fin 13, I 0 m2 = false → I q2 m2 = false → I q3 m2 = false →
    ∀ m3 : Fin 13, I 0 m3 = false → I q2 m3 = false → I q3 m3 = false →
    H2b m1 m2 m3 = true → Gb q2 q3 m1 m2 m3 = true := by
  decide +kernel

theorem core0' (q2 q3 m1 m2 m3 : Fin 13) (h : Hyp 0 q2 q3 m1 m2 m3) :
    ∃ p, Good 0 q2 q3 m1 m2 m3 p := by
  obtain ⟨h1, h2, ⟨a1, a2, a3⟩, ⟨b1, b2, b3⟩, ⟨c1, c2, c3⟩⟩ := h
  have e1 : H1b q2 q3 = true := by
    unfold H1b
    exact decide_eq_true h1
  have e2 : H2b m1 m2 m3 = true := by
    unfold H2b
    exact decide_eq_true h2
  have r := core0 q2 q3 e1 m1 a1 a2 a3 m2 b1 b2 b3 m3 c1 c2 c3 e2
  unfold Gb at r
  have r' := of_decide_eq_true r
  exact r'

theorem Hyp_tr (c : Fin 13) {a1 a2 a3 l1 l2 l3 : Fin 13}
    (h : Hyp (a1 + c) (a2 + c) (a3 + c) (l1 + c) (l2 + c) (l3 + c)) :
    Hyp a1 a2 a3 l1 l2 l3 := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun l => ?_, fun p => ?_, ?_⟩
  · have := h1 (l + c)
    simpa [tr] using this
  · have := h2 (p + c)
    simpa [tr] using this
  · simpa [tr] using h3

theorem Good_tr (c : Fin 13) {a1 a2 a3 l1 l2 l3 p : Fin 13}
    (g : Good a1 a2 a3 l1 l2 l3 p) :
    Good (a1 + c) (a2 + c) (a3 + c) (l1 + c) (l2 + c) (l3 + c) (p + c) := by
  obtain ⟨g1, g2, g3, g4, g5, g6, g7⟩ := g
  refine ⟨by simpa [tr] using g1, by simpa [tr] using g2, by simpa [tr] using g3,
    by simpa using g4, by simpa using g5, by simpa using g6, fun l hl => ?_⟩
  obtain ⟨l', rfl⟩ : ∃ l', l = l' + c := ⟨l - c, (sub_add_cancel l c).symm⟩
  have := g7 l' (by simpa [tr] using hl)
  simpa [tr] using this

theorem gen (p1 p2 p3 l1 l2 l3 : Fin 13) (h : Hyp p1 p2 p3 l1 l2 l3) :
    ∃ p, Good p1 p2 p3 l1 l2 l3 p := by
  have h' : Hyp 0 (p2 - p1) (p3 - p1) (l1 - p1) (l2 - p1) (l3 - p1) :=
    Hyp_tr p1 (by simpa using h)
  obtain ⟨p, hp⟩ := core0' _ _ _ _ _ h'
  have := Good_tr p1 hp
  exact ⟨p + p1, by simpa using this⟩

theorem rep (A : Finset (Fin 13)) (h : A.card ≤ 3) : A = ∅ ∨ ∃ a b c, A = {a, b, c} := by
  have : A.card = 0 ∨ A.card = 1 ∨ A.card = 2 ∨ A.card = 3 := by omega
  rcases this with h | h | h | h
  · left
    exact Finset.card_eq_zero.mp h
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h
    exact Or.inr ⟨a, a, a, by simp⟩
  · obtain ⟨a, b, _, rfl⟩ := Finset.card_eq_two.mp h
    exact Or.inr ⟨a, a, b, by simp⟩
  · obtain ⟨a, b, c, _, _, _, rfl⟩ := Finset.card_eq_three.mp h
    exact Or.inr ⟨a, b, c, rfl⟩

theorem H1of {p1 p2 p3 : Fin 13}
    (hP : ∀ l : Fin 13, (({p1, p2, p3} : Finset (Fin 13)) ∩ singerLines3 l).card ≤ 2) :
    ∀ l : Fin 13, ¬ (p1 ≠ p2 ∧ p1 ≠ p3 ∧ p2 ≠ p3 ∧
      I p1 l = true ∧ I p2 l = true ∧ I p3 l = true) := by
  rintro l ⟨n12, n13, n23, i1, i2, i3⟩
  have := hP l
  have e : ({p1, p2, p3} : Finset (Fin 13)) ∩ singerLines3 l = {p1, p2, p3} := by
    apply Finset.inter_eq_left.mpr
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with hx | hx | hx <;> rw [hx]
    · exact mem_iff.mpr i1
    · exact mem_iff.mpr i2
    · exact mem_iff.mpr i3
  rw [e, Finset.card_eq_three.mpr ⟨p1, p2, p3, n12, n13, n23, rfl⟩] at this
  omega

theorem H2of {l1 l2 l3 : Fin 13}
    (hL : ∀ p : Fin 13,
      (Finset.filter (fun l => p ∈ singerLines3 l) ({l1, l2, l3} : Finset (Fin 13))).card ≤ 2) :
    ∀ p : Fin 13, ¬ (l1 ≠ l2 ∧ l1 ≠ l3 ∧ l2 ≠ l3 ∧
      I p l1 = true ∧ I p l2 = true ∧ I p l3 = true) := by
  rintro p ⟨n12, n13, n23, i1, i2, i3⟩
  have := hL p
  have e : Finset.filter (fun l => p ∈ singerLines3 l) ({l1, l2, l3} : Finset (Fin 13))
      = {l1, l2, l3} := by
    apply Finset.filter_true_of_mem
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with hx | hx | hx <;> rw [hx]
    · exact mem_iff.mpr i1
    · exact mem_iff.mpr i2
    · exact mem_iff.mpr i3
  rw [e, Finset.card_eq_three.mpr ⟨l1, l2, l3, n12, n13, n23, rfl⟩] at this
  omega

theorem finish {p1 p2 p3 l1 l2 l3 p : Fin 13} {L : Finset (Fin 13)}
    (hP : ∀ l : Fin 13, (({p1, p2, p3} : Finset (Fin 13)) ∩ singerLines3 l).card ≤ 2)
    (hsub : L ⊆ {l1, l2, l3})
    (hm : L ⊆ missLines singerLines3 {p1, p2, p3})
    (g : Good p1 p2 p3 l1 l2 l3 p) :
    p ∉ ({p1, p2, p3} : Finset (Fin 13)) ∧
    (∀ l : Fin 13, (insert p ({p1, p2, p3} : Finset (Fin 13)) ∩ singerLines3 l).card ≤ 2) ∧
    L ⊆ missLines singerLines3 (insert p ({p1, p2, p3} : Finset (Fin 13))) := by
  obtain ⟨g1, g2, g3, g4, g5, g6, sec⟩ := g
  refine ⟨?_, ?_, ?_⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (h | h | h)
    · exact g4 h
    · exact g5 h
    · exact g6 h
  · intro l
    by_cases hpl : p ∈ singerLines3 l
    · rw [Finset.insert_inter_of_mem hpl]
      obtain ⟨s12, s13, s23⟩ := sec l (mem_iff.mp hpl)
      have : (({p1, p2, p3} : Finset (Fin 13)) ∩ singerLines3 l).card ≤ 1 := by
        apply Finset.card_le_one.mpr
        intro a ha b hb
        simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton, mem_iff] at ha hb
        obtain ⟨ha1, ha2⟩ := ha
        obtain ⟨hb1, hb2⟩ := hb
        rcases ha1 with rfl | rfl | rfl <;> rcases hb1 with rfl | rfl | rfl <;>
          first
          | rfl
          | exact s12 ⟨ha2, hb2⟩
          | exact (s12 ⟨hb2, ha2⟩).symm
          | exact s13 ⟨ha2, hb2⟩
          | exact (s13 ⟨hb2, ha2⟩).symm
          | exact s23 ⟨ha2, hb2⟩
          | exact (s23 ⟨hb2, ha2⟩).symm
      exact (Finset.card_insert_le _ _).trans (by omega)
    · have e : insert p ({p1, p2, p3} : Finset (Fin 13)) ∩ singerLines3 l
          = ({p1, p2, p3} : Finset (Fin 13)) ∩ singerLines3 l := by
        ext x
        simp only [Finset.mem_inter, Finset.mem_insert]
        constructor
        · rintro ⟨h | h, h2⟩
          · rw [h] at h2
            exact absurd h2 hpl
          · exact ⟨h, h2⟩
        · rintro ⟨h, h2⟩
          exact ⟨Or.inr h, h2⟩
      rw [e]
      exact hP l
  · intro l hl
    rw [mem_miss]
    intro x hx
    rcases Finset.mem_insert.mp hx with hx | hx
    · rw [hx]
      have hl' := hsub hl
      simp only [Finset.mem_insert, Finset.mem_singleton] at hl'
      rcases hl' with h | h | h <;> rw [h]
      · exact g1
      · exact g2
      · exact g3
    · exact (mem_miss l _).mp (hm hl) x hx

theorem step (P L : Finset (Fin 13)) (hc : P.card ≤ 3) (hcL : L.card ≤ 3)
    (hP : ∀ l : Fin 13, (P ∩ singerLines3 l).card ≤ 2)
    (hL : ∀ p : Fin 13, (Finset.filter (fun l => p ∈ singerLines3 l) L).card ≤ 2)
    (hm : L ⊆ missLines singerLines3 P) :
    ∃ p, p ∉ P ∧ (∀ l : Fin 13, (insert p P ∩ singerLines3 l).card ≤ 2) ∧
      L ⊆ missLines singerLines3 (insert p P) := by
  rcases rep P hc with rfl | ⟨p1, p2, p3, rfl⟩
  · rcases rep L hcL with rfl | ⟨l1, l2, l3, rfl⟩
    · exact ⟨0, by simp,
        fun l => (Finset.card_le_card Finset.inter_subset_left).trans (by simp),
        Finset.empty_subset _⟩
    · obtain ⟨p, a1, a2, a3⟩ := offPt l1 l2 l3
      refine ⟨p, by simp,
        fun l => (Finset.card_le_card Finset.inter_subset_left).trans (by simp), ?_⟩
      intro l hl
      rw [mem_miss]
      intro x hx
      have hx' : x = p := by simpa using hx
      rw [hx']
      simp only [Finset.mem_insert, Finset.mem_singleton] at hl
      rcases hl with h | h | h <;> rw [h]
      · exact a1
      · exact a2
      · exact a3
  · rcases rep L hcL with rfl | ⟨l1, l2, l3, rfl⟩
    · obtain ⟨l, a1, a2, a3⟩ := offLine p1 p2 p3
      have hyp : Hyp p1 p2 p3 l l l :=
        ⟨H1of hP, fun p h => h.1 rfl, ⟨a1, a2, a3⟩, ⟨a1, a2, a3⟩, ⟨a1, a2, a3⟩⟩
      obtain ⟨p, g⟩ := gen _ _ _ _ _ _ hyp
      exact ⟨p, finish hP (Finset.empty_subset _) hm g⟩
    · have m : ∀ l ∈ ({l1, l2, l3} : Finset (Fin 13)),
          ∀ x ∈ ({p1, p2, p3} : Finset (Fin 13)), I x l = false :=
        fun l hl => (mem_miss l _).mp (hm hl)
      have hyp : Hyp p1 p2 p3 l1 l2 l3 :=
        ⟨H1of hP, H2of hL,
          ⟨m l1 (by simp) p1 (by simp), m l1 (by simp) p2 (by simp), m l1 (by simp) p3 (by simp)⟩,
          ⟨m l2 (by simp) p1 (by simp), m l2 (by simp) p2 (by simp), m l2 (by simp) p3 (by simp)⟩,
          ⟨m l3 (by simp) p1 (by simp), m l3 (by simp) p2 (by simp), m l3 (by simp) p3 (by simp)⟩⟩
      obtain ⟨p, g⟩ := gen _ _ _ _ _ _ hyp
      exact ⟨p, finish hP (Finset.Subset.refl _) hm g⟩

theorem aux : ∀ (n : ℕ) (P L : Finset (Fin 13)), 4 - P.card = n → P.card ≤ 4 → L.card ≤ 3 →
    (∀ l : Fin 13, (P ∩ singerLines3 l).card ≤ 2) →
    (∀ p : Fin 13, (Finset.filter (fun l => p ∈ singerLines3 l) L).card ≤ 2) →
    L ⊆ missLines singerLines3 P →
    ∃ Q ∈ quadrangles singerLines3, P ⊆ Q ∧ L ⊆ missLines singerLines3 Q := by
  intro n
  induction n with
  | zero =>
    intro P L hn hc hcL hP hL hm
    refine ⟨P, ?_, Finset.Subset.refl _, hm⟩
    rw [quadrangles, Finset.mem_filter, Finset.mem_powersetCard]
    exact ⟨⟨Finset.subset_univ _, by omega⟩, hP⟩
  | succ n ih =>
    intro P L hn hc hcL hP hL hm
    obtain ⟨p, hp, hP', hm'⟩ := step P L (by omega) hcL hP hL hm
    have hcard : (insert p P).card = P.card + 1 := Finset.card_insert_of_notMem hp
    obtain ⟨Q, hQ, hsub, hmQ⟩ := ih (insert p P) L (by omega) (by omega) hcL hP' hL hm'
    exact ⟨Q, hQ, (Finset.subset_insert p P).trans hsub, hmQ⟩

end PEqualNP.Outside.L_meta_4867_aux

theorem PEqualNP.Outside.L_meta_4867 : ∀ (x1 x2 : Finset (Fin (13 : ℕ))), x1.card ≤ (4 : ℕ) → x2.card ≤ (3 : ℕ) → (∀ (x5 : Fin (13 : ℕ)), (x1 ∩ PEqualNP.HeptadCover.singerLines3 x5).card ≤ (2 : ℕ)) → (∀ (x6 : Fin (13 : ℕ)), {x7 ∈ x2 | x6 ∈ PEqualNP.HeptadCover.singerLines3 x7}.card ≤ (2 : ℕ)) → x2 ⊆ PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x1 → ∃ x8 ∈ PEqualNP.HeptadCover.quadrangles PEqualNP.HeptadCover.singerLines3, x1 ⊆ x8 ∧ x2 ⊆ PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x8 := by
  intro x1 x2 h1 h2 h3 h4 h5
  exact PEqualNP.Outside.L_meta_4867_aux.aux _ x1 x2 rfl h1 h2 h3 h4 h5
