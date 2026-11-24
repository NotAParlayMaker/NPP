import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4857

-- A closed sequence of m steps in the graph.
def OC {V : Type} (G : SimpleGraph V) (m : ℕ) : Prop :=
  ∃ c : ℕ → V, c m = c 0 ∧ ∀ i, i < m → G.Adj (c i) (c (i + 1))

-- Replace the stretch from position i to position j of a closed sequence by a bridge b of
-- r steps: both the short circuit through the bridge and the rest are closed sequences.
theorem detour {V : Type} {G : SimpleGraph V} (c : ℕ → V) (m i j r : ℕ) (b : ℕ → V)
    (hc0 : c m = c 0) (hc : ∀ k, k < m → G.Adj (c k) (c (k + 1))) (hij : i ≤ j) (hjm : j ≤ m)
    (hb0 : b 0 = c i) (hbr : b r = c j) (hb : ∀ t, t < r → G.Adj (b t) (b (t + 1))) :
    OC G ((j - i) + r) ∧ OC G (i + r + (m - j)) := by
  constructor
  · obtain ⟨s, s1, s2⟩ : ∃ s : ℕ → V, (∀ k, k < j - i → s k = c (i + k)) ∧
        (∀ k, ¬ k < j - i → s k = b (r - (k - (j - i)))) :=
      ⟨fun k => if k < j - i then c (i + k) else b (r - (k - (j - i))),
        fun k h => if_pos h, fun k h => if_neg h⟩
    refine ⟨s, ?_, ?_⟩
    · rw [s2 (j - i + r) (by omega), show r - (j - i + r - (j - i)) = 0 by omega, hb0]
      by_cases h : 0 < j - i
      · rw [s1 0 h]; rfl
      · rw [s2 0 h, show r - (0 - (j - i)) = r by omega, hbr]
        congr 1
        omega
    · intro k hk
      by_cases h1 : k + 1 < j - i
      · rw [s1 k (by omega), s1 (k + 1) h1]
        exact hc (i + k) (by omega)
      · by_cases h2 : k < j - i
        · rw [s1 k h2, s2 (k + 1) h1, show r - (k + 1 - (j - i)) = r by omega, hbr]
          have := hc (i + k) (by omega)
          rwa [show i + k + 1 = j by omega] at this
        · rw [s2 k h2, s2 (k + 1) h1]
          have := hb (r - (k + 1 - (j - i))) (by omega)
          rw [show r - (k + 1 - (j - i)) + 1 = r - (k - (j - i)) by omega] at this
          exact this.symm
  · obtain ⟨s, s1, s2, s3⟩ : ∃ s : ℕ → V, (∀ k, k < i → s k = c k) ∧
        (∀ k, i ≤ k → k < i + r → s k = b (k - i)) ∧
        (∀ k, i + r ≤ k → s k = c (j + (k - (i + r)))) :=
      ⟨fun k => if k < i then c k else if k < i + r then b (k - i) else c (j + (k - (i + r))),
        fun k h => if_pos h,
        fun k h1 h2 => by
          show (if k < i then c k else if k < i + r then b (k - i) else c (j + (k - (i + r)))) = _
          rw [if_neg (by omega), if_pos h2],
        fun k h => by
          show (if k < i then c k else if k < i + r then b (k - i) else c (j + (k - (i + r)))) = _
          rw [if_neg (by omega), if_neg (by omega)]⟩
    have hsir : s (i + r) = c j := by
      rw [s3 (i + r) (le_refl _), show j + (i + r - (i + r)) = j by omega]
    have hsi : s i = c i := by
      by_cases hr : 0 < r
      · rw [s2 i (le_refl _) (by omega), Nat.sub_self, hb0]
      · have hr0 : r = 0 := by omega
        subst hr0
        have h := hsir
        rw [Nat.add_zero] at h
        rw [h, ← hbr, hb0]
    refine ⟨s, ?_, ?_⟩
    · rw [s3 _ (by omega), show j + (i + r + (m - j) - (i + r)) = m by omega, hc0]
      by_cases hi : 0 < i
      · rw [s1 0 hi]
      · have hi0 : i = 0 := by omega
        subst hi0
        rw [hsi]
    · intro k hk
      by_cases h1 : k + 1 < i
      · rw [s1 k (by omega), s1 (k + 1) h1]
        exact hc k (by omega)
      · by_cases h2 : k < i
        · rw [s1 k h2, show k + 1 = i by omega, hsi]
          have := hc k (by omega)
          rwa [show k + 1 = i by omega] at this
        · by_cases h3 : k + 1 < i + r
          · rw [s2 k (by omega) (by omega), s2 (k + 1) (by omega) h3,
              show k + 1 - i = k - i + 1 by omega]
            exact hb (k - i) (by omega)
          · by_cases h4 : k < i + r
            · rw [s2 k (by omega) h4, show k + 1 = i + r by omega, hsir, ← hbr]
              have := hb (k - i) (by omega)
              rwa [show k - i + 1 = r by omega] at this
            · rw [s3 k (by omega), s3 (k + 1) (by omega),
                show j + (k + 1 - (i + r)) = j + (k - (i + r)) + 1 by omega]
              exact hc _ (by omega)

theorem cyc3 {V : Type} {G : SimpleGraph V} (h7 : (7 : ℕ∞) ≤ G.egirth) {a b c : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hca : G.Adj c a) : False := by
  have hw : (SimpleGraph.Walk.cons hab (SimpleGraph.Walk.cons hbc
      (SimpleGraph.Walk.cons hca SimpleGraph.Walk.nil))).IsCycle := by
    simp [SimpleGraph.Walk.cons_isCycle_iff, hab.ne, hbc.ne, hca.ne, hab.ne', hbc.ne', hca.ne']
  have h := SimpleGraph.le_egirth.mp h7 a _ hw
  have h' : (7 : ℕ) ≤ 3 := by exact_mod_cast h
  omega

theorem cyc4 {V : Type} {G : SimpleGraph V} (h7 : (7 : ℕ∞) ≤ G.egirth) {a b c d : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hda : G.Adj d a)
    (hac : a ≠ c) (hbd : b ≠ d) : False := by
  have hw : (SimpleGraph.Walk.cons hab (SimpleGraph.Walk.cons hbc
      (SimpleGraph.Walk.cons hcd (SimpleGraph.Walk.cons hda SimpleGraph.Walk.nil)))).IsCycle := by
    simp [SimpleGraph.Walk.cons_isCycle_iff, hab.ne, hbc.ne, hcd.ne, hda.ne, hab.ne', hbc.ne',
      hcd.ne', hda.ne', hac, hbd, hac.symm, hbd.symm]
  have h := SimpleGraph.le_egirth.mp h7 a _ hw
  have h' : (7 : ℕ) ≤ 4 := by exact_mod_cast h
  omega

theorem cyc5 {V : Type} {G : SimpleGraph V} (h7 : (7 : ℕ∞) ≤ G.egirth) {a b c d e : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hde : G.Adj d e) (hea : G.Adj e a)
    (hac : a ≠ c) (had : a ≠ d) (hbd : b ≠ d) (hbe : b ≠ e) (hce : c ≠ e) : False := by
  have hw : (SimpleGraph.Walk.cons hab (SimpleGraph.Walk.cons hbc
      (SimpleGraph.Walk.cons hcd (SimpleGraph.Walk.cons hde
        (SimpleGraph.Walk.cons hea SimpleGraph.Walk.nil))))).IsCycle := by
    simp [SimpleGraph.Walk.cons_isCycle_iff, hab.ne, hbc.ne, hcd.ne, hde.ne, hea.ne, hab.ne',
      hbc.ne', hcd.ne', hde.ne', hea.ne', hac, had, hbd, hbe, hce, hac.symm, had.symm, hbd.symm,
      hbe.symm, hce.symm]
  have h := SimpleGraph.le_egirth.mp h7 a _ hw
  have h' : (7 : ℕ) ≤ 5 := by exact_mod_cast h
  omega

theorem main (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (hnb : ¬ G.Colorable 2)
    (hdeg : ∀ v ∉ A, (G.neighborSet v).ncard = 3) (h7 : (7 : ℕ∞) ≤ G.egirth)
    (hA : ∀ u v : Fin n, G.Adj u v → u ∉ A) :
    ∃ m : ℕ, 7 ≤ m ∧ Odd m ∧ ∃ (f : Fin m ↪ Fin n) (g : Fin m ↪ Fin n),
      (∀ k : Fin m, G.Adj (f k) (g k) ∧ g k ∉ Set.range f) ∧
      ∀ k l : Fin m, G.Adj (f k) (f l) ↔
        (k.val + 1) % m = l.val ∨ (l.val + 1) % m = k.val := by
  classical
  have hex : ∃ m, Odd m ∧ OC G m := by
    by_contra hno
    apply hnb
    have hbip : G.IsBipartite := by
      rw [SimpleGraph.isBipartite_iff_forall_walk_even_length]
      intro v p
      by_contra hev
      apply hno
      refine ⟨p.length, Nat.not_even_iff_odd.mp hev, fun k => p.getVert k, ?_, ?_⟩
      · simp
      · intro i hi
        exact p.adj_getVert_succ hi
    exact hbip
  obtain ⟨m, ⟨hodd, c, hc0, hc⟩, hmin'⟩ : ∃ m, (Odd m ∧ OC G m) ∧
      ∀ k, k < m → ¬ (Odd k ∧ OC G k) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun k hk => Nat.find_min hex hk⟩
  have hmin : ∀ k, k < m → Odd k → ¬ OC G k := fun k hk ho hoc => hmin' k hk ⟨ho, hoc⟩
  -- the sequence does not repeat a vertex
  have inj : ∀ i j, i < j → j < m → c i ≠ c j := by
    intro i j hij hjm heq
    obtain ⟨h1, h2⟩ := detour c m i j 0 (fun _ => c i) hc0 hc hij.le hjm.le rfl heq
      (by intro t ht; omega)
    rcases Nat.even_or_odd (j - i) with he | ho
    · exact hmin _ (by omega)
        (by rw [Nat.odd_iff] at hodd ⊢; rw [Nat.even_iff] at he; omega) h2
    · exact hmin _ (by omega) (by rw [Nat.odd_iff] at ho ⊢; omega) h1
  -- it has no chord
  have chord : ∀ i j, i < j → j < m → G.Adj (c i) (c j) → j = i + 1 ∨ (i = 0 ∧ j + 1 = m) := by
    intro i j hij hjm hadj
    by_contra hcon
    obtain ⟨h1, h2⟩ := detour c m i j 1 (fun t => if t = 0 then c i else c j) hc0 hc hij.le
      hjm.le (by simp) (by simp)
      (by
        intro t ht
        have ht0 : t = 0 := by omega
        subst ht0
        simpa using hadj)
    have hji : 2 ≤ j - i ∧ j - i + 2 ≤ m := by omega
    rcases Nat.even_or_odd (j - i) with he | ho
    · exact hmin _ (by omega) (by rw [Nat.odd_iff]; rw [Nat.even_iff] at he; omega) h1
    · exact hmin _ (by omega) (by rw [Nat.odd_iff] at hodd ho ⊢; omega) h2
  have hm7 : 7 ≤ m := by
    by_contra hlt
    have hm : m = 1 ∨ m = 3 ∨ m = 5 := by rw [Nat.odd_iff] at hodd; omega
    rcases hm with rfl | rfl | rfl
    · exact (hc 0 (by omega)).ne hc0.symm
    · have a01 := hc 0 (by omega)
      have a12 := hc 1 (by omega)
      have a20 := hc 2 (by omega)
      rw [show (2 : ℕ) + 1 = 3 from rfl, hc0] at a20
      exact cyc3 h7 a01 a12 a20
    · have a01 := hc 0 (by omega)
      have a12 := hc 1 (by omega)
      have a23 := hc 2 (by omega)
      have a34 := hc 3 (by omega)
      have a40 := hc 4 (by omega)
      rw [show (4 : ℕ) + 1 = 5 from rfl, hc0] at a40
      exact cyc5 h7 a01 a12 a23 a34 a40 (inj 0 2 (by omega) (by omega))
        (inj 0 3 (by omega) (by omega)) (inj 1 3 (by omega) (by omega))
        (inj 1 4 (by omega) (by omega)) (inj 2 4 (by omega) (by omega))
  have hcA : ∀ k, k < m → c k ∉ A := fun k hk => hA _ _ (hc k hk)
  have adjcl : ∀ k l, k < m → l < m → G.Adj (c k) (c l) →
      c l = c ((k + m - 1) % m) ∨ c l = c (k + 1) := by
    intro k l hk hl hadj
    have hkl : k ≠ l := fun e => hadj.ne (by rw [e])
    rcases Nat.lt_or_gt_of_ne hkl with h | h
    · rcases chord k l h hl hadj with e | ⟨e1, e2⟩
      · right; rw [e]
      · left
        subst e1
        congr 1
        rw [Nat.mod_eq_of_lt (by omega)]
        omega
    · rcases chord l k h hk hadj.symm with e | ⟨e1, e2⟩
      · left
        congr 1
        rw [show k + m - 1 = l + m by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hl]
      · right
        subst e1
        rw [e2, hc0]
  have ex : ∀ k, ∃ d, k < m → (G.Adj (c k) d ∧ ∀ l, l < m → d ≠ c l) := by
    intro k
    by_cases hk : k < m
    · have h3 := hdeg (c k) (hcA k hk)
      have hlt : ({c ((k + m - 1) % m), c (k + 1)} : Set (Fin n)).ncard <
          (G.neighborSet (c k)).ncard := by
        rw [h3]
        have h2 : ({c ((k + m - 1) % m), c (k + 1)} : Set (Fin n)).ncard ≤
            ({c (k + 1)} : Set (Fin n)).ncard + 1 := Set.ncard_insert_le _ _
        rw [Set.ncard_singleton] at h2
        omega
      obtain ⟨d, hd, hnd⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard hlt (Set.toFinite _)
      refine ⟨d, fun _ => ⟨hd, fun l hl e => ?_⟩⟩
      subst e
      rcases adjcl k l hk hl hd with h | h
      · exact hnd (by simp [h])
      · exact hnd (by simp [h])
    · exact ⟨c 0, fun h => absurd h hk⟩
  choose d hd using ex
  -- the outside neighbours are pairwise different
  have dinj : ∀ i j, i < j → j < m → d i ≠ d j := by
    intro i j hij hjm heq
    have hi := hd i (by omega)
    have hj := hd j hjm
    have hdj : G.Adj (d i) (c j) := by rw [heq]; exact hj.1.symm
    obtain ⟨h1, h2⟩ := detour c m i j 2
      (fun t => if t = 0 then c i else if t = 1 then d i else c j) hc0 hc hij.le hjm.le
      (by simp) (by simp)
      (by
        intro t ht
        have ht01 : t = 0 ∨ t = 1 := by omega
        rcases ht01 with rfl | rfl
        · simpa using hi.1
        · simpa using hdj)
    rcases Nat.even_or_odd (j - i) with he | ho
    · by_cases hlt : i + 2 + (m - j) < m
      · exact hmin _ hlt
          (by rw [Nat.odd_iff] at hodd ⊢; rw [Nat.even_iff] at he; omega) h2
      · have hji : j = i + 2 := by rw [Nat.even_iff] at he; omega
        subst hji
        exact cyc4 h7 (hc i (by omega)) (hc (i + 1) (by omega)) hdj.symm hi.1.symm
          (inj i (i + 2) (by omega) hjm) (fun e => hi.2 (i + 1) (by omega) e.symm)
    · by_cases hlt : j - i + 2 < m
      · exact hmin _ hlt (by rw [Nat.odd_iff] at ho ⊢; omega) h1
      · have hcase : (i = 0 ∧ j + 2 = m) ∨ (i = 1 ∧ j + 1 = m) := by
          rw [Nat.odd_iff] at ho hodd
          omega
        rcases hcase with ⟨rfl, hj2⟩ | ⟨rfl, hj1⟩
        · have a1 := hc j (by omega)
          have a2 := hc (j + 1) (by omega)
          rw [show j + 1 + 1 = m by omega, hc0] at a2
          exact cyc4 h7 hi.1 hdj a1 a2 (inj 0 j hij hjm) (fun e => hi.2 (j + 1) (by omega) e)
        · have a1 := hc j (by omega)
          rw [show j + 1 = m by omega, hc0] at a1
          have a2 := hc 0 (by omega)
          exact cyc4 h7 hi.1 hdj a1 a2 (inj 1 j hij hjm) (fun e => hi.2 0 (by omega) e)
  refine ⟨m, hm7, hodd, ⟨fun k => c k.val, ?_⟩, ⟨fun k => d k.val, ?_⟩, ?_, ?_⟩
  · intro k l h
    apply Fin.ext
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h' | h'
    · exact inj _ _ h' l.isLt h
    · exact inj _ _ h' k.isLt h.symm
  · intro k l h
    apply Fin.ext
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h' | h'
    · exact dinj _ _ h' l.isLt h
    · exact dinj _ _ h' k.isLt h.symm
  · intro k
    refine ⟨(hd k.val k.isLt).1, ?_⟩
    rintro ⟨l, hl⟩
    exact (hd k.val k.isLt).2 l.val l.isLt hl.symm
  · intro k l
    constructor
    · intro hadj
      change G.Adj (c k.val) (c l.val) at hadj
      have hkl : k.val ≠ l.val := fun e => hadj.ne (by rw [e])
      have hk := k.isLt
      have hl := l.isLt
      rcases Nat.lt_or_gt_of_ne hkl with h | h
      · rcases chord _ _ h l.isLt hadj with e | ⟨e1, e2⟩
        · left
          rw [Nat.mod_eq_of_lt (by omega)]
          omega
        · right
          rw [e2, Nat.mod_self]
          omega
      · rcases chord _ _ h k.isLt hadj.symm with e | ⟨e1, e2⟩
        · right
          rw [Nat.mod_eq_of_lt (by omega)]
          omega
        · left
          rw [e2, Nat.mod_self]
          omega
    · have key : ∀ a b : ℕ, a < m → (a + 1) % m = b → G.Adj (c a) (c b) := by
        intro a b ha h
        by_cases hlt : a + 1 < m
        · rw [Nat.mod_eq_of_lt hlt] at h
          rw [← h]
          exact hc a ha
        · have hm : a + 1 = m := by omega
          rw [hm, Nat.mod_self] at h
          rw [← h, ← hc0, ← hm]
          exact hc a ha
      rintro (h | h)
      · exact key _ _ k.isLt h
      · exact (key _ _ l.isLt h).symm

end PEqualNP.Outside.L_meta_4857

theorem PEqualNP.Outside.L_meta_4857 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)), ¬x2.Colorable (2 : ℕ) → (∀ x5 ∉ x3, (x2.neighborSet x5).ncard = (3 : ℕ)) → (7 : ℕ∞) ≤ x2.egirth → (∀ (x7 x8 : Fin x1), x2.Adj x7 x8 → x7 ∉ x3) → ∃ (x8 : ℕ), (7 : ℕ) ≤ x8 ∧ Odd x8 ∧ ∃ (x9 : Fin x8 ↪ Fin x1) (x10 : Fin x8 ↪ Fin x1), (∀ (x11 : Fin x8), x2.Adj (x9 x11) (x10 x11) ∧ x10 x11 ∉ Set.range ⇑x9) ∧ ∀ (x11 x12 : Fin x8), x2.Adj (x9 x11) (x9 x12) ↔ (↑x11 + (1 : ℕ)) % x8 = ↑x12 ∨ (↑x12 + (1 : ℕ)) % x8 = ↑x11 := by
  intro n G A hnb hdeg h7 hA
  exact PEqualNP.Outside.L_meta_4857.main n G A hnb hdeg h7 hA
