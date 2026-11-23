import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.Meta159

private abbrev bow : SimpleGraph (Fin 5) :=
  SimpleGraph.fromRel (fun a b : Fin 5 =>
    (a = 0 ∧ b = 1) ∨ (a = 0 ∧ b = 2) ∨ (a = 1 ∧ b = 2) ∨
    (a = 0 ∧ b = 3) ∨ (a = 0 ∧ b = 4) ∨ (a = 3 ∧ b = 4))

private abbrev independent (I : Finset (Fin 5)) : Prop :=
  ∀ u ∈ I, ∀ v ∈ I, ¬ bow.Adj u v

private def fiber {k : ℕ} (t : Fin k → Fin 5) (v : Fin 5) : Finset (Fin k) :=
  Finset.univ.filter (fun i => t i = v)

private def Rules {k : ℕ} (A : Fin k → Finset (Sym2 (Fin 5)))
    (B : Fin k → Finset (Finset (Fin 5))) (t : Fin k → Fin 5) : Prop :=
  (∀ i, ∀ e ∈ A i, t i ∈ e) ∧
  (∀ i, ∀ I ∈ B i, t i ∉ I) ∧
  (∀ u v, bow.Adj u v → ∀ I, independent I →
    ∃! i, s(u, v) ∈ A i ∧ I ∈ B i)

variable {k : ℕ} {A : Fin k → Finset (Sym2 (Fin 5))}
  {B : Fin k → Finset (Finset (Fin 5))} {t : Fin k → Fin 5}

private lemma singleton_independent (v : Fin 5) : independent {v} := by
  intro u hu w hw
  simp only [Finset.mem_singleton] at hu hw
  subst u
  subst w
  exact bow.irrefl

private lemma label_forced (h : Rules A B t) {i : Fin k} {u v : Fin 5}
    {I : Finset (Fin 5)} (he : s(u, v) ∈ A i) (hI : I ∈ B i)
    (hv : v ∈ I) : t i = u := by
  have hm := h.1 i _ he
  have hn := h.2.1 i I hI
  have hp : t i = u ∨ t i = v := by simpa using hm
  rcases hp with hp | hp
  · exact hp
  · exact False.elim (hn (hp ▸ hv))

private lemma single_eq {v : Fin 5} (hc : (fiber t v).card ≤ 1)
    {i j : Fin k} (hi : t i = v) (hj : t j = v) : i = j := by
  exact Finset.card_le_one.mp hc i (by simp [fiber, hi]) j (by simp [fiber, hj])

private lemma small_full (h : Rules A B t) {v u : Fin 5}
    (hc : (fiber t v).card ≤ 1) {i : Fin k} (hi : t i = v)
    (hu : bow.Adj v u) : s(v, u) ∈ A i := by
  obtain ⟨j, hj, _⟩ := h.2.2 v u hu {u} (singleton_independent u)
  have ht : t j = v := label_forced h hj.1 hj.2 (by simp)
  exact (single_eq hc hi ht) ▸ hj.1

private lemma unique_cell (h : Rules A B t) {u v : Fin 5}
    (he : bow.Adj u v) {I : Finset (Fin 5)} (hI : independent I)
    {i j : Fin k} (hi : s(u, v) ∈ A i ∧ I ∈ B i)
    (hj : s(u, v) ∈ A j ∧ I ∈ B j) : i = j := by
  obtain ⟨z, _, hz⟩ := h.2.2 u v he I hI
  exact (hz i hi).trans (hz j hj).symm

private lemma positive (h : Rules A B t) (v : Fin 5) : 1 ≤ (fiber t v).card := by
  have hn : ∀ v : Fin 5, ∃ u : Fin 5, bow.Adj v u := by decide
  obtain ⟨u, hu⟩ := hn v
  obtain ⟨i, hi, _⟩ := h.2.2 v u hu {u} (singleton_independent u)
  have ht := label_forced h hi.1 hi.2 (by simp)
  have : (fiber t v).Nonempty := ⟨i, by simp [fiber, ht]⟩
  exact Finset.card_pos.mpr this

private lemma adjacent_count (h : Rules A B t) {u v : Fin 5}
    (huv : bow.Adj u v) : 3 ≤ (fiber t u).card + (fiber t v).card := by
  have hposu := positive h u
  have hposv := positive h v
  by_contra hc
  have hcu : (fiber t u).card ≤ 1 := by omega
  have hcv : (fiber t v).card ≤ 1 := by omega
  have common : ∀ u v : Fin 5, bow.Adj u v →
      ∃ w : Fin 5, bow.Adj u w ∧ bow.Adj v w := by
    intro a b
    fin_cases a <;> fin_cases b <;> decide
  obtain ⟨w, huw, hvw⟩ := common u v huv
  obtain ⟨i, hi, _⟩ := h.2.2 u w huw {w} (singleton_independent w)
  obtain ⟨j, hj, _⟩ := h.2.2 v w hvw {w} (singleton_independent w)
  have hti : t i = u := label_forced h hi.1 hi.2 (by simp)
  have htj : t j = v := label_forced h hj.1 hj.2 (by simp)
  have hei := small_full h hcu hti huv
  have hej : s(u, v) ∈ A j := by
    simpa [Sym2.eq_swap] using small_full h hcv htj huv.symm
  have hij := unique_cell h huv (singleton_independent w) ⟨hei, hi.2⟩ ⟨hej, hj.2⟩
  have : u = v := hti.symm.trans ((congrArg t hij).trans htj)
  exact huv.ne this

private lemma small_excludes (h : Rules A B t) {v w : Fin 5}
    (hc : (fiber t v).card ≤ 1) (h0v : bow.Adj 0 v)
    (hvw : bow.Adj v w) (hne : (0 : Fin 5) ≠ v)
    {I : Finset (Fin 5)} (hI : independent I) (hw : w ∈ I)
    {i : Fin k} (hiB : I ∈ B i) (hti : t i = 0) : s(0, v) ∉ A i := by
  obtain ⟨j, hj, _⟩ := h.2.2 v w hvw I hI
  have htj : t j = v := label_forced h hj.1 hj.2 hw
  have hej : s(0, v) ∈ A j := by
    simpa [Sym2.eq_swap] using small_full h hc htj h0v.symm
  intro hei
  have hij := unique_cell h h0v hI ⟨hei, hiB⟩ ⟨hej, hj.2⟩
  exact hne (hti.symm.trans ((congrArg t hij).trans htj))

private lemma center_three (h : Rules A B t) (a a' b b' : Fin 5)
    (h0a : bow.Adj 0 a) (h0b : bow.Adj 0 b) (h0a' : bow.Adj 0 a')
    (haa' : bow.Adj a a') (hbb' : bow.Adj b b')
    (ha0 : (0 : Fin 5) ≠ a) (hb0 : (0 : Fin 5) ≠ b)
    (hI1 : independent {a, b'}) (hI2 : independent {a', b})
    (hI3 : independent {a', b'})
    (hca : (fiber t a).card ≤ 1) (hcb : (fiber t b).card ≤ 1) :
    3 ≤ (fiber t 0).card := by
  obtain ⟨i, hi, _⟩ := h.2.2 0 a h0a {a, b'} hI1
  obtain ⟨j, hj, _⟩ := h.2.2 0 b h0b {a', b} hI2
  obtain ⟨l, hl, _⟩ := h.2.2 0 a' h0a' {a', b'} hI3
  have hti : t i = 0 := label_forced h hi.1 hi.2 (by simp)
  have htj : t j = 0 := label_forced h hj.1 hj.2 (by simp)
  have htl : t l = 0 := label_forced h hl.1 hl.2 (by simp)
  have hjno : s(0, a) ∉ A j :=
    small_excludes h hca h0a haa' ha0 hI2 (by simp) hj.2 htj
  have hlnoa : s(0, a) ∉ A l :=
    small_excludes h hca h0a haa' ha0 hI3 (by simp) hl.2 htl
  have hlnob : s(0, b) ∉ A l :=
    small_excludes h hcb h0b hbb' hb0 hI3 (by simp) hl.2 htl
  have hij : i ≠ j := fun heq => hjno (heq ▸ hi.1)
  have hil : i ≠ l := fun heq => hlnoa (heq ▸ hi.1)
  have hjl : j ≠ l := fun heq => hlnob (heq ▸ hj.1)
  have hsub : ({i, j, l} : Finset (Fin k)) ⊆ fiber t 0 := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl <;> simp [fiber, hti, htj, htl]
  calc
    3 = ({i, j, l} : Finset (Fin k)).card := by simp [hij, hil, hjl]
    _ ≤ (fiber t 0).card := Finset.card_le_card hsub

private lemma lower_bound (h : Rules A B t) : 9 ≤ k := by
  have total : ∑ v : Fin 5, (fiber t v).card = k := by
    have he := Finset.card_eq_sum_card_fiberwise
      (f := t) (s := Finset.univ) (t := Finset.univ) (by simp)
    simpa [fiber] using he.symm
  have sum5 : (fiber t 0).card + (fiber t 1).card + (fiber t 2).card +
      (fiber t 3).card + (fiber t 4).card = k := by
    simpa [Fin.sum_univ_succ, add_assoc] using total
  have p0 := positive h 0
  have p1 := positive h 1
  have p2 := positive h 2
  have p3 := positive h 3
  have p4 := positive h 4
  have p01 := adjacent_count h (show bow.Adj 0 1 by decide)
  have p02 := adjacent_count h (show bow.Adj 0 2 by decide)
  have p03 := adjacent_count h (show bow.Adj 0 3 by decide)
  have p04 := adjacent_count h (show bow.Adj 0 4 by decide)
  have p12 := adjacent_count h (show bow.Adj 1 2 by decide)
  have p34 := adjacent_count h (show bow.Adj 3 4 by decide)
  by_contra hk
  have small1 : (fiber t 1).card ≤ 1 ∨ (fiber t 2).card ≤ 1 := by omega
  have small2 : (fiber t 3).card ≤ 1 ∨ (fiber t 4).card ≤ 1 := by omega
  have pcenter : 3 ≤ (fiber t 0).card := by
    rcases small1 with h1 | h2 <;> rcases small2 with h3 | h4
    · exact center_three h 1 2 3 4 (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) h1 h3
    · exact center_three h 1 2 4 3 (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) h1 h4
    · exact center_three h 2 1 3 4 (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) h2 h3
    · exact center_three h 2 1 4 3 (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) h2 h4
  omega

end PEqualNP.Outside.Meta159

theorem PEqualNP.Outside.L_meta_159 : ∀ (k : ℕ) (A : Fin k → Finset (Sym2 (Fin 5))) (B : Fin k → Finset (Finset (Fin 5)))
    (t : Fin k → Fin 5),
    (∀ i, ∀ e ∈ A i, e ∈ (SimpleGraph.fromRel (fun a b : Fin 5 =>
        (a = 0 ∧ b = 1) ∨ (a = 0 ∧ b = 2) ∨ (a = 1 ∧ b = 2) ∨
        (a = 0 ∧ b = 3) ∨ (a = 0 ∧ b = 4) ∨ (a = 3 ∧ b = 4))).edgeFinset ∧ t i ∈ e) →
    (∀ i, ∀ I ∈ B i, t i ∉ I) →
    (∀ e ∈ (SimpleGraph.fromRel (fun a b : Fin 5 =>
        (a = 0 ∧ b = 1) ∨ (a = 0 ∧ b = 2) ∨ (a = 1 ∧ b = 2) ∨
        (a = 0 ∧ b = 3) ∨ (a = 0 ∧ b = 4) ∨ (a = 3 ∧ b = 4))).edgeFinset,
      ∀ I : Finset (Fin 5), (∀ u ∈ I, ∀ w ∈ I, ¬ (SimpleGraph.fromRel (fun a b : Fin 5 =>
        (a = 0 ∧ b = 1) ∨ (a = 0 ∧ b = 2) ∨ (a = 1 ∧ b = 2) ∨
        (a = 0 ∧ b = 3) ∨ (a = 0 ∧ b = 4) ∨ (a = 3 ∧ b = 4))).Adj u w) →
        ∃! i : Fin k, e ∈ A i ∧ I ∈ B i) →
    9 ≤ k := by
  intro k A B t hA hB hCover
  apply PEqualNP.Outside.Meta159.lower_bound (A := A) (B := B) (t := t)
  refine ⟨?_, hB, ?_⟩
  · intro i e he
    exact (hA i e he).2
  · intro u v huv I hI
    exact hCover s(u, v) (SimpleGraph.mem_edgeFinset.mpr huv) I hI
