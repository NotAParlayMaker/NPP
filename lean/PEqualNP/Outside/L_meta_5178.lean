import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.GenericRejection PEqualNP.ReadK PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_5178

def pts {n : ℕ} (S : Finset (Fin (n + n))) : Finset (Fin n) :=
  Finset.univ.filter fun p => Fin.castAdd n p ∈ S

def lns {n : ℕ} (S : Finset (Fin (n + n))) : Finset (Fin n) :=
  Finset.univ.filter fun l => Fin.natAdd n l ∈ S

theorem ofFn_setInput {n : ℕ} (S : Finset (Fin (n + n))) :
    List.ofFn (setInput S) = incidenceInput (pts S) (lns S) := by
  rw [List.ofFn_add]
  simp [incidenceInput, setInput, pts, lns]
  rfl

theorem count_eq {n : ℕ} (S : Finset (Fin (n + n))) :
    List.countP (fun l : Fin n => decide (Fin.natAdd n l ∈ S)) (List.finRange n) =
      (lns S).card := by
  rw [List.countP_eq_length_filter,
    ← List.toFinset_card_of_nodup ((List.nodup_finRange n).filter _)]
  congr 1
  ext z
  simp [lns]

theorem cast_ne_nat {n : ℕ} (p l : Fin n) : Fin.castAdd n p ≠ Fin.natAdd n l := by
  intro h
  have := congrArg Fin.val h
  simp at this
  omega

theorem pts_pair {n : ℕ} (p l : Fin n) :
    pts ({Fin.castAdd n p, Fin.natAdd n l} : Finset (Fin (n + n))) = {p} := by
  ext q
  simp only [pts, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro (h | h)
    · exact Fin.castAdd_injective _ _ h
    · exact absurd h (cast_ne_nat q l)
  · rintro rfl; exact Or.inl rfl

theorem lns_pair {n : ℕ} (p l : Fin n) :
    lns ({Fin.castAdd n p, Fin.natAdd n l} : Finset (Fin (n + n))) = {l} := by
  ext q
  simp only [lns, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro (h | h)
    · exact absurd h.symm (cast_ne_nat p q)
    · exact Fin.natAdd_injective _ _ h
  · rintro rfl; exact Or.inr rfl

end PEqualNP.Outside.L_meta_5178

theorem PEqualNP.Outside.L_meta_5178 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (1 : ℕ) ≤ x1 → PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 → (∀ (x7 x8 : Finset (Fin x2)), x8.card ≤ x1 → PEqualNP.GenericRejection.IsFalseInput x3 x7 x8 → x4.eval (PEqualNP.GenericRejection.incidenceInput x7 x8) = Bool.false) → ∀ (x8 : Finset (Fin (x2 + x2))), List.countP (fun (x9 : Fin x2) => Decidable.decide (Fin.natAdd x2 x9 ∈ x8)) (List.finRange x2) ≤ x1 → (PEqualNP.ReadK.IsPrimeImplicant (x2 + x2) x4 x8 ↔ ∃ (x10 : Fin x2) (x11 : Fin x2), x10 ∈ x3 x11 ∧ x8 = {Fin.castAdd x2 x10, Fin.natAdd x2 x11}) := by
  intro k n S C hk hright hfalse X hcnt
  open PEqualNP.Outside.L_meta_5178 in
  have hfun : ∀ T : Finset (Fin (n + n)),
      circuitFun (n + n) C (setInput T) = C.eval (incidenceInput (pts T) (lns T)) := by
    intro T
    simp only [circuitFun, ofFn_setInput]
  open PEqualNP.Outside.L_meta_5178 in
  have hpair : ∀ p l : Fin n, p ∈ S l →
      circuitFun (n + n) C (setInput {Fin.castAdd n p, Fin.natAdd n l}) = true := by
    intro p l h
    rw [hfun, pts_pair, lns_pair]
    exact hright l p h
  open PEqualNP.Outside.L_meta_5178 in
  have hcard : (lns X).card ≤ k := by rw [← count_eq]; exact hcnt
  constructor
  · rintro ⟨htrue, hmin⟩
    open PEqualNP.Outside.L_meta_5178 in
    have hnf : ¬ IsFalseInput S (pts X) (lns X) := by
      intro hf
      have := hfalse _ _ hcard hf
      rw [hfun] at htrue
      rw [this] at htrue
      exact Bool.false_ne_true htrue
    open PEqualNP.Outside.L_meta_5178 in
    obtain ⟨l, hl, hnd⟩ : ∃ l ∈ lns X, ¬ Disjoint (S l) (pts X) := by
      simpa [IsFalseInput] using hnf
    obtain ⟨p, hpS, hpX⟩ := Finset.not_disjoint_iff.mp hnd
    open PEqualNP.Outside.L_meta_5178 in
    simp only [pts, lns, Finset.mem_filter, Finset.mem_univ, true_and] at hl hpX
    refine ⟨p, l, hpS, ?_⟩
    by_contra hne
    have hsub : ({Fin.castAdd n p, Fin.natAdd n l} : Finset (Fin (n + n))) ⊂ X := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, fun h => hne h.symm⟩
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl <;> assumption
    have := hmin _ (Finset.mem_ssubsets.mpr hsub)
    rw [hpair p l hpS] at this
    simp at this
  · rintro ⟨p, l, hpS, rfl⟩
    refine ⟨hpair p l hpS, ?_⟩
    intro T hT
    have hTs := Finset.mem_ssubsets.mp hT
    open PEqualNP.Outside.L_meta_5178 in
    have hTl : lns T ⊆ {l} := by
      rw [← lns_pair p l]
      intro z hz
      simp only [lns, Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
      exact hTs.1 hz
    open PEqualNP.Outside.L_meta_5178 in
    have hTp : pts T ⊆ {p} := by
      rw [← pts_pair p l]
      intro z hz
      simp only [pts, Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
      exact hTs.1 hz
    open PEqualNP.Outside.L_meta_5178 in
    have hf : IsFalseInput S (pts T) (lns T) := by
      intro l' hl'
      have hl'e : l' = l := Finset.mem_singleton.mp (hTl hl')
      subst hl'e
      rw [Finset.disjoint_left]
      intro q _ hq
      have hqe : q = p := Finset.mem_singleton.mp (hTp hq)
      subst hqe
      apply hTs.2
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      simp only [pts, lns, Finset.mem_filter, Finset.mem_univ, true_and] at hl' hq
      rcases hz with rfl | rfl <;> assumption
    open PEqualNP.Outside.L_meta_5178 in
    have hc1 : (lns T).card ≤ k := le_trans (Finset.card_le_card hTl) (by simpa using hk)
    rw [hfun]
    exact hfalse _ _ hc1 hf
