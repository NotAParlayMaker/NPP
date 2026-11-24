import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1636

open PEqualNP.CircuitLowerBounds

-- The wire monotonicity argument follows L_meta_610.
private def wiresStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private lemma getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

private lemma getD_append_last_eq (w : List Bool) (b : Bool) (m : ℕ) (hm : w.length = m) :
    (w ++ [b]).getD m false = b := by
  subst hm
  simp [List.getD_eq_getElem?_getD]

private lemma getD_ofFn {m : ℕ} (x : Fin m → Bool) (i : ℕ) (hi : i < m) :
    (List.ofFn x).getD i false = x ⟨i, hi⟩ := by
  simp [List.getD_eq_getElem?_getD, hi]

private lemma monotone_foldl_wiresStep (gs : List Gate)
    (hM : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (w1 w2 : List Bool) (hlen : w1.length = w2.length)
    (hle : ∀ k : ℕ, w1.getD k false = true → w2.getD k false = true) :
    ∀ k : ℕ, (gs.foldl wiresStep w1).getD k false = true →
      (gs.foldl wiresStep w2).getD k false = true := by
  induction gs generalizing w1 w2 with
  | nil => exact hle
  | cons g gs ih =>
    have hg : g.op = GateOp.and ∨ g.op = GateOp.or := by
      simpa using hM g List.mem_cons_self
    have hM' : ∀ g' ∈ gs, g'.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) :=
      fun g' hg' => hM g' (List.mem_cons_of_mem g hg')
    apply ih hM' (wiresStep w1 g) (wiresStep w2 g)
    · simp only [wiresStep, List.length_append, List.length_cons, List.length_nil, hlen]
    · intro k hk
      by_cases hlt : k < w1.length
      · have hlt2 : k < w2.length := hlen ▸ hlt
        simp only [wiresStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt] at hk
        simp only [wiresStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt2]
        exact hle k hk
      · by_cases heq : k = w1.length
        · subst heq
          have hk1 : g.op.eval (g.inputs.map fun i => w1.getD i false) = true := by
            simpa [wiresStep, getD_append_last_eq w1 _ w1.length rfl] using hk
          rw [wiresStep, getD_append_last_eq w2 _ w1.length hlen.symm]
          rcases hg with hand | hor
          · rw [hand] at hk1 ⊢
            simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq,
              forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at hk1 ⊢
            intro i hi
            exact hle i (hk1 i hi)
          · rw [hor] at hk1 ⊢
            simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at hk1 ⊢
            obtain ⟨b, ⟨i, hi, rfl⟩, hbi⟩ := hk1
            exact ⟨true, ⟨i, hi, hle i hbi⟩, rfl⟩
        · have hge : (wiresStep w1 g).length ≤ k := by
            simp only [wiresStep, List.length_append, List.length_cons, List.length_nil]
            omega
          rw [getD_ge_length _ k hge] at hk
          cases hk

end PEqualNP.Outside.L_meta_1636

open PEqualNP.Outside.L_meta_1636

theorem PEqualNP.Outside.L_meta_1636 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N),
    3 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    p0 ≠ p1 → p0 ∈ L i0 → p1 ∈ L i0 →
    ∀ T : Fin N → Fin N → Fin N → Bool,
    (∀ (t p v : Fin N), T t p v = true ↔ (v = p ∨ (p0 ∉ L t ∧ p ≠ p1 ∧ v = p0) ∨ (p0 ∈ L t ∧ p1 ∉ L t ∧ p ≠ p0 ∧ v = p1) ∨
      (p0 ∈ L t ∧ p1 ∈ L t ∧ p ≠ p0 ∧ p ≠ p1 ∧ v ∉ L t))) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate),
    (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ gt.inputs.length ≤ 2) →
    (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length) →
    (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
    ∀ ev : ℕ → (Fin N → Bool) → Bool, (∀ (w : ℕ) (x : Fin N → Bool), ev w x = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w⟩ (List.ofFn x)) →
    ∀ w : ℕ,
    (∀ m l : Fin N, (p1 ∈ L m ∧ p0 ∉ L m) → (p0 ∈ L l ∧ p1 ∉ L l) → ev w (fun v : Fin N => decide (v ∉ L m)) = false → (∃ p ∈ L l, ev w (T l p) = true) →
      ∀ l' : Fin N, (p0 ∈ L l' ∧ p1 ∉ L l') → l' ≠ l → ev w (fun v : Fin N => decide (v ∉ L l')) = true) ∧
    (∀ l m : Fin N, (p0 ∈ L l ∧ p1 ∉ L l) → (p1 ∈ L m ∧ p0 ∉ L m) → ev w (fun v : Fin N => decide (v ∉ L l)) = false → (∃ p ∈ L m, ev w (T m p) = true) →
      ∀ m' : Fin N, (p1 ∈ L m' ∧ p0 ∉ L m') → m' ≠ m → ev w (fun v : Fin N => decide (v ∉ L m')) = true) ∧
    (∀ m M : Fin N, (p1 ∈ L m ∧ p0 ∉ L m) → ev w (fun v : Fin N => decide (v ∉ L m)) = false → (p0 ∉ L M ∧ p1 ∉ L M) → ((L M).filter (fun p => ev w (T M p) = true)).card ≤ 1) := by
  intro q N L i0 p0 p1 _ _ _ hmeet _ _ _ _ T hT gates hgate _ _ ev hev w
  have mono {x y : Fin N → Bool} (hxy : ∀ i, x i = true → y i = true)
      (hx : ev w x = true) : ev w y = true := by
    rw [hev] at hx ⊢
    apply monotone_foldl_wiresStep gates (fun g hg => by simpa using (hgate g hg).1)
      (List.ofFn x) (List.ofFn y) (by simp) _ w hx
    intro i hi
    by_cases hn : i < N
    · rw [getD_ofFn x i hn] at hi
      rw [getD_ofFn y i hn]
      exact hxy ⟨i, hn⟩ hi
    · simp [List.getD_eq_getElem?_getD, hn] at hi
  have unique {a b u v : Fin N} (hab : a ≠ b)
      (hua : u ∈ L a) (hub : u ∈ L b) (hva : v ∈ L a) (hvb : v ∈ L b) :
      u = v :=
    Finset.card_le_one.mp (by rw [hmeet a b hab]) u (Finset.mem_inter.mpr ⟨hua, hub⟩)
      v (Finset.mem_inter.mpr ⟨hva, hvb⟩)
  refine ⟨?_, ?_, ?_⟩
  · rintro m l ⟨hm1, hm0⟩ ⟨hl0, hl1⟩ hm ⟨p, hp, ht⟩ l' ⟨hl'0, hl'1⟩ hne
    have hp0 : p ≠ p0 := by
      intro heq
      subst p
      have hc : ev w (fun v => decide (v ∉ L m)) = true := mono (x := T l p0) (by
        intro v hv
        have h := (hT l p0 v).mp hv
        simp [hl0, hl1] at h
        simpa [h, hm0]) ht
      rw [hm] at hc
      cases hc
    have hp' : p ∉ L l' := fun h => hp0 (unique hne.symm hp h hl0 hl'0)
    apply mono (x := T l p) _ ht
    intro v hv
    have h := (hT l p v).mp hv
    simp [hl0, hl1, hp0] at h
    rcases h with rfl | rfl
    · simp [hp']
    · simp [hl'1]
  · rintro l m ⟨hl0, hl1⟩ ⟨hm1, hm0⟩ hl ⟨p, hp, ht⟩ m' ⟨hm'1, hm'0⟩ hne
    have hp1 : p ≠ p1 := by
      intro heq
      subst p
      have hc : ev w (fun v => decide (v ∉ L l)) = true := mono (x := T m p1) (by
        intro v hv
        have h := (hT m p1 v).mp hv
        simp [hm0, hm1] at h
        simpa [h, hl1]) ht
      rw [hl] at hc
      cases hc
    have hp' : p ∉ L m' := fun h => hp1 (unique hne.symm hp h hm1 hm'1)
    apply mono (x := T m p) _ ht
    intro v hv
    have h := (hT m p v).mp hv
    simp [hm0, hm1, hp1] at h
    rcases h with rfl | rfl
    · simp [hp']
    · simp [hm'0]
  · rintro m M ⟨hm1, hm0⟩ hm ⟨hM0, hM1⟩
    have hne : M ≠ m := fun h => hM1 (h.symm ▸ hm1)
    have hsub : (L M).filter (fun p => ev w (T M p) = true) ⊆ L M ∩ L m := by
      intro p hp
      obtain ⟨hpM, ht⟩ := Finset.mem_filter.mp hp
      refine Finset.mem_inter.mpr ⟨hpM, ?_⟩
      by_contra hp'
      have hp1 : p ≠ p1 := fun h => hM1 (h ▸ hpM)
      have hc : ev w (fun v => decide (v ∉ L m)) = true := mono (x := T M p) (by
        intro v hv
        have h := (hT M p v).mp hv
        simp [hM0, hM1, hp1] at h
        rcases h with rfl | rfl
        · simp [hp']
        · simp [hm0]) ht
      rw [hm] at hc
      cases hc
    simpa [hmeet M m hne] using Finset.card_le_card hsub
