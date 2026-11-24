import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1636

open PEqualNP.CircuitLowerBounds

-- one gate appended to the list of wire values
def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem getD_snoc (W : List Bool) (v : Bool) (i : ℕ) :
    (W ++ [v]).getD i false = if i = W.length then v else W.getD i false := by
  rcases lt_trichotomy i W.length with h | h | h
  · rw [if_neg (by omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · subst h
    simp [List.getD_eq_getElem?_getD]
  · rw [if_neg (by omega)]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

theorem ev_and (g : Gate) (f : ℕ → Bool) (h : g.op = GateOp.and) :
    (g.op.eval (g.inputs.map f) = true ↔ ∀ i ∈ g.inputs, f i = true) := by
  rw [h]
  simp [GateOp.eval]

theorem ev_or (g : Gate) (f : ℕ → Bool) (h : g.op = GateOp.or) :
    (g.op.eval (g.inputs.map f) = true ↔ ∃ i ∈ g.inputs, f i = true) := by
  rw [h]
  simp [GateOp.eval]

-- AND and OR gates are monotone: a wire true on the smaller run is true on the larger
theorem mono : ∀ (gs : List Gate) (W1 W2 : List Bool), W1.length = W2.length →
    (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
    (∀ i, W1.getD i false = true → W2.getD i false = true) →
    ∀ i, (gs.foldl stp W1).getD i false = true → (gs.foldl stp W2).getD i false = true := by
  intro gs
  induction gs with
  | nil => intro W1 W2 _ _ H; simpa using H
  | cons g gs ih =>
    intro W1 W2 hl hop H
    rw [List.foldl_cons, List.foldl_cons]
    apply ih (stp W1 g) (stp W2 g) (by simp [stp, hl])
      (fun g' hg' => hop g' (List.mem_cons_of_mem _ hg'))
    intro i
    simp only [stp, getD_snoc, hl]
    split_ifs
    · rcases hop g List.mem_cons_self with ha | ho
      · rw [ev_and g _ ha, ev_and g _ ha]
        intro h k hk
        exact H k (h k hk)
      · rw [ev_or g _ ho, ev_or g _ ho]
        rintro ⟨k, hk, h⟩
        exact ⟨k, hk, H k h⟩
    · exact H i

-- the value of any wire of an AND/OR list is monotone in the input
theorem evmono (N : ℕ) (gates : List Gate)
    (hop : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or) (w : ℕ)
    (x y : Fin N → Bool) (H : ∀ v, x v = true → y v = true)
    (h : Circuit.eval ⟨gates, w⟩ (List.ofFn x) = true) :
    Circuit.eval ⟨gates, w⟩ (List.ofFn y) = true := by
  have h' : (gates.foldl stp (List.ofFn x)).getD w false = true := h
  show (gates.foldl stp (List.ofFn y)).getD w false = true
  refine mono gates (List.ofFn x) (List.ofFn y) (by simp) hop ?_ w h'
  intro i hi
  by_cases hN : i < N
  · have h1 : i < (List.ofFn x).length := by simpa using hN
    have h2 : i < (List.ofFn y).length := by simpa using hN
    rw [List.getD_eq_getElem _ _ h1] at hi
    rw [List.getD_eq_getElem _ _ h2]
    simp only [List.getElem_ofFn] at hi ⊢
    exact H _ hi
  · have h1 : (List.ofFn x).length ≤ i := by simp; omega
    rw [List.getD_eq_default _ _ h1] at hi
    exact absurd hi (by simp)

-- two distinct lines share exactly one point
theorem uniq {N : ℕ} (L : Fin N → Finset (Fin N))
    (hc : ∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) (i j : Fin N) (hij : i ≠ j)
    (a b : Fin N) (ha : a ∈ L i) (ha' : a ∈ L j) (hb : b ∈ L i) (hb' : b ∈ L j) : a = b := by
  obtain ⟨c, hcc⟩ := Finset.card_eq_one.mp (hc i j hij)
  have h1 : a ∈ L i ∩ L j := Finset.mem_inter.mpr ⟨ha, ha'⟩
  have h2 : b ∈ L i ∩ L j := Finset.mem_inter.mpr ⟨hb, hb'⟩
  rw [hcc, Finset.mem_singleton] at h1 h2
  rw [h1, h2]

end PEqualNP.Outside.L_meta_1636

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
  intro q N L i0 p0 p1 _ _ _ hc _ _ _ _ T hT gates hg _ _ ev hev w
  have hop : ∀ g ∈ gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      g.op = PEqualNP.CircuitLowerBounds.GateOp.or := fun g hgm => (hg g hgm).1
  have mono' : ∀ (x y : Fin N → Bool), (∀ v, x v = true → y v = true) →
      ev w x = true → ev w y = true := by
    intro x y H h
    rw [hev] at h ⊢
    exact PEqualNP.Outside.L_meta_1636.evmono N gates hop w x y H h
  refine ⟨?_, ?_, ?_⟩
  · intro m l hm hl hfalse hex l' hl' hne
    obtain ⟨hm1, hm0⟩ := hm
    obtain ⟨hl0, hl1⟩ := hl
    obtain ⟨hl'0, hl'1⟩ := hl'
    obtain ⟨p, hp, hTp⟩ := hex
    by_cases hpp : p = p0
    · exfalso
      have hbad : ev w (fun v : Fin N => decide (v ∉ L m)) = true := by
        apply mono' (T l p) _ _ hTp
        intro v hv
        have hv' := (hT l p v).mp hv
        apply decide_eq_true
        rcases hv' with h | h | h | h
        · rw [h, hpp]; exact hm0
        · exact absurd hl0 h.1
        · exact absurd hpp h.2.2.1
        · exact absurd h.2.1 hl1
      rw [hfalse] at hbad
      exact absurd hbad (by simp)
    · apply mono' (T l p) _ _ hTp
      intro v hv
      have hv' := (hT l p v).mp hv
      apply decide_eq_true
      rcases hv' with h | h | h | h
      · rw [h]
        intro hpl'
        exact hpp (PEqualNP.Outside.L_meta_1636.uniq L hc l l' (Ne.symm hne) p p0 hp hpl' hl0 hl'0)
      · exact absurd hl0 h.1
      · rw [h.2.2.2]; exact hl'1
      · exact absurd h.2.1 hl1
  · intro l m hl hm hfalse hex m' hm' hne
    obtain ⟨hm1, hm0⟩ := hm
    obtain ⟨hl0, hl1⟩ := hl
    obtain ⟨hm'1, hm'0⟩ := hm'
    obtain ⟨p, hp, hTp⟩ := hex
    by_cases hpp : p = p1
    · exfalso
      have hbad : ev w (fun v : Fin N => decide (v ∉ L l)) = true := by
        apply mono' (T m p) _ _ hTp
        intro v hv
        have hv' := (hT m p v).mp hv
        apply decide_eq_true
        rcases hv' with h | h | h | h
        · rw [h, hpp]; exact hl1
        · exact absurd hpp h.2.1
        · exact absurd h.1 hm0
        · exact absurd h.1 hm0
      rw [hfalse] at hbad
      exact absurd hbad (by simp)
    · apply mono' (T m p) _ _ hTp
      intro v hv
      have hv' := (hT m p v).mp hv
      apply decide_eq_true
      rcases hv' with h | h | h | h
      · rw [h]
        intro hpm'
        exact hpp (PEqualNP.Outside.L_meta_1636.uniq L hc m m' (Ne.symm hne) p p1 hp hpm' hm1 hm'1)
      · rw [h.2.2]; exact hm'0
      · exact absurd h.1 hm0
      · exact absurd h.1 hm0
  · intro m M hm hfalse hM
    obtain ⟨hm1, hm0⟩ := hm
    obtain ⟨hM0, hM1⟩ := hM
    have hMm : M ≠ m := by
      intro h
      rw [h] at hM1
      exact hM1 hm1
    have hsub : (L M).filter (fun p => ev w (T M p) = true) ⊆ L M ∩ L m := by
      intro p hp
      rw [Finset.mem_filter] at hp
      rw [Finset.mem_inter]
      refine ⟨hp.1, ?_⟩
      by_contra hpm
      have hbad : ev w (fun v : Fin N => decide (v ∉ L m)) = true := by
        apply mono' (T M p) _ _ hp.2
        intro v hv
        have hv' := (hT M p v).mp hv
        apply decide_eq_true
        rcases hv' with h | h | h | h
        · rw [h]; exact hpm
        · rw [h.2.2]; exact hm0
        · exact absurd h.1 hM0
        · exact absurd h.1 hM0
      rw [hfalse] at hbad
      exact absurd hbad (by simp)
    calc ((L M).filter (fun p => ev w (T M p) = true)).card ≤ (L M ∩ L m).card :=
          Finset.card_le_card hsub
      _ = 1 := hc M m hMm
