import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1645

open PEqualNP.CircuitLowerBounds

theorem wires_snoc (gs : List Gate) (g : Gate) (o o2 : ℕ) (l : List Bool) :
    Circuit.wires ⟨gs ++ [g], o⟩ l = Circuit.wires ⟨gs, o2⟩ l ++
      [g.op.eval (g.inputs.map fun i => (Circuit.wires ⟨gs, o2⟩ l).getD i false)] := by
  simp [Circuit.wires, List.foldl_append]

theorem wires_length (gs : List Gate) (o : ℕ) (l : List Bool) :
    (Circuit.wires ⟨gs, o⟩ l).length = l.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [Circuit.wires]
  | append_singleton gs g ih =>
    rw [wires_snoc gs g o o, List.length_append, ih]
    simp
    omega

theorem foldl_prefix (r : List Gate) : ∀ l : List Bool,
    l <+: r.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) l := by
  induction r with
  | nil => intro l; simp
  | cons g r ih =>
    intro l
    rw [List.foldl_cons]
    exact (List.prefix_append l _).trans (ih _)

theorem wires_prefix (gs r : List Gate) (o o2 : ℕ) (l : List Bool) :
    Circuit.wires ⟨gs, o⟩ l <+: Circuit.wires ⟨gs ++ r, o2⟩ l := by
  simp only [Circuit.wires, List.foldl_append]
  exact foldl_prefix r _

theorem getD_prefix (l1 l2 : List Bool) (h : l1 <+: l2) (i : ℕ) (hi : i < l1.length) :
    l2.getD i false = l1.getD i false := by
  obtain ⟨t, rfl⟩ := h
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem eval_prefix (gs r : List Gate) (o : ℕ) (l : List Bool) (i : ℕ)
    (hi : i < l.length + gs.length) :
    Circuit.eval ⟨gs ++ r, i⟩ l = (Circuit.wires ⟨gs, o⟩ l).getD i false := by
  unfold Circuit.eval
  exact getD_prefix _ _ (wires_prefix gs r o i l) i (by rw [wires_length]; exact hi)

theorem all_mono (f1 f2 : ℕ → Bool) (h : ∀ i, f1 i = true → f2 i = true) (l : List ℕ)
    (h1 : (l.map f1).all id = true) : (l.map f2).all id = true := by
  simp only [List.all_eq_true, List.mem_map] at *
  rintro b ⟨a, ha, rfl⟩
  exact h a (h1 _ ⟨a, ha, rfl⟩)

theorem any_mono (f1 f2 : ℕ → Bool) (h : ∀ i, f1 i = true → f2 i = true) (l : List ℕ)
    (h1 : (l.map f1).any id = true) : (l.map f2).any id = true := by
  simp only [List.any_eq_true, List.mem_map] at *
  obtain ⟨b, ⟨a, ha, rfl⟩, hb⟩ := h1
  exact ⟨_, ⟨a, ha, rfl⟩, h a hb⟩

-- Monotonicity on the inputs vanishing on T, for the prefixes of at most B gates,
-- given that every NOT gate among the first B gates is true at all such inputs.
theorem mono (n : ℕ) (T : Finset (Fin n)) (gates : List Gate) (B : ℕ)
    (hops : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (htrue : ∀ i : Fin gates.length, (i : ℕ) < B → (gates.get i).op = GateOp.not →
      ∀ x : Fin n → Bool, (∀ v ∈ T, x v = false) →
      Circuit.eval ⟨gates, n + (i : ℕ)⟩ (List.ofFn x) = true) :
    ∀ (gs rest : List Gate), gates = gs ++ rest → gs.length ≤ B →
    ∀ (w : ℕ) (x y : Fin n → Bool), (∀ v ∈ T, y v = false) → (∀ v : Fin n, x v = true → y v = true) →
      (Circuit.wires ⟨gs, 0⟩ (List.ofFn x)).getD w false = true →
      (Circuit.wires ⟨gs, 0⟩ (List.ofFn y)).getD w false = true := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil =>
    intro rest _ _ w x y hy hxy h
    simp only [Circuit.wires, List.foldl_nil] at h ⊢
    by_cases hw : w < n
    · simp [List.getD_eq_getElem?_getD, hw] at h ⊢
      exact hxy _ h
    · simp [List.getD_eq_getElem?_getD, hw] at h
  | append_singleton gs g ih =>
    intro rest hg hB w x y hy hxy h
    have hB' : gs.length < B := by
      simp only [List.length_append, List.length_singleton] at hB
      omega
    have ih' := ih (g :: rest) (by simp [hg]) (le_of_lt hB')
    have hlen : ∀ z : Fin n → Bool,
        (Circuit.wires ⟨gs, 0⟩ (List.ofFn z)).length = n + gs.length := by
      intro z
      rw [wires_length]
      simp
    rcases lt_trichotomy w (n + gs.length) with hw | hw | hw
    · rw [wires_snoc gs g 0 0] at h ⊢
      rw [List.getD_append _ _ _ _ (by rw [hlen]; exact hw)] at h ⊢
      exact ih' w x y hy hxy h
    · have hgm : g ∈ gates := by rw [hg]; simp
      have hval : ∀ z : Fin n → Bool,
          (Circuit.wires ⟨gs ++ [g], 0⟩ (List.ofFn z)).getD w false =
          g.op.eval (g.inputs.map fun i => (Circuit.wires ⟨gs, 0⟩ (List.ofFn z)).getD i false) := by
        intro z
        rw [wires_snoc gs g 0 0, List.getD_append_right _ _ _ _ (by rw [hlen]; omega), hlen, hw]
        simp
      rcases (hops g hgm).1 with ho | ho | ho
      · rw [hval, ho] at h ⊢
        exact all_mono _ _ (fun i hi => ih' i x y hy hxy hi) _ h
      · rw [hval, ho] at h ⊢
        exact any_mono _ _ (fun i hi => ih' i x y hy hxy hi) _ h
      · have hget : gates[gs.length]? = some g := by rw [hg]; simp
        obtain ⟨hl, hh⟩ := List.getElem?_eq_some_iff.mp hget
        have ht := htrue ⟨gs.length, hl⟩ hB' (by simp [hh, ho]) y hy
        have he := eval_prefix (gs ++ [g]) rest 0 (List.ofFn y) w (by simp; omega)
        rw [← hg, hw] at he
        rw [hw, ← he]
        exact ht
    · rw [wires_snoc gs g 0 0] at h
      rw [List.getD_append_right _ _ _ _ (by rw [hlen]; omega), hlen] at h
      have : w - (n + gs.length) ≠ 0 := by omega
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero this
      rw [hk] at h
      simp at h

theorem gate_val (gs rest : List Gate) (g : Gate) (n : ℕ) (l : List Bool) (hl : l.length = n) :
    Circuit.eval ⟨gs ++ g :: rest, n + gs.length⟩ l =
      g.op.eval (g.inputs.map fun i => (Circuit.wires ⟨gs, 0⟩ l).getD i false) := by
  have he := eval_prefix (gs ++ [g]) rest 0 l (n + gs.length) (by simp; omega)
  rw [List.append_assoc, List.singleton_append] at he
  rw [he, wires_snoc gs g 0 0,
    List.getD_append_right _ _ _ _ (by rw [wires_length]; omega), wires_length, hl]
  simp

end PEqualNP.Outside.L_meta_1645

theorem PEqualNP.Outside.L_meta_1645 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N),
    2 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    p0 ≠ p1 → p0 ∈ L i0 → p1 ∈ L i0 →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin N → ℕ) (j h : Fin gates.length),
    (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ gt.inputs.length ≤ 2) →
    (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
    (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) →
    h < j → (∃ r : List ℕ, (gates.get j).inputs = (N + (h : ℕ)) :: r) →
    (∀ (t : Fin N) (x : Fin N → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
    ∀ ev : ℕ → (Fin N → Bool) → Bool, (∀ (w : ℕ) (x : Fin N → Bool), ev w x = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w⟩ (List.ofFn x)) →
    ev (N + (h : ℕ)) (fun v : Fin N => decide (v = p0)) = true → ev (N + (h : ℕ)) (fun v : Fin N => decide (v = p1)) = true → (∀ p : Fin N, p ≠ p0 → p ≠ p1 → ev (N + (h : ℕ)) (fun v : Fin N => decide (v = p)) = false) →
    ev (N + (h : ℕ)) (fun v : Fin N => decide (v ∉ L i0)) = false →
    (∀ x : Fin N → Bool, (∀ v : Fin N, x v = true → v ∉ L i0) → ev (N + (h : ℕ)) x = false ∧ ev (N + (j : ℕ)) x = true) ∧
    (∀ w ∈ L i0, w ≠ p0 → w ≠ p1 → ev (N + (h : ℕ)) (fun v : Fin N => decide (v = w)) = false ∧ ev (N + (j : ℕ)) (fun v : Fin N => decide (v = w)) = true) ∧
    ev (N + (j : ℕ)) (fun v : Fin N => decide (v = p0)) = false ∧ ev (N + (j : ℕ)) (fun v : Fin N => decide (v = p1)) = false ∧
    ∀ (w : ℕ) (x y : Fin N → Bool), (∀ v : Fin N, x v = true → v ∉ L i0) → (∀ v : Fin N, y v = true → v ∉ L i0) → (∀ v : Fin N, x v = true → y v = true) → ev w x = true → ev w y = true := by
  intro q N L i0 p0 p1 hq hNq hcard hint hjoin hp01 hp0 hp1 gates o j h hops hback hjop hnot hhj hinp hout ev hev h0 h1 hoth hW
  have hhj' : (h : ℕ) < (j : ℕ) := hhj
  have hsplit : gates = gates.take (j : ℕ) ++ gates.get j :: gates.drop ((j : ℕ) + 1) := by
    simp
  have hlen : (gates.take (j : ℕ)).length = (j : ℕ) := by
    simp
  -- the NOT gate reads gate h
  have K1 : ∀ x : Fin N → Bool, ev (N + (j : ℕ)) x = !(ev (N + (h : ℕ)) x) := by
    intro x
    rw [hev, hev]
    have hv := PEqualNP.Outside.L_meta_1645.gate_val (gates.take (j : ℕ)) (gates.drop ((j : ℕ) + 1))
      (gates.get j) N (List.ofFn x) (by simp)
    have hea := PEqualNP.Outside.L_meta_1645.eval_prefix (gates.take (j : ℕ))
      (gates.get j :: gates.drop ((j : ℕ) + 1)) 0 (List.ofFn x) (N + (h : ℕ))
      (by rw [hlen, List.length_ofFn]; exact Nat.add_lt_add_left hhj' N)
    rw [← hsplit] at hv hea
    rw [hlen] at hv
    obtain ⟨r, hr⟩ := hinp
    rw [hv, hjop, hr, hea]
    simp [PEqualNP.CircuitLowerBounds.GateOp.eval]
  -- the gates before the NOT gate are monotone below the complement of the line
  have Mpre := PEqualNP.Outside.L_meta_1645.mono N (L i0) gates (j : ℕ) hops (by
      intro i hi hop
      exfalso
      have hij := congrArg Fin.val (hnot i hop)
      omega)
    (gates.take (j : ℕ)) (gates.drop (j : ℕ)) (by simp) (le_of_eq hlen)
  have hea : ∀ z : Fin N → Bool,
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (h : ℕ)⟩ (List.ofFn z) =
        (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates.take (j : ℕ), 0⟩ (List.ofFn z)).getD (N + (h : ℕ)) false := by
    intro z
    have he := PEqualNP.Outside.L_meta_1645.eval_prefix (gates.take (j : ℕ)) (gates.drop (j : ℕ)) 0
      (List.ofFn z) (N + (h : ℕ))
      (by rw [hlen, List.length_ofFn]; exact Nat.add_lt_add_left hhj' N)
    rw [List.take_append_drop] at he
    exact he
  have K2 : ∀ x : Fin N → Bool, (∀ v : Fin N, x v = true → v ∉ L i0) → ev (N + (h : ℕ)) x = false := by
    intro x hx
    by_contra hc
    have hc' : ev (N + (h : ℕ)) x = true := by simpa using hc
    rw [hev, hea] at hc'
    have hm := Mpre (N + (h : ℕ)) x (fun v : Fin N => decide (v ∉ L i0))
      (by intro v hv; simp [hv]) (by intro v hv; simpa using hx v hv) hc'
    have hW' := hW
    rw [hev, hea] at hW'
    rw [hW'] at hm
    cases hm
  have htrue : ∀ i : Fin gates.length, (i : ℕ) < gates.length →
      (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not →
      ∀ x : Fin N → Bool, (∀ v ∈ L i0, x v = false) →
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (i : ℕ)⟩ (List.ofFn x) = true := by
    intro i _ hop x hx
    rw [hnot i hop, ← hev]
    have hk := K2 x (fun v hv hmem => by rw [hx v hmem] at hv; cases hv)
    simp only [K1, hk, Bool.not_false]
  have Mfull := PEqualNP.Outside.L_meta_1645.mono N (L i0) gates gates.length hops htrue
    gates [] (by simp) le_rfl
  refine ⟨fun x hx => ⟨K2 x hx, by simp only [K1, K2 x hx, Bool.not_false]⟩,
    fun w hw hw0 hw1 => ⟨hoth w hw0 hw1, by simp only [K1, hoth w hw0 hw1, Bool.not_false]⟩,
    by simp only [K1, h0, Bool.not_true], by simp only [K1, h1, Bool.not_true], ?_⟩
  intro w x y hx hy hxy hw
  rw [hev] at hw ⊢
  exact Mfull w x y (fun v hv => by
    by_contra hc
    exact hy v (by simpa using hc) hv) hxy hw
