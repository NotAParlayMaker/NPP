import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_5827_1
    (hA : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (u v : Fin 18),
      PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 17 →
      let P : (Fin 10 → Bool) → Bool := fun z =>
        ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)] : List (Fin 10 × Fin 10)).any fun e => z e.1 && z e.2
      let W : (Fin 10 → Bool) → ℕ → Bool := fun z i => (C.wires (List.ofFn z ++ [z 0 || z 1])).getD i false
      (∃ z, W z (10 + u) = true ∧ W z (10 + v) = false) →
      (∃ z, W z (10 + u) = false ∧ W z (10 + v) = true) →
      (∀ z, P z = false → W z (10 + u) = false ∧ W z (10 + v) = false) →
      ∃ z, P z = true ∧ W z (10 + u) = false ∧ W z (10 + v) = false)
    (hB : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (u v : Fin 18),
      PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 17 →
      let P : (Fin 10 → Bool) → Bool := fun z =>
        ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)] : List (Fin 10 × Fin 10)).any fun e => z e.1 && z e.2
      let W : (Fin 10 → Bool) → ℕ → Bool := fun z i => (C.wires (List.ofFn z ++ [z 0 || z 2])).getD i false
      (∃ z, W z (10 + u) = true ∧ W z (10 + v) = false) →
      (∃ z, W z (10 + u) = false ∧ W z (10 + v) = true) →
      (∀ z, P z = false → W z (10 + u) = false ∧ W z (10 + v) = false) →
      ∃ z, P z = true ∧ W z (10 + u) = false ∧ W z (10 + v) = false)
    (hC : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (u v : Fin 18),
      PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 17 →
      let P : (Fin 10 → Bool) → Bool := fun z =>
        ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)] : List (Fin 10 × Fin 10)).any fun e => z e.1 && z e.2
      let W : (Fin 10 → Bool) → ℕ → Bool := fun z i => (C.wires (List.ofFn z ++ [z 0])).getD i false
      (∃ z, W z (10 + u) = true ∧ W z (10 + v) = false) →
      (∃ z, W z (10 + u) = false ∧ W z (10 + v) = true) →
      (∀ z, P z = false → W z (10 + u) = false ∧ W z (10 + v) = false) →
      ∃ z, P z = true ∧ W z (10 + u) = false ∧ W z (10 + v) = false) :
    (∀ (x1 x2 : Fin (11 : ℕ)) (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : Fin (18 : ℕ)),   PEqualNP.MetaComplexity.FanInTwo x3 →     x3.size ≤ (17 : ℕ) →       have x8 : PEqualNP.CircuitLowerBounds.Gate := { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [↑x1, ↑x2] : PEqualNP.CircuitLowerBounds.Gate };       have x9 : (Fin (10 : ℕ) → Bool) → Bool := fun (x9 : Fin (10 : ℕ) → Bool) => x9 (0 : Fin (10 : ℕ)) && x9 (1 : Fin (10 : ℕ)) || x9 (1 : Fin (10 : ℕ)) && x9 (2 : Fin (10 : ℕ)) || x9 (2 : Fin (10 : ℕ)) && x9 (3 : Fin (10 : ℕ)) || x9 (3 : Fin (10 : ℕ)) && x9 (4 : Fin (10 : ℕ)) || x9 (4 : Fin (10 : ℕ)) && x9 (0 : Fin (10 : ℕ)) || x9 (0 : Fin (10 : ℕ)) && x9 (5 : Fin (10 : ℕ)) || x9 (1 : Fin (10 : ℕ)) && x9 (6 : Fin (10 : ℕ)) || x9 (2 : Fin (10 : ℕ)) && x9 (7 : Fin (10 : ℕ)) || x9 (3 : Fin (10 : ℕ)) && x9 (8 : Fin (10 : ℕ)) || x9 (4 : Fin (10 : ℕ)) && x9 (9 : Fin (10 : ℕ)) || x9 (5 : Fin (10 : ℕ)) && x9 (7 : Fin (10 : ℕ)) || x9 (7 : Fin (10 : ℕ)) && x9 (9 : Fin (10 : ℕ)) || x9 (9 : Fin (10 : ℕ)) && x9 (6 : Fin (10 : ℕ)) || x9 (6 : Fin (10 : ℕ)) && x9 (8 : Fin (10 : ℕ)) || x9 (8 : Fin (10 : ℕ)) && x9 (5 : Fin (10 : ℕ));       have x10 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x10 : Fin (10 : ℕ) → Bool) (x11 : ℕ) => (x3.wires ({ gates := [x8], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x10))).getD x11 Bool.false;       (∃ (x11 : Fin (10 : ℕ) → Bool), x10 x11 ((10 : ℕ) + ↑x4) = Bool.true ∧ x10 x11 ((10 : ℕ) + ↑x5) = Bool.false) → (∃ (x12 : Fin (10 : ℕ) → Bool), x10 x12 ((10 : ℕ) + ↑x4) = Bool.false ∧ x10 x12 ((10 : ℕ) + ↑x5) = Bool.true) → (∀ (x13 : Fin (10 : ℕ) → Bool), x9 x13 = Bool.false → x10 x13 ((10 : ℕ) + ↑x4) = Bool.false ∧ x10 x13 ((10 : ℕ) + ↑x5) = Bool.false) → ∃ (x14 : Fin (10 : ℕ) → Bool), x9 x14 = Bool.true ∧ x10 x14 ((10 : ℕ) + ↑x4) = Bool.false ∧ x10 x14 ((10 : ℕ) + ↑x5) = Bool.false) := by
  intro a b C u v hfan hsize
  let E : List (Fin 10 × Fin 10) := [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)]
  let P : (Fin 10 → Bool) → Bool := fun z => E.any fun e => z e.1 && z e.2
  let f : (Fin 10 → Bool) → Bool := fun (x9 : Fin (10 : ℕ) → Bool) => x9 (0 : Fin (10 : ℕ)) && x9 (1 : Fin (10 : ℕ)) || x9 (1 : Fin (10 : ℕ)) && x9 (2 : Fin (10 : ℕ)) || x9 (2 : Fin (10 : ℕ)) && x9 (3 : Fin (10 : ℕ)) || x9 (3 : Fin (10 : ℕ)) && x9 (4 : Fin (10 : ℕ)) || x9 (4 : Fin (10 : ℕ)) && x9 (0 : Fin (10 : ℕ)) || x9 (0 : Fin (10 : ℕ)) && x9 (5 : Fin (10 : ℕ)) || x9 (1 : Fin (10 : ℕ)) && x9 (6 : Fin (10 : ℕ)) || x9 (2 : Fin (10 : ℕ)) && x9 (7 : Fin (10 : ℕ)) || x9 (3 : Fin (10 : ℕ)) && x9 (8 : Fin (10 : ℕ)) || x9 (4 : Fin (10 : ℕ)) && x9 (9 : Fin (10 : ℕ)) || x9 (5 : Fin (10 : ℕ)) && x9 (7 : Fin (10 : ℕ)) || x9 (7 : Fin (10 : ℕ)) && x9 (9 : Fin (10 : ℕ)) || x9 (9 : Fin (10 : ℕ)) && x9 (6 : Fin (10 : ℕ)) || x9 (6 : Fin (10 : ℕ)) && x9 (8 : Fin (10 : ℕ)) || x9 (8 : Fin (10 : ℕ)) && x9 (5 : Fin (10 : ℕ))
  have hPf : ∀ z, f z = P z := by
    intro z
    simp only [f, P, E, List.any_cons, List.any_nil, Bool.or_false, Bool.or_assoc]
  let Q : ((Fin 10 → Bool) → Bool) → ((Fin 10 → Bool) → ℕ → Bool) → ℕ → ℕ → Prop :=
    fun F W p q => (∃ z, W z p = true ∧ W z q = false) → (∃ z, W z p = false ∧ W z q = true) →
      (∀ z, F z = false → W z p = false ∧ W z q = false) →
      ∃ z, F z = true ∧ W z p = false ∧ W z q = false
  let W0 : (Fin 10 → Bool) → ℕ → Bool := fun z i =>
    (C.wires ((⟨[⟨GateOp.or, [a.val, b.val]⟩], 0⟩ : Circuit).wires (List.ofFn z))).getD i false
  change Q f W0 (10 + u.val) (10 + v.val)
  have hQ : ∀ W p q, Q P W p q → Q f W p q := by
    intro W p q h h1 h2 h3
    obtain ⟨z, hz, hz'⟩ := h h1 h2 (fun z hz => h3 z (by rw [hPf]; exact hz))
    exact ⟨z, by rw [hPf]; exact hz, hz'⟩
  have transport : ∀ (σ : Fin 10 → Fin 10) (W W' : (Fin 10 → Bool) → ℕ → Bool) (p q : ℕ),
      Function.Injective σ → (∀ z, P (z ∘ σ) = P z) →
      (∀ z i, (i = p ∨ i = q) → W' z i = W (z ∘ σ) i) → Q P W' p q → Q P W p q := by
    intro σ W W' p q hinj haut hW hq h1 h2 h3
    let e := Equiv.ofBijective σ (Finite.injective_iff_bijective.mp hinj)
    have hback : ∀ z : Fin 10 → Bool, (z ∘ e.symm) ∘ σ = z := by
      intro z
      funext k
      simp only [Function.comp]
      congr 1
      exact e.symm_apply_apply k
    have h1' : ∃ z, W' z p = true ∧ W' z q = false := by
      obtain ⟨z, hz1, hz2⟩ := h1
      refine ⟨z ∘ e.symm, ?_, ?_⟩
      · rw [hW _ _ (Or.inl rfl), hback]; exact hz1
      · rw [hW _ _ (Or.inr rfl), hback]; exact hz2
    have h2' : ∃ z, W' z p = false ∧ W' z q = true := by
      obtain ⟨z, hz1, hz2⟩ := h2
      refine ⟨z ∘ e.symm, ?_, ?_⟩
      · rw [hW _ _ (Or.inl rfl), hback]; exact hz1
      · rw [hW _ _ (Or.inr rfl), hback]; exact hz2
    have h3' : ∀ z, P z = false → W' z p = false ∧ W' z q = false := by
      intro z hz
      rw [hW _ _ (Or.inl rfl), hW _ _ (Or.inr rfl)]
      apply h3
      rw [haut]
      exact hz
    obtain ⟨z, hz, hzp, hzq⟩ := hq h1' h2' h3'
    refine ⟨z ∘ σ, ?_, ?_, ?_⟩
    · rw [haut]; exact hz
    · rw [← hW _ _ (Or.inl rfl)]; exact hzp
    · rw [← hW _ _ (Or.inr rfl)]; exact hzq
  have getD_snoc : ∀ (w : List Bool) (c : Bool) (i : ℕ),
      (w ++ [c]).getD i false = (w.getD i false || (c && decide (w.length = i))) := by
    intro w c i
    rcases lt_trichotomy i w.length with h | h | h
    · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h, h.ne']
    · subst h
      simp [List.getD_eq_getElem?_getD]
    · obtain ⟨d, rfl⟩ : ∃ d, i = w.length + (d + 1) := ⟨i - w.length - 1, by omega⟩
      simp [List.getD_eq_getElem?_getD]
  have getD_ofFn : ∀ (y : Fin 10 → Bool) (i : ℕ),
      (List.ofFn y).getD i false = if h : i < 10 then y ⟨i, h⟩ else false := by
    intro y i
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    by_cases h : i < 10 <;> simp [h]
  have FL : ∀ (ρ : ℕ → ℕ) (gs : List Gate) (xs ys : List Bool), xs.length = ys.length →
      11 ≤ xs.length → (∀ i, 11 ≤ i → ρ i = i) →
      (∀ i, i < 11 → ρ i < 11 ∨ xs.length + gs.length ≤ ρ i) →
      (∀ i, ys.getD (ρ i) false = xs.getD i false) →
      ∀ i, ((gs.map fun g => (⟨g.op, g.inputs.map ρ⟩ : Gate)).foldl
          (fun w g => w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]) ys).getD (ρ i) false =
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]) xs).getD i
          false := by
    intro ρ gs
    induction gs with
    | nil => intro xs ys _ _ _ _ h i; exact h i
    | cons g gs ih =>
      intro xs ys hl h11 hid hsm h
      simp only [List.map_cons, List.foldl_cons]
      have hval : g.op.eval ((g.inputs.map ρ).map fun j => ys.getD j false) =
          g.op.eval (g.inputs.map fun j => xs.getD j false) := by
        rw [List.map_map]
        congr 1
        apply List.map_congr_left
        intro j _
        exact h j
      apply ih
      · simp [hl]
      · simp only [List.length_append, List.length_singleton]; omega
      · exact hid
      · intro i hi
        rcases hsm i hi with h1 | h1
        · left; exact h1
        · right; simp only [List.length_append, List.length_singleton, List.length_cons,
            List.length_nil] at h1 ⊢
          omega
      · intro i
        rw [getD_snoc, getD_snoc, hval, h i]
        by_cases hi : 11 ≤ i
        · rw [hid i hi, hl]
        · have hne1 : ¬ (ys.length = ρ i) := by
            rcases hsm i (by omega) with h1 | h1
            · omega
            · simp only [List.length_cons] at h1; omega
          have hne2 : ¬ (xs.length = i) := by omega
          simp only [hne1, hne2, decide_false]
  have relab : ∀ ρ : ℕ → ℕ,
      FanInTwo (⟨C.gates.map fun g => (⟨g.op, g.inputs.map ρ⟩ : Gate), C.output⟩ : Circuit) ∧
      (⟨C.gates.map fun g => (⟨g.op, g.inputs.map ρ⟩ : Gate), C.output⟩ : Circuit).size ≤ 17 := by
    intro ρ
    constructor
    · intro g hg
      obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
      have := hfan g0 hg0
      exact ⟨this.1, by simpa using this.2⟩
    · simpa [Circuit.size] using hsize
  have autP : ∀ σ : Fin 10 → Fin 10, (∀ e ∈ E, (σ e.1, σ e.2) ∈ E ∨ (σ e.2, σ e.1) ∈ E) →
      (∀ e ∈ E, ∃ e' ∈ E, (σ e'.1, σ e'.2) = e ∨ (σ e'.2, σ e'.1) = e) →
      ∀ z, P (z ∘ σ) = P z := by
    intro σ h1 h2 z
    apply Bool.eq_iff_iff.mpr
    simp only [P, List.any_eq_true, Bool.and_eq_true, Function.comp]
    constructor
    · rintro ⟨e, he, h1z, h2z⟩
      rcases h1 e he with h | h
      · exact ⟨_, h, h1z, h2z⟩
      · exact ⟨_, h, h2z, h1z⟩
    · rintro ⟨e, he, h1z, h2z⟩
      obtain ⟨e', he', h | h⟩ := h2 e he
      · subst h; exact ⟨e', he', h1z, h2z⟩
      · subst h; exact ⟨e', he', h2z, h1z⟩
  have finish : ∀ (σ : Fin 10 → Fin 10) (r10 : ℕ) (val : (Fin 10 → Bool) → Bool) (p q : ℕ),
      Function.Injective σ → (∀ z, P (z ∘ σ) = P z) → (r10 = 10 ∨ 11 + C.size ≤ r10) →
      (p = 10 → r10 = 10) → (q = 10 → r10 = 10) → 10 ≤ p → 10 ≤ q →
      (∀ z, (List.ofFn z ++ [val z]).getD r10 false =
        (List.ofFn (z ∘ σ) ++ [GateOp.or.eval ([a.val, b.val].map fun i =>
          (List.ofFn (z ∘ σ)).getD i false)]).getD 10 false) →
      Q P (fun z i => ((⟨C.gates.map fun g => (⟨g.op, g.inputs.map (fun i =>
          if h : i < 10 then (σ ⟨i, h⟩).val else if i = 10 then r10 else i)⟩ : Gate),
          C.output⟩ : Circuit).wires (List.ofFn z ++ [val z])).getD i false) p q →
      Q f W0 p q := by
    intro σ r10 val p q hinj haut hr10 hp10 hq10 hp hq hten hQ'
    apply hQ
    let ρ : ℕ → ℕ := fun i => if h : i < 10 then (σ ⟨i, h⟩).val else if i = 10 then r10 else i
    refine transport σ W0 (fun z i => ((⟨C.gates.map fun g => (⟨g.op, g.inputs.map ρ⟩ : Gate),
      C.output⟩ : Circuit).wires (List.ofFn z ++ [val z])).getD i false) p q hinj haut ?_ hQ'
    intro z i hi
    have hρi : ρ i = i := by
      have hi10 : 10 ≤ i := by rcases hi with rfl | rfl <;> assumption
      have hr : i = 10 → r10 = 10 := by rcases hi with rfl | rfl <;> assumption
      by_cases h10 : i = 10
      · subst h10
        simp only [ρ]
        rw [hr rfl]
        simp
      · simp only [ρ]
        rw [dif_neg (by omega), if_neg h10]
    let xs := List.ofFn (z ∘ σ) ++ [GateOp.or.eval ([a.val, b.val].map fun i =>
          (List.ofFn (z ∘ σ)).getD i false)]
    let ys := List.ofFn z ++ [val z]
    have hlx : xs.length = 11 := by simp [xs]
    have hly : ys.length = 11 := by simp [ys]
    have key := FL ρ C.gates xs ys (by rw [hlx, hly]) (by rw [hlx])
      (by
        intro j hj
        simp only [ρ]
        rw [dif_neg (by omega), if_neg (by omega)])
      (by
        intro j hj
        rw [hlx]
        by_cases hj10 : j < 10
        · left; simp only [ρ, dif_pos hj10]; omega
        · have : j = 10 := by omega
          subst this
          simp only [ρ]
          rcases hr10 with h | h
          · left; simp; omega
          · right; simp only [Circuit.size] at h; simp; omega)
      (by
        intro j
        rcases lt_trichotomy j 10 with hj | rfl | hj
        · have hs := (σ ⟨j, hj⟩).isLt
          have hρj : ρ j = (σ ⟨j, hj⟩).val := by simp only [ρ, dif_pos hj]
          rw [hρj]
          simp only [ys, xs]
          rw [getD_snoc, getD_snoc, getD_ofFn, getD_ofFn, dif_pos hs, dif_pos hj]
          simp only [List.length_ofFn, Function.comp,
            decide_eq_false (show (10:ℕ) ≠ (σ ⟨j, hj⟩).val by omega),
            decide_eq_false (show (10:ℕ) ≠ j by omega), Bool.and_false, Bool.or_false]
        · have hρ10 : ρ 10 = r10 := by simp [ρ]
          rw [hρ10]
          exact hten z
        · simp only [ρ]
          rw [dif_neg (by omega), if_neg (by omega)]
          simp only [ys, xs]
          rw [getD_snoc, getD_snoc, getD_ofFn, getD_ofFn]
          rw [dif_neg (by omega), dif_neg (by omega)]
          simp [show (10:ℕ) ≠ j by omega])
      i
    rw [hρi] at key
    exact key
  obtain ⟨sg, hinj, hfwd, hbwd, hpos⟩ : ∃ sg : Fin 11 → Fin 11 → Fin 10 → Fin 10,
      (∀ a b : Fin 11, ∀ i j : Fin 10, sg a b i = sg a b j → i = j) ∧
      (∀ a b : Fin 11, ∀ e ∈ E, (sg a b e.1, sg a b e.2) ∈ E ∨ (sg a b e.2, sg a b e.1) ∈ E) ∧
      (∀ a b : Fin 11, ∀ e ∈ E, ∃ e' ∈ E, (sg a b e'.1, sg a b e'.2) = e ∨
        (sg a b e'.2, sg a b e'.1) = e) ∧
      (∀ a b : Fin 11, ∀ k : Fin 10, (k.val = a.val → (sg a b k).val = 0) ∧
        (k.val = b.val → a.val ≠ b.val → a.val < 10 → ((sg a b k).val = 1 ∨ (sg a b k).val = 2)) ∧
        (k.val = b.val → a.val = 10 → (sg a b k).val = 0)) := by
    refine ⟨fun a b k => ⟨((([[0, 1, 2, 3, 4, 5, 6, 7, 8, 9], [0, 1, 2, 3, 4, 5, 6, 7, 8, 9], [0, 1, 2, 3, 4, 5, 6, 7, 8, 9], [0, 4, 3, 2, 1, 5, 9, 8, 7, 6], [0, 4, 3, 2, 1, 5, 9, 8, 7, 6], [0, 4, 3, 8, 5, 1, 9, 2, 6, 7], [0, 1, 6, 8, 5, 4, 2, 9, 3, 7], [0, 4, 3, 8, 5, 1, 9, 2, 6, 7], [0, 4, 9, 7, 5, 1, 3, 6, 2, 8], [0, 4, 9, 6, 1, 5, 3, 7, 8, 2], [0, 1, 2, 3, 4, 5, 6, 7, 8, 9], [1, 0, 4, 3, 2, 6, 5, 9, 8, 7], [1, 0, 4, 3, 2, 6, 5, 9, 8, 7], [4, 0, 1, 2, 3, 9, 5, 6, 7, 8], [4, 0, 1, 2, 3, 9, 5, 6, 7, 8], [1, 0, 4, 3, 2, 6, 5, 9, 8, 7], [1, 0, 4, 9, 6, 2, 5, 3, 7, 8], [4, 0, 5, 7, 9, 3, 1, 8, 2, 6], [4, 0, 1, 6, 9, 3, 5, 2, 8, 7], [4, 0, 5, 7, 9, 3, 1, 8, 2, 6], [4, 0, 5, 8, 3, 9, 1, 7, 6, 2], [1, 0, 4, 3, 2, 6, 5, 9, 8, 7], [2, 1, 0, 4, 3, 7, 6, 5, 9, 8], [2, 1, 0, 4, 3, 7, 6, 5, 9, 8], [2, 1, 0, 4, 3, 7, 6, 5, 9, 8], [3, 4, 0, 1, 2, 8, 9, 5, 6, 7], [3, 4, 0, 1, 2, 8, 9, 5, 6, 7], [3, 4, 0, 5, 8, 2, 9, 1, 7, 6], [6, 1, 0, 4, 9, 8, 2, 5, 3, 7], [3, 4, 0, 5, 8, 2, 9, 1, 7, 6], [8, 5, 0, 1, 6, 3, 7, 4, 2, 9], [8, 5, 0, 4, 3, 6, 7, 1, 9, 2], [2, 1, 0, 4, 3, 7, 6, 5, 9, 8], [2, 3, 4, 0, 1, 7, 8, 9, 5, 6], [3, 2, 1, 0, 4, 8, 7, 6, 5, 9], [3, 2, 1, 0, 4, 8, 7, 6, 5, 9], [2, 3, 4, 0, 1, 7, 8, 9, 5, 6], [2, 3, 4, 0, 1, 7, 8, 9, 5, 6], [3, 8, 5, 0, 4, 2, 6, 7, 1, 9], [8, 3, 4, 0, 5, 6, 2, 9, 1, 7], [8, 6, 1, 0, 5, 3, 9, 2, 4, 7], [3, 8, 5, 0, 4, 2, 6, 7, 1, 9], [6, 8, 5, 0, 1, 9, 3, 7, 4, 2], [2, 3, 4, 0, 1, 7, 8, 9, 5, 6], [1, 2, 3, 4, 0, 6, 7, 8, 9, 5], [1, 2, 3, 4, 0, 6, 7, 8, 9, 5], [4, 3, 2, 1, 0, 9, 8, 7, 6, 5], [4, 3, 2, 1, 0, 9, 8, 7, 6, 5], [1, 2, 3, 4, 0, 6, 7, 8, 9, 5], [1, 6, 8, 5, 0, 2, 9, 3, 7, 4], [4, 3, 8, 5, 0, 9, 2, 6, 7, 1], [4, 9, 7, 5, 0, 3, 6, 2, 8, 1], [4, 9, 6, 1, 0, 3, 7, 8, 2, 5], [4, 3, 8, 5, 0, 9, 2, 6, 7, 1], [1, 2, 3, 4, 0, 6, 7, 8, 9, 5], [1, 2, 3, 8, 6, 0, 7, 4, 5, 9], [1, 2, 3, 8, 6, 0, 7, 4, 5, 9], [4, 3, 2, 7, 9, 0, 8, 1, 5, 6], [4, 9, 7, 2, 3, 0, 6, 5, 1, 8], [1, 6, 8, 3, 2, 0, 9, 5, 4, 7], [1, 2, 3, 8, 6, 0, 7, 4, 5, 9], [4, 3, 8, 6, 9, 0, 2, 5, 1, 7], [4, 3, 2, 7, 9, 0, 8, 1, 5, 6], [4, 3, 8, 6, 9, 0, 2, 5, 1, 7], [4, 9, 6, 8, 3, 0, 7, 1, 5, 2], [1, 2, 3, 8, 6, 0, 7, 4, 5, 9], [2, 1, 6, 8, 3, 7, 0, 9, 5, 4], [2, 1, 6, 8, 3, 7, 0, 9, 5, 4], [6, 1, 2, 3, 8, 9, 0, 7, 4, 5], [8, 5, 7, 2, 3, 6, 0, 9, 1, 4], [3, 4, 9, 7, 2, 8, 0, 6, 5, 1], [3, 4, 9, 6, 8, 2, 0, 7, 1, 5], [2, 1, 6, 8, 3, 7, 0, 9, 5, 4], [8, 5, 7, 9, 6, 3, 0, 2, 4, 1], [3, 4, 9, 6, 8, 2, 0, 7, 1, 5], [3, 4, 9, 7, 2, 8, 0, 6, 5, 1], [2, 1, 6, 8, 3, 7, 0, 9, 5, 4], [2, 3, 4, 9, 7, 1, 8, 0, 6, 5], [3, 2, 1, 6, 8, 4, 7, 0, 9, 5], [3, 2, 1, 6, 8, 4, 7, 0, 9, 5], [8, 6, 1, 2, 3, 5, 9, 0, 7, 4], [3, 8, 5, 7, 2, 4, 6, 0, 9, 1], [2, 3, 4, 9, 7, 1, 8, 0, 6, 5], [8, 3, 4, 9, 6, 5, 2, 0, 7, 1], [2, 3, 4, 9, 7, 1, 8, 0, 6, 5], [6, 8, 5, 7, 9, 1, 3, 0, 2, 4], [3, 8, 5, 7, 2, 4, 6, 0, 9, 1], [2, 3, 4, 9, 7, 1, 8, 0, 6, 5], [2, 3, 8, 5, 7, 1, 4, 6, 0, 9], [3, 2, 7, 5, 8, 4, 1, 9, 0, 6], [8, 3, 2, 1, 6, 5, 4, 7, 0, 9], [3, 8, 6, 1, 2, 4, 5, 9, 0, 7], [3, 8, 6, 1, 2, 4, 5, 9, 0, 7], [2, 3, 8, 5, 7, 1, 4, 6, 0, 9], [3, 2, 7, 5, 8, 4, 1, 9, 0, 6], [6, 8, 3, 4, 9, 1, 5, 2, 0, 7], [2, 3, 8, 5, 7, 1, 4, 6, 0, 9], [8, 6, 9, 4, 3, 5, 1, 7, 0, 2], [2, 3, 8, 5, 7, 1, 4, 6, 0, 9], [2, 3, 8, 6, 1, 7, 4, 5, 9, 0], [3, 2, 7, 9, 4, 8, 1, 5, 6, 0], [8, 3, 2, 7, 5, 6, 4, 1, 9, 0], [6, 8, 3, 2, 1, 9, 5, 4, 7, 0], [2, 3, 8, 6, 1, 7, 4, 5, 9, 0], [3, 8, 6, 9, 4, 2, 5, 1, 7, 0], [3, 2, 7, 9, 4, 8, 1, 5, 6, 0], [3, 8, 6, 9, 4, 2, 5, 1, 7, 0], [8, 6, 9, 7, 5, 3, 1, 4, 2, 0], [2, 3, 8, 6, 1, 7, 4, 5, 9, 0], [2, 3, 8, 6, 1, 7, 4, 5, 9, 0], [0, 1, 2, 3, 4, 5, 6, 7, 8, 9], [1, 0, 4, 3, 2, 6, 5, 9, 8, 7], [2, 1, 0, 4, 3, 7, 6, 5, 9, 8], [2, 3, 4, 0, 1, 7, 8, 9, 5, 6], [1, 2, 3, 4, 0, 6, 7, 8, 9, 5], [1, 2, 3, 8, 6, 0, 7, 4, 5, 9], [2, 1, 6, 8, 3, 7, 0, 9, 5, 4], [2, 3, 4, 9, 7, 1, 8, 0, 6, 5], [2, 3, 8, 5, 7, 1, 4, 6, 0, 9], [2, 3, 8, 6, 1, 7, 4, 5, 9, 0], [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]] : List (List ℕ))).getD (a.val * 11 + b.val) []).getD k.val 0 % 10,
      Nat.mod_lt _ (by norm_num)⟩, ?_, ?_, ?_, ?_⟩
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
  have hinjσ : Function.Injective (sg a b) := fun i j h => hinj a b i j h
  have haut := autP (sg a b) (hfwd a b) (hbwd a b)
  have hu : 10 ≤ 10 + u.val := by omega
  have hv : 10 ≤ 10 + v.val := by omega
  have evalOr : ∀ l : List Bool, GateOp.or.eval l = l.any id := fun l => rfl
  by_cases ha : a.val < 10
  · have hσa : sg a b ⟨a.val, ha⟩ = 0 := Fin.ext ((hpos a b ⟨a.val, ha⟩).1 rfl)
    by_cases hb : b.val < 10
    · by_cases hab : a.val = b.val
      · apply finish (sg a b) 10 (fun z => z 0) _ _ hinjσ haut (Or.inl rfl) (fun _ => rfl)
          (fun _ => rfl) hu hv
        · intro z
          rw [getD_snoc, getD_snoc, evalOr]
          simp only [List.length_ofFn, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
            id_eq, Bool.or_false, getD_ofFn, ← hab, dif_pos ha, Function.comp, hσa]
          simp
        · exact hC _ u v (relab _).1 (relab _).2
      · rcases (hpos a b ⟨b.val, hb⟩).2.1 rfl hab ha with h1 | h2
        · have hσb : sg a b ⟨b.val, hb⟩ = 1 := Fin.ext h1
          apply finish (sg a b) 10 (fun z => z 0 || z 1) _ _ hinjσ haut (Or.inl rfl) (fun _ => rfl)
            (fun _ => rfl) hu hv
          · intro z
            rw [getD_snoc, getD_snoc, evalOr]
            simp only [List.length_ofFn, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
              id_eq, Bool.or_false, getD_ofFn, dif_pos ha, dif_pos hb, Function.comp, hσa, hσb]
            simp
          · exact hA _ u v (relab _).1 (relab _).2
        · have hσb : sg a b ⟨b.val, hb⟩ = 2 := Fin.ext h2
          apply finish (sg a b) 10 (fun z => z 0 || z 2) _ _ hinjσ haut (Or.inl rfl) (fun _ => rfl)
            (fun _ => rfl) hu hv
          · intro z
            rw [getD_snoc, getD_snoc, evalOr]
            simp only [List.length_ofFn, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
              id_eq, Bool.or_false, getD_ofFn, dif_pos ha, dif_pos hb, Function.comp, hσa, hσb]
            simp
          · exact hB _ u v (relab _).1 (relab _).2
    · apply finish (sg a b) 10 (fun z => z 0) _ _ hinjσ haut (Or.inl rfl) (fun _ => rfl)
        (fun _ => rfl) hu hv
      · intro z
        rw [getD_snoc, getD_snoc, evalOr]
        simp only [List.length_ofFn, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
          id_eq, Bool.or_false, getD_ofFn, dif_pos ha, dif_neg hb, Function.comp, hσa]
        simp
      · exact hC _ u v (relab _).1 (relab _).2
  · by_cases hb : b.val < 10
    · have ha10 : a.val = 10 := by omega
      have hσb : sg a b ⟨b.val, hb⟩ = 0 := Fin.ext ((hpos a b ⟨b.val, hb⟩).2.2 rfl ha10)
      apply finish (sg a b) 10 (fun z => z 0) _ _ hinjσ haut (Or.inl rfl) (fun _ => rfl)
        (fun _ => rfl) hu hv
      · intro z
        rw [getD_snoc, getD_snoc, evalOr]
        simp only [List.length_ofFn, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
          id_eq, Bool.or_false, getD_ofFn, dif_neg ha, dif_pos hb, Function.comp, hσb]
        simp
      · exact hC _ u v (relab _).1 (relab _).2
    · have prefixW : ∀ (gs : List Gate) (xs : List Bool) (i : ℕ), i < xs.length →
          (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]) xs).getD i
            false = xs.getD i false := by
        intro gs
        induction gs with
        | nil => intro xs i _; rfl
        | cons g gs ih =>
          intro xs i hi
          simp only [List.foldl_cons]
          rw [ih _ _ (by simp only [List.length_append, List.length_singleton]; omega), getD_snoc]
          simp [show xs.length ≠ i by omega]
      have hW10 : ∀ z, W0 z 10 = false := by
        intro z
        show (C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)])
          (List.ofFn z ++ [GateOp.or.eval ([a.val, b.val].map fun i =>
            (List.ofFn z).getD i false)])).getD 10 false = false
        rw [prefixW _ _ _ (by simp), getD_snoc, evalOr]
        simp only [List.length_ofFn, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
          id_eq, Bool.or_false, getD_ofFn, dif_neg ha, dif_neg hb]
        simp
      intro h1 h2 h3
      have hu10 : 10 + u.val ≠ 10 := by
        intro h
        obtain ⟨z, hz, _⟩ := h1
        rw [h, hW10] at hz
        exact Bool.false_ne_true hz
      have hv10 : 10 + v.val ≠ 10 := by
        intro h
        obtain ⟨z, _, hz⟩ := h2
        rw [h, hW10] at hz
        exact Bool.false_ne_true hz
      refine finish (sg a b) (11 + C.size) (fun z => z 0) _ _ hinjσ haut (Or.inr le_rfl)
        (fun h => absurd h hu10) (fun h => absurd h hv10) hu hv ?_
        (hC _ u v (relab _).1 (relab _).2) h1 h2 h3
      intro z
      have hbig : ¬ (11 + C.size < 10) := by omega
      have hne : ¬ ((10:ℕ) = 11 + C.size) := by omega
      rw [getD_snoc, getD_snoc, evalOr, getD_ofFn, dif_neg hbig]
      simp only [List.length_ofFn, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
        id_eq, Bool.or_false, getD_ofFn, dif_neg ha, dif_neg hb, decide_eq_false hne,
        Bool.false_or, Bool.and_false]
      simp
