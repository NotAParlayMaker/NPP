import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1516

private def line13 (t : Fin 13) : Finset (Fin 13) :=
  {t, t + 1, t + 3, t + 9}

private lemma mem_line13_iff (t v : Fin 13) :
    v ∈ line13 t ↔ v = t ∨ v = t + 1 ∨ v = t + 3 ∨ v = t + 9 := by
  simp [line13]

private lemma line13_card (t : Fin 13) : (line13 t).card = 4 := by
  have h1 : t ≠ t + 1 := by intro h; have := congrArg Fin.val h; omega
  have h2 : t ≠ t + 3 := by intro h; have := congrArg Fin.val h; omega
  have h3 : t ≠ t + 9 := by intro h; have := congrArg Fin.val h; omega
  have h4 : t + 1 ≠ t + 3 := by intro h; have := congrArg Fin.val h; omega
  have h5 : t + 1 ≠ t + 9 := by intro h; have := congrArg Fin.val h; omega
  have h6 : t + 3 ≠ t + 9 := by intro h; have := congrArg Fin.val h; omega
  simp [line13, h1, h2, h3, h4, h5, h6]

private lemma diff13_uniq : ∀ (t t' p q : Fin 13), t ≠ t' →
    (p = t ∨ p = t + 1 ∨ p = t + 3 ∨ p = t + 9) →
    (p = t' ∨ p = t' + 1 ∨ p = t' + 3 ∨ p = t' + 9) →
    (q = t ∨ q = t + 1 ∨ q = t + 3 ∨ q = t + 9) →
    (q = t' ∨ q = t' + 1 ∨ q = t' + 3 ∨ q = t' + 9) →
    p = q := by
  intro t t' p q hne hp1 hp2 hq1 hq2
  have h0 : ∀ (a b c e : Fin 13),
      (a = 0 ∨ a = 1 ∨ a = 3 ∨ a = 9) →
      (b = 0 ∨ b = 1 ∨ b = 3 ∨ b = 9) →
      (c = 0 ∨ c = 1 ∨ c = 3 ∨ c = 9) →
      (e = 0 ∨ e = 1 ∨ e = 3 ∨ e = 9) →
      a - b ≠ 0 → a - b = c - e → a = c := by
    intro a b c e ha hb hc he hne' hEq
    rcases ha with rfl | rfl | rfl | rfl <;>
    rcases hb with rfl | rfl | rfl | rfl <;>
    rcases hc with rfl | rfl | rfl | rfl <;>
    rcases he with rfl | rfl | rfl | rfl <;>
    first | rfl | (exfalso; revert hne'; decide) | (exfalso; revert hEq; decide)
  have hd : t' - t ≠ 0 := sub_ne_zero.mpr hne.symm
  have hpa : p - t = 0 ∨ p - t = 1 ∨ p - t = 3 ∨ p - t = 9 := by
    rcases hp1 with rfl | rfl | rfl | rfl <;> simp
  have hpb : p - t' = 0 ∨ p - t' = 1 ∨ p - t' = 3 ∨ p - t' = 9 := by
    rcases hp2 with rfl | rfl | rfl | rfl <;> simp
  have hqa : q - t = 0 ∨ q - t = 1 ∨ q - t = 3 ∨ q - t = 9 := by
    rcases hq1 with rfl | rfl | rfl | rfl <;> simp
  have hqb : q - t' = 0 ∨ q - t' = 1 ∨ q - t' = 3 ∨ q - t' = 9 := by
    rcases hq2 with rfl | rfl | rfl | rfl <;> simp
  have heq1 : (p - t) - (p - t') = t' - t := by abel
  have heq2 : (q - t) - (q - t') = t' - t := by abel
  have hpt : p - t = q - t := h0 (p - t) (p - t') (q - t) (q - t') hpa hpb hqa hqb
    (by rw [heq1]; exact hd) (by rw [heq1, heq2])
  exact sub_left_inj.mp hpt

private lemma line13_inter_card (t t' : Fin 13) (hne : t ≠ t') :
    (line13 t ∩ line13 t').card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro p hp q hq
  rw [Finset.mem_inter, mem_line13_iff, mem_line13_iff] at hp hq
  exact diff13_uniq t t' p q hne hp.1 hp.2 hq.1 hq.2

private lemma line13_sdiff_nonempty (t t' : Fin 13) (hne : t ≠ t') :
    (line13 t \ line13 t').Nonempty := by
  apply Finset.card_pos.mp
  have hs := Finset.card_sdiff_add_card_inter (line13 t) (line13 t')
  have hc := line13_card t
  have hi := line13_inter_card t t' hne
  omega

private lemma line13_other_line (t v : Fin 13) (hv : v ∈ line13 t) :
    ∃ t' : Fin 13, t' ≠ t ∧ v ∈ line13 t' := by
  rw [mem_line13_iff] at hv
  rcases hv with rfl | rfl | rfl | rfl
  · refine ⟨v - 1, ?_, ?_⟩
    · intro h; have := congrArg Fin.val h; omega
    · rw [mem_line13_iff]; right; left; abel
  · refine ⟨t + 1, ?_, ?_⟩
    · intro h; have := congrArg Fin.val h; omega
    · rw [mem_line13_iff]; left; rfl
  · refine ⟨t + 3, ?_, ?_⟩
    · intro h; have := congrArg Fin.val h; omega
    · rw [mem_line13_iff]; left; rfl
  · refine ⟨t + 9, ?_, ?_⟩
    · intro h; have := congrArg Fin.val h; omega
    · rw [mem_line13_iff]; left; rfl

private lemma line13_mem_self (t : Fin 13) : t ∈ line13 t := by
  simp [line13]

private def step (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def wiresAt (gates : List PEqualNP.CircuitLowerBounds.Gate) (x : List Bool) (m : ℕ) :
    List Bool :=
  (gates.take m).foldl step x

private lemma take_succ_of_getElem? {α : Type} :
    ∀ (l : List α) (m : ℕ) (a : α), l[m]? = some a → l.take (m + 1) = l.take m ++ [a]
  | [], _, _, h => by simp at h
  | x :: xs, 0, a, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    rfl
  | x :: xs, m + 1, a, h => by
    simp only [List.getElem?_cons_succ] at h
    simp only [List.take_succ_cons, List.cons_append]
    exact congrArg (x :: ·) (take_succ_of_getElem? xs m a h)

private lemma wiresAt_zero (gates : List PEqualNP.CircuitLowerBounds.Gate) (x : List Bool) :
    wiresAt gates x 0 = x := rfl

private lemma wiresAt_succ (gates : List PEqualNP.CircuitLowerBounds.Gate) (x : List Bool) (m : ℕ)
    (g : PEqualNP.CircuitLowerBounds.Gate) (hg : gates[m]? = some g) :
    wiresAt gates x (m + 1) = step (wiresAt gates x m) g := by
  unfold wiresAt
  rw [take_succ_of_getElem? gates m g hg, List.foldl_append]
  rfl

private lemma wiresAt_eq_wires (gates : List PEqualNP.CircuitLowerBounds.Gate) (x : List Bool)
    (out : ℕ) :
    wiresAt gates x gates.length = PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, out⟩ x := by
  unfold wiresAt PEqualNP.CircuitLowerBounds.Circuit.wires step
  rw [List.take_length]

private lemma wiresAt_length (gates : List PEqualNP.CircuitLowerBounds.Gate) (x : List Bool) :
    ∀ m : ℕ, m ≤ gates.length → (wiresAt gates x m).length = x.length + m
  | 0, _ => by simp [wiresAt]
  | m + 1, hm => by
    have hm' : m < gates.length := Nat.lt_of_succ_le hm
    have hg : gates[m]? = some gates[m] := List.getElem?_eq_getElem hm'
    rw [wiresAt_succ gates x m gates[m] hg]
    unfold step
    rw [List.length_append, List.length_singleton, wiresAt_length gates x m (Nat.le_of_lt hm')]
    omega

private lemma getD_of_ge (w : List Bool) (i : ℕ) (h : w.length ≤ i) :
    w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

private lemma step_getD_lt (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate)
    (i : ℕ) (h : i < w.length) :
    (step w g).getD i false = w.getD i false := by
  unfold step
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

private lemma step_getD_eq (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) :
    (step w g).getD w.length false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  unfold step
  simp [List.getD_eq_getElem?_getD]

private lemma step_getD_gt (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate)
    (i : ℕ) (h : w.length < i) :
    (step w g).getD i false = false := by
  have hge : (step w g).length ≤ i := by
    unfold step
    simp
    omega
  exact getD_of_ge (step w g) i hge

private lemma wiresAt_getD_stable (gates : List PEqualNP.CircuitLowerBounds.Gate) (x : List Bool)
    (m1 : ℕ) :
    ∀ (m2 : ℕ), m1 ≤ m2 → m2 ≤ gates.length → ∀ (i : ℕ), i < x.length + m1 →
      (wiresAt gates x m2).getD i false = (wiresAt gates x m1).getD i false
  | 0, h12, _, _, _ => by
    have : m1 = 0 := Nat.eq_zero_of_le_zero h12
    subst this
    rfl
  | m2 + 1, h12, h2len, i, hi => by
    by_cases heq : m1 = m2 + 1
    · subst heq; rfl
    · have hle : m1 ≤ m2 := by omega
      have hm2lt : m2 < gates.length := Nat.lt_of_succ_le h2len
      have hg : gates[m2]? = some gates[m2] := List.getElem?_eq_getElem hm2lt
      rw [wiresAt_succ gates x m2 gates[m2] hg]
      have hlen : (wiresAt gates x m2).length = x.length + m2 :=
        wiresAt_length gates x m2 (Nat.le_of_lt hm2lt)
      have hilt : i < (wiresAt gates x m2).length := by omega
      rw [step_getD_lt _ _ i hilt]
      exact wiresAt_getD_stable gates x m1 m2 hle (Nat.le_of_lt hm2lt) i hi

private def wireVal (gates : List PEqualNP.CircuitLowerBounds.Gate) (x : Fin 13 → Bool) (w : ℕ) :
    Bool :=
  (wiresAt gates (List.ofFn x) gates.length).getD w false

private lemma eval_eq_wireVal (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ)
    (x : Fin 13 → Bool) :
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = wireVal gates x o := by
  unfold PEqualNP.CircuitLowerBounds.Circuit.eval wireVal
  rw [wiresAt_eq_wires]

private lemma wireVal_input (gates : List PEqualNP.CircuitLowerBounds.Gate) (x : Fin 13 → Bool)
    (v : Fin 13) : wireVal gates x v.val = x v := by
  unfold wireVal
  have hst := wiresAt_getD_stable gates (List.ofFn x) 0 gates.length (Nat.zero_le _) (Nat.le_refl _)
    v.val (by simp [v.isLt])
  rw [hst, wiresAt_zero, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [v.isLt]

private lemma wireVal_ge (gates : List PEqualNP.CircuitLowerBounds.Gate) (x : Fin 13 → Bool)
    (w : ℕ) (hw : 13 + gates.length ≤ w) : wireVal gates x w = false := by
  unfold wireVal
  apply getD_of_ge
  rw [wiresAt_length gates (List.ofFn x) gates.length (Nat.le_refl _)]
  simp
  omega

private lemma wireVal_gate (gates : List PEqualNP.CircuitLowerBounds.Gate) (x : Fin 13 → Bool)
    (k : ℕ) (hk : k < gates.length) :
    wireVal gates x (13 + k) =
      (gates[k]).op.eval ((gates[k]).inputs.map fun i =>
        if i < 13 + k then wireVal gates x i else false) := by
  unfold wireVal
  have hst := wiresAt_getD_stable gates (List.ofFn x) (k + 1) gates.length hk (Nat.le_refl _)
    (13 + k) (by simp)
  rw [hst]
  have hg : gates[k]? = some gates[k] := List.getElem?_eq_getElem hk
  rw [wiresAt_succ gates (List.ofFn x) k gates[k] hg]
  have hlen : (wiresAt gates (List.ofFn x) k).length = 13 + k := by
    simpa using wiresAt_length gates (List.ofFn x) k (Nat.le_of_lt hk)
  conv_lhs => rw [← hlen, step_getD_eq]
  congr 1
  apply List.map_congr_left
  intro i _
  by_cases hi : i < 13 + k
  · simp only [hi, ↓reduceIte]
    exact (wiresAt_getD_stable gates (List.ofFn x) k gates.length (Nat.le_of_lt hk) (Nat.le_refl _)
      i (by simp; omega)).symm
  · simp only [hi, ↓reduceIte]
    exact getD_of_ge _ i (by omega)

private lemma wiresAt_mono (gates : List PEqualNP.CircuitLowerBounds.Gate)
    (hmono : ∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2)
    (x y : Fin 13 → Bool) (hxy : ∀ v : Fin 13, x v = true → y v = true) :
    ∀ m : ℕ, m ≤ gates.length → ∀ i : ℕ,
      (wiresAt gates (List.ofFn x) m).getD i false = true →
      (wiresAt gates (List.ofFn y) m).getD i false = true
  | 0, _, i, hi => by
    rw [wiresAt_zero] at hi ⊢
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn] at hi ⊢
    by_cases hlt : i < 13
    · simp only [hlt, ↓reduceDIte, Option.getD_some] at hi ⊢
      exact hxy ⟨i, hlt⟩ hi
    · simp only [hlt, ↓reduceDIte, Option.getD_none] at hi
      exact Bool.noConfusion hi
  | m + 1, hm, i, hi => by
    have hmlt : m < gates.length := Nat.lt_of_succ_le hm
    have hg : gates[m]? = some gates[m] := List.getElem?_eq_getElem hmlt
    have hgmem : gates[m] ∈ gates := List.getElem_mem hmlt
    have ih := wiresAt_mono gates hmono x y hxy m (Nat.le_of_lt hmlt)
    rw [wiresAt_succ gates _ m gates[m] hg] at hi ⊢
    have hlenx : (wiresAt gates (List.ofFn x) m).length = 13 + m := by
      simpa using wiresAt_length gates (List.ofFn x) m (Nat.le_of_lt hmlt)
    have hleny : (wiresAt gates (List.ofFn y) m).length = 13 + m := by
      simpa using wiresAt_length gates (List.ofFn y) m (Nat.le_of_lt hmlt)
    rcases Nat.lt_trichotomy i (13 + m) with hlt | heq | hgt
    · rw [step_getD_lt _ _ i (by omega)] at hi ⊢
      exact ih i hi
    · subst heq
      rw [← hlenx, step_getD_eq] at hi
      rw [← hleny, step_getD_eq]
      rcases (hmono gates[m] hgmem).1 with hand | hor
      · rw [hand] at hi ⊢
        simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.all_eq_true, List.mem_map,
          id_eq, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at hi ⊢
        intro u hu
        exact ih u (hi u hu)
      · rw [hor] at hi ⊢
        simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.any_eq_true, List.mem_map,
          id_eq] at hi ⊢
        rcases hi with ⟨b, ⟨u, hu, rfl⟩, hb⟩
        exact ⟨true, ⟨u, hu, ih u hb⟩, rfl⟩
    · rw [step_getD_gt _ _ i (by omega)] at hi
      exact Bool.noConfusion hi

private lemma wireVal_mono (gates : List PEqualNP.CircuitLowerBounds.Gate)
    (hmono : ∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2)
    (x y : Fin 13 → Bool) (hxy : ∀ v : Fin 13, x v = true → y v = true)
    (w : ℕ) (hw : wireVal gates x w = true) : wireVal gates y w = true :=
  wiresAt_mono gates hmono x y hxy gates.length (Nat.le_refl _) w hw

private def zVec (L : Fin 13 → Finset (Fin 13)) (t : Fin 13) : Fin 13 → Bool :=
  fun v => decide (v ∉ L t)

private def yVec (B : Fin 13 → Fin 13 → Finset (Fin 13)) (t p : Fin 13) : Fin 13 → Bool :=
  fun v => decide (v = p ∨ v ∈ B t p)

private def Sset (gates : List PEqualNP.CircuitLowerBounds.Gate)
    (L : Fin 13 → Finset (Fin 13)) (B : Fin 13 → Fin 13 → Finset (Fin 13))
    (t : Fin 13) (w : ℕ) : Finset (Fin 13) :=
  (L t).filter (fun p => wireVal gates (yVec B t p) w = true)

private def isOr : PEqualNP.CircuitLowerBounds.GateOp → Bool
  | PEqualNP.CircuitLowerBounds.GateOp.or => true
  | _ => false

private lemma isOr_eq_true_iff (op : PEqualNP.CircuitLowerBounds.GateOp) :
    isOr op = true ↔ op = PEqualNP.CircuitLowerBounds.GateOp.or := by
  cases op <;> simp [isOr]

private def Mset (gates : List PEqualNP.CircuitLowerBounds.Gate)
    (L : Fin 13 → Finset (Fin 13)) (B : Fin 13 → Fin 13 → Finset (Fin 13))
    (t : Fin 13) : Finset (Fin gates.length) :=
  Finset.univ.filter (fun g : Fin gates.length =>
    isOr (gates.get g).op = true ∧
    wireVal gates (zVec L t) (13 + g.val) = false ∧
    2 ≤ (Sset gates L B t (13 + g.val)).card)

private def MsetUpto (gates : List PEqualNP.CircuitLowerBounds.Gate)
    (L : Fin 13 → Finset (Fin 13)) (B : Fin 13 → Fin 13 → Finset (Fin 13))
    (t : Fin 13) (k : ℕ) : Finset (Fin gates.length) :=
  (Mset gates L B t).filter (fun g => g.val < k)

private lemma main
    (L : Fin 13 → Finset (Fin 13)) (hL : ∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9})
    (D : (Fin 13 → Bool) → Prop)
    (_hDup : ∀ x y : Fin 13 → Bool, D x → (∀ v : Fin 13, x v = true → y v = true) → D y)
    (hDz : ∀ t : Fin 13, D (fun v => decide (v ∉ L t)))
    (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin 13 → ℕ)
    (hmono : ∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2)
    (hEval : ∀ (t : Fin 13) (x : Fin 13 → Bool), D x →
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) =
        decide (∃ v ∈ L t, x v = true))
    (Lam : Finset (Fin 13)) (B : Fin 13 → Fin 13 → Finset (Fin 13))
    (hB1 : ∀ t ∈ Lam, ∀ p ∈ L t, B t p ∩ L t = ∅ ∧ D (fun v => decide (v = p ∨ v ∈ B t p)))
    (hB2 : ∀ t ∈ Lam, ∀ t' ∈ Lam, t ≠ t' →
      ¬ ((∃ p ∈ L t \ L t', (B t p ∩ L t').Nonempty) ∧
         (∃ p ∈ L t' \ L t, (B t' p ∩ L t).Nonempty)))
    (I : Finset (Fin gates.length))
    (hI : ∀ g ∈ I, (gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.and) :
    3 * Lam.card + max (13 - Lam.card) I.card ≤ gates.length := by
  have hL_eq : L = line13 := funext hL
  subst hL_eq
  have heval_z_self : ∀ t : Fin 13, wireVal gates (zVec line13 t) (o t) = false := by
    intro t
    rw [← eval_eq_wireVal, hEval t (zVec line13 t) (hDz t)]
    simp [zVec]
  have heval_z_ne : ∀ t t' : Fin 13, t' ≠ t → wireVal gates (zVec line13 t) (o t') = true := by
    intro t t' hne
    rw [← eval_eq_wireVal, hEval t' (zVec line13 t) (hDz t)]
    rcases line13_sdiff_nonempty t' t hne with ⟨v, hv⟩
    rw [Finset.mem_sdiff] at hv
    simp [zVec]
    exact ⟨v, hv.1, hv.2⟩
  have heval_y : ∀ t ∈ Lam, ∀ p ∈ line13 t, wireVal gates (yVec B t p) (o t) = true := by
    intro t ht p hp
    rw [← eval_eq_wireVal, hEval t (yVec B t p) (hB1 t ht p hp).2]
    simp [yVec]
    exact ⟨p, hp, Or.inl rfl⟩
  have ho_bounds : ∀ t : Fin 13, 13 ≤ o t ∧ o t < 13 + gates.length := by
    intro t
    constructor
    · by_contra hlt
      have hlt' : o t < 13 := Nat.lt_of_not_ge hlt
      let v : Fin 13 := ⟨o t, hlt'⟩
      by_cases hv : v ∈ line13 t
      · rcases line13_other_line t v hv with ⟨t', ht'ne, hvt'⟩
        have h1 : wireVal gates (zVec line13 t') (o t) = true := heval_z_ne t' t ht'ne.symm
        have h2 : wireVal gates (zVec line13 t') v.val = zVec line13 t' v := wireVal_input gates _ v
        have h3 : zVec line13 t' v = false := by simp [zVec, hvt']
        change wireVal gates (zVec line13 t') v.val = true at h1
        rw [h2, h3] at h1
        exact Bool.noConfusion h1
      · have h1 : wireVal gates (zVec line13 t) (o t) = false := heval_z_self t
        have h2 : wireVal gates (zVec line13 t) v.val = zVec line13 t v := wireVal_input gates _ v
        have h3 : zVec line13 t v = true := by simp [zVec, hv]
        change wireVal gates (zVec line13 t) v.val = false at h1
        rw [h2, h3] at h1
        exact Bool.noConfusion h1
    · by_contra hge
      have hge' : 13 + gates.length ≤ o t := Nat.le_of_not_lt hge
      rcases line13_other_line t t (line13_mem_self t) with ⟨t', ht'ne, _⟩
      have h1 : wireVal gates (zVec line13 t') (o t) = true := heval_z_ne t' t ht'ne.symm
      have h2 : wireVal gates (zVec line13 t') (o t) = false := wireVal_ge gates _ (o t) hge'
      rw [h2] at h1
      exact Bool.noConfusion h1
  have ho_inj : Function.Injective o := by
    intro t1 t2 hEq
    by_contra hne
    have h1 := heval_z_self t1
    have h2 := heval_z_ne t1 t2 (Ne.symm hne)
    rw [← hEq, h1] at h2
    exact Bool.noConfusion h2
  have hM_card : ∀ t ∈ Lam, 3 ≤ (Mset gates line13 B t).card := by
    intro t ht
    have hinv : ∀ k : ℕ, k ≤ gates.length →
        ∃ c : Fin 13 → Fin 13,
          4 ≤ ((line13 t).image c).card + (MsetUpto gates line13 B t k).card ∧
          ∀ w : ℕ, w < 13 + k → wireVal gates (zVec line13 t) w = false →
            ∀ p ∈ Sset gates line13 B t w, ∀ q ∈ Sset gates line13 B t w, c p = c q := by
      intro k
      induction k with
      | zero =>
        intro _
        refine ⟨id, ?_, ?_⟩
        · simp [MsetUpto, line13_card t]
        · intro w hw _ p hp q hq
          have hw13 : w < 13 := by omega
          let v : Fin 13 := ⟨w, hw13⟩
          simp only [Sset, Finset.mem_filter] at hp hq
          have hpw : wireVal gates (yVec B t p) v.val = true := hp.2
          have hqw : wireVal gates (yVec B t q) v.val = true := hq.2
          rw [wireVal_input] at hpw hqw
          simp only [yVec, decide_eq_true_eq] at hpw hqw
          have hvp : v = p := by
            rcases hpw with hEq | hB
            · exact hEq
            · exfalso
              have hmem : v ∈ B t p ∩ line13 t := Finset.mem_inter.mpr ⟨hB, by
                have hzv : wireVal gates (zVec line13 t) v.val = false := by
                  assumption
                rw [wireVal_input] at hzv
                simpa [zVec] using hzv⟩
              rw [(hB1 t ht p hp.1).1] at hmem
              exact Finset.notMem_empty v hmem
          have hvq : v = q := by
            rcases hqw with hEq | hB
            · exact hEq
            · exfalso
              have hmem : v ∈ B t q ∩ line13 t := Finset.mem_inter.mpr ⟨hB, by
                have hzv : wireVal gates (zVec line13 t) v.val = false := by
                  assumption
                rw [wireVal_input] at hzv
                simpa [zVec] using hzv⟩
              rw [(hB1 t ht q hq.1).1] at hmem
              exact Finset.notMem_empty v hmem
          exact hvp.symm.trans hvq
      | succ k ih =>
        intro hklen
        have hklt : k < gates.length := Nat.lt_of_succ_le hklen
        rcases ih (Nat.le_of_lt hklt) with ⟨c, hcard, hconst⟩
        let gIdx : Fin gates.length := ⟨k, hklt⟩
        have hupto_sub : MsetUpto gates line13 B t k ⊆ MsetUpto gates line13 B t (k + 1) := by
          intro x hx
          simp only [MsetUpto, Finset.mem_filter] at hx ⊢
          exact ⟨hx.1, Nat.lt_succ_of_lt hx.2⟩
        have hcard_mono : (MsetUpto gates line13 B t k).card ≤ (MsetUpto gates line13 B t (k + 1)).card :=
          Finset.card_le_card hupto_sub
        by_cases hzk : wireVal gates (zVec line13 t) (13 + k) = false
        · have hgmem : gates[k] ∈ gates := List.getElem_mem hklt
          rcases (hmono gates[k] hgmem).1 with hand | hor
          · refine ⟨c, by omega, ?_⟩
            intro w hw hzw p hp q hq
            by_cases hwk : w < 13 + k
            · exact hconst w hwk hzw p hp q hq
            · have hweq : w = 13 + k := by omega
              subst hweq
              have hzk' := hzk
              rw [wireVal_gate gates (zVec line13 t) k hklt, hand] at hzk'
              simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.all_eq_false, List.mem_map,
                id_eq, Bool.not_eq_true] at hzk'
              rcases hzk' with ⟨b, ⟨u, hu, hbu⟩, hb⟩
              subst hb
              by_cases hult : u < 13 + k
              · simp only [hult, ↓reduceIte] at hbu
                have hsub : Sset gates line13 B t (13 + k) ⊆ Sset gates line13 B t u := by
                  intro r hr
                  simp only [Sset, Finset.mem_filter] at hr ⊢
                  refine ⟨hr.1, ?_⟩
                  have hrv := hr.2
                  rw [wireVal_gate gates (yVec B t r) k hklt, hand] at hrv
                  simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.all_eq_true, List.mem_map,
                    id_eq, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at hrv
                  have hru := hrv u hu
                  simpa [hult] using hru
                exact hconst u hult hbu p (hsub hp) q (hsub hq)
              · exfalso
                simp only [Sset, Finset.mem_filter] at hp
                have hpv := hp.2
                rw [wireVal_gate gates (yVec B t p) k hklt, hand] at hpv
                simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.all_eq_true, List.mem_map,
                  id_eq, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at hpv
                have hpu := hpv u hu
                simp [hult] at hpu
          · by_cases hbig : 2 ≤ (Sset gates line13 B t (13 + k)).card
            · have hgInM : gIdx ∈ Mset gates line13 B t := by
                simp only [Mset, Finset.mem_filter, Finset.mem_univ, true_and]
                exact ⟨(isOr_eq_true_iff _).mpr (by simpa [gIdx] using hor), hzk, hbig⟩
              have hgNotIn : gIdx ∉ MsetUpto gates line13 B t k := by
                simp [MsetUpto, gIdx]
              have hupto_eq : MsetUpto gates line13 B t (k + 1) =
                  insert gIdx (MsetUpto gates line13 B t k) := by
                ext x
                simp only [MsetUpto, Finset.mem_filter, Finset.mem_insert]
                constructor
                · intro hx
                  by_cases hxk : x.val = k
                  · left; exact Fin.ext hxk
                  · right; exact ⟨hx.1, by omega⟩
                · rintro (rfl | hx)
                  · exact ⟨hgInM, Nat.lt_succ_self k⟩
                  · exact ⟨hx.1, Nat.lt_succ_of_lt hx.2⟩
              have hcard_inc : (MsetUpto gates line13 B t (k + 1)).card =
                  (MsetUpto gates line13 B t k).card + 1 := by
                rw [hupto_eq, Finset.card_insert_of_notMem hgNotIn]
              have hlen2 : (gates[k]).inputs.length ≤ 2 := (hmono gates[k] hgmem).2
              have hzk_in : ∀ u ∈ (gates[k]).inputs, u < 13 + k →
                  wireVal gates (zVec line13 t) u = false := by
                intro u hu hult
                have hzk' := hzk
                rw [wireVal_gate gates (zVec line13 t) k hklt, hor] at hzk'
                simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.any_eq_false, List.mem_map,
                  id_eq, Bool.not_eq_true, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at hzk'
                have hzu := hzk' u hu
                simpa [hult] using hzu
              have hor_mem : ∀ r ∈ Sset gates line13 B t (13 + k),
                  ∃ u ∈ (gates[k]).inputs, u < 13 + k ∧ r ∈ Sset gates line13 B t u := by
                intro r hr
                simp only [Sset, Finset.mem_filter] at hr
                have hrv := hr.2
                rw [wireVal_gate gates (yVec B t r) k hklt, hor] at hrv
                simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.any_eq_true, List.mem_map,
                  id_eq] at hrv
                rcases hrv with ⟨b, ⟨u, hu, hbu⟩, hb⟩
                subst hb
                by_cases hult : u < 13 + k
                · simp only [hult, ↓reduceIte] at hbu
                  exact ⟨u, hu, hult, Finset.mem_filter.mpr ⟨hr.1, hbu⟩⟩
                · simp [hult] at hbu
              rcases hList : (gates[k]).inputs with _ | ⟨u1, _ | ⟨u2, rest⟩⟩
              · exfalso
                have hne : (Sset gates line13 B t (13 + k)).Nonempty :=
                  Finset.card_pos.mp (by omega)
                rcases hne with ⟨r, hr⟩
                rcases hor_mem r hr with ⟨u, hu, _, _⟩
                rw [hList] at hu
                exact List.not_mem_nil hu
              · refine ⟨c, by omega, ?_⟩
                intro w hw hzw p hp q hq
                by_cases hwk : w < 13 + k
                · exact hconst w hwk hzw p hp q hq
                · have hweq : w = 13 + k := by omega
                  subst hweq
                  rcases hor_mem p hp with ⟨up, hup, huplt, hpr⟩
                  rcases hor_mem q hq with ⟨uq, huq, huqlt, hqr⟩
                  rw [hList] at hup huq
                  simp only [List.mem_singleton] at hup huq
                  rw [hup] at huplt hpr
                  rw [huq] at huqlt hqr
                  have hu1mem : u1 ∈ (gates[k]).inputs := by rw [hList]; simp
                  exact hconst u1 huplt (hzk_in u1 hu1mem huplt) p hpr q hqr
              · have hrest : rest = [] := by
                  rw [hList] at hlen2
                  cases rest with
                  | nil => rfl
                  | cons _ _ => simp at hlen2
                subst hrest
                have hu1mem : u1 ∈ (gates[k]).inputs := by rw [hList]; simp
                have hu2mem : u2 ∈ (gates[k]).inputs := by rw [hList]; simp
                by_cases hne1 : u1 < 13 + k ∧ (Sset gates line13 B t u1).Nonempty
                · by_cases hne2 : u2 < 13 + k ∧ (Sset gates line13 B t u2).Nonempty
                  · rcases hne1 with ⟨hu1lt, ⟨p1, hp1⟩⟩
                    rcases hne2 with ⟨hu2lt, ⟨p2, hp2⟩⟩
                    let a := c p1
                    let b := c p2
                    let c' : Fin 13 → Fin 13 := fun r => if c r = b then a else c r
                    refine ⟨c', ?_, ?_⟩
                    · have hsub_img : ((line13 t).image c).erase b ⊆ (line13 t).image c' := by
                        intro y hy
                        rw [Finset.mem_erase, Finset.mem_image] at hy
                        rcases hy with ⟨hyb, r, hr, rfl⟩
                        exact Finset.mem_image.mpr ⟨r, hr, by simp [c', hyb]⟩
                      have h1 := Finset.card_le_card hsub_img
                      have h2 : ((line13 t).image c).card - 1 ≤ (((line13 t).image c).erase b).card :=
                        Finset.pred_card_le_card_erase
                      omega
                    · intro w hw hzw p hp q hq
                      by_cases hwk : w < 13 + k
                      · have hcpq : c p = c q := hconst w hwk hzw p hp q hq
                        simp [c', hcpq]
                      · have hweq : w = 13 + k := by omega
                        subst hweq
                        have hval : ∀ r ∈ Sset gates line13 B t (13 + k), c' r = a := by
                          intro r hr
                          rcases hor_mem r hr with ⟨u, hu, hult, hru⟩
                          rw [hList] at hu
                          simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
                          rcases hu with hEq | hEq
                          · rw [hEq] at hru
                            have hcr : c r = a := hconst u1 hu1lt (hzk_in u1 hu1mem hu1lt) r hru p1 hp1
                            by_cases hab : a = b
                            · simp [c', hcr, hab]
                            · simp [c', hcr, hab]
                          · rw [hEq] at hru
                            have hcr : c r = b := hconst u2 hu2lt (hzk_in u2 hu2mem hu2lt) r hru p2 hp2
                            simp [c', hcr]
                        rw [hval p hp, hval q hq]
                  · refine ⟨c, by omega, ?_⟩
                    intro w hw hzw p hp q hq
                    by_cases hwk : w < 13 + k
                    · exact hconst w hwk hzw p hp q hq
                    · have hweq : w = 13 + k := by omega
                      subst hweq
                      have hmem1 : ∀ r ∈ Sset gates line13 B t (13 + k), r ∈ Sset gates line13 B t u1 := by
                        intro r hr
                        rcases hor_mem r hr with ⟨u, hu, hult, hru⟩
                        rw [hList] at hu
                        simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
                        rcases hu with hEq | hEq
                        · rw [hEq] at hru; exact hru
                        · rw [hEq] at hult hru; exfalso; exact hne2 ⟨hult, ⟨r, hru⟩⟩
                      exact hconst u1 hne1.1 (hzk_in u1 hu1mem hne1.1) p (hmem1 p hp) q (hmem1 q hq)
                · refine ⟨c, by omega, ?_⟩
                  intro w hw hzw p hp q hq
                  by_cases hwk : w < 13 + k
                  · exact hconst w hwk hzw p hp q hq
                  · have hweq : w = 13 + k := by omega
                    subst hweq
                    rcases hor_mem p hp with ⟨up, hup, huplt, hpr⟩
                    rcases hor_mem q hq with ⟨uq, huq, huqlt, hqr⟩
                    rw [hList] at hup huq
                    simp only [List.mem_cons, List.not_mem_nil, or_false] at hup huq
                    have hup2 : up = u2 := by
                      rcases hup with hEq | hEq
                      · rw [hEq] at huplt hpr; exfalso; exact hne1 ⟨huplt, ⟨p, hpr⟩⟩
                      · exact hEq
                    have huq2 : uq = u2 := by
                      rcases huq with hEq | hEq
                      · rw [hEq] at huqlt hqr; exfalso; exact hne1 ⟨huqlt, ⟨q, hqr⟩⟩
                      · exact hEq
                    rw [hup2] at huplt hpr
                    rw [huq2] at huqlt hqr
                    exact hconst u2 huplt (hzk_in u2 hu2mem huplt) p hpr q hqr
            · refine ⟨c, by omega, ?_⟩
              intro w hw hzw p hp q hq
              by_cases hwk : w < 13 + k
              · exact hconst w hwk hzw p hp q hq
              · have hweq : w = 13 + k := by omega
                subst hweq
                have hle1 : (Sset gates line13 B t (13 + k)).card ≤ 1 := by omega
                have hpq : p = q := Finset.card_le_one.mp hle1 p hp q hq
                subst hpq; rfl
        · refine ⟨c, by omega, ?_⟩
          intro w hw hzw p hp q hq
          by_cases hwk : w < 13 + k
          · exact hconst w hwk hzw p hp q hq
          · have hweq : w = 13 + k := by omega
            subst hweq
            exact False.elim (hzk hzw)
    rcases hinv gates.length (Nat.le_refl _) with ⟨c, hcard, hconst⟩
    have hot_lt : o t < 13 + gates.length := (ho_bounds t).2
    have hS_ot : Sset gates line13 B t (o t) = line13 t := by
      ext p
      simp only [Sset, Finset.mem_filter, and_iff_left_iff_imp]
      exact fun hp => heval_y t ht p hp
    have himg_le : ((line13 t).image c).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro y1 hy1 y2 hy2
      rw [Finset.mem_image] at hy1 hy2
      rcases hy1 with ⟨p1, hp1, rfl⟩
      rcases hy2 with ⟨p2, hp2, rfl⟩
      rw [← hS_ot] at hp1 hp2
      exact hconst (o t) hot_lt (heval_z_self t) p1 hp1 p2 hp2
    have hM_eq : MsetUpto gates line13 B t gates.length = Mset gates line13 B t := by
      ext g
      simp [MsetUpto]
    rw [hM_eq] at hcard
    omega
  have hM_disj : Set.PairwiseDisjoint (↑Lam : Set (Fin 13)) (fun t => Mset gates line13 B t) := by
    intro t1 ht1 t2 ht2 hne
    rw [Function.onFun, Finset.disjoint_left]
    intro g hg1 hg2
    simp only [Mset, Finset.mem_filter, Finset.mem_univ, true_and] at hg1 hg2
    have hfind : ∀ a b : Fin 13, a ∈ Lam → b ∈ Lam → a ≠ b →
        wireVal gates (zVec line13 b) (13 + g.val) = false →
        2 ≤ (Sset gates line13 B a (13 + g.val)).card →
        ∃ p ∈ line13 a \ line13 b, (B a p ∩ line13 b).Nonempty := by
      intro a b ha _ hab hzb hcard_a
      have hinter_le : (Sset gates line13 B a (13 + g.val) ∩ line13 b).card ≤ 1 := by
        have hsub : Sset gates line13 B a (13 + g.val) ∩ line13 b ⊆ line13 a ∩ line13 b := by
          intro r hr
          rw [Finset.mem_inter] at hr ⊢
          exact ⟨(Finset.mem_filter.mp hr.1).1, hr.2⟩
        have hc := Finset.card_le_card hsub
        exact le_trans hc (line13_inter_card a b hab)
      have hdiff_ne : (Sset gates line13 B a (13 + g.val) \ line13 b).Nonempty := by
        apply Finset.card_pos.mp
        have hs := Finset.card_sdiff_add_card_inter (Sset gates line13 B a (13 + g.val)) (line13 b)
        omega
      rcases hdiff_ne with ⟨p, hp⟩
      rw [Finset.mem_sdiff] at hp
      rcases hp with ⟨hpS, hpb⟩
      have hpL : p ∈ line13 a := (Finset.mem_filter.mp hpS).1
      have hpv : wireVal gates (yVec B a p) (13 + g.val) = true := (Finset.mem_filter.mp hpS).2
      refine ⟨p, Finset.mem_sdiff.mpr ⟨hpL, hpb⟩, ?_⟩
      by_contra hempty
      rw [Finset.not_nonempty_iff_eq_empty] at hempty
      have hle_vec : ∀ v : Fin 13, yVec B a p v = true → zVec line13 b v = true := by
        intro v hv
        simp only [yVec, decide_eq_true_eq] at hv
        simp only [zVec, decide_eq_true_eq]
        intro hvb
        rcases hv with rfl | hvB
        · exact hpb hvb
        · have hm : v ∈ B a p ∩ line13 b := Finset.mem_inter.mpr ⟨hvB, hvb⟩
          rw [hempty] at hm
          exact Finset.notMem_empty v hm
      have htrue := wireVal_mono gates hmono (yVec B a p) (zVec line13 b) hle_vec (13 + g.val) hpv
      rw [hzb] at htrue
      exact Bool.noConfusion htrue
    have h1 := hfind t1 t2 ht1 ht2 hne hg2.2.1 hg1.2.2
    have h2 := hfind t2 t1 ht2 ht1 hne.symm hg1.2.1 hg2.2.2
    exact hB2 t1 ht1 t2 ht2 hne ⟨h1, h2⟩
  let U : Finset (Fin gates.length) := Lam.biUnion (fun t => Mset gates line13 B t)
  have hU_card : 3 * Lam.card ≤ U.card := by
    rw [Finset.card_biUnion hM_disj]
    have hsum : ∑ _t ∈ Lam, 3 ≤ ∑ t ∈ Lam, (Mset gates line13 B t).card :=
      Finset.sum_le_sum hM_card
    simpa [Nat.mul_comm] using hsum
  have hU_disj_I : Disjoint U I := by
    rw [Finset.disjoint_left]
    intro g hgU hgI
    rw [Finset.mem_biUnion] at hgU
    rcases hgU with ⟨t, _, hgt⟩
    simp only [Mset, Finset.mem_filter, Finset.mem_univ, true_and] at hgt
    have hand := hI g hgI
    have hor := (isOr_eq_true_iff _).mp hgt.1
    rw [hand] at hor
    exact PEqualNP.CircuitLowerBounds.GateOp.noConfusion hor
  have hbound_I : 3 * Lam.card + I.card ≤ gates.length := by
    have h1 : (U ∪ I).card = U.card + I.card := Finset.card_union_of_disjoint hU_disj_I
    have h2 : (U ∪ I).card ≤ gates.length := by
      simpa [Fintype.card_fin] using Finset.card_le_univ (U ∪ I)
    omega
  let outGate : Fin 13 → Fin gates.length := fun t => ⟨o t - 13, by
    have hb := ho_bounds t
    omega⟩
  have houtGate_inj : Function.Injective outGate := by
    intro t1 t2 hEq
    have hval : o t1 - 13 = o t2 - 13 := congrArg Fin.val hEq
    have hb1 := (ho_bounds t1).1
    have hb2 := (ho_bounds t2).1
    exact ho_inj (by omega)
  let Gout : Finset (Fin gates.length) := (Finset.univ \ Lam).image outGate
  have hGout_card : Gout.card = 13 - Lam.card := by
    rw [Finset.card_image_of_injective _ houtGate_inj, Finset.card_sdiff]
    simp
  have hU_disj_Gout : Disjoint U Gout := by
    rw [Finset.disjoint_left]
    intro g hgU hgG
    rw [Finset.mem_biUnion] at hgU
    rcases hgU with ⟨t, htLam, hgt⟩
    simp only [Mset, Finset.mem_filter, Finset.mem_univ, true_and] at hgt
    rw [Finset.mem_image] at hgG
    rcases hgG with ⟨t', ht'mem, hEq⟩
    rw [Finset.mem_sdiff] at ht'mem
    have hne : t' ≠ t := fun h => ht'mem.2 (h ▸ htLam)
    have hval : 13 + g.val = o t' := by
      have h1 : o t' - 13 = g.val := congrArg Fin.val hEq
      have hb := (ho_bounds t').1
      omega
    have htrue : wireVal gates (zVec line13 t) (o t') = true := heval_z_ne t t' hne
    rw [← hval, hgt.2.1] at htrue
    exact Bool.noConfusion htrue
  have hbound_out : 3 * Lam.card + (13 - Lam.card) ≤ gates.length := by
    have h1 : (U ∪ Gout).card = U.card + Gout.card := Finset.card_union_of_disjoint hU_disj_Gout
    have h2 : (U ∪ Gout).card ≤ gates.length := by
      simpa [Fintype.card_fin] using Finset.card_le_univ (U ∪ Gout)
    omega
  omega

end PEqualNP.Outside.L_meta_1516

theorem PEqualNP.Outside.L_meta_1516 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ D : (Fin 13 → Bool) → Prop,
    (∀ x y : Fin 13 → Bool, D x → (∀ v : Fin 13, x v = true → y v = true) → D y) →
    (∀ t : Fin 13, D (fun v => decide (v ∉ L t))) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin 13 → ℕ),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) →
    (∀ (t : Fin 13) (x : Fin 13 → Bool), D x →
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
    ∀ (Lam : Finset (Fin 13)) (B : Fin 13 → Fin 13 → Finset (Fin 13)),
    (∀ t ∈ Lam, ∀ p ∈ L t, B t p ∩ L t = ∅ ∧ D (fun v => decide (v = p ∨ v ∈ B t p))) →
    (∀ t ∈ Lam, ∀ t' ∈ Lam, t ≠ t' → ¬ ((∃ p ∈ L t \ L t', (B t p ∩ L t').Nonempty) ∧
      (∃ p ∈ L t' \ L t, (B t' p ∩ L t).Nonempty))) →
    ∀ I : Finset (Fin gates.length), (∀ g ∈ I, (gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.and) →
      3 * Lam.card + max (13 - Lam.card) I.card ≤ gates.length := by
  exact PEqualNP.Outside.L_meta_1516.main
