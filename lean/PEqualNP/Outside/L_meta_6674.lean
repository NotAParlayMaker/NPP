import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6674

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.GenericRejection PEqualNP.HeptadCover

private lemma getD_snoc_lt (w : List Bool) (b : Bool) (i : ℕ) (hi : i < w.length) :
    (w ++ [b]).getD i false = w.getD i false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private lemma getD_snoc_eq (w : List Bool) (b : Bool) :
    (w ++ [b]).getD w.length false = b := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl, Nat.sub_self,
    List.getElem?_cons_zero, Option.getD_some]

private lemma getD_ofFn {n : ℕ} (f : Fin n → Bool) (i : Fin n) :
    (List.ofFn f).getD i.val false = f i := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, i.isLt, ↓reduceDIte,
    Option.getD_some, Fin.eta]

private lemma getD_append_left (l₁ l₂ : List Bool) (i : ℕ) (hi : i < l₁.length) :
    (l₁ ++ l₂).getD i false = l₁.getD i false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private lemma getD_append_right (l₁ l₂ : List Bool) (i : ℕ) (hi : l₁.length ≤ i) :
    (l₁ ++ l₂).getD i false = l₂.getD (i - l₁.length) false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right hi]

private def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private lemma foldl_len (gs : List Gate) (w : List Bool) :
    (gs.foldl stepW w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => rw [List.foldl_cons, ih]; simp [stepW]; omega

private lemma foldl_keep (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepW w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp [stepW]; omega)]
    exact getD_snoc_lt w _ i hi

private def embP (n m k : ℕ) : Fin n ↪ Fin (n + (m - k)) :=
  ⟨fun p => ⟨p.val, by omega⟩, fun a b h => Fin.ext (by simpa using congrArg Fin.val h)⟩

private def embL (n m k : ℕ) (hk1 : k ≤ n) : Fin m ↪ Fin (n + (m - k)) :=
  ⟨fun l => if h : l.val < k then ⟨l.val, by omega⟩ else ⟨n + (l.val - k), by omega⟩,
   by
    intro a b h
    have hv := congrArg Fin.val h
    by_cases ha : a.val < k <;> by_cases hb : b.val < k
    · simp only [ha, hb, ↓reduceDIte] at hv
      exact Fin.ext hv
    · simp only [ha, hb, ↓reduceDIte] at hv
      omega
    · simp only [ha, hb, ↓reduceDIte] at hv
      omega
    · simp only [ha, hb, ↓reduceDIte] at hv
      exact Fin.ext (by omega)⟩

private lemma embP_val (n m k : ℕ) (p : Fin n) : (embP n m k p).val = p.val := rfl

private lemma embL_val_lt (n m k : ℕ) (hk1 : k ≤ n) (l : Fin m) (hl : l.val < k) :
    (embL n m k hk1 l).val = l.val := by
  change (if h : l.val < k then (⟨l.val, by omega⟩ : Fin (n + (m - k))) else _).val = l.val
  simp only [hl, ↓reduceDIte]

private lemma embL_val_ge (n m k : ℕ) (hk1 : k ≤ n) (l : Fin m) (hl : ¬ l.val < k) :
    (embL n m k hk1 l).val = n + (l.val - k) := by
  change (if h : l.val < k then (⟨l.val, by omega⟩ : Fin (n + (m - k))) else _).val = n + (l.val - k)
  simp only [hl, ↓reduceDIte]

private def padS (n m k : ℕ) (_hk1 : k ≤ n) (hk2 : k ≤ m) (S : Fin m → Finset (Fin n)) :
    Fin (n + (m - k)) → Finset (Fin (n + (m - k))) := fun l =>
  if h1 : l.val < k then
    (S ⟨l.val, by omega⟩).map (embP n m k)
  else if h2 : l.val < n then
    {l}
  else
    insert l ((S ⟨l.val - n + k, by omega⟩).map (embP n m k))

private lemma padS_diag {n m k : ℕ} (hk1 : k ≤ n) (hk2 : k ≤ m)
    (S : Fin m → Finset (Fin n))
    (hdiag : ∀ i : Fin k, Fin.castLE hk1 i ∈ S (Fin.castLE hk2 i))
    (i : Fin (n + (m - k))) : i ∈ padS n m k hk1 hk2 S i := by
  unfold padS
  split_ifs with h1 h2
  · rw [Finset.mem_map]
    refine ⟨⟨i.val, by omega⟩, ?_, by ext; rfl⟩
    exact hdiag ⟨i.val, h1⟩
  · exact Finset.mem_singleton_self i
  · exact Finset.mem_insert_self i _

private lemma padS_c4 {n m k : ℕ} (hk1 : k ≤ n) (hk2 : k ≤ m)
    (S : Fin m → Finset (Fin n))
    (hc4 : ∀ l₁ l₂ : Fin m, l₁ ≠ l₂ → (S l₁ ∩ S l₂).card ≤ 1)
    (l₁ l₂ : Fin (n + (m - k))) (hne : l₁ ≠ l₂) :
    (padS n m k hk1 hk2 S l₁ ∩ padS n m k hk1 hk2 S l₂).card ≤ 1 := by
  by_cases h1 : k ≤ l₁.val ∧ l₁.val < n
  · have heq : padS n m k hk1 hk2 S l₁ = {l₁} := by
      unfold padS
      rw [dite_eq_right (by omega), dite_eq_left h1.2]
    calc (padS n m k hk1 hk2 S l₁ ∩ padS n m k hk1 hk2 S l₂).card
        ≤ (padS n m k hk1 hk2 S l₁).card := Finset.card_le_card Finset.inter_subset_left
      _ = 1 := by rw [heq, Finset.card_singleton]
  · by_cases h2 : k ≤ l₂.val ∧ l₂.val < n
    · have heq : padS n m k hk1 hk2 S l₂ = {l₂} := by
        unfold padS
        rw [dite_eq_right (by omega), dite_eq_left h2.2]
      calc (padS n m k hk1 hk2 S l₁ ∩ padS n m k hk1 hk2 S l₂).card
          ≤ (padS n m k hk1 hk2 S l₂).card := Finset.card_le_card Finset.inter_subset_right
        _ = 1 := by rw [heq, Finset.card_singleton]
    · let j₁ : Fin m := if hl : l₁.val < k then ⟨l₁.val, by omega⟩ else ⟨l₁.val - n + k, by omega⟩
      let j₂ : Fin m := if hl : l₂.val < k then ⟨l₂.val, by omega⟩ else ⟨l₂.val - n + k, by omega⟩
      have hjne : j₁ ≠ j₂ := by
        intro heq
        have hv := congrArg Fin.val heq
        by_cases ha : l₁.val < k <;> by_cases hb : l₂.val < k
        · simp only [j₁, j₂, ha, hb, ↓reduceDIte] at hv
          exact hne (Fin.ext hv)
        · simp only [j₁, j₂, ha, hb, ↓reduceDIte] at hv
          omega
        · simp only [j₁, j₂, ha, hb, ↓reduceDIte] at hv
          omega
        · simp only [j₁, j₂, ha, hb, ↓reduceDIte] at hv
          exact hne (Fin.ext (by omega))
      have hsub : padS n m k hk1 hk2 S l₁ ∩ padS n m k hk1 hk2 S l₂ ⊆
          (S j₁ ∩ S j₂).map (embP n m k) := by
        intro p hp
        obtain ⟨hp1, hp2⟩ := Finset.mem_inter.1 hp
        have hmem1 : p ∈ (S j₁).map (embP n m k) ∨ p = l₁ := by
          unfold padS at hp1
          dsimp only [j₁]
          split_ifs at hp1 ⊢ with ha ha'
          · exact Or.inl hp1
          · omega
          · exact (Finset.mem_insert.1 hp1).symm
        have hmem2 : p ∈ (S j₂).map (embP n m k) ∨ p = l₂ := by
          unfold padS at hp2
          dsimp only [j₂]
          split_ifs at hp2 ⊢ with hb hb'
          · exact Or.inl hp2
          · omega
          · exact (Finset.mem_insert.1 hp2).symm
        have hlt1 : p ∈ (S j₁).map (embP n m k) := by
          rcases hmem1 with hm | hp_eq
          · exact hm
          · rcases hmem2 with hm2 | hp_eq2
            · obtain ⟨q, _, hq⟩ := Finset.mem_map.1 hm2
              have hpn : p.val < n := by
                have hvq := congrArg Fin.val hq
                rw [embP_val] at hvq
                omega
              have hl1k : l₁.val < k := by rw [← hp_eq] at h1 ⊢; omega
              unfold padS at hp1
              rw [dite_eq_left hl1k] at hp1
              simpa [j₁, hl1k] using hp1
            · exact absurd (hp_eq.symm.trans hp_eq2) hne
        have hlt2 : p ∈ (S j₂).map (embP n m k) := by
          rcases hmem2 with hm | hp_eq
          · exact hm
          · obtain ⟨q, _, hq⟩ := Finset.mem_map.1 hlt1
            have hpn : p.val < n := by
              have hvq := congrArg Fin.val hq
              rw [embP_val] at hvq
              omega
            have hl2k : l₂.val < k := by rw [← hp_eq] at h2 ⊢; omega
            unfold padS at hp2
            rw [dite_eq_left hl2k] at hp2
            simpa [j₂, hl2k] using hp2
        obtain ⟨q₁, hq₁, hqq₁⟩ := Finset.mem_map.1 hlt1
        obtain ⟨q₂, hq₂, hqq₂⟩ := Finset.mem_map.1 hlt2
        have hqe : q₁ = q₂ := (embP n m k).injective (hqq₁.trans hqq₂.symm)
        subst hqe
        exact Finset.mem_map.2 ⟨q₁, Finset.mem_inter.2 ⟨hq₁, hq₂⟩, hqq₁⟩
      calc (padS n m k hk1 hk2 S l₁ ∩ padS n m k hk1 hk2 S l₂).card
          ≤ ((S j₁ ∩ S j₂).map (embP n m k)).card := Finset.card_le_card hsub
        _ = (S j₁ ∩ S j₂).card := Finset.card_map _
        _ ≤ 1 := hc4 j₁ j₂ hjne

private lemma padS_incidences_card {n m k : ℕ} (hk1 : k ≤ n) (hk2 : k ≤ m)
    (S : Fin m → Finset (Fin n))
    (hdiag : ∀ i : Fin k, Fin.castLE hk1 i ∈ S (Fin.castLE hk2 i)) :
    (incidences (padS n m k hk1 hk2 S)).card =
      (incidences S).card + ((n + (m - k)) - k) := by
  let N := n + (m - k)
  let embPL : (Fin n × Fin m) ↪ (Fin N × Fin N) :=
    ⟨fun pl => (embP n m k pl.1, embL n m k hk1 pl.2), fun a b h => by
      have h1 := (embP n m k).injective (congrArg Prod.fst h)
      have h2 := (embL n m k hk1).injective (congrArg Prod.snd h)
      exact Prod.ext h1 h2⟩
  let oldSet : Finset (Fin N × Fin N) := (incidences S).map embPL
  let diagEmb : Fin N ↪ (Fin N × Fin N) := ⟨fun i => (i, i), fun a b h => congrArg Prod.fst h⟩
  let newSet : Finset (Fin N × Fin N) :=
    (Finset.univ.filter fun i : Fin N => k ≤ i.val).map diagEmb
  have hdisj : Disjoint oldSet newSet := by
    rw [Finset.disjoint_left]
    intro pl h1 h2
    obtain ⟨⟨p, l⟩, _, rfl⟩ := Finset.mem_map.1 h1
    obtain ⟨i, hi, heq⟩ := Finset.mem_map.1 h2
    have hki : k ≤ i.val := (Finset.mem_filter.1 hi).2
    have hp_eq : (embP n m k p).val = i.val := congrArg (fun x => x.1.val) heq.symm
    have hl_eq : (embL n m k hk1 l).val = i.val := congrArg (fun x => x.2.val) heq.symm
    rw [embP_val] at hp_eq
    by_cases hl : l.val < k
    · rw [embL_val_lt n m k hk1 l hl] at hl_eq
      omega
    · rw [embL_val_ge n m k hk1 l hl] at hl_eq
      omega
  have hunion : incidences (padS n m k hk1 hk2 S) = oldSet ∪ newSet := by
    ext ⟨p', l'⟩
    simp only [incidences, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · intro hmem
      unfold padS at hmem
      split_ifs at hmem with h1 h2
      · left
        obtain ⟨p, hp, rfl⟩ := Finset.mem_map.1 hmem
        refine Finset.mem_map.2 ⟨(p, ⟨l'.val, by omega⟩), Finset.mem_filter.2 ⟨Finset.mem_univ _, hp⟩, ?_⟩
        refine Prod.ext rfl (Fin.ext ?_)
        exact embL_val_lt n m k hk1 ⟨l'.val, by omega⟩ h1
      · right
        have hp_eq : p' = l' := Finset.mem_singleton.1 hmem
        subst hp_eq
        exact Finset.mem_map.2 ⟨p', Finset.mem_filter.2 ⟨Finset.mem_univ _, by omega⟩, rfl⟩
      · rcases Finset.mem_insert.1 hmem with rfl | hm
        · right
          exact Finset.mem_map.2 ⟨p', Finset.mem_filter.2 ⟨Finset.mem_univ _, by omega⟩, rfl⟩
        · left
          obtain ⟨p, hp, rfl⟩ := Finset.mem_map.1 hm
          refine Finset.mem_map.2 ⟨(p, ⟨l'.val - n + k, by omega⟩),
            Finset.mem_filter.2 ⟨Finset.mem_univ _, hp⟩, ?_⟩
          refine Prod.ext rfl (Fin.ext ?_)
          change (embL n m k hk1 ⟨l'.val - n + k, by omega⟩).val = l'.val
          rw [embL_val_ge n m k hk1 ⟨l'.val - n + k, by omega⟩ (by dsimp; omega)]
          dsimp; omega
    · rintro (ho | hn)
      · obtain ⟨⟨p, l⟩, hpl, heq⟩ := Finset.mem_map.1 ho
        have hpS : p ∈ S l := (Finset.mem_filter.1 hpl).2
        have hp' : p' = embP n m k p := congrArg Prod.fst heq.symm
        have hl' : l' = embL n m k hk1 l := congrArg Prod.snd heq.symm
        rw [hp', hl']
        unfold padS
        by_cases hl : l.val < k
        · have hlt : (embL n m k hk1 l).val < k := by rw [embL_val_lt n m k hk1 l hl]; exact hl
          rw [dite_eq_left hlt]
          refine Finset.mem_map.2 ⟨p, ?_, rfl⟩
          have hidx : (⟨(embL n m k hk1 l).val, by omega⟩ : Fin m) = l :=
            Fin.ext (embL_val_lt n m k hk1 l hl)
          rw [hidx]; exact hpS
        · have hge : (embL n m k hk1 l).val = n + (l.val - k) := embL_val_ge n m k hk1 l hl
          rw [dite_eq_right (by omega), dite_eq_right (by omega)]
          apply Finset.mem_insert_of_mem
          refine Finset.mem_map.2 ⟨p, ?_, rfl⟩
          have hidx : (⟨(embL n m k hk1 l).val - n + k, by omega⟩ : Fin m) = l :=
            Fin.ext (by dsimp; omega)
          rw [hidx]; exact hpS
      · obtain ⟨i, _, heq⟩ := Finset.mem_map.1 hn
        have hp' : p' = i := congrArg Prod.fst heq.symm
        have hl' : l' = i := congrArg Prod.snd heq.symm
        rw [hp', hl']
        exact padS_diag hk1 hk2 S hdiag i
  have hnew_card : newSet.card = N - k := by
    rw [Finset.card_map]
    have hbij : (Finset.univ.filter fun i : Fin N => k ≤ i.val).card = (Finset.Ico k N).card := by
      refine Finset.card_bij (fun i _ => i.val) ?_ ?_ ?_
      · intro i hi
        have hki : k ≤ i.val := (Finset.mem_filter.1 hi).2
        exact Finset.mem_Ico.2 ⟨hki, i.isLt⟩
      · intro a _ b _ h; exact Fin.ext h
      · intro j hj
        obtain ⟨hkj, hjN⟩ := Finset.mem_Ico.1 hj
        exact ⟨⟨j, hjN⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, hkj⟩, rfl⟩
    rw [hbij, Nat.card_Ico]
  rw [hunion, Finset.card_union_of_disjoint hdisj, Finset.card_map, hnew_card]

private def mapWire (n m k : ℕ) (w : ℕ) : ℕ :=
  let N := n + (m - k)
  if w < n then w
  else if w < n + m then
    let j := w - n
    if j < k then N + j else N + n + (j - k)
  else (N + N) + (w - (n + m))

private lemma mapWire_lt {n m k : ℕ} (hk1 : k ≤ n) (hk2 : k ≤ m) {r w : ℕ} (hw : w < n + m + r) :
    mapWire n m k w < (n + (m - k)) + (n + (m - k)) + r := by
  unfold mapWire
  dsimp only
  split_ifs <;> omega

private def curWire (N baseSz cur0 : ℕ) : ℕ → ℕ
  | 0 => cur0
  | t + 1 => (N + N) + baseSz + 2 * t + 1

private lemma curWire_lt {N baseSz cur0 : ℕ} (h0 : cur0 < (N + N) + baseSz) (t : ℕ) :
    curWire N baseSz cur0 t < (N + N) + baseSz + 2 * t := by
  cases t with
  | zero => simpa [curWire] using h0
  | succ t => simp [curWire]; omega

private def extraGates (N k baseSz cur0 : ℕ) : ℕ → List Gate
  | 0 => []
  | t + 1 => extraGates N k baseSz cur0 t ++
      [Gate.mk GateOp.and [k + t, N + (k + t)],
       Gate.mk GateOp.or [curWire N baseSz cur0 t, (N + N) + baseSz + 2 * t]]

private lemma extraGates_len (N k baseSz cur0 t : ℕ) :
    (extraGates N k baseSz cur0 t).length = 2 * t := by
  induction t with
  | zero => simp [extraGates]
  | succ t ih => simp [extraGates, ih]; omega

private lemma extraGates_ao2 {N k baseSz cur0 : ℕ} (h0 : cur0 < (N + N) + baseSz)
    (t : ℕ) (ht : k + t ≤ N) :
    (∀ g ∈ extraGates N k baseSz cur0 t, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∧
    (∀ j (hj : j < (extraGates N k baseSz cur0 t).length),
      ∀ w ∈ ((extraGates N k baseSz cur0 t)[j]).inputs, w < (N + N) + baseSz + j) := by
  induction t with
  | zero => simp [extraGates]
  | succ t ih =>
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    constructor
    · intro g hg
      simp only [extraGates, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with hg | rfl | rfl
      · exact ih1 g hg
      · exact ⟨Or.inl rfl, rfl⟩
      · exact ⟨Or.inr rfl, rfl⟩
    · intro j hj w hw
      have hlen : (extraGates N k baseSz cur0 t).length = 2 * t := extraGates_len N k baseSz cur0 t
      by_cases hjt : j < 2 * t
      · have hidx : (extraGates N k baseSz cur0 (t + 1))[j] =
            (extraGates N k baseSz cur0 t)[j]'(by omega) := by
          simp only [extraGates]
          exact List.getElem_append_left (by omega)
        rw [hidx] at hw
        exact ih2 j (by omega) w hw
      · have hjeq : j = 2 * t ∨ j = 2 * t + 1 := by
          rw [extraGates_len] at hj; omega
        rcases hjeq with rfl | rfl
        · have hidx : (extraGates N k baseSz cur0 (t + 1))[2 * t] =
              Gate.mk GateOp.and [k + t, N + (k + t)] := by
            simp only [extraGates]
            rw [List.getElem_append_right (by omega)]
            simp [hlen]
          rw [hidx] at hw
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
          rcases hw with rfl | rfl <;> omega
        · have hidx : (extraGates N k baseSz cur0 (t + 1))[2 * t + 1] =
              Gate.mk GateOp.or [curWire N baseSz cur0 t, (N + N) + baseSz + 2 * t] := by
            simp only [extraGates]
            rw [List.getElem_append_right (by omega)]
            simp [hlen]
          rw [hidx] at hw
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
          rcases hw with rfl | rfl
          · have := curWire_lt h0 t; omega
          · omega

private lemma base_sim {n m k : ℕ} (hk1 : k ≤ n) (hk2 : k ≤ m)
    (gs : List Gate) (wC wP : List Bool)
    (hreads : ∀ r (hr : r < gs.length), ∀ i ∈ gs[r].inputs, i < wC.length + r)
    (hlenC : n + m ≤ wC.length)
    (hlenP : wP.length = (n + (m - k)) + (n + (m - k)) + (wC.length - (n + m)))
    (hmatch : ∀ w < wC.length, wP.getD (mapWire n m k w) false = wC.getD w false) :
    let gsP := gs.map (fun g => Gate.mk g.op (g.inputs.map (mapWire n m k)))
    (gsP.foldl stepW wP).length = (n + (m - k)) + (n + (m - k)) + ((gs.foldl stepW wC).length - (n + m)) ∧
    ∀ w < (gs.foldl stepW wC).length,
      (gsP.foldl stepW wP).getD (mapWire n m k w) false = (gs.foldl stepW wC).getD w false := by
  induction gs generalizing wC wP with
  | nil => exact ⟨hlenP, hmatch⟩
  | cons g gs ih =>
    simp only [List.map_cons, List.foldl_cons]
    have hg_reads : ∀ i ∈ g.inputs, i < wC.length := by
      intro i hi
      have := hreads 0 (by simp) i (by simpa using hi)
      omega
    have hvg : (Gate.mk g.op (g.inputs.map (mapWire n m k))).op.eval
        ((g.inputs.map (mapWire n m k)).map fun i => wP.getD i false) =
        g.op.eval (g.inputs.map fun i => wC.getD i false) := by
      simp only [List.map_map]
      congr 1
      refine List.map_congr_left fun i hi => ?_
      simp only [Function.comp_apply]
      exact hmatch i (hg_reads i hi)
    have hstepP : stepW wP (Gate.mk g.op (g.inputs.map (mapWire n m k))) =
        wP ++ [g.op.eval (g.inputs.map fun i => wC.getD i false)] := by
      dsimp only [stepW]
      rw [hvg]
    rw [hstepP]
    set b := g.op.eval (g.inputs.map fun i => wC.getD i false)
    have hres := ih (wC ++ [b]) (wP ++ [b])
      (fun r hr i hi => by
        have := hreads (r + 1) (by simp; omega) i (by simpa using hi)
        simp; omega)
      (by simp; omega)
      (by simp [hlenP]; omega)
      (fun w hw => by
        simp only [List.length_append, List.length_singleton] at hw
        by_cases hlt : w < wC.length
        · have hmlt : mapWire n m k w < wP.length := by
            have := mapWire_lt hk1 hk2 (r := wC.length - (n + m)) (w := w) (by omega)
            omega
          rw [getD_snoc_lt wP b _ hmlt, getD_snoc_lt wC b _ hlt]
          exact hmatch w hlt
        · have heq : w = wC.length := by omega
          subst heq
          have hmeq : mapWire n m k wC.length = wP.length := by
            unfold mapWire
            dsimp only
            rw [ite_eq_right (by omega), ite_eq_right (by omega)]
            omega
          rw [hmeq, getD_snoc_eq, getD_snoc_eq])
    exact hres

private lemma extra_sim {N k baseSz cur0 : ℕ} (h0 : cur0 < (N + N) + baseSz)
    (X' Y' : Finset (Fin N)) (w : List Bool)
    (hlen : w.length = (N + N) + baseSz)
    (hX : ∀ i : Fin N, w.getD i.val false = decide (i ∈ X'))
    (hY : ∀ i : Fin N, w.getD (N + i.val) false = decide (i ∈ Y'))
    (t : ℕ) (ht : k + t ≤ N) :
    ((extraGates N k baseSz cur0 t).foldl stepW w).getD (curWire N baseSz cur0 t) false =
      (w.getD cur0 false ||
        decide (∃ i : Fin N, k ≤ i.val ∧ i.val < k + t ∧ i ∈ X' ∧ i ∈ Y')) := by
  induction t with
  | zero =>
    simp [extraGates, curWire]
    intro i h1 h2
    omega
  | succ t ih =>
    have iht := ih (by omega)
    simp only [extraGates, List.foldl_append, List.foldl_cons, List.foldl_nil]
    set w1 := (extraGates N k baseSz cur0 t).foldl stepW w
    have hw1_len : w1.length = (N + N) + baseSz + 2 * t := by
      dsimp only [w1]
      rw [foldl_len, hlen, extraGates_len]
    let it : Fin N := ⟨k + t, by omega⟩
    have hlt_x : it.val < w.length := by omega
    have hlt_y : N + it.val < w.length := by omega
    have hw1_x : w1.getD (k + t) false = decide (it ∈ X') := by
      dsimp only [w1]
      rw [foldl_keep _ _ _ hlt_x]
      exact hX it
    have hw1_y : w1.getD (N + (k + t)) false = decide (it ∈ Y') := by
      dsimp only [w1]
      rw [foldl_keep _ _ _ hlt_y]
      exact hY it
    have hand_val : stepW w1 (Gate.mk GateOp.and [k + t, N + (k + t)]) =
        w1 ++ [decide (it ∈ X') && decide (it ∈ Y')] := by
      dsimp only [stepW]
      congr 1
      change [((w1.getD (k + t) false && (w1.getD (N + (k + t)) false && true)))] = _
      rw [hw1_x, hw1_y, Bool.and_true]
    rw [hand_val]
    set ba := decide (it ∈ X') && decide (it ∈ Y')
    have hcur_lt : curWire N baseSz cur0 t < w1.length := by
      rw [hw1_len]; exact curWire_lt h0 t
    have hor_val : stepW (w1 ++ [ba])
        (Gate.mk GateOp.or [curWire N baseSz cur0 t, (N + N) + baseSz + 2 * t]) =
        (w1 ++ [ba]) ++ [w1.getD (curWire N baseSz cur0 t) false || ba] := by
      dsimp only [stepW]
      congr 1
      change [((w1 ++ [ba]).getD (curWire N baseSz cur0 t) false ||
        ((w1 ++ [ba]).getD ((N + N) + baseSz + 2 * t) false || false))] = _
      rw [getD_snoc_lt w1 ba _ hcur_lt, ← hw1_len, getD_snoc_eq, Bool.or_false]
    rw [hor_val]
    have hlen2 : (w1 ++ [ba]).length = curWire N baseSz cur0 (t + 1) := by
      simp [curWire, hw1_len]
    rw [← hlen2, getD_snoc_eq, iht, Bool.or_assoc]
    congr 1
    apply Bool.eq_iff_iff.2
    simp only [ba, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro (⟨i, hki, hilt, hiX, hiY⟩ | ⟨hXit, hYit⟩)
      · exact ⟨i, hki, by omega, hiX, hiY⟩
      · exact ⟨it, by dsimp [it]; omega, by dsimp [it]; omega, hXit, hYit⟩
    · rintro ⟨i, hki, hilt, hiX, hiY⟩
      by_cases heq : i.val = k + t
      · right
        have hi_eq : i = it := Fin.ext heq
        subst hi_eq
        exact ⟨hiX, hiY⟩
      · left
        exact ⟨i, hki, by omega, hiX, hiY⟩

end PEqualNP.Outside.L_meta_6674

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.GenericRejection PEqualNP.HeptadCover

theorem PEqualNP.Outside.L_meta_6674 : ∀ (x1 x2 x3 : ℕ) (x4 : Fin x2 → Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : x3 ≤ x1) (x7 : x3 ≤ x2),   (∀ (x8 : Fin x3), Fin.castLE x6 x8 ∈ x4 (Fin.castLE x7 x8)) →     (∀ (x9 x10 : Fin x2), x9 ≠ x10 → (x4 x9 ∩ x4 x10).card ≤ (1 : ℕ)) →       PEqualNP.TopForm.IsAO2 (x1 + x2) x5 →         x5.output < x1 + x2 + x5.size →           PEqualNP.GenericRejection.ComputesIncidence x4 x5 →             have x13 : ℕ := x1 + (x2 - x3);             ∃ (x14 : Fin x13 → Finset (Fin x13)) (x15 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x16 : Fin x13), x16 ∈ x14 x16) ∧ (∀ (x16 x17 : Fin x13), x16 ≠ x17 → (x14 x16 ∩ x14 x17).card ≤ (1 : ℕ)) ∧ PEqualNP.TopForm.IsAO2 (x13 + x13) x15 ∧ PEqualNP.GenericRejection.ComputesIncidence x14 x15 ∧ (PEqualNP.HeptadCover.incidences x14).card = (PEqualNP.HeptadCover.incidences x4).card + (x13 - x3) ∧ x15.size = x5.size + (2 : ℕ) * (x13 - x3) := by
  intro n m k S C hk1 hk2 hdiag hc4 hAO hout hcomp N
  have hN_def : N = n + (m - k) := rfl
  let S' := PEqualNP.Outside.L_meta_6674.padS n m k hk1 hk2 S
  let baseGates : List Gate :=
    C.gates.map (fun g => Gate.mk g.op (g.inputs.map (PEqualNP.Outside.L_meta_6674.mapWire n m k)))
  let cur0 : ℕ := PEqualNP.Outside.L_meta_6674.mapWire n m k C.output
  let exGates : List Gate :=
    PEqualNP.Outside.L_meta_6674.extraGates N k C.gates.length cur0 (N - k)
  let C' : Circuit := ⟨baseGates ++ exGates, PEqualNP.Outside.L_meta_6674.curWire N C.gates.length cur0 (N - k)⟩
  have hcur0_lt : cur0 < (N + N) + C.gates.length :=
    PEqualNP.Outside.L_meta_6674.mapWire_lt hk1 hk2 hout
  have hex_ao2 := PEqualNP.Outside.L_meta_6674.extraGates_ao2 (k := k) hcur0_lt (N - k) (by omega)
  have hC'_sz : C'.size = C.size + 2 * (N - k) := by
    change (baseGates ++ exGates).length = C.gates.length + 2 * (N - k)
    rw [List.length_append, List.length_map, PEqualNP.Outside.L_meta_6674.extraGates_len]
  have hC'_AO : IsAO2 (N + N) C' := by
    refine ⟨?_, ?_, ?_⟩
    · intro g hg
      simp only [C', List.mem_append, baseGates, List.mem_map] at hg
      rcases hg with ⟨g0, hg0, rfl⟩ | hg
      · exact hAO.1 g0 hg0
      · exact (hex_ao2.1 g hg).1
    · intro j hj w hw
      have hblen : baseGates.length = C.gates.length := List.length_map _
      by_cases hjb : j < C.gates.length
      · have hg_at : gateAt C' j = Gate.mk (gateAt C j).op
            ((gateAt C j).inputs.map (PEqualNP.Outside.L_meta_6674.mapWire n m k)) := by
          simp only [gateAt, C']
          rw [List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ hjb]
          rw [List.getElem_append_left (by omega)]
          simp [baseGates]
        rw [hg_at] at hw
        obtain ⟨w0, hw0, rfl⟩ := List.mem_map.1 hw
        exact PEqualNP.Outside.L_meta_6674.mapWire_lt hk1 hk2 (hAO.2.1 j hjb w0 hw0)
      · have hjex : j - C.gates.length < exGates.length := by
          simp only [C', List.length_append, hblen] at hj; omega
        have hg_at : gateAt C' j = exGates[j - C.gates.length] := by
          simp only [gateAt, C']
          rw [List.getD_eq_getElem _ _ hj, List.getElem_append_right (by omega)]
          simp [hblen]
        rw [hg_at] at hw
        have := hex_ao2.2 (j - C.gates.length) hjex w hw
        omega
    · intro g hg
      simp only [C', List.mem_append, baseGates, List.mem_map] at hg
      rcases hg with ⟨g0, hg0, rfl⟩ | hg
      · simp [hAO.2.2 g0 hg0]
      · exact (hex_ao2.1 g hg).2
  have hC'_comp : ComputesIncidence S' C' := by
    intro X' Y'
    let X : Finset (Fin n) := Finset.univ.filter fun p => PEqualNP.Outside.L_meta_6674.embP n m k p ∈ X'
    let Y : Finset (Fin m) := Finset.univ.filter fun l => PEqualNP.Outside.L_meta_6674.embL n m k hk1 l ∈ Y'
    have hbase_reads : ∀ r (hr : r < C.gates.length), ∀ i ∈ C.gates[r].inputs,
        i < (incidenceInput X Y).length + r := by
      intro r hr i hi
      have hlen_in : (incidenceInput X Y).length = n + m := by simp [incidenceInput]
      rw [hlen_in]
      have hga : gateAt C r = C.gates[r] := by unfold gateAt; exact List.getD_eq_getElem _ _ hr
      exact hAO.2.1 r hr i (by rw [hga]; exact hi)
    have hin_match : ∀ w < (incidenceInput X Y).length,
        (incidenceInput X' Y').getD (PEqualNP.Outside.L_meta_6674.mapWire n m k w) false =
          (incidenceInput X Y).getD w false := by
      intro w hw
      simp only [incidenceInput, List.length_append, List.length_ofFn] at hw
      by_cases hwn : w < n
      · have hmw : PEqualNP.Outside.L_meta_6674.mapWire n m k w = w := by
          unfold PEqualNP.Outside.L_meta_6674.mapWire
          dsimp only
          exact ite_eq_left hwn
        rw [hmw]
        simp only [incidenceInput]
        rw [PEqualNP.Outside.L_meta_6674.getD_append_left _ _ w (by simp; omega),
            PEqualNP.Outside.L_meta_6674.getD_append_left _ _ w (by simp; omega)]
        have h1 := PEqualNP.Outside.L_meta_6674.getD_ofFn (fun p : Fin N => decide (p ∈ X')) ⟨w, by omega⟩
        have h2 := PEqualNP.Outside.L_meta_6674.getD_ofFn (fun p : Fin n => decide (p ∈ X)) ⟨w, hwn⟩
        rw [h1, h2]
        simp only [X, Finset.mem_filter, Finset.mem_univ, true_and]
        rfl
      · let l : Fin m := ⟨w - n, by omega⟩
        have hmw : PEqualNP.Outside.L_meta_6674.mapWire n m k w =
            N + (PEqualNP.Outside.L_meta_6674.embL n m k hk1 l).val := by
          unfold PEqualNP.Outside.L_meta_6674.mapWire
          dsimp only
          rw [ite_eq_right hwn, ite_eq_left hw]
          by_cases hlk : w - n < k
          · rw [ite_eq_left hlk, PEqualNP.Outside.L_meta_6674.embL_val_lt n m k hk1 l hlk]
          · rw [ite_eq_right hlk, PEqualNP.Outside.L_meta_6674.embL_val_ge n m k hk1 l hlk]
            dsimp [l]; omega
        rw [hmw]
        simp only [incidenceInput]
        have hl1 : (List.ofFn fun p : Fin N => decide (p ∈ X')).length = N := by simp
        have hl2 : (List.ofFn fun p : Fin n => decide (p ∈ X)).length = n := by simp
        rw [PEqualNP.Outside.L_meta_6674.getD_append_right _ _ _ (by rw [hl1]; omega),
            hl1, Nat.add_sub_cancel_left,
            PEqualNP.Outside.L_meta_6674.getD_append_right _ _ _ (by rw [hl2]; omega),
            hl2]
        have h1 := PEqualNP.Outside.L_meta_6674.getD_ofFn (fun j : Fin N => decide (j ∈ Y'))
          (PEqualNP.Outside.L_meta_6674.embL n m k hk1 l)
        have h2 := PEqualNP.Outside.L_meta_6674.getD_ofFn (fun j : Fin m => decide (j ∈ Y)) l
        rw [h1, h2]
        simp [Y]
    have hsim := PEqualNP.Outside.L_meta_6674.base_sim hk1 hk2 C.gates
      (incidenceInput X Y) (incidenceInput X' Y') hbase_reads
      (by simp [incidenceInput]) (by simp [incidenceInput]) hin_match
    set wBase := baseGates.foldl PEqualNP.Outside.L_meta_6674.stepW (incidenceInput X' Y')
    have hwBase_len : wBase.length = (N + N) + C.gates.length := by
      dsimp only [wBase]
      rw [PEqualNP.Outside.L_meta_6674.foldl_len]
      simp [baseGates, incidenceInput, hN_def]
    have hwBase_cur0 : wBase.getD cur0 false = incidenceFun S X Y := by
      have h1 := hsim.2 C.output (by
        rw [PEqualNP.Outside.L_meta_6674.foldl_len]
        simp only [incidenceInput, List.length_append, List.length_ofFn]
        exact hout)
      rw [h1]
      exact hcomp X Y
    have hwBase_X : ∀ i : Fin N, wBase.getD i.val false = decide (i ∈ X') := by
      intro i
      dsimp only [wBase]
      rw [PEqualNP.Outside.L_meta_6674.foldl_keep _ _ _ (by simp [incidenceInput]; omega)]
      simp only [incidenceInput]
      rw [PEqualNP.Outside.L_meta_6674.getD_append_left _ _ i.val (by simp; omega)]
      exact PEqualNP.Outside.L_meta_6674.getD_ofFn (fun p : Fin N => decide (p ∈ X')) i
    have hwBase_Y : ∀ i : Fin N, wBase.getD (N + i.val) false = decide (i ∈ Y') := by
      intro i
      dsimp only [wBase]
      rw [PEqualNP.Outside.L_meta_6674.foldl_keep _ _ _ (by simp [incidenceInput]; omega)]
      simp only [incidenceInput]
      have hl1 : (List.ofFn fun p : Fin N => decide (p ∈ X')).length = N := by simp
      rw [PEqualNP.Outside.L_meta_6674.getD_append_right _ _ _ (by rw [hl1]; omega),
          hl1, Nat.add_sub_cancel_left]
      exact PEqualNP.Outside.L_meta_6674.getD_ofFn (fun l : Fin N => decide (l ∈ Y')) i
    have hex := PEqualNP.Outside.L_meta_6674.extra_sim (k := k) hcur0_lt X' Y' wBase hwBase_len
      hwBase_X hwBase_Y (N - k) (by omega)
    change ((baseGates ++ exGates).foldl PEqualNP.Outside.L_meta_6674.stepW (incidenceInput X' Y')).getD
      (PEqualNP.Outside.L_meta_6674.curWire N C.gates.length cur0 (N - k)) false =
      incidenceFun S' X' Y'
    rw [List.foldl_append]
    change (exGates.foldl PEqualNP.Outside.L_meta_6674.stepW wBase).getD
      (PEqualNP.Outside.L_meta_6674.curWire N C.gates.length cur0 (N - k)) false =
      incidenceFun S' X' Y'
    rw [hex, hwBase_cur0]
    apply Bool.eq_iff_iff.2
    simp only [incidenceFun, Bool.or_eq_true, decide_eq_true_eq]
    constructor
    · rintro (⟨p, hpX, l, hlY, hpS⟩ | ⟨i, hki, _, hiX, hiY⟩)
      · have hpX' : PEqualNP.Outside.L_meta_6674.embP n m k p ∈ X' := (Finset.mem_filter.1 hpX).2
        have hlY' : PEqualNP.Outside.L_meta_6674.embL n m k hk1 l ∈ Y' := (Finset.mem_filter.1 hlY).2
        refine ⟨PEqualNP.Outside.L_meta_6674.embP n m k p, hpX',
                PEqualNP.Outside.L_meta_6674.embL n m k hk1 l, hlY', ?_⟩
        dsimp only [S', PEqualNP.Outside.L_meta_6674.padS]
        by_cases hl : l.val < k
        · have hlt : (PEqualNP.Outside.L_meta_6674.embL n m k hk1 l).val < k := by
            rw [PEqualNP.Outside.L_meta_6674.embL_val_lt n m k hk1 l hl]; exact hl
          rw [dite_eq_left hlt]
          refine Finset.mem_map.2 ⟨p, ?_, rfl⟩
          have hidx : (⟨(PEqualNP.Outside.L_meta_6674.embL n m k hk1 l).val, by omega⟩ : Fin m) = l :=
            Fin.ext (PEqualNP.Outside.L_meta_6674.embL_val_lt n m k hk1 l hl)
          rw [hidx]; exact hpS
        · have hge : (PEqualNP.Outside.L_meta_6674.embL n m k hk1 l).val = n + (l.val - k) :=
            PEqualNP.Outside.L_meta_6674.embL_val_ge n m k hk1 l hl
          rw [dite_eq_right (by omega), dite_eq_right (by omega)]
          apply Finset.mem_insert_of_mem
          refine Finset.mem_map.2 ⟨p, ?_, rfl⟩
          have hidx : (⟨(PEqualNP.Outside.L_meta_6674.embL n m k hk1 l).val - n + k, by omega⟩ : Fin m) = l :=
            Fin.ext (by dsimp; omega)
          rw [hidx]; exact hpS
      · exact ⟨i, hiX, i, hiY, PEqualNP.Outside.L_meta_6674.padS_diag hk1 hk2 S hdiag i⟩
    · rintro ⟨p', hpX', l', hlY', hpS'⟩
      dsimp only [S', PEqualNP.Outside.L_meta_6674.padS] at hpS'
      split_ifs at hpS' with h1 h2
      · left
        obtain ⟨p, hpS, rfl⟩ := Finset.mem_map.1 hpS'
        let l : Fin m := ⟨l'.val, by omega⟩
        have hl_eq : PEqualNP.Outside.L_meta_6674.embL n m k hk1 l = l' :=
          Fin.ext (PEqualNP.Outside.L_meta_6674.embL_val_lt n m k hk1 l h1)
        exact ⟨p, Finset.mem_filter.2 ⟨Finset.mem_univ _, hpX'⟩,
               l, Finset.mem_filter.2 ⟨Finset.mem_univ _, hl_eq.symm ▸ hlY'⟩, hpS⟩
      · right
        have hpl : p' = l' := Finset.mem_singleton.1 hpS'
        subst hpl
        exact ⟨p', by omega, by omega, hpX', hlY'⟩
      · rcases Finset.mem_insert.1 hpS' with rfl | hm
        · right
          exact ⟨p', by omega, by omega, hpX', hlY'⟩
        · left
          obtain ⟨p, hpS, rfl⟩ := Finset.mem_map.1 hm
          let l : Fin m := ⟨l'.val - n + k, by omega⟩
          have hl_eq : PEqualNP.Outside.L_meta_6674.embL n m k hk1 l = l' := by
            apply Fin.ext
            rw [PEqualNP.Outside.L_meta_6674.embL_val_ge n m k hk1 l (by dsimp [l]; omega)]
            dsimp [l]; omega
          exact ⟨p, Finset.mem_filter.2 ⟨Finset.mem_univ _, hpX'⟩,
                 l, Finset.mem_filter.2 ⟨Finset.mem_univ _, hl_eq.symm ▸ hlY'⟩, hpS⟩
  exact ⟨S', C',
    PEqualNP.Outside.L_meta_6674.padS_diag hk1 hk2 S hdiag,
    PEqualNP.Outside.L_meta_6674.padS_c4 hk1 hk2 S hc4,
    hC'_AO, hC'_comp,
    PEqualNP.Outside.L_meta_6674.padS_incidences_card hk1 hk2 S hdiag,
    hC'_sz⟩
