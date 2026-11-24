import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1619
open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem eval_eq (gs : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.eval ⟨gs, o⟩ x = (wf gs x).getD o false := rfl

theorem wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
  simp [wf, List.foldl_append]

theorem wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i (by simp; omega)
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem wf_prefix (pre post : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length + pre.length) :
    (wf (pre ++ post) w).getD i false = (wf pre w).getD i false := by
  have : wf (pre ++ post) w = wf post (wf pre w) := by simp [wf, List.foldl_append]
  rw [this]
  exact wf_keep post _ i (by rw [wf_len]; exact hi)

theorem getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega


theorem wire_take (gates : List Gate) (X : List Bool) (k i : ℕ) (hi : i < X.length + k)
    (hk : k ≤ gates.length) :
    (wf gates X).getD i false = (wf (gates.take k) X).getD i false := by
  conv_lhs => rw [← List.take_append_drop k gates]
  exact wf_prefix _ _ _ _ (by rw [List.length_take, Nat.min_eq_left hk]; exact hi)

theorem gate_val (gates : List Gate) (X : List Bool) (k : ℕ) (hk : k < gates.length) :
    (wf gates X).getD (X.length + k) false
      = gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false) := by
  rw [wire_take gates X (k + 1) _ (by omega) hk, List.take_succ_eq_append_getElem hk, wf_snoc]
  have := getD_snoc_eq (wf (gates.take k) X)
    (gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false))
  rw [wf_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)] at this
  exact this

def val (gates : List Gate) {n : ℕ} (w : ℕ) (x : Fin n → Bool) : Bool :=
  (wf gates (List.ofFn x)).getD w false

theorem iv_eq (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k ≤ gates.length)
    (i : ℕ) : (wf (gates.take k) (List.ofFn x)).getD i false = true ↔
      i < n + k ∧ val gates i x = true := by
  by_cases hi : i < n + k
  · rw [val, wire_take gates (List.ofFn x) k i (by simpa using hi) hk]
    simp [hi]
  · rw [List.getD_eq_default _ _ (by rw [wf_len, List.length_take, Nat.min_eq_left hk]; simp; omega)]
    simp [hi]

theorem val_and (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gates.length)
    (hop : gates[k].op = GateOp.and) :
    val gates (n + k) x = true ↔ ∀ i ∈ gates[k].inputs, i < n + k ∧ val gates i x = true := by
  have := gate_val gates (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
  constructor
  · intro h i hi; exact (iv_eq gates x k (Nat.le_of_lt hk) i).1 (h i hi)
  · intro h i hi; exact (iv_eq gates x k (Nat.le_of_lt hk) i).2 (h i hi)

theorem val_or (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gates.length)
    (hop : gates[k].op = GateOp.or) :
    val gates (n + k) x = true ↔ ∃ i ∈ gates[k].inputs, i < n + k ∧ val gates i x = true := by
  have := gate_val gates (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
  constructor
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gates x k (Nat.le_of_lt hk) i).1 h⟩
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gates x k (Nat.le_of_lt hk) i).2 h⟩

theorem val_input (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    val gates w x = x ⟨w, hw⟩ := by
  rw [val, wf_keep gates _ w (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

theorem val_big (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (w : ℕ)
    (hw : n + gates.length ≤ w) : val gates w x = false := by
  rw [val, List.getD_eq_default _ _ (by rw [wf_len]; simpa using hw)]

def sp (gates : List Gate) (w : ℕ) : Finset (Fin 13) :=
  Finset.univ.filter (fun u : Fin 13 => val gates w (fun v : Fin 13 => decide (v = u)) = true)

theorem mem_sp (gates : List Gate) (w : ℕ) (u : Fin 13) :
    u ∈ sp gates w ↔ val gates w (fun v : Fin 13 => decide (v = u)) = true := by
  simp [sp]

theorem sp_input (gates : List Gate) (w : ℕ) (hw : w < 13) : (sp gates w).card ≤ 1 := by
  have : sp gates w = {⟨w, hw⟩} := by
    ext u
    rw [mem_sp, val_input gates _ w hw]
    simp [eq_comm]
  rw [this]; simp

theorem sp_big (gates : List Gate) (w : ℕ) (hw : 13 + gates.length ≤ w) :
    (sp gates w).card ≤ 1 := by
  have : sp gates w = ∅ := by
    ext u
    rw [mem_sp, val_big gates _ w hw]
    simp
  rw [this]; simp

def Ch (gates : List Gate) (k : ℕ) (X : Finset (Fin 13)) : Prop :=
  X.card ≤ 1 ∨ ∃ j, j < k ∧ X = sp gates (13 + j)

def cs (gates : List Gate) (k i : ℕ) : Finset (Fin 13) :=
  if i < 13 + k then sp gates i else ∅

theorem cs_ch (gates : List Gate) (k i : ℕ) : Ch gates k (cs gates k i) := by
  unfold cs
  split_ifs with h
  · by_cases h13 : i < 13
    · exact Or.inl (sp_input gates i h13)
    · refine Or.inr ⟨i - 13, by omega, ?_⟩
      rw [show 13 + (i - 13) = i by omega]
  · exact Or.inl (by simp)

theorem mem_cs (gates : List Gate) (k i : ℕ) (u : Fin 13) :
    u ∈ cs gates k i ↔ i < 13 + k ∧ val gates i (fun v : Fin 13 => decide (v = u)) = true := by
  unfold cs
  split_ifs with h
  · rw [mem_sp]; simp [h]
  · simp [h]

theorem struct (gates : List Gate)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (k : ℕ) (hk : k < gates.length) :
    sp gates (13 + k) = Finset.univ ∨ ∃ X Y : Finset (Fin 13), Ch gates k X ∧ Ch gates k Y ∧
      (sp gates (13 + k) = X ∩ Y ∨ sp gates (13 + k) = X ∪ Y) := by
  obtain ⟨hop, hlen⟩ := hg gates[k] (List.getElem_mem hk)
  have hins : gates[k].inputs = [] ∨ (∃ a, gates[k].inputs = [a]) ∨
      ∃ a b, gates[k].inputs = [a, b] := by
    rcases h : gates[k].inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨a, rfl⟩)
    · exact Or.inr (Or.inr ⟨a, b, rfl⟩)
    · rw [h] at hlen
      simp only [List.length_cons] at hlen
      omega
  rcases hop with hop | hop
  · have hv := fun u : Fin 13 => val_and gates (fun v : Fin 13 => decide (v = u)) k hk hop
    rcases hins with h | ⟨a, h⟩ | ⟨a, b, h⟩
    · left
      ext u
      rw [mem_sp, hv u, h]
      simp
    · right
      refine ⟨cs gates k a, cs gates k a, cs_ch _ _ _, cs_ch _ _ _, Or.inl ?_⟩
      ext u
      rw [mem_sp, hv u, h, Finset.inter_self, mem_cs]
      simp
    · right
      refine ⟨cs gates k a, cs gates k b, cs_ch _ _ _, cs_ch _ _ _, Or.inl ?_⟩
      ext u
      rw [mem_sp, hv u, h, Finset.mem_inter, mem_cs, mem_cs]
      simp
  · have hv := fun u : Fin 13 => val_or gates (fun v : Fin 13 => decide (v = u)) k hk hop
    rcases hins with h | ⟨a, h⟩ | ⟨a, b, h⟩
    · right
      refine ⟨∅, ∅, Or.inl (by simp), Or.inl (by simp), Or.inl ?_⟩
      ext u
      rw [mem_sp, hv u, h]
      simp
    · right
      refine ⟨cs gates k a, cs gates k a, cs_ch _ _ _, cs_ch _ _ _, Or.inl ?_⟩
      ext u
      rw [mem_sp, hv u, h, Finset.inter_self, mem_cs]
      simp
    · right
      refine ⟨cs gates k a, cs gates k b, cs_ch _ _ _, cs_ch _ _ _, Or.inr ?_⟩
      ext u
      rw [mem_sp, hv u, h, Finset.mem_union, mem_cs, mem_cs]
      simp

theorem chs : ∀ q < 7, Nat.choose q 2 ≤ 2 * q + (if q = 6 then 3 else 0) := by decide

theorem num (q b1 b2 : ℕ) (h13 : b1 + b2 ≤ 13) (hch : b2 ≤ Nat.choose q 2)
    (hlt : b1 + 2 * q < b2) : q = 6 ∧ b2 = 13 ∧ b1 = 0 := by
  have hq : q < 7 := by omega
  have := chs q hq
  split_ifs at this <;> omega

theorem count (G : ℕ) (s : Fin G → Finset (Fin 13)) (pts : Fin 13 → Finset (Fin 13))
    (B : Finset (Fin 13)) (H : Finset (Fin G))
    (h4 : ∀ l, (pts l).card = 4)
    (h2 : ∀ (l l' : Fin 13) (S : Finset (Fin 13)), 2 ≤ S.card → S ⊆ pts l → S ⊆ pts l' → l = l')
    (hst : ∀ k : Fin G, s k = Finset.univ ∨ ∃ X Y : Finset (Fin 13),
      (X.card ≤ 1 ∨ ∃ j : Fin G, j < k ∧ X = s j) ∧
      (Y.card ≤ 1 ∨ ∃ j : Fin G, j < k ∧ Y = s j) ∧
      (s k = X ∩ Y ∨ s k = X ∪ Y))
    (hout : ∀ l ∈ B, ∃ k : Fin G, s k = pts l)
    (hH : ∀ k ∈ H, 2 ≤ (s k).card ∧ ∃ l, l ∉ B ∧ s k ⊆ pts l) :
    3 * B.card + 2 * H.card ≤ 2 * G := by
  classical
  obtain ⟨P, hP⟩ : ∃ P : Fin 13 → Finset (Fin G),
      ∀ l k, k ∈ P l ↔ 2 ≤ (s k).card ∧ s k ⊆ pts l :=
    ⟨fun l => Finset.univ.filter (fun k => 2 ≤ (s k).card ∧ s k ⊆ pts l), by simp⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : Finset (Fin G), ∀ k, k ∈ Q ↔ 5 ≤ (s k).card ∧ (s k).card ≤ 12 :=
    ⟨Finset.univ.filter (fun k => 5 ≤ (s k).card ∧ (s k).card ≤ 12), by simp⟩
  have hsub4 : ∀ (l : Fin 13) (X : Finset (Fin 13)), X ⊆ pts l → X.card ≤ 4 := by
    intro l X hX
    rw [← h4 l]
    exact Finset.card_le_card hX
  have hK : ∀ l ∈ B, (P l).Nonempty ∧ (2 ≤ (P l).card ∨
      ∃ a b : Fin G, a ≠ b ∧ a ∈ Q ∧ b ∈ Q ∧ s a ∩ s b = pts l ∧ ∀ k ∈ P l, a < k) := by
    intro l hl
    obtain ⟨k, hk⟩ := hout l hl
    have hkP : k ∈ P l := (hP l k).2 ⟨by rw [hk, h4]; omega, by rw [hk]⟩
    refine ⟨⟨k, hkP⟩, ?_⟩
    by_cases huniq : ∀ k' ∈ P l, k' = k
    · right
      have hbig : ∀ X : Finset (Fin 13), (X.card ≤ 1 ∨ ∃ j : Fin G, j < k ∧ X = s j) →
          2 ≤ X.card → X ⊆ pts l → False := by
        intro X hX hX2 hXs
        rcases hX with h1 | ⟨j, hj, e⟩
        · omega
        · have hjP : j ∈ P l := (hP l j).2 ⟨by rw [← e]; exact hX2, by rw [← e]; exact hXs⟩
          rw [huniq j hjP] at hj
          exact lt_irrefl _ hj
      have hQ' : ∀ X Z : Finset (Fin 13), (X.card ≤ 1 ∨ ∃ j : Fin G, j < k ∧ X = s j) →
          (Z.card ≤ 1 ∨ ∃ j : Fin G, j < k ∧ Z = s j) → pts l = X ∩ Z →
          ∃ a : Fin G, a < k ∧ X = s a ∧ a ∈ Q := by
        intro X Z hX hZ hXZ
        have hXs : pts l ⊆ X := by rw [hXZ]; exact Finset.inter_subset_left
        have hc4 : 4 ≤ X.card := by rw [← h4 l]; exact Finset.card_le_card hXs
        have hXne : X ≠ pts l := fun e => hbig X hX (by omega) (by rw [e])
        have h5 : 5 ≤ X.card := by
          by_contra hlt
          exact hXne (Finset.eq_of_subset_of_card_le hXs (by rw [h4]; omega)).symm
        have h12 : X.card ≤ 12 := by
          by_contra hgt
          have hXu : X = Finset.univ := by
            apply Finset.eq_univ_of_card
            have := Finset.card_le_univ X
            rw [Fintype.card_fin] at this ⊢
            omega
          have hZe : Z = pts l := by rw [hXZ, hXu, Finset.univ_inter]
          exact hbig Z hZ (by rw [hZe, h4]; omega) (by rw [hZe])
        rcases hX with h1 | ⟨a, ha, e⟩
        · omega
        · exact ⟨a, ha, e, (hQ a).2 ⟨by rw [← e]; exact h5, by rw [← e]; exact h12⟩⟩
      rcases hst k with hu | ⟨X, Y, hX, hY, hXY⟩
      · exfalso
        have h := h4 l
        rw [← hk, hu, Finset.card_univ, Fintype.card_fin] at h
        omega
      · rw [hk] at hXY
        rcases hXY with hXY | hXY
        · obtain ⟨a, ha, ea, haQ⟩ := hQ' X Y hX hY hXY
          obtain ⟨b, hb, eb, hbQ⟩ := hQ' Y X hY hX (by rw [hXY, Finset.inter_comm])
          refine ⟨a, b, ?_, haQ, hbQ, ?_, ?_⟩
          · intro hab
            rw [ea, eb, hab, Finset.inter_self] at hXY
            have h5 := ((hQ b).1 hbQ).1
            rw [← hXY, h4] at h5
            omega
          · rw [← ea, ← eb]; exact hXY.symm
          · intro k' hk'
            rw [huniq k' hk']
            exact ha
        · exfalso
          have hXs : X ⊆ pts l := by rw [hXY]; exact Finset.subset_union_left
          have hYs : Y ⊆ pts l := by rw [hXY]; exact Finset.subset_union_right
          have hc : 4 ≤ X.card + Y.card := by
            have := Finset.card_union_le X Y
            rw [← hXY, h4] at this
            exact this
          by_cases hX2 : 2 ≤ X.card
          · exact hbig X hX hX2 hXs
          · exact hbig Y hY (by omega) hYs
    · left
      push_neg at huniq
      obtain ⟨k', hk', hne⟩ := huniq
      exact Finset.one_lt_card.2 ⟨k', hk', k, hkP, hne⟩
  have hPdis : ∀ l l', l ≠ l' → Disjoint (P l) (P l') := by
    intro l l' hne
    rw [Finset.disjoint_left]
    intro k h1 h1'
    exact hne (h2 l l' (s k) ((hP l k).1 h1).1 ((hP l k).1 h1).2 ((hP l' k).1 h1').2)
  have hPQ : ∀ l, Disjoint (P l) Q := by
    intro l
    rw [Finset.disjoint_left]
    intro k h1 h1'
    have := hsub4 l (s k) ((hP l k).1 h1).2
    have := ((hQ k).1 h1').1
    omega
  have hHP : ∀ l ∈ B, Disjoint H (P l) := by
    intro l hl
    rw [Finset.disjoint_left]
    intro k h1 h1'
    obtain ⟨hc, l4, hl4, hs4⟩ := hH k h1
    have := h2 l l4 (s k) hc ((hP l k).1 h1').2 hs4
    rw [this] at hl
    exact hl4 hl
  have hHQ : Disjoint H Q := by
    rw [Finset.disjoint_left]
    intro k h1 h1'
    obtain ⟨hc, l4, hl4, hs4⟩ := hH k h1
    have := hsub4 l4 (s k) hs4
    have := ((hQ k).1 h1').1
    omega
  have hUcard : (B.biUnion P).card = ∑ l ∈ B, (P l).card :=
    Finset.card_biUnion (fun l _ l' _ hne => hPdis l l' hne)
  have hUQ : Disjoint (B.biUnion P) Q := by
    rw [Finset.disjoint_biUnion_left]
    exact fun l _ => hPQ l
  have hHU : Disjoint H (B.biUnion P) := by
    rw [Finset.disjoint_biUnion_right]
    exact hHP
  have hUQcard : (B.biUnion P ∪ Q).card = (∑ l ∈ B, (P l).card) + Q.card := by
    rw [Finset.card_union_of_disjoint hUQ, hUcard]
  have htot : H.card + (∑ l ∈ B, (P l).card) + Q.card ≤ G := by
    have h1 : (H ∪ (B.biUnion P ∪ Q)).card = H.card + (B.biUnion P ∪ Q).card :=
      Finset.card_union_of_disjoint (Finset.disjoint_union_right.2 ⟨hHU, hHQ⟩)
    have h3 := Finset.card_le_univ (H ∪ (B.biUnion P ∪ Q))
    rw [Fintype.card_fin, h1, hUQcard] at h3
    omega
  have hsum : B.card + (B.filter (fun l => 2 ≤ (P l).card)).card ≤ ∑ l ∈ B, (P l).card := by
    rw [Finset.card_filter, Finset.card_eq_sum_ones B, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro l hl
    have := (hK l hl).1.card_pos
    split_ifs with hc <;> omega
  have hsplit := Finset.card_filter_add_card_filter_not (s := B) (fun l => 2 ≤ (P l).card)
  have hB13 : B.card ≤ 13 := by
    have := Finset.card_le_univ B
    rw [Fintype.card_fin] at this
    exact this
  have hpair : ∀ l ∈ B.filter (fun l => ¬ 2 ≤ (P l).card), ∃ t : Finset (Fin G),
      t ∈ Q.powersetCard 2 ∧ t.inf s = pts l := by
    intro l hl
    rw [Finset.mem_filter] at hl
    rcases (hK l hl.1).2 with h | ⟨a, b, hab, haQ, hbQ, hint, _⟩
    · exact absurd h hl.2
    · refine ⟨{a, b}, ?_, ?_⟩
      · rw [Finset.mem_powersetCard]
        refine ⟨?_, Finset.card_pair hab⟩
        intro x hx
        rw [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact haQ
        · exact hbQ
      · rw [Finset.inf_insert, Finset.inf_singleton]
        exact hint
  choose! f hf using hpair
  have hb2 : (B.filter (fun l => ¬ 2 ≤ (P l).card)).card ≤ Nat.choose Q.card 2 := by
    rw [← Finset.card_powersetCard]
    apply Finset.card_le_card_of_injOn f (fun l hl => (hf l (Finset.mem_coe.1 hl)).1)
    intro l hl l' hl' e
    have e1 := (hf l (Finset.mem_coe.1 hl)).2
    have e2 := (hf l' (Finset.mem_coe.1 hl')).2
    rw [e, e2] at e1
    exact h2 l l' (pts l) (by rw [h4]; omega) (Finset.Subset.refl _) (by rw [e1])
  by_cases hex : (B.filter (fun l => ¬ 2 ≤ (P l).card)).card ≤
      (B.filter (fun l => 2 ≤ (P l).card)).card + 2 * Q.card
  · omega
  · obtain ⟨hq6, hb213, hb10⟩ := num Q.card (B.filter (fun l => 2 ≤ (P l).card)).card
      (B.filter (fun l => ¬ 2 ≤ (P l).card)).card (by omega) hb2 (by omega)
    have hB2u : B.filter (fun l => ¬ 2 ≤ (P l).card) = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [Fintype.card_fin]
      exact hb213
    have hall : ∀ l : Fin 13, l ∈ B ∧ ¬ 2 ≤ (P l).card := by
      intro l
      have : l ∈ B.filter (fun l => ¬ 2 ≤ (P l).card) := by rw [hB2u]; exact Finset.mem_univ l
      exact Finset.mem_filter.1 this
    have hH0 : H.card = 0 := by
      rw [Finset.card_eq_zero]
      by_contra hne
      obtain ⟨k, hk⟩ := Finset.nonempty_iff_ne_empty.2 hne
      obtain ⟨_, l, hl, _⟩ := hH k hk
      exact hl (hall l).1
    have hGpos : 0 < G := by
      have hQne : Q.Nonempty := by
        rw [← Finset.card_pos]; omega
      obtain ⟨k, _⟩ := hQne
      exact Fin.pos k
    have h0Q : (⟨0, hGpos⟩ : Fin G) ∉ Q := by
      intro hin
      have h5 := (hQ _).1 hin
      have hch : ∀ X : Finset (Fin 13),
          (X.card ≤ 1 ∨ ∃ j : Fin G, j < (⟨0, hGpos⟩ : Fin G) ∧ X = s j) → X.card ≤ 1 := by
        intro X hX
        rcases hX with h | ⟨j, hj, _⟩
        · exact h
        · exact absurd hj (Nat.not_lt_zero _)
      rcases hst ⟨0, hGpos⟩ with hu | ⟨X, Y, hX, hY, hXY⟩
      · rw [hu, Finset.card_univ, Fintype.card_fin] at h5
        omega
      · have hx := hch X hX
        have hy := hch Y hY
        rcases hXY with hXY | hXY
        · have := Finset.card_le_card (Finset.inter_subset_left (s₁ := X) (s₂ := Y))
          rw [hXY] at h5
          omega
        · have := Finset.card_union_le X Y
          rw [hXY] at h5
          omega
    have h0U : (⟨0, hGpos⟩ : Fin G) ∉ B.biUnion P := by
      intro hin
      rw [Finset.mem_biUnion] at hin
      obtain ⟨l, hl, hin⟩ := hin
      rcases (hK l hl).2 with h | ⟨a, b, _, _, _, _, hlt⟩
      · exact (hall l).2 h
      · exact absurd (hlt _ hin) (Nat.not_lt_zero _)
    have h0 : (⟨0, hGpos⟩ : Fin G) ∉ B.biUnion P ∪ Q := by
      rw [Finset.mem_union]
      rintro (h | h)
      · exact h0U h
      · exact h0Q h
    have h3 := Finset.card_le_univ (insert (⟨0, hGpos⟩ : Fin G) (B.biUnion P ∪ Q))
    rw [Fintype.card_fin, Finset.card_insert_eq_ite, if_neg h0, hUQcard] at h3
    omega

end PEqualNP.Outside.L_meta_1619

theorem PEqualNP.Outside.L_meta_1619 : ∀ (I : Fin 13 → Fin 13 → Prop) [DecidableRel I] (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin 13 → ℕ), (∀ l0 : Fin 13, (Finset.univ.filter (fun p0 : Fin 13 => I p0 l0)).card = 4) → (∀ p1 p2 : Fin 13, p1 ≠ p2 → ∃! l1 : Fin 13, I p1 l1 ∧ I p2 l1) → (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (l2 u2 : Fin 13), (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u2k : Fin 13 => decide (u2k = u2)))).getD (out l2) false = true ↔ I u2 l2) → ∀ (B : Finset (Fin 13)) (H : Finset (Fin gates.length)), (∀ k5 ∈ H, 2 ≤ (Finset.univ.filter (fun u5 : Fin 13 => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u5k : Fin 13 => decide (u5k = u5)))).getD (13 + k5.val) false = true)).card ∧ ∃ l4 : Fin 13, l4 ∉ B ∧ ∀ u6 : Fin 13, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u6k : Fin 13 => decide (u6k = u6)))).getD (13 + k5.val) false = true → I u6 l4) → 3 * B.card + 2 * H.card ≤ 2 * gates.length := by
  intro I _ gates out h4 h2 hg hout B H hH
  apply PEqualNP.Outside.L_meta_1619.count gates.length
    (fun k => PEqualNP.Outside.L_meta_1619.sp gates (13 + k.val))
    (fun l => Finset.univ.filter (fun p : Fin 13 => I p l)) B H
  · exact h4
  · intro l l' S hS h1 h1'
    obtain ⟨p1, hp1, p2, hp2, hne⟩ := Finset.one_lt_card.1 hS
    obtain ⟨l0, _, huniq⟩ := h2 p1 p2 hne
    have a1 := (Finset.mem_filter.1 (h1 hp1)).2
    have a2 := (Finset.mem_filter.1 (h1 hp2)).2
    have b1 := (Finset.mem_filter.1 (h1' hp1)).2
    have b2 := (Finset.mem_filter.1 (h1' hp2)).2
    exact (huniq l ⟨a1, a2⟩).trans (huniq l' ⟨b1, b2⟩).symm
  · intro k
    have conv : ∀ X : Finset (Fin 13), PEqualNP.Outside.L_meta_1619.Ch gates k.val X →
        (X.card ≤ 1 ∨ ∃ j : Fin gates.length, j < k ∧
          X = PEqualNP.Outside.L_meta_1619.sp gates (13 + j.val)) := by
      intro X hX
      rcases hX with h | ⟨j, hj, e⟩
      · exact Or.inl h
      · exact Or.inr ⟨⟨j, lt_trans hj k.isLt⟩, hj, e⟩
    rcases PEqualNP.Outside.L_meta_1619.struct gates hg k.val k.isLt with h | ⟨X, Y, hX, hY, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨X, Y, conv X hX, conv Y hY, h⟩
  · intro l _
    have hsp : PEqualNP.Outside.L_meta_1619.sp gates (out l)
        = Finset.univ.filter (fun p : Fin 13 => I p l) := by
      ext u
      rw [PEqualNP.Outside.L_meta_1619.mem_sp, Finset.mem_filter]
      exact ⟨fun h => ⟨Finset.mem_univ _, (hout l u).1 h⟩, fun h => (hout l u).2 h.2⟩
    have hc : (PEqualNP.Outside.L_meta_1619.sp gates (out l)).card = 4 := by
      rw [hsp]; exact h4 l
    by_cases h13 : out l < 13
    · have := PEqualNP.Outside.L_meta_1619.sp_input gates (out l) h13
      omega
    · by_cases hbig : 13 + gates.length ≤ out l
      · have := PEqualNP.Outside.L_meta_1619.sp_big gates (out l) hbig
        omega
      · refine ⟨⟨out l - 13, by omega⟩, ?_⟩
        show PEqualNP.Outside.L_meta_1619.sp gates (13 + (out l - 13)) = _
        rw [show 13 + (out l - 13) = out l by omega]
        exact hsp
  · intro k hk
    obtain ⟨hc, l4, hl4, hsub⟩ := hH k hk
    refine ⟨hc, l4, hl4, ?_⟩
    intro u hu
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hsub u ((PEqualNP.Outside.L_meta_1619.mem_sp gates _ u).1 hu)⟩
