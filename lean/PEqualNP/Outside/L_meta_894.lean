import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_894

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Support-count argument adapted from the project proof of L-meta-757.
private def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

private def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

variable {n : ℕ}

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp


def gateSupp (L : List (Finset (Fin n))) (g : Gate) : Finset (Fin n) :=
  (g.inputs.map fun a => L.getD a ∅).foldr (· ∪ ·) ∅

theorem mem_foldr_union (l : List ℕ) (F : ℕ → Finset (Fin n)) (i : Fin n) :
    i ∈ (l.map F).foldr (· ∪ ·) ∅ ↔ ∃ a ∈ l, i ∈ F a := by
  induction l with
  | nil => simp
  | cons b l ih => simp [ih]

theorem mem_gateSupp (L : List (Finset (Fin n))) (g : Gate) (i : Fin n) :
    i ∈ gateSupp L g ↔ ∃ a ∈ g.inputs, i ∈ L.getD a ∅ :=
  mem_foldr_union _ _ _


def suppsFrom (gs : List Gate) (L : List (Finset (Fin n))) : List (Finset (Fin n)) :=
  gs.foldl (fun L g => L ++ [gateSupp L g]) L


def inputSupps (n : ℕ) : List (Finset (Fin n)) := List.ofFn fun i : Fin n => {i}


def Agree (x y : Fin n → Bool) (L : List (Finset (Fin n))) (w w' : List Bool) : Prop :=
  L.length = w.length ∧ w.length = w'.length ∧
    ∀ j : ℕ, (∀ i ∈ L.getD j ∅, x i = y i) → w.getD j false = w'.getD j false

theorem agree_wiresFrom (x y : Fin n → Bool) (gs : List Gate) :
    ∀ (L : List (Finset (Fin n))) (w w' : List Bool), Agree x y L w w' →
      Agree x y (suppsFrom gs L) (wiresFrom gs w) (wiresFrom gs w') := by
  induction gs with
  | nil => intro L w w' h; exact h
  | cons g gs ih =>
    intro L w w' h
    obtain ⟨h1, h2, h3⟩ := h
    apply ih (L ++ [gateSupp L g])
      (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
    refine ⟨by simp [h1], by simp [h2], ?_⟩
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq] at hj
      rw [h1, getD_snoc_eq, h2, getD_snoc_eq]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact h3 a (fun i hi => hj i ((mem_gateSupp L g i).2 ⟨a, ha, hi⟩))
    · rw [getD_snoc_ne _ _ _ _ hjl] at hj
      rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
      exact h3 j hj

theorem agree_inputs (x y : Fin n → Bool) :
    Agree x y (inputSupps n) (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp [inputSupps], by simp, ?_⟩
  intro j hj
  by_cases hjn : j < n
  · have hx : x ⟨j, hjn⟩ = y ⟨j, hjn⟩ := hj _ (by simp [inputSupps, hjn])
    simp [hjn, hx]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]


def Cnt (t : ℕ) (L : List (Finset (Fin n))) : Prop :=
  ∀ W : Finset ℕ, (W.biUnion fun j => L.getD j ∅).card ≤ t + W.card

theorem cnt_inputs : Cnt 0 (inputSupps n) := by
  intro W
  refine le_trans Finset.card_biUnion_le ?_
  rw [zero_add, Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro j _
  by_cases hjn : j < n
  · simp [inputSupps, hjn]
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

theorem cnt_step (t : ℕ) (L : List (Finset (Fin n))) (g : Gate) (hg : g.inputs.length ≤ 2)
    (h : Cnt t L) : Cnt (t + 1) (L ++ [gateSupp L g]) := by
  intro W
  by_cases hW : L.length ∈ W
  · have hsub : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        ⊆ ((W.erase L.length ∪ g.inputs.toFinset).biUnion fun j => L.getD j ∅) := by
      intro i hi
      rw [Finset.mem_biUnion] at hi ⊢
      obtain ⟨j, hjW, hij⟩ := hi
      by_cases hjl : j = L.length
      · subst hjl
        rw [getD_snoc_eq] at hij
        obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g i).1 hij
        exact ⟨a, Finset.mem_union_right _ (List.mem_toFinset.2 ha), hia⟩
      · rw [getD_snoc_ne _ _ _ _ hjl] at hij
        exact ⟨j, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hjl, hjW⟩), hij⟩
    have hc1 : (W.erase L.length ∪ g.inputs.toFinset).card ≤ (W.card - 1) + 2 := by
      refine le_trans (Finset.card_union_le _ _) ?_
      rw [Finset.card_erase_of_mem hW]
      exact Nat.add_le_add_left (le_trans (List.toFinset_card_le _) hg) _
    have hWpos : 1 ≤ W.card := Finset.card_pos.2 ⟨_, hW⟩
    have := h (W.erase L.length ∪ g.inputs.toFinset)
    have := Finset.card_le_card hsub
    omega
  · have heq : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        = (W.biUnion fun j => L.getD j ∅) := by
      apply Finset.biUnion_congr rfl
      intro j hj
      exact getD_snoc_ne _ _ _ _ (fun e => hW (e ▸ hj))
    rw [heq]
    have := h W
    omega

theorem cnt_suppsFrom (gs : List Gate) : ∀ (t : ℕ) (L : List (Finset (Fin n))),
    (∀ g ∈ gs, Ok g) → Cnt t L → Cnt (t + gs.length) (suppsFrom gs L) := by
  induction gs with
  | nil => intro t L _ h; exact h
  | cons g gs ih =>
    intro t L hok h
    have := ih (t + 1) (L ++ [gateSupp L g]) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (cnt_step t L g (hok g List.mem_cons_self).2 h)
    rw [List.length_cons, show t + (gs.length + 1) = t + 1 + gs.length by omega]
    exact this

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

private def base : Finset (Fin 73) := {0, 1, 3, 7, 15, 31, 36, 54, 63}

private def line (w : Fin 73) := base.image (fun u => u + w)

private theorem line_card (w : Fin 73) : (line w).card = 9 := by
  rw [line, Finset.card_image_of_injective _ (add_left_injective w)]
  decide

set_option maxRecDepth 8192 in
private theorem period_zero : ∀ t : Fin 73, (∀ b ∈ base, b + t ∈ base) → t = 0 := by
  decide

private theorem line_injective : Function.Injective line := by
  intro i j h
  have period : ∀ b ∈ base, b + (i - j) ∈ base := by
    intro b hb
    have hbi : b + i ∈ line i := Finset.mem_image.mpr ⟨b, hb, rfl⟩
    rw [h] at hbi
    obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hbi
    have : a = b + (i - j) := by rw [← eq_sub_iff_add_eq] at he; rw [he]; abel
    exact this ▸ ha
  exact sub_eq_zero.mp (period_zero (i-j) period)

private theorem wire_count (L : List Gate) (out : Fin 73 → ℕ)
    (hok : ∀ g ∈ L, Ok g)
    (heval : ∀ w (x : Fin 73 → Bool), (wiresFrom L (List.ofFn x)).getD (out w) false =
      decide (∃ v ∈ line w, x v = true)) : 80 ≤ L.length := by
  have hs (w p : Fin 73) : (wiresFrom L (List.ofFn (fun q : Fin 73 => decide (q = p)))).getD
      (out w) false = decide (p ∈ line w) := by
    rw [heval]
    simp
  have hinj : Function.Injective out := by
    intro i j hij
    apply line_injective
    ext p
    have e := hs i p
    rw [hij, hs j p] at e
    simpa using e.symm
  have hvalid (w : Fin 73) : out w < 73 + L.length := by
    by_contra! hn
    have hp : w ∈ line w := by
      exact Finset.mem_image.mpr ⟨0, by decide, zero_add w⟩
    have h := hs w w
    rw [List.getD_eq_default _ _ (by simp [length_wiresFrom]; omega)] at h
    simp [hp] at h
  have hlower (w : Fin 73) : 80 ≤ out w := by
    by_contra! hearly
    let pre := L.take 7
    have hlen : pre.length = min 7 L.length := List.length_take
    have hout := hvalid w
    have hp (x : Fin 73 → Bool) : (wiresFrom pre (List.ofFn x)).getD (out w) false =
        (wiresFrom L (List.ofFn x)).getD (out w) false := by
      conv_rhs => rw [← List.take_append_drop 7 L, wiresFrom_append]
      apply Eq.symm
      apply getD_wiresFrom
      simp only [length_wiresFrom, List.length_ofFn, List.length_take]
      omega
    let S := (suppsFrom pre (inputSupps 73)).getD (out w) ∅
    have hsub : line w ⊆ S := by
      intro p hpl
      by_contra hn
      let x := fun q : Fin 73 => decide (q = p)
      let z := fun _ : Fin 73 => false
      have hag := (agree_wiresFrom x z pre _ _ _ (agree_inputs _ _)).2.2 (out w)
        (by
          intro q hq
          have hnq : q ≠ p := fun e => hn (e ▸ hq)
          simp [x, z, hnq])
      rw [hp, hp, heval, heval] at hag
      simp [x, z, hpl] at hag
    have hc := cnt_suppsFrom pre 0 (inputSupps 73)
      (fun g hg => hok g (List.mem_of_mem_take hg)) cnt_inputs {out w}
    change _ ≤ _ at hc
    simp only [Finset.singleton_biUnion, Finset.card_singleton, zero_add] at hc
    have hs9 : 9 ≤ S.card := line_card w ▸ Finset.card_le_card hsub
    change S.card ≤ pre.length + 1 at hc
    omega
  let f (w : Fin 73) : Fin (L.length - 7) :=
    ⟨out w - 80, by have := hlower w; have := hvalid w; omega⟩
  have hf : Function.Injective f := by
    intro i j he
    apply hinj
    have h : out i - 80 = out j - 80 := congrArg Fin.val he
    have := hlower i
    have := hlower j
    omega
  have h := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_fin] at h
  omega

end PEqualNP.Outside.L_meta_894

theorem PEqualNP.Outside.L_meta_894 : ((∀ (n m k : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (c : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ i : Fin m, 2 ≤ (S i).card) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → (∀ (i : Fin m) (p : Fin n), (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (o i) false = true ↔ p ∈ S i) → (∀ (i : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k → (∀ q ∈ S i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false) → (∀ i : Fin m, c i ≤ k) → (∀ i : Fin m, c i + 1 ≤ (S i).card) → ∑ i : Fin m, c i ≤ C.size) → (∀ (n : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate) (T Z : Finset (Fin n)), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (r : ℕ → ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∧ gates'.length ≤ gates.length ∧ ∀ o : ℕ, (∃ x y : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i)) ≠ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else y i))) → ∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', r o⟩ (List.ofFn x) = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i))) → ∀ (nP mL qO : ℕ) (Fam : Fin mL → Finset (Fin nP)), (∀ i1 : Fin mL, (Fam i1).card = qO + 1) → (∀ i7 i8 : Fin mL, i7 ≠ i8 → (Fam i7 ∩ Fam i8).card ≤ 1) → (∀ p1 p2 : Fin nP, p1 ≠ p2 → ∃ i3 : Fin mL, p1 ∈ Fam i3 ∧ p2 ∈ Fam i3) → (∀ p3 : Fin nP, (Finset.univ.filter (fun i4 : Fin mL => p3 ∈ Fam i4)).card = qO + 1) → ∀ (tN kW : ℕ) (L : List PEqualNP.CircuitLowerBounds.Gate) (outW : Fin mL → ℕ), 1 ≤ tN → 1 ≤ kW → (∀ g1 ∈ L, (g1.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g1.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g1.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g1.inputs.length ≤ 2) → Set.ncard {i5 : Fin L.length | (L.get i5).op = PEqualNP.CircuitLowerBounds.GateOp.not} ≤ tN → (∀ (j1 : ℕ) (g2 : PEqualNP.CircuitLowerBounds.Gate), L[j1]? = some g2 → g2.op = PEqualNP.CircuitLowerBounds.GateOp.not → Monotone (fun x1 : Fin nP → Bool => (g2.inputs.map (fun i6 => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨L.take j1, 0⟩ (List.ofFn x1)).getD i6 false)).headD false)) → (∀ (w1 : Fin mL) (x2 : Fin nP → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨L, outW w1⟩ (List.ofFn x2) = decide (∃ v1 ∈ Fam w1, x2 v1 = true)) → ∀ Kb : ℕ, ((tN = 1 ∧ Kb ≤ kW * mL ∧ Kb ≤ qO * mL) ∨ (Kb + kW * (tN * kW * qO + 1) ≤ kW * mL + kW * kW * qO ∧ Kb + qO * (tN * kW * qO + 1) ≤ qO * mL + qO * kW * qO)) → Kb + qO * (tN * kW * qO + 1) ≤ qO * mL → Kb ≤ L.length) → ∀ (L5 : List PEqualNP.CircuitLowerBounds.Gate) (out5 : Fin 73 → ℕ), (∀ ga5 ∈ L5, (ga5.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ ga5.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ ga5.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ ga5.inputs.length ≤ 2) → Set.ncard {ic5 : Fin L5.length | (L5.get ic5).op = PEqualNP.CircuitLowerBounds.GateOp.not} ≤ 3 → (∀ (ja5 : ℕ) (gb5 : PEqualNP.CircuitLowerBounds.Gate), L5[ja5]? = some gb5 → gb5.op = PEqualNP.CircuitLowerBounds.GateOp.not → Monotone (fun xa5 : Fin 73 → Bool => (gb5.inputs.map (fun ia5 => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨L5.take ja5, 0⟩ (List.ofFn xa5)).getD ia5 false)).headD false)) → (∀ (wa5 : Fin 73) (xb5 : Fin 73 → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨L5, out5 wa5⟩ (List.ofFn xb5) = decide (∃ va5 ∈ (({0, 1, 3, 7, 15, 31, 36, 54, 63} : Finset (Fin 73)).image (fun ua5 => ua5 + wa5)), xb5 va5 = true)) → 80 ≤ L5.length := by
  intro _ L out hg _ _ heval
  apply PEqualNP.Outside.L_meta_894.wire_count L out
  · intro gate hgate
    obtain ⟨h, hlen⟩ := hg gate hgate
    exact ⟨h, hlen⟩
  · exact heval
