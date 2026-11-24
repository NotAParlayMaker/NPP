import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1612_aux

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

lemma wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_ext (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    let v := g.op.eval (g.inputs.map fun i => w.getD i false)
    obtain ⟨t, ht, hl⟩ := ih (w ++ [v])
    refine ⟨v :: t, ?_, by simp [hl]⟩
    have hstep : wiresFrom (g :: gs) w = wiresFrom gs (w ++ [v]) := rfl
    rw [hstep, ht]
    simp

lemma length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_ext gs w
  rw [ht, List.length_append, hl]

lemma getD_wiresFrom_lt (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_ext gs w
  rw [ht, List.getD_append _ _ _ _ h]

lemma getD_wiresFrom_take (gs : List Gate) (w : List Bool) (k i : ℕ) (hk : k ≤ gs.length) :
    (wiresFrom (gs.take k) w).getD i false =
      if i < w.length + k then (wiresFrom gs w).getD i false else false := by
  have hlen : (wiresFrom (gs.take k) w).length = w.length + k := by
    rw [length_wiresFrom, List.length_take, min_eq_left hk]
  split_ifs with hi
  · have hsplit : gs = gs.take k ++ gs.drop k := (List.take_append_drop k gs).symm
    conv_rhs => rw [hsplit, wiresFrom_append]
    exact (getD_wiresFrom_lt (gs.drop k) (wiresFrom (gs.take k) w) i (by omega)).symm
  · rw [List.getD_eq_default]
    omega

lemma getD_snoc_eq (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp

lemma getD_wiresFrom_gate (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < gs.length) :
    (wiresFrom gs w).getD (w.length + k) false =
      (gs[k]).op.eval ((gs[k]).inputs.map fun i =>
        if i < w.length + k then (wiresFrom gs w).getD i false else false) := by
  have hsplit : gs = gs.take k ++ gs[k] :: gs.drop (k + 1) := by
    have h1 := (List.take_append_drop k gs).symm
    rw [List.drop_eq_getElem_cons hk] at h1
    exact h1
  have hlen : (wiresFrom (gs.take k) w).length = w.length + k := by
    rw [length_wiresFrom, List.length_take, min_eq_left (Nat.le_of_lt hk)]
  have heq : wiresFrom gs w =
      wiresFrom (gs.drop (k + 1))
        (wiresFrom (gs.take k) w ++
          [(gs[k]).op.eval ((gs[k]).inputs.map fun i => (wiresFrom (gs.take k) w).getD i false)]) := by
    conv_lhs => rw [hsplit, wiresFrom_append]
    rfl
  rw [heq, getD_wiresFrom_lt]
  · conv_lhs => rw [← hlen, getD_snoc_eq]
    congr 1
    apply List.map_congr_left
    intro i _
    rw [getD_wiresFrom_take gs w k i (Nat.le_of_lt hk), heq]
  · rw [List.length_append, hlen]; simp

lemma gateOp_eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l₁ l₂ : List Bool) (hlen : l₁.length = l₂.length)
    (hle : ∀ i, l₁.getD i false = true → l₂.getD i false = true) :
    op.eval l₁ = true → op.eval l₂ = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, id_eq]
    intro h b hb
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
    have h1 : l₁.getD i false = true := by
      have hi1 : i < l₁.length := by omega
      rw [List.getD_eq_getElem _ _ hi1]
      exact h _ (List.getElem_mem hi1)
    have h2 := hle i h1
    rwa [List.getD_eq_getElem _ _ hi] at h2
  · simp only [GateOp.eval, List.any_eq_true, id_eq]
    rintro ⟨b, hb, rfl⟩
    obtain ⟨i, hi, hbi⟩ := List.getElem_of_mem hb
    have h1 : l₁.getD i false = true := by
      rw [List.getD_eq_getElem _ _ hi]; exact hbi
    have h2 := hle i h1
    have hi2 : i < l₂.length := by omega
    rw [List.getD_eq_getElem _ _ hi2] at h2
    exact ⟨l₂[i], List.getElem_mem hi2, h2⟩

lemma wiresFrom_mono (gs : List Gate)
    (hmono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ (w₁ w₂ : List Bool), w₁.length = w₂.length →
      (∀ i, w₁.getD i false = true → w₂.getD i false = true) →
      ∀ i, (wiresFrom gs w₁).getD i false = true → (wiresFrom gs w₂).getD i false = true := by
  induction gs with
  | nil =>
    intro w₁ w₂ _ hle i hi
    exact hle i hi
  | cons g gs ih =>
    intro w₁ w₂ hlen hle i hi
    have hstep1 : wiresFrom (g :: gs) w₁ =
        wiresFrom gs (w₁ ++ [g.op.eval (g.inputs.map fun j => w₁.getD j false)]) := rfl
    have hstep2 : wiresFrom (g :: gs) w₂ =
        wiresFrom gs (w₂ ++ [g.op.eval (g.inputs.map fun j => w₂.getD j false)]) := rfl
    rw [hstep1] at hi
    rw [hstep2]
    apply ih (fun g' hg' => hmono g' (List.mem_cons_of_mem g hg')) _ _ (by simp [hlen]) _ i hi
    intro j hj
    by_cases hlt : j < w₁.length
    · rw [List.getD_append _ _ _ _ hlt] at hj
      rw [List.getD_append _ _ _ _ (by omega)]
      exact hle j hj
    · by_cases heq : j = w₁.length
      · subst heq
        rw [getD_snoc_eq] at hj
        rw [hlen, getD_snoc_eq]
        exact gateOp_eval_mono g.op (hmono g List.mem_cons_self)
          (g.inputs.map fun k => w₁.getD k false) (g.inputs.map fun k => w₂.getD k false)
          (by simp) (by
            intro t ht
            by_cases ht_lt : t < g.inputs.length
            · rw [List.getD_eq_getElem _ _ (by simpa using ht_lt)] at ht
              rw [List.getD_eq_getElem _ _ (by simpa using ht_lt)]
              simp only [List.getElem_map] at ht ⊢
              exact hle _ ht
            · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt ht_lt)] at ht
              exact Bool.noConfusion ht) hj
      · rw [List.getD_eq_default _ _ (by simp; omega)] at hj
        exact Bool.noConfusion hj

abbrev V := Fin 13
abbrev counts (a b c d : V) :=
  a = b ∨ a = c ∨ a = d ∨ b = c ∨ b = d ∨ c = d

private lemma pigeon {S : Finset V} (small : S.card ≤ 3) {a b c d : V}
    (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (hd : d ∈ S) : counts a b c d := by
  unfold counts
  by_contra! h
  obtain ⟨ab, ac, ad, bc, bd, cd⟩ := h
  have sub : ({a,b,c,d} : Finset V) ⊆ S := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  have q := Finset.card_le_card sub
  simp [ab,ac,ad,bc,bd,cd] at q
  omega

private lemma cuts_bound {n : ℕ} (I : Finset (Fin n)) (S : Finset V) (small : S.card ≤ 3)
    (a b : I → V) (cut : I → Finset V)
    (ha : ∀ i, a i ∈ S) (hb : ∀ i, b i ∈ S)
    (inCut : ∀ i, a i ∈ cut i) (outCut : ∀ i, b i ∉ cut i)
    (prior : ∀ i j : I, i.val < j.val → (a i ∈ cut j ↔ b i ∈ cut j)) : I.card ≤ 2 := by
  by_contra! many
  let ord := I.orderEmbOfCardLe (show 3 ≤ I.card by omega)
  let atI (k : Fin 3) : I := ⟨ord k, I.orderEmbOfCardLe_mem _ k⟩
  have inc (i j : Fin 3) (h : i < j) : (atI i).val < (atI j).val := ord.strictMono h
  let i := atI 0
  let j := atI 1
  let k := atI 2
  have ij := prior i j (inc 0 1 (by decide))
  have ik := prior i k (inc 0 2 (by decide))
  have jk := prior j k (inc 1 2 (by decide))
  have ai := inCut i
  have bi := outCut i
  have aj := inCut j
  have bj := outCut j
  have ak := inCut k
  have bk := outCut k
  have joined : a i ∈ cut k ↔ a j ∈ cut k := by
    have overlap := pigeon small (ha i) (hb i) (ha j) (hb j)
    unfold counts at overlap
    grind only
  have fresh : (a j ≠ a i ∧ a j ≠ b i) ∨ (b j ≠ a i ∧ b j ≠ b i) := by
    grind only
  have sameSide (p : V) (hp : p ∈ S) : p ∈ cut k ↔ a i ∈ cut k := by
    rcases fresh with newLeft | newRight
    · have cover := pigeon small (ha i) (hb i) (ha j) hp
      unfold counts at cover
      grind only
    · have cover := pigeon small (ha i) (hb i) (hb j) hp
      unfold counts at cover
      grind only
  exact bk ((sameSide (b k) (hb k)).2 ((sameSide (a k) (ha k)).1 ak))

abbrev val (gs : List Gate) (wire : ℕ) (x : V → Bool) : Bool :=
  Circuit.eval ⟨gs,wire⟩ (List.ofFn x)

private theorem raise_input {gs : List Gate} (ops : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
    {x y : V → Bool} (h : ∀ v, x v = true → y v = true) (w : ℕ) :
    val gs w x = true → val gs w y = true := by
  apply wiresFrom_mono gs ops _ _ (by simp) _ w
  intro v
  by_cases hv : v < 13
  · simpa only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left hv,
      Option.getD_some] using h ⟨v,hv⟩
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_right hv,
      Option.getD_none, imp_self]

private theorem or_reads {gs : List Gate} (back : ∀ i : Fin gs.length,
    ∀ w ∈ (gs.get i).inputs, w < 13+i.val) (g : Fin gs.length)
    {a b : ℕ} (op : (gs.get g).op = .or) (ports : (gs.get g).inputs = [a,b])
    (x : V → Bool) : val gs (13+g.val) x = true ↔
      val gs a x = true ∨ val gs b x = true := by
  have ha := back g a (by rw [ports]; simp)
  have hb := back g b (by rw [ports]; simp)
  have eq := getD_wiresFrom_gate gs (List.ofFn x) g.val g.isLt
  change gs[g.val].op = .or at op
  change gs[g.val].inputs = [a,b] at ports
  simp only [List.length_ofFn, op, ports, List.map_cons, List.map_nil, ite_eq_left ha, ite_eq_left hb,
    GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false] at eq
  change (wiresFrom gs (List.ofFn x)).getD (13+g.val) false = true ↔ _
  rw [eq, Bool.or_eq_true]
  rfl

abbrev live (gs : List Gate) (g : Fin gs.length) (t : V → V → Bool) (p : V) : Prop :=
  ∃ w ∈ (gs.get g).inputs, val gs w (t p) = true

def event (gs : List Gate) (g : Fin gs.length) (s : Finset V) (t : V → V → Bool) : Prop :=
  (gs.get g).op = .or ∧ val gs (13+g.val) (fun v => decide (v ∉ s)) = false ∧
  ∃ a b, (gs.get g).inputs = [a,b] ∧ ∃ r ∈ s, ∃ q ∈ s,
    val gs a (t r) = true ∧ val gs b (t q) = true ∧
    ∃ X : Finset V, r ∈ X ∧ q ∉ X ∧ ∀ i : Fin gs.length, i < g →
      (gs.get i).op = .or → val gs (13+i.val) (fun v => decide (v ∉ s)) = false →
      ∀ w w', (gs.get i).inputs = [w,w'] → ∀ p ∈ s, ∀ q ∈ s,
        (val gs w (t p) = true ∨ val gs w' (t p) = true) →
        (val gs w (t q) = true ∨ val gs w' (t q) = true) → (p ∈ X ↔ q ∈ X)

private theorem side (gs : List Gate) (ops : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
    (back : ∀ i : Fin gs.length, ∀ w ∈ (gs.get i).inputs, w < 13+i.val)
    (s : Finset V) (z : V) (t : V → V → Bool) (small : (s.erase z).card ≤ 3)
    (anchor : t z = fun v => decide (v = z)) (I : Finset (Fin gs.length))
    (hi : ∀ g ∈ I, event gs g s t)
    (block : ∀ g ∈ I, ∃ y : V → Bool, y z = true ∧ val gs (13+g.val) y = false) :
    I.card ≤ 2 := by
  classical
  have data (g : I) : ∃ p ∈ s.erase z, ∃ q ∈ s.erase z,
      live gs g.val t p ∧ live gs g.val t q ∧ ∃ X : Finset V,
      p ∈ X ∧ q ∉ X ∧ ∀ i : I, i.val < g.val → ∀ u ∈ s, ∀ v ∈ s,
        live gs i.val t u → live gs i.val t v → (u ∈ X ↔ v ∈ X) := by
    obtain ⟨op, _, a, b, ports, p, hp, q, hq, left, right, X, hx, hy, prior⟩ := hi g g.property
    have off (v : V) (h : val gs (13+g.val.val) (t v) = true) : v ≠ z := by
      intro eq
      subst v
      obtain ⟨y, hz, zero⟩ := block g g.property
      apply Bool.noConfusion (zero.symm.trans (raise_input ops (x := t z) (y := y) ?_ _ h))
      intro u hu
      rw [anchor] at hu
      have eq : u = z := of_decide_eq_true hu
      simpa [eq] using hz
    have hread := or_reads back g.val op ports
    refine ⟨p, Finset.mem_erase.mpr ⟨off p ((hread _).2 (Or.inl left)), hp⟩,
      q, Finset.mem_erase.mpr ⟨off q ((hread _).2 (Or.inr right)), hq⟩,
      ⟨a, by rw [ports]; simp, left⟩, ⟨b, by rw [ports]; simp, right⟩, X, hx, hy, ?_⟩
    intro i earlier u hu v hv h1 h2
    obtain ⟨iop, izero, c, d, ins, _⟩ := hi i i.property
    apply prior i.val earlier iop izero c d ins u hu v hv
    · unfold live at h1
      rw [ins] at h1
      simpa using h1
    · unfold live at h2
      rw [ins] at h2
      simpa using h2
  choose a ha b hb la lb X ax bx same using data
  apply cuts_bound I (s.erase z) small a b X ha hb ax bx
  intro i j h
  exact same j i h (a i) (Finset.mem_of_mem_erase (ha i)) (b i)
    (Finset.mem_of_mem_erase (hb i)) (la i) (lb i)

end PEqualNP.Outside.L_meta_1612_aux

open PEqualNP.Outside.L_meta_1612_aux
theorem PEqualNP.Outside.L_meta_1612 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ (T : Fin 13 → Fin 13 → Fin 13 → Bool) (gates : List PEqualNP.CircuitLowerBounds.Gate),
    (∀ t : Fin 13, ∀ p ∈ L t, ∀ v ∈ L t, T t p v = true ↔ v = p) → (∀ l ∈ ({4, 10, 12} : Finset (Fin 13)), T l 0 = (fun v : Fin 13 => decide (v = 0))) → (∀ m ∈ ({1, 5, 11} : Finset (Fin 13)), T m 1 = (fun v : Fin 13 => decide (v = 1))) → (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < 13 + (i : ℕ)) →
    (∀ l ∈ ({4, 10, 12} : Finset (Fin 13)), (∀ X : Finset (Fin 13), (∀ i : Fin gates.length, True → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (i : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = false →
          ∀ a b : ℕ, (gates.get i).inputs = [a, b] → ∀ y ∈ L l, ∀ y' ∈ L l,
          (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, a⟩ (List.ofFn (T l y)) = true ∨ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, b⟩ (List.ofFn (T l y)) = true) → (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, a⟩ (List.ofFn (T l y')) = true ∨ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, b⟩ (List.ofFn (T l y')) = true) → (y ∈ X ↔ y' ∈ X)) → ∀ y ∈ L l, ∀ y' ∈ L l, (y ∈ X ↔ y' ∈ X)) →
      ∀ I : Finset (Fin gates.length), (∀ g ∈ I, ((gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (g : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = false ∧
        ∃ w1 w2 : ℕ, (gates.get g).inputs = [w1, w2] ∧ ∃ r ∈ L l, ∃ r' ∈ L l, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w1⟩ (List.ofFn (T l r)) = true ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w2⟩ (List.ofFn (T l r')) = true ∧
        ∃ X : Finset (Fin 13), r ∈ X ∧ r' ∉ X ∧ (∀ i : Fin gates.length, i < g → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (i : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = false →
          ∀ a b : ℕ, (gates.get i).inputs = [a, b] → ∀ y ∈ L l, ∀ y' ∈ L l,
          (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, a⟩ (List.ofFn (T l y)) = true ∨ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, b⟩ (List.ofFn (T l y)) = true) → (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, a⟩ (List.ofFn (T l y')) = true ∨ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, b⟩ (List.ofFn (T l y')) = true) → (y ∈ X ↔ y' ∈ X))) ∧
        ∃ m ∈ ({1, 5, 11} : Finset (Fin 13)), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (g : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = false) → I.card ≤ 2) ∧
    (∀ m ∈ ({1, 5, 11} : Finset (Fin 13)), (∀ X : Finset (Fin 13), (∀ i : Fin gates.length, True → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (i : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = false →
          ∀ a b : ℕ, (gates.get i).inputs = [a, b] → ∀ y ∈ L m, ∀ y' ∈ L m,
          (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, a⟩ (List.ofFn (T m y)) = true ∨ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, b⟩ (List.ofFn (T m y)) = true) → (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, a⟩ (List.ofFn (T m y')) = true ∨ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, b⟩ (List.ofFn (T m y')) = true) → (y ∈ X ↔ y' ∈ X)) → ∀ y ∈ L m, ∀ y' ∈ L m, (y ∈ X ↔ y' ∈ X)) →
      ∀ I : Finset (Fin gates.length), (∀ g ∈ I, ((gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (g : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = false ∧
        ∃ w1 w2 : ℕ, (gates.get g).inputs = [w1, w2] ∧ ∃ r ∈ L m, ∃ r' ∈ L m, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w1⟩ (List.ofFn (T m r)) = true ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w2⟩ (List.ofFn (T m r')) = true ∧
        ∃ X : Finset (Fin 13), r ∈ X ∧ r' ∉ X ∧ (∀ i : Fin gates.length, i < g → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (i : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = false →
          ∀ a b : ℕ, (gates.get i).inputs = [a, b] → ∀ y ∈ L m, ∀ y' ∈ L m,
          (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, a⟩ (List.ofFn (T m y)) = true ∨ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, b⟩ (List.ofFn (T m y)) = true) → (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, a⟩ (List.ofFn (T m y')) = true ∨ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, b⟩ (List.ofFn (T m y')) = true) → (y ∈ X ↔ y' ∈ X))) ∧
        ∃ l ∈ ({4, 10, 12} : Finset (Fin 13)), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (g : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = false) → I.card ≤ 2) := by
  intro L plane T gates _ atZero atOne logic precedes
  have ops : ∀ g ∈ gates, g.op = .and ∨ g.op = .or := fun g hg => (logic g hg).1
  have geometry : (∀ l ∈ ({4,10,12} : Finset (Fin 13)), ((L l).erase 0).card ≤ 3 ∧ 1 ∉ L l) ∧
      (∀ m ∈ ({1,5,11} : Finset (Fin 13)), ((L m).erase 1).card ≤ 3 ∧ 0 ∉ L m) := by
    simp only [plane]
    decide +kernel
  constructor
  · intro l hl _ I hI
    apply side gates ops precedes (L l) 0 (T l) (geometry.1 l hl).1 (atZero l hl) I
      (fun i hi => (hI i hi).1)
    intro i hi
    obtain ⟨m, hm, e⟩ := (hI i hi).2
    exact ⟨_, decide_eq_true (geometry.2 m hm).2, e⟩
  · intro m hm _ I hI
    apply side gates ops precedes (L m) 1 (T m) (geometry.2 m hm).1 (atOne m hm) I
      (fun i hi => (hI i hi).1)
    intro i hi
    obtain ⟨l, hl, e⟩ := (hI i hi).2
    exact ⟨_, decide_eq_true (geometry.1 l hl).2, e⟩
