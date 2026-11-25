import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6088

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def targetA : Fin 4 → Fin 4 → Bool :=
  fun u v => (5807 : ℕ).testBit (4 * u.val + v.val)

def oe (u v : Fin 4) : List Bool :=
  oneEach u v

def upperCircuit : Circuit :=
  ⟨[⟨GateOp.or, [5, 7]⟩, ⟨GateOp.and, [1, 8]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.and, [2, 10]⟩,
    ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.or, [0, 9]⟩, ⟨GateOp.or, [11, 12]⟩, ⟨GateOp.or, [13, 14]⟩], 15⟩

lemma upperCircuit_mono2 : Monotone2 upperCircuit := by
  intro g hg
  simp only [upperCircuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

lemma upper : RepSizeAtMost targetA 8 :=
  ⟨upperCircuit, upperCircuit_mono2, by decide, by decide⟩

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def W (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl step w

lemma W_append (a b : List Gate) (w : List Bool) : W (a ++ b) w = W b (W a w) := by
  simp [W, List.foldl_append]

lemma W_length (gs : List Gate) : ∀ w : List Bool, (W gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [W]
  | cons g gs ih =>
    intro w
    change (W gs (step w g)).length = w.length + (gs.length + 1)
    rw [ih]
    simp [step]
    omega

lemma getD_append_lt (l l2 : List Bool) (i : ℕ) (h : i < l.length) :
    (l ++ l2).getD i false = l.getD i false := by
  simp [List.getD, List.getElem?_append_left h]

lemma W_prefix (gs : List Gate) :
    ∀ (w : List Bool) (i : ℕ), i < w.length → (W gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    change (W gs (step w g)).getD i false = w.getD i false
    rw [ih (step w g) i (by simp [step]; omega)]
    exact getD_append_lt w _ i hi

def val (C : Circuit) (x : List Bool) (w : ℕ) : Bool :=
  (C.wires x).getD w false

lemma val_input (C : Circuit) (x : List Bool) (hx : x.length = 8) (i : ℕ) (hi : i < 8) :
    val C x i = x.getD i false := by
  unfold val Circuit.wires
  exact W_prefix C.gates x i (by omega)

lemma val_ge (C : Circuit) (x : List Bool) (hx : x.length = 8) (w : ℕ)
    (hw : 8 + C.gates.length ≤ w) : val C x w = false := by
  unfold val Circuit.wires
  have hlen : (W C.gates x).length = 8 + C.gates.length := by
    rw [W_length, hx]
  change (W C.gates x).getD w false = false
  rw [List.getD_eq_default _ _ (by omega)]

lemma val_gate (C : Circuit) (x : List Bool) (hx : x.length = 8) (w : ℕ)
    (hw1 : 8 ≤ w) (hw2 : w < 8 + C.gates.length) :
    val C x w =
      (C.gates[w - 8]'(by omega)).op.eval
        ((C.gates[w - 8]'(by omega)).inputs.map fun i => if i < w then val C x i else false) := by
  set j := w - 8
  have hj : j < C.gates.length := by omega
  set pre := C.gates.take j
  set g := C.gates[j]'hj
  set post := C.gates.drop (j + 1)
  have hsplit : C.gates = pre ++ g :: post := by
    have h1 : C.gates = C.gates.take j ++ C.gates.drop j := (List.take_append_drop j C.gates).symm
    have h2 : C.gates.drop j = g :: post := List.drop_eq_getElem_cons hj
    rw [h1, h2]
  have hpre_len : (W pre x).length = w := by
    rw [W_length, hx]
    simp [pre]
    omega
  have hW : W C.gates x = W post (step (W pre x) g) := by
    rw [hsplit, W_append]
    rfl
  have hstep_val : (step (W pre x) g).getD w false =
      g.op.eval (g.inputs.map fun i => (W pre x).getD i false) := by
    unfold step
    rw [← hpre_len]
    simp [List.getD]
  have hmain : val C x w = g.op.eval (g.inputs.map fun i => (W pre x).getD i false) := by
    unfold val Circuit.wires
    change (W C.gates x).getD w false = _
    rw [hW, W_prefix post (step (W pre x) g) w (by simp [step, hpre_len]), hstep_val]
  rw [hmain]
  congr 1
  apply List.map_congr_left
  intro i _
  by_cases hi : i < w
  · simp only [hi, ↓reduceIte]
    unfold val Circuit.wires
    change (W pre x).getD i false = (W C.gates x).getD i false
    rw [hsplit, W_append, W_prefix (g :: post) (W pre x) i (by omega)]
  · simp only [hi, ↓reduceIte]
    exact List.getD_eq_default _ _ (by omega)

def ch (C : Circuit) (w : ℕ) : Finset ℕ :=
  if h : 8 ≤ w ∧ w < 8 + C.gates.length then
    ((C.gates[w - 8]'(by omega)).inputs.filter (· < w)).toFinset
  else
    ∅

lemma mem_ch_lt (C : Circuit) (w a : ℕ) (ha : a ∈ ch C w) : a < w := by
  unfold ch at ha
  split_ifs at ha with h
  · simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at ha
    exact ha.2
  · simp at ha

lemma card_ch_le (C : Circuit) (hC : Monotone2 C) (w : ℕ) : (ch C w).card ≤ 2 := by
  unfold ch
  split_ifs with h
  · have hg := hC (C.gates[w - 8]'(by omega)) (List.getElem_mem _)
    calc
      ((C.gates[w - 8]'(by omega)).inputs.filter (· < w)).toFinset.card
          ≤ ((C.gates[w - 8]'(by omega)).inputs.filter (· < w)).length := List.toFinset_card_le _
      _ ≤ (C.gates[w - 8]'(by omega)).inputs.length := List.length_filter_le _ _
      _ ≤ 2 := hg.2
  · simp

def reach (C : Circuit) (w : ℕ) : Finset ℕ :=
  insert w ((ch C w).attach.biUnion fun a => reach C a.1)
termination_by w
decreasing_by exact mem_ch_lt C w a.1 a.2

lemma mem_reach_self (C : Circuit) (w : ℕ) : w ∈ reach C w := by
  rw [reach]
  exact Finset.mem_insert_self _ _

lemma mem_reach_iff (C : Circuit) (w v : ℕ) :
    v ∈ reach C w ↔ v = w ∨ ∃ a ∈ ch C w, v ∈ reach C a := by
  conv_lhs => rw [reach]
  simp only [Finset.mem_insert, Finset.mem_biUnion, Finset.mem_attach, true_and, Subtype.exists,
    exists_prop]

lemma reach_subset_of_mem_ch (C : Circuit) (w a : ℕ) (ha : a ∈ ch C w) :
    reach C a ⊆ reach C w := by
  intro v hv
  exact (mem_reach_iff C w v).mpr (Or.inr ⟨a, ha, hv⟩)

lemma mem_reach_le (C : Circuit) : ∀ (w v : ℕ), v ∈ reach C w → v ≤ w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro v hv
    rcases (mem_reach_iff C w v).mp hv with rfl | ⟨a, ha, hva⟩
    · exact le_rfl
    · have hlt : a < w := mem_ch_lt C w a ha
      exact le_trans (ih a hlt v hva) (le_of_lt hlt)

lemma reach_trans (C : Circuit) :
    ∀ (w v u : ℕ), v ∈ reach C w → u ∈ reach C v → u ∈ reach C w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro v u hv hu
    rcases (mem_reach_iff C w v).mp hv with rfl | ⟨a, ha, hva⟩
    · exact hu
    · exact reach_subset_of_mem_ch C w a ha (ih a (mem_ch_lt C w a ha) v u hva hu)

lemma reach_erase_subset (C : Circuit) :
    ∀ w : ℕ, (reach C w).erase w ⊆ ((reach C w).filter (8 ≤ ·)).biUnion (ch C) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro v hv
    rw [Finset.mem_erase] at hv
    rcases (mem_reach_iff C w v).mp hv.2 with rfl | ⟨a, ha, hva⟩
    · exact absurd rfl hv.1
    · by_cases hveq : v = a
      · subst hveq
        have hw8 : 8 ≤ w := by
          unfold ch at ha
          split_ifs at ha with h
          · exact h.1
          · simp at ha
        exact Finset.mem_biUnion.mpr ⟨w, Finset.mem_filter.mpr ⟨mem_reach_self C w, hw8⟩, ha⟩
      · have hva' : v ∈ (reach C a).erase a := Finset.mem_erase.mpr ⟨hveq, hva⟩
        have hsub := ih a (mem_ch_lt C w a ha) hva'
        rcases Finset.mem_biUnion.mp hsub with ⟨u, hu, hvu⟩
        rw [Finset.mem_filter] at hu
        exact Finset.mem_biUnion.mpr
          ⟨u, Finset.mem_filter.mpr ⟨reach_subset_of_mem_ch C w a ha hu.1, hu.2⟩, hvu⟩

lemma val_mono_reach (C : Circuit) (hC : Monotone2 C) (x y : List Bool)
    (hx : x.length = 8) (hy : y.length = 8) :
    ∀ w : ℕ,
      (∀ i ∈ reach C w, i < 8 → x.getD i false = true → y.getD i false = true) →
      val C x w = true → val C y w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hxy hval
    by_cases hw8 : w < 8
    · rw [val_input C x hx w hw8] at hval
      rw [val_input C y hy w hw8]
      exact hxy w (mem_reach_self C w) hw8 hval
    · by_cases hwtop : w < 8 + C.gates.length
      · rw [val_gate C x hx w (by omega) hwtop] at hval
        rw [val_gate C y hy w (by omega) hwtop]
        set g := C.gates[w - 8]'(by omega)
        have hgop := (hC g (List.getElem_mem _)).1
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hgop
        have hstep : ∀ i ∈ g.inputs,
            (if i < w then val C x i else false) = true →
            (if i < w then val C y i else false) = true := by
          intro i hi hxi
          by_cases hil : i < w
          · simp only [hil, ↓reduceIte] at hxi ⊢
            have hmem : i ∈ ch C w := by
              unfold ch
              split_ifs with h
              · simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
                exact ⟨hi, hil⟩
              · omega
            exact ih i hil (fun k hk hk8 hxk =>
              hxy k (reach_subset_of_mem_ch C w i hmem hk) hk8 hxk) hxi
          · simp only [hil, ↓reduceIte] at hxi
            exact absurd hxi (by decide)
        rcases hgop with hop | hop
        · rw [hop] at hval ⊢
          simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq,
            forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at hval ⊢
          intro i hi
          exact hstep i hi (hval i hi)
        · rw [hop] at hval ⊢
          simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at hval ⊢
          rcases hval with ⟨_, ⟨i, hi, rfl⟩, hxi⟩
          exact ⟨_, ⟨i, hi, rfl⟩, hstep i hi hxi⟩
      · rw [val_ge C x hx w (by omega)] at hval
        exact absurd hval (by decide)

lemma val_congr_reach (C : Circuit) (hC : Monotone2 C) (x y : List Bool)
    (hx : x.length = 8) (hy : y.length = 8) (w : ℕ)
    (hxy : ∀ i ∈ reach C w, i < 8 → x.getD i false = y.getD i false) :
    val C x w = val C y w := by
  have h1 : val C x w = true → val C y w = true :=
    val_mono_reach C hC x y hx hy w (fun i hi hi8 hxi => by rw [← hxy i hi hi8]; exact hxi)
  have h2 : val C y w = true → val C x w = true :=
    val_mono_reach C hC y x hy hx w (fun i hi hi8 hyi => by rw [hxy i hi hi8]; exact hyi)
  cases hxval : val C x w <;> cases hyval : val C y w
  · rfl
  · exact absurd (h2 hyval) (by rw [hxval]; decide)
  · exact absurd (h1 hxval) (by rw [hyval]; decide)
  · rfl

lemma oe_len (u v : Fin 4) : (oe u v).length = 8 := by
  simp [oe, oneEach]

lemma input_essential (C : Circuit) (hC : Monotone2 C) (hrep : Represents targetA C)
    (i : ℕ) (u1 v1 u2 v2 : Fin 4)
    (h1 : targetA u1 v1 = true) (h2 : targetA u2 v2 = false)
    (hle : ∀ k : Fin 8, k.val ≠ i →
      (oe u1 v1).getD k.val false = true → (oe u2 v2).getD k.val false = true) :
    i ∈ reach C C.output := by
  by_contra hni
  have hmono := val_mono_reach C hC (oe u1 v1) (oe u2 v2)
    (oe_len u1 v1) (oe_len u2 v2) C.output (fun k hk hk8 hxk => by
      have hne : k ≠ i := fun heq => hni (heq ▸ hk)
      exact hle ⟨k, hk8⟩ hne hxk)
  have he1 : val C (oe u1 v1) C.output = true := by
    change C.eval (oneEach u1 v1) = true
    rw [hrep u1 v1, h1]
  have he2 : val C (oe u2 v2) C.output = true := hmono he1
  change C.eval (oneEach u2 v2) = true at he2
  rw [hrep u2 v2, h2] at he2
  exact absurd he2 (by decide)

lemma all_inputs_mem_reach (C : Circuit) (hC : Monotone2 C) (hrep : Represents targetA C) :
    Finset.range 8 ⊆ (reach C C.output).filter (· < 8) := by
  intro i hi
  rw [Finset.mem_range] at hi
  refine Finset.mem_filter.mpr ⟨?_, hi⟩
  match i, hi with
  | 0, _ => exact input_essential C hC hrep 0 0 0 1 0 (by decide) (by decide) (by decide)
  | 1, _ => exact input_essential C hC hrep 1 1 3 2 3 (by decide) (by decide) (by decide)
  | 2, _ => exact input_essential C hC hrep 2 2 2 1 2 (by decide) (by decide) (by decide)
  | 3, _ => exact input_essential C hC hrep 3 3 0 1 0 (by decide) (by decide) (by decide)
  | 4, _ => exact input_essential C hC hrep 4 3 0 3 1 (by decide) (by decide) (by decide)
  | 5, _ => exact input_essential C hC hrep 5 1 1 1 0 (by decide) (by decide) (by decide)
  | 6, _ => exact input_essential C hC hrep 6 2 2 2 0 (by decide) (by decide) (by decide)
  | 7, _ => exact input_essential C hC hrep 7 1 3 1 0 (by decide) (by decide) (by decide)
  | n + 8, h => omega

lemma disjoint_of_card_biUnion_eq {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (f : α → Finset β)
    (heq : (s.biUnion f).card = ∑ x ∈ s, (f x).card) :
    ∀ x ∈ s, ∀ y ∈ s, x ≠ y → Disjoint (f x) (f y) := by
  intro x hx y hy hxy
  rw [Finset.disjoint_left]
  intro z hzx hzy
  set s' := (s.erase x).erase y
  have hsu : s = insert x (insert y s') := by
    ext t
    simp only [s', Finset.mem_insert, Finset.mem_erase]
    constructor
    · intro ht
      by_cases htx : t = x
      · exact Or.inl htx
      · by_cases hty : t = y
        · exact Or.inr (Or.inl hty)
        · exact Or.inr (Or.inr ⟨hty, htx, ht⟩)
    · rintro (rfl | rfl | ⟨_, _, ht⟩)
      · exact hx
      · exact hy
      · exact ht
  have hx_ni : x ∉ insert y s' := by
    simp [s', hxy]
  have hy_ni : y ∉ s' := by
    simp [s']
  have hsum : ∑ u ∈ s, (f u).card = (f x).card + (f y).card + ∑ u ∈ s', (f u).card := by
    rw [hsu, Finset.sum_insert hx_ni, Finset.sum_insert hy_ni]
    omega
  have hbu : s.biUnion f = (f x ∪ f y) ∪ s'.biUnion f := by
    rw [hsu, Finset.biUnion_insert, Finset.biUnion_insert, Finset.union_assoc]
  have hlt_pair : (f x ∪ f y).card < (f x).card + (f y).card := by
    have h1 := Finset.card_union_add_card_inter (f x) (f y)
    have hpos : 0 < (f x ∩ f y).card :=
      Finset.card_pos.mpr ⟨z, Finset.mem_inter.mpr ⟨hzx, hzy⟩⟩
    omega
  have hle_rest : (s'.biUnion f).card ≤ ∑ u ∈ s', (f u).card := Finset.card_biUnion_le
  have hle_tot : (s.biUnion f).card ≤ (f x ∪ f y).card + (s'.biUnion f).card := by
    rw [hbu]
    exact Finset.card_union_le _ _
  omega

lemma exact_tree_structure (C : Circuit) (hC : Monotone2 C) (hsize : C.size ≤ 7)
    (hrep : Represents targetA C) :
    let G := (reach C C.output).filter (8 ≤ ·)
    (∀ u ∈ G, u < 8 + C.gates.length) ∧
    (∀ u ∈ G, (ch C u).card = 2) ∧
    (∀ u1 ∈ G, ∀ u2 ∈ G, u1 ≠ u2 → Disjoint (ch C u1) (ch C u2)) := by
  intro G
  set V := reach C C.output
  set I := V.filter (· < 8)
  have hI_eq : I = Finset.range 8 := by
    apply Finset.Subset.antisymm
    · intro x hx
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hx).2
    · exact all_inputs_mem_reach C hC hrep
  have hI_card : I.card = 8 := by rw [hI_eq, Finset.card_range]
  have hout_lt : C.output < 8 + C.gates.length := by
    by_contra hge
    have hch_empty : ch C C.output = ∅ := by
      unfold ch
      have hcond : ¬ (8 ≤ C.output ∧ C.output < 8 + C.gates.length) := by omega
      simp only [hcond, ↓reduceDIte]
    have hV_single : V = {C.output} := by
      change reach C C.output = {C.output}
      rw [reach, hch_empty]
      simp
    have h0 : 0 ∈ V := by
      have : 0 ∈ I := by rw [hI_eq]; decide
      exact (Finset.mem_filter.mp this).1
    rw [hV_single, Finset.mem_singleton] at h0
    omega
  have hG_lt : ∀ u ∈ G, u < 8 + C.gates.length := by
    intro u hu
    have hle : u ≤ C.output := mem_reach_le C C.output u (Finset.mem_filter.mp hu).1
    omega
  have hG_sub : G ⊆ Finset.Ico 8 (8 + C.gates.length) := by
    intro u hu
    exact Finset.mem_Ico.mpr ⟨(Finset.mem_filter.mp hu).2, hG_lt u hu⟩
  have hG_card_le : G.card ≤ 7 := by
    have h1 : G.card ≤ (Finset.Ico 8 (8 + C.gates.length)).card := Finset.card_le_card hG_sub
    rw [Nat.card_Ico] at h1
    simp only [Circuit.size] at hsize
    omega
  have hIG_union : I ∪ G = V := by
    ext x
    simp only [I, G, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
    · intro hx
      by_cases h8 : x < 8
      · exact Or.inl ⟨hx, h8⟩
      · exact Or.inr ⟨hx, by omega⟩
  have hIG_disj : Disjoint I G := by
    rw [Finset.disjoint_left]
    intro x hxI hxG
    have h1 := (Finset.mem_filter.mp hxI).2
    have h2 := (Finset.mem_filter.mp hxG).2
    omega
  have hV_card : V.card = 8 + G.card := by
    rw [← hIG_union, Finset.card_union_of_disjoint hIG_disj, hI_card]
  have herase_card : (V.erase C.output).card = 7 + G.card := by
    rw [Finset.card_erase_of_mem (mem_reach_self C C.output), hV_card]
    omega
  have hsub : V.erase C.output ⊆ G.biUnion (ch C) := reach_erase_subset C C.output
  have h1 : 7 + G.card ≤ (G.biUnion (ch C)).card := by
    rw [← herase_card]
    exact Finset.card_le_card hsub
  have h2 : (G.biUnion (ch C)).card ≤ ∑ u ∈ G, (ch C u).card := Finset.card_biUnion_le
  have h3 : ∑ u ∈ G, (ch C u).card ≤ ∑ _u ∈ G, 2 :=
    Finset.sum_le_sum (fun u _ => card_ch_le C hC u)
  have h4 : ∑ _u ∈ G, 2 = 2 * G.card := by
    rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have hbiUnion_eq : (G.biUnion (ch C)).card = ∑ u ∈ G, (ch C u).card := by omega
  have hsum_eq : ∑ u ∈ G, (ch C u).card = ∑ _u ∈ G, 2 := by omega
  refine ⟨hG_lt, ?_, disjoint_of_card_biUnion_eq G (ch C) hbiUnion_eq⟩
  have hall := (Finset.sum_eq_sum_iff_of_le (fun u _ => card_ch_le C hC u)).mp hsum_eq
  exact fun u hu => hall u hu

lemma gate_pair (C : Circuit) (hC : Monotone2 C) (u : ℕ)
    (hu8 : 8 ≤ u) (hult : u < 8 + C.gates.length) (hcard : (ch C u).card = 2) :
    ∃ a b : ℕ, a < u ∧ b < u ∧ a ≠ b ∧ (C.gates[u - 8]'(by omega)).inputs = [a, b] ∧
      ch C u = {a, b} := by
  set g := C.gates[u - 8]'(by omega)
  have hlen : g.inputs.length ≤ 2 := (hC g (List.getElem_mem _)).2
  have hch_eq : ch C u = (g.inputs.filter (· < u)).toFinset := by
    unfold ch
    split_ifs with h
    · rfl
    · omega
  rw [hch_eq] at hcard
  match hgin : g.inputs with
  | [] =>
    rw [hgin] at hcard
    simp at hcard
  | [a] =>
    rw [hgin] at hcard
    have : ([a].filter (· < u)).toFinset.card ≤ 1 := by
      calc ([a].filter (· < u)).toFinset.card
          ≤ ([a].filter (· < u)).length := List.toFinset_card_le _
        _ ≤ [a].length := List.length_filter_le _ _
        _ = 1 := rfl
    omega
  | [a, b] =>
    rw [hgin] at hcard
    have hcard_le : ([a, b].filter (· < u)).toFinset.card ≤ ([a, b].filter (· < u)).length :=
      List.toFinset_card_le _
    have hau : a < u := by
      by_contra ha
      have : ([a, b].filter (· < u)).length ≤ 1 := by
        simp only [List.filter, decide_eq_false ha]
        cases decide (b < u) <;> simp
      omega
    have hbu : b < u := by
      by_contra hb
      have : ([a, b].filter (· < u)).length ≤ 1 := by
        simp only [List.filter, decide_eq_false hb]
        cases decide (a < u) <;> simp
      omega
    have hflt : [a, b].filter (· < u) = [a, b] := by
      simp [List.filter, hau, hbu]
    rw [hflt] at hcard
    have hne : a ≠ b := by
      intro heq
      subst heq
      simp at hcard
    refine ⟨a, b, hau, hbu, hne, rfl, ?_⟩
    rw [hch_eq, hgin, hflt]
    ext x
    simp
  | a :: b :: c :: rest =>
    rw [hgin] at hlen
    simp at hlen

lemma exists_max_finset (S : Finset ℕ) (h : S.Nonempty) : ∃ m ∈ S, ∀ x ∈ S, x ≤ m := by
  induction S using Finset.induction_on with
  | empty => exact absurd h Finset.not_nonempty_empty
  | insert a s ha ih =>
    by_cases hs : s.Nonempty
    · obtain ⟨m, hm, hmax⟩ := ih hs
      by_cases ham : a ≤ m
      · refine ⟨m, Finset.mem_insert_of_mem hm, fun x hx => ?_⟩
        rcases Finset.mem_insert.mp hx with rfl | hxs
        · exact ham
        · exact hmax x hxs
      · refine ⟨a, Finset.mem_insert_self a s, fun x hx => ?_⟩
        rcases Finset.mem_insert.mp hx with rfl | hxs
        · exact le_rfl
        · exact le_trans (hmax x hxs) (by omega)
    · rw [Finset.not_nonempty_iff_eq_empty] at hs
      subst hs
      exact ⟨a, Finset.mem_singleton_self a, fun x hx => by
        rw [Finset.mem_singleton.mp hx]⟩

lemma disjoint_children_reach (C : Circuit)
    (hdisj_ch : ∀ u1 ∈ (reach C C.output).filter (8 ≤ ·),
      ∀ u2 ∈ (reach C C.output).filter (8 ≤ ·), u1 ≠ u2 → Disjoint (ch C u1) (ch C u2))
    (u a b : ℕ) (hu : u ∈ (reach C C.output).filter (8 ≤ ·))
    (ha : a ∈ ch C u) (hb : b ∈ ch C u) (hab : a ≠ b) :
    Disjoint (reach C a) (reach C b) := by
  rw [Finset.disjoint_left]
  intro z hza hzb
  set S := reach C a ∩ reach C b
  have hSne : S.Nonempty := ⟨z, Finset.mem_inter.mpr ⟨hza, hzb⟩⟩
  obtain ⟨m, hm, hmax⟩ := exists_max_finset S hSne
  have hma : m ∈ reach C a := (Finset.mem_inter.mp hm).1
  have hmb : m ∈ reach C b := (Finset.mem_inter.mp hm).2
  have hu_reach : u ∈ reach C C.output := (Finset.mem_filter.mp hu).1
  have hsub_a : reach C a ⊆ reach C C.output := fun x hx =>
    reach_trans C C.output u x hu_reach (reach_subset_of_mem_ch C u a ha hx)
  have hsub_b : reach C b ⊆ reach C C.output := fun x hx =>
    reach_trans C C.output u x hu_reach (reach_subset_of_mem_ch C u b hb hx)
  by_cases hmeqa : m = a
  · rw [hmeqa] at hmb
    have hmb' : a ∈ (reach C b).erase b := Finset.mem_erase.mpr ⟨hab, hmb⟩
    rcases Finset.mem_biUnion.mp (reach_erase_subset C b hmb') with ⟨u2, hu2, hmu2⟩
    have hu2G : u2 ∈ (reach C C.output).filter (8 ≤ ·) :=
      Finset.mem_filter.mpr ⟨hsub_b (Finset.mem_filter.mp hu2).1, (Finset.mem_filter.mp hu2).2⟩
    have hu2_lt : u2 < u := lt_of_le_of_lt (mem_reach_le C b u2 (Finset.mem_filter.mp hu2).1)
      (mem_ch_lt C u b hb)
    have hne : u ≠ u2 := by omega
    exact Finset.disjoint_left.mp (hdisj_ch u hu u2 hu2G hne) ha hmu2
  · by_cases hmeqb : m = b
    · rw [hmeqb] at hma
      have hma' : b ∈ (reach C a).erase a := Finset.mem_erase.mpr ⟨hab.symm, hma⟩
      rcases Finset.mem_biUnion.mp (reach_erase_subset C a hma') with ⟨u1, hu1, hmu1⟩
      have hu1G : u1 ∈ (reach C C.output).filter (8 ≤ ·) :=
        Finset.mem_filter.mpr ⟨hsub_a (Finset.mem_filter.mp hu1).1, (Finset.mem_filter.mp hu1).2⟩
      have hu1_lt : u1 < u := lt_of_le_of_lt (mem_reach_le C a u1 (Finset.mem_filter.mp hu1).1)
        (mem_ch_lt C u a ha)
      have hne : u ≠ u1 := by omega
      exact Finset.disjoint_left.mp (hdisj_ch u hu u1 hu1G hne) hb hmu1
    · have hma' : m ∈ (reach C a).erase a := Finset.mem_erase.mpr ⟨hmeqa, hma⟩
      have hmb' : m ∈ (reach C b).erase b := Finset.mem_erase.mpr ⟨hmeqb, hmb⟩
      rcases Finset.mem_biUnion.mp (reach_erase_subset C a hma') with ⟨u1, hu1, hmu1⟩
      rcases Finset.mem_biUnion.mp (reach_erase_subset C b hmb') with ⟨u2, hu2, hmu2⟩
      by_cases hu12 : u1 = u2
      · subst hu12
        have hu1S : u1 ∈ S :=
          Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp hu1).1, (Finset.mem_filter.mp hu2).1⟩
        have hle : u1 ≤ m := hmax u1 hu1S
        have hlt : m < u1 := mem_ch_lt C u1 m hmu1
        omega
      · have hu1G : u1 ∈ (reach C C.output).filter (8 ≤ ·) :=
          Finset.mem_filter.mpr ⟨hsub_a (Finset.mem_filter.mp hu1).1, (Finset.mem_filter.mp hu1).2⟩
        have hu2G : u2 ∈ (reach C C.output).filter (8 ≤ ·) :=
          Finset.mem_filter.mpr ⟨hsub_b (Finset.mem_filter.mp hu2).1, (Finset.mem_filter.mp hu2).2⟩
        exact Finset.disjoint_left.mp (hdisj_ch u1 hu1G u2 hu2G hu12) hmu1 hmu2

def z0 : List Bool := List.replicate 8 false

def eX (p : Fin 4) : List Bool := List.ofFn (fun i : Fin 8 => decide (i.val = p.val))

def eY (q : Fin 4) : List Bool := List.ofFn (fun i : Fin 8 => decide (i.val = 4 + q.val))

lemma z0_len : z0.length = 8 := by simp [z0]

lemma eX_len (p : Fin 4) : (eX p).length = 8 := by simp [eX]

lemma eY_len (q : Fin 4) : (eY q).length = 8 := by simp [eY]

lemma val_z0_false (C : Circuit) (hC : Monotone2 C)
    (hG_lt : ∀ u ∈ (reach C C.output).filter (8 ≤ ·), u < 8 + C.gates.length)
    (hG_card : ∀ u ∈ (reach C C.output).filter (8 ≤ ·), (ch C u).card = 2) :
    ∀ w : ℕ, w ∈ reach C C.output → val C z0 w = false := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hw8 : w < 8
    · rw [val_input C z0 z0_len w hw8]
      have key : ∀ k : Fin 8, z0.getD k.val false = false := by decide
      exact key ⟨w, hw8⟩
    · have hwG : w ∈ (reach C C.output).filter (8 ≤ ·) :=
        Finset.mem_filter.mpr ⟨hw, by omega⟩
      have hwlt := hG_lt w hwG
      obtain ⟨a, b, hau, hbu, _, hgin, hch⟩ :=
        gate_pair C hC w (by omega) hwlt (hG_card w hwG)
      have ha_mem : a ∈ reach C C.output :=
        reach_trans C C.output w a hw
          (reach_subset_of_mem_ch C w a (by rw [hch]; simp) (mem_reach_self C a))
      have hb_mem : b ∈ reach C C.output :=
        reach_trans C C.output w b hw
          (reach_subset_of_mem_ch C w b (by rw [hch]; simp) (mem_reach_self C b))
      have hva := ih a hau ha_mem
      have hvb := ih b hbu hb_mem
      rw [val_gate C z0 z0_len w (by omega) hwlt, hgin]
      have hgop := (hC (C.gates[w - 8]'(by omega)) (List.getElem_mem _)).1
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hgop
      rcases hgop with hop | hop <;> simp [hop, GateOp.eval, hau, hbu, hva, hvb]

lemma oe_getD_eq_eX (p q : Fin 4) (i : ℕ) (hi : i < 8) (hne : i ≠ 4 + q.val) :
    (oe p q).getD i false = (eX p).getD i false := by
  have key : ∀ (p q : Fin 4) (k : Fin 8), k.val ≠ 4 + q.val →
      (oe p q).getD k.val false = (eX p).getD k.val false := by decide
  exact key p q ⟨i, hi⟩ hne

lemma oe_getD_eq_eY (p q : Fin 4) (i : ℕ) (hi : i < 8) (hne : i ≠ p.val) :
    (oe p q).getD i false = (eY q).getD i false := by
  have key : ∀ (p q : Fin 4) (k : Fin 8), k.val ≠ p.val →
      (oe p q).getD k.val false = (eY q).getD k.val false := by decide
  exact key p q ⟨i, hi⟩ hne

lemma oe_getD_eq_z0 (p q : Fin 4) (i : ℕ) (hi : i < 8)
    (hne1 : i ≠ p.val) (hne2 : i ≠ 4 + q.val) :
    (oe p q).getD i false = z0.getD i false := by
  have key : ∀ (p q : Fin 4) (k : Fin 8), k.val ≠ p.val → k.val ≠ 4 + q.val →
      (oe p q).getD k.val false = z0.getD k.val false := by decide
  exact key p q ⟨i, hi⟩ hne1 hne2

lemma oe_true_mem_or (C : Circuit) (hC : Monotone2 C)
    (hz : ∀ w ∈ reach C C.output, val C z0 w = false)
    (w : ℕ) (hw : w ∈ reach C C.output) (p q : Fin 4)
    (ht : val C (oe p q) w = true) :
    p.val ∈ reach C w ∨ 4 + q.val ∈ reach C w := by
  by_contra h
  have h1 : p.val ∉ reach C w := fun hp => h (Or.inl hp)
  have h2 : 4 + q.val ∉ reach C w := fun hq => h (Or.inr hq)
  have heq : val C (oe p q) w = val C z0 w :=
    val_congr_reach C hC (oe p q) z0 (oe_len p q) z0_len w (fun i hi hi8 =>
      oe_getD_eq_z0 p q i hi8 (fun he => h1 (he ▸ hi)) (fun he => h2 (he ▸ hi)))
  rw [hz w hw] at heq
  rw [ht] at heq
  exact absurd heq (by decide)

lemma oe_true_mem_and (C : Circuit) (hC : Monotone2 C)
    (w : ℕ) (p q : Fin 4)
    (hx : val C (eX p) w = false) (hy : val C (eY q) w = false)
    (ht : val C (oe p q) w = true) :
    p.val ∈ reach C w ∧ 4 + q.val ∈ reach C w := by
  constructor
  · by_contra hp
    have heq : val C (oe p q) w = val C (eY q) w :=
      val_congr_reach C hC (oe p q) (eY q) (oe_len p q) (eY_len q) w (fun i hi hi8 =>
        oe_getD_eq_eY p q i hi8 (fun he => hp (he ▸ hi)))
    rw [hy, ht] at heq
    exact absurd heq (by decide)
  · by_contra hq
    have heq : val C (oe p q) w = val C (eX p) w :=
      val_congr_reach C hC (oe p q) (eX p) (oe_len p q) (eX_len p) w (fun i hi hi8 =>
        oe_getD_eq_eX p q i hi8 (fun he => hq (he ▸ hi)))
    rw [hx, ht] at heq
    exact absurd heq (by decide)

lemma and_p4_contra (C : Circuit) (hC : Monotone2 C)
    (hz : ∀ w ∈ reach C C.output, val C z0 w = false)
    (a b : ℕ) (ha_mem : a ∈ reach C C.output) (hb_mem : b ∈ reach C C.output)
    (hdisj : Disjoint (reach C a) (reach C b))
    (ha11 : val C (oe 1 1) a = true) (hb11 : val C (oe 1 1) b = true)
    (ha21 : val C (oe 2 1) a = true)
    (hb22 : val C (oe 2 2) b = true)
    (h12 : (val C (oe 1 2) a && val C (oe 1 2) b) = false)
    (h1a : 1 ∈ reach C a) : False := by
  have h1nb : 1 ∉ reach C b := Finset.disjoint_left.mp hdisj h1a
  have h5b : 5 ∈ reach C b := by
    rcases oe_true_mem_or C hC hz b hb_mem 1 1 hb11 with h | h
    · exact absurd h h1nb
    · exact h
  have h5na : 5 ∉ reach C a := Finset.disjoint_right.mp hdisj h5b
  have h2a : 2 ∈ reach C a := by
    rcases oe_true_mem_or C hC hz a ha_mem 2 1 ha21 with h | h
    · exact h
    · exact absurd h h5na
  have h2nb : 2 ∉ reach C b := Finset.disjoint_left.mp hdisj h2a
  have h6b : 6 ∈ reach C b := by
    rcases oe_true_mem_or C hC hz b hb_mem 2 2 hb22 with h | h
    · exact absurd h h2nb
    · exact h
  have h6na : 6 ∉ reach C a := Finset.disjoint_right.mp hdisj h6b
  have ha12 : val C (oe 1 2) a = true := by
    have heq : val C (oe 1 2) a = val C (oe 1 1) a :=
      val_congr_reach C hC (oe 1 2) (oe 1 1) (oe_len 1 2) (oe_len 1 1) a
        (fun i hi hi8 => by
          have hne5 : i ≠ 5 := fun he => h5na (he ▸ hi)
          have hne6 : i ≠ 6 := fun he => h6na (he ▸ hi)
          have key : ∀ k : Fin 8, k.val ≠ 5 → k.val ≠ 6 →
              (oe 1 2).getD k.val false = (oe 1 1).getD k.val false := by decide
          exact key ⟨i, hi8⟩ hne5 hne6)
    rw [heq, ha11]
  have hb12 : val C (oe 1 2) b = true := by
    have heq : val C (oe 1 2) b = val C (oe 2 2) b :=
      val_congr_reach C hC (oe 1 2) (oe 2 2) (oe_len 1 2) (oe_len 2 2) b
        (fun i hi hi8 => by
          have hne1 : i ≠ 1 := fun he => h1nb (he ▸ hi)
          have hne2 : i ≠ 2 := fun he => h2nb (he ▸ hi)
          have key : ∀ k : Fin 8, k.val ≠ 1 → k.val ≠ 2 →
              (oe 1 2).getD k.val false = (oe 2 2).getD k.val false := by decide
          exact key ⟨i, hi8⟩ hne1 hne2)
    rw [heq, hb22]
  rw [ha12, hb12] at h12
  exact absurd h12 (by decide)

lemma no_p4 (C : Circuit) (hC : Monotone2 C)
    (hG_lt : ∀ u ∈ (reach C C.output).filter (8 ≤ ·), u < 8 + C.gates.length)
    (hG_card : ∀ u ∈ (reach C C.output).filter (8 ≤ ·), (ch C u).card = 2)
    (hdisj_ch : ∀ u1 ∈ (reach C C.output).filter (8 ≤ ·),
      ∀ u2 ∈ (reach C C.output).filter (8 ≤ ·), u1 ≠ u2 → Disjoint (ch C u1) (ch C u2))
    (hz : ∀ w ∈ reach C C.output, val C z0 w = false) :
    ∀ w : ℕ, w ∈ reach C C.output →
      val C (eX 1) w = false →
      val C (eX 2) w = false →
      val C (eY 1) w = false →
      val C (eY 2) w = false →
      val C (oe 1 1) w = true →
      val C (oe 2 1) w = true →
      val C (oe 2 2) w = true →
      val C (oe 1 2) w = false →
      False := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hx1 hx2 hy1 hy2 h11 h21 h22 h12
    by_cases hw8 : w < 8
    · rw [val_input C (eX 1) (eX_len 1) w hw8] at hx1
      rw [val_input C (eX 2) (eX_len 2) w hw8] at hx2
      rw [val_input C (eY 1) (eY_len 1) w hw8] at hy1
      rw [val_input C (eY 2) (eY_len 2) w hw8] at hy2
      rw [val_input C (oe 1 1) (oe_len 1 1) w hw8] at h11
      have key : ∀ k : Fin 8,
          (eX 1).getD k.val false = false →
          (eX 2).getD k.val false = false →
          (eY 1).getD k.val false = false →
          (eY 2).getD k.val false = false →
          (oe 1 1).getD k.val false = true → False := by decide
      exact key ⟨w, hw8⟩ hx1 hx2 hy1 hy2 h11
    · have hwG : w ∈ (reach C C.output).filter (8 ≤ ·) :=
        Finset.mem_filter.mpr ⟨hw, by omega⟩
      have hwlt := hG_lt w hwG
      obtain ⟨a, b, hau, hbu, hab, hgin, hch⟩ :=
        gate_pair C hC w (by omega) hwlt (hG_card w hwG)
      have ha_ch : a ∈ ch C w := by rw [hch]; simp
      have hb_ch : b ∈ ch C w := by rw [hch]; simp
      have ha_mem : a ∈ reach C C.output :=
        reach_trans C C.output w a hw (reach_subset_of_mem_ch C w a ha_ch (mem_reach_self C a))
      have hb_mem : b ∈ reach C C.output :=
        reach_trans C C.output w b hw (reach_subset_of_mem_ch C w b hb_ch (mem_reach_self C b))
      have hdisj : Disjoint (reach C a) (reach C b) :=
        disjoint_children_reach C hdisj_ch w a b hwG ha_ch hb_ch hab
      have hgop := (hC (C.gates[w - 8]'(by omega)) (List.getElem_mem _)).1
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hgop
      have heval : ∀ (x : List Bool), x.length = 8 →
          val C x w = (C.gates[w - 8]'(by omega)).op.eval [val C x a, val C x b] := by
        intro x hxlen
        rw [val_gate C x hxlen w (by omega) hwlt, hgin]
        simp [hau, hbu]
      rcases hgop with hop | hop
      · have hband : ∀ (x : List Bool), x.length = 8 →
            val C x w = (val C x a && val C x b) := by
          intro x hxlen
          rw [heval x hxlen, hop]
          simp [GateOp.eval]
        rw [hband _ (oe_len 1 1), Bool.and_eq_true] at h11
        rw [hband _ (oe_len 2 1), Bool.and_eq_true] at h21
        rw [hband _ (oe_len 2 2), Bool.and_eq_true] at h22
        rw [hband _ (oe_len 1 2)] at h12
        by_cases h1a : 1 ∈ reach C a
        · exact and_p4_contra C hC hz a b ha_mem hb_mem hdisj
            h11.1 h11.2 h21.1 h22.2 h12 h1a
        · have h5a : 5 ∈ reach C a := by
            rcases oe_true_mem_or C hC hz a ha_mem 1 1 h11.1 with h | h
            · exact absurd h h1a
            · exact h
          have h5nb : 5 ∉ reach C b := Finset.disjoint_left.mp hdisj h5a
          have h1b : 1 ∈ reach C b := by
            rcases oe_true_mem_or C hC hz b hb_mem 1 1 h11.2 with h | h
            · exact h
            · exact absurd h h5nb
          rw [Bool.and_comm] at h12
          exact and_p4_contra C hC hz b a hb_mem ha_mem hdisj.symm
            h11.2 h11.1 h21.2 h22.1 h12 h1b
      · have hbor : ∀ (x : List Bool), x.length = 8 →
            val C x w = (val C x a || val C x b) := by
          intro x hxlen
          rw [heval x hxlen, hop]
          simp [GateOp.eval]
        rw [hbor _ (eX_len 1), Bool.or_eq_false_iff] at hx1
        rw [hbor _ (eX_len 2), Bool.or_eq_false_iff] at hx2
        rw [hbor _ (eY_len 1), Bool.or_eq_false_iff] at hy1
        rw [hbor _ (eY_len 2), Bool.or_eq_false_iff] at hy2
        rw [hbor _ (oe_len 1 2), Bool.or_eq_false_iff] at h12
        rw [hbor _ (oe_len 1 1), Bool.or_eq_true] at h11
        rw [hbor _ (oe_len 2 1), Bool.or_eq_true] at h21
        rw [hbor _ (oe_len 2 2), Bool.or_eq_true] at h22
        rcases h11 with ha11 | hb11
        · have h5a : 5 ∈ reach C a := (oe_true_mem_and C hC a 1 1 hx1.1 hy1.1 ha11).2
          have h5nb : 5 ∉ reach C b := Finset.disjoint_left.mp hdisj h5a
          have ha21 : val C (oe 2 1) a = true := by
            rcases h21 with h | h
            · exact h
            · exact absurd (oe_true_mem_and C hC b 2 1 hx2.2 hy1.2 h).2 h5nb
          have h2a : 2 ∈ reach C a := (oe_true_mem_and C hC a 2 1 hx2.1 hy1.1 ha21).1
          have h2nb : 2 ∉ reach C b := Finset.disjoint_left.mp hdisj h2a
          have ha22 : val C (oe 2 2) a = true := by
            rcases h22 with h | h
            · exact h
            · exact absurd (oe_true_mem_and C hC b 2 2 hx2.2 hy2.2 h).1 h2nb
          exact ih a hau ha_mem hx1.1 hx2.1 hy1.1 hy2.1 ha11 ha21 ha22 h12.1
        · have h5b : 5 ∈ reach C b := (oe_true_mem_and C hC b 1 1 hx1.2 hy1.2 hb11).2
          have h5na : 5 ∉ reach C a := Finset.disjoint_right.mp hdisj h5b
          have hb21 : val C (oe 2 1) b = true := by
            rcases h21 with h | h
            · exact absurd (oe_true_mem_and C hC a 2 1 hx2.1 hy1.1 h).2 h5na
            · exact h
          have h2b : 2 ∈ reach C b := (oe_true_mem_and C hC b 2 1 hx2.2 hy1.2 hb21).1
          have h2na : 2 ∉ reach C a := Finset.disjoint_right.mp hdisj h2b
          have hb22 : val C (oe 2 2) b = true := by
            rcases h22 with h | h
            · exact absurd (oe_true_mem_and C hC a 2 2 hx2.1 hy2.1 h).1 h2na
            · exact h
          exact ih b hbu hb_mem hx1.2 hx2.2 hy1.2 hy2.2 hb11 hb21 hb22 h12.2

lemma val_le_false (C : Circuit) (hC : Monotone2 C) (hrep : Represents targetA C)
    (x : List Bool) (hx : x.length = 8) (u v : Fin 4)
    (hf : targetA u v = false)
    (hle : ∀ k : Fin 8, x.getD k.val false = true → (oe u v).getD k.val false = true) :
    val C x C.output = false := by
  cases h : val C x C.output
  · rfl
  · have hmono := val_mono_reach C hC x (oe u v) hx (oe_len u v) C.output
      (fun k _ hk8 hxk => hle ⟨k, hk8⟩ hxk) h
    change C.eval (oneEach u v) = true at hmono
    rw [hrep u v, hf] at hmono
    exact absurd hmono (by decide)

lemma lower : ¬ RepSizeAtMost targetA 7 := by
  rintro ⟨C, hC, hsize, hrep⟩
  obtain ⟨hG_lt, hG_card, hdisj_ch⟩ := exact_tree_structure C hC hsize hrep
  have hz := val_z0_false C hC hG_lt hG_card
  have hx1 : val C (eX 1) C.output = false :=
    val_le_false C hC hrep (eX 1) (eX_len 1) 1 0 (by decide) (by decide)
  have hx2 : val C (eX 2) C.output = false :=
    val_le_false C hC hrep (eX 2) (eX_len 2) 2 0 (by decide) (by decide)
  have hy1 : val C (eY 1) C.output = false :=
    val_le_false C hC hrep (eY 1) (eY_len 1) 3 1 (by decide) (by decide)
  have hy2 : val C (eY 2) C.output = false :=
    val_le_false C hC hrep (eY 2) (eY_len 2) 3 2 (by decide) (by decide)
  have h11 : val C (oe 1 1) C.output = true := by
    change C.eval (oneEach (1 : Fin 4) (1 : Fin 4)) = true; rw [hrep 1 1]; decide
  have h21 : val C (oe 2 1) C.output = true := by
    change C.eval (oneEach (2 : Fin 4) (1 : Fin 4)) = true; rw [hrep 2 1]; decide
  have h22 : val C (oe 2 2) C.output = true := by
    change C.eval (oneEach (2 : Fin 4) (2 : Fin 4)) = true; rw [hrep 2 2]; decide
  have h12 : val C (oe 1 2) C.output = false := by
    change C.eval (oneEach (1 : Fin 4) (2 : Fin 4)) = false; rw [hrep 1 2]; decide
  exact no_p4 C hC hG_lt hG_card hdisj_ch hz C.output (mem_reach_self C C.output)
    hx1 hx2 hy1 hy2 h11 h21 h22 h12

end PEqualNP.Outside.L_meta_6088

theorem PEqualNP.Outside.L_meta_6088 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (5807 : ℕ).testBit (4 * u.val + v.val)) 8 ∧
  ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (5807 : ℕ).testBit (4 * u.val + v.val)) 7 := by
  exact ⟨PEqualNP.Outside.L_meta_6088.upper, PEqualNP.Outside.L_meta_6088.lower⟩
