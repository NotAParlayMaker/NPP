import PEqualNP.Defs
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Pigeonhole

namespace PEqualNP.Outside

open PEqualNP.CircuitLowerBounds

private def wiresPrefix (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

private lemma wiresPrefix_nil (x : List Bool) : wiresPrefix [] x = x := rfl

private lemma wiresPrefix_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    wiresPrefix (g :: gs) x =
      wiresPrefix gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) := rfl

private lemma wiresPrefix_append (gs1 gs2 : List Gate) (x : List Bool) :
    wiresPrefix (gs1 ++ gs2) x = wiresPrefix gs2 (wiresPrefix gs1 x) := by
  simp [wiresPrefix, List.foldl_append]

private lemma wiresPrefix_length (gs : List Gate) (x : List Bool) :
    (wiresPrefix gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [wiresPrefix]
  | cons g gs ih =>
    rw [wiresPrefix_cons, ih]
    simp
    omega

private lemma getD_append_left_of_lt {α : Type*} (l1 l2 : List α) (d : α) {k : ℕ}
    (hk : k < l1.length) : (l1 ++ l2).getD k d = l1.getD k d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hk]

private lemma getD_of_length_le {α : Type*} (l : List α) (d : α) {k : ℕ}
    (hk : l.length ≤ k) : l.getD k d = d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hk]

private lemma wiresPrefix_getD_prefix (gs : List Gate) (x : List Bool) {k : ℕ}
    (hk : k < x.length) : (wiresPrefix gs x).getD k false = x.getD k false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [wiresPrefix_cons]
    have hk' : k < (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]).length := by
      simp
      omega
    rw [ih _ hk', getD_append_left_of_lt _ _ _ hk]

private lemma wiresPrefix_getD_of_take (gs : List Gate) (x : List Bool) (j k : ℕ)
    (hk : k < x.length + min j gs.length) :
    (wiresPrefix gs x).getD k false = (wiresPrefix (gs.take j) x).getD k false := by
  have hsplit : gs = gs.take j ++ gs.drop j := (List.take_append_drop j gs).symm
  conv_lhs => rw [hsplit, wiresPrefix_append]
  apply wiresPrefix_getD_prefix
  rw [wiresPrefix_length, List.length_take]
  omega

private lemma wiresPrefix_getD_gate (gs : List Gate) (x : List Bool) (j : ℕ) (hj : j < gs.length) :
    (wiresPrefix gs x).getD (x.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i => (wiresPrefix (gs.take j) x).getD i false) := by
  have hsplit : gs = gs.take j ++ [gs[j]] ++ gs.drop (j + 1) := by
    have h1 : gs.take (j + 1) = gs.take j ++ [gs[j]] := List.take_succ_eq_append_getElem hj
    rw [← h1, List.take_append_drop]
  conv_lhs => rw [hsplit, wiresPrefix_append]
  have hlen_take : (wiresPrefix (gs.take j) x).length = x.length + j := by
    rw [wiresPrefix_length, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  have hlt : x.length + j < (wiresPrefix (gs.take j ++ [gs[j]]) x).length := by
    rw [wiresPrefix_length, List.length_append, List.length_take,
      Nat.min_eq_left (Nat.le_of_lt hj)]
    simp
  rw [wiresPrefix_getD_prefix _ _ hlt, wiresPrefix_append, wiresPrefix_cons, wiresPrefix_nil]
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by omega), hlen_take, Nat.sub_self]
  simp

private lemma gate_eval_mono (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (w1 w2 : List Bool)
    (hle : ∀ k, w1.getD k false = true → w2.getD k false = true) :
    g.op.eval (g.inputs.map fun i => w1.getD i false) = true →
      g.op.eval (g.inputs.map fun i => w2.getD i false) = true := by
  rcases hop with h | h <;> rw [h]
  · simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq, forall_exists_index,
      and_imp, forall_apply_eq_imp_iff₂]
    intro h1 i hi
    exact hle i (h1 i hi)
  · simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
    rintro ⟨b, ⟨i, hi, rfl⟩, hb⟩
    exact ⟨w2.getD i false, ⟨i, hi, rfl⟩, hle i hb⟩

private lemma wiresPrefix_mono (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (w1 w2 : List Bool) (hlen : w1.length = w2.length)
    (hle : ∀ k, w1.getD k false = true → w2.getD k false = true) :
    ∀ k, (wiresPrefix gs w1).getD k false = true → (wiresPrefix gs w2).getD k false = true := by
  induction gs generalizing w1 w2 with
  | nil => exact hle
  | cons g gs ih =>
    rw [wiresPrefix_cons, wiresPrefix_cons]
    apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem g hg'))
    · simp [hlen]
    · intro k hk
      by_cases hkl : k < w1.length
      · rw [getD_append_left_of_lt _ _ _ hkl] at hk
        rw [getD_append_left_of_lt _ _ _ (hlen ▸ hkl)]
        exact hle k hk
      · by_cases hke : k = w1.length
        · subst hke
          simp only [List.getD_eq_getElem?_getD] at hk ⊢
          rw [List.getElem?_append_right (le_refl _), Nat.sub_self] at hk
          rw [List.getElem?_append_right (by omega), hlen, Nat.sub_self]
          simp only [List.getElem?_cons_zero, Option.getD_some] at hk ⊢
          exact gate_eval_mono g (hgs g List.mem_cons_self) w1 w2 hle hk
        · have hgt : (w1 ++ [g.op.eval (g.inputs.map fun i => w1.getD i false)]).length ≤ k := by
            simp
            omega
          rw [getD_of_length_le _ _ hgt] at hk
          cases hk

private def fanoLines : Fin 4 → Finset (Fin 7) :=
  ![{0, 1, 2}, {0, 3, 4}, {0, 5, 6}, {1, 3, 5}]

private lemma fanoLines_card (i : Fin 4) : (fanoLines i).card = 3 := by
  fin_cases i <;> decide

private lemma fanoLines_inter_le (i j : Fin 4) (hij : i ≠ j) :
    (fanoLines i ∩ fanoLines j).card ≤ 1 := by
  fin_cases i <;> fin_cases j <;> simp_all [fanoLines] <;> decide

private lemma fanoLines_inj (i j : Fin 4) (h : fanoLines i = fanoLines j) : i = j := by
  by_contra hij
  have h1 := fanoLines_inter_le i j hij
  rw [h, Finset.inter_self, fanoLines_card] at h1
  omega

private def wireSupp (gs : List Gate) (w : ℕ) : Finset (Fin 7) :=
  Finset.univ.filter fun p : Fin 7 =>
    (wiresPrefix gs (List.ofFn fun q : Fin 7 => decide (q = p))).getD w false = true

private lemma wireSupp_input (gs : List Gate) {w : ℕ} (hw : w < 7) :
    wireSupp gs w = {⟨w, hw⟩} := by
  ext p
  simp only [wireSupp, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  have hlen : (List.ofFn fun q : Fin 7 => decide (q = p)).length = 7 := by simp
  rw [wiresPrefix_getD_prefix gs _ (by omega)]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hw, Option.getD_some,
    decide_eq_true_eq]
  constructor
  · intro h
    exact h.symm
  · intro h
    exact h.symm

private lemma wireSupp_of_ge (gs : List Gate) {w : ℕ} (hw : 7 + gs.length ≤ w) :
    wireSupp gs w = ∅ := by
  ext p
  simp only [wireSupp, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
    iff_false]
  have hlen : (wiresPrefix gs (List.ofFn fun q : Fin 7 => decide (q = p))).length ≤ w := by
    rw [wiresPrefix_length]
    simp
    omega
  rw [getD_of_length_le _ _ hlen]
  decide

private lemma wireSupp_take_eq (gs : List Gate) (j w : ℕ) (hj : j ≤ gs.length)
    (hw : w < 7 + j) :
    wireSupp (gs.take j) w = wireSupp gs w := by
  ext p
  simp only [wireSupp, Finset.mem_filter, Finset.mem_univ, true_and]
  have hlen : (List.ofFn fun q : Fin 7 => decide (q = p)).length = 7 := by simp
  have hlt : w < (List.ofFn fun q : Fin 7 => decide (q = p)).length + min j gs.length := by
    rw [hlen, Nat.min_eq_left hj]
    exact hw
  rw [wiresPrefix_getD_of_take gs _ j w hlt]

theorem L_meta_275 :
    ¬ ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin 4 → ℕ),
      C.size ≤ 7 ∧
      (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∧
      ∀ i : Fin 4,
        (∀ p : Fin 7,
          (C.wires (List.ofFn (fun q : Fin 7 => decide (q = p)))).getD (o i) false = true ↔
            p ∈ (![{0, 1, 2}, {0, 3, 4}, {0, 5, 6}, {1, 3, 5}] : Fin 4 → Finset (Fin 7)) i) ∧
        ∀ x : Fin 7 → Bool,
          (Finset.univ.filter (fun q : Fin 7 => x q = true)).card ≤ 2 →
          (∀ q ∈ (![{0, 1, 2}, {0, 3, 4}, {0, 5, 6}, {1, 3, 5}] : Fin 4 → Finset (Fin 7)) i,
            x q = false) →
          (C.wires (List.ofFn x)).getD (o i) false = false := by
  rintro ⟨C, o, hsize, hgates, hout⟩
  have hsupp_o : ∀ i : Fin 4, wireSupp C.gates (o i) = fanoLines i := by
    intro i
    ext p
    simp only [wireSupp, Finset.mem_filter, Finset.mem_univ, true_and]
    exact (hout i).1 p
  have ho_bounds : ∀ i : Fin 4, 7 ≤ o i ∧ o i < 7 + C.gates.length := by
    intro i
    constructor
    · by_contra hlt
      have hw : o i < 7 := by omega
      have hcard := congrArg Finset.card (hsupp_o i)
      rw [wireSupp_input C.gates hw, Finset.card_singleton, fanoLines_card] at hcard
      omega
    · by_contra hge
      have hw : 7 + C.gates.length ≤ o i := by omega
      have hcard := congrArg Finset.card (hsupp_o i)
      rw [wireSupp_of_ge C.gates hw, Finset.card_empty, fanoLines_card] at hcard
      omega
  have ho_inj : Function.Injective o := by
    intro i j hij
    apply fanoLines_inj
    rw [← hsupp_o i, ← hsupp_o j, hij]
  have hgate_witness :
      ∀ i : Fin 4, ∃ u : ℕ, 7 ≤ u ∧ u < o i ∧ wireSupp C.gates u ⊆ fanoLines i ∧
        2 ≤ (wireSupp C.gates u).card := by
    intro i
    have hge7 : 7 ≤ o i := (ho_bounds i).1
    have hlt_end : o i < 7 + C.gates.length := (ho_bounds i).2
    let j : ℕ := o i - 7
    have hj : j < C.gates.length := by omega
    have hoi_eq : o i = 7 + j := by omega
    let g : Gate := C.gates[j]
    have hg_mem : g ∈ C.gates := List.getElem_mem hj
    have hg_spec := hgates g hg_mem
    rcases hg_spec with ⟨hg_op, hg_len⟩
    rcases h_in : g.inputs with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
    · simp [h_in] at hg_len
    · simp [h_in] at hg_len
    · have heval : ∀ x : Fin 7 → Bool,
          (wiresPrefix C.gates (List.ofFn x)).getD (o i) false =
            g.op.eval
              [(wiresPrefix (C.gates.take j) (List.ofFn x)).getD a false,
               (wiresPrefix (C.gates.take j) (List.ofFn x)).getD b false] := by
        intro x
        have hlenx : (List.ofFn x).length = 7 := by simp
        have h1 := wiresPrefix_getD_gate C.gates (List.ofFn x) j hj
        rw [hlenx, ← hoi_eq] at h1
        rw [h1]
        simp [g, h_in]
      rcases hg_op with hop_and | hop_or
      · have hsub_a : fanoLines i ⊆ wireSupp (C.gates.take j) a := by
          intro p hp
          have hp' : (wiresPrefix C.gates (List.ofFn fun q : Fin 7 => decide (q = p))).getD (o i) false = true :=
            ((hout i).1 p).mpr hp
          rw [heval, hop_and] at hp'
          simp only [GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true,
            Bool.and_eq_true] at hp'
          simp only [wireSupp, Finset.mem_filter, Finset.mem_univ, true_and]
          exact hp'.1
        have hsub_b : fanoLines i ⊆ wireSupp (C.gates.take j) b := by
          intro p hp
          have hp' : (wiresPrefix C.gates (List.ofFn fun q : Fin 7 => decide (q = p))).getD (o i) false = true :=
            ((hout i).1 p).mpr hp
          rw [heval, hop_and] at hp'
          simp only [GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true,
            Bool.and_eq_true] at hp'
          simp only [wireSupp, Finset.mem_filter, Finset.mem_univ, true_and]
          exact hp'.2
        have hclean : wireSupp (C.gates.take j) a ⊆ fanoLines i ∨
            wireSupp (C.gates.take j) b ⊆ fanoLines i := by
          by_contra hboth
          rw [not_or] at hboth
          rcases Finset.not_subset.mp hboth.1 with ⟨pa, hpa_in, hpa_not⟩
          rcases Finset.not_subset.mp hboth.2 with ⟨pb, hpb_in, hpb_not⟩
          let x : Fin 7 → Bool := fun q => decide (q = pa ∨ q = pb)
          have hx_card : (Finset.univ.filter fun q : Fin 7 => x q = true).card ≤ 2 := by
            have hsubx : (Finset.univ.filter fun q : Fin 7 => x q = true) ⊆ {pa, pb} := by
              intro q hq
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, x,
                decide_eq_true_eq] at hq
              simp [hq]
            exact le_trans (Finset.card_le_card hsubx) (Finset.card_le_two)
          have hx_zero : ∀ q ∈ fanoLines i, x q = false := by
            intro q hq
            simp only [x, decide_eq_false_iff_not, not_or]
            exact ⟨fun h => hpa_not (h ▸ hq), fun h => hpb_not (h ▸ hq)⟩
          have ho_false : (wiresPrefix C.gates (List.ofFn x)).getD (o i) false = false :=
            (hout i).2 x hx_card hx_zero
          have htake_ops : ∀ g' ∈ C.gates.take j,
              g'.op = GateOp.and ∨ g'.op = GateOp.or :=
            fun g' hg' => (hgates g' (List.mem_of_mem_take hg')).1
          have ha_true : (wiresPrefix (C.gates.take j) (List.ofFn x)).getD a false = true := by
            apply wiresPrefix_mono (C.gates.take j) htake_ops
              (List.ofFn fun q : Fin 7 => decide (q = pa)) (List.ofFn x)
            · simp
            · intro k hk
              by_cases hk7 : k < 7
              · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hk7,
                  Option.getD_some, x, decide_eq_true_eq] at hk ⊢
                exact Or.inl hk
              · rw [getD_of_length_le _ _ (by simp; omega)] at hk
                cases hk
            · simp only [wireSupp, Finset.mem_filter, Finset.mem_univ, true_and] at hpa_in
              exact hpa_in
          have hb_true : (wiresPrefix (C.gates.take j) (List.ofFn x)).getD b false = true := by
            apply wiresPrefix_mono (C.gates.take j) htake_ops
              (List.ofFn fun q : Fin 7 => decide (q = pb)) (List.ofFn x)
            · simp
            · intro k hk
              by_cases hk7 : k < 7
              · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hk7,
                  Option.getD_some, x, decide_eq_true_eq] at hk ⊢
                exact Or.inr hk
              · rw [getD_of_length_le _ _ (by simp; omega)] at hk
                cases hk
            · simp only [wireSupp, Finset.mem_filter, Finset.mem_univ, true_and] at hpb_in
              exact hpb_in
          rw [heval, hop_and, ha_true, hb_true] at ho_false
          simp [GateOp.eval] at ho_false
        rcases hclean with ha_sub | hb_sub
        · have ha_eq : wireSupp (C.gates.take j) a = fanoLines i :=
            Finset.Subset.antisymm ha_sub hsub_a
          have ha_lt : a < 7 + j := by
            by_contra hge
            have hge' : 7 + (C.gates.take j).length ≤ a := by
              rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
              omega
            have hcard := congrArg Finset.card ha_eq
            rw [wireSupp_of_ge _ hge', Finset.card_empty, fanoLines_card] at hcard
            omega
          have ha_ge7 : 7 ≤ a := by
            by_contra hlt7
            have hcard := congrArg Finset.card ha_eq
            rw [wireSupp_input _ (by omega), Finset.card_singleton, fanoLines_card] at hcard
            omega
          have ha_supp : wireSupp C.gates a = fanoLines i := by
            rw [← wireSupp_take_eq C.gates j a (Nat.le_of_lt hj) ha_lt, ha_eq]
          refine ⟨a, ha_ge7, by omega, ha_supp ▸ Finset.Subset.refl _, ?_⟩
          rw [ha_supp, fanoLines_card]
          omega
        · have hb_eq : wireSupp (C.gates.take j) b = fanoLines i :=
            Finset.Subset.antisymm hb_sub hsub_b
          have hb_lt : b < 7 + j := by
            by_contra hge
            have hge' : 7 + (C.gates.take j).length ≤ b := by
              rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
              omega
            have hcard := congrArg Finset.card hb_eq
            rw [wireSupp_of_ge _ hge', Finset.card_empty, fanoLines_card] at hcard
            omega
          have hb_ge7 : 7 ≤ b := by
            by_contra hlt7
            have hcard := congrArg Finset.card hb_eq
            rw [wireSupp_input _ (by omega), Finset.card_singleton, fanoLines_card] at hcard
            omega
          have hb_supp : wireSupp C.gates b = fanoLines i := by
            rw [← wireSupp_take_eq C.gates j b (Nat.le_of_lt hj) hb_lt, hb_eq]
          refine ⟨b, hb_ge7, by omega, hb_supp ▸ Finset.Subset.refl _, ?_⟩
          rw [hb_supp, fanoLines_card]
          omega
      · have hunion : wireSupp (C.gates.take j) a ∪ wireSupp (C.gates.take j) b = fanoLines i := by
          ext p
          simp only [Finset.mem_union, wireSupp, Finset.mem_filter, Finset.mem_univ, true_and]
          have hp_iff :
              (wiresPrefix C.gates (List.ofFn fun q : Fin 7 => decide (q = p))).getD (o i) false = true ↔
                p ∈ fanoLines i := (hout i).1 p
          rw [← hp_iff, heval, hop_or]
          simp [GateOp.eval]
        have hcard_sum :
            3 ≤ (wireSupp (C.gates.take j) a).card + (wireSupp (C.gates.take j) b).card := by
          calc 3 = (fanoLines i).card := (fanoLines_card i).symm
            _ = (wireSupp (C.gates.take j) a ∪ wireSupp (C.gates.take j) b).card := by rw [hunion]
            _ ≤ (wireSupp (C.gates.take j) a).card + (wireSupp (C.gates.take j) b).card :=
                Finset.card_union_le _ _
        by_cases hca : 2 ≤ (wireSupp (C.gates.take j) a).card
        · have ha_lt : a < 7 + j := by
            by_contra hge
            have hge' : 7 + (C.gates.take j).length ≤ a := by
              rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
              omega
            rw [wireSupp_of_ge _ hge', Finset.card_empty] at hca
            omega
          have ha_ge7 : 7 ≤ a := by
            by_contra hlt7
            rw [wireSupp_input _ (by omega), Finset.card_singleton] at hca
            omega
          have ha_eq := wireSupp_take_eq C.gates j a (Nat.le_of_lt hj) ha_lt
          refine ⟨a, ha_ge7, by omega, ?_, ?_⟩
          · rw [← ha_eq, ← hunion]
            exact Finset.subset_union_left
          · rwa [← ha_eq]
        · have hcb : 2 ≤ (wireSupp (C.gates.take j) b).card := by omega
          have hb_lt : b < 7 + j := by
            by_contra hge
            have hge' : 7 + (C.gates.take j).length ≤ b := by
              rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
              omega
            rw [wireSupp_of_ge _ hge', Finset.card_empty] at hcb
            omega
          have hb_ge7 : 7 ≤ b := by
            by_contra hlt7
            rw [wireSupp_input _ (by omega), Finset.card_singleton] at hcb
            omega
          have hb_eq := wireSupp_take_eq C.gates j b (Nat.le_of_lt hj) hb_lt
          refine ⟨b, hb_ge7, by omega, ?_, ?_⟩
          · rw [← hb_eq, ← hunion]
            exact Finset.subset_union_right
          · rwa [← hb_eq]
    · simp [h_in] at hg_len
  choose u hu_ge7 hu_lt hu_sub hu_card using hgate_witness
  let H : Finset ℕ := Finset.Ico 7 (7 + C.gates.length) \ Finset.univ.image o
  have hu_mem : ∀ i : Fin 4, u i ∈ H := by
    intro i
    rw [Finset.mem_sdiff, Finset.mem_Ico, Finset.mem_image]
    refine ⟨⟨hu_ge7 i, lt_trans (hu_lt i) (ho_bounds i).2⟩, ?_⟩
    rintro ⟨j, _, hjo⟩
    by_cases hij : j = i
    · subst hij
      exact Nat.lt_irrefl _ (hjo ▸ hu_lt j)
    · have hsub : fanoLines j ⊆ fanoLines i := by
        rw [← hsupp_o j, hjo]
        exact hu_sub i
      have hinter : fanoLines j ⊆ fanoLines i ∩ fanoLines j :=
        Finset.subset_inter hsub (Finset.Subset.refl _)
      have h3 : 3 ≤ (fanoLines i ∩ fanoLines j).card := by
        rw [← fanoLines_card j]
        exact Finset.card_le_card hinter
      have h1 : (fanoLines i ∩ fanoLines j).card ≤ 1 :=
        fanoLines_inter_le i j (Ne.symm hij)
      omega
  have himg_sub : Finset.univ.image o ⊆ Finset.Ico 7 (7 + C.gates.length) := by
    intro w hw
    rcases Finset.mem_image.mp hw with ⟨i, _, rfl⟩
    rw [Finset.mem_Ico]
    exact ho_bounds i
  have hH_card : H.card < (Finset.univ : Finset (Fin 4)).card := by
    have hsum : H.card + (Finset.univ.image o).card = (Finset.Ico 7 (7 + C.gates.length)).card :=
      Finset.card_sdiff_add_card_eq_card himg_sub
    have himg_card : (Finset.univ.image o).card = 4 := by
      rw [Finset.card_image_of_injective _ ho_inj, Finset.card_univ, Fintype.card_fin]
    have hico_card : (Finset.Ico 7 (7 + C.gates.length)).card = C.gates.length := by
      rw [Nat.card_Ico]
      omega
    have hlen_le : C.gates.length ≤ 7 := hsize
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  rcases Finset.exists_ne_map_eq_of_card_lt_of_maps_to hH_card (fun i _ => hu_mem i) with
    ⟨i, _, j, _, hij, huij⟩
  have hsub_inter : wireSupp C.gates (u i) ⊆ fanoLines i ∩ fanoLines j :=
    Finset.subset_inter (hu_sub i) (huij ▸ hu_sub j)
  have h2 : 2 ≤ (fanoLines i ∩ fanoLines j).card :=
    le_trans (hu_card i) (Finset.card_le_card hsub_inter)
  have h1 : (fanoLines i ∩ fanoLines j).card ≤ 1 := fanoLines_inter_le i j hij
  omega

end PEqualNP.Outside
