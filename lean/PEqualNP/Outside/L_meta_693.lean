import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_693_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def mstep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def mwires (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl mstep w

private theorem wires_eq_mwires (C : Circuit) (x : List Bool) :
    C.wires x = mwires C.gates x := rfl

private theorem mwires_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    mwires (g :: gs) w = mwires gs (mstep w g) := rfl

private theorem mwires_append (gs1 gs2 : List Gate) (w : List Bool) :
    mwires (gs1 ++ gs2) w = mwires gs2 (mwires gs1 w) := by
  simp [mwires, List.foldl_append]

private theorem mwires_length (gs : List Gate) : ∀ w : List Bool,
    (mwires gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [mwires]
  | cons g gs ih =>
    intro w
    rw [mwires_cons, ih]
    simp [mstep]
    omega

private theorem getD_append_lt {α : Type*} (a b : List α) (d : α) (i : ℕ) (h : i < a.length) :
    (a ++ b).getD i d = a.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

private theorem getD_ge_len {α : Type*} (a : List α) (d : α) (i : ℕ) (h : a.length ≤ i) :
    a.getD i d = d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

private theorem mwires_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, mwires gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [mwires], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (mstep w g)
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    rw [mwires_cons, ht, mstep]
    simp

private theorem mwires_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (mwires gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := mwires_prefix gs w
  rw [ht, getD_append_lt _ _ _ _ h]

private theorem list_split_getElem {α : Type*} {l : List α} {j : ℕ} (hj : j < l.length) :
    l = l.take j ++ l[j] :: l.drop (j + 1) := by
  have h1 := (List.take_append_drop j l).symm
  have h2 : l.drop j = l[j] :: l.drop (j + 1) := List.drop_eq_getElem_cons hj
  rw [h2] at h1
  exact h1

private theorem mwires_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (g : Gate)
    (hg : gs[j]? = some g) :
    (mwires gs w).getD (w.length + j) false =
      g.op.eval (g.inputs.map fun i => (mwires (gs.take j) w).getD i false) := by
  have hj : j < gs.length := (List.getElem?_eq_some_iff.mp hg).1
  have hget : gs[j] = g := (List.getElem?_eq_some_iff.mp hg).2
  have hsplit : gs = gs.take j ++ g :: gs.drop (j + 1) := by
    rw [← hget]; exact list_split_getElem hj
  conv_lhs => rw [hsplit]
  rw [mwires_append, mwires_cons]
  set pre := mwires (gs.take j) w
  have hprelen : pre.length = w.length + j := by
    rw [mwires_length, List.length_take_of_le (by omega)]
  have hstep_len : (mstep pre g).length = w.length + j + 1 := by
    simp [mstep, hprelen]
  rw [mwires_getD_lt _ _ _ (by omega)]
  simp [mstep, List.getD_eq_getElem?_getD, hprelen]

private theorem gateOp_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l1 l2 : List Bool) (hlen : l1.length = l2.length)
    (hle : ∀ i, l1.getD i false = true → l2.getD i false = true) :
    op.eval l1 = true → op.eval l2 = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, id_eq]
    intro h1 b hb
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
    have hi1 : i < l1.length := by omega
    have h1i : l1.getD i false = true := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi1, Option.getD_some]
      exact h1 l1[i] (List.getElem_mem hi1)
    have h2i := hle i h1i
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] at h2i
    exact h2i
  · simp only [GateOp.eval, List.any_eq_true, id_eq]
    rintro ⟨b, hb, rfl⟩
    obtain ⟨i, hi, hbi⟩ := List.getElem_of_mem hb
    have hi2 : i < l2.length := by omega
    have h1i : l1.getD i false = true := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
      exact hbi
    have h2i := hle i h1i
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi2, Option.getD_some] at h2i
    exact ⟨l2[i], List.getElem_mem hi2, h2i⟩

private theorem mwires_mono (gs : List Gate)
    (hmono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ (w1 w2 : List Bool), w1.length = w2.length →
      (∀ i, w1.getD i false = true → w2.getD i false = true) →
      ∀ i, (mwires gs w1).getD i false = true → (mwires gs w2).getD i false = true := by
  induction gs with
  | nil => intro w1 w2 _ hle; exact hle
  | cons g gs ih =>
    intro w1 w2 hlen hle
    apply ih (fun g' hg' => hmono g' (List.mem_cons_of_mem _ hg')) (mstep w1 g) (mstep w2 g)
      (by simp [mstep, hlen])
    intro i hi
    by_cases hlt : i < w1.length
    · rw [mstep, getD_append_lt _ _ _ _ hlt] at hi
      rw [mstep, getD_append_lt _ _ _ _ (by omega)]
      exact hle i hi
    · by_cases heq : i = w1.length
      · subst heq
        simp only [mstep, List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _),
          Nat.sub_self, List.getElem?_cons_zero, Option.getD_some] at hi
        simp only [mstep, hlen, List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _),
          Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
        refine gateOp_mono g.op (hmono g List.mem_cons_self) _ _ (by simp) ?_ hi
        intro k hk
        by_cases hkl : k < g.inputs.length
        · simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hkl,
            Option.map_some, Option.getD_some] at hk ⊢
          exact hle _ hk
        · rw [getD_ge_len _ _ _ (by simp; omega)] at hk
          cases hk
      · rw [getD_ge_len _ _ _ (by simp [mstep]; omega)] at hi
        cases hi

theorem main_thm :
    ∀ (n k r : ℕ) (S : Finset (Fin n)) (C : Circuit) (Q : Finset ℕ) (ψ : ℕ → Bool),
      (∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) →
      (∀ x : Fin n → Bool, (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k →
        (∀ q ∈ S, x q = false) → (C.wires (List.ofFn x)).getD (n + r) false = false) →
      r ∈ Q →
      (∀ j ∈ Q, j < C.size) →
      (∀ j ∈ Q, j ≠ r → ∃ j' ∈ Q, j < j' ∧ ∃ g : Gate, C.gates[j']? = some g ∧ n + j ∈ g.inputs) →
      (∀ j ∈ Q, ∀ g : Gate, C.gates[j]? = some g →
        ψ (n + j) = g.op.eval (g.inputs.map (fun w => if w < n + j then ψ w else false))) →
      (∀ w : ℕ, (∀ j ∈ Q, w ≠ n + j) → ψ w = true →
        ¬ (Finset.univ.filter (fun p : Fin n =>
          (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD w false = true)) ⊆ S) →
      ψ (n + r) = true →
      k ≤ Q.card := by
  classical
  intro n k r S C Q ψ hgates hprom hrQ hQsz hparent hψ hout hψr
  let wireOf (j : ℕ) (i : Fin 2) : ℕ :=
    match C.gates[j]? with
    | some g => g.inputs.getD i.val 0
    | none => 0
  let Slots : Finset (ℕ × Fin 2) := Q ×ˢ Finset.univ
  let InSlots : Finset (ℕ × Fin 2) :=
    Slots.filter (fun s => ∃ j ∈ Q, j ≠ r ∧ wireOf s.1 s.2 = n + j)
  let OutSlots : Finset (ℕ × Fin 2) :=
    Slots.filter (fun s => (∀ j ∈ Q, wireOf s.1 s.2 ≠ n + j) ∧ wireOf s.1 s.2 < n + s.1 ∧ ψ (wireOf s.1 s.2) = true)
  -- Step 1: OutSlots.card ≤ Q.card + 1
  have hSlots_card : Slots.card = 2 * Q.card := by
    simp only [Slots, Finset.card_product, Finset.card_univ, Fintype.card_fin]
    omega
  have hdisj : Disjoint InSlots OutSlots := by
    rw [Finset.disjoint_left]
    intro s hs1 hs2
    simp only [InSlots, OutSlots, Finset.mem_filter] at hs1 hs2
    obtain ⟨j, hjQ, _, hw⟩ := hs1.2
    exact hs2.2.1 j hjQ hw
  have hIn_ge : Q.card - 1 ≤ InSlots.card := by
    have hex : ∀ j ∈ Q.erase r, ∃ s ∈ InSlots, wireOf s.1 s.2 = n + j := by
      intro j hj
      obtain ⟨hjr, hjQ⟩ := Finset.mem_erase.mp hj
      obtain ⟨j', hj'Q, _, g, hg, hmem⟩ := hparent j hjQ hjr
      have hlen : g.inputs.length = 2 := (hgates g (List.mem_of_getElem? hg)).2
      obtain ⟨idx, hidx_lt, hidx_eq⟩ := List.getElem_of_mem hmem
      have hidx2 : idx < 2 := by omega
      refine ⟨(j', ⟨idx, hidx2⟩), ?_, ?_⟩
      · simp only [InSlots, Slots, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
        refine ⟨hj'Q, j, hjQ, hjr, ?_⟩
        simp only [wireOf, hg, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hidx_lt, Option.getD_some]
        exact hidx_eq
      · simp only [wireOf, hg, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hidx_lt, Option.getD_some]
        exact hidx_eq
    choose f hf_mem hf_wire using hex
    have hsub : (Q.erase r).attach.image (fun x => f x.1 x.2) ⊆ InSlots := by
      intro s hs
      rcases Finset.mem_image.mp hs with ⟨x, _, rfl⟩
      exact hf_mem x.1 x.2
    have hinj : Set.InjOn (fun x : {x // x ∈ Q.erase r} => f x.1 x.2) (Q.erase r).attach := by
      intro x _ y _ hxy
      have hw : wireOf (f x.1 x.2).1 (f x.1 x.2).2 = wireOf (f y.1 y.2).1 (f y.1 y.2).2 :=
        congrArg (fun s => wireOf s.1 s.2) hxy
      rw [hf_wire x.1 x.2, hf_wire y.1 y.2] at hw
      exact Subtype.ext (by omega)
    have hcard_img : ((Q.erase r).attach.image (fun x => f x.1 x.2)).card = (Q.erase r).card := by
      rw [Finset.card_image_of_injOn hinj, Finset.card_attach]
    have hle := Finset.card_le_card hsub
    rw [hcard_img, Finset.card_erase_of_mem hrQ] at hle
    exact hle
  have hOut_le : OutSlots.card ≤ Q.card + 1 := by
    have hunion : InSlots ∪ OutSlots ⊆ Slots :=
      Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    have hle := Finset.card_le_card hunion
    rw [Finset.card_union_of_disjoint hdisj, hSlots_card] at hle
    have hQpos : 1 ≤ Q.card := Finset.card_pos.mpr ⟨r, hrQ⟩
    omega
  -- Step 2: For each s ∈ OutSlots, pick p_s ∉ S with wireOf s.1 s.2 true at e_{p_s}
  have hpick_ex : ∀ s ∈ OutSlots, ∃ p : Fin n, p ∉ S ∧
      (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (wireOf s.1 s.2) false = true := by
    intro s hs
    simp only [OutSlots, Finset.mem_filter] at hs
    have hnsub := hout (wireOf s.1 s.2) hs.2.1 hs.2.2.2
    rw [Finset.not_subset] at hnsub
    obtain ⟨p, hp_mem, hpS⟩ := hnsub
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp_mem
    exact ⟨p, hpS, hp_mem⟩
  choose pick hpick_notS hpick_true using hpick_ex
  let T : Finset (Fin n) := OutSlots.attach.image (fun s => pick s.1 s.2)
  let xT : Fin n → Bool := fun q => decide (q ∈ T)
  have hT_card : (Finset.univ.filter (fun q : Fin n => xT q = true)).card ≤ OutSlots.card := by
    have hfilt : Finset.univ.filter (fun q : Fin n => xT q = true) = T := by
      ext q; simp [xT]
    rw [hfilt]
    calc T.card ≤ OutSlots.attach.card := Finset.card_image_le
      _ = OutSlots.card := Finset.card_attach
  have hT_missS : ∀ q ∈ S, xT q = false := by
    intro q hqS
    simp only [xT, decide_eq_false_iff_not]
    intro hqT
    rcases Finset.mem_image.mp hqT with ⟨s, _, rfl⟩
    exact hpick_notS s.1 s.2 hqS
  -- Step 3: Strong induction on j: every j ∈ Q with ψ (n + j) = true has wire (n + j) true at xT!
  have hind : ∀ j : ℕ, j ∈ Q → ψ (n + j) = true →
      (C.wires (List.ofFn xT)).getD (n + j) false = true := by
    intro j
    induction j using Nat.strongRecOn with
    | ind j ih =>
      intro hjQ hψj
      have hjlt : j < C.gates.length := hQsz j hjQ
      obtain ⟨g, hg⟩ : ∃ g, C.gates[j]? = some g := ⟨C.gates[j], List.getElem?_eq_getElem hjlt⟩
      obtain ⟨hop, hlen⟩ := hgates g (List.mem_of_getElem? hg)
      have hψ_eval := hψ j hjQ g hg
      rw [hψj] at hψ_eval
      -- Helper: for any input slot i : Fin 2 of g whose wire w satisfies w < n + j and ψ w = true,
      -- (C.wires (List.ofFn xT)).getD w false = true
      have hslot_true : ∀ i : Fin 2,
          let w := g.inputs.getD i.val 0
          w < n + j → ψ w = true → (C.wires (List.ofFn xT)).getD w false = true := by
        intro i w hwlt hψw
        by_cases hinQ : ∃ j' ∈ Q, w = n + j'
        · obtain ⟨j', hj'Q, hw_eq⟩ := hinQ
          rw [hw_eq] at hwlt hψw ⊢
          exact ih j' (by omega) hj'Q hψw
        · push Not at hinQ
          have hs_mem : (j, i) ∈ OutSlots := by
            simp only [OutSlots, Slots, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
            refine ⟨hjQ, ?_, ?_, ?_⟩
            · intro j' hj'Q; simp only [wireOf, hg]; exact hinQ j' hj'Q
            · simp only [wireOf, hg]; exact hwlt
            · simp only [wireOf, hg]; exact hψw
          let p := pick (j, i) hs_mem
          have hpT : p ∈ T := Finset.mem_image.mpr ⟨⟨(j, i), hs_mem⟩, Finset.mem_attach _ _, rfl⟩
          have hp_eval : (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD w false = true := by
            have := hpick_true (j, i) hs_mem
            simpa [wireOf, hg, w] using this
          have hle_in : ∀ idx, (List.ofFn (fun q : Fin n => decide (q = p))).getD idx false = true →
              (List.ofFn xT).getD idx false = true := by
            intro idx hidx
            rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn] at hidx ⊢
            by_cases hlt : idx < n
            · simp only [hlt, dite_true, Option.getD_some, decide_eq_true_eq] at hidx
              simp only [hlt, dite_true, Option.getD_some, xT, decide_eq_true_eq]
              rw [hidx]; exact hpT
            · simp [hlt] at hidx
          exact mwires_mono C.gates (fun g' hg' => (hgates g' hg').1) _ _ (by simp) hle_in w hp_eval
      -- Express g.inputs as [w0, w1]
      rcases hgin : g.inputs with _ | ⟨w0, _ | ⟨w1, _ | ⟨w2, rest⟩⟩⟩
      · simp [hgin] at hlen
      · simp [hgin] at hlen
      · -- g.inputs = [w0, w1]
        have hw0_eq : g.inputs.getD 0 0 = w0 := by simp [hgin]
        have hw1_eq : g.inputs.getD 1 0 = w1 := by simp [hgin]
        have hpre : ∀ u < n + j, (mwires (C.gates.take j) (List.ofFn xT)).getD u false =
            (C.wires (List.ofFn xT)).getD u false := by
          intro u hu
          have hsp : C.gates = C.gates.take j ++ C.gates.drop j := (List.take_append_drop j C.gates).symm
          rw [wires_eq_mwires]
          conv_rhs => rw [hsp, mwires_append]
          exact (mwires_getD_lt (C.gates.drop j) (mwires (C.gates.take j) (List.ofFn xT)) u (by
            rw [mwires_length, List.length_ofFn, List.length_take_of_le (by omega)]; omega)).symm
        have hgate_eval : (C.wires (List.ofFn xT)).getD (n + j) false =
            g.op.eval [(mwires (C.gates.take j) (List.ofFn xT)).getD w0 false,
                       (mwires (C.gates.take j) (List.ofFn xT)).getD w1 false] := by
          rw [wires_eq_mwires]
          have hw_eq : n + j = (List.ofFn xT).length + j := by simp
          rw [hw_eq, mwires_getD_gate C.gates (List.ofFn xT) j g hg, hgin]
          simp
        rw [hgate_eval]
        rcases hop with hop | hop
        · rw [hop, hgin] at hψ_eval
          simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
            id_eq, Bool.and_true] at hψ_eval
          have h01 : (if w0 < n + j then ψ w0 else false) = true ∧
              (if w1 < n + j then ψ w1 else false) = true := by
            simpa [Bool.and_eq_true] using hψ_eval.symm
          have hw0_lt : w0 < n + j := by
            by_contra h; rw [if_neg h] at h01; cases h01.1
          have hψw0 : ψ w0 = true := by rw [if_pos hw0_lt] at h01; exact h01.1
          have hw1_lt : w1 < n + j := by
            by_contra h; rw [if_neg h] at h01; cases h01.2
          have hψw1 : ψ w1 = true := by rw [if_pos hw1_lt] at h01; exact h01.2
          have ht0 := hslot_true ⟨0, by decide⟩ (by dsimp only; rw [hw0_eq]; exact hw0_lt) (by dsimp only; rw [hw0_eq]; exact hψw0)
          have ht1 := hslot_true ⟨1, by decide⟩ (by dsimp only; rw [hw1_eq]; exact hw1_lt) (by dsimp only; rw [hw1_eq]; exact hψw1)
          rw [hop, GateOp.eval]
          simp only [List.all_cons, List.all_nil, id_eq, Bool.and_true,
            hpre w0 hw0_lt, hpre w1 hw1_lt, hw0_eq ▸ ht0, hw1_eq ▸ ht1]
        · rw [hop, hgin] at hψ_eval
          simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
            id_eq, Bool.or_false] at hψ_eval
          have h01 : (if w0 < n + j then ψ w0 else false) = true ∨
              (if w1 < n + j then ψ w1 else false) = true := by
            simpa [Bool.or_eq_true] using hψ_eval.symm
          rw [hop, GateOp.eval]
          simp only [List.any_cons, List.any_nil, id_eq, Bool.or_false, Bool.or_eq_true]
          rcases h01 with h0 | h1
          · have hw0_lt : w0 < n + j := by by_contra h; rw [if_neg h] at h0; cases h0
            have hψw0 : ψ w0 = true := by rw [if_pos hw0_lt] at h0; exact h0
            have ht0 := hslot_true ⟨0, by decide⟩ (by dsimp only; rw [hw0_eq]; exact hw0_lt) (by dsimp only; rw [hw0_eq]; exact hψw0)
            left; rw [hpre w0 hw0_lt, ← hw0_eq]; exact ht0
          · have hw1_lt : w1 < n + j := by by_contra h; rw [if_neg h] at h1; cases h1
            have hψw1 : ψ w1 = true := by rw [if_pos hw1_lt] at h1; exact h1
            have ht1 := hslot_true ⟨1, by decide⟩ (by dsimp only; rw [hw1_eq]; exact hw1_lt) (by dsimp only; rw [hw1_eq]; exact hψw1)
            right; rw [hpre w1 hw1_lt, ← hw1_eq]; exact ht1
      · simp [hgin] at hlen
  -- Step 4: Contradict promise if T.card ≤ k
  have hr_true := hind r hrQ hψr
  have hgt_k : ¬ (Finset.univ.filter (fun q : Fin n => xT q = true)).card ≤ k := by
    intro hle
    have hrf := hprom xT hle hT_missS
    rw [hrf] at hr_true
    cases hr_true
  omega

end PEqualNP.Outside.L_meta_693_aux

theorem PEqualNP.Outside.L_meta_693 : ∀ (n k r : ℕ) (S : Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (Q : Finset ℕ) (ψ : ℕ → Bool), (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → (∀ x : Fin n → Bool, (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k → (∀ q ∈ S, x q = false) → (C.wires (List.ofFn x)).getD (n + r) false = false) → r ∈ Q → (∀ j ∈ Q, j < C.size) → (∀ j ∈ Q, j ≠ r → ∃ j' ∈ Q, j < j' ∧ ∃ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[j']? = some g ∧ n + j ∈ g.inputs) → (∀ j ∈ Q, ∀ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[j]? = some g → ψ (n + j) = g.op.eval (g.inputs.map (fun w => if w < n + j then ψ w else false))) → (∀ w : ℕ, (∀ j ∈ Q, w ≠ n + j) → ψ w = true → ¬ (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (w) false = true)) ⊆ S) → ψ (n + r) = true → k ≤ Q.card :=
  PEqualNP.Outside.L_meta_693_aux.main_thm
