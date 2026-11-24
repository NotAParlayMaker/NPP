import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1660

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    cases j with
    | zero =>
      simp only [List.foldl_cons, Nat.add_zero, List.getElem_cons_zero]
      have hlen : w.length < (stepWire w g).length := by simp [stepWire]
      rw [foldl_getD_lt gs (stepWire w g) w.length hlen]
      have htail : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [htail]
      congr 1
      refine List.map_congr_left ?_
      intro i _
      by_cases hi : i < w.length
      · rw [ite_eq_left hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [ite_eq_right hi, getD_ge w i (Nat.le_of_not_lt hi)]
    | succ j' =>
      simp only [List.foldl_cons, List.getElem_cons_succ]
      have hlen : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      have hj' : j' < gs.length := by simpa using hj
      have h := ih (stepWire w g) j' hj'
      rwa [hlen, Nat.add_assoc, Nat.add_comm 1 j'] at h

def val (n : ℕ) (C : Circuit) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD i false

def Reads (n : ℕ) (C : Circuit) (w v : ℕ) : Prop :=
  ∃ j < C.gates.length, v = n + j ∧ w ∈ (gateAt C j).inputs

def Reach (n : ℕ) (C : Circuit) (w : ℕ) : Prop :=
  Relation.ReflTransGen (Reads n C) w C.output

lemma wires_length (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  change (C.gates.foldl stepWire (List.ofFn x)).length = n + C.gates.length
  rw [foldl_length, List.length_ofFn]

lemma val_lt (n : ℕ) (C : Circuit) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    val n C x i = x ⟨i, hi⟩ := by
  unfold val Circuit.wires
  change (C.gates.foldl stepWire (List.ofFn x)).getD i false = x ⟨i, hi⟩
  have hi' : i < (List.ofFn x).length := by simpa using hi
  rw [foldl_getD_lt _ _ _ hi', List.getD_eq_getElem _ _ hi']
  simp

lemma gateAt_eq (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]

lemma val_eq_of_reach (n : ℕ) (C : Circuit) (hrb : ReadsBack n C)
    (x y : Fin n → Bool) (hagree : ∀ k : Fin n, Reach n C k.val → x k = y k) :
    ∀ w : ℕ, Reach n C w → val n C x w = val n C y w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hwn : w < n
    · rw [val_lt n C x w hwn, val_lt n C y w hwn]
      exact hagree ⟨w, hwn⟩ hw
    · set j := w - n
      have hwj : w = n + j := by omega
      by_cases hj : j < C.gates.length
      · have hlenx : (List.ofFn x).length = n := List.length_ofFn
        have hleny : (List.ofFn y).length = n := List.length_ofFn
        have hgx : val n C x w = (C.gates[j]).op.eval ((C.gates[j]).inputs.map fun i =>
            if i < n + j then val n C x i else false) := by
          unfold val
          change (C.gates.foldl stepWire (List.ofFn x)).getD w false = _
          rw [hwj]
          have hfg := foldl_getD_gate C.gates (List.ofFn x) j hj
          rw [hlenx] at hfg
          exact hfg
        have hgy : val n C y w = (C.gates[j]).op.eval ((C.gates[j]).inputs.map fun i =>
            if i < n + j then val n C y i else false) := by
          unfold val
          change (C.gates.foldl stepWire (List.ofFn y)).getD w false = _
          rw [hwj]
          have hfg := foldl_getD_gate C.gates (List.ofFn y) j hj
          rw [hleny] at hfg
          exact hfg
        rw [hgx, hgy]
        congr 1
        refine List.map_congr_left ?_
        intro i hi
        have hi_gate : i ∈ (gateAt C j).inputs := by rwa [gateAt_eq C j hj]
        have hi_lt : i < n + j := hrb j hj i hi_gate
        rw [ite_eq_left hi_lt, ite_eq_left hi_lt]
        have hreads : Reads n C i w := ⟨j, hj, hwj, hi_gate⟩
        exact ih i (by omega) (Relation.ReflTransGen.head hreads hw)
      · have hge : n + C.gates.length ≤ w := by omega
        have hx0 : val n C x w = false := by
          unfold val
          exact getD_ge _ _ (by rw [wires_length]; exact hge)
        have hy0 : val n C y w = false := by
          unfold val
          exact getD_ge _ _ (by rw [wires_length]; exact hge)
        rw [hx0, hy0]

lemma eval_eq_of_agree_reach (n : ℕ) (C : Circuit) (hrb : ReadsBack n C)
    (x y : Fin n → Bool) (hagree : ∀ k : Fin n, Reach n C k.val → x k = y k) :
    circuitFun n C x = circuitFun n C y :=
  val_eq_of_reach n C hrb x y hagree C.output Relation.ReflTransGen.refl

lemma reach_all_inputs (n : ℕ) (C : Circuit) (hrb : ReadsBack n C)
    (hess : ∀ k : Fin n, ∃ x0 x1 : Fin n → Bool,
      (∀ k' : Fin n, k' ≠ k → x0 k' = x1 k') ∧
      circuitFun n C x0 ≠ circuitFun n C x1) :
    ∀ k : ℕ, k < n → Reach n C k := by
  intro k hk
  obtain ⟨x0, x1, hdiff, hne⟩ := hess ⟨k, hk⟩
  by_contra hnr
  apply hne
  apply eval_eq_of_agree_reach n C hrb x0 x1
  intro k' hk'
  have hkne : k' ≠ ⟨k, hk⟩ := by
    intro heq
    subst heq
    exact hnr hk'
  exact hdiff k' hkne

lemma output_lt_of_eval_true (n : ℕ) (C : Circuit) (x : Fin n → Bool)
    (htrue : circuitFun n C x = true) :
    C.output < n + C.gates.length := by
  by_contra hge
  have hfalse : circuitFun n C x = false := by
    unfold circuitFun Circuit.eval
    exact getD_ge _ _ (by rw [wires_length]; omega)
  rw [hfalse] at htrue
  cases htrue

lemma size_lower_bound (n : ℕ) (C : Circuit) (hn : 0 < n) (hM2 : Monotone2 C)
    (hout : C.output < n + C.gates.length) (hin : ∀ k : ℕ, k < n → Reach n C k) :
    n ≤ C.size + 1 := by
  classical
  let G : Finset ℕ := (Finset.range C.gates.length).filter (fun j => Reach n C (n + j))
  let R : Finset ℕ := Finset.range n ∪ G.image (fun j => n + j)
  have hdisj : Disjoint (Finset.range n) (G.image (fun j => n + j)) := by
    rw [Finset.disjoint_left]
    intro w hw1 hw2
    rw [Finset.mem_range] at hw1
    rw [Finset.mem_image] at hw2
    rcases hw2 with ⟨j, _, rfl⟩
    omega
  have hinj : Function.Injective (fun j => n + j) := fun a b h => by dsimp at h; omega
  have hRcard : R.card = n + G.card := by
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_range,
      Finset.card_image_of_injective G hinj]
  have houtR : C.output ∈ R := by
    by_cases hcn : C.output < n
    · exact Finset.mem_union_left _ (Finset.mem_range.2 hcn)
    · apply Finset.mem_union_right
      rw [Finset.mem_image]
      refine ⟨C.output - n, ?_, by omega⟩
      rw [Finset.mem_filter, Finset.mem_range]
      refine ⟨by omega, ?_⟩
      have hrew : n + (C.output - n) = C.output := by omega
      rw [hrew]
      exact Relation.ReflTransGen.refl
  have hsub : R.erase C.output ⊆ G.biUnion (fun j => (gateAt C j).inputs.toFinset) := by
    intro w hw
    rw [Finset.mem_erase] at hw
    rcases hw with ⟨hwne, hwR⟩
    have hwreach : Reach n C w := by
      rcases Finset.mem_union.1 hwR with hw1 | hw2
      · exact hin w (Finset.mem_range.1 hw1)
      · rcases Finset.mem_image.1 hw2 with ⟨j, hjG, rfl⟩
        exact (Finset.mem_filter.1 hjG).2
    rcases Relation.ReflTransGen.cases_head hwreach with hEq | ⟨v, hvReads, hvReach⟩
    · exact absurd hEq hwne
    · rcases hvReads with ⟨j, hjlen, hv_eq, hwmem⟩
      subst hv_eq
      rw [Finset.mem_biUnion]
      refine ⟨j, ?_, List.mem_toFinset.2 hwmem⟩
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨hjlen, hvReach⟩
  have hcard1 : R.card - 1 = (R.erase C.output).card := by
    rw [Finset.card_erase_of_mem houtR]
  have hcard2 : (R.erase C.output).card ≤
      (G.biUnion (fun j => (gateAt C j).inputs.toFinset)).card :=
    Finset.card_le_card hsub
  have hcard3 : (G.biUnion (fun j => (gateAt C j).inputs.toFinset)).card ≤
      ∑ j ∈ G, ((gateAt C j).inputs.toFinset).card :=
    Finset.card_biUnion_le
  have hcard4 : ∑ j ∈ G, ((gateAt C j).inputs.toFinset).card ≤ ∑ _j ∈ G, 2 := by
    refine Finset.sum_le_sum ?_
    intro j hjG
    have hjlen : j < C.gates.length := Finset.mem_range.1 (Finset.mem_filter.1 hjG).1
    have hgate : C.gates[j] ∈ C.gates := List.getElem_mem hjlen
    have hlen2 : (gateAt C j).inputs.length ≤ 2 := by
      rw [gateAt_eq C j hjlen]
      exact (hM2 _ hgate).2
    exact (List.toFinset_card_le _).trans hlen2
  have hcard5 : ∑ _j ∈ G, 2 = 2 * G.card := by
    simp [Nat.mul_comm]
  have hGcard : G.card ≤ C.size := by
    calc G.card ≤ (Finset.range C.gates.length).card := Finset.card_filter_le _ _
    _ = C.gates.length := Finset.card_range _
    _ = C.size := rfl
  omega

end PEqualNP.Outside.L_meta_1660

theorem PEqualNP.Outside.L_meta_1660 : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q → N = q ^ 2 + q + 1 → (∀ l : Fin N, (Finset.univ.filter (fun p0 => I p0 l)).card = q + 1) → (∀ pa pb : Fin N, pa ≠ pb → ∃! l0 : Fin N, I pa l0 ∧ I pb l0) → PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) C → (∀ p1 l1 : Fin N, I p1 l1 → PEqualNP.MetaComplexity.circuitFun (N + N) C (fun k1 => decide (k1 = Fin.castAdd N p1 ∨ k1 = Fin.natAdd N l1)) = true) → (∀ z1 : Fin (N + N) → Bool, (Finset.univ.filter (fun l1b : Fin N => z1 (Fin.natAdd N l1b) = true)).card ≤ q → (¬ ∃ p1c l1c : Fin N, I p1c l1c ∧ z1 (Fin.castAdd N p1c) = true ∧ z1 (Fin.natAdd N l1c) = true) → PEqualNP.MetaComplexity.circuitFun (N + N) C z1 = false) → 2 * N ≤ C.size + 1 := by
  intro q N I _ C hq hN hline hpair hM2 hrb hacc hsound
  have hN7 : 7 ≤ N := by nlinarith
  have hNpos : 0 < N := by omega
  have hpt_line : ∀ p : Fin N, ∃ l : Fin N, I p l := by
    intro p
    let p' : Fin N := if p.val = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩
    have hpne : p ≠ p' := by
      intro heq
      by_cases h0 : p.val = 0
      · have : p.val = p'.val := congrArg Fin.val heq
        simp [p', h0] at this
      · have : p.val = p'.val := congrArg Fin.val heq
        simp [p', h0] at this
    obtain ⟨l, hl, _⟩ := hpair p p' hpne
    exact ⟨l, hl.1⟩
  have hline_pt : ∀ l : Fin N, ∃ p : Fin N, I p l := by
    intro l
    have hpos : 0 < (Finset.univ.filter (fun p0 => I p0 l)).card := by
      rw [hline l]
      omega
    obtain ⟨p, hp⟩ := Finset.card_pos.1 hpos
    exact ⟨p, (Finset.mem_filter.1 hp).2⟩
  have hess : ∀ k : Fin (N + N), ∃ x0 x1 : Fin (N + N) → Bool,
      (∀ k' : Fin (N + N), k' ≠ k → x0 k' = x1 k') ∧
      PEqualNP.MetaComplexity.circuitFun (N + N) C x0 ≠
        PEqualNP.MetaComplexity.circuitFun (N + N) C x1 := by
    intro k
    by_cases hk : k.val < N
    · let p : Fin N := ⟨k.val, hk⟩
      have hkp : k = Fin.castAdd N p := Fin.ext rfl
      obtain ⟨l, hpl⟩ := hpt_line p
      let x1 : Fin (N + N) → Bool := fun k1 => decide (k1 = Fin.castAdd N p ∨ k1 = Fin.natAdd N l)
      let x0 : Fin (N + N) → Bool := fun k1 => decide (k1 = Fin.natAdd N l)
      refine ⟨x0, x1, ?_, ?_⟩
      · intro k' hk'
        have hk'p : k' ≠ Fin.castAdd N p := fun h => hk' (h.trans hkp.symm)
        simp [x0, x1, hk'p]
      · have hx1 : PEqualNP.MetaComplexity.circuitFun (N + N) C x1 = true := hacc p l hpl
        have hx0 : PEqualNP.MetaComplexity.circuitFun (N + N) C x0 = false := by
          apply hsound x0
          · have hsub : Finset.univ.filter (fun l1b : Fin N => x0 (Fin.natAdd N l1b) = true) ⊆ {l} := by
              intro l1b hl1b
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, x0, decide_eq_true_eq] at hl1b
              have : l1b = l := Fin.ext (by have := congrArg Fin.val hl1b; simpa using this)
              simp [this]
            calc (Finset.univ.filter (fun l1b : Fin N => x0 (Fin.natAdd N l1b) = true)).card
                ≤ ({l} : Finset (Fin N)).card := Finset.card_le_card hsub
              _ = 1 := Finset.card_singleton l
              _ ≤ q := by omega
          · rintro ⟨p1c, l1c, _, hp1c, _⟩
            simp only [x0, decide_eq_true_eq] at hp1c
            have : (Fin.castAdd N p1c).val = (Fin.natAdd N l).val := congrArg Fin.val hp1c
            simp at this
            omega
        rw [hx0, hx1]
        decide
    · let l : Fin N := ⟨k.val - N, by omega⟩
      have hkl : k = Fin.natAdd N l := Fin.ext (by simp [l]; omega)
      obtain ⟨p, hpl⟩ := hline_pt l
      let x1 : Fin (N + N) → Bool := fun k1 => decide (k1 = Fin.castAdd N p ∨ k1 = Fin.natAdd N l)
      let x0 : Fin (N + N) → Bool := fun k1 => decide (k1 = Fin.castAdd N p)
      refine ⟨x0, x1, ?_, ?_⟩
      · intro k' hk'
        have hk'l : k' ≠ Fin.natAdd N l := fun h => hk' (h.trans hkl.symm)
        simp only [x0, x1, decide_eq_decide]
        exact ⟨fun h => Or.inl h, fun h => h.elim id (fun h2 => absurd h2 hk'l)⟩
      · have hx1 : PEqualNP.MetaComplexity.circuitFun (N + N) C x1 = true := hacc p l hpl
        have hx0 : PEqualNP.MetaComplexity.circuitFun (N + N) C x0 = false := by
          apply hsound x0
          · have hempty : Finset.univ.filter (fun l1b : Fin N => x0 (Fin.natAdd N l1b) = true) = ∅ := by
              rw [Finset.filter_eq_empty_iff]
              intro l1b _
              simp only [x0, decide_eq_true_eq]
              intro heq
              have : (Fin.natAdd N l1b).val = (Fin.castAdd N p).val := congrArg Fin.val heq
              simp at this
              omega
            rw [hempty, Finset.card_empty]
            omega
          · rintro ⟨p1c, l1c, _, _, hl1c⟩
            simp only [x0, decide_eq_true_eq] at hl1c
            have : (Fin.natAdd N l1c).val = (Fin.castAdd N p).val := congrArg Fin.val hl1c
            simp at this
            omega
        rw [hx0, hx1]
        decide
  obtain ⟨l0, hl0⟩ := hpt_line ⟨0, hNpos⟩
  have hout : C.output < (N + N) + C.gates.length :=
    PEqualNP.Outside.L_meta_1660.output_lt_of_eval_true (N + N) C _ (hacc ⟨0, hNpos⟩ l0 hl0)
  have hreach := PEqualNP.Outside.L_meta_1660.reach_all_inputs (N + N) C hrb hess
  have hbound := PEqualNP.Outside.L_meta_1660.size_lower_bound (N + N) C (by omega) hM2 hout hreach
  omega
