import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_782

open PEqualNP.CircuitLowerBounds

theorem frontier (deps : ℕ → Finset ℕ) (binary : ∀ j, (deps j).card ≤ 2)
    (earlier : ∀ j a, a ∈ deps j → a < j) (bound : ℕ) (P W : Finset ℕ)
    (hP : ∀ j ∈ P, j < bound) :
    ∃ E : Finset ℕ, E.card ≤ P.card + W.card ∧ E ⊆ W ∪ Finset.range bound ∧
      Disjoint E P ∧ ∀ G : ℕ → Prop, (∀ j ∈ P, (∀ a ∈ deps j, G a) → G j) →
        (∀ a ∈ E, G a) → ∀ a ∈ W, G a := by
  classical
  induction bound generalizing P W with
  | zero =>
    have hp : P = ∅ := Finset.eq_empty_iff_forall_notMem.mpr fun j hj => by
      have := hP j hj
      omega
    subst P
    exact ⟨W, by simp, Finset.subset_union_left, by simp, fun _ _ h => h⟩
  | succ bound ih =>
    by_cases hk : bound ∈ P
    · let P' := P.erase bound
      let W' := if bound ∈ W then W.erase bound ∪ deps bound else W
      have hP' : ∀ j ∈ P', j < bound := by
        intro j hj
        obtain ⟨hne, hm⟩ := Finset.mem_erase.mp hj
        have := hP j hm
        omega
      obtain ⟨E, hE, hsub, hdis, himp⟩ := ih P' W' hP'
      have hsize : W'.card ≤ W.card + 1 := by
        by_cases hw : bound ∈ W
        · simp only [W', hw, ite_true]
          have hpos := Finset.card_pos.mpr ⟨bound, hw⟩
          have hdiff := Finset.card_erase_of_mem hw
          have hsum := Finset.card_union_le (W.erase bound) (deps bound)
          have hbin := binary bound
          omega
        · simp [W', hw]
      have hpc : P'.card + 1 = P.card := by
        have hpos := Finset.card_pos.mpr ⟨bound, hk⟩
        have hdiff := Finset.card_erase_of_mem hk
        dsimp [P']
        omega
      have hnw : bound ∉ W' := by
        by_cases hw : bound ∈ W
        · simpa [W', hw] using (show bound ∉ deps bound from fun hb =>
            Nat.lt_irrefl _ (earlier bound bound hb))
        · simp [W', hw]
      refine ⟨E, by omega, ?_, ?_, ?_⟩
      · intro a ha
        rcases Finset.mem_union.mp (hsub ha) with hm | hm
        · by_cases hw : bound ∈ W
          · simp only [W', hw, ite_true, Finset.mem_union, Finset.mem_erase] at hm
            rcases hm with ⟨_, hw'⟩ | hd
            · exact Finset.mem_union_left _ hw'
            · exact Finset.mem_union_right _ (Finset.mem_range.mpr (by
                have := earlier bound a hd
                omega))
          · exact Finset.mem_union_left _ (by simpa [W', hw] using hm)
        · exact Finset.mem_union_right _ (Finset.mem_range.mpr (by
            have := Finset.mem_range.mp hm
            omega))
      · rw [Finset.disjoint_left] at hdis ⊢
        intro a ha hp
        by_cases he : a = bound
        · subst a
          simpa [hnw] using hsub ha
        · exact hdis ha (Finset.mem_erase.mpr ⟨he, hp⟩)
      · intro G hstep hex a ha
        have hW' := himp G (fun j hj => hstep j (Finset.mem_of_mem_erase hj)) hex
        by_cases hw : bound ∈ W
        · by_cases he : a = bound
          · subst a
            apply hstep bound hk
            intro b hb
            apply hW' b
            simp [W', hw, hb]
          · apply hW' a
            simp [W', hw, he, ha]
        · exact hW' a (by simpa [W', hw] using ha)
    · have hp : ∀ j ∈ P, j < bound := by
        intro j hj
        have hne : j ≠ bound := fun he => hk (he ▸ hj)
        have := hP j hj
        omega
      obtain ⟨E, hc, hs, hd, hi⟩ := ih P W hp
      refine ⟨E, hc, ?_, hd, hi⟩
      intro a ha
      rcases Finset.mem_union.mp (hs ha) with hw | hr
      · exact Finset.mem_union_left _ hw
      · exact Finset.mem_union_right _ (Finset.range_mono (Nat.le_succ bound) hr)

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun a => w.getD a false)]) w

theorem wires_split (gs hs : List Gate) (w : List Bool) :
    wiresFrom (gs ++ hs) w = wiresFrom hs (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wires_prefix (gs : List Gate) (w : List Bool) :
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs generalizing w with
  | nil => exact ⟨[], by simp [wiresFrom]⟩
  | cons g gs ih =>
    let b := g.op.eval (g.inputs.map fun a => w.getD a false)
    obtain ⟨t, h, ht⟩ := ih (w ++ [b])
    refine ⟨b :: t, ?_, by simp [ht]⟩
    change wiresFrom gs (w ++ [b]) = w ++ b :: t
    rw [h, List.append_assoc]
    rfl

theorem wires_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hlen⟩ := wires_prefix gs w
  simp [ht, hlen]

theorem wires_keep (gs : List Gate) (w : List Bool) (a : ℕ) (ha : a < w.length) :
    (wiresFrom gs w).getD a false = w.getD a false := by
  obtain ⟨t, ht, _⟩ := wires_prefix gs w
  rw [ht, List.getD_append _ _ _ _ ha]

theorem wires_at (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (wiresFrom gs w).getD (w.length + j) false =
      (gs[j]'hj).op.eval ((gs[j]'hj).inputs.map fun a =>
        (wiresFrom (gs.take j) w).getD a false) := by
  have heq := List.take_append_drop (j + 1) gs
  have hpre : (wiresFrom (gs.take (j + 1)) w).length = w.length + (j + 1) := by
    simp [wires_length, List.length_take, Nat.min_eq_left (by omega : j + 1 ≤ gs.length)]
  conv_lhs => rw [← heq, wires_split, wires_keep _ _ _ (by omega : w.length + j < _)]
  rw [List.take_succ_eq_append_getElem hj, wires_split]
  have hlen : (wiresFrom (gs.take j) w).length = w.length + j := by
    simp [wires_length, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  rw [← hlen]
  simp [wiresFrom]

theorem eval_mono (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or)
    (f f' : ℕ → Bool) (h : ∀ a ∈ g.inputs, f a = true → f' a = true) :
    g.op.eval (g.inputs.map f) = true → g.op.eval (g.inputs.map f') = true := by
  rcases hg with hg | hg
  · rw [hg]
    simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq]
    intro htrue b hb
    obtain ⟨a, ha, rfl⟩ := hb
    exact h a ha (htrue _ ⟨a, ha, rfl⟩)
  · rw [hg]
    simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
    rintro ⟨b, ⟨a, ha, rfl⟩, hb⟩
    exact ⟨f' a, ⟨a, ha, rfl⟩, h a ha hb⟩

theorem wires_mono (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (u v : List Bool) (hlen : u.length = v.length)
    (h : ∀ a, u.getD a false = true → v.getD a false = true) :
    ∀ a, (wiresFrom gs u).getD a false = true → (wiresFrom gs v).getD a false = true := by
  induction gs generalizing u v with
  | nil => exact h
  | cons g gs ih =>
    let b := g.op.eval (g.inputs.map fun a => u.getD a false)
    let b' := g.op.eval (g.inputs.map fun a => v.getD a false)
    change ∀ a, (wiresFrom gs (u ++ [b])).getD a false = true →
      (wiresFrom gs (v ++ [b'])).getD a false = true
    apply ih (fun t ht => hgs t (List.mem_cons_of_mem _ ht)) _ _ (by simp [hlen])
    intro a ha
    by_cases hlt : a < u.length
    · rw [List.getD_append _ _ _ _ (by omega : a < v.length)]
      exact h a (by simpa only [List.getD_append _ _ _ _ hlt] using ha)
    by_cases he : a = u.length
    · subst a
      have hb : b = true := by simpa using ha
      have hb' : b' = true := eval_mono g (hgs _ (by simp)) _ _ (fun a _ => h a) hb
      simpa [hlen] using hb'
    · rw [List.getD_eq_default _ _ (by simp; omega)] at ha
      cases ha

def value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (a : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD a false

def pulse {n : ℕ} (p : Fin n) (q : Fin n) : Bool := decide (q = p)

def singles {n : ℕ} (C : Circuit) (a : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun p => value C (pulse p) a = true

theorem value_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (a : ℕ) (ha : a < n) :
    value C x a = x ⟨a, ha⟩ := by
  change (wiresFrom C.gates (List.ofFn x)).getD a false = _
  rw [wires_keep _ _ _ (by simpa using ha)]
  simp [ha]

theorem singles_outside {n : ℕ} (C : Circuit) (a : ℕ) (ha : n + C.size ≤ a) :
    singles (n := n) C a = ∅ := by
  ext p
  have hh : (wiresFrom C.gates (List.ofFn (pulse p))).length ≤ a := by
    simpa [wires_length, Circuit.size] using ha
  simp only [singles, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
    iff_false]
  change ¬ (wiresFrom C.gates (List.ofFn (pulse p))).getD a false = true
  rw [List.getD_eq_default _ _ hh]
  decide

theorem singles_input {n : ℕ} (C : Circuit) (a : ℕ) (ha : a < n) :
    (singles (n := n) C a).card = 1 := by
  have hs : singles (n := n) C a = {⟨a, ha⟩} := by
    ext p
    simp [singles, value_input C _ _ ha, pulse, eq_comm]
  simp [hs]

def deps (C : Circuit) (n a : ℕ) : Finset ℕ :=
  ((C.gates[a - n]?).toList.flatMap Gate.inputs).toFinset.filter (· < a)

theorem deps_at (C : Circuit) (n a : ℕ) (ha : a - n < C.gates.length) :
    deps C n a = (C.gates[a - n]'ha).inputs.toFinset.filter (· < a) := by
  simp [deps, List.getElem?_eq_getElem ha]

theorem deps_binary (C : Circuit) (n : ℕ) (h : ∀ g ∈ C.gates, g.inputs.length = 2) :
    ∀ a, (deps C n a).card ≤ 2 := by
  intro a
  by_cases ha : a - n < C.gates.length
  · rw [deps_at C n a ha]
    exact (Finset.card_filter_le _ _).trans ((List.toFinset_card_le _).trans (by
      rw [h _ (List.getElem_mem _) ]))
  · simp [deps, List.getElem?_eq_none (by omega : C.gates.length ≤ a - n)]

theorem value_step {n : ℕ} (C : Circuit) (u v : Fin n → Bool)
    (hgs : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (a : ℕ) (hal : n ≤ a) (har : a < n + C.size)
    (h : ∀ w ∈ deps C n a, value C u w = true → value C v w = true) :
    value C u a = true → value C v a = true := by
  let j := a - n
  have hj : j < C.gates.length := by
    simp only [Circuit.size] at har
    dsimp [j]
    omega
  have ha (x : Fin n → Bool) : (List.ofFn x).length + j = a := by
    simp [j]
    omega
  have heval (x : Fin n → Bool) : value C x a =
      (C.gates[j]'hj).op.eval ((C.gates[j]'hj).inputs.map fun w =>
        (wiresFrom (C.gates.take j) (List.ofFn x)).getD w false) := by
    change (wiresFrom C.gates (List.ofFn x)).getD a false = _
    rw [← ha x, wires_at _ _ _ hj]
  rw [heval u, heval v]
  refine eval_mono _ (hgs _ (List.getElem_mem _)) _ _ ?_
  intro w hw htrue
  have hlen (x : Fin n → Bool) : (wiresFrom (C.gates.take j) (List.ofFn x)).length = a := by
    rw [wires_length, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj), ha x]
  have hwlt : w < a := by
    by_contra hlt
    rw [List.getD_eq_default _ _ (by rw [hlen]; omega)] at htrue
    cases htrue
  have hd : w ∈ deps C n a := by
    rw [deps_at C n a hj]
    simpa [hwlt] using hw
  have hv (x : Fin n → Bool) : value C x w =
      (wiresFrom (C.gates.take j) (List.ofFn x)).getD w false := by
    change (wiresFrom C.gates (List.ofFn x)).getD w false = _
    conv_lhs => rw [← List.take_append_drop j C.gates, wires_split]
    exact wires_keep _ _ _ (by rwa [hlen])
  rw [← hv v]
  exact h w hd (by rwa [hv u])

theorem value_mono {n : ℕ} (C : Circuit) (u v : Fin n → Bool)
    (hgs : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (h : ∀ p, u p = true → v p = true) :
    ∀ a, value C u a = true → value C v a = true := by
  apply wires_mono C.gates hgs _ _ (by simp)
  intro a hau
  by_cases ha : a < n
  · simpa [ha] using h ⟨a, ha⟩ (by simpa [ha] using hau)
  · rw [List.getD_eq_default _ _ (by simp; omega)] at hau
    cases hau

noncomputable def privateGates {n : ℕ} (C : Circuit) (S : Finset (Fin n)) : Finset ℕ := by
  classical
  exact (Finset.range (n + C.size)).filter fun a =>
    n ≤ a ∧ singles C a ⊆ S ∧ 2 ≤ (singles (n := n) C a).card

theorem private_bound {n : ℕ} (C : Circuit) (S : Finset (Fin n)) (o c k : ℕ)
    (hgs : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hbin : ∀ g ∈ C.gates, g.inputs.length = 2)
    (hpromise : ∀ x : Fin n → Bool, (Finset.univ.filter (fun q => x q = true)).card ≤ k →
      (∀ q ∈ S, x q = false) → value C x o = false)
    (hck : c ≤ k) (haccept : c + 1 ≤ (singles (n := n) C o).card) :
    c ≤ (privateGates C S).card := by
  classical
  let P := privateGates C S
  have hP : ∀ a ∈ P, a < n + C.size := fun a ha =>
    Finset.mem_range.mp (Finset.mem_filter.mp ha).1
  obtain ⟨E, hEc, _, hEd, htransfer⟩ := frontier (deps C n) (deps_binary C n hbin)
    (fun a b hb => (Finset.mem_filter.mp hb).2) (n + C.size) P {o} hP
  simp only [Finset.card_singleton] at hEc
  by_contra hc
  have hEc' : E.card ≤ c := by change ¬ c ≤ P.card at hc; omega
  let small := E.filter fun a => singles C a ⊆ S
  let bad := small.biUnion (singles (n := n) C)
  have hsmall : ∀ a ∈ small, (singles (n := n) C a).card ≤ 1 := by
    intro a hm
    obtain ⟨ha, hS⟩ := Finset.mem_filter.mp hm
    by_cases hlow : a < n
    · rw [singles_input C a hlow]
    by_cases hhigh : n + C.size ≤ a
    · simp [singles_outside C a hhigh]
    by_contra hcard
    have hp : a ∈ P := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_range.mpr (by omega), by omega, hS, by omega⟩
    exact Finset.disjoint_left.mp hEd ha hp
  have hbad : bad.card ≤ E.card := by
    apply Finset.card_biUnion_le.trans
    calc
      ∑ a ∈ small, (singles (n := n) C a).card ≤ ∑ _a ∈ small, 1 :=
        Finset.sum_le_sum hsmall
      _ ≤ E.card := by simpa using Finset.card_filter_le E (fun a => singles C a ⊆ S)
  have hnsub : ¬ singles (n := n) C o ⊆ bad := fun hs => by
    have := Finset.card_le_card hs
    omega
  obtain ⟨p, hp, hpb⟩ := Finset.not_subset.mp hnsub
  let exits := E.filter fun a => ¬ singles C a ⊆ S
  have hwit (a : exits) : ∃ q ∈ singles (n := n) C a.val, q ∉ S :=
    Finset.not_subset.mp (Finset.mem_filter.mp a.property).2
  let chosen (a : exits) := Classical.choose (hwit a)
  let X := exits.attach.image chosen
  have hXcard : X.card ≤ k := by
    calc
      X.card ≤ exits.attach.card := Finset.card_image_le
      _ = exits.card := Finset.card_attach
      _ ≤ E.card := Finset.card_filter_le _ _
      _ ≤ k := hEc'.trans hck
  let x (q : Fin n) := decide (q ∈ X)
  have hxout : ∀ q ∈ S, x q = false := by
    intro q hq
    apply decide_eq_false
    intro hmem
    obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hmem
    have hz : chosen a ∉ S := (Classical.choose_spec (hwit a)).2
    exact hz (ha.symm ▸ hq)
  have hxcount : Finset.univ.filter (fun q => x q = true) = X := by
    ext q
    simp [x]
  have hfalse := hpromise x (by rwa [hxcount]) hxout
  have hcmp : ∀ a ∈ E, value C (pulse p) a = true → value C x a = true := by
    intro a ha hv
    have hpa : p ∈ singles (n := n) C a := by simpa [singles] using hv
    have hnot : ¬ singles C a ⊆ S := by
      intro hS
      exact hpb (Finset.mem_biUnion.mpr ⟨a, Finset.mem_filter.mpr ⟨ha, hS⟩, hpa⟩)
    let a' : exits := ⟨a, Finset.mem_filter.mpr ⟨ha, hnot⟩⟩
    have hx : chosen a' ∈ X := Finset.mem_image.mpr ⟨a', Finset.mem_attach _ _, rfl⟩
    have hm : ∀ q, pulse (chosen a') q = true → x q = true := by
      intro q hq
      have : q = chosen a' := by simpa [pulse] using hq
      simp [x, this, hx]
    apply value_mono C _ _ hgs hm a
    have hchoose := (Classical.choose_spec (hwit a')).1
    simpa [singles, chosen, a'] using hchoose
  have hstep : ∀ a ∈ P, (∀ w ∈ deps C n a, value C (pulse p) w = true →
      value C x w = true) → value C (pulse p) a = true → value C x a = true := by
    intro a ha
    have hlow : n ≤ a := (Finset.mem_filter.mp ha).2.1
    exact value_step C _ _ hgs a hlow (hP a ha)
  have ht := htransfer _ hstep hcmp o (Finset.mem_singleton_self o)
    (by simpa [singles] using hp)
  rw [hfalse] at ht
  cases ht

theorem count_private {n m : ℕ} (C : Circuit) (S : Fin m → Finset (Fin n))
    (hs : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) :
    ∑ i : Fin m, (privateGates C (S i)).card ≤ C.size := by
  classical
  let P (i : Fin m) := privateGates C (S i)
  have hd : (↑(Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint P := by
    intro i _ j _ hij
    change Disjoint (P i) (P j)
    rw [Finset.disjoint_left]
    intro a hi hj
    have hi' := (Finset.mem_filter.mp hi).2
    have hj' := (Finset.mem_filter.mp hj).2
    have hsub : singles (n := n) C a ⊆ S i ∩ S j := fun q hq =>
      Finset.mem_inter.mpr ⟨hi'.2.1 hq, hj'.2.1 hq⟩
    have hcard := (Finset.card_le_card hsub).trans (hs i j hij)
    have htwo := hi'.2.2
    omega
  change ∑ i : Fin m, (P i).card ≤ C.size
  rw [← Finset.card_biUnion hd]
  have hsub : Finset.univ.biUnion P ⊆ Finset.Ico n (n + C.size) := by
    intro a ha
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp ha
    have hmem := Finset.mem_filter.mp hi
    exact Finset.mem_Ico.mpr ⟨hmem.2.1, Finset.mem_range.mp hmem.1⟩
  exact (Finset.card_le_card hsub).trans (by simp)

end PEqualNP.Outside.L_meta_782

theorem PEqualNP.Outside.L_meta_782 : ∀ (n m k : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (c : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ i : Fin m, 2 ≤ (Finset.univ.filter (fun a : Fin n => (C.wires (List.ofFn (fun b : Fin n => decide (b = a)))).getD (o i) false = true)).card) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → (∀ (i : Fin m) (p : Fin n), (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (o i) false = true → p ∈ S i) → (∀ (i : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k → (∀ q ∈ S i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false) → (∀ i : Fin m, c i ≤ k) → (∀ i : Fin m, c i + 1 ≤ (Finset.univ.filter (fun a : Fin n => (C.wires (List.ofFn (fun b : Fin n => decide (b = a)))).getD (o i) false = true)).card) → ∑ i : Fin m, c i ≤ C.size := by
  intro n m k S C o c hs _ hg _ hp hk haccept
  calc
    ∑ i : Fin m, c i ≤ ∑ i : Fin m, (PEqualNP.Outside.L_meta_782.privateGates C (S i)).card := by
      apply Finset.sum_le_sum
      intro i _
      exact PEqualNP.Outside.L_meta_782.private_bound C (S i) (o i) (c i) k
        (fun g hg' => (hg g hg').1) (fun g hg' => (hg g hg').2) (hp i) (hk i) (haccept i)
    _ ≤ C.size := PEqualNP.Outside.L_meta_782.count_private C S hs
