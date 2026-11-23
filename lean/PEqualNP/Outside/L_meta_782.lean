import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L782

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

private theorem foldl_step_length (G : List Gate) (w : List Bool) :
    (G.foldl step w).length = w.length + G.length := by
  induction G generalizing w with
  | nil => simp
  | cons g G ih => rw [List.foldl_cons, ih]; simp [step]; omega

private theorem getD_append_lt (l l' : List Bool) (i : ℕ) (hi : i < l.length) :
    (l ++ l').getD i false = l.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private theorem getD_of_length_le (l : List Bool) (i : ℕ) (hi : l.length ≤ i) :
    l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

private theorem foldl_step_getD (G : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (G.foldl step w).getD i false = w.getD i false := by
  induction G generalizing w with
  | nil => rfl
  | cons g G ih =>
    rw [List.foldl_cons, ih _ (by simp [step]; omega)]
    exact getD_append_lt _ _ _ hi

private theorem foldl_step_getD_gate (G : List Gate) (w : List Bool) (t : ℕ) (ht : t < G.length) :
    (G.foldl step w).getD (w.length + t) false =
      (G[t]).op.eval ((G[t]).inputs.map fun i => ((G.take t).foldl step w).getD i false) := by
  have hsplit : G = G.take t ++ G[t] :: G.drop (t + 1) := by
    simp [List.take_append_drop]
  conv_lhs => rw [hsplit, List.foldl_append, List.foldl_cons]
  rw [foldl_step_getD _ _ _ (by simp only [step, List.length_append, List.length_singleton, foldl_step_length, List.length_take, Nat.min_eq_left ht.le]; omega)]
  simp only [step]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp only [foldl_step_length, List.length_take, Nat.min_eq_left ht.le]; omega)]
  simp [foldl_step_length, Nat.min_eq_left ht.le]

private theorem foldl_take_getD (G : List Gate) (w : List Bool) (t i : ℕ)
    (hi : i < ((G.take t).foldl step w).length) :
    (G.foldl step w).getD i false = ((G.take t).foldl step w).getD i false := by
  conv_lhs => rw [← List.take_append_drop t G, List.foldl_append]
  exact foldl_step_getD _ _ _ hi

private theorem gate_value (G : List Gate) (w : List Bool) (t : ℕ) (ht : t < G.length) :
    (G.foldl step w).getD (w.length + t) false =
      (G[t]).op.eval ((G[t]).inputs.map fun i =>
        if i < w.length + t then (G.foldl step w).getD i false else false) := by
  rw [foldl_step_getD_gate G w t ht]
  congr 1
  apply List.map_congr_left
  intro i _
  have hlen : ((G.take t).foldl step w).length = w.length + t := by
    rw [foldl_step_length, List.length_take, Nat.min_eq_left ht.le]
  split_ifs with h
  · exact (foldl_take_getD G w t i (by rw [hlen]; exact h)).symm
  · exact getD_of_length_le _ _ (by rw [hlen]; omega)

private def val (C : Circuit) (n : ℕ) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

private theorem val_input (C : Circuit) (n : ℕ) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    val C n x w = x ⟨w, hw⟩ := by
  unfold val
  rw [wires_eq, foldl_step_getD _ _ _ (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

private theorem val_none (C : Circuit) (n : ℕ) (x : Fin n → Bool) (j : ℕ)
    (hg : C.gates[j]? = none) : val C n x (n + j) = false := by
  unfold val
  apply getD_of_length_le
  rw [wires_eq, foldl_step_length]
  have := List.getElem?_eq_none_iff.mp hg
  simp only [List.length_ofFn]
  omega

private theorem val_gate (C : Circuit) (n : ℕ) (x : Fin n → Bool) (j : ℕ) (h : Gate)
    (hg : C.gates[j]? = some h) :
    val C n x (n + j) =
      h.op.eval (h.inputs.map fun i => if i < n + j then val C n x i else false) := by
  obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.mp hg
  have := gate_value C.gates (List.ofFn x) j hj
  simp only [List.length_ofFn] at this
  exact this

private theorem val_or (C : Circuit) (n : ℕ) (x : Fin n → Bool) (j : ℕ) (h : Gate)
    (hg : C.gates[j]? = some h) (hop : h.op = GateOp.or) :
    val C n x (n + j) = true ↔ ∃ w ∈ h.inputs, w < n + j ∧ val C n x w = true := by
  rw [val_gate C n x j h hg, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id]
  constructor
  · rintro ⟨w, hw, hv⟩
    by_cases hlt : w < n + j
    · exact ⟨w, hw, hlt, by simpa [hlt] using hv⟩
    · simp [hlt] at hv
  · rintro ⟨w, hw, hlt, hv⟩
    exact ⟨w, hw, by simpa [hlt] using hv⟩

private theorem val_and (C : Circuit) (n : ℕ) (x : Fin n → Bool) (j : ℕ) (h : Gate)
    (hg : C.gates[j]? = some h) (hop : h.op = GateOp.and) :
    val C n x (n + j) = true ↔ ∀ w ∈ h.inputs, w < n + j ∧ val C n x w = true := by
  rw [val_gate C n x j h hg, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id]
  constructor
  · intro hall w hw
    have hv := hall w hw
    by_cases hlt : w < n + j
    · exact ⟨hlt, by simpa [hlt] using hv⟩
    · simp [hlt] at hv
  · intro hall w hw
    obtain ⟨hlt, hv⟩ := hall w hw
    simpa [hlt] using hv


private theorem card_le_of_rel {α β : Type} (s : Finset α) (t : Finset β) (Q : α → β → Prop)
    (h1 : ∀ a ∈ s, ∃ b ∈ t, Q a b)
    (h2 : ∀ a1 ∈ s, ∀ a2 ∈ s, ∀ b, Q a1 b → Q a2 b → a1 = a2) : s.card ≤ t.card := by
  classical
  have hsub : s ⊆ t.biUnion (fun b => s.filter (fun a => Q a b)) := by
    intro a ha
    obtain ⟨b, hb, hq⟩ := h1 a ha
    exact Finset.mem_biUnion.mpr ⟨b, hb, Finset.mem_filter.mpr ⟨ha, hq⟩⟩
  calc s.card ≤ (t.biUnion fun b => s.filter fun a => Q a b).card := Finset.card_le_card hsub
    _ ≤ ∑ b ∈ t, (s.filter fun a => Q a b).card := Finset.card_biUnion_le
    _ ≤ ∑ b ∈ t, 1 := Finset.sum_le_sum (fun b _ => Finset.card_le_one.mpr (by
        intro a1 h1' a2 h2'
        rw [Finset.mem_filter] at h1' h2'
        exact h2 a1 h1'.1 a2 h2'.1 b h1'.2 h2'.2))
    _ = t.card := by simp

def e1 {n : ℕ} (t : Fin n) : Fin n → Bool := fun i => decide (i = t)

def Aset (C : Circuit) (n : ℕ) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun a => val C n (e1 a) w = true)

abbrev Priv (C : Circuit) (n : ℕ) (S : Finset (Fin n)) (w : ℕ) : Prop :=
  Aset C n w ⊆ S ∧ 2 ≤ (Aset C n w).card

def kids (C : Circuit) (n u : ℕ) : Finset ℕ :=
  match C.gates[u - n]? with
  | some g => g.inputs.toFinset.filter (· < u)
  | none => ∅

theorem val_mono (C : Circuit) (n : ℕ)
    (hM : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : Fin n → Bool) (hxy : ∀ q, x q = true → y q = true) :
    ∀ w, val C n x w = true → val C n y w = true := by
  intro w
  refine Nat.strong_induction_on w ?_
  intro w ih hw
  by_cases hn : w < n
  · rw [val_input C n x w hn] at hw
    rw [val_input C n y w hn]
    exact hxy _ hw
  · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
    cases hg : C.gates[j]? with
    | none => rw [val_none C n x j hg] at hw; exact absurd hw (by simp)
    | some h =>
      rcases hM h (List.mem_of_getElem? hg) with hop | hop
      · rw [val_and C n x j h hg hop] at hw
        rw [val_and C n y j h hg hop]
        intro v hv
        obtain ⟨hlt, hv'⟩ := hw v hv
        exact ⟨hlt, ih v hlt hv'⟩
      · rw [val_or C n x j h hg hop] at hw
        rw [val_or C n y j h hg hop]
        obtain ⟨v, hv, hlt, hv'⟩ := hw
        exact ⟨v, hv, hlt, ih v hlt hv'⟩

theorem Aset_input (C : Circuit) (n w : ℕ) (hw : w < n) : (Aset C n w).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro a ha b hb
  simp only [Aset, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  rw [val_input C n _ w hw] at ha hb
  simp only [e1, decide_eq_true_eq] at ha hb
  exact ha.symm.trans hb

theorem priv_gate {C : Circuit} {n : ℕ} {S : Finset (Fin n)} {w : ℕ} (hp : Priv C n S w) :
    ∃ j h, w = n + j ∧ C.gates[j]? = some h := by
  by_cases hn : w < n
  · have h1 := Aset_input C n w hn
    have h2 := hp.2
    omega
  · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
    cases hg : C.gates[j]? with
    | none =>
      exfalso
      have h0 : Aset C n (n + j) = ∅ := by
        ext a
        simp [Aset, val_none C n (e1 a) j hg]
      have h2 := hp.2
      rw [h0] at h2
      simp at h2
    | some h => exact ⟨j, h, rfl, hg⟩

theorem kids_card (C : Circuit) (n u : ℕ) (hL : ∀ g ∈ C.gates, g.inputs.length = 2) :
    (kids C n u).card ≤ 2 := by
  cases hg : C.gates[u - n]? with
  | none => simp [kids, hg]
  | some g =>
    simp only [kids, hg]
    calc (g.inputs.toFinset.filter (· < u)).card ≤ g.inputs.toFinset.card :=
          Finset.card_filter_le _ _
      _ ≤ g.inputs.length := List.toFinset_card_le _
      _ = 2 := hL g (List.mem_of_getElem? hg)

theorem mem_kids {C : Circuit} {n j : ℕ} {h : Gate} {c : ℕ} (hg : C.gates[j]? = some h)
    (hc : c ∈ h.inputs) (hlt : c < n + j) : c ∈ kids C n (n + j) := by
  simp only [kids, Nat.add_sub_cancel_left, hg, Finset.mem_filter, List.mem_toFinset]
  exact ⟨hc, hlt⟩

theorem one_out (C : Circuit) (n k c : ℕ) (S : Finset (Fin n)) (o : ℕ)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (h2 : 2 ≤ (Aset C n o).card) (hsub : Aset C n o ⊆ S)
    (hpr : ∀ x : Fin n → Bool, (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k →
      (∀ q ∈ S, x q = false) → val C n x o = false)
    (hck : c ≤ k) (hca : c + 1 ≤ (Aset C n o).card) :
    c ≤ ((Finset.Ico n (n + C.size)).filter (Priv C n S)).card := by
  classical
  have hM : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := fun g hg => (hG g hg).1
  have hL : ∀ g ∈ C.gates, g.inputs.length = 2 := fun g hg => (hG g hg).2
  have hpo : Priv C n S o := ⟨hsub, h2⟩
  let st : ℕ → ℕ → Prop := fun u v => v ∈ kids C n u ∧ Priv C n S v
  have reach_priv : ∀ w, Relation.ReflTransGen st o w → Priv C n S w := by
    intro w hw
    cases hw with
    | refl => exact hpo
    | tail _ hst => exact hst.2
  have priv_range : ∀ w, Priv C n S w → n ≤ w ∧ w < n + C.size := by
    intro w hw
    obtain ⟨j, h, rfl, hg⟩ := priv_gate hw
    have := (List.getElem?_eq_some_iff.mp hg).1
    unfold Circuit.size
    omega
  set R := (Finset.range (n + C.size)).filter (fun w => Relation.ReflTransGen st o w) with hR
  have memR : ∀ w, w ∈ R ↔ Relation.ReflTransGen st o w := by
    intro w
    rw [hR, Finset.mem_filter, Finset.mem_range]
    exact ⟨fun h => h.2, fun h => ⟨(priv_range w (reach_priv w h)).2, h⟩⟩
  have hoR : o ∈ R := (memR o).mpr Relation.ReflTransGen.refl
  have RP : R ⊆ (Finset.Ico n (n + C.size)).filter (Priv C n S) := by
    intro w hw
    have hp := reach_priv w ((memR w).mp hw)
    have := priv_range w hp
    simp only [Finset.mem_filter, Finset.mem_Ico]
    exact ⟨this, hp⟩
  set E := (R.biUnion (kids C n)).filter (fun v => ¬ Priv C n S v) with hE
  have hEcard : E.card ≤ R.card + 1 := by
    have hdisj : Disjoint E (R.erase o) := by
      rw [Finset.disjoint_left]
      intro v hvE hvR
      exact (Finset.mem_filter.mp hvE).2
        (reach_priv v ((memR v).mp (Finset.mem_of_mem_erase hvR)))
    have hsub2 : E ∪ R.erase o ⊆ R.biUnion (kids C n) := by
      intro v hv
      rcases Finset.mem_union.mp hv with hv | hv
      · exact (Finset.mem_filter.mp hv).1
      · obtain ⟨hne, hvR⟩ := Finset.mem_erase.mp hv
        have hrt := (memR v).mp hvR
        cases hrt with
        | refl => exact absurd rfl hne
        | tail hu hst =>
          exact Finset.mem_biUnion.mpr ⟨_, (memR _).mpr hu, hst.1⟩
    have hc1 : (E ∪ R.erase o).card = E.card + (R.card - 1) := by
      rw [Finset.card_union_of_disjoint hdisj, Finset.card_erase_of_mem hoR]
    have hc2 : (R.biUnion (kids C n)).card ≤ 2 * R.card := by
      calc (R.biUnion (kids C n)).card ≤ ∑ u ∈ R, (kids C n u).card := Finset.card_biUnion_le
        _ ≤ ∑ u ∈ R, 2 := Finset.sum_le_sum (fun u _ => kids_card C n u hL)
        _ = 2 * R.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    have hc3 := Finset.card_le_card hsub2
    have hRpos : 0 < R.card := Finset.card_pos.mpr ⟨o, hoR⟩
    omega
  let pick : ℕ → Finset (Fin n) := fun v =>
    if h : (Aset C n v \ S).Nonempty then {h.choose} else ∅
  set X := E.biUnion pick with hX
  have hXcard : X.card ≤ E.card := by
    calc X.card ≤ ∑ v ∈ E, (pick v).card := Finset.card_biUnion_le
      _ ≤ ∑ v ∈ E, 1 := Finset.sum_le_sum (fun v _ => by
          simp only [pick]
          split_ifs <;> simp)
      _ = E.card := by simp
  have hXS : ∀ q ∈ X, q ∉ S := by
    intro q hq
    obtain ⟨v, _, hqv⟩ := Finset.mem_biUnion.mp hq
    simp only [pick] at hqv
    split_ifs at hqv with h
    · rw [Finset.mem_singleton] at hqv
      subst hqv
      exact (Finset.mem_sdiff.mp h.choose_spec).2
    · simp at hqv
  have hXhit : ∀ v ∈ E, ¬ Aset C n v ⊆ S → ∃ p ∈ X, p ∈ Aset C n v := by
    intro v hv hns
    have h : (Aset C n v \ S).Nonempty := Finset.sdiff_nonempty.mpr hns
    refine ⟨h.choose, Finset.mem_biUnion.mpr ⟨v, hv, ?_⟩, (Finset.mem_sdiff.mp h.choose_spec).1⟩
    simp only [pick, dif_pos h, Finset.mem_singleton]
  let xs : Fin n → Bool := fun q => decide (q ∈ X)
  have hxs_card : (Finset.univ.filter (fun q : Fin n => xs q = true)) = X := by
    ext q
    simp [xs]
  have walk : ∀ u, u ∈ R → ∀ a, a ∈ Aset C n u → val C n xs u = false →
      ∃ v ∈ E, a ∈ Aset C n v ∧ (Aset C n v).card ≤ 1 := by
    intro u
    refine Nat.strong_induction_on u ?_
    intro u ih huR a ha hxu
    have hpu := reach_priv u ((memR u).mp huR)
    obtain ⟨j, h, rfl, hg⟩ := priv_gate hpu
    have haT : val C n (e1 a) (n + j) = true := by
      simpa [Aset] using ha
    obtain ⟨d, hd, hlt, hda, hdx⟩ : ∃ d ∈ h.inputs, d < n + j ∧
        val C n (e1 a) d = true ∧ val C n xs d = false := by
      rcases hM h (List.mem_of_getElem? hg) with hop | hop
      · have h1 := (val_and C n (e1 a) j h hg hop).mp haT
        have h2 : ¬ ∀ w ∈ h.inputs, w < n + j ∧ val C n xs w = true := by
          rw [← val_and C n xs j h hg hop]
          simp [hxu]
        push_neg at h2
        obtain ⟨d, hd, hd2⟩ := h2
        obtain ⟨hlt, hda⟩ := h1 d hd
        exact ⟨d, hd, hlt, hda, by simpa using hd2 hlt⟩
      · obtain ⟨d, hd, hlt, hda⟩ := (val_or C n (e1 a) j h hg hop).mp haT
        have h2 : ¬ ∃ w ∈ h.inputs, w < n + j ∧ val C n xs w = true := by
          rw [← val_or C n xs j h hg hop]
          simp [hxu]
        refine ⟨d, hd, hlt, hda, ?_⟩
        cases hv : val C n xs d
        · rfl
        · exact absurd ⟨d, hd, hlt, hv⟩ h2
    have hkid : d ∈ kids C n (n + j) := mem_kids hg hd hlt
    have hads : a ∈ Aset C n d := by simp [Aset, hda]
    by_cases hpd : Priv C n S d
    · have hdR : d ∈ R :=
        (memR d).mpr (Relation.ReflTransGen.tail ((memR _).mp huR) ⟨hkid, hpd⟩)
      exact ih d hlt hdR a hads hdx
    · have hdE : d ∈ E :=
        Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr ⟨n + j, huR, hkid⟩, hpd⟩
      refine ⟨d, hdE, hads, ?_⟩
      by_cases hs : Aset C n d ⊆ S
      · have : ¬ 2 ≤ (Aset C n d).card := fun h2 => hpd ⟨hs, h2⟩
        omega
      · exfalso
        obtain ⟨p, hpX, hpA⟩ := hXhit d hdE hs
        have hp1 : val C n (e1 p) d = true := by simpa [Aset] using hpA
        have hmono := val_mono C n hM (e1 p) xs (fun q hq => by
          simp only [e1, decide_eq_true_eq] at hq
          subst hq
          simp [xs, hpX]) d hp1
        rw [hdx] at hmono
        exact absurd hmono (by simp)
  have hRP := Finset.card_le_card RP
  by_cases hval : val C n xs o = true
  · have hk : k < X.card := by
      by_contra hk
      push_neg at hk
      have := hpr xs (by rw [hxs_card]; exact hk) (fun q hq => by
        simp only [xs, decide_eq_false_iff_not]
        exact fun hqX => hXS q hqX hq)
      rw [hval] at this
      exact absurd this (by simp)
    omega
  · have hval' : val C n xs o = false := by simpa using hval
    have hA : (Aset C n o).card ≤ E.card := card_le_of_rel (Aset C n o) E
      (fun a v => a ∈ Aset C n v ∧ (Aset C n v).card ≤ 1)
      (fun a ha => walk o hoR a ha hval')
      (fun a1 _ a2 _ v h1 h2 => Finset.card_le_one.mp h1.2 a1 h1.1 a2 h2.1)
    omega

theorem main (n m k : ℕ) (S : Fin m → Finset (Fin n)) (C : Circuit) (o c : Fin m → ℕ)
    (h1 : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (h2 : ∀ i : Fin m, 2 ≤ (Aset C n (o i)).card)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (h4 : ∀ (i : Fin m) (p : Fin n), val C n (e1 p) (o i) = true → p ∈ S i)
    (h5 : ∀ (i : Fin m) (x : Fin n → Bool),
      (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k →
      (∀ q ∈ S i, x q = false) → val C n x (o i) = false)
    (h6 : ∀ i : Fin m, c i ≤ k) (h7 : ∀ i : Fin m, c i + 1 ≤ (Aset C n (o i)).card) :
    ∑ i : Fin m, c i ≤ C.size := by
  classical
  let P : Fin m → Finset ℕ := fun i => (Finset.Ico n (n + C.size)).filter (Priv C n (S i))
  have hc : ∀ i, c i ≤ (P i).card := fun i =>
    one_out C n k (c i) (S i) (o i) hG (h2 i)
      (fun p hp => h4 i p (by simpa [Aset] using hp)) (h5 i) (h6 i) (h7 i)
  have hdisj : ∀ i ∈ (Finset.univ : Finset (Fin m)), ∀ j ∈ (Finset.univ : Finset (Fin m)),
      i ≠ j → Disjoint (P i) (P j) := by
    intro i _ j _ hij
    rw [Finset.disjoint_left]
    intro w hwi hwj
    have pi := (Finset.mem_filter.mp hwi).2
    have pj := (Finset.mem_filter.mp hwj).2
    have hs := Finset.card_le_card (Finset.subset_inter pi.1 pj.1)
    have := h1 i j hij
    have := pi.2
    omega
  calc ∑ i, c i ≤ ∑ i, (P i).card := Finset.sum_le_sum (fun i _ => hc i)
    _ = (Finset.univ.biUnion P).card := (Finset.card_biUnion hdisj).symm
    _ ≤ (Finset.Ico n (n + C.size)).card :=
        Finset.card_le_card (Finset.biUnion_subset.mpr (fun i _ => Finset.filter_subset _ _))
    _ = C.size := by simp

end PEqualNP.Outside.L782

theorem PEqualNP.Outside.L_meta_782 : ∀ (n m k : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (c : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ i : Fin m, 2 ≤ (Finset.univ.filter (fun a : Fin n => (C.wires (List.ofFn (fun b : Fin n => decide (b = a)))).getD (o i) false = true)).card) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → (∀ (i : Fin m) (p : Fin n), (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (o i) false = true → p ∈ S i) → (∀ (i : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k → (∀ q ∈ S i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false) → (∀ i : Fin m, c i ≤ k) → (∀ i : Fin m, c i + 1 ≤ (Finset.univ.filter (fun a : Fin n => (C.wires (List.ofFn (fun b : Fin n => decide (b = a)))).getD (o i) false = true)).card) → ∑ i : Fin m, c i ≤ C.size := by
  intro n m k S C o c h1 h2 h3 h4 h5 h6 h7
  exact PEqualNP.Outside.L782.main n m k S C o c h1 h2 h3 h4 h5 h6 h7
