import Mathlib.Combinatorics.Configuration
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Mathlib.Tactic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2461

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma run_stable (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (run gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    change (run gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])).getD i false = _
    rw [ih _ _ (by simp; omega)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma run_length (gs : List Gate) : ∀ w : List Bool, (run gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    change (run gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])).length = _
    rw [ih]; simp; omega

lemma run_gate (gs : List Gate) : ∀ (w : List Bool) (j : ℕ) (hj : j < gs.length),
    (∀ i ∈ (gs[j]).inputs, i < w.length + j) →
    (run gs w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i => (run gs w).getD i false) := by
  induction gs with
  | nil => intro w j hj; simp at hj
  | cons g gs ih =>
    intro w j hj hin
    have e : run (g :: gs) w =
      run gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    cases j with
    | zero =>
      simp only [List.getElem_cons_zero, Nat.add_zero] at hin ⊢
      have hm : (g.inputs.map fun i => (run (g :: gs) w).getD i false) =
          g.inputs.map fun i => w.getD i false := by
        apply List.map_congr_left
        intro i hi
        exact run_stable _ _ _ (hin i hi)
      rw [hm, e, run_stable _ _ _ (by simp)]
      simp [List.getD_eq_getElem?_getD]
    | succ j =>
      simp only [List.getElem_cons_succ] at hin ⊢
      have hj' : j < gs.length := by simpa using hj
      have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) j hj'
        (by intro i hi; have := hin i hi; simp; omega)
      rw [e]
      simp only [List.length_append, List.length_cons, List.length_nil] at this
      rw [show w.length + (j + 1) = w.length + (0 + 1) + j by omega]
      exact this

def val (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma val_var {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    val n C x w = x ⟨w, hw⟩ := by
  unfold val
  change (run C.gates (List.ofFn x)).getD w false = _
  rw [run_stable _ _ _ (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

lemma val_gate {n : ℕ} (C : Circuit) (hR : ReadsBack n C) (x : Fin n → Bool) (j : ℕ)
    (hj : j < C.gates.length) :
    val n C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map (val n C x)) := by
  have hg : gateAt C j = C.gates[j] := by simp [gateAt, List.getD_eq_getElem?_getD, hj]
  have := run_gate C.gates (List.ofFn x) j hj (by
    intro i hi; have := hR j hj i (by rw [hg]; exact hi); simpa using this)
  simp only [List.length_ofFn] at this
  rw [hg]
  exact this

lemma val_big {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : n + C.gates.length ≤ w) :
    val n C x w = false := by
  unfold val
  change (run C.gates (List.ofFn x)).getD w false = _
  rw [List.getD_eq_default]
  rw [run_length]; simpa using hw

inductive Live (n : ℕ) (C : Circuit) : ℕ → Prop
  | out : Live n C C.output
  | read (k w : ℕ) : k < C.gates.length → Live n C (n + k) → w ∈ (gateAt C k).inputs → Live n C w

lemma block {n : ℕ} (C : Circuit) (hR : ReadsBack n C) (b h : ℕ) (x y : Fin n → Bool)
    (hxy : ∀ i : Fin n, i.val ≠ b → x i = y i)
    (hb : ∀ k < C.gates.length, Live n C (n + k) → b ∈ (gateAt C k).inputs → k = h)
    (hh : val n C x (n + h) = val n C y (n + h)) :
    ∀ w, Live n C w → w ≠ b → val n C x w = val n C y w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hwb
    by_cases h1 : w < n
    · rw [val_var _ _ _ h1, val_var _ _ _ h1]
      exact hxy _ hwb
    · by_cases h2 : n + C.gates.length ≤ w
      · rw [val_big _ _ _ h2, val_big _ _ _ h2]
      · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
        have hk : k < C.gates.length := by omega
        by_cases hkh : k = h
        · rw [hkh]; exact hh
        · rw [val_gate C hR x k hk, val_gate C hR y k hk]
          congr 1
          apply List.map_congr_left
          intro i hi
          refine ih i (hR k hk i hi) (Live.read k i hk hw hi) ?_
          rintro rfl
          exact hkh (hb k hk hw hi)

theorem core (n : ℕ) (C : Circuit) (hn : 4 ≤ n)
    (hAO : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or) (hR : ReadsBack n C)
    (h2 : ∀ g ∈ C.gates, g.inputs.length = 2) (hs : C.size ≤ n)
    (hA : ∀ i j : Fin n, i ≠ j → ∃ x : Fin n → Bool, x j = false ∧
      circuitFun n C (Function.update x i true) ≠ circuitFun n C (Function.update x i false))
    (hO : ∀ i j : Fin n, i ≠ j → ∃ x : Fin n → Bool, x j = true ∧
      circuitFun n C (Function.update x i true) ≠ circuitFun n C (Function.update x i false)) :
    False := by
  classical
  have hF : ∀ x : Fin n → Bool, circuitFun n C x = val n C x C.output := fun x => rfl
  have hmem : ∀ k < C.gates.length, gateAt C k ∈ C.gates := by
    intro k hk
    simp [gateAt, List.getD_eq_getElem?_getD, hk]
  have other : ∀ i : Fin n, ∃ j : Fin n, i ≠ j := by
    intro i
    by_cases h0 : i.val = 0
    · exact ⟨⟨1, by omega⟩, fun h => by rw [h] at h0; simp at h0⟩
    · exact ⟨⟨0, by omega⟩, fun h => h0 (by rw [h])⟩
  -- the output is no variable
  have hout : ∀ i : Fin n, C.output ≠ i.val := by
    intro i hi
    obtain ⟨j, hj⟩ := other i
    obtain ⟨x, _, hx⟩ := hA j i hj.symm
    apply hx
    rw [hF, hF, hi, val_var _ _ _ i.2, val_var _ _ _ i.2]
    simp [Function.update_of_ne hj]
  set S : Finset ℕ := (Finset.range C.gates.length).filter fun k => Live n C (n + k) with hS
  have memS : ∀ k, k ∈ S ↔ k < C.gates.length ∧ Live n C (n + k) := by
    intro k; simp [hS]
  obtain ⟨R, hRdef⟩ : ∃ R : ℕ → Finset ℕ,
      R = fun w => S.filter fun k => w ∈ (gateAt C k).inputs := ⟨_, rfl⟩
  have memR : ∀ w k, k ∈ R w ↔ k ∈ S ∧ w ∈ (gateAt C k).inputs := by
    intro w k; simp [hRdef]
  -- every variable is read
  have varRead : ∀ i : Fin n, 1 ≤ (R i.val).card := by
    intro i
    by_contra hc
    have hemp : R i.val = ∅ := Finset.card_eq_zero.1 (by omega)
    obtain ⟨j, hj⟩ := other i
    obtain ⟨x, _, hx⟩ := hA i j hj
    apply hx
    rw [hF, hF]
    refine block C hR i.val C.gates.length _ _ ?_ ?_ ?_ _ Live.out (hout i)
    · intro k hk
      have : k ≠ i := fun h => hk (by rw [h])
      simp [Function.update_of_ne this]
    · intro k hk hl hi
      exact absurd ((memR i.val k).2 ⟨(memS k).2 ⟨hk, hl⟩, hi⟩) (by simp [hemp])
    · rw [val_big _ _ _ le_rfl, val_big _ _ _ le_rfl]
  -- every live gate but the output is read
  have gateRead : ∀ k ∈ S, n + k ≠ C.output → 1 ≤ (R (n + k)).card := by
    intro k hk hne
    have hl := ((memS k).1 hk).2
    generalize n + k = w at hl hne ⊢
    cases hl with
    | out => exact absurd rfl hne
    | read j _ hj hjl hin =>
      exact Finset.card_pos.2 ⟨j, (memR _ j).2 ⟨(memS j).2 ⟨hj, hjl⟩, hin⟩⟩
  -- a gate reading a variable read nowhere else, against another variable
  have key : ∀ (k v : ℕ) (i j : Fin n), k ∈ S → i ≠ j →
      ((gateAt C k).inputs = [i.val, v] ∨ (gateAt C k).inputs = [v, i.val]) →
      (∀ x, val n C x v = x j) → (R i.val).card ≤ 1 → False := by
    intro k v i j hk hij hin hv hc
    have hkm := (memS k).1 hk
    have hkR : k ∈ R i.val := (memR _ _).2 ⟨hk, by rcases hin with h | h <;> simp [h]⟩
    have hone : ∀ k' < C.gates.length, Live n C (n + k') → i.val ∈ (gateAt C k').inputs →
        k' = k := fun k' h1 h3 h4 =>
      Finset.card_le_one.1 hc k' ((memR _ _).2 ⟨(memS k').2 ⟨h1, h3⟩, h4⟩) k hkR
    have fin : ∀ x : Fin n → Bool,
        val n C (Function.update x i true) (n + k) = val n C (Function.update x i false) (n + k) →
        circuitFun n C (Function.update x i true) = circuitFun n C (Function.update x i false) := by
      intro x hx
      rw [hF, hF]
      refine block C hR i.val k _ _ ?_ hone hx _ Live.out (hout i)
      intro m hm
      have : m ≠ i := fun h => hm (by rw [h])
      simp [Function.update_of_ne this]
    rcases hAO _ (hmem k hkm.1) with hop | hop
    · obtain ⟨x, hxj, hx⟩ := hA i j hij
      refine hx (fin x ?_)
      rw [val_gate C hR _ k hkm.1, val_gate C hR _ k hkm.1, hop]
      rcases hin with h | h <;>
        simp [h, GateOp.eval, hv, Function.update_of_ne hij.symm, hxj]
    · obtain ⟨x, hxj, hx⟩ := hO i j hij
      refine hx (fin x ?_)
      rw [val_gate C hR _ k hkm.1, val_gate C hR _ k hkm.1, hop]
      rcases hin with h | h <;>
        simp [h, GateOp.eval, hv, Function.update_of_ne hij.symm, hxj]
  have two : ∀ k ∈ S, ∃ u v, (gateAt C k).inputs = [u, v] := by
    intro k hk
    exact List.length_eq_two.1 (h2 _ (hmem k ((memS k).1 hk).1))
  obtain ⟨T, hT⟩ : ∃ T, T = S.filter fun k => (gateAt C k).inputs.toFinset.card = 1 := ⟨_, rfl⟩
  -- double counting
  have hdc : ∑ k ∈ S, (gateAt C k).inputs.toFinset.card =
      ∑ w ∈ Finset.range (n + C.gates.length), (R w).card := by
    have := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
      (s := S) (t := Finset.range (n + C.gates.length))
      (fun k w => w ∈ (gateAt C k).inputs)
    simp only [Finset.bipartiteAbove, Finset.bipartiteBelow] at this
    rw [hRdef, ← this]
    apply Finset.sum_congr rfl
    intro k hk
    congr 1
    ext w
    simp only [List.mem_toFinset, Finset.mem_filter, Finset.mem_range]
    constructor
    · intro hw
      have hk' := ((memS k).1 hk).1
      have := hR k hk' w hw
      exact ⟨by omega, hw⟩
    · exact fun h => h.2
  have hlhs : ∑ k ∈ S, (gateAt C k).inputs.toFinset.card + T.card = 2 * S.card := by
    rw [hT, Finset.card_filter, ← Finset.sum_add_distrib]
    rw [Finset.sum_congr rfl (g := fun _ => 2), Finset.sum_const, smul_eq_mul, mul_comm]
    intro k hk
    obtain ⟨u, v, h⟩ := two k hk
    by_cases huv : u = v
    · simp [h, huv]
    · have : ([u, v] : List ℕ).toFinset.card = 2 := by
        simp [huv]
      rw [h, this]; simp
  obtain ⟨W, hW⟩ : ∃ W, W = Finset.range n ∪
    ((S.image fun k => n + k).erase C.output) := ⟨_, rfl⟩
  have hWcard : n + S.card ≤ W.card + 1 := by
    rw [hW, Finset.card_union_of_disjoint, Finset.card_range]
    · have h1 : (S.image fun k => n + k).card = S.card :=
        Finset.card_image_of_injective _ (fun a b h => by simpa using h)
      have h3 := Finset.pred_card_le_card_erase (s := S.image fun k => n + k) (a := C.output)
      omega
    · rw [Finset.disjoint_left]
      intro w hw hw'
      have := Finset.mem_of_mem_erase hw'
      simp only [Finset.mem_image] at this
      obtain ⟨k, _, rfl⟩ := this
      simp at hw
  have hWR : ∀ w ∈ W, 1 ≤ (R w).card := by
    intro w hw
    rw [hW, Finset.mem_union] at hw
    rcases hw with hw | hw
    · exact varRead ⟨w, Finset.mem_range.1 hw⟩
    · obtain ⟨hne, hw⟩ := Finset.mem_erase.1 hw
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hw
      exact gateRead k hk hne
  obtain ⟨D, hD⟩ : ∃ D, D = W.filter fun w => 2 ≤ (R w).card := ⟨_, rfl⟩
  have hWsub : W ⊆ Finset.range (n + C.gates.length) := by
    intro w hw
    rw [hW, Finset.mem_union] at hw
    rw [Finset.mem_range]
    rcases hw with hw | hw
    · have := Finset.mem_range.1 hw; omega
    · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 (Finset.mem_of_mem_erase hw)
      have := ((memS k).1 hk).1; omega
  have hrhs : W.card + D.card ≤ ∑ w ∈ Finset.range (n + C.gates.length), (R w).card := by
    refine le_trans ?_ (Finset.sum_le_sum_of_subset hWsub)
    rw [hD, Finset.card_filter, Finset.card_eq_sum_ones, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro w hw
    have := hWR w hw
    split_ifs <;> omega
  have hSm : S.card ≤ n := by
    refine le_trans (Finset.card_le_card (Finset.filter_subset _ _)) ?_
    rw [Finset.card_range]; exact hs
  have hDT : D.card + T.card ≤ 1 := by omega
  have hSge : 3 ≤ S.card := by omega
  have inD : ∀ i : Fin n, 2 ≤ (R i.val).card → i.val ∈ D := by
    intro i hi
    rw [hD, Finset.mem_filter, hW]
    exact ⟨Finset.mem_union_left _ (Finset.mem_range.2 i.2), hi⟩
  -- inputs of a live gate are variables or earlier live gates
  have inpS : ∀ k ∈ S, ∀ w ∈ (gateAt C k).inputs, w < n ∨ ∃ j ∈ S, w = n + j ∧ j < k := by
    intro k hk w hw
    have hk' := (memS k).1 hk
    have hlt := hR k hk'.1 w hw
    by_cases h : w < n
    · exact Or.inl h
    · refine Or.inr ⟨w - n, (memS _).2 ⟨by omega, ?_⟩, by omega, by omega⟩
      rw [show n + (w - n) = w by omega]
      exact Live.read k w hk'.1 hk'.2 hw
  have hSne : S.Nonempty := Finset.card_pos.1 (by omega)
  obtain ⟨a, haS, hamin⟩ : ∃ a ∈ S, ∀ b ∈ S, a ≤ b :=
    ⟨S.min' hSne, S.min'_mem hSne, fun b hb => S.min'_le b hb⟩
  obtain ⟨u, v, huv⟩ := two a haS
  have hvar : ∀ w ∈ (gateAt C a).inputs, w < n := by
    intro w hw
    rcases inpS a haS w hw with h | ⟨j, hj, _, hja⟩
    · exact h
    · exact absurd (hamin j hj) (by omega)
  have hu : u < n := hvar u (by simp [huv])
  have hv : v < n := hvar v (by simp [huv])
  by_cases e : u = v
  · subst e
    have haT : a ∈ T := by
      rw [hT, Finset.mem_filter]; exact ⟨haS, by simp [huv]⟩
    have hTpos : 1 ≤ T.card := Finset.card_pos.2 ⟨a, haT⟩
    have hD0 : D = ∅ := Finset.card_eq_zero.1 (by omega)
    have hle : ∀ i : Fin n, (R i.val).card ≤ 1 := by
      intro i
      by_contra hc
      have := inD i (by omega)
      rw [hD0] at this; simp at this
    have hTa : ∀ b ∈ T, b = a := fun b hb => Finset.card_le_one.1 (by omega) b hb a haT
    have hne : (S.erase a).Nonempty := by
      apply Finset.card_pos.1
      rw [Finset.card_erase_of_mem haS]; omega
    obtain ⟨b, hbS', hbmin⟩ : ∃ b ∈ S.erase a, ∀ c ∈ S.erase a, b ≤ c :=
      ⟨_, (S.erase a).min'_mem hne, fun c hc => (S.erase a).min'_le c hc⟩
    obtain ⟨hba, hbS⟩ := Finset.mem_erase.1 hbS'
    obtain ⟨p, q, hpq⟩ := two b hbS
    have hpqne : p ≠ q := by
      rintro rfl
      exact hba (hTa b (by rw [hT, Finset.mem_filter]; exact ⟨hbS, by simp [hpq]⟩))
    have hin : ∀ w ∈ (gateAt C b).inputs, w < n ∨ w = n + a := by
      intro w hw
      rcases inpS b hbS w hw with h | ⟨j, hj, rfl, hjb⟩
      · exact Or.inl h
      · right
        by_contra hc
        have : j ≠ a := fun h => hc (by rw [h])
        have := hbmin j (Finset.mem_erase.2 ⟨this, hj⟩)
        omega
    have hva : ∀ x, val n C x (n + a) = x ⟨u, hu⟩ := by
      intro x
      rw [val_gate C hR x a ((memS a).1 haS).1, huv]
      rcases hAO _ (hmem a ((memS a).1 haS).1) with hop | hop <;>
        simp [hop, GateOp.eval, val_var _ _ _ hu]
    have huR : ∀ w, w ∈ (gateAt C b).inputs → w ≠ u := by
      rintro w hw rfl
      exact hba (Finset.card_le_one.1 (hle ⟨w, hu⟩) b ((memR _ _).2 ⟨hbS, hw⟩) a
        ((memR _ _).2 ⟨haS, by simp [huv]⟩))
    rcases hin p (by simp [hpq]) with hp | hp
    · rcases hin q (by simp [hpq]) with hq | hq
      · exact key b q ⟨p, hp⟩ ⟨q, hq⟩ hbS (by simpa using hpqne) (Or.inl hpq)
          (fun x => val_var _ _ _ hq) (hle _)
      · refine key b q ⟨p, hp⟩ ⟨u, hu⟩ hbS ?_ (Or.inl hpq) (fun x => by rw [hq]; exact hva x)
          (hle _)
        simpa using huR p (by simp [hpq])
    · rcases hin q (by simp [hpq]) with hq | hq
      · refine key b p ⟨q, hq⟩ ⟨u, hu⟩ hbS ?_ (Or.inr hpq) (fun x => by rw [hp]; exact hva x)
          (hle _)
        simpa using huR q (by simp [hpq])
      · exact hpqne (hp.trans hq.symm)
  · have h1 : u ∈ D := by
      refine inD ⟨u, hu⟩ ?_
      by_contra hc
      exact key a v ⟨u, hu⟩ ⟨v, hv⟩ haS (by simpa using e) (Or.inl huv)
        (fun x => val_var _ _ _ hv) (by simp only at hc ⊢; omega)
    have h3 : v ∈ D := by
      refine inD ⟨v, hv⟩ ?_
      by_contra hc
      exact key a u ⟨v, hv⟩ ⟨u, hu⟩ haS (by simpa using Ne.symm e) (Or.inr huv)
        (fun x => val_var _ _ _ hu) (by simp only at hc ⊢; omega)
    have : 2 ≤ D.card := by
      rw [← Finset.card_pair e]
      apply Finset.card_le_card
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl <;> assumption
    omega

def adj {N : ℕ} (I : Fin N → Fin N → Prop) : Fin N ⊕ Fin N → Fin N ⊕ Fin N → Prop
  | Sum.inl p, Sum.inr l => I p l
  | Sum.inr l, Sum.inl p => I p l
  | _, _ => False

lemma adj_irrefl {N : ℕ} (I : Fin N → Fin N → Prop) (s : Fin N ⊕ Fin N) : ¬ adj I s s := by
  rcases s with s | s <;> simp [adj]

lemma adj_F {N : ℕ} (I : Fin N → Fin N → Prop) (x : Fin (N + N) → Bool) :
    (∃ p l : Fin N, I p l ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true) ↔
    ∃ s t, adj I s t ∧ x (finSumFinEquiv s) = true ∧ x (finSumFinEquiv t) = true := by
  constructor
  · rintro ⟨p, l, h, hp, hl⟩
    exact ⟨Sum.inl p, Sum.inr l, h, by simpa using hp, by simpa using hl⟩
  · rintro ⟨s | s, t | t, h, hs, ht⟩
    · exact h.elim
    · exact ⟨s, t, h, by simpa using hs, by simpa using ht⟩
    · exact ⟨t, s, h, by simpa using ht, by simpa using hs⟩
    · exact h.elim

lemma priv {N : ℕ} (I : Fin N → Fin N → Prop)
    (hp : ∀ p, ∃ l l', l ≠ l' ∧ I p l ∧ I p l') (hl : ∀ l, ∃ p p', p ≠ p' ∧ I p l ∧ I p' l)
    (he : ∀ p p' l l', I p l → I p' l → I p l' → I p' l' → p = p' ∨ l = l')
    (s t : Fin N ⊕ Fin N) (hst : s ≠ t) : ∃ k, adj I s k ∧ k ≠ t ∧ ¬ adj I k t := by
  rcases s with p | l
  · obtain ⟨l, l', hne, h1, h2⟩ := hp p
    rcases t with p' | m
    · have hpp : p ≠ p' := fun h => hst (by rw [h])
      by_cases h : I p' l
      · refine ⟨Sum.inr l', h2, by simp, fun h' => ?_⟩
        rcases he p p' l l' h1 h h2 h' with e | e
        · exact hpp e
        · exact hne e
      · exact ⟨Sum.inr l, h1, by simp, h⟩
    · by_cases h : l = m
      · exact ⟨Sum.inr l', h2, fun e => hne (h.trans (Sum.inr.inj e).symm), fun e => e.elim⟩
      · exact ⟨Sum.inr l, h1, fun e => h (Sum.inr.inj e), fun e => e.elim⟩
  · obtain ⟨p, p', hne, h1, h2⟩ := hl l
    rcases t with m | l'
    · by_cases h : p = m
      · exact ⟨Sum.inl p', h2, fun e => hne (h.trans (Sum.inl.inj e).symm), fun e => e.elim⟩
      · exact ⟨Sum.inl p, h1, fun e => h (Sum.inl.inj e), fun e => e.elim⟩
    · have hll : l ≠ l' := fun h => hst (by rw [h])
      by_cases h : I p l'
      · refine ⟨Sum.inl p', h2, by simp, fun h' => ?_⟩
        rcases he p p' l l' h1 h2 h h' with e | e
        · exact hne e
        · exact hll e
      · exact ⟨Sum.inl p, h1, by simp, h⟩

theorem noCircuit (N : ℕ) (hN : 2 ≤ N) (I : Fin N → Fin N → Prop)
    (hp : ∀ p, ∃ l l', l ≠ l' ∧ I p l ∧ I p l') (hl : ∀ l, ∃ p p', p ≠ p' ∧ I p l ∧ I p' l)
    (he : ∀ p p' l l', I p l → I p' l → I p l' → I p' l' → p = p' ∨ l = l')
    (C : Circuit) (hAO : PEqualNP.TopForm.IsAO2 (N + N) C)
    (hF : ∀ x : Fin (N + N) → Bool, circuitFun (N + N) C x = true ↔
      ∃ p l : Fin N, I p l ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true)
    (hs : C.size ≤ 2 * N) : False := by
  classical
  have hF' := fun x => (hF x).trans (adj_F I x)
  have inj := (finSumFinEquiv (m := N) (n := N)).injective
  have gen : ∀ (s t k : Fin N ⊕ Fin N), s ≠ t → adj I s k → ¬ adj I k t → ¬ adj I t k →
      ∀ (Q : Fin (N + N) → Prop) [DecidablePred Q], (∀ v, Q v → v = finSumFinEquiv t ∨ v = finSumFinEquiv k) →
      Q (finSumFinEquiv k) →
      circuitFun (N + N) C (Function.update (fun v => decide (Q v)) (finSumFinEquiv s) true) ≠
      circuitFun (N + N) C (Function.update (fun v => decide (Q v)) (finSumFinEquiv s) false) := by
    intro s t k hst hsk hkt htk Q _ hQ hQk
    have hks : k ≠ s := by rintro rfl; exact adj_irrefl I k hsk
    have h1 : circuitFun (N + N) C
        (Function.update (fun v => decide (Q v)) (finSumFinEquiv s) true) = true := by
      rw [hF']
      refine ⟨s, k, hsk, by simp, ?_⟩
      rw [Function.update_of_ne (fun h => hks (inj h))]
      simpa using hQk
    have h0 : ¬ circuitFun (N + N) C
        (Function.update (fun v => decide (Q v)) (finSumFinEquiv s) false) = true := by
      rw [hF']
      rintro ⟨a, b, hab, ha, hb⟩
      have cl : ∀ c, Function.update (fun v => decide (Q v)) (finSumFinEquiv s) false
          (finSumFinEquiv c) = true → c = t ∨ c = k := by
        intro c hc
        by_cases e : c = s
        · rw [e] at hc; simp at hc
        · rw [Function.update_of_ne (fun h => e (inj h))] at hc
          rcases hQ _ (by simpa using hc) with h | h
          · exact Or.inl (inj h)
          · exact Or.inr (inj h)
      rcases cl a ha with h | h <;> rcases cl b hb with h' | h' <;> rw [h, h'] at hab
      · exact adj_irrefl I _ hab
      · exact htk hab
      · exact hkt hab
      · exact adj_irrefl I _ hab
    rw [h1]
    exact fun h => h0 h.symm
  have symm : ∀ s t, adj I s t → adj I t s := by
    rintro (s | s) (t | t) h <;> exact h
  refine core (N + N) C (by omega) hAO.1 hAO.2.1 hAO.2.2 (by omega) ?_ ?_
  · intro i j hij
    obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨t, rfl⟩ := finSumFinEquiv.surjective j
    have hst : s ≠ t := fun h => hij (by rw [h])
    obtain ⟨k, h1, h2, h3⟩ := priv I hp hl he s t hst
    refine ⟨fun v => decide (v = finSumFinEquiv k), ?_, gen s t k hst h1 h3
      (fun h => h3 (symm _ _ h)) (fun v => v = finSumFinEquiv k) (fun v hv => Or.inr hv) rfl⟩
    simpa using fun h => h2 (inj h).symm
  · intro i j hij
    obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨t, rfl⟩ := finSumFinEquiv.surjective j
    have hst : s ≠ t := fun h => hij (by rw [h])
    obtain ⟨k, h1, h2, h3⟩ := priv I hp hl he s t hst
    refine ⟨fun v => decide (v = finSumFinEquiv t ∨ v = finSumFinEquiv k), by simp,
      gen s t k hst h1 h3 (fun h => h3 (symm _ _ h))
        (fun v => v = finSumFinEquiv t ∨ v = finSumFinEquiv k) (fun v hv => hv) (Or.inr rfl)⟩

open Configuration ProjectivePlane in
theorem plane : ∃ (N : ℕ) (I : Fin N → Fin N → Prop), N = 211 ^ 2 + 211 + 1 ∧
    (∀ l, Nat.card {p // I p l} = 211 + 1) ∧ (∀ p, Nat.card {l // I p l} = 211 + 1) ∧
    (∀ p p', p ≠ p' → ∃! l, I p l ∧ I p' l) ∧
    (∀ p p' l l', I p l → I p' l → I p l' → I p' l' → p = p' ∨ l = l') := by
  classical
  haveI : Fact (Nat.Prime 211) := ⟨by norm_num⟩
  let X := Projectivization (ZMod 211) (Fin 3 → ZMod 211)
  have hc : Nat.card X = 211 ^ 2 + 211 + 1 := by
    have := Projectivization.card_of_finrank (ZMod 211) (Fin 3 → ZMod 211) (n := 3) (by simp)
    change Nat.card (Projectivization (ZMod 211) (Fin 3 → ZMod 211)) = _
    rw [this]
    simp [Finset.sum_range_succ]
  haveI : Finite X := Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  haveI : Fintype X := Fintype.ofFinite X
  letI : Membership X X := inferInstanceAs (Membership
    (Projectivization (ZMod 211) (Fin 3 → ZMod 211))
    (Projectivization (ZMod 211) (Fin 3 → ZMod 211)))
  letI : ProjectivePlane X X := inferInstanceAs (ProjectivePlane
    (Projectivization (ZMod 211) (Fin 3 → ZMod 211))
    (Projectivization (ZMod 211) (Fin 3 → ZMod 211)))
  have hord : order X X = 211 := by
    have h := card_points X X
    rw [← Nat.card_eq_fintype_card, hc] at h
    nlinarith
  obtain ⟨e⟩ : Nonempty (Fin (211 ^ 2 + 211 + 1) ≃ X) :=
    ⟨(Finite.equivFinOfCardEq hc).symm⟩
  refine ⟨_, fun p l => e p ∈ e l, rfl, ?_, ?_, ?_, ?_⟩
  · intro l
    have := pointCount_eq X (e l)
    rw [hord] at this
    rw [← this]
    exact Nat.card_congr (e.subtypeEquiv fun p => Iff.rfl)
  · intro p
    have := lineCount_eq X (e p)
    rw [hord] at this
    rw [← this]
    exact Nat.card_congr (e.subtypeEquiv fun p => Iff.rfl)
  · intro p p' hpp
    have hne : e p ≠ e p' := fun h => hpp (e.injective h)
    have hm := HasLines.mkLine_ax (L := X) hne
    refine ⟨e.symm (HasLines.mkLine hne), by simpa using hm, ?_⟩
    intro l hl
    have := Nondegenerate.eq_or_eq hl.1 hl.2 hm.1 hm.2
    rcases this with h | h
    · exact absurd h hne
    · rw [← h]; simp
  · intro p p' l l' h1 h2 h3 h4
    rcases Nondegenerate.eq_or_eq h1 h2 h3 h4 with h | h
    · exact Or.inl (e.injective h)
    · exact Or.inr (e.injective h)

lemma pair {N : ℕ} (Q : Fin N → Prop) (h : Nat.card {p // Q p} = 211 + 1) :
    ∃ a b, a ≠ b ∧ Q a ∧ Q b := by
  classical
  rw [Nat.card_eq_fintype_card] at h
  obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card (α := {p // Q p}) (by omega)
  exact ⟨a, b, fun h => hab (Subtype.ext h), a.2, b.2⟩

end PEqualNP.Outside.L_meta_2461

theorem PEqualNP.Outside.L_meta_2461 : ¬ (∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3], (201 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) → ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (x2 + x2) x9 ∧ (∀ (x10 : Fin (x2 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x2 + x2) x9 x10 = Decidable.decide (∃ (x11 : Fin x2) (x12 : Fin x2), x3 x11 x12 ∧ x10 (Fin.castAdd x2 x11) = Bool.true ∧ x10 (Fin.natAdd x2 x12) = Bool.true)) ∧ PEqualNP.ReadK.IsReadK (x2 + x2) x9 (2 : ℕ) ∧ x9.size ≤ (2 : ℕ) * x2) := by
  classical
  intro H
  obtain ⟨N, I, hN, hpt, hln, hex, he⟩ := PEqualNP.Outside.L_meta_2461.plane
  obtain ⟨C, hAO, hF, _, hs⟩ := @H 211 N I (Classical.decRel I) (by norm_num) hN
    (fun l => by rw [← Nat.card_eq_fintype_card]; exact hpt l) hex
  refine PEqualNP.Outside.L_meta_2461.noCircuit N (by omega) I
    (fun p => PEqualNP.Outside.L_meta_2461.pair _ (hln p))
    (fun l => PEqualNP.Outside.L_meta_2461.pair (fun p => I p l) (hpt l)) he C hAO ?_ hs
  intro x
  rw [hF x, decide_eq_true_iff]
