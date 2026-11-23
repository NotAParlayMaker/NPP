import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Card
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.ByContra
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_925_aux

open PEqualNP.CircuitLowerBounds

-- The wire evaluation lemmas through val_and are adapted from L_meta_613.
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

def val (C : Circuit) (n : ℕ) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

theorem val_input (C : Circuit) (n : ℕ) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
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

def children (C : Circuit) (n w : ℕ) : Finset ℕ :=
  if n ≤ w then
    match C.gates[w - n]? with
    | some g => g.inputs.toFinset.filter (fun q => q < w)
    | none => ∅
  else ∅

def Good (C : Circuit) : Prop :=
  ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2

theorem child_lt (C : Circuit) (n w q : ℕ) (hq : q ∈ children C n w) : q < w := by
  unfold children at hq
  split at hq
  · split at hq
    · exact (Finset.mem_filter.mp hq).2
    · simp at hq
  · simp at hq

theorem children_card (C : Circuit) (n w : ℕ) (hgood : Good C) :
    (children C n w).card ≤ 2 := by
  unfold children
  split
  · split
    next g heq =>
      obtain ⟨h, rfl⟩ := List.getElem?_eq_some_iff.mp heq
      have hlen := (hgood _ (List.getElem_mem h)).2
      exact (Finset.card_le_card (Finset.filter_subset _ _)).trans
        ((List.toFinset_card_le _).trans hlen)
    next => simp
  · simp

theorem val_children (C : Circuit) (n w : ℕ) (x y : Fin n → Bool) (hgood : Good C)
    (hw : n ≤ w)
    (hchildren : ∀ q ∈ children C n w, val C n x q = true → val C n y q = true) :
    val C n x w = true → val C n y w = true := by
  obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
  cases hg : C.gates[j]? with
  | none => simp [val_none C n x j hg]
  | some g =>
    have hmem : g ∈ C.gates := by
      obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.mp hg
      exact List.getElem_mem hj
    have hchildren' (q : ℕ) (hq : q ∈ g.inputs) (hqlt : q < n+j) :=
      hchildren q (by simp [children, hg, hq, hqlt])
    rcases (hgood g hmem).1 with hop | hop
    · rw [val_and C n x j g hg hop, val_and C n y j g hg hop]
      intro h q hq
      obtain ⟨hqlt, hv⟩ := h q hq
      exact ⟨hqlt, hchildren' q hq hqlt hv⟩
    · rw [val_or C n x j g hg hop, val_or C n y j g hg hop]
      rintro ⟨q, hq, hqlt, hv⟩
      exact ⟨q, hq, hqlt, hchildren' q hq hqlt hv⟩

theorem val_mono (C : Circuit) (n : ℕ) (x y : Fin n → Bool) (hgood : Good C)
    (hxy : ∀ q, x q = true → y q = true) (w : ℕ) :
    val C n x w = true → val C n y w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hw : w < n
    · simpa only [val_input C n x w hw, val_input C n y w hw] using hxy ⟨w, hw⟩
    · exact val_children C n w x y hgood (by omega) fun q hq => ih q (child_lt C n w q hq)

theorem val_oob (C : Circuit) (n : ℕ) (x : Fin n → Bool) (w : ℕ) (hw : n + C.size ≤ w) :
    val C n x w = false := by
  unfold val
  apply getD_of_length_le
  rw [wires_eq, foldl_step_length, List.length_ofFn]
  exact hw

end PEqualNP.Outside.L_meta_925_aux

namespace PEqualNP.Outside.L_meta_925_aux

private theorem expand_one (F C : Finset ℕ) (v : ℕ)
    (hc : C.card ≤ 2) (hp : ∀ w ∈ C, w < v) :
    ∃ F' : Finset ℕ, v ∉ F' ∧ F'.card ≤ F.card + 1 ∧
      (∀ w ∈ F', w ∈ F ∨ w ∈ C) ∧
      ∀ P : ℕ → Prop, ((∀ w ∈ C, P w) → P v) →
        (∀ w ∈ F', P w) → ∀ w ∈ F, P w := by
  by_cases hv : v ∈ F
  · refine ⟨F.erase v ∪ C, ?_, ?_, ?_, ?_⟩
    · have hvc : v ∉ C := fun h => (lt_irrefl v) (hp v h)
      simp [hvc]
    · have he := Finset.card_erase_add_one hv
      have hu := Finset.card_union_le (F.erase v) C
      omega
    · intro w hw
      rcases Finset.mem_union.mp hw with h | h
      · exact Or.inl (Finset.mem_of_mem_erase h)
      · exact Or.inr h
    · intro P hprop hbase w hw
      by_cases heq : w = v
      · subst w
        exact hprop fun z hz => hbase z (Finset.mem_union_right _ hz)
      · exact hbase _ (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨heq, hw⟩))
  · exact ⟨F, hv, by omega, fun _ h => Or.inl h, fun _ _ h => h⟩

private theorem exists_frontier_from (Q : Finset ℕ) (children : ℕ → Finset ℕ)
    (hsmall : ∀ j ∈ Q, (children j).card ≤ 2)
    (hprev : ∀ j ∈ Q, ∀ w ∈ children j, w < j)
    (F : Finset ℕ) (Good : ℕ → Prop) (hF : ∀ w ∈ F, Good w)
    (hchildren : ∀ j ∈ Q, ∀ w ∈ children j, Good w) :
    ∃ B : Finset ℕ, Disjoint B Q ∧ B.card ≤ Q.card + F.card ∧
      (∀ w ∈ B, Good w) ∧
      ∀ P : ℕ → Prop, (∀ j ∈ Q, (∀ w ∈ children j, P w) → P j) →
        (∀ w ∈ B, P w) → ∀ w ∈ F, P w := by
  induction Q using Finset.induction_on_max generalizing F Good with
  | empty => exact ⟨F, by simp, by simp, hF, fun _ _ h => h⟩
  | insert j Q hmax ih =>
    have hj : j ∉ Q := fun h => (lt_irrefl _) (hmax j h)
    have hj' : j ∈ insert j Q := Finset.mem_insert_self _ _
    have hsub : Q ⊆ insert j Q := Finset.subset_insert _ _
    obtain ⟨F', havoid, hcard, hsrc, hlocal⟩ :=
      expand_one F (children j) j (hsmall j hj') (hprev j hj')
    obtain ⟨B, hdis, hbcard, hgood, hforce⟩ := ih
      (fun q hq => hsmall q (hsub hq)) (fun q hq => hprev q (hsub hq))
      F' (fun w => Good w ∧ w ≠ j)
      (fun w hw => ⟨(hsrc w hw).elim (hF w) (hchildren j hj' w),
        fun he => havoid (he ▸ hw)⟩)
      (fun q hq w hw => ⟨hchildren q (hsub hq) w hw,
        (lt_trans (hprev q (hsub hq) w hw) (hmax q hq)).ne⟩)
    refine ⟨B, ?_, ?_, fun w hw => (hgood w hw).1, ?_⟩
    · refine Finset.disjoint_left.mpr fun w hw hw' => ?_
      rcases Finset.mem_insert.mp hw' with heq | hq
      · exact (hgood w hw).2 heq
      · exact Finset.disjoint_left.mp hdis hw hq
    · rw [Finset.card_insert_of_notMem hj]
      omega
    · intro P hstep hbase
      exact hlocal P (hstep j hj') (hforce P (fun q hq => hstep q (hsub hq)) hbase)

theorem exists_frontier (Q : Finset ℕ) (children : ℕ → Finset ℕ)
    (hsmall : ∀ j ∈ Q, (children j).card ≤ 2)
    (hprev : ∀ j ∈ Q, ∀ w ∈ children j, w < j) (r : ℕ) :
    ∃ B : Finset ℕ, Disjoint B Q ∧ B.card ≤ Q.card + 1 ∧
      ∀ P : ℕ → Prop, (∀ j ∈ Q, (∀ w ∈ children j, P w) → P j) →
        (∀ w ∈ B, P w) → P r := by
  obtain ⟨B, hd, hc, _, hf⟩ := exists_frontier_from Q children hsmall hprev {r}
    (fun _ => True) (by simp) (by simp)
  exact ⟨B, hd, by simpa using hc, fun P hstep hbase => hf P hstep hbase r (by simp)⟩

end PEqualNP.Outside.L_meta_925_aux

namespace PEqualNP.Outside.L_meta_925_aux

private lemma union_card_mul {α β : Type*} [DecidableEq α] (B : Finset β)
    (T : β → Finset α) (q : ℕ) (h : ∀ w ∈ B, (T w).card ≤ q) :
    (B.biUnion T).card ≤ q * B.card := calc
  _ ≤ ∑ w ∈ B, (T w).card := Finset.card_biUnion_le
  _ ≤ ∑ _w ∈ B, q := Finset.sum_le_sum h
  _ = _ := by simp [Nat.mul_comm]

lemma card_witness_inter {α β : Type*} [DecidableEq α]
    (B : Finset β) (T : β → Finset α) (A : Finset α)
    (hinter : ∀ w ∈ B, (T w ∩ A).card ≤ 1) :
    (B.biUnion T ∩ A).card ≤ B.card := by
  rw [Finset.biUnion_inter]
  simpa using union_card_mul B (fun w => T w ∩ A) 1 hinter

lemma card_witness_union {α β ι : Type*} [DecidableEq α]
    (B : Finset β) (T : β → Finset α) (S : ι → Finset α) (q : ℕ)
    (hq : 2 ≤ q) (hsize : ∀ i, (S i).card = q + 1)
    (hmeet : ∀ i j, i ≠ j → (S i ∩ S j).card = 1)
    (hshape : ∀ w ∈ B, (T w).card ≤ 1 ∨ ∃ j, T w = S j) :
    (B.biUnion T).card ≤ q * B.card + 1 := by
  classical
  by_cases hline : ∃ w ∈ B, ∃ i, T w = S i
  · obtain ⟨w, hw, i, hi⟩ := hline
    let outside (v : β) := T v \ S i
    have hout : ∀ v ∈ B.erase w, (outside v).card ≤ q := by
      intro v hv
      have hvB := Finset.mem_of_mem_erase hv
      rcases hshape v hvB with hs | ⟨j, hj⟩
      · exact le_trans (Finset.card_le_card Finset.sdiff_subset) (by omega)
      · change (T v \ S i).card ≤ q
        rw [hj]
        by_cases he : j = i
        · simp [he]
        · have hsplit := Finset.card_sdiff_add_card_inter (S j) (S i)
          rw [hsize, hmeet j i he] at hsplit
          omega
    have hsub : B.biUnion T ⊆ S i ∪ (B.erase w).biUnion outside := by
      intro x hx
      obtain ⟨v, hv, hxv⟩ := Finset.mem_biUnion.mp hx
      by_cases hxi : x ∈ S i
      · exact Finset.mem_union_left _ hxi
      · have hvw : v ≠ w := by
          rintro rfl
          exact hxi (hi ▸ hxv)
        exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
          ⟨v, Finset.mem_erase.mpr ⟨hvw, hv⟩, Finset.mem_sdiff.mpr ⟨hxv, hxi⟩⟩)
    have heq : q * B.card = q * (B.erase w).card + q := by
      rw [← Finset.card_erase_add_one hw, Nat.mul_add, Nat.mul_one]
    calc
      _ ≤ (S i ∪ (B.erase w).biUnion outside).card := Finset.card_le_card hsub
      _ ≤ (S i).card + ((B.erase w).biUnion outside).card := Finset.card_union_le _ _
      _ ≤ q * B.card + 1 := by
        have hu := union_card_mul (B.erase w) outside q hout
        rw [hsize, heq]
        omega
  · apply le_trans (union_card_mul B T q ?_) (by omega)
    intro w hw
    rcases hshape w hw with hs | h
    · omega
    · exact (hline ⟨w, hw, h⟩).elim

end PEqualNP.Outside.L_meta_925_aux

namespace PEqualNP.Outside.L_meta_925_aux

theorem boundary_witness {n m : ℕ} (C : PEqualNP.CircuitLowerBounds.Circuit)
    (S : Fin m → Finset (Fin n)) (i : Fin m) (w : ℕ)
    (hmeet : ∀ j, j ≠ i → (S j ∩ S i).card ≤ 1)
    (hnonprivate : ¬ (n ≤ w ∧ w < n + C.size ∧
      val C n (fun p => decide (p ∈ S i)) w = true ∧
      ∀ j, j ≠ i → val C n (fun p => decide (p ∈ S j)) w = false)) :
    ∃ T : Finset (Fin n), (T.card ≤ 1 ∨ ∃ j, j ≠ i ∧ T = S j) ∧
      (T ∩ S i).card ≤ 1 ∧ (val C n (fun p => decide (p ∈ S i)) w = true →
        val C n (fun p => decide (p ∈ T)) w = true) := by
  classical
  by_cases hinput : w < n
  · let p : Fin n := ⟨w, hinput⟩
    refine ⟨{p}, Or.inl (by simp), ?_, fun _ => ?_⟩
    · exact (Finset.card_le_card Finset.inter_subset_left).trans (by simp)
    · simp [val_input C n _ w hinput, p]
  by_cases htrue : val C n (fun p => decide (p ∈ S i)) w = true
  · have hvalid : w < n + C.size := by
      by_contra! he
      simp [val_oob C n _ w he] at htrue
    have hex : ∃ j, j ≠ i ∧ val C n (fun p => decide (p ∈ S j)) w = true := by
      by_contra! hn
      exact hnonprivate ⟨Nat.le_of_not_gt hinput, hvalid, htrue, fun j hj => by
        simpa using hn j hj⟩
    obtain ⟨j, hji, hj⟩ := hex
    exact ⟨S j, Or.inr ⟨j, hji, rfl⟩, hmeet j hji, fun _ => hj⟩
  · exact ⟨∅, Or.inl (by simp), by simp, fun hv => False.elim (htrue hv)⟩

end PEqualNP.Outside.L_meta_925_aux

open PEqualNP.Outside.L_meta_925_aux

theorem PEqualNP.Outside.L_meta_925 : ∀ (q n m K : ℕ) (S : Fin m → Finset (Fin n)), 2 ≤ q → (∀ i : Fin m, (S i).card = q + 1) → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card = 1) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (w : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun i : Fin n => x i = true)).card ≤ K → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∀ v ∈ S w, x v = true)) → ∀ c : ℕ, c ≤ q → c * q < K → m * c ≤ gates.length := by
  classical
  intro q n m K S hq hsize hmeet gates out hgood hpromise c hc hcK
  by_cases hc0 : c = 0
  · simp [hc0]
  have hqK : q < K := by
    have hle := Nat.mul_le_mul_right q (show 1 ≤ c by omega)
    simpa using (lt_of_le_of_lt hle hcK)
  let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨gates, 0⟩
  let bits (X : Finset (Fin n)) := fun a : Fin n => decide (a ∈ X)
  let G := Finset.Ico n (n + C.size)
  let Q (i : Fin m) := G.filter (fun w => val C n (bits (S i)) w = true ∧
    ∀ j, j ≠ i → val C n (bits (S j)) w = false)
  have sub (i : Fin m) : Q i ⊆ G := Finset.filter_subset _ _
  have promise (i : Fin m) (X : Finset (Fin n)) (hX : X.card ≤ K) :
      val C n (bits X) (out i) = decide (∀ v ∈ S i, bits X v = true) := by
    apply hpromise
    simpa [bits] using hX
  have row (i : Fin m) : c ≤ (Q i).card := by
    by_contra! hlt
    obtain ⟨B, hd, hB, prop⟩ := exists_frontier (Q i) (children C n)
      (fun w _ => children_card C n w hgood) (fun w _ u hu => child_lt C n w u hu) (out i)
    have getT (w : ℕ) : ∃ T : Finset (Fin n), w ∈ B →
        (T.card ≤ 1 ∨ ∃ j, j ≠ i ∧ T = S j) ∧ (T ∩ S i).card ≤ 1 ∧
        (val C n (bits (S i)) w = true → val C n (bits T) w = true) := by
      by_cases hw : w ∈ B
      · obtain ⟨T, hT⟩ := boundary_witness C S i w (fun j hj => (hmeet j i hj).le)
          (fun ⟨hlo, hhi, ht, ho⟩ => Finset.disjoint_left.mp hd hw
            (Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hlo, hhi⟩, ht, ho⟩))
        exact ⟨T, fun _ => hT⟩
      · exact ⟨∅, fun h => (hw h).elim⟩
    choose T hT using getT
    let U := B.biUnion T
    have hU : U.card ≤ K := by
      have h1 := card_witness_union B T S q hq hsize hmeet (by
        intro w hw
        exact ((hT w hw).1).imp_right (fun ⟨j, _, hj⟩ => ⟨j, hj⟩))
      have h2 := Nat.mul_le_mul_left q (show B.card ≤ c by omega)
      dsimp [U]
      rw [Nat.mul_comm c q] at hcK
      omega
    have hI : (U ∩ S i).card ≤ B.card :=
      card_witness_inter B T (S i) (fun w hw => (hT w hw).2.1)
    have hroot : val C n (bits (S i)) (out i) = true := by
      rw [promise i (S i) (by rw [hsize]; omega)]
      simp [bits]
    have hup := prop (fun w => val C n (bits (S i)) w = true → val C n (bits U) w = true)
      (fun w hw => val_children C n w _ _ hgood (Finset.mem_Ico.mp (sub i hw)).1)
      (by
        intro w hw hv
        apply val_mono C n (bits (T w)) (bits U) hgood ?_ w ((hT w hw).2.2 hv)
        intro a ha
        exact decide_eq_true (Finset.mem_biUnion.mpr ⟨w, hw, of_decide_eq_true ha⟩)) hroot
    rw [promise i U hU] at hup
    have hsub : S i ⊆ U := fun a ha => of_decide_eq_true ((of_decide_eq_true hup) a ha)
    rw [Finset.inter_eq_right.mpr hsub, hsize] at hI
    omega
  have hd : (↑(Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint Q := by
    intro i hi j hj hij
    apply Finset.disjoint_left.mpr
    intro w hwi hwj
    have hfalse := (Finset.mem_filter.mp hwi).2.2 j (Ne.symm hij)
    have htrue := (Finset.mem_filter.mp hwj).2.1
    simp_all
  calc
    m * c = ∑ _i : Fin m, c := by simp
    _ ≤ ∑ i, (Q i).card := Finset.sum_le_sum (fun i _ => row i)
    _ = (Finset.univ.biUnion Q).card := (Finset.card_biUnion hd).symm
    _ ≤ G.card := Finset.card_le_card (by
      intro w hw
      obtain ⟨i, _, hwi⟩ := Finset.mem_biUnion.mp hw
      exact sub i hwi)
    _ = gates.length := by simp [G, C, PEqualNP.CircuitLowerBounds.Circuit.size]
