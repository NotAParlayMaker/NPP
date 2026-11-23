import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_925_aux

open PEqualNP.CircuitLowerBounds

-- Prefix evaluation lemmas are from the checked project proof of L-meta-275.
lemma fold_len (gs : List Gate) : ∀ w : List Bool,
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).length
      = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp
  | cons g gs ih =>
    intro w
    rw [List.foldl_cons, ih]
    simp
    omega

lemma fold_prefix (gs : List Gate) : ∀ w : List Bool,
    w <+: gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w := by
  induction gs with
  | nil => intro w; simp
  | cons g gs ih =>
    intro w
    rw [List.foldl_cons]
    exact (List.prefix_append w _).trans (ih _)

lemma getD_prefix {w l : List Bool} (h : w <+: l) {i : ℕ} (hi : i < w.length) :
    l.getD i false = w.getD i false := by
  obtain ⟨r, rfl⟩ := h
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma wires_len (C : Circuit) (x : List Bool) : (C.wires x).length = x.length + C.gates.length :=
  fold_len C.gates x

lemma wires_gate (C : Circuit) (x : List Bool) (j : ℕ) (hj : j < C.gates.length) :
    (C.wires x).getD (x.length + j) false = (C.gates[j]).op.eval
      ((C.gates[j]).inputs.map fun i =>
        if i < x.length + j then (C.wires x).getD i false else false) := by
  have hsplit : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j + 1) := by
    rw [← List.drop_eq_getElem_cons hj, List.take_append_drop]
  have hpl : ((C.gates.take j).foldl
      (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x).length
      = x.length + j := by
    rw [fold_len, List.length_take, min_eq_left hj.le]
  have hfull : C.wires x = (C.gates.drop (j + 1)).foldl
      (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (((C.gates.take j).foldl
      (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x) ++
      [(C.gates[j]).op.eval ((C.gates[j]).inputs.map fun i => ((C.gates.take j).foldl
      (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x).getD i false)]) := by
    conv_lhs => rw [Circuit.wires, hsplit, List.foldl_append, List.foldl_cons]
  have hp1 := fold_prefix (C.gates.drop (j + 1)) (((C.gates.take j).foldl
      (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x) ++
      [(C.gates[j]).op.eval ((C.gates[j]).inputs.map fun i => ((C.gates.take j).foldl
      (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x).getD i false)])
  rw [← hfull] at hp1
  have hp0 := (List.prefix_append _ _).trans hp1
  rw [getD_prefix hp1 (by rw [List.length_append, hpl]; simp)]
  rw [← hpl, List.getD_append_right _ _ _ _ le_rfl]
  simp only [Nat.sub_self, List.getD_cons_zero]
  congr 1
  apply List.map_congr_left
  intro i _
  by_cases hi : i < x.length + j
  · rw [hpl, ite_eq_left_of_eq_true _ _ (eq_true hi)]
    exact (getD_prefix hp0 (by rw [hpl]; exact hi)).symm
  · rw [hpl, ite_eq_right_of_eq_false _ _ (eq_false hi)]
    exact List.getD_eq_default _ _ (by rw [hpl]; omega)

lemma wires_input (C : Circuit) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (C.wires x).getD i false = x.getD i false :=
  getD_prefix (fold_prefix C.gates x) hi

def val {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) : Bool :=
  ((Circuit.mk gs 0).wires (List.ofFn x)).getD i false

theorem val_input {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : Fin n) :
    val gs x i = x i := by
  rw [val, wires_input _ _ _ (by simp)]
  simp [List.getD_eq_getElem?_getD]

theorem val_outside {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ)
    (hi : n + gs.length ≤ i) : val gs x i = false := by
  exact List.getD_eq_default _ _ (by rw [wires_len]; simpa using hi)

theorem val_children {n : ℕ} (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    {x : Fin n → Bool} {w : ℕ} (hw : n ≤ w) (hon : val gs x w = true) :
    ∃ U : Finset ℕ, U ⊆ Finset.range w ∧ U.card ≤ 2 ∧
      (∀ u ∈ U, val gs x u = true) ∧
      ∀ y : Fin n → Bool, (∀ u ∈ U, val gs y u = true) → val gs y w = true := by
  by_cases hbound : n + gs.length ≤ w
  · rw [val_outside gs x w hbound] at hon
    contradiction
  have hj : w - n < gs.length := by omega
  let g : Gate := gs[w - n]
  have hgmem : g ∈ gs := List.getElem_mem hj
  obtain ⟨hop, hlen⟩ := hg g hgmem
  let readAt := fun (y : Fin n → Bool) (i : ℕ) => if i < w then val gs y i else false
  have heval (y : Fin n → Bool) :
      val gs y w = g.op.eval (g.inputs.map (readAt y)) := by
    have h := wires_gate (Circuit.mk gs 0) (List.ofFn y) (w - n) hj
    have he : n + (w - n) = w := by omega
    simpa only [val, List.length_ofFn, he, g, readAt] using h
  rw [heval] at hon
  rcases hop with hAnd | hOr
  · have hx : ∀ i ∈ g.inputs, readAt x i = true := by
      simpa [hAnd, GateOp.eval] using hon
    have hsmall (i) (hi : i ∈ g.inputs) : i < w := by
      by_contra hn
      simpa [readAt, hn] using hx i hi
    refine ⟨g.inputs.toFinset, ?_, ?_, ?_, ?_⟩
    · intro i hi
      exact Finset.mem_range.mpr (hsmall i (List.mem_toFinset.mp hi))
    · exact g.inputs.toFinset_card_le.trans hlen
    · intro i hi
      have hi' := List.mem_toFinset.mp hi
      simpa [readAt, hsmall i hi'] using hx i hi'
    · intro y hy
      rw [heval, hAnd]
      suffices ∀ i ∈ g.inputs, readAt y i = true by simpa [GateOp.eval] using this
      intro i hi
      simpa [readAt, hsmall i hi] using hy i (List.mem_toFinset.mpr hi)
  · have hx : ∃ i ∈ g.inputs, readAt x i = true := by
      simpa [hOr, GateOp.eval] using hon
    obtain ⟨i, hi, hix⟩ := hx
    have hsmall : i < w := by
      by_contra hn
      simp [readAt, hn] at hix
    refine ⟨{i}, by simpa using hsmall, by simp, ?_, ?_⟩
    · simpa [readAt, hsmall] using hix
    · intro y hy
      rw [heval, hOr]
      suffices ∃ i ∈ g.inputs, readAt y i = true by simpa [GateOp.eval] using this
      exact ⟨i, hi, by simpa [readAt, hsmall] using hy i (by simp)⟩

theorem val_mono {n : ℕ} (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    {x y : Fin n → Bool} (hxy : ∀ i, x i = true → y i = true) (w : ℕ) :
    val gs x w = true → val gs y w = true := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hon
    by_cases hw : w < n
    · have h := hxy ⟨w, hw⟩ ((val_input gs x ⟨w, hw⟩).symm.trans hon)
      exact (val_input gs y ⟨w, hw⟩).trans h
    · obtain ⟨U, hU, _, hUx, hforce⟩ := val_children gs hg (Nat.le_of_not_gt hw) hon
      exact hforce y fun u hu => ih u (Finset.mem_range.mp (hU hu)) (hUx u hu)

-- Sweep the internal wires from last to first. Replacing a wire by its predecessors
-- can increase the frontier by one, and each internal wire is visited at most once.
private lemma frontier_sweep {α : Type*} (A : Finset ℕ) (Good : ℕ → Prop)
    (V : ℕ → α → Prop)
    (hstep : ∀ j ∈ A, Good j → ∃ D : Finset ℕ, D.card ≤ 2 ∧
      (∀ t ∈ D, t < j ∧ Good t) ∧ ∀ x : α, (∀ t ∈ D, V t x) → V j x)
    (k : ℕ) (F : Finset ℕ) (hg : ∀ j ∈ F, Good j)
    (hb : ∀ j ∈ F, j ∈ A → j < k) :
    ∃ R : Finset ℕ, R.card ≤ F.card + (A.filter (fun i => i < k)).card ∧
      (∀ t ∈ R, Good t ∧ t ∉ A) ∧
      ∀ x : α, (∀ t ∈ R, V t x) → ∀ j ∈ F, V j x := by
  classical
  induction k generalizing F with
  | zero =>
    refine ⟨F, by simp, ?_, fun _ h => h⟩
    exact fun j hj => ⟨hg j hj, fun hjA => by have := hb j hj hjA; omega⟩
  | succ k ih =>
    have hinc : A.filter (fun i => i < k) ⊆ A.filter (fun i => i < k + 1) := by
      intro i hi
      obtain ⟨hiA, hik⟩ := Finset.mem_filter.mp hi
      exact Finset.mem_filter.mpr ⟨hiA, by omega⟩
    by_cases hk : k ∈ F ∧ k ∈ A
    · obtain ⟨D, hDcard, hD, hforce⟩ := hstep k hk.2 (hg k hk.1)
      let F' := F.erase k ∪ D
      have hg' : ∀ j ∈ F', Good j := by
        intro j hj
        rcases Finset.mem_union.mp hj with hj | hj
        · exact hg j (Finset.mem_of_mem_erase hj)
        · exact (hD j hj).2
      have hb' : ∀ j ∈ F', j ∈ A → j < k := by
        intro j hj hjA
        rcases Finset.mem_union.mp hj with hj | hj
        · obtain ⟨hne, hjF⟩ := Finset.mem_erase.mp hj
          have := hb j hjF hjA
          omega
        · exact (hD j hj).1
      obtain ⟨R, hcard, hterm, hR⟩ := ih F' hg' hb'
      refine ⟨R, ?_, hterm, ?_⟩
      · have hF' : F'.card ≤ (F.erase k).card + D.card := Finset.card_union_le _ _
        have hF := Finset.card_erase_add_one hk.1
        have hknot : k ∉ A.filter (fun i => i < k) := by simp
        have hsub : insert k (A.filter (fun i => i < k)) ⊆ A.filter (fun i => i < k + 1) :=
          Finset.insert_subset (Finset.mem_filter.mpr ⟨hk.2, by omega⟩) hinc
        have hcount := Finset.card_le_card hsub
        rw [Finset.card_insert_of_notMem hknot] at hcount
        omega
      · intro x hx j hj
        have hh := hR x hx
        by_cases hjk : j = k
        · subst j
          exact hforce x (fun t ht => hh t (Finset.mem_union_right _ ht))
        · exact hh j (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hjk, hj⟩))
    · have hb' : ∀ j ∈ F, j ∈ A → j < k := by
        intro j hj hjA
        have hne : j ≠ k := by rintro rfl; exact hk ⟨hj, hjA⟩
        have := hb j hj hjA
        omega
      obtain ⟨R, hcard, hterm, hR⟩ := ih F hg hb'
      exact ⟨R, hcard.trans (Nat.add_le_add_left (Finset.card_le_card hinc) _), hterm, hR⟩

lemma frontier {α : Type*} (A : Finset ℕ) (Good : ℕ → Prop) (V : ℕ → α → Prop)
    (hstep : ∀ j ∈ A, Good j → ∃ D : Finset ℕ, D.card ≤ 2 ∧
      (∀ t ∈ D, t < j ∧ Good t) ∧ ∀ x : α, (∀ t ∈ D, V t x) → V j x)
    (j : ℕ) (hj : Good j) :
    ∃ R : Finset ℕ, R.card ≤ A.card + 1 ∧ (∀ t ∈ R, Good t ∧ t ∉ A) ∧
      ∀ x : α, (∀ t ∈ R, V t x) → V j x := by
  classical
  obtain ⟨R, hcard, hterm, hR⟩ :=
    frontier_sweep A Good V hstep (j + 1) {j} (by simpa using hj) (by simp)
  have := Finset.card_le_card (Finset.filter_subset (fun i => i < j + 1) A)
  simp only [Finset.card_singleton] at hcard
  exact ⟨R, by omega, hterm, fun x hx => hR x hx j (Finset.mem_singleton_self _)⟩

private lemma uniform_union_bound {α β : Type*} [DecidableEq β]
    (T : Finset α) (B : α → Finset β) (r : ℕ)
    (h : ∀ t ∈ T, (B t).card ≤ r) :
    (T.biUnion B).card ≤ r * T.card := by
  calc
    _ ≤ ∑ t ∈ T, (B t).card := Finset.card_biUnion_le
    _ ≤ ∑ _t ∈ T, r := Finset.sum_le_sum h
    _ = _ := by simp [Nat.mul_comm]

lemma witness_bounds {α : Type*} [DecidableEq α] {q n m : ℕ}
    (S : Fin m → Finset (Fin n)) (w : Fin m) (hq : 2 ≤ q)
    (hsize : ∀ j, (S j).card = q + 1)
    (hinter : ∀ i j, i ≠ j → (S i ∩ S j).card = 1)
    (T : Finset α) (B : α → Finset (Fin n))
    (hB : ∀ t ∈ T, (B t).card ≤ 1 ∨ ∃ j, j ≠ w ∧ B t = S j) :
    (T.biUnion B).card ≤ q * T.card + 1 ∧
      ((T.biUnion B) ∩ S w).card ≤ T.card := by
  constructor
  · by_cases hlarge : ∃ a ∈ T, ∃ j, B a = S j
    · obtain ⟨a, ha, j, hj⟩ := hlarge
      let R := (T.erase a).biUnion (fun t => B t \ S j)
      have hR : R.card ≤ q * (T.erase a).card := by
        apply uniform_union_bound
        intro t ht
        rcases hB t (Finset.mem_erase.mp ht).2 with hsmall | ⟨k, _, hk⟩
        · exact (Finset.card_le_card Finset.sdiff_subset).trans (by omega)
        · rw [hk]
          by_cases hkj : k = j
          · simp [hkj]
          · have h := Finset.card_sdiff_add_card_inter (S k) (S j)
            rw [hinter k j hkj, hsize k] at h
            omega
      have hcover : T.biUnion B ⊆ S j ∪ R := by
        intro z hz
        obtain ⟨t, ht, hzt⟩ := Finset.mem_biUnion.mp hz
        by_cases hzj : z ∈ S j
        · exact Finset.mem_union_left _ hzj
        · have hta : t ≠ a := by
            rintro rfl
            exact hzj (hj ▸ hzt)
          exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
            ⟨t, Finset.mem_erase.mpr ⟨hta, ht⟩, Finset.mem_sdiff.mpr ⟨hzt, hzj⟩⟩)
      have hsum := (Finset.card_le_card hcover).trans (Finset.card_union_le (S j) R)
      have hcard := Finset.card_erase_add_one ha
      calc
        _ ≤ (S j).card + R.card := hsum
        _ ≤ (q + 1) + q * (T.erase a).card := by rw [hsize j]; omega
        _ = q * T.card + 1 := by rw [← hcard, Nat.mul_add, Nat.mul_one]; omega
    · have hsmall : ∀ t ∈ T, (B t).card ≤ q := by
        intro t ht
        rcases hB t ht with hs | ⟨j, _, hj⟩
        · omega
        · exact (hlarge ⟨t, ht, j, hj⟩).elim
      exact (uniform_union_bound T B q hsmall).trans (by omega)
  · rw [Finset.biUnion_inter]
    have hs : ∀ t ∈ T, (B t ∩ S w).card ≤ 1 := by
      intro t ht
      rcases hB t ht with hsmall | ⟨j, hjw, hj⟩
      · exact (Finset.card_le_card Finset.inter_subset_left).trans hsmall
      · rw [hj, hinter j w hjw]
    simpa using uniform_union_bound T (fun t => B t ∩ S w) 1 hs

lemma setLower {n m q K c : ℕ} (S : Fin m → Finset (Fin n))
    (hq : 2 ≤ q) (hcard : ∀ i, (S i).card = q + 1)
    (hinter : ∀ i j, i ≠ j → (S i ∩ S j).card = 1)
    (hc : c ≤ q) (hK : c * q < K) (U : Finset ℕ)
    (V : ℕ → Finset (Fin n) → Prop) (out : Fin m → ℕ)
    (hm : ∀ t X Y, X ⊆ Y → V t X → V t Y)
    (hp : ∀ t X, t ∉ U → V t X → ∃ B : Finset (Fin n), B.card ≤ 1 ∧ V t B)
    (hg : ∀ t ∈ U, ∀ X, V t X → ∃ D : Finset ℕ, D.card ≤ 2 ∧
      (∀ u ∈ D, u < t ∧ V u X) ∧ ∀ Y, (∀ u ∈ D, V u Y) → V t Y)
    (he : ∀ i X, X.card ≤ K → (V (out i) X ↔ S i ⊆ X)) : m * c ≤ U.card := by
  classical
  by_cases hzero : c = 0
  · simp [hzero]
  have hqK : q + 1 ≤ K := by
    have hle := Nat.mul_le_mul_right q (show 1 ≤ c by omega)
    simp only [Nat.one_mul] at hle
    omega
  let A (i : Fin m) := U.filter (fun t => V t (S i) ∧ ∀ j, j ≠ i → ¬ V t (S j))
  have hi (i : Fin m) : c ≤ (A i).card := by
    by_contra hsmall
    have hroot : V (out i) (S i) := (he i (S i) (by simpa [hcard] using hqK)).mpr (by rfl)
    obtain ⟨R, hr, hR, hforce⟩ := frontier (A i) (fun t => V t (S i)) V
      (fun t ht h => hg t (Finset.mem_filter.mp ht).1 (S i) h) (out i) hroot
    have hRcard : R.card ≤ c := by omega
    have hterminal (t : ℕ) (ht : t ∈ R) : ∃ B : Finset (Fin n),
        (B.card ≤ 1 ∨ ∃ j : Fin m, j ≠ i ∧ B = S j) ∧ V t B := by
      obtain ⟨htrue, hfree⟩ := hR t ht
      by_cases hu : t ∈ U
      · have other : ∃ j, j ≠ i ∧ V t (S j) := by
          by_contra! h
          exact hfree (Finset.mem_filter.mpr ⟨hu, htrue, h⟩)
        obtain ⟨j, hj, hjv⟩ := other
        exact ⟨S j, Or.inr ⟨j, hj, rfl⟩, hjv⟩
      · obtain ⟨B, hB, hv⟩ := hp t (S i) hu htrue
        exact ⟨B, Or.inl hB, hv⟩
    let B (t : ℕ) : Finset (Fin n) := if h : t ∈ R then (hterminal t h).choose else ∅
    have hB (t : ℕ) (ht : t ∈ R) :
        ((B t).card ≤ 1 ∨ ∃ j : Fin m, j ≠ i ∧ B t = S j) ∧ V t (B t) := by
      simpa only [B, dite_eq_left ht] using (hterminal t ht).choose_spec
    obtain ⟨hsize, hhit⟩ := witness_bounds S i hq hcard hinter R B (fun t ht => (hB t ht).1)
    have hlight : (R.biUnion B).card ≤ K := by
      have hmul := Nat.mul_le_mul_left q hRcard
      rw [Nat.mul_comm c q] at hK
      omega
    have hall : S i ⊆ R.biUnion B := (he i _ hlight).mp (hforce _ (fun t ht =>
      hm t _ _ (fun a ha => Finset.mem_biUnion.mpr ⟨t, ht, ha⟩) (hB t ht).2))
    rw [Finset.inter_eq_right.mpr hall, hcard] at hhit
    omega
  have hdisj : ∀ i ∈ (Finset.univ : Finset (Fin m)), ∀ j ∈ (Finset.univ : Finset (Fin m)),
      i ≠ j → Disjoint (A i) (A j) := by
    intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro t hti htj
    exact (Finset.mem_filter.mp hti).2.2 j hij.symm (Finset.mem_filter.mp htj).2.1
  calc m * c = ∑ _i : Fin m, c := by simp
       _ ≤ ∑ i : Fin m, (A i).card := Finset.sum_le_sum (fun i _ => hi i)
       _ = (Finset.univ.biUnion A).card := (Finset.card_biUnion hdisj).symm
       _ ≤ U.card := by
         apply Finset.card_le_card
         intro t ht
         obtain ⟨i, _, hi'⟩ := Finset.mem_biUnion.mp ht
         exact (Finset.mem_filter.mp hi').1

end PEqualNP.Outside.L_meta_925_aux

open PEqualNP.Outside.L_meta_925_aux

theorem PEqualNP.Outside.L_meta_925 : ∀ (q n m K : ℕ) (S : Fin m → Finset (Fin n)),
    2 ≤ q →
    (∀ i : Fin m, (S i).card = q + 1) →
    (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card = 1) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) →
    (∀ (w : Fin m) (x : Fin n → Bool),
    (Finset.univ.filter (fun i : Fin n => x i = true)).card ≤ K →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∀ v ∈ S w, x v = true)) →
    ∀ c : ℕ, c ≤ q → c * q < K → m * c ≤ gates.length := by
  intro q n m K S hq hcard hinter gates out hgate heval c hc hK
  classical
  let U := Finset.Ico n (n + gates.length)
  let ind (X : Finset (Fin n)) : Fin n → Bool := fun i => decide (i ∈ X)
  let V (t : ℕ) (X : Finset (Fin n)) := val gates (ind X) t = true
  calc m * c ≤ U.card := by
         apply setLower S hq hcard hinter hc hK U V out
         · intro t X Y hXY
           apply val_mono gates hgate _ t
           intro i hi
           simpa only [ind, decide_eq_true_eq] using hXY (of_decide_eq_true hi)
         · intro t X ht htrue
           by_cases htin : t < n
           · let i : Fin n := ⟨t, htin⟩
             refine ⟨{i}, by simp, ?_⟩
             change val gates (ind {i}) i = true
             rw [val_input]
             simp [ind]
           · have hout : n + gates.length ≤ t := by
               by_contra! h
               exact ht (Finset.mem_Ico.mpr ⟨by omega, h⟩)
             change val gates (ind X) t = true at htrue
             rw [val_outside gates (ind X) t hout] at htrue
             contradiction
         · intro t ht X htrue
           obtain ⟨D, hd, hcardD, hX, hforce⟩ := val_children gates hgate
             (Finset.mem_Ico.mp ht).1 htrue
           exact ⟨D, hcardD, fun u hu => ⟨Finset.mem_range.mp (hd hu), hX u hu⟩,
             fun Y hY => hforce (ind Y) hY⟩
         · intro i X hlight
           have hsupport : Finset.univ.filter (fun j : Fin n => ind X j = true) = X := by
             ext j
             simp [ind]
           have he := heval i (ind X) (by simpa only [hsupport] using hlight)
           change val gates (ind X) (out i) = _ at he
           change val gates (ind X) (out i) = true ↔ _
           rw [he]
           simp only [ind, decide_eq_true_eq]
           rfl
       _ = gates.length := by simp [U]
