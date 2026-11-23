import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_782_aux

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

def support (C : Circuit) (n w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun p => val C n (fun q : Fin n => decide (q = p)) w = true

def children (C : Circuit) (n w : ℕ) : Finset ℕ :=
  if n ≤ w then
    match C.gates[w - n]? with
    | some g => g.inputs.toFinset.filter (fun q => q < w)
    | none => ∅
  else ∅

def Good (C : Circuit) : Prop :=
  ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2

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
        ((List.toFinset_card_le _).trans hlen.le)
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

theorem support_gate (C : Circuit) (n w : ℕ) (hs : 2 ≤ (support C n w).card) :
    n ≤ w ∧ w < n + C.size := by
  have hw : n ≤ w := by
    by_contra! hw
    let i : Fin n := ⟨w, hw⟩
    have hsub : support C n w ⊆ {i} := by
      intro p hp
      obtain ⟨_, h⟩ := Finset.mem_filter.mp hp
      simp only [val_input C n _ w hw, decide_eq_true_eq] at h
      exact Finset.mem_singleton.mpr h.symm
    have := Finset.card_le_card hsub
    simp only [Finset.card_singleton] at this
    omega
  refine ⟨hw, ?_⟩
  by_contra! hlen
  obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
  have hgate : C.gates[j]? = none := List.getElem?_eq_none (by
    change n + C.gates.length ≤ n + j at hlen
    omega)
  have hempty : support C n (n+j) = ∅ := by
    ext q
    simp [support, val_none C n _ j hgate]
  simp [hempty] at hs

end PEqualNP.Outside.L_meta_782_aux

namespace PEqualNP.Outside.L_meta_782_aux

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


lemma select_witnesses {α : Type*} (A : ℕ → Finset α) (R S : Finset α)
    (B : Finset ℕ) (hcard : B.card < R.card)
    (hsmall : ∀ w ∈ B, A w ⊆ S → (A w).card ≤ 1) :
    ∃ Y : Finset α, Disjoint Y S ∧ Y.card ≤ B.card ∧
      ∃ p ∈ R, ∀ w ∈ B, p ∈ A w → ∃ q ∈ Y, q ∈ A w := by
  classical
  let small := B.filter (fun w => A w ⊆ S)
  have hcovered : (small.biUnion A).card ≤ B.card := calc
    (small.biUnion A).card ≤ ∑ w ∈ small, (A w).card := Finset.card_biUnion_le
    _ ≤ ∑ _w ∈ small, 1 := Finset.sum_le_sum fun w hw => by
      obtain ⟨hwB, hwS⟩ := Finset.mem_filter.mp hw
      exact hsmall w hwB hwS
    _ = small.card := by simp
    _ ≤ B.card := Finset.card_le_card (Finset.filter_subset _ _)
  obtain ⟨p, hp, havoid⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (lt_of_le_of_lt hcovered hcard)
  let large := B.filter (fun w => ¬ A w ⊆ S)
  have hout (w : ↥large) : ∃ q ∈ A w.val, q ∉ S := by
    have hnot := (Finset.mem_filter.mp w.prop).2
    exact Set.not_subset.mp hnot
  let pick (w : ↥large) := Classical.choose (hout w)
  have hpick (w : ↥large) : pick w ∈ A w.val ∧ pick w ∉ S :=
    Classical.choose_spec (hout w)
  refine ⟨large.attach.image pick, Finset.disjoint_left.mpr ?_, ?_, p, hp, ?_⟩
  · intro q hq
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hq
    exact (hpick w).2
  · calc
      (large.attach.image pick).card ≤ large.attach.card := Finset.card_image_le
      _ = large.card := Finset.card_attach
      _ ≤ B.card := Finset.card_le_card (Finset.filter_subset _ _)
  · intro w hw hwp
    have hwlarge : w ∈ large := Finset.mem_filter.mpr ⟨hw, fun hsub =>
      havoid (Finset.mem_biUnion.mpr ⟨w, Finset.mem_filter.mpr ⟨hw, hsub⟩, hwp⟩)⟩
    exact ⟨pick ⟨w, hwlarge⟩,
      Finset.mem_image.mpr ⟨⟨w, hwlarge⟩, Finset.mem_attach _ _, rfl⟩,
      (hpick ⟨w, hwlarge⟩).1⟩


private theorem count_private {n m k : ℕ}
    (S : Fin m → Finset (Fin n)) (o c : Fin m → ℕ) (G : Finset ℕ)
    (A : ℕ → Finset (Fin n)) (v : (Fin n → Bool) → ℕ → Bool)
    (child : ℕ → Finset ℕ)
    (hchild : ∀ w ∈ G, (child w).card ≤ 2)
    (hprev : ∀ w ∈ G, ∀ u ∈ child w, u < w)
    (hgate : ∀ w, 2 ≤ (A w).card → w ∈ G)
    (hsing : ∀ w p, p ∈ A w ↔ v (fun q => decide (q = p)) w = true)
    (hmono : ∀ x y : Fin n → Bool, (∀ p, x p = true → y p = true) →
      ∀ w, v x w = true → v y w = true)
    (hstep : ∀ w ∈ G, ∀ x y : Fin n → Bool,
      (∀ u ∈ child w, v x u = true → v y u = true) → v x w = true → v y w = true)
    (hpair : ∀ i j, i ≠ j → ((S i) ∩ (S j)).card ≤ 1)
    (hpromise : ∀ i x, (Finset.univ.filter (fun q => x q = true)).card ≤ k →
      (∀ p ∈ S i, x p = false) → v x (o i) = false)
    (hck : ∀ i, c i ≤ k) (hcount : ∀ i, c i + 1 ≤ (A (o i)).card) :
    ∑ i, c i ≤ G.card := by
  classical
  let Q (i : Fin m) := G.filter (fun w => A w ⊆ S i ∧ 2 ≤ (A w).card)
  have hsub (i : Fin m) : Q i ⊆ G := Finset.filter_subset _ _
  have hrow (i : Fin m) : c i ≤ (Q i).card := by
    by_contra! hlt
    obtain ⟨B, hd, hB, hprop⟩ := exists_frontier (Q i) child
      (fun w hw => hchild w (hsub i hw)) (fun w hw => hprev w (hsub i hw)) (o i)
    have hsmall : ∀ w ∈ B, A w ⊆ S i → (A w).card ≤ 1 := by
      intro w hw hS
      by_contra! hf
      have hwQ : w ∈ Q i := Finset.mem_filter.mpr ⟨hgate w hf, hS, hf⟩
      exact Finset.disjoint_left.mp hd hw hwQ
    obtain ⟨Y, hYS, hY, p, hp, hhit⟩ := select_witnesses A (A (o i)) (S i) B
      (by have := hcount i; omega) hsmall
    let y : Fin n → Bool := fun q => decide (q ∈ Y)
    have hP := hprop (fun w => v (fun q => decide (q = p)) w = true → v y w = true)
      (fun w hw => hstep w (hsub i hw) _ y) (by
        intro w hw hv
        obtain ⟨q, hqY, hqA⟩ := hhit w hw ((hsing w p).mpr hv)
        apply hmono (fun z => decide (z = q)) y ?_ w ((hsing w q).mp hqA)
        intro z hz
        have e : z = q := of_decide_eq_true hz
        simpa [y, e] using hqY)
    have hbad := hP ((hsing (o i) p).mp hp)
    have hyset : Finset.univ.filter (fun q => y q = true) = Y := by
      ext q
      simp [y]
    have hfalse := hpromise i y (by rw [hyset]; have := hck i; omega) (by
      intro q hq
      have hn : q ∉ Y := fun h => Finset.disjoint_left.mp hYS h hq
      simp [y, hn])
    simp [hfalse] at hbad
  have hd : (↑(Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint Q := by
    intro i hi j hj hij
    apply Finset.disjoint_left.mpr
    intro w hwi hwj
    have hai := (Finset.mem_filter.mp hwi).2
    have haj := (Finset.mem_filter.mp hwj).2
    have hboth : A w ⊆ S i ∩ S j := fun z hz => Finset.mem_inter.mpr ⟨hai.1 hz, haj.1 hz⟩
    have := Finset.card_le_card hboth
    have := hpair i j hij
    omega
  calc
    ∑ i, c i ≤ ∑ i, (Q i).card := Finset.sum_le_sum (fun i _ => hrow i)
    _ = (Finset.univ.biUnion Q).card := (Finset.card_biUnion hd).symm
    _ ≤ G.card := Finset.card_le_card (by
      intro w hw
      obtain ⟨i, _, hwi⟩ := Finset.mem_biUnion.mp hw
      exact hsub i hwi)

end PEqualNP.Outside.L_meta_782_aux

open PEqualNP.Outside.L_meta_782_aux

theorem PEqualNP.Outside.L_meta_782 : ∀ (n m k : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (c : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ i : Fin m, 2 ≤ (Finset.univ.filter (fun a : Fin n => (C.wires (List.ofFn (fun b : Fin n => decide (b = a)))).getD (o i) false = true)).card) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → (∀ (i : Fin m) (p : Fin n), (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (o i) false = true → p ∈ S i) → (∀ (i : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k → (∀ q ∈ S i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false) → (∀ i : Fin m, c i ≤ k) → (∀ i : Fin m, c i + 1 ≤ (Finset.univ.filter (fun a : Fin n => (C.wires (List.ofFn (fun b : Fin n => decide (b = a)))).getD (o i) false = true)).card) → ∑ i : Fin m, c i ≤ C.size := by
  intro n m k S C o c hinter _ hgood _ hpromise hck hcount
  let G := Finset.Ico n (n + C.size)
  have h := PEqualNP.Outside.L_meta_782_aux.count_private S o c G
    (support C n) (val C n) (children C n)
    (fun w _ => children_card C n w hgood)
    (fun w _ q hq => child_lt C n w q hq)
    (fun w hw => Finset.mem_Ico.mpr (support_gate C n w hw))
    (by intro w p; simp [support, val])
    (fun x y hxy w => val_mono C n x y hgood hxy w)
    (fun w hw x y => val_children C n w x y hgood (Finset.mem_Ico.mp hw).1)
    hinter hpromise hck hcount
  simpa [G] using h
