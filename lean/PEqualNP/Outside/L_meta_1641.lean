import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1641
open PEqualNP.CircuitLowerBounds

-- The wire evaluator is adapted from L_meta_782.
private def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

private lemma run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

private lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih => rw [run_cons, ih]; simp; omega

private lemma run_getD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (run gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

private lemma run_split (gs : List Gate) (x : List Bool) (j : ℕ) :
    run gs x = run (gs.drop j) (run (gs.take j) x) := by
  simpa only [run, List.foldl_append] using
    congrArg (fun l : List Gate => run l x) (List.take_append_drop j gs).symm

private def value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

private lemma input_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (p : Fin n) :
    value C x p = x p := by
  change (run C.gates (List.ofFn x)).getD p false = x p
  have hp : (p : ℕ) < (List.ofFn x).length := by simp
  rw [run_getD _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp

private lemma missing_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.size ≤ w) : value C x w = false := by
  change (run C.gates (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by simpa [run_length, Circuit.size] using hw)

-- At a gate, reads of earlier wires agree with the completed run.
-- All other reads contribute false, even if the wire is produced later.
private lemma gate_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + C.size) :
    let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
    value C x w = g.op.eval (g.inputs.map fun r => if r < w then value C x r else false) := by
  let j := w - n
  have hj : j < C.gates.length := by unfold j Circuit.size at *; omega
  let g := C.gates[j]
  let earlier := run (C.gates.take j) (List.ofFn x)
  have plen : earlier.length = w := by
    simp [earlier, run_length, Nat.min_eq_left hj.le, j]; omega
  have split : run C.gates (List.ofFn x) = run (g :: C.gates.drop (j + 1)) earlier := by
    rw [run_split C.gates (List.ofFn x) j, List.drop_eq_getElem_cons hj]
  have read (r : ℕ) : earlier.getD r false = if r < w then value C x r else false := by
    by_cases hr : r < w
    · rw [ite_eq_left hr]
      change earlier.getD r false = (run C.gates (List.ofFn x)).getD r false
      rw [split]
      exact (run_getD _ earlier r (by simpa only [plen] using hr)).symm
    · rw [ite_eq_right hr]
      exact List.getD_eq_default _ _ (by omega)
  change (run C.gates (List.ofFn x)).getD w false =
    g.op.eval (g.inputs.map fun r => if r < w then value C x r else false)
  rw (occs := [1]) [split]
  rw (occs := [1]) [run_cons]
  rw [run_getD _ _ _ (by simp [plen]), List.getD_append_right _ _ _ _ (by omega)]
  simp only [plen, Nat.sub_self, List.getD_cons_zero, read]

-- The monotonicity argument is adapted from L_meta_988.
lemma gate_inputs {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (w : ℕ) (hn : n ≤ w) (hw : w < n + C.size) :
    ∃ P : Finset ℕ, P.card ≤ 2 ∧ (∀ r ∈ P, r < w) ∧
      ∀ (x y : Fin n → Bool), (∀ r ∈ P, value C x r = true → value C y r = true) →
        value C x w = true → value C y w = true := by
  classical
  let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
  obtain ⟨hop, hlen⟩ := hG g (List.getElem_mem _)
  let P := g.inputs.toFinset.filter (· < w)
  refine ⟨P, (Finset.card_filter_le _ _).trans ((List.toFinset_card_le _).trans hlen), ?_, ?_⟩
  · intro r hr
    exact (Finset.mem_filter.mp hr).2
  · intro x y hxy hx
    have hr (r : ℕ) (hr : r ∈ g.inputs) :
        (if r < w then value C x r else false) = true →
        (if r < w then value C y r else false) = true := by
      by_cases h : r < w
      · simpa [h] using hxy r (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hr, h⟩)
      · simp [h]
    have formula (z : Fin n → Bool) :
        value C z w = g.op.eval (g.inputs.map fun r => if r < w then value C z r else false) :=
      gate_value C z w hn hw
    rw [formula x] at hx
    rw [formula y]
    rcases hop with hop | hop
    · simp only [hop, GateOp.eval, List.all_eq_true, id_eq] at hx ⊢
      intro b hb
      obtain ⟨r, hrm, rfl⟩ := List.mem_map.mp hb
      exact hr r hrm (hx _ (List.mem_map.mpr ⟨r, hrm, rfl⟩))
    · simp only [hop, GateOp.eval, List.any_eq_true, id_eq] at hx ⊢
      obtain ⟨b, hb, hbt⟩ := hx
      obtain ⟨r, hrm, rfl⟩ := List.mem_map.mp hb
      exact ⟨_, List.mem_map.mpr ⟨r, hrm, rfl⟩, hr r hrm hbt⟩

lemma value_mono {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x y : Fin n → Bool) (hxy : ∀ p, x p = true → y p = true) (w : ℕ) :
    value C x w = true → value C y w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hn : w < n
    · let p : Fin n := ⟨w, hn⟩
      change value C x p = true → value C y p = true
      simpa only [input_value] using hxy p
    by_cases hw : w < n + C.size
    · obtain ⟨P, _, hP, hstep⟩ := gate_inputs C hG w (by omega) hw
      exact hstep x y fun r hr => ih r (hP r hr)
    · simp [missing_value C x w (by omega)]

private def OrClosed (n : ℕ) (gates : List Gate) (Z : Set ℕ) : Prop :=
  ∀ k : Fin gates.length, n + (k : ℕ) ∈ Z → (gates.get k).op = GateOp.or →
    ∀ e ∈ (gates.get k).inputs, e ∈ Z

private def Reaches (n : ℕ) (gates : List Gate) (w z : ℕ) : Prop :=
  ∀ Z : Set ℕ, w ∈ Z → OrClosed n gates Z → z ∈ Z

private theorem reaches_refl (n : ℕ) (gates : List Gate) (w : ℕ) :
    Reaches n gates w w := fun _ hw _ => hw

private theorem reaches_edge {n : ℕ} {gates : List Gate} {k : Fin gates.length}
    {e : ℕ} (hop : (gates.get k).op = GateOp.or) (he : e ∈ (gates.get k).inputs) :
    Reaches n gates (n + (k : ℕ)) e := fun _ hw hZ => hZ k hw hop e he

private theorem reaches_trans {n : ℕ} {gates : List Gate} {a b c : ℕ}
    (hab : Reaches n gates a b) (hbc : Reaches n gates b c) : Reaches n gates a c :=
  fun Z ha hZ => hbc Z (hab Z ha hZ) hZ

private theorem reaches_split {n : ℕ} {gates : List Gate} {w z : ℕ} :
    Reaches n gates w z ↔ z = w ∨
      ∃ k : Fin gates.length, w = n + (k : ℕ) ∧ (gates.get k).op = GateOp.or ∧
        ∃ e ∈ (gates.get k).inputs, Reaches n gates e z := by
  constructor
  · intro hz
    let Z : Set ℕ := {a | a = w ∨
      ∃ k : Fin gates.length, w = n + (k : ℕ) ∧ (gates.get k).op = GateOp.or ∧
        ∃ e ∈ (gates.get k).inputs, Reaches n gates e a}
    have hZ : OrClosed n gates Z := by
      intro k hk hop e he
      change e = w ∨ _
      rcases show n + (k : ℕ) = w ∨ _ from hk with h | ⟨j, hj, hjop, a, ha, hr⟩
      · exact Or.inr ⟨k, h.symm, hop, e, he, reaches_refl n gates e⟩
      · exact Or.inr ⟨j, hj, hjop, a, ha, reaches_trans hr (reaches_edge hop he)⟩
    exact hz Z (Or.inl rfl) hZ
  · rintro (rfl | ⟨k, rfl, hop, e, he, hz⟩)
    · exact reaches_refl n gates _
    · exact reaches_trans (reaches_edge hop he) hz

private theorem reaches_input {n : ℕ} {gates : List Gate} {p q : Fin n} :
    Reaches n gates p q ↔ q = p := by
  rw [reaches_split]
  constructor
  · rintro (h | ⟨k, hk, _⟩)
    · exact Fin.ext h
    · have hp := p.isLt
      omega
  · exact fun h => Or.inl (congrArg Fin.val h)

private theorem reaches_gate {n : ℕ} {gates : List Gate} (k : Fin gates.length) (p : Fin n) :
    Reaches n gates (n + (k : ℕ)) p ↔
      (gates.get k).op = GateOp.or ∧
        ∃ e ∈ (gates.get k).inputs, Reaches n gates e p := by
  rw [reaches_split]
  constructor
  · rintro (h | ⟨j, hj, hop, hreach⟩)
    · have hp := p.isLt
      omega
    · have h : j = k := Fin.ext (by omega)
      subst j
      exact ⟨hop, hreach⟩
  · exact fun ⟨hop, hr⟩ => Or.inr ⟨k, rfl, hop, hr⟩

private theorem normalized_or_value {n : ℕ} {gates : List Gate}
    (k : Fin gates.length) (x : Fin n → Bool)
    (hBack : ∀ e ∈ (gates.get k).inputs, e < n + (k : ℕ))
    (hOr : (gates.get k).op = GateOp.or) :
    value ⟨gates, 0⟩ x (n + (k : ℕ)) = true ↔
      ∃ e ∈ (gates.get k).inputs, value ⟨gates, 0⟩ x e = true := by
  have hw : n + (k : ℕ) < n + (Circuit.mk gates 0).size := by
    simpa [Circuit.size] using Nat.add_lt_add_left k.isLt n
  have he := gate_value (Circuit.mk gates 0) x (n + (k : ℕ)) (Nat.le_add_right _ _) hw
  have he' : value ⟨gates, 0⟩ x (n + (k : ℕ)) =
      (gates.get k).op.eval ((gates.get k).inputs.map fun e =>
        if e < n + (k : ℕ) then value ⟨gates, 0⟩ x e else false) := by
    simpa only [Nat.add_sub_cancel_left, List.get_eq_getElem] using he
  have hm : ((gates.get k).inputs.map fun e =>
        if e < n + (k : ℕ) then value ⟨gates, 0⟩ x e else false) =
      (gates.get k).inputs.map (value ⟨gates, 0⟩ x) :=
    List.map_congr_left (fun e h => if_pos (hBack e h))
  rw [he', hm, hOr]
  simp only [GateOp.eval, List.any_map, Function.comp_def, id_eq, List.any_eq_true]

private theorem reached_input_fires {n : ℕ} {gates : List Gate} {w : ℕ} {p : Fin n}
    (hBack : ∀ k : Fin gates.length, ∀ e ∈ (gates.get k).inputs, e < n + (k : ℕ))
    (x : Fin n → Bool) (hp : x p = true) (hReach : Reaches n gates w p) :
    value ⟨gates, 0⟩ x w = true := by
  by_contra hw
  have hwF : value ⟨gates, 0⟩ x w = false := Bool.eq_false_of_not_eq_true hw
  let Z : Set ℕ := {r | value ⟨gates, 0⟩ x r = false}
  have hZ : OrClosed n gates Z := by
    intro k hk hOr e he
    change value ⟨gates, 0⟩ x e = false
    apply Bool.eq_false_of_not_eq_true
    intro hTrue
    have hV := (normalized_or_value k x (hBack k) hOr).2 ⟨e, he, hTrue⟩
    exact Bool.false_ne_true ((show value ⟨gates, 0⟩ x (n + (k : ℕ)) = false from hk).symm.trans hV)
  have hpF : value ⟨gates, 0⟩ x p = false := hReach Z hwF hZ
  rw [input_value, hp] at hpF
  contradiction


private def Agrees {α : Type*} (A X : Finset α) : Prop :=
  ∀ p ∈ A, ∀ q ∈ A, p ∈ X ↔ q ∈ X

private def Related {α : Type*} (family : Finset α → Prop) (p q : α) : Prop :=
  ∀ X : Finset α, (∀ T, family T → Agrees T X) → (p ∈ X ↔ q ∈ X)

private theorem related_refl {α : Type*} (family : Finset α → Prop) (p : α) :
    Related family p p := fun _ _ => Iff.rfl

private theorem related_symm {α : Type*} {family : Finset α → Prop} {p q : α}
    (h : Related family p q) : Related family q p := fun X hX => (h X hX).symm

private theorem related_trans {α : Type*} {family : Finset α → Prop} {p q r : α}
    (hpq : Related family p q) (hqr : Related family q r) : Related family p r :=
  fun X hX => (hpq X hX).trans (hqr X hX)

private theorem related_add {α : Type*} {family : Finset α → Prop}
    {S A : Finset α} (hSub : ∀ T, family T → T ⊆ S) (hA : A ⊆ S)
    {p q : α} (hp : p ∈ S) (hq : q ∈ S) :
    Related (fun T => family T ∨ T = A) p q ↔
      Related family p q ∨ ((∃ r ∈ A, Related family p r) ∧ (∃ r ∈ A, Related family q r)) := by
  classical
  have separate {u v : α} (hu : u ∈ S) (hn : ¬ Related family u v)
      (hMiss : ¬ ∃ r ∈ A, Related family u r) :
      ¬ Related (fun T => family T ∨ T = A) u v := by
    intro h
    let X := S.filter (Related family u)
    have hX : ∀ T : Finset α, family T ∨ T = A → Agrees T X := by
      intro T hT r hr s hs
      rcases hT with hT | rfl
      · have hRel : Related family r s := fun Y hY => hY T hT r hr s hs
        simp only [X, Finset.mem_filter, hSub T hT hr, hSub T hT hs, true_and]
        exact ⟨fun h => related_trans h hRel, fun h => related_trans h (related_symm hRel)⟩
      · simp only [X, Finset.mem_filter, hA hr, hA hs, true_and]
        exact iff_of_false (fun h => hMiss ⟨r, hr, h⟩) (fun h => hMiss ⟨s, hs, h⟩)
    have huX : u ∈ X := Finset.mem_filter.mpr ⟨hu, related_refl family u⟩
    exact hn (Finset.mem_filter.mp ((h X hX).mp huX)).2
  constructor
  · intro h
    by_cases hpq : Related family p q
    · exact Or.inl hpq
    · apply Or.inr
      exact ⟨Classical.byContradiction (fun hn => separate hp hpq hn h),
        Classical.byContradiction (fun hn => separate hq (fun hh => hpq (related_symm hh)) hn (related_symm h))⟩
  · rintro (h | ⟨⟨r, hr, hpr⟩, ⟨s, hs, hqs⟩⟩) X hX
    · exact h X (fun T hT => hX T (Or.inl hT))
    · exact (hpr X (fun T hT => hX T (Or.inl hT))).trans
        ((hX A (Or.inr rfl) r hr s hs).trans
          (hqs X (fun T hT => hX T (Or.inl hT))).symm)

private noncomputable def Block {α : Type*} (S : Finset α)
    (family : Finset α → Prop) (p : α) : Finset α := by
  classical
  exact S.filter (Related family p)

private theorem mem_block {α : Type*} {S : Finset α} {family : Finset α → Prop} {p q : α} :
    q ∈ Block S family p ↔ q ∈ S ∧ Related family p q := by
  classical
  simp [Block]

private theorem block_eq {α : Type*} {S : Finset α} {family : Finset α → Prop} {p q : α}
    (h : Related family p q) : Block S family p = Block S family q := by
  ext r
  simp only [mem_block]
  refine and_congr_right (fun _ => ?_)
  exact ⟨fun hp => related_trans (related_symm h) hp, related_trans h⟩

private theorem block_not_touched {α : Type*} {family : Finset α → Prop}
    {S A : Finset α} (hFamily : ∀ T, family T → T ⊆ S) (hAS : A ⊆ S)
    {p : α} (hp : p ∈ S) (hd : Disjoint (Block S family p) A) :
    Block S (fun T => family T ∨ T = A) p = Block S family p := by
  ext q
  simp only [mem_block]
  refine and_congr_right (fun hq => ?_)
  rw [related_add hFamily hAS hp hq]
  refine or_iff_left (fun h => ?_)
  obtain ⟨r, hr, hpr⟩ := h.1
  exact Finset.disjoint_left.mp hd (mem_block.mpr ⟨hAS hr, hpr⟩) hr

private theorem block_touched {α : Type*} {family : Finset α → Prop}
    {S A : Finset α} (hFamily : ∀ T, family T → T ⊆ S) (hAS : A ⊆ S)
    {p q : α} (hp : p ∈ A) :
    q ∈ Block S (fun T => family T ∨ T = A) p ↔
      q ∈ S ∧ ∃ r ∈ A, Related family q r := by
  simp only [mem_block]
  refine and_congr_right (fun hq => ?_)
  rw [related_add hFamily hAS (hAS hp) hq]
  constructor
  · rintro (h | h)
    · exact ⟨p, hp, related_symm h⟩
    · exact h.2
  · exact fun h => Or.inr ⟨⟨p, hp, related_refl family p⟩, h⟩

private theorem touched_card {α β : Type*} [DecidableEq α]
    {S : Finset α} {family : Finset α → Prop} {B : Finset (Finset α)}
    {W : Finset β} {A : β → Finset α}
    (hB : ∀ b ∈ B, ∃ p ∈ S, b = Block S family p)
    (hLocal : ∀ w ∈ W, ∀ r ∈ A w, ∀ s ∈ A w, Related family r s)
    (hTouch : ∀ b ∈ B, ∃ w ∈ W, ∃ r ∈ A w, r ∈ b) :
    B.card ≤ W.card := by
  classical
  let pick (w : β) : Finset α :=
    if h : (A w).Nonempty then Block S family h.choose else ∅
  have hIncl : B ⊆ W.image pick := by
    intro b hb
    obtain ⟨p, _, rfl⟩ := hB b hb
    obtain ⟨w, hw, r, hr, hrB⟩ := hTouch (Block S family p) hb
    have hne : (A w).Nonempty := ⟨r, hr⟩
    have hpr := (mem_block.mp hrB).2
    have hpc := related_trans hpr (hLocal w hw r hr hne.choose hne.choose_spec)
    apply Finset.mem_image.mpr
    refine ⟨w, hw, ?_⟩
    simpa [pick, hne] using (block_eq (S := S) hpc).symm
  exact (Finset.card_le_card hIncl).trans Finset.card_image_le

private theorem card_drop_le_one {α : Type*} [DecidableEq α]
    {old next affected : Finset α} (hOld : affected ⊆ old)
    (hKeep : old \ affected ⊆ next) (hTwo : affected.card ≤ 2)
    (hReplace : affected.card = 2 → ∃ x ∈ next, x ∉ old \ affected) :
    old.card ≤ next.card + 1 := by
  have hRest := Finset.card_sdiff_of_subset hOld
  have hKept := Finset.card_le_card hKeep
  by_cases h : affected.card = 2
  · obtain ⟨x, hx, hn⟩ := hReplace h
    have hInsert : insert x (old \ affected) ⊆ next :=
      Finset.insert_subset hx hKeep
    have hc := Finset.card_le_card hInsert
    rw [Finset.card_insert_of_notMem hn] at hc
    omega
  · omega

private theorem count_losses {len : ℕ} (c : ℕ → ℕ) (X : Finset (Fin len))
    (hDrop : ∀ j : Fin len, c j ≤ c (j + 1) + 1)
    (hStay : ∀ j : Fin len, j ∉ X → c j = c (j + 1)) :
    c 0 ≤ X.card + c len := by
  classical
  let before (k : ℕ) : Finset (Fin len) := X.filter (fun i => (i : ℕ) < k)
  have bound (k : ℕ) (hk : k ≤ len) : c 0 ≤ (before k).card + c k := by
    induction k with
    | zero => simp
    | succ k ih =>
      let j : Fin len := ⟨k, by omega⟩
      have hPrev := ih (by omega)
      have prefixStep : before (k + 1) =
          if j ∈ X then insert j (before k) else before k := by
        ext i
        by_cases hj : j ∈ X
        · simp only [before, hj, if_pos, Finset.mem_filter, Finset.mem_insert]
          constructor
          · rintro ⟨hi, hik⟩
            by_cases h : (i : ℕ) = k
            · exact Or.inl (Fin.ext h)
            · exact Or.inr ⟨hi, by omega⟩
          · rintro (rfl | ⟨hi, hik⟩)
            · exact ⟨hj, by change k < k + 1; omega⟩
            · exact ⟨hi, by omega⟩
        · simp only [before, hj, if_false, Finset.mem_filter]
          refine and_congr_right (fun hi => ?_)
          have hne : (i : ℕ) ≠ k := fun h => hj ((Fin.ext h : i = j) ▸ hi)
          omega
      by_cases hj : j ∈ X
      · have hn : j ∉ before k := by simp [before, j]
        have h := hDrop j
        change c k ≤ c (k + 1) + 1 at h
        rw [prefixStep, if_pos hj, Finset.card_insert_of_notMem hn]
        omega
      · have h := hStay j hj
        change c k = c (k + 1) at h
        rw [prefixStep, if_neg hj]
        omega
  have hPrefix : (before len).card ≤ X.card := Finset.card_filter_le _ _
  exact (bound len le_rfl).trans (Nat.add_le_add_right hPrefix _)

private noncomputable def Unanchored {α : Type*} (S : Finset α)
    (family : Finset α → Prop) (A : Finset α) : Finset (Finset α) := by
  classical
  exact (S.image (Block S family)).filter (fun b => Disjoint b A)

private theorem mem_unanchored {α : Type*} {S A b : Finset α}
    {family : Finset α → Prop} :
    b ∈ Unanchored S family A ↔ ∃ p ∈ S, b = Block S family p ∧ Disjoint b A := by
  classical
  unfold Unanchored
  rw [Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨⟨p, hp, he⟩, hd⟩
    exact ⟨p, hp, he.symm, hd⟩
  · rintro ⟨p, hp, he, hd⟩
    exact ⟨⟨p, hp, he.symm⟩, hd⟩

private theorem block_le_after {α : Type*} {S T : Finset α}
    {family : Finset α → Prop} {p : α} :
    Block S family p ⊆ Block S (fun Q => family Q ∨ Q = T) p := by
  intro u hu
  obtain ⟨huS, hRel⟩ := mem_block.mp hu
  exact mem_block.mpr ⟨huS, fun X hX => hRel X fun Q hQ => hX Q (Or.inl hQ)⟩

private noncomputable def Affected {α : Type*} (B : Finset (Finset α)) (T : Finset α) :
    Finset (Finset α) := by
  classical
  exact B.filter (fun b => ¬ Disjoint b T)

private theorem mem_affected {α : Type*} {B : Finset (Finset α)} {T b : Finset α} :
    b ∈ Affected B T ↔ b ∈ B ∧ ¬ Disjoint b T := by
  classical
  simp [Affected]

private theorem unaffected_stay {α : Type*} [DecidableEq α]
    {S A A' T : Finset α} {family : Finset α → Prop}
    (hFamily : ∀ Q, family Q → Q ⊆ S) (hTS : T ⊆ S) (hA' : A' ⊆ A ∪ T) :
    Unanchored S family A \ Affected (Unanchored S family A) T ⊆
      Unanchored S (fun Q => family Q ∨ Q = T) A' := by
  classical
  intro b hb
  obtain ⟨hbOld, hbKeep⟩ := Finset.mem_sdiff.mp hb
  obtain ⟨p, hp, rfl, hd⟩ := mem_unanchored.mp hbOld
  have hDT : Disjoint (Block S family p) T := by
    by_contra hn
    exact hbKeep (mem_affected.mpr ⟨hbOld, hn⟩)
  refine mem_unanchored.mpr ⟨p, hp, (block_not_touched hFamily hTS hp hDT).symm, ?_⟩
  exact (Finset.disjoint_union_right.mpr ⟨hd, hDT⟩).mono_right hA'

private theorem next_class_cases {α : Type*} [DecidableEq α]
    {S A A' T : Finset α} {family : Finset α → Prop}
    (hFamily : ∀ Q, family Q → Q ⊆ S) (hTS : T ⊆ S) (hA : A ⊆ A')
    {b : Finset α}
    (hb : b ∈ Unanchored S (fun Q => family Q ∨ Q = T) A') :
    b ∈ Unanchored S family A \ Affected (Unanchored S family A) T ∨
      ∃ t ∈ T, b = Block S (fun Q => family Q ∨ Q = T) t := by
  classical
  obtain ⟨p, hp, rfl, hD⟩ := mem_unanchored.mp hb
  by_cases hd : Disjoint (Block S (fun Q => family Q ∨ Q = T) p) T
  · have hOld : Disjoint (Block S family p) T := hd.mono_left block_le_after
    have he := block_not_touched hFamily hTS hp hOld
    left
    rw [he]
    have hOldA : Disjoint (Block S family p) A := (hD.mono_right hA).mono_left block_le_after
    exact Finset.mem_sdiff.mpr ⟨mem_unanchored.mpr ⟨p, hp, rfl, hOldA⟩,
      fun hm => (mem_affected.mp hm).2 hOld⟩
  · obtain ⟨t, htp, ht⟩ := Finset.not_disjoint_iff.mp hd
    exact Or.inr ⟨t, ht, block_eq (mem_block.mp htp).2⟩

private theorem merge_class_eq {α : Type*} {S T : Finset α}
    {family : Finset α → Prop} {s t : α} (hs : s ∈ T) (ht : t ∈ T) :
    Block S (fun Q => family Q ∨ Q = T) s =
      Block S (fun Q => family Q ∨ Q = T) t :=
  block_eq (fun _ hX => hX T (Or.inr rfl) s hs t ht)

private theorem merge_class_counts {α : Type*} [DecidableEq α]
    {S A A' T : Finset α} {family : Finset α → Prop}
    (hFamily : ∀ Q, family Q → Q ⊆ S) (hTS : T ⊆ S) (hA : A ⊆ A')
    (hA' : A' ⊆ A ∪ T)
    (hTwo : (Affected (Unanchored S family A) T).card ≤ 2)
    (hReplace : (Affected (Unanchored S family A) T).card = 2 →
      ∃ t ∈ T, Disjoint (Block S (fun Q => family Q ∨ Q = T) t) A') :
    (Unanchored S (fun Q => family Q ∨ Q = T) A').card ≤ (Unanchored S family A).card ∧
      (Unanchored S family A).card ≤ (Unanchored S (fun Q => family Q ∨ Q = T) A').card + 1 := by
  classical
  let prev := Unanchored S family A
  let next := Unanchored S (fun Q => family Q ∨ Q = T) A'
  let cut := Affected prev T
  have hCut : cut ⊆ prev := fun _ h => (mem_affected.mp h).1
  have hKeep : prev \ cut ⊆ next := unaffected_stay hFamily hTS hA'
  have hDrop : prev.card ≤ next.card + 1 := by
    apply card_drop_le_one hCut hKeep hTwo
    intro hEq
    obtain ⟨t, ht, hd⟩ := hReplace hEq
    let b := Block S (fun Q => family Q ∨ Q = T) t
    have htB : t ∈ b := mem_block.mpr ⟨hTS ht, related_refl _ _⟩
    refine ⟨b, mem_unanchored.mpr ⟨t, hTS ht, rfl, hd⟩, ?_⟩
    intro h
    obtain ⟨hbPrev, hNot⟩ := Finset.mem_sdiff.mp h
    exact hNot (mem_affected.mpr ⟨hbPrev, fun hh => Finset.disjoint_left.mp hh htB ht⟩)
  refine ⟨?_, hDrop⟩
  change next.card ≤ prev.card
  by_cases hNo : ∀ b ∈ next, b ∈ prev \ cut
  · exact (Finset.card_le_card hNo).trans (Finset.card_le_card Finset.sdiff_subset)
  · push_neg at hNo
    obtain ⟨b, hbNext, hbn⟩ := hNo
    obtain ⟨t, ht, hbt⟩ := (next_class_cases hFamily hTS hA hbNext).resolve_left hbn
    have hIncl : next ⊆ insert b (prev \ cut) := by
      intro c hc
      rcases next_class_cases hFamily hTS hA hc with hcOld | ⟨s, hs, hcs⟩
      · exact Finset.mem_insert_of_mem hcOld
      · exact Finset.mem_insert.mpr (Or.inl (hcs.trans ((merge_class_eq hs ht).trans hbt.symm)))
    have hOld : Block S family t ∈ prev := by
      have hd := (mem_unanchored.mp hbNext).choose_spec.2.2
      rw [hbt] at hd
      exact mem_unanchored.mpr ⟨t, hTS ht, rfl, (hd.mono_right hA).mono_left block_le_after⟩
    have hTCut : Block S family t ∈ cut :=
      mem_affected.mpr ⟨hOld, fun h => Finset.disjoint_left.mp h
        (mem_block.mpr ⟨hTS ht, related_refl _ _⟩) ht⟩
    have hPos : 0 < cut.card := Finset.card_pos.mpr ⟨_, hTCut⟩
    have hc := Finset.card_le_card hIncl
    rw [Finset.card_insert_of_notMem hbn, Finset.card_sdiff_of_subset hCut] at hc
    have hLe := Finset.card_le_card hCut
    omega


private noncomputable def TraceSupport {n : ℕ} (gates : List Gate) (S : Finset (Fin n))
    (w : ℕ) : Finset (Fin n) := by
  classical
  exact S.filter (fun p => Reaches n gates w p)

private theorem mem_trace {n : ℕ} {gates : List Gate} {S : Finset (Fin n)}
    {w : ℕ} {p : Fin n} :
    p ∈ TraceSupport gates S w ↔ p ∈ S ∧ Reaches n gates w p := by
  classical
  simp [TraceSupport]

private def Cold {n : ℕ} (gates : List Gate) (S : Finset (Fin n)) (w : ℕ) : Prop :=
  value ⟨gates, 0⟩ (fun v : Fin n => decide (v ∉ S)) w = false

private def HitsAnchor {n : ℕ} (gates : List Gate) (p0 p1 : Fin n) (w : ℕ) : Prop :=
  value ⟨gates, 0⟩ (fun v : Fin n => decide (v = p0)) w = true ∨
    value ⟨gates, 0⟩ (fun v : Fin n => decide (v = p1)) w = true

private def MergesAt {n : ℕ} (gates : List Gate) (S : Finset (Fin n)) (j : ℕ)
    (T : Finset (Fin n)) : Prop :=
  ∃ k : Fin gates.length, (k : ℕ) < j ∧ (gates.get k).op = GateOp.or ∧
    Cold gates S (n + (k : ℕ)) ∧ T = TraceSupport gates S (n + (k : ℕ))

private noncomputable def AnchorsAt {n : ℕ} (gates : List Gate) (S : Finset (Fin n))
    (p0 p1 : Fin n) (j : ℕ) : Finset (Fin n) := by
  classical
  exact insert p0 (insert p1 (S.filter (fun p =>
    ∃ k : Fin gates.length, (k : ℕ) < j ∧ (gates.get k).op = GateOp.or ∧
      Cold gates S (n + (k : ℕ)) ∧ HitsAnchor gates p0 p1 (n + (k : ℕ)) ∧
      Reaches n gates (n + (k : ℕ)) p)))

private theorem merge_subset {n : ℕ} {gates : List Gate} {S T : Finset (Fin n)} {j : ℕ}
    (h : MergesAt gates S j T) : T ⊆ S := by
  obtain ⟨k, _, _, _, rfl⟩ := h
  exact fun _ hp => (mem_trace.mp hp).1

private theorem reaches_mem_cold {n : ℕ} {gates : List Gate} {S : Finset (Fin n)}
    {w : ℕ} {p : Fin n}
    (hBack : ∀ k : Fin gates.length, ∀ e ∈ (gates.get k).inputs, e < n + (k : ℕ))
    (hw : Cold gates S w) (h : Reaches n gates w p) : p ∈ S := by
  by_contra hp
  have hv := reached_input_fires hBack (fun v : Fin n => decide (v ∉ S)) (by simp [hp]) h
  exact Bool.false_ne_true (hw.symm.trans hv)

private theorem child_cold {n : ℕ} {gates : List Gate} {S : Finset (Fin n)}
    {j : Fin gates.length} {w : ℕ}
    (hBack : ∀ k : Fin gates.length, ∀ e ∈ (gates.get k).inputs, e < n + (k : ℕ))
    (hOr : (gates.get j).op = GateOp.or) (hCold : Cold gates S (n + (j : ℕ)))
    (hw : w ∈ (gates.get j).inputs) : Cold gates S w := by
  apply Bool.eq_false_of_not_eq_true
  intro hTrue
  have h := (normalized_or_value j (fun v : Fin n => decide (v ∉ S)) (hBack j) hOr).2
    ⟨w, hw, hTrue⟩
  exact Bool.false_ne_true (hCold.symm.trans h)

private theorem child_trace {n : ℕ} {gates : List Gate} {S : Finset (Fin n)}
    {p0 p1 : Fin n} {j : Fin gates.length} {w : ℕ}
    (hEarlier : w < n + (j : ℕ)) (hw : Cold gates S w) :
    (∀ r ∈ TraceSupport gates S w, ∀ s ∈ TraceSupport gates S w,
      Related (MergesAt gates S j) r s) ∧
    (HitsAnchor gates p0 p1 w → TraceSupport gates S w ⊆ AnchorsAt gates S p0 p1 j) := by
  classical
  by_cases hSmall : w < n
  · let v : Fin n := ⟨w, hSmall⟩
    have hAll : ∀ r ∈ TraceSupport gates S w, r = v :=
      fun _ hr => reaches_input.mp (mem_trace.mp hr).2
    constructor
    · intro r hr s hs
      rw [hAll r hr, hAll s hs]
      exact related_refl _ _
    · intro hAnchor r hr
      have hv : v = p0 ∨ v = p1 := by
        unfold HitsAnchor at hAnchor
        change value ⟨gates, 0⟩ (fun u : Fin n => decide (u = p0)) v = true ∨
          value ⟨gates, 0⟩ (fun u : Fin n => decide (u = p1)) v = true at hAnchor
        simpa only [input_value, decide_eq_true_eq] using hAnchor
      rcases hv with hv | hv
      · exact Finset.mem_insert.mpr (Or.inl ((hAll r hr).trans hv))
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl ((hAll r hr).trans hv))))
  · let k : Fin gates.length := ⟨w - n, by have hj := j.isLt; omega⟩
    have hkw : n + (k : ℕ) = w := by simp [k]; omega
    have hk : (k : ℕ) < (j : ℕ) := by omega
    have hOr {r : Fin n} (hr : r ∈ TraceSupport gates S w) : (gates.get k).op = GateOp.or := by
      have h := (mem_trace.mp hr).2
      rw [← hkw] at h
      exact (reaches_gate k r |>.mp h).1
    constructor
    · intro r hr s hs X hX
      have hT : MergesAt gates S j (TraceSupport gates S w) :=
        ⟨k, hk, hOr hr, by simpa only [hkw] using hw, by rw [hkw]⟩
      exact hX _ hT r hr s hs
    · intro hAnchor r hr
      have hm := mem_trace.mp hr
      apply Finset.mem_insert.mpr
      apply Or.inr
      apply Finset.mem_insert.mpr
      apply Or.inr
      exact Finset.mem_filter.mpr ⟨hm.1, k, hk, hOr hr, by simpa only [hkw] using hw,
        by simpa only [hkw] using hAnchor, by simpa only [hkw] using hm.2⟩

private theorem gate_trace {n : ℕ} {gates : List Gate} {S : Finset (Fin n)}
    {j : Fin gates.length} (hOr : (gates.get j).op = GateOp.or) :
    TraceSupport gates S (n + (j : ℕ)) =
      (gates.get j).inputs.toFinset.biUnion (TraceSupport gates S) := by
  classical
  ext r
  simp only [mem_trace, reaches_gate, hOr, true_and, Finset.mem_biUnion, List.mem_toFinset]
  constructor
  · rintro ⟨hr, e, he, hReaches⟩
    exact ⟨e, he, hr, hReaches⟩
  · rintro ⟨e, he, hr, hReaches⟩
    exact ⟨hr, e, he, hReaches⟩

private theorem merges_succ {n : ℕ} {gates : List Gate} {S : Finset (Fin n)}
    (j : Fin gates.length) :
    MergesAt gates S ((j : ℕ) + 1) = fun T => MergesAt gates S j T ∨
      ((gates.get j).op = GateOp.or ∧ Cold gates S (n + (j : ℕ)) ∧
        T = TraceSupport gates S (n + (j : ℕ))) := by
  funext T
  apply propext
  constructor
  · rintro ⟨k, hk, hOr, hCold, hT⟩
    by_cases hEq : k = j
    · subst k
      exact Or.inr ⟨hOr, hCold, hT⟩
    · have hne : (k : ℕ) ≠ (j : ℕ) := fun h => hEq (Fin.ext h)
      exact Or.inl ⟨k, by omega, hOr, hCold, hT⟩
  · rintro (⟨k, hk, hOr, hCold, hT⟩ | ⟨hOr, hCold, hT⟩)
    · exact ⟨k, by omega, hOr, hCold, hT⟩
    · exact ⟨j, by omega, hOr, hCold, hT⟩

private theorem anchors_succ {n : ℕ} {gates : List Gate} {S : Finset (Fin n)}
    (p0 p1 : Fin n) (j : Fin gates.length) (p : Fin n) :
    p ∈ AnchorsAt gates S p0 p1 ((j : ℕ) + 1) ↔
      p ∈ AnchorsAt gates S p0 p1 j ∨
      ((gates.get j).op = GateOp.or ∧ Cold gates S (n + (j : ℕ)) ∧
        HitsAnchor gates p0 p1 (n + (j : ℕ)) ∧ p ∈ TraceSupport gates S (n + (j : ℕ))) := by
  classical
  simp only [AnchorsAt, Finset.mem_insert, Finset.mem_filter, mem_trace]
  constructor
  · rintro (h | h | ⟨hp, k, hk, hOr, hCold, hHit, hReach⟩)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr (Or.inl h))
    · by_cases hEq : k = j
      · subst k
        exact Or.inr ⟨hOr, hCold, hHit, hp, hReach⟩
      · have hne : (k : ℕ) ≠ (j : ℕ) := fun h => hEq (Fin.ext h)
        exact Or.inl (Or.inr (Or.inr ⟨hp, k, by omega, hOr, hCold, hHit, hReach⟩))
  · rintro ((h | h | ⟨hp, k, hk, hOr, hCold, hHit, hReach⟩) |
      ⟨hOr, hCold, hHit, hp, hReach⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨hp, k, by omega, hOr, hCold, hHit, hReach⟩)
    · exact Or.inr (Or.inr ⟨hp, j, by omega, hOr, hCold, hHit, hReach⟩)

private theorem initial_blocks {n : ℕ} {gates : List Gate} {S : Finset (Fin n)}
    {p0 p1 : Fin n} (h01 : p0 ≠ p1) (h0 : p0 ∈ S) (h1 : p1 ∈ S) :
    (Unanchored S (MergesAt gates S 0) (AnchorsAt gates S p0 p1 0)).card = S.card - 2 := by
  classical
  have hBlock (p : Fin n) (hp : p ∈ S) : Block S (MergesAt gates S 0) p = {p} := by
    ext q
    rw [mem_block, Finset.mem_singleton]
    constructor
    · intro h
      have hv := h.2 {p} (by
        rintro _ ⟨k, hk, _⟩
        omega)
      exact Finset.mem_singleton.mp (hv.mp (Finset.mem_singleton_self p))
    · rintro rfl
      exact ⟨hp, related_refl _ _⟩
  have hAnchors : AnchorsAt gates S p0 p1 0 = {p0, p1} := by
    ext u
    simp [AnchorsAt]
  have hBlocks : Unanchored S (MergesAt gates S 0) (AnchorsAt gates S p0 p1 0) =
      (S \ {p0, p1}).image (fun p => {p}) := by
    ext b
    rw [mem_unanchored, Finset.mem_image, hAnchors]
    constructor
    · rintro ⟨p, hp, rfl, hd⟩
      rw [hBlock p hp] at hd ⊢
      exact ⟨p, Finset.mem_sdiff.mpr ⟨hp, fun h => Finset.disjoint_left.mp hd
        (Finset.mem_singleton_self p) h⟩, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      obtain ⟨hpS, hpOff⟩ := Finset.mem_sdiff.mp hp
      exact ⟨p, hpS, (hBlock p hpS).symm, by simpa using hpOff⟩
  rw [hBlocks, Finset.card_image_of_injective _ Finset.singleton_injective,
    Finset.card_sdiff_of_subset (Finset.insert_subset h0 (Finset.singleton_subset_iff.mpr h1)),
    Finset.card_pair h01]


private theorem gate_keeps_count {n : ℕ} {gates : List Gate}
    {L : Fin n → Finset (Fin n)} {i0 p0 p1 : Fin n}
    (hLines : ∀ i j : Fin n, i ≠ j → (L i ∩ L j).card = 1)
    (hp0 : p0 ∈ L i0) (hp1 : p1 ∈ L i0)
    (hG : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hBack : ∀ k : Fin gates.length, ∀ e ∈ (gates.get k).inputs, e < n + (k : ℕ))
    (j : Fin gates.length) :
    let S := L i0
    let clk := fun k => (Unanchored S (MergesAt gates S k) (AnchorsAt gates S p0 p1 k)).card
    clk (j + 1) ≤ clk j ∧ clk j ≤ clk (j + 1) + 1 ∧
      (¬ ((gates.get j).op = GateOp.or ∧ Cold gates S (n + (j : ℕ)) ∧
        (∀ t : Fin n, t ≠ i0 → ¬ Cold gates (L t) (n + (j : ℕ))) ∧
        ¬ ∀ e ∈ (gates.get j).inputs, HitsAnchor gates p0 p1 e) →
        clk j = clk (j + 1)) := by
  classical
  dsimp only
  let S := L i0
  let family := MergesAt gates S (j : ℕ)
  let oldMarks := AnchorsAt gates S p0 p1 (j : ℕ)
  let newMarks := AnchorsAt gates S p0 p1 ((j : ℕ) + 1)
  let touch := TraceSupport gates S (n + (j : ℕ))
  change (Unanchored S (MergesAt gates S ((j : ℕ) + 1)) newMarks).card ≤
      (Unanchored S family oldMarks).card ∧
    (Unanchored S family oldMarks).card ≤
      (Unanchored S (MergesAt gates S ((j : ℕ) + 1)) newMarks).card + 1 ∧ _
  by_cases hGate : (gates.get j).op = GateOp.or ∧ Cold gates S (n + (j : ℕ))
  · have hFamily : MergesAt gates S ((j : ℕ) + 1) =
        fun Q => family Q ∨ Q = touch := by
      rw [merges_succ j]
      simp only [hGate.1, hGate.2, true_and, family, touch]
    rw [hFamily]
    let added := fun Q => family Q ∨ Q = touch
    let before := Unanchored S family oldMarks
    let after := Unanchored S added newMarks
    let inputs := (gates.get j).inputs.toFinset
    let supp := TraceSupport gates S
    let affected := Affected before touch
    have hOld (Q : Finset (Fin n)) (h : family Q) : Q ⊆ S := merge_subset h
    have hTouch : touch ⊆ S := fun _ hp => (mem_trace.mp hp).1
    have mark (p : Fin n) : p ∈ newMarks ↔
        p ∈ oldMarks ∨ (HitsAnchor gates p0 p1 (n + (j : ℕ)) ∧ p ∈ touch) := by
      simpa only [hGate.1, hGate.2, true_and] using
        (anchors_succ (S := S) (gates := gates) p0 p1 j p)
    have hMarkLe : oldMarks ⊆ newMarks := fun p hp => (mark p).mpr (Or.inl hp)
    have hMarkGrow : newMarks ⊆ oldMarks ∪ touch := by
      intro p hp
      exact Finset.mem_union.mpr (((mark p).mp hp).imp_right And.right)
    have hChild (w : ℕ) (hw : w ∈ inputs) :=
      child_trace (p0 := p0) (p1 := p1) (j := j)
        (hBack j w (List.mem_toFinset.mp hw))
        (child_cold hBack hGate.1 hGate.2 (List.mem_toFinset.mp hw))
    have hSupport : touch = inputs.biUnion supp := gate_trace hGate.1
    have hInputCount : inputs.card ≤ 2 :=
      (List.toFinset_card_le _).trans (hG _ (List.get_mem gates j)).2
    have hOldBlock (b : Finset (Fin n)) (hb : b ∈ affected) :
        ∃ p ∈ S, b = Block S family p :=
      let ⟨p, hp, he, _⟩ := mem_unanchored.mp (mem_affected.mp hb).1
      ⟨p, hp, he⟩
    have hTouchInput (b : Finset (Fin n)) (hb : b ∈ affected) :
        ∃ w ∈ inputs, ∃ r ∈ supp w, r ∈ b := by
      obtain ⟨r, hr, hrt⟩ := Finset.not_disjoint_iff.mp (mem_affected.mp hb).2
      obtain ⟨w, hw, hrs⟩ := Finset.mem_biUnion.mp (hSupport ▸ hrt)
      exact ⟨w, hw, r, hrs, hr⟩
    have hAffected : affected.card ≤ 2 :=
      (touched_card hOldBlock (fun w hw => (hChild w hw).1) hTouchInput).trans hInputCount
    have hReplacement (hc : affected.card = 2) : ∃ t ∈ touch,
        Disjoint (Block S added t) newMarks := by
      let contributing := inputs.filter (fun w => ∃ b ∈ before, ∃ p ∈ supp w, p ∈ b)
      have hContrib : ∀ b ∈ affected, ∃ w ∈ contributing, ∃ r ∈ supp w, r ∈ b := by
        intro b hb
        obtain ⟨w, hw, r, hr, hrb⟩ := hTouchInput b hb
        exact ⟨w, Finset.mem_filter.mpr ⟨hw, b, (mem_affected.mp hb).1, r, hr, hrb⟩,
          r, hr, hrb⟩
      have hTwo := touched_card hOldBlock (fun w hw => (hChild w (Finset.mem_filter.mp hw).1).1) hContrib
      have hAll : contributing = inputs := by
        apply Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
        omega
      have hInBlock (w : ℕ) (hw : w ∈ inputs) :
          ∃ b ∈ before, ∃ p ∈ supp w, p ∈ b := by
        have hw' : w ∈ contributing := hAll.symm ▸ hw
        exact (Finset.mem_filter.mp hw').2
      have hNever (w : ℕ) (hw : w ∈ inputs) : ¬ HitsAnchor gates p0 p1 w := by
        intro h
        obtain ⟨b, hb, p, hp, hpb⟩ := hInBlock w hw
        exact Finset.disjoint_left.mp (mem_unanchored.mp hb).choose_spec.2.2 hpb
          ((hChild w hw).2 h hp)
      have hNotHit : ¬ HitsAnchor gates p0 p1 (n + (j : ℕ)) := by
        intro h
        rcases h with h0 | h1
        · obtain ⟨w, hw, h0w⟩ := (normalized_or_value j
            (fun p : Fin n => decide (p = p0)) (hBack j) hGate.1).mp h0
          exact hNever w (List.mem_toFinset.mpr hw) (Or.inl h0w)
        · obtain ⟨w, hw, h1w⟩ := (normalized_or_value j
            (fun p : Fin n => decide (p = p1)) (hBack j) hGate.1).mp h1
          exact hNever w (List.mem_toFinset.mpr hw) (Or.inr h1w)
      obtain ⟨b, hb⟩ := Finset.card_pos.mp (by omega : 0 < affected.card)
      obtain ⟨w, hw, t, ht, _⟩ := hTouchInput b hb
      have htT : t ∈ touch := by rw [hSupport]; exact Finset.mem_biUnion.mpr ⟨w, hw, ht⟩
      refine ⟨t, htT, Finset.disjoint_left.mpr ?_⟩
      intro r hr hMarkR
      have hMark0 : r ∈ oldMarks := ((mark r).mp hMarkR).resolve_right (fun h => hNotHit h.1)
      obtain ⟨hrS, s, hsT, hrs⟩ := (block_touched hOld hTouch htT).mp hr
      obtain ⟨v, hv, hvs⟩ := Finset.mem_biUnion.mp (hSupport ▸ hsT)
      obtain ⟨d, hd, p, hps, hpd⟩ := hInBlock v hv
      obtain ⟨q, _, he, hdA⟩ := mem_unanchored.mp hd
      have hqp : Related family q p := (mem_block.mp (he ▸ hpd)).2
      have hqr := related_trans hqp (related_trans ((hChild v hv).1 p hps s hvs) (related_symm hrs))
      exact Finset.disjoint_left.mp hdA (he.symm ▸ (mem_block.mpr ⟨hrS, hqr⟩)) hMark0
    obtain ⟨hLe, hDrop⟩ := merge_class_counts hOld hTouch hMarkLe hMarkGrow hAffected hReplacement
    refine ⟨hLe, hDrop, ?_⟩
    intro hNo
    change before.card = after.card
    have unchanged_if_marked (hMarked : touch ⊆ oldMarks) : before.card = after.card := by
      apply Nat.le_antisymm _ hLe
      apply Finset.card_le_card
      intro b hb
      have hd := (mem_unanchored.mp hb).choose_spec.2.2
      have k : b ∈ before \ affected := Finset.mem_sdiff.mpr ⟨hb,
        fun hc => (mem_affected.mp hc).2 (hd.mono_right hMarked)⟩
      exact unaffected_stay hOld hTouch hMarkGrow k
    by_cases hElse : ∀ t : Fin n, t ≠ i0 → ¬ Cold gates (L t) (n + (j : ℕ))
    · have hInputs : ∀ e ∈ (gates.get j).inputs, HitsAnchor gates p0 p1 e := by
        by_contra hn
        exact hNo ⟨hGate.1, hGate.2, hElse, hn⟩
      apply unchanged_if_marked
      intro r hr
      obtain ⟨w, hw, hwr⟩ := Finset.mem_biUnion.mp (hSupport ▸ hr)
      exact (hChild w hw).2 (hInputs w (List.mem_toFinset.mp hw)) hwr
    · push Not at hElse
      obtain ⟨t, hti, hCold⟩ := hElse
      have hrT (r : Fin n) (hr : r ∈ touch) : r ∈ S ∩ L t :=
        Finset.mem_inter.mpr ⟨hTouch hr, reaches_mem_cold hBack hCold (mem_trace.mp hr).2⟩
      have hSmall : touch.card ≤ 1 :=
        (Finset.card_le_card hrT).trans (by rw [Finset.inter_comm]; exact (hLines t i0 hti).le)
      by_cases hHit : HitsAnchor gates p0 p1 (n + (j : ℕ))
      · have point_cold (p : Fin n) (hp : p ∈ S)
            (h : value ⟨gates, 0⟩ (fun r : Fin n => decide (r = p)) (n + (j : ℕ)) = true) :
            p ∈ S ∩ L t := by
          refine Finset.mem_inter.mpr ⟨hp, ?_⟩
          by_contra hen
          have hv := value_mono ⟨gates, 0⟩ hG
            (fun r : Fin n => decide (r = p)) (fun r : Fin n => decide (r ∉ L t))
            (by
              intro r hr
              simp only [decide_eq_true_eq] at hr ⊢
              exact hr.symm ▸ hen)
            (n + (j : ℕ)) h
          exact Bool.false_ne_true (hCold.symm.trans hv)
        have hp : ∃ p ∈ S ∩ L t, p ∈ oldMarks := by
          rcases hHit with h | h
          · exact ⟨p0, point_cold p0 hp0 h, by simp [oldMarks, AnchorsAt]⟩
          · exact ⟨p1, point_cold p1 hp1 h, by simp [oldMarks, AnchorsAt]⟩
        obtain ⟨p, hp, hpM⟩ := hp
        apply unchanged_if_marked
        intro r hr
        have hc : (S ∩ L t).card ≤ 1 := by
          rw [Finset.inter_comm]
          exact (hLines t i0 hti).le
        rw [Finset.card_le_one] at hc
        exact (hc r (hrT r hr) p hp).symm ▸ hpM
      · have hMarks : newMarks = oldMarks := by
          ext p
          simp only [mark, hHit, false_and, or_false]
        have hRelated : Related added = Related family := by
          funext p q
          apply propext
          constructor
          · intro h Y hY
            apply h Y
            rintro Q (hQ | rfl)
            · exact hY Q hQ
            · intro r hr s hs
              rw [(Finset.card_le_one.mp hSmall) r hr s hs]
          · intro h Y hY
            exact h Y fun Q hQ => hY Q (Or.inl hQ)
        have hb : Block S added = Block S family := by
          funext p
          unfold Block
          rw [hRelated]
        have hSame : before = after := by
          ext b
          simp [after, before, mem_unanchored, hMarks, hb]
        exact congrArg Finset.card hSame
  · have hFamily : MergesAt gates S ((j : ℕ) + 1) = family := by
      rw [merges_succ j]
      funext Q
      apply propext
      exact or_iff_left (fun h => hGate ⟨h.1, h.2.1⟩)
    have hMarks : newMarks = oldMarks := by
      ext p
      rw [anchors_succ p0 p1 j p]
      exact or_iff_left (fun h => hGate ⟨h.1, h.2.1⟩)
    have he : (Unanchored S (MergesAt gates S ((j : ℕ) + 1)) newMarks).card =
        (Unanchored S family oldMarks).card := by rw [hFamily, hMarks]
    refine ⟨he.le, ?_, fun _ => he.symm⟩
    rw [he]
    omega


private theorem disjoint_anchors {n : ℕ} {gates : List Gate} {S b : Finset (Fin n)}
    {p0 p1 : Fin n} {j : ℕ} (hSub : b ⊆ S) :
    Disjoint b (AnchorsAt gates S p0 p1 j) ↔ p0 ∉ b ∧ p1 ∉ b ∧
      ∀ k : Fin gates.length, (k : ℕ) < j → (gates.get k).op = GateOp.or →
        Cold gates S (n + (k : ℕ)) → HitsAnchor gates p0 p1 (n + (k : ℕ)) →
        ∀ p ∈ b, ¬ Reaches n gates (n + (k : ℕ)) p := by
  classical
  simp only [Finset.disjoint_left, AnchorsAt, Finset.mem_insert, Finset.mem_filter]
  constructor
  · intro h
    refine ⟨fun hp => h hp (Or.inl rfl), fun hp => h hp (Or.inr (Or.inl rfl)), ?_⟩
    intro k hk hOr hCold hHit p hp hReach
    exact h hp (Or.inr (Or.inr ⟨hSub hp, k, hk, hOr, hCold, hHit, hReach⟩))
  · rintro ⟨h0, h1, h⟩ p hp (rfl | rfl | ⟨_, k, hk, hOr, hCold, hHit, hReach⟩)
    · exact h0 hp
    · exact h1 hp
    · exact h k hk hOr hCold hHit p hp hReach

private theorem stable_equivalence {n : ℕ} {gates : List Gate}
    {S X : Finset (Fin n)} {j : ℕ} :
    (∀ k : Fin gates.length, (k : ℕ) < j → (gates.get k).op = GateOp.or →
      Cold gates S (n + (k : ℕ)) →
      ∀ s ∈ S, ∀ t ∈ S, Reaches n gates (n + (k : ℕ)) s →
        Reaches n gates (n + (k : ℕ)) t → (s ∈ X ↔ t ∈ X)) ↔
    (∀ T, MergesAt gates S j T → Agrees T X) := by
  constructor
  · intro h T hT
    obtain ⟨k, hk, hOr, hc, rfl⟩ := hT
    intro s hs t ht
    exact h k hk hOr hc s (mem_trace.mp hs).1 t (mem_trace.mp ht).1
      (mem_trace.mp hs).2 (mem_trace.mp ht).2
  · intro h k hk hOr hc s hs t ht hrs hrt
    exact h _ ⟨k, hk, hOr, hc, rfl⟩ s (mem_trace.mpr ⟨hs, hrs⟩) t (mem_trace.mpr ⟨ht, hrt⟩)


end PEqualNP.Outside.L_meta_1641


set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.L_meta_1641 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N),
    3 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    p0 ≠ p1 → p0 ∈ L i0 → p1 ∈ L i0 →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate),
    (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ gt.inputs.length ≤ 2) →
    (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length) →
    (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
    ∀ ev : ℕ → (Fin N → Bool) → Bool, (∀ (w : ℕ) (x : Fin N → Bool), ev w x = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w⟩ (List.ofFn x)) →
    ∀ o0 : ℕ, ev o0 (fun v : Fin N => decide (v ∉ L i0)) = false → ev o0 (fun v : Fin N => decide (v = p0)) = true → ev o0 (fun v : Fin N => decide (v = p1)) = true →
    (∀ r ∈ L i0, r ≠ p0 → r ≠ p1 → ev o0 (fun v : Fin N => decide (v ∉ L i0 ∨ v = r)) = true) →
    ∀ St : ℕ → Fin N → Prop,
    (∀ (w : ℕ) (p : Fin N), St w p ↔ ∀ Zs : Set ℕ, w ∈ Zs → (∀ k : Fin gates.length, N + (k : ℕ) ∈ Zs → (gates.get k).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ e ∈ (gates.get k).inputs, e ∈ Zs) → (p : ℕ) ∈ Zs) →
    ∀ UB : ℕ → Finset (Finset (Fin N)),
    (∀ (j : ℕ) (b : Finset (Fin N)), b ∈ UB j ↔ ((∃ r ∈ L i0, ∀ r' : Fin N, r' ∈ b ↔ (r' ∈ L i0 ∧ ∀ X : Finset (Fin N), (∀ i : Fin gates.length, (i : ℕ) < j → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ev (N + (i : ℕ)) (fun v : Fin N => decide (v ∉ L i0)) = false →
          ∀ s ∈ L i0, ∀ s' ∈ L i0, St (N + (i : ℕ)) s → St (N + (i : ℕ)) s' → (s ∈ X ↔ s' ∈ X)) → (r ∈ X ↔ r' ∈ X))) ∧
        p0 ∉ b ∧ p1 ∉ b ∧ ∀ i : Fin gates.length, (i : ℕ) < j → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ev (N + (i : ℕ)) (fun v : Fin N => decide (v ∉ L i0)) = false →
        (ev (N + (i : ℕ)) (fun v : Fin N => decide (v = p0)) = true ∨ ev (N + (i : ℕ)) (fun v : Fin N => decide (v = p1)) = true) → ∀ s ∈ b, ¬ St (N + (i : ℕ)) s)) →
    ∀ Xs : Finset (Fin gates.length), (∀ g : Fin gates.length, g ∈ Xs ↔ ((gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ev (N + (g : ℕ)) (fun v : Fin N => decide (v ∉ L i0)) = false ∧ (∀ t : Fin N, t ≠ i0 → ev (N + (g : ℕ)) (fun v : Fin N => decide (v ∉ L t)) = true) ∧
        ¬ ∀ e ∈ (gates.get g).inputs, (ev e (fun v : Fin N => decide (v = p0)) = true ∨ ev e (fun v : Fin N => decide (v = p1)) = true))) →
      (∀ j : Fin gates.length, (UB ((j : ℕ) + 1)).card ≤ (UB j).card ∧ (UB j).card ≤ (UB ((j : ℕ) + 1)).card + 1 ∧
        (j ∉ Xs → (UB j).card = (UB ((j : ℕ) + 1)).card)) ∧
      (UB 0).card = q - 1 ∧ q - 1 ≤ Xs.card + (UB gates.length).card := by
  classical
  intro q N L i0 p0 p1 _ _ hSize hLines _ h01 hp0 hp1 gates hG _ hBack ev hEv o0 _ _ _ _
    St hSt UB hUB Xs hXs
  have hValue : ev = fun w x => PEqualNP.Outside.L_meta_1641.value ⟨gates, 0⟩ x w := by
    funext w x
    exact hEv w x
  subst ev
  have hReach : St = fun w (p : Fin N) => PEqualNP.Outside.L_meta_1641.Reaches N gates w (p : ℕ) := by
    funext w p
    exact propext (hSt w p)
  subst St
  let S := L i0
  let computed (j : ℕ) := PEqualNP.Outside.L_meta_1641.Unanchored S
    (PEqualNP.Outside.L_meta_1641.MergesAt gates S j)
    (PEqualNP.Outside.L_meta_1641.AnchorsAt gates S p0 p1 j)
  have hComputed (j : ℕ) : UB j = computed j := by
    ext b
    rw [hUB j b, PEqualNP.Outside.L_meta_1641.mem_unanchored]
    have hClass (r : Fin N) :
        (∀ r' : Fin N, r' ∈ b ↔ (r' ∈ S ∧ ∀ X : Finset (Fin N),
          (∀ k : Fin gates.length, (k : ℕ) < j →
            (gates.get k).op = PEqualNP.CircuitLowerBounds.GateOp.or →
            PEqualNP.Outside.L_meta_1641.Cold gates S (N + (k : ℕ)) →
            ∀ s ∈ S, ∀ s' ∈ S, PEqualNP.Outside.L_meta_1641.Reaches N gates (N + (k : ℕ)) s →
              PEqualNP.Outside.L_meta_1641.Reaches N gates (N + (k : ℕ)) s' →
                (s ∈ X ↔ s' ∈ X)) → (r ∈ X ↔ r' ∈ X))) ↔
        b = PEqualNP.Outside.L_meta_1641.Block S (PEqualNP.Outside.L_meta_1641.MergesAt gates S j) r := by
      constructor
      · intro h
        ext p
        rw [h p]
        simp only [PEqualNP.Outside.L_meta_1641.mem_block, PEqualNP.Outside.L_meta_1641.Related,
          ← PEqualNP.Outside.L_meta_1641.stable_equivalence]
      · intro h p
        rw [h]
        simp only [PEqualNP.Outside.L_meta_1641.mem_block, PEqualNP.Outside.L_meta_1641.Related,
          ← PEqualNP.Outside.L_meta_1641.stable_equivalence]
    have hSubset {r : Fin N} (h : b = PEqualNP.Outside.L_meta_1641.Block S
        (PEqualNP.Outside.L_meta_1641.MergesAt gates S j) r) : b ⊆ S := by
      intro p hp
      rw [h] at hp
      exact (PEqualNP.Outside.L_meta_1641.mem_block.mp hp).1
    constructor
    · rintro ⟨⟨r, hr, hrClass⟩, hMarks⟩
      have he := (hClass r).mp hrClass
      exact ⟨r, hr, he, (PEqualNP.Outside.L_meta_1641.disjoint_anchors (hSubset he)).mpr hMarks⟩
    · rintro ⟨r, hr, he, hMarks⟩
      exact ⟨⟨r, hr, (hClass r).mpr he⟩,
        (PEqualNP.Outside.L_meta_1641.disjoint_anchors (hSubset he)).mp hMarks⟩
  have hLocal (j : Fin gates.length) :
      (UB ((j : ℕ) + 1)).card ≤ (UB j).card ∧
      (UB j).card ≤ (UB ((j : ℕ) + 1)).card + 1 ∧
      (j ∉ Xs → (UB j).card = (UB ((j : ℕ) + 1)).card) := by
    rw [hComputed (j : ℕ), hComputed ((j : ℕ) + 1)]
    have h := PEqualNP.Outside.L_meta_1641.gate_keeps_count hLines hp0 hp1 hG hBack j
    refine ⟨h.1, h.2.1, fun hn => h.2.2 ?_⟩
    intro he
    refine hn ((hXs j).mpr ⟨he.1, he.2.1, ?_, he.2.2.2⟩)
    intro t hti
    exact Bool.eq_true_of_not_eq_false (he.2.2.1 t hti)
  have hStart : (UB 0).card = q - 1 := by
    rw [hComputed 0]
    have h := PEqualNP.Outside.L_meta_1641.initial_blocks
      (gates := gates) h01 hp0 hp1
    change (computed 0).card = (L i0).card - 2 at h
    rw [h, hSize i0]
    omega
  refine ⟨hLocal, hStart, ?_⟩
  rw [← hStart]
  exact PEqualNP.Outside.L_meta_1641.count_losses (fun k => (UB k).card) Xs
    (fun j => (hLocal j).2.1) (fun j => (hLocal j).2.2)
