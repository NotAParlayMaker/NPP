import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_12408_aux

open PEqualNP.CircuitLowerBounds
open Relation

abbrev Input := Fin 14
abbrev Output := Fin 4
abbrev Support := Finset Input

def goal (i : Output) : Support := Finset.univ.filter fun p : Input => (p.val + 1).testBit i.val

def bits (p : Input) : Finset Output :=
  Finset.univ.filter fun i : Output => (p.val + 1).testBit i.val

theorem mem_goal (p : Input) (i : Output) : p ∈ goal i ↔ i ∈ bits p := by
  simp [goal, bits]

theorem distinct_goals : ∀ i j, goal i ⊆ goal j → i = j := by decide

theorem all_goals_large : ∀ i, 1 < (goal i).card := by decide

theorem bits_nonempty : ∀ p, (bits p).Nonempty := by decide

theorem pair_bits_inj :
    ∀ p q, (bits p).card = 2 → bits p = bits q → p = q := by decide

theorem inter_two :
    ∀ p q : Input, p ≠ q → ((bits p) ∩ (bits q)).card ≤ 2 := by decide

def pairInputs : Finset Input := Finset.univ.filter fun p => (bits p).card = 2

def tripleInputs : Finset Input := Finset.univ.filter fun p => (bits p).card = 3

theorem pair_card : pairInputs.card = 6 := by decide

theorem triple_card : tripleInputs.card = 4 := by decide

section Count

variable (A : Finset Support) (l r : Support → Support)

def Edge (u v : Support) : Prop := v ∈ A ∧ 1 < v.card ∧ (u = l v ∨ u = r v)

noncomputable def targets (v : Support) : Finset Output := by
  classical
  exact Finset.univ.filter fun i => ReflTransGen (Edge A l r) v (goal i)

theorem mem_targets (v : Support) (i : Output) :
    i ∈ targets A l r v ↔ ReflTransGen (Edge A l r) v (goal i) := by
  classical
  simp [targets]

noncomputable def live : Finset Support := by
  classical
  exact A.filter fun v => (targets A l r v).Nonempty

noncomputable def internal : Finset Support := by
  classical
  exact (live A l r).filter fun v => 1 < v.card

noncomputable def nexts (v : Support) : Finset Support := by
  classical
  exact (internal A l r).filter fun w => v = l w ∨ v = r w

def endpoints (v : Support) : Finset Output := Finset.univ.filter (fun i => v = goal i)

noncomputable def degree (v : Support) : ℕ :=
  (nexts A l r v).card + (endpoints v).card

variable (hdecomp : ∀ v ∈ A, 1 < v.card →
  l v ∈ A ∧ r v ∈ A ∧ l v ⊂ v ∧ r v ⊂ v ∧ l v ∪ r v = v)
variable (hinputs : ∀ p : Input, {p} ∈ A)
variable (hgoals : ∀ i, goal i ∈ A)
variable (hempty : ∅ ∉ A)

include hdecomp in
theorem edge_ssubset {u v : Support} (e : Edge A l r u v) : u ⊂ v := by
  obtain ⟨_, _, hl, hr, _⟩ := hdecomp v e.1 e.2.1
  rcases e.2.2 with h | h
  · simpa [h] using hl
  · simpa [h] using hr

include hdecomp in
theorem reach_subset {u v : Support} (h : ReflTransGen (Edge A l r) u v) : u ⊆ v := by
  induction h with
  | refl => exact fun _ h => h
  | tail _ e ih => exact ih.trans (edge_ssubset A l r hdecomp e).subset

include hdecomp in
theorem reach_singleton (v : Support) (hA : v ∈ A) (p : Input) (hp : p ∈ v) :
    ReflTransGen (Edge A l r) {p} v := by
  induction v using Finset.strongInductionOn with
  | _ v ih =>
    by_cases hcard : 1 < v.card
    · obtain ⟨hlA, hrA, hl, hr, hunion⟩ := hdecomp v hA hcard
      rw [← hunion, Finset.mem_union] at hp
      rcases hp with hp | hp
      · exact (ih (l v) hl hlA hp).tail ⟨hA, hcard, Or.inl rfl⟩
      · exact (ih (r v) hr hrA hp).tail ⟨hA, hcard, Or.inr rfl⟩
    · have heq : v = {p} := by
        apply Finset.Subset.antisymm _ (Finset.singleton_subset_iff.mpr hp)
        intro x hx
        exact Finset.mem_singleton.mpr (Finset.card_le_one.mp (Nat.le_of_not_gt hcard) x hx p hp)
      subst v
      exact .refl

include hdecomp hgoals in
theorem targets_singleton (p : Input) : targets A l r {p} = bits p := by
  ext i
  rw [mem_targets, ← mem_goal]
  exact ⟨fun h => reach_subset A l r hdecomp h (by simp),
    fun h => reach_singleton A l r hdecomp _ (hgoals i) p h⟩

include hdecomp in
theorem connected_targets (v : Support) (hv : 1 < v.card) :
    (targets A l r v).card ≤ 2 := by
  obtain ⟨p, q, hp, hq, hpq⟩ := Finset.one_lt_card_iff.mp hv
  have sub : targets A l r v ⊆ bits p ∩ bits q := by
    intro i hi
    have h := reach_subset A l r hdecomp ((mem_targets A l r v i).mp hi)
    exact Finset.mem_inter.mpr ⟨(mem_goal p i).mp (h hp), (mem_goal q i).mp (h hq)⟩
  exact (Finset.card_le_card sub).trans (inter_two p q hpq)

theorem targets_mono {v w : Support} (e : Edge A l r v w) :
    targets A l r w ⊆ targets A l r v := by
  intro i hi
  rw [mem_targets] at hi ⊢
  exact ReflTransGen.head e hi

include hdecomp in
theorem endpoint_target {v : Support} {i : Output} (h : v = goal i) :
    targets A l r v = {i} := by
  rw [h]
  ext j
  rw [mem_targets, Finset.mem_singleton]
  exact ⟨fun ht => (distinct_goals i j (reach_subset A l r hdecomp ht)).symm,
    fun hj => hj ▸ ReflTransGen.refl⟩

theorem mem_live {v : Support} :
    v ∈ live A l r ↔ v ∈ A ∧ (targets A l r v).Nonempty := by
  classical
  simp [live]

theorem mem_internal {v : Support} :
    v ∈ internal A l r ↔ v ∈ live A l r ∧ 1 < v.card := by
  classical
  simp [internal]

theorem mem_nexts {v w : Support} :
    w ∈ nexts A l r v ↔ w ∈ internal A l r ∧ (v = l w ∨ v = r w) := by
  classical
  simp [nexts]

include hdecomp hinputs hgoals in
theorem live_singleton (p : Input) : {p} ∈ live A l r := by
  rw [mem_live, targets_singleton A l r hdecomp hgoals p]
  exact ⟨hinputs p, bits_nonempty p⟩

include hgoals in
theorem live_goal (i : Output) : goal i ∈ live A l r :=
  (mem_live A l r).mpr ⟨hgoals i, ⟨i, (mem_targets A l r _ _).mpr .refl⟩⟩

include hdecomp in
theorem live_child {v w : Support} (e : Edge A l r v w) (hw : w ∈ live A l r) :
    v ∈ live A l r := by
  obtain ⟨hl, hr, _, _, _⟩ := hdecomp w e.1 e.2.1
  have hv : v ∈ A := e.2.2.elim (· ▸ hl) (· ▸ hr)
  obtain ⟨i, hi⟩ := ((mem_live A l r).mp hw).2
  exact (mem_live A l r).mpr ⟨hv, i, targets_mono A l r e hi⟩

theorem next_or_end {v : Support} {i : Output} (hi : i ∈ targets A l r v) :
    v = goal i ∨ ∃ w ∈ nexts A l r v, i ∈ targets A l r w := by
  rcases ((mem_targets A l r v i).mp hi).cases_head with he | ⟨w, edge, h⟩
  · exact Or.inl he
  · have hi' : i ∈ targets A l r w := (mem_targets A l r w i).mpr h
    have hw : w ∈ live A l r := (mem_live A l r).mpr ⟨edge.1, i, hi'⟩
    exact Or.inr ⟨w, (mem_nexts A l r).mpr ⟨(mem_internal A l r).mpr ⟨hw, edge.2.1⟩,
      edge.2.2⟩, hi'⟩

theorem degree_pos {v : Support} (hv : v ∈ live A l r) : 1 ≤ degree A l r v := by
  obtain ⟨i, hi⟩ := ((mem_live A l r).mp hv).2
  rcases next_or_end A l r hi with h | ⟨w, hw, _⟩
  · have hpos : 0 < (endpoints v).card :=
      Finset.card_pos.mpr ⟨i, by simp [endpoints, h]⟩
    unfold degree
    omega
  · have hpos : 0 < (nexts A l r v).card := Finset.card_pos.mpr ⟨w, hw⟩
    unfold degree
    omega

include hdecomp in
theorem empty_endpoints {v : Support} (h : 2 ≤ (targets A l r v).card) : endpoints v = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  have he : v = goal i := (Finset.mem_filter.mp hi).2
  rw [endpoint_target A l r hdecomp he, Finset.card_singleton] at h
  omega

include hdecomp in
theorem branch_of_small_children {v : Support}
    (h : 2 ≤ (targets A l r v).card)
    (hsmall : ∀ w ∈ nexts A l r v, (targets A l r w).card ≤ 1) :
    2 ≤ degree A l r v := by
  obtain ⟨i, j, hi, hj, hij⟩ := Finset.one_lt_card_iff.mp (show 1 < _ from h)
  have get_next : ∀ k ∈ targets A l r v, ∃ w ∈ nexts A l r v, k ∈ targets A l r w := by
    intro k hk
    rcases next_or_end A l r hk with he | hn
    · have hm : k ∈ endpoints v := by simp [endpoints, he]
      rw [empty_endpoints A l r hdecomp h] at hm
      simp at hm
    · exact hn
  obtain ⟨u, hu, hiu⟩ := get_next i hi
  obtain ⟨w, hw, hjw⟩ := get_next j hj
  have different : u ≠ w := by
    intro he
    subst w
    exact hij (Finset.card_le_one.mp (hsmall u hu) i hiu j hjw)
  have card : 1 < (nexts A l r v).card := Finset.one_lt_card_iff.mpr ⟨u, w, hu, hw, different⟩
  unfold degree
  omega

include hdecomp in
theorem branch_pair {v : Support} (hv : v ∈ live A l r)
    (htwo : (targets A l r v).card = 2) :
    ∃ w ∈ live A l r, targets A l r w = targets A l r v ∧ 2 ≤ degree A l r w := by
  classical
  let T := targets A l r v
  let candidates := (live A l r).filter fun w => targets A l r w = T
  have hn : candidates.Nonempty := ⟨v, Finset.mem_filter.mpr ⟨hv, rfl⟩⟩
  obtain ⟨w, hw, hmax⟩ := Finset.exists_max_image candidates Finset.card hn
  have hw' := Finset.mem_filter.mp hw
  refine ⟨w, hw'.1, hw'.2, branch_of_small_children A l r hdecomp (by rw [hw'.2]; change 2 ≤ (targets A l r v).card; omega) ?_⟩
  intro u hu
  by_contra! hnu
  have hu' := (mem_nexts A l r).mp hu
  have hu'' := (mem_internal A l r).mp hu'.1
  have edge : Edge A l r w u := ⟨((mem_live A l r).mp hu''.1).1, hu''.2, hu'.2⟩
  have sub := targets_mono A l r edge
  have he : targets A l r u = targets A l r w := by
    apply Finset.eq_of_subset_of_card_le sub
    rw [hw'.2]
    change (targets A l r v).card ≤ _
    omega
  have huC : u ∈ candidates := Finset.mem_filter.mpr ⟨hu''.1, he.trans hw'.2⟩
  exact (Nat.not_lt_of_ge (hmax u huC)) (Finset.card_lt_card (edge_ssubset A l r hdecomp edge))

include hdecomp in
theorem branch_triple {v : Support} (hv : (targets A l r v).card = 3) :
    2 ≤ degree A l r v := by
  by_contra! hsmall
  have hadd : (nexts A l r v).card ≤ 1 := by
    unfold degree at hsmall
    omega
  obtain ⟨i, hi⟩ := Finset.card_pos.mp (show 0 < (targets A l r v).card by omega)
  have get_next : ∀ k ∈ targets A l r v, ∃ w ∈ nexts A l r v, k ∈ targets A l r w := by
    intro k hk
    rcases next_or_end A l r hk with he | hn
    · have hm : k ∈ endpoints v := by simp [endpoints, he]
      rw [empty_endpoints A l r hdecomp (by omega)] at hm
      simp at hm
    · exact hn
  obtain ⟨w, hw, _⟩ := get_next i hi
  have sub : targets A l r v ⊆ targets A l r w := by
    intro j hj
    obtain ⟨u, hu, h⟩ := get_next j hj
    exact (Finset.card_le_one.mp hadd u hu w hw) ▸ h
  have le := Finset.card_le_card sub
  have two := connected_targets A l r hdecomp w
    ((mem_internal A l r).mp ((mem_nexts A l r).mp hw).1).2
  omega

include hdecomp hinputs hgoals in
include hdecomp hinputs hgoals in
theorem branching_count :
    10 ≤ ((live A l r).filter fun v => 2 ≤ degree A l r v).card := by
  classical
  let B := (live A l r).filter fun v => 2 ≤ degree A l r v
  have choose_pair (p : ↥pairInputs) :
      ∃ w ∈ B, targets A l r w = bits p.val := by
    have hc : (bits p.val).card = 2 := (Finset.mem_filter.mp p.property).2
    obtain ⟨w, hw, he, hd⟩ := branch_pair A l r hdecomp
      (live_singleton A l r hdecomp hinputs hgoals p.val)
      (by rw [targets_singleton A l r hdecomp hgoals]; exact hc)
    exact ⟨w, Finset.mem_filter.mpr ⟨hw, hd⟩, he.trans (targets_singleton A l r hdecomp hgoals _)⟩
  let choose (p : ↥pairInputs) := Classical.choose (choose_pair p)
  have choose_spec (p : ↥pairInputs) : choose p ∈ B ∧ targets A l r (choose p) = bits p.val :=
    Classical.choose_spec (choose_pair p)
  have inj : Function.Injective choose := by
    intro p q he
    apply Subtype.ext
    apply pair_bits_inj p.val q.val (Finset.mem_filter.mp p.property).2
    rw [← (choose_spec p).2, ← (choose_spec q).2, he]
  let P := pairInputs.attach.image choose
  have hP : P.card = 6 := by
    rw [Finset.card_image_of_injective _ inj, Finset.card_attach, pair_card]
  have hPB : P ⊆ B := by
    intro w hw
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hw
    exact (choose_spec p).1
  let Q := tripleInputs.image fun p => ({p} : Support)
  have hQ : Q.card = 4 := by
    rw [Finset.card_image_of_injective _ (fun _ _ h => Finset.singleton_injective h), triple_card]
  have hQB : Q ⊆ B := by
    intro w hw
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hw
    have hc : (bits p).card = 3 := (Finset.mem_filter.mp hp).2
    have ht : (targets A l r {p}).card = 3 := by
      rw [targets_singleton A l r hdecomp hgoals]; exact hc
    exact Finset.mem_filter.mpr ⟨live_singleton A l r hdecomp hinputs hgoals p,
      branch_triple A l r hdecomp ht⟩
  have disjoint : Disjoint P Q := by
    refine Finset.disjoint_left.mpr ?_
    intro w hw hq
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨q, hq', eq⟩ := Finset.mem_image.mp hq
    have a := (Finset.mem_filter.mp p.property).2
    have b := (Finset.mem_filter.mp hq').2
    rw [← (choose_spec p).2, ← eq, targets_singleton A l r hdecomp hgoals] at a
    omega
  have le := Finset.card_le_card (Finset.union_subset hPB hQB)
  rw [Finset.card_union_of_disjoint disjoint, hP, hQ] at le
  exact le

include hdecomp hinputs hgoals hempty in
include hdecomp hinputs hgoals hempty in
theorem live_card :
    (live A l r).card = (internal A l r).card + 14 := by
  classical
  have parts := Finset.card_filter_add_card_filter_not (s := live A l r) (fun v => 1 < v.card)
  have hsingle : ((live A l r).filter fun v => ¬ 1 < v.card) =
      Finset.univ.image (fun p : Input => ({p} : Support)) := by
    ext v
    constructor
    · intro hv
      obtain ⟨hl, hs⟩ := Finset.mem_filter.mp hv
      have hn : v.Nonempty := by
        by_contra! hn
        exact hempty (hn ▸ ((mem_live A l r).mp hl).1)
      have hc : v.card = 1 := by
        have := Finset.card_pos.mpr hn
        omega
      obtain ⟨p, rfl⟩ := Finset.card_eq_one.mp hc
      exact Finset.mem_image.mpr ⟨p, Finset.mem_univ p, rfl⟩
    · intro hv
      obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hv
      exact Finset.mem_filter.mpr ⟨live_singleton A l r hdecomp hinputs hgoals p, by simp⟩
  rw [hsingle, Finset.card_image_of_injective _ (fun _ _ h => Finset.singleton_injective h)] at parts
  simpa [internal] using parts.symm

include hdecomp in
include hdecomp in
theorem sum_nexts :
    (∑ v ∈ live A l r, (nexts A l r v).card) = 2 * (internal A l r).card := by
  classical
  calc
    _ = ∑ v ∈ live A l r, ∑ w ∈ internal A l r, if v = l w ∨ v = r w then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro v _
      rw [Finset.sum_boole]
      rfl
    _ = ∑ w ∈ internal A l r, ∑ v ∈ live A l r, if v = l w ∨ v = r w then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ _ ∈ internal A l r, 2 := by
      apply Finset.sum_congr rfl
      intro w hw
      have hw' := (mem_internal A l r).mp hw
      have wA := ((mem_live A l r).mp hw'.1).1
      obtain ⟨_, _, leftsmall, _, union⟩ := hdecomp w wA hw'.2
      have hl := live_child A l r hdecomp ⟨wA, hw'.2, Or.inl rfl⟩ hw'.1
      have hr := live_child A l r hdecomp ⟨wA, hw'.2, Or.inr rfl⟩ hw'.1
      have ne : l w ≠ r w := by
        intro h
        rw [← h, Finset.union_self] at union
        exact (ne_of_lt leftsmall) union
      have filtered : ((live A l r).filter fun v => v = l w ∨ v = r w) = {l w, r w} := by
        ext v
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        exact ⟨And.right, fun h => ⟨h.elim (· ▸ hl) (· ▸ hr), h⟩⟩
      rw [Finset.sum_boole, filtered]
      simp [ne]
    _ = _ := by simp [Nat.mul_comm]

include hgoals in
include hgoals in
theorem sum_endpoints :
    (∑ v ∈ live A l r, (endpoints v).card) = 4 := by
  classical
  calc
    _ = ∑ v ∈ live A l r, ∑ i : Output, if v = goal i then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro v _
      rw [Finset.sum_boole]
      rfl
    _ = ∑ i : Output, ∑ v ∈ live A l r, if v = goal i then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ _ : Output, 1 := by
      apply Finset.sum_congr rfl
      intro i _
      have filtered : ((live A l r).filter fun v => v = goal i) = {goal i} := by
        ext v
        simp [and_iff_right_of_imp (fun (h : v = goal i) => h ▸ live_goal A l r hgoals i)]
      rw [Finset.sum_boole, filtered]
      simp
    _ = _ := by simp

include hdecomp hinputs hgoals hempty in
include hdecomp hinputs hgoals hempty in
theorem enough_internal : 20 ≤ (internal A l r).card := by
  classical
  have branches := branching_count A l r hdecomp hinputs hgoals
  have hc := live_card A l r hdecomp hinputs hgoals hempty
  have count : (∑ v ∈ live A l r, degree A l r v) = 2 * (internal A l r).card + 4 := by
    unfold degree
    rw [Finset.sum_add_distrib, sum_nexts A l r hdecomp, sum_endpoints A l r hgoals]
  have lower : (live A l r).card +
      ((live A l r).filter fun v => 2 ≤ degree A l r v).card ≤
      ∑ v ∈ live A l r, degree A l r v := by
    calc
      _ = ∑ v ∈ live A l r, (1 + if 2 ≤ degree A l r v then 1 else 0) := by
        rw [Finset.sum_add_distrib, Finset.sum_boole]
        simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro v hv
        have h := degree_pos A l r hv
        split <;> omega
  omega

end Count


def pushMask (S : List Support) (g : Gate) : Support :=
  g.inputs.foldr (fun i t => S.getD i ∅ ∪ t) ∅

def encode (p : Input) (s : Support) : Bool := decide (p ∈ s)

theorem readMask (p : Input) (S : List Support) (i : ℕ) :
    (S.map (encode p)).getD i false = encode p (S.getD i ∅) := by
  simpa only [encode, Finset.notMem_empty, decide_false] using
    (List.getD_map (l := S) (d := (∅ : Support)) (n := i) (encode p))

theorem encode_push (p : Input) (S : List Support) (g : Gate) (hg : g.op = .or) :
    encode p (pushMask S g) =
      g.op.eval (g.inputs.map fun i => (S.map (encode p)).getD i false) := by
  rw [hg]
  change encode p (g.inputs.foldr (fun i t => S.getD i ∅ ∪ t) ∅) =
    (g.inputs.map fun i => (S.map (encode p)).getD i false).any id
  generalize g.inputs = ix
  induction ix with
  | nil => simp [encode]
  | cons i ix ih =>
    have e (a b : Support) : encode p (a ∪ b) = (encode p a || encode p b) := by
      simp [encode, Finset.mem_union]
    simp only [List.foldr_cons, List.map_cons, List.any_cons, id_eq]
    rw [e, readMask, ih]

def maskFold (gs : List Gate) (S : List Support) : List Support :=
  gs.foldl (fun w g => w ++ [pushMask w g]) S

theorem fold_correct (p : Input) (gs : List Gate) (S : List Support)
    (hor : ∀ g ∈ gs, g.op = .or) :
    (maskFold gs S).map (encode p) = gs.foldl
      (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (S.map (encode p)) := by
  induction gs generalizing S with
  | nil => rfl
  | cons g gs ih =>
    rw [maskFold, List.foldl_cons, List.foldl_cons]
    change (maskFold gs (S ++ [pushMask S g])).map (encode p) = _
    rw [ih _ (fun g' hg' => hor g' (List.mem_cons_of_mem _ hg')), List.map_append]
    simp only [List.map_cons, List.map_nil, encode_push p S g (hor g (by simp))]

def initial : List Support := List.ofFn (fun p : Input => {p})

def masks (C : Circuit) : List Support := maskFold C.gates initial

theorem masks_correct (C : Circuit) (hor : ∀ g ∈ C.gates, g.op = .or) (p : Input) :
    (masks C).map (encode p) = C.wires (List.ofFn (fun q : Input => decide (q = p))) := by
  rw [masks, fold_correct p C.gates initial hor]
  simp [Circuit.wires, initial, encode, eq_comm]

theorem read_in (S : List Support) (i : ℕ) :
    S.getD i ∅ = ∅ ∨ S.getD i ∅ ∈ S := by
  by_cases h : i < S.length
  · have el := List.getD_eq_getElem (l := S) (d := (∅ : Support)) h
    exact Or.inr (el.symm ▸ List.getElem_mem h)
  · exact Or.inl (List.getD_eq_default _ _ (Nat.le_of_not_gt h))

def Invariant (S : List Support) : Prop :=
  ∀ v ∈ S, 1 < v.card → ∃ a ∈ S, ∃ b ∈ S, a ⊂ v ∧ b ⊂ v ∧ a ∪ b = v

theorem invariant_extend (S : List Support) (hS : Invariant S)
    (a b : Support) (ha : a = ∅ ∨ a ∈ S) (hb : b = ∅ ∨ b ∈ S) :
    Invariant (S ++ [a ∪ b]) := by
  intro v hv hc
  have inherit : v ∈ S → ∃ x ∈ S ++ [a ∪ b], ∃ y ∈ S ++ [a ∪ b],
      x ⊂ v ∧ y ⊂ v ∧ x ∪ y = v := by
    intro h
    obtain ⟨x, hx, y, hy, rest⟩ := hS v h hc
    exact ⟨x, List.mem_append_left _ hx, y, List.mem_append_left _ hy, rest⟩
  rw [List.mem_append, List.mem_singleton] at hv
  rcases hv with hv | rfl
  · exact inherit hv
  by_cases ea : a = a ∪ b
  · have ha' : a ∈ S := ha.resolve_left (by
      intro e; rw [← ea, e, Finset.card_empty] at hc; omega)
    exact inherit (ea ▸ ha')
  by_cases eb : b = a ∪ b
  · have hb' : b ∈ S := hb.resolve_left (by
      intro e; rw [← eb, e, Finset.card_empty] at hc; omega)
    exact inherit (eb ▸ hb')
  have ha' : a ∈ S := ha.resolve_left (fun e => eb (by simp [e]))
  have hb' : b ∈ S := hb.resolve_left (fun e => ea (by simp [e]))
  exact ⟨a, List.mem_append_left _ ha', b, List.mem_append_left _ hb',
    Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_union_left, ea⟩,
    Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_union_right, eb⟩, rfl⟩

theorem input_pair (S : List Support) (g : Gate) (h : g.inputs.length ≤ 2) :
    ∃ a b, (a = ∅ ∨ a ∈ S) ∧ (b = ∅ ∨ b ∈ S) ∧ a ∪ b = pushMask S g := by
  unfold pushMask
  generalize g.inputs = ix at h ⊢
  rcases ix with _ | ⟨i, _ | ⟨j, _ | ⟨k, rest⟩⟩⟩
  · exact ⟨∅, ∅, Or.inl rfl, Or.inl rfl, by simp⟩
  · exact ⟨S.getD i ∅, ∅, read_in S i, Or.inl rfl, rfl⟩
  · exact ⟨S.getD i ∅, S.getD j ∅, read_in S i, read_in S j, by simp⟩
  · simp at h

theorem fold_invariant (gs : List Gate) (S : List Support) (hS : Invariant S)
    (hb : ∀ g ∈ gs, g.inputs.length ≤ 2) : Invariant (maskFold gs S) := by
  induction gs generalizing S with
  | nil => exact hS
  | cons g gs ih =>
    obtain ⟨a, b, ha, hg, he⟩ := input_pair S g (hb g (by simp))
    change Invariant (maskFold gs (S ++ [pushMask S g]))
    rw [← he]
    exact ih _ (invariant_extend S hS a b ha hg)
      (fun g' hg' => hb g' (List.mem_cons_of_mem _ hg'))

theorem initial_invariant : Invariant initial := by
  intro v hv hc
  obtain ⟨p, rfl⟩ := List.mem_ofFn.mp hv
  simp at hc

theorem fold_len (gs : List Gate) (S : List Support) :
    (maskFold gs S).length = S.length + gs.length := by
  induction gs generalizing S with
  | nil => simp [maskFold]
  | cons g gs ih =>
    change (maskFold gs (S ++ [pushMask S g])).length = _
    rw [ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

theorem in_fold (gs : List Gate) (S : List Support) (v : Support) (h : v ∈ S) :
    v ∈ maskFold gs S := by
  induction gs generalizing S with
  | nil => exact h
  | cons g gs ih =>
    exact ih (S ++ [pushMask S g]) (List.mem_append_left _ h)

theorem circuits_large (C : Circuit)
    (hgood : ∀ g ∈ C.gates, g.op = GateOp.or ∧ g.inputs.length ≤ 2)
    (h : ∀ i : Output, ∃ w : ℕ, ∀ p : Input,
      (C.wires (List.ofFn (fun q : Input => decide (q = p)))).getD w false =
        (p.val + 1).testBit i.val) : 20 ≤ C.size := by
  classical
  let W := masks C
  let A := W.toFinset.erase ∅
  have belongs (v : Support) : v ∈ A ↔ v ≠ ∅ ∧ v ∈ W := by
    simp [A]
  have inv : Invariant W :=
    fold_invariant C.gates initial initial_invariant (fun g hg => (hgood g hg).2)
  have hinputs : ∀ p : Input, {p} ∈ A := by
    intro p
    apply (belongs _).mpr
    exact ⟨by simp, in_fold C.gates initial {p} (List.mem_ofFn.mpr ⟨p, rfl⟩)⟩
  have hgoals : ∀ i, goal i ∈ A := by
    intro i
    obtain ⟨w, hw⟩ := h i
    have he : W.getD w ∅ = goal i := by
      ext p
      have he' : encode p (W.getD w ∅) = (p.val + 1).testBit i.val := by
        rw [← readMask]
        change ((masks C).map (encode p)).getD w false = _
        rw [masks_correct C (fun g hg => (hgood g hg).1), hw]
      simpa [encode, goal] using iff_of_eq (congrArg (· = true) he')
    have ne : goal i ≠ ∅ := by
      have large := all_goals_large i
      intro eq
      simp [eq] at large
    exact (belongs _).mpr ⟨ne, he ▸ (read_in W w).resolve_left (fun eq => ne (he.symm.trans eq))⟩
  have decomp : ∀ v, ∃ a b, v ∈ A ∧ 1 < v.card →
      a ∈ A ∧ b ∈ A ∧ a ⊂ v ∧ b ⊂ v ∧ a ∪ b = v := by
    intro v
    by_cases hv : v ∈ A ∧ 1 < v.card
    · obtain ⟨a, ha, b, hb, sa, sb, eq⟩ := inv v ((belongs v).mp hv.1).2 hv.2
      have ha' : a ≠ ∅ := by
        intro e
        have : b = v := by simpa [e] using eq
        exact (ne_of_lt sb) this
      have hb' : b ≠ ∅ := by
        intro e
        have : a = v := by simpa [e] using eq
        exact (ne_of_lt sa) this
      exact ⟨a, b, fun _ => ⟨(belongs _).mpr ⟨ha', ha⟩, (belongs _).mpr ⟨hb', hb⟩, sa, sb, eq⟩⟩
    · exact ⟨∅, ∅, fun h' => (hv h').elim⟩
  choose l r parts using decomp
  have hdecomp := fun v hv hc => parts v ⟨hv, hc⟩
  have hempty : ∅ ∉ A := by simp [A]
  have lower := enough_internal A l r hdecomp hinputs hgoals hempty
  have card := live_card A l r hdecomp hinputs hgoals hempty
  have sub : live A l r ⊆ W.toFinset := by
    intro v hv
    exact (List.mem_toFinset).mpr ((belongs v).mp ((mem_live A l r).mp hv).1).2
  have upper := (Finset.card_le_card sub).trans (List.toFinset_card_le W)
  have len : W.length = 14 + C.size := by
    change (maskFold C.gates initial).length = _
    simp [fold_len, initial, Circuit.size]
  omega

end PEqualNP.Outside.L_meta_12408_aux

theorem PEqualNP.Outside.L_meta_12408 : (¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, (∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ g.inputs.length ≤ 2) ∧ C.size ≤ 19 ∧ ∀ v : Fin 4, ∃ w : ℕ, ∀ p : Fin 14, (C.wires (List.ofFn (fun q : Fin 14 => decide (q = p)))).getD w false = Nat.testBit (p.val + 1) v.val)) := by
  rintro ⟨C, good, size, works⟩
  have large := PEqualNP.Outside.L_meta_12408_aux.circuits_large C good works
  omega
