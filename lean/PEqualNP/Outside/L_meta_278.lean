import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.GetD
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_278_aux

open PEqualNP.CircuitLowerBounds

def stepWires (ws : List Bool) (g : Gate) : List Bool :=
  ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]

def runWires (n : ℕ) (gs : List Gate) (x : Fin n → Bool) : List Bool :=
  gs.foldl stepWires (List.ofFn x)

def wireVal (n : ℕ) (gs : List Gate) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (runWires n gs x).getD i false

def wireAt (n : ℕ) (gs : List Gate) (bound i : ℕ) (x : Fin n → Bool) : Bool :=
  if i < bound then wireVal n gs x i else false

lemma foldl_stepWires_length (gs : List Gate) (ws : List Bool) :
    (gs.foldl stepWires ws).length = ws.length + gs.length := by
  induction gs generalizing ws with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, List.length_cons, ih, stepWires, List.length_append]
    simp only [List.length_nil]
    omega

lemma runWires_length (n : ℕ) (gs : List Gate) (x : Fin n → Bool) :
    (runWires n gs x).length = n + gs.length := by
  unfold runWires
  rw [foldl_stepWires_length, List.length_ofFn]

lemma foldl_stepWires_getD_lt (gs : List Gate) (ws : List Bool) {i : ℕ} (hi : i < ws.length) :
    (gs.foldl stepWires ws).getD i false = ws.getD i false := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWires ws g).length := by
      simp only [stepWires, List.length_append, List.length_cons, List.length_nil]
      omega
    rw [ih (stepWires ws g) hlt, List.getD_eq_getElem _ _ hlt, List.getD_eq_getElem _ _ hi]
    simp only [stepWires, List.getElem_append_left hi]

lemma wireVal_input (n : ℕ) (gs : List Gate) (x : Fin n → Bool) (v : Fin n) :
    wireVal n gs x v.val = x v := by
  unfold wireVal runWires
  have hv : v.val < (List.ofFn x).length := by simp
  rw [foldl_stepWires_getD_lt gs (List.ofFn x) hv, List.getD_eq_getElem _ _ hv, List.getElem_ofFn]

lemma wireVal_of_ge (n : ℕ) (gs : List Gate) (x : Fin n → Bool) {i : ℕ} (hi : n + gs.length ≤ i) :
    wireVal n gs x i = false := by
  unfold wireVal
  rw [List.getD_eq_default]
  rw [runWires_length]
  exact hi

lemma wireVal_gate (n : ℕ) (gs : List Gate) (x : Fin n → Bool) {k : ℕ} (hk : k < gs.length) :
    wireVal n gs x (n + k) =
      (gs[k]'hk).op.eval ((gs[k]'hk).inputs.map fun i => wireAt n gs (n + k) i x) := by
  unfold wireVal runWires
  have hsplit : gs = gs.take k ++ (gs[k]'hk) :: gs.drop (k + 1) := by
    simp
  conv_lhs => rw [hsplit, List.foldl_append, List.foldl_cons]
  set ws := (gs.take k).foldl stepWires (List.ofFn x)
  have hws_len : ws.length = n + k := by
    rw [foldl_stepWires_length, List.length_ofFn, List.length_take]
    omega
  have hstep_len : (stepWires ws (gs[k]'hk)).length = n + k + 1 := by
    simp [stepWires, hws_len]
  have hlt : n + k < (stepWires ws (gs[k]'hk)).length := by omega
  rw [foldl_stepWires_getD_lt (gs.drop (k + 1)) (stepWires ws (gs[k]'hk)) hlt]
  have hlast : (stepWires ws (gs[k]'hk)).getD (n + k) false =
      (gs[k]'hk).op.eval ((gs[k]'hk).inputs.map fun i => ws.getD i false) := by
    rw [List.getD_eq_getElem _ _ hlt]
    simp [stepWires, hws_len]
  rw [hlast]
  congr 1
  apply List.map_congr_left
  intro i _
  unfold wireAt
  split_ifs with hi
  · have hi_ws : i < ws.length := by omega
    have hsplit2 : gs = gs.take k ++ gs.drop k := (List.take_append_drop k gs).symm
    symm
    unfold wireVal runWires
    rw [hsplit2, List.foldl_append]
    exact foldl_stepWires_getD_lt (gs.drop k) ws hi_ws
  · rw [List.getD_eq_default]
    omega

lemma gateOp_mono {op : GateOp} (hop : op = GateOp.and ∨ op = GateOp.or)
    {l1 l2 : List Bool} (hlen : l1.length = l2.length)
    (hle : ∀ i (h1 : i < l1.length) (h2 : i < l2.length), l1[i]'h1 = true → l2[i]'h2 = true) :
    op.eval l1 = true → op.eval l2 = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, id_eq]
    intro h1 b hb
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
    have hi1 : i < l1.length := by omega
    exact hle i hi1 hi (h1 _ (List.getElem_mem hi1))
  · simp only [GateOp.eval, List.any_eq_true, id_eq]
    rintro ⟨b, hb, rfl⟩
    obtain ⟨i, hi, hget⟩ := List.getElem_of_mem hb
    have hi2 : i < l2.length := by omega
    refine ⟨l2[i]'hi2, List.getElem_mem hi2, ?_⟩
    exact hle i hi hi2 hget

lemma wireVal_mono (n : ℕ) (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    {x y : Fin n → Bool} (hxy : ∀ v : Fin n, x v = true → y v = true) :
    ∀ i : ℕ, wireVal n gs x i = true → wireVal n gs y i = true := by
  have hgen : ∀ (ws1 ws2 : List Bool), ws1.length = ws2.length →
      (∀ i, ws1.getD i false = true → ws2.getD i false = true) →
      ∀ i, (gs.foldl stepWires ws1).getD i false = true →
           (gs.foldl stepWires ws2).getD i false = true := by
    induction gs with
    | nil =>
      intro ws1 ws2 _ hle i hi
      exact hle i hi
    | cons g gs ih =>
      intro ws1 ws2 hlen hle
      simp only [List.foldl_cons]
      have hg_g := hg g (by simp)
      have hg_gs : ∀ g' ∈ gs, (g'.op = GateOp.and ∨ g'.op = GateOp.or) ∧ g'.inputs.length = 2 :=
        fun g' hg' => hg g' (by simp [hg'])
      apply ih hg_gs (stepWires ws1 g) (stepWires ws2 g)
      · simp [stepWires, hlen]
      · intro i hi
        by_cases hlt : i < ws1.length
        · have hlt2 : i < ws2.length := by omega
          have hl1 : i < (stepWires ws1 g).length := by simp [stepWires]; omega
          have hl2 : i < (stepWires ws2 g).length := by simp [stepWires]; omega
          rw [List.getD_eq_getElem _ _ hl1] at hi
          rw [List.getD_eq_getElem _ _ hl2]
          simp only [stepWires, List.getElem_append_left hlt] at hi
          simp only [stepWires, List.getElem_append_left hlt2]
          have hstep := hle i
          rw [List.getD_eq_getElem _ _ hlt, List.getD_eq_getElem _ _ hlt2] at hstep
          exact hstep hi
        · by_cases heq : i = ws1.length
          · subst heq
            have hl1 : ws1.length < (stepWires ws1 g).length := by simp [stepWires]
            have hl2 : ws1.length < (stepWires ws2 g).length := by simp [stepWires, hlen]
            rw [List.getD_eq_getElem _ _ hl1] at hi
            rw [List.getD_eq_getElem _ _ hl2]
            simp only [stepWires, List.getElem_append_right (le_refl _), Nat.sub_self,
              List.getElem_singleton] at hi
            simp only [stepWires, hlen, List.getElem_append_right (le_refl _), Nat.sub_self,
              List.getElem_singleton]
            apply gateOp_mono hg_g.1 (by simp) _ hi
            intro j hj1 hj2 hval
            simp only [List.getElem_map] at hval ⊢
            exact hle _ hval
          · have hge1 : (stepWires ws1 g).length ≤ i := by simp [stepWires]; omega
            rw [List.getD_eq_default _ _ hge1] at hi
            simp at hi
  apply hgen (List.ofFn x) (List.ofFn y) (by simp)
  intro i hi
  by_cases hlt : i < n
  · have hl1 : i < (List.ofFn x).length := by simp [hlt]
    have hl2 : i < (List.ofFn y).length := by simp [hlt]
    rw [List.getD_eq_getElem _ _ hl1, List.getElem_ofFn] at hi
    rw [List.getD_eq_getElem _ _ hl2, List.getElem_ofFn]
    exact hxy ⟨i, hlt⟩ hi
  · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
    simp at hi

def e1 {n : ℕ} (p : Fin n) : Fin n → Bool := fun q => decide (q = p)

def supp (n : ℕ) (gs : List Gate) (i : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun p : Fin n => wireVal n gs (e1 p) i = true)

def suppAt (n : ℕ) (gs : List Gate) (bound i : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun p : Fin n => wireAt n gs bound i (e1 p) = true)

lemma supp_input (n : ℕ) (gs : List Gate) (v : Fin n) : supp n gs v.val = {v} := by
  ext p
  simp [supp, wireVal_input, e1, eq_comm]

lemma supp_of_ge (n : ℕ) (gs : List Gate) {i : ℕ} (hi : n + gs.length ≤ i) :
    supp n gs i = ∅ := by
  ext p
  simp [supp, wireVal_of_ge n gs _ hi]

lemma suppAt_eq_of_lt (n : ℕ) (gs : List Gate) {bound i : ℕ} (hi : i < bound) :
    suppAt n gs bound i = supp n gs i := by
  ext p
  simp [suppAt, supp, wireAt, hi]

lemma suppAt_eq_empty_of_ge (n : ℕ) (gs : List Gate) {bound i : ℕ} (hi : bound ≤ i) :
    suppAt n gs bound i = ∅ := by
  ext p
  simp [suppAt, wireAt, show ¬ i < bound by omega]

lemma gate_two_inputs {g : Gate} (h : g.inputs.length = 2) :
    ∃ a b : ℕ, g.inputs = [a, b] := by
  cases hin : g.inputs with
  | nil => simp [hin] at h
  | cons a l =>
    cases l with
    | nil => simp [hin] at h
    | cons b l2 =>
      cases l2 with
      | nil => exact ⟨a, b, rfl⟩
      | cons c l3 => simp [hin] at h

-- General reachability and exit counting on strictly decreasing DAGs over ℕ.

def reach (ch : ℕ → Finset ℕ) (hdec : ∀ x, ∀ y ∈ ch x, y < x) : ℕ → Finset ℕ
  | x => insert x ((ch x).attach.biUnion (fun y => reach ch hdec y.val))
termination_by x => x
decreasing_by exact hdec x y.val y.property

lemma self_mem_reach (ch : ℕ → Finset ℕ) (hdec : ∀ x, ∀ y ∈ ch x, y < x) (x : ℕ) :
    x ∈ reach ch hdec x := by
  rw [reach]
  exact Finset.mem_insert_self _ _

lemma reach_subset_of_mem_ch (ch : ℕ → Finset ℕ) (hdec : ∀ x, ∀ y ∈ ch x, y < x)
    {x y : ℕ} (hy : y ∈ ch x) :
    reach ch hdec y ⊆ reach ch hdec x := by
  intro z hz
  rw [reach]
  apply Finset.mem_insert_of_mem
  rw [Finset.mem_biUnion]
  exact ⟨⟨y, hy⟩, Finset.mem_attach _ _, hz⟩

lemma reach_closed (ch : ℕ → Finset ℕ) (hdec : ∀ x, ∀ y ∈ ch x, y < x) :
    ∀ x, ∀ u ∈ reach ch hdec x, ∀ v ∈ ch u, v ∈ reach ch hdec x := by
  intro x
  induction x using Nat.strong_induction_on with
  | ind x ih =>
    intro u hu v hv
    rw [reach, Finset.mem_insert] at hu
    rcases hu with rfl | hu'
    · exact reach_subset_of_mem_ch ch hdec hv (self_mem_reach ch hdec v)
    · rw [Finset.mem_biUnion] at hu'
      obtain ⟨⟨y, hy⟩, _, huy⟩ := hu'
      have hv_y := ih y (hdec x y hy) u huy v hv
      exact reach_subset_of_mem_ch ch hdec hy hv_y

lemma reach_has_parent (ch : ℕ → Finset ℕ) (hdec : ∀ x, ∀ y ∈ ch x, y < x) :
    ∀ x, ∀ v ∈ reach ch hdec x, v ≠ x → ∃ u ∈ reach ch hdec x, v ∈ ch u := by
  intro x
  induction x using Nat.strong_induction_on with
  | ind x ih =>
    intro v hv hne
    rw [reach, Finset.mem_insert] at hv
    rcases hv with rfl | hv'
    · exact (hne rfl).elim
    · rw [Finset.mem_biUnion] at hv'
      obtain ⟨⟨y, hy⟩, _, hvy⟩ := hv'
      by_cases hvy_eq : v = y
      · subst hvy_eq
        exact ⟨x, self_mem_reach ch hdec x, hy⟩
      · obtain ⟨u, hu_y, hvu⟩ := ih y (hdec x y hy) v hvy hvy_eq
        exact ⟨u, reach_subset_of_mem_ch ch hdec hy hu_y, hvu⟩

lemma exit_card_le (ch : ℕ → Finset ℕ) (hdec : ∀ x, ∀ y ∈ ch x, y < x)
    (P : ℕ → Bool) (o : ℕ) (ho : P o = true)
    (hcard : ∀ x, (ch x).card ≤ 2)
    (hempty : ∀ x, P x = false → ch x = ∅) :
    ((reach ch hdec o).filter (fun x => P x = false)).card ≤
      ((reach ch hdec o).filter (fun x => P x = true)).card + 1 := by
  set R := reach ch hdec o
  set P0 := R.filter (fun x => P x = true)
  set E := R.filter (fun x => P x = false)
  have ho_P0 : o ∈ P0 := by
    simp [P0, R, self_mem_reach, ho]
  have hsub : (P0.erase o) ∪ E ⊆ P0.biUnion ch := by
    intro v hv
    have hv_R : v ∈ R := by
      rw [Finset.mem_union] at hv
      rcases hv with h1 | h2
      · exact (Finset.mem_filter.mp (Finset.mem_of_mem_erase h1)).1
      · exact (Finset.mem_filter.mp h2).1
    have hne : v ≠ o := by
      rw [Finset.mem_union] at hv
      rcases hv with h1 | h2
      · exact (Finset.mem_erase.mp h1).1
      · intro heq
        subst heq
        have hf := (Finset.mem_filter.mp h2).2
        rw [ho] at hf
        simp at hf
    obtain ⟨u, hu_R, hvu⟩ := reach_has_parent ch hdec o v hv_R hne
    have hu_P : P u = true := by
      cases hpu : P u with
      | true => rfl
      | false =>
        rw [hempty u hpu] at hvu
        simp at hvu
    rw [Finset.mem_biUnion]
    exact ⟨u, Finset.mem_filter.mpr ⟨hu_R, hu_P⟩, hvu⟩
  have hdisj : Disjoint (P0.erase o) E := by
    rw [Finset.disjoint_left]
    intro v h1 h2
    have ht := (Finset.mem_filter.mp (Finset.mem_of_mem_erase h1)).2
    have hf := (Finset.mem_filter.mp h2).2
    rw [ht] at hf
    simp at hf
  have hle1 := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_erase_of_mem ho_P0] at hle1
  have hle2 : (P0.biUnion ch).card ≤ ∑ x ∈ P0, (ch x).card := Finset.card_biUnion_le
  have hle3 : ∑ x ∈ P0, (ch x).card ≤ ∑ _x ∈ P0, 2 :=
    Finset.sum_le_sum (fun x _ => hcard x)
  rw [Finset.sum_const, smul_eq_mul] at hle3
  have hP0_pos : 1 ≤ P0.card := Finset.card_pos.mpr ⟨o, ho_P0⟩
  omega

-- Private-wire predicate and global valuation valStar.

def defaultGate : Gate := ⟨GateOp.or, []⟩

def privWire (n : ℕ) (S : Finset (Fin n)) (gs : List Gate) (x : ℕ) : Bool :=
  decide (n ≤ x ∧ x < n + gs.length ∧ supp n gs x ⊆ S ∧ 2 ≤ (supp n gs x).card)

def valStar (n : ℕ) (S : Finset (Fin n)) (gs : List Gate) : ℕ → Bool
  | x =>
    if privWire n S gs x = true then
      let g := gs.getD (x - n) defaultGate
      g.op.eval (g.inputs.map fun i => if hi : i < x then valStar n S gs i else false)
    else
      decide (¬ supp n gs x ⊆ S)
termination_by x => x
decreasing_by exact hi

def valStarAt (n : ℕ) (S : Finset (Fin n)) (gs : List Gate) (bound i : ℕ) : Bool :=
  if i < bound then valStar n S gs i else false

lemma valStar_of_priv (n : ℕ) (S : Finset (Fin n)) (gs : List Gate) {x : ℕ}
    (h : privWire n S gs x = true) (hx : x - n < gs.length) :
    valStar n S gs x =
      (gs[x - n]'hx).op.eval ((gs[x - n]'hx).inputs.map fun i => valStarAt n S gs x i) := by
  rw [valStar]
  simp only [h, ↓reduceIte, List.getD_eq_getElem _ _ hx]
  rfl

lemma valStar_of_not_priv (n : ℕ) (S : Finset (Fin n)) (gs : List Gate) {x : ℕ}
    (h : privWire n S gs x = false) :
    valStar n S gs x = decide (¬ supp n gs x ⊆ S) := by
  rw [valStar]
  simp [h]

lemma card_le_one_of_not_priv_false (n : ℕ) (S : Finset (Fin n)) (gs : List Gate) {u : ℕ}
    (hp : privWire n S gs u = false) (hv : valStar n S gs u = false) :
    (supp n gs u).card ≤ 1 := by
  rw [valStar_of_not_priv n S gs hp, decide_eq_false_iff_not, not_not] at hv
  by_cases h1 : u < n
  · have hs := supp_input n gs ⟨u, h1⟩
    change supp n gs u = {⟨u, h1⟩} at hs
    rw [hs]
    simp
  · by_cases h2 : u < n + gs.length
    · simp only [privWire, decide_eq_false_iff_not] at hp
      have hge : ¬ 2 ≤ (supp n gs u).card := fun hc => hp ⟨by omega, h2, hv, hc⟩
      omega
    · rw [supp_of_ge n gs (by omega)]
      simp

lemma priv_set_card_le (n : ℕ) (S : Finset (Fin n)) (gs : List Gate) (A : Finset ℕ)
    (hA : ∀ x ∈ A, privWire n S gs x = true) :
    A.card ≤ ((Finset.range gs.length).filter (fun j =>
      supp n gs (n + j) ⊆ S ∧ 2 ≤ (supp n gs (n + j)).card)).card := by
  have hsub : A.image (fun x => x - n) ⊆ (Finset.range gs.length).filter (fun j =>
      supp n gs (n + j) ⊆ S ∧ 2 ≤ (supp n gs (n + j)).card) := by
    intro j hj
    rw [Finset.mem_image] at hj
    obtain ⟨x, hxA, rfl⟩ := hj
    have hpx := hA x hxA
    simp only [privWire, decide_eq_true_eq] at hpx
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, ?_, ?_⟩
    · rw [show n + (x - n) = x by omega]; exact hpx.2.2.1
    · rw [show n + (x - n) = x by omega]; exact hpx.2.2.2
  have hinj : Set.InjOn (fun x => x - n) (A : Set ℕ) := by
    intro x hx y hy hxy
    have hpx := hA x hx
    have hpy := hA y hy
    simp only [privWire, decide_eq_true_eq] at hpx hpy
    dsimp only at hxy
    omega
  rw [← Finset.card_image_of_injOn hinj]
  exact Finset.card_le_card hsub

-- Case 1 children: all in-bounds inputs of a private gate.
def ch1 (n : ℕ) (S : Finset (Fin n)) (gs : List Gate) (x : ℕ) : Finset ℕ :=
  if privWire n S gs x = true then
    ((gs.getD (x - n) defaultGate).inputs.filter (fun i => decide (i < x))).toFinset
  else ∅

lemma ch1_dec (n : ℕ) (S : Finset (Fin n)) (gs : List Gate) :
    ∀ x, ∀ y ∈ ch1 n S gs x, y < x := by
  intro x y hy
  unfold ch1 at hy
  split_ifs at hy with h
  · simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at hy
    exact hy.2
  · simp at hy

lemma ch1_card (n : ℕ) (S : Finset (Fin n)) (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (x : ℕ) : (ch1 n S gs x).card ≤ 2 := by
  unfold ch1
  split_ifs with h
  · have hx : x - n < gs.length := by
      simp only [privWire, decide_eq_true_eq] at h; omega
    rw [List.getD_eq_getElem _ _ hx]
    have hlen := (hg (gs[x - n]'hx) (List.getElem_mem hx)).2
    have h1 := List.toFinset_card_le ((gs[x - n]'hx).inputs.filter (fun i => decide (i < x)))
    have h2 := List.length_filter_le (fun i => decide (i < x)) (gs[x - n]'hx).inputs
    omega
  · simp

lemma ch1_empty (n : ℕ) (S : Finset (Fin n)) (gs : List Gate) (x : ℕ)
    (h : privWire n S gs x = false) : ch1 n S gs x = ∅ := by
  simp [ch1, h]

-- Case 2 children: for private gates with valStar = false.
def isPrivF (n : ℕ) (S : Finset (Fin n)) (gs : List Gate) (x : ℕ) : Bool :=
  privWire n S gs x && !valStar n S gs x

def ch2 (n : ℕ) (S : Finset (Fin n)) (gs : List Gate) (x : ℕ) : Finset ℕ :=
  if isPrivF n S gs x = true then
    let g := gs.getD (x - n) defaultGate
    match g.op with
    | GateOp.or => (g.inputs.filter (fun i => decide (i < x))).toFinset
    | _ =>
      match g.inputs with
      | [a, b] =>
        if a < x ∧ valStar n S gs a = false then {a}
        else if b < x ∧ valStar n S gs b = false then {b}
        else ∅
      | _ => ∅
  else ∅

lemma ch2_dec (n : ℕ) (S : Finset (Fin n)) (gs : List Gate) :
    ∀ x, ∀ y ∈ ch2 n S gs x, y < x := by
  intro x y hy
  unfold ch2 at hy
  split_ifs at hy with h
  · dsimp only at hy
    cases hop : (gs.getD (x - n) defaultGate).op <;> rw [hop] at hy <;> dsimp only at hy
    · cases hin : (gs.getD (x - n) defaultGate).inputs with
      | nil => rw [hin] at hy; simp at hy
      | cons a l =>
        cases l with
        | nil => rw [hin] at hy; simp at hy
        | cons b l2 =>
          cases l2 with
          | nil =>
            rw [hin] at hy; dsimp only at hy
            split_ifs at hy with ha hb
            · simp only [Finset.mem_singleton] at hy; omega
            · simp only [Finset.mem_singleton] at hy; omega
            · simp at hy
          | cons c l3 => rw [hin] at hy; simp at hy
    · simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at hy
      exact hy.2
    · cases hin : (gs.getD (x - n) defaultGate).inputs with
      | nil => rw [hin] at hy; simp at hy
      | cons a l =>
        cases l with
        | nil => rw [hin] at hy; simp at hy
        | cons b l2 =>
          cases l2 with
          | nil =>
            rw [hin] at hy; dsimp only at hy
            split_ifs at hy with ha hb
            · simp only [Finset.mem_singleton] at hy; omega
            · simp only [Finset.mem_singleton] at hy; omega
            · simp at hy
          | cons c l3 => rw [hin] at hy; simp at hy
    · cases hin : (gs.getD (x - n) defaultGate).inputs with
      | nil => rw [hin] at hy; simp at hy
      | cons a l =>
        cases l with
        | nil => rw [hin] at hy; simp at hy
        | cons b l2 =>
          cases l2 with
          | nil =>
            rw [hin] at hy; dsimp only at hy
            split_ifs at hy with ha hb
            · simp only [Finset.mem_singleton] at hy; omega
            · simp only [Finset.mem_singleton] at hy; omega
            · simp at hy
          | cons c l3 => rw [hin] at hy; simp at hy
    · cases hin : (gs.getD (x - n) defaultGate).inputs with
      | nil => rw [hin] at hy; simp at hy
      | cons a l =>
        cases l with
        | nil => rw [hin] at hy; simp at hy
        | cons b l2 =>
          cases l2 with
          | nil =>
            rw [hin] at hy; dsimp only at hy
            split_ifs at hy with ha hb
            · simp only [Finset.mem_singleton] at hy; omega
            · simp only [Finset.mem_singleton] at hy; omega
            · simp at hy
          | cons c l3 => rw [hin] at hy; simp at hy
  · simp at hy

lemma ch2_card (n : ℕ) (S : Finset (Fin n)) (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (x : ℕ) : (ch2 n S gs x).card ≤ 2 := by
  unfold ch2
  split_ifs with h
  · have hp : privWire n S gs x = true := by
      simp only [isPrivF, Bool.and_eq_true] at h; exact h.1
    have hx : x - n < gs.length := by
      simp only [privWire, decide_eq_true_eq] at hp; omega
    rw [List.getD_eq_getElem _ _ hx]
    have hgx := hg (gs[x - n]'hx) (List.getElem_mem hx)
    rcases hgx.1 with hand | hor
    · dsimp only
      rw [hand]
      obtain ⟨a, b, hab⟩ := gate_two_inputs hgx.2
      rw [hab]
      dsimp only
      split_ifs <;> simp
    · dsimp only
      rw [hor]
      dsimp only
      have h1 := List.toFinset_card_le ((gs[x - n]'hx).inputs.filter (fun i => decide (i < x)))
      have h2 := List.length_filter_le (fun i => decide (i < x)) (gs[x - n]'hx).inputs
      have hlen := hgx.2
      omega
  · simp

lemma ch2_empty (n : ℕ) (S : Finset (Fin n)) (gs : List Gate) (x : ℕ)
    (h : isPrivF n S gs x = false) : ch2 n S gs x = ∅ := by
  simp [ch2, h]

lemma ch2_valStar_false (n : ℕ) (S : Finset (Fin n)) (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    {x y : ℕ} (hy : y ∈ ch2 n S gs x) : valStar n S gs y = false := by
  unfold ch2 at hy
  split_ifs at hy with h
  · have hp : privWire n S gs x = true := by
      simp only [isPrivF, Bool.and_eq_true] at h; exact h.1
    have hvf : valStar n S gs x = false := by
      simp only [isPrivF, Bool.and_eq_true, Bool.not_eq_true'] at h; exact h.2
    have hx : x - n < gs.length := by
      simp only [privWire, decide_eq_true_eq] at hp; omega
    rw [List.getD_eq_getElem _ _ hx] at hy
    have hgx := hg (gs[x - n]'hx) (List.getElem_mem hx)
    rcases hgx.1 with hand | hor
    · dsimp only at hy
      rw [hand] at hy
      obtain ⟨a, b, hab⟩ := gate_two_inputs hgx.2
      rw [hab] at hy
      dsimp only at hy
      split_ifs at hy with ha hb
      · simp only [Finset.mem_singleton] at hy; subst hy; exact ha.2
      · simp only [Finset.mem_singleton] at hy; subst hy; exact hb.2
      · simp at hy
    · dsimp only at hy
      rw [hor] at hy
      simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at hy
      have hvs := valStar_of_priv n S gs hp hx
      rw [hvf, hor] at hvs
      by_contra hnt
      have hyt : valStar n S gs y = true := by cases h1 : valStar n S gs y <;> simp_all
      have hmem : true ∈ (gs[x - n]'hx).inputs.map (fun i => valStarAt n S gs x i) := by
        rw [List.mem_map]
        refine ⟨y, hy.1, ?_⟩
        simp [valStarAt, hy.2, hyt]
      have hany : ((gs[x - n]'hx).inputs.map (fun i => valStarAt n S gs x i)).any id = true := by
        rw [List.any_eq_true]; exact ⟨true, hmem, rfl⟩
      simp only [GateOp.eval] at hvs
      rw [hany] at hvs
      simp at hvs
  · simp at hy

lemma ch2_supp_subset (n : ℕ) (S : Finset (Fin n)) (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    {x : ℕ} (hx_pf : isPrivF n S gs x = true) :
    supp n gs x ⊆ (ch2 n S gs x).biUnion (supp n gs) := by
  have hp : privWire n S gs x = true := by
    simp only [isPrivF, Bool.and_eq_true] at hx_pf; exact hx_pf.1
  have hvf : valStar n S gs x = false := by
    simp only [isPrivF, Bool.and_eq_true, Bool.not_eq_true'] at hx_pf; exact hx_pf.2
  have hpx : n ≤ x ∧ x < n + gs.length ∧ supp n gs x ⊆ S ∧ 2 ≤ (supp n gs x).card := by
    simpa only [privWire, decide_eq_true_eq] using hp
  have hx_lt : x - n < gs.length := by omega
  have hgx := hg (gs[x - n]'hx_lt) (List.getElem_mem hx_lt)
  obtain ⟨a, b, hab⟩ := gate_two_inputs hgx.2
  have hgate : ∀ inp : Fin n → Bool,
      wireVal n gs inp x =
        (gs[x - n]'hx_lt).op.eval [wireAt n gs x a inp, wireAt n gs x b inp] := by
    intro inp
    have h1 := wireVal_gate n gs inp hx_lt
    rwa [show n + (x - n) = x by omega, hab] at h1
  rcases hgx.1 with hand | hor
  · -- AND gate
    have hsupp_eq : supp n gs x = suppAt n gs x a ∩ suppAt n gs x b := by
      ext p
      simp only [supp, suppAt, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hgate (e1 p), hand]
      simp [GateOp.eval]
    have ha_lt : a < x := by
      by_contra hge
      have hempty : supp n gs x = ∅ := by
        rw [hsupp_eq, suppAt_eq_empty_of_ge n gs (by omega), Finset.empty_inter]
      have hcard := hpx.2.2.2
      rw [hempty] at hcard
      simp at hcard
    have hb_lt : b < x := by
      by_contra hge
      have hempty : supp n gs x = ∅ := by
        rw [hsupp_eq, suppAt_eq_empty_of_ge n gs (i := b) (by omega), Finset.inter_empty]
      have hcard := hpx.2.2.2
      rw [hempty] at hcard
      simp at hcard
    have hvs := valStar_of_priv n S gs hp hx_lt
    rw [hvf, hand, hab] at hvs
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq,
      Bool.and_true, valStarAt, ha_lt, hb_lt, ↓reduceIte] at hvs
    have hor_false : valStar n S gs a = false ∨ valStar n S gs b = false := by
      cases h1 : valStar n S gs a <;> cases h2 : valStar n S gs b <;>
        rw [h1, h2] at hvs <;> simp at hvs ⊢
    have hch : ch2 n S gs x =
        if a < x ∧ valStar n S gs a = false then {a}
        else if b < x ∧ valStar n S gs b = false then {b}
        else ∅ := by
      unfold ch2
      simp only [hx_pf, ↓reduceIte, List.getD_eq_getElem _ _ hx_lt, hand, hab]
    rw [hch]
    split_ifs with h1 h2
    · rw [Finset.singleton_biUnion, hsupp_eq, suppAt_eq_of_lt n gs ha_lt]
      exact Finset.inter_subset_left
    · rw [Finset.singleton_biUnion, hsupp_eq, suppAt_eq_of_lt n gs hb_lt]
      exact Finset.inter_subset_right
    · rcases hor_false with haf | hbf
      · exact (h1 ⟨ha_lt, haf⟩).elim
      · exact (h2 ⟨hb_lt, hbf⟩).elim
  · -- OR gate
    have hsupp_eq : supp n gs x = suppAt n gs x a ∪ suppAt n gs x b := by
      ext p
      simp only [supp, suppAt, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hgate (e1 p), hor]
      simp [GateOp.eval]
    have hch : ch2 n S gs x = ([a, b].filter (fun i => decide (i < x))).toFinset := by
      unfold ch2
      simp only [hx_pf, ↓reduceIte, List.getD_eq_getElem _ _ hx_lt, hor, hab]
    intro p hp_mem
    rw [hsupp_eq, Finset.mem_union] at hp_mem
    rw [hch, Finset.mem_biUnion]
    rcases hp_mem with hpa | hpb
    · have ha_lt : a < x := by
        by_contra hge
        rw [suppAt_eq_empty_of_ge n gs (by omega)] at hpa
        simp at hpa
      refine ⟨a, ?_, ?_⟩
      · simp [ha_lt]
      · rwa [suppAt_eq_of_lt n gs ha_lt] at hpa
    · have hb_lt : b < x := by
        by_contra hge
        rw [suppAt_eq_empty_of_ge n gs (by omega)] at hpb
        simp at hpb
      refine ⟨b, ?_, ?_⟩
      · simp [hb_lt]
      · rwa [suppAt_eq_of_lt n gs hb_lt] at hpb

lemma reach_ch2_valStar_false (n : ℕ) (S : Finset (Fin n)) (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) :
    ∀ x, valStar n S gs x = false →
      ∀ u ∈ reach (ch2 n S gs) (ch2_dec n S gs) x, valStar n S gs u = false := by
  intro x
  induction x using Nat.strong_induction_on with
  | ind x ih =>
    intro hxf u hu
    rw [reach, Finset.mem_insert] at hu
    rcases hu with rfl | hu'
    · exact hxf
    · rw [Finset.mem_biUnion] at hu'
      obtain ⟨⟨y, hy⟩, _, huy⟩ := hu'
      exact ih y (ch2_dec n S gs x y hy) (ch2_valStar_false n S gs hg hy) u huy

lemma supp_subset_exits_ch2 (n : ℕ) (S : Finset (Fin n)) (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (o : ℕ) :
    ∀ x, x ∈ reach (ch2 n S gs) (ch2_dec n S gs) o →
      supp n gs x ⊆ ((reach (ch2 n S gs) (ch2_dec n S gs) o).filter
        (fun u => isPrivF n S gs u = false)).biUnion (supp n gs) := by
  intro x
  induction x using Nat.strong_induction_on with
  | ind x ih =>
    intro hx_R
    cases hpf : isPrivF n S gs x with
    | false =>
      intro p hp
      rw [Finset.mem_biUnion]
      exact ⟨x, Finset.mem_filter.mpr ⟨hx_R, hpf⟩, hp⟩
    | true =>
      have hstep := ch2_supp_subset n S gs hg hpf
      intro p hp
      have hp' := hstep hp
      rw [Finset.mem_biUnion] at hp'
      obtain ⟨y, hy_ch, hpy⟩ := hp'
      have hy_R := reach_closed (ch2 n S gs) (ch2_dec n S gs) o x hx_R y hy_ch
      exact ih y (ch2_dec n S gs x y hy_ch) hy_R hpy

end PEqualNP.Outside.L_meta_278_aux

open PEqualNP.Outside.L_meta_278_aux

theorem PEqualNP.Outside.L_meta_278 : ∀ (n k c o : ℕ) (S : Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → (∀ p : Fin n, (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD o false = true ↔ p ∈ S) → (∀ x : Fin n → Bool, (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k → (∀ q ∈ S, x q = false) → (C.wires (List.ofFn x)).getD o false = false) → c ≤ k → c + 1 ≤ S.card → c ≤ ((Finset.range C.size).filter (fun j => (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + j) false = true)) ⊆ S ∧ 2 ≤ (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + j) false = true)).card)).card := by
  classical
  intro n k c o S C hg hS hlight hck hcS
  change c ≤ ((Finset.range C.gates.length).filter (fun j =>
    supp n C.gates (n + j) ⊆ S ∧ 2 ≤ (supp n C.gates (n + j)).card)).card
  by_cases hc0 : c = 0
  · subst hc0; exact Nat.zero_le _
  have hS2 : 2 ≤ S.card := by omega
  have ho_supp : supp n C.gates o = S := by
    ext p
    simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hS p
  have ho_ge : n ≤ o := by
    by_contra hlt
    have hlt' : o < n := by omega
    have hs := supp_input n C.gates ⟨o, hlt'⟩
    change supp n C.gates o = {⟨o, hlt'⟩} at hs
    rw [ho_supp] at hs
    have hc := congrArg Finset.card hs
    simp at hc
    omega
  have ho_lt : o < n + C.gates.length := by
    by_contra hge
    have hs := supp_of_ge n C.gates (by omega : n + C.gates.length ≤ o)
    rw [ho_supp] at hs
    rw [hs] at hS2
    simp at hS2
  have ho_priv : privWire n S C.gates o = true := by
    simp only [privWire, decide_eq_true_eq, ho_supp]
    exact ⟨ho_ge, ho_lt, Finset.Subset.refl _, hS2⟩
  cases hvo : valStar n S C.gates o with
  | true =>
    set R1 := reach (ch1 n S C.gates) (ch1_dec n S C.gates) o
    set P1 := R1.filter (fun x => privWire n S C.gates x = true)
    set E1 := R1.filter (fun x => privWire n S C.gates x = false)
    have hE1_le : E1.card ≤ P1.card + 1 :=
      exit_card_le (ch1 n S C.gates) (ch1_dec n S C.gates) (privWire n S C.gates) o ho_priv
        (ch1_card n S C.gates hg) (ch1_empty n S C.gates)
    have hP1_le := priv_set_card_le n S C.gates P1 (fun x hx => (Finset.mem_filter.mp hx).2)
    set EL := E1.filter (fun u => ¬ supp n C.gates u ⊆ S)
    have hEL_le : EL.card ≤ E1.card := Finset.card_filter_le _ _
    have hex_pt : ∀ u : EL, ∃ q : Fin n, q ∈ supp n C.gates u.val ∧ q ∉ S := by
      rintro ⟨u, hu⟩
      have hns : ¬ supp n C.gates u ⊆ S := (Finset.mem_filter.mp hu).2
      exact Finset.not_subset.mp hns
    let testSet : Finset (Fin n) := EL.attach.image (fun u => Classical.choose (hex_pt u))
    have htest_card : testSet.card ≤ EL.card := by
      have h1 := Finset.card_image_le (s := EL.attach) (f := fun u => Classical.choose (hex_pt u))
      simpa using h1
    have htest_disj : ∀ q ∈ testSet, q ∉ S := by
      intro q hq
      rw [Finset.mem_image] at hq
      obtain ⟨u, _, rfl⟩ := hq
      exact (Classical.choose_spec (hex_pt u)).2
    let x : Fin n → Bool := fun q => decide (q ∈ testSet)
    have hval_eval : ∀ w, w ∈ R1 → valStar n S C.gates w = true →
        wireVal n C.gates x w = true := by
      intro w
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro hw_R hw_t
        cases hpw : privWire n S C.gates w with
        | false =>
          rw [valStar_of_not_priv n S C.gates hpw, decide_eq_true_eq] at hw_t
          have hw_EL : w ∈ EL := Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hw_R, hpw⟩, hw_t⟩
          let u : EL := ⟨w, hw_EL⟩
          let q := Classical.choose (hex_pt u)
          have hq_spec : q ∈ supp n C.gates w ∧ q ∉ S := Classical.choose_spec (hex_pt u)
          have hq_supp : wireVal n C.gates (e1 q) w = true := by
            have h1 := hq_spec.1
            simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and] at h1
            exact h1
          have hq_test : q ∈ testSet := by
            rw [Finset.mem_image]
            exact ⟨u, Finset.mem_attach _ _, rfl⟩
          apply wireVal_mono n C.gates hg _ w hq_supp
          intro v hv
          simp only [e1, decide_eq_true_eq] at hv
          subst hv
          simp [x, hq_test]
        | true =>
          have hpw' : n ≤ w ∧ w < n + C.gates.length := by
            simp only [privWire, decide_eq_true_eq] at hpw; exact ⟨hpw.1, hpw.2.1⟩
          have hw_lt : w - n < C.gates.length := by omega
          have hgw := hg (C.gates[w - n]'hw_lt) (List.getElem_mem hw_lt)
          have hvs := valStar_of_priv n S C.gates hpw hw_lt
          rw [hw_t] at hvs
          have hvg := wireVal_gate n C.gates x hw_lt
          rw [show n + (w - n) = w by omega] at hvg
          rw [hvg]
          apply gateOp_mono hgw.1 (by simp) _ hvs.symm
          intro j hj1 hj2 hj_val
          simp only [List.getElem_map] at hj_val ⊢
          set idx := (C.gates[w - n]'hw_lt).inputs[j]'(by simp at hj1; exact hj1)
          have hidx_mem : idx ∈ (C.gates[w - n]'hw_lt).inputs := List.getElem_mem _
          unfold valStarAt at hj_val
          split_ifs at hj_val with hlt
          have hidx_ch : idx ∈ ch1 n S C.gates w := by
            unfold ch1
            simp only [hpw, ↓reduceIte, List.getD_eq_getElem _ _ hw_lt,
              List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
            exact ⟨hidx_mem, hlt⟩
          have hidx_R : idx ∈ R1 := reach_closed (ch1 n S C.gates) (ch1_dec n S C.gates) o w hw_R idx hidx_ch
          unfold wireAt
          simp only [hlt, ↓reduceIte]
          exact ih idx hlt hidx_R hj_val
    have ho_eval_t : wireVal n C.gates x o = true :=
      hval_eval o (self_mem_reach _ _ o) hvo
    by_contra hlt_c
    have hcard_x : (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k := by
      have heq : Finset.univ.filter (fun q : Fin n => x q = true) = testSet := by
        ext q; simp [x]
      rw [heq]
      omega
    have hzero_S : ∀ q ∈ S, x q = false := by
      intro q hqS
      simp only [x, decide_eq_false_iff_not]
      intro hqt
      exact htest_disj q hqt hqS
    have ho_eval_f : wireVal n C.gates x o = false := hlight x hcard_x hzero_S
    rw [ho_eval_t] at ho_eval_f
    simp at ho_eval_f
  | false =>
    set R2 := reach (ch2 n S C.gates) (ch2_dec n S C.gates) o
    set P2 := R2.filter (fun x => isPrivF n S C.gates x = true)
    set E2 := R2.filter (fun x => isPrivF n S C.gates x = false)
    have ho_pf : isPrivF n S C.gates o = true := by
      simp [isPrivF, ho_priv, hvo]
    have hE2_le : E2.card ≤ P2.card + 1 :=
      exit_card_le (ch2 n S C.gates) (ch2_dec n S C.gates) (isPrivF n S C.gates) o ho_pf
        (ch2_card n S C.gates hg) (ch2_empty n S C.gates)
    have hP2_le := priv_set_card_le n S C.gates P2 (fun x hx => by
      have h1 := (Finset.mem_filter.mp hx).2
      simp only [isPrivF, Bool.and_eq_true] at h1
      exact h1.1)
    have hS_sub : S ⊆ E2.biUnion (supp n C.gates) := by
      rw [← ho_supp]
      exact supp_subset_exits_ch2 n S C.gates hg o o (self_mem_reach _ _ o)
    have hS_le1 : S.card ≤ (E2.biUnion (supp n C.gates)).card := Finset.card_le_card hS_sub
    have hS_le2 : (E2.biUnion (supp n C.gates)).card ≤ ∑ u ∈ E2, (supp n C.gates u).card :=
      Finset.card_biUnion_le
    have hS_le3 : ∑ u ∈ E2, (supp n C.gates u).card ≤ ∑ _u ∈ E2, 1 := by
      apply Finset.sum_le_sum
      intro u hu
      have hu_R : u ∈ R2 := (Finset.mem_filter.mp hu).1
      have hu_npf : isPrivF n S C.gates u = false := (Finset.mem_filter.mp hu).2
      have hu_vf : valStar n S C.gates u = false :=
        reach_ch2_valStar_false n S C.gates hg o hvo u hu_R
      have hu_np : privWire n S C.gates u = false := by
        simp only [isPrivF, hu_vf, Bool.not_false, Bool.and_true] at hu_npf
        exact hu_npf
      exact card_le_one_of_not_priv_false n S C.gates hu_np hu_vf
    rw [Finset.sum_const, smul_eq_mul, mul_one] at hS_le3
    omega
