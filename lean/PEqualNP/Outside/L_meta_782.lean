import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_782

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

private theorem val_mono (C : Circuit) (n : ℕ) (hMono : Monotone2 C) (x y : Fin n → Bool)
    (hxy : ∀ i, x i = true → y i = true) :
    ∀ w : ℕ, val C n x w = true → val C n y w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hx
    by_cases hwn : w < n
    · rw [val_input C n _ w hwn] at hx ⊢
      exact hxy _ hx
    · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      cases hg : C.gates[j]? with
      | none =>
        rw [val_none C n x j hg] at hx
        simp at hx
      | some h =>
        have hop := (hMono h (List.mem_of_getElem? hg)).1
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
        rcases hop with hop | hop
        · refine (val_and C n y j h hg hop).mpr (fun w hw => ?_)
          obtain ⟨hlt, hv⟩ := (val_and C n x j h hg hop).mp hx w hw
          exact ⟨hlt, ih w hlt hv⟩
        · obtain ⟨w, hw, hlt, hv⟩ := (val_or C n x j h hg hop).mp hx
          exact (val_or C n y j h hg hop).mpr ⟨w, hw, hlt, ih w hlt hv⟩


section Frontier

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, ∃ z ∈ ops a b, build ops goal k (insert z available)

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

theorem compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero =>
    exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

theorem live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

theorem live_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩


end Frontier

abbrev Fn (n : ℕ) := (Fin n → Bool) → Bool

def single {n : ℕ} (p : Fin n) : Fin n → Bool := fun q => decide (q = p)

def singles {n : ℕ} (f : Fn n) : Finset (Fin n) :=
  Finset.univ.filter (fun p => f (single p) = true)

def Private {n : ℕ} (S : Finset (Fin n)) (f : Fn n) : Prop :=
  2 ≤ (singles f).card ∧ singles f ⊆ S

def Mono {n : ℕ} (f : Fn n) : Prop :=
  ∀ x y, (∀ p, x p = true → y p = true) → f x = true → f y = true

noncomputable def boundary {n : ℕ} (S : Finset (Fin n)) : Finset (Fn n) := by
  classical
  exact Finset.univ.filter (fun f => ¬ Private S f ∧ Mono f)

noncomputable def pairOps {n : ℕ} (f g : Fn n) : Finset (Fn n) := by
  classical
  exact {fun x => f x && g x, fun x => f x || g x}

def wire (C : Circuit) (n w : ℕ) : Fn n := fun x => val C n x w

noncomputable def available (C : Circuit) (n : ℕ) (S : Finset (Fin n)) (j : ℕ) :
    Finset (Fn n) := by
  classical
  exact boundary S ∪ (Finset.range j).image (fun r => wire C n (n + r))

noncomputable def privates (C : Circuit) (n : ℕ) (S : Finset (Fin n)) (j : ℕ) :
    Finset ℕ := by
  classical
  exact (Finset.range j).filter (fun r => Private S (wire C n (n + r)))

lemma singles_input {n : ℕ} (p : Fin n) : singles (fun x : Fin n → Bool => x p) = {p} := by
  ext a
  simp [singles, single, eq_comm]

lemma boundary_input {n : ℕ} (S : Finset (Fin n)) (p : Fin n) :
    (fun x : Fin n → Bool => x p) ∈ boundary S := by
  classical
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_, ?_⟩
  · simp [Private, singles_input]
  · intro x y hxy hx
    exact hxy p hx

lemma boundary_false {n : ℕ} (S : Finset (Fin n)) :
    (fun _ : Fin n → Bool => false) ∈ boundary S := by
  classical
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_, ?_⟩
  · simp [Private, singles]
  · intro x y hxy hx
    cases hx

lemma wire_mono (C : Circuit) (n : ℕ) (hm : Monotone2 C) (w : ℕ) : Mono (wire C n w) := by
  intro x y hxy hx
  exact val_mono C n hm x y hxy w hx

lemma available_earlier (C : Circuit) (n : ℕ) (S : Finset (Fin n)) (j w : ℕ)
    (hw : w < n + j) : wire C n w ∈ available C n S j := by
  classical
  by_cases hn : w < n
  · have he : wire C n w = (fun x : Fin n → Bool => x ⟨w, hn⟩) := by
      funext x
      exact val_input C n x w hn
    rw [he]
    exact Finset.mem_union_left _ (boundary_input S ⟨w, hn⟩)
  · apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    refine ⟨w - n, Finset.mem_range.mpr (by omega), ?_⟩
    congr 1
    omega

lemma gate_ops (C : Circuit) (n : ℕ) (S : Finset (Fin n)) (hm : Monotone2 C)
    (hl : ∀ g ∈ C.gates, g.inputs.length = 2) (j : ℕ) (hj : j < C.gates.length) :
    ∃ a ∈ available C n S j, ∃ b ∈ available C n S j,
      wire C n (n + j) ∈ pairOps a b := by
  classical
  let g := C.gates[j]
  have hg : C.gates[j]? = some g := List.getElem?_eq_some_iff.mpr ⟨hj, rfl⟩
  have hmem := List.mem_of_getElem? hg
  obtain ⟨u, v, huv⟩ := List.length_eq_two.mp (hl g hmem)
  let a : Fn n := if u < n + j then wire C n u else fun _ => false
  let b : Fn n := if v < n + j then wire C n v else fun _ => false
  have ha : a ∈ available C n S j := by
    dsimp [a]
    split_ifs with h
    · exact available_earlier C n S j u h
    · exact Finset.mem_union_left _ (boundary_false S)
  have hb : b ∈ available C n S j := by
    dsimp [b]
    split_ifs with h
    · exact available_earlier C n S j v h
    · exact Finset.mem_union_left _ (boundary_false S)
  refine ⟨a, ha, b, hb, ?_⟩
  have hop := (hm g hmem).1
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  simp only [pairOps, Finset.mem_insert, Finset.mem_singleton]
  rcases hop with hop | hop
  · left
    funext x
    change val C n x (n + j) = _
    rw [val_gate C n x j g hg, hop, huv]
    by_cases hu : u < n + j <;> by_cases hv : v < n + j <;>
      simp [GateOp.eval, a, b, wire, hu, hv]
  · right
    funext x
    change val C n x (n + j) = _
    rw [val_gate C n x j g hg, hop, huv]
    by_cases hu : u < n + j <;> by_cases hv : v < n + j <;>
      simp [GateOp.eval, a, b, wire, hu, hv]

lemma available_succ (C : Circuit) (n : ℕ) (S : Finset (Fin n)) (j : ℕ) :
    available C n S (j + 1) = insert (wire C n (n + j)) (available C n S j) := by
  classical
  ext f
  simp [available, Finset.range_add_one]

lemma stages (C : Circuit) (n : ℕ) (S : Finset (Fin n)) (hm : Monotone2 C)
    (hl : ∀ g ∈ C.gates, g.inputs.length = 2) :
    ∀ j, j ≤ C.gates.length → ∀ f k,
      build pairOps f k (available C n S j) →
      build pairOps f (k + (privates C n S j).card) (boundary S) := by
  classical
  intro j
  induction j with
  | zero =>
    intro hj f k h
    simpa [privates, available] using h
  | succ j ih =>
    intro hj f k h
    rw [available_succ] at h
    by_cases hp : Private S (wire C n (n + j))
    · have hc : privates C n S (j + 1) = insert j (privates C n S j) := by
        simp [privates, Finset.range_add_one, Finset.filter_insert, hp]
      have hn : j ∉ privates C n S j := by simp [privates]
      obtain ⟨a, ha, b, hb, hz⟩ := gate_ops C n S hm hl j (by omega)
      have hstep : build pairOps f (k + 1) (available C n S j) :=
        Or.inr ⟨a, ha, b, hb, wire C n (n + j), hz, h⟩
      have hh := ih (by omega) f (k + 1) hstep
      simpa [hc, Finset.card_insert_of_notMem hn, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hh
    · have hc : privates C n S (j + 1) = privates C n S j := by
        simp [privates, Finset.range_add_one, Finset.filter_insert, hp]
      have hb : wire C n (n + j) ∈ boundary S :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp, wire_mono C n hm _⟩
      have hw : wire C n (n + j) ∈ available C n S j := Finset.mem_union_left _ hb
      rw [Finset.insert_eq_of_mem hw] at h
      simpa [hc] using ih (by omega) f k h

lemma final_available (C : Circuit) (n : ℕ) (S : Finset (Fin n)) (w : ℕ) :
    wire C n w ∈ available C n S C.gates.length := by
  classical
  by_cases hw : w < n + C.gates.length
  · exact available_earlier C n S C.gates.length w hw
  · have he : wire C n w = (fun _ => false) := by
      funext x
      apply getD_of_length_le
      rw [wires_eq, foldl_step_length, List.length_ofFn]
      omega
    rw [he]
    exact Finset.mem_union_left _ (boundary_false S)

lemma frontier (C : Circuit) (n : ℕ) (S : Finset (Fin n)) (hm : Monotone2 C)
    (hl : ∀ g ∈ C.gates, g.inputs.length = 2) (w : ℕ) :
    ∃ R ⊆ boundary S,
      live pairOps (wire C n w) (privates C n S C.gates.length).card R := by
  classical
  apply compress
  have h := stages C n S hm hl C.gates.length le_rfl (wire C n w) 0
    (final_available C n S w)
  simpa using h

lemma ops_separate {n : ℕ} (x y : Fin n → Bool) (a b z : Fn n)
    (hz : z ∈ pairOps a b) :
    z x = true ∧ z y = false →
      (a x = true ∧ a y = false) ∨ (b x = true ∧ b y = false) := by
  classical
  simp only [pairOps, Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with rfl | rfl
  · cases ha : a x <;> cases hb : b x <;> cases hc : a y <;> cases hd : b y <;>
      simp_all
  · cases ha : a x <;> cases hb : b x <;> cases hc : a y <;> cases hd : b y <;>
      simp_all

lemma frontier_bound {n : ℕ} (S : Finset (Fin n)) (f : Fn n) (k c q : ℕ)
    (hc : c ≤ k) (hs : c + 1 ≤ (singles f).card)
    (hp : ∀ x : Fin n → Bool, (Finset.univ.filter (fun p => x p = true)).card ≤ k →
      (∀ p ∈ S, x p = false) → f x = false)
    (R : Finset (Fn n)) (hR : R ⊆ boundary S) (hrun : live pairOps f q R) : c ≤ q := by
  classical
  by_contra hq
  have hq' : q < c := by omega
  have hRc := live_card hrun
  let smalls : Fn n → Finset (Fin n) := fun g => if singles g ⊆ S then singles g else ∅
  have hsmall : ∀ g ∈ R, (smalls g).card ≤ 1 := by
    intro g hg
    have hn := (Finset.mem_filter.mp (hR hg)).2.1
    dsimp [smalls]
    split_ifs with hsub
    · by_contra hc'
      exact hn ⟨by omega, hsub⟩
    · simp
  let A := R.biUnion smalls
  have hAc : A.card ≤ R.card := by
    calc
      A.card ≤ ∑ g ∈ R, (smalls g).card := Finset.card_biUnion_le
      _ ≤ ∑ g ∈ R, 1 := Finset.sum_le_sum hsmall
      _ = R.card := by simp
  obtain ⟨a, ha, haA⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show A.card < (singles f).card by omega)
  have hat : f (single a) = true := (Finset.mem_filter.mp ha).2
  let R' := R.filter (fun g => g (single a) = true)
  have hex : ∀ g : {g // g ∈ R'}, ∃ b : Fin n, b ∉ S ∧ g.1 (single b) = true := by
    intro g
    have hg := Finset.mem_filter.mp g.2
    have hns : ¬ singles g.1 ⊆ S := by
      intro hsub
      apply haA
      apply Finset.mem_biUnion.mpr
      refine ⟨g.1, hg.1, ?_⟩
      change a ∈ (if singles g.1 ⊆ S then singles g.1 else ∅)
      rw [if_pos hsub]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hg.2⟩
    obtain ⟨b, hb, hbS⟩ := Finset.not_subset.mp hns
    exact ⟨b, hbS, (Finset.mem_filter.mp hb).2⟩
  choose b hb using hex
  let X : Finset (Fin n) := Finset.univ.image b
  let x : Fin n → Bool := fun p => decide (p ∈ X)
  have hXc : X.card ≤ R.card := by
    calc
      X.card ≤ (Finset.univ : Finset {g // g ∈ R'}).card := Finset.card_image_le
      _ = R'.card := by simp
      _ ≤ R.card := Finset.card_le_card (Finset.filter_subset _ _)
  have hX : ∀ p ∈ S, x p = false := by
    intro p hpS
    have hn : p ∉ X := by
      intro hpX
      obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hpX
      exact (hb g).1 hpS
    simp [x, hn]
  have hxc : (Finset.univ.filter (fun p => x p = true)).card ≤ k := by
    have : X.card ≤ k := by omega
    simpa [x] using this
  have hft : f x = false := hp x hxc hX
  have hgood : ∀ g ∈ R, g (single a) = true → g x = true := by
    intro g hg hga
    let gg : {g // g ∈ R'} := ⟨g, Finset.mem_filter.mpr ⟨hg, hga⟩⟩
    have hbx : b gg ∈ X := Finset.mem_image.mpr ⟨gg, Finset.mem_univ _, rfl⟩
    have hmono := (Finset.mem_filter.mp (hR hg)).2.2
    apply hmono (single (b gg)) x _ (hb gg).2
    intro p hp
    have he : p = b gg := by simpa [single] using hp
    subst p
    simpa [x] using hbx
  obtain ⟨g, hg, hga, hgx⟩ := live_separates
    (fun g => g (single a) = true ∧ g x = false) ⟨hat, hft⟩
    (fun u v z hz => ops_separate (single a) x u v z hz) hrun
  have := hgood g hg hga
  rw [this] at hgx
  cases hgx

lemma private_bound (C : Circuit) (n : ℕ) (S : Finset (Fin n)) (hm : Monotone2 C)
    (hl : ∀ g ∈ C.gates, g.inputs.length = 2) (w k c : ℕ)
    (hc : c ≤ k) (hs : c + 1 ≤ (singles (wire C n w)).card)
    (hp : ∀ x : Fin n → Bool, (Finset.univ.filter (fun p => x p = true)).card ≤ k →
      (∀ p ∈ S, x p = false) → wire C n w x = false) :
    c ≤ (privates C n S C.gates.length).card := by
  obtain ⟨R, hR, hrun⟩ := frontier C n S hm hl w
  exact frontier_bound S (wire C n w) k c _ hc hs hp R hR hrun

end PEqualNP.Outside.L_meta_782

open PEqualNP.Outside.L_meta_782

theorem PEqualNP.Outside.L_meta_782 : ∀ (n m k : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (c : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ i : Fin m, 2 ≤ (Finset.univ.filter (fun a : Fin n => (C.wires (List.ofFn (fun b : Fin n => decide (b = a)))).getD (o i) false = true)).card) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → (∀ (i : Fin m) (p : Fin n), (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (o i) false = true → p ∈ S i) → (∀ (i : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k → (∀ q ∈ S i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false) → (∀ i : Fin m, c i ≤ k) → (∀ i : Fin m, c i + 1 ≤ (Finset.univ.filter (fun a : Fin n => (C.wires (List.ofFn (fun b : Fin n => decide (b = a)))).getD (o i) false = true)).card) → ∑ i : Fin m, c i ≤ C.size := by
  classical
  intro n m k S C o c hinter _hmin hgates _hacc hprom hck hcs
  have hm : PEqualNP.MetaComplexity.Monotone2 C := by
    intro g hg
    obtain ⟨hop, hlen⟩ := hgates g hg
    refine ⟨?_, by omega⟩
    rcases hop with hop | hop <;> simp [hop]
  have hl : ∀ g ∈ C.gates, g.inputs.length = 2 := fun g hg => (hgates g hg).2
  let P : Fin m → Finset ℕ := fun i => privates C n (S i) C.gates.length
  have hcount : ∀ i, c i ≤ (P i).card := by
    intro i
    apply private_bound C n (S i) hm hl (o i) k (c i) (hck i)
    · exact hcs i
    · exact hprom i
  have hdis : (↑(Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint P := by
    intro i hi j hj hij
    apply Finset.disjoint_left.mpr
    intro r hri hrj
    have hpi : Private (S i) (wire C n (n + r)) := (Finset.mem_filter.mp hri).2
    have hpj : Private (S j) (wire C n (n + r)) := (Finset.mem_filter.mp hrj).2
    have hsub : singles (wire C n (n + r)) ⊆ S i ∩ S j := by
      intro a ha
      exact Finset.mem_inter.mpr ⟨hpi.2 ha, hpj.2 ha⟩
    have hh := Finset.card_le_card hsub
    have hi' := hinter i j hij
    have ht := hpi.1
    omega
  have hsub : Finset.univ.biUnion P ⊆ Finset.range C.gates.length := by
    intro r hr
    obtain ⟨i, hi, hri⟩ := Finset.mem_biUnion.mp hr
    exact (Finset.mem_filter.mp hri).1
  calc
    ∑ i, c i ≤ ∑ i, (P i).card := Finset.sum_le_sum (fun i _ => hcount i)
    _ = (Finset.univ.biUnion P).card := (Finset.card_biUnion hdis).symm
    _ ≤ (Finset.range C.gates.length).card := Finset.card_le_card hsub
    _ = C.size := by simp [PEqualNP.CircuitLowerBounds.Circuit.size]
