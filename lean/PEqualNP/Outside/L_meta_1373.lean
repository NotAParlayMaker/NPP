import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1373

open PEqualNP.CircuitLowerBounds

-- Constant propagation adapted from the checked L-meta-894 proof.
-- Splitting the gate list adapts the project OneNotSplit helper.
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma step_len (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

lemma step_lt (w : List Bool) (g : Gate) (i : ℕ) (hi : i < w.length) :
    (step w g).getD i false = w.getD i false := by
  simp [step, List.getD, List.getElem?_append_left hi]

lemma step_last (w : List Bool) (g : Gate) (k : ℕ) (hk : k = w.length) :
    (step w g).getD k false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  subst hk
  simp [step, List.getD]

def W {n : ℕ} (gs : List Gate) (x : Fin n → Bool) : List Bool :=
  gs.foldl step (List.ofFn x)

lemma W_len {n : ℕ} (gs : List Gate) (x : Fin n → Bool) :
    (W gs x).length = n + gs.length := by
  have h : ∀ (gs : List Gate) (w : List Bool), (gs.foldl step w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp
    | cons g gs ih =>
      intro w
      rw [List.foldl_cons, ih, step_len, List.length_cons]
      omega
  rw [W, h]
  simp

lemma W_snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) :
    W (gs ++ [g]) x = step (W gs x) g := by
  simp [W, List.foldl_append]

lemma W_val {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) (t : ℕ) :
    (W (gs ++ [g]) x).getD t false =
      if t = n + gs.length then g.op.eval (g.inputs.map fun i => (W gs x).getD i false)
      else (W gs x).getD t false := by
  rw [W_snoc]
  by_cases ht : t = n + gs.length
  · rw [if_pos ht, step_last _ _ _ (by rw [W_len]; exact ht)]
  · rw [if_neg ht]
    by_cases hlt : t < n + gs.length
    · exact step_lt _ _ _ (by rw [W_len]; exact hlt)
    · rw [List.getD_eq_default _ _ (by rw [step_len, W_len]; omega),
        List.getD_eq_default _ _ (by rw [W_len]; omega)]

def Rep {n : ℕ} (new : List Gate) (f : (Fin n → Bool) → Bool) : Prop :=
  (∃ c : Bool, ∀ x : Fin n → Bool, f x = c) ∨
    (∃ j : ℕ, j < n + new.length ∧ ∀ x : Fin n → Bool, (W new x).getD j false = f x)

def Fan (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2

def Ext (new new' : List Gate) : Prop :=
  new' = new ∨ ∃ h : Gate, new' = new ++ [h] ∧ Fan h

lemma rep_congr {n : ℕ} {new : List Gate} {f g : (Fin n → Bool) → Bool}
    (h : ∀ x, f x = g x) (hf : Rep new f) : Rep new g := by
  obtain rfl : f = g := funext h
  exact hf

lemma rep_mono {n : ℕ} {new new' : List Gate} (he : Ext new new')
    (f : (Fin n → Bool) → Bool) (h : Rep new f) : Rep new' f := by
  rcases he with rfl | ⟨k, rfl, _⟩
  · exact h
  · rcases h with hc | ⟨j, hj, hv⟩
    · exact Or.inl hc
    · have hne : ¬ j = n + new.length := by omega
      refine Or.inr ⟨j, by rw [List.length_append, List.length_singleton]; omega, fun x => ?_⟩
      rw [W_val, if_neg hne]
      exact hv x

lemma rep_and {n : ℕ} (new : List Gate) (f g : (Fin n → Bool) → Bool) (hf : Rep new f)
    (hg : Rep new g) : ∃ new', Ext new new' ∧ Rep new' (fun x => f x && g x) := by
  rcases hf with ⟨c1, h1⟩ | ⟨j, hj, hjv⟩
  · cases c1 with
    | false =>
      exact ⟨new, Or.inl rfl, Or.inl ⟨false, fun x => by
        show (f x && g x) = false
        simp [h1 x]⟩⟩
    | true =>
      exact ⟨new, Or.inl rfl, rep_congr (fun x => by
        show g x = (f x && g x)
        simp [h1 x]) hg⟩
  · rcases hg with ⟨c2, h2⟩ | ⟨k, hk, hkv⟩
    · cases c2 with
      | false =>
        exact ⟨new, Or.inl rfl, Or.inl ⟨false, fun x => by
          show (f x && g x) = false
          simp [h2 x]⟩⟩
      | true =>
        exact ⟨new, Or.inl rfl, Or.inr ⟨j, hj, fun x => by
          show (W new x).getD j false = (f x && g x)
          rw [hjv x]
          simp [h2 x]⟩⟩
    · refine ⟨new ++ [⟨GateOp.and, [j, k]⟩], Or.inr ⟨_, rfl, Or.inl rfl, rfl⟩,
        Or.inr ⟨n + new.length, by rw [List.length_append, List.length_singleton]; omega,
          fun x => ?_⟩⟩
      show (W (new ++ [⟨GateOp.and, [j, k]⟩]) x).getD (n + new.length) false = (f x && g x)
      rw [W_val, if_pos rfl]
      show GateOp.and.eval [(W new x).getD j false, (W new x).getD k false] = _
      rw [hjv x, hkv x]
      simp [GateOp.eval]

lemma rep_or {n : ℕ} (new : List Gate) (f g : (Fin n → Bool) → Bool) (hf : Rep new f)
    (hg : Rep new g) : ∃ new', Ext new new' ∧ Rep new' (fun x => f x || g x) := by
  rcases hf with ⟨c1, h1⟩ | ⟨j, hj, hjv⟩
  · cases c1 with
    | true =>
      exact ⟨new, Or.inl rfl, Or.inl ⟨true, fun x => by
        show (f x || g x) = true
        simp [h1 x]⟩⟩
    | false =>
      exact ⟨new, Or.inl rfl, rep_congr (fun x => by
        show g x = (f x || g x)
        simp [h1 x]) hg⟩
  · rcases hg with ⟨c2, h2⟩ | ⟨k, hk, hkv⟩
    · cases c2 with
      | true =>
        exact ⟨new, Or.inl rfl, Or.inl ⟨true, fun x => by
          show (f x || g x) = true
          simp [h2 x]⟩⟩
      | false =>
        exact ⟨new, Or.inl rfl, Or.inr ⟨j, hj, fun x => by
          show (W new x).getD j false = (f x || g x)
          rw [hjv x]
          simp [h2 x]⟩⟩
    · refine ⟨new ++ [⟨GateOp.or, [j, k]⟩], Or.inr ⟨_, rfl, Or.inr rfl, rfl⟩,
        Or.inr ⟨n + new.length, by rw [List.length_append, List.length_singleton]; omega,
          fun x => ?_⟩⟩
      show (W (new ++ [⟨GateOp.or, [j, k]⟩]) x).getD (n + new.length) false = (f x || g x)
      rw [W_val, if_pos rfl]
      show GateOp.or.eval [(W new x).getD j false, (W new x).getD k false] = _
      rw [hjv x, hkv x]
      simp [GateOp.eval]

lemma rep_input {n : ℕ} (ρ : (Fin n → Bool) → Fin n → Bool)
    (hρ : ∀ i : Fin n, (∃ c : Bool, ∀ x : Fin n → Bool, ρ x i = c) ∨
      (∀ x : Fin n → Bool, ρ x i = x i)) (t : ℕ) :
    Rep ([] : List Gate) (fun x => (W [] (ρ x)).getD t false) := by
  by_cases ht : t < n
  · have hval : ∀ y : Fin n → Bool, (W [] y).getD t false = y ⟨t, ht⟩ := by
      intro y
      show (List.ofFn y).getD t false = _
      rw [List.getD_eq_getElem _ _ (by simpa using ht)]
      simp
    rcases hρ ⟨t, ht⟩ with ⟨c, hc⟩ | hid
    · exact Or.inl ⟨c, fun x => by
        show (W [] (ρ x)).getD t false = c
        rw [hval, hc x]⟩
    · exact Or.inr ⟨t, by simpa using ht, fun x => by
        show (W [] x).getD t false = (W [] (ρ x)).getD t false
        rw [hval, hval, hid x]⟩
  · exact Or.inl ⟨false, fun x =>
      List.getD_eq_default _ _ (by rw [W_len, List.length_nil]; omega)⟩

lemma gate_rep {n : ℕ} (ρ : (Fin n → Bool) → Fin n → Bool) (old new : List Gate)
    (op : GateOp) (l : List ℕ) (hop : op = GateOp.and ∨ op = GateOp.or) (hlen : l.length ≤ 2)
    (h : ∀ t : ℕ, Rep new (fun x => (W old (ρ x)).getD t false)) :
    ∃ new', Ext new new' ∧ (l.length = 2 ∨ new' = new) ∧
      Rep new' (fun x => op.eval (l.map fun i => (W old (ρ x)).getD i false)) := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c3, rest⟩⟩⟩
  · rcases hop with rfl | rfl
    · exact ⟨new, Or.inl rfl, Or.inr rfl, Or.inl ⟨true, fun x => by simp [GateOp.eval]⟩⟩
    · exact ⟨new, Or.inl rfl, Or.inr rfl, Or.inl ⟨false, fun x => by simp [GateOp.eval]⟩⟩
  · rcases hop with rfl | rfl
    · exact ⟨new, Or.inl rfl, Or.inr rfl, rep_congr (fun x => by simp [GateOp.eval]) (h a)⟩
    · exact ⟨new, Or.inl rfl, Or.inr rfl, rep_congr (fun x => by simp [GateOp.eval]) (h a)⟩
  · rcases hop with rfl | rfl
    · obtain ⟨new', he, hr⟩ := rep_and new _ _ (h a) (h b)
      exact ⟨new', he, Or.inl rfl, rep_congr (fun x => by simp [GateOp.eval]) hr⟩
    · obtain ⟨new', he, hr⟩ := rep_or new _ _ (h a) (h b)
      exact ⟨new', he, Or.inl rfl, rep_congr (fun x => by simp [GateOp.eval]) hr⟩
  · simp only [List.length_cons] at hlen
    omega

def paid (gs : List Gate) : ℕ := (gs.filter fun g => decide (g.inputs.length = 2)).length

lemma paid_snoc (gs : List Gate) (g : Gate) :
    paid (gs ++ [g]) = paid gs + (if g.inputs.length = 2 then 1 else 0) := by
  by_cases h : g.inputs.length = 2 <;> simp [paid, List.filter_append, h]

lemma paid_append (gs hs : List Gate) : paid (gs ++ hs) = paid gs + paid hs := by
  simp [paid, List.filter_append]

lemma paid_le (gs : List Gate) : paid gs ≤ gs.length := List.length_filter_le _ _

def Inv {n : ℕ} (ρ : (Fin n → Bool) → Fin n → Bool) (old : List Gate) : Prop :=
  ∃ new : List Gate, (∀ g ∈ new, Fan g) ∧ new.length ≤ paid old ∧
    ∀ t : ℕ, Rep new (fun x => (W old (ρ x)).getD t false)

lemma inv_step {n : ℕ} (ρ : (Fin n → Bool) → Fin n → Bool) (old : List Gate) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (hlen : g.inputs.length ≤ 2)
    (h : Inv ρ old) : Inv ρ (old ++ [g]) := by
  obtain ⟨new, hfan, hl, hrep⟩ := h
  obtain ⟨new', he, hpaid, hr⟩ := gate_rep ρ old new g.op g.inputs hop hlen hrep
  refine ⟨new', ?_, ?_, ?_⟩
  · rcases he with rfl | ⟨k, rfl, hk⟩
    · exact hfan
    · intro q hq
      rcases List.mem_append.mp hq with hq | hq
      · exact hfan q hq
      · rw [List.mem_singleton] at hq
        rw [hq]
        exact hk
  · rw [paid_snoc]
    rcases hpaid with htwo | hsame
    · rw [if_pos htwo]
      rcases he with rfl | ⟨k, rfl, hk⟩
      · omega
      · simpa using Nat.succ_le_succ hl
    · rw [hsame]
      exact hl.trans (Nat.le_add_right _ _)
  · intro t
    by_cases ht : t = n + old.length
    · exact rep_congr (fun x => by
        show _ = (W (old ++ [g]) (ρ x)).getD t false
        rw [W_val, if_pos ht]) hr
    · exact rep_congr (fun x => by
        show _ = (W (old ++ [g]) (ρ x)).getD t false
        rw [W_val, if_neg ht]) (rep_mono he _ (hrep t))

lemma inv_all {n : ℕ} (ρ : (Fin n → Bool) → Fin n → Bool)
    (hρ : ∀ i : Fin n, (∃ c : Bool, ∀ x : Fin n → Bool, ρ x i = c) ∨
      (∀ x : Fin n → Bool, ρ x i = x i)) (gates : List Gate)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    Inv ρ gates := by
  have hall : ∀ (post pre : List Gate), pre ++ post = gates → Inv ρ pre → Inv ρ gates := by
    intro post
    induction post with
    | nil =>
      intro pre h hinv
      rw [List.append_nil] at h
      rw [← h]
      exact hinv
    | cons g post ih =>
      intro pre h hinv
      have hmem : g ∈ gates := by
        rw [← h]
        simp
      exact ih (pre ++ [g]) (by rw [List.append_assoc]; exact h)
        (inv_step ρ pre g (hg g hmem).1 (hg g hmem).2 hinv)
  exact hall gates [] (List.nil_append _)
    ⟨[], by simp, le_refl _, rep_input ρ hρ⟩

lemma inv_final {n : ℕ} (ρ : (Fin n → Bool) → Fin n → Bool) (gates : List Gate)
    (h : Inv ρ gates) :
    ∃ (gates' : List Gate) (r : ℕ → ℕ), (∀ g ∈ gates', Fan g) ∧ gates'.length ≤ paid gates ∧
      ∀ o : ℕ, (∃ x y : Fin n → Bool,
        (W gates (ρ x)).getD o false ≠ (W gates (ρ y)).getD o false) →
        ∀ x : Fin n → Bool, (W gates' x).getD (r o) false = (W gates (ρ x)).getD o false := by
  obtain ⟨new, hfan, hl, hrep⟩ := h
  have hsel : ∀ o : ℕ, ∃ j : ℕ,
      (∃ c : Bool, ∀ x : Fin n → Bool, (W gates (ρ x)).getD o false = c) ∨
      (∀ x : Fin n → Bool, (W new x).getD j false = (W gates (ρ x)).getD o false) := by
    intro o
    rcases hrep o with hc | ⟨j, _, hj⟩
    · exact ⟨0, Or.inl hc⟩
    · exact ⟨j, Or.inr hj⟩
  choose r hr using hsel
  refine ⟨new, r, hfan, hl, ?_⟩
  intro o hne x
  rcases hr o with ⟨c, hc⟩ | hj
  · obtain ⟨x1, y1, hxy⟩ := hne
    exact absurd ((hc x1).trans (hc y1).symm) hxy
  · exact hj x

theorem on1_split : ∀ gates : List PEqualNP.CircuitLowerBounds.Gate,
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) →
    (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not →
        (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) →
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∨
    ∃ (pre post : List PEqualNP.CircuitLowerBounds.Gate) (ins : List ℕ),
      gates = pre ++ ({ op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := ins } :
        PEqualNP.CircuitLowerBounds.Gate) :: post ∧
      (∀ g ∈ pre, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      (∀ g ∈ post, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) := by
  intro gates hops huniq
  by_cases hex : ∃ g ∈ gates, g.op = GateOp.not
  · right
    obtain ⟨g, hg, hop⟩ := hex
    obtain ⟨s, t, rfl⟩ := List.append_of_mem hg
    -- the NOT gate sits at index `s.length`
    have hslot : ((s ++ g :: t).get ⟨s.length, by simp⟩).op = GateOp.not := by
      simp [hop]
    have nf : ∀ g' ∈ s ++ g :: t, g'.op ≠ GateOp.not → (g'.op = GateOp.and ∨
        g'.op = GateOp.or) ∧ g'.inputs.length ≤ 2 := by
      intro g' hg' hne
      obtain ⟨h1 | h1 | h1, h2⟩ := hops g' hg'
      · exact ⟨Or.inl h1, h2⟩
      · exact ⟨Or.inr h1, h2⟩
      · exact absurd h1 hne
    refine ⟨s, t, g.inputs, ?_, ?_, ?_⟩
    · cases g with
      | mk op ins => simp only at hop; subst hop; rfl
    · intro g' hg'
      apply nf g' (by simp [hg'])
      intro hn
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg'
      have := huniq ⟨i, by simp; omega⟩ ⟨s.length, by simp⟩
        (by simp [List.getElem_append_left hi, hn]) hslot
      simp only [Fin.mk.injEq] at this; omega
    · intro g' hg'
      apply nf g' (by simp [hg'])
      intro hn
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg'
      have := huniq ⟨s.length + 1 + i, by simp; omega⟩ ⟨s.length, by simp⟩
        (by
          simp only [List.get_eq_getElem]
          rw [List.getElem_append_right (by omega)]
          simp only [show s.length + 1 + i - s.length = i + 1 by omega,
            List.getElem_cons_succ]
          exact hn) hslot
      simp only [Fin.mk.injEq] at this; omega
  · left
    intro g hg
    obtain ⟨h1 | h1 | h1, h2⟩ := hops g hg
    · exact ⟨Or.inl h1, h2⟩
    · exact ⟨Or.inr h1, h2⟩
    · exact absurd ⟨g, hg, h1⟩ hex



open Finset

def planeSize (q : ℕ) : ℕ := q ^ 2 + q + 1

def through {q : ℕ} (S : Fin (planeSize q) → Finset (Fin (planeSize q)))
    (p : Fin (planeSize q)) : Finset (Fin (planeSize q)) :=
  univ.filter (fun l => p ∈ S l)

lemma commonLine {q : ℕ} (S : Fin (planeSize q) → Finset (Fin (planeSize q)))
    (hsize : ∀ l, (S l).card = q + 1)
    (hinter : ∀ l m, l ≠ m → (S l ∩ S m).card ≤ 1)
    (hdeg : ∀ p, (through S p).card = q + 1)
    {p v : Fin (planeSize q)} (hpv : p ≠ v) : ∃ l, p ∈ S l ∧ v ∈ S l := by
  classical
  let pencils := (through S p).biUnion (fun l => (S l).erase p)
  have hd : (through S p : Set (Fin (planeSize q))).PairwiseDisjoint (fun l => (S l).erase p) := by
    intro l hl m hm hlm
    apply Finset.disjoint_left.mpr
    intro u hu hv
    have hpL : p ∈ S l := (Finset.mem_filter.mp hl).2
    have hpM : p ∈ S m := (Finset.mem_filter.mp hm).2
    have hu' := Finset.mem_erase.mp hu
    have hv' := Finset.mem_erase.mp hv
    have hsub : ({p, u} : Finset (Fin (planeSize q))) ⊆ S l ∩ S m := by
      simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff, Finset.mem_inter]
      exact ⟨⟨hpL, hpM⟩, hu'.2, hv'.2⟩
    have htwo := Finset.card_le_card hsub
    simp [hu'.1.symm] at htwo
    have hone := hinter l m hlm
    omega
  have hcard : pencils.card = (univ.erase p).card := by
    rw [show pencils = (through S p).biUnion (fun l => (S l).erase p) by rfl,
      Finset.card_biUnion hd]
    have he : ∀ l ∈ through S p, ((S l).erase p).card = q := by
      intro l hl
      rw [Finset.card_erase_of_mem (Finset.mem_filter.mp hl).2, hsize]
      omega
    rw [Finset.sum_congr rfl he]
    rw [Finset.sum_const, hdeg, Nat.nsmul_eq_mul,
      Finset.card_erase_of_mem (Finset.mem_univ p), Finset.card_univ, Fintype.card_fin]
    simp only [planeSize, Nat.add_sub_cancel]
    ring
  have hs : pencils ⊆ univ.erase p := by
    intro u hu
    rcases Finset.mem_biUnion.mp hu with ⟨l, _, hu'⟩
    exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hu').1, Finset.mem_univ _⟩
  have he := Finset.eq_of_subset_of_card_le hs hcard.ge
  have hv : v ∈ pencils := by rw [he]; simp [hpv.symm]
  obtain ⟨l, hl, hv'⟩ := Finset.mem_biUnion.mp hv
  exact ⟨l, (Finset.mem_filter.mp hl).2, (Finset.mem_erase.mp hv').2⟩

lemma linesHit {q : ℕ} (S : Fin (planeSize q) → Finset (Fin (planeSize q)))
    (hsize : ∀ l, (S l).card = q + 1)
    (hinter : ∀ l m, l ≠ m → (S l ∩ S m).card ≤ 1)
    (hdeg : ∀ p, (through S p).card = q + 1)
    (Y : Finset (Fin (planeSize q))) :
    (univ.filter (fun l => ¬ Disjoint (S l) Y)).card ≤ Y.card * q + 1 := by
  classical
  by_cases hy : Y.Nonempty
  · obtain ⟨p, hp⟩ := hy
    let rest := Y.erase p
    have hd : ∀ v ∈ rest, (through S v \ through S p).card ≤ q := by
      intro v hv
      obtain ⟨l, hpl, hvl⟩ := commonLine S hsize hinter hdeg (Finset.mem_erase.mp hv).1.symm
      have hmem : l ∈ through S v ∩ through S p := by simp [through, hpl, hvl]
      have hpos := Finset.card_pos.mpr ⟨l, hmem⟩
      have he := Finset.card_sdiff_add_card_inter (through S v) (through S p)
      rw [hdeg] at he
      omega
    have hsub : univ.filter (fun l => ¬ Disjoint (S l) Y) ⊆
        through S p ∪ rest.biUnion (fun v => through S v \ through S p) := by
      intro l hl
      by_cases hs : l ∈ through S p
      · exact Finset.mem_union_left _ hs
      · have hn := (Finset.mem_filter.mp hl).2
        rw [Finset.disjoint_left] at hn
        push Not at hn
        obtain ⟨v, hv, hvY⟩ := hn
        have hv' : v ≠ p := by rintro rfl; exact hs (by simp [through, hv])
        exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
          ⟨v, Finset.mem_erase.mpr ⟨hv', hvY⟩, Finset.mem_sdiff.mpr ⟨by simp [through, hv], hs⟩⟩)
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le (through S p) (rest.biUnion (fun v => through S v \ through S p))
    have h3 := Finset.card_biUnion_le_card_mul rest (fun v => through S v \ through S p) q hd
    have he : rest.card + 1 = Y.card := Finset.card_erase_add_one hp
    rw [← he, Nat.add_mul, Nat.one_mul]
    rw [hdeg] at h2
    omega
  · have hY : Y = ∅ := Finset.not_nonempty_iff_eq_empty.mp hy
    simp [hY]


def SmallBound : Prop := (∀ (n m k : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (c : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ i : Fin m, 2 ≤ (S i).card) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → (∀ (i : Fin m) (p : Fin n), (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (o i) false = true ↔ p ∈ S i) → (∀ (i : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k → (∀ q ∈ S i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false) → (∀ i : Fin m, c i ≤ k) → (∀ i : Fin m, c i + 1 ≤ (S i).card) → ∑ i : Fin m, c i ≤ C.size)

def onSet {n : ℕ} (A : Finset (Fin n)) (i : Fin n) : Bool := decide (i ∈ A)

def support {n : ℕ} (x : Fin n → Bool) : Finset (Fin n) :=
  Finset.univ.filter (fun i => x i = true)

lemma support_onSet {n : ℕ} (A : Finset (Fin n)) : support (onSet A) = A := by
  ext i
  simp [support, onSet]

def face {n : ℕ} (T : Finset (Fin n)) (x : Fin n → Bool) (i : Fin n) : Bool :=
  if i ∈ T then true else x i

lemma face_empty {n : ℕ} (x : Fin n → Bool) : face ∅ x = x := by
  ext i
  simp [face]

lemma face_or {n : ℕ} {T S : Finset (Fin n)} (hd : Disjoint S T) (x : Fin n → Bool) :
    (∃ v ∈ S, face T x v = true) ↔ ∃ v ∈ S, x v = true := by
  have hx : ∀ v ∈ S, face T x v = x v := fun v hv => by
    rw [face, if_neg (fun ht => Finset.disjoint_left.mp hd hv ht)]
  constructor
  · rintro ⟨v, hv, h⟩
    exact ⟨v, hv, (hx v hv).symm.trans h⟩
  · rintro ⟨v, hv, h⟩
    exact ⟨v, hv, (hx v hv).trans h⟩

lemma face_bound (small : SmallBound) {n m q k : ℕ} (hq : 1 ≤ q)
    (S : Fin m → Finset (Fin n))
    (hsize : ∀ i, (S i).card = q + 1)
    (hinter : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (T : Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hval : ∀ i x, (support x).card ≤ k →
      Circuit.eval ⟨gates, out i⟩ (List.ofFn (face T x)) = decide (∃ v ∈ S i, x v = true)) :
    m * min k q ≤ paid gates := by
  classical
  by_cases hk : k = 0
  · simp [hk]
  have hk1 : 1 ≤ k := by omega
  have hρ : ∀ i : Fin n, (∃ c : Bool, ∀ x : Fin n → Bool, face T x i = c) ∨
      (∀ x : Fin n → Bool, face T x i = x i) := by
    intro i
    by_cases hi : i ∈ T
    · exact Or.inl ⟨true, fun x => by simp [face, hi]⟩
    · exact Or.inr (fun x => by simp [face, hi])
  obtain ⟨gs, r, hnorm, hlen, hcorrect⟩ := inv_final (face T) gates (inv_all _ hρ gates hg)
  have hnon : ∀ i : Fin m, ∃ x y : Fin n → Bool,
      (W gates (face T x)).getD (out i) false ≠ (W gates (face T y)).getD (out i) false := by
    intro i
    obtain ⟨p, hp⟩ := Finset.card_pos.mp (by rw [hsize]; omega : 0 < (S i).card)
    refine ⟨fun _ => false, onSet {p}, ?_⟩
    change Circuit.eval ⟨gates, out i⟩ (List.ofFn (face T (fun _ => false))) ≠
      Circuit.eval ⟨gates, out i⟩ (List.ofFn (face T (onSet {p})))
    rw [hval _ _ (by simp [support]), hval _ _ (by simpa [support_onSet] using hk1)]
    simp [onSet, hp]
  have hv : ∀ i x, (support x).card ≤ k →
      (Circuit.wires ⟨gs, 0⟩ (List.ofFn x)).getD (r (out i)) false =
        decide (∃ v ∈ S i, x v = true) := by
    intro i x hx
    exact (hcorrect (out i) (hnon i) x).trans (hval i x hx)
  have total := small n m k S ⟨gs, 0⟩ (fun i => r (out i)) (fun _ => min k q) hinter
    (fun i => by rw [hsize]; omega) hnorm
    (fun i p => by
      have e := hv i (onSet {p}) (by simpa [support_onSet] using hk1)
      have hs : (fun q : Fin n => decide (q = p)) = onSet {p} := by
        funext q
        simp [onSet]
      rw [hs, e]
      simp [onSet])
    (fun i x hx hz => by
      rw [hv i x hx]
      have hfalse : ¬ ∃ v ∈ S i, x v = true := by
        rintro ⟨v, hv', ht⟩
        simp [hz v hv'] at ht
      simp [hfalse])
    (fun _ => min_le_left _ _)
    (fun i => by rw [hsize]; exact Nat.add_le_add_right (min_le_right _ _) 1)
  exact (by simpa [Circuit.size, Nat.mul_comm] using total : m * min k q ≤ gs.length).trans hlen

def readsNot {n : ℕ} (pre : List Gate) (ins : List ℕ) (x : Fin n → Bool) : Bool :=
  (ins.map fun i => (W pre x).getD i false).headD false

lemma W_mono {n : ℕ} (gs : List Gate)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : Fin n → Bool) (hxy : ∀ p, x p = true → y p = true) :
    ∀ i, (W gs x).getD i false = true → (W gs y).getD i false = true := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro i hi
    by_cases hv : i < n
    · change (List.ofFn x).getD i false = true at hi
      change (List.ofFn y).getD i false = true
      have eX : (List.ofFn x).getD i false = x ⟨i, hv⟩ := by
        rw [List.getD_eq_getElem _ _ (by simpa using hv)]
        simp
      have eY : (List.ofFn y).getD i false = y ⟨i, hv⟩ := by
        rw [List.getD_eq_getElem _ _ (by simpa using hv)]
        simp
      exact eY.trans (hxy _ (eX.symm.trans hi))
    · rw [List.getD_eq_default _ _ (by rw [W_len, List.length_nil]; omega)] at hi
      contradiction
  | append_singleton pre g ih =>
    have hpre : ∀ a ∈ pre, a.op = GateOp.and ∨ a.op = GateOp.or := fun a ha =>
      hg a (List.mem_append_left _ ha)
    intro i hi
    rw [W_val] at hi ⊢
    by_cases e : i = n + pre.length
    · rw [if_pos e] at hi ⊢
      rcases hg g (by simp) with hop | hop
      · rw [hop] at hi ⊢
        simp only [GateOp.eval, List.all_eq_true, List.mem_map, id] at hi ⊢
        rintro b ⟨j, hj, rfl⟩
        exact ih hpre j (hi _ ⟨j, hj, rfl⟩)
      · rw [hop] at hi ⊢
        simp only [GateOp.eval, List.any_eq_true, List.mem_map, id] at hi ⊢
        obtain ⟨b, ⟨j, hj, rfl⟩, hb⟩ := hi
        exact ⟨_, ⟨j, hj, rfl⟩, ih hpre j hb⟩
    · rw [if_neg e] at hi ⊢
      exact ih hpre i hi

lemma readsNot_mono {n : ℕ} (pre : List Gate) (ins : List ℕ)
    (hpre : ∀ g ∈ pre, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x y : Fin n → Bool) (hxy : ∀ p, x p = true → y p = true)
    (hx : readsNot pre ins x = true) : readsNot pre ins y = true := by
  cases ins with
  | nil => simp [readsNot] at hx
  | cons j js =>
    simp only [readsNot, List.map_cons, List.headD_cons] at hx ⊢
    exact W_mono pre (fun g hg => (hpre g hg).1) x y hxy j hx

def constGate (b : Bool) : Gate := ⟨if b then GateOp.and else GateOp.or, []⟩

def replacement (pre post : List Gate) (b : Bool) : List Gate :=
  pre ++ constGate b :: post

lemma replacement_ops (pre post : List Gate) (b : Bool)
    (hpre : ∀ g ∈ pre, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hpost : ∀ g ∈ post, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ g ∈ replacement pre post b, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  rcases List.mem_append.mp hg with ha | hb
  · exact hpre _ ha
  · rcases List.mem_cons.mp hb with rfl | hz
    · cases b <;> simp [constGate]
    · exact hpost _ hz

lemma replacement_paid (pre post : List Gate) (b : Bool) :
    paid (replacement pre post b) ≤ pre.length + post.length := by
  rw [replacement, paid_append]
  have he : paid (constGate b :: post) = paid post := by simp [paid, constGate]
  rw [he]
  exact Nat.add_le_add (paid_le pre) (paid_le post)

lemma W_join {n : ℕ} (pre post : List Gate) (g : Gate) (x : Fin n → Bool) :
    W (pre ++ g :: post) x = post.foldl step (step (W pre x) g) := by
  simp only [W, List.foldl_append, List.foldl_cons]

lemma replacement_eval {n : ℕ} (pre post : List Gate) (ins : List ℕ) (b : Bool)
    (o : ℕ) (x : Fin n → Bool) (hb : readsNot pre ins x = b) :
    Circuit.eval ⟨replacement pre post (!b), o⟩ (List.ofFn x) =
    Circuit.eval ⟨pre ++ ⟨GateOp.not, ins⟩ :: post, o⟩ (List.ofFn x) := by
  change (W (pre ++ constGate (!b) :: post) x).getD o false =
    (W (pre ++ ⟨GateOp.not, ins⟩ :: post) x).getD o false
  rw [W_join, W_join]
  have hs : step (W pre x) (constGate (!b)) = step (W pre x) ⟨GateOp.not, ins⟩ := by
    unfold readsNot at hb
    cases b
    · change W pre x ++ [true] = W pre x ++ [!((ins.map fun i => (W pre x).getD i false).headD false)]
      rw [hb]; rfl
    · change W pre x ++ [false] = W pre x ++ [!((ins.map fun i => (W pre x).getD i false).headD false)]
      rw [hb]; rfl
  rw [hs]

lemma onSet_support {n : ℕ} (x : Fin n → Bool) : onSet (support x) = x := by
  ext i
  cases h : x i <;> simp [onSet, support, h]

lemma one_le_cost (q : ℕ) (hq : 2 ≤ q) :
    1 + max (planeSize q * min (1 - 1) q) (q * (planeSize q - (1 * q + 1))) ≤ planeSize q * q := by
  have hN : 1 ≤ planeSize q := by simp [planeSize]
  have hsub : planeSize q - (q + 1) ≤ planeSize q - 1 := by omega
  have hmul := Nat.mul_le_mul_left q hsub
  have hsum : q * (planeSize q - 1) + q = planeSize q * q := by
    calc
      _ = q * ((planeSize q - 1) + 1) := by rw [Nat.mul_add, Nat.mul_one]
      _ = _ := by rw [Nat.sub_add_cancel hN, Nat.mul_comm]
  simp only [Nat.sub_self, Nat.zero_min, Nat.mul_zero, zero_max, Nat.one_mul]
  omega

lemma solve (small : SmallBound) (q : ℕ)
    (S : Fin (planeSize q) → Finset (Fin (planeSize q)))
    (gates : List Gate) (out : Fin (planeSize q) → ℕ)
    (hq : 2 ≤ q) (hsize : ∀ i, (S i).card = q + 1)
    (hinter : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hdeg : ∀ p, (through S p).card = q + 1)
    (hops : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (huniq : ∀ i j : Fin gates.length, (gates.get i).op = GateOp.not →
      (gates.get j).op = GateOp.not → i = j)
    (hval : ∀ i (x : Fin (planeSize q) → Bool),
      Circuit.eval ⟨gates, out i⟩ (List.ofFn x) = decide (∃ v ∈ S i, x v = true)) :
    ∃ w : ℕ, 1 ≤ w ∧ 1 + max (planeSize q * min (w - 1) q)
        (q * (planeSize q - (w * q + 1))) ≤ gates.length := by
  classical
  have hq1 : 1 ≤ q := by omega
  have full (gs : List Gate)
      (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
      (hr : ∀ i (x : Fin (planeSize q) → Bool),
        Circuit.eval ⟨gs, out i⟩ (List.ofFn x) = decide (∃ v ∈ S i, x v = true)) :
      planeSize q * q ≤ paid gs := by
    have h := face_bound small (k := q) hq1 S hsize hinter ∅ gs out hg
      (by intro i x _; simpa only [face_empty] using hr i x)
    simpa using h
  rcases on1_split gates hops huniq with hmono | ⟨pre, post, ins, rfl, hpre, hpost⟩
  · exact ⟨1, by decide, (one_le_cost q hq).trans ((full gates hmono hval).trans (paid_le gates))⟩
  let f := readsNot (n := planeSize q) pre ins
  have hmono (x y : Fin (planeSize q) → Bool) (hxy : ∀ p, x p = true → y p = true) :
      f x = true → f y = true := readsNot_mono pre ins hpre x y hxy
  have repl (b : Bool) (i : Fin (planeSize q)) (x : Fin (planeSize q) → Bool) (hx : f x = b) :
      Circuit.eval ⟨replacement pre post (!b), out i⟩ (List.ofFn x) =
        decide (∃ v ∈ S i, x v = true) :=
    (replacement_eval pre post ins b (out i) x hx).trans (hval i x)
  have finishTrivial (b : Bool) (hb : ∀ x, f x = b) :
      ∃ w : ℕ, 1 ≤ w ∧ 1 + max (planeSize q * min (w - 1) q)
        (q * (planeSize q - (w * q + 1))) ≤ (pre ++ ⟨GateOp.not, ins⟩ :: post).length := by
    have h := full (replacement pre post (!b)) (replacement_ops _ _ _ hpre hpost)
      (fun i x => repl b i x (hb x))
    have s := (one_le_cost q hq).trans (h.trans (replacement_paid pre post (!b)))
    refine ⟨1, by decide, ?_⟩
    simp only [List.length_append, List.length_cons]
    omega
  let P (k : ℕ) := ∃ Y : Finset (Fin (planeSize q)), Y.card = k ∧ f (onSet Y) = true
  by_cases hex : ∃ k, P k
  · let w := Nat.find hex
    obtain ⟨Y, hY, hfY⟩ := Nat.find_spec hex
    change Y.card = w at hY
    by_cases hw : w = 0
    · apply finishTrivial true
      intro x
      apply hmono (onSet Y) x _ hfY
      have he : Y = ∅ := Finset.card_eq_zero.mp (hY.trans hw)
      simp [he, onSet]
    have hw1 : 1 ≤ w := by omega
    have hd (x : Fin (planeSize q) → Bool) (hx : (support x).card ≤ w - 1) : f x = false := by
      cases hv : f x
      · rfl
      · have h := Nat.find_min' hex (show P (support x).card from
          ⟨support x, rfl, by rw [onSet_support]; exact hv⟩)
        change w ≤ (support x).card at h
        omega
    have hdown := face_bound small (k := w - 1) hq1 S hsize hinter ∅
      (replacement pre post true) out (replacement_ops _ _ _ hpre hpost)
      (by intro i x hx; simpa only [face_empty, Bool.not_false] using repl false i x (hd x hx))
    let A : Finset (Fin (planeSize q)) := Finset.univ.filter (fun i => Disjoint (S i) Y)
    let e : Fin A.card ↪ Fin (planeSize q) := (A.orderEmbOfFin rfl).toEmbedding
    have hgood (i : Fin A.card) : Disjoint (S (e i)) Y := by
      have he : e i ∈ A := A.orderEmbOfFin_mem rfl i
      exact (Finset.mem_filter.mp he).2
    have hcount : planeSize q - (w * q + 1) ≤ A.card := by
      have h1 := linesHit S hsize hinter hdeg Y
      rw [hY] at h1
      have h2 := Finset.card_filter_add_card_filter_not (s := Finset.univ)
        (fun l : Fin (planeSize q) => Disjoint (S l) Y)
      change A.card + _ = _ at h2
      simp only [Finset.card_univ, Fintype.card_fin] at h2
      omega
    have hu (x : Fin (planeSize q) → Bool) : f (face Y x) = true := by
      apply hmono (onSet Y) (face Y x) _ hfY
      intro p hp
      have hmem : p ∈ Y := by simpa [onSet] using hp
      simp [face, hmem]
    have hup := face_bound small (k := q) hq1 (S ∘ e) (fun i => hsize (e i))
      (fun i j hij => hinter (e i) (e j) (fun he => hij (e.injective he))) Y
      (replacement pre post false) (out ∘ e) (replacement_ops _ _ _ hpre hpost)
      (by
        intro i x _
        have he := repl true (e i) (face Y x) (hu x)
        simp only [Bool.not_true] at he
        change Circuit.eval ⟨replacement pre post false, out (e i)⟩ (List.ofFn (face Y x)) = _
        rw [he]
        exact Bool.eq_iff_iff.mpr (by
          simpa only [decide_eq_true_eq, Function.comp_apply] using face_or (hgood i) x))
    have h1 := hdown.trans (replacement_paid pre post true)
    have h2 : q * (planeSize q - (w * q + 1)) ≤ pre.length + post.length := by
      have h3 := (Nat.mul_le_mul_right q hcount).trans
        (by simpa using hup : A.card * q ≤ paid (replacement pre post false))
      simpa [Nat.mul_comm] using h3.trans (replacement_paid pre post false)
    have h3 := max_le h1 h2
    refine ⟨w, hw1, ?_⟩
    simp only [List.length_append, List.length_cons]
    omega
  · apply finishTrivial false
    intro x
    cases hv : f x
    · rfl
    · exact (hex ⟨(support x).card, support x, rfl, by rw [onSet_support]; exact hv⟩).elim

end PEqualNP.Outside.L_meta_1373

theorem PEqualNP.Outside.L_meta_1373 : (∀ (n m k : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (c : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ i : Fin m, 2 ≤ (S i).card) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → (∀ (i : Fin m) (p : Fin n), (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (o i) false = true ↔ p ∈ S i) → (∀ (i : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k → (∀ q ∈ S i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false) → (∀ i : Fin m, c i ≤ k) → (∀ i : Fin m, c i + 1 ≤ (S i).card) → ∑ i : Fin m, c i ≤ C.size) → (∀ (n : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate) (T Z : Finset (Fin n)), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (r : ℕ → ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∧ gates'.length ≤ gates.length ∧ ∀ o : ℕ, (∃ x y : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i)) ≠ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else y i))) → ∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', r o⟩ (List.ofFn x) = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i))) → ∀ (q : ℕ) (S : Fin (q^2+q+1) → Finset (Fin (q^2+q+1))) (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin (q^2+q+1) → ℕ), 2 ≤ q → (∀ i, (S i).card = q + 1) → (∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ p, (Finset.univ.filter (fun i => p ∈ S i)).card = q + 1) → (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ (w : Fin (q^2+q+1)) (x : Fin (q^2+q+1) → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∃ v ∈ S w, x v = true)) → ∃ w : ℕ, 1 ≤ w ∧ 1 + max ((q^2+q+1) * min (w - 1) q) (q * ((q^2+q+1) - (w * q + 1))) ≤ gates.length := by
  intro hsmall _ q S gates out hq hsize hinter hdeg hops huniq hval
  exact PEqualNP.Outside.L_meta_1373.solve hsmall q S gates out hq hsize hinter hdeg hops huniq hval
