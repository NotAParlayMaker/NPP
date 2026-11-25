import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.GetD
import Mathlib.Data.Finset.Sort
import Mathlib.Logic.Relation
import PEqualNP.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Union

namespace PEqualNP.Outside.L_meta_12408_aux

open scoped BigOperators

abbrev Color := Finset (Fin 4)

def labelUnion : List Color → Color
  | [] => ∅
  | label :: rest => label ∪ labelUnion rest

def mass (uses : List Color) : Nat := (uses.map Finset.card).sum

def pairUses (uses : List Color) : List Color := uses.filter (fun s => s.card == 2)

def otherUses (uses : List Color) : List Color := uses.filter (fun s => !(s.card == 2))

def pairLabels (uses : List Color) : Finset Color := (pairUses uses).toFinset

theorem mem_labelUnion (i : Fin 4) (uses : List Color) :
    i ∈ labelUnion uses ↔ ∃ label ∈ uses, i ∈ label := by
  induction uses with
  | nil => simp [labelUnion]
  | cons a rest ih =>
      rw [labelUnion, Finset.mem_union, ih]
      constructor
      · rintro (ha | ⟨b, hb, hi⟩)
        · exact ⟨a, List.mem_cons_self, ha⟩
        · exact ⟨b, List.mem_cons_of_mem _ hb, hi⟩
      · rintro ⟨b, hb, hi⟩
        rcases List.mem_cons.mp hb with rfl | hb
        · exact Or.inl hi
        · exact Or.inr ⟨b, hb, hi⟩

theorem labelUnion_card_le (uses : List Color) : (labelUnion uses).card ≤ mass uses := by
  induction uses with
  | nil => simp [labelUnion, mass]
  | cons a rest ih =>
      change (a ∪ labelUnion rest).card ≤ a.card + mass rest
      exact (Finset.card_union_le _ _).trans (Nat.add_le_add_left ih _)

theorem union_of_filtered (uses : List Color) :
    labelUnion uses ⊆ labelUnion (pairUses uses) ∪ labelUnion (otherUses uses) := by
  intro i hi
  obtain ⟨label, hm, hp⟩ := (mem_labelUnion i uses).mp hi
  apply Finset.mem_union.mpr
  by_cases heq : label.card = 2
  · exact Or.inl ((mem_labelUnion i _).mpr ⟨label, by simp [pairUses, hm, heq], hp⟩)
  · exact Or.inr ((mem_labelUnion i _).mpr ⟨label, by simp [otherUses, hm, heq], hp⟩)

theorem pair_mass (uses : List Color) :
    mass uses = 2 * (pairUses uses).length + mass (otherUses uses) := by
  induction uses with
  | nil => rfl
  | cons label rest ih =>
      by_cases h : label.card = 2
      · change label.card + mass rest = _
        rw [h, ih]
        simp [pairUses, otherUses, h]
        omega
      · change label.card + mass rest = _
        rw [ih]
        simp [pairUses, otherUses, mass, h]
        omega

theorem pair_union (uses : List Color) :
    labelUnion (pairUses uses) = (pairLabels uses).biUnion id := by
  ext i
  rw [mem_labelUnion, Finset.mem_biUnion]
  simp [pairLabels]

theorem pair_union_card_le (uses : List Color) :
    (labelUnion (pairUses uses)).card ≤ 2 * (pairLabels uses).card := by
  rw [pair_union]
  calc
    ((pairLabels uses).biUnion id).card ≤ ∑ label ∈ pairLabels uses, label.card :=
      Finset.card_biUnion_le
    _ = 2 * (pairLabels uses).card := by
      have hc (label : Color) (hl : label ∈ pairLabels uses) : label.card = 2 := by
        simpa [pairLabels, pairUses, and_comm] using
          (List.mem_filter.mp (List.mem_toFinset.mp hl)).2
      rw [show (∑ label ∈ pairLabels uses, label.card) = ∑ _label ∈ pairLabels uses, 2 by
        exact Finset.sum_congr rfl hc]
      simp [Nat.mul_comm]

theorem wire_overlap (uses : List Color) :
    (labelUnion uses).card + 2 * (pairUses uses).length ≤
      mass uses + (labelUnion (pairUses uses)).card := by
  have h := (Finset.card_le_card (union_of_filtered uses)).trans (Finset.card_union_le _ _)
  have hother := labelUnion_card_le (otherUses uses)
  rw [pair_mass]
  omega

theorem triple_net_saving (uses : List Color) (htriple : (labelUnion uses).card ≤ 3) :
    (labelUnion (pairUses uses)).card ≤ (pairLabels uses).card + 1 := by
  have hsubset : labelUnion (pairUses uses) ⊆ labelUnion uses := by
    intro i hi
    obtain ⟨label, h, hi⟩ := (mem_labelUnion i _).mp hi
    exact (mem_labelUnion i _).mpr ⟨label, (List.mem_filter.mp h).1, hi⟩
  have hu := (Finset.card_le_card hsubset).trans htriple
  have hp := pair_union_card_le uses
  omega

/-- A lower bound for a finite system of wire uses once the gate and input totals are established. -/
theorem lower_from_wire_totals {Wire : Type*} [DecidableEq Wire]
    (wires triples : Finset Wire) (uses : Wire → List Color) (gates shared : Nat)
    (hsubset : triples ⊆ wires) (htriples : triples.card ≤ 4)
    (hcolors : ∀ w ∈ triples, (labelUnion (uses w)).card ≤ 3)
    (hpair : (∑ w ∈ wires, (pairUses (uses w)).length) = 2 * shared)
    (hmass : (∑ w ∈ wires, mass (uses w)) = 2 * (gates + shared) + 4)
    (hdemand : (∑ w ∈ wires, (labelUnion (uses w)).card) = gates + shared + 28)
    (hdistinct : (∑ w ∈ wires, (pairLabels (uses w)).card) ≤
      shared + ∑ w ∈ triples, (pairLabels (uses w)).card) : 20 ≤ gates := by
  let a (w : Wire) := (pairLabels (uses w)).card
  let b (w : Wire) := (pairUses (uses w)).length
  let u (w : Wire) := (labelUnion (pairUses (uses w))).card
  have hwire : (∑ w ∈ wires, (labelUnion (uses w)).card) + 2 * (∑ w ∈ wires, b w) ≤
      (∑ w ∈ wires, mass (uses w)) + (∑ w ∈ wires, u w) := by
    simpa only [Finset.sum_add_distrib, Finset.mul_sum, b, u] using
      (Finset.sum_le_sum fun w (_hw : w ∈ wires) => wire_overlap (uses w))
  have hdup : (∑ w ∈ wires, a w) ≤ ∑ w ∈ wires, b w := by
    apply Finset.sum_le_sum
    intro w _
    exact List.toFinset_card_le _
  have hterm (w : Wire) : u w + (if w ∈ triples then a w else 0) ≤
      2 * a w + (if w ∈ triples then 1 else 0) := by
    by_cases hw : w ∈ triples
    · simp only [hw, ite_true]
      have := triple_net_saving (uses w) (hcolors w hw)
      change u w ≤ a w + 1 at this
      omega
    · simp only [hw, ite_false, Nat.add_zero]
      exact pair_union_card_le (uses w)
  have hfilter : wires.filter (fun w => w ∈ triples) = triples := by
    ext w
    simpa only [Finset.mem_filter, and_iff_right_of_imp] using
      (show (w ∈ wires ∧ w ∈ triples) ↔ w ∈ triples from ⟨And.right, fun h => ⟨hsubset h, h⟩⟩)
  have hsave : (∑ w ∈ wires, u w) + (∑ w ∈ triples, a w) ≤
      2 * (∑ w ∈ wires, a w) + triples.card := by
    simpa only [Finset.sum_add_distrib, ← Finset.sum_filter, hfilter, Finset.mul_sum,
      Finset.sum_const, Nat.nsmul_eq_mul, mul_one] using
        (Finset.sum_le_sum fun w (_hw : w ∈ wires) => hterm w)
  change (∑ w ∈ wires, b w) = 2 * shared at hpair
  change (∑ w ∈ wires, a w) ≤ shared + ∑ w ∈ triples, a w at hdistinct
  omega



open scoped BigOperators

abbrev Wires (n : Nat) := Fin 14 ⊕ Fin n

def wanted (p : Fin 14) : Color := Finset.univ.filter fun i => (p.val + 1).testBit i.val

theorem wanted_card : ∀ p : Fin 14, 1 ≤ (wanted p).card ∧ (wanted p).card ≤ 3 := by
  decide +kernel

theorem wanted_injective : ∀ p q : Fin 14, wanted p = wanted q → p = q := by decide +kernel

theorem wanted_mass : (∑ p : Fin 14, (wanted p).card) = 28 := by decide +kernel

theorem wanted_triples : (Finset.univ.filter fun p : Fin 14 => (wanted p).card = 3).card = 4 := by
  decide +kernel

def usesAt {W : Type*} [DecidableEq W] (es : List (W × Color)) (w : W) : List Color :=
  (es.filter fun e => e.1 == w).map Prod.snd

theorem sum_by_wire {W : Type*} [Fintype W] [DecidableEq W]
    (es : List (W × Color)) (weight : Color → Nat) :
    (∑ w : W, ((usesAt es w).map weight).sum) = (es.map fun e => weight e.2).sum := by
  induction es with
  | nil => simp [usesAt]
  | cons e tail ih =>
      have h (w : W) : ((usesAt (e :: tail) w).map weight).sum =
          (if e.1 = w then weight e.2 else 0) + ((usesAt tail w).map weight).sum := by
        by_cases he : e.1 = w <;> simp [usesAt, he]
      simp_rw [h]
      rw [Finset.sum_add_distrib, ih]
      simp [eq_comm]

def edges {n : Nat} (left right : Fin n → Wires n) (roots : Fin 4 → Wires n)
    (color : Fin n → Color) : List (Wires n × Color) :=
  List.ofFn (fun g => (left g, color g)) ++ List.ofFn (fun g => (right g, color g)) ++
    List.ofFn (fun bit => (roots bit, {bit}))

theorem source_lookup {n : Nat} (l r : Fin n → Wires n) (roots : Fin 4 → Wires n)
    (color : Fin n → Color) (w : Wires n) (s : Color) :
    s ∈ usesAt (edges l r roots color) w ↔
      (∃ g : Fin n, (l g = w ∨ r g = w) ∧ color g = s) ∨
      (∃ bit : Fin 4, roots bit = w ∧ ({bit} : Color) = s) := by
  simp only [usesAt, List.mem_map, List.mem_filter, beq_iff_eq, edges, List.mem_append,
    List.mem_ofFn]
  constructor
  · rintro ⟨e, ⟨(⟨g, he⟩ | ⟨g, he⟩) | ⟨bit, he⟩, hw⟩, hc⟩
    · subst e; exact Or.inl ⟨g, Or.inl hw, hc⟩
    · subst e; exact Or.inl ⟨g, Or.inr hw, hc⟩
    · subst e; exact Or.inr ⟨bit, hw, hc⟩
  · rintro (⟨g, (hl | hr), hc⟩ | ⟨bit, hr, hc⟩)
    · exact ⟨(l g, color g), ⟨Or.inl (Or.inl ⟨g, rfl⟩), hl⟩, hc⟩
    · exact ⟨(r g, color g), ⟨Or.inl (Or.inr ⟨g, rfl⟩), hr⟩, hc⟩
    · exact ⟨(roots bit, {bit}), ⟨Or.inr ⟨bit, rfl⟩, hr⟩, hc⟩

def pairWeight (s : Color) : Nat := if s.card = 2 then 1 else 0

theorem pair_length (uses : List Color) : (pairUses uses).length = (uses.map pairWeight).sum := by
  induction uses with
  | nil => rfl
  | cons s rest ih =>
      by_cases h : s.card = 2 <;> simp [pairUses, pairWeight, h, ← ih, Nat.add_comm]

def doubleGates {n : Nat} (color : Fin n → Color) : Finset (Fin n) :=
  Finset.univ.filter fun g => (color g).card = 2

theorem gate_color_mass {n : Nat} (color : Fin n → Color)
    (hcolor : ∀ g, 1 ≤ (color g).card ∧ (color g).card ≤ 2) :
    (∑ g, (color g).card) = n + (doubleGates color).card := by
  have h g : (color g).card = 1 + pairWeight (color g) := by
    have hb := hcolor g
    by_cases hh : (color g).card = 2
    · simp [pairWeight, hh]
    · simp [pairWeight, hh]; omega
  simp_rw [h]
  simp [pairWeight, doubleGates, Finset.sum_add_distrib]

theorem pair_uses_total {n : Nat} (l r : Fin n → Wires n) (roots : Fin 4 → Wires n)
    (color : Fin n → Color) :
    (∑ w, (pairUses (usesAt (edges l r roots color) w)).length) = 2 * (doubleGates color).card := by
  simp_rw [pair_length]
  rw [sum_by_wire]
  simp [edges, List.map_append, List.map_ofFn, List.sum_append, List.sum_ofFn,
    pairWeight, doubleGates, two_mul]

theorem mass_total {n : Nat} (l r : Fin n → Wires n) (roots : Fin 4 → Wires n)
    (color : Fin n → Color) (hcolor : ∀ g, 1 ≤ (color g).card ∧ (color g).card ≤ 2) :
    (∑ w, mass (usesAt (edges l r roots color) w)) = 2 * (n + (doubleGates color).card) + 4 := by
  unfold mass
  rw [sum_by_wire]
  simp [edges, List.map_append, List.map_ofFn, List.sum_append, List.sum_ofFn, gate_color_mass color hcolor,
    two_mul, Nat.add_assoc]

theorem demand_total {n : Nat} (use : Wires n → List Color)
    (color : Fin n → Color) (hcolor : ∀ g, 1 ≤ (color g).card ∧ (color g).card ≤ 2)
    (hin : ∀ p, labelUnion (use (.inl p)) = wanted p)
    (hgate : ∀ g, labelUnion (use (.inr g)) = color g) :
    (∑ w, (labelUnion (use w)).card) = n + (doubleGates color).card + 28 := by
  rw [Fintype.sum_sum_type]
  simp_rw [hin, hgate]
  rw [wanted_mass, gate_color_mass color hcolor, Nat.add_comm]

theorem pair_info {us : List Color} {s : Color} (h : s ∈ pairLabels us) :
    s ∈ us ∧ s.card = 2 ∧ s ⊆ labelUnion us := by
  have hf : s ∈ pairUses us := List.mem_toFinset.mp h
  have hparts := List.mem_filter.mp hf
  exact ⟨hparts.1, by simpa using hparts.2,
    fun i hi => (mem_labelUnion i us).mpr ⟨s, hparts.1, hi⟩⟩

theorem pair_eq {us : List Color} {s : Color} (h : s ∈ pairLabels us)
    (hu : (labelUnion us).card ≤ 2) : s = labelUnion us := by
  obtain ⟨_, hs, hsub⟩ := pair_info h
  exact Finset.eq_of_subset_of_card_le hsub (by omega)

theorem pair_count_le_one (us : List Color) (hu : (labelUnion us).card ≤ 2) :
    (pairLabels us).card ≤ 1 := by
  have h : pairLabels us ⊆ {labelUnion us} := by
    intro s hs
    simpa using pair_eq hs hu
  simpa using Finset.card_le_card h

theorem pair_count_zero (us : List Color) (hu : (labelUnion us).card < 2) :
    (pairLabels us).card = 0 := by
  by_contra h
  obtain ⟨s, hs⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero h)
  obtain ⟨_, hc, hsub⟩ := pair_info hs
  have := Finset.card_le_card hsub
  omega

theorem pair_consumer {n : Nat} (l r : Fin n → Wires n) (roots : Fin 4 → Wires n)
    (color : Fin n → Color) {w : Wires n} {s : Color}
    (hs : s ∈ pairLabels (usesAt (edges l r roots color) w)) :
    ∃ g : Fin n, (l g = w ∨ r g = w) ∧ color g = s := by
  obtain ⟨hu, hp, _⟩ := pair_info hs
  rcases (source_lookup l r roots color w s).mp hu with hg | ⟨i, _, eq⟩
  · exact hg
  · rw [← eq, Finset.card_singleton] at hp
    omega

def tripleInputs : Finset (Fin 14) := Finset.univ.filter fun p => (wanted p).card = 3

def inputWire (n : Nat) : Fin 14 ↪ Wires n := ⟨Sum.inl, Sum.inl_injective⟩

def tripleWires (n : Nat) : Finset (Wires n) := tripleInputs.map (inputWire n)

theorem distinct_pairs_total {n : Nat} (l r : Fin n → Wires n) (roots : Fin 4 → Wires n)
    (color : Fin n → Color) (hcolor : ∀ g, 1 ≤ (color g).card ∧ (color g).card ≤ 2)
    (horder : ∀ g h, l g = .inr h ∨ r g = .inr h → h < g)
    (hin : ∀ p, labelUnion (usesAt (edges l r roots color) (.inl p)) = wanted p)
    (hgate : ∀ g, labelUnion (usesAt (edges l r roots color) (.inr g)) = color g) :
    (∑ w, (pairLabels (usesAt (edges l r roots color) w)).card) ≤
      (doubleGates color).card + ∑ w ∈ tripleWires n,
        (pairLabels (usesAt (edges l r roots color) w)).card := by
  let us (w : Wires n) := usesAt (edges l r roots color) w
  let a (w : Wires n) := (pairLabels (us w)).card
  let gateSources : Finset (Fin n) := Finset.univ.filter fun g => 0 < a (.inr g)
  let twoSources : Finset (Fin 14) :=
    Finset.univ.filter fun p => (wanted p).card = 2 ∧ 0 < a (.inl p)
  have hg : gateSources ⊆ doubleGates color := by
    intro g h
    have hp : 0 < a (.inr g) := (Finset.mem_filter.mp h).2
    obtain ⟨s, hs⟩ := Finset.card_pos.mp hp
    obtain ⟨_, hc, hsub⟩ := pair_info hs
    have hh := Finset.card_le_card hsub
    change s.card ≤ (labelUnion (usesAt (edges l r roots color) (.inr g))).card at hh
    rw [hgate] at hh
    have := (hcolor g).2
    simp only [doubleGates, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have last_for (p : ↥twoSources) :
      ∃ g : ↥(doubleGates color \ gateSources), color g.val = wanted p.val := by
    have pp : (wanted p.val).card = 2 ∧ 0 < a (.inl p.val) := (Finset.mem_filter.mp p.property).2
    obtain ⟨s, hs⟩ := Finset.card_pos.mp pp.2
    have hs_eq := pair_eq hs (show (labelUnion (us (.inl p.val))).card ≤ 2 by
      change (labelUnion (usesAt (edges l r roots color) (.inl p.val))).card ≤ 2
      rw [hin, pp.1])
    change s = labelUnion (usesAt (edges l r roots color) (.inl p.val)) at hs_eq
    rw [hin] at hs_eq
    obtain ⟨first, _, hfirst⟩ := pair_consumer l r roots color hs
    let matching : Finset (Fin n) := Finset.univ.filter fun g => color g = wanted p.val
    have hm : matching.Nonempty := ⟨first, by simp [matching, hfirst, hs_eq]⟩
    let g := matching.max' hm
    have hmg : g ∈ matching := matching.max'_mem hm
    have hcg : color g = wanted p.val := (Finset.mem_filter.mp hmg).2
    have hsg : g ∉ gateSources := by
      intro hgs
      have hpa : 0 < a (.inr g) := (Finset.mem_filter.mp hgs).2
      obtain ⟨t, ht⟩ := Finset.card_pos.mp hpa
      have hte := pair_eq ht (show (labelUnion (us (.inr g))).card ≤ 2 by
        change (labelUnion (usesAt (edges l r roots color) (.inr g))).card ≤ 2
        rw [hgate, hcg, pp.1])
      change t = labelUnion (usesAt (edges l r roots color) (.inr g)) at hte
      rw [hgate, hcg] at hte
      obtain ⟨next, hn, hcn⟩ := pair_consumer l r roots color ht
      have hnm : next ∈ matching := by simp [matching, hcn, hte]
      exact (not_lt_of_ge (matching.le_max' next hnm)) (horder next g hn)
    exact ⟨⟨g, Finset.mem_sdiff.mpr ⟨by simp [doubleGates, hcg, pp.1], hsg⟩⟩, hcg⟩
  choose last last_color using last_for
  have hinj : Function.Injective last := by
    intro p q heq
    apply Subtype.ext
    exact wanted_injective _ _ ((last_color p).symm.trans (by rw [heq, last_color q]))
  have htwo : twoSources.card ≤ (doubleGates color \ gateSources).card := by
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective last hinj
  have hgate_sum : (∑ g, a (.inr g)) ≤ gateSources.card := by
    calc
      (∑ g, a (.inr g)) ≤ ∑ g, (if 0 < a (.inr g) then 1 else 0) := by
        apply Finset.sum_le_sum
        intro g _
        by_cases h : 0 < a (.inr g)
        · simpa only [h, ite_true] using pair_count_le_one (us (.inr g)) (by
            change (labelUnion (usesAt (edges l r roots color) (.inr g))).card ≤ 2
            rw [hgate]; exact (hcolor g).2)
        · simp only [h, ite_false]; omega
      _ = gateSources.card := by simp [gateSources]
  have hin_sum : (∑ p, a (.inl p)) ≤
      twoSources.card + ∑ p ∈ tripleInputs, a (.inl p) := by
    calc
      (∑ p, a (.inl p)) ≤ ∑ p, ((if p ∈ twoSources then 1 else 0) +
          (if p ∈ tripleInputs then a (.inl p) else 0)) := by
        apply Finset.sum_le_sum
        intro p _
        obtain ⟨hp1, hp3⟩ := wanted_card p
        by_cases h3 : (wanted p).card = 3
        · simp [tripleInputs, h3]
        · by_cases h2 : (wanted p).card = 2
          · by_cases ha : 0 < a (.inl p)
            · have hcap := pair_count_le_one (us (.inl p)) (by
                change (labelUnion (usesAt (edges l r roots color) (.inl p))).card ≤ 2
                rw [hin, h2])
              simpa [tripleInputs, twoSources, h2, ha] using hcap
            · simp [tripleInputs, twoSources, h2, ha]; omega
          · have hzero := pair_count_zero (us (.inl p)) (by
              change (labelUnion (usesAt (edges l r roots color) (.inl p))).card < 2
              rw [hin]; omega)
            change a (.inl p) = 0 at hzero
            simp [hzero]
      _ = twoSources.card + ∑ p ∈ tripleInputs, a (.inl p) := by
        simp only [Finset.sum_add_distrib, ← Finset.sum_filter]
        simp
  change (∑ w, a w) ≤ (doubleGates color).card + ∑ w ∈ tripleWires n, a w
  rw [Fintype.sum_sum_type]
  have ht : (∑ w ∈ tripleWires n, a w) = ∑ p ∈ tripleInputs, a (.inl p) := by
    simp [tripleWires, inputWire]
  rw [ht]
  have hd := Finset.card_sdiff_add_card_eq_card hg
  omega

theorem normalized_encoder_bound {n : Nat} (l r : Fin n → Wires n) (roots : Fin 4 → Wires n)
    (color : Fin n → Color) (hcolor : ∀ g, 1 ≤ (color g).card ∧ (color g).card ≤ 2)
    (horder : ∀ g h, l g = .inr h ∨ r g = .inr h → h < g)
    (hin : ∀ p, labelUnion (usesAt (edges l r roots color) (.inl p)) = wanted p)
    (hgate : ∀ g, labelUnion (usesAt (edges l r roots color) (.inr g)) = color g) : 20 ≤ n := by
  refine lower_from_wire_totals Finset.univ (tripleWires n) (usesAt (edges l r roots color))
    n (doubleGates color).card (Finset.subset_univ _) ?_ ?_
    (pair_uses_total l r roots color) (mass_total l r roots color hcolor)
    (demand_total _ color hcolor hin hgate)
    (distinct_pairs_total l r roots color hcolor horder hin hgate)
  · simp [tripleWires, tripleInputs, wanted_triples]
  · intro w hw
    obtain ⟨p, _, rfl⟩ := Finset.mem_map.mp hw
    change (labelUnion (usesAt (edges l r roots color) (.inl p))).card ≤ 3
    rw [hin]
    exact (wanted_card p).2



open PEqualNP.CircuitLowerBounds

abbrev Support := Finset (Fin 14)

def collect (read : Nat → Support) : List Nat → Support
  | [] => ∅
  | j :: rest => read j ∪ collect read rest

def supportStep (wires : List Support) (g : Gate) : List Support :=
  wires ++ [collect (fun j => wires.getD j ∅) g.inputs]

def supportFold (gs : List Gate) (wires : List Support) : List Support :=
  gs.foldl supportStep wires

def initialSupport : List Support := List.ofFn (fun p : Fin 14 => {p})

def actualSupport (C : Circuit) (wire : Nat) : Support :=
  (supportFold C.gates initialSupport).getD wire ∅

def readBit (p : Fin 14) (ss : List Support) : List Bool := ss.map (fun s => decide (p ∈ s))

theorem readBit_getD (p : Fin 14) (ss : List Support) (i : Nat) :
    (readBit p ss).getD i false = decide (p ∈ ss.getD i ∅) := by
  change (ss.map (fun s => decide (p ∈ s))).getD i (decide (p ∈ (∅ : Support))) = _
  exact List.getD_map ss ∅ _

theorem collect_or (p : Fin 14) (ss : List Support) (ids : List Nat) :
    decide (p ∈ collect (fun j => ss.getD j ∅) ids) =
      (ids.map (fun j => (readBit p ss).getD j false)).any id := by
  induction ids with
  | nil => simp [collect]
  | cons j tail ih =>
      simp only [collect, Finset.mem_union, List.map_cons, List.any_cons, id_eq]
      rw [← ih, readBit_getD]
      by_cases hp : p ∈ ss.getD j ∅ <;> simp_all

theorem step_support_eval (p : Fin 14) (ss : List Support) (g : Gate) (hg : g.op = .or) :
    readBit p (supportStep ss g) = readBit p ss ++
      [g.op.eval (g.inputs.map fun i => (readBit p ss).getD i false)] := by
  simp only [readBit, supportStep, List.map_append, List.map_cons, List.map_nil, hg, GateOp.eval]
  exact congrArg (fun x => readBit p ss ++ [x]) (collect_or p ss g.inputs)

theorem fold_support_eval (p : Fin 14) (gs : List Gate) (ss : List Support)
    (hleg : ∀ g ∈ gs, g.op = .or) :
    readBit p (supportFold gs ss) =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (readBit p ss) := by
  induction gs generalizing ss with
  | nil => rfl
  | cons g rest ih =>
      change readBit p (supportFold rest (supportStep ss g)) = _
      rw [ih (supportStep ss g) (fun h hh => hleg h (List.mem_cons_of_mem _ hh)),
        step_support_eval p ss g (hleg g List.mem_cons_self)]
      rfl

theorem read_initial (p : Fin 14) :
    readBit p initialSupport = List.ofFn (fun q : Fin 14 => decide (q = p)) := by
  simp [readBit, initialSupport, eq_comm]

theorem support_semantics (C : Circuit) (p : Fin 14) (wire : Nat)
    (hleg : ∀ g ∈ C.gates, g.op = .or) :
    decide (p ∈ actualSupport C wire) =
      (C.wires (List.ofFn (fun q : Fin 14 => decide (q = p)))).getD wire false := by
  unfold actualSupport
  rw [← readBit_getD, fold_support_eval p C.gates initialSupport hleg, read_initial]
  rfl

theorem fold_prefix (gs : List Gate) (ss : List Support) :
    ∃ tail, supportFold gs ss = ss ++ tail ∧ tail.length = gs.length := by
  induction gs generalizing ss with
  | nil => exact ⟨[], by simp [supportFold], rfl⟩
  | cons g gs ih =>
      obtain ⟨tail, eq, len⟩ := ih (supportStep ss g)
      refine ⟨collect (fun j => ss.getD j ∅) g.inputs :: tail, ?_, by simp [len]⟩
      change supportFold gs (supportStep ss g) = _
      rw [eq]
      simp [supportStep, List.append_assoc]

theorem fold_length (gs : List Gate) (ss : List Support) :
    (supportFold gs ss).length = ss.length + gs.length := by
  obtain ⟨tail, eq, len⟩ := fold_prefix gs ss
  simp [eq, len]

theorem getD_fold_prefix (gs : List Gate) (ss : List Support) (i : Nat) (hi : i < ss.length) :
    (supportFold gs ss).getD i ∅ = ss.getD i ∅ := by
  obtain ⟨tail, eq, _⟩ := fold_prefix gs ss
  rw [eq, List.getD_append _ _ _ _ hi]

theorem initial_length : initialSupport.length = 14 := by simp [initialSupport]

theorem support_input (C : Circuit) (p : Fin 14) : actualSupport C p.val = {p} := by
  unfold actualSupport
  rw [getD_fold_prefix _ _ _ (by simp [initial_length])]
  rw [List.getD_eq_getElem _ _ (by simp [initial_length])]
  simp only [initialSupport, List.getElem_ofFn]

theorem support_outside (C : Circuit) (i : Nat) (h : 14 + C.gates.length ≤ i) :
    actualSupport C i = ∅ := by
  unfold actualSupport
  exact List.getD_eq_default _ _ (by simpa [fold_length, initial_length] using h)

theorem support_gate (C : Circuit) (g : Fin C.gates.length) :
    actualSupport C (14 + g.val) =
      collect (fun j => if j < 14 + g.val then actualSupport C j else ∅) (C.gates.get g).inputs := by
  let k := 14 + g.val
  let before := supportFold (C.gates.take g.val) initialSupport
  let suffix := C.gates.drop (g.val + 1)
  let gate := C.gates.get g
  have hlen : before.length = k := by
    simp [before, fold_length, initial_length, k]
  have hsplit : C.gates = C.gates.take g.val ++ gate :: suffix := by
    conv_lhs => rw [← List.take_append_drop g.val C.gates]
    rw [List.drop_eq_getElem_cons g.isLt]
    rfl
  have hr : supportFold C.gates initialSupport = supportFold suffix (supportStep before gate) := by
    conv_lhs => rw [hsplit]
    simp [supportFold, List.foldl_append, before]
  have hreads : (fun j => before.getD j ∅) =
      (fun j => if j < k then actualSupport C j else ∅) := by
    funext j
    by_cases h : j < k
    · simp only [h, ite_true, actualSupport, hr]
      rw [getD_fold_prefix suffix (supportStep before gate) j
        (by simp only [supportStep, List.length_append, List.length_cons, List.length_nil, hlen]; omega)]
      change before.getD j ∅ = (before ++ [_]).getD j ∅
      exact (List.getD_append _ _ _ _ (by rwa [hlen])).symm
    · simp only [h, ite_false]
      exact List.getD_eq_default _ _ (by omega)
  change (supportFold C.gates initialSupport).getD k ∅ = _
  rw [hr, getD_fold_prefix _ _ _ (by simp [supportStep, hlen])]
  rw [supportStep, List.getD_append_right _ _ _ _ (by omega), hlen, Nat.sub_self]
  change collect (fun j => before.getD j ∅) gate.inputs = _
  rw [hreads]

def bitInputs (i : Fin 4) : Support := Finset.univ.filter fun p : Fin 14 => (p.val + 1).testBit i.val

theorem bitInputs_size : ∀ i : Fin 4, (bitInputs i).card = 7 := by decide +kernel

theorem support_root (C : Circuit) (i : Fin 4) (wire : Nat) (hleg : ∀ g ∈ C.gates, g.op = .or)
    (hcorrect : ∀ p : Fin 14,
      (C.wires (List.ofFn (fun q : Fin 14 => decide (q = p)))).getD wire false =
        (p.val + 1).testBit i.val) : actualSupport C wire = bitInputs i := by
  ext p
  have h := (support_semantics C p wire hleg).trans (hcorrect p)
  simpa only [bitInputs, Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq] using
    Iff.of_eq (congrArg (fun b : Bool => b = true) h)

def wireId {n : Nat} : Wires n → Nat
  | .inl p => p.val
  | .inr g => 14 + g.val

def wireSupport (C : Circuit) (w : Wires C.gates.length) : Support := actualSupport C (wireId w)

def nontrivial (C : Circuit) (g : Fin C.gates.length) : Prop :=
  2 ≤ (wireSupport C (.inr g)).card

def earlySource (C : Circuit) (g : Fin C.gates.length) (w : Wires C.gates.length) : Prop :=
  wireId w < 14 + g.val ∧ match w with
    | .inl _ => True
    | .inr h => nontrivial C h

def canRead (C : Circuit) (g : Fin C.gates.length) (s : Support) : Prop :=
  s = ∅ ∨ ∃ w, earlySource C g w ∧ wireSupport C w = s

def cutRead (C : Circuit) (g : Fin C.gates.length) (j : Nat) : Support :=
  if j < 14 + g.val then actualSupport C j else ∅

theorem cutRead_canRead (C : Circuit) (g : Fin C.gates.length) (j : Nat) :
    canRead C g (cutRead C g j) := by
  unfold cutRead
  by_cases hj : j < 14 + g.val
  · simp only [hj, ite_true]
    by_cases he : actualSupport C j = ∅
    · exact Or.inl he
    · apply Or.inr
      by_cases hone : (actualSupport C j).card = 1
      · obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hone
        exact ⟨.inl p, ⟨by change p.val < 14 + g.val; have := p.isLt; omega, trivial⟩,
          (support_input C p).trans hp.symm⟩
      · have hc : 0 < (actualSupport C j).card :=
          Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr he)
        have hj' : 14 ≤ j := by
          by_contra hlt
          let p : Fin 14 := ⟨j, by omega⟩
          have hp := support_input C p
          change actualSupport C j = {p} at hp
          exact hone (by rw [hp, Finset.card_singleton])
        let origin : Fin C.gates.length := ⟨j - 14, by have := g.isLt; omega⟩
        have hid : wireId (Sum.inr origin : Wires C.gates.length) = j := by
          change 14 + (j - 14) = j
          omega
        refine ⟨.inr origin, ⟨by rwa [hid], ?_⟩, ?_⟩
        · change 2 ≤ (actualSupport C (wireId (Sum.inr origin : Wires C.gates.length))).card
          rw [hid]
          omega
        · unfold wireSupport
          rw [hid]
  · simp [hj, canRead]

def childrenSpec (C : Circuit) (g : Fin C.gates.length)
    (lr : Wires C.gates.length × Wires C.gates.length) : Prop :=
  earlySource C g lr.1 ∧ earlySource C g lr.2 ∧
    wireSupport C (.inr g) = wireSupport C lr.1 ∪ wireSupport C lr.2

theorem chooseChildren (C : Circuit) (g : Fin C.gates.length)
    (ha : (C.gates.get g).inputs.length ≤ 2) (hn : nontrivial C g) :
    ∃ lr, childrenSpec C g lr := by
  have hrec := support_gate C g
  change wireSupport C (.inr g) = collect (cutRead C g) (C.gates.get g).inputs at hrec
  generalize hxs : (C.gates.get g).inputs = xs at hrec ha
  have hparts : ∃ a b, canRead C g a ∧ canRead C g b ∧ wireSupport C (.inr g) = a ∪ b := by
    rcases xs with _ | ⟨x, xs⟩
    · exact ⟨∅, ∅, Or.inl rfl, Or.inl rfl, by simpa [collect] using hrec⟩
    rcases xs with _ | ⟨y, xs⟩
    · exact ⟨cutRead C g x, ∅, cutRead_canRead C g x, Or.inl rfl,
        by simpa [collect] using hrec⟩
    have hx : xs = [] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at ha; omega)
    subst xs
    exact ⟨cutRead C g x, cutRead C g y, cutRead_canRead C g x, cutRead_canRead C g y,
      by simpa [collect] using hrec⟩
  obtain ⟨a, b, ha, hb, eq⟩ := hparts
  rcases ha with he | ⟨l, hl, hla⟩ <;> rcases hb with hf | ⟨r, hr, hrb⟩
  · simp [he, hf] at eq
    unfold nontrivial at hn
    simp [eq] at hn
  · exact ⟨(r, r), hr, hr, by simpa [he, ← hrb] using eq⟩
  · exact ⟨(l, l), hl, hl, by simpa [hf, ← hla] using eq⟩
  · exact ⟨(l, r), hl, hr, by simpa only [← hla, ← hrb] using eq⟩

theorem locate_root (C : Circuit) (i : Fin 4) (wire : Nat)
    (hs : actualSupport C wire = bitInputs i) :
    ∃ g : Fin C.gates.length, wireSupport C (.inr g) = bitInputs i := by
  have hc : (actualSupport C wire).card = 7 := by rw [hs, bitInputs_size]
  have hsmall : wire < 14 + C.gates.length := by
    by_contra h
    rw [support_outside C wire (by omega), Finset.card_empty] at hc
    omega
  have hlarge : 14 ≤ wire := by
    by_contra h
    let p : Fin 14 := ⟨wire, by omega⟩
    have hp := support_input C p
    change actualSupport C wire = {p} at hp
    rw [hp, Finset.card_singleton] at hc
    omega
  let g : Fin C.gates.length := ⟨wire - 14, by omega⟩
  refine ⟨g, ?_⟩
  change actualSupport C (14 + (wire - 14)) = bitInputs i
  rw [show 14 + (wire - 14) = wire by omega]
  exact hs



open PEqualNP.CircuitLowerBounds

section Wiring

variable (C : Circuit) (left right : Fin C.gates.length → Wires C.gates.length)

def wireEdge (a b : Wires C.gates.length) : Prop :=
  ∃ g : Fin C.gates.length, b = .inr g ∧ nontrivial C g ∧ (left g = a ∨ right g = a)

theorem edge_support
    (hspec : ∀ g, nontrivial C g → childrenSpec C g (left g, right g))
    {a b : Wires C.gates.length} (he : wireEdge C left right a b) :
    wireSupport C a ⊆ wireSupport C b := by
  obtain ⟨g, rfl, hg, h⟩ := he
  have hs := (hspec g hg).2.2
  change wireSupport C (.inr g) = wireSupport C (left g) ∪ wireSupport C (right g) at hs
  rw [hs]
  rcases h with eq | eq
  · rw [← eq]; exact Finset.subset_union_left
  · rw [← eq]; exact Finset.subset_union_right

theorem path_support
    (hspec : ∀ g, nontrivial C g → childrenSpec C g (left g, right g))
    {a b : Wires C.gates.length} (h : Relation.ReflTransGen (wireEdge C left right) a b) :
    wireSupport C a ⊆ wireSupport C b := by
  induction h with
  | refl => exact Finset.Subset.refl _
  | tail _ he ih => exact ih.trans (edge_support C left right hspec he)

def validWire (a : Wires C.gates.length) : Prop :=
  match a with
  | .inl _ => True
  | .inr g => nontrivial C g

theorem support_path
    (hspec : ∀ g, nontrivial C g → childrenSpec C g (left g, right g))
    (p : Fin 14) (w : Wires C.gates.length) (hv : validWire C w) (hp : p ∈ wireSupport C w) :
    Relation.ReflTransGen (wireEdge C left right) (.inl p) w := by
  revert hv hp
  refine (measure (wireId (n := C.gates.length))).wf.induction
    (C := fun u => validWire C u → p ∈ wireSupport C u →
      Relation.ReflTransGen (wireEdge C left right) (.inl p) u) w ?_
  intro node ih hn hp
  rcases node with q | g
  · change p ∈ actualSupport C q.val at hp
    rw [support_input] at hp
    have hq : p = q := Finset.mem_singleton.mp hp
    subst q
    exact .refl
  · have hn' : nontrivial C g := hn
    obtain ⟨hl, hr, he⟩ := hspec g hn'
    change wireSupport C (.inr g) = wireSupport C (left g) ∪ wireSupport C (right g) at he
    rw [he] at hp
    rcases Finset.mem_union.mp hp with hpl | hpr
    · exact (ih (left g) hl.1 hl.2 hpl).tail ⟨g, rfl, hn', Or.inl rfl⟩
    · exact (ih (right g) hr.1 hr.2 hpr).tail ⟨g, rfl, hn', Or.inr rfl⟩

variable (root : Fin 4 → Fin C.gates.length)

noncomputable def request (w : Wires C.gates.length) : Color := by
  classical
  exact Finset.univ.filter fun i => Relation.ReflTransGen (wireEdge C left right) w (.inr (root i))

theorem request_mem (w : Wires C.gates.length) (i : Fin 4) :
    i ∈ request C left right root w ↔ Relation.ReflTransGen (wireEdge C left right) w (.inr (root i)) := by
  classical
  simp [request]

theorem root_nontrivial (hroot : ∀ i, wireSupport C (.inr (root i)) = bitInputs i) (i : Fin 4) :
    nontrivial C (root i) := by
  unfold nontrivial
  rw [hroot, bitInputs_size]
  decide

theorem request_input (hspec : ∀ g, nontrivial C g → childrenSpec C g (left g, right g))
    (hroot : ∀ i, wireSupport C (.inr (root i)) = bitInputs i) (p : Fin 14) :
    request C left right root (.inl p) = wanted p := by
  ext i
  rw [request_mem]
  have hp : p ∈ wireSupport C (.inl p) := by
    change p ∈ actualSupport C p.val
    rw [support_input]; simp
  constructor
  · intro h
    have hh := path_support C left right hspec h hp
    rw [hroot] at hh
    simpa only [bitInputs, wanted, Finset.mem_filter, Finset.mem_univ, true_and] using hh
  · intro h
    apply support_path C left right hspec p (.inr (root i)) (root_nontrivial C root hroot i)
    rw [hroot]
    simpa only [bitInputs, wanted, Finset.mem_filter, Finset.mem_univ, true_and] using h

theorem wanted_intersection : ∀ p q : Fin 14, p ≠ q → (wanted p ∩ wanted q).card ≤ 2 := by
  decide +kernel

theorem gate_request_bound (hspec : ∀ g, nontrivial C g → childrenSpec C g (left g, right g))
    (hroot : ∀ i, wireSupport C (.inr (root i)) = bitInputs i) (g : Fin C.gates.length)
    (hg : nontrivial C g) : (request C left right root (.inr g)).card ≤ 2 := by
  obtain ⟨p, hp, q, hq, hne⟩ := Finset.one_lt_card.mp hg
  have hs : request C left right root (.inr g) ⊆ wanted p ∩ wanted q := by
    intro i hi
    have hpath := (request_mem C left right root _ i).mp hi
    have hsub := path_support C left right hspec hpath
    have hh₁ := hsub hp
    have hh₂ := hsub hq
    rw [hroot] at hh₁ hh₂
    simpa only [Finset.mem_inter, wanted, bitInputs, Finset.mem_filter, Finset.mem_univ, true_and]
      using And.intro hh₁ hh₂
  exact (Finset.card_le_card hs).trans (wanted_intersection p q hne)

noncomputable def usedGates : Finset (Fin C.gates.length) := by
  classical
  exact Finset.univ.filter fun g => nontrivial C g ∧ (request C left right root (.inr g)).Nonempty

theorem mem_usedGates (g : Fin C.gates.length) : g ∈ usedGates C left right root ↔
    nontrivial C g ∧ (request C left right root (.inr g)).Nonempty := by
  classical
  simp [usedGates]

theorem count_projected_circuit
    (hspec : ∀ g, nontrivial C g → childrenSpec C g (left g, right g))
    (hroot : ∀ i, wireSupport C (.inr (root i)) = bitInputs i) : 20 ≤ C.size := by
  classical
  let used := usedGates C left right root
  let n := used.card
  let renumber : Fin n ≃o ↥used := used.orderIsoOfFin rfl
  let expand : Wires n → Wires C.gates.length := fun w => match w with
    | .inl p => .inl p
    | .inr g => .inr (renumber g).val
  have expand_inj : Function.Injective expand := by
    intro w w' hw
    rcases w with p | g <;> rcases w' with p' | g'
    · change (Sum.inl p : Wires C.gates.length) = .inl p' at hw
      exact congrArg (Sum.inl : Fin 14 → Wires n) (Sum.inl.inj hw)
    · cases hw
    · cases hw
    · have he : (renumber g).val = (renumber g').val := Sum.inr.inj hw
      exact congrArg Sum.inr (renumber.injective (Subtype.ext he))
  let kept (w : Wires C.gates.length) : Prop := match w with
      | .inl _ => True
      | .inr g => g ∈ used
  have rep (w : Wires C.gates.length) (hw : kept w) : ∃ reduced : Wires n, expand reduced = w := by
    rcases w with p | g
    · exact ⟨.inl p, rfl⟩
    · exact ⟨.inr (renumber.symm ⟨g, hw⟩), by simp [expand]⟩
  have retain (g : Fin C.gates.length) (hg : g ∈ used) (w : Wires C.gates.length)
      (hw : earlySource C g w) (he : left g = w ∨ right g = w) : kept w := by
    rcases w with p | j
    · trivial
    · obtain ⟨hnt, i, hi⟩ := (mem_usedGates C left right root g).mp hg
      have hpath := (request_mem C left right root _ i).mp hi
      have head : wireEdge C left right (.inr j) (.inr g) := ⟨g, rfl, hnt, he⟩
      exact (mem_usedGates C left right root j).mpr
        ⟨hw.2, i, (request_mem C left right root _ i).mpr (Relation.ReflTransGen.head head hpath)⟩
  have orig_spec (g : Fin n) : childrenSpec C (renumber g).val
      (left (renumber g).val, right (renumber g).val) :=
    hspec _ ((mem_usedGates C left right root _).mp (renumber g).property).1
  have left_rep (g : Fin n) : ∃ w, expand w = left (renumber g).val :=
    rep _ (retain _ (renumber g).property _ (orig_spec g).1 (Or.inl rfl))
  have right_rep (g : Fin n) : ∃ w, expand w = right (renumber g).val :=
    rep _ (retain _ (renumber g).property _ (orig_spec g).2.1 (Or.inr rfl))
  have root_rep (i : Fin 4) : ∃ w, expand w = .inr (root i) := by
    apply rep
    apply (mem_usedGates C left right root _).mpr
    exact ⟨root_nontrivial C root hroot i, i, (request_mem C left right root _ i).mpr .refl⟩
  choose l hl using left_rep
  choose r hr using right_rep
  choose roots hroots using root_rep
  let req (w : Wires C.gates.length) := request C left right root w
  let color (g : Fin n) := req (.inr (renumber g).val)
  have hcolor (g : Fin n) : 1 ≤ (color g).card ∧ (color g).card ≤ 2 := by
    obtain ⟨hnt, hne⟩ := (mem_usedGates C left right root _).mp (renumber g).property
    exact ⟨Finset.card_pos.mpr hne, gate_request_bound C left right root hspec hroot _ hnt⟩
  have horder (g h : Fin n) (hsrc : l g = .inr h ∨ r g = .inr h) : h < g := by
    apply renumber.lt_iff_lt.mp
    change (renumber h).val < (renumber g).val
    rcases hsrc with he | he
    · have ho := (orig_spec g).1.1
      rw [← hl g, he] at ho
      change 14 + (renumber h).val.val < 14 + (renumber g).val.val at ho
      exact Nat.add_lt_add_iff_left.mp ho
    · have ho := (orig_spec g).2.1.1
      rw [← hr g, he] at ho
      change 14 + (renumber h).val.val < 14 + (renumber g).val.val at ho
      exact Nat.add_lt_add_iff_left.mp ho
  have demands (w : Wires n) : labelUnion (usesAt (edges l r roots color) w) = req (expand w) := by
    ext i
    rw [mem_labelUnion]
    change (∃ label ∈ usesAt (edges l r roots color) w, i ∈ label) ↔
      i ∈ request C left right root (expand w)
    rw [request_mem]
    constructor
    · rintro ⟨s, hs, hi⟩
      rcases (source_lookup l r roots color w s).mp hs with ⟨g, hw, he⟩ | ⟨bit, hw, he⟩
      · rw [← he] at hi
        have hpath := (request_mem C left right root (.inr (renumber g).val) i).mp hi
        have hnt := (mem_usedGates C left right root _).mp (renumber g).property |>.1
        have hdeg : left (renumber g).val = expand w ∨ right (renumber g).val = expand w := by
          rcases hw with hw | hw
          · exact Or.inl ((hl g).symm.trans (congrArg expand hw))
          · exact Or.inr ((hr g).symm.trans (congrArg expand hw))
        exact Relation.ReflTransGen.head ⟨_, rfl, hnt, hdeg⟩ hpath
      · rw [← he] at hi
        have hb := Finset.mem_singleton.mp hi
        subst bit
        rw [← hw, hroots]
    · intro hpath
      rcases hpath.cases_head with he | ⟨child, hstep, hchild⟩
      · have hw : roots i = w := expand_inj ((hroots i).trans he.symm)
        exact ⟨{i}, (source_lookup l r roots color w {i}).mpr (Or.inr ⟨i, hw, rfl⟩),
          Finset.mem_singleton_self _⟩
      · obtain ⟨old, rfl, hnt, hdeg⟩ := hstep
        have hi := (request_mem C left right root (.inr old) i).mpr hchild
        have hused : old ∈ used := (mem_usedGates C left right root old).mpr ⟨hnt, i, hi⟩
        let new := renumber.symm ⟨old, hused⟩
        have he : (renumber new).val = old := by simp [new]
        have hw : l new = w ∨ r new = w := by
          rcases hdeg with hlold | hrold
          · exact Or.inl (expand_inj ((hl new).trans (he ▸ hlold)))
          · exact Or.inr (expand_inj ((hr new).trans (he ▸ hrold)))
        have hbit : i ∈ color new := by
          change i ∈ request C left right root (.inr (renumber new).val)
          rwa [he]
        exact ⟨color new, (source_lookup l r roots color w _).mpr (Or.inl ⟨new, hw, rfl⟩), hbit⟩
  have hin (p : Fin 14) : labelUnion (usesAt (edges l r roots color) (.inl p)) = wanted p :=
    (demands (.inl p)).trans (request_input C left right root hspec hroot p)
  have hgate (g : Fin n) : labelUnion (usesAt (edges l r roots color) (.inr g)) = color g := demands _
  have hbound := normalized_encoder_bound l r roots color hcolor horder hin hgate
  exact hbound.trans (by simpa only [n, Circuit.size, Fintype.card_fin] using used.card_le_univ)

end Wiring

theorem encoder_lower (C : Circuit)
    (hleg : ∀ g ∈ C.gates, g.op = .or ∧ g.inputs.length ≤ 2)
    (hbits : ∀ v : Fin 4, ∃ w : Nat, ∀ p : Fin 14,
        (C.wires (List.ofFn (fun q : Fin 14 => decide (q = p)))).getD w false =
          (p.val + 1).testBit v.val) : 20 ≤ C.size := by
  classical
  have hchoice (g : Fin C.gates.length) : ∃ lr, nontrivial C g → childrenSpec C g lr := by
    by_cases hn : nontrivial C g
    · obtain ⟨lr, hlr⟩ := chooseChildren C g (hleg _ (List.get_mem C.gates g)).2 hn
      exact ⟨lr, fun _ => hlr⟩
    · exact ⟨(.inl 0, .inl 0), fun h => (hn h).elim⟩
  choose lr hspec using hchoice
  have hroots (i : Fin 4) : ∃ g : Fin C.gates.length, wireSupport C (.inr g) = bitInputs i := by
    obtain ⟨w, hw⟩ := hbits i
    exact locate_root C i w (support_root C i w (fun g hg => (hleg g hg).1) hw)
  choose root hroot using hroots
  exact count_projected_circuit C (fun g => (lr g).1) (fun g => (lr g).2) root hspec hroot

end PEqualNP.Outside.L_meta_12408_aux


theorem PEqualNP.Outside.L_meta_12408 :
  ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, (∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ g.inputs.length ≤ 2) ∧ C.size ≤ 19 ∧ ∀ v : Fin 4, ∃ w : ℕ, ∀ p : Fin 14, (C.wires (List.ofFn (fun q : Fin 14 => decide (q = p)))).getD w false = Nat.testBit (p.val + 1) v.val) := by
  rintro ⟨C, hleg, hsize, hbits⟩
  have lower := PEqualNP.Outside.L_meta_12408_aux.encoder_lower C hleg hbits
  omega
