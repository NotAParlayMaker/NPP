import PEqualNP.Defs

namespace PEqualNP.Outside.R_meta_3791_419

open Finset

lemma frontier_bound {α : Type} [DecidableEq α] (label : ℕ → Finset α)
    (children : ℕ → Finset ℕ)
    (hChildren : ∀ w, (children w).card ≤ 2 ∧ ∀ u ∈ children w, u < w)
    (hLabel : ∀ w, 1 < (label w).card → label w = (children w).biUnion label) :
    ∀ (m : ℕ) (D R : Finset ℕ), (∀ w ∈ D, w < m) → (∀ w ∈ R, w < m) →
      (∀ w ∈ D, ∀ u ∈ children w, 1 < (label u).card → u ∈ D) →
      (∀ w ∈ R, 1 < (label w).card → w ∈ D) →
      (R.biUnion label).card ≤ D.card + R.card := by
  intro m
  induction m with
  | zero =>
    intro D R _ hR _ _
    have hEmpty : R = ∅ := Finset.eq_empty_of_forall_notMem fun w hw => Nat.not_lt_zero _ (hR w hw)
    simp [hEmpty]
  | succ m ih =>
    intro D R hD hR hClosed hRoots
    have hDErase (w) (hw : w ∈ D.erase m) : w < m :=
      Nat.lt_of_le_of_ne (Nat.le_of_lt_succ (hD w (mem_of_mem_erase hw))) (ne_of_mem_erase hw)
    have hRErase (w) (hw : w ∈ R.erase m) : w < m :=
      Nat.lt_of_le_of_ne (Nat.le_of_lt_succ (hR w (mem_of_mem_erase hw))) (ne_of_mem_erase hw)
    have hClosedErase (w) (hw : w ∈ D.erase m) (u) (hu : u ∈ children w)
        (hLu : 1 < (label u).card) : u ∈ D.erase m :=
      mem_erase.mpr ⟨by
        have h := (hChildren w).2 u hu
        have h' := hDErase w hw
        omega, hClosed w (mem_of_mem_erase hw) u hu hLu⟩
    have hRootsErase (w) (hw : w ∈ R.erase m) (hl : 1 < (label w).card) :
        w ∈ D.erase m :=
      mem_erase.mpr ⟨ne_of_mem_erase hw, hRoots w (mem_of_mem_erase hw) hl⟩
    by_cases hIn : m ∈ R
    · have hUnion : R.biUnion label = label m ∪ (R.erase m).biUnion label := by
        conv_lhs => rw [← insert_erase hIn]
        rw [biUnion_insert]
      have hCardR := card_erase_add_one hIn
      by_cases hLarge : 1 < (label m).card
      · let R' := children m ∪ R.erase m
        have hDIn := hRoots m hIn hLarge
        have hR' (w) (hw : w ∈ R') : w < m := by
          rcases mem_union.mp hw with hw | hw
          · exact (hChildren m).2 w hw
          · exact hRErase w hw
        have hRoots' (w) (hw : w ∈ R') (hW : 1 < (label w).card) : w ∈ D.erase m := by
          rcases mem_union.mp hw with hw | hw
          · exact mem_erase.mpr ⟨Nat.ne_of_lt ((hChildren m).2 w hw), hClosed m hDIn w hw hW⟩
          · exact hRootsErase w hw hW
        have hCardD := card_erase_add_one hDIn
        have hCardR' : R'.card ≤ (children m).card + (R.erase m).card :=
          card_union_le (children m) (R.erase m)
        have hChild := (hChildren m).1
        have h := ih (D.erase m) R' hDErase hR' hClosedErase hRoots'
        change ((children m ∪ R.erase m).biUnion label).card ≤ _ at h
        rw [union_biUnion, ← hLabel m hLarge, ← hUnion] at h
        omega
      · have h := ih (D.erase m) (R.erase m) hDErase hRErase hClosedErase hRootsErase
        have hCardD := card_le_card (erase_subset m D)
        rw [hUnion]
        have hU := card_union_le (label m) ((R.erase m).biUnion label)
        omega
    · have h := ih (D.erase m) (R.erase m) hDErase hRErase hClosedErase hRootsErase
      have hCardD := card_le_card (erase_subset m D)
      rw [erase_eq_of_notMem hIn] at h
      omega

lemma union_count {α β : Type} [DecidableEq β] (s : Finset α) (f : α → Finset β) :
    (s.biUnion f).card ≤ ∑ a ∈ s, (f a).card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [biUnion_insert, sum_insert ha]
    exact (card_union_le _ _).trans (Nat.add_le_add_left ih _)

lemma sum_card_le_of_disjoint {α β : Type} [DecidableEq β] (s : Finset α) (f : α → Finset β)
    (h : (s : Set α).PairwiseDisjoint f) (G : Finset β) (hG : ∀ a ∈ s, f a ⊆ G) :
    (∑ a ∈ s, (f a).card) ≤ G.card := by
  rw [← Finset.card_biUnion h]
  exact card_le_card (biUnion_subset.mpr hG)

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def wire (C : Circuit) (x : List Bool) (w : ℕ) : Bool := (C.wires x).getD w false

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma fold_input (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (stepWire w g) (by simp [stepWire]; omega)]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma input_wire (C : Circuit) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    wire C x w = x.getD w false := fold_input C.gates x w hw

lemma gate_wire (C : Circuit) (x : List Bool) (h : ReadsBack x.length C)
    (j : ℕ) (hj : j < C.size) :
    wire C x (x.length + j) =
      (gateAt C j).op.eval ((gateAt C j).inputs.map (wire C x)) := by
  have hj' : j < C.gates.length := hj
  have hgate : gateAt C j = C.gates[j] := by
    simp [gateAt, List.getD_eq_getElem?_getD, hj']
  let pre := C.gates.take j
  let post := C.gates.drop (j + 1)
  have hs : C.gates = pre ++ C.gates[j] :: post := by
    dsimp only [pre, post]
    rw [List.cons_getElem_drop_succ, List.take_append_drop]
  have hpre : pre.length = j := by simp [pre]; omega
  let w := pre.foldl stepWire x
  have hw : w.length = x.length + j := by rw [fold_length, hpre]
  have hw' : ∀ i ∈ (gateAt C j).inputs, w.getD i false = wire C x i := by
    intro i hi
    have hlt := h j hj' i hi
    change _ = (C.gates.foldl stepWire x).getD i false
    rw [hs, List.foldl_append]
    exact (fold_input _ w i (by omega)).symm
  have hlast : wire C x (x.length + j) =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => w.getD i false) := by
    change (C.gates.foldl stepWire x).getD (x.length + j) false = _
    rw [hs, List.foldl_append, List.foldl_cons]
    have hlt : x.length + j < (stepWire w C.gates[j]).length := by simp [stepWire]; omega
    rw [fold_input post (stepWire w C.gates[j]) _ hlt]
    change (stepWire w C.gates[j]).getD (x.length + j) false = _
    rw [hgate, ← hw]
    simp [stepWire, List.getD_eq_getElem?_getD]
  rw [hlast, List.map_congr_left hw']

def child (C : Circuit) (w : ℕ) : Finset ℕ :=
  if 26 ≤ w ∧ w - 26 < C.size then (gateAt C (w - 26)).inputs.toFinset else ∅

def isOr (C : Circuit) (w : ℕ) : Prop :=
  26 ≤ w ∧ w - 26 < C.size ∧ (gateAt C (w - 26)).op = .or

noncomputable def tails (C : Circuit) (w : ℕ) : Finset ℕ := by
  classical
  exact if isOr C w then
    ((child C w).filter (· < w)).attach.biUnion fun u =>
      tails C u.val
  else {w}
termination_by w
decreasing_by exact (Finset.mem_filter.mp u.property).2

lemma tails_or (C : Circuit) (h : ReadsBack 26 C) (w : ℕ) (ho : isOr C w) :
    tails C w = (child C w).biUnion (tails C) := by
  classical
  rw [tails, ite_eq_left ho]
  rw [attach_biUnion]
  congr 1
  apply filter_true_of_mem
  intro u hu
  change u ∈ child C w at hu
  have he := h (w - 26) ho.2.1 u
  unfold child at hu
  rw [ite_eq_left ⟨ho.1, ho.2.1⟩, List.mem_toFinset] at hu
  exact (Nat.add_sub_of_le ho.1) ▸ he hu

lemma tails_stop (C : Circuit) (w : ℕ) (ho : ¬ isOr C w) : tails C w = {w} := by
  rw [tails, ite_eq_right ho]

lemma child_bound (C : Circuit) (hm : Monotone2 C) (hb : ReadsBack 26 C) (w : ℕ) :
    (child C w).card ≤ 2 ∧ ∀ u ∈ child C w, u < w := by
  unfold child
  split
  next hw =>
    have hg : gateAt C (w - 26) ∈ C.gates := by
      have h : w - 26 < C.gates.length := hw.2
      simp [gateAt, List.getD_eq_getElem?_getD, h]
    refine ⟨(List.toFinset_card_le _).trans (hm _ hg).2, ?_⟩
    intro u hu
    have hi := hb (w - 26) hw.2 u (List.mem_toFinset.mp hu)
    omega
  next => simp

lemma tails_nonOr (C : Circuit) (hb : ReadsBack 26 C) :
    ∀ w t, t ∈ tails C w → t ≤ w ∧ ¬ isOr C t := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro t ht
    by_cases ho : isOr C w
    · have h26 := ho.1
      rw [tails_or C hb w ho, mem_biUnion] at ht
      obtain ⟨u, hu, ht⟩ := ht
      have hmem : u ∈ (gateAt C (w - 26)).inputs := by
        simpa [child, ho.1, ho.2.1] using hu
      have hlt := hb (w - 26) ho.2.1 u hmem
      have huw : u < w := by omega
      exact ⟨(ih u huw t ht).1.trans huw.le, (ih u huw t ht).2⟩
    · rw [tails_stop _ _ ho, mem_singleton] at ht
      subst t
      exact ⟨le_rfl, ho⟩

lemma tail_eval (C : Circuit) (hb : ReadsBack 26 C) (x : List Bool) (hx : x.length = 26) :
    ∀ w, wire C x w = true ↔ ∃ t ∈ tails C w, wire C x t = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases ho : isOr C w
    · have h26 := ho.1
      have hb' : ReadsBack x.length C := hx ▸ hb
      have he : x.length + (w - 26) = w := by omega
      rw [tails_or C hb w ho]
      have hchild : ∀ t, t ∈ child C w ↔ t ∈ (gateAt C (w - 26)).inputs := by
        intro t
        simp [child, ho.1, ho.2.1]
      apply Iff.intro
      · intro hw
        have hh := gate_wire C x hb' (w - 26) ho.2.1
        rw [he, ho.2.2, GateOp.eval, hw] at hh
        obtain ⟨b, hbmem, hbtrue⟩ := List.any_eq_true.mp hh.symm
        obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hbmem
        have hlt := hb (w - 26) ho.2.1 u hu
        obtain ⟨t, ht, htv⟩ := (ih u (by omega)).mp hbtrue
        exact ⟨t, mem_biUnion.mpr ⟨u, (hchild _).mpr hu, ht⟩, htv⟩
      · rintro ⟨t, ht, htv⟩
        obtain ⟨u, hu, ht⟩ := mem_biUnion.mp ht
        have hmem := (hchild u).mp hu
        have hlt := hb (w - 26) ho.2.1 u hmem
        have hw := (ih u (by omega)).mpr ⟨t, ht, htv⟩
        have hh := gate_wire C x hb' (w - 26) ho.2.1
        rw [he, ho.2.2, GateOp.eval] at hh
        rw [hh, List.any_eq_true]
        exact ⟨wire C x u, List.mem_map.mpr ⟨u, hmem, rfl⟩, hw⟩
    · simp [tails_stop C w ho]

def diff : Finset (Fin 13) := {0, 1, 3, 9}
abbrev incident (p l : Fin 13) : Prop := p - l ∈ diff

def pos (p l : Fin 13) : List Bool :=
  (List.ofFn fun i : Fin 13 => decide (i = p)) ++ (List.ofFn fun i : Fin 13 => decide (i = l))

def neg (Q : Finset (Fin 13)) : List Bool :=
  (List.ofFn fun i : Fin 13 => decide (i ∈ Q)) ++
  (List.ofFn fun i : Fin 13 => decide (∀ p ∈ Q, ¬ incident p i))

abbrev quad (Q : Finset (Fin 13)) : Prop :=
  Q.card = 4 ∧ ∀ l : Fin 13, (Q.filter fun p => incident p l).card ≤ 2

def point (p : Fin 13) : Fin 26 := p.castAdd 13
def line (l : Fin 13) : Fin 26 := l.natAdd 13

abbrev adj (u v : Fin 26) : Prop :=
  if u.val < 13 then 13 ≤ v.val ∧ incident (Fin.ofNat 13 u.val) (Fin.ofNat 13 v.val)
  else v.val < 13 ∧ incident (Fin.ofNat 13 v.val) (Fin.ofNat 13 u.val)

lemma point_mod (p : Fin 13) : Fin.ofNat 13 (point p).val = p := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt p.isLt

lemma line_mod (l : Fin 13) : Fin.ofNat 13 (line l).val = l := by
  apply Fin.ext
  change (13 + l.val) % 13 = l.val
  simp [Nat.mod_eq_of_lt l.isLt]

lemma pt_lt (p : Fin 13) : (point p).val < 13 := p.isLt
lemma ln_le (l : Fin 13) : 13 ≤ (line l).val := Nat.le_add_right _ _

lemma adj_pos (p l : Fin 13) : adj (point p) (line l) ↔ incident p l := by
  simp only [adj, pt_lt, ite_true, ln_le, point_mod, line_mod, true_and]

lemma adj_symm : ∀ u v : Fin 26, adj u v → adj v u := by decide

lemma adj_irrefl : ∀ u : Fin 26, ¬ adj u u := by decide

def nb (c : Fin 26) : Finset (Fin 26) :=
  Finset.univ.filter (adj c)

lemma nb_card : ∀ c : Fin 26, (nb c).card = 4 := by decide

set_option maxHeartbeats 3000000 in
lemma nb_inter : ∀ c d : Fin 26, c ≠ d → ((nb c) ∩ (nb d)).card ≤ 1 := by
  decide +kernel

def edges : Finset (Fin 13 × Fin 13) :=
  Finset.univ.filter fun p => incident p.1 p.2

lemma edges_card : edges.card = 52 := by decide

def negWitnessTable : List ℕ :=
  [0x1d000011c04e027089807400002702981a4001013403908c42a113043811c04e05300e809c04e027,
   0x74000047011c04e027089800009c0270298000001013403908c44c113043811c04e053027009c04e027,
   0x1d047011c04e027000007409c02700000000e900e403903442a10e043811c04e01d00e809c04e027,
   0x7401d047007409a00008c807409c00000001a400102940c903443811904681340d201d00e807409c01d,
   0x7401d01d014c000053089807400000002980000e9013409906442a11304d014c07405300e80740a6053,
   0x74065053000004e027211800000002700001a40e9023411908c44a129053019404e03a034809c04e027,
   0x19404d000011c08e047000000009c00002981a40e904342311284a2149061811c0ca053026811c08e047,
   0x134000047021c10e00000002340000870618324329089442920c702183043830c14c09a046821c10e087,
   0x119087044c000000089800021c18308984a426910a481940c6421130c1852425211308c8438226113,
   0x4642151130000000215000085460c2251288984001211502981442a3211c0894444a21510e085444c215,
   0x85440d0000000846000211903489442324180008c9403605108cc0a50324191288464192069034846423,
   0x1034000000201c000807409a05508c80700022250a9809403b02940a903442a11904681340ca01d00e807,
   0x8070002047013809c22601c000809c0a6069013c04d00e42310a844c10e047013814c03a027013,
   0x8e007409a05508c80742982250a881a40e823800e903442a11900001340ca01d00e807400001d0000000,
   0x1d006915403240d2261094a2246903210e081a51c102944480004c212906481a40d20000348000000069,
   0x1a41510c9014c1860530899844c8418302987043a1013000120c4a2113061814c00005300000000a6053,
   0x544225053021c04e027211921460c0270c18c84348000403908c44a183043800004e000000009c04e027,
   0x89414c087013809c846485183009c3063210d20a8900e423112860c10e0000138000000027013809c000,
   0x53001d04e007411a21520c8074c18485308a22512908940a903442a000046800000001d00e807400001d,
   0x7411901d044c846813089906521442308984a4a61013409908c000113000000084611308c8000226113,
   0x464055113011c04e027409885508c02702989840e9013403800042a000000011c04e053000009c04e027,
   0x15404d047011c04e027211823409c02706181a48c9023000108c000000043811c04e000026809c04e027,
   0x13401d047011c08e047089807409c08702983242a80004038000000113043811c00005300e811c08e047,
   0x7411c047023811c22601d027021c0a60c90aa026900e000000044c10e047000014c03a047023811c000,
   0x47001d08e007409a05508c80742982250a881a40e8000000103442a11900001340ca01d00e807400001d,
   0x7423801d026815423201d0a608942a206903a08e000040d10a846400004d032807403a01d0000074000]

def negWitness (u v : Fin 26) : Finset (Fin 13) :=
  Finset.univ.filter fun p => Nat.testBit ((negWitnessTable.getD u.val 0) >>> (13 * v.val)) p.val

set_option maxHeartbeats 3000000 in
lemma neg_witness : ∀ u v : Fin 26, ¬ adj u v →
    quad (negWitness u v) ∧
      (neg (negWitness u v)).getD u.val false = true ∧
      (neg (negWitness u v)).getD v.val false = true := by
  decide +kernel

def nbWire (c : Fin 26) : Finset ℕ := (nb c).image Fin.val

lemma nbWire_low (c : Fin 26) (u : ℕ) (hu : u ∈ nbWire c) : u < 26 := by
  obtain ⟨v, _, rfl⟩ := mem_image.mp hu
  exact v.isLt

lemma nbWire_card_le (c : Fin 26) : (nbWire c).card ≤ 4 :=
  card_image_le.trans_eq (nb_card c)

lemma nbWire_inter (c d : Fin 26) (h : c ≠ d) : (nbWire c ∩ nbWire d).card ≤ 1 := by
  have he : nbWire c ∩ nbWire d = ((nb c) ∩ (nb d)).image Fin.val := by
    ext w
    simp only [mem_inter, nbWire, mem_image]
    constructor
    · rintro ⟨⟨u, hu, rfl⟩, ⟨v, hv, huv⟩⟩
      have h := Fin.ext huv
      subst v
      exact ⟨u, ⟨hu, hv⟩, rfl⟩
    · rintro ⟨u, ⟨hu, hv⟩, rfl⟩
      exact ⟨⟨u, hu, rfl⟩, ⟨u, hv, rfl⟩⟩
  rw [he]
  exact card_image_le.trans (nb_inter _ _ h)

def edgeOf (c : Fin 26) (u : ℕ) : Fin 13 × Fin 13 :=
  if c.val < 13 then (Fin.ofNat 13 c.val, Fin.ofNat 13 u)
  else (Fin.ofNat 13 u, Fin.ofNat 13 c.val)

lemma edgeOf_correct (p l : Fin 13) (c : Fin 26) (u : ℕ)
    (h : (c = point p ∧ u = (line l).val) ∨ (c = line l ∧ u = (point p).val)) :
    edgeOf c u = (p, l) := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp only [edgeOf, pt_lt, ite_true, point_mod, line_mod]
  · simp only [edgeOf, ite_eq_right (not_lt.mpr (ln_le l)), point_mod, line_mod]

noncomputable def reserve (C : Circuit) (A : Finset ℕ) : Finset ℕ := by
  classical
  exact (Ico 26 (26 + C.size)).filter fun t =>
    isOr C t ∧ tails C t ⊆ A ∧ 1 < (tails C t).card

lemma reserve_iff (C : Circuit) (A : Finset ℕ) (t : ℕ) :
    t ∈ reserve C A ↔ isOr C t ∧ tails C t ⊆ A ∧ 1 < (tails C t).card := by
  classical
  unfold reserve
  refine ⟨fun h => (mem_filter.mp h).2, fun h => mem_filter.mpr ⟨?_, h⟩⟩
  rw [mem_Ico]
  have h₁ := h.1.1
  have h₂ := h.1.2.1
  omega

lemma reserve_count (C : Circuit) (hm : Monotone2 C) (hb : ReadsBack 26 C)
    (A R : Finset ℕ)
    (hR : ∀ t ∈ R, t < 26 + C.size ∧ tails C t ⊆ A) :
    (R.biUnion (tails C)).card ≤ (reserve C A).card + R.card := by
  have hOr (t : ℕ) (ht : 1 < (tails C t).card) : isOr C t := by
    by_contra h
    rw [tails_stop C t h, card_singleton] at ht
    omega
  apply frontier_bound (tails C) (child C) (child_bound C hm hb)
    (fun w hw => tails_or C hb w (hOr w hw)) (26 + C.size) (reserve C A) R
  · intro w hw
    have ho := (reserve_iff C A w).mp hw |>.1
    have h₁ := ho.1
    have h₂ := ho.2.1
    omega
  · exact fun w hw => (hR w hw).1
  · intro w hw u hu hcard
    obtain ⟨hwOr, hwA, _⟩ := (reserve_iff C A w).mp hw
    apply (reserve_iff C A u).mpr ⟨hOr u hcard, ?_, hcard⟩
    apply Subset.trans _ hwA
    rw [tails_or C hb w hwOr]
    exact subset_biUnion_of_mem _ hu
  · intro w hw hcard
    exact (reserve_iff C A w).mpr ⟨hOr w hcard, (hR w hw).2, hcard⟩

lemma count_stars (C : Circuit) (a b : ℕ) (hm : Monotone2 C) (hb : ReadsBack 26 C)
    (ha : a < 26 + C.size) (hbnd : b < 26 + C.size)
    (hJ : ∀ t ∈ tails C a ∪ tails C b, 26 ≤ t)
    (T : Finset ℕ) (ctr : ℕ → Fin 26) (leaf : ℕ → ℕ)
    (hT : ∀ t ∈ T, t ∈ tails C a ∪ tails C b ∧ leaf t < t ∧ tails C (leaf t) ⊆ nbWire (ctr t))
    (hCover : ∀ p l : Fin 13, incident p l → ∃ t ∈ T, ∃ u ∈ tails C (leaf t),
      (ctr t = point p ∧ u = (line l).val) ∨ (ctr t = line l ∧ u = (point p).val)) :
    63 ≤ C.size := by
  classical
  let J := tails C a ∪ tails C b
  let D₀ := reserve C J
  let D (c : Fin 26) := reserve C (nbWire c)
  let T₁ (c : Fin 26) := T.filter fun w => ctr w = c
  let R (c : Fin 26) := (T₁ c).image leaf
  let L (c : Fin 26) := (R c).biUnion (tails C)
  have hTlt (t : ℕ) (ht : t ∈ T) : t < 26 + C.size := by
    rcases mem_union.mp (hT t ht).1 with h | h
    · exact ((tails_nonOr C hb a t h).1).trans_lt ha
    · exact ((tails_nonOr C hb b t h).1).trans_lt hbnd
  have hTn (t : ℕ) (ht : t ∈ T) : ¬ isOr C t := by
    rcases mem_union.mp (hT t ht).1 with h | h
    · exact (tails_nonOr C hb a t h).2
    · exact (tails_nonOr C hb b t h).2
  have hTop : T.card ≤ D₀.card + 2 := by
    have h := reserve_count C hm hb J {a, b} (by
      intro t ht
      rcases mem_insert.mp ht with rfl | ht
      · exact ⟨ha, subset_union_left⟩
      · rw [mem_singleton] at ht
        subst t
        exact ⟨hbnd, subset_union_right⟩)
    rw [biUnion_insert, singleton_biUnion] at h
    have hc := card_insert_le a ({b} : Finset ℕ)
    rw [card_singleton] at hc
    exact (card_le_card fun t ht => (hT t ht).1).trans (h.trans (Nat.add_le_add_left hc _))
  have hR (c : Fin 26) (u : ℕ) (hu : u ∈ R c) :
      u < 26 + C.size ∧ tails C u ⊆ nbWire c := by
    obtain ⟨t, ht, rfl⟩ := mem_image.mp hu
    obtain ⟨ht, hc⟩ := mem_filter.mp ht
    exact ⟨(hT t ht).2.1.trans (hTlt t ht), hc ▸ (hT t ht).2.2⟩
  have hL (c : Fin 26) : (L c).card ≤ (D c).card + (T₁ c).card :=
    (reserve_count C hm hb _ _ (hR c)).trans (Nat.add_le_add_left card_image_le _)
  have hL₄ (c : Fin 26) : (L c).card ≤ 4 * (T₁ c).card := by
    by_cases h : (T₁ c).Nonempty
    · have h₁ := card_pos.mpr h
      have h₂ : (L c).card ≤ 4 := (card_le_card (biUnion_subset.mpr fun u hu => (hR c u hu).2)).trans (nbWire_card_le c)
      omega
    · have he : T₁ c = ∅ := not_nonempty_iff_eq_empty.mp h
      simp [L, R, he]
  have hFull : 52 ≤ ∑ c : Fin 26, (L c).card := by
    have hE : edges ⊆ (univ : Finset (Fin 26)).biUnion (fun c => (L c).image (edgeOf c)) := by
      rintro ⟨p, l⟩ he
      have hi := (mem_filter.mp he).2
      obtain ⟨t, ht, u, hu, hh⟩ := hCover p l hi
      refine mem_biUnion.mpr ⟨ctr t, mem_univ _, mem_image.mpr ⟨u, ?_, edgeOf_correct _ _ _ _ hh⟩⟩
      exact mem_biUnion.mpr ⟨leaf t, mem_image.mpr ⟨t, mem_filter.mpr ⟨ht, rfl⟩, rfl⟩, hu⟩
    rw [← edges_card]
    exact (card_le_card hE).trans ((union_count _ _).trans (sum_le_sum fun c _ => card_image_le))
  have hTF : (∑ c : Fin 26, (T₁ c).card) = T.card := by
    have hp : ((univ : Finset (Fin 26)) : Set (Fin 26)).PairwiseDisjoint T₁ := by
      intro c _ d _ hne
      change Disjoint (T₁ c) (T₁ d)
      rw [disjoint_left]
      intro t ht hd
      exact hne ((mem_filter.mp ht).2.symm.trans (mem_filter.mp hd).2)
    rw [← card_biUnion hp]
    congr 1
    ext t
    simp [T₁]
  have hTHalf : 13 ≤ T.card := by
    have h := (sum_le_sum fun c (_ : c ∈ (univ : Finset (Fin 26))) => hL₄ c)
    rw [← mul_sum, hTF] at h
    omega
  have hBottom : 52 ≤ (∑ c : Fin 26, (D c).card) + T.card := by
    have h := sum_le_sum (s := (univ : Finset (Fin 26))) fun c _ => hL c
    rw [sum_add_distrib, hTF] at h
    omega
  let Dall := (univ : Finset (Fin 26)).biUnion D
  have hDCard : Dall.card = ∑ c : Fin 26, (D c).card := by
    apply card_biUnion
    intro c _ d _ hne
    change Disjoint (D c) (D d)
    rw [disjoint_left]
    intro t ht hd
    have hc := (reserve_iff C (nbWire c) t).mp ht
    have hd := (reserve_iff C (nbWire d) t).mp hd
    have h := (card_le_card (subset_inter hc.2.1 hd.2.1)).trans (nbWire_inter c d hne)
    omega
  have hDisjD : Disjoint D₀ Dall := by
    rw [disjoint_left]
    intro t ht hd
    have hc := (reserve_iff C J t).mp ht
    obtain ⟨c, _, hc'⟩ := mem_biUnion.mp hd
    have hc' := (reserve_iff C (nbWire c) t).mp hc'
    obtain ⟨u, hu⟩ := card_pos.mp (by omega : 0 < (tails C t).card)
    exact Nat.not_lt_of_ge (hJ u (hc.2.1 hu)) (nbWire_low c u (hc'.2.1 hu))
  have hDisjT : Disjoint T (D₀ ∪ Dall) := by
    rw [disjoint_left]
    intro t ht h
    rcases mem_union.mp h with h | h
    · exact hTn t ht ((reserve_iff C J t).mp h).1
    · obtain ⟨c, _, hc⟩ := mem_biUnion.mp h
      exact hTn t ht ((reserve_iff C (nbWire c) t).mp hc).1
  have hAll : T ∪ (D₀ ∪ Dall) ⊆ Ico 26 (26 + C.size) := by
    intro t ht
    rcases mem_union.mp ht with ht | hd
    · exact mem_Ico.mpr ⟨hJ t (hT t ht).1, hTlt t ht⟩
    · rcases mem_union.mp hd with h | h
      · exact (mem_filter.mp h).1
      · obtain ⟨_, _, hc⟩ := mem_biUnion.mp h
        exact (mem_filter.mp hc).1
  have hAll := card_le_card hAll
  rw [card_union_of_disjoint hDisjT, card_union_of_disjoint hDisjD, Nat.card_Ico,
      Nat.add_sub_cancel_left, hDCard] at hAll
  omega

lemma neg_len (Q : Finset (Fin 13)) : (neg Q).length = 26 := by simp [neg]
lemma pos_len (p l : Fin 13) : (pos p l).length = 26 := by simp [pos]

lemma pos_inputs (p l : Fin 13) (t : ℕ) (ht : t < 26) :
    wire C (pos p l) t = true ↔ t = (point p).val ∨ t = (line l).val := by
  rw [input_wire _ _ _ (by simpa [pos_len] using ht)]
  by_cases hp : t < 13
  · have hlen : t < (List.ofFn fun i : Fin 13 => decide (i = p)).length := by simpa using hp
    have hln := ln_le l
    simp only [pos, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left hlen, List.getElem?_ofFn]
    simp [hp, point, line, Fin.ext_iff]
    omega
  · have hl : t - 13 < 13 := by omega
    have hlen : (List.ofFn fun i : Fin 13 => decide (i = p)).length ≤ t := by simp; omega
    simp only [pos, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right hlen, List.length_ofFn, List.getElem?_ofFn]
    simp [hl, point, line, Fin.ext_iff]
    omega

lemma neg_tail_false (C : Circuit) (a b : ℕ) (hb : ReadsBack 26 C)
    (hneg : ∀ Q, quad Q → wire C (neg Q) a = false ∧ wire C (neg Q) b = false)
    (t : ℕ) (ht : t ∈ tails C a ∪ tails C b) (Q : Finset (Fin 13)) (hQ : quad Q) :
    wire C (neg Q) t = false := by
  cases he : wire C (neg Q) t
  · rfl
  · rcases mem_union.mp ht with ha | hb'
    · have h := (tail_eval C hb (neg Q) (neg_len Q) a).mpr ⟨t, ha, he⟩
      simp [(hneg Q hQ).1] at h
    · have h := (tail_eval C hb (neg Q) (neg_len Q) b).mpr ⟨t, hb', he⟩
      simp [(hneg Q hQ).2] at h

lemma terminal_high (C : Circuit) (a b : ℕ) (hb : ReadsBack 26 C)
    (hneg : ∀ Q, quad Q → wire C (neg Q) a = false ∧ wire C (neg Q) b = false)
    (t : ℕ) (ht : t ∈ tails C a ∪ tails C b) : 26 ≤ t := by
  by_contra! h
  let u : Fin 26 := ⟨t, h⟩
  have hn := neg_witness u u (adj_irrefl u)
  have hv := neg_tail_false C a b hb hneg t ht (negWitness u u) hn.1
  rw [input_wire _ _ _ (by simpa [neg_len] using h)] at hv
  exact Bool.noConfusion (hn.2.1.symm.trans hv)

lemma cross_neighbours (A B : Finset ℕ) (hA : A.Nonempty) (hB : B.Nonempty)
    (h : ∀ u ∈ A, ∀ v ∈ B, ∃ x y : Fin 26, x.val = u ∧ y.val = v ∧ adj x y) :
    (∃ c : Fin 26, A = {c.val} ∧ B ⊆ nbWire c) ∨
    (∃ c : Fin 26, B = {c.val} ∧ A ⊆ nbWire c) := by
  obtain ⟨u, hu⟩ := hA
  obtain ⟨v, hv⟩ := hB
  obtain ⟨x, y, hxu, hyv, _⟩ := h u hu v hv
  have hBsub (z : ℕ) (hz : z ∈ B) : z ∈ nbWire x := by
    obtain ⟨x', y', hx', hy', hxy⟩ := h u hu z hz
    have he : x' = x := Fin.ext (hx'.trans hxu.symm)
    subst x'
    exact mem_image.mpr ⟨y', mem_filter.mpr ⟨mem_univ _, hxy⟩, hy'⟩
  have hAsub (z : ℕ) (hz : z ∈ A) : z ∈ nbWire y := by
    obtain ⟨x', y', hx', hy', hxy⟩ := h z hz v hv
    have he : y' = y := Fin.ext (hy'.trans hyv.symm)
    subst y'
    exact mem_image.mpr ⟨x', mem_filter.mpr ⟨mem_univ _, adj_symm _ _ hxy⟩, hx'⟩
  by_cases hOne : A ⊆ {u}
  · exact Or.inl ⟨x, (Subset.antisymm hOne (singleton_subset_iff.mpr hu)).trans (congrArg singleton hxu.symm), hBsub⟩
  · obtain ⟨u', hu', huu'⟩ := not_subset.mp hOne
    obtain ⟨x', _, hx', _, _⟩ := h u' hu' v hv
    have hxx' : x ≠ x' := fun he => huu' (mem_singleton.mpr (hx'.symm.trans (congrArg Fin.val he.symm) |>.trans hxu))
    have hBsub' (z : ℕ) (hz : z ∈ B) : z ∈ nbWire x' := by
      obtain ⟨x'', y', hx'', hy', hxy⟩ := h u' hu' z hz
      have he : x'' = x' := Fin.ext (hx''.trans hx'.symm)
      subst x''
      exact mem_image.mpr ⟨y', mem_filter.mpr ⟨mem_univ _, hxy⟩, hy'⟩
    have hbCard := (card_le_card (subset_inter hBsub hBsub')).trans (nbWire_inter x x' hxx')
    have hEq : B = {v} := by
      symm
      apply eq_of_subset_of_card_le (singleton_subset_iff.mpr hv)
      simpa using hbCard
    exact Or.inr ⟨y, hEq.trans (congrArg singleton hyv.symm), hAsub⟩

lemma disjoint_groups (p l : Fin 13) : (point p).val ≠ (line l).val :=
  fun h => (Nat.not_lt_of_ge (ln_le l)) (h ▸ pt_lt p)

lemma centre_leaf_on_pos (C : Circuit) (hb : ReadsBack 26 C) (p l : Fin 13)
    (c : Fin 26) (k : ℕ) (hk : tails C k ⊆ nbWire c)
    (hc : wire C (pos p l) c.val = true) (hv : wire C (pos p l) k = true) :
    ∃ u ∈ tails C k,
      (c = point p ∧ u = (line l).val) ∨ (c = line l ∧ u = (point p).val) := by
  obtain ⟨u, hu, hut⟩ := (tail_eval C hb _ (pos_len p l) k).mp hv
  obtain ⟨v, hv, hvu⟩ := mem_image.mp (hk hu)
  have hAdj := (mem_filter.mp hv).2
  have hne : c.val ≠ u := fun h => adj_irrefl c (Fin.ext (hvu.trans h.symm) ▸ hAdj)
  have hc := (pos_inputs p l c.val c.isLt).mp hc
  have hPos := (pos_inputs p l u (nbWire_low c u (hk hu))).mp hut
  refine ⟨u, hu, ?_⟩
  rcases hc with hc | hc <;> rcases hPos with hPos | hPos
  · exact (hne (hc.trans hPos.symm)).elim
  · exact Or.inl ⟨Fin.ext hc, hPos⟩
  · exact Or.inr ⟨Fin.ext hc, hPos⟩
  · exact (hne (hc.trans hPos.symm)).elim

def active (C : Circuit) (t : ℕ) : Prop :=
  ∃ p l : Fin 13, incident p l ∧ wire C (pos p l) t = true

lemma obtain_star (C : Circuit) (a b t : ℕ) (hm : Monotone2 C) (hb : ReadsBack 26 C)
    (ha : a < 26 + C.size) (hbnd : b < 26 + C.size)
    (hneg : ∀ Q, quad Q → wire C (neg Q) a = false ∧ wire C (neg Q) b = false)
    (ht : t ∈ tails C a ∪ tails C b) (hActive : active C t)
    (hPure : ∀ u ∈ child C t, ∀ v ∈ tails C u, v < 26) :
    ∃ (c : Fin 26) (k : ℕ), k < t ∧ tails C k ⊆ nbWire c ∧
      ∀ x : List Bool, x.length = 26 → wire C x t = (wire C x c.val && wire C x k) := by
  have htLow := terminal_high C a b hb hneg t ht
  have htHighAndOr : t < 26 + C.size ∧ ¬ isOr C t := by
    rcases mem_union.mp ht with ht | ht
    · exact ⟨((tails_nonOr C hb a t ht).1).trans_lt ha, (tails_nonOr C hb a t ht).2⟩
    · exact ⟨((tails_nonOr C hb b t ht).1).trans_lt hbnd, (tails_nonOr C hb b t ht).2⟩
  let j := t - 26
  have hJ : j < C.size := by
    have := htHighAndOr.1
    dsimp [j]
    omega
  have hGmem : gateAt C j ∈ C.gates := by
    have hJ' : j < C.gates.length := hJ
    simp [gateAt, List.getD_eq_getElem?_getD, hJ']
  have hop : (gateAt C j).op = .and := by
    rcases (show (gateAt C j).op = .and ∨ (gateAt C j).op = .or by simpa using (hm _ hGmem).1) with h | h
    · exact h
    · exact (htHighAndOr.2 ⟨htLow, hJ, h⟩).elim
  have hEval (x : List Bool) (hx : x.length = 26) :
      wire C x t = ((gateAt C j).inputs.map (wire C x)).all id := by
    have h := gate_wire C x (hx ▸ hb) j hJ
    have htEq : x.length + j = t := by dsimp [j]; omega
    rwa [htEq, hop, GateOp.eval] at h
  have hChild (u : ℕ) : u ∈ child C t ↔ u ∈ (gateAt C j).inputs := by
    simp [child, htLow, hJ, j]
  have hArity := (hm _ hGmem).2
  have hReject (Q : Finset (Fin 13)) (hQ : quad Q) : wire C (neg Q) t = false :=
    neg_tail_false C a b hb hneg t ht Q hQ
  have hFind (u : ℕ) (hu : u ∈ child C t) (p l : Fin 13) (h : wire C (pos p l) u = true) :
      ∃ v ∈ tails C u, v < 26 := by
    obtain ⟨v, hv, _⟩ := (tail_eval C hb _ (pos_len p l) u).mp h
    exact ⟨v, hv, hPure u hu v hv⟩
  have hNegValue (i z : ℕ) (hz : z ∈ tails C i) (Q : Finset (Fin 13)) (hzt : z < 26)
      (hQz : (neg Q).getD z false = true) : wire C (neg Q) i = true := by
    apply (tail_eval C hb _ (neg_len Q) i).mpr
    exact ⟨z, hz, (input_wire C _ z (by simpa [neg_len] using hzt)).trans hQz⟩
  obtain ⟨p, l, _, hAct⟩ := hActive
  cases eq : (gateAt C j).inputs with
  | nil =>
    have hQ := (neg_witness 0 0 (adj_irrefl 0)).1
    have h := hEval (neg (negWitness 0 0)) (neg_len _)
    simp [eq, hReject _ hQ] at h
  | cons u us =>
    have hu : u ∈ child C t := (hChild u).mpr (by simp [eq])
    cases us with
    | nil =>
      have hPu : wire C (pos p l) u = true := by simpa [eq, hAct] using (hEval _ (pos_len p l)).symm
      obtain ⟨z, hz, hzt⟩ := hFind u hu p l hPu
      let c : Fin 26 := ⟨z, hzt⟩
      have hQ := neg_witness c c (adj_irrefl c)
      have h := hEval (neg (negWitness c c)) (neg_len _)
      rw [hReject _ hQ.1, eq] at h
      simp [hNegValue u z hz _ hzt hQ.2.1] at h
    | cons v vs =>
      have hEmpty : vs = [] := by simpa [eq] using hArity
      subst vs
      have hv : v ∈ child C t := (hChild v).mpr (by simp [eq])
      have hPair (x : List Bool) (hx : x.length = 26) :
          wire C x t = (wire C x u && wire C x v) := by simpa [eq] using hEval x hx
      have hPos := (hPair _ (pos_len p l)).symm.trans hAct
      obtain ⟨hPu, hPv⟩ := Bool.and_eq_true_iff.mp hPos
      obtain ⟨u', hu', _⟩ := hFind u hu p l hPu
      obtain ⟨v', hv', _⟩ := hFind v hv p l hPv
      have hCross (r : ℕ) (hr : r ∈ tails C u) (s : ℕ) (hs : s ∈ tails C v) :
          ∃ x y : Fin 26, x.val = r ∧ y.val = s ∧ adj x y := by
        have hr' := hPure u hu r hr
        have hs' := hPure v hv s hs
        let x : Fin 26 := ⟨r, hr'⟩
        let y : Fin 26 := ⟨s, hs'⟩
        refine ⟨x, y, rfl, rfl, ?_⟩
        by_contra h
        have hQ := neg_witness x y h
        have hP := hPair (neg (negWitness x y)) (neg_len _)
        rw [hReject _ hQ.1, hNegValue u r hr _ hr' hQ.2.1, hNegValue v s hs _ hs' hQ.2.2] at hP
        contradiction
      have hSingle (x : List Bool) (hx : x.length = 26) (w : ℕ) (c : Fin 26)
          (hc : tails C w = {c.val}) : wire C x w = wire C x c.val :=
        Bool.eq_iff_iff.mpr (by rw [tail_eval C hb x hx w, hc]; simp)
      rcases cross_neighbours _ _ ⟨u', hu'⟩ ⟨v', hv'⟩ hCross with ⟨c, hc, hcNb⟩ | ⟨c, hc, hcNb⟩
      · refine ⟨c, v, (child_bound C hm hb t).2 v hv, hcNb, fun x hx => ?_⟩
        rw [hPair x hx, hSingle x hx u c hc]
      · refine ⟨c, u, (child_bound C hm hb t).2 u hu, hcNb, fun x hx => ?_⟩
        rw [hPair x hx, hSingle x hx v c hc, Bool.and_comm]

lemma single_layer_bound (C : Circuit) (a b : ℕ) (hm : Monotone2 C) (hb : ReadsBack 26 C)
    (ha : a < 26 + C.size) (hbnd : b < 26 + C.size)
    (hpos : ∀ p l : Fin 13, incident p l → wire C (pos p l) a = true ∨ wire C (pos p l) b = true)
    (hneg : ∀ Q, quad Q → wire C (neg Q) a = false ∧ wire C (neg Q) b = false)
    (hPure : ∀ t ∈ tails C a ∪ tails C b, active C t → ∀ u ∈ child C t, ∀ v ∈ tails C u, v < 26) :
    63 ≤ C.size := by
  classical
  let T := (tails C a ∪ tails C b).filter (active C)
  have hCut : ∀ t : ℕ, ∃ (c : Fin 26) (k : ℕ), t ∈ T →
      k < t ∧ tails C k ⊆ nbWire c ∧
      ∀ x : List Bool, x.length = 26 → wire C x t = (wire C x c.val && wire C x k) := by
    intro t
    by_cases ht : t ∈ T
    · obtain ⟨hmem, hAct⟩ := mem_filter.mp ht
      obtain ⟨c, k, h⟩ := obtain_star C a b t hm hb ha hbnd hneg hmem hAct (hPure t hmem hAct)
      exact ⟨c, k, fun _ => h⟩
    · exact ⟨0, 0, fun h => (ht h).elim⟩
  choose ctr k h using hCut
  apply count_stars C a b hm hb ha hbnd (terminal_high C a b hb hneg) T ctr k
  · exact fun t ht => ⟨(mem_filter.mp ht).1, (h t ht).1, (h t ht).2.1⟩
  · intro p l hi
    have hEx : ∃ t ∈ tails C a ∪ tails C b, wire C (pos p l) t = true := by
      rcases hpos p l hi with h | h
      · obtain ⟨t, ht, hw⟩ := (tail_eval C hb _ (pos_len p l) a).mp h
        exact ⟨t, mem_union_left _ ht, hw⟩
      · obtain ⟨t, ht, hw⟩ := (tail_eval C hb _ (pos_len p l) b).mp h
        exact ⟨t, mem_union_right _ ht, hw⟩
    obtain ⟨t, ht, hw⟩ := hEx
    have ht' : t ∈ T := mem_filter.mpr ⟨ht, p, l, hi, hw⟩
    have hAnd := ((h t ht').2.2 _ (pos_len p l)).symm.trans hw
    obtain ⟨hc, hk⟩ := Bool.and_eq_true_iff.mp hAnd
    exact ⟨t, ht', centre_leaf_on_pos C hb p l _ _ (h t ht').2.1 hc hk⟩

open PEqualNP.EdgeOwnership

lemma cone_length (n : ℕ) (gs : List Gate) (w : List (List ℕ)) :
    (gs.foldl (coneStep n) w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

lemma cone_prefix (n : ℕ) (gs : List Gate) (w : List (List ℕ)) (i : ℕ) (hi : i < w.length) :
    (gs.foldl (coneStep n) w).getD i [] = w.getD i [] := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (coneStep n w g) (by simp [coneStep]; omega)]
    simp only [coneStep, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left hi]

lemma cone_of_child (C : Circuit) (i j u : ℕ) (hj : j < C.size)
    (hu : u ∈ (gateAt C j).inputs) (h₂ : 26 ≤ u) (h₃ : u < 26 + j)
    (hi : i = u - 26 ∨ InCone 26 C i (u - 26)) : InCone 26 C i j := by
  have hj' : j < C.gates.length := hj
  have hgate : gateAt C j = C.gates[j] := by simp [gateAt, List.getD_eq_getElem?_getD, hj']
  let pre := C.gates.take j
  let post := C.gates.drop (j + 1)
  have hs : C.gates = pre ++ C.gates[j] :: post := by
    dsimp only [pre, post]
    rw [List.cons_getElem_drop_succ, List.take_append_drop]
  have hpre : pre.length = j := by simp [pre]; omega
  let w := pre.foldl (coneStep 26) []
  have hw : w.length = j := by rw [cone_length, hpre]; simp
  have hsmall : u - 26 < w.length := by omega
  have hEq : (cones 26 C).getD (u - 26) [] = w.getD (u - 26) [] := by
    unfold cones
    rw [hs, List.foldl_append]
    exact cone_prefix 26 (C.gates[j] :: post) w _ hsmall
  have hjEq : (cones 26 C).getD j [] =
      ((gateAt C j).inputs.filter fun v => decide (26 ≤ v ∧ v < 26 + j)).flatMap
        (fun v => (v - 26) :: w.getD (v - 26) []) := by
    unfold cones
    rw [hs, List.foldl_append, List.foldl_cons]
    have hlt : j < (coneStep 26 w C.gates[j]).length := by simp [coneStep, hw]
    rw [cone_prefix 26 post (coneStep 26 w C.gates[j]) j hlt]
    rw [hgate]
    simp [coneStep, List.getD_eq_getElem?_getD, hw]
  unfold InCone
  rw [hjEq, List.mem_flatMap]
  refine ⟨u, by simpa using ⟨hu, h₂, h₃⟩, ?_⟩
  rw [List.mem_cons, ← hEq]
  exact hi

lemma tail_in_cone (C : Circuit) (hb : ReadsBack 26 C) (v : ℕ) (hv : 26 ≤ v) :
    ∀ u < 26 + C.size, v ∈ tails C u →
      v = u ∨ InCone 26 C (v - 26) (u - 26) := by
  intro u
  induction u using Nat.strong_induction_on with
  | ind u ih =>
    intro hu hT
    by_cases hOr : isOr C u
    · have h26 := hOr.1
      rw [tails_or C hb u hOr, mem_biUnion] at hT
      obtain ⟨k, hk, hTail⟩ := hT
      have hk' : k ∈ (gateAt C (u - 26)).inputs := by
        simpa [child, hOr.1, hOr.2.1] using hk
      have hklt := hb (u - 26) hOr.2.1 k hk'
      have hkLow : 26 ≤ k := hv.trans (tails_nonOr C hb k v hTail).1
      apply Or.inr
      apply cone_of_child C _ _ k hOr.2.1 hk' hkLow hklt
      obtain h | h := ih k (by omega) (by omega) hTail
      · exact Or.inl (congrArg (· - 26) h)
      · exact Or.inr h
    · rw [tails_stop C u hOr, mem_singleton] at hT
      exact Or.inl hT

lemma gate_and_of_not_or (C : Circuit) (hm : Monotone2 C) (t : ℕ)
    (hlo : 26 ≤ t) (hhi : t < 26 + C.size) (hn : ¬ isOr C t) :
    (gateAt C (t - 26)).op = .and := by
  have ht : t - 26 < C.gates.length := by unfold Circuit.size at hhi; omega
  have hg : gateAt C (t - 26) ∈ C.gates := by simp [gateAt, List.getD_eq_getElem?_getD, ht]
  rcases (show (gateAt C (t - 26)).op = .and ∨ (gateAt C (t - 26)).op = .or by simpa using (hm _ hg).1) with h | h
  · exact h
  · exact (hn ⟨hlo, ht, h⟩).elim

lemma pure_of_no_nested (C : Circuit) (a b : ℕ) (hm : Monotone2 C) (hb : ReadsBack 26 C)
    (ha : a < 26 + C.size) (hf : b < 26 + C.size) (hz : PEqualNP.TopForm.andPairs 26 C = 0)
    (t : ℕ) (ht : t ∈ tails C a ∪ tails C b)
    (u : ℕ) (hu : u ∈ child C t) (v : ℕ) (hv : v ∈ tails C u) : v < 26 := by
  let _ : DecidableEq GateOp := gateOpDecEq
  by_contra! h26
  have htTop : t < 26 + C.size ∧ ¬ isOr C t := by
    rcases mem_union.mp ht with hx | hx
    · exact ⟨((tails_nonOr C hb _ _ hx).1).trans_lt ha, (tails_nonOr C hb _ _ hx).2⟩
    · exact ⟨((tails_nonOr C hb _ _ hx).1).trans_lt hf, (tails_nonOr C hb _ _ hx).2⟩
  have hU := (child_bound C hm hb t).2 u hu
  have hV := tails_nonOr C hb u v hv
  have ht26 := h26.trans (hV.1.trans hU.le)
  have hhiV := (hV.1.trans_lt hU).trans htTop.1
  have hJ : t - 26 < C.gates.length := by have := htTop.1; unfold Circuit.size at this; omega
  have hI : v - 26 < C.gates.length := by unfold Circuit.size at hhiV; omega
  have hJs : t - 26 < C.size := hJ
  have huC : u ∈ (gateAt C (t - 26)).inputs := by simpa [child, ht26, hJs] using hu
  have hu26 := h26.trans hV.1
  have hPath : InCone 26 C (v - 26) (t - 26) := by
    apply cone_of_child C (v - 26) (t - 26) u hJ huC hu26 (by omega)
    rcases tail_in_cone C hb v h26 u (hU.trans htTop.1) hv with h | h
    · exact Or.inl (congrArg (· - 26) h)
    · exact Or.inr h
  unfold PEqualNP.TopForm.andPairs at hz
  rw [card_eq_zero] at hz
  have hEmpty : (v - 26, t - 26) ∈ (∅ : Finset (ℕ × ℕ)) := by
    rw [← hz, mem_filter]
    exact ⟨mem_product.mpr ⟨mem_range.mpr hI, mem_range.mpr hJ⟩,
      gate_and_of_not_or C hm v h26 hhiV hV.2, gate_and_of_not_or C hm t ht26 htTop.1 htTop.2, hPath⟩
  exact notMem_empty _ hEmpty

end PEqualNP.Outside.R_meta_3791_419

theorem PEqualNP.Outside.R_meta_3791_419
    (onePair : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ),   PEqualNP.TopForm.andPairs 26 x1 = 1 → PEqualNP.MetaComplexity.Monotone2 x1 →     PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x1 →       x2 < (26 : ℕ) + x1.size →         x3 < (26 : ℕ) + x1.size →           ((26 : ℕ) ≤ x2 → ¬PEqualNP.CleanedNonEdge.OrReaches (26 : ℕ) x1 x3 (x2 - (26 : ℕ))) →             ((26 : ℕ) ≤ x3 → ¬PEqualNP.CleanedNonEdge.OrReaches (26 : ℕ) x1 x2 (x3 - (26 : ℕ))) →               have x10 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};               have x11 : Fin (13 : ℕ) → Fin (13 : ℕ) → List Bool := fun (x11 x12 : Fin (13 : ℕ)) => (List.ofFn fun (x13 : Fin (13 : ℕ)) => Decidable.decide (x13 = x11)) ++ List.ofFn fun (x13 : Fin (13 : ℕ)) => Decidable.decide (x13 = x12);               have x12 : Finset (Fin (13 : ℕ)) → List Bool := fun (x12 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x13 : Fin (13 : ℕ)) => Decidable.decide (x13 ∈ x12)) ++ List.ofFn fun (x13 : Fin (13 : ℕ)) => Decidable.decide (∀ x14 ∈ x12, x14 - x13 ∉ x10);               have x13 : Finset (Fin (13 : ℕ)) → Prop := fun (x13 : Finset (Fin (13 : ℕ))) => x13.card = (4 : ℕ) ∧ ∀ (x14 : Fin (13 : ℕ)), {x15 ∈ x13 | x15 - x14 ∈ x10}.card ≤ (2 : ℕ);               have x14 : ℕ → List Bool → Bool := fun (x14 : ℕ) (x15 : List Bool) => (x1.wires x15).getD x14 Bool.false;               (∀ (x15 x16 : Fin (13 : ℕ)), x15 - x16 ∈ x10 → x14 x2 (x11 x15 x16) = Bool.true ∨ x14 x3 (x11 x15 x16) = Bool.true) → (∀ (x16 : Finset (Fin (13 : ℕ))), x13 x16 → x14 x2 (x12 x16) = Bool.false ∧ x14 x3 (x12 x16) = Bool.false) → (∃ (x17 : Fin (13 : ℕ)) (x18 : Fin (13 : ℕ)), x17 - x18 ∈ x10 ∧ x14 x2 (x11 x17 x18) = Bool.true ∧ x14 x3 (x11 x17 x18) = Bool.false) → (∃ (x18 : Fin (13 : ℕ)) (x19 : Fin (13 : ℕ)), x18 - x19 ∈ x10 ∧ x14 x3 (x11 x18 x19) = Bool.true ∧ x14 x2 (x11 x18 x19) = Bool.false) → (63 : ℕ) ≤ x1.size)
    (manyPairs : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ),   2 ≤ PEqualNP.TopForm.andPairs 26 x1 → PEqualNP.MetaComplexity.Monotone2 x1 →     PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x1 →       x2 < (26 : ℕ) + x1.size →         x3 < (26 : ℕ) + x1.size →           ((26 : ℕ) ≤ x2 → ¬PEqualNP.CleanedNonEdge.OrReaches (26 : ℕ) x1 x3 (x2 - (26 : ℕ))) →             ((26 : ℕ) ≤ x3 → ¬PEqualNP.CleanedNonEdge.OrReaches (26 : ℕ) x1 x2 (x3 - (26 : ℕ))) →               have x10 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};               have x11 : Fin (13 : ℕ) → Fin (13 : ℕ) → List Bool := fun (x11 x12 : Fin (13 : ℕ)) => (List.ofFn fun (x13 : Fin (13 : ℕ)) => Decidable.decide (x13 = x11)) ++ List.ofFn fun (x13 : Fin (13 : ℕ)) => Decidable.decide (x13 = x12);               have x12 : Finset (Fin (13 : ℕ)) → List Bool := fun (x12 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x13 : Fin (13 : ℕ)) => Decidable.decide (x13 ∈ x12)) ++ List.ofFn fun (x13 : Fin (13 : ℕ)) => Decidable.decide (∀ x14 ∈ x12, x14 - x13 ∉ x10);               have x13 : Finset (Fin (13 : ℕ)) → Prop := fun (x13 : Finset (Fin (13 : ℕ))) => x13.card = (4 : ℕ) ∧ ∀ (x14 : Fin (13 : ℕ)), {x15 ∈ x13 | x15 - x14 ∈ x10}.card ≤ (2 : ℕ);               have x14 : ℕ → List Bool → Bool := fun (x14 : ℕ) (x15 : List Bool) => (x1.wires x15).getD x14 Bool.false;               (∀ (x15 x16 : Fin (13 : ℕ)), x15 - x16 ∈ x10 → x14 x2 (x11 x15 x16) = Bool.true ∨ x14 x3 (x11 x15 x16) = Bool.true) → (∀ (x16 : Finset (Fin (13 : ℕ))), x13 x16 → x14 x2 (x12 x16) = Bool.false ∧ x14 x3 (x12 x16) = Bool.false) → (∃ (x17 : Fin (13 : ℕ)) (x18 : Fin (13 : ℕ)), x17 - x18 ∈ x10 ∧ x14 x2 (x11 x17 x18) = Bool.true ∧ x14 x3 (x11 x17 x18) = Bool.false) → (∃ (x18 : Fin (13 : ℕ)) (x19 : Fin (13 : ℕ)), x18 - x19 ∈ x10 ∧ x14 x3 (x11 x18 x19) = Bool.true ∧ x14 x2 (x11 x18 x19) = Bool.false) → (63 : ℕ) ≤ x1.size) : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 →     PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x1 →       x2 < (26 : ℕ) + x1.size →         x3 < (26 : ℕ) + x1.size →           ((26 : ℕ) ≤ x2 → ¬PEqualNP.CleanedNonEdge.OrReaches (26 : ℕ) x1 x3 (x2 - (26 : ℕ))) →             ((26 : ℕ) ≤ x3 → ¬PEqualNP.CleanedNonEdge.OrReaches (26 : ℕ) x1 x2 (x3 - (26 : ℕ))) →               have x10 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};               have x11 : Fin (13 : ℕ) → Fin (13 : ℕ) → List Bool := fun (x11 x12 : Fin (13 : ℕ)) => (List.ofFn fun (x13 : Fin (13 : ℕ)) => Decidable.decide (x13 = x11)) ++ List.ofFn fun (x13 : Fin (13 : ℕ)) => Decidable.decide (x13 = x12);               have x12 : Finset (Fin (13 : ℕ)) → List Bool := fun (x12 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x13 : Fin (13 : ℕ)) => Decidable.decide (x13 ∈ x12)) ++ List.ofFn fun (x13 : Fin (13 : ℕ)) => Decidable.decide (∀ x14 ∈ x12, x14 - x13 ∉ x10);               have x13 : Finset (Fin (13 : ℕ)) → Prop := fun (x13 : Finset (Fin (13 : ℕ))) => x13.card = (4 : ℕ) ∧ ∀ (x14 : Fin (13 : ℕ)), {x15 ∈ x13 | x15 - x14 ∈ x10}.card ≤ (2 : ℕ);               have x14 : ℕ → List Bool → Bool := fun (x14 : ℕ) (x15 : List Bool) => (x1.wires x15).getD x14 Bool.false;               (∀ (x15 x16 : Fin (13 : ℕ)), x15 - x16 ∈ x10 → x14 x2 (x11 x15 x16) = Bool.true ∨ x14 x3 (x11 x15 x16) = Bool.true) → (∀ (x16 : Finset (Fin (13 : ℕ))), x13 x16 → x14 x2 (x12 x16) = Bool.false ∧ x14 x3 (x12 x16) = Bool.false) → (∃ (x17 : Fin (13 : ℕ)) (x18 : Fin (13 : ℕ)), x17 - x18 ∈ x10 ∧ x14 x2 (x11 x17 x18) = Bool.true ∧ x14 x3 (x11 x17 x18) = Bool.false) → (∃ (x18 : Fin (13 : ℕ)) (x19 : Fin (13 : ℕ)), x18 - x19 ∈ x10 ∧ x14 x3 (x11 x18 x19) = Bool.true ∧ x14 x2 (x11 x18 x19) = Bool.false) → (63 : ℕ) ≤ x1.size := by
  intro C a b hm hb ha hbound hab hba
  dsimp only
  intro hpos hneg hA hB
  by_cases hZero : PEqualNP.TopForm.andPairs 26 C = 0
  · exact PEqualNP.Outside.R_meta_3791_419.single_layer_bound C a b hm hb ha hbound hpos hneg
      (fun t ht _ => PEqualNP.Outside.R_meta_3791_419.pure_of_no_nested C a b hm hb ha hbound hZero t ht)
  · by_cases hOne : PEqualNP.TopForm.andPairs 26 C = 1
    · exact onePair C a b hOne hm hb ha hbound hab hba hpos hneg hA hB
    · exact manyPairs C a b (by omega) hm hb ha hbound hab hba hpos hneg hA hB
