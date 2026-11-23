import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_782

open PEqualNP.CircuitLowerBounds

def fw {α : Type} (f : List α → Gate → α) (gs : List Gate) (init : List α) : List α :=
  gs.foldl (fun w g => w ++ [f w g]) init

lemma fw_nil {α : Type} (f : List α → Gate → α) (init : List α) : fw f [] init = init := rfl

lemma fw_cons {α : Type} (f : List α → Gate → α) (g : Gate) (gs : List Gate) (init : List α) :
    fw f (g :: gs) init = fw f gs (init ++ [f init g]) := rfl

lemma fw_append {α : Type} (f : List α → Gate → α) (gs hs : List Gate) (init : List α) :
    fw f (gs ++ hs) init = fw f hs (fw f gs init) := by
  simp [fw, List.foldl_append]

lemma fw_snoc {α : Type} (f : List α → Gate → α) (gs : List Gate) (g : Gate) (init : List α) :
    fw f (gs ++ [g]) init = fw f gs init ++ [f (fw f gs init) g] := by
  rw [fw_append]; rfl

lemma fw_length {α : Type} (f : List α → Gate → α) (gs : List Gate) (init : List α) :
    (fw f gs init).length = init.length + gs.length := by
  induction gs generalizing init with
  | nil => simp [fw_nil]
  | cons g gs ih => rw [fw_cons, ih]; simp; omega

lemma fw_prefix {α : Type} (f : List α → Gate → α) (gs : List Gate) (init : List α) :
    ∃ r, fw f gs init = init ++ r := by
  induction gs generalizing init with
  | nil => exact ⟨[], by simp [fw_nil]⟩
  | cons g gs ih =>
    obtain ⟨r, hr⟩ := ih (init ++ [f init g])
    exact ⟨[f init g] ++ r, by rw [fw_cons, hr]; simp⟩

lemma getD_append_left' {α : Type} (l r : List α) (i : ℕ) (d : α) (h : i < l.length) :
    (l ++ r).getD i d = l.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma getD_take' {α : Type} (l : List α) (m i : ℕ) (d : α) :
    (l.take m).getD i d = if i < m then l.getD i d else d := by
  split_ifs with h
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, h]

lemma fw_take {α : Type} (f : List α → Gate → α) (gs : List Gate) (init : List α) (j : ℕ)
    (hj : j ≤ gs.length) :
    (fw f gs init).take (init.length + j) = fw f (gs.take j) init := by
  have h := List.take_append_drop j gs
  conv_lhs => rw [← h, fw_append]
  obtain ⟨r, hr⟩ := fw_prefix f (gs.drop j) (fw f (gs.take j) init)
  rw [hr]
  have hl : (fw f (gs.take j) init).length = init.length + j := by
    rw [fw_length]; simp; omega
  rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]

lemma fw_getD_gate {α : Type} (f : List α → Gate → α) (gs : List Gate) (init : List α) (j : ℕ)
    (hj : j < gs.length) (d : α) :
    (fw f gs init).getD (init.length + j) d =
      f ((fw f gs init).take (init.length + j)) gs[j] := by
  rw [fw_take f gs init j hj.le]
  have h : gs = gs.take j ++ [gs[j]] ++ gs.drop (j + 1) := by
    simp
  conv_lhs => rw [h, fw_append, fw_snoc]
  obtain ⟨r, hr⟩ := fw_prefix f (gs.drop (j + 1)) (fw f (gs.take j) init ++ [f (fw f (gs.take j) init) gs[j]])
  rw [hr]
  have hl : (fw f (gs.take j) init).length = init.length + j := by
    rw [fw_length]; simp; omega
  rw [getD_append_left' _ _ _ _ (by simp; omega)]
  simp [List.getD_eq_getElem?_getD, hl]


section W

variable (n : ℕ) (C : Circuit)

def val (x : Fin n → Bool) (w : ℕ) : Bool := (C.wires (List.ofFn x)).getD w false

def ev (a : Fin n) : Fin n → Bool := fun b => decide (b = a)

def Iset (w : ℕ) : Finset (Fin n) := Finset.univ.filter fun a => val n C (ev n a) w = true

def Priv (S : Finset (Fin n)) (w : ℕ) : Prop := Iset n C w ⊆ S ∧ 2 ≤ (Iset n C w).card

def gw (w : ℕ) : Gate := C.gates.getD (w - n) ⟨GateOp.or, []⟩

def in0 (w : ℕ) : ℕ := (gw n C w).inputs.getD 0 0

def in1 (w : ℕ) : ℕ := (gw n C w).inputs.getD 1 0

def rd (ν : ℕ → Bool) (w u : ℕ) : Bool := if u < w then ν u else false

def comb : GateOp → Bool → Bool → Bool
  | GateOp.and, p, q => p && q
  | _, p, q => p || q

lemma comb_mono (op : GateOp) (p q p' q' : Bool) (hp : p = true → p' = true) (hq : q = true → q' = true)
    (h : comb op p q = true) : comb op p' q' = true := by
  cases op <;> simp only [comb, Bool.and_eq_true, Bool.or_eq_true] at h ⊢ <;> tauto

lemma wires_eq (z : List Bool) : C.wires z =
    fw (fun w g => g.op.eval (g.inputs.map fun i => w.getD i false)) C.gates z := rfl

lemma val_input (x : Fin n → Bool) (w : ℕ) (hw : w < n) : val n C x w = x ⟨w, hw⟩ := by
  unfold val
  rw [wires_eq]
  obtain ⟨r, hr⟩ := fw_prefix (fun w g => g.op.eval (g.inputs.map fun i => w.getD i false))
    C.gates (List.ofFn x)
  rw [hr, getD_append_left' _ _ _ _ (by simp; exact hw)]
  simp [List.getD_eq_getElem?_getD, hw]

lemma val_ge (x : Fin n → Bool) (w : ℕ) (hw : n + C.gates.length ≤ w) : val n C x w = false := by
  unfold val
  apply List.getD_eq_default
  rw [wires_eq, fw_length]; simp; omega

lemma val_gate (x : Fin n → Bool) (j : ℕ) (hj : j < C.gates.length) :
    val n C x (n + j) =
      C.gates[j].op.eval (C.gates[j].inputs.map fun i => if i < n + j then val n C x i else false) := by
  have h := fw_getD_gate (fun w g => g.op.eval (g.inputs.map fun i => w.getD i false)) C.gates
    (List.ofFn x) j hj false
  simp only [List.length_ofFn] at h
  unfold val
  rw [wires_eq, h]
  simp only [getD_take']

lemma gate_eq (hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (x : Fin n → Bool) (w : ℕ) (hw1 : n ≤ w) (hw2 : w < n + C.gates.length) :
    val n C x w = comb (gw n C w).op (rd (val n C x) w (in0 n C w)) (rd (val n C x) w (in1 n C w)) := by
  have e : w = n + (w - n) := by omega
  have hj : w - n < C.gates.length := by omega
  have hgw : gw n C w = C.gates[w - n] := by
    simp [gw, List.getD_eq_getElem?_getD, hj]
  obtain ⟨hop, hlen⟩ := hg _ (List.getElem_mem hj)
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
  unfold in0 in1
  rw [hgw, hab]
  conv_lhs => rw [e, val_gate n C x (w - n) hj, hab]
  rw [← e]
  rcases hop with hop | hop <;> rw [hop] <;> simp [GateOp.eval, comb, rd]

lemma val_mono (hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (x x' : Fin n → Bool) (hx : ∀ q, x q = true → x' q = true) (w : ℕ) (h : val n C x w = true) :
    val n C x' w = true := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases h1 : w < n
    · rw [val_input n C x w h1] at h; rw [val_input n C x' w h1]; exact hx _ h
    · by_cases h2 : w < n + C.gates.length
      · rw [gate_eq n C hg x w (by omega) h2] at h
        rw [gate_eq n C hg x' w (by omega) h2]
        refine comb_mono _ _ _ _ _ ?_ ?_ h
        · unfold rd; split_ifs with hh
          · exact ih _ hh
          · exact id
        · unfold rd; split_ifs with hh
          · exact ih _ hh
          · exact id
      · rw [val_ge n C x w (by omega)] at h; exact absurd h (by simp)

lemma Iset_input (w : ℕ) (hw : w < n) : (Iset n C w).card = 1 := by
  have : Iset n C w = {⟨w, hw⟩} := by
    ext a
    simp only [Iset, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
      val_input n C _ w hw, ev, decide_eq_true_eq]
    constructor
    · intro h; exact h.symm
    · intro h; exact h.symm
  rw [this]; simp

lemma Iset_ge (w : ℕ) (hw : n + C.gates.length ≤ w) : (Iset n C w).card = 0 := by
  have : Iset n C w = ∅ := by
    ext a
    simp [Iset, val_ge n C _ w hw]
  rw [this]; simp

lemma priv_bounds (S : Finset (Fin n)) (w : ℕ) (h : Priv n C S w) : n ≤ w ∧ w < n + C.gates.length := by
  obtain ⟨-, h2⟩ := h
  constructor
  · by_contra hc; rw [Iset_input n C w (by omega)] at h2; omega
  · by_contra hc; rw [Iset_ge n C w (by omega)] at h2; omega

def prel (S : Finset (Fin n)) (u h : ℕ) : Prop :=
  Priv n C S u ∧ Priv n C S h ∧ u < h ∧ (u = in0 n C h ∨ u = in1 n C h)

noncomputable def Rset (S : Finset (Fin n)) (r : ℕ) : Finset ℕ :=
  @Finset.filter _ (fun w => Relation.ReflTransGen (prel n C S) w r) (Classical.decPred _)
    (Finset.range (n + C.gates.length))

lemma mem_R (S : Finset (Fin n)) (r w : ℕ) :
    w ∈ Rset n C S r ↔ w < n + C.gates.length ∧ Relation.ReflTransGen (prel n C S) w r := by
  simp only [Rset, Finset.mem_filter, Finset.mem_range]

lemma R_priv (S : Finset (Fin n)) (r : ℕ) (hr : Priv n C S r) (w : ℕ) (hw : w ∈ Rset n C S r) :
    Priv n C S w := by
  obtain ⟨-, h⟩ := (mem_R n C S r w).mp hw
  rcases Relation.ReflTransGen.cases_head h with h | ⟨c, hc, -⟩
  · rw [h]; exact hr
  · exact hc.1

lemma R_closed (S : Finset (Fin n)) (r : ℕ) (hr : Priv n C S r) (h : ℕ) (hh : h ∈ Rset n C S r)
    (u : ℕ) (hu : u = in0 n C h ∨ u = in1 n C h) (hlt : u < h) (hpu : Priv n C S u) :
    u ∈ Rset n C S r := by
  obtain ⟨hb, hreach⟩ := (mem_R n C S r h).mp hh
  refine (mem_R n C S r u).mpr ⟨by omega, ?_⟩
  exact Relation.ReflTransGen.head ⟨hpu, R_priv n C S r hr h hh, hlt, hu⟩ hreach

lemma R_parent (S : Finset (Fin n)) (r : ℕ) (w : ℕ) (hw : w ∈ Rset n C S r) (hne : w ≠ r) :
    ∃ h ∈ Rset n C S r, w = in0 n C h ∨ w = in1 n C h := by
  obtain ⟨-, hreach⟩ := (mem_R n C S r w).mp hw
  rcases Relation.ReflTransGen.cases_head hreach with h | ⟨c, hc, hc2⟩
  · exact absurd h hne
  · refine ⟨c, (mem_R n C S r c).mpr ⟨?_, hc2⟩, hc.2.2.2⟩
    exact (priv_bounds n C S c hc.2.1).2

lemma r_mem (S : Finset (Fin n)) (r : ℕ) (hr : Priv n C S r) : r ∈ Rset n C S r :=
  (mem_R n C S r r).mpr ⟨(priv_bounds n C S r hr).2, Relation.ReflTransGen.refl⟩

def Eset (R : Finset ℕ) : Finset ℕ :=
  R.biUnion fun h => (({in0 n C h, in1 n C h} : Finset ℕ).filter fun u => u < h ∧ u ∉ R)

lemma mem_E (R : Finset ℕ) (u : ℕ) :
    u ∈ Eset n C R ↔ ∃ h ∈ R, (u = in0 n C h ∨ u = in1 n C h) ∧ u < h ∧ u ∉ R := by
  unfold Eset
  simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]

lemma card_E (S : Finset (Fin n)) (r : ℕ) (hr : Priv n C S r) :
    (Eset n C (Rset n C S r)).card ≤ (Rset n C S r).card + 1 := by
  set R := Rset n C S r
  have hsub : (R.erase r) ∪ Eset n C R ⊆
      (R ×ˢ (Finset.univ : Finset (Fin 2))).image
        (fun p : ℕ × Fin 2 => if p.2 = 0 then in0 n C p.1 else in1 n C p.1) := by
    intro u hu
    rw [Finset.mem_image]
    rcases Finset.mem_union.mp hu with hu | hu
    · obtain ⟨hne, huR⟩ := Finset.mem_erase.mp hu
      obtain ⟨h, hh, hu'⟩ := R_parent n C S r u huR hne
      rcases hu' with e | e
      · exact ⟨(h, 0), Finset.mem_product.mpr ⟨hh, Finset.mem_univ _⟩, by simp [e]⟩
      · exact ⟨(h, 1), Finset.mem_product.mpr ⟨hh, Finset.mem_univ _⟩, by simp [e]⟩
    · obtain ⟨h, hh, hu', -, -⟩ := (mem_E n C R u).mp hu
      rcases hu' with e | e
      · exact ⟨(h, 0), by simp [hh], by simp [e]⟩
      · exact ⟨(h, 1), by simp [hh], by simp [e]⟩
  have hdis : Disjoint (R.erase r) (Eset n C R) := by
    rw [Finset.disjoint_left]
    intro u hu hE
    obtain ⟨-, -, -, -, hnot⟩ := (mem_E n C R u).mp hE
    exact hnot (Finset.mem_of_mem_erase hu)
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdis] at h1
  have h2 := Finset.card_image_le (s := R ×ˢ (Finset.univ : Finset (Fin 2)))
    (f := fun p : ℕ × Fin 2 => if p.2 = 0 then in0 n C p.1 else in1 n C p.1)
  rw [Finset.card_product, Finset.card_univ, Fintype.card_fin] at h2
  have hrR : r ∈ R := r_mem n C S r hr
  have h3 := Finset.card_erase_of_mem hrR
  have h4 : 1 ≤ R.card := Finset.card_pos.mpr ⟨r, hrR⟩
  omega

lemma compare (R : Finset ℕ) (ν μ : ℕ → Bool)
    (hν : ∀ h ∈ R, ν h = comb (gw n C h).op (rd ν h (in0 n C h)) (rd ν h (in1 n C h)))
    (hμ : ∀ h ∈ R, μ h = comb (gw n C h).op (rd μ h (in0 n C h)) (rd μ h (in1 n C h)))
    (hE : ∀ u ∈ Eset n C R, ν u = true → μ u = true) :
    ∀ h ∈ R, ν h = true → μ h = true := by
  intro h
  induction h using Nat.strong_induction_on with
  | _ h ih =>
    intro hh hv
    rw [hν h hh] at hv
    rw [hμ h hh]
    have key : ∀ u, (u = in0 n C h ∨ u = in1 n C h) → rd ν h u = true → rd μ h u = true := by
      intro u hu
      unfold rd
      split_ifs with hlt
      · intro hvu
        by_cases huR : u ∈ R
        · exact ih u hlt huR hvu
        · exact hE u ((mem_E n C R u).mpr ⟨h, hh, hu, hlt, huR⟩) hvu
      · exact id
    exact comb_mono _ _ _ _ _ (key _ (Or.inl rfl)) (key _ (Or.inr rfl)) hv

def lab (S : Finset (Fin n)) (R : Finset ℕ) (w : ℕ) : Bool :=
  if w ∈ R then
    comb (gw n C w).op
      (if h0 : in0 n C w < w then lab S R (in0 n C w) else false)
      (if h1 : in1 n C w < w then lab S R (in1 n C w) else false)
  else decide (¬ Iset n C w ⊆ S)
termination_by w

lemma lab_R (S : Finset (Fin n)) (R : Finset ℕ) (h : ℕ) (hh : h ∈ R) :
    lab n C S R h = comb (gw n C h).op (rd (lab n C S R) h (in0 n C h)) (rd (lab n C S R) h (in1 n C h)) := by
  rw [lab, if_pos hh]
  simp only [rd, dite_eq_ite]

lemma lab_out (S : Finset (Fin n)) (R : Finset ℕ) (u : ℕ) (hu : u ∉ R) :
    lab n C S R u = decide (¬ Iset n C u ⊆ S) := by
  rw [lab, if_neg hu]

lemma per_out (hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (S : Finset (Fin n)) (r k c : ℕ) (hr : Priv n C S r)
    (hprom : ∀ x : Fin n → Bool, (Finset.univ.filter fun q => x q = true).card ≤ k →
      (∀ q ∈ S, x q = false) → val n C x r = false)
    (hck : c ≤ k) (hcA : c + 1 ≤ (Iset n C r).card) : c ≤ (Rset n C S r).card := by
  classical
  set R := Rset n C S r with hRdef
  have hE : (Eset n C R).card ≤ R.card + 1 := card_E n C S r hr
  have hrR : r ∈ R := r_mem n C S r hr
  have hvalR : ∀ (x : Fin n → Bool), ∀ h ∈ R,
      val n C x h = comb (gw n C h).op (rd (val n C x) h (in0 n C h)) (rd (val n C x) h (in1 n C h)) := by
    intro x h hh
    have := priv_bounds n C S h (R_priv n C S r hr h hh)
    exact gate_eq n C hg x h this.1 this.2
  have hlabR : ∀ h ∈ R, lab n C S R h =
      comb (gw n C h).op (rd (lab n C S R) h (in0 n C h)) (rd (lab n C S R) h (in1 n C h)) :=
    fun h hh => lab_R n C S R h hh
  by_cases hl : lab n C S R r = true
  · -- the label at the root is true: the promise
    have hpick : ∀ u ∈ Eset n C R, ¬ Iset n C u ⊆ S → ∃ a : Fin n, a ∉ S ∧ a ∈ Iset n C u := by
      intro u _ hu
      rw [Finset.not_subset] at hu
      obtain ⟨a, ha, hna⟩ := hu
      exact ⟨a, hna, ha⟩
    have hne : Nonempty (Fin n) := by
      obtain ⟨a, -⟩ := Finset.card_pos.mp (by omega : 0 < (Iset n C r).card); exact ⟨a⟩
    choose! pk hpkS hpkI using hpick
    let EL := (Eset n C R).filter fun u => ¬ Iset n C u ⊆ S
    let X := EL.image pk
    let x : Fin n → Bool := fun q => decide (q ∈ X)
    have hxr : val n C x r = true := by
      refine compare n C R (lab n C S R) (val n C x) hlabR (hvalR x) ?_ r hrR hl
      intro u hu hlu
      have huR : u ∉ R := by obtain ⟨-, -, -, -, h⟩ := (mem_E n C R u).mp hu; exact h
      rw [lab_out n C S R u huR] at hlu
      have hns : ¬ Iset n C u ⊆ S := by simpa using hlu
      have hmem := hpkI u hu hns
      simp only [Iset, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
      apply val_mono n C hg _ x _ u hmem
      intro q hq
      simp only [ev, decide_eq_true_eq] at hq
      subst hq
      simp only [x, decide_eq_true_eq, X, Finset.mem_image]
      exact ⟨u, Finset.mem_filter.mpr ⟨hu, hns⟩, rfl⟩
    have hXS : ∀ q ∈ S, x q = false := by
      intro q hq
      simp only [x, decide_eq_false_iff_not, X, Finset.mem_image, not_exists, not_and]
      intro u hu hpq
      have hu' := Finset.mem_filter.mp hu
      have := hpkS u hu'.1 hu'.2
      rw [hpq] at this
      exact this hq
    have hcard : (Finset.univ.filter fun q => x q = true).card ≤ (Eset n C R).card := by
      have : (Finset.univ.filter fun q => x q = true) = X := by
        ext q; simp [x]
      rw [this]
      exact le_trans Finset.card_image_le (Finset.card_filter_le _ _)
    by_contra hcon
    have := hprom x (by omega) hXS
    rw [hxr] at this
    exact absurd this (by simp)
  · -- the label at the root is false: one small exit per accepted index
    have hex : ∀ a ∈ Iset n C r, ∃ u ∈ Eset n C R, Iset n C u ⊆ S ∧ a ∈ Iset n C u := by
      intro a ha
      by_contra hno
      simp only [not_exists, not_and] at hno
      have hra : val n C (ev n a) r = true := by
        simp only [Iset, Finset.mem_filter, Finset.mem_univ, true_and] at ha; exact ha
      have := compare n C R (val n C (ev n a)) (lab n C S R) (hvalR _) hlabR (by
        intro u hu hv
        have huR : u ∉ R := by obtain ⟨-, -, -, -, h⟩ := (mem_E n C R u).mp hu; exact h
        rw [lab_out n C S R u huR]
        by_contra hlu
        have hs : Iset n C u ⊆ S := by simpa using hlu
        exact hno u hu hs (by simp only [Iset, Finset.mem_filter, Finset.mem_univ, true_and]; exact hv)) r hrR hra
      exact hl this
    choose! f hfE hfS hfa using hex
    have hsmall : ∀ a ∈ Iset n C r, (Iset n C (f a)).card ≤ 1 := by
      intro a ha
      by_contra hc
      have hpriv : Priv n C S (f a) := ⟨hfS a ha, by omega⟩
      obtain ⟨h, hh, hu, hlt, hnot⟩ := (mem_E n C R (f a)).mp (hfE a ha)
      exact hnot (R_closed n C S r hr h hh (f a) hu hlt hpriv)
    have hinj : Set.InjOn f (Iset n C r) := by
      intro a ha b hb hab
      have h1 := hfa a ha
      have h2 := hfa b hb
      rw [hab] at h1
      exact Finset.card_le_one.mp (hsmall b hb) a h1 b h2
    have := Finset.card_le_card_of_injOn f (fun a ha => hfE a ha) hinj
    omega

end W

end PEqualNP.Outside.L_meta_782

theorem PEqualNP.Outside.L_meta_782 : ∀ (n m k : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (c : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ i : Fin m, 2 ≤ (Finset.univ.filter (fun a : Fin n => (C.wires (List.ofFn (fun b : Fin n => decide (b = a)))).getD (o i) false = true)).card) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → (∀ (i : Fin m) (p : Fin n), (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (o i) false = true → p ∈ S i) → (∀ (i : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k → (∀ q ∈ S i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false) → (∀ i : Fin m, c i ≤ k) → (∀ i : Fin m, c i + 1 ≤ (Finset.univ.filter (fun a : Fin n => (C.wires (List.ofFn (fun b : Fin n => decide (b = a)))).getD (o i) false = true)).card) → ∑ i : Fin m, c i ≤ C.size := by
  intro n m k S C o c hS hA hg hsub hprom hck hcA
  open PEqualNP.Outside.L_meta_782 in
  have hpriv : ∀ i, Priv n C (S i) (o i) := fun i => ⟨fun a ha => hsub i a (by
      simp only [Iset, Finset.mem_filter, Finset.mem_univ, true_and] at ha; exact ha), hA i⟩
  open PEqualNP.Outside.L_meta_782 in
  have hper : ∀ i, c i ≤ (Rset n C (S i) (o i)).card := fun i =>
    per_out n C hg (S i) (o i) k (c i) (hpriv i) (hprom i) (hck i) (hcA i)
  open PEqualNP.Outside.L_meta_782 in
  have hdis : ∀ i ∈ (Finset.univ : Finset (Fin m)), ∀ j ∈ (Finset.univ : Finset (Fin m)), i ≠ j →
      Disjoint (Rset n C (S i) (o i)) (Rset n C (S j) (o j)) := by
    intro i _ j _ hij
    rw [Finset.disjoint_left]
    intro w hwi hwj
    have p1 := R_priv n C (S i) (o i) (hpriv i) w hwi
    have p2 := R_priv n C (S j) (o j) (hpriv j) w hwj
    have := Finset.card_le_card (Finset.subset_inter p1.1 p2.1)
    have := hS i j hij
    have := p1.2
    omega
  open PEqualNP.Outside.L_meta_782 in
  have hsubU : (Finset.univ.biUnion fun i => Rset n C (S i) (o i)) ⊆ Finset.Ico n (n + C.gates.length) := by
    intro w hw
    obtain ⟨i, -, hwi⟩ := Finset.mem_biUnion.mp hw
    have := priv_bounds n C (S i) w (R_priv n C (S i) (o i) (hpriv i) w hwi)
    exact Finset.mem_Ico.mpr this
  have h1 := Finset.card_le_card hsubU
  rw [Finset.card_biUnion hdis] at h1
  simp only [Nat.card_Ico] at h1
  have h2 := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin m))) => hper i)
  show _ ≤ C.gates.length
  omega
