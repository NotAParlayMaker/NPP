import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds


namespace PEqualNP.Outside.L_meta_1407.ReverseDemand

/- Each request asks for the labels associated to one wire. Visit the wires from
the output backwards. At most one remaining request needs to expand each wire. -/

variable {Role Token : Type} [DecidableEq Role] [DecidableEq Token]

abbrev Req (Role : Type) := ℕ × Role

lemma collect {n : ℕ}
    (ok : Req Role → Prop) (raw : Req Role → Finset Token)
    (inherited : ℕ → Set Token) (child : Req Role → Finset (Req Role))
    (hin : ∀ r, ok r → r.1 < n → (raw r).card ≤ 1 ∧ inherited r.1 = ∅)
    (hchild : ∀ r, ok r → n ≤ r.1 → (child r).card ≤ 2 ∧
      ∀ q ∈ child r, q.1 < r.1 ∧ ok q)
    (hstep : ∀ r, ok r → n ≤ r.1 → ∀ a, a ∈ raw r ∨ a ∈ inherited r.1 →
      ∃ q ∈ child r, a ∈ raw q ∨ a ∈ inherited q.1)
    (hprimary : ∀ w (F : Finset (Req Role)), F.Nonempty →
      (∀ r ∈ F, r.1 = w ∧ ok r) →
      ∃ p ∈ F, ∃ extra : Finset Token, extra.card + 1 ≤ F.card ∧
        ∀ q ∈ F, raw q ⊆ extra ∪ raw p)
    (t : ℕ) (pending : Finset (Req Role))
    (hpend : ∀ r ∈ pending, r.1 < n + t ∧ ok r) :
    ∃ A : Finset Token, A.card ≤ pending.card + t ∧
      ∀ r ∈ pending, ∀ a, a ∈ raw r ∨ a ∈ inherited r.1 → a ∈ A := by
  classical
  induction t generalizing pending with
  | zero =>
      have hlow (r) (hr : r ∈ pending) : r.1 < n := by
        simpa using (hpend r hr).1
      refine ⟨pending.biUnion raw, ?_, ?_⟩
      · simpa using Finset.card_biUnion_le_card_mul pending raw 1
          (fun r hr => (hin r (hpend r hr).2 (hlow r hr)).1)
      · intro r hr a ha
        rcases ha with har | han
        · exact Finset.mem_biUnion.mpr ⟨r, hr, har⟩
        · simp [(hin r (hpend r hr).2 (hlow r hr)).2] at han
  | succ t ih =>
      let high := pending.filter (fun r => r.1 = n + t)
      let low := pending.filter (fun r => r.1 ≠ n + t)
      have hhigh : ∀ r ∈ high, r.1 = n + t ∧ ok r := by
        intro r hr
        obtain ⟨hm, he⟩ := Finset.mem_filter.mp hr
        exact ⟨he, (hpend r hm).2⟩
      have hlow : ∀ r ∈ low, r.1 < n + t ∧ ok r := by
        intro r hr
        obtain ⟨hm, hn⟩ := Finset.mem_filter.mp hr
        obtain ⟨hlt, hok⟩ := hpend r hm
        exact ⟨by omega, hok⟩
      by_cases hex : high.Nonempty
      · obtain ⟨p, hp, extra, hcost, hraw⟩ := hprimary (n + t) high hex hhigh
        obtain ⟨hpi, hpo⟩ := hhigh p hp
        have hpn : n ≤ p.1 := by omega
        let next := low ∪ child p
        have hn : ∀ r ∈ next, r.1 < n + t ∧ ok r := by
          intro r hr
          rcases Finset.mem_union.mp hr with hl | hc
          · exact hlow r hl
          · obtain ⟨hlt, hok⟩ := (hchild p hpo hpn).2 r hc
            exact ⟨by omega, hok⟩
        obtain ⟨below, hb, hcover⟩ := ih next hn
        have hpart : low.card + high.card = pending.card := by
          have hd : Disjoint low high := Finset.disjoint_left.mpr (fun r hl hh =>
            (Finset.mem_filter.mp hl).2 (hhigh r hh).1)
          have hu : low ∪ high = pending := by
            ext r
            by_cases h : r.1 = n+t <;> simp [low, high, h]
          rw [← Finset.card_union_of_disjoint hd, hu]
        have hall (a : Token) (ha : a ∈ raw p ∨ a ∈ inherited p.1) : a ∈ below := by
          obtain ⟨r, hr, hmem⟩ := hstep p hpo hpn a ha
          exact hcover r (Finset.mem_union_right _ hr) a hmem
        refine ⟨below ∪ extra, ?_, ?_⟩
        · have hu := Finset.card_union_le below extra
          have hcl := Finset.card_union_le low (child p)
          have hc := (hchild p hpo hpn).1
          change next.card ≤ _ at hcl
          omega
        · intro r hr a ha
          by_cases hrw : r.1 = n+t
          · have hh : r ∈ high := Finset.mem_filter.mpr ⟨hr, hrw⟩
            rcases ha with har | han
            · rcases Finset.mem_union.mp (hraw r hh har) with hx | hpraw
              · exact Finset.mem_union_right _ hx
              · exact Finset.mem_union_left _ (hall a (Or.inl hpraw))
            · exact Finset.mem_union_left _ (hall a (Or.inr (by simpa only [hpi, hrw] using han)))
          · have hl : r ∈ low := Finset.mem_filter.mpr ⟨hr, hrw⟩
            exact Finset.mem_union_left _ (hcover r (Finset.mem_union_left _ hl) a ha)
      · have hp : ∀ r ∈ pending, r.1 < n + t ∧ ok r := by
          intro r hr
          have hne : r.1 ≠ n+t := fun he => hex ⟨r, Finset.mem_filter.mpr ⟨hr, he⟩⟩
          exact hlow r (Finset.mem_filter.mpr ⟨hr, hne⟩)
        obtain ⟨A, ha, hc⟩ := ih pending hp
        exact ⟨A, by omega, hc⟩

end PEqualNP.Outside.L_meta_1407.ReverseDemand

namespace PEqualNP.Outside.L_meta_1407

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih => rw [run_cons, ih]; simp; omega

lemma run_getD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (run gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

lemma run_split (gs : List Gate) (x : List Bool) (j : ℕ) :
    run gs x = run (gs.drop j) (run (gs.take j) x) := by
  simpa only [run, List.foldl_append] using
    congrArg (fun l : List Gate => run l x) (List.take_append_drop j gs).symm

def value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma input_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (p : Fin n) :
    value C x p = x p := by
  change (run C.gates (List.ofFn x)).getD p false = x p
  have hp : (p : ℕ) < (List.ofFn x).length := by simp
  rw [run_getD _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp

lemma missing_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.size ≤ w) : value C x w = false := by
  change (run C.gates (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by simpa [run_length, Circuit.size] using hw)

-- At a gate, reads of earlier wires agree with the completed run.
-- All other reads contribute false, even if the wire is produced later.
lemma gate_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
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


private def gateAt (n : ℕ) (C : Circuit) (w : ℕ) : Option Gate :=
  if n ≤ w then C.gates[w - n]? else none

private lemma gateAt_mem {n w : ℕ} {C : Circuit} {g : Gate}
    (h : gateAt n C w = some g) : g ∈ C.gates := by
  unfold gateAt at h
  split at h
  · exact List.mem_of_getElem? h
  · simp at h

private lemma gateAt_rec {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) :
    value C x w = if h : w < n then x ⟨w, h⟩ else
      match gateAt n C w with
      | none => false
      | some g => g.op.eval (g.inputs.map fun r => if r < w then value C x r else false) := by
  split
  · exact input_value C x ⟨w, by assumption⟩
  · rename_i hn
    by_cases hw : w < n + C.size
    · have hj : w - n < C.gates.length := by unfold Circuit.size at hw; omega
      simp only [gateAt, Nat.le_of_not_gt hn, ite_true, List.getElem?_eq_getElem hj]
      exact gate_value C x w (by omega) hw
    · have hj : C.gates.length ≤ w - n := by unfold Circuit.size at hw; omega
      simp only [gateAt, Nat.le_of_not_gt hn, ite_true, List.getElem?_eq_none hj]
      exact missing_value C x w (by omega)

private def support {n} (C : Circuit) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun p => value C (fun v => decide (v = p)) w = true

private lemma mem_support {n} {C : Circuit} {w : ℕ} {p : Fin n} :
    p ∈ support C w ↔ value C (fun v => decide (v = p)) w = true := by
  simp [support]

private lemma support_input {n} (C : Circuit) (p : Fin n) :
    support C p = {p} := by
  ext q
  rw [mem_support, input_value, Finset.mem_singleton]
  simp [eq_comm]

private def prev (n : ℕ) (C : Circuit) (w : ℕ) : Finset ℕ :=
  match gateAt n C w with
  | none => ∅
  | some g => g.inputs.toFinset.filter (· < w)

private lemma prev_mem {n w r : ℕ} {C : Circuit} {g : Gate}
    (hg : gateAt n C w = some g) : r ∈ prev n C w ↔ r ∈ g.inputs ∧ r < w := by
  simp [prev, hg]

private lemma and_eval {n w : ℕ} {C : Circuit} {g : Gate} (x : Fin n → Bool)
    (hg : gateAt n C w = some g) (hop : g.op = .and) :
    value C x w = true ↔ ∀ r ∈ g.inputs, r < w ∧ value C x r = true := by
  have hn : ¬ w < n := by
    intro h
    simp [gateAt, Nat.not_le_of_lt h] at hg
  rw [gateAt_rec C x w, dite_eq_right hn, hg]
  change g.op.eval _ = true ↔ _
  simp only [hop, GateOp.eval, List.all_eq_true, id_eq]
  constructor
  · intro h r hr
    have ht := h _ (List.mem_map.mpr ⟨r,hr,rfl⟩)
    by_cases hlt : r < w
    · exact ⟨hlt, by simpa [hlt] using ht⟩
    · simp [hlt] at ht
  · intro h y hy
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hy
    obtain ⟨hlt,hv⟩ := h r hr
    simpa [hlt] using hv

private lemma or_eval {n w : ℕ} {C : Circuit} {g : Gate} (x : Fin n → Bool)
    (hg : gateAt n C w = some g) (hop : g.op = .or) :
    value C x w = true ↔ ∃ r ∈ prev n C w, value C x r = true := by
  have hn : ¬ w < n := by
    intro h
    simp [gateAt, Nat.not_le_of_lt h] at hg
  rw [gateAt_rec C x w, dite_eq_right hn, hg]
  change g.op.eval _ = true ↔ _
  simp only [hop, GateOp.eval, List.any_eq_true, List.mem_map, id_eq, prev_mem hg]
  constructor
  · rintro ⟨_, ⟨r, hr, rfl⟩, ht⟩
    by_cases h : r < w
    · exact ⟨r, ⟨hr, h⟩, by simpa [h] using ht⟩
    · simp [h] at ht
  · rintro ⟨r, ⟨hr, hlt⟩, ht⟩
    exact ⟨_, ⟨r, hr, rfl⟩, by simpa [hlt] using ht⟩

private lemma or_support {n w : ℕ} {C : Circuit} {g : Gate}
    (hg : gateAt n C w = some g) (hop : g.op = .or) (p : Fin n) :
    p ∈ support C w ↔ ∃ r ∈ prev n C w, p ∈ support C r := by
  simpa only [mem_support] using or_eval (fun v => decide (v = p)) hg hop

private def Clean {n} (G : SimpleGraph (Fin n)) (C : Circuit) : Prop :=
  ∀ (i : Fin C.gates.length) (x : Fin n → Bool), (C.gates.get i).op = .and →
    value C x (n + i) = true → ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true

private lemma clean_at {n w : ℕ} {G : SimpleGraph (Fin n)} {C : Circuit} {g : Gate}
    (hclean : Clean G C) (hg : gateAt n C w = some g) (hop : g.op = .and)
    {x : Fin n → Bool} (hx : value C x w = true) :
    ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
  unfold gateAt at hg
  split at hg
  · rename_i hn
    have hi : w - n < C.gates.length := by
      by_contra! h
      simp [List.getElem?_eq_none h] at hg
    let i : Fin C.gates.length := ⟨w - n, hi⟩
    have he : n + (i : ℕ) = w := by dsimp [i]; omega
    have hgi : C.gates.get i = g := by
      simpa [List.getElem?_eq_getElem hi, i] using hg
    exact hclean i x (hgi ▸ hop) (he ▸ hx)
  · simp at hg

private lemma and_support_empty {n w : ℕ} {G : SimpleGraph (Fin n)} {C : Circuit} {g : Gate}
    (hclean : Clean G C) (hg : gateAt n C w = some g) (hop : g.op = .and) :
    support (n := n) C w = ∅ := by
  ext p
  simp only [Finset.notMem_empty, iff_false, mem_support]
  intro hp
  obtain ⟨a,b,hab,ha,hb⟩ := clean_at hclean hg hop hp
  have ha' : a = p := of_decide_eq_true ha
  have hb' : b = p := of_decide_eq_true hb
  exact G.irrefl (ha' ▸ hb' ▸ hab)

private lemma pair_adjacency {n} {G : SimpleGraph (Fin n)} {a b : Fin n}
    (h : ∃ u v, G.Adj u v ∧ (u = a ∨ u = b) ∧ (v = a ∨ v = b)) : G.Adj a b := by
  obtain ⟨u,v,hu, rfl | rfl, rfl | rfl⟩ := h
  · exact False.elim (G.irrefl hu)
  · exact hu
  · exact hu.symm
  · exact False.elim (G.irrefl hu)

private def Legal (C : Circuit) : Prop :=
  ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2

private lemma value_mono {n} (C : Circuit) (x y : Fin n → Bool)
    (legal : Legal C) (hxy : ∀ p, x p = true → y p = true) (w : ℕ) :
    value C x w = true → value C y w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hw : w < n
    · change value C x (⟨w, hw⟩ : Fin n) = true → value C y (⟨w, hw⟩ : Fin n) = true
      simpa only [gateAt_rec C x w, gateAt_rec C y w, dite_eq_left hw] using hxy ⟨w, hw⟩
    cases hg : gateAt n C w with
    | none => simp [gateAt_rec C x w, hw, hg]
    | some g =>
      rcases (legal g (gateAt_mem hg)).1 with hop | hop
      · intro h
        apply (and_eval y hg hop).2
        intro r hr
        obtain ⟨hlt, hx⟩ := (and_eval x hg hop).1 h r hr
        exact ⟨hlt, ih r hlt hx⟩
      · rintro h
        obtain ⟨r, hr, hx⟩ := (or_eval x hg hop).1 h
        exact (or_eval y hg hop).2 ⟨r, hr, ih r ((prev_mem hg).1 hr).2 hx⟩

private def NoSquare {n} (G : SimpleGraph (Fin n)) : Prop :=
  ∀ a b c d, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)

private lemma small_side {n} {G : SimpleGraph (Fin n)} (hG : NoSquare G)
    {S T : Finset (Fin n)} (hST : ∀ a ∈ S, ∀ b ∈ T, G.Adj a b) :
    S.card ≤ 1 ∨ T.card ≤ 1 := by
  by_contra! h
  obtain ⟨a, ha, c, hc, hac⟩ := Finset.one_lt_card.mp h.1
  obtain ⟨b, hb, d, hd, hbd⟩ := Finset.one_lt_card.mp h.2
  exact hG a b c d hac hbd ⟨hST a ha b hb, (hST c hc b hb).symm,
    hST c hc d hd, (hST a ha d hd).symm⟩

/- The two nonempty singleton supports of a clean AND form a biclique. Its center
is taken from the side with one point. -/
private structure StarPlan {n} (G : SimpleGraph (Fin n)) (C : Circuit) (w : ℕ) where
  center : Fin n
  centerWire : ℕ
  leavesWire : ℕ
  centerEarlier : centerWire < w
  leavesEarlier : leavesWire < w
  supportCenter : support C centerWire = {center}
  adjacentLeaves : ∀ p ∈ support C leavesWire, G.Adj center p
  reads : ∃ g, gateAt n C w = some g ∧ g.op = .and ∧
    (g.inputs = [centerWire, leavesWire] ∨ g.inputs = [leavesWire, centerWire])

private noncomputable def plan {n} (G : SimpleGraph (Fin n)) (C : Circuit) (w : ℕ) :
    Option (StarPlan G C w) := by
  classical
  exact if h : Nonempty (StarPlan G C w) then some (Classical.choice h) else none

private lemma plan_of_binary {n w r s : ℕ} {G : SimpleGraph (Fin n)} {C : Circuit} {g : Gate}
    (hG : NoSquare G) (hclean : Clean G C) (hlegal : Legal C)
    (hg : gateAt n C w = some g) (hop : g.op = .and) (hargs : g.inputs = [r,s])
    (hr : r < w) (hs : s < w) (hR : (support (n := n) C r).Nonempty)
    (hS : (support (n := n) C s).Nonempty) : Nonempty (StarPlan G C w) := by
  have hcross a (ha : a ∈ support (n := n) C r) b (hb : b ∈ support (n := n) C s) :
      G.Adj a b := by
    let x : Fin n → Bool := fun v => decide (v = a ∨ v = b)
    have hra : value C x r = true := value_mono C _ _ hlegal
      (fun p hp => decide_eq_true (Or.inl (of_decide_eq_true hp))) r (mem_support.1 ha)
    have hsb : value C x s = true := value_mono C _ _ hlegal
      (fun p hp => decide_eq_true (Or.inr (of_decide_eq_true hp))) s (mem_support.1 hb)
    have hw : value C x w = true := (and_eval x hg hop).2 (by
      intro u hu
      simp [hargs] at hu
      rcases hu with rfl | rfl
      · exact ⟨hr,hra⟩
      · exact ⟨hs,hsb⟩)
    apply pair_adjacency
    obtain ⟨u,v,huv,hu,hv⟩ := clean_at hclean hg hop hw
    exact ⟨u,v,huv,of_decide_eq_true hu,of_decide_eq_true hv⟩
  rcases small_side hG hcross with hsmall | hsmall
  · obtain ⟨a,ha⟩ := hR
    have hEq : support C r = {a} := Finset.Subset.antisymm
      (fun p hp => Finset.mem_singleton.2 (Finset.card_le_one.1 hsmall p hp a ha))
      (by simpa using ha)
    exact ⟨⟨a,r,s,hr,hs,hEq,hcross a ha,g,hg,hop,Or.inl hargs⟩⟩
  · obtain ⟨b,hb⟩ := hS
    have hEq : support C s = {b} := Finset.Subset.antisymm
      (fun p hp => Finset.mem_singleton.2 (Finset.card_le_one.1 hsmall p hp b hb))
      (by simpa using hb)
    exact ⟨⟨b,s,r,hs,hr,hEq,fun p hp => (hcross p hp b hb).symm,g,hg,hop,Or.inr hargs⟩⟩

private inductive Role (n : ℕ)
  | empty
  | center
  | neighbor (c : Fin n)
deriving DecidableEq

private abbrev Request (n : ℕ) := ℕ × Role n
private abbrev Token (n : ℕ) := Fin n ⊕ Sym2 (Fin n)

private def raw {n} (C : Circuit) (q : Request n) : Finset (Token n) :=
  match q.2 with
  | .empty => ∅
  | .center => (support C q.1).image Sum.inl
  | .neighbor c => (support C q.1).image (fun p => Sum.inr (s(c,p)))

private def allowed {n} (G : SimpleGraph (Fin n)) (C : Circuit) (q : Request n) : Prop :=
  match q.2 with
  | .empty => True
  | .center => (support (n := n) C q.1).card ≤ 1
  | .neighbor c => ∀ p ∈ support (n := n) C q.1, G.Adj c p

private lemma raw_card {n} (C : Circuit) (q : Request n) :
    (raw C q).card ≤ (support (n := n) C q.1).card := by
  rcases q with ⟨w, _ | _ | c⟩
  · simp [raw]
  · exact Finset.card_image_le
  · exact Finset.card_image_le

private def StarPlan.arms {n w} {G : SimpleGraph (Fin n)} {C : Circuit}
    (P : StarPlan G C w) : Finset (Request n) :=
  {(P.centerWire, .center), (P.leavesWire, .neighbor P.center)}

private noncomputable def own {n} (G : SimpleGraph (Fin n)) (C : Circuit) (w : ℕ) :
    Finset (Token n) :=
  (plan G C w).elim ∅ (fun P => P.arms.biUnion (raw C))

private def inherited {n} (G : SimpleGraph (Fin n)) (C : Circuit) (w : ℕ) : Set (Token n) :=
  {tok | ∃ v, Relation.ReflTransGen (fun a b => b ∈ prev n C a) w v ∧ tok ∈ own G C v}

private noncomputable def children {n} (G : SimpleGraph (Fin n)) (C : Circuit) (q : Request n) :
    Finset (Request n) := by
  classical
  exact match plan G C q.1 with
  | some P => P.arms
  | none =>
    match gateAt n C q.1 with
    | none => ∅
    | some g => (prev n C q.1).image fun r => (r, if g.op = .or then q.2 else .empty)

private lemma prev_card {C : Circuit} {n w : ℕ} (legal : Legal C) : (prev n C w).card ≤ 2 := by
  cases hg : gateAt n C w with
  | none => simp [prev, hg]
  | some g =>
    simpa only [prev, hg] using
      (Finset.card_filter_le g.inputs.toFinset (· < w)).trans
        ((List.toFinset_card_le _).trans (legal g (gateAt_mem hg)).2)

private lemma raw_empty_of_support {n} {C : Circuit} (q : Request n)
    (h : support (n := n) C q.1 = ∅) : raw C q = ∅ := by
  rcases q with ⟨w, r⟩
  cases r <;> simp [raw, h]

private lemma or_raw {n} {C : Circuit} {w : ℕ} {g : Gate} {role : Role n}
    (hg : gateAt n C w = some g) (hop : g.op = .or) {a : Token n} (ha : a ∈ raw C (w,role)) :
    ∃ r ∈ prev n C w, a ∈ raw C (r,role) := by
  cases role with
  | empty => simp [raw] at ha
  | center =>
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨r,hr,hpr⟩ := (or_support hg hop p).1 hp
    exact ⟨r,hr,Finset.mem_image.mpr ⟨p,hpr,rfl⟩⟩
  | neighbor c =>
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨r,hr,hpr⟩ := (or_support hg hop p).1 hp
    exact ⟨r,hr,Finset.mem_image.mpr ⟨p,hpr,rfl⟩⟩

private lemma or_child_allowed {n} {C : Circuit} {G : SimpleGraph (Fin n)} {w r : ℕ} {g : Gate}
    {role : Role n} (hg : gateAt n C w = some g) (hop : g.op = .or)
    (hr : r ∈ prev n C w) (hok : allowed G C (w,role)) :
    allowed G C (r,role) := by
  have hsub : support (n := n) C r ⊆ support C w := fun p hp =>
    (or_support hg hop p).2 ⟨r,hr,hp⟩
  cases role with
  | empty => trivial
  | center => exact (Finset.card_le_card hsub).trans hok
  | neighbor c => exact fun p hp => hok p (hsub hp)

private lemma local_rule {n} {G : SimpleGraph (Fin n)} {C : Circuit}
    (legal : Legal C) (clean : Clean G C) (q : Request n) (hok : allowed G C q) (hn : n ≤ q.1) :
    (children G C q).card ≤ 2 ∧
    (∀ r ∈ children G C q, r.1 < q.1 ∧ allowed G C r) ∧
    (∀ w ∈ prev n C q.1, ∃ r ∈ children G C q, r.1 = w) ∧
    (∀ a, a ∈ raw C q ∨ a ∈ own G C q.1 → ∃ r ∈ children G C q, a ∈ raw C r) := by
  classical
  obtain ⟨w,role⟩ := q
  cases hP : plan G C w with
  | some P =>
    have hch : children G C (w,role) = P.arms := by simp [children, hP]
    have hown : own G C w = P.arms.biUnion (raw C) := by simp [own, hP]
    obtain ⟨g,hg,hop,hargs⟩ := P.reads
    have hrw : raw C (w,role) = ∅ := raw_empty_of_support _ (and_support_empty clean hg hop)
    rw [hch, hown, hrw]
    refine ⟨?_, ?_, ?_, ?_⟩
    · dsimp [StarPlan.arms]
      exact (Finset.card_insert_le _ _).trans (by simp)
    · intro r hr
      simp only [StarPlan.arms, Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl
      · exact ⟨P.centerEarlier, by simp [allowed, P.supportCenter]⟩
      · exact ⟨P.leavesEarlier, P.adjacentLeaves⟩
    · intro u hu
      have hu' := ((prev_mem hg).1 hu).1
      have hpair : u = P.centerWire ∨ u = P.leavesWire := by
        rcases hargs with h | h <;> simpa [h, or_comm] using hu'
      rcases hpair with rfl | rfl
      · exact ⟨(P.centerWire,.center), by simp [StarPlan.arms], rfl⟩
      · exact ⟨(P.leavesWire,.neighbor P.center), by simp [StarPlan.arms], rfl⟩
    · intro t ht
      simpa only [Finset.notMem_empty, false_or, Finset.mem_biUnion] using ht
  | none =>
    have hown : own G C w = ∅ := by simp [own, hP]
    cases hg : gateAt n C w with
    | none =>
      have hs : support (n := n) C w = ∅ := by
        ext p
        simp [mem_support, gateAt_rec C (fun v : Fin n => decide (v = p)) w, Nat.not_lt.mpr hn, hg]
      simp [children, hP, hg, prev, hown, raw_empty_of_support (w,role) hs]
    | some g =>
      rcases (legal g (gateAt_mem hg)).1 with hop | hop
      · have hne : g.op ≠ .or := by rw [hop]; intro h; cases h
        have hch : children G C (w,role) = (prev n C w).image (fun r => (r, .empty)) := by
          simp [children, hP, hg, hne]
        rw [hch, hown, raw_empty_of_support _ (and_support_empty clean hg hop)]
        refine ⟨Finset.card_image_le.trans (prev_card legal), ?_, ?_, by simp⟩
        · intro r hr
          obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hr
          exact ⟨((prev_mem hg).1 hu).2, trivial⟩
        · intro u hu
          exact ⟨(u,.empty),Finset.mem_image_of_mem _ hu,rfl⟩
      · have hch : children G C (w,role) = (prev n C w).image (fun r => (r,role)) := by
          simp [children, hP, hg, hop]
        rw [hch,hown]
        refine ⟨Finset.card_image_le.trans (prev_card legal), ?_, ?_, ?_⟩
        · intro r hr
          obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hr
          exact ⟨((prev_mem hg).1 hu).2, or_child_allowed hg hop hu hok⟩
        · intro u hu
          exact ⟨(u,role),Finset.mem_image_of_mem _ hu,rfl⟩
        · intro a ha
          simp only [Finset.notMem_empty, or_false] at ha
          obtain ⟨r,hr,har⟩ := or_raw hg hop ha
          exact ⟨(r,role),Finset.mem_image_of_mem _ hr,har⟩

private lemma inherited_through {n} {G : SimpleGraph (Fin n)} {C : Circuit} {w r : ℕ}
    {a : Token n} (hr : r ∈ prev n C w) (ha : a ∈ inherited G C r) :
    a ∈ inherited G C w := by
  obtain ⟨v,hv,hm⟩ := ha
  exact ⟨v, Relation.ReflTransGen.head hr hv, hm⟩

private lemma all_child_demands {n} {G : SimpleGraph (Fin n)} {C : Circuit}
    (legal : Legal C) (clean : Clean G C) (q : Request n) (hok : allowed G C q) (hn : n ≤ q.1)
    (a : Token n) (ha : a ∈ raw C q ∨ a ∈ inherited G C q.1) :
    ∃ r ∈ children G C q, a ∈ raw C r ∨ a ∈ inherited G C r.1 := by
  obtain ⟨_, _, hlink, hraw⟩ := local_rule legal clean q hok hn
  rcases ha with hr | hn
  · obtain ⟨r,hr,hm⟩ := hraw a (Or.inl hr)
    exact ⟨r,hr,Or.inl hm⟩
  · obtain ⟨v,hv,hown⟩ := hn
    rcases hv.cases_head with rfl | ⟨w,hw,hrest⟩
    · obtain ⟨r,hr,hm⟩ := hraw a (Or.inr hown)
      exact ⟨r,hr,Or.inl hm⟩
    · obtain ⟨r,hr,he⟩ := hlink w hw
      exact ⟨r,hr,Or.inr ⟨v,he ▸ hrest,hown⟩⟩

private lemma demand_input {n} (G : SimpleGraph (Fin n)) (C : Circuit) (q : Request n)
    (hq : q.1 < n) : (raw C q).card ≤ 1 ∧ inherited G C q.1 = ∅ := by
  let p : Fin n := ⟨q.1, hq⟩
  have hno : gateAt n C q.1 = none := by simp [gateAt, Nat.not_le_of_lt hq]
  have hp : ¬ Nonempty (StarPlan G C q.1) := by
    rintro ⟨P⟩
    obtain ⟨g,hg,_⟩ := P.reads
    simp [hno] at hg
  have hpc : (support (n := n) C q.1).card ≤ 1 := by
    change (support C p).card ≤ 1
    rw [support_input, Finset.card_singleton]
  refine ⟨(raw_card C q).trans hpc, ?_⟩
  ext a
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨v,hv,hm⟩
  rcases hv.cases_head with rfl | ⟨w,hw,_⟩
  · simp [own,plan,hp] at hm
  · simp [prev,hno] at hw

/- If the support has several points, C4-freeness permits only one neighboring
center. Otherwise extra requests are paid for by a single label apiece. -/
private lemma main_role {n} {G : SimpleGraph (Fin n)} {C : Circuit}
    (hG : NoSquare G) (w : ℕ) (F : Finset (Request n)) (hF : F.Nonempty)
    (hok : ∀ r ∈ F, r.1 = w ∧ allowed G C r) :
    ∃ p ∈ F, ∃ extra : Finset (Token n), extra.card + 1 ≤ F.card ∧
      ∀ q ∈ F, raw C q ⊆ extra ∪ raw C p := by
  classical
  by_cases hs : (support (n := n) C w).card ≤ 1
  · obtain ⟨p,hp⟩ := hF
    let extra := (F.erase p).biUnion (raw C)
    have hcount : extra.card ≤ (F.erase p).card := by
      simpa using Finset.card_biUnion_le_card_mul (F.erase p) (raw C) 1 (fun r hr =>
        (raw_card C r).trans (by simpa only [(hok r (Finset.mem_of_mem_erase hr)).1] using hs))
    refine ⟨p,hp,extra,by rw [← Finset.card_erase_add_one hp]; omega,?_⟩
    intro q hq a ha
    by_cases he : q = p
    · exact Finset.mem_union_right _ (he ▸ ha)
    · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨q, Finset.mem_erase.mpr ⟨he,hq⟩,ha⟩)
  · have huniq (q p : Request n) (hq : q ∈ F) (hp : p ∈ F)
        (hqe : q.2 ≠ .empty) (hpe : p.2 ≠ .empty) : q = p := by
      obtain ⟨hwq,hqok⟩ := hok q hq
      obtain ⟨hwp,hpok⟩ := hok p hp
      rcases q with ⟨x, _ | _ | c⟩
      · exact False.elim (hqe rfl)
      · exact False.elim (hs (hwq ▸ hqok))
      rcases p with ⟨y, _ | _ | d⟩
      · exact False.elim (hpe rfl)
      · exact False.elim (hs (hwp ▸ hpok))
      change x = w at hwq
      change y = w at hwp
      subst x
      subst y
      obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp (Nat.lt_of_not_ge hs)
      have he : c = d := by
        by_contra hne
        exact hG c a d b hne hab ⟨hqok a ha, (hpok a ha).symm, hpok b hb, (hqok b hb).symm⟩
      simp [he]
    by_cases he : ∃ p ∈ F, p.2 ≠ .empty
    · obtain ⟨p,hp,hpe⟩ := he
      refine ⟨p,hp,∅,by simpa using Finset.one_le_card.2 ⟨p,hp⟩,?_⟩
      intro q hq
      by_cases hqe : q.2 = .empty
      · rcases q with ⟨v,r⟩
        change r = .empty at hqe
        subst r
        simp [raw]
      · simp [huniq q p hq hp hqe hpe]
    · obtain ⟨p,hp⟩ := hF
      refine ⟨p,hp,∅,by simpa using Finset.one_le_card.2 ⟨p,hp⟩,?_⟩
      intro q hq
      have hqe : q.2 = .empty := by by_contra h; exact he ⟨q,hq,h⟩
      rcases q with ⟨v,r⟩
      change r = .empty at hqe
      subst r
      simp [raw]



private lemma pair_in_inherited {n} {G : SimpleGraph (Fin n)} {C : Circuit}
    (hG : NoSquare G) (legal : Legal C) (clean : Clean G C) (a b : Fin n)
    (w : ℕ) (ha : a ∉ support C w) (hb : b ∉ support C w)
    (hv : value C (fun v => decide (v = a ∨ v = b)) w = true) :
    Sum.inr (s(a,b)) ∈ inherited G C w ∧
      (Sum.inl a ∈ inherited G C w ∨ Sum.inl b ∈ inherited G C w) := by
  classical
  let x : Fin n → Bool := fun v => decide (v = a ∨ v = b)
  change value C x w = true at hv
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hw : w < n
    · let p : Fin n := ⟨w, hw⟩
      have h : x p = true := by simpa only [gateAt_rec C x w, dite_eq_left hw] using hv
      change decide (p = a ∨ p = b) = true at h
      have hp : p ∈ support C w := by
        change p ∈ support C p
        rw [support_input]
        exact Finset.mem_singleton_self _
      rcases of_decide_eq_true h with rfl | rfl
      · exact False.elim (ha hp)
      · exact False.elim (hb hp)
    cases hg : gateAt n C w with
    | none => simp [gateAt_rec C x w, hw, hg] at hv
    | some g =>
      have forward (r : ℕ) (hr : r ∈ prev n C w) (ha' : a ∉ support C r)
          (hb' : b ∉ support C r) (ht : value C x r = true) :=
        ih r ((prev_mem hg).1 hr).2 ha' hb' ht
      have transfer (r : ℕ) (hr : r ∈ prev n C w)
          (h : Sum.inr (s(a,b)) ∈ inherited G C r ∧
            (Sum.inl a ∈ inherited G C r ∨ Sum.inl b ∈ inherited G C r)) :
          Sum.inr (s(a,b)) ∈ inherited G C w ∧
            (Sum.inl a ∈ inherited G C w ∨ Sum.inl b ∈ inherited G C w) :=
        ⟨inherited_through hr h.1, h.2.imp (inherited_through hr) (inherited_through hr)⟩
      obtain ⟨hkind,hlen⟩ := legal g (gateAt_mem hg)
      rcases hkind with hop | hop
      · have hargs := (and_eval x hg hop).1 hv
        by_cases hex : ∃ r ∈ g.inputs, a ∉ support C r ∧ b ∉ support C r
        · obtain ⟨r,hr,ha',hb'⟩ := hex
          obtain ⟨hlt,hv'⟩ := hargs r hr
          have hprev := (prev_mem hg).2 ⟨hr,hlt⟩
          exact transfer r hprev (forward r hprev ha' hb' hv')
        have ht (r) (hr : r ∈ g.inputs) : a ∈ support C r ∨ b ∈ support C r := by
          by_contra! h
          exact hex ⟨r,hr,h⟩
        have hf (p : Fin n) (hp : ∀ r ∈ g.inputs, p ∈ support C r) : False := by
          let single : Fin n → Bool := fun v => decide (v = p)
          have hs : value C single w = true := (and_eval single hg hop).2 (fun r hr =>
            ⟨(hargs r hr).1, mem_support.1 (hp r hr)⟩)
          obtain ⟨u,v,huv,hu,hv⟩ := clean_at clean hg hop hs
          have hu' : u = p := of_decide_eq_true hu
          have hv' : v = p := of_decide_eq_true hv
          exact G.irrefl (hu' ▸ hv' ▸ huv)
        have hplan : Nonempty (StarPlan G C w) := by
          cases he : g.inputs with
          | nil =>
            exact False.elim (hf a (by simp [he]))
          | cons r rs =>
            have hr : r ∈ g.inputs := by simp [he]
            cases rs with
            | nil =>
              rcases ht r hr with ha' | hb'
              · exact False.elim (hf a (by simpa [he] using ha'))
              · exact False.elim (hf b (by simpa [he] using hb'))
            | cons s ss =>
              have hss : ss = [] := by
                have hh : (r :: s :: ss).length ≤ 2 := he ▸ hlen
                simp only [List.length_cons] at hh
                exact List.length_eq_zero_iff.mp (by omega)
              subst ss
              have hs : s ∈ g.inputs := by simp [he]
              have hne (r) (hr : r ∈ g.inputs) : (support (n := n) C r).Nonempty :=
                (ht r hr).elim (fun h => ⟨a,h⟩) (fun h => ⟨b,h⟩)
              exact plan_of_binary hG clean legal hg hop he (hargs r hr).1 (hargs s hs).1
                (hne r hr) (hne s hs)
        let P := Classical.choice hplan
        have hP : plan G C w = some P := by simp [plan,hplan,P]
        have hOwn : own G C w = P.arms.biUnion (raw C) := by simp [own,hP]
        have hmem : P.centerWire ∈ g.inputs ∧ P.leavesWire ∈ g.inputs := by
          obtain ⟨g',hg',_,hi⟩ := P.reads
          have he : g' = g := Option.some.inj (hg'.symm.trans hg)
          subst g'
          rcases hi with hh | hh <;> simp [hh]
        have hc : a = P.center ∨ b = P.center := by
          simpa [P.supportCenter] using ht P.centerWire hmem.1
        have hl := ht P.leavesWire hmem.2
        have hcenter : Sum.inl P.center ∈ inherited G C w := by
          refine ⟨w,.refl,?_⟩
          rw [hOwn]
          refine Finset.mem_biUnion.mpr ⟨(P.centerWire,.center),by simp [StarPlan.arms],?_⟩
          simp [raw, P.supportCenter]
        have hleaf (p : Fin n) (hp : p ∈ support C P.leavesWire) :
            Sum.inr (s(P.center,p)) ∈ inherited G C w := by
          refine ⟨w,.refl,?_⟩
          rw [hOwn]
          exact Finset.mem_biUnion.mpr ⟨(P.leavesWire,.neighbor P.center),by simp [StarPlan.arms],
            Finset.mem_image.mpr ⟨p,hp,rfl⟩⟩
        rcases hc with hac | hbc
        · have hbp : b ∈ support C P.leavesWire := hl.resolve_left (fun h =>
            G.irrefl (hac ▸ P.adjacentLeaves a h))
          exact ⟨by simpa [hac] using hleaf b hbp, Or.inl (by simpa [hac] using hcenter)⟩
        · have hap : a ∈ support C P.leavesWire := hl.resolve_right (fun h =>
            G.irrefl (hbc ▸ P.adjacentLeaves b h))
          exact ⟨by simpa [hbc, Sym2.eq_swap (a := P.center) (b := a)] using hleaf a hap,
            Or.inr (by simpa [hbc] using hcenter)⟩
      · obtain ⟨r,hr,ht⟩ := (or_eval x hg hop).1 hv
        exact transfer r hr (forward r hr
          (fun h => ha ((or_support hg hop a).2 ⟨r,hr,h⟩))
          (fun h => hb ((or_support hg hop b).2 ⟨r,hr,h⟩)) ht)

private theorem finish {n} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoSquare G) (C : Circuit) (legal : Legal C) (clean : Clean G C)
    (computed : ∀ x : Fin n → Bool, value C x C.output =
      decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) :
    ∃ T : Finset (Fin n), (∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) ∧
      G.edgeFinset.card + T.card ≤ C.size + 1 := by
  classical
  have output_true {a b : Fin n} (hab : G.Adj a b) :
      value C (fun v => decide (v = a ∨ v = b)) C.output = true := by
    rw [computed]
    exact decide_eq_true ⟨a,b,hab,by simp,by simp⟩
  by_cases hw : C.output < n + C.size
  · have hs (p : Fin n) : p ∉ support C C.output := by
      intro hp
      have ht := mem_support.1 hp
      rw [computed] at ht
      obtain ⟨u,v,huv,hu,hv⟩ := of_decide_eq_true ht
      have hu' : u = p := of_decide_eq_true hu
      have hv' : v = p := of_decide_eq_true hv
      exact G.irrefl (hu' ▸ hv' ▸ huv)
    let r : Request n := (C.output,.empty)
    obtain ⟨A,hA,hcollect⟩ := ReverseDemand.collect (allowed G C) (raw C) (inherited G C)
      (children G C) (fun q _ hq => demand_input G C q hq)
      (fun q hq hqn => ⟨(local_rule legal clean q hq hqn).1,(local_rule legal clean q hq hqn).2.1⟩)
      (all_child_demands legal clean) (main_role hG) C.size {r}
      (fun q hq => by have he := Finset.mem_singleton.mp hq; subst q; exact ⟨hw,trivial⟩)
    let T : Finset (Fin n) := Finset.univ.filter fun p => Sum.inl p ∈ A
    have hget (a : Token n) (ha : a ∈ inherited G C C.output) : a ∈ A :=
      hcollect r (Finset.mem_singleton_self _) a (Or.inr ha)
    have hsource (a b) (hab : G.Adj a b) :=
      pair_in_inherited hG legal clean a b C.output (hs a) (hs b) (output_true hab)
    refine ⟨T, ?_, ?_⟩
    · intro a b hab
      simpa [T] using (hsource a b hab).2.imp (hget _) (hget _)
    · let U := G.edgeFinset.image (Sum.inr : Sym2 (Fin n) → Token n)
      let V := T.image (Sum.inl : Fin n → Token n)
      have hU : U ⊆ A := by
        intro e he
        obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp he
        induction p using Sym2.inductionOn with
        | _ a b =>
          have hab : G.Adj a b := by simpa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hp
          exact hget _ (hsource a b hab).1
      have hV : V ⊆ A := by
        intro v hv
        obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hv
        simpa [T] using hp
      have hd : Disjoint U V := Finset.disjoint_left.mpr (by
        intro w hw hw'
        obtain ⟨e,_,rfl⟩ := Finset.mem_image.mp hw
        obtain ⟨v,_,hv⟩ := Finset.mem_image.mp hw'
        cases hv)
      have hbound := Finset.card_le_card (Finset.union_subset hU hV)
      rw [Finset.card_union_of_disjoint hd] at hbound
      change (G.edgeFinset.image _).card + (T.image _).card ≤ A.card at hbound
      rw [Finset.card_image_of_injective _ Sum.inr_injective,
        Finset.card_image_of_injective _ Sum.inl_injective] at hbound
      rw [Finset.card_singleton] at hA
      omega
  · have hno (a b : Fin n) (hab : G.Adj a b) : False := by
      have ht := output_true hab
      rw [missing_value C _ _ (Nat.le_of_not_gt hw)] at ht
      cases ht
    have hE : G.edgeFinset = ∅ := by
      ext e
      induction e using Sym2.inductionOn with
      | _ a b =>
        simp only [Finset.notMem_empty, iff_false, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
        exact hno a b
    exact ⟨∅, fun a b hab => False.elim (hno a b hab), by simp [hE]⟩

end PEqualNP.Outside.L_meta_1407


theorem PEqualNP.Outside.L_meta_1407 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out⟩ (List.ofFn x) = decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) → (∀ (i : Fin gates.length) (x : Fin n → Bool), (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn x)).getD (n + (i : ℕ)) false = true → ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) → ∃ T : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ T ∨ v ∈ T) ∧ G.edgeFinset.card + T.card ≤ gates.length + 1 := by
  intro n G _ hG gates out legal eval clean
  exact PEqualNP.Outside.L_meta_1407.finish G hG ⟨gates,out⟩ legal clean eval
