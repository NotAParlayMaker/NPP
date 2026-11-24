import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.List.GetD
import Mathlib.Order.Interval.Finset.Nat
import PEqualNP.Defs

-- The cut construction and wire evaluation use the checked L-meta-925 and L-meta-270 arguments.


open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1460

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

private lemma gate_inputs {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (w : ℕ) (hn : n ≤ w) (hw : w < n + C.size) :
    ∃ P : Finset ℕ, P.card ≤ 2 ∧ (∀ r ∈ P, r < w) ∧
      ∀ (x y : Fin n → Bool), (∀ r ∈ P, value C x r = true → value C y r = true) →
        value C x w = true → value C y w = true := by
  let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
  obtain ⟨hop, hlen⟩ := hG g (List.getElem_mem _)
  let P := g.inputs.toFinset.filter (· < w)
  refine ⟨P, (Finset.card_filter_le _ _).trans ((List.toFinset_card_le g.inputs).trans hlen), ?_, ?_⟩
  · intro r hr
    exact (Finset.mem_filter.mp hr).2
  · intro x y hxy hx
    have hr (r : ℕ) (hm : r ∈ g.inputs) :
        (if r < w then value C x r else false) = true →
        (if r < w then value C y r else false) = true := by
      by_cases h : r < w
      · simpa [h] using hxy r (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hm, h⟩)
      · simp [h]
    rw [gate_value C x w hn hw] at hx
    rw [gate_value C y w hn hw]
    change g.op.eval _ = true at hx ⊢
    rcases hop with hop | hop
    · simp only [hop, GateOp.eval, List.all_eq_true, id_eq] at hx ⊢
      intro b hb
      obtain ⟨r, hm, rfl⟩ := List.mem_map.mp hb
      exact hr r hm (hx _ (List.mem_map.mpr ⟨r, hm, rfl⟩))
    · simp only [hop, GateOp.eval, List.any_eq_true, id_eq] at hx ⊢
      obtain ⟨b, hb, rfl⟩ := hx
      obtain ⟨r, hm, hv⟩ := List.mem_map.mp hb
      exact ⟨_, List.mem_map.mpr ⟨r, hm, rfl⟩, hr r hm hv⟩

private lemma value_mono {n : ℕ} (C : Circuit)
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

private def input {n : ℕ} (A : Finset (Fin n)) (p : Fin n) : Bool := decide (p ∈ A)

private def probes {n : ℕ} (C : Circuit) (S : Finset (Fin n))
    (R : Fin n → Finset (Fin n)) (w : ℕ) : Finset (Fin n) :=
  S.filter fun p => value C (input (R p)) w = true

private lemma mem_probes {n : ℕ} (C : Circuit) (S : Finset (Fin n))
    (R : Fin n → Finset (Fin n)) (w : ℕ) (p : Fin n) :
    p ∈ probes C S R w ↔ p ∈ S ∧ value C (input (R p)) w = true := by
  simp [probes]

private def outside {n : ℕ} (S : Finset (Fin n)) (p : Fin n) : Bool :=
  decide (p ∉ S)

private def charged {n : ℕ} (C : Circuit) (S : Finset (Fin n))
    (R : Fin n → Finset (Fin n)) (w : ℕ) : Prop :=
  ∃ j : Fin C.gates.length, w = n + j.val ∧
    (C.gates.get j).op = GateOp.or ∧ (C.gates.get j).inputs.length = 2 ∧
    value C (outside S) w = false ∧ 2 ≤ (probes C S R w).card ∧
    ∀ r ∈ (C.gates.get j).inputs, (probes C S R r).Nonempty

-- A gate rejecting the outside assignment can be replaced by earlier rejecting wires.
-- Only a binary OR with two productive reads can enlarge this frontier.
private lemma expand {n : ℕ} (C : Circuit) (S : Finset (Fin n)) (R : Fin n → Finset (Fin n))
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hR : ∀ p ∈ S, R p ∩ S = {p}) (w : ℕ)
    (hF : value C (outside S) w = false) (hLarge : 1 < (probes C S R w).card) :
    ∃ P : Finset ℕ, P.card ≤ 2 ∧ (1 < P.card → charged C S R w) ∧
      (∀ r ∈ P, r < w ∧ value C (outside S) r = false) ∧
      probes C S R w ⊆ P.biUnion (probes C S R) := by
  classical
  have hw₀ : n ≤ w := by
    by_contra! hn
    let p : Fin n := ⟨w, hn⟩
    have hp : p ∈ S := by
      change value C (outside S) p = false at hF
      simpa [input_value, outside] using hF
    have hsmall : probes C S R w ⊆ {p} := by
      intro s hs
      obtain ⟨hsS, hv⟩ := (mem_probes C S R w s).1 hs
      change value C (input (R s)) p = true at hv
      have hr : p ∈ R s := by simpa [input_value, input] using hv
      have he : p ∈ ({s} : Finset (Fin n)) := hR s hsS ▸ Finset.mem_inter.mpr ⟨hr, hp⟩
      simp [Finset.mem_singleton.mp he]
    have hb := Finset.card_le_card hsmall
    simp at hb
    omega
  have hw₁ : w < n + C.size := by
    by_contra! hn
    obtain ⟨p, hp⟩ := Finset.card_pos.mp (by omega : 0 < (probes C S R w).card)
    have hv := (mem_probes C S R w p).1 hp
    rw [missing_value C _ w hn] at hv
    simp_all
  let g := C.gates[w - n]'(by unfold Circuit.size at hw₁; omega)
  obtain ⟨hop, hlen⟩ := hG g (List.getElem_mem _)
  let read (x : Fin n → Bool) (r : ℕ) := if r < w then value C x r else false
  have hgate (x : Fin n → Bool) : value C x w = g.op.eval (g.inputs.map (read x)) :=
    gate_value C x w hw₀ hw₁
  have hAnd (h : g.op = GateOp.and) (x : Fin n → Bool) :
      value C x w = true ↔ ∀ r ∈ g.inputs, read x r = true := by
    rw [hgate, h, GateOp.eval, List.all_eq_true]
    simp
  have hOr (h : g.op = GateOp.or) (x : Fin n → Bool) :
      value C x w = true ↔ ∃ r ∈ g.inputs, read x r = true := by
    rw [hgate, h, GateOp.eval, List.any_eq_true]
    simp
  rcases hop with h | h
  · have hbad : ¬ ∀ r ∈ g.inputs, read (outside S) r = true := by
      rw [← hAnd h, hF]; decide
    push Not at hbad
    obtain ⟨r, hr, hrF⟩ := hbad
    obtain ⟨p, hp⟩ := Finset.card_pos.mp (by omega : 0 < (probes C S R w).card)
    have hread := (hAnd h _).1 ((mem_probes C S R w p).1 hp).2 r hr
    have hrlt : r < w := (by simpa [read] using hread : r < w ∧ value C (input (R p)) r = true).1
    refine ⟨{r}, by simp, by simp, ?_, ?_⟩
    · intro s hs
      have he : s = r := Finset.mem_singleton.mp hs
      subst s
      exact ⟨hrlt, by simpa [read, hrlt] using hrF⟩
    · intro p hp
      obtain ⟨hps, hpv⟩ := (mem_probes C S R w p).1 hp
      exact Finset.mem_biUnion.mpr ⟨r, by simp, (mem_probes C S R r p).2
        ⟨hps, by simpa [read, hrlt] using (hAnd h _).1 hpv r hr⟩⟩
  · let P := g.inputs.toFinset.filter fun r => r < w ∧ (probes C S R r).Nonempty
    have hcard : P.card ≤ g.inputs.toFinset.card := Finset.card_filter_le _ _
    have hcard' := List.toFinset_card_le g.inputs
    refine ⟨P, by omega, ?_, ?_, ?_⟩
    · intro hlarge
      have hj : w - n < C.gates.length := by unfold Circuit.size at hw₁; omega
      have hlen' : g.inputs.length = 2 := by omega
      have hP : P = g.inputs.toFinset :=
        Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by omega)
      refine ⟨⟨w - n, hj⟩, by simp; omega, h, hlen', hF, hLarge, ?_⟩
      intro r hr
      change r ∈ g.inputs at hr
      exact (Finset.mem_filter.mp (by rw [hP]; exact List.mem_toFinset.mpr hr : r ∈ P)).2.2
    · intro r hr
      obtain ⟨hri, hrlt, _⟩ := Finset.mem_filter.mp hr
      refine ⟨hrlt, ?_⟩
      have hn : read (outside S) r ≠ true := by
        intro ht
        have := (hOr h _).2 ⟨r, List.mem_toFinset.mp hri, ht⟩
        rw [hF] at this
        simp_all
      simpa [read, hrlt] using hn
    · intro p hp
      obtain ⟨hps, hpv⟩ := (mem_probes C S R w p).1 hp
      obtain ⟨r, hr, hrv⟩ := (hOr h _).1 hpv
      have hrlt : r < w := (by simpa [read] using hrv : r < w ∧ value C (input (R p)) r = true).1
      have hpr := (mem_probes C S R r p).2 ⟨hps, by simpa [read, hrlt] using hrv⟩
      exact Finset.mem_biUnion.mpr ⟨r, Finset.mem_filter.mpr
        ⟨List.mem_toFinset.mpr hr, hrlt, p, hpr⟩, hpr⟩


private lemma card_prefix (G : Finset ℕ) (t : ℕ) :
    (G.filter (· < t + 1)).card = (G.filter (· < t)).card + if t ∈ G then 1 else 0 := by
  classical
  by_cases ht : t ∈ G
  · have h : G.filter (· < t + 1) = insert t (G.filter (· < t)) := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨hw, hlt⟩
        by_cases he : w = t
        · exact Or.inl he
        · exact Or.inr ⟨hw, by omega⟩
      · rintro (rfl | ⟨hw, hlt⟩)
        · exact ⟨ht, by omega⟩
        · exact ⟨hw, by omega⟩
    rw [h, Finset.card_insert_of_notMem (by simp), ite_eq_left ht]
  · have h : G.filter (· < t + 1) = G.filter (· < t) := by
      ext w
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hw, hlt⟩
        have hne : w ≠ t := fun e => ht (e ▸ hw)
        exact ⟨hw, by omega⟩
      · rintro ⟨hw, hlt⟩
        exact ⟨hw, by omega⟩
    rw [h, ite_eq_right ht, Nat.add_zero]

-- Count each expanding wire at most once by processing the frontier in reverse order.
private lemma cut_card {α : Type*} [DecidableEq α]
    (P : ℕ → Finset α) (ok : ℕ → Prop) (G : Finset ℕ)
    (expandWire : ∀ w, ok w → 1 < (P w).card →
      ∃ B : Finset ℕ, B.card ≤ 2 ∧ (1 < B.card → w ∈ G) ∧
        (∀ r ∈ B, r < w ∧ ok r) ∧ P w ⊆ B.biUnion P)
    (t : ℕ) (F : Finset ℕ)
    (hF : ∀ w ∈ F, ok w ∧ (1 < (P w).card → w < t)) :
    (F.biUnion P).card ≤ F.card + (G.filter (· < t)).card := by
  classical
  induction t generalizing F with
  | zero =>
    apply (Finset.card_biUnion_le_card_mul F P 1 ?_).trans
    · simp
    · intro r hr
      have h := (hF r hr).2
      omega
  | succ t ih =>
    by_cases ht : t ∈ F ∧ 1 < (P t).card
    · obtain ⟨B, hBcard, hcharge, hB, hcover⟩ := expandWire t (hF t ht.1).1 ht.2
      let F' := F.erase t ∪ B
      have hF' : ∀ w ∈ F', ok w ∧ (1 < (P w).card → w < t) := by
        intro w hw
        rcases Finset.mem_union.mp hw with hw | hw
        · have ⟨hne, hmem⟩ := Finset.mem_erase.mp hw
          have ⟨hok, hlt⟩ := hF w hmem
          exact ⟨hok, fun h => by have := hlt h; omega⟩
        · exact ⟨(hB w hw).2, fun _ => (hB w hw).1⟩
      have hU : F.biUnion P ⊆ F'.biUnion P := by
        intro p hp
        obtain ⟨w, hw, hpw⟩ := Finset.mem_biUnion.mp hp
        by_cases h : w = t
        · subst w
          obtain ⟨r, hr, hpr⟩ := Finset.mem_biUnion.mp (hcover hpw)
          exact Finset.mem_biUnion.mpr ⟨r, Finset.mem_union_right _ hr, hpr⟩
        · exact Finset.mem_biUnion.mpr
            ⟨w, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨h, hw⟩), hpw⟩
      have hsize := Finset.card_union_le (F.erase t) B
      change F'.card ≤ _ at hsize
      have he := Finset.card_erase_add_one ht.1
      have hh := (Finset.card_le_card hU).trans (ih F' hF')
      rw [card_prefix]
      by_cases hg : t ∈ G
      · simp only [ite_eq_left hg]
        omega
      · simp only [ite_eq_right hg]
        have : B.card ≤ 1 := by by_contra! hl; exact hg (hcharge hl)
        omega
    · have hFt : ∀ w ∈ F, ok w ∧ (1 < (P w).card → w < t) := by
        intro w hw
        refine ⟨(hF w hw).1, fun h => ?_⟩
        have hne : w ≠ t := fun e => ht ⟨e ▸ hw, e ▸ h⟩
        have := (hF w hw).2 h
        omega
      have hh := ih F hFt
      rw [card_prefix]
      omega

private noncomputable def charges {n : ℕ} (C : Circuit) (S : Finset (Fin n))
    (R : Fin n → Finset (Fin n)) : Finset ℕ :=
  open Classical in
  (Finset.Ico n (n + C.size)).filter (charged C S R)

private lemma mem_charges {n : ℕ} (C : Circuit) (S : Finset (Fin n))
    (R : Fin n → Finset (Fin n)) (w : ℕ) :
    w ∈ charges C S R ↔ charged C S R w := by
  classical
  rw [charges, Finset.mem_filter, Finset.mem_Ico]
  refine ⟨And.right, fun h => ⟨?_, h⟩⟩
  obtain ⟨j, rfl, _⟩ := h
  have hj := j.isLt
  unfold Circuit.size
  omega

private lemma charge_card {n : ℕ} (C : Circuit) (S : Finset (Fin n))
    (R : Fin n → Finset (Fin n)) (w : ℕ)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hR : ∀ p ∈ S, R p ∩ S = {p})
    (hFalse : value C (outside S) w = false)
    (hTrue : ∀ p ∈ S, value C (input (R p)) w = true) :
    S.card ≤ 1 + (charges C S R).card := by
  classical
  let G := charges C S R
  have hstep (r : ℕ) (hf : value C (outside S) r = false) (hcard : 1 < (probes C S R r).card) :
      ∃ B : Finset ℕ, B.card ≤ 2 ∧ (1 < B.card → r ∈ G) ∧
        (∀ s ∈ B, s < r ∧ value C (outside S) s = false) ∧
        probes C S R r ⊆ B.biUnion (probes C S R) := by
    obtain ⟨B, hB, hcharge, hread, hcover⟩ := expand C S R hG hR r hf hcard
    exact ⟨B, hB, fun h => (mem_charges C S R r).2 (hcharge h), hread, hcover⟩
  have hh := cut_card (probes C S R) (fun r => value C (outside S) r = false) G
    hstep (w + 1) {w} (by
      intro r hr
      have he : r = w := Finset.mem_singleton.mp hr
      subst r
      exact ⟨hFalse, fun _ => by omega⟩)
  simp only [Finset.singleton_biUnion, Finset.card_singleton] at hh
  have hFull : probes C S R w = S := by
    ext p
    simp only [mem_probes]
    exact ⟨And.left, fun hp => ⟨hp, hTrue p hp⟩⟩
  rw [hFull] at hh
  have hbound := Finset.card_filter_le G (· < w + 1)
  change S.card ≤ 1 + G.card
  omega

private lemma cross_hit {n : ℕ} (C : Circuit)
    (S T : Finset (Fin n)) (R : Fin n → Finset (Fin n)) (w : ℕ)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hSize : (S ∩ T).card ≤ 1)
    (hCard : 2 ≤ (probes C S R w).card)
    (hFalse : value C (outside T) w = false) :
    ∃ p ∈ S \ T, (R p ∩ T).Nonempty := by
  classical
  have hex : ∃ p ∈ probes C S R w, p ∉ T := by
    by_contra! h
    have hsub : probes C S R w ⊆ S ∩ T := by
      intro p hp
      exact Finset.mem_inter.mpr ⟨((mem_probes C S R w p).1 hp).1, h p hp⟩
    have := Finset.card_le_card hsub
    omega
  obtain ⟨p, hp, hpt⟩ := hex
  obtain ⟨hps, hpw⟩ := (mem_probes C S R w p).1 hp
  refine ⟨p, Finset.mem_sdiff.mpr ⟨hps, hpt⟩, ?_⟩
  by_contra hn
  have hxy (v : Fin n) (hv : input (R p) v = true) : outside T v = true := by
    simp only [input, decide_eq_true_eq] at hv
    simp only [outside, decide_eq_true_eq]
    exact fun ht => hn ⟨v, Finset.mem_inter.mpr ⟨hv, ht⟩⟩
  have := value_mono C hG _ _ hxy w hpw
  rw [hFalse] at this
  contradiction

end PEqualNP.Outside.L_meta_1460

open PEqualNP.Outside.L_meta_1460 in
theorem PEqualNP.Outside.L_meta_1460 :
    ∀ (q n m : ℕ) (S : Fin m → Finset (Fin n))
    (R : Fin m → Fin n → Finset (Fin n)),
    1 ≤ q → (∀ i : Fin m, (S i).card = q + 1) →
    (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) →
    (∀ (i : Fin m) (p : Fin n), p ∈ S i → R i p ∩ S i = {p}) →
    (∀ i j : Fin m, i ≠ j → ¬ ((∃ p ∈ S i \ S j, (R i p ∩ S j).Nonempty) ∧
      (∃ s ∈ S j \ S i, (R j s ∩ S i).Nonempty))) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
      g.inputs.length ≤ 2) →
    (∀ w : Fin m, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn (fun v : Fin n => decide (v ∉ S w))) = false) →
    (∀ (w : Fin m) (p : Fin n), p ∈ S w →
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn (fun v : Fin n => decide (v ∈ R w p))) = true) →
    ∀ I : Finset (Fin gates.length), (∀ g : Fin gates.length, ((gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (gates.get g).inputs.length = 2 ∧
      (∃ i : Fin m, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (g : ℕ)⟩ (List.ofFn (fun v : Fin n => decide (v ∉ S i))) = false) ∧
      ∀ w ∈ (gates.get g).inputs, ∃ (i : Fin m) (p : Fin n), p ∈ S i ∧
        PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w⟩ (List.ofFn (fun v : Fin n => decide (v ∈ R i p))) = true) → g ∈ I) → m * q ≤ I.card := by
  classical
  intro q n m S R _ hSize hInter hR hNo gates out hG hFalse hTrue I hI
  let C : Circuit := ⟨gates, 0⟩
  let G (i : Fin m) := charges C (S i) (R i)
  have hcard (i : Fin m) : q ≤ (G i).card := by
    have h := charge_card C (S i) (R i) (out i) hG (hR i) (hFalse i) (hTrue i)
    change (S i).card ≤ 1 + (G i).card at h
    rw [hSize i] at h
    omega
  have hDis : (↑(Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint G := by
    intro i _ j _ hij
    change Disjoint (G i) (G j)
    rw [Finset.disjoint_left]
    intro w hi hj
    obtain ⟨_, _, _, _, hfi, hci, _⟩ := (mem_charges C (S i) (R i) w).1 hi
    obtain ⟨_, _, _, _, hfj, hcj, _⟩ := (mem_charges C (S j) (R j) w).1 hj
    exact hNo i j hij ⟨cross_hit C (S i) (S j) (R i) w hG (hInter i j hij) hci hfj,
      cross_hit C (S j) (S i) (R j) w hG (hInter j i hij.symm) hcj hfi⟩
  have hAll : Finset.univ.biUnion G ⊆ I.image (fun j : Fin gates.length => n + j.val) := by
    intro w hw
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hw
    obtain ⟨j, rfl, hop, hlen, hf, _, hp⟩ := (mem_charges C (S i) (R i) w).1 hi
    have hj : j ∈ I := hI j ⟨hop, hlen, ⟨i, hf⟩, fun r hr => by
      obtain ⟨p, hpr⟩ := hp r hr
      obtain ⟨hs, hv⟩ := (mem_probes C (S i) (R i) r p).1 hpr
      exact ⟨i, p, hs, hv⟩⟩
    exact Finset.mem_image_of_mem _ hj
  calc
    m * q = ∑ i : Fin m, q := by simp
    _ ≤ ∑ i : Fin m, (G i).card := Finset.sum_le_sum (fun i _ => hcard i)
    _ = (Finset.univ.biUnion G).card := (Finset.card_biUnion hDis).symm
    _ ≤ (I.image (fun j : Fin gates.length => n + j.val)).card := Finset.card_le_card hAll
    _ ≤ I.card := Finset.card_image_le
