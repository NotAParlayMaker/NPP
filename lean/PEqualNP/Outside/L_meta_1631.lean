import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1631_aux

open PEqualNP.CircuitLowerBounds

-- The wire evaluation lemmas are adapted from L-meta-1525 and L-meta-1457.
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

lemma gate_inputs {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (w : ℕ) (hn : n ≤ w) (hw : w < n + C.size) :
    ∃ P : Finset ℕ, P.card ≤ 2 ∧ (∀ r ∈ P, r < w) ∧
      ∀ (x y : Fin n → Bool), (∀ r ∈ P, value C x r = true → value C y r = true) →
        value C x w = true → value C y w = true := by
  let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
  obtain ⟨hop, hlen⟩ := hG g (List.getElem_mem _)
  let P := g.inputs.toFinset.filter (· < w)
  refine ⟨P, (Finset.card_filter_le _ _).trans ((List.toFinset_card_le g.inputs).trans hlen), ?_, ?_⟩
  · exact fun r hr => (Finset.mem_filter.mp hr).2
  · intro x y hxy hx
    have step (r) (hr : r ∈ g.inputs) :
        (if r < w then value C x r else false) = true →
        (if r < w then value C y r else false) = true := by
      by_cases h : r < w
      · simpa [h] using hxy r (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hr,h⟩)
      · simp [h]
    have form (z : Fin n → Bool) :
        value C z w = g.op.eval (g.inputs.map fun r => if r < w then value C z r else false) :=
      gate_value C z w hn hw
    rw [form x] at hx
    rw [form y]
    rcases hop with hop|hop
    · simp only [hop, GateOp.eval, List.all_eq_true, List.mem_map, id_eq] at hx ⊢
      intro b hb
      obtain ⟨r,hr,rfl⟩ := hb
      exact step r hr (hx _ ⟨r,hr,rfl⟩)
    · simp only [hop, GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at hx ⊢
      obtain ⟨b,⟨r,hr,rfl⟩,hv⟩ := hx
      exact ⟨_, ⟨r,hr,rfl⟩, step r hr hv⟩

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



end PEqualNP.Outside.L_meta_1631_aux

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_1631_aux in
theorem PEqualNP.Outside.L_meta_1631 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N),
    3 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    p0 ≠ p1 → p0 ∈ L i0 → p1 ∈ L i0 →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate),
    (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ gt.inputs.length ≤ 2) →
    (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length) →
    (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
    ∀ ev : ℕ → (Fin N → Bool) → Bool, (∀ (w : ℕ) (x : Fin N → Bool), ev w x = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w⟩ (List.ofFn x)) →
    ∀ o : Fin N → ℕ, ((∀ (t : Fin N) (x : Fin N → Bool), (x p0 = true ∨ x p1 = true ∨ ∀ u : Fin N, u ∉ L i0 → x u = true) →
      ev (o t) x = decide (∃ v ∈ L t, x v = true)) ↔
    ∀ t : Fin N, ev (o t) (fun v : Fin N => decide (v ∉ L t)) = false ∧ (p0 ∈ L t → ev (o t) (fun v : Fin N => decide (v = p0)) = true) ∧ (p1 ∈ L t → ev (o t) (fun v : Fin N => decide (v = p1)) = true) ∧
      (∀ p ∈ L t, ev (o t) (fun v : Fin N => decide (v = p0 ∨ v = p)) = true ∧ ev (o t) (fun v : Fin N => decide (v = p1 ∨ v = p)) = true) ∧ (t ≠ i0 → ev (o t) (fun v : Fin N => decide (v ∉ L i0)) = true) ∧
      (∀ w ∈ L t ∩ L i0, w ≠ p0 → w ≠ p1 → ev (o t) (fun v : Fin N => decide (v ∉ L i0 ∨ v = w)) = true)) := by
  classical
  intro q N L i0 p0 p1 hq hN hsize hcross hjoin h01 hp0 hp1 gates hb hne hprev ev hev o
  have mono (w : ℕ) (x y : Fin N → Bool) (hxy : ∀ v, x v = true → y v = true) :
      ev w x = true → ev w y = true := by
    rw [hev, hev]
    exact value_mono ⟨gates,w⟩ hb x y hxy w
  constructor
  · intro H t
    constructor
    · let x : Fin N → Bool := fun v => decide (v ∉ L t)
      change ev (o t) x = false
      have hfalse : ¬ ∃ v ∈ L t, x v = true := by
        rintro ⟨v, hv, hxv⟩
        simp [x, hv] at hxv
      by_cases ht : t = i0
      · subst t
        have hcond : (x p0 = true ∨ x p1 = true ∨
            ∀ u : Fin N, u ∉ L i0 → x u = true) := by
          right
          right
          intro u hu
          simp [x, hu]
        rw [H i0 x hcond]
        exact decide_eq_false hfalse
      · have hnot : ¬ (p0 ∈ L t ∧ p1 ∈ L t) := by
          intro hboth
          have hle : (L i0 ∩ L t).card ≤ 1 := by
            rw [hcross i0 t (Ne.symm ht)]
          have hp0' : p0 ∈ L i0 ∩ L t := Finset.mem_inter.mpr ⟨hp0, hboth.1⟩
          have hp1' : p1 ∈ L i0 ∩ L t := Finset.mem_inter.mpr ⟨hp1, hboth.2⟩
          have heq := (Finset.card_le_one.1 hle) p0 hp0' p1 hp1'
          exact h01 heq
        have hcond : (x p0 = true ∨ x p1 = true ∨
            ∀ u : Fin N, u ∉ L i0 → x u = true) := by
          by_cases hp0t : p0 ∈ L t
          · right
            left
            have hp1t : p1 ∉ L t := by
              intro hp1t
              exact hnot ⟨hp0t, hp1t⟩
            simp [x, hp1t]
          · left
            simp [x, hp0t]
        rw [H t x hcond]
        exact decide_eq_false hfalse
    · constructor
      · intro hp0t
        let x : Fin N → Bool := fun v => decide (v = p0)
        change ev (o t) x = true
        have hcond : (x p0 = true ∨ x p1 = true ∨
            ∀ u : Fin N, u ∉ L i0 → x u = true) := by
          left
          simp [x]
        rw [H t x hcond]
        exact decide_eq_true ⟨p0, hp0t, by simp [x]⟩
      · constructor
        · intro hp1t
          let x : Fin N → Bool := fun v => decide (v = p1)
          change ev (o t) x = true
          have hcond : (x p0 = true ∨ x p1 = true ∨
              ∀ u : Fin N, u ∉ L i0 → x u = true) := by
            right
            left
            simp [x]
          rw [H t x hcond]
          exact decide_eq_true ⟨p1, hp1t, by simp [x]⟩
        · constructor
          · intro p hp
            constructor
            · let x : Fin N → Bool := fun v => decide (v = p0 ∨ v = p)
              change ev (o t) x = true
              have hcond : (x p0 = true ∨ x p1 = true ∨
                  ∀ u : Fin N, u ∉ L i0 → x u = true) := by
                left
                simp [x]
              rw [H t x hcond]
              exact decide_eq_true ⟨p, hp, by simp [x]⟩
            · let x : Fin N → Bool := fun v => decide (v = p1 ∨ v = p)
              change ev (o t) x = true
              have hcond : (x p0 = true ∨ x p1 = true ∨
                  ∀ u : Fin N, u ∉ L i0 → x u = true) := by
                right
                left
                simp [x]
              rw [H t x hcond]
              exact decide_eq_true ⟨p, hp, by simp [x]⟩
          · constructor
            · intro hti
              let x : Fin N → Bool := fun v => decide (v ∉ L i0)
              change ev (o t) x = true
              have houtside : ∃ v ∈ L t, v ∉ L i0 := by
                by_contra hno
                have hsub : L t ⊆ L i0 := by
                  intro v hv
                  by_contra hvnot
                  exact hno ⟨v, hv, hvnot⟩
                have hle : (L t).card ≤ (L i0 ∩ L t).card :=
                  Finset.card_le_card (by
                    intro v hv
                    exact Finset.mem_inter.mpr ⟨hsub hv, hv⟩)
                rw [hcross i0 t (Ne.symm hti)] at hle
                rw [hsize t] at hle
                omega
              have hcond : (x p0 = true ∨ x p1 = true ∨
                  ∀ u : Fin N, u ∉ L i0 → x u = true) := by
                right
                right
                intro u hu
                simp [x, hu]
              rw [H t x hcond]
              obtain ⟨v, hv, hvnot⟩ := houtside
              exact decide_eq_true ⟨v, hv, by simp [x, hvnot]⟩
            · intro w hw hwp0 hwp1
              let x : Fin N → Bool := fun v => decide (v ∉ L i0 ∨ v = w)
              change ev (o t) x = true
              have hcond : (x p0 = true ∨ x p1 = true ∨
                  ∀ u : Fin N, u ∉ L i0 → x u = true) := by
                right
                right
                intro u hu
                simp [x, hu]
              rw [H t x hcond]
              have hw' : w ∈ L t := (Finset.mem_inter.mp hw).1
              exact decide_eq_true ⟨w, hw', by simp [x]⟩
  · intro H t x hx
    by_cases hline : ∃ v ∈ L t, x v = true
    · have hval : ev (o t) x = true := by
        rcases H t with ⟨hcomp, hp0test, hp1test, hpairs, hco, hinter⟩
        by_cases hx0 : x p0 = true
        · obtain ⟨v, hv, hxv⟩ := hline
          have hpair := (hpairs v hv).1
          have hsub : ∀ u : Fin N,
              (fun z : Fin N => decide (z = p0 ∨ z = v)) u = true → x u = true := by
            intro u hu
            have hu' : u = p0 ∨ u = v := of_decide_eq_true hu
            rcases hu' with hu' | hu'
            · simpa [hu'] using hx0
            · simpa [hu'] using hxv
          exact mono (o t) (fun u : Fin N => decide (u = p0 ∨ u = v)) x hsub hpair
        · by_cases hx1 : x p1 = true
          · obtain ⟨v, hv, hxv⟩ := hline
            have hpair := (hpairs v hv).2
            have hsub : ∀ u : Fin N,
                (fun z : Fin N => decide (z = p1 ∨ z = v)) u = true → x u = true := by
              intro u hu
              have hu' : u = p1 ∨ u = v := of_decide_eq_true hu
              rcases hu' with hu' | hu'
              · simpa [hu'] using hx1
              · simpa [hu'] using hxv
            exact mono (o t) (fun u : Fin N => decide (u = p1 ∨ u = v)) x hsub hpair
          · have hout : ∀ u : Fin N, u ∉ L i0 → x u = true := by
              rcases hx with h0 | h1 | hout
              · exact False.elim (hx0 h0)
              · exact False.elim (hx1 h1)
              · exact hout
            by_cases hti : t = i0
            · subst t
              obtain ⟨v, hv, hxv⟩ := hline
              have hvboth : v ∈ L i0 ∩ L i0 := Finset.mem_inter.mpr ⟨hv, hv⟩
              have hv0 : v ≠ p0 := by
                intro heq
                subst v
                exact hx0 hxv
              have hv1 : v ≠ p1 := by
                intro heq
                subst v
                exact hx1 hxv
              have htest := hinter v hvboth hv0 hv1
              have hsub : ∀ u : Fin N,
                  (fun z : Fin N => decide (z ∉ L i0 ∨ z = v)) u = true → x u = true := by
                intro u hu
                have hu' : u ∉ L i0 ∨ u = v := of_decide_eq_true hu
                rcases hu' with hu' | hu'
                · exact hout u hu'
                · simpa [hu'] using hxv
              exact mono (o i0) (fun u : Fin N => decide (u ∉ L i0 ∨ u = v)) x hsub htest
            · have hsub : ∀ u : Fin N,
                (fun z : Fin N => decide (z ∉ L i0)) u = true → x u = true := by
                intro u hu
                exact hout u (of_decide_eq_true hu)
              exact mono (o t) (fun u : Fin N => decide (u ∉ L i0)) x hsub (hco hti)
      have htarget : decide (∃ v ∈ L t, x v = true) = true := by simp [hline]
      rw [htarget]
      exact hval
    · rcases H t with ⟨hcomp, hp0test, hp1test, hpairs, hco, hinter⟩
      have hnot : ev (o t) x ≠ true := by
        intro htrue
        have hsub : ∀ u : Fin N, x u = true →
            (fun z : Fin N => decide (z ∉ L t)) u = true := by
          intro u hu
          have hu' : u ∉ L t := by
            intro hv
            exact hline ⟨u, hv, hu⟩
          exact decide_eq_true hu'
        have hupper := mono (o t) x (fun z : Fin N => decide (z ∉ L t)) hsub htrue
        exact Bool.noConfusion (hcomp.symm.trans hupper)
      have hfalse : ev (o t) x = false := by
        cases heval : ev (o t) x with
        | false => rfl
        | true => exact (hnot heval).elim
      have htarget : decide (∃ v ∈ L t, x v = true) = false := by simp [hline]
      rw [htarget]
      exact hfalse
