import Mathlib
import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership

-- Repeatedly remove sparse endpoint and witness-gate classes. The discarded
-- edges cost at most d per label, and a binary circuit supplies at most 3s labels.
theorem PEqualNP.Outside.R_meta_5328_834
    (peel : ∀ (n d : Nat) (r : Sym2 (Fin n) → Nat ⊕ Nat → Bool)
      (labels : Finset (Nat ⊕ Nat)) (edges : Finset (Sym2 (Fin n))),
      ∃ t ⊆ edges, (∀ v ∈ labels, (t.filter (r · v)).card = 0 ∨ d < (t.filter (r · v)).card) ∧
      edges.card ≤ t.card + d * labels.card)
    (dense : ∃ d k : Nat, ∀ (n : Nat) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      (∀ (u : Fin n) (p : G.Walk u u), p.IsCycle → 5 ≤ p.length) →
      IsLeastAO G C → TopForm G C → ∀ t ⊆ Ustar G C, ∀ own : Sym2 (Fin n) → Nat,
      (∀ e ∈ t, (fun (e : Sym2 (Fin n)) (g : Nat) => g ∈ junk G C ∧ ∃ u v : Fin n,
        e = s(u,v) ∧ u ∈ wmax G C g ∧ gateVal n C g (pairInput u v) = true ∧
        gateVal n C g (pairInput u u) = false ∧ gateVal n C g (pairInput v v) = false) e (own e)) →
      (∀ v ∈ (C.gates.flatMap Gate.inputs).toFinset.disjSum (Finset.range C.size), let f := fun (e : Sym2 (Fin n)) (v : Nat ⊕ Nat) => v.elim (fun w => decide (w ∈ e.map Fin.val)) (fun g => decide (own e = g));
        (t.filter (f · v)).card = 0 ∨ d < (t.filter (f · v)).card) →
      t.card ≤ k * (C.size+1)) :
    ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x6 : Fin x2) (x7 : x3.Walk x6 x6), x7.IsCycle → (5 : ℕ) ≤ x7.length) → PEqualNP.TopForm.IsLeastAO x3 x5 → PEqualNP.TopForm.TopForm x3 x5 → {x9 ∈ PEqualNP.TopForm.Ustar x3 x5 | ∃ (x10 : Fin x2) (x11 : Fin x2), x9 = s(x10, x11) ∧ ∃ x12 ∈ PEqualNP.TopForm.junk x3 x5, x10 ∈ PEqualNP.TopForm.wmax x3 x5 x12 ∧ PEqualNP.EdgeOwnership.gateVal x2 x5 x12 (PEqualNP.EdgeOwnership.pairInput x10 x11) = Bool.true ∧ PEqualNP.EdgeOwnership.gateVal x2 x5 x12 (PEqualNP.EdgeOwnership.pairInput x10 x10) = Bool.false ∧ PEqualNP.EdgeOwnership.gateVal x2 x5 x12 (PEqualNP.EdgeOwnership.pairInput x11 x11) = Bool.false}.card ≤ x1 * (x5.size + (1 : ℕ)) := by
  classical
  obtain ⟨d,k,bound⟩ := dense
  refine ⟨k+3*d,?_⟩
  intro n G inst C girth least top
  let W := fun (e : Sym2 (Fin n)) (g : Nat) => g ∈ junk G C ∧ ∃ u v : Fin n,
        e = s(u,v) ∧ u ∈ wmax G C g ∧ gateVal n C g (pairInput u v) = true ∧
        gateVal n C g (pairInput u u) = false ∧ gateVal n C g (pairInput v v) = false
  let E := (Ustar G C).filter fun e => ∃ (u v : Fin n), e = s(u,v) ∧
    ∃ g ∈ junk G C, u ∈ wmax G C g ∧ gateVal n C g (pairInput u v) = true ∧
      gateVal n C g (pairInput u u) = false ∧ gateVal n C g (pairInput v v) = false
  change E.card ≤ _
  have owned (e) (he : e ∈ E) : ∃ g, W e g := by
    obtain ⟨u,v,eq,g,mem,h⟩ := (Finset.mem_filter.mp he).2
    exact ⟨g,mem,u,v,eq,h⟩
  let own := fun e => if h : e ∈ E then (owned e h).choose else 0
  have good (e) (he : e ∈ E) : W e (own e) := by
    simpa only [own,dif_pos he] using (owned e he).choose_spec
  let labels := (C.gates.flatMap Gate.inputs).toFinset.disjSum (Finset.range C.size)
  let r := fun (e : Sym2 (Fin n)) (v : Nat ⊕ Nat) => v.elim (fun w => decide (w ∈ e.map Fin.val)) (fun g => decide (own e = g))
  obtain ⟨t,sub,regular,price⟩ := peel n d r labels E
  have limited := bound n G C girth least top t (sub.trans (Finset.filter_subset _ _))
    own (fun e he => good e (sub he)) regular
  have arities (gs : List Gate) (h : ∀ g ∈ gs, g.inputs.length = 2) :
      (gs.flatMap Gate.inputs).length = 2 * gs.length := by
    induction gs with
    | nil => rfl
    | cons g gs ih =>
      have a := h g List.mem_cons_self
      have b := ih (fun z hz => h z (List.mem_cons_of_mem _ hz))
      simp only [List.flatMap_cons,List.length_append,List.length_cons,a,b]
      omega
  have wireBound := List.toFinset_card_le (C.gates.flatMap Gate.inputs)
  have eqLen := arities C.gates least.1.2.2
  have lab : labels.card ≤ 3*C.size := by
    simp only [labels,Finset.card_disjSum,Finset.card_range]
    change _ ≤ 3*C.gates.length
    change (C.gates.flatMap Gate.inputs).toFinset.card+C.gates.length ≤ _
    omega
  calc E.card ≤ t.card + d*labels.card := price
       _ ≤ k*(C.size+1) + d*(3*C.size) := Nat.add_le_add limited (Nat.mul_le_mul_left _ lab)
       _ ≤ (k+3*d)*(C.size+1) := by nlinarith
