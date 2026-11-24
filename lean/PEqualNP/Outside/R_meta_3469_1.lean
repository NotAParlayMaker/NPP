import Mathlib.Data.List.GetD
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.GenericRejection PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_3469_1
    (factor : ∀ (n : ℕ) (C : Circuit), IsAO2 (n + n) C →
      n + n ≤ C.output → C.output < n + n + C.size →
      (∃ g : Gate, C.gates[C.output - (n + n)]? = some g ∧ g.op = GateOp.and) →
      ∃ w : Bool → ℕ, (∀ b, w b < C.output) ∧
        ∀ X Y : Finset (Fin n), C.eval (incidenceInput X Y) =
          ((Circuit.mk C.gates (w false)).eval (incidenceInput X Y) &&
           (Circuit.mk C.gates (w true)).eval (incidenceInput X Y)))
    (slices : ∀ (q n : ℕ) (S : Fin n → Finset (Fin n)) (C : Circuit) (w : Bool → ℕ),
      200 ≤ q → n = q ^ 2 + q + 1 → (∀ l, (S l).card = q + 1) →
      (∀ p r, p ≠ r → ∃! l, p ∈ S l ∧ r ∈ S l) → IsAO2 (n + n) C →
      C.output < n + n + C.size → (∀ b, w b < C.output) →
      (∀ b, RightOnIncidentPairs S (Circuit.mk C.gates (w b))) →
      (∀ Y : Finset (Fin n), Y.card ≤ q → ∃ b : Bool, ∀ X : Finset (Fin n),
        (Circuit.mk C.gates (w b)).eval (incidenceInput X Y) = incidenceFun S X Y) →
      n * q ≤ 100 * C.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (200 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) → PEqualNP.TopForm.IsAO2 (x2 + x2) x4 → x2 + x2 ≤ x4.output → x4.output < x2 + x2 + x4.size → (∃ (x12 : PEqualNP.CircuitLowerBounds.Gate), x4.gates[x4.output - (x2 + x2)]? = Option.some x12 ∧ x12.op = PEqualNP.CircuitLowerBounds.GateOp.and) → PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 → (∀ (x14 x15 : Finset (Fin x2)), x15.card ≤ x1 → PEqualNP.GenericRejection.IsFalseInput x3 x14 x15 → x4.eval (PEqualNP.GenericRejection.incidenceInput x14 x15) = Bool.false) → x2 * x1 ≤ (100 : ℕ) * x4.size := by
  intro q n S C hq hn hcard hplane hao hstart hend hand hpairs hreject
  have mono (w : ℕ) (X X' Y Y' : Finset (Fin n)) (hX : X ⊆ X') (hY : Y ⊆ Y') :
      (Circuit.mk C.gates w).eval (incidenceInput X Y) = true →
      (Circuit.mk C.gates w).eval (incidenceInput X' Y') = true := by
    let extendsBits (u v : List Bool) := ∀ i, u.getD i false = true → v.getD i false = true
    have liftGates (gs : List Gate)
        (hops : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) (u v : List Bool)
        (hlen : u.length = v.length) (huv : extendsBits u v) :
        extendsBits ((Circuit.mk gs w).wires u) ((Circuit.mk gs w).wires v) := by
      induction gs generalizing u v with
      | nil => exact huv
      | cons g gs ih =>
        let val (t : List Bool) := g.op.eval (g.inputs.map fun j => t.getD j false)
        have hgate : val u = true → val v = true := by
          rcases hops g List.mem_cons_self with h | h
          · simp only [val, h, GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
            intro hall j hj
            exact huv j (hall j hj)
          · simp only [val, h, GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
            rintro ⟨j, hj, ht⟩
            exact ⟨j, hj, huv j ht⟩
        apply ih (fun g' hg' => hops g' (List.mem_cons_of_mem _ hg'))
          (u ++ [val u]) (v ++ [val v]) (by simp [hlen])
        intro i hi
        by_cases hlt : i < u.length
        · rw [List.getD_append _ _ _ _ hlt] at hi
          rw [List.getD_append _ _ _ _ (by omega)]
          exact huv i hi
        · by_cases heq : i = u.length
          · subst i
            simpa [hlen] using hgate (by simpa using hi)
          · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
            contradiction
    apply liftGates C.gates hao.1 _ _ (by simp [incidenceInput])
    intro i hi
    by_cases hlt : i < n
    · have hu : i < (List.ofFn (fun p : Fin n => decide (p ∈ X))).length := by simpa using hlt
      have hv : i < (List.ofFn (fun p : Fin n => decide (p ∈ X'))).length := by simpa using hlt
      simp only [incidenceInput, List.getD_append _ _ _ _ hu, List.getD_eq_getElem _ _ hu,
        List.getElem_ofFn, decide_eq_true_eq] at hi
      simp only [incidenceInput, List.getD_append _ _ _ _ hv, List.getD_eq_getElem _ _ hv,
        List.getElem_ofFn, decide_eq_true_eq]
      exact hX hi
    · have transfer (A B : Finset (Fin n)) : (incidenceInput A B).getD i false =
          (List.ofFn (fun l : Fin n => decide (l ∈ B))).getD (i - n) false := by
        simp only [incidenceInput, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by simp; omega)]
        simp
      rw [transfer] at hi ⊢
      by_cases hj : i - n < n
      · have hu : i - n < (List.ofFn (fun l : Fin n => decide (l ∈ Y))).length := by simpa using hj
        have hv : i - n < (List.ofFn (fun l : Fin n => decide (l ∈ Y'))).length := by simpa using hj
        simp only [List.getD_eq_getElem _ _ hu, List.getElem_ofFn, decide_eq_true_eq] at hi
        simp only [List.getD_eq_getElem _ _ hv, List.getElem_ofFn, decide_eq_true_eq]
        exact hY hi
      · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt hj)] at hi
        contradiction
  obtain ⟨w, hbefore, hfactor⟩ := factor n C hao hstart hend hand
  have hp : ∀ b, RightOnIncidentPairs S (Circuit.mk C.gates (w b)) := by
    intro b l p hpl
    have ht := hpairs l p hpl
    rw [hfactor, Bool.and_eq_true] at ht
    cases b
    · exact ht.1
    · exact ht.2
  apply slices q n S C w hq hn hcard hplane hao hend hbefore hp
  intro Y hY
  let Z := zeroSet S Y
  have hZ : IsFalseInput S Z Y := by
    intro l hl
    apply Finset.disjoint_left.mpr
    intro p hpl hpZ
    exact (Finset.mem_filter.mp hpZ).2 l hl hpl
  have hzero := hreject Z Y hY hZ
  rw [hfactor] at hzero
  obtain ⟨b, hb⟩ : ∃ b, (Circuit.mk C.gates (w b)).eval (incidenceInput Z Y) = false := by
    cases hv : (Circuit.mk C.gates (w false)).eval (incidenceInput Z Y) with
    | false => exact ⟨false, hv⟩
    | true => exact ⟨true, by simpa [hv] using hzero⟩
  refine ⟨b, ?_⟩
  intro X
  by_cases hex : ∃ p ∈ X, ∃ l ∈ Y, p ∈ S l
  · obtain ⟨p, hpX, l, hlY, hpl⟩ := hex
    have hit := mono (w b) {p} X {l} Y
      (Finset.singleton_subset_iff.mpr hpX) (Finset.singleton_subset_iff.mpr hlY) (hp b l p hpl)
    have witness : ∃ p ∈ X, ∃ l ∈ Y, p ∈ S l := ⟨p, hpX, l, hlY, hpl⟩
    simp [hit, incidenceFun, witness]
  · have hsub : X ⊆ Z := by
      intro p hpX
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun l hl hpl => hex ⟨p, hpX, l, hl, hpl⟩⟩
    cases hx : (Circuit.mk C.gates (w b)).eval (incidenceInput X Y) with
    | false => simp [incidenceFun, hex]
    | true =>
      have ht := mono (w b) X Z Y Y hsub (by rfl) hx
      simp [hb] at ht
