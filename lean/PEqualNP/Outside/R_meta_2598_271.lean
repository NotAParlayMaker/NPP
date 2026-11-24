import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 24000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_2598_271
    (cofactor : ¬ HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) 15)
    (eliminate : ∀ D : Circuit, FanInTwo D →
      (∃ y z : Fin 9 → Bool, D.eval (false :: (List.ofFn y ++ [true])) ≠
        D.eval (false :: (List.ofFn z ++ [true]))) →
      3 ≤ D.gates.countP (fun g => (if g.op.eval [false] = true then g.inputs.take 1 else g.inputs).any (fun i => i == 0 || i == 10)) →
      ∃ E : Circuit, FanInTwo E ∧ E.size + 3 ≤ D.size ∧
        ∀ y : Fin 9 → Bool, E.eval (List.ofFn y) = D.eval (false :: (List.ofFn y ++ [true])))
    (residual : ∀ D : Circuit, FanInTwo D → D.size ≤ 18 →
      D.gates.countP (fun g => (if g.op.eval [false] = true then g.inputs.take 1 else g.inputs).any (fun i => i == 0 || i == 10)) ≤ 2 →
      ∃ x : Fin 10 → Bool, D.eval (List.ofFn x ++ [!x 0]) ≠ (fun x : Fin 10 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)) x) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) → ∃ (x4 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x4 ++ [!x4 (0 : Fin (10 : ℕ))]) ≠ (fun (x5 : Fin (10 : ℕ) → Bool) => x5 (0 : Fin (10 : ℕ)) && x5 (1 : Fin (10 : ℕ)) || x5 (1 : Fin (10 : ℕ)) && x5 (2 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ)) && x5 (3 : Fin (10 : ℕ)) || x5 (3 : Fin (10 : ℕ)) && x5 (4 : Fin (10 : ℕ)) || x5 (4 : Fin (10 : ℕ)) && x5 (0 : Fin (10 : ℕ)) || x5 (0 : Fin (10 : ℕ)) && x5 (5 : Fin (10 : ℕ)) || x5 (1 : Fin (10 : ℕ)) && x5 (6 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ)) && x5 (7 : Fin (10 : ℕ)) || x5 (3 : Fin (10 : ℕ)) && x5 (8 : Fin (10 : ℕ)) || x5 (4 : Fin (10 : ℕ)) && x5 (9 : Fin (10 : ℕ)) || x5 (5 : Fin (10 : ℕ)) && x5 (7 : Fin (10 : ℕ)) || x5 (7 : Fin (10 : ℕ)) && x5 (9 : Fin (10 : ℕ)) || x5 (9 : Fin (10 : ℕ)) && x5 (6 : Fin (10 : ℕ)) || x5 (6 : Fin (10 : ℕ)) && x5 (8 : Fin (10 : ℕ)) || x5 (8 : Fin (10 : ℕ)) && x5 (5 : Fin (10 : ℕ))) x4 := by
  intro D hD hsz
  let F : (Fin 10 → Bool) → Bool := fun x => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)
  let G : (Fin 9 → Bool) → Bool := fun x => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
  by_contra hne
  have h : ∀ x : Fin 10 → Bool, D.eval (List.ofFn x ++ [!x 0]) = F x := by
    intro x
    by_contra hx
    exact hne ⟨x, hx⟩
  by_cases hr : D.gates.countP (fun g => (if g.op.eval [false] = true then g.inputs.take 1 else g.inputs).any (fun i => i == 0 || i == 10)) ≤ 2
  · obtain ⟨x, hx⟩ := residual D hD hsz hr
    exact hx (h x)
  · have restr : ∀ y : Fin 9 → Bool,
        D.eval (false :: (List.ofFn y ++ [true])) = F (Fin.cons false y) := by
      intro y
      have e := h (Fin.cons false y)
      rw [List.ofFn_succ] at e
      simpa using e
    obtain ⟨E, hE, hEs, hEv⟩ := eliminate D hD
      ⟨fun _ => false, fun _ => true, by rw [restr, restr]; decide⟩ (by omega)
    let p : Fin 9 → Fin 9 := ![4, 0, 1, 6, 7, 3, 5, 2, 8]
    have iso : ∀ y : Fin 9 → Bool, F (Fin.cons false (y ∘ p)) = G y := by decide +kernel
    let μ : ℕ → ℕ := fun i => if h : i < 9 then ((p ⟨i, h⟩ : Fin 9) : ℕ) else i
    let E' : Circuit := ⟨E.gates.map (fun t => ⟨t.op, t.inputs.map μ⟩), μ E.output⟩
    have μlt : ∀ i, i < 9 → μ i < 9 := by
      intro i hi
      simp only [μ, hi, ↓reduceDIte]
      exact (p ⟨i, hi⟩).isLt
    have μge : ∀ i, ¬ i < 9 → μ i = i := by
      intro i hi
      simp only [μ, hi, ↓reduceDIte]
    have app : ∀ (L L' : List Bool) (c : Bool), L.length = L'.length → 9 ≤ L.length →
        (∀ i, L.getD i false = L'.getD (μ i) false) →
        ∀ i, (L ++ [c]).getD i false = (L' ++ [c]).getD (μ i) false := by
      intro L L' c hlen h9 hrel i
      by_cases h1 : i < L.length
      · have h2 : μ i < L'.length := by
          by_cases hi : i < 9
          · have := μlt i hi
            omega
          · rw [μge i hi]
            omega
        rw [List.getD_append _ _ _ _ h1, List.getD_append _ _ _ _ h2]
        exact hrel i
      · have hμ : μ i = i := μge i (by omega)
        rw [hμ, List.getD_append_right _ _ _ _ (by omega),
          List.getD_append_right _ _ _ _ (by omega), hlen]
    have rel : ∀ (gs : List Gate) (L L' : List Bool), L.length = L'.length → 9 ≤ L.length →
        (∀ i, L.getD i false = L'.getD (μ i) false) →
        ∀ i, ((⟨gs, 0⟩ : Circuit).wires L).getD i false =
          ((⟨gs.map (fun t => ⟨t.op, t.inputs.map μ⟩), 0⟩ : Circuit).wires L').getD (μ i) false := by
      intro gs
      induction gs with
      | nil => intro L L' _ _ hrel i; exact hrel i
      | cons t ts ih =>
        intro L L' hlen h9 hrel
        have hval : t.op.eval (t.inputs.map fun i => L.getD i false) =
            t.op.eval ((t.inputs.map μ).map fun i => L'.getD i false) := by
          rw [List.map_map]
          congr 1
          apply List.map_congr_left
          intro i _
          exact hrel i
        have step := ih (L ++ [t.op.eval (t.inputs.map fun i => L.getD i false)])
          (L' ++ [t.op.eval ((t.inputs.map μ).map fun i => L'.getD i false)])
          (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
          (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
          (by rw [← hval]; exact app L L' _ hlen h9 hrel)
        exact step
    have base : ∀ (y : Fin 9 → Bool) (i : ℕ),
        (List.ofFn (y ∘ p)).getD i false = (List.ofFn y).getD (μ i) false := by
      intro y i
      by_cases hi : i < 9
      · rw [List.getD_eq_getElem _ _ (by simpa using hi),
          List.getD_eq_getElem _ _ (by simpa using μlt i hi)]
        simp only [List.getElem_ofFn, Function.comp_apply]
        congr 1
        apply Fin.ext
        simp only [μ, hi, ↓reduceDIte]
      · rw [μge i hi, List.getD_eq_default _ _ (by simpa using hi),
          List.getD_eq_default _ _ (by simpa using hi)]
    have hE' : FanInTwo E' := by
      intro t ht
      obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht
      obtain ⟨hop, hlen⟩ := hE t0 ht0
      exact ⟨hop, by simpa using hlen⟩
    have hsize : E'.size ≤ 15 := by
      change (E.gates.map _).length ≤ 15
      rw [List.length_map]
      change E.gates.length + 3 ≤ D.gates.length at hEs
      change D.gates.length ≤ 18 at hsz
      omega
    have hval : ∀ y : Fin 9 → Bool, E'.eval (List.ofFn y) = G y := by
      intro y
      have r := rel E.gates (List.ofFn (y ∘ p)) (List.ofFn y) (by simp) (by simp) (base y) E.output
      have e1 : E'.eval (List.ofFn y) = E.eval (List.ofFn (y ∘ p)) := r.symm
      rw [e1, hEv, restr, iso]
    exact cofactor ⟨E', hE', hsize, hval⟩
