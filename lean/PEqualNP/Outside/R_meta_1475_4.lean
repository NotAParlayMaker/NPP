import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Split the negative tests into small sides and the exceptional six-point configurations.
-- Checking a candidate on the indicated inputs suffices by monotonicity.
set_option maxHeartbeats 3000000 in
set_option maxRecDepth 12000 in
theorem PEqualNP.Outside.R_meta_1475_4 :
    (let D : Finset (Fin 21) := {0, 5, 7, 17, 20}
     ∀ P L : Finset (Fin 21), 6 ≤ P.card → 6 ≤ L.card →
      (∀ p ∈ P, ∀ l ∈ L, l - p ∉ D) →
      P.card = 6 ∧ (∀ l : Fin 21, let d :=
        ∑ p ∈ P, if l - p ∈ D then (1 : ℕ) else 0;
        d = 0 ∨ d = 2)) →
    (let D : Finset (Fin 21) := {0, 5, 7, 17, 20}
     let Left : Finset (Fin 21) → Fin 42 → Bool := fun S =>
       Fin.append (m := 21) (n := 21) (fun i => decide (i ∈ S)) (fun j => decide (∀ i ∈ S, j - i ∉ D))
     let Right : Finset (Fin 21) → Fin 42 → Bool := fun S =>
       Fin.append (m := 21) (n := 21) (fun i => decide (∀ j ∈ S, j - i ∉ D)) (fun j => decide (j ∈ S))
     ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 124 ∧
      (∀ p l : Fin 21, l - p ∈ D →
        C.eval (List.ofFn (Fin.append (fun i => decide (i = p)) (fun j => decide (j = l)))) = true) ∧
      (∀ S : Finset (Fin 21), S.card ≤ 5 →
          C.eval (List.ofFn (Left S)) = false ∧ C.eval (List.ofFn (Right S)) = false) ∧
      ∀ S : Finset (Fin 21), S.card = 6 →
        (∀ j : Fin 21, let d := ∑ i ∈ S, if j - i ∈ D then (1 : ℕ) else 0; d = 0 ∨ d = 2) →
        C.eval (List.ofFn (Left S)) = false) →
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 124 ∧ (∀ x : Fin 42 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 42, (u.val, v.val) ∈ ([(0, 21), (0, 26), (0, 28), (0, 38), (0, 41), (1, 21), (1, 22), (1, 27), (1, 29), (1, 39), (2, 22), (2, 23), (2, 28), (2, 30), (2, 40), (3, 23), (3, 24), (3, 29), (3, 31), (3, 41), (4, 21), (4, 24), (4, 25), (4, 30), (4, 32), (5, 22), (5, 25), (5, 26), (5, 31), (5, 33), (6, 23), (6, 26), (6, 27), (6, 32), (6, 34), (7, 24), (7, 27), (7, 28), (7, 33), (7, 35), (8, 25), (8, 28), (8, 29), (8, 34), (8, 36), (9, 26), (9, 29), (9, 30), (9, 35), (9, 37), (10, 27), (10, 30), (10, 31), (10, 36), (10, 38), (11, 28), (11, 31), (11, 32), (11, 37), (11, 39), (12, 29), (12, 32), (12, 33), (12, 38), (12, 40), (13, 30), (13, 33), (13, 34), (13, 39), (13, 41), (14, 21), (14, 31), (14, 34), (14, 35), (14, 40), (15, 22), (15, 32), (15, 35), (15, 36), (15, 41), (16, 21), (16, 23), (16, 33), (16, 36), (16, 37), (17, 22), (17, 24), (17, 34), (17, 37), (17, 38), (18, 23), (18, 25), (18, 35), (18, 38), (18, 39), (19, 24), (19, 26), (19, 36), (19, 39), (19, 40), (20, 25), (20, 27), (20, 37), (20, 40), (20, 41)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) := by
  intro geometry tested
  obtain ⟨C, hC, hsize, hy, hn, hexc⟩ := tested
  refine ⟨C, hC, hsize, ?_⟩
  let D : Finset (Fin 21) := {0, 5, 7, 17, 20}
  let E := ([(0, 21), (0, 26), (0, 28), (0, 38), (0, 41), (1, 21), (1, 22), (1, 27), (1, 29), (1, 39), (2, 22), (2, 23), (2, 28), (2, 30), (2, 40), (3, 23), (3, 24), (3, 29), (3, 31), (3, 41), (4, 21), (4, 24), (4, 25), (4, 30), (4, 32), (5, 22), (5, 25), (5, 26), (5, 31), (5, 33), (6, 23), (6, 26), (6, 27), (6, 32), (6, 34), (7, 24), (7, 27), (7, 28), (7, 33), (7, 35), (8, 25), (8, 28), (8, 29), (8, 34), (8, 36), (9, 26), (9, 29), (9, 30), (9, 35), (9, 37), (10, 27), (10, 30), (10, 31), (10, 36), (10, 38), (11, 28), (11, 31), (11, 32), (11, 37), (11, 39), (12, 29), (12, 32), (12, 33), (12, 38), (12, 40), (13, 30), (13, 33), (13, 34), (13, 39), (13, 41), (14, 21), (14, 31), (14, 34), (14, 35), (14, 40), (15, 22), (15, 32), (15, 35), (15, 36), (15, 41), (16, 21), (16, 23), (16, 33), (16, 36), (16, 37), (17, 22), (17, 24), (17, 34), (17, 37), (17, 38), (18, 23), (18, 25), (18, 35), (18, 38), (18, 39), (19, 24), (19, 26), (19, 36), (19, 39), (19, 40), (20, 25), (20, 27), (20, 37), (20, 40), (20, 41)] : List (ℕ × ℕ))
  let row (p : Fin 21) : List (ℕ × ℕ) :=
    ((List.finRange 21).filter (fun l => decide (l - p ∈ D))).map
      (fun l => (p.val, 21 + l.val))
  have table : E = (List.finRange 21).flatMap row := by decide +kernel
  have leftRight : ∀ e ∈ E, e.1 < 21 ∧ 21 ≤ e.2 := by
    intro e h
    rw [table, List.mem_flatMap] at h
    obtain ⟨p, _, hm⟩ := h
    obtain ⟨l, _, rfl⟩ := List.mem_map.mp hm
    exact ⟨p.isLt, by omega⟩
  have incidence : ∀ p l : Fin 21, (p.val, 21 + l.val) ∈ E ↔ l - p ∈ D := by
    intro p l
    rw [table, List.mem_flatMap]
    constructor
    · rintro ⟨q, _, hq⟩
      obtain ⟨k, hk, he⟩ := List.mem_map.mp hq
      have hq' : q = p := Fin.ext (congrArg Prod.fst he)
      have hk' : k = l := Fin.ext (Nat.add_left_cancel (congrArg Prod.snd he))
      subst q
      subst k
      exact of_decide_eq_true (List.mem_filter.mp hk).2
    · intro h
      exact ⟨p, List.mem_finRange p,
        List.mem_map.mpr ⟨l, List.mem_filter.mpr ⟨List.mem_finRange l, decide_eq_true h⟩, rfl⟩⟩
  have mono : ∀ x y : Fin 42 → Bool, (∀ i, x i = true → y i = true) →
      C.eval (List.ofFn x) = true → C.eval (List.ofFn y) = true := by
    intro x y hxy hx
    let step : List Bool → Gate → List Bool :=
      fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]
    have fold : ∀ gs : List Gate,
        (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) →
        ∀ a b : List Bool, a.length = b.length →
          (∀ k, a.getD k false = true → b.getD k false = true) →
          ∀ k, (gs.foldl step a).getD k false = true → (gs.foldl step b).getD k false = true := by
      intro gs
      induction gs with
      | nil => intro _ _ _ _ h; exact h
      | cons g gs ih =>
        intro ops a b eq ab
        have op : g.op = .and ∨ g.op = .or := by simpa using ops g (by simp)
        apply ih (fun j hj => ops j (by simp [hj])) (step a g) (step b g)
        · simp [step, eq]
        · intro k hk
          by_cases hlt : k < a.length
          · have hlt' : k < b.length := by omega
            simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt] at hk
            simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt']
            exact ab k hk
          · by_cases heq : k = a.length
            · have heq' : k = b.length := by omega
              have aa : g.op.eval (g.inputs.map fun k => a.getD k false) = true := by
                simpa [step, heq, List.getD_eq_getElem?_getD] using hk
              have bb : g.op.eval (g.inputs.map fun k => b.getD k false) = true := by
                rcases op with hand | hor
                · rw [hand] at aa ⊢
                  change (g.inputs.map fun i => a.getD i false).all id = true at aa
                  change (g.inputs.map fun i => b.getD i false).all id = true
                  simp only [List.all_eq_true, List.mem_map, id_eq,
                    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at aa ⊢
                  exact fun k hk' => ab k (aa k hk')
                · rw [hor] at aa ⊢
                  change (g.inputs.map fun i => a.getD i false).any id = true at aa
                  change (g.inputs.map fun i => b.getD i false).any id = true
                  simp only [List.any_eq_true, List.mem_map, id_eq] at aa ⊢
                  obtain ⟨_, ⟨k, hk', rfl⟩, ht⟩ := aa
                  exact ⟨true, ⟨k, hk', ab k ht⟩, rfl⟩
              simpa [step, heq', List.getD_eq_getElem?_getD] using bb
            · have hg : (step a g).length ≤ k := by simp [step]; omega
              simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hg] at hk
    apply fold C.gates (fun g hg => (hC g hg).1) (List.ofFn x) (List.ofFn y) (by simp)
      _ C.output hx
    intro k hk
    by_cases h : k < 42
    · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, h, dite_eq_left, Option.getD_some] at hk ⊢
      exact hxy ⟨k, h⟩ hk
    · simp [List.getD_eq_getElem?_getD, h] at hk
  intro x
  have edgeSpec : (∃ u v : Fin 42, (u.val, v.val) ∈ E ∧ x u = true ∧ x v = true) ↔
      ∃ p l : Fin 21, l - p ∈ D ∧ x (Fin.castAdd 21 p) = true ∧ x (Fin.natAdd 21 l) = true := by
    constructor
    · rintro ⟨u, v, huv, hu, hv⟩
      have sides := leftRight _ huv
      let p : Fin 21 := ⟨u.val, sides.1⟩
      let l : Fin 21 := ⟨v.val - 21, by have := v.isLt; omega⟩
      have pu : Fin.castAdd 21 p = u := Fin.ext rfl
      have lv : Fin.natAdd 21 l = v := Fin.ext (by change 21 + (v.val - 21) = v.val; omega)
      refine ⟨p, l, incidence p l |>.mp ?_, pu.symm ▸ hu, lv.symm ▸ hv⟩
      have hpv : p.val = u.val := rfl
      have hlv : 21 + l.val = v.val := by change 21 + (v.val - 21) = v.val; omega
      simpa only [hpv, hlv] using huv
    · rintro ⟨p, l, hp, hxp, hxl⟩
      exact ⟨Fin.castAdd 21 p, Fin.natAdd 21 l, (incidence p l).mpr hp, hxp, hxl⟩
  change C.eval (List.ofFn x) = true ↔ _
  rw [edgeSpec]
  constructor
  · intro htrue
    apply Classical.byContradiction
    intro hnone
    let P := Finset.univ.filter (fun p : Fin 21 => x (Fin.castAdd 21 p) = true)
    let L := Finset.univ.filter (fun l : Fin 21 => x (Fin.natAdd 21 l) = true)
    have pMem : ∀ p, p ∈ P ↔ x (Fin.castAdd 21 p) = true := by intro p; simp [P]
    have lMem : ∀ l, l ∈ L ↔ x (Fin.natAdd 21 l) = true := by intro l; simp [L]
    have noEdge : ∀ p ∈ P, ∀ l ∈ L, l - p ∉ D :=
      fun p hp l hl hadj => hnone ⟨p, l, hadj, (pMem p).mp hp, (lMem l).mp hl⟩
    let yP : Fin 42 → Bool := Fin.append
      (fun (p : Fin 21) => decide (p ∈ P)) (fun (l : Fin 21) => decide (∀ p ∈ P, l - p ∉ D))
    let yL : Fin 42 → Bool := Fin.append
      (fun (p : Fin 21) => decide (∀ l ∈ L, l - p ∉ D)) (fun (l : Fin 21) => decide (l ∈ L))
    have coverP : ∀ i, x i = true → yP i = true := by
      intro i
      refine Fin.addCases (m := 21) (n := 21) (motive := fun k => x k = true → yP k = true)
        (fun p hp => ?_) (fun l hl => ?_) i
      · simpa only [yP, Fin.append_left, decide_eq_true_eq] using (pMem p).mpr hp
      · have h : ∀ p ∈ P, l - p ∉ D := fun p hp => noEdge p hp l ((lMem l).mpr hl)
        simpa only [yP, Fin.append_right, decide_eq_true_eq] using h
    have coverL : ∀ i, x i = true → yL i = true := by
      intro i
      refine Fin.addCases (m := 21) (n := 21) (motive := fun k => x k = true → yL k = true)
        (fun p hp => ?_) (fun l hl => ?_) i
      · simpa only [yL, Fin.append_left, decide_eq_true_eq] using noEdge p ((pMem p).mpr hp)
      · simpa only [yL, Fin.append_right, decide_eq_true_eq] using (lMem l).mpr hl
    by_cases hp : P.card ≤ 5
    · have hf := (hn P hp).1
      have ht := mono x yP coverP htrue
      simp only [yP, D] at ht
      rw [hf] at ht
      exact Bool.false_ne_true ht
    by_cases hl : L.card ≤ 5
    · have hf := (hn L hl).2
      have ht := mono x yL coverL htrue
      simp only [yL, D] at ht
      rw [hf] at ht
      exact Bool.false_ne_true ht
    obtain ⟨size, config⟩ := geometry P L (by omega) (by omega) noEdge
    have hf := hexc P size config
    have ht := mono x yP coverP htrue
    simp only [yP, D] at ht
    rw [hf] at ht
    exact Bool.false_ne_true ht
  · rintro ⟨p, l, hadj, hp, hl⟩
    let y : Fin 42 → Bool := Fin.append (fun i => decide (i = p)) (fun j => decide (j = l))
    apply mono y x ?_ (hy p l hadj)
    intro i
    refine Fin.addCases (m := 21) (n := 21)
      (motive := fun k => y k = true → x k = true) (fun a ha => ?_) (fun b hb => ?_) i
    · have : a = p := by simpa only [y, Fin.append_left, decide_eq_true_eq] using ha
      simpa [this] using hp
    · have : b = l := by simpa only [y, Fin.append_right, decide_eq_true_eq] using hb
      simpa [this] using hl
