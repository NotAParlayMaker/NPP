import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 1500000 in
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.R_meta_2377_512
    (lowAnd :
      let E := fun u v : Fin 42 => u.val < 21 ∧ 21 ≤ v.val ∧
        (v.val + 21 - u.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)
      let orCost := fun D : Circuit =>
        ({i : Fin D.gates.length | (D.gates.get i).op = GateOp.or} : Set _).ncard
      let andCost := fun D : Circuit =>
        ({i : Fin D.gates.length | (D.gates.get i).op = GateOp.and} : Set _).ncard
      let bypass := fun (D : Circuit) (j w : ℕ) =>
        ({D with gates := D.gates.set j ⟨GateOp.and, [w]⟩} : Circuit)
      let row := fun (u v z : Fin 42) => decide (z = u ∨ z = v)
      ∀ D : Circuit, Monotone2 D →
        (∀ x : Fin 42 → Bool, D.eval (List.ofFn x) = true ↔ ∃ u v, E u v ∧ x u = true ∧ x v = true) →
        (∀ j : Fin D.gates.length, (D.gates.get j).op = GateOp.or →
          (∃ w1 w2, (D.gates.get j).inputs = [w1, w2] ∧ w1 ≠ w2) ∧
          ∀ w ∈ (D.gates.get j).inputs, ∃ u v, E u v ∧
            (bypass D j.val w).eval (List.ofFn (row u v)) = false ∧
            let pre := ({D with gates := D.gates.take j.val} : Circuit).wires (List.ofFn (row u v))
            pre.getD w false = false ∧ ∃ k ∈ (D.gates.get j).inputs, pre.getD k false = true) →
        andCost D ≤ 20 →
        104 ≤ orCost D)
    (highAnd :
      let E := fun u v : Fin 42 => u.val < 21 ∧ 21 ≤ v.val ∧
        (v.val + 21 - u.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)
      let orCost := fun D : Circuit =>
        ({i : Fin D.gates.length | (D.gates.get i).op = GateOp.or} : Set _).ncard
      let andCost := fun D : Circuit =>
        ({i : Fin D.gates.length | (D.gates.get i).op = GateOp.and} : Set _).ncard
      let bypass := fun (D : Circuit) (j w : ℕ) =>
        ({D with gates := D.gates.set j ⟨GateOp.and, [w]⟩} : Circuit)
      let row := fun (u v z : Fin 42) => decide (z = u ∨ z = v)
      ∀ D : Circuit, Monotone2 D →
        (∀ x : Fin 42 → Bool, D.eval (List.ofFn x) = true ↔ ∃ u v, E u v ∧ x u = true ∧ x v = true) →
        (∀ j : Fin D.gates.length, (D.gates.get j).op = GateOp.or →
          (∃ w1 w2, (D.gates.get j).inputs = [w1, w2] ∧ w1 ≠ w2) ∧
          ∀ w ∈ (D.gates.get j).inputs, ∃ u v, E u v ∧
            (bypass D j.val w).eval (List.ofFn (row u v)) = false ∧
            let pre := ({D with gates := D.gates.take j.val} : Circuit).wires (List.ofFn (row u v))
            pre.getD w false = false ∧ ∃ k ∈ (D.gates.get j).inputs, pre.getD k false = true) →
        21 ≤ andCost D →
        104 ≤ orCost D) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x3 : Fin (42 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (42 : ℕ)) (x5 : Fin (42 : ℕ)), (↑x4, ↑x5) ∈ List.flatMap (fun (x6 : ℕ) => [(x6, (21 : ℕ) + (x6 + (20 : ℕ)) % (21 : ℕ)), (x6, (21 : ℕ) + x6), (x6, (21 : ℕ) + (x6 + (5 : ℕ)) % (21 : ℕ)), (x6, (21 : ℕ) + (x6 + (7 : ℕ)) % (21 : ℕ)), (x6, (21 : ℕ) + (x6 + (17 : ℕ)) % (21 : ℕ))]) (List.range (21 : ℕ)) ∧ x3 x4 = Bool.true ∧ x3 x5 = Bool.true) → (104 : ℕ) ≤ {x4 : Fin x1.gates.length | (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.or}.ncard := by
  classical
  intro C hm hf
  let E : Fin 42 → Fin 42 → Prop := fun u v =>
    u.val < 21 ∧ 21 ≤ v.val ∧ (v.val + 21 - u.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)
  let orCost : Circuit → ℕ := fun D =>
    ({i : Fin D.gates.length | (D.gates.get i).op = GateOp.or} : Set _).ncard
  let andCost : Circuit → ℕ := fun D =>
    ({i : Fin D.gates.length | (D.gates.get i).op = GateOp.and} : Set _).ncard
  let bypass : Circuit → ℕ → ℕ → Circuit := fun D j w =>
    {D with gates := D.gates.set j ⟨GateOp.and, [w]⟩}
  let computes : Circuit → Prop := fun D =>
    ∀ x : Fin 42 → Bool, D.eval (List.ofFn x) = true ↔ ∃ u v, E u v ∧ x u = true ∧ x v = true
  let row : Fin 42 → Fin 42 → Fin 42 → Bool := fun u v z => decide (z = u ∨ z = v)
  have key : ∀ (u v : Fin 42),
      ((u.val, v.val) ∈ List.flatMap (fun (x6 : ℕ) =>
        [(x6, (21 : ℕ) + (x6 + (20 : ℕ)) % (21 : ℕ)), (x6, (21 : ℕ) + x6),
         (x6, (21 : ℕ) + (x6 + (5 : ℕ)) % (21 : ℕ)), (x6, (21 : ℕ) + (x6 + (7 : ℕ)) % (21 : ℕ)),
         (x6, (21 : ℕ) + (x6 + (17 : ℕ)) % (21 : ℕ))]) (List.range (21 : ℕ))) ↔ E u v := by
    intro u v
    rw [List.mem_flatMap]
    dsimp only [E]
    simp only [List.mem_range, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq]
    constructor
    · rintro ⟨x, hx, ⟨rfl, hv⟩ | ⟨rfl, hv⟩ | ⟨rfl, hv⟩ | ⟨rfl, hv⟩ | ⟨rfl, hv⟩⟩ <;>
        refine ⟨hx, by omega, ?_⟩
      · right; right; right; right; omega
      · left; omega
      · right; left; omega
      · right; right; left; omega
      · right; right; right; left; omega
    · rintro ⟨hu, hv, hmem⟩
      refine ⟨u.val, hu, ?_⟩
      have hvlt : v.val < 42 := v.isLt
      rcases hmem with h | h | h | h | h
      · right; left; exact ⟨rfl, by omega⟩
      · right; right; left; exact ⟨rfl, by omega⟩
      · right; right; right; left; exact ⟨rfl, by omega⟩
      · right; right; right; right; exact ⟨rfl, by omega⟩
      · left; exact ⟨rfl, by omega⟩
  have hCcomp : computes C := by
    intro x
    rw [hf x]
    constructor
    · rintro ⟨u, v, huv, hxu, hxv⟩; exact ⟨u, v, (key u v).mp huv, hxu, hxv⟩
    · rintro ⟨u, v, huv, hxu, hxv⟩; exact ⟨u, v, (key u v).mpr huv, hxu, hxv⟩
  let leW : List Bool → List Bool → Prop := fun a b =>
    a.length = b.length ∧ ∀ i, a.getD i false = true → b.getD i false = true
  have gate_mono : ∀ (g : Gate), (g.op = .and ∨ g.op = .or) →
      ∀ (a b : List Bool), leW a b →
      g.op.eval (g.inputs.map fun i => a.getD i false) = true →
      g.op.eval (g.inputs.map fun i => b.getD i false) = true := by
    intro g hop a b hab htrue
    rcases hop with h | h <;> rw [h] at htrue ⊢
    · simp only [GateOp.eval, List.all_eq_true, List.mem_map] at htrue ⊢
      rintro y ⟨i, hi, rfl⟩
      exact hab.2 i (htrue (a.getD i false) ⟨i, hi, rfl⟩)
    · simp only [GateOp.eval, List.any_eq_true, List.mem_map] at htrue ⊢
      obtain ⟨_, ⟨i, hi, rfl⟩, hbi⟩ := htrue
      exact ⟨true, ⟨i, hi, hab.2 i hbi⟩, rfl⟩
  have fold_mono : ∀ (gs : List Gate), (∀ g ∈ gs, g.op = .and ∨ g.op = .or) →
      ∀ (a b : List Bool), leW a b →
      leW (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) a)
          (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) b) := by
    intro gs; induction gs with
    | nil => intro _ a b hab; exact hab
    | cons g r ih =>
      intro hgs a b hab
      simp only [List.foldl_cons]
      apply ih (fun t ht => hgs t (by simp [ht]))
      refine ⟨by simp [hab.1], fun i hi => ?_⟩
      by_cases hlt : i < a.length
      · simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt] at hi
        simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : i < b.length)]
        exact hab.2 i (by simpa [List.getD_eq_getElem?_getD] using hi)
      · by_cases heq : i = a.length
        · subst heq
          simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl, Nat.sub_self,
            List.getElem?_cons_zero, Option.getD_some] at hi
          simp only [List.getD_eq_getElem?_getD, hab.1, List.getElem?_append_right le_rfl, Nat.sub_self,
            List.getElem?_cons_zero, Option.getD_some]
          exact gate_mono g (hgs g (by simp)) a b hab hi
        · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)] at hi
          cases hi
  have mono_eval : ∀ (D : Circuit), Monotone2 D →
      ∀ (x y : Fin 42 → Bool), (∀ i, x i = true → y i = true) →
      D.eval (List.ofFn x) = true → D.eval (List.ofFn y) = true := by
    intro D hD x y hxy hx
    have hle : leW (List.ofFn x) (List.ofFn y) := by
      refine ⟨by simp, fun i hi => ?_⟩
      by_cases hlt : i < 42
      · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hlt, ↓reduceDIte, Option.getD_some] at hi ⊢
        exact hxy ⟨i, hlt⟩ hi
      · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hlt, ↓reduceDIte, Option.getD_none] at hi
        cases hi
    have hres := fold_mono D.gates (fun g hg => by
      have := (hD g hg).1; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this; exact this)
      (List.ofFn x) (List.ofFn y) hle
    exact hres.2 D.output hx
  have bypass_mono2 : ∀ (D : Circuit) (j w : ℕ), Monotone2 D → Monotone2 (bypass D j w) := by
    intro D j w hD g hg
    dsimp only [bypass] at hg
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hg
    rw [List.getElem_set]
    split_ifs
    · exact ⟨by simp, by simp⟩
    · exact hD _ (List.getElem_mem (by rw [List.length_set] at hk; exact hk))
  have bypass_cost_lt : ∀ (D : Circuit) (j : Fin D.gates.length) (w : ℕ),
      (D.gates.get j).op = GateOp.or → orCost (bypass D j.val w) < orCost D := by
    intro D j w hop
    dsimp only [orCost, bypass]
    let e : Fin (D.gates.set j.val ⟨GateOp.and, [w]⟩).length ≃ Fin D.gates.length :=
      finCongr (List.length_set)
    let S1 : Set (Fin (D.gates.set j.val ⟨GateOp.and, [w]⟩).length) :=
      {i | ((D.gates.set j.val ⟨GateOp.and, [w]⟩).get i).op = GateOp.or}
    let S2 : Set (Fin D.gates.length) := {i | (D.gates.get i).op = GateOp.or}
    have hcard : S1.ncard = (e '' S1).ncard := (Set.ncard_image_of_injective S1 e.injective).symm
    rw [hcard]
    apply Set.ncard_lt_ncard
    · refine ⟨?_, ?_⟩
      · rintro k ⟨i, hi, rfl⟩
        have hget : (D.gates.set j.val ⟨GateOp.and, [w]⟩).get i =
            if j.val = i.val then ⟨GateOp.and, [w]⟩ else D.gates.get (e i) := by
          simp only [List.get_eq_getElem, List.getElem_set, e, finCongr_apply, Fin.val_cast]
        change ((D.gates.set j.val ⟨GateOp.and, [w]⟩).get i).op = GateOp.or at hi
        rw [hget] at hi
        by_cases hij : j.val = i.val
        · rw [if_pos hij] at hi; cases hi
        · rw [if_neg hij] at hi; exact hi
      · intro hsub
        have hjmem : j ∈ e '' S1 := hsub hop
        obtain ⟨i, hi, hij⟩ := hjmem
        have hival : i.val = j.val := by
          have := congrArg Fin.val hij
          simpa [e] using this
        change ((D.gates.set j.val ⟨GateOp.and, [w]⟩).get i).op = GateOp.or at hi
        simp only [List.get_eq_getElem, List.getElem_set, hival, ↓reduceIte] at hi
        cases hi
    · exact Set.toFinite S2
  have bypass_le : ∀ (D : Circuit) (j : Fin D.gates.length) (w : ℕ),
      Monotone2 D → (D.gates.get j).op = GateOp.or →
      w ∈ (D.gates.get j).inputs →
      ∀ (x : Fin 42 → Bool), (bypass D j.val w).eval (List.ofFn x) = true → D.eval (List.ofFn x) = true := by
    intro D j w hD hop hmem x hx
    let g := D.gates.get j
    have hsplit : D.gates.take j.val ++ g :: D.gates.drop (j.val + 1) = D.gates := by
      simp [g, List.get_eq_getElem, List.getElem_cons_drop, List.take_append_drop]
    let pre := (D.gates.take j.val).foldl (fun ws t => ws ++ [t.op.eval (t.inputs.map fun i => ws.getD i false)]) (List.ofFn x)
    have hset : D.gates.set j.val ⟨GateOp.and, [w]⟩ = D.gates.take j.val ++ ⟨GateOp.and, [w]⟩ :: D.gates.drop (j.val + 1) := by
      rw [List.set_eq_take_append_cons_drop, if_pos j.isLt]
    have hB : (bypass D j.val w).wires (List.ofFn x) =
        (D.gates.drop (j.val + 1)).foldl (fun ws t => ws ++ [t.op.eval (t.inputs.map fun i => ws.getD i false)])
          (pre ++ [pre.getD w false]) := by
      dsimp only [bypass, Circuit.wires]
      rw [hset, List.foldl_append, List.foldl_cons]
      have hhead : GateOp.and.eval ([w].map fun i => pre.getD i false) = pre.getD w false := by
        simp [GateOp.eval]
      rw [hhead]
    have hD' : D.wires (List.ofFn x) =
        (D.gates.drop (j.val + 1)).foldl (fun ws t => ws ++ [t.op.eval (t.inputs.map fun i => ws.getD i false)])
          (pre ++ [g.op.eval (g.inputs.map fun i => pre.getD i false)]) := by
      dsimp only [Circuit.wires]
      conv_lhs => rw [← hsplit]
      rw [List.foldl_append, List.foldl_cons]
    have hstep : leW (pre ++ [pre.getD w false]) (pre ++ [g.op.eval (g.inputs.map fun i => pre.getD i false)]) := by
      refine ⟨by simp, fun i hi => ?_⟩
      by_cases hlt : i < pre.length
      · simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt] at hi ⊢; exact hi
      · by_cases heq : i = pre.length
        · subst heq
          simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl, Nat.sub_self,
            List.getElem?_cons_zero, Option.getD_some] at hi ⊢
          rw [show g.op = GateOp.or from hop]
          exact List.any_eq_true.mpr ⟨true, List.mem_map.mpr ⟨w, hmem, hi⟩, rfl⟩
        · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)] at hi; cases hi
    have hres := fold_mono (D.gates.drop (j.val + 1)) (fun t ht => by
      have := (hD t (List.mem_of_mem_drop ht)).1; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this; exact this)
      _ _ hstep
    unfold Circuit.eval at hx ⊢
    rw [hB] at hx; rw [hD']
    exact hres.2 D.output hx
  have local_witness : ∀ (D : Circuit) (j : Fin D.gates.length) (pin : ℕ),
      (D.gates.get j).op = GateOp.or → pin ∈ (D.gates.get j).inputs →
      ∀ (x : List Bool), (bypass D j.val pin).eval x ≠ D.eval x →
      let pre := ({D with gates := D.gates.take j.val} : Circuit).wires x
      pre.getD pin false = false ∧ ∃ k ∈ (D.gates.get j).inputs, pre.getD k false = true := by
    intro D j pin hop hmem x hchg
    let pre := ({D with gates := D.gates.take j.val} : Circuit).wires x
    let g := D.gates.get j
    have hsplit : D.gates.take j.val ++ g :: D.gates.drop (j.val + 1) = D.gates := by
      simp [g, List.get_eq_getElem, List.getElem_cons_drop, List.take_append_drop]
    have hdiff : pre.getD pin false ≠ g.op.eval (g.inputs.map fun i => pre.getD i false) := by
      intro heq
      apply hchg
      change ((D.gates.set j.val _).foldl _ x).getD _ _ = (D.gates.foldl _ x).getD _ _
      conv_rhs => rw [← hsplit]
      rw [List.set_eq_take_append_cons_drop, if_pos j.isLt]
      have hhead : GateOp.and.eval ([pin].map fun i => pre.getD i false) = pre.getD pin false := by
        simp [GateOp.eval]
      simp only [List.foldl_append, List.foldl_cons]
      have : pre ++ [GateOp.and.eval ([pin].map fun i => pre.getD i false)] =
          pre ++ [g.op.eval (g.inputs.map fun i => pre.getD i false)] := by rw [hhead, heq]
      change ((D.gates.drop (j.val + 1)).foldl _ (pre ++ [GateOp.and.eval ([pin].map fun i => pre.getD i false)])).getD D.output false =
        ((D.gates.drop (j.val + 1)).foldl _ (pre ++ [g.op.eval (g.inputs.map fun i => pre.getD i false)])).getD D.output false
      rw [this]
    have hfires : pre.getD pin false = true → g.op.eval (g.inputs.map fun i => pre.getD i false) = true := by
      intro hy
      rw [show g.op = GateOp.or from hop]
      exact List.any_eq_true.mpr ⟨true, List.mem_map.mpr ⟨pin, hmem, hy⟩, rfl⟩
    have hoff : pre.getD pin false = false := by
      cases h : pre.getD pin false
      · rfl
      · exact False.elim (hdiff (h.trans (hfires h).symm))
    have hon : g.op.eval (g.inputs.map fun i => pre.getD i false) = true := by
      cases h : g.op.eval (g.inputs.map fun i => pre.getD i false)
      · exact False.elim (hdiff (hoff.trans h.symm))
      · rfl
    rw [show g.op = GateOp.or from hop] at hon
    obtain ⟨b, hb, hbeq⟩ := List.any_eq_true.mp hon
    obtain ⟨k, hk, hkb⟩ := List.mem_map.mp hb
    exact ⟨hoff, k, hk, hkb.trans hbeq⟩
  have hmain : ∀ s, ∀ D : Circuit, orCost D = s → Monotone2 D → computes D → 104 ≤ s := by
    intro s
    induction s using Nat.strong_induction_on with
    | ind s ih =>
      intro D hs hD hcomp
      by_cases hEmpty : ∃ j : Fin D.gates.length, (D.gates.get j).op = GateOp.or ∧ (D.gates.get j).inputs = []
      · obtain ⟨j, hop, hnil⟩ := hEmpty
        let oob := 42 + D.gates.length
        let B := bypass D j.val oob
        have hBlt : orCost B < s := hs ▸ bypass_cost_lt D j oob hop
        have hBeq : ∀ x : Fin 42 → Bool, B.eval (List.ofFn x) = D.eval (List.ofFn x) := by
          intro x
          let g := D.gates.get j
          have hsplit : D.gates.take j.val ++ g :: D.gates.drop (j.val + 1) = D.gates := by
            simp [g, List.get_eq_getElem, List.getElem_cons_drop, List.take_append_drop]
          let pre := (D.gates.take j.val).foldl (fun ws t => ws ++ [t.op.eval (t.inputs.map fun i => ws.getD i false)]) (List.ofFn x)
          have hpreLen : pre.length = 42 + j.val := by
            have hfl : ∀ (gs : List Gate) (acc : List Bool),
                (gs.foldl (fun ws t => ws ++ [t.op.eval (t.inputs.map fun i => ws.getD i false)]) acc).length = acc.length + gs.length := by
              intro gs; induction gs with
              | nil => intro acc; simp
              | cons t r ihr => intro acc; simp only [List.foldl_cons, ihr, List.length_append, List.length_cons, List.length_nil]; omega
            dsimp only [pre]; rw [hfl, List.length_ofFn, List.length_take, Nat.min_eq_left (Nat.le_of_lt j.isLt)]
          have hoob : pre.getD oob false = false := by
            simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : pre.length ≤ oob)]
          have hsame : GateOp.and.eval ([oob].map fun i => pre.getD i false) =
              g.op.eval (g.inputs.map fun i => pre.getD i false) := by
            simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true,
              hoob, show g.op = GateOp.or from hop, show g.inputs = [] from hnil]; rfl
          unfold Circuit.eval Circuit.wires
          dsimp only [B, bypass]
          conv_rhs => rw [← hsplit]
          rw [List.set_eq_take_append_cons_drop, if_pos j.isLt]
          simp only [List.foldl_append, List.foldl_cons]
          change ((D.gates.drop (j.val + 1)).foldl _ (pre ++ [GateOp.and.eval ([oob].map fun i => pre.getD i false)])).getD D.output false =
            ((D.gates.drop (j.val + 1)).foldl _ (pre ++ [g.op.eval (g.inputs.map fun i => pre.getD i false)])).getD D.output false
          rw [hsame]
        have hBcomp : computes B := fun x => by rw [hBeq x]; exact hcomp x
        have h104 := ih (orCost B) hBlt B rfl (bypass_mono2 D j.val oob hD) hBcomp
        omega
      · push Not at hEmpty
        by_cases hCrit : ∀ j : Fin D.gates.length, (D.gates.get j).op = GateOp.or →
            ∀ w ∈ (D.gates.get j).inputs, ∃ u v, E u v ∧ (bypass D j.val w).eval (List.ofFn (row u v)) = false
        · have hFullCrit : ∀ j : Fin D.gates.length, (D.gates.get j).op = GateOp.or →
              (∃ w1 w2, (D.gates.get j).inputs = [w1, w2] ∧ w1 ≠ w2) ∧
              ∀ w ∈ (D.gates.get j).inputs, ∃ u v, E u v ∧
                (bypass D j.val w).eval (List.ofFn (row u v)) = false ∧
                let pre := ({D with gates := D.gates.take j.val} : Circuit).wires (List.ofFn (row u v))
                pre.getD w false = false ∧ ∃ k ∈ (D.gates.get j).inputs, pre.getD k false = true := by
            intro j hop
            have hW : ∀ w ∈ (D.gates.get j).inputs, ∃ u v, E u v ∧
                (bypass D j.val w).eval (List.ofFn (row u v)) = false ∧
                let pre := ({D with gates := D.gates.take j.val} : Circuit).wires (List.ofFn (row u v))
                pre.getD w false = false ∧ ∃ k ∈ (D.gates.get j).inputs, pre.getD k false = true := by
              intro w hw
              obtain ⟨u, v, huv, hlost⟩ := hCrit j hop w hw
              have hacc : D.eval (List.ofFn (row u v)) = true :=
                (hcomp (row u v)).mpr ⟨u, v, huv, by simp [row], by simp [row]⟩
              have hdiff : (bypass D j.val w).eval (List.ofFn (row u v)) ≠ D.eval (List.ofFn (row u v)) := by
                rw [hlost, hacc]; decide
              exact ⟨u, v, huv, hlost, local_witness D j w hop hw _ hdiff⟩
            refine ⟨?_, hW⟩
            have hle2 := (hD (D.gates.get j) (List.get_mem _ _)).2
            cases hgin : (D.gates.get j).inputs with
            | nil => exact False.elim (hEmpty j hop hgin)
            | cons w1 tl =>
              cases tl with
              | nil =>
                obtain ⟨u, v, _, _, hoff, k, hk, hkt⟩ := hW w1 (by rw [hgin]; simp)
                rw [hgin] at hk; simp at hk; subst hk; rw [hoff] at hkt; cases hkt
              | cons w2 tl2 =>
                cases tl2 with
                | nil =>
                  refine ⟨w1, w2, rfl, ?_⟩
                  intro heq; subst heq
                  obtain ⟨u, v, _, _, hoff, k, hk, hkt⟩ := hW w1 (by rw [hgin]; simp)
                  rw [hgin] at hk; simp at hk; subst hk; rw [hoff] at hkt; cases hkt
                | cons _ _ => rw [hgin] at hle2; simp at hle2
          rw [← hs]
          by_cases hAnd : andCost D ≤ 20
          · exact lowAnd D hD hcomp hFullCrit hAnd
          · exact highAnd D hD hcomp hFullCrit (by change 21 ≤ andCost D; omega)
        · push Not at hCrit
          obtain ⟨j, hop, w, hw, hkeep⟩ := hCrit
          let B := bypass D j.val w
          have hBlt : orCost B < s := hs ▸ bypass_cost_lt D j w hop
          have hBmono : Monotone2 B := bypass_mono2 D j.val w hD
          have hBcomp : computes B := by
            intro x
            constructor
            · intro hbx
              exact (hcomp x).mp (bypass_le D j w hD hop hw x hbx)
            · rintro ⟨u, v, huv, hxu, hxv⟩
              have hrow : B.eval (List.ofFn (row u v)) = true := by
                cases h : B.eval (List.ofFn (row u v))
                · exact False.elim (hkeep u v huv h)
                · rfl
              exact mono_eval B hBmono (row u v) x (fun z hz => by
                dsimp only [row] at hz; simp only [decide_eq_true_eq] at hz
                rcases hz with rfl | rfl <;> assumption) hrow
          have h104 := ih (orCost B) hBlt B rfl hBmono hBcomp
          omega
  exact hmain (orCost C) C rfl hm hCcomp
