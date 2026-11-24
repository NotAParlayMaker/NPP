import Mathlib.Data.List.OfFn
import Mathlib.Tactic.Push
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The search needs only incident pairs and maximal independent sets.
set_option maxRecDepth 32768 in
set_option maxHeartbeats 1500000 in
theorem PEqualNP.Outside.R_meta_650_1
    (hRows : let D : Finset (Fin 13) := {0, 1, 3, 9}
     ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 63 ∧
       (∀ p l : Fin 13, p + l ∈ D →
         C.eval (List.ofFn (fun a : Fin 13 => decide (a = p)) ++
           List.ofFn (fun b : Fin 13 => decide (b = l))) = true) ∧
       (∀ P : Finset (Fin 13),
         (∀ p : Fin 13, p ∉ P → ∃ l : Fin 13, p + l ∈ D ∧ ∀ q ∈ P, q + l ∉ D) →
         C.eval (List.ofFn (fun a : Fin 13 => decide (a ∈ P)) ++
           List.ofFn (fun b : Fin 13 => decide (∀ a ∈ P, a + b ∉ D))) = false))
    (hTable : ∀ p l : Fin 13,
      Nat.testBit 0x41641641601621621621621621620620e20a20a20b (13 * p.val + l.val) = true ↔
        p + l = 0 ∨ p + l = 1 ∨ p + l = 3 ∨ p + l = 9) :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 63 ∧ (∀ x : Fin 26 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 26, (u.val, v.val) ∈ ([(0, 13), (0, 14), (0, 16), (0, 22), (1, 13), (1, 15), (1, 21), (1, 25), (2, 14), (2, 20), (2, 24), (2, 25), (3, 13), (3, 19), (3, 23), (3, 24), (4, 18), (4, 22), (4, 23), (4, 25), (5, 17), (5, 21), (5, 22), (5, 24), (6, 16), (6, 20), (6, 21), (6, 23), (7, 15), (7, 19), (7, 20), (7, 22), (8, 14), (8, 18), (8, 19), (8, 21), (9, 13), (9, 17), (9, 18), (9, 20), (10, 16), (10, 17), (10, 19), (10, 25), (11, 15), (11, 16), (11, 18), (11, 24), (12, 14), (12, 15), (12, 17), (12, 23)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) := by
  classical
  obtain ⟨C, hC, hsize, hpositive, hnegative⟩ := hRows
  refine ⟨C, hC, hsize, ?_⟩
  let D : Finset (Fin 13) := {0, 1, 3, 9}
  -- The adjacency matrix uses thirteen consecutive bits for each point.
  have hRaw : ∀ u v : Fin 26, (u.val, v.val) ∈ ([(0, 13), (0, 14), (0, 16), (0, 22), (1, 13), (1, 15), (1, 21), (1, 25), (2, 14), (2, 20), (2, 24), (2, 25), (3, 13), (3, 19), (3, 23), (3, 24), (4, 18), (4, 22), (4, 23), (4, 25), (5, 17), (5, 21), (5, 22), (5, 24), (6, 16), (6, 20), (6, 21), (6, 23), (7, 15), (7, 19), (7, 20), (7, 22), (8, 14), (8, 18), (8, 19), (8, 21), (9, 13), (9, 17), (9, 18), (9, 20), (10, 16), (10, 17), (10, 19), (10, 25), (11, 15), (11, 16), (11, 18), (11, 24), (12, 14), (12, 15), (12, 17), (12, 23)] : List (ℕ × ℕ)) ↔
      u.val < 13 ∧ 13 ≤ v.val ∧ Nat.testBit 0x41641641601621621621621621620620e20a20a20b (13 * u.val + (v.val - 13)) = true := by
    decide +kernel
  have hIncidence (u v : Fin 26) : (u.val, v.val) ∈ ([(0, 13), (0, 14), (0, 16), (0, 22), (1, 13), (1, 15), (1, 21), (1, 25), (2, 14), (2, 20), (2, 24), (2, 25), (3, 13), (3, 19), (3, 23), (3, 24), (4, 18), (4, 22), (4, 23), (4, 25), (5, 17), (5, 21), (5, 22), (5, 24), (6, 16), (6, 20), (6, 21), (6, 23), (7, 15), (7, 19), (7, 20), (7, 22), (8, 14), (8, 18), (8, 19), (8, 21), (9, 13), (9, 17), (9, 18), (9, 20), (10, 16), (10, 17), (10, 19), (10, 25), (11, 15), (11, 16), (11, 18), (11, 24), (12, 14), (12, 15), (12, 17), (12, 23)] : List (ℕ × ℕ)) ↔
      ∃ p l : Fin 13, u = Fin.castAdd 13 p ∧ v = Fin.natAdd 13 l ∧ p + l ∈ D := by
    rw [hRaw]
    constructor
    · rintro ⟨hu, hv, hbit⟩
      let p : Fin 13 := ⟨u.val, hu⟩
      let l : Fin 13 := ⟨v.val - 13, by have := v.isLt; omega⟩
      refine ⟨p, l, Fin.ext rfl, Fin.ext ?_, ?_⟩
      · change v.val = 13 + (v.val - 13)
        omega
      · simpa only [D, Finset.mem_insert, Finset.mem_singleton] using (hTable p l).mp hbit
    · rintro ⟨p, l, rfl, rfl, hpl⟩
      change p.val < 13 ∧ 13 ≤ 13 + l.val ∧
        Nat.testBit 0x41641641601621621621621621620620e20a20a20b (13 * p.val + (13 + l.val - 13)) = true
      rw [Nat.add_sub_cancel_left]
      refine ⟨p.isLt, Nat.le_add_right _ _, (hTable p l).mpr ?_⟩
      simpa only [D, Finset.mem_insert, Finset.mem_singleton] using hpl
  let addGate := fun (ws : List Bool) (g : Gate) =>
    ws ++ [g.op.eval (g.inputs.map fun w => ws.getD w false)]
  have gateMono (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or)
      (xs ys : List Bool) (hxy : ∀ w, xs.getD w false = true → ys.getD w false = true) :
      g.op.eval (g.inputs.map fun w => xs.getD w false) = true →
      g.op.eval (g.inputs.map fun w => ys.getD w false) = true := by
    rcases hg with hop | hop
    · rw [hop]
      change (g.inputs.map fun w => xs.getD w false).all id = true →
        (g.inputs.map fun w => ys.getD w false).all id = true
      simp only [List.all_eq_true, List.mem_map, id_eq]
      rintro ht _ ⟨w, hw, rfl⟩
      exact hxy w (ht _ ⟨w, hw, rfl⟩)
    · rw [hop]
      change (g.inputs.map fun w => xs.getD w false).any id = true →
        (g.inputs.map fun w => ys.getD w false).any id = true
      simp only [List.any_eq_true, List.mem_map, id_eq]
      rintro ⟨_, ⟨w, hw, rfl⟩, ht⟩
      exact ⟨_, ⟨w, hw, rfl⟩, hxy w ht⟩
  have appendMono (xs ys : List Bool) (a b : Bool) (he : xs.length = ys.length)
      (hxy : ∀ w, xs.getD w false = true → ys.getD w false = true)
      (hab : a = true → b = true) : ∀ w,
      (xs ++ [a]).getD w false = true → (ys ++ [b]).getD w false = true := by
    intro w
    by_cases hw : w < xs.length
    · rw [List.getD_append _ _ _ _ hw, List.getD_append _ _ _ _ (by rwa [← he])]
      exact hxy w
    · rw [List.getD_append_right _ _ _ _ (Nat.le_of_not_gt hw),
        List.getD_append_right _ _ _ _ (by rw [← he]; omega), he]
      cases w - ys.length with
      | zero => simpa using hab
      | succ k => simp
  have runMono (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
      (xs ys : List Bool) (he : xs.length = ys.length)
      (hxy : ∀ w, xs.getD w false = true → ys.getD w false = true) : ∀ w,
      (gs.foldl addGate xs).getD w false = true → (gs.foldl addGate ys).getD w false = true := by
    induction gs generalizing xs ys with
    | nil => exact hxy
    | cons g gs ih =>
      exact ih (fun k hk => hgs k (List.mem_cons_of_mem _ hk)) _ _
        (by simp [addGate, he]) (appendMono _ _ _ _ he hxy
          (gateMono g (hgs g List.mem_cons_self) xs ys hxy))
  have mono (x y : Fin 26 → Bool) (hxy : ∀ i, x i = true → y i = true) :
      C.eval (List.ofFn x) = true → C.eval (List.ofFn y) = true := by
    change (C.gates.foldl addGate (List.ofFn x)).getD C.output false = true →
      (C.gates.foldl addGate (List.ofFn y)).getD C.output false = true
    have hops : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
      intro g hg
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using (hC g hg).1
    refine runMono C.gates hops _ _ (by simp) ?_ C.output
    intro w
    by_cases hw : w < 26
    · rw [List.getD_eq_getElem (List.ofFn x) false (by simpa only [List.length_ofFn] using hw),
        List.getD_eq_getElem (List.ofFn y) false (by simpa only [List.length_ofFn] using hw)]
      simpa only [List.getElem_ofFn] using hxy ⟨w, hw⟩
    · rw [List.getD_eq_default (List.ofFn x) false (by simpa only [List.length_ofFn] using Nat.le_of_not_gt hw)]
      simp
  intro x
  let left : Fin 13 → Bool := fun i => x (Fin.castAdd 13 i)
  let right : Fin 13 → Bool := fun i => x (Fin.natAdd 13 i)
  constructor
  · intro heval
    by_contra hn
    let R : Finset (Fin 13) := Finset.univ.filter fun l => right l = true
    let P : Finset (Fin 13) := Finset.univ.filter fun p => ∀ l ∈ R, p + l ∉ D
    have hleft (p : Fin 13) (hp : left p = true) : p ∈ P := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      intro l hl hpL
      apply hn
      refine ⟨Fin.castAdd 13 p, Fin.natAdd 13 l, ?_, hp, (Finset.mem_filter.mp hl).2⟩
      exact (hIncidence _ _).mpr ⟨p, l, rfl, rfl, hpL⟩
    have hright (l : Fin 13) (hl : right l = true) : ∀ p ∈ P, p + l ∉ D := by
      intro p hp
      exact (Finset.mem_filter.mp hp).2 l (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl⟩)
    have hclosed (p : Fin 13) (hp : p ∉ P) : ∃ l : Fin 13, p + l ∈ D ∧ ∀ q ∈ P, q + l ∉ D := by
      have h : ¬ ∀ l ∈ R, p + l ∉ D := fun hh => hp (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh⟩)
      push Not at h
      obtain ⟨l, hl, hi⟩ := h
      exact ⟨l, hi, hright l (Finset.mem_filter.mp hl).2⟩
    let px : Fin 13 → Bool := fun p => decide (p ∈ P)
    let lx : Fin 13 → Bool := fun l => decide (∀ p ∈ P, p + l ∉ D)
    have hdom : ∀ i : Fin 26, x i = true → Fin.append px lx i = true := by
      intro i
      refine Fin.addCases (motive := fun j => x j = true → Fin.append px lx j = true) ?_ ?_ i
      · intro i hi
        simpa only [Fin.append_left, px, decide_eq_true_eq] using hleft i hi
      · intro i hi
        simpa only [Fin.append_right, lx, decide_eq_true_eq] using hright i hi
    have hc := mono x (Fin.append px lx) hdom heval
    rw [List.ofFn_fin_append] at hc
    have hf : C.eval (List.ofFn px ++ List.ofFn lx) = false := hnegative P hclosed
    rw [hf] at hc
    contradiction
  · rintro ⟨u, v, huv, hu, hv⟩
    obtain ⟨p, l, rfl, rfl, hp⟩ := (hIncidence u v).mp huv
    let px : Fin 13 → Bool := fun a => decide (a = p)
    let lx : Fin 13 → Bool := fun b => decide (b = l)
    have hstart : C.eval (List.ofFn px ++ List.ofFn lx) = true := hpositive p l hp
    have hdom : ∀ i : Fin 26, Fin.append px lx i = true → x i = true := by
      intro i
      refine Fin.addCases (motive := fun j => Fin.append px lx j = true → x j = true) ?_ ?_ i
      · intro i hi
        have hi' : i = p := by simpa only [Fin.append_left, px, decide_eq_true_eq] using hi
        simpa only [hi'] using hu
      · intro i hi
        have hi' : i = l := by simpa only [Fin.append_right, lx, decide_eq_true_eq] using hi
        simpa only [hi'] using hv
    apply mono _ _ hdom
    rw [List.ofFn_fin_append]
    exact hstart
