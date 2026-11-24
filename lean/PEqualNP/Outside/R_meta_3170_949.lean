import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- A repeated pin produces a copy, which is removed by renumbering the suffix.
-- The distinct pins produce a single unordered branch.
theorem PEqualNP.Outside.R_meta_3170_949
    (root : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x3 : Fin (9 : ℕ) → Bool) => x3 (0 : Fin (9 : ℕ)) && x3 (1 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (2 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (3 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (4 : Fin (9 : ℕ)) || x3 (4 : Fin (9 : ℕ)) && x3 (0 : Fin (9 : ℕ)) || x3 (0 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (6 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (5 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (8 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ))) → (15 : ℕ) ≤ x1.size)
    (many : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∃ (x3 : Fin x1.gates.length) (x4 : Fin x1.gates.length) (x5 : Fin x1.gates.length), x3 ≠ x4 ∧ x3 ≠ x5 ∧ x4 ≠ x5 ∧ (x1.gates.get x3).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.not) → (∀ (x4 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x4)).getD (9 : ℕ) Bool.false = (x4 (0 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x5 : Fin (9 : ℕ) → Bool) => x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ))) → (16 : ℕ) ≤ x1.size)
    (normal : ∀ C : Circuit, FanInTwo C → C.size ≤ 13 →
      (∀ i j : Fin C.gates.length, (C.gates.get i).op = .not → (C.gates.get j).op = .not → i = j) →
      ∃ x : Fin 9 → Bool,
      C.eval (List.ofFn x ++ [!x 0, x 1 || x 5]) ≠ ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) :
    ∀ (x1 : List ℕ),   x1.length = (2 : ℕ) →     (∀ x3 ∈ x1, x3 = (1 : ℕ) ∨ x3 = (2 : ℕ) ∨ x3 = (3 : ℕ) ∨ x3 = (5 : ℕ) ∨ x3 = (8 : ℕ)) →       (∀ x4 ∈ x1, x4 = (1 : ℕ) ∨ x4 = (5 : ℕ)) →         ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit),           PEqualNP.MetaComplexity.FanInTwo x5 →             x5.size ≤ (13 : ℕ) →               ∃ (x8 : Fin (9 : ℕ) → Bool),                 have x9 : List Bool := List.ofFn x8 ++ [!x8 (0 : Fin (9 : ℕ))];                 x5.eval (x9 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x10 : ℕ) => x9.getD x10 Bool.false) x1)]) ≠ (x8 (0 : Fin (9 : ℕ)) && x8 (1 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (2 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (3 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (4 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ)) && x8 (0 : Fin (9 : ℕ)) || x8 (0 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (6 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (5 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (6 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (8 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ))) := by
  let redirect (k a i : ℕ) : ℕ := if i = k then a else if i < k then i else i - 1

  let redirectGate (k a : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (redirect k a)⟩

  let withoutDuplicate (k a : ℕ) (C : Circuit) : Circuit :=
    ⟨C.gates.map (redirectGate k a), redirect k a C.output⟩

  have duplicateLookup (u v : List Bool) {a : ℕ} (ha : a < u.length) (i : ℕ) :
      (u ++ v).getD (redirect u.length a i) false =
        (u ++ [u.getD a false] ++ v).getD i false := by
    by_cases hlt : i < u.length
    · simp only [redirect, ite_eq_right (Nat.ne_of_lt hlt), ite_eq_left hlt]
      rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ (by simp; omega),
        List.getD_append _ _ _ _ hlt]
    · by_cases eq : i = u.length
      · subst i
        simp only [redirect, ite_true]
        rw [List.getD_append _ _ _ _ ha, List.getD_append _ _ _ _ (by simp),
          List.getD_append_right _ _ _ _ le_rfl]
        simp
      · have gt : u.length < i := by omega
        simp only [redirect, ite_eq_right eq, ite_eq_right hlt]
        rw [List.getD_append_right _ _ _ _ (by omega : u.length ≤ i - 1),
          List.getD_append_right _ _ _ _ (by simp; omega)]
        simp only [List.length_append, List.length_singleton]
        congr 1
        omega

  have evalWithoutDuplicate (C : Circuit) (u : List Bool) {a : ℕ} (ha : a < u.length) :
      (withoutDuplicate u.length a C).eval u = C.eval (u ++ [u.getD a false]) := by
    let step (w : List Bool) (g : Gate) :=
      w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]
    have evaluation (gs : List Gate) (v : List Bool) : ∃ tail : List Bool,
        (gs.map (redirectGate u.length a)).foldl step (u ++ v) = u ++ tail ∧
        gs.foldl step (u ++ [u.getD a false] ++ v) = u ++ [u.getD a false] ++ tail := by
      induction gs generalizing v with
      | nil => exact ⟨v, rfl, rfl⟩
      | cons g gs ih =>
        let old := g.op.eval (g.inputs.map fun j => (u ++ [u.getD a false] ++ v).getD j false)
        have eq : (step (u ++ v) (redirectGate u.length a g)) = u ++ (v ++ [old]) := by
          have same : g.inputs.map ((fun j => (u ++ v).getD j false) ∘ redirect u.length a) =
              g.inputs.map (fun j => (u ++ [u.getD a false] ++ v).getD j false) :=
            List.map_congr_left (fun j _ => duplicateLookup u v ha j)
          simp only [step, redirectGate, List.map_map, List.append_assoc]
          rw [same]
        have oldStep : step (u ++ [u.getD a false] ++ v) g = u ++ [u.getD a false] ++ (v ++ [old]) := by
          dsimp only [step, old]
          rw [List.append_assoc (u ++ [u.getD a false])]
        simp only [List.map_cons, List.foldl_cons, eq, oldStep]
        exact ih (v ++ [old])
    obtain ⟨tail, newEval, oldEval⟩ := evaluation C.gates []
    simp only [List.append_nil] at newEval oldEval
    change ((C.gates.map (redirectGate u.length a)).foldl step u).getD (redirect u.length a C.output) false =
      (C.gates.foldl step (u ++ [u.getD a false])).getD C.output false
    rw [newEval, oldEval]
    exact duplicateLookup u tail ha C.output

  have noNewGates (C : Circuit) (k a : ℕ) (fan : FanInTwo C) :
      FanInTwo (withoutDuplicate k a C) ∧ (withoutDuplicate k a C).size = C.size := by
    refine ⟨?_, List.length_map _⟩
    intro g hg
    obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hg
    exact ⟨(fan h hh).1, by simpa only [redirectGate, List.length_map] using (fan h hh).2⟩
  let vertices (i : Fin 9) : Fin 9 := (![1, 0, 5, 8, 6, 2, 4, 7, 3] : Fin 9 → Fin 9) i

  let wire (i : ℕ) : ℕ :=
    if h : i < 9 then (vertices ⟨i, h⟩).val else if i = 9 then 10 else if i = 10 then 9 else i

  let target (x : Fin 9 → Bool) : Bool :=
    (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
    (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
    (x 6 && x 8) || (x 8 && x 5)

  have targetInvariant (x : Fin 9 → Bool) : target (x ∘ vertices) = target x := by
    change (x 1 && x 0 || x 0 && x 5 || x 5 && x 8 || x 8 && x 6 || x 6 && x 1 ||
      x 1 && x 2 || x 0 && x 4 || x 5 && x 7 || x 8 && x 3 || x 2 && x 7 ||
      x 4 && x 3 || x 3 && x 2) = _
    unfold target
    ac_rfl

  let orig (x : Fin 9 → Bool) : List Bool :=
    List.ofFn (x ∘ vertices) ++ [!((x ∘ vertices) 0), (x ∘ vertices) 1 || (x ∘ vertices) 5]

  let reordered (x : Fin 9 → Bool) : List Bool := List.ofFn x ++ [x 0 || x 2, !x 1]

  have lookup (x : Fin 9 → Bool) (tail : List Bool) (j : ℕ) :
      (reordered x ++ tail).getD (wire j) false = (orig x ++ tail).getD j false := by
    by_cases h : j < 11
    · interval_cases j <;> rfl
    · have hj : 11 ≤ j := by omega
      have same : wire j = j := by
        unfold wire
        rw [dite_eq_right (by omega : ¬j < 9), ite_eq_right (by omega : j ≠ 9),
          ite_eq_right (by omega : j ≠ 10)]
      have newLen : (reordered x).length = 11 := by simp [reordered]
      have oldLen : (orig x).length = 11 := by simp [orig]
      rw [same, List.getD_append_right _ _ _ _ (newLen.symm ▸ hj),
        List.getD_append_right _ _ _ _ (oldLen.symm ▸ hj), newLen, oldLen]

  let rename (C : Circuit) : Circuit :=
    ⟨C.gates.map (fun g => ⟨g.op, g.inputs.map wire⟩), wire C.output⟩

  have evaluation (C : Circuit) (x : Fin 9 → Bool) :
      (rename C).eval (reordered x) = C.eval (orig x) := by
    let step (w : List Bool) (g : Gate) :=
      w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]
    let shift : Gate → Gate := fun g => ⟨g.op, g.inputs.map wire⟩
    have h (gs : List Gate) (t : List Bool) : ∃ u : List Bool,
        (gs.map shift).foldl step (reordered x ++ t) = reordered x ++ u ∧
        gs.foldl step (orig x ++ t) = orig x ++ u := by
      induction gs generalizing t with
      | nil => exact ⟨t, rfl, rfl⟩
      | cons g gs ih =>
        have reads : g.inputs.map ((fun j => (reordered x ++ t).getD j false) ∘ wire) =
            g.inputs.map (fun j => (orig x ++ t).getD j false) :=
          List.map_congr_left (fun j _ => lookup x t j)
        let val := g.op.eval (g.inputs.map fun j => (orig x ++ t).getD j false)
        have next : step (reordered x ++ t) (shift g) = reordered x ++ (t ++ [val]) := by
          simp only [step, shift, List.map_map, List.append_assoc, reads, val]
        have old : step (orig x ++ t) g = orig x ++ (t ++ [val]) := by
          dsimp only [step, val]
          rw [List.append_assoc]
        simp only [List.map_cons, List.foldl_cons, next, old]
        exact ih (t ++ [val])
    obtain ⟨u, hu, hv⟩ := h C.gates []
    simp only [List.append_nil] at hu hv
    change ((C.gates.map shift).foldl step (reordered x)).getD (wire C.output) false =
      (C.gates.foldl step (orig x)).getD C.output false
    rw [hu, hv]
    exact lookup x u C.output

  have excludeTwoNots
      (lower : ∀ D : Circuit, FanInTwo D →
        (∃ i j k : Fin D.gates.length, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
          (D.gates.get i).op = .not ∧ (D.gates.get j).op = .not ∧ (D.gates.get k).op = .not) →
        (∀ x : Fin 9 → Bool, (D.wires (List.ofFn x)).getD 9 false = (x 0 || x 2)) →
        circuitFun 9 D = target → 16 ≤ D.size)
      (C : Circuit) (fan : FanInTwo C) (bound : C.size ≤ 13)
      (i j : Fin C.gates.length) (diff : i ≠ j)
      (iNot : (C.gates.get i).op = .not) (jNot : (C.gates.get j).op = .not) :
      ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [!x 0, x 1 || x 5]) ≠ target x := by
    let g : Gate := ⟨.or, [0, 2]⟩
    let n : Gate := ⟨.not, [1]⟩
    let D : Circuit := ⟨g :: n :: (rename C).gates, (rename C).output⟩
    have dfan : FanInTwo D := by
      intro k hk
      change k ∈ g :: n :: (rename C).gates at hk
      rcases List.mem_cons.mp hk with rfl | hk
      · simp [g]
      rcases List.mem_cons.mp hk with rfl | hk
      · simp [n]
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hk
      exact ⟨(fan a ha).1, by simpa only [List.length_map] using (fan a ha).2⟩
    have dlen : D.gates.length = C.gates.length + 2 := by simp [D, rename]
    let i' : Fin D.gates.length := ⟨i.val + 2, by rw [dlen]; omega⟩
    let j' : Fin D.gates.length := ⟨j.val + 2, by rw [dlen]; omega⟩
    let n' : Fin D.gates.length := ⟨1, by rw [dlen]; omega⟩
    have dfanNeg : ∃ a b c : Fin D.gates.length, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
        (D.gates.get a).op = .not ∧ (D.gates.get b).op = .not ∧ (D.gates.get c).op = .not := by
      have distinct := Fin.val_injective.ne diff
      refine ⟨n', i', j', ?_, ?_, ?_, rfl, ?_, ?_⟩
      · intro h
        have v := congrArg Fin.val h
        change 1 = i.val + 2 at v
        omega
      · intro h
        have v := congrArg Fin.val h
        change 1 = j.val + 2 at v
        omega
      · exact fun h => by have v := congrArg Fin.val h; dsimp [i', j'] at v; omega
      · simpa [D, rename, i', Nat.add_comm] using iNot
      · simpa [D, rename, j', Nat.add_comm] using jNot
    let step (w : List Bool) (a : Gate) :=
      w ++ [a.op.eval (a.inputs.map fun key => w.getD key false)]
    have executedPrefix (x : Fin 9 → Bool) : step (step (List.ofFn x) g) n = reordered x := by
      change (List.ofFn x ++ [x 0 || (x 2 || false)]) ++ [!x 1] = reordered x
      simp [reordered, List.append_assoc]
    have wirePrefix (x : Fin 9 → Bool) : D.wires (List.ofFn x) = (rename C).wires (reordered x) := by
      change (g :: n :: (rename C).gates).foldl step (List.ofFn x) =
        (rename C).gates.foldl step (reordered x)
      rw [List.foldl_cons, List.foldl_cons, executedPrefix]
    have preserves (gs : List Gate) (w : List Bool) (h : 9 < w.length) :
        (gs.foldl step w).getD 9 false = w.getD 9 false := by
      induction gs generalizing w with
      | nil => rfl
      | cons a gs ih =>
        rw [List.foldl_cons, ih]
        · exact List.getD_append _ _ _ _ h
        · simp [step]; omega
    have dfirst (x : Fin 9 → Bool) : (D.wires (List.ofFn x)).getD 9 false = (x 0 || x 2) := by
      rw [wirePrefix]
      change ((rename C).gates.foldl step (reordered x)).getD 9 false = _
      rw [preserves _ _ (by simp [reordered])]
      rfl
    by_contra! agree
    have dfun : circuitFun 9 D = target := by
      funext x
      change (D.wires (List.ofFn x)).getD D.output false = target x
      rw [wirePrefix]
      change (rename C).eval (reordered x) = target x
      rw [evaluation, ← targetInvariant x]
      exact agree (x ∘ vertices)
    have large := lower D dfan dfanNeg dfirst dfun
    change 16 ≤ D.gates.length at large
    rw [dlen] at large
    change C.gates.length ≤ 13 at bound
    omega

  intro pins hlen _ valid C fan size
  have shape : ∃ a b, pins = [a, b] := by
    rcases pins with _ | ⟨a, _ | ⟨b, _ | ⟨c, tail⟩⟩⟩
    · simp at hlen
    · simp at hlen
    · exact ⟨a, b, rfl⟩
    · simp at hlen
  obtain ⟨a, b, rfl⟩ := shape
  have va := valid a (by simp)
  have vb := valid b (by simp)
  let base (x : Fin 9 → Bool) := List.ofFn x ++ [!x 0]
  have baseLen (x : Fin 9 → Bool) : (base x).length = 10 := by simp [base]
  have readBase (x : Fin 9 → Bool) (i : Fin 9) : (base x).getD i.val false = x i := by
    rw [show base x = List.ofFn x ++ [!x 0] from rfl,
      List.getD_append _ _ _ _ (by simpa only [List.length_ofFn] using i.isLt),
      List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left i.isLt]
    rfl
  let edge (x : Fin 9 → Bool) := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
  have repeated (a : ℕ) (ha : a < 9) : ∃ x : Fin 9 → Bool,
      C.eval (base x ++ [GateOp.or.eval ([a, a].map fun j => (base x).getD j false)]) ≠ edge x := by
    let D := withoutDuplicate 10 a C
    let first : Gate := ⟨.not, [0]⟩
    let prefixed : Circuit := ⟨first :: D.gates, D.output⟩
    obtain ⟨fanD, sizeD⟩ := noNewGates C 10 a fan
    have fanP : FanInTwo prefixed := by
      intro g hg
      change g ∈ first :: D.gates at hg
      rcases List.mem_cons.mp hg with rfl | hg
      · simp [first]
      · exact fanD g hg
    have sizeP : prefixed.size ≤ 14 := by
      change D.gates.length + 1 ≤ 14
      change D.gates.length = C.size at sizeD
      omega
    have evalP (x : Fin 9 → Bool) : prefixed.eval (List.ofFn x) = D.eval (base x) := by
      unfold Circuit.eval Circuit.wires prefixed
      rw [List.foldl_cons]
      have notZero : first.op.eval (first.inputs.map fun j => (List.ofFn x).getD j false) = !x 0 := by
        change (!((List.ofFn x).getD 0 false)) = (!x 0)
        rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left (by decide : 0 < 9)]
        rfl
      rw [notZero]
    by_contra! agreement
    have computed : circuitFun 9 prefixed = edge := by
      funext x
      change prefixed.eval (List.ofFn x) = edge x
      rw [evalP]
      have lookup : a < (base x).length := by rw [baseLen]; omega
      have rename := evalWithoutDuplicate C (base x) lookup
      rw [baseLen] at rename
      change D.eval (base x) = _ at rename
      rw [rename]
      have h := agreement x
      change C.eval (base x ++ [((base x).getD a false || ((base x).getD a false || false))]) = edge x at h
      simpa only [Bool.or_false, Bool.or_self] using h
    have impossible := root prefixed fanP computed
    omega
  have distinct : ∃ x : Fin 9 → Bool,
      C.eval (base x ++ [GateOp.or.eval ([1, 5].map fun j => (base x).getD j false)]) ≠ edge x := by
    have tested : ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [!x 0, x 1 || x 5]) ≠ edge x := by
      by_cases two : ∃ i j : Fin C.gates.length, i ≠ j ∧
          (C.gates.get i).op = .not ∧ (C.gates.get j).op = .not
      · obtain ⟨i, j, diff, hi, hj⟩ := two
        exact excludeTwoNots many C fan size i j diff hi hj
      · exact normal C fan size (fun i j hi hj => by
          by_contra diff
          exact two ⟨i, j, diff, hi, hj⟩)
    obtain ⟨x, hx⟩ := tested
    refine ⟨x, ?_⟩
    change C.eval (base x ++ [GateOp.or.eval ([(base x).getD 1 false, (base x).getD 5 false])]) ≠ edge x
    rw [show (base x).getD 1 false = x 1 from readBase x 1,
      show (base x).getD 5 false = x 5 from readBase x 5]
    change C.eval (base x ++ [x 1 || (x 5 || false)]) ≠ edge x
    simp only [base, Bool.or_false, List.append_assoc, List.singleton_append]
    exact hx
  rcases va with rfl | rfl <;> rcases vb with rfl | rfl
  · exact repeated 1 (by decide)
  · exact distinct
  · obtain ⟨x, hx⟩ := distinct
    refine ⟨x, ?_⟩
    change C.eval (base x ++ [((base x).getD 5 false || ((base x).getD 1 false || false))]) ≠ edge x
    change C.eval (base x ++ [((base x).getD 1 false || ((base x).getD 5 false || false))]) ≠ edge x at hx
    simp only [Bool.or_false] at hx ⊢
    rw [Bool.or_comm ((base x).getD 5 false) ((base x).getD 1 false)]
    exact hx
  · exact repeated 5 (by decide)
