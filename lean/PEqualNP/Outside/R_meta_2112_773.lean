import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover

theorem PEqualNP.Outside.R_meta_2112_773
    (blocked : ∀ (n : ℕ) (C : Circuit) (v u : Fin n), C.output ≠ v.val →
      (∀ g ∈ C.gates, v.val ∈ g.inputs → g.op = GateOp.and ∧ u.val ∈ g.inputs) →
      ∀ x y : Fin n → Bool, (∀ a, a ≠ v → x a = y a) →
        x u = false → y u = false → C.eval (List.ofFn x) = C.eval (List.ofFn y))
    (laterNot : ∀ (n : ℕ) (C : Circuit) (v : Fin n) (j : ℕ),
      FanInTwo C → ReadsBack n C → j < C.gates.length → gateAt C j = ⟨GateOp.not, [v.val]⟩ →
      (∀ k < C.gates.length, v.val ∈ (gateAt C k).inputs → k = j) → C.output ≠ v.val →
      ∀ x y : Fin n → Bool, (∀ u ≠ v, x u = y u) →
        x v = false → y v = true → circuitFun n C x = false → circuitFun n C y = true →
        ∃ k < C.gates.length, j < k ∧ (gateAt C k).op = GateOp.not)
    (remaining :
      let edges : List (Fin 9 × Fin 9) := [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)]
      let R := fun (C : Circuit) (v : Fin 9) => {j : Fin C.size | v.val ∈ (C.gates.get j).inputs}
      ∀ C : Circuit, IsMinimalCircuit 9 C → C.size ≤ 15 →
      circuitFun 9 C = (fun x => edges.any fun e => x e.1 && x e.2) → ReadsBack 9 C →
      (∀ j : Fin C.size, (C.gates.get j).inputs.Nodup ∧
        ((C.gates.get j).op = GateOp.not ∧ (C.gates.get j).inputs.length = 1 ∨
        (C.gates.get j).op ≠ GateOp.not ∧ (C.gates.get j).inputs.length = 2)) →
      (∀ v ∈ ([4,6,7] : List (Fin 9)), (R C v).Nonempty ∧ (R C v).ncard ≤ 2 ∧
        ((R C v).ncard = 2 → ∀ j ∈ R C v, (C.gates.get j).op = GateOp.or)) →
      (∃ v ∈ ([4,6,7] : List (Fin 9)), ∃ j ∈ R C v,
        ((C.gates.get j).op = GateOp.and ∧ ∃ w ∈ (C.gates.get j).inputs, 9 ≤ w) ∨
        ((C.gates.get j).op = GateOp.not ∧ ∃ k : Fin C.size, j < k ∧ (C.gates.get k).op = GateOp.not)) → False) :
  have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)); have x2 : (x2 : PEqualNP.CircuitLowerBounds.Circuit) → Fin (9 : ℕ) → Finset (Fin x2.size) := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Fin (9 : ℕ)) => {x4 : Fin x2.size | ↑x3 ∈ (x2.gates.get x4).inputs}; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) =>   PEqualNP.MetaComplexity.IsMinimalCircuit (9 : ℕ) x3 ∧     x3.size ≤ (15 : ℕ) ∧       PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x3 = x1 ∧         (∀ (x4 : Fin x3.size),             have x5 : PEqualNP.CircuitLowerBounds.Gate := x3.gates.get x4;             (∀ x6 ∈ x5.inputs, x6 < (9 : ℕ) + ↑x4) ∧ x5.inputs.Nodup ∧ (x5.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ x5.inputs.length = (1 : ℕ) ∨ x5.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ x5.inputs.length = (2 : ℕ))) ∧           ∀ x4 ∈ [(4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))], (x2 x3 x4).Nonempty ∧ (x2 x3 x4).card ≤ (2 : ℕ) ∧ ((x2 x3 x4).card = (2 : ℕ) → ∀ x7 ∈ x2 x3 x4, (x3.gates.get x7).op = PEqualNP.CircuitLowerBounds.GateOp.or); ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), x3 x4 → (∃ x6 ∈ [(4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))], ∃ x7 ∈ x2 x4 x6, (x4.gates.get x7).op ≠ PEqualNP.CircuitLowerBounds.GateOp.or) → False := by
  intro postedTarget postedReaders postedValid C valid witness
  classical
  let edges : List (Fin 9 × Fin 9) := [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)]
  let target := fun x : Fin 9 → Bool => edges.any fun e => x e.1 && x e.2
  let readers := postedReaders C
  let R : Fin 9 → Set (Fin C.size) := fun v => {j | v.val ∈ (C.gates.get j).inputs}
  obtain ⟨minimal, size, correct, normal, special⟩ := valid
  have correctTarget : circuitFun 9 C = target := by
    rw [correct]
    funext x
    simp [postedTarget, target, edges, Bool.or_assoc]
  obtain ⟨v, hv, j, hj, notOr⟩ := witness
  have hjR : j ∈ readers v := hj
  have inputJ : v.val ∈ (C.gates.get j).inputs := (Finset.mem_filter.mp hjR).2
  have bounds := special v hv
  change (readers v).Nonempty ∧ (readers v).card ≤ 2 ∧
    ((readers v).card = 2 → ∀ j ∈ readers v, (C.gates.get j).op = GateOp.or) at bounds
  have single : (readers v).card ≤ 1 := by
    by_contra h
    have two : (readers v).card = 2 := by omega
    exact notOr (bounds.2.2 two j hjR)
  have sole (k : Fin C.size) (hk : v.val ∈ (C.gates.get k).inputs) : k = j := by
    have mem : k ∈ readers v := Finset.mem_filter.mpr ⟨Finset.mem_univ k, hk⟩
    exact Finset.card_le_one.mp single k mem j hjR
  have atEq (i : Fin C.size) : gateAt C i.val = C.gates.get i := by
    have hlt : i.val < C.gates.length := i.isLt
    change C.gates.getD i.val ⟨GateOp.or, []⟩ = C.gates.get i
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
    rfl
  have back : ReadsBack 9 C := by
    intro k hk w hw
    let i : Fin C.size := ⟨k, hk⟩
    have he : gateAt C k = C.gates.get i := atEq i
    exact (normal i).1 w (he ▸ hw)
  have out : C.output ≠ v.val := by
    intro he
    let x : Fin 9 → Bool := fun i => decide (i = v)
    have singleFalse : ∀ z : Fin 9, target (fun i => decide (i = z)) = false := by decide
    have value (gs : List Gate) (w : List Bool) (hw : v.val < w.length) :
        (Circuit.mk gs v.val).eval w = w.getD v.val false := by
      induction gs generalizing w with
      | nil => rfl
      | cons g gs ih =>
        let next := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
        change (Circuit.mk gs v.val).eval next = w.getD v.val false
        rw [ih next (by simp [next]; omega)]
        exact List.getD_append _ _ _ _ hw
    have evalTrue : circuitFun 9 C x = true := by
      change (Circuit.mk C.gates C.output).eval (List.ofFn x) = true
      rw [he, value C.gates _ (by simpa using v.isLt)]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using v.isLt)]
      change (List.ofFn x)[v.val] = true
      rw [List.getElem_ofFn]
      simp [x]
    rw [correctTarget, singleFalse v] at evalTrue
    contradiction
  have sensitivity : ∀ (u : Fin 9), v ≠ u →
      ∃ x y : Fin 9 → Bool, (∀ a, a ≠ v → x a = y a) ∧
        x v = false ∧ y v = true ∧ x u = false ∧ y u = false ∧
        circuitFun 9 C x = false ∧ circuitFun 9 C y = true := by
    have examples : ∀ v ∈ ([4,6,7] : List (Fin 9)), ∀ u : Fin 9, v ≠ u →
        ∃ w : Fin 9, w ≠ v ∧ w ≠ u ∧
          target (fun i => decide (i = w)) = false ∧
          target (fun i => decide (i = w ∨ i = v)) = true := by decide
    intro u hvu
    obtain ⟨w, hwv, hwu, hx, hy⟩ := examples v hv u hvu
    refine ⟨fun i => decide (i = w), fun i => decide (i = w ∨ i = v), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro a hav
      simp [hav]
    · simp [Ne.symm hwv]
    · simp
    · simp [Ne.symm hwu]
    · simp [Ne.symm hwu, Ne.symm hvu]
    · simpa [correctTarget] using hx
    · simpa [correctTarget] using hy
  apply remaining C minimal size correctTarget back
  · exact fun i => (normal i).2
  · intro u hu
    change (R u).Nonempty ∧ (R u).ncard ≤ 2 ∧
      ((R u).ncard = 2 → ∀ j ∈ R u, (C.gates.get j).op = GateOp.or)
    have coe : R u = ((readers u : Finset (Fin C.size)) : Set (Fin C.size)) := by
      ext i
      simp [R, readers, postedReaders]
    have hs := special u hu
    change (readers u).Nonempty ∧ (readers u).card ≤ 2 ∧
      ((readers u).card = 2 → ∀ i ∈ readers u, (C.gates.get i).op = GateOp.or) at hs
    rw [coe, Set.ncard_coe_finset]
    exact ⟨(Finset.coe_nonempty.mpr hs.1), hs.2⟩
  · refine ⟨v, hv, j, inputJ, ?_⟩
    have ops := (minimal.1 (C.gates.get j) (List.get_mem _ _)).1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ops
    rcases ops with andOp | orOp | notOp
    · left
      refine ⟨andOp, ?_⟩
      by_contra allRaw
      have len : (C.gates.get j).inputs.length = 2 := by
        rcases (normal j).2.2 with ⟨h, _⟩ | ⟨_, h⟩
        · rw [andOp] at h
          contradiction
        · exact h
      obtain ⟨a, b, ab⟩ := List.length_eq_two.mp len
      have ha : a < 9 := by
        by_contra hn
        exact allRaw ⟨a, by simp [ab], by omega⟩
      have hb : b < 9 := by
        by_contra hn
        exact allRaw ⟨b, by simp [ab], by omega⟩
      have distinct : a ≠ b := by simpa [ab] using (normal j).2.1
      have vSide : v.val = a ∨ v.val = b := by simpa [ab] using inputJ
      have neighbor : ∃ u : Fin 9, v ≠ u ∧ u.val ∈ (C.gates.get j).inputs := by
        rcases vSide with h | h
        · exact ⟨⟨b, hb⟩, fun eq => distinct (h.symm.trans (congrArg Fin.val eq)), by simp [ab]⟩
        · exact ⟨⟨a, ha⟩, fun eq => distinct ((congrArg Fin.val eq).symm.trans h), by simp [ab]⟩
      obtain ⟨u, huv, hu⟩ := neighbor
      obtain ⟨x, y, agree, _, _, hxu, hyu, fx, fy⟩ := sensitivity u huv
      have same := blocked 9 C v u out (by
        intro g hg hv
        obtain ⟨i, rfl⟩ := List.get_of_mem hg
        rw [sole i hv]
        exact ⟨andOp, hu⟩) x y agree hxu hyu
      change circuitFun 9 C x = circuitFun 9 C y at same
      rw [fx, fy] at same
      contradiction
    · exact False.elim (notOr orOp)
    · right
      refine ⟨notOp, ?_⟩
      have len : (C.gates.get j).inputs.length = 1 := by
        rcases (normal j).2.2 with ⟨_, h⟩ | ⟨h, _⟩
        · exact h
        · exact (h notOp).elim
      obtain ⟨a, aEq⟩ := List.length_eq_one_iff.mp len
      have aVal : a = v.val := by simpa [aEq, eq_comm] using inputJ
      have notGate : gateAt C j.val = ⟨GateOp.not, [v.val]⟩ := by
        rw [atEq]
        have inEq : (C.gates.get j).inputs = [v.val] := by rw [aEq, aVal]
        calc
          C.gates.get j = ⟨(C.gates.get j).op, (C.gates.get j).inputs⟩ := rfl
          _ = ⟨GateOp.not, [v.val]⟩ := by rw [notOp, inEq]
      have unique (k : ℕ) (hk : k < C.gates.length)
          (hkv : v.val ∈ (gateAt C k).inputs) : k = j.val := by
        let i : Fin C.size := ⟨k, hk⟩
        have he : gateAt C k = C.gates.get i := atEq i
        exact congrArg Fin.val (sole i (he ▸ hkv))
      have nonzero : v ≠ 0 := by
        intro he
        rw [he] at hv
        simpa using hv
      obtain ⟨x, y, agree, xv, yv, _, _, fx, fy⟩ := sensitivity 0 nonzero
      obtain ⟨k, hk, jk, op⟩ := laterNot 9 C v j.val minimal.1 back j.isLt notGate unique out x y agree xv yv fx fy
      let i : Fin C.size := ⟨k, hk⟩
      have he : gateAt C k = C.gates.get i := atEq i
      exact ⟨i, jk, he ▸ op⟩
