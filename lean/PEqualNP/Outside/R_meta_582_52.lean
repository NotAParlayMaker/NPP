import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
theorem PEqualNP.Outside.R_meta_582_52
    (residual :
      let edge : Fin 14 → Fin 14 → Prop := fun u v =>
        (([1408,8832,12544,6272,11264,5632,2816] : List ℕ).getD u.val 0).testBit v.val = true
      ∃ (D : Circuit) (q : ℕ), Monotone2 D ∧ D.size ≤ 24 ∧ D.output < 14 + D.size ∧ q < 14 + D.size ∧
        let wire := fun x : Fin 14 → Bool => (D.wires (List.ofFn x)).getD q false
        (∀ u v, edge u v → let x := pairInput u v
          D.eval (List.ofFn x) = true ∨ (x 0 = true ∧ wire x = true)) ∧
        ∀ x : Fin 14 → Bool,
          Maximal (fun y : Fin 14 → Bool => ¬ (∃ u v : Fin 14, edge u v ∧ y u = true ∧ y v = true)) x →
          D.eval (List.ofFn x) = false ∧ (x 0 = true → wire x = false))
    (append : ∀ (n : ℕ) (D : Circuit) (p : Fin n) (q : ℕ),
      Monotone2 D → D.output < n + D.size → q < n + D.size →
      ∃ C : Circuit, Monotone2 C ∧ C.size ≤ D.size + 2 ∧ ∀ x : Fin n → Bool,
        C.eval (List.ofFn x) = (D.eval (List.ofFn x) ||
          (x p && (D.wires (List.ofFn x)).getD q false)))
    : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 26 ∧ (∀ x : Fin 14 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 14, (u.val, v.val) ∈ ([(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) := by
  classical
  let stepW : List Bool → Gate → List Bool :=
    fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have getD_app_lt : ∀ (w t : List Bool) (i : ℕ), i < w.length →
      (w ++ t).getD i false = w.getD i false := by
    intro w t i hi
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have getD_app_self : ∀ (w : List Bool) (b : Bool),
      (w ++ [b]).getD w.length false = b := by
    intro w b
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (le_refl w.length)]
    simp
  have getD_ge : ∀ (w : List Bool) (i : ℕ), w.length ≤ i → w.getD i false = false := by
    intro w i hi
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi, Option.getD_none]
  have foldl_getD_lt : ∀ (gs : List Gate) (w : List Bool) (i : ℕ), i < w.length →
      (gs.foldl stepW w).getD i false = w.getD i false := by
    intro gs
    induction gs with
    | nil => intro w i _; rfl
    | cons g0 gs ih =>
      intro w i hi
      rw [List.foldl_cons]
      have hlt : i < (stepW w g0).length := by
        change i < (w ++ [_]).length
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      rw [ih (stepW w g0) i hlt]
      exact getD_app_lt w _ i hi
  have foldl_gate : ∀ (gs : List Gate) (w : List Bool) (j : ℕ) (g : Gate),
      gs[j]? = some g →
      (gs.foldl stepW w).getD (w.length + j) false =
        g.op.eval (g.inputs.map fun i =>
          if i < w.length + j then (gs.foldl stepW w).getD i false else false) := by
    intro gs
    induction gs with
    | nil => intro _ _ _ h; simp at h
    | cons g0 gs ih =>
      intro w j g hj
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
        subst hj
        rw [Nat.add_zero, List.foldl_cons]
        have hlt : w.length < (stepW w g0).length := by
          change w.length < (w ++ [_]).length
          simp only [List.length_append, List.length_cons, List.length_nil]
          omega
        rw [foldl_getD_lt gs (stepW w g0) w.length hlt]
        change (w ++ [g0.op.eval (g0.inputs.map fun i => w.getD i false)]).getD w.length false = _
        rw [getD_app_self w _]
        congr 1
        apply List.map_congr_left
        intro i _
        by_cases hi : i < w.length
        · have hilt : i < (stepW w g0).length := by
            change i < (w ++ [_]).length
            simp only [List.length_append, List.length_cons, List.length_nil]
            omega
          simp only [hi, ↓reduceIte, foldl_getD_lt gs (stepW w g0) i hilt]
          exact (getD_app_lt w _ i hi).symm
        · simp only [hi, ↓reduceIte]
          exact getD_ge w i (Nat.le_of_not_lt hi)
      | succ j' =>
        simp only [List.getElem?_cons_succ] at hj
        have hlen : (stepW w g0).length + j' = w.length + (j' + 1) := by
          change (w ++ [_]).length + j' = w.length + (j' + 1)
          simp only [List.length_append, List.length_cons, List.length_nil]
          omega
        rw [List.foldl_cons, ← hlen]
        exact ih (stepW w g0) j' g hj
  have wires_gate (n : ℕ) (C : Circuit) : ∀ (x : Fin n → Bool) (j : ℕ) (g : Gate),
      C.gates[j]? = some g →
      (C.wires (List.ofFn x)).getD (n + j) false =
        g.op.eval (g.inputs.map fun i =>
          if i < n + j then (C.wires (List.ofFn x)).getD i false else false) := by
    intro x j g hj
    have h := foldl_gate C.gates (List.ofFn x) j g hj
    have hlen : (List.ofFn x).length = n := List.length_ofFn
    rw [hlen] at h
    exact h
  have wires_inp (n : ℕ) (C : Circuit) : ∀ (x : Fin n → Bool) (w : ℕ) (hw : w < n),
      (C.wires (List.ofFn x)).getD w false = x ⟨w, hw⟩ := by
    intro x w hw
    have h := foldl_getD_lt C.gates (List.ofFn x) w (by rw [List.length_ofFn]; exact hw)
    change (C.gates.foldl stepW (List.ofFn x)).getD w false = x ⟨w, hw⟩
    rw [h]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, ↓reduceDIte, Option.getD_some]

  have wires_len (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
      (C.wires (List.ofFn x)).length = n + C.gates.length := by
    have hfold (gs : List Gate) : ∀ w, (gs.foldl stepW w).length = w.length + gs.length := by
      induction gs with
      | nil => intro; simp
      | cons g gs ih =>
        intro w
        rw [List.foldl_cons, ih]
        simp only [stepW,List.length_append,List.length_cons,List.length_nil]
        omega
    change (C.gates.foldl stepW (List.ofFn x)).length = _
    rw [hfold, List.length_ofFn]

  have gate_read (C : Circuit) (j : ℕ) (g : Gate) (h : C.gates[j]? = some g) :
      gateAt C j = g := by
    change C.gates.getD j ⟨.or,[]⟩ = g
    rw [List.getD_eq_getElem?_getD,h]
    rfl

  have and_inputs (n : ℕ) (C : Circuit) (x : Fin n → Bool) (j : ℕ) (g : Gate)
      (hg : C.gates[j]? = some g) (hop : g.op = .and) :
      gateVal n C j x = true ↔
        ∀ w ∈ g.inputs, w < n+j ∧ (C.wires (List.ofFn x)).getD w false = true := by
    unfold gateVal
    rw [wires_gate n C _ _ _ hg, hop]
    change (g.inputs.map _).all id = true ↔ _
    simp only [List.all_eq_true,List.mem_map]
    constructor
    · intro h k hk
      by_cases e : k < n+j
      · exact ⟨e, by simpa only [e, ↓reduceIte,id_eq] using h _ ⟨k,hk,rfl⟩⟩
      · have bad := h _ ⟨k,hk,rfl⟩
        simp [e] at bad
    · rintro h _ ⟨k, hk, rfl⟩
      rcases h k hk with ⟨e,he⟩
      simpa only [e, ↓reduceIte,id_eq] using he

  have or_inputs (n : ℕ) (C : Circuit) (x : Fin n → Bool) (j : ℕ) (g : Gate)
      (hg : C.gates[j]? = some g) (hop : g.op = .or) :
      gateVal n C j x = true ↔
        ∃ w ∈ g.inputs, w < n+j ∧ (C.wires (List.ofFn x)).getD w false = true := by
    unfold gateVal
    rw [wires_gate n C _ _ _ hg, hop]
    change (g.inputs.map _).any id = true ↔ _
    rw [List.any_eq_true]
    constructor
    · rintro ⟨_, h, hp⟩
      obtain ⟨k,hk,rfl⟩ := List.mem_map.mp h
      by_cases e : k < n+j
      · exact ⟨k,hk,e,by simpa only [e, ↓reduceIte,id_eq] using hp⟩
      · simp [e] at hp
    · rintro ⟨k,hk,e,he⟩
      refine ⟨_,List.mem_map.mpr ⟨k,hk,rfl⟩,?_⟩
      simpa only [e, ↓reduceIte,id_eq] using he


  have active_bound (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ)
      (ht : (C.wires (List.ofFn x)).getD w false = true) : w < n + C.gates.length := by
    by_contra! he
    have hge : (C.wires (List.ofFn x)).length ≤ w := by rwa [wires_len n C x]
    rw [List.getD_eq_default _ _ hge] at ht
    contradiction

  have wire_mono (n : ℕ) (C : Circuit) (mono : Monotone2 C) (x y : Fin n → Bool)
      (inc : ∀ a, x a = true → y a = true) :
      ∀ w, (C.wires (List.ofFn x)).getD w false = true →
        (C.wires (List.ofFn y)).getD w false = true := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro ht
      by_cases hw : w < n
      · rw [wires_inp n C y w hw]
        apply inc
        simpa only [wires_inp n C x w hw] using ht
      · have bound := active_bound n C x w ht
        let j := w-n
        have jlt : j < C.gates.length := by dsimp [j]; omega
        have row : w = n+j := by dsimp [j]; omega
        let g := C.gates[j]
        have hg : C.gates[j]? = some g := List.getElem?_eq_getElem jlt
        have mem : g ∈ C.gates := List.getElem_mem jlt
        rw [row] at ht ⊢
        change gateVal n C j x = true at ht
        change gateVal n C j y = true
        rcases (mono g mem).1 with e | e
        · apply (and_inputs n C y j g hg e).mpr
          intro a ha
          obtain ⟨early,hit⟩ := (and_inputs n C x j g hg e).mp ht a ha
          exact ⟨early,ih a (row ▸ early) hit⟩
        · obtain ⟨a,ha,early,hit⟩ := (or_inputs n C x j g hg e).mp ht
          exact (or_inputs n C y j g hg e).mpr ⟨a,ha,early,ih a (row ▸ early) hit⟩

  let edge : Fin 14 → Fin 14 → Prop := fun u v =>
    (([1408,8832,12544,6272,11264,5632,2816] : List ℕ).getD u.val 0).testBit v.val = true
  let P := fun x : Fin 14 → Bool => ∃ u v : Fin 14, edge u v ∧ x u = true ∧ x v = true
  have edgeSpec : ∀ u v : Fin 14, edge u v ↔
    (u.val,v.val) ∈ ([(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13),
      (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12),
      (6, 8), (6, 9), (6, 11)] : List (ℕ × ℕ)) := by decide +kernel
  obtain ⟨D,q,mono,size,outValid,qValid,positive,negative⟩ := residual
  obtain ⟨C,legal,budget,outs⟩ := append 14 D (0 : Fin 14) q mono outValid qValid
  have on_edges (u v : Fin 14) (h : edge u v) :
      C.eval (List.ofFn (pairInput u v)) = true := by
    have ok := positive u v h
    rw [outs]
    rcases ok with got | ⟨guard,port⟩
    · simp only [got,Bool.true_or]
    · simp only [guard,port,Bool.true_and,Bool.or_true]
  have rejects (x : Fin 14 → Bool) (no : Maximal (fun y => ¬ P y) x) : C.eval (List.ofFn x) = false := by
    have both := negative x no
    rw [outs,both.1]
    cases guard : x 0
    · simp only [Bool.false_and,Bool.false_or]
    · simp only [both.2 guard,Bool.true_and,Bool.false_or]
  refine ⟨C,legal,by omega,?_⟩
  intro x
  suffices eval : C.eval (List.ofFn x) = true ↔ P x by
    simpa only [P,edgeSpec] using eval
  constructor
  · intro hit
    by_contra no
    obtain ⟨y, incl, maximal⟩ := Finite.exists_le_maximal (p := fun z => ¬ P z) no
    have pinMono (i : Fin 14) (hi : x i = true) : y i = true := by
      have iy := incl i
      cases e : y i
      · rw [hi,e] at iy
        exact False.elim ((by decide : ¬ ((true : Bool) ≤ false)) iy)
      · rfl
    have hitY := wire_mono 14 C legal x y pinMono C.output hit
    change C.eval (List.ofFn y) = true at hitY
    rw [rejects y maximal] at hitY
    contradiction
  · rintro ⟨u,v,h,hu,hv⟩
    change (C.wires (List.ofFn x)).getD C.output false = true
    apply wire_mono 14 C legal (pairInput u v) x _ C.output (on_edges u v h)
    intro i yes
    have pin : i = u ∨ i = v := of_decide_eq_true yes
    rcases pin with rfl | rfl <;> assumption
