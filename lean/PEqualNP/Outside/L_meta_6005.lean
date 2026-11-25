import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6005_aux

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.CleanedNonEdge
open PEqualNP.TopForm

private def targetFun (x : Fin 9 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 ||
  x 5 && x 7 || x 6 && x 8 || x 8 && x 5

private theorem single_false :
    ∀ v : Fin 9, v ∈ [(4 : Fin 9), (6 : Fin 9), (7 : Fin 9)] →
      targetFun (fun i => decide (i = v)) = false := by
  decide +kernel

private theorem exists_sep :
    ∀ v u : Fin 9, v ∈ [(4 : Fin 9), (6 : Fin 9), (7 : Fin 9)] → u ≠ v →
      ∃ m : Fin 512,
        m.val.testBit u.val = true ∧
        m.val.testBit v.val = false ∧
        targetFun (fun i => m.val.testBit i.val) = false ∧
        targetFun (fun i => if i = v then true else m.val.testBit i.val) = true := by
  decide +kernel

private def isOrOp : GateOp → Bool
  | GateOp.or => true
  | _ => false

private theorem isOrOp_iff (op : GateOp) : isOrOp op = true ↔ op = GateOp.or := by
  cases op <;> simp [isOrOp]

private theorem getD_append_left {α : Type} :
    ∀ (xs ys : List α) (d : α) (i : ℕ), i < xs.length → (xs ++ ys).getD i d = xs.getD i d
  | [], _, _, _, hi => by simp at hi
  | _ :: _, _, _, 0, _ => rfl
  | _ :: xs, ys, d, i + 1, hi => getD_append_left xs ys d i (by simpa using hi)

private theorem getD_append_len {α : Type} :
    ∀ (xs : List α) (v d : α), (xs ++ [v]).getD xs.length d = v
  | [], _, _ => rfl
  | _ :: xs, v, d => getD_append_len xs v d

private theorem getD_ge_len {α : Type} :
    ∀ (xs : List α) (d : α) (i : ℕ), xs.length ≤ i → xs.getD i d = d
  | [], _, 0, _ => rfl
  | [], _, _ + 1, _ => rfl
  | _ :: _, _, 0, hi => by simp at hi
  | _ :: xs, d, i + 1, hi => getD_ge_len xs d i (by simpa using hi)

private theorem getD_eq_get {α : Type} :
    ∀ (xs : List α) (d : α) (k : Fin xs.length), xs.getD k.val d = xs.get k
  | [], _, k => Fin.elim0 k
  | _ :: _, _, ⟨0, _⟩ => rfl
  | _ :: xs, d, ⟨i + 1, hi⟩ => getD_eq_get xs d ⟨i, Nat.lt_of_succ_lt_succ hi⟩

private theorem getD_ofFn :
    ∀ (n : ℕ) (f : Fin n → Bool) (i : ℕ) (hi : i < n),
      (List.ofFn f).getD i false = f ⟨i, hi⟩
  | 0, _, _, hi => by omega
  | n + 1, f, 0, _ => by rw [List.ofFn_succ]; rfl
  | n + 1, f, i + 1, hi => by
    rw [List.ofFn_succ]
    exact getD_ofFn n (fun j => f j.succ) i (by omega)

private def gateStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem foldl_gateStep_len (z : List Bool) (gs : List Gate) :
    (gs.foldl gateStep z).length = z.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp
  | append_singleton xs g ih =>
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil, gateStep]
    simp [ih, Nat.add_assoc]

private theorem foldl_gateStep_input (z : List Bool) (gs : List Gate) (i : ℕ) (hi : i < z.length) :
    (gs.foldl gateStep z).getD i false = z.getD i false := by
  induction gs using List.reverseRecOn with
  | nil => rfl
  | append_singleton xs g ih =>
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil, gateStep]
    have hlen : i < (xs.foldl gateStep z).length := by
      rw [foldl_gateStep_len]
      omega
    rw [getD_append_left _ _ false i hlen]
    exact ih

private theorem foldl_gateStep_gate (z : List Bool) (gs : List Gate) :
    ∀ k < gs.length,
      (gs.foldl gateStep z).getD (z.length + k) false =
        (gs.getD k ⟨GateOp.or, []⟩).op.eval
          ((gs.getD k ⟨GateOp.or, []⟩).inputs.map (fun u =>
            if u < z.length + k then (gs.foldl gateStep z).getD u false else false)) := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro k hk
    simp at hk
  | append_singleton xs g ih =>
    intro k hk
    rw [List.length_append, List.length_singleton] at hk
    let ws := xs.foldl gateStep z
    have hws_len : ws.length = z.length + xs.length := foldl_gateStep_len z xs
    let val := g.op.eval (g.inputs.map (fun u => ws.getD u false))
    have hfold : (xs ++ [g]).foldl gateStep z = ws ++ [val] := by
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      rfl
    rw [hfold]
    by_cases hlt : k < xs.length
    · have h1 : (ws ++ [val]).getD (z.length + k) false = ws.getD (z.length + k) false :=
        getD_append_left ws [val] false (z.length + k) (by omega)
      have h2 : (xs ++ [g]).getD k ⟨GateOp.or, []⟩ = xs.getD k ⟨GateOp.or, []⟩ :=
        getD_append_left xs [g] ⟨GateOp.or, []⟩ k hlt
      rw [h1, h2, ih k hlt]
      congr 1
      apply List.map_congr_left
      intro u _
      by_cases hu : u < z.length + k
      · simp only [hu, ↓reduceIte]
        exact (getD_append_left ws [val] false u (by omega)).symm
      · simp [hu]
    · have hkeq : k = xs.length := by omega
      subst hkeq
      have h1 : (ws ++ [val]).getD (z.length + xs.length) false = val := by
        rw [← hws_len]
        exact getD_append_len ws val false
      have h2 : (xs ++ [g]).getD xs.length ⟨GateOp.or, []⟩ = g :=
        getD_append_len xs g ⟨GateOp.or, []⟩
      rw [h1, h2]
      dsimp only [val]
      congr 1
      apply List.map_congr_left
      intro u _
      by_cases hu : u < z.length + xs.length
      · simp only [hu, ↓reduceIte]
        exact (getD_append_left ws [val] false u (by omega)).symm
      · simp only [hu, ↓reduceIte]
        exact getD_ge_len ws false u (by omega)

private theorem wires9_input (C : Circuit) (z : Fin 9 → Bool) (i : ℕ) (hi : i < 9) :
    (C.wires (List.ofFn z)).getD i false = z ⟨i, hi⟩ := by
  unfold Circuit.wires
  change ((List.ofFn z |> fun s => C.gates.foldl gateStep s)).getD i false = z ⟨i, hi⟩
  rw [foldl_gateStep_input (List.ofFn z) C.gates i (by simp [hi])]
  exact getD_ofFn 9 z i hi

private theorem wires9_ge (C : Circuit) (z : Fin 9 → Bool) (w : ℕ) (hw : 9 + C.gates.length ≤ w) :
    (C.wires (List.ofFn z)).getD w false = false := by
  unfold Circuit.wires
  apply getD_ge_len
  change (C.gates.foldl gateStep (List.ofFn z)).length ≤ w
  rw [foldl_gateStep_len]
  simp
  omega

private theorem wires9_gate (C : Circuit) (z : Fin 9 → Bool) (w : ℕ)
    (hw1 : 9 ≤ w) (hw2 : w < 9 + C.gates.length) :
    (C.wires (List.ofFn z)).getD w false =
      (gateAt C (w - 9)).op.eval
        ((gateAt C (w - 9)).inputs.map (fun u =>
          if u < w then (C.wires (List.ofFn z)).getD u false else false)) := by
  unfold Circuit.wires gateAt
  change (C.gates.foldl gateStep (List.ofFn z)).getD w false =
    (C.gates.getD (w - 9) ⟨GateOp.or, []⟩).op.eval
      ((C.gates.getD (w - 9) ⟨GateOp.or, []⟩).inputs.map (fun u =>
        if u < w then (C.gates.foldl gateStep (List.ofFn z)).getD u false else false))
  have hlen : (List.ofFn z).length = 9 := by simp
  have h := foldl_gateStep_gate (List.ofFn z) C.gates (w - 9) (by omega)
  have heq : 9 + (w - 9) = w := by omega
  rw [hlen, heq] at h
  exact h

private theorem foldl_orStep_len (n : ℕ) (gs : List Gate) :
    (gs.foldl (orStep n) []).length = gs.length := by
  induction gs using List.reverseRecOn with
  | nil => rfl
  | append_singleton xs g ih =>
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil, orStep]
    simp [ih]

private theorem flatMap_congr_mem {α β : Type} (l : List α) (f g : α → List β)
    (hfg : ∀ x ∈ l, f x = g x) : l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    simp only [List.flatMap_cons]
    rw [hfg a (List.mem_cons.mpr (Or.inl rfl)),
      ih (fun x hx => hfg x (List.mem_cons.mpr (Or.inr hx)))]

private theorem orStep_eq (n : ℕ) (cs : List (List ℕ)) (g : Gate) :
    orStep n cs g = cs ++ [cs.length :: (if isOrOp g.op = true then
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => cs.getD (w - n) [])
      else [])] := by
  unfold orStep
  cases g.op <;> rfl

private theorem foldl_orStep_getD (n : ℕ) (gs : List Gate) :
    ∀ k < gs.length,
      (gs.foldl (orStep n) []).getD k [] =
        k :: (if isOrOp (gs.getD k ⟨GateOp.or, []⟩).op = true then
          ((gs.getD k ⟨GateOp.or, []⟩).inputs.filter (fun w => decide (n ≤ w ∧ w < n + k))).flatMap
            (fun w => (gs.foldl (orStep n) []).getD (w - n) [])
        else []) := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro k hk
    simp at hk
  | append_singleton xs g ih =>
    intro k hk
    rw [List.length_append, List.length_singleton] at hk
    let cs := xs.foldl (orStep n) []
    have hcs_len : cs.length = xs.length := foldl_orStep_len n xs
    let entry : List ℕ := cs.length :: (if isOrOp g.op = true then
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => cs.getD (w - n) [])
      else [])
    have hfold : (xs ++ [g]).foldl (orStep n) [] = cs ++ [entry] := by
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil, orStep_eq]
    rw [hfold]
    by_cases hlt : k < xs.length
    · have h1 : (cs ++ [entry]).getD k [] = cs.getD k [] :=
        getD_append_left cs [entry] [] k (by omega)
      have h2 : (xs ++ [g]).getD k ⟨GateOp.or, []⟩ = xs.getD k ⟨GateOp.or, []⟩ :=
        getD_append_left xs [g] ⟨GateOp.or, []⟩ k hlt
      rw [h1, h2, ih k hlt]
      cases isOrOp (xs.getD k ⟨GateOp.or, []⟩).op
      · simp
      · simp only [↓reduceIte, List.cons.injEq, true_and]
        apply flatMap_congr_mem
        intro w hw
        rw [List.mem_filter, decide_eq_true_iff] at hw
        exact (getD_append_left cs [entry] [] (w - n) (by omega)).symm
    · have hkeq : k = xs.length := by omega
      subst hkeq
      have h1 : (cs ++ [entry]).getD xs.length [] = entry := by
        rw [← hcs_len]
        exact getD_append_len cs entry []
      have h2 : (xs ++ [g]).getD xs.length ⟨GateOp.or, []⟩ = g :=
        getD_append_len xs g ⟨GateOp.or, []⟩
      conv_lhs => rw [h1]
      rw [h2]
      dsimp only [entry]
      conv_lhs => rw [hcs_len]
      cases isOrOp g.op
      · simp
      · simp only [↓reduceIte, List.cons.injEq, true_and]
        apply flatMap_congr_mem
        intro w hw
        rw [List.mem_filter, decide_eq_true_iff] at hw
        exact (getD_append_left cs _ [] (w - n) (by omega)).symm

private theorem orSets_mem_iff (n : ℕ) (C : Circuit) {k : ℕ} (hk : k < C.gates.length) (j : ℕ) :
    j ∈ (orSets n C).getD k [] ↔
      j = k ∨ ((gateAt C k).op = GateOp.or ∧
        ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧ j ∈ (orSets n C).getD (w - n) []) := by
  unfold orSets gateAt
  rw [foldl_orStep_getD n C.gates k hk, List.mem_cons]
  cases hop : isOrOp (C.gates.getD k ⟨GateOp.or, []⟩).op
  · have hnot : (C.gates.getD k ⟨GateOp.or, []⟩).op ≠ GateOp.or := by
      intro heq
      rw [(isOrOp_iff _).mpr heq] at hop
      cases hop
    constructor
    · rintro (hjk | hmem)
      · exact Or.inl hjk
      · cases hmem
    · rintro (hjk | ⟨hop', _⟩)
      · exact Or.inl hjk
      · exact False.elim (hnot hop')
  · have heq : (C.gates.getD k ⟨GateOp.or, []⟩).op = GateOp.or := (isOrOp_iff _).mp hop
    simp only [↓reduceIte, List.mem_flatMap, List.mem_filter, decide_eq_true_iff, heq, true_and]
    constructor
    · rintro (hjk | ⟨w, ⟨hw1, hw2, hw3⟩, hjw⟩)
      · exact Or.inl hjk
      · exact Or.inr ⟨w, hw1, hw2, hw3, hjw⟩
    · rintro (hjk | ⟨w, hw1, hw2, hw3, hjw⟩)
      · exact Or.inl hjk
      · exact Or.inr ⟨w, ⟨hw1, hw2, hw3⟩, hjw⟩

private theorem orSets_le_and_true (C : Circuit) (z : Fin 9 → Bool) :
    ∀ (r : ℕ), r < C.gates.length → ∀ (k : ℕ), k ∈ (orSets 9 C).getD r [] →
      k ≤ r ∧ ((C.wires (List.ofFn z)).getD (9 + k) false = true →
        (C.wires (List.ofFn z)).getD (9 + r) false = true) := by
  intro r
  induction r using Nat.strong_induction_on with
  | ind r ih =>
    intro hr k hk
    rcases (orSets_mem_iff 9 C hr k).mp hk with rfl | ⟨hor, w, hw_in, hw1, hw2, hkw⟩
    · exact ⟨Nat.le_refl _, fun h => h⟩
    · have hwr_lt : w - 9 < r := by omega
      have hwr_len : w - 9 < C.gates.length := by omega
      rcases ih (w - 9) hwr_lt hwr_len k hkw with ⟨hkle, htrue⟩
      refine ⟨by omega, fun hkt => ?_⟩
      have hwt : (C.wires (List.ofFn z)).getD w false = true := by
        have heq : 9 + (w - 9) = w := by omega
        rw [← heq]
        exact htrue hkt
      rw [wires9_gate C z (9 + r) (by omega) (by omega)]
      have hsub : 9 + r - 9 = r := by omega
      rw [hsub, hor]
      simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
      refine ⟨w, hw_in, ?_⟩
      simp only [hw2, ↓reduceIte]
      exact hwt

theorem main :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) =>
      x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) ||
      x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) ||
      x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) ||
      x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) ||
      x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) ||
      x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) ||
      x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) ||
      x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) ||
      x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) ||
      x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) ||
      x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) ||
      x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ));
    ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x2 = x1 →
      ∀ (x4 : Fin (9 : ℕ)) (x5 : Fin x2.size) (x6 : ℕ),
        x4 ∈ [(4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))] →
        x6 < (9 : ℕ) + ↑x5 →
        x6 ≠ ↑x4 →
        (x2.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.or →
        (x2.gates.get x5).inputs = [↑x4, x6] ∨ (x2.gates.get x5).inputs = [x6, ↑x4] →
        (∀ (x12 : Fin x2.size), x12 ≠ x5 → ↑x4 ∉ (x2.gates.get x12).inputs) →
        PEqualNP.TopForm.orIn (9 : ℕ) x2 x6 = ∅ ∧
          ∀ (x13 : Fin (9 : ℕ) → Bool),
            x13 x4 = Bool.false →
            x1 x13 = Bool.false →
            x1 (Function.update x13 x4 Bool.true) = Bool.true →
            (x2.wires (List.ofFn x13)).getD x6 Bool.false = Bool.false := by
  change ∀ (C : Circuit), circuitFun 9 C = targetFun →
    ∀ (v : Fin 9) (gIdx : Fin C.size) (x6 : ℕ),
      v ∈ [(4 : Fin 9), (6 : Fin 9), (7 : Fin 9)] →
      x6 < 9 + gIdx.val →
      x6 ≠ v.val →
      (C.gates.get gIdx).op = GateOp.or →
      (C.gates.get gIdx).inputs = [v.val, x6] ∨ (C.gates.get gIdx).inputs = [x6, v.val] →
      (∀ k : Fin C.size, k ≠ gIdx → v.val ∉ (C.gates.get k).inputs) →
      orIn 9 C x6 = ∅ ∧
        ∀ z : Fin 9 → Bool,
          z v = false →
          targetFun z = false →
          targetFun (Function.update z v true) = true →
          (C.wires (List.ofFn z)).getD x6 false = false
  intro C hcf v gIdx x6 hv hx6_lt hx6_ne hop hins huniq
  have heval : ∀ z : Fin 9 → Bool, (C.wires (List.ofFn z)).getD C.output false = targetFun z := by
    intro z
    exact congrFun hcf z
  have hout_ne : C.output ≠ v.val := by
    intro heq
    let z0 : Fin 9 → Bool := fun i => decide (i = v)
    have h1 := heval z0
    rw [heq, wires9_input C z0 v.val v.isLt] at h1
    have h2 : z0 v = true := by simp [z0]
    have h3 : targetFun z0 = false := single_false v hv
    rw [h2, h3] at h1
    cases h1
  have hpart2 : ∀ z : Fin 9 → Bool,
      z v = false → targetFun z = false → targetFun (Function.update z v true) = true →
      (C.wires (List.ofFn z)).getD x6 false = false := by
    intro z hzv hfz hfz'
    apply Classical.byContradiction
    intro hx6_nf
    have hx6_t : (C.wires (List.ofFn z)).getD x6 false = true := by
      revert hx6_nf
      cases (C.wires (List.ofFn z)).getD x6 false <;> simp
    let z' : Fin 9 → Bool := Function.update z v true
    have hagree : ∀ w : ℕ, w ≠ v.val →
        (C.wires (List.ofFn z)).getD w false = (C.wires (List.ofFn z')).getD w false := by
      intro w
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro hw_ne
        by_cases hw9 : w < 9
        · rw [wires9_input C z w hw9, wires9_input C z' w hw9]
          have hfin_ne : (⟨w, hw9⟩ : Fin 9) ≠ v := fun h => hw_ne (congrArg Fin.val h)
          simp [z', Function.update_of_ne hfin_ne]
        · by_cases hwlen : w < 9 + C.gates.length
          · rw [wires9_gate C z w (by omega) hwlen, wires9_gate C z' w (by omega) hwlen]
            let k : Fin C.size := ⟨w - 9, by dsimp [Circuit.size]; omega⟩
            have hgate_eq : gateAt C (w - 9) = C.gates.get k :=
              getD_eq_get C.gates ⟨GateOp.or, []⟩ k
            rw [hgate_eq]
            by_cases hkg : k = gIdx
            · have hw_eq : w = 9 + gIdx.val := by
                have hkval : k.val = gIdx.val := congrArg Fin.val hkg
                dsimp only [k] at hkval
                omega
              rw [hkg, hop]
              have hz_or :
                  GateOp.or.eval ((C.gates.get gIdx).inputs.map (fun u =>
                    if u < w then (C.wires (List.ofFn z)).getD u false else false)) = true := by
                simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
                refine ⟨x6, ?_, ?_⟩
                · rcases hins with h1 | h2
                  · rw [h1]; simp
                  · rw [h2]; simp
                · have hlt_w : x6 < w := by omega
                  simp only [hlt_w, ↓reduceIte]
                  exact hx6_t
              have hz'_or :
                  GateOp.or.eval ((C.gates.get gIdx).inputs.map (fun u =>
                    if u < w then (C.wires (List.ofFn z')).getD u false else false)) = true := by
                simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
                refine ⟨v.val, ?_, ?_⟩
                · rcases hins with h1 | h2
                  · rw [h1]; simp
                  · rw [h2]; simp
                · have hlt_w : v.val < w := by omega
                  have hvt : (C.wires (List.ofFn z')).getD v.val false = true := by
                    rw [wires9_input C z' v.val v.isLt]
                    simp [z']
                  simp only [hlt_w, ↓reduceIte]
                  exact hvt
              rw [hz_or, hz'_or]
            · have hv_not_in : v.val ∉ (C.gates.get k).inputs := huniq k hkg
              congr 1
              apply List.map_congr_left
              intro u hu_in
              have hu_ne : u ≠ v.val := fun heq => hv_not_in (heq ▸ hu_in)
              by_cases hu_lt : u < w
              · simp only [hu_lt, ↓reduceIte]
                exact ih u hu_lt hu_ne
              · simp [hu_lt]
          · rw [wires9_ge C z w (by omega), wires9_ge C z' w (by omega)]
    have hout := hagree C.output hout_ne
    rw [heval z, heval z', hfz] at hout
    have hfz'_eq : targetFun z' = true := hfz'
    rw [hfz'_eq] at hout
    cases hout
  refine ⟨?_, hpart2⟩
  ext u
  constructor
  · intro hu
    letI : DecidableEq GateOp := gateOpDecEq
    unfold orIn at hu
    rw [Finset.mem_filter] at hu
    have hu2 := hu.2
    have hgIdx_len : gIdx.val < C.gates.length := gIdx.isLt
    have hu_ne_v : u ≠ v := by
      intro huv
      subst huv
      rcases hu2 with hvx6 | ⟨k, hk_len, hreach, _, hvin⟩
      · exact hx6_ne hvx6.symm
      · rcases hreach with ⟨hx6_ge9, hk_mem⟩
        have hx6_sub_lt : x6 - 9 < C.gates.length := by omega
        have hkle : k ≤ x6 - 9 := (orSets_le_and_true C (fun _ => false) (x6 - 9) hx6_sub_lt k hk_mem).1
        let kFin : Fin C.size := ⟨k, hk_len⟩
        have hk_ne_gIdx : kFin ≠ gIdx := by
          intro heq
          have hval : k = gIdx.val := congrArg Fin.val heq
          omega
        have hgate_eq : gateAt C k = C.gates.get kFin := getD_eq_get C.gates ⟨GateOp.or, []⟩ kFin
        rw [hgate_eq] at hvin
        exact huniq kFin hk_ne_gIdx hvin
    rcases exists_sep v u hv hu_ne_v with ⟨m, hmu, hmv, hfm0, hfm1⟩
    let zm : Fin 9 → Bool := fun i => m.val.testBit i.val
    have hupd_eq : Function.update zm v true = (fun i : Fin 9 => if i = v then true else m.val.testBit i.val) := by
      ext i
      by_cases hiv : i = v
      · subst hiv; simp [zm]
      · simp [zm, hiv]
    have hzm_f : (C.wires (List.ofFn zm)).getD x6 false = false := by
      apply hpart2 zm hmv hfm0
      rw [hupd_eq]
      exact hfm1
    have hzm_t : (C.wires (List.ofFn zm)).getD x6 false = true := by
      rcases hu2 with hux6 | ⟨k, hk_len, hreach, hor_k, huin⟩
      · rw [← hux6, wires9_input C zm u.val u.isLt]
        exact hmu
      · have hkt : (C.wires (List.ofFn zm)).getD (9 + k) false = true := by
          rw [wires9_gate C zm (9 + k) (by omega) (by omega)]
          have hsub : 9 + k - 9 = k := by omega
          rw [hsub, hor_k]
          simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
          refine ⟨u.val, huin, ?_⟩
          have hult : u.val < 9 + k := by omega
          simp only [hult, ↓reduceIte]
          rw [wires9_input C zm u.val u.isLt]
          exact hmu
        rcases hreach with ⟨hx6_ge9, hk_mem⟩
        have hx6_sub_lt : x6 - 9 < C.gates.length := by omega
        have hr_t := (orSets_le_and_true C zm (x6 - 9) hx6_sub_lt k hk_mem).2 hkt
        have heq : 9 + (x6 - 9) = x6 := by omega
        rwa [heq] at hr_t
    rw [hzm_t] at hzm_f
    cases hzm_f
  · intro hu
    cases hu

end PEqualNP.Outside.L_meta_6005_aux

theorem PEqualNP.Outside.L_meta_6005 : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x2 = x1 → ∀ (x4 : Fin (9 : ℕ)) (x5 : Fin x2.size) (x6 : ℕ), x4 ∈ [(4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))] → x6 < (9 : ℕ) + ↑x5 → x6 ≠ ↑x4 → (x2.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.or → (x2.gates.get x5).inputs = [↑x4, x6] ∨ (x2.gates.get x5).inputs = [x6, ↑x4] → (∀ (x12 : Fin x2.size), x12 ≠ x5 → ↑x4 ∉ (x2.gates.get x12).inputs) → PEqualNP.TopForm.orIn (9 : ℕ) x2 x6 = ∅ ∧ ∀ (x13 : Fin (9 : ℕ) → Bool), x13 x4 = Bool.false → x1 x13 = Bool.false → x1 (Function.update x13 x4 Bool.true) = Bool.true → (x2.wires (List.ofFn x13)).getD x6 Bool.false = Bool.false :=
  PEqualNP.Outside.L_meta_6005_aux.main
