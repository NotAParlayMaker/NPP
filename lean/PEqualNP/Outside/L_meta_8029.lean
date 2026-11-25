import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8029

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.EdgeOwnership

private def edges : List (Fin 11 × Fin 11) :=
  [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7),
   (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]

private def masks : List ℕ :=
  [15, 29, 43, 57, 71, 85, 99, 113, 135, 149, 163, 177, 269, 325, 389,
   526, 540, 582, 596, 1066, 1186, 1288, 1408, 1546]

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem gate_eval_mono (g : Gate)
    (hop : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (w1 w2 : List Bool)
    (hle : ∀ i, w1.getD i false = true → w2.getD i false = true) :
    g.op.eval (g.inputs.map fun i => w1.getD i false) = true →
    g.op.eval (g.inputs.map fun i => w2.getD i false) = true := by
  have hcases : g.op = GateOp.and ∨ g.op = GateOp.or := by
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hop
  rcases hcases with h | h <;> rw [h]
  · simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq,
      forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    intro h1 i hi
    exact hle i (h1 i hi)
  · simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq,
      exists_exists_and_eq_and]
    rintro ⟨i, hi, h1⟩
    exact ⟨i, hi, hle i h1⟩

private theorem foldl_mono (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (w1 w2 : List Bool) (hlen : w1.length = w2.length)
    (hle : ∀ i, w1.getD i false = true → w2.getD i false = true) :
    ∀ i, (gs.foldl step w1).getD i false = true →
         (gs.foldl step w2).getD i false = true := by
  induction gs generalizing w1 w2 with
  | nil => exact hle
  | cons g rest ih =>
    simp only [List.foldl_cons]
    have hg : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) := hgs g List.mem_cons_self
    have hrest : ∀ g' ∈ rest, g'.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) :=
      fun g' hg' => hgs g' (List.mem_cons_of_mem g hg')
    apply ih hrest (step w1 g) (step w2 g)
    · simp only [step, List.length_append, List.length_singleton, hlen]
    · intro i hi
      by_cases hlt : i < w1.length
      · have hlt2 : i < w2.length := hlen ▸ hlt
        simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt] at hi
        simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt2]
        exact hle i hi
      · by_cases heq : i = w1.length
        · subst heq
          simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl,
            Nat.sub_self, List.getElem?_cons_zero, Option.getD_some] at hi
          simp only [step, List.getD_eq_getElem?_getD, hlen, List.getElem?_append_right le_rfl,
            Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
          exact gate_eval_mono g hg w1 w2 hle hi
        · have hgt : w1.length + 1 ≤ i := by omega
          have hlen1 : (step w1 g).length = w1.length + 1 := by simp [step]
          rw [List.getD_eq_default _ _ (by omega)] at hi
          cases hi

private theorem circuit_mono (C : Circuit) (hM : Monotone2 C) (x y : Fin 11 → Bool)
    (hle : ∀ i : Fin 11, x i = true → y i = true) :
    C.eval (List.ofFn x) = true → C.eval (List.ofFn y) = true := by
  apply foldl_mono C.gates (fun g hg => (hM g hg).1) (List.ofFn x) (List.ofFn y)
  · simp only [List.length_ofFn]
  · intro i hi
    by_cases hlt : i < 11
    · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hlt, ↓reduceDIte,
        Option.getD_some] at hi ⊢
      exact hle ⟨i, hlt⟩ hi
    · rw [List.getD_eq_default _ _ (by simp only [List.length_ofFn]; omega)] at hi
      cases hi

private def encodeShift (x : Fin 11 → Bool) : ℕ → ℕ
  | 0 => 0
  | n + 1 => 2 * encodeShift x n + if h : 10 - n < 11 then if x ⟨10 - n, h⟩ then 1 else 0 else 0

private theorem encodeShift_lt (x : Fin 11 → Bool) (n : ℕ) :
    encodeShift x n < 2 ^ n := by
  induction n with
  | zero => simp [encodeShift]
  | succ n ih =>
    simp only [encodeShift, pow_succ]
    split_ifs <;> omega

private theorem encodeShift_testBit (x : Fin 11 → Bool) :
    ∀ (n j : ℕ) (hn : n ≤ 11) (hj : j < n),
      (encodeShift x n).testBit j = x ⟨11 - n + j, by omega⟩ := by
  intro n
  induction n with
  | zero => intro j _ hj; omega
  | succ n ih =>
    intro j hn hj
    have hlt : 10 - n < 11 := by omega
    simp only [encodeShift, hlt, ↓reduceDIte]
    cases j with
    | zero =>
      have hidx : (⟨11 - (n + 1) + 0, by omega⟩ : Fin 11) = ⟨10 - n, hlt⟩ := by
        ext; dsimp; omega
      rw [hidx]
      cases hx : x ⟨10 - n, hlt⟩
      · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero, Nat.testBit_zero,
          Nat.mul_mod_right]
        rfl
      · simp only [↓reduceIte, Nat.testBit_zero, Nat.mul_add_mod, Nat.one_mod]
        rfl
    | succ j =>
      have hsub : 11 - (n + 1) + (j + 1) = 11 - n + j := by omega
      have hidx : (⟨11 - (n + 1) + (j + 1), by omega⟩ : Fin 11) = ⟨11 - n + j, by omega⟩ := by
        ext; exact hsub
      rw [hidx]
      cases hx : x ⟨10 - n, hlt⟩
      · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero, Nat.testBit_succ,
          Nat.mul_div_right _ (by omega : 0 < 2)]
        exact ih j (by omega) (by omega)
      · simp only [↓reduceIte, Nat.testBit_succ]
        have hdiv : (2 * encodeShift x n + 1) / 2 = encodeShift x n := by omega
        rw [hdiv]
        exact ih j (by omega) (by omega)

private def maskHasEdge (s : ℕ) : Bool :=
  edges.any fun e => s.testBit e.1.val && s.testBit e.2.val

private def maskCovered (s : ℕ) : Bool :=
  masks.any fun m => (s &&& m) == s

private theorem all_masks_ok :
    (List.range 2048).all (fun s => maskHasEdge s || maskCovered s) = true := by
  decide +kernel

private theorem main (C : Circuit) (hM : Monotone2 C)
    (hpos : ∀ p ∈ edges, C.eval (List.ofFn (pairInput p.1 p.2)) = true)
    (hneg : ∀ m ∈ masks, C.eval (List.ofFn fun i : Fin 11 => m.testBit i.val) = false) :
    circuitFun 11 C = fun x : Fin 11 → Bool => edges.any fun p => x p.1 && x p.2 := by
  funext x
  change C.eval (List.ofFn x) = edges.any fun p => x p.1 && x p.2
  cases hval : edges.any fun p => x p.1 && x p.2
  · have hno : maskHasEdge (encodeShift x 11) = false := by
      rw [← hval]
      simp only [maskHasEdge]
      congr 1
      funext p
      have h1 := encodeShift_testBit x 11 p.1.val le_rfl p.1.isLt
      have h2 := encodeShift_testBit x 11 p.2.val le_rfl p.2.isLt
      simp only [Nat.sub_self, Nat.zero_add, Fin.eta] at h1 h2
      rw [h1, h2]
    have hlt : encodeShift x 11 < 2048 := encodeShift_lt x 11
    have hmem : encodeShift x 11 ∈ List.range 2048 := List.mem_range.mpr hlt
    have hok := List.all_eq_true.mp all_masks_ok (encodeShift x 11) hmem
    rw [hno, Bool.false_or] at hok
    simp only [maskCovered, List.any_eq_true, beq_iff_eq] at hok
    obtain ⟨m, hm, hand⟩ := hok
    cases hce : C.eval (List.ofFn x)
    · rfl
    · exfalso
      have hle : ∀ i : Fin 11, x i = true → m.testBit i.val = true := by
        intro i hi
        have htb := encodeShift_testBit x 11 i.val le_rfl i.isLt
        simp only [Nat.sub_self, Nat.zero_add, Fin.eta] at htb
        have hs : (encodeShift x 11).testBit i.val = true := htb.trans hi
        rw [← hand, Nat.testBit_and, Bool.and_eq_true] at hs
        exact hs.2
      have hmtrue := circuit_mono C hM x (fun i : Fin 11 => m.testBit i.val) hle hce
      have hmfalse := hneg m hm
      rw [hmfalse] at hmtrue
      cases hmtrue
  · simp only [List.any_eq_true, Bool.and_eq_true] at hval
    obtain ⟨p, hp, h1, h2⟩ := hval
    apply circuit_mono C hM (pairInput p.1 p.2) x
    · intro i hi
      simp only [pairInput, decide_eq_true_eq] at hi
      rcases hi with rfl | rfl
      · exact h1
      · exact h2
    · exact hpos p hp

end PEqualNP.Outside.L_meta_8029

theorem PEqualNP.Outside.L_meta_8029 : have x1 : List (Fin (11 : ℕ) × Fin (11 : ℕ)) := [((0 : Fin (11 : ℕ)), (9 : Fin (11 : ℕ))), ((0 : Fin (11 : ℕ)), (10 : Fin (11 : ℕ))), ((1 : Fin (11 : ℕ)), (4 : Fin (11 : ℕ))), ((1 : Fin (11 : ℕ)), (8 : Fin (11 : ℕ))), ((2 : Fin (11 : ℕ)), (5 : Fin (11 : ℕ))), ((2 : Fin (11 : ℕ)), (10 : Fin (11 : ℕ))), ((3 : Fin (11 : ℕ)), (6 : Fin (11 : ℕ))), ((3 : Fin (11 : ℕ)), (7 : Fin (11 : ℕ))), ((4 : Fin (11 : ℕ)), (8 : Fin (11 : ℕ))), ((4 : Fin (11 : ℕ)), (10 : Fin (11 : ℕ))), ((5 : Fin (11 : ℕ)), (8 : Fin (11 : ℕ))), ((5 : Fin (11 : ℕ)), (9 : Fin (11 : ℕ))), ((6 : Fin (11 : ℕ)), (7 : Fin (11 : ℕ))), ((6 : Fin (11 : ℕ)), (10 : Fin (11 : ℕ))), ((7 : Fin (11 : ℕ)), (9 : Fin (11 : ℕ))), ((8 : Fin (11 : ℕ)), (9 : Fin (11 : ℕ)))]; have x2 : List ℕ := [(15 : ℕ), (29 : ℕ), (43 : ℕ), (57 : ℕ), (71 : ℕ), (85 : ℕ), (99 : ℕ), (113 : ℕ), (135 : ℕ), (149 : ℕ), (163 : ℕ), (177 : ℕ), (269 : ℕ), (325 : ℕ), (389 : ℕ), (526 : ℕ), (540 : ℕ), (582 : ℕ), (596 : ℕ), (1066 : ℕ), (1186 : ℕ), (1288 : ℕ), (1408 : ℕ), (1546 : ℕ)]; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x3 → (∀ x5 ∈ x1, x3.eval (List.ofFn (PEqualNP.EdgeOwnership.pairInput x5.1 x5.2)) = Bool.true) → (∀ x6 ∈ x2, x3.eval (List.ofFn fun (x8 : Fin (11 : ℕ)) => x6.testBit ↑x8) = Bool.false) → PEqualNP.MetaComplexity.circuitFun (11 : ℕ) x3 = fun (x7 : Fin (11 : ℕ) → Bool) => x1.any fun (x8 : Fin (11 : ℕ) × Fin (11 : ℕ)) => x7 x8.1 && x7 x8.2 := by
  exact PEqualNP.Outside.L_meta_8029.main
