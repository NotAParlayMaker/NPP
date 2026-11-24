import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3897_214
    (left : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (r : Nat),
        gs.length = 13 → PEqualNP.MetaComplexity.FanInTwo ⟨gs, 0⟩ →
        gs.countP (fun g => g.op.eval [false]) ≤ 1 → 16 ≤ r → r < 22 →
        let w := fun (x : Fin 9 → Bool) (i : Nat) =>
          ((⟨gs, 0⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires (List.ofFn x ++ [x 0 || x 3])).getD i false
        let f := fun (x : Fin 9 → Bool) => ([1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85] : List Nat).any fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))
        (∀ j ∈ ([r,22] : List Nat), (gs.getD (j-10) ⟨.or,[]⟩).op ≠ .not) →
        (∃ x, w x r = true ∧ w x 22 = false) →
        (∃ x, w x r = false ∧ w x 22 = true) →
        (∀ x, (w x r && w x 22) = f x) →
        (∀ i : Fin 9, ∃ x, w x r = false ∧ w (Function.update x i true) r = true) → False)
    (right : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (r : Nat),
        gs.length = 13 → PEqualNP.MetaComplexity.FanInTwo ⟨gs, 0⟩ →
        gs.countP (fun g => g.op.eval [false]) ≤ 1 → 12 ≤ r → r < 22 →
        let w := fun (x : Fin 9 → Bool) (i : Nat) =>
          ((⟨gs, 0⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires (List.ofFn x ++ [x 0 || x 3])).getD i false
        let f := fun (x : Fin 9 → Bool) => ([1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85] : List Nat).any fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))
        (∀ j ∈ ([r,22] : List Nat), (gs.getD (j-10) ⟨.or,[]⟩).op ≠ .not) →
        (∃ x, w x r = true ∧ w x 22 = false) →
        (∃ x, w x r = false ∧ w x 22 = true) →
        (∀ x, (w x r && w x 22) = f x) →
        (∀ i : Fin 9, ∃ x, w x 22 = false ∧ w (Function.update x i true) 22 = true) → False) :
    ∀ (x1 : List PEqualNP.CircuitLowerBounds.Gate),   x1.length = (13 : ℕ) →     PEqualNP.MetaComplexity.FanInTwo { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →       List.countP (fun (x4 : PEqualNP.CircuitLowerBounds.Gate) => x4.op.eval [Bool.false]) x1 ≤ (1 : ℕ) →         ∀ (x5 : ℕ),           (12 : ℕ) ≤ x5 →             x5 < (22 : ℕ) →               have x8 : (Fin (9 : ℕ) → Bool) → ℕ → Bool := fun (x8 : Fin (9 : ℕ) → Bool) (x9 : ℕ) => ({ gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x8 ++ [x8 (0 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ))])).getD x9 Bool.false;               have x9 : (Fin (9 : ℕ) → Bool) → Bool := fun (x9 : Fin (9 : ℕ) → Bool) => x9 (0 : Fin (9 : ℕ)) && x9 (1 : Fin (9 : ℕ)) || x9 (1 : Fin (9 : ℕ)) && x9 (2 : Fin (9 : ℕ)) || x9 (2 : Fin (9 : ℕ)) && x9 (3 : Fin (9 : ℕ)) || x9 (3 : Fin (9 : ℕ)) && x9 (4 : Fin (9 : ℕ)) || x9 (4 : Fin (9 : ℕ)) && x9 (0 : Fin (9 : ℕ)) || x9 (0 : Fin (9 : ℕ)) && x9 (5 : Fin (9 : ℕ)) || x9 (1 : Fin (9 : ℕ)) && x9 (6 : Fin (9 : ℕ)) || x9 (2 : Fin (9 : ℕ)) && x9 (7 : Fin (9 : ℕ)) || x9 (3 : Fin (9 : ℕ)) && x9 (8 : Fin (9 : ℕ)) || x9 (5 : Fin (9 : ℕ)) && x9 (7 : Fin (9 : ℕ)) || x9 (6 : Fin (9 : ℕ)) && x9 (8 : Fin (9 : ℕ)) || x9 (8 : Fin (9 : ℕ)) && x9 (5 : Fin (9 : ℕ));               (∀ x10 ∈ [x5, (22 : ℕ)], (x1.getD (x10 - (10 : ℕ)) { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] : PEqualNP.CircuitLowerBounds.Gate }).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) → (∃ (x11 : Fin (9 : ℕ) → Bool), x8 x11 x5 = Bool.true ∧ x8 x11 (22 : ℕ) = Bool.false) → (∃ (x12 : Fin (9 : ℕ) → Bool), x8 x12 x5 = Bool.false ∧ x8 x12 (22 : ℕ) = Bool.true) → ∃ (x13 : Fin (9 : ℕ) → Bool), (x8 x13 x5 && x8 x13 (22 : ℕ)) ≠ x9 x13 := by
  classical
  intro gs hl fan hn r lr ur
  dsimp only
  intro safe ab ba
  let w := fun (x : Fin 9 → Bool) (i : Nat) =>
    ((⟨gs, 0⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires (List.ofFn x ++ [x 0 || x 3])).getD i false
  let f := fun (x : Fin 9 → Bool) => ([1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85] : List Nat).any fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))
  let spelled := fun (x : Fin 9 → Bool) => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5
  change ∃ x, (w x r && w x 22) ≠ spelled x
  by_contra! contra
  have same (x : Fin 9 → Bool) : (w x r && w x 22) = f x := by
    rw [contra x]
    simp only [spelled, f, List.any_cons, List.any_nil, Bool.or_false, Bool.or_assoc]
    rfl
  let rise := fun (k : Nat) (i : Fin 9) =>
    ∃ x, w x k = false ∧ w (Function.update x i true) k = true
  by_cases h : ∀ i, rise r i
  · have sixteen : 16 ≤ r := by
      let step := fun (v : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) =>
        v ++ [g.op.eval (g.inputs.map fun k => v.getD k false)]
      have pull (ls : List PEqualNP.CircuitLowerBounds.Gate) (hb : ∀ g ∈ ls, g.inputs.length ≤ 2)
          (n : Nat) (t : Finset Nat) : ∃ s : Finset Nat, s.card ≤ t.card + ls.length ∧
          ∀ (u v : List Bool), u.length = n → v.length = n →
            (∀ k ∈ s, u.getD k false = v.getD k false) →
            ∀ k ∈ t, (ls.foldl step u).getD k false = (ls.foldl step v).getD k false := by
        induction ls generalizing n t with
        | nil => exact ⟨t, by simp, fun _ _ _ _ hh => hh⟩
        | cons g ls ih =>
          obtain ⟨s, hs, hh⟩ := ih (fun a ha => hb a (by simp [ha])) (n+1) t
          have snoc (u : List Bool) (hn : u.length = n) (k : Nat) (hk : k ≠ n) :
              (step u g).getD k false = u.getD k false := by
            by_cases hlt : k < n
            · exact List.getD_append _ _ _ _ (by omega)
            · rw [List.getD_eq_default _ _ (by simp [step, hn]; omega),
                  List.getD_eq_default _ _ (by omega)]
          by_cases hnew : n ∈ s
          · refine ⟨s.erase n ∪ g.inputs.toFinset, ?_, ?_⟩
            · have h1 := Finset.card_union_le (s.erase n) g.inputs.toFinset
              have h2 := List.toFinset_card_le g.inputs
              have h3 := hb g List.mem_cons_self
              rw [Finset.card_erase_of_mem hnew] at h1
              have h4 := Finset.card_pos.mpr ⟨n,hnew⟩
              simp only [List.length_cons]
              omega
            · intro u v hu hv agree
              apply hh _ _ (by simp [step,hu]) (by simp [step,hv])
              intro k hk
              by_cases e : k = n
              · subst k
                have reads : g.inputs.map (fun a => u.getD a false) = g.inputs.map (fun a => v.getD a false) := by
                  apply List.map_congr_left
                  intro a ha
                  exact agree _ (Finset.mem_union_right _ (List.mem_toFinset.mpr ha))
                change (u ++ [_]).getD n false = (v ++ [_]).getD n false
                rw [reads, List.getD_append_right _ _ _ _ (by omega),
                  List.getD_append_right _ _ _ _ (by omega), hu, hv]
              · rw [snoc u hu k e, snoc v hv k e]
                exact agree _ (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨e,hk⟩))
          · refine ⟨s, by simp only [List.length_cons]; omega, ?_⟩
            intro u v hu hv agree
            apply hh _ _ (by simp [step,hu]) (by simp [step,hv])
            intro k hk
            have hne : k ≠ n := fun e => hnew (e ▸ hk)
            rw [snoc u hu k hne, snoc v hv k hne]
            exact agree k hk
      let data := fun (x : Fin 9 → Bool) => List.ofFn x ++ [x 0 || x 3]
      let pref := gs.take (r-9)
      have keep (ls : List PEqualNP.CircuitLowerBounds.Gate) (u : List Bool) (k : Nat) (hk : k < u.length) :
          (ls.foldl step u).getD k false = u.getD k false := by
        induction ls generalizing u with
        | nil => rfl
        | cons g ls ih =>
          rw [List.foldl_cons, ih _ (by simp [step]; omega)]
          exact List.getD_append _ _ _ _ hk
      have plen : pref.length = r-9 := by simp [pref, List.length_take,hl]; omega
      have wl (x : Fin 9 → Bool) : w x r = (pref.foldl step (data x)).getD r false := by
        have len (ls : List PEqualNP.CircuitLowerBounds.Gate) (u : List Bool) :
            (ls.foldl step u).length = u.length + ls.length := by
          induction ls generalizing u with
          | nil => simp
          | cons g ls ih => rw [List.foldl_cons, ih]; simp [step]; omega
        change (gs.foldl step (data x)).getD r false = _
        conv_lhs => rw [← List.take_append_drop (r-9) gs, List.foldl_append]
        exact keep _ _ _ (by change r < (pref.foldl step (data x)).length; rw [len, plen]; simp [data]; omega)
      obtain ⟨s, size, pred⟩ := pull pref (fun g hg => (fan g (List.mem_of_mem_take hg)).2) 10 {r}
      have allInputs (i : Fin 9) (aux : i = 0 ∨ i = 3 → 9 ∉ s) : i.val ∈ s := by
        by_contra miss
        obtain ⟨x, h0, h1⟩ := h i
        let y := Function.update x i true
        have eqv (k : Nat) (hk : k ∈ s) : (data x).getD k false = (data y).getD k false := by
          by_cases low : k < 9
          · have ne : (⟨k,low⟩ : Fin 9) ≠ i := fun e => miss (congrArg Fin.val e ▸ hk)
            have read (z : Fin 9 → Bool) : (data z).getD k false = z ⟨k,low⟩ := by
              rw [List.getD_append _ _ _ _ (by simpa), List.getD_eq_getElem _ _ (by simpa), List.getElem_ofFn]
            rw [read,read]
            exact (Function.update_of_ne ne true x).symm
          · by_cases e : k = 9
            · subst k
              have n0 : (0 : Fin 9) ≠ i := fun e => aux (Or.inl e.symm) hk
              have n3 : (3 : Fin 9) ≠ i := fun e => aux (Or.inr e.symm) hk
              have read (z : Fin 9 → Bool) : (data z).getD 9 false = (z 0 || z 3) := by
                change ((List.ofFn z) ++ [_]).getD 9 false = _
                rw [List.getD_append_right _ _ _ _ (by simp), List.length_ofFn]; rfl
              simp only [read, y, Function.update_of_ne n0, Function.update_of_ne n3]
            · rw [List.getD_eq_default _ _ (by simp [data]; omega),
                  List.getD_eq_default _ _ (by simp [data]; omega)]
        have bad := pred _ _ (by simp [data]) (by simp [data]) eqv r (Finset.mem_singleton_self _)
        rw [← wl, ← wl, h0] at bad
        exact Bool.false_ne_true (bad.trans h1)
      have core : ({1,2,4,5,6,7,8} : Finset Nat) ⊆ s := by
        intro k hk
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals apply allInputs (i := (⟨_,by decide⟩ : Fin 9)); intro impossible; exact False.elim ((by decide : ¬ _) impossible)
      have count : 8 ≤ s.card := by
        by_cases hnine : 9 ∈ s
        · have hh := Finset.card_le_card (Finset.insert_subset hnine core)
          exact (show 8 = (insert 9 ({1,2,4,5,6,7,8} : Finset Nat)).card by decide).le.trans hh
        · have z := allInputs 0 (fun _ => hnine)
          have hh := Finset.card_le_card (Finset.insert_subset z core)
          exact (show 8 = (insert 0 ({1,2,4,5,6,7,8} : Finset Nat)).card by decide).le.trans hh
      rw [plen, Finset.card_singleton] at size
      omega
    exact left gs r hl fan hn sixteen ur safe ab ba same h
  apply right gs r hl fan hn lr ur safe ab ba same
  obtain ⟨i, hi⟩ := Classical.not_forall.mp h
  intro j
  let masks : List (List Nat) := [[42, 104, 42, 50, 42, 138, 42, 42, 42], [104, 69, 104, 69, 69, 69, 261, 69, 69], [42, 104, 42, 50, 42, 138, 42, 42, 42], [50, 69, 50, 50, 69, 69, 50, 50, 50], [42, 69, 42, 69, 42, 69, 42, 42, 42], [138, 69, 138, 69, 69, 69, 138, 69, 69], [42, 261, 42, 50, 42, 138, 42, 42, 42], [42, 69, 42, 50, 42, 69, 42, 42, 42], [42, 69, 42, 50, 42, 69, 42, 42, 42]]
  let sample := fun (p q v : Fin 9) => (((masks.getD p.val []).getD q.val 0).testBit v.val)
  have cert : ∀ p q : Fin 9, f (sample p q) = false ∧
      f (Function.update (sample p q) p true) = true ∧
      f (Function.update (sample p q) q true) = true := by
    dsimp only [f, sample, masks]
    decide +kernel
  let x := sample i j
  obtain ⟨neg, posI, posJ⟩ := cert i j
  have hp := Bool.and_eq_true_iff.mp ((same (Function.update x i true)).trans posI)
  have hq := Bool.and_eq_true_iff.mp ((same (Function.update x j true)).trans posJ)
  have hv : w x r = true := by
    cases e : w x r
    · exact False.elim (hi ⟨x, e, hp.1⟩)
    · rfl
  have hz := (same x).trans neg
  rw [hv, Bool.true_and] at hz
  exact ⟨x, hz, hq.2⟩
