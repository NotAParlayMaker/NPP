import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_2794_701
    (h1 : ∀ (x1 : ℕ) (x2 : Fin x1 → Fin x1 → Prop) [DecidableRel x2] (x4 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x5 x6 x7 x8 : Fin x1), x5 ≠ x6 → x7 ≠ x8 → ¬(x2 x5 x7 ∧ x2 x6 x7 ∧ x2 x5 x8 ∧ x2 x6 x8)) → PEqualNP.TopForm.IsAO2 (x1 + x1) x4 → (∀ (x7 : Fin (x1 + x1) → Bool), Fintype.card { x8 : Fin x1 // x7 (Fin.natAdd x1 x8) = Bool.true } ≤ (1 : ℕ) → (¬∃ (x9 : Fin x1) (x10 : Fin x1), x2 x9 x10 ∧ x7 (Fin.castAdd x1 x9) = Bool.true ∧ x7 (Fin.natAdd x1 x10) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x1 + x1) x4 x7 = Bool.false) → Fintype.card { x8 : Fin x1 × Fin x1 // x2 x8.1 x8.2 ∧ PEqualNP.ReadK.lineSingle x4 (x1 + x1) (fun (x9 : ℕ) => Decidable.decide (x1 ≤ x9)) (↑x8.1) (x1 + ↑x8.2) = Bool.true } ≤ (10 : ℕ) * x4.size)
    (h2 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (2 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.TopForm.IsAO2 (x2 + x2) x5 → (∀ (x11 : Fin (x2 + x2) → Bool), Fintype.card { x12 : Fin x2 // x11 (Fin.natAdd x2 x12) = Bool.true } ≤ x1 → (¬∃ (x13 : Fin x2) (x14 : Fin x2), x3 x13 x14 ∧ x11 (Fin.castAdd x2 x13) = Bool.true ∧ x11 (Fin.natAdd x2 x14) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x11 = Bool.false) → Fintype.card { x12 : Fin x2 × Fin x2 // x3 x12.1 x12.2 ∧ PEqualNP.ReadK.lineSingle x5 (x2 + x2) (fun (x13 : ℕ) => Decidable.decide (x13 < x2)) (↑x12.1) (x2 + ↑x12.2) = Bool.true } ≤ (10 : ℕ) * x5.size)
    (h3 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (87 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.TopForm.IsAO2 (x2 + x2) x5 → (∀ (x11 : Fin (x2 + x2) → Bool), Fintype.card { x12 : Fin x2 // x11 (Fin.natAdd x2 x12) = Bool.true } ≤ x1 → (¬∃ (x13 : Fin x2) (x14 : Fin x2), x3 x13 x14 ∧ x11 (Fin.castAdd x2 x13) = Bool.true ∧ x11 (Fin.natAdd x2 x14) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x11 = Bool.false) → Fintype.card { x12 : Fin x2 × Fin x2 // x3 x12.1 x12.2 ∧ (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x13 : Fin (x2 + x2)) => Decidable.decide (x13 = Fin.castAdd x2 x12.1 ∨ x13 = Fin.natAdd x2 x12.2)) = Bool.true ∧ PEqualNP.ReadK.lineSingle x5 (x2 + x2) (fun (x13 : ℕ) => Decidable.decide (x2 ≤ x13)) (↑x12.1) (x2 + ↑x12.2) = Bool.false ∧ PEqualNP.ReadK.lineSingle x5 (x2 + x2) (fun (x13 : ℕ) => Decidable.decide (x13 < x2)) (↑x12.1) (x2 + ↑x12.2) = Bool.false } ≤ (24 : ℕ) * x5.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [DecidableRel x3],   (100 : ℕ) < x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) →         (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) →           ∀ (x9 x10 : ℕ) (x11 : Finset ℕ) (x12 : ℕ → Set ((Fin x2 → Bool) × (Fin x2 → Bool))),             x10 < x2 + x2 + x9 →               (∀ (x14 : Fin x2), x12 ↑x14 = {x15 : (Fin x2 → Bool) × (Fin x2 → Bool) | x15.1 x14 = Bool.true} ∧ x12 (x2 + ↑x14) = {x15 : (Fin x2 → Bool) × (Fin x2 → Bool) | x15.2 x14 = Bool.true}) →                 (∀ x15 < x9,                     ∃ x17 < x2 + x2 + x15,                       ∃ x18 < x2 + x2 + x15,                         have x19 : Set ((Fin x2 → Bool) × (Fin x2 → Bool)) := x12 (x2 + x2 + x15);                         x19 = x12 x17 ∪ x12 x18 ∨ x19 = x12 x17 ∨ x19 = ∅ ∨ x19 = x12 x17 ∩ x12 x18 ∧ (x15 ∈ x11 ∨ ∃ (x20 : Set (Fin x2 → Bool)) (x21 : Set (Fin x2 → Bool)), x12 x17 = x20 ×ˢ Set.univ ∧ x12 x18 = Set.univ ×ˢ x21)) →                   (∀ (x16 x17 : Fin x2), x3 x16 x17 → (fun (x19 : Fin x2) => Decidable.decide (x19 = x16), fun (x19 : Fin x2) => Decidable.decide (x19 = x17)) ∈ x12 x10) → (∀ (x17 : Fin x2 → Bool), Fintype.card { x18 : Fin x2 // x17 x18 = Bool.true } ≤ x1 → (fun (x19 : Fin x2) => Decidable.decide ¬∃ (x20 : Fin x2), x3 x19 x20 ∧ x17 x20 = Bool.true, x17) ∉ x12 x10) → (100 : ℕ) * x11.card < x2 * x1 → x2 * x1 ≤ (100 : ℕ) * x9 := by
  classical
  intro q N I inst hq hN hdeg huniq s o marked W ho hbase hsteps hpos hneg _
  let n : ℕ := N + N
  let step : List Bool → Gate → List Bool := fun w g =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let run : List Gate → List Bool → List Bool := fun gs w => gs.foldl step w
  have run_append : ∀ (gs hs : List Gate) (w : List Bool), run (gs ++ hs) w = run hs (run gs w) := by
    intro gs hs w
    simp [run, List.foldl_append]
  have run_length : ∀ (gs : List Gate) (w : List Bool), (run gs w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp [run]
    | cons g gs ih =>
      intro w
      change (run gs (step w g)).length = w.length + (gs.length + 1)
      rw [ih (step w g)]
      simp [step]
      omega
  have run_snoc_lt : ∀ (gs : List Gate) (g : Gate) (w : List Bool) (i : ℕ),
      i < w.length + gs.length → (run (gs ++ [g]) w).getD i false = (run gs w).getD i false := by
    intro gs g w i hi
    rw [run_append]
    change (step (run gs w) g).getD i false = (run gs w).getD i false
    have hlen : i < (run gs w).length := by rw [run_length]; exact hi
    exact List.getD_append _ _ _ _ hlen
  have run_snoc_last : ∀ (gs : List Gate) (g : Gate) (w : List Bool),
      (run (gs ++ [g]) w).getD (w.length + gs.length) false =
        g.op.eval (g.inputs.map fun i => (run gs w).getD i false) := by
    intro gs g w
    rw [run_append]
    change (step (run gs w) g).getD (w.length + gs.length) false = _
    have hlen : (run gs w).length = w.length + gs.length := run_length gs w
    rw [← hlen]
    simp [step]
  let wireSpec : List Gate → Option ℕ → Set ((Fin N → Bool) × (Fin N → Bool)) → Prop :=
    fun gs rOpt S =>
      (rOpt = none → S = ∅) ∧
      ∀ r, rOpt = some r → r < n + gs.length ∧
        ∀ P L : Fin N → Bool,
          (run gs (List.ofFn (Fin.append P L))).getD r false = true ↔ (P, L) ∈ S
  have compile : ∀ k ≤ s,
      ∃ (gs : List Gate) (φ : ℕ → Option ℕ),
        gs.length ≤ k ∧
        (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∧
        (∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < n + j) ∧
        (∀ w < n + k, wireSpec gs (φ w) (W w)) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨[], fun w => some w, Nat.le_refl 0, by simp, by simp, ?_⟩
      intro w hw
      refine ⟨fun h => (by cases h), ?_⟩
      intro r hr
      have hrw : w = r := Option.some.inj hr
      subst hrw
      refine ⟨by simpa using hw, ?_⟩
      intro P L
      have hlen : w < (List.ofFn (Fin.append P L)).length := by simpa [n] using hw
      change (List.ofFn (Fin.append P L)).getD w false = true ↔ (P, L) ∈ W w
      rw [List.getD_eq_getElem _ _ hlen, List.getElem_ofFn]
      by_cases hlt : w < N
      · let p : Fin N := ⟨w, hlt⟩
        have hcast : (⟨w, by omega⟩ : Fin (N + N)) = Fin.castAdd N p := Fin.ext rfl
        rw [hcast, Fin.append_left]
        have hw_eq : W w = {z : (Fin N → Bool) × (Fin N → Bool) | z.1 p = true} := (hbase p).1
        rw [hw_eq]
        rfl
      · let l : Fin N := ⟨w - N, by omega⟩
        have hnat : (⟨w, by omega⟩ : Fin (N + N)) = Fin.natAdd N l := Fin.ext (by dsimp [l]; omega)
        rw [hnat, Fin.append_right]
        have hw_id : N + l.val = w := by dsimp [l]; omega
        have hw_eq : W w = {z : (Fin N → Bool) × (Fin N → Bool) | z.2 l = true} := by
          rw [← hw_id]; exact (hbase l).2
        rw [hw_eq]
        rfl
    | succ k ih =>
      intro hks
      obtain ⟨gs, φ, hlen, hao, hrb, hspec⟩ := ih (Nat.le_of_succ_le hks)
      obtain ⟨a, ha, b, hb, hlaw⟩ := hsteps k (Nat.lt_of_succ_le hks)
      have ha' : a < n + k := ha
      have hb' : b < n + k := hb
      have hkeep : ∀ (rOpt : Option ℕ), wireSpec gs rOpt (W (n + k)) →
          ∃ (gs' : List Gate) (φ' : ℕ → Option ℕ),
            gs'.length ≤ k + 1 ∧
            (∀ g ∈ gs', (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∧
            (∀ j < gs'.length, ∀ i ∈ (gs'.getD j ⟨GateOp.or, []⟩).inputs, i < n + j) ∧
            (∀ w < n + (k + 1), wireSpec gs' (φ' w) (W w)) := by
        intro rOpt hrOpt
        refine ⟨gs, fun w => if w = n + k then rOpt else φ w, by omega, hao, hrb, ?_⟩
        intro w hw
        by_cases hwk : w = n + k
        · subst hwk
          simpa using hrOpt
        · simp only [hwk, ↓reduceIte]
          exact hspec w (by omega)
      have hpush : ∀ (op : GateOp) (ra rb : ℕ),
          (op = GateOp.and ∨ op = GateOp.or) →
          ra < n + gs.length → rb < n + gs.length →
          (∀ P L : Fin N → Bool,
            op.eval [(run gs (List.ofFn (Fin.append P L))).getD ra false,
                     (run gs (List.ofFn (Fin.append P L))).getD rb false] = true ↔
            (P, L) ∈ W (n + k)) →
          ∃ (gs' : List Gate) (φ' : ℕ → Option ℕ),
            gs'.length ≤ k + 1 ∧
            (∀ g ∈ gs', (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∧
            (∀ j < gs'.length, ∀ i ∈ (gs'.getD j ⟨GateOp.or, []⟩).inputs, i < n + j) ∧
            (∀ w < n + (k + 1), wireSpec gs' (φ' w) (W w)) := by
        intro op ra rb hop hra hrb_in heval
        let g : Gate := ⟨op, [ra, rb]⟩
        refine ⟨gs ++ [g], fun w => if w = n + k then some (n + gs.length) else φ w,
          by simp; omega, ?_, ?_, ?_⟩
        · intro g' hg'
          rcases List.mem_append.mp hg' with hmem | hmem
          · exact hao g' hmem
          · have : g' = g := by simpa using hmem
            subst this
            exact ⟨hop, rfl⟩
        · intro j hj i hi
          simp only [List.length_append, List.length_singleton] at hj
          by_cases hjl : j < gs.length
          · rw [List.getD_append _ _ _ _ hjl] at hi
            exact hrb j hjl i hi
          · have hjeq : j = gs.length := by omega
            subst hjeq
            rw [List.getD_append_right _ _ _ _ (Nat.le_refl _), Nat.sub_self] at hi
            simp only [List.getD_cons_zero, g, List.mem_cons, List.not_mem_nil, or_false] at hi
            rcases hi with rfl | rfl
            · exact hra
            · exact hrb_in
        · intro w hw
          by_cases hwk : w = n + k
          · subst hwk
            simp only [↓reduceIte]
            refine ⟨fun h => (by cases h), ?_⟩
            intro r hr
            have hreq : n + gs.length = r := Option.some.inj hr
            subst hreq
            refine ⟨by simp, ?_⟩
            intro P L
            have hxlen : (List.ofFn (Fin.append P L)).length = n := by simp [n]
            have hlast := run_snoc_last gs g (List.ofFn (Fin.append P L))
            rw [hxlen] at hlast
            rw [hlast]
            exact heval P L
          · simp only [hwk, ↓reduceIte]
            have hs := hspec w (by omega)
            refine ⟨hs.1, ?_⟩
            intro r hr
            obtain ⟨hrlt, hreval⟩ := hs.2 r hr
            refine ⟨by simp; omega, ?_⟩
            intro P L
            have hxlen : (List.ofFn (Fin.append P L)).length = n := by simp [n]
            have hlt' : r < (List.ofFn (Fin.append P L)).length + gs.length := by rw [hxlen]; exact hrlt
            rw [run_snoc_lt gs g (List.ofFn (Fin.append P L)) r hlt']
            exact hreval P L
      rcases hlaw with hU | hC | hE | ⟨hInter, _⟩
      · have hsa := hspec a ha'
        have hsb := hspec b hb'
        cases hφa : φ a with
        | none =>
          have hWa : W a = ∅ := hsa.1 hφa
          have hWeq : W (n + k) = W b := by simpa [hWa] using hU
          apply hkeep (φ b)
          exact ⟨fun hb0 => hWeq.trans (hsb.1 hb0), fun r hr =>
            ⟨(hsb.2 r hr).1, fun P L => by rw [hWeq]; exact (hsb.2 r hr).2 P L⟩⟩
        | some ra =>
          obtain ⟨hra, hrae⟩ := hsa.2 ra hφa
          cases hφb : φ b with
          | none =>
            have hWb : W b = ∅ := hsb.1 hφb
            have hWeq : W (n + k) = W a := by simpa [hWb] using hU
            apply hkeep (some ra)
            exact ⟨fun h => (by cases h), fun r hr => by
              have : ra = r := Option.some.inj hr
              subst this
              exact ⟨hra, fun P L => by rw [hWeq]; exact hrae P L⟩⟩
          | some rb =>
            obtain ⟨hrb_in, hrbe⟩ := hsb.2 rb hφb
            apply hpush GateOp.or ra rb (Or.inr rfl) hra hrb_in
            intro P L
            change (((run gs (List.ofFn (Fin.append P L))).getD ra false ||
                     ((run gs (List.ofFn (Fin.append P L))).getD rb false || false)) = true) ↔
              (P, L) ∈ W (n + k)
            rw [Bool.or_false, Bool.or_eq_true, hrae P L, hrbe P L, hU]
            rfl
      · have hsa := hspec a ha'
        apply hkeep (φ a)
        exact ⟨fun ha0 => hC.trans (hsa.1 ha0), fun r hr =>
          ⟨(hsa.2 r hr).1, fun P L => by rw [hC]; exact (hsa.2 r hr).2 P L⟩⟩
      · exact hkeep none ⟨fun _ => hE, fun _ h => (by cases h)⟩
      · have hsa := hspec a ha'
        have hsb := hspec b hb'
        cases hφa : φ a with
        | none =>
          have hWa : W a = ∅ := hsa.1 hφa
          have hWeq : W (n + k) = ∅ := by simpa [hWa] using hInter
          exact hkeep none ⟨fun _ => hWeq, fun _ h => (by cases h)⟩
        | some ra =>
          obtain ⟨hra, hrae⟩ := hsa.2 ra hφa
          cases hφb : φ b with
          | none =>
            have hWb : W b = ∅ := hsb.1 hφb
            have hWeq : W (n + k) = ∅ := by simpa [hWb] using hInter
            exact hkeep none ⟨fun _ => hWeq, fun _ h => (by cases h)⟩
          | some rb =>
            obtain ⟨hrb_in, hrbe⟩ := hsb.2 rb hφb
            apply hpush GateOp.and ra rb (Or.inl rfl) hra hrb_in
            intro P L
            change (((run gs (List.ofFn (Fin.append P L))).getD ra false &&
                     ((run gs (List.ofFn (Fin.append P L))).getD rb false && true)) = true) ↔
              (P, L) ∈ W (n + k)
            rw [Bool.and_true, Bool.and_eq_true, hrae P L, hrbe P L, hInter]
            rfl
  obtain ⟨gs, φ, hlen, hao, hrb, hspec⟩ := compile s (Nat.le_refl s)
  have hNpos : 0 < N := by nlinarith
  have ho_spec := hspec o ho
  have hφo_ne : φ o ≠ none := by
    intro hnone
    have hWo : W o = ∅ := ho_spec.1 hnone
    let l0 : Fin N := ⟨0, hNpos⟩
    have hcard_pos : 0 < Fintype.card { p : Fin N // I p l0 } := by rw [hdeg l0]; omega
    obtain ⟨⟨p0, hp0⟩⟩ := Fintype.card_pos_iff.mp hcard_pos
    have hmem := hpos p0 l0 hp0
    rw [hWo] at hmem
    exact hmem
  obtain ⟨out, hout⟩ : ∃ out, φ o = some out := Option.ne_none_iff_exists'.mp hφo_ne
  obtain ⟨_, hC_eval⟩ := ho_spec.2 out hout
  let C : Circuit := ⟨gs, out⟩
  have hCsize : C.size ≤ s := hlen
  have hAO2 : PEqualNP.TopForm.IsAO2 (N + N) C := by
    refine ⟨fun g hg => (hao g hg).1, ?_, fun g hg => (hao g hg).2⟩
    intro j hj i hi
    exact hrb j hj i hi
  have hmono : ∀ (a b : List Bool), a.length = b.length →
      (∀ i, a.getD i false = true → b.getD i false = true) →
      ∀ i, (run gs a).getD i false = true → (run gs b).getD i false = true := by
    have hstep_mono : ∀ (g : Gate), (g.op = GateOp.and ∨ g.op = GateOp.or) →
        ∀ (a b : List Bool), a.length = b.length →
        (∀ i, a.getD i false = true → b.getD i false = true) →
        ∀ i, (step a g).getD i false = true → (step b g).getD i false = true := by
      intro g hg a b hlab hab i hi
      by_cases hlt : i < a.length
      · rw [List.getD_append _ _ _ _ hlt] at hi
        rw [List.getD_append _ _ _ _ (hlab ▸ hlt)]
        exact hab i hi
      · rw [List.getD_append_right _ _ _ _ (by omega)] at hi
        rw [List.getD_append_right _ _ _ _ (by omega), ← hlab]
        cases hd : i - a.length with
        | zero =>
          simp only [hd, List.getD_cons_zero] at hi ⊢
          rcases hg with hop | hop
          · rw [hop] at hi ⊢
            change (g.inputs.map fun j => a.getD j false).all id = true at hi
            change (g.inputs.map fun j => b.getD j false).all id = true
            simp only [List.all_eq_true, List.mem_map, id_eq] at hi ⊢
            rintro _ ⟨j, hj, rfl⟩
            exact hab j (hi _ ⟨j, hj, rfl⟩)
          · rw [hop] at hi ⊢
            change (g.inputs.map fun j => a.getD j false).any id = true at hi
            change (g.inputs.map fun j => b.getD j false).any id = true
            simp only [List.any_eq_true, List.mem_map, id_eq] at hi ⊢
            rcases hi with ⟨_, ⟨j, hj, rfl⟩, htrue⟩
            exact ⟨_, ⟨j, hj, rfl⟩, hab j htrue⟩
        | succ m =>
          simp [hd] at hi
    have hfold : ∀ (ls : List Gate), (∀ g ∈ ls, g.op = GateOp.and ∨ g.op = GateOp.or) →
        ∀ (a b : List Bool), a.length = b.length →
        (∀ i, a.getD i false = true → b.getD i false = true) →
        ∀ i, (run ls a).getD i false = true → (run ls b).getD i false = true := by
      intro ls
      induction ls with
      | nil => intro _ a b _ hab; exact hab
      | cons g ls ih =>
        intro hls a b hlab hab
        exact ih (fun g' hg' => hls g' (List.mem_cons_of_mem _ hg')) (step a g) (step b g)
          (by simp [step, hlab]) (hstep_mono g (hls g List.mem_cons_self) a b hlab hab)
    exact hfold gs (fun g hg => (hao g hg).1)
  have hC4 : ∀ (p1 p2 l1 l2 : Fin N), p1 ≠ p2 → l1 ≠ l2 → ¬(I p1 l1 ∧ I p2 l1 ∧ I p1 l2 ∧ I p2 l2) := by
    intro p1 p2 l1 l2 hp hl h
    exact hl ((huniq p1 p2 hp).unique ⟨h.1, h.2.1⟩ ⟨h.2.2.1, h.2.2.2⟩)
  have hsound_q : ∀ (z : Fin (N + N) → Bool),
      Fintype.card { l : Fin N // z (Fin.natAdd N l) = true } ≤ q →
      (¬∃ (p l : Fin N), I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
      circuitFun (N + N) C z = false := by
    intro z hL hno
    let P : Fin N → Bool := fun p => z (Fin.castAdd N p)
    let L : Fin N → Bool := fun l => z (Fin.natAdd N l)
    let PL : Fin N → Bool := fun p => decide (¬∃ l : Fin N, I p l ∧ L l = true)
    have hz_eq : z = Fin.append P L := by
      funext k
      refine Fin.addCases (fun p => ?_) (fun l => ?_) k
      · simp only [Fin.append_left, P]
      · simp only [Fin.append_right, L]
    have hle : ∀ i : ℕ, (List.ofFn z).getD i false = true →
        (List.ofFn (Fin.append PL L)).getD i false = true := by
      intro i hi
      by_cases hlt : i < N + N
      · rw [List.getD_eq_getElem _ _ (by simpa using hlt), List.getElem_ofFn] at hi
        rw [List.getD_eq_getElem _ _ (by simpa using hlt), List.getElem_ofFn]
        rw [hz_eq] at hi
        have hk : (⟨i, hlt⟩ : Fin (N + N)) = if h : i < N then Fin.castAdd N ⟨i, h⟩
            else Fin.natAdd N ⟨i - N, by omega⟩ := by
          split_ifs with h
          · exact Fin.ext rfl
          · exact Fin.ext (by simp; omega)
        rw [hk] at hi ⊢
        split_ifs at hi ⊢ with h
        · rw [Fin.append_left] at hi ⊢
          simp only [PL, decide_eq_true_eq]
          rintro ⟨l, hIpl, hLl⟩
          exact hno ⟨⟨i, h⟩, l, hIpl, hi, hLl⟩
        · rw [Fin.append_right] at hi ⊢
          exact hi
      · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
        cases hi
    cases hcz : circuitFun (N + N) C z with
    | false => rfl
    | true =>
      have htrue : circuitFun (N + N) C (Fin.append PL L) = true :=
        hmono (List.ofFn z) (List.ofFn (Fin.append PL L)) (by simp) hle out hcz
      exact False.elim (hneg L hL ((hC_eval PL L).mp htrue))
  have hsound_1 : ∀ (z : Fin (N + N) → Bool),
      Fintype.card { l : Fin N // z (Fin.natAdd N l) = true } ≤ 1 →
      (¬∃ (p l : Fin N), I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
      circuitFun (N + N) C z = false :=
    fun z hL hno => hsound_q z (hL.trans (by omega)) hno
  have hpair_eq : ∀ (p l : Fin N),
      (fun k : Fin (N + N) => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)) =
      Fin.append (fun u : Fin N => decide (u = p)) (fun v : Fin N => decide (v = l)) := by
    intro p l
    funext k
    refine Fin.addCases (fun a => ?_) (fun b => ?_) k
    · have hne : Fin.castAdd N a ≠ Fin.natAdd N l := by
        intro e
        have hv := congrArg Fin.val e
        simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
        omega
      simp only [Fin.append_left, hne, or_false, Fin.castAdd_inj]
    · have hne : Fin.natAdd N b ≠ Fin.castAdd N p := by
        intro e
        have hv := congrArg Fin.val e
        simp only [Fin.val_natAdd, Fin.val_castAdd] at hv
        omega
      have hiff : Fin.natAdd N b = Fin.natAdd N l ↔ b = l := by
        constructor
        · intro e
          apply Fin.ext
          have hv := congrArg Fin.val e
          simp only [Fin.val_natAdd] at hv
          omega
        · rintro rfl; rfl
      simp only [Fin.append_right, hne, false_or, hiff]
  have hacc : ∀ (p l : Fin N), I p l →
      circuitFun (N + N) C (fun k : Fin (N + N) => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)) = true := by
    intro p l hIpl
    rw [hpair_eq p l]
    exact (hC_eval _ _).mpr (hpos p l hIpl)
  have hb1 := h1 N I C hC4 hAO2 hsound_1
  have hb2 := h2 q N I C (by omega) hN hdeg huniq hAO2 hsound_q
  have hb3 := h3 q N I C (by omega) hN hdeg huniq hAO2 hsound_q
  let E : Finset (Fin N × Fin N) := Finset.univ.filter (fun e => I e.1 e.2)
  let Ey : Finset (Fin N × Fin N) := Finset.univ.filter (fun e =>
    I e.1 e.2 ∧ PEqualNP.ReadK.lineSingle C (N + N) (fun k => decide (N ≤ k)) e.1.val (N + e.2.val) = true)
  let Ex : Finset (Fin N × Fin N) := Finset.univ.filter (fun e =>
    I e.1 e.2 ∧ PEqualNP.ReadK.lineSingle C (N + N) (fun k => decide (k < N)) e.1.val (N + e.2.val) = true)
  let Ed : Finset (Fin N × Fin N) := Finset.univ.filter (fun e =>
    I e.1 e.2 ∧
    circuitFun (N + N) C (fun k => decide (k = Fin.castAdd N e.1 ∨ k = Fin.natAdd N e.2)) = true ∧
    PEqualNP.ReadK.lineSingle C (N + N) (fun k => decide (N ≤ k)) e.1.val (N + e.2.val) = false ∧
    PEqualNP.ReadK.lineSingle C (N + N) (fun k => decide (k < N)) e.1.val (N + e.2.val) = false)
  have hEy : Ey.card ≤ 10 * C.size := by simpa only [Fintype.card_subtype] using hb1
  have hEx : Ex.card ≤ 10 * C.size := by simpa only [Fintype.card_subtype] using hb2
  have hEd : Ed.card ≤ 24 * C.size := by simpa only [Fintype.card_subtype] using hb3
  have hE_sub : E ⊆ Ey ∪ (Ex ∪ Ed) := by
    intro e he
    have hI : I e.1 e.2 := (Finset.mem_filter.mp he).2
    cases hly : PEqualNP.ReadK.lineSingle C (N + N) (fun k => decide (N ≤ k)) e.1.val (N + e.2.val) with
    | true =>
      exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hI, hly⟩)
    | false =>
      cases hlx : PEqualNP.ReadK.lineSingle C (N + N) (fun k => decide (k < N)) e.1.val (N + e.2.val) with
      | true =>
        exact Finset.mem_union_right _ (Finset.mem_union_left _
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hI, hlx⟩))
      | false =>
        exact Finset.mem_union_right _ (Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hI, hacc e.1 e.2 hI, hly, hlx⟩))
  have hE_eq : E = (Finset.univ : Finset (Fin N)).biUnion
      (fun l => (Finset.univ.filter (fun p : Fin N => I p l)).image (fun p => (p, l))) := by
    ext ⟨p, l⟩
    simp [E]
  have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin N)))
      (fun l : Fin N => (Finset.univ.filter (fun p : Fin N => I p l)).image (fun p => (p, l))) := by
    intro l1 _ l2 _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro x hx1 hx2
    obtain ⟨p1, _, rfl⟩ := Finset.mem_image.mp hx1
    obtain ⟨p2, _, heq⟩ := Finset.mem_image.mp hx2
    exact hne (Prod.mk.inj heq).2.symm
  have hE_card : E.card = N * (q + 1) := by
    rw [hE_eq, Finset.card_biUnion hdisj]
    have hterm : ∀ l : Fin N,
        ((Finset.univ.filter (fun p : Fin N => I p l)).image (fun p => (p, l))).card = q + 1 := by
      intro l
      rw [Finset.card_image_of_injective _ (fun a b h => (Prod.mk.inj h).1)]
      simpa only [Fintype.card_subtype] using hdeg l
    simp [hterm]
  have hE_le : E.card ≤ Ey.card + (Ex.card + Ed.card) :=
    (Finset.card_le_card hE_sub).trans
      ((Finset.card_union_le _ _).trans (Nat.add_le_add_left (Finset.card_union_le _ _) _))
  have hNq_le : N * q ≤ N * (q + 1) := Nat.mul_le_mul_left N (Nat.le_succ q)
  omega
