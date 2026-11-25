import Mathlib.Data.Fintype.Fin
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm PEqualNP.ReadK PEqualNP.GenericRejection PEqualNP.TwoColour

theorem PEqualNP.Outside.R_meta_3698_9
    (hBounded : ∀ (q N : ℕ) (S : Fin N → Finset (Fin N)) (C : Circuit) (H : Finset (Fin N × Fin N)),
      87 ≤ q → q ≤ 299 → N = q ^ 2 + q + 1 →
      (∀ l : Fin N, (S l).card = q + 1) →
      (∀ p : Fin N, Fintype.card { l : Fin N // p ∈ S l } = q + 1) →
      (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, p ∈ S l ∧ p' ∈ S l) →
      (∀ l l' : Fin N, l ≠ l' → ∃! p : Fin N, p ∈ S l ∧ p ∈ S l') →
      IsAO2 (N + N) C → N + N ≤ C.output → C.output < N + N + C.size →
      4513 ≤ C.size → 24 * C.size < N * (q + 1) →
      (∀ X Y : Finset (Fin N), Y.card ≤ q → IsFalseInput S X Y → C.eval (incidenceInput X Y) = false) →
      (∀ e ∈ H, e.1 ∈ S e.2 ∧ C.eval (incidenceInput {e.1} {e.2}) = true ∧
        lineSingle C (N + N) (fun i => decide (N ≤ i)) e.1.val (N + e.2.val) = false ∧
        lineSingle C (N + N) (fun i => decide (i < N)) e.1.val (N + e.2.val) = false) →
      (∀ w : Fin (N + N),
        0 < (H.filter fun e => w = Fin.castAdd N e.1 ∨ w = Fin.natAdd N e.2).card →
        1 ≤ (C.gates.filter fun g => g.inputs.contains w.val).length ∧
        24 * (C.gates.filter fun g => g.inputs.contains w.val).length <
          (H.filter fun e => w = Fin.castAdd N e.1 ∨ w = Fin.natAdd N e.2).card) →
      H.card ≤ 24 * C.size)
    (hPureOr : ∀ (q N : ℕ) (S : Fin N → Finset (Fin N)) (C : Circuit) (H : Finset (Fin N × Fin N)),
      300 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l : Fin N, (S l).card = q + 1) →
      (∀ p : Fin N, Fintype.card { l : Fin N // p ∈ S l } = q + 1) →
      (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, p ∈ S l ∧ p' ∈ S l) →
      (∀ l l' : Fin N, l ≠ l' → ∃! p : Fin N, p ∈ S l ∧ p ∈ S l') →
      IsAO2 (N + N) C → N + N ≤ C.output → C.output < N + N + C.size →
      4513 ≤ C.size → 24 * C.size < N * (q + 1) →
      tCount (N + N) C (fun i => decide (N ≤ i)) = 0 →
      (∀ X Y : Finset (Fin N), Y.card ≤ q → IsFalseInput S X Y → C.eval (incidenceInput X Y) = false) →
      (∀ e ∈ H, e.1 ∈ S e.2 ∧ C.eval (incidenceInput {e.1} {e.2}) = true ∧
        lineSingle C (N + N) (fun i => decide (N ≤ i)) e.1.val (N + e.2.val) = false ∧
        lineSingle C (N + N) (fun i => decide (i < N)) e.1.val (N + e.2.val) = false) →
      (∀ w : Fin (N + N),
        0 < (H.filter fun e => w = Fin.castAdd N e.1 ∨ w = Fin.natAdd N e.2).card →
        1 ≤ (C.gates.filter fun g => g.inputs.contains w.val).length ∧
        24 * (C.gates.filter fun g => g.inputs.contains w.val).length <
          (H.filter fun e => w = Fin.castAdd N e.1 ∨ w = Fin.natAdd N e.2).card) →
      H.card ≤ 24 * C.size)
    (hTwoCol : ∀ (q N : ℕ) (S : Fin N → Finset (Fin N)) (C : Circuit) (H : Finset (Fin N × Fin N)),
      300 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l : Fin N, (S l).card = q + 1) →
      (∀ p : Fin N, Fintype.card { l : Fin N // p ∈ S l } = q + 1) →
      (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, p ∈ S l ∧ p' ∈ S l) →
      (∀ l l' : Fin N, l ≠ l' → ∃! p : Fin N, p ∈ S l ∧ p ∈ S l') →
      IsAO2 (N + N) C → N + N ≤ C.output → C.output < N + N + C.size →
      4513 ≤ C.size → 24 * C.size < N * (q + 1) →
      0 < tCount (N + N) C (fun i => decide (N ≤ i)) →
      (∀ X Y : Finset (Fin N), Y.card ≤ q → IsFalseInput S X Y → C.eval (incidenceInput X Y) = false) →
      (∀ e ∈ H, e.1 ∈ S e.2 ∧ C.eval (incidenceInput {e.1} {e.2}) = true ∧
        lineSingle C (N + N) (fun i => decide (N ≤ i)) e.1.val (N + e.2.val) = false ∧
        lineSingle C (N + N) (fun i => decide (i < N)) e.1.val (N + e.2.val) = false) →
      (∀ w : Fin (N + N),
        0 < (H.filter fun e => w = Fin.castAdd N e.1 ∨ w = Fin.natAdd N e.2).card →
        1 ≤ (C.gates.filter fun g => g.inputs.contains w.val).length ∧
        24 * (C.gates.filter fun g => g.inputs.contains w.val).length <
          (H.filter fun e => w = Fin.castAdd N e.1 ∨ w = Fin.natAdd N e.2).card) →
      H.card ≤ 24 * C.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [DecidableRel x3],   (87 : ℕ) ≤ x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) →         (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) →           have x9 : PEqualNP.CircuitLowerBounds.Circuit → Finset (Fin x2 × Fin x2) := fun (x9 : PEqualNP.CircuitLowerBounds.Circuit) => {x10 : Fin x2 × Fin x2 | x3 x10.1 x10.2 ∧ (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x9 fun (x11 : Fin (x2 + x2)) => Decidable.decide (x11 = Fin.castAdd x2 x10.1 ∨ x11 = Fin.natAdd x2 x10.2)) = Bool.true ∧ PEqualNP.ReadK.lineSingle x9 (x2 + x2) (fun (x11 : ℕ) => Decidable.decide (x2 ≤ x11)) (↑x10.1) (x2 + ↑x10.2) = Bool.false ∧ PEqualNP.ReadK.lineSingle x9 (x2 + x2) (fun (x11 : ℕ) => Decidable.decide (x11 < x2)) (↑x10.1) (x2 + ↑x10.2) = Bool.false};           have x10 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x10 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x11 : Fin (x2 + x2) → Bool), Fintype.card { x12 : Fin x2 // x11 (Fin.natAdd x2 x12) = Bool.true } ≤ x1 → (¬∃ (x13 : Fin x2) (x14 : Fin x2), x3 x13 x14 ∧ x11 (Fin.castAdd x2 x13) = Bool.true ∧ x11 (Fin.natAdd x2 x14) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x10 x11 = Bool.false;           have x11 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x11 : PEqualNP.CircuitLowerBounds.Circuit) =>             ∀ (x12 : Fin (x2 + x2)),               have x13 : ℕ := {x13 ∈ x9 x11 | x12 = Fin.castAdd x2 x13.1 ∨ x12 = Fin.natAdd x2 x13.2}.card;               (0 : ℕ) < x13 → (24 : ℕ) * Max.max (1 : ℕ) (Fintype.card { x15 : Fin x11.size // ↑x12 ∈ (x11.gates.get x15).inputs }) < x13;           ∀ (x12 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (x2 + x2) x12 → x10 x12 → (4513 : ℕ) ≤ x12.size → x11 x12 → (x9 x12).card ≤ (24 : ℕ) * x12.size := by
  intro q N I instI hq hN hcol huniq
  dsimp only
  intro C hao hsound hsize hdense
  let H : Finset (Fin N × Fin N) :=
    Finset.univ.filter fun e : Fin N × Fin N =>
      I e.1 e.2 ∧
      (circuitFun (N + N) C fun i : Fin (N + N) =>
        Decidable.decide (i = Fin.castAdd N e.1 ∨ i = Fin.natAdd N e.2)) = true ∧
      lineSingle C (N + N) (fun i : ℕ => Decidable.decide (N ≤ i)) e.1.val (N + e.2.val) = false ∧
      lineSingle C (N + N) (fun i : ℕ => Decidable.decide (i < N)) e.1.val (N + e.2.val) = false
  change H.card ≤ 24 * C.size
  rcases H.eq_empty_or_nonempty with hHemp | hHne
  · rw [hHemp]
    simp
  obtain ⟨e0, he0⟩ := hHne
  let S : Fin N → Finset (Fin N) := fun l => Finset.univ.filter fun p : Fin N => I p l
  have hS_mem : ∀ (p l : Fin N), p ∈ S l ↔ I p l := by
    intro p l
    simp [S]
  have hS_col : ∀ l : Fin N, (S l).card = q + 1 := by
    intro l
    have hc := hcol l
    rw [Fintype.card_subtype] at hc
    exact hc
  have htot_card : (Finset.univ.filter fun e : Fin N × Fin N => I e.1 e.2).card = N * (q + 1) := by
    have heq : (Finset.univ.filter fun e : Fin N × Fin N => I e.1 e.2) =
        (Finset.univ : Finset (Fin N)).biUnion
          (fun l => (S l).image (fun p => (p, l))) := by
      ext e
      rcases e with ⟨p, l⟩
      simp [S]
    have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin N)))
        (fun l : Fin N => (S l).image (fun p => (p, l))) := by
      intro l1 _ l2 _ hne
      rw [Function.onFun, Finset.disjoint_left]
      intro e he1 he2
      obtain ⟨p1, _, rfl⟩ := Finset.mem_image.mp he1
      obtain ⟨p2, _, heq2⟩ := Finset.mem_image.mp he2
      exact hne (Prod.mk.inj heq2).2.symm
    rw [heq, Finset.card_biUnion hdisj]
    have heach : ∀ l : Fin N, ((S l).image (fun p => (p, l))).card = q + 1 := by
      intro l
      rw [Finset.card_image_of_injective _ (fun a b h => (Prod.mk.inj h).1), hS_col l]
    simp [heach]
  have hH_le_tot : H.card ≤ N * (q + 1) := by
    rw [← htot_card]
    apply Finset.card_le_card
    intro e he
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp he).2.1⟩
  by_cases hbig : N * (q + 1) ≤ 24 * C.size
  · exact hH_le_tot.trans hbig
  have hsubcubic : 24 * C.size < N * (q + 1) := Nat.lt_of_not_ge hbig
  have hS_uniqP : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, p ∈ S l ∧ p' ∈ S l := by
    intro p p' hne
    obtain ⟨l, hl, hluniq⟩ := huniq p p' hne
    refine ⟨l, ⟨(hS_mem p l).mpr hl.1, (hS_mem p' l).mpr hl.2⟩, ?_⟩
    intro l' hl'
    exact hluniq l' ⟨(hS_mem p l').mp hl'.1, (hS_mem p' l').mp hl'.2⟩
  have hfour : ∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' →
      ¬ (p ∈ S l ∧ p ∈ S l' ∧ p' ∈ S l ∧ p' ∈ S l') := by
    intro p p' l l' hp hl h4
    exact hl ((hS_uniqP p p' hp).unique ⟨h4.1, h4.2.2.1⟩ ⟨h4.2.1, h4.2.2.2⟩)
  have hS_row : ∀ p : Fin N, (Finset.univ.filter fun l : Fin N => p ∈ S l).card = q + 1 := by
    clear * - hq hN hS_col hS_uniqP hfour
    intro p
    let Lp : Finset (Fin N) := Finset.univ.filter fun l : Fin N => p ∈ S l
    have hpart : (Finset.univ.erase p : Finset (Fin N)) =
        Lp.biUnion (fun l => (S l).erase p) := by
      ext p'
      simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_biUnion, Lp,
        Finset.mem_filter, true_and]
      constructor
      · intro hne
        obtain ⟨l, hl, _⟩ := hS_uniqP p p' hne.symm
        exact ⟨l, hl.1, hne, hl.2⟩
      · intro hex
        obtain ⟨_, _, hne, _⟩ := hex
        exact hne
    have hdisj : Set.PairwiseDisjoint (↑Lp) (fun l => (S l).erase p) := by
      intro l1 hl1 l2 hl2 hne
      rw [Function.onFun, Finset.disjoint_left]
      intro p' hp1 hp2
      have h1 := Finset.mem_erase.mp hp1
      have h2 := Finset.mem_erase.mp hp2
      have hl1' := (Finset.mem_filter.mp hl1).2
      have hl2' := (Finset.mem_filter.mp hl2).2
      exact hfour p p' l1 l2 h1.1.symm hne ⟨hl1', hl2', h1.2, h2.2⟩
    have hcard_eq := congrArg Finset.card hpart
    rw [Finset.card_erase_of_mem (Finset.mem_univ p), Finset.card_univ, Fintype.card_fin,
      Finset.card_biUnion hdisj] at hcard_eq
    have hsum_q : ∑ l ∈ Lp, ((S l).erase p).card = Lp.card * q := by
      have heach : ∀ l ∈ Lp, ((S l).erase p).card = q := by
        intro l hl
        have hmem : p ∈ S l := (Finset.mem_filter.mp hl).2
        rw [Finset.card_erase_of_mem hmem, hS_col l]
        omega
      rw [Finset.sum_congr rfl heach]
      simp
    rw [hsum_q] at hcard_eq
    have hN1 : N - 1 = (q + 1) * q := by
      rw [hN, Nat.add_sub_cancel]
      ring
    rw [hN1] at hcard_eq
    exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < q) hcard_eq.symm
  have hS_uniqL : ∀ l l' : Fin N, l ≠ l' → ∃! p : Fin N, p ∈ S l ∧ p ∈ S l' := by
    clear * - hq hN hS_col hS_row hfour
    intro l l' hll'
    let F : Fin N → Finset (Fin N) := fun p =>
      (Finset.univ.filter fun l'' : Fin N => p ∈ S l'').erase l
    have hdisj : Set.PairwiseDisjoint (↑(S l)) F := by
      intro p1 hp1 p2 hp2 hne
      rw [Function.onFun, Finset.disjoint_left]
      intro l'' hl1 hl2
      have h1 := Finset.mem_erase.mp hl1
      have h2 := Finset.mem_erase.mp hl2
      have hp1' := (Finset.mem_filter.mp h1.2).2
      have hp2' := (Finset.mem_filter.mp h2.2).2
      exact hfour p1 p2 l l'' hne h1.1.symm ⟨hp1, hp1', hp2, hp2'⟩
    have hsub : (S l).biUnion F ⊆ Finset.univ.erase l := by
      intro l'' hl''
      obtain ⟨p, _, hpF⟩ := Finset.mem_biUnion.mp hl''
      exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hpF).1, Finset.mem_univ _⟩
    have hcard_bi : ((S l).biUnion F).card = N - 1 := by
      rw [Finset.card_biUnion hdisj]
      have heach : ∀ p ∈ S l, (F p).card = q := by
        intro p hp
        have hmem : l ∈ Finset.univ.filter (fun l'' : Fin N => p ∈ S l'') :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩
        rw [Finset.card_erase_of_mem hmem, hS_row p]
        omega
      rw [Finset.sum_congr rfl heach]
      simp only [Finset.sum_const, smul_eq_mul]
      rw [hS_col l, hN, Nat.add_sub_cancel]
      ring
    have hcard_er : (Finset.univ.erase l : Finset (Fin N)).card = N - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ l), Finset.card_univ, Fintype.card_fin]
    have heq : (S l).biUnion F = Finset.univ.erase l :=
      Finset.eq_of_subset_of_card_le hsub (by omega)
    have hl'mem : l' ∈ (S l).biUnion F := by
      rw [heq]
      exact Finset.mem_erase.mpr ⟨hll'.symm, Finset.mem_univ _⟩
    obtain ⟨p, hp, hpF⟩ := Finset.mem_biUnion.mp hl'mem
    have hp' : p ∈ S l' := (Finset.mem_filter.mp (Finset.mem_erase.mp hpF).2).2
    refine ⟨p, ⟨hp, hp'⟩, ?_⟩
    intro p2 hp2
    by_contra hne
    exact hfour p2 p l l' hne hll' ⟨hp2.1, hp2.2, hp, hp'⟩
  have separate : ∀ p l : Fin N, Fin.castAdd N p ≠ Fin.natAdd N l := by
    clear * -
    intro p l heq
    have hv := congrArg Fin.val heq
    simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
    have := p.isLt
    omega
  have singleton_false : ∀ w : Fin (N + N),
      circuitFun (N + N) C (fun i => decide (i = w)) = false := by
    clear * - hq hsound separate
    intro w
    apply hsound
    · apply Nat.le_trans _ (by omega : 1 ≤ q)
      rw [Fintype.card_subtype]
      apply Finset.card_le_one.mpr
      intro a ha b hb
      have ha' : Fin.natAdd N a = w := of_decide_eq_true (Finset.mem_filter.mp ha).2
      have hb' : Fin.natAdd N b = w := of_decide_eq_true (Finset.mem_filter.mp hb).2
      exact Fin.ext (Nat.add_left_cancel (congrArg Fin.val (ha'.trans hb'.symm)))
    · intro hex
      obtain ⟨p, l, _, hp, hl⟩ := hex
      exact separate p l ((of_decide_eq_true hp).trans (of_decide_eq_true hl).symm)
  let runW : List Gate → List Bool → List Bool := fun gs xs =>
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) xs
  have runW_len : ∀ (gs : List Gate) (xs : List Bool),
      (runW gs xs).length = xs.length + gs.length := by
    clear * -
    intro gs
    induction gs with
    | nil => intro xs; simp [runW]
    | cons g rest ih =>
      intro xs
      have hstep : runW (g :: rest) xs =
          runW rest (xs ++ [g.op.eval (g.inputs.map fun i => xs.getD i false)]) := rfl
      rw [hstep, ih]
      simp
      omega
  have runW_keep : ∀ (gs : List Gate) (xs : List Bool) (i : ℕ), i < xs.length →
      (runW gs xs).getD i false = xs.getD i false := by
    clear * -
    intro gs
    induction gs with
    | nil => intro xs i _; rfl
    | cons g rest ih =>
      intro xs i hi
      have hstep : runW (g :: rest) xs =
          runW rest (xs ++ [g.op.eval (g.inputs.map fun k => xs.getD k false)]) := rfl
      rw [hstep, ih _ i (by simp; omega)]
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have hout_lo : N + N ≤ C.output := by
    by_contra hlt'
    have hlt : C.output < N + N := Nat.lt_of_not_ge hlt'
    let w : Fin (N + N) := ⟨C.output, hlt⟩
    let xw : Fin (N + N) → Bool := fun i => decide (i = w)
    have h1 : circuitFun (N + N) C xw = true := by
      show (runW C.gates (List.ofFn xw)).getD C.output false = true
      rw [runW_keep C.gates (List.ofFn xw) C.output (by simp; exact hlt)]
      rw [List.getD_eq_getElem _ _ (by simp; exact hlt), List.getElem_ofFn]
      simp [xw, w]
    rw [singleton_false w] at h1
    cases h1
  have hout_hi : C.output < N + N + C.size := by
    by_contra hge'
    have hge : N + N + C.size ≤ C.output := Nat.le_of_not_lt hge'
    have he0_acc : (circuitFun (N + N) C fun i : Fin (N + N) =>
        Decidable.decide (i = Fin.castAdd N e0.1 ∨ i = Fin.natAdd N e0.2)) = true :=
      (Finset.mem_filter.mp he0).2.2.1
    have hfalse : (circuitFun (N + N) C fun i : Fin (N + N) =>
        Decidable.decide (i = Fin.castAdd N e0.1 ∨ i = Fin.natAdd N e0.2)) = false := by
      show (runW C.gates _).getD C.output false = false
      apply List.getD_eq_default
      rw [runW_len, List.length_ofFn]
      exact hge
    rw [hfalse] at he0_acc
    cases he0_acc
  have hinc_eq : ∀ (X Y : Finset (Fin N)),
      incidenceInput X Y =
        List.ofFn (fun i : Fin (N + N) =>
          if h : i.val < N then decide ((⟨i.val, h⟩ : Fin N) ∈ X)
          else decide ((⟨i.val - N, by omega⟩ : Fin N) ∈ Y)) := by
    clear * -
    intro X Y
    change (List.ofFn (fun p : Fin N => decide (p ∈ X)) ++
        List.ofFn (fun l : Fin N => decide (l ∈ Y))) = _
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      simp only [List.length_ofFn] at h2
      rw [List.getElem_ofFn]
      by_cases hi : i < N
      · simp only [hi, ↓reduceDIte]
        rw [List.getElem_append_left (by simp; exact hi), List.getElem_ofFn]
      · simp only [hi, ↓reduceDIte]
        rw [List.getElem_append_right (by simp; omega)]
        simp only [List.length_ofFn, List.getElem_ofFn]
  have hsound_inc : ∀ X Y : Finset (Fin N), Y.card ≤ q → IsFalseInput S X Y →
      C.eval (incidenceInput X Y) = false := by
    clear * - hsound hS_mem hinc_eq
    intro X Y hYcard hfalse
    let z : Fin (N + N) → Bool := fun i =>
      if h : i.val < N then decide ((⟨i.val, h⟩ : Fin N) ∈ X)
      else decide ((⟨i.val - N, by omega⟩ : Fin N) ∈ Y)
    rw [hinc_eq X Y]
    show circuitFun (N + N) C z = false
    apply hsound z
    · have hcard : Fintype.card { l : Fin N // z (Fin.natAdd N l) = true } = Y.card := by
        rw [Fintype.card_subtype]
        congr 1
        ext l
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, z, Fin.val_natAdd]
        have hnlt : ¬ N + l.val < N := by omega
        simp [hnlt]
      omega
    · intro hex
      obtain ⟨p, l, hI, hp, hl⟩ := hex
      have hpX : p ∈ X := by
        simp only [z, Fin.val_castAdd, p.isLt, ↓reduceDIte, decide_eq_true_eq] at hp
        exact hp
      have hlY : l ∈ Y := by
        have hnlt : ¬ N + l.val < N := by omega
        simp only [z, Fin.val_natAdd, hnlt, ↓reduceDIte, Nat.add_sub_cancel_left,
          decide_eq_true_eq] at hl
        exact hl
      exact Finset.disjoint_left.mp (hfalse l hlY) ((hS_mem p l).mpr hI) hpX
  have hH_spec : ∀ e ∈ H, e.1 ∈ S e.2 ∧ C.eval (incidenceInput {e.1} {e.2}) = true ∧
      lineSingle C (N + N) (fun i => decide (N ≤ i)) e.1.val (N + e.2.val) = false ∧
      lineSingle C (N + N) (fun i => decide (i < N)) e.1.val (N + e.2.val) = false := by
    clear * - hS_mem hinc_eq
    intro e he
    obtain ⟨hI, hacc, hL, hP⟩ := (Finset.mem_filter.mp he).2
    refine ⟨(hS_mem e.1 e.2).mpr hI, ?_, hL, hP⟩
    rw [hinc_eq {e.1} {e.2}]
    have hfn : (fun i : Fin (N + N) =>
        if h : i.val < N then decide ((⟨i.val, h⟩ : Fin N) ∈ ({e.1} : Finset (Fin N)))
        else decide ((⟨i.val - N, by omega⟩ : Fin N) ∈ ({e.2} : Finset (Fin N)))) =
        (fun i : Fin (N + N) =>
          Decidable.decide (i = Fin.castAdd N e.1 ∨ i = Fin.natAdd N e.2)) := by
      funext i
      by_cases hi : i.val < N
      · simp only [hi, ↓reduceDIte, Finset.mem_singleton]
        apply decide_eq_decide.mpr
        constructor
        · intro heq
          have hv := congrArg Fin.val heq
          dsimp only at hv
          exact Or.inl (Fin.ext (by simp only [Fin.val_castAdd]; exact hv))
        · intro hor
          rcases hor with h1 | h2
          · have hv := congrArg Fin.val h1
            simp only [Fin.val_castAdd] at hv
            exact Fin.ext (by dsimp only; exact hv)
          · have hv := congrArg Fin.val h2
            simp only [Fin.val_natAdd] at hv
            omega
      · simp only [hi, ↓reduceDIte, Finset.mem_singleton]
        apply decide_eq_decide.mpr
        constructor
        · intro heq
          have hv := congrArg Fin.val heq
          dsimp only at hv
          exact Or.inr (Fin.ext (by simp only [Fin.val_natAdd]; omega))
        · intro hor
          rcases hor with h1 | h2
          · have hv := congrArg Fin.val h1
            simp only [Fin.val_castAdd] at hv
            have := e.1.isLt
            omega
          · have hv := congrArg Fin.val h2
            simp only [Fin.val_natAdd] at hv
            exact Fin.ext (by dsimp only; omega)
    rw [hfn]
    exact hacc
  have hfan_eq : ∀ i : ℕ,
      Fintype.card { j : Fin C.size // i ∈ (C.gates.get j).inputs } =
        (C.gates.filter fun g => g.inputs.contains i).length := by
    clear * -
    intro i
    have hcp : ∀ (gs : List Gate) (p : Gate → Bool),
        gs.countP p = (gs.filter p).length := by
      intro gs p
      induction gs with
      | nil => rfl
      | cons g rest ih =>
        rw [List.countP_cons, List.filter_cons]
        cases p g <;> simp [ih]
    rw [← hcp C.gates (fun g => g.inputs.contains i)]
    calc Fintype.card { j : Fin C.size // i ∈ (C.gates.get j).inputs }
      _ = (List.ofFn fun j : Fin C.size => C.gates.get j).countP
            (fun g => g.inputs.contains i) := by
          rw [List.countP_ofFn, Fintype.card_subtype]
          congr 1
      _ = C.gates.countP (fun g => g.inputs.contains i) := by
          change (List.ofFn fun j : Fin C.gates.length => C.gates[j.val]).countP _ = _
          rw [List.ofFn_getElem]
  have runW_unused : ∀ (gs : List Gate) (v : ℕ),
      (∀ g ∈ gs, v ∉ g.inputs) →
      ∀ (x y : List Bool), x.length = y.length →
      (∀ i, i ≠ v → x.getD i false = y.getD i false) →
      ∀ i, i ≠ v → (runW gs x).getD i false = (runW gs y).getD i false := by
    clear * -
    intro gs
    induction gs with
    | nil => intro _ _ x y _ hag i hi; exact hag i hi
    | cons g rest ih =>
      intro v hno x y hlen hag i hi
      have h1 : runW (g :: rest) x =
          runW rest (x ++ [g.op.eval (g.inputs.map fun k => x.getD k false)]) := rfl
      have h2 : runW (g :: rest) y =
          runW rest (y ++ [g.op.eval (g.inputs.map fun k => y.getD k false)]) := rfl
      rw [h1, h2]
      have hmap : (g.inputs.map fun k => x.getD k false) =
          (g.inputs.map fun k => y.getD k false) := by
        apply List.map_congr_left
        intro k hk
        exact hag k (fun he => hno g List.mem_cons_self (he ▸ hk))
      rw [hmap]
      apply ih v (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg')) _ _ (by simp [hlen]) _ i hi
      intro j hj
      by_cases hlt : j < x.length
      · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt,
          List.getElem?_append_left (hlen ▸ hlt)]
        exact hag j hj
      · by_cases heq : j = x.length
        · subst heq
          simp [hlen]
        · rw [List.getD_eq_default _ _ (by simp; omega),
            List.getD_eq_default _ _ (by simp; omega)]
  have hdense_clean : ∀ w : Fin (N + N),
      0 < (H.filter fun e => w = Fin.castAdd N e.1 ∨ w = Fin.natAdd N e.2).card →
      1 ≤ (C.gates.filter fun g => g.inputs.contains w.val).length ∧
      24 * (C.gates.filter fun g => g.inputs.contains w.val).length <
        (H.filter fun e => w = Fin.castAdd N e.1 ∨ w = Fin.natAdd N e.2).card := by
    intro w hdpos
    have hpos : 1 ≤ (C.gates.filter fun g => g.inputs.contains w.val).length := by
      by_contra h0
      have hzero : (C.gates.filter fun g => g.inputs.contains w.val).length = 0 := by omega
      have hno : ∀ g ∈ C.gates, w.val ∉ g.inputs := by
        intro g hg hmem
        have hc : g.inputs.contains w.val = true := List.contains_iff_mem.mpr hmem
        have hgf : g ∈ C.gates.filter (fun g' => g'.inputs.contains w.val) :=
          List.mem_filter.mpr ⟨hg, hc⟩
        have hl := List.length_pos_of_mem hgf
        omega
      obtain ⟨e, heF⟩ := Finset.card_pos.mp hdpos
      obtain ⟨heH, hwe⟩ := Finset.mem_filter.mp heF
      have heacc : (circuitFun (N + N) C fun i : Fin (N + N) =>
          Decidable.decide (i = Fin.castAdd N e.1 ∨ i = Fin.natAdd N e.2)) = true :=
        (Finset.mem_filter.mp heH).2.2.1
      have hout_ne : C.output ≠ w.val := by
        have := w.isLt
        omega
      rcases hwe with rfl | rfl
      · let x1 : Fin (N + N) → Bool := fun i =>
          Decidable.decide (i = Fin.castAdd N e.1 ∨ i = Fin.natAdd N e.2)
        let x2 : Fin (N + N) → Bool := fun i => decide (i = Fin.natAdd N e.2)
        have hag : ∀ i, i ≠ (Fin.castAdd N e.1).val →
            (List.ofFn x1).getD i false = (List.ofFn x2).getD i false := by
          intro i hi
          by_cases hlt : i < N + N
          · rw [List.getD_eq_getElem _ _ (by simp; exact hlt),
              List.getD_eq_getElem _ _ (by simp; exact hlt),
              List.getElem_ofFn, List.getElem_ofFn]
            have hne : (⟨i, hlt⟩ : Fin (N + N)) ≠ Fin.castAdd N e.1 :=
              fun heq => hi (congrArg Fin.val heq)
            dsimp only [x1, x2]
            exact decide_eq_decide.mpr ⟨fun h => h.resolve_left hne, Or.inr⟩
          · rw [List.getD_eq_default _ _ (by simp; omega),
              List.getD_eq_default _ _ (by simp; omega)]
        have heq : circuitFun (N + N) C x1 = circuitFun (N + N) C x2 :=
          runW_unused C.gates (Fin.castAdd N e.1).val hno
            (List.ofFn x1) (List.ofFn x2) (by simp) hag C.output hout_ne
        rw [heacc, singleton_false (Fin.natAdd N e.2)] at heq
        cases heq
      · let x1 : Fin (N + N) → Bool := fun i =>
          Decidable.decide (i = Fin.castAdd N e.1 ∨ i = Fin.natAdd N e.2)
        let x2 : Fin (N + N) → Bool := fun i => decide (i = Fin.castAdd N e.1)
        have hag : ∀ i, i ≠ (Fin.natAdd N e.2).val →
            (List.ofFn x1).getD i false = (List.ofFn x2).getD i false := by
          intro i hi
          by_cases hlt : i < N + N
          · rw [List.getD_eq_getElem _ _ (by simp; exact hlt),
              List.getD_eq_getElem _ _ (by simp; exact hlt),
              List.getElem_ofFn, List.getElem_ofFn]
            have hne : (⟨i, hlt⟩ : Fin (N + N)) ≠ Fin.natAdd N e.2 :=
              fun heq => hi (congrArg Fin.val heq)
            dsimp only [x1, x2]
            exact decide_eq_decide.mpr ⟨fun h => h.resolve_right hne, Or.inl⟩
          · rw [List.getD_eq_default _ _ (by simp; omega),
              List.getD_eq_default _ _ (by simp; omega)]
        have heq : circuitFun (N + N) C x1 = circuitFun (N + N) C x2 :=
          runW_unused C.gates (Fin.natAdd N e.2).val hno
            (List.ofFn x1) (List.ofFn x2) (by simp) hag C.output hout_ne
        rw [heacc, singleton_false (Fin.castAdd N e.1)] at heq
        cases heq
    have hd := hdense w hdpos
    rw [hfan_eq w.val, Nat.max_eq_right hpos] at hd
    exact ⟨hpos, hd⟩
  have hS_row' : ∀ p : Fin N, Fintype.card { l : Fin N // p ∈ S l } = q + 1 := by
    intro p
    rw [Fintype.card_subtype]
    exact hS_row p
  by_cases hq299 : q ≤ 299
  · exact hBounded q N S C H hq hq299 hN hS_col hS_row' hS_uniqP hS_uniqL
      hao hout_lo hout_hi hsize hsubcubic hsound_inc hH_spec hdense_clean
  · have hq300 : 300 ≤ q := by omega
    by_cases ht0 : tCount (N + N) C (fun i => decide (N ≤ i)) = 0
    · exact hPureOr q N S C H hq300 hN hS_col hS_row' hS_uniqP hS_uniqL
        hao hout_lo hout_hi hsize hsubcubic ht0 hsound_inc hH_spec hdense_clean
    · exact hTwoCol q N S C H hq300 hN hS_col hS_row' hS_uniqP hS_uniqL
        hao hout_lo hout_hi hsize hsubcubic (Nat.pos_of_ne_zero ht0)
        hsound_inc hH_spec hdense_clean
