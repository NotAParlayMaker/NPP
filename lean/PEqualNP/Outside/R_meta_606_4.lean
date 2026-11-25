import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.LowMerge in
theorem PEqualNP.Outside.R_meta_606_4
    (independentMerge :
      ∀ (P L : ℕ) (inc : Fin P → Fin L → Bool) (C : Circuit) (g : ℕ),
      (∀ (p q : Fin P) (w v : Fin L), p ≠ q → w ≠ v →
        ¬ (inc p w = true ∧ inc p v = true ∧ inc q w = true ∧ inc q v = true)) →
      (∀ (p : Fin P) (w v : Fin L),
        wireVal C (pointLineInput P L p w) g = wireVal C (pointLineInput P L p v) g) →
      ∀ (w v : Fin L), IsLowMerge P L inc C g w → IsLow P L inc C g v → w = v)
    (lineCount :
      ∀ (P L : ℕ) (inc : Fin P → Fin L → Bool) (C : Circuit), Monotone2 C →
      (∀ (w : Fin L) (x : Fin P → Bool),
        C.eval (restrictInput P L w x) = lineSum P L inc w x) →
      ∀ (w : Fin L), Fintype.card {p : Fin P // inc p w = true} ≤
        ((Finset.Ico (P + L) (P + L + C.size)).filter
          (fun g => IsLowMerge P L inc C g w ∧ IsNewLowMerge P L inc C g w)).card + 1)
    (dependentBudget :
      ∃ b : ℕ, ∀ (P L : ℕ) (inc : Fin P → Fin L → Bool) (C : Circuit),
      (∀ (p q : Fin P) (w v : Fin L), p ≠ q → w ≠ v →
        ¬ (inc p w = true ∧ inc p v = true ∧ inc q w = true ∧ inc q v = true)) →
      Monotone2 C →
      (∀ (w : Fin L) (x : Fin P → Bool),
        C.eval (restrictInput P L w x) = lineSum P L inc w x) →
      ∃ B : Circuit, Monotone2 B ∧
        (∀ (w : Fin L) (x : Fin P → Bool),
          B.eval (restrictInput P L w x) = C.eval (restrictInput P L w x)) ∧
        B.size + (∑ g ∈ Finset.Ico (P + L) (P + L + B.size),
          Fintype.card {w : Fin L // (IsLowMerge P L inc B g w ∧ IsNewLowMerge P L inc B g w) ∧
            ¬ ∀ (p : Fin P) (w v : Fin L),
              wireVal B (pointLineInput P L p w) g =
              wireVal B (pointLineInput P L p v) g}) ≤ b * (C.size + 1))
    (lift :
      ∃ a : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
      ∀ D : Circuit, Monotone2 D →
      (∀ x : Fin n → Bool, D.eval (List.ofFn x) =
        decide (∃ i j, G.Adj i j ∧ x i = true ∧ x j = true)) →
      ∃ C : Circuit, Monotone2 C ∧ C.size + 1 ≤ a * (D.size + 1) ∧
        ∀ (w : Fin n) (x : Fin n → Bool),
          C.eval (restrictInput n n w x) = lineSum n n (fun p v => decide (G.Adj p v)) w x) :
    ∃ c : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) → ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D → PEqualNP.MetaComplexity.circuitFun n D = (fun x : Fin n → Bool => decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) → G.edgeFinset.card ≤ c * (D.size + 1) := by
  obtain ⟨a, ha⟩ := lift
  obtain ⟨b, hb⟩ := dependentBudget
  refine ⟨b * a + 2, ?_⟩
  intro n G inst hg D hD hfun
  have hGraph (x : Fin n → Bool) :
      D.eval (List.ofFn x) = decide (∃ i j, G.Adj i j ∧ x i = true ∧ x j = true) :=
    congrFun hfun x
  let inc : Fin n → Fin n → Bool := fun p w => decide (G.Adj p w)
  have hinc (p w : Fin n) : inc p w = true ↔ G.Adj p w := decide_eq_true_iff
  have noRectangle (p q w v : Fin n) (hpq : p ≠ q) (hwv : w ≠ v) :
      ¬ (inc p w = true ∧ inc p v = true ∧ inc q w = true ∧ inc q v = true) := by
    rintro ⟨h₁, h₂, h₃, h₄⟩
    have hpw := (hinc p w).mp h₁
    have hpv := (hinc p v).mp h₂
    have hqw := (hinc q w).mp h₃
    have hqv := (hinc q v).mp h₄
    let cycle : G.Walk p p :=
      .cons hpw (.cons hqw.symm (.cons hqv (.cons hpv.symm .nil)))
    have hcycle : cycle.IsCycle := by
      rw [show cycle = .cons hpw (.cons hqw.symm (.cons hqv (.cons hpv.symm .nil))) from rfl,
        SimpleGraph.Walk.cons_isCycle_iff]
      constructor
      · simp [SimpleGraph.Walk.cons_isPath_iff, hqv.ne, hwv, hpw.ne.symm,
          hpv.ne.symm, hqw.ne.symm, hpq.symm]
      · simp [hpw.ne, hpv.ne, hpq, hwv, hpw.ne.symm]
    have hlen := hg p cycle hcycle
    simp [cycle] at hlen
  obtain ⟨C, hC, hCD, hcorrect⟩ := ha n G hg D hD hGraph
  obtain ⟨B, hB, hBC, hBudget⟩ := hb n n inc C noRectangle hC hcorrect
  have hCorrectB (w : Fin n) (x : Fin n → Bool) :
      B.eval (restrictInput n n w x) = lineSum n n inc w x :=
    (hBC w x).trans (hcorrect w x)
  let wires := Finset.Ico (n + n) (n + n + B.size)
  let merges (g : ℕ) (w : Fin n) := IsLowMerge n n inc B g w ∧ IsNewLowMerge n n inc B g w
  let M : Finset (ℕ × Fin n) :=
    (wires ×ˢ Finset.univ).filter (fun gw => merges gw.1 gw.2)
  let independent (g : ℕ) := ∀ (p w v : Fin n),
    wireVal B (pointLineInput n n p w) g = wireVal B (pointLineInput n n p v) g
  have hM : M.card ≤ b * (C.size + 1) := by
    let I := M.filter (fun gw => independent gw.1)
    let J := M.filter (fun gw => ¬ independent gw.1)
    have hsplit : I.card + J.card = M.card := by
      exact Finset.card_filter_add_card_filter_not (s := M) (fun gw => independent gw.1)
    have hI : I.card ≤ wires.card := by
      apply Finset.card_le_card_of_injOn Prod.fst
      · intro e he
        exact (Finset.mem_product.mp (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).1).1
      · intro e he f hf hef
        have hme := (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).2
        have hmf := (Finset.mem_filter.mp (Finset.mem_filter.mp hf).1).2
        obtain ⟨_, _, _, _, _, _, hlow, _, _⟩ := hmf.1
        exact Prod.ext hef (independentMerge n n inc B e.1 noRectangle
          (Finset.mem_filter.mp he).2 e.2 f.2 hme.1 (hef.symm ▸ hlow))
    have hwires : wires.card = B.size := by simp [wires]
    have jMem (e : ℕ × Fin n) :
        e ∈ J ↔ e.1 ∈ wires ∧ merges e.1 e.2 ∧ ¬ independent e.1 := by
      simp only [J, M, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true, and_assoc]
    have jCount : J.card = ∑ g ∈ wires,
        Fintype.card {w : Fin n // merges g w ∧ ¬ independent g} := by
      rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := wires)
        (fun e he => ((jMem e).mp he).1)]
      apply Finset.sum_congr rfl
      intro g hg
      rw [Fintype.card_subtype]
      apply Finset.card_bij (fun e _ => e.2)
      · intro e he
        obtain ⟨hme, he⟩ := Finset.mem_filter.mp he
        obtain ⟨_, hmerge, hdep⟩ := (jMem e).mp hme
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, he ▸ hmerge, he ▸ hdep⟩
      · intro e he f hf hef
        exact Prod.ext ((Finset.mem_filter.mp he).2.trans (Finset.mem_filter.mp hf).2.symm) hef
      · intro w hw
        refine ⟨(g, w), Finset.mem_filter.mpr ⟨(jMem (g, w)).mpr ?_, rfl⟩, rfl⟩
        exact ⟨hg, (Finset.mem_filter.mp hw).2⟩
    have hJ : B.size + J.card ≤ b * (C.size + 1) := by
      rw [jCount]
      exact hBudget
    omega
  let active : Finset (Fin n) := Finset.univ.filter (fun w => ∃ p, inc p w = true)
  let edges : Finset (Fin n × Fin n) := Finset.univ.filter (fun pw => inc pw.1 pw.2 = true)
  have hCardFibers {α : Type} [DecidableEq α] (W : Finset α) (R : α → Fin n → Prop)
      [∀ x w, Decidable (R x w)] (S : Finset (Fin n)) (hR : ∀ x w, R x w → w ∈ S) :
      ((W ×ˢ Finset.univ).filter (fun e => R e.1 e.2)).card =
        ∑ w ∈ S, (W.filter (fun x => R x w)).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := Prod.snd) (t := S)
      (fun e he => hR e.1 e.2 (Finset.mem_filter.mp he).2)]
    apply Finset.sum_congr rfl
    intro w _
    apply Finset.card_bij (fun e _ => e.1)
    · intro e he
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true] at he ⊢
      obtain ⟨⟨hmem, hrel⟩, rfl⟩ := he
      exact ⟨hmem, hrel⟩
    · intro e he f hf h
      exact Prod.ext h ((Finset.mem_filter.mp he).2.trans (Finset.mem_filter.mp hf).2.symm)
    · intro x hx
      obtain ⟨hmem, hrel⟩ := Finset.mem_filter.mp hx
      exact ⟨(x, w), by simp [hmem, hrel], rfl⟩
  have hEdgeCount : edges.card ≤ M.card + active.card := by
    have hEdges := hCardFibers Finset.univ (fun p w => inc p w = true) active
      (fun p w hp => Finset.mem_filter.mpr ⟨Finset.mem_univ w, ⟨p, hp⟩⟩)
    rw [Finset.univ_product_univ] at hEdges
    have hMerges := hCardFibers wires merges Finset.univ (fun _ w _ => Finset.mem_univ w)
    have hPerLine (w : Fin n) : (Finset.univ.filter (fun p => inc p w = true)).card ≤
        (wires.filter (fun g => merges g w)).card + 1 := by
      simpa only [Fintype.card_subtype] using lineCount n n inc B hB hCorrectB w
    have hsum := Finset.sum_le_sum (s := active) (fun w _ => hPerLine w)
    rw [Finset.sum_add_distrib] at hsum
    have hsub : (∑ w ∈ active, (wires.filter (fun g => merges g w)).card) ≤
        ∑ w : Fin n, (wires.filter (fun g => merges g w)).card :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    have hOnes : (∑ _w ∈ active, (1 : ℕ)) = active.card := by simp
    rw [hOnes] at hsum
    rw [show edges.card = _ from hEdges, show M.card = _ from hMerges]
    exact hsum.trans (Nat.add_le_add_right hsub _)
  have hGraphEdges : G.edgeFinset.card ≤ edges.card := by
    apply Finset.card_le_card_of_surjOn (fun pw : Fin n × Fin n => s(pw.1, pw.2))
    intro e he
    induction e using Sym2.ind with
    | h p w =>
      exact ⟨(p, w), Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, (hinc p w).mpr (G.mem_edgeFinset.mp he)⟩, rfl⟩
  have hActive : active.card ≤ 2 * (D.size + 1) := by
    let reads := D.output :: D.gates.flatMap Gate.inputs
    let extend (x : List Bool) (g : Gate) :=
      x ++ [g.op.eval (g.inputs.map (fun i => x.getD i false))]
    have sameOutput (gs : List Gate) (a b : List Bool) (hlen : a.length = b.length)
        (agree : ∀ i ∈ D.output :: gs.flatMap Gate.inputs, a.getD i false = b.getD i false) :
        (gs.foldl extend a).getD D.output false = (gs.foldl extend b).getD D.output false := by
      induction gs generalizing a b with
      | nil => exact agree D.output (by simp)
      | cons g gs ih =>
        have hval : g.op.eval (g.inputs.map (fun i => a.getD i false)) =
            g.op.eval (g.inputs.map (fun i => b.getD i false)) := by
          congr 1
          apply List.map_congr_left
          intro i hi
          exact agree i (by simp [hi])
        simp only [List.foldl_cons]
        apply ih _ _ (by simp [extend, hlen])
        intro i hi
        by_cases h : i < a.length
        · have h' : i < b.length := hlen ▸ h
          dsimp only [extend]
          rw [List.getD_append _ _ _ _ h, List.getD_append _ _ _ _ h']
          apply agree i
          simp only [List.mem_cons, List.flatMap_cons, List.mem_append] at hi ⊢
          tauto
        · dsimp only [extend]
          rw [List.getD_append_right _ _ _ _ (by omega),
            List.getD_append_right _ _ _ _ (by omega), hlen, hval]
    have hmem (w : Fin n) (hw : w ∈ active) : w.val ∈ reads := by
      obtain ⟨p, hp⟩ := (Finset.mem_filter.mp hw).2
      have hpw := (hinc p w).mp hp
      by_contra h
      let x : Fin n → Bool := fun i => decide (i = p)
      let y : Fin n → Bool := fun i => decide (i = p ∨ i = w)
      have hx : D.eval (List.ofFn x) = false := by
        rw [hGraph]
        apply decide_eq_false_iff_not.mpr
        rintro ⟨i, j, hij, hi, hj⟩
        simp only [x, decide_eq_true_iff] at hi hj
        exact G.irrefl (hi ▸ hj ▸ hij)
      have hy : D.eval (List.ofFn y) = true := by
        rw [hGraph]
        exact decide_eq_true ⟨p, w, hpw, by simp [y], by simp [y]⟩
      have eq : D.eval (List.ofFn x) = D.eval (List.ofFn y) := by
        apply sameOutput D.gates _ _ (by simp)
        intro i hi
        have hne : i ≠ w.val := fun e => h (e ▸ hi)
        by_cases hb : i < n
        · have hf : (⟨i, hb⟩ : Fin n) ≠ w := fun e => hne (congrArg Fin.val e)
          simp [List.getD_eq_getElem?_getD, hb, x, y, hf]
        · simp [List.getD_eq_getElem?_getD, hb]
      exact Bool.false_ne_true (hx.symm.trans (eq.trans hy))
    have cap (gs : List Gate) (hf : ∀ g ∈ gs, g.inputs.length ≤ 2) :
        (gs.flatMap Gate.inputs).length ≤ 2 * gs.length := by
      induction gs with
      | nil => simp
      | cons g gs ih =>
        have hg := hf g (by simp)
        have hgs := ih (fun j hj => hf j (by simp [hj]))
        simp only [List.flatMap_cons, List.length_append, List.length_cons]
        omega
    have hcard : active.card ≤ reads.toFinset.card := by
      apply Finset.card_le_card_of_injOn Fin.val
      · intro w hw
        exact List.mem_toFinset.mpr (hmem w hw)
      · exact Fin.val_injective.injOn
    have hlen := cap D.gates (fun g hg => (hD g hg).2)
    have hlist := hcard.trans (List.toFinset_card_le reads)
    simp only [reads, List.length_cons] at hlist
    unfold Circuit.size
    omega
  calc
    G.edgeFinset.card ≤ edges.card := hGraphEdges
    _ ≤ M.card + active.card := hEdgeCount
    _ ≤ b * (C.size + 1) + 2 * (D.size + 1) := Nat.add_le_add hM hActive
    _ ≤ b * (a * (D.size + 1)) + 2 * (D.size + 1) :=
      Nat.add_le_add_right (Nat.mul_le_mul_left b hCD) _
    _ = (b * a + 2) * (D.size + 1) := by rw [Nat.add_mul, Nat.mul_assoc]
