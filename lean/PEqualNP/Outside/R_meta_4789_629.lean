import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Choose
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.HeptadCover

-- Every set of five coordinates forces a selected pair to accept an incidence
-- while rejecting both endpoint singleton inputs. The budget bounds the number
-- of selected pairs by 26, below the 27 distinct negative projections.
set_option maxHeartbeats 1500000 in
theorem PEqualNP.Outside.R_meta_4789_629
    (geometry :
    let V := Fin 13
    let L := PEqualNP.HeptadCover.singerLines3
    let M := PEqualNP.HeptadCover.missLines L
    let D := fun A : Finset V =>
      (∀ p ∉ A, ∃ l ∈ M A, p ∈ L l) ∧
      ((∃ l, ∀ p ∈ A, p ∈ L l) ∨ ∃ p, ∀ l ∈ M A, p ∈ L l)
    ∀ (side : Bool) (T : Finset V), T.card = 5 →
      ∃ R : Finset (Finset V), 27 ≤ R.card ∧ (∀ A ∈ R, D A) ∧
        ∀ A ∈ R, ∀ B ∈ R, (if side then A else M A) ∩ T =
          (if side then B else M B) ∩ T → A = B)
    (support :
    ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (a b : Nat),
      (∀ g ∈ C.gates, g.inputs.length ≤ 2) →
      ∃ S : Finset (Fin 26), S.card ≤ C.size + 2 ∧
        ∀ x y : Fin 26 → Bool, (∀ i ∈ S, x i = y i) →
          (C.wires (List.ofFn x ++ [true, false])).getD a false =
            (C.wires (List.ofFn y ++ [true, false])).getD a false ∧
          (C.wires (List.ofFn x ++ [true, false])).getD b false =
            (C.wires (List.ofFn y ++ [true, false])).getD b false)
    (mono :
    ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C →
      ∀ (x y : Fin 26 → Bool), (∀ i, x i = true → y i = true) →
        ∀ w, (C.wires (List.ofFn x ++ [true, false])).getD w false = true →
          (C.wires (List.ofFn y ++ [true, false])).getD w false = true)
    (remaining :
    let V := Fin 13
    let L := PEqualNP.HeptadCover.singerLines3
    let M := PEqualNP.HeptadCover.missLines L
    let D := fun A : Finset V =>
      (∀ p ∉ A, ∃ l ∈ M A, p ∈ L l) ∧
      ((∃ l, ∀ p ∈ A, p ∈ L l) ∨ ∃ p, ∀ l ∈ M A, p ∈ L l)
    let F := Finset V
    let e := fun (A B : F) => Fin.append (fun p : V => decide (p ∈ A))
        (fun l : V => decide (l ∈ B))
    ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C →
      let w := fun i (A B : F) => (C.wires (List.ofFn (e A B) ++ [true, false])).getD i false
      let t := fun (q : Nat × Nat) A B => w q.1 A B || w q.2 A B
      let pos := fun f : F → F → Bool => ∀ l, ∀ p ∈ L l, f {p} {l} = true
      let cov := fun Q : Finset (Nat × Nat) =>
        ∀ A, D A → ∃ q ∈ Q, t q A (M A) ≠ true
      ∀ Q : Finset (Nat × Nat), 2 ≤ Q.card → C.size + 2 * Q.card ≤ 64 →
        (∀ q ∈ Q, pos (t q) ∧ ¬pos (w q.1) ∧ ¬pos (w q.2)) →
        cov Q → (∀ q ∈ Q, ¬cov (Q.erase q)) →
        (∀ (side : Bool) (T : F), T.card = 5 →
          ∃ p l, p ∈ L l ∧ (if side then p ∈ T else l ∈ T) ∧
            ∃ q ∈ Q, t q {p} ∅ ≠ true ∧ t q ∅ {l} ≠ true) → False) :
    let x1 : Type := Fin (13 : ℕ); have x2 : Finset x1 := {(0 : x1), (1 : x1), (3 : x1), (9 : x1)}; let x3 : x1 → x1 → Prop := fun (x3 x4 : x1) => ∃ x5 ∈ x2, x3 = x4 + x5; let x4 : Finset x1 → x1 → Prop := fun (x4 : Finset x1) (x5 : x1) => ∀ x6 ∈ x4, ¬x3 x6 x5; let x5 : Type := Fin (26 : ℕ) → Bool; have x6 : x1 → x1 → x5 := fun (x6 x7 : x1) (x8 : Fin (26 : ℕ)) => Decidable.decide (x8 = Fin.castAdd (13 : ℕ) x6 ∨ x8 = Fin.natAdd (13 : ℕ) x7); have x7 : Finset x1 → x5 := fun (x7 : Finset x1) (x8 : Fin (26 : ℕ)) => Decidable.decide ((∃ x9 ∈ x7, x8 = Fin.castAdd (13 : ℕ) x9) ∨ ∃ (x9 : Fin (13 : ℕ)), x8 = Fin.natAdd (13 : ℕ) x9 ∧ x4 x7 x9); have x8 : Finset x1 → Prop := fun (x8 : Finset x1) => (∀ x9 ∉ x8, ∃ (x11 : x1), x4 x8 x11 ∧ x3 x9 x11) ∧ ((∃ (x9 : x1), ∀ x10 ∈ x8, x3 x10 x9) ∨ ∃ (x9 : x1), ∀ (x10 : x1), x4 x8 x10 → x3 x9 x10); ∀ (x9 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x9 →     have x11 : ℕ → x5 → Bool := fun (x11 : ℕ) (x12 : x5) => (x9.wires (List.ofFn x12 ++ [Bool.true, Bool.false])).getD x11 Bool.false;     have x12 : (x5 → Bool) → Prop := fun (x12 : x5 → Bool) => ∀ (x13 x14 : x1), x3 x13 x14 → x12 (x6 x13 x14) = Bool.true;     have x13 : ℕ × ℕ → x5 → Bool := fun (x13 : ℕ × ℕ) (x14 : x5) => x11 x13.1 x14 || x11 x13.2 x14;     have x14 : Finset (ℕ × ℕ) → Prop := fun (x14 : Finset (ℕ × ℕ)) => ∀ (x15 : Finset x1), x8 x15 → ∃ x17 ∈ x14, ¬x13 x17 (x7 x15) = Bool.true;     ∀ (x15 : Finset (ℕ × ℕ)), (2 : ℕ) ≤ x15.card → x9.size + (2 : ℕ) * x15.card ≤ (64 : ℕ) → (∀ x18 ∈ x15, x12 (x13 x18) ∧ ¬x12 (x11 x18.1) ∧ ¬x12 (x11 x18.2)) → x14 x15 → (∀ x20 ∈ x15, ¬x14 (x15.erase x20)) → False := by
  classical
  let V := Fin 13
  let L := singerLines3
  let M := missLines L
  let D := fun A : Finset V =>
    (∀ p ∉ A, ∃ l ∈ M A, p ∈ L l) ∧
    ((∃ l, ∀ p ∈ A, p ∈ L l) ∨ ∃ p, ∀ l ∈ M A, p ∈ L l)
  let near := fun p l : V => ∃ a ∈ ({0,1,3,9} : Finset V), p = l + a
  let misses := fun (A : Finset V) (l : V) => ∀ p ∈ A, ¬near p l
  let origD := fun A : Finset V =>
    (∀ p ∉ A, ∃ l : V, misses A l ∧ near p l) ∧
    ((∃ l, ∀ p ∈ A, near p l) ∨ ∃ p : V, ∀ l : V, misses A l → near p l)
  let edge := fun (p l : V) (i : Fin 26) => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l)
  let neg := fun (A : Finset V) (i : Fin 26) =>
    decide ((∃ p ∈ A, i = Fin.castAdd 13 p) ∨ ∃ l : V, i = Fin.natAdd 13 l ∧ misses A l)
  let e := fun (A B : Finset V) => Fin.append (fun p : V => decide (p ∈ A))
    (fun l : V => decide (l ∈ B))
  have inc : ∀ p l, near p l ↔ p ∈ L l := by decide +kernel
  have self : ∀ p : V, p ∈ L p := by decide +kernel
  have missEq (A : Finset V) (l : V) : misses A l ↔ l ∈ M A := by
    change (∀ p ∈ A, ¬near p l) ↔ l ∈ Finset.univ.filter (fun k => Disjoint (L k) A)
    simp only [inc, Finset.mem_filter, Finset.mem_univ, true_and, Finset.disjoint_left]
    exact ⟨fun h p hp pa => h p pa hp, fun h p pa hp => h hp pa⟩
  have dEq (A : Finset V) : origD A ↔ D A := by
    change ((∀ p ∉ A, ∃ l : V, misses A l ∧ near p l) ∧
      ((∃ l, ∀ p ∈ A, near p l) ∨ ∃ p : V, ∀ l : V, misses A l → near p l)) ↔ D A
    simp only [inc, missEq]
    rfl
  have cross (p l : V) : Fin.castAdd 13 p ≠ Fin.natAdd 13 l := by
    intro eq
    have h := congrArg Fin.val eq
    change p.val = 13 + l.val at h
    omega
  have leftInj (p q : V) : Fin.castAdd 13 p = Fin.castAdd 13 q ↔ p = q := by
    constructor
    · intro h
      exact Fin.ext (congrArg (fun i : Fin 26 => i.val) h)
    · rintro rfl
      rfl
  have rightInj (p q : V) : Fin.natAdd 13 p = Fin.natAdd 13 q ↔ p = q := by
    constructor
    · intro eq
      apply Fin.ext
      have h := congrArg Fin.val eq
      change 13 + p.val = 13 + q.val at h
      omega
    · rintro rfl
      rfl
  have leftRow (A B : Finset V) (p : V) :
      e A B (Fin.castAdd 13 p) = decide (p ∈ A) := Fin.append_left _ _ _
  have rightRow (A B : Finset V) (l : V) :
      e A B (Fin.natAdd 13 l) = decide (l ∈ B) := Fin.append_right _ _ _
  have edgeEq (p l : V) : edge p l = e {p} {l} := by
    funext i
    refine Fin.addCases (m := 13) (n := 13) (fun q => ?_) (fun k => ?_) i
    · change decide (Fin.castAdd 13 q = Fin.castAdd 13 p ∨
        Fin.castAdd 13 q = Fin.natAdd 13 l) = e {p} {l} (Fin.castAdd 13 q)
      simp only [leftRow, cross, leftInj, or_false, Finset.mem_singleton]
    · change decide (Fin.natAdd 13 k = Fin.castAdd 13 p ∨
        Fin.natAdd 13 k = Fin.natAdd 13 l) = e {p} {l} (Fin.natAdd 13 k)
      simp only [rightRow, Ne.symm (cross p k), rightInj, false_or, Finset.mem_singleton]
  have negEq (A : Finset V) : neg A = e A (M A) := by
    funext i
    refine Fin.addCases (m := 13) (n := 13) (fun p => ?_) (fun l => ?_) i
    · change decide ((∃ q ∈ A, Fin.castAdd 13 p = Fin.castAdd 13 q) ∨
        ∃ l : V, Fin.castAdd 13 p = Fin.natAdd 13 l ∧ misses A l) = e A (M A) (Fin.castAdd 13 p)
      simp only [leftRow, cross, leftInj, false_and, exists_false, or_false]
      simp only [exists_eq_right']
    · change decide ((∃ q ∈ A, Fin.natAdd 13 l = Fin.castAdd 13 q) ∨
        ∃ k : V, Fin.natAdd 13 l = Fin.natAdd 13 k ∧ misses A k) = e A (M A) (Fin.natAdd 13 l)
      simp only [rightRow, fun p => Ne.symm (cross p l), rightInj, missEq,
        and_false, exists_false, false_or, exists_eq_left']
  let origRead := fun (C : Circuit) i (x : Fin 26 → Bool) =>
    (C.wires (List.ofFn x ++ [true, false])).getD i false
  let origPos := fun f : (Fin 26 → Bool) → Bool => ∀ p l : V, near p l → f (edge p l) = true
  let origTerm := fun (C : Circuit) (q : Nat × Nat) (x : Fin 26 → Bool) =>
    origRead C q.1 x || origRead C q.2 x
  let origCover := fun C (Q : Finset (Nat × Nat)) =>
    ∀ A, origD A → ∃ q ∈ Q, origTerm C q (neg A) ≠ true
  change ∀ (C : Circuit), Monotone2 C → ∀ Q : Finset (Nat × Nat),
    2 ≤ Q.card → C.size + 2 * Q.card ≤ 64 →
    (∀ q ∈ Q, origPos (origTerm C q) ∧ ¬origPos (origRead C q.1) ∧ ¬origPos (origRead C q.2)) →
    origCover C Q → (∀ q ∈ Q, ¬origCover C (Q.erase q)) → False
  intro C hM Q two bound origGood origHit origEssential
  let w := fun i A B => origRead C i (e A B)
  let t := fun (q : Nat × Nat) A B => w q.1 A B || w q.2 A B
  let pos := fun f : Finset V → Finset V → Bool => ∀ l, ∀ p ∈ L l, f {p} {l} = true
  let cov := fun Q' : Finset (Nat × Nat) => ∀ A, D A → ∃ q ∈ Q', t q A (M A) ≠ true
  have samePos (f : (Fin 26 → Bool) → Bool) : origPos f ↔ pos (fun A B => f (e A B)) := by
    constructor
    · intro h l p hp
      have atEdge := h p l ((inc p l).2 hp)
      rw [edgeEq] at atEdge
      exact atEdge
    · intro h p l hp
      rw [edgeEq]
      exact h l p ((inc p l).1 hp)
  have good : ∀ q ∈ Q, pos (t q) ∧ ¬pos (w q.1) ∧ ¬pos (w q.2) := by
    intro q hq
    obtain ⟨coverage, notFirst, notSecond⟩ := origGood q hq
    exact ⟨(samePos (origTerm C q)).1 coverage,
      fun hf => notFirst ((samePos (origRead C q.1)).2 hf),
      fun hs => notSecond ((samePos (origRead C q.2)).2 hs)⟩
  have sameCov (Q' : Finset (Nat × Nat)) : origCover C Q' ↔ cov Q' := by
    constructor
    · intro h A hA
      obtain ⟨q, hq, rej⟩ := h A ((dEq A).2 hA)
      rw [negEq] at rej
      exact ⟨q, hq, rej⟩
    · intro h A hA
      obtain ⟨q, hq, rej⟩ := h A ((dEq A).1 hA)
      refine ⟨q, hq, ?_⟩
      rw [negEq]
      exact rej
  have hit : cov Q := (sameCov Q).1 origHit
  have essential : ∀ q ∈ Q, ¬cov (Q.erase q) :=
    fun q hq hc => origEssential q hq ((sameCov _).2 hc)
  have ordered (A B P F : Finset V) (ap : A ⊆ P) (bf : B ⊆ F) :
      ∀ i, e A B i = true → e P F i = true := by
    intro i
    refine Fin.addCases (m := 13) (n := 13) (fun p => ?_) (fun l => ?_) i
    · simpa only [leftRow, decide_eq_true_eq] using (@ap p)
    · simpa only [rightRow, decide_eq_true_eq] using (@bf l)
  have termMono (q : Nat × Nat) (A B P F : Finset V) (ap : A ⊆ P) (bf : B ⊆ F) :
      t q A B = true → t q P F = true := by
    have transport := mono C hM (e A B) (e P F) (ordered A B P F ap bf)
    change (w q.1 A B || w q.2 A B) = true → (w q.1 P F || w q.2 P F) = true
    simp only [Bool.or_eq_true]
    exact Or.imp (transport q.1) (transport q.2)
  have dEmpty : D ∅ := by
    refine ⟨?_, Or.inl ⟨(0 : V), by simp⟩⟩
    intro p _
    exact ⟨p, (missEq ∅ p).1 (by intro a ha; simp at ha), self p⟩
  obtain ⟨q, qin, reject⟩ := hit ∅ dEmpty
  have rejectsZero : t q ∅ ∅ ≠ true :=
    fun hh => reject (termMono q ∅ ∅ ∅ _ (Finset.empty_subset _) (Finset.empty_subset _) hh)
  obtain ⟨S, cost, depends⟩ := support C q.1 q.2 (fun g hg => (hM g hg).2)
  have readsMatching (p : V) : Fin.castAdd 13 p ∈ S ∨ Fin.natAdd 13 p ∈ S := by
    by_contra missesBoth
    have agree (i : Fin 26) (hi : i ∈ S) : e {p} {p} i = e ∅ ∅ i := by
      refine Fin.addCases (m := 13) (n := 13) (fun u => ?_) (fun l => ?_) i hi
      · intro hu
        have neq : u ≠ p := fun eq => missesBoth (Or.inl (eq ▸ hu))
        simp only [leftRow, Finset.mem_singleton, neq, Finset.notMem_empty, decide_false]
      · intro hl
        have neq : l ≠ p := fun eq => missesBoth (Or.inr (eq ▸ hl))
        simp only [rightRow, Finset.mem_singleton, neq, Finset.notMem_empty, decide_false]
    have eq := depends (e {p} {p}) (e ∅ ∅) agree
    have h := (good q qin).1 p p (self p)
    change (w q.1 {p} {p} || w q.2 {p} {p}) = true at h
    change w q.1 {p} {p} = w q.1 ∅ ∅ ∧ w q.2 {p} {p} = w q.2 ∅ ∅ at eq
    rw [eq.1, eq.2] at h
    exact rejectsZero h
  let mark := fun p : V => if Fin.castAdd 13 p ∈ S then Fin.castAdd 13 p else Fin.natAdd 13 p
  have markIn (p : V) : mark p ∈ S := by
    by_cases hp : Fin.castAdd 13 p ∈ S
    · simpa [mark, hp] using hp
    · simp only [mark, if_neg hp]
      exact (readsMatching p).resolve_left hp
  have markInj : Function.Injective mark := by
    intro p l eq
    by_cases hp : Fin.castAdd 13 p ∈ S <;> by_cases hl : Fin.castAdd 13 l ∈ S
    · exact (leftInj p l).1 (by simpa [mark, hp, hl] using eq)
    · exact False.elim (cross p l (by simpa [mark, hp, hl] using eq))
    · exact False.elim (cross l p (by simpa [mark, hp, hl] using eq.symm))
    · exact (rightInj p l).1 (by simpa [mark, hp, hl] using eq)
  have thirteen : 13 ≤ S.card := by
    have h := Finset.card_le_card_of_injOn (s := (Finset.univ : Finset V)) (t := S)
      mark (fun p _ => markIn p) markInj.injOn
    rw [Finset.card_univ] at h
    change Fintype.card (Fin 13) ≤ S.card at h
    rwa [Fintype.card_fin] at h
  have pairBudget : Q.card ≤ 26 := by omega
  apply remaining C hM Q two bound good hit essential
  intro side T hT
  by_contra none
  obtain ⟨R, size, valid, separated⟩ := geometry side T hT
  have colors : ∀ A : R, ∃ q ∈ Q, t q A.val (M A.val) ≠ true :=
    fun A => hit A.val (valid A.val A.property)
  choose color inQ rejects using colors
  have conflict (A B : Finset V) (q : Nat × Nat) (hq : q ∈ Q)
      (ra : t q A (M A) ≠ true) (rb : t q B (M B) ≠ true)
      (p l : V) (pl : p ∈ L l) (tested : if side then p ∈ T else l ∈ T)
      (pa : p ∈ A) (lb : l ∈ M B) : False := by
    apply none
    refine ⟨p, l, pl, tested, q, hq, ?_, ?_⟩
    · intro h
      exact ra (termMono q {p} ∅ A (M A)
        (Finset.singleton_subset_iff.mpr pa) (Finset.empty_subset _) h)
    · intro h
      exact rb (termMono q ∅ {l} B (M B)
        (Finset.empty_subset _) (Finset.singleton_subset_iff.mpr lb) h)
  have inclusion (A B : R) (q : Nat × Nat) (hq : q ∈ Q)
      (ra : t q A.val (M A.val) ≠ true) (rb : t q B.val (M B.val) ≠ true) :
      (if side then A.val else M A.val) ∩ T ⊆ (if side then B.val else M B.val) ∩ T := by
    intro v hv
    cases hside : side
    · have hx : v ∈ M A.val ∩ T := by simpa only [hside, Bool.false_eq_true, if_false] using hv
      have hGoal : v ∈ M B.val ∩ T := by
        obtain ⟨vA, vT⟩ := Finset.mem_inter.mp hx
        refine Finset.mem_inter.mpr ⟨?_, vT⟩
        apply (missEq B.val v).1
        intro p hp bad
        exact conflict B.val A.val q hq rb ra p v ((inc p v).1 bad)
          (by simpa only [hside, Bool.false_eq_true, if_false] using vT) hp vA
      simpa only [hside, Bool.false_eq_true, if_false] using hGoal
    · have hx : v ∈ A.val ∩ T := by simpa only [hside, if_true] using hv
      have hGoal : v ∈ B.val ∩ T := by
        obtain ⟨vA, vT⟩ := Finset.mem_inter.mp hx
        refine Finset.mem_inter.mpr ⟨?_, vT⟩
        by_contra vB
        obtain ⟨l, hl, pl⟩ := (valid B.val B.property).1 v vB
        exact conflict A.val B.val q hq ra rb v l pl (by simpa only [hside, if_true] using vT) vA hl
      simpa only [hside, if_true] using hGoal
  let assign : R → Q := fun A => ⟨color A, inQ A⟩
  have injection : Function.Injective assign := by
    intro A B he
    have eq : color A = color B := congrArg Subtype.val he
    have ra := rejects A
    have rb := rejects B
    rw [← eq] at rb
    have inclAB := inclusion A B (color A) (inQ A) ra rb
    have inclBA := inclusion B A (color A) (inQ A) rb ra
    exact Subtype.ext (separated A.val A.property B.val B.property (Finset.Subset.antisymm inclAB inclBA))
  have pigeon := Fintype.card_le_of_injective assign injection
  rw [Fintype.card_coe, Fintype.card_coe] at pigeon
  omega
