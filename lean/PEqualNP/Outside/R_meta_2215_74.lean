import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- A mask stores the set bits among the 25 original wires. All incidence- and
-- pencil-preserving images of each mask are tested by the same circuit.
theorem PEqualNP.Outside.R_meta_2215_74
    (classify :
      let I := fun i j : Fin 25 => i.val < 12 ∧ 12 ≤ j.val ∧
        (i.val+j.val+2) % 13 ∈ ([0,1,3,9] : List ℕ)
      let pencil : Finset (Fin 25) := {12,13,15,21}
      let independent := fun s : Finset (Fin 25) => ∀ i ∈ s, ∀ j ∈ s, ¬ I i j
      let symm := fun g : Equiv.Perm (Fin 25) =>
        (∀ i j, I (g i) (g j) ↔ I i j) ∧ (∀ i, g i ∈ pencil ↔ i ∈ pencil)
      let orbit := fun (m : ℕ) (g : Equiv.Perm (Fin 25)) =>
        (Finset.univ.filter (fun i : Fin 25 => m.testBit i.val)).map g.toEmbedding
      let mainMasks : List ℕ := [4095,7930,13944,17342,21178,29240,45144,82094,
        86186,90156,118922,348202,847896,1429514,7852034,33550336]
      let flagMasks : List ℕ := [4095,17342,82094,213030,475170,720901,5718018,31408128]
      (∀ s, Maximal independent s → ∃ m ∈ mainMasks, ∃ g, symm g ∧ orbit m g = s) ∧
      (∀ s, Maximal (fun t => independent t ∧ Disjoint t pencil) s →
        ∃ m ∈ flagMasks, ∃ g, symm g ∧ orbit m g = s))
    (tests :
      let I := fun i j : Fin 25 => i.val < 12 ∧ 12 ≤ j.val ∧
        (i.val+j.val+2) % 13 ∈ ([0,1,3,9] : List ℕ)
      let pencil : Finset (Fin 25) := {12,13,15,21}
      let symm := fun g : Equiv.Perm (Fin 25) =>
        (∀ i j, I (g i) (g j) ↔ I i j) ∧ (∀ i, g i ∈ pencil ↔ i ∈ pencil)
      let orbit := fun (m : ℕ) (g : Equiv.Perm (Fin 25)) =>
        (Finset.univ.filter (fun i : Fin 25 => m.testBit i.val)).map g.toEmbedding
      let mainMasks : List ℕ := [4095,7930,13944,17342,21178,29240,45144,82094,
        86186,90156,118922,348202,847896,1429514,7852034,33550336]
      let flagMasks : List ℕ := [4095,17342,82094,213030,475170,720901,5718018,31408128]
      let row := fun s : Finset (Fin 25) => List.ofFn (fun k : Fin 25 => decide (k ∈ s))
      ∃ (C : Circuit) (q : ℕ), Monotone2 C ∧ C.size ≤ 61 ∧ C.output < 25+C.size ∧
        q < 25+C.size ∧
        (∀ i j, I i j → C.eval (row {i,j}) = true) ∧
        (∀ m ∈ mainMasks, ∀ g, symm g → C.eval (row (orbit m g)) = false) ∧
        (∀ j ∈ pencil, (C.wires (row {j})).getD q false = true) ∧
        (∀ m ∈ flagMasks, ∀ g, symm g → (C.wires (row (orbit m g))).getD q false = false)) :
    ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 ∧     x1.size ≤ (61 : ℕ) ∧       x1.output < (25 : ℕ) + x1.size ∧         x2 < (25 : ℕ) + x1.size ∧           ∀ (x3 : Fin (25 : ℕ) → Bool),             have x4 : Fin (25 : ℕ) → Fin (25 : ℕ) → Prop := fun (x4 x5 : Fin (25 : ℕ)) => ↑x4 < (12 : ℕ) ∧ (12 : ℕ) ≤ ↑x5 ∧ (↑x4 + ↑x5 + (2 : ℕ)) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)];             have x5 : Bool := x1.eval (List.ofFn x3);             (x5 = Bool.true ↔ ∃ (x6 : Fin (25 : ℕ)) (x7 : Fin (25 : ℕ)), x4 x6 x7 ∧ x3 x6 = Bool.true ∧ x3 x7 = Bool.true) ∧ (x5 = Bool.false → (x1.wires (List.ofFn x3)).getD x2 Bool.false = (x3 (12 : Fin (25 : ℕ)) || x3 (13 : Fin (25 : ℕ)) || x3 (15 : Fin (25 : ℕ)) || x3 (21 : Fin (25 : ℕ)))) := by
  classical
  let I := fun i j : Fin 25 => i.val < 12 ∧ 12 ≤ j.val ∧
    (i.val+j.val+2) % 13 ∈ ([0,1,3,9] : List ℕ)
  let pencil : Finset (Fin 25) := {12,13,15,21}
  let independent := fun s : Finset (Fin 25) => ∀ i ∈ s, ∀ j ∈ s, ¬ I i j
  let row := fun s : Finset (Fin 25) => List.ofFn (fun k : Fin 25 => decide (k ∈ s))
  obtain ⟨C,q,hm,hsize,ho,hq,pos,negOrbit,fpos,fnegOrbit⟩ := tests
  obtain ⟨cls, fcls⟩ := classify
  have neg (s : Finset (Fin 25)) (hs : Maximal independent s) : C.eval (row s) = false := by
    obtain ⟨m,hm,g,hg,rfl⟩ := cls s hs
    exact negOrbit m hm g hg
  have fneg (s : Finset (Fin 25)) (hs : Maximal (fun t => independent t ∧ Disjoint t pencil) s) :
      (C.wires (row s)).getD q false = false := by
    obtain ⟨m,hm,g,hg,rfl⟩ := fcls s hs
    exact fnegOrbit m hm g hg
  let step (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let Le := fun (w z : List Bool) => ∀ i : ℕ, w.getD i false = true → z.getD i false = true
  have extend (gs : List PEqualNP.CircuitLowerBounds.Gate)
      (ok : ∀ g ∈ gs, g.op = .and ∨ g.op = .or) (w z : List Bool)
      (len : w.length = z.length) (le : Le w z) :
      Le (gs.foldl step w) (gs.foldl step z) := by
    induction gs generalizing w z with
    | nil => exact le
    | cons g gs ih =>
      apply ih (fun k hk => ok k (by simp [hk])) (step w g) (step z g) (by simp [step,len])
      have gate : g.op.eval (g.inputs.map fun i => w.getD i false) = true →
          g.op.eval (g.inputs.map fun i => z.getD i false) = true := by
        rcases ok g (by simp) with hop | hop
        · rw [hop]
          change (g.inputs.map fun i => w.getD i false).all id = true → (g.inputs.map fun i => z.getD i false).all id = true
          simp only [List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
          intro h i hi
          exact le i (h i hi)
        · rw [hop]
          change (g.inputs.map fun i => w.getD i false).any id = true → (g.inputs.map fun i => z.getD i false).any id = true
          simp only [List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
          rintro ⟨i,hi,ha⟩
          exact ⟨i,hi,le i ha⟩
      intro i
      by_cases small : i < w.length
      · simpa only [step,List.getD_append _ _ _ _ small,List.getD_append _ _ _ _ (len ▸ small)] using le i
      · have big : w.length ≤ i := by omega
        simp only [step,List.getD_append_right _ _ _ _ big,List.getD_append_right _ _ _ _ (len ▸ big), ← len]
        cases e : i-w.length with
        | zero => exact gate
        | succ j => simp
  have mono {s t : Finset (Fin 25)} (st : s ⊆ t) :
      Le (C.wires (row s)) (C.wires (row t)) := by
    apply extend C.gates (fun g hg => (hm g hg).1) _ _ (by simp [row])
    intro j
    by_cases hj : j < 25
    · rw [List.getD_eq_getElem (row s) false (by simpa only [row,List.length_ofFn] using hj),
          List.getD_eq_getElem (row t) false (by simpa only [row,List.length_ofFn] using hj)]
      simp only [row,List.getElem_ofFn,decide_eq_true_eq]
      exact fun h => st h
    · rw [List.getD_eq_default (row s) false (by simp only [row,List.length_ofFn]; omega)]
      intro h
      exact Bool.noConfusion h
  refine ⟨C,q,hm,hsize,ho,hq,?_⟩
  intro x
  dsimp only
  let s := Finset.univ.filter (fun i : Fin 25 => x i = true)
  have mem (i : Fin 25) : i ∈ s ↔ x i = true := by simp [s]
  have repr : row s = List.ofFn x := by
    apply congrArg List.ofFn
    funext i
    simp [mem]
  have indep (rejected : C.eval (List.ofFn x) = false) : independent s := by
    intro i hi j hj hij
    have sub : ({i,j} : Finset (Fin 25)) ⊆ s :=
      Finset.insert_subset hi (Finset.singleton_subset_iff.mpr hj)
    have yes := mono sub C.output (pos i j hij)
    rw [repr] at yes
    exact Bool.noConfusion (rejected.symm.trans yes)
  constructor
  · constructor
    · intro yes
      by_contra no
      have hs : independent s := fun i hi j hj edge =>
        no ⟨i,j,edge,(mem i).mp hi,(mem j).mp hj⟩
      obtain ⟨t,st,mt⟩ := Finite.exists_le_maximal hs
      rw [← repr] at yes
      exact Bool.noConfusion ((neg t mt).symm.trans (mono st C.output yes))
    · rintro ⟨i,j,hij,hi,hj⟩
      have sub : ({i,j} : Finset (Fin 25)) ⊆ s :=
        Finset.insert_subset ((mem i).mpr hi) (Finset.singleton_subset_iff.mpr ((mem j).mpr hj))
      rw [← repr]
      exact mono sub C.output (pos i j hij)
  · intro rejected
    have flags : ((x 12 || x 13 || x 15 || x 21) = true) ↔
        ∃ j ∈ pencil, j ∈ s := by simp [pencil,mem,or_assoc]
    cases h : (x 12 || x 13 || x 15 || x 21) with
    | true =>
      obtain ⟨j,hj,hs⟩ := flags.mp h
      rw [← repr]
      exact mono (Finset.singleton_subset_iff.mpr hs) q (fpos j hj)
    | false =>
      have disj : Disjoint s pencil := by
        apply Finset.disjoint_left.mpr
        intro j hs hj
        exact Bool.noConfusion (h.symm.trans (flags.mpr ⟨j,hj,hs⟩))
      obtain ⟨t,st,mt⟩ := Finite.exists_le_maximal
        (p := fun u => independent u ∧ Disjoint u pencil) ⟨indep rejected,disj⟩
      rw [← repr]
      cases he : (C.wires (row s)).getD q false with
      | false => rfl
      | true => exact False.elim (Bool.noConfusion ((fneg t mt).symm.trans (mono st q he)))
