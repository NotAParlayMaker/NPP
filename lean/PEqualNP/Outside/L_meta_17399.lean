import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17399

private abbrev Incident (p l : Fin 13) : Prop :=
  p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9

private def pointsOn (l : Fin 13) : Finset (Fin 13) :=
  Finset.univ.filter (fun p => Incident p l)

private def linesOn (p : Fin 13) : Finset (Fin 13) :=
  Finset.univ.filter (fun l => Incident p l)

private def missedLines (X : Finset (Fin 13)) : Finset (Fin 13) :=
  Finset.univ.filter (fun l => ∀ p ∈ X, ¬ Incident p l)

private def missedPoints (Y : Finset (Fin 13)) : Finset (Fin 13) :=
  Finset.univ.filter (fun p => ∀ l ∈ Y, ¬ Incident p l)

private abbrev PointArc (X : Finset (Fin 13)) : Prop :=
  ∀ l, (X ∩ pointsOn l).card ≤ 2

private abbrev LineArc (Y : Finset (Fin 13)) : Prop :=
  ∀ p, (Y ∩ linesOn p).card ≤ 2

private abbrev Tested (X Y : Finset (Fin 13)) : Prop :=
  Y = missedLines X ∧ X = missedPoints Y ∧
    (∀ l, ¬ X ⊆ pointsOn l) ∧ (∀ p, ¬ Y ⊆ linesOn p)

private theorem lineCard : ∀ l, (pointsOn l).card = 4 := by decide +kernel

private theorem uniqueJoin : ∀ a b : Fin 13, a ≠ b →
    ∃ l, (Incident a l ∧ Incident b l) ∧ ∀ m, Incident a m ∧ Incident b m → m = l := by
  decide +kernel

private abbrev labels := List.finRange 13
private abbrev bitInc (p l : Fin 13) : Bool := decide (Incident p l)
private abbrev bitDual (l p : Fin 13) : Bool := bitInc p l

private def excludes (R : Fin 13 → Fin 13 → Bool) (xs : List (Fin 13)) : List (Fin 13) :=
  labels.filter (fun y => xs.all (fun x => !(R x y)))

private theorem mem_excludes (R : Fin 13 → Fin 13 → Bool) (xs : List (Fin 13)) (y : Fin 13) :
    y ∈ excludes R xs ↔ ∀ x ∈ xs, R x y = false := by
  simp [excludes, List.all_eq_true]

private theorem excludes_points (xs : List (Fin 13)) :
    (excludes bitDual xs).toFinset = missedPoints xs.toFinset := by
  ext p
  simp [missedPoints, mem_excludes, decide_eq_false_iff_not]

private theorem excludes_lines (xs : List (Fin 13)) :
    (excludes bitInc xs).toFinset = missedLines xs.toFinset := by
  ext l
  simp [missedLines, mem_excludes, decide_eq_false_iff_not]

private def arcList (R : Fin 13 → Fin 13 → Bool) (xs : List (Fin 13)) : Bool :=
  labels.all (fun y => decide ((xs.filter (fun x => R x y)).length ≤ 2))

private theorem card_filter_list (R : Fin 13 → Bool) (xs : List (Fin 13)) (nodup : xs.Nodup) :
    (xs.toFinset.filter (fun p => R p = true)).card = (xs.filter R).length := by
  rw [← List.toFinset_card_of_nodup (nodup.filter R)]
  congr 1
  ext p
  simp [and_comm]

private theorem arcList_spec (R : Fin 13 → Fin 13 → Bool) (xs : List (Fin 13)) (nodup : xs.Nodup) :
    arcList R xs = true ↔ ∀ y, (xs.toFinset ∩ Finset.univ.filter (fun x => R x y = true)).card ≤ 2 := by
  have eq (y : Fin 13) : xs.toFinset ∩ Finset.univ.filter (fun x => R x y = true) =
      xs.toFinset.filter (fun x => R x y = true) := by
    ext x
    simp [and_comm]
  simp only [arcList, List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq,
    eq, card_filter_list _ xs nodup]

private def listTested (R : Fin 13 → Fin 13 → Bool) (xs : List (Fin 13)) : Bool :=
  let ys := excludes R xs
  (excludes (fun y x => R x y) ys == xs) &&
    labels.all (fun y => !(xs.all (fun x => R x y))) &&
    labels.all (fun x => !(ys.all (fun y => R x y)))

private theorem listTested_spec (R : Fin 13 → Fin 13 → Bool) (xs : List (Fin 13))
    (ok : listTested R xs = true) :
    let ys := excludes R xs
    xs.toFinset = (excludes (fun y x => R x y) ys).toFinset ∧
      (∀ y, ¬ ∀ x ∈ xs.toFinset, R x y = true) ∧
      (∀ x, ¬ ∀ y ∈ ys.toFinset, R x y = true) := by
  simp only [listTested, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_finRange,
    true_implies] at ok
  have notAll (ws : List (Fin 13)) (f : Fin 13 → Bool) (off : !(ws.all f) = true) :
      ¬ ∀ v ∈ ws.toFinset, f v = true := by
    intro all
    have on : ws.all f = true :=
      List.all_eq_true.mpr (fun v mem => all v (List.mem_toFinset.mpr mem))
    rw [on] at off
    cases off
  exact ⟨congrArg List.toFinset ok.1.1.symm, fun y => notAll _ _ (ok.1.2 y),
    fun x => notAll _ _ (ok.2 x)⟩

private def arcCheck (k : ℕ) (xs : List (Fin 13)) : Bool :=
  if k = 5 then !(arcList bitInc xs) && !(arcList bitDual xs)
  else (!(arcList bitInc xs) || listTested bitInc xs) &&
    (!(arcList bitDual xs) || listTested bitDual xs)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem arcCheck3 : ((labels.sublistsLen 3).all (arcCheck 3)) = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem arcCheck4 : ((labels.sublistsLen 4).all (arcCheck 4)) = true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem arcCheck5 : ((labels.sublistsLen 5).all (arcCheck 5)) = true := by decide +kernel

private abbrev ArcData (k : ℕ) (X : Finset (Fin 13)) : Prop :=
  if k = 5 then ¬PointArc X ∧ ¬LineArc X
  else (PointArc X → Tested X (missedLines X)) ∧ (LineArc X → Tested (missedPoints X) X)

private theorem checkedArcData (k : ℕ) (X : Finset (Fin 13)) (size : X.card = k)
    (checked : ((labels.sublistsLen k).all (arcCheck k)) = true) : ArcData k X := by
  let xs := labels.filter (fun x => decide (x ∈ X))
  have nd : xs.Nodup := (List.nodup_finRange 13).filter _
  have same : xs.toFinset = X := by ext p; simp [xs]
  have len : xs.length = k := by rw [← List.toFinset_card_of_nodup nd, same, size]
  have mem : xs ∈ labels.sublistsLen k := List.mem_sublistsLen.mpr ⟨List.filter_sublist, len⟩
  have ok := List.all_eq_true.mp checked xs mem
  have pointArc : arcList bitInc xs = true ↔ PointArc X := by
    rw [arcList_spec _ _ nd, same]
    simp [pointsOn, PointArc]
  have lineArc : arcList bitDual xs = true ↔ LineArc X := by
    rw [arcList_spec _ _ nd, same]
    simp [linesOn, LineArc]
  by_cases five : k = 5
  · have off : arcList bitInc xs = false ∧ arcList bitDual xs = false := by
      simpa [arcCheck, five] using ok
    simp only [ArcData, five, ↓reduceIte]
    exact ⟨fun hp => Bool.noConfusion (off.1.symm.trans (pointArc.mpr hp)),
      fun hl => Bool.noConfusion (off.2.symm.trans (lineArc.mpr hl))⟩
  · have options : (arcList bitInc xs = false ∨ listTested bitInc xs = true) ∧
        (arcList bitDual xs = false ∨ listTested bitDual xs = true) := by
      simpa [arcCheck, five] using ok
    simp only [ArcData, five, ↓reduceIte]
    constructor
    · intro arc
      have h := options.1.resolve_left (by simp [pointArc.mpr arc])
      obtain ⟨equality, pts, ls⟩ := listTested_spec bitInc xs h
      rw [same, excludes_points, excludes_lines, same] at equality
      refine ⟨rfl, equality, ?_, ?_⟩
      · intro l included
        apply pts l
        rw [same]
        intro p hp
        exact decide_eq_true (Finset.mem_filter.mp (included hp)).2
      · intro p included
        apply ls p
        rw [excludes_lines, same]
        intro l hl
        exact decide_eq_true (Finset.mem_filter.mp (included hl)).2
    · intro arc
      have h := options.2.resolve_left (by simp [lineArc.mpr arc])
      obtain ⟨equality, ls, pts⟩ := listTested_spec bitDual xs h
      rw [same, excludes_lines, excludes_points, same] at equality
      refine ⟨equality, rfl, ?_, ?_⟩
      · intro l included
        apply pts l
        rw [excludes_points, same]
        intro p hp
        exact decide_eq_true (Finset.mem_filter.mp (included hp)).2
      · intro p included
        apply ls p
        rw [same]
        intro l hl
        exact decide_eq_true (Finset.mem_filter.mp (included hl)).2

private theorem arcSubsetCount {X Z S : Finset (Fin 13)} (sub : Z ⊆ X) :
    (Z ∩ S).card ≤ (X ∩ S).card := by
  apply Finset.card_le_card
  intro v mem
  obtain ⟨hz, hs⟩ := Finset.mem_inter.mp mem
  exact Finset.mem_inter.mpr ⟨sub hz, hs⟩

private theorem completePointArc (X : Finset (Fin 13))
    (arc : PointArc X) (large : 3 ≤ X.card) : Tested X (missedLines X) := by
  have cap : X.card ≤ 4 := by
    by_contra! excessive
    obtain ⟨Z, sub, card⟩ := Finset.exists_subset_card_eq (by omega : 5 ≤ X.card)
    exact (checkedArcData 5 Z card arcCheck5).1 (fun l => (arcSubsetCount sub).trans (arc l))
  by_cases size : X.card = 3
  · exact (checkedArcData 3 X size arcCheck3).1 arc
  · exact (checkedArcData 4 X (by omega) arcCheck4).1 arc

private theorem completeLineArc (Y : Finset (Fin 13))
    (arc : LineArc Y) (large : 3 ≤ Y.card) : Tested (missedPoints Y) Y := by
  have cap : Y.card ≤ 4 := by
    by_contra! excessive
    obtain ⟨Z, sub, card⟩ := Finset.exists_subset_card_eq (by omega : 5 ≤ Y.card)
    exact (checkedArcData 5 Z card arcCheck5).2 (fun p => (arcSubsetCount sub).trans (arc p))
  by_cases size : Y.card = 3
  · exact (checkedArcData 3 Y size arcCheck3).2 arc
  · exact (checkedArcData 4 Y (by omega) arcCheck4).2 arc

private theorem pointsOutsideSmallLineSet (Y : Finset (Fin 13))
    (small : Y.card ≤ 2) : 5 ≤ (missedPoints Y).card := by
  have eq : missedPoints Y = Finset.univ \ Y.biUnion pointsOn := by
    ext p
    simp [missedPoints, pointsOn, Finset.mem_biUnion, not_exists]
  have bound : (Y.biUnion pointsOn).card ≤ 4 * Y.card := by
    calc
      _ ≤ ∑ l ∈ Y, (pointsOn l).card := Finset.card_biUnion_le
      _ = _ := by simp [lineCard, Nat.mul_comm]
  rw [eq, Finset.card_sdiff_of_subset (Finset.subset_univ _)]
  simp only [Finset.card_univ, Fintype.card_fin]
  omega

private theorem extendSmallPointArc (X W : Finset (Fin 13)) (fits : X ⊆ W)
    (small : X.card ≤ 2) (enough : 5 ≤ W.card) :
    ∃ T : Finset (Fin 13), X ⊆ T ∧ T ⊆ W ∧ 3 ≤ T.card ∧ PointArc T := by
  obtain ⟨S, xS, sW, size⟩ := Finset.exists_subsuperset_card_eq fits small
    (by omega : 2 ≤ W.card)
  obtain ⟨a, b, distinct, shape⟩ := Finset.card_eq_two.mp size
  obtain ⟨l, onLine, unique⟩ := uniqueJoin a b distinct
  have pairOn : S ⊆ pointsOn l := by
    rw [shape, Finset.insert_subset_iff, Finset.singleton_subset_iff]
    simp [pointsOn, onLine.1, onLine.2]
  have notAllOn : ¬ W ⊆ pointsOn l := by
    intro all
    have bound := Finset.card_le_card all
    rw [lineCard] at bound
    omega
  obtain ⟨c, cW, cOff⟩ := Finset.not_subset.mp notAllOn
  have cNew : c ∉ S := fun hc => cOff (pairOn hc)
  let T := insert c S
  have tSize : T.card = 3 := by simp [T, cNew, size]
  refine ⟨T, xS.trans (Finset.subset_insert _ _), Finset.insert_subset_iff.mpr ⟨cW, sW⟩,
    tSize.ge, ?_⟩
  intro r
  by_contra! large
  have same : T ∩ pointsOn r = T :=
    Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
  have allOn : T ⊆ pointsOn r := by
    intro i hi
    rw [← same] at hi
    exact (Finset.mem_inter.mp hi).2
  have hca : Incident a r := (Finset.mem_filter.mp (allOn (by simp [T, shape]))).2
  have hcb : Incident b r := (Finset.mem_filter.mp (allOn (by simp [T, shape]))).2
  have equal : r = l := unique r ⟨hca, hcb⟩
  rw [equal] at allOn
  exact cOff (allOn (by simp [T]))

private theorem independentArcs_extend {X Y : Finset (Fin 13)}
    (apart : ∀ p ∈ X, ∀ l ∈ Y, ¬ Incident p l)
    (pArc : PointArc X) (lArc : LineArc Y) :
    ∃ A B : Finset (Fin 13), X ⊆ A ∧ Y ⊆ B ∧ Tested A B := by
  have yMiss : Y ⊆ missedLines X := by
    intro l hl
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun p hp => apart p hp l hl⟩
  have xMiss : X ⊆ missedPoints Y := by
    intro p hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun l hl => apart p hp l hl⟩
  by_cases largeX : 3 ≤ X.card
  · exact ⟨X, missedLines X, Finset.Subset.rfl, yMiss, completePointArc X pArc largeX⟩
  by_cases largeY : 3 ≤ Y.card
  · exact ⟨missedPoints Y, Y, xMiss, Finset.Subset.rfl, completeLineArc Y lArc largeY⟩
  obtain ⟨A, xA, aMiss, largeA, aArc⟩ :=
    extendSmallPointArc X (missedPoints Y) xMiss (by omega)
      (pointsOutsideSmallLineSet Y (by omega))
  have yMissA : Y ⊆ missedLines A := by
    intro l hl
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, fun p hp => (Finset.mem_filter.mp (aMiss hp)).2 l hl⟩
  exact ⟨A, missedLines A, xA, yMissA, completePointArc A aArc largeA⟩

end PEqualNP.Outside.L_meta_17399

open PEqualNP.Outside.L_meta_17399 in
theorem PEqualNP.Outside.L_meta_17399 : (let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); have x2 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x2 : Finset (Fin (13 : ℕ))) => {x3 : Fin (13 : ℕ) | ∀ x4 ∈ x2, ¬x1 x4 x3}; ∀ (x3 x4 : Finset (Fin (13 : ℕ))), (∀ x5 ∈ x3, ∀ x7 ∈ x4, ¬x1 x5 x7) → (∀ (x6 : Fin (13 : ℕ)), {x7 ∈ x3 | x1 x7 x6}.card ≤ (2 : ℕ)) → (∀ (x7 : Fin (13 : ℕ)), {x8 ∈ x4 | x1 x7 x8}.card ≤ (2 : ℕ)) → ∃ (x8 : Finset (Fin (13 : ℕ))), x3 ⊆ x8 ∧ x4 ⊆ x2 x8 ∧ (∀ x9 ∉ x8, ∃ x11 ∈ x2 x8, x1 x9 x11) ∧ (¬∃ (x9 : Fin (13 : ℕ)), ∀ x10 ∈ x8, x1 x10 x9) ∧ ¬∃ (x9 : Fin (13 : ℕ)), ∀ x10 ∈ x2 x8, x1 x9 x10) := by
  dsimp only
  intro X Y apart pointLines linePoints
  have pArc : PointArc X := by
    intro l
    have eq : X ∩ pointsOn l = X.filter (fun p => Incident p l) := by
      ext p
      simp [pointsOn]
    rw [eq]
    exact pointLines l
  have lArc : LineArc Y := by
    intro p
    have eq : Y ∩ linesOn p = Y.filter (fun l => Incident p l) := by
      ext l
      simp [linesOn]
    rw [eq]
    exact linePoints p
  obtain ⟨A, B, xA, yB, eqB, eqA, points, lines⟩ := independentArcs_extend apart pArc lArc
  subst B
  refine ⟨A, xA, yB, ?_, ?_, ?_⟩
  · intro p notIn
    by_contra absent
    have inMissed : p ∈ missedPoints (missedLines A) := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, fun l mem inc => absent ⟨l, mem, inc⟩⟩
    exact notIn (eqA.symm ▸ inMissed)
  · rintro ⟨l, allOn⟩
    apply points l
    intro p hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, allOn p hp⟩
  · rintro ⟨p, allOn⟩
    apply lines p
    intro l hl
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, allOn l hl⟩
