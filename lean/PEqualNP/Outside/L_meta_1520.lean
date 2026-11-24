import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi

namespace DeepLineCountA

private def needA : Finset (Fin 13) := {0, 1, 3}
private def freeA (i : Fin 10) : Fin 13 :=
  if i = 0 then 2 else ⟨i.val + 3, by omega⟩
private def indexA (v : Fin 13) : Fin 10 :=
  ⟨v.val - 3, by omega⟩
private def fillA (f : Fin 10 → Bool) (v : Fin 13) : Bool :=
  if v ∈ needA then false else f (indexA v)
private theorem freeA_ok : ∀ i : Fin 10, freeA i ∉ needA ∧ indexA (freeA i) = i := by decide
private theorem indexA_ok : ∀ v : Fin 13, v ∉ needA → freeA (indexA v) = v := by decide

private theorem lineCountA :
    (Finset.univ.filter (fun x : Fin 13 → Bool => ∃ v ∈ ({0, 1, 3} : Finset (Fin 13)), x v = true)).card =
      7168 := by
  classical
  let hit : (Fin 13 → Bool) → Prop := fun x => ∃ v ∈ needA, x v = true
  let avoid := (Finset.univ : Finset (Fin 13 → Bool)).filter fun x => ¬ hit x
  have eqImage : (Finset.univ : Finset (Fin 10 → Bool)).image fillA = avoid := by
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and, avoid, Finset.mem_filter]
    constructor
    · rintro ⟨f, rfl⟩ ⟨v, hv, hval⟩
      simp [fillA, hv] at hval
    · intro h
      refine ⟨fun i => x (freeA i), ?_⟩
      funext v
      by_cases hv : v ∈ needA
      · have hv' : x v ≠ true := fun hval => h ⟨v, hv, hval⟩
        cases hx : x v <;> simp_all [fillA]
      · simp [fillA, hv, indexA_ok v hv]
  have injFill : Function.Injective fillA := by
    intro f g eq
    funext i
    simpa [fillA, (freeA_ok i).1, (freeA_ok i).2] using congrFun eq (freeA i)
  have hAvoid := Finset.card_image_of_injective (Finset.univ : Finset (Fin 10 → Bool)) injFill
  rw [eqImage] at hAvoid
  have hSmall : (Finset.univ : Finset (Fin 10 → Bool)).card = 1024 := by
    simp
  have hTotal : (Finset.univ : Finset (Fin 13 → Bool)).card = 8192 := by
    simp
  have hParts := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin 13 → Bool))) hit
  change ((Finset.univ : Finset (Fin 13 → Bool)).filter hit).card + avoid.card = _ at hParts
  change ((Finset.univ : Finset (Fin 13 → Bool)).filter hit).card = _
  omega

end DeepLineCountA

namespace DeepLineCountB

private def lines (t : Fin 13) : Finset (Fin 13) := {t, t + 1, t + 3, t + 9}

private def lineParts : Finset (Finset (Fin 13)) :=
  Finset.univ.biUnion (fun t => (lines t).powerset)

private def zeros (x : Fin 13 → Bool) : Finset (Fin 13) :=
  Finset.univ.filter (fun v => x v = false)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem linePartsCount : lineParts.card = 157 := by
  decide +kernel

private theorem lineCountB :
    (Finset.univ.filter (fun x : Fin 13 → Bool =>
      ∃ s : Fin 13, ∀ v : Fin 13, x v = false → v ∈ lines s)).card = 157 := by
  rw [← linePartsCount]
  refine Finset.card_bij' (fun x _ => zeros x)
    (fun S _ => fun v => decide (v ∉ S)) ?_ ?_ ?_ ?_
  · intro x hx
    obtain ⟨_, s, hs⟩ := Finset.mem_filter.mp hx
    refine Finset.mem_biUnion.mpr ⟨s, Finset.mem_univ s, Finset.mem_powerset.mpr ?_⟩
    intro v hv
    exact hs v (by simpa [zeros] using hv)
  · intro S hS
    obtain ⟨s, _, hs⟩ := Finset.mem_biUnion.mp hS
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, s, ?_⟩
    intro v hv
    exact Finset.mem_powerset.mp hs (by simpa using hv)
  · intro x _
    funext v
    cases h : x v <;> simp [zeros, h]
  · intro S _
    ext v
    simp [zeros]

end DeepLineCountB

namespace DeepLineCount

private abbrev V := Fin 13
private abbrev Input := V → Bool
private def line (t : V) : Finset V := {t, t + 1, t + 3, t + 9}
private def seed : Finset V := {0, 1, 3}
private abbrev hit (x : Input) : Prop := ∃ v ∈ seed, x v = true
private abbrev contained (x : Input) : Prop :=
  ∃ s : V, ∀ v : V, x v = false → v ∈ line s

private def low : Input := fun v => decide (v ∉ line 0)
private def high : Input := fun v => decide (v ∉ line 0 ∨ v = 9)

private theorem uniqueLine : ∀ s : V, 0 ∈ line s → 1 ∈ line s → s = 0 := by decide +kernel
private theorem seedOrNine : ∀ v : V, v ∈ line 0 → v ∈ seed ∨ v = 9 := by decide +kernel
private theorem noLowHit : ¬ hit low := by decide +kernel
private theorem noHighHit : ¬ hit high := by decide +kernel
private theorem lowHigh : low ≠ high := by
  intro h
  exact (by decide +kernel : low 9 ≠ high 9) (congrFun h 9)

private theorem lowContained : contained low := by
  refine ⟨0, ?_⟩
  intro v hv
  by_contra h
  simp [low, h] at hv

private theorem highContained : contained high := by
  refine ⟨0, ?_⟩
  intro v hv
  by_contra h
  simp [high, h] at hv

private theorem describe (x : Input) :
    hit x ∨ contained x ↔ hit x ∨ x = low ∨ x = high := by
  constructor
  · rintro (ha | ⟨s, hs⟩)
    · exact Or.inl ha
    · by_cases ha : hit x
      · exact Or.inl ha
      have falseAtSeed : ∀ v ∈ seed, x v = false := by
        intro v hv
        cases h : x v with
        | false => rfl
        | true => exact False.elim (ha ⟨v, hv, h⟩)
      have hs0 := uniqueLine s (hs 0 (falseAtSeed 0 (by decide)))
        (hs 1 (falseAtSeed 1 (by decide)))
      subst s
      have formula (v : V) : x v = if v ∈ line 0 then if v = 9 then x 9 else false else true := by
        by_cases hline : v ∈ line 0
        · rcases seedOrNine v hline with hseed | h9
          · have hn : v ≠ 9 := by
              intro hn
              subst v
              exact (by decide : (9 : V) ∉ seed) hseed
            simp [hline, hn, falseAtSeed v hseed]
          · subst v
            simp [hline]
        · cases hv : x v with
          | false => exact False.elim (hline (hs v hv))
          | true => simp [hline]
      cases hn : x 9 with
      | false =>
        refine Or.inr (Or.inl ?_)
        funext v
        rw [formula v]
        by_cases hv : v ∈ line 0 <;> simp [hv, hn, low]
      | true =>
        refine Or.inr (Or.inr ?_)
        funext v
        rw [formula v]
        by_cases hv : v ∈ line 0 <;> by_cases h9 : v = 9 <;> simp [hv, hn, h9, high]
  · rintro (h | rfl | rfl)
    · exact Or.inl h
    · exact Or.inr lowContained
    · exact Or.inr highContained

private theorem hitDiff (x : Input) (h : hit x) : x ≠ low ∧ x ≠ high := by
  constructor
  · rintro rfl
    exact noLowHit h
  · rintro rfl
    exact noHighHit h

private theorem countTogether (countHit : (Finset.univ.filter (fun x : Input => hit x)).card = 7168) :
    (Finset.univ.filter (fun x : Input => hit x ∨ contained x)).card = 7170 := by
  let hitSet : Finset Input := Finset.univ.filter (fun x => hit x)
  have eq : (Finset.univ.filter (fun x : Input => hit x ∨ contained x)) =
      insert low (insert high hitSet) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, hitSet]
    simpa only [or_assoc, or_left_comm, or_comm] using describe x
  have highNew : high ∉ hitSet := by
    simp only [hitSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact noHighHit
  have lowNew : low ∉ insert high hitSet := by
    simp only [Finset.mem_insert, hitSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact fun h => h.elim lowHigh noLowHit
  rw [eq, Finset.card_insert_of_notMem lowNew, Finset.card_insert_of_notMem highNew]
  exact congrArg (fun x : ℕ => x + 1 + 1) countHit

private theorem upClosed (x y : Input) (hx : hit x ∨ contained x)
    (hxy : ∀ v, x v = true → y v = true) : hit y ∨ contained y := by
  rcases hx with ⟨v, hv, h⟩ | ⟨s, hs⟩
  · exact Or.inl ⟨v, hv, hxy v h⟩
  · refine Or.inr ⟨s, ?_⟩
    intro v hy
    cases hv : x v with
    | false => exact hs v hv
    | true =>
      have h := hxy v hv
      simp [hy] at h

private theorem mainProof
    (countHit : (Finset.univ.filter (fun x : Input => hit x)).card = 7168)
    (countContained : (Finset.univ.filter (fun x : Input => contained x)).card = 157) :
    ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    (∀ x : Fin 13 → Bool, ((∃ v ∈ ({0, 1, 3} : Finset (Fin 13)), x v = true) ∨ ∃ s : Fin 13, ∀ v : Fin 13, x v = false → v ∈ L s) ↔
      ((∃ v ∈ ({0, 1, 3} : Finset (Fin 13)), x v = true) ∨ x = (fun v : Fin 13 => decide (v ∉ L 0)) ∨ x = (fun v : Fin 13 => decide (v ∉ L 0 ∨ v = 9)))) ∧
    (∀ x : Fin 13 → Bool, (∃ v ∈ ({0, 1, 3} : Finset (Fin 13)), x v = true) → x ≠ (fun v : Fin 13 => decide (v ∉ L 0)) ∧ x ≠ (fun v : Fin 13 => decide (v ∉ L 0 ∨ v = 9))) ∧
    (Finset.univ.filter (fun x : Fin 13 → Bool => ((∃ v ∈ ({0, 1, 3} : Finset (Fin 13)), x v = true) ∨ ∃ s : Fin 13, ∀ v : Fin 13, x v = false → v ∈ L s))).card = 7170 ∧
    (Finset.univ.filter (fun x : Fin 13 → Bool => ∃ s : Fin 13, ∀ v : Fin 13, x v = false → v ∈ L s)).card = 157 ∧
    (∀ x y : Fin 13 → Bool, ((∃ v ∈ ({0, 1, 3} : Finset (Fin 13)), x v = true) ∨ ∃ s : Fin 13, ∀ v : Fin 13, x v = false → v ∈ L s) → (∀ v : Fin 13, x v = true → y v = true) → ((∃ v ∈ ({0, 1, 3} : Finset (Fin 13)), y v = true) ∨ ∃ s : Fin 13, ∀ v : Fin 13, y v = false → v ∈ L s)) := by
  intro L hL
  have eq : L = line := funext hL
  subst L
  exact ⟨describe, hitDiff, countTogether countHit, countContained, upClosed⟩

end DeepLineCount

theorem PEqualNP.Outside.L_meta_1520 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    (∀ x : Fin 13 → Bool, ((∃ v ∈ ({0, 1, 3} : Finset (Fin 13)), x v = true) ∨ ∃ s : Fin 13, ∀ v : Fin 13, x v = false → v ∈ L s) ↔
      ((∃ v ∈ ({0, 1, 3} : Finset (Fin 13)), x v = true) ∨ x = (fun v : Fin 13 => decide (v ∉ L 0)) ∨ x = (fun v : Fin 13 => decide (v ∉ L 0 ∨ v = 9)))) ∧
    (∀ x : Fin 13 → Bool, (∃ v ∈ ({0, 1, 3} : Finset (Fin 13)), x v = true) → x ≠ (fun v : Fin 13 => decide (v ∉ L 0)) ∧ x ≠ (fun v : Fin 13 => decide (v ∉ L 0 ∨ v = 9))) ∧
    (Finset.univ.filter (fun x : Fin 13 → Bool => ((∃ v ∈ ({0, 1, 3} : Finset (Fin 13)), x v = true) ∨ ∃ s : Fin 13, ∀ v : Fin 13, x v = false → v ∈ L s))).card = 7170 ∧
    (Finset.univ.filter (fun x : Fin 13 → Bool => ∃ s : Fin 13, ∀ v : Fin 13, x v = false → v ∈ L s)).card = 157 ∧
    (∀ x y : Fin 13 → Bool, ((∃ v ∈ ({0, 1, 3} : Finset (Fin 13)), x v = true) ∨ ∃ s : Fin 13, ∀ v : Fin 13, x v = false → v ∈ L s) → (∀ v : Fin 13, x v = true → y v = true) → ((∃ v ∈ ({0, 1, 3} : Finset (Fin 13)), y v = true) ∨ ∃ s : Fin 13, ∀ v : Fin 13, y v = false → v ∈ L s)) :=
  DeepLineCount.mainProof DeepLineCountA.lineCountA DeepLineCountB.lineCountB
