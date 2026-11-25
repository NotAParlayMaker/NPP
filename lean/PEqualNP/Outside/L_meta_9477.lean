import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9477_aux

open PEqualNP.ProofComplexity PEqualNP.Search

variable {V : Type} [DecidableEq V]

-- fs holds literals already known false. A trail entry names a clause that is
-- either the contradiction, every literal false, or a unit whose other
-- literals are false, so its remaining literal is forced true.
def replay (db : List (List (Literal V))) (fs : List (Literal V)) : List Nat → Bool
  | [] => false
  | i :: trail =>
    match db[i]? with
    | none => false
    | some d =>
      match d.filter (fun l => !fs.contains l) with
      | [] => true
      | [l] => replay db (negLit l :: fs) trail
      | _ => false

-- each unit step is one use of UPForces.unit, and the final all-false clause
-- is the witness IsRUP asks for.
theorem replay_sound (db : List (List (Literal V))) (Γ : Set (Clause V))
    (A : Set (Literal V)) (hd : ∀ d ∈ db, d.toFinset ∈ Γ)
    (trail : List Nat) (fs : List (Literal V))
    (hf : ∀ l ∈ fs, UPForces Γ A (negLit l)) (h : replay db fs trail = true) :
    ∃ D ∈ Γ, ∀ l ∈ D, UPForces Γ A (negLit l) := by
  induction trail generalizing fs with
  | nil => simp [replay] at h
  | cons i trail ih =>
    simp only [replay] at h
    split at h
    · contradiction
    next d he =>
      have hm := hd d (List.mem_of_getElem? he)
      split at h
      next hnil =>
        refine ⟨d.toFinset, hm, ?_⟩
        intro l hl
        have hld : l ∈ d := List.mem_toFinset.mp hl
        apply hf
        by_contra hn
        have : l ∈ d.filter (fun l => !fs.contains l) := by simp [hld, hn]
        rw [hnil] at this
        exact List.not_mem_nil this
      next l hsingle =>
        have hld : l ∈ d.filter (fun v => !fs.contains v) := by
          rw [hsingle]
          exact List.mem_cons_self
        have hu : UPForces Γ A l := by
          apply UPForces.unit hm (List.mem_toFinset.mpr (List.mem_filter.mp hld).1)
          intro v hv hne
          apply hf
          by_contra hn
          have hvd : v ∈ d := List.mem_toFinset.mp hv
          have : v ∈ d.filter (fun x => !fs.contains x) := by simp [hvd, hn]
          rw [hsingle] at this
          exact hne (List.mem_singleton.mp this)
        apply ih (negLit l :: fs) _ h
        intro v hv
        rcases List.mem_cons.mp hv with rfl | hv
        · simpa [negLit] using hu
        · exact hf v hv
      next => contradiction

def verify (db : List (List (Literal V))) :
    List (List (Literal V) × List Nat) → Bool
  | [] => true
  | (c, trail) :: rest => replay db c trail && verify (db ++ [c]) rest

-- newest clause first, matching the way IsRUPRun learns by cons
def learned (s : List (List (Literal V) × List Nat)) (ρ : List (Clause V)) :=
  s.foldl (fun acc p => p.1.toFinset :: acc) ρ

theorem verify_sound (F : Set (Clause V)) (steps : List (List (Literal V) × List Nat))
    (db : List (List (Literal V))) (ρ : List (Clause V)) (hr : IsRUPRun F ρ)
    (hd : ∀ d ∈ db, d.toFinset ∈ F ∪ {D | D ∈ ρ}) (h : verify db steps = true) :
    IsRUPRun F (learned steps ρ) := by
  induction steps generalizing db ρ with
  | nil => exact hr
  | cons head rest ih =>
    obtain ⟨c, trail⟩ := head
    have ⟨ht, hs⟩ := Bool.and_eq_true_iff.mp h
    have hc : IsRUP (F ∪ {D | D ∈ ρ}) c.toFinset := by
      apply replay_sound db _ _ hd trail c _ ht
      intro l hl
      exact UPForces.hyp ⟨l, List.mem_toFinset.mpr hl, rfl⟩
    apply ih (db ++ [c]) (c.toFinset :: ρ) (IsRUPRun.learn hr hc) _ hs
    intro d hmem
    rcases List.mem_append.mp hmem with hm | hm
    · rcases hd d hm with hF | hρ
      · exact Or.inl hF
      · exact Or.inr (List.mem_cons_of_mem _ hρ)
    · have he : d = c := by simpa using hm
      exact Or.inr (he ▸ List.mem_cons_self)

abbrev Board := Fin (5 + 1) × Fin 5

def row (p : Fin (5 + 1)) : List (Literal Board) :=
  (List.finRange 5).map (fun h => ((p, h), true))

def block (p q : Fin (5 + 1)) (h : Fin 5) : List (Literal Board) :=
  [((p, h), false), ((q, h), false)]

-- pigeon clauses first, then every pairwise exclusion, so the trails have stable indices
def input : List (List (Literal Board)) :=
  (List.finRange (5 + 1)).map row ++ (List.finRange 5).flatMap (fun h =>
    (List.finRange (5 + 1)).flatMap (fun p =>
      ((List.finRange (5 + 1)).filter (fun q => p < q)).map (fun q => block p q h)))

theorem input_sound (d : List (Literal Board)) (hd : d ∈ input) :
    d.toFinset ∈ PHP (5 + 1) 5 := by
  rcases List.mem_append.mp hd with hr | hb
  · obtain ⟨p, _, rfl⟩ := List.mem_map.mp hr
    left
    refine ⟨p, ?_⟩
    ext l
    simp [row]
  · obtain ⟨h, _, hh⟩ := List.mem_flatMap.mp hb
    obtain ⟨p, _, hp⟩ := List.mem_flatMap.mp hh
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    right
    exact ⟨p, q, h, ne_of_lt (of_decide_eq_true (List.mem_filter.mp hq).2), by simp [block]⟩

-- 63 learned clauses and then the empty clause; each trail is one unit-propagation
def steps : List (List (Literal Board) × List Nat) := [
  ([((3, 3), false), ((4, 0), true), ((4, 1), true), ((4, 2), true), ((5, 0), true), ((5, 1), true), ((5, 2), true)], [53, 57, 60, 63, 4, 64, 5, 80]),
  ([((2, 2), false), ((3, 0), true), ((3, 1), true), ((4, 0), true), ((4, 1), true), ((5, 0), true), ((5, 1), true)], [37, 41, 45, 46, 47, 81, 3, 68, 72, 75, 78, 4, 54, 58, 61, 63, 65, 5, 79]),
  ([((3, 2), false), ((4, 0), true), ((4, 1), true), ((4, 3), true), ((5, 0), true), ((5, 1), true), ((5, 3), true)], [38, 42, 45, 48, 4, 49, 5, 80]),
  ([((2, 3), false), ((3, 0), true), ((3, 1), true), ((4, 0), true), ((4, 1), true), ((5, 0), true), ((5, 1), true)], [52, 56, 60, 61, 62, 82, 83, 3, 68, 72, 75, 78, 4, 39, 43, 46, 48, 50, 5, 79]),
  ([((2, 4), false), ((3, 0), true), ((3, 1), true), ((3, 2), false), ((4, 0), true), ((4, 1), true), ((5, 0), true), ((5, 1), true), ((5, 4), true)], [38, 42, 45, 48, 49, 5, 55, 59, 62, 64, 65, 4, 76]),
  ([((1, 1), false), ((2, 0), true), ((3, 0), true), ((4, 0), true), ((5, 0), true)], [21, 26, 27, 28, 29, 82, 84, 2, 67, 71, 75, 76, 77, 85, 3, 53, 57, 60, 63, 4, 39, 0, 6, 7, 8, 9, 10, 43, 1, 46, 48, 50, 5, 64]),
  ([((2, 1), false), ((3, 0), true), ((3, 2), true), ((4, 0), true), ((4, 2), true), ((5, 0), true), ((5, 2), true)], [22, 26, 30, 31, 32, 81, 3, 68, 72, 75, 78, 4, 54, 58, 61, 63, 65, 5, 79]),
  ([((3, 1), false), ((4, 0), true), ((4, 2), true), ((4, 3), true), ((5, 0), true), ((5, 2), true), ((5, 3), true)], [23, 27, 30, 33, 4, 34, 5, 80]),
  ([((2, 3), false), ((3, 0), true), ((3, 2), true), ((4, 0), true), ((4, 2), true), ((5, 0), true), ((5, 2), true)], [52, 56, 60, 61, 62, 87, 88, 3, 68, 72, 75, 78, 4, 24, 28, 31, 33, 35, 5, 79]),
  ([((2, 4), false), ((3, 0), true), ((3, 1), false), ((3, 2), true), ((4, 0), true), ((4, 2), true), ((5, 0), true), ((5, 2), true), ((5, 4), true)], [23, 27, 30, 33, 34, 5, 55, 59, 62, 64, 65, 4, 76]),
  ([((1, 2), false), ((2, 0), true), ((3, 0), true), ((4, 0), true), ((5, 0), true)], [36, 41, 42, 43, 44, 86, 87, 89, 2, 67, 71, 75, 76, 77, 90, 3, 53, 57, 60, 63, 4, 24, 0, 6, 1, 7, 8, 9, 10, 28, 31, 33, 35, 5, 64]),
  ([((2, 1), false), ((3, 0), true), ((3, 3), true), ((4, 0), true), ((4, 3), true), ((5, 0), true), ((5, 3), true)], [22, 26, 30, 31, 32, 82, 83, 3, 68, 72, 75, 78, 4, 39, 43, 46, 48, 50, 5, 79]),
  ([((2, 2), false), ((3, 0), true), ((3, 3), true), ((4, 0), true), ((4, 3), true), ((5, 0), true), ((5, 3), true)], [37, 41, 45, 46, 47, 87, 88, 3, 68, 72, 75, 78, 4, 24, 28, 31, 33, 35, 5, 79]),
  ([((2, 4), false), ((3, 0), true), ((3, 1), false), ((3, 3), true), ((4, 0), true), ((4, 3), true), ((5, 0), true), ((5, 3), true), ((5, 4), true)], [23, 27, 30, 33, 34, 5, 40, 44, 47, 49, 50, 4, 76]),
  ([((1, 3), false), ((2, 0), true), ((3, 0), true), ((4, 0), true), ((5, 0), true)], [51, 56, 57, 58, 59, 86, 91, 92, 93, 2, 67, 71, 75, 76, 77, 94, 3, 38, 42, 45, 48, 4, 24, 0, 6, 1, 7, 8, 9, 10, 28, 31, 33, 35, 5, 49]),
  ([((3, 2), false), ((4, 0), true), ((4, 1), true), ((4, 4), true), ((5, 0), true), ((5, 1), true), ((5, 4), true)], [38, 42, 45, 48, 4, 49, 5, 65]),
  ([((1, 4), false), ((2, 0), true), ((2, 1), false), ((3, 0), true), ((3, 4), true), ((4, 0), true), ((4, 4), true), ((5, 0), true), ((5, 4), true)], [22, 26, 30, 31, 32, 66, 71, 72, 73, 74, 82, 84, 2, 86, 91, 95, 96, 3, 53, 57, 60, 63, 4, 39, 0, 6, 1, 7, 8, 9, 10, 43, 46, 48, 50, 5, 64]),
  ([((3, 1), false), ((4, 0), true), ((4, 2), true), ((4, 4), true), ((5, 0), true), ((5, 2), true), ((5, 4), true)], [23, 27, 30, 33, 4, 34, 5, 65]),
  ([((1, 4), false), ((2, 0), true), ((2, 1), true), ((2, 2), false), ((3, 0), true), ((3, 4), true), ((4, 0), true), ((4, 4), true), ((5, 0), true), ((5, 4), true)], [37, 41, 45, 46, 47, 66, 71, 72, 73, 74, 86, 87, 89, 2, 91, 95, 97, 98, 3, 53, 57, 60, 63, 4, 24, 0, 6, 1, 7, 8, 9, 10, 28, 31, 33, 35, 5, 64]),
  ([((1, 4), false), ((2, 0), true), ((2, 2), true), ((3, 0), true), ((3, 1), false), ((4, 0), true), ((4, 3), true), ((5, 0), true), ((5, 3), true), ((5, 4), true)], [23, 27, 30, 33, 34, 5, 40, 44, 47, 49, 50, 4, 73]),
  ([((0, 0), false)], [6, 7, 8, 9, 10, 86, 91, 95, 1, 66, 71, 72, 73, 74, 97, 99, 2, 52, 56, 60, 61, 62, 92, 93, 100, 3, 38, 42, 45, 48, 4, 24, 0, 28, 31, 33, 35, 5, 49]),
  ([((1, 0), false), ((2, 1), true), ((3, 1), true), ((4, 1), true), ((5, 1), true)], [6, 11, 12, 13, 14, 82, 84, 2, 67, 71, 75, 76, 77, 85, 3, 53, 57, 60, 63, 4, 39, 0, 21, 22, 23, 24, 25, 43, 1, 46, 48, 50, 5, 64]),
  ([((2, 0), false), ((3, 1), true), ((3, 2), true), ((4, 1), true), ((4, 2), true), ((5, 1), true), ((5, 2), true)], [7, 11, 15, 16, 17, 81, 3, 68, 72, 75, 78, 4, 54, 58, 61, 63, 65, 5, 79]),
  ([((3, 0), false), ((4, 1), true), ((4, 2), true), ((4, 3), true), ((5, 1), true), ((5, 2), true), ((5, 3), true)], [8, 12, 15, 18, 4, 19, 5, 80]),
  ([((2, 3), false), ((3, 1), true), ((3, 2), true), ((4, 1), true), ((4, 2), true), ((5, 1), true), ((5, 2), true)], [52, 56, 60, 61, 62, 101, 103, 104, 3, 68, 72, 75, 78, 4, 9, 13, 16, 18, 20, 5, 79]),
  ([((1, 2), false), ((2, 1), true), ((2, 3), true), ((3, 0), false), ((3, 1), true), ((4, 1), true), ((4, 2), true), ((5, 1), true), ((5, 2), true), ((5, 4), true)], [8, 12, 15, 18, 19, 5, 36, 41, 2, 42, 43, 44, 55, 59, 62, 64, 65, 4, 76]),
  ([((1, 2), false), ((2, 1), true), ((3, 1), true), ((4, 1), true), ((5, 1), true)], [36, 41, 42, 43, 44, 101, 102, 103, 105, 2, 67, 71, 75, 76, 77, 106, 3, 53, 0, 21, 22, 23, 24, 25, 57, 1, 60, 63, 4, 9, 13, 16, 18, 20, 5, 64]),
  ([((2, 0), false), ((3, 1), true), ((3, 3), true), ((4, 1), true), ((4, 3), true), ((5, 1), true), ((5, 3), true)], [7, 11, 15, 16, 17, 82, 83, 3, 68, 72, 75, 78, 4, 39, 43, 46, 48, 50, 5, 79]),
  ([((2, 2), false), ((3, 1), true), ((3, 3), true), ((4, 1), true), ((4, 3), true), ((5, 1), true), ((5, 3), true)], [37, 41, 45, 46, 47, 101, 103, 104, 3, 68, 72, 75, 78, 4, 9, 13, 16, 18, 20, 5, 79]),
  ([((1, 3), false), ((2, 1), true), ((2, 2), true), ((3, 0), false), ((3, 1), true), ((4, 1), true), ((4, 3), true), ((5, 1), true), ((5, 3), true), ((5, 4), true)], [8, 12, 15, 18, 19, 5, 40, 44, 47, 49, 50, 4, 51, 56, 2, 76]),
  ([((1, 3), false), ((2, 1), true), ((3, 1), true), ((4, 1), true), ((5, 1), true)], [51, 56, 57, 58, 59, 101, 102, 107, 108, 109, 2, 67, 71, 75, 76, 77, 110, 3, 38, 0, 21, 1, 22, 23, 24, 25, 42, 45, 48, 4, 9, 13, 16, 18, 20, 5, 49]),
  ([((1, 4), false), ((2, 0), false), ((2, 1), true), ((3, 1), true), ((3, 4), true), ((4, 1), true), ((4, 4), true), ((5, 1), true), ((5, 4), true)], [7, 11, 15, 16, 17, 66, 71, 72, 73, 74, 82, 84, 2, 96, 3, 53, 57, 60, 63, 4, 39, 0, 21, 22, 23, 24, 25, 43, 1, 46, 48, 50, 5, 64]),
  ([((3, 0), false), ((4, 1), true), ((4, 2), true), ((4, 4), true), ((5, 1), true), ((5, 2), true), ((5, 4), true)], [8, 12, 15, 18, 4, 19, 5, 65]),
  ([((1, 4), false), ((2, 0), true), ((2, 1), true), ((2, 2), false), ((3, 1), true), ((3, 4), true), ((4, 1), true), ((4, 4), true), ((5, 1), true), ((5, 4), true)], [37, 41, 45, 46, 47, 66, 71, 72, 73, 74, 101, 102, 103, 105, 2, 107, 111, 112, 113, 3, 53, 0, 21, 1, 22, 23, 24, 25, 57, 60, 63, 4, 9, 13, 16, 18, 20, 5, 64]),
  ([((3, 0), false), ((4, 1), true), ((4, 3), true), ((4, 4), true), ((5, 1), true), ((5, 3), true), ((5, 4), true)], [8, 12, 15, 18, 4, 19, 5, 50]),
  ([((0, 1), false)], [21, 22, 23, 24, 25, 101, 102, 107, 111, 1, 66, 71, 72, 73, 74, 112, 114, 2, 52, 56, 60, 61, 62, 108, 109, 115, 3, 38, 0, 42, 45, 48, 4, 9, 13, 16, 18, 20, 5, 49]),
  ([((1, 0), false), ((2, 2), true), ((3, 2), true), ((4, 2), true), ((5, 2), true)], [6, 11, 12, 13, 14, 86, 87, 89, 2, 67, 71, 75, 76, 77, 90, 3, 53, 57, 60, 63, 4, 24, 0, 28, 31, 33, 35, 5, 64]),
  ([((1, 1), false), ((2, 2), true), ((3, 2), true), ((4, 2), true), ((5, 2), true)], [21, 26, 27, 28, 29, 101, 102, 103, 105, 2, 67, 71, 75, 76, 77, 107, 111, 1, 113, 3, 53, 0, 36, 37, 38, 39, 40, 57, 60, 63, 4, 9, 13, 16, 18, 20, 5, 64]),
  ([((2, 0), false), ((3, 2), true), ((3, 3), true), ((4, 2), true), ((4, 3), true), ((5, 2), true), ((5, 3), true)], [7, 11, 15, 16, 17, 87, 88, 3, 68, 72, 75, 78, 4, 24, 28, 31, 33, 35, 5, 79]),
  ([((2, 1), false), ((3, 2), true), ((3, 3), true), ((4, 2), true), ((4, 3), true), ((5, 2), true), ((5, 3), true)], [22, 26, 30, 31, 32, 101, 103, 104, 3, 68, 72, 75, 78, 4, 9, 13, 16, 18, 20, 5, 79]),
  ([((1, 3), false), ((2, 1), true), ((2, 2), true), ((3, 0), false), ((3, 2), true), ((4, 2), true), ((4, 3), true), ((5, 2), true), ((5, 3), true), ((5, 4), true)], [8, 12, 15, 18, 19, 5, 25, 29, 32, 34, 35, 4, 51, 56, 2, 76]),
  ([((1, 3), false), ((2, 2), true), ((3, 2), true), ((4, 2), true), ((5, 2), true)], [51, 56, 57, 58, 59, 101, 116, 117, 118, 119, 120, 2, 67, 0, 36, 37, 38, 39, 40, 71, 1, 75, 76, 77, 121, 3, 23, 27, 30, 33, 4, 9, 13, 16, 18, 20, 5, 34]),
  ([((1, 4), false), ((2, 0), false), ((2, 2), true), ((3, 2), true), ((3, 4), true), ((4, 2), true), ((4, 4), true), ((5, 2), true), ((5, 4), true)], [7, 11, 15, 16, 17, 66, 71, 72, 73, 74, 87, 89, 2, 98, 3, 53, 57, 60, 63, 4, 24, 0, 28, 31, 33, 35, 5, 64]),
  ([((1, 4), false), ((2, 0), true), ((2, 1), false), ((2, 2), true), ((3, 2), true), ((3, 4), true), ((4, 2), true), ((4, 4), true), ((5, 2), true), ((5, 4), true)], [22, 26, 30, 31, 32, 66, 71, 72, 73, 74, 101, 103, 105, 2, 113, 3, 53, 0, 36, 37, 38, 39, 40, 57, 60, 63, 4, 9, 13, 1, 16, 18, 20, 5, 64]),
  ([((3, 0), false), ((4, 2), true), ((4, 3), true), ((4, 4), true), ((5, 2), true), ((5, 3), true), ((5, 4), true)], [8, 12, 15, 18, 4, 19, 5, 35]),
  ([((0, 2), false)], [36, 37, 38, 39, 40, 101, 116, 117, 118, 122, 1, 66, 71, 72, 73, 74, 123, 124, 2, 52, 0, 56, 60, 61, 62, 119, 120, 125, 3, 23, 27, 30, 33, 4, 9, 13, 16, 18, 20, 5, 34]),
  ([((1, 0), false), ((2, 3), true), ((3, 3), true), ((4, 3), true), ((5, 3), true)], [6, 11, 12, 13, 14, 86, 91, 92, 93, 2, 67, 71, 75, 76, 77, 94, 3, 38, 42, 45, 48, 4, 24, 0, 28, 31, 33, 35, 5, 49]),
  ([((1, 1), false), ((2, 3), true), ((3, 3), true), ((4, 3), true), ((5, 3), true)], [21, 26, 27, 28, 29, 101, 102, 107, 108, 109, 2, 67, 71, 75, 76, 77, 111, 1, 115, 3, 38, 0, 42, 45, 48, 4, 9, 13, 16, 18, 20, 5, 49]),
  ([((1, 2), false), ((2, 3), true), ((3, 3), true), ((4, 3), true), ((5, 3), true)], [36, 41, 42, 43, 44, 101, 116, 117, 118, 119, 120, 2, 67, 0, 51, 52, 53, 54, 55, 71, 1, 75, 76, 77, 122, 125, 3, 23, 27, 30, 33, 4, 9, 13, 16, 18, 20, 5, 34]),
  ([((3, 1), false), ((4, 0), true), ((4, 3), true), ((4, 4), true), ((5, 0), true), ((5, 3), true), ((5, 4), true)], [23, 27, 30, 33, 4, 34, 5, 50]),
  ([((2, 0), false), ((3, 3), true), ((3, 4), true), ((4, 3), true), ((4, 4), true), ((5, 3), true), ((5, 4), true)], [7, 11, 15, 16, 17, 92, 93, 101, 116, 126, 130, 3, 38, 42, 45, 48, 4, 24, 28, 31, 33, 35, 5, 49]),
  ([((0, 3), false), ((1, 0), true), ((1, 2), true), ((2, 0), true), ((2, 1), false), ((3, 3), true), ((3, 4), true), ((4, 3), true), ((4, 4), true), ((5, 3), true), ((5, 4), true)], [22, 26, 30, 31, 32, 51, 1, 52, 53, 54, 55, 66, 71, 72, 73, 74, 101, 108, 109, 2, 115, 3, 38, 0, 42, 45, 48, 4, 9, 13, 16, 18, 20, 5, 49]),
  ([((0, 3), false)], [51, 52, 53, 54, 55, 101, 116, 126, 127, 128, 129, 1, 66, 0, 71, 72, 73, 74, 131, 132, 2, 37, 41, 45, 46, 47, 119, 120, 125, 3, 23, 27, 30, 33, 4, 9, 13, 16, 18, 20, 5, 34]),
  ([((2, 1), false), ((3, 0), true), ((3, 4), true), ((4, 0), true), ((4, 4), true), ((5, 0), true), ((5, 4), true)], [22, 26, 30, 31, 32, 82, 84, 96, 3, 53, 57, 60, 63, 4, 39, 43, 46, 48, 50, 5, 64]),
  ([((2, 2), false), ((3, 0), true), ((3, 4), true), ((4, 0), true), ((4, 4), true), ((5, 0), true), ((5, 4), true)], [37, 41, 45, 46, 47, 87, 89, 98, 3, 53, 57, 60, 63, 4, 24, 28, 31, 33, 35, 5, 64]),
  ([((1, 0), false), ((2, 4), true), ((3, 4), true), ((4, 4), true), ((5, 4), true)], [6, 11, 12, 13, 14, 86, 91, 95, 101, 116, 126, 133, 0, 66, 1, 67, 68, 69, 70, 134, 135, 2, 52, 56, 60, 61, 62, 92, 93, 127, 130, 3, 38, 42, 45, 48, 4, 24, 28, 31, 33, 35, 5, 49]),
  ([((2, 0), false), ((3, 1), true), ((3, 4), true), ((4, 1), true), ((4, 4), true), ((5, 1), true), ((5, 4), true)], [7, 11, 15, 16, 17, 82, 84, 96, 3, 53, 57, 60, 63, 4, 39, 43, 46, 48, 50, 5, 64]),
  ([((2, 2), false), ((3, 1), true), ((3, 4), true), ((4, 1), true), ((4, 4), true), ((5, 1), true), ((5, 4), true)], [37, 41, 45, 46, 47, 101, 103, 105, 113, 3, 53, 57, 60, 63, 4, 9, 13, 16, 18, 20, 5, 64]),
  ([((1, 1), false), ((2, 4), true), ((3, 4), true), ((4, 4), true), ((5, 4), true)], [21, 26, 27, 28, 29, 101, 102, 107, 111, 116, 126, 133, 0, 66, 1, 67, 68, 69, 70, 136, 137, 138, 2, 52, 56, 60, 61, 62, 108, 109, 115, 3, 38, 42, 45, 48, 4, 9, 13, 16, 18, 20, 5, 49]),
  ([((2, 0), false), ((3, 2), true), ((3, 4), true), ((4, 2), true), ((4, 4), true), ((5, 2), true), ((5, 4), true)], [7, 11, 15, 16, 17, 87, 89, 98, 3, 53, 57, 60, 63, 4, 24, 28, 31, 33, 35, 5, 64]),
  ([((2, 1), false), ((3, 2), true), ((3, 4), true), ((4, 2), true), ((4, 4), true), ((5, 2), true), ((5, 4), true)], [22, 26, 30, 31, 32, 101, 103, 105, 113, 3, 53, 57, 60, 63, 4, 9, 13, 16, 18, 20, 5, 64]),
  ([((0, 4), false), ((1, 0), true), ((1, 1), true), ((1, 2), false), ((2, 4), true), ((3, 4), true), ((4, 4), true), ((5, 4), true)], [36, 41, 42, 43, 44, 66, 67, 68, 69, 70, 101, 116, 117, 118, 122, 1, 126, 133, 0, 136, 139, 140, 141, 2, 52, 56, 60, 61, 62, 119, 120, 125, 3, 23, 27, 30, 33, 4, 9, 13, 16, 18, 20, 5, 34]),
  ([((2, 1), false), ((3, 3), true), ((3, 4), true), ((4, 3), true), ((4, 4), true), ((5, 3), true), ((5, 4), true)], [22, 26, 30, 31, 32, 101, 108, 109, 115, 3, 38, 42, 45, 48, 4, 9, 13, 16, 18, 20, 5, 49]),
  ([], [101, 116, 126, 133, 0, 66, 67, 68, 69, 70, 136, 139, 142, 1, 51, 56, 57, 58, 59, 127, 128, 129, 131, 143, 2, 37, 41, 45, 46, 47, 119, 120, 122, 125, 3, 23, 27, 30, 33, 4, 9, 13, 16, 18, 20, 5, 34])
]

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

theorem checked : verify input steps = true := by
  decide +kernel

theorem run : IsRUPRun (PHP (5 + 1) 5) (learned steps []) :=
  verify_sound _ _ _ _ IsRUPRun.nil (fun d hd => Or.inl (input_sound d hd)) checked

theorem containsEmpty : (∅ : Clause Board) ∈ learned steps [] := by
  decide +kernel

theorem count : (learned steps []).length ≤ 64 := by
  decide +kernel

end PEqualNP.Outside.L_meta_9477_aux

theorem PEqualNP.Outside.L_meta_9477 :
    ∃ ρ : List (PEqualNP.ProofComplexity.Clause (Fin (5 + 1) × Fin 5)),
      PEqualNP.Search.IsRUPRun (PEqualNP.ProofComplexity.PHP (5 + 1) 5) ρ ∧
        (∅ : PEqualNP.ProofComplexity.Clause (Fin (5 + 1) × Fin 5)) ∈ ρ ∧ ρ.length ≤ 64 :=
  ⟨PEqualNP.Outside.L_meta_9477_aux.learned PEqualNP.Outside.L_meta_9477_aux.steps [],
    PEqualNP.Outside.L_meta_9477_aux.run,
    PEqualNP.Outside.L_meta_9477_aux.containsEmpty,
    PEqualNP.Outside.L_meta_9477_aux.count⟩

