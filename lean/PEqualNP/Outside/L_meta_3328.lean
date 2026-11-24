import Mathlib.Data.List.Basic
import Mathlib.Tactic.Tauto

theorem PEqualNP.Outside.L_meta_3328 :
    have x1 : List ℕ → ℕ → Prop := fun (x1 : List ℕ) (x2 : ℕ) => ∃ x3 ∈ x1, ∃ x4 ∈ x1, x2 = x3 &&& x4 ∨ x2 = x3 ||| x4; have x2 : List ℕ → List ℕ → Prop := fun (x2 x3 : List ℕ) => ∀ (x4 : Fin x3.length), x1 (x2 ++ List.take (↑x4) x3) (x3.get x4); ∀ (x3 : List ℕ) (x4 x5 : ℕ) (x6 : List ℕ), x5 ∉ x3 → x1 x3 x4 → x2 (x4 :: x3) x6 → x1 (x4 :: x3 ++ x6) x5 → ∃ (x11 : List ℕ), x11.length ≤ x6.length + (2 : ℕ) ∧ x11.Nodup ∧ (∀ x12 ∈ x11, x12 ∉ x3) ∧ x5 ∈ x11 ∧ x2 x3 x11 := by
  intro allowed runs base first goal rest goalNew firstAllowed restRuns goalAllowed
  have move {left right : List ℕ} {a : ℕ} (sub : ∀ n ∈ left, n ∈ right)
      (h : allowed left a) : allowed right a := by
    obtain ⟨u, hu, v, hv, computes⟩ := h
    exact ⟨u, sub u hu, v, sub v hv, computes⟩
  have moveRuns {left right tail : List ℕ} (sub : ∀ n ∈ left, n ∈ right)
      (h : runs left tail) : runs right tail := by
    intro i
    apply move (h := h i)
    intro n hn
    rcases List.mem_append.mp hn with hn | hn
    · exact List.mem_append_left _ (sub n hn)
    · exact List.mem_append_right _ hn
  have reorder (s t : List ℕ) (a n : ℕ) :
      n ∈ s ++ a :: t ↔ n ∈ (a :: s) ++ t := by
    simp only [List.mem_append, List.mem_cons]
    tauto
  have runsNil (s : List ℕ) : runs s [] := by
    intro i
    exact Fin.elim0 i
  have runsCons (s t : List ℕ) (a : ℕ) :
      runs s (a :: t) ↔ allowed s a ∧ runs (a :: s) t := by
    constructor
    · intro h
      constructor
      · simpa only [Fin.val_zero, List.take_zero, List.append_nil, List.get_cons_zero] using h 0
      · intro i
        have ha := h i.succ
        change allowed (s ++ (a :: t).take (i.val + 1)) ((a :: t).get i.succ) at ha
        simp only [List.take_succ_cons, List.get_cons_succ'] at ha
        exact move (fun n hn => (reorder s _ a n).mp hn) ha
    · rintro ⟨ha, ht⟩ i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa only [Fin.val_zero, List.take_zero, List.append_nil, List.get_cons_zero] using ha
      · change allowed (s ++ (a :: t).take (j.val + 1)) ((a :: t).get j.succ)
        simp only [List.take_succ_cons, List.get_cons_succ']
        exact move (fun n hn => (reorder s _ a n).mpr hn) (ht j)
  have snoc (s t : List ℕ) (a : ℕ) (ht : runs s t)
      (ha : allowed (s ++ t) a) : runs s (t ++ [a]) := by
    induction t generalizing s with
    | nil =>
      exact (runsCons s [] a).mpr ⟨by simpa only [List.append_nil] using ha, runsNil _⟩
    | cons b t ih =>
      obtain ⟨hb, tailRuns⟩ := (runsCons s t b).mp ht
      apply (runsCons s (t ++ [a]) b).mpr
      refine ⟨hb, ih (b :: s) tailRuns ?_⟩
      exact move (fun n hn => (reorder s t b n).mp hn) ha
  have clean (s t : List ℕ) (ht : runs s t) :
      ∃ u : List ℕ, u.length ≤ t.length ∧ u.Nodup ∧
        (∀ n ∈ u, n ∉ s) ∧ (∀ n ∈ t, n ∈ s ∨ n ∈ u) ∧ runs s u := by
    induction t generalizing s with
    | nil =>
      refine ⟨[], Nat.le_refl _, List.nodup_nil, ?_, ?_, runsNil _⟩ <;> simp
    | cons a t ih =>
      obtain ⟨ha, tailRuns⟩ := (runsCons s t a).mp ht
      by_cases seen : a ∈ s
      · have sub : ∀ n ∈ a :: s, n ∈ s := by
          intro n hn
          rcases List.mem_cons.mp hn with rfl | old
          · exact seen
          · exact old
        obtain ⟨u, len, uniq, fresh, kept, valid⟩ := ih s (moveRuns sub tailRuns)
        refine ⟨u, Nat.le_trans len (Nat.le_succ _), uniq, fresh, ?_, valid⟩
        intro n hn
        rcases List.mem_cons.mp hn with rfl | hn
        · exact Or.inl seen
        · exact kept n hn
      · obtain ⟨u, len, uniq, fresh, kept, valid⟩ := ih (a :: s) tailRuns
        refine ⟨a :: u, Nat.succ_le_succ len, List.nodup_cons.mpr ⟨?_, uniq⟩, ?_, ?_,
          (runsCons s u a).mpr ⟨ha, valid⟩⟩
        · exact fun hn => fresh a hn List.mem_cons_self
        · intro n hn
          rcases List.mem_cons.mp hn with rfl | hn
          · exact seen
          · exact fun old => fresh n hn (List.mem_cons_of_mem _ old)
        · intro n hn
          rcases List.mem_cons.mp hn with rfl | hn
          · exact Or.inr List.mem_cons_self
          · rcases kept n hn with old | found
            · rcases List.mem_cons.mp old with rfl | old
              · exact Or.inr List.mem_cons_self
              · exact Or.inl old
            · exact Or.inr (List.mem_cons_of_mem _ found)
  have withGoal : runs (first :: base) (rest ++ [goal]) :=
    snoc _ _ _ restRuns goalAllowed
  have allRuns : runs base (first :: (rest ++ [goal])) :=
    (runsCons _ _ _).mpr ⟨firstAllowed, withGoal⟩
  obtain ⟨u, len, uniq, fresh, kept, valid⟩ := clean _ _ allRuns
  have goalKept := kept goal (List.mem_cons_of_mem first (List.mem_append_right _ (by simp)))
  have bound : u.length ≤ rest.length + 2 := by
    simp only [List.length_cons, List.length_append, List.length_nil] at len
    omega
  exact ⟨u, bound, uniq, fresh, goalKept.resolve_left goalNew, valid⟩
