import Mathlib.Tactic
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.HeptadCover
open PEqualNP.GenericRejection

-- Each wire gives a rectangle of pairs on which its values differ.
-- A gate covers its rectangle by the rectangles of its two inputs.
-- The geometric premise extends a point arc and up to three nonconcurrent
-- exterior lines to a quadrangle. Closing the negative side of each rectangle
-- under deleting input bits keeps the same gates and includes all these pairs.
theorem PEqualNP.Outside.R_meta_4732_519
  (extract : ∀ (n : ℕ) (C : Circuit), 0 < n → Monotone2 C →
      (∀ j : Fin C.gates.length, ∀ w ∈ (C.gates.get j).inputs, w < n+j.val) →
      ∃ (R : ℕ → Set (List Bool × List Bool)) (o : ℕ), o < n+C.size ∧
        (∀ w, ∃ A B : Set (List Bool), R w = A ×ˢ B) ∧
        (∀ w < n, ∀ z ∈ R w, z.1.getD w false = true ∧ z.2.getD w false = false) ∧
        (∀ j < C.size, ∃ a < n+j, ∃ b < n+j, R (n+j) ⊆ R a ∪ R b) ∧
        ∀ x y : List Bool, x.length = n → y.length = n →
          C.eval x = true → C.eval y = false → (x,y) ∈ R o)
  (extension : let S := singerLines3
    ∀ P L : Finset (Fin 13), (∀ l, (P ∩ S l).card ≤ 2) → L ⊆ missLines S P →
      L.card ≤ 3 → (∀ p : Fin 13, (L.filter (fun l => p ∈ S l)).card ≤ 2) →
      ∃ Q ∈ quadrangles S, P ⊆ Q ∧ L ⊆ missLines S Q)
  (lower : let S := singerLines3
    ∀ (m : ℕ) (R : ℕ → Set (List Bool × List Bool)) (o : ℕ), o < 27+m →
      (∀ w, ∃ A B : Set (List Bool), R w = A ×ˢ B) →
      (∀ w < 27, ∀ z ∈ R w, z.1.getD w false = true ∧ z.2.getD w false = false) →
      (∀ j < m, ∃ a < 27+j, ∃ b < 27+j, R (27+j) ⊆ R a ∪ R b) →
      ∀ (l : Fin 13) (b : Bool),
        (∀ e ∈ incidences S, e ≠ (0,l) → ∀ P L : Finset (Fin 13),
          (∀ l, (P ∩ S l).card ≤ 2) → L ⊆ missLines S P → L.card ≤ 3 →
          (∀ p : Fin 13, (L.filter (fun l => p ∈ S l)).card ≤ 2) →
          (incidenceInput {e.1} {e.2} ++ [b], incidenceInput P L ++ [b]) ∈ R o) →
        63 ≤ m) :
  have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → List Bool := fun (x2 x3 : Fin (13 : ℕ)) => (List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 = x2)) ++ List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 = x3); have x3 : Finset (Fin (13 : ℕ)) → List Bool := fun (x3 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 ∈ x3)) ++ List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (∀ x5 ∈ x3, x5 - x4 ∉ x1); have x4 : Finset (Fin (13 : ℕ)) → Prop := fun (x4 : Finset (Fin (13 : ℕ))) => x4.card = (4 : ℕ) ∧ ∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x4 | x6 - x5 ∈ x1}.card ≤ (2 : ℕ); ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : Fin (13 : ℕ)) (x7 : Bool), PEqualNP.MetaComplexity.Monotone2 x5 → (∀ (x9 : Fin x5.gates.length), ∀ x10 ∈ (x5.gates.get x9).inputs, x10 < (27 : ℕ) + ↑x9) → (∀ (x10 x11 : Fin (13 : ℕ)), x10 - x11 ∈ x1 → x10 ≠ (0 : Fin (13 : ℕ)) ∨ x11 ≠ x6 → x5.eval (x2 x10 x11 ++ [x7]) = Bool.true) → (∀ (x11 : Finset (Fin (13 : ℕ))), x4 x11 → x5.eval (x3 x11 ++ [x7]) = Bool.false) → (63 : ℕ) ≤ x5.size := by
  dsimp only
  intro C l b hm hw hp hn
  obtain ⟨R,o,ho,hrect,hleaf,hgrow,hout⟩ := extract 27 C (by decide) hm hw
  let leBits (y z : List Bool) := ∀ i, y.getD i false = true → z.getD i false = true
  let wide (w : ℕ) : Set (List Bool × List Bool) :=
    {pair | ∃ y, leBits pair.2 y ∧ (pair.1,y) ∈ R w}
  have rect (w : ℕ) : ∃ A B : Set (List Bool), wide w = A ×ˢ B := by
    obtain ⟨A,B,eqn⟩ := hrect w
    refine ⟨A, {z | ∃ y ∈ B, leBits z y}, ?_⟩
    ext pair
    constructor
    · rintro ⟨y,h,r⟩
      rw [eqn] at r
      exact ⟨r.1,y,r.2,h⟩
    · rintro ⟨hx,y,hy,h⟩
      exact ⟨y,h,eqn ▸ ⟨hx,hy⟩⟩
  have leaves (w : ℕ) (hw : w < 27) :
      ∀ z ∈ wide w, z.1.getD w false = true ∧ z.2.getD w false = false := by
    rintro z ⟨y,hy,mem⟩
    obtain ⟨hx,hzero⟩ := hleaf w hw (z.1,y) mem
    refine ⟨hx, ?_⟩
    cases h : z.2.getD w false with
    | false => rfl
    | true => exact Bool.noConfusion ((hy w h).symm.trans hzero)
  have grow (j : ℕ) (hj : j < C.size) :
      ∃ u < 27+j, ∃ v < 27+j, wide (27+j) ⊆ wide u ∪ wide v := by
    obtain ⟨u,hu,v,hv,sub⟩ := hgrow j hj
    refine ⟨u,hu,v,hv,?_⟩
    rintro z ⟨y,hy,mem⟩
    rcases sub mem with left | right
    · exact Or.inl ⟨y,hy,left⟩
    · exact Or.inr ⟨y,hy,right⟩
  have appendLe {a c d f : List Bool} (length : a.length = c.length) (ac : leBits a c)
      (df : leBits d f) : leBits (a ++ d) (c ++ f) := by
    intro i
    by_cases hi : i < a.length
    · rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ (length ▸ hi)]
      exact ac i
    · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), length]
      exact df _
  have bits {P Q : Finset (Fin 13)} (sub : P ⊆ Q) :
      leBits (List.ofFn (fun p : Fin 13 => decide (p ∈ P))) (List.ofFn (fun p : Fin 13 => decide (p ∈ Q))) := by
    intro i
    by_cases hi : i < 13
    · simpa only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi, dite_true, Option.getD_some, decide_eq_true_eq] using
        (show (⟨i,hi⟩ : Fin 13) ∈ P → (⟨i,hi⟩ : Fin 13) ∈ Q from fun h => sub h)
    · rw [List.getD_eq_default _ _ (by simp; omega)]
      simp
  apply lower C.size wide o ho rect leaves grow l b
  intro e he hne P L hpArc dis count hlArc
  obtain ⟨Q,hQ,hP,hL⟩ := extension P L hpArc dis count hlArc
  refine ⟨incidenceInput Q (missLines singerLines3 Q) ++ [b], ?_, ?_⟩
  · apply appendLe (by change (List.ofFn _ ++ List.ofFn _).length = (List.ofFn _ ++ List.ofFn _).length; simp) _ (fun _ h => h)
    exact appendLe (by simp) (bits hP) (bits hL)
  have line : ∀ p t : Fin 13, p ∈ singerLines3 t ↔ p-t ∈ ({0,1,3,9} : Finset (Fin 13)) := by
    decide +kernel
  have hinc : e.1 ∈ singerLines3 e.2 := (Finset.mem_filter.mp he).2
  have hflag : e.1 ≠ 0 ∨ e.2 ≠ l := by
    by_contra! h
    exact hne (Prod.ext h.1 h.2)
  have hneg := Finset.mem_filter.mp hQ
  have meet (t : Fin 13) : Q ∩ singerLines3 t =
      Q.filter (fun p => p-t ∈ ({0,1,3,9} : Finset (Fin 13))) := by
    ext p
    simp [line]
  have hmiss (t : Fin 13) : t ∈ missLines singerLines3 Q ↔
      ∀ p ∈ Q, p-t ∉ ({0,1,3,9} : Finset (Fin 13)) := by
    change t ∈ Finset.univ.filter (fun t => Disjoint (singerLines3 t) Q) ↔ _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.disjoint_left, line]
    exact ⟨fun h p hp hpt => h hpt hp, fun h p hpt hp => h p hp hpt⟩
  have ilen (P L : Finset (Fin 13)) : (incidenceInput P L ++ [b]).length = 27 := by
    change ((List.ofFn fun p : Fin 13 => decide (p ∈ P)) ++
      List.ofFn (fun t : Fin 13 => decide (t ∈ L)) ++ [b]).length = 27
    simp
  apply hout _ _ (ilen _ _) (ilen _ _)
  · change C.eval ((List.ofFn fun p : Fin 13 => decide (p ∈ ({e.1} : Finset _))) ++
      List.ofFn (fun t : Fin 13 => decide (t ∈ ({e.2} : Finset _))) ++ [b]) = true
    simpa only [Finset.mem_singleton] using hp e.1 e.2 ((line _ _).mp hinc) hflag
  · have bad := hn Q ⟨(Finset.mem_powersetCard.mp hneg.1).2,
        fun t => (meet t) ▸ hneg.2 t⟩
    change C.eval ((List.ofFn fun p : Fin 13 => decide (p ∈ Q)) ++
      List.ofFn (fun t : Fin 13 => decide (t ∈ missLines singerLines3 Q)) ++ [b]) = false
    simpa only [hmiss] using bad
