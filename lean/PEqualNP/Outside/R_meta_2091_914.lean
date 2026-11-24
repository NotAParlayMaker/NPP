import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The earlier of the two output wires need not be read by any gate.
-- The later output can be the last gate of the suffix.
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.R_meta_2091_914
    (normalize : ∀ (n : ℕ) (C : Circuit), Monotone2 C → ∀ (a b : ℕ),
      n ≤ a → a < b → b < n + C.size →
      ∃ D : Circuit, Monotone2 D ∧ D.size ≤ C.size ∧ b + 1 = n + D.size ∧
        (∀ g ∈ D.gates, a ∉ g.inputs) ∧
        ∀ x : Fin n → Bool,
          ((D.wires (List.ofFn x)).getD a false || (D.wires (List.ofFn x)).getD b false) =
          ((C.wires (List.ofFn x)).getD a false || (C.wires (List.ofFn x)).getD b false))
    (bound :
      let S : Finset (Fin 13) := {0, 1, 3, 9}
      let E := fun (p l : Fin 13) => ∃ d ∈ S, p = l + d
      let A := fun (P : Finset (Fin 13)) (l : Fin 13) => ∀ p ∈ P, ¬ E p l
      let T := fun (p l : Fin 13) (i : Fin 26) =>
        decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l)
      let F := fun (P : Finset (Fin 13)) (i : Fin 26) =>
        decide ((∃ p ∈ P, i = Fin.castAdd 13 p) ∨ ∃ l, i = Fin.natAdd 13 l ∧ A P l)
      let W := fun (D : Circuit) (a b : ℕ) (x : Fin 26 → Bool) =>
        let ws := D.wires (List.ofFn x)
        ws.getD a false || ws.getD b false
      ∀ (D : Circuit), Monotone2 D → D.size ≤ 62 → ∀ (a b : ℕ),
        26 ≤ a → a < b → b + 1 = 26 + D.size → (∀ g ∈ D.gates, a ∉ g.inputs) →
        (∀ p l, E p l → W D a b (T p l) = true) →
        (∀ P, (∀ p ∉ P, ∃ l, A P l ∧ E p l) →
          ((∃ l, ∀ p ∈ P, E p l) ∨ ∃ p, ∀ l, A P l → E p l) →
          W D a b (F P) = false) → False) :
    have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x2 x3 : Fin (13 : ℕ)) => ∃ x4 ∈ x1, x2 = x3 + x4; have x3 : Finset (Fin (13 : ℕ)) → Fin (13 : ℕ) → Prop := fun (x3 : Finset (Fin (13 : ℕ))) (x4 : Fin (13 : ℕ)) => ∀ x5 ∈ x3, ¬x2 x5 x4; have x4 : Fin (13 : ℕ) → Fin (13 : ℕ) → Fin (26 : ℕ) → Bool := fun (x4 x5 : Fin (13 : ℕ)) (x6 : Fin (26 : ℕ)) => Decidable.decide (x6 = Fin.castAdd (13 : ℕ) x4 ∨ x6 = Fin.natAdd (13 : ℕ) x5); have x5 : Finset (Fin (13 : ℕ)) → Fin ((13 : ℕ) + (13 : ℕ)) → Bool := fun (x5 : Finset (Fin (13 : ℕ))) (x6 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide ((∃ x7 ∈ x5, x6 = Fin.castAdd (13 : ℕ) x7) ∨ ∃ (x7 : Fin (13 : ℕ)), x6 = Fin.natAdd (13 : ℕ) x7 ∧ ∀ x8 ∈ x5, ¬∃ x10 ∈ x1, x8 = x7 + x10); have x6 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → (Fin (26 : ℕ) → Bool) → Bool := fun (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 : ℕ) (x8 : Fin (26 : ℕ) → Bool) => (x6.wires (List.ofFn x8)).getD x7 Bool.false; ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 → x7.size ≤ (62 : ℕ) → ∀ (x10 x11 : Fin ((26 : ℕ) + x7.size)), x10 ≠ x11 → (∀ (x13 x14 : Fin (13 : ℕ)), x2 x13 x14 → PEqualNP.CircuitLowerBounds.GateOp.or.eval [x6 x7 (↑x10) (x4 x13 x14), x6 x7 (↑x11) (x4 x13 x14)] = Bool.true) → (∀ (x14 : Finset (Fin (13 : ℕ))), (∀ x15 ∉ x14, ∃ (x17 : Fin (13 : ℕ)), x3 x14 x17 ∧ x2 x15 x17) → ((∃ (x16 : Fin (13 : ℕ)), ∀ x17 ∈ x14, x2 x17 x16) ∨ ∃ (x16 : Fin (13 : ℕ)), ∀ (x17 : Fin (13 : ℕ)), x3 x14 x17 → x2 x16 x17) → PEqualNP.CircuitLowerBounds.GateOp.or.eval [x6 x7 (↑x10) (x5 x14), x6 x7 (↑x11) (x5 x14)] = Bool.false) → False := by
  dsimp only
  intro C mono size a b distinct pos neg
  let S : Finset (Fin 13) := {0, 1, 3, 9}
  let E := fun (p l : Fin 13) => ∃ d ∈ S, p = l + d
  let A := fun (P : Finset (Fin 13)) (l : Fin 13) => ∀ p ∈ P, ¬ E p l
  let T := fun (p l : Fin 13) (i : Fin 26) =>
    decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l)
  let F := fun (P : Finset (Fin 13)) (i : Fin 26) =>
    decide ((∃ p ∈ P, i = Fin.castAdd 13 p) ∨ ∃ l, i = Fin.natAdd 13 l ∧ A P l)
  let W := fun (D : Circuit) (i : ℕ) (x : Fin 26 → Bool) =>
    (D.wires (List.ofFn x)).getD i false
  let maximal := fun (P : Finset (Fin 13)) => ∀ p ∉ P, ∃ l, A P l ∧ E p l
  let degenerate := fun (P : Finset (Fin 13)) =>
    (∃ l, ∀ p ∈ P, E p l) ∨ ∃ p, ∀ l, A P l → E p l
  have orPair (u v : Bool) : GateOp.or.eval [u, v] = (u || v) := by
    change (u || (v || false)) = (u || v)
    rw [Bool.or_false]
  simp only [orPair] at pos neg
  change ∀ p l, E p l → (W C a.val (T p l) || W C b.val (T p l)) = true at pos
  change ∀ P, maximal P → degenerate P →
    (W C a.val (F P) || W C b.val (F P)) = false at neg
  have diagonal (p : Fin 13) : E p p := ⟨0, by decide, by simp⟩
  have noShift (d : Fin 13) (hd : d ∈ S) (nonzero : d ≠ 0) : d + 1 ∉ S := by
    revert hd nonzero
    fin_cases d <;> decide +kernel
  have separatePoints (p v : Fin 13) (distinct : v ≠ p) : ∃ l, ¬ E p l ∧ E v l := by
    by_cases h : E p v
    · obtain ⟨d, hd, eq⟩ := h
      have nz : d ≠ 0 := by
        intro z
        exact distinct (by simpa [z] using eq.symm)
      refine ⟨v - 1, ?_, 1, by decide, (sub_add_cancel v 1).symm⟩
      rintro ⟨c, hc, he⟩
      have shift : c = d + 1 := by
        apply add_left_cancel (a := v - 1)
        calc
          v - 1 + c = p := he.symm
          _ = v + d := eq
          _ = v - 1 + (d + 1) := by abel
      exact noShift d hd nz (shift ▸ hc)
    · exact ⟨v, h, diagonal v⟩
  have separateLines (l t : Fin 13) (distinct : t ≠ l) : ∃ p, ¬ E p l ∧ E p t := by
    by_cases h : E t l
    · obtain ⟨d, hd, eq⟩ := h
      have nz : d ≠ 0 := by
        intro z
        exact distinct (by simpa [z] using eq)
      refine ⟨t + 1, ?_, 1, by decide, rfl⟩
      rintro ⟨c, hc, he⟩
      have shift : c = d + 1 := by
        apply add_left_cancel (a := l)
        rw [← he, eq, add_assoc]
      exact noShift d hd nz (shift ▸ hc)
    · exact ⟨t, h, diagonal t⟩
  have pointFalse (p : Fin 13) : maximal {p} ∧ degenerate {p} ∧
      F {p} (Fin.castAdd 13 p) = true := by
    refine ⟨?_, Or.inl ⟨p, ?_⟩, ?_⟩
    · intro v hv
      obtain ⟨l, hmiss, hhit⟩ := separatePoints p v (by simpa using hv)
      refine ⟨l, ?_, hhit⟩
      intro q hq
      obtain rfl := Finset.mem_singleton.mp hq
      exact hmiss
    · intro q hq
      have eq : q = p := Finset.mem_singleton.mp hq
      rw [eq]
      exact diagonal p
    · exact decide_eq_true (Or.inl ⟨p, Finset.mem_singleton_self p, rfl⟩)
  let offLine (l : Fin 13) : Finset (Fin 13) := Finset.univ.filter fun p => ¬ E p l
  have lineFalse (l : Fin 13) : maximal (offLine l) ∧ degenerate (offLine l) ∧
      F (offLine l) (Fin.natAdd 13 l) = true := by
    have iffOff (p : Fin 13) : p ∈ offLine l ↔ ¬ E p l := by simp [offLine]
    have misses : A (offLine l) l := fun p hp => (iffOff p).mp hp
    refine ⟨?_, Or.inr ⟨l, ?_⟩, ?_⟩
    · intro p hp
      refine ⟨l, misses, ?_⟩
      by_contra hn
      exact hp ((iffOff p).mpr hn)
    · intro t ht
      by_cases h : t = l
      · subst t
        exact diagonal l
      · obtain ⟨p, hp, hpt⟩ := separateLines l t h
        exact (ht p ((iffOff p).mpr hp) hpt).elim
    · exact decide_eq_true (Or.inr ⟨l, rfl, misses⟩)
  have rawFalse (i : Fin 26) : ∃ P, maximal P ∧ degenerate P ∧ F P i = true := by
    refine Fin.addCases (m := 13) (n := 13) ?_ ?_ i
    · intro p
      exact ⟨{p}, pointFalse p⟩
    · intro l
      exact ⟨offLine l, lineFalse l⟩
  let step (w : List Bool) (g : Gate) :=
    w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]
  have oldWire (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl step w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih (step w g) (by simp [step]; omega)]
      exact List.getD_append _ _ _ _ hi
  have rawWire (i : Fin 26) (x : Fin 26 → Bool) : W C i.val x = x i := by
    change (C.gates.foldl step (List.ofFn x)).getD i.val false = x i
    rw [oldWire _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
  have gateWire (i : ℕ) (low : ∀ P, maximal P → degenerate P → W C i (F P) = false) :
      26 ≤ i := by
    by_contra! small
    obtain ⟨P, hmax, hdeg, hv⟩ := rawFalse ⟨i, small⟩
    have recorded := low P hmax hdeg
    have read : W C i (F P) = F P ⟨i, small⟩ := rawWire ⟨i, small⟩ _
    rw [read, hv] at recorded
    contradiction
  have ha : 26 ≤ a.val := gateWire a.val fun P hmax hdeg =>
    (Bool.or_eq_false_iff.mp (neg P hmax hdeg)).1
  have hb : 26 ≤ b.val := gateWire b.val fun P hmax hdeg =>
    (Bool.or_eq_false_iff.mp (neg P hmax hdeg)).2
  have ordered (i j : Fin (26 + C.size)) (hi : 26 ≤ i.val) (hij : i.val < j.val)
      (hp : ∀ p l, E p l → (W C i.val (T p l) || W C j.val (T p l)) = true)
      (hn : ∀ P, maximal P → degenerate P → (W C i.val (F P) || W C j.val (F P)) = false) :
      False := by
    obtain ⟨D, hm, hs, hlast, hread, hvalues⟩ := normalize 26 C mono i.val j.val hi hij j.isLt
    have dp : ∀ p l, E p l → (W D i.val (T p l) || W D j.val (T p l)) = true := by
      intro p l edge
      exact (hvalues (T p l)).trans (hp p l edge)
    have dn : ∀ P, maximal P → degenerate P → (W D i.val (F P) || W D j.val (F P)) = false := by
      intro P hmax hdeg
      exact (hvalues (F P)).trans (hn P hmax hdeg)
    change ∀ D : Circuit, Monotone2 D → D.size ≤ 62 → ∀ (a b : ℕ),
      26 ≤ a → a < b → b + 1 = 26 + D.size → (∀ g ∈ D.gates, a ∉ g.inputs) →
      (∀ p l, E p l → (W D a (T p l) || W D b (T p l)) = true) →
      (∀ P, maximal P → degenerate P → (W D a (F P) || W D b (F P)) = false) → False at bound
    exact bound D hm (hs.trans size) i.val j.val hi hij hlast hread dp dn
  rcases lt_or_gt_of_ne distinct with hab | hba
  · exact ordered a b ha hab pos neg
  · exact ordered b a hb hba
      (fun p l edge => by rw [Bool.or_comm]; exact pos p l edge)
      (fun P hmax hdeg => by rw [Bool.or_comm]; exact neg P hmax hdeg)
