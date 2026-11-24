import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Translate the point and line labels in opposite directions, multiply
-- both labels by 3, and interchange points and lines. The resulting action
-- has two positive row orbits and fourteen negative row orbits.
theorem PEqualNP.Outside.R_meta_2056_637
    (search :
      let tr := fun (a b : Fin 13) (d : Bool) (i : Fin 26) =>
        let j := a * Fin.ofNat 13 i.val + (if i.val < 13 then b else -b)
        Fin.ofNat 26 (j.val + if decide (i.val < 13) == d then 13 else 0)
      ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 63 ∧
        (∀ a ∈ ([1, 3, 9] : List (Fin 13)), ∀ (b : Fin 13) (d : Bool) (x : Fin 26 → Bool),
          C.eval (List.ofFn (x ∘ tr a b d)) = C.eval (List.ofFn x)) ∧
        (∀ r ∈ ([8193, 8194] : List ℕ), C.eval (List.ofFn (fun i : Fin 26 => r.testBit i.val)) = true) ∧
        (∀ r ∈ ([8191, 15860, 27888, 42356, 58480, 90288, 106804, 157904, 172372, 205204, 237844, 340132, 682064, 1324064] : List ℕ), C.eval (List.ofFn (fun i : Fin 26 => r.testBit i.val)) = false))
    (positiveOrbit :
      let tr := fun (a b : Fin 13) (d : Bool) (i : Fin 26) =>
        let j := a * Fin.ofNat 13 i.val + (if i.val < 13 then b else -b)
        Fin.ofNat 26 (j.val + if decide (i.val < 13) == d then 13 else 0)
      let vec := fun (s t : Finset (Fin 13)) (i : Fin 26) =>
        if i.val < 13 then decide (Fin.ofNat 13 i.val ∈ s) else decide (Fin.ofNat 13 i.val ∈ t)
      ∀ (p l : Fin 13), (p.val + l.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ) →
        ∃ a ∈ ([1, 3, 9] : List (Fin 13)), ∃ (b : Fin 13) (d : Bool), ∃ r ∈ ([8193, 8194] : List ℕ),
          vec {p} {l} = (fun i : Fin 26 => r.testBit i.val) ∘ tr a b d)
    (negativeOrbit :
      let tr := fun (a b : Fin 13) (d : Bool) (i : Fin 26) =>
        let j := a * Fin.ofNat 13 i.val + (if i.val < 13 then b else -b)
        Fin.ofNat 26 (j.val + if decide (i.val < 13) == d then 13 else 0)
      let vec := fun (s t : Finset (Fin 13)) (i : Fin 26) =>
        if i.val < 13 then decide (Fin.ofNat 13 i.val ∈ s) else decide (Fin.ofNat 13 i.val ∈ t)
      let off := fun (s : Finset (Fin 13)) =>
        Finset.univ.filter fun l : Fin 13 => ∀ p ∈ s, (p.val + l.val) % 13 ∉ ([0, 1, 3, 9] : List ℕ)
      ∀ s : Finset (Fin 13), s.card ≤ 3 → ∀ side : Bool,
        ∃ a ∈ ([1, 3, 9] : List (Fin 13)), ∃ (b : Fin 13) (d : Bool), ∃ r ∈ ([8191, 15860, 27888, 42356, 58480, 90288, 106804, 157904, 172372, 205204, 237844, 340132, 682064, 1324064] : List ℕ),
          (if side then vec (off s) s else vec s (off s)) =
            (fun i : Fin 26 => r.testBit i.val) ∘ tr a b d) :
  ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x1 ∧     x1.size ≤ (63 : ℕ) ∧       let x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x2 x3 : Fin (13 : ℕ)) => (↑x2 + ↑x3) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)];       have x3 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Fin (26 : ℕ) → Bool := fun (x3 x4 : Finset (Fin (13 : ℕ))) (x5 : Fin (26 : ℕ)) => if ↑x5 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x5 ∈ x3) else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x5 ∈ x4);       have x4 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x4 : Finset (Fin (13 : ℕ))) => {x5 : Fin (13 : ℕ) | ∀ x6 ∈ x4, ¬x2 x6 x5};       have x5 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Bool := fun (x5 x6 : Finset (Fin (13 : ℕ))) => x1.eval (List.ofFn (x3 x5 x6));       (∀ (x6 x7 : Fin (13 : ℕ)), x2 x6 x7 → x5 {x6} {x7} = Bool.true) ∧ ∀ (x6 : Finset (Fin (13 : ℕ))), x6.card ≤ (3 : ℕ) → x5 x6 (x4 x6) = Bool.false ∧ x5 (x4 x6) x6 = Bool.false := by
  let tr := fun (a b : Fin 13) (d : Bool) (i : Fin 26) =>
        let j := a * Fin.ofNat 13 i.val + (if i.val < 13 then b else -b)
        Fin.ofNat 26 (j.val + if decide (i.val < 13) == d then 13 else 0)
  let vec := fun (s t : Finset (Fin 13)) (i : Fin 26) =>
        if i.val < 13 then decide (Fin.ofNat 13 i.val ∈ s) else decide (Fin.ofNat 13 i.val ∈ t)
  let off := fun (s : Finset (Fin 13)) =>
        Finset.univ.filter fun l : Fin 13 => ∀ p ∈ s, (p.val + l.val) % 13 ∉ ([0, 1, 3, 9] : List ℕ)
  let near (p l : Fin 13) := (p.val + l.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)
  obtain ⟨C, hMono, hSize, stable, yes, no⟩ := search
  refine ⟨C, hMono, hSize, ?_⟩
  let value (x : Fin 26 → Bool) := C.eval (List.ofFn x)
  have valueOrbit (x : Fin 26 → Bool) (a : Fin 13) (ha : a ∈ ([1, 3, 9] : List (Fin 13)))
      (b : Fin 13) (d : Bool) (r : Nat) (eq : x = (fun i : Fin 26 => r.testBit i.val) ∘ tr a b d) :
      value x = value (fun i : Fin 26 => r.testBit i.val) := by
    rw [eq]
    exact stable a ha b d _
  change (∀ p l, near p l → value (vec {p} {l}) = true) ∧
    ∀ s : Finset (Fin 13), s.card ≤ 3 → value (vec s (off s)) = false ∧ value (vec (off s) s) = false
  constructor
  · intro p l edge
    obtain ⟨a,ha,b,d,r,hr,eq⟩ := positiveOrbit p l edge
    exact (valueOrbit _ a ha b d r eq).trans (yes r hr)
  · intro s small
    have allSides (side : Bool) : value (if side then vec (off s) s else vec s (off s)) = false := by
      obtain ⟨a,ha,b,d,r,hr,eq⟩ := negativeOrbit s small side
      exact (valueOrbit _ a ha b d r eq).trans (no r hr)
    exact ⟨allSides false, allSides true⟩
