import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4885_801
    (synthesis :
      let near := fun p l : Fin 13 => (p.val + l.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)
      let vec := fun (s t : Finset (Fin 13)) (i : Fin 26) =>
        Fin.addCases (motive := fun _ => Bool) (fun p => decide (p ∈ s)) (fun l => decide (l ∈ t)) i
      let off := fun s : Finset (Fin 13) => Finset.univ.filter fun l => ∀ p ∈ s, ¬ near p l
      let back := fun t : Finset (Fin 13) => Finset.univ.filter fun p => ∀ l ∈ t, ¬ near p l
      ∃ b ∈ ([1, 13, 15] : List (Fin 26)), ∃ o : Bool,
        let input := (List.ofFn fun (i : Fin 26) (x : Fin 26 → Bool) => x i) ++
          [fun x => if o then x 0 || x b else x 0 && x b]
        ∃ (t : List ((Fin 26 → Bool) → Bool)) (r : (Fin 26 → Bool) → Bool),
          t.length ≤ 62 ∧ r ∈ input ++ t ∧
          (∀ i : Fin t.length, let prev := input ++ t.take i.val
            ∃ u ∈ prev, ∃ v ∈ prev, ∃ k : Bool,
              t.get i = fun x => if k then u x || v x else u x && v x) ∧
          (∀ p l, near p l → r (vec {p} {l}) = true) ∧
          (∀ s, back (off s) = s → r (vec s (off s)) = false))
    (boundary :
    let near := fun p l : Fin 13 => (p.val + l.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)
    let F := fun x : Fin 26 → Bool => ∃ p l : Fin 13,
      near p l ∧ x (p.castAdd 13) = true ∧ x (Fin.natAdd 13 l) = true
    let vec := fun (s t : Finset (Fin 13)) (i : Fin 26) =>
      Fin.addCases (motive := fun _ => Bool) (fun p => decide (p ∈ s)) (fun l => decide (l ∈ t)) i
    let off := fun s : Finset (Fin 13) => Finset.univ.filter fun l => ∀ p ∈ s, ¬ near p l
    let back := fun t : Finset (Fin 13) => Finset.univ.filter fun p => ∀ l ∈ t, ¬ near p l
    ∀ x, (Minimal F x → ∃ p l, near p l ∧ x = vec {p} {l}) ∧
      (Maximal (fun y => ¬ F y) x → ∃ s, back (off s) = s ∧ x = vec s (off s))) :
  have x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => (↑x1 + ↑x2) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]; have x2 : (Fin (26 : ℕ) → Bool) → Prop := fun (x2 : Fin (26 : ℕ) → Bool) => ∃ (x3 : Fin (13 : ℕ)) (x4 : Fin (13 : ℕ)), x1 x3 x4 ∧ x2 (Fin.castAdd (13 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (13 : ℕ) x4) = Bool.true; ∃ x3 ∈ [(1 : Fin (26 : ℕ)), (13 : Fin (26 : ℕ)), (15 : Fin (26 : ℕ))],   ∃ (x4 : Bool),     have x5 : List ((Fin (26 : ℕ) → Bool) → Bool) := (List.ofFn fun (x5 : Fin (26 : ℕ)) (x6 : Fin (26 : ℕ) → Bool) => x6 x5) ++ [fun (x5 : Fin (26 : ℕ) → Bool) => if x4 = Bool.true then x5 (0 : Fin (26 : ℕ)) || x5 x3 else x5 (0 : Fin (26 : ℕ)) && x5 x3];     have x6 : List (Bool → Set (Fin (26 : ℕ) → Bool)) := List.map (fun (x6 : (Fin (26 : ℕ) → Bool) → Bool) (x7 : Bool) => {x8 : Fin (26 : ℕ) → Bool | x6 x8 = x7}) x5;     ∃ (x7 : List (Bool → Set (Fin (26 : ℕ) → Bool))) (x8 : Bool → Set (Fin (26 : ℕ) → Bool)),       x7.length ≤ (62 : ℕ) ∧         x8 ∈ x6 ++ x7 ∧           (∀ (x9 : Fin x7.length),               have x10 : List (Bool → Set (Fin (26 : ℕ) → Bool)) := x6 ++ List.take (↑x9) x7;               ∃ x11 ∈ x10, ∃ x12 ∈ x10, ∃ (x13 : Bool), ∀ (x14 : Bool), x7.get x9 x14 ⊆ if x14 = x13 then x11 x14 ∪ x12 x14 else x11 x14 ∩ x12 x14) ∧             ∀ (x9 : Fin (26 : ℕ) → Bool), (Minimal x2 x9 → x9 ∈ x8 Bool.true) ∧ (Maximal (fun (x10 : Fin (26 : ℕ) → Bool) => ¬x2 x10) x9 → x9 ∈ x8 Bool.false) := by
  let near := fun p l : Fin 13 => (p.val + l.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)
  let vec := fun (s t : Finset (Fin 13)) (i : Fin 26) =>
    Fin.addCases (motive := fun _ => Bool) (fun p => decide (p ∈ s)) (fun l => decide (l ∈ t)) i
  let off := fun s : Finset (Fin 13) => Finset.univ.filter fun l => ∀ p ∈ s, ¬ near p l
  obtain ⟨b, hb, o, t, r, ht, hr, hbuild, hpos, hneg⟩ := synthesis
  let input := (List.ofFn fun (i : Fin 26) (x : Fin 26 → Bool) => x i) ++
    [fun x => if o then x 0 || x b else x 0 && x b]
  let fiber (f : (Fin 26 → Bool) → Bool) (q : Bool) : Set (Fin 26 → Bool) := {x | f x = q}
  refine ⟨b, hb, o, t.map fiber, fiber r, by simpa using ht, ?_, ?_, ?_⟩
  · change fiber r ∈ input.map fiber ++ t.map fiber
    rw [← List.map_append]
    exact List.mem_map.mpr ⟨r, hr, rfl⟩
  · intro i
    let j : Fin t.length := ⟨i.val, by simpa using i.isLt⟩
    obtain ⟨u, hu, v, hv, k, hk⟩ := hbuild j
    have hmem (f : (Fin 26 → Bool) → Bool) (hf : f ∈ input ++ t.take i.val) :
        fiber f ∈ input.map fiber ++ (t.map fiber).take i.val := by
      rw [← List.map_take, ← List.map_append]
      exact List.mem_map.mpr ⟨f, hf, rfl⟩
    refine ⟨fiber u, hmem u hu, fiber v, hmem v hv, k, ?_⟩
    intro q x hx
    have hx' : t.get j x = q := by
      simpa [j, fiber, List.get_eq_getElem] using hx
    rw [hk] at hx'
    cases k <;> cases q <;> cases hu' : u x <;> cases hv' : v x <;>
      simp [fiber, hu', hv'] at hx' ⊢
  · intro x
    constructor
    · intro hx
      obtain ⟨p, l, hi, he⟩ := (boundary x).1 hx
      change x = vec {p} {l} at he
      change r x = true
      rw [he]
      exact hpos p l hi
    · intro hx
      obtain ⟨s, hclosed, he⟩ := (boundary x).2 hx
      change x = vec s (off s) at he
      change r x = false
      rw [he]
      exact hneg s hclosed
