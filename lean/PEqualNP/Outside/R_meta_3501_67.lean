import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 2000000
open scoped Classical in
theorem PEqualNP.Outside.R_meta_3501_67
    (minimal : ∀ (N q : Nat) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (regular : ∀ l, Fintype.card {p : Fin N // I p l} = q+1)
    (uniqueLine : ∀ p r, p ≠ r → ∃! l, I p l ∧ I r l)
    (T : Finset (Fin N)) (small : T.card ≤ q)
    (A C : Finset (Fin (N+N))) (sub : A ⊆ C)
    (cover : ∀ p l, I p l → Fin.castAdd N p ∈ A ∨ Fin.natAdd N l ∈ A)
    (pts : ∀ p, Fin.castAdd N p ∈ C ↔ ∃ j ∈ T, I p j)
    (lns : ∀ l, Fin.natAdd N l ∈ C ↔ l ∉ T), A = C)
    (leftBound : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3],   (250 : ℕ) ≤ x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) →         (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) →           let x9 : Type := Finset (Fin (x2 + x2));           ∀ (x10 x11 : ℕ) (x12 : ℕ → x9 → Prop),             x11 < x2 + x2 + x10 →               (∀ (x14 : Fin (x2 + x2)) (x15 : x9), x12 (↑x14) x15 ↔ x14 ∈ x15) →                 (∀ x15 < x10, ∃ (x17 : ℕ) (x18 : ℕ), x17 < x18 ∧ x18 < x2 + x2 + x15 ∧ ((∀ (x19 : x9), x12 (x2 + x2 + x15) x19 ↔ x12 x17 x19 ∨ x12 x18 x19) ∨ ∀ (x19 : x9), x12 (x2 + x2 + x15) x19 ↔ x12 x17 x19 ∧ x12 x18 x19)) →                   (∀ (x16 : x9), x12 x11 x16 → ∀ (x18 x19 : Fin x2), x3 x18 x19 → Fin.castAdd x2 x18 ∈ x16 ∨ Fin.natAdd x2 x19 ∈ x16) →                     (∀ (x17 : Finset (Fin x2)), x17.card ≤ x1 → ∃ (x19 : x9), (∀ (x20 : Fin x2), Fin.castAdd x2 x20 ∈ x19 ↔ ∃ x21 ∈ x17, x3 x20 x21) ∧ (∀ (x20 : Fin x2), Fin.natAdd x2 x20 ∈ x19 ↔ x20 ∉ x17) ∧ ∀ x20 ⊆ x19, x12 x11 x20 ↔ x20 = x19) →                       (∃ x18 < x10,                           ∃ (x19 : ℕ) (x20 : ℕ),                             x19 < x20 ∧                               x20 < x2 + x2 + x18 ∧                                 (∀ (x21 : x9), x12 (x2 + x2 + x18) x21 ↔ x12 x19 x21 ∨ x12 x20 x21) ∧                                   ∀ x21 ∈ [x19, x20],                                     ∃ (x23 : Fin x2 → Bool),                                       have x24 : Bool → List Bool := fun (x24 : Bool) => List.ofFn x23 ++ List.replicate x2 x24;                                       have x25 : Bool → Finset (Fin (x2 + x2)) := fun (x25 : Bool) => {x26 : Fin (x2 + x2) | (x24 x25).getD (↑x26) Bool.false = Bool.false};                                       ¬(x12 x21 (x25 Bool.false) ↔ x12 x21 (x25 Bool.true))) →                         x2 * x1 ≤ (100 : ℕ) * x10)
    (rightBound : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3],   (250 : ℕ) ≤ x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) →         (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) →           let x9 : Type := Finset (Fin (x2 + x2));           ∀ (x10 x11 : ℕ) (x12 : ℕ → x9 → Prop),             x11 < x2 + x2 + x10 →               (∀ (x14 : Fin (x2 + x2)) (x15 : x9), x12 (↑x14) x15 ↔ x14 ∈ x15) →                 (∀ x15 < x10, ∃ (x17 : ℕ) (x18 : ℕ), x17 < x18 ∧ x18 < x2 + x2 + x15 ∧ ((∀ (x19 : x9), x12 (x2 + x2 + x15) x19 ↔ x12 x17 x19 ∨ x12 x18 x19) ∨ ∀ (x19 : x9), x12 (x2 + x2 + x15) x19 ↔ x12 x17 x19 ∧ x12 x18 x19)) →                   (∀ (x16 : x9), x12 x11 x16 → ∀ (x18 x19 : Fin x2), x3 x18 x19 → Fin.castAdd x2 x18 ∈ x16 ∨ Fin.natAdd x2 x19 ∈ x16) →                     (∀ (x17 : Finset (Fin x2)), x17.card ≤ x1 → ∃ (x19 : x9), (∀ (x20 : Fin x2), Fin.castAdd x2 x20 ∈ x19 ↔ ∃ x21 ∈ x17, x3 x20 x21) ∧ (∀ (x20 : Fin x2), Fin.natAdd x2 x20 ∈ x19 ↔ x20 ∉ x17) ∧ ∀ x20 ⊆ x19, x12 x11 x20 ↔ x20 = x19) →                       (∃ x18 < x10,                           ∃ (x19 : ℕ) (x20 : ℕ),                             x19 < x20 ∧                               x20 < x2 + x2 + x18 ∧                                 (∀ (x21 : x9), x12 (x2 + x2 + x18) x21 ↔ x12 x19 x21 ∨ x12 x20 x21) ∧                                   ∀ x21 ∈ [x19, x20],                                     ∃ (x23 : Fin x2 → Bool),                                       have x24 : Bool → List Bool := fun (x24 : Bool) => List.replicate x2 x24 ++ List.ofFn x23;                                       have x25 : Bool → Finset (Fin (x2 + x2)) := fun (x25 : Bool) => {x26 : Fin (x2 + x2) | (x24 x25).getD (↑x26) Bool.false = Bool.false};                                       ¬(x12 x21 (x25 Bool.false) ↔ x12 x21 (x25 Bool.true))) →                         x2 * x1 ≤ (100 : ℕ) * x10) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3],   (250 : ℕ) ≤ x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) →         (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) →           ∀ (x9 x10 : ℕ) (x11 : ℕ → Finset (Finset (Fin (x2 + x2)))),             x10 < x2 + x2 + x9 →               (∀ (x13 : Fin (x2 + x2)), x11 ↑x13 = {{x13}}) →                 (∀ x14 < x9, ∃ (x16 : ℕ) (x17 : ℕ), x16 < x17 ∧ x17 < x2 + x2 + x14 ∧ (x11 (x2 + x2 + x14) = x11 x16 ∪ x11 x17 ∨ x11 (x2 + x2 + x14) = (x11 x16).biUnion fun (x18 : Finset (Fin (x2 + x2))) => Finset.image (fun (x19 : Finset (Fin (x2 + x2))) => x18 ∪ x19) (x11 x17))) →                   (∀ x15 ∈ x11 x10, ∀ (x17 x18 : Fin x2), x3 x17 x18 → Fin.castAdd x2 x17 ∈ x15 ∨ Fin.natAdd x2 x18 ∈ x15) →                     (∀ (x16 : Finset (Fin x2)), x16.card ≤ x1 → ∃ x18 ∈ x11 x10, (∀ (x19 : Fin x2), Fin.castAdd x2 x19 ∈ x18 ↔ ∃ x20 ∈ x16, x3 x19 x20) ∧ ∀ (x19 : Fin x2), Fin.natAdd x2 x19 ∈ x18 ↔ x19 ∉ x16) →                       (∃ x17 < x9,                           ∃ (x18 : ℕ) (x19 : ℕ),                             x18 < x19 ∧                               x19 < x2 + x2 + x17 ∧                                 x11 (x2 + x2 + x17) = x11 x18 ∪ x11 x19 ∧                                   ∃ (x20 : Bool),                                     ∀ x21 ∈ [x18, x19],                                       ∃ (x23 : Fin x2 → Bool),                                         have x24 : Bool → List Bool := fun (x24 : Bool) => if x20 = Bool.true then List.ofFn x23 ++ List.replicate x2 x24 else List.replicate x2 x24 ++ List.ofFn x23;                                         have x25 : Bool → Prop := fun (x25 : Bool) => ∀ x26 ∈ x11 x21, ∃ x28 ∈ x26, (x24 x25).getD (↑x28) Bool.false = Bool.true;                                         ¬(x25 Bool.false ↔ x25 Bool.true)) →                         x2 * x1 ≤ (100 : ℕ) * x9 := by
  classical
  have booleanBound : ∀ (q N : Nat) (I : Fin N → Fin N → Prop) [DecidableRel I],
      250 ≤ q → N = q^2+q+1 →
      (∀ l, Fintype.card {p : Fin N // I p l} = q+1) →
      (∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) →
      let W := Finset (Fin (N+N))
      ∀ (s o : Nat) (g : Nat → W → Prop),
      o < N+N+s →
      (∀ (i : Fin (N+N)) Z, g i Z ↔ i ∈ Z) →
      (∀ t < s, ∃ a b : Nat, a < b ∧ b < N+N+t ∧
        ((∀ Z, g (N+N+t) Z ↔ g a Z ∨ g b Z) ∨ (∀ Z, g (N+N+t) Z ↔ g a Z ∧ g b Z))) →
      (∀ Z, g o Z → ∀ p l, I p l → Fin.castAdd N p ∈ Z ∨ Fin.natAdd N l ∈ Z) →
      (∀ T : Finset (Fin N), T.card ≤ q → ∃ C : W,
        (∀ p, Fin.castAdd N p ∈ C ↔ ∃ l ∈ T, I p l) ∧
        (∀ l, Fin.natAdd N l ∈ C ↔ l ∉ T) ∧
        (∀ Z, Z ⊆ C → (g o Z ↔ Z = C))) →
      (∃ t < s, ∃ a b : Nat, a < b ∧ b < N+N+t ∧
        (∀ Z, g (N+N+t) Z ↔ g a Z ∨ g b Z) ∧
        ∃ side : Bool, ∀ k ∈ [a,b], ∃ x : Fin N → Bool,
          let inp := fun (c : Bool) => if side then List.ofFn x ++ List.replicate N c
            else List.replicate N c ++ List.ofFn x
          let mask := fun c => Finset.univ.filter (fun i : Fin (N+N) => (inp c).getD i false = false)
          ¬(g k (mask false) ↔ g k (mask true))) →
      N*q ≤ 100*s := by
    intro q N I dec hq order reg pair W s o g
    dsimp only
    intro addr raw gates cover min mix
    obtain ⟨t,ht,a,b,ab,bt,gate,side,changes⟩ := mix
    cases side
    · apply rightBound q N I hq order reg pair s o g addr raw gates cover min
      exact ⟨t,ht,a,b,ab,bt,gate,changes⟩
    · apply leftBound q N I hq order reg pair s o g addr raw gates cover min
      exact ⟨t,ht,a,b,ab,bt,gate,changes⟩
  intro q N I dec hq order reg pair s o F addr raw gates cover wit mixed
  let g (k : Nat) (Z : Finset (Fin (N+N))) : Prop := ∃ A ∈ F k, A ⊆ Z
  apply booleanBound q N I hq order reg pair s o g addr
  · intro i Z
    simp [g,raw]
  · intro t ht
    obtain ⟨a,b,ab,bt,op⟩ := gates t ht
    refine ⟨a,b,ab,bt,?_⟩
    rcases op with plus | times
    · left
      intro Z
      simp only [g,plus,Finset.mem_union]
      constructor
      · rintro ⟨A,af|ag,az⟩
        · exact Or.inl ⟨A,af,az⟩
        · exact Or.inr ⟨A,ag,az⟩
      · rintro (⟨A,af,az⟩|⟨A,ag,az⟩)
        · exact ⟨A,Or.inl af,az⟩
        · exact ⟨A,Or.inr ag,az⟩
    · right
      intro Z
      simp only [g,times,Finset.mem_biUnion,Finset.mem_image]
      constructor
      · rintro ⟨A,⟨U,uf,V,vg,rfl⟩,az⟩
        exact ⟨⟨U,uf,(Finset.union_subset_iff.mp az).1⟩,
          ⟨V,vg,(Finset.union_subset_iff.mp az).2⟩⟩
      · rintro ⟨⟨U,uf,uz⟩,⟨V,vg,vz⟩⟩
        exact ⟨U ∪ V,⟨U,uf,V,vg,rfl⟩,Finset.union_subset uz vz⟩
  · intro Z hz p l hp
    obtain ⟨A,af,az⟩ := hz
    exact (cover A af p l hp).imp (@az _) (@az _)
  · intro T small
    obtain ⟨C,cf,pts,lns⟩ := wit T small
    refine ⟨C,pts,lns,?_⟩
    intro Z zc
    constructor
    · rintro ⟨A,af,az⟩
      have h := minimal N q I reg pair T small A C (az.trans zc) (cover A af) pts lns
      exact Finset.Subset.antisymm zc (h ▸ az)
    · rintro rfl
      exact ⟨_,cf,Finset.Subset.refl _⟩

  · obtain ⟨t,ht,a,b,ab,bt,union,side,changes⟩ := mixed
    refine ⟨t,ht,a,b,ab,bt,?_,side,?_⟩
    · intro Z
      simp only [g,union,Finset.mem_union]
      constructor
      · rintro ⟨A,af|ag,az⟩
        · exact Or.inl ⟨A,af,az⟩
        · exact Or.inr ⟨A,ag,az⟩
      · rintro (⟨A,af,az⟩|⟨A,ag,az⟩)
        · exact ⟨A,Or.inl af,az⟩
        · exact ⟨A,Or.inr ag,az⟩
    · intro k hk
      obtain ⟨x,hx⟩ := changes k hk
      refine ⟨x,?_⟩
      let inp (c : Bool) := if side then List.ofFn x ++ List.replicate N c
        else List.replicate N c ++ List.ofFn x
      let mask (c : Bool) := Finset.univ.filter (fun i : Fin (N+N) => (inp c).getD i false = false)
      have neg (c : Bool) : (∀ A ∈ F k, ∃ i ∈ A, (inp c).getD i false = true) ↔ ¬g k (mask c) := by
        constructor
        · intro hit occurs
          obtain ⟨A,af,az⟩ := occurs
          obtain ⟨i,ia,yes⟩ := hit A af
          have no := (Finset.mem_filter.mp (az ia)).2
          exact Bool.noConfusion (yes.symm.trans no)
        · intro h A af
          by_contra! miss
          apply h
          refine ⟨A,af,?_⟩
          intro i ia
          apply Finset.mem_filter.mpr
          exact ⟨Finset.mem_univ _, Bool.eq_false_iff.mpr (miss i ia)⟩
      change ¬(g k (mask false) ↔ g k (mask true))
      intro equal
      apply hx
      exact (neg false).trans (equal.not.trans (neg true).symm)
