import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3188_67
    (normal : let B : List (BitVec 24) := [202052,276515,549652,1097833,101010,10616859,4456668,2624736,13635328,751444];
      let G : BitVec 24 := 16773120;
      let valid := fun xs : List (BitVec 24) => ∀ i : Fin xs.length,
        let w := B ++ xs.take i.val; let z := xs.get i;
        z∉w ∧ z≠0 ∧ z≠ -1 ∧ ∃ u∈w, ∃ v∈w, z=u&&&v ∨ z=u|||v;
      ∀ xs : List (BitVec 24), G∈B++xs → valid xs → xs.length≤14 →
        ∃ hist : List (BitVec 24), hist.length=13 ∧ valid hist ∧
        ∃ u∈hist.take 12, ∃ v∈hist.drop 12, u&&&v≠u ∧ u&&&v≠v ∧ (G=u&&&v ∨ G=u|||v))
    (andCut : let B : List (BitVec 24) := [202052,276515,549652,1097833,101010,10616859,4456668,2624736,13635328,751444];
      let G : BitVec 24 := 16773120;
      let valid := fun xs : List (BitVec 24) => ∀ i : Fin xs.length,
        let w := B ++ xs.take i.val; let z := xs.get i;
        z∉w ∧ z≠0 ∧ z≠ -1 ∧ ∃ u∈w, ∃ v∈w, z=u&&&v ∨ z=u|||v;
      ∀ hist : List (BitVec 24), hist.length=13 → valid hist →
        ∀ u∈hist.take 12, ∀ v∈hist.drop 12, u&&&v≠u → u&&&v≠v → G&&&u=G → G&&&v=G → G≠u&&&v)
    (orCut : let B : List (BitVec 24) := [202052,276515,549652,1097833,101010,10616859,4456668,2624736,13635328,751444];
      let G : BitVec 24 := 16773120;
      let valid := fun xs : List (BitVec 24) => ∀ i : Fin xs.length,
        let w := B ++ xs.take i.val; let z := xs.get i;
        z∉w ∧ z≠0 ∧ z≠ -1 ∧ ∃ u∈w, ∃ v∈w, z=u&&&v ∨ z=u|||v;
      ∀ hist : List (BitVec 24), hist.length=13 → valid hist →
        ∀ u∈hist.take 12, ∀ v∈hist.drop 12, u&&&v≠u → u&&&v≠v → G|||u=G → G|||v=G → G≠u|||v) : have x1 : Fin (9 : ℕ) → BitVec (24 : ℕ) := fun (x1 : Fin (9 : ℕ)) =>   have x2 : ℕ × ℕ := [((49 : ℕ), (1348 : ℕ)), ((67 : ℕ), (2083 : ℕ)), ((134 : ℕ), (788 : ℕ)), ((268 : ℕ), (105 : ℕ)), ((24 : ℕ), (2706 : ℕ)), ((2592 : ℕ), (27 : ℕ)), ((1088 : ℕ), (220 : ℕ)), ((640 : ℕ), (3296 : ℕ)), ((3328 : ℕ), (3840 : ℕ))].getD ↑x1 ((0 : ℕ), (0 : ℕ));   BitVec.ofNat (24 : ℕ) ((4096 : ℕ) * x2.1 + x2.2); have x2 : List (BitVec (24 : ℕ)) := List.ofFn x1 ++ [x1 (0 : Fin (9 : ℕ)) ||| x1 (2 : Fin (9 : ℕ))]; ∀ (x3 : List (BitVec (24 : ℕ))),   BitVec.ofNat (24 : ℕ) ((4095 : ℕ) * (4096 : ℕ)) ∈ x2 ++ x3 →     (∀ (x5 : Fin x3.length),         have x6 : List (BitVec (24 : ℕ)) := x2 ++ List.take (↑x5) x3;         x3.get x5 ∉ x6 ∧ x3.get x5 ≠ (0 : BitVec (24 : ℕ)) ∧ x3.get x5 ≠ (-1 : BitVec (24 : ℕ)) ∧ ∃ x7 ∈ x6, ∃ x8 ∈ x6, x3.get x5 = x7 &&& x8 ∨ x3.get x5 = x7 ||| x8) →       (15 : ℕ) ≤ x3.length := by
  dsimp only
  intro xs has ok
  by_contra! low
  obtain ⟨h,len,steps,u,hu,v,hv,nu,nv,join⟩ := normal xs has ok (by omega)
  rcases join with meet|join
  · apply andCut h len steps u hu v hv nu nv _ _ meet
    · rw [meet]; calc
        _ = (u &&& u) &&& v := by ac_rfl
        _ = _ := by simp
    · rw [meet,BitVec.and_assoc,BitVec.and_self]
  · apply orCut h len steps u hu v hv nu nv _ _ join
    · rw [join]; calc
        _ = (u ||| u) ||| v := by ac_rfl
        _ = _ := by simp
    · rw [join,BitVec.or_assoc,BitVec.or_self]
