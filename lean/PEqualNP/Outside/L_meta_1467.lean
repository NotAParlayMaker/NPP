import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1467

private lemma planeQuad_intersection_unique
    {n m : ℕ} (S : Fin m → Finset (Fin n))
    (hmeet : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card = 1)
    {i j : Fin m} (hij : i ≠ j) {x y : Fin n}
    (hxi : x ∈ S i) (hxj : x ∈ S j)
    (hyi : y ∈ S i) (hyj : y ∈ S j) : x = y := by
  by_contra hxy
  have hx : x ∈ S i ∩ S j := by simp [Finset.mem_inter, hxi, hxj]
  have hy : y ∈ S i ∩ S j := by simp [Finset.mem_inter, hyi, hyj]
  have hlt : 1 < (S i ∩ S j).card :=
    Finset.one_lt_card_iff.mpr ⟨x, y, hx, hy, hxy⟩
  rw [hmeet i j hij] at hlt
  omega

private lemma planeQuad_line_eq_of_two
    {n m : ℕ} (S : Fin m → Finset (Fin n))
    (hmeet : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card = 1)
    {i j : Fin m} {x y : Fin n} (hxy : x ≠ y)
    (hxi : x ∈ S i) (hyi : y ∈ S i)
    (hxj : x ∈ S j) (hyj : y ∈ S j) : i = j := by
  by_contra hij
  have hpoint := planeQuad_intersection_unique S hmeet hij
    (x := x) (y := y) hxi hxj hyi hyj
  exact hxy hpoint

private lemma planeQuad_exists_third
    {n : ℕ} (T : Finset (Fin n)) (hcard : 2 < T.card)
    {a b : Fin n} (hab : a ≠ b) :
    ∃ c, c ∈ T ∧ c ≠ a ∧ c ≠ b := by
  by_contra hno
  have hsub : T ⊆ {a, b} := by
    intro z hz
    by_cases hza : z = a
    · simp [hza]
    by_cases hzb : z = b
    · simp [hzb]
    · exact False.elim (hno ⟨z, hz, hza, hzb⟩)
  have hle : T.card ≤ 2 := by
    calc
      T.card ≤ ({a, b} : Finset (Fin n)).card := Finset.card_le_card hsub
      _ = 2 := by simp [hab]
  omega

private def planeQuad_map {n : ℕ} (A B C D : Fin n) : Fin 4 → Fin n := fun t =>
  if t.val = 0 then A else if t.val = 1 then B else if t.val = 2 then C else D

set_option maxHeartbeats 1000000 in
theorem exists_quadrangle
    (q n m : ℕ) (S : Fin m → Finset (Fin n))
    (hq : 2 ≤ q)
    (hsize : ∀ i : Fin m, (S i).card = q + 1)
    (hmeet : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card = 1)
    (hpair : ∀ u v : Fin n, u ≠ v → ∃ i : Fin m, u ∈ S i ∧ v ∈ S i)
    (hoff : ∃ i : Fin m, ∃ v : Fin n, v ∉ S i) :
    ∃ P : Fin 4 → Fin n, Function.Injective P ∧
      ∀ i : Fin m, (Finset.univ.filter (fun j : Fin 4 => P j ∈ S i)).card ≤ 2 := by
  obtain ⟨i₀, B, hBoff⟩ := hoff
  have hlarge (i : Fin m) : 3 ≤ (S i).card := by
    rw [hsize i]
    omega
  have hlarge0 := hlarge i₀
  have htwo : 1 < (S i₀).card := by omega
  obtain ⟨A, C, hA, hC, hAC⟩ := Finset.one_lt_card_iff.mp htwo
  have hAB : A ≠ B := by
    intro h
    subst B
    exact hBoff hA
  have hBC : B ≠ C := by
    intro h
    subst B
    exact hBoff hC

  obtain ⟨j, hAj, hBj⟩ := hpair A B hAB
  obtain ⟨k, hBk, hCk⟩ := hpair B C hBC
  have hk0 : k ≠ i₀ := by
    intro h
    subst k
    exact hBoff hBk
  have hjk : j ≠ k := by
    intro h
    subst k
    have hAi₀ : A ∈ S i₀ := hA
    have hCi₀ : C ∈ S i₀ := hC
    have hAk : A ∈ S j := hAj
    have hCk' : C ∈ S j := hCk
    have heq := planeQuad_line_eq_of_two S hmeet hAC hAi₀ hCi₀ hAk hCk'
    exact hk0 heq.symm

  have hlargek := hlarge k
  have hcardk : 2 < (S k).card := by omega
  obtain ⟨Q, hQk, hQB, hQC⟩ :=
    planeQuad_exists_third (S k) hcardk hBC
  have hQoff0 : Q ∉ S i₀ := by
    intro hQi₀
    have hpoint := planeQuad_intersection_unique S hmeet hk0
      (x := C) (y := Q) hCk hC hQk hQi₀
    exact hQC hpoint.symm
  have hQoffj : Q ∉ S j := by
    intro hQj
    have hpoint := planeQuad_intersection_unique S hmeet hjk
      (x := B) (y := Q) hBj hBk hQj hQk
    exact hQB hpoint.symm
  have hAoffk : A ∉ S k := by
    intro hAk
    have heq := planeQuad_line_eq_of_two S hmeet hAC hA hC hAk hCk
    exact hk0 heq.symm
  have hAQ : A ≠ Q := by
    intro h
    subst Q
    exact hQoff0 hA
  obtain ⟨ell, hAell, hQell⟩ := hpair A Q hAQ
  have hell0 : ell ≠ i₀ := by
    intro h
    subst ell
    exact hQoff0 hQell
  have hellj : ell ≠ j := by
    intro h
    subst ell
    exact hQoffj hQell
  have hellk : ell ≠ k := by
    intro h
    subst ell
    exact hAoffk hAell

  have hlargeell := hlarge ell
  have hcardell : 2 < (S ell).card := by omega
  obtain ⟨D, hDell, hDA, hDQ⟩ :=
    planeQuad_exists_third (S ell) hcardell hAQ
  have hDoff0 : D ∉ S i₀ := by
    intro hDi₀
    have hpoint := planeQuad_intersection_unique S hmeet hell0
      (x := A) (y := D) hAell hA hDell hDi₀
    exact hDA hpoint.symm
  have hDoffj : D ∉ S j := by
    intro hDj
    have hpoint := planeQuad_intersection_unique S hmeet hellj
      (x := A) (y := D) hAell hAj hDell hDj
    exact hDA hpoint.symm
  have hDoffk : D ∉ S k := by
    intro hDk
    have hpoint := planeQuad_intersection_unique S hmeet hellk
      (x := Q) (y := D) hQell hQk hDell hDk
    exact hDQ hpoint.symm

  have hDB : D ≠ B := by
    intro h
    subst D
    exact hDoffj hBj
  have hDA' : D ≠ A := hDA
  have hDC : D ≠ C := by
    intro h
    subst D
    exact hDoff0 hC
  let P : Fin 4 → Fin n := planeQuad_map A B C D
  have hP0 : P 0 = A := by simp [P, planeQuad_map]
  have hP1 : P 1 = B := by simp [P, planeQuad_map]
  have hP2 : P 2 = C := by simp [P, planeQuad_map]
  have hP3 : P 3 = D := by simp [P, planeQuad_map]
  have hPinj : Function.Injective P := by
    intro x y hxy
    fin_cases x <;> fin_cases y <;> simp_all [P, planeQuad_map, hAB, hAC, hBC,
      hDA', hDB, hDC]

  have hnoABC (i : Fin m) : ¬ (A ∈ S i ∧ B ∈ S i ∧ C ∈ S i) := by
    rintro ⟨hAi, hBi, hCi⟩
    have heq := planeQuad_line_eq_of_two S hmeet hAC hA hC hAi hCi
    subst i
    exact hBoff hBi
  have hnoABD (i : Fin m) : ¬ (A ∈ S i ∧ B ∈ S i ∧ D ∈ S i) := by
    rintro ⟨hAi, hBi, hDi⟩
    have heq := planeQuad_line_eq_of_two S hmeet hAB hAj hBj hAi hBi
    subst i
    exact hDoffj hDi
  have hnoACD (i : Fin m) : ¬ (A ∈ S i ∧ C ∈ S i ∧ D ∈ S i) := by
    rintro ⟨hAi, hCi, hDi⟩
    have heq := planeQuad_line_eq_of_two S hmeet hAC hA hC hAi hCi
    subst i
    exact hDoff0 hDi
  have hnoBCD (i : Fin m) : ¬ (B ∈ S i ∧ C ∈ S i ∧ D ∈ S i) := by
    rintro ⟨hBi, hCi, hDi⟩
    have heq := planeQuad_line_eq_of_two S hmeet hBC hBk hCk hBi hCi
    subst i
    exact hDoffk hDi

  refine ⟨P, hPinj, ?_⟩
  intro i
  classical
  by_contra hcard
  have hgt : 2 < (Finset.univ.filter (fun t : Fin 4 => P t ∈ S i)).card := by omega
  obtain ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz⟩ :=
    Finset.two_lt_card_iff.mp hgt
  have hxmem : P x ∈ S i := (Finset.mem_filter.mp hx).2
  have hymem : P y ∈ S i := (Finset.mem_filter.mp hy).2
  have hzmem : P z ∈ S i := (Finset.mem_filter.mp hz).2
  fin_cases x <;> fin_cases y <;> fin_cases z <;>
    simp_all [P, planeQuad_map, hnoABC, hnoABD, hnoACD, hnoBCD]

end PEqualNP.Outside.L_meta_1467

namespace PEqualNP.Outside.L_meta_1467

def sideEnds : Fin 6 → Finset (Fin 4) := ![{0,1},{0,2},{1,3},{1,2},{2,3},{0,3}]

lemma choose_sides {n m : ℕ} (S : Fin m → Finset (Fin n)) (P : Fin 4 → Fin n)
    (hP : Function.Injective P)
    (hquad : ∀ i : Fin m, (Finset.univ.filter (fun j : Fin 4 => P j ∈ S i)).card ≤ 2)
    (hjoin : ∀ u v : Fin n, u ≠ v → ∃ i : Fin m, u ∈ S i ∧ v ∈ S i) :
    ∃ L : Fin 6 → Fin m, Function.Injective L ∧ ∀ i j, P j ∈ S (L i) ↔ j ∈ sideEnds i := by
  have each (r : Fin 6) : ∃ l : Fin m, ∀ j, P j ∈ S l ↔ j ∈ sideEnds r := by
    have h2 : ∀ r : Fin 6, (sideEnds r).card = 2 := by decide
    obtain ⟨a, b, hab, he⟩ := Finset.card_eq_two.mp (h2 r)
    obtain ⟨l, ha, hb⟩ := hjoin (P a) (P b) (fun h => hab (hP h))
    let trace := Finset.univ.filter (fun j : Fin 4 => P j ∈ S l)
    have sub : sideEnds r ⊆ trace := by
      rw [he]
      intro j hj
      rcases (by simpa using hj : j = a ∨ j = b) with rfl | rfl <;> simp [trace, *]
    have eq := Finset.eq_of_subset_of_card_le sub (by rw [h2]; exact hquad l)
    refine ⟨l, fun j => ?_⟩
    rw [eq]
    simp [trace]
  choose L hL using each
  refine ⟨L, ?_, hL⟩
  have diff : ∀ i j : Fin 6, sideEnds i = sideEnds j → i = j := by decide
  intro i j hij
  apply diff
  ext x
  rw [← hL i x, hij, hL j x]

end PEqualNP.Outside.L_meta_1467

namespace PEqualNP.Outside.L_meta_1467

def residueInc (i : Fin 6) (z : Fin 7) : Prop :=
  z.val = (i.val + 1) % 7 ∨ z.val = (i.val + 2) % 7 ∨ z.val = (i.val + 4) % 7

lemma residue_columns_distinct : ∀ x y : Fin 7,
    (∀ i : Fin 6, (x.val = (i.val + 1) % 7 ∨ x.val = (i.val + 2) % 7 ∨ x.val = (i.val + 4) % 7) ↔
      (y.val = (i.val + 1) % 7 ∨ y.val = (i.val + 2) % 7 ∨ y.val = (i.val + 4) % 7)) → x = y := by
  decide

lemma pack_diagonal_points {n m : ℕ} (S : Fin m → Finset (Fin n)) (P : Fin 4 → Fin n)
    (L : Fin 6 → Fin m) (d0 d1 d3 : Fin n)
    (hSides : ∀ i j, P j ∈ S (L i) ↔ j ∈ sideEnds i)
    (h0 : ∀ i, d0 ∈ S (L i) ↔ i = 3 ∨ i = 5)
    (h1 : ∀ i, d1 ∈ S (L i) ↔ i = 0 ∨ i = 4)
    (h3 : ∀ i, d3 ∈ S (L i) ↔ i = 1 ∨ i = 2) :
    ∃ p : Fin 7 → Fin n, Function.Injective p ∧ ∀ i z, p z ∈ S (L i) ↔ residueInc i z := by
  let p : Fin 7 → Fin n := ![d0, d1, P 0, d3, P 1, P 2, P 3]
  have trace : ∀ z i, p z ∈ S (L i) ↔ residueInc i z := by
    intro z
    fin_cases z
    · change ∀ i : Fin 6, d0 ∈ S (L i) ↔ _
      intro i
      rw [h0]
      unfold residueInc
      decide +revert
    · change ∀ i : Fin 6, d1 ∈ S (L i) ↔ _
      intro i
      rw [h1]
      unfold residueInc
      decide +revert
    · change ∀ i : Fin 6, P 0 ∈ S (L i) ↔ _
      intro i
      rw [hSides]
      unfold residueInc
      decide +revert
    · change ∀ i : Fin 6, d3 ∈ S (L i) ↔ _
      intro i
      rw [h3]
      unfold residueInc
      decide +revert
    · change ∀ i : Fin 6, P 1 ∈ S (L i) ↔ _
      intro i
      rw [hSides]
      unfold residueInc
      decide +revert
    · change ∀ i : Fin 6, P 2 ∈ S (L i) ↔ _
      intro i
      rw [hSides]
      unfold residueInc
      decide +revert
    · change ∀ i : Fin 6, P 3 ∈ S (L i) ↔ _
      intro i
      rw [hSides]
      unfold residueInc
      decide +revert
  refine ⟨p, ?_, fun i z => trace z i⟩
  intro x y hxy
  apply residue_columns_distinct x y
  intro i
  exact (trace x i).symm.trans (hxy ▸ trace y i)

end PEqualNP.Outside.L_meta_1467

namespace PEqualNP.Outside.L_meta_1467.Diagonals

open PEqualNP.Outside.L_meta_1467

private lemma common_point_eq {α : Type*} [DecidableEq α]
    {A B : Finset α} (hcard : (A ∩ B).card = 1) {x y : α}
    (hxA : x ∈ A) (hxB : x ∈ B) (hyA : y ∈ A) (hyB : y ∈ B) : x = y := by
  obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hcard
  have hx : x = z := by
    have hm : x ∈ A ∩ B := Finset.mem_inter.mpr ⟨hxA, hxB⟩
    rw [hz] at hm
    simpa using hm
  have hy : y = z := by
    have hm : y ∈ A ∩ B := Finset.mem_inter.mpr ⟨hyA, hyB⟩
    rw [hz] at hm
    simpa using hm
  exact hx.trans hy.symm

noncomputable def meetPoint {n m : ℕ} (S : Fin m → Finset (Fin n))
    (L : Fin 6 → Fin m) (hL : Function.Injective L)
    (hcross : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card = 1)
    (i j : Fin 6) (hij : i ≠ j) : Fin n :=
  Classical.choose (Finset.card_eq_one.mp (hcross (L i) (L j) (fun h => hij (hL h))))

lemma meetPoint_spec {n m : ℕ} (S : Fin m → Finset (Fin n))
    (L : Fin 6 → Fin m) (hL : Function.Injective L)
    (hcross : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card = 1)
    (i j : Fin 6) (hij : i ≠ j) :
    S (L i) ∩ S (L j) = {meetPoint S L hL hcross i j hij} := by
  exact Classical.choose_spec (Finset.card_eq_one.mp (hcross (L i) (L j) (fun h => hij (hL h))))

lemma meetPoint_mem_left {n m : ℕ} (S : Fin m → Finset (Fin n))
    (L : Fin 6 → Fin m) (hL : Function.Injective L)
    (hcross : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card = 1)
    (i j : Fin 6) (hij : i ≠ j) :
    meetPoint S L hL hcross i j hij ∈ S (L i) := by
  have hs := meetPoint_spec S L hL hcross i j hij
  have hm : meetPoint S L hL hcross i j hij ∈ S (L i) ∩ S (L j) := by
    rw [hs]
    simp
  exact (Finset.mem_inter.mp hm).1

lemma meetPoint_mem_right {n m : ℕ} (S : Fin m → Finset (Fin n))
    (L : Fin 6 → Fin m) (hL : Function.Injective L)
    (hcross : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card = 1)
    (i j : Fin 6) (hij : i ≠ j) :
    meetPoint S L hL hcross i j hij ∈ S (L j) := by
  have hs := meetPoint_spec S L hL hcross i j hij
  have hm : meetPoint S L hL hcross i j hij ∈ S (L i) ∩ S (L j) := by
    rw [hs]
    simp
  exact (Finset.mem_inter.mp hm).2

private lemma unique_on_lines {n m : ℕ} (S : Fin m → Finset (Fin n))
    (L : Fin 6 → Fin m) (hL : Function.Injective L)
    (hcross : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card = 1)
    (i j : Fin 6) (hij : i ≠ j) {x y : Fin n}
    (hxI : x ∈ S (L i)) (hxJ : x ∈ S (L j))
    (hyI : y ∈ S (L i)) (hyJ : y ∈ S (L j)) : x = y := by
  apply common_point_eq (hcross (L i) (L j) (fun h => hij (hL h))) <;> assumption

private lemma share_side_0 (i : Fin 6) (hi0 : i ≠ 0) (hi4 : i ≠ 4) :
    ∃ j : Fin 4, j ∈ sideEnds 0 ∧ j ∈ sideEnds i := by
  fin_cases i <;> simp_all [sideEnds]

private lemma share_side_1 (i : Fin 6) (hi1 : i ≠ 1) (hi2 : i ≠ 2) :
    ∃ j : Fin 4, j ∈ sideEnds 1 ∧ j ∈ sideEnds i := by
  fin_cases i <;> simp_all [sideEnds]

private lemma share_side_3 (i : Fin 6) (hi3 : i ≠ 3) (hi5 : i ≠ 5) :
    ∃ j : Fin 4, j ∈ sideEnds 3 ∧ j ∈ sideEnds i := by
  fin_cases i <;> simp_all [sideEnds]

private lemma meet_not_base {n m : ℕ} (S : Fin m → Finset (Fin n))
    (P : Fin 4 → Fin n) (L : Fin 6 → Fin m) (hL : Function.Injective L)
    (hSides : ∀ i j, P j ∈ S (L i) ↔ j ∈ sideEnds i)
    (hcross : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card = 1)
    (i j : Fin 6) (hij : i ≠ j) (k : Fin 4)
    (hi : meetPoint S L hL hcross i j hij ∈ S (L i))
    (hj : meetPoint S L hL hcross i j hij ∈ S (L j))
    (hdis : Disjoint (sideEnds i) (sideEnds j)) :
    meetPoint S L hL hcross i j hij ≠ P k := by
  intro heq
  have hi' : P k ∈ S (L i) := by simpa [heq] using hi
  have hj' : P k ∈ S (L j) := by simpa [heq] using hj
  have hki : k ∈ sideEnds i := (hSides i k).mp hi'
  have hkj : k ∈ sideEnds j := (hSides j k).mp hj'
  exact Finset.disjoint_left.mp hdis hki hkj

private lemma meet_not_third {n m : ℕ} (S : Fin m → Finset (Fin n))
    (P : Fin 4 → Fin n) (L : Fin 6 → Fin m) (hL : Function.Injective L)
    (hSides : ∀ i j, P j ∈ S (L i) ↔ j ∈ sideEnds i)
    (hcross : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card = 1)
    (i k : Fin 6) (hik : i ≠ k) (d : Fin n)
    (hdi : d ∈ S (L i)) (hdb : ∀ j : Fin 4, d ≠ P j)
    (hshare : ∃ j : Fin 4, j ∈ sideEnds i ∧ j ∈ sideEnds k) :
    d ∉ S (L k) := by
  intro hdk
  obtain ⟨j, hji, hjk⟩ := hshare
  have hpI : P j ∈ S (L i) := (hSides i j).2 hji
  have hpK : P j ∈ S (L k) := (hSides k j).2 hjk
  have heq := unique_on_lines S L hL hcross i k hik hdi hdk hpI hpK
  exact hdb j heq

theorem choose_diagonals {n m : ℕ} (S : Fin m → Finset (Fin n))
    (P : Fin 4 → Fin n) (L : Fin 6 → Fin m)
    (hL : Function.Injective L)
    (hSides : ∀ i j, P j ∈ S (L i) ↔ j ∈ sideEnds i)
    (hcross : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card = 1) :
    ∃ p : Fin 7 → Fin n, Function.Injective p ∧
      ∀ i : Fin 6, ∀ z : Fin 7, p z ∈ S (L i) ↔
        z.val = (i.val + 1) % 7 ∨ z.val = (i.val + 2) % 7 ∨ z.val = (i.val + 4) % 7 := by
  classical
  let d1 := meetPoint S L hL hcross 0 4 (by decide)
  let d3 := meetPoint S L hL hcross 1 2 (by decide)
  let d0 := meetPoint S L hL hcross 3 5 (by decide)
  have hd1_0 : d1 ∈ S (L 0) := meetPoint_mem_left S L hL hcross 0 4 (by decide)
  have hd1_4 : d1 ∈ S (L 4) := meetPoint_mem_right S L hL hcross 0 4 (by decide)
  have hd3_1 : d3 ∈ S (L 1) := meetPoint_mem_left S L hL hcross 1 2 (by decide)
  have hd3_2 : d3 ∈ S (L 2) := meetPoint_mem_right S L hL hcross 1 2 (by decide)
  have hd0_3 : d0 ∈ S (L 3) := meetPoint_mem_left S L hL hcross 3 5 (by decide)
  have hd0_5 : d0 ∈ S (L 5) := meetPoint_mem_right S L hL hcross 3 5 (by decide)
  have hd1_nb : ∀ j : Fin 4, d1 ≠ P j := by
    intro j
    exact meet_not_base S P L hL hSides hcross 0 4 (by decide) j hd1_0 hd1_4 (by decide)
  have hd3_nb : ∀ j : Fin 4, d3 ≠ P j := by
    intro j
    exact meet_not_base S P L hL hSides hcross 1 2 (by decide) j hd3_1 hd3_2 (by decide)
  have hd0_nb : ∀ j : Fin 4, d0 ≠ P j := by
    intro j
    exact meet_not_base S P L hL hSides hcross 3 5 (by decide) j hd0_3 hd0_5 (by decide)
  have h1 : ∀ i : Fin 6, d1 ∈ S (L i) ↔ i = 0 ∨ i = 4 := by
    intro i
    constructor
    · intro hdi
      by_cases hi0 : i = 0
      · exact Or.inl hi0
      by_cases hi4 : i = 4
      · exact Or.inr hi4
      · have hnot := meet_not_third S P L hL hSides hcross 0 i (Ne.symm hi0)
          d1 hd1_0 hd1_nb (share_side_0 i hi0 hi4)
        exact False.elim (hnot hdi)
    · rintro (rfl | rfl)
      · exact hd1_0
      · exact hd1_4
  have h3 : ∀ i : Fin 6, d3 ∈ S (L i) ↔ i = 1 ∨ i = 2 := by
    intro i
    constructor
    · intro hdi
      by_cases hi1 : i = 1
      · exact Or.inl hi1
      by_cases hi2 : i = 2
      · exact Or.inr hi2
      · have hnot := meet_not_third S P L hL hSides hcross 1 i (Ne.symm hi1)
          d3 hd3_1 hd3_nb (share_side_1 i hi1 hi2)
        exact False.elim (hnot hdi)
    · rintro (rfl | rfl)
      · exact hd3_1
      · exact hd3_2
  have h0 : ∀ i : Fin 6, d0 ∈ S (L i) ↔ i = 3 ∨ i = 5 := by
    intro i
    constructor
    · intro hdi
      by_cases hi3 : i = 3
      · exact Or.inl hi3
      by_cases hi5 : i = 5
      · exact Or.inr hi5
      · have hnot := meet_not_third S P L hL hSides hcross 3 i (Ne.symm hi3)
          d0 hd0_3 hd0_nb (share_side_3 i hi3 hi5)
        exact False.elim (hnot hdi)
    · rintro (rfl | rfl)
      · exact hd0_3
      · exact hd0_5
  exact pack_diagonal_points S P L d0 d1 d3 hSides h0 h1 h3

end PEqualNP.Outside.L_meta_1467.Diagonals

namespace PEqualNP.Outside.L_meta_1467

def fanoTriple (i : Fin 7) : Finset (Fin 7) :=
  Finset.univ.filter fun z =>
    z.val = (i.val + 1) % 7 ∨
    z.val = (i.val + 2) % 7 ∨
    z.val = (i.val + 4) % 7

lemma mem_fanoTriple (i z : Fin 7) :
    z ∈ fanoTriple i ↔
      z.val = (i.val + 1) % 7 ∨
      z.val = (i.val + 2) % 7 ∨
      z.val = (i.val + 4) % 7 := by
  simp [fanoTriple]

lemma no_self_mem_fanoTriple (i : Fin 7) : i ∉ fanoTriple i := by
  decide +revert

lemma fano_antipodal : ∀ a b : Fin 7,
    a.val ≠ b.val →
    ¬ (a.val = (b.val + 1) % 7 ∨ a.val = (b.val + 2) % 7 ∨ a.val = (b.val + 4) % 7) ∨
    ¬ (b.val = (a.val + 1) % 7 ∨ b.val = (a.val + 2) % 7 ∨ b.val = (a.val + 4) % 7) := by
  decide

set_option maxRecDepth 4096 in
lemma trace_subset_some_fanoTriple (A : Finset (Fin 7))
    (hA : ∀ i : Fin 7, (A ∩ fanoTriple i).card ≤ 1) :
    ∃ i : Fin 7, A ⊆ fanoTriple i := by
  decide +revert

def fanoIndex (i : Fin 6) : Fin 7 := ⟨i.val, by omega⟩

set_option maxRecDepth 4096 in
lemma trace_subset_from_first_six (A : Finset (Fin 7))
    (hA : ∀ i : Fin 6, (A ∩ fanoTriple (fanoIndex i)).card ≤ 1) :
    ∃ i : Fin 7, A ⊆ fanoTriple i := by
  decide +revert

def pointTrace {n m : ℕ} (S : Fin m → Finset (Fin n))
    (p : Fin 7 → Fin n) (j : Fin m) : Finset (Fin 7) :=
  Finset.univ.filter fun z => p z ∈ S j

lemma each_point_trace_fano {n m : ℕ} (S : Fin m → Finset (Fin n))
    (p : Fin 7 → Fin n) (L : Fin 6 → Fin m)
    (hp : Function.Injective p)
    (htrace : ∀ (i : Fin 6) (z : Fin 7), p z ∈ S (L i) ↔
      z.val = (i.val + 1) % 7 ∨ z.val = (i.val + 2) % 7 ∨ z.val = (i.val + 4) % 7)
    (hline : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card = 1) :
    ∀ j : Fin m, ∃ r : Fin 7, pointTrace S p j ⊆ fanoTriple r := by
  intro j
  by_cases hex : ∃ i : Fin 6, L i = j
  · obtain ⟨i, hi⟩ := hex
    subst j
    refine ⟨fanoIndex i, ?_⟩
    intro z hz
    have hzline : p z ∈ S (L i) := (Finset.mem_filter.mp hz).2
    have hzcoords := (htrace i z).1 hzline
    exact (mem_fanoTriple (fanoIndex i) z).2 (by simpa [fanoIndex] using hzcoords)
  · apply trace_subset_from_first_six
    intro i
    let U := pointTrace S p j ∩ fanoTriple (fanoIndex i)
    have hij : j ≠ L i := by
      intro h
      exact hex ⟨i, h.symm⟩
    have himage : U.image p ⊆ S j ∩ S (L i) := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨z, hz, rfl⟩
      have hz' := Finset.mem_inter.mp hz
      have hzline : p z ∈ S j := (Finset.mem_filter.mp hz'.1).2
      have hzfano : z ∈ fanoTriple (fanoIndex i) := hz'.2
      have hzcoords := (mem_fanoTriple (fanoIndex i) z).mp hzfano
      have hzcoords' : z.val = (i.val + 1) % 7 ∨
          z.val = (i.val + 2) % 7 ∨ z.val = (i.val + 4) % 7 := by
        simpa [fanoIndex] using hzcoords
      exact Finset.mem_inter.mpr ⟨hzline, (htrace i z).2 hzcoords'⟩
    have hinj : Set.InjOn p U := by
      intro a ha b hb hab
      exact hp hab
    have hcardImage : (U.image p).card = U.card := Finset.card_image_iff.mpr hinj
    have hcardU : U.card ≤ 1 := by
      calc
        U.card = (U.image p).card := hcardImage.symm
        _ ≤ (S j ∩ S (L i)).card := Finset.card_le_card himage
        _ = 1 := hline j (L i) hij
    simpa [U] using hcardU

theorem select_points {n m : ℕ} (S : Fin m → Finset (Fin n))
    (p : Fin 7 → Fin n) (L : Fin 6 → Fin m)
    (hp : Function.Injective p)
    (htrace : ∀ (i : Fin 6) (z : Fin 7), p z ∈ S (L i) ↔
      z.val = (i.val + 1) % 7 ∨ z.val = (i.val + 2) % 7 ∨ z.val = (i.val + 4) % 7)
    (hline : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card = 1) :
    ∃ b : Fin m → Fin n, (∀ i : Fin m, b i ∉ S i) ∧
      ∀ i j : Fin m, i ≠ j → ¬ (b i ∈ S j ∧ b j ∈ S i) := by
  let r : Fin m → Fin 7 := fun j =>
    Classical.choose (each_point_trace_fano S p L hp htrace hline j)
  have hr (j : Fin m) : pointTrace S p j ⊆ fanoTriple (r j) :=
    Classical.choose_spec (each_point_trace_fano S p L hp htrace hline j)
  have hoff (j : Fin m) : p (r j) ∉ S j := by
    intro h
    have hmem : r j ∈ pointTrace S p j := by
      simp [pointTrace, h]
    exact no_self_mem_fanoTriple (r j) (hr j hmem)
  refine ⟨fun j => p (r j), ?_, ?_⟩
  · exact hoff
  · intro i j hij
    rintro ⟨hi, hj⟩
    have hneq : (r i).val ≠ (r j).val := by
      intro heq
      apply hoff j
      have hEq : r i = r j := Fin.ext heq
      simpa [hEq] using hi
    have hiTrace : r i ∈ pointTrace S p j := by
      simp [pointTrace, hi]
    have hjTrace : r j ∈ pointTrace S p i := by
      simp [pointTrace, hj]
    have hiTriple := (mem_fanoTriple (r j) (r i)).mp (hr j hiTrace)
    have hjTriple := (mem_fanoTriple (r i) (r j)).mp (hr i hjTrace)
    rcases fano_antipodal (r i) (r j) hneq with h | h
    · exact h hiTriple
    · exact h hjTriple

end PEqualNP.Outside.L_meta_1467

open PEqualNP.Outside.L_meta_1467 in
theorem PEqualNP.Outside.L_meta_1467 : ∀ (q n m : ℕ) (S : Fin m → Finset (Fin n)),
    2 ≤ q → (∀ i : Fin m, (S i).card = q + 1) →
    (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card = 1) →
    (∀ u v : Fin n, u ≠ v → ∃ i : Fin m, u ∈ S i ∧ v ∈ S i) →
    (∃ (i : Fin m) (v : Fin n), v ∉ S i) →
    ∃ b : Fin m → Fin n, (∀ i : Fin m, b i ∉ S i) ∧
      ∀ i j : Fin m, i ≠ j → ¬ (b i ∈ S j ∧ b j ∈ S i) := by
  intro q n m S hq hsize hmeet hpair hoff
  obtain ⟨P, hp, hquad⟩ := exists_quadrangle q n m S hq hsize hmeet hpair hoff
  obtain ⟨L, hl, hsides⟩ := choose_sides S P hp hquad hpair
  obtain ⟨p, hinj, htrace⟩ := Diagonals.choose_diagonals S P L hl hsides hmeet
  exact select_points S p L hinj htrace hmeet
