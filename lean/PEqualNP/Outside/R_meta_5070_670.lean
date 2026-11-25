import PEqualNP.Defs

-- Separate exact incidence computation from genuinely high-width errors.
-- In the latter case all sparse slices are exact, but a whole incidence-free
-- subcube computes AND, with more than q free line coordinates.
theorem PEqualNP.Outside.R_meta_5070_670
    (cube :
    ∀ (q n : ℕ) (I : Fin n → Fin n → Prop) [DecidableRel I],
    let B := Fin n → Bool
    let m := n+n
    let one (a b : Fin n) := decide (b=a)
    let wt (v : B) := Fintype.card {j : Fin n // v j = true}
    let H : Set (B × B) := {z | ∃ p l, I p l ∧ z.1 p = true ∧ z.2 l = true}
    ∀ (s o : ℕ) (W : ℕ → Set (B × B)), o < m+s →
    (∀ j : Fin n, W j.val = {z | z.1 j = true} ∧ W (n+j.val) = {z | z.2 j = true}) →
    (∀ i < s, ∃ a b, max a b < m+i ∧ W (m+i) ∈ [W a ∪ W b, W a, ∅, W a ∩ W b]) →
    (∀ p l, I p l → (one p,one l) ∈ W o) →
    (∀ L : B, wt L ≤ q → ((fun p => decide (¬∃ l, I p l ∧ L l = true)),L) ∉ W o) →
    (∀ z : B × B, wt z.2 ≤ q → (z ∈ W o ↔ z ∈ H)) ∧
    (W o = H ∨ ∃ z : B × B, z ∉ H ∧ q < wt z.2 ∧ ∀ y ≤ z, (y ∈ W o ↔ y = z)))
    (exactCase :
    ∀ (q n : ℕ) (I : Fin n → Fin n → Prop) [DecidableRel I],
    let B := Fin n → Bool
    let m := n+n
    let one (a b : Fin n) := decide (b=a)
    let H : Set (B × B) := {z | ∃ p l, I p l ∧ z.1 p = true ∧ z.2 l = true}
    200 ≤ q → n=q^2+q+1 → (∀ l, Fintype.card {p : Fin n // I p l}=q+1) →
    (∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) →
    ∀ (s o : ℕ) (W : ℕ → Set (B × B)) (E : Set (Fin n × Fin n)), o < m+s → m ≤ s+1 →
    (∀ j : Fin n, W j.val = {z | z.1 j = true} ∧ W (n+j.val) = {z | z.2 j = true}) →
    (∀ i < s, ∃ a b, max a b < m+i ∧ W (m+i) ∈ [W a ∪ W b, W a, ∅, W a ∩ W b]) →
    W o = H →
    E ⊆ {e | I e.1 e.2} → 96*s+n < E.ncard → 24*(n*q)+25*n < 25*E.ncard →
    (∀ i<s, W (m+i) ⊆ W o → ∀ a b, max a b < m+i → W (m+i) = W a ∩ W b →
       ∀ A C, W a = A ×ˢ Set.univ → W b = Set.univ ×ˢ C →
       ∀ e ∈ E, (one e.1,one e.2) ∉ W (m+i)) → False)
    (andMinor :
    ∀ (q n : ℕ) (I : Fin n → Fin n → Prop) [DecidableRel I],
    let B := Fin n → Bool
    let m := n+n
    let one (a b : Fin n) := decide (b=a)
    let wt (v : B) := Fintype.card {j : Fin n // v j = true}
    let H : Set (B × B) := {z | ∃ p l, I p l ∧ z.1 p = true ∧ z.2 l = true}
    200 ≤ q → n=q^2+q+1 → (∀ l, Fintype.card {p : Fin n // I p l}=q+1) →
    (∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) →
    ∀ (s o : ℕ) (W : ℕ → Set (B × B)) (E : Set (Fin n × Fin n)), o < m+s → m ≤ s+1 →
    (∀ j : Fin n, W j.val = {z | z.1 j = true} ∧ W (n+j.val) = {z | z.2 j = true}) →
    (∀ i < s, ∃ a b, max a b < m+i ∧ W (m+i) ∈ [W a ∪ W b, W a, ∅, W a ∩ W b]) →
    (∀ z : B × B, wt z.2 ≤ q → (z ∈ W o ↔ z ∈ H)) →
    (∃ z : B × B, z ∉ H ∧ q < wt z.2 ∧ ∀ y ≤ z, (y ∈ W o ↔ y = z)) →
    E ⊆ {e | I e.1 e.2} → 96*s+n < E.ncard → 24*(n*q)+25*n < 25*E.ncard →
    (∀ i<s, W (m+i) ⊆ W o → ∀ a b, max a b < m+i → W (m+i) = W a ∩ W b →
       ∀ A C, W a = A ×ˢ Set.univ → W b = Set.univ ×ˢ C →
       ∀ e ∈ E, (one e.1,one e.2) ∉ W (m+i)) → False) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3],   let x5 : Type := Fin x2 → Bool;   have x6 : Fin x2 → Fin x2 → Bool := fun (x6 x7 : Fin x2) => Decidable.decide (x7 = x6);   have x7 : ℕ := x2 + x2;   (200 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x10 : Fin x2), Fintype.card { x11 : Fin x2 // x3 x11 x10 } = x1 + (1 : ℕ)) → (∀ (x11 x12 : Fin x2), x11 ≠ x12 → ∃! x14 : Fin x2, x3 x11 x14 ∧ x3 x12 x14) → ∀ (x12 x13 : ℕ) (x14 : ℕ → Set (x5 × x5)) (x15 : Set (Fin x2 × Fin x2)), x13 < x7 + x12 → x7 ≤ x12 + (1 : ℕ) → (∀ (x18 : Fin x2), x14 ↑x18 = {x19 : x5 × x5 | x19.1 x18 = Bool.true} ∧ x14 (x2 + ↑x18) = {x19 : x5 × x5 | x19.2 x18 = Bool.true}) → (∀ x19 < x12, ∃ (x21 : ℕ) (x22 : ℕ), Max.max x21 x22 < x7 + x19 ∧ x14 (x7 + x19) ∈ [x14 x21 ∪ x14 x22, x14 x21, ∅, x14 x21 ∩ x14 x22]) → (∀ (x20 x21 : Fin x2), x3 x20 x21 → (x6 x20, x6 x21) ∈ x14 x13) → (∀ (x21 : x5), Fintype.card { x22 : Fin x2 // x21 x22 = Bool.true } ≤ x1 → (fun (x23 : Fin x2) => Decidable.decide ¬∃ (x24 : Fin x2), x3 x23 x24 ∧ x21 x24 = Bool.true, x21) ∉ x14 x13) → x15 ⊆ {x22 : Fin x2 × Fin x2 | x3 x22.1 x22.2} → (96 : ℕ) * x12 + x2 < x15.ncard → (24 : ℕ) * (x2 * x1) + (25 : ℕ) * x2 < (25 : ℕ) * x15.ncard → (∀ x25 < x12, x14 (x7 + x25) ⊆ x14 x13 → ∀ (x28 x29 : ℕ), Max.max x28 x29 < x7 + x25 → x14 (x7 + x25) = x14 x28 ∩ x14 x29 → ∀ (x32 x33 : Set x5), x14 x28 = x32 ×ˢ Set.univ → x14 x29 = Set.univ ×ˢ x33 → ∀ x36 ∈ x15, (x6 x36.1, x6 x36.2) ∉ x14 (x7 + x25)) → False := by
  intro q n I _ B one m hq hn line plane s o W E ho hm base gates pos neg sub density fraction bridges
  obtain ⟨sparse,H | large⟩ := cube q n I s o W ho base gates pos neg
  · exact exactCase q n I hq hn line plane s o W E ho hm base gates H sub density fraction bridges
  · exact andMinor q n I hq hn line plane s o W E ho hm base gates sparse large sub density fraction bridges
