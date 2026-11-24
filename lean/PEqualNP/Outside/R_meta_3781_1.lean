import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Set.Basic

-- Use an incident pair as a constant replacement. It changes no pure singleton
-- row and can add only positive rows to any wire.
theorem PEqualNP.Outside.R_meta_3781_1
  (removeConstants :
    ∀ (X : Type) (m s a₀ b₀ : ℕ) (W : ℕ → Set X),
      a₀ < m → b₀ < m →
      (∀ g < s, ∃ a b, max a b < m+g ∧
        W (m+g) ∈ [W a ∪ W b, W a, ∅, W a ∩ W b]) →
      ∃ U : ℕ → Set X, (∀ i < m, U i = W i) ∧
        (∀ i < m+s, W i ⊆ U i ∧ U i ⊆ W i ∪ (W a₀ ∩ W b₀)) ∧
        (∀ g < s, ∃ a b, max a b < m+g ∧
          (U (m+g) = U a ∪ U b ∨ U (m+g) = U a ∩ U b)))
  (cleanLower :
    ∀ (q n : ℕ) (S : Fin n → Finset (Fin n)),
      100 < q → n = q^2+q+1 → q % 2 = 0 →
      (∀ l, (S l).card = q+1) →
      (∀ p r, p ≠ r → ∃! l, p ∈ S l ∧ r ∈ S l) →
      ∀ (s o : ℕ) (U : ℕ → Set (Finset (Fin n) × Finset (Fin n))),
        let A (d : Bool) (w : ℕ) := {i : Fin n |
          (if d then ({i}, ∅) else (∅, {i})) ∈ U w}
        o < n+n+s →
        (∀ i : Fin n, U i.val = {z | i ∈ z.1} ∧ U (n+i.val) = {z | i ∈ z.2}) →
        (∀ g < s, ∃ a b, max a b < n+n+g ∧
          (U (n+n+g) = U a ∪ U b ∨ U (n+n+g) = U a ∩ U b)) →
        (∀ z, z.2.card ≤ q →
          (z ∈ U o ↔ ∃ i ∈ z.1, ∃ j ∈ z.2, i ∈ S j)) →
        (∃ g < s, ∃ d, (∃ T : Finset (Fin n), T.card = 3 ∧ ↑T ⊆ A d (n+n+g)) ∧
          ¬∃ a < n+n+g, ∃ b < n+n+g, A d (n+n+g) = A d a ∪ A d b) →
        n*q ≤ 100*s) :
  ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3],   (100 : ℕ) < x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) →         (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) →           x1 % (2 : ℕ) = (0 : ℕ) →             ∀ (x10 x11 : ℕ) (x12 : ℕ → Set ((Fin x2 → Bool) × (Fin x2 → Bool))),               have x13 : ℕ := x2 + x2;               have x14 : Fin x2 → Fin x2 → Bool := fun (x14 x15 : Fin x2) => Decidable.decide (x15 = x14);               x11 < x13 + x10 →                 (∀ (x16 : Fin x2), x12 ↑x16 = {x17 : (Fin x2 → Bool) × (Fin x2 → Bool) | x17.1 x16 = Bool.true} ∧ x12 (x2 + ↑x16) = {x17 : (Fin x2 → Bool) × (Fin x2 → Bool) | x17.2 x16 = Bool.true}) →                   (∀ x17 < x10, ∃ (x19 : ℕ) (x20 : ℕ), Max.max x19 x20 < x13 + x17 ∧ x12 (x13 + x17) ∈ [x12 x19 ∪ x12 x20, x12 x19, ∅, x12 x19 ∩ x12 x20]) →                     (∀ (x18 x19 : Fin x2), x3 x18 x19 → (x14 x18, x14 x19) ∈ x12 x11) →                       (∀ (x19 : Fin x2 → Bool), Fintype.card { x20 : Fin x2 // x19 x20 = Bool.true } ≤ x1 → (fun (x21 : Fin x2) => Decidable.decide ¬∃ (x22 : Fin x2), x3 x21 x22 ∧ x19 x22 = Bool.true, x19) ∉ x12 x11) →                         (have x20 : Bool → ℕ → Set (Fin x2) := fun (x20 : Bool) (x21 : ℕ) => {x22 : Fin x2 | (if x20 = Bool.true then (x14 x22, fun (x23 : Fin x2) => Bool.false) else (fun (x23 : Fin x2) => Bool.false, x14 x22)) ∈ x12 x21};                           ∃ x21 < x10, ∃ (x22 : Bool) (x23 : Fin x2) (x24 : Fin x2), x23 ≠ x24 ∧ x23 ∈ x20 x22 (x13 + x21) ∧ x24 ∈ x20 x22 (x13 + x21) ∧ ¬∃ x25 < x13 + x21, ∃ x26 < x13 + x21, x20 x22 (x13 + x21) = x20 x22 x25 ∪ x20 x22 x26) →                           x2 * x1 ≤ (100 : ℕ) * x10 := by
  dsimp only
  intro q n I idec large order degrees unique parity s o W out inputs steps accept reject witness
  classical
  let m := n+n
  let B := Fin n → Bool
  let bit (i j : Fin n) : Bool := decide (j = i)
  let below (x y : B × B) : Prop :=
    (∀ i, x.1 i = true → y.1 i = true) ∧ (∀ i, x.2 i = true → y.2 i = true)
  have mono (w : ℕ) (bound : w < m+s) (x y : B × B) (le : below x y) :
      x ∈ W w → y ∈ W w := by
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro mem
      by_cases lo : w < n
      · let i : Fin n := ⟨w,lo⟩
        change x ∈ W i.val at mem
        change y ∈ W i.val
        rw [(inputs i).1] at mem ⊢
        exact le.1 i mem
      · by_cases hi : w < m
        · let i : Fin n := ⟨w-n, by dsimp [m] at hi; omega⟩
          have eq : w = n+i.val := by dsimp [i]; omega
          rw [eq, (inputs i).2] at mem ⊢
          exact le.2 i mem
        · let g := w-m
          have eq : w = m+g := by dsimp [g]; omega
          obtain ⟨a,b,earlier,law⟩ := steps g (by omega)
          change max a b < m+g at earlier
          change W (m+g) ∈ [W a ∪ W b, W a, ∅, W a ∩ W b] at law
          have ha : a < w := (le_max_left _ _).trans_lt (eq.symm ▸ earlier)
          have hb : b < w := (le_max_right _ _).trans_lt (eq.symm ▸ earlier)
          have left := ih a ha (ha.trans bound)
          have right := ih b hb (hb.trans bound)
          rw [eq] at mem ⊢
          simp only [List.mem_cons, List.not_mem_nil, or_false] at law
          rcases law with e | e | e | e
          · rw [e] at mem ⊢
            exact mem.elim (fun h => Or.inl (left h)) (fun h => Or.inr (right h))
          · rw [e] at mem ⊢
            exact left mem
          · rw [e] at mem
            exact False.elim mem
          · rw [e] at mem ⊢
            exact ⟨left mem.1, right mem.2⟩
  have single_le (i : Fin n) (x : B) (hx : x i = true) :
      ∀ j, bit i j = true → x j = true := by
    intro j hj
    have e : j = i := of_decide_eq_true hj
    rwa [e]
  have npos : 0 < n := by omega
  let l : Fin n := ⟨0, npos⟩
  have incident : Nonempty {p : Fin n // I p l} :=
    Fintype.card_pos_iff.mp (by rw [degrees l]; omega)
  obtain ⟨⟨p,pl⟩⟩ := incident
  let K := W p.val ∩ W (n+l.val)
  have pbase : p.val < m := by have := p.isLt; dsimp [m]; omega
  have lbase : n+l.val < m := by have := l.isLt; dsimp [m]; omega
  obtain ⟨U, sameIn, sandwich, gates⟩ := removeConstants (B × B) m s p.val (n+l.val) W
    pbase lbase steps
  have safe : K ⊆ W o := by
    intro z hz
    have hp : z.1 p = true := by
      have h := hz.1
      rwa [(inputs p).1] at h
    have hl : z.2 l = true := by
      have h := hz.2
      rwa [(inputs l).2] at h
    exact mono o out (bit p, bit l) z ⟨single_le p z.1 hp, single_le l z.2 hl⟩ (accept p l pl)
  have sameOut : U o = W o := Set.Subset.antisymm
    (fun _ hz => ((sandwich o out).2 hz).elim id (fun hk => safe hk)) (sandwich o out).1
  let S (l : Fin n) := Finset.univ.filter (fun p => I p l)
  have memS (p l : Fin n) : p ∈ S l ↔ I p l := by simp [S]
  have cardS (l : Fin n) : (S l).card = q+1 := by
    rw [← Fintype.card_of_subtype (S l) (fun p => memS p l)]
    exact degrees l
  have uniqueS (p r : Fin n) (ne : p ≠ r) : ∃! l, p ∈ S l ∧ r ∈ S l := by
    simpa only [memS] using unique p r ne
  let F := Finset (Fin n)
  let enc (z : F × F) : B × B := (fun i => decide (i ∈ z.1), fun i => decide (i ∈ z.2))
  let V (w : ℕ) : Set (F × F) := enc ⁻¹' U w
  have encLeft (z : F × F) (i : Fin n) : (enc z).1 i = true ↔ i ∈ z.1 := by simp [enc]
  have encRight (z : F × F) (i : Fin n) : (enc z).2 i = true ↔ i ∈ z.2 := by simp [enc]
  have ventries (i : Fin n) : V i.val = {z | i ∈ z.1} ∧ V (n+i.val) = {z | i ∈ z.2} := by
    have hleft : i.val < m := by have := i.isLt; dsimp [m]; omega
    have hright : n+i.val < m := by have := i.isLt; dsimp [m]; omega
    constructor
    · ext z
      change enc z ∈ U i.val ↔ _
      rw [sameIn _ hleft, (inputs i).1]
      exact encLeft z i
    · ext z
      change enc z ∈ U (n+i.val) ↔ _
      rw [sameIn _ hright, (inputs i).2]
      exact encRight z i
  have vgates (g : ℕ) (hg : g < s) : ∃ a b, max a b < m+g ∧
      (V (m+g) = V a ∪ V b ∨ V (m+g) = V a ∩ V b) := by
    obtain ⟨a,b,earlier,h⟩ := gates g hg
    refine ⟨a,b,earlier,?_⟩
    rcases h with eq | eq
    · exact Or.inl (congrArg (fun T : Set (B × B) => enc ⁻¹' T) eq)
    · exact Or.inr (congrArg (fun T : Set (B × B) => enc ⁻¹' T) eq)
  have correct (z : F × F) (small : z.2.card ≤ q) :
      z ∈ V o ↔ ∃ i ∈ z.1, ∃ j ∈ z.2, i ∈ S j := by
    change enc z ∈ U o ↔ _
    rw [sameOut]
    simp only [memS]
    constructor
    · intro hit
      by_contra empty
      have count : Fintype.card {i : Fin n // (enc z).2 i = true} ≤ q :=
        (Fintype.card_of_subtype z.2 (fun i => (encRight z i).symm)).trans_le small
      let miss (i : Fin n) : Bool := decide (¬ ∃ j, I i j ∧ (enc z).2 j = true)
      have enlarged : below (enc z) (miss, (enc z).2) := by
        refine ⟨?_, fun _ h => h⟩
        intro i h
        apply decide_eq_true
        rintro ⟨j,ij,jin⟩
        exact empty ⟨i,(encLeft z i).mp h,j,(encRight z j).mp jin,ij⟩
      exact reject (enc z).2 count (mono o out (enc z) (miss, (enc z).2) enlarged hit)
    · rintro ⟨i,hi,j,hj,ij⟩
      exact mono o out (bit i,bit j) (enc z)
        ⟨single_le i _ ((encLeft z i).mpr hi), single_le j _ ((encRight z j).mpr hj)⟩
        (accept i j ij)
  let pure (d : Bool) (w : ℕ) : Set (Fin n) := {i |
    (if d then (bit i, fun _ => false) else (fun _ => false, bit i)) ∈ W w}
  let pureV (d : Bool) (w : ℕ) : Set (Fin n) := {i |
    (if d then ({i}, ∅) else (∅, {i})) ∈ V w}
  have samePure (d : Bool) (w : ℕ) (hw : w < m+s) : pureV d w = pure d w := by
    ext i
    let z : F × F := if d then ({i}, ∅) else (∅, {i})
    have emptyBit : (fun j : Fin n => decide (j ∈ (∅ : F))) = (fun _ => false) := by
      funext j
      exact decide_eq_false (Finset.notMem_empty j)
    have singleBit : (fun j : Fin n => decide (j ∈ ({i} : F))) = bit i := by
      funext j
      apply Bool.eq_iff_iff.mpr
      change decide (j ∈ ({i} : F)) = true ↔ decide (j = i) = true
      exact ⟨fun h => decide_eq_true (Finset.mem_singleton.mp (of_decide_eq_true h)),
        fun h => decide_eq_true (Finset.mem_singleton.mpr (of_decide_eq_true h))⟩
    have encoded : enc z = if d then (bit i, fun _ => false) else (fun _ => false, bit i) := by
      cases d
      · change enc ((∅, {i}) : F × F) = (fun _ => false, bit i)
        exact Prod.ext emptyBit singleBit
      · change enc (({i}, ∅) : F × F) = (bit i, fun _ => false)
        exact Prod.ext singleBit emptyBit
    have notK : enc z ∉ K := by
      change enc z ∉ W p.val ∩ W (n+l.val)
      rw [(inputs p).1, (inputs l).2]
      intro hit
      have hp : p ∈ z.1 := (encLeft z p).mp hit.1
      have hl : l ∈ z.2 := (encRight z l).mp hit.2
      cases d
      · exact Finset.notMem_empty p (show p ∈ (∅ : F) from hp)
      · exact Finset.notMem_empty l (show l ∈ (∅ : F) from hl)
    change enc z ∈ U w ↔
      (if d then (bit i, fun _ => false) else (fun _ => false, bit i)) ∈ W w
    rw [← encoded]
    exact ⟨fun h => ((sandwich w hw).2 h).resolve_right notK, fun h => (sandwich w hw).1 h⟩
  apply cleanLower q n S large order parity cardS uniqueS s o V out ventries vgates correct
  obtain ⟨g,hg,d,i,j,ne,hi,hj,noUnion⟩ := witness
  have bound : m+g < m+s := by omega
  have inI : i ∈ pureV d (m+g) := by rw [samePure d _ bound]; exact hi
  have inJ : j ∈ pureV d (m+g) := by rw [samePure d _ bound]; exact hj
  have noUnionV : ¬ ∃ a < m+g, ∃ b < m+g, pureV d (m+g) = pureV d a ∪ pureV d b := by
    rintro ⟨a,ha,b,hb,eq⟩
    rw [samePure d _ bound, samePure d _ (ha.trans bound), samePure d _ (hb.trans bound)] at eq
    exact noUnion ⟨a,ha,b,hb,eq⟩
  have atoms (x : Fin n) :
      ∃ a < m+g, pureV d a = ({x} : Set (Fin n)) := by
    cases d
    · refine ⟨n+x.val, by have := x.isLt; dsimp [m]; omega, ?_⟩
      ext y
      change ((∅, {y}) : F × F) ∈ V (n+x.val) ↔ _
      rw [(ventries x).2]
      change x ∈ ({y} : F) ↔ y = x
      exact Finset.mem_singleton.trans ⟨Eq.symm, Eq.symm⟩
    · refine ⟨x.val, by have := x.isLt; dsimp [m]; omega, ?_⟩
      ext y
      change (({y}, ∅) : F × F) ∈ V x.val ↔ _
      rw [(ventries x).1]
      change x ∈ ({y} : F) ↔ y = x
      exact Finset.mem_singleton.trans ⟨Eq.symm, Eq.symm⟩
  have third : ∃ k ∈ pureV d (m+g), k ≠ i ∧ k ≠ j := by
    by_contra bad
    have subset : pureV d (m+g) ⊆ ({i,j} : Set (Fin n)) := by
      intro k hk
      by_contra missing
      have ki : k ≠ i := fun eq => missing (by simp [eq])
      have kj : k ≠ j := fun eq => missing (by simp [eq])
      exact bad ⟨k,hk,ki,kj⟩
    have same : pureV d (m+g) = ({i} : Set (Fin n)) ∪ {j} := by
      ext k
      constructor
      · intro hk
        have h := subset hk
        simpa only [Set.mem_insert_iff, Set.mem_union, Set.mem_singleton_iff] using h
      · simp only [Set.mem_union, Set.mem_singleton_iff]
        rintro (rfl | rfl)
        · exact inI
        · exact inJ
    obtain ⟨a,ha,ea⟩ := atoms i
    obtain ⟨b,hb,eb⟩ := atoms j
    exact noUnionV ⟨a,ha,b,hb,by rw [ea,eb,same]⟩
  obtain ⟨k,inK,ki,kj⟩ := third
  refine ⟨g,hg,d,⟨{i,j,k}, by simp [ne,ki.symm,kj.symm], ?_⟩,noUnionV⟩
  intro u hu
  change u ∈ ({i,j,k} : Finset (Fin n)) at hu
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu
  rcases hu with rfl | rfl | rfl
  · exact inI
  · exact inJ
  · exact inK
