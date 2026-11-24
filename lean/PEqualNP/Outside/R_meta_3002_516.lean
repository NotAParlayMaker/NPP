import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3002_516
    (compile :
    ∀ (N s : ℕ) (F : ℕ → Set (Finset ℕ)),
    (∀ w < N+N, F w = {{w}}) →
    (∀ j < s, ∃ a < N+N+j, ∃ b < N+N+j,
      F (N+N+j) = Set.image2 (fun (u v : Finset ℕ) => u ∪ v) (F a) (F b) ∨
      F (N+N+j) = F a ∨ F (N+N+j) = {∅} ∨ F (N+N+j) = F a ∪ F b) →
    ∃ K : Finset (Fin N) → Finset (Fin N) → ℕ → Set (Fin N),
      (∀ X T (p : Fin N), K X T p.val = if p ∈ X then Set.univ else {p}) ∧
      (∀ X T (l : Fin N), K X T (N+l.val) = if l ∈ T then Set.univ else ∅) ∧
      (∀ j < s, ∃ a < N+N+j, ∃ b < N+N+j,
        (∀ X T, K X T (N+N+j) = K X T a ∪ K X T b) ∨
        (∀ X T, K X T (N+N+j) = K X T a) ∨
        (∀ X T, K X T (N+N+j) = ∅) ∨
        (∀ X T, K X T (N+N+j) = K X T a ∩ K X T b)) ∧
      ∀ X T w (p : Fin N), p ∈ K X T w ↔ ∀ A ∈ F w,
        (∀ x ∈ X, x.val ∉ A) → (∀ l ∈ T, N+l.val ∉ A) → p.val ∈ A)
    (bound :
    ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I], 200 ≤ q → N = q^2+q+1 →
      (∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q+1) →
      (∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l) →
      ∀ (s o : ℕ) (K : Finset (Fin N) → Finset (Fin N) → ℕ → Set (Fin N)), o < N+N+s →
      (∀ X T (p : Fin N), K X T p.val = if p ∈ X then Set.univ else {p}) →
      (∀ X T (l : Fin N), K X T (N+l.val) = if l ∈ T then Set.univ else ∅) →
      (∀ j < s, ∃ a < N+N+j, ∃ b < N+N+j,
        (∀ X T, K X T (N+N+j) = K X T a ∪ K X T b) ∨
        (∀ X T, K X T (N+N+j) = K X T a) ∨
        (∀ X T, K X T (N+N+j) = ∅) ∨
        (∀ X T, K X T (N+N+j) = K X T a ∩ K X T b)) →
      (∀ X T, (∃ p ∈ X, ∃ l ∈ T, I p l) → K X T o = Set.univ) →
      (∀ X T, T.card ≤ q → (¬∃ p ∈ X, ∃ l ∈ T, I p l) →
        K X T o = {p | ∃ l ∈ T, I p l}) → N*q ≤ 100*s) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3], (200 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) → ∀ (x9 x10 : ℕ) (x11 : ℕ → Set (Finset ℕ)), x10 < x2 + x2 + x9 → (∀ x13 < x2 + x2, x11 x13 = {{x13}}) → (∀ x14 < x9, ∃ x16 < x2 + x2 + x14, ∃ x17 < x2 + x2 + x14, x11 (x2 + x2 + x14) = Set.image2 (fun (x18 x19 : Finset ℕ) => x18 ∪ x19) (x11 x16) (x11 x17) ∨ x11 (x2 + x2 + x14) = x11 x16 ∨ x11 (x2 + x2 + x14) = {∅} ∨ x11 (x2 + x2 + x14) = x11 x16 ∪ x11 x17) → (∀ x15 ∈ x11 x10, ∀ (x17 x18 : Fin x2), x3 x17 x18 → ↑x17 ∈ x15 ∨ x2 + ↑x18 ∈ x15) → (∀ (x16 : Finset (Fin x2)), x16.card ≤ x1 → ∃ x18 ∈ x11 x10, ∀ (x19 : Fin x2), (↑x19 ∈ x18 ↔ ∃ x20 ∈ x16, x3 x19 x20) ∧ (x2 + ↑x19 ∈ x18 ↔ x19 ∉ x16)) → x2 * x1 ≤ (100 : ℕ) * x9 := by
  classical
  intro q N I decI hq hN hcard huniq s o F room inputs gates safe sat
  obtain ⟨K, Kpoints, Klines, Kgates, core⟩ := compile N s F inputs gates
  apply bound q N I hq hN hcard huniq s o K room Kpoints Klines Kgates
  · intro X T h
    obtain ⟨p,hp,l,hl,inc⟩ := h
    ext r
    refine ⟨fun _ => Set.mem_univ r, fun _ => ?_⟩
    apply (core X T o r).mpr
    intro A hA hx ht
    exact False.elim ((safe A hA p l inc).elim (hx p hp) (ht l hl))
  · intro X T hT hnone
    obtain ⟨A,hA,hAspec⟩ := sat T hT
    have hxA : ∀ p ∈ X, p.val ∉ A := by
      intro p hp hmem
      obtain ⟨l,hl,inc⟩ := (hAspec p).1.mp hmem
      exact hnone ⟨p,hp,l,hl,inc⟩
    have htA : ∀ l ∈ T, N+l.val ∉ A := by
      intro l hl hmem
      exact ((hAspec l).2.mp hmem) hl
    ext p
    change p ∈ K X T o ↔ ∃ l ∈ T, I p l
    rw [core X T o p]
    constructor
    · intro h
      exact (hAspec p).1.mp (h A hA hxA htA)
    · rintro ⟨l,hl,inc⟩ B hB _ ht
      exact (safe B hB p l inc).elim id (fun h => False.elim (ht l hl h))
