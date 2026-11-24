import Mathlib.Data.Fintype.Card
import Mathlib.Data.Set.Prod

theorem PEqualNP.Outside.R_meta_3002_727
    (splitGate : ∀ (A B : Set (Finset ℕ)) (X Y : Set ℕ),
      let live := fun (D : Set (Finset ℕ)) =>
        (∃ d ∈ D, ∀ v ∈ d, v ∈ X) ∧ (∀ d ∈ D, ∃ v ∈ d, v ∈ Y)
      live (Set.image2 (fun u v => u ∪ v) A B) ∨ live (A ∪ B) → live A ∨ live B)
    (pricing : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I],
      200 ≤ q → N = q^2+q+1 →
      (∀ l, Fintype.card {p : Fin N // I p l} = q+1) →
      (∀ p r : Fin N, p ≠ r → ∃! l, I p l ∧ I r l) →
      ∀ (s o : ℕ) (U : ℕ → Set (Finset (Fin N))) (V : ℕ → Set (Fin N × Fin N)),
      o < N+N+s →
      (∀ i < N+N, ∀ T p l, T ∈ U i → (p,l) ∈ V i →
        (i = p.val ∧ ∃ k ∈ T, I p k) ∨ (i = N+l.val ∧ l ∉ T)) →
      (∀ g < s, ∃ a < N+N+g, ∃ b < N+N+g,
        U (N+N+g) ×ˢ V (N+N+g) ⊆ (U a ×ˢ V a) ∪ (U b ×ˢ V b)) →
      (∀ T : Finset (Fin N), T.card ≤ q → T ∈ U o) →
      (∀ p l, I p l → (p,l) ∈ V o) → N*q ≤ 100*s) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3], (200 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) → ∀ (x9 x10 : ℕ) (x11 : ℕ → Set (Finset ℕ)), x10 < x2 + x2 + x9 → (∀ x13 < x2 + x2, x11 x13 = {{x13}}) → (∀ x14 < x9, ∃ x16 < x2 + x2 + x14, ∃ x17 < x2 + x2 + x14, x11 (x2 + x2 + x14) = Set.image2 (fun (x18 x19 : Finset ℕ) => x18 ∪ x19) (x11 x16) (x11 x17) ∨ x11 (x2 + x2 + x14) = x11 x16 ∨ x11 (x2 + x2 + x14) = {∅} ∨ x11 (x2 + x2 + x14) = x11 x16 ∪ x11 x17) → (∀ x15 ∈ x11 x10, ∀ (x17 x18 : Fin x2), x3 x17 x18 → ↑x17 ∈ x15 ∨ x2 + ↑x18 ∈ x15) → (∀ (x16 : Finset (Fin x2)), x16.card ≤ x1 → ∃ x18 ∈ x11 x10, ∀ (x19 : Fin x2), (↑x19 ∈ x18 ↔ ∃ x20 ∈ x16, x3 x19 x20) ∧ (x2 + ↑x19 ∈ x18 ↔ x19 ∉ x16)) → x2 * x1 ≤ (100 : ℕ) * x9 := by
  intro q N I inst hq hn lines joins s o F ho leaves gates sound saturated
  classical
  let X (T : Finset (Fin N)) : Set ℕ := {i |
    (∀ p : Fin N, i = p.val → ∃ k ∈ T, I p k) ∧
    (∀ l : Fin N, i = N+l.val → l ∉ T)}
  let Y (e : Fin N × Fin N) : Set ℕ := {e.1.val, N+e.2.val}
  let U (w : ℕ) : Set (Finset (Fin N)) := {T | ∃ d ∈ F w, ∀ v ∈ d, v ∈ X T}
  let V (w : ℕ) : Set (Fin N × Fin N) := {e | ∀ d ∈ F w, ∃ v ∈ d, v ∈ Y e}
  apply pricing q N I hq hn lines joins s o U V ho
  · intro i hi T p l ht he
    obtain ⟨d, hd, sub⟩ := ht
    rw [leaves i hi] at hd
    have eq : d = {i} := hd
    subst d
    have hx := sub i (by simp)
    obtain ⟨v, hv, hy⟩ := he {i} (by rw [leaves i hi]; exact Set.mem_singleton _)
    have ev : v = i := by simpa using hv
    subst v
    rcases (show i = p.val ∨ i = N+l.val from hy) with h | h
    · exact Or.inl ⟨h, hx.1 p h⟩
    · exact Or.inr ⟨h, hx.2 l h⟩
  · intro g hg
    obtain ⟨a, ha, b, hb, hop⟩ := gates g hg
    refine ⟨a, ha, b, hb, ?_⟩
    rintro ⟨T,e⟩ ⟨ht, he⟩
    let live := fun (D : Set (Finset ℕ)) =>
      (∃ d ∈ D, ∀ v ∈ d, v ∈ X T) ∧ (∀ d ∈ D, ∃ v ∈ d, v ∈ Y e)
    have good : live (F (N+N+g)) := ⟨ht, he⟩
    change live (F a) ∨ live (F b)
    rcases hop with mul | copy | unit | add
    · exact splitGate (F a) (F b) (X T) (Y e) (Or.inl (mul ▸ good))
    · exact Or.inl (copy ▸ good)
    · obtain ⟨v,hv,_⟩ := good.2 ∅ (by rw [unit]; exact Set.mem_singleton _)
      simp at hv
    · exact splitGate (F a) (F b) (X T) (Y e) (Or.inr (add ▸ good))
  · intro T hT
    obtain ⟨d,hd,hmem⟩ := saturated T hT
    refine ⟨d,hd,?_⟩
    intro v hv
    exact ⟨fun p h => (hmem p).1.mp (h ▸ hv), fun l h => (hmem l).2.mp (h ▸ hv)⟩
  · intro p l hI d hd
    rcases sound d hd p l hI with hp | hl
    · exact ⟨p.val,hp,Or.inl rfl⟩
    · exact ⟨N+l.val,hl,Or.inr rfl⟩
