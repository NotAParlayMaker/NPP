import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3254_1
    (freshPoint : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I],
      (∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q + 1) →
      (∀ a b : Fin N, a ≠ b → ∃! l : Fin N, I a l ∧ I b l) →
      ∀ T : Finset (Fin N), T.card ≤ q → ∀ l : Fin N, l ∉ T →
        ∃ p : Fin N, I p l ∧ ∀ k ∈ T, ¬ I p k)
    (coverBound : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I], 200 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q + 1) →
      (∀ a b : Fin N, a ≠ b → ∃! l : Fin N, I a l ∧ I b l) →
      ∀ (s o : ℕ) (F : ℕ → Set (Finset ℕ)), o < N + N + s →
      (∀ v < N + N, F v = {{v}}) →
      (∀ g < s, ∃ a < N + N + g, ∃ b < N + N + g,
        F (N + N + g) = Set.image2 (· ∪ ·) (F a) (F b) ∨ F (N + N + g) = F a ∨
        F (N + N + g) = {∅} ∨ F (N + N + g) = F a ∪ F b) →
      (∀ A ∈ F o, ∀ p l : Fin N, I p l → p.val ∈ A ∨ N + l.val ∈ A) →
      (∀ T : Finset (Fin N), T.card ≤ q → ∃ A ∈ F o, ∀ p : Fin N,
        (p.val ∈ A ↔ ∃ l ∈ T, I p l) ∧ (N + p.val ∈ A ↔ p ∉ T)) →
      N * q ≤ 100 * s) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3],   (100 : ℕ) < x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) →         (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) →           ∀ (x9 x10 : ℕ) (x11 : ℕ → Set ((Fin x2 → Bool) × (Fin x2 → Bool))),             have x12 : ℕ := x2 + x2;             have x13 : Fin x2 → Fin x2 → Bool := fun (x13 x14 : Fin x2) => Decidable.decide (x14 = x13);             x10 < x12 + x9 → (∀ (x15 : Fin x2), x11 ↑x15 = {x16 : (Fin x2 → Bool) × (Fin x2 → Bool) | x16.1 x15 = Bool.true} ∧ x11 (x2 + ↑x15) = {x16 : (Fin x2 → Bool) × (Fin x2 → Bool) | x16.2 x15 = Bool.true}) → (∀ x16 < x9, ∃ (x18 : ℕ) (x19 : ℕ), Max.max x18 x19 < x12 + x16 ∧ x11 (x12 + x16) ∈ [x11 x18 ∪ x11 x19, x11 x18, ∅, x11 x18 ∩ x11 x19]) → (∀ (x17 x18 : Fin x2), x3 x17 x18 → (x13 x17, x13 x18) ∈ x11 x10) → (∀ (x18 : Fin x2 → Bool), Fintype.card { x19 : Fin x2 // x18 x19 = Bool.true } ≤ x1 → (fun (x20 : Fin x2) => Decidable.decide ¬∃ (x21 : Fin x2), x3 x20 x21 ∧ x18 x21 = Bool.true, x18) ∉ x11 x10) → {x19 : Fin x2 × Fin x2 | x3 x19.1 x19.2 ∧ ∃ x20 < x9, x11 (x12 + x20) ⊆ x11 x10 ∧ (x13 x19.1, x13 x19.2) ∈ x11 (x12 + x20) ∧ ∃ (x21 : ℕ) (x22 : ℕ), Max.max x21 x22 < x12 + x20 ∧ x11 (x12 + x20) = x11 x21 ∩ x11 x22 ∧ ∃ (x23 : Set (Fin x2 → Bool)) (x24 : Set (Fin x2 → Bool)), x11 x21 = x23 ×ˢ Set.univ ∧ x11 x22 = Set.univ ×ˢ x24}.ncard ≤ (4 : ℕ) * x9 → x2 * x1 ≤ (100 : ℕ) * x9 := by
  classical
  intro q N I inst hq hN hdegree hunique s o W
  dsimp only
  intro ho hbase hstep hpos hneg _hclean
  have hN' : N = q ^ 2 + q + 1 := by simpa using hN
  obtain ⟨F, hFbase, hFstep, hFcert⟩ := _certificates ((Fin N → Bool) × (Fin N → Bool)) (N + N) s W (by
    intro g hg
    obtain ⟨a, b, hmax, law⟩ := hstep g hg
    obtain ⟨ha, hb⟩ := max_lt_iff.mp hmax
    refine ⟨a, ha, b, hb, ?_⟩
    simpa only [List.mem_cons, List.mem_nil_iff, or_false] using law)
  have inputs := hbase
  have leaves : ∀ v < N + N, F v = {{v}} := hFbase
  have gates := hFstep
  have cover : ∀ A ∈ F o, ∀ p l : Fin N, I p l → p.val ∈ A ∨ N + l.val ∈ A := by
    intro A hA p l hpl
    by_contra hcon
    push_neg at hcon
    have hz : (fun u : Fin N => decide (u = p), fun u : Fin N => decide (u = l)) ∈ W o :=
      hpos p l hpl
    have hno : ¬ ∀ v ∈ A,
        (fun u : Fin N => decide (u = p), fun u : Fin N => decide (u = l)) ∉ W v := by
      intro hall
      exact ((hFcert o ho).2 _).mpr ⟨A, hA, hall⟩ hz
    push_neg at hno
    obtain ⟨v, hvA, hvz⟩ := hno
    have hvlt : v < N + N := (hFcert o ho).1 A hA v hvA
    rcases Nat.lt_or_ge v N with hv | hv
    · have hbv : W v = {z : (Fin N → Bool) × (Fin N → Bool) | z.1 ⟨v, hv⟩ = true} := by
        simpa using (inputs ⟨v, hv⟩).1
      rw [hbv] at hvz
      simp only [Set.mem_setOf_eq] at hvz
      have e : (⟨v, hv⟩ : Fin N) = p := of_decide_eq_true hvz
      exact hcon.1 (by rwa [← e])
    · obtain ⟨k, hk⟩ : ∃ k, v = N + k := ⟨v - N, by omega⟩
      have hklt : k < N := by omega
      have hbv : W (N + k) = {z : (Fin N → Bool) × (Fin N → Bool) | z.2 ⟨k, hklt⟩ = true} := by
        simpa using (inputs ⟨k, hklt⟩).2
      rw [hk, hbv] at hvz
      simp only [Set.mem_setOf_eq] at hvz
      have e : (⟨k, hklt⟩ : Fin N) = l := of_decide_eq_true hvz
      exact hcon.2 (by rwa [← e, ← hk])
  have saturated : ∀ T : Finset (Fin N), T.card ≤ q → ∃ A ∈ F o, ∀ p : Fin N,
      (p.val ∈ A ↔ ∃ l ∈ T, I p l) ∧ (N + p.val ∈ A ↔ p ∉ T) := by
    intro T ht
    have fresh : ∀ l : Fin N, l ∉ T → ∃ p : Fin N, I p l ∧ ∀ k ∈ T, ¬ I p k :=
      freshPoint q N I hdegree hunique T ht
    let y : Fin N → Bool := fun l => decide (l ∈ T)
    let x : Fin N → Bool := fun p => decide (¬ ∃ l : Fin N, I p l ∧ y l = true)
    have cy : Fintype.card {l : Fin N // y l = true} ≤ q := by
      simpa [Fintype.card_subtype, y] using ht
    obtain ⟨A, hA, zero⟩ := ((hFcert o ho).2 (x, y)).mp (hneg y cy)
    have pl : ∀ (p : Fin N), p.val ∈ A → ∃ l ∈ T, I p l := by
      intro p h
      have hh := zero p.val h
      rw [(inputs p).1] at hh
      change ¬ x p = true at hh
      simpa [x, y, and_comm] using hh
    have ln : ∀ (l : Fin N), N + l.val ∈ A → l ∉ T := by
      intro l h
      have hh := zero _ h
      rw [(inputs l).2] at hh
      exact fun m => hh (show y l = true from decide_eq_true m)
    refine ⟨A, hA, fun p => ⟨⟨pl p, ?_⟩, ⟨ln p, ?_⟩⟩⟩
    · rintro ⟨l, hl, inc⟩
      exact (cover A hA p l inc).resolve_right (fun bad => ln l bad hl)
    · intro hp
      obtain ⟨a, ha, avoid⟩ := fresh p hp
      apply (cover A hA a p ha).resolve_left
      intro bad
      obtain ⟨l, hl, inc⟩ := pl a bad
      exact avoid l hl inc
  by_cases large : 200 ≤ q
  · exact coverBound q N I large hN' hdegree hunique s o F ho leaves gates cover saturated
  have propagate (g : ℕ) (hg : g < s) : ∃ a < N + N + g, ∃ b < N + N + g,
      ∀ A ∈ F (N + N + g), ∀ v ∈ A, ∃ B, (B ∈ F a ∨ B ∈ F b) ∧ v ∈ B := by
    obtain ⟨a, ha, b, hb, law⟩ := gates g hg
    refine ⟨a, ha, b, hb, ?_⟩
    intro A hA v hv
    rcases law with join | copy | empty | meet
    · rw [join] at hA
      obtain ⟨U, hU, V, hV, rfl⟩ := hA
      exact (Finset.mem_union.mp hv).elim (fun h => ⟨U, Or.inl hU, h⟩) (fun h => ⟨V, Or.inr hV, h⟩)
    · exact ⟨A, Or.inl (copy ▸ hA), hv⟩
    · have e : A = ∅ := Set.mem_singleton_iff.mp (empty ▸ hA)
      exact False.elim (Finset.notMem_empty _ (e ▸ hv))
    · rw [meet] at hA
      exact ⟨A, hA, hv⟩
  have reach (k : ℕ) (hk : k ≤ s) (R : Finset ℕ) (hw : ∀ w ∈ R, w < N + N + k) :
      ∃ S : Finset ℕ, S.card ≤ R.card + k ∧ ∀ w ∈ R, ∀ A ∈ F w, A ⊆ S := by
    induction k generalizing R with
    | zero =>
      refine ⟨R, by omega, ?_⟩
      intro w mem A cert
      rw [leaves w (by simpa using hw w mem)] at cert
      have : A = {w} := Set.mem_singleton_iff.mp cert
      simpa [this] using mem
    | succ k ih =>
      let w := N + N + k
      by_cases use : w ∈ R
      · obtain ⟨a, ha, b, hb, parent⟩ := propagate k (by omega)
        let U := insert a (insert b (R.erase w))
        have bounds : ∀ u ∈ U, u < w := by
          intro u hu
          rcases Finset.mem_insert.mp hu with rfl | h
          · exact ha
          rcases Finset.mem_insert.mp h with rfl | h
          · exact hb
          obtain ⟨ne, inc⟩ := Finset.mem_erase.mp h
          have bound := hw u inc
          change u ≠ N + N + k at ne
          change u < N + N + k
          omega
        obtain ⟨S, c, dep⟩ := ih (by omega) U bounds
        have uc : U.card ≤ R.card + 1 := by
          have c1 := Finset.card_insert_le a (insert b (R.erase w))
          have c2 := Finset.card_insert_le b (R.erase w)
          rw [Finset.card_erase_of_mem use] at c2
          have := Finset.card_pos.mpr ⟨_, use⟩
          dsimp [U]
          omega
        refine ⟨S, by omega, ?_⟩
        intro u hu A cert v hv
        by_cases eq : u = w
        · subst u
          obtain ⟨B, anc, hv'⟩ := parent A cert v hv
          rcases anc with h | h
          · exact dep a (by simp [U]) B h hv'
          · exact dep b (by simp [U]) B h hv'
        · exact dep u (by simp [U, eq, hu]) A cert hv
      · have bounds : ∀ u ∈ R, u < w := by
          intro u hu
          have ne : u ≠ w := fun eq => use (eq ▸ hu)
          have bound := hw u hu
          change u ≠ N + N + k at ne
          change u < N + N + k
          omega
        obtain ⟨S, c, h⟩ := ih (by omega) R bounds
        exact ⟨S, by omega, h⟩
  obtain ⟨S, card, dep⟩ := reach s le_rfl {o} (by simpa using ho)
  have allBits : Finset.range (N + N) ⊆ S := by
    intro v hv
    have bound := Finset.mem_range.mp hv
    by_cases point : v < N
    · let p : Fin N := ⟨v, point⟩
      have big : 2 ≤ N := by nlinarith [Nat.zero_le (q ^ 2)]
      let p' : Fin N := if p.val = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩
      have ne : p ≠ p' := by
        intro e
        have eq := congrArg Fin.val e
        unfold p' at eq
        split at eq
        · change p.val = 1 at eq
          omega
        · change p.val = 0 at eq
          contradiction
      obtain ⟨l, hl, _⟩ := hunique p p' ne
      obtain ⟨A, hA, eq⟩ := saturated {l} (by simp; omega)
      exact dep o (by simp) A hA ((eq p).1.mpr ⟨l, by simp, hl.1⟩)
    · let l : Fin N := ⟨v - N, by omega⟩
      obtain ⟨A, hA, eq⟩ := saturated ∅ (by simp)
      have inc := dep o (by simp) A hA ((eq l).2.mpr (by simp))
      have e : N + l.val = v := by dsimp [l]; omega
      exact e ▸ inc
  have count := Finset.card_le_card allBits
  simp only [Finset.card_range] at count
  simp only [Finset.card_singleton] at card
  have qmax : q ≤ 199 := by omega
  have hmul := Nat.mul_le_mul_left N qmax
  have nn : 100 ≤ N := by nlinarith [Nat.zero_le (q ^ 2)]
  omega
where
 _certificates : ∀ (Z : Type) (m s : ℕ) (X : ℕ → Set Z),
     (∀ g < s, ∃ a < m + g, ∃ b < m + g,
       X (m + g) = X a ∪ X b ∨ X (m + g) = X a ∨ X (m + g) = ∅ ∨ X (m + g) = X a ∩ X b) →
     ∃ F : ℕ → Set (Finset ℕ), (∀ v < m, F v = {{v}}) ∧
       (∀ g < s, ∃ a < m + g, ∃ b < m + g,
         F (m + g) = Set.image2 (· ∪ ·) (F a) (F b) ∨ F (m + g) = F a ∨
         F (m + g) = {∅} ∨ F (m + g) = F a ∪ F b) ∧
       ∀ w < m + s, (∀ A ∈ F w, ∀ v ∈ A, v < m) ∧
         ∀ z, z ∉ X w ↔ ∃ A ∈ F w, ∀ v ∈ A, z ∉ X v := by
  classical
  intro Z m s X steps
  let ga : ℕ → ℕ := fun g => if h : g < s then Classical.choose (steps g h) else 0
  let gb : ℕ → ℕ := fun g => if h : g < s then Classical.choose (Classical.choose_spec (steps g h)).2 else 0
  have gha : ∀ g (h : g < s), ga g < m + g := by
    intro g h
    simp only [ga, dif_pos h]
    exact (Classical.choose_spec (steps g h)).1
  have ghb : ∀ g (h : g < s), gb g < m + g := by
    intro g h
    simp only [gb, dif_pos h]
    exact (Classical.choose_spec (Classical.choose_spec (steps g h)).2).1
  have glaw : ∀ g (h : g < s),
      X (m + g) = X (ga g) ∪ X (gb g) ∨ X (m + g) = X (ga g) ∨
        X (m + g) = ∅ ∨ X (m + g) = X (ga g) ∩ X (gb g) := by
    intro g h
    simp only [ga, gb, dif_pos h]
    exact (Classical.choose_spec (Classical.choose_spec (steps g h)).2).2
  let step : (w : ℕ) → ((v : ℕ) → v < w → Set (Finset ℕ)) → Set (Finset ℕ) :=
    fun w rec =>
      if hw : w < m then {{w}}
      else if h : w - m < s then
        if h0 : X w = ∅ then {∅}
        else if h1 : X w = X (ga (w - m)) then rec (ga (w - m)) (by have := gha (w - m) h; omega)
        else if h2 : X w = X (ga (w - m)) ∪ X (gb (w - m)) then
          Set.image2 (· ∪ ·) (rec (ga (w - m)) (by have := gha (w - m) h; omega))
            (rec (gb (w - m)) (by have := ghb (w - m) h; omega))
        else rec (ga (w - m)) (by have := gha (w - m) h; omega) ∪
          rec (gb (w - m)) (by have := ghb (w - m) h; omega)
      else ∅
  let F : ℕ → Set (Finset ℕ) := Nat.strongRec step
  have F_eq : ∀ w, F w = step w (fun v _ => F v) := by
    intro w
    exact Nat.strongRec_eq step w
  have Fbase : ∀ v < m, F v = {{v}} := by
    intro v hv
    rw [F_eq v]
    dsimp only [step]
    rw [dif_pos hv]
  have Fstep : ∀ g < s, ∃ a < m + g, ∃ b < m + g,
      F (m + g) = Set.image2 (· ∪ ·) (F a) (F b) ∨ F (m + g) = F a ∨
        F (m + g) = {∅} ∨ F (m + g) = F a ∪ F b := by
    intro g hg
    have hge : ¬ (m + g < m) := by omega
    have hgs : m + g - m < s := by omega
    have hsub : m + g - m = g := by omega
    refine ⟨ga g, gha g hg, gb g, ghb g hg, ?_⟩
    rw [F_eq (m + g)]
    dsimp only [step]
    rw [dif_neg hge, dif_pos hgs, hsub]
    by_cases h0 : X (m + g) = ∅
    · rw [dif_pos h0]
      exact Or.inr (Or.inr (Or.inl rfl))
    · rw [dif_neg h0]
      by_cases h1 : X (m + g) = X (ga g)
      · rw [dif_pos h1]
        exact Or.inr (Or.inl rfl)
      · rw [dif_neg h1]
        by_cases h2 : X (m + g) = X (ga g) ∪ X (gb g)
        · rw [dif_pos h2]
          exact Or.inl rfl
        · rw [dif_neg h2]
          exact Or.inr (Or.inr (Or.inr rfl))
  have Fcert : ∀ w < m + s, (∀ A ∈ F w, ∀ v ∈ A, v < m) ∧
      ∀ z, z ∉ X w ↔ ∃ A ∈ F w, ∀ v ∈ A, z ∉ X v := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw
      by_cases hwm : w < m
      · have hFw : F w = {{w}} := Fbase w hwm
        constructor
        · intro A hA v hv
          rw [hFw] at hA
          have hA' : A = {w} := Set.mem_singleton_iff.mp hA
          subst hA'
          rw [Finset.mem_singleton] at hv
          exact hv ▸ hwm
        · intro z
          rw [hFw]
          simp
      · have hgs : w - m < s := by omega
        have hFw : F w = step w (fun v _ => F v) := F_eq w
        rw [hFw]
        dsimp only [step]
        rw [dif_neg hwm, dif_pos hgs]
        have ha : ga (w - m) < w := by
          have := gha (w - m) hgs
          omega
        have hb : gb (w - m) < w := by
          have := ghb (w - m) hgs
          omega
        have iha := ih (ga (w - m)) ha (by omega)
        have ihb := ih (gb (w - m)) hb (by omega)
        by_cases h0 : X w = ∅
        · rw [dif_pos h0]
          constructor
          · intro A hA v hv
            have hA' : A = ∅ := Set.mem_singleton_iff.mp hA
            subst hA'
            exact absurd hv (Finset.notMem_empty v)
          · intro z
            rw [h0]
            simp
        · rw [dif_neg h0]
          by_cases h1 : X w = X (ga (w - m))
          · rw [dif_pos h1]
            constructor
            · intro A hA v hv
              exact iha.1 A hA v hv
            · intro z
              rw [h1]
              exact iha.2 z
          · rw [dif_neg h1]
            by_cases h2 : X w = X (ga (w - m)) ∪ X (gb (w - m))
            · rw [dif_pos h2]
              constructor
              · intro C hC v hv
                obtain ⟨A, hA, B, hB, rfl⟩ := Set.mem_image2.mp hC
                rcases Finset.mem_union.mp hv with h | h
                · exact iha.1 A hA v h
                · exact ihb.1 B hB v h
              · intro z
                rw [h2]
                constructor
                · intro hz
                  have hza : z ∉ X (ga (w - m)) := fun h' => hz (Set.mem_union_left _ h')
                  have hzb : z ∉ X (gb (w - m)) := fun h' => hz (Set.mem_union_right _ h')
                  obtain ⟨A, hA, hAZ⟩ := (iha.2 z).mp hza
                  obtain ⟨B, hB, hBZ⟩ := (ihb.2 z).mp hzb
                  refine ⟨A ∪ B, Set.mem_image2.mpr ⟨A, hA, B, hB, rfl⟩, ?_⟩
                  intro v hv
                  rcases Finset.mem_union.mp hv with h | h
                  · exact hAZ v h
                  · exact hBZ v h
                · rintro ⟨C, hC, hCZ⟩ hxw
                  obtain ⟨A, hA, B, hB, rfl⟩ := Set.mem_image2.mp hC
                  rw [Set.mem_union] at hxw
                  rcases hxw with h | h
                  · exact (iha.2 z).mpr ⟨A, hA, fun v hv => hCZ v (Finset.mem_union.mpr (Or.inl hv))⟩ h
                  · exact (ihb.2 z).mpr ⟨B, hB, fun v hv => hCZ v (Finset.mem_union.mpr (Or.inr hv))⟩ h
            · rw [dif_neg h2]
              have hmw : m + (w - m) = w := by omega
              have h3 : X w = X (ga (w - m)) ∩ X (gb (w - m)) := by
                rcases glaw (w - m) hgs with h | h | h | h
                · exact absurd (by simpa [hmw] using h) h2
                · exact absurd (by simpa [hmw] using h) h1
                · exact absurd (by simpa [hmw] using h) h0
                · simpa [hmw] using h
              constructor
              · intro C hC v hv
                rw [Set.mem_union] at hC
                rcases hC with h | h
                · exact iha.1 C h v hv
                · exact ihb.1 C h v hv
              · intro z
                rw [h3, Set.mem_inter_iff, not_and_or]
                constructor
                · rintro (h | h)
                  · obtain ⟨A, hA, hAZ⟩ := (iha.2 z).mp h
                    exact ⟨A, Set.mem_union_left _ hA, hAZ⟩
                  · obtain ⟨B, hB, hBZ⟩ := (ihb.2 z).mp h
                    exact ⟨B, Set.mem_union_right _ hB, hBZ⟩
                · rintro ⟨C, hC, hCZ⟩
                  rw [Set.mem_union] at hC
                  rcases hC with h | h
                  · exact Or.inl ((iha.2 z).mpr ⟨C, h, hCZ⟩)
                  · exact Or.inr ((ihb.2 z).mpr ⟨C, h, hCZ⟩)
  exact ⟨F, Fbase, Fstep, Fcert⟩
