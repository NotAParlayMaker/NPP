import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_3576_17
    (h3 : ∀ (n k : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (side : Fin n → Bool) (I : Fin k → Finset (Fin n)) (V : Finset (Fin n)), (∀ a b : Fin n, G.Adj a b → side a ≠ side b) → (∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) → 2 ≤ k → (∀ j : Fin k, ∀ a ∈ I j, ∀ b ∈ I j, ¬ G.Adj a b) → (∀ v : Fin n, ∃ j : Fin k, v ∈ I j) → (∀ v : Fin n, ∃ j : Fin k, v ∉ I j) → (∀ j : Fin k, (I j).card + 2 ≤ n) → (∀ a b : Fin n, a ≠ b → ¬ G.Adj a b → ∃ j : Fin k, a ∈ I j ∧ b ∈ I j) → (∀ v ∈ V, 3 ≤ (V.filter (fun u => G.Adj v u)).card) → (∃ v ∈ V, (V.filter (fun u => G.Adj v u)).card = 3) → ∃ z ∈ V, (V.filter (fun u => G.Adj z u)).card + 1 ≤ (Finset.univ.filter (fun j => z ∉ I j)).card)
    (h4 : ∀ (n k : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (side : Fin n → Bool) (I : Fin k → Finset (Fin n)) (V : Finset (Fin n)), (∀ a b : Fin n, G.Adj a b → side a ≠ side b) → (∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) → 2 ≤ k → (∀ j : Fin k, ∀ a ∈ I j, ∀ b ∈ I j, ¬ G.Adj a b) → (∀ v : Fin n, ∃ j : Fin k, v ∈ I j) → (∀ v : Fin n, ∃ j : Fin k, v ∉ I j) → (∀ j : Fin k, (I j).card + 2 ≤ n) → (∀ a b : Fin n, a ≠ b → ¬ G.Adj a b → ∃ j : Fin k, a ∈ I j ∧ b ∈ I j) → (∀ v ∈ V, 4 ≤ (V.filter (fun u => G.Adj v u)).card) → ∃ z ∈ V, (V.filter (fun u => G.Adj z u)).card + 1 ≤ (Finset.univ.filter (fun j => z ∉ I j)).card) :
    ∀ (n k : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (side : Fin n → Bool) (I : Fin k → Finset (Fin n)), (∀ a b : Fin n, G.Adj a b → side a ≠ side b) → (∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) → 2 ≤ k → (∀ j : Fin k, ∀ a ∈ I j, ∀ b ∈ I j, ¬ G.Adj a b) → (∀ v : Fin n, ∃ j : Fin k, v ∈ I j) → (∀ v : Fin n, ∃ j : Fin k, v ∉ I j) → (∀ j : Fin k, (I j).card + 2 ≤ n) → (∀ a b : Fin n, a ≠ b → ¬ G.Adj a b → ∃ j : Fin k, a ∈ I j ∧ b ∈ I j) → ∃ T : Finset (Fin n), (∀ a b : Fin n, G.Adj a b → a ∈ T ∨ b ∈ T) ∧ G.edgeFinset.card + T.card + 1 ≤ ∑ j : Fin k, (n - (I j).card) := by
  intro n k G _ side I hbip hc4 hk hind hin hout hsize hpair
  have KL : ∀ V : Finset (Fin n), V.Nonempty → (∀ v ∈ V, 2 ≤ (V.filter (fun u => G.Adj v u)).card) →
      ∃ z ∈ V, (V.filter (fun u => G.Adj z u)).card + 1 ≤ (Finset.univ.filter (fun j => z ∉ I j)).card := by
    intro V hV hmin
    by_cases h2 : ∃ v ∈ V, (V.filter (fun u => G.Adj v u)).card = 2
    · obtain ⟨v, hv, hd⟩ := h2
      refine ⟨v, hv, ?_⟩
      rw [hd]
      obtain ⟨u1, u2, hne, heq⟩ := Finset.card_eq_two.mp hd
      have hu1 : u1 ∈ V.filter (fun u => G.Adj v u) := by rw [heq]; simp
      have hu2 : u2 ∈ V.filter (fun u => G.Adj v u) := by rw [heq]; simp
      simp only [Finset.mem_filter] at hu1 hu2
      have hw : ∀ u ∈ V, ∃ w, G.Adj u w ∧ w ≠ v := by
        intro u hu
        obtain ⟨w, hw, hwv⟩ := Finset.exists_mem_ne (s := V.filter (fun x => G.Adj u x)) (by have := hmin u hu; omega) v
        exact ⟨w, (Finset.mem_filter.mp hw).2, hwv⟩
      obtain ⟨w1, hw1, hw1v⟩ := hw u1 hu1.1
      obtain ⟨w2, hw2, hw2v⟩ := hw u2 hu2.1
      have nadj12 : ¬ G.Adj u1 u2 := by
        intro h
        have a1 := hbip v u1 hu1.2
        have a2 := hbip v u2 hu2.2
        have a3 := hbip u1 u2 h
        revert a1 a2 a3
        cases side v <;> cases side u1 <;> cases side u2 <;> simp
      obtain ⟨j12, h12a, h12b⟩ := hpair u1 u2 hne nadj12
      have nw1 : ¬ G.Adj w1 u2 := fun h => hc4 v u1 w1 u2 (Ne.symm hw1v) hne ⟨hu1.2, hw1, h, G.adj_symm hu2.2⟩
      have w1ne : w1 ≠ u2 := by rintro rfl; exact nadj12 hw1
      obtain ⟨ja, hja1, hja2⟩ := hpair w1 u2 w1ne nw1
      have nw2 : ¬ G.Adj w2 u1 := fun h => hc4 v u2 w2 u1 (Ne.symm hw2v) (Ne.symm hne) ⟨hu2.2, hw2, h, G.adj_symm hu1.2⟩
      have w2ne : w2 ≠ u1 := by rintro rfl; exact nadj12 (G.adj_symm hw2)
      obtain ⟨jb, hjb1, hjb2⟩ := hpair w2 u1 w2ne nw2
      have v12 : v ∉ I j12 := fun h => hind j12 v h u1 h12a hu1.2
      have va : v ∉ I ja := fun h => hind ja v h u2 hja2 hu2.2
      have vb : v ∉ I jb := fun h => hind jb v h u1 hjb2 hu1.2
      have u1a : u1 ∉ I ja := fun h => hind ja u1 h w1 hja1 hw1
      have u2b : u2 ∉ I jb := fun h => hind jb u2 h w2 hjb1 hw2
      have d1 : j12 ≠ ja := fun h => u1a (h ▸ h12a)
      have d2 : j12 ≠ jb := fun h => u2b (h ▸ h12b)
      have d3 : ja ≠ jb := fun h => u2b (h ▸ hja2)
      have hsub : ({j12, ja, jb} : Finset (Fin k)) ⊆ Finset.univ.filter (fun j => v ∉ I j) := by
        intro j hj
        simp only [Finset.mem_insert, Finset.mem_singleton] at hj
        rcases hj with rfl | rfl | rfl <;> simp [*]
      have hc3 : ({j12, ja, jb} : Finset (Fin k)).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp [d1, d2]), Finset.card_pair d3]
      have := Finset.card_le_card hsub
      omega
    · push Not at h2
      have h3' : ∀ v ∈ V, 3 ≤ (V.filter (fun u => G.Adj v u)).card := fun v hv => by
        have := hmin v hv; have := h2 v hv; omega
      by_cases e3 : ∃ v ∈ V, (V.filter (fun u => G.Adj v u)).card = 3
      · exact h3 n k G side I V hbip hc4 hk hind hin hout hsize hpair h3' e3
      · push Not at e3
        exact h4 n k G side I V hbip hc4 hk hind hin hout hsize hpair (fun v hv => by
          have := h3' v hv; have := e3 v hv; omega)
  have STEP : ∀ (V : Finset (Fin n)) (z : Fin n), z ∈ V →
      (∑ v ∈ V, (V.filter (fun u => G.Adj v u)).card) =
        (∑ v ∈ V.erase z, ((V.erase z).filter (fun u => G.Adj v u)).card) + 2 * (V.filter (fun u => G.Adj z u)).card := by
    intro V z hz
    rw [← Finset.add_sum_erase V _ hz]
    have h1 : ∀ v ∈ V.erase z, (V.filter (fun u => G.Adj v u)).card =
        ((V.erase z).filter (fun u => G.Adj v u)).card + (if G.Adj v z then 1 else 0) := by
      intro v hv
      conv_lhs => rw [← Finset.insert_erase hz]
      rw [Finset.filter_insert]
      split_ifs with h
      · rw [Finset.card_insert_of_notMem (by simp)]
      · simp
    rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, Finset.sum_boole]
    have h2 : ((V.erase z).filter (fun v => G.Adj v z)) = V.filter (fun u => G.Adj z u) := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨⟨_, hu⟩, ha⟩; exact ⟨hu, G.adj_symm ha⟩
      · rintro ⟨hu, ha⟩; exact ⟨⟨fun h => G.irrefl (h ▸ ha), hu⟩, G.adj_symm ha⟩
    rw [h2]
    simp only [Nat.cast_id]
    ring
  have MAIN : ∀ m : ℕ, ∀ V : Finset (Fin n), V.card = m → V.Nonempty →
      (∑ v ∈ V, (V.filter (fun u => G.Adj v u)).card) + 2 ≤
        2 * ∑ v ∈ V, max 1 ((Finset.univ.filter (fun j => v ∉ I j)).card - 1) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro V hVc hV
      have hz : ∃ z ∈ V, (V.filter (fun u => G.Adj z u)).card ≤
          max 1 ((Finset.univ.filter (fun j => z ∉ I j)).card - 1) := by
        by_cases hl : ∃ z ∈ V, (V.filter (fun u => G.Adj z u)).card ≤ 1
        · obtain ⟨z, hz, hd⟩ := hl
          exact ⟨z, hz, le_trans hd (le_max_left _ _)⟩
        · push Not at hl
          obtain ⟨z, hz, hd⟩ := KL V hV (fun v hv => hl v hv)
          exact ⟨z, hz, le_trans (Nat.le_sub_one_of_lt (Nat.lt_of_succ_le hd)) (le_max_right _ _)⟩
      obtain ⟨z, hzV, hzd⟩ := hz
      rw [STEP V z hzV, ← Finset.add_sum_erase V _ hzV]
      by_cases hs : V.erase z = ∅
      · rw [hs]
        simp only [Finset.sum_empty]
        have : V.filter (fun u => G.Adj z u) = ∅ := by
          rcases (Finset.erase_eq_empty_iff V z).mp hs with h | h
          · exact absurd h (Finset.nonempty_iff_ne_empty.mp hV)
          · rw [h]; ext u; simp only [Finset.mem_filter, Finset.mem_singleton]
            constructor
            · rintro ⟨rfl, ha⟩; exact absurd ha (G.irrefl)
            · simp
        rw [this, Finset.card_empty]
        have := le_max_left 1 ((Finset.univ.filter (fun j => z ∉ I j)).card - 1)
        omega
      · have hne : (V.erase z).Nonempty := Finset.nonempty_iff_ne_empty.mpr hs
        have hlt : (V.erase z).card < m := by rw [← hVc]; exact Finset.card_erase_lt_of_mem hzV
        have IH := ih _ hlt (V.erase z) rfl hne
        omega
  have n2 : 2 ≤ n := by have := hsize ⟨0, by omega⟩; omega
  have M := MAIN n Finset.univ (by simp) ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  have hdeg : (∑ v ∈ (Finset.univ : Finset (Fin n)), ((Finset.univ : Finset (Fin n)).filter (fun u => G.Adj v u)).card) = 2 * G.edgeFinset.card := by
    rw [← G.sum_degrees_eq_twice_card_edges]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    rw [← G.card_neighborFinset_eq_degree, G.neighborFinset_eq_filter]
  rw [hdeg] at M
  have cpos : ∀ v : Fin n, 1 ≤ (Finset.univ.filter (fun j => v ∉ I j)).card := by
    intro v
    obtain ⟨j, hj⟩ := hout v
    exact Finset.card_pos.mpr ⟨j, by simp [hj]⟩
  refine ⟨Finset.univ.filter (fun v => 2 ≤ (Finset.univ.filter (fun j => v ∉ I j)).card), ?_, ?_⟩
  · intro a b hab
    by_contra hcon
    push Not at hcon
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hcon
    have ca : (Finset.univ.filter (fun j => a ∉ I j)).card = 1 := by have := cpos a; omega
    have cb : (Finset.univ.filter (fun j => b ∉ I j)).card = 1 := by have := cpos b; omega
    obtain ⟨j0, hj0⟩ := Finset.card_eq_one.mp ca
    obtain ⟨j1, hj1⟩ := Finset.card_eq_one.mp cb
    have mema : ∀ j, a ∉ I j ↔ j = j0 := by
      intro j; have := congrArg (fun s => j ∈ s) hj0; simpa using this
    have memb : ∀ j, b ∉ I j ↔ j = j1 := by
      intro j; have := congrArg (fun s => j ∈ s) hj1; simpa using this
    have all : ∀ j, j = j0 ∨ j = j1 := by
      intro j
      by_contra hc
      push Not at hc
      have ha : a ∈ I j := by by_contra h; exact hc.1 ((mema j).mp h)
      have hb : b ∈ I j := by by_contra h; exact hc.2 ((memb j).mp h)
      exact hind j a ha b hb hab
    have part : ∀ v : Fin n, (v ∈ I j0 ↔ v ∉ I j1) := by
      intro v
      obtain ⟨ji, hji⟩ := hin v
      obtain ⟨jo, hjo⟩ := hout v
      rcases all ji with rfl | rfl <;> rcases all jo with rfl | rfl
      · exact absurd hji hjo
      · exact ⟨fun _ => hjo, fun _ => hji⟩
      · exact ⟨fun h => absurd h hjo, fun h => absurd hji h⟩
      · exact absurd hji hjo
    have big : ∀ j, 2 ≤ (Finset.univ.filter (fun v => v ∉ I j)).card := by
      intro j
      have hc : (Finset.univ.filter (fun v => v ∉ I j)) = (I j)ᶜ := by ext; simp
      rw [hc, Finset.card_compl, Fintype.card_fin]
      have := hsize j; omega
    obtain ⟨p, hp, p', hp', hpp⟩ := Finset.one_lt_card.mp (show 1 < (Finset.univ.filter (fun v => v ∉ I j1)).card by have := big j1; omega)
    obtain ⟨q, hq, q', hq', hqq⟩ := Finset.one_lt_card.mp (show 1 < (Finset.univ.filter (fun v => v ∉ I j0)).card by have := big j0; omega)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp hp' hq hq'
    have cross : ∀ x y : Fin n, x ∉ I j1 → y ∉ I j0 → G.Adj x y := by
      intro x y hx hy
      by_contra hxy
      have hxy' : x ≠ y := by
        rintro rfl
        exact hy ((part x).mpr hx)
      obtain ⟨j, hjx, hjy⟩ := hpair x y hxy' hxy
      rcases all j with rfl | rfl
      · exact hy hjy
      · exact hx hjx
    exact hc4 p q p' q' hpp hqq ⟨cross p q hp hq, G.adj_symm (cross p' q hp' hq), cross p' q' hp' hq', G.adj_symm (cross p q' hp hq')⟩
  · have hsum : ∑ j : Fin k, (n - (I j).card) = ∑ v : Fin n, (Finset.univ.filter (fun j => v ∉ I j)).card := by
      have e1 : ∀ j : Fin k, n - (I j).card = ∑ v : Fin n, (if v ∉ I j then 1 else 0) := by
        intro j
        rw [Finset.sum_boole]
        have hc : (Finset.univ.filter (fun v => v ∉ I j)) = (I j)ᶜ := by ext; simp
        rw [hc, Finset.card_compl, Fintype.card_fin]
        simp
      rw [Finset.sum_congr rfl (fun j _ => e1 j), Finset.sum_comm]
      refine Finset.sum_congr rfl (fun v _ => ?_)
      rw [Finset.sum_boole]
      simp
    have hsplit : ∑ v : Fin n, (Finset.univ.filter (fun j => v ∉ I j)).card =
        ∑ v : Fin n, max 1 ((Finset.univ.filter (fun j => v ∉ I j)).card - 1) +
          (Finset.univ.filter (fun v => 2 ≤ (Finset.univ.filter (fun j => v ∉ I j)).card)).card := by
      rw [Finset.card_filter, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun v _ => ?_)
      have := cpos v
      split_ifs with h
      · rw [max_eq_right (by omega)]; omega
      · rw [max_eq_left (by omega)]; omega
    rw [hsum, hsplit]
    omega
