import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L249

abbrev TL {N : ℕ} (k : ℕ) (E : Fin N → Fin N → Prop) (pos : Fin N → ℕ) : Prop :=
  (∀ u v : Fin N, E u v → E v u) ∧ (∀ u v : Fin N, E u v → pos u ≠ 0 ∨ pos v ≠ 0) ∧
    ∀ v : Fin N, pos v ≠ 0 → pos v ≤ 2 * k ∧ ∃ a b : Fin N, (∀ w : Fin N, E v w ↔ w = a ∨ w = b) ∧
      pos a + 1 = pos v ∧ pos b = (pos v + 1) % (2 * k + 1)

variable {N k : ℕ} {E : Fin N → Fin N → Prop} {pos : Fin N → ℕ}

theorem succ_mod (p k : ℕ) (hp : p ≤ 2 * k) :
    (p + 1) % (2 * k + 1) = if p = 2 * k then 0 else p + 1 := by
  split_ifs with h
  · subst h
    exact Nat.mod_self _
  · exact Nat.mod_eq_of_lt (by omega)

noncomputable def nbA (hT : TL k E pos) (v : Fin N) : Fin N :=
  if h : pos v ≠ 0 then Classical.choose (hT.2.2 v h).2 else v

noncomputable def nbB (hT : TL k E pos) (v : Fin N) : Fin N :=
  if h : pos v ≠ 0 then Classical.choose (Classical.choose_spec (hT.2.2 v h).2) else v

theorem nb_spec (hT : TL k E pos) (v : Fin N) (h : pos v ≠ 0) :
    (∀ w : Fin N, E v w ↔ w = nbA hT v ∨ w = nbB hT v) ∧ pos (nbA hT v) + 1 = pos v ∧
      pos (nbB hT v) = (pos v + 1) % (2 * k + 1) := by
  have := Classical.choose_spec (Classical.choose_spec (hT.2.2 v h).2)
  simp only [nbA, nbB, dif_pos h]
  exact this

theorem bpos (hT : TL k E pos) (v : Fin N) (hv : pos v ≠ 0) :
    (pos v < 2 * k ∧ pos (nbB hT v) = pos v + 1) ∨ (pos v = 2 * k ∧ pos (nbB hT v) = 0) := by
  have hle := (hT.2.2 v hv).1
  obtain ⟨_, _, hb⟩ := nb_spec hT v hv
  rw [succ_mod _ _ hle] at hb
  split_ifs at hb with h
  · right
    exact ⟨h, hb⟩
  · left
    exact ⟨by omega, hb⟩

theorem back (hT : TL k E pos) (v : Fin N) (hv : pos v ≠ 0) (hlt : pos v < 2 * k) :
    nbA hT (nbB hT v) = v := by
  obtain ⟨hnb, ha, hb⟩ := nb_spec hT v hv
  have hbv : pos (nbB hT v) = pos v + 1 := by
    rcases bpos hT v hv with ⟨_, h⟩ | ⟨h, _⟩
    · exact h
    · omega
  have hb0 : pos (nbB hT v) ≠ 0 := by omega
  obtain ⟨hnb', ha', hb'⟩ := nb_spec hT (nbB hT v) hb0
  have hE : E (nbB hT v) v := hT.1 _ _ ((hnb (nbB hT v)).2 (Or.inr rfl))
  rcases (hnb' v).1 hE with h | h
  · exact h.symm
  · exfalso
    rcases bpos hT (nbB hT v) hb0 with ⟨_, hq⟩ | ⟨_, hq⟩
    · rw [← h] at hq
      omega
    · rw [← h] at hq
      omega

theorem hub_adj (hT : TL k E pos) (u x : Fin N) (hE : E u x) (hu : pos u = 0) (hx : pos x ≠ 0) :
    pos x = 1 ∨ pos x = 2 * k := by
  obtain ⟨hnb, ha, hb⟩ := nb_spec hT x hx
  rcases (hnb u).1 (hT.1 _ _ hE) with h' | h'
  · left
    rw [← h', hu] at ha
    omega
  · right
    rcases bpos hT x hx with ⟨_, hq⟩ | ⟨hq, _⟩
    · rw [← h', hu] at hq
      omega
    · exact hq

theorem nbA_one (hT : TL k E pos) (hk : 1 ≤ k) (u x : Fin N) (hE : E u x) (hu : pos u = 0)
    (hx : pos x = 1) : nbA hT x = u := by
  have hx0 : pos x ≠ 0 := by omega
  obtain ⟨hnb, ha, hb⟩ := nb_spec hT x hx0
  rcases (hnb u).1 (hT.1 _ _ hE) with h' | h'
  · exact h'.symm
  · exfalso
    rw [← h', hu, hx, Nat.mod_eq_of_lt (by omega)] at hb
    omega

theorem U_pos (hT : TL k E pos) (x : Fin N) (hx : pos x = 1) :
    ∀ q, q < 2 * k → pos ((nbB hT)^[q] x) = q + 1 := by
  intro q
  induction q with
  | zero =>
    intro _
    simpa using hx
  | succ q ih =>
    intro hq
    rw [Function.iterate_succ_apply']
    have hpq := ih (by omega)
    rcases bpos hT ((nbB hT)^[q] x) (by omega) with ⟨_, h⟩ | ⟨h, _⟩
    · rw [h, hpq]
    · omega

theorem climb (hT : TL k E pos) (hk : 1 ≤ k) (L : ℕ) (w : ℕ → Fin N)
    (h0 : pos (w 0) = 0) (h1 : pos (w 1) = 1) (hin : ∀ i, 0 < i → i < L → pos (w i) ≠ 0)
    (hadj : ∀ i, i < L → E (w i) (w (i + 1))) :
    ∀ i, 0 < i → i < L → w i = (nbB hT)^[pos (w i) - 1] (w 1) ∧ pos (w i) ≤ i := by
  intro i
  induction i with
  | zero =>
    intro h
    exact absurd h (Nat.lt_irrefl 0)
  | succ i ih =>
    intro _ hiL
    rcases Nat.eq_zero_or_pos i with hi0 | hi0
    · subst hi0
      show w 1 = (nbB hT)^[pos (w 1) - 1] (w 1) ∧ pos (w 1) ≤ 1
      rw [h1]
      exact ⟨by simp only [Nat.sub_self, Function.iterate_zero, id_eq], le_rfl⟩
    · obtain ⟨hwi, hpi⟩ := ih hi0 (by omega)
      have hinner : pos (w i) ≠ 0 := hin i hi0 (by omega)
      have hinner' : pos (w (i + 1)) ≠ 0 := hin (i + 1) (by omega) hiL
      have hle := (hT.2.2 (w i) hinner).1
      obtain ⟨hnb, ha, hb⟩ := nb_spec hT (w i) hinner
      rcases (hnb (w (i + 1))).1 (hadj i (by omega)) with h | h
      · have hp : pos (w (i + 1)) + 1 = pos (w i) := by
          rw [h]
          exact ha
        have hp2 : 2 ≤ pos (w i) := by omega
        have hidx : pos (w (i + 1)) - 1 = pos (w i) - 2 := by omega
        refine ⟨?_, by omega⟩
        rw [hidx]
        obtain ⟨q, hq⟩ : ∃ q, pos (w i) - 1 = q + 1 := ⟨pos (w i) - 2, by omega⟩
        have hq2 : pos (w i) - 2 = q := by omega
        rw [hq2]
        calc w (i + 1) = nbA hT (w i) := h
          _ = nbA hT (nbB hT ((nbB hT)^[q] (w 1))) := by
              rw [hwi, hq, Function.iterate_succ_apply']
          _ = (nbB hT)^[q] (w 1) :=
              back hT _ (by rw [U_pos hT _ h1 q (by omega)]; omega)
                (by rw [U_pos hT _ h1 q (by omega)]; omega)
      · have hidx : pos (w (i + 1)) = pos (w i) + 1 := by
          rcases bpos hT (w i) hinner with ⟨_, hq⟩ | ⟨_, hq⟩
          · rw [h]
            exact hq
          · exfalso
            apply hinner'
            rw [h]
            exact hq
        refine ⟨?_, by omega⟩
        rw [hidx, Nat.add_sub_cancel]
        obtain ⟨q, hq⟩ : ∃ q, pos (w i) = q + 1 := ⟨pos (w i) - 1, by omega⟩
        rw [hq, Function.iterate_succ_apply', h, hwi, hq, Nat.add_sub_cancel]

theorem exit_up (hT : TL k E pos) (hk : 1 ≤ k) (L : ℕ) (w : ℕ → Fin N) (hL2 : 2 ≤ L)
    (h0 : pos (w 0) = 0) (h1 : pos (w 1) = 1) (hin : ∀ i, 0 < i → i < L → pos (w i) ≠ 0)
    (hadj : ∀ i, i < L → E (w i) (w (i + 1))) (hL : pos (w L) = 0) :
    w L = w 0 ∨ 2 * k + 1 ≤ L := by
  obtain ⟨n, rfl⟩ : ∃ n, L = n + 1 := ⟨L - 1, by omega⟩
  have hn : 0 < n := by omega
  obtain ⟨hwn, hpn⟩ := climb hT hk (n + 1) w h0 h1 hin hadj n hn (by omega)
  have hinner : pos (w n) ≠ 0 := hin n hn (by omega)
  obtain ⟨hnb, ha, hb⟩ := nb_spec hT (w n) hinner
  rcases (hnb (w (n + 1))).1 (hadj n (by omega)) with h | h
  · left
    rw [h] at hL
    have hp1 : pos (w n) = 1 := by omega
    rw [hp1] at hwn
    simp only [Nat.sub_self, Function.iterate_zero, id_eq] at hwn
    rw [h, hwn]
    exact nbA_one hT hk (w 0) (w 1) (hadj 0 (by omega)) h0 h1
  · right
    rw [h] at hL
    rcases bpos hT (w n) hinner with ⟨_, hq⟩ | ⟨hq, _⟩
    · omega
    · omega

def mirror (k : ℕ) (pos : Fin N → ℕ) (v : Fin N) : ℕ :=
  if pos v = 0 then 0 else 2 * k + 1 - pos v

theorem mirror_eq_zero (hT : TL k E pos) (v : Fin N) : mirror k pos v = 0 ↔ pos v = 0 := by
  unfold mirror
  constructor
  · intro h
    by_contra hv
    rw [if_neg hv] at h
    have := (hT.2.2 v hv).1
    omega
  · intro h
    rw [if_pos h]

theorem TL_mirror (hT : TL k E pos) (hk : 1 ≤ k) : TL k E (mirror k pos) := by
  refine ⟨hT.1, ?_, ?_⟩
  · intro u v huv
    rcases hT.2.1 u v huv with h | h
    · exact Or.inl (fun h' => h ((mirror_eq_zero hT u).1 h'))
    · exact Or.inr (fun h' => h ((mirror_eq_zero hT v).1 h'))
  · intro v hv'
    have hv : pos v ≠ 0 := fun h => hv' ((mirror_eq_zero hT v).2 h)
    obtain ⟨hle, a, b, hnb, ha, hb⟩ := hT.2.2 v hv
    rw [succ_mod _ _ hle] at hb
    refine ⟨?_, b, a, fun w => by rw [hnb]; exact or_comm, ?_, ?_⟩
    · unfold mirror
      rw [if_neg hv]
      omega
    · unfold mirror
      split_ifs at hb with h2
      · rw [if_pos hb, if_neg hv]
        omega
      · rw [if_neg (by omega), if_neg hv]
        omega
    · unfold mirror
      by_cases h1 : pos v = 1
      · rw [if_pos (by omega), if_neg hv, h1, show 2 * k + 1 - 1 + 1 = 2 * k + 1 by omega,
          Nat.mod_self]
      · rw [if_neg (by omega), if_neg hv, Nat.mod_eq_of_lt (by omega)]
        omega

theorem thread_exit (hT : TL k E pos) (hk : 1 ≤ k) (L : ℕ) (w : ℕ → Fin N) (hL2 : 2 ≤ L)
    (h0 : pos (w 0) = 0) (hin : ∀ i, 0 < i → i < L → pos (w i) ≠ 0)
    (hadj : ∀ i, i < L → E (w i) (w (i + 1))) (hL : pos (w L) = 0) (hne : w 0 ≠ w L) :
    2 * k + 1 ≤ L := by
  have h1 : pos (w 1) ≠ 0 := hin 1 (by omega) (by omega)
  rcases hub_adj hT (w 0) (w 1) (hadj 0 (by omega)) h0 h1 with hp | hp
  · rcases exit_up hT hk L w hL2 h0 hp hin hadj hL with h | h
    · exact absurd h.symm hne
    · exact h
  · have hT' := TL_mirror hT hk
    rcases exit_up hT' hk L w hL2 ((mirror_eq_zero hT _).2 h0)
        (by unfold mirror; rw [if_neg h1, hp]; omega)
        (fun i hi hiL h => hin i hi hiL ((mirror_eq_zero hT _).1 h)) hadj
        ((mirror_eq_zero hT _).2 hL) with h | h
    · exact absurd h.symm hne
    · exact h

theorem walk_bound (hT : TL k E pos) (hk : 1 ≤ k) :
    ∀ (L : ℕ) (w : ℕ → Fin N), pos (w 0) = 0 → pos (w L) = 0 → w 0 ≠ w L →
      (∀ i : ℕ, i < L → E (w i) (w (i + 1))) → 2 * k + 1 ≤ L := by
  intro L
  induction L using Nat.strong_induction_on with
  | _ L ih =>
  intro w h0 hL hne hadj
  by_cases hmid : ∃ j, 0 < j ∧ j < L ∧ pos (w j) = 0
  · obtain ⟨j, hj0, hjL, hj⟩ := hmid
    by_cases hwj : w j = w 0
    · have := ih (L - j) (by omega) (fun i => w (j + i))
        (by show pos (w (j + 0)) = 0; rw [Nat.add_zero]; exact hj)
        (by show pos (w (j + (L - j))) = 0; rw [show j + (L - j) = L by omega]; exact hL)
        (by show w (j + 0) ≠ w (j + (L - j)); rw [Nat.add_zero, show j + (L - j) = L by omega, hwj]; exact hne)
        (fun i hi => by show E (w (j + i)) (w (j + (i + 1))); rw [← Nat.add_assoc]; exact hadj _ (by omega))
      omega
    · have := ih j hjL w h0 hj (fun h => hwj h.symm) (fun i hi => hadj i (by omega))
      omega
  · have hL2 : 2 ≤ L := by
      rcases Nat.lt_or_ge L 2 with h | h
      · exfalso
        interval_cases L
        · exact hne rfl
        · rcases hT.2.1 _ _ (hadj 0 (by omega)) with h | h
          · exact h h0
          · exact h hL
      · exact h
    exact thread_exit hT hk L w hL2 h0 (fun i hi hiL h => hmid ⟨i, hi, hiL, h⟩) hadj hL hne

end PEqualNP.Outside.L249

theorem PEqualNP.Outside.L_meta_249 :
    ∀ (N k : ℕ) (E : Fin N → Fin N → Prop) (pos : Fin N → ℕ), 1 ≤ k → ((∀ u v : Fin N, E u v → E v u) ∧ (∀ u v : Fin N, E u v → pos u ≠ 0 ∨ pos v ≠ 0) ∧ ∀ v : Fin N, pos v ≠ 0 → pos v ≤ 2 * k ∧ ∃ a b : Fin N, (∀ w : Fin N, E v w ↔ w = a ∨ w = b) ∧ pos a + 1 = pos v ∧ pos b = (pos v + 1) % (2 * k + 1)) → (∀ (L : ℕ) (w : ℕ → Fin N), pos (w 0) = 0 → pos (w L) = 0 → w 0 ≠ w L → (∀ i : ℕ, i < L → E (w i) (w (i + 1))) → 2 * k + 1 ≤ L) ∧ ∀ v a b c : Fin N, E v a → E v b → E v c → a ≠ b → a ≠ c → b ≠ c → pos v = 0 := by
  intro N k E pos hk hT
  refine ⟨fun L w h0 hL hne hadj => PEqualNP.Outside.L249.walk_bound hT hk L w h0 hL hne hadj, ?_⟩
  intro v a b c hva hvb hvc hab hac hbc
  by_contra hv
  obtain ⟨_, a', b', hnb, _, _⟩ := hT.2.2 v hv
  rcases (hnb a).1 hva with rfl | rfl <;> rcases (hnb b).1 hvb with rfl | rfl <;>
    rcases (hnb c).1 hvc with rfl | rfl <;>
    first | exact hab rfl | exact hac rfl | exact hbc rfl
