import Mathlib.Data.Fin.Basic

theorem PEqualNP.Outside.L_meta_249 : ∀ (N k : ℕ) (E : Fin N → Fin N → Prop) (pos : Fin N → ℕ), 1 ≤ k → ((∀ u v : Fin N, E u v → E v u) ∧ (∀ u v : Fin N, E u v → pos u ≠ 0 ∨ pos v ≠ 0) ∧ ∀ v : Fin N, pos v ≠ 0 → pos v ≤ 2 * k ∧ ∃ a b : Fin N, (∀ w : Fin N, E v w ↔ w = a ∨ w = b) ∧ pos a + 1 = pos v ∧ pos b = (pos v + 1) % (2 * k + 1)) → (∀ (L : ℕ) (w : ℕ → Fin N), pos (w 0) = 0 → pos (w L) = 0 → w 0 ≠ w L → (∀ i : ℕ, i < L → E (w i) (w (i + 1))) → 2 * k + 1 ≤ L) ∧ ∀ v a b c : Fin N, E v a → E v b → E v c → a ≠ b → a ≠ c → b ≠ c → pos v = 0 := by
  intro N k E pos hk h
  obtain ⟨symm, noHubEdge, inner⟩ := h
  have successor (p : ℕ) (hp : p ≤ 2 * k) :
      (p + 1) % (2 * k + 1) = p + 1 ∨
        ((p + 1) % (2 * k + 1) = 0 ∧ p = 2 * k) := by
    by_cases he : p = 2 * k
    · subst p
      simp
    · exact Or.inl (Nat.mod_eq_of_lt (by omega))
  constructor
  · intro L
    induction L using Nat.strong_induction_on with
    | ind L shorter =>
      intro w start finish distinct edge
      by_contra short
      have positive : 0 < L := by
        by_contra hn
        have : L = 0 := by omega
        exact distinct (congrArg w this.symm)
      -- Delete an immediate reversal, retaining both endpoints of the walk.
      have noReturn (j : ℕ) (hj : j + 2 ≤ L) : w j ≠ w (j + 2) := by
        intro back
        let u (i : ℕ) := if i ≤ j then w i else w (i + 2)
        have endEq : u (L - 2) = w L := by
          by_cases eq : L - 2 = j
          · have hL : L = j + 2 := by omega
            simpa [u, eq, hL] using back
          · have gt : ¬ L - 2 ≤ j := by omega
            simp [u, gt, Nat.sub_add_cancel (by omega : 2 ≤ L)]
        have path (i : ℕ) (hi : i < L - 2) : E (u i) (u (i + 1)) := by
          by_cases left : i + 1 ≤ j
          · simpa [u, left, show i ≤ j by omega] using edge i (by omega)
          · by_cases atJ : i = j
            · subst i
              simpa [u, left, back] using edge (j + 2) (by omega)
            · have right : ¬ i ≤ j := by omega
              simpa [u, left, right, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
                using edge (i + 2) (by omega)
        have newBound := shorter (L - 2) (by omega) u (by simpa [u] using start)
          (endEq ▸ finish) (by simpa [u, endEq] using distinct) path
        omega
      -- At an inner vertex a walk without reversals uses its two different neighbours.
      have step (j : ℕ) (hj : j + 2 ≤ L) (inside : pos (w (j + 1)) ≠ 0) :
          (pos (w j) + 1 = pos (w (j + 1)) ∧
            (pos (w (j + 2)) = pos (w (j + 1)) + 1 ∨
              (pos (w (j + 2)) = 0 ∧ pos (w (j + 1)) = 2 * k))) ∨
          (pos (w (j + 2)) + 1 = pos (w (j + 1)) ∧
            (pos (w j) = pos (w (j + 1)) + 1 ∨
              (pos (w j) = 0 ∧ pos (w (j + 1)) = 2 * k))) := by
        obtain ⟨bound, a, b, adj, ha, hb⟩ := inner _ inside
        have wrap := successor _ bound
        have prev := (adj _).mp (symm _ _ (edge j (by omega)))
        have next := (adj _).mp (edge (j + 1) (by omega))
        rcases prev with pa | pb <;> rcases next with na | nb
        · exact (noReturn j hj (pa.trans na.symm)).elim
        · left
          rw [pa, nb]
          exact ⟨ha, by rw [hb]; exact wrap⟩
        · right
          rw [pb, na]
          exact ⟨ha, by rw [hb]; exact wrap⟩
        · exact (noReturn j hj (pb.trans nb.symm)).elim
      have e := edge 0 positive
      have firstInner : pos (w 1) ≠ 0 := (noHubEdge _ _ e).resolve_left (by simp [start])
      obtain ⟨bound, a, b, adj, ha, hb⟩ := inner _ firstInner
      have first : pos (w 1) = 1 ∨ pos (w 1) = 2 * k := by
        rcases (adj _).mp (symm _ _ e) with e0 | e0
        · rw [← e0, start] at ha
          omega
        · rw [← e0, start] at hb
          have wrap := successor _ bound
          omega
      have reach : L - 1 + 1 = L := by omega
      rcases first with up | down
      · have walk (j : ℕ) (hj : j + 1 ≤ L) :
            pos (w j) = j ∧ pos (w (j + 1)) = j + 1 := by
          induction j with
          | zero => exact ⟨start, up⟩
          | succ j ih =>
            obtain ⟨p, q⟩ := ih (by omega)
            have advance := step j hj (by omega)
            refine ⟨q, ?_⟩
            change pos (w (j + 2)) = j + 2
            omega
        have last := (walk (L - 1) (by omega)).2
        rw [reach, finish] at last
        omega
      · have walk (j : ℕ) (hj : j + 1 ≤ L) :
            (j = 0 ∧ pos (w j) = 0 ∨ pos (w j) + j = 2 * k + 1) ∧
              pos (w (j + 1)) + (j + 1) = 2 * k + 1 := by
          induction j with
          | zero =>
            refine ⟨Or.inl ⟨rfl, start⟩, ?_⟩
            change pos (w 1) + 1 = 2 * k + 1
            rw [down]
          | succ j ih =>
            obtain ⟨p, q⟩ := ih (by omega)
            have advance := step j hj (by omega)
            refine ⟨Or.inr q, ?_⟩
            change pos (w (j + 2)) + (j + 2) = 2 * k + 1
            omega
        have last := (walk (L - 1) (by omega)).2
        rw [reach, finish] at last
        omega
  · intro v a b c ea eb ec ab ac bc
    by_contra inside
    obtain ⟨_, l, r, adj, _, _⟩ := inner v inside
    rcases (adj a).mp ea with ha | ha <;> rcases (adj b).mp eb with hb | hb <;>
      rcases (adj c).mp ec with hc | hc <;> simp_all
