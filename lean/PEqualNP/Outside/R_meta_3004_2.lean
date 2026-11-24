import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3004_2
    (search :
      let A : List ℕ := [95229015649943559, 63038587666488, 256462815680, 4292497062759936, 8521481482240, 14003410187812864, 55389823207997440, 189297016294081033, 155696362464477250, 218994303132270608, 183565875465490436, 229736628138025984, 270286071508633728, 288160007407550752]
      let run := fun (S : List ℕ) (P : List (Bool × ℕ × ℕ)) =>
        P.foldl (fun ws g => ws ++ [cond g.1 (ws.getD g.2.1 0 ||| ws.getD g.2.2 0) (ws.getD g.2.1 0 &&& ws.getD g.2.2 0)]) S
      ∃ g0 ∈ ([(false, 0, 7), (true, 0, 7), (false, 0, 1), (true, 0, 1), (false, 0, 9), (true, 0, 9)] : List (Bool × ℕ × ℕ)),
      ∃ (P : List (Bool × ℕ × ℕ)) (finOp : Bool) (u v : ℕ),
        P.length ≤ 24 ∧
        (∀ i : Fin P.length, (P.get i).2.1 < (P.get i).2.2 ∧ (P.get i).2.2 < 15 + i.val) ∧
        u < v ∧ v < 15 + P.length ∧
        let ws := run A (g0 :: P)
        cond finOp (ws.getD u 0 ||| ws.getD v 0) (ws.getD u 0 &&& ws.getD v 0) = 2097151)
    (eval_valid :
      let run := fun (S : List ℕ) (P : List (Bool × ℕ × ℕ)) =>
        P.foldl (fun ws g => ws ++ [cond g.1 (ws.getD g.2.1 0 ||| ws.getD g.2.2 0) (ws.getD g.2.1 0 &&& ws.getD g.2.2 0)]) S
      ∀ (S : List ℕ) (P : List (Bool × ℕ × ℕ)),
        (∀ i : Fin P.length, (P.get i).2.1 < S.length + i.val ∧ (P.get i).2.2 < S.length + i.val) →
        let L := (run S P).drop S.length
        L.length = P.length ∧
        ∀ i : Fin L.length, ∃ a ∈ S ++ L.take i.val, ∃ b ∈ S ++ L.take i.val,
          L.get i = (a &&& b) ∨ L.get i = (a ||| b))
    (compact :
      ∀ (S L : List ℕ) (t : ℕ), t ∉ S → t ∈ L →
        (∀ i : Fin L.length, ∃ a ∈ S ++ L.take i.val, ∃ b ∈ S ++ L.take i.val,
          L.get i = (a &&& b) ∨ L.get i = (a ||| b)) →
        ∃ K : List ℕ, K.length ≤ L.length ∧ K.Nodup ∧ (∀ z ∈ K, z ∉ S) ∧ t ∈ K ∧
          ∀ i : Fin K.length, ∃ a ∈ S ++ K.take i.val, ∃ b ∈ S ++ K.take i.val,
            K.get i = (a &&& b) ∨ K.get i = (a ||| b)) :
    have x1 : List ℕ := [(95229015649943559 : ℕ), (63038587666488 : ℕ), (256462815680 : ℕ), (4292497062759936 : ℕ), (8521481482240 : ℕ), (14003410187812864 : ℕ), (55389823207997440 : ℕ), (189297016294081033 : ℕ), (155696362464477250 : ℕ), (218994303132270608 : ℕ), (183565875465490436 : ℕ), (229736628138025984 : ℕ), (270286071508633728 : ℕ), (288160007407550752 : ℕ)]; ∃ (x2 : List ℕ), x2.length ≤ (26 : ℕ) ∧ x2.Nodup ∧ (∀ x3 ∈ x2, x3 ∉ x1) ∧ (2097151 : ℕ) ∈ x2 ∧ ∀ (x3 : Fin x2.length), ∃ x4 ∈ x1 ++ List.take (↑x3) x2, ∃ x5 ∈ x1 ++ List.take (↑x3) x2, x2.get x3 = x4 &&& x5 ∨ x2.get x3 = x4 ||| x5 := by
  let A : List ℕ := [95229015649943559, 63038587666488, 256462815680, 4292497062759936, 8521481482240, 14003410187812864, 55389823207997440, 189297016294081033, 155696362464477250, 218994303132270608, 183565875465490436, 229736628138025984, 270286071508633728, 288160007407550752]
  let run := fun (S : List ℕ) (P : List (Bool × ℕ × ℕ)) =>
    P.foldl (fun ws g => ws ++ [cond g.1 (ws.getD g.2.1 0 ||| ws.getD g.2.2 0) (ws.getD g.2.1 0 &&& ws.getD g.2.2 0)]) S
  obtain ⟨g0, hg0, P, finOp, u, v, hPlen, hPbnd, huv, hv, hfin⟩ := search
  let Q : List (Bool × ℕ × ℕ) := (g0 :: P) ++ [(finOp, u, v)]
  have hg0_bnd : g0.2.1 < 14 ∧ g0.2.2 < 14 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg0
    rcases hg0 with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hAlen : A.length = 14 := rfl
  have hQlen : Q.length = P.length + 2 := by
    simp [Q]
  have hQbnd : ∀ i : Fin Q.length, (Q.get i).2.1 < A.length + i.val ∧ (Q.get i).2.2 < A.length + i.val := by
    intro i
    have hi_lt : i.val < P.length + 2 := hQlen ▸ i.isLt
    by_cases h0 : i.val = 0
    · have hget : Q.get i = g0 := by
        rw [List.get_eq_getElem]
        simp only [h0, Q]
        rfl
      rw [hget, h0, hAlen]
      exact hg0_bnd
    · by_cases hmid : i.val < P.length + 1
      · have hk_lt : i.val - 1 < P.length := by omega
        have hget : Q.get i = P.get ⟨i.val - 1, hk_lt⟩ := by
          rw [List.get_eq_getElem, List.get_eq_getElem]
          dsimp only [Q]
          rw [List.getElem_append_left (by simp only [List.length_cons]; exact hmid)]
          obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero h0
          simp only [hk, List.getElem_cons_succ, Nat.succ_sub_one]
        have hpb := hPbnd ⟨i.val - 1, hk_lt⟩
        dsimp only at hpb
        rw [hget, hAlen]
        omega
      · have heq : i.val = P.length + 1 := by omega
        have hget : Q.get i = (finOp, u, v) := by
          rw [List.get_eq_getElem]
          dsimp only [Q]
          rw [List.getElem_append_right (by simp only [List.length_cons]; omega)]
          simp [heq]
        rw [hget, heq, hAlen]
        dsimp only
        omega
  have hrun_len : ∀ (S : List ℕ) (R : List (Bool × ℕ × ℕ)), (run S R).length = S.length + R.length := by
    intro S R
    induction R generalizing S with
    | nil => simp [run]
    | cons g R ih =>
      simp only [run, List.foldl_cons, List.length_cons]
      rw [ih]
      simp only [List.length_append, List.length_singleton]
      omega
  obtain ⟨hLlen, hLval⟩ := eval_valid A Q hQbnd
  let L := (run A Q).drop A.length
  have hlast : run A Q = run A (g0 :: P) ++ [2097151] := by
    dsimp only [Q, run]
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact congrArg (fun x => run A (g0 :: P) ++ [x]) hfin
  have hdrop : L = (run A (g0 :: P)).drop A.length ++ [2097151] := by
    dsimp only [L]
    rw [hlast, List.drop_append]
    have hle : A.length ≤ (run A (g0 :: P)).length := by
      rw [hrun_len]
      exact Nat.le_add_right _ _
    simp [Nat.sub_eq_zero_of_le hle]
  have hmem : 2097151 ∈ L := by
    rw [hdrop]
    exact List.mem_append.mpr (Or.inr List.mem_cons_self)
  obtain ⟨K, hKlen, hKnd, hKout, hKmem, hKval⟩ := compact A L 2097151 (by decide) hmem hLval
  dsimp only [L, run] at hKlen
  dsimp only at hLlen
  exact ⟨K, by omega, hKnd, hKout, hKmem, hKval⟩
