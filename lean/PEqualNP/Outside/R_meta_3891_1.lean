import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_3891_1
    (hShort : ∀ gs : List Gate, gs.length ≤ 12 →
      FanInTwo { gates := gs, output := 0 } →
      gs.countP (fun g => g.op.eval [false]) ≤ 1 →
      ∀ j, ¬ ∀ x : Fin 9 → Bool,
        (({ gates := gs, output := 0 } : Circuit).wires (List.ofFn x ++ [x 0 || x 3])).getD j false =
          (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
            x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
            x 6 && x 8 || x 8 && x 5))
    (hFull : ∀ gs : List Gate, gs.length = 13 →
      FanInTwo { gates := gs, output := 0 } →
      gs.countP (fun g => g.op.eval [false]) ≤ 1 →
      ∀ j, ¬ ∀ x : Fin 9 → Bool,
        (({ gates := gs, output := 0 } : Circuit).wires (List.ofFn x ++ [x 0 || x 3])).getD j false =
          (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
            x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
            x 6 && x 8 || x 8 && x 5)) :
    ∀ (x1 : List PEqualNP.CircuitLowerBounds.Gate),   x1.length = (13 : ℕ) →     PEqualNP.MetaComplexity.FanInTwo { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →       List.countP (fun (x4 : PEqualNP.CircuitLowerBounds.Gate) => x4.op.eval [Bool.false]) x1 ≤ (1 : ℕ) →         ∀ (x5 x6 : ℕ),           have x7 : (Fin (9 : ℕ) → Bool) → ℕ → Bool := fun (x7 : Fin (9 : ℕ) → Bool) (x8 : ℕ) => ({ gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x7 ++ [x7 (0 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ))])).getD x8 Bool.false;           have x8 : (Fin (9 : ℕ) → Bool) → Bool := fun (x8 : Fin (9 : ℕ) → Bool) => x8 (0 : Fin (9 : ℕ)) && x8 (1 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (2 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (3 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (4 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ)) && x8 (0 : Fin (9 : ℕ)) || x8 (0 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (6 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (5 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (6 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (8 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ));           (∀ (x9 : Fin (9 : ℕ) → Bool), (x7 x9 x5 && x7 x9 x6) = x8 x9) → (x5 = (22 : ℕ) ∧ (10 : ℕ) ≤ x6 ∧ x6 < (22 : ℕ) ∨ x6 = (22 : ℕ) ∧ (10 : ℕ) ≤ x5 ∧ x5 < (22 : ℕ)) ∧ ∀ x10 ∈ [x5, x6], (x1.getD (x10 - (10 : ℕ)) { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] : PEqualNP.CircuitLowerBounds.Gate }).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not := by
  intro gs hlen hfan hcnt a b wF edgeF hagree
  let edge : (Fin 9 → Bool) → Bool := fun x =>
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
    x 6 && x 8 || x 8 && x 5
  let base : (Fin 9 → Bool) → List Bool := fun x => List.ofFn x ++ [x 0 || x 3]
  let step : List Bool → Gate → List Bool := fun w g =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let wlen : (Fin 9 → Bool) → ℕ → Bool := fun x i =>
    (gs.foldl step (base x)).getD i false
  have hwF (x : Fin 9 → Bool) (i : ℕ) : wF x i = wlen x i := by
    simp [wF, wlen, step, base, Circuit.wires]
  have heF (x : Fin 9 → Bool) : edgeF x = edge x := by
    rfl
  have hedge : ∀ x, (wlen x a && wlen x b) = edge x := by
    intro x
    rw [← hwF x a, ← hwF x b, ← heF x]
    exact hagree x
  have base_len (x : Fin 9 → Bool) : (base x).length = 10 := by
    simp [base, List.length_append, List.length_ofFn]
  have len_add : ∀ extra : List Gate, ∀ w : List Bool,
      (extra.foldl step w).length = w.length + extra.length := by
    intro extra
    induction extra with
    | nil => intro w; simp
    | cons g extra ih =>
        intro w
        rw [List.foldl_cons, ih]
        simp [step]
        omega
  have take_stable : ∀ extra : List Gate, ∀ w : List Bool,
      (extra.foldl step w).take w.length = w := by
    intro extra
    induction extra with
    | nil => intro w; simp
    | cons g extra ih =>
        intro w
        rw [List.foldl_cons]
        have htake := ih (step w g)
        have hlen1 : (step w g).length = w.length + 1 := by simp [step]
        have h2 : ((extra.foldl step (step w g)).take (step w g).length).take w.length = w := by
          rw [htake]
          simp [step, List.take_append_of_le_length]
        rw [List.take_take] at h2
        simpa [hlen1, Nat.min_eq_left] using h2
  have get_take : ∀ (l : List Bool) (n i : ℕ), i < n → (l.take n).getD i false = l.getD i false := by
    intro l n i hi
    by_cases hlt : i < l.length
    · have htake : i < (l.take n).length := by
        rw [List.length_take]
        exact Nat.lt_min.mpr ⟨hi, hlt⟩
      rw [List.getD_eq_getElem _ _ hlt, List.getD_eq_getElem _ _ htake, List.getElem_take]
    · have hle : l.length ≤ i := Nat.le_of_not_gt hlt
      rw [List.getD_eq_default _ _ hle]
      have : (l.take n).length ≤ i := by
        rw [List.length_take]
        exact le_trans (Nat.min_le_right _ _) hle
      rw [List.getD_eq_default _ _ this]
  have agree (extra : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (extra.foldl step w).getD i false = w.getD i false := by
    rw [← get_take (extra.foldl step w) w.length i hi, take_stable]
  have step_at (w : List Bool) (g : Gate) (i : ℕ) :
      (step w g).getD i false =
        if i < w.length then w.getD i false
        else if i = w.length then g.op.eval (g.inputs.map fun j => w.getD j false)
        else false := by
    by_cases hlt : i < w.length
    · rw [show step w g = w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)] from rfl,
        List.getD_append _ _ _ _ hlt, if_pos hlt]
    · have hle : w.length ≤ i := Nat.le_of_not_gt hlt
      rw [show step w g = w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)] from rfl,
        List.getD_append_right _ _ _ _ hle, if_neg hlt]
      by_cases heq : i = w.length
      · simp [heq]
      · rw [if_neg heq]
        have : [g.op.eval (g.inputs.map fun j => w.getD j false)].length ≤ i - w.length := by
          simp
          omega
        exact List.getD_eq_default _ _ this
  have full_len (x) : (gs.foldl step (base x)).length = 23 := by
    simpa [hlen, base_len x] using len_add gs (base x)
  have top : edge (fun _ : Fin 9 => true) = true := by decide
  have bot : edge (fun _ : Fin 9 => false) = false := by decide
  let off : Fin 9 → Fin 9 → Bool := fun i j =>
    bif i.val = 1 then j.val = 2 || j.val = 3
    else bif i.val = 2 then j.val = 3 || j.val = 4
    else bif i.val = 3 then j.val = 0 || j.val = 4
    else j.val = 1 || j.val = 2
  have hoff : ∀ i : Fin 9, off i i = false ∧ edge (off i) = true := by decide
  let zseed : Fin 9 → Bool := fun j => j.val = 1 || j.val = 2
  have hseed : (zseed 0 || zseed 3) = false ∧ edge zseed = true := by decide
  have base_get (x : Fin 9 → Bool) (i : ℕ) :
      (base x).getD i false =
        if h : i < 9 then x ⟨i, h⟩ else if i = 9 then x 0 || x 3 else false := by
    by_cases h9 : i < 9
    · have hlen9 : i < (List.ofFn x).length := by simpa [List.length_ofFn] using h9
      rw [show base x = List.ofFn x ++ [x 0 || x 3] from rfl,
        List.getD_append _ _ _ _ hlen9, List.getD_eq_getElem _ _ hlen9, List.getElem_ofFn]
      simp [h9]
    · by_cases h8 : i = 9
      · have hlen9 : (List.ofFn x).length ≤ i := by
          simp [List.length_ofFn, h8]
        rw [show base x = List.ofFn x ++ [x 0 || x 3] from rfl, List.getD_append_right _ _ _ _ hlen9]
        simp [h9, h8, List.length_ofFn]
      · have hle : (base x).length ≤ i := by rw [base_len]; omega
        rw [List.getD_eq_default _ _ hle]
        simp [h9, h8]
  have early (x) (i : ℕ) (hi : i < 10) : wlen x i = (base x).getD i false := by
    have hi' : i < (base x).length := by simpa [base_len x] using hi
    simpa [wlen] using agree gs (base x) i hi'
  have opKind (g : Gate) (hg : g ∈ gs) : g.op = .and ∨ g.op = .or ∨ g.op = .not := by
    simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using (hfan g hg).1
  have countTwo (l : List Gate) (i j : ℕ) (hij : i < j) (hj : j < l.length)
      (hi : (l[i]'(Nat.lt_trans hij hj)).op.eval [false] = true)
      (hjv : (l[j]'hj).op.eval [false] = true) :
      2 ≤ l.countP (fun g => g.op.eval [false]) := by
    induction l generalizing i j with
    | nil => simp at hj
    | cons g l ih =>
        simp only [List.length_cons] at hj
        cases j with
        | zero => omega
        | succ j =>
            have hj' : j < l.length := by omega
            cases i with
            | zero =>
                have hg : g.op.eval [false] = true := by simpa using hi
                have htail : 0 < l.countP (fun g => g.op.eval [false]) := by
                  rw [List.countP_pos_iff]
                  exact ⟨l[j]'hj', List.getElem_mem hj', by simpa using hjv⟩
                have hcount : l.countP (fun g => g.op.eval [false]) + 1 =
                    (g :: l).countP (fun g => g.op.eval [false]) := by
                  simp [List.countP_cons, hg]
                omega
            | succ i =>
                have hih := ih i j (by omega) hj' (by simpa using hi) (by simpa using hjv)
                have hle : l.countP (fun g => g.op.eval [false]) ≤
                    (g :: l).countP (fun g => g.op.eval [false]) := by
                  simp only [List.countP_cons]
                  split_ifs <;> omega
                omega
  have killHigh (i : ℕ) (hi : 23 ≤ i) (hside : i = a ∨ i = b) : False := by
    have hfalse : wlen (fun _ : Fin 9 => true) i = false := by
      have hle : (gs.foldl step (base (fun _ => true))).length ≤ i := by
        simpa [full_len] using hi
      simpa [wlen] using List.getD_eq_default (gs.foldl step (base (fun _ => true))) false hle
    have h := hedge (fun _ : Fin 9 => true)
    rcases hside with rfl | rfl
    · rw [hfalse, Bool.false_and, top] at h
      exact Bool.false_ne_true h
    · rw [hfalse, Bool.and_false, top] at h
      exact Bool.false_ne_true h
  by_cases ha : 23 ≤ a
  · exact (killHigh a ha (Or.inl rfl)).elim
  by_cases hb : 23 ≤ b
  · exact (killHigh b hb (Or.inr rfl)).elim
  have ha23 : a < 23 := Nat.not_le.mp ha
  have hb23 : b < 23 := Nat.not_le.mp hb
  have killIn (i : ℕ) (hi : i < 10)
      (hk : ∀ x, wlen x i = false → edge x = false) : False := by
    by_cases h9 : i < 9
    · obtain ⟨hx, he⟩ := hoff ⟨i, h9⟩
      have hbit : wlen (off ⟨i, h9⟩) i = false := by
        rw [early _ _ hi, base_get]
        simp [h9, hx]
      exact Bool.false_ne_true ((hk _ hbit) ▸ he)
    · have hi9 : i = 9 := by omega
      have hz : wlen zseed i = false := by
        rw [early _ _ hi, base_get, hi9]
        simpa using hseed.1
      exact Bool.false_ne_true ((hk _ hz) ▸ hseed.2)
  have fromA (x) (hx : wlen x a = false) : edge x = false := by
    have h := hedge x
    rw [hx, Bool.false_and] at h
    exact h.symm
  have fromB (x) (hx : wlen x b = false) : edge x = false := by
    have h := hedge x
    rw [hx, Bool.and_false] at h
    exact h.symm
  by_cases ha10 : a < 10
  · exact (killIn a ha10 fromA).elim
  by_cases hb10 : b < 10
  · exact (killIn b hb10 fromB).elim
  have ha10' : 10 ≤ a := Nat.le_of_not_gt ha10
  have hb10' : 10 ≤ b := Nat.le_of_not_gt hb10
  have ha22 : a ≤ 22 := by omega
  have hb22 : b ≤ 22 := by omega
  let m := max a b
  have hm10 : 10 ≤ m := le_trans ha10' (le_max_left _ _)
  have hm22 : m ≤ 22 := max_le ha22 hb22
  have wireEq (c : List Gate) (j : ℕ)
      (hc : ∀ x, (c.foldl step (base x)).getD j false = edge x)
      (hf : FanInTwo { gates := c, output := 0 })
      (hn : c.countP (fun g => g.op.eval [false]) ≤ 1)
      (hlenC : c.length ≤ 13) : False := by
    by_cases h13 : c.length = 13
    · exact hFull c h13 hf hn j (by simpa [step, base, edge, Circuit.wires] using hc)
    · have hle : c.length ≤ 12 := by omega
      exact hShort c hle hf hn j (by simpa [step, base, edge, Circuit.wires] using hc)
  by_cases hm : m = 22
  · by_cases hab : a = b
    · have : ∀ x, wlen x a = edge x := by
        intro x
        simpa [hab, Bool.and_self] using hedge x
      exact (hFull gs hlen hfan hcnt a (by simpa [wlen, step, base, edge, Circuit.wires] using this)).elim
    · have hshape : a = 22 ∧ 10 ≤ b ∧ b < 22 ∨ b = 22 ∧ 10 ≤ a ∧ a < 22 := by
        by_cases ha22' : a = 22
        · left
          refine ⟨ha22', hb10', ?_⟩
          by_contra h
          have hb22' : b = 22 := by omega
          exact hab (ha22'.trans hb22'.symm)
        · right
          have hb22' : b = 22 := by
            by_contra h
            have : m < 22 := max_lt (by omega : a < 22) (by omega : b < 22)
            omega
          refine ⟨hb22', ha10', by omega⟩
      have base_mono (x y : Fin 9 → Bool) (hxy : ∀ i, x i = true → y i = true) :
          ∀ i, (base x).getD i false = true → (base y).getD i false = true := by
        intro i hi
        rw [base_get] at hi
        rw [base_get]
        by_cases h9 : i < 9
        · simp only [h9, dite_true] at hi ⊢
          exact hxy ⟨i, h9⟩ hi
        · by_cases h8 : i = 9
          · simp only [h9, h8, dite_false, ite_true] at hi ⊢
            rcases Bool.or_eq_true_iff.mp hi with h0 | h3
            · simp [hxy 0 h0]
            · simp [hxy 3 h3]
          · simp [h9, h8] at hi
      have preserve (u v : List Bool) (g : Gate) (hop : g.op = .and ∨ g.op = .or)
          (hlenuv : u.length = v.length)
          (hm' : ∀ i, u.getD i false = true → v.getD i false = true) :
          ∀ i, (step u g).getD i false = true → (step v g).getD i false = true := by
        intro i hi
        have hlenS : (step u g).length = u.length + 1 := by simp [step]
        by_cases hlt : i < u.length
        · have hu : u.getD i false = true := by
            have hs := step_at u g i
            rw [if_pos hlt] at hs
            exact hs ▸ hi
          have hv := hm' i hu
          have hs := step_at v g i
          have hltv : i < v.length := by simpa [hlenuv] using hlt
          rw [if_pos hltv] at hs
          exact hs.symm ▸ hv
        · have hltS : i < (step u g).length := by
            by_contra hge
            rw [List.getD_eq_default _ _ (Nat.le_of_not_gt hge)] at hi
            exact Bool.false_ne_true hi
          have heq : i = u.length := by omega
          rw [heq] at hi
          have hval : g.op.eval (g.inputs.map fun j => u.getD j false) = true := by
            have hs := step_at u g u.length
            rw [if_neg (by omega : ¬ u.length < u.length), if_pos rfl] at hs
            exact hs ▸ hi
          have hvalv : g.op.eval (g.inputs.map fun j => v.getD j false) = true := by
            rcases hop with hAnd | hOr
            · rw [hAnd] at hval ⊢
              simp only [GateOp.eval, List.all_eq_true] at hval ⊢
              intro bit hbit
              obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hbit
              exact hm' j (hval _ (List.mem_map.mpr ⟨j, hj, rfl⟩))
            · rw [hOr] at hval ⊢
              simp only [GateOp.eval, List.any_eq_true] at hval ⊢
              obtain ⟨bit, hbit, htrue⟩ := hval
              obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hbit
              exact ⟨v.getD j false, List.mem_map.mpr ⟨j, hj, rfl⟩, hm' j htrue⟩
          have hsv := step_at v g i
          have hltv : ¬ i < v.length := by rw [← hlenuv]; omega
          have heqv : i = v.length := by rw [← hlenuv]; omega
          rw [if_neg hltv, if_pos heqv] at hsv
          exact hsv.symm ▸ hvalv
      have acc_mono : ∀ (pre : List Gate) (u v : List Bool),
          (∀ g ∈ pre, g.op = .and ∨ g.op = .or) → u.length = v.length →
          (∀ i, u.getD i false = true → v.getD i false = true) →
          ∀ i, (pre.foldl step u).getD i false = true → (pre.foldl step v).getD i false = true := by
        intro pre
        induction pre with
        | nil => intro u v _ _ hm' i hi; exact hm' i hi
        | cons g pre ih =>
            intro u v hp hlenuv hm' i hi
            simp only [List.foldl_cons] at hi ⊢
            exact ih (step u g) (step v g)
              (fun q hq => hp q (List.mem_cons_of_mem _ hq))
              (by simp [step, hlenuv])
              (preserve u v g (hp g List.mem_cons_self) hlenuv hm') i hi
      have notSel (t s : ℕ) (ht : 10 ≤ t) (ht22 : t ≤ 22)
          (hsame : ∀ x, (wlen x t && wlen x s) = edge x)
          (hop : (gs.getD (t - 10) { op := .or, inputs := [] }).op = .not) : False := by
        have hp : t - 10 < gs.length := by omega
        let p := t - 10
        have hpp : p = t - 10 := rfl
        have hgate : (gs[p]'hp).op = .not := by
          have h := hop
          rw [← hpp] at h
          rw [List.getD_eq_getElem (l := gs) (n := p)
            (d := ({ op := .or, inputs := [] } : Gate)) (hn := hp)] at h
          exact h
        have hpos : (gs[p]'hp).op.eval [false] = true := by
          rw [hgate]
          rfl
        have alone (q : ℕ) (hq : q < gs.length) (hqn : (gs[q]'hq).op = .not) : q = p := by
          by_contra hne
          have htwo : 2 ≤ gs.countP (fun g => g.op.eval [false]) := by
            rcases lt_or_gt_of_ne hne with hlt | hgt
            · exact countTwo gs q p hlt hp (by rw [hqn]; rfl) hpos
            · exact countTwo gs p q hgt hq hpos (by rw [hqn]; rfl)
          omega
        have pre_ok : ∀ g ∈ gs.take p, g.op = .and ∨ g.op = .or := by
          intro g hg
          obtain ⟨q, hq, hqg⟩ := List.mem_iff_getElem.mp hg
          have hq' : q < p := by
            have := hq
            simp only [List.length_take, hlen] at this
            omega
          have hqlen : q < gs.length := by omega
          have hmem : gs[q]'hqlen ∈ gs := List.getElem_mem _
          have hne : (gs[q]'hqlen).op ≠ .not := by
            intro hn
            exact absurd (alone q hqlen hn) (by omega)
          have hqeq : g = gs[q]'hqlen := by
            rw [← hqg]
            exact List.getElem_take
          rw [hqeq]
          rcases opKind _ hmem with h | h | h
          · exact Or.inl h
          · exact Or.inr h
          · exact (hne h).elim
        let gte := gs[p]'hp
        let pre := gs.take p
        have hpre_len : pre.length = p := by
          simp [pre, List.length_take_of_le (by omega : p ≤ gs.length)]
        have wlen_pre (x) : (pre.foldl step (base x)).length = t := by
          have := len_add pre (base x)
          simp [hpre_len, base_len x, p] at this
          omega
        have full_at (x) : wlen x t =
            gte.op.eval (gte.inputs.map fun j => (pre.foldl step (base x)).getD j false) := by
          have hsplit : gs.foldl step (base x) =
              (gs.drop (p + 1)).foldl step (step (pre.foldl step (base x)) gte) := by
            have happ : gs.take p ++ gs.drop p = gs := List.take_append_drop p gs
            have hd : gs.drop p = gte :: gs.drop (p + 1) := by
              simpa [gte] using (List.drop_eq_getElem_cons (i := p) (l := gs) hp)
            calc
              gs.foldl step (base x)
                  = (gs.take p ++ gs.drop p).foldl step (base x) := by simp [happ]
              _ = (gs.drop p).foldl step ((gs.take p).foldl step (base x)) := by
                    rw [List.foldl_append]
              _ = (gte :: gs.drop (p + 1)).foldl step (pre.foldl step (base x)) := by
                    rw [hd]
              _ = (gs.drop (p + 1)).foldl step (step (pre.foldl step (base x)) gte) := by
                    simp [List.foldl_cons, pre]
          have hkeep := agree (gs.drop (p + 1)) (step (pre.foldl step (base x)) gte) t (by
            have hlen := wlen_pre x
            simp [step] at hlen ⊢
            omega)
          have hs := step_at (pre.foldl step (base x)) gte t
          have hnotlt : ¬ t < (pre.foldl step (base x)).length := by
            rw [wlen_pre x]
            exact Nat.lt_irrefl _
          have heqt : t = (pre.foldl step (base x)).length := (wlen_pre x).symm
          rw [ite_eq_right hnotlt, ite_eq_left heqt] at hs
          have hwire : wlen x t = (step (pre.foldl step (base x)) gte).getD t false := by
            unfold wlen
            rw [hsplit]
            exact hkeep
          rw [hwire, hs]
        have tout (x) : wlen x t = true := by
          let tall : Fin 9 → Bool := fun _ => true
          have htall : wlen tall t = true := by
            have h := hsame tall
            rw [top] at h
            exact (Bool.and_eq_true_iff.mp h).1
          have hbit_false :
              gte.inputs = [] ∨
                (pre.foldl step (base tall)).getD (gte.inputs.headD 0) false = false := by
            have hval := full_at tall
            rw [htall, hgate] at hval
            cases hinputs : gte.inputs with
            | nil => exact Or.inl rfl
            | cons j rest =>
                right
                have h := hval
                rw [hinputs] at h
                simp only [GateOp.eval, List.map_cons, List.headD] at h
                cases hbit : (pre.foldl step (base tall)).getD j false with
                | false => exact hbit
                | true =>
                    rw [hbit] at h
                    cases h
          have alwaysFalse (x) :
              gte.inputs = [] ∨
                (pre.foldl step (base x)).getD (gte.inputs.headD 0) false = false := by
            rcases hbit_false with hempty | hfalse
            · exact Or.inl hempty
            · right
              by_contra htrue
              have hmbase : ∀ i, (base x).getD i false = true →
                  (base tall).getD i false = true :=
                base_mono x tall (fun _ _ => rfl)
              have hmono := acc_mono pre (base x) (base tall) pre_ok
                (by simp [base_len]) hmbase (gte.inputs.headD 0) (by simpa using htrue)
              exact Bool.false_ne_true (hfalse ▸ hmono)
          have hval := full_at x
          rw [hgate] at hval
          rcases alwaysFalse x with hempty | hfalse
          · rw [hempty] at hval
            simp only [GateOp.eval, List.map_nil, List.headD] at hval
            exact hval
          · cases hinputs : gte.inputs with
            | nil =>
                rw [hinputs] at hval
                simp only [GateOp.eval, List.map_nil, List.headD] at hval
                exact hval
            | cons j rest =>
                have hfalse' : (pre.foldl step (base x)).getD j false = false := by
                  have h := hfalse
                  rw [hinputs] at h
                  simp only [List.headD] at h
                  exact h
                have h := hval
                rw [hinputs] at h
                simp only [GateOp.eval, List.map_cons, List.headD, hfalse'] at h
                exact h
        have hsF : ∀ x, wlen x s = edge x := by
          intro x
          have h := hsame x
          rw [tout x, Bool.true_and] at h
          exact h
        exact hFull gs hlen hfan hcnt s
          (by simpa [wlen, step, base, edge, Circuit.wires] using hsF)
      refine ⟨hshape, ?_⟩
      intro j hj hop
      have hdis : j = a ∨ j = b := by
        simpa [List.mem_cons, List.mem_singleton] using hj
      rcases hdis with hja | hjb
      · rw [hja] at hop
        exact (notSel a b ha10' ha22 hedge hop).elim
      · rw [hjb] at hop
        exact (notSel b a hb10' hb22 (fun x => by simpa [Bool.and_comm] using hedge x) hop).elim
  · have hm21 : m ≤ 21 := by omega
    let k := m - 9
    have hklen : k ≤ gs.length := by omega
    let pref := gs.take k
    have hpref_len : pref.length = k := by simp [pref, List.length_take_of_le hklen]
    let built := pref ++ [{ op := GateOp.and, inputs := [a, b] }]
    have hfanB : FanInTwo { gates := built, output := 0 } := by
      intro g hg
      simp only [built, List.mem_append, List.mem_singleton] at hg
      rcases hg with hg | rfl
      · exact hfan g (List.mem_of_mem_take hg)
      · exact ⟨by simp [Set.mem_insert_iff, Set.mem_singleton_iff], by simp⟩
    have hcntB : built.countP (fun g => g.op.eval [false]) ≤ 1 := by
      have sub : ∀ (l : List Gate) (n : ℕ),
          (l.take n).countP (fun g => g.op.eval [false]) ≤ l.countP (fun g => g.op.eval [false]) := by
        intro l n
        induction l generalizing n with
        | nil => simp
        | cons g l ih =>
            cases n with
            | zero => simp
            | succ n =>
                simp only [List.take_succ_cons, List.countP_cons]
                have := ih n
                split_ifs <;> omega
      have htake : pref.countP (fun g => g.op.eval [false]) ≤
          gs.countP (fun g => g.op.eval [false]) := by
        simpa [pref] using sub gs k
      have hand : built.countP (fun g => g.op.eval [false]) =
          pref.countP (fun g => g.op.eval [false]) := by
        simp [built, List.countP_append, GateOp.eval]
      rw [hand]
      exact htake.trans hcnt
    have hwire : ∀ x, (built.foldl step (base x)).getD (m + 1) false = edge x := by
      intro x
      have hwlen : (pref.foldl step (base x)).length = m + 1 := by
        have := len_add pref (base x)
        simp [hpref_len, base_len x, k] at this
        omega
      have haI : a < (pref.foldl step (base x)).length := by omega
      have hbI : b < (pref.foldl step (base x)).length := by omega
      have hdrop : (gs.drop k).foldl step (pref.foldl step (base x)) = gs.foldl step (base x) := by
        simpa [pref, List.take_append_drop] using
          (List.foldl_append (f := step) (b := base x) (l := gs.take k) (l' := gs.drop k)).symm
      have hag : (pref.foldl step (base x)).getD a false = wlen x a := by
        have := agree (gs.drop k) (pref.foldl step (base x)) a haI
        simpa [wlen, hdrop] using this.symm
      have hbg : (pref.foldl step (base x)).getD b false = wlen x b := by
        have := agree (gs.drop k) (pref.foldl step (base x)) b hbI
        simpa [wlen, hdrop] using this.symm
      have hfold : built.foldl step (base x) =
          step (pref.foldl step (base x)) { op := GateOp.and, inputs := [a, b] } := by
        simp [built, List.foldl_append]
      rw [hfold]
      have hlast := step_at (pref.foldl step (base x))
        { op := GateOp.and, inputs := [a, b] } (m + 1)
      rw [if_neg (by omega : ¬ m + 1 < (pref.foldl step (base x)).length),
        if_pos (by omega : m + 1 = (pref.foldl step (base x)).length)] at hlast
      rw [hlast]
      simp only [GateOp.eval, List.map_cons, List.map_nil, hag, hbg,
        List.all_cons, List.all_nil, Bool.and_true, id_eq]
      rw [hedge]
    have hlenB : built.length = k + 1 := by simp [built, hpref_len]
    exact (wireEq built (m + 1) hwire hfanB hcntB (by omega)).elim
