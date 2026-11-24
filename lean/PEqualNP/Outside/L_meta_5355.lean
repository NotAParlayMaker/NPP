import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5355

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

def gateEval (g : Gate) (w : List Bool) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [gateEval g w]

def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl step w

lemma run_nil (w : List Bool) : run [] w = w := rfl

lemma run_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    run (g :: gs) w = run gs (step w g) := rfl

lemma run_append (gs hs : List Gate) (w : List Bool) :
    run (gs ++ hs) w = run hs (run gs w) := by
  simp [run, List.foldl_append]

lemma run_length (gs : List Gate) (w : List Bool) :
    (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [run]
  | cons g gs ih =>
    rw [run_cons, ih]
    simp [step]
    omega

lemma run_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih (step w g) (by simp [step]; omega)]
    exact List.getD_append _ _ _ _ hi

lemma step_getD_last (w : List Bool) (g : Gate) :
    (step w g).getD w.length false = gateEval g w := by
  simp [step, List.getD_eq_getElem?_getD]

def orChain : ℕ → ℕ → List ℕ → List Gate × ℕ
  | _, cur, [] => ([], cur)
  | base, cur, w :: ws =>
    let r := orChain (base + 1) base ws
    (⟨GateOp.or, [cur, w]⟩ :: r.1, r.2)

lemma orChain_length (base cur : ℕ) (ws : List ℕ) :
    (orChain base cur ws).1.length = ws.length := by
  induction ws generalizing base cur with
  | nil => rfl
  | cons w ws ih =>
    simp [orChain, ih]

lemma orChain_out_lt (base cur : ℕ) (ws : List ℕ) (hcur : cur < base) :
    (orChain base cur ws).2 < base + ws.length := by
  induction ws generalizing base cur with
  | nil => simp [orChain]; omega
  | cons w ws ih =>
    have h := ih (base + 1) base (by omega)
    simp only [orChain, List.length_cons]
    omega

lemma orChain_all_or (base cur : ℕ) (ws : List ℕ) :
    ∀ g ∈ (orChain base cur ws).1, g.op = GateOp.or ∧ g.inputs.length = 2 := by
  induction ws generalizing base cur with
  | nil => intro g hg; simp [orChain] at hg
  | cons w ws ih =>
    intro g hg
    simp only [orChain, List.mem_cons] at hg
    rcases hg with rfl | hg
    · exact ⟨rfl, rfl⟩
    · exact ih (base + 1) base g hg

lemma orChain_eval (base cur : ℕ) (ws : List ℕ) (w : List Bool)
    (hlen : w.length = base) (hcur : cur < base) (hws : ∀ u ∈ ws, u < base) :
    (run (orChain base cur ws).1 w).getD (orChain base cur ws).2 false =
      (w.getD cur false || ws.any (fun u => w.getD u false)) := by
  induction ws generalizing base cur w with
  | nil =>
    simp [orChain, run]
  | cons u us ih =>
    simp only [orChain, run_cons, List.any_cons]
    have hu : u < base := hws u (List.mem_cons_self ..)
    have hstep_len : (step w ⟨GateOp.or, [cur, u]⟩).length = base + 1 := by
      simp [step, hlen]
    have hstep_cur : (step w ⟨GateOp.or, [cur, u]⟩).getD base false = (w.getD cur false || w.getD u false) := by
      rw [← hlen, step_getD_last]
      simp [gateEval, GateOp.eval]
    have hstep_us : ∀ v ∈ us, v < base + 1 := fun v hv => by
      have := hws v (List.mem_cons_of_mem u hv); omega
    rw [ih (base + 1) base (step w ⟨GateOp.or, [cur, u]⟩) hstep_len (by omega) hstep_us, hstep_cur]
    have hany : us.any (fun v => (step w ⟨GateOp.or, [cur, u]⟩).getD v false) =
        us.any (fun v => w.getD v false) := by
      apply Bool.eq_iff_iff.mpr
      simp only [List.any_eq_true]
      constructor
      · rintro ⟨v, hv, h⟩
        have hlt : v < w.length := by rw [hlen]; exact hws v (List.mem_cons_of_mem u hv)
        rw [step, List.getD_append _ _ _ _ hlt] at h
        exact ⟨v, hv, h⟩
      · rintro ⟨v, hv, h⟩
        have hlt : v < w.length := by rw [hlen]; exact hws v (List.mem_cons_of_mem u hv)
        exact ⟨v, hv, by rw [step, List.getD_append _ _ _ _ hlt]; exact h⟩
    rw [hany, Bool.or_assoc]

lemma orChain_out_is_cur_or_ge (base cur : ℕ) (ws : List ℕ) :
    (orChain base cur ws).2 = cur ∨ (base ≤ (orChain base cur ws).2 ∧ (orChain base cur ws).2 < base + ws.length) := by
  induction ws generalizing base cur with
  | nil => exact Or.inl rfl
  | cons u us ih =>
    simp only [orChain, List.length_cons]
    rcases ih (base + 1) base with h | ⟨h1, h2⟩
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩

lemma orChain_inputs_or (n lo base cur : ℕ) (ws : List ℕ)
    (hlo : lo ≤ base)
    (hcur : cur < n ∨ (lo ≤ cur ∧ cur < base)) (hws : ∀ u ∈ ws, u < n) :
    ∀ (k : ℕ) (hk : k < (orChain base cur ws).1.length) (w : ℕ),
      w ∈ ((orChain base cur ws).1[k]).inputs →
      w < n ∨ (lo ≤ w ∧ w < base + k) := by
  induction ws generalizing base cur with
  | nil => intro k hk; simp [orChain] at hk
  | cons u us ih =>
    intro k hk w hw
    cases k with
    | zero =>
      simp only [orChain, List.getElem_cons_zero, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · rcases hcur with h | ⟨h1, h2⟩
        · exact Or.inl h
        · exact Or.inr ⟨h1, by omega⟩
      · exact Or.inl (hws w (List.mem_cons_self ..))
    | succ k' =>
      simp only [orChain, List.getElem_cons_succ] at hw
      simp only [orChain, List.length_cons] at hk
      have hws' : ∀ v ∈ us, v < n := fun v hv => hws v (by simp [hv])
      have := ih (base + 1) base (by omega) (Or.inr ⟨by omega, by omega⟩) hws' k' (by omega) w hw
      rcases this with h | ⟨h1, h2⟩
      · exact Or.inl h
      · exact Or.inr ⟨h1, by omega⟩

def starGates {n : ℕ} (base : ℕ) (u : Fin n) (v0 : Fin n) (vs : List (Fin n)) : List Gate × ℕ :=
  let r := orChain base v0.val (vs.map Fin.val)
  (r.1 ++ [⟨GateOp.and, [u.val, r.2]⟩], base + vs.length)

lemma starGates_length {n : ℕ} (base : ℕ) (u v0 : Fin n) (vs : List (Fin n)) :
    (starGates base u v0 vs).1.length = vs.length + 1 := by
  simp [starGates, orChain_length]

lemma starGates_eval {n : ℕ} (base : ℕ) (u v0 : Fin n) (vs : List (Fin n))
    (w : List Bool) (x : Fin n → Bool)
    (hlen : w.length = base) (hge : n ≤ base)
    (hx : ∀ i : Fin n, w.getD i.val false = x i) :
    (run (starGates base u v0 vs).1 w).getD (starGates base u v0 vs).2 false =
      (x u && (x v0 || vs.any (fun v => x v))) := by
  simp only [starGates, run_append, run_cons, run_nil]
  have hrlen : (orChain base v0.val (vs.map Fin.val)).1.length = vs.length := by
    rw [orChain_length, List.length_map]
  have hw1len : (run (orChain base v0.val (vs.map Fin.val)).1 w).length = base + vs.length := by
    rw [run_length, hlen, hrlen]
  rw [← hw1len, step_getD_last]
  simp only [gateEval, GateOp.eval, List.map, List.all, id, Bool.and_true]
  have hu : (run (orChain base v0.val (vs.map Fin.val)).1 w).getD u.val false = x u := by
    have hult : u.val < w.length := by have := u.isLt; omega
    rw [run_getD_lt _ _ u.val hult, hx u]
  have hor : (run (orChain base v0.val (vs.map Fin.val)).1 w).getD (orChain base v0.val (vs.map Fin.val)).2 false =
      (x v0 || vs.any (fun v => x v)) := by
    have hv0lt : v0.val < base := by have := v0.isLt; omega
    rw [orChain_eval base v0.val (vs.map Fin.val) w hlen hv0lt
      (fun a ha => by rcases List.mem_map.mp ha with ⟨v, _, rfl⟩; have := v.isLt; omega), hx v0]
    congr 1
    rw [List.any_map]
    congr 1
    funext v
    exact hx v
  rw [hu, hor]

def buildStars {n : ℕ} : ℕ → List (Fin n × Fin n × List (Fin n)) → List Gate × List ℕ
  | _, [] => ([], [])
  | base, (u, v0, vs) :: rest =>
    let s := starGates base u v0 vs
    let r := buildStars (base + vs.length + 1) rest
    (s.1 ++ r.1, s.2 :: r.2)

def totalStarSize {n : ℕ} : List (Fin n × Fin n × List (Fin n)) → ℕ
  | [] => 0
  | (_, _, vs) :: rest => (vs.length + 1) + totalStarSize rest

lemma buildStars_length {n : ℕ} (base : ℕ) (ps : List (Fin n × Fin n × List (Fin n))) :
    (buildStars base ps).1.length = totalStarSize ps := by
  induction ps generalizing base with
  | nil => rfl
  | cons p ps ih =>
    rcases p with ⟨u, v0, vs⟩
    simp [buildStars, totalStarSize, starGates_length, ih]

lemma buildStars_outs_length {n : ℕ} (base : ℕ) (ps : List (Fin n × Fin n × List (Fin n))) :
    (buildStars base ps).2.length = ps.length := by
  induction ps generalizing base with
  | nil => rfl
  | cons p ps ih =>
    rcases p with ⟨u, v0, vs⟩
    simp [buildStars, ih]

lemma buildStars_outs_lt {n : ℕ} (base : ℕ) (ps : List (Fin n × Fin n × List (Fin n))) :
    ∀ w ∈ (buildStars base ps).2, w < base + totalStarSize ps := by
  induction ps generalizing base with
  | nil => intro w hw; simp [buildStars] at hw
  | cons p ps ih =>
    rcases p with ⟨u, v0, vs⟩
    intro w hw
    simp only [buildStars, List.mem_cons] at hw
    rcases hw with rfl | hw
    · simp [starGates, totalStarSize]; omega
    · have h := ih (base + vs.length + 1) w hw
      simp only [totalStarSize]
      omega

lemma buildStars_mono {n : ℕ} (base : ℕ) (ps : List (Fin n × Fin n × List (Fin n))) :
    ∀ g ∈ (buildStars base ps).1, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  induction ps generalizing base with
  | nil => intro g hg; simp [buildStars] at hg
  | cons p ps ih =>
    rcases p with ⟨u, v0, vs⟩
    intro g hg
    simp only [buildStars, List.mem_append] at hg
    rcases hg with hg | hg
    · simp only [starGates, List.mem_append, List.mem_singleton] at hg
      rcases hg with hg | rfl
      · have h := orChain_all_or base v0.val (vs.map Fin.val) g hg
        exact ⟨Or.inr h.1, by omega⟩
      · exact ⟨Or.inl rfl, by simp⟩
    · exact ih (base + vs.length + 1) g hg

lemma buildStars_eval {n : ℕ} (base : ℕ) (ps : List (Fin n × Fin n × List (Fin n)))
    (w : List Bool) (x : Fin n → Bool)
    (hlen : w.length = base) (hge : n ≤ base)
    (hx : ∀ i : Fin n, w.getD i.val false = x i) :
    (buildStars base ps).2.any (fun idx => (run (buildStars base ps).1 w).getD idx false) =
      ps.any (fun p => x p.1 && (x p.2.1 || p.2.2.any (fun v => x v))) := by
  induction ps generalizing base w with
  | nil => rfl
  | cons p ps ih =>
    rcases p with ⟨u, v0, vs⟩
    simp only [buildStars, run_append, List.any_cons]
    let w1 := run (starGates base u v0 vs).1 w
    have hw1len : w1.length = base + vs.length + 1 := by
      simp [w1, run_length, hlen, starGates_length]; omega
    have hw1x : ∀ i : Fin n, w1.getD i.val false = x i := fun i => by
      simp only [w1]
      rw [run_getD_lt _ _ i.val (by omega), hx i]
    have hhead : (run (buildStars (base + vs.length + 1) ps).1 w1).getD (starGates base u v0 vs).2 false =
        (x u && (x v0 || vs.any (fun v => x v))) := by
      rw [run_getD_lt _ _ _ (by simp [starGates, hw1len])]
      exact starGates_eval base u v0 vs w x hlen hge hx
    rw [hhead, ih (base + vs.length + 1) w1 hw1len (by omega) hw1x]

lemma buildStars_and_info {n : ℕ} (base : ℕ) (ps : List (Fin n × Fin n × List (Fin n)))
    (hge : n ≤ base) :
    ∀ (k : ℕ) (hk : k < (buildStars base ps).1.length),
      ((buildStars base ps).1[k]).op = GateOp.and →
      ∃ p ∈ ps,
        (∀ (w : List Bool) (x : Fin n → Bool),
          w.length = base → (∀ i : Fin n, w.getD i.val false = x i) →
          (run (buildStars base ps).1 w).getD (base + k) false = (x p.1 && (x p.2.1 || p.2.2.any (fun v => x v)))) := by
  induction ps generalizing base with
  | nil => intro k hk; simp [buildStars] at hk
  | cons p ps ih =>
    rcases p with ⟨u, v0, vs⟩
    intro k hk hop
    simp only [buildStars] at hk hop
    have hslen : (starGates base u v0 vs).1.length = vs.length + 1 := starGates_length base u v0 vs
    by_cases hlt : k < vs.length + 1
    · have hget : ((starGates base u v0 vs).1 ++ (buildStars (base + vs.length + 1) ps).1)[k] =
          (starGates base u v0 vs).1[k]'(by omega) := List.getElem_append_left (by omega)
      rw [hget] at hop
      by_cases hkl : k < vs.length
      · exfalso
        have horlen : (orChain base v0.val (vs.map Fin.val)).1.length = vs.length := by
          rw [orChain_length, List.length_map]
        have hget2 : (starGates base u v0 vs).1[k]'(by omega) =
            (orChain base v0.val (vs.map Fin.val)).1[k]'(by omega) := by
          simp only [starGates]
          exact List.getElem_append_left (by omega)
        rw [hget2] at hop
        have hmem : (orChain base v0.val (vs.map Fin.val)).1[k]'(by omega) ∈ (orChain base v0.val (vs.map Fin.val)).1 :=
          List.getElem_mem _
        have hor := (orChain_all_or base v0.val (vs.map Fin.val) _ hmem).1
        rw [hor] at hop
        cases hop
      · have hkeq : k = vs.length := by omega
        refine ⟨(u, v0, vs), List.mem_cons_self .., ?_⟩
        intro w x hlen hx
        simp only [buildStars, run_append]
        have hw1len : (run (starGates base u v0 vs).1 w).length = base + vs.length + 1 := by
          rw [run_length, hlen, hslen]; omega
        rw [hkeq, run_getD_lt _ _ (base + vs.length) (by omega)]
        exact starGates_eval base u v0 vs w x hlen hge hx
    · have hget : ((starGates base u v0 vs).1 ++ (buildStars (base + vs.length + 1) ps).1)[k] =
          (buildStars (base + vs.length + 1) ps).1[k - (vs.length + 1)]'(by rw [List.length_append, hslen] at hk; omega) := by
        rw [List.getElem_append_right (by omega)]
        congr 1; omega
      rw [hget] at hop
      have hk' : k - (vs.length + 1) < (buildStars (base + vs.length + 1) ps).1.length := by
        rw [List.length_append, hslen] at hk; omega
      obtain ⟨q, hq, hqeval⟩ := ih (base + vs.length + 1) (by omega) (k - (vs.length + 1)) hk' hop
      refine ⟨q, List.mem_cons_of_mem _ hq, ?_⟩
      intro w x hlen hx
      simp only [buildStars, run_append]
      let w1 := run (starGates base u v0 vs).1 w
      have hw1len : w1.length = base + vs.length + 1 := by
        simp [w1, run_length, hlen, hslen]; omega
      have hw1x : ∀ i : Fin n, w1.getD i.val false = x i := fun i => by
        simp only [w1]
        have hilt : i.val < w.length := by have := i.isLt; omega
        rw [run_getD_lt _ _ i.val hilt, hx i]
      have hidx : base + k = (base + vs.length + 1) + (k - (vs.length + 1)) := by omega
      rw [hidx]
      exact hqeval w1 x hw1len hw1x

lemma buildStars_inputs_only_or {n : ℕ} (base : ℕ) (ps : List (Fin n × Fin n × List (Fin n)))
    (hge : n ≤ base) :
    ∀ (k : ℕ) (hk : k < (buildStars base ps).1.length) (w : ℕ),
      w ∈ ((buildStars base ps).1[k]).inputs →
      w < n ∨ ∃ m : ℕ, m < k ∧ w = base + m ∧ ((buildStars base ps).1.getD m ⟨GateOp.or, []⟩).op = GateOp.or := by
  induction ps generalizing base with
  | nil => intro k hk; simp [buildStars] at hk
  | cons p ps ih =>
    rcases p with ⟨u, v0, vs⟩
    intro k hk w hw
    simp only [buildStars] at hk hw
    have hslen : (starGates base u v0 vs).1.length = vs.length + 1 := starGates_length base u v0 vs
    have horlen : (orChain base v0.val (vs.map Fin.val)).1.length = vs.length := by
      rw [orChain_length, List.length_map]
    by_cases hlt : k < vs.length + 1
    · have hget : ((starGates base u v0 vs).1 ++ (buildStars (base + vs.length + 1) ps).1)[k] =
          (starGates base u v0 vs).1[k]'(by omega) := List.getElem_append_left (by omega)
      rw [hget] at hw
      by_cases hkl : k < vs.length
      · have hget2 : (starGates base u v0 vs).1[k]'(by omega) =
            (orChain base v0.val (vs.map Fin.val)).1[k]'(by omega) := by
          simp only [starGates]
          exact List.getElem_append_left (by omega)
        rw [hget2] at hw
        have hin := orChain_inputs_or n base base v0.val (vs.map Fin.val) (le_refl base) (Or.inl v0.isLt)
          (fun a ha => by rcases List.mem_map.mp ha with ⟨v, _, rfl⟩; exact v.isLt) k (by omega) w hw
        rcases hin with h | ⟨h1, h2⟩
        · exact Or.inl h
        · right
          refine ⟨w - base, by omega, by omega, ?_⟩
          have hltm : w - base < (orChain base v0.val (vs.map Fin.val)).1.length := by omega
          simp only [buildStars, starGates]
          rw [List.getD_append _ _ _ _ (by simp [horlen]; omega), List.getD_append _ _ _ _ hltm,
              List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hltm, Option.getD_some]
          exact (orChain_all_or base v0.val (vs.map Fin.val) _ (List.getElem_mem hltm)).1
      · have hkeq : k = vs.length := by omega
        have hget2 : (starGates base u v0 vs).1[k]'(by omega) =
            ⟨GateOp.and, [u.val, (orChain base v0.val (vs.map Fin.val)).2]⟩ := by
          simp only [starGates]
          rw [List.getElem_append_right (by omega)]
          have : k - (orChain base v0.val (vs.map Fin.val)).1.length = 0 := by omega
          simp [this]
        rw [hget2] at hw
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl
        · exact Or.inl u.isLt
        · rcases orChain_out_is_cur_or_ge base v0.val (vs.map Fin.val) with h | ⟨h1, h2⟩
          · rw [h]; exact Or.inl v0.isLt
          · right
            rw [List.length_map] at h2
            refine ⟨(orChain base v0.val (vs.map Fin.val)).2 - base, by omega, by omega, ?_⟩
            have hltm : (orChain base v0.val (vs.map Fin.val)).2 - base < (orChain base v0.val (vs.map Fin.val)).1.length := by omega
            simp only [buildStars, starGates]
            rw [List.getD_append _ _ _ _ (by simp [horlen]; omega), List.getD_append _ _ _ _ hltm,
                List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hltm, Option.getD_some]
            exact (orChain_all_or base v0.val (vs.map Fin.val) _ (List.getElem_mem hltm)).1
    · have hget : ((starGates base u v0 vs).1 ++ (buildStars (base + vs.length + 1) ps).1)[k] =
          (buildStars (base + vs.length + 1) ps).1[k - (vs.length + 1)]'(by rw [List.length_append, hslen] at hk; omega) := by
        rw [List.getElem_append_right (by omega)]
        congr 1; omega
      rw [hget] at hw
      have hk' : k - (vs.length + 1) < (buildStars (base + vs.length + 1) ps).1.length := by
        rw [List.length_append, hslen] at hk; omega
      rcases ih (base + vs.length + 1) (by omega) (k - (vs.length + 1)) hk' w hw with h | ⟨m, hm1, hm2, hm3⟩
      · exact Or.inl h
      · right
        refine ⟨(vs.length + 1) + m, by omega, by omega, ?_⟩
        simp only [buildStars]
        rw [List.getD_append_right _ _ _ _ (by omega)]
        have hsub : (vs.length + 1) + m - (starGates base u v0 vs).1.length = m := by omega
        simpa [hsub] using hm3

lemma cones_foldl_len (n : ℕ) (gs : List Gate) (acc : List (List ℕ)) :
    (gs.foldl (coneStep n) acc).length = acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, coneStep, List.length_append, List.length_cons, List.length_nil]
    omega

lemma cones_foldl_getD_lt (n : ℕ) (gs : List Gate) (acc : List (List ℕ)) (i : ℕ) (hi : i < acc.length) :
    (gs.foldl (coneStep n) acc).getD i [] = acc.getD i [] := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (coneStep n acc g) (by simp [coneStep]; omega)]
    rw [coneStep, List.getD_append _ _ _ _ hi]

lemma cones_or_closed (n : ℕ) (gs : List Gate) (m : ℕ) (hm : m ≤ gs.length)
    (hclosed : ∀ (k : ℕ) (hk : k < m) (w : ℕ), w ∈ (gs.getD k ⟨GateOp.or, []⟩).inputs →
      w < n ∨ ∃ r : ℕ, r < k ∧ w = n + r ∧ (gs.getD r ⟨GateOp.or, []⟩).op = GateOp.or) :
    ∀ (j : ℕ), j < m → ∀ i ∈ (gs.foldl (coneStep n) []).getD j [],
      i < j ∧ (gs.getD i ⟨GateOp.or, []⟩).op = GateOp.or := by
  have hprefix : ∀ (t : ℕ) (ht : t ≤ m),
      ∀ (j : ℕ), j < t → ∀ i ∈ ((gs.take t).foldl (coneStep n) []).getD j [],
        i < j ∧ (gs.getD i ⟨GateOp.or, []⟩).op = GateOp.or := by
    intro t
    induction t with
    | zero => intro _ j hj; omega
    | succ t ih =>
      intro ht j hj i hi
      have htake : gs.take (t + 1) = gs.take t ++ [gs[t]'(by omega)] := List.take_succ_eq_append_getElem (by omega)
      rw [htake, List.foldl_append, List.foldl_cons, List.foldl_nil] at hi
      set cs := (gs.take t).foldl (coneStep n) []
      have hcslen : cs.length = t := by
        simp [cs, cones_foldl_len, List.length_take, Nat.min_eq_left (by omega : t ≤ gs.length)]
      by_cases hjt : j < t
      · rw [coneStep, List.getD_append _ _ _ _ (by omega)] at hi
        exact ih (by omega) j hjt i hi
      · have hjeq : j = t := by omega
        subst hjeq
        have hlast : (coneStep n cs (gs[j]'(by omega))).getD j [] =
            (((gs[j]'(by omega)).inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
              (fun w => (w - n) :: cs.getD (w - n) [])) := by
          have hjlen : j = cs.length := hcslen.symm
          simp only [coneStep, hjlen, List.getD_eq_getElem?_getD]
          simp
        rw [hlast] at hi
        rw [List.mem_flatMap] at hi
        rcases hi with ⟨w, hw, hiw⟩
        rw [List.mem_filter, decide_eq_true_eq] at hw
        have hgetj : gs.getD j ⟨GateOp.or, []⟩ = gs[j]'(by omega) := by
          simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : j < gs.length)]
        have hw' : w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs := by rw [hgetj]; exact hw.1
        rcases hclosed j (by omega) w hw' with hlt | ⟨r, hr1, hr2, hr3⟩
        · omega
        · have hwn : w - n = r := by omega
          rw [hwn, List.mem_cons] at hiw
          rcases hiw with rfl | hiw
          · exact ⟨hr1, hr3⟩
          · have hrec := ih (by omega) r hr1 i hiw
            exact ⟨by omega, hrec.2⟩
  intro j hj i hi
  have hsplit : gs = gs.take m ++ gs.drop m := (List.take_append_drop m gs).symm
  rw [hsplit, List.foldl_append] at hi
  have hlen : ((gs.take m).foldl (coneStep n) []).length = m := by
    simp [cones_foldl_len, List.length_take, Nat.min_eq_left hm]
  rw [cones_foldl_getD_lt n (gs.drop m) _ j (by omega)] at hi
  exact hprefix m (le_refl m) j hj i hi

def extractStars {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    List (Fin n) → List (Fin n × Fin n × List (Fin n))
  | [] => []
  | u :: rest =>
    match (List.finRange n).filter (fun v => decide (G.Adj u v ∧ v ∉ rest)) with
    | [] => extractStars G rest
    | v0 :: vs => (u, v0, vs) :: extractStars G rest

lemma extractStars_length_le {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (L : List (Fin n)) :
    (extractStars G L).length ≤ L.length := by
  induction L with
  | nil => simp [extractStars]
  | cons u rest ih =>
    simp only [extractStars]
    cases (List.finRange n).filter (fun v => decide (G.Adj u v ∧ v ∉ rest)) with
    | nil => simp; omega
    | cons v0 vs => simp; omega

lemma extractStars_adj {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (L : List (Fin n)) :
    ∀ p ∈ extractStars G L, G.Adj p.1 p.2.1 ∧ ∀ v ∈ p.2.2, G.Adj p.1 v := by
  induction L with
  | nil => intro p hp; simp [extractStars] at hp
  | cons u rest ih =>
    intro p hp
    simp only [extractStars] at hp
    generalize hf : (List.finRange n).filter (fun v => decide (G.Adj u v ∧ v ∉ rest)) = fl at hp
    cases fl with
    | nil => exact ih p hp
    | cons v0 vs =>
      simp only [List.mem_cons] at hp
      rcases hp with rfl | hp
      · have hv0 : v0 ∈ (List.finRange n).filter (fun v => decide (G.Adj u v ∧ v ∉ rest)) := by
          rw [hf]; exact List.mem_cons_self ..
        rw [List.mem_filter, decide_eq_true_eq] at hv0
        refine ⟨hv0.2.1, fun v hv => ?_⟩
        have hvm : v ∈ (List.finRange n).filter (fun v => decide (G.Adj u v ∧ v ∉ rest)) := by
          rw [hf]; exact List.mem_cons_of_mem v0 hv
        rw [List.mem_filter, decide_eq_true_eq] at hvm
        exact hvm.2.1
      · exact ih p hp

lemma extractStars_covers {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (L : List (Fin n))
    (hnodup : L.Nodup) (a b : Fin n) (hadj : G.Adj a b) (hcov : a ∈ L ∨ b ∈ L) :
    ∃ p ∈ extractStars G L,
      (p.1 = a ∧ (p.2.1 = b ∨ b ∈ p.2.2)) ∨ (p.1 = b ∧ (p.2.1 = a ∨ a ∈ p.2.2)) := by
  induction L with
  | nil => simp at hcov
  | cons u rest ih =>
    have hnodup' : u ∉ rest ∧ rest.Nodup := List.nodup_cons.mp hnodup
    by_cases hrest : a ∈ rest ∨ b ∈ rest
    · obtain ⟨p, hp, hrel⟩ := ih hnodup'.2 hrest
      refine ⟨p, ?_, hrel⟩
      simp only [extractStars]
      cases (List.finRange n).filter (fun v => decide (G.Adj u v ∧ v ∉ rest)) with
      | nil => exact hp
      | cons v0 vs => exact List.mem_cons_of_mem _ hp
    · have ha_not : a ∉ rest := fun h => hrest (Or.inl h)
      have hb_not : b ∉ rest := fun h => hrest (Or.inr h)
      simp only [List.mem_cons] at hcov
      rcases hcov with (rfl | ha) | (rfl | hb)
      · have hbm : b ∈ (List.finRange n).filter (fun v => decide (G.Adj a v ∧ v ∉ rest)) := by
          rw [List.mem_filter, decide_eq_true_eq]
          exact ⟨List.mem_finRange b, hadj, hb_not⟩
        generalize hf : (List.finRange n).filter (fun v => decide (G.Adj a v ∧ v ∉ rest)) = fl
        rw [hf] at hbm
        cases fl with
        | nil => simp at hbm
        | cons v0 vs =>
          refine ⟨(a, v0, vs), ?_, Or.inl ⟨rfl, (List.mem_cons.mp hbm).imp Eq.symm id⟩⟩
          simp only [extractStars, hf]
          exact List.mem_cons_self ..
      · exact (ha_not ha).elim
      · have ham : a ∈ (List.finRange n).filter (fun v => decide (G.Adj b v ∧ v ∉ rest)) := by
          rw [List.mem_filter, decide_eq_true_eq]
          exact ⟨List.mem_finRange a, hadj.symm, ha_not⟩
        generalize hf : (List.finRange n).filter (fun v => decide (G.Adj b v ∧ v ∉ rest)) = fl
        rw [hf] at ham
        cases fl with
        | nil => simp at ham
        | cons v0 vs =>
          refine ⟨(b, v0, vs), ?_, Or.inr ⟨rfl, (List.mem_cons.mp ham).imp Eq.symm id⟩⟩
          simp only [extractStars, hf]
          exact List.mem_cons_self ..
      · exact (hb_not hb).elim

def starEdgesList {n : ℕ} : List (Fin n × Fin n × List (Fin n)) → List (Sym2 (Fin n))
  | [] => []
  | (u, v0, vs) :: rest => (v0 :: vs).map (fun v => s(u, v)) ++ starEdgesList rest

lemma starEdgesList_length {n : ℕ} (ps : List (Fin n × Fin n × List (Fin n))) :
    (starEdgesList ps).length = totalStarSize ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    rcases p with ⟨u, v0, vs⟩
    simp [starEdgesList, totalStarSize, ih]
    omega

lemma extractStars_edges_nodup_and_mem {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (L : List (Fin n)) (hnodup : L.Nodup) :
    (starEdgesList (extractStars G L)).Nodup ∧
      (∀ e ∈ starEdgesList (extractStars G L), e ∈ G.edgeFinset) ∧
      (∀ e ∈ starEdgesList (extractStars G L), ∃ u ∈ L, u ∈ e) := by
  induction L with
  | nil => simp [extractStars, starEdgesList]
  | cons u rest ih =>
    have hnodup' : u ∉ rest ∧ rest.Nodup := List.nodup_cons.mp hnodup
    obtain ⟨hnd, hmem, hhit⟩ := ih hnodup'.2
    simp only [extractStars]
    generalize hf : (List.finRange n).filter (fun v => decide (G.Adj u v ∧ v ∉ rest)) = fl
    cases fl with
    | nil =>
      exact ⟨hnd, hmem, fun e he => by
        obtain ⟨w, hw, hwe⟩ := hhit e he
        exact ⟨w, List.mem_cons_of_mem u hw, hwe⟩⟩
    | cons v0 vs =>
      have hfl_nodup : (v0 :: vs).Nodup := by
        rw [← hf]
        exact (List.nodup_finRange n).filter _
      have hfl_prop : ∀ v ∈ v0 :: vs, G.Adj u v ∧ v ∉ rest := by
        intro v hv
        rw [← hf, List.mem_filter, decide_eq_true_eq] at hv
        exact hv.2
      simp only [starEdgesList]
      refine ⟨?_, ?_, ?_⟩
      · rw [List.nodup_append]
        refine ⟨?_, hnd, ?_⟩
        · apply List.Nodup.map _ hfl_nodup
          intro x y hxy
          rw [Sym2.eq_iff] at hxy
          rcases hxy with ⟨_, rfl⟩ | ⟨rfl, rfl⟩
          · rfl
          · rfl
        · intro e1 he1 e2 he2 hEq
          subst hEq
          rcases List.mem_map.mp he1 with ⟨v, hv, rfl⟩
          obtain ⟨w, hwrest, hwe⟩ := hhit s(u, v) he2
          rw [Sym2.mem_iff] at hwe
          rcases hwe with hwu | hwv
          · exact hnodup'.1 (hwu ▸ hwrest)
          · exact (hfl_prop v hv).2 (hwv ▸ hwrest)
      · intro e he
        rw [List.mem_append] at he
        rcases he with he | he
        · rcases List.mem_map.mp he with ⟨v, hv, rfl⟩
          exact SimpleGraph.mem_edgeFinset.mpr (hfl_prop v hv).1
        · exact hmem e he
      · intro e he
        rw [List.mem_append] at he
        rcases he with he | he
        · rcases List.mem_map.mp he with ⟨v, _, rfl⟩
          exact ⟨u, List.mem_cons_self .., by simp⟩
        · obtain ⟨w, hw, hwe⟩ := hhit e he
          exact ⟨w, List.mem_cons_of_mem u hw, hwe⟩

lemma totalStarSize_le_ncard {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (L : List (Fin n)) (hnodup : L.Nodup) :
    totalStarSize (extractStars G L) ≤ G.edgeSet.ncard := by
  obtain ⟨hnd, hmem, _⟩ := extractStars_edges_nodup_and_mem G L hnodup
  have h1 : (starEdgesList (extractStars G L)).length = (starEdgesList (extractStars G L)).toFinset.card :=
    (List.toFinset_card_of_nodup hnd).symm
  have hsub : (starEdgesList (extractStars G L)).toFinset ⊆ G.edgeFinset := by
    intro e he
    exact hmem e (List.mem_toFinset.mp he)
  have h2 : (starEdgesList (extractStars G L)).toFinset.card ≤ G.edgeFinset.card :=
    Finset.card_le_card hsub
  have h3 : G.edgeFinset.card = G.edgeSet.ncard := by
    rw [← Set.ncard_coe_finset G.edgeFinset, SimpleGraph.coe_edgeFinset]
  rw [← starEdgesList_length, h1, ← h3]
  exact h2

end PEqualNP.Outside.L_meta_5355

theorem PEqualNP.Outside.L_meta_5355 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover x2 x4 → ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x6 ∧ PEqualNP.MetaComplexity.circuitFun x1 x6 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ ∧ x6.size ≤ x2.edgeSet.ncard + x4.card - (1 : ℕ) ∧ ∀ x7 < x6.size, (PEqualNP.MetaComplexity.NestedCover.gateAt x6 x7).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x10 : Fin x1) (x11 : Fin x1), x2.Adj x10 x11 ∧ PEqualNP.EdgeOwnership.Owns x1 x6 x7 x10 x11 := by
  intro n G inst S hcov
  let L := S.toList
  have hLnodup : L.Nodup := Finset.nodup_toList S
  have hLlen : L.length = S.card := Finset.length_toList S
  let ps := PEqualNP.Outside.L_meta_5355.extractStars G L
  have hps_adj := PEqualNP.Outside.L_meta_5355.extractStars_adj G L
  have hps_len : ps.length ≤ S.card := by
    rw [← hLlen]
    exact PEqualNP.Outside.L_meta_5355.extractStars_length_le G L
  have hps_size : PEqualNP.Outside.L_meta_5355.totalStarSize ps ≤ G.edgeSet.ncard :=
    PEqualNP.Outside.L_meta_5355.totalStarSize_le_ncard G L hLnodup
  have hps_cov : ∀ a b : Fin n, G.Adj a b →
      ∃ p ∈ ps, (p.1 = a ∧ (p.2.1 = b ∨ b ∈ p.2.2)) ∨ (p.1 = b ∧ (p.2.1 = a ∨ a ∈ p.2.2)) := by
    intro a b hab
    have hmem : a ∈ L ∨ b ∈ L := by
      rcases hcov a b hab with ha | hb
      · exact Or.inl (Finset.mem_toList.mpr ha)
      · exact Or.inr (Finset.mem_toList.mpr hb)
    exact PEqualNP.Outside.L_meta_5355.extractStars_covers G L hLnodup a b hab hmem
  cases hps : ps with
  | nil =>
    refine ⟨{ gates := [], output := n }, ?_, ?_, ?_, ?_⟩
    · intro g hg; simp at hg
    · funext x
      have hnoedge : ∀ a b : Fin n, ¬ G.Adj a b := by
        intro a b hab
        obtain ⟨p, hp, _⟩ := hps_cov a b hab
        rw [hps] at hp
        simp at hp
      have heval : PEqualNP.MetaComplexity.circuitFun n { gates := [], output := n } x = false := by
        simp [PEqualNP.MetaComplexity.circuitFun, PEqualNP.CircuitLowerBounds.Circuit.eval,
              PEqualNP.CircuitLowerBounds.Circuit.wires, List.getD_eq_default]
      have hgf : PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = false := by
        simp only [PEqualNP.MetaComplexity.NestedCover.graphFun, Finset.notMem_empty, false_and,
                   exists_false, decide_false, Bool.false_or, decide_eq_false_iff_not]
        rintro ⟨a, b, hab, _, _⟩
        exact hnoedge a b hab
      rw [heval, hgf]
    · simp [PEqualNP.CircuitLowerBounds.Circuit.size]
    · intro j hj; simp [PEqualNP.CircuitLowerBounds.Circuit.size] at hj
  | cons p0 ps' =>
    let bs := PEqualNP.Outside.L_meta_5355.buildStars n ps
    have hbs_len : bs.1.length = PEqualNP.Outside.L_meta_5355.totalStarSize ps :=
      PEqualNP.Outside.L_meta_5355.buildStars_length n ps
    have hbs_outs_len : bs.2.length = ps.length :=
      PEqualNP.Outside.L_meta_5355.buildStars_outs_length n ps
    cases houts : bs.2 with
    | nil =>
      rw [houts, hps] at hbs_outs_len
      simp at hbs_outs_len
    | cons w0 ws =>
      let top := PEqualNP.Outside.L_meta_5355.orChain (n + bs.1.length) w0 ws
      let C : PEqualNP.CircuitLowerBounds.Circuit := { gates := bs.1 ++ top.1, output := top.2 }
      refine ⟨C, ?_, ?_, ?_, ?_⟩
      · intro g hg
        simp only [C, List.mem_append] at hg
        rcases hg with hg | hg
        · exact PEqualNP.Outside.L_meta_5355.buildStars_mono n ps g hg
        · have h := PEqualNP.Outside.L_meta_5355.orChain_all_or (n + bs.1.length) w0 ws g hg
          exact ⟨Or.inr h.1, by omega⟩
      · funext x
        have hCeval : PEqualNP.MetaComplexity.circuitFun n C x =
            ps.any (fun p => x p.1 && (x p.2.1 || p.2.2.any (fun v => x v))) := by
          change (PEqualNP.Outside.L_meta_5355.run (bs.1 ++ top.1) (List.ofFn x)).getD top.2 false = _
          rw [PEqualNP.Outside.L_meta_5355.run_append]
          let w1 := PEqualNP.Outside.L_meta_5355.run bs.1 (List.ofFn x)
          have hw1len : w1.length = n + bs.1.length := by
            simp [w1, PEqualNP.Outside.L_meta_5355.run_length]
          have hw0 : w0 < n + bs.1.length := by
            rw [hbs_len]
            exact PEqualNP.Outside.L_meta_5355.buildStars_outs_lt n ps w0 (by rw [houts]; exact List.mem_cons_self ..)
          have hws : ∀ u ∈ ws, u < n + bs.1.length := by
            intro u hu
            rw [hbs_len]
            exact PEqualNP.Outside.L_meta_5355.buildStars_outs_lt n ps u (by rw [houts]; exact List.mem_cons_of_mem w0 hu)
          rw [PEqualNP.Outside.L_meta_5355.orChain_eval (n + bs.1.length) w0 ws w1 hw1len hw0 hws]
          have hbe := PEqualNP.Outside.L_meta_5355.buildStars_eval n ps (List.ofFn x) x
            (by simp) (le_refl n) (fun i => by simp [List.getD_eq_getElem?_getD])
          rw [← hbe]
          change (w1.getD w0 false || ws.any (fun u => w1.getD u false)) = bs.2.any (fun idx => w1.getD idx false)
          rw [houts, List.any_cons]
        rw [hCeval]
        have hgf : PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x =
            decide (∃ a b : Fin n, G.Adj a b ∧ x a = true ∧ x b = true) := by
          simp [PEqualNP.MetaComplexity.NestedCover.graphFun]
        rw [hgf]
        apply Bool.eq_iff_iff.mpr
        rw [List.any_eq_true, decide_eq_true_eq]
        constructor
        · rintro ⟨p, hp, hpx⟩
          rw [Bool.and_eq_true, Bool.or_eq_true, List.any_eq_true] at hpx
          rcases hpx with ⟨hx1, hx2 | ⟨v, hv, hxv⟩⟩
          · exact ⟨p.1, p.2.1, (hps_adj p hp).1, hx1, hx2⟩
          · exact ⟨p.1, v, (hps_adj p hp).2 v hv, hx1, hxv⟩
        · rintro ⟨a, b, hab, hxa, hxb⟩
          obtain ⟨p, hp, hrel⟩ := hps_cov a b hab
          refine ⟨p, hp, ?_⟩
          rw [Bool.and_eq_true, Bool.or_eq_true, List.any_eq_true]
          rcases hrel with ⟨rfl, rfl | hb⟩ | ⟨rfl, rfl | ha⟩
          · exact ⟨hxa, Or.inl hxb⟩
          · exact ⟨hxa, Or.inr ⟨b, hb, hxb⟩⟩
          · exact ⟨hxb, Or.inl hxa⟩
          · exact ⟨hxb, Or.inr ⟨a, ha, hxa⟩⟩
      · have htop_len : top.1.length = ws.length :=
          PEqualNP.Outside.L_meta_5355.orChain_length (n + bs.1.length) w0 ws
        have hws_len : ws.length + 1 = ps.length := by
          rw [← hbs_outs_len, houts, List.length_cons]
        have hps_pos : 1 ≤ ps.length := by rw [hps]; simp
        change (bs.1 ++ top.1).length ≤ G.edgeSet.ncard + S.card - 1
        rw [List.length_append, hbs_len, htop_len]
        omega
      · intro j hj hop
        have hjlt_bs : j < bs.1.length := by
          by_contra hge
          have hgt : bs.1.length ≤ j := by omega
          have hjC : j < C.gates.length := hj
          have htop_lt : j - bs.1.length < top.1.length := by
            simp only [C, List.length_append] at hjC; omega
          have hget : PEqualNP.MetaComplexity.NestedCover.gateAt C j = top.1[j - bs.1.length]'htop_lt := by
            simp only [PEqualNP.MetaComplexity.NestedCover.gateAt, C, List.getD_eq_getElem?_getD,
                       List.getElem?_eq_getElem hjC, Option.getD_some]
            exact List.getElem_append_right hgt
          rw [hget] at hop
          have hor := (PEqualNP.Outside.L_meta_5355.orChain_all_or (n + bs.1.length) w0 ws
            (top.1[j - bs.1.length]'htop_lt) (List.getElem_mem htop_lt)).1
          rw [hor] at hop
          cases hop
        have hgetj : PEqualNP.MetaComplexity.NestedCover.gateAt C j = bs.1[j] := by
          have hjC : j < C.gates.length := hj
          simp only [PEqualNP.MetaComplexity.NestedCover.gateAt, C, List.getD_eq_getElem?_getD,
                     List.getElem?_eq_getElem hjC, Option.getD_some]
          exact List.getElem_append_left hjlt_bs
        have hop_bs : bs.1[j].op = PEqualNP.CircuitLowerBounds.GateOp.and := by
          rw [← hgetj]; exact hop
        obtain ⟨p, hp, hpeval⟩ := PEqualNP.Outside.L_meta_5355.buildStars_and_info n ps (le_refl n) j hjlt_bs hop_bs
        refine ⟨p.1, p.2.1, (hps_adj p hp).1, hj, hop, ?_, ?_⟩
        · change (PEqualNP.Outside.L_meta_5355.run (bs.1 ++ top.1) (List.ofFn (PEqualNP.EdgeOwnership.pairInput p.1 p.2.1))).getD (n + j) false = true
          rw [PEqualNP.Outside.L_meta_5355.run_append]
          have hw1len : (PEqualNP.Outside.L_meta_5355.run bs.1 (List.ofFn (PEqualNP.EdgeOwnership.pairInput p.1 p.2.1))).length = n + bs.1.length := by
            simp [PEqualNP.Outside.L_meta_5355.run_length]
          rw [PEqualNP.Outside.L_meta_5355.run_getD_lt _ _ (n + j) (by omega)]
          rw [hpeval (List.ofFn (PEqualNP.EdgeOwnership.pairInput p.1 p.2.1)) (PEqualNP.EdgeOwnership.pairInput p.1 p.2.1)
            (by simp) (fun i => by simp [List.getD_eq_getElem?_getD])]
          simp [PEqualNP.EdgeOwnership.pairInput]
        · intro i hij hcone hiand
          exfalso
          have hclosed : ∀ (k : ℕ) (hk : k < bs.1.length) (w : ℕ),
              w ∈ (C.gates.getD k ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).inputs →
              w < n ∨ ∃ r : ℕ, r < k ∧ w = n + r ∧
                (C.gates.getD r ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).op = PEqualNP.CircuitLowerBounds.GateOp.or := by
            intro k hk w hw
            have hgk : C.gates.getD k ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ = bs.1[k] := by
              simp only [C]
              rw [List.getD_append _ _ _ _ hk, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
            rw [hgk] at hw
            rcases PEqualNP.Outside.L_meta_5355.buildStars_inputs_only_or n ps (le_refl n) k hk w hw with h | ⟨r, hr1, hr2, hr3⟩
            · exact Or.inl h
            · right
              refine ⟨r, hr1, hr2, ?_⟩
              have hgr : C.gates.getD r ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ =
                  bs.1.getD r ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ := by
                simp only [C]
                exact List.getD_append _ _ _ _ (by omega)
              rw [hgr]
              exact hr3
          have hor := (PEqualNP.Outside.L_meta_5355.cones_or_closed n C.gates bs.1.length (by simp [C]) hclosed j hjlt_bs i hcone).2
          change (C.gates.getD i ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).op = PEqualNP.CircuitLowerBounds.GateOp.and at hiand
          rw [hor] at hiand
          cases hiand
