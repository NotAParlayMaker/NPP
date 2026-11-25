import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6337

/-! Part 1: pools, live chains, and the order normal form (generic in the value type). -/

section Pool

variable {α : Type} [DecidableEq α]

/-- From the pool `P`, adding at most `k` values, each produced by `op` from two distinct pool
members, the target `t` enters the pool. -/
def Reach (op : α → α → Finset α) (t : α) : ℕ → Finset α → Prop
  | 0, P => t ∈ P
  | k + 1, P => Reach op t k P ∨
      ∃ x ∈ P, ∃ y ∈ P, x ≠ y ∧ ∃ z ∈ op x y, Reach op t k (insert z P)

theorem reach_mono {op : α → α → Finset α} {t : α} {k : ℕ} {P Q : Finset α}
    (hPQ : P ⊆ Q) (h : Reach op t k P) : Reach op t k Q := by
  induction k generalizing P Q with
  | zero => exact hPQ h
  | succ k ih =>
    rcases h with h | ⟨x, hx, y, hy, hxy, z, hz, h⟩
    · exact Or.inl (ih hPQ h)
    · exact Or.inr ⟨x, hPQ hx, y, hPQ hy, hxy, z, hz, ih (Finset.insert_subset_insert z hPQ) h⟩

theorem reach_le {op : α → α → Finset α} {t : α} {j k : ℕ} {P : Finset α}
    (hjk : j ≤ k) (h : Reach op t j P) : Reach op t k P := by
  induction hjk with
  | refl => exact h
  | step _ ih => exact Or.inl ih

/-- A run of steps that keeps exactly the live values: each step reads two distinct live values,
which stay live only when they lie in the remainder, and adds one value that was not live;
at the end only the target is live. -/
def Live (op : α → α → Finset α) (t : α) : List (α × α × α) → Finset α → Prop
  | [], L => L = {t}
  | (x, y, z) :: gs, L => x ∈ L ∧ y ∈ L ∧ x ≠ y ∧ z ∈ op x y ∧ z ∉ L ∧
      ∃ R : Finset α, L = insert x (insert y R) ∧ Live op t gs (insert z R)

theorem reach_live {op : α → α → Finset α} {t : α} {k : ℕ} {P : Finset α}
    (h : Reach op t k P) : ∃ gs : List (α × α × α), gs.length ≤ k ∧ ∃ L ⊆ P, Live op t gs L := by
  induction k generalizing P with
  | zero => exact ⟨[], le_refl 0, {t}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with h | ⟨x, hx, y, hy, hxy, z, hz, h⟩
    · obtain ⟨gs, hl, L, hL, hr⟩ := ih h
      exact ⟨gs, Nat.le_succ_of_le hl, L, hL, hr⟩
    · obtain ⟨gs, hl, L, hL, hr⟩ := ih h
      by_cases hsub : L ⊆ P
      · exact ⟨gs, Nat.le_succ_of_le hl, L, hsub, hr⟩
      · have hzL : z ∈ L := by
          by_contra hn
          apply hsub
          intro u hu
          rcases Finset.mem_insert.mp (hL hu) with rfl | hu'
          · exact absurd hu hn
          · exact hu'
        have hzP : z ∉ P := fun hm => hsub ((Finset.insert_eq_of_mem hm) ▸ hL)
        have hR : L.erase z ⊆ P := by
          intro u hu
          obtain ⟨hne, hu⟩ := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (hL hu)).resolve_left hne
        have hS : insert x (insert y (L.erase z)) ⊆ P :=
          Finset.insert_subset hx (Finset.insert_subset hy hR)
        refine ⟨(x, y, z) :: gs, Nat.succ_le_succ hl, _, hS, by simp, by simp, hxy, hz,
          fun hm => hzP (hS hm), L.erase z, rfl, ?_⟩
        rwa [Finset.insert_erase hzL]

theorem live_reach {op : α → α → Finset α} {t : α} {gs : List (α × α × α)} {L : Finset α}
    (h : Live op t gs L) : Reach op t gs.length L := by
  induction gs generalizing L with
  | nil => change L = {t} at h; simp [Reach, h]
  | cons g gs ih =>
    obtain ⟨x, y, z⟩ := g
    obtain ⟨hx, hy, hxy, hz, _, R, hL, h⟩ := h
    refine Or.inr ⟨x, hx, y, hy, hxy, z, hz, reach_mono ?_ (ih h)⟩
    intro u hu
    rw [hL]
    rcases Finset.mem_insert.mp hu with rfl | hu
    · exact Finset.mem_insert_self u _
    · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu))

theorem live_card {op : α → α → Finset α} {t : α} {gs : List (α × α × α)} {L : Finset α}
    (h : Live op t gs L) : L.card ≤ gs.length + 1 := by
  induction gs generalizing L with
  | nil => change L = {t} at h; simp [h]
  | cons g gs ih =>
    obtain ⟨x, y, z⟩ := g
    obtain ⟨_, _, _, _, hn, R, rfl, h⟩ := h
    have hzR : z ∉ R := fun hm => hn (by simp [hm])
    have h0 := ih h
    rw [Finset.card_insert_of_notMem hzR] at h0
    have h1 := Finset.card_insert_le x (insert y R)
    have h2 := Finset.card_insert_le y R
    simp only [List.length_cons]
    omega

/-- A property of the target that every step can only inherit from one of its two operands
holds for some live value at every stage. -/
theorem live_witness {op : α → α → Finset α} {t : α} (D : α → Prop)
    (ht : D t) (hop : ∀ x y, ∀ z ∈ op x y, D z → D x ∨ D y)
    {gs : List (α × α × α)} {L : Finset α} (h : Live op t gs L) : ∃ w ∈ L, D w := by
  induction gs generalizing L with
  | nil => change L = {t} at h; exact ⟨t, by simp [h], ht⟩
  | cons g gs ih =>
    obtain ⟨x, y, z⟩ := g
    obtain ⟨hx, hy, _, hz, _, R, rfl, h⟩ := h
    obtain ⟨w, hw, hD⟩ := ih h
    rcases Finset.mem_insert.mp hw with rfl | hw
    · rcases hop x y w hz hD with hd | hd
      · exact ⟨x, hx, hd⟩
      · exact ⟨y, hy, hd⟩
    · exact ⟨w, by simp [hw], hD⟩

/-- Two adjacent steps where the second does not read the output of the first can be
exchanged, unless the second output is already live (then one step can be saved). -/
theorem live_swap {op : α → α → Finset α} {t : α}
    {g h : α × α × α} {gs : List (α × α × α)} {L : Finset α}
    (hl : Live op t (g :: h :: gs) L) (h1 : h.1 ≠ g.2.2) (h2 : h.2.1 ≠ g.2.2) :
    Live op t (h :: g :: gs) L ∨ Reach op t (gs.length + 1) L := by
  obtain ⟨x₁, y₁, z₁⟩ := g
  obtain ⟨x₂, y₂, z₂⟩ := h
  obtain ⟨hx₁, hy₁, hxy₁, hz₁, hn₁, R₁, hL, hx₂, hy₂, hxy₂, hz₂, hn₂, R₂, hR, tail⟩ := hl
  dsimp only at h1 h2
  have hzR₂ : z₁ ∈ R₂ := by
    have hm : z₁ ∈ insert x₂ (insert y₂ R₂) := hR ▸ Finset.mem_insert_self z₁ R₁
    rcases Finset.mem_insert.mp hm with e | hm
    · exact absurd e.symm h1
    · rcases Finset.mem_insert.mp hm with e | hm
      · exact absurd e.symm h2
      · exact hm
  set M := R₂.erase z₁ with hM
  have hMeq : insert z₁ M = R₂ := Finset.insert_erase hzR₂
  have hzM : z₁ ∉ M := Finset.notMem_erase z₁ R₂
  have hzR₁ : z₁ ∉ R₁ := fun hm =>
    hn₁ (hL ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
  have hR₁ : R₁ = insert x₂ (insert y₂ M) := by
    ext u
    by_cases hu : u = z₁
    · subst hu
      simp [hzR₁, h1.symm, h2.symm, hzM]
    · have hmem : u ∈ insert z₁ R₁ ↔ u ∈ insert x₂ (insert y₂ (insert z₁ M)) := by
        rw [hMeq, hR]
      simp [hu] at hmem
      simpa using hmem
  by_cases hz₂L : z₂ ∈ L
  · right
    refine Or.inr ⟨x₁, hx₁, y₁, hy₁, hxy₁, z₁, hz₁, reach_mono ?_ (live_reach tail)⟩
    intro u hu
    rcases Finset.mem_insert.mp hu with rfl | hu
    · exact Finset.mem_insert_of_mem hz₂L
    · rw [← hMeq] at hu
      rcases Finset.mem_insert.mp hu with rfl | hu
      · exact Finset.mem_insert_self u L
      · rw [hL, hR₁]
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu))))
  · left
    have hL' : L = insert x₂ (insert y₂ (insert x₁ (insert y₁ M))) := by
      rw [hL, hR₁]
      ext u; simp [or_left_comm]
    have hz₁₂ : z₁ ≠ z₂ := fun e => hn₂ (e ▸ Finset.mem_insert_self z₁ R₁)
    have hswap : insert z₂ (insert x₁ (insert y₁ M)) = insert x₁ (insert y₁ (insert z₂ M)) := by
      ext u; simp [or_left_comm]
    have hz₁out : z₁ ∉ insert z₂ (insert x₁ (insert y₁ M)) := by
      intro hm
      rcases Finset.mem_insert.mp hm with e | hm
      · exact hz₁₂ e
      · exact hn₁ (hL' ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    refine ⟨by rw [hL']; simp, by rw [hL']; simp, hxy₂, hz₂, hz₂L, insert x₁ (insert y₁ M), hL',
      by rw [hswap]; simp, by rw [hswap]; simp, hxy₁, hz₁, hz₁out, insert z₂ M, hswap, ?_⟩
    have hfin : insert z₁ (insert z₂ M) = insert z₂ R₂ := by
      rw [← hMeq, Finset.insert_comm]
    simpa only [hfin] using tail

/-- The order normal form: a step either reads the previous output or has an output whose key
is at least the previous output key. -/
def Ordered (key : α → ℕ) : ℕ → List (α × α × α) → Prop
  | _, [] => True
  | prev, (x, y, z) :: gs => (key x = prev ∨ key y = prev ∨ prev ≤ key z) ∧ Ordered key (key z) gs

/-- Number of pairs of steps whose outputs are out of key order. -/
def disorder (key : α → ℕ) : List (α × α × α) → ℕ
  | [] => 0
  | g :: gs => (gs.filter (fun h => decide (key h.2.2 < key g.2.2))).length + disorder key gs

omit [DecidableEq α] in
theorem disorder_swap (key : α → ℕ) (pre suf : List (α × α × α)) (g h : α × α × α)
    (hlt : key h.2.2 < key g.2.2) :
    disorder key (pre ++ h :: g :: suf) < disorder key (pre ++ g :: h :: suf) := by
  induction pre with
  | nil =>
    simp only [List.nil_append, disorder, List.filter_cons]
    have e1 : decide (key h.2.2 < key g.2.2) = true := decide_eq_true hlt
    have e2 : decide (key g.2.2 < key h.2.2) = false := decide_eq_false (by omega)
    simp only [e1, e2, ↓reduceIte, Bool.false_eq_true, List.length_cons]
    omega
  | cons x xs ih =>
    simp only [List.cons_append, disorder]
    have hp : (xs ++ h :: g :: suf).Perm (xs ++ g :: h :: suf) :=
      List.Perm.append_left xs (List.Perm.swap g h suf)
    have hl : ((xs ++ h :: g :: suf).filter (fun u => decide (key u.2.2 < key x.2.2))).length =
        ((xs ++ g :: h :: suf).filter (fun u => decide (key u.2.2 < key x.2.2))).length :=
      (hp.filter _).length_eq
    omega

theorem live_swap_at {op : α → α → Finset α} {t : α}
    (pre : List (α × α × α)) (g h : α × α × α) (suf : List (α × α × α)) {L : Finset α}
    (hl : Live op t (pre ++ g :: h :: suf) L) (h1 : h.1 ≠ g.2.2) (h2 : h.2.1 ≠ g.2.2) :
    Live op t (pre ++ h :: g :: suf) L ∨ Reach op t (pre.length + suf.length + 1) L := by
  induction pre generalizing L with
  | nil => simpa using live_swap hl h1 h2
  | cons q pre ih =>
    obtain ⟨x, y, z⟩ := q
    obtain ⟨hx, hy, hxy, hz, hn, R, hL, tail⟩ := hl
    rcases ih tail with hs | hr
    · exact Or.inl ⟨hx, hy, hxy, hz, hn, R, hL, hs⟩
    · right
      have e : ((x, y, z) :: pre).length + suf.length + 1 = (pre.length + suf.length + 1) + 1 := by
        simp; omega
      rw [e]
      refine Or.inr ⟨x, hx, y, hy, hxy, z, hz, reach_mono ?_ hr⟩
      intro u hu
      rw [hL]
      rcases Finset.mem_insert.mp hu with rfl | hu
      · exact Finset.mem_insert_self u _
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu))

omit [DecidableEq α] in
theorem ordered_or_bad (key : α → ℕ) (prev : ℕ) (gs : List (α × α × α))
    (hhead : ∀ g gs', gs = g :: gs' → key g.1 = prev ∨ key g.2.1 = prev ∨ prev ≤ key g.2.2) :
    Ordered key prev gs ∨
    ∃ pre g h suf, gs = pre ++ g :: h :: suf ∧
      key h.1 ≠ key g.2.2 ∧ key h.2.1 ≠ key g.2.2 ∧ key h.2.2 < key g.2.2 := by
  induction gs generalizing prev with
  | nil => exact Or.inl trivial
  | cons g rest ih =>
    have hg := hhead g rest rfl
    cases rest with
    | nil => exact Or.inl ⟨hg, trivial⟩
    | cons h suf =>
      by_cases hok : key h.1 = key g.2.2 ∨ key h.2.1 = key g.2.2 ∨ key g.2.2 ≤ key h.2.2
      · rcases ih (key g.2.2) (fun q qs e => by cases e; exact hok) with
          ho | ⟨pre, a, b, s', e, e1, e2, elt⟩
        · exact Or.inl ⟨hg, ho⟩
        · exact Or.inr ⟨g :: pre, a, b, s', by simp [e], e1, e2, elt⟩
      · simp only [not_or, not_le] at hok
        exact Or.inr ⟨[], g, h, suf, rfl, hok.1, hok.2.1, hok.2.2⟩

theorem normal_aux {op : α → α → Finset α} {t : α} (key : α → ℕ) (P : Finset α) :
    ∀ (m d : ℕ) (gs : List (α × α × α)) (L : Finset α),
      gs.length ≤ m → disorder key gs ≤ d → L ⊆ P → Live op t gs L →
      ∃ gs' : List (α × α × α), gs'.length ≤ m ∧ Ordered key 0 gs' ∧
        ∃ L' ⊆ P, Live op t gs' L' := by
  intro m
  induction m with
  | zero =>
    intro d gs L hl _ hLP hr
    have e : gs = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hl)
    subst e
    exact ⟨[], le_refl 0, trivial, L, hLP, hr⟩
  | succ m ihm =>
    intro d
    induction d with
    | zero =>
      intro gs L hl hd hLP hr
      rcases ordered_or_bad key 0 gs (fun _ _ _ => Or.inr (Or.inr (Nat.zero_le _))) with
        ho | ⟨pre, g, h, suf, rfl, h1, h2, hlt⟩
      · exact ⟨_, hl, ho, L, hLP, hr⟩
      · exfalso
        have := disorder_swap key pre suf g h hlt
        omega
    | succ d ihd =>
      intro gs L hl hd hLP hr
      rcases ordered_or_bad key 0 gs (fun _ _ _ => Or.inr (Or.inr (Nat.zero_le _))) with
        ho | ⟨pre, g, h, suf, rfl, h1, h2, hlt⟩
      · exact ⟨_, hl, ho, L, hLP, hr⟩
      · have n1 : h.1 ≠ g.2.2 := fun e => h1 (congrArg key e)
        have n2 : h.2.1 ≠ g.2.2 := fun e => h2 (congrArg key e)
        rcases live_swap_at pre g h suf hr n1 n2 with hs | hs
        · have hlt' := disorder_swap key pre suf g h hlt
          have hl' : (pre ++ h :: g :: suf).length ≤ m + 1 := by
            simp only [List.length_append, List.length_cons] at hl ⊢; omega
          exact ihd _ L hl' (by omega) hLP hs
        · have hm : Reach op t m P := by
            have hle : pre.length + suf.length + 1 ≤ m := by
              simp only [List.length_append, List.length_cons] at hl; omega
            exact reach_le hle (reach_mono hLP hs)
          obtain ⟨gs', hl', L', hL', hr'⟩ := reach_live hm
          obtain ⟨gs'', hl'', ho'', L'', hL'', hr''⟩ :=
            ihm (disorder key gs') gs' L' hl' (le_refl _) hL' hr'
          exact ⟨gs'', Nat.le_succ_of_le hl'', ho'', L'', hL'', hr''⟩

theorem reach_ordered {op : α → α → Finset α} {t : α} (key : α → ℕ) {k : ℕ} {P : Finset α}
    (h : Reach op t k P) :
    ∃ gs : List (α × α × α), gs.length ≤ k ∧ Ordered key 0 gs ∧ ∃ L ⊆ P, Live op t gs L := by
  obtain ⟨gs, hl, L, hLP, hr⟩ := reach_live h
  exact normal_aux key P k (disorder key gs) gs L hl (le_refl _) hLP hr

end Pool

/-! Part 2: choosing two members of a list. -/

section Choose

variable {α : Type}

/-- Every way to take one member out of a list. -/
def picks : List α → List (α × List α)
  | [] => []
  | a :: t => (a, t) :: (picks t).map (fun p => (p.1, a :: p.2))

/-- Every way to take two members out of a list (in list order). -/
def splits : List α → List (α × α × List α)
  | [] => []
  | a :: t => (picks t).map (fun p => (a, p.1, p.2)) ++
      (splits t).map (fun q => (q.1, q.2.1, a :: q.2.2))

theorem mem_picks {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ r, (a, r) ∈ picks ws ∧ ws.Perm (a :: r) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst e; exact ⟨xs, by simp [picks], .refl _⟩
    · obtain ⟨r, hm, hp⟩ := ih h
      refine ⟨x :: r, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

theorem mem_splits {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ r, ((a, b, r) ∈ splits ws ∨ (b, a, r) ∈ splits ws) ∧ ws.Perm (a :: b :: r) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with e | ha
    · subst e
      obtain ⟨r, hm, hp⟩ := mem_picks ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b, r), hm, rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with e | hb
      · subst e
        obtain ⟨r, hm, hp⟩ := mem_picks (ws := xs) (a := a) (by assumption)
        exact ⟨r, .inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_,
          (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))

/-- The four ways the two operands of a step can stay live. -/
def keeps (x y : α) : List (List α) := [[], [x], [y], [x, y]]

theorem keep_exists [DecidableEq α] {ws r : List α} {x y : α} {need : Finset α}
    (hp : ws.Perm (x :: y :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert x (insert y need)) :
    ∃ ks ∈ keeps x y, (ks ++ r).Nodup ∧ (ks ++ r).toFinset = need := by
  have hxyr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert x (insert y r.toFinset) := by
    ext v; simp [hp.mem_iff]
  have hr : ∀ v, v ∈ r ↔ v ∈ need ∧ v ≠ x ∧ v ≠ y := by
    intro v
    have he : (v ∈ insert x (insert y r.toFinset)) ↔ v ∈ insert x (insert y need) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at hxyr
    grind
  simp only [List.nodup_cons, List.mem_cons, not_or] at hxyr
  by_cases hx : x ∈ need <;> by_cases hy : y ∈ need
  · refine ⟨[x, y], by simp [keeps], ?_, ?_⟩
    · simp only [List.cons_append, List.nil_append, List.nodup_cons, List.mem_cons, not_or]
      exact ⟨⟨hxyr.1.1, hxyr.1.2⟩, hxyr.2.1, hxyr.2.2⟩
    · ext v; simp [hr]; grind
  · refine ⟨[x], by simp [keeps], ?_, ?_⟩
    · simp only [List.cons_append, List.nil_append, List.nodup_cons]
      exact ⟨hxyr.1.2, hxyr.2.2⟩
    · ext v; simp [hr]; grind
  · refine ⟨[y], by simp [keeps], ?_, ?_⟩
    · simp only [List.cons_append, List.nil_append, List.nodup_cons]
      exact ⟨hxyr.2.1, hxyr.2.2⟩
    · ext v; simp [hr]; grind
  · refine ⟨[], by simp [keeps], hxyr.2.2, ?_⟩
    ext v; simp [hr]; grind

end Choose



/-! Part 3: values on the sample rows. A value is a natural number; its bit `NN + i` is the
value at the positive row of pair `i`, and its bit `i` the value at the negative row of pair `i`.
The constants are written as literals so that the kernel computes with them directly. -/

def NN : ℕ := 63
def FULL : ℕ := 85070591730234615865843651857942052863
def LOW : ℕ := 9223372036854775807
def target : ℕ := 85070591730234615856620279821087277056

abbrev B : ℕ := 2 ^ (NN + NN)

theorem full_eq : FULL = 2 ^ (NN + NN) - 1 := by decide +kernel
theorem low_eq : LOW = 2 ^ NN - 1 := by decide +kernel
theorem target_bit (i : ℕ) : target.testBit i = (decide (NN ≤ i) && decide (i < NN + NN)) := by
  have e : target = (2 ^ NN - 1) <<< NN := by decide +kernel
  rw [e, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
  by_cases h : NN ≤ i
  · simp only [h, decide_true, Bool.true_and]
    congr 1
    exact propext ⟨fun h' => by omega, fun h' => by omega⟩
  · simp [h]

theorem target_lt : target < B := by decide +kernel
theorem target_ne_zero : target ≠ 0 := by decide +kernel
theorem target_ne_full : target ≠ FULL := by decide +kernel
theorem full_lt : FULL < B := by rw [full_eq]; exact Nat.sub_lt (by positivity) one_pos
theorem zero_lt_B : 0 < B := by positivity

theorem bit_high {x : ℕ} (hx : x < B) {i : ℕ} (hi : NN + NN ≤ i) : x.testBit i = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) hi))

theorem and_full {x : ℕ} (hx : x < B) : x &&& FULL = x := by
  rw [full_eq, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hx]

theorem full_and {x : ℕ} (hx : x < B) : FULL &&& x = x := by
  rw [Nat.and_comm, and_full hx]

/-- The two non-constant monotone combinations of two values. -/
def comb (x y : ℕ) : List ℕ := [x &&& y, x ||| y].filter (fun z => z != 0 && z != FULL)

def combF (x y : ℕ) : Finset ℕ := (comb x y).toFinset

theorem combF_swap (x y : ℕ) : combF x y = combF y x := by
  ext z
  simp [combF, comb, Nat.and_comm, Nat.or_comm]

/-- The pairs separated by a value (positive row on, negative row off), as low bits. -/
def cov (x : ℕ) : ℕ := Nat.land (Nat.shiftRight x NN) (Nat.xor LOW x)

/-- The pairs separated by some member of a list. -/
def covL : List ℕ → ℕ
  | [] => 0
  | a :: t => Nat.lor (cov a) (covL t)

/-- Every pair is separated. -/
def isFull (c : ℕ) : Bool := Nat.beq (Nat.land c LOW) LOW

def Hits (i : ℕ) (w : ℕ) : Prop := w.testBit (NN + i) = true ∧ w.testBit i = false

theorem cov_bit {i : ℕ} (hi : i < NN) (x : ℕ) :
    (cov x).testBit i = (x.testBit (NN + i) && !x.testBit i) := by
  change ((x >>> NN) &&& (LOW ^^^ x)).testBit i = _
  simp [low_eq, Nat.testBit_and, Nat.testBit_xor, Nat.testBit_shiftRight, hi]

theorem covL_bit {i : ℕ} (hi : i < NN) (ws : List ℕ) :
    (covL ws).testBit i = true ↔ ∃ w ∈ ws, Hits i w := by
  induction ws with
  | nil => simp [covL]
  | cons a rest ih =>
    change (cov a ||| covL rest).testBit i = true ↔ _
    rw [Nat.testBit_or, Bool.or_eq_true, ih, cov_bit hi]
    simp [Hits]

theorem isFull_of {c : ℕ} (h : c &&& LOW = LOW) : isFull c = true := by
  unfold isFull
  change Nat.beq (c &&& LOW) LOW = true
  rw [h]
  exact Nat.beq_refl LOW

theorem beq_f {a b : ℕ} (h : a ≠ b) : Nat.beq a b = false :=
  Bool.eq_false_iff.mpr (fun h' => h (Nat.eq_of_beq_eq_true h'))

theorem blt_f {a b : ℕ} (h : ¬ a < b) : Nat.blt a b = false :=
  Bool.eq_false_iff.mpr (fun h' => h (by simpa using h'))

theorem ble_t {a b : ℕ} (h : a ≤ b) : Nat.ble a b = true := by simpa using h

/-- Membership with the kernel-friendly equality test. -/
def memN (z : ℕ) : List ℕ → Bool
  | [] => false
  | a :: t => Nat.beq z a || memN z t

theorem memN_f {z : ℕ} {r : List ℕ} (h : z ∉ r) : memN z r = false := by
  induction r with
  | nil => rfl
  | cons a t ih =>
    simp only [List.mem_cons, not_or] at h
    simp only [memN, beq_f h.1, ih h.2, Bool.false_or]

theorem comb_hits {x y z : ℕ} (hz : z ∈ combF x y) (i : ℕ) (hd : Hits i z) : Hits i x ∨ Hits i y := by
  simp only [combF, comb, List.mem_toFinset, List.mem_filter, List.mem_cons, List.not_mem_nil,
    or_false] at hz
  unfold Hits at hd ⊢
  rcases hz.1 with rfl | rfl <;> revert hd <;> simp only [Nat.testBit_and, Nat.testBit_or] <;>
    cases x.testBit (NN + i) <;> cases x.testBit i <;>
    cases y.testBit (NN + i) <;> cases y.testBit i <;> simp

theorem cover_full {gs : List (ℕ × ℕ × ℕ)} {ws : List ℕ}
    (h : Live combF target gs ws.toFinset) : covL ws &&& LOW = LOW := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, low_eq, Nat.testBit_two_pow_sub_one]
  by_cases hj : j < NN
  · have ht : Hits j target := by
      unfold Hits
      rw [target_bit, target_bit]
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.and_eq_false_iff, decide_eq_false_iff_not]
      omega
    obtain ⟨w, hw, hd⟩ := live_witness (Hits j) ht (fun x y z hz => comb_hits hz j) h
    have hb := (covL_bit hj ws).mpr ⟨w, by simpa using hw, hd⟩
    simp [hb, hj]
  · simp [hj]

/-! Part 4: the search. `srch n e last ws`: from the live list `ws`, the target can be reached
with at most `n` more steps, where `e + ws.length = n + 1`, every live list covers every pair,
and the steps are in the order normal form for the key `id`. -/

/-- The four ways to keep the operands live, with the cover of the remainder precomputed. -/
def tryK (e : ℕ) (k : ℕ → ℕ → List ℕ → Bool) (z x y base : ℕ) (r : List ℕ) : Bool :=
  (isFull (Nat.lor (cov z) base) && k e z (z :: r)) ||
  (Nat.ble 1 e && isFull (Nat.lor (cov z) (Nat.lor (cov x) base)) && k (e - 1) z (z :: x :: r)) ||
  (Nat.ble 1 e && isFull (Nat.lor (cov z) (Nat.lor (cov y) base)) && k (e - 1) z (z :: y :: r)) ||
  (Nat.ble 2 e && isFull (Nat.lor (cov z) (Nat.lor (cov x) (Nat.lor (cov y) base))) &&
    k (e - 2) z (z :: x :: y :: r))

/-- One candidate output `z` of a step on `x` and `y`. -/
def stepZ (e last : ℕ) (k : ℕ → ℕ → List ℕ → Bool) (x y base : ℕ) (r : List ℕ) (z : ℕ) : Bool :=
  !(Nat.beq z 0 || Nat.beq z FULL || Nat.beq z x || Nat.beq z y || memN z r ||
    (!(Nat.beq x last) && !(Nat.beq y last) && Nat.blt z last)) &&
  tryK e k z x y base r

def stepS (e last : ℕ) (k : ℕ → ℕ → List ℕ → Bool) (x y : ℕ) (r : List ℕ) : Bool :=
  stepZ e last k x y (covL r) r (Nat.land x y) || stepZ e last k x y (covL r) r (Nat.lor x y)

def srch : ℕ → ℕ → ℕ → List ℕ → Bool
  | 0, _, _, ws => ws == [target]
  | n + 1, e, last, ws => ws == [target] ||
      (splits ws).any fun p => stepS e last (srch n) p.1 p.2.1 p.2.2

theorem list_single {ws : List ℕ} (hn : ws.Nodup) (hs : ws.toFinset = {target}) :
    ws = [target] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

theorem srch_complete : ∀ (n : ℕ) (ws : List ℕ) (e last : ℕ) (gs : List (ℕ × ℕ × ℕ)),
    ws.Nodup → gs.length ≤ n → e + ws.length = n + 1 → Ordered id last gs →
    Live combF target gs ws.toFinset → srch n e last ws = true := by
  intro n
  induction n with
  | zero =>
    intro ws e last gs hn hl _ _ h
    have e0 : gs = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hl)
    subst e0
    simp [srch, list_single hn h]
  | succ n ih =>
    intro ws e last gs hn hl he ho h
    cases gs with
    | nil => simp [srch, list_single hn h]
    | cons g gs =>
      obtain ⟨x, y, z⟩ := g
      obtain ⟨hx, hy, hxy, hz, hzn, need, hs, tail⟩ := h
      obtain ⟨ho1, ho2⟩ := ho
      simp only [id_eq] at ho1
      obtain ⟨r, hm, hp⟩ := mem_splits (List.mem_toFinset.mp hx) (List.mem_toFinset.mp hy) hxy
      have main : ∀ {a b : ℕ}, ws.Perm (a :: b :: r) → ws.toFinset = insert a (insert b need) →
          z ∈ combF a b → (a = last ∨ b = last ∨ last ≤ z) →
          stepS e last (srch n) a b r = true := by
        intro a b hp' hs' hz' ho'
        obtain ⟨ks, hks, hkn, hkf⟩ := keep_exists hp' hn hs'
        have hzw : z ∉ a :: b :: r := fun hu => hzn (List.mem_toFinset.mpr (hp'.mem_iff.mpr hu))
        have hza : z ≠ a := fun e => hzw (e ▸ List.mem_cons_self)
        have hzb : z ≠ b := fun e => hzw (List.mem_cons_of_mem _ (e ▸ List.mem_cons_self))
        have hzr : z ∉ r := fun hu => hzw (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hu))
        have hzk : z ∉ ks ++ r := by
          intro hu
          apply hzn
          rw [hs']
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hkf ▸ List.mem_toFinset.mpr hu))
        have hnd : (z :: (ks ++ r)).Nodup := List.nodup_cons.mpr ⟨hzk, hkn⟩
        have hl' : Live combF target gs (z :: (ks ++ r)).toFinset := by
          rw [List.toFinset_cons, hkf]
          exact tail
        have hc := live_card hl'
        rw [List.toFinset_card_of_nodup hnd] at hc
        have hlen := hp'.length_eq
        simp only [List.length_cons, List.length_append] at hc hlen hl
        have hke : ks.length ≤ e := by omega
        have hcov := isFull_of (cover_full hl')
        have hrec := ih (z :: (ks ++ r)) (e - ks.length) z gs hnd (by omega)
          (by simp only [List.length_cons, List.length_append]; omega) ho2 hl'
        have hzc : (z = Nat.land a b ∨ z = Nat.lor a b) ∧ z ≠ 0 ∧ z ≠ FULL := by
          simp only [combF, comb, List.mem_toFinset, List.mem_filter, List.mem_cons,
            List.not_mem_nil, or_false, Bool.and_eq_true, bne_iff_ne] at hz'
          exact ⟨hz'.1, hz'.2.1, hz'.2.2⟩
        have hguard : (!(Nat.beq z 0 || Nat.beq z FULL || Nat.beq z a || Nat.beq z b || memN z r ||
            (!(Nat.beq a last) && !(Nat.beq b last) && Nat.blt z last))) = true := by
          rw [beq_f hzc.2.1, beq_f hzc.2.2, beq_f hza, beq_f hzb, memN_f hzr]
          rcases ho' with e1 | e1 | e1
          · subst e1; simp [Nat.beq_refl]
          · subst e1; simp [Nat.beq_refl]
          · have : ¬ z < last := by omega
            simp [blt_f this]
        have htry : tryK e (srch n) z a b (covL r) r = true := by
          unfold tryK
          simp only [keeps, List.mem_cons, List.not_mem_nil, or_false] at hks
          rcases hks with rfl | rfl | rfl | rfl
          · simp only [List.nil_append, List.length_nil, Nat.sub_zero] at hcov hrec
            have h1 : isFull (cov z ||| covL r) = true := hcov
            simp [h1, hrec]
          · simp only [List.cons_append, List.nil_append, List.length_cons, List.length_nil]
              at hcov hrec hke
            have h1 : isFull (cov z ||| (cov a ||| covL r)) = true := hcov
            have h2 : 1 ≤ e := by omega
            simp [h1, h2, hrec]
          · simp only [List.cons_append, List.nil_append, List.length_cons, List.length_nil]
              at hcov hrec hke
            have h1 : isFull (cov z ||| (cov b ||| covL r)) = true := hcov
            have h2 : 1 ≤ e := by omega
            simp [h1, h2, hrec]
          · simp only [List.cons_append, List.nil_append, List.length_cons, List.length_nil]
              at hcov hrec hke
            have h1 : isFull (cov z ||| (cov a ||| (cov b ||| covL r))) = true :=
              hcov
            have h2 : 2 ≤ e := by omega
            simp [h1, h2, hrec]
        have hstep : stepZ e last (srch n) a b (covL r) r z = true := by
          unfold stepZ
          rw [hguard, htry]
          all_goals rfl
        unfold stepS
        rcases hzc.1 with e1 | e1
        · rw [← e1, hstep]; all_goals rfl
        · rw [← e1, hstep]; simp
      simp only [srch, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with hm | hm
      · exact ⟨(x, y, r), hm, main hp hs hz ho1⟩
      · refine ⟨(y, x, r), hm, main (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm])
          (combF_swap x y ▸ hz) ?_⟩
        rcases ho1 with e1 | e1 | e1
        · exact Or.inr (Or.inl e1)
        · exact Or.inl e1
        · exact Or.inr (Or.inr e1)

/-! Part 5: from a circuit to a pool argument. -/

open PEqualNP.CircuitLowerBounds

/-- The value of an AND or OR gate on all sample rows at once. -/
def opV : GateOp → List ℕ → ℕ
  | GateOp.and, l => l.foldr (fun a b => a &&& b) FULL
  | _, l => l.foldr (fun a b => a ||| b) 0

def wstep (w : List ℕ) (g : Gate) : List ℕ := w ++ [opV g.op (g.inputs.map fun i => w.getD i 0)]

def bit (k : ℕ) (v : ℕ) : Bool := v.testBit k

def Legal (g : Gate) : Prop := g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem legal_op {g : Gate} (h : Legal g) : g.op = GateOp.and ∨ g.op = GateOp.or := by
  have := h.1
  simpa using this

theorem eval_bits (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (l : List ℕ) {k : ℕ}
    (hk : k < NN + NN) : op.eval (l.map (bit k)) = bit k (opV op l) := by
  rcases hop with rfl | rfl
  · induction l with
    | nil => simp [GateOp.eval, opV, bit, full_eq, hk]
    | cons a l ih =>
      simp only [GateOp.eval, opV, bit, List.map_cons, List.all_cons, List.foldr_cons,
        Nat.testBit_and, id_eq] at ih ⊢
      rw [ih]
  · induction l with
    | nil => simp [GateOp.eval, opV, bit]
    | cons a l ih =>
      simp only [GateOp.eval, opV, bit, List.map_cons, List.any_cons, List.foldr_cons,
        Nat.testBit_or, id_eq] at ih ⊢
      rw [ih]

theorem read_bit (w : List ℕ) (i k : ℕ) : (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

theorem wires_bits (gs : List Gate) (hg : ∀ g ∈ gs, Legal g) (w : List ℕ) {k : ℕ}
    (hk : k < NN + NN) :
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (w.map (bit k)) =
      (gs.foldl wstep w).map (bit k) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [← ih (fun g' h => hg g' (List.mem_cons_of_mem _ h))]
    congr 1
    simp only [wstep, List.map_append, List.map_cons, List.map_nil]
    congr 2
    have e : (g.inputs.map fun i => (w.map (bit k)).getD i false) =
        (g.inputs.map fun i => w.getD i 0).map (bit k) := by
      simp only [List.map_map]
      congr 1
      funext i
      exact read_bit w i k
    rw [e, eval_bits g.op (legal_op (hg g List.mem_cons_self)) _ hk]

theorem opV_lt (op : GateOp) (l : List ℕ) (hl : ∀ t ∈ l, t < B) : opV op l < B := by
  cases op with
  | and =>
    induction l with
    | nil => exact full_lt
    | cons a l ih =>
      simp only [opV, List.foldr_cons]
      exact Nat.and_lt_two_pow _ (ih (fun t ht => hl t (List.mem_cons_of_mem _ ht)))
  | _ =>
    induction l with
    | nil => exact zero_lt_B
    | cons a l ih =>
      simp only [opV, List.foldr_cons]
      exact Nat.or_lt_two_pow (hl a List.mem_cons_self)
        (ih (fun t ht => hl t (List.mem_cons_of_mem _ ht)))

theorem getD_mem_or (w : List ℕ) (i : ℕ) : w.getD i 0 = 0 ∨ w.getD i 0 ∈ w := by
  by_cases h : i < w.length
  · exact Or.inr (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_gt h)]

theorem wires_lt (gs : List Gate) : ∀ w : List ℕ, (∀ t ∈ w, t < B) → ∀ t ∈ gs.foldl wstep w, t < B := by
  induction gs with
  | nil => intro w hw; simpa using hw
  | cons g gs ih =>
    intro w hw
    simp only [List.foldl_cons]
    apply ih
    intro t ht
    simp only [wstep, List.mem_append, List.mem_singleton] at ht
    rcases ht with ht | rfl
    · exact hw t ht
    · apply opV_lt
      intro t ht
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp ht
      rcases getD_mem_or w i with h | h
      · rw [h]; exact zero_lt_B
      · exact hw _ h

def Good (P : Finset ℕ) (t : ℕ) : Prop := t < B ∧ (t = 0 ∨ t = FULL ∨ t ∈ P)

theorem good_and {P : Finset ℕ} {x y : ℕ} (hx : Good P x) (hy : Good P y) :
    Good P (x &&& y) ∨ ∃ a ∈ P, ∃ b ∈ P, a ≠ b ∧ x &&& y ∈ combF a b := by
  have hb : x &&& y < B := Nat.and_lt_two_pow x hy.1
  obtain ⟨hxb, hx⟩ := hx
  obtain ⟨hyb, hy⟩ := hy
  rcases hx with rfl | rfl | hx
  · exact Or.inl ⟨hb, Or.inl (Nat.zero_and y)⟩
  · rw [full_and hyb]; exact Or.inl ⟨hyb, hy⟩
  rcases hy with rfl | rfl | hy
  · exact Or.inl ⟨hb, Or.inl (Nat.and_zero x)⟩
  · rw [and_full hxb]; exact Or.inl ⟨hxb, Or.inr (Or.inr hx)⟩
  by_cases e : x = y
  · subst e; rw [Nat.and_self]; exact Or.inl ⟨hxb, Or.inr (Or.inr hx)⟩
  by_cases h0 : x &&& y = 0
  · exact Or.inl ⟨hb, Or.inl h0⟩
  by_cases h1 : x &&& y = FULL
  · exact Or.inl ⟨hb, Or.inr (Or.inl h1)⟩
  exact Or.inr ⟨x, hx, y, hy, e, by simp [combF, comb, h0, h1]⟩

theorem good_or {P : Finset ℕ} {x y : ℕ} (hx : Good P x) (hy : Good P y) :
    Good P (x ||| y) ∨ ∃ a ∈ P, ∃ b ∈ P, a ≠ b ∧ x ||| y ∈ combF a b := by
  have hb : x ||| y < B := Nat.or_lt_two_pow hx.1 hy.1
  obtain ⟨hxb, hx⟩ := hx
  obtain ⟨hyb, hy⟩ := hy
  have hfull : ∀ {t : ℕ}, t < B → (t ||| FULL = FULL ∧ FULL ||| t = FULL) := by
    intro t ht
    have e1 : t ||| FULL = FULL := by
      apply Nat.eq_of_testBit_eq
      intro i
      rw [Nat.testBit_or, full_eq, Nat.testBit_two_pow_sub_one]
      by_cases hi : i < NN + NN
      · simp [hi]
      · simp [hi, bit_high ht (i := i) (by omega)]
    exact ⟨e1, by rw [Nat.or_comm]; exact e1⟩
  rcases hx with rfl | rfl | hx
  · rw [Nat.zero_or]; exact Or.inl ⟨hyb, hy⟩
  · rw [(hfull hyb).2]; exact Or.inl ⟨full_lt, Or.inr (Or.inl rfl)⟩
  rcases hy with rfl | rfl | hy
  · rw [Nat.or_zero]; exact Or.inl ⟨hxb, Or.inr (Or.inr hx)⟩
  · rw [(hfull hxb).1]; exact Or.inl ⟨full_lt, Or.inr (Or.inl rfl)⟩
  by_cases e : x = y
  · subst e; rw [Nat.or_self]; exact Or.inl ⟨hxb, Or.inr (Or.inr hx)⟩
  by_cases h0 : x ||| y = 0
  · exact Or.inl ⟨hb, Or.inl h0⟩
  by_cases h1 : x ||| y = FULL
  · exact Or.inl ⟨hb, Or.inr (Or.inl h1)⟩
  exact Or.inr ⟨x, hx, y, hy, e, by simp [combF, comb, h0, h1]⟩

theorem good_gate {P : Finset ℕ} (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l : List ℕ) (hl : l.length ≤ 2) (hg : ∀ t ∈ l, Good P t) :
    Good P (opV op l) ∨ ∃ a ∈ P, ∃ b ∈ P, a ≠ b ∧ opV op l ∈ combF a b := by
  match l, hl, hg with
  | [], _, _ =>
    rcases hop with rfl | rfl
    · exact Or.inl ⟨full_lt, Or.inr (Or.inl rfl)⟩
    · exact Or.inl ⟨zero_lt_B, Or.inl rfl⟩
  | [x], _, hg =>
    have hx := hg x (by simp)
    rcases hop with rfl | rfl
    · simp only [opV, List.foldr_cons, List.foldr_nil]
      rw [and_full hx.1]; exact Or.inl hx
    · simp only [opV, List.foldr_cons, List.foldr_nil]
      rw [Nat.or_zero]; exact Or.inl hx
  | [x, y], _, hg =>
    have hx := hg x (by simp)
    have hy := hg y (by simp)
    rcases hop with rfl | rfl
    · simp only [opV, List.foldr_cons, List.foldr_nil]
      rw [and_full hy.1]; exact good_and hx hy
    · simp only [opV, List.foldr_cons, List.foldr_nil]
      rw [Nat.or_zero]; exact good_or hx hy
  | _ :: _ :: _ :: _, hl, _ => simp at hl

theorem compile (gs : List Gate) (hg : ∀ g ∈ gs, Legal g) (out : ℕ) :
    ∀ (w : List ℕ) (P : Finset ℕ), (∀ t ∈ w, Good P t) →
      (gs.foldl wstep w).getD out 0 = target → Reach combF target gs.length P := by
  induction gs with
  | nil =>
    intro w P hw hv
    simp only [List.foldl_nil] at hv
    have hg' : Good P (w.getD out 0) := by
      rcases getD_mem_or w out with h | h
      · rw [h]; exact ⟨zero_lt_B, Or.inl rfl⟩
      · exact hw _ h
    rw [hv] at hg'
    rcases hg'.2 with h | h | h
    · exact absurd h target_ne_zero
    · exact absurd h target_ne_full
    · exact h
  | cons g gs ih =>
    intro w P hw hv
    have hg2 : ∀ g' ∈ gs, Legal g' := fun g' h => hg g' (List.mem_cons_of_mem _ h)
    have hargs : ∀ t ∈ g.inputs.map (fun i => w.getD i 0), Good P t := by
      intro t ht
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp ht
      rcases getD_mem_or w i with h | h
      · rw [h]; exact ⟨zero_lt_B, Or.inl rfl⟩
      · exact hw _ h
    have hlen : (g.inputs.map fun i => w.getD i 0).length ≤ 2 := by
      rw [List.length_map]; exact (hg g List.mem_cons_self).2
    have hzlt : opV g.op (g.inputs.map fun i => w.getD i 0) < B :=
      opV_lt _ _ (fun t ht => (hargs t ht).1)
    have hcase := good_gate g.op (legal_op (hg g List.mem_cons_self)) _ hlen hargs
    simp only [List.foldl_cons, wstep] at hv
    generalize opV g.op (g.inputs.map fun i => w.getD i 0) = z at hv hzlt hcase
    rcases hcase with hgood | ⟨a, ha, b, hb, hab, hzab⟩
    · refine Or.inl (ih hg2 (w ++ [z]) P ?_ hv)
      intro t ht
      rcases List.mem_append.mp ht with ht | ht
      · exact hw t ht
      · rw [List.mem_singleton.mp ht]; exact hgood
    · refine Or.inr ⟨a, ha, b, hb, hab, z, hzab, ih hg2 (w ++ [z]) (insert z P) ?_ hv⟩
      intro t ht
      rcases List.mem_append.mp ht with ht | ht
      · obtain ⟨hb', h'⟩ := hw t ht
        exact ⟨hb', h'.imp_right (Or.imp_right (Finset.mem_insert_of_mem ·))⟩
      · rw [List.mem_singleton.mp ht]
        exact ⟨hzlt, Or.inr (Or.inr (Finset.mem_insert_self _ _))⟩

/-! Part 6: the instance. -/

def posL : List (Fin 4 × Fin 4) := [(0, 0), (0, 2), (0, 3), (1, 0), (1, 1), (1, 3), (2, 0), (2, 1), (2, 2)]

def negL : List (Fin 4 × Fin 4) := [(0, 1), (1, 2), (2, 3), (3, 0), (3, 1), (3, 2), (3, 3)]

def pt (k : ℕ) : Fin 4 × Fin 4 :=
  if k < NN then negL.getD (k % 7) (0, 0) else posL.getD ((k - NN) / 7) (0, 0)

def ins : List ℕ :=
  [19342803963087006608670849, 40564799864490372263781043568898,
    85070551165415408562793303870112072196, 8714997200177740920,
    5151734495865961693857578731308040, 659422015470693088544587461547018385,
    84405977732342307866996828645754442018, 40247925748948608378171909284420]

set_option maxRecDepth 20000 in
theorem ins_rows : ∀ k : Fin (NN + NN),
    ins.map (bit k.val) = PEqualNP.Represents.oneEach (pt k.val).1 (pt k.val).2 := by
  decide +kernel

set_option maxRecDepth 20000 in
theorem target_rows : ∀ k : Fin (NN + NN),
    bit k.val target = (1981 : ℕ).testBit (4 * (pt k.val).1.val + (pt k.val).2.val) := by
  decide +kernel

theorem ins_nodup : ins.Nodup := by decide +kernel

theorem ins_lt : ∀ t ∈ ins, t < B := by decide +kernel

def T0 : List (ℕ × ℕ × List ℕ) :=
  [(1, 40564819207294335350787652239747, [40564819207294335350787652239747, 19342803963087006608670849, 40564799864490372263781043568898, 85070551165415408562793303870112072196, 5151734495865961693857578731308040, 659422015470693088544587461547018385, 84405977732342307866996828645754442018, 40247925748948608378171909284420])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok0 : T0.all (fun c => !srch 8 c.1 c.2.1 c.2.2) = true := by
  decide +kernel

def T1 : List (ℕ × ℕ × List ℕ) :=
  [(1, 85070551165434751366756390876720743045, [85070551165434751366756390876720743045, 19342803963087006608670849, 85070551165415408562793303870112072196, 40564799864490372263781043568898, 5151734495865961693857578731308040, 659422015470693088544587461547018385, 84405977732342307866996828645754442018, 40247925748948608378171909284420])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok1 : T1.all (fun c => !srch 8 c.1 c.2.1 c.2.2) = true := by
  decide +kernel

def T2 : List (ℕ × ℕ × List ℕ) :=
  [(1, 1171368248680556527616, [1171368248680556527616, 19342803963087006608670849, 5151734495865961693857578731308040, 40564799864490372263781043568898, 85070551165415408562793303870112072196, 659422015470693088544587461547018385, 84405977732342307866996828645754442018, 40247925748948608378171909284420])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok2 : T2.all (fun c => !srch 8 c.1 c.2.1 c.2.2) = true := by
  decide +kernel

def T3 : List (ℕ × ℕ × List ℕ) :=
  [(1, 5151734515207594288695904783451273, [5151734515207594288695904783451273, 19342803963087006608670849, 5151734495865961693857578731308040, 40564799864490372263781043568898, 85070551165415408562793303870112072196, 659422015470693088544587461547018385, 84405977732342307866996828645754442018, 40247925748948608378171909284420])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok3 : T3.all (fun c => !srch 8 c.1 c.2.1 c.2.2) = true := by
  decide +kernel

def T4 : List (ℕ × ℕ × List ℕ) :=
  [(1, 72624976668147841, [72624976668147841, 19342803963087006608670849, 659422015470693088544587461547018385, 40564799864490372263781043568898, 85070551165415408562793303870112072196, 5151734495865961693857578731308040, 84405977732342307866996828645754442018, 40247925748948608378171909284420])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok4 : T4.all (fun c => !srch 8 c.1 c.2.1 c.2.2) = true := by
  decide +kernel

def T5 : List (ℕ × ℕ × List ℕ) :=
  [(3, 659422015490035892435049491487541393, [659422015490035892435049491487541393, 40564799864490372263781043568898, 85070551165415408562793303870112072196, 5151734495865961693857578731308040, 84405977732342307866996828645754442018, 40247925748948608378171909284420])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok5 : T5.all (fun c => !srch 8 c.1 c.2.1 c.2.2) = true := by
  decide +kernel

def T6 : List (ℕ × ℕ × List ℕ) :=
  [(2, 659422015490035892435049491487541393, [659422015490035892435049491487541393, 19342803963087006608670849, 40564799864490372263781043568898, 85070551165415408562793303870112072196, 5151734495865961693857578731308040, 84405977732342307866996828645754442018, 40247925748948608378171909284420])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok6 : T6.all (fun c => !srch 8 c.1 c.2.1 c.2.2) = true := by
  decide +kernel

def T7 : List (ℕ × ℕ × List ℕ) :=
  [(2, 659422015490035892435049491487541393, [659422015490035892435049491487541393, 659422015470693088544587461547018385, 40564799864490372263781043568898, 85070551165415408562793303870112072196, 5151734495865961693857578731308040, 84405977732342307866996828645754442018, 40247925748948608378171909284420])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok7 : T7.all (fun c => !srch 8 c.1 c.2.1 c.2.2) = true := by
  decide +kernel

def T8 : List (ℕ × ℕ × List ℕ) :=
  [(1, 659422015490035892435049491487541393, [659422015490035892435049491487541393, 19342803963087006608670849, 659422015470693088544587461547018385, 40564799864490372263781043568898, 85070551165415408562793303870112072196, 5151734495865961693857578731308040, 84405977732342307866996828645754442018, 40247925748948608378171909284420])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok8 : T8.all (fun c => !srch 8 c.1 c.2.1 c.2.2) = true := by
  decide +kernel

def T9 : List (ℕ × ℕ × List ℕ) :=
  [(1, 149935135831111235534848, [149935135831111235534848, 19342803963087006608670849, 84405977732342307866996828645754442018, 40564799864490372263781043568898, 85070551165415408562793303870112072196, 5151734495865961693857578731308040, 659422015470693088544587461547018385, 40247925748948608378171909284420])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok9 : T9.all (fun c => !srch 8 c.1 c.2.1 c.2.2) = true := by
  decide +kernel

def T10 : List (ℕ × ℕ × List ℕ) :=
  [(1, 84405977732361500735824084541127578019, [84405977732361500735824084541127578019, 19342803963087006608670849, 84405977732342307866996828645754442018, 40564799864490372263781043568898, 85070551165415408562793303870112072196, 5151734495865961693857578731308040, 659422015470693088544587461547018385, 40247925748948608378171909284420])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok10 : T10.all (fun c => !srch 8 c.1 c.2.1 c.2.2) = true := by
  decide +kernel

def T11 : List (ℕ × ℕ × List ℕ) :=
  [(1, 19191697386382238148460544, [19191697386382238148460544, 19342803963087006608670849, 40247925748948608378171909284420, 40564799864490372263781043568898, 85070551165415408562793303870112072196, 5151734495865961693857578731308040, 659422015470693088544587461547018385, 84405977732342307866996828645754442018])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok11 : T11.all (fun c => !srch 8 c.1 c.2.1 c.2.2) = true := by
  decide +kernel

def T12 : List (ℕ × ℕ × List ℕ) :=
  [(1, 40247925900055185082940369494725, [40247925900055185082940369494725, 19342803963087006608670849, 40247925748948608378171909284420, 40564799864490372263781043568898, 85070551165415408562793303870112072196, 5151734495865961693857578731308040, 659422015470693088544587461547018385, 84405977732342307866996828645754442018]),
   (1, 85070591730215273053165567651155641094, [85070591730215273053165567651155641094, 40564799864490372263781043568898, 85070551165415408562793303870112072196, 19342803963087006608670849, 5151734495865961693857578731308040, 659422015470693088544587461547018385, 84405977732342307866996828645754442018, 40247925748948608378171909284420])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok12 : T12.all (fun c => !srch 8 c.1 c.2.1 c.2.2) = true := by
  decide +kernel

def T13 : List (ℕ × ℕ × List ℕ) :=
  [(1, 2456537265456926483002949632, [2456537265456926483002949632, 40564799864490372263781043568898, 5151734495865961693857578731308040, 19342803963087006608670849, 85070551165415408562793303870112072196, 659422015470693088544587461547018385, 84405977732342307866996828645754442018, 40247925748948608378171909284420])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok13 : T13.all (fun c => !srch 8 c.1 c.2.1 c.2.2) = true := by
  decide +kernel

def T14 : List (ℕ × ℕ × List ℕ) :=
  [(1, 5192296839193186609194876771927306, [5192296839193186609194876771927306, 40564799864490372263781043568898, 5151734495865961693857578731308040, 19342803963087006608670849, 85070551165415408562793303870112072196, 659422015470693088544587461547018385, 84405977732342307866996828645754442018, 40247925748948608378171909284420])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok14 : T14.all (fun c => !srch 8 c.1 c.2.1 c.2.2) = true := by
  decide +kernel

def T15 : List (ℕ × ℕ × List ℕ) :=
  [(1, 314436769978486589824377552896, [314436769978486589824377552896, 40564799864490372263781043568898, 659422015470693088544587461547018385, 19342803963087006608670849, 85070551165415408562793303870112072196, 5151734495865961693857578731308040, 84405977732342307866996828645754442018, 40247925748948608378171909284420])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok15 : T15.all (fun c => !srch 8 c.1 c.2.1 c.2.2) = true := by
  decide +kernel

def T16 : List (ℕ × ℕ × List ℕ) :=
  [(1, 659462265833787600430261418213034387, [659462265833787600430261418213034387, 40564799864490372263781043568898, 659422015470693088544587461547018385, 19342803963087006608670849, 85070551165415408562793303870112072196, 5151734495865961693857578731308040, 84405977732342307866996828645754442018, 40247925748948608378171909284420]),
   (1, 145249953336295682, [145249953336295682, 40564799864490372263781043568898, 84405977732342307866996828645754442018, 19342803963087006608670849, 85070551165415408562793303870112072196, 5151734495865961693857578731308040, 659422015470693088544587461547018385, 40247925748948608378171909284420])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok16 : T16.all (fun c => !srch 8 c.1 c.2.1 c.2.2) = true := by
  decide +kernel

def T17 : List (ℕ × ℕ × List ℕ) :=
  [(3, 84406018297142172357223842473461715234, [84406018297142172357223842473461715234, 19342803963087006608670849, 85070551165415408562793303870112072196, 5151734495865961693857578731308040, 659422015470693088544587461547018385, 40247925748948608378171909284420])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok17 : T17.all (fun c => !srch 8 c.1 c.2.1 c.2.2) = true := by
  decide +kernel

def T18 : List (ℕ × ℕ × List ℕ) :=
  [(2, 84406018297142172357223842473461715234, [84406018297142172357223842473461715234, 40564799864490372263781043568898, 19342803963087006608670849, 85070551165415408562793303870112072196, 5151734495865961693857578731308040, 659422015470693088544587461547018385, 40247925748948608378171909284420])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok18 : T18.all (fun c => !srch 8 c.1 c.2.1 c.2.2) = true := by
  decide +kernel

def T19 : List (ℕ × ℕ × List ℕ) :=
  [(2, 84406018297142172357223842473461715234, [84406018297142172357223842473461715234, 84405977732342307866996828645754442018, 19342803963087006608670849, 85070551165415408562793303870112072196, 5151734495865961693857578731308040, 659422015470693088544587461547018385, 40247925748948608378171909284420])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok19 : T19.all (fun c => !srch 8 c.1 c.2.1 c.2.2) = true := by
  decide +kernel

def T20 : List (ℕ × ℕ × List ℕ) :=
  [(1, 84406018297142172357223842473461715234, [84406018297142172357223842473461715234, 40564799864490372263781043568898, 84405977732342307866996828645754442018, 19342803963087006608670849, 85070551165415408562793303870112072196, 5151734495865961693857578731308040, 659422015470693088544587461547018385, 40247925748948608378171909284420])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok20 : T20.all (fun c => !srch 8 c.1 c.2.1 c.2.2) = true := by
  decide +kernel

def T21 : List (ℕ × ℕ × List ℕ) :=
  [(1, 40247906557246283497520326770688, [40247906557246283497520326770688, 40564799864490372263781043568898, 40247925748948608378171909284420, 19342803963087006608670849, 85070551165415408562793303870112072196, 5151734495865961693857578731308040, 659422015470693088544587461547018385, 84405977732342307866996828645754442018])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok21 : T21.all (fun c => !srch 8 c.1 c.2.1 c.2.2) = true := by
  decide +kernel

def T22 : List (ℕ × ℕ × List ℕ) :=
  [(1, 40564819056192697144432626082630, [40564819056192697144432626082630, 40564799864490372263781043568898, 40247925748948608378171909284420, 19342803963087006608670849, 85070551165415408562793303870112072196, 5151734495865961693857578731308040, 659422015470693088544587461547018385, 84405977732342307866996828645754442018])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok22 : T22.all (fun c => !srch 8 c.1 c.2.1 c.2.2) = true := by
  decide +kernel

def T23 : List (ℕ × ℕ × List ℕ) :=
  [(1, 5151732039327524287682601826648064, [5151732039327524287682601826648064, 85070551165415408562793303870112072196, 5151734495865961693857578731308040, 19342803963087006608670849, 40564799864490372263781043568898, 659422015470693088544587461547018385, 84405977732342307866996828645754442018, 40247925748948608378171909284420])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok23 : T23.all (fun c => !srch 8 c.1 c.2.1 c.2.2) = true := by
  decide +kernel

def T24 : List (ℕ × ℕ × List ℕ) :=
  [(1, 85070551167871947000199478847016732172, [85070551167871947000199478847016732172, 85070551165415408562793303870112072196, 5151734495865961693857578731308040, 19342803963087006608670849, 40564799864490372263781043568898, 659422015470693088544587461547018385, 84405977732342307866996828645754442018, 40247925748948608378171909284420])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok24 : T24.all (fun c => !srch 8 c.1 c.2.1 c.2.2) = true := by
  decide +kernel

def T25 : List (ℕ × ℕ × List ℕ) :=
  [(1, 659421701033923108823373033810952192, [659421701033923108823373033810952192, 85070551165415408562793303870112072196, 659422015470693088544587461547018385, 19342803963087006608670849, 40564799864490372263781043568898, 5151734495865961693857578731308040, 84405977732342307866996828645754442018, 40247925748948608378171909284420]),
   (1, 85070551479852178542514518297848138389, [85070551479852178542514518297848138389, 85070551165415408562793303870112072196, 659422015470693088544587461547018385, 19342803963087006608670849, 40564799864490372263781043568898, 5151734495865961693857578731308040, 84405977732342307866996828645754442018, 40247925748948608378171909284420])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok25 : T25.all (fun c => !srch 8 c.1 c.2.1 c.2.2) = true := by
  decide +kernel

def T26 : List (ℕ × ℕ × List ℕ) :=
  [(1, 84405977732342157929391748327801880576, [84405977732342157929391748327801880576, 85070551165415408562793303870112072196, 84405977732342307866996828645754442018, 19342803963087006608670849, 40564799864490372263781043568898, 5151734495865961693857578731308040, 659422015470693088544587461547018385, 40247925748948608378171909284420]),
   (1, 85070551165415558500398384188064633638, [85070551165415558500398384188064633638, 85070551165415408562793303870112072196, 84405977732342307866996828645754442018, 19342803963087006608670849, 40564799864490372263781043568898, 5151734495865961693857578731308040, 659422015470693088544587461547018385, 40247925748948608378171909284420]),
   (1, 290499906672591364, [290499906672591364, 85070551165415408562793303870112072196, 40247925748948608378171909284420, 19342803963087006608670849, 40564799864490372263781043568898, 5151734495865961693857578731308040, 659422015470693088544587461547018385, 84405977732342307866996828645754442018])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok26 : T26.all (fun c => !srch 8 c.1 c.2.1 c.2.2) = true := by
  decide +kernel

def T27 : List (ℕ × ℕ × List ℕ) :=
  [(3, 85070591413341157511111182135348765252, [85070591413341157511111182135348765252, 19342803963087006608670849, 40564799864490372263781043568898, 5151734495865961693857578731308040, 659422015470693088544587461547018385, 84405977732342307866996828645754442018])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok27 : T27.all (fun c => !srch 8 c.1 c.2.1 c.2.2) = true := by
  decide +kernel

def T28 : List (ℕ × ℕ × List ℕ) :=
  [(2, 85070591413341157511111182135348765252, [85070591413341157511111182135348765252, 85070551165415408562793303870112072196, 19342803963087006608670849, 40564799864490372263781043568898, 5151734495865961693857578731308040, 659422015470693088544587461547018385, 84405977732342307866996828645754442018]),
   (2, 85070591413341157511111182135348765252, [85070591413341157511111182135348765252, 40247925748948608378171909284420, 19342803963087006608670849, 40564799864490372263781043568898, 5151734495865961693857578731308040, 659422015470693088544587461547018385, 84405977732342307866996828645754442018]),
   (1, 85070591413341157511111182135348765252, [85070591413341157511111182135348765252, 85070551165415408562793303870112072196, 40247925748948608378171909284420, 19342803963087006608670849, 40564799864490372263781043568898, 5151734495865961693857578731308040, 659422015470693088544587461547018385, 84405977732342307866996828645754442018])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok28 : T28.all (fun c => !srch 8 c.1 c.2.1 c.2.2) = true := by
  decide +kernel

def T29 : List (ℕ × ℕ × List ℕ) :=
  [(2, 664573749966559050238445040278326425, [664573749966559050238445040278326425, 5151734495865961693857578731308040, 19342803963087006608670849, 40564799864490372263781043568898, 85070551165415408562793303870112072196, 84405977732342307866996828645754442018, 40247925748948608378171909284420])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok29 : T29.all (fun c => !srch 8 c.1 c.2.1 c.2.2) = true := by
  decide +kernel

def T30 : List (ℕ × ℕ × List ℕ) :=
  [(1, 664573749966559050238445040278326425, [664573749966559050238445040278326425, 5151734495865961693857578731308040, 659422015470693088544587461547018385, 19342803963087006608670849, 40564799864490372263781043568898, 85070551165415408562793303870112072196, 84405977732342307866996828645754442018, 40247925748948608378171909284420]),
   (2, 84411129466838173828690686224485750058, [84411129466838173828690686224485750058, 5151734495865961693857578731308040, 19342803963087006608670849, 40564799864490372263781043568898, 85070551165415408562793303870112072196, 659422015470693088544587461547018385, 40247925748948608378171909284420])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok30 : T30.all (fun c => !srch 8 c.1 c.2.1 c.2.2) = true := by
  decide +kernel

def T31 : List (ℕ × ℕ × List ℕ) :=
  [(1, 84411129466838173828690686224485750058, [84411129466838173828690686224485750058, 5151734495865961693857578731308040, 84405977732342307866996828645754442018, 19342803963087006608670849, 40564799864490372263781043568898, 85070551165415408562793303870112072196, 659422015470693088544587461547018385, 40247925748948608378171909284420])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok31 : T31.all (fun c => !srch 8 c.1 c.2.1 c.2.2) = true := by
  decide +kernel

def T32 : List (ℕ × ℕ × List ℕ) :=
  [(2, 5191982421614910302235750640592460, [5191982421614910302235750640592460, 5151734495865961693857578731308040, 19342803963087006608670849, 40564799864490372263781043568898, 85070551165415408562793303870112072196, 659422015470693088544587461547018385, 84405977732342307866996828645754442018])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok32 : T32.all (fun c => !srch 8 c.1 c.2.1 c.2.2) = true := by
  decide +kernel

def T33 : List (ℕ × ℕ × List ℕ) :=
  [(1, 5191982421614910302235750640592460, [5191982421614910302235750640592460, 5151734495865961693857578731308040, 40247925748948608378171909284420, 19342803963087006608670849, 40564799864490372263781043568898, 85070551165415408562793303870112072196, 659422015470693088544587461547018385, 84405977732342307866996828645754442018]),
   (1, 85065399747813000955541416107301460403, [85065399747813000955541416107301460403, 659422015470693088544587461547018385, 84405977732342307866996828645754442018, 19342803963087006608670849, 40564799864490372263781043568898, 85070551165415408562793303870112072196, 5151734495865961693857578731308040, 40247925748948608378171909284420])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok33 : T33.all (fun c => !srch 8 c.1 c.2.1 c.2.2) = true := by
  decide +kernel

def T34 : List (ℕ × ℕ × List ℕ) :=
  [(1, 659462263396442037152965633456302805, [659462263396442037152965633456302805, 659422015470693088544587461547018385, 40247925748948608378171909284420, 19342803963087006608670849, 40564799864490372263781043568898, 85070551165415408562793303870112072196, 5151734495865961693857578731308040, 84405977732342307866996828645754442018]),
   (1, 84406017980268056815605206817663726438, [84406017980268056815605206817663726438, 84405977732342307866996828645754442018, 40247925748948608378171909284420, 19342803963087006608670849, 40564799864490372263781043568898, 85070551165415408562793303870112072196, 5151734495865961693857578731308040, 659422015470693088544587461547018385]),
   (0, 40564819207294335350787652239747, [40564819207294335350787652239747, 19342803963087006608670849, 40564799864490372263781043568898, 85070551165415408562793303870112072196, 8714997200177740920, 5151734495865961693857578731308040, 659422015470693088544587461547018385, 84405977732342307866996828645754442018, 40247925748948608378171909284420]),
   (0, 85070551165434751366756390876720743045, [85070551165434751366756390876720743045, 19342803963087006608670849, 85070551165415408562793303870112072196, 40564799864490372263781043568898, 8714997200177740920, 5151734495865961693857578731308040, 659422015470693088544587461547018385, 84405977732342307866996828645754442018, 40247925748948608378171909284420]),
   (1, 19342812678084206786411769, [19342812678084206786411769, 19342803963087006608670849, 40564799864490372263781043568898, 85070551165415408562793303870112072196, 5151734495865961693857578731308040, 659422015470693088544587461547018385, 84405977732342307866996828645754442018, 40247925748948608378171909284420]),
   (0, 19342812678084206786411769, [19342812678084206786411769, 19342803963087006608670849, 8714997200177740920, 40564799864490372263781043568898, 85070551165415408562793303870112072196, 5151734495865961693857578731308040, 659422015470693088544587461547018385, 84405977732342307866996828645754442018, 40247925748948608378171909284420]),
   (0, 1171368248680556527616, [1171368248680556527616, 19342803963087006608670849, 5151734495865961693857578731308040, 40564799864490372263781043568898, 85070551165415408562793303870112072196, 8714997200177740920, 659422015470693088544587461547018385, 84405977732342307866996828645754442018, 40247925748948608378171909284420]),
   (0, 5151734515207594288695904783451273, [5151734515207594288695904783451273, 19342803963087006608670849, 5151734495865961693857578731308040, 40564799864490372263781043568898, 85070551165415408562793303870112072196, 8714997200177740920, 659422015470693088544587461547018385, 84405977732342307866996828645754442018, 40247925748948608378171909284420]),
   (0, 72624976668147841, [72624976668147841, 19342803963087006608670849, 659422015470693088544587461547018385, 40564799864490372263781043568898, 85070551165415408562793303870112072196, 8714997200177740920, 5151734495865961693857578731308040, 84405977732342307866996828645754442018, 40247925748948608378171909284420])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok34 : T34.all (fun c => !srch 8 c.1 c.2.1 c.2.2) = true := by
  decide +kernel

def T35 : List (ℕ × ℕ × List ℕ) :=
  [(2, 659422015490035892435049491487541393, [659422015490035892435049491487541393, 40564799864490372263781043568898, 85070551165415408562793303870112072196, 8714997200177740920, 5151734495865961693857578731308040, 84405977732342307866996828645754442018, 40247925748948608378171909284420])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok35 : T35.all (fun c => !srch 8 c.1 c.2.1 c.2.2) = true := by
  decide +kernel

def T36 : List (ℕ × ℕ × List ℕ) :=
  [(1, 659422015490035892435049491487541393, [659422015490035892435049491487541393, 19342803963087006608670849, 40564799864490372263781043568898, 85070551165415408562793303870112072196, 8714997200177740920, 5151734495865961693857578731308040, 84405977732342307866996828645754442018, 40247925748948608378171909284420]),
   (1, 659422015490035892435049491487541393, [659422015490035892435049491487541393, 659422015470693088544587461547018385, 40564799864490372263781043568898, 85070551165415408562793303870112072196, 8714997200177740920, 5151734495865961693857578731308040, 84405977732342307866996828645754442018, 40247925748948608378171909284420]),
   (0, 659422015490035892435049491487541393, [659422015490035892435049491487541393, 19342803963087006608670849, 659422015470693088544587461547018385, 40564799864490372263781043568898, 85070551165415408562793303870112072196, 8714997200177740920, 5151734495865961693857578731308040, 84405977732342307866996828645754442018, 40247925748948608378171909284420]),
   (0, 149935135831111235534848, [149935135831111235534848, 19342803963087006608670849, 84405977732342307866996828645754442018, 40564799864490372263781043568898, 85070551165415408562793303870112072196, 8714997200177740920, 5151734495865961693857578731308040, 659422015470693088544587461547018385, 40247925748948608378171909284420]),
   (0, 84405977732361500735824084541127578019, [84405977732361500735824084541127578019, 19342803963087006608670849, 84405977732342307866996828645754442018, 40564799864490372263781043568898, 85070551165415408562793303870112072196, 8714997200177740920, 5151734495865961693857578731308040, 659422015470693088544587461547018385, 40247925748948608378171909284420]),
   (0, 19191697386382238148460544, [19191697386382238148460544, 19342803963087006608670849, 40247925748948608378171909284420, 40564799864490372263781043568898, 85070551165415408562793303870112072196, 8714997200177740920, 5151734495865961693857578731308040, 659422015470693088544587461547018385, 84405977732342307866996828645754442018]),
   (0, 40247925900055185082940369494725, [40247925900055185082940369494725, 19342803963087006608670849, 40247925748948608378171909284420, 40564799864490372263781043568898, 85070551165415408562793303870112072196, 8714997200177740920, 5151734495865961693857578731308040, 659422015470693088544587461547018385, 84405977732342307866996828645754442018]),
   (0, 85070591730215273053165567651155641094, [85070591730215273053165567651155641094, 40564799864490372263781043568898, 85070551165415408562793303870112072196, 19342803963087006608670849, 8714997200177740920, 5151734495865961693857578731308040, 659422015470693088544587461547018385, 84405977732342307866996828645754442018, 40247925748948608378171909284420]),
   (1, 40564799864499087260981221309818, [40564799864499087260981221309818, 40564799864490372263781043568898, 19342803963087006608670849, 85070551165415408562793303870112072196, 5151734495865961693857578731308040, 659422015470693088544587461547018385, 84405977732342307866996828645754442018, 40247925748948608378171909284420]),
   (0, 40564799864499087260981221309818, [40564799864499087260981221309818, 40564799864490372263781043568898, 8714997200177740920, 19342803963087006608670849, 85070551165415408562793303870112072196, 5151734495865961693857578731308040, 659422015470693088544587461547018385, 84405977732342307866996828645754442018, 40247925748948608378171909284420]),
   (0, 2456537265456926483002949632, [2456537265456926483002949632, 40564799864490372263781043568898, 5151734495865961693857578731308040, 19342803963087006608670849, 85070551165415408562793303870112072196, 8714997200177740920, 659422015470693088544587461547018385, 84405977732342307866996828645754442018, 40247925748948608378171909284420])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok36 : T36.all (fun c => !srch 8 c.1 c.2.1 c.2.2) = true := by
  decide +kernel

def T37 : List (ℕ × ℕ × List ℕ) :=
  [(0, 5192296839193186609194876771927306, [5192296839193186609194876771927306, 40564799864490372263781043568898, 5151734495865961693857578731308040, 19342803963087006608670849, 85070551165415408562793303870112072196, 8714997200177740920, 659422015470693088544587461547018385, 84405977732342307866996828645754442018, 40247925748948608378171909284420]),
   (0, 314436769978486589824377552896, [314436769978486589824377552896, 40564799864490372263781043568898, 659422015470693088544587461547018385, 19342803963087006608670849, 85070551165415408562793303870112072196, 8714997200177740920, 5151734495865961693857578731308040, 84405977732342307866996828645754442018, 40247925748948608378171909284420]),
   (0, 659462265833787600430261418213034387, [659462265833787600430261418213034387, 40564799864490372263781043568898, 659422015470693088544587461547018385, 19342803963087006608670849, 85070551165415408562793303870112072196, 8714997200177740920, 5151734495865961693857578731308040, 84405977732342307866996828645754442018, 40247925748948608378171909284420]),
   (0, 145249953336295682, [145249953336295682, 40564799864490372263781043568898, 84405977732342307866996828645754442018, 19342803963087006608670849, 85070551165415408562793303870112072196, 8714997200177740920, 5151734495865961693857578731308040, 659422015470693088544587461547018385, 40247925748948608378171909284420]),
   (2, 84406018297142172357223842473461715234, [84406018297142172357223842473461715234, 19342803963087006608670849, 85070551165415408562793303870112072196, 8714997200177740920, 5151734495865961693857578731308040, 659422015470693088544587461547018385, 40247925748948608378171909284420]),
   (1, 84406018297142172357223842473461715234, [84406018297142172357223842473461715234, 40564799864490372263781043568898, 19342803963087006608670849, 85070551165415408562793303870112072196, 8714997200177740920, 5151734495865961693857578731308040, 659422015470693088544587461547018385, 40247925748948608378171909284420]),
   (1, 84406018297142172357223842473461715234, [84406018297142172357223842473461715234, 84405977732342307866996828645754442018, 19342803963087006608670849, 85070551165415408562793303870112072196, 8714997200177740920, 5151734495865961693857578731308040, 659422015470693088544587461547018385, 40247925748948608378171909284420]),
   (0, 84406018297142172357223842473461715234, [84406018297142172357223842473461715234, 40564799864490372263781043568898, 84405977732342307866996828645754442018, 19342803963087006608670849, 85070551165415408562793303870112072196, 8714997200177740920, 5151734495865961693857578731308040, 659422015470693088544587461547018385, 40247925748948608378171909284420]),
   (0, 40247906557246283497520326770688, [40247906557246283497520326770688, 40564799864490372263781043568898, 40247925748948608378171909284420, 19342803963087006608670849, 85070551165415408562793303870112072196, 8714997200177740920, 5151734495865961693857578731308040, 659422015470693088544587461547018385, 84405977732342307866996828645754442018]),
   (0, 40564819056192697144432626082630, [40564819056192697144432626082630, 40564799864490372263781043568898, 40247925748948608378171909284420, 19342803963087006608670849, 85070551165415408562793303870112072196, 8714997200177740920, 5151734495865961693857578731308040, 659422015470693088544587461547018385, 84405977732342307866996828645754442018]),
   (1, 85070551165415408571508301070289813116, [85070551165415408571508301070289813116, 85070551165415408562793303870112072196, 19342803963087006608670849, 40564799864490372263781043568898, 5151734495865961693857578731308040, 659422015470693088544587461547018385, 84405977732342307866996828645754442018, 40247925748948608378171909284420]),
   (0, 85070551165415408571508301070289813116, [85070551165415408571508301070289813116, 85070551165415408562793303870112072196, 8714997200177740920, 19342803963087006608670849, 40564799864490372263781043568898, 5151734495865961693857578731308040, 659422015470693088544587461547018385, 84405977732342307866996828645754442018, 40247925748948608378171909284420])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok37 : T37.all (fun c => !srch 8 c.1 c.2.1 c.2.2) = true := by
  decide +kernel

def T38 : List (ℕ × ℕ × List ℕ) :=
  [(0, 5151732039327524287682601826648064, [5151732039327524287682601826648064, 85070551165415408562793303870112072196, 5151734495865961693857578731308040, 19342803963087006608670849, 40564799864490372263781043568898, 8714997200177740920, 659422015470693088544587461547018385, 84405977732342307866996828645754442018, 40247925748948608378171909284420]),
   (0, 85070551167871947000199478847016732172, [85070551167871947000199478847016732172, 85070551165415408562793303870112072196, 5151734495865961693857578731308040, 19342803963087006608670849, 40564799864490372263781043568898, 8714997200177740920, 659422015470693088544587461547018385, 84405977732342307866996828645754442018, 40247925748948608378171909284420]),
   (0, 659421701033923108823373033810952192, [659421701033923108823373033810952192, 85070551165415408562793303870112072196, 659422015470693088544587461547018385, 19342803963087006608670849, 40564799864490372263781043568898, 8714997200177740920, 5151734495865961693857578731308040, 84405977732342307866996828645754442018, 40247925748948608378171909284420]),
   (0, 85070551479852178542514518297848138389, [85070551479852178542514518297848138389, 85070551165415408562793303870112072196, 659422015470693088544587461547018385, 19342803963087006608670849, 40564799864490372263781043568898, 8714997200177740920, 5151734495865961693857578731308040, 84405977732342307866996828645754442018, 40247925748948608378171909284420]),
   (0, 84405977732342157929391748327801880576, [84405977732342157929391748327801880576, 85070551165415408562793303870112072196, 84405977732342307866996828645754442018, 19342803963087006608670849, 40564799864490372263781043568898, 8714997200177740920, 5151734495865961693857578731308040, 659422015470693088544587461547018385, 40247925748948608378171909284420]),
   (0, 85070551165415558500398384188064633638, [85070551165415558500398384188064633638, 85070551165415408562793303870112072196, 84405977732342307866996828645754442018, 19342803963087006608670849, 40564799864490372263781043568898, 8714997200177740920, 5151734495865961693857578731308040, 659422015470693088544587461547018385, 40247925748948608378171909284420]),
   (0, 290499906672591364, [290499906672591364, 85070551165415408562793303870112072196, 40247925748948608378171909284420, 19342803963087006608670849, 40564799864490372263781043568898, 8714997200177740920, 5151734495865961693857578731308040, 659422015470693088544587461547018385, 84405977732342307866996828645754442018]),
   (2, 85070591413341157511111182135348765252, [85070591413341157511111182135348765252, 19342803963087006608670849, 40564799864490372263781043568898, 8714997200177740920, 5151734495865961693857578731308040, 659422015470693088544587461547018385, 84405977732342307866996828645754442018]),
   (1, 85070591413341157511111182135348765252, [85070591413341157511111182135348765252, 85070551165415408562793303870112072196, 19342803963087006608670849, 40564799864490372263781043568898, 8714997200177740920, 5151734495865961693857578731308040, 659422015470693088544587461547018385, 84405977732342307866996828645754442018]),
   (1, 85070591413341157511111182135348765252, [85070591413341157511111182135348765252, 40247925748948608378171909284420, 19342803963087006608670849, 40564799864490372263781043568898, 8714997200177740920, 5151734495865961693857578731308040, 659422015470693088544587461547018385, 84405977732342307866996828645754442018]),
   (0, 85070591413341157511111182135348765252, [85070591413341157511111182135348765252, 85070551165415408562793303870112072196, 40247925748948608378171909284420, 19342803963087006608670849, 40564799864490372263781043568898, 8714997200177740920, 5151734495865961693857578731308040, 659422015470693088544587461547018385, 84405977732342307866996828645754442018]),
   (1, 580999813345182728, [580999813345182728, 5151734495865961693857578731308040, 19342803963087006608670849, 40564799864490372263781043568898, 85070551165415408562793303870112072196, 659422015470693088544587461547018385, 84405977732342307866996828645754442018, 40247925748948608378171909284420]),
   (0, 580999813345182728, [580999813345182728, 8714997200177740920, 5151734495865961693857578731308040, 19342803963087006608670849, 40564799864490372263781043568898, 85070551165415408562793303870112072196, 659422015470693088544587461547018385, 84405977732342307866996828645754442018, 40247925748948608378171909284420]),
   (2, 5151734495865969827854965563866232, [5151734495865969827854965563866232, 19342803963087006608670849, 40564799864490372263781043568898, 85070551165415408562793303870112072196, 659422015470693088544587461547018385, 84405977732342307866996828645754442018, 40247925748948608378171909284420]),
   (1, 5151734495865969827854965563866232, [5151734495865969827854965563866232, 8714997200177740920, 19342803963087006608670849, 40564799864490372263781043568898, 85070551165415408562793303870112072196, 659422015470693088544587461547018385, 84405977732342307866996828645754442018, 40247925748948608378171909284420])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok38 : T38.all (fun c => !srch 8 c.1 c.2.1 c.2.2) = true := by
  decide +kernel

def T39 : List (ℕ × ℕ × List ℕ) :=
  [(1, 5151734495865969827854965563866232, [5151734495865969827854965563866232, 5151734495865961693857578731308040, 19342803963087006608670849, 40564799864490372263781043568898, 85070551165415408562793303870112072196, 659422015470693088544587461547018385, 84405977732342307866996828645754442018, 40247925748948608378171909284420]),
   (0, 5151734495865969827854965563866232, [5151734495865969827854965563866232, 8714997200177740920, 5151734495865961693857578731308040, 19342803963087006608670849, 40564799864490372263781043568898, 85070551165415408562793303870112072196, 659422015470693088544587461547018385, 84405977732342307866996828645754442018, 40247925748948608378171909284420]),
   (1, 1161999626690365456, [1161999626690365456, 659422015470693088544587461547018385, 19342803963087006608670849, 40564799864490372263781043568898, 85070551165415408562793303870112072196, 5151734495865961693857578731308040, 84405977732342307866996828645754442018, 40247925748948608378171909284420])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok39 : T39.all (fun c => !srch 8 c.1 c.2.1 c.2.2) = true := by
  decide +kernel

def T40 : List (ℕ × ℕ × List ℕ) :=
  [(0, 1161999626690365456, [1161999626690365456, 8714997200177740920, 659422015470693088544587461547018385, 19342803963087006608670849, 40564799864490372263781043568898, 85070551165415408562793303870112072196, 5151734495865961693857578731308040, 84405977732342307866996828645754442018, 40247925748948608378171909284420]),
   (2, 659422015470693096097585035034393849, [659422015470693096097585035034393849, 19342803963087006608670849, 40564799864490372263781043568898, 85070551165415408562793303870112072196, 5151734495865961693857578731308040, 84405977732342307866996828645754442018, 40247925748948608378171909284420]),
   (1, 659422015470693096097585035034393849, [659422015470693096097585035034393849, 8714997200177740920, 19342803963087006608670849, 40564799864490372263781043568898, 85070551165415408562793303870112072196, 5151734495865961693857578731308040, 84405977732342307866996828645754442018, 40247925748948608378171909284420]),
   (1, 659422015470693096097585035034393849, [659422015470693096097585035034393849, 659422015470693088544587461547018385, 19342803963087006608670849, 40564799864490372263781043568898, 85070551165415408562793303870112072196, 5151734495865961693857578731308040, 84405977732342307866996828645754442018, 40247925748948608378171909284420]),
   (0, 659422015470693096097585035034393849, [659422015470693096097585035034393849, 8714997200177740920, 659422015470693088544587461547018385, 19342803963087006608670849, 40564799864490372263781043568898, 85070551165415408562793303870112072196, 5151734495865961693857578731308040, 84405977732342307866996828645754442018, 40247925748948608378171909284420]),
   (1, 2323999253380730912, [2323999253380730912, 84405977732342307866996828645754442018, 19342803963087006608670849, 40564799864490372263781043568898, 85070551165415408562793303870112072196, 5151734495865961693857578731308040, 659422015470693088544587461547018385, 40247925748948608378171909284420]),
   (0, 2323999253380730912, [2323999253380730912, 8714997200177740920, 84405977732342307866996828645754442018, 19342803963087006608670849, 40564799864490372263781043568898, 85070551165415408562793303870112072196, 5151734495865961693857578731308040, 659422015470693088544587461547018385, 40247925748948608378171909284420]),
   (2, 84405977732342307873387826592551452026, [84405977732342307873387826592551452026, 19342803963087006608670849, 40564799864490372263781043568898, 85070551165415408562793303870112072196, 5151734495865961693857578731308040, 659422015470693088544587461547018385, 40247925748948608378171909284420]),
   (1, 84405977732342307873387826592551452026, [84405977732342307873387826592551452026, 8714997200177740920, 19342803963087006608670849, 40564799864490372263781043568898, 85070551165415408562793303870112072196, 5151734495865961693857578731308040, 659422015470693088544587461547018385, 40247925748948608378171909284420]),
   (1, 84405977732342307873387826592551452026, [84405977732342307873387826592551452026, 84405977732342307866996828645754442018, 19342803963087006608670849, 40564799864490372263781043568898, 85070551165415408562793303870112072196, 5151734495865961693857578731308040, 659422015470693088544587461547018385, 40247925748948608378171909284420]),
   (0, 84405977732342307873387826592551452026, [84405977732342307873387826592551452026, 8714997200177740920, 84405977732342307866996828645754442018, 19342803963087006608670849, 40564799864490372263781043568898, 85070551165415408562793303870112072196, 5151734495865961693857578731308040, 659422015470693088544587461547018385, 40247925748948608378171909284420])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok40 : T40.all (fun c => !srch 8 c.1 c.2.1 c.2.2) = true := by
  decide +kernel

def T41 : List (ℕ × ℕ × List ℕ) :=
  [(1, 4647998506761461824, [4647998506761461824, 40247925748948608378171909284420, 19342803963087006608670849, 40564799864490372263781043568898, 85070551165415408562793303870112072196, 5151734495865961693857578731308040, 659422015470693088544587461547018385, 84405977732342307866996828645754442018]),
   (0, 4647998506761461824, [4647998506761461824, 8714997200177740920, 40247925748948608378171909284420, 19342803963087006608670849, 40564799864490372263781043568898, 85070551165415408562793303870112072196, 5151734495865961693857578731308040, 659422015470693088544587461547018385, 84405977732342307866996828645754442018]),
   (2, 40247925748952675376865325563516, [40247925748952675376865325563516, 19342803963087006608670849, 40564799864490372263781043568898, 85070551165415408562793303870112072196, 5151734495865961693857578731308040, 659422015470693088544587461547018385, 84405977732342307866996828645754442018]),
   (1, 40247925748952675376865325563516, [40247925748952675376865325563516, 8714997200177740920, 19342803963087006608670849, 40564799864490372263781043568898, 85070551165415408562793303870112072196, 5151734495865961693857578731308040, 659422015470693088544587461547018385, 84405977732342307866996828645754442018]),
   (1, 40247925748952675376865325563516, [40247925748952675376865325563516, 40247925748948608378171909284420, 19342803963087006608670849, 40564799864490372263781043568898, 85070551165415408562793303870112072196, 5151734495865961693857578731308040, 659422015470693088544587461547018385, 84405977732342307866996828645754442018]),
   (0, 40247925748952675376865325563516, [40247925748952675376865325563516, 8714997200177740920, 40247925748948608378171909284420, 19342803963087006608670849, 40564799864490372263781043568898, 85070551165415408562793303870112072196, 5151734495865961693857578731308040, 659422015470693088544587461547018385, 84405977732342307866996828645754442018]),
   (1, 664573749966559050238445040278326425, [664573749966559050238445040278326425, 5151734495865961693857578731308040, 19342803963087006608670849, 40564799864490372263781043568898, 85070551165415408562793303870112072196, 8714997200177740920, 84405977732342307866996828645754442018, 40247925748948608378171909284420]),
   (0, 664573749966559050238445040278326425, [664573749966559050238445040278326425, 5151734495865961693857578731308040, 659422015470693088544587461547018385, 19342803963087006608670849, 40564799864490372263781043568898, 85070551165415408562793303870112072196, 8714997200177740920, 84405977732342307866996828645754442018, 40247925748948608378171909284420]),
   (1, 84411129466838173828690686224485750058, [84411129466838173828690686224485750058, 5151734495865961693857578731308040, 19342803963087006608670849, 40564799864490372263781043568898, 85070551165415408562793303870112072196, 8714997200177740920, 659422015470693088544587461547018385, 40247925748948608378171909284420]),
   (0, 84411129466838173828690686224485750058, [84411129466838173828690686224485750058, 5151734495865961693857578731308040, 84405977732342307866996828645754442018, 19342803963087006608670849, 40564799864490372263781043568898, 85070551165415408562793303870112072196, 8714997200177740920, 659422015470693088544587461547018385, 40247925748948608378171909284420])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok41 : T41.all (fun c => !srch 8 c.1 c.2.1 c.2.2) = true := by
  decide +kernel

def T42 : List (ℕ × ℕ × List ℕ) :=
  [(1, 5191982421614910302235750640592460, [5191982421614910302235750640592460, 5151734495865961693857578731308040, 19342803963087006608670849, 40564799864490372263781043568898, 85070551165415408562793303870112072196, 8714997200177740920, 659422015470693088544587461547018385, 84405977732342307866996828645754442018]),
   (0, 5191982421614910302235750640592460, [5191982421614910302235750640592460, 5151734495865961693857578731308040, 40247925748948608378171909284420, 19342803963087006608670849, 40564799864490372263781043568898, 85070551165415408562793303870112072196, 8714997200177740920, 659422015470693088544587461547018385, 84405977732342307866996828645754442018]),
   (0, 85065399747813000955541416107301460403, [85065399747813000955541416107301460403, 659422015470693088544587461547018385, 84405977732342307866996828645754442018, 19342803963087006608670849, 40564799864490372263781043568898, 85070551165415408562793303870112072196, 8714997200177740920, 5151734495865961693857578731308040, 40247925748948608378171909284420]),
   (0, 659462263396442037152965633456302805, [659462263396442037152965633456302805, 659422015470693088544587461547018385, 40247925748948608378171909284420, 19342803963087006608670849, 40564799864490372263781043568898, 85070551165415408562793303870112072196, 8714997200177740920, 5151734495865961693857578731308040, 84405977732342307866996828645754442018]),
   (0, 84406017980268056815605206817663726438, [84406017980268056815605206817663726438, 84405977732342307866996828645754442018, 40247925748948608378171909284420, 19342803963087006608670849, 40564799864490372263781043568898, 85070551165415408562793303870112072196, 8714997200177740920, 5151734495865961693857578731308040, 659422015470693088544587461547018385])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ok42 : T42.all (fun c => !srch 8 c.1 c.2.1 c.2.2) = true := by
  decide +kernel

def TAB : List (ℕ × ℕ × List ℕ) := T0 ++ T1 ++ T2 ++ T3 ++ T4 ++ T5 ++ T6 ++ T7 ++ T8 ++ T9 ++ T10 ++ T11 ++ T12 ++ T13 ++ T14 ++ T15 ++ T16 ++ T17 ++ T18 ++ T19 ++ T20 ++ T21 ++ T22 ++ T23 ++ T24 ++ T25 ++ T26 ++ T27 ++ T28 ++ T29 ++ T30 ++ T31 ++ T32 ++ T33 ++ T34 ++ T35 ++ T36 ++ T37 ++ T38 ++ T39 ++ T40 ++ T41 ++ T42

theorem tab_ok : TAB.all (fun c => !srch 8 c.1 c.2.1 c.2.2) = true := by
  simp only [TAB, List.all_append, ok0, ok1, ok2, ok3, ok4, ok5, ok6, ok7, ok8, ok9, ok10, ok11, ok12, ok13, ok14, ok15, ok16, ok17, ok18, ok19, ok20, ok21, ok22, ok23, ok24, ok25, ok26, ok27, ok28, ok29, ok30, ok31, ok32, ok33, ok34, ok35, ok36, ok37, ok38, ok39, ok40, ok41, ok42, Bool.and_self]

def srchM (e last : ℕ) (ws : List ℕ) : Bool :=
  if (e, last, ws) ∈ TAB then false else srch 8 e last ws

theorem srchM_eq : srchM = srch 8 := by
  funext e last ws
  unfold srchM
  split_ifs with hc
  · have h := List.all_eq_true.mp tab_ok _ hc
    revert h
    cases srch 8 e last ws <;> simp
  · rfl

def top (e : ℕ) (ws : List ℕ) : Bool :=
  ws == [target] || (splits ws).any fun p => stepS e 0 srchM p.1 p.2.1 p.2.2

theorem top_eq (e : ℕ) (ws : List ℕ) : top e ws = srch 9 e 0 ws := by
  simp only [top, srchM_eq, srch]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem roots_ok : ins.sublists.all (fun l => decide (10 < l.length) ||
    !(isFull (covL l)) || !(top (10 - l.length) l)) = true := by
  decide +kernel

theorem no_small (C : Circuit)
    (hm : ∀ g ∈ C.gates, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hs : C.size ≤ 9) (hr : PEqualNP.Represents.Represents (fun u v : Fin 4 => (1981 : ℕ).testBit (4 * u.val + v.val)) C) : False := by
  have hg : ∀ g ∈ C.gates, Legal g := hm
  have hv : (C.gates.foldl wstep ins).getD C.output 0 = target := by
    apply Nat.eq_of_testBit_eq
    intro k
    by_cases hk : k < NN + NN
    · have h1 := hr (pt k).1 (pt k).2
      have hi : ins.map (bit k) = PEqualNP.Represents.oneEach (pt k).1 (pt k).2 := ins_rows ⟨k, hk⟩
      have h2 : bit k target = _ := target_rows ⟨k, hk⟩
      simp only [Circuit.eval, Circuit.wires] at h1
      rw [← hi, wires_bits C.gates hg ins hk, read_bit] at h1
      simp only [bit] at h1 h2
      rw [h1, h2]
    · have hb1 : (C.gates.foldl wstep ins).getD C.output 0 < B := by
        rcases getD_mem_or (C.gates.foldl wstep ins) C.output with h | h
        · rw [h]; exact zero_lt_B
        · exact wires_lt C.gates ins ins_lt _ h
      rw [bit_high hb1 (by omega), bit_high target_lt (by omega)]
  have hreach := compile C.gates hg C.output ins ins.toFinset
    (fun t ht => ⟨ins_lt t ht, Or.inr (Or.inr (List.mem_toFinset.mpr ht))⟩) hv
  obtain ⟨gs, hlen, hord, L, hLP, hlive⟩ := reach_ordered id hreach
  have hlenk : gs.length ≤ 9 := le_trans hlen hs
  let l := ins.filter (fun w => decide (w ∈ L))
  have hlL : l.toFinset = L := by
    ext v
    simp only [l, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨List.mem_toFinset.mp (hLP h), h⟩⟩
  have hnd : l.Nodup := ins_nodup.filter _
  have hcard := live_card hlive
  rw [← hlL, List.toFinset_card_of_nodup hnd] at hcard
  rw [← hlL] at hlive
  have hcov := cover_full hlive
  have hsrch := srch_complete 9 l (10 - l.length) 0 gs hnd hlenk (by omega) hord hlive
  rw [← top_eq] at hsrch
  have hmem : l ∈ ins.sublists := List.mem_sublists.mpr List.filter_sublist
  have hrow := List.all_eq_true.mp roots_ok l hmem
  have h4 : decide (10 < l.length) = false := by simp; omega
  have h5 : (!(isFull (covL l))) = false := by simp [isFull_of hcov]
  rw [h4, h5, hsrch] at hrow
  exact Bool.noConfusion hrow

theorem upper : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (1981 : ℕ).testBit (4 * u.val + v.val)) 10 := by
  refine ⟨⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [0, 2]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.or, [4, 7]⟩, ⟨GateOp.and, [8, 12]⟩, ⟨GateOp.and, [10, 11]⟩, ⟨GateOp.and, [6, 9]⟩, ⟨GateOp.or, [13, 15]⟩, ⟨GateOp.or, [14, 16]⟩], 17⟩, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_6337

theorem PEqualNP.Outside.L_meta_6337 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (1981 : ℕ).testBit (4 * u.val + v.val)) 10 ∧
  ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (1981 : ℕ).testBit (4 * u.val + v.val)) 9 := by
  refine ⟨PEqualNP.Outside.L_meta_6337.upper, ?_⟩
  rintro ⟨C, hm, hs, hr⟩
  exact PEqualNP.Outside.L_meta_6337.no_small C hm hs hr
