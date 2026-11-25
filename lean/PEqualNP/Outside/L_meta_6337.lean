import PEqualNP.Defs

-- The ordered live-wire search is adapted from the checked L-meta-6341 proof.

namespace PEqualNP.Outside.L_meta_6337

section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

theorem build_mono {ops : α → α → Finset α} {goal : α} {k : ℕ} {s t : Finset α}
    (hsub : s ⊆ t) (h : build ops goal k s) : build ops goal k t := by
  induction k generalizing s t with
  | zero => exact hsub h
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · exact Or.inl (ih hsub skip)
    · exact Or.inr ⟨a, hsub ha, b, hsub hb, hab, z, hz, ih (Finset.insert_subset_insert z hsub) tail⟩

def liveChain (ops : α → α → Finset α) (goal : α) : List (α × α × α) → Finset α → Prop
  | [], s => s = {goal}
  | (a, b, z) :: gs, s =>
    a ∈ s ∧ b ∈ s ∧ a ≠ b ∧ z ∈ ops a b ∧ z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ liveChain ops goal gs (insert z rest)

theorem compress_chain {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) :
    ∃ gs : List (α × α × α), gs.length ≤ k ∧ ∃ s ⊆ available, liveChain ops goal gs s := by
  induction k generalizing available with
  | zero =>
    exact ⟨[], Nat.le_refl 0, {goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨gs, hlen, s, hs, hrun⟩ := ih skip
      exact ⟨gs, Nat.le_succ_of_le hlen, s, hs, hrun⟩
    · obtain ⟨gs, hlen, t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨gs, Nat.le_succ_of_le hlen, t, sub, hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨(a, b, z) :: gs, Nat.succ_le_succ hlen, s, hs,
          by simp [s], by simp [s], hab, hz, fun h => hzout (hs h), rest, rfl, ?_⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

theorem chain_to_build {ops : α → α → Finset α} {goal : α} {gs : List (α × α × α)} {s : Finset α}
    (h : liveChain ops goal gs s) : build ops goal gs.length s := by
  induction gs generalizing s with
  | nil => change s = {goal} at h; simp [build, h]
  | cons g gs ih =>
    rcases g with ⟨a, b, z⟩
    rcases h with ⟨ha, hb, hab, hz, _, rest, hs, tail⟩
    refine Or.inr ⟨a, ha, b, hb, hab, z, hz, build_mono ?_ (ih tail)⟩
    intro u hu
    rw [hs]
    rcases Finset.mem_insert.mp hu with rfl | hu
    · exact Finset.mem_insert_self u _
    · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu))

theorem chain_card {ops : α → α → Finset α} {goal : α} {gs : List (α × α × α)} {s : Finset α}
    (h : liveChain ops goal gs s) : s.card ≤ gs.length + 1 := by
  induction gs generalizing s with
  | nil => change s = {goal} at h; simp [h]
  | cons g gs ih =>
    rcases g with ⟨a, b, z⟩
    rcases h with ⟨_, _, _, _, hout, rest, rfl, tail⟩
    have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
    have htail := ih tail
    rw [Finset.card_insert_of_notMem hzrest] at htail
    have h₁ := Finset.card_insert_le a (insert b rest)
    have h₂ := Finset.card_insert_le b rest
    simp only [List.length_cons]
    omega

theorem chain_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {gs : List (α × α × α)} {s : Finset α} (h : liveChain ops goal gs s) : ∃ w ∈ s, D w := by
  induction gs generalizing s with
  | nil => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | cons g gs ih =>
    rcases g with ⟨a, b, z⟩
    rcases h with ⟨ha, hb, _, hz, _, rest, rfl, tail⟩
    obtain ⟨w, hw, hD⟩ := ih tail
    rcases Finset.mem_insert.mp hw with rfl | hw
    · rcases hops a b w hz hD with h | h
      · exact ⟨a, ha, h⟩
      · exact ⟨b, hb, h⟩
    · exact ⟨w, by simp [hw], hD⟩

theorem swap_two {ops : α → α → Finset α} {goal : α}
    {g₁ g₂ : α × α × α} {gs : List (α × α × α)} {s₀ : Finset α}
    (h : liveChain ops goal (g₁ :: g₂ :: gs) s₀)
    (h1 : g₂.1 ≠ g₁.2.2) (h2 : g₂.2.1 ≠ g₁.2.2) :
    liveChain ops goal (g₂ :: g₁ :: gs) s₀ ∨ build ops goal (gs.length + 1) s₀ := by
  rcases g₁ with ⟨a₁, b₁, z₁⟩
  rcases g₂ with ⟨a₂, b₂, z₂⟩
  rcases h with ⟨ha₁, hb₁, hab₁, hz₁, hout₁, rest₁, hs₀,
                 ha₂, hb₂, hab₂, hz₂, hout₂, rest₂, hs₁, tail⟩
  dsimp only at h1 h2
  have hz₁_r₂ : z₁ ∈ rest₂ := by
    have hm : z₁ ∈ insert a₂ (insert b₂ rest₂) := hs₁ ▸ Finset.mem_insert_self z₁ rest₁
    rcases Finset.mem_insert.mp hm with h | hm
    · exact absurd h.symm h1
    · rcases Finset.mem_insert.mp hm with h | hm
      · exact absurd h.symm h2
      · exact hm
  let core := rest₂.erase z₁
  have hcore_eq : insert z₁ core = rest₂ := Finset.insert_erase hz₁_r₂
  have hz₁_core : z₁ ∉ core := Finset.notMem_erase z₁ rest₂
  have hz₁_r₁ : z₁ ∉ rest₁ := fun hm => hout₁ (hs₀ ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
  have hr₁ : rest₁ = insert a₂ (insert b₂ core) := by
    ext u
    by_cases hu : u = z₁
    · subst hu
      simp [hz₁_r₁, h1.symm, h2.symm, hz₁_core]
    · have hmem : u ∈ insert z₁ rest₁ ↔ u ∈ insert a₂ (insert b₂ (insert z₁ core)) := by
        rw [hcore_eq, hs₁]
      simp [hu] at hmem
      simpa using hmem
  by_cases hz₂_s₀ : z₂ ∈ s₀
  · right
    refine Or.inr ⟨a₁, ha₁, b₁, hb₁, hab₁, z₁, hz₁, build_mono ?_ (chain_to_build tail)⟩
    intro u hu
    rcases Finset.mem_insert.mp hu with rfl | hu
    · exact Finset.mem_insert_of_mem hz₂_s₀
    · rw [← hcore_eq] at hu
      rcases Finset.mem_insert.mp hu with rfl | hu
      · exact Finset.mem_insert_self u s₀
      · rw [hs₀, hr₁]
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu))))
  · left
    have hs₀' : s₀ = insert a₂ (insert b₂ (insert a₁ (insert b₁ core))) := by
      rw [hs₀, hr₁]
      ext u; simp [or_left_comm]
    have ha₂_s₀ : a₂ ∈ s₀ := by rw [hs₀']; simp
    have hb₂_s₀ : b₂ ∈ s₀ := by rw [hs₀']; simp
    have hz₁_ne_z₂ : z₁ ≠ z₂ := fun heq => hout₂ (heq ▸ Finset.mem_insert_self z₁ rest₁)
    have hs₁' : insert z₂ (insert a₁ (insert b₁ core)) = insert a₁ (insert b₁ (insert z₂ core)) := by
      ext u; simp [or_left_comm]
    have hz₁_out' : z₁ ∉ insert z₂ (insert a₁ (insert b₁ core)) := by
      intro hm
      rcases Finset.mem_insert.mp hm with h | hm
      · exact hz₁_ne_z₂ h
      · exact hout₁ (hs₀' ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    refine ⟨ha₂_s₀, hb₂_s₀, hab₂, hz₂, hz₂_s₀, insert a₁ (insert b₁ core), hs₀',
            by rw [hs₁']; simp, by rw [hs₁']; simp, hab₁, hz₁, hz₁_out', insert z₂ core, hs₁', ?_⟩
    have hs₂' : insert z₁ (insert z₂ core) = insert z₂ rest₂ := by
      rw [← hcore_eq, Finset.insert_comm]
    simpa only [hs₂'] using tail

def chainOrd (key : α → ℕ) : ℕ → List (α × α × α) → Prop
  | _, [] => True
  | last, (a, b, z) :: gs =>
    (key a = last ∨ key b = last ∨ last ≤ key z) ∧ chainOrd key (key z) gs

def invCount (key : α → ℕ) : List (α × α × α) → ℕ
  | [] => 0
  | g :: gs => (gs.filter (fun h => decide (key h.2.2 < key g.2.2))).length + invCount key gs

theorem invCount_swap_lt (key : α → ℕ) (pre suf : List (α × α × α)) (g₁ g₂ : α × α × α)
    (hlt : key g₂.2.2 < key g₁.2.2) :
    invCount key (pre ++ g₂ :: g₁ :: suf) < invCount key (pre ++ g₁ :: g₂ :: suf) := by
  induction pre with
  | nil =>
    simp only [List.nil_append, invCount, List.filter_cons]
    have h1 : decide (key g₂.2.2 < key g₁.2.2) = true := decide_eq_true hlt
    have h2 : decide (key g₁.2.2 < key g₂.2.2) = false := decide_eq_false (by omega)
    simp only [h1, h2, ↓reduceIte, Bool.false_eq_true, List.length_cons]
    omega
  | cons x xs ih =>
    simp only [List.cons_append, invCount]
    have hperm : (xs ++ g₂ :: g₁ :: suf).Perm (xs ++ g₁ :: g₂ :: suf) :=
      List.Perm.append_left xs (List.Perm.swap g₁ g₂ suf)
    have hlen : ((xs ++ g₂ :: g₁ :: suf).filter (fun h => decide (key h.2.2 < key x.2.2))).length =
                ((xs ++ g₁ :: g₂ :: suf).filter (fun h => decide (key h.2.2 < key x.2.2))).length :=
      (hperm.filter _).length_eq
    omega

theorem swap_in_chain {ops : α → α → Finset α} {goal : α}
    (pre : List (α × α × α)) (g₁ g₂ : α × α × α) (suf : List (α × α × α)) {s : Finset α}
    (h : liveChain ops goal (pre ++ g₁ :: g₂ :: suf) s)
    (h1 : g₂.1 ≠ g₁.2.2) (h2 : g₂.2.1 ≠ g₁.2.2) :
    liveChain ops goal (pre ++ g₂ :: g₁ :: suf) s ∨ build ops goal (pre.length + suf.length + 1) s := by
  induction pre generalizing s with
  | nil =>
    simpa using swap_two h h1 h2
  | cons g pre ih =>
    rcases g with ⟨a, b, z⟩
    rcases h with ⟨ha, hb, hab, hz, hout, rest, hs, tail⟩
    rcases ih tail with hswap | hshort
    · exact Or.inl ⟨ha, hb, hab, hz, hout, rest, hs, hswap⟩
    · right
      have hlen : ((a, b, z) :: pre).length + suf.length + 1 = (pre.length + suf.length + 1) + 1 := by
        simp; omega
      rw [hlen]
      refine Or.inr ⟨a, ha, b, hb, hab, z, hz, build_mono ?_ hshort⟩
      intro u hu
      rw [hs]
      rcases Finset.mem_insert.mp hu with rfl | hu
      · exact Finset.mem_insert_self u _
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu))

omit [DecidableEq α] in
theorem find_violation (key : α → ℕ) (last : ℕ) (gs : List (α × α × α))
    (hstart : ∀ g gs', gs = g :: gs' → key g.1 = last ∨ key g.2.1 = last ∨ last ≤ key g.2.2) :
    chainOrd key last gs ∨
    ∃ pre g₁ g₂ suf, gs = pre ++ g₁ :: g₂ :: suf ∧
      key g₂.1 ≠ key g₁.2.2 ∧ key g₂.2.1 ≠ key g₁.2.2 ∧ key g₂.2.2 < key g₁.2.2 := by
  induction gs generalizing last with
  | nil => exact Or.inl trivial
  | cons g₁ rest ih =>
    have hg₁ := hstart g₁ rest rfl
    cases rest with
    | nil => exact Or.inl ⟨hg₁, trivial⟩
    | cons g₂ suf =>
      by_cases hok : key g₂.1 = key g₁.2.2 ∨ key g₂.2.1 = key g₁.2.2 ∨ key g₁.2.2 ≤ key g₂.2.2
      · rcases ih (key g₁.2.2) (fun g gs' heq => by cases heq; exact hok) with hord | ⟨pre, a, b, s', heq, h1, h2, hlt⟩
        · exact Or.inl ⟨hg₁, hord⟩
        · exact Or.inr ⟨g₁ :: pre, a, b, s', by simp [heq], h1, h2, hlt⟩
      · push_neg at hok
        exact Or.inr ⟨[], g₁, g₂, suf, rfl, hok.1, hok.2.1, hok.2.2⟩

theorem normalize_aux {ops : α → α → Finset α} {goal : α} (key : α → ℕ) (av : Finset α) :
    ∀ (m inv : ℕ) (gs : List (α × α × α)) (s : Finset α),
      gs.length ≤ m → invCount key gs ≤ inv → s ⊆ av → liveChain ops goal gs s →
      ∃ gs' : List (α × α × α), gs'.length ≤ m ∧ chainOrd key 0 gs' ∧
        ∃ s' ⊆ av, liveChain ops goal gs' s' := by
  intro m
  induction m with
  | zero =>
    intro inv gs s hlen _ hsub hrun
    have hnil : gs = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hlen)
    subst hnil
    exact ⟨[], Nat.le_refl 0, trivial, s, hsub, hrun⟩
  | succ m ihm =>
    intro inv
    induction inv with
    | zero =>
      intro gs s hlen hinv hsub hrun
      rcases find_violation key 0 gs (fun _ _ _ => Or.inr (Or.inr (Nat.zero_le _))) with
        hord | ⟨pre, g₁, g₂, suf, rfl, h1, h2, hlt⟩
      · exact ⟨gs, hlen, hord, s, hsub, hrun⟩
      · exfalso
        have hpos : 0 < invCount key (pre ++ g₁ :: g₂ :: suf) :=
          Nat.lt_of_le_of_lt (Nat.zero_le _) (invCount_swap_lt key pre suf g₁ g₂ hlt)
        omega
    | succ inv ihi =>
      intro gs s hlen hinv hsub hrun
      rcases find_violation key 0 gs (fun _ _ _ => Or.inr (Or.inr (Nat.zero_le _))) with
        hord | ⟨pre, g₁, g₂, suf, rfl, h1, h2, hlt⟩
      · exact ⟨gs, hlen, hord, s, hsub, hrun⟩
      · have hne1 : g₂.1 ≠ g₁.2.2 := fun heq => h1 (congrArg key heq)
        have hne2 : g₂.2.1 ≠ g₁.2.2 := fun heq => h2 (congrArg key heq)
        rcases swap_in_chain pre g₁ g₂ suf hrun hne1 hne2 with hswap | hshort
        · have hlt' := invCount_swap_lt key pre suf g₁ g₂ hlt
          have hlen' : (pre ++ g₂ :: g₁ :: suf).length ≤ m + 1 := by
            simp only [List.length_append, List.length_cons] at hlen ⊢; omega
          exact ihi (pre ++ g₂ :: g₁ :: suf) s hlen' (by omega) hsub hswap
        · have hbm : build ops goal m av := by
            have hle : pre.length + suf.length + 1 ≤ m := by
              simp only [List.length_append, List.length_cons] at hlen; omega
            have hb1 : build ops goal (pre.length + suf.length + 1) av := build_mono hsub hshort
            clear hshort hsub hrun hlen ihm ihi hinv h1 h2 hlt hne1 hne2
            induction hle with
            | refl => exact hb1
            | step _ ih => exact Or.inl ih
          obtain ⟨gs', hlen', s', hsub', hrun'⟩ := compress_chain hbm
          obtain ⟨gs'', hlen'', hord'', s'', hsub'', hrun''⟩ :=
            ihm (invCount key gs') gs' s' hlen' (Nat.le_refl _) hsub' hrun'
          exact ⟨gs'', Nat.le_succ_of_le hlen'', hord'', s'', hsub'', hrun''⟩

theorem normalize_build {ops : α → α → Finset α} {goal : α} (key : α → ℕ)
    {k : ℕ} {av : Finset α} (h : build ops goal k av) :
    ∃ gs : List (α × α × α), gs.length ≤ k ∧ chainOrd key 0 gs ∧
      ∃ s ⊆ av, liveChain ops goal gs s := by
  obtain ⟨gs, hlen, s, hsub, hrun⟩ := compress_chain h
  exact normalize_aux key av k (invCount key gs) gs s hlen (Nat.le_refl _) hsub hrun

end Live

abbrev W := BitVec 126

def ops (x y : W) : List W := [x &&& y, x ||| y].filter (fun z => z != 0 && z != BitVec.allOnes 126)

def sep (x : W) : BitVec 63 := ((x >>> 63) &&& ~~~x).setWidth 63

def cuts (ws : List W) : BitVec 63 := ws.foldr (fun w v => sep w ||| v) 0

def goal : W := (-1 : BitVec 63) ++ (0 : BitVec 63)

def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

def rawInputs : List W :=
  [0xfffff8102040810204081, 0x1fffff000000204081020408102, 0x3ffffe00000000000408102040810204, 0x78f1e3c78f1e3c78, 0xfe0007f0003f8810204081020408, 0x7f0003f80000001122448912244891, 0x3f80000000001fc02244891224489122, 0x1fc000fe0004489122448912244]

def inputs : List W := rawInputs

theorem pick_one {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

theorem pick_two {α : Type} {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b, r), hm, rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r, .inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_,
          (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))

abbrev basicOps (a b : W) : Finset W := (ops a b).toFinset

def differs (i : Fin 63) (w : W) : Prop :=
  w.getLsbD (63 + i.val) = true ∧ w.getLsbD i.val = false

theorem ops_differs (i : Fin 63) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_filter, List.mem_cons, List.not_mem_nil, or_false] at hz
  unfold differs at hd ⊢
  rcases hz.1 with rfl | rfl <;> revert hd <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or] <;>
    cases a.getLsbD (63 + i.val) <;> cases a.getLsbD i.val <;>
    cases b.getLsbD (63 + i.val) <;> cases b.getLsbD i.val <;> simp

theorem goal_differs : ∀ i : Fin 63, differs i goal := by
  unfold differs
  decide

theorem cuts_spec (ws : List W) (i : Fin 63) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have hi : i.val < 126 := by omega
    simp [sep, i.isLt, differs, hi, Nat.add_comm]

theorem cuts_full {gs : List (W × W × W)} {ws : List W} (h : liveChain basicOps goal gs ws.toFinset) :
    cuts ws = -1 := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := chain_separates (differs ⟨j, hj⟩) (goal_differs ⟨j, hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 63)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp [basicOps, ops, BitVec.and_comm, BitVec.or_comm]

def keepChoices (a b : W) (r : List W) : List (List W) := [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept {ws r : List W} {a b : W} {needed : Finset W}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

theorem singleton_list {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def possible (w : List W) (z : W) : Bool :=
  z == 0 || z == BitVec.allOnes 126 || w.any (fun u => z == u ||
    w.any (fun v => z == (u &&& v) || z == (u ||| v)))

private def bit (k : Fin 126) (z : W) : Bool := z[k.val]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 126) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

private theorem read_wire (w : List W) (i : ℕ) : w.getD i 0 = 0 ∨ w.getD i 0 ∈ w := by
  by_cases h : i < w.length
  · exact Or.inr (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_gt h)]

private theorem atom {ws : List W} {x : W} (hx : x = 0 ∨ x ∈ ws) : possible ws x := by
  rcases hx with rfl | hx
  · simp [possible]
  · simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    exact .inr ⟨x, hx, .inl rfl⟩

private theorem pair {ws : List W} {x y : W} (hx : x = 0 ∨ x ∈ ws) (hy : y = 0 ∨ y ∈ ws) :
    possible ws (x &&& y) ∧ possible ws (x ||| y) := by
  rcases hx with rfl | hx
  · simpa [possible] using atom hy
  rcases hy with rfl | hy
  · simpa [possible] using atom (.inr hx)
  · simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    constructor
    · exact .inr ⟨x, hx, .inr ⟨y, hy, .inl rfl⟩⟩
    · exact .inr ⟨x, hx, .inr ⟨y, hy, .inr rfl⟩⟩

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def legal (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

set_option maxRecDepth 2000 in
private theorem gate_table (w ws : List W) (hw : w ⊆ ws) (g : Gate) (hg : legal g) :
    ∃ z, possible ws z ∧ ∀ k, step (w.map (bit k)) g = (w ++ [z]).map (bit k) := by
  have mem (i : ℕ) : w.getD i 0 = 0 ∨ w.getD i 0 ∈ ws :=
    (read_wire w i).imp_right (fun h => hw h)
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  change op = .and ∨ op = .or at hop
  change args.length ≤ 2 at hlen
  cases args with
  | nil =>
    rcases hop with rfl | rfl
    · exact ⟨BitVec.allOnes 126, by simp [possible], by simp [step, GateOp.eval, bit]; decide⟩
    · exact ⟨0, by simp [possible], by simp [step, GateOp.eval, bit]⟩
  | cons i tail =>
    cases tail with
    | nil =>
      rcases hop with rfl | rfl
      · exact ⟨_, atom (mem i),
          by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval]⟩
      · exact ⟨_, atom (mem i),
          by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval]⟩
    | cons j tail =>
      cases tail with
      | cons => simp at hlen
      | nil =>
        rcases hop with rfl | rfl
        · exact ⟨_, (pair (mem i) (mem j)).1,
            by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit]⟩
        · exact ⟨_, (pair (mem i) (mem j)).2,
            by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit]⟩

def represents (available : Finset W) (w : List W) : Prop :=
  ∀ u ∈ w, u = 0 ∨ u = BitVec.allOnes 126 ∨ u ∈ available

theorem classify {available : Finset W} {ws : List W} (hw : represents available ws)
    {z : W} (hz : possible ws z) :
    z = 0 ∨ z = BitVec.allOnes 126 ∨ z ∈ available ∨
      ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧ z ∈ basicOps a b := by
  have lift {t : W} (h : t = 0 ∨ t = BitVec.allOnes 126 ∨ t ∈ available) :
      t = 0 ∨ t = BitVec.allOnes 126 ∨ t ∈ available ∨
        ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧ t ∈ basicOps a b :=
    h.imp_right (Or.imp_right Or.inl)
  simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at hz
  rcases hz with ((h | h) | ⟨x, hx, h | ⟨y, hy, h | h⟩⟩)
  · exact .inl h
  · exact .inr (.inl h)
  · subst z; exact lift (hw _ hx)
  · subst z
    rcases hw _ hx with rfl | rfl | hu
    · left; simp
    · rw [BitVec.allOnes_and]; exact lift (hw _ hy)
    rcases hw _ hy with rfl | rfl | hv
    · left; simp
    · rw [BitVec.and_allOnes]; exact .inr (.inr (.inl hu))
    by_cases h : x = y
    · subst h; rw [BitVec.and_self]; exact .inr (.inr (.inl hu))
    · by_cases h0 : x &&& y = 0
      · exact .inl h0
      · by_cases h1 : x &&& y = BitVec.allOnes 126
        · exact .inr (.inl h1)
        · exact .inr (.inr (.inr ⟨x, hu, y, hv, h, by
            simp only [basicOps, ops, List.mem_toFinset, List.mem_filter, List.mem_cons,
              List.not_mem_nil, or_false, Bool.and_eq_true, bne_iff_ne]
            exact ⟨by simp, h0, h1⟩⟩))
  · subst z
    rcases hw _ hx with rfl | rfl | hu
    · rw [show (0 : W) ||| y = y by ext i hi; simp]; exact lift (hw _ hy)
    · right; left; exact BitVec.allOnes_or
    rcases hw _ hy with rfl | rfl | hv
    · rw [show x ||| (0 : W) = x by ext i hi; simp]; exact .inr (.inr (.inl hu))
    · right; left; exact BitVec.or_allOnes
    by_cases h : x = y
    · subst h; rw [BitVec.or_self]; exact .inr (.inr (.inl hu))
    · by_cases h0 : x ||| y = 0
      · exact .inl h0
      · by_cases h1 : x ||| y = BitVec.allOnes 126
        · exact .inr (.inl h1)
        · exact .inr (.inr (.inr ⟨x, hu, y, hv, h, by
            simp only [basicOps, ops, List.mem_toFinset, List.mem_filter, List.mem_cons,
              List.not_mem_nil, or_false, Bool.and_eq_true, bne_iff_ne]
            exact ⟨by simp, h0, h1⟩⟩))

private theorem compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W) (av : Finset W) (hw : represents av w)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k goal) :
    build basicOps goal gs.length av := by
  induction gs generalizing w av with
  | nil =>
    have hval : w.getD out 0 = goal := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i, hi⟩
    have hr := read_wire w out
    rw [hval] at hr
    rcases hr with hz | hm
    · exact False.elim ((by decide : goal ≠ (0 : W)) hz)
    · rcases hw _ hm with h | h | h
      · exact False.elim ((by decide : goal ≠ (0 : W)) h)
      · exact False.elim ((by decide : goal ≠ BitVec.allOnes 126) h)
      · exact h
  | cons g gs ih =>
    obtain ⟨z, hz, hstep⟩ := gate_table w w (fun _ h => h) g (hg g (by simp))
    have fn := ih (fun g' h => hg g' (by simp [h])) (w ++ [z])
    have he' : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k goal := by
      intro k; simpa only [List.foldl_cons, hstep] using he k
    have appendOK (h : z = 0 ∨ z = BitVec.allOnes 126 ∨ z ∈ av) : represents av (w ++ [z]) := by
      intro u hu
      rcases List.mem_append.mp hu with old | fresh
      · exact hw _ old
      · have eq : u = z := List.mem_singleton.mp fresh
        exact eq ▸ h
    rcases classify hw hz with h | h | h | ⟨a, ha, b, hb, hab, hop⟩
    · exact Or.inl (fn av (appendOK (.inl h)) he')
    · exact Or.inl (fn av (appendOK (.inr (.inl h))) he')
    · exact Or.inl (fn av (appendOK (.inr (.inr h))) he')
    · refine Or.inr ⟨a, ha, b, hb, hab, z, hop, fn (insert z av) ?_ he'⟩
      intro u hu
      rcases List.mem_append.mp hu with hu | hu
      · exact (hw _ hu).imp_right (Or.imp_right (Finset.mem_insert_of_mem ·))
      · simp_all

def dispatch (extra last : ℕ) (next : ℕ → ℕ → List W → Bool) (a b : W) (r : List W) : Bool :=
  let base := cuts r
  (ops a b).any fun w =>
    if w == a || w == b || r.elem w || (a.toNat != last && b.toNat != last && w.toNat < last) then false
    else
      let v := sep w ||| base
      let wn := w.toNat
      ((v == -1) && next extra wn (w :: r)) ||
      ((extra != 0) && (((v ||| sep a == -1) && next (extra - 1) wn (w :: a :: r)) ||
                         ((v ||| sep b == -1) && next (extra - 1) wn (w :: b :: r)))) ||
      ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && next (extra - 2) wn (w :: a :: b :: r))

def optimized : ℕ → ℕ → ℕ → List W → Bool
  | 0, _, _, ws => ws == [goal]
  | 1, _, _, [a] => a == goal
  | 1, _, _, [a, b] => (a &&& b == goal) || (a ||| b == goal)
  | 1, _, _, _ => false
  | 2, _, _, [a] => a == goal
  | 2, _, _, [a, b] => a == goal || b == goal || (a &&& b == goal) || (a ||| b == goal)
  | 2, _, _, [a, b, c] =>
    (a &&& b &&& c == goal) || (a ||| b ||| c == goal) ||
    ((a &&& b) ||| c == goal) || ((a ||| b) &&& c == goal) ||
    ((a &&& c) ||| b == goal) || ((a ||| c) &&& b == goal) ||
    ((b &&& c) ||| a == goal) || ((b ||| c) &&& a == goal)
  | 2, _, _, _ => false
  | k + 3, extra, last, ws => ws == [goal] ||
    (pairs ws).any (fun (a, b, r) => dispatch extra last (optimized (k + 2)) a b r)

theorem dispatch_complete {k extra last : ℕ} {a b z : W} {r kept : List W}
    (next : ℕ → ℕ → List W → Bool)
    (hz : z ∈ basicOps a b) (hna : z ≠ a) (hnb : z ≠ b) (hnr : z ∉ r)
    (hord : a.toNat = last ∨ b.toNat = last ∨ last ≤ z.toNat)
    (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts (z :: kept) = -1) (ht : next (k - kept.length) z.toNat (z :: kept) = true) :
    dispatch extra last next a b r = true := by
  apply List.any_eq_true.mpr
  refine ⟨z, List.mem_toFinset.mp hz, ?_⟩
  have hordb : (a.toNat != last && b.toNat != last && decide (z.toNat < last)) = false := by
    rcases hord with h | h | h
    · simp [h]
    · simp [h]
    · have : ¬ (z.toNat < last) := by omega
      simp [this]
  have hcond : (z == a || z == b || r.elem z || (a.toNat != last && b.toNat != last && decide (z.toNat < last))) = false := by
    simp [hna, hnb, hnr, hordb]
  rw [hcond]
  simp only [Bool.false_eq_true, ↓reduceIte]
  simp [keepChoices] at hk
  rcases hk with rfl | rfl | rfl | rfl <;>
    simp only [cuts, List.foldr_cons] at hc ⊢ <;>
    (try simp only [List.length_cons] at *) <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne]
  · left; left; exact ⟨hc, by convert ht using 2; omega⟩
  · left; right; exact ⟨by omega, .inl ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · left; right; exact ⟨by omega, .inr ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · right; exact ⟨⟨by omega, by convert hc using 1; ac_rfl⟩, by convert ht using 2; omega⟩

theorem chain_one_pair {a b : W} {gs : List (W × W × W)}
    (h : liveChain basicOps goal gs {a, b}) (hab : a ≠ b) (hlen : gs.length ≤ 1) :
    goal ∈ basicOps a b := by
  cases gs with
  | nil =>
    change ({a, b} : Finset W) = {goal} at h
    have hc := congrArg Finset.card h
    rw [Finset.card_pair hab, Finset.card_singleton] at hc
    omega
  | cons g gs' =>
    cases gs' with
    | cons => simp at hlen
    | nil =>
      rcases g with ⟨x, y, z⟩
      rcases h with ⟨hx, hy, hxy, hz, hout, rest, hs, tail⟩
      change insert z rest = {goal} at tail
      have hzg : z = goal := Finset.mem_singleton.mp (tail ▸ Finset.mem_insert_self z rest)
      have hxy_ab : (x = a ∧ y = b) ∨ (x = b ∧ y = a) := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
        rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
        · exact absurd rfl hxy
        · exact .inl ⟨rfl, rfl⟩
        · exact .inr ⟨rfl, rfl⟩
        · exact absurd rfl hxy
      rcases hxy_ab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hzg ▸ hz
      · rw [ops_swap]; exact hzg ▸ hz

theorem optimized_one {ws : List W} {extra last : ℕ} {gs : List (W × W × W)}
    (hn : ws.Nodup) (hlen : gs.length ≤ 1) (h : liveChain basicOps goal gs ws.toFinset) :
    optimized 1 extra last ws = true := by
  have hc := chain_card h
  rw [List.toFinset_card_of_nodup hn] at hc
  match ws, hn, hc, h with
  | [], _, _, h =>
    cases gs with
    | nil => change ∅ = {goal} at h; simp at h
    | cons g _ => rcases g with ⟨a, _, _⟩; exact absurd h.1 (by simp)
  | [a], hn, _, h =>
    cases gs with
    | nil =>
      have : a = goal := by
        have hm : a ∈ ({goal} : Finset W) := h ▸ Finset.mem_singleton_self a
        exact Finset.mem_singleton.mp hm
      simp [optimized, this]
    | cons g _ =>
      rcases g with ⟨x, y, _⟩
      rcases h with ⟨hx, hy, hxy, _⟩
      simp only [List.toFinset_cons, List.toFinset_nil, insert_empty_eq, Finset.mem_singleton] at hx hy
      exact absurd (hx.trans hy.symm) hxy
  | [a, b], hn, _, h =>
    have hab : a ≠ b := (List.nodup_cons.mp hn).1 ∘ List.mem_singleton.mpr
    have hset : ([a, b] : List W).toFinset = {a, b} := by simp
    rw [hset] at h
    have hzg := chain_one_pair h hab hlen
    simp only [basicOps, ops, List.mem_toFinset, List.mem_filter, List.mem_cons, List.not_mem_nil, or_false] at hzg
    simp only [optimized, Bool.or_eq_true, beq_iff_eq]
    exact hzg.1.imp Eq.symm Eq.symm
  | _ :: _ :: _ :: _, _, hc, _ => simp at hc; omega

theorem abs_ops {a b z : W} (hz : z ∈ basicOps a b) (w : W) (hw : w ∈ basicOps z a ∨ w ∈ basicOps z b) :
    w = a ∨ w = b ∨ w = (a &&& b) ∨ w = (a ||| b) := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_filter, List.mem_cons, List.not_mem_nil, or_false] at hz hw
  rcases hz.1 with rfl | rfl <;> rcases hw with (⟨rfl | rfl, _⟩) | (⟨rfl | rfl, _⟩)
  · right; right; left; ext i hi; simp; try (cases a[i] <;> cases b[i] <;> simp)
  · left; ext i hi; simp; try (cases a[i] <;> cases b[i] <;> simp)
  · right; right; left; ext i hi; simp; try (cases a[i] <;> cases b[i] <;> simp)
  · right; left; ext i hi; simp; try (cases a[i] <;> cases b[i] <;> simp)
  · left; ext i hi; simp; try (cases a[i] <;> cases b[i] <;> simp)
  · right; right; right; ext i hi; simp; try (cases a[i] <;> cases b[i] <;> simp)
  · right; left; ext i hi; simp; try (cases a[i] <;> cases b[i] <;> simp)
  · right; right; right; ext i hi; simp; try (cases a[i] <;> cases b[i] <;> simp)

theorem optimized_two {ws : List W} {extra last : ℕ} {gs : List (W × W × W)}
    (hn : ws.Nodup) (hlen : gs.length ≤ 2) (h : liveChain basicOps goal gs ws.toFinset) :
    optimized 2 extra last ws = true := by
  have hc := chain_card h
  rw [List.toFinset_card_of_nodup hn] at hc
  match ws, hn, hc, h with
  | [], _, _, h =>
    cases gs with
    | nil => change ∅ = {goal} at h; simp at h
    | cons g _ => rcases g with ⟨a, _, _⟩; exact absurd h.1 (by simp)
  | [a], hn, _, h =>
    cases gs with
    | nil =>
      have : a = goal := Finset.mem_singleton.mp (h ▸ Finset.mem_singleton_self a)
      simp [optimized, this]
    | cons g _ =>
      rcases g with ⟨x, y, _⟩
      rcases h with ⟨hx, hy, hxy, _⟩
      simp only [List.toFinset_cons, List.toFinset_nil, insert_empty_eq, Finset.mem_singleton] at hx hy
      exact absurd (hx.trans hy.symm) hxy
  | [a, b], hn, _, h =>
    have hab : a ≠ b := (List.nodup_cons.mp hn).1 ∘ List.mem_singleton.mpr
    have hset : ([a, b] : List W).toFinset = {a, b} := by simp
    rw [hset] at h
    cases gs with
    | nil =>
      change ({a, b} : Finset W) = {goal} at h
      have hcard := congrArg Finset.card h
      rw [Finset.card_pair hab, Finset.card_singleton] at hcard
      omega
    | cons g gs' =>
      rcases g with ⟨x, y, z⟩
      rcases h with ⟨hx, hy, hxy, hz, hout, rest, hs, tail⟩
      have hxy_ab : (x = a ∧ y = b) ∨ (x = b ∧ y = a) := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
        rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
        · exact absurd rfl hxy
        · exact .inl ⟨rfl, rfl⟩
        · exact .inr ⟨rfl, rfl⟩
        · exact absurd rfl hxy
      have hz_ab : z ∈ basicOps a b := by
        rcases hxy_ab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hz
        · rw [ops_swap]; exact hz
      cases gs' with
      | nil =>
        change insert z rest = {goal} at tail
        have hzg : z = goal := Finset.mem_singleton.mp (tail ▸ Finset.mem_insert_self z rest)
        have hmem : goal ∈ basicOps a b := hzg ▸ hz_ab
        simp only [basicOps, ops, List.mem_toFinset, List.mem_filter, List.mem_cons, List.not_mem_nil, or_false] at hmem
        simp only [optimized, Bool.or_eq_true, beq_iff_eq]
        rcases hmem.1 with h1 | h2
        · left; right; exact h1.symm
        · right; exact h2.symm
      | cons g2 gs'' =>
        cases gs'' with
        | cons => simp at hlen
        | nil =>
          have hsub : rest ⊆ {a, b} := by
            intro u hu; rw [hs]; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu)
          have hcard2 := chain_card tail
          have hzrest : z ∉ rest := fun hm => hout (hsub hm)
          rw [Finset.card_insert_of_notMem hzrest] at hcard2
          simp only [List.length_singleton] at hcard2
          have hrest1 : rest.card = 1 := by
            by_cases he : rest = ∅
            · subst he
              rcases g2 with ⟨u, v, _⟩
              rcases tail with ⟨hu, hv, huv, _⟩
              simp at hu hv
              exact absurd (hu.trans hv.symm) huv
            · have := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr he); omega
          obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hrest1
          rw [hw] at tail hsub
          have hw_ab : w = a ∨ w = b := by
            have := hsub (Finset.mem_singleton_self w); simpa using this
          have hzw : z ≠ w := fun heq => hout (heq ▸ hsub (Finset.mem_singleton_self w))
          have hzg := chain_one_pair (by simpa [insert_empty_eq] using tail) hzw (by simp)
          have hres := abs_ops hz_ab goal (hw_ab.elim (fun h => .inl (h ▸ hzg)) (fun h => .inr (h ▸ hzg)))
          simp only [optimized, Bool.or_eq_true, beq_iff_eq]
          rcases hres with h1 | h2 | h3 | h4
          · left; left; left; exact h1.symm
          · left; left; right; exact h2.symm
          · left; right; exact h3.symm
          · right; exact h4.symm
  | [a, b, c], hn, _, h =>
    have hnd1 := List.nodup_cons.mp hn
    have hnd2 := List.nodup_cons.mp hnd1.2
    have hab : a ≠ b := fun heq => hnd1.1 (by simp [heq])
    have hac : a ≠ c := fun heq => hnd1.1 (by simp [heq])
    have hbc : b ≠ c := fun heq => hnd2.1 (by simp [heq])
    have hlen2 : gs.length = 2 := by
      have hc' := chain_card h
      rw [List.toFinset_card_of_nodup hn] at hc'
      simp at hc'; omega
    match gs, hlen2, h with
    | [(x, y, z), g2], _, h =>
      rcases h with ⟨hx, hy, hxy, hz, hout, rest, hs, tail⟩
      have hcard2 := chain_card tail
      have hzrest : z ∉ rest := fun hm => hout (hs ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
      rw [Finset.card_insert_of_notMem hzrest] at hcard2
      simp only [List.length_singleton] at hcard2
      have hset3 : ([a, b, c] : List W).toFinset = {a, b, c} := by simp
      rw [hset3] at hs hx hy hout
      have hcard3 : ({a, b, c} : Finset W).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp [hab, hac]), Finset.card_pair hbc]
      have hrest1 : rest.card = 1 := by
        have h1 := Finset.card_insert_le x (insert y rest)
        have h2 := Finset.card_insert_le y rest
        rw [← hs, hcard3] at h1
        omega
      obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hrest1
      rw [hw] at hs tail
      have hzw : z ≠ w := fun heq => hout (hs ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (heq ▸ Finset.mem_singleton_self w)))
      have hzg := chain_one_pair (by simpa [insert_empty_eq] using tail) hzw (by simp)
      have htri : (z ∈ basicOps a b ∧ w = c) ∨ (z ∈ basicOps a c ∧ w = b) ∨ (z ∈ basicOps b c ∧ w = a) := by
        have hwx : w ≠ x := by
          intro heq; subst heq
          have : (insert w (insert y ({w} : Finset W))).card ≤ 2 := by
            rw [Finset.insert_comm, show insert w ({w} : Finset W) = {w} by simp]
            exact Finset.card_insert_le y {w}
          rw [← hs, hcard3] at this; omega
        have hwy : w ≠ y := by
          intro heq; subst heq
          have : (insert x (insert w ({w} : Finset W))).card ≤ 2 := by
            rw [show insert w ({w} : Finset W) = {w} by simp]
            exact Finset.card_insert_le x {w}
          rw [← hs, hcard3] at this; omega
        have hwm : w ∈ ({a, b, c} : Finset W) := hs ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self w))
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy hwm
        rcases hwm with rfl | rfl | rfl
        · rcases hx with rfl | rfl | rfl
          · exact absurd rfl hwx
          · rcases hy with rfl | rfl | rfl
            · exact absurd rfl hwy
            · exact absurd rfl hxy
            · exact .inr (.inr ⟨hz, rfl⟩)
          · rcases hy with rfl | rfl | rfl
            · exact absurd rfl hwy
            · exact .inr (.inr ⟨ops_swap _ _ ▸ hz, rfl⟩)
            · exact absurd rfl hxy
        · rcases hx with rfl | rfl | rfl
          · rcases hy with rfl | rfl | rfl
            · exact absurd rfl hxy
            · exact absurd rfl hwy
            · exact .inr (.inl ⟨hz, rfl⟩)
          · exact absurd rfl hwx
          · rcases hy with rfl | rfl | rfl
            · exact .inr (.inl ⟨ops_swap _ _ ▸ hz, rfl⟩)
            · exact absurd rfl hwy
            · exact absurd rfl hxy
        · rcases hx with rfl | rfl | rfl
          · rcases hy with rfl | rfl | rfl
            · exact absurd rfl hxy
            · exact .inl ⟨hz, rfl⟩
            · exact absurd rfl hwy
          · rcases hy with rfl | rfl | rfl
            · exact .inl ⟨ops_swap _ _ ▸ hz, rfl⟩
            · exact absurd rfl hxy
            · exact absurd rfl hwy
          · exact absurd rfl hwx
      simp only [basicOps, ops, List.mem_toFinset, List.mem_filter, List.mem_cons, List.not_mem_nil, or_false] at htri hzg
      simp only [optimized, Bool.or_eq_true, beq_iff_eq]
      rcases htri with ⟨⟨hz1 | hz1, _⟩, rfl⟩ | ⟨⟨hz1 | hz1, _⟩, rfl⟩ | ⟨⟨hz1 | hz1, _⟩, rfl⟩ <;>
        (subst hz1; rcases hzg.1 with hzg | hzg)
      · exact .inl (.inl (.inl (.inl (.inl (.inl (.inl hzg.symm))))))
      · exact .inl (.inl (.inl (.inl (.inl (.inr hzg.symm)))))
      · exact .inl (.inl (.inl (.inl (.inr hzg.symm))))
      · exact .inl (.inl (.inl (.inl (.inl (.inl (.inr hzg.symm))))))
      · exact .inl (.inl (.inl (.inl (.inl (.inl (.inl (by rw [hzg]; ac_rfl)))))))
      · exact .inl (.inl (.inl (.inr hzg.symm)))
      · exact .inl (.inl (.inr hzg.symm))
      · exact .inl (.inl (.inl (.inl (.inl (.inl (.inr (by rw [hzg]; ac_rfl)))))))
      · exact .inl (.inl (.inl (.inl (.inl (.inl (.inl (by rw [hzg]; ac_rfl)))))))
      · exact .inl (.inr hzg.symm)
      · exact .inr hzg.symm
      · exact .inl (.inl (.inl (.inl (.inl (.inl (.inr (by rw [hzg]; ac_rfl)))))))
  | _ :: _ :: _ :: _ :: _, _, hc, _ => simp at hc; omega

theorem optimized_complete (n : ℕ) (ws : List W) (extra last : ℕ) (gs : List (W × W × W))
    (hn : ws.Nodup) (hlen : gs.length ≤ n)
    (room : extra + ws.length = n + 1)
    (hord : chainOrd BitVec.toNat last gs)
    (h : liveChain basicOps goal gs ws.toFinset) :
    optimized n extra last ws = true := by
  induction n generalizing ws extra last gs with
  | zero =>
    have hnil : gs = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hlen)
    subst hnil
    simp [optimized, singleton_list hn h]
  | succ k ih =>
    cases k with
    | zero => exact optimized_one hn hlen h
    | succ m =>
      cases m with
      | zero => exact optimized_two hn hlen h
      | succ p =>
        cases gs with
        | nil => simp [optimized, singleton_list hn h]
        | cons g gs' =>
          rcases g with ⟨a, b, z⟩
          rcases h with ⟨ha, hb, hab, hz, hout, needed, hs, tail⟩
          rcases hord with ⟨hg_ord, hgs_ord⟩
          obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
          have go {a b : W} (perm : ws.Perm (a :: b :: r))
              (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b)
              (hord' : a.toNat = last ∨ b.toNat = last ∨ last ≤ z.toNat) :
              dispatch extra last (optimized (p + 2)) a b r = true := by
            obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
            have hzws : z ∉ a :: b :: r := fun hu => hout (List.mem_toFinset.mpr (perm.mem_iff.mpr hu))
            have hna : z ≠ a := fun h => hzws (h ▸ List.mem_cons_self)
            have hnb : z ≠ b := fun h => hzws (List.mem_cons_of_mem _ (h ▸ List.mem_cons_self))
            have hnr : z ∉ r := fun h => hzws (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))
            have hznew : z ∉ kept := by
              intro hu
              apply hout
              rw [hset]
              exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
            have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
            have hl : liveChain basicOps goal gs' (z :: kept).toFinset := by
              simpa [hfin] using tail
            have hlen' : gs'.length ≤ p + 2 := by simp at hlen; omega
            have hc := chain_card hl
            rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
            have len := perm.length_eq
            simp only [List.length_cons] at len
            apply dispatch_complete (k := p + 2) (extra := extra) (last := last) (optimized (p + 2))
              hop hna hnb hnr hord' hk (by omega) (by omega) (cuts_full hl)
            apply ih _ _ _ gs' hnd hlen' _ hgs_ord hl
            simp; omega
          simp only [optimized, Bool.or_eq_true, List.any_eq_true]
          right
          rcases hm with direct | swap
          · exact ⟨(a, b, r), direct, go hp hs hz hg_ord⟩
          · exact ⟨(b, a, r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm])
              (ops_swap a b ▸ hz) (by rcases hg_ord with h | h | h; exact .inr (.inl h); exact .inl h; exact .inr (.inr h))⟩

def A : Fin 4 → Fin 4 → Bool := fun u v : Fin 4 => (1981 : ℕ).testBit (4 * u.val + v.val)

def posL : List (Fin 4 × Fin 4) := [(0, 0), (0, 2), (0, 3), (1, 0), (1, 1), (1, 3), (2, 0), (2, 1), (2, 2)]

def negL : List (Fin 4 × Fin 4) := [(0, 1), (1, 2), (2, 3), (3, 0), (3, 1), (3, 2), (3, 3)]

def samp (k : Fin 126) : Fin 4 × Fin 4 :=
  if k.val < 63 then negL.getD (k.val % 7) (0, 0) else posL.getD ((k.val - 63) / 7) (0, 0)

theorem input_rows : ∀ k : Fin 126,
    rawInputs.map (bit k) = PEqualNP.Represents.oneEach (samp k).1 (samp k).2 := by
  decide +kernel

theorem goal_rows : ∀ k : Fin 126, bit k goal = A (samp k).1 (samp k).2 := by
  decide +kernel

theorem rows_eval (C : Circuit) (hr : PEqualNP.Represents.Represents A C) (k : Fin 126) :
    (C.gates.foldl step (rawInputs.map (bit k))).getD C.output false = bit k goal := by
  rw [input_rows k, goal_rows k]
  exact hr (samp k).1 (samp k).2

theorem initial_rep : represents inputs.toFinset rawInputs := by
  intro u hu
  exact .inr (.inr (List.mem_toFinset.mpr hu))

theorem get_build (C : Circuit) (hg : Monotone2 C) (hr : PEqualNP.Represents.Represents A C) :
    build basicOps goal C.gates.length inputs.toFinset :=
  compile C.gates C.output hg rawInputs inputs.toFinset initial_rep (rows_eval C hr)

theorem inputs_nodup : inputs.Nodup := by decide +kernel

def allPairCuts : Nat := 0x7fffffffffffffff
def allWireBits : Nat := 0x3fffffffffffffffffffffffffffffff
def targetBits : Nat := 0x3fffffffffffffff8000000000000000

def sepN (w : Nat) : Nat := ((w >>> 63) &&& (allWireBits - w)) % 0x8000000000000000
def cutsN (ws : List Nat) : Nat := ws.foldr (fun w rest => sepN w ||| rest) 0

theorem sep_toNat (w : W) : (sep w).toNat = sepN w.toNat := by
  simp only [sep, sepN, BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_not,
    BitVec.toNat_ushiftRight]
  rfl

theorem cuts_toNat (ws : List W) : (cuts ws).toNat = cutsN (ws.map BitVec.toNat) := by
  induction ws with
  | nil => rfl
  | cons a r ih =>
    change (sep a ||| cuts r).toNat = sepN a.toNat ||| cutsN (r.map BitVec.toNat)
    rw [BitVec.toNat_or, sep_toNat, ih]

theorem beq_toNat {n : Nat} (x y : BitVec n) : (x.toNat == y.toNat) = (x == y) := by
  apply Bool.eq_iff_iff.mpr
  simp [BitVec.toNat_inj]

theorem match_goal : goal.toNat = targetBits := by decide +kernel
theorem match_full : (-1 : BitVec 63).toNat = allPairCuts := by decide +kernel
theorem match_word : (BitVec.allOnes 126).toNat = allWireBits := by decide +kernel

theorem singles_map {α β : Type} (f : α → β) (ws : List α) :
    singles (ws.map f) = (singles ws).map (fun (a,r) => (f a, r.map f)) := by
  induction ws with
  | nil => rfl
  | cons a r ih => simp [singles, ih, List.map_map, Function.comp_def]

theorem pairs_map {α β : Type} (f : α → β) (ws : List α) :
    pairs (ws.map f) = (pairs ws).map (fun (a,b,r) => (f a, f b, r.map f)) := by
  induction ws with
  | nil => rfl
  | cons a r ih => simp [pairs, ih, singles_map, List.map_map, Function.comp_def]

def opsN (a b : Nat) : List Nat := [a &&& b, a ||| b].filter (fun w => w != 0 && w != allWireBits)

theorem ops_map (a b : W) : opsN a.toNat b.toNat = (ops a b).map BitVec.toNat := by
  unfold opsN ops
  rw [← BitVec.toNat_and, ← BitVec.toNat_or, ← match_word]
  generalize (a &&& b) = p
  generalize (a ||| b) = q
  have keep (x : W) : (x.toNat != 0 && x.toNat != (BitVec.allOnes 126).toNat) =
      (x != 0 && x != BitVec.allOnes 126) := by
    change (!(x.toNat == (0 : W).toNat) && !(x.toNat == (BitVec.allOnes 126).toNat)) = _
    rw [beq_toNat, beq_toNat]; rfl
  simp only [List.filter_cons, keep, List.filter_nil]
  split <;> split <;> rfl

theorem memN (r : List W) (w : W) : (r.map BitVec.toNat).elem w.toNat = r.elem w := by
  apply Bool.eq_iff_iff.mpr
  simp [List.elem_eq_contains, BitVec.toNat_inj]

def dispatchN (extra last : Nat) (next : Nat → Nat → List Nat → Bool) (a b : Nat) (r : List Nat) : Bool :=
  let restCuts := cutsN r
  (opsN a b).any fun w =>
    if w == a || w == b || r.elem w || (a != last && b != last && w < last) then false
    else
      let v := sepN w ||| restCuts
      ((v == allPairCuts) && next extra w (w :: r)) ||
        ((extra != 0) && (((v ||| sepN a == allPairCuts) && next (extra - 1) w (w :: a :: r)) ||
                          ((v ||| sepN b == allPairCuts) && next (extra - 1) w (w :: b :: r)))) ||
        ((extra ≥ 2) && (v ||| sepN a ||| sepN b == allPairCuts) && next (extra - 2) w (w :: a :: b :: r))

theorem dispatchN_eq (extra last : Nat) (f : Nat → Nat → List Nat → Bool) (g : Nat → Nat → List W → Bool)
    (h : ∀ e l ws, f e l (ws.map BitVec.toNat) = g e l ws) (a b : W) (r : List W) :
    dispatchN extra last f a.toNat b.toNat (r.map BitVec.toNat) = dispatch extra last g a b r := by
  unfold dispatchN dispatch
  rw [ops_map, List.any_map]
  apply List.any_congr rfl
  intro w
  simp only [Function.comp_apply, beq_toNat, memN, ← cuts_toNat, ← sep_toNat, ← BitVec.toNat_or,
    ← match_full, ← List.map_cons, h]

def optN : Nat → Nat → Nat → List Nat → Bool
  | 0, _, _, ws => ws == [targetBits]
  | 1, _, _, [a] => a == targetBits
  | 1, _, _, [a,b] => (a &&& b == targetBits) || (a ||| b == targetBits)
  | 1, _, _, _ => false
  | 2, _, _, [a] => a == targetBits
  | 2, _, _, [a,b] => a == targetBits || b == targetBits || (a &&& b == targetBits) || (a ||| b == targetBits)
  | 2, _, _, [a,b,c] =>
    (a &&& b &&& c == targetBits) || (a ||| b ||| c == targetBits) ||
    ((a &&& b) ||| c == targetBits) || ((a ||| b) &&& c == targetBits) ||
    ((a &&& c) ||| b == targetBits) || ((a ||| c) &&& b == targetBits) ||
    ((b &&& c) ||| a == targetBits) || ((b ||| c) &&& a == targetBits)
  | 2, _, _, _ => false
  | k+3, extra, last, ws => ws == [targetBits] ||
    (pairs ws).any (fun (a,b,r) => dispatchN extra last (optN (k+2)) a b r)

theorem goal_listN (ws : List W) : (ws.map BitVec.toNat == [targetBits]) = (ws == [goal]) := by
  rcases ws with _ | ⟨a, _ | ⟨b,r⟩⟩ <;> simp [← match_goal, beq_toNat]

theorem optN_eq (k extra last : Nat) (ws : List W) :
    optN k extra last (ws.map BitVec.toNat) = optimized k extra last ws := by
  induction k generalizing extra last ws with
  | zero => exact goal_listN ws
  | succ k ih =>
    cases k with
    | zero =>
      rcases ws with _ | ⟨a, _ | ⟨b, _ | ⟨c,r⟩⟩⟩ <;>
        simp only [List.map_cons, List.map_nil, optN, optimized, ← match_goal, ← BitVec.toNat_or,
          ← BitVec.toNat_and, beq_toNat]
    | succ k =>
      cases k with
      | zero =>
        rcases ws with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d,r⟩⟩⟩⟩ <;>
          simp only [List.map_cons, List.map_nil, optN, optimized, ← match_goal, ← BitVec.toNat_or,
            ← BitVec.toNat_and, beq_toNat]
      | succ k =>
        simp only [optN, optimized, goal_listN, pairs_map, List.any_map]
        congr 1
        apply List.any_congr rfl
        rintro ⟨a,b,r⟩
        exact dispatchN_eq _ _ _ _ ih a b r

abbrev SearchNode := Nat × Nat × List Nat

def keepNode (ok : Bool) (node : SearchNode) : List SearchNode := if ok then [node] else []

theorem any_keepNode (f : SearchNode → Bool) (ok : Bool) (s : SearchNode) :
    (keepNode ok s).any f = (ok && f s) := by cases ok <;> simp [keepNode]

def nextNodes (extra last : Nat) (a b : Nat) (r : List Nat) : List SearchNode :=
  (opsN a b).flatMap fun w =>
    if w == a || w == b || r.elem w || (a != last && b != last && w < last) then []
    else
      let v := sepN w ||| cutsN r
      keepNode (v == allPairCuts) (extra,w,w :: r) ++
      (if extra != 0 then
        keepNode (v ||| sepN a == allPairCuts) (extra-1,w,w :: a :: r) ++
        keepNode (v ||| sepN b == allPairCuts) (extra-1,w,w :: b :: r) else []) ++
      keepNode ((extra ≥ 2) && (v ||| sepN a ||| sepN b == allPairCuts)) (extra-2,w,w :: a :: b :: r)

def frontierN (s : SearchNode) : List SearchNode :=
  (pairs s.2.2).flatMap fun (a,b,r) => nextNodes s.1 s.2.1 a b r

def evaluateN (k : Nat) (s : SearchNode) : Bool := optN k s.1 s.2.1 s.2.2

theorem nextNodes_any (extra last a b : Nat) (r : List Nat) (f : Nat → Nat → List Nat → Bool) :
    (nextNodes extra last a b r).any (fun s => f s.1 s.2.1 s.2.2) = dispatchN extra last f a b r := by
  simp only [nextNodes, dispatchN, List.any_flatMap]
  apply List.any_congr rfl
  intro w
  split
  · rfl
  · by_cases h : extra != 0 <;> simp [h, any_keepNode, Bool.and_assoc, Bool.or_assoc]

theorem evaluateN_step (k : Nat) (s : SearchNode) :
    evaluateN (k+3) s = ((s.2.2 == [targetBits]) || (frontierN s).any (evaluateN (k+2))) := by
  rcases s with ⟨e,l,ws⟩
  simp only [evaluateN, frontierN, optN, List.any_flatMap]
  congr 1
  apply List.any_congr rfl
  rintro ⟨a,b,r⟩
  exact (nextNodes_any e l a b r _).symm

def asNode (s : Nat × Nat × List W) : SearchNode := (s.1, s.2.1, s.2.2.map BitVec.toNat)

theorem batch_clear (xs : List (Nat × Nat × List W))
    (h : (xs.map asNode).any (evaluateN 8) = false) :
    xs.all (fun s => !(optimized 8 s.1 s.2.1 s.2.2)) = true := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    change (evaluateN 8 (asNode x) || (rest.map asNode).any (evaluateN 8)) = false at h
    simp only [Bool.or_eq_false_iff] at h
    simpa only [List.all_cons, evaluateN, asNode, optN_eq, ih h.2, Bool.and_true,
      Bool.not_eq_true'] using h.1

def mask0 : Nat := 0x102040810204081

def mask1 : Nat := 0x204081020408102

def mask2 : Nat := 0x408102040810204

def mask3 : Nat := 0x810204081020408

def mask4 : Nat := 0x1020408102040810

def mask5 : Nat := 0x2040810204081020

def mask6 : Nat := 0x4081020408102040

def mask7 : Nat := 0x78f1e3c78f1e3c78

def mask8 : Nat := 0x3f8000000000000000

def mask9 : Nat := 0x3f8102040810204081

def mask10 : Nat := 0x1fc00000000000000000

def mask11 : Nat := 0x1fc00204081020408102

def mask12 : Nat := 0xfe0000000000000000000

def mask13 : Nat := 0xfe03f8000000000000000

def mask14 : Nat := 0xfffff8102040810204081

def mask15 : Nat := 0xffffff9f3e7cf9f3e7cf9

def mask16 : Nat := 0x7f000000000000000000000

def mask17 : Nat := 0x7f0003f8000000000000000

def mask18 : Nat := 0x7ffffff8102040810204081

def mask19 : Nat := 0x3f80000000000000000000000

def mask20 : Nat := 0x3f80000000102040810204081

def mask21 : Nat := 0x3f8001fc00000000000000000

def mask22 : Nat := 0x3f80fffff8102040810204081

def mask23 : Nat := 0x3fff000000000000000000000

def mask24 : Nat := 0x1fc000000000000000000000000

def mask25 : Nat := 0x1fc000fe0000000000000000000

def mask26 : Nat := 0x1fc000fe0004489122448912244

def mask27 : Nat := 0x1fc000fe0007cf9f3e7cf9f3e7c

def mask28 : Nat := 0x1fc000fe03fc489122448912244

def mask29 : Nat := 0x1fc000fffc04489122448912244

def mask30 : Nat := 0x1fc000fffff8102040810204081

def mask31 : Nat := 0x1fc000fffffc58b162c58b162c5

def mask32 : Nat := 0x1fc07f000000000000000000000

def mask33 : Nat := 0x1fc07ffe0004489122448912244

def mask34 : Nat := 0x1fff80fe0004489122448912244

def mask35 : Nat := 0x1fffff000000204081020408102

def mask36 : Nat := 0x1fffff000007af5ebd7af5ebd7a

def mask37 : Nat := 0x1fffff0003f8204081020408102

def mask38 : Nat := 0x1fffff01fc00204081020408102

def mask39 : Nat := 0x1ffffffe0000204081020408102

def mask40 : Nat := 0x1ffffffe000468d1a3468d1a346

def mask41 : Nat := 0x1ffffffffff83060c183060c183

def mask42 : Nat := 0x1ffffffffffc78f1e3c78f1e3c7

def mask43 : Nat := 0xfe00000000000000000000000000

def mask44 : Nat := 0xfe00000000000408102040810204

def mask45 : Nat := 0xfe00000fffff8102040810204081

def mask46 : Nat := 0xfe0007f0003f8810204081020408

def mask47 : Nat := 0xfe0007f0003ff8f1e3c78f1e3c78

def mask48 : Nat := 0xfe0007f01fff8810204081020408

def mask49 : Nat := 0xfe0007ffe03f8810204081020408

def mask50 : Nat := 0xfe0007ffffff8912244891224489

def mask51 : Nat := 0xfe0007fffffff9f3e7cf9f3e7cf9

def mask52 : Nat := 0xfe03fff0003f8810204081020408

def mask53 : Nat := 0xfffc000fe0004489122448912244

def mask54 : Nat := 0xfffc07f0003f8810204081020408

def mask55 : Nat := 0xfffc07ffe03fcc993264c993264c

def mask56 : Nat := 0xfffc07ffe03ffcf9f3e7cf9f3e7c

def mask57 : Nat := 0xfffc07ffffffcd9b366cd9b366cd

def mask58 : Nat := 0xfffffff000000204081020408102

def mask59 : Nat := 0xfffffff0003f8a142850a142850a

def mask60 : Nat := 0xfffffff0003ffaf5ebd7af5ebd7a

def mask61 : Nat := 0xffffffffe03fce9d3a74e9d3a74e

def mask62 : Nat := 0xffffffffffff8b162c58b162c58b

def mask63 : Nat := 0x7f0000000000000000000000000000

def mask64 : Nat := 0x7f0000000fffff8102040810204081

def mask65 : Nat := 0x7f0003f80000001122448912244891

def mask66 : Nat := 0x7f0003f800000079f3e7cf9f3e7cf9

def mask67 : Nat := 0x7f0003f800003f9122448912244891

def mask68 : Nat := 0x7f0003f8001fc01122448912244891

def mask69 : Nat := 0x7f0003f80fe0001122448912244891

def mask70 : Nat := 0x7f0003f80fffff9122448912244891

def mask71 : Nat := 0x7f0003f80ffffff9f3e7cf9f3e7cf9

def mask72 : Nat := 0x7f0003fff000001122448912244891

def mask73 : Nat := 0x7f01fc000fe0004489122448912244

def mask74 : Nat := 0x7f01fff80000001122448912244891

def mask75 : Nat := 0x7f01fff80fe00055ab56ad5ab56ad5

def mask76 : Nat := 0x7f01fff80fffffd5ab56ad5ab56ad5

def mask77 : Nat := 0x7f01fffff000000204081020408102

def mask78 : Nat := 0x7f01fffff0000013264c993264c993

def mask79 : Nat := 0x7f01ffffffe00057af5ebd7af5ebd7

def mask80 : Nat := 0x7f01ffffffffff93264c993264c993

def mask81 : Nat := 0x7ffe00000000000000000000000000

def mask82 : Nat := 0x7ffe0007f0003f8810204081020408

def mask83 : Nat := 0x7ffe03f80000001122448912244891

def mask84 : Nat := 0x7ffe03fff0003f993264c993264c99

def mask85 : Nat := 0x7ffe03fff0003ff9f3e7cf9f3e7cf9

def mask86 : Nat := 0x7ffe03ffffffff993264c993264c99

def mask87 : Nat := 0x7ffffffff0003f9b366cd9b366cd9b

def mask88 : Nat := 0x7fffffffffe03fddbb76eddbb76edd

def mask89 : Nat := 0x3f800000000000000000000000000000

def mask90 : Nat := 0x3f80000000001fc02244891224489122

def mask91 : Nat := 0x3f80000000001fc07af5ebd7af5ebd7a

def mask92 : Nat := 0x3f80000000001fffa244891224489122

def mask93 : Nat := 0x3f800000000fffc02244891224489122

def mask94 : Nat := 0x3f800000000fffffa3468d1a3468d1a3

def mask95 : Nat := 0x3f80000007f01fc02244891224489122

def mask96 : Nat := 0x3f800003f8001fc02244891224489122

def mask97 : Nat := 0x3f8001fc00001fc02244891224489122

def mask98 : Nat := 0x3f8001fc000fffc066cd9b366cd9b366

def mask99 : Nat := 0x3f8001fc000fffffe7cf9f3e7cf9f3e7

def mask100 : Nat := 0x3f8001fffff01fc02244891224489122

def mask101 : Nat := 0x3f8001fffff01fc07af5ebd7af5ebd7a

def mask102 : Nat := 0x3f8001ffffffffc066cd9b366cd9b366

def mask103 : Nat := 0x3f8001ffffffffffa3468d1a3468d1a3

def mask104 : Nat := 0x3f80fe0000001fc02244891224489122

def mask105 : Nat := 0x3f80fe0007f01fffaa54a952a54a952a

def mask106 : Nat := 0x3f80fe0007f01ffffaf5ebd7af5ebd7a

def mask107 : Nat := 0x3f80fe0007ffffffab56ad5ab56ad5ab

def mask108 : Nat := 0x3f80fffc07ffffffeeddbb76eddbb76e

def mask109 : Nat := 0x3f80fffffff01fffaa54a952a54a952a

def mask110 : Nat := 0x3fff000000001fc02244891224489122

def mask111 : Nat := 0x3fff0003f8001fc03366cd9b366cd9b3

def mask112 : Nat := 0x3fff0003f80fffffb366cd9b366cd9b3

def mask113 : Nat := 0x3fff01fffff01fc03366cd9b366cd9b3

def mask114 : Nat := 0x3fff01ffffffffffb366cd9b366cd9b3

def mask115 : Nat := 0x3ffffe00000000000408102040810204

def mask116 : Nat := 0x3ffffe00000000007cf9f3e7cf9f3e7c

def mask117 : Nat := 0x3ffffe000000003f8408102040810204

def mask118 : Nat := 0x3ffffe0000001fc00408102040810204

def mask119 : Nat := 0x3ffffe0000001fc0264c993264c99326

def mask120 : Nat := 0x3ffffe00000fe0000408102040810204

def mask121 : Nat := 0x3ffffe00000fffff850a142850a14285

def mask122 : Nat := 0x3ffffe0007f000000408102040810204

def mask123 : Nat := 0x3ffffe0007f0003f8c183060c183060c

def mask124 : Nat := 0x3ffffe0007f0003ffcf9f3e7cf9f3e7c

def mask125 : Nat := 0x3ffffe0007ffffff8d1a3468d1a3468d

def mask126 : Nat := 0x3ffffe03f80000000408102040810204

def mask127 : Nat := 0x3ffffe03f8000000152a54a952a54a95

def mask128 : Nat := 0x3ffffe03f80fffff952a54a952a54a95

def mask129 : Nat := 0x3ffffe03fff0003f9d3a74e9d3a74e9d

def mask130 : Nat := 0x3ffffe03fff01fffbb76eddbb76eddbb

def mask131 : Nat := 0x3ffffffc000000000408102040810204

def mask132 : Nat := 0x3ffffffc000fe0004489122448912244

def mask133 : Nat := 0x3ffffffc000fffc066cd9b366cd9b366

def mask134 : Nat := 0x3ffffffc000fffffc58b162c58b162c5

def mask135 : Nat := 0x3ffffffc07ffe03fcc993264c993264c

def mask136 : Nat := 0x3ffffffff80fe00055ab56ad5ab56ad5

def mask137 : Nat := 0x3ffffffffff00000060c183060c18306

def mask138 : Nat := 0x3ffffffffff0003f8e1c3870e1c3870e

def mask139 : Nat := 0x3ffffffffff01fc0264c993264c99326

def mask140 : Nat := 0x3fffffffffffe000468d1a3468d1a346

def mask141 : Nat := 0x3fffffffffffffff870e1c3870e1c387

def branch0 : SearchNode := (3, mask100, [mask100, mask70, mask115, mask46, mask26])

def branch1 : SearchNode := (1, mask41, [mask41, mask14, mask35, mask115, mask46, mask65, mask90, mask26])

def branch2 : SearchNode := (1, mask8, [mask8, mask14, mask46, mask35, mask115, mask65, mask90, mask26])

def branch3 : SearchNode := (1, mask50, [mask50, mask14, mask46, mask35, mask115, mask65, mask90, mask26])

def branch4 : SearchNode := (3, mask70, [mask70, mask35, mask115, mask46, mask90, mask26])

def branch5 : SearchNode := (2, mask70, [mask70, mask14, mask35, mask115, mask46, mask90, mask26])

def branch6 : SearchNode := (2, mask70, [mask70, mask65, mask35, mask115, mask46, mask90, mask26])

def branch7 : SearchNode := (1, mask70, [mask70, mask14, mask65, mask35, mask115, mask46, mask90, mask26])

def branch8 : SearchNode := (1, mask10, [mask10, mask14, mask90, mask35, mask115, mask46, mask65, mask26])

def branch9 : SearchNode := (1, mask12, [mask12, mask14, mask26, mask35, mask115, mask46, mask65, mask90])

def branch10 : SearchNode := (1, mask31, [mask31, mask14, mask26, mask35, mask115, mask46, mask65, mask90])

def branch11 : SearchNode := (1, mask16, [mask16, mask35, mask46, mask14, mask115, mask65, mask90, mask26])

def branch12 : SearchNode := (1, mask59, [mask59, mask35, mask46, mask14, mask115, mask65, mask90, mask26])

def branch13 : SearchNode := (1, mask19, [mask19, mask35, mask65, mask14, mask115, mask46, mask90, mask26])

def branch14 : SearchNode := (3, mask100, [mask100, mask14, mask115, mask46, mask65, mask26])

def branch15 : SearchNode := (2, mask100, [mask100, mask35, mask14, mask115, mask46, mask65, mask26])

def branch16 : SearchNode := (2, mask100, [mask100, mask90, mask14, mask115, mask46, mask65, mask26])

def branch17 : SearchNode := (1, mask24, [mask24, mask35, mask26, mask14, mask115, mask46, mask65, mask90])

def branch18 : SearchNode := (1, mask40, [mask40, mask35, mask26, mask14, mask115, mask46, mask65, mask90])

def branch19 : SearchNode := (1, mask43, [mask43, mask115, mask46, mask14, mask35, mask65, mask90, mask26])

def branch20 : SearchNode := (1, mask63, [mask63, mask115, mask65, mask14, mask35, mask46, mask90, mask26])

def branch21 : SearchNode := (3, mask132, [mask132, mask14, mask35, mask46, mask65, mask90])

def branch22 : SearchNode := (2, mask84, [mask84, mask46, mask14, mask35, mask115, mask90, mask26])

def branch23 : SearchNode := (1, mask84, [mask84, mask46, mask65, mask14, mask35, mask115, mask90, mask26])

def branch24 : SearchNode := (2, mask55, [mask55, mask46, mask14, mask35, mask115, mask65, mask90])

def branch25 : SearchNode := (1, mask55, [mask55, mask46, mask26, mask14, mask35, mask115, mask65, mask90])

def branch26 : SearchNode := (2, mask70, [mask70, mask35, mask115, mask7, mask46, mask90, mask26])

def branch27 : SearchNode := (2, mask100, [mask100, mask14, mask115, mask7, mask46, mask65, mask26])

def branch28 : SearchNode := (1, mask47, [mask47, mask46, mask14, mask35, mask115, mask65, mask90, mask26])

def branch0Part0 : List SearchNode :=
  [(1, mask21, [mask21, mask100, mask70, mask115, mask46, mask26]),
    (1, mask114, [mask114, mask100, mask70, mask115, mask46, mask26]),
    (1, mask89, [mask89, mask100, mask115, mask70, mask46, mask26]),
    (1, mask139, [mask139, mask100, mask115, mask70, mask46, mask26]),
    (1, mask16, [mask16, mask100, mask46, mask70, mask115, mask26]),
    (1, mask109, [mask109, mask100, mask46, mask70, mask115, mask26]),
    (1, mask24, [mask24, mask100, mask26, mask70, mask115, mask46]),
    (1, mask102, [mask102, mask100, mask26, mask70, mask115, mask46])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch0Part0_dead : branch0Part0.any (evaluateN 6) = false := by
  decide +kernel

def branch0Part1 : List SearchNode :=
  [(1, mask128, [mask128, mask70, mask115, mask100, mask46, mask26]),
    (1, mask123, [mask123, mask115, mask46, mask100, mask70, mask26]),
    (3, mask132, [mask132, mask100, mask70, mask46]),
    (2, mask132, [mask132, mask115, mask100, mask70, mask46]),
    (2, mask132, [mask132, mask26, mask100, mask70, mask46]),
    (1, mask132, [mask132, mask115, mask26, mask100, mask70, mask46])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch0Part1_dead : branch0Part1.any (evaluateN 6) = false := by
  decide +kernel

def branch0Next : List SearchNode :=
  branch0Part0 ++ branch0Part1

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch0Next_dead : branch0Next.any (evaluateN 6) = false := by
  simp only [branch0Next, List.any_append, List.any_cons, List.any_nil, branch0Part0_dead, branch0Part1_dead, Bool.or_false, Bool.false_or]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch0_front : frontierN branch0 = branch0Next := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch0_dead : evaluateN 7 branch0 = false := by
  rw [evaluateN_step 4, branch0_front, branch0Next_dead, Bool.or_false]
  rfl

def branch1Part0 : List SearchNode :=
  [(0, mask141, [mask141, mask115, mask14, mask35, mask46, mask65, mask90, mask26]),
    (0, mask17, [mask17, mask46, mask14, mask35, mask115, mask65, mask90, mask26]),
    (0, mask62, [mask62, mask46, mask14, mask35, mask115, mask65, mask90, mask26]),
    (0, mask20, [mask20, mask65, mask14, mask35, mask115, mask46, mask90, mask26]),
    (0, mask80, [mask80, mask65, mask14, mask35, mask115, mask46, mask90, mask26]),
    (0, mask11, [mask11, mask90, mask14, mask35, mask115, mask46, mask65, mask26]),
    (0, mask103, [mask103, mask90, mask14, mask35, mask115, mask46, mask65, mask26]),
    (1, mask25, [mask25, mask14, mask35, mask115, mask46, mask65, mask90])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch1Part0_dead : branch1Part0.any (evaluateN 7) = false := by
  decide +kernel

def branch1Part1 : List SearchNode :=
  [(0, mask25, [mask25, mask41, mask14, mask35, mask115, mask46, mask65, mask90]),
    (0, mask25, [mask25, mask26, mask14, mask35, mask115, mask46, mask65, mask90]),
    (0, mask42, [mask42, mask26, mask14, mask35, mask115, mask46, mask65, mask90]),
    (0, mask121, [mask121, mask115, mask41, mask35, mask46, mask65, mask90, mask26]),
    (0, mask50, [mask50, mask46, mask41, mask35, mask115, mask65, mask90, mask26]),
    (1, mask70, [mask70, mask41, mask35, mask115, mask46, mask90, mask26]),
    (0, mask70, [mask70, mask14, mask41, mask35, mask115, mask46, mask90, mask26]),
    (0, mask70, [mask70, mask65, mask41, mask35, mask115, mask46, mask90, mask26]),
    (0, mask137, [mask137, mask115, mask41, mask14, mask46, mask65, mask90, mask26]),
    (0, mask59, [mask59, mask46, mask41, mask14, mask115, mask65, mask90, mask26]),
    (1, mask100, [mask100, mask41, mask14, mask115, mask46, mask65, mask26]),
    (0, mask100, [mask100, mask35, mask41, mask14, mask115, mask46, mask65, mask26])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch1Part1_dead : branch1Part1.any (evaluateN 7) = false := by
  decide +kernel

def branch1Part2 : List SearchNode :=
  [(0, mask100, [mask100, mask90, mask41, mask14, mask115, mask46, mask65, mask26]),
    (1, mask132, [mask132, mask41, mask14, mask35, mask46, mask65, mask90]),
    (0, mask132, [mask132, mask115, mask41, mask14, mask35, mask46, mask65, mask90]),
    (0, mask132, [mask132, mask26, mask41, mask14, mask35, mask46, mask65, mask90]),
    (0, mask84, [mask84, mask46, mask41, mask14, mask35, mask115, mask90, mask26]),
    (0, mask105, [mask105, mask46, mask41, mask14, mask35, mask115, mask65, mask26]),
    (0, mask55, [mask55, mask46, mask41, mask14, mask35, mask115, mask65, mask90])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch1Part2_dead : branch1Part2.any (evaluateN 7) = false := by
  decide +kernel

def branch1Next : List SearchNode :=
  branch1Part0 ++ branch1Part1 ++ branch1Part2

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch1Next_dead : branch1Next.any (evaluateN 7) = false := by
  simp only [branch1Next, List.any_append, List.any_cons, List.any_nil, branch1Part0_dead, branch1Part1_dead, branch1Part2_dead, Bool.or_false, Bool.false_or]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch1_front : frontierN branch1 = branch1Next := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch1_dead : evaluateN 8 branch1 = false := by
  rw [evaluateN_step 5, branch1_front, branch1Next_dead, Bool.or_false]
  rfl

def branch2Part0 : List SearchNode :=
  [(1, mask37, [mask37, mask14, mask46, mask115, mask65, mask90, mask26]),
    (0, mask37, [mask37, mask8, mask14, mask46, mask115, mask65, mask90, mask26]),
    (0, mask37, [mask37, mask35, mask14, mask46, mask115, mask65, mask90, mask26]),
    (1, mask117, [mask117, mask14, mask46, mask35, mask65, mask90, mask26]),
    (0, mask117, [mask117, mask8, mask14, mask46, mask35, mask65, mask90, mask26]),
    (0, mask117, [mask117, mask115, mask14, mask46, mask35, mask65, mask90, mask26]),
    (1, mask67, [mask67, mask14, mask46, mask35, mask115, mask90, mask26]),
    (0, mask67, [mask67, mask8, mask14, mask46, mask35, mask115, mask90, mask26]),
    (0, mask67, [mask67, mask65, mask14, mask46, mask35, mask115, mask90, mask26]),
    (1, mask92, [mask92, mask14, mask46, mask35, mask115, mask65, mask26]),
    (0, mask92, [mask92, mask8, mask14, mask46, mask35, mask115, mask65, mask26]),
    (0, mask92, [mask92, mask90, mask14, mask46, mask35, mask115, mask65, mask26])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch2Part0_dead : branch2Part0.any (evaluateN 7) = false := by
  decide +kernel

def branch2Part1 : List SearchNode :=
  [(1, mask28, [mask28, mask14, mask46, mask35, mask115, mask65, mask90]),
    (0, mask28, [mask28, mask8, mask14, mask46, mask35, mask115, mask65, mask90]),
    (0, mask28, [mask28, mask26, mask14, mask46, mask35, mask115, mask65, mask90])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch2Part1_dead : branch2Part1.any (evaluateN 7) = false := by
  decide +kernel

def branch2Part2 : List SearchNode :=
  [(1, mask50, [mask50, mask8, mask35, mask115, mask65, mask90, mask26]),
    (0, mask50, [mask50, mask14, mask8, mask35, mask115, mask65, mask90, mask26]),
    (0, mask50, [mask50, mask46, mask8, mask35, mask115, mask65, mask90, mask26]),
    (1, mask70, [mask70, mask8, mask46, mask35, mask115, mask90, mask26])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch2Part2_dead : branch2Part2.any (evaluateN 7) = false := by
  decide +kernel

def branch2Part3 : List SearchNode :=
  [(0, mask70, [mask70, mask14, mask8, mask46, mask35, mask115, mask90, mask26]),
    (0, mask70, [mask70, mask65, mask8, mask46, mask35, mask115, mask90, mask26]),
    (1, mask84, [mask84, mask8, mask14, mask35, mask115, mask90, mask26]),
    (0, mask84, [mask84, mask46, mask8, mask14, mask35, mask115, mask90, mask26]),
    (0, mask84, [mask84, mask65, mask8, mask14, mask35, mask115, mask90, mask26]),
    (0, mask105, [mask105, mask46, mask8, mask14, mask35, mask115, mask65, mask26]),
    (0, mask55, [mask55, mask46, mask8, mask14, mask35, mask115, mask65, mask90]),
    (1, mask100, [mask100, mask8, mask14, mask46, mask115, mask65, mask26]),
    (0, mask100, [mask100, mask35, mask8, mask14, mask46, mask115, mask65, mask26]),
    (0, mask100, [mask100, mask90, mask8, mask14, mask46, mask115, mask65, mask26]),
    (1, mask132, [mask132, mask8, mask14, mask46, mask35, mask65, mask90]),
    (0, mask132, [mask132, mask115, mask8, mask14, mask46, mask35, mask65, mask90]),
    (0, mask132, [mask132, mask26, mask8, mask14, mask46, mask35, mask65, mask90])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch2Part3_dead : branch2Part3.any (evaluateN 7) = false := by
  decide +kernel

def branch2Next : List SearchNode :=
  branch2Part0 ++ branch2Part1 ++ branch2Part2 ++ branch2Part3

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch2Next_dead : branch2Next.any (evaluateN 7) = false := by
  simp only [branch2Next, List.any_append, List.any_cons, List.any_nil, branch2Part0_dead, branch2Part1_dead, branch2Part2_dead, branch2Part3_dead, Bool.or_false, Bool.false_or]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch2_front : frontierN branch2 = branch2Next := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch2_dead : evaluateN 8 branch2 = false := by
  rw [evaluateN_step 5, branch2_front, branch2Next_dead, Bool.or_false]
  rfl

def branch3Part0 : List SearchNode :=
  [(0, mask16, [mask16, mask35, mask14, mask46, mask115, mask65, mask90, mask26]),
    (0, mask62, [mask62, mask35, mask14, mask46, mask115, mask65, mask90, mask26]),
    (0, mask43, [mask43, mask115, mask14, mask46, mask35, mask65, mask90, mask26]),
    (0, mask125, [mask125, mask115, mask14, mask46, mask35, mask65, mask90, mask26]),
    (0, mask0, [mask0, mask65, mask14, mask46, mask35, mask115, mask90, mask26]),
    (1, mask86, [mask86, mask14, mask46, mask35, mask115, mask90, mask26]),
    (0, mask86, [mask86, mask50, mask14, mask46, mask35, mask115, mask90, mask26]),
    (0, mask86, [mask86, mask65, mask14, mask46, mask35, mask115, mask90, mask26])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch3Part0_dead : branch3Part0.any (evaluateN 7) = false := by
  decide +kernel

def branch3Part1 : List SearchNode :=
  [(0, mask10, [mask10, mask90, mask14, mask46, mask35, mask115, mask65, mask26]),
    (0, mask107, [mask107, mask90, mask14, mask46, mask35, mask115, mask65, mask26]),
    (0, mask12, [mask12, mask26, mask14, mask46, mask35, mask115, mask65, mask90]),
    (0, mask57, [mask57, mask26, mask14, mask46, mask35, mask115, mask65, mask90]),
    (0, mask121, [mask121, mask115, mask50, mask46, mask35, mask65, mask90, mask26]),
    (1, mask70, [mask70, mask50, mask46, mask35, mask115, mask90, mask26]),
    (0, mask70, [mask70, mask14, mask50, mask46, mask35, mask115, mask90, mask26]),
    (0, mask70, [mask70, mask65, mask50, mask46, mask35, mask115, mask90, mask26]),
    (0, mask94, [mask94, mask90, mask50, mask46, mask35, mask115, mask65, mask26])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch3Part1_dead : branch3Part1.any (evaluateN 7) = false := by
  decide +kernel

def branch3Part2 : List SearchNode :=
  [(0, mask59, [mask59, mask35, mask50, mask14, mask115, mask65, mask90, mask26]),
    (0, mask123, [mask123, mask115, mask50, mask14, mask35, mask65, mask90, mask26]),
    (0, mask84, [mask84, mask46, mask50, mask14, mask35, mask115, mask90, mask26]),
    (1, mask105, [mask105, mask50, mask14, mask35, mask115, mask65, mask26]),
    (0, mask105, [mask105, mask46, mask50, mask14, mask35, mask115, mask65, mask26]),
    (0, mask105, [mask105, mask90, mask50, mask14, mask35, mask115, mask65, mask26]),
    (1, mask55, [mask55, mask50, mask14, mask35, mask115, mask65, mask90]),
    (0, mask55, [mask55, mask46, mask50, mask14, mask35, mask115, mask65, mask90]),
    (0, mask55, [mask55, mask26, mask50, mask14, mask35, mask115, mask65, mask90])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch3Part2_dead : branch3Part2.any (evaluateN 7) = false := by
  decide +kernel

def branch3Part3 : List SearchNode :=
  [(1, mask100, [mask100, mask50, mask14, mask46, mask115, mask65, mask26]),
    (0, mask100, [mask100, mask35, mask50, mask14, mask46, mask115, mask65, mask26]),
    (0, mask100, [mask100, mask90, mask50, mask14, mask46, mask115, mask65, mask26]),
    (1, mask132, [mask132, mask50, mask14, mask46, mask35, mask65, mask90]),
    (0, mask132, [mask132, mask115, mask50, mask14, mask46, mask35, mask65, mask90]),
    (0, mask132, [mask132, mask26, mask50, mask14, mask46, mask35, mask65, mask90])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch3Part3_dead : branch3Part3.any (evaluateN 7) = false := by
  decide +kernel

def branch3Next : List SearchNode :=
  branch3Part0 ++ branch3Part1 ++ branch3Part2 ++ branch3Part3

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch3Next_dead : branch3Next.any (evaluateN 7) = false := by
  simp only [branch3Next, List.any_append, List.any_cons, List.any_nil, branch3Part0_dead, branch3Part1_dead, branch3Part2_dead, branch3Part3_dead, Bool.or_false, Bool.false_or]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch3_front : frontierN branch3 = branch3Next := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch3_dead : evaluateN 8 branch3 = false := by
  rw [evaluateN_step 5, branch3_front, branch3Next_dead, Bool.or_false]
  rfl

def branch4Part0 : List SearchNode :=
  [(1, mask19, [mask19, mask70, mask35, mask115, mask46, mask90, mask26])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch4Part0_dead : branch4Part0.any (evaluateN 7) = false := by
  decide +kernel

def branch4Part1 : List SearchNode :=
  [(1, mask80, [mask80, mask70, mask35, mask115, mask46, mask90, mask26]),
    (1, mask63, [mask63, mask70, mask115, mask35, mask46, mask90, mask26])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch4Part1_dead : branch4Part1.any (evaluateN 7) = false := by
  decide +kernel

def branch4Part2 : List SearchNode :=
  [(1, mask128, [mask128, mask70, mask115, mask35, mask46, mask90, mask26])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch4Part2_dead : branch4Part2.any (evaluateN 7) = false := by
  decide +kernel

def branch4Part3 : List SearchNode :=
  [(1, mask8, [mask8, mask70, mask46, mask35, mask115, mask90, mask26])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch4Part3_dead : branch4Part3.any (evaluateN 7) = false := by
  decide +kernel

def branch4Part4 : List SearchNode :=
  [(1, mask86, [mask86, mask70, mask46, mask35, mask115, mask90, mask26])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch4Part4_dead : branch4Part4.any (evaluateN 7) = false := by
  decide +kernel

def branch4Part5 : List SearchNode :=
  [(1, mask10, [mask10, mask70, mask90, mask35, mask115, mask46, mask26]),
    (1, mask112, [mask112, mask70, mask90, mask35, mask115, mask46, mask26])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch4Part5_dead : branch4Part5.any (evaluateN 7) = false := by
  decide +kernel

def branch4Part6 : List SearchNode :=
  [(1, mask12, [mask12, mask70, mask26, mask35, mask115, mask46, mask90]),
    (1, mask76, [mask76, mask70, mask26, mask35, mask115, mask46, mask90])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch4Part6_dead : branch4Part6.any (evaluateN 7) = false := by
  decide +kernel

def branch4Part7 : List SearchNode :=
  [(1, mask137, [mask137, mask35, mask115, mask70, mask46, mask90, mask26])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch4Part7_dead : branch4Part7.any (evaluateN 7) = false := by
  decide +kernel

def branch4Part8 : List SearchNode :=
  [(2, mask100, [mask100, mask35, mask70, mask115, mask46, mask26])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch4Part8_dead : branch4Part8.any (evaluateN 7) = false := by
  decide +kernel

def branch4Part9 : List SearchNode :=
  [(2, mask100, [mask100, mask90, mask70, mask115, mask46, mask26])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch4Part9_dead : branch4Part9.any (evaluateN 7) = false := by
  decide +kernel

def branch4Part10 : List SearchNode :=
  [(1, mask100, [mask100, mask35, mask90, mask70, mask115, mask46, mask26]),
    (1, mask123, [mask123, mask115, mask46, mask70, mask35, mask90, mask26])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch4Part10_dead : branch4Part10.any (evaluateN 7) = false := by
  decide +kernel

def branch4Part11 : List SearchNode :=
  [(1, mask89, [mask89, mask115, mask90, mask70, mask35, mask46, mask26]),
    (1, mask119, [mask119, mask115, mask90, mask70, mask35, mask46, mask26])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch4Part11_dead : branch4Part11.any (evaluateN 7) = false := by
  decide +kernel

def branch4Part12 : List SearchNode :=
  [(3, mask132, [mask132, mask70, mask35, mask46, mask90])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch4Part12_dead : branch4Part12.any (evaluateN 7) = false := by
  decide +kernel

def branch4Part13 : List SearchNode :=
  [(2, mask132, [mask132, mask115, mask70, mask35, mask46, mask90]),
    (2, mask132, [mask132, mask26, mask70, mask35, mask46, mask90]),
    (1, mask132, [mask132, mask115, mask26, mask70, mask35, mask46, mask90])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch4Part13_dead : branch4Part13.any (evaluateN 7) = false := by
  decide +kernel

def branch4Part14 : List SearchNode :=
  [(2, mask105, [mask105, mask46, mask70, mask35, mask115, mask26]),
    (1, mask105, [mask105, mask46, mask90, mask70, mask35, mask115, mask26]),
    (1, mask98, [mask98, mask90, mask26, mask70, mask35, mask115, mask46])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch4Part14_dead : branch4Part14.any (evaluateN 7) = false := by
  decide +kernel

def branch4Next : List SearchNode :=
  branch4Part0 ++ branch4Part1 ++ branch4Part2 ++ branch4Part3 ++ branch4Part4 ++ branch4Part5 ++ branch4Part6 ++ branch4Part7 ++ [branch0] ++ branch4Part8 ++ branch4Part9 ++ branch4Part10 ++ branch4Part11 ++ branch4Part12 ++ branch4Part13 ++ branch4Part14

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch4Next_dead : branch4Next.any (evaluateN 7) = false := by
  simp only [branch4Next, List.any_append, List.any_cons, List.any_nil, branch4Part0_dead, branch4Part1_dead, branch4Part2_dead, branch4Part3_dead, branch4Part4_dead, branch4Part5_dead, branch4Part6_dead, branch4Part7_dead, branch0_dead, branch4Part8_dead, branch4Part9_dead, branch4Part10_dead, branch4Part11_dead, branch4Part12_dead, branch4Part13_dead, branch4Part14_dead, Bool.or_false, Bool.false_or]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch4_front : frontierN branch4 = branch4Next := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch4_dead : evaluateN 8 branch4 = false := by
  rw [evaluateN_step 5, branch4_front, branch4Next_dead, Bool.or_false]
  rfl

def branch5Part0 : List SearchNode :=
  [(0, mask19, [mask19, mask70, mask35, mask14, mask115, mask46, mask90, mask26]),
    (0, mask80, [mask80, mask70, mask35, mask14, mask115, mask46, mask90, mask26]),
    (0, mask63, [mask63, mask70, mask115, mask14, mask35, mask46, mask90, mask26]),
    (0, mask128, [mask128, mask70, mask115, mask14, mask35, mask46, mask90, mask26]),
    (0, mask8, [mask8, mask70, mask46, mask14, mask35, mask115, mask90, mask26]),
    (1, mask86, [mask86, mask46, mask14, mask35, mask115, mask90, mask26]),
    (0, mask86, [mask86, mask70, mask46, mask14, mask35, mask115, mask90, mask26]),
    (0, mask10, [mask10, mask70, mask90, mask14, mask35, mask115, mask46, mask26]),
    (0, mask112, [mask112, mask70, mask90, mask14, mask35, mask115, mask46, mask26]),
    (0, mask12, [mask12, mask70, mask26, mask14, mask35, mask115, mask46, mask90]),
    (0, mask76, [mask76, mask70, mask26, mask14, mask35, mask115, mask46, mask90])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch5Part0_dead : branch5Part0.any (evaluateN 7) = false := by
  decide +kernel

def branch5Part1 : List SearchNode :=
  [(1, mask121, [mask121, mask115, mask70, mask35, mask46, mask90, mask26]),
    (0, mask121, [mask121, mask14, mask115, mask70, mask35, mask46, mask90, mask26]),
    (1, mask94, [mask94, mask90, mask70, mask35, mask115, mask46, mask26]),
    (0, mask94, [mask94, mask14, mask90, mask70, mask35, mask115, mask46, mask26]),
    (0, mask137, [mask137, mask35, mask115, mask70, mask14, mask46, mask90, mask26])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch5Part1_dead : branch5Part1.any (evaluateN 7) = false := by
  decide +kernel

def branch5Part2 : List SearchNode :=
  [(2, mask100, [mask100, mask70, mask14, mask115, mask46, mask26])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch5Part2_dead : branch5Part2.any (evaluateN 7) = false := by
  decide +kernel

def branch5Part3 : List SearchNode :=
  [(1, mask100, [mask100, mask35, mask70, mask14, mask115, mask46, mask26]),
    (1, mask100, [mask100, mask90, mask70, mask14, mask115, mask46, mask26]),
    (0, mask100, [mask100, mask35, mask90, mask70, mask14, mask115, mask46, mask26]),
    (0, mask123, [mask123, mask115, mask46, mask70, mask14, mask35, mask90, mask26]),
    (0, mask89, [mask89, mask115, mask90, mask70, mask14, mask35, mask46, mask26]),
    (0, mask119, [mask119, mask115, mask90, mask70, mask14, mask35, mask46, mask26])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch5Part3_dead : branch5Part3.any (evaluateN 7) = false := by
  decide +kernel

def branch5Part4 : List SearchNode :=
  [(2, mask132, [mask132, mask70, mask14, mask35, mask46, mask90]),
    (1, mask132, [mask132, mask115, mask70, mask14, mask35, mask46, mask90]),
    (1, mask132, [mask132, mask26, mask70, mask14, mask35, mask46, mask90]),
    (0, mask132, [mask132, mask115, mask26, mask70, mask14, mask35, mask46, mask90]),
    (1, mask105, [mask105, mask46, mask70, mask14, mask35, mask115, mask26]),
    (0, mask105, [mask105, mask46, mask90, mask70, mask14, mask35, mask115, mask26]),
    (0, mask98, [mask98, mask90, mask26, mask70, mask14, mask35, mask115, mask46])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch5Part4_dead : branch5Part4.any (evaluateN 7) = false := by
  decide +kernel

def branch5Next : List SearchNode :=
  branch5Part0 ++ branch5Part1 ++ branch5Part2 ++ branch5Part3 ++ branch5Part4

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch5Next_dead : branch5Next.any (evaluateN 7) = false := by
  simp only [branch5Next, List.any_append, List.any_cons, List.any_nil, branch5Part0_dead, branch5Part1_dead, branch5Part2_dead, branch5Part3_dead, branch5Part4_dead, Bool.or_false, Bool.false_or]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch5_front : frontierN branch5 = branch5Next := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch5_dead : evaluateN 8 branch5 = false := by
  rw [evaluateN_step 5, branch5_front, branch5Next_dead, Bool.or_false]
  rfl

def branch6Part0 : List SearchNode :=
  [(0, mask19, [mask19, mask70, mask35, mask65, mask115, mask46, mask90, mask26]),
    (0, mask80, [mask80, mask70, mask35, mask65, mask115, mask46, mask90, mask26]),
    (0, mask63, [mask63, mask70, mask115, mask65, mask35, mask46, mask90, mask26]),
    (0, mask128, [mask128, mask70, mask115, mask65, mask35, mask46, mask90, mask26]),
    (0, mask8, [mask8, mask70, mask46, mask65, mask35, mask115, mask90, mask26]),
    (0, mask86, [mask86, mask70, mask46, mask65, mask35, mask115, mask90, mask26]),
    (0, mask10, [mask10, mask70, mask90, mask65, mask35, mask115, mask46, mask26]),
    (0, mask112, [mask112, mask70, mask90, mask65, mask35, mask115, mask46, mask26]),
    (0, mask12, [mask12, mask70, mask26, mask65, mask35, mask115, mask46, mask90]),
    (0, mask76, [mask76, mask70, mask26, mask65, mask35, mask115, mask46, mask90]),
    (1, mask78, [mask78, mask35, mask70, mask115, mask46, mask90, mask26]),
    (0, mask78, [mask78, mask65, mask35, mask70, mask115, mask46, mask90, mask26])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch6Part0_dead : branch6Part0.any (evaluateN 7) = false := by
  decide +kernel

def branch6Part1 : List SearchNode :=
  [(1, mask127, [mask127, mask115, mask70, mask35, mask46, mask90, mask26]),
    (0, mask127, [mask127, mask65, mask115, mask70, mask35, mask46, mask90, mask26]),
    (1, mask84, [mask84, mask46, mask70, mask35, mask115, mask90, mask26]),
    (0, mask84, [mask84, mask65, mask46, mask70, mask35, mask115, mask90, mask26]),
    (1, mask111, [mask111, mask90, mask70, mask35, mask115, mask46, mask26]),
    (0, mask111, [mask111, mask65, mask90, mask70, mask35, mask115, mask46, mask26])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch6Part1_dead : branch6Part1.any (evaluateN 7) = false := by
  decide +kernel

def branch6Part2 : List SearchNode :=
  [(1, mask75, [mask75, mask26, mask70, mask35, mask115, mask46, mask90]),
    (0, mask75, [mask75, mask65, mask26, mask70, mask35, mask115, mask46, mask90]),
    (0, mask137, [mask137, mask35, mask115, mask70, mask65, mask46, mask90, mask26])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch6Part2_dead : branch6Part2.any (evaluateN 7) = false := by
  decide +kernel

def branch6Part3 : List SearchNode :=
  [(2, mask100, [mask100, mask70, mask65, mask115, mask46, mask26]),
    (1, mask100, [mask100, mask35, mask70, mask65, mask115, mask46, mask26])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch6Part3_dead : branch6Part3.any (evaluateN 7) = false := by
  decide +kernel

def branch6Part4 : List SearchNode :=
  [(1, mask100, [mask100, mask90, mask70, mask65, mask115, mask46, mask26]),
    (0, mask100, [mask100, mask35, mask90, mask70, mask65, mask115, mask46, mask26]),
    (0, mask123, [mask123, mask115, mask46, mask70, mask65, mask35, mask90, mask26]),
    (0, mask89, [mask89, mask115, mask90, mask70, mask65, mask35, mask46, mask26]),
    (0, mask119, [mask119, mask115, mask90, mask70, mask65, mask35, mask46, mask26]),
    (2, mask132, [mask132, mask70, mask65, mask35, mask46, mask90]),
    (1, mask132, [mask132, mask115, mask70, mask65, mask35, mask46, mask90]),
    (1, mask132, [mask132, mask26, mask70, mask65, mask35, mask46, mask90])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch6Part4_dead : branch6Part4.any (evaluateN 7) = false := by
  decide +kernel

def branch6Part5 : List SearchNode :=
  [(0, mask132, [mask132, mask115, mask26, mask70, mask65, mask35, mask46, mask90]),
    (1, mask105, [mask105, mask46, mask70, mask65, mask35, mask115, mask26]),
    (0, mask105, [mask105, mask46, mask90, mask70, mask65, mask35, mask115, mask26]),
    (0, mask98, [mask98, mask90, mask26, mask70, mask65, mask35, mask115, mask46])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch6Part5_dead : branch6Part5.any (evaluateN 7) = false := by
  decide +kernel

def branch6Next : List SearchNode :=
  branch6Part0 ++ branch6Part1 ++ branch6Part2 ++ branch6Part3 ++ branch6Part4 ++ branch6Part5

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch6Next_dead : branch6Next.any (evaluateN 7) = false := by
  simp only [branch6Next, List.any_append, List.any_cons, List.any_nil, branch6Part0_dead, branch6Part1_dead, branch6Part2_dead, branch6Part3_dead, branch6Part4_dead, branch6Part5_dead, Bool.or_false, Bool.false_or]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch6_front : frontierN branch6 = branch6Next := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch6_dead : evaluateN 8 branch6 = false := by
  rw [evaluateN_step 5, branch6_front, branch6Next_dead, Bool.or_false]
  rfl

def branch7Part0 : List SearchNode :=
  [(0, mask19, [mask19, mask35, mask14, mask65, mask115, mask46, mask90, mask26]),
    (0, mask80, [mask80, mask35, mask14, mask65, mask115, mask46, mask90, mask26]),
    (0, mask63, [mask63, mask115, mask14, mask65, mask35, mask46, mask90, mask26]),
    (0, mask128, [mask128, mask115, mask14, mask65, mask35, mask46, mask90, mask26]),
    (0, mask8, [mask8, mask46, mask14, mask65, mask35, mask115, mask90, mask26]),
    (0, mask86, [mask86, mask46, mask14, mask65, mask35, mask115, mask90, mask26]),
    (0, mask10, [mask10, mask90, mask14, mask65, mask35, mask115, mask46, mask26]),
    (0, mask112, [mask112, mask90, mask14, mask65, mask35, mask115, mask46, mask26]),
    (0, mask12, [mask12, mask26, mask14, mask65, mask35, mask115, mask46, mask90]),
    (0, mask76, [mask76, mask26, mask14, mask65, mask35, mask115, mask46, mask90]),
    (0, mask121, [mask121, mask115, mask70, mask65, mask35, mask46, mask90, mask26]),
    (0, mask94, [mask94, mask90, mask70, mask65, mask35, mask115, mask46, mask26])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch7Part0_dead : branch7Part0.any (evaluateN 7) = false := by
  decide +kernel

def branch7Part1 : List SearchNode :=
  [(0, mask78, [mask78, mask35, mask70, mask14, mask115, mask46, mask90, mask26]),
    (0, mask127, [mask127, mask115, mask70, mask14, mask35, mask46, mask90, mask26]),
    (0, mask84, [mask84, mask46, mask70, mask14, mask35, mask115, mask90, mask26]),
    (0, mask111, [mask111, mask90, mask70, mask14, mask35, mask115, mask46, mask26]),
    (0, mask75, [mask75, mask26, mask70, mask14, mask35, mask115, mask46, mask90]),
    (1, mask100, [mask100, mask70, mask14, mask65, mask115, mask46, mask26]),
    (0, mask100, [mask100, mask35, mask70, mask14, mask65, mask115, mask46, mask26]),
    (0, mask100, [mask100, mask90, mask70, mask14, mask65, mask115, mask46, mask26]),
    (1, mask132, [mask132, mask70, mask14, mask65, mask35, mask46, mask90]),
    (0, mask132, [mask132, mask115, mask70, mask14, mask65, mask35, mask46, mask90]),
    (0, mask132, [mask132, mask26, mask70, mask14, mask65, mask35, mask46, mask90]),
    (0, mask105, [mask105, mask46, mask70, mask14, mask65, mask35, mask115, mask26])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch7Part1_dead : branch7Part1.any (evaluateN 7) = false := by
  decide +kernel

def branch7Next : List SearchNode :=
  branch7Part0 ++ branch7Part1

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch7Next_dead : branch7Next.any (evaluateN 7) = false := by
  simp only [branch7Next, List.any_append, List.any_cons, List.any_nil, branch7Part0_dead, branch7Part1_dead, Bool.or_false, Bool.false_or]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch7_front : frontierN branch7 = branch7Next := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch7_dead : evaluateN 8 branch7 = false := by
  rw [evaluateN_step 5, branch7_front, branch7Next_dead, Bool.or_false]
  rfl

def branch8Part0 : List SearchNode :=
  [(1, mask38, [mask38, mask14, mask90, mask115, mask46, mask65, mask26]),
    (0, mask38, [mask38, mask10, mask14, mask90, mask115, mask46, mask65, mask26]),
    (0, mask38, [mask38, mask35, mask14, mask90, mask115, mask46, mask65, mask26]),
    (1, mask118, [mask118, mask14, mask90, mask35, mask46, mask65, mask26]),
    (0, mask118, [mask118, mask10, mask14, mask90, mask35, mask46, mask65, mask26]),
    (0, mask118, [mask118, mask115, mask14, mask90, mask35, mask46, mask65, mask26]),
    (1, mask48, [mask48, mask14, mask90, mask35, mask115, mask65, mask26]),
    (0, mask48, [mask48, mask10, mask14, mask90, mask35, mask115, mask65, mask26]),
    (0, mask48, [mask48, mask46, mask14, mask90, mask35, mask115, mask65, mask26]),
    (1, mask68, [mask68, mask14, mask90, mask35, mask115, mask46, mask26]),
    (0, mask68, [mask68, mask10, mask14, mask90, mask35, mask115, mask46, mask26])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch8Part0_dead : branch8Part0.any (evaluateN 7) = false := by
  decide +kernel

def branch8Part1 : List SearchNode :=
  [(0, mask68, [mask68, mask65, mask14, mask90, mask35, mask115, mask46, mask26]),
    (1, mask29, [mask29, mask14, mask90, mask35, mask115, mask46, mask65]),
    (0, mask29, [mask29, mask10, mask14, mask90, mask35, mask115, mask46, mask65]),
    (0, mask29, [mask29, mask26, mask14, mask90, mask35, mask115, mask46, mask65]),
    (1, mask94, [mask94, mask10, mask35, mask115, mask46, mask65, mask26]),
    (0, mask94, [mask94, mask14, mask10, mask35, mask115, mask46, mask65, mask26]),
    (0, mask94, [mask94, mask90, mask10, mask35, mask115, mask46, mask65, mask26]),
    (0, mask41, [mask41, mask35, mask10, mask90, mask115, mask46, mask65, mask26]),
    (1, mask70, [mask70, mask10, mask90, mask35, mask115, mask46, mask26]),
    (0, mask70, [mask70, mask14, mask10, mask90, mask35, mask115, mask46, mask26]),
    (0, mask70, [mask70, mask65, mask10, mask90, mask35, mask115, mask46, mask26]),
    (1, mask100, [mask100, mask10, mask14, mask115, mask46, mask65, mask26]),
    (0, mask100, [mask100, mask90, mask10, mask14, mask115, mask46, mask65, mask26])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch8Part1_dead : branch8Part1.any (evaluateN 7) = false := by
  decide +kernel

def branch8Part2 : List SearchNode :=
  [(0, mask100, [mask100, mask35, mask10, mask14, mask115, mask46, mask65, mask26]),
    (0, mask89, [mask89, mask115, mask10, mask14, mask35, mask46, mask65, mask26]),
    (0, mask105, [mask105, mask46, mask10, mask14, mask35, mask115, mask65, mask26]),
    (0, mask111, [mask111, mask65, mask10, mask14, mask35, mask115, mask46, mask26]),
    (1, mask132, [mask132, mask10, mask14, mask90, mask35, mask46, mask65]),
    (0, mask132, [mask132, mask115, mask10, mask14, mask90, mask35, mask46, mask65]),
    (0, mask132, [mask132, mask26, mask10, mask14, mask90, mask35, mask46, mask65]),
    (0, mask84, [mask84, mask46, mask10, mask14, mask90, mask35, mask115, mask26]),
    (0, mask55, [mask55, mask46, mask10, mask14, mask90, mask35, mask115, mask65])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch8Part2_dead : branch8Part2.any (evaluateN 7) = false := by
  decide +kernel

def branch8Next : List SearchNode :=
  branch8Part0 ++ branch8Part1 ++ branch8Part2

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch8Next_dead : branch8Next.any (evaluateN 7) = false := by
  simp only [branch8Next, List.any_append, List.any_cons, List.any_nil, branch8Part0_dead, branch8Part1_dead, branch8Part2_dead, Bool.or_false, Bool.false_or]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch8_front : frontierN branch8 = branch8Next := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch8_dead : evaluateN 8 branch8 = false := by
  rw [evaluateN_step 5, branch8_front, branch8Next_dead, Bool.or_false]
  rfl

def branch9Part0 : List SearchNode :=
  [(1, mask39, [mask39, mask14, mask26, mask115, mask46, mask65, mask90]),
    (0, mask39, [mask39, mask12, mask14, mask26, mask115, mask46, mask65, mask90]),
    (0, mask39, [mask39, mask35, mask14, mask26, mask115, mask46, mask65, mask90]),
    (1, mask120, [mask120, mask14, mask26, mask35, mask46, mask65, mask90]),
    (0, mask120, [mask120, mask12, mask14, mask26, mask35, mask46, mask65, mask90]),
    (0, mask120, [mask120, mask115, mask14, mask26, mask35, mask46, mask65, mask90]),
    (1, mask49, [mask49, mask14, mask26, mask35, mask115, mask65, mask90]),
    (0, mask49, [mask49, mask12, mask14, mask26, mask35, mask115, mask65, mask90]),
    (0, mask49, [mask49, mask46, mask14, mask26, mask35, mask115, mask65, mask90]),
    (1, mask69, [mask69, mask14, mask26, mask35, mask115, mask46, mask90]),
    (0, mask69, [mask69, mask12, mask14, mask26, mask35, mask115, mask46, mask90]),
    (0, mask69, [mask69, mask65, mask14, mask26, mask35, mask115, mask46, mask90])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch9Part0_dead : branch9Part0.any (evaluateN 7) = false := by
  decide +kernel

def branch9Part1 : List SearchNode :=
  [(1, mask93, [mask93, mask14, mask26, mask35, mask115, mask46, mask65]),
    (0, mask93, [mask93, mask12, mask14, mask26, mask35, mask115, mask46, mask65]),
    (0, mask93, [mask93, mask90, mask14, mask26, mask35, mask115, mask46, mask65]),
    (1, mask31, [mask31, mask12, mask35, mask115, mask46, mask65, mask90]),
    (0, mask31, [mask31, mask14, mask12, mask35, mask115, mask46, mask65, mask90]),
    (0, mask31, [mask31, mask26, mask12, mask35, mask115, mask46, mask65, mask90]),
    (0, mask121, [mask121, mask115, mask12, mask26, mask35, mask46, mask65, mask90]),
    (1, mask70, [mask70, mask12, mask26, mask35, mask115, mask46, mask90]),
    (0, mask70, [mask70, mask14, mask12, mask26, mask35, mask115, mask46, mask90]),
    (0, mask70, [mask70, mask65, mask12, mask26, mask35, mask115, mask46, mask90])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch9Part1_dead : branch9Part1.any (evaluateN 7) = false := by
  decide +kernel

def branch9Part2 : List SearchNode :=
  [(0, mask24, [mask24, mask35, mask12, mask14, mask115, mask46, mask65, mask90]),
    (1, mask132, [mask132, mask12, mask14, mask35, mask46, mask65, mask90]),
    (0, mask132, [mask132, mask26, mask12, mask14, mask35, mask46, mask65, mask90]),
    (0, mask132, [mask132, mask115, mask12, mask14, mask35, mask46, mask65, mask90]),
    (0, mask55, [mask55, mask46, mask12, mask14, mask35, mask115, mask65, mask90]),
    (0, mask75, [mask75, mask65, mask12, mask14, mask35, mask115, mask46, mask90]),
    (1, mask100, [mask100, mask12, mask14, mask26, mask115, mask46, mask65]),
    (0, mask100, [mask100, mask35, mask12, mask14, mask26, mask115, mask46, mask65]),
    (0, mask100, [mask100, mask90, mask12, mask14, mask26, mask115, mask46, mask65]),
    (0, mask84, [mask84, mask46, mask12, mask14, mask26, mask35, mask115, mask90]),
    (0, mask105, [mask105, mask46, mask12, mask14, mask26, mask35, mask115, mask65])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch9Part2_dead : branch9Part2.any (evaluateN 7) = false := by
  decide +kernel

def branch9Next : List SearchNode :=
  branch9Part0 ++ branch9Part1 ++ branch9Part2

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch9Next_dead : branch9Next.any (evaluateN 7) = false := by
  simp only [branch9Next, List.any_append, List.any_cons, List.any_nil, branch9Part0_dead, branch9Part1_dead, branch9Part2_dead, Bool.or_false, Bool.false_or]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch9_front : frontierN branch9 = branch9Next := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch9_dead : evaluateN 8 branch9 = false := by
  rw [evaluateN_step 5, branch9_front, branch9Next_dead, Bool.or_false]
  rfl

def branch10Part0 : List SearchNode :=
  [(0, mask24, [mask24, mask35, mask14, mask26, mask115, mask46, mask65, mask90]),
    (0, mask42, [mask42, mask35, mask14, mask26, mask115, mask46, mask65, mask90]),
    (0, mask2, [mask2, mask115, mask14, mask26, mask35, mask46, mask65, mask90]),
    (0, mask134, [mask134, mask115, mask14, mask26, mask35, mask46, mask65, mask90]),
    (0, mask8, [mask8, mask46, mask14, mask26, mask35, mask115, mask65, mask90]),
    (0, mask57, [mask57, mask46, mask14, mask26, mask35, mask115, mask65, mask90]),
    (0, mask0, [mask0, mask65, mask14, mask26, mask35, mask115, mask46, mask90]),
    (0, mask76, [mask76, mask65, mask14, mask26, mask35, mask115, mask46, mask90]),
    (0, mask10, [mask10, mask90, mask14, mask26, mask35, mask115, mask46, mask65]),
    (0, mask99, [mask99, mask90, mask14, mask26, mask35, mask115, mask46, mask65]),
    (0, mask41, [mask41, mask35, mask31, mask26, mask115, mask46, mask65, mask90]),
    (0, mask50, [mask50, mask46, mask31, mask26, mask35, mask115, mask65, mask90]),
    (1, mask70, [mask70, mask31, mask26, mask35, mask115, mask46, mask90]),
    (0, mask70, [mask70, mask14, mask31, mask26, mask35, mask115, mask46, mask90])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch10Part0_dead : branch10Part0.any (evaluateN 7) = false := by
  decide +kernel

def branch10Part1 : List SearchNode :=
  [(0, mask70, [mask70, mask65, mask31, mask26, mask35, mask115, mask46, mask90]),
    (0, mask94, [mask94, mask90, mask31, mask26, mask35, mask115, mask46, mask65]),
    (0, mask40, [mask40, mask35, mask31, mask14, mask115, mask46, mask65, mask90]),
    (1, mask132, [mask132, mask31, mask14, mask35, mask46, mask65, mask90]),
    (0, mask132, [mask132, mask26, mask31, mask14, mask35, mask46, mask65, mask90]),
    (0, mask132, [mask132, mask115, mask31, mask14, mask35, mask46, mask65, mask90]),
    (0, mask55, [mask55, mask46, mask31, mask14, mask35, mask115, mask65, mask90]),
    (0, mask98, [mask98, mask90, mask31, mask14, mask35, mask115, mask46, mask65]),
    (1, mask100, [mask100, mask31, mask14, mask26, mask115, mask46, mask65]),
    (0, mask100, [mask100, mask35, mask31, mask14, mask26, mask115, mask46, mask65]),
    (0, mask100, [mask100, mask90, mask31, mask14, mask26, mask115, mask46, mask65]),
    (0, mask84, [mask84, mask46, mask31, mask14, mask26, mask35, mask115, mask90]),
    (0, mask105, [mask105, mask46, mask31, mask14, mask26, mask35, mask115, mask65])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch10Part1_dead : branch10Part1.any (evaluateN 7) = false := by
  decide +kernel

def branch10Next : List SearchNode :=
  branch10Part0 ++ branch10Part1

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch10Next_dead : branch10Next.any (evaluateN 7) = false := by
  simp only [branch10Next, List.any_append, List.any_cons, List.any_nil, branch10Part0_dead, branch10Part1_dead, Bool.or_false, Bool.false_or]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch10_front : frontierN branch10 = branch10Next := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch10_dead : evaluateN 8 branch10 = false := by
  rw [evaluateN_step 5, branch10_front, branch10Next_dead, Bool.or_false]
  rfl

def branch11Part0 : List SearchNode :=
  [(1, mask18, [mask18, mask35, mask46, mask115, mask65, mask90, mask26]),
    (0, mask18, [mask18, mask16, mask35, mask46, mask115, mask65, mask90, mask26]),
    (0, mask18, [mask18, mask14, mask35, mask46, mask115, mask65, mask90, mask26]),
    (1, mask122, [mask122, mask35, mask46, mask14, mask65, mask90, mask26]),
    (0, mask122, [mask122, mask16, mask35, mask46, mask14, mask65, mask90, mask26]),
    (0, mask122, [mask122, mask115, mask35, mask46, mask14, mask65, mask90, mask26]),
    (1, mask72, [mask72, mask35, mask46, mask14, mask115, mask90, mask26])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch11Part0_dead : branch11Part0.any (evaluateN 7) = false := by
  decide +kernel

def branch11Part1 : List SearchNode :=
  [(0, mask72, [mask72, mask16, mask35, mask46, mask14, mask115, mask90, mask26]),
    (0, mask72, [mask72, mask65, mask35, mask46, mask14, mask115, mask90, mask26]),
    (1, mask95, [mask95, mask35, mask46, mask14, mask115, mask65, mask26]),
    (0, mask95, [mask95, mask16, mask35, mask46, mask14, mask115, mask65, mask26]),
    (0, mask95, [mask95, mask90, mask35, mask46, mask14, mask115, mask65, mask26]),
    (1, mask33, [mask33, mask35, mask46, mask14, mask115, mask65, mask90]),
    (0, mask33, [mask33, mask16, mask35, mask46, mask14, mask115, mask65, mask90]),
    (0, mask33, [mask33, mask26, mask35, mask46, mask14, mask115, mask65, mask90])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch11Part1_dead : branch11Part1.any (evaluateN 7) = false := by
  decide +kernel

def branch11Part2 : List SearchNode :=
  [(1, mask59, [mask59, mask16, mask14, mask115, mask65, mask90, mask26]),
    (0, mask59, [mask59, mask35, mask16, mask14, mask115, mask65, mask90, mask26]),
    (0, mask59, [mask59, mask46, mask16, mask14, mask115, mask65, mask90, mask26]),
    (1, mask100, [mask100, mask16, mask46, mask14, mask115, mask65, mask26]),
    (0, mask100, [mask100, mask35, mask16, mask46, mask14, mask115, mask65, mask26]),
    (0, mask100, [mask100, mask90, mask16, mask46, mask14, mask115, mask65, mask26]),
    (0, mask84, [mask84, mask46, mask16, mask35, mask14, mask115, mask90, mask26]),
    (1, mask105, [mask105, mask16, mask35, mask14, mask115, mask65, mask26]),
    (0, mask105, [mask105, mask46, mask16, mask35, mask14, mask115, mask65, mask26]),
    (0, mask105, [mask105, mask90, mask16, mask35, mask14, mask115, mask65, mask26])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch11Part2_dead : branch11Part2.any (evaluateN 7) = false := by
  decide +kernel

def branch11Part3 : List SearchNode :=
  [(0, mask55, [mask55, mask46, mask16, mask35, mask14, mask115, mask65, mask90]),
    (1, mask70, [mask70, mask16, mask35, mask46, mask115, mask90, mask26]),
    (0, mask70, [mask70, mask14, mask16, mask35, mask46, mask115, mask90, mask26]),
    (0, mask70, [mask70, mask65, mask16, mask35, mask46, mask115, mask90, mask26]),
    (1, mask132, [mask132, mask16, mask35, mask46, mask14, mask65, mask90]),
    (0, mask132, [mask132, mask115, mask16, mask35, mask46, mask14, mask65, mask90]),
    (0, mask132, [mask132, mask26, mask16, mask35, mask46, mask14, mask65, mask90])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch11Part3_dead : branch11Part3.any (evaluateN 7) = false := by
  decide +kernel

def branch11Next : List SearchNode :=
  branch11Part0 ++ branch11Part1 ++ branch11Part2 ++ branch11Part3

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch11Next_dead : branch11Next.any (evaluateN 7) = false := by
  simp only [branch11Next, List.any_append, List.any_cons, List.any_nil, branch11Part0_dead, branch11Part1_dead, branch11Part2_dead, branch11Part3_dead, Bool.or_false, Bool.false_or]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch11_front : frontierN branch11 = branch11Next := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch11_dead : evaluateN 8 branch11 = false := by
  rw [evaluateN_step 5, branch11_front, branch11Next_dead, Bool.or_false]
  rfl

def branch12Part0 : List SearchNode :=
  [(0, mask8, [mask8, mask14, mask35, mask46, mask115, mask65, mask90, mask26]),
    (0, mask62, [mask62, mask14, mask35, mask46, mask115, mask65, mask90, mask26]),
    (0, mask43, [mask43, mask115, mask35, mask46, mask14, mask65, mask90, mask26]),
    (0, mask138, [mask138, mask115, mask35, mask46, mask14, mask65, mask90, mask26]),
    (0, mask19, [mask19, mask65, mask35, mask46, mask14, mask115, mask90, mask26]),
    (0, mask87, [mask87, mask65, mask35, mask46, mask14, mask115, mask90, mask26]),
    (0, mask1, [mask1, mask90, mask35, mask46, mask14, mask115, mask65, mask26]),
    (1, mask109, [mask109, mask35, mask46, mask14, mask115, mask65, mask26]),
    (0, mask109, [mask109, mask59, mask35, mask46, mask14, mask115, mask65, mask26]),
    (0, mask109, [mask109, mask90, mask35, mask46, mask14, mask115, mask65, mask26]),
    (0, mask24, [mask24, mask26, mask35, mask46, mask14, mask115, mask65, mask90])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch12Part0_dead : branch12Part0.any (evaluateN 7) = false := by
  decide +kernel

def branch12Part1 : List SearchNode :=
  [(0, mask61, [mask61, mask26, mask35, mask46, mask14, mask115, mask65, mask90]),
    (0, mask137, [mask137, mask115, mask59, mask46, mask14, mask65, mask90, mask26]),
    (0, mask78, [mask78, mask65, mask59, mask46, mask14, mask115, mask90, mask26]),
    (1, mask100, [mask100, mask59, mask46, mask14, mask115, mask65, mask26]),
    (0, mask100, [mask100, mask35, mask59, mask46, mask14, mask115, mask65, mask26]),
    (0, mask100, [mask100, mask90, mask59, mask46, mask14, mask115, mask65, mask26]),
    (0, mask123, [mask123, mask115, mask59, mask35, mask14, mask65, mask90, mask26]),
    (1, mask84, [mask84, mask59, mask35, mask14, mask115, mask90, mask26]),
    (0, mask84, [mask84, mask46, mask59, mask35, mask14, mask115, mask90, mask26]),
    (0, mask84, [mask84, mask65, mask59, mask35, mask14, mask115, mask90, mask26]),
    (0, mask105, [mask105, mask46, mask59, mask35, mask14, mask115, mask65, mask26])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch12Part1_dead : branch12Part1.any (evaluateN 7) = false := by
  decide +kernel

def branch12Part2 : List SearchNode :=
  [(1, mask70, [mask70, mask59, mask35, mask46, mask115, mask90, mask26]),
    (0, mask70, [mask70, mask14, mask59, mask35, mask46, mask115, mask90, mask26]),
    (0, mask70, [mask70, mask65, mask59, mask35, mask46, mask115, mask90, mask26]),
    (1, mask132, [mask132, mask59, mask35, mask46, mask14, mask65, mask90]),
    (0, mask132, [mask132, mask115, mask59, mask35, mask46, mask14, mask65, mask90]),
    (0, mask132, [mask132, mask26, mask59, mask35, mask46, mask14, mask65, mask90])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch12Part2_dead : branch12Part2.any (evaluateN 7) = false := by
  decide +kernel

def branch12Next : List SearchNode :=
  branch12Part0 ++ branch12Part1 ++ branch12Part2

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch12Next_dead : branch12Next.any (evaluateN 7) = false := by
  simp only [branch12Next, List.any_append, List.any_cons, List.any_nil, branch12Part0_dead, branch12Part1_dead, branch12Part2_dead, Bool.or_false, Bool.false_or]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch12_front : frontierN branch12 = branch12Next := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch12_dead : evaluateN 8 branch12 = false := by
  rw [evaluateN_step 5, branch12_front, branch12Next_dead, Bool.or_false]
  rfl

def branch13Part0 : List SearchNode :=
  [(1, mask22, [mask22, mask35, mask65, mask115, mask46, mask90, mask26]),
    (0, mask22, [mask22, mask19, mask35, mask65, mask115, mask46, mask90, mask26]),
    (0, mask22, [mask22, mask14, mask35, mask65, mask115, mask46, mask90, mask26]),
    (1, mask126, [mask126, mask35, mask65, mask14, mask46, mask90, mask26]),
    (0, mask126, [mask126, mask19, mask35, mask65, mask14, mask46, mask90, mask26]),
    (0, mask126, [mask126, mask115, mask35, mask65, mask14, mask46, mask90, mask26]),
    (1, mask52, [mask52, mask35, mask65, mask14, mask115, mask90, mask26]),
    (0, mask52, [mask52, mask19, mask35, mask65, mask14, mask115, mask90, mask26]),
    (0, mask52, [mask52, mask46, mask35, mask65, mask14, mask115, mask90, mask26]),
    (1, mask96, [mask96, mask35, mask65, mask14, mask115, mask46, mask26]),
    (0, mask96, [mask96, mask19, mask35, mask65, mask14, mask115, mask46, mask26]),
    (0, mask96, [mask96, mask90, mask35, mask65, mask14, mask115, mask46, mask26])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch13Part0_dead : branch13Part0.any (evaluateN 7) = false := by
  decide +kernel

def branch13Part1 : List SearchNode :=
  [(1, mask34, [mask34, mask35, mask65, mask14, mask115, mask46, mask90]),
    (0, mask34, [mask34, mask19, mask35, mask65, mask14, mask115, mask46, mask90]),
    (0, mask34, [mask34, mask26, mask35, mask65, mask14, mask115, mask46, mask90]),
    (1, mask78, [mask78, mask19, mask14, mask115, mask46, mask90, mask26]),
    (0, mask78, [mask78, mask35, mask19, mask14, mask115, mask46, mask90, mask26]),
    (0, mask78, [mask78, mask65, mask19, mask14, mask115, mask46, mask90, mask26]),
    (0, mask41, [mask41, mask14, mask19, mask65, mask115, mask46, mask90, mask26]),
    (1, mask100, [mask100, mask19, mask65, mask14, mask115, mask46, mask26]),
    (0, mask100, [mask100, mask35, mask19, mask65, mask14, mask115, mask46, mask26]),
    (0, mask100, [mask100, mask90, mask19, mask65, mask14, mask115, mask46, mask26]),
    (1, mask70, [mask70, mask19, mask35, mask115, mask46, mask90, mask26]),
    (0, mask70, [mask70, mask65, mask19, mask35, mask115, mask46, mask90, mask26])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch13Part1_dead : branch13Part1.any (evaluateN 7) = false := by
  decide +kernel

def branch13Part2 : List SearchNode :=
  [(0, mask70, [mask70, mask14, mask19, mask35, mask115, mask46, mask90, mask26]),
    (0, mask63, [mask63, mask115, mask19, mask35, mask14, mask46, mask90, mask26]),
    (0, mask84, [mask84, mask46, mask19, mask35, mask14, mask115, mask90, mask26]),
    (0, mask111, [mask111, mask90, mask19, mask35, mask14, mask115, mask46, mask26]),
    (1, mask132, [mask132, mask19, mask35, mask65, mask14, mask46, mask90]),
    (0, mask132, [mask132, mask115, mask19, mask35, mask65, mask14, mask46, mask90]),
    (0, mask132, [mask132, mask26, mask19, mask35, mask65, mask14, mask46, mask90]),
    (0, mask105, [mask105, mask46, mask19, mask35, mask65, mask14, mask115, mask26]),
    (0, mask55, [mask55, mask46, mask19, mask35, mask65, mask14, mask115, mask90])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch13Part2_dead : branch13Part2.any (evaluateN 7) = false := by
  decide +kernel

def branch13Next : List SearchNode :=
  branch13Part0 ++ branch13Part1 ++ branch13Part2

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch13Next_dead : branch13Next.any (evaluateN 7) = false := by
  simp only [branch13Next, List.any_append, List.any_cons, List.any_nil, branch13Part0_dead, branch13Part1_dead, branch13Part2_dead, Bool.or_false, Bool.false_or]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch13_front : frontierN branch13 = branch13Next := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch13_dead : evaluateN 8 branch13 = false := by
  rw [evaluateN_step 5, branch13_front, branch13Next_dead, Bool.or_false]
  rfl

def branch14Part0 : List SearchNode :=
  [(1, mask10, [mask10, mask100, mask14, mask115, mask46, mask65, mask26]),
    (1, mask103, [mask103, mask100, mask14, mask115, mask46, mask65, mask26])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch14Part0_dead : branch14Part0.any (evaluateN 7) = false := by
  decide +kernel

def branch14Part1 : List SearchNode :=
  [(1, mask89, [mask89, mask100, mask115, mask14, mask46, mask65, mask26]),
    (1, mask139, [mask139, mask100, mask115, mask14, mask46, mask65, mask26])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch14Part1_dead : branch14Part1.any (evaluateN 7) = false := by
  decide +kernel

def branch14Part2 : List SearchNode :=
  [(1, mask16, [mask16, mask100, mask46, mask14, mask115, mask65, mask26])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch14Part2_dead : branch14Part2.any (evaluateN 7) = false := by
  decide +kernel

def branch14Part3 : List SearchNode :=
  [(1, mask109, [mask109, mask100, mask46, mask14, mask115, mask65, mask26]),
    (1, mask19, [mask19, mask100, mask65, mask14, mask115, mask46, mask26])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch14Part3_dead : branch14Part3.any (evaluateN 7) = false := by
  decide +kernel

def branch14Part4 : List SearchNode :=
  [(1, mask113, [mask113, mask100, mask65, mask14, mask115, mask46, mask26]),
    (1, mask24, [mask24, mask100, mask26, mask14, mask115, mask46, mask65]),
    (1, mask102, [mask102, mask100, mask26, mask14, mask115, mask46, mask65])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch14Part4_dead : branch14Part4.any (evaluateN 7) = false := by
  decide +kernel

def branch14Part5 : List SearchNode :=
  [(1, mask121, [mask121, mask14, mask115, mask100, mask46, mask65, mask26]),
    (1, mask123, [mask123, mask115, mask46, mask100, mask14, mask65, mask26]),
    (1, mask127, [mask127, mask115, mask65, mask100, mask14, mask46, mask26])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch14Part5_dead : branch14Part5.any (evaluateN 7) = false := by
  decide +kernel

def branch14Part6 : List SearchNode :=
  [(3, mask132, [mask132, mask100, mask14, mask46, mask65])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch14Part6_dead : branch14Part6.any (evaluateN 7) = false := by
  decide +kernel

def branch14Part7 : List SearchNode :=
  [(2, mask132, [mask132, mask115, mask100, mask14, mask46, mask65]),
    (2, mask132, [mask132, mask26, mask100, mask14, mask46, mask65]),
    (1, mask132, [mask132, mask115, mask26, mask100, mask14, mask46, mask65])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch14Part7_dead : branch14Part7.any (evaluateN 7) = false := by
  decide +kernel

def branch14Next : List SearchNode :=
  branch14Part0 ++ branch14Part1 ++ branch14Part2 ++ branch14Part3 ++ branch14Part4 ++ branch14Part5 ++ branch14Part6 ++ branch14Part7

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch14Next_dead : branch14Next.any (evaluateN 7) = false := by
  simp only [branch14Next, List.any_append, List.any_cons, List.any_nil, branch14Part0_dead, branch14Part1_dead, branch14Part2_dead, branch14Part3_dead, branch14Part4_dead, branch14Part5_dead, branch14Part6_dead, branch14Part7_dead, Bool.or_false, Bool.false_or]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch14_front : frontierN branch14 = branch14Next := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch14_dead : evaluateN 8 branch14 = false := by
  rw [evaluateN_step 5, branch14_front, branch14Next_dead, Bool.or_false]
  rfl

def branch15Part0 : List SearchNode :=
  [(0, mask10, [mask10, mask100, mask14, mask35, mask115, mask46, mask65, mask26]),
    (0, mask103, [mask103, mask100, mask14, mask35, mask115, mask46, mask65, mask26]),
    (0, mask89, [mask89, mask100, mask115, mask35, mask14, mask46, mask65, mask26]),
    (0, mask139, [mask139, mask100, mask115, mask35, mask14, mask46, mask65, mask26]),
    (0, mask16, [mask16, mask100, mask46, mask35, mask14, mask115, mask65, mask26]),
    (1, mask109, [mask109, mask46, mask35, mask14, mask115, mask65, mask26]),
    (0, mask109, [mask109, mask100, mask46, mask35, mask14, mask115, mask65, mask26]),
    (0, mask19, [mask19, mask100, mask65, mask35, mask14, mask115, mask46, mask26]),
    (0, mask113, [mask113, mask100, mask65, mask35, mask14, mask115, mask46, mask26]),
    (0, mask24, [mask24, mask100, mask26, mask35, mask14, mask115, mask46, mask65]),
    (0, mask102, [mask102, mask100, mask26, mask35, mask14, mask115, mask46, mask65]),
    (1, mask137, [mask137, mask115, mask100, mask14, mask46, mask65, mask26])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch15Part0_dead : branch15Part0.any (evaluateN 7) = false := by
  decide +kernel

def branch15Part1 : List SearchNode :=
  [(0, mask137, [mask137, mask35, mask115, mask100, mask14, mask46, mask65, mask26]),
    (0, mask121, [mask121, mask14, mask115, mask100, mask35, mask46, mask65, mask26]),
    (0, mask123, [mask123, mask115, mask46, mask100, mask35, mask14, mask65, mask26]),
    (0, mask127, [mask127, mask115, mask65, mask100, mask35, mask14, mask46, mask26]),
    (2, mask132, [mask132, mask100, mask35, mask14, mask46, mask65]),
    (1, mask132, [mask132, mask115, mask100, mask35, mask14, mask46, mask65]),
    (1, mask132, [mask132, mask26, mask100, mask35, mask14, mask46, mask65])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch15Part1_dead : branch15Part1.any (evaluateN 7) = false := by
  decide +kernel

def branch15Part2 : List SearchNode :=
  [(0, mask132, [mask132, mask115, mask26, mask100, mask35, mask14, mask46, mask65])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch15Part2_dead : branch15Part2.any (evaluateN 7) = false := by
  decide +kernel

def branch15Next : List SearchNode :=
  branch15Part0 ++ branch15Part1 ++ branch15Part2

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch15Next_dead : branch15Next.any (evaluateN 7) = false := by
  simp only [branch15Next, List.any_append, List.any_cons, List.any_nil, branch15Part0_dead, branch15Part1_dead, branch15Part2_dead, Bool.or_false, Bool.false_or]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch15_front : frontierN branch15 = branch15Next := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch15_dead : evaluateN 8 branch15 = false := by
  rw [evaluateN_step 5, branch15_front, branch15Next_dead, Bool.or_false]
  rfl

def branch16Part0 : List SearchNode :=
  [(0, mask10, [mask10, mask100, mask14, mask90, mask115, mask46, mask65, mask26]),
    (0, mask103, [mask103, mask100, mask14, mask90, mask115, mask46, mask65, mask26]),
    (0, mask89, [mask89, mask100, mask115, mask90, mask14, mask46, mask65, mask26]),
    (0, mask139, [mask139, mask100, mask115, mask90, mask14, mask46, mask65, mask26]),
    (0, mask16, [mask16, mask100, mask46, mask90, mask14, mask115, mask65, mask26]),
    (0, mask109, [mask109, mask100, mask46, mask90, mask14, mask115, mask65, mask26]),
    (0, mask19, [mask19, mask100, mask65, mask90, mask14, mask115, mask46, mask26]),
    (0, mask113, [mask113, mask100, mask65, mask90, mask14, mask115, mask46, mask26]),
    (0, mask24, [mask24, mask100, mask26, mask90, mask14, mask115, mask46, mask65]),
    (0, mask102, [mask102, mask100, mask26, mask90, mask14, mask115, mask46, mask65]),
    (1, mask119, [mask119, mask115, mask100, mask14, mask46, mask65, mask26]),
    (0, mask119, [mask119, mask90, mask115, mask100, mask14, mask46, mask65, mask26])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch16Part0_dead : branch16Part0.any (evaluateN 7) = false := by
  decide +kernel

def branch16Part1 : List SearchNode :=
  [(1, mask105, [mask105, mask46, mask100, mask14, mask115, mask65, mask26]),
    (0, mask105, [mask105, mask90, mask46, mask100, mask14, mask115, mask65, mask26]),
    (1, mask111, [mask111, mask65, mask100, mask14, mask115, mask46, mask26]),
    (0, mask111, [mask111, mask90, mask65, mask100, mask14, mask115, mask46, mask26]),
    (0, mask121, [mask121, mask14, mask115, mask100, mask90, mask46, mask65, mask26]),
    (0, mask123, [mask123, mask115, mask46, mask100, mask90, mask14, mask65, mask26]),
    (0, mask127, [mask127, mask115, mask65, mask100, mask90, mask14, mask46, mask26]),
    (2, mask132, [mask132, mask100, mask90, mask14, mask46, mask65]),
    (1, mask132, [mask132, mask115, mask100, mask90, mask14, mask46, mask65]),
    (1, mask132, [mask132, mask26, mask100, mask90, mask14, mask46, mask65]),
    (0, mask132, [mask132, mask115, mask26, mask100, mask90, mask14, mask46, mask65])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch16Part1_dead : branch16Part1.any (evaluateN 7) = false := by
  decide +kernel

def branch16Next : List SearchNode :=
  branch16Part0 ++ branch16Part1

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch16Next_dead : branch16Next.any (evaluateN 7) = false := by
  simp only [branch16Next, List.any_append, List.any_cons, List.any_nil, branch16Part0_dead, branch16Part1_dead, Bool.or_false, Bool.false_or]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch16_front : frontierN branch16 = branch16Next := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch16_dead : evaluateN 8 branch16 = false := by
  rw [evaluateN_step 5, branch16_front, branch16Next_dead, Bool.or_false]
  rfl

def branch17Part0 : List SearchNode :=
  [(1, mask30, [mask30, mask35, mask26, mask115, mask46, mask65, mask90]),
    (0, mask30, [mask30, mask24, mask35, mask26, mask115, mask46, mask65, mask90]),
    (0, mask30, [mask30, mask14, mask35, mask26, mask115, mask46, mask65, mask90]),
    (1, mask131, [mask131, mask35, mask26, mask14, mask46, mask65, mask90]),
    (0, mask131, [mask131, mask24, mask35, mask26, mask14, mask46, mask65, mask90]),
    (0, mask131, [mask131, mask115, mask35, mask26, mask14, mask46, mask65, mask90]),
    (1, mask54, [mask54, mask35, mask26, mask14, mask115, mask65, mask90]),
    (0, mask54, [mask54, mask24, mask35, mask26, mask14, mask115, mask65, mask90]),
    (0, mask54, [mask54, mask46, mask35, mask26, mask14, mask115, mask65, mask90]),
    (1, mask74, [mask74, mask35, mask26, mask14, mask115, mask46, mask90])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch17Part0_dead : branch17Part0.any (evaluateN 7) = false := by
  decide +kernel

def branch17Part1 : List SearchNode :=
  [(0, mask74, [mask74, mask24, mask35, mask26, mask14, mask115, mask46, mask90]),
    (0, mask74, [mask74, mask65, mask35, mask26, mask14, mask115, mask46, mask90]),
    (1, mask97, [mask97, mask35, mask26, mask14, mask115, mask46, mask65]),
    (0, mask97, [mask97, mask24, mask35, mask26, mask14, mask115, mask46, mask65]),
    (0, mask97, [mask97, mask90, mask35, mask26, mask14, mask115, mask46, mask65]),
    (1, mask40, [mask40, mask24, mask14, mask115, mask46, mask65, mask90]),
    (0, mask40, [mask40, mask35, mask24, mask14, mask115, mask46, mask65, mask90]),
    (0, mask40, [mask40, mask26, mask24, mask14, mask115, mask46, mask65, mask90]),
    (0, mask137, [mask137, mask115, mask24, mask26, mask14, mask46, mask65, mask90]),
    (1, mask100, [mask100, mask24, mask26, mask14, mask115, mask46, mask65]),
    (0, mask100, [mask100, mask35, mask24, mask26, mask14, mask115, mask46, mask65]),
    (0, mask100, [mask100, mask90, mask24, mask26, mask14, mask115, mask46, mask65]),
    (1, mask132, [mask132, mask24, mask35, mask14, mask46, mask65, mask90]),
    (0, mask132, [mask132, mask26, mask24, mask35, mask14, mask46, mask65, mask90]),
    (0, mask132, [mask132, mask115, mask24, mask35, mask14, mask46, mask65, mask90]),
    (0, mask55, [mask55, mask46, mask24, mask35, mask14, mask115, mask65, mask90]),
    (0, mask98, [mask98, mask90, mask24, mask35, mask14, mask115, mask46, mask65]),
    (1, mask70, [mask70, mask24, mask35, mask26, mask115, mask46, mask90])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch17Part1_dead : branch17Part1.any (evaluateN 7) = false := by
  decide +kernel

def branch17Part2 : List SearchNode :=
  [(0, mask70, [mask70, mask14, mask24, mask35, mask26, mask115, mask46, mask90]),
    (0, mask70, [mask70, mask65, mask24, mask35, mask26, mask115, mask46, mask90]),
    (0, mask84, [mask84, mask46, mask24, mask35, mask26, mask14, mask115, mask90]),
    (0, mask105, [mask105, mask46, mask24, mask35, mask26, mask14, mask115, mask65])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch17Part2_dead : branch17Part2.any (evaluateN 7) = false := by
  decide +kernel

def branch17Next : List SearchNode :=
  branch17Part0 ++ branch17Part1 ++ branch17Part2

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch17Next_dead : branch17Next.any (evaluateN 7) = false := by
  simp only [branch17Next, List.any_append, List.any_cons, List.any_nil, branch17Part0_dead, branch17Part1_dead, branch17Part2_dead, Bool.or_false, Bool.false_or]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch17_front : frontierN branch17 = branch17Next := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch17_dead : evaluateN 8 branch17 = false := by
  rw [evaluateN_step 5, branch17_front, branch17Next_dead, Bool.or_false]
  rfl

def branch18Part0 : List SearchNode :=
  [(0, mask12, [mask12, mask14, mask35, mask26, mask115, mask46, mask65, mask90]),
    (0, mask42, [mask42, mask14, mask35, mask26, mask115, mask46, mask65, mask90]),
    (0, mask2, [mask2, mask115, mask35, mask26, mask14, mask46, mask65, mask90]),
    (0, mask140, [mask140, mask115, mask35, mask26, mask14, mask46, mask65, mask90]),
    (0, mask16, [mask16, mask46, mask35, mask26, mask14, mask115, mask65, mask90]),
    (0, mask61, [mask61, mask46, mask35, mask26, mask14, mask115, mask65, mask90]),
    (0, mask19, [mask19, mask65, mask35, mask26, mask14, mask115, mask46, mask90]),
    (0, mask79, [mask79, mask65, mask35, mask26, mask14, mask115, mask46, mask90]),
    (0, mask1, [mask1, mask90, mask35, mask26, mask14, mask115, mask46, mask65]),
    (0, mask102, [mask102, mask90, mask35, mask26, mask14, mask115, mask46, mask65]),
    (0, mask41, [mask41, mask14, mask40, mask26, mask115, mask46, mask65, mask90]),
    (0, mask59, [mask59, mask46, mask40, mask26, mask14, mask115, mask65, mask90]),
    (0, mask78, [mask78, mask65, mask40, mask26, mask14, mask115, mask46, mask90]),
    (1, mask100, [mask100, mask40, mask26, mask14, mask115, mask46, mask65]),
    (0, mask100, [mask100, mask35, mask40, mask26, mask14, mask115, mask46, mask65]),
    (0, mask100, [mask100, mask90, mask40, mask26, mask14, mask115, mask46, mask65])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch18Part0_dead : branch18Part0.any (evaluateN 7) = false := by
  decide +kernel

def branch18Part1 : List SearchNode :=
  [(1, mask132, [mask132, mask40, mask35, mask14, mask46, mask65, mask90]),
    (0, mask132, [mask132, mask26, mask40, mask35, mask14, mask46, mask65, mask90]),
    (0, mask132, [mask132, mask115, mask40, mask35, mask14, mask46, mask65, mask90]),
    (0, mask55, [mask55, mask46, mask40, mask35, mask14, mask115, mask65, mask90]),
    (0, mask75, [mask75, mask65, mask40, mask35, mask14, mask115, mask46, mask90]),
    (1, mask70, [mask70, mask40, mask35, mask26, mask115, mask46, mask90]),
    (0, mask70, [mask70, mask14, mask40, mask35, mask26, mask115, mask46, mask90]),
    (0, mask70, [mask70, mask65, mask40, mask35, mask26, mask115, mask46, mask90]),
    (0, mask84, [mask84, mask46, mask40, mask35, mask26, mask14, mask115, mask90]),
    (0, mask105, [mask105, mask46, mask40, mask35, mask26, mask14, mask115, mask65])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch18Part1_dead : branch18Part1.any (evaluateN 7) = false := by
  decide +kernel

def branch18Next : List SearchNode :=
  branch18Part0 ++ branch18Part1

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch18Next_dead : branch18Next.any (evaluateN 7) = false := by
  simp only [branch18Next, List.any_append, List.any_cons, List.any_nil, branch18Part0_dead, branch18Part1_dead, Bool.or_false, Bool.false_or]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch18_front : frontierN branch18 = branch18Next := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch18_dead : evaluateN 8 branch18 = false := by
  rw [evaluateN_step 5, branch18_front, branch18Next_dead, Bool.or_false]
  rfl

def branch19Part0 : List SearchNode :=
  [(1, mask45, [mask45, mask115, mask46, mask35, mask65, mask90, mask26]),
    (0, mask45, [mask45, mask43, mask115, mask46, mask35, mask65, mask90, mask26]),
    (0, mask45, [mask45, mask14, mask115, mask46, mask35, mask65, mask90, mask26]),
    (1, mask58, [mask58, mask115, mask46, mask14, mask65, mask90, mask26]),
    (0, mask58, [mask58, mask43, mask115, mask46, mask14, mask65, mask90, mask26])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch19Part0_dead : branch19Part0.any (evaluateN 7) = false := by
  decide +kernel

def branch19Part1 : List SearchNode :=
  [(0, mask58, [mask58, mask35, mask115, mask46, mask14, mask65, mask90, mask26]),
    (1, mask83, [mask83, mask115, mask46, mask14, mask35, mask90, mask26]),
    (0, mask83, [mask83, mask43, mask115, mask46, mask14, mask35, mask90, mask26]),
    (0, mask83, [mask83, mask65, mask115, mask46, mask14, mask35, mask90, mask26]),
    (1, mask104, [mask104, mask115, mask46, mask14, mask35, mask65, mask26]),
    (0, mask104, [mask104, mask43, mask115, mask46, mask14, mask35, mask65, mask26]),
    (0, mask104, [mask104, mask90, mask115, mask46, mask14, mask35, mask65, mask26]),
    (1, mask53, [mask53, mask115, mask46, mask14, mask35, mask65, mask90]),
    (0, mask53, [mask53, mask43, mask115, mask46, mask14, mask35, mask65, mask90]),
    (0, mask53, [mask53, mask26, mask115, mask46, mask14, mask35, mask65, mask90]),
    (1, mask123, [mask123, mask43, mask14, mask35, mask65, mask90, mask26]),
    (0, mask123, [mask123, mask115, mask43, mask14, mask35, mask65, mask90, mask26]),
    (0, mask123, [mask123, mask46, mask43, mask14, mask35, mask65, mask90, mask26]),
    (1, mask132, [mask132, mask43, mask46, mask14, mask35, mask65, mask90]),
    (0, mask132, [mask132, mask115, mask43, mask46, mask14, mask35, mask65, mask90]),
    (0, mask132, [mask132, mask26, mask43, mask46, mask14, mask35, mask65, mask90])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch19Part1_dead : branch19Part1.any (evaluateN 7) = false := by
  decide +kernel

def branch19Part2 : List SearchNode :=
  [(0, mask84, [mask84, mask46, mask43, mask115, mask14, mask35, mask90, mask26]),
    (0, mask105, [mask105, mask46, mask43, mask115, mask14, mask35, mask65, mask26]),
    (1, mask55, [mask55, mask43, mask115, mask14, mask35, mask65, mask90]),
    (0, mask55, [mask55, mask46, mask43, mask115, mask14, mask35, mask65, mask90]),
    (0, mask55, [mask55, mask26, mask43, mask115, mask14, mask35, mask65, mask90])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch19Part2_dead : branch19Part2.any (evaluateN 7) = false := by
  decide +kernel

def branch19Part3 : List SearchNode :=
  [(1, mask70, [mask70, mask43, mask115, mask46, mask35, mask90, mask26]),
    (0, mask70, [mask70, mask14, mask43, mask115, mask46, mask35, mask90, mask26]),
    (0, mask70, [mask70, mask65, mask43, mask115, mask46, mask35, mask90, mask26]),
    (1, mask100, [mask100, mask43, mask115, mask46, mask14, mask65, mask26]),
    (0, mask100, [mask100, mask35, mask43, mask115, mask46, mask14, mask65, mask26]),
    (0, mask100, [mask100, mask90, mask43, mask115, mask46, mask14, mask65, mask26])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch19Part3_dead : branch19Part3.any (evaluateN 7) = false := by
  decide +kernel

def branch19Next : List SearchNode :=
  branch19Part0 ++ branch19Part1 ++ branch19Part2 ++ branch19Part3

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch19Next_dead : branch19Next.any (evaluateN 7) = false := by
  simp only [branch19Next, List.any_append, List.any_cons, List.any_nil, branch19Part0_dead, branch19Part1_dead, branch19Part2_dead, branch19Part3_dead, Bool.or_false, Bool.false_or]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch19_front : frontierN branch19 = branch19Next := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch19_dead : evaluateN 8 branch19 = false := by
  rw [evaluateN_step 5, branch19_front, branch19Next_dead, Bool.or_false]
  rfl

def branch20Part0 : List SearchNode :=
  [(1, mask64, [mask64, mask115, mask65, mask35, mask46, mask90, mask26]),
    (0, mask64, [mask64, mask63, mask115, mask65, mask35, mask46, mask90, mask26]),
    (0, mask64, [mask64, mask14, mask115, mask65, mask35, mask46, mask90, mask26]),
    (1, mask77, [mask77, mask115, mask65, mask14, mask46, mask90, mask26]),
    (0, mask77, [mask77, mask63, mask115, mask65, mask14, mask46, mask90, mask26]),
    (0, mask77, [mask77, mask35, mask115, mask65, mask14, mask46, mask90, mask26]),
    (1, mask82, [mask82, mask115, mask65, mask14, mask35, mask90, mask26]),
    (0, mask82, [mask82, mask63, mask115, mask65, mask14, mask35, mask90, mask26]),
    (0, mask82, [mask82, mask46, mask115, mask65, mask14, mask35, mask90, mask26]),
    (1, mask110, [mask110, mask115, mask65, mask14, mask35, mask46, mask26]),
    (0, mask110, [mask110, mask63, mask115, mask65, mask14, mask35, mask46, mask26]),
    (0, mask110, [mask110, mask90, mask115, mask65, mask14, mask35, mask46, mask26]),
    (1, mask73, [mask73, mask115, mask65, mask14, mask35, mask46, mask90])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch20Part0_dead : branch20Part0.any (evaluateN 7) = false := by
  decide +kernel

def branch20Part1 : List SearchNode :=
  [(0, mask73, [mask73, mask63, mask115, mask65, mask14, mask35, mask46, mask90]),
    (0, mask73, [mask73, mask26, mask115, mask65, mask14, mask35, mask46, mask90]),
    (1, mask127, [mask127, mask63, mask14, mask35, mask46, mask90, mask26]),
    (0, mask127, [mask127, mask115, mask63, mask14, mask35, mask46, mask90, mask26]),
    (0, mask127, [mask127, mask65, mask63, mask14, mask35, mask46, mask90, mask26]),
    (0, mask121, [mask121, mask14, mask63, mask65, mask35, mask46, mask90, mask26]),
    (1, mask132, [mask132, mask63, mask65, mask14, mask35, mask46, mask90]),
    (0, mask132, [mask132, mask115, mask63, mask65, mask14, mask35, mask46, mask90]),
    (0, mask132, [mask132, mask26, mask63, mask65, mask14, mask35, mask46, mask90]),
    (1, mask70, [mask70, mask63, mask115, mask35, mask46, mask90, mask26]),
    (0, mask70, [mask70, mask65, mask63, mask115, mask35, mask46, mask90, mask26]),
    (0, mask70, [mask70, mask14, mask63, mask115, mask35, mask46, mask90, mask26]),
    (0, mask84, [mask84, mask46, mask63, mask115, mask14, mask35, mask90, mask26]),
    (0, mask75, [mask75, mask26, mask63, mask115, mask14, mask35, mask46, mask90]),
    (1, mask100, [mask100, mask63, mask115, mask65, mask14, mask46, mask26]),
    (0, mask100, [mask100, mask35, mask63, mask115, mask65, mask14, mask46, mask26]),
    (0, mask100, [mask100, mask90, mask63, mask115, mask65, mask14, mask46, mask26])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch20Part1_dead : branch20Part1.any (evaluateN 7) = false := by
  decide +kernel

def branch20Part2 : List SearchNode :=
  [(0, mask105, [mask105, mask46, mask63, mask115, mask65, mask14, mask35, mask26])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch20Part2_dead : branch20Part2.any (evaluateN 7) = false := by
  decide +kernel

def branch20Next : List SearchNode :=
  branch20Part0 ++ branch20Part1 ++ branch20Part2

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch20Next_dead : branch20Next.any (evaluateN 7) = false := by
  simp only [branch20Next, List.any_append, List.any_cons, List.any_nil, branch20Part0_dead, branch20Part1_dead, branch20Part2_dead, Bool.or_false, Bool.false_or]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch20_front : frontierN branch20 = branch20Next := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch20_dead : evaluateN 8 branch20 = false := by
  rw [evaluateN_step 5, branch20_front, branch20Next_dead, Bool.or_false]
  rfl

def branch21Part0 : List SearchNode :=
  [(1, mask12, [mask12, mask132, mask14, mask35, mask46, mask65, mask90]),
    (1, mask134, [mask134, mask132, mask14, mask35, mask46, mask65, mask90])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch21Part0_dead : branch21Part0.any (evaluateN 7) = false := by
  decide +kernel

def branch21Part1 : List SearchNode :=
  [(1, mask24, [mask24, mask132, mask35, mask14, mask46, mask65, mask90]),
    (1, mask140, [mask140, mask132, mask35, mask14, mask46, mask65, mask90])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch21Part1_dead : branch21Part1.any (evaluateN 7) = false := by
  decide +kernel

def branch21Part2 : List SearchNode :=
  [(1, mask43, [mask43, mask132, mask46, mask14, mask35, mask65, mask90]),
    (1, mask135, [mask135, mask132, mask46, mask14, mask35, mask65, mask90])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch21Part2_dead : branch21Part2.any (evaluateN 7) = false := by
  decide +kernel

def branch21Part3 : List SearchNode :=
  [(1, mask63, [mask63, mask132, mask65, mask14, mask35, mask46, mask90]),
    (1, mask136, [mask136, mask132, mask65, mask14, mask35, mask46, mask90]),
    (1, mask89, [mask89, mask132, mask90, mask14, mask35, mask46, mask65])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch21Part3_dead : branch21Part3.any (evaluateN 7) = false := by
  decide +kernel

def branch21Part4 : List SearchNode :=
  [(1, mask133, [mask133, mask132, mask90, mask14, mask35, mask46, mask65])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch21Part4_dead : branch21Part4.any (evaluateN 7) = false := by
  decide +kernel

def branch21Next : List SearchNode :=
  branch21Part0 ++ branch21Part1 ++ branch21Part2 ++ branch21Part3 ++ branch21Part4

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch21Next_dead : branch21Next.any (evaluateN 7) = false := by
  simp only [branch21Next, List.any_append, List.any_cons, List.any_nil, branch21Part0_dead, branch21Part1_dead, branch21Part2_dead, branch21Part3_dead, branch21Part4_dead, Bool.or_false, Bool.false_or]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch21_front : frontierN branch21 = branch21Next := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch21_dead : evaluateN 8 branch21 = false := by
  rw [evaluateN_step 5, branch21_front, branch21Next_dead, Bool.or_false]
  rfl

def branch22Part0 : List SearchNode :=
  [(0, mask9, [mask9, mask84, mask14, mask46, mask35, mask115, mask90, mask26]),
    (1, mask86, [mask86, mask14, mask46, mask35, mask115, mask90, mask26]),
    (0, mask86, [mask86, mask84, mask14, mask46, mask35, mask115, mask90, mask26]),
    (0, mask23, [mask23, mask84, mask35, mask46, mask14, mask115, mask90, mask26]),
    (0, mask87, [mask87, mask84, mask35, mask46, mask14, mask115, mask90, mask26]),
    (0, mask81, [mask81, mask84, mask115, mask46, mask14, mask35, mask90, mask26]),
    (0, mask129, [mask129, mask84, mask115, mask46, mask14, mask35, mask90, mask26]),
    (0, mask130, [mask130, mask84, mask90, mask46, mask14, mask35, mask115, mask26]),
    (0, mask88, [mask88, mask84, mask26, mask46, mask14, mask35, mask115, mask90]),
    (1, mask123, [mask123, mask115, mask84, mask14, mask35, mask90, mask26]),
    (0, mask123, [mask123, mask46, mask115, mask84, mask14, mask35, mask90, mask26])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch22Part0_dead : branch22Part0.any (evaluateN 7) = false := by
  decide +kernel

def branch22Part1 : List SearchNode :=
  [(2, mask105, [mask105, mask84, mask14, mask35, mask115, mask26]),
    (1, mask105, [mask105, mask46, mask84, mask14, mask35, mask115, mask26]),
    (1, mask105, [mask105, mask90, mask84, mask14, mask35, mask115, mask26]),
    (0, mask105, [mask105, mask46, mask90, mask84, mask14, mask35, mask115, mask26]),
    (0, mask121, [mask121, mask14, mask115, mask84, mask46, mask35, mask90, mask26]),
    (0, mask94, [mask94, mask14, mask90, mask84, mask46, mask35, mask115, mask26]),
    (0, mask137, [mask137, mask35, mask115, mask84, mask46, mask14, mask90, mask26])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch22Part1_dead : branch22Part1.any (evaluateN 7) = false := by
  decide +kernel

def branch22Part2 : List SearchNode :=
  [(2, mask100, [mask100, mask84, mask46, mask14, mask115, mask26]),
    (1, mask100, [mask100, mask35, mask84, mask46, mask14, mask115, mask26]),
    (1, mask100, [mask100, mask90, mask84, mask46, mask14, mask115, mask26]),
    (0, mask100, [mask100, mask35, mask90, mask84, mask46, mask14, mask115, mask26]),
    (0, mask89, [mask89, mask115, mask90, mask84, mask46, mask14, mask35, mask26]),
    (0, mask119, [mask119, mask115, mask90, mask84, mask46, mask14, mask35, mask26])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch22Part2_dead : branch22Part2.any (evaluateN 7) = false := by
  decide +kernel

def branch22Part3 : List SearchNode :=
  [(2, mask132, [mask132, mask84, mask46, mask14, mask35, mask90]),
    (1, mask132, [mask132, mask115, mask84, mask46, mask14, mask35, mask90]),
    (1, mask132, [mask132, mask26, mask84, mask46, mask14, mask35, mask90]),
    (0, mask132, [mask132, mask115, mask26, mask84, mask46, mask14, mask35, mask90]),
    (0, mask98, [mask98, mask90, mask26, mask84, mask46, mask14, mask35, mask115])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch22Part3_dead : branch22Part3.any (evaluateN 7) = false := by
  decide +kernel

def branch22Next : List SearchNode :=
  branch22Part0 ++ branch22Part1 ++ branch22Part2 ++ branch22Part3

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch22Next_dead : branch22Next.any (evaluateN 7) = false := by
  simp only [branch22Next, List.any_append, List.any_cons, List.any_nil, branch22Part0_dead, branch22Part1_dead, branch22Part2_dead, branch22Part3_dead, Bool.or_false, Bool.false_or]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch22_front : frontierN branch22 = branch22Next := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch22_dead : evaluateN 8 branch22 = false := by
  rw [evaluateN_step 5, branch22_front, branch22Next_dead, Bool.or_false]
  rfl

def branch23Part0 : List SearchNode :=
  [(0, mask9, [mask9, mask14, mask46, mask65, mask35, mask115, mask90, mask26]),
    (0, mask86, [mask86, mask14, mask46, mask65, mask35, mask115, mask90, mask26]),
    (0, mask23, [mask23, mask35, mask46, mask65, mask14, mask115, mask90, mask26]),
    (0, mask87, [mask87, mask35, mask46, mask65, mask14, mask115, mask90, mask26]),
    (0, mask81, [mask81, mask115, mask46, mask65, mask14, mask35, mask90, mask26]),
    (0, mask129, [mask129, mask115, mask46, mask65, mask14, mask35, mask90, mask26]),
    (0, mask130, [mask130, mask90, mask46, mask65, mask14, mask35, mask115, mask26]),
    (0, mask88, [mask88, mask26, mask46, mask65, mask14, mask35, mask115, mask90]),
    (0, mask123, [mask123, mask115, mask84, mask65, mask14, mask35, mask90, mask26]),
    (1, mask105, [mask105, mask84, mask65, mask14, mask35, mask115, mask26]),
    (0, mask105, [mask105, mask46, mask84, mask65, mask14, mask35, mask115, mask26]),
    (0, mask105, [mask105, mask90, mask84, mask65, mask14, mask35, mask115, mask26]),
    (0, mask127, [mask127, mask115, mask84, mask46, mask14, mask35, mask90, mask26]),
    (0, mask111, [mask111, mask90, mask84, mask46, mask14, mask35, mask115, mask26])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch23Part0_dead : branch23Part0.any (evaluateN 7) = false := by
  decide +kernel

def branch23Part1 : List SearchNode :=
  [(1, mask100, [mask100, mask84, mask46, mask65, mask14, mask115, mask26]),
    (0, mask100, [mask100, mask35, mask84, mask46, mask65, mask14, mask115, mask26]),
    (0, mask100, [mask100, mask90, mask84, mask46, mask65, mask14, mask115, mask26]),
    (1, mask132, [mask132, mask84, mask46, mask65, mask14, mask35, mask90]),
    (0, mask132, [mask132, mask115, mask84, mask46, mask65, mask14, mask35, mask90]),
    (0, mask132, [mask132, mask26, mask84, mask46, mask65, mask14, mask35, mask90])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch23Part1_dead : branch23Part1.any (evaluateN 7) = false := by
  decide +kernel

def branch23Next : List SearchNode :=
  branch23Part0 ++ branch23Part1

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch23Next_dead : branch23Next.any (evaluateN 7) = false := by
  simp only [branch23Next, List.any_append, List.any_cons, List.any_nil, branch23Part0_dead, branch23Part1_dead, Bool.or_false, Bool.false_or]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch23_front : frontierN branch23 = branch23Next := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch23_dead : evaluateN 8 branch23 = false := by
  rw [evaluateN_step 5, branch23_front, branch23Next_dead, Bool.or_false]
  rfl

def branch24Part0 : List SearchNode :=
  [(0, mask13, [mask13, mask55, mask14, mask46, mask35, mask115, mask65, mask90]),
    (0, mask57, [mask57, mask55, mask14, mask46, mask35, mask115, mask65, mask90]),
    (0, mask32, [mask32, mask55, mask35, mask46, mask14, mask115, mask65, mask90]),
    (0, mask61, [mask61, mask55, mask35, mask46, mask14, mask115, mask65, mask90]),
    (0, mask44, [mask44, mask55, mask115, mask46, mask14, mask35, mask65, mask90]),
    (1, mask135, [mask135, mask115, mask46, mask14, mask35, mask65, mask90]),
    (0, mask135, [mask135, mask55, mask115, mask46, mask14, mask35, mask65, mask90]),
    (0, mask88, [mask88, mask55, mask65, mask46, mask14, mask35, mask115, mask90]),
    (0, mask108, [mask108, mask55, mask90, mask46, mask14, mask35, mask115, mask65]),
    (1, mask59, [mask59, mask35, mask55, mask14, mask115, mask65, mask90]),
    (0, mask59, [mask59, mask46, mask35, mask55, mask14, mask115, mask65, mask90]),
    (0, mask123, [mask123, mask46, mask115, mask55, mask14, mask35, mask65, mask90])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch24Part0_dead : branch24Part0.any (evaluateN 7) = false := by
  decide +kernel

def branch24Part1 : List SearchNode :=
  [(2, mask84, [mask84, mask55, mask14, mask35, mask115, mask90]),
    (1, mask84, [mask84, mask46, mask55, mask14, mask35, mask115, mask90]),
    (1, mask84, [mask84, mask65, mask55, mask14, mask35, mask115, mask90]),
    (0, mask84, [mask84, mask46, mask65, mask55, mask14, mask35, mask115, mask90]),
    (2, mask105, [mask105, mask55, mask14, mask35, mask115, mask65]),
    (1, mask105, [mask105, mask46, mask55, mask14, mask35, mask115, mask65]),
    (1, mask105, [mask105, mask90, mask55, mask14, mask35, mask115, mask65]),
    (0, mask105, [mask105, mask46, mask90, mask55, mask14, mask35, mask115, mask65]),
    (0, mask121, [mask121, mask14, mask115, mask55, mask46, mask35, mask65, mask90])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch24Part1_dead : branch24Part1.any (evaluateN 7) = false := by
  decide +kernel

def branch24Part2 : List SearchNode :=
  [(2, mask70, [mask70, mask55, mask46, mask35, mask115, mask90]),
    (1, mask70, [mask70, mask14, mask55, mask46, mask35, mask115, mask90])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch24Part2_dead : branch24Part2.any (evaluateN 7) = false := by
  decide +kernel

def branch24Part3 : List SearchNode :=
  [(1, mask70, [mask70, mask65, mask55, mask46, mask35, mask115, mask90]),
    (0, mask70, [mask70, mask14, mask65, mask55, mask46, mask35, mask115, mask90]),
    (0, mask94, [mask94, mask14, mask90, mask55, mask46, mask35, mask115, mask65]),
    (0, mask137, [mask137, mask35, mask115, mask55, mask46, mask14, mask65, mask90]),
    (0, mask78, [mask78, mask35, mask65, mask55, mask46, mask14, mask115, mask90]),
    (2, mask100, [mask100, mask55, mask46, mask14, mask115, mask65]),
    (1, mask100, [mask100, mask35, mask55, mask46, mask14, mask115, mask65]),
    (1, mask100, [mask100, mask90, mask55, mask46, mask14, mask115, mask65]),
    (0, mask100, [mask100, mask35, mask90, mask55, mask46, mask14, mask115, mask65])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch24Part3_dead : branch24Part3.any (evaluateN 7) = false := by
  decide +kernel

def branch24Part4 : List SearchNode :=
  [(0, mask63, [mask63, mask115, mask65, mask55, mask46, mask14, mask35, mask90]),
    (0, mask127, [mask127, mask115, mask65, mask55, mask46, mask14, mask35, mask90]),
    (0, mask89, [mask89, mask115, mask90, mask55, mask46, mask14, mask35, mask65]),
    (0, mask119, [mask119, mask115, mask90, mask55, mask46, mask14, mask35, mask65]),
    (0, mask111, [mask111, mask65, mask90, mask55, mask46, mask14, mask35, mask115])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch24Part4_dead : branch24Part4.any (evaluateN 7) = false := by
  decide +kernel

def branch24Next : List SearchNode :=
  branch24Part0 ++ branch24Part1 ++ branch24Part2 ++ branch24Part3 ++ branch24Part4

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch24Next_dead : branch24Next.any (evaluateN 7) = false := by
  simp only [branch24Next, List.any_append, List.any_cons, List.any_nil, branch24Part0_dead, branch24Part1_dead, branch24Part2_dead, branch24Part3_dead, branch24Part4_dead, Bool.or_false, Bool.false_or]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch24_front : frontierN branch24 = branch24Next := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch24_dead : evaluateN 8 branch24 = false := by
  rw [evaluateN_step 5, branch24_front, branch24Next_dead, Bool.or_false]
  rfl

def branch25Part0 : List SearchNode :=
  [(0, mask13, [mask13, mask14, mask46, mask26, mask35, mask115, mask65, mask90]),
    (0, mask57, [mask57, mask14, mask46, mask26, mask35, mask115, mask65, mask90]),
    (0, mask32, [mask32, mask35, mask46, mask26, mask14, mask115, mask65, mask90]),
    (0, mask61, [mask61, mask35, mask46, mask26, mask14, mask115, mask65, mask90]),
    (0, mask44, [mask44, mask115, mask46, mask26, mask14, mask35, mask65, mask90]),
    (0, mask135, [mask135, mask115, mask46, mask26, mask14, mask35, mask65, mask90]),
    (0, mask88, [mask88, mask65, mask46, mask26, mask14, mask35, mask115, mask90]),
    (0, mask108, [mask108, mask90, mask46, mask26, mask14, mask35, mask115, mask65]),
    (0, mask59, [mask59, mask35, mask55, mask26, mask14, mask115, mask65, mask90]),
    (1, mask84, [mask84, mask55, mask26, mask14, mask35, mask115, mask90]),
    (0, mask84, [mask84, mask46, mask55, mask26, mask14, mask35, mask115, mask90]),
    (0, mask84, [mask84, mask65, mask55, mask26, mask14, mask35, mask115, mask90])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch25Part0_dead : branch25Part0.any (evaluateN 7) = false := by
  decide +kernel

def branch25Part1 : List SearchNode :=
  [(1, mask105, [mask105, mask55, mask26, mask14, mask35, mask115, mask65]),
    (0, mask105, [mask105, mask46, mask55, mask26, mask14, mask35, mask115, mask65]),
    (0, mask105, [mask105, mask90, mask55, mask26, mask14, mask35, mask115, mask65]),
    (1, mask132, [mask132, mask55, mask46, mask14, mask35, mask65, mask90]),
    (0, mask132, [mask132, mask26, mask55, mask46, mask14, mask35, mask65, mask90]),
    (0, mask132, [mask132, mask115, mask55, mask46, mask14, mask35, mask65, mask90]),
    (0, mask75, [mask75, mask65, mask55, mask46, mask14, mask35, mask115, mask90]),
    (0, mask98, [mask98, mask90, mask55, mask46, mask14, mask35, mask115, mask65]),
    (1, mask70, [mask70, mask55, mask46, mask26, mask35, mask115, mask90]),
    (0, mask70, [mask70, mask14, mask55, mask46, mask26, mask35, mask115, mask90]),
    (0, mask70, [mask70, mask65, mask55, mask46, mask26, mask35, mask115, mask90])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch25Part1_dead : branch25Part1.any (evaluateN 7) = false := by
  decide +kernel

def branch25Part2 : List SearchNode :=
  [(1, mask100, [mask100, mask55, mask46, mask26, mask14, mask115, mask65]),
    (0, mask100, [mask100, mask35, mask55, mask46, mask26, mask14, mask115, mask65]),
    (0, mask100, [mask100, mask90, mask55, mask46, mask26, mask14, mask115, mask65])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch25Part2_dead : branch25Part2.any (evaluateN 7) = false := by
  decide +kernel

def branch25Next : List SearchNode :=
  branch25Part0 ++ branch25Part1 ++ branch25Part2

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch25Next_dead : branch25Next.any (evaluateN 7) = false := by
  simp only [branch25Next, List.any_append, List.any_cons, List.any_nil, branch25Part0_dead, branch25Part1_dead, branch25Part2_dead, Bool.or_false, Bool.false_or]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch25_front : frontierN branch25 = branch25Next := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch25_dead : evaluateN 8 branch25 = false := by
  rw [evaluateN_step 5, branch25_front, branch25Next_dead, Bool.or_false]
  rfl

def branch26Part0 : List SearchNode :=
  [(0, mask19, [mask19, mask70, mask35, mask115, mask7, mask46, mask90, mask26]),
    (0, mask80, [mask80, mask70, mask35, mask115, mask7, mask46, mask90, mask26]),
    (0, mask63, [mask63, mask70, mask115, mask35, mask7, mask46, mask90, mask26]),
    (0, mask128, [mask128, mask70, mask115, mask35, mask7, mask46, mask90, mask26]),
    (1, mask4, [mask4, mask70, mask35, mask115, mask46, mask90, mask26]),
    (0, mask4, [mask4, mask70, mask7, mask35, mask115, mask46, mask90, mask26]),
    (1, mask71, [mask71, mask70, mask35, mask115, mask46, mask90, mask26]),
    (0, mask71, [mask71, mask70, mask7, mask35, mask115, mask46, mask90, mask26]),
    (0, mask8, [mask8, mask70, mask46, mask35, mask115, mask7, mask90, mask26]),
    (0, mask86, [mask86, mask70, mask46, mask35, mask115, mask7, mask90, mask26]),
    (0, mask10, [mask10, mask70, mask90, mask35, mask115, mask7, mask46, mask26]),
    (0, mask112, [mask112, mask70, mask90, mask35, mask115, mask7, mask46, mask26]),
    (0, mask12, [mask12, mask70, mask26, mask35, mask115, mask7, mask46, mask90])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch26Part0_dead : branch26Part0.any (evaluateN 7) = false := by
  decide +kernel

def branch26Part1 : List SearchNode :=
  [(0, mask76, [mask76, mask70, mask26, mask35, mask115, mask7, mask46, mask90]),
    (0, mask137, [mask137, mask35, mask115, mask70, mask7, mask46, mask90, mask26]),
    (2, mask100, [mask100, mask70, mask115, mask7, mask46, mask26]),
    (1, mask100, [mask100, mask35, mask70, mask115, mask7, mask46, mask26]),
    (1, mask100, [mask100, mask90, mask70, mask115, mask7, mask46, mask26]),
    (0, mask100, [mask100, mask35, mask90, mask70, mask115, mask7, mask46, mask26]),
    (1, mask116, [mask116, mask115, mask70, mask35, mask46, mask90, mask26]),
    (0, mask116, [mask116, mask115, mask7, mask70, mask35, mask46, mask90, mask26]),
    (0, mask123, [mask123, mask115, mask46, mask70, mask35, mask7, mask90, mask26]),
    (0, mask89, [mask89, mask115, mask90, mask70, mask35, mask7, mask46, mask26])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch26Part1_dead : branch26Part1.any (evaluateN 7) = false := by
  decide +kernel

def branch26Part2 : List SearchNode :=
  [(0, mask119, [mask119, mask115, mask90, mask70, mask35, mask7, mask46, mask26]),
    (2, mask132, [mask132, mask70, mask35, mask7, mask46, mask90]),
    (1, mask132, [mask132, mask115, mask70, mask35, mask7, mask46, mask90]),
    (1, mask132, [mask132, mask26, mask70, mask35, mask7, mask46, mask90]),
    (0, mask132, [mask132, mask115, mask26, mask70, mask35, mask7, mask46, mask90]),
    (1, mask91, [mask91, mask90, mask70, mask35, mask115, mask46, mask26]),
    (0, mask91, [mask91, mask7, mask90, mask70, mask35, mask115, mask46, mask26]),
    (1, mask105, [mask105, mask46, mask70, mask35, mask115, mask7, mask26]),
    (0, mask105, [mask105, mask46, mask90, mask70, mask35, mask115, mask7, mask26]),
    (0, mask98, [mask98, mask90, mask26, mask70, mask35, mask115, mask7, mask46])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch26Part2_dead : branch26Part2.any (evaluateN 7) = false := by
  decide +kernel

def branch26Next : List SearchNode :=
  branch26Part0 ++ branch26Part1 ++ branch26Part2

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch26Next_dead : branch26Next.any (evaluateN 7) = false := by
  simp only [branch26Next, List.any_append, List.any_cons, List.any_nil, branch26Part0_dead, branch26Part1_dead, branch26Part2_dead, Bool.or_false, Bool.false_or]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch26_front : frontierN branch26 = branch26Next := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch26_dead : evaluateN 8 branch26 = false := by
  rw [evaluateN_step 5, branch26_front, branch26Next_dead, Bool.or_false]
  rfl

def branch27Part0 : List SearchNode :=
  [(0, mask10, [mask10, mask100, mask14, mask115, mask7, mask46, mask65, mask26]),
    (0, mask103, [mask103, mask100, mask14, mask115, mask7, mask46, mask65, mask26]),
    (0, mask89, [mask89, mask100, mask115, mask14, mask7, mask46, mask65, mask26]),
    (0, mask139, [mask139, mask100, mask115, mask14, mask7, mask46, mask65, mask26]),
    (1, mask5, [mask5, mask100, mask14, mask115, mask46, mask65, mask26]),
    (0, mask5, [mask5, mask100, mask7, mask14, mask115, mask46, mask65, mask26]),
    (1, mask101, [mask101, mask100, mask14, mask115, mask46, mask65, mask26]),
    (0, mask101, [mask101, mask100, mask7, mask14, mask115, mask46, mask65, mask26]),
    (0, mask16, [mask16, mask100, mask46, mask14, mask115, mask7, mask65, mask26]),
    (0, mask109, [mask109, mask100, mask46, mask14, mask115, mask7, mask65, mask26]),
    (0, mask19, [mask19, mask100, mask65, mask14, mask115, mask7, mask46, mask26]),
    (0, mask113, [mask113, mask100, mask65, mask14, mask115, mask7, mask46, mask26]),
    (0, mask24, [mask24, mask100, mask26, mask14, mask115, mask7, mask46, mask65]),
    (0, mask102, [mask102, mask100, mask26, mask14, mask115, mask7, mask46, mask65]),
    (0, mask121, [mask121, mask14, mask115, mask100, mask7, mask46, mask65, mask26])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch27Part0_dead : branch27Part0.any (evaluateN 7) = false := by
  decide +kernel

def branch27Part1 : List SearchNode :=
  [(1, mask116, [mask116, mask115, mask100, mask14, mask46, mask65, mask26]),
    (0, mask116, [mask116, mask115, mask7, mask100, mask14, mask46, mask65, mask26]),
    (0, mask123, [mask123, mask115, mask46, mask100, mask14, mask7, mask65, mask26]),
    (0, mask127, [mask127, mask115, mask65, mask100, mask14, mask7, mask46, mask26]),
    (2, mask132, [mask132, mask100, mask14, mask7, mask46, mask65]),
    (1, mask132, [mask132, mask115, mask100, mask14, mask7, mask46, mask65]),
    (1, mask132, [mask132, mask26, mask100, mask14, mask7, mask46, mask65]),
    (0, mask132, [mask132, mask115, mask26, mask100, mask14, mask7, mask46, mask65])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch27Part1_dead : branch27Part1.any (evaluateN 7) = false := by
  decide +kernel

def branch27Next : List SearchNode :=
  branch27Part0 ++ branch27Part1

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch27Next_dead : branch27Next.any (evaluateN 7) = false := by
  simp only [branch27Next, List.any_append, List.any_cons, List.any_nil, branch27Part0_dead, branch27Part1_dead, Bool.or_false, Bool.false_or]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch27_front : frontierN branch27 = branch27Next := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch27_dead : evaluateN 8 branch27 = false := by
  rw [evaluateN_step 5, branch27_front, branch27Next_dead, Bool.or_false]
  rfl

def branch28Part0 : List SearchNode :=
  [(0, mask8, [mask8, mask14, mask46, mask35, mask115, mask65, mask90, mask26]),
    (0, mask51, [mask51, mask14, mask46, mask35, mask115, mask65, mask90, mask26]),
    (0, mask16, [mask16, mask35, mask46, mask14, mask115, mask65, mask90, mask26]),
    (0, mask60, [mask60, mask35, mask46, mask14, mask115, mask65, mask90, mask26]),
    (0, mask43, [mask43, mask115, mask46, mask14, mask35, mask65, mask90, mask26]),
    (0, mask124, [mask124, mask115, mask46, mask14, mask35, mask65, mask90, mask26]),
    (0, mask4, [mask4, mask65, mask46, mask14, mask35, mask115, mask90, mask26]),
    (1, mask85, [mask85, mask46, mask14, mask35, mask115, mask90, mask26]),
    (0, mask85, [mask85, mask47, mask46, mask14, mask35, mask115, mask90, mask26])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch28Part0_dead : branch28Part0.any (evaluateN 7) = false := by
  decide +kernel

def branch28Part1 : List SearchNode :=
  [(0, mask85, [mask85, mask65, mask46, mask14, mask35, mask115, mask90, mask26]),
    (0, mask5, [mask5, mask90, mask46, mask14, mask35, mask115, mask65, mask26]),
    (1, mask106, [mask106, mask46, mask14, mask35, mask115, mask65, mask26]),
    (0, mask106, [mask106, mask47, mask46, mask14, mask35, mask115, mask65, mask26]),
    (0, mask106, [mask106, mask90, mask46, mask14, mask35, mask115, mask65, mask26]),
    (0, mask6, [mask6, mask26, mask46, mask14, mask35, mask115, mask65, mask90]),
    (1, mask56, [mask56, mask46, mask14, mask35, mask115, mask65, mask90]),
    (0, mask56, [mask56, mask47, mask46, mask14, mask35, mask115, mask65, mask90]),
    (0, mask56, [mask56, mask26, mask46, mask14, mask35, mask115, mask65, mask90]),
    (0, mask50, [mask50, mask14, mask47, mask35, mask115, mask65, mask90, mask26]),
    (0, mask59, [mask59, mask35, mask47, mask14, mask115, mask65, mask90, mask26]),
    (0, mask123, [mask123, mask115, mask47, mask14, mask35, mask65, mask90, mask26]),
    (1, mask84, [mask84, mask47, mask14, mask35, mask115, mask90, mask26]),
    (0, mask84, [mask84, mask46, mask47, mask14, mask35, mask115, mask90, mask26]),
    (0, mask84, [mask84, mask65, mask47, mask14, mask35, mask115, mask90, mask26]),
    (1, mask105, [mask105, mask47, mask14, mask35, mask115, mask65, mask26]),
    (0, mask105, [mask105, mask46, mask47, mask14, mask35, mask115, mask65, mask26]),
    (0, mask105, [mask105, mask90, mask47, mask14, mask35, mask115, mask65, mask26]),
    (1, mask55, [mask55, mask47, mask14, mask35, mask115, mask65, mask90]),
    (0, mask55, [mask55, mask46, mask47, mask14, mask35, mask115, mask65, mask90])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch28Part1_dead : branch28Part1.any (evaluateN 7) = false := by
  decide +kernel

def branch28Part2 : List SearchNode :=
  [(0, mask55, [mask55, mask26, mask47, mask14, mask35, mask115, mask65, mask90]),
    (1, mask70, [mask70, mask47, mask46, mask35, mask115, mask90, mask26]),
    (0, mask70, [mask70, mask14, mask47, mask46, mask35, mask115, mask90, mask26]),
    (0, mask70, [mask70, mask65, mask47, mask46, mask35, mask115, mask90, mask26]),
    (1, mask100, [mask100, mask47, mask46, mask14, mask115, mask65, mask26]),
    (0, mask100, [mask100, mask35, mask47, mask46, mask14, mask115, mask65, mask26]),
    (0, mask100, [mask100, mask90, mask47, mask46, mask14, mask115, mask65, mask26]),
    (1, mask132, [mask132, mask47, mask46, mask14, mask35, mask65, mask90]),
    (0, mask132, [mask132, mask115, mask47, mask46, mask14, mask35, mask65, mask90]),
    (0, mask132, [mask132, mask26, mask47, mask46, mask14, mask35, mask65, mask90])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch28Part2_dead : branch28Part2.any (evaluateN 7) = false := by
  decide +kernel

def branch28Next : List SearchNode :=
  branch28Part0 ++ branch28Part1 ++ branch28Part2

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch28Next_dead : branch28Next.any (evaluateN 7) = false := by
  simp only [branch28Next, List.any_append, List.any_cons, List.any_nil, branch28Part0_dead, branch28Part1_dead, branch28Part2_dead, Bool.or_false, Bool.false_or]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch28_front : frontierN branch28 = branch28Next := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem branch28_dead : evaluateN 8 branch28 = false := by
  rw [evaluateN_step 5, branch28_front, branch28Next_dead, Bool.or_false]
  rfl

def tab0 : List (ℕ × ℕ × List W) :=
  [(1, 0x1ffffffffff83060c183060c183, [0x1ffffffffff83060c183060c183, 0xfffff8102040810204081, 0x1fffff000000204081020408102, 0x3ffffe00000000000408102040810204, 0xfe0007f0003f8810204081020408, 0x7f0003f80000001122448912244891, 0x3f80000000001fc02244891224489122, 0x1fc000fe0004489122448912244]),
   (1, 0x3ffffe00000fffff850a142850a14285, [0x3ffffe00000fffff850a142850a14285, 0xfffff8102040810204081, 0x3ffffe00000000000408102040810204, 0x1fffff000000204081020408102, 0xfe0007f0003f8810204081020408, 0x7f0003f80000001122448912244891, 0x3f80000000001fc02244891224489122, 0x1fc000fe0004489122448912244]),
   (1, 0x3f8000000000000000, [0x3f8000000000000000, 0xfffff8102040810204081, 0xfe0007f0003f8810204081020408, 0x1fffff000000204081020408102, 0x3ffffe00000000000408102040810204, 0x7f0003f80000001122448912244891, 0x3f80000000001fc02244891224489122, 0x1fc000fe0004489122448912244]),
   (1, 0xfe0007ffffff8912244891224489, [0xfe0007ffffff8912244891224489, 0xfffff8102040810204081, 0xfe0007f0003f8810204081020408, 0x1fffff000000204081020408102, 0x3ffffe00000000000408102040810204, 0x7f0003f80000001122448912244891, 0x3f80000000001fc02244891224489122, 0x1fc000fe0004489122448912244]),
   (1, 0x102040810204081, [0x102040810204081, 0xfffff8102040810204081, 0x7f0003f80000001122448912244891, 0x1fffff000000204081020408102, 0x3ffffe00000000000408102040810204, 0xfe0007f0003f8810204081020408, 0x3f80000000001fc02244891224489122, 0x1fc000fe0004489122448912244]),
   (3, 0x7f0003f80fffff9122448912244891, [0x7f0003f80fffff9122448912244891, 0x1fffff000000204081020408102, 0x3ffffe00000000000408102040810204, 0xfe0007f0003f8810204081020408, 0x3f80000000001fc02244891224489122, 0x1fc000fe0004489122448912244]),
   (2, 0x7f0003f80fffff9122448912244891, [0x7f0003f80fffff9122448912244891, 0xfffff8102040810204081, 0x1fffff000000204081020408102, 0x3ffffe00000000000408102040810204, 0xfe0007f0003f8810204081020408, 0x3f80000000001fc02244891224489122, 0x1fc000fe0004489122448912244])]

def tab1 : List (ℕ × ℕ × List W) :=
  [(2, 0x7f0003f80fffff9122448912244891, [0x7f0003f80fffff9122448912244891, 0x7f0003f80000001122448912244891, 0x1fffff000000204081020408102, 0x3ffffe00000000000408102040810204, 0xfe0007f0003f8810204081020408, 0x3f80000000001fc02244891224489122, 0x1fc000fe0004489122448912244]),
   (1, 0x7f0003f80fffff9122448912244891, [0x7f0003f80fffff9122448912244891, 0xfffff8102040810204081, 0x7f0003f80000001122448912244891, 0x1fffff000000204081020408102, 0x3ffffe00000000000408102040810204, 0xfe0007f0003f8810204081020408, 0x3f80000000001fc02244891224489122, 0x1fc000fe0004489122448912244]),
   (1, 0x1fc00000000000000000, [0x1fc00000000000000000, 0xfffff8102040810204081, 0x3f80000000001fc02244891224489122, 0x1fffff000000204081020408102, 0x3ffffe00000000000408102040810204, 0xfe0007f0003f8810204081020408, 0x7f0003f80000001122448912244891, 0x1fc000fe0004489122448912244]),
   (1, 0x3f800000000fffffa3468d1a3468d1a3, [0x3f800000000fffffa3468d1a3468d1a3, 0xfffff8102040810204081, 0x3f80000000001fc02244891224489122, 0x1fffff000000204081020408102, 0x3ffffe00000000000408102040810204, 0xfe0007f0003f8810204081020408, 0x7f0003f80000001122448912244891, 0x1fc000fe0004489122448912244]),
   (1, 0xfe0000000000000000000, [0xfe0000000000000000000, 0xfffff8102040810204081, 0x1fc000fe0004489122448912244, 0x1fffff000000204081020408102, 0x3ffffe00000000000408102040810204, 0xfe0007f0003f8810204081020408, 0x7f0003f80000001122448912244891, 0x3f80000000001fc02244891224489122]),
   (1, 0x1fc000fffffc58b162c58b162c5, [0x1fc000fffffc58b162c58b162c5, 0xfffff8102040810204081, 0x1fc000fe0004489122448912244, 0x1fffff000000204081020408102, 0x3ffffe00000000000408102040810204, 0xfe0007f0003f8810204081020408, 0x7f0003f80000001122448912244891, 0x3f80000000001fc02244891224489122]),
   (1, 0x3ffffffffff00000060c183060c18306, [0x3ffffffffff00000060c183060c18306, 0x1fffff000000204081020408102, 0x3ffffe00000000000408102040810204, 0xfffff8102040810204081, 0xfe0007f0003f8810204081020408, 0x7f0003f80000001122448912244891, 0x3f80000000001fc02244891224489122, 0x1fc000fe0004489122448912244])]

def tab2 : List (ℕ × ℕ × List W) :=
  [(1, 0x7f000000000000000000000, [0x7f000000000000000000000, 0x1fffff000000204081020408102, 0xfe0007f0003f8810204081020408, 0xfffff8102040810204081, 0x3ffffe00000000000408102040810204, 0x7f0003f80000001122448912244891, 0x3f80000000001fc02244891224489122, 0x1fc000fe0004489122448912244]),
   (1, 0xfffffff0003f8a142850a142850a, [0xfffffff0003f8a142850a142850a, 0x1fffff000000204081020408102, 0xfe0007f0003f8810204081020408, 0xfffff8102040810204081, 0x3ffffe00000000000408102040810204, 0x7f0003f80000001122448912244891, 0x3f80000000001fc02244891224489122, 0x1fc000fe0004489122448912244]),
   (1, 0x3f80000000000000000000000, [0x3f80000000000000000000000, 0x1fffff000000204081020408102, 0x7f0003f80000001122448912244891, 0xfffff8102040810204081, 0x3ffffe00000000000408102040810204, 0xfe0007f0003f8810204081020408, 0x3f80000000001fc02244891224489122, 0x1fc000fe0004489122448912244]),
   (1, 0x7f01fffff0000013264c993264c993, [0x7f01fffff0000013264c993264c993, 0x1fffff000000204081020408102, 0x7f0003f80000001122448912244891, 0xfffff8102040810204081, 0x3ffffe00000000000408102040810204, 0xfe0007f0003f8810204081020408, 0x3f80000000001fc02244891224489122, 0x1fc000fe0004489122448912244]),
   (1, 0x204081020408102, [0x204081020408102, 0x1fffff000000204081020408102, 0x3f80000000001fc02244891224489122, 0xfffff8102040810204081, 0x3ffffe00000000000408102040810204, 0xfe0007f0003f8810204081020408, 0x7f0003f80000001122448912244891, 0x1fc000fe0004489122448912244]),
   (3, 0x3f8001fffff01fc02244891224489122, [0x3f8001fffff01fc02244891224489122, 0xfffff8102040810204081, 0x3ffffe00000000000408102040810204, 0xfe0007f0003f8810204081020408, 0x7f0003f80000001122448912244891, 0x1fc000fe0004489122448912244]),
   (2, 0x3f8001fffff01fc02244891224489122, [0x3f8001fffff01fc02244891224489122, 0x1fffff000000204081020408102, 0xfffff8102040810204081, 0x3ffffe00000000000408102040810204, 0xfe0007f0003f8810204081020408, 0x7f0003f80000001122448912244891, 0x1fc000fe0004489122448912244])]

def tab3 : List (ℕ × ℕ × List W) :=
  [(2, 0x3f8001fffff01fc02244891224489122, [0x3f8001fffff01fc02244891224489122, 0x3f80000000001fc02244891224489122, 0xfffff8102040810204081, 0x3ffffe00000000000408102040810204, 0xfe0007f0003f8810204081020408, 0x7f0003f80000001122448912244891, 0x1fc000fe0004489122448912244]),
   (1, 0x3f8001fffff01fc02244891224489122, [0x3f8001fffff01fc02244891224489122, 0x1fffff000000204081020408102, 0x3f80000000001fc02244891224489122, 0xfffff8102040810204081, 0x3ffffe00000000000408102040810204, 0xfe0007f0003f8810204081020408, 0x7f0003f80000001122448912244891, 0x1fc000fe0004489122448912244]),
   (1, 0x1fc000000000000000000000000, [0x1fc000000000000000000000000, 0x1fffff000000204081020408102, 0x1fc000fe0004489122448912244, 0xfffff8102040810204081, 0x3ffffe00000000000408102040810204, 0xfe0007f0003f8810204081020408, 0x7f0003f80000001122448912244891, 0x3f80000000001fc02244891224489122]),
   (1, 0x1ffffffe000468d1a3468d1a346, [0x1ffffffe000468d1a3468d1a346, 0x1fffff000000204081020408102, 0x1fc000fe0004489122448912244, 0xfffff8102040810204081, 0x3ffffe00000000000408102040810204, 0xfe0007f0003f8810204081020408, 0x7f0003f80000001122448912244891, 0x3f80000000001fc02244891224489122]),
   (1, 0xfe00000000000000000000000000, [0xfe00000000000000000000000000, 0x3ffffe00000000000408102040810204, 0xfe0007f0003f8810204081020408, 0xfffff8102040810204081, 0x1fffff000000204081020408102, 0x7f0003f80000001122448912244891, 0x3f80000000001fc02244891224489122, 0x1fc000fe0004489122448912244]),
   (1, 0x3ffffe0007f0003f8c183060c183060c, [0x3ffffe0007f0003f8c183060c183060c, 0x3ffffe00000000000408102040810204, 0xfe0007f0003f8810204081020408, 0xfffff8102040810204081, 0x1fffff000000204081020408102, 0x7f0003f80000001122448912244891, 0x3f80000000001fc02244891224489122, 0x1fc000fe0004489122448912244]),
   (1, 0x7f0000000000000000000000000000, [0x7f0000000000000000000000000000, 0x3ffffe00000000000408102040810204, 0x7f0003f80000001122448912244891, 0xfffff8102040810204081, 0x1fffff000000204081020408102, 0xfe0007f0003f8810204081020408, 0x3f80000000001fc02244891224489122, 0x1fc000fe0004489122448912244])]

def tab4 : List (ℕ × ℕ × List W) :=
  [(1, 0x3ffffe03f8000000152a54a952a54a95, [0x3ffffe03f8000000152a54a952a54a95, 0x3ffffe00000000000408102040810204, 0x7f0003f80000001122448912244891, 0xfffff8102040810204081, 0x1fffff000000204081020408102, 0xfe0007f0003f8810204081020408, 0x3f80000000001fc02244891224489122, 0x1fc000fe0004489122448912244]),
   (1, 0x3f800000000000000000000000000000, [0x3f800000000000000000000000000000, 0x3ffffe00000000000408102040810204, 0x3f80000000001fc02244891224489122, 0xfffff8102040810204081, 0x1fffff000000204081020408102, 0xfe0007f0003f8810204081020408, 0x7f0003f80000001122448912244891, 0x1fc000fe0004489122448912244]),
   (1, 0x3ffffe0000001fc0264c993264c99326, [0x3ffffe0000001fc0264c993264c99326, 0x3ffffe00000000000408102040810204, 0x3f80000000001fc02244891224489122, 0xfffff8102040810204081, 0x1fffff000000204081020408102, 0xfe0007f0003f8810204081020408, 0x7f0003f80000001122448912244891, 0x1fc000fe0004489122448912244]),
   (1, 0x408102040810204, [0x408102040810204, 0x3ffffe00000000000408102040810204, 0x1fc000fe0004489122448912244, 0xfffff8102040810204081, 0x1fffff000000204081020408102, 0xfe0007f0003f8810204081020408, 0x7f0003f80000001122448912244891, 0x3f80000000001fc02244891224489122]),
   (3, 0x3ffffffc000fe0004489122448912244, [0x3ffffffc000fe0004489122448912244, 0xfffff8102040810204081, 0x1fffff000000204081020408102, 0xfe0007f0003f8810204081020408, 0x7f0003f80000001122448912244891, 0x3f80000000001fc02244891224489122]),
   (2, 0x3ffffffc000fe0004489122448912244, [0x3ffffffc000fe0004489122448912244, 0x3ffffe00000000000408102040810204, 0xfffff8102040810204081, 0x1fffff000000204081020408102, 0xfe0007f0003f8810204081020408, 0x7f0003f80000001122448912244891, 0x3f80000000001fc02244891224489122]),
   (2, 0x3ffffffc000fe0004489122448912244, [0x3ffffffc000fe0004489122448912244, 0x1fc000fe0004489122448912244, 0xfffff8102040810204081, 0x1fffff000000204081020408102, 0xfe0007f0003f8810204081020408, 0x7f0003f80000001122448912244891, 0x3f80000000001fc02244891224489122])]

def tab5 : List (ℕ × ℕ × List W) :=
  [(1, 0x3ffffffc000fe0004489122448912244, [0x3ffffffc000fe0004489122448912244, 0x3ffffe00000000000408102040810204, 0x1fc000fe0004489122448912244, 0xfffff8102040810204081, 0x1fffff000000204081020408102, 0xfe0007f0003f8810204081020408, 0x7f0003f80000001122448912244891, 0x3f80000000001fc02244891224489122]),
   (2, 0x7ffe03fff0003f993264c993264c99, [0x7ffe03fff0003f993264c993264c99, 0xfe0007f0003f8810204081020408, 0xfffff8102040810204081, 0x1fffff000000204081020408102, 0x3ffffe00000000000408102040810204, 0x3f80000000001fc02244891224489122, 0x1fc000fe0004489122448912244]),
   (1, 0x7ffe03fff0003f993264c993264c99, [0x7ffe03fff0003f993264c993264c99, 0xfe0007f0003f8810204081020408, 0x7f0003f80000001122448912244891, 0xfffff8102040810204081, 0x1fffff000000204081020408102, 0x3ffffe00000000000408102040810204, 0x3f80000000001fc02244891224489122, 0x1fc000fe0004489122448912244]),
   (2, 0x3f80fe0007f01fffaa54a952a54a952a, [0x3f80fe0007f01fffaa54a952a54a952a, 0xfe0007f0003f8810204081020408, 0xfffff8102040810204081, 0x1fffff000000204081020408102, 0x3ffffe00000000000408102040810204, 0x7f0003f80000001122448912244891, 0x1fc000fe0004489122448912244]),
   (1, 0x3f80fe0007f01fffaa54a952a54a952a, [0x3f80fe0007f01fffaa54a952a54a952a, 0xfe0007f0003f8810204081020408, 0x3f80000000001fc02244891224489122, 0xfffff8102040810204081, 0x1fffff000000204081020408102, 0x3ffffe00000000000408102040810204, 0x7f0003f80000001122448912244891, 0x1fc000fe0004489122448912244]),
   (2, 0xfffc07ffe03fcc993264c993264c, [0xfffc07ffe03fcc993264c993264c, 0xfe0007f0003f8810204081020408, 0xfffff8102040810204081, 0x1fffff000000204081020408102, 0x3ffffe00000000000408102040810204, 0x7f0003f80000001122448912244891, 0x3f80000000001fc02244891224489122]),
   (1, 0xfffc07ffe03fcc993264c993264c, [0xfffc07ffe03fcc993264c993264c, 0xfe0007f0003f8810204081020408, 0x1fc000fe0004489122448912244, 0xfffff8102040810204081, 0x1fffff000000204081020408102, 0x3ffffe00000000000408102040810204, 0x7f0003f80000001122448912244891, 0x3f80000000001fc02244891224489122])]

def tab6 : List (ℕ × ℕ × List W) :=
  [(1, 0x3fff0003f8001fc03366cd9b366cd9b3, [0x3fff0003f8001fc03366cd9b366cd9b3, 0x7f0003f80000001122448912244891, 0x3f80000000001fc02244891224489122, 0xfffff8102040810204081, 0x1fffff000000204081020408102, 0x3ffffe00000000000408102040810204, 0xfe0007f0003f8810204081020408, 0x1fc000fe0004489122448912244]),
   (1, 0x7f01fff80fe00055ab56ad5ab56ad5, [0x7f01fff80fe00055ab56ad5ab56ad5, 0x7f0003f80000001122448912244891, 0x1fc000fe0004489122448912244, 0xfffff8102040810204081, 0x1fffff000000204081020408102, 0x3ffffe00000000000408102040810204, 0xfe0007f0003f8810204081020408, 0x3f80000000001fc02244891224489122]),
   (1, 0x3f8001fc000fffc066cd9b366cd9b366, [0x3f8001fc000fffc066cd9b366cd9b366, 0x3f80000000001fc02244891224489122, 0x1fc000fe0004489122448912244, 0xfffff8102040810204081, 0x1fffff000000204081020408102, 0x3ffffe00000000000408102040810204, 0xfe0007f0003f8810204081020408, 0x7f0003f80000001122448912244891]),
   (0, 0x1ffffffffff83060c183060c183, [0x1ffffffffff83060c183060c183, 0xfffff8102040810204081, 0x1fffff000000204081020408102, 0x3ffffe00000000000408102040810204, 0x78f1e3c78f1e3c78, 0xfe0007f0003f8810204081020408, 0x7f0003f80000001122448912244891, 0x3f80000000001fc02244891224489122, 0x1fc000fe0004489122448912244]),
   (0, 0x3ffffe00000fffff850a142850a14285, [0x3ffffe00000fffff850a142850a14285, 0xfffff8102040810204081, 0x3ffffe00000000000408102040810204, 0x1fffff000000204081020408102, 0x78f1e3c78f1e3c78, 0xfe0007f0003f8810204081020408, 0x7f0003f80000001122448912244891, 0x3f80000000001fc02244891224489122, 0x1fc000fe0004489122448912244]),
   (1, 0xffffff9f3e7cf9f3e7cf9, [0xffffff9f3e7cf9f3e7cf9, 0xfffff8102040810204081, 0x1fffff000000204081020408102, 0x3ffffe00000000000408102040810204, 0xfe0007f0003f8810204081020408, 0x7f0003f80000001122448912244891, 0x3f80000000001fc02244891224489122, 0x1fc000fe0004489122448912244]),
   (0, 0xffffff9f3e7cf9f3e7cf9, [0xffffff9f3e7cf9f3e7cf9, 0xfffff8102040810204081, 0x78f1e3c78f1e3c78, 0x1fffff000000204081020408102, 0x3ffffe00000000000408102040810204, 0xfe0007f0003f8810204081020408, 0x7f0003f80000001122448912244891, 0x3f80000000001fc02244891224489122, 0x1fc000fe0004489122448912244])]

def tab7 : List (ℕ × ℕ × List W) :=
  [(0, 0x3f8000000000000000, [0x3f8000000000000000, 0xfffff8102040810204081, 0xfe0007f0003f8810204081020408, 0x1fffff000000204081020408102, 0x3ffffe00000000000408102040810204, 0x78f1e3c78f1e3c78, 0x7f0003f80000001122448912244891, 0x3f80000000001fc02244891224489122, 0x1fc000fe0004489122448912244]),
   (0, 0xfe0007ffffff8912244891224489, [0xfe0007ffffff8912244891224489, 0xfffff8102040810204081, 0xfe0007f0003f8810204081020408, 0x1fffff000000204081020408102, 0x3ffffe00000000000408102040810204, 0x78f1e3c78f1e3c78, 0x7f0003f80000001122448912244891, 0x3f80000000001fc02244891224489122, 0x1fc000fe0004489122448912244]),
   (0, 0x102040810204081, [0x102040810204081, 0xfffff8102040810204081, 0x7f0003f80000001122448912244891, 0x1fffff000000204081020408102, 0x3ffffe00000000000408102040810204, 0x78f1e3c78f1e3c78, 0xfe0007f0003f8810204081020408, 0x3f80000000001fc02244891224489122, 0x1fc000fe0004489122448912244]),
   (2, 0x7f0003f80fffff9122448912244891, [0x7f0003f80fffff9122448912244891, 0x1fffff000000204081020408102, 0x3ffffe00000000000408102040810204, 0x78f1e3c78f1e3c78, 0xfe0007f0003f8810204081020408, 0x3f80000000001fc02244891224489122, 0x1fc000fe0004489122448912244]),
   (1, 0x7f0003f80fffff9122448912244891, [0x7f0003f80fffff9122448912244891, 0xfffff8102040810204081, 0x1fffff000000204081020408102, 0x3ffffe00000000000408102040810204, 0x78f1e3c78f1e3c78, 0xfe0007f0003f8810204081020408, 0x3f80000000001fc02244891224489122, 0x1fc000fe0004489122448912244]),
   (1, 0x7f0003f80fffff9122448912244891, [0x7f0003f80fffff9122448912244891, 0x7f0003f80000001122448912244891, 0x1fffff000000204081020408102, 0x3ffffe00000000000408102040810204, 0x78f1e3c78f1e3c78, 0xfe0007f0003f8810204081020408, 0x3f80000000001fc02244891224489122, 0x1fc000fe0004489122448912244]),
   (0, 0x7f0003f80fffff9122448912244891, [0x7f0003f80fffff9122448912244891, 0xfffff8102040810204081, 0x7f0003f80000001122448912244891, 0x1fffff000000204081020408102, 0x3ffffe00000000000408102040810204, 0x78f1e3c78f1e3c78, 0xfe0007f0003f8810204081020408, 0x3f80000000001fc02244891224489122, 0x1fc000fe0004489122448912244])]

def tab8 : List (ℕ × ℕ × List W) :=
  [(0, 0x1fc00000000000000000, [0x1fc00000000000000000, 0xfffff8102040810204081, 0x3f80000000001fc02244891224489122, 0x1fffff000000204081020408102, 0x3ffffe00000000000408102040810204, 0x78f1e3c78f1e3c78, 0xfe0007f0003f8810204081020408, 0x7f0003f80000001122448912244891, 0x1fc000fe0004489122448912244]),
   (0, 0x3f800000000fffffa3468d1a3468d1a3, [0x3f800000000fffffa3468d1a3468d1a3, 0xfffff8102040810204081, 0x3f80000000001fc02244891224489122, 0x1fffff000000204081020408102, 0x3ffffe00000000000408102040810204, 0x78f1e3c78f1e3c78, 0xfe0007f0003f8810204081020408, 0x7f0003f80000001122448912244891, 0x1fc000fe0004489122448912244]),
   (0, 0xfe0000000000000000000, [0xfe0000000000000000000, 0xfffff8102040810204081, 0x1fc000fe0004489122448912244, 0x1fffff000000204081020408102, 0x3ffffe00000000000408102040810204, 0x78f1e3c78f1e3c78, 0xfe0007f0003f8810204081020408, 0x7f0003f80000001122448912244891, 0x3f80000000001fc02244891224489122]),
   (0, 0x1fc000fffffc58b162c58b162c5, [0x1fc000fffffc58b162c58b162c5, 0xfffff8102040810204081, 0x1fc000fe0004489122448912244, 0x1fffff000000204081020408102, 0x3ffffe00000000000408102040810204, 0x78f1e3c78f1e3c78, 0xfe0007f0003f8810204081020408, 0x7f0003f80000001122448912244891, 0x3f80000000001fc02244891224489122]),
   (0, 0x3ffffffffff00000060c183060c18306, [0x3ffffffffff00000060c183060c18306, 0x1fffff000000204081020408102, 0x3ffffe00000000000408102040810204, 0xfffff8102040810204081, 0x78f1e3c78f1e3c78, 0xfe0007f0003f8810204081020408, 0x7f0003f80000001122448912244891, 0x3f80000000001fc02244891224489122, 0x1fc000fe0004489122448912244]),
   (1, 0x1fffff000007af5ebd7af5ebd7a, [0x1fffff000007af5ebd7af5ebd7a, 0x1fffff000000204081020408102, 0xfffff8102040810204081, 0x3ffffe00000000000408102040810204, 0xfe0007f0003f8810204081020408, 0x7f0003f80000001122448912244891, 0x3f80000000001fc02244891224489122, 0x1fc000fe0004489122448912244]),
   (0, 0x1fffff000007af5ebd7af5ebd7a, [0x1fffff000007af5ebd7af5ebd7a, 0x1fffff000000204081020408102, 0x78f1e3c78f1e3c78, 0xfffff8102040810204081, 0x3ffffe00000000000408102040810204, 0xfe0007f0003f8810204081020408, 0x7f0003f80000001122448912244891, 0x3f80000000001fc02244891224489122, 0x1fc000fe0004489122448912244])]

def tab9 : List (ℕ × ℕ × List W) :=
  [(0, 0x7f000000000000000000000, [0x7f000000000000000000000, 0x1fffff000000204081020408102, 0xfe0007f0003f8810204081020408, 0xfffff8102040810204081, 0x3ffffe00000000000408102040810204, 0x78f1e3c78f1e3c78, 0x7f0003f80000001122448912244891, 0x3f80000000001fc02244891224489122, 0x1fc000fe0004489122448912244]),
   (0, 0xfffffff0003f8a142850a142850a, [0xfffffff0003f8a142850a142850a, 0x1fffff000000204081020408102, 0xfe0007f0003f8810204081020408, 0xfffff8102040810204081, 0x3ffffe00000000000408102040810204, 0x78f1e3c78f1e3c78, 0x7f0003f80000001122448912244891, 0x3f80000000001fc02244891224489122, 0x1fc000fe0004489122448912244]),
   (0, 0x3f80000000000000000000000, [0x3f80000000000000000000000, 0x1fffff000000204081020408102, 0x7f0003f80000001122448912244891, 0xfffff8102040810204081, 0x3ffffe00000000000408102040810204, 0x78f1e3c78f1e3c78, 0xfe0007f0003f8810204081020408, 0x3f80000000001fc02244891224489122, 0x1fc000fe0004489122448912244]),
   (0, 0x7f01fffff0000013264c993264c993, [0x7f01fffff0000013264c993264c993, 0x1fffff000000204081020408102, 0x7f0003f80000001122448912244891, 0xfffff8102040810204081, 0x3ffffe00000000000408102040810204, 0x78f1e3c78f1e3c78, 0xfe0007f0003f8810204081020408, 0x3f80000000001fc02244891224489122, 0x1fc000fe0004489122448912244]),
   (0, 0x204081020408102, [0x204081020408102, 0x1fffff000000204081020408102, 0x3f80000000001fc02244891224489122, 0xfffff8102040810204081, 0x3ffffe00000000000408102040810204, 0x78f1e3c78f1e3c78, 0xfe0007f0003f8810204081020408, 0x7f0003f80000001122448912244891, 0x1fc000fe0004489122448912244]),
   (2, 0x3f8001fffff01fc02244891224489122, [0x3f8001fffff01fc02244891224489122, 0xfffff8102040810204081, 0x3ffffe00000000000408102040810204, 0x78f1e3c78f1e3c78, 0xfe0007f0003f8810204081020408, 0x7f0003f80000001122448912244891, 0x1fc000fe0004489122448912244]),
   (1, 0x3f8001fffff01fc02244891224489122, [0x3f8001fffff01fc02244891224489122, 0x1fffff000000204081020408102, 0xfffff8102040810204081, 0x3ffffe00000000000408102040810204, 0x78f1e3c78f1e3c78, 0xfe0007f0003f8810204081020408, 0x7f0003f80000001122448912244891, 0x1fc000fe0004489122448912244])]

def tab10 : List (ℕ × ℕ × List W) :=
  [(1, 0x3f8001fffff01fc02244891224489122, [0x3f8001fffff01fc02244891224489122, 0x3f80000000001fc02244891224489122, 0xfffff8102040810204081, 0x3ffffe00000000000408102040810204, 0x78f1e3c78f1e3c78, 0xfe0007f0003f8810204081020408, 0x7f0003f80000001122448912244891, 0x1fc000fe0004489122448912244]),
   (0, 0x3f8001fffff01fc02244891224489122, [0x3f8001fffff01fc02244891224489122, 0x1fffff000000204081020408102, 0x3f80000000001fc02244891224489122, 0xfffff8102040810204081, 0x3ffffe00000000000408102040810204, 0x78f1e3c78f1e3c78, 0xfe0007f0003f8810204081020408, 0x7f0003f80000001122448912244891, 0x1fc000fe0004489122448912244]),
   (0, 0x1fc000000000000000000000000, [0x1fc000000000000000000000000, 0x1fffff000000204081020408102, 0x1fc000fe0004489122448912244, 0xfffff8102040810204081, 0x3ffffe00000000000408102040810204, 0x78f1e3c78f1e3c78, 0xfe0007f0003f8810204081020408, 0x7f0003f80000001122448912244891, 0x3f80000000001fc02244891224489122]),
   (0, 0x1ffffffe000468d1a3468d1a346, [0x1ffffffe000468d1a3468d1a346, 0x1fffff000000204081020408102, 0x1fc000fe0004489122448912244, 0xfffff8102040810204081, 0x3ffffe00000000000408102040810204, 0x78f1e3c78f1e3c78, 0xfe0007f0003f8810204081020408, 0x7f0003f80000001122448912244891, 0x3f80000000001fc02244891224489122]),
   (1, 0x3ffffe00000000007cf9f3e7cf9f3e7c, [0x3ffffe00000000007cf9f3e7cf9f3e7c, 0x3ffffe00000000000408102040810204, 0xfffff8102040810204081, 0x1fffff000000204081020408102, 0xfe0007f0003f8810204081020408, 0x7f0003f80000001122448912244891, 0x3f80000000001fc02244891224489122, 0x1fc000fe0004489122448912244]),
   (0, 0x3ffffe00000000007cf9f3e7cf9f3e7c, [0x3ffffe00000000007cf9f3e7cf9f3e7c, 0x3ffffe00000000000408102040810204, 0x78f1e3c78f1e3c78, 0xfffff8102040810204081, 0x1fffff000000204081020408102, 0xfe0007f0003f8810204081020408, 0x7f0003f80000001122448912244891, 0x3f80000000001fc02244891224489122, 0x1fc000fe0004489122448912244]),
   (0, 0xfe00000000000000000000000000, [0xfe00000000000000000000000000, 0x3ffffe00000000000408102040810204, 0xfe0007f0003f8810204081020408, 0xfffff8102040810204081, 0x1fffff000000204081020408102, 0x78f1e3c78f1e3c78, 0x7f0003f80000001122448912244891, 0x3f80000000001fc02244891224489122, 0x1fc000fe0004489122448912244])]

def tab11 : List (ℕ × ℕ × List W) :=
  [(0, 0x3ffffe0007f0003f8c183060c183060c, [0x3ffffe0007f0003f8c183060c183060c, 0x3ffffe00000000000408102040810204, 0xfe0007f0003f8810204081020408, 0xfffff8102040810204081, 0x1fffff000000204081020408102, 0x78f1e3c78f1e3c78, 0x7f0003f80000001122448912244891, 0x3f80000000001fc02244891224489122, 0x1fc000fe0004489122448912244]),
   (0, 0x7f0000000000000000000000000000, [0x7f0000000000000000000000000000, 0x3ffffe00000000000408102040810204, 0x7f0003f80000001122448912244891, 0xfffff8102040810204081, 0x1fffff000000204081020408102, 0x78f1e3c78f1e3c78, 0xfe0007f0003f8810204081020408, 0x3f80000000001fc02244891224489122, 0x1fc000fe0004489122448912244]),
   (0, 0x3ffffe03f8000000152a54a952a54a95, [0x3ffffe03f8000000152a54a952a54a95, 0x3ffffe00000000000408102040810204, 0x7f0003f80000001122448912244891, 0xfffff8102040810204081, 0x1fffff000000204081020408102, 0x78f1e3c78f1e3c78, 0xfe0007f0003f8810204081020408, 0x3f80000000001fc02244891224489122, 0x1fc000fe0004489122448912244]),
   (0, 0x3f800000000000000000000000000000, [0x3f800000000000000000000000000000, 0x3ffffe00000000000408102040810204, 0x3f80000000001fc02244891224489122, 0xfffff8102040810204081, 0x1fffff000000204081020408102, 0x78f1e3c78f1e3c78, 0xfe0007f0003f8810204081020408, 0x7f0003f80000001122448912244891, 0x1fc000fe0004489122448912244]),
   (0, 0x3ffffe0000001fc0264c993264c99326, [0x3ffffe0000001fc0264c993264c99326, 0x3ffffe00000000000408102040810204, 0x3f80000000001fc02244891224489122, 0xfffff8102040810204081, 0x1fffff000000204081020408102, 0x78f1e3c78f1e3c78, 0xfe0007f0003f8810204081020408, 0x7f0003f80000001122448912244891, 0x1fc000fe0004489122448912244]),
   (0, 0x408102040810204, [0x408102040810204, 0x3ffffe00000000000408102040810204, 0x1fc000fe0004489122448912244, 0xfffff8102040810204081, 0x1fffff000000204081020408102, 0x78f1e3c78f1e3c78, 0xfe0007f0003f8810204081020408, 0x7f0003f80000001122448912244891, 0x3f80000000001fc02244891224489122]),
   (2, 0x3ffffffc000fe0004489122448912244, [0x3ffffffc000fe0004489122448912244, 0xfffff8102040810204081, 0x1fffff000000204081020408102, 0x78f1e3c78f1e3c78, 0xfe0007f0003f8810204081020408, 0x7f0003f80000001122448912244891, 0x3f80000000001fc02244891224489122])]

def tab12 : List (ℕ × ℕ × List W) :=
  [(1, 0x3ffffffc000fe0004489122448912244, [0x3ffffffc000fe0004489122448912244, 0x3ffffe00000000000408102040810204, 0xfffff8102040810204081, 0x1fffff000000204081020408102, 0x78f1e3c78f1e3c78, 0xfe0007f0003f8810204081020408, 0x7f0003f80000001122448912244891, 0x3f80000000001fc02244891224489122]),
   (1, 0x3ffffffc000fe0004489122448912244, [0x3ffffffc000fe0004489122448912244, 0x1fc000fe0004489122448912244, 0xfffff8102040810204081, 0x1fffff000000204081020408102, 0x78f1e3c78f1e3c78, 0xfe0007f0003f8810204081020408, 0x7f0003f80000001122448912244891, 0x3f80000000001fc02244891224489122]),
   (0, 0x3ffffffc000fe0004489122448912244, [0x3ffffffc000fe0004489122448912244, 0x3ffffe00000000000408102040810204, 0x1fc000fe0004489122448912244, 0xfffff8102040810204081, 0x1fffff000000204081020408102, 0x78f1e3c78f1e3c78, 0xfe0007f0003f8810204081020408, 0x7f0003f80000001122448912244891, 0x3f80000000001fc02244891224489122]),
   (1, 0x810204081020408, [0x810204081020408, 0xfe0007f0003f8810204081020408, 0xfffff8102040810204081, 0x1fffff000000204081020408102, 0x3ffffe00000000000408102040810204, 0x7f0003f80000001122448912244891, 0x3f80000000001fc02244891224489122, 0x1fc000fe0004489122448912244]),
   (0, 0x810204081020408, [0x810204081020408, 0x78f1e3c78f1e3c78, 0xfe0007f0003f8810204081020408, 0xfffff8102040810204081, 0x1fffff000000204081020408102, 0x3ffffe00000000000408102040810204, 0x7f0003f80000001122448912244891, 0x3f80000000001fc02244891224489122, 0x1fc000fe0004489122448912244]),
   (2, 0xfe0007f0003ff8f1e3c78f1e3c78, [0xfe0007f0003ff8f1e3c78f1e3c78, 0xfffff8102040810204081, 0x1fffff000000204081020408102, 0x3ffffe00000000000408102040810204, 0x7f0003f80000001122448912244891, 0x3f80000000001fc02244891224489122, 0x1fc000fe0004489122448912244]),
   (1, 0xfe0007f0003ff8f1e3c78f1e3c78, [0xfe0007f0003ff8f1e3c78f1e3c78, 0x78f1e3c78f1e3c78, 0xfffff8102040810204081, 0x1fffff000000204081020408102, 0x3ffffe00000000000408102040810204, 0x7f0003f80000001122448912244891, 0x3f80000000001fc02244891224489122, 0x1fc000fe0004489122448912244])]

def tab13 : List (ℕ × ℕ × List W) :=
  [(1, 0xfe0007f0003ff8f1e3c78f1e3c78, [0xfe0007f0003ff8f1e3c78f1e3c78, 0xfe0007f0003f8810204081020408, 0xfffff8102040810204081, 0x1fffff000000204081020408102, 0x3ffffe00000000000408102040810204, 0x7f0003f80000001122448912244891, 0x3f80000000001fc02244891224489122, 0x1fc000fe0004489122448912244]),
   (0, 0xfe0007f0003ff8f1e3c78f1e3c78, [0xfe0007f0003ff8f1e3c78f1e3c78, 0x78f1e3c78f1e3c78, 0xfe0007f0003f8810204081020408, 0xfffff8102040810204081, 0x1fffff000000204081020408102, 0x3ffffe00000000000408102040810204, 0x7f0003f80000001122448912244891, 0x3f80000000001fc02244891224489122, 0x1fc000fe0004489122448912244]),
   (1, 0x1020408102040810, [0x1020408102040810, 0x7f0003f80000001122448912244891, 0xfffff8102040810204081, 0x1fffff000000204081020408102, 0x3ffffe00000000000408102040810204, 0xfe0007f0003f8810204081020408, 0x3f80000000001fc02244891224489122, 0x1fc000fe0004489122448912244]),
   (0, 0x1020408102040810, [0x1020408102040810, 0x78f1e3c78f1e3c78, 0x7f0003f80000001122448912244891, 0xfffff8102040810204081, 0x1fffff000000204081020408102, 0x3ffffe00000000000408102040810204, 0xfe0007f0003f8810204081020408, 0x3f80000000001fc02244891224489122, 0x1fc000fe0004489122448912244]),
   (2, 0x7f0003f800000079f3e7cf9f3e7cf9, [0x7f0003f800000079f3e7cf9f3e7cf9, 0xfffff8102040810204081, 0x1fffff000000204081020408102, 0x3ffffe00000000000408102040810204, 0xfe0007f0003f8810204081020408, 0x3f80000000001fc02244891224489122, 0x1fc000fe0004489122448912244]),
   (1, 0x7f0003f800000079f3e7cf9f3e7cf9, [0x7f0003f800000079f3e7cf9f3e7cf9, 0x78f1e3c78f1e3c78, 0xfffff8102040810204081, 0x1fffff000000204081020408102, 0x3ffffe00000000000408102040810204, 0xfe0007f0003f8810204081020408, 0x3f80000000001fc02244891224489122, 0x1fc000fe0004489122448912244]),
   (1, 0x7f0003f800000079f3e7cf9f3e7cf9, [0x7f0003f800000079f3e7cf9f3e7cf9, 0x7f0003f80000001122448912244891, 0xfffff8102040810204081, 0x1fffff000000204081020408102, 0x3ffffe00000000000408102040810204, 0xfe0007f0003f8810204081020408, 0x3f80000000001fc02244891224489122, 0x1fc000fe0004489122448912244])]

def tab14 : List (ℕ × ℕ × List W) :=
  [(0, 0x7f0003f800000079f3e7cf9f3e7cf9, [0x7f0003f800000079f3e7cf9f3e7cf9, 0x78f1e3c78f1e3c78, 0x7f0003f80000001122448912244891, 0xfffff8102040810204081, 0x1fffff000000204081020408102, 0x3ffffe00000000000408102040810204, 0xfe0007f0003f8810204081020408, 0x3f80000000001fc02244891224489122, 0x1fc000fe0004489122448912244]),
   (1, 0x2040810204081020, [0x2040810204081020, 0x3f80000000001fc02244891224489122, 0xfffff8102040810204081, 0x1fffff000000204081020408102, 0x3ffffe00000000000408102040810204, 0xfe0007f0003f8810204081020408, 0x7f0003f80000001122448912244891, 0x1fc000fe0004489122448912244]),
   (0, 0x2040810204081020, [0x2040810204081020, 0x78f1e3c78f1e3c78, 0x3f80000000001fc02244891224489122, 0xfffff8102040810204081, 0x1fffff000000204081020408102, 0x3ffffe00000000000408102040810204, 0xfe0007f0003f8810204081020408, 0x7f0003f80000001122448912244891, 0x1fc000fe0004489122448912244]),
   (2, 0x3f80000000001fc07af5ebd7af5ebd7a, [0x3f80000000001fc07af5ebd7af5ebd7a, 0xfffff8102040810204081, 0x1fffff000000204081020408102, 0x3ffffe00000000000408102040810204, 0xfe0007f0003f8810204081020408, 0x7f0003f80000001122448912244891, 0x1fc000fe0004489122448912244]),
   (1, 0x3f80000000001fc07af5ebd7af5ebd7a, [0x3f80000000001fc07af5ebd7af5ebd7a, 0x78f1e3c78f1e3c78, 0xfffff8102040810204081, 0x1fffff000000204081020408102, 0x3ffffe00000000000408102040810204, 0xfe0007f0003f8810204081020408, 0x7f0003f80000001122448912244891, 0x1fc000fe0004489122448912244]),
   (1, 0x3f80000000001fc07af5ebd7af5ebd7a, [0x3f80000000001fc07af5ebd7af5ebd7a, 0x3f80000000001fc02244891224489122, 0xfffff8102040810204081, 0x1fffff000000204081020408102, 0x3ffffe00000000000408102040810204, 0xfe0007f0003f8810204081020408, 0x7f0003f80000001122448912244891, 0x1fc000fe0004489122448912244]),
   (0, 0x3f80000000001fc07af5ebd7af5ebd7a, [0x3f80000000001fc07af5ebd7af5ebd7a, 0x78f1e3c78f1e3c78, 0x3f80000000001fc02244891224489122, 0xfffff8102040810204081, 0x1fffff000000204081020408102, 0x3ffffe00000000000408102040810204, 0xfe0007f0003f8810204081020408, 0x7f0003f80000001122448912244891, 0x1fc000fe0004489122448912244])]

def tab15 : List (ℕ × ℕ × List W) :=
  [(1, 0x4081020408102040, [0x4081020408102040, 0x1fc000fe0004489122448912244, 0xfffff8102040810204081, 0x1fffff000000204081020408102, 0x3ffffe00000000000408102040810204, 0xfe0007f0003f8810204081020408, 0x7f0003f80000001122448912244891, 0x3f80000000001fc02244891224489122]),
   (0, 0x4081020408102040, [0x4081020408102040, 0x78f1e3c78f1e3c78, 0x1fc000fe0004489122448912244, 0xfffff8102040810204081, 0x1fffff000000204081020408102, 0x3ffffe00000000000408102040810204, 0xfe0007f0003f8810204081020408, 0x7f0003f80000001122448912244891, 0x3f80000000001fc02244891224489122]),
   (2, 0x1fc000fe0007cf9f3e7cf9f3e7c, [0x1fc000fe0007cf9f3e7cf9f3e7c, 0xfffff8102040810204081, 0x1fffff000000204081020408102, 0x3ffffe00000000000408102040810204, 0xfe0007f0003f8810204081020408, 0x7f0003f80000001122448912244891, 0x3f80000000001fc02244891224489122]),
   (1, 0x1fc000fe0007cf9f3e7cf9f3e7c, [0x1fc000fe0007cf9f3e7cf9f3e7c, 0x78f1e3c78f1e3c78, 0xfffff8102040810204081, 0x1fffff000000204081020408102, 0x3ffffe00000000000408102040810204, 0xfe0007f0003f8810204081020408, 0x7f0003f80000001122448912244891, 0x3f80000000001fc02244891224489122]),
   (1, 0x1fc000fe0007cf9f3e7cf9f3e7c, [0x1fc000fe0007cf9f3e7cf9f3e7c, 0x1fc000fe0004489122448912244, 0xfffff8102040810204081, 0x1fffff000000204081020408102, 0x3ffffe00000000000408102040810204, 0xfe0007f0003f8810204081020408, 0x7f0003f80000001122448912244891, 0x3f80000000001fc02244891224489122]),
   (0, 0x1fc000fe0007cf9f3e7cf9f3e7c, [0x1fc000fe0007cf9f3e7cf9f3e7c, 0x78f1e3c78f1e3c78, 0x1fc000fe0004489122448912244, 0xfffff8102040810204081, 0x1fffff000000204081020408102, 0x3ffffe00000000000408102040810204, 0xfe0007f0003f8810204081020408, 0x7f0003f80000001122448912244891, 0x3f80000000001fc02244891224489122]),
   (1, 0x7ffe03fff0003f993264c993264c99, [0x7ffe03fff0003f993264c993264c99, 0xfe0007f0003f8810204081020408, 0xfffff8102040810204081, 0x1fffff000000204081020408102, 0x3ffffe00000000000408102040810204, 0x78f1e3c78f1e3c78, 0x3f80000000001fc02244891224489122, 0x1fc000fe0004489122448912244])]

def tab16 : List (ℕ × ℕ × List W) :=
  [(0, 0x7ffe03fff0003f993264c993264c99, [0x7ffe03fff0003f993264c993264c99, 0xfe0007f0003f8810204081020408, 0x7f0003f80000001122448912244891, 0xfffff8102040810204081, 0x1fffff000000204081020408102, 0x3ffffe00000000000408102040810204, 0x78f1e3c78f1e3c78, 0x3f80000000001fc02244891224489122, 0x1fc000fe0004489122448912244]),
   (1, 0x3f80fe0007f01fffaa54a952a54a952a, [0x3f80fe0007f01fffaa54a952a54a952a, 0xfe0007f0003f8810204081020408, 0xfffff8102040810204081, 0x1fffff000000204081020408102, 0x3ffffe00000000000408102040810204, 0x78f1e3c78f1e3c78, 0x7f0003f80000001122448912244891, 0x1fc000fe0004489122448912244]),
   (0, 0x3f80fe0007f01fffaa54a952a54a952a, [0x3f80fe0007f01fffaa54a952a54a952a, 0xfe0007f0003f8810204081020408, 0x3f80000000001fc02244891224489122, 0xfffff8102040810204081, 0x1fffff000000204081020408102, 0x3ffffe00000000000408102040810204, 0x78f1e3c78f1e3c78, 0x7f0003f80000001122448912244891, 0x1fc000fe0004489122448912244]),
   (1, 0xfffc07ffe03fcc993264c993264c, [0xfffc07ffe03fcc993264c993264c, 0xfe0007f0003f8810204081020408, 0xfffff8102040810204081, 0x1fffff000000204081020408102, 0x3ffffe00000000000408102040810204, 0x78f1e3c78f1e3c78, 0x7f0003f80000001122448912244891, 0x3f80000000001fc02244891224489122]),
   (0, 0xfffc07ffe03fcc993264c993264c, [0xfffc07ffe03fcc993264c993264c, 0xfe0007f0003f8810204081020408, 0x1fc000fe0004489122448912244, 0xfffff8102040810204081, 0x1fffff000000204081020408102, 0x3ffffe00000000000408102040810204, 0x78f1e3c78f1e3c78, 0x7f0003f80000001122448912244891, 0x3f80000000001fc02244891224489122]),
   (0, 0x3fff0003f8001fc03366cd9b366cd9b3, [0x3fff0003f8001fc03366cd9b366cd9b3, 0x7f0003f80000001122448912244891, 0x3f80000000001fc02244891224489122, 0xfffff8102040810204081, 0x1fffff000000204081020408102, 0x3ffffe00000000000408102040810204, 0x78f1e3c78f1e3c78, 0xfe0007f0003f8810204081020408, 0x1fc000fe0004489122448912244]),
   (0, 0x7f01fff80fe00055ab56ad5ab56ad5, [0x7f01fff80fe00055ab56ad5ab56ad5, 0x7f0003f80000001122448912244891, 0x1fc000fe0004489122448912244, 0xfffff8102040810204081, 0x1fffff000000204081020408102, 0x3ffffe00000000000408102040810204, 0x78f1e3c78f1e3c78, 0xfe0007f0003f8810204081020408, 0x3f80000000001fc02244891224489122])]

def tab17 : List (ℕ × ℕ × List W) :=
  [(0, 0x3f8001fc000fffc066cd9b366cd9b366, [0x3f8001fc000fffc066cd9b366cd9b366, 0x3f80000000001fc02244891224489122, 0x1fc000fe0004489122448912244, 0xfffff8102040810204081, 0x1fffff000000204081020408102, 0x3ffffe00000000000408102040810204, 0x78f1e3c78f1e3c78, 0xfe0007f0003f8810204081020408, 0x7f0003f80000001122448912244891])]

def table : List (ℕ × ℕ × List W) := tab0 ++ tab1 ++ tab2 ++ tab3 ++ tab4 ++ tab5 ++ tab6 ++ tab7 ++ tab8 ++ tab9 ++ tab10 ++ tab11 ++ tab12 ++ tab13 ++ tab14 ++ tab15 ++ tab16 ++ tab17

def startPart0 : List SearchNode :=
  [(1, mask121, [mask121, mask14, mask115, mask35, mask46, mask65, mask90, mask26])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem startPart0_dead : startPart0.any (evaluateN 8) = false := by
  decide +kernel

def startPart1 : List SearchNode :=
  [(1, mask0, [mask0, mask14, mask65, mask35, mask115, mask46, mask90, mask26])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem startPart1_dead : startPart1.any (evaluateN 8) = false := by
  decide +kernel

def startPart2 : List SearchNode :=
  [(1, mask94, [mask94, mask14, mask90, mask35, mask115, mask46, mask65, mask26])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem startPart2_dead : startPart2.any (evaluateN 8) = false := by
  decide +kernel

def startPart3 : List SearchNode :=
  [(1, mask137, [mask137, mask35, mask115, mask14, mask46, mask65, mask90, mask26])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem startPart3_dead : startPart3.any (evaluateN 8) = false := by
  decide +kernel

def startPart4 : List SearchNode :=
  [(1, mask78, [mask78, mask35, mask65, mask14, mask115, mask46, mask90, mask26])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem startPart4_dead : startPart4.any (evaluateN 8) = false := by
  decide +kernel

def startPart5 : List SearchNode :=
  [(1, mask1, [mask1, mask35, mask90, mask14, mask115, mask46, mask65, mask26])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem startPart5_dead : startPart5.any (evaluateN 8) = false := by
  decide +kernel

def startPart6 : List SearchNode :=
  [(1, mask100, [mask100, mask35, mask90, mask14, mask115, mask46, mask65, mask26])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem startPart6_dead : startPart6.any (evaluateN 8) = false := by
  decide +kernel

def startPart7 : List SearchNode :=
  [(1, mask123, [mask123, mask115, mask46, mask14, mask35, mask65, mask90, mask26])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem startPart7_dead : startPart7.any (evaluateN 8) = false := by
  decide +kernel

def startPart8 : List SearchNode :=
  [(1, mask127, [mask127, mask115, mask65, mask14, mask35, mask46, mask90, mask26])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem startPart8_dead : startPart8.any (evaluateN 8) = false := by
  decide +kernel

def startPart9 : List SearchNode :=
  [(1, mask89, [mask89, mask115, mask90, mask14, mask35, mask46, mask65, mask26])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem startPart9_dead : startPart9.any (evaluateN 8) = false := by
  decide +kernel

def startPart10 : List SearchNode :=
  [(1, mask119, [mask119, mask115, mask90, mask14, mask35, mask46, mask65, mask26])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem startPart10_dead : startPart10.any (evaluateN 8) = false := by
  decide +kernel

def startPart11 : List SearchNode :=
  [(1, mask2, [mask2, mask115, mask26, mask14, mask35, mask46, mask65, mask90])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem startPart11_dead : startPart11.any (evaluateN 8) = false := by
  decide +kernel

def startPart12 : List SearchNode :=
  [(2, mask132, [mask132, mask115, mask14, mask35, mask46, mask65, mask90])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem startPart12_dead : startPart12.any (evaluateN 8) = false := by
  decide +kernel

def startPart13 : List SearchNode :=
  [(2, mask132, [mask132, mask26, mask14, mask35, mask46, mask65, mask90])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem startPart13_dead : startPart13.any (evaluateN 8) = false := by
  decide +kernel

def startPart14 : List SearchNode :=
  [(1, mask132, [mask132, mask115, mask26, mask14, mask35, mask46, mask65, mask90])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem startPart14_dead : startPart14.any (evaluateN 8) = false := by
  decide +kernel

def startPart15 : List SearchNode :=
  [(2, mask105, [mask105, mask46, mask14, mask35, mask115, mask65, mask26])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem startPart15_dead : startPart15.any (evaluateN 8) = false := by
  decide +kernel

def startPart16 : List SearchNode :=
  [(1, mask105, [mask105, mask46, mask90, mask14, mask35, mask115, mask65, mask26])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem startPart16_dead : startPart16.any (evaluateN 8) = false := by
  decide +kernel

def startPart17 : List SearchNode :=
  [(1, mask111, [mask111, mask65, mask90, mask14, mask35, mask115, mask46, mask26]),
    (1, mask75, [mask75, mask65, mask26, mask14, mask35, mask115, mask46, mask90])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem startPart17_dead : startPart17.any (evaluateN 8) = false := by
  decide +kernel

def startPart18 : List SearchNode :=
  [(1, mask98, [mask98, mask90, mask26, mask14, mask35, mask115, mask46, mask65]),
    (0, mask41, [mask41, mask14, mask35, mask115, mask7, mask46, mask65, mask90, mask26]),
    (0, mask121, [mask121, mask14, mask115, mask35, mask7, mask46, mask65, mask90, mask26])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem startPart18_dead : startPart18.any (evaluateN 8) = false := by
  decide +kernel

def startPart19 : List SearchNode :=
  [(1, mask15, [mask15, mask14, mask35, mask115, mask46, mask65, mask90, mask26]),
    (0, mask15, [mask15, mask14, mask7, mask35, mask115, mask46, mask65, mask90, mask26])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem startPart19_dead : startPart19.any (evaluateN 8) = false := by
  decide +kernel

def startPart20 : List SearchNode :=
  [(0, mask8, [mask8, mask14, mask46, mask35, mask115, mask7, mask65, mask90, mask26]),
    (0, mask50, [mask50, mask14, mask46, mask35, mask115, mask7, mask65, mask90, mask26]),
    (0, mask0, [mask0, mask14, mask65, mask35, mask115, mask7, mask46, mask90, mask26])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem startPart20_dead : startPart20.any (evaluateN 8) = false := by
  decide +kernel

def startPart21 : List SearchNode :=
  [(1, mask70, [mask70, mask14, mask35, mask115, mask7, mask46, mask90, mask26])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem startPart21_dead : startPart21.any (evaluateN 8) = false := by
  decide +kernel

def startPart22 : List SearchNode :=
  [(1, mask70, [mask70, mask65, mask35, mask115, mask7, mask46, mask90, mask26]),
    (0, mask70, [mask70, mask14, mask65, mask35, mask115, mask7, mask46, mask90, mask26]),
    (0, mask10, [mask10, mask14, mask90, mask35, mask115, mask7, mask46, mask65, mask26]),
    (0, mask94, [mask94, mask14, mask90, mask35, mask115, mask7, mask46, mask65, mask26])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem startPart22_dead : startPart22.any (evaluateN 8) = false := by
  decide +kernel

def startPart23 : List SearchNode :=
  [(0, mask12, [mask12, mask14, mask26, mask35, mask115, mask7, mask46, mask65, mask90]),
    (0, mask31, [mask31, mask14, mask26, mask35, mask115, mask7, mask46, mask65, mask90]),
    (0, mask137, [mask137, mask35, mask115, mask14, mask7, mask46, mask65, mask90, mask26])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem startPart23_dead : startPart23.any (evaluateN 8) = false := by
  decide +kernel

def startPart24 : List SearchNode :=
  [(1, mask36, [mask36, mask35, mask14, mask115, mask46, mask65, mask90, mask26]),
    (0, mask36, [mask36, mask35, mask7, mask14, mask115, mask46, mask65, mask90, mask26])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem startPart24_dead : startPart24.any (evaluateN 8) = false := by
  decide +kernel

def startPart25 : List SearchNode :=
  [(0, mask16, [mask16, mask35, mask46, mask14, mask115, mask7, mask65, mask90, mask26]),
    (0, mask59, [mask59, mask35, mask46, mask14, mask115, mask7, mask65, mask90, mask26])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem startPart25_dead : startPart25.any (evaluateN 8) = false := by
  decide +kernel

def startPart26 : List SearchNode :=
  [(0, mask19, [mask19, mask35, mask65, mask14, mask115, mask7, mask46, mask90, mask26]),
    (0, mask78, [mask78, mask35, mask65, mask14, mask115, mask7, mask46, mask90, mask26]),
    (0, mask1, [mask1, mask35, mask90, mask14, mask115, mask7, mask46, mask65, mask26])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem startPart26_dead : startPart26.any (evaluateN 8) = false := by
  decide +kernel

def startPart27 : List SearchNode :=
  [(1, mask100, [mask100, mask35, mask14, mask115, mask7, mask46, mask65, mask26]),
    (1, mask100, [mask100, mask90, mask14, mask115, mask7, mask46, mask65, mask26]),
    (0, mask100, [mask100, mask35, mask90, mask14, mask115, mask7, mask46, mask65, mask26]),
    (0, mask24, [mask24, mask35, mask26, mask14, mask115, mask7, mask46, mask65, mask90]),
    (0, mask40, [mask40, mask35, mask26, mask14, mask115, mask7, mask46, mask65, mask90])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem startPart27_dead : startPart27.any (evaluateN 8) = false := by
  decide +kernel

def startPart28 : List SearchNode :=
  [(1, mask116, [mask116, mask115, mask14, mask35, mask46, mask65, mask90, mask26]),
    (0, mask116, [mask116, mask115, mask7, mask14, mask35, mask46, mask65, mask90, mask26]),
    (0, mask43, [mask43, mask115, mask46, mask14, mask35, mask7, mask65, mask90, mask26])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem startPart28_dead : startPart28.any (evaluateN 8) = false := by
  decide +kernel

def startPart29 : List SearchNode :=
  [(0, mask123, [mask123, mask115, mask46, mask14, mask35, mask7, mask65, mask90, mask26]),
    (0, mask63, [mask63, mask115, mask65, mask14, mask35, mask7, mask46, mask90, mask26]),
    (0, mask127, [mask127, mask115, mask65, mask14, mask35, mask7, mask46, mask90, mask26]),
    (0, mask89, [mask89, mask115, mask90, mask14, mask35, mask7, mask46, mask65, mask26]),
    (0, mask119, [mask119, mask115, mask90, mask14, mask35, mask7, mask46, mask65, mask26]),
    (0, mask2, [mask2, mask115, mask26, mask14, mask35, mask7, mask46, mask65, mask90])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem startPart29_dead : startPart29.any (evaluateN 8) = false := by
  decide +kernel

def startPart30 : List SearchNode :=
  [(2, mask132, [mask132, mask14, mask35, mask7, mask46, mask65, mask90]),
    (1, mask132, [mask132, mask115, mask14, mask35, mask7, mask46, mask65, mask90]),
    (1, mask132, [mask132, mask26, mask14, mask35, mask7, mask46, mask65, mask90]),
    (0, mask132, [mask132, mask115, mask26, mask14, mask35, mask7, mask46, mask65, mask90])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem startPart30_dead : startPart30.any (evaluateN 8) = false := by
  decide +kernel

def startPart31 : List SearchNode :=
  [(1, mask3, [mask3, mask46, mask14, mask35, mask115, mask65, mask90, mask26]),
    (0, mask3, [mask3, mask7, mask46, mask14, mask35, mask115, mask65, mask90, mask26])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem startPart31_dead : startPart31.any (evaluateN 8) = false := by
  decide +kernel

def startPart32 : List SearchNode :=
  [(2, mask47, [mask47, mask14, mask35, mask115, mask65, mask90, mask26]),
    (1, mask47, [mask47, mask7, mask14, mask35, mask115, mask65, mask90, mask26])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem startPart32_dead : startPart32.any (evaluateN 8) = false := by
  decide +kernel

def startPart33 : List SearchNode :=
  [(0, mask47, [mask47, mask7, mask46, mask14, mask35, mask115, mask65, mask90, mask26]),
    (1, mask4, [mask4, mask65, mask14, mask35, mask115, mask46, mask90, mask26])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem startPart33_dead : startPart33.any (evaluateN 8) = false := by
  decide +kernel

def startPart34 : List SearchNode :=
  [(0, mask4, [mask4, mask7, mask65, mask14, mask35, mask115, mask46, mask90, mask26]),
    (2, mask66, [mask66, mask14, mask35, mask115, mask46, mask90, mask26]),
    (1, mask66, [mask66, mask7, mask14, mask35, mask115, mask46, mask90, mask26])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem startPart34_dead : startPart34.any (evaluateN 8) = false := by
  decide +kernel

def startPart35 : List SearchNode :=
  [(1, mask66, [mask66, mask65, mask14, mask35, mask115, mask46, mask90, mask26]),
    (0, mask66, [mask66, mask7, mask65, mask14, mask35, mask115, mask46, mask90, mask26])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem startPart35_dead : startPart35.any (evaluateN 8) = false := by
  decide +kernel

def startPart36 : List SearchNode :=
  [(1, mask5, [mask5, mask90, mask14, mask35, mask115, mask46, mask65, mask26]),
    (0, mask5, [mask5, mask7, mask90, mask14, mask35, mask115, mask46, mask65, mask26])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem startPart36_dead : startPart36.any (evaluateN 8) = false := by
  decide +kernel

def startPart37 : List SearchNode :=
  [(2, mask91, [mask91, mask14, mask35, mask115, mask46, mask65, mask26]),
    (1, mask91, [mask91, mask7, mask14, mask35, mask115, mask46, mask65, mask26]),
    (1, mask91, [mask91, mask90, mask14, mask35, mask115, mask46, mask65, mask26]),
    (0, mask91, [mask91, mask7, mask90, mask14, mask35, mask115, mask46, mask65, mask26])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem startPart37_dead : startPart37.any (evaluateN 8) = false := by
  decide +kernel

def startPart38 : List SearchNode :=
  [(1, mask6, [mask6, mask26, mask14, mask35, mask115, mask46, mask65, mask90]),
    (0, mask6, [mask6, mask7, mask26, mask14, mask35, mask115, mask46, mask65, mask90])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem startPart38_dead : startPart38.any (evaluateN 8) = false := by
  decide +kernel

def startPart39 : List SearchNode :=
  [(2, mask27, [mask27, mask14, mask35, mask115, mask46, mask65, mask90]),
    (1, mask27, [mask27, mask7, mask14, mask35, mask115, mask46, mask65, mask90])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem startPart39_dead : startPart39.any (evaluateN 8) = false := by
  decide +kernel

def startPart40 : List SearchNode :=
  [(1, mask27, [mask27, mask26, mask14, mask35, mask115, mask46, mask65, mask90])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem startPart40_dead : startPart40.any (evaluateN 8) = false := by
  decide +kernel

def startPart41 : List SearchNode :=
  [(0, mask27, [mask27, mask7, mask26, mask14, mask35, mask115, mask46, mask65, mask90]),
    (1, mask84, [mask84, mask46, mask14, mask35, mask115, mask7, mask90, mask26]),
    (0, mask84, [mask84, mask46, mask65, mask14, mask35, mask115, mask7, mask90, mask26]),
    (1, mask105, [mask105, mask46, mask14, mask35, mask115, mask7, mask65, mask26]),
    (0, mask105, [mask105, mask46, mask90, mask14, mask35, mask115, mask7, mask65, mask26])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem startPart41_dead : startPart41.any (evaluateN 8) = false := by
  decide +kernel

def startPart42 : List SearchNode :=
  [(1, mask55, [mask55, mask46, mask14, mask35, mask115, mask7, mask65, mask90])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem startPart42_dead : startPart42.any (evaluateN 8) = false := by
  decide +kernel

def startPart43 : List SearchNode :=
  [(0, mask55, [mask55, mask46, mask26, mask14, mask35, mask115, mask7, mask65, mask90]),
    (0, mask111, [mask111, mask65, mask90, mask14, mask35, mask115, mask7, mask46, mask26]),
    (0, mask75, [mask75, mask65, mask26, mask14, mask35, mask115, mask7, mask46, mask90]),
    (0, mask98, [mask98, mask90, mask26, mask14, mask35, mask115, mask7, mask46, mask65])]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem startPart43_dead : startPart43.any (evaluateN 8) = false := by
  decide +kernel

def startNext : List SearchNode :=
  [branch1] ++ startPart0 ++ [branch2] ++ [branch3] ++ startPart1 ++ [branch4] ++ [branch5] ++ [branch6] ++ [branch7] ++ [branch8] ++ startPart2 ++ [branch9] ++ [branch10] ++ startPart3 ++ [branch11] ++ [branch12] ++ [branch13] ++ startPart4 ++ startPart5 ++ [branch14] ++ [branch15] ++ [branch16] ++ startPart6 ++ [branch17] ++ [branch18] ++ [branch19] ++ startPart7 ++ [branch20] ++ startPart8 ++ startPart9 ++ startPart10 ++ startPart11 ++ [branch21] ++ startPart12 ++ startPart13 ++ startPart14 ++ [branch22] ++ [branch23] ++ startPart15 ++ startPart16 ++ [branch24] ++ [branch25] ++ startPart17 ++ startPart18 ++ startPart19 ++ startPart20 ++ [branch26] ++ startPart21 ++ startPart22 ++ startPart23 ++ startPart24 ++ startPart25 ++ startPart26 ++ [branch27] ++ startPart27 ++ startPart28 ++ startPart29 ++ startPart30 ++ startPart31 ++ startPart32 ++ [branch28] ++ startPart33 ++ startPart34 ++ startPart35 ++ startPart36 ++ startPart37 ++ startPart38 ++ startPart39 ++ startPart40 ++ startPart41 ++ startPart42 ++ startPart43

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem startNext_dead : startNext.any (evaluateN 8) = false := by
  simp only [startNext, List.any_append, List.any_cons, List.any_nil, branch1_dead, startPart0_dead, branch2_dead, branch3_dead, startPart1_dead, branch4_dead, branch5_dead, branch6_dead, branch7_dead, branch8_dead, startPart2_dead, branch9_dead, branch10_dead, startPart3_dead, branch11_dead, branch12_dead, branch13_dead, startPart4_dead, startPart5_dead, branch14_dead, branch15_dead, branch16_dead, startPart6_dead, branch17_dead, branch18_dead, branch19_dead, startPart7_dead, branch20_dead, startPart8_dead, startPart9_dead, startPart10_dead, startPart11_dead, branch21_dead, startPart12_dead, startPart13_dead, startPart14_dead, branch22_dead, branch23_dead, startPart15_dead, startPart16_dead, branch24_dead, branch25_dead, startPart17_dead, startPart18_dead, startPart19_dead, startPart20_dead, branch26_dead, startPart21_dead, startPart22_dead, startPart23_dead, startPart24_dead, startPart25_dead, startPart26_dead, branch27_dead, startPart27_dead, startPart28_dead, startPart29_dead, startPart30_dead, startPart31_dead, startPart32_dead, branch28_dead, startPart33_dead, startPart34_dead, startPart35_dead, startPart36_dead, startPart37_dead, startPart38_dead, startPart39_dead, startPart40_dead, startPart41_dead, startPart42_dead, startPart43_dead, Bool.or_false, Bool.false_or]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem roots_accounted : table.map asNode = startNext := by
  decide +kernel

theorem leaf_all : table.all (fun c => !(optimized 8 c.1 c.2.1 c.2.2)) = true := by
  apply batch_clear
  rw [roots_accounted]
  exact startNext_dead

def optT (e last : ℕ) (ws : List W) : Bool := if (e, last, ws) ∈ table then false else optimized 8 e last ws

theorem optT_eq : optT = optimized 8 := by
  funext e last ws
  unfold optT
  split_ifs with h
  · have hc := List.all_eq_true.mp leaf_all _ h
    dsimp only at hc
    revert hc
    cases optimized 8 e last ws <;> simp
  · rfl

def optRoot (e last : ℕ) (ws : List W) : Bool :=
  ws == [goal] || (pairs ws).any (fun (a, b, r) => dispatch e last optT a b r)

theorem optRoot_eq : optRoot = optimized 9 := by
  funext e last ws
  simp only [optRoot, optT_eq, optimized]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem all_front : inputs.sublists.all
    (fun l => decide (10 < l.length) || (cuts l != -1) || !(optRoot (10 - l.length) 0 l)) = true := by
  decide +kernel

theorem no_small (C : Circuit) (hm : Monotone2 C) (hs : C.size ≤ 9)
    (hr : PEqualNP.Represents.Represents A C) : False := by
  obtain ⟨gs, hlen, hord, S, hsub, hl⟩ := normalize_build BitVec.toNat (get_build C hm hr)
  have hlenk : gs.length ≤ 9 := Nat.le_trans hlen hs
  let l := inputs.filter (fun w => decide (w ∈ S))
  have hlS : l.toFinset = S := by
    ext v
    simp only [l, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨List.mem_toFinset.mp (hsub h), h⟩
  have hnd : l.Nodup := inputs_nodup.filter _
  have hcard := chain_card hl
  rw [← hlS, List.toFinset_card_of_nodup hnd] at hcard
  have hcuts : cuts l = -1 := cuts_full (hlS ▸ hl)
  have hsearch := optimized_complete 9 l (10 - l.length) 0 gs hnd hlenk (by omega) hord (hlS ▸ hl)
  rw [← optRoot_eq] at hsearch
  have hmem : l ∈ inputs.sublists := List.mem_sublists.mpr List.filter_sublist
  have hrow := List.all_eq_true.mp all_front l hmem
  have h4 : decide (10 < l.length) = false := by simp; omega
  have h5 : (cuts l != -1) = false := by simp [hcuts]
  rw [h4, h5, hsearch] at hrow
  exact Bool.noConfusion hrow

theorem upper : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (1981 : ℕ).testBit (4 * u.val + v.val)) 10 := by
  refine ⟨⟨[⟨GateOp.or, [2, 4]⟩, ⟨GateOp.and, [2, 4]⟩, ⟨GateOp.or, [0, 5]⟩,
    ⟨GateOp.or, [1, 6]⟩, ⟨GateOp.or, [7, 8]⟩, ⟨GateOp.or, [10, 12]⟩,
    ⟨GateOp.and, [10, 12]⟩, ⟨GateOp.and, [11, 13]⟩, ⟨GateOp.or, [9, 15]⟩,
    ⟨GateOp.or, [14, 16]⟩], 17⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by simp⟩

end PEqualNP.Outside.L_meta_6337

theorem PEqualNP.Outside.L_meta_6337 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (1981 : ℕ).testBit (4 * u.val + v.val)) 10 ∧
  ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (1981 : ℕ).testBit (4 * u.val + v.val)) 9 := by
  refine ⟨PEqualNP.Outside.L_meta_6337.upper, ?_⟩
  rintro ⟨C, hm, hs, hr⟩
  exact PEqualNP.Outside.L_meta_6337.no_small C hm hs hr
