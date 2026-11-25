import PEqualNP.Defs

-- The live-set lower-bound framework below (`build`, `live`, `compress`, `live_separates`, the
-- 128-bit pair encoding with `sep` / `cuts`, the `optimized` search and its completeness proof) is
-- copied from the accepted L-meta-6345 by BastianMIllan (open-goat/pequalnp-proofs, Apache License
-- 2.0). New here: the graph, the pair slots, the search depth, the split of the long search into
-- one theorem per first-level pair, and the upper circuit.


namespace PEqualNP.Outside.L_meta_6346_aux

section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

theorem compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero =>
    exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
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
        refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

theorem live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

theorem live_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

theorem first_live {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal (k + 1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, tail⟩
      · exact .inl done
      · exact .inr ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, Or.inl tail⟩
    · exact .inr step

end Live

abbrev W := BitVec 128

def ops (x y : W) : List W := [x &&& y, x ||| y]

def sep (x : W) : BitVec 64 := ((x >>> 64) &&& ~~~x).setWidth 64

def cuts (ws : List W) : BitVec 64 := ws.foldr (fun w v => sep w ||| v) 0

def goal : W := (-1 : BitVec 64) ++ (0 : BitVec 64)

def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

def rawInputs : List W :=
  [0x80000000001fffff8102040810204081, 0x3ffffe000000204081020408102, 0xfffc00000000000c183060c183060c, 0x7f0000000000000070e1c3870e1c3870, 0xff0000000fe0007f0408102040810204, 0x1fc07f0003f801020408102040810, 0xfe03f800000000a142850a142850a1, 0x1fc0004a952a54a952a54a]

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

def differs (i : Fin 64) (w : W) : Prop :=
  w.getLsbD (64 + i.val) = true ∧ w.getLsbD i.val = false

theorem ops_differs (i : Fin 64) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  unfold differs at hd ⊢
  rcases hz with rfl | rfl <;> revert hd <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or] <;>
    cases a.getLsbD (64 + i.val) <;> cases a.getLsbD i.val <;>
    cases b.getLsbD (64 + i.val) <;> cases b.getLsbD i.val <;> simp

theorem goal_differs : ∀ i : Fin 64, differs i goal := by
  unfold differs
  decide

theorem cuts_spec (ws : List W) (i : Fin 64) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have hi : i.val < 128 := by omega
    simp [sep, i.isLt, differs, hi, Nat.add_comm]

theorem cuts_full {k : ℕ} {ws : List W} (h : live basicOps goal k ws.toFinset) :
    cuts ws = -1 := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (goal_differs ⟨j, hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 64)[j]
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
  z == 0 || z == BitVec.allOnes 128 || w.any (fun u => z == u ||
    w.any (fun v => z == (u &&& v) || z == (u ||| v)))

private def bit (k : Fin 128) (z : W) : Bool := z[k.val]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 128) :
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
    · exact ⟨BitVec.allOnes 128, by simp [possible], by simp [step, GateOp.eval, bit]; decide⟩
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
  ∀ u ∈ w, u = 0 ∨ u = BitVec.allOnes 128 ∨ u ∈ available

theorem classify {available : Finset W} {ws : List W} (hw : represents available ws)
    {z : W} (hz : possible ws z) :
    z = 0 ∨ z = BitVec.allOnes 128 ∨ z ∈ available ∨
      ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧ z ∈ basicOps a b := by
  have lift {t : W} (h : t = 0 ∨ t = BitVec.allOnes 128 ∨ t ∈ available) :
      t = 0 ∨ t = BitVec.allOnes 128 ∨ t ∈ available ∨
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
    · exact .inr (.inr (.inr ⟨x, hu, y, hv, h, by simp [basicOps, ops]⟩))
  · subst z
    rcases hw _ hx with rfl | rfl | hu
    · rw [show (0 : W) ||| y = y by ext i hi; simp]; exact lift (hw _ hy)
    · right; left; exact BitVec.allOnes_or
    rcases hw _ hy with rfl | rfl | hv
    · rw [show x ||| (0 : W) = x by ext i hi; simp]; exact .inr (.inr (.inl hu))
    · right; left; exact BitVec.or_allOnes
    by_cases h : x = y
    · subst h; rw [BitVec.or_self]; exact .inr (.inr (.inl hu))
    · exact .inr (.inr (.inr ⟨x, hu, y, hv, h, by simp [basicOps, ops]⟩))

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
      · exact False.elim ((by decide : goal ≠ BitVec.allOnes 128) h)
      · exact h
  | cons g gs ih =>
    obtain ⟨z, hz, hstep⟩ := gate_table w w (fun _ h => h) g (hg g (by simp))
    have fn := ih (fun g' h => hg g' (by simp [h])) (w ++ [z])
    have he' : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k goal := by
      intro k; simpa only [List.foldl_cons, hstep] using he k
    have appendOK (h : z = 0 ∨ z = BitVec.allOnes 128 ∨ z ∈ av) : represents av (w ++ [z]) := by
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

def dispatch (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) : Bool :=
  let base := cuts r
  (ops a b).any fun w =>
    let v := sep w ||| base
    ((v == -1) && next extra (w :: r)) ||
    ((extra != 0) && (((v ||| sep a == -1) && next (extra - 1) (w :: a :: r)) ||
                       ((v ||| sep b == -1) && next (extra - 1) (w :: b :: r)))) ||
    ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && next (extra - 2) (w :: a :: b :: r))

def optimized : ℕ → ℕ → List W → Bool
  | 0, _, ws => ws == [goal]
  | k + 1, extra, ws => ws == [goal] ||
    (pairs ws).any (fun (a, b, r) => dispatch extra (optimized k) a b r)

theorem dispatch_complete {k extra : ℕ} {a b z : W} {r kept : List W}
    (next : ℕ → List W → Bool)
    (hz : z ∈ basicOps a b) (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts (z :: kept) = -1) (ht : next (k - kept.length) (z :: kept) = true) :
    dispatch extra next a b r = true := by
  apply List.any_eq_true.mpr
  refine ⟨z, List.mem_toFinset.mp hz, ?_⟩
  simp [keepChoices] at hk
  rcases hk with rfl | rfl | rfl | rfl <;>
    simp only [cuts, List.foldr_cons] at hc ⊢ <;>
    (try simp only [List.length_cons] at *) <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne]
  · left; left; exact ⟨hc, by convert ht using 2; omega⟩
  · left; right; exact ⟨by omega, .inl ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · left; right; exact ⟨by omega, .inr ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · right; exact ⟨⟨by omega, by convert hc using 1; ac_rfl⟩, by convert ht using 2; omega⟩

theorem optimized_complete (n : ℕ) (ws : List W) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n + 1) (h : live basicOps goal n ws.toFinset) :
    optimized n extra ws = true := by
  induction n generalizing ws extra with
  | zero => simp [optimized, singleton_list hn h]
  | succ k ih =>
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · simp [optimized, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : W} (perm : ws.Perm (a :: b :: r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          dispatch extra (optimized k) a b r = true := by
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live basicOps goal k (z :: kept).toFinset := by
          simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        apply dispatch_complete (k := k) (extra := extra) (optimized k) hop hk (by omega) (by omega) (cuts_full hl)
        apply ih _ _ hnd _ hl
        simp; omega
      simp only [optimized, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs hz⟩
      · exact ⟨(b, a, r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

def A : Fin 4 → Fin 4 → Bool := fun u v : Fin 4 => (5755 : ℕ).testBit (4 * u.val + v.val)

def posL : List (Fin 4 × Fin 4) :=
  [(0, 0), (0, 1), (0, 3), (1, 0), (1, 1), (1, 2), (2, 1), (2, 2), (3, 0)]

def negL : List (Fin 4 × Fin 4) :=
  [(0, 2), (1, 3), (2, 0), (2, 3), (3, 1), (3, 2), (3, 3)]

def samp (k : Fin 128) : Fin 4 × Fin 4 :=
  if k.val < 64 then negL.getD (k.val % 7) (0, 2) else posL.getD ((k.val - 64) / 7) (0, 0)

theorem input_rows : ∀ k : Fin 128,
    rawInputs.map (bit k) = PEqualNP.Represents.oneEach (samp k).1 (samp k).2 := by
  decide +kernel

theorem goal_rows : ∀ k : Fin 128, bit k goal = A (samp k).1 (samp k).2 := by
  decide +kernel

theorem rows_eval (C : Circuit) (hr : PEqualNP.Represents.Represents A C) (k : Fin 128) :
    (C.gates.foldl step (rawInputs.map (bit k))).getD C.output false = bit k goal := by
  rw [input_rows k, goal_rows k]
  exact hr (samp k).1 (samp k).2

theorem initial_rep : represents inputs.toFinset rawInputs := by
  intro u hu
  exact .inr (.inr (List.mem_toFinset.mpr hu))

theorem get_build (C : Circuit) (hg : Monotone2 C) (hr : PEqualNP.Represents.Represents A C) :
    build basicOps goal C.gates.length inputs.toFinset :=
  compile C.gates C.output hg rawInputs inputs.toFinset initial_rep (rows_eval C hr)

theorem extend_live {m n : ℕ} {s : Finset W} (le : m ≤ n) (h : live basicOps goal m s) :
    live basicOps goal n s := by
  induction le with
  | refl => exact h
  | step _ ih => exact Or.inl ih
theorem inputs_nodup : inputs.Nodup := by decide +kernel

-- The sublists whose search is long are checked one first-level pair at a time.
def x0 : W := 0x80000000001fffff8102040810204081
def x1 : W := 0x3ffffe000000204081020408102
def x2 : W := 0xfffc00000000000c183060c183060c
def x3 : W := 0x7f0000000000000070e1c3870e1c3870
def x4 : W := 0xff0000000fe0007f0408102040810204
def x5 : W := 0x1fc07f0003f801020408102040810
def x6 : W := 0xfe03f800000000a142850a142850a1
def x7 : W := 0x1fc0004a952a54a952a54a

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t1 : optimized 8 0 [x0 &&& x1, x0, x1, x2, x3, x4, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t2 : optimized 8 0 [x0 ||| x1, x0, x1, x2, x3, x4, x5, x6, x7] = false := by
  decide +kernel

theorem t3 : dispatch 2 (optimized 8) x0 x1 [x2, x3, x4, x5, x6, x7] = false := by
  simp only [dispatch, ops, List.any_cons, List.any_nil, Nat.reduceSub, t1, t2, Bool.and_false, Bool.or_false]
  all_goals decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t4 : dispatch 2 (optimized 8) x0 x2 [x1, x3, x4, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t5 : optimized 8 0 [x0 &&& x3, x0, x3, x1, x2, x4, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t6 : dispatch 1 (optimized 7) (x0 ||| x3) x0 [x1, x2, x4, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t7 : dispatch 1 (optimized 7) (x0 ||| x3) x1 [x0, x2, x4, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t8 : dispatch 1 (optimized 7) (x0 ||| x3) x2 [x0, x1, x4, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t9 : dispatch 1 (optimized 7) (x0 ||| x3) x4 [x0, x1, x2, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t10 : dispatch 1 (optimized 7) (x0 ||| x3) x5 [x0, x1, x2, x4, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t11 : dispatch 1 (optimized 7) (x0 ||| x3) x6 [x0, x1, x2, x4, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t12 : dispatch 1 (optimized 7) (x0 ||| x3) x7 [x0, x1, x2, x4, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t13 : dispatch 1 (optimized 7) x0 x1 [x0 ||| x3, x2, x4, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t14 : dispatch 1 (optimized 7) x0 x2 [x0 ||| x3, x1, x4, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t15 : dispatch 1 (optimized 7) x0 x4 [x0 ||| x3, x1, x2, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t16 : dispatch 1 (optimized 7) x0 x5 [x0 ||| x3, x1, x2, x4, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t17 : dispatch 1 (optimized 7) x0 x6 [x0 ||| x3, x1, x2, x4, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t18 : dispatch 1 (optimized 7) x0 x7 [x0 ||| x3, x1, x2, x4, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t19 : dispatch 1 (optimized 7) x1 x2 [x0 ||| x3, x0, x4, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t20 : dispatch 1 (optimized 7) x1 x4 [x0 ||| x3, x0, x2, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t21 : dispatch 1 (optimized 7) x1 x5 [x0 ||| x3, x0, x2, x4, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t22 : dispatch 1 (optimized 7) x1 x6 [x0 ||| x3, x0, x2, x4, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t23 : dispatch 1 (optimized 7) x1 x7 [x0 ||| x3, x0, x2, x4, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t24 : dispatch 1 (optimized 7) x2 x4 [x0 ||| x3, x0, x1, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t25 : dispatch 1 (optimized 7) x2 x5 [x0 ||| x3, x0, x1, x4, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t26 : dispatch 1 (optimized 7) x2 x6 [x0 ||| x3, x0, x1, x4, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t27 : dispatch 1 (optimized 7) x2 x7 [x0 ||| x3, x0, x1, x4, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t28 : dispatch 1 (optimized 7) x4 x5 [x0 ||| x3, x0, x1, x2, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t29 : dispatch 1 (optimized 7) x4 x6 [x0 ||| x3, x0, x1, x2, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t30 : dispatch 1 (optimized 7) x4 x7 [x0 ||| x3, x0, x1, x2, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t31 : dispatch 1 (optimized 7) x5 x6 [x0 ||| x3, x0, x1, x2, x4, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t32 : dispatch 1 (optimized 7) x5 x7 [x0 ||| x3, x0, x1, x2, x4, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t33 : dispatch 1 (optimized 7) x6 x7 [x0 ||| x3, x0, x1, x2, x4, x5] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
theorem t34_pairs : pairs [x0 ||| x3, x0, x1, x2, x4, x5, x6, x7] = [(x0 ||| x3, x0, [x1, x2, x4, x5, x6, x7]), (x0 ||| x3, x1, [x0, x2, x4, x5, x6, x7]), (x0 ||| x3, x2, [x0, x1, x4, x5, x6, x7]), (x0 ||| x3, x4, [x0, x1, x2, x5, x6, x7]), (x0 ||| x3, x5, [x0, x1, x2, x4, x6, x7]), (x0 ||| x3, x6, [x0, x1, x2, x4, x5, x7]), (x0 ||| x3, x7, [x0, x1, x2, x4, x5, x6]), (x0, x1, [x0 ||| x3, x2, x4, x5, x6, x7]), (x0, x2, [x0 ||| x3, x1, x4, x5, x6, x7]), (x0, x4, [x0 ||| x3, x1, x2, x5, x6, x7]), (x0, x5, [x0 ||| x3, x1, x2, x4, x6, x7]), (x0, x6, [x0 ||| x3, x1, x2, x4, x5, x7]), (x0, x7, [x0 ||| x3, x1, x2, x4, x5, x6]), (x1, x2, [x0 ||| x3, x0, x4, x5, x6, x7]), (x1, x4, [x0 ||| x3, x0, x2, x5, x6, x7]), (x1, x5, [x0 ||| x3, x0, x2, x4, x6, x7]), (x1, x6, [x0 ||| x3, x0, x2, x4, x5, x7]), (x1, x7, [x0 ||| x3, x0, x2, x4, x5, x6]), (x2, x4, [x0 ||| x3, x0, x1, x5, x6, x7]), (x2, x5, [x0 ||| x3, x0, x1, x4, x6, x7]), (x2, x6, [x0 ||| x3, x0, x1, x4, x5, x7]), (x2, x7, [x0 ||| x3, x0, x1, x4, x5, x6]), (x4, x5, [x0 ||| x3, x0, x1, x2, x6, x7]), (x4, x6, [x0 ||| x3, x0, x1, x2, x5, x7]), (x4, x7, [x0 ||| x3, x0, x1, x2, x5, x6]), (x5, x6, [x0 ||| x3, x0, x1, x2, x4, x7]), (x5, x7, [x0 ||| x3, x0, x1, x2, x4, x6]), (x6, x7, [x0 ||| x3, x0, x1, x2, x4, x5])] := by
  decide +kernel

theorem t34 : optimized 8 1 [x0 ||| x3, x0, x1, x2, x4, x5, x6, x7] = false := by
  rw [optimized.eq_2, t34_pairs]
  simp only [List.any_cons, List.any_nil, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, t24, t25, t26, t27, t28, t29, t30, t31, t32, t33, Bool.or_false]
  all_goals decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t35 : optimized 8 0 [x0 ||| x3, x0, x3, x1, x2, x4, x5, x6, x7] = false := by
  decide +kernel

theorem t36 : dispatch 2 (optimized 8) x0 x3 [x1, x2, x4, x5, x6, x7] = false := by
  simp only [dispatch, ops, List.any_cons, List.any_nil, Nat.reduceSub, t5, t34, t35, Bool.and_false, Bool.or_false]
  all_goals decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t37 : optimized 8 0 [x0 &&& x4, x0, x4, x1, x2, x3, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t38 : optimized 8 0 [x0 ||| x4, x0, x4, x1, x2, x3, x5, x6, x7] = false := by
  decide +kernel

theorem t39 : dispatch 2 (optimized 8) x0 x4 [x1, x2, x3, x5, x6, x7] = false := by
  simp only [dispatch, ops, List.any_cons, List.any_nil, Nat.reduceSub, t37, t38, Bool.and_false, Bool.or_false]
  all_goals decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t40 : dispatch 0 (optimized 7) (x0 &&& x5) x0 [x5, x1, x2, x3, x4, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t41 : dispatch 0 (optimized 7) (x0 &&& x5) x5 [x0, x1, x2, x3, x4, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t42 : dispatch 0 (optimized 7) (x0 &&& x5) x1 [x0, x5, x2, x3, x4, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t43 : dispatch 0 (optimized 7) (x0 &&& x5) x2 [x0, x5, x1, x3, x4, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t44 : dispatch 0 (optimized 7) (x0 &&& x5) x3 [x0, x5, x1, x2, x4, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t45 : dispatch 0 (optimized 7) (x0 &&& x5) x4 [x0, x5, x1, x2, x3, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t46 : dispatch 0 (optimized 7) (x0 &&& x5) x6 [x0, x5, x1, x2, x3, x4, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t47 : dispatch 0 (optimized 7) (x0 &&& x5) x7 [x0, x5, x1, x2, x3, x4, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t48 : dispatch 0 (optimized 7) x0 x5 [x0 &&& x5, x1, x2, x3, x4, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t49 : dispatch 0 (optimized 7) x0 x1 [x0 &&& x5, x5, x2, x3, x4, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t50 : dispatch 0 (optimized 7) x0 x2 [x0 &&& x5, x5, x1, x3, x4, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t51 : dispatch 0 (optimized 7) x0 x3 [x0 &&& x5, x5, x1, x2, x4, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t52 : dispatch 0 (optimized 7) x0 x4 [x0 &&& x5, x5, x1, x2, x3, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t53 : dispatch 0 (optimized 7) x0 x6 [x0 &&& x5, x5, x1, x2, x3, x4, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t54 : dispatch 0 (optimized 7) x0 x7 [x0 &&& x5, x5, x1, x2, x3, x4, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t55 : dispatch 0 (optimized 7) x5 x1 [x0 &&& x5, x0, x2, x3, x4, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t56 : dispatch 0 (optimized 7) x5 x2 [x0 &&& x5, x0, x1, x3, x4, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t57 : dispatch 0 (optimized 7) x5 x3 [x0 &&& x5, x0, x1, x2, x4, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t58 : dispatch 0 (optimized 7) x5 x4 [x0 &&& x5, x0, x1, x2, x3, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t59 : dispatch 0 (optimized 7) x5 x6 [x0 &&& x5, x0, x1, x2, x3, x4, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t60 : dispatch 0 (optimized 7) x5 x7 [x0 &&& x5, x0, x1, x2, x3, x4, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t61 : dispatch 0 (optimized 7) x1 x2 [x0 &&& x5, x0, x5, x3, x4, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t62 : dispatch 0 (optimized 7) x1 x3 [x0 &&& x5, x0, x5, x2, x4, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t63 : dispatch 0 (optimized 7) x1 x4 [x0 &&& x5, x0, x5, x2, x3, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t64 : dispatch 0 (optimized 7) x1 x6 [x0 &&& x5, x0, x5, x2, x3, x4, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t65 : dispatch 0 (optimized 7) x1 x7 [x0 &&& x5, x0, x5, x2, x3, x4, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t66 : dispatch 0 (optimized 7) x2 x3 [x0 &&& x5, x0, x5, x1, x4, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t67 : dispatch 0 (optimized 7) x2 x4 [x0 &&& x5, x0, x5, x1, x3, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t68 : dispatch 0 (optimized 7) x2 x6 [x0 &&& x5, x0, x5, x1, x3, x4, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t69 : dispatch 0 (optimized 7) x2 x7 [x0 &&& x5, x0, x5, x1, x3, x4, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t70 : dispatch 0 (optimized 7) x3 x4 [x0 &&& x5, x0, x5, x1, x2, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t71 : dispatch 0 (optimized 7) x3 x6 [x0 &&& x5, x0, x5, x1, x2, x4, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t72 : dispatch 0 (optimized 7) x3 x7 [x0 &&& x5, x0, x5, x1, x2, x4, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t73 : dispatch 0 (optimized 7) x4 x6 [x0 &&& x5, x0, x5, x1, x2, x3, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t74 : dispatch 0 (optimized 7) x4 x7 [x0 &&& x5, x0, x5, x1, x2, x3, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t75 : dispatch 0 (optimized 7) x6 x7 [x0 &&& x5, x0, x5, x1, x2, x3, x4] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
theorem t76_pairs : pairs [x0 &&& x5, x0, x5, x1, x2, x3, x4, x6, x7] = [(x0 &&& x5, x0, [x5, x1, x2, x3, x4, x6, x7]), (x0 &&& x5, x5, [x0, x1, x2, x3, x4, x6, x7]), (x0 &&& x5, x1, [x0, x5, x2, x3, x4, x6, x7]), (x0 &&& x5, x2, [x0, x5, x1, x3, x4, x6, x7]), (x0 &&& x5, x3, [x0, x5, x1, x2, x4, x6, x7]), (x0 &&& x5, x4, [x0, x5, x1, x2, x3, x6, x7]), (x0 &&& x5, x6, [x0, x5, x1, x2, x3, x4, x7]), (x0 &&& x5, x7, [x0, x5, x1, x2, x3, x4, x6]), (x0, x5, [x0 &&& x5, x1, x2, x3, x4, x6, x7]), (x0, x1, [x0 &&& x5, x5, x2, x3, x4, x6, x7]), (x0, x2, [x0 &&& x5, x5, x1, x3, x4, x6, x7]), (x0, x3, [x0 &&& x5, x5, x1, x2, x4, x6, x7]), (x0, x4, [x0 &&& x5, x5, x1, x2, x3, x6, x7]), (x0, x6, [x0 &&& x5, x5, x1, x2, x3, x4, x7]), (x0, x7, [x0 &&& x5, x5, x1, x2, x3, x4, x6]), (x5, x1, [x0 &&& x5, x0, x2, x3, x4, x6, x7]), (x5, x2, [x0 &&& x5, x0, x1, x3, x4, x6, x7]), (x5, x3, [x0 &&& x5, x0, x1, x2, x4, x6, x7]), (x5, x4, [x0 &&& x5, x0, x1, x2, x3, x6, x7]), (x5, x6, [x0 &&& x5, x0, x1, x2, x3, x4, x7]), (x5, x7, [x0 &&& x5, x0, x1, x2, x3, x4, x6]), (x1, x2, [x0 &&& x5, x0, x5, x3, x4, x6, x7]), (x1, x3, [x0 &&& x5, x0, x5, x2, x4, x6, x7]), (x1, x4, [x0 &&& x5, x0, x5, x2, x3, x6, x7]), (x1, x6, [x0 &&& x5, x0, x5, x2, x3, x4, x7]), (x1, x7, [x0 &&& x5, x0, x5, x2, x3, x4, x6]), (x2, x3, [x0 &&& x5, x0, x5, x1, x4, x6, x7]), (x2, x4, [x0 &&& x5, x0, x5, x1, x3, x6, x7]), (x2, x6, [x0 &&& x5, x0, x5, x1, x3, x4, x7]), (x2, x7, [x0 &&& x5, x0, x5, x1, x3, x4, x6]), (x3, x4, [x0 &&& x5, x0, x5, x1, x2, x6, x7]), (x3, x6, [x0 &&& x5, x0, x5, x1, x2, x4, x7]), (x3, x7, [x0 &&& x5, x0, x5, x1, x2, x4, x6]), (x4, x6, [x0 &&& x5, x0, x5, x1, x2, x3, x7]), (x4, x7, [x0 &&& x5, x0, x5, x1, x2, x3, x6]), (x6, x7, [x0 &&& x5, x0, x5, x1, x2, x3, x4])] := by
  decide +kernel

theorem t76 : optimized 8 0 [x0 &&& x5, x0, x5, x1, x2, x3, x4, x6, x7] = false := by
  rw [optimized.eq_2, t76_pairs]
  simp only [List.any_cons, List.any_nil, t40, t41, t42, t43, t44, t45, t46, t47, t48, t49, t50, t51, t52, t53, t54, t55, t56, t57, t58, t59, t60, t61, t62, t63, t64, t65, t66, t67, t68, t69, t70, t71, t72, t73, t74, t75, Bool.or_false]
  all_goals decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t77 : dispatch 0 (optimized 7) (x0 ||| x5) x0 [x5, x1, x2, x3, x4, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t78 : dispatch 0 (optimized 7) (x0 ||| x5) x5 [x0, x1, x2, x3, x4, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t79 : dispatch 0 (optimized 7) (x0 ||| x5) x1 [x0, x5, x2, x3, x4, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t80 : dispatch 0 (optimized 7) (x0 ||| x5) x2 [x0, x5, x1, x3, x4, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t81 : dispatch 0 (optimized 7) (x0 ||| x5) x3 [x0, x5, x1, x2, x4, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t82 : dispatch 0 (optimized 7) (x0 ||| x5) x4 [x0, x5, x1, x2, x3, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t83 : dispatch 0 (optimized 7) (x0 ||| x5) x6 [x0, x5, x1, x2, x3, x4, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t84 : dispatch 0 (optimized 7) (x0 ||| x5) x7 [x0, x5, x1, x2, x3, x4, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t85 : dispatch 0 (optimized 7) x0 x5 [x0 ||| x5, x1, x2, x3, x4, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t86 : dispatch 0 (optimized 7) x0 x1 [x0 ||| x5, x5, x2, x3, x4, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t87 : dispatch 0 (optimized 7) x0 x2 [x0 ||| x5, x5, x1, x3, x4, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t88 : dispatch 0 (optimized 7) x0 x3 [x0 ||| x5, x5, x1, x2, x4, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t89 : dispatch 0 (optimized 7) x0 x4 [x0 ||| x5, x5, x1, x2, x3, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t90 : dispatch 0 (optimized 7) x0 x6 [x0 ||| x5, x5, x1, x2, x3, x4, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t91 : dispatch 0 (optimized 7) x0 x7 [x0 ||| x5, x5, x1, x2, x3, x4, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t92 : dispatch 0 (optimized 7) x5 x1 [x0 ||| x5, x0, x2, x3, x4, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t93 : dispatch 0 (optimized 7) x5 x2 [x0 ||| x5, x0, x1, x3, x4, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t94 : dispatch 0 (optimized 7) x5 x3 [x0 ||| x5, x0, x1, x2, x4, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t95 : dispatch 0 (optimized 7) x5 x4 [x0 ||| x5, x0, x1, x2, x3, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t96 : dispatch 0 (optimized 7) x5 x6 [x0 ||| x5, x0, x1, x2, x3, x4, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t97 : dispatch 0 (optimized 7) x5 x7 [x0 ||| x5, x0, x1, x2, x3, x4, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t98 : dispatch 0 (optimized 7) x1 x2 [x0 ||| x5, x0, x5, x3, x4, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t99 : dispatch 0 (optimized 7) x1 x3 [x0 ||| x5, x0, x5, x2, x4, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t100 : dispatch 0 (optimized 7) x1 x4 [x0 ||| x5, x0, x5, x2, x3, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t101 : dispatch 0 (optimized 7) x1 x6 [x0 ||| x5, x0, x5, x2, x3, x4, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t102 : dispatch 0 (optimized 7) x1 x7 [x0 ||| x5, x0, x5, x2, x3, x4, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t103 : dispatch 0 (optimized 7) x2 x3 [x0 ||| x5, x0, x5, x1, x4, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t104 : dispatch 0 (optimized 7) x2 x4 [x0 ||| x5, x0, x5, x1, x3, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t105 : dispatch 0 (optimized 7) x2 x6 [x0 ||| x5, x0, x5, x1, x3, x4, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t106 : dispatch 0 (optimized 7) x2 x7 [x0 ||| x5, x0, x5, x1, x3, x4, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t107 : dispatch 0 (optimized 7) x3 x4 [x0 ||| x5, x0, x5, x1, x2, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t108 : dispatch 0 (optimized 7) x3 x6 [x0 ||| x5, x0, x5, x1, x2, x4, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t109 : dispatch 0 (optimized 7) x3 x7 [x0 ||| x5, x0, x5, x1, x2, x4, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t110 : dispatch 0 (optimized 7) x4 x6 [x0 ||| x5, x0, x5, x1, x2, x3, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t111 : dispatch 0 (optimized 7) x4 x7 [x0 ||| x5, x0, x5, x1, x2, x3, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t112 : dispatch 0 (optimized 7) x6 x7 [x0 ||| x5, x0, x5, x1, x2, x3, x4] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
theorem t113_pairs : pairs [x0 ||| x5, x0, x5, x1, x2, x3, x4, x6, x7] = [(x0 ||| x5, x0, [x5, x1, x2, x3, x4, x6, x7]), (x0 ||| x5, x5, [x0, x1, x2, x3, x4, x6, x7]), (x0 ||| x5, x1, [x0, x5, x2, x3, x4, x6, x7]), (x0 ||| x5, x2, [x0, x5, x1, x3, x4, x6, x7]), (x0 ||| x5, x3, [x0, x5, x1, x2, x4, x6, x7]), (x0 ||| x5, x4, [x0, x5, x1, x2, x3, x6, x7]), (x0 ||| x5, x6, [x0, x5, x1, x2, x3, x4, x7]), (x0 ||| x5, x7, [x0, x5, x1, x2, x3, x4, x6]), (x0, x5, [x0 ||| x5, x1, x2, x3, x4, x6, x7]), (x0, x1, [x0 ||| x5, x5, x2, x3, x4, x6, x7]), (x0, x2, [x0 ||| x5, x5, x1, x3, x4, x6, x7]), (x0, x3, [x0 ||| x5, x5, x1, x2, x4, x6, x7]), (x0, x4, [x0 ||| x5, x5, x1, x2, x3, x6, x7]), (x0, x6, [x0 ||| x5, x5, x1, x2, x3, x4, x7]), (x0, x7, [x0 ||| x5, x5, x1, x2, x3, x4, x6]), (x5, x1, [x0 ||| x5, x0, x2, x3, x4, x6, x7]), (x5, x2, [x0 ||| x5, x0, x1, x3, x4, x6, x7]), (x5, x3, [x0 ||| x5, x0, x1, x2, x4, x6, x7]), (x5, x4, [x0 ||| x5, x0, x1, x2, x3, x6, x7]), (x5, x6, [x0 ||| x5, x0, x1, x2, x3, x4, x7]), (x5, x7, [x0 ||| x5, x0, x1, x2, x3, x4, x6]), (x1, x2, [x0 ||| x5, x0, x5, x3, x4, x6, x7]), (x1, x3, [x0 ||| x5, x0, x5, x2, x4, x6, x7]), (x1, x4, [x0 ||| x5, x0, x5, x2, x3, x6, x7]), (x1, x6, [x0 ||| x5, x0, x5, x2, x3, x4, x7]), (x1, x7, [x0 ||| x5, x0, x5, x2, x3, x4, x6]), (x2, x3, [x0 ||| x5, x0, x5, x1, x4, x6, x7]), (x2, x4, [x0 ||| x5, x0, x5, x1, x3, x6, x7]), (x2, x6, [x0 ||| x5, x0, x5, x1, x3, x4, x7]), (x2, x7, [x0 ||| x5, x0, x5, x1, x3, x4, x6]), (x3, x4, [x0 ||| x5, x0, x5, x1, x2, x6, x7]), (x3, x6, [x0 ||| x5, x0, x5, x1, x2, x4, x7]), (x3, x7, [x0 ||| x5, x0, x5, x1, x2, x4, x6]), (x4, x6, [x0 ||| x5, x0, x5, x1, x2, x3, x7]), (x4, x7, [x0 ||| x5, x0, x5, x1, x2, x3, x6]), (x6, x7, [x0 ||| x5, x0, x5, x1, x2, x3, x4])] := by
  decide +kernel

theorem t113 : optimized 8 0 [x0 ||| x5, x0, x5, x1, x2, x3, x4, x6, x7] = false := by
  rw [optimized.eq_2, t113_pairs]
  simp only [List.any_cons, List.any_nil, t77, t78, t79, t80, t81, t82, t83, t84, t85, t86, t87, t88, t89, t90, t91, t92, t93, t94, t95, t96, t97, t98, t99, t100, t101, t102, t103, t104, t105, t106, t107, t108, t109, t110, t111, t112, Bool.or_false]
  all_goals decide +kernel

theorem t114 : dispatch 2 (optimized 8) x0 x5 [x1, x2, x3, x4, x6, x7] = false := by
  simp only [dispatch, ops, List.any_cons, List.any_nil, Nat.reduceSub, t76, t113, Bool.and_false, Bool.or_false]
  all_goals decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t115 : optimized 8 0 [x0 &&& x6, x0, x6, x1, x2, x3, x4, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t116 : dispatch 2 (optimized 7) (x0 ||| x6) x1 [x2, x3, x4, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t117 : dispatch 2 (optimized 7) (x0 ||| x6) x2 [x1, x3, x4, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t118 : dispatch 2 (optimized 7) (x0 ||| x6) x3 [x1, x2, x4, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t119 : dispatch 2 (optimized 7) (x0 ||| x6) x4 [x1, x2, x3, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t120 : dispatch 2 (optimized 7) (x0 ||| x6) x5 [x1, x2, x3, x4, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t121 : dispatch 2 (optimized 7) (x0 ||| x6) x7 [x1, x2, x3, x4, x5] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t122 : dispatch 2 (optimized 7) x1 x2 [x0 ||| x6, x3, x4, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t123 : optimized 7 0 [x1 &&& x3, x1, x3, x0 ||| x6, x2, x4, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t124 : dispatch 1 (optimized 6) (x1 ||| x3) x1 [x0 ||| x6, x2, x4, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t125 : dispatch 1 (optimized 6) (x1 ||| x3) (x0 ||| x6) [x1, x2, x4, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t126 : dispatch 1 (optimized 6) (x1 ||| x3) x2 [x1, x0 ||| x6, x4, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t127 : dispatch 1 (optimized 6) (x1 ||| x3) x4 [x1, x0 ||| x6, x2, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t128 : dispatch 1 (optimized 6) (x1 ||| x3) x5 [x1, x0 ||| x6, x2, x4, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t129 : dispatch 1 (optimized 6) (x1 ||| x3) x7 [x1, x0 ||| x6, x2, x4, x5] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t130 : dispatch 1 (optimized 6) x1 (x0 ||| x6) [x1 ||| x3, x2, x4, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t131 : dispatch 1 (optimized 6) x1 x2 [x1 ||| x3, x0 ||| x6, x4, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t132 : dispatch 1 (optimized 6) x1 x4 [x1 ||| x3, x0 ||| x6, x2, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t133 : dispatch 1 (optimized 6) x1 x5 [x1 ||| x3, x0 ||| x6, x2, x4, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t134 : dispatch 1 (optimized 6) x1 x7 [x1 ||| x3, x0 ||| x6, x2, x4, x5] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t135 : dispatch 1 (optimized 6) (x0 ||| x6) x2 [x1 ||| x3, x1, x4, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t136 : dispatch 1 (optimized 6) (x0 ||| x6) x4 [x1 ||| x3, x1, x2, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t137 : dispatch 1 (optimized 6) (x0 ||| x6) x5 [x1 ||| x3, x1, x2, x4, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t138 : dispatch 1 (optimized 6) (x0 ||| x6) x7 [x1 ||| x3, x1, x2, x4, x5] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t139 : dispatch 1 (optimized 6) x2 x4 [x1 ||| x3, x1, x0 ||| x6, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t140 : dispatch 1 (optimized 6) x2 x5 [x1 ||| x3, x1, x0 ||| x6, x4, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t141 : dispatch 1 (optimized 6) x2 x7 [x1 ||| x3, x1, x0 ||| x6, x4, x5] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t142 : dispatch 1 (optimized 6) x4 x5 [x1 ||| x3, x1, x0 ||| x6, x2, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t143 : dispatch 1 (optimized 6) x4 x7 [x1 ||| x3, x1, x0 ||| x6, x2, x5] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t144 : dispatch 1 (optimized 6) x5 x7 [x1 ||| x3, x1, x0 ||| x6, x2, x4] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
theorem t145_pairs : pairs [x1 ||| x3, x1, x0 ||| x6, x2, x4, x5, x7] = [(x1 ||| x3, x1, [x0 ||| x6, x2, x4, x5, x7]), (x1 ||| x3, x0 ||| x6, [x1, x2, x4, x5, x7]), (x1 ||| x3, x2, [x1, x0 ||| x6, x4, x5, x7]), (x1 ||| x3, x4, [x1, x0 ||| x6, x2, x5, x7]), (x1 ||| x3, x5, [x1, x0 ||| x6, x2, x4, x7]), (x1 ||| x3, x7, [x1, x0 ||| x6, x2, x4, x5]), (x1, x0 ||| x6, [x1 ||| x3, x2, x4, x5, x7]), (x1, x2, [x1 ||| x3, x0 ||| x6, x4, x5, x7]), (x1, x4, [x1 ||| x3, x0 ||| x6, x2, x5, x7]), (x1, x5, [x1 ||| x3, x0 ||| x6, x2, x4, x7]), (x1, x7, [x1 ||| x3, x0 ||| x6, x2, x4, x5]), (x0 ||| x6, x2, [x1 ||| x3, x1, x4, x5, x7]), (x0 ||| x6, x4, [x1 ||| x3, x1, x2, x5, x7]), (x0 ||| x6, x5, [x1 ||| x3, x1, x2, x4, x7]), (x0 ||| x6, x7, [x1 ||| x3, x1, x2, x4, x5]), (x2, x4, [x1 ||| x3, x1, x0 ||| x6, x5, x7]), (x2, x5, [x1 ||| x3, x1, x0 ||| x6, x4, x7]), (x2, x7, [x1 ||| x3, x1, x0 ||| x6, x4, x5]), (x4, x5, [x1 ||| x3, x1, x0 ||| x6, x2, x7]), (x4, x7, [x1 ||| x3, x1, x0 ||| x6, x2, x5]), (x5, x7, [x1 ||| x3, x1, x0 ||| x6, x2, x4])] := by
  decide +kernel

theorem t145 : optimized 7 1 [x1 ||| x3, x1, x0 ||| x6, x2, x4, x5, x7] = false := by
  rw [optimized.eq_2, t145_pairs]
  simp only [List.any_cons, List.any_nil, t124, t125, t126, t127, t128, t129, t130, t131, t132, t133, t134, t135, t136, t137, t138, t139, t140, t141, t142, t143, t144, Bool.or_false]
  all_goals decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t146 : optimized 7 0 [x1 ||| x3, x1, x3, x0 ||| x6, x2, x4, x5, x7] = false := by
  decide +kernel

theorem t147 : dispatch 2 (optimized 7) x1 x3 [x0 ||| x6, x2, x4, x5, x7] = false := by
  simp only [dispatch, ops, List.any_cons, List.any_nil, Nat.reduceSub, t123, t145, t146, Bool.and_false, Bool.or_false]
  all_goals decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t148 : dispatch 2 (optimized 7) x1 x4 [x0 ||| x6, x2, x3, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t149 : dispatch 2 (optimized 7) x1 x5 [x0 ||| x6, x2, x3, x4, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t150 : optimized 7 0 [x1 &&& x7, x1, x7, x0 ||| x6, x2, x3, x4, x5] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t151 : optimized 7 2 [x1 ||| x7, x0 ||| x6, x2, x3, x4, x5] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t152 : optimized 7 1 [x1 ||| x7, x1, x0 ||| x6, x2, x3, x4, x5] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t153 : optimized 7 1 [x1 ||| x7, x7, x0 ||| x6, x2, x3, x4, x5] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t154 : optimized 7 0 [x1 ||| x7, x1, x7, x0 ||| x6, x2, x3, x4, x5] = false := by
  decide +kernel

theorem t155 : dispatch 2 (optimized 7) x1 x7 [x0 ||| x6, x2, x3, x4, x5] = false := by
  simp only [dispatch, ops, List.any_cons, List.any_nil, Nat.reduceSub, t150, t151, t152, t153, t154, Bool.and_false, Bool.or_false]
  all_goals decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t156 : dispatch 2 (optimized 7) x2 x3 [x0 ||| x6, x1, x4, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t157 : optimized 7 0 [x2 &&& x4, x2, x4, x0 ||| x6, x1, x3, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t158 : optimized 7 2 [x2 ||| x4, x0 ||| x6, x1, x3, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t159 : optimized 7 1 [x2 ||| x4, x2, x0 ||| x6, x1, x3, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t160 : optimized 7 1 [x2 ||| x4, x4, x0 ||| x6, x1, x3, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t161 : optimized 7 0 [x2 ||| x4, x2, x4, x0 ||| x6, x1, x3, x5, x7] = false := by
  decide +kernel

theorem t162 : dispatch 2 (optimized 7) x2 x4 [x0 ||| x6, x1, x3, x5, x7] = false := by
  simp only [dispatch, ops, List.any_cons, List.any_nil, Nat.reduceSub, t157, t158, t159, t160, t161, Bool.and_false, Bool.or_false]
  all_goals decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t163 : dispatch 2 (optimized 7) x2 x5 [x0 ||| x6, x1, x3, x4, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t164 : dispatch 2 (optimized 7) x2 x7 [x0 ||| x6, x1, x3, x4, x5] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t165 : dispatch 1 (optimized 6) (x3 &&& x4) x4 [x0 ||| x6, x1, x2, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t166 : dispatch 1 (optimized 6) (x3 &&& x4) (x0 ||| x6) [x4, x1, x2, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t167 : dispatch 1 (optimized 6) (x3 &&& x4) x1 [x4, x0 ||| x6, x2, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t168 : dispatch 1 (optimized 6) (x3 &&& x4) x2 [x4, x0 ||| x6, x1, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t169 : dispatch 1 (optimized 6) (x3 &&& x4) x5 [x4, x0 ||| x6, x1, x2, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t170 : dispatch 1 (optimized 6) (x3 &&& x4) x7 [x4, x0 ||| x6, x1, x2, x5] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t171 : dispatch 1 (optimized 6) x4 (x0 ||| x6) [x3 &&& x4, x1, x2, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t172 : dispatch 1 (optimized 6) x4 x1 [x3 &&& x4, x0 ||| x6, x2, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t173 : dispatch 1 (optimized 6) x4 x2 [x3 &&& x4, x0 ||| x6, x1, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t174 : dispatch 1 (optimized 6) x4 x5 [x3 &&& x4, x0 ||| x6, x1, x2, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t175 : dispatch 1 (optimized 6) x4 x7 [x3 &&& x4, x0 ||| x6, x1, x2, x5] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t176 : dispatch 1 (optimized 6) (x0 ||| x6) x1 [x3 &&& x4, x4, x2, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t177 : dispatch 1 (optimized 6) (x0 ||| x6) x2 [x3 &&& x4, x4, x1, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t178 : dispatch 1 (optimized 6) (x0 ||| x6) x5 [x3 &&& x4, x4, x1, x2, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t179 : dispatch 1 (optimized 6) (x0 ||| x6) x7 [x3 &&& x4, x4, x1, x2, x5] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t180 : dispatch 1 (optimized 6) x1 x2 [x3 &&& x4, x4, x0 ||| x6, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t181 : dispatch 1 (optimized 6) x1 x5 [x3 &&& x4, x4, x0 ||| x6, x2, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t182 : dispatch 1 (optimized 6) x1 x7 [x3 &&& x4, x4, x0 ||| x6, x2, x5] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t183 : dispatch 1 (optimized 6) x2 x5 [x3 &&& x4, x4, x0 ||| x6, x1, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t184 : dispatch 1 (optimized 6) x2 x7 [x3 &&& x4, x4, x0 ||| x6, x1, x5] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t185 : dispatch 1 (optimized 6) x5 x7 [x3 &&& x4, x4, x0 ||| x6, x1, x2] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
theorem t186_pairs : pairs [x3 &&& x4, x4, x0 ||| x6, x1, x2, x5, x7] = [(x3 &&& x4, x4, [x0 ||| x6, x1, x2, x5, x7]), (x3 &&& x4, x0 ||| x6, [x4, x1, x2, x5, x7]), (x3 &&& x4, x1, [x4, x0 ||| x6, x2, x5, x7]), (x3 &&& x4, x2, [x4, x0 ||| x6, x1, x5, x7]), (x3 &&& x4, x5, [x4, x0 ||| x6, x1, x2, x7]), (x3 &&& x4, x7, [x4, x0 ||| x6, x1, x2, x5]), (x4, x0 ||| x6, [x3 &&& x4, x1, x2, x5, x7]), (x4, x1, [x3 &&& x4, x0 ||| x6, x2, x5, x7]), (x4, x2, [x3 &&& x4, x0 ||| x6, x1, x5, x7]), (x4, x5, [x3 &&& x4, x0 ||| x6, x1, x2, x7]), (x4, x7, [x3 &&& x4, x0 ||| x6, x1, x2, x5]), (x0 ||| x6, x1, [x3 &&& x4, x4, x2, x5, x7]), (x0 ||| x6, x2, [x3 &&& x4, x4, x1, x5, x7]), (x0 ||| x6, x5, [x3 &&& x4, x4, x1, x2, x7]), (x0 ||| x6, x7, [x3 &&& x4, x4, x1, x2, x5]), (x1, x2, [x3 &&& x4, x4, x0 ||| x6, x5, x7]), (x1, x5, [x3 &&& x4, x4, x0 ||| x6, x2, x7]), (x1, x7, [x3 &&& x4, x4, x0 ||| x6, x2, x5]), (x2, x5, [x3 &&& x4, x4, x0 ||| x6, x1, x7]), (x2, x7, [x3 &&& x4, x4, x0 ||| x6, x1, x5]), (x5, x7, [x3 &&& x4, x4, x0 ||| x6, x1, x2])] := by
  decide +kernel

theorem t186 : optimized 7 1 [x3 &&& x4, x4, x0 ||| x6, x1, x2, x5, x7] = false := by
  rw [optimized.eq_2, t186_pairs]
  simp only [List.any_cons, List.any_nil, t165, t166, t167, t168, t169, t170, t171, t172, t173, t174, t175, t176, t177, t178, t179, t180, t181, t182, t183, t184, t185, Bool.or_false]
  all_goals decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t187 : optimized 7 0 [x3 &&& x4, x3, x4, x0 ||| x6, x1, x2, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t188 : optimized 7 0 [x3 ||| x4, x3, x4, x0 ||| x6, x1, x2, x5, x7] = false := by
  decide +kernel

theorem t189 : dispatch 2 (optimized 7) x3 x4 [x0 ||| x6, x1, x2, x5, x7] = false := by
  simp only [dispatch, ops, List.any_cons, List.any_nil, Nat.reduceSub, t186, t187, t188, Bool.and_false, Bool.or_false]
  all_goals decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t190 : dispatch 2 (optimized 7) x3 x5 [x0 ||| x6, x1, x2, x4, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t191 : dispatch 2 (optimized 7) x3 x7 [x0 ||| x6, x1, x2, x4, x5] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t192 : dispatch 2 (optimized 7) x4 x5 [x0 ||| x6, x1, x2, x3, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t193 : dispatch 2 (optimized 7) x4 x7 [x0 ||| x6, x1, x2, x3, x5] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t194 : dispatch 2 (optimized 7) x5 x7 [x0 ||| x6, x1, x2, x3, x4] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
theorem t195_pairs : pairs [x0 ||| x6, x1, x2, x3, x4, x5, x7] = [(x0 ||| x6, x1, [x2, x3, x4, x5, x7]), (x0 ||| x6, x2, [x1, x3, x4, x5, x7]), (x0 ||| x6, x3, [x1, x2, x4, x5, x7]), (x0 ||| x6, x4, [x1, x2, x3, x5, x7]), (x0 ||| x6, x5, [x1, x2, x3, x4, x7]), (x0 ||| x6, x7, [x1, x2, x3, x4, x5]), (x1, x2, [x0 ||| x6, x3, x4, x5, x7]), (x1, x3, [x0 ||| x6, x2, x4, x5, x7]), (x1, x4, [x0 ||| x6, x2, x3, x5, x7]), (x1, x5, [x0 ||| x6, x2, x3, x4, x7]), (x1, x7, [x0 ||| x6, x2, x3, x4, x5]), (x2, x3, [x0 ||| x6, x1, x4, x5, x7]), (x2, x4, [x0 ||| x6, x1, x3, x5, x7]), (x2, x5, [x0 ||| x6, x1, x3, x4, x7]), (x2, x7, [x0 ||| x6, x1, x3, x4, x5]), (x3, x4, [x0 ||| x6, x1, x2, x5, x7]), (x3, x5, [x0 ||| x6, x1, x2, x4, x7]), (x3, x7, [x0 ||| x6, x1, x2, x4, x5]), (x4, x5, [x0 ||| x6, x1, x2, x3, x7]), (x4, x7, [x0 ||| x6, x1, x2, x3, x5]), (x5, x7, [x0 ||| x6, x1, x2, x3, x4])] := by
  decide +kernel

theorem t195 : optimized 8 2 [x0 ||| x6, x1, x2, x3, x4, x5, x7] = false := by
  rw [optimized.eq_2, t195_pairs]
  simp only [List.any_cons, List.any_nil, t116, t117, t118, t119, t120, t121, t122, t147, t148, t149, t155, t156, t162, t163, t164, t189, t190, t191, t192, t193, t194, Bool.or_false]
  all_goals decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t196 : dispatch 1 (optimized 7) (x0 ||| x6) x0 [x1, x2, x3, x4, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t197 : dispatch 1 (optimized 7) (x0 ||| x6) x1 [x0, x2, x3, x4, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t198 : dispatch 1 (optimized 7) (x0 ||| x6) x2 [x0, x1, x3, x4, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t199 : dispatch 1 (optimized 7) (x0 ||| x6) x3 [x0, x1, x2, x4, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t200 : dispatch 1 (optimized 7) (x0 ||| x6) x4 [x0, x1, x2, x3, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t201 : dispatch 1 (optimized 7) (x0 ||| x6) x5 [x0, x1, x2, x3, x4, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t202 : dispatch 1 (optimized 7) (x0 ||| x6) x7 [x0, x1, x2, x3, x4, x5] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t203 : dispatch 1 (optimized 7) x0 x1 [x0 ||| x6, x2, x3, x4, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t204 : dispatch 1 (optimized 7) x0 x2 [x0 ||| x6, x1, x3, x4, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t205 : dispatch 1 (optimized 7) x0 x3 [x0 ||| x6, x1, x2, x4, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t206 : dispatch 1 (optimized 7) x0 x4 [x0 ||| x6, x1, x2, x3, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t207 : dispatch 1 (optimized 7) x0 x5 [x0 ||| x6, x1, x2, x3, x4, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t208 : dispatch 1 (optimized 7) x0 x7 [x0 ||| x6, x1, x2, x3, x4, x5] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t209 : dispatch 1 (optimized 7) x1 x2 [x0 ||| x6, x0, x3, x4, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t210 : dispatch 1 (optimized 7) x1 x3 [x0 ||| x6, x0, x2, x4, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t211 : dispatch 1 (optimized 7) x1 x4 [x0 ||| x6, x0, x2, x3, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t212 : dispatch 1 (optimized 7) x1 x5 [x0 ||| x6, x0, x2, x3, x4, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t213 : dispatch 1 (optimized 7) x1 x7 [x0 ||| x6, x0, x2, x3, x4, x5] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t214 : dispatch 1 (optimized 7) x2 x3 [x0 ||| x6, x0, x1, x4, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t215 : dispatch 1 (optimized 7) x2 x4 [x0 ||| x6, x0, x1, x3, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t216 : dispatch 1 (optimized 7) x2 x5 [x0 ||| x6, x0, x1, x3, x4, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t217 : dispatch 1 (optimized 7) x2 x7 [x0 ||| x6, x0, x1, x3, x4, x5] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t218 : dispatch 1 (optimized 7) x3 x4 [x0 ||| x6, x0, x1, x2, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t219 : dispatch 1 (optimized 7) x3 x5 [x0 ||| x6, x0, x1, x2, x4, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t220 : dispatch 1 (optimized 7) x3 x7 [x0 ||| x6, x0, x1, x2, x4, x5] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t221 : dispatch 1 (optimized 7) x4 x5 [x0 ||| x6, x0, x1, x2, x3, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t222 : dispatch 1 (optimized 7) x4 x7 [x0 ||| x6, x0, x1, x2, x3, x5] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t223 : dispatch 1 (optimized 7) x5 x7 [x0 ||| x6, x0, x1, x2, x3, x4] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
theorem t224_pairs : pairs [x0 ||| x6, x0, x1, x2, x3, x4, x5, x7] = [(x0 ||| x6, x0, [x1, x2, x3, x4, x5, x7]), (x0 ||| x6, x1, [x0, x2, x3, x4, x5, x7]), (x0 ||| x6, x2, [x0, x1, x3, x4, x5, x7]), (x0 ||| x6, x3, [x0, x1, x2, x4, x5, x7]), (x0 ||| x6, x4, [x0, x1, x2, x3, x5, x7]), (x0 ||| x6, x5, [x0, x1, x2, x3, x4, x7]), (x0 ||| x6, x7, [x0, x1, x2, x3, x4, x5]), (x0, x1, [x0 ||| x6, x2, x3, x4, x5, x7]), (x0, x2, [x0 ||| x6, x1, x3, x4, x5, x7]), (x0, x3, [x0 ||| x6, x1, x2, x4, x5, x7]), (x0, x4, [x0 ||| x6, x1, x2, x3, x5, x7]), (x0, x5, [x0 ||| x6, x1, x2, x3, x4, x7]), (x0, x7, [x0 ||| x6, x1, x2, x3, x4, x5]), (x1, x2, [x0 ||| x6, x0, x3, x4, x5, x7]), (x1, x3, [x0 ||| x6, x0, x2, x4, x5, x7]), (x1, x4, [x0 ||| x6, x0, x2, x3, x5, x7]), (x1, x5, [x0 ||| x6, x0, x2, x3, x4, x7]), (x1, x7, [x0 ||| x6, x0, x2, x3, x4, x5]), (x2, x3, [x0 ||| x6, x0, x1, x4, x5, x7]), (x2, x4, [x0 ||| x6, x0, x1, x3, x5, x7]), (x2, x5, [x0 ||| x6, x0, x1, x3, x4, x7]), (x2, x7, [x0 ||| x6, x0, x1, x3, x4, x5]), (x3, x4, [x0 ||| x6, x0, x1, x2, x5, x7]), (x3, x5, [x0 ||| x6, x0, x1, x2, x4, x7]), (x3, x7, [x0 ||| x6, x0, x1, x2, x4, x5]), (x4, x5, [x0 ||| x6, x0, x1, x2, x3, x7]), (x4, x7, [x0 ||| x6, x0, x1, x2, x3, x5]), (x5, x7, [x0 ||| x6, x0, x1, x2, x3, x4])] := by
  decide +kernel

theorem t224 : optimized 8 1 [x0 ||| x6, x0, x1, x2, x3, x4, x5, x7] = false := by
  rw [optimized.eq_2, t224_pairs]
  simp only [List.any_cons, List.any_nil, t196, t197, t198, t199, t200, t201, t202, t203, t204, t205, t206, t207, t208, t209, t210, t211, t212, t213, t214, t215, t216, t217, t218, t219, t220, t221, t222, t223, Bool.or_false]
  all_goals decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t225 : dispatch 1 (optimized 7) (x0 ||| x6) x6 [x1, x2, x3, x4, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t226 : dispatch 1 (optimized 7) (x0 ||| x6) x1 [x6, x2, x3, x4, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t227 : dispatch 1 (optimized 7) (x0 ||| x6) x2 [x6, x1, x3, x4, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t228 : dispatch 1 (optimized 7) (x0 ||| x6) x3 [x6, x1, x2, x4, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t229 : dispatch 1 (optimized 7) (x0 ||| x6) x4 [x6, x1, x2, x3, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t230 : dispatch 1 (optimized 7) (x0 ||| x6) x5 [x6, x1, x2, x3, x4, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t231 : dispatch 1 (optimized 7) (x0 ||| x6) x7 [x6, x1, x2, x3, x4, x5] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t232 : dispatch 1 (optimized 7) x6 x1 [x0 ||| x6, x2, x3, x4, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t233 : dispatch 1 (optimized 7) x6 x2 [x0 ||| x6, x1, x3, x4, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t234 : dispatch 1 (optimized 7) x6 x3 [x0 ||| x6, x1, x2, x4, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t235 : dispatch 1 (optimized 7) x6 x4 [x0 ||| x6, x1, x2, x3, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t236 : dispatch 1 (optimized 7) x6 x5 [x0 ||| x6, x1, x2, x3, x4, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t237 : dispatch 1 (optimized 7) x6 x7 [x0 ||| x6, x1, x2, x3, x4, x5] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t238 : dispatch 1 (optimized 7) x1 x2 [x0 ||| x6, x6, x3, x4, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t239 : dispatch 1 (optimized 7) x1 x3 [x0 ||| x6, x6, x2, x4, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t240 : dispatch 1 (optimized 7) x1 x4 [x0 ||| x6, x6, x2, x3, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t241 : dispatch 1 (optimized 7) x1 x5 [x0 ||| x6, x6, x2, x3, x4, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t242 : dispatch 1 (optimized 7) x1 x7 [x0 ||| x6, x6, x2, x3, x4, x5] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t243 : dispatch 1 (optimized 7) x2 x3 [x0 ||| x6, x6, x1, x4, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t244 : dispatch 1 (optimized 7) x2 x4 [x0 ||| x6, x6, x1, x3, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t245 : dispatch 1 (optimized 7) x2 x5 [x0 ||| x6, x6, x1, x3, x4, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t246 : dispatch 1 (optimized 7) x2 x7 [x0 ||| x6, x6, x1, x3, x4, x5] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t247 : dispatch 1 (optimized 7) x3 x4 [x0 ||| x6, x6, x1, x2, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t248 : dispatch 1 (optimized 7) x3 x5 [x0 ||| x6, x6, x1, x2, x4, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t249 : dispatch 1 (optimized 7) x3 x7 [x0 ||| x6, x6, x1, x2, x4, x5] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t250 : dispatch 1 (optimized 7) x4 x5 [x0 ||| x6, x6, x1, x2, x3, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t251 : dispatch 1 (optimized 7) x4 x7 [x0 ||| x6, x6, x1, x2, x3, x5] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t252 : dispatch 1 (optimized 7) x5 x7 [x0 ||| x6, x6, x1, x2, x3, x4] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
theorem t253_pairs : pairs [x0 ||| x6, x6, x1, x2, x3, x4, x5, x7] = [(x0 ||| x6, x6, [x1, x2, x3, x4, x5, x7]), (x0 ||| x6, x1, [x6, x2, x3, x4, x5, x7]), (x0 ||| x6, x2, [x6, x1, x3, x4, x5, x7]), (x0 ||| x6, x3, [x6, x1, x2, x4, x5, x7]), (x0 ||| x6, x4, [x6, x1, x2, x3, x5, x7]), (x0 ||| x6, x5, [x6, x1, x2, x3, x4, x7]), (x0 ||| x6, x7, [x6, x1, x2, x3, x4, x5]), (x6, x1, [x0 ||| x6, x2, x3, x4, x5, x7]), (x6, x2, [x0 ||| x6, x1, x3, x4, x5, x7]), (x6, x3, [x0 ||| x6, x1, x2, x4, x5, x7]), (x6, x4, [x0 ||| x6, x1, x2, x3, x5, x7]), (x6, x5, [x0 ||| x6, x1, x2, x3, x4, x7]), (x6, x7, [x0 ||| x6, x1, x2, x3, x4, x5]), (x1, x2, [x0 ||| x6, x6, x3, x4, x5, x7]), (x1, x3, [x0 ||| x6, x6, x2, x4, x5, x7]), (x1, x4, [x0 ||| x6, x6, x2, x3, x5, x7]), (x1, x5, [x0 ||| x6, x6, x2, x3, x4, x7]), (x1, x7, [x0 ||| x6, x6, x2, x3, x4, x5]), (x2, x3, [x0 ||| x6, x6, x1, x4, x5, x7]), (x2, x4, [x0 ||| x6, x6, x1, x3, x5, x7]), (x2, x5, [x0 ||| x6, x6, x1, x3, x4, x7]), (x2, x7, [x0 ||| x6, x6, x1, x3, x4, x5]), (x3, x4, [x0 ||| x6, x6, x1, x2, x5, x7]), (x3, x5, [x0 ||| x6, x6, x1, x2, x4, x7]), (x3, x7, [x0 ||| x6, x6, x1, x2, x4, x5]), (x4, x5, [x0 ||| x6, x6, x1, x2, x3, x7]), (x4, x7, [x0 ||| x6, x6, x1, x2, x3, x5]), (x5, x7, [x0 ||| x6, x6, x1, x2, x3, x4])] := by
  decide +kernel

theorem t253 : optimized 8 1 [x0 ||| x6, x6, x1, x2, x3, x4, x5, x7] = false := by
  rw [optimized.eq_2, t253_pairs]
  simp only [List.any_cons, List.any_nil, t225, t226, t227, t228, t229, t230, t231, t232, t233, t234, t235, t236, t237, t238, t239, t240, t241, t242, t243, t244, t245, t246, t247, t248, t249, t250, t251, t252, Bool.or_false]
  all_goals decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t254 : optimized 8 0 [x0 ||| x6, x0, x6, x1, x2, x3, x4, x5, x7] = false := by
  decide +kernel

theorem t255 : dispatch 2 (optimized 8) x0 x6 [x1, x2, x3, x4, x5, x7] = false := by
  simp only [dispatch, ops, List.any_cons, List.any_nil, Nat.reduceSub, t115, t195, t224, t253, t254, Bool.and_false, Bool.or_false]
  all_goals decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t256 : dispatch 1 (optimized 7) (x0 &&& x7) x0 [x1, x2, x3, x4, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t257 : dispatch 1 (optimized 7) (x0 &&& x7) x1 [x0, x2, x3, x4, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t258 : dispatch 1 (optimized 7) (x0 &&& x7) x2 [x0, x1, x3, x4, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t259 : dispatch 1 (optimized 7) (x0 &&& x7) x3 [x0, x1, x2, x4, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t260 : dispatch 1 (optimized 7) (x0 &&& x7) x4 [x0, x1, x2, x3, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t261 : dispatch 1 (optimized 7) (x0 &&& x7) x5 [x0, x1, x2, x3, x4, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t262 : dispatch 1 (optimized 7) (x0 &&& x7) x6 [x0, x1, x2, x3, x4, x5] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t263 : dispatch 1 (optimized 7) x0 x1 [x0 &&& x7, x2, x3, x4, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t264 : dispatch 1 (optimized 7) x0 x2 [x0 &&& x7, x1, x3, x4, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t265 : dispatch 1 (optimized 7) x0 x3 [x0 &&& x7, x1, x2, x4, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t266 : dispatch 1 (optimized 7) x0 x4 [x0 &&& x7, x1, x2, x3, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t267 : dispatch 1 (optimized 7) x0 x5 [x0 &&& x7, x1, x2, x3, x4, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t268 : dispatch 1 (optimized 7) x0 x6 [x0 &&& x7, x1, x2, x3, x4, x5] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t269 : dispatch 1 (optimized 7) x1 x2 [x0 &&& x7, x0, x3, x4, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t270 : dispatch 1 (optimized 7) x1 x3 [x0 &&& x7, x0, x2, x4, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t271 : dispatch 1 (optimized 7) x1 x4 [x0 &&& x7, x0, x2, x3, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t272 : dispatch 1 (optimized 7) x1 x5 [x0 &&& x7, x0, x2, x3, x4, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t273 : dispatch 1 (optimized 7) x1 x6 [x0 &&& x7, x0, x2, x3, x4, x5] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t274 : dispatch 1 (optimized 7) x2 x3 [x0 &&& x7, x0, x1, x4, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t275 : dispatch 1 (optimized 6) (x2 ||| x4) (x0 &&& x7) [x0, x1, x3, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t276 : dispatch 1 (optimized 6) (x2 ||| x4) x0 [x0 &&& x7, x1, x3, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t277 : dispatch 1 (optimized 6) (x2 ||| x4) x1 [x0 &&& x7, x0, x3, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t278 : dispatch 1 (optimized 6) (x2 ||| x4) x3 [x0 &&& x7, x0, x1, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t279 : dispatch 1 (optimized 6) (x2 ||| x4) x5 [x0 &&& x7, x0, x1, x3, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t280 : dispatch 1 (optimized 6) (x2 ||| x4) x6 [x0 &&& x7, x0, x1, x3, x5] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t281 : dispatch 1 (optimized 6) (x0 &&& x7) x0 [x2 ||| x4, x1, x3, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t282 : dispatch 1 (optimized 6) (x0 &&& x7) x1 [x2 ||| x4, x0, x3, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t283 : dispatch 1 (optimized 6) (x0 &&& x7) x3 [x2 ||| x4, x0, x1, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t284 : dispatch 1 (optimized 6) (x0 &&& x7) x5 [x2 ||| x4, x0, x1, x3, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t285 : dispatch 1 (optimized 6) (x0 &&& x7) x6 [x2 ||| x4, x0, x1, x3, x5] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t286 : dispatch 1 (optimized 6) x0 x1 [x2 ||| x4, x0 &&& x7, x3, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t287 : dispatch 1 (optimized 6) x0 x3 [x2 ||| x4, x0 &&& x7, x1, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t288 : dispatch 1 (optimized 6) x0 x5 [x2 ||| x4, x0 &&& x7, x1, x3, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t289 : dispatch 1 (optimized 6) x0 x6 [x2 ||| x4, x0 &&& x7, x1, x3, x5] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t290 : dispatch 1 (optimized 6) x1 x3 [x2 ||| x4, x0 &&& x7, x0, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t291 : dispatch 1 (optimized 6) x1 x5 [x2 ||| x4, x0 &&& x7, x0, x3, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t292 : dispatch 1 (optimized 6) x1 x6 [x2 ||| x4, x0 &&& x7, x0, x3, x5] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t293 : dispatch 1 (optimized 6) x3 x5 [x2 ||| x4, x0 &&& x7, x0, x1, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t294 : dispatch 1 (optimized 6) x3 x6 [x2 ||| x4, x0 &&& x7, x0, x1, x5] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t295 : dispatch 1 (optimized 6) x5 x6 [x2 ||| x4, x0 &&& x7, x0, x1, x3] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
theorem t296_pairs : pairs [x2 ||| x4, x0 &&& x7, x0, x1, x3, x5, x6] = [(x2 ||| x4, x0 &&& x7, [x0, x1, x3, x5, x6]), (x2 ||| x4, x0, [x0 &&& x7, x1, x3, x5, x6]), (x2 ||| x4, x1, [x0 &&& x7, x0, x3, x5, x6]), (x2 ||| x4, x3, [x0 &&& x7, x0, x1, x5, x6]), (x2 ||| x4, x5, [x0 &&& x7, x0, x1, x3, x6]), (x2 ||| x4, x6, [x0 &&& x7, x0, x1, x3, x5]), (x0 &&& x7, x0, [x2 ||| x4, x1, x3, x5, x6]), (x0 &&& x7, x1, [x2 ||| x4, x0, x3, x5, x6]), (x0 &&& x7, x3, [x2 ||| x4, x0, x1, x5, x6]), (x0 &&& x7, x5, [x2 ||| x4, x0, x1, x3, x6]), (x0 &&& x7, x6, [x2 ||| x4, x0, x1, x3, x5]), (x0, x1, [x2 ||| x4, x0 &&& x7, x3, x5, x6]), (x0, x3, [x2 ||| x4, x0 &&& x7, x1, x5, x6]), (x0, x5, [x2 ||| x4, x0 &&& x7, x1, x3, x6]), (x0, x6, [x2 ||| x4, x0 &&& x7, x1, x3, x5]), (x1, x3, [x2 ||| x4, x0 &&& x7, x0, x5, x6]), (x1, x5, [x2 ||| x4, x0 &&& x7, x0, x3, x6]), (x1, x6, [x2 ||| x4, x0 &&& x7, x0, x3, x5]), (x3, x5, [x2 ||| x4, x0 &&& x7, x0, x1, x6]), (x3, x6, [x2 ||| x4, x0 &&& x7, x0, x1, x5]), (x5, x6, [x2 ||| x4, x0 &&& x7, x0, x1, x3])] := by
  decide +kernel

theorem t296 : optimized 7 1 [x2 ||| x4, x0 &&& x7, x0, x1, x3, x5, x6] = false := by
  rw [optimized.eq_2, t296_pairs]
  simp only [List.any_cons, List.any_nil, t275, t276, t277, t278, t279, t280, t281, t282, t283, t284, t285, t286, t287, t288, t289, t290, t291, t292, t293, t294, t295, Bool.or_false]
  all_goals decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t297 : optimized 7 0 [x2 ||| x4, x2, x0 &&& x7, x0, x1, x3, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t298 : optimized 7 0 [x2 ||| x4, x4, x0 &&& x7, x0, x1, x3, x5, x6] = false := by
  decide +kernel

theorem t299 : dispatch 1 (optimized 7) x2 x4 [x0 &&& x7, x0, x1, x3, x5, x6] = false := by
  simp only [dispatch, ops, List.any_cons, List.any_nil, Nat.reduceSub, t296, t297, t298, Bool.and_false, Bool.or_false]
  all_goals decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t300 : dispatch 1 (optimized 7) x2 x5 [x0 &&& x7, x0, x1, x3, x4, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t301 : dispatch 1 (optimized 7) x2 x6 [x0 &&& x7, x0, x1, x3, x4, x5] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t302 : dispatch 1 (optimized 7) x3 x4 [x0 &&& x7, x0, x1, x2, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t303 : dispatch 1 (optimized 7) x3 x5 [x0 &&& x7, x0, x1, x2, x4, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t304 : dispatch 1 (optimized 7) x3 x6 [x0 &&& x7, x0, x1, x2, x4, x5] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t305 : dispatch 1 (optimized 7) x4 x5 [x0 &&& x7, x0, x1, x2, x3, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t306 : dispatch 1 (optimized 7) x4 x6 [x0 &&& x7, x0, x1, x2, x3, x5] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t307 : dispatch 1 (optimized 7) x5 x6 [x0 &&& x7, x0, x1, x2, x3, x4] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
theorem t308_pairs : pairs [x0 &&& x7, x0, x1, x2, x3, x4, x5, x6] = [(x0 &&& x7, x0, [x1, x2, x3, x4, x5, x6]), (x0 &&& x7, x1, [x0, x2, x3, x4, x5, x6]), (x0 &&& x7, x2, [x0, x1, x3, x4, x5, x6]), (x0 &&& x7, x3, [x0, x1, x2, x4, x5, x6]), (x0 &&& x7, x4, [x0, x1, x2, x3, x5, x6]), (x0 &&& x7, x5, [x0, x1, x2, x3, x4, x6]), (x0 &&& x7, x6, [x0, x1, x2, x3, x4, x5]), (x0, x1, [x0 &&& x7, x2, x3, x4, x5, x6]), (x0, x2, [x0 &&& x7, x1, x3, x4, x5, x6]), (x0, x3, [x0 &&& x7, x1, x2, x4, x5, x6]), (x0, x4, [x0 &&& x7, x1, x2, x3, x5, x6]), (x0, x5, [x0 &&& x7, x1, x2, x3, x4, x6]), (x0, x6, [x0 &&& x7, x1, x2, x3, x4, x5]), (x1, x2, [x0 &&& x7, x0, x3, x4, x5, x6]), (x1, x3, [x0 &&& x7, x0, x2, x4, x5, x6]), (x1, x4, [x0 &&& x7, x0, x2, x3, x5, x6]), (x1, x5, [x0 &&& x7, x0, x2, x3, x4, x6]), (x1, x6, [x0 &&& x7, x0, x2, x3, x4, x5]), (x2, x3, [x0 &&& x7, x0, x1, x4, x5, x6]), (x2, x4, [x0 &&& x7, x0, x1, x3, x5, x6]), (x2, x5, [x0 &&& x7, x0, x1, x3, x4, x6]), (x2, x6, [x0 &&& x7, x0, x1, x3, x4, x5]), (x3, x4, [x0 &&& x7, x0, x1, x2, x5, x6]), (x3, x5, [x0 &&& x7, x0, x1, x2, x4, x6]), (x3, x6, [x0 &&& x7, x0, x1, x2, x4, x5]), (x4, x5, [x0 &&& x7, x0, x1, x2, x3, x6]), (x4, x6, [x0 &&& x7, x0, x1, x2, x3, x5]), (x5, x6, [x0 &&& x7, x0, x1, x2, x3, x4])] := by
  decide +kernel

theorem t308 : optimized 8 1 [x0 &&& x7, x0, x1, x2, x3, x4, x5, x6] = false := by
  rw [optimized.eq_2, t308_pairs]
  simp only [List.any_cons, List.any_nil, t256, t257, t258, t259, t260, t261, t262, t263, t264, t265, t266, t267, t268, t269, t270, t271, t272, t273, t274, t299, t300, t301, t302, t303, t304, t305, t306, t307, Bool.or_false]
  all_goals decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t309 : optimized 8 0 [x0 &&& x7, x0, x7, x1, x2, x3, x4, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t310 : optimized 8 0 [x0 ||| x7, x0, x7, x1, x2, x3, x4, x5, x6] = false := by
  decide +kernel

theorem t311 : dispatch 2 (optimized 8) x0 x7 [x1, x2, x3, x4, x5, x6] = false := by
  simp only [dispatch, ops, List.any_cons, List.any_nil, Nat.reduceSub, t308, t309, t310, Bool.and_false, Bool.or_false]
  all_goals decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t312 : optimized 8 0 [x1 &&& x2, x1, x2, x0, x3, x4, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t313 : dispatch 1 (optimized 7) (x1 ||| x2) x1 [x0, x3, x4, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t314 : dispatch 1 (optimized 7) (x1 ||| x2) x0 [x1, x3, x4, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t315 : dispatch 1 (optimized 7) (x1 ||| x2) x3 [x1, x0, x4, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t316 : dispatch 1 (optimized 7) (x1 ||| x2) x4 [x1, x0, x3, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t317 : dispatch 1 (optimized 7) (x1 ||| x2) x5 [x1, x0, x3, x4, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t318 : dispatch 1 (optimized 7) (x1 ||| x2) x6 [x1, x0, x3, x4, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t319 : dispatch 1 (optimized 7) (x1 ||| x2) x7 [x1, x0, x3, x4, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t320 : dispatch 1 (optimized 7) x1 x0 [x1 ||| x2, x3, x4, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t321 : dispatch 1 (optimized 7) x1 x3 [x1 ||| x2, x0, x4, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t322 : dispatch 1 (optimized 7) x1 x4 [x1 ||| x2, x0, x3, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t323 : dispatch 1 (optimized 7) x1 x5 [x1 ||| x2, x0, x3, x4, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t324 : dispatch 1 (optimized 7) x1 x6 [x1 ||| x2, x0, x3, x4, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t325 : dispatch 1 (optimized 7) x1 x7 [x1 ||| x2, x0, x3, x4, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t326 : dispatch 1 (optimized 7) x0 x3 [x1 ||| x2, x1, x4, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t327 : dispatch 1 (optimized 7) x0 x4 [x1 ||| x2, x1, x3, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t328 : dispatch 1 (optimized 7) x0 x5 [x1 ||| x2, x1, x3, x4, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t329 : dispatch 1 (optimized 7) x0 x6 [x1 ||| x2, x1, x3, x4, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t330 : dispatch 1 (optimized 7) x0 x7 [x1 ||| x2, x1, x3, x4, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t331 : dispatch 1 (optimized 7) x3 x4 [x1 ||| x2, x1, x0, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t332 : dispatch 1 (optimized 7) x3 x5 [x1 ||| x2, x1, x0, x4, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t333 : dispatch 1 (optimized 7) x3 x6 [x1 ||| x2, x1, x0, x4, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t334 : dispatch 1 (optimized 7) x3 x7 [x1 ||| x2, x1, x0, x4, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t335 : dispatch 1 (optimized 7) x4 x5 [x1 ||| x2, x1, x0, x3, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t336 : dispatch 1 (optimized 7) x4 x6 [x1 ||| x2, x1, x0, x3, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t337 : dispatch 1 (optimized 7) x4 x7 [x1 ||| x2, x1, x0, x3, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t338 : dispatch 1 (optimized 7) x5 x6 [x1 ||| x2, x1, x0, x3, x4, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t339 : dispatch 1 (optimized 7) x5 x7 [x1 ||| x2, x1, x0, x3, x4, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t340 : dispatch 1 (optimized 7) x6 x7 [x1 ||| x2, x1, x0, x3, x4, x5] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
theorem t341_pairs : pairs [x1 ||| x2, x1, x0, x3, x4, x5, x6, x7] = [(x1 ||| x2, x1, [x0, x3, x4, x5, x6, x7]), (x1 ||| x2, x0, [x1, x3, x4, x5, x6, x7]), (x1 ||| x2, x3, [x1, x0, x4, x5, x6, x7]), (x1 ||| x2, x4, [x1, x0, x3, x5, x6, x7]), (x1 ||| x2, x5, [x1, x0, x3, x4, x6, x7]), (x1 ||| x2, x6, [x1, x0, x3, x4, x5, x7]), (x1 ||| x2, x7, [x1, x0, x3, x4, x5, x6]), (x1, x0, [x1 ||| x2, x3, x4, x5, x6, x7]), (x1, x3, [x1 ||| x2, x0, x4, x5, x6, x7]), (x1, x4, [x1 ||| x2, x0, x3, x5, x6, x7]), (x1, x5, [x1 ||| x2, x0, x3, x4, x6, x7]), (x1, x6, [x1 ||| x2, x0, x3, x4, x5, x7]), (x1, x7, [x1 ||| x2, x0, x3, x4, x5, x6]), (x0, x3, [x1 ||| x2, x1, x4, x5, x6, x7]), (x0, x4, [x1 ||| x2, x1, x3, x5, x6, x7]), (x0, x5, [x1 ||| x2, x1, x3, x4, x6, x7]), (x0, x6, [x1 ||| x2, x1, x3, x4, x5, x7]), (x0, x7, [x1 ||| x2, x1, x3, x4, x5, x6]), (x3, x4, [x1 ||| x2, x1, x0, x5, x6, x7]), (x3, x5, [x1 ||| x2, x1, x0, x4, x6, x7]), (x3, x6, [x1 ||| x2, x1, x0, x4, x5, x7]), (x3, x7, [x1 ||| x2, x1, x0, x4, x5, x6]), (x4, x5, [x1 ||| x2, x1, x0, x3, x6, x7]), (x4, x6, [x1 ||| x2, x1, x0, x3, x5, x7]), (x4, x7, [x1 ||| x2, x1, x0, x3, x5, x6]), (x5, x6, [x1 ||| x2, x1, x0, x3, x4, x7]), (x5, x7, [x1 ||| x2, x1, x0, x3, x4, x6]), (x6, x7, [x1 ||| x2, x1, x0, x3, x4, x5])] := by
  decide +kernel

theorem t341 : optimized 8 1 [x1 ||| x2, x1, x0, x3, x4, x5, x6, x7] = false := by
  rw [optimized.eq_2, t341_pairs]
  simp only [List.any_cons, List.any_nil, t313, t314, t315, t316, t317, t318, t319, t320, t321, t322, t323, t324, t325, t326, t327, t328, t329, t330, t331, t332, t333, t334, t335, t336, t337, t338, t339, t340, Bool.or_false]
  all_goals decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t342 : optimized 8 0 [x1 ||| x2, x1, x2, x0, x3, x4, x5, x6, x7] = false := by
  decide +kernel

theorem t343 : dispatch 2 (optimized 8) x1 x2 [x0, x3, x4, x5, x6, x7] = false := by
  simp only [dispatch, ops, List.any_cons, List.any_nil, Nat.reduceSub, t312, t341, t342, Bool.and_false, Bool.or_false]
  all_goals decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t344 : optimized 8 0 [x1 &&& x3, x1, x3, x0, x2, x4, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t345 : dispatch 1 (optimized 7) (x1 ||| x3) x1 [x0, x2, x4, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t346 : dispatch 1 (optimized 7) (x1 ||| x3) x0 [x1, x2, x4, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t347 : dispatch 1 (optimized 7) (x1 ||| x3) x2 [x1, x0, x4, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t348 : dispatch 0 (optimized 6) ((x1 ||| x3) &&& x4) x4 [x1, x0, x2, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t349 : dispatch 0 (optimized 6) ((x1 ||| x3) &&& x4) x1 [x4, x0, x2, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t350 : dispatch 0 (optimized 6) ((x1 ||| x3) &&& x4) x0 [x4, x1, x2, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t351 : dispatch 0 (optimized 6) ((x1 ||| x3) &&& x4) x2 [x4, x1, x0, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t352 : dispatch 0 (optimized 6) ((x1 ||| x3) &&& x4) x5 [x4, x1, x0, x2, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t353 : dispatch 0 (optimized 6) ((x1 ||| x3) &&& x4) x6 [x4, x1, x0, x2, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t354 : dispatch 0 (optimized 6) ((x1 ||| x3) &&& x4) x7 [x4, x1, x0, x2, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t355 : dispatch 0 (optimized 6) x4 x1 [(x1 ||| x3) &&& x4, x0, x2, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t356 : dispatch 0 (optimized 6) x4 x0 [(x1 ||| x3) &&& x4, x1, x2, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t357 : dispatch 0 (optimized 6) x4 x2 [(x1 ||| x3) &&& x4, x1, x0, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t358 : dispatch 0 (optimized 6) x4 x5 [(x1 ||| x3) &&& x4, x1, x0, x2, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t359 : dispatch 0 (optimized 6) x4 x6 [(x1 ||| x3) &&& x4, x1, x0, x2, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t360 : dispatch 0 (optimized 6) x4 x7 [(x1 ||| x3) &&& x4, x1, x0, x2, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t361 : dispatch 0 (optimized 6) x1 x0 [(x1 ||| x3) &&& x4, x4, x2, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t362 : dispatch 0 (optimized 6) x1 x2 [(x1 ||| x3) &&& x4, x4, x0, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t363 : dispatch 0 (optimized 6) x1 x5 [(x1 ||| x3) &&& x4, x4, x0, x2, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t364 : dispatch 0 (optimized 6) x1 x6 [(x1 ||| x3) &&& x4, x4, x0, x2, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t365 : dispatch 0 (optimized 6) x1 x7 [(x1 ||| x3) &&& x4, x4, x0, x2, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t366 : dispatch 0 (optimized 6) x0 x2 [(x1 ||| x3) &&& x4, x4, x1, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t367 : dispatch 0 (optimized 6) x0 x5 [(x1 ||| x3) &&& x4, x4, x1, x2, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t368 : dispatch 0 (optimized 6) x0 x6 [(x1 ||| x3) &&& x4, x4, x1, x2, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t369 : dispatch 0 (optimized 6) x0 x7 [(x1 ||| x3) &&& x4, x4, x1, x2, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t370 : dispatch 0 (optimized 6) x2 x5 [(x1 ||| x3) &&& x4, x4, x1, x0, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t371 : dispatch 0 (optimized 6) x2 x6 [(x1 ||| x3) &&& x4, x4, x1, x0, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t372 : dispatch 0 (optimized 6) x2 x7 [(x1 ||| x3) &&& x4, x4, x1, x0, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t373 : dispatch 0 (optimized 6) x5 x6 [(x1 ||| x3) &&& x4, x4, x1, x0, x2, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t374 : dispatch 0 (optimized 6) x5 x7 [(x1 ||| x3) &&& x4, x4, x1, x0, x2, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t375 : dispatch 0 (optimized 6) x6 x7 [(x1 ||| x3) &&& x4, x4, x1, x0, x2, x5] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
theorem t376_pairs : pairs [(x1 ||| x3) &&& x4, x4, x1, x0, x2, x5, x6, x7] = [((x1 ||| x3) &&& x4, x4, [x1, x0, x2, x5, x6, x7]), ((x1 ||| x3) &&& x4, x1, [x4, x0, x2, x5, x6, x7]), ((x1 ||| x3) &&& x4, x0, [x4, x1, x2, x5, x6, x7]), ((x1 ||| x3) &&& x4, x2, [x4, x1, x0, x5, x6, x7]), ((x1 ||| x3) &&& x4, x5, [x4, x1, x0, x2, x6, x7]), ((x1 ||| x3) &&& x4, x6, [x4, x1, x0, x2, x5, x7]), ((x1 ||| x3) &&& x4, x7, [x4, x1, x0, x2, x5, x6]), (x4, x1, [(x1 ||| x3) &&& x4, x0, x2, x5, x6, x7]), (x4, x0, [(x1 ||| x3) &&& x4, x1, x2, x5, x6, x7]), (x4, x2, [(x1 ||| x3) &&& x4, x1, x0, x5, x6, x7]), (x4, x5, [(x1 ||| x3) &&& x4, x1, x0, x2, x6, x7]), (x4, x6, [(x1 ||| x3) &&& x4, x1, x0, x2, x5, x7]), (x4, x7, [(x1 ||| x3) &&& x4, x1, x0, x2, x5, x6]), (x1, x0, [(x1 ||| x3) &&& x4, x4, x2, x5, x6, x7]), (x1, x2, [(x1 ||| x3) &&& x4, x4, x0, x5, x6, x7]), (x1, x5, [(x1 ||| x3) &&& x4, x4, x0, x2, x6, x7]), (x1, x6, [(x1 ||| x3) &&& x4, x4, x0, x2, x5, x7]), (x1, x7, [(x1 ||| x3) &&& x4, x4, x0, x2, x5, x6]), (x0, x2, [(x1 ||| x3) &&& x4, x4, x1, x5, x6, x7]), (x0, x5, [(x1 ||| x3) &&& x4, x4, x1, x2, x6, x7]), (x0, x6, [(x1 ||| x3) &&& x4, x4, x1, x2, x5, x7]), (x0, x7, [(x1 ||| x3) &&& x4, x4, x1, x2, x5, x6]), (x2, x5, [(x1 ||| x3) &&& x4, x4, x1, x0, x6, x7]), (x2, x6, [(x1 ||| x3) &&& x4, x4, x1, x0, x5, x7]), (x2, x7, [(x1 ||| x3) &&& x4, x4, x1, x0, x5, x6]), (x5, x6, [(x1 ||| x3) &&& x4, x4, x1, x0, x2, x7]), (x5, x7, [(x1 ||| x3) &&& x4, x4, x1, x0, x2, x6]), (x6, x7, [(x1 ||| x3) &&& x4, x4, x1, x0, x2, x5])] := by
  decide +kernel

theorem t376 : optimized 7 0 [(x1 ||| x3) &&& x4, x4, x1, x0, x2, x5, x6, x7] = false := by
  rw [optimized.eq_2, t376_pairs]
  simp only [List.any_cons, List.any_nil, t348, t349, t350, t351, t352, t353, t354, t355, t356, t357, t358, t359, t360, t361, t362, t363, t364, t365, t366, t367, t368, t369, t370, t371, t372, t373, t374, t375, Bool.or_false]
  all_goals decide +kernel

theorem t377 : dispatch 1 (optimized 7) (x1 ||| x3) x4 [x1, x0, x2, x5, x6, x7] = false := by
  simp only [dispatch, ops, List.any_cons, List.any_nil, Nat.reduceSub, t376, Bool.and_false, Bool.or_false]
  all_goals decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t378 : dispatch 1 (optimized 7) (x1 ||| x3) x5 [x1, x0, x2, x4, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t379 : dispatch 1 (optimized 7) (x1 ||| x3) x6 [x1, x0, x2, x4, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t380 : dispatch 1 (optimized 7) (x1 ||| x3) x7 [x1, x0, x2, x4, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t381 : dispatch 1 (optimized 7) x1 x0 [x1 ||| x3, x2, x4, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t382 : dispatch 1 (optimized 7) x1 x2 [x1 ||| x3, x0, x4, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t383 : dispatch 1 (optimized 7) x1 x4 [x1 ||| x3, x0, x2, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t384 : dispatch 1 (optimized 7) x1 x5 [x1 ||| x3, x0, x2, x4, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t385 : dispatch 1 (optimized 7) x1 x6 [x1 ||| x3, x0, x2, x4, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t386 : dispatch 1 (optimized 7) x1 x7 [x1 ||| x3, x0, x2, x4, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t387 : dispatch 1 (optimized 7) x0 x2 [x1 ||| x3, x1, x4, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t388 : dispatch 1 (optimized 7) x0 x4 [x1 ||| x3, x1, x2, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t389 : dispatch 1 (optimized 7) x0 x5 [x1 ||| x3, x1, x2, x4, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t390 : dispatch 1 (optimized 6) (x0 ||| x6) (x1 ||| x3) [x1, x2, x4, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t391 : dispatch 1 (optimized 6) (x0 ||| x6) x1 [x1 ||| x3, x2, x4, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t392 : dispatch 1 (optimized 6) (x1 ||| x3) x2 [x0 ||| x6, x1, x4, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t393 : dispatch 1 (optimized 6) (x1 ||| x3) x4 [x0 ||| x6, x1, x2, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t394 : dispatch 1 (optimized 6) (x1 ||| x3) x5 [x0 ||| x6, x1, x2, x4, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t395 : dispatch 1 (optimized 6) (x1 ||| x3) x7 [x0 ||| x6, x1, x2, x4, x5] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t396 : dispatch 1 (optimized 6) x1 x2 [x0 ||| x6, x1 ||| x3, x4, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t397 : dispatch 1 (optimized 6) x1 x4 [x0 ||| x6, x1 ||| x3, x2, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t398 : dispatch 1 (optimized 6) x1 x5 [x0 ||| x6, x1 ||| x3, x2, x4, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t399 : dispatch 1 (optimized 6) x1 x7 [x0 ||| x6, x1 ||| x3, x2, x4, x5] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t400 : dispatch 1 (optimized 6) x2 x4 [x0 ||| x6, x1 ||| x3, x1, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t401 : dispatch 1 (optimized 6) x2 x5 [x0 ||| x6, x1 ||| x3, x1, x4, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t402 : dispatch 1 (optimized 6) x2 x7 [x0 ||| x6, x1 ||| x3, x1, x4, x5] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t403 : dispatch 1 (optimized 6) x4 x5 [x0 ||| x6, x1 ||| x3, x1, x2, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t404 : dispatch 1 (optimized 6) x4 x7 [x0 ||| x6, x1 ||| x3, x1, x2, x5] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t405 : dispatch 1 (optimized 6) x5 x7 [x0 ||| x6, x1 ||| x3, x1, x2, x4] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
theorem t406_pairs : pairs [x0 ||| x6, x1 ||| x3, x1, x2, x4, x5, x7] = [(x0 ||| x6, x1 ||| x3, [x1, x2, x4, x5, x7]), (x0 ||| x6, x1, [x1 ||| x3, x2, x4, x5, x7]), (x0 ||| x6, x2, [x1 ||| x3, x1, x4, x5, x7]), (x0 ||| x6, x4, [x1 ||| x3, x1, x2, x5, x7]), (x0 ||| x6, x5, [x1 ||| x3, x1, x2, x4, x7]), (x0 ||| x6, x7, [x1 ||| x3, x1, x2, x4, x5]), (x1 ||| x3, x1, [x0 ||| x6, x2, x4, x5, x7]), (x1 ||| x3, x2, [x0 ||| x6, x1, x4, x5, x7]), (x1 ||| x3, x4, [x0 ||| x6, x1, x2, x5, x7]), (x1 ||| x3, x5, [x0 ||| x6, x1, x2, x4, x7]), (x1 ||| x3, x7, [x0 ||| x6, x1, x2, x4, x5]), (x1, x2, [x0 ||| x6, x1 ||| x3, x4, x5, x7]), (x1, x4, [x0 ||| x6, x1 ||| x3, x2, x5, x7]), (x1, x5, [x0 ||| x6, x1 ||| x3, x2, x4, x7]), (x1, x7, [x0 ||| x6, x1 ||| x3, x2, x4, x5]), (x2, x4, [x0 ||| x6, x1 ||| x3, x1, x5, x7]), (x2, x5, [x0 ||| x6, x1 ||| x3, x1, x4, x7]), (x2, x7, [x0 ||| x6, x1 ||| x3, x1, x4, x5]), (x4, x5, [x0 ||| x6, x1 ||| x3, x1, x2, x7]), (x4, x7, [x0 ||| x6, x1 ||| x3, x1, x2, x5]), (x5, x7, [x0 ||| x6, x1 ||| x3, x1, x2, x4])] := by
  decide +kernel

theorem t406 : optimized 7 1 [x0 ||| x6, x1 ||| x3, x1, x2, x4, x5, x7] = false := by
  rw [optimized.eq_2, t406_pairs]
  simp only [List.any_cons, List.any_nil, t390, t391, t135, t136, t137, t138, t124, t392, t393, t394, t395, t396, t397, t398, t399, t400, t401, t402, t403, t404, t405, Bool.or_false]
  all_goals decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t407 : optimized 7 0 [x0 ||| x6, x0, x1 ||| x3, x1, x2, x4, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t408 : optimized 7 0 [x0 ||| x6, x6, x1 ||| x3, x1, x2, x4, x5, x7] = false := by
  decide +kernel

theorem t409 : dispatch 1 (optimized 7) x0 x6 [x1 ||| x3, x1, x2, x4, x5, x7] = false := by
  simp only [dispatch, ops, List.any_cons, List.any_nil, Nat.reduceSub, t406, t407, t408, Bool.and_false, Bool.or_false]
  all_goals decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t410 : dispatch 1 (optimized 7) x0 x7 [x1 ||| x3, x1, x2, x4, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t411 : optimized 7 1 [x2 ||| x4, x1 ||| x3, x1, x0, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t412 : optimized 7 0 [x2 ||| x4, x2, x1 ||| x3, x1, x0, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t413 : optimized 7 0 [x2 ||| x4, x4, x1 ||| x3, x1, x0, x5, x6, x7] = false := by
  decide +kernel

theorem t414 : dispatch 1 (optimized 7) x2 x4 [x1 ||| x3, x1, x0, x5, x6, x7] = false := by
  simp only [dispatch, ops, List.any_cons, List.any_nil, Nat.reduceSub, t411, t412, t413, Bool.and_false, Bool.or_false]
  all_goals decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t415 : dispatch 1 (optimized 7) x2 x5 [x1 ||| x3, x1, x0, x4, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t416 : dispatch 1 (optimized 7) x2 x6 [x1 ||| x3, x1, x0, x4, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t417 : dispatch 1 (optimized 7) x2 x7 [x1 ||| x3, x1, x0, x4, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t418 : dispatch 1 (optimized 7) x4 x5 [x1 ||| x3, x1, x0, x2, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t419 : dispatch 1 (optimized 7) x4 x6 [x1 ||| x3, x1, x0, x2, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t420 : dispatch 1 (optimized 7) x4 x7 [x1 ||| x3, x1, x0, x2, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t421 : dispatch 1 (optimized 7) x5 x6 [x1 ||| x3, x1, x0, x2, x4, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t422 : dispatch 1 (optimized 7) x5 x7 [x1 ||| x3, x1, x0, x2, x4, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t423 : dispatch 1 (optimized 7) x6 x7 [x1 ||| x3, x1, x0, x2, x4, x5] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
theorem t424_pairs : pairs [x1 ||| x3, x1, x0, x2, x4, x5, x6, x7] = [(x1 ||| x3, x1, [x0, x2, x4, x5, x6, x7]), (x1 ||| x3, x0, [x1, x2, x4, x5, x6, x7]), (x1 ||| x3, x2, [x1, x0, x4, x5, x6, x7]), (x1 ||| x3, x4, [x1, x0, x2, x5, x6, x7]), (x1 ||| x3, x5, [x1, x0, x2, x4, x6, x7]), (x1 ||| x3, x6, [x1, x0, x2, x4, x5, x7]), (x1 ||| x3, x7, [x1, x0, x2, x4, x5, x6]), (x1, x0, [x1 ||| x3, x2, x4, x5, x6, x7]), (x1, x2, [x1 ||| x3, x0, x4, x5, x6, x7]), (x1, x4, [x1 ||| x3, x0, x2, x5, x6, x7]), (x1, x5, [x1 ||| x3, x0, x2, x4, x6, x7]), (x1, x6, [x1 ||| x3, x0, x2, x4, x5, x7]), (x1, x7, [x1 ||| x3, x0, x2, x4, x5, x6]), (x0, x2, [x1 ||| x3, x1, x4, x5, x6, x7]), (x0, x4, [x1 ||| x3, x1, x2, x5, x6, x7]), (x0, x5, [x1 ||| x3, x1, x2, x4, x6, x7]), (x0, x6, [x1 ||| x3, x1, x2, x4, x5, x7]), (x0, x7, [x1 ||| x3, x1, x2, x4, x5, x6]), (x2, x4, [x1 ||| x3, x1, x0, x5, x6, x7]), (x2, x5, [x1 ||| x3, x1, x0, x4, x6, x7]), (x2, x6, [x1 ||| x3, x1, x0, x4, x5, x7]), (x2, x7, [x1 ||| x3, x1, x0, x4, x5, x6]), (x4, x5, [x1 ||| x3, x1, x0, x2, x6, x7]), (x4, x6, [x1 ||| x3, x1, x0, x2, x5, x7]), (x4, x7, [x1 ||| x3, x1, x0, x2, x5, x6]), (x5, x6, [x1 ||| x3, x1, x0, x2, x4, x7]), (x5, x7, [x1 ||| x3, x1, x0, x2, x4, x6]), (x6, x7, [x1 ||| x3, x1, x0, x2, x4, x5])] := by
  decide +kernel

theorem t424 : optimized 8 1 [x1 ||| x3, x1, x0, x2, x4, x5, x6, x7] = false := by
  rw [optimized.eq_2, t424_pairs]
  simp only [List.any_cons, List.any_nil, t345, t346, t347, t377, t378, t379, t380, t381, t382, t383, t384, t385, t386, t387, t388, t389, t409, t410, t414, t415, t416, t417, t418, t419, t420, t421, t422, t423, Bool.or_false]
  all_goals decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t425 : optimized 8 0 [x1 ||| x3, x1, x3, x0, x2, x4, x5, x6, x7] = false := by
  decide +kernel

theorem t426 : dispatch 2 (optimized 8) x1 x3 [x0, x2, x4, x5, x6, x7] = false := by
  simp only [dispatch, ops, List.any_cons, List.any_nil, Nat.reduceSub, t344, t424, t425, Bool.and_false, Bool.or_false]
  all_goals decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t427 : dispatch 0 (optimized 7) (x1 &&& x4) x1 [x4, x0, x2, x3, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t428 : dispatch 0 (optimized 7) (x1 &&& x4) x4 [x1, x0, x2, x3, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t429 : dispatch 0 (optimized 7) (x1 &&& x4) x0 [x1, x4, x2, x3, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t430 : dispatch 0 (optimized 7) (x1 &&& x4) x2 [x1, x4, x0, x3, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t431 : dispatch 0 (optimized 7) (x1 &&& x4) x3 [x1, x4, x0, x2, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t432 : dispatch 0 (optimized 7) (x1 &&& x4) x5 [x1, x4, x0, x2, x3, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t433 : dispatch 0 (optimized 7) (x1 &&& x4) x6 [x1, x4, x0, x2, x3, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t434 : dispatch 0 (optimized 7) (x1 &&& x4) x7 [x1, x4, x0, x2, x3, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t435 : dispatch 0 (optimized 7) x1 x4 [x1 &&& x4, x0, x2, x3, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t436 : dispatch 0 (optimized 7) x1 x0 [x1 &&& x4, x4, x2, x3, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t437 : dispatch 0 (optimized 7) x1 x2 [x1 &&& x4, x4, x0, x3, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t438 : dispatch 0 (optimized 7) x1 x3 [x1 &&& x4, x4, x0, x2, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t439 : dispatch 0 (optimized 7) x1 x5 [x1 &&& x4, x4, x0, x2, x3, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t440 : dispatch 0 (optimized 7) x1 x6 [x1 &&& x4, x4, x0, x2, x3, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t441 : dispatch 0 (optimized 7) x1 x7 [x1 &&& x4, x4, x0, x2, x3, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t442 : dispatch 0 (optimized 7) x4 x0 [x1 &&& x4, x1, x2, x3, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t443 : dispatch 0 (optimized 7) x4 x2 [x1 &&& x4, x1, x0, x3, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t444 : dispatch 0 (optimized 7) x4 x3 [x1 &&& x4, x1, x0, x2, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t445 : dispatch 0 (optimized 7) x4 x5 [x1 &&& x4, x1, x0, x2, x3, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t446 : dispatch 0 (optimized 7) x4 x6 [x1 &&& x4, x1, x0, x2, x3, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t447 : dispatch 0 (optimized 7) x4 x7 [x1 &&& x4, x1, x0, x2, x3, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t448 : dispatch 0 (optimized 7) x0 x2 [x1 &&& x4, x1, x4, x3, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t449 : dispatch 0 (optimized 7) x0 x3 [x1 &&& x4, x1, x4, x2, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t450 : dispatch 0 (optimized 7) x0 x5 [x1 &&& x4, x1, x4, x2, x3, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t451 : dispatch 0 (optimized 7) x0 x6 [x1 &&& x4, x1, x4, x2, x3, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t452 : dispatch 0 (optimized 7) x0 x7 [x1 &&& x4, x1, x4, x2, x3, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t453 : dispatch 0 (optimized 7) x2 x3 [x1 &&& x4, x1, x4, x0, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t454 : dispatch 0 (optimized 7) x2 x5 [x1 &&& x4, x1, x4, x0, x3, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t455 : dispatch 0 (optimized 7) x2 x6 [x1 &&& x4, x1, x4, x0, x3, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t456 : dispatch 0 (optimized 7) x2 x7 [x1 &&& x4, x1, x4, x0, x3, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t457 : dispatch 0 (optimized 7) x3 x5 [x1 &&& x4, x1, x4, x0, x2, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t458 : dispatch 0 (optimized 7) x3 x6 [x1 &&& x4, x1, x4, x0, x2, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t459 : dispatch 0 (optimized 7) x3 x7 [x1 &&& x4, x1, x4, x0, x2, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t460 : dispatch 0 (optimized 7) x5 x6 [x1 &&& x4, x1, x4, x0, x2, x3, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t461 : dispatch 0 (optimized 7) x5 x7 [x1 &&& x4, x1, x4, x0, x2, x3, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t462 : dispatch 0 (optimized 7) x6 x7 [x1 &&& x4, x1, x4, x0, x2, x3, x5] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
theorem t463_pairs : pairs [x1 &&& x4, x1, x4, x0, x2, x3, x5, x6, x7] = [(x1 &&& x4, x1, [x4, x0, x2, x3, x5, x6, x7]), (x1 &&& x4, x4, [x1, x0, x2, x3, x5, x6, x7]), (x1 &&& x4, x0, [x1, x4, x2, x3, x5, x6, x7]), (x1 &&& x4, x2, [x1, x4, x0, x3, x5, x6, x7]), (x1 &&& x4, x3, [x1, x4, x0, x2, x5, x6, x7]), (x1 &&& x4, x5, [x1, x4, x0, x2, x3, x6, x7]), (x1 &&& x4, x6, [x1, x4, x0, x2, x3, x5, x7]), (x1 &&& x4, x7, [x1, x4, x0, x2, x3, x5, x6]), (x1, x4, [x1 &&& x4, x0, x2, x3, x5, x6, x7]), (x1, x0, [x1 &&& x4, x4, x2, x3, x5, x6, x7]), (x1, x2, [x1 &&& x4, x4, x0, x3, x5, x6, x7]), (x1, x3, [x1 &&& x4, x4, x0, x2, x5, x6, x7]), (x1, x5, [x1 &&& x4, x4, x0, x2, x3, x6, x7]), (x1, x6, [x1 &&& x4, x4, x0, x2, x3, x5, x7]), (x1, x7, [x1 &&& x4, x4, x0, x2, x3, x5, x6]), (x4, x0, [x1 &&& x4, x1, x2, x3, x5, x6, x7]), (x4, x2, [x1 &&& x4, x1, x0, x3, x5, x6, x7]), (x4, x3, [x1 &&& x4, x1, x0, x2, x5, x6, x7]), (x4, x5, [x1 &&& x4, x1, x0, x2, x3, x6, x7]), (x4, x6, [x1 &&& x4, x1, x0, x2, x3, x5, x7]), (x4, x7, [x1 &&& x4, x1, x0, x2, x3, x5, x6]), (x0, x2, [x1 &&& x4, x1, x4, x3, x5, x6, x7]), (x0, x3, [x1 &&& x4, x1, x4, x2, x5, x6, x7]), (x0, x5, [x1 &&& x4, x1, x4, x2, x3, x6, x7]), (x0, x6, [x1 &&& x4, x1, x4, x2, x3, x5, x7]), (x0, x7, [x1 &&& x4, x1, x4, x2, x3, x5, x6]), (x2, x3, [x1 &&& x4, x1, x4, x0, x5, x6, x7]), (x2, x5, [x1 &&& x4, x1, x4, x0, x3, x6, x7]), (x2, x6, [x1 &&& x4, x1, x4, x0, x3, x5, x7]), (x2, x7, [x1 &&& x4, x1, x4, x0, x3, x5, x6]), (x3, x5, [x1 &&& x4, x1, x4, x0, x2, x6, x7]), (x3, x6, [x1 &&& x4, x1, x4, x0, x2, x5, x7]), (x3, x7, [x1 &&& x4, x1, x4, x0, x2, x5, x6]), (x5, x6, [x1 &&& x4, x1, x4, x0, x2, x3, x7]), (x5, x7, [x1 &&& x4, x1, x4, x0, x2, x3, x6]), (x6, x7, [x1 &&& x4, x1, x4, x0, x2, x3, x5])] := by
  decide +kernel

theorem t463 : optimized 8 0 [x1 &&& x4, x1, x4, x0, x2, x3, x5, x6, x7] = false := by
  rw [optimized.eq_2, t463_pairs]
  simp only [List.any_cons, List.any_nil, t427, t428, t429, t430, t431, t432, t433, t434, t435, t436, t437, t438, t439, t440, t441, t442, t443, t444, t445, t446, t447, t448, t449, t450, t451, t452, t453, t454, t455, t456, t457, t458, t459, t460, t461, t462, Bool.or_false]
  all_goals decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t464 : dispatch 0 (optimized 7) (x1 ||| x4) x1 [x4, x0, x2, x3, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t465 : dispatch 0 (optimized 7) (x1 ||| x4) x4 [x1, x0, x2, x3, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t466 : dispatch 0 (optimized 7) (x1 ||| x4) x0 [x1, x4, x2, x3, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t467 : dispatch 0 (optimized 7) (x1 ||| x4) x2 [x1, x4, x0, x3, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t468 : dispatch 0 (optimized 7) (x1 ||| x4) x3 [x1, x4, x0, x2, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t469 : dispatch 0 (optimized 7) (x1 ||| x4) x5 [x1, x4, x0, x2, x3, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t470 : dispatch 0 (optimized 7) (x1 ||| x4) x6 [x1, x4, x0, x2, x3, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t471 : dispatch 0 (optimized 7) (x1 ||| x4) x7 [x1, x4, x0, x2, x3, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t472 : dispatch 0 (optimized 7) x1 x4 [x1 ||| x4, x0, x2, x3, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t473 : dispatch 0 (optimized 7) x1 x0 [x1 ||| x4, x4, x2, x3, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t474 : dispatch 0 (optimized 7) x1 x2 [x1 ||| x4, x4, x0, x3, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t475 : dispatch 0 (optimized 7) x1 x3 [x1 ||| x4, x4, x0, x2, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t476 : dispatch 0 (optimized 7) x1 x5 [x1 ||| x4, x4, x0, x2, x3, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t477 : dispatch 0 (optimized 7) x1 x6 [x1 ||| x4, x4, x0, x2, x3, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t478 : dispatch 0 (optimized 7) x1 x7 [x1 ||| x4, x4, x0, x2, x3, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t479 : dispatch 0 (optimized 7) x4 x0 [x1 ||| x4, x1, x2, x3, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t480 : dispatch 0 (optimized 7) x4 x2 [x1 ||| x4, x1, x0, x3, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t481 : dispatch 0 (optimized 7) x4 x3 [x1 ||| x4, x1, x0, x2, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t482 : dispatch 0 (optimized 7) x4 x5 [x1 ||| x4, x1, x0, x2, x3, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t483 : dispatch 0 (optimized 7) x4 x6 [x1 ||| x4, x1, x0, x2, x3, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t484 : dispatch 0 (optimized 7) x4 x7 [x1 ||| x4, x1, x0, x2, x3, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t485 : dispatch 0 (optimized 7) x0 x2 [x1 ||| x4, x1, x4, x3, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t486 : dispatch 0 (optimized 7) x0 x3 [x1 ||| x4, x1, x4, x2, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t487 : dispatch 0 (optimized 7) x0 x5 [x1 ||| x4, x1, x4, x2, x3, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t488 : dispatch 0 (optimized 7) x0 x6 [x1 ||| x4, x1, x4, x2, x3, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t489 : dispatch 0 (optimized 7) x0 x7 [x1 ||| x4, x1, x4, x2, x3, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t490 : dispatch 0 (optimized 7) x2 x3 [x1 ||| x4, x1, x4, x0, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t491 : dispatch 0 (optimized 7) x2 x5 [x1 ||| x4, x1, x4, x0, x3, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t492 : dispatch 0 (optimized 7) x2 x6 [x1 ||| x4, x1, x4, x0, x3, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t493 : dispatch 0 (optimized 7) x2 x7 [x1 ||| x4, x1, x4, x0, x3, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t494 : dispatch 0 (optimized 7) x3 x5 [x1 ||| x4, x1, x4, x0, x2, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t495 : dispatch 0 (optimized 7) x3 x6 [x1 ||| x4, x1, x4, x0, x2, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t496 : dispatch 0 (optimized 7) x3 x7 [x1 ||| x4, x1, x4, x0, x2, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t497 : dispatch 0 (optimized 7) x5 x6 [x1 ||| x4, x1, x4, x0, x2, x3, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t498 : dispatch 0 (optimized 7) x5 x7 [x1 ||| x4, x1, x4, x0, x2, x3, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t499 : dispatch 0 (optimized 7) x6 x7 [x1 ||| x4, x1, x4, x0, x2, x3, x5] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
theorem t500_pairs : pairs [x1 ||| x4, x1, x4, x0, x2, x3, x5, x6, x7] = [(x1 ||| x4, x1, [x4, x0, x2, x3, x5, x6, x7]), (x1 ||| x4, x4, [x1, x0, x2, x3, x5, x6, x7]), (x1 ||| x4, x0, [x1, x4, x2, x3, x5, x6, x7]), (x1 ||| x4, x2, [x1, x4, x0, x3, x5, x6, x7]), (x1 ||| x4, x3, [x1, x4, x0, x2, x5, x6, x7]), (x1 ||| x4, x5, [x1, x4, x0, x2, x3, x6, x7]), (x1 ||| x4, x6, [x1, x4, x0, x2, x3, x5, x7]), (x1 ||| x4, x7, [x1, x4, x0, x2, x3, x5, x6]), (x1, x4, [x1 ||| x4, x0, x2, x3, x5, x6, x7]), (x1, x0, [x1 ||| x4, x4, x2, x3, x5, x6, x7]), (x1, x2, [x1 ||| x4, x4, x0, x3, x5, x6, x7]), (x1, x3, [x1 ||| x4, x4, x0, x2, x5, x6, x7]), (x1, x5, [x1 ||| x4, x4, x0, x2, x3, x6, x7]), (x1, x6, [x1 ||| x4, x4, x0, x2, x3, x5, x7]), (x1, x7, [x1 ||| x4, x4, x0, x2, x3, x5, x6]), (x4, x0, [x1 ||| x4, x1, x2, x3, x5, x6, x7]), (x4, x2, [x1 ||| x4, x1, x0, x3, x5, x6, x7]), (x4, x3, [x1 ||| x4, x1, x0, x2, x5, x6, x7]), (x4, x5, [x1 ||| x4, x1, x0, x2, x3, x6, x7]), (x4, x6, [x1 ||| x4, x1, x0, x2, x3, x5, x7]), (x4, x7, [x1 ||| x4, x1, x0, x2, x3, x5, x6]), (x0, x2, [x1 ||| x4, x1, x4, x3, x5, x6, x7]), (x0, x3, [x1 ||| x4, x1, x4, x2, x5, x6, x7]), (x0, x5, [x1 ||| x4, x1, x4, x2, x3, x6, x7]), (x0, x6, [x1 ||| x4, x1, x4, x2, x3, x5, x7]), (x0, x7, [x1 ||| x4, x1, x4, x2, x3, x5, x6]), (x2, x3, [x1 ||| x4, x1, x4, x0, x5, x6, x7]), (x2, x5, [x1 ||| x4, x1, x4, x0, x3, x6, x7]), (x2, x6, [x1 ||| x4, x1, x4, x0, x3, x5, x7]), (x2, x7, [x1 ||| x4, x1, x4, x0, x3, x5, x6]), (x3, x5, [x1 ||| x4, x1, x4, x0, x2, x6, x7]), (x3, x6, [x1 ||| x4, x1, x4, x0, x2, x5, x7]), (x3, x7, [x1 ||| x4, x1, x4, x0, x2, x5, x6]), (x5, x6, [x1 ||| x4, x1, x4, x0, x2, x3, x7]), (x5, x7, [x1 ||| x4, x1, x4, x0, x2, x3, x6]), (x6, x7, [x1 ||| x4, x1, x4, x0, x2, x3, x5])] := by
  decide +kernel

theorem t500 : optimized 8 0 [x1 ||| x4, x1, x4, x0, x2, x3, x5, x6, x7] = false := by
  rw [optimized.eq_2, t500_pairs]
  simp only [List.any_cons, List.any_nil, t464, t465, t466, t467, t468, t469, t470, t471, t472, t473, t474, t475, t476, t477, t478, t479, t480, t481, t482, t483, t484, t485, t486, t487, t488, t489, t490, t491, t492, t493, t494, t495, t496, t497, t498, t499, Bool.or_false]
  all_goals decide +kernel

theorem t501 : dispatch 2 (optimized 8) x1 x4 [x0, x2, x3, x5, x6, x7] = false := by
  simp only [dispatch, ops, List.any_cons, List.any_nil, Nat.reduceSub, t463, t500, Bool.and_false, Bool.or_false]
  all_goals decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t502 : optimized 8 0 [x1 &&& x5, x1, x5, x0, x2, x3, x4, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t503 : optimized 8 0 [x1 ||| x5, x1, x5, x0, x2, x3, x4, x6, x7] = false := by
  decide +kernel

theorem t504 : dispatch 2 (optimized 8) x1 x5 [x0, x2, x3, x4, x6, x7] = false := by
  simp only [dispatch, ops, List.any_cons, List.any_nil, Nat.reduceSub, t502, t503, Bool.and_false, Bool.or_false]
  all_goals decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t505 : dispatch 2 (optimized 8) x1 x6 [x0, x2, x3, x4, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t506 : optimized 8 0 [x1 &&& x7, x1, x7, x0, x2, x3, x4, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t507 : dispatch 2 (optimized 7) (x1 ||| x7) x0 [x2, x3, x4, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t508 : dispatch 2 (optimized 7) (x1 ||| x7) x2 [x0, x3, x4, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t509 : dispatch 2 (optimized 7) (x1 ||| x7) x3 [x0, x2, x4, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t510 : dispatch 2 (optimized 7) (x1 ||| x7) x4 [x0, x2, x3, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t511 : dispatch 2 (optimized 7) (x1 ||| x7) x5 [x0, x2, x3, x4, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t512 : dispatch 2 (optimized 7) (x1 ||| x7) x6 [x0, x2, x3, x4, x5] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t513 : dispatch 2 (optimized 7) x0 x2 [x1 ||| x7, x3, x4, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t514 : dispatch 2 (optimized 7) x0 x3 [x1 ||| x7, x2, x4, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t515 : dispatch 2 (optimized 7) x0 x4 [x1 ||| x7, x2, x3, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t516 : dispatch 2 (optimized 7) x0 x5 [x1 ||| x7, x2, x3, x4, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t517 : dispatch 2 (optimized 7) x0 x6 [x1 ||| x7, x2, x3, x4, x5] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t518 : dispatch 2 (optimized 7) x2 x3 [x1 ||| x7, x0, x4, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t519 : dispatch 2 (optimized 7) x2 x4 [x1 ||| x7, x0, x3, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t520 : dispatch 2 (optimized 7) x2 x5 [x1 ||| x7, x0, x3, x4, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t521 : dispatch 2 (optimized 7) x2 x6 [x1 ||| x7, x0, x3, x4, x5] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t522 : dispatch 2 (optimized 7) x3 x4 [x1 ||| x7, x0, x2, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t523 : dispatch 2 (optimized 7) x3 x5 [x1 ||| x7, x0, x2, x4, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t524 : dispatch 2 (optimized 7) x3 x6 [x1 ||| x7, x0, x2, x4, x5] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t525 : dispatch 2 (optimized 7) x4 x5 [x1 ||| x7, x0, x2, x3, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t526 : dispatch 2 (optimized 7) x4 x6 [x1 ||| x7, x0, x2, x3, x5] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t527 : dispatch 2 (optimized 7) x5 x6 [x1 ||| x7, x0, x2, x3, x4] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
theorem t528_pairs : pairs [x1 ||| x7, x0, x2, x3, x4, x5, x6] = [(x1 ||| x7, x0, [x2, x3, x4, x5, x6]), (x1 ||| x7, x2, [x0, x3, x4, x5, x6]), (x1 ||| x7, x3, [x0, x2, x4, x5, x6]), (x1 ||| x7, x4, [x0, x2, x3, x5, x6]), (x1 ||| x7, x5, [x0, x2, x3, x4, x6]), (x1 ||| x7, x6, [x0, x2, x3, x4, x5]), (x0, x2, [x1 ||| x7, x3, x4, x5, x6]), (x0, x3, [x1 ||| x7, x2, x4, x5, x6]), (x0, x4, [x1 ||| x7, x2, x3, x5, x6]), (x0, x5, [x1 ||| x7, x2, x3, x4, x6]), (x0, x6, [x1 ||| x7, x2, x3, x4, x5]), (x2, x3, [x1 ||| x7, x0, x4, x5, x6]), (x2, x4, [x1 ||| x7, x0, x3, x5, x6]), (x2, x5, [x1 ||| x7, x0, x3, x4, x6]), (x2, x6, [x1 ||| x7, x0, x3, x4, x5]), (x3, x4, [x1 ||| x7, x0, x2, x5, x6]), (x3, x5, [x1 ||| x7, x0, x2, x4, x6]), (x3, x6, [x1 ||| x7, x0, x2, x4, x5]), (x4, x5, [x1 ||| x7, x0, x2, x3, x6]), (x4, x6, [x1 ||| x7, x0, x2, x3, x5]), (x5, x6, [x1 ||| x7, x0, x2, x3, x4])] := by
  decide +kernel

theorem t528 : optimized 8 2 [x1 ||| x7, x0, x2, x3, x4, x5, x6] = false := by
  rw [optimized.eq_2, t528_pairs]
  simp only [List.any_cons, List.any_nil, t507, t508, t509, t510, t511, t512, t513, t514, t515, t516, t517, t518, t519, t520, t521, t522, t523, t524, t525, t526, t527, Bool.or_false]
  all_goals decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t529 : dispatch 1 (optimized 7) (x1 ||| x7) x1 [x0, x2, x3, x4, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t530 : dispatch 1 (optimized 7) (x1 ||| x7) x0 [x1, x2, x3, x4, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t531 : dispatch 1 (optimized 7) (x1 ||| x7) x2 [x1, x0, x3, x4, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t532 : dispatch 1 (optimized 7) (x1 ||| x7) x3 [x1, x0, x2, x4, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t533 : dispatch 1 (optimized 7) (x1 ||| x7) x4 [x1, x0, x2, x3, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t534 : dispatch 1 (optimized 7) (x1 ||| x7) x5 [x1, x0, x2, x3, x4, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t535 : dispatch 1 (optimized 7) (x1 ||| x7) x6 [x1, x0, x2, x3, x4, x5] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t536 : dispatch 1 (optimized 7) x1 x0 [x1 ||| x7, x2, x3, x4, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t537 : dispatch 1 (optimized 7) x1 x2 [x1 ||| x7, x0, x3, x4, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t538 : dispatch 1 (optimized 7) x1 x3 [x1 ||| x7, x0, x2, x4, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t539 : dispatch 1 (optimized 7) x1 x4 [x1 ||| x7, x0, x2, x3, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t540 : dispatch 1 (optimized 7) x1 x5 [x1 ||| x7, x0, x2, x3, x4, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t541 : dispatch 1 (optimized 7) x1 x6 [x1 ||| x7, x0, x2, x3, x4, x5] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t542 : dispatch 1 (optimized 7) x0 x2 [x1 ||| x7, x1, x3, x4, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t543 : dispatch 1 (optimized 7) x0 x3 [x1 ||| x7, x1, x2, x4, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t544 : dispatch 1 (optimized 7) x0 x4 [x1 ||| x7, x1, x2, x3, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t545 : dispatch 1 (optimized 7) x0 x5 [x1 ||| x7, x1, x2, x3, x4, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t546 : dispatch 1 (optimized 7) x0 x6 [x1 ||| x7, x1, x2, x3, x4, x5] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t547 : dispatch 1 (optimized 7) x2 x3 [x1 ||| x7, x1, x0, x4, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t548 : dispatch 1 (optimized 7) x2 x4 [x1 ||| x7, x1, x0, x3, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t549 : dispatch 1 (optimized 7) x2 x5 [x1 ||| x7, x1, x0, x3, x4, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t550 : dispatch 1 (optimized 7) x2 x6 [x1 ||| x7, x1, x0, x3, x4, x5] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t551 : dispatch 1 (optimized 7) x3 x4 [x1 ||| x7, x1, x0, x2, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t552 : dispatch 1 (optimized 7) x3 x5 [x1 ||| x7, x1, x0, x2, x4, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t553 : dispatch 1 (optimized 7) x3 x6 [x1 ||| x7, x1, x0, x2, x4, x5] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t554 : dispatch 1 (optimized 7) x4 x5 [x1 ||| x7, x1, x0, x2, x3, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t555 : dispatch 1 (optimized 7) x4 x6 [x1 ||| x7, x1, x0, x2, x3, x5] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t556 : dispatch 1 (optimized 7) x5 x6 [x1 ||| x7, x1, x0, x2, x3, x4] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
theorem t557_pairs : pairs [x1 ||| x7, x1, x0, x2, x3, x4, x5, x6] = [(x1 ||| x7, x1, [x0, x2, x3, x4, x5, x6]), (x1 ||| x7, x0, [x1, x2, x3, x4, x5, x6]), (x1 ||| x7, x2, [x1, x0, x3, x4, x5, x6]), (x1 ||| x7, x3, [x1, x0, x2, x4, x5, x6]), (x1 ||| x7, x4, [x1, x0, x2, x3, x5, x6]), (x1 ||| x7, x5, [x1, x0, x2, x3, x4, x6]), (x1 ||| x7, x6, [x1, x0, x2, x3, x4, x5]), (x1, x0, [x1 ||| x7, x2, x3, x4, x5, x6]), (x1, x2, [x1 ||| x7, x0, x3, x4, x5, x6]), (x1, x3, [x1 ||| x7, x0, x2, x4, x5, x6]), (x1, x4, [x1 ||| x7, x0, x2, x3, x5, x6]), (x1, x5, [x1 ||| x7, x0, x2, x3, x4, x6]), (x1, x6, [x1 ||| x7, x0, x2, x3, x4, x5]), (x0, x2, [x1 ||| x7, x1, x3, x4, x5, x6]), (x0, x3, [x1 ||| x7, x1, x2, x4, x5, x6]), (x0, x4, [x1 ||| x7, x1, x2, x3, x5, x6]), (x0, x5, [x1 ||| x7, x1, x2, x3, x4, x6]), (x0, x6, [x1 ||| x7, x1, x2, x3, x4, x5]), (x2, x3, [x1 ||| x7, x1, x0, x4, x5, x6]), (x2, x4, [x1 ||| x7, x1, x0, x3, x5, x6]), (x2, x5, [x1 ||| x7, x1, x0, x3, x4, x6]), (x2, x6, [x1 ||| x7, x1, x0, x3, x4, x5]), (x3, x4, [x1 ||| x7, x1, x0, x2, x5, x6]), (x3, x5, [x1 ||| x7, x1, x0, x2, x4, x6]), (x3, x6, [x1 ||| x7, x1, x0, x2, x4, x5]), (x4, x5, [x1 ||| x7, x1, x0, x2, x3, x6]), (x4, x6, [x1 ||| x7, x1, x0, x2, x3, x5]), (x5, x6, [x1 ||| x7, x1, x0, x2, x3, x4])] := by
  decide +kernel

theorem t557 : optimized 8 1 [x1 ||| x7, x1, x0, x2, x3, x4, x5, x6] = false := by
  rw [optimized.eq_2, t557_pairs]
  simp only [List.any_cons, List.any_nil, t529, t530, t531, t532, t533, t534, t535, t536, t537, t538, t539, t540, t541, t542, t543, t544, t545, t546, t547, t548, t549, t550, t551, t552, t553, t554, t555, t556, Bool.or_false]
  all_goals decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t558 : optimized 8 1 [x1 ||| x7, x7, x0, x2, x3, x4, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t559 : optimized 8 0 [x1 ||| x7, x1, x7, x0, x2, x3, x4, x5, x6] = false := by
  decide +kernel

theorem t560 : dispatch 2 (optimized 8) x1 x7 [x0, x2, x3, x4, x5, x6] = false := by
  simp only [dispatch, ops, List.any_cons, List.any_nil, Nat.reduceSub, t506, t528, t557, t558, t559, Bool.and_false, Bool.or_false]
  all_goals decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t561 : dispatch 2 (optimized 8) x2 x3 [x0, x1, x4, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t562 : optimized 8 0 [x2 &&& x4, x2, x4, x0, x1, x3, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t563 : dispatch 2 (optimized 7) (x2 ||| x4) x0 [x1, x3, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t564 : dispatch 2 (optimized 7) (x2 ||| x4) x1 [x0, x3, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t565 : dispatch 2 (optimized 7) (x2 ||| x4) x3 [x0, x1, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t566 : dispatch 2 (optimized 7) (x2 ||| x4) x5 [x0, x1, x3, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t567 : dispatch 2 (optimized 7) (x2 ||| x4) x6 [x0, x1, x3, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t568 : dispatch 2 (optimized 7) (x2 ||| x4) x7 [x0, x1, x3, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t569 : dispatch 2 (optimized 7) x0 x1 [x2 ||| x4, x3, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t570 : dispatch 2 (optimized 7) x0 x3 [x2 ||| x4, x1, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t571 : dispatch 2 (optimized 7) x0 x5 [x2 ||| x4, x1, x3, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t572 : optimized 7 0 [x0 &&& x6, x0, x6, x2 ||| x4, x1, x3, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t573 : optimized 7 2 [x0 ||| x6, x2 ||| x4, x1, x3, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t574 : optimized 7 1 [x0 ||| x6, x0, x2 ||| x4, x1, x3, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t575 : optimized 7 1 [x0 ||| x6, x6, x2 ||| x4, x1, x3, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t576 : optimized 7 0 [x0 ||| x6, x0, x6, x2 ||| x4, x1, x3, x5, x7] = false := by
  decide +kernel

theorem t577 : dispatch 2 (optimized 7) x0 x6 [x2 ||| x4, x1, x3, x5, x7] = false := by
  simp only [dispatch, ops, List.any_cons, List.any_nil, Nat.reduceSub, t572, t573, t574, t575, t576, Bool.and_false, Bool.or_false]
  all_goals decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t578 : dispatch 1 (optimized 6) (x0 &&& x7) (x2 ||| x4) [x0, x1, x3, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t579 : dispatch 1 (optimized 6) (x0 &&& x7) x1 [x0, x2 ||| x4, x3, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t580 : dispatch 1 (optimized 6) (x0 &&& x7) x3 [x0, x2 ||| x4, x1, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t581 : dispatch 1 (optimized 6) (x0 &&& x7) x5 [x0, x2 ||| x4, x1, x3, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t582 : dispatch 1 (optimized 6) (x0 &&& x7) x6 [x0, x2 ||| x4, x1, x3, x5] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t583 : dispatch 1 (optimized 6) x0 (x2 ||| x4) [x0 &&& x7, x1, x3, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t584 : dispatch 1 (optimized 6) x0 x1 [x0 &&& x7, x2 ||| x4, x3, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t585 : dispatch 1 (optimized 6) x0 x3 [x0 &&& x7, x2 ||| x4, x1, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t586 : dispatch 1 (optimized 6) x0 x5 [x0 &&& x7, x2 ||| x4, x1, x3, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t587 : dispatch 1 (optimized 6) x0 x6 [x0 &&& x7, x2 ||| x4, x1, x3, x5] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t588 : dispatch 1 (optimized 6) x1 x3 [x0 &&& x7, x0, x2 ||| x4, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t589 : dispatch 1 (optimized 6) x1 x5 [x0 &&& x7, x0, x2 ||| x4, x3, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t590 : dispatch 1 (optimized 6) x1 x6 [x0 &&& x7, x0, x2 ||| x4, x3, x5] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t591 : dispatch 1 (optimized 6) x3 x5 [x0 &&& x7, x0, x2 ||| x4, x1, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t592 : dispatch 1 (optimized 6) x3 x6 [x0 &&& x7, x0, x2 ||| x4, x1, x5] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t593 : dispatch 1 (optimized 6) x5 x6 [x0 &&& x7, x0, x2 ||| x4, x1, x3] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
theorem t594_pairs : pairs [x0 &&& x7, x0, x2 ||| x4, x1, x3, x5, x6] = [(x0 &&& x7, x0, [x2 ||| x4, x1, x3, x5, x6]), (x0 &&& x7, x2 ||| x4, [x0, x1, x3, x5, x6]), (x0 &&& x7, x1, [x0, x2 ||| x4, x3, x5, x6]), (x0 &&& x7, x3, [x0, x2 ||| x4, x1, x5, x6]), (x0 &&& x7, x5, [x0, x2 ||| x4, x1, x3, x6]), (x0 &&& x7, x6, [x0, x2 ||| x4, x1, x3, x5]), (x0, x2 ||| x4, [x0 &&& x7, x1, x3, x5, x6]), (x0, x1, [x0 &&& x7, x2 ||| x4, x3, x5, x6]), (x0, x3, [x0 &&& x7, x2 ||| x4, x1, x5, x6]), (x0, x5, [x0 &&& x7, x2 ||| x4, x1, x3, x6]), (x0, x6, [x0 &&& x7, x2 ||| x4, x1, x3, x5]), (x2 ||| x4, x1, [x0 &&& x7, x0, x3, x5, x6]), (x2 ||| x4, x3, [x0 &&& x7, x0, x1, x5, x6]), (x2 ||| x4, x5, [x0 &&& x7, x0, x1, x3, x6]), (x2 ||| x4, x6, [x0 &&& x7, x0, x1, x3, x5]), (x1, x3, [x0 &&& x7, x0, x2 ||| x4, x5, x6]), (x1, x5, [x0 &&& x7, x0, x2 ||| x4, x3, x6]), (x1, x6, [x0 &&& x7, x0, x2 ||| x4, x3, x5]), (x3, x5, [x0 &&& x7, x0, x2 ||| x4, x1, x6]), (x3, x6, [x0 &&& x7, x0, x2 ||| x4, x1, x5]), (x5, x6, [x0 &&& x7, x0, x2 ||| x4, x1, x3])] := by
  decide +kernel

theorem t594 : optimized 7 1 [x0 &&& x7, x0, x2 ||| x4, x1, x3, x5, x6] = false := by
  rw [optimized.eq_2, t594_pairs]
  simp only [List.any_cons, List.any_nil, t281, t578, t579, t580, t581, t582, t583, t584, t585, t586, t587, t277, t278, t279, t280, t588, t589, t590, t591, t592, t593, Bool.or_false]
  all_goals decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t595 : optimized 7 0 [x0 &&& x7, x0, x7, x2 ||| x4, x1, x3, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t596 : optimized 7 0 [x0 ||| x7, x0, x7, x2 ||| x4, x1, x3, x5, x6] = false := by
  decide +kernel

theorem t597 : dispatch 2 (optimized 7) x0 x7 [x2 ||| x4, x1, x3, x5, x6] = false := by
  simp only [dispatch, ops, List.any_cons, List.any_nil, Nat.reduceSub, t594, t595, t596, Bool.and_false, Bool.or_false]
  all_goals decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t598 : dispatch 2 (optimized 7) x1 x3 [x2 ||| x4, x0, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t599 : dispatch 2 (optimized 7) x1 x5 [x2 ||| x4, x0, x3, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t600 : dispatch 2 (optimized 7) x1 x6 [x2 ||| x4, x0, x3, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t601 : dispatch 2 (optimized 7) x1 x7 [x2 ||| x4, x0, x3, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t602 : optimized 7 0 [x3 &&& x5, x3, x5, x2 ||| x4, x0, x1, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t603 : optimized 7 2 [x3 ||| x5, x2 ||| x4, x0, x1, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t604 : optimized 7 1 [x3 ||| x5, x3, x2 ||| x4, x0, x1, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t605 : optimized 7 1 [x3 ||| x5, x5, x2 ||| x4, x0, x1, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t606 : optimized 7 0 [x3 ||| x5, x3, x5, x2 ||| x4, x0, x1, x6, x7] = false := by
  decide +kernel

theorem t607 : dispatch 2 (optimized 7) x3 x5 [x2 ||| x4, x0, x1, x6, x7] = false := by
  simp only [dispatch, ops, List.any_cons, List.any_nil, Nat.reduceSub, t602, t603, t604, t605, t606, Bool.and_false, Bool.or_false]
  all_goals decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t608 : dispatch 2 (optimized 7) x3 x6 [x2 ||| x4, x0, x1, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t609 : dispatch 2 (optimized 7) x3 x7 [x2 ||| x4, x0, x1, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t610 : dispatch 2 (optimized 7) x5 x6 [x2 ||| x4, x0, x1, x3, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t611 : optimized 7 0 [x5 &&& x7, x5, x7, x2 ||| x4, x0, x1, x3, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t612 : dispatch 1 (optimized 6) (x5 ||| x7) x5 [x2 ||| x4, x0, x1, x3, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t613 : dispatch 1 (optimized 6) (x5 ||| x7) (x2 ||| x4) [x5, x0, x1, x3, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t614 : dispatch 1 (optimized 6) (x5 ||| x7) x0 [x5, x2 ||| x4, x1, x3, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t615 : dispatch 1 (optimized 6) (x5 ||| x7) x1 [x5, x2 ||| x4, x0, x3, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t616 : dispatch 1 (optimized 6) (x5 ||| x7) x3 [x5, x2 ||| x4, x0, x1, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t617 : dispatch 1 (optimized 6) (x5 ||| x7) x6 [x5, x2 ||| x4, x0, x1, x3] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t618 : dispatch 1 (optimized 6) x5 (x2 ||| x4) [x5 ||| x7, x0, x1, x3, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t619 : dispatch 1 (optimized 6) x5 x0 [x5 ||| x7, x2 ||| x4, x1, x3, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t620 : dispatch 1 (optimized 6) x5 x1 [x5 ||| x7, x2 ||| x4, x0, x3, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t621 : dispatch 1 (optimized 6) x5 x3 [x5 ||| x7, x2 ||| x4, x0, x1, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t622 : dispatch 1 (optimized 6) x5 x6 [x5 ||| x7, x2 ||| x4, x0, x1, x3] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t623 : dispatch 1 (optimized 6) (x2 ||| x4) x0 [x5 ||| x7, x5, x1, x3, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t624 : dispatch 1 (optimized 6) (x2 ||| x4) x1 [x5 ||| x7, x5, x0, x3, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t625 : dispatch 1 (optimized 6) (x2 ||| x4) x3 [x5 ||| x7, x5, x0, x1, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t626 : dispatch 1 (optimized 6) (x2 ||| x4) x6 [x5 ||| x7, x5, x0, x1, x3] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t627 : dispatch 1 (optimized 6) x0 x1 [x5 ||| x7, x5, x2 ||| x4, x3, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t628 : dispatch 1 (optimized 6) x0 x3 [x5 ||| x7, x5, x2 ||| x4, x1, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t629 : dispatch 1 (optimized 6) x0 x6 [x5 ||| x7, x5, x2 ||| x4, x1, x3] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t630 : dispatch 1 (optimized 6) x1 x3 [x5 ||| x7, x5, x2 ||| x4, x0, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t631 : dispatch 1 (optimized 6) x1 x6 [x5 ||| x7, x5, x2 ||| x4, x0, x3] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t632 : dispatch 1 (optimized 6) x3 x6 [x5 ||| x7, x5, x2 ||| x4, x0, x1] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
theorem t633_pairs : pairs [x5 ||| x7, x5, x2 ||| x4, x0, x1, x3, x6] = [(x5 ||| x7, x5, [x2 ||| x4, x0, x1, x3, x6]), (x5 ||| x7, x2 ||| x4, [x5, x0, x1, x3, x6]), (x5 ||| x7, x0, [x5, x2 ||| x4, x1, x3, x6]), (x5 ||| x7, x1, [x5, x2 ||| x4, x0, x3, x6]), (x5 ||| x7, x3, [x5, x2 ||| x4, x0, x1, x6]), (x5 ||| x7, x6, [x5, x2 ||| x4, x0, x1, x3]), (x5, x2 ||| x4, [x5 ||| x7, x0, x1, x3, x6]), (x5, x0, [x5 ||| x7, x2 ||| x4, x1, x3, x6]), (x5, x1, [x5 ||| x7, x2 ||| x4, x0, x3, x6]), (x5, x3, [x5 ||| x7, x2 ||| x4, x0, x1, x6]), (x5, x6, [x5 ||| x7, x2 ||| x4, x0, x1, x3]), (x2 ||| x4, x0, [x5 ||| x7, x5, x1, x3, x6]), (x2 ||| x4, x1, [x5 ||| x7, x5, x0, x3, x6]), (x2 ||| x4, x3, [x5 ||| x7, x5, x0, x1, x6]), (x2 ||| x4, x6, [x5 ||| x7, x5, x0, x1, x3]), (x0, x1, [x5 ||| x7, x5, x2 ||| x4, x3, x6]), (x0, x3, [x5 ||| x7, x5, x2 ||| x4, x1, x6]), (x0, x6, [x5 ||| x7, x5, x2 ||| x4, x1, x3]), (x1, x3, [x5 ||| x7, x5, x2 ||| x4, x0, x6]), (x1, x6, [x5 ||| x7, x5, x2 ||| x4, x0, x3]), (x3, x6, [x5 ||| x7, x5, x2 ||| x4, x0, x1])] := by
  decide +kernel

theorem t633 : optimized 7 1 [x5 ||| x7, x5, x2 ||| x4, x0, x1, x3, x6] = false := by
  rw [optimized.eq_2, t633_pairs]
  simp only [List.any_cons, List.any_nil, t612, t613, t614, t615, t616, t617, t618, t619, t620, t621, t622, t623, t624, t625, t626, t627, t628, t629, t630, t631, t632, Bool.or_false]
  all_goals decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t634 : optimized 7 0 [x5 ||| x7, x5, x7, x2 ||| x4, x0, x1, x3, x6] = false := by
  decide +kernel

theorem t635 : dispatch 2 (optimized 7) x5 x7 [x2 ||| x4, x0, x1, x3, x6] = false := by
  simp only [dispatch, ops, List.any_cons, List.any_nil, Nat.reduceSub, t611, t633, t634, Bool.and_false, Bool.or_false]
  all_goals decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t636 : dispatch 2 (optimized 7) x6 x7 [x2 ||| x4, x0, x1, x3, x5] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
theorem t637_pairs : pairs [x2 ||| x4, x0, x1, x3, x5, x6, x7] = [(x2 ||| x4, x0, [x1, x3, x5, x6, x7]), (x2 ||| x4, x1, [x0, x3, x5, x6, x7]), (x2 ||| x4, x3, [x0, x1, x5, x6, x7]), (x2 ||| x4, x5, [x0, x1, x3, x6, x7]), (x2 ||| x4, x6, [x0, x1, x3, x5, x7]), (x2 ||| x4, x7, [x0, x1, x3, x5, x6]), (x0, x1, [x2 ||| x4, x3, x5, x6, x7]), (x0, x3, [x2 ||| x4, x1, x5, x6, x7]), (x0, x5, [x2 ||| x4, x1, x3, x6, x7]), (x0, x6, [x2 ||| x4, x1, x3, x5, x7]), (x0, x7, [x2 ||| x4, x1, x3, x5, x6]), (x1, x3, [x2 ||| x4, x0, x5, x6, x7]), (x1, x5, [x2 ||| x4, x0, x3, x6, x7]), (x1, x6, [x2 ||| x4, x0, x3, x5, x7]), (x1, x7, [x2 ||| x4, x0, x3, x5, x6]), (x3, x5, [x2 ||| x4, x0, x1, x6, x7]), (x3, x6, [x2 ||| x4, x0, x1, x5, x7]), (x3, x7, [x2 ||| x4, x0, x1, x5, x6]), (x5, x6, [x2 ||| x4, x0, x1, x3, x7]), (x5, x7, [x2 ||| x4, x0, x1, x3, x6]), (x6, x7, [x2 ||| x4, x0, x1, x3, x5])] := by
  decide +kernel

theorem t637 : optimized 8 2 [x2 ||| x4, x0, x1, x3, x5, x6, x7] = false := by
  rw [optimized.eq_2, t637_pairs]
  simp only [List.any_cons, List.any_nil, t563, t564, t565, t566, t567, t568, t569, t570, t571, t577, t597, t598, t599, t600, t601, t607, t608, t609, t610, t635, t636, Bool.or_false]
  all_goals decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t638 : dispatch 1 (optimized 7) (x2 ||| x4) x2 [x0, x1, x3, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t639 : dispatch 1 (optimized 7) (x2 ||| x4) x0 [x2, x1, x3, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t640 : dispatch 1 (optimized 7) (x2 ||| x4) x1 [x2, x0, x3, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t641 : dispatch 1 (optimized 7) (x2 ||| x4) x3 [x2, x0, x1, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t642 : dispatch 1 (optimized 7) (x2 ||| x4) x5 [x2, x0, x1, x3, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t643 : dispatch 1 (optimized 7) (x2 ||| x4) x6 [x2, x0, x1, x3, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t644 : dispatch 1 (optimized 7) (x2 ||| x4) x7 [x2, x0, x1, x3, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t645 : dispatch 1 (optimized 7) x2 x0 [x2 ||| x4, x1, x3, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t646 : dispatch 1 (optimized 7) x2 x1 [x2 ||| x4, x0, x3, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t647 : dispatch 1 (optimized 7) x2 x3 [x2 ||| x4, x0, x1, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t648 : dispatch 1 (optimized 7) x2 x5 [x2 ||| x4, x0, x1, x3, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t649 : dispatch 1 (optimized 7) x2 x6 [x2 ||| x4, x0, x1, x3, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t650 : dispatch 1 (optimized 7) x2 x7 [x2 ||| x4, x0, x1, x3, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t651 : dispatch 1 (optimized 7) x0 x1 [x2 ||| x4, x2, x3, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t652 : dispatch 1 (optimized 7) x0 x3 [x2 ||| x4, x2, x1, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t653 : dispatch 1 (optimized 7) x0 x5 [x2 ||| x4, x2, x1, x3, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t654 : dispatch 1 (optimized 7) x0 x6 [x2 ||| x4, x2, x1, x3, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t655 : dispatch 1 (optimized 7) x0 x7 [x2 ||| x4, x2, x1, x3, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t656 : dispatch 1 (optimized 7) x1 x3 [x2 ||| x4, x2, x0, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t657 : dispatch 1 (optimized 7) x1 x5 [x2 ||| x4, x2, x0, x3, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t658 : dispatch 1 (optimized 7) x1 x6 [x2 ||| x4, x2, x0, x3, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t659 : dispatch 1 (optimized 7) x1 x7 [x2 ||| x4, x2, x0, x3, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t660 : dispatch 1 (optimized 7) x3 x5 [x2 ||| x4, x2, x0, x1, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t661 : dispatch 1 (optimized 7) x3 x6 [x2 ||| x4, x2, x0, x1, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t662 : dispatch 1 (optimized 7) x3 x7 [x2 ||| x4, x2, x0, x1, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t663 : dispatch 1 (optimized 7) x5 x6 [x2 ||| x4, x2, x0, x1, x3, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t664 : dispatch 1 (optimized 7) x5 x7 [x2 ||| x4, x2, x0, x1, x3, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t665 : dispatch 1 (optimized 7) x6 x7 [x2 ||| x4, x2, x0, x1, x3, x5] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
theorem t666_pairs : pairs [x2 ||| x4, x2, x0, x1, x3, x5, x6, x7] = [(x2 ||| x4, x2, [x0, x1, x3, x5, x6, x7]), (x2 ||| x4, x0, [x2, x1, x3, x5, x6, x7]), (x2 ||| x4, x1, [x2, x0, x3, x5, x6, x7]), (x2 ||| x4, x3, [x2, x0, x1, x5, x6, x7]), (x2 ||| x4, x5, [x2, x0, x1, x3, x6, x7]), (x2 ||| x4, x6, [x2, x0, x1, x3, x5, x7]), (x2 ||| x4, x7, [x2, x0, x1, x3, x5, x6]), (x2, x0, [x2 ||| x4, x1, x3, x5, x6, x7]), (x2, x1, [x2 ||| x4, x0, x3, x5, x6, x7]), (x2, x3, [x2 ||| x4, x0, x1, x5, x6, x7]), (x2, x5, [x2 ||| x4, x0, x1, x3, x6, x7]), (x2, x6, [x2 ||| x4, x0, x1, x3, x5, x7]), (x2, x7, [x2 ||| x4, x0, x1, x3, x5, x6]), (x0, x1, [x2 ||| x4, x2, x3, x5, x6, x7]), (x0, x3, [x2 ||| x4, x2, x1, x5, x6, x7]), (x0, x5, [x2 ||| x4, x2, x1, x3, x6, x7]), (x0, x6, [x2 ||| x4, x2, x1, x3, x5, x7]), (x0, x7, [x2 ||| x4, x2, x1, x3, x5, x6]), (x1, x3, [x2 ||| x4, x2, x0, x5, x6, x7]), (x1, x5, [x2 ||| x4, x2, x0, x3, x6, x7]), (x1, x6, [x2 ||| x4, x2, x0, x3, x5, x7]), (x1, x7, [x2 ||| x4, x2, x0, x3, x5, x6]), (x3, x5, [x2 ||| x4, x2, x0, x1, x6, x7]), (x3, x6, [x2 ||| x4, x2, x0, x1, x5, x7]), (x3, x7, [x2 ||| x4, x2, x0, x1, x5, x6]), (x5, x6, [x2 ||| x4, x2, x0, x1, x3, x7]), (x5, x7, [x2 ||| x4, x2, x0, x1, x3, x6]), (x6, x7, [x2 ||| x4, x2, x0, x1, x3, x5])] := by
  decide +kernel

theorem t666 : optimized 8 1 [x2 ||| x4, x2, x0, x1, x3, x5, x6, x7] = false := by
  rw [optimized.eq_2, t666_pairs]
  simp only [List.any_cons, List.any_nil, t638, t639, t640, t641, t642, t643, t644, t645, t646, t647, t648, t649, t650, t651, t652, t653, t654, t655, t656, t657, t658, t659, t660, t661, t662, t663, t664, t665, Bool.or_false]
  all_goals decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t667 : dispatch 1 (optimized 7) (x2 ||| x4) x4 [x0, x1, x3, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t668 : dispatch 1 (optimized 7) (x2 ||| x4) x0 [x4, x1, x3, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t669 : dispatch 1 (optimized 7) (x2 ||| x4) x1 [x4, x0, x3, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t670 : dispatch 1 (optimized 7) (x2 ||| x4) x3 [x4, x0, x1, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t671 : dispatch 1 (optimized 7) (x2 ||| x4) x5 [x4, x0, x1, x3, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t672 : dispatch 1 (optimized 7) (x2 ||| x4) x6 [x4, x0, x1, x3, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t673 : dispatch 1 (optimized 7) (x2 ||| x4) x7 [x4, x0, x1, x3, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t674 : dispatch 1 (optimized 7) x4 x0 [x2 ||| x4, x1, x3, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t675 : dispatch 1 (optimized 7) x4 x1 [x2 ||| x4, x0, x3, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t676 : dispatch 1 (optimized 7) x4 x3 [x2 ||| x4, x0, x1, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t677 : dispatch 1 (optimized 7) x4 x5 [x2 ||| x4, x0, x1, x3, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t678 : dispatch 1 (optimized 7) x4 x6 [x2 ||| x4, x0, x1, x3, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t679 : dispatch 1 (optimized 7) x4 x7 [x2 ||| x4, x0, x1, x3, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t680 : dispatch 1 (optimized 7) x0 x1 [x2 ||| x4, x4, x3, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t681 : dispatch 1 (optimized 7) x0 x3 [x2 ||| x4, x4, x1, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t682 : dispatch 1 (optimized 7) x0 x5 [x2 ||| x4, x4, x1, x3, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t683 : dispatch 1 (optimized 7) x0 x6 [x2 ||| x4, x4, x1, x3, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t684 : dispatch 1 (optimized 7) x0 x7 [x2 ||| x4, x4, x1, x3, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t685 : dispatch 1 (optimized 7) x1 x3 [x2 ||| x4, x4, x0, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t686 : dispatch 1 (optimized 7) x1 x5 [x2 ||| x4, x4, x0, x3, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t687 : dispatch 1 (optimized 7) x1 x6 [x2 ||| x4, x4, x0, x3, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t688 : dispatch 1 (optimized 7) x1 x7 [x2 ||| x4, x4, x0, x3, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t689 : dispatch 1 (optimized 7) x3 x5 [x2 ||| x4, x4, x0, x1, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t690 : dispatch 1 (optimized 7) x3 x6 [x2 ||| x4, x4, x0, x1, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t691 : dispatch 1 (optimized 7) x3 x7 [x2 ||| x4, x4, x0, x1, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t692 : dispatch 1 (optimized 7) x5 x6 [x2 ||| x4, x4, x0, x1, x3, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t693 : dispatch 1 (optimized 7) x5 x7 [x2 ||| x4, x4, x0, x1, x3, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t694 : dispatch 1 (optimized 7) x6 x7 [x2 ||| x4, x4, x0, x1, x3, x5] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
theorem t695_pairs : pairs [x2 ||| x4, x4, x0, x1, x3, x5, x6, x7] = [(x2 ||| x4, x4, [x0, x1, x3, x5, x6, x7]), (x2 ||| x4, x0, [x4, x1, x3, x5, x6, x7]), (x2 ||| x4, x1, [x4, x0, x3, x5, x6, x7]), (x2 ||| x4, x3, [x4, x0, x1, x5, x6, x7]), (x2 ||| x4, x5, [x4, x0, x1, x3, x6, x7]), (x2 ||| x4, x6, [x4, x0, x1, x3, x5, x7]), (x2 ||| x4, x7, [x4, x0, x1, x3, x5, x6]), (x4, x0, [x2 ||| x4, x1, x3, x5, x6, x7]), (x4, x1, [x2 ||| x4, x0, x3, x5, x6, x7]), (x4, x3, [x2 ||| x4, x0, x1, x5, x6, x7]), (x4, x5, [x2 ||| x4, x0, x1, x3, x6, x7]), (x4, x6, [x2 ||| x4, x0, x1, x3, x5, x7]), (x4, x7, [x2 ||| x4, x0, x1, x3, x5, x6]), (x0, x1, [x2 ||| x4, x4, x3, x5, x6, x7]), (x0, x3, [x2 ||| x4, x4, x1, x5, x6, x7]), (x0, x5, [x2 ||| x4, x4, x1, x3, x6, x7]), (x0, x6, [x2 ||| x4, x4, x1, x3, x5, x7]), (x0, x7, [x2 ||| x4, x4, x1, x3, x5, x6]), (x1, x3, [x2 ||| x4, x4, x0, x5, x6, x7]), (x1, x5, [x2 ||| x4, x4, x0, x3, x6, x7]), (x1, x6, [x2 ||| x4, x4, x0, x3, x5, x7]), (x1, x7, [x2 ||| x4, x4, x0, x3, x5, x6]), (x3, x5, [x2 ||| x4, x4, x0, x1, x6, x7]), (x3, x6, [x2 ||| x4, x4, x0, x1, x5, x7]), (x3, x7, [x2 ||| x4, x4, x0, x1, x5, x6]), (x5, x6, [x2 ||| x4, x4, x0, x1, x3, x7]), (x5, x7, [x2 ||| x4, x4, x0, x1, x3, x6]), (x6, x7, [x2 ||| x4, x4, x0, x1, x3, x5])] := by
  decide +kernel

theorem t695 : optimized 8 1 [x2 ||| x4, x4, x0, x1, x3, x5, x6, x7] = false := by
  rw [optimized.eq_2, t695_pairs]
  simp only [List.any_cons, List.any_nil, t667, t668, t669, t670, t671, t672, t673, t674, t675, t676, t677, t678, t679, t680, t681, t682, t683, t684, t685, t686, t687, t688, t689, t690, t691, t692, t693, t694, Bool.or_false]
  all_goals decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t696 : optimized 8 0 [x2 ||| x4, x2, x4, x0, x1, x3, x5, x6, x7] = false := by
  decide +kernel

theorem t697 : dispatch 2 (optimized 8) x2 x4 [x0, x1, x3, x5, x6, x7] = false := by
  simp only [dispatch, ops, List.any_cons, List.any_nil, Nat.reduceSub, t562, t637, t666, t695, t696, Bool.and_false, Bool.or_false]
  all_goals decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t698 : dispatch 2 (optimized 8) x2 x5 [x0, x1, x3, x4, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t699 : dispatch 2 (optimized 8) x2 x6 [x0, x1, x3, x4, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t700 : optimized 8 0 [x2 &&& x7, x2, x7, x0, x1, x3, x4, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t701 : dispatch 2 (optimized 7) (x2 ||| x7) x0 [x1, x3, x4, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t702 : dispatch 2 (optimized 7) (x2 ||| x7) x1 [x0, x3, x4, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t703 : dispatch 2 (optimized 7) (x2 ||| x7) x3 [x0, x1, x4, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t704 : dispatch 2 (optimized 7) (x2 ||| x7) x4 [x0, x1, x3, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t705 : dispatch 2 (optimized 7) (x2 ||| x7) x5 [x0, x1, x3, x4, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t706 : dispatch 2 (optimized 7) (x2 ||| x7) x6 [x0, x1, x3, x4, x5] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t707 : dispatch 2 (optimized 7) x0 x1 [x2 ||| x7, x3, x4, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t708 : dispatch 2 (optimized 7) x0 x3 [x2 ||| x7, x1, x4, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t709 : dispatch 2 (optimized 7) x0 x4 [x2 ||| x7, x1, x3, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t710 : dispatch 2 (optimized 7) x0 x5 [x2 ||| x7, x1, x3, x4, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t711 : dispatch 2 (optimized 7) x0 x6 [x2 ||| x7, x1, x3, x4, x5] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t712 : dispatch 2 (optimized 7) x1 x3 [x2 ||| x7, x0, x4, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t713 : dispatch 2 (optimized 7) x1 x4 [x2 ||| x7, x0, x3, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t714 : dispatch 2 (optimized 7) x1 x5 [x2 ||| x7, x0, x3, x4, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t715 : dispatch 2 (optimized 7) x1 x6 [x2 ||| x7, x0, x3, x4, x5] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t716 : dispatch 2 (optimized 7) x3 x4 [x2 ||| x7, x0, x1, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t717 : dispatch 2 (optimized 7) x3 x5 [x2 ||| x7, x0, x1, x4, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t718 : dispatch 2 (optimized 7) x3 x6 [x2 ||| x7, x0, x1, x4, x5] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t719 : dispatch 2 (optimized 7) x4 x5 [x2 ||| x7, x0, x1, x3, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t720 : dispatch 2 (optimized 7) x4 x6 [x2 ||| x7, x0, x1, x3, x5] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t721 : dispatch 2 (optimized 7) x5 x6 [x2 ||| x7, x0, x1, x3, x4] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
theorem t722_pairs : pairs [x2 ||| x7, x0, x1, x3, x4, x5, x6] = [(x2 ||| x7, x0, [x1, x3, x4, x5, x6]), (x2 ||| x7, x1, [x0, x3, x4, x5, x6]), (x2 ||| x7, x3, [x0, x1, x4, x5, x6]), (x2 ||| x7, x4, [x0, x1, x3, x5, x6]), (x2 ||| x7, x5, [x0, x1, x3, x4, x6]), (x2 ||| x7, x6, [x0, x1, x3, x4, x5]), (x0, x1, [x2 ||| x7, x3, x4, x5, x6]), (x0, x3, [x2 ||| x7, x1, x4, x5, x6]), (x0, x4, [x2 ||| x7, x1, x3, x5, x6]), (x0, x5, [x2 ||| x7, x1, x3, x4, x6]), (x0, x6, [x2 ||| x7, x1, x3, x4, x5]), (x1, x3, [x2 ||| x7, x0, x4, x5, x6]), (x1, x4, [x2 ||| x7, x0, x3, x5, x6]), (x1, x5, [x2 ||| x7, x0, x3, x4, x6]), (x1, x6, [x2 ||| x7, x0, x3, x4, x5]), (x3, x4, [x2 ||| x7, x0, x1, x5, x6]), (x3, x5, [x2 ||| x7, x0, x1, x4, x6]), (x3, x6, [x2 ||| x7, x0, x1, x4, x5]), (x4, x5, [x2 ||| x7, x0, x1, x3, x6]), (x4, x6, [x2 ||| x7, x0, x1, x3, x5]), (x5, x6, [x2 ||| x7, x0, x1, x3, x4])] := by
  decide +kernel

theorem t722 : optimized 8 2 [x2 ||| x7, x0, x1, x3, x4, x5, x6] = false := by
  rw [optimized.eq_2, t722_pairs]
  simp only [List.any_cons, List.any_nil, t701, t702, t703, t704, t705, t706, t707, t708, t709, t710, t711, t712, t713, t714, t715, t716, t717, t718, t719, t720, t721, Bool.or_false]
  all_goals decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t723 : dispatch 1 (optimized 7) (x2 ||| x7) x2 [x0, x1, x3, x4, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t724 : dispatch 1 (optimized 7) (x2 ||| x7) x0 [x2, x1, x3, x4, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t725 : dispatch 1 (optimized 7) (x2 ||| x7) x1 [x2, x0, x3, x4, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t726 : dispatch 1 (optimized 7) (x2 ||| x7) x3 [x2, x0, x1, x4, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t727 : dispatch 1 (optimized 7) (x2 ||| x7) x4 [x2, x0, x1, x3, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t728 : dispatch 1 (optimized 7) (x2 ||| x7) x5 [x2, x0, x1, x3, x4, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t729 : dispatch 1 (optimized 7) (x2 ||| x7) x6 [x2, x0, x1, x3, x4, x5] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t730 : dispatch 1 (optimized 7) x2 x0 [x2 ||| x7, x1, x3, x4, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t731 : dispatch 1 (optimized 7) x2 x1 [x2 ||| x7, x0, x3, x4, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t732 : dispatch 1 (optimized 7) x2 x3 [x2 ||| x7, x0, x1, x4, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t733 : dispatch 1 (optimized 7) x2 x4 [x2 ||| x7, x0, x1, x3, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t734 : dispatch 1 (optimized 7) x2 x5 [x2 ||| x7, x0, x1, x3, x4, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t735 : dispatch 1 (optimized 7) x2 x6 [x2 ||| x7, x0, x1, x3, x4, x5] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t736 : dispatch 1 (optimized 7) x0 x1 [x2 ||| x7, x2, x3, x4, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t737 : dispatch 1 (optimized 7) x0 x3 [x2 ||| x7, x2, x1, x4, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t738 : dispatch 1 (optimized 7) x0 x4 [x2 ||| x7, x2, x1, x3, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t739 : dispatch 1 (optimized 7) x0 x5 [x2 ||| x7, x2, x1, x3, x4, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t740 : dispatch 1 (optimized 7) x0 x6 [x2 ||| x7, x2, x1, x3, x4, x5] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t741 : dispatch 1 (optimized 7) x1 x3 [x2 ||| x7, x2, x0, x4, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t742 : dispatch 1 (optimized 7) x1 x4 [x2 ||| x7, x2, x0, x3, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t743 : dispatch 1 (optimized 7) x1 x5 [x2 ||| x7, x2, x0, x3, x4, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t744 : dispatch 1 (optimized 7) x1 x6 [x2 ||| x7, x2, x0, x3, x4, x5] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t745 : dispatch 1 (optimized 7) x3 x4 [x2 ||| x7, x2, x0, x1, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t746 : dispatch 1 (optimized 7) x3 x5 [x2 ||| x7, x2, x0, x1, x4, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t747 : dispatch 1 (optimized 7) x3 x6 [x2 ||| x7, x2, x0, x1, x4, x5] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t748 : dispatch 1 (optimized 7) x4 x5 [x2 ||| x7, x2, x0, x1, x3, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t749 : dispatch 1 (optimized 7) x4 x6 [x2 ||| x7, x2, x0, x1, x3, x5] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t750 : dispatch 1 (optimized 7) x5 x6 [x2 ||| x7, x2, x0, x1, x3, x4] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
theorem t751_pairs : pairs [x2 ||| x7, x2, x0, x1, x3, x4, x5, x6] = [(x2 ||| x7, x2, [x0, x1, x3, x4, x5, x6]), (x2 ||| x7, x0, [x2, x1, x3, x4, x5, x6]), (x2 ||| x7, x1, [x2, x0, x3, x4, x5, x6]), (x2 ||| x7, x3, [x2, x0, x1, x4, x5, x6]), (x2 ||| x7, x4, [x2, x0, x1, x3, x5, x6]), (x2 ||| x7, x5, [x2, x0, x1, x3, x4, x6]), (x2 ||| x7, x6, [x2, x0, x1, x3, x4, x5]), (x2, x0, [x2 ||| x7, x1, x3, x4, x5, x6]), (x2, x1, [x2 ||| x7, x0, x3, x4, x5, x6]), (x2, x3, [x2 ||| x7, x0, x1, x4, x5, x6]), (x2, x4, [x2 ||| x7, x0, x1, x3, x5, x6]), (x2, x5, [x2 ||| x7, x0, x1, x3, x4, x6]), (x2, x6, [x2 ||| x7, x0, x1, x3, x4, x5]), (x0, x1, [x2 ||| x7, x2, x3, x4, x5, x6]), (x0, x3, [x2 ||| x7, x2, x1, x4, x5, x6]), (x0, x4, [x2 ||| x7, x2, x1, x3, x5, x6]), (x0, x5, [x2 ||| x7, x2, x1, x3, x4, x6]), (x0, x6, [x2 ||| x7, x2, x1, x3, x4, x5]), (x1, x3, [x2 ||| x7, x2, x0, x4, x5, x6]), (x1, x4, [x2 ||| x7, x2, x0, x3, x5, x6]), (x1, x5, [x2 ||| x7, x2, x0, x3, x4, x6]), (x1, x6, [x2 ||| x7, x2, x0, x3, x4, x5]), (x3, x4, [x2 ||| x7, x2, x0, x1, x5, x6]), (x3, x5, [x2 ||| x7, x2, x0, x1, x4, x6]), (x3, x6, [x2 ||| x7, x2, x0, x1, x4, x5]), (x4, x5, [x2 ||| x7, x2, x0, x1, x3, x6]), (x4, x6, [x2 ||| x7, x2, x0, x1, x3, x5]), (x5, x6, [x2 ||| x7, x2, x0, x1, x3, x4])] := by
  decide +kernel

theorem t751 : optimized 8 1 [x2 ||| x7, x2, x0, x1, x3, x4, x5, x6] = false := by
  rw [optimized.eq_2, t751_pairs]
  simp only [List.any_cons, List.any_nil, t723, t724, t725, t726, t727, t728, t729, t730, t731, t732, t733, t734, t735, t736, t737, t738, t739, t740, t741, t742, t743, t744, t745, t746, t747, t748, t749, t750, Bool.or_false]
  all_goals decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t752 : optimized 8 1 [x2 ||| x7, x7, x0, x1, x3, x4, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t753 : optimized 8 0 [x2 ||| x7, x2, x7, x0, x1, x3, x4, x5, x6] = false := by
  decide +kernel

theorem t754 : dispatch 2 (optimized 8) x2 x7 [x0, x1, x3, x4, x5, x6] = false := by
  simp only [dispatch, ops, List.any_cons, List.any_nil, Nat.reduceSub, t700, t722, t751, t752, t753, Bool.and_false, Bool.or_false]
  all_goals decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t755 : dispatch 1 (optimized 7) (x3 &&& x4) x4 [x0, x1, x2, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t756 : dispatch 1 (optimized 7) (x3 &&& x4) x0 [x4, x1, x2, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t757 : dispatch 1 (optimized 7) (x3 &&& x4) x1 [x4, x0, x2, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t758 : dispatch 1 (optimized 7) (x3 &&& x4) x2 [x4, x0, x1, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t759 : dispatch 1 (optimized 7) (x3 &&& x4) x5 [x4, x0, x1, x2, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t760 : dispatch 1 (optimized 7) (x3 &&& x4) x6 [x4, x0, x1, x2, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t761 : dispatch 1 (optimized 7) (x3 &&& x4) x7 [x4, x0, x1, x2, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t762 : dispatch 1 (optimized 7) x4 x0 [x3 &&& x4, x1, x2, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t763 : dispatch 1 (optimized 7) x4 x1 [x3 &&& x4, x0, x2, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t764 : dispatch 1 (optimized 7) x4 x2 [x3 &&& x4, x0, x1, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t765 : dispatch 1 (optimized 7) x4 x5 [x3 &&& x4, x0, x1, x2, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t766 : dispatch 1 (optimized 7) x4 x6 [x3 &&& x4, x0, x1, x2, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t767 : dispatch 1 (optimized 7) x4 x7 [x3 &&& x4, x0, x1, x2, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t768 : dispatch 1 (optimized 7) x0 x1 [x3 &&& x4, x4, x2, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t769 : dispatch 1 (optimized 7) x0 x2 [x3 &&& x4, x4, x1, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t770 : dispatch 1 (optimized 7) x0 x5 [x3 &&& x4, x4, x1, x2, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t771 : dispatch 1 (optimized 6) (x0 ||| x6) (x3 &&& x4) [x4, x1, x2, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t772 : dispatch 1 (optimized 6) (x0 ||| x6) x4 [x3 &&& x4, x1, x2, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t773 : dispatch 1 (optimized 6) (x3 &&& x4) x1 [x0 ||| x6, x4, x2, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t774 : dispatch 1 (optimized 6) (x3 &&& x4) x2 [x0 ||| x6, x4, x1, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t775 : dispatch 1 (optimized 6) (x3 &&& x4) x5 [x0 ||| x6, x4, x1, x2, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t776 : dispatch 1 (optimized 6) (x3 &&& x4) x7 [x0 ||| x6, x4, x1, x2, x5] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t777 : dispatch 1 (optimized 6) x4 x1 [x0 ||| x6, x3 &&& x4, x2, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t778 : dispatch 1 (optimized 6) x4 x2 [x0 ||| x6, x3 &&& x4, x1, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t779 : dispatch 1 (optimized 6) x4 x5 [x0 ||| x6, x3 &&& x4, x1, x2, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t780 : dispatch 1 (optimized 6) x4 x7 [x0 ||| x6, x3 &&& x4, x1, x2, x5] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t781 : dispatch 1 (optimized 6) x1 x2 [x0 ||| x6, x3 &&& x4, x4, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t782 : dispatch 1 (optimized 6) x1 x5 [x0 ||| x6, x3 &&& x4, x4, x2, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t783 : dispatch 1 (optimized 6) x1 x7 [x0 ||| x6, x3 &&& x4, x4, x2, x5] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t784 : dispatch 1 (optimized 6) x2 x5 [x0 ||| x6, x3 &&& x4, x4, x1, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t785 : dispatch 1 (optimized 6) x2 x7 [x0 ||| x6, x3 &&& x4, x4, x1, x5] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t786 : dispatch 1 (optimized 6) x5 x7 [x0 ||| x6, x3 &&& x4, x4, x1, x2] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
theorem t787_pairs : pairs [x0 ||| x6, x3 &&& x4, x4, x1, x2, x5, x7] = [(x0 ||| x6, x3 &&& x4, [x4, x1, x2, x5, x7]), (x0 ||| x6, x4, [x3 &&& x4, x1, x2, x5, x7]), (x0 ||| x6, x1, [x3 &&& x4, x4, x2, x5, x7]), (x0 ||| x6, x2, [x3 &&& x4, x4, x1, x5, x7]), (x0 ||| x6, x5, [x3 &&& x4, x4, x1, x2, x7]), (x0 ||| x6, x7, [x3 &&& x4, x4, x1, x2, x5]), (x3 &&& x4, x4, [x0 ||| x6, x1, x2, x5, x7]), (x3 &&& x4, x1, [x0 ||| x6, x4, x2, x5, x7]), (x3 &&& x4, x2, [x0 ||| x6, x4, x1, x5, x7]), (x3 &&& x4, x5, [x0 ||| x6, x4, x1, x2, x7]), (x3 &&& x4, x7, [x0 ||| x6, x4, x1, x2, x5]), (x4, x1, [x0 ||| x6, x3 &&& x4, x2, x5, x7]), (x4, x2, [x0 ||| x6, x3 &&& x4, x1, x5, x7]), (x4, x5, [x0 ||| x6, x3 &&& x4, x1, x2, x7]), (x4, x7, [x0 ||| x6, x3 &&& x4, x1, x2, x5]), (x1, x2, [x0 ||| x6, x3 &&& x4, x4, x5, x7]), (x1, x5, [x0 ||| x6, x3 &&& x4, x4, x2, x7]), (x1, x7, [x0 ||| x6, x3 &&& x4, x4, x2, x5]), (x2, x5, [x0 ||| x6, x3 &&& x4, x4, x1, x7]), (x2, x7, [x0 ||| x6, x3 &&& x4, x4, x1, x5]), (x5, x7, [x0 ||| x6, x3 &&& x4, x4, x1, x2])] := by
  decide +kernel

theorem t787 : optimized 7 1 [x0 ||| x6, x3 &&& x4, x4, x1, x2, x5, x7] = false := by
  rw [optimized.eq_2, t787_pairs]
  simp only [List.any_cons, List.any_nil, t771, t772, t176, t177, t178, t179, t165, t773, t774, t775, t776, t777, t778, t779, t780, t781, t782, t783, t784, t785, t786, Bool.or_false]
  all_goals decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t788 : optimized 7 0 [x0 ||| x6, x0, x3 &&& x4, x4, x1, x2, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t789 : optimized 7 0 [x0 ||| x6, x6, x3 &&& x4, x4, x1, x2, x5, x7] = false := by
  decide +kernel

theorem t790 : dispatch 1 (optimized 7) x0 x6 [x3 &&& x4, x4, x1, x2, x5, x7] = false := by
  simp only [dispatch, ops, List.any_cons, List.any_nil, Nat.reduceSub, t787, t788, t789, Bool.and_false, Bool.or_false]
  all_goals decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t791 : dispatch 1 (optimized 7) x0 x7 [x3 &&& x4, x4, x1, x2, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t792 : dispatch 1 (optimized 7) x1 x2 [x3 &&& x4, x4, x0, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t793 : dispatch 1 (optimized 7) x1 x5 [x3 &&& x4, x4, x0, x2, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t794 : dispatch 1 (optimized 7) x1 x6 [x3 &&& x4, x4, x0, x2, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t795 : dispatch 1 (optimized 7) x1 x7 [x3 &&& x4, x4, x0, x2, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t796 : dispatch 1 (optimized 7) x2 x5 [x3 &&& x4, x4, x0, x1, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t797 : dispatch 1 (optimized 7) x2 x6 [x3 &&& x4, x4, x0, x1, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t798 : dispatch 1 (optimized 7) x2 x7 [x3 &&& x4, x4, x0, x1, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t799 : dispatch 1 (optimized 7) x5 x6 [x3 &&& x4, x4, x0, x1, x2, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t800 : dispatch 1 (optimized 7) x5 x7 [x3 &&& x4, x4, x0, x1, x2, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t801 : dispatch 1 (optimized 7) x6 x7 [x3 &&& x4, x4, x0, x1, x2, x5] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
theorem t802_pairs : pairs [x3 &&& x4, x4, x0, x1, x2, x5, x6, x7] = [(x3 &&& x4, x4, [x0, x1, x2, x5, x6, x7]), (x3 &&& x4, x0, [x4, x1, x2, x5, x6, x7]), (x3 &&& x4, x1, [x4, x0, x2, x5, x6, x7]), (x3 &&& x4, x2, [x4, x0, x1, x5, x6, x7]), (x3 &&& x4, x5, [x4, x0, x1, x2, x6, x7]), (x3 &&& x4, x6, [x4, x0, x1, x2, x5, x7]), (x3 &&& x4, x7, [x4, x0, x1, x2, x5, x6]), (x4, x0, [x3 &&& x4, x1, x2, x5, x6, x7]), (x4, x1, [x3 &&& x4, x0, x2, x5, x6, x7]), (x4, x2, [x3 &&& x4, x0, x1, x5, x6, x7]), (x4, x5, [x3 &&& x4, x0, x1, x2, x6, x7]), (x4, x6, [x3 &&& x4, x0, x1, x2, x5, x7]), (x4, x7, [x3 &&& x4, x0, x1, x2, x5, x6]), (x0, x1, [x3 &&& x4, x4, x2, x5, x6, x7]), (x0, x2, [x3 &&& x4, x4, x1, x5, x6, x7]), (x0, x5, [x3 &&& x4, x4, x1, x2, x6, x7]), (x0, x6, [x3 &&& x4, x4, x1, x2, x5, x7]), (x0, x7, [x3 &&& x4, x4, x1, x2, x5, x6]), (x1, x2, [x3 &&& x4, x4, x0, x5, x6, x7]), (x1, x5, [x3 &&& x4, x4, x0, x2, x6, x7]), (x1, x6, [x3 &&& x4, x4, x0, x2, x5, x7]), (x1, x7, [x3 &&& x4, x4, x0, x2, x5, x6]), (x2, x5, [x3 &&& x4, x4, x0, x1, x6, x7]), (x2, x6, [x3 &&& x4, x4, x0, x1, x5, x7]), (x2, x7, [x3 &&& x4, x4, x0, x1, x5, x6]), (x5, x6, [x3 &&& x4, x4, x0, x1, x2, x7]), (x5, x7, [x3 &&& x4, x4, x0, x1, x2, x6]), (x6, x7, [x3 &&& x4, x4, x0, x1, x2, x5])] := by
  decide +kernel

theorem t802 : optimized 8 1 [x3 &&& x4, x4, x0, x1, x2, x5, x6, x7] = false := by
  rw [optimized.eq_2, t802_pairs]
  simp only [List.any_cons, List.any_nil, t755, t756, t757, t758, t759, t760, t761, t762, t763, t764, t765, t766, t767, t768, t769, t770, t790, t791, t792, t793, t794, t795, t796, t797, t798, t799, t800, t801, Bool.or_false]
  all_goals decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t803 : optimized 8 0 [x3 &&& x4, x3, x4, x0, x1, x2, x5, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t804 : optimized 8 0 [x3 ||| x4, x3, x4, x0, x1, x2, x5, x6, x7] = false := by
  decide +kernel

theorem t805 : dispatch 2 (optimized 8) x3 x4 [x0, x1, x2, x5, x6, x7] = false := by
  simp only [dispatch, ops, List.any_cons, List.any_nil, Nat.reduceSub, t802, t803, t804, Bool.and_false, Bool.or_false]
  all_goals decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t806 : optimized 8 0 [x3 &&& x5, x3, x5, x0, x1, x2, x4, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t807 : dispatch 2 (optimized 7) (x3 ||| x5) x0 [x1, x2, x4, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t808 : dispatch 2 (optimized 7) (x3 ||| x5) x1 [x0, x2, x4, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t809 : dispatch 2 (optimized 7) (x3 ||| x5) x2 [x0, x1, x4, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t810 : dispatch 2 (optimized 7) (x3 ||| x5) x4 [x0, x1, x2, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t811 : dispatch 2 (optimized 7) (x3 ||| x5) x6 [x0, x1, x2, x4, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t812 : dispatch 2 (optimized 7) (x3 ||| x5) x7 [x0, x1, x2, x4, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t813 : dispatch 2 (optimized 7) x0 x1 [x3 ||| x5, x2, x4, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t814 : dispatch 2 (optimized 7) x0 x2 [x3 ||| x5, x1, x4, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t815 : dispatch 2 (optimized 7) x0 x4 [x3 ||| x5, x1, x2, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t816 : dispatch 2 (optimized 7) x0 x6 [x3 ||| x5, x1, x2, x4, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t817 : dispatch 2 (optimized 7) x0 x7 [x3 ||| x5, x1, x2, x4, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t818 : dispatch 2 (optimized 7) x1 x2 [x3 ||| x5, x0, x4, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t819 : dispatch 2 (optimized 7) x1 x4 [x3 ||| x5, x0, x2, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t820 : dispatch 2 (optimized 7) x1 x6 [x3 ||| x5, x0, x2, x4, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t821 : dispatch 2 (optimized 7) x1 x7 [x3 ||| x5, x0, x2, x4, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t822 : dispatch 2 (optimized 7) x2 x4 [x3 ||| x5, x0, x1, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t823 : dispatch 2 (optimized 7) x2 x6 [x3 ||| x5, x0, x1, x4, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t824 : dispatch 2 (optimized 7) x2 x7 [x3 ||| x5, x0, x1, x4, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t825 : dispatch 2 (optimized 7) x4 x6 [x3 ||| x5, x0, x1, x2, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t826 : dispatch 2 (optimized 7) x4 x7 [x3 ||| x5, x0, x1, x2, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t827 : dispatch 2 (optimized 7) x6 x7 [x3 ||| x5, x0, x1, x2, x4] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
theorem t828_pairs : pairs [x3 ||| x5, x0, x1, x2, x4, x6, x7] = [(x3 ||| x5, x0, [x1, x2, x4, x6, x7]), (x3 ||| x5, x1, [x0, x2, x4, x6, x7]), (x3 ||| x5, x2, [x0, x1, x4, x6, x7]), (x3 ||| x5, x4, [x0, x1, x2, x6, x7]), (x3 ||| x5, x6, [x0, x1, x2, x4, x7]), (x3 ||| x5, x7, [x0, x1, x2, x4, x6]), (x0, x1, [x3 ||| x5, x2, x4, x6, x7]), (x0, x2, [x3 ||| x5, x1, x4, x6, x7]), (x0, x4, [x3 ||| x5, x1, x2, x6, x7]), (x0, x6, [x3 ||| x5, x1, x2, x4, x7]), (x0, x7, [x3 ||| x5, x1, x2, x4, x6]), (x1, x2, [x3 ||| x5, x0, x4, x6, x7]), (x1, x4, [x3 ||| x5, x0, x2, x6, x7]), (x1, x6, [x3 ||| x5, x0, x2, x4, x7]), (x1, x7, [x3 ||| x5, x0, x2, x4, x6]), (x2, x4, [x3 ||| x5, x0, x1, x6, x7]), (x2, x6, [x3 ||| x5, x0, x1, x4, x7]), (x2, x7, [x3 ||| x5, x0, x1, x4, x6]), (x4, x6, [x3 ||| x5, x0, x1, x2, x7]), (x4, x7, [x3 ||| x5, x0, x1, x2, x6]), (x6, x7, [x3 ||| x5, x0, x1, x2, x4])] := by
  decide +kernel

theorem t828 : optimized 8 2 [x3 ||| x5, x0, x1, x2, x4, x6, x7] = false := by
  rw [optimized.eq_2, t828_pairs]
  simp only [List.any_cons, List.any_nil, t807, t808, t809, t810, t811, t812, t813, t814, t815, t816, t817, t818, t819, t820, t821, t822, t823, t824, t825, t826, t827, Bool.or_false]
  all_goals decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t829 : optimized 8 1 [x3 ||| x5, x3, x0, x1, x2, x4, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t830 : dispatch 1 (optimized 7) (x3 ||| x5) x5 [x0, x1, x2, x4, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t831 : dispatch 1 (optimized 7) (x3 ||| x5) x0 [x5, x1, x2, x4, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t832 : dispatch 1 (optimized 7) (x3 ||| x5) x1 [x5, x0, x2, x4, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t833 : dispatch 1 (optimized 7) (x3 ||| x5) x2 [x5, x0, x1, x4, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t834 : dispatch 1 (optimized 7) (x3 ||| x5) x4 [x5, x0, x1, x2, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t835 : dispatch 1 (optimized 7) (x3 ||| x5) x6 [x5, x0, x1, x2, x4, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t836 : dispatch 1 (optimized 7) (x3 ||| x5) x7 [x5, x0, x1, x2, x4, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t837 : dispatch 1 (optimized 7) x5 x0 [x3 ||| x5, x1, x2, x4, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t838 : dispatch 1 (optimized 7) x5 x1 [x3 ||| x5, x0, x2, x4, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t839 : dispatch 1 (optimized 7) x5 x2 [x3 ||| x5, x0, x1, x4, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t840 : dispatch 1 (optimized 7) x5 x4 [x3 ||| x5, x0, x1, x2, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t841 : dispatch 1 (optimized 7) x5 x6 [x3 ||| x5, x0, x1, x2, x4, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t842 : dispatch 1 (optimized 7) x5 x7 [x3 ||| x5, x0, x1, x2, x4, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t843 : dispatch 1 (optimized 7) x0 x1 [x3 ||| x5, x5, x2, x4, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t844 : dispatch 1 (optimized 7) x0 x2 [x3 ||| x5, x5, x1, x4, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t845 : dispatch 1 (optimized 7) x0 x4 [x3 ||| x5, x5, x1, x2, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t846 : dispatch 1 (optimized 7) x0 x6 [x3 ||| x5, x5, x1, x2, x4, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t847 : dispatch 1 (optimized 7) x0 x7 [x3 ||| x5, x5, x1, x2, x4, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t848 : dispatch 1 (optimized 7) x1 x2 [x3 ||| x5, x5, x0, x4, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t849 : dispatch 1 (optimized 7) x1 x4 [x3 ||| x5, x5, x0, x2, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t850 : dispatch 1 (optimized 7) x1 x6 [x3 ||| x5, x5, x0, x2, x4, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t851 : dispatch 1 (optimized 7) x1 x7 [x3 ||| x5, x5, x0, x2, x4, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t852 : dispatch 1 (optimized 7) x2 x4 [x3 ||| x5, x5, x0, x1, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t853 : dispatch 1 (optimized 7) x2 x6 [x3 ||| x5, x5, x0, x1, x4, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t854 : dispatch 1 (optimized 7) x2 x7 [x3 ||| x5, x5, x0, x1, x4, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t855 : dispatch 1 (optimized 7) x4 x6 [x3 ||| x5, x5, x0, x1, x2, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t856 : dispatch 1 (optimized 7) x4 x7 [x3 ||| x5, x5, x0, x1, x2, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t857 : dispatch 1 (optimized 7) x6 x7 [x3 ||| x5, x5, x0, x1, x2, x4] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
theorem t858_pairs : pairs [x3 ||| x5, x5, x0, x1, x2, x4, x6, x7] = [(x3 ||| x5, x5, [x0, x1, x2, x4, x6, x7]), (x3 ||| x5, x0, [x5, x1, x2, x4, x6, x7]), (x3 ||| x5, x1, [x5, x0, x2, x4, x6, x7]), (x3 ||| x5, x2, [x5, x0, x1, x4, x6, x7]), (x3 ||| x5, x4, [x5, x0, x1, x2, x6, x7]), (x3 ||| x5, x6, [x5, x0, x1, x2, x4, x7]), (x3 ||| x5, x7, [x5, x0, x1, x2, x4, x6]), (x5, x0, [x3 ||| x5, x1, x2, x4, x6, x7]), (x5, x1, [x3 ||| x5, x0, x2, x4, x6, x7]), (x5, x2, [x3 ||| x5, x0, x1, x4, x6, x7]), (x5, x4, [x3 ||| x5, x0, x1, x2, x6, x7]), (x5, x6, [x3 ||| x5, x0, x1, x2, x4, x7]), (x5, x7, [x3 ||| x5, x0, x1, x2, x4, x6]), (x0, x1, [x3 ||| x5, x5, x2, x4, x6, x7]), (x0, x2, [x3 ||| x5, x5, x1, x4, x6, x7]), (x0, x4, [x3 ||| x5, x5, x1, x2, x6, x7]), (x0, x6, [x3 ||| x5, x5, x1, x2, x4, x7]), (x0, x7, [x3 ||| x5, x5, x1, x2, x4, x6]), (x1, x2, [x3 ||| x5, x5, x0, x4, x6, x7]), (x1, x4, [x3 ||| x5, x5, x0, x2, x6, x7]), (x1, x6, [x3 ||| x5, x5, x0, x2, x4, x7]), (x1, x7, [x3 ||| x5, x5, x0, x2, x4, x6]), (x2, x4, [x3 ||| x5, x5, x0, x1, x6, x7]), (x2, x6, [x3 ||| x5, x5, x0, x1, x4, x7]), (x2, x7, [x3 ||| x5, x5, x0, x1, x4, x6]), (x4, x6, [x3 ||| x5, x5, x0, x1, x2, x7]), (x4, x7, [x3 ||| x5, x5, x0, x1, x2, x6]), (x6, x7, [x3 ||| x5, x5, x0, x1, x2, x4])] := by
  decide +kernel

theorem t858 : optimized 8 1 [x3 ||| x5, x5, x0, x1, x2, x4, x6, x7] = false := by
  rw [optimized.eq_2, t858_pairs]
  simp only [List.any_cons, List.any_nil, t830, t831, t832, t833, t834, t835, t836, t837, t838, t839, t840, t841, t842, t843, t844, t845, t846, t847, t848, t849, t850, t851, t852, t853, t854, t855, t856, t857, Bool.or_false]
  all_goals decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t859 : optimized 8 0 [x3 ||| x5, x3, x5, x0, x1, x2, x4, x6, x7] = false := by
  decide +kernel

theorem t860 : dispatch 2 (optimized 8) x3 x5 [x0, x1, x2, x4, x6, x7] = false := by
  simp only [dispatch, ops, List.any_cons, List.any_nil, Nat.reduceSub, t806, t828, t829, t858, t859, Bool.and_false, Bool.or_false]
  all_goals decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t861 : optimized 8 0 [x3 &&& x6, x3, x6, x0, x1, x2, x4, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t862 : dispatch 2 (optimized 7) (x3 ||| x6) x0 [x1, x2, x4, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t863 : dispatch 2 (optimized 7) (x3 ||| x6) x1 [x0, x2, x4, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t864 : dispatch 2 (optimized 7) (x3 ||| x6) x2 [x0, x1, x4, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t865 : dispatch 2 (optimized 7) (x3 ||| x6) x4 [x0, x1, x2, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t866 : dispatch 2 (optimized 7) (x3 ||| x6) x5 [x0, x1, x2, x4, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t867 : dispatch 2 (optimized 7) (x3 ||| x6) x7 [x0, x1, x2, x4, x5] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t868 : dispatch 2 (optimized 7) x0 x1 [x3 ||| x6, x2, x4, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t869 : dispatch 2 (optimized 7) x0 x2 [x3 ||| x6, x1, x4, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t870 : dispatch 2 (optimized 7) x0 x4 [x3 ||| x6, x1, x2, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t871 : dispatch 2 (optimized 7) x0 x5 [x3 ||| x6, x1, x2, x4, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t872 : dispatch 2 (optimized 7) x0 x7 [x3 ||| x6, x1, x2, x4, x5] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t873 : dispatch 2 (optimized 7) x1 x2 [x3 ||| x6, x0, x4, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t874 : dispatch 2 (optimized 7) x1 x4 [x3 ||| x6, x0, x2, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t875 : dispatch 2 (optimized 7) x1 x5 [x3 ||| x6, x0, x2, x4, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t876 : dispatch 2 (optimized 7) x1 x7 [x3 ||| x6, x0, x2, x4, x5] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t877 : dispatch 2 (optimized 7) x2 x4 [x3 ||| x6, x0, x1, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t878 : dispatch 2 (optimized 7) x2 x5 [x3 ||| x6, x0, x1, x4, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t879 : dispatch 2 (optimized 7) x2 x7 [x3 ||| x6, x0, x1, x4, x5] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t880 : dispatch 2 (optimized 7) x4 x5 [x3 ||| x6, x0, x1, x2, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t881 : dispatch 2 (optimized 7) x4 x7 [x3 ||| x6, x0, x1, x2, x5] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t882 : dispatch 2 (optimized 7) x5 x7 [x3 ||| x6, x0, x1, x2, x4] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
theorem t883_pairs : pairs [x3 ||| x6, x0, x1, x2, x4, x5, x7] = [(x3 ||| x6, x0, [x1, x2, x4, x5, x7]), (x3 ||| x6, x1, [x0, x2, x4, x5, x7]), (x3 ||| x6, x2, [x0, x1, x4, x5, x7]), (x3 ||| x6, x4, [x0, x1, x2, x5, x7]), (x3 ||| x6, x5, [x0, x1, x2, x4, x7]), (x3 ||| x6, x7, [x0, x1, x2, x4, x5]), (x0, x1, [x3 ||| x6, x2, x4, x5, x7]), (x0, x2, [x3 ||| x6, x1, x4, x5, x7]), (x0, x4, [x3 ||| x6, x1, x2, x5, x7]), (x0, x5, [x3 ||| x6, x1, x2, x4, x7]), (x0, x7, [x3 ||| x6, x1, x2, x4, x5]), (x1, x2, [x3 ||| x6, x0, x4, x5, x7]), (x1, x4, [x3 ||| x6, x0, x2, x5, x7]), (x1, x5, [x3 ||| x6, x0, x2, x4, x7]), (x1, x7, [x3 ||| x6, x0, x2, x4, x5]), (x2, x4, [x3 ||| x6, x0, x1, x5, x7]), (x2, x5, [x3 ||| x6, x0, x1, x4, x7]), (x2, x7, [x3 ||| x6, x0, x1, x4, x5]), (x4, x5, [x3 ||| x6, x0, x1, x2, x7]), (x4, x7, [x3 ||| x6, x0, x1, x2, x5]), (x5, x7, [x3 ||| x6, x0, x1, x2, x4])] := by
  decide +kernel

theorem t883 : optimized 8 2 [x3 ||| x6, x0, x1, x2, x4, x5, x7] = false := by
  rw [optimized.eq_2, t883_pairs]
  simp only [List.any_cons, List.any_nil, t862, t863, t864, t865, t866, t867, t868, t869, t870, t871, t872, t873, t874, t875, t876, t877, t878, t879, t880, t881, t882, Bool.or_false]
  all_goals decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t884 : optimized 8 1 [x3 ||| x6, x3, x0, x1, x2, x4, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t885 : dispatch 1 (optimized 7) (x3 ||| x6) x6 [x0, x1, x2, x4, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t886 : dispatch 1 (optimized 7) (x3 ||| x6) x0 [x6, x1, x2, x4, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t887 : dispatch 1 (optimized 7) (x3 ||| x6) x1 [x6, x0, x2, x4, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t888 : dispatch 1 (optimized 7) (x3 ||| x6) x2 [x6, x0, x1, x4, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t889 : dispatch 1 (optimized 7) (x3 ||| x6) x4 [x6, x0, x1, x2, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t890 : dispatch 1 (optimized 7) (x3 ||| x6) x5 [x6, x0, x1, x2, x4, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t891 : dispatch 1 (optimized 7) (x3 ||| x6) x7 [x6, x0, x1, x2, x4, x5] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t892 : dispatch 1 (optimized 7) x6 x0 [x3 ||| x6, x1, x2, x4, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t893 : dispatch 1 (optimized 7) x6 x1 [x3 ||| x6, x0, x2, x4, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t894 : dispatch 1 (optimized 7) x6 x2 [x3 ||| x6, x0, x1, x4, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t895 : dispatch 1 (optimized 7) x6 x4 [x3 ||| x6, x0, x1, x2, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t896 : dispatch 1 (optimized 7) x6 x5 [x3 ||| x6, x0, x1, x2, x4, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t897 : dispatch 1 (optimized 7) x6 x7 [x3 ||| x6, x0, x1, x2, x4, x5] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t898 : dispatch 1 (optimized 7) x0 x1 [x3 ||| x6, x6, x2, x4, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t899 : dispatch 1 (optimized 7) x0 x2 [x3 ||| x6, x6, x1, x4, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t900 : dispatch 1 (optimized 7) x0 x4 [x3 ||| x6, x6, x1, x2, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t901 : dispatch 1 (optimized 7) x0 x5 [x3 ||| x6, x6, x1, x2, x4, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t902 : dispatch 1 (optimized 7) x0 x7 [x3 ||| x6, x6, x1, x2, x4, x5] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t903 : dispatch 1 (optimized 7) x1 x2 [x3 ||| x6, x6, x0, x4, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t904 : dispatch 1 (optimized 7) x1 x4 [x3 ||| x6, x6, x0, x2, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t905 : dispatch 1 (optimized 7) x1 x5 [x3 ||| x6, x6, x0, x2, x4, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t906 : dispatch 1 (optimized 7) x1 x7 [x3 ||| x6, x6, x0, x2, x4, x5] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t907 : dispatch 1 (optimized 7) x2 x4 [x3 ||| x6, x6, x0, x1, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t908 : dispatch 1 (optimized 7) x2 x5 [x3 ||| x6, x6, x0, x1, x4, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t909 : dispatch 1 (optimized 7) x2 x7 [x3 ||| x6, x6, x0, x1, x4, x5] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t910 : dispatch 1 (optimized 7) x4 x5 [x3 ||| x6, x6, x0, x1, x2, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t911 : dispatch 1 (optimized 7) x4 x7 [x3 ||| x6, x6, x0, x1, x2, x5] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t912 : dispatch 1 (optimized 7) x5 x7 [x3 ||| x6, x6, x0, x1, x2, x4] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
theorem t913_pairs : pairs [x3 ||| x6, x6, x0, x1, x2, x4, x5, x7] = [(x3 ||| x6, x6, [x0, x1, x2, x4, x5, x7]), (x3 ||| x6, x0, [x6, x1, x2, x4, x5, x7]), (x3 ||| x6, x1, [x6, x0, x2, x4, x5, x7]), (x3 ||| x6, x2, [x6, x0, x1, x4, x5, x7]), (x3 ||| x6, x4, [x6, x0, x1, x2, x5, x7]), (x3 ||| x6, x5, [x6, x0, x1, x2, x4, x7]), (x3 ||| x6, x7, [x6, x0, x1, x2, x4, x5]), (x6, x0, [x3 ||| x6, x1, x2, x4, x5, x7]), (x6, x1, [x3 ||| x6, x0, x2, x4, x5, x7]), (x6, x2, [x3 ||| x6, x0, x1, x4, x5, x7]), (x6, x4, [x3 ||| x6, x0, x1, x2, x5, x7]), (x6, x5, [x3 ||| x6, x0, x1, x2, x4, x7]), (x6, x7, [x3 ||| x6, x0, x1, x2, x4, x5]), (x0, x1, [x3 ||| x6, x6, x2, x4, x5, x7]), (x0, x2, [x3 ||| x6, x6, x1, x4, x5, x7]), (x0, x4, [x3 ||| x6, x6, x1, x2, x5, x7]), (x0, x5, [x3 ||| x6, x6, x1, x2, x4, x7]), (x0, x7, [x3 ||| x6, x6, x1, x2, x4, x5]), (x1, x2, [x3 ||| x6, x6, x0, x4, x5, x7]), (x1, x4, [x3 ||| x6, x6, x0, x2, x5, x7]), (x1, x5, [x3 ||| x6, x6, x0, x2, x4, x7]), (x1, x7, [x3 ||| x6, x6, x0, x2, x4, x5]), (x2, x4, [x3 ||| x6, x6, x0, x1, x5, x7]), (x2, x5, [x3 ||| x6, x6, x0, x1, x4, x7]), (x2, x7, [x3 ||| x6, x6, x0, x1, x4, x5]), (x4, x5, [x3 ||| x6, x6, x0, x1, x2, x7]), (x4, x7, [x3 ||| x6, x6, x0, x1, x2, x5]), (x5, x7, [x3 ||| x6, x6, x0, x1, x2, x4])] := by
  decide +kernel

theorem t913 : optimized 8 1 [x3 ||| x6, x6, x0, x1, x2, x4, x5, x7] = false := by
  rw [optimized.eq_2, t913_pairs]
  simp only [List.any_cons, List.any_nil, t885, t886, t887, t888, t889, t890, t891, t892, t893, t894, t895, t896, t897, t898, t899, t900, t901, t902, t903, t904, t905, t906, t907, t908, t909, t910, t911, t912, Bool.or_false]
  all_goals decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t914 : optimized 8 0 [x3 ||| x6, x3, x6, x0, x1, x2, x4, x5, x7] = false := by
  decide +kernel

theorem t915 : dispatch 2 (optimized 8) x3 x6 [x0, x1, x2, x4, x5, x7] = false := by
  simp only [dispatch, ops, List.any_cons, List.any_nil, Nat.reduceSub, t861, t883, t884, t913, t914, Bool.and_false, Bool.or_false]
  all_goals decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t916 : optimized 8 0 [x3 &&& x7, x3, x7, x0, x1, x2, x4, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t917 : optimized 8 2 [x3 ||| x7, x0, x1, x2, x4, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t918 : optimized 8 1 [x3 ||| x7, x3, x0, x1, x2, x4, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t919 : optimized 8 1 [x3 ||| x7, x7, x0, x1, x2, x4, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t920 : optimized 8 0 [x3 ||| x7, x3, x7, x0, x1, x2, x4, x5, x6] = false := by
  decide +kernel

theorem t921 : dispatch 2 (optimized 8) x3 x7 [x0, x1, x2, x4, x5, x6] = false := by
  simp only [dispatch, ops, List.any_cons, List.any_nil, Nat.reduceSub, t916, t917, t918, t919, t920, Bool.and_false, Bool.or_false]
  all_goals decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t922 : optimized 8 0 [x4 &&& x5, x4, x5, x0, x1, x2, x3, x6, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t923 : optimized 8 0 [x4 ||| x5, x4, x5, x0, x1, x2, x3, x6, x7] = false := by
  decide +kernel

theorem t924 : dispatch 2 (optimized 8) x4 x5 [x0, x1, x2, x3, x6, x7] = false := by
  simp only [dispatch, ops, List.any_cons, List.any_nil, Nat.reduceSub, t922, t923, Bool.and_false, Bool.or_false]
  all_goals decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t925 : dispatch 2 (optimized 8) x4 x6 [x0, x1, x2, x3, x5, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t926 : optimized 8 0 [x4 &&& x7, x4, x7, x0, x1, x2, x3, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t927 : dispatch 1 (optimized 7) (x4 ||| x7) x4 [x0, x1, x2, x3, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t928 : dispatch 1 (optimized 7) (x4 ||| x7) x0 [x4, x1, x2, x3, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t929 : dispatch 1 (optimized 7) (x4 ||| x7) x1 [x4, x0, x2, x3, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t930 : dispatch 1 (optimized 7) (x4 ||| x7) x2 [x4, x0, x1, x3, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t931 : dispatch 1 (optimized 7) (x4 ||| x7) x3 [x4, x0, x1, x2, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t932 : dispatch 1 (optimized 7) (x4 ||| x7) x5 [x4, x0, x1, x2, x3, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t933 : dispatch 1 (optimized 7) (x4 ||| x7) x6 [x4, x0, x1, x2, x3, x5] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t934 : dispatch 1 (optimized 7) x4 x0 [x4 ||| x7, x1, x2, x3, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t935 : dispatch 1 (optimized 7) x4 x1 [x4 ||| x7, x0, x2, x3, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t936 : dispatch 1 (optimized 7) x4 x2 [x4 ||| x7, x0, x1, x3, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t937 : dispatch 1 (optimized 7) x4 x3 [x4 ||| x7, x0, x1, x2, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t938 : dispatch 1 (optimized 7) x4 x5 [x4 ||| x7, x0, x1, x2, x3, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t939 : dispatch 1 (optimized 7) x4 x6 [x4 ||| x7, x0, x1, x2, x3, x5] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t940 : dispatch 1 (optimized 7) x0 x1 [x4 ||| x7, x4, x2, x3, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t941 : dispatch 1 (optimized 7) x0 x2 [x4 ||| x7, x4, x1, x3, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t942 : dispatch 1 (optimized 7) x0 x3 [x4 ||| x7, x4, x1, x2, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t943 : dispatch 1 (optimized 7) x0 x5 [x4 ||| x7, x4, x1, x2, x3, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t944 : dispatch 1 (optimized 7) x0 x6 [x4 ||| x7, x4, x1, x2, x3, x5] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t945 : dispatch 1 (optimized 7) x1 x2 [x4 ||| x7, x4, x0, x3, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t946 : dispatch 1 (optimized 7) x1 x3 [x4 ||| x7, x4, x0, x2, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t947 : dispatch 1 (optimized 7) x1 x5 [x4 ||| x7, x4, x0, x2, x3, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t948 : dispatch 1 (optimized 7) x1 x6 [x4 ||| x7, x4, x0, x2, x3, x5] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t949 : dispatch 1 (optimized 7) x2 x3 [x4 ||| x7, x4, x0, x1, x5, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t950 : dispatch 1 (optimized 7) x2 x5 [x4 ||| x7, x4, x0, x1, x3, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t951 : dispatch 1 (optimized 7) x2 x6 [x4 ||| x7, x4, x0, x1, x3, x5] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t952 : dispatch 1 (optimized 7) x3 x5 [x4 ||| x7, x4, x0, x1, x2, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t953 : dispatch 1 (optimized 7) x3 x6 [x4 ||| x7, x4, x0, x1, x2, x5] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t954 : dispatch 1 (optimized 7) x5 x6 [x4 ||| x7, x4, x0, x1, x2, x3] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
theorem t955_pairs : pairs [x4 ||| x7, x4, x0, x1, x2, x3, x5, x6] = [(x4 ||| x7, x4, [x0, x1, x2, x3, x5, x6]), (x4 ||| x7, x0, [x4, x1, x2, x3, x5, x6]), (x4 ||| x7, x1, [x4, x0, x2, x3, x5, x6]), (x4 ||| x7, x2, [x4, x0, x1, x3, x5, x6]), (x4 ||| x7, x3, [x4, x0, x1, x2, x5, x6]), (x4 ||| x7, x5, [x4, x0, x1, x2, x3, x6]), (x4 ||| x7, x6, [x4, x0, x1, x2, x3, x5]), (x4, x0, [x4 ||| x7, x1, x2, x3, x5, x6]), (x4, x1, [x4 ||| x7, x0, x2, x3, x5, x6]), (x4, x2, [x4 ||| x7, x0, x1, x3, x5, x6]), (x4, x3, [x4 ||| x7, x0, x1, x2, x5, x6]), (x4, x5, [x4 ||| x7, x0, x1, x2, x3, x6]), (x4, x6, [x4 ||| x7, x0, x1, x2, x3, x5]), (x0, x1, [x4 ||| x7, x4, x2, x3, x5, x6]), (x0, x2, [x4 ||| x7, x4, x1, x3, x5, x6]), (x0, x3, [x4 ||| x7, x4, x1, x2, x5, x6]), (x0, x5, [x4 ||| x7, x4, x1, x2, x3, x6]), (x0, x6, [x4 ||| x7, x4, x1, x2, x3, x5]), (x1, x2, [x4 ||| x7, x4, x0, x3, x5, x6]), (x1, x3, [x4 ||| x7, x4, x0, x2, x5, x6]), (x1, x5, [x4 ||| x7, x4, x0, x2, x3, x6]), (x1, x6, [x4 ||| x7, x4, x0, x2, x3, x5]), (x2, x3, [x4 ||| x7, x4, x0, x1, x5, x6]), (x2, x5, [x4 ||| x7, x4, x0, x1, x3, x6]), (x2, x6, [x4 ||| x7, x4, x0, x1, x3, x5]), (x3, x5, [x4 ||| x7, x4, x0, x1, x2, x6]), (x3, x6, [x4 ||| x7, x4, x0, x1, x2, x5]), (x5, x6, [x4 ||| x7, x4, x0, x1, x2, x3])] := by
  decide +kernel

theorem t955 : optimized 8 1 [x4 ||| x7, x4, x0, x1, x2, x3, x5, x6] = false := by
  rw [optimized.eq_2, t955_pairs]
  simp only [List.any_cons, List.any_nil, t927, t928, t929, t930, t931, t932, t933, t934, t935, t936, t937, t938, t939, t940, t941, t942, t943, t944, t945, t946, t947, t948, t949, t950, t951, t952, t953, t954, Bool.or_false]
  all_goals decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t956 : optimized 8 0 [x4 ||| x7, x4, x7, x0, x1, x2, x3, x5, x6] = false := by
  decide +kernel

theorem t957 : dispatch 2 (optimized 8) x4 x7 [x0, x1, x2, x3, x5, x6] = false := by
  simp only [dispatch, ops, List.any_cons, List.any_nil, Nat.reduceSub, t926, t955, t956, Bool.and_false, Bool.or_false]
  all_goals decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t958 : optimized 8 0 [x5 &&& x6, x5, x6, x0, x1, x2, x3, x4, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t959 : dispatch 1 (optimized 7) (x5 ||| x6) x5 [x0, x1, x2, x3, x4, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t960 : dispatch 1 (optimized 7) (x5 ||| x6) x0 [x5, x1, x2, x3, x4, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t961 : dispatch 1 (optimized 7) (x5 ||| x6) x1 [x5, x0, x2, x3, x4, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t962 : dispatch 1 (optimized 7) (x5 ||| x6) x2 [x5, x0, x1, x3, x4, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t963 : dispatch 1 (optimized 7) (x5 ||| x6) x3 [x5, x0, x1, x2, x4, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t964 : dispatch 1 (optimized 7) (x5 ||| x6) x4 [x5, x0, x1, x2, x3, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t965 : dispatch 1 (optimized 7) (x5 ||| x6) x7 [x5, x0, x1, x2, x3, x4] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t966 : dispatch 1 (optimized 7) x5 x0 [x5 ||| x6, x1, x2, x3, x4, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t967 : dispatch 1 (optimized 7) x5 x1 [x5 ||| x6, x0, x2, x3, x4, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t968 : dispatch 1 (optimized 7) x5 x2 [x5 ||| x6, x0, x1, x3, x4, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t969 : dispatch 1 (optimized 7) x5 x3 [x5 ||| x6, x0, x1, x2, x4, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t970 : dispatch 1 (optimized 7) x5 x4 [x5 ||| x6, x0, x1, x2, x3, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t971 : dispatch 1 (optimized 7) x5 x7 [x5 ||| x6, x0, x1, x2, x3, x4] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t972 : dispatch 1 (optimized 7) x0 x1 [x5 ||| x6, x5, x2, x3, x4, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t973 : dispatch 1 (optimized 7) x0 x2 [x5 ||| x6, x5, x1, x3, x4, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t974 : dispatch 1 (optimized 7) x0 x3 [x5 ||| x6, x5, x1, x2, x4, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t975 : dispatch 1 (optimized 7) x0 x4 [x5 ||| x6, x5, x1, x2, x3, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t976 : dispatch 1 (optimized 7) x0 x7 [x5 ||| x6, x5, x1, x2, x3, x4] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t977 : dispatch 1 (optimized 7) x1 x2 [x5 ||| x6, x5, x0, x3, x4, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t978 : dispatch 1 (optimized 7) x1 x3 [x5 ||| x6, x5, x0, x2, x4, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t979 : dispatch 1 (optimized 7) x1 x4 [x5 ||| x6, x5, x0, x2, x3, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t980 : dispatch 1 (optimized 7) x1 x7 [x5 ||| x6, x5, x0, x2, x3, x4] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t981 : dispatch 1 (optimized 7) x2 x3 [x5 ||| x6, x5, x0, x1, x4, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t982 : dispatch 1 (optimized 7) x2 x4 [x5 ||| x6, x5, x0, x1, x3, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t983 : dispatch 1 (optimized 7) x2 x7 [x5 ||| x6, x5, x0, x1, x3, x4] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t984 : dispatch 1 (optimized 7) x3 x4 [x5 ||| x6, x5, x0, x1, x2, x7] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t985 : dispatch 1 (optimized 7) x3 x7 [x5 ||| x6, x5, x0, x1, x2, x4] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t986 : dispatch 1 (optimized 7) x4 x7 [x5 ||| x6, x5, x0, x1, x2, x3] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
theorem t987_pairs : pairs [x5 ||| x6, x5, x0, x1, x2, x3, x4, x7] = [(x5 ||| x6, x5, [x0, x1, x2, x3, x4, x7]), (x5 ||| x6, x0, [x5, x1, x2, x3, x4, x7]), (x5 ||| x6, x1, [x5, x0, x2, x3, x4, x7]), (x5 ||| x6, x2, [x5, x0, x1, x3, x4, x7]), (x5 ||| x6, x3, [x5, x0, x1, x2, x4, x7]), (x5 ||| x6, x4, [x5, x0, x1, x2, x3, x7]), (x5 ||| x6, x7, [x5, x0, x1, x2, x3, x4]), (x5, x0, [x5 ||| x6, x1, x2, x3, x4, x7]), (x5, x1, [x5 ||| x6, x0, x2, x3, x4, x7]), (x5, x2, [x5 ||| x6, x0, x1, x3, x4, x7]), (x5, x3, [x5 ||| x6, x0, x1, x2, x4, x7]), (x5, x4, [x5 ||| x6, x0, x1, x2, x3, x7]), (x5, x7, [x5 ||| x6, x0, x1, x2, x3, x4]), (x0, x1, [x5 ||| x6, x5, x2, x3, x4, x7]), (x0, x2, [x5 ||| x6, x5, x1, x3, x4, x7]), (x0, x3, [x5 ||| x6, x5, x1, x2, x4, x7]), (x0, x4, [x5 ||| x6, x5, x1, x2, x3, x7]), (x0, x7, [x5 ||| x6, x5, x1, x2, x3, x4]), (x1, x2, [x5 ||| x6, x5, x0, x3, x4, x7]), (x1, x3, [x5 ||| x6, x5, x0, x2, x4, x7]), (x1, x4, [x5 ||| x6, x5, x0, x2, x3, x7]), (x1, x7, [x5 ||| x6, x5, x0, x2, x3, x4]), (x2, x3, [x5 ||| x6, x5, x0, x1, x4, x7]), (x2, x4, [x5 ||| x6, x5, x0, x1, x3, x7]), (x2, x7, [x5 ||| x6, x5, x0, x1, x3, x4]), (x3, x4, [x5 ||| x6, x5, x0, x1, x2, x7]), (x3, x7, [x5 ||| x6, x5, x0, x1, x2, x4]), (x4, x7, [x5 ||| x6, x5, x0, x1, x2, x3])] := by
  decide +kernel

theorem t987 : optimized 8 1 [x5 ||| x6, x5, x0, x1, x2, x3, x4, x7] = false := by
  rw [optimized.eq_2, t987_pairs]
  simp only [List.any_cons, List.any_nil, t959, t960, t961, t962, t963, t964, t965, t966, t967, t968, t969, t970, t971, t972, t973, t974, t975, t976, t977, t978, t979, t980, t981, t982, t983, t984, t985, t986, Bool.or_false]
  all_goals decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t988 : optimized 8 0 [x5 ||| x6, x5, x6, x0, x1, x2, x3, x4, x7] = false := by
  decide +kernel

theorem t989 : dispatch 2 (optimized 8) x5 x6 [x0, x1, x2, x3, x4, x7] = false := by
  simp only [dispatch, ops, List.any_cons, List.any_nil, Nat.reduceSub, t958, t987, t988, Bool.and_false, Bool.or_false]
  all_goals decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t990 : optimized 8 0 [x5 &&& x7, x5, x7, x0, x1, x2, x3, x4, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t991 : dispatch 1 (optimized 7) (x5 ||| x7) x5 [x0, x1, x2, x3, x4, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t992 : dispatch 0 (optimized 6) ((x5 ||| x7) &&& x0) x0 [x5, x1, x2, x3, x4, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t993 : dispatch 0 (optimized 6) ((x5 ||| x7) &&& x0) x5 [x0, x1, x2, x3, x4, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t994 : dispatch 0 (optimized 6) ((x5 ||| x7) &&& x0) x1 [x0, x5, x2, x3, x4, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t995 : dispatch 0 (optimized 6) ((x5 ||| x7) &&& x0) x2 [x0, x5, x1, x3, x4, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t996 : dispatch 0 (optimized 6) ((x5 ||| x7) &&& x0) x3 [x0, x5, x1, x2, x4, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t997 : dispatch 0 (optimized 6) ((x5 ||| x7) &&& x0) x4 [x0, x5, x1, x2, x3, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t998 : dispatch 0 (optimized 6) ((x5 ||| x7) &&& x0) x6 [x0, x5, x1, x2, x3, x4] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t999 : dispatch 0 (optimized 6) x0 x5 [(x5 ||| x7) &&& x0, x1, x2, x3, x4, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t1000 : dispatch 0 (optimized 6) x0 x1 [(x5 ||| x7) &&& x0, x5, x2, x3, x4, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t1001 : dispatch 0 (optimized 6) x0 x2 [(x5 ||| x7) &&& x0, x5, x1, x3, x4, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t1002 : dispatch 0 (optimized 6) x0 x3 [(x5 ||| x7) &&& x0, x5, x1, x2, x4, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t1003 : dispatch 0 (optimized 6) x0 x4 [(x5 ||| x7) &&& x0, x5, x1, x2, x3, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t1004 : dispatch 0 (optimized 6) x0 x6 [(x5 ||| x7) &&& x0, x5, x1, x2, x3, x4] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t1005 : dispatch 0 (optimized 6) x5 x1 [(x5 ||| x7) &&& x0, x0, x2, x3, x4, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t1006 : dispatch 0 (optimized 6) x5 x2 [(x5 ||| x7) &&& x0, x0, x1, x3, x4, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t1007 : dispatch 0 (optimized 6) x5 x3 [(x5 ||| x7) &&& x0, x0, x1, x2, x4, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t1008 : dispatch 0 (optimized 6) x5 x4 [(x5 ||| x7) &&& x0, x0, x1, x2, x3, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t1009 : dispatch 0 (optimized 6) x5 x6 [(x5 ||| x7) &&& x0, x0, x1, x2, x3, x4] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t1010 : dispatch 0 (optimized 6) x1 x2 [(x5 ||| x7) &&& x0, x0, x5, x3, x4, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t1011 : dispatch 0 (optimized 6) x1 x3 [(x5 ||| x7) &&& x0, x0, x5, x2, x4, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t1012 : dispatch 0 (optimized 6) x1 x4 [(x5 ||| x7) &&& x0, x0, x5, x2, x3, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t1013 : dispatch 0 (optimized 6) x1 x6 [(x5 ||| x7) &&& x0, x0, x5, x2, x3, x4] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t1014 : dispatch 0 (optimized 6) x2 x3 [(x5 ||| x7) &&& x0, x0, x5, x1, x4, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t1015 : dispatch 0 (optimized 6) x2 x4 [(x5 ||| x7) &&& x0, x0, x5, x1, x3, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t1016 : dispatch 0 (optimized 6) x2 x6 [(x5 ||| x7) &&& x0, x0, x5, x1, x3, x4] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t1017 : dispatch 0 (optimized 6) x3 x4 [(x5 ||| x7) &&& x0, x0, x5, x1, x2, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t1018 : dispatch 0 (optimized 6) x3 x6 [(x5 ||| x7) &&& x0, x0, x5, x1, x2, x4] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t1019 : dispatch 0 (optimized 6) x4 x6 [(x5 ||| x7) &&& x0, x0, x5, x1, x2, x3] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
theorem t1020_pairs : pairs [(x5 ||| x7) &&& x0, x0, x5, x1, x2, x3, x4, x6] = [((x5 ||| x7) &&& x0, x0, [x5, x1, x2, x3, x4, x6]), ((x5 ||| x7) &&& x0, x5, [x0, x1, x2, x3, x4, x6]), ((x5 ||| x7) &&& x0, x1, [x0, x5, x2, x3, x4, x6]), ((x5 ||| x7) &&& x0, x2, [x0, x5, x1, x3, x4, x6]), ((x5 ||| x7) &&& x0, x3, [x0, x5, x1, x2, x4, x6]), ((x5 ||| x7) &&& x0, x4, [x0, x5, x1, x2, x3, x6]), ((x5 ||| x7) &&& x0, x6, [x0, x5, x1, x2, x3, x4]), (x0, x5, [(x5 ||| x7) &&& x0, x1, x2, x3, x4, x6]), (x0, x1, [(x5 ||| x7) &&& x0, x5, x2, x3, x4, x6]), (x0, x2, [(x5 ||| x7) &&& x0, x5, x1, x3, x4, x6]), (x0, x3, [(x5 ||| x7) &&& x0, x5, x1, x2, x4, x6]), (x0, x4, [(x5 ||| x7) &&& x0, x5, x1, x2, x3, x6]), (x0, x6, [(x5 ||| x7) &&& x0, x5, x1, x2, x3, x4]), (x5, x1, [(x5 ||| x7) &&& x0, x0, x2, x3, x4, x6]), (x5, x2, [(x5 ||| x7) &&& x0, x0, x1, x3, x4, x6]), (x5, x3, [(x5 ||| x7) &&& x0, x0, x1, x2, x4, x6]), (x5, x4, [(x5 ||| x7) &&& x0, x0, x1, x2, x3, x6]), (x5, x6, [(x5 ||| x7) &&& x0, x0, x1, x2, x3, x4]), (x1, x2, [(x5 ||| x7) &&& x0, x0, x5, x3, x4, x6]), (x1, x3, [(x5 ||| x7) &&& x0, x0, x5, x2, x4, x6]), (x1, x4, [(x5 ||| x7) &&& x0, x0, x5, x2, x3, x6]), (x1, x6, [(x5 ||| x7) &&& x0, x0, x5, x2, x3, x4]), (x2, x3, [(x5 ||| x7) &&& x0, x0, x5, x1, x4, x6]), (x2, x4, [(x5 ||| x7) &&& x0, x0, x5, x1, x3, x6]), (x2, x6, [(x5 ||| x7) &&& x0, x0, x5, x1, x3, x4]), (x3, x4, [(x5 ||| x7) &&& x0, x0, x5, x1, x2, x6]), (x3, x6, [(x5 ||| x7) &&& x0, x0, x5, x1, x2, x4]), (x4, x6, [(x5 ||| x7) &&& x0, x0, x5, x1, x2, x3])] := by
  decide +kernel

theorem t1020 : optimized 7 0 [(x5 ||| x7) &&& x0, x0, x5, x1, x2, x3, x4, x6] = false := by
  rw [optimized.eq_2, t1020_pairs]
  simp only [List.any_cons, List.any_nil, t992, t993, t994, t995, t996, t997, t998, t999, t1000, t1001, t1002, t1003, t1004, t1005, t1006, t1007, t1008, t1009, t1010, t1011, t1012, t1013, t1014, t1015, t1016, t1017, t1018, t1019, Bool.or_false]
  all_goals decide +kernel

theorem t1021 : dispatch 1 (optimized 7) (x5 ||| x7) x0 [x5, x1, x2, x3, x4, x6] = false := by
  simp only [dispatch, ops, List.any_cons, List.any_nil, Nat.reduceSub, t1020, Bool.and_false, Bool.or_false]
  all_goals decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t1022 : dispatch 1 (optimized 7) (x5 ||| x7) x1 [x5, x0, x2, x3, x4, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t1023 : dispatch 1 (optimized 7) (x5 ||| x7) x2 [x5, x0, x1, x3, x4, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t1024 : dispatch 1 (optimized 7) (x5 ||| x7) x3 [x5, x0, x1, x2, x4, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t1025 : dispatch 1 (optimized 7) (x5 ||| x7) x4 [x5, x0, x1, x2, x3, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t1026 : dispatch 1 (optimized 7) (x5 ||| x7) x6 [x5, x0, x1, x2, x3, x4] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t1027 : dispatch 1 (optimized 7) x5 x0 [x5 ||| x7, x1, x2, x3, x4, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t1028 : dispatch 1 (optimized 7) x5 x1 [x5 ||| x7, x0, x2, x3, x4, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t1029 : dispatch 1 (optimized 7) x5 x2 [x5 ||| x7, x0, x1, x3, x4, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t1030 : dispatch 1 (optimized 7) x5 x3 [x5 ||| x7, x0, x1, x2, x4, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t1031 : dispatch 1 (optimized 7) x5 x4 [x5 ||| x7, x0, x1, x2, x3, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t1032 : dispatch 1 (optimized 7) x5 x6 [x5 ||| x7, x0, x1, x2, x3, x4] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t1033 : dispatch 1 (optimized 7) x0 x1 [x5 ||| x7, x5, x2, x3, x4, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t1034 : dispatch 1 (optimized 7) x0 x2 [x5 ||| x7, x5, x1, x3, x4, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t1035 : dispatch 1 (optimized 7) x0 x3 [x5 ||| x7, x5, x1, x2, x4, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t1036 : dispatch 1 (optimized 7) x0 x4 [x5 ||| x7, x5, x1, x2, x3, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t1037 : optimized 7 1 [x0 ||| x6, x5 ||| x7, x5, x1, x2, x3, x4] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t1038 : optimized 7 0 [x0 ||| x6, x0, x5 ||| x7, x5, x1, x2, x3, x4] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t1039 : optimized 7 0 [x0 ||| x6, x6, x5 ||| x7, x5, x1, x2, x3, x4] = false := by
  decide +kernel

theorem t1040 : dispatch 1 (optimized 7) x0 x6 [x5 ||| x7, x5, x1, x2, x3, x4] = false := by
  simp only [dispatch, ops, List.any_cons, List.any_nil, Nat.reduceSub, t1037, t1038, t1039, Bool.and_false, Bool.or_false]
  all_goals decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t1041 : dispatch 1 (optimized 7) x1 x2 [x5 ||| x7, x5, x0, x3, x4, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t1042 : dispatch 1 (optimized 7) x1 x3 [x5 ||| x7, x5, x0, x2, x4, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t1043 : dispatch 1 (optimized 7) x1 x4 [x5 ||| x7, x5, x0, x2, x3, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t1044 : dispatch 1 (optimized 7) x1 x6 [x5 ||| x7, x5, x0, x2, x3, x4] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t1045 : dispatch 1 (optimized 7) x2 x3 [x5 ||| x7, x5, x0, x1, x4, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t1046 : dispatch 1 (optimized 6) (x2 ||| x4) (x5 ||| x7) [x5, x0, x1, x3, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t1047 : dispatch 1 (optimized 6) (x2 ||| x4) x5 [x5 ||| x7, x0, x1, x3, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t1048 : dispatch 1 (optimized 6) (x5 ||| x7) x0 [x2 ||| x4, x5, x1, x3, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t1049 : dispatch 1 (optimized 6) (x5 ||| x7) x1 [x2 ||| x4, x5, x0, x3, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t1050 : dispatch 1 (optimized 6) (x5 ||| x7) x3 [x2 ||| x4, x5, x0, x1, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t1051 : dispatch 1 (optimized 6) (x5 ||| x7) x6 [x2 ||| x4, x5, x0, x1, x3] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t1052 : dispatch 1 (optimized 6) x5 x0 [x2 ||| x4, x5 ||| x7, x1, x3, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t1053 : dispatch 1 (optimized 6) x5 x1 [x2 ||| x4, x5 ||| x7, x0, x3, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t1054 : dispatch 1 (optimized 6) x5 x3 [x2 ||| x4, x5 ||| x7, x0, x1, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t1055 : dispatch 1 (optimized 6) x5 x6 [x2 ||| x4, x5 ||| x7, x0, x1, x3] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t1056 : dispatch 1 (optimized 6) x0 x1 [x2 ||| x4, x5 ||| x7, x5, x3, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t1057 : dispatch 1 (optimized 6) x0 x3 [x2 ||| x4, x5 ||| x7, x5, x1, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t1058 : dispatch 1 (optimized 6) x0 x6 [x2 ||| x4, x5 ||| x7, x5, x1, x3] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t1059 : dispatch 1 (optimized 6) x1 x3 [x2 ||| x4, x5 ||| x7, x5, x0, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t1060 : dispatch 1 (optimized 6) x1 x6 [x2 ||| x4, x5 ||| x7, x5, x0, x3] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t1061 : dispatch 1 (optimized 6) x3 x6 [x2 ||| x4, x5 ||| x7, x5, x0, x1] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
theorem t1062_pairs : pairs [x2 ||| x4, x5 ||| x7, x5, x0, x1, x3, x6] = [(x2 ||| x4, x5 ||| x7, [x5, x0, x1, x3, x6]), (x2 ||| x4, x5, [x5 ||| x7, x0, x1, x3, x6]), (x2 ||| x4, x0, [x5 ||| x7, x5, x1, x3, x6]), (x2 ||| x4, x1, [x5 ||| x7, x5, x0, x3, x6]), (x2 ||| x4, x3, [x5 ||| x7, x5, x0, x1, x6]), (x2 ||| x4, x6, [x5 ||| x7, x5, x0, x1, x3]), (x5 ||| x7, x5, [x2 ||| x4, x0, x1, x3, x6]), (x5 ||| x7, x0, [x2 ||| x4, x5, x1, x3, x6]), (x5 ||| x7, x1, [x2 ||| x4, x5, x0, x3, x6]), (x5 ||| x7, x3, [x2 ||| x4, x5, x0, x1, x6]), (x5 ||| x7, x6, [x2 ||| x4, x5, x0, x1, x3]), (x5, x0, [x2 ||| x4, x5 ||| x7, x1, x3, x6]), (x5, x1, [x2 ||| x4, x5 ||| x7, x0, x3, x6]), (x5, x3, [x2 ||| x4, x5 ||| x7, x0, x1, x6]), (x5, x6, [x2 ||| x4, x5 ||| x7, x0, x1, x3]), (x0, x1, [x2 ||| x4, x5 ||| x7, x5, x3, x6]), (x0, x3, [x2 ||| x4, x5 ||| x7, x5, x1, x6]), (x0, x6, [x2 ||| x4, x5 ||| x7, x5, x1, x3]), (x1, x3, [x2 ||| x4, x5 ||| x7, x5, x0, x6]), (x1, x6, [x2 ||| x4, x5 ||| x7, x5, x0, x3]), (x3, x6, [x2 ||| x4, x5 ||| x7, x5, x0, x1])] := by
  decide +kernel

theorem t1062 : optimized 7 1 [x2 ||| x4, x5 ||| x7, x5, x0, x1, x3, x6] = false := by
  rw [optimized.eq_2, t1062_pairs]
  simp only [List.any_cons, List.any_nil, t1046, t1047, t623, t624, t625, t626, t612, t1048, t1049, t1050, t1051, t1052, t1053, t1054, t1055, t1056, t1057, t1058, t1059, t1060, t1061, Bool.or_false]
  all_goals decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t1063 : optimized 7 0 [x2 ||| x4, x2, x5 ||| x7, x5, x0, x1, x3, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t1064 : optimized 7 0 [x2 ||| x4, x4, x5 ||| x7, x5, x0, x1, x3, x6] = false := by
  decide +kernel

theorem t1065 : dispatch 1 (optimized 7) x2 x4 [x5 ||| x7, x5, x0, x1, x3, x6] = false := by
  simp only [dispatch, ops, List.any_cons, List.any_nil, Nat.reduceSub, t1062, t1063, t1064, Bool.and_false, Bool.or_false]
  all_goals decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t1066 : dispatch 1 (optimized 7) x2 x6 [x5 ||| x7, x5, x0, x1, x3, x4] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t1067 : dispatch 1 (optimized 7) x3 x4 [x5 ||| x7, x5, x0, x1, x2, x6] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t1068 : dispatch 1 (optimized 7) x3 x6 [x5 ||| x7, x5, x0, x1, x2, x4] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t1069 : dispatch 1 (optimized 7) x4 x6 [x5 ||| x7, x5, x0, x1, x2, x3] = false := by
  decide +kernel

set_option maxRecDepth 8000 in
theorem t1070_pairs : pairs [x5 ||| x7, x5, x0, x1, x2, x3, x4, x6] = [(x5 ||| x7, x5, [x0, x1, x2, x3, x4, x6]), (x5 ||| x7, x0, [x5, x1, x2, x3, x4, x6]), (x5 ||| x7, x1, [x5, x0, x2, x3, x4, x6]), (x5 ||| x7, x2, [x5, x0, x1, x3, x4, x6]), (x5 ||| x7, x3, [x5, x0, x1, x2, x4, x6]), (x5 ||| x7, x4, [x5, x0, x1, x2, x3, x6]), (x5 ||| x7, x6, [x5, x0, x1, x2, x3, x4]), (x5, x0, [x5 ||| x7, x1, x2, x3, x4, x6]), (x5, x1, [x5 ||| x7, x0, x2, x3, x4, x6]), (x5, x2, [x5 ||| x7, x0, x1, x3, x4, x6]), (x5, x3, [x5 ||| x7, x0, x1, x2, x4, x6]), (x5, x4, [x5 ||| x7, x0, x1, x2, x3, x6]), (x5, x6, [x5 ||| x7, x0, x1, x2, x3, x4]), (x0, x1, [x5 ||| x7, x5, x2, x3, x4, x6]), (x0, x2, [x5 ||| x7, x5, x1, x3, x4, x6]), (x0, x3, [x5 ||| x7, x5, x1, x2, x4, x6]), (x0, x4, [x5 ||| x7, x5, x1, x2, x3, x6]), (x0, x6, [x5 ||| x7, x5, x1, x2, x3, x4]), (x1, x2, [x5 ||| x7, x5, x0, x3, x4, x6]), (x1, x3, [x5 ||| x7, x5, x0, x2, x4, x6]), (x1, x4, [x5 ||| x7, x5, x0, x2, x3, x6]), (x1, x6, [x5 ||| x7, x5, x0, x2, x3, x4]), (x2, x3, [x5 ||| x7, x5, x0, x1, x4, x6]), (x2, x4, [x5 ||| x7, x5, x0, x1, x3, x6]), (x2, x6, [x5 ||| x7, x5, x0, x1, x3, x4]), (x3, x4, [x5 ||| x7, x5, x0, x1, x2, x6]), (x3, x6, [x5 ||| x7, x5, x0, x1, x2, x4]), (x4, x6, [x5 ||| x7, x5, x0, x1, x2, x3])] := by
  decide +kernel

theorem t1070 : optimized 8 1 [x5 ||| x7, x5, x0, x1, x2, x3, x4, x6] = false := by
  rw [optimized.eq_2, t1070_pairs]
  simp only [List.any_cons, List.any_nil, t991, t1021, t1022, t1023, t1024, t1025, t1026, t1027, t1028, t1029, t1030, t1031, t1032, t1033, t1034, t1035, t1036, t1040, t1041, t1042, t1043, t1044, t1045, t1065, t1066, t1067, t1068, t1069, Bool.or_false]
  all_goals decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t1071 : optimized 8 0 [x5 ||| x7, x5, x7, x0, x1, x2, x3, x4, x6] = false := by
  decide +kernel

theorem t1072 : dispatch 2 (optimized 8) x5 x7 [x0, x1, x2, x3, x4, x6] = false := by
  simp only [dispatch, ops, List.any_cons, List.any_nil, Nat.reduceSub, t990, t1070, t1071, Bool.and_false, Bool.or_false]
  all_goals decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem t1073 : dispatch 2 (optimized 8) x6 x7 [x0, x1, x2, x3, x4, x5] = false := by
  decide +kernel

def heavy0 : List W := [x0, x1, x2, x3, x4, x5, x6, x7]

set_option maxRecDepth 8000 in
theorem heavy0_pairs : pairs heavy0 = [(x0, x1, [x2, x3, x4, x5, x6, x7]), (x0, x2, [x1, x3, x4, x5, x6, x7]), (x0, x3, [x1, x2, x4, x5, x6, x7]), (x0, x4, [x1, x2, x3, x5, x6, x7]), (x0, x5, [x1, x2, x3, x4, x6, x7]), (x0, x6, [x1, x2, x3, x4, x5, x7]), (x0, x7, [x1, x2, x3, x4, x5, x6]), (x1, x2, [x0, x3, x4, x5, x6, x7]), (x1, x3, [x0, x2, x4, x5, x6, x7]), (x1, x4, [x0, x2, x3, x5, x6, x7]), (x1, x5, [x0, x2, x3, x4, x6, x7]), (x1, x6, [x0, x2, x3, x4, x5, x7]), (x1, x7, [x0, x2, x3, x4, x5, x6]), (x2, x3, [x0, x1, x4, x5, x6, x7]), (x2, x4, [x0, x1, x3, x5, x6, x7]), (x2, x5, [x0, x1, x3, x4, x6, x7]), (x2, x6, [x0, x1, x3, x4, x5, x7]), (x2, x7, [x0, x1, x3, x4, x5, x6]), (x3, x4, [x0, x1, x2, x5, x6, x7]), (x3, x5, [x0, x1, x2, x4, x6, x7]), (x3, x6, [x0, x1, x2, x4, x5, x7]), (x3, x7, [x0, x1, x2, x4, x5, x6]), (x4, x5, [x0, x1, x2, x3, x6, x7]), (x4, x6, [x0, x1, x2, x3, x5, x7]), (x4, x7, [x0, x1, x2, x3, x5, x6]), (x5, x6, [x0, x1, x2, x3, x4, x7]), (x5, x7, [x0, x1, x2, x3, x4, x6]), (x6, x7, [x0, x1, x2, x3, x4, x5])] := by
  decide +kernel

theorem heavy0_false : optimized 9 (10 - heavy0.length) heavy0 = false := by
  rw [show 10 - heavy0.length = 2 by decide, optimized.eq_2, heavy0_pairs]
  simp only [List.any_cons, List.any_nil, t3, t4, t36, t39, t114, t255, t311, t343, t426, t501, t504, t505, t560, t561, t697, t698, t699, t754, t805, t860, t915, t921, t924, t925, t957, t989, t1072, t1073, Bool.or_false]
  all_goals decide

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem all_front : inputs.sublists.all
    (fun l => (l == heavy0) || decide (10 < l.length) || !(optimized 9 (10 - l.length) l)) = true := by
  decide +kernel

theorem no_small (C : Circuit) (hm : Monotone2 C) (hs : C.size ≤ 9)
    (hr : PEqualNP.Represents.Represents A C) : False := by
  obtain ⟨S, hsub, hl⟩ := compress (get_build C hm hr)
  have hl3 : live basicOps goal 9 S := extend_live hs hl
  let l := inputs.filter (fun w => decide (w ∈ S))
  have hlS : l.toFinset = S := by
    ext v
    simp only [l, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨List.mem_toFinset.mp (hsub h), h⟩
  have hnd : l.Nodup := inputs_nodup.filter _
  have hcard := live_card hl3
  rw [← hlS, List.toFinset_card_of_nodup hnd] at hcard
  have hsearch := optimized_complete 9 l (10 - l.length) hnd (by omega) (hlS ▸ hl3)
  have hmem : l ∈ inputs.sublists := List.mem_sublists.mpr List.filter_sublist
  by_cases e0 : l = heavy0
  · rw [e0, heavy0_false] at hsearch
    exact Bool.noConfusion hsearch
  have n0 : (l == heavy0) = false := by simpa using e0
  have hrow := List.all_eq_true.mp all_front l hmem
  have h4 : decide (10 < l.length) = false := by simp; omega
  rw [n0, h4, hsearch] at hrow
  exact Bool.noConfusion hrow

def upperC : Circuit :=
  { gates := [{ op := GateOp.or, inputs := [0, 1] }, { op := GateOp.or, inputs := [8, 3] }, { op := GateOp.and, inputs := [9, 4] }, { op := GateOp.or, inputs := [1, 2] }, { op := GateOp.or, inputs := [5, 6] }, { op := GateOp.and, inputs := [12, 11] }, { op := GateOp.or, inputs := [13, 10] }, { op := GateOp.or, inputs := [5, 7] }, { op := GateOp.and, inputs := [15, 0] }, { op := GateOp.or, inputs := [16, 14] }],
    output := 17 }

theorem upper_mono : Monotone2 upperC := by
  intro g hg
  simp only [upperC, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem upper_rep : PEqualNP.Represents.Represents A upperC := by
  decide +kernel

end PEqualNP.Outside.L_meta_6346_aux

theorem PEqualNP.Outside.L_meta_6346 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (5755 : ℕ).testBit (4 * u.val + v.val)) 10 ∧
  ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (5755 : ℕ).testBit (4 * u.val + v.val)) 9 := by
  refine ⟨⟨PEqualNP.Outside.L_meta_6346_aux.upperC, PEqualNP.Outside.L_meta_6346_aux.upper_mono,
    by decide, PEqualNP.Outside.L_meta_6346_aux.upper_rep⟩, ?_⟩
  rintro ⟨C, hm, hs, hr⟩
  exact PEqualNP.Outside.L_meta_6346_aux.no_small C hm hs hr
