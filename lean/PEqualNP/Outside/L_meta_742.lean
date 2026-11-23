import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_742


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def build {α : Type} [DecidableEq α] (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k+1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

def live {α : Type} [DecidableEq α] (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k+1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

theorem compress {α : Type} [DecidableEq α] {ops : α → α → Finset α} {goal : α} {k : ℕ}
    {available : Finset α} (h : build ops goal k available) :
    ∃ s ⊆ available, live ops goal k s := by
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

theorem live_card {α : Type} [DecidableEq α] {ops : α → α → Finset α} {goal : α} {k : ℕ}
    {s : Finset α} (h : live ops goal k s) : s.card ≤ k + 1 := by
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

theorem live_separates {α : Type} [DecidableEq α] {ops : α → α → Finset α} {goal : α}
    (D : α → Prop) (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
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

theorem first_live {α : Type} [DecidableEq α] {ops : α → α → Finset α} {goal : α}
    {k : ℕ} {s : Finset α} (h : live ops goal (k + 1) s) :
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

abbrev W := BitVec 108

def ops (x y : W) : List W := [x &&& y, x ||| y]

def sep (x : W) : BitVec 54 := ((x >>> 54) &&& ~~~x).setWidth 54

def cuts (ws : List W) : BitVec 54 := ws.foldr (fun w v => sep w ||| v) 0

def goal : W := (-1 : BitVec 54) ++ (0 : BitVec 54)

def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

def rawInputs : List W :=
  [0xfc000003ffd4514514514514, 0x3f000000fc0fe1861861861861, 0xfc0000000fff00a28a28a28a28a, 0xfc0fff0000030c30c30c30c3, 0x3f03f03f00000c30c30c30c30c, 0xfc003ffc0000030c30c30c30c30]

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

abbrev basicOps (a b : W) := (ops a b).toFinset

def differs (i : Fin 54) (w : W) : Prop :=
  w.getLsbD (54 + i.val) = true ∧ w.getLsbD i.val = false

theorem ops_differs (i : Fin 54) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  unfold differs at hd ⊢
  rcases hz with rfl | rfl <;> revert hd <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or] <;>
    cases a.getLsbD (54 + i.val) <;> cases a.getLsbD i.val <;>
    cases b.getLsbD (54 + i.val) <;> cases b.getLsbD i.val <;> simp

theorem goal_differs : ∀ i : Fin 54, differs i goal := by
  unfold differs
  decide

theorem cuts_spec (ws : List W) (i : Fin 54) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have hi : i.val < 108 := by omega
    simp [sep, i.isLt, differs, hi, Nat.add_comm]

theorem cuts_full {k : ℕ} {ws : List W} (h : live basicOps goal k ws.toFinset) :
    cuts ws = -1 := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (goal_differs ⟨j, hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 54)[j]
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

theorem singleton_list {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) :
    ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

private def possible (w : List W) (z : W) : Bool :=
  z == 0 || z == BitVec.allOnes 108 || w.any (fun u => z == u ||
    w.any (fun v => z == (u &&& v) || z == (u ||| v)))

private def bit (k : Fin 108) (z : W) : Bool := z[k.val]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 108) :
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
  have mem (i : ℕ) : w.getD i 0 = 0 ∨ w.getD i 0 ∈ ws := (read_wire w i).imp_right (fun h => hw h)
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  change op = .and ∨ op = .or at hop
  change args.length ≤ 2 at hlen
  cases args with
  | nil =>
    rcases hop with rfl | rfl
    · exact ⟨BitVec.allOnes 108, by simp [possible], by simp [step, GateOp.eval, bit]; decide⟩
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
  ∀ u ∈ w, u = 0 ∨ u = BitVec.allOnes 108 ∨ u ∈ available

theorem classify {available : Finset W} {ws : List W} (hw : represents available ws)
    {z : W} (hz : possible ws z) :
    z = 0 ∨ z = BitVec.allOnes 108 ∨ z ∈ available ∨
      ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧ z ∈ basicOps a b := by
  have lift {t : W} (h : t = 0 ∨ t = BitVec.allOnes 108 ∨ t ∈ available) :
      t = 0 ∨ t = BitVec.allOnes 108 ∨ t ∈ available ∨
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
      · exact False.elim ((by decide : goal ≠ BitVec.allOnes 108) h)
      · exact h
  | cons g gs ih =>
    obtain ⟨z, hz, hstep⟩ := gate_table w w (fun _ h => h) g (hg g (by simp))
    have fn := ih (fun g' h => hg g' (by simp [h])) (w ++ [z])
    have he' : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k goal := by
      intro k; simpa only [List.foldl_cons, hstep] using he k
    have appendOK (h : z = 0 ∨ z = BitVec.allOnes 108 ∨ z ∈ av) : represents av (w ++ [z]) := by
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

def edges : List (ℕ × ℕ) :=
  [(0, 1), (0, 2), (1, 2), (3, 4), (3, 5), (4, 5), (0, 3), (1, 4), (2, 5)]

def assignment (k : Fin 108) (i : Fin 6) : Bool := bit k (rawInputs.getD i.val 0)

theorem full_inputs {s : Finset W} {k : ℕ} (hs : s ⊆ inputs.toFinset)
    (hr : live basicOps goal k s) : s = inputs.toFinset := by
  apply Finset.Subset.antisymm hs
  intro a ha
  let sites : List (Fin 54) := [0, 2, 8, 20, 18, 24]
  have necessary : inputs.all (fun a => sites.any (fun i => inputs.all (fun b =>
      !(b.getLsbD (54 + i.val) && !b.getLsbD i.val) || b == a))) = true := by decide
  obtain ⟨i, _, hAll⟩ :=
    List.any_eq_true.mp (List.all_eq_true.mp necessary a (List.mem_toFinset.mp ha))
  have hi (b : W) (hb : b ∈ inputs) (hd : differs i b) : b = a := by
    have hrow := List.all_eq_true.mp hAll b hb
    obtain ⟨h1, h2⟩ := hd
    simpa [h1, h2] using hrow
  obtain ⟨b, hb, hd⟩ := live_separates (differs i) (goal_differs i) (ops_differs i) hr
  exact hi b (List.mem_toFinset.mp (hs hb)) hd ▸ hb

theorem input_rows (k : Fin 108) : List.ofFn (assignment k) = rawInputs.map (bit k) := by
  rfl

theorem graph_rows : ∀ k : Fin 108, (∃ u v : Fin 6, (u.val, v.val) ∈ edges ∧
    assignment k u = true ∧ assignment k v = true) ↔ bit k goal = true := by
  decide +kernel

theorem rows_eval (C : Circuit)
    (he : ∀ x : Fin 6 → Bool, (C.eval (List.ofFn x) = true ↔
      ∃ u v : Fin 6, (u.val, v.val) ∈ edges ∧ x u = true ∧ x v = true)) (k : Fin 108) :
    (C.gates.foldl step (rawInputs.map (bit k))).getD C.output false = bit k goal := by
  rw [← input_rows]
  exact Bool.eq_iff_iff.mpr ((he (assignment k)).trans (graph_rows k))

theorem initial_rep : represents inputs.toFinset rawInputs := by
  intro u hu
  exact .inr (.inr (List.mem_toFinset.mpr hu))

theorem get_build (C : Circuit) (hg : Monotone2 C)
    (he : ∀ x : Fin 6 → Bool, (C.eval (List.ofFn x) = true ↔
      ∃ u v : Fin 6, (u.val, v.val) ∈ edges ∧ x u = true ∧ x v = true)) :
    build basicOps goal C.gates.length inputs.toFinset :=
  compile C.gates C.output hg rawInputs inputs.toFinset initial_rep (rows_eval C he)

theorem input_live (k : ℕ) (hb : build basicOps goal k inputs.toFinset) :
    live basicOps goal k inputs.toFinset := by
  obtain ⟨S, hsub, hLive⟩ := compress hb
  exact full_inputs hsub hLive ▸ hLive

theorem extend_live {m n : ℕ} (le : m ≤ n) (h : live basicOps goal m inputs.toFinset) :
    live basicOps goal n inputs.toFinset := by
  induction le with
  | refl => exact h
  | step _ ih => exact Or.inl ih

def dispatch (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) : Bool :=
  let base := cuts r
  (ops a b).any fun w =>
    let v := sep w ||| base
    !(w == a || w == b || r.contains w) && ( (v == -1) && next extra (w :: r) ||
    ((extra != 0) && (((v ||| sep a == -1) && next (extra - 1) (w :: a :: r)) ||
                       ((v ||| sep b == -1) && next (extra - 1) (w :: b :: r)))) ||
    ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && next (extra - 2) (w :: a :: b :: r)))

theorem dispatch_complete {k extra : ℕ} {a b z : W} {r kept : List W}
    (next : ℕ → List W → Bool)
    (hz : z ∈ basicOps a b) (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hf : z ∉ a :: b :: r) (hc : cuts (z :: kept) = -1) (ht : next (k - kept.length) (z :: kept) = true) :
    dispatch extra next a b r = true := by
  apply List.any_eq_true.mpr
  refine ⟨z, List.mem_toFinset.mp hz, ?_⟩
  have fresh : (!(z == a || z == b || r.contains z)) = true := by simpa [and_assoc] using hf
  simp only [fresh, Bool.true_and]
  simp [keepChoices] at hk
  rcases hk with rfl | rfl | rfl | rfl <;>
    simp only [cuts, List.foldr_cons] at hc ⊢ <;>
    (try simp only [List.length_cons] at *) <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne]
  · left; left; exact ⟨hc, by convert ht using 2; omega⟩
  · left; right; exact ⟨by omega,
      .inl ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · left; right; exact ⟨by omega,
      .inr ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · right; exact ⟨⟨by omega, by convert hc using 1; ac_rfl⟩, by convert ht using 2; omega⟩

def branch (extra : ℕ) (next : ℕ → List W → Bool) (ws : List W) : Bool :=
  ws == [goal] || (pairs ws).any (fun (a,b,r) => dispatch extra next a b r)

theorem branch_complete (k : ℕ) (ws : List W) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = k + 2) (h : live basicOps goal (k+1) ws.toFinset)
    (next : ℕ → List W → Bool)
    (ih : ∀ (ys : List W) (e : ℕ), ys.Nodup → e + ys.length = k+1 →
      live basicOps goal k ys.toFinset → next e ys = true) :
    branch extra next ws = true := by
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · simp [branch, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : W} (perm : ws.Perm (a :: b :: r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          dispatch extra next a b r = true := by
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem
            (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live basicOps goal k (z :: kept).toFinset := by
          simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        apply dispatch_complete (k := k) (extra := extra) next hop hk
          (by omega) (by omega) (by intro mem; exact hout (List.mem_toFinset.mpr (perm.mem_iff.mpr mem))) (cuts_full hl)
        apply ih _ _ hnd _ hl
        simp; omega
      simp only [branch, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs hz⟩
      · exact ⟨(b, a, r), swap,
          go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

def equalSet (xs ys : List W) : Bool :=
  xs.all (fun w => ys.contains w) && ys.all (fun w => xs.contains w)

lemma equalSet_sound {xs ys : List W} (h : equalSet xs ys = true) : xs.toFinset = ys.toFinset := by
  simpa [equalSet, Bool.and_eq_true, List.all_eq_true, Finset.Subset.antisymm_iff,
    Finset.subset_iff] using h

def fingerprint (xs : List W) : ℕ :=
  xs.foldl (fun a w => a + ((w.toNat + 37) * (w.toNat + 37) % 1000000007)) 0

def field (a width index : ℕ) : ℕ := (a >>> (width * index)) % (2^width)

def unpack (wire : ℕ → W) (bits : ℕ) : ℕ → ℕ → List W
  | 0, _ => []
  | n+1, a => wire (a % (2^bits)) :: unpack wire bits n (a >>> bits)

def matchTable (size : ℕ) (db : ℕ → List W) (pick : ℕ → ℕ) (xs : List W) : Bool :=
  equalSet xs (db (pick (fingerprint xs) % size))

lemma match_safe {k size : ℕ} (hp : 0 < size) {db : ℕ → List W} {pick : ℕ → ℕ}
    (hd : ∀ i < size, ¬live basicOps goal k (db i).toFinset) (xs : List W)
    (hl : live basicOps goal k xs.toFinset) : (!(matchTable size db pick xs)) = true := by
  cases hh : matchTable size db pick xs with
  | false => rfl
  | true => exact False.elim (hd _ (Nat.mod_lt _ hp) (equalSet_sound hh ▸ hl))

def checkState (k : ℕ) (allows : List W → Bool) (ws : List W) : Bool :=
  decide ws.Nodup && !(branch (k + 2 - ws.length) (fun _ => allows) ws)

lemma checkState_sound {k : ℕ} {allows : List W → Bool}
    (good : ∀ xs : List W, live basicOps goal k xs.toFinset → allows xs = true)
    {ws : List W} (hc : checkState k allows ws = true) : ¬live basicOps goal (k+1) ws.toFinset := by
  intro hl
  simp only [checkState, Bool.and_eq_true] at hc
  obtain ⟨nd, hh⟩ := hc
  have hn : ws.Nodup := of_decide_eq_true nd
  have sz := live_card hl
  rw [List.toFinset_card_of_nodup hn] at sz
  have hit := branch_complete k ws (k+2-ws.length) hn (by omega) hl _ (fun ys _ _ _ hy => good ys hy)
  simp [hit] at hh

def runBlock (test : ℕ → Bool) (start : ℕ) : ℕ → Bool
  | 0 => true
  | n+1 => test (start+n) && runBlock test start n

lemma runBlock_get {test : ℕ → Bool} {start len : ℕ} (h : runBlock test start len = true)
    (i : ℕ) (lo : start ≤ i) (hi : i < start + len) : test i = true := by
  induction len with
  | zero => omega
  | succ n ih =>
    simp only [runBlock, Bool.and_eq_true] at h
    obtain ⟨last, rest⟩ := h
    by_cases eq : i = start+n
    · simpa [eq] using last
    · exact ih rest (by omega)
def wireRawChunk (i : ℕ) : ℕ :=
  if i < 28 then if i < 14 then if i < 7 then if i < 3 then if i < 1 then 0x1041041041041000000000000000c30c30c30c30c00000000000000a28a28a28a28a0000000000000092492492492490000000000000082082082082080000000000000061861861861860000000000000051451451451450000000000000041041041041040000000000000030c30c30c30c3000000000000002082082082082000000000000001041041041041000000000000000000000000000 else if i < 2 then 0xfc1041041041041000000000000fc0000000000000000000000000030c30c30c30c30000000000000028a28a28a28a280000000000000249249249249240000000000000228a28a28a28a2000000000000021861861861861000000000000020820820820820000000000000018618618618618000000000000014514514514514000000000000012492492492492000000000000011451451451451 else 0x3f00820820820820800000000003f00410410410410400000000003f00208208208208200000000003f00104104104104100000000003f000000000000000000000000000fe1861861861861000000000000fe0820820820820000000000000fd4514514514514000000000000fd0410410410410000000000000fc8208208208208000000000000fc4104104104104000000000000fc2082082082082 else if i < 5 then if i < 4 then 0xfc0004104104104104000000000fc0002082082082082000000000fc0001041041041041000000000fc000000000000000000000000003ffd041041041041000000000003ffc410410410410400000000003ffc30c30c30c30c300000000003ffc000000000000000000000003f02082082082082000000000003f01451451451451400000000003f01041041041041000000000003f00a28a28a28a28a else 0xfff008208208208208000000000fff002082082082082000000000fff000000000000000000000000fc0fe0820820820820000000000fc0fcc30c30c30c30c000000000fc0fc1041041041041000000000fc0fc0000000000000000000000fc0021861861861861000000000fc0020820820820820000000000fc0010410410410410000000000fc000a28a28a28a28a000000000fc0008208208208208 else if i < 6 then 0x3f000fc514514514514500000003f000fc000000000000000000003f00002082082082082000000003f00001041041041041000000003f00000c30c30c30c30c00000003f00000820820820820800000003f00000410410410410400000003f0000030c30c30c30c300000003f00000208208208208200000003f00000104104104104100000003f000000000000000000000000000fff030c30c30c30c30 else 0xfc0000020820820820820000000fc0000010410410410410000000fc0000008208208208208000000fc0000004104104104104000000fc00000030c30c30c30c3000000fc0000002082082082082000000fc0000001041041041041000000fc000000000000000000000000003ffc000924924924924900000003ffc000000000000000000000003f03f00618618618618600000003f03f000000000000000 else if i < 10 then if i < 8 then 0x3f000000000000000000000000000fff000014514514514514000000fff000002082082082082000000fff000001041041041041000000fff000000000000000000000000fc0fc00228a28a28a28a2000000fc0fc0000000000000000000000fc003f012492492492492000000fc003f000000000000000000000fc0000fd1451451451451000000fc0000fc0000000000000000000fc0000030c30c30c30c30 else if i < 9 then 0x3f00003f01861861861861800003f00003f00000000000000000003f000000fe492492492492400003f000000fc000000000000000003f000000030c30c30c30c3000003f00000002082082082082000003f00000001041041041041000003f00000000c30c30c30c30c00003f00000000820820820820800003f00000000410410410410400003f00000000208208208208200003f000000001041041041041 else 0xfc0000000001041041041041000fc000000000000000000000000003ffc000002082082082082000003ffc000001041041041041000003ffc000000a28a28a28a28a00003ffc000000000000000000000003f03f00002186186186186100003f03f00000820820820820800003f03f00000410410410410400003f03f00000000000000000000003f000fc0028a28a28a28a2800003f000fc0000000000000000 else if i < 12 then if i < 11 then 0xfc0000000fd0410410410410000fc0000000fc4104104104104000fc0000000fc0000000000000000fc0000000031c71c71c71c71000fc0000000020820820820820000fc0000000014514514514514000fc0000000010410410410410000fc000000000e38e38e38e38e000fc0000000008208208208208000fc0000000004104104104104000fc00000000030c30c30c30c3000fc0000000002082082082082 else 0xfc000003ffde79e79e79e79e000fc000003ffdc71c71c71c71c000fc000003ffd75d75d75d75d7000fc000003ffd6596596596596000fc000003ffd5555555555555000fc000003ffd4514514514514000fc000003ffd0410410410410000fc000003ffc4104104104104000fc000003ffc0000000000000000fc000003f010410410410410000fc000003f004104104104104000fc000003f000000000000000 else if i < 13 then 0xfc003f000001041041041041000fc003f000000000000000000000fc0000fffff4d34d34d34d34000fc0000ffffdc71c71c71c71c000fc0000ffffd6596596596596000fc0000ffffd5555555555555000fc0000ffffd4514514514514000fc0000fff001041041041041000fc0000fc0fc2082082082082000fc0000fc0000000000000000000fc000003fff5d75d75d75d75000fc000003fff4d34d34d34d34 else 0xfc0fc003ffd4514514514514000fc0fc0000fe0820820820820000fc0fc0000002082082082082000fc0fc0000001041041041041000fc0fc0000000000000000000000fc003fffffd4514514514514000fc003f03ffdc71c71c71c71c000fc003f03ffd6596596596596000fc003f03ffd5555555555555000fc003f03ffd4514514514514000fc003f03f008208208208208000fc003f000002082082082082 else if i < 21 then if i < 17 then if i < 15 then 0xfc0fff0000134d34d34d34d3000fc0fff00000f3cf3cf3cf3cf000fc0fff00000b2cb2cb2cb2cb000fc0fff0000071c71c71c71c7000fc0fff0000030c30c30c30c3000fc0fff000002082082082082000fc0fff000001041041041041000fc0fff000000000000000000000fc0fc0ffffd4514514514514000fc0fc003fff4d34d34d34d34000fc0fc003ffd6596596596596000fc0fc003ffd5555555555555 else if i < 16 then 0xfc0fff03ffc30c30c30c30c3000fc0fff03f0134d34d34d34d3000fc0fff03f00b2cb2cb2cb2cb000fc0fff03f0071c71c71c71c7000fc0fff03f0030c30c30c30c3000fc0fff000fe38e38e38e38e3000fc0fff000fd34d34d34d34d3000fc0fff000fc71c71c71c71c7000fc0fff000fc30c30c30c30c3000fc0fff000033cf3cf3cf3cf3000fc0fff0000238e38e38e38e3000fc0fff0000175d75d75d75d7 else 0xfff00003ffd4514514514514000fff000000000000000000000000fc0fffffffd75d75d75d75d7000fc0ffffff0030c30c30c30c3000fc0ffffc0fc30c30c30c30c3000fc0ffffc00238e38e38e38e3000fc0ffffc000b2cb2cb2cb2cb000fc0ffffc00030c30c30c30c3000fc0fff03fff7df7df7df7df7000fc0fff03ffdf7df7df7df7df000fc0fff03ffd75d75d75d75d7000fc0fff03ffd4514514514514 else if i < 19 then if i < 18 then 0xffffff0000238e38e38e38e3000ffffff0000134d34d34d34d3000ffffff00000b2cb2cb2cb2cb000ffffff0000071c71c71c71c7000ffffff0000030c30c30c30c3000ffffc003ffd4514514514514000ffffc0000004104104104104000fff03f03ffd4514514514514000fff03f000010410410410410000fff000ffffd4514514514514000fff00003fff4d34d34d34d34000fff00003ffdc71c71c71c71c else 0x3f00000000001041041041041003f00000000000c30c30c30c30c03f00000000000b2cb2cb2cb2cb03f00000000000820820820820803f00000000000410410410410403f00000000000208208208208203f00000000000104104104104103f000000000000000000000000000fffffffc00030c30c30c30c3000ffffff03ffd75d75d75d75d7000ffffff03f0030c30c30c30c3000ffffff000fc30c30c30c30c3 else if i < 20 then 0x3f000000fc0fc000000000000003f000000fc002082082082082003f000000fc000104104104104103f000000fc000000000000000003f00000003ffc820820820820803f00000003f00000000000000003f000000000fe082082082082003f000000000fc104104104104103f000000000fc000000000000003f000000000034d34d34d34d3403f00000000002186186186186103f000000000020820820820820 else 0x3f000000ffffe186186186186103f000000fff00410410410410403f000000fc0ff5d75d75d75d7503f000000fc0ff1c71c71c71c7103f000000fc0fedb6db6db6db6d03f000000fc0febaebaebaebaeb03f000000fc0fe9a69a69a69a6903f000000fc0fe596596596596503f000000fc0fe38e38e38e38e303f000000fc0fe186186186186103f000000fc0fe082082082082003f000000fc0fc1041041041041 else if i < 24 then if i < 22 then 0x3f00003ffc0fe9a69a69a69a6903f00003ffc0fe596596596596503f00003ffc0fe38e38e38e38e303f00003ffc0fe186186186186103f00003ffc000208208208208203f00003f00000820820820820803f00003f00000410410410410403f00003f00000000000000000003f000000fffff1c71c71c71c7103f000000ffffe9a69a69a69a6903f000000ffffe596596596596503f000000ffffe38e38e38e38e3 else if i < 23 then 0x3f03f000000fd041041041041003f03f00000000820820820820803f03f00000000410410410410403f03f00000000000000000000003f000ffffc0fe186186186186103f000fff00002082082082082003f000fc0ffffe186186186186103f000fc0fc0ff1c71c71c71c7103f000fc0fc0fe38e38e38e38e303f000fc0fc0fe186186186186103f000fc000000000000000000003f00003fffffe1861861861861 else 0x3f03f03f00000f3cf3cf3cf3cf03f03f03f00000e38e38e38e38e03f03f03f00000d34d34d34d34d03f03f03f00000c30c30c30c30c03f03f03f00000820820820820803f03f03f00000410410410410403f03f03f00000000000000000003f03f000ffffe186186186186103f03f000fc0ff1c71c71c71c7103f03f000fc0fe9a69a69a69a6903f03f000fc0fe596596596596503f03f000fc0fe1861861861861 else if i < 26 then if i < 25 then 0x3f03f03f03ffcc30c30c30c30c03f03f03f03f01c71c71c71c71c03f03f03f03f00e38e38e38e38e03f03f03f03f00c30c30c30c30c03f03f03f000fecb2cb2cb2cb2c03f03f03f000fdc71c71c71c71c03f03f03f000fcd34d34d34d34d03f03f03f000fcc30c30c30c30c03f03f03f00003cf3cf3cf3cf3c03f03f03f00002db6db6db6db6d03f03f03f00002cb2cb2cb2cb2c03f03f03f00001c71c71c71c71c else 0x3f03ffc000000104104104104103f03f03fffffedb6db6db6db6d03f03f03ffff00c30c30c30c30c03f03f03ffc0ffdf7df7df7df7d03f03f03ffc0fefbefbefbefbef03f03f03ffc0fedb6db6db6db6d03f03f03ffc0fe186186186186103f03f03ffc0fcc30c30c30c30c03f03f03ffc002cb2cb2cb2cb2c03f03f03ffc000e38e38e38e38e03f03f03ffc000d34d34d34d34d03f03f03ffc000c30c30c30c30c else if i < 27 then 0x3ffc000000000514514514514503ffc000000000000000000000003f03fffffc0fedb6db6db6db6d03f03fffffc000c30c30c30c30c03f03ffff03f00c30c30c30c30c03f03ffff000fcc30c30c30c30c03f03ffff00002cb2cb2cb2cb2c03f03ffff00001c71c71c71c71c03f03ffff00000e38e38e38e38e03f03ffff00000d34d34d34d34d03f03ffff00000c30c30c30c30c03f03ffc0fc0fe1861861861861 else 0x3ffc0000fffff7df7df7df7df703ffc0000fffff5d75d75d75d7503ffc0000ffffe186186186186103ffc0000ffffd451451451451403ffc0000fc0ff1c71c71c71c7103ffc0000fc0fe596596596596503ffc0000fc0fe38e38e38e38e303ffc0000fc0fe186186186186103ffc000003fff4d34d34d34d3403ffc000003ffdc71c71c71c71c03ffc000003ffd555555555555503ffc000003ffd4514514514514 else if i < 42 then if i < 35 then if i < 31 then if i < 29 then 0x3ffc0fff0000238e38e38e38e303ffc0fff00000b2cb2cb2cb2cb03ffc0fff0000071c71c71c71c703ffc0fff0000030c30c30c30c303ffc0fc0fffff5d75d75d75d7503ffc0fc0fc0fe186186186186103ffc0fc003ffd451451451451403ffc003ffffff5d75d75d75d7503ffc003ffc0fe186186186186103ffc003f03ffd451451451451403ffc003f000fc000000000000003ffc0000fffffdf7df7df7df7d else if i < 30 then 0x3ffc0ffffffff7df7df7df7df703ffc0fffffffe38e38e38e38e303ffc0ffffc0ff3cf3cf3cf3cf303ffc0ffffc0febaebaebaebaeb03ffc0ffffc0fe79e79e79e79e703ffc0ffffc0fe38e38e38e38e303ffc0ffffc0fe186186186186103ffc0ffffc0fc30c30c30c30c303ffc0ffffc00030c30c30c30c303ffc0fff03ffd75d75d75d75d703ffc0fff03f0030c30c30c30c303ffc0fff000fc30c30c30c30c3 else 0x3ffff03f03ffdc71c71c71c71c03ffff03f03ffd451451451451403ffff03f03ffcc30c30c30c30c03ffff03f03f00c30c30c30c30c03ffff03f000fcc30c30c30c30c03ffff03f00001c71c71c71c71c03ffff03f00000e38e38e38e38e03ffff03f00000d34d34d34d34d03ffff03f00000c30c30c30c30c03ffff000fffff5d75d75d75d7503ffff000fc0fe186186186186103ffff00003ffd4514514514514 else if i < 33 then if i < 32 then 0x3fffffff00002fbefbefbefbef03fffffff00001f7df7df7df7df03fffffff00000f3cf3cf3cf3cf03fffffff00000c30c30c30c30c03fffffff0000030c30c30c30c303ffff03ffffffdf7df7df7df7d03ffff03fffffdc71c71c71c71c03ffff03ffc0fedb6db6db6db6d03ffff03ffc000c30c30c30c30c03ffff03f03fffcf3cf3cf3cf3c03ffff03f03ffde79e79e79e79e03ffff03f03ffdd75d75d75d75d else 0xfc0000000000004104104104104fc0000000000002082082082082fc0000000000001041041041041fc000000000000000000000000003fffffffffffffffffffffffff03ffffffffc0fefbefbefbefbef03ffffffffc0fe38e38e38e38e303ffffffffc000f3cf3cf3cf3cf03fffffff03ffdf7df7df7df7df03fffffff03ffdc71c71c71c71c03fffffff03f00f3cf3cf3cf3cf03fffffff000fcf3cf3cf3cf3cf else if i < 34 then 0xfc000000003ffe0820820820820fc000000003f008208208208208fc000000003f002082082082082fc000000003f000000000000000fc0000000000fc0000000000000fc0000000000030c30c30c30c30fc00000000000238e38e38e38e3fc0000000000020820820820820fc000000000001c71c71c71c71cfc0000000000010410410410410fc000000000000a28a28a28a28afc0000000000008208208208208 else 0xfc0000000fff01e79e79e79e79efc0000000fff01a69a69a69a69afc0000000fff00e38e38e38e38efc0000000fff00b2cb2cb2cb2cbfc0000000fff00a28a28a28a28afc0000000fff008208208208208fc0000000fff002082082082082fc0000000fff000000000000000fc0000000fc0fd0410410410410fc0000000fc0008208208208208fc0000000fc0002082082082082fc0000000fc0000000000000000 else if i < 38 then if i < 36 then 0xfc000003ffff00e38e38e38e38efc000003ffff00b2cb2cb2cb2cbfc000003ffff00a28a28a28a28afc000003f000000000000000000fc0000000ffffeaaaaaaaaaaaaafc0000000ffffda69a69a69a69afc0000000ffffce38e38e38e38efc0000000ffffcb2cb2cb2cb2cbfc0000000ffffca28a28a28a28afc0000000fff03aebaebaebaebafc0000000fff02baebaebaebaebfc0000000fff02aaaaaaaaaaaaa else if i < 37 then 0xfc0000ffffff00a28a28a28a28afc0000fff000008208208208208fc0000fc0ffffca28a28a28a28afc0000fc0fff02aaaaaaaaaaaaafc0000fc0fff01a69a69a69a69afc0000fc0fff00b2cb2cb2cb2cbfc0000fc0fff00a28a28a28a28afc0000fc0fc0001041041041041fc0000fc0000020820820820820fc0000fc0000010410410410410fc0000fc0000000000000000000fc000003fffffca28a28a28a28a else 0xfc003ffc0000000000000000000fc003f03ffff00a28a28a28a28afc003f03f000002082082082082fc003f000ffffca28a28a28a28afc003f000fff02aaaaaaaaaaaaafc003f000fff01a69a69a69a69afc003f000fff00e38e38e38e38efc003f000fff00a28a28a28a28afc003f00003f004104104104104fc003f000000020820820820820fc003f000000010410410410410fc003f000000000000000000000 else if i < 40 then if i < 39 then 0xfc003ffc0000ff1c71c71c71c71fc003ffc0000ff0c30c30c30c30fc003ffc000003cf3cf3cf3cf3cfc003ffc000003aebaebaebaebafc003ffc0000038e38e38e38e38fc003ffc0000034d34d34d34d34fc003ffc0000033cf3cf3cf3cf3fc003ffc0000032cb2cb2cb2cb2fc003ffc0000031c71c71c71c71fc003ffc0000030c30c30c30c30fc003ffc0000020820820820820fc003ffc0000010410410410410 else 0xfc003ffc0fff00a28a28a28a28afc003ffc0fc0ff0c30c30c30c30fc003ffc0fc0038e38e38e38e38fc003ffc0fc0032cb2cb2cb2cb2fc003ffc0fc0031c71c71c71c71fc003ffc0fc0030c30c30c30c30fc003ffc003fff0c30c30c30c30fc003ffc003f038e38e38e38e38fc003ffc003f034d34d34d34d34fc003ffc003f032cb2cb2cb2cb2fc003ffc003f030c30c30c30c30fc003ffc0000ff4d34d34d34d34 else if i < 41 then 0xfc003ffff03f030c30c30c30c30fc003ffff000ff0c30c30c30c30fc003ffff000038e38e38e38e38fc003ffff000034d34d34d34d34fc003ffff000032cb2cb2cb2cb2fc003ffff000031c71c71c71c71fc003ffff000030c30c30c30c30fc003ffc0fffffaebaebaebaebafc003ffc0fff03efbefbefbefbefc003ffc0fff03befbefbefbefbfc003ffc0fff03aebaebaebaebafc003ffc0fff030c30c30c30c30 else 0xfc0fc0000fff01a69a69a69a69afc0fc0000fff00e38e38e38e38efc0fc0000fff00b2cb2cb2cb2cbfc0fc0000fff00a28a28a28a28afc0fc000003fff4d34d34d34d34fc0fc000003ffdc71c71c71c71cfc0fc000003ffd6596596596596fc0fc000003ffd4514514514514fc0fc0000000012492492492492fc0fc0000000000000000000000fc003fffffff03aebaebaebaebafc003fffffc0030c30c30c30c30 else if i < 49 then if i < 45 then if i < 43 then 0xfc0fc0fc0ffffde79e79e79e79efc0fc0fc0fff00a28a28a28a28afc0fc0fc003ffd4514514514514fc0fc0fc003f000000000000000fc0fc003fffffde79e79e79e79efc0fc003ffff00a28a28a28a28afc0fc003f03ffd4514514514514fc0fc0000fffffefbefbefbefbefc0fc0000ffffdf7df7df7df7dffc0fc0000ffffde79e79e79e79efc0fc0000ffffd4514514514514fc0fc0000ffffca28a28a28a28a else if i < 44 then 0xfc0fc0ffffff00f3cf3cf3cf3cffc0fc0ffffff00b2cb2cb2cb2cbfc0fc0ffffff00a28a28a28a28afc0fc0ffffff0030c30c30c30c3fc0fc0ffffc00030c30c30c30c3fc0fc0fff03ffd75d75d75d75d7fc0fc0fff03f0030c30c30c30c3fc0fc0fff000fc30c30c30c30c3fc0fc0fff0000238e38e38e38e3fc0fc0fff0000134d34d34d34d3fc0fc0fff00000b2cb2cb2cb2cbfc0fc0fff0000030c30c30c30c3 else 0xfc0ffffc0000ff0c30c30c30c30fc0ffffc0000034d34d34d34d34fc0ffffc0000032cb2cb2cb2cb2fc0ffffc0000031c71c71c71c71fc0ffffc0000030c30c30c30c30fc0fff000ffffde79e79e79e79efc0fff000fff00a28a28a28a28afc0fff00003ffd4514514514514fc0fc0fffffffdf7df7df7df7dffc0fc0fffffffcb2cb2cb2cb2cbfc0fc0ffffff02baebaebaebaebfc0fc0ffffff01b6db6db6db6db else if i < 47 then if i < 46 then 0xfc0ffffff0000030c30c30c30c3fc0ffffc0fffffefbefbefbefbefc0ffffc0fffff4d34d34d34d34fc0ffffc0fff03aebaebaebaebafc0ffffc0fc0030c30c30c30c30fc0ffffc003fffcf3cf3cf3cf3cfc0ffffc003fff6db6db6db6db6fc0ffffc003fff5d75d75d75d75fc0ffffc003fff4d34d34d34d34fc0ffffc003fff0c30c30c30c30fc0ffffc003ffd4514514514514fc0ffffc003f030c30c30c30c30 else 0xfc0fffffffffffffffffffffffffc0fffffffff03befbefbefbefbfc0fffffffff00b2cb2cb2cb2cbfc0fffffffc0033cf3cf3cf3cf3fc0ffffff03fff7df7df7df7df7fc0ffffff03fff4d34d34d34d34fc0ffffff03f033cf3cf3cf3cf3fc0ffffff000ff3cf3cf3cf3cf3fc0ffffff00003befbefbefbefbfc0ffffff000037df7df7df7df7fc0ffffff000033cf3cf3cf3cf3fc0ffffff000030c30c30c30c30 else if i < 48 then 0xfff000000ffffe1861861861861fff000000ffffca28a28a28a28afff000000fff02aaaaaaaaaaaaafff000000fff00e38e38e38e38efff000000fff00b2cb2cb2cb2cbfff000000fff00a28a28a28a28afff000000fc0ff1c71c71c71c71fff000000fc0fe9a69a69a69a69fff000000fc0fe38e38e38e38e3fff000000fc0fe1861861861861fff000000000028a28a28a28a28fff000000000000000000000000 else 0xfff03f000fff00a28a28a28a28afff03f000fc0fe1861861861861fff03f000fc0000000000000000fff000fc0ffffebaebaebaebaebfff000fc0fff00a28a28a28a28afff000fc0fc0fe1861861861861fff00003fffffebaebaebaebaebfff00003ffff00a28a28a28a28afff00003ffc0fe1861861861861fff000000fffffbefbefbefbefbfff000000ffffefbefbefbefbeffff000000ffffebaebaebaebaeb else if i < 53 then if i < 51 then if i < 50 then 0xfff03f03ffff00e38e38e38e38efff03f03ffff00c30c30c30c30cfff03f03ffff00a28a28a28a28afff03f03ffc0fedb6db6db6db6dfff03f03ffc000c30c30c30c30cfff03f03f03f00c30c30c30c30cfff03f03f000fcc30c30c30c30cfff03f03f00002cb2cb2cb2cb2cfff03f03f00001c71c71c71c71cfff03f03f00000e38e38e38e38efff03f03f00000c30c30c30c30cfff03f000ffffebaebaebaebaeb else 0xfff03ffc0fc0030c30c30c30c30fff03ffc003f030c30c30c30c30fff03ffc0000ff0c30c30c30c30fff03ffc0000038e38e38e38e38fff03ffc0000034d34d34d34d34fff03ffc0000031c71c71c71c71fff03ffc0000030c30c30c30c30fff03f03fffffefbefbefbefbeffff03f03fffffce38e38e38e38efff03f03ffff02ebaebaebaebaefff03f03ffff01e79e79e79e79efff03f03ffff00f3cf3cf3cf3cf else if i < 52 then 0xfff03ffff00003cf3cf3cf3cf3cfff03ffff000030c30c30c30c30fff03ffff00000c30c30c30c30cfff03ffc0fffffbefbefbefbefbfff03ffc0fffff1c71c71c71c71fff03ffc0fff03aebaebaebaebafff03ffc0fc0ff9e79e79e79e79fff03ffc0fc0ff5d75d75d75d75fff03ffc0fc0ff3cf3cf3cf3cf3fff03ffc0fc0ff1c71c71c71c71fff03ffc0fc0ff0c30c30c30c30fff03ffc0fc0fe1861861861861 else 0xffffc0000fc0fe1861861861861ffffc000003ffd4514514514514fff03fffffffffffffffffffffffff03fffffff03efbefbefbefbefff03fffffff00e38e38e38e38efff03fffffc0ffdf7df7df7df7dfff03fffffc0ff1c71c71c71c71fff03fffffc003cf3cf3cf3cf3cfff03ffff03f03cf3cf3cf3cf3cfff03ffff000ffcf3cf3cf3cf3cfff03ffff00003efbefbefbefbefff03ffff00003df7df7df7df7d else if i < 55 then if i < 54 then 0xffffc0fffffffffffffffffffffffffc0fffffffebaebaebaebaebffffc0ffffff00b2cb2cb2cb2cbffffc0ffffc0fe38e38e38e38e3ffffc0fff0000030c30c30c30c3ffffc0fc0ffffe1861861861861ffffc003fffffca28a28a28a28affffc0000ffffffffffffffffffffffc0000fffff5d75d75d75d75ffffc0000ffffebaebaebaebaebffffc0000ffffde79e79e79e79effffc0000fff00a28a28a28a28a else 0xfffffffff00000f3cf3cf3cf3cffffffffc0fffffffffffffffffffffffffc0fffff5d75d75d75d75fffffffc0fc0ff1c71c71c71c71fffffffc003fff4d34d34d34d34fffffffc0000030c30c30c30c30ffffff03fffffffffffffffffffffffff03fffffde79e79e79e79effffff03ffff00e38e38e38e38effffff03f03ffdc71c71c71c71cffffff03f00000c30c30c30c30cffffff000ffffd4514514514514 else if i < 56 then 0xffffffffffff03fffffffffffffffffffffffff00f3cf3cf3cf3cfffffffffffc0fffffffffffffffffffffffffc0ff3cf3cf3cf3cf3ffffffffffc00030c30c30c30c3fffffffff03fffffffffffffffffffffffff03fffcf3cf3cf3cf3cfffffffff03f00c30c30c30c30cfffffffff000ff0c30c30c30c30fffffffff00003ffffffffffffffffffffff00003cf3cf3cf3cf3cfffffffff000033cf3cf3cf3cf3 else 0xffffffffffffffefbefbefbefbeffffffffffffffdf7df7df7df7dffffffffffffffbefbefbefbefbffffffffffffff7df7df7df7df7fffffffffffffefbefbefbefbeffffffffffffffdf7df7df7df7df

def wireRaw (i : ℕ) := field (wireRawChunk (i / 12)) 108 (i % 12)

def wireOf (i : ℕ) : W := BitVec.ofNat 108 (wireRaw i)

def disp4Chunk (i : ℕ) : ℕ :=
  if i < 10 then if i < 5 then if i < 2 then if i < 1 then 0x9e0500d000bbbada0e00b400 else 0x83b891002caf06ab3200 else if i < 3 then 0xd500cd0002321f000000aa93 else if i < 4 then 0xd526000f2321009f3b3e0090 else 0x170600000000e300000a else if i < 7 then if i < 6 then 0xc7c50000a251001100000006 else 0xb7ad0300000001ca01b100a3 else if i < 8 then 0x4e0097ba008b8d7c00970d06 else if i < 9 then 0x5e98e4ce0000a8000000 else 0x3088a001d0002b8a2970043 else if i < 15 then if i < 12 then if i < 11 then 0x7f0000019c0008e400036500 else 0x44b3dd00e600e600000000 else if i < 13 then 0x2000000004e009985000003 else if i < 14 then 0xd000b000007000100000000 else 0x3da7100000085000600c7 else if i < 17 then if i < 16 then 0x7d0000b6ce00000000b8 else 0x5aca000000c6000900050a00 else if i < 18 then 0x14700000000002701000e00 else if i < 19 then 0x710100a98c00000003e036 else 0x7e2f

def disp4 (i : ℕ) := field (disp4Chunk (i / 12)) 8 (i % 12)

def val4Chunk (i : ℕ) : ℕ :=
  if i < 10 then if i < 5 then if i < 2 then if i < 1 then 0x754f25bd9f2bd5d93c97395caf59988a4f99f2bd61f9992b67caf587e664c19f2bd666229246d4af59b8f22299f5ed6652293067caf587e664919f2bd5148051c67caf587cf25cd9f89d64a29d1c67caf5 else 0x9988a4e5a72bd61f9992469caf587e66471a72bd6632291c69caf587e4a5cd9f2bd61f4e17367caf587d315cd9f2bd5d54517367caf5794f22292c8395ca5357167caf5728f22792c83961c3c97395caf5 else if i < 3 then 0x729622ad1c67d64a2293967caf5728fb5cdc02bd5da5888a4e59f5794f227a578396648751c67caf587cf25cdc02bd5d53c973700af587cf2491c02bd6662291c6e4af59908a471b52bd66e3c88a95e0e5 else if i < 4 then 0x9908a471df2bd5ca8fdf9470af5794f22551c83961f45173700af587cf25cdc62bd61f4512467caf5728fb5c59f2bd5ca3c97267cd35729042551c8395ca4617367caf59908a4e59f2bd61f3c91c69cd35 else 0x87cf25cd9f5ed5ca54c8a95e0e5539ca472812bd5ca3c972954af59908a9b59f2bd5ca4108a954af5794f222a552bd5ca3c89e92caf59948a4723e2bd61f9991c7e0af5878f2471f82bd5ca43c8a95e0e5 else if i < 7 then if i < 6 then 0x9948a471a72bd61c3c91c69caf5999622291c6ed5d53c89e95caf57290822a572bd61e3c97167caf5794fb22a572bd5ca5888a4b1b5572a3f22a562bd666588a74719f5780f222a562bd4f28751c77caf5 else 0x999623011c67d61f9991c69cb75754fb5ce572bd5ca5894c4720e53ca1d471c02bd5ca4109e95e0e5878f24719f2fd5ca3ed6f67caf5728fb5ce572bd5ca3c97395cc85780f25ce572bd61f3c97377caf5 else if i < 8 then 0x9bcf22299fa6d5ca4517367cbb587cf2471c02dd66629d1c69caf59988a471b52dd6662293967cb75729612291c8355caa09fa470af5728f222a532ed61e3c91c67cb75729622553967d5ca8fd7395caf5 else if i < 9 then 0x728f25c59f2fd5ca3c97395cbb598c8a4719f2dd5ca3c89e95cbb587cf24919f34d6283c88a4720d57290422a572ed5ca3ed7395cbb5794f222a572ed5e53c88a92caf5728f25cdc02ed61f9991c8f8af5 else 0x728954719f5815d53c88a958af59948a4719f5815ca3c895472095728954719f57166e3c88a954af57688a4719f5715ca3c97367cd957293122a552bd61f3c973700d35728fb5cd9f34d5ca3c95267cd35 else if i < 15 then if i < 12 then if i < 11 then 0x768f22291c8315ca3c97267d7b57288a4b19f5815ca5311c67d605769622551c83966629d1c67cb75728f254a5783961f4517367caf587e664919f2dd61f3c91c67cd85728f2342578395ca3c88a4b2095 else 0x87d145cd9f34d6665888a471df57296229d2c67d6665888a471b55729613011c67d5ca5311c8f8af5769622292c83961c3c92467caf59948a4919f2bd5da588a74719f57288a4c19f5815e03c88a4720c5 else if i < 13 then 0x8a0f22297c67d5ca5888a5019f59996229d3967d6665888a4e59f58a4f222a9867d5ca3c97167cbb59be40228af92561e3c91c69caf5779622291c8395ca5848a4e59f5729532293967d61f9991c67cc75 else if i < 14 then 0x9996222a6d67d61f3c91c710af5729612297c67d4f28051c67cd35999628051c67d5ca3c952700af5539ca5f59f54566629d2467caf5728f25ce572fd5d54108a95caf572a40a211c2bd61f9996f67caf5 else 0x3ca1d4719f34d5d53c97367cd35729315c99f2bd5da4108a4720e5728f23011c8355ca3c89e4720d5999622291c8096665888a4e5b55729622551c6d55da5888a471b55729532291c6d56973c88a5f59f5 else if i < 17 then if i < 16 then 0x87cf25cd9f34d5ca588954720e598d622291c8395ca3c89e95e0e57294d471f82bd6293c9fa472005781622291c8395d53c97395caf587e664719f2fd5da5888a4720e5999622297c67d5ec3c88a4720e5 else 0x7294d5ce572bd5ca5888a4c20e5794f22291c8095eb3c88a95caf572962229358395ca3c8954720c587d144719f2dd4f28751c67e275794f222a57839666588a7471b55729627e51c8395ca3c8a24720e5 else if i < 18 then 0x8a0f222a578395ca3c97395e095768f22791c8395ca588954b20e57296129d1c67d5ca3ec8a94caf587cf25ce4b2bd61f9991c67d5c5729042292c83961f4511c69caf5729145c99f2bd5ca3c88a95a0c5 else if i < 19 then 0x728f2302578395ca4c48a95e0e5729622292c8395ca3c9f94720c57950422a578395e53c88a4720d53c88a9b59f89d5d53c97395cbb5729042291c8095ca4108a95e0e587e664719f2dd666588d24719f5 else 0x1ca3ec8a958af57296222a538395ca3ec9e95caf5

def val4 (i : ℕ) := field (val4Chunk (i / 12)) 54 (i % 12)

def pick4 (h : ℕ) := (h * 311 % 10000019) % 231 + disp4 (h % 231)

def db4 (i : ℕ) : List W :=
  let a := val4 i
  unpack wireOf 10 (a % 16) (a >>> 4)

def allow4 (ws : List W) := !(matchTable 231 db4 pick4 ws)

def disp5Chunk (i : ℕ) : ℕ :=
  if i < 68 then if i < 34 then if i < 17 then if i < 8 then if i < 4 then if i < 2 then if i < 1 then 0xc00220801ae6000c0000000f4c00107 else 0x850006a2f640780600000000202 else if i < 3 then 0x201007e0f0000014aa0016a00000000 else 0x25e0000a376c01800b129b803005 else if i < 6 then if i < 5 then 0x15f8003725c57c000000222000003aa else 0x100000000000ccf37200800000 else if i < 7 then 0x3e60000014d00128c0000000000000000 else 0x99800000de0005d90020000018b else if i < 12 then if i < 10 then if i < 9 then 0xca60000559b2aa002d5a60a0a10800000 else 0x400536000002bf00000000000399 else if i < 11 then 0x1dcc650091080000000000001000 else 0xab80000104b67c01000a116dabd001 else if i < 14 then if i < 13 then 0xa7c0002e22f0020025800000800032800 else 0x3e20000000000a0000080000000000000 else if i < 15 then 0x4e40000000000a00c86800000002f3000 else if i < 16 then 0x450c0000000000200000000 else 0x1bce00004001672bd46400002d92 else if i < 25 then if i < 21 then if i < 19 then if i < 18 then 0x6e601c0000000009c0028a6fa00004005 else 0x163003652004b147edf200000000565 else if i < 20 then 0x582bc80014d0000000000100000000006 else 0x1f300000d7e0000000004e801 else if i < 23 then if i < 22 then 0x878000e8800b510c01e86d82200001000 else 0x3f6000000000000029d80000000000001 else if i < 24 then 0x1af000b4c43001000008000e4555 else 0x91600c0026b0000000000000002a2aa4a else if i < 29 then if i < 27 then if i < 26 then 0x1ae000000070000a14f96500200001000 else 0x400800066a34000005e700200000000 else if i < 28 then 0x51a00000003000000000004c728800283 else 0x9ca0008800e000de0009160000000d203 else if i < 31 then if i < 30 then 0x6000005b2000f00001d700199237a7a else 0xae80147b00000000800000b9e00001000 else if i < 32 then 0x1e400000000b300000b00000000250 else if i < 33 then 0x11c00272001390001f56d5338ff000 else 0x10f0006667f2578000000013a637 else if i < 51 then if i < 42 then if i < 38 then if i < 36 then if i < 35 then 0x1a2800000002650049b801800093 else 0xb4350c02000000b20d016e000000002c5 else if i < 37 then 0x136428004102f200000154002000004d7 else 0x2e000d58005f399800002000b0c00000 else if i < 40 then if i < 39 then 0x1434005100020000000028600214800 else 0x18000020000000025000000022001 else if i < 41 then 0x7fb25006000040004ca00800800 else 0x19b0031ee00000800000000001b5 else if i < 46 then if i < 44 then if i < 43 then 0x8b4000000034300100036862c7a574 else 0x126c714d20008c4000009be00000000 else if i < 45 then 0x8600000000057e1c55e0040005b000321 else 0x4bf00000001000000d7400000 else if i < 48 then if i < 47 then 0x680000000012100000034b000d9800002 else 0x4020000000458370c0000201200000000 else if i < 49 then 0x7c4000018000080000056700097c01d01 else if i < 50 then 0xe5300000c0000019792c0015a else 0x809970002eb004508000000000000404e else if i < 59 then if i < 55 then if i < 53 then if i < 52 then 0x59e02d78001486000003b2000000c5000 else 0x191c000020000082b800c1a00000000 else if i < 54 then 0x4000ee14f0078a40033f0f770c00002 else 0x9213a0000000d000001524fb000 else if i < 57 then if i < 56 then 0x11d380800000000802c14000f2800 else 0x6fa3c800000000d540000000016cc7004 else if i < 58 then 0x2000000000ff294000000000086a011 else 0xbb6000000070000018c215000000012f5 else if i < 63 then if i < 61 then if i < 60 then 0x1b20050005300000000595803000 else 0x2004018000000060e852000000005f3 else if i < 62 then 0x3c1732eb9ea0000071a33100000400001 else 0x32d000000005ad0000698b000 else if i < 65 then if i < 64 then 0x4217b9ed0000ee0186e9b600200000368 else 0x1714d4000028ab96c000035d200003800 else if i < 66 then 0x4003198000000000000022b55cc0ce9 else if i < 67 then 0x2984950d53700000478ab4b74000015a7 else 0x300002000000000000024d2dbcef else if i < 102 then if i < 85 then if i < 76 then if i < 72 then if i < 70 then if i < 69 then 0x2680040000000400000000003254000f8 else 0x7200280000001404800 else if i < 71 then 0x2dd8000010009c9fd0000000032e082 else 0x71a000000020040014c000000010004b3 else if i < 74 then if i < 73 then 0x10000001c3a7b40000000000000000 else 0x35568000020000100300000401000 else if i < 75 then 0x32480000008c00000000002a1b1b else 0x4e20000000768b42d7180000200000647 else if i < 80 then if i < 78 then if i < 77 then 0x784000000150040000008600000404000 else 0x8a7f814003190109a002b81 else if i < 79 then 0x9221a00000068e001b68000000000031e else 0xc542cc00000ca2d3dc3497 else if i < 82 then if i < 81 then 0x9800000000000002634437000004039d8 else 0x802638000002ca003091d1db7 else if i < 83 then 0x1000000000000eba943ba4aa00000000 else if i < 84 then 0x84270cb5800000790118000000011a000 else 0x40000000000600000101003274005da else if i < 93 then if i < 89 then if i < 87 then if i < 86 then 0x5de004000000020000180000000006000 else 0x7300080101d1cc0000003d6ec0026e else if i < 88 then 0x12d09a00069c00656b2a00002000 else 0x1a0029b000001552ad8060000005159d else if i < 91 then if i < 90 then 0x38d24880080014b8002e400000000 else 0x214aec8009b741c3ebad1b6001fe001 else if i < 92 then 0x4000000d46500340025971e00000000 else 0xa48004000056080000200000000000000 else if i < 97 then if i < 95 then if i < 94 then 0x2778019a4000d30009d400003801 else 0xb4600022b6a0001100000100000dd5800 else if i < 96 then 0x17a0005190020010a800b2200000000 else 0xb2200000000000acc4080000001001000 else if i < 99 then if i < 98 then 0x80003b4041b02b0001d200000291 else 0x8002a62e1ba800 else if i < 100 then 0xa34001ced830760000000093400004a80 else if i < 101 then 0xbe25c005001440ba80017287853928 else 0x312614003d80000000000000001000000 else if i < 119 then if i < 110 then if i < 106 then if i < 104 then if i < 103 then 0x9734e80000000000000001 else 0xac2d745f0000005661580000000000000 else if i < 105 then 0x17a8060000000036f0014740006a else 0x8a80009a00052a045ec5380003980000d else if i < 108 then if i < 107 then 0x8002a18000000080d00700000058000 else 0x2f3924002102de000000060014c800000 else if i < 109 then 0x1be000000003860006d00000000800000 else 0x23058000007594ec001cf0025cc00000 else if i < 114 then if i < 112 then if i < 111 then 0x2ad0aa8c802804000006523c0 else 0x97820006120013d6a710e5ac00000000 else if i < 113 then 0x9780002e80085000000800000726b1000 else 0x600000637acd4c40036a000000efde2 else if i < 116 then if i < 115 then 0x59d34400000002000000005dc else 0x69000000a4936e0000080300175000002 else if i < 117 then 0x200000000000000f32ce000664000ff else if i < 118 then 0x40005230000480061c44200190a0e else 0xd3a798010011d800000 else if i < 128 then if i < 123 then if i < 121 then if i < 120 then 0x696a64800002de2d4002000c6800000 else 0x7f0bb0041b47ee0067d80006800005000 else if i < 122 then 0x8480011d000caa2115000018400215 else 0x75a35aab80034000000000004006872ff else if i < 125 then if i < 124 then 0xf226860399e00000000 else 0x5a8004c8800a86001e5000000000002d0 else if i < 126 then 0x24271800000000eac0053eb0447404000 else if i < 127 then 0x2800000000001ce005a524aa13a68 else 0x34000000000034d8006081460140055c else if i < 132 then if i < 130 then if i < 129 then 0x4401119800adc000000000b000000000 else 0x3d90040029300100201572000 else if i < 131 then 0x40a0090040024100000600273cd5 else 0x1f000cbe00640000 else if i < 134 then if i < 133 then 0x6001c511d000011d82d7000000d4000 else 0x17180002afb803800a1e00800000 else if i < 135 then 0xc6a000000c50020000000000200800000 else if i < 136 then 0x18000000000000000554f64c00308 else 0x12080000055e18400800

def disp5 (i : ℕ) := field (disp5Chunk (i / 12)) 11 (i % 12)

def val5Chunk (i : ℕ) : ℕ :=
  if i < 68 then if i < 34 then if i < 17 then if i < 8 then if i < 4 then if i < 2 then if i < 1 then 0x98e402291c67caf687cf24719f34c16687e66471a72bc166768f22551c838af6999622291c67c4c6728f25112c67caf6728f222a562bd9c6870f24719f2bc16698c8a4719f2bc16672a362291c6d4af6728f22291c67caf6728f22291c8083d6 else 0x728f25111c67e046794f22299f2bd1067861f3c92467caf6768f22551c67cc46002665888a471b55728f22299f468af687d1432d1c67caf6728f22291c2ed986728f222a578383d6728f22556b67caf6728f23411c67cd36729382291c77caf6 else if i < 3 then 0x7288a4719f5702c6728f25ce572bc286728f25ce572ec1f69996229c8a4719f6728f22552c67caf6729042299f2bd1967550a2291c67caf6728fb5ce572bc1f6729482291c6d4af6728f22791c67cc467290422a572bc1f6728f22291c67cbb6 else 0x728f22293967e046729622291c838396728f25ce572bc396728f222a4d2bc396764f22291c67caf67288a4719f560356728f22292b67cbf6748f22291c67cd369748a4719f2bc356794f22291c8382c6728f25ce572bc216728f22291c8242c6 else if i < 6 then if i < 5 then 0x769622291c67c4c69988a4719f2dc4c6728f25cc8a95cbb6728f22292c8383d6728f27e91c2be006728f2229248e8af687dca3c91c69caf6728f22291c69cd36729562297c67caf6728f22551c67e046728f222a572ec3d672a362292c67caf6 else 0x3c88a4719f89dc76999622293967c4c6728f25111c67cd36728f22293977caf6729622292c67c4c687e293c9fa4720e6729142291c8e8af69996229d1c67c4c685cf232d1c67caf63ca014719f2bc5f685d482296b67caf6999ca2291c67cb76 else if i < 7 then 0x85cf22297c67caf6729042291c67caf687d143051c67caf6728f22292c7d0af67294d7e91c838af685cf22296b7d0af6728f227a578383d6729482291c67c5b6729622291c67c596974fb2291c67caf6728f25ce572bc84687cf2471c02bc166 else 0x85d042291c67caf6728f25cd9f34c1f6728f22291c7d2046728f25cc8a700d36974f229d1c67caf687cf25cd9f2bc5f67290a2291c6b4af6728f22791c67cbb69b8f222a5767caf6998f229d1c67caf6999412293967caf6728f22291c808af6 else if i < 12 then if i < 10 then if i < 9 then 0x3c9f04719f2bc72687cf24719f2dc5f687e2c3c91c67cb76748f22292467cb7687d145cd9f2bc5f6728f25111c69caf67290422a578383d6729562291c808af6768f22291c67caf685cf22291c808af69be662291c69caf6728f22293967cd36 else 0x754f22291c67caf6754f24719f2bc816728f222a3a2bc6e674a362291c67caf672a362291c67cd3687cf25cd9f2bc6e6728f27c11c69caf687dca3c973700af6729624288a471b5687cf25cd9f34c5f6728fb2291c67cc4672a3f2291c67caf6 else if i < 11 then 0x728f22292469cb76728f2471a72bc846728f22293967c9a6728f22293969caf6728f22291c67d586728f22551c69caf6729482291c67cd3687cf25cc8a67cd3687dca3c91c8f8af67290432d1c67caf6794f22291c6b4af6729382293967caf6 else 0x7288a4720e2bcef6754f25cc8a95caf685cf22291c67d586729482291c67d586729042291c67ca36768f232d1c67caf6728f24719f2fc876728f24719f2ec876728f2471f82bc876998f222a6d67caf6729623c88a471bb6878f24719f2bc876 else if i < 14 then if i < 13 then 0x728f23011c67cac6728f229d1c67cac6729612291c67cac6728f25111c8f8af672a405311c67caf6728f27c13967caf6728f25113967caf6794f22291c67cac6729622291c8382c6729532291c67c4c672a362291c69caf68d88a4719f2bc726 else 0x728f27c11c2bd9c67288a4719f2bcf0699a402293967caf69948a4719f2bcef67288a471a72bcec672a362291c67e0b67688a4719f2bce76728f227a57838af672a365111c67caf6728f22291c6b4af67288a4c19f2bcef6728f22291c834ac6 else if i < 15 then 0x728f222a578390067290422a57838af6728f32551c67caf6754f22791c67caf6728f22299f34d006728f2229c02bd006728f22291c6d4b767288a4719f580ef67288a4723a2bcef6728f229d396d4af6728fb5cd2867caf6728f22553967caf6 else if i < 16 then 0x728f22291c67cad6728f22791c67d58687cf22299f2bd196769ca5888a4720e6974f22299f2bd196794f22299f2bd19687dca3c91c7e0af672a362551c67caf6975142291c67caf60021f4517367caf5539ca2291c67d5c6728f22799f2bd106 else 0x87cf25cd1c700af6754f22291c2bd9c687dd23c91c67cb76728f229d1c67cbb6728f22291c2bd9c6728f22297d67d516728f22299f561196729623c88a471b56728f22292c838c46728f25111c7d0af6728f22299f34d196755042291c67caf6 else if i < 25 then if i < 21 then if i < 19 then if i < 18 then 0x999622291c67db164508a4719f2bdb16728f22551c2bd9c6728f22291c67cbf672a3f2291c2bd9c6728fb2291c2bd9c6728f22293567caf672a362291c2bd9c6729042291c67d586728f22296b67cb7698d622291c67caf6780f22291c2bd9c6 else 0x728f22291c854af63c88a4e59f2bdbc6729145ccc167caf6728f222a532bc1f6728f2229397d0af60021f9992467caf5728f22791c6b4af6994f22291c67caf67b0f22291c67caf6729622291c6d42c6794f22291c8e8af6729142291c67cc46 else if i < 20 then 0x3c88a471b52bdc763c88a9b59f2bdc768a5ca3c88a5f19f6728f25119f2bc6e6729042291c6b4af672a362291c7d0af63c88a4e59f2bdc763c88a4719f2bdc76002665888a4e59f5728f27e89e4720e6728f222a57274af6728f222a6d67caf6 else 0x778f22291c69caf6588f22291c67dc763c88a7211c67caf6984f25111c67caf67861f3c97395caf6780f22551c67caf63c88a4719f811c76738f22291c700af6769622291c8382c6729622292c838af63c88a4719f34dc769988a471a72bc4c6 else if i < 23 then if i < 22 then 0x999622291c67c4e67288a4b19f2bcef6729622291c67db46729313411c67caf6728f229d1c808af6728f222a578383e687e664719f2bc17672a402291c2be4969bcf22299f2be496764f22291c67cbf68a4f22291c67e006728f22291c8e8af6 else 0x729612291c67caf687cf25cd9f34caf6728f25cd1c67cc8685cf22291c8e8af6984f22291c8f8af6768fb2291c67caf6728f25ce572ecaf6729623c88a471df6754f22291c6b4af685d482291c7d0af687e664719f2dcaf6728f22291c839036 else if i < 24 then 0x729482291c7e0af67288a4719f2dcec687cf22291c67cd36729623ca014719f687cf25cdc067caf6728f2229246d4af6728f22291c678af687cf25cd9f18caf6769622291c8399f6768f229d1c67caf6728f22291c8e8bb6728f27c12867caf6 else 0x98cf22291c67caf6984f22291c67caf6974f22291c67caf685cf22291c67caf6728f22291c718af6729624288a4e59f67a8f22291c67caf63c9c92291c67caf6778f22551c67caf6728f232d1c700d36728f25551c67caf6754f229d1c67caf6 else if i < 29 then if i < 27 then if i < 26 then 0x728f25cc2595caf6728f25ad9f2bc286769042291c67caf6728f25c59f2bc876728f229d1c67d586764fb2291c67caf6728f27c11c700af6728f222a57470c86754fb2291c67caf6729042791c6b4af6728f222a552bd196a5cf22291c67caf6 else 0x729042291e67caf687dca3c96f67caf67290f2291c67caf687d142291c700af67291432d1c67caf67290d2291c67caf69750a2291c67caf685d0a2291c67caf6998f23011c67caf67690a2291c67caf69b9042291c67caf6795042291c67caf6 else if i < 28 then 0x87d382291c67caf6729042291c8e8af6729382291c67caf687d312291c67caf6728f229d1c6b4af685d142291c67caf6728f222939700af687e4a2291c67caf6749142291c67caf6728f25cdc02bc1f6728f22291c67cac687dca4719f2bcef6 else 0x72a362291c700af6975482291c67caf686d482291c67caf6728f22292467e046728f222a8967caf6794f22291c67ca3685d482291c67caf6795482291c67caf685cf22291c67cac6769482291c67caf6755482291c67caf6729482291c67caf6 else if i < 31 then if i < 30 then 0x72a642291c67caf687e664719f2bc3569be4a2291c67caf6728f22291c8384a672a432291c67caf6998a74719f2bc166796362291c67caf6728f222a4d67e04687cf24719f2bc686756362291c67caf68a1532291c67caf67294d2291c67caf6 else 0x754f22551c67caf6728f25cd1c2bd9c69908a4719f2bdc763c8a74719f2bdbc63c88a471c02bdc76748f22551c67caf6728f22551c67caf6781622291c67caf6754f22291c8e8af6779622291c67caf6728f22551c67cb767288a471a72bcef6 else if i < 32 then 0x728fb2291c67cbf6768f22791c67caf6729323ec8a95caf6728fb2293567caf6769142291c67caf6729622551c67caf6729623c88a4e59f6728f27e88a472096785e53c88a4720e6729444719f2bcef6728fb2551c67caf685cf22551c67caf6 else if i < 33 then 0x728f22292467cd36755142291c67caf6728954719f2bce76728fb5cd9f2bc5f687dca3c92467caf6794f22291c6ecaf6728f22791c67cac6728f24808a67cd36795042791c67caf6729042791c67caf6974f22791c67caf6998f2229396d4af6 else 0x748f22292467caf6729622293967c2c6728f22291c81039686cf22291c7e0af6748f222a4d67caf6794f229d1c67caf672a362791c67caf6729482791c67caf67288a4723e2bcef67290a2791c67caf672a454108a95caf6728954719f2bcef6 else if i < 51 then if i < 42 then if i < 38 then if i < 36 then if i < 35 then 0x87dca3c92b67caf67295629d1c67caf6728b53c8a74719f6974f22291c67cbb6999d22291c69caf687dca3c91c67cc767291429d1c67caf67290429d1c67caf6728f25312c67caf6729622293067caf672cf229d1c67caf6729082291c67caf6 else 0x728f23011c67caf6728f222a4d69caf67290a2296b67caf6728fb2291c8e8af6878f22291c67caf6728f222a578385b6768f22291c8383d6780f25cd1c67caf6728f22292469caf69993229d1c67caf69996229d1c67caf672a3629d1c67caf6 else if i < 37 then 0x728fb32d1c67caf6974f232d1c67caf6794f232d1c67caf6728f25112467caf6754f232d1c67caf6729142291c6b4af6748f232d1c67caf6728f22552c838af69be662292467caf6728f232d1c67caf67290f3011c67caf6728f229d1c8e8af6 else 0x728f22293f67caf672a462291c67caf67290f2293967caf6728f22292b69caf6794f23411c67caf6728f22251c67caf6728f27c24d67caf6728f23411c67caf672a3632d1c67caf6728f22291c69cc767294832d1c67caf6728f27c12467caf6 else if i < 40 then if i < 39 then 0x72932588a74719f6974f25111c67caf685cf25111c67caf6748f25111c67caf6728f25111c67caf6729383491c67caf68a0f22791c67caf672a404108a95caf67290a2291c67e046728f22291c910af6728f23491c67caf6728f232d1c67cc46 else 0x729620cc8a4720e6729625311c67caf6794f22296b67caf6974f22291c67d7b6728fb22a572bc3d672a4a5cc8a67caf6785ca3c89e4720e6999322293967caf698cf25311c67caf6728f25311c67caf6729145111c67caf6998f22291c808af6 else if i < 41 then 0x728fb7c11c67caf6728f22296f7e0af6794f27c11c67caf6754f27c11c67caf6738f22291c67cd36728f22292867cb76748f27c11c67caf6728fb2292867caf6768f222a5367caf6728f25c91c67caf6728f22291c6d4af6729145a11c67caf6 else 0x539ca4719f2bd516729042291c67cc467294822a4d67caf6794f22292c67caf687e66471a767caf6729622552c67caf6728fb5cd7d67caf672a367c11c67caf6729047c11c67caf685cf22291c6d4af6728f222a5767cac6001ca3c89e95e0e5 else if i < 46 then if i < 44 then if i < 43 then 0x728f2229247d0af6794f22291c67e0468a4f28051c67caf63c88a9359f2bdc76729532291c67caf6001d53c97395caf5728f23491c77caf6974f22291c67d5867290a2291c67cd36768f22291c838af6241ca3c91c69caf672a367e51c67caf6 else 0x728f22292c67caf685cf22296b67caf6870f25cd1c67caf6728f25cd9f6fcaf6764f25cd1c67caf6728f32292c67caf6728f22296b67caf6728f22299f5ed196728f28511c67caf6728f222a4d7d0af687cf22291c700af6728f22291c700b76 else if i < 45 then 0x984f22292467caf6728f22291c67cd86728f22291c67e0c6974f22292467caf685cf22292467caf6728f25a11c67caf6870f27e91c67caf672a3f5cd1c67caf6754f22291c67cc46754fb5cd1c67caf6728fb5cd1c67caf687cf22291c92caf6 else 0x729182291c67caf686cf22296f67caf6728f22291c67e046729482292467caf6999ca5888a471b56728f22791c6d4af685cf22292c67caf6729142292467caf6728f232d1c67cbb6728f23491c67cd3687e66901fa470af67290a2291c69caf6 else if i < 48 then if i < 47 then 0x729042291c6d4af687cf27e91c67cd36728f229d2467caf6728f22552467caf6729312291c8399f6786662292467caf685cf22291c67e046728f25bd9f2bc1f687cf232d1c700af6999d22292467caf6999ca2292467caf672a362292467caf6 else 0x728f28051c67caf685cf22292867caf67290a29d1c6d4af6794f22292867caf672a3f7e88a470af6728f22291c6b4c46999ca2291c67cbf6748f22292867caf687d142291c67cd36769622291c67caf687e663c92467caf68a0f222a5767caf6 else if i < 49 then 0x728f22552867caf672a362292867caf6728f22296f67cb76729482292867caf63c88a471df2bdc767290a2292867caf6729042292867caf69988a4919f2bc4c67290a2551c67caf6974f22292867caf6728f22291c67d7b6729532791c67caf6 else if i < 50 then 0x728fb2292b67caf6728f232d2867caf6728f229d2867caf6748f22291c67caf6729142292867caf6729042296b67caf60021f9991c67cb75728f22792c67caf688cf22291c67caf6728f22792867caf6754f25cd2867caf6794f22291c69caf6 else 0x749482291c67caf6728f25499f2bc5f6729482292c67caf6539ca589735f59f6768f22552c67caf6794f25111c67caf6728f22791c67e04685cf22291c67cd36729142292c67caf6768f22291c67cbb6728f22291c67cd367290a2292c67caf6 else if i < 59 then if i < 55 then if i < 53 then if i < 52 then 0x728f22291c69caf6729042291c67e04687cf23051c700af6728f22293067caf6728f27c12c67caf6754f22291c67cbb6728f22294067caf6778f22291c67cc76754f222a574a0af6728f232d2c67caf6728f229d2c67caf68a0f22291c8399f6 else 0x780f22293567caf6999622291c6d59f672a4a2291c67caf6728f22297c808af6728f22553067caf6728f23493967caf6778f22293067caf6728f22291c67e0b6794f22551c67caf6729622291c838306728f222924700af6729142291c700af6 else if i < 54 then 0x728f29e91c67caf6729142293967caf67290a2293967caf6728f232d1c67d586729623c88a4b20e6728f22291c67d606974f22293967caf6748f22293967caf6728f22291c9f0af6728f24808a700af685cf22291c69caf6794f22293967caf6 else 0x728f22291c6b4bb6728f222a578386e6728f22791c67cd3672962324954719f6728fb2296b67caf68a0f22296b67caf6729485111c67caf6754f22296b67caf6728fb2291c6d4af6728f229d3967caf672a362293967caf6729482293967caf6 else if i < 57 then if i < 56 then 0x729622292c8382c6729042291c67cd36728f27f51c67caf6728f25cc8a92caf6728f22291c8e8c46728f22293967caf6728f222a4d67cb76729487c11c67caf6729627e51c67caf6728f229d1c6d4af6748f22791c67caf6728f22291c67cae6 else 0x728f222a572bc48672a4622a6d67caf68a0f25cc8a5f59f672a362291c67caf687e662291c69caf6729315cc8a67caf6728f27e51c67caf6729482551c67caf6729622293567caf6728f232d1c6b4af69988a4719f2bc556729482296b67caf6 else if i < 58 then 0x7288a4919f2bcef685e362291c67caf687e663c91c67cb767290f2291c6ecaf6768f22291c680af6999622291c67c726728fb22a574a0af6768f22291c67cd367861f3c8c14720e6728f22291c8f8af6794f22291c7d0af6729323c97367cbb6 else 0x728f222a6d6d4af67563f2291c67caf6729622291c838ec6729622292c8399f6728f22796b67caf687e664719f2bce76728fb2292c67caf68a4f222a6d67caf6728f2471a72bc876999622291c67c5b685cf22293967caf672a362296b67caf6 else if i < 63 then if i < 61 then if i < 60 then 0x7294d5cd1c67caf672a7b2291c67caf6870f22297067caf6728f22292c67cb76729482296f67caf6728f229d6b67caf6729323c88a95cbb6768f22291c67d586998f22291c67cac67acf22291c67caf687dca4517367caf6728fb5ce5767caf6 else 0x768f222a4d67caf6728f22793967caf6754f222a4d67caf6729622292c4720e6728f25111c67d5c685cf22291c7d0af6728f229d7c67caf6728f25cd9f2ec5f6998f22297c67caf6728f22297c67caf6728f22297767caf6728f22297167caf6 else if i < 62 then 0x7290a22a4d67caf6729042551c67caf67290a2291c700af6780f22291c67caf63c88a4719f34db1655dca588a74719f6974f222a4d67caf6728fb5ce57470af6794f222a4d67caf6729482291c7d0af687cf22291c77caf6974f22291c700af6 else 0x728f22299f46caf6728f22291c7e0af6728f22564d67caf672a3622a4d67caf6728f23425767caf687e667292467caf6539ca3c96f67caf69b9623c88a5f59f6729042293967caf67291422a4d67caf6999ca5888a4e59f698cf22292c67caf6 else if i < 65 then if i < 64 then 0x728f229d1c67cd36728f22296b8e8af6728fb2291c67cd36729622551c67c4c6539ca3c97367cd36999623c88a4e59f6728f232e4d67caf6729142291c6d4af67290a29d3967caf6728f229e4d67caf68c1da3c88a4720e6728f227a4d67caf6 else 0x755323c97367caf6728f22291c6b5586728f25124d67caf6728f22791c7d0af67294c4719f2bcef6768f27e51c67caf6748f229d1c67caf6729484719f2bc876728f23411c8399f6748fb2291c67caf6748f22291c67cb76728f222a6d67e046 else if i < 66 then 0x728f27c25267caf6728f2471f42bc876778f22291c67caf6729312299f2bd196794f22291c700af6728f222a5267caf6999ca2292469caf6728f222a5167caf6768f22291c2bd9c69990a2291c6d4af6999ca2293067caf6974f22291c8e9586 else if i < 67 then 0x728f27e65367caf6728f28066d67caf67296222a5367caf6728f229d1c69caf6728f22292867caf6728f22293567cc8672a3622a5367caf6729535cc8a5f59f6728f22291c69cb7687cf27e91c700af6728f222a5367caf6729142296b67caf6 else 0x87cf232d1c67cd36728f25111c67cb76728f22291c67e086754f25cd9f2bc5f6728fb5111c67caf6729622551c8382c69be662291c67cb76998f22291c6ecaf6794f22291e67caf6728f222a5667caf6795312291c67caf6728f22292c67d5f6 else if i < 102 then if i < 85 then if i < 76 then if i < 72 then if i < 70 then if i < 69 then 0x728f25497d67caf6729692291c67caf69b8f22297d67caf6754f25ce5767caf6729142291c67e046728f22291c700af67295322a5767caf687d145cd1c67caf67293122a5767caf67290f22a5767caf6728f22791e67caf6728f27c11c67cb76 else 0x728f22293967cb7687d143c97367caf6729145cccb67caf699a4029d1c67caf6729385cc8a67caf687d145cc8a67caf6728f23011c6ecaf6728f25cd7d67cbb6785e53c88a95caf6729144808a67caf6754f25cd7d67caf63ca1d4719f2bdc76 else if i < 71 then 0x748f22291c69caf6a38f22291c67caf687e664c97367caf6539ca4517367caf6729363ed7367caf6241ca3c92467caf6729323ed7367caf68a0f22297d4719f699962229394719f6728f22291c2bd9d6728fb2293967caf6729312291c67caf6 else 0x87e663c91c69caf6728f22791c69caf6792662291c69caf6786662291c69caf687e664911c67caf6999ca2291c69caf6729482291c69caf6728fb2391c67caf69b8f22291c910af6729142291c69caf6728f25ce572bc1f6728fb2291c69caf6 else if i < 74 then if i < 73 then 0x266588a74719f5729482291c67cb76728f22297c67cac6768f22291c6b4af6728f22296b69caf6728f12291c67caf6539caa19fa470af6728f22293069caf60021f9991c69caf587e667291c69caf67861f3c91c69caf687e293c91c69caf6 else 0x795042291c6b4af6728f22791c700af6728fb2291c6b4af6728f24719f220af6974f22291c6b4af6728f22891c67caf685cf22291c6b4af687cf23051c67cd36728f25cc8a77caf67290a2292467caf687e664719f2bc8168a0f22291c67caf6 else if i < 75 then 0x728f22291c6c0af6794f222a576b4af6728f22296b6b4af6728f2229286b4af6754f222a572bc3d6974f22296b67caf6768f22292867caf6728f22296f67caf6728f25111c6b4af69be9c3c88a5f59f6794f22791c6b4af6728f22551c6b4af6 else 0x780fb2291c67caf6728f28051c6d4af6974f22292c67caf6728f222a9867caf6728f22551c6d4af6999322291c6d4af67290a2291c6d4af6754f22292867caf6998f22291c6d4af6974f22291c6d4af6794f22291c6d4af6748f22291c6d4af6 else if i < 80 then if i < 78 then if i < 77 then 0x729147c11c67caf6728f254a5767caf6768f22291c700af6729482291c700af6729042291c700af6728fb2291c700af685cf22291c700af6974f25a11c67caf6748f22291c700af6728f22291c6ecaf6728f22291c6e4af6728f222a4d6d4af6 else 0x728f222928700af672a462291c6d4af6728f24719f2dc876728f27fc9e4720e687cf28591c700af6728f28511c700af6728f25111c700af67291432d1c700af6794f22292467caf6728f232d1c700af6728f22551c700af672a4a2291c700af6 else if i < 79 then 0x729145cc8a700af6785ca4108a95caf6728f22292c67cc46998f22291c77caf6729142551c67caf6729145cd9f2bc1f687cf25cc8a700af687e664719f2dc166728f25cc8a700af6728f222a4d700af6728f22292c700af6754f22291c700af6 else 0x729042291c7d0af6728fb2291c7d0af6729532297d4719f6748f22291c7d0af67b5e53c88a95caf6728f22291c7d0af6728f25cc8a718af6794f22291c718af69be293c88aa799f6728f22291c710af6728f25ccc1700af6728f295d1c2bc876 else if i < 82 then if i < 81 then 0x728f27c11c7d0af6728f229d1c7d0af6785ca4108a4720e6728f222a4d67caf69990a2293967caf6999622291c6d44c6728f22551c7d0af6754f25ce572bc1f67294d2291c7d0af67290a2291c7d0af6728f22292467caf6998f28051c67caf6 else 0x748f22291c8e8af6728f22291c7f8af6769622291c67cc4685cf222a4d67caf6728f22291c834af68a0f22291c7f8af67b5e53c88a4720e6729482296b7d0af6728f22296b7d0af6728f2229287d0af6769622291c838af6988f22291c67caf6 else if i < 83 then 0x539ca3c973700af6729622292c67caf67490a2291c67caf6728f2229288e8af6728f25311c8e8af6728f232d1c8e8af6728f22292b67caf6728f22291c67cc76728f22791c8e8af67290a2291c8e8af6974f22291c8e8af6768f22291c8e8af6 else if i < 84 then 0x728f25491c910af6728f2229248f8af6539ca5cd1c8f8af6974f22291c69caf6999ca2291c8f8af6728f2229398e8af6729142291c7d0af6728f232d1c6d4af6728f23048a4b20e6728f229d1c700af6728fb4719f2bc81672a462291c67e046 else 0x98cf22291c838af6748f22291c67cc46728f22551c680af6728f22291ca04af69be669008a95caf6728f22291c954af69be663c88a92caf687dca3c93067caf6728f25a11c92caf6728f22291c92caf6728f22291c91caf699962228524719f6 else if i < 93 then if i < 89 then if i < 87 then if i < 86 then 0x728f22792467caf6794f222a574720e672a468051c67caf6728f25cd9f2bc6a6768f22292c838af6974f27c11c67caf6728f2229707d0af63c9732299f2bdc76870f27e91c838af6728f27e51c838af6729042291c910af687e662292467caf6 else 0x729415888a4e59f6755ca3c97395caf67290a7c11c67caf6998f229d1c6d4af67290a5111c67caf6728f22291c77caf6728f222a53838af6728f25ce5767cbb6728f222935838af6764f22292b67caf6728f222930838af6728f232d6b67caf6 else if i < 88 then 0x9288a4719f2bc4c6728f25111c67cc46728f22791c7f8af69be293c88a95e0e6998f22293967caf6728f22291c69cc46728f22292467d5c687e664919f2bc166794f222a57838af6729042292467caf6974f22551c67caf6728f27c11c67e096 else 0x728f25ce57470bb672a3f22a57470af6729043c88a95e0e6870f222a57470af6728f22291c911586976362291c67caf67290422a4d67caf6780f222a57470af6728f232d1c67e046768f22291c6d4af6754f222a57470af6728f22292c67cbb6 else if i < 91 then if i < 90 then 0x754f22291c6d4af6728f22551c67cc469be4a22a5767caf687cf25cd9f2bd106754fb2292867caf6539ca5891c7e0af67296229d1c67c2c6999ca901f9470af672a403c9f9470af672a4053257470af6728f22551c838af698e4022a57470af6 else 0x768f22296b67caf69bdca3ec8a95caf6539ca3c91c7e0af6729042292c67caf672a4a8511c67caf69cdd53c88a95caf6728f22291c6d55869bdd53c88a95caf6755323c88a95caf6728f22293967cc46728f23013967caf672a403c88a94caf6 else if i < 92 then 0x85cf22291c67cb76728f227a578399f6754f22291c67cb76728f22293e67caf6748f22291c67cbb6539ca9017395caf6001ca3ed7395caf572a362291c67cc46974f22291c7d0af6728fb3c97395caf6785ca3c89e95caf6786664c88a95caf6 else 0x999ca2291c7e0af67294d4719f2bc876729142291c67cb76729042291c67cb76728f25a11c67d7b6729142291c92caf68a5ca3c88a4b20e6728f232d1c67cd36870f22291c7d0af6974f22291c67cb76768f22292c67caf686cf22291c67cb76 else if i < 97 then if i < 95 then if i < 94 then 0x87dd23c91c69caf6999d22291c67cb76728f22791c67cb7687e667291c67cb76728f27c11c67caf6728f22292c680af6786662291c67cb76728f222a4d6b4af6754f22292c67caf63e1ca2291c67cb76728f22296b67d58672a362291c67cb76 else 0x728f22292467cb7685cf27c11c67caf69988a471b52bc166728fb2292467caf687d142291c67caf6794f222a572bc1f6729312291c718af6754f22291c67e046728f227a574720e687dca3c91c67cb76728f22291c69cbb6728f229d1c67cb76 else if i < 96 then 0x87dca3c92467cb76780f22291c838af6754f25ce57470af6728f232d1c69caf6764f22291c69caf6728f27c11c67cbb6999ca2292467cb76728f25111c67cbb6729562291c67caf6728fb22a4d67caf6728f2304954720e6729622291c838356 else 0x85cf22291c67cbb6794f22291c67cbb6728f22292c6b4af6728f22291c7e0b76728f22291c7d0b7685d562291c67caf672a4a2291c67e276749042291c67caf67921f3c91c69caf6999ca2291c69cb769b8f25491c67caf6729622291c2bd9c6 else if i < 99 then if i < 98 then 0x728f22291c6b6046728fb229a1470af67294d2291c67cbb6729142291c67cbb67290a2291c67cbb687d144719f2bc166728f22293967cbb6729042291c67cbb6754fb2291c67cbb6728f22551c67cbb6728fb2291c67cbb6870f22291c67cbb6 else 0x72a367c11c67e04672cf22291c6d4af672a362291c67cbb6728f232d3967caf6729042291c69caf687cf23691c67cd36754f22291c67cd36a45ca901fa470af6728f25cccb700af687cf2471a72bc5f6728f22391c67cbb698cf22291c67d5f6 else if i < 100 then 0x728fb2292867cbb6728f222a578389a6729482291c67cbb6778f22291c838af672962229844b19f6754f22292867cbb6728f22292867cbb6728f22292467cbb6728f22291c67e836794f22791c67caf6728fb5cd1c67cbb6754f25cd1c67cbb6 else if i < 101 then 0x728f22291c700bb65a9ca4517367caf6728f22291c6d4bb6728f25cd8167cbb6728f22297067cbb60021f3c973700af5728f22296b67cbb68a0f22291c67cac6729045111c67caf6728f25cd2867cbb6748f22291c67d586768f22291c69caf6 else 0x998a62291c67caf687cf25cdc02bc5f6768f27c11c67caf69bdca3c88a67d7b6768f25111c67caf6728f22291c7d0bb6728f222a4d8e8af6241ca3c91c67cb76754f222a57470bb6754f22291c69caf6539ca5896f67caf6974f22291c92caf6 else if i < 119 then if i < 110 then if i < 106 then if i < 104 then if i < 103 then 0x8a5ca3c8954720e6728f25491c67caf6728f22291c8319c6999622291c67ca3672a3f7c11c67caf6754f25111c67caf6728f22291c69d5867294d22a57470af6769622551c67caf6998f229d3967caf6728f22291c6b4d36728f22791c67caf6 else 0x728f22791c2c59f6728f22292c2bd946728f232d1c7d0af6768f22551c67caf687e293c91c67cb76728f25ce572bd946728f24719f2bc876728f227a572bc1f687cf244d1c67caf685cf22791c67caf6728f22291c700c46539ca2291c8f8af6 else if i < 105 then 0x754f22293967caf676a362291c67caf6728f23025767caf6728f22551c67cc86728f22291c67d5c6999ca2296f67caf6768f22293967caf6768f32291c67caf687e664719f064af67290a2291c67cb76728f27c11c67d58687e664719f2bc166 else 0x768f22291c67cc46728f22291c67cc4687dca3c91c67cbf69b8f22291c8399f6001ca3c97395cbb59bdca3c88a95cbb6728f222a574a0bb6748f22291c6b4af6728f25cd1c67e096786665888a4720e6728f22292c8e8af67290a29d1c67caf6 else if i < 108 then if i < 107 then 0x728f22552c67cc46974f25111c8e8af6728f27c11c6b4af6728f22788a95e0e6729145cc8a67caf6754f22391c67caf6728f22292867cc46728f22292467cc46728f229d1c67cc467290a2291c67cc46728f22293967d586974f22291c67cc46 else 0x728f2229286d4af6794f222a5767caf6999ca2291c67cc76768f22291c838c4686cf22291c67caf6768f22291c7d0af6728f22291c7d0c46728f22291c6d4c46728f23011c8399f6728f222a4d67cc46728f28751c67caf6728f22296b67cc46 else if i < 109 then 0x729382291c67cd36729142291c67cd36974f22291c67cd36754f22291c7d0af6728f2229396b4af6794f22291c67cd36794fb2291c67caf6794f22291c67cb76728fb2291c67cc86728f222a0e67d196728f22291c67cc86728f22551c67cc76 else 0x729045491c67caf6728f22291c7d1586729145cc8a67cd36728f22296b67cac6794f22291c8399f672a362291c6b4af63e1ca2292467caf6728f25cc8a67cd367294d7e91c67caf6728f27c11c67cd367291432d1c67cd36728f22551c67cd36 else if i < 114 then if i < 112 then if i < 111 then 0x728fb2291c67caf6729482291c6b4af6728f25311c67d5f6729622291c839986728f25ccda67cd36780f22291c67cc8687dca3c97367cd36728fb2291c2bd9869988a4e59f2bc166728f22291c69cbf6728f25ccc167cd36728f25cccb67cd36 else 0x728f22291c8e8d36728f22291c7d0d36728f22291c77cd36728f22291c718d36728f229d1c67caf6739142291c67caf6729142291c700d3687cf22291c700d36728f22291c67cb760021f3c97367cd35728f22296b700af6999622291c6d4af6 else if i < 113 then 0x728f22291c67cdb6728f22291c67cd967294829d1c67caf685cf229d1c67caf6728f22553567caf685cfb2291c67caf6728f23391c67caf6728f25cd1c67cbb67294d2297067caf6728f22291c702276999ca2292b67caf687e293c92467caf6 else 0x72a362291c67d586729142291c67d586794f227a5767caf6728fb5cc8a95caf67290a2291c67d586728fb2291c67d5869b8f22291c67d586728f25491c67d586728f27e51c2bd9c6794f22291c67d586754f22291c67d586728f23411c718af6 else if i < 116 then if i < 115 then 0x728f22292c67d586728f22292867d5867950422a5767caf6728f222a57470bb6728f27c11c8e8af67288a4719f2bcef6728f232d1c67cb7672cf22293967caf6728f22551c2bd946728f25111c8e8af6728f25111c67d586728f22551c67d586 else 0x999ca2291c67d5c6748f22291c69cb76984f22291c67d5c6729142299f2bd196728f22291c8e958687dca3c91c69cb7687e662291c67cb76728b53c88a4e59f6728f22791c8382c6728f22292867cd36794f22791c8399f6728f222a4d67d586 else if i < 117 then 0x728f22291c67d5d6728f22291c92d7b6728f22291c8f95c6728f227a5767caf687cf21997367caf687dca3c91c67d5c6729042291c8382c6795042291c8399f6728fb2791c67caf6728f22551c8e8af6764f222a57470af67950f2291c67caf6 else if i < 118 then 0x728f22292869caf6728f22791c8399f6729142291c67d7b687d147e91c67caf672a362291c8e8af6729622292c67cc4687cf22291c67d7b6728fb4719f2bc876728f22293067cc76728f22291c8e95f6795142291c67caf6999ca588a74719f6 else 0x729482291c8e8af6768f22291c67e0467290422a5767caf69be663c88a67d7b6728f22ad1c67caf69ca662292467caf6728f28524d67caf6728f222a4b2bc3d6728f22292c838af6728f22291c700d36728f25cc8a67d7b6728f222a5267e096 else if i < 128 then if i < 123 then if i < 121 then if i < 120 then 0x728fb2291c67e046728f22291c67d5f6754f25cd1c67caf6768f22291c67cb76728f25112867caf6999ca9008a94caf6974f22291c67e046729623c88a472026729042291c8399f68714d2291c67caf6729312291c67cd36728f22291c701586 else 0x728f22291c8ea046728f22291c702046728f22291c69e046728f27c24d67e046728f22296b67e046728f22292867e046728f25311c838af6728f27c11c67e046728f229d1c67e04672a362291c67e046729142291c67caf6729482291c67e046 else if i < 122 then 0x87cf22291c67e276728f22291c67e276728f222a5367e0b6728f27e51c67e0b6768f22291c67e0b687dca3c9fa472096539ca9028c470af6728f222a5747209672a3f2291c67e0963e1ca2291c69caf6754f22291c67e09685cf24719f2bc286 else 0x728f22297067caf6728f222a4d67cbb67290427a5767caf6728f25cc8a67e276728f22296b6d4af6728f22293967cac6794f22291c839ad69bcf222a5767e27687dd23c92467caf6728f22551c8383d6728f28511c67e2769bcf22291c67e276 else if i < 125 then if i < 124 then 0x728f22292c6d4af6728f25491c8399f6729622551c8399f6729532291c8399f6728f24919f2bc8467290f2291c8399f6729042291c2c59f6794f22291c2c59f6728f232d2467caf69bdca3c88a92caf6728f222a57838416728f22291c67e9b6 else 0x748f22292469caf68a4f222a6d8399f6998f23491c67caf6728f222a4d67e276728f22296b7f8af6729363ec8a95caf687dca3c92469caf6729532291c7f8af68a4f28051c8399f687e664719f2bc286728f22291c6b4b76728f22551c838c46 else if i < 126 then 0x769622297d4719f6728fb29d1c67caf6729142791c67caf69b8f22299f2bd19687e66588c14719f6728fb2291c67cb76539ca5cd1c67d5c6796403c88a95caf67290422a578399f6794f222a578399f6728f22291c6d6046728f25111c8e9586 else if i < 127 then 0x7950a2291c67caf6999623c8a74719f6728f2229a1470bb6768f22292c67cc46999622293967caf6728f22291c7d05b687cf24919f2bc5f6729623c8a74719f672962304954719f6769623048a4719f672a3622a4d67e046729532296b67caf6 else 0x729623c8a74e59f6794f23011c67caf6539ca5888a4e59f687cf25cd9f2bc726729325888a4e59f6729623048a4b19f6729042791c8399f6729622297d4b19f6729623c8d24719f6729623c8c04719f672962428a74719f6728fb22a57470af6 else if i < 132 then if i < 130 then if i < 129 then 0x728f27c11c67cc46728f227a576b4af6794f22291c67cc46729622551c67cc46729622551c838af67290a229396d4af69be665888a5f59f6728f25cd1c67cbf6768f22292467caf6a66293c88a5f59f6729623c88a9b59f6729623c88a5f19f6 else 0x72932589733059f687e293c9735f59f6870f22291c67caf6728f222a4d67cd36728f25c99f2bd19672a822291c67caf6728f22292c67e046754f22292467caf6729623c9525f59f6728f22291c6d4d36728fb22a57470bb67861f3c91c67cb76 else if i < 131 then 0x729325888a471b56728f222a57470bf6728f2229396ecaf6999623c88a471b56728f22292467d586728b53c88a471b56728f22791c839ad6729042291c839ad67290a2291c67caf67290422a576b4af6728f22291c67e0969b8f22291c67caf6 else 0x729622548a4720e6728f22291c6d49a687cf25cd9f2bdbc67290422a574720e68a5ca3c88a472026729623c88a4e5b56729623c8a7471b5687e293c88a5f19f6729622557d4719f6539ca5888a471b5699a482291c6d4af6769622292c67caf6 else if i < 134 then if i < 133 then 0x7290a32d1c67caf6999ca4719f2bc876754f2229a1470af6729047e88a4720e6728f22299f2bd19685cf22291c67cc46729482291c67cc46794f27e88a4720e6748f22296b67caf6768f23048a4720e6728f22291c8e8b7687e293c88a472026 else 0x8a5da3c88a4720e6728f27c11c6d4af6794f22291c67caf6748f22292c67caf672a403c89e95caf672a3f22a5267caf6728f22292c67cd36728f28051c67e04672a4a22a4d67caf6728f25111c6d4af6769623c88a4720e6728f2229246b4af6 else if i < 135 then 0x539ca588a74719f699a402291c6d4af6794f222a578383d6748f22291c67e046729623c8954720e6728f2324954720e6728f2a211c67caf6754f222a5267caf6728f22296b67cd3672a367c24d67caf687cf25cd1c67cd36001da5888a4720e5 else if i < 136 then 0x1ca4108a95e0e5728f25116b67caf687cf22291c718af698cf22291c8e8af6001e53c88a95e0e5974f25111c67d586728f2229396d4af6795ca3c88a95e0e6975042291c67caf6001ca5888a4b20e5539ca589fa4720e6001ca588954720e5 else 0x728f25ccc195e0e69990a29d1c67caf6729325888a95e0e687dca8fdfa470af6728f27c16b67caf6754fb22a57470af6728f22292c69caf6

def val5 (i : ℕ) := field (val5Chunk (i / 12)) 64 (i % 12)

def pick5 (h : ℕ) := (h * 137 % 10000019) % 1639 + disp5 (h % 1639)

def db5 (i : ℕ) : List W :=
  let a := val5 i
  unpack wireOf 10 (a % 16) (a >>> 4)

def allow5 (ws : List W) := !(matchTable 1639 db5 pick5 ws)

def disp6Chunk (i : ℕ) : ℕ :=
  if i < 121 then if i < 60 then if i < 30 then if i < 15 then if i < 7 then if i < 3 then if i < 1 then 0x20000007b93c90090031708e516d else if i < 2 then 0x22a85d0001752b8000000000000000853002 else 0x1005000013002000000012000899867001 else if i < 5 then if i < 4 then 0x976000515000002000000000000000000000 else 0xa7a0000003ba19700200099d00020b472000 else if i < 6 then 0x8f594700010f00a001004002000000000 else 0x25a93de00000000000098031c017000000 else if i < 11 then if i < 9 then if i < 8 then 0x9e000c0010000000003161b5347000000000 else 0x8b34c00000010003cb000b498a6000000000 else if i < 10 then 0x466a001943000000000000b42868000000 else 0x100e000000ad900100247c0000006d6000 else if i < 13 then if i < 12 then 0x3fe00000033000000000039c4e7000001000 else 0x40006b10025e760f000000000000000 else if i < 14 then 0x200000097146da2300000200163e else 0x4000a1e3cd00045300d0010bb000000000 else if i < 22 then if i < 18 then if i < 16 then 0xdd0040000080010000007980043c7011 else if i < 17 then 0x10009280004a1000000020000000005000 else 0x97a000000a0056e0003880045113b90015d6 else if i < 20 then if i < 19 then 0x2c50000000000000000005846e2005000000 else 0xa2b7a4072a2c00000082100000000a007 else if i < 21 then 0x4cf00090d6631467097150000002d64cd else 0x30011ab000000000000000003000 else if i < 26 then if i < 24 then if i < 23 then 0x2000001002000027000000ad6000858000 else 0x6b80063880007f50010000005f1ab3000003 else if i < 25 then 0x7e1897004851007b427367eca52000396 else 0x1000a3c8f192200000057000081a458000 else if i < 28 then if i < 27 then 0x6660004d5000360000acd000000000000 else 0x93b0000010005790040002b300000000f691 else if i < 29 then 0x12fd0000003f90120008e9000000000000 else 0xa001ac2aa40000000000005c900000037a else if i < 45 then if i < 37 then if i < 33 then if i < 31 then 0x25b319006000681000002000004000b22001 else if i < 32 then 0x98422eb39001000000002000000006000000 else 0xa6b274447000a680008020000009942c6000 else if i < 35 then if i < 34 then 0xb2d00000000700038802600000436d41b else 0x30005d90010031f5afb000000000070 else if i < 36 then 0x6913136c618132e351b4d0033eb004000000 else 0x1006509000000000b43001000000000 else if i < 41 then if i < 39 then if i < 38 then 0x67201b8760004f700000000018300000074a else 0xb530000005dc000000a3b000246000000002 else if i < 40 then 0x9c4000008810000a355304370002f4000 else 0x200000000000052d000001000744 else if i < 43 then if i < 42 then 0xab99a900e3aa10d000000a50001000000 else 0xe00000000000000300000a000000210002 else if i < 44 then 0xf0008df11287b00022a767000 else 0x2470000003730000002de211000ada000000 else if i < 52 then if i < 48 then if i < 46 then 0x9e600060d00700a0004caa340008f4003000 else if i < 47 then 0x3356fe0000031206fa0020008e8000004000 else 0x13aca11000000000000a2d00400034a1a1 else if i < 50 then if i < 49 then 0x5480004ec00020f004561b428c200401e4dd else 0x27a000afc6b000d000006943000 else if i < 51 then 0x68c0000001bc0000a200000000000042098f else 0x9a900069100000000000078e001004000 else if i < 56 then if i < 54 then if i < 53 then 0x94871f5c10002eb000008000000001014 else 0x3160020040031880059d6000000029 else if i < 55 then 0x677377000004000000a5e0089780004c2000 else 0x54a0000000005472ac0000006c77ff000000 else if i < 58 then if i < 57 then 0x5790000008300010000000000000000006b4 else 0xaa0000000004105c2000000000010000000 else if i < 59 then 0x4f40000000000000000014bca0b000000000 else 0x71600000048a000013000001000000000 else if i < 90 then if i < 75 then if i < 67 then if i < 63 then if i < 61 then 0x5072fa0000000010004b800000000321d197 else if i < 62 then 0x2a3000000000000000aeb000005091000005 else 0x46c003285000b230018df else if i < 65 then if i < 64 then 0x80238b00000002476e000000000a63570000 else 0x72d0000006780000000001024917a5000b21 else if i < 66 then 0x2c535442a00100076100079a002a61 else 0xadd0100073df00000000000000125c017 else if i < 71 then if i < 69 then if i < 68 then 0x40007a90030004f10101048270000000d1 else 0x9306bb0008120000000050000002e8 else if i < 70 then 0x17c100000000040c76094183f00762f9cd else 0x76609e0000000000007931ec000029001 else if i < 73 then if i < 72 then 0x59133a0001640000000000020010006ca000 else 0x10094ee9b1b176e7000000000004000a29 else if i < 74 then 0x3ac02a11660024690006ee000000 else 0x3b929000000000371600120a001 else if i < 82 then if i < 78 then if i < 76 then 0x2b800100000000000002200000071f0004ed else if i < 77 then 0x1890000020000004b36ab004004b10003000 else 0x1840000002fc0006950000000001b0000000 else if i < 80 then if i < 79 then 0x2fe51c58f005000a7032456e879000757003 else 0x60150010030017590006e32ba0004f3000 else if i < 81 then 0x7da0a0009840080000080017dc00200015f else 0xb4b0000b80000000006bc00e57f000809739 else if i < 86 then if i < 84 then if i < 83 then 0x45fd1b10008137f39bf00d656003 else 0x1001000a82712826005000000610000008 else if i < 85 then 0x7b541200000800031894d875000001 else 0x833352002002000002aa00000078af007800 else if i < 88 then if i < 87 then 0x12400000400000161825200099590f7bc else 0x9ba00000000000002e000000000000 else if i < 89 then 0xa720000024e600000000023d000000 else 0x5f0000006790000a24a7000102000a5c000 else if i < 105 then if i < 97 then if i < 93 then if i < 91 then 0x6e5000000001371a640000060006270003a6 else if i < 92 then 0xb3f00000060e4da7c60000005360007d900b else 0x7a40018e47756e7007ad3000000663000000 else if i < 95 then if i < 94 then 0x14ff77c00000086d82b0020006c1 else 0x55c0000cd000000a9f0003c68df000000 else if i < 96 then 0x215400000000130638f00000a000001 else 0x14d60003950159b69dd003000341000 else if i < 101 then if i < 99 then if i < 98 then 0x91d28a23400b6a40000330056900004bd else 0x4320000000159fc9d6a9213a07a006001000 else if i < 100 then 0x6e0007ad000adaa0e000 else 0x40000348f10d0030000001174622824ab000 else if i < 103 then if i < 102 then 0x5c600091430200000100000b000000 else 0xb4f536000000a9d000021468001893000000 else if i < 104 then 0x83e00000000047b8a614e006803000a61 else 0x67700003700000072277b0006b3000000b44 else if i < 113 then if i < 109 then if i < 107 then if i < 106 then 0x9445000001000679acf000000000000000 else 0x40000130000026fd757000394000002000 else if i < 108 then 0x4424dc00200200000408d000000a32000 else 0x10020000000016bf001000000005000 else if i < 111 then if i < 110 then 0x39d2550000000033c000064e51f001000000 else 0x5b883300000171c000000001000000000 else if i < 112 then 0x64800000001a000000000961000000004 else 0x1db00007c0007f30002975a700119166d4ca else if i < 117 then if i < 115 then if i < 114 then 0x6770000000000000007870001c9 else 0x16c0004740008d4000002000002000b01 else if i < 116 then 0x470004360000000008fa9d100000000a000 else 0x7a331d8ed72e00000000604f00000000011f else if i < 119 then if i < 118 then 0x11260060000007f2000508002001000000 else 0x45700038600344700084a9410f320c else if i < 120 then 0x40000000000038ed000798a9a111000b2c else 0x100300300000098c004000000 else if i < 181 then if i < 151 then if i < 136 then if i < 128 then if i < 124 then if i < 122 then 0x72800051a0002bd00001231d005006000000 else if i < 123 then 0x100000055500000079c000000b3541bad3 else 0x67c000003008219024000006000 else if i < 126 then if i < 125 then 0x30010000000d83ad0005d18f8 else 0x81b0000007880300010000097bc847001 else if i < 127 then 0x64e000000000000674000198001000000000 else 0x10000008bd5b10010000000000033a3 else if i < 132 then if i < 130 then if i < 129 then 0x5660000000013200030000000009828bf000 else 0xb300000000008c749c51500062b000000 else if i < 131 then 0xac26cf0000005b6637000000a120010019e0 else 0x4260000000004c94d7001000001000789297 else if i < 134 then if i < 133 then 0xc10007530000003e846aa46000631669000 else 0x6e900000000000000000084c009683427 else if i < 135 then 0x95c3a50000000001c47f60000000000000b2 else 0x349000000000000a9a1f90026a80000002e2 else if i < 143 then if i < 139 then if i < 137 then 0x2d300000000000000089600000a0003f7658 else if i < 138 then 0x6200032c000675000009005000000593009 else 0x71d000000000005300000058b else if i < 141 then if i < 140 then 0x6ab0000010000000037ea001000508000000 else 0x888899191000000000000000840002000abc else if i < 142 then 0x40057eaac50005cb0014aa000000000013 else 0x97a9d2000000000069000000000000000000 else if i < 147 then if i < 145 then if i < 144 then 0x70000039cb000323000000648000000000 else 0x3496b50a70051ad009a0397a0007aa000002 else if i < 146 then 0x659a3400000a00023b0002635661f70c9007 else 0x19f548d89c000000 else if i < 149 then if i < 148 then 0x8279f4000000001000000000007000006000 else 0x300a00639700000094f8bfb40000000591 else if i < 150 then 0x3751d56e45973f0000000381000b33000 else 0x100000081ea6982f0000b88e6000001000 else if i < 166 then if i < 158 then if i < 154 then if i < 152 then 0x340002050008670000015f724f0ee0cbb2b else if i < 153 then 0x500000087300078f001000b1800020e else 0xa4b0008e671e00a8a5000000947000000000 else if i < 156 then if i < 155 then 0xc000000000003000658000000018000b51 else 0x8fd00000000000400000001300000036b else if i < 157 then 0x9bc3875980000020000020047ae805001000 else 0x30010010000000060008b647b40483e else if i < 162 then if i < 160 then if i < 159 then 0x2890000024d81f90022cc000000b48000500 else 0x3f3000000000014000ae26e076541e000781 else if i < 161 then 0xaf35360000005bc3f7000451441000360 else 0x6518f600a0007d47acaf6000000000000000 else if i < 164 then if i < 163 then 0x64b67bc8536c0000003000001000000 else 0x77c00000000000000a000 else if i < 165 then 0x5a40030008460000012e500000293f000 else 0x9cd0000000009b700000015d71678f6a9001 else if i < 173 then if i < 169 then if i < 167 then 0x8b57a1219c16b96ef00000000012d000 else if i < 168 then 0x6000000000221b360010000014e20ca001 else 0x22f00f8c40012789b3000000000 else if i < 171 then if i < 170 then 0x3249b40004300000008b900000000000099b else 0x66b00000020db1900100025030e000a3d000 else if i < 172 then 0x1280000010000000030037ed096000000006 else 0x19d61e00c08e00045693000000000687a000 else if i < 177 then if i < 175 then if i < 174 then 0x3fda0128200000035a12100012f083000 else 0x10000008b25310000017a7313000000000 else if i < 176 then 0x9c024ea3a00072e8de00022f003000000 else 0x8000002000000000000 else if i < 179 then if i < 178 then 0x491009a08000000001000879000000005000 else 0x9234960000008927610000009ee0001d0606 else if i < 180 then 0x3ae4f900521d00199a000000000000000a8f else 0xa110032670050004f2000000002004000000 else if i < 211 then if i < 196 then if i < 188 then if i < 184 then if i < 182 then 0x11000d59400000000100000063f00100394b else if i < 183 then 0x6760000010000000a7000003000000000002 else 0x70d41f003938000003018120000000000 else if i < 186 then if i < 185 then 0x4a100088300000017764d000000000 else 0x42d00000022600000000000038a000000003 else if i < 187 then 0x8f400000000400109642d0000009890009b0 else 0x7b50000000002100000be141003000 else if i < 192 then if i < 190 then if i < 189 then 0x10010002e40007500008a61c2a02000 else 0x4b4a0009e90004ff0ae6a9000 else if i < 191 then 0x2000000697558000000622011000000a25 else 0xba3030000000187db0105e30000007b73bc else if i < 194 then if i < 193 then 0x9fa217ac1000000000000000a271a8340 else 0x716740030010008dc000000000a6c307000 else if i < 195 then 0x10000000020000007016255756d8 else 0xa5b000000625000504011000000000000 else if i < 203 then if i < 199 then if i < 197 then 0x2fc0000000000045b6aaf630000000 else if i < 198 then 0xe00000006440020873be0020fb0008fe138 else 0x9970000000d822600094d0000005ed000000 else if i < 201 then if i < 200 then 0x50400000000000116c067000000000000000 else 0x1ad249000a9579800161a556000000000000 else if i < 202 then 0x4a923cb0027622660000057500022e0b50 else 0x580020004250003d5000000000008002000 else if i < 207 then if i < 205 then if i < 204 then 0x70000000002adaf584a00000671e2ab else 0x4a8000000a2307232b46a0002bd0008b2000 else if i < 206 then 0x17700046a4250000008c80009e2000000 else 0xb0000300d39e9400117280010e8 else if i < 209 then if i < 208 then 0xa090025cb000002000546001a3e0000c7 else 0xb2c0000000000000009cc0000084f6000000 else if i < 210 then 0x126f30000010025f6ade8026b3002000012 else 0x9b9000002693000007ab6237000000281 else if i < 226 then if i < 218 then if i < 214 then if i < 212 then 0x2e3000655000000001000000002000 else if i < 213 then 0x3d90000011d7000a3086e000000000000885 else 0x250020030000000000000005fe00017e4cf else if i < 216 then if i < 215 then 0x41400000336600800000119600101626e550 else 0x2a80000010000006c48b7001000000007312 else if i < 217 then 0x7ce4b70045cc001000000000 else 0x1000000000000000690000000000000 else if i < 222 then if i < 220 then if i < 219 then 0x50030000b200000000100000000054f40c else 0x197300093d0002d82b700000163e000 else if i < 221 then 0x475000309000000000403aaa9b63e9000000 else 0x500000100014a92f000000000 else if i < 224 then if i < 223 then 0x51300000056800000000000000000025b00b else 0x75a0000000000005601d69d0091000000 else if i < 225 then 0xb0000040000008c09b501f000000003135 else 0x1a3d00800022b0005857d1010079000 else if i < 234 then if i < 230 then if i < 228 then if i < 227 then 0xade03e00000100000000070f000841009000 else 0x300000000090d000000000987000 else if i < 229 then 0x2bc0356b661100070fa0e00368b001000000 else 0x7a39a50000000000008cb0000020007ea else if i < 232 then if i < 231 then 0x32d1000001000000000000002000 else 0xb725b000002015000000000000000000 else if i < 233 then 0x2174ea61b00100026a000000 else 0x400f074a4382e00000000148300056a003 else if i < 238 then if i < 236 then if i < 235 then 0x3650030001f00616e8000abd8a2000aae else 0x8110010000000000000010007305b4000 else if i < 237 then 0x8dcacf104494000004706000006000000 else 0x8ab2ed0000003d51eb002304000001 else if i < 240 then if i < 239 then 0x2e82dd9fe300663003000a770005746bf else 0x96d00f00000000711f0006a7000000 else if i < 241 then 0x3000003000002002000000001000000000 else 0xb2c0010008b8007

def disp6 (i : ℕ) := field (disp6Chunk (i / 12)) 12 (i % 12)

def val6Chunk (i : ℕ) : ℕ :=
  if i < 121 then if i < 60 then if i < 30 then if i < 15 then if i < 7 then if i < 3 then if i < 1 then 0x728f22291c2f59f2bdc00728f22291c6ecaf6728f2305444719f2bddda3c88a4719f2bc0077290a3048a4719f2bddca3c88a5f52c67caf7728f22291c67c732bddd53c88a4719f2bc007795ca4108a4719f2bddca3c88a4719f2bc007728f22291c839b52bddca429732291c67caf7 else if i < 2 then 0x728f22299f2bcdc1b9dca3c88a471f867caf7729042291c67caf009e6f8a4f22297d4719f7728f22551c67caf001dca2d4f22291c8399f7729142291c67caf001dca4288a4719f2bc007001ca3c88a4719f2ed800728f222a4d67e046728f22291c67c852bddca3ec8a4719f2bc007 else 0x728f22291c7d0af001dca3c88a471c02bc007728f22291c6d4af001d4e728f22291c2bd9c7728f25cc8a471a72bddca3c88a471ad67caf7728f22291c8e8af009dca3c9fb2291c67caf7728f222a574719f2dddca3c88a471ad2bc007728f22291c69caf001dca3c88a4719f2bc367 else if i < 5 then if i < 4 then 0x870f22291c67caf211dca3c88a471c001caf79988a4719f2bc4c059dca3c88a4719f34c007728f22291c8e8af001dca3c88a02d1c67caf7728f22291c67caf1a9dca3c88a471df2bc727000f22291c67caf71d9ca3c8c12291c69caf7728f27e88a470af651dca3c89f2291c67caf7 else 0x9be662291c67caf059de19988a4719f2bc16787e662291c67caf059e667488a4719f2bc167001ca3c89e4719f2bd9ca8d88a4719f2bc167001ca3c88a4e5b52bd9ca3c88a4719f3104c7728fb2291c67caf059dd53c88a4719f2bc167241ca3c88a4719f2bddca3c91c67caf210167 else if i < 6 then 0x728f27c11c67caf059dca3c9444719f2bc167728f232d1c67caf059dca3c88a4b19f2bc167729623ec8a4719f2bddca4288a4719f2bc4d7728f22291c67d592bddca3c8a74719f2bc167794f22291c67caf001dca588f22291c67ca37728f22791c67caf059dca3c88a471c02bc017 else 0x728f22291c6b4422bde1f728f24919f2bc16772a362291c67caf621e667288a4919f2bc167728f22292467caf059e1f999ca4719f2bc16787e293c91c67caf059dca4108a4719f2bc5f7728f27c08a9359f2bde1f728f24719f2bc167795ca3c88a95d9f2bddca3c8c22291c67caf7 else if i < 11 then if i < 9 then if i < 8 then 0x748f22291c69caf059dca3c88a471a72bc167728f222a5b4919f2bddca3c88a5ad9f2bc167775ca3c88a4719f2bddca3c9902291c67caf7728f22292867caf059dca3c88a4723a2bc5f79be173c88a4719f2bddca3c88a471c067cd379bcf22291c67caf6f1dca4d8fb2291c67caf7 else 0xa66293c88a4719f2bddca3c88a4719f310167728f24719f2bc8107ddca3c88a4919f2dc1678bdca3c9734719f2bde1f728f24719f2dc167748f22291c67cb7059dca3c88a4723a2bc167728f22291c6d4af059dca3c88a471c02bc167728f22291c6b4af059e1f728f2471a72bc167 else if i < 10 then 0x539ca3c91c67caf205dd23c88a4919f2bc167728f22291c2bd9807ddca3c97367caf17c1f79bdca3c88a4919f2bddca3c8cb4720e67caf7728f22291c67cd3059dca4c8f25cd9f2bc1f7728f27c11c67c072bddca3c8102293967caf7728f2829f04719f2bdc00729142291c67cd36 else 0x728f25cc8a4919f2bdde1728f22791c67caf7728fb7e88a4719f2bddca8d88a4719f2bc1f7729923c88a4719f2bde29728f22291c2c59f7728fb2291c67cbb2bde1f728f229d1c67caf7728f22291c67caf07ddca3c9202291c67caf7728f22291c67cd31b9c00764f22291c67caf6 else if i < 13 then if i < 12 then 0x754f25cd1c67caf07ddca3c9734719f2bc1f7728f22391c67caf07ddca3c8954719f2bc1f7729142291c67caf07ddca3c88a4720e67d587001ca3c88a5c19f2bda6f998f22297d67caf7729382297d4719f2bddca3ec8a4719f01caf7754f22291c67caf07ddca4c8f22292c67caf7 else 0x728f22291c6b4af07ddca3c88a471a72bc1f7728f22291c67cd42bddca3c9735f59f2bc1f7728f22293967caf07ddca3c9734a19f2bc1f7728fb2291c67caf005c00728f22291c67cc46728fb2292867caf07ddca3c88a4723a2bc2c772a403c88a95caf0f5dca3c88a4a19f2bc1f7 else if i < 14 then 0x768f22291c67caf1d9dca3c8a02291c67caf7728f22291c2bd880e5dd53c88a95d1c2bc1f7794f25cc8a4719f2bddca3c88a471f42bc5f77290a3c88a471b52bddca3c88a471f42bc1f7728f22291c67cfa2bddca3c88a471c02bc1f7729623c88a4e59f2bddca1b4f22291c67caf7 else 0x728f22291c67caf119e6f728f222a572bc1f7728f2229814719f2edde5728f22791c67caf7728f2229284719f2bddca588f260c8a4719f7729623c88a5ad9f2bddca70cf22291c67caf7728f2229804919f2bddca588f22291c67cd37729042291c67caf07ddca3c97322a572bc1f7 else if i < 22 then if i < 18 then if i < 16 then 0x729383c88a4719f2bddca3c88a4719f2ec1f7728f22291c67caf465dca3c88a4719f2dc1f7001ca3c8cb4719f34da1f730f22291c67caf7729785208a4719f2bddca3c89e4719f2bc02772a403c8a74719f2bddca3c88a38d1c67caf7001ca3c97395caf07d9ca3c88a4723a2bc1f7 else if i < 17 then 0x728f22297d4719f269dca3c9732291c67cb77728f22348a4719f2bddca588f229d1c67c4c7728f229d1c67caf0f5e663c88a4e51c67caf77288a4719f2bce70b1dca3c88a4720e0f42c7728f222a57470af0a1dca3ec8a4719f2bc287764f22291c67caf0a1e66728fb2291c67caf7 else 0x728f22551c8399f2bdc00728f23011c67caf6728f22291c0299f2bddca3c8a75f51c67caf7728f25cc8a67c622bddca3c9fa2293967caf7728f22291c67dba2bddca8d88a4719f010af7768f222a574719f2bddca3c88a5bd9f2bc817728fb2291c67caf0e5dca3c8c12291c67cb77 else if i < 20 then if i < 19 then 0x729663c88a4719f2eddca3c9f02291c67e047729142291c67caf0b1dca3c88a4e59f01caf77290a2291c67caf0b1de1728f22291c67cc47729042291c67caf0b1dca3c88a471f42bc2c785cf22291c67caf0b1dca3c9682291c67caf7748f22291c67caf0b1dca3c88a02d1c700af7 else 0x728f22292c67caf0b1dca3c88a5f64d67caf7728f22292867caf0b1dca3c8a74719f2bc2c7729622551c67caf0b1dda3c8954719f2bc2c7728f22291c6b4af621dca3cc8a4719f2bc2c787dca5208a4719f2bddca8d88a4719f2bc2c772a843c88a4719f811dd2588f22291c67caf7 else if i < 21 then 0x729042291c67c042bddca3c9444719f2bd887728f22293967caf005dca3c9ff2791c67caf7728f22296b67caf0b1e173c88a5ad9f2bc767998f22291c67caf16ddca3c88a4719f2bc4e7728f22552c67caf0b1dca5888a4b19f2bc2c7728f22291c69caf17dc00728f22291c8f8af6 else 0x728f25111c67caf0b1dca3c88a4720e2bc2c7728f22291c680af0b1dca3c88a471c02bc2c7728f22291c6b4af0b1dca3c88a471a72bc2c7728f23908a4719f2bde663c88a4719f2bdb17728f22296b67caf005d4e728f22292867caf7728f22291c67cd3005dd53c88a4719f2bd947 else if i < 26 then if i < 24 then if i < 23 then 0x729622291c67cc40b1dda3c88a4719f3102c7728f22291c67cc40b1e667288a4719f2bc177539ca3c88a471f42bddca3c88a4719f2ec2c7729622291c67caf3b1dca3c9f002d1c67caf7974f22291c67c072bddca3c88a4723a010af7729042291c6b4af0f5dca5888a4720e2bc2c7 else 0x728f22291c8399f2eddca901482291c67caf7728f22291c69caf621dca3c91c67caf1d8287998f22291c6d59f2bddca588c12291c67c2c7728f22291c67e040b1dca3c88a4719f208af7729535cc8a4719f2bddca588f22291c7e0af7728f203c8a4719f2bddca3c88a4719f34c2c7 else if i < 25 then 0x728f25111c67caf07de29728f22291c8382c7728f23048a4720e0b1dd53c8102291c67caf772a367c11c67caf621dd0728f22291c67caf7728f222a4d67caf005e66728f22291c67cd37728fb2280b4719f2bddca3c8954b11c67caf772932900f222a572bdc00729623c88a4e59f6 else 0x728f22548a4719f2bddca3c88a4719f811887728f26888a95d1c2bdcf22291c8399f2bdc77539ca3c97395d9f2bdd4e7288a4719f2bce77728f20408a4719f811dca3c8954719f2bc3578a5ca3c88a4719f2bddca5208a5f51c67caf7778f22291c67caf0d5e6fa70f22291c67caf7 else if i < 28 then if i < 27 then 0x728f22291c67caf6b1dca3c88a4719f2bd937728f222a4d67caf059e5d3c88a4719f2bc167729622291c67caf0e5dca3c9fa2292867caf772a362291c67caf371de1998f222a57470af7728f53c88a4719f2bdd4e728f25111c67caf7728f22291c67cc70d5c0098cf22291c67caf6 else 0x728f28508a4719f2bde72748f22291c67caf77290a2291c67caf0f5de54108a4719f2bc3d7754f22291c67caf0f5dca3c88a4720e2bc397728f22291ca159f561dca3c88a4d59f2bc397728f22551c67caf0e5dca3c88a7051c67caf79c1ca3c88a4719f2bddca3c9fa2291c6b4af7 else if i < 29 then 0x728f25cc8a67cd32bddca4109e4719f2bc3d7728f22291c67c082bddca3c89e4719f2bc3d772a362291c67caf0f5dca3c9734719f2ec1f7728f25f88a4719f2bddca3c88a4719f090af7728f2228264719f2bddca5208a4719f2bc3d7001ca4108a471ad2bda1c728f22291c67caf7 else 0x728f25488a4719f2bddca3c88a4c19f2bc357729063c88a4719f2bdc00728f22291c67d5c6728f23048a4719f2bddca3c88a4720567caf7729623c88a4719f811dca3c88a471a067caf785cf20408a4719f2bddca3c88a95d1c700af7728f22291c67caf401d4e728f22291c69caf7 else if i < 45 then if i < 37 then if i < 33 then if i < 31 then 0x728f227a5767caf0f5e663c88a4719f2bc4c7728f22291c8e8af371dca3c88a9359f2bc3d7728f20408a4919f2bddca3c9f04719f2bc3d7728f25111c67caf0f5de1738f22291c67caf7728f232d1c67caf0f5e6f768f22291c67caf787dca3c9735f59f2bddca3c88e3051c67caf7 else if i < 32 then 0x728f222a6d67caf6c5c0072a4a2291c67caf6728f22291c6d4af0f5dca3c88a95d1c08caf7975323c88a4719f2bddca3c9792292c67caf7768f25cc8a4719f2bddd53c88a5f51c67caf7728f22291c718af1b9c00729482291c67caf6728f22292467caf621dca3c88a471ad2bc3d7 else 0x85cf22291c67caf131e66728f22291c6b4af7728f2228cf4719f2bdde53c88a4719f2bc4c7768f22291c67caf131dca3c88a4719f2bc4a7728f22291c67caf121de53c88a4720e67c3d7761ca3c88a4719f2bddca3c88a470b167c3d7728f22291c700af0f5d4e72a4022a57470af7 else if i < 35 then if i < 34 then 0x754f22291c67c072bddca4508a4719f2bc4c79990a2291c67caf131dca3c88a7d91c67caf785d623c88a4719f2bddca3c9fa2291c67e0477292f3c88a4719f2bde6f728f22291e67caf77290a2291c67caf131dca3c9f095d1c67caf7729042291c67caf131dca3ec8a4719f2bc4c7 else 0x974f22280b4719f2bde667290a2291c67caf7728f24720e67caf21ddca3c88a471a7010af7728f28288a4719f811dca3c88a4a19f2bc4c7728f232d1c67caf131e663c8a74719f2bc4c7729213c88a4719f2bddca3c89e4719f2bc4c7728f22291c67d7b2bde665888a4719f2bc4c7 else if i < 36 then 0x794f22291c67caf0b1cff728f22291c67caf7728f28408a4719f2bde17729482291c67caf7728f22280b9359f2bddca3c88a471a72bc4c7002665888a4719f1319ca3c8a74e59f2bc4c7728f22292867caf371dca4288a4e59f2bc4c7998f22293967caf131dca3c88a4b19f2bc4c7 else 0x728b53c88a4719f131dca3c88a4719f2dc4c7728f22291c7d0af131e2d728f22291c67caf7728f22291c67c192bdde187cf23051c67caf7728f25d48a4719f2bddca3c8382291c67caf7728f25cc8a4719f2b1e20728f22291c67caf772a4a2291c67caf6f1dca3c89e471ad2bc3d7 else if i < 41 then if i < 39 then if i < 38 then 0x1ca3c9f94719f2bd9e53c88a4719f2bc5b79be663c88a95d9f2bddca3c88a4719f2bc5b772a3622a4d67caf621e173c9fa2291c67caf772a403c88a471b52bddca4c9482291c67caf7768f22291c838af0b1dca3c88a4719f2bc577539ca5888a4719f131e66588f22291c67c4c7 else 0x728f22297d471b52bddca3c8972291c67caf7748f22291c67caf17ddca3c88a67caf4005f7728fc3c88a4719f2bddca5208a471f467caf7729623c88a4719f16ddca3c88a6a51c67caf772a462291c67caf6c5dca3c88a471bb2bc5b7728f222a774e59f2bddca3c88a4719f188af7 else if i < 40 then 0x729482291c67caf17ddca3ec8a4719f2bc5f79bdca3c88a4b19f2bddda728f22291c67cc4785cf22291c67c072bde1f3c88a4719f2bc5f7728f22291c3559f2bde66728f22291c67e04785cf22291c67caf17ddca588f22291c6d44c7728f22292c67caf3b1dda3c88a4719f2bc5f7 else 0x999ca2291c67caf0a1e6f8a4f22297d67caf787cf23051c67caf17ddca3c9444719f2bcdc77291432d1c67caf17de6f728f22291c700af787cf25cc654719f2bdde199a402291c67caf787cf232d1c67caf17ddca3c89e4719f2bc5f772a863c88a95d1c2bddca3c88a4919f01caf7 else if i < 43 then if i < 42 then 0x21f3c97367caf17d9ca3c9732291c700af7001ca3c89e471ad2bd9ca3c88a471b501caf7729145cc8a67caf17ddca3c9732299f2bc5f787dca3c91c67caf205dca3c9734719f2bc287728f22292467caf005cf22291c67caf620727728f22296b67caf17dc00754f25cd1c67caf6 else 0x728f22292c67cc40b1dca3c88a4719f34c5f7728f22291c67caf21ddd54c8f22291c67caf7728f22291c67cc417ddca3c88a4719f2ec5f7728f25cc8a700af17ddca4508a5f51c67caf7728f232d1c700af17ddca4508a471c02bc5f787dca4c8f25cd9f2bde1f3c88a471c02bc5f7 else if i < 44 then 0x99a173c88a4719f2bdc00728f22293067caf6728f2199732299f2bdc00795042291c67caf6909ca3c88a4719f2bddca3c88a471a72bcdc787cf22291c67caf1b9de53c88a95d9f2bc3d7728f22291c67caf1a1e1f3c88a4719f34c5f787dca3c91c67caf0d5dca900f42291c67caf7 else 0x728f22588a4719f2bddca3c88a4719f2bc767729623c88a4719f1c9dca3c88a4719f34c727728f25cc8a67caf1c9e663c88a4719f2bc727728f22291c67caf1c9dca3c88a4720e67c6e7729623c9fa2291c839dca3c9732299f2bc6e7728f222a5767caf1b9e29728f27c11c67caf7 else if i < 52 then if i < 48 then if i < 46 then 0x2613c88a4719f2bd9ca4108a4719f2bc767794f22291c67c042bddca3c9fa2291c67cb77974f22291c67caf1d9e29728f22291c67ca378a5ca3ec8a4719f2bddca3c88a5ad1c7d0af7895ca3c8954719f2bddd23c88a4719f2bc76785cf22291c67caf1d9c00728f22291c67d7b6 else if i < 47 then 0x728f22292467caf1d9dca3c9f04719f2bc767728f232d1c67caf1d9dca3c89e4719f2bc767728f22551c67caf1d9dca3c8a74720e67caf7974f222a574719f2bddd53c88a02d1c67caf7729143c88a4719f2bddca3c88a95e4d67caf79bdca3c9f04719f2bddca3c8cb2291c67cd37 else 0x728693c88a4719f2bddca3c8c17c11c67caf7771ca3c88a4719f2bddca900f232d1c67caf7728f22291c67cb71d9dca844f22291c67caf772a362291c67caf131dca3c88a4723a2bc767728f25cdf04719f2bde173c88a471f42bc767728f22291c700af1d9dca3c88a9359f2bc767 else if i < 50 then if i < 49 then 0x728f22291c67cb7205dd23c88a95d1c67caf77290a229394719f2bdd4e729624719f2bc817999ca2291c67caf205dca3c88a4e59f2bc007729482291c67caf205e1b3c88a4719f2bc817728f2228564719f2bddca900f22291c67d58772a453c88a4719f2bddca3c88a4719f310767 else 0x728f22291c67caf3bdd4e728f32291c67caf7001e53c88a95d9f2bd9ca588f22291c8382e7728f22296b67caf001dca3c88a5f51c77caf7729142291c67caf059dca3c88a4719f5603d7729623c91c67caf21ddca3c88a471f42bc847728f25cd1c67caf211dca3c88a4719f2bc847 else if i < 51 then 0x729532291c67caf269e283c88a4719f2bc9a7728f22291c67caf269dca528f22291c67caf7728f22a48a4719f2bddca3c88a4719f2bc927728f22291c67caf621dca3c88a4719f08caf7001ca3c91c67caf21d9ca3ecc12291c67caf772a403c91c67caf21ddca3c88a4719f89caf7 else 0x728f22291c67caf28ddca901042291c67caf70026f8a4f22297d67d9ca3c88a95d9f2bc9a79bdca900f222a572bddca3c8cb4719f01caf7728f22296c4719f2bde66728f22291c67cb77728f22296b67caf269de53c89e4719f2bc3d79cdd53c88a4719f2bddca3c89e4719f2bc9a7 else if i < 56 then if i < 54 then if i < 53 then 0x768f22291c67caf371dd23c88a4719f2bcdc787dca3c88a4719f2b1dca3c88a4719f2bcac7728f22291c7d0af1e1c007288a4719f2bcef6728f2532574719f2bddca3c88a5f19f2bca37728f22291c67cd3131dca3c97322d1c67caf7998f22291c67caf28ddca3c88a4719f2bc187 else 0x754f22291c67caf1d9dca3c88a4723a2bc3d7728f27e88a471a02bddca3ec8a4719f2bcdc7974f22291c67caf371ea5728f22291c67caf7786664c88a4719f2bddca488f22291c67caf7728f229c8a4719f2bddca4108a5f51c67caf7794f22291c67caf371dca4108a4719f2bc3d7 else if i < 55 then 0x728f22280b471b52bde1f728f22291c7d0af7728f22291c67caf0b5dca3c8cb4719f2bcdc7728f22791c67caf371dca5208a4719f2bcdc7729042291c67caf371dca5208a4720e67caf78a5ca3c88a5ad9f2bddd23c88a4719f2bc007728f22292867caf001e29728f22291c67cd37 else 0x729622291c67c302bddca3c88a9359f2bcdc7728f22296b67caf371dca4288a471b567caf7728f22291c8f8af39de1f728f24911c67caf7001ca8d88a4719f2bd9ca3c88a4719f2bca57728f27c11c67caf371dca3c88a4719f2bd107974f25111c67caf371dca3c9732299f34c5f7 else if i < 58 then if i < 57 then 0x984f22291c67caf39ddca3c88a4719f2bce77728f22291c67e04371dca3c88a4719f18caf7728f22291c67d58371dca3c88a4719f560167728f22291c67cc4371dca3c9444723a2bcdc7728f22291c7d0af371dca3c88a471c02bcdc7728f22291c6b4af371d4e728f22291c67caf7 else 0x728f27e88a4719f2bddca3c8955f51c67caf772a402291c67caf3b1e633c88a4719f2bcec7729142280b4719f2bddca3c8c12293967caf7974f22291c67d58371dca3c88a4719f2bcec7728f22291c67caf3a9e1f3c9732299f2bc5f79a1ca3c88a4719f2bddca3c88a4719f570e77 else if i < 59 then 0x728f222a5767caf0f5dca150f22291c67caf772a863c88a4719f2bdde53c88a4719f2bd887768f22291c67caf621e9c728f22299f2bd1979be663c88a67caf441dca588f22297d67d0079b8f22291c67caf401dca3c88a4719f57cec7729483c88a5ad9f2bdd4e728f22391c67caf7 else 0x974f22291c67caf621e173c88a4719f2bd88786d623c88a4719f2bde6f974f22291c67caf7728f24388a4719f2bde29748f22291c67caf772a8c2291c67caf3bddca3c88a471a72bc357a51ca3c88a4719f2bddca2291c67caf370357728f24988a4719f2bde283c9732291c67caf7 else if i < 90 then if i < 75 then if i < 67 then if i < 63 then if i < 61 then 0x728f232d1c67caf621e1f728f22791c67caf7728f229d1c67caf621c00728f22291c8e8af6729482291c67caf621e5d3c9732291c67caf7728f22291c6b4af131e66729622291c67c4c7728f25cc8a9359f2bddca4108a4719f2bc167729142291c67caf621dca4288a4719f2bd887 else if i < 62 then 0x974f22291c8e8af371dca3c88a4719f010af7728f22291c67cb7621dca3c88a471f42bd887728f22291c700af621dca3c88a9359f2bd887729323c88a4719f561dca3c88a5ad9f2bd887728f22292867caf621cf9728f22291c67caf7768f27e88a4719f2bddca3c9442291c8e8af7 else 0x72a362291c67e04621dd23c9732291c67caf7728f22291c67d58621dca3c88a4719f34d887728f25cd1c67cbb2bde29728f22291c6b4af7728f22291c8399f401dca3c88a5f11c67caf7728f22291c5699f2bddca3c88a471b52bc767728f25111c67caf131dca900f22291c67cbb7 else if i < 65 then if i < 64 then 0x729623c88a4b19f2bddca900f22291c2bd98772a483c88a471b52bddca3c9f94719f2bd98772a362291c67caf661dca3c88a9499f2bd947728f22297d4719f2eddca3c9734719f2bd947748f23048a4719f2bddd2728f22291c69caf7728f22291c67caf651dca3c88a9359f811887 else 0x728f22291c67e046c5dca3c8954719f2bc167729a53c88a4719f2bddca3c88a470af6502c7728f22291c6d4af6c5e293c88a4719f2bdb17728f22291c67caf6c5dca3c88a4719f810007a45ca3c88a470af671e66728f22291c2bd9c7001ca3c88a470af6719ca3c88a4719f2bd9c7 else if i < 66 then 0x728f232c654719f2bdcf22297d4719f2bdc779bde1728f222a572bddca3c8c92291c67cc47729142291c67caf1d9dca3c88a471c02bdbc772a403c89e4719f2bdc00728f23411c67caf687e663c91c67caf059dca3ca144719f2bdbc78a4f22291c8399f6c5dca3c88a4719f668af7 else 0x754f22291c67cbb07dc00768f22551c67caf6728f22291c67caf801c00728f22291c7d0af6729623c88a471c02bddca3c8982291c67caf7728f25311c67caf3b1e66768f22291c67caf7728f22291c67c072eddca8d88a4719f2bc027728f22298e4719f2bdde1728f22291c8e8af7 else if i < 71 then if i < 69 then if i < 68 then 0x728f22551c67caf005e173c88a4719f2bc017728f22291c67caf24ddda3c88a4719f2bc017748f22291c67caf005dca3c88a4719f2bc017728f22291c67caf925c00728f22291c67cc86728f25cc8a471fe2bdc00998f22293967caf6785ca3c97322a572bddca3c89e5f51c67caf7 else 0x728f22291c67d58005dca3c88a4719f310017728f22291c69caf005dca3ca132291c67caf7728f27c11c67caf621dca3c88a4a19f2bc017728f27c11c67caf005dca3c9fa2292c67caf787dca3c88a4719f311dca3c9444719f2bc017728f229d1c67caf005e6f8a4f222a5767caf7 else if i < 70 then 0xa75ca3c88a4719f2bddca3c88a4719f2bc3e7729622291c8399f0b5dca3c88a4b19f01caf7728f22292467caf001dca3c88a4719f3102d7728f22291c67e04005dca3c88a4720e2bc357728f25cd1c67caf0e5dca3c88a95d282bc1f785cf22291c67caf001e29728f22291c67e047 else 0x728f27e88a471c02bddca8d88a4719f2bc5f7728f22291c67cd3009de1728f22292867caf7728f22291c67caf26ddca3c88a4719f2ec167728fb2291c67caf621dca3c88a4719f2bc5c7729623c88a4719f135dca3c88a4719f2bc4d7001ca3c9444719f2bd9ca3c88a4720e67c3e7 else if i < 73 then if i < 72 then 0x728f222924471a72bddca3ec8a4719f2bc2c7728f22291c67caf291dcf8a4f22291c67caf7728f20cc8a4719f2bddca3c88a4719f2bcdc7754f25cc8a4719f2bddca04cf22291c67caf75a9ca3c88a4719f2bddca3c88a471b52bc4e7728f22292c67caf005dca3c88a4724b67caf7 else 0x728f22291c67caf3a1e6f754f22291c67caf7785ca3c88a471f42bdcf22291c67caf6c45f7728f22291c67d581d9c00870f22291c67caf6728f22292c67c302bddca3c89e2291c6b4af761dca3c88a4719f2bddca3c88a4719f2bd897768f22291c67cc42bddca3c88a4719f2bcdd7 else if i < 74 then 0x728f22292867caf009dca3c88a4919f2bc027728f25111c67caf009c00728f25cd1c67cbb6728f229d1c67caf009dca3c8c12291c67e047001ca8fc8a4719f2bd800728f22291c69caf6728f22551c67caf009dca3ec8a4719f2bc027728f22291c67caf009dca3c88a4719f2bdb47 else 0x1ca3c8a7471b52bd9ca5348a4719f2bc847241ca3c9734719f2bddca3c88a5f51c67cc47728fb2291c67caf07ddca3c88a4719f3103d7728f22293967caf17ddca3c88a471f567caf7729854508a4719f2bdd4e728f27c11c67caf7a45ca9008a4719f2bddca3c88a5ad9f2bc027 else if i < 82 then if i < 78 then if i < 76 then 0x728f22291c838af0b9e5d3c88a4719f560af7539ca3ec8a4719f2bddca3c9202299f2bc5f7728f22291c67caf0b9dca3c88a4719f560027728f22291c67cc4009dca3c88a471f42bc027241ca3c8c14719f2bddca450f22291c67cd37539ca901fa2291c2bddca3c88a471c02bc027 else if i < 77 then 0x87d143c88a4719f2bde2e794f22291c67caf7728f22291c8399f0fddca3c88a4719f3102e7999ca3c88a471c02bdde1728f25111c67caf7728f22291c6b4af0fddca3c9fa7c11c67caf7728f22291c67cb7001e1f8a4f22291c67ca37728f222a574719f561dca4c8f22291c67cbb7 else 0x728c63c88a4719f2bddca3c88a4719f2bc407728f22291c67caf00ddca3c88a4719f2bdc57728f22291c67caf665dca3c88a6052867caf7728f22291c67e04629e1f3c88a471c067caf7728f22291c67caf629dca3c88a4719f2bd037728f22291c67caf185d4b728f22291c67caf7 else if i < 80 then if i < 79 then 0x785ca3c88a471a72bddca3c88a02d1c67cbb7729323c89e4719f2bdde1728f222a9e470af7728f22292867cbb2bddd53c88a4719f2ecaf7729053c88a4719f2bde667288a4719f2dcaf7748f22291c67cb72bddca3c81029d1c67caf7728f22291c67caf1e5dca3c88a4e59f2bd887 else 0x728f22291c8e9582bddca3c8cb4719f34caf7729142291c67cd32bddca3c88a4719f320af7728f22291c67cc72bddca3c88a4719f2bcca7728f22292c67cc42bddca3c8954719f310af7728f22293967caf0b1dca3c88a471ad2bc027728f22291c67cc42bddca3c88a4719f2fcaf7 else if i < 81 then 0x728f25111c67c042bddca3c8a74719f010af7728f22551c67c042bddca4508a4719f010af77290a2291c67c042bddca3ec8a4719f010af785cf22291c67c042bddda3c88a4719f010af7748f22291c67c042bddca3c88a4719f57caf7728f22291c67d5c2bddca3c88a4a19f2bc5f7 else 0x728f26f88a4719f2bdc00728f23491c67caf6751ca3c88a4719f2bddca3c88a4719f634af7998f22291c6d4af131dca3c88a471f4010af7974f20408a4719f2bddca3c9a32291c67caf77290a2291c67caf009dca3c9fa22d1c67caf7728f22292c67c042bddca19cf22291c67caf7 else if i < 86 then if i < 84 then if i < 83 then 0x728f25cc8a95e0e2bddca3c97395d9f088af77290f3c88a4719f2bddca3c88a4a19f088af753dca3c88a4719f2bddca3c88a4720e8e8af7728f25cd1c67c222bddca3c88a4719f088af787dca3c91c67c192bddca2d4f23048a4719f7728f222a57470af211dca588f229d1c67caf7 else 0x728f22291c69caf009dca3c88a471ad2bc5f7728f25cc8a67caf6f1dca3ca7d5111c67caf7728f22291c67cd307ddca3c88a5ad9f2bc1f7729482291c7d0af1d9d4e728f22293967caf772a863c9fa2291c2bddca3c88a95d1d67caf78a5ca3c9fa2291c839dca451732291c67caf7 else if i < 85 then 0x729623c88a9359f2bddca3c9f06391c67caf7001ca3ec8a4a19f2bd94e728f22296b67caf77cdca3c88a4719f2bddca3c88a4719f2bd517539ca3c88a4719f34ddca3c89595d1c67caf7728f27fc8a471ad2bddca3c88a471b567caf7748f22291c67caf621cf222a9e4719f2bdc77 else 0x7290a2291c67caf17ddca3c88a4719f2bc787728f22291c67c6f2bddca3c88a4919f064af7728f22291c67c502bddca3c88a95d9f104af7728f22291c67c412bddca3c9444719f2bc5f7001ca43c8a4719f2bd9ca3c88a4719f0bcaf7778f27e88a4719f2bde5d588f22291c67caf7 else if i < 88 then if i < 87 then 0x728f25111c67cdf2bddca3c88a4719f2ec767728f22291c67cd12bddca520102291c67caf7974f22291c67caf441dca4108a4720e67c3d7728f22296b67c7a2bddca3c88a4719f1e8af7728f2852574719f2bde1f3c88a4719f2bd10772a453c88a471ad2bddca3c8e92291c67caf7 else 0x728f22291c67c062bddca588952291c67caf7728f28051c67caf6c5dca3c88a4723167cd37728f22291c67c472bde1f728f22391c67caf7728f27e8c12291c839dca3c88a4719f014af7728f27e88a4719f31ddca3c9fa29d1c67caf7728f22291c67dbf2bddca3c88a4719f404af7 else if i < 89 then 0x728f22291c839f42bddd23c88a4719f01caf7728f22291c67cb82bddca3c88aa2d1c7d0af7728f22291c67caf509e1f999622291c67caf79bdca3c8cb4719f2bddca8d88a4719f810af7728f22291c67cb02bde6a728f22291c67caf7729323c88a4719f311dca3ecf22291c67cbb7 else 0x728f222a4d67c072bddca3c88a5ad9f01caf7728f229d1c67c072bddca3c8954719f01caf7729142291c67c072bddca4108a4719f01caf7794f22291c67c072bdde8728f22291c67caf7974f27e88a4719f2bddca3c88a4e59f010af7728f2a308a4720e2bddca930f22291c700af7 else if i < 105 then if i < 97 then if i < 93 then if i < 91 then 0x728f22291c700632bde1f3c88a4719f18caf7728f22292867c232bddca588f22291c67c4e7728f22296b67c042bddca3c88a4720e2bd987728f22291c67e0417ddca3c88a471f401caf7728f22291c69c072bdd4e728f52291c67caf79bdca3c88aa799f2bddca3c88a4b19f2bc767 else if i < 92 then 0x728f22291c67cdf2bddca3c88a4723a560dc7974f22291c67caf005e667288a471a767caf7748f22291c69d9f2bddca3c88a4719f658af7728f22291c67caf131dca3c88a4723a380af70025d3c88a4723a2bd800728f22292c67cc46728f22291c67ce02bddca3c88a4719f1c0af7 else 0x728f22292469d9f2bddd53c88a4719f2bd887728f22291c92caf441c00729042291c8399f6999ca3c8a74719f2bddca3c88a95e0e67c3d787dca3c91c69d9f2bddca3c97395d9f2bc1f7728f222a57838422bde1f728f24719f2bce77001ca3c973229c02bd8f222a574719f2bdc77 else if i < 95 then if i < 94 then 0x728f222a574b19f2bddca4288a4719f2bc1f7728f22291c77d9f2bddca3c88a471c667caf7728f22291c7019f2bdc00729623c8a74719f655dca3c8a74719f2bddca3c88a83d1c67caf7728f2a288a4719f2bddca3c88a4719f2bd377794f22291c6b59f2bddca3c88a4724467caf7 else 0x974f22291c8e99f2bde76728f222a5767caf7728f22292867c042bdde53c88a4719f2bc027728f22291c8099f2bddca3c88a471fe67caf7728f22296b7d19f2bddca3c88a4ad9f2bc28785cf22291c7d19f2bddca3c9822291c67caf7728f22291c7d19f2bdde1728f22291c8383d7 else if i < 96 then 0x85cf22291c8399f2bddda3c88a4720e67caf79bdca3c88a4759f2bddca3c88a471b667caf7728f22291c6b99f2bddca3c88a471a867caf7001ca3c88a5adf42bd9ca3c88a470e167caf7728f2229bd4719f2bde66974f22291c67caf7999ca3c88a9359f2bddca3c88a470b167caf7 else 0x728f23491c67caf1c9dca3c89e4720e67caf7729142291c8399f2bddca4288a4720e67caf7431ca3c88a4719f2bddca4108a4720e67caf7732663c88a4719f2bddca3c88a95dad2bc3d7974f22291c8399f2bddca5208a4719f01caf7870f22291c8399f2bddca3c88a4919f2bc5f7 else if i < 101 then if i < 99 then if i < 98 then 0x728f22291c67cb7009e1a728f22291c67caf7729482291c67caf005dca3c88a4721267caf7728f222a4d8399f2bddca3c88a5c20e67caf772a4a3c88a4719f2bddca3c88a4e60e67caf7728f22292c8399f2bddca3c88a4a20e67caf7728f28051c8399f2bddda3c8952291c67caf7 else 0x728f22291c67cd3371e1f998f25cd1c67caf7728f22291c6b4042bdd4e729734719f2bce77728f22291c10d9f2bddca3c88a4719f8101f7999ca3d48a4719f2bddca3c88a4723b67caf7728f22291c8c59f2bddca3c88a4719f560dd7728f22293967caf371dca3c9462291c67caf7 else if i < 100 then 0x87dca3c88a5f19f2bddd53c88a4a11c67caf7728f2229244719f2bddca588f2228524719f7539ca3c88a4719f811c0072a362291c67e046728f22299b4719f2bdde53c88a4719f2bc5f7728f25ccc167caf17ddca3c88a67caf4403d7728f22292c67caf001dca3c88a4706467caf7 else 0x728f22291c6d4af621dda3c88a4b11c67caf7728f22292c4719f2bddca3ec8a4a11c67caf7728f22292467caf0b1dca5208a4719f2bc167729142291c7019f2bdd7a728f22291c67caf7728f229c0b4719f2bddca3c89e4720e67c3d7728f22291c8399f2c1dca3c9f09359f2bd887 else if i < 103 then if i < 102 then 0x728f22551c67cc40b1dca3c88a4751c67caf7728f222a6d4719f2bddca8d88a9351c67caf7729482296b4719f2bde173c88a5ad1c67caf7999ca3c88a4724b2bddca690f22291c838af787dca3c91c67cb72bdce6728f22291c67caf7728f22296b4719f2bddca3c88a4e51c67caf7 else 0x754f22291c67caf005dca3c88a1f11c67caf7728f22293a4719f2bde6672a5c2291c67caf787dca3c88a470af671dca3c88a4719f2dc5f7728f22291c67ceb2bde6f728f22291c6ecaf785cf22291c67caf07ddca3c9524719f2bd007728f22292d4719f2bddca3c8102291c6d4af7 else if i < 104 then 0x754f222a574719f2bddca450102291c67caf78a5ca3c88a4b19f2bddca3c88a95d1c67caf7728f22291c8399f311dca3c88a4919f2bc1f7728f222a4e4719f2bddca3c89e2291c67caf7728f22296d4719f2bddca3c88a4ed1c67caf7728f22292e4719f2bddca9f9482291c67caf7 else 0x7291422a574719f2bddca4288a95d1c67caf7539ca3c88a4919f2bddca3ec8a95d1c67caf785cf222a574719f2bddca3c8952292c67caf7794f222a574719f2bddca3c88a471c02bc4c7729623c88a471b52bddca3c8954720e2bc2c7728f25cc8a4719f2eddca3c88a95d1c2bc1f7 else if i < 113 then if i < 109 then if i < 107 then if i < 106 then 0x728f222a774719f2bddca3c88a96d1c67caf7728f232e574719f2bddca3c8a795d1c67caf7728f25111c67caf39dde1728f22291c67caf7728f22291c67c04811dca8d88a95d1c67caf78a9ca3c88a4719f2bdc00728f28051c67caf6728f22291c67c1a2bddca588f22291c8382c7 else 0x728f232d1c7019f2bdc00728f22291c67cac6001d23c88a471a72bd9ca3c88a5f51c67caf73e1ca2291c67caf059dca3c88a0ad1c67caf7999d53c88a4719f2bde29728f22291c700af7728f22291f4719f2bde6f728f22791c67caf70021f728f24919f2bd9ca3c88aa2d1c67caf7 else if i < 108 then 0x728f22291c67caf175dca4108a4719f2bc3e7729624508a4719f2bdc00729622291c8382c6728f22291c67cbf0a1dca8d88a5f51c67caf7974f22297d4719f2bddca3c88a4719f2bc3f7728f22291c67cb70b1de53c88a4719f2bc1f7728f27c11c67caf001dd23c88a5f51c67caf7 else 0x729493c88a4719f2bddca3c8ee2291c67caf7999ca2291c67c192bddca3c88a4719f0a8af7728f2229844719f2bddca3c8d25f51c67caf7728fe3c88a4719f2bddca3c8c12292c67caf7728f2229354719f2bddca3c88a471bb67caf7728f229d1c67caf1d9dca3c8cb5f51c67caf7 else if i < 111 then if i < 110 then 0x728f232c0b4719f2bddca3c89502d1c67caf7728f27c11c67caf131e173c88a02d1c67caf7729142291c67caf441dca4288a4719f2bcdc7728f22291c67caf181dca3c8752291c67caf7768f22280b4719f2bddd23c88a02d1c67caf7729482280b4719f2bddca3c88a4e59f2bc5b7 else 0x728f229c524719f2bddca3c8102291c67d587728f2228524719f2bddca3c88a0c91c67caf7728f222a3c4719f2bddca3c88a4919f010af72a9ca3c88a4719f2bddca3ca8a7c11c67caf7728f2040cb4719f2bddca3c9730951c67caf7728f2228254719f2bde1f728f206d1c67caf7 else if i < 112 then 0x728f2229396d59f2bddca3c88a9491c67caf7728f23488a4719f2bddca3c88a2191c67caf785cf22287d4719f2bddca3c88a1f51c67caf7728f2228744719f2bdcf8729322291c67caf7728f22292c4720e2bde1f3c88a1951c67caf7728f22291c6d4af005dca3c88a1951c67caf7 else 0x794f22788a4719f2bddca3c8c122a574720e7728f29f48a4719f2bddca3c9f04719f811887729623c88a472442bddca3c88a1f91c67caf7728f22280e4719f2bddca3c88a4719f2bdee7728f2228b34719f2bddca451fa2291c67caf7728f280c8a471b52bddca3c88a1611c67caf7 else if i < 117 then if i < 115 then if i < 114 then 0x728f23008a4719f2bddca428a72291c67caf7728f222a5767caf0f9e663c8a72291c67caf7728f25788a4719f561dca4109e2291c67caf7728f22292c838af0b1dca5888a4719f2bc2c7768f22291c67caf009c00729312291c67caf6728f2229814719f2bdc00754f22291c67cbb6 else 0x728f22291c67caf17ddca3c88a4720e67c5b7729142291c67caf005e633c88a95d1c67caf7728f27c08a4719f2bddca3c94c2291c67caf7974f25108a4719f2bdd4e728f22293567caf7728f232c8a4719f2bddca3c8112291c67caf7002173c88a471f42bda6f728f22291c67cc47 else if i < 116 then 0x87dca3c88a4719f34ddca3c9f12291c67caf7728f22308a4719f2bddca3c8a82291c67caf7728f25d08a4719f2bde1f728f22293967caf7728f22291c67caf165c00729623c88a471b56728f25a11c67caf441e99728f22291c67cac7794f22291c6b4af0f5dca3c9f92291c67caf7 else 0x754f23048a4719f2bddca3d0f22291c67caf7728f22291c67caf379dca3c9fa4720e2bc847729482291c67caf1d9dca3c8b42291c67caf7975ca3c88a4723a2bde1f3c91c67caf17c167729622291c67c4c0b1e66729862291c67caf7729623c88a4719f561dca5888a4719f2bc2d7 else if i < 119 then if i < 118 then 0x85cf22291c67caf371e66729142291c67caf7799ca3c88a4719f2bddca3c88a471a72dcaf7728f260c8a4719f2bddca902362291c67caf7728f22291c67cd32bde29728f222a9e4719f7728f229d1c67caf001e8f728f25111c67caf7728f26dc8a4719f2bddda3c8c12291c67caf7 else 0x728f26888a4719f2bddca3c86b2291c67caf7728f23248a4719f2bddca8d8c12291c67caf7729483048a4719f2bddca3c9fa32d1c67caf7729624108a4719f2bde5d3c8c12291c67caf785cf23048a4719f2bdde53c8c12291c67caf787dca3c88a5ad9f2bddca3c9b32291c67caf7 else if i < 120 then 0x728f22551c67caf621e6f728f23011c67caf7728f25cc8a4719f2bddca3c88a4719f2bc2c7728f24f08a4719f2bde9585cf22291c67caf7728f23308a4719f2bddca3c8102551c67caf7728f22293967caf131dca3c88a4919f2bcdc7728f27088a4719f2bddca3c9aa2291c67caf7 else 0x728f22291c7e0af205dca3ed732291c67caf785cf25cc8a4719f2bdc00728fb2291c67caf672a4a22a574719f2bddca3c88a5ad9f2bc4c77294822a574719f2bddcb3c88a4719f2bc4c7728f22291c67c9a131e5d3c88a4719f2bc007728f222a4d67caf001de187cf22291c838af7 else if i < 181 then if i < 151 then if i < 136 then if i < 128 then if i < 124 then if i < 122 then 0x1ca3c88a491a72bd9ca3c88a2f91c67caf7728f26088a4e59f2bddca3ca4f2291c67caf7728f25e48a4719f2bddca3c88a4a51c67caf772a463c88a4719f2bddca3c88a2e51c67caf7729153c88a4719f2bdc00794f22291c6b4af648dca3c88a4719f2bddca3c8cb4719f2bc017 else if i < 123 then 0x728f222a4d67caf131dd53c9fa2291c67caf7974f22291c67caf131dd23c9fa2291c67caf78a5ca3c8a74719f2bddca3c9202297d67caf7728f22296b67caf0f5dca3c88a95d1c8383f7728f22291c67caf155dca3c88a4719f34c3d7768f22291c67caf0b1dca3c88f2291c67caf7 else 0x728f28588a4719f2bdde1728f27c11c67caf7001ca9188a4719f2bd9ca3c9ff2291c67caf7729487e88a4719f2bddd7728f22291c67caf7728f22291e4719f2bddca429fa2291c67caf7729047e88a4719f2bdde53c9fa2291c67caf7728f222a57470af085d4e72a405cd1c67caf7 else if i < 126 then if i < 125 then 0x999ca0748a4719f2bddca3c88a4723a01caf7748f20748a4719f2bddca8d8102291c67caf7729040408a4719f2bde1f728f22291c6b4af7728fb0408a4719f2bde66728f232d1c67caf7768f20408a4719f2bddca3ec8a95d1c2bc1f7748f20408a4719f2bddca3ca592291c67caf7 else 0x729620cc8a4719f2bde1f728f25111c67caf7728f22291c67cb7371dca4108a4719f2bc01787dca3c97395d9f2bddca3c88a4719f2ed887729043c88a4719f2bddda3c88a4719f2bc1f7748f22291c67caf131d4e728f25cd9f2bc5f7780f22291c67caf0e5dda3c8332291c67caf7 else if i < 127 then 0x769ca3c88a4719f2bddca3c8532291c67caf7728f22292867caf0f5dca3c8102291c67cbb7539da3c88a4719f2bde5d728f25111c67caf787dca4288a4719f2bdde1728fb2291c67caf79d1ca3c88a4719f2bddca3c88a4723a2bc017728f21148a4719f2bddca900f22292867caf7 else 0x728f22291c8f99f2bddca3c81e2291c67caf7974f23908a4719f2bddca3c88a471c02bc5f7728f21fc8a4719f2bde1f3c8662291c67caf7728f21988a4719f2bddca900f22291c7d0af79996214c8a4719f2bde30768f22291c67caf7728f263c8a4719f2bddd6728f22291c67caf7 else if i < 132 then if i < 130 then if i < 129 then 0x728f27c11c67caf009dca3c88a4b19f2bd887728f22291c7d0af0f5e6f730f22291c67caf7001ca3c88a471a72dda1f8a4f25cd1c67caf7891ca3c88a471f42bddca3c8e52291c67caf7728f20409e4719f2bddca968f22291c67caf7728f21c48a4719f2bddca3c8342291c67caf7 else 0x728f222a934719f2bddca3c81d2291c67caf7728f24a88a4719f2bddca3c88a1791c67caf7728f22291c69cb7059dd53ecf22291c67caf787dca8fc8a4719f2bde1f8a4f22297d4719f7728f23048a9359f2bddca3ecf22291c67caf772a503c88a4719f2bde1f728f22291c808af7 else if i < 131 then 0x754f2228254719f2bddca3c88a9dd1c6d4af772a403c9444719f2bddca3c88e2291c67caf787e663c9fa4719f2bddd53c88a4a19f2bc1f7728f22291c700d32bddca3c88a4719f2bc29772a4c4508a4719f2bddca428f22291c67caf7795043c88a4719f2bddca588f22291c67cbb7 else 0x728d73c88a4719f2bddca2e8f22291c67caf77285a3c88a4719f2bddca048f22291c67caf772a3f3c88a4719f2bddca8d8f22291c67caf7999ca5888a5f51c67ddca558f22291c67caf7729483c88a4719f2bddca4ca362291c67caf787dca3c88a4719f811e6672a862291c67caf7 else if i < 134 then if i < 133 then 0x728f22280b4719f561dca598f22291c67caf79b9623c88a4719f2bdd17728f22291c67caf7769623c88a4719f2bddd5588f22291c67caf7728f25cc8a4719f571dca3c88a4719f810af7748f2229244719f2bddca3c9445f51c67caf7729623c89e4719f2bddd5728f22292867caf7 else 0x754f22291c67caf131dca3c9fa2291c67cbb7001ca451732299f2bd800728f22292867caf6001d23c88a4719f2bda663c88a4719f2bc4e77290a2297d4719f2bddca3c9fa4719f2bc847785ca3c88a4e59f2bddca3c9f04719f2bc5f7999ca3c8954719f2bddca3c88a4b19f2bc1f7 else if i < 135 then 0x72a353c88a4719f2bddca3f4f22291c67caf772a843c88a4719f2bdde1728f22296b67caf772a373c88a4719f2bddca644f22291c67caf7785cb3c88a4719f2bdde1728f22291c67cd37539ca3c88a4b19f2bdc00728f22299f2bd196729485cc8a4719f2bddcf87cf22291c67caf7 else 0x728f63c88a4719f2bdc00998f229d1c67caf6729042291c6b59f2bddca3c88a471f42bc167728f22291c67cbb005dca6acf22291c67caf7729a43c88a4719f2bddca458f22291c67caf7728f22291c67e04131dca41cf22291c67caf7728f22297d471a72bddca3c88a471a72bc3d7 else if i < 143 then if i < 139 then if i < 137 then 0x728f73c88a4719f2bddca588f22291c67cb0776a403c88a4719f2bdc00728f22291c6b4af6729042280b4719f2bddd9900f22291c67caf7729643c88a4719f2bdde1728f2229a1470af7728f20408a4719f311e1f728f22292467caf7001ca3c88a471f82bda29754f22291c67caf7 else if i < 138 then 0x728f25111c8e99f2bddca5e0f22291c67caf7729413c88a4719f2bddca3c89e4719f01caf7729363c88a4719f2bde174c8f22291c67caf7795323c88a4719f2bddca4f4f22291c67caf772a7e3c88a4719f2bddca930f22291c67caf7976403c88a4719f2bde17900f22291c67caf7 else 0x729323c88a4a19f2bddd2728f22292467caf7001ca4288a4719f2bd9e5728f22291c67caf7755ca3c88a4719f2bddca054f22291c67caf772a5c3c88a4719f2bddca3c88a4e59f2bc027728f22291c67cc80e5dca618f22291c67caf772a543c88a4719f2bddca3c9f04719f2bc2c7 else if i < 141 then if i < 140 then 0x86dca3c88a4719f2bddca4288a4719f2bc1677291432c8a4719f2bddca8d8f27c11c67caf70026e3c88a4719f2bd9ca3c88a4719f82caf785dca3c88a4719f2bddca3c89e4719f2bc017999ca3c88a4719f2eddca3c88a2cd7d4719f73c88a4719f2bdbc131dca3c88a4719f0c4af7 else 0x2d9ca3c88a4719f2bddcc728f22291c67caf7999ca3c88a4719f2bddca3c88a9b60e67caf7728f22292467caf131e75728f22291c67caf7979ca3c88a4719f2bddcaa84f22291c67caf7861ca3c88a4719f2bde6e728f22291c67caf7985ca3c88a4719f2bddca3c88a47231700af7 else if i < 142 then 0x728f22291c67d8c2bddca3c88a9359f2bc027728f22291c67caf085e1f72a403c9fa470af7998f2228524719f2bde5d3c88a4719f2bc027001ca5348a4719f2bd9ca22a574719f2bcef7728f22297d67caf401dca3c88a3591c67caf77290b3c88a4719f2bddca3c9f04719f2bc1f7 else 0x8c1ca3c88a4719f2bdc00728f22291c808af687dca3c88c4719f2bde2c728f22291c67caf7998f214c8a4719f2bddca3ec8a4720e67caf7795ca3c88a4720e67ddca3c88a471c0010af7999ca3c89e4719f2bdc0072a367c11c67caf6735ca3c88a4719f2bdd65728f22291c67caf7 else if i < 147 then if i < 145 then if i < 144 then 0x885ca3c88a4719f2bde91728f22291c67caf755dca3c88a4719f2bdd54728f22291c67caf797dca3c88a4719f2bde2e728f22291c67caf787dca3c88a4719f2bddca3c8a74719f2bc5f7335ca3c88a4719f2bdc99728f22291c67caf7999ca4c88a95d9f2bddca3c88a4e59f2bc727 else 0x2667288a471a72bda69728f22291c67caf77a5ca3c88a4719f2bdde5900f22291c67caf773dca3c88a4719f2bdea2728f22291c67caf7729323c9444719f2bde2f728f22291c67caf79e5ca3c88a4719f2bddca3c88a4719f2dcaf730dca3c88a4719f2bddd23c88a4719f2bc027 else if i < 146 then 0x745ca3c88a4719f2bde17520f22291c67caf7729482296b67caf1d9d76728f22291c67caf772a073c88a4719f2bde6c728f22291c67caf78c9ca3c88a4719f2bde2b728f22291c67caf77b5ca3c88a4719f2bdde4728f22291c67caf7699ca3c88a4719f2bddcaa18f24719f2bc877 else 0x729622291c8399f0b1e73728f22291c67caf772a362291c8399f2bde8f728f22291c67caf78b5d53c88a4719f2bdde53c88a5f51c67caf7974f22291c67caf17ddca484f22297d67caf787cf22291c67caf1c9de53c88a4719f2bc3d79c9ca3c88a4719f2bde6f728f22291c67caf7 else if i < 149 then if i < 148 then 0x7290422a574719f2bddca5888a4719f2bc3579d9ca3c88a4719f2bddca900f22291c67cb77728f222a4d67caf17de29729142291c67caf7002173c88a4719f2bda99728f22291c67caf7a55ca3c88a4719f2bddca9188a4720e67caf7728fb5cd1c67caf07ddca4c8f22291c69caf7 else 0x728f222a8b5ad9f2bde613c9732291c67caf79e1ca3c88a4719f2bde71728f22291c67caf7899ca3c88a4719f2bddca3c9f04719f010af7728f23048a471b52bde1f3c88a4719f34caf7728f2229254719f2bddca3c8a12291c67caf77f1ca3c88a4719f2bddca3c88a95caf0f41f7 else if i < 150 then 0x728f22291c67d58001e80728f22291c67caf78cdca3c88a4719f2bde1f728f222a5267caf7001ca3c88a471c62bd9ca3c8cb4719f2bc007728f22791c6b59f2bdde1728f22291c67e04787dca3c91c67caf05ddca3c88a4b19f2bcdc7728f22291c67cb70f5e6f999322291c67caf7 else 0x728f22280d4719f2bddca3c88a4720e67cd37728f222a4d4719f2bddca3c9f04719f810af7a35ca3c88a4719f2bdc00728f22551c67cc46728fb3c88a4a19f2bde87728f22291c67caf7728f22297d4719f2dddde728f22291c67caf7728f22291c808af28dc91728f22291c67caf7 else if i < 166 then if i < 158 then if i < 154 then if i < 152 then 0x728f22281b4719f2bddca450c12291c67caf7728f22780b4719f2bddca3c88a471f42bc767a69ca3c88a4719f2bdc00728f22291c67e0b6728f22291c67d8b2bddca3c88a5ae0e67caf7a49ca3c88a4719f2bddca3c88a9359f2bc2c7728f229d1c67caf07de5d3c88a4719f2bc2c7 else if i < 153 then 0x8b1d23c88a4719f2bddca3c88a6851c2bc1f7999d23c88a4719f2bddd53c88a4719f2bc027728f22291c67caf205c00794f22291c67caf6729633c88a4719f2bddca3c88a470e267caf7001ca3c8954720e2bd94e729622291c8399f7a7dca3c88a4719f2bdd4e72a407e91c67caf7 else 0x1da3c88a4719f2bd9e1754f22291c67caf787dd53c88a4719f2bdd4e728f229d1c67caf79add53c88a4719f2bddcb728f22291c67caf7728f22988a4719f2bdde185cf22291c67caf7794f22291c67caf059e6f748f22291c67caf7785d23c88a4719f2bdd4e748f22291c67caf7 else if i < 156 then if i < 155 then 0x785ca3c88a4919f2bde74768f22291c67caf7895da3c88a4719f2bde96728f22291c67caf7728f22291c67e04009e28728f22291c67caf7728f22291c67caf0d5e1f768f22291c67caf7541ca3c88a4719f2bddca3c88a9359f2bc1f7974f22291c67caf07de29768f22291c67caf7 else 0x728f22291c67d432bde29728f22291c67d587729732291c67caf3bde5d728f22291c67caf7001ca8d88a9359f2bd94e728f222a4d67caf7728f222a57471f42bdd4e974f22291c67caf7539e03c88a4719f2bdc00728f22291c67cb76728f25cccb67caf17dc00780f22291c67caf6 else if i < 157 then 0x785e53c88a4719f2bdd4e794f22291c67caf787de53c88a4719f2bddca3c9f72291c67caf78a5e53c88a4719f2bddca3c88a471c034c5f785cf22291c67caf28ddd23c88a4719f2bc1f7728f22291c67cb7059e75794f22291c67caf7728f22291c910af401e66794f22291c67caf7 else 0x2283c88a4719f2bd80086cf22291c67caf6002663c88a471b52bda2485cf22291c67caf753a173c88a4719f2bddca9210a2291c67caf787e173c88a4719f2bddd53c88a4719f2bc5f77295b3c88a4719f2bde6f72a362291c67caf7999ca4c9732299f2bde2985cf22291c67caf7 else if i < 162 then if i < 160 then if i < 159 then 0xa525d3c88a4719f2bdc00728f22293567caf6729625208a4719f2bde29974f22291c67caf7729043c88a4720e67ddca3c88a4a11c67cbb7728f22291c67caf251dca3c88a4719f561007728f265c8a4719f2bddca3c88a6bd1c67caf785cf22291c67caf009dd2728f22291c67caf7 else 0x89a663c88a4719f2bde39728f22291c67caf7a66663c88a4719f2bddcf998f22291c67caf787dcb3c88a4719f2bde1f748f24719f2bc1677865d3c88a4719f2bddca428a74719f2bc4c7728f22291c839ad2bdde1729623c88a4720e7728f33c88a4719f2bddca3c88a02d1c67cc47 else if i < 161 then 0x728f22291c6d4af009dca3c88a9359f010af7728f25111c8399f2bddca4ccf22291c67caf7786913c88a4719f2bde6c87cf22291c67caf78ca1f3c88a4719f2bddca588f22296f67caf772a403c88a4719f2bddce998f22291c67caf7729323c88a95caf07de78998f22291c67caf7 else 0x1ca3c88a9499f2bd9ca588f22291c67c4c7899ca3c88a4720e2bddca3c88a4719f2bc3d79bdca3c88a4723a2bde24728f22291c67caf7001ca3c88a4b20e2bda6b728fb2291c67caf7728f222a939359f2bddca4c8fb2291c67caf7729323c88a4719f2ddd4e729482291c67caf7 else if i < 164 then if i < 163 then 0x728f22291c8e8af3b1e29728f22551c67caf7001ca4108a4719f2bd9ca4c9042291c67caf7729043048a4719f2bde1f728fb2291c67caf75e9ca5888a4719f2bddca3c89e95d1c67caf7974f22291c67c042bddd53c88a4719f2bc2c7729042291c67caf401dca411732291c67caf7 else 0x728f22291c67cbb001dca5890a2291c67caf79bdca4108a4719f2bddca3c88a4720e69caf7551ca4108a4719f2bde1f729042291c67caf78a5ca4108a4719f2bdc00729532291c67caf6728f22291c67caf8d1dca3c9732291c8e8af79d5ca4108a4719f2bddca3c88a4a19f2ec1f7 else if i < 165 then 0x72a363c88a4719f811d577290a2291c67caf7539ca4288a4719f2bddca428f22293967caf7728f27c88a4719f2bddca4c90a2291c67caf785d482291c67caf1d9dca3c8d02291c67caf7729142291c67caf009dca3c88a4720e6b43d7768f22291c67caf0f5dca9010a2291c67caf7 else 0x5a9ca4508a4719f2bddca3c88a4720e67e047539ca4508a4719f2bde1f729142291c67caf7001ca4508a4719f2bd9ca3c88a471b52bc5f7729324508a4719f2bddca901142291c67caf799dca3c88a4719f2bddca3c88a470c567caf73e1ca5888a4719f2bdde17290a2291c67caf7 else if i < 173 then if i < 169 then if i < 167 then 0x2175208a4719f2bd9ca3c8cb4719f188af79bdca5208a4719f2bddca3c88a4c11c67caf7728fb3c88a95d1c2bddca5208a4719f2bc777539d53c88a4719f2bdde1729482291c67caf78a5ca5208a4719f2bde90729482291c67caf70021f4508a4719f2bda6f729142291c67caf7 else if i < 168 then 0x728f222a5767caf401dca3c88a4799f2bc3d7728f22291c69d9f2dde1f728f24719f2bc287729323cc8a4719f2bddca3c88a4719f448af7728f22291c8e99f2bddca3c89e4719f2bc007728f27c24d4719f2bdc007290a29d1c67caf6729628d88a4719f2bddca3c8a74719f2bcdc7 else 0x87dca3c88a4719f825dca3c88a4719f2bc167728f25108a4719f2bddca3d5622291c67caf7728f45888a4719f2bdde172a362291c67caf79fdca8d88a4719f2bdd4e72a362291c67caf787dca8d88a4719f2bddca690f222a57470af7999ca8d88a4719f2bde1f998f23051c67caf7 else if i < 171 then if i < 170 then 0x785ca3c88a471a02bddca3c88a4e5b52bc4c79d9ca5888a4719f2bdde4748f22291c67caf7201ca3c88a4719f2bdc00974f25111c67caf6728f222a574719f311dda729622291c67caf7001ca3ec8a95d1c2bda66729482291c67caf779dca3c88a4719f2bddca4508a4719f2bc5f7 else 0x999ca229244719f2bdcf872a402291c67caf7728f232d1c67caf009de1999622291c67caf774dca3c88a4719f2bddca3c9732291c7d0af7728f22291c6d4af0b1ded794f22291c67caf7728f25cc8a5f59f269dca4c9622291c67c4c7728f22291c67e092bddca3c9444719f560dc7 else if i < 172 then 0x8a5ca3c89e4719f2bddca3c8c92551c67caf787dca3c9fa4720e2bddca3c8c12551c67caf79bdca3c9444719f2bde1f999322291c67caf7a71ca4c88a4719f2bde6f99a402291c67caf7728f2229248399f2bddca8e0f22291c67caf73e1ca3c88a4719f2bde1f99a402291c67caf7 else 0x9bdca3c8954719f2bdde1728f22551c67caf7769ca3c8954719f2bddca8d9f02291c67caf7729323c8954719f2bddca900f22551c67caf7729623c8954719f2bddca3c9fa2551c67caf7728f25e4954719f2bddca3c9732551c67caf7754f22291c67c042bddca3c88a4719f2bdbc7 else if i < 177 then if i < 175 then if i < 174 then 0x728f2304a74719f2bddca4c8f22291c67caf7728f229d394719f2bde1f728f27c11c67caf7551ca3c89e4719f2bddca3c88a96d1c69caf7728f27e89e4719f2bddca3c88a471b52bc1f77290a14c8a4719f2bddca3c9732791c67caf7001ca588954719f2bd9ca3c8c12291c67cbb7 else 0x728f2304cb4719f2bddca3c88a4ad1c67caf7794f22291c8399f2bde6f728f229d1c67caf7539ca3c88a471b52bddca3c88a5f51c700af7729323c8a74719f2bddca3ca0329d1c67caf7728f2608a74719f2bddca3c88a4719f5ed107728f25cca74719f2bddca3ca8c2291c67caf7 else if i < 176 then 0x729323c8cb4719f2bddca588f232d1c67caf7728f22280c4719f2bddca3c88a4719f2ec847728f232d1c67caf17dde187cf24719f2bc167728f22291c67caf661c00754f22292867caf6729143c8cb4719f2bddca3c97332d1c67caf7728f22291c67cc4001dca3c8da32d1c67caf7 else 0x1ca450cb4719f2bd9ca3c88a95d9f108af78a5ca3c8cb4719f2bdc0085cf22296b67caf6728f2228b24719f2bddca3c97395d1c2bc1f7728f222a574720e0f5c00728f232d1c67caf6728f23049e4719f2bdde1768f22291c67caf7728f22291c67d5817ddda4c8f22291c67caf7 else if i < 179 then if i < 178 then 0x729623c9f04719f2bddda3c88a4719f2bd987728f2041f04719f2bddca3c88a4720e67cb77999ca3c9684719f2bddca3c88a4719f144af7001ca3c9684719f2bd9ca588f25491c67caf7728f22291c67c7616de66728f25111c67caf7999ca5888a4719f135dca588f25111c67caf7 else 0x728fb3c9734719f2bddca9008a95d1c2bcec7a65ca3c8c14719f2bdd4e728f22311c67caf7728f25cc8c4719f2bde1f728f222d1c67caf7999ca3c9f94719f2bde7f728f27c11c67caf7999ca3c9f04719f2bddca900f27c11c67caf7728f22291c67c092bde8f974f22291c67caf7 else if i < 180 then 0x87e293c9fa4719f2bde91728f27e91c67caf7241ca3c9fa4719f2bdc00728fb5cd1c67caf6728f22291c67cb705dd67728f25cd1c67caf7a45ca3c9734719f2bddca4c4f22291c67caf7729323c88a4799f2bddca3c88a95d1c2ec1f7755ca3c9734719f2bde1f3c9fa4719f2bc5f7 else 0x728f22291c67d580b1dca3c8a7471b567caf7728f22548a4719f311dca900fb2291c67caf7728f22291c6d4042bdd4e728f2a311c67caf787dca3ca8c4719f2bddca3c88a471a767caf7728f232d1c67caf0b1d4e729627e91c67caf7728f222a9e4719f2bddca3c9f05f51c67caf7 else if i < 211 then if i < 196 then if i < 188 then if i < 184 then if i < 182 then 0x728f22280b4919f2bddca3c88a5adf42bc767728fb2291c67caf0f5dca3c88a95d2467caf787dca3ca134719f2bddca4288a471b52bc4c7728f22291c67ca30f5c00728f22291c700af687dca3c9834719f2bddca915042291c67caf7754f22291c67caf371c00728f22291c67e096 else if i < 183 then 0x1d23c88a4919f2bda72728f22292467caf7999ca3c88a4719f5ede29728f22292467caf7999ca3c88a4919f2bdc00728f22292467caf6729323c88a4919f2bddca900f22292467caf7729623c88a4919f2bddca3c9fa2292467caf7728f23048a4919f2bddca3ec8a5f51c67caf7 else 0x728f22291c69caf0a1dca3c88a4719f5601f7728f25cc8a4719f311dca3c8c12292867caf7728f2229134719f2bddca3c88a94d1c67caf772a5c3c9732299f2bddca4108a4719f2bd887728f232d1c67caf07ddca3c88a02d2867caf7728f22297d4a19f2bddca3c88a4719f2bd097 else if i < 186 then if i < 185 then 0x728f22291c67caf271dca3caa02291c67caf7728f25b88a4719f2bddca3c97322a5708caf7728f22297067caf211dca3c88a4723a2bd887729fa2291c67caf3bddca3c88a4919f2bce77728f22551c67caf17ddca3c8c12291c67cc47785ca3c88a4b19f2bddda5888a4719f2bc2c7 else 0x9bdca3c88a4a19f2bddca3c88a4719f2ec027539ca3c8cb4719f2bde6f794f22291c67caf7748f22281b4719f2bddca3c88a4720e2bcec7781ca3c88a4719f2bddd53ec8a4719f2bc1f787dca3c88a4a19f2bddca4d8f22292867caf7728f25cc8a4a19f2bdd4e728f22291c67d587 else if i < 187 then 0x728f22280b4b19f2bddca5888a5f51c67c2c79bdca43c8a4719f2bdddb728f22291c67caf7728f2229844b19f2bddca450662291c67caf7729273c88a4719f2bddca920f22291c67caf7001ca3c88a4ad9f2bd9e187cf222a57470af7001ca3c9f04719f2bd9ca900f22292b67caf7 else 0x1da3c88a4b19f2bd9d5728fb2291c67caf787dca5588a4719f2bde19728f22291c67caf79aa5d3c88a4719f2bddca3c88a4719f2bc4f7999ca3c88a4b19f2bdc00728f22292c67caf6728f20408a4b19f2bddca3c9732292c67caf7785ca3c88a471c02bde1f974f22291c67caf7 else if i < 192 then if i < 190 then if i < 189 then 0x728f25111c67d582bddca3c8102292867caf7728f22292c67caf009d4e729042291c67caf772a362291c67c072bddca3c8d04719f2bc6e7728143c88a4719f2bde66728f42291c67caf7728f229d1c67caf131dca0f0f22291c67caf7001ca5888a4b19f2bd9ca8d9fa2291c67caf7 else 0x728f20408a471f42bde9c728f22291c67caf7001ca3c88a4723a561a9085cf22291c67caf7539ca3c88a4723a2bddca900f22296b67caf7729623c88a4e59f131dca3c88a4720e3102c7001ca3c8954b19f2bd9ca3c88a471b52bcdc787dd23c88a4719f2bddca3c8954719f2bc2c7 else if i < 191 then 0x539caa188a4719f2bddca3c88a5f53967caf7728f22291c67c04561d4e729622297d4719f7728f23688a4719f2bddca3c8cb4719f010af772a362291c67caf005d4e729625cd1c67caf7728f22291c8399f2bddca3c88a4e59f2bc3d7729622292c4719f2bddce8a4f22291c67caf7 else 0x7290422a5767caf0f5c00729382291c67caf6001d53c88a95d1c2bd9ca3ca8a22a4d67caf7728f22297d5ad9f2bddca900f222a4d67caf7728f222a574e59f2bdc007290a2291c6d4af6728f22292469caf059dca3c9732291c8f8af7728f27e88a4c19f2bddca3c88a5f51c67cd37 else if i < 194 then if i < 193 then 0x974f22291c67caf0f5e66728f22293967caf7001ca3c88a4e59f2bd9ca504f22293967caf7729323c88a4e59f2bddca4c8f27c11c67caf7729142291c67caf371dca900f22293967caf7729623c88a4a19f2bddca3c88a4719f2bc177728f229c8a4e59f2bddca3c88a02d3967caf7 else 0x729482291c67caf001dca588f22291c7d0af7728f23048a5ad9f2bddca3c88a02d6b67caf7729623c88a67caf465c00778f22291c67caf6728f22292c67caf17ddca3c88a4919f2dcaf7729853c88a4719f2bdd4e728f22551c67caf7001ca4288a4e59f2bda29728f22293967caf7 else if i < 195 then 0x1ca3c88a5ad9f2bd9ca5e0f22296b67caf7a71ca3c88a5f51c67ddca3c8102296b67caf7728f27e88a5ad9f2bddca3c8105111c67caf7728f22291c67c7b2bddca8fc8a4719f2bd94774a403c88a4719f2bddca428102291c67caf7728f25cc8a5ad9f2bddca3c88a6011c67cb77 else 0x1ca3c88a4719f31d9ca3c9fa22a4d67caf7728f22291c67c4b2bddca952362291c67caf7001ca3c88a5f19f2bd800728f22296f67caf6a55ca3c88a5ad9f2bddd23c88a4719f2bc3d79bdca3c88a5ad9f2bde66728f22296b67caf7728f22291c8399f0f5e17728f22296b67caf7 else if i < 203 then if i < 199 then if i < 197 then 0x9bdca3c88a9359f2bde1f728f222a4d67caf78a5ca3c88a9359f2bddca5208a4719f2bc4c7728f22293967caf059dca3c8102291c69caf74d1ca3c88a4719f2bddca3c95e5111c67caf7001ca3c88a9359f2bd800728f229d1c67caf672a543c88a9359f2bddca3c81022a4d67caf7 else if i < 198 then 0x728f22788a95d9f2bddca4508a4719f34c5f7728f22292867c072bde66728f22291c8e8af7728f25cc8a4799f2bddca3c9732291d67caf7728f22291c67caf081c00728f222a6d67caf6999ca3c88a94d9f2bde66729042291c67caf7001ca3c9f09359f2bd9ca3c89e4719f2bd887 else 0x78629728f22291c839dca4c8f24808a67caf7728f25cc8aa799f2bddca3c9733057d67caf7729325888a95d9f2bdc007290422a5767caf6a65ca3c88a95d9f2bddca3c9fa2291c7d0af7728f22791c67caf0b1dca484f222a5767caf7729043c88a95d9f2bde1f8a4f23051c67caf7 else if i < 201 then if i < 200 then 0x728f22281c4719f2bdd6a728f232d1c67caf7729323ca8c2299f2bddca4c9625cc8a67caf7729863c9732299f2bddca484f25cc8a67caf799a402291c67caf131dca3c973229c067caf7729143c9732299f2bdd4e728f22291c67cbb7785ca3c88a95caf0f5c00974f22291c67caf6 else 0x728f22291c7d0af005e6672a402291c2bd9878a5ca3c88a471a72bddda3c88a4b19f2bc2c772a403c88a471a72bddca3c9fa2291c69caf7729623c88a471a72bddca3c88a95d1c69caf7728f22291c849a72bdd4e729323c97367caf7001ca5588a4719f2bda1f4508a4719f2bc5f7 else if i < 202 then 0x791ca3c88a471a72bddca3c9fa5111c67caf787dca3c9fa470af651de1998f22291c838af7728f22291c6b4072bddca3c88a95d1c2bd947728f22291c67caf71ddca8d88a02d1c67caf787dca3c88a471a72bddca3c89e4719f2bc1f7728f22291c67d112bddca5890a2291c67c4c7 else 0x729414288a4719f2bddca3c88a471ad2bc017728f22297d471ad2bddca4c8f22296b67caf79be665888a4719f2bddca3c88a5c11c67caf7748f22291c67caf059d4e728f22791c67caf7728f222a57471ad2bdde1728f229d1c67caf70021f728f2471a72bda6f728f22291c69caf7 else if i < 207 then if i < 205 then if i < 204 then 0x728f20408a471ad2bde66728f22292867caf7729043c89e4719f2bddca4288a4719f01caf7999ca3c88a67caf465dd5900f22291c67caf7728f222a4d67caf6f1dca3c9444719f01caf7785ca3c8c12291c839dca3c88a4720e700af787cf22291c67caf6f1dca3c8c12291c6b4af7 else 0x7290a2291c67caf005dca3c88a4719f311887728f22291c67c042edc00728f22291c7f8af69be293c88a4720e67ddca588f2228b34719f7729043c88a471ad2bddca8d9902291c67caf7728f232d1c67cd317de66728f22291c7d0af7728f28048a4719f2bddca900f22291c67e047 else if i < 206 then 0x1ca4109e4719f2bd9ca2291c67caf3b0167729663ec8a4719f2bddca3c8a74719f2bca37728f22297d4719f811dda728f22292c67caf7728f22291c67e040f5e74728f22292c67caf7001ca3c94c4719f2bd9e1728f222a4d67caf7728fb2291c67caf1d9dca4c8f222a4d67caf7 else 0x72a3d3c88a4719f2bde78728f22291c838af7785ca3c88a471ad2bddca3c88a4728567caf7539ca3c88a471ad2bddca4e08a4719f2bc727728f22291c67c3b2bdde5728f22291c6b4af772a403c88a471ad2bdd47728f22291c67caf7728f22280b4719f34ddca588f22291c6b4af7 else if i < 209 then if i < 208 then 0x1ca3c88a4724b2bd9ed728f22291c6b4af7749323c88a4719f2bddca3c8954719f2bcdc7794f20408a4719f2bdd67728f22291c67caf77294d3c88a4719f2bdde53c88a4719f2bc6e7999ca2291c67caf39ddca3c88a6011c67caf79bdca3c88a67caf441dca588f284c8a4719f7 else 0x729562291c67caf28dde187cf25cd1c67caf7728f25cc8a471b52bddd9728f22291c67caf7728f27c11c8399f2bddca3c8a72291c6d4af7728f22791c67c042bde6f728f22291c67cac7728f25cc8a67caf441dca3c88a95d1c6d4af7728f222939471b52bdc00728f22292867cbb6 else if i < 210 then 0x8a5ca3c88a471b52bddca2d4f22291c67caf785cf22297d4719f2bddca3c9732299f18caf785cf22291c67caf0f5e30728f22291c67cc47999ca3c88a471b52bddca4c8f22291c6d4af772a362291c67caf1d9dca3c9fa2291c6d4af7a45ca5888a4719f2bddca3c88a4719f3101f7 else 0x728f232c8a471c02bddca4c8f22291c6b4af7728f22297d4919f2bddca3c88a4919f2bc3d7728f222a064719f2bddca3c8102291c67cb779bdca3c88a471b52bddca3c88a471b52bc4c7539ca3c88a4719f311c00754f22291c67caf6a41ca3c88a4719f2bde1f728f22291c6d4af7 else if i < 226 then if i < 218 then if i < 214 then if i < 212 then 0x1ca3c89e95d9f2bd9e2728f22291c67caf7729143c88a471c02bddce3c88a4719f2bc5f7728f20408a471c02bddca3ca162291c700af78bdca3c88a4720e67ddca3c88a4719f108af7728f23048a471c02bde66728f22291c69caf79bdca588f22297d67ddca3c88a4719f2bc287 else if i < 213 then 0x999322291c67caf131dca3c88a4719f810167728f222a584719f2bddca3c88a20d1c67caf7728f22293967caf1d9c0087cf22291c700af6539ca3c88a471c02bde29729312291c67caf787dca3c88a471c02bddca4c8f22291c700af772a403c88a471c02bdde5588f22291c67caf7 else 0x728f22291c67d022bddca3c8c12291c7d0af7728f22280b471f42bddca3c88a4719f34c767728f22297d471f42bddca3c88a4719f2ecdc7001ca3c88a471df2bd9ca3c88a4703767caf7728f222a57470bb2bddca6e0f22291c67caf78a5ca3c88a471c62bdc00728f232d1c700af6 else if i < 216 then if i < 215 then 0x9bdca3c88a471f42bde17728f22291c7d0af7728f22291c67c492bddca2d4f22297d4719f7729323c88a471f42bdc90728f24719f2bc16772a7e3c88a471f42bde6f3c88a95d9f2bdbc7999ca2291c69caf059dca3c88a02d1c6b4af7728f22296b67caf1d9dca3c9734719f2bc217 else 0x728f27e88a4723a2bddca3c88a4719f010c47728f222a57838af0f5dca3c94402d1c67caf7729623c88a4e51c67ddca3c8c12291c8e8af7729482291c67caf009e73728f22292867caf7728f22280b4723a2bddca3c88a5f51c8e8af7728f222a574723a2bddca3c88a472858e8af7 else if i < 217 then 0x729323c88a4723a2bddca900f22291c8e8af7729623c88a4723a2bddca3c8102291c8e8af785cf22291c67caf059e1f728f22291c67d587728f22291c67caf0e9e1f728f25cd9f188af77290a2280b4719f2bddca3ca7d2291c8e8af787dca3c8cb4719f2bddca4508a4719f2bc3d7 else 0x728f23688a4719f34de22728f22291c67caf7769ca3c88a4720e2bddca3c9a22291c838af7728f22548a4720e2bddca3c88a95d6b67caf7729323c88a4719f811dca3c88a95d1c680af7001ca3c9444723a2bda1f728f22291c8e8af78a5ca3c88a4723a2bddca3c88a4719f2ec217 else if i < 222 then if i < 220 then if i < 219 then 0x728f22291c8399f269c00768f22291c838af6728f22291c838302bdde53c88a4719f2bc017728f22280b471a72bdc00728f22291c6d4af6728f24808a95d9f2bddca3c88a4a19f2bc76772a362291c67caf001e1f3c9734719f2bc5f7728f22291c67d582bddca3ec8a4719f2ec1f7 else 0x728f222a57470af0e5dca3c88a95d9f2bc5b78c9ca3c88a95d1c2bddd5728f222a57470af7728f22282595d1c2bddca3c9fa2291c8383d772a403c88a6851c2bde6f728f222a57838af772a413c88a4719f2bddca4c8f222a57838af7895ca3c88a4719f2bdd4e728f27e91c838af7 else if i < 221 then 0x728f22291c67d58131dca3c88a6851c838af7728f209c8a4719f2bddca8d8f222a4d67caf7002667288a4919f2bda99728f22297d67caf7729623c88a4719f6c5dca690f27e88a470af772a403c9a22291c2bde6672a4022a57470af7728f22291c67c072dde6c728f222a57470af7 else 0x14e72a407e91c2bd9ca4108a4719f2bc007728f25148a4719f2bdd4e72a403c9fa470af787e663c81b4719f2bddca3c88b2291c67caf7739ca3c88a4719f2bddca3c88a4719f2dc0179bdca3ec8a4719f2bddca900f2a308a470af7999ca901fa2291c2bde1fa70f22291c67caf7 else if i < 224 then if i < 223 then 0x8a5ca8d88a4719f2bddca3c88a4719f2bc6e7728f22280b4719f2dddca3c88a4911c67cb77728f22291c8499f2dddca3c88a4719f010b77728f22291c7f8af269de1729323c88a95caf7728f22291c6b4af1d9dca900f25cc8a95caf7728f222a574a19f2bde6a728f22291c8e8af7 else 0x748f22291c8399f2bdc00728f229d3967caf6539ca3c88a4719f2dde1f728f22291c67cb77728f25111c67caf1d9dca3c88a6c91c67caf7a71ca3c88a4720e67de2c728f22291c67cb778a5ca3c88a4719f2dddd2728f22291c67cb77728f20408a4719f2bddca588f22291c67cb77 else if i < 225 then 0x87dca3c97367caf17ddca5208a4719f2bc2c70021f728f24719f2dda1f728f22551c67caf7002667288a4719f2dd9e1728f22291c6d4af7728f22296f4719f2bdc00748f22291c67cb7698dca3c88a4719f2bddca4288a4719f2bc7679bdca3c88a4719f2ddde1728f22291c67cb77 else 0x1ca3c88a95d1c2ed9ca3c95e2291c67caf7001ca3ec8a4719f2ed9ca3c88a7bd1c67caf79bdca3c88a4719f2edde1728f22291c67cbb7728f22291c8e8af131e2d728f22291c67cbb78a5ca3c88a4719f2eddd5728f22291c67cbb7728f222a574719f2edc00728f22292467cb76 else if i < 234 then if i < 230 then if i < 228 then if i < 227 then 0x729623c88a4719f311dca3c9fa2291c67cc47728f22291c69caf1d9c00728f222a578383d672a365cc8a4719f2bddca3c88a4719f82d987728f2229844719f311dca3c88a4b11c67cc47999ca2291c67caf0d5dca4c8f25ccc167caf7728f22291c67c07311dca900f22291c67cbf7 else 0x728f22291c67c0734ddca5208a4719f2bc1f7728f22291c67c0434ddca54cf22291c67caf7539ca3c88a4719f321c00768f22291c67cc46001ca3c88a472442bda29728f22291c67cc47999ca3c88a4719f311dca900f22291c67cc47729623c88a4719f2bddca3c94495d1c67caf7 else if i < 229 then 0x9bdca3c88a4e59f2bddca3c88a4719f810767728f22291c8e99f561de1729142291c67caf772a403c88a4719f34ddca614f22291c67cd37728f20408a4719f34ddca3c9fa2291c67cd37999ca2291c67cb7059dca3c8332291c838af7728f23048a4719f34ddca3c88a95d1c67cd37 else 0x9bdca3c88a4719f34dde53c88a02d1c67caf7728f23048a4719f561dca3c88a5f51c67d587728f22291c67c07561c00728f22291c700d36001ca3c9732299f34d80087cf22291c67cd36001ca3c88a4719f34d9ca4c8f22291c67cd37001ca3c88a4719f5619ca3c8954719f2bc4c7 else if i < 232 then if i < 231 then 0x728f22551c67caf0f5de1728f22291c67d587a51ca3c88a4719f561c00794f22791c67caf6999ca3c88a4719f561e1f728f22291c67cbb7975ca3c88a4719f561c00754fb2291c67caf6728f27e88a4719f561dca3c9732291c67d587728f25cc8a4e59f2bde6f72cf22291c67caf7 else 0x728f222a4d67e042bddca3c88a95d1c67e047728f222a4d4719f811dca3c88a4719f01e047001ca3c88a4719f57d9ca3c88a95d1c67d5f7001ca3c9444719f561800974f22291c67d586728f25cc8a4719f34de66728f32291c67caf79bdca3c88a4719f561dca3c9442291c67d587 else if i < 233 then 0x728f22791c67c412bddca428f229d1c67caf7728f28288a4719f2bddca3c88a4719f01caf787e660748a4719f2bdc00769622291c67caf6728f25cc8a4719f811dca5348a4720e67caf7728f22280b4719f811dca3c88aa4d1c67e047728f22291c67cbb2bde29728f22292867caf7 else 0x87dca3c88a4b19f2bde6f728f22291c67e0479adca3c88a4719f2bde29728f22291c7d0af7768f22297d4719f2bddca3c88a4719f825947a91ca3c88a4719f2bde29728f23411c67caf78a5ca3c88a67caf465c00728f22291c67e046728f25111c67caf001dd53c88a4720e67caf7 else if i < 238 then if i < 236 then if i < 235 then 0xa8dca3c88a4719f2bddca3c88a4719f2ec4c7728f22291c67caf1dddca5208a4719f010af7728f22291c67caf655dca3c88a4719f2bced7001ca3c88a4719f89d9e3728f22291c67caf7981ca3c88a4719f2bdc00728f222a5367caf6999ca3c88a4719f82dc00728f27c11c67e046 else 0x728f22291c67caf1b1dca588f22291c6d59f78a5ca3c88a4719f2c1dca3c88a4720e67c417728f2228444719f2bddca3c88a4719f274af7728f22291c67c302bddca3c88a95d1c67e2777297f3c88a4719f2bdc00729482296b67caf6728f280c8a4719f2bddda3c88a4719f01caf7 else if i < 237 then 0x999ca5888a4720e67ddca4c9622291c8399f787e293c88a4720e67ddca4c48a4719f2bc6e7001e53c88a4720e67d967728f22291c8399f7728f22788a4720e67dde1728f232d1c67caf7728f2228b34720e67dc00729142291c700af6729623c88a470b167ddca3c8c12291c2c59f7 else 0x7861f3c9fa4719f2bddca4c9622297d4719f787dca3c8c14720e67ddca5888a4719f2bd987794f22291c67caf1d9dca3c9733051c8399f78a5ca3c9444719f2bdc00728f22791c8399f6001ca3c8954719f2bd9ca3c88a6851c67caf7729483c88a471f42bddca3c88a4719f2ec3d7 else if i < 240 then if i < 239 then 0x72a403c88a4b19f2bdc00728f28511c67caf6728f22291c67caf0e5dca3c9f04719f2bd947999ca588c12291c67ddca4c9623048a4719f772a863c8c12291c67de6f728f22291c6b4af7729623c8a72291c67dc00728f22291c67cbf6729623c88aa791c67de297290a2291c67caf7 else 0x1ca5208a471f42bd9ca588f25cc8a5f59f787dca588f23051c67dde1729042291c67caf7728f25cc8a471ad2bddca588f25ccc14719f7768f22291c67caf059d7a728f222a5767caf7539ca588c12291c67ddca3c88a4719f89dbc78b9ca3c89e4719f2bddca3c8a7471b52bc4c7 else if i < 241 then 0x728f222a4d67d8c2bde667288a4719f2bc167728f25ccc195d9f2bddca588f222a574720e79fdca3c88a4719f2bde6f7290a2291c67caf7728f22292c67caf0f5dca3c88a4719f2f0af7539ca3c9735f59f2bde6f8a5ca3c88a5f59f78a5ca3c9732297d67ddca43c8a4719f2bc5b7 else 0x72a848d88a4719f2bddca3c88a94d9f2bd9878a5ca3c88a95d1c839c0087e664719f2bc166728f25cd444719f2bddca3ca1632d1c67caf7001ca3c9524719f2bd9ca3c8c04719f2bc5b7

def val6 (i : ℕ) := field (val6Chunk (i / 12)) 74 (i % 12)

def pick6 (h : ℕ) := (h * 137 % 10000019) % 2900 + disp6 (h % 2900)

def db6 (i : ℕ) : List W :=
  let a := val6 i
  unpack wireOf 10 (a % 16) (a >>> 4)

def allow6 (ws : List W) := !(matchTable 2900 db6 pick6 ws)

def disp7Chunk (i : ℕ) : ℕ :=
  if i < 37 then if i < 18 then if i < 9 then if i < 4 then if i < 2 then if i < 1 then 0x1aa51c04ba8000680000273 else 0xc0800000000000000002b40100064d else if i < 3 then 0xdc00003706083500000c90f500000 else 0x2392c8000033dd50003018b00000 else if i < 6 then if i < 5 then 0x830000140051cf40000000400 else 0x4000000000002320001a689 else if i < 7 then 0x808530000000140000324 else if i < 8 then 0xa90680055e9763d000000000000000 else 0x86000000000a4ac0065c00160d6 else if i < 13 then if i < 11 then if i < 10 then 0xa2800000000000043c000000003000 else 0x8f8100000333004000000000160 else if i < 12 then 0x458000000000000d6000d4cfc00000 else 0x8000014901a1f003390010e00000 else if i < 15 then if i < 14 then 0x1c47000f48dc0067c8900a2a00000 else 0x37500000014006e4000029dd0400 else if i < 16 then 0x9c800c28000000086c0000000 else if i < 17 then 0x800000000256500000db000 else 0x3ba66004000024c010140000000000 else if i < 27 then if i < 22 then if i < 20 then if i < 19 then 0x50080000000000007a002 else 0xaa400004024d40000002a700000001 else if i < 21 then 0x72400bac60006e90000200005b4401 else 0x351002de61e94000000240000031 else if i < 24 then if i < 23 then 0x36e1000b6000000040038c005d809 else 0xca4000000100000000005780000000 else if i < 25 then 0x2bfcc400ab80000000001c469000 else if i < 26 then 0x614819000007880000003006c4 else 0x3630032ac80b1b2800871ed else if i < 32 then if i < 29 then if i < 28 then 0xc2800002fa0007f000000000002400 else 0x69c008b40000000500000000000000 else if i < 30 then 0x8ea14001080000510c02bc40000000 else if i < 31 then 0x5064034000000300000806b7d3457 else 0x17000000000000400001af40200001 else if i < 34 then if i < 33 then 0x281b3000070000078801888600000a else 0xc00799e0000000000000000 else if i < 35 then 0x23d2b000002b0623a0000000000000 else if i < 36 then 0x8410002e40000048a8a33c0000000 else 0x36137402dc000de6440000000124 else if i < 56 then if i < 46 then if i < 41 then if i < 39 then if i < 38 then 0xc2cb800401000050000a00002960a3 else 0x5feeb0100002800002644400000400 else if i < 40 then 0x1c000074100002dcc02 else 0x211000008e1d7000000000000400 else if i < 43 then if i < 42 then 0x8034e000000003540112000 else 0x4000000c39400000000000000000 else if i < 44 then 0x1000c6800000139bc4b5d4001a400 else if i < 45 then 0x4004000000200e42db8b300009 else 0x868d3708003ac00000000000000000 else if i < 51 then if i < 48 then if i < 47 then 0x9a235b764c040000003c0100364 else 0x78400d2000000000006d00000 else if i < 49 then 0x18f71f1701a9c98c007955c00000 else if i < 50 then 0x81620db82cd5c0070348000000017f else 0x8004000043425d6f0013e00000 else if i < 53 then if i < 52 then 0x9d000039a901935c580100000 else 0x3540044cde00000ac532002b400048 else if i < 54 then 0x64679b0b8c0001f2d124006d400 else if i < 55 then 0x1b7364c0000000001fd001e616800 else 0x56f00001a14c3c683965b25a9800 else if i < 65 then if i < 60 then if i < 58 then if i < 57 then 0x176002de076db else 0x400000000014d0040000035015d7 else if i < 59 then 0xbe0006e00d0000000000c200000279 else 0x50000000000034c0045700000c7183 else if i < 62 then if i < 61 then 0x90000000000000004994e0010b else 0x2cc0199e0e85c006080000000 else if i < 63 then 0xbf6440040000198001390000070b4b else if i < 64 then 0x70040500000000af0040108108 else 0x92c0000eb50000000000004003223e else if i < 70 then if i < 67 then if i < 66 then 0x401000004caa8000003dc01 else 0x800000000000009c00000010166e else if i < 68 then 0x20f004a3acc000025400c00 else if i < 69 then 0x400bcc0000000000000000000001 else 0x800091140000d379a0009d46e01c00 else if i < 72 then if i < 71 then 0xd680000c0000000774048bc0023000 else 0xb600000005cad9a0000103000275fe else if i < 73 then 0x801adc0073c00004000c400c0c02 else if i < 74 then 0xac003002fb8dcdb5b800005ad00000 else 0x24575f6e

def disp7 (i : ℕ) := field (disp7Chunk (i / 12)) 10 (i % 12)

def val7Chunk (i : ℕ) : ℕ :=
  if i < 37 then if i < 18 then if i < 9 then if i < 4 then if i < 2 then if i < 1 then 0x728f22291c67caf37000887dca3c88a95d1c67caf8728f22291c67caf1d80088a5ca3c88a02d1c67caf889a1f728f22291c67caf88a5ca3c88a4719f2bc768728f22291c67caf058008975ca3c88a4719f2bcdc8999ca3c9fa2291c67caf8999ca3c88a4719f2bc2c80025d728f22291c67caf7001ca3c88a4b11c67caf7 else 0x728f22291c67caf17c1688ca29728f22291c67caf8728f232c8a4719f2bc5f8728f20408a4719f2bc008728f22291c67c042bc008728f229c8a4719f2bc4c8728f22291c67caf008008001ca3c8e42291c67caf7001ca3c88a4719f108af7001ca3c88a4719f2bcec7539ca3c88a4719f2bd888728f22280b95d1c67caf8 else if i < 3 then 0x728f2229244719f2bc168001ca3c88a471c02bc5f7728f22291c67caf0047688a5ca3c88a4719f2bd888001ca3c88a95d9f2bc3d7728f22291c69d9f2bc168728f222c8a4719f2bc018728f22291c8399f2bc8489bdca3c88a4719f2bc018728f22291c67c072bc168728f22291c67cb72bc168728f22291c67caf620168 else 0x999ca3c88a4719f2bc168749ca3c88a4719f2bc168539ca3c88a4719f2bcdc800000728f22791c67caf6001ca3c88a4791c67caf7728f27e88a4719f010af8001ca3c88a4719f2bc4d7728f22291c67caf1301f872a403c9732291c67caf8728f27e88a4719f2bc168728f23048a4719f2bc168728f222a574719f2bc168 else if i < 6 then if i < 5 then 0x7861f728f22291c67caf8728f22291c67caf07c168728f22291c67caf005888729323c88a4719f01caf8001ca3c88a4720e2bc2c7001ca3c88a4719f2bdb1753a66728f22291c67caf8002667288a4719f2bc16772dca3c88a4719f2bc018001d23c88a4719f2bc1679bdca3c88a4719f2bc168001ca3c9fa2291c838af7 else 0x728f23048a4719f2bc4c8728f22291c67caf1302c8728f22291c67caf0f42c872a403c88a4719f01caf88a5ca3c88a4719f2bcdc8001ca3c88a4719f2bc287001ca3c89e2291c67caf7001ca3c88a4719f2ec1f7001ca3c88a95d1c2bc1f7728f222a4d4719f2bd888728f2229284719f2bc1f80021f728f24719f2bc167 else if i < 7 then 0x72a403c88a4719f2bc5f8001ca3c88a4719f2ecaf7728f22548a4719f2bc2c887dca4c8f22291c67caf8729623c88a4719f2bc1f8728f22297d4719f2bc2c8728f222a574719f2bc2c8728f22291c67c042bc2c8728f22292c4719f2bc2c8728f22291c67cc42bc2c88a666728f22291c67caf8728f22291c67caf6202c8 else if i < 8 then 0x1da3c88a4719f2bc2c7729323c88a4719f2bc2c8728f20408a4719f2bc16887dca900f22291c67caf8001ca3c9734719f2bc1f787dca3c88a4719f2bca38728f20408a4719f2bc2c800291728f22291c67caf7a4666728f22291c67caf8a666f728f22291c67caf8728f25cc8a4719f2bc2c8728f23048a4719f2bc2c8 else 0x539ca3c88a4719f2bc028001ca3c88a4719f2bc357731ca3c88a4719f2bc028001ca3c88a4a19f2bc1f7999ca3c88a4719f2bc018001ca3c88a4719f2bc3e7539ca3c88a4719f010af8001cf728f22291c67caf79bdca3c88a4719f2bc5b8785ca3c88a4719f2bc4e8728f22291c67caf004dc8728f27e88a4719f2bc358 else if i < 13 then if i < 11 then if i < 10 then 0x539ca3c88a4720e67caf8539ca3c88a4719f2bc2c8728f22788a4719f2bc3d89bdca3c88a4719f2bc76800000728f22292467caf6001ca3c88a1491c67caf7728f22291c67cd32bc5f88a5ca3c88a4719f2bc6e8785ca4c8f22291c67caf8729623c8102291c67caf8728f22291e4719f2bc028728f22297d4719f2bc1f8 else 0x1ca3c88a4723a67caf78a5ca3c88a4719f010af8001ca3c88a4719f2bc39772a403c9902291c67caf8728f20408a4719f2bc018001ca3c9732297d67caf7728f25cc8a4719f2bc1f8728f22291c67caf07c008728f22291c8e99f2bcdc8785ca900f22291c67caf8001ca3c88a471a72bc167001ca3c9733051c67caf7 else if i < 12 then 0x728f22291c67caf1d83d885dca3c88a4719f2bc768001ca3c88a95d1c838af78a5ca3c88a4719f2bc2c8539ca3c9fa2291c67caf8728f23048a5f51c67caf8001ca3c88a4719f810af79bdca3c88a4719f2bd888a71ca588f22291c67caf8001ca3c88a4719f2bce778a5ca3c9fa2291c67caf8729623c8532291c67caf8 else 0x1ca3c88a4719f2c0af7728f25cc8a4719f2bc3d8728f222a574719f2bc3d872932900f22291c67caf8728f22291c67c042bc018728f284dfa2291c67caf8728f22291c67c042bc3d8728f22291c67c072bc1f88a5ca3c88a4720e67caf8728f22291c67caf0043d8728f22291c67caf620768001ca588f22291c8399f7 else if i < 15 then if i < 14 then 0x9d9ca4c8f22291c67caf8001ca4288a4719f2bc4c7001ca3c88a4719f2bc5b7001e5728f22291c67caf7728f27e88a4719f2bc018728f22291c67caf17c1f8728f25cc8a4719f2bc4c8728f22291c67caf130008728f22291c67caf008018728f27e88a4719f2bc3d8001ca5208a4719f2bc76700299728f22291c67caf7 else 0x1ca054f22291c67caf7728f23048a4719f01caf8001ca3c88b2291c67caf7728f25cc8a4719f2bc168728f22280b4719f2bc1f872a403c88a4719f2bc3d89bdca3c88a4719f2bc1f887dca3c88a4719f2bc1f8728f22291c8399f2bc018728f22291c67caf0042c8729623c88a4719f2bc3d8729043c88a4719f2bc3d8 else if i < 16 then 0x999ca3c88a4719f2bc768728f22291c67caf3704c853a29728f22291c67caf8728f22291c67caf17c4c8001e53c88a4719f2bc3d7539ca3c88a4719f2bc3d8728f22291c67caf370768999ca3c88a4719f2bc3d8728f53c88a4719f01caf8795ca3c88a4719f2bc3d8729323c88a4719f2bc3d80026f728f22297d67caf7 else if i < 17 then 0x72a403c88a4719f2bc4c87290a3c88a4719f2bc4c800217728f22291c67caf79bdca3c8c12291c67caf8728f20408a4719f2bc4c8728f260cc12291c67caf8728f222a574719f2bc4c8728f2229394719f2bc4c8728f22291c8399f2bc4c8728f22291c67c072bc4c89e26f728f22291c67caf8728f22291c67caf6204c8 else 0x728f22280b4719f2bc4c8001ca3c88a471b52bc4c7001ca3c8a74719f2bc4c7002663c88a4719f2bc4c700000728f22291c6b4af60026f998f22291c67caf7728f23048a4719f2bc768785ca3c88a4719f2bc4c8001ca4c8f222a5767caf79bdca3c8102291c67caf887dca3c88a4719f2bc4c8001ca4c9622291c67caf7 else if i < 27 then if i < 22 then if i < 20 then if i < 19 then 0x728f222a574719f2bc5f89bdca3c88a4719f2bc3d88a5ca3c88a95d1c67caf8728f222a9e5f51c67caf8728f22291c67c042bc5f8728f22291c67caf6205f8001ca588f22291c67c4c7539ca3c88a4719f2bc018001ca900f27e88a470af700000729482291c67caf6999ca3c88a4719f2bd888001ca3c88a4719f2bd987 else 0x1caa18f22291c67caf79bdca3c88a4719f2bc028729623c88a4719f2bc5f887dca3c88a4719f2bc5f800229728f22297d4719f7999ca3c88a4719f2bc5f8729323c88a4719f2bc5f8728f23048a4719f2bc5f8728f22297d4719f2bc5f8001ca3c81d2291c67caf787dca3c88a4719f2bc168728f25cc8a5f51c67caf8 else if i < 21 then 0x728f27e88a4719f2bc768728f22291c67caf008768999ca3c88a4719f2bc1f887dca588f22291c67caf8001ca3c88a4e51c67caf79bdca3c88a4719f2bc5f872986588f22291c67caf8999ca3c88a4719f2bd988728f22291c67caf3701f800000729142291c67caf68a5ca3c88a4719f2bc018785ca3c88a4719f2bc5f8 else 0x278728f22291c67caf7001ca3c88a471ad2bc3d7001ca3c88a4719f2bc727728f22291c67caf6203d8785ca3c88a4719f2bc168728f22291c67caf1d82c8001ca3ecf22291c67caf7728f22297d4719f2bc728728f222a574719f2bc018001ca3c88a4719f2bc6e70021f3c88a4719f2bc5f7001ca3c88a4719f2bc9a7 else if i < 24 then if i < 23 then 0x1ca3c88a1f51c67caf70026c728f22291c67caf70000072a362291c67caf6001ca3c88a4719f2dc167729483c88a4719f2bc768728f20408a4719f2bc768728f22291c67c072bc008728f22308a4719f2bc028728f22291c8399f2bc768728f22291c7d19f2bc768728f22291c67c042bd888728f22291c67c042bc768 else 0x755ca3c88a4719f2bc1f8728f22291c67caf17c0089b266728f22291c67caf8999ca3c8c12291c67caf8728f22291c8399f2bd888728f22280b5f51c67caf8001ca3c88a4719f37caf787dca3c88a5f51c67caf8728f20408a4719f2bcdc8785ca588f22291c67caf8001ca3c88a471a067caf7728f22291c67caf009888 else if i < 25 then 0x728f22291c67caf3703d8729323c88a4719f2bc768728f22291c67c042bc1f8728f25cc8a02d1c67caf8728f22280b4719f2bc008729623c88a4719f2bc768728f27e88a4719f2bd888539ca3c88a4719f2bc398999ca3c8102291c67caf8728f260d732291c67caf8729323c88a4719f2bc168728f25cc8a4719f2bc5f8 else if i < 26 then 0x728f22291c67caf008dc8785ca3c88a5f51c67caf8539ca054f22291c67caf8001ca3c88a4719f2bc847729213c8102291c67caf8729623c88a4719f2bc818728f22297d4719f1e8af800000728f22291c69caf6002173c88a4719f2bc767785ca3c88a4719f2bc76872a403c88a4719f2bc16887dca3c88a4719f2bc768 else 0x728f22291c8399f2bcdc8001ca3c88a0951c67caf7728f22297d4719f2bcdc8728f222a574719f2bcdc800000754f22291c67caf6001ca3c8cb4719f2bc5f7999ca3c88a4719f2bc028728f22291c67d582bcdc872a863c88a4720e67caf8001ca3c88a471b567caf7728f22291c67caf620dc8728f22291c67c072bc5f8 else if i < 32 then if i < 29 then if i < 28 then 0x1ca2d4f22291c67caf787dca3c88a4719f2bcdc8729323c88a4719f2bcdc872a403c88a4719f2bcdc8729623c88a4719f2bcdc8001ca3c88a6851c67caf7728f20408a4719f2bc3d8728f25cc8a4719f2bcdc8728f23048a4719f010af8728f23048a4719f2bcdc8728f22280b4719f2bcdc887dca3c88a4719f01caf8 else 0x72a363c88a4719f2bd888729323c88a4719f2bc3e8728f2041fa2291c67caf89bdca3c88a95d1c67caf8729323c88a5f51c67caf8728f24808a02d1c67caf8001ca3c88a4723a2bcdc7728f27e8c12291c67caf8728f22280b4719f2bc5f8001ca3c9444719f2bcdc772a403c88a4719f2bc0189bdca3c88a4719f2bcdc8 else if i < 30 then 0x729623c88a4719f2bd008001ca3c88aa791c67caf70025d3c88a4719f2bcdc7728f222a574719f2bcec800000974f22291c67caf6728f20408a4720e67caf8785ca3c88a4719f01caf872a403c88a5f51c67caf8001ca3c88a4719f2bd007728f20408a4719f2bc02887dca3c88a02d1c67caf8001ca3c88a4719f2bd8a7 else if i < 31 then 0x728f22291c8399f2bc3d8728f23048a4719f2bd888728f27c08a4719f2bd888728f22280b4719f2bd888a5a6f728f22291c67caf8539ca3c88a4719f2bc1f8728f222a574719f2bd888001ca3c88a4719f2bd1070026f8a4f22291c67caf7728f222a574719f2bc768728f22291c67caf0083d8001ca450f22291c67caf7 else 0x72a403c88a4719f2bd88800266729322291c67caf7001ca3c88a4719f560af700090728f22291c67caf7728f20408a4719f2bd888785ca3c88a02d1c67caf8728f27e88a4719f2bc028001ca8d8f22291c67caf79bde1728f22291c67caf8728f22291c67c042bc028728f22291c7019f2bc5f8728f222a574719f2bc3f8 else if i < 34 then if i < 33 then 0x539ca3c8c12291c67caf800000728f22291c67cbb6001ca3c88a9359f2bd88787dca3c88a4719f2bd888728f22291c8399f2bc028728f27e88a4719f2bc2c8785ca3c88a4719f18caf8728f27e88a4720e67caf88a5ca3c88a4719f2bc1f8001ca4108a4719f2bc3d7001ca3c88a5ad9f2bc767728f22291c67caf0082c8 else 0x785ca3c88a4719f2bd888539ca3c88a4719f37caf8728f22291c67cbb2bc1f8728f22291c8399f2bc2d8001e187cf22291c67caf7001ca3c88a4719f2bc177728f22291c8399f2bdb1887dca3c88a4719f2bd9480026672a402291c67caf7728f22291c8399f2bc2c8001ca3c88a4719f81188700226728f22291c67caf7 else if i < 35 then 0x1ca3c89e4719f2bc3d7728f22291c67caf0041f8001ca3c88a4719f34c5f7539ca3c88a4719f2bc778999ca3c88a4719f2bc4d8728f22291c8399f108af8999ca3c88a95d1c67caf8241ca3c8102291c67caf80014e728f27e91c67caf7739ca3c88a4719f010af80022f728f22291c67caf7001ca3c9202291c67caf7 else if i < 36 then 0x728f23048a95d1c67caf8001ca3c9f02291c67caf79bdca900f22291c67caf8001ca3c88a4719f2bd947728f22291c67e042bd888001ca3c88a4719f2bc81772a403c88a4719f2bc768001ca3c8cb2291c67caf772a5c4c8f22291c67caf8728f22291c67caf1301688a5ca3c8c12291c67caf8728f22297d4719f2bcdd8 else 0x8a5ca3c88a4719f2bc3d8728f43c88a4719f010af8728f33c88a4719f2bc028729623c88a4719f2bc4c8001ca3c88a4719f2bcdd7729323c88a4719f2bd888728f20408a95d1c67caf8728f22291c67caf0b000872a5c900f22291c67caf8a7229728f22291c67caf8728f222a9e4720e67caf88a5ca3c8102291c67caf8 else if i < 56 then if i < 46 then if i < 41 then if i < 39 then if i < 38 then 0x728f22291c6819f2bc018001ca3c88a4719f2bc21778666728f22291c67caf8728f23048a4719f2bc21800296728f22291c67caf700000728f22291c67e0468a5ca3c88a4719f2bc028785ca3c88a4719f2bcdc8728f23048a4719f2bc018001ca410f22291c67caf700229728f22291c8399f7001ca3c88a4719f1e8af7 else 0x1ca3c88a4719f2dcaf772a403c88a4719f2bc038899ca3c9fa2291c67caf8001ca3c88a4719f2bc787728f222a574719f010af8001ca3c88a4719f2bc4e7001ca3c88a4719f2bc3f73e1ca3c88a02d1c67caf8728f22291c67caf0044c8001ca3c88a4719f2bc2e7729623c88a4719f2bc2e8729623c88a4719f2bc168 else if i < 40 then 0x1ca3c88a4719f2bca37728f22291c67c07010af8001ca3ec8a4719f2bc1f7728f22291c67cb0010af8728f27e88a95d1c67caf8001ca3c88a4719f34caf7728f22297d4719f2bc4c8001ca3c88a4719f310af7001ca3c8952291c67caf700000728f22292c67caf6728f222a574719f2bc02800000728f25111c67caf6 else 0x9bdca3c88a4719f010af8729323c8662291c67caf8728f22297d4719f2bc168785ca3c88a4719f010af8001ca3c88a4719f2bc2d7539ca3c9732291c67caf8729623c88a4719f010af8728f20408a4719f010af8728f2229a14719f010af872a86900f22291c67caf8728f22291c8399f010af8728f222a574720e67caf8 else if i < 43 then if i < 42 then 0x728f22280b4719f01caf8728f222a574719f01caf8728f22291c8399f01caf8728f22291c2c59f01caf887dca3c88a4719f188af8001ca3c88a4e59f2bc4c7001ca3c88a4719f104af7728f25108a4719f2bcdc88a5ca3c88a4719f2bd8a8001ca3c88a4719f064af7001ca3c9442291c67caf7729323c88a4719f064af8 else 0x9bdca3c88a4719f01caf8999ca3c88a4719f01caf800000728f229d1c67caf6785ca3c9fa2291c67caf8001ca3c88a4719f380af70014e72a402291c67caf78a5ca3c9732291c67caf8001ca3c88a471f42bc767728f27e88a4719f01caf8001e1728f22291c838af7728f22291c67caf1d81f8728f25cc8a4719f01caf8 else if i < 44 then 0x1ca3c88a471f467caf7001ca3c88a4719f024af79bdca3c88a4719f630af8785ca3c88a4720e67caf8001ca3c88a4719f630af7001ca3c88a4719f18caf7785ca3c88a4719f2bc2c8729323c88a4719f0c0af8001ca3c88a4719f3102c7539ca3c88a4719f01caf8001ca3c88a4719f08caf7728f25cc8a4719f08caf8 else if i < 45 then 0x729323c88a4719f2bc028769ca3c88a4719f2bc2c89bdca3c88a4719f2bc4c872a403c88a4720e67caf8729323c88a4719f010af8729623c88a4720e67caf8728f284c8a4720e67caf8728f25cc8a4720e67caf8539ca3c88a4719f2bc5f8728f23048a4720e67caf8728f22291c67caf6201f8001ca3c88a470b167caf7 else 0x8a5ca3c88a4719f2bc5f8729323c88a4720e67caf8729623c88a4719f01caf89bdca3c88a4720e67caf88c9ca3c88a4720e67caf8001ca3c88a4911c67caf772a403c88a4719f010af8728f25cc8a4719f2bc018728f22291c67caf004008729323c9fa2291c67caf8999ca3c88a4720e67caf8001ca3c88a4b19f2bc2c7 else if i < 51 then if i < 48 then if i < 47 then 0x728f22291c67caf1d816872a403c88a4719f2bc2c887e29728f22291c67caf8001ca3c88a4a11c67caf7001ca3c88a471ad67caf7001ca3c88a4700a67caf7728f22280b4719f2bc168728f22291c67caf1d84c853a1f728f22291c67caf872a403c9fa2291c67caf8728f27e88a4700a67caf872a403c88a4719f2bc028 else 0x72a403c88a95d1c67caf8728f2a308a95d1c67caf8728f25cc8a95d1c67caf8a461f728f22291c67caf8728f222a9e95d1c67caf8728f22297d95d1c67caf85e9ca3c9732291c67caf8001ca3c88a9351c67caf7728f22291c67c072bc01872a403c88a4719f2bc288001ca3c88a5ad1c67caf7001ca8d88a4719f2bd887 else if i < 49 then 0x9e1ca3c88a95d1c67caf8539ca3c88a95d1c67caf872a5c3c88a95d1c67caf8729323c88a95d1c67caf8728f22297d4719f01caf8728f23048a4719f104af8728f22291c67caf0045f8728fb3c88a4719f2bc1f87854e728f22291c67caf8728f27e88a4719f2bc788728f25cc8a4719f2bce7873dca3c88a4719f01caf8 else if i < 50 then 0x728f20408a4719f2bc1f8729863c88a5f51c67caf8729623c88a5f51c67caf8001e1728f222a57470af778629728f22291c67caf8728f22280b4719f2bc018728f23048a4719f2bc1f8728f25cc8a1951c67caf887dca3c88a4719f2bc018728f20408a5f51c67caf8728f260c8a5f51c67caf8728f27e88a5f51c67caf8 else 0x539ca900f22291c67caf8728f2228b302d1c67caf8a59ca3c88a5f51c67caf8729623c88a4719f2bd888a65ca3c9732291c67caf80021f728f25cd1c67caf7785ca3c88a95d1c67caf89bdca3c88a5f51c67caf8539ca3c88a5f51c67caf8728f22291c6b59f2bc3d8001ca3d4f22291c67caf7539ca4c8f22291c67caf8 else if i < 53 then if i < 52 then 0x539ca3c88a02d1c67caf8729323c88a02d1c67caf88a5ca4c8f22291c67caf872a403c88a02d1c67caf8729623c88a02d1c67caf8728f22291c67caf0f41f8728f22388a4719f01caf8999ca3c88a4719f2bc4c8001ca5888a4719f2bc2c7728f26888a02d1c67caf8728f22297d4719f2bc768728f23048a02d1c67caf8 else 0x728f27e88a4719f2bc1f88a5ca900f22291c67caf8001d53c88a4719f2bc1f7001ca3c88a1951c67caf7728f22291c67caf0081f8728f23048a1491c67caf8728f2040c12291c67caf8001ca3c88a06d1c67caf7728f25cc8a4719f2bc768728f22291c67caf3701689bdca3c88a02d1c67caf8785ca3c88a4719f2bc018 else if i < 54 then 0x729623c8c12291c67caf8728f284cc12291c67caf8001ca3c8a72291c67caf7001ca3c88a471a767caf7728f22291c8399f2bc1f8728f22291c67caf0b01f8001ca3c88a0391c67caf7001ca3c88a4719f088af7001ca3c88a2cd1c67caf7001ca3c88a6391c67caf7728f22297d4719f2bd8888a5ca3c88a1f51c67caf8 else if i < 55 then 0x728f22291c67caf1303d88bdca3c8c12291c67caf8728f22291c67c072bc76859dca3c8c12291c67caf887dca3c8c12291c67caf8001ca3c88a4719f188af7a661f728f22291c67caf8729323c88a4719f2bc018001ca3c8c12291c8399f7729323c8c12291c67caf8728f22291c67caf620008728f23048a4719f2bc3d8 else 0x728f22291c67caf1d85f800000728f22291c8e8af6728f2a31732291c67caf8728f27e9732291c67caf8001ca3c88e2291c67caf7001ca3c9a22291c67caf7728f23048a4719f2bc028728f22291c67c042bc4c80014e729622291c67caf7728f25cc8a4719f2bd888785ca3c8c12291c67caf800280728f22291c67caf7 else if i < 65 then if i < 60 then if i < 58 then if i < 57 then 0x999ca3c9732291c67caf8728f22291c6d59f2bc4c8728f22280b4719f2bc768728f22291c67c042bc168001ca3c88a4719f560dc7001ca3c88a4720e67c3d7729323c9732291c67caf8728f22291c67caf0f4168728f27e88a4719f2bc4c8729623c9732291c67caf8728f22291c67caf0084c800000728f22292867caf6 else 0x728b53c8102291c67caf8001ca3ca132291c67caf79bdca3c9fa2291c67caf89bdca3c9732291c67caf8000007290a2291c67caf6001ca3c9f04719f2bd887728f22291c67caf008168001ca3c88a4719f2bc007999ca3c88a5f51c67caf8785ca3c9732291c67caf8728f22291c67c072bd88887dca3c9732291c67caf8 else if i < 59 then 0x785ca3c8332291c67caf8729623c88a4719f2bc028001ca3c8332291c67caf700000728f22293967caf687dca3c81d2291c67caf8785ca3c8102291c67caf8728f22291c8399f2bc168539ca3c8102291c67caf8728f22291c67caf0b016872a403c8102291c67caf8729a43c8102291c67caf8728f25cc8a4719f2bc9a8 else 0x728f22291c67c072bcdc872a40588f22291c67caf8729623c88a4719f2bc2c8001ca3ccf22291c67caf7001ca520f22291c67caf7728f25ccc12291c67caf8001ca428f22291c67caf7001ca3c8112291c67caf79bdca3c8e42291c67caf8729623c9fa2291c67caf8001ca3c8662291c67caf7001ca3c8532291c67caf7 else if i < 62 then if i < 61 then 0x728f22297d4719f010af8a01ca3c9fa2291c67caf8001ca4508a4719f2bc5f7728f22297d4719f2bc3d8728f222a574719f2bc1f8001ca3c88a4719f2bdbc79bdca588f22291c67caf859dca588f22291c67caf8999ca588f22291c67caf872932588f22291c67caf872a86588f22291c67caf8728f2041732291c67caf8 else 0xa01ca900f22291c67caf8999ca900f22291c67caf8001ca690f22291c67caf7728f22291d4719f2bc018728f22297d4719f2bc028728f22291c67caf0f400800000728f27c11c67caf6001ca3c9832291c67caf7001ca3d0f22291c67caf772a403c88a4719f380af8728f22291c67caf3705f8539ca3c88a4719f2bc4c8 else if i < 63 then 0x8a5ca3c88a4719f2bc4c89bdca4c8f22291c67caf8728f25cc8a4719f2bc028728f20408a4719f01caf8999ca3c88a02d1c67caf8728f22297d4720e67caf887e66728f22291c67caf8539ca3c88a4719f2bc168999ca4c8f22291c67caf8729864c8f22291c67caf8001ca3c9732299f2bc5f7001ca484f22291c67caf7 else if i < 64 then 0x1ca3c88a4719f0c0af7539ca588f22291c67caf8001da728f22291c67caf7728f20408a4719f2bc5f88a5ca3c8112291c67caf8001d2728f22291c67caf7001ca970f22291c67caf7001ca618f22291c67caf75e9ca4c8f22291c67caf8728f25cc8a4719f010af89da6f728f22291c67caf8001ca3c9902291c67caf7 else 0x9be66728f22291c67caf8728f23048a4719f2bc178a7266728f22291c67caf80021f998f22291c67caf7728f20408a02d1c67caf8001cb728f22291c67caf787dca3c8102291c67caf8000f8728f22291c67caf78a5ca3c88a4719f2bc168785ca3c88a4719f2bc1f8001ca3c88c2291c67caf7728f22291c67c072bc3d8 else if i < 70 then if i < 67 then if i < 66 then 0x1ce728f22291c67caf70029c728f22291c67caf7a5a29728f22291c67caf88a5ca588f22291c67caf88be29728f22291c67caf8001cc728f22291c67caf7a014e728f22291c67caf89da66728f22291c67caf80014e728f25cd1c67caf7728f22291c67caf17c3d8728f22291c67c072bc028728f27e88a6391c67caf8 else 0x728f22291c67caf004168728f222a574719f088af80026f728f222a5767caf7728f27e88a4719f2bc5f8728f22280b4719f010af8729323c88a4719f2bc1f887dca3c88a4719f010af887dca3c88a4719f2bc3d8728f22291c67caf0085f8728f22280b4719f2bc3d88be1f728f22291c67caf8728f22291c67c072bc2c8 else if i < 68 then 0x728f22296b4719f2bc7689bdca3c88a4719f2bc2c89be1f728f22291c67caf8728f22291c8399f2bc5f89b1e1728f22291c67caf8728f27e88a02d1c67caf872a403c88a4719f2bc1f887dca3c9fa2291c67caf8728f22291c67caf17c2c8001ca3c88a471c067caf787dca3c88a4719f2bc028729623c88a95d1c67caf8 else if i < 69 then 0x1ca3c88a4719f2bc037785ca3c88a4719f2bc3d8728f22280b4719f2bc2c8729623c88a4719f2bc018001ca3c88a4919f2bc16700000728f22291c67cd368a5ca3c88a5f51c67caf8999ca3c88a4719f2bcdc8728f22280b4720e67caf887dca3c88a4719f2bc2c8728f22280b4719f2bc02887dca3c88a4720e67caf8 else 0x785ca3c88a4719f2bc028729323c88a4719f2bc4c8001ca3c8954719f2bc2c78c9e1728f22291c67caf800167728f22291c67caf759d4e728f22291c67caf8729323c8102291c67caf8a454e728f22291c67caf8729143c88a4719f2bc5f85e94e728f22291c67caf8001ca3ca8c2291c67caf700276728f22291c67caf7 else if i < 72 then if i < 71 then 0x999ca3c88a4719f2bd1080000085cf22291c67caf600000794f22291c67caf6001d5728f22291c67caf700000768f22291c67caf600000748f22291c67caf60017a728f22291c67caf700232728f22291c67caf79b1ca900f22291c67caf89e1e1728f22291c67caf8899e1728f22291c67caf872a403c8c12291c67caf8 else 0x8a5ca3c88a4719f01caf800000728f232d1c67caf600000728f22551c67caf6999ca3c88a06d1c67caf800266729622291c67caf700000729042291c67caf600000728fb2291c67caf60021f8a4f22291c67caf7001e1998f22291c67caf7785ca3c88a0951c67caf8728f22297d4719f2bc0189bdca3c88a0391c67caf8 else if i < 73 then 0x999ca3c88a4719f010af800000728f22291c700af6539ca3c88a4719f2bc768001ca4c8f25cc8a67caf7001ca3c97322a5767caf700000728f222a4d67caf600000728f22296b67caf6728f22291c67c042bcdc80021f728f27e91c67caf700000728f22291c6d4af60021f728f23051c67caf7001ca3c88a4719f2bc777 else if i < 74 then 0x728f222a574719f2bdbc8728f22297d4719f024af89be29728f22291c67caf8001ca588f22297d4719f700000728f22291c67d58600000728f22291c67cc4600000728f22291c67cb76001ca900f222a57470af7728f27e88a4719f2bcdc800000728f22291c7d0af6001ca3c88a4751c67caf79bd4e728f22291c67caf8 else 0x728f2a31fa2291c67caf8001ca588f23048a4719f7728f22291c67caf3702c8

def val7 (i : ℕ) := field (val7Chunk (i / 12)) 84 (i % 12)

def pick7 (h : ℕ) := (h * 137 % 10000019) % 891 + disp7 (h % 891)

def db7 (i : ℕ) : List W :=
  let a := val7 i
  unpack wireOf 10 (a % 16) (a >>> 4)

def allow7 (ws : List W) := !(matchTable 891 db7 pick7 ws)

def disp8Chunk (i : ℕ) : ℕ :=
  if i < 1 then 0x4000004588002a0 else if i < 2 then 0x900007032092000 else 0x2f00001a

def disp8 (i : ℕ) := field (disp8Chunk (i / 12)) 5 (i % 12)

def val8Chunk (i : ℕ) : ℕ :=
  if i < 1 then 0x728f22291c67caf0f5dca3c88a4719f2bc167728f22291c67c072bddca3c88a5f51c67caf7728f22291c67caf371de1728f22291c67caf7728f22291c67caf0b1e1f728f22291c67caf7728f22291c67caf009e29728f22291c67caf79bdca3c88a4719f2bddca3c88a4719f010af7 else if i < 2 then 0x729623c88a4719f2bdd4e728f22291c67caf7728f22291c67caf07ddca3c88a4720e67caf7728f22280b4719f2bddca3c88a4719f2bc017728f22291c67caf621dca3c8102291c67caf7728f22291c67caf1d9dca3c88a4719f2bc5f7728f22291c67caf131dca3c9fa2291c67caf7 else 0x999ca3c88a4719f2bddca4c8f22291c67caf772a403c88a4719f2bddca3c9732291c67caf7728f222a574719f2bddca3c8c12291c67caf7

def val8 (i : ℕ) := field (val8Chunk (i / 12)) 74 (i % 12)

def pick8 (h : ℕ) := (h * 311 % 10000019) % 30 + disp8 (h % 30)

def db8 (i : ℕ) : List W :=
  let a := val8 i
  unpack wireOf 10 (a % 16) (a >>> 4)

def allow8 (ws : List W) := !(matchTable 30 db8 pick8 ws)

def allow3 (_ : List W) := true

def test4 (i : ℕ) := checkState 3 allow3 (db4 i)

def test5 (i : ℕ) := checkState 4 allow4 (db5 i)

def test6 (i : ℕ) := checkState 5 allow5 (db6 i)

def test7 (i : ℕ) := checkState 6 allow6 (db7 i)

def test8 (i : ℕ) := checkState 7 allow7 (db8 i)

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v4b0 : runBlock test4 0 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v4b24 : runBlock test4 24 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v4b48 : runBlock test4 48 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v4b72 : runBlock test4 72 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v4b96 : runBlock test4 96 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v4b120 : runBlock test4 120 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v4b144 : runBlock test4 144 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v4b168 : runBlock test4 168 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v4b192 : runBlock test4 192 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v4b216 : runBlock test4 216 15 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 8000000 in
lemma every4 (i : ℕ) (hi : i < 231) : test4 i = true := by
  by_cases h1 : i < 120
  ·
    by_cases h2 : i < 48
    ·
      by_cases h3 : i < 24
      ·
        exact runBlock_get v4b0 i (by omega) (by omega)
      ·
        exact runBlock_get v4b24 i (by omega) (by omega)
    ·
      by_cases h3 : i < 72
      ·
        exact runBlock_get v4b48 i (by omega) (by omega)
      ·
        by_cases h4 : i < 96
        ·
          exact runBlock_get v4b72 i (by omega) (by omega)
        ·
          exact runBlock_get v4b96 i (by omega) (by omega)
  ·
    by_cases h2 : i < 168
    ·
      by_cases h3 : i < 144
      ·
        exact runBlock_get v4b120 i (by omega) (by omega)
      ·
        exact runBlock_get v4b144 i (by omega) (by omega)
    ·
      by_cases h3 : i < 192
      ·
        exact runBlock_get v4b168 i (by omega) (by omega)
      ·
        by_cases h4 : i < 216
        ·
          exact runBlock_get v4b192 i (by omega) (by omega)
        ·
          exact runBlock_get v4b216 i (by omega) (by omega)

lemma sound4 (xs : List W) (hl : live basicOps goal 4 xs.toFinset) : allow4 xs = true := by
  apply match_safe (by decide) (fun i hi => checkState_sound (allows := allow3) (fun _ _ => rfl) (every4 i hi)) xs hl

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v5b0 : runBlock test5 0 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v5b24 : runBlock test5 24 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v5b48 : runBlock test5 48 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v5b72 : runBlock test5 72 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v5b96 : runBlock test5 96 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v5b120 : runBlock test5 120 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v5b144 : runBlock test5 144 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v5b168 : runBlock test5 168 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v5b192 : runBlock test5 192 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v5b216 : runBlock test5 216 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v5b240 : runBlock test5 240 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v5b264 : runBlock test5 264 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v5b288 : runBlock test5 288 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v5b312 : runBlock test5 312 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v5b336 : runBlock test5 336 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v5b360 : runBlock test5 360 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v5b384 : runBlock test5 384 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v5b408 : runBlock test5 408 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v5b432 : runBlock test5 432 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v5b456 : runBlock test5 456 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v5b480 : runBlock test5 480 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v5b504 : runBlock test5 504 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v5b528 : runBlock test5 528 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v5b552 : runBlock test5 552 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v5b576 : runBlock test5 576 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v5b600 : runBlock test5 600 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v5b624 : runBlock test5 624 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v5b648 : runBlock test5 648 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v5b672 : runBlock test5 672 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v5b696 : runBlock test5 696 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v5b720 : runBlock test5 720 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v5b744 : runBlock test5 744 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v5b768 : runBlock test5 768 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v5b792 : runBlock test5 792 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v5b816 : runBlock test5 816 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v5b840 : runBlock test5 840 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v5b864 : runBlock test5 864 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v5b888 : runBlock test5 888 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v5b912 : runBlock test5 912 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v5b936 : runBlock test5 936 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v5b960 : runBlock test5 960 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v5b984 : runBlock test5 984 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v5b1008 : runBlock test5 1008 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v5b1032 : runBlock test5 1032 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v5b1056 : runBlock test5 1056 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v5b1080 : runBlock test5 1080 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v5b1104 : runBlock test5 1104 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v5b1128 : runBlock test5 1128 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v5b1152 : runBlock test5 1152 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v5b1176 : runBlock test5 1176 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v5b1200 : runBlock test5 1200 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v5b1224 : runBlock test5 1224 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v5b1248 : runBlock test5 1248 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v5b1272 : runBlock test5 1272 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v5b1296 : runBlock test5 1296 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v5b1320 : runBlock test5 1320 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v5b1344 : runBlock test5 1344 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v5b1368 : runBlock test5 1368 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v5b1392 : runBlock test5 1392 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v5b1416 : runBlock test5 1416 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v5b1440 : runBlock test5 1440 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v5b1464 : runBlock test5 1464 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v5b1488 : runBlock test5 1488 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v5b1512 : runBlock test5 1512 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v5b1536 : runBlock test5 1536 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v5b1560 : runBlock test5 1560 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v5b1584 : runBlock test5 1584 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v5b1608 : runBlock test5 1608 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v5b1632 : runBlock test5 1632 7 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 8000000 in
lemma every5 (i : ℕ) (hi : i < 1639) : test5 i = true := by
  by_cases h1 : i < 816
  ·
    by_cases h2 : i < 408
    ·
      by_cases h3 : i < 192
      ·
        by_cases h4 : i < 96
        ·
          by_cases h5 : i < 48
          ·
            by_cases h6 : i < 24
            ·
              exact runBlock_get v5b0 i (by omega) (by omega)
            ·
              exact runBlock_get v5b24 i (by omega) (by omega)
          ·
            by_cases h6 : i < 72
            ·
              exact runBlock_get v5b48 i (by omega) (by omega)
            ·
              exact runBlock_get v5b72 i (by omega) (by omega)
        ·
          by_cases h5 : i < 144
          ·
            by_cases h6 : i < 120
            ·
              exact runBlock_get v5b96 i (by omega) (by omega)
            ·
              exact runBlock_get v5b120 i (by omega) (by omega)
          ·
            by_cases h6 : i < 168
            ·
              exact runBlock_get v5b144 i (by omega) (by omega)
            ·
              exact runBlock_get v5b168 i (by omega) (by omega)
      ·
        by_cases h4 : i < 288
        ·
          by_cases h5 : i < 240
          ·
            by_cases h6 : i < 216
            ·
              exact runBlock_get v5b192 i (by omega) (by omega)
            ·
              exact runBlock_get v5b216 i (by omega) (by omega)
          ·
            by_cases h6 : i < 264
            ·
              exact runBlock_get v5b240 i (by omega) (by omega)
            ·
              exact runBlock_get v5b264 i (by omega) (by omega)
        ·
          by_cases h5 : i < 336
          ·
            by_cases h6 : i < 312
            ·
              exact runBlock_get v5b288 i (by omega) (by omega)
            ·
              exact runBlock_get v5b312 i (by omega) (by omega)
          ·
            by_cases h6 : i < 360
            ·
              exact runBlock_get v5b336 i (by omega) (by omega)
            ·
              by_cases h7 : i < 384
              ·
                exact runBlock_get v5b360 i (by omega) (by omega)
              ·
                exact runBlock_get v5b384 i (by omega) (by omega)
    ·
      by_cases h3 : i < 600
      ·
        by_cases h4 : i < 504
        ·
          by_cases h5 : i < 456
          ·
            by_cases h6 : i < 432
            ·
              exact runBlock_get v5b408 i (by omega) (by omega)
            ·
              exact runBlock_get v5b432 i (by omega) (by omega)
          ·
            by_cases h6 : i < 480
            ·
              exact runBlock_get v5b456 i (by omega) (by omega)
            ·
              exact runBlock_get v5b480 i (by omega) (by omega)
        ·
          by_cases h5 : i < 552
          ·
            by_cases h6 : i < 528
            ·
              exact runBlock_get v5b504 i (by omega) (by omega)
            ·
              exact runBlock_get v5b528 i (by omega) (by omega)
          ·
            by_cases h6 : i < 576
            ·
              exact runBlock_get v5b552 i (by omega) (by omega)
            ·
              exact runBlock_get v5b576 i (by omega) (by omega)
      ·
        by_cases h4 : i < 696
        ·
          by_cases h5 : i < 648
          ·
            by_cases h6 : i < 624
            ·
              exact runBlock_get v5b600 i (by omega) (by omega)
            ·
              exact runBlock_get v5b624 i (by omega) (by omega)
          ·
            by_cases h6 : i < 672
            ·
              exact runBlock_get v5b648 i (by omega) (by omega)
            ·
              exact runBlock_get v5b672 i (by omega) (by omega)
        ·
          by_cases h5 : i < 744
          ·
            by_cases h6 : i < 720
            ·
              exact runBlock_get v5b696 i (by omega) (by omega)
            ·
              exact runBlock_get v5b720 i (by omega) (by omega)
          ·
            by_cases h6 : i < 768
            ·
              exact runBlock_get v5b744 i (by omega) (by omega)
            ·
              by_cases h7 : i < 792
              ·
                exact runBlock_get v5b768 i (by omega) (by omega)
              ·
                exact runBlock_get v5b792 i (by omega) (by omega)
  ·
    by_cases h2 : i < 1224
    ·
      by_cases h3 : i < 1008
      ·
        by_cases h4 : i < 912
        ·
          by_cases h5 : i < 864
          ·
            by_cases h6 : i < 840
            ·
              exact runBlock_get v5b816 i (by omega) (by omega)
            ·
              exact runBlock_get v5b840 i (by omega) (by omega)
          ·
            by_cases h6 : i < 888
            ·
              exact runBlock_get v5b864 i (by omega) (by omega)
            ·
              exact runBlock_get v5b888 i (by omega) (by omega)
        ·
          by_cases h5 : i < 960
          ·
            by_cases h6 : i < 936
            ·
              exact runBlock_get v5b912 i (by omega) (by omega)
            ·
              exact runBlock_get v5b936 i (by omega) (by omega)
          ·
            by_cases h6 : i < 984
            ·
              exact runBlock_get v5b960 i (by omega) (by omega)
            ·
              exact runBlock_get v5b984 i (by omega) (by omega)
      ·
        by_cases h4 : i < 1104
        ·
          by_cases h5 : i < 1056
          ·
            by_cases h6 : i < 1032
            ·
              exact runBlock_get v5b1008 i (by omega) (by omega)
            ·
              exact runBlock_get v5b1032 i (by omega) (by omega)
          ·
            by_cases h6 : i < 1080
            ·
              exact runBlock_get v5b1056 i (by omega) (by omega)
            ·
              exact runBlock_get v5b1080 i (by omega) (by omega)
        ·
          by_cases h5 : i < 1152
          ·
            by_cases h6 : i < 1128
            ·
              exact runBlock_get v5b1104 i (by omega) (by omega)
            ·
              exact runBlock_get v5b1128 i (by omega) (by omega)
          ·
            by_cases h6 : i < 1176
            ·
              exact runBlock_get v5b1152 i (by omega) (by omega)
            ·
              by_cases h7 : i < 1200
              ·
                exact runBlock_get v5b1176 i (by omega) (by omega)
              ·
                exact runBlock_get v5b1200 i (by omega) (by omega)
    ·
      by_cases h3 : i < 1440
      ·
        by_cases h4 : i < 1320
        ·
          by_cases h5 : i < 1272
          ·
            by_cases h6 : i < 1248
            ·
              exact runBlock_get v5b1224 i (by omega) (by omega)
            ·
              exact runBlock_get v5b1248 i (by omega) (by omega)
          ·
            by_cases h6 : i < 1296
            ·
              exact runBlock_get v5b1272 i (by omega) (by omega)
            ·
              exact runBlock_get v5b1296 i (by omega) (by omega)
        ·
          by_cases h5 : i < 1368
          ·
            by_cases h6 : i < 1344
            ·
              exact runBlock_get v5b1320 i (by omega) (by omega)
            ·
              exact runBlock_get v5b1344 i (by omega) (by omega)
          ·
            by_cases h6 : i < 1392
            ·
              exact runBlock_get v5b1368 i (by omega) (by omega)
            ·
              by_cases h7 : i < 1416
              ·
                exact runBlock_get v5b1392 i (by omega) (by omega)
              ·
                exact runBlock_get v5b1416 i (by omega) (by omega)
      ·
        by_cases h4 : i < 1536
        ·
          by_cases h5 : i < 1488
          ·
            by_cases h6 : i < 1464
            ·
              exact runBlock_get v5b1440 i (by omega) (by omega)
            ·
              exact runBlock_get v5b1464 i (by omega) (by omega)
          ·
            by_cases h6 : i < 1512
            ·
              exact runBlock_get v5b1488 i (by omega) (by omega)
            ·
              exact runBlock_get v5b1512 i (by omega) (by omega)
        ·
          by_cases h5 : i < 1584
          ·
            by_cases h6 : i < 1560
            ·
              exact runBlock_get v5b1536 i (by omega) (by omega)
            ·
              exact runBlock_get v5b1560 i (by omega) (by omega)
          ·
            by_cases h6 : i < 1608
            ·
              exact runBlock_get v5b1584 i (by omega) (by omega)
            ·
              by_cases h7 : i < 1632
              ·
                exact runBlock_get v5b1608 i (by omega) (by omega)
              ·
                exact runBlock_get v5b1632 i (by omega) (by omega)

lemma sound5 (xs : List W) (hl : live basicOps goal 5 xs.toFinset) : allow5 xs = true := by
  apply match_safe (by decide) (fun i hi => checkState_sound (allows := allow4) sound4 (every5 i hi)) xs hl

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b0 : runBlock test6 0 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b24 : runBlock test6 24 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b48 : runBlock test6 48 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b72 : runBlock test6 72 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b96 : runBlock test6 96 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b120 : runBlock test6 120 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b144 : runBlock test6 144 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b168 : runBlock test6 168 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b192 : runBlock test6 192 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b216 : runBlock test6 216 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b240 : runBlock test6 240 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b264 : runBlock test6 264 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b288 : runBlock test6 288 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b312 : runBlock test6 312 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b336 : runBlock test6 336 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b360 : runBlock test6 360 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b384 : runBlock test6 384 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b408 : runBlock test6 408 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b432 : runBlock test6 432 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b456 : runBlock test6 456 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b480 : runBlock test6 480 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b504 : runBlock test6 504 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b528 : runBlock test6 528 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b552 : runBlock test6 552 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b576 : runBlock test6 576 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b600 : runBlock test6 600 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b624 : runBlock test6 624 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b648 : runBlock test6 648 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b672 : runBlock test6 672 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b696 : runBlock test6 696 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b720 : runBlock test6 720 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b744 : runBlock test6 744 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b768 : runBlock test6 768 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b792 : runBlock test6 792 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b816 : runBlock test6 816 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b840 : runBlock test6 840 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b864 : runBlock test6 864 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b888 : runBlock test6 888 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b912 : runBlock test6 912 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b936 : runBlock test6 936 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b960 : runBlock test6 960 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b984 : runBlock test6 984 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b1008 : runBlock test6 1008 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b1032 : runBlock test6 1032 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b1056 : runBlock test6 1056 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b1080 : runBlock test6 1080 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b1104 : runBlock test6 1104 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b1128 : runBlock test6 1128 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b1152 : runBlock test6 1152 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b1176 : runBlock test6 1176 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b1200 : runBlock test6 1200 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b1224 : runBlock test6 1224 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b1248 : runBlock test6 1248 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b1272 : runBlock test6 1272 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b1296 : runBlock test6 1296 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b1320 : runBlock test6 1320 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b1344 : runBlock test6 1344 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b1368 : runBlock test6 1368 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b1392 : runBlock test6 1392 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b1416 : runBlock test6 1416 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b1440 : runBlock test6 1440 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b1464 : runBlock test6 1464 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b1488 : runBlock test6 1488 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b1512 : runBlock test6 1512 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b1536 : runBlock test6 1536 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b1560 : runBlock test6 1560 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b1584 : runBlock test6 1584 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b1608 : runBlock test6 1608 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b1632 : runBlock test6 1632 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b1656 : runBlock test6 1656 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b1680 : runBlock test6 1680 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b1704 : runBlock test6 1704 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b1728 : runBlock test6 1728 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b1752 : runBlock test6 1752 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b1776 : runBlock test6 1776 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b1800 : runBlock test6 1800 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b1824 : runBlock test6 1824 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b1848 : runBlock test6 1848 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b1872 : runBlock test6 1872 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b1896 : runBlock test6 1896 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b1920 : runBlock test6 1920 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b1944 : runBlock test6 1944 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b1968 : runBlock test6 1968 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b1992 : runBlock test6 1992 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b2016 : runBlock test6 2016 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b2040 : runBlock test6 2040 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b2064 : runBlock test6 2064 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b2088 : runBlock test6 2088 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b2112 : runBlock test6 2112 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b2136 : runBlock test6 2136 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b2160 : runBlock test6 2160 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b2184 : runBlock test6 2184 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b2208 : runBlock test6 2208 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b2232 : runBlock test6 2232 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b2256 : runBlock test6 2256 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b2280 : runBlock test6 2280 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b2304 : runBlock test6 2304 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b2328 : runBlock test6 2328 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b2352 : runBlock test6 2352 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b2376 : runBlock test6 2376 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b2400 : runBlock test6 2400 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b2424 : runBlock test6 2424 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b2448 : runBlock test6 2448 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b2472 : runBlock test6 2472 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b2496 : runBlock test6 2496 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b2520 : runBlock test6 2520 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b2544 : runBlock test6 2544 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b2568 : runBlock test6 2568 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b2592 : runBlock test6 2592 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b2616 : runBlock test6 2616 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b2640 : runBlock test6 2640 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b2664 : runBlock test6 2664 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b2688 : runBlock test6 2688 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b2712 : runBlock test6 2712 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b2736 : runBlock test6 2736 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b2760 : runBlock test6 2760 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b2784 : runBlock test6 2784 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b2808 : runBlock test6 2808 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b2832 : runBlock test6 2832 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b2856 : runBlock test6 2856 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v6b2880 : runBlock test6 2880 20 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 8000000 in
lemma every6 (i : ℕ) (hi : i < 2900) : test6 i = true := by
  by_cases h1 : i < 1440
  ·
    by_cases h2 : i < 720
    ·
      by_cases h3 : i < 360
      ·
        by_cases h4 : i < 168
        ·
          by_cases h5 : i < 72
          ·
            by_cases h6 : i < 24
            ·
              exact runBlock_get v6b0 i (by omega) (by omega)
            ·
              by_cases h7 : i < 48
              ·
                exact runBlock_get v6b24 i (by omega) (by omega)
              ·
                exact runBlock_get v6b48 i (by omega) (by omega)
          ·
            by_cases h6 : i < 120
            ·
              by_cases h7 : i < 96
              ·
                exact runBlock_get v6b72 i (by omega) (by omega)
              ·
                exact runBlock_get v6b96 i (by omega) (by omega)
            ·
              by_cases h7 : i < 144
              ·
                exact runBlock_get v6b120 i (by omega) (by omega)
              ·
                exact runBlock_get v6b144 i (by omega) (by omega)
        ·
          by_cases h5 : i < 264
          ·
            by_cases h6 : i < 216
            ·
              by_cases h7 : i < 192
              ·
                exact runBlock_get v6b168 i (by omega) (by omega)
              ·
                exact runBlock_get v6b192 i (by omega) (by omega)
            ·
              by_cases h7 : i < 240
              ·
                exact runBlock_get v6b216 i (by omega) (by omega)
              ·
                exact runBlock_get v6b240 i (by omega) (by omega)
          ·
            by_cases h6 : i < 312
            ·
              by_cases h7 : i < 288
              ·
                exact runBlock_get v6b264 i (by omega) (by omega)
              ·
                exact runBlock_get v6b288 i (by omega) (by omega)
            ·
              by_cases h7 : i < 336
              ·
                exact runBlock_get v6b312 i (by omega) (by omega)
              ·
                exact runBlock_get v6b336 i (by omega) (by omega)
      ·
        by_cases h4 : i < 528
        ·
          by_cases h5 : i < 432
          ·
            by_cases h6 : i < 384
            ·
              exact runBlock_get v6b360 i (by omega) (by omega)
            ·
              by_cases h7 : i < 408
              ·
                exact runBlock_get v6b384 i (by omega) (by omega)
              ·
                exact runBlock_get v6b408 i (by omega) (by omega)
          ·
            by_cases h6 : i < 480
            ·
              by_cases h7 : i < 456
              ·
                exact runBlock_get v6b432 i (by omega) (by omega)
              ·
                exact runBlock_get v6b456 i (by omega) (by omega)
            ·
              by_cases h7 : i < 504
              ·
                exact runBlock_get v6b480 i (by omega) (by omega)
              ·
                exact runBlock_get v6b504 i (by omega) (by omega)
        ·
          by_cases h5 : i < 624
          ·
            by_cases h6 : i < 576
            ·
              by_cases h7 : i < 552
              ·
                exact runBlock_get v6b528 i (by omega) (by omega)
              ·
                exact runBlock_get v6b552 i (by omega) (by omega)
            ·
              by_cases h7 : i < 600
              ·
                exact runBlock_get v6b576 i (by omega) (by omega)
              ·
                exact runBlock_get v6b600 i (by omega) (by omega)
          ·
            by_cases h6 : i < 672
            ·
              by_cases h7 : i < 648
              ·
                exact runBlock_get v6b624 i (by omega) (by omega)
              ·
                exact runBlock_get v6b648 i (by omega) (by omega)
            ·
              by_cases h7 : i < 696
              ·
                exact runBlock_get v6b672 i (by omega) (by omega)
              ·
                exact runBlock_get v6b696 i (by omega) (by omega)
    ·
      by_cases h3 : i < 1080
      ·
        by_cases h4 : i < 888
        ·
          by_cases h5 : i < 792
          ·
            by_cases h6 : i < 744
            ·
              exact runBlock_get v6b720 i (by omega) (by omega)
            ·
              by_cases h7 : i < 768
              ·
                exact runBlock_get v6b744 i (by omega) (by omega)
              ·
                exact runBlock_get v6b768 i (by omega) (by omega)
          ·
            by_cases h6 : i < 840
            ·
              by_cases h7 : i < 816
              ·
                exact runBlock_get v6b792 i (by omega) (by omega)
              ·
                exact runBlock_get v6b816 i (by omega) (by omega)
            ·
              by_cases h7 : i < 864
              ·
                exact runBlock_get v6b840 i (by omega) (by omega)
              ·
                exact runBlock_get v6b864 i (by omega) (by omega)
        ·
          by_cases h5 : i < 984
          ·
            by_cases h6 : i < 936
            ·
              by_cases h7 : i < 912
              ·
                exact runBlock_get v6b888 i (by omega) (by omega)
              ·
                exact runBlock_get v6b912 i (by omega) (by omega)
            ·
              by_cases h7 : i < 960
              ·
                exact runBlock_get v6b936 i (by omega) (by omega)
              ·
                exact runBlock_get v6b960 i (by omega) (by omega)
          ·
            by_cases h6 : i < 1032
            ·
              by_cases h7 : i < 1008
              ·
                exact runBlock_get v6b984 i (by omega) (by omega)
              ·
                exact runBlock_get v6b1008 i (by omega) (by omega)
            ·
              by_cases h7 : i < 1056
              ·
                exact runBlock_get v6b1032 i (by omega) (by omega)
              ·
                exact runBlock_get v6b1056 i (by omega) (by omega)
      ·
        by_cases h4 : i < 1248
        ·
          by_cases h5 : i < 1152
          ·
            by_cases h6 : i < 1104
            ·
              exact runBlock_get v6b1080 i (by omega) (by omega)
            ·
              by_cases h7 : i < 1128
              ·
                exact runBlock_get v6b1104 i (by omega) (by omega)
              ·
                exact runBlock_get v6b1128 i (by omega) (by omega)
          ·
            by_cases h6 : i < 1200
            ·
              by_cases h7 : i < 1176
              ·
                exact runBlock_get v6b1152 i (by omega) (by omega)
              ·
                exact runBlock_get v6b1176 i (by omega) (by omega)
            ·
              by_cases h7 : i < 1224
              ·
                exact runBlock_get v6b1200 i (by omega) (by omega)
              ·
                exact runBlock_get v6b1224 i (by omega) (by omega)
        ·
          by_cases h5 : i < 1344
          ·
            by_cases h6 : i < 1296
            ·
              by_cases h7 : i < 1272
              ·
                exact runBlock_get v6b1248 i (by omega) (by omega)
              ·
                exact runBlock_get v6b1272 i (by omega) (by omega)
            ·
              by_cases h7 : i < 1320
              ·
                exact runBlock_get v6b1296 i (by omega) (by omega)
              ·
                exact runBlock_get v6b1320 i (by omega) (by omega)
          ·
            by_cases h6 : i < 1392
            ·
              by_cases h7 : i < 1368
              ·
                exact runBlock_get v6b1344 i (by omega) (by omega)
              ·
                exact runBlock_get v6b1368 i (by omega) (by omega)
            ·
              by_cases h7 : i < 1416
              ·
                exact runBlock_get v6b1392 i (by omega) (by omega)
              ·
                exact runBlock_get v6b1416 i (by omega) (by omega)
  ·
    by_cases h2 : i < 2160
    ·
      by_cases h3 : i < 1800
      ·
        by_cases h4 : i < 1608
        ·
          by_cases h5 : i < 1512
          ·
            by_cases h6 : i < 1464
            ·
              exact runBlock_get v6b1440 i (by omega) (by omega)
            ·
              by_cases h7 : i < 1488
              ·
                exact runBlock_get v6b1464 i (by omega) (by omega)
              ·
                exact runBlock_get v6b1488 i (by omega) (by omega)
          ·
            by_cases h6 : i < 1560
            ·
              by_cases h7 : i < 1536
              ·
                exact runBlock_get v6b1512 i (by omega) (by omega)
              ·
                exact runBlock_get v6b1536 i (by omega) (by omega)
            ·
              by_cases h7 : i < 1584
              ·
                exact runBlock_get v6b1560 i (by omega) (by omega)
              ·
                exact runBlock_get v6b1584 i (by omega) (by omega)
        ·
          by_cases h5 : i < 1704
          ·
            by_cases h6 : i < 1656
            ·
              by_cases h7 : i < 1632
              ·
                exact runBlock_get v6b1608 i (by omega) (by omega)
              ·
                exact runBlock_get v6b1632 i (by omega) (by omega)
            ·
              by_cases h7 : i < 1680
              ·
                exact runBlock_get v6b1656 i (by omega) (by omega)
              ·
                exact runBlock_get v6b1680 i (by omega) (by omega)
          ·
            by_cases h6 : i < 1752
            ·
              by_cases h7 : i < 1728
              ·
                exact runBlock_get v6b1704 i (by omega) (by omega)
              ·
                exact runBlock_get v6b1728 i (by omega) (by omega)
            ·
              by_cases h7 : i < 1776
              ·
                exact runBlock_get v6b1752 i (by omega) (by omega)
              ·
                exact runBlock_get v6b1776 i (by omega) (by omega)
      ·
        by_cases h4 : i < 1968
        ·
          by_cases h5 : i < 1872
          ·
            by_cases h6 : i < 1824
            ·
              exact runBlock_get v6b1800 i (by omega) (by omega)
            ·
              by_cases h7 : i < 1848
              ·
                exact runBlock_get v6b1824 i (by omega) (by omega)
              ·
                exact runBlock_get v6b1848 i (by omega) (by omega)
          ·
            by_cases h6 : i < 1920
            ·
              by_cases h7 : i < 1896
              ·
                exact runBlock_get v6b1872 i (by omega) (by omega)
              ·
                exact runBlock_get v6b1896 i (by omega) (by omega)
            ·
              by_cases h7 : i < 1944
              ·
                exact runBlock_get v6b1920 i (by omega) (by omega)
              ·
                exact runBlock_get v6b1944 i (by omega) (by omega)
        ·
          by_cases h5 : i < 2064
          ·
            by_cases h6 : i < 2016
            ·
              by_cases h7 : i < 1992
              ·
                exact runBlock_get v6b1968 i (by omega) (by omega)
              ·
                exact runBlock_get v6b1992 i (by omega) (by omega)
            ·
              by_cases h7 : i < 2040
              ·
                exact runBlock_get v6b2016 i (by omega) (by omega)
              ·
                exact runBlock_get v6b2040 i (by omega) (by omega)
          ·
            by_cases h6 : i < 2112
            ·
              by_cases h7 : i < 2088
              ·
                exact runBlock_get v6b2064 i (by omega) (by omega)
              ·
                exact runBlock_get v6b2088 i (by omega) (by omega)
            ·
              by_cases h7 : i < 2136
              ·
                exact runBlock_get v6b2112 i (by omega) (by omega)
              ·
                exact runBlock_get v6b2136 i (by omega) (by omega)
    ·
      by_cases h3 : i < 2520
      ·
        by_cases h4 : i < 2328
        ·
          by_cases h5 : i < 2232
          ·
            by_cases h6 : i < 2184
            ·
              exact runBlock_get v6b2160 i (by omega) (by omega)
            ·
              by_cases h7 : i < 2208
              ·
                exact runBlock_get v6b2184 i (by omega) (by omega)
              ·
                exact runBlock_get v6b2208 i (by omega) (by omega)
          ·
            by_cases h6 : i < 2280
            ·
              by_cases h7 : i < 2256
              ·
                exact runBlock_get v6b2232 i (by omega) (by omega)
              ·
                exact runBlock_get v6b2256 i (by omega) (by omega)
            ·
              by_cases h7 : i < 2304
              ·
                exact runBlock_get v6b2280 i (by omega) (by omega)
              ·
                exact runBlock_get v6b2304 i (by omega) (by omega)
        ·
          by_cases h5 : i < 2424
          ·
            by_cases h6 : i < 2376
            ·
              by_cases h7 : i < 2352
              ·
                exact runBlock_get v6b2328 i (by omega) (by omega)
              ·
                exact runBlock_get v6b2352 i (by omega) (by omega)
            ·
              by_cases h7 : i < 2400
              ·
                exact runBlock_get v6b2376 i (by omega) (by omega)
              ·
                exact runBlock_get v6b2400 i (by omega) (by omega)
          ·
            by_cases h6 : i < 2472
            ·
              by_cases h7 : i < 2448
              ·
                exact runBlock_get v6b2424 i (by omega) (by omega)
              ·
                exact runBlock_get v6b2448 i (by omega) (by omega)
            ·
              by_cases h7 : i < 2496
              ·
                exact runBlock_get v6b2472 i (by omega) (by omega)
              ·
                exact runBlock_get v6b2496 i (by omega) (by omega)
      ·
        by_cases h4 : i < 2712
        ·
          by_cases h5 : i < 2616
          ·
            by_cases h6 : i < 2568
            ·
              by_cases h7 : i < 2544
              ·
                exact runBlock_get v6b2520 i (by omega) (by omega)
              ·
                exact runBlock_get v6b2544 i (by omega) (by omega)
            ·
              by_cases h7 : i < 2592
              ·
                exact runBlock_get v6b2568 i (by omega) (by omega)
              ·
                exact runBlock_get v6b2592 i (by omega) (by omega)
          ·
            by_cases h6 : i < 2664
            ·
              by_cases h7 : i < 2640
              ·
                exact runBlock_get v6b2616 i (by omega) (by omega)
              ·
                exact runBlock_get v6b2640 i (by omega) (by omega)
            ·
              by_cases h7 : i < 2688
              ·
                exact runBlock_get v6b2664 i (by omega) (by omega)
              ·
                exact runBlock_get v6b2688 i (by omega) (by omega)
        ·
          by_cases h5 : i < 2808
          ·
            by_cases h6 : i < 2760
            ·
              by_cases h7 : i < 2736
              ·
                exact runBlock_get v6b2712 i (by omega) (by omega)
              ·
                exact runBlock_get v6b2736 i (by omega) (by omega)
            ·
              by_cases h7 : i < 2784
              ·
                exact runBlock_get v6b2760 i (by omega) (by omega)
              ·
                exact runBlock_get v6b2784 i (by omega) (by omega)
          ·
            by_cases h6 : i < 2856
            ·
              by_cases h7 : i < 2832
              ·
                exact runBlock_get v6b2808 i (by omega) (by omega)
              ·
                exact runBlock_get v6b2832 i (by omega) (by omega)
            ·
              by_cases h7 : i < 2880
              ·
                exact runBlock_get v6b2856 i (by omega) (by omega)
              ·
                exact runBlock_get v6b2880 i (by omega) (by omega)

lemma sound6 (xs : List W) (hl : live basicOps goal 6 xs.toFinset) : allow6 xs = true := by
  apply match_safe (by decide) (fun i hi => checkState_sound (allows := allow5) sound5 (every6 i hi)) xs hl

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v7b0 : runBlock test7 0 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v7b24 : runBlock test7 24 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v7b48 : runBlock test7 48 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v7b72 : runBlock test7 72 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v7b96 : runBlock test7 96 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v7b120 : runBlock test7 120 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v7b144 : runBlock test7 144 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v7b168 : runBlock test7 168 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v7b192 : runBlock test7 192 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v7b216 : runBlock test7 216 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v7b240 : runBlock test7 240 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v7b264 : runBlock test7 264 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v7b288 : runBlock test7 288 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v7b312 : runBlock test7 312 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v7b336 : runBlock test7 336 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v7b360 : runBlock test7 360 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v7b384 : runBlock test7 384 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v7b408 : runBlock test7 408 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v7b432 : runBlock test7 432 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v7b456 : runBlock test7 456 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v7b480 : runBlock test7 480 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v7b504 : runBlock test7 504 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v7b528 : runBlock test7 528 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v7b552 : runBlock test7 552 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v7b576 : runBlock test7 576 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v7b600 : runBlock test7 600 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v7b624 : runBlock test7 624 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v7b648 : runBlock test7 648 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v7b672 : runBlock test7 672 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v7b696 : runBlock test7 696 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v7b720 : runBlock test7 720 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v7b744 : runBlock test7 744 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v7b768 : runBlock test7 768 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v7b792 : runBlock test7 792 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v7b816 : runBlock test7 816 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v7b840 : runBlock test7 840 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v7b864 : runBlock test7 864 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v7b888 : runBlock test7 888 3 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 8000000 in
lemma every7 (i : ℕ) (hi : i < 891) : test7 i = true := by
  by_cases h1 : i < 456
  ·
    by_cases h2 : i < 216
    ·
      by_cases h3 : i < 96
      ·
        by_cases h4 : i < 48
        ·
          by_cases h5 : i < 24
          ·
            exact runBlock_get v7b0 i (by omega) (by omega)
          ·
            exact runBlock_get v7b24 i (by omega) (by omega)
        ·
          by_cases h5 : i < 72
          ·
            exact runBlock_get v7b48 i (by omega) (by omega)
          ·
            exact runBlock_get v7b72 i (by omega) (by omega)
      ·
        by_cases h4 : i < 144
        ·
          by_cases h5 : i < 120
          ·
            exact runBlock_get v7b96 i (by omega) (by omega)
          ·
            exact runBlock_get v7b120 i (by omega) (by omega)
        ·
          by_cases h5 : i < 168
          ·
            exact runBlock_get v7b144 i (by omega) (by omega)
          ·
            by_cases h6 : i < 192
            ·
              exact runBlock_get v7b168 i (by omega) (by omega)
            ·
              exact runBlock_get v7b192 i (by omega) (by omega)
    ·
      by_cases h3 : i < 336
      ·
        by_cases h4 : i < 264
        ·
          by_cases h5 : i < 240
          ·
            exact runBlock_get v7b216 i (by omega) (by omega)
          ·
            exact runBlock_get v7b240 i (by omega) (by omega)
        ·
          by_cases h5 : i < 288
          ·
            exact runBlock_get v7b264 i (by omega) (by omega)
          ·
            by_cases h6 : i < 312
            ·
              exact runBlock_get v7b288 i (by omega) (by omega)
            ·
              exact runBlock_get v7b312 i (by omega) (by omega)
      ·
        by_cases h4 : i < 384
        ·
          by_cases h5 : i < 360
          ·
            exact runBlock_get v7b336 i (by omega) (by omega)
          ·
            exact runBlock_get v7b360 i (by omega) (by omega)
        ·
          by_cases h5 : i < 408
          ·
            exact runBlock_get v7b384 i (by omega) (by omega)
          ·
            by_cases h6 : i < 432
            ·
              exact runBlock_get v7b408 i (by omega) (by omega)
            ·
              exact runBlock_get v7b432 i (by omega) (by omega)
  ·
    by_cases h2 : i < 672
    ·
      by_cases h3 : i < 552
      ·
        by_cases h4 : i < 504
        ·
          by_cases h5 : i < 480
          ·
            exact runBlock_get v7b456 i (by omega) (by omega)
          ·
            exact runBlock_get v7b480 i (by omega) (by omega)
        ·
          by_cases h5 : i < 528
          ·
            exact runBlock_get v7b504 i (by omega) (by omega)
          ·
            exact runBlock_get v7b528 i (by omega) (by omega)
      ·
        by_cases h4 : i < 600
        ·
          by_cases h5 : i < 576
          ·
            exact runBlock_get v7b552 i (by omega) (by omega)
          ·
            exact runBlock_get v7b576 i (by omega) (by omega)
        ·
          by_cases h5 : i < 624
          ·
            exact runBlock_get v7b600 i (by omega) (by omega)
          ·
            by_cases h6 : i < 648
            ·
              exact runBlock_get v7b624 i (by omega) (by omega)
            ·
              exact runBlock_get v7b648 i (by omega) (by omega)
    ·
      by_cases h3 : i < 792
      ·
        by_cases h4 : i < 720
        ·
          by_cases h5 : i < 696
          ·
            exact runBlock_get v7b672 i (by omega) (by omega)
          ·
            exact runBlock_get v7b696 i (by omega) (by omega)
        ·
          by_cases h5 : i < 744
          ·
            exact runBlock_get v7b720 i (by omega) (by omega)
          ·
            by_cases h6 : i < 768
            ·
              exact runBlock_get v7b744 i (by omega) (by omega)
            ·
              exact runBlock_get v7b768 i (by omega) (by omega)
      ·
        by_cases h4 : i < 840
        ·
          by_cases h5 : i < 816
          ·
            exact runBlock_get v7b792 i (by omega) (by omega)
          ·
            exact runBlock_get v7b816 i (by omega) (by omega)
        ·
          by_cases h5 : i < 864
          ·
            exact runBlock_get v7b840 i (by omega) (by omega)
          ·
            by_cases h6 : i < 888
            ·
              exact runBlock_get v7b864 i (by omega) (by omega)
            ·
              exact runBlock_get v7b888 i (by omega) (by omega)

lemma sound7 (xs : List W) (hl : live basicOps goal 7 xs.toFinset) : allow7 xs = true := by
  apply match_safe (by decide) (fun i hi => checkState_sound (allows := allow6) sound6 (every7 i hi)) xs hl

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v8b0 : runBlock test8 0 24 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma v8b24 : runBlock test8 24 6 = true := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 8000000 in
lemma every8 (i : ℕ) (hi : i < 30) : test8 i = true := by
  by_cases h1 : i < 24
  ·
    exact runBlock_get v8b0 i (by omega) (by omega)
  ·
    exact runBlock_get v8b24 i (by omega) (by omega)

lemma sound8 (xs : List W) (hl : live basicOps goal 8 xs.toFinset) : allow8 xs = true := by
  apply match_safe (by decide) (fun i hi => checkState_sound (allows := allow7) sound7 (every8 i hi)) xs hl

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
lemma rootCheck : checkState 8 allow8 inputs = true := by decide +kernel

lemma no_small (C : Circuit) (hm : Monotone2 C) (hs : C.size ≤ 9)
    (he : ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = true ↔
      ∃ u v : Fin 6, (u.val, v.val) ∈ edges ∧ x u = true ∧ x v = true) : False := by
  exact checkState_sound sound8 rootCheck (extend_live hs (input_live _ (get_build C hm he)))

end PEqualNP.Outside.L_meta_742

theorem PEqualNP.Outside.L_meta_742 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 6, (u.val, v.val) ∈ ([(0, 1), (0, 2), (1, 2), (3, 4), (3, 5), (4, 5), (0, 3), (1, 4), (2, 5)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) → 10 ≤ C.size := by
  intro C hm he
  by_contra h
  exact PEqualNP.Outside.L_meta_742.no_small C hm (by omega) he
