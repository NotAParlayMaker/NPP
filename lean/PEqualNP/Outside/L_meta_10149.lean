import Mathlib
import PEqualNP.Defs
import PEqualNP.Defs.Represents

-- The four by four certificate and live-set argument are from L-meta-6032.
-- The prefix invariance fact for wire evaluation is from L-meta-1483.
-- Removing the duplicate row and column saves two gates. The remaining table is 4974 after relabelling.

namespace PEqualNP.Outside.L_meta_10149.Four

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

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

abbrev m := 28
abbrev W := BitVec (2*m)
def ops (a b : W) : List W := [a &&& b, a ||| b]
def sep (w : W) : BitVec m := ((w >>> m) &&& ~~~w).setWidth m
def cuts (ws : List W) : BitVec m := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec m) ++ (0 : BitVec m)
def inputs : List W := [137178972197, 17454764013120, 2234207631589512, 69805794463353106, 70069677040276005, 1971287752706050, 16500259078168, 128985867712]
def available : List W := 0 :: (-1 : W) :: inputs
def rows : List Nat := [0, 13, 0, 10, 14, 0, 7, 11, 15, 4, 7, 13, 4, 7, 10, 14, 0, 4, 10, 11, 10, 11, 13, 0, 4, 13, 14, 15, 1, 1, 2, 2, 2, 3, 3, 3, 3, 5, 5, 5, 6, 6, 6, 6, 8, 8, 8, 8, 9, 9, 9, 12, 12, 12, 12, 12]
def leftAt (i : Fin (2*m)) : Fin 4 := Fin.ofNat 4 ((rows.getD i.val 0) / 4)
def rightAt (i : Fin (2*m)) : Fin 4 := Fin.ofNat 4 ((rows.getD i.val 0) % 4)
def graph (u v : Fin 4) : Bool := (4974 : Nat).testBit (4*u.val + v.val)

def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))
def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

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
def differs (i : Fin m) (w : W) : Prop :=
  w.getLsbD (m+i.val) = true ∧ w.getLsbD i.val = false

theorem ops_differs (i : Fin m) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (h : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl <;>
    simp only [differs, BitVec.getLsbD_and, BitVec.getLsbD_or] at *
  all_goals
    cases ha : a.getLsbD (m+i.val) <;> cases hb : b.getLsbD (m+i.val) <;>
      cases hc : a.getLsbD i.val <;> cases hd : b.getLsbD i.val <;> simp_all

theorem goal_differs : ∀ i : Fin m, differs i goal := by unfold differs; decide +kernel

theorem cuts_spec (ws : List W) (i : Fin m) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or,Bool.or_eq_true,ih]
    have hi : i.val < 2*m := by have := i.isLt; omega
    simp [sep,i.isLt,differs,hi,Nat.add_comm, Bool.and_eq_true]

theorem cuts_full {k : ℕ} {ws : List W} (h : live basicOps goal k ws.toFinset) :
    cuts ws = -1 := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (goal_differs ⟨j, hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes m)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext w
  simp [ops, BitVec.and_comm, BitVec.or_comm]

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
    · exact List.nodup_cons.mpr ⟨fun hm => (List.nodup_cons.mp habr).1 (List.mem_cons_of_mem _ hm),
        (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2⟩
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

theorem must_have_inputs {s : Finset W} {k : Nat} (hs : s ⊆ available.toFinset)
    (hl : live basicOps goal k s) : inputs.toFinset ⊆ s := by
  intro a ha
  have necessary : inputs.all (fun a => (List.finRange m).any (fun i => available.all (fun b =>
      !(b.getLsbD (m+i.val) && !b.getLsbD i.val) || b == a))) = true := by decide +kernel
  obtain ⟨i, _, hall⟩ :=
    List.any_eq_true.mp (List.all_eq_true.mp necessary a (List.mem_toFinset.mp ha))
  obtain ⟨b, hb, hd⟩ := live_separates (differs i) (goal_differs i) (ops_differs i) hl
  have checked := List.all_eq_true.mp hall b (List.mem_toFinset.mp (hs hb))
  have eq : b = a := by simpa [hd.1, hd.2] using checked
  exact eq ▸ hb

theorem starting_sets {s : Finset W} (hs : s ⊆ available.toFinset)
    (hl : live basicOps goal 8 s) :
    s = inputs.toFinset ∨ s = (0 :: inputs).toFinset ∨ s = ((-1 : W) :: inputs).toFinset := by
  have hi := must_have_inputs hs hl
  have hn : ¬ ((0 : W) ∈ s ∧ (-1 : W) ∈ s) := by
    rintro ⟨h0, h1⟩
    have ha : available.toFinset ⊆ s := by
      intro x hx
      simp only [available, List.toFinset_cons, Finset.mem_insert] at hx
      rcases hx with rfl | rfl | h
      · exact h0
      · exact h1
      · exact hi h
    have hc := Finset.card_le_card ha
    have hd := live_card hl
    have h10 : available.toFinset.card = 10 := by decide
    omega
  by_cases h0 : (0 : W) ∈ s
  · right; left
    ext x
    have h1 : (-1 : W) ∉ s := fun h => hn ⟨h0,h⟩
    constructor
    · intro hx
      have h := hs hx
      simp only [available, List.toFinset_cons, Finset.mem_insert] at h ⊢
      rcases h with h | rfl | h
      · exact Or.inl h
      · exact (h1 hx).elim
      · exact Or.inr h
    · simp only [List.toFinset_cons, Finset.mem_insert]
      rintro (rfl | h)
      · exact h0
      · exact hi h
  · by_cases h1 : (-1 : W) ∈ s
    · right; right
      ext x
      constructor
      · intro hx
        have h := hs hx
        simp only [available, List.toFinset_cons, Finset.mem_insert] at h ⊢
        rcases h with rfl | h | h
        · exact (h0 hx).elim
        · exact Or.inl h
        · exact Or.inr h
      · simp only [List.toFinset_cons, Finset.mem_insert]
        rintro (rfl | h)
        · exact h1
        · exact hi h
    · left
      apply Finset.Subset.antisymm _ hi
      intro x hx
      have hh := hs hx
      simp only [available, List.toFinset_cons, Finset.mem_insert] at hh
      rcases hh with rfl | rfl | h
      · exact (h0 hx).elim
      · exact (h1 hx).elim
      · exact h

def dispatch (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) : Bool :=
  let base := cuts r
  (ops a b).any fun w =>
    let v := sep w ||| base
    !(w == a || w == b || r.contains w) && (
    ((v == -1) && next extra (w :: r)) ||
    ((extra != 0) && (((v ||| sep a == -1) && next (extra - 1) (w :: a :: r)) ||
                       ((v ||| sep b == -1) && next (extra - 1) (w :: b :: r)))) ||
    ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && next (extra - 2) (w :: a :: b :: r)))
def optimized : ℕ → ℕ → List W → Bool
  | 0, _, ws => ws == [goal]
  | k+1, extra, ws => ws == [goal] ||
    (pairs ws).any (fun (a, b, r) => dispatch extra (optimized k) a b r)
theorem dispatch_complete {k extra : ℕ} {a b z : W} {r kept : List W}
    (next : ℕ → List W → Bool)
    (hz : z ∈ basicOps a b) (hk : kept ∈ keepChoices a b r)
    (hfresh : z ∉ a :: b :: r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts (z :: kept) = -1) (ht : next (k - kept.length) (z :: kept) = true) :
    dispatch extra next a b r = true := by
  apply List.any_eq_true.mpr
  refine ⟨z, List.mem_toFinset.mp hz, ?_⟩
  rw [Bool.and_eq_true]
  constructor
  · simpa [List.mem_cons, and_assoc] using hfresh
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
          exact Finset.mem_insert_of_mem
            (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live basicOps goal k (z :: kept).toFinset := by
          simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        apply dispatch_complete (k := k) (extra := extra) (optimized k) hop hk
          (fun hm => hout (List.mem_toFinset.mpr (perm.mem_iff.mpr hm)))
          (by omega) (by omega) (cuts_full hl)
        apply ih _ _ hnd _ hl
        simp; omega
      simp only [optimized, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs hz⟩
      · exact ⟨(b, a, r), swap,
          go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem run0 : optimized 8 1 inputs = false := by decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem run1 : optimized 8 0 (0 :: inputs) = false := by decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem run2 : optimized 8 0 ((-1 : W) :: inputs) = false := by decide +kernel

theorem noBuild : ¬ build basicOps goal 8 available.toFinset := by
  intro h
  obtain ⟨s, hs, hl⟩ := compress h
  rcases starting_sets hs hl with he | he | he
  · exact Bool.noConfusion (run0.symm.trans
      (optimized_complete 8 inputs 1 (by decide) (by decide) (he ▸ hl)))
  · exact Bool.noConfusion (run1.symm.trans
      (optimized_complete 8 (0 :: inputs) 0 (by decide) (by decide) (he ▸ hl)))
  · exact Bool.noConfusion (run2.symm.trans
      (optimized_complete 8 ((-1 : W) :: inputs) 0 (by decide) (by decide) (he ▸ hl)))

def gateWord (ws : List W) (g : Gate) : W :=
  let args := g.inputs.map fun i => ws.getD i 0
  match g.op with
  | .and => args.foldr (· &&& ·) (BitVec.allOnes _)
  | .or => args.foldr (· ||| ·) 0
  | _ => 0

def stepWord (ws : List W) (g : Gate) : List W := ws ++ [gateWord ws g]
def stepBool (ws : List Bool) (g : Gate) : List Bool :=
  ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]

def GateOK (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem getD_bits (ws : List W) (r j : Nat) :
    (ws.map fun w => w.getLsbD r).getD j false = (ws.getD j 0).getLsbD r := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases ws[j]? <;> simp

theorem fold_and_bit (ws : List W) (r : Fin (2*m)) :
    (ws.foldr (· &&& ·) (BitVec.allOnes _)).getLsbD r.val =
      (ws.map fun w => w.getLsbD r.val).all id := by
  induction ws with
  | nil => simp [r.isLt]
  | cons a t ih => simp only [List.foldr_cons, List.map_cons, List.all_cons, BitVec.getLsbD_and, id, ih]

theorem fold_or_bit (ws : List W) (r : Fin (2*m)) :
    (ws.foldr (· ||| ·) 0).getLsbD r.val =
      (ws.map fun w => w.getLsbD r.val).any id := by
  induction ws with
  | nil => simp
  | cons a t ih => simp only [List.foldr_cons, List.map_cons, List.any_cons, BitVec.getLsbD_or, id, ih]

theorem step_bits (ws : List W) (g : Gate) (hg : GateOK g) (r : Fin (2*m)) :
    (stepWord ws g).map (fun w => w.getLsbD r.val) =
      stepBool (ws.map fun w => w.getLsbD r.val) g := by
  have hopen : g.op = GateOp.and ∨ g.op = GateOp.or := by simpa using hg.1
  unfold stepWord stepBool
  simp only [List.map_append, List.map_cons, List.map_nil, List.append_cancel_left_eq, List.cons.injEq, and_true]
  unfold gateWord
  rcases hopen with h | h
  · simp only [h, GateOp.eval, fold_and_bit, List.map_map, Function.comp_def, getD_bits]
  · simp only [h, GateOp.eval, fold_or_bit, List.map_map, Function.comp_def, getD_bits]

theorem run_bits (gs : List Gate) (hgs : ∀ g ∈ gs, GateOK g) (ws : List W) (r : Fin (2*m)) :
    (gs.foldl stepWord ws).map (fun w => w.getLsbD r.val) =
      gs.foldl stepBool (ws.map fun w => w.getLsbD r.val) := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g t ih =>
    simp only [List.foldl_cons]
    rw [ih (fun a ha => hgs a (List.mem_cons_of_mem _ ha)), step_bits ws g (hgs g (by simp)) r]

theorem getD_in (ws : List W) (s : Finset W) (hw : ∀ a ∈ ws, a ∈ s)
    (h0 : 0 ∈ s) (j : Nat) : ws.getD j 0 ∈ s := by
  rw [List.getD_eq_getElem?_getD]
  cases h : ws[j]? with
  | none => exact h0
  | some a => exact hw a (List.mem_of_getElem? h)

theorem gateWord_cases (ws : List W) (s : Finset W) (hw : ∀ a ∈ ws, a ∈ s)
    (h0 : 0 ∈ s) (h1 : (-1 : W) ∈ s) (g : Gate) (hg : GateOK g) :
    gateWord ws g ∈ s ∨
      ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ gateWord ws g ∈ basicOps a b := by
  obtain ⟨op, xs⟩ := g
  have hop : op = GateOp.and ∨ op = GateOp.or := by simpa using hg.1
  have hlen : xs.length ≤ 2 := hg.2
  cases xs with
  | nil =>
    rcases hop with rfl | rfl
    · exact Or.inl h1
    · exact Or.inl h0
  | cons i xs =>
    cases xs with
    | nil =>
      rcases hop with rfl | rfl <;> exact Or.inl (by simpa [gateWord] using getD_in ws s hw h0 i)
    | cons j xs =>
      cases xs with
      | cons k ks => simp at hlen
      | nil =>
        let a := ws.getD i 0
        let b := ws.getD j 0
        have ha : a ∈ s := getD_in ws s hw h0 i
        have hb : b ∈ s := getD_in ws s hw h0 j
        have hform : gateWord ws ⟨op, [i,j]⟩ = a &&& b ∨
            gateWord ws ⟨op, [i,j]⟩ = a ||| b := by
          rcases hop with rfl | rfl
          · left; simp [gateWord, a, b]
          · right; simp [gateWord, a, b]
        by_cases eq : a = b
        · left
          rcases hform with h | h <;> rw [h, ← eq] <;> simpa using ha
        · right
          exact ⟨a, ha, b, hb, eq, by simpa [ops] using hform⟩

theorem run_build (gs : List Gate) (hgs : ∀ g ∈ gs, GateOK g) (ws : List W)
    (s : Finset W) (hw : ∀ a ∈ ws, a ∈ s)
    (h0 : 0 ∈ s) (h1 : (-1 : W) ∈ s) (out : Nat) :
    build basicOps ((gs.foldl stepWord ws).getD out 0) gs.length s := by
  induction gs generalizing ws s with
  | nil => exact getD_in ws s hw h0 out
  | cons g t ih =>
    have ht : ∀ u ∈ t, GateOK u := fun u hu => hgs u (List.mem_cons_of_mem _ hu)
    have hz := gateWord_cases ws s hw h0 h1 g (hgs g (by simp))
    rcases hz with hm | ⟨a, ha, b, hb, hab, hmem⟩
    · apply Or.inl
      apply ih ht (stepWord ws g) s _ h0 h1
      intro x hx
      simp only [stepWord, List.mem_append, List.mem_singleton] at hx
      exact hx.elim (hw x) (fun h => h ▸ hm)
    · apply Or.inr
      refine ⟨a, ha, b, hb, hab, gateWord ws g, hmem, ?_⟩
      apply ih ht (stepWord ws g) (insert (gateWord ws g) s) _
        (Finset.mem_insert_of_mem h0) (Finset.mem_insert_of_mem h1)
      intro x hx
      simp only [stepWord, List.mem_append, List.mem_singleton] at hx
      exact hx.elim (fun hx' => Finset.mem_insert_of_mem (hw x hx')) (fun h => h ▸ Finset.mem_insert_self _ _)

theorem extend_build {a b : Nat} {s : Finset W} (h : a ≤ b)
    (hb : build basicOps goal a s) : build basicOps goal b s := by
  induction h with
  | refl => exact hb
  | step _ ih => exact Or.inl ih

theorem inputs_bits : ∀ r : Fin (2*m),
    (inputs.map fun w => w.getLsbD r.val) = oneEach (leftAt r) (rightAt r) := by decide +kernel

theorem goal_bits : ∀ r : Fin (2*m),
    goal.getLsbD r.val = graph (leftAt r) (rightAt r) := by decide +kernel

theorem lower : ¬ RepSizeAtMost graph 8 := by
  rintro ⟨C, hC, hsz, hrep⟩
  have hgs : ∀ g ∈ C.gates, GateOK g := hC
  let out := (C.gates.foldl stepWord inputs).getD C.output 0
  have heq : out = goal := by
    apply BitVec.eq_of_getElem_eq
    intro i h
    have hr := run_bits C.gates hgs inputs ⟨i,h⟩
    have bit : out.getLsbD i = C.eval (oneEach (leftAt ⟨i,h⟩) (rightAt ⟨i,h⟩)) := by
      change ((C.gates.foldl stepWord inputs).getD C.output 0).getLsbD i = _
      rw [← getD_bits, hr, inputs_bits ⟨i,h⟩]
      rfl
    have ht := hrep (leftAt ⟨i,h⟩) (rightAt ⟨i,h⟩)
    have hg := goal_bits ⟨i,h⟩
    simpa only [BitVec.getLsbD_eq_getElem h] using bit.trans (ht.trans hg.symm)
  have hb : build basicOps out C.gates.length available.toFinset :=
    run_build C.gates hgs inputs available.toFinset (by intro a ha; simp [available, ha])
      (by simp [available]) (by simp [available]) C.output
  exact noBuild (extend_build hsz (heq ▸ hb))

end PEqualNP.Outside.L_meta_10149.Four

namespace PEqualNP.Outside.L_meta_10149.Wire
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_append (gs rest : List Gate) (w : List Bool) :
    wiresFrom (gs ++ rest) w = wiresFrom rest (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    change wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) = _
    rw [ht]; simp

theorem wiresFrom_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem prefix_val (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]
end PEqualNP.Outside.L_meta_10149.Wire

namespace PEqualNP.Outside.L_meta_10149.Eliminate
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_10149.Wire
def nextWire (V : List Bool) (g : Gate) : Bool := g.op.eval (g.inputs.map (fun i => V.getD i false))
def step (V : List Bool) (g : Gate) : List Bool := V ++ [nextWire V g]
def reads (p : Nat) (g : Gate) : Bool := decide (p ∈ g.inputs)
abbrev Good (g : Gate) := g.op ∈ ({GateOp.and,GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2
set_option maxHeartbeats 750000 in
lemma lastRead (xs : List Bool) (v : Bool) : (xs ++ [v]).getD xs.length false = v := by
  simp [List.getD_eq_getElem?_getD]
set_option maxHeartbeats 750000 in
lemma stable (xs : List Bool) (x : Bool) (i : Nat) (hn : i ≠ xs.length) :
    (xs ++ [x]).getD i false = xs.getD i false := by
  by_cases h : i < xs.length
  · exact List.getD_append _ _ _ _ h
  · rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by omega)]
set_option maxHeartbeats 750000 in
private lemma deletedGate {p : Nat} (g : Gate) (hg : Good g) (hit : p ∈ g.inputs) :
    ∃ w : Nat, ∀ V : List Bool, V.getD p false = false →
      nextWire V g = V.getD w false := by
  obtain ⟨op,l⟩ := g
  change _ ∈ _ ∧ l.length ≤ 2 at hg
  change p ∈ l at hit
  obtain ⟨hop,len⟩ := hg
  rcases hop with hop|hop
  · change op = GateOp.and at hop
    subst op
    refine ⟨p,fun V h => ?_⟩
    rw [h]
    exact List.all_eq_false.mpr ⟨false,List.mem_map.mpr ⟨p,hit,h⟩,by decide⟩
  · change op = GateOp.or at hop
    subst op
    cases l with
    | nil => simp at hit
    | cons a l =>
      cases l with
      | nil => exact ⟨a,by simp [nextWire,GateOp.eval]⟩
      | cons b l =>
        have eqn : l = [] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at len; omega)
        subst l
        rcases (by simpa using hit : p = a ∨ p = b) with rfl|rfl
        · exact ⟨b,by intro V hv; change (V.getD _ false || (V.getD _ false || false)) = _; rw [hv]; simp⟩
        · exact ⟨a,by intro V hv; change (V.getD _ false || (V.getD _ false || false)) = _; rw [hv]; simp⟩

def touches (P : Finset Nat) (g : Gate) := g.inputs.any (fun i => decide (i ∈ P))

set_option maxHeartbeats 750000 in
theorem compressFuture {α : Type} (P : Finset Nat) (out dummy : Nat) (gs : List Gate) (ok : ∀ g ∈ gs, Good g) :
    ∀ (A B : α → List Bool) (m t : Nat) (f : Nat → Nat),
      (∀ x, (A x).length = m) → (∀ x, (B x).length = t) →
      (t + gs.length ≤ dummy) →
      (∀ i, f i < t ∨ f i = dummy) →
      (∀ x i, (A x).getD i false = (B x).getD (f i) false) →
      (∀ x p, p ∈ P → (wiresFrom gs (A x)).getD p false = false) →
      ∃ D : Circuit, Monotone2 D ∧ D.size + gs.countP (touches P) = gs.length ∧
        ∀ x, D.eval (B x) = ((Circuit.mk gs out).eval (A x)) := by
  induction gs with
  | nil =>
    intro A B m t f _ _ _ _ ha _
    exact ⟨⟨[],f out⟩,by simp [Monotone2],rfl, fun x => (ha x out).symm⟩
  | cons g gs ih =>
    intro A B m t f la lb cap safe agr finalPin
    let A' (x : α) := step (A x) g
    have la' (x : α) : (A' x).length = m+1 := by simp [A',step,la]
    have pin (x : α) (p) (hp : p ∈ P) : (A x).getD p false=false := by
      by_cases lt : p<(A x).length
      · exact (prefix_val (g::gs) (A x) p lt).symm.trans (finalPin x p hp)
      · exact List.getD_eq_default _ _ (by omega)
    have h : Good g := ok _ (by simp)
    have tail g' (hg : g' ∈ gs) := ok g' (by simp [hg])
    by_cases hit : touches P g = true
    · obtain ⟨p,hin,hp⟩ := List.any_eq_true.mp hit
      have hpin := of_decide_eq_true hp
      obtain ⟨w,hw⟩ := deletedGate g h hin
      let f' (i : Nat) := if i = m then f w else f i
      have fresh (x : α) (i : Nat) : (A' x).getD i false = (B x).getD (f' i) false := by
        by_cases e : i = m
        · subst i
          simp only [f',ite_true, A',step,← la x,lastRead, hw _ (pin x p hpin), agr]
        · simp only [f',if_neg e,A',step,stable (A x) (nextWire (A x) g) i (by simpa only [la x] using e),agr]
      obtain ⟨D,mono,count,correct⟩ := ih tail A' B (m+1) t f' la' lb
        (by simp at cap; omega) (fun i => by dsimp [f']; split <;> apply safe) fresh finalPin
      exact ⟨D,mono,by simp [List.countP_cons,hit] at count ⊢; omega, correct⟩
    · let g' : Gate := ⟨g.op,g.inputs.map f⟩
      let B' (x : α) := step (B x) g'
      have lb' (x : α) : (B' x).length = t+1 := by simp [B',step,lb]
      have geq (x : α) : nextWire (A x) g = nextWire (B x) g' := by
        dsimp [nextWire,g']
        rw [List.map_map]
        exact congrArg g.op.eval (List.map_congr_left (fun i _ => agr x i))
      let f' (i : Nat) := if i = m then t else f i
      have fresh (x : α) (i : Nat) : (A' x).getD i false = (B' x).getD (f' i) false := by
        by_cases e : i = m
        · subst i
          simp only [f',ite_true,A',B',step,← la x,← lb x,lastRead,geq]
        · have old : f i ≠ (B x).length := by
            have := safe i
            have := lb x
            simp only [List.length_cons] at cap
            omega
          simp only [f',if_neg e,A',B',step,stable (A x) (nextWire (A x) g) i (by simpa only [la x] using e),stable (B x) (nextWire (B x) g') (f i) old,agr]
      obtain ⟨D,mono,count,correct⟩ := ih tail A' B' (m+1) (t+1) f' la' lb'
        (by simp at cap; omega) (fun i => by have := safe i; dsimp [f']; split <;> omega) fresh finalPin
      refine ⟨⟨g'::D.gates,D.output⟩,?_,?_,correct⟩
      · intro k hk
        rcases List.mem_cons.mp hk with rfl|hh
        · exact ⟨h.1,by simpa [g'] using h.2⟩
        · exact mono k hh
      · change (g' :: D.gates).length + _ = _
        change D.gates.length + _ = _ at count
        simp [List.countP_cons,hit] at count ⊢
        omega

set_option maxHeartbeats 750000 in
theorem compress {α : Type} (P : Finset Nat) (out dummy : Nat) (gs : List Gate) (ok : ∀ g ∈ gs, Good g) :
    ∀ (A B : α → List Bool) (m t : Nat) (f : Nat → Nat),
      (∀ x, (A x).length = m) → (∀ x, (B x).length = t) →
      (∀ p ∈ P, p < m) → (t + gs.length ≤ dummy) →
      (∀ i, f i < t ∨ f i = dummy) →
      (∀ x i, (A x).getD i false = (B x).getD (f i) false) →
      (∀ x p, p ∈ P → (A x).getD p false = false) →
      ∃ D : Circuit, Monotone2 D ∧ D.size + gs.countP (touches P) = gs.length ∧
        ∀ x, D.eval (B x) = ((Circuit.mk gs out).eval (A x)) := by
  intro A B m t f la lb pm cap safe agree pin
  apply compressFuture P out dummy gs ok A B m t f la lb cap safe agree
  intro x p hp
  rw [prefix_val _ _ _ (by rw [la];exact pm p hp)]
  exact pin x p hp

end PEqualNP.Outside.L_meta_10149.Eliminate

namespace PEqualNP.Outside.L_meta_10149.Eliminate
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents PEqualNP.Outside.L_meta_10149.Wire

def full (u v : Fin 5) := (7711899 : Nat).testBit (5*u.val+v.val)
def rr : Fin 4 → Fin 5 := ![0,1,2,4]
def cc : Fin 4 → Fin 5 := ![0,2,3,4]
def middle (u : Fin 4) (v : Fin 5) := full (rr u) v
def core (u v : Fin 4) := middle u (cc v)

set_option maxHeartbeats 2000000 in
private theorem orderExcept (gs : List Gate) (hm : ∀ g∈gs, Good g) (p : Nat)
    (unused : ∀ g∈gs, p∉g.inputs) (A B : List Bool) (len : A.length=B.length)
    (close : ∀ i, i≠p → A.getD i false=true → B.getD i false=true) :
    ∀ i, i≠p → (wiresFrom gs A).getD i false=true → (wiresFrom gs B).getD i false=true := by
  induction gs generalizing A B with
  | nil => exact close
  | cons g gs ih =>
    have good := hm g (by simp)
    have avoid := unused g (by simp)
    have wires : nextWire A g=true → nextWire B g=true := by
      have ops : g.op=.and ∨ g.op=.or := good.1
      rcases ops with op|op
      · simp only [nextWire,op,GateOp.eval,List.all_map,List.all_eq_true,Function.comp_apply,id_eq]
        intro h i hi
        exact close i (fun eq => avoid (eq ▸ hi)) (h i hi)
      · simp only [nextWire,op,GateOp.eval,List.any_map,List.any_eq_true,Function.comp_apply,id_eq]
        rintro ⟨i,hi,h⟩
        exact ⟨i,hi,close i (fun eq => avoid (eq ▸ hi)) h⟩
    apply ih (fun h mem => hm h (by simp [mem])) (fun h mem => unused h (by simp [mem]))
      (step A g) (step B g) (by simp [step,len])
    intro i ne
    by_cases last : i=A.length
    · subst i;unfold step;rw [lastRead,len,lastRead];exact wires
    · unfold step;rw [stable _ _ _ last,stable _ _ _ (by rw [←len];exact last)]
      exact close i ne

set_option maxHeartbeats 2000000 in
theorem indispensable (C : Circuit) (hm : Monotone2 C) (p : Nat) (A B : List Bool) (len : A.length=B.length)
    (outside : C.output≠p) (close : ∀ i,i≠p → A.getD i false=true → B.getD i false=true)
    (on : C.eval A=true) (off : C.eval B=false) : 0<C.gates.countP (touches {p}) := by
  by_contra! none
  have z := List.countP_eq_zero.mp (Nat.eq_zero_of_le_zero none)
  have unused (g) (mem : g∈C.gates) : p∉g.inputs := by
    have h := z _ mem
    simpa [touches,List.any_eq_false] using h
  have wrong := orderExcept C.gates hm p unused A B len close C.output outside on
  exact Bool.noConfusion (wrong.symm.trans off)

def renum (n cut d i : Nat) := if i<n ∧ i≠cut then (if i<cut then i else i-1) else d

set_option maxHeartbeats 2000000 in
theorem removeInput {T : Type} (n cut : Nat) (hc : cut<n) (A B : T→List Bool) (C : Circuit) (hm : Monotone2 C)
    (la : ∀ x,(A x).length=n) (lb : ∀ x,(B x).length=n-1)
    (matchReads : ∀ (x : T) (i : Fin n), i.val≠cut →
      (A x).getD i.val false=(B x).getD (if i.val<cut then i.val else i.val-1) false)
    (zero : ∀x,(A x).getD cut false=false) (count : 0<C.gates.countP (touches {cut})) :
    ∃ D : Circuit, Monotone2 D ∧ D.size+1≤C.size ∧ ∀ x,D.eval (B x)=C.eval (A x) := by
  let d := n-1+C.size
  obtain ⟨D,md,sz,correct⟩ := compress {cut} C.output d C.gates hm A B n (n-1) (renum n cut d) la lb
    (by intro p hp;simpa only [Finset.mem_singleton.mp hp] using hc) (by rfl)
    (by intro i;unfold renum;split_ifs <;> omega) (by
      intro x i
      have far : (B x).getD d false=false := List.getD_eq_default _ _ (by rw [lb];dsimp [d];omega)
      by_cases lt : i<n
      · by_cases eq : i=cut
        · subst i;rw [show renum n cut d cut=d by simp [renum],far];exact zero x
        · rw [show renum n cut d i=(if i<cut then i else i-1) by simp [renum,lt,eq]]
          exact matchReads x ⟨i,lt⟩ eq
      · rw [show renum n cut d i=d by simp [renum,lt],far]
        exact List.getD_eq_default _ _ (by rw [la];omega)) (by
      intro x i hi;obtain rfl := Finset.mem_singleton.mp hi;exact zero x)
  exact ⟨D,md,by change _=C.size at sz;omega,correct⟩

set_option maxHeartbeats 2000000 in
private theorem primary {T : List Bool} {n p : Nat} (C : Circuit) (len : T.length=n) (lt : p<n) :
    (wiresFrom C.gates T).getD p false=T.getD p false := prefix_val _ _ _ (by rw [len];exact lt)

set_option maxHeartbeats 2000000 in
private theorem finiteClose {p n : Nat} {A B : List Bool} (l : A.length=n)
    (yes : ∀ i : Fin n,i.val≠p → A.getD i.val false=true → B.getD i.val false=true) :
    ∀ i,i≠p → A.getD i false=true → B.getD i false=true := by
  intro i h on
  by_cases lt : i<n
  · exact yes ⟨i,lt⟩ h on
  · have bad := List.getD_eq_default A false (by rw [l];exact Nat.le_of_not_gt lt : A.length ≤ i)
    exact Bool.noConfusion (on.symm.trans bad)

set_option maxHeartbeats 2000000 in
theorem deleteRow {C : Circuit} (hm : Monotone2 C) (rep : Represents full C) :
    ∃ D : Circuit, Monotone2 D ∧ D.size+1≤C.size ∧ Represents middle D := by
  have out : C.output≠3 := by
    intro eq
    have z := rep 0 0
    change (wiresFrom C.gates (oneEach (0:Fin 5) (0:Fin 5))).getD C.output false=full 0 0 at z
    rw [eq,primary C (show (oneEach (0:Fin 5) (0:Fin 5)).length=10 by decide) (by decide : 3<10)] at z
    exact (by decide +kernel : (oneEach (0:Fin 5) (0:Fin 5)).getD 3 false≠full 0 0) z
  have count := indispensable C hm 3 (oneEach (3:Fin 5) (0:Fin 5)) (oneEach (1:Fin 5) (0:Fin 5))
    (by decide) out (finiteClose (n:=10) (by decide) (by decide +kernel))
    (by simpa only [(by decide : full 3 0=true)] using rep 3 0)
    (by simpa only [(by decide : full 1 0=false)] using rep 1 0)
  let A (x : Fin 4 × Fin 5) := oneEach (rr x.1) x.2
  let B (x : Fin 4 × Fin 5) := oneEach x.1 x.2
  obtain ⟨D,md,sz,correct⟩ := removeInput 10 3 (by decide) A B C hm
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) count
  exact ⟨D,md,sz,fun u v => (correct (u,v)).trans (rep (rr u) v)⟩

set_option maxHeartbeats 2000000 in
theorem deleteCol {C : Circuit} (hm : Monotone2 C) (rep : Represents middle C) :
    ∃ D : Circuit, Monotone2 D ∧ D.size+1≤C.size ∧ Represents core D := by
  have out : C.output≠5 := by
    intro eq
    have z := rep 0 0
    change (wiresFrom C.gates (oneEach (0:Fin 4) (0:Fin 5))).getD C.output false=middle 0 0 at z
    rw [eq,primary C (show (oneEach (0:Fin 4) (0:Fin 5)).length=9 by decide) (by decide : 5<9)] at z
    exact (by decide +kernel : (oneEach (0:Fin 4) (0:Fin 5)).getD 5 false≠middle 0 0) z
  have count := indispensable C hm 5 (oneEach (0:Fin 4) (1:Fin 5)) (oneEach (0:Fin 4) (2:Fin 5))
    (by decide) out (finiteClose (n:=9) (by decide) (by decide +kernel))
    (by simpa only [(by decide : middle 0 1=true)] using rep 0 1)
    (by simpa only [(by decide : middle 0 2=false)] using rep 0 2)
  let A (x : Fin 4 × Fin 4) := oneEach x.1 (cc x.2)
  let B (x : Fin 4 × Fin 4) := oneEach x.1 x.2
  obtain ⟨D,md,sz,correct⟩ := removeInput 9 5 (by decide) A B C hm
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) count
  exact ⟨D,md,sz,fun u v => (correct (u,v)).trans (rep u (cc v))⟩

set_option maxHeartbeats 2000000 in
theorem coreReduction : RepSizeAtMost full 10 → RepSizeAtMost core 8 := by
  rintro ⟨C,hm,sz,rep⟩
  obtain ⟨D,md,one,step⟩ := deleteRow hm rep
  obtain ⟨E,me,two,done⟩ := deleteCol md step
  exact ⟨E,me,by omega,done⟩

end PEqualNP.Outside.L_meta_10149.Eliminate

namespace PEqualNP.Outside.L_meta_10149.Perm
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
def stepB (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def permWire (σ : Fin 8 → Fin 8) (i : ℕ) : ℕ :=
  if h : i < 8 then (σ ⟨i, h⟩).val else i

def permGate (σ : Fin 8 → Fin 8) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (permWire σ)⟩

def permCircuit (σ : Fin 8 → Fin 8) (C : Circuit) : Circuit :=
  { gates := C.gates.map (permGate σ), output := permWire σ C.output }

theorem permCircuit_size (σ : Fin 8 → Fin 8) (C : Circuit) :
    (permCircuit σ C).size = C.size := by
  simp [permCircuit, Circuit.size]

theorem permCircuit_mono (σ : Fin 8 → Fin 8) (C : Circuit) (hm : Monotone2 C) :
    Monotone2 (permCircuit σ C) := by
  intro g hg
  simp only [permCircuit, List.mem_map] at hg
  obtain ⟨g0, hg0, rfl⟩ := hg
  simpa [permGate] using hm g0 hg0

theorem stepB_perm (σ : Fin 8 → Fin 8) (g : Gate) (w1 w2 : List Bool)
    (hlen : w1.length = w2.length) (h8 : 8 ≤ w1.length)
    (hinv : ∀ i, w2.getD (permWire σ i) false = w1.getD i false) :
    (stepB w1 g).length = (stepB w2 (permGate σ g)).length ∧
    8 ≤ (stepB w1 g).length ∧
    ∀ i, (stepB w2 (permGate σ g)).getD (permWire σ i) false = (stepB w1 g).getD i false := by
  have hval : (permGate σ g).op.eval ((permGate σ g).inputs.map fun j => w2.getD j false) =
      g.op.eval (g.inputs.map fun i => w1.getD i false) := by
    simp only [permGate, List.map_map]
    congr 1
    apply List.map_congr_left
    intro i _
    exact hinv i
  refine ⟨by simp [stepB, hlen], by simp [stepB]; omega, fun i => ?_⟩
  by_cases hi8 : i < 8
  · have hpi : permWire σ i < 8 := by
      simp only [permWire, hi8, ↓reduceDIte]
      exact (σ ⟨i, hi8⟩).isLt
    have hlt1 : i < w1.length := by omega
    have hlt2 : permWire σ i < w2.length := by omega
    simp only [stepB, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt1,
      List.getElem?_append_left hlt2]
    exact hinv i
  · have hpi : permWire σ i = i := by simp [permWire, hi8]
    rw [hpi]
    by_cases hlt : i < w1.length
    · have hlt2 : i < w2.length := hlen ▸ hlt
      simp only [stepB, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt,
        List.getElem?_append_left hlt2]
      have h0 := hinv i
      rw [hpi] at h0
      exact h0
    · by_cases heq : i = w1.length
      · subst heq
        have h1 : (stepB w1 g).getD w1.length false =
            g.op.eval (g.inputs.map fun j => w1.getD j false) := by
          simp [stepB, List.getD_eq_getElem?_getD]
        have h2 : (stepB w2 (permGate σ g)).getD w1.length false =
            (permGate σ g).op.eval ((permGate σ g).inputs.map fun j => w2.getD j false) := by
          rw [hlen]
          simp [stepB, List.getD_eq_getElem?_getD]
        rw [h1, h2, hval]
      · have hge1 : (stepB w1 g).length ≤ i := by simp [stepB]; omega
        have hge2 : (stepB w2 (permGate σ g)).length ≤ i := by simp [stepB]; omega
        rw [List.getD_eq_default _ _ hge1, List.getD_eq_default _ _ hge2]

theorem foldl_stepB_perm (σ : Fin 8 → Fin 8) (gs : List Gate) :
    ∀ w1 w2 : List Bool, w1.length = w2.length → 8 ≤ w1.length →
      (∀ i, w2.getD (permWire σ i) false = w1.getD i false) →
      ∀ i, ((gs.map (permGate σ)).foldl stepB w2).getD (permWire σ i) false =
        (gs.foldl stepB w1).getD i false := by
  induction gs with
  | nil => intro w1 w2 _ _ hinv i; exact hinv i
  | cons g gs ih =>
    intro w1 w2 hlen h8 hinv i
    obtain ⟨hlen', h8', hinv'⟩ := stepB_perm σ g w1 w2 hlen h8 hinv
    exact ih (stepB w1 g) (stepB w2 (permGate σ g)) hlen' h8' hinv' i

theorem permCircuit_eval (σ : Fin 8 → Fin 8) (C : Circuit) (y : Fin 8 → Bool) :
    circuitFun 8 (permCircuit σ C) y = circuitFun 8 C (fun i => y (σ i)) := by
  apply foldl_stepB_perm σ C.gates (List.ofFn (fun i => y (σ i))) (List.ofFn y)
    (by simp) (by simp)
  intro i
  by_cases hi : i < 8
  · have hlt : (σ ⟨i, hi⟩).val < 8 := (σ ⟨i, hi⟩).isLt
    simp only [permWire, hi, ↓reduceDIte, List.getD_eq_getElem?_getD, List.getElem?_ofFn, hlt,
      Option.getD_some, Fin.eta]
  · simp only [permWire, hi, ↓reduceDIte]
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

def perm : Fin 8 → Fin 8 := ![0,3,1,2,5,4,6,7]
def pp : Fin 4 → Fin 4 := ![0,2,3,1]
def ww : Fin 4 → Fin 4 := ![1,0,2,3]
def assignment (a b : Fin 4) (k : Fin 8) := decide (k.val=a.val ∨ k.val=4+b.val)
theorem inputs : ∀ a b : Fin 4, List.ofFn (assignment a b) = oneEach a b := by decide +kernel
theorem changed : ∀ a b : Fin 4, List.ofFn (fun k => assignment a b (perm k)) = oneEach (pp a) (ww b) := by decide +kernel
def core (u v : Fin 4) := (13613 : Nat).testBit (4*u.val+v.val)
def canon (u v : Fin 4) := (4974 : Nat).testBit (4*u.val+v.val)
theorem same : ∀ a b, core (pp a) (ww b) = canon a b := by decide +kernel
theorem forwards (s : Nat) : RepSizeAtMost core s → RepSizeAtMost canon s := by
  rintro ⟨C,hc,sz,ok⟩
  refine ⟨permCircuit perm C,permCircuit_mono perm C hc,(permCircuit_size perm C) ▸ sz,?_⟩
  intro a b
  have eq := permCircuit_eval perm C (assignment a b)
  unfold circuitFun at eq
  rw [inputs,changed] at eq
  exact eq.trans ((ok (pp a) (ww b)).trans (same a b))
end PEqualNP.Outside.L_meta_10149.Perm

theorem PEqualNP.Outside.L_meta_10149 : ¬ (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (7711899 : ℕ).testBit (5 * u.val + v.val)) 10) := by
  intro h
  have hh := PEqualNP.Outside.L_meta_10149.Eliminate.coreReduction h
  have eq : PEqualNP.Outside.L_meta_10149.Eliminate.core = PEqualNP.Outside.L_meta_10149.Perm.core := by
    funext u v
    exact (by decide +kernel : ∀ p q, PEqualNP.Outside.L_meta_10149.Eliminate.core p q = PEqualNP.Outside.L_meta_10149.Perm.core p q) u v
  rw [eq] at hh
  exact PEqualNP.Outside.L_meta_10149.Four.lower (PEqualNP.Outside.L_meta_10149.Perm.forwards 8 hh)
