import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_14784

-- The signed circuit search uses the live-wire compression from L-meta-1423.
-- A NOT gate costs one gate in the given circuit and zero in the signed search.
-- The live-wire compression argument follows the project proof of L-meta-703.
-- The live-wire reduction and circuit semantics follow the merged L-meta-1429.
-- Each finite search layer below is checked against the next layer of smaller states.
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

-- The upper and lower halves represent opposite target labels on 162 pairs of assignments.
abbrev W := BitVec 324
-- Free complementation leaves four binary choices up to output polarity.
def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 162 := ((x >>> 162) ^^^ x).setWidth 162
def cuts (ws : List W) : BitVec 162 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 162) ++ (0 : BitVec 162)
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

abbrev basicOps (a b : W) : Finset W := (ops a b).toFinset

def differs (i : Fin 162) (w : W) : Prop :=
  w.getLsbD (162+i.val) ≠ w.getLsbD i.val

theorem ops_differs (i : Fin 162) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 162+i.val < 324 := by omega
  have hi' : i.val < 324 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

theorem cuts_spec (ws : List W) (i : Fin 162) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have bx (p q : Bool) : Bool.xor p q = true ↔ p ≠ q := by cases p <;> cases q <;> decide
    simp [sep, i.isLt, differs, Nat.add_comm, bx]

theorem cuts_full {g : W} (hg : g = goal ∨ g = ~~~goal) {k : ℕ} {ws : List W}
    (h : live basicOps g k ws.toFinset) : cuts ws = -1 := by
  have hd : ∀ i, differs i g := by rcases hg with rfl | rfl <;> unfold differs <;> decide +kernel
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (hd ⟨j,hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 162)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto

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

theorem singleton_list {goal : W} {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

def insertW (v : W) : List W → List W
  | [] => [v]
  | x :: xs => if v ≤ x then v :: x :: xs else x :: insertW v xs

def ordered (ws : List W) := ws.foldr insertW []

theorem insertW_perm (v : W) (ws : List W) : (insertW v ws).Perm (v :: ws) := by
  induction ws with
  | nil => exact .refl _
  | cons x xs ih =>
    simp only [insertW]
    split
    · exact .refl _
    · exact (ih.cons x).trans (.swap _ _ _)

theorem ordered_perm (ws : List W) : (ordered ws).Perm ws := by
  induction ws with
  | nil => exact .refl _
  | cons x xs ih => exact (insertW_perm x (ordered xs)).trans (ih.cons x)

def children (k : ℕ) (ws : List W) : List (List W) := (pairs ws).flatMap fun (a,b,r) =>
  (ops a b).flatMap fun z =>
    (keepChoices a b r).filterMap fun kept =>
      if kept.length ≤ k ∧ cuts (z :: kept) = -1 then some (ordered (z :: kept)) else none

def earlier : List W → List W → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: l, b :: r => if a = b then earlier l r else decide (a.toNat < b.toNat)

def containsKey (q : List W) : BinaryTree (List W) → Bool
  | .nil => false
  | .node a l r => if q = a then true else if earlier q a then containsKey q l else containsKey q r

def everyKey (f : List W → Bool) : BinaryTree (List W) → Bool
  | .nil => true
  | .node a l r => f a && everyKey f l && everyKey f r

theorem every_at {f : List W → Bool} {q : List W} (tr : BinaryTree (List W))
    (ha : everyKey f tr = true) (hm : containsKey q tr = true) : f q = true := by
  induction tr with
  | nil => contradiction
  | node a l r il ir =>
    simp only [everyKey,Bool.and_eq_true] at ha
    simp only [containsKey] at hm
    split at hm
    next e => simpa [e] using ha.1.1
    next e =>
      split at hm
      · exact il ha.1.2 hm
      · exact ir ha.2 hm

def Closed (k : Nat) (tr : BinaryTree (List W)) : Prop :=
  ∀ (g : W), g = goal ∨ g = ~~~goal → ∀ ws : List W,
    ws.Nodup → ws.length ≤ 10 → containsKey ws tr = true → ¬ live basicOps g k ws.toFinset

def doneTest (s : List W) : Bool := s == [goal] || s == [~~~goal]

theorem closed_nil (tr : BinaryTree (List W)) (hc : everyKey (fun q => !doneTest q) tr = true) :
    Closed 0 tr := by
  intro g hg ws hn hl hm h
  have hy := every_at tr hc hm
  have eq := singleton_list hn h
  rcases hg with rfl | rfl <;> simp [eq,doneTest] at hy

def rowOK (k : Nat) (tr : BinaryTree (List W)) (ws : List W) :=
  !doneTest ws && (children k ws).all (fun child => containsKey child tr)

theorem perm_set {u v : List W} (p : u.Perm v) : u.toFinset = v.toFinset := by
  ext a
  simpa only [List.mem_toFinset] using (p.mem_iff : a ∈ u ↔ a ∈ v)

theorem closed_next (k : Nat) (hk : k < 10) (tr next : BinaryTree (List W))
    (hnext : Closed k next) (hc : everyKey (rowOK k next) tr = true) :
    Closed (k+1) tr := by
  intro g hg ws hn hl hm h
  have hy := every_at tr hc hm
  simp only [rowOK,Bool.and_eq_true,List.all_eq_true] at hy
  rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
  · have eq := singleton_list hn done
    rcases hg with rfl | rfl <;> simp [eq,doneTest] at hy
  · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
    have go {a b : W} (hp : ws.Perm (a :: b :: r)) (hmem : (a,b,r) ∈ pairs ws)
        (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) : False := by
      obtain ⟨kept, hkeep, hnk, hfin⟩ := recover_kept hp hn hset
      have hznew : z ∉ kept := by
        intro hu
        apply hout
        rw [hset]
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
      have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
      have hraw : live basicOps g k (z :: kept).toFinset := by simpa [hfin] using tail
      have hc := live_card hraw
      rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
      have hp' := ordered_perm (z :: kept)
      have mem : ordered (z :: kept) ∈ children k ws := by
        apply List.mem_flatMap.mpr
        refine ⟨(a,b,r),hmem,List.mem_flatMap.mpr ⟨z,List.mem_toFinset.mp hop,?_⟩⟩
        exact List.mem_filterMap.mpr ⟨kept,hkeep,by simp [show kept.length ≤ k by omega,cuts_full hg hraw]⟩
      have sz : (ordered (z :: kept)).length ≤ 10 := by rw [hp'.length_eq]; simp only [List.length_cons]; omega
      apply hnext g hg _ (hp'.nodup_iff.mpr hnd) sz (hy.2 _ mem)
      rwa [perm_set hp']
    rcases hm with direct | swap
    · exact go hp direct hs hz
    · exact go (hp.trans (.swap _ _ _)) swap (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)

def startOK (n : Nat) (tr : BinaryTree (List W)) (ws : List W) : Bool :=
  !(decide (ws.length ≤ n+1) && (cuts ws == -1)) || containsKey (ordered ws) tr

theorem no_build (n : Nat) (tr : BinaryTree (List W)) (ins : List W) (nd : ins.Nodup)
    (small : ins.length ≤ 10) (hc : Closed n tr) (hi : ins.sublists.all (startOK n tr) = true)
    (g : W) (hg : g = goal ∨ g = ~~~goal) : ¬ build basicOps g n ins.toFinset := by
  intro hb
  classical
  obtain ⟨s,hs,hl⟩ := compress hb
  let ws := ins.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws,List.mem_toFinset,List.mem_filter,decide_eq_true_eq,and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hnd := nd.filter (fun u => decide (u ∈ s))
  have hl' : live basicOps g n ws.toFinset := eq.symm ▸ hl
  have size := live_card hl'
  rw [List.toFinset_card_of_nodup (show ws.Nodup from hnd)] at size
  have sub : ws.Sublist ins := List.filter_sublist ..
  have key := List.all_eq_true.mp hi ws (List.mem_sublists.mpr sub)
  have perm := ordered_perm ws
  apply hc g hg (ordered ws) (perm.nodup_iff.mpr hnd) (by rw [perm.length_eq]; exact sub.length_le.trans small) ?_
  · rwa [perm_set perm]
  · simpa [startOK,size,cuts_full hg hl'] using key

open PEqualNP.CircuitLowerBounds

def holds (av : Finset W) (z : W) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

theorem holds_insert {av : Finset W} {z a : W} (h : holds av z) : holds (insert a av) z := by
  rcases h with h|h|⟨u,hu,he⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨u,Finset.mem_insert_of_mem hu,he⟩)

theorem holds_not {av : Finset W} {z : W} (h : holds av z) : holds av (~~~z) := by
  rcases h with rfl|rfl|⟨a,ha,he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he|he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable (av : Finset W) (z : W) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps a b, holds (insert w av) z

theorem reachable_not {av : Finset W} {z : W} (h : reachable av z) : reachable av (~~~z) := by
  rcases h with h|⟨a,ha,b,hb,ne,w,hop,hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a,ha,b,hb,ne,w,hop,holds_not hw⟩

set_option maxRecDepth 5000 in
theorem and_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x &&& y) := by
  have const : holds av (0 : W) := .inl rfl
  have oldx := hx
  rcases hx with rfl|rfl|⟨a,ha,ea⟩
  · rw [show (0 : W) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · change reachable av (BitVec.allOnes 324 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 324)
    rw [BitVec.and_allOnes]; exact .inl oldx
  by_cases h : a = b
  · subst b
    rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb] <;>
      simp only [BitVec.and_self, BitVec.and_not_self, BitVec.not_and_self] <;>
      first | exact .inl const | exact .inl (.inr (.inr ⟨a,ha,.inl rfl⟩)) |
        exact .inl (.inr (.inr ⟨a,ha,.inr rfl⟩))
  have add (w : W) (hw : w ∈ basicOps a b) (z : W) (hz : z = w ∨ z = ~~~w) :
      reachable av z :=
    .inr ⟨a,ha,b,hb,h,w,hw,.inr (.inr ⟨w,Finset.mem_insert_self ..,hz⟩)⟩
  rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb]
  · exact add _ (by simp [basicOps,ops] : a &&& b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : a &&& ~~~b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : b &&& ~~~a ∈ basicOps a b) _ (.inl (BitVec.and_comm ..))
  · exact add _ (by simp [basicOps,ops] : a ||| b ∈ basicOps a b) _ (.inr BitVec.not_or.symm)

theorem or_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))

private def bit (k : Fin 324) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 324) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

def legal (g : Gate) : Prop := (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def action (w : List W) (g : Gate) : W := match g.op with
  | .not => ~~~(g.inputs.head?.map (fun i => w.getD i 0)).getD 0
  | .and => (g.inputs.map fun i => w.getD i 0).foldr (· &&& ·) (~~~0)
  | .or => (g.inputs.map fun i => w.getD i 0).foldr (· ||| ·) 0
  | _ => 0

theorem evalAnd (xs : List Bool) : GateOp.and.eval xs = xs.all id := rfl
theorem evalOr (xs : List Bool) : GateOp.or.eval xs = xs.any id := rfl
theorem evalNot (xs : List Bool) : GateOp.not.eval xs = !(xs.headD false) := rfl

set_option maxRecDepth 5000 in
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 324) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> try simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#324)[k.val] = false; simp
  all_goals rcases hop with rfl|rfl|rfl <;>
    simp only [step, List.map_cons,List.map_nil,read_bit,List.map_append] <;>
    simp only [action, evalAnd, evalOr, evalNot, List.foldr_cons,List.foldr_nil,List.head?_cons,List.head?_nil,
      List.headD_cons,List.headD_nil,Option.map_some,Option.map_none,Option.getD_some,Option.getD_none,
      List.all_cons,List.all_nil,List.any_cons,List.any_nil,List.map_cons,List.map_nil,id_eq,
      Bool.and_true,Bool.or_false, bit,BitVec.getElem_and,BitVec.getElem_or,BitVec.getElem_not,
      BitVec.getElem_zero,bit0,Bool.not_false] <;> rfl

def isBinary (g : Gate) : Bool := match g.op with
  | .not => false
  | _ => true
def binaryCost (gs : List Gate) := (gs.filter isBinary).length

theorem available_read {av : Finset W} {w : List W} (hw : ∀ u ∈ w, holds av u) (i : ℕ) :
    holds av (w.getD i 0) := by
  by_cases h : i < w.length
  · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    exact .inl rfl

set_option maxRecDepth 5000 in
theorem gate_reach (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (g : Gate) (hg : legal g) :
    if isBinary g then reachable av (action w g) else holds av (action w g) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> try simp at cap
  all_goals rcases hop with rfl|rfl|rfl <;> simp only [isBinary,Bool.false_eq_true,ite_false,ite_true,
    action,List.head?_nil,List.head?_cons,List.map_nil,List.map_cons,List.foldr_nil,List.foldr_cons,
    Option.map_none,Option.map_some,Option.getD_none,Option.getD_some,
    show ∀ x : W, x ||| (0 : W) = x from fun x => BitVec.or_zero,
    show ∀ x : W, x &&& ~~~0 = x from fun x => BitVec.and_allOnes]
  all_goals first
    | exact .inl (.inl rfl)
    | exact .inl (.inr (.inl rfl))
    | exact .inr (.inl rfl)
    | exact .inl (available_read hw _)
    | exact holds_not (available_read hw _)
    | exact and_reach (available_read hw _) (available_read hw _)
    | exact or_reach (available_read hw _) (available_read hw _)

set_option maxRecDepth 4000 in
theorem compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k goal) :
    ∃ t, (t = goal ∨ t = ~~~goal) ∧ build basicOps t (binaryCost gs) av := by
  induction gs generalizing w av with
  | nil =>
    have hv : w.getD out 0 = goal := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i,hi⟩
    have h := hv ▸ available_read hw out
    rcases h with zero|ones|⟨t,ht,eq|eq⟩
    · exact False.elim ((by decide : goal ≠ 0) zero)
    · exact False.elim ((by decide : goal ≠ ~~~0) ones)
    · exact ⟨t, .inl eq.symm, ht⟩
    · exact ⟨t, .inr (by rw [eq, BitVec.not_not]), ht⟩
  | cons g gs ih =>
    let z := action w g
    have stepOK := action_spec w g (hg g (by simp))
    have nextEval : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k goal := by
      intro k; simpa only [List.foldl_cons, stepOK] using he k
    have tail := ih (fun t ht => hg t (by simp [ht])) (w ++ [z])
    have cont (A : Finset W) (hold : ∀ u ∈ w, holds A u) (new : holds A z) :=
      tail A (by
        intro u hu
        rcases List.mem_append.mp hu with hu|hu
        · exact hold u hu
        · exact (List.mem_singleton.mp hu) ▸ new) nextEval
    have stepClass := gate_reach w av hw g (hg g (by simp))
    cases neg : isBinary g
    · simp only [neg,Bool.false_eq_true,ite_false] at stepClass
      simpa [binaryCost,neg] using cont av hw stepClass
    · simp only [neg,ite_true] at stepClass
      have len : binaryCost (g::gs) = binaryCost gs+1 := by simp [binaryCost,neg]
      rw [len]
      rcases stepClass with existing|⟨a,ha,b,hb,ne,new,op,rep⟩
      · obtain ⟨t,ht,run⟩ := cont av hw existing
        exact ⟨t,ht,Or.inl run⟩
      · obtain ⟨t,ht,run⟩ := cont (insert new av) (fun u hu => holds_insert (hw u hu)) rep
        exact ⟨t,ht,Or.inr ⟨a,ha,b,hb,ne,new,op,run⟩⟩
theorem bound_from_search (T n : ℕ) (ins : List W) (nd : ins.Nodup)
    (row : ∀ j : Fin 324, Nat.testBit T (∑ i : Fin 8, if (ins.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val])
    (width : ins.length = 8) (rejection : ∀ z, z = goal ∨ z = ~~~goal → ¬ build basicOps z n ins.toFinset)
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) =
      Nat.testBit T (∑ i : Fin 8, if x i then 2^(i : ℕ) else 0)) : n < binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ ins, holds ins.toFinset u := fun u hu =>
    .inr (.inr ⟨u,List.mem_toFinset.mpr hu,.inl rfl⟩)
  have evaluate (k : Fin 324) :
      (gs.foldl step (ins.map (bit k))).getD o false = bit k goal := by
    let x (i : Fin 8) : Bool := bit k (ins.getD i.val 0)
    have same : List.ofFn x = ins.map (bit k) := by
      apply List.ext_getElem
      · simp [width]
      · intro i hi hj
        have hlt : i < ins.length := by simpa using hj
        simp only [List.getElem_ofFn, List.getElem_map, x, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs,o⟩ (ins.map (bit k)) = bit k goal
    rw [← same, he]
    exact row k
  obtain ⟨t,ht,run⟩ := compile gs o hg ins ins.toFinset init evaluate
  have lift {a b : ℕ} (h : a ≤ b) (hr : build basicOps t a ins.toFinset) : build basicOps t b ins.toFinset := by
    induction h with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  exact rejection t ht (lift low run)

theorem replace (T m : ℕ) (ins : List W) (nd : ins.Nodup)
    (row : ∀ j : Fin 324, Nat.testBit T (∑ i : Fin 8, if (ins.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val])
    (width : ins.length = 8) (rejection : ∀ z, z = goal ∨ z = ~~~goal → ¬ build basicOps z (m-2) ins.toFinset)
    (upper : ∃ (gs : List Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
      ∧ gs.length = m ∧ ∀ x : Fin 8 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) =
        Nat.testBit T (∑ i : Fin 8, if x i then 2^(i : ℕ) else 0))
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) =
      Nat.testBit T (∑ i : Fin 8, if x i then 2^(i : ℕ) else 0)) :
    ∃ (ds : List Gate) (p : ℕ), (∀ g ∈ ds, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
      ∧ ds.length ≤ gs.length ∧ ∀ x : Fin 8 → Bool, Circuit.eval ⟨ds,p⟩ (List.ofFn x) =
        Nat.testBit T (∑ i : Fin 8, if x i then 2^(i : ℕ) else 0) := by
  by_cases present : ∃ g ∈ gs, g.op = .not
  · obtain ⟨g,hm,hn⟩ := present
    have cut : binaryCost gs < gs.length := (List.length_filter_lt_length_iff_exists (p := isBinary)).mpr ⟨g,hm,by simp [isBinary, hn]⟩
    have b := bound_from_search T (m-2) ins nd row width rejection gs o hg he
    obtain ⟨ds,p,ok,size,ev⟩ := upper
    exact ⟨ds,p,ok,by omega,ev⟩
  · refine ⟨gs,o,?_,le_rfl,he⟩
    intro g hm
    obtain ⟨hop,cap⟩ := hg g hm
    exact ⟨hop.elim Or.inl (fun h => h.elim Or.inr (fun eq => (present ⟨g,hm,eq⟩).elim)),cap⟩

def signal0 : W := (0x0 : BitVec 162) ++ (0x0 : BitVec 162)
def signal1 : W := (0x202040840010010010 : BitVec 162) ++ (0x0 : BitVec 162)
def signal2 : W := (0x204000222400040810400000 : BitVec 162) ++ (0x0 : BitVec 162)
def signal3 : W := (0x401101e1e0003f80fe000000 : BitVec 162) ++ (0x1e1e0003f80fe000000 : BitVec 162)
def signal4 : W := (0x500000224040000000000000000000 : BitVec 162) ++ (0x0 : BitVec 162)
def signal5 : W := (0x500300224040222448c40810410411 : BitVec 162) ++ (0x0 : BitVec 162)
def signal6 : W := (0x5e03e022f070222448dc3870c71c71 : BitVec 162) ++ (0x3e01e001f0f00000003c78f1cf1cf1 : BitVec 162)
def signal7 : W := (0x822000441112404081088022022022 : BitVec 162) ++ (0x0 : BitVec 162)
def signal8 : W := (0x822424441112e0e1c39d8076076076 : BitVec 162) ++ (0x1e1e3c7bf80fe0fe0fe : BitVec 162)
def signal9 : W := (0x1044848882224ee01f81dbb00077f00 : BitVec 162) ++ (0x1fe03f83fff000fff00 : BitVec 162)
def signal10 : W := (0x2088003e1ff00444000089122000000 : BitVec 162) ++ (0x3e1ff00000000000000000000 : BitVec 162)
def signal11 : W := (0x2089091e0f700eeec001dbb76d00000 : BitVec 162) ++ (0x3e1ff01fffc003ffffff00000 : BitVec 162)
def signal12 : W := (0x3d01f01ee4040eeedfbc40810410411 : BitVec 162) ++ (0x7c01e03fe0001ffffffc00000000000 : BitVec 162)
def signal13 : W := (0x3dee001eef776444091089122022922 : BitVec 162) ++ (0x7ffe003fffffe000000000000000000 : BitVec 162)
def signal14 : W := (0x3defffd008400888922112244945244 : BitVec 162) ++ (0x7fffffc000000000000000000000000 : BitVec 162)
def signal15 : W := (0x810000000000000000220048040800010400 : BitVec 162) ++ (0x0 : BitVec 162)
def signal16 : W := (0x890100000000224040222448c40810410411 : BitVec 162) ++ (0x0 : BitVec 162)
def signal17 : W := (0x8bc3c00000002370f0222448ec58b14b0cb1 : BitVec 162) ++ (0x7c3c000000001f0f00000003c78f1cf1cf1 : BitVec 162)
def signal18 : W := (0x1004400000000000001e003c03f80000fe000 : BitVec 162) ++ (0x1e003c03f80000fe000 : BitVec 162)
def signal19 : W := (0x11044480000004411136162c5ae80ba0ba0ba : BitVec 162) ++ (0x1e1e3c7bf80fe0fe0fe : BitVec 162)
def signal20 : W := (0x2008800000000802201fe00003fff00000000 : BitVec 162) ++ (0x1fe00003fff00000000 : BitVec 162)
def signal21 : W := (0x2208890000002e17b017774002eddbb600000 : BitVec 162) ++ (0x3e1ff01fffc003ffffff00000 : BitVec 162)
def signal22 : W := (0x4021001044000882224440090089100022900 : BitVec 162) ++ (0x0 : BitVec 162)
def signal23 : W := (0x4421220000002ff7bfe444091089122022922 : BitVec 162) ++ (0x3fffffe000000000000000000 : BitVec 162)
def signal24 : W := (0x783dc000000008822257602d82edd000bad00 : BitVec 162) ++ (0xf87fc00000000000001fe03f83fff000fff00 : BitVec 162)
def signal25 : W := (0x7f90100000002fe40417776ddc40810410411 : BitVec 162) ++ (0xff80000000003fe0001ffffffc00000000000 : BitVec 162)
def signal26 : W := (0x7fbdff8000002110889111204224489288088 : BitVec 162) ++ (0xffffff8000000000000000000000000000000 : BitVec 162)
def signal27 : W := (0x7fbdffbdeffff118c89999b263366cdbcd2cc : BitVec 162) ++ (0xffffffffffffc000000000000000000000000 : BitVec 162)
def signal28 : W := (0x100004040020020001010202040bc00f00f00f0 : BitVec 162) ++ (0x3c00f00f00f0 : BitVec 162)
def signal29 : W := (0x1100044480220240011120000003b80ee0ee0ee : BitVec 162) ++ (0x3f80fe0fe0fe : BitVec 162)
def signal30 : W := (0x20087c0000400400020202200483c78000f1c00 : BitVec 162) ++ (0x7c0000000000000000000003c78000f1c00 : BitVec 162)
def signal31 : W := (0x22006fc000440480022240000003bf7000efb00 : BitVec 162) ++ (0x7fc000000000000000000003fff000fff00 : BitVec 162)
def signal32 : W := (0x40000808008008021f0002224003c78f1c00000 : BitVec 162) ++ (0x1f0000000003c78f1c00000 : BitVec 162)
def signal33 : W := (0x44000889008809001bf000000003bf7efb00000 : BitVec 162) ++ (0x1ff000000003ffffff00000 : BitVec 162)
def signal34 : W := (0x10000202007e000023f0f0000000081020020820 : BitVec 162) ++ (0x3e000001f0f0000000000000000000 : BitVec 162)
def signal35 : W := (0x10800212202fe00001bfbe000000089122022922 : BitVec 162) ++ (0x3fe00001fffe000000000000000000 : BitVec 162)
def signal36 : W := (0x170006c2c02e00e001b0b00000003870e18e18e0 : BitVec 162) ++ (0x1f0007c3c03e01e001f0f00000003c78f1cf1cf1 : BitVec 162)
def signal37 : W := (0x171006c6c82e20e401b1b20000003bf0ef8ef8ee : BitVec 162) ++ (0x1f0007c3c03e01e001f0f00000003ff8ffcffcff : BitVec 162)
def signal38 : W := (0x172006fec02e40e801b2b40000003bf7e18efbe0 : BitVec 162) ++ (0x1f0007ffc03e01e001f0f00000003ffff1cffff1 : BitVec 162)
def signal39 : W := (0x174006cad02e80f001bfb00000003bf7efbe18e0 : BitVec 162) ++ (0x1f0007c3c03e01e001fff00000003fffffff1cf1 : BitVec 162)
def signal40 : W := (0x178006d2e02fe0e001bfbe00000038f1e38e39e2 : BitVec 162) ++ (0x1f0007c3c03fe1e001fffe0000003c78f1cf1cf1 : BitVec 162)
def signal41 : W := (0x17f00420002fe0fc008400000000112244945244 : BitVec 162) ++ (0x1ff00000003fe1fc000000000000000000000000 : BitVec 162)
def signal42 : W := (0x17f006e2c02fe0fc01b4b00000003972e59e5ae4 : BitVec 162) ++ (0x1ff007c3c03fe1fc01f0f00000003c78f1cf1cf1 : BitVec 162)
def signal43 : W := (0x17f006fef8210000010888000000224489288088 : BitVec 162) ++ (0x1ff007fff8000000000000000000000000000000 : BitVec 162)
def signal44 : W := (0x17f006fef82f00e001b8b80000003a74e9ae98e8 : BitVec 162) ++ (0x1ff007fff83e01e001f0f00000003c78f1cf1cf1 : BitVec 162)
def signal45 : W := (0x17f006fefbf11f01ef48c8eeedfbe64c99698499 : BitVec 162) ++ (0x1ff007ffffc01e03fe0001ffffffc00000000000 : BitVec 162)
def signal46 : W := (0x17f7fd21002fe0fefec4417776ddd52a54d55655 : BitVec 162) ++ (0x1ffff800003fe1fffe0001ffffffc00000000000 : BitVec 162)
def signal47 : W := (0x2800000000500300000000000000000000000000 : BitVec 162) ++ (0x0 : BitVec 162)
def signal48 : W := (0x2800080100500300224040002400c00010400011 : BitVec 162) ++ (0x0 : BitVec 162)
def signal49 : W := (0x2800890100000000000000000000000000000000 : BitVec 162) ++ (0x0 : BitVec 162)
def signal50 : W := (0x2800890100000300000000222448c40810410411 : BitVec 162) ++ (0x0 : BitVec 162)
def signal51 : W := (0x2800890100500300020040000048c00000010411 : BitVec 162) ++ (0x0 : BitVec 162)
def signal52 : W := (0x2800890100500300224040020408400800400401 : BitVec 162) ++ (0x0 : BitVec 162)
def signal53 : W := (0x2800890100500300224040222448c40810410411 : BitVec 162) ++ (0x0 : BitVec 162)
def signal54 : W := (0x2800890100520300225050222448cc0830430431 : BitVec 162) ++ (0x0 : BitVec 162)
def signal55 : W := (0x28008901005e03e022f070222448dc3870c71c71 : BitVec 162) ++ (0x3e01e001f0f00000003c78f1cf1cf1 : BitVec 162)
def signal56 : W := (0x2800890100d003006640406264c9c40810410411 : BitVec 162) ++ (0x0 : BitVec 162)
def signal57 : W := (0x2800890100d223006651526264c9cc8832432433 : BitVec 162) ++ (0x0 : BitVec 162)
def signal58 : W := (0x2800890103d01f01ee4040eeedfbc40810410411 : BitVec 162) ++ (0x7c01e03fe0001ffffffc00000000000 : BitVec 162)
def signal59 : W := (0x28008b0100540300226060222448cc1810430c11 : BitVec 162) ++ (0x0 : BitVec 162)
def signal60 : W := (0x28008bc3c05003002370f0222448ec58b14b0cb1 : BitVec 162) ++ (0x7c3c000000001f0f00000003c78f1cf1cf1 : BitVec 162)
def signal61 : W := (0x2804890101500300aa40406624d8c40810410411 : BitVec 162) ++ (0x0 : BitVec 162)
def signal62 : W := (0x28048b1101544300aa62646624d8cc9910432d11 : BitVec 162) ++ (0x0 : BitVec 162)
def signal63 : W := (0x2807f90100500302fe40417776ddc40810410411 : BitVec 162) ++ (0xff80000000003fe0001ffffffc00000000000 : BitVec 162)
def signal64 : W := (0x2900890100520320224040222448d40850450451 : BitVec 162) ++ (0x0 : BitVec 162)
def signal65 : W := (0x2900894140500300224040222448e40890490491 : BitVec 162) ++ (0x0 : BitVec 162)
def signal66 : W := (0x2900894140520320225050222448fc08f04f04f1 : BitVec 162) ++ (0x3c00f00f00f0 : BitVec 162)
def signal67 : W := (0x2a008d0100540340224040222448d42810451411 : BitVec 162) ++ (0x0 : BitVec 162)
def signal68 : W := (0x2a008fc100540340226060222448fc78104f1c11 : BitVec 162) ++ (0x7c0000000000000000000003c78000f1c00 : BitVec 162)
def signal69 : W := (0x2c0089010058038022c040222448d42850c10411 : BitVec 162) ++ (0x0 : BitVec 162)
def signal70 : W := (0x2c00898180500300234040222448e44891410411 : BitVec 162) ++ (0x0 : BitVec 162)
def signal71 : W := (0x2c0089818058038023f040222448fc78f1c10411 : BitVec 162) ++ (0x1f0000000003c78f1c00000 : BitVec 162)
def signal72 : W := (0x2f008dc1c00003e0000000222448f468d1cd14d1 : BitVec 162) ++ (0x1f0007c3c00001e00000000000003c78f1cf1cf1 : BitVec 162)
def signal73 : W := (0x2f008dc1c05003e0224040222448f468d1cd14d1 : BitVec 162) ++ (0x1f0007c3c00001e00000000000003c78f1cf1cf1 : BitVec 162)
def signal74 : W := (0x2f008dc1c05e03e022f070222448fc78f1cf1cf1 : BitVec 162) ++ (0x1f0007c3c03e01e001f0f00000003c78f1cf1cf1 : BitVec 162)
def signal75 : W := (0x38008b03007003002340c0222448c40810410411 : BitVec 162) ++ (0x0 : BitVec 162)
def signal76 : W := (0x38008b03007e030023f0f0222448cc1830430c31 : BitVec 162) ++ (0x3e000001f0f0000000000000000000 : BitVec 162)
def signal77 : W := (0x3b008f43407603600200f0000048c000000f1cf1 : BitVec 162) ++ (0x1f0007c3c03e01e00000f00000000000000f1cf1 : BitVec 162)
def signal78 : W := (0x3b008f43407603602240f0222448c408104f1cf1 : BitVec 162) ++ (0x1f0007c3c03e01e00000f00000000000000f1cf1 : BitVec 162)
def signal79 : W := (0x3b008f43407e03e022f0f0222448dc3870cf1cf1 : BitVec 162) ++ (0x1f0007c3c03e01e001f0f00000003c78f1cf1cf1 : BitVec 162)
def signal80 : W := (0x3b008fc3c07603602370f0222448ec58b14f1cf1 : BitVec 162) ++ (0x1f0007c3c03e01e001f0f00000003c78f1cf1cf1 : BitVec 162)
def signal81 : W := (0x3d000803c07a03a023d0d0002400c000f1c000f1 : BitVec 162) ++ (0x1f000003c03e01e001f0f00000000000f1c000f1 : BitVec 162)
def signal82 : W := (0x3d008903c07a03a023d0d0222448c408f1c104f1 : BitVec 162) ++ (0x1f000003c03e01e001f0f00000000000f1c000f1 : BitVec 162)
def signal83 : W := (0x3d008bc3c07a03a023f0f0222448ec58f1cb0cf1 : BitVec 162) ++ (0x1f0007c3c03e01e001f0f00000003c78f1cf1cf1 : BitVec 162)
def signal84 : W := (0x3e008f83807c03c023e0e0020408407801c01c01 : BitVec 162) ++ (0x1f0007c3c03e01e001f0f0000000007801c01c01 : BitVec 162)
def signal85 : W := (0x3e008f83807c03c023e0e0222448c47811c11c11 : BitVec 162) ++ (0x1f0007c3c03e01e001f0f0000000007801c01c01 : BitVec 162)
def signal86 : W := (0x3e008f83807e03e023f0f0222448dc7871c71c71 : BitVec 162) ++ (0x1f0007c3c03e01e001f0f00000003c78f1cf1cf1 : BitVec 162)
def signal87 : W := (0x3e008fc3c07c03c023f0f0222448ec78b1cb1cb1 : BitVec 162) ++ (0x1f0007c3c03e01e001f0f00000003c78f1cf1cf1 : BitVec 162)
def signal88 : W := (0x3f000400007e03e0008000000000102040841040 : BitVec 162) ++ (0x1f000000003e01e0000000000000000000000000 : BitVec 162)
def signal89 : W := (0x3f008d01007e03e022c040222448d42850c51451 : BitVec 162) ++ (0x1f000000003e01e0000000000000000000000000 : BitVec 162)
def signal90 : W := (0x3f008dc3c07a03e023d0d0222448f468f1cd14f1 : BitVec 162) ++ (0x1f0007c3c03e01e001f0f00000003c78f1cf1cf1 : BitVec 162)
def signal91 : W := (0x3f008fc3c0200000010080000000204081080080 : BitVec 162) ++ (0x1f0007c3c0000000000000000000000000000000 : BitVec 162)
def signal92 : W := (0x3f008fc3c07003002340c0222448e44891490491 : BitVec 162) ++ (0x1f0007c3c0000000000000000000000000000000 : BitVec 162)
def signal93 : W := (0x3f008fc3c07c03e023e0e0222448f478d1cd1cd1 : BitVec 162) ++ (0x1f0007c3c03e01e001f0f00000003c78f1cf1cf1 : BitVec 162)
def signal94 : W := (0x3f008fc3c07e03e023f0f0222448fc78f1cf1cf1 : BitVec 162) ++ (0x1f0007c3c03e01e001f0f00000003c78f1cf1cf1 : BitVec 162)
def signal95 : W := (0x3f008fc3c0fe23e067f1f26264c9fcf8f3cf3cf3 : BitVec 162) ++ (0x1f0007c3c03e01e001f0f00000003c78f1cf1cf1 : BitVec 162)
def signal96 : W := (0x3f048fd3c17e43e0abf2f46624d8fcf9f1cf3df1 : BitVec 162) ++ (0x1f0007c3c03e01e001f0f00000003c78f1cf1cf1 : BitVec 162)
def signal97 : W := (0x3f108fc7c87e23e423f1f2222448fff8ffcffcff : BitVec 162) ++ (0x1f0007c3c03e01e001f0f00000003ff8ffcffcff : BitVec 162)
def signal98 : W := (0x3f208fffc07e43e823f2f4222448fffff1cffff1 : BitVec 162) ++ (0x1f0007ffc03e01e001f0f00000003ffff1cffff1 : BitVec 162)
def signal99 : W := (0x3f408fcbd07e83f023fff0222448ffffffff1cf1 : BitVec 162) ++ (0x1f0007c3c03e01e001fff00000003fffffff1cf1 : BitVec 162)
def signal100 : W := (0x3f808fd3e07fe3e023fffe222448fcf9f3cf3df3 : BitVec 162) ++ (0x1f0007c3c03fe1e001fffe0000003c78f1cf1cf1 : BitVec 162)
def signal101 : W := (0x3ff08fe3c07fe3fc23f4f0222448fd7af5df5ef5 : BitVec 162) ++ (0x1ff007c3c03fe1fc01f0f00000003c78f1cf1cf1 : BitVec 162)
def signal102 : W := (0x3ff08ffff87f03e023f8f8222448fe7cf9ef9cf9 : BitVec 162) ++ (0x1ff007fff83e01e001f0f00000003c78f1cf1cf1 : BitVec 162)
def signal103 : W := (0x4001100000800400440001e1e3c7840010010010 : BitVec 162) ++ (0x1e1e3c7800000000000 : BitVec 162)
def signal104 : W := (0x4011100408802404440103c1c38703800e00e00e : BitVec 162) ++ (0x1e1e3c783800e00e00e : BitVec 162)
def signal105 : W := (0x4110000000822424000000808102110044044044 : BitVec 162) ++ (0x0 : BitVec 162)
def signal106 : W := (0x411010004882242444111201e0078000fe0000fe : BitVec 162) ++ (0x1e0078000fe0000fe : BitVec 162)
def signal107 : W := (0x4111104448000000000001010204220088088088 : BitVec 162) ++ (0x0 : BitVec 162)
def signal108 : W := (0x4111104448000424000001a1a346b700dc0dc0dc : BitVec 162) ++ (0x1e1e3c7bf80fe0fe0fe : BitVec 162)
def signal109 : W := (0x41111044488224240400120003c78000000fe0fe : BitVec 162) ++ (0x3c78000000fe0fe : BitVec 162)
def signal110 : W := (0x411110444882242444111201e3c78000fe0fe0fe : BitVec 162) ++ (0x1e3c78000fe0fe0fe : BitVec 162)
def signal111 : W := (0x41111044488224244411124043c78880220fe0fe : BitVec 162) ++ (0x3c78000000fe0fe : BitVec 162)
def signal112 : W := (0x4111104448822424441112e0e3c79d80760fe0fe : BitVec 162) ++ (0x1e1e3c7bf80fe0fe0fe : BitVec 162)
def signal113 : W := (0x411110444882242444111301e207a200fe0880fe : BitVec 162) ++ (0x1e0078000fe0000fe : BitVec 162)
def signal114 : W := (0x41111044488224244411136163c7ae80ba0fe0fe : BitVec 162) ++ (0x1e1e3c7bf80fe0fe0fe : BitVec 162)
def signal115 : W := (0x411110444882242444111361e2c7ae80fe0ba0fe : BitVec 162) ++ (0x1e1e3c7bf80fe0fe0fe : BitVec 162)
def signal116 : W := (0x4111104448822424441113a1e347b700fe0dc0fe : BitVec 162) ++ (0x1e1e3c7bf80fe0fe0fe : BitVec 162)
def signal117 : W := (0x4111104448822424441113c1c3873b80ee0ee0ee : BitVec 162) ++ (0x1e1e3c7bf80fe0fe0fe : BitVec 162)
def signal118 : W := (0x4111104448822424441113c1c3c7bb80ee0fe0fe : BitVec 162) ++ (0x1e1e3c7bf80fe0fe0fe : BitVec 162)
def signal119 : W := (0x4111104448822424441113c1e387bb80fe0ee0fe : BitVec 162) ++ (0x1e1e3c7bf80fe0fe0fe : BitVec 162)
def signal120 : W := (0x4111104448822424441113e1c3c73f80ee0fe0ee : BitVec 162) ++ (0x1e1e3c7bf80fe0fe0fe : BitVec 162)
def signal121 : W := (0x4111104448822424441113e1e3873f80fe0ee0ee : BitVec 162) ++ (0x1e1e3c7bf80fe0fe0fe : BitVec 162)
def signal122 : W := (0x4111104448822424441113e1e3c7bf80fe0fe0fe : BitVec 162) ++ (0x1e1e3c7bf80fe0fe0fe : BitVec 162)
def signal123 : W := (0x4111104448822424645113e3e7c7bf88fe4fe0fe : BitVec 162) ++ (0x1e1e3c7bf80fe0fe0fe : BitVec 162)
def signal124 : W := (0x4111104448d22424665153e1e3c7bf80fe0fe0fe : BitVec 162) ++ (0x1e1e3c7bf80fe0fe0fe : BitVec 162)
def signal125 : W := (0x4111104448d22724665153e3e7cfff88fe4fe4ff : BitVec 162) ++ (0x1e1e3c7bf80fe0fe0fe : BitVec 162)
def signal126 : W := (0x4111104449866c6ccc3337efe3ffbfbbfe0ffffe : BitVec 162) ++ (0x1ffe3ffbffffe0ffffe : BitVec 162)
def signal127 : W := (0x4111914448822424441113e3e3cfbf88fe0fe4fe : BitVec 162) ++ (0x1e1e3c7bf80fe0fe0fe : BitVec 162)
def signal128 : W := (0x4111994548822424665153e3e7cfff88fe4fe4ff : BitVec 162) ++ (0x1e1e3c7bf80fe0fe0fe : BitVec 162)
def signal129 : W := (0x411310cc48822424c43313ffe3c7bffffe0fe0fe : BitVec 162) ++ (0x1ffe3c7bffffe0fe0fe : BitVec 162)
def signal130 : W := (0x4115125449866424cc3337e5e3d7bf91fe0fe9fe : BitVec 162) ++ (0x1e1e3c7bf80fe0fe0fe : BitVec 162)
def signal131 : W := (0x6800890100d00700224040a2a54ac40810410411 : BitVec 162) ++ (0x0 : BitVec 162)
def signal132 : W := (0x680199010050030022404123264cc40810410411 : BitVec 162) ++ (0x0 : BitVec 162)
def signal133 : W := (0x6801990100d00700664041e3e7cfc40810410411 : BitVec 162) ++ (0x1e1e3c7800000000000 : BitVec 162)
def signal134 : W := (0x6910890100d22724224040a2a54ad50854454455 : BitVec 162) ++ (0x0 : BitVec 162)
def signal135 : W := (0x6911104448d22724441113e1e3c7bf80fe0fe0fe : BitVec 162) ++ (0x1e1e3c7bf80fe0fe0fe : BitVec 162)
def signal136 : W := (0x6911184548d22724665153e1e7c7ff80fe4fe0ff : BitVec 162) ++ (0x1e1e3c7bf80fe0fe0fe : BitVec 162)
def signal137 : W := (0x691199454850030022404123264ce60898498499 : BitVec 162) ++ (0x0 : BitVec 162)
def signal138 : W := (0x6911994548822424441113e1e3c7bf80fe0fe0fe : BitVec 162) ++ (0x1e1e3c7bf80fe0fe0fe : BitVec 162)
def signal139 : W := (0x6911994548822724441113e3e7cfff88fe4fe4ff : BitVec 162) ++ (0x1e1e3c7bf80fe0fe0fe : BitVec 162)
def signal140 : W := (0x6911994548d22724461153e1e3cfff80fe0fe4ff : BitVec 162) ++ (0x1e1e3c7bf80fe0fe0fe : BitVec 162)
def signal141 : W := (0x6911994548d22724665153c3c78f7b88ee4ee4ef : BitVec 162) ++ (0x1e1e3c7bf80fe0fe0fe : BitVec 162)
def signal142 : W := (0x6911994548d22724665153e3e7cfff88fe4fe4ff : BitVec 162) ++ (0x1e1e3c7bf80fe0fe0fe : BitVec 162)
def signal143 : W := (0x7e119f8788fc27c467e1e3c3c78f43f80fc0fc0f : BitVec 162) ++ (0x1f0007c3c03e01e001f0f1e1e3c783f80fc0fc0f : BitVec 162)
def signal144 : W := (0x7f108fc3c0fe27e423f0f0a2a54afd78f5cf5cf5 : BitVec 162) ++ (0x1f0007c3c03e01e001f0f00000003c78f1cf1cf1 : BitVec 162)
def signal145 : W := (0x7f119fc7c87e03e023f0f123264cfe78f9cf9cf9 : BitVec 162) ++ (0x1f0007c3c03e01e001f0f00000003c78f1cf1cf1 : BitVec 162)
def signal146 : W := (0x7f119fc7c8fe27e467f1f3e3e7cffff8ffcffcff : BitVec 162) ++ (0x1f0007c3c03e01e001f0f1e1e3c7bff8ffcffcff : BitVec 162)
def signal147 : W := (0x800f810001000800880001fe03f8040800010400 : BitVec 162) ++ (0xf800000000000000001fe03f8000000000000 : BitVec 162)
def signal148 : W := (0x802f003c01004808880205dc03b003870000e300 : BitVec 162) ++ (0xf803c00000000000001fe03f803870000e300 : BitVec 162)
def signal149 : W := (0x8228042001044848000000880120112200045200 : BitVec 162) ++ (0x0 : BitVec 162)
def signal150 : W := (0x8228042001044848882224ee01f81dbb00077f00 : BitVec 162) ++ (0x1fe03f83fff000fff00 : BitVec 162)
def signal151 : W := (0x8228042003defffd008400888922112244945244 : BitVec 162) ++ (0x7fffffc000000000000000000000000 : BitVec 162)
def signal152 : W := (0x822b85ec00000848000001ba0368376e000dd600 : BitVec 162) ++ (0xf87fc00000000000001fe03f83fff000fff00 : BitVec 162)
def signal153 : W := (0x822b85ec01044848882225fe03f83fff000fff00 : BitVec 162) ++ (0xf87fc00000000000001fe03f83fff000fff00 : BitVec 162)
def signal154 : W := (0x822c063001044848882224cc01b019b300067b00 : BitVec 162) ++ (0x0 : BitVec 162)
def signal155 : W := (0x822d8774010448480800240003f80000000fff00 : BitVec 162) ++ (0xf87fc000000000000000003f80000000fff00 : BitVec 162)
def signal156 : W := (0x822d8774010448488822244403f80891000fff00 : BitVec 162) ++ (0xf87fc000000000000000003f80000000fff00 : BitVec 162)
def signal157 : W := (0x822d877401044848882224ee03f81dbb000fff00 : BitVec 162) ++ (0xf87fc00000000000001fe03f83fff000fff00 : BitVec 162)
def signal158 : W := (0x822e06b8010448488822241c0030007700001b00 : BitVec 162) ++ (0xf87fc000000000000001e0038007f00001f00 : BitVec 162)
def signal159 : W := (0x822e87b8010448488822241e0038007f00001f00 : BitVec 162) ++ (0xf87fc000000000000001e0038007f00001f00 : BitVec 162)
def signal160 : W := (0x822e87b8010448488822243e0078047f00011f00 : BitVec 162) ++ (0xf87fc000000000000001e0038007f00001f00 : BitVec 162)
def signal161 : W := (0x822e87b8010448488822245e00b808ff00023f00 : BitVec 162) ++ (0xf87fc000000000000001e0038007f00001f00 : BitVec 162)
def signal162 : W := (0x822e87b8010448488822249e0138117f00045f00 : BitVec 162) ++ (0xf87fc000000000000001e0038007f00001f00 : BitVec 162)
def signal163 : W := (0x822e87b801044848882224fe01f81dff00077f00 : BitVec 162) ++ (0xf87fc00000000000001fe03f83fff000fff00 : BitVec 162)
def signal164 : W := (0x822e87b801044848882225fe00383fff00001f00 : BitVec 162) ++ (0xf87fc00000000000001fe00383fff00001f00 : BitVec 162)
def signal165 : W := (0x822e87f8010448488822243e00783c7f000f1f00 : BitVec 162) ++ (0xf87fc000000000000001e00383c7f000f1f00 : BitVec 162)
def signal166 : W := (0x822e87fc010448488822241e00383bff000eff00 : BitVec 162) ++ (0xf87fc000000000000001e00383fff000fff00 : BitVec 162)
def signal167 : W := (0x822f06fc01044848882225dc03b03bf7000efb00 : BitVec 162) ++ (0xf87fc00000000000001fe03f83fff000fff00 : BitVec 162)
def signal168 : W := (0x822f06fc01044848882225fc03f03ff7000ffb00 : BitVec 162) ++ (0xf87fc00000000000001fe03f83fff000fff00 : BitVec 162)
def signal169 : W := (0x822f06fc01044848882225fe03b03fff000efb00 : BitVec 162) ++ (0xf87fc00000000000001fe03f83fff000fff00 : BitVec 162)
def signal170 : W := (0x822f06fc01044848882225fe03f83fff000fff00 : BitVec 162) ++ (0xf87fc00000000000001fe03f83fff000fff00 : BitVec 162)
def signal171 : W := (0x822f87b801044848882225fe03f8047f00011f00 : BitVec 162) ++ (0xf87fc00000000000001fe03f8007f00001f00 : BitVec 162)
def signal172 : W := (0x822f87bc01044848882225de03b803ff0000ff00 : BitVec 162) ++ (0xf87fc00000000000001fe03f803ff0000ff00 : BitVec 162)
def signal173 : W := (0x822f87fc00000000000001100200224400088000 : BitVec 162) ++ (0xf87fc00000000000000000000000000000000 : BitVec 162)
def signal174 : W := (0x822f87fc010448488822241e03f8007f000fff00 : BitVec 162) ++ (0xf87fc000000000000001e03f8007f000fff00 : BitVec 162)
def signal175 : W := (0x822f87fc010448488822251e0238227f00089f00 : BitVec 162) ++ (0xf87fc000000000000001e0038007f00001f00 : BitVec 162)
def signal176 : W := (0x822f87fc010448488822257603f82edd000fff00 : BitVec 162) ++ (0xf87fc00000000000001fe03f83fff000fff00 : BitVec 162)
def signal177 : W := (0x822f87fc010448488822257e02f82eff000bbf00 : BitVec 162) ++ (0xf87fc00000000000001fe03f83fff000fff00 : BitVec 162)
def signal178 : W := (0x822f87fc01044848882225be0378377f000ddf00 : BitVec 162) ++ (0xf87fc00000000000001fe03f83fff000fff00 : BitVec 162)
def signal179 : W := (0x822f87fc01044848882225dc03b03bf7000efb00 : BitVec 162) ++ (0xf87fc00000000000001fe03f83fff000fff00 : BitVec 162)
def signal180 : W := (0x822f87fc01044848882225dc03f83bf7000fff00 : BitVec 162) ++ (0xf87fc00000000000001fe03f83fff000fff00 : BitVec 162)
def signal181 : W := (0x822f87fc01044848882225de03b83bff000eff00 : BitVec 162) ++ (0xf87fc00000000000001fe03f83fff000fff00 : BitVec 162)
def signal182 : W := (0x822f87fc01044848882225fe03f83fff000fff00 : BitVec 162) ++ (0xf87fc00000000000001fe03f83fff000fff00 : BitVec 162)
def signal183 : W := (0x822f87fc01044848882225fe23f8bfff100fff10 : BitVec 162) ++ (0xf87fc00000000000001fe03f83fff000fff00 : BitVec 162)
def signal184 : W := (0x822f87fc01044848a86225fe27f83fff104fff00 : BitVec 162) ++ (0xf87fc00000000000001fe03f83fff000fff00 : BitVec 162)
def signal185 : W := (0x822f87fc01044848c83325ffe3f83ffffe0fff00 : BitVec 162) ++ (0xf87fc00000000000001ffe3f83ffffe0fff00 : BitVec 162)
def signal186 : W := (0x822f87fc01544848aa6265fe03f83fff000fff00 : BitVec 162) ++ (0xf87fc00000000000001fe03f83fff000fff00 : BitVec 162)
def signal187 : W := (0x822f87fc01544b48aa6265fe27f8ffff104fff11 : BitVec 162) ++ (0xf87fc00000000000001fe03f83fff000fff00 : BitVec 162)
def signal188 : W := (0x822f87fc01866848cc3337fe43f93fff220fff22 : BitVec 162) ++ (0xf87fc00000000000001fe03f83fff000fff00 : BitVec 162)
def signal189 : W := (0x822f87fc01866c6ccc3337fee3fbbfff760fff76 : BitVec 162) ++ (0xf87fc00000000000001ffe3ffbffffe0ffffe : BitVec 162)
def signal190 : W := (0x822f8ffd01044848aa6265fe27f8ffff104fff11 : BitVec 162) ++ (0xf87fc00000000000001fe03f83fff000fff00 : BitVec 162)
def signal191 : W := (0x822f97fc49044848cc3337ff63fdbfffba0fffba : BitVec 162) ++ (0xf87fc00000000000001ffe3ffbffffe0ffffe : BitVec 162)
def signal192 : W := (0x822ffffff904484a992aadff13fc3fff892fff88 : BitVec 162) ++ (0xffffff8000000000001fe03f83fff000fff00 : BitVec 162)
def signal193 : W := (0x832f87fc41064868883235fe23f8bffff00ffff0 : BitVec 162) ++ (0xf87fc00000000000001fe03f83ffff00ffff0 : BitVec 162)
def signal194 : W := (0x833f87fc4906686c883337fe03f83fffee0fffee : BitVec 162) ++ (0xf87fc00000000000001fe03f83ffffe0ffffe : BitVec 162)
def signal195 : W := (0xa808890101500b00224040aa2568c40810410411 : BitVec 162) ++ (0x0 : BitVec 162)
def signal196 : W := (0xa80f890101500b00aa4041fe27f8c40810410411 : BitVec 162) ++ (0xf800000000000000001fe03f8000000000000 : BitVec 162)
def signal197 : W := (0xaa288d2101544b48224040aa2568d52a10455611 : BitVec 162) ++ (0x0 : BitVec 162)
def signal198 : W := (0xaa2c8f3101544b48aa6264ee25f8ddbb10477f11 : BitVec 162) ++ (0x0 : BitVec 162)
def signal199 : W := (0xaa2e8fb901544b48aa62641e0438407f00401f01 : BitVec 162) ++ (0xf87fc000000000000001e0038007f00001f00 : BitVec 162)
def signal200 : W := (0xaa2e8fb901544b48aa62643e2478c47f10411f11 : BitVec 162) ++ (0xf87fc000000000000001e0038007f00001f00 : BitVec 162)
def signal201 : W := (0xaa2f0efd01544b48aa6265dc27b0fbf7104efb11 : BitVec 162) ++ (0xf87fc00000000000001fe03f83fff000fff00 : BitVec 162)
def signal202 : W := (0xaa2f87fc01544b48882225fe03f83fff000fff00 : BitVec 162) ++ (0xf87fc00000000000001fe03f83fff000fff00 : BitVec 162)
def signal203 : W := (0xaa2f8ffd01044848882225fe03f83fff000fff00 : BitVec 162) ++ (0xf87fc00000000000001fe03f83fff000fff00 : BitVec 162)
def signal204 : W := (0xaa2f8ffd01044b48882225fe27f8ffff104fff11 : BitVec 162) ++ (0xf87fc00000000000001fe03f83fff000fff00 : BitVec 162)
def signal205 : W := (0xaa2f8ffd01544b488a2265fe03f8ffff000fff11 : BitVec 162) ++ (0xf87fc00000000000001fe03f83fff000fff00 : BitVec 162)
def signal206 : W := (0xaa2f8ffd01544b48aa6265fe07f87fff004fff01 : BitVec 162) ++ (0xf87fc00000000000001fe03f83fff000fff00 : BitVec 162)
def signal207 : W := (0xaa2f8ffd01544b48aa6265fe27f8ffff104fff11 : BitVec 162) ++ (0xf87fc00000000000001fe03f83fff000fff00 : BitVec 162)
def signal208 : W := (0xbd2f083fc17a4ba8abd2d5dc27b0c387f1c0e3f1 : BitVec 162) ++ (0x1f0f803fc03e01e001f0f1fe03f80387f1c0e3f1 : BitVec 162)
def signal209 : W := (0xbf288fe3c17e4be823f0f0aa2568fd7af1cf5ef1 : BitVec 162) ++ (0x1f0007c3c03e01e001f0f00000003c78f1cf1cf1 : BitVec 162)
def signal210 : W := (0xbf2f8fffc17e4be8abf2f5fe27f8fffff1cffff1 : BitVec 162) ++ (0x1f0f87ffc03e01e001f0f1fe03f83ffff1cffff1 : BitVec 162)
def signal211 : W := (0xc22f97fc01844c48cc2225ffe3ffbfff100fff10 : BitVec 162) ++ (0xf87fc00000000000001ffe3ffbfff000fff00 : BitVec 162)
def signal212 : W := (0xc23f97fc09846c4ccc2327ffc3ff3fff0e0fff0e : BitVec 162) ++ (0xf87fc00000000000001ffe3ffbfff0e0fff0e : BitVec 162)
def signal213 : W := (0xc339146449866c6c441113e9e3e7bfa2fe0ff2fe : BitVec 162) ++ (0x1e1e3c7bf80fe0fe0fe : BitVec 162)
def signal214 : W := (0xc339146449866c6ccc3337efe3ffbfbbfe0ffffe : BitVec 162) ++ (0x1ffe3ffbffffe0ffffe : BitVec 162)
def signal215 : W := (0xc33d167449866c6ccc3337ede3f7bfb3fe0ffbfe : BitVec 162) ++ (0x1e1e3c7bf80fe0fe0fe : BitVec 162)
def signal216 : W := (0xc33e97b849866c6ccc33361fe03f807ffe001ffe : BitVec 162) ++ (0xf87fc000000000000001fe03f807ffe001ffe : BitVec 162)
def signal217 : W := (0xc33f16fc49866c6ccc3337ddc3b73bf7ee0efbee : BitVec 162) ++ (0xf87fc00000000000001ffe3ffbffffe0ffffe : BitVec 162)
def signal218 : W := (0xc33f16fc49866c6ccc3337fde3f7bff7fe0ffbfe : BitVec 162) ++ (0xf87fc00000000000001ffe3ffbffffe0ffffe : BitVec 162)
def signal219 : W := (0xc33f87fc01866c6c882225fe83fa3fff440fff44 : BitVec 162) ++ (0xf87fc00000000000001fe03f83fff000fff00 : BitVec 162)
def signal220 : W := (0xc33f97fc49044848882225ff03fc3fff880fff88 : BitVec 162) ++ (0xf87fc00000000000001fe03f83fff000fff00 : BitVec 162)
def signal221 : W := (0xc33f97fc49044c6c882225ffa3febfffdc0fffdc : BitVec 162) ++ (0xf87fc00000000000001ffe3ffbffffe0ffffe : BitVec 162)
def signal222 : W := (0xc33f97fc49866c6c8c2237fe03ffbfff000ffffe : BitVec 162) ++ (0xf87fc00000000000001fe03ffbfff000ffffe : BitVec 162)
def signal223 : W := (0xc33f97fc49866c6ccc3337ffc3ff3fffee0fffee : BitVec 162) ++ (0xf87fc00000000000001ffe3ffbffffe0ffffe : BitVec 162)
def signal224 : W := (0xc33f97fc49866c6ccc3337ffe3ffbffffe0ffffe : BitVec 162) ++ (0xf87fc00000000000001ffe3ffbffffe0ffffe : BitVec 162)
def signal225 : W := (0xeb3f9ffd49d66f6cee7377ffe7fffffffe4fffff : BitVec 162) ++ (0xf87fc00000000000001ffe3ffbffffe0ffffe : BitVec 162)
def signal226 : W := (0x10002200002001003e04001fffc00040810400000 : BitVec 162) ++ (0x3e00001fffc00000000000000 : BitVec 162)
def signal227 : W := (0x10042200812009013c00f01ddd80003870e300000 : BitVec 162) ++ (0x3e00f01fffc0003870e300000 : BitVec 162)
def signal228 : W := (0x10440000002089091008400888800112244900000 : BitVec 162) ++ (0x0 : BitVec 162)
def signal229 : W := (0x1044020009208909361dd0001fc000000fff00000 : BitVec 162) ++ (0x3e1ff0001fc000000fff00000 : BitVec 162)
def signal230 : W := (0x10442208890000002010801111000224489200000 : BitVec 162) ++ (0x0 : BitVec 162)
def signal231 : W := (0x10442208890001090000001bbbc00376eddf00000 : BitVec 162) ++ (0x1fffc003ffffff00000 : BitVec 162)
def signal232 : W := (0x10442208892089091008401bbbc00376eddf00000 : BitVec 162) ++ (0x1fffc003ffffff00000 : BitVec 162)
def signal233 : W := (0x10442208892089091e0f701fffc003ffffff00000 : BitVec 162) ++ (0x3e1ff01fffc003ffffff00000 : BitVec 162)
def signal234 : W := (0x10442208892089093018c019998003366cdb00000 : BitVec 162) ++ (0x0 : BitVec 162)
def signal235 : W := (0x1044220889208909361dd0111fc002244fff00000 : BitVec 162) ++ (0x3e1ff0001fc000000fff00000 : BitVec 162)
def signal236 : W := (0x1044220889208909361dd01bbfc00376efff00000 : BitVec 162) ++ (0x3e1ff01fffc003ffffff00000 : BitVec 162)
def signal237 : W := (0x1044220889208909381ae001c1800007701b00000 : BitVec 162) ++ (0x3e1ff001e1c00007f01f00000 : BitVec 162)
def signal238 : W := (0x10442208892089093a1ee001e1c00007f01f00000 : BitVec 162) ++ (0x3e1ff001e1c00007f01f00000 : BitVec 162)
def signal239 : W := (0x10442208892089093a1ee003e3c00047f11f00000 : BitVec 162) ++ (0x3e1ff001e1c00007f01f00000 : BitVec 162)
def signal240 : W := (0x10442208892089093a1ee009e9c00117f45f00000 : BitVec 162) ++ (0x3e1ff001e1c00007f01f00000 : BitVec 162)
def signal241 : W := (0x10442208892089093a1ee011f1c00227f89f00000 : BitVec 162) ++ (0x3e1ff001e1c00007f01f00000 : BitVec 162)
def signal242 : W := (0x10442208892089093a1ee01bfbc00377fddf00000 : BitVec 162) ++ (0x3e1ff01fffc003ffffff00000 : BitVec 162)
def signal243 : W := (0x10442208892089093a1ee01fe1c003fff01f00000 : BitVec 162) ++ (0x3e1ff01fe1c003fff01f00000 : BitVec 162)
def signal244 : W := (0x10442208892089093a1fe003e3c003c7ff1f00000 : BitVec 162) ++ (0x3e1ff001e1c003c7ff1f00000 : BitVec 162)
def signal245 : W := (0x10442208892089093a1ff001e1c003bffeff00000 : BitVec 162) ++ (0x3e1ff001e1c003ffffff00000 : BitVec 162)
def signal246 : W := (0x10442208892089093c1bf01ddd8003bf7efb00000 : BitVec 162) ++ (0x3e1ff01fffc003ffffff00000 : BitVec 162)
def signal247 : W := (0x10442208892089093c1bf01fdf8003ff7ffb00000 : BitVec 162) ++ (0x3e1ff01fffc003ffffff00000 : BitVec 162)
def signal248 : W := (0x10442208892089093c1bf01ffd8003fffefb00000 : BitVec 162) ++ (0x3e1ff01fffc003ffffff00000 : BitVec 162)
def signal249 : W := (0x10442208892089093c1bf01fffc003ffffff00000 : BitVec 162) ++ (0x3e1ff01fffc003ffffff00000 : BitVec 162)
def signal250 : W := (0x10442208892089093e1ee01fffc00047f11f00000 : BitVec 162) ++ (0x3e1ff01fffc00007f01f00000 : BitVec 162)
def signal251 : W := (0x10442208892089093e1ef01dfdc0003ff0ff00000 : BitVec 162) ++ (0x3e1ff01fffc0003ff0ff00000 : BitVec 162)
def signal252 : W := (0x10442208892089093e1ff001ffc00007ffff00000 : BitVec 162) ++ (0x3e1ff001ffc00007ffff00000 : BitVec 162)
def signal253 : W := (0x10442208892089093e1ff005e5c0008ff23f00000 : BitVec 162) ++ (0x3e1ff001e1c00007f01f00000 : BitVec 162)
def signal254 : W := (0x10442208892089093e1ff00fefc001dff77f00000 : BitVec 162) ++ (0x3e1ff01fffc003ffffff00000 : BitVec 162)
def signal255 : W := (0x10442208892089093e1ff0177fc002eddfff00000 : BitVec 162) ++ (0x3e1ff01fffc003ffffff00000 : BitVec 162)
def signal256 : W := (0x10442208892089093e1ff017f7c002effbbf00000 : BitVec 162) ++ (0x3e1ff01fffc003ffffff00000 : BitVec 162)
def signal257 : W := (0x10442208892089093e1ff01ddd8003bf7efb00000 : BitVec 162) ++ (0x3e1ff01fffc003ffffff00000 : BitVec 162)
def signal258 : W := (0x10442208892089093e1ff01ddfc003bf7fff00000 : BitVec 162) ++ (0x3e1ff01fffc003ffffff00000 : BitVec 162)
def signal259 : W := (0x10442208892089093e1ff01dfdc003bffeff00000 : BitVec 162) ++ (0x3e1ff01fffc003ffffff00000 : BitVec 162)
def signal260 : W := (0x10442208892089093e1ff01fffc003ffffff00000 : BitVec 162) ++ (0x3e1ff01fffc003ffffff00000 : BitVec 162)
def signal261 : W := (0x10442208892089093e1ff01fffc40bffffff10010 : BitVec 162) ++ (0x3e1ff01fffc003ffffff00000 : BitVec 162)
def signal262 : W := (0x10442208892589093e3ff41fffc003ffffff00000 : BitVec 162) ++ (0x3e1ff01fffc003ffffff00000 : BitVec 162)
def signal263 : W := (0x10442208892589393e3ff41fffc48fffffff10411 : BitVec 162) ++ (0x3e1ff01fffc003ffffff00000 : BitVec 162)
def signal264 : W := (0x104422088928ab093e5ff13fffc813ffffff22022 : BitVec 162) ++ (0x3e1ff01fffc003ffffff00000 : BitVec 162)
def signal265 : W := (0x104422088928ab4b7e5ff13fffdc3bffffff76076 : BitVec 162) ++ (0x3e1ff01ffffc7bfffffffe0fe : BitVec 162)
def signal266 : W := (0x104422088930cd8dbe9ff25fffdf83ffffff77f00 : BitVec 162) ++ (0x3e1ff01fffff83fffffffff00 : BitVec 162)
def signal267 : W := (0x10442a18892089093e1ff01fffc483ffffff10400 : BitVec 162) ++ (0x3e1ff01fffc003ffffff00000 : BitVec 162)
def signal268 : W := (0x10442a98992089093e3ff41fffc48fffffff10411 : BitVec 162) ++ (0x3e1ff01fffc003ffffff00000 : BitVec 162)
def signal269 : W := (0x1044320cc92089093e1ff01ffffc03fffffffe000 : BitVec 162) ++ (0x3e1ff01ffffc03fffffffe000 : BitVec 162)
def signal270 : W := (0x1044330ccda089093e5ff13fffec5bffffffba0ba : BitVec 162) ++ (0x3e1ff01ffffc7bfffffffe0fe : BitVec 162)
def signal271 : W := (0x104462298930cd093e9ff25fffc903ffffff22900 : BitVec 162) ++ (0x3e1ff01fffc003ffffff00000 : BitVec 162)
def signal272 : W := (0x10446629ab2089093fffffffffc913ffffff22922 : BitVec 162) ++ (0x3fffffffffc003ffffff00000 : BitVec 162)
def signal273 : W := (0x1054220c8d20a90b3e1ff11fffc40bfffffff00f0 : BitVec 162) ++ (0x3e1ff01fffc003fffffff00f0 : BitVec 162)
def signal274 : W := (0x1055220ccda0ab0b7e1ff13fffc003ffffffee0ee : BitVec 162) ++ (0x3e1ff01fffc003fffffffe0fe : BitVec 162)
def signal275 : W := (0x12800890102501301224040aaac48c40810410411 : BitVec 162) ++ (0x0 : BitVec 162)
def signal276 : W := (0x12802a90100500302224041333448c40810410411 : BitVec 162) ++ (0x0 : BitVec 162)
def signal277 : W := (0x12802a90102501303e24041fffc48c40810410411 : BitVec 162) ++ (0x3e00001fffc00000000000000 : BitVec 162)
def signal278 : W := (0x12c4089010258939122c440aaac48d52a54d10411 : BitVec 162) ++ (0x0 : BitVec 162)
def signal279 : W := (0x12c42208892589393e1ff01fffc003ffffff00000 : BitVec 162) ++ (0x3e1ff01fffc003ffffff00000 : BitVec 162)
def signal280 : W := (0x12c42288992589393e3ff41fffc00fffffff00011 : BitVec 162) ++ (0x3e1ff01fffc003ffffff00000 : BitVec 162)
def signal281 : W := (0x12c42a98990500302234841333448e64c99610411 : BitVec 162) ++ (0x0 : BitVec 162)
def signal282 : W := (0x12c42a98992089093e1ff01fffc003ffffff00000 : BitVec 162) ++ (0x3e1ff01fffc003ffffff00000 : BitVec 162)
def signal283 : W := (0x12c42a98992089393e1ff01fffc48fffffff10411 : BitVec 162) ++ (0x3e1ff01fffc003ffffff00000 : BitVec 162)
def signal284 : W := (0x12c42a9899258939323cc41bbbc48f76eddf10411 : BitVec 162) ++ (0x0 : BitVec 162)
def signal285 : W := (0x12c42a98992589393a3ee401e1c08407f01f00401 : BitVec 162) ++ (0x3e1ff001e1c00007f01f00000 : BitVec 162)
def signal286 : W := (0x12c42a98992589393a3ee403e3c48c47f11f10411 : BitVec 162) ++ (0x3e1ff001e1c00007f01f00000 : BitVec 162)
def signal287 : W := (0x12c42a98992589393c3bf41ddd848fbf7efb10411 : BitVec 162) ++ (0x3e1ff01fffc003ffffff00000 : BitVec 162)
def signal288 : W := (0x12c42a98992589393e3ff41fffc087ffffff00401 : BitVec 162) ++ (0x3e1ff01fffc003ffffff00000 : BitVec 162)
def signal289 : W := (0x12c42a98992589393e3ff41fffc48fffffff10411 : BitVec 162) ++ (0x3e1ff01fffc003ffffff00000 : BitVec 162)
def signal290 : W := (0x13b42af4b52769373c20ff1ddd848c3870e3f1cf1 : BitVec 162) ++ (0x1f0007c3c03e01e3e00ff1fffc0003870e3f1cf1 : BitVec 162)
def signal291 : W := (0x13f408fc3c27e93f123f4f0aaac48fd7af5df1cf1 : BitVec 162) ++ (0x1f0007c3c03e01e001f0f00000003c78f1cf1cf1 : BitVec 162)
def signal292 : W := (0x13f42afcbd07e03e223f8f1333448fe7cf9ef1cf1 : BitVec 162) ++ (0x1f0007c3c03e01e001f0f00000003c78f1cf1cf1 : BitVec 162)
def signal293 : W := (0x13f42afcbd27e93f3e3fff1fffc48ffffffff1cf1 : BitVec 162) ++ (0x1f0007c3c03e01e3e1fff1fffc003fffffff1cf1 : BitVec 162)
def signal294 : W := (0x14443308892889493e5ff01ffffc7bffffff10010 : BitVec 162) ++ (0x3e1ff01ffffc7bffffff00000 : BitVec 162)
def signal295 : W := (0x14453308c9a88b497e5ff03ffff873ffffff0e00e : BitVec 162) ++ (0x3e1ff01ffffc7bffffff0e00e : BitVec 162)
def signal296 : W := (0x1455110444a8ab4b5449513e9ebc7bfa2fe9fe0fe : BitVec 162) ++ (0x1e1e3c7bf80fe0fe0fe : BitVec 162)
def signal297 : W := (0x145522088928ab4b7e1ff01fffd023ffffff44044 : BitVec 162) ++ (0x3e1ff01fffc003ffffff00000 : BitVec 162)
def signal298 : W := (0x145523088da8ab4b7e5ff13fffc07bffffff000fe : BitVec 162) ++ (0x3e1ff01fffc07bffffff000fe : BitVec 162)
def signal299 : W := (0x1455330ccd8822426451913f1f3c7bfc4ff2fe0fe : BitVec 162) ++ (0x1e1e3c7bf80fe0fe0fe : BitVec 162)
def signal300 : W := (0x1455330ccd88234b4441113fbffc7bfeeffffe0fe : BitVec 162) ++ (0x1ffffc7bfffffffe0fe : BitVec 162)
def signal301 : W := (0x1455330ccda089093e1ff01fffe043ffffff88088 : BitVec 162) ++ (0x3e1ff01fffc003ffffff00000 : BitVec 162)
def signal302 : W := (0x1455330ccda0894b7e1ff01ffff46bffffffdc0dc : BitVec 162) ++ (0x3e1ff01ffffc7bfffffffe0fe : BitVec 162)
def signal303 : W := (0x1455330ccda8ab4b5449513fbffc7bfeeffffe0fe : BitVec 162) ++ (0x1ffffc7bfffffffe0fe : BitVec 162)
def signal304 : W := (0x1455330ccda8ab4b7459d13f9fbc7bfe6ffbfe0fe : BitVec 162) ++ (0x1e1e3c7bf80fe0fe0fe : BitVec 162)
def signal305 : W := (0x1455330ccda8ab4b7a5ee121e1fc7807f01ffe0fe : BitVec 162) ++ (0x3e1ff001e1fc7807f01ffe0fe : BitVec 162)
def signal306 : W := (0x1455330ccda8ab4b7c5bf13dddb873bf7efbee0ee : BitVec 162) ++ (0x3e1ff01ffffc7bfffffffe0fe : BitVec 162)
def signal307 : W := (0x1455330ccda8ab4b7c5bf13fdfbc7bff7ffbfe0fe : BitVec 162) ++ (0x3e1ff01ffffc7bfffffffe0fe : BitVec 162)
def signal308 : W := (0x1455330ccda8ab4b7e5ff13ffff873ffffffee0ee : BitVec 162) ++ (0x3e1ff01ffffc7bfffffffe0fe : BitVec 162)
def signal309 : W := (0x1455330ccda8ab4b7e5ff13ffffc7bfffffffe0fe : BitVec 162) ++ (0x3e1ff01ffffc7bfffffffe0fe : BitVec 162)
def signal310 : W := (0x16d53b9cddadab7b7e7ff53ffffcfffffffffe4ff : BitVec 162) ++ (0x3e1ff01ffffc7bfffffffe0fe : BitVec 162)
def signal311 : W := (0x1866a24a8930cd8dbe1ff01fffd203ffffff45200 : BitVec 162) ++ (0x3e1ff01fffc003ffffff00000 : BitVec 162)
def signal312 : W := (0x1866da774930cd8db69dd2401fff80000ffffff00 : BitVec 162) ++ (0xf87fc00000003e1ff0001fff80000ffffff00 : BitVec 162)
def signal313 : W := (0x1866f87fc030cd8d988a625fe8bf83fff449fff00 : BitVec 162) ++ (0xf87fc00000000000001fe03f83fff000fff00 : BitVec 162)
def signal314 : W := (0x1866fa7fc9104484a892a25ff13f83fff892fff00 : BitVec 162) ++ (0xf87fc00000000000001fe03f83fff000fff00 : BitVec 162)
def signal315 : W := (0x1866fa7fc910458d8882225ffbff83fffddffff00 : BitVec 162) ++ (0xf87fc00000000000001fffff83fffffffff00 : BitVec 162)
def signal316 : W := (0x1866fa7fc930cd8dbe9ff25fffff83fffffffff00 : BitVec 162) ++ (0xf87fc00000003e1ff01fffff83fffffffff00 : BitVec 162)
def signal317 : W := (0x1e80bb90100001f00000001bbbf6ec40810410411 : BitVec 162) ++ (0x3e00ff80000001e00000001ffffffc00000000000 : BitVec 162)
def signal318 : W := (0x1e80bb90100501f00224041bbbf6ec40810410411 : BitVec 162) ++ (0x3e00ff80000001e00000001ffffffc00000000000 : BitVec 162)
def signal319 : W := (0x1e80bb90103d01f01ee4041ffffffc40810410411 : BitVec 162) ++ (0x3e00ff80007c01e03fe0001ffffffc00000000000 : BitVec 162)
def signal320 : W := (0x1ef78042000001ffc000000888922112244945244 : BitVec 162) ++ (0x3fff0000000001ffc000000000000000000000000 : BitVec 162)
def signal321 : W := (0x1ef78042002089ffd008400888922112244945244 : BitVec 162) ++ (0x3fff0000000001ffc000000000000000000000000 : BitVec 162)
def signal322 : W := (0x1ef78042003defffd008400888922112244945244 : BitVec 162) ++ (0x3fff0000007fffffc000000000000000000000000 : BitVec 162)
def signal323 : W := (0x1ef7bbdedd8000000000001111204224489288088 : BitVec 162) ++ (0x3fffffffff8000000000000000000000000000000 : BitVec 162)
def signal324 : W := (0x1ef7bbdeddbdee001eef7775552952ad5ab2aa9aa : BitVec 162) ++ (0x3ffffffffffffe003fffffe000000000000000000 : BitVec 162)
def signal325 : W := (0x1ef7c463220001ffeff7bfeccc9b319b366967b66 : BitVec 162) ++ (0x3fff0000000001ffffffffe000000000000000000 : BitVec 162)
def signal326 : W := (0x1f88bbb13202fff0001bfbfbbbf6ecc9932432d33 : BitVec 162) ++ (0x3e00ff800003ffe0001ffffffffffc00000000000 : BitVec 162)
def signal327 : W := (0x20004400007d00003fe4040444091000000000000 : BitVec 162) ++ (0x7c00003fe0000000000000000000000 : BitVec 162)
def signal328 : W := (0x2008440102781e003dc0f0e444091008102002102 : BitVec 162) ++ (0x7c1e003fe0f0e000000000000000000 : BitVec 162)
def signal329 : W := (0x21080000007ffe001008400000000000000000000 : BitVec 162) ++ (0x7ffe000000000000000000000000000 : BitVec 162)
def signal330 : W := (0x21080400226fba00377ddda004001000022000022 : BitVec 162) ++ (0x7ffe003fffffe000000000000000000 : BitVec 162)
def signal331 : W := (0x21084421224210002110888000000000000000000 : BitVec 162) ++ (0x0 : BitVec 162)
def signal332 : W := (0x21084421224210002ff7bfe444091089122022922 : BitVec 162) ++ (0x3fffffe000000000000000000 : BitVec 162)
def signal333 : W := (0x21084421225f760001e00fe000091000000022922 : BitVec 162) ++ (0x7ffe0001e00fe000000000000000000 : BitVec 162)
def signal334 : W := (0x21084421225f76002ff7bfe444091089122022922 : BitVec 162) ++ (0x7ffe003fffffe000000000000000000 : BitVec 162)
def signal335 : W := (0x21084421226fba003fffffe444091089122022922 : BitVec 162) ++ (0x7ffe003fffffe000000000000000000 : BitVec 162)
def signal336 : W := (0x210844212277dc003bbeeec040010001100000900 : BitVec 162) ++ (0x7ffe003fffffe000000000000000000 : BitVec 162)
def signal337 : W := (0x210844212277dc003fffffe444091089122022922 : BitVec 162) ++ (0x7ffe003fffffe000000000000000000 : BitVec 162)
def signal338 : W := (0x21084421227afe003ddbfbe444091089122022922 : BitVec 162) ++ (0x7ffe003fffffe000000000000000000 : BitVec 162)
def signal339 : W := (0x21084421227afe003fdffbe444091089122022922 : BitVec 162) ++ (0x7ffe003fffffe000000000000000000 : BitVec 162)
def signal340 : W := (0x21084421227afe003fffffe444091089122022922 : BitVec 162) ++ (0x7ffe003fffffe000000000000000000 : BitVec 162)
def signal341 : W := (0x21084421227ffe001fef7fe444091089122022922 : BitVec 162) ++ (0x7ffe003fffffe000000000000000000 : BitVec 162)
def signal342 : W := (0x21084421227ffe003ddbfbe444091089122022922 : BitVec 162) ++ (0x7ffe003fffffe000000000000000000 : BitVec 162)
def signal343 : W := (0x21084421227ffe003dfbffe444091089122022922 : BitVec 162) ++ (0x7ffe003fffffe000000000000000000 : BitVec 162)
def signal344 : W := (0x21084421227ffe003fffffe444091089122022922 : BitVec 162) ++ (0x7ffe003fffffe000000000000000000 : BitVec 162)
def signal345 : W := (0x21084421227ffe003fffffe6460d18c9132032932 : BitVec 162) ++ (0x7ffe003fffffe000000000000000000 : BitVec 162)
def signal346 : W := (0x21084421227ffe003fffffe6664910c9932422922 : BitVec 162) ++ (0x7ffe003fffffe000000000000000000 : BitVec 162)
def signal347 : W := (0x21084421227ffe303fffffe6664d9cc9932432d33 : BitVec 162) ++ (0x7ffe003fffffe000000000000000000 : BitVec 162)
def signal348 : W := (0x21084421227fffffffffffeccc9b319b366967b66 : BitVec 162) ++ (0x7fffffffffffe000000000000000000 : BitVec 162)
def signal349 : W := (0x21084c31227ffe003fffffe6640d90c9922032d22 : BitVec 162) ++ (0x7ffe003fffffe000000000000000000 : BitVec 162)
def signal350 : W := (0x21084cb1327ffe003fffffe6664d9cc9932432d33 : BitVec 162) ++ (0x7ffe003fffffe000000000000000000 : BitVec 162)
def signal351 : W := (0x21087fbdffc210002110889111204224489288088 : BitVec 162) ++ (0xffffff8000000000000000000000000000000 : BitVec 162)
def signal352 : W := (0x22804c90104500302324040222448c40810410411 : BitVec 162) ++ (0x0 : BitVec 162)
def signal353 : W := (0x22804c90107d00303fe40406664d9c40810410411 : BitVec 162) ++ (0x7c00003fe0000000000000000000000 : BitVec 162)
def signal354 : W := (0x22f84cdd1e781e3e3dc0f0e6664d9f4e9d3cd35d3 : BitVec 162) ++ (0x1f0007c3c7c1e1e3fe0f0e0000003c78f1cf1cf1 : BitVec 162)
def signal355 : W := (0x23884421227ffe303fffffe444091089122022922 : BitVec 162) ++ (0x7ffe003fffffe000000000000000000 : BitVec 162)
def signal356 : W := (0x238844a1327ffe303fffffe446491c89132422933 : BitVec 162) ++ (0x7ffe003fffffe000000000000000000 : BitVec 162)
def signal357 : W := (0x23884cb13247103023348c8222448c40810410411 : BitVec 162) ++ (0x0 : BitVec 162)
def signal358 : W := (0x23884cb1327afe303ddbfbe6664d9cc9932432d33 : BitVec 162) ++ (0x7ffe003fffffe000000000000000000 : BitVec 162)
def signal359 : W := (0x23884cb1327ffe003fffffe444091089122022922 : BitVec 162) ++ (0x7ffe003fffffe000000000000000000 : BitVec 162)
def signal360 : W := (0x23884cb1327ffe303fffffe4440d9c89122032d33 : BitVec 162) ++ (0x7ffe003fffffe000000000000000000 : BitVec 162)
def signal361 : W := (0x23884cb1327ffe303fffffe464499489922422d23 : BitVec 162) ++ (0x7ffe003fffffe000000000000000000 : BitVec 162)
def signal362 : W := (0x23884cb1327ffe303fffffe6664d9cc9932432d33 : BitVec 162) ++ (0x7ffe003fffffe000000000000000000 : BitVec 162)
def signal363 : W := (0x23f84cfd3e47f03e233f8f8222448fc78f1cf1cf1 : BitVec 162) ++ (0x1f0007c3c03e01e001f0f00000003c78f1cf1cf1 : BitVec 162)
def signal364 : W := (0x23f84cfd3e7ffe3e3fffffe6664d9fcf9f3cf3df3 : BitVec 162) ++ (0x1f0007c3c7ffe1e3fffffe0000003c78f1cf1cf1 : BitVec 162)
def signal365 : W := (0x25194421227ffe427fffffec4c193199166066966 : BitVec 162) ++ (0x7ffe003fffffe000000000000000000 : BitVec 162)
def signal366 : W := (0x2519552566ca3242655199be1e3c7bf80fe0fe0fe : BitVec 162) ++ (0x1e1e3c7bf80fe0fe0fe : BitVec 162)
def signal367 : W := (0x2519552566f7dc427bbeeeda5a356b711dc0dc9dc : BitVec 162) ++ (0x7ffe003ffffffe1e3c7bf80fe0fe0fe : BitVec 162)
def signal368 : W := (0x2519552566fffe003ffffff4542952a91aa0aa9aa : BitVec 162) ++ (0x7ffe003fffffe000000000000000000 : BitVec 162)
def signal369 : W := (0x2519552566fffe427ffffffe5e3d7bf91fe0fe9fe : BitVec 162) ++ (0x7ffe003ffffffe1e3c7bf80fe0fe0fe : BitVec 162)
def signal370 : W := (0x292abc5ee26fba84b77dddbba4369376e220dd622 : BitVec 162) ++ (0xf87fc07ffe003fffffffe03f83fff000fff00 : BitVec 162)
def signal371 : W := (0x292ac463227ffe84bfffffecc41b119b322067b22 : BitVec 162) ++ (0x7ffe003fffffe000000000000000000 : BitVec 162)
def signal372 : W := (0x292afc7fe2525484a992aadfe03f83fff000fff00 : BitVec 162) ++ (0xf87fc00000000000001fe03f83fff000fff00 : BitVec 162)
def signal373 : W := (0x292afc7fe27ffe84bfffffffe43f93fff220fff22 : BitVec 162) ++ (0xf87fc07ffe003fffffffe03f83fff000fff00 : BitVec 162)
def signal374 : W := (0x2e80dd90105d00f001e00400003ffc00000010411 : BitVec 162) ++ (0x3e00ff80007c01e001e00000003ffc00000000000 : BitVec 162)
def signal375 : W := (0x2e80dd90105d00f003e40402227ffc40810410411 : BitVec 162) ++ (0x3e00ff80007c01e001e00000003ffc00000000000 : BitVec 162)
def signal376 : W := (0x2e80dd90107d01f01fe4040eeefffc40810410411 : BitVec 162) ++ (0x3e00ff80007c01e03fe0001ffffffc00000000000 : BitVec 162)
def signal377 : W := (0x2e80ff90105d00f02fe40417777ffc40810410411 : BitVec 162) ++ (0x3e00ff80007c01e03fe0001ffffffc00000000000 : BitVec 162)
def signal378 : W := (0x2ec4dd98995d88f901fbf400003fffbf7efb10411 : BitVec 162) ++ (0x3e00ff80007c01e001fff000003fffffffff00000 : BitVec 162)
def signal379 : W := (0x2fbb8042005f76f6c000000000122000000045244 : BitVec 162) ++ (0x3fff0000007fffffc000000000000000000000000 : BitVec 162)
def signal380 : W := (0x2fbb8042007fffffd008400888922112244945244 : BitVec 162) ++ (0x3fff0000007fffffc000000000000000000000000 : BitVec 162)
def signal381 : W := (0x2fbba24a895f76f6ee17b017775222eddbb645244 : BitVec 162) ++ (0x3fff0000007ffffffe1ff01fffc003ffffff00000 : BitVec 162)
def signal382 : W := (0x2fbbddf776c210000100088000204000000088088 : BitVec 162) ++ (0x3fffffffff8000000000000000000000000000000 : BitVec 162)
def signal383 : W := (0x2fbbddf776df76f6c1000880003260000000cd2cc : BitVec 162) ++ (0x3fffffffffffffffc000000000000000000000000 : BitVec 162)
def signal384 : W := (0x2fbbddf776e299091f0f788eeee041dbb76d88088 : BitVec 162) ++ (0x3fffffffff8000003e1ff01fffc003ffffff00000 : BitVec 162)
def signal385 : W := (0x2fbbffffffc210002110889111204224489288088 : BitVec 162) ++ (0x3fffffffff8000000000000000000000000000000 : BitVec 162)
def signal386 : W := (0x314c4421227fff093fffffeccc89119b366922922 : BitVec 162) ++ (0x7ffe003fffffe000000000000000000 : BitVec 162)
def signal387 : W := (0x314c6629ab5f770901e00ffbbbc91376eddf22922 : BitVec 162) ++ (0x7ffe0001e00fffffc003ffffff00000 : BitVec 162)
def signal388 : W := (0x314c6629ab6299093f1ff89fffc003ffffff00000 : BitVec 162) ++ (0x3e1ff01fffc003ffffff00000 : BitVec 162)
def signal389 : W := (0x314c6629ab7ffe003ffffff5550912ad5ab222922 : BitVec 162) ++ (0x7ffe003fffffe000000000000000000 : BitVec 162)
def signal390 : W := (0x314c6629ab7fff093fffffffffc913ffffff22922 : BitVec 162) ++ (0x7ffe003fffffffffc003ffffff00000 : BitVec 162)
def signal391 : W := (0x36800780106d0170376404001fc07c00010400011 : BitVec 162) ++ (0x3e000780007c01e03fe000001fc07c00000000000 : BitVec 162)
def signal392 : W := (0x36800f90106d0170376404023fc4fc40810410411 : BitVec 162) ++ (0x3e000780007c01e03fe000001fc07c00000000000 : BitVec 162)
def signal393 : W := (0x36807f90106d01703fe404177fedfc40810410411 : BitVec 162) ++ (0x3e00ff80007c01e03fe0001ffffffc00000000000 : BitVec 162)
def signal394 : W := (0x36a207efd06d4574b76626401fc07fbf7104efb11 : BitVec 162) ++ (0x3e0007ffc07c01e03fe000001fc07ffff000fff00 : BitVec 162)
def signal395 : W := (0x37dd0000006fbb7b5008400008802000044900044 : BitVec 162) ++ (0x3fff0000007fffffc000000000000000000000000 : BitVec 162)
def signal396 : W := (0x37dd0400226fbb7b777ddda00c803000066900066 : BitVec 162) ++ (0x3fff0000007fffffffffffe000000000000000000 : BitVec 162)
def signal397 : W := (0x37dd07803fc210002110888011004000089200088 : BitVec 162) ++ (0x3fff07803f8000000000000000000000000000000 : BitVec 162)
def signal398 : W := (0x37dd07803fd25484a992aacef11fc1dbb89277f88 : BitVec 162) ++ (0x3fff07803f8000000000001fe03f83fff000fff00 : BitVec 162)
def signal399 : W := (0x37dd783dc06fbb7b588a625768ada2edd449bad44 : BitVec 162) ++ (0x3ffff87fc07fffffc000001fe03f83fff000fff00 : BitVec 162)
def signal400 : W := (0x37dd7fbdffc210002110889111204224489288088 : BitVec 162) ++ (0x3fffffffff8000000000000000000000000000000 : BitVec 162)
def signal401 : W := (0x3a80ee90107501b03ba40401e1c38400800400401 : BitVec 162) ++ (0x3e00ff80007c01e03fe00001e1c38400000000000 : BitVec 162)
def signal402 : W := (0x3a80ee90107501b03ba40403e3c78c40810410411 : BitVec 162) ++ (0x3e00ff80007c01e03fe00001e1c38400000000000 : BitVec 162)
def signal403 : W := (0x3a80ee90107d01f03fe4040fefdfbc40810410411 : BitVec 162) ++ (0x3e00ff80007c01e03fe0001ffffffc00000000000 : BitVec 162)
def signal404 : W := (0x3a80ff90107501b03fe40417f7efdc40810410411 : BitVec 162) ++ (0x3e00ff80007c01e03fe0001ffffffc00000000000 : BitVec 162)
def signal405 : W := (0x3a91ee9454f523b27ba51521e1c387b88ee4ee4ef : BitVec 162) ++ (0x3e00ff80007c01e03fe00001e1c387f80fe0fe0fe : BitVec 162)
def signal406 : W := (0x3bee80420077ddbd9008400080820002200901200 : BitVec 162) ++ (0x3fff0000007fffffc000000000000000000000000 : BitVec 162)
def signal407 : W := (0x3bee8042007fffffd008400888922112244945244 : BitVec 162) ++ (0x3fff0000007fffffc000000000000000000000000 : BitVec 162)
def signal408 : W := (0x3bee914644f7ddbd9449513696ae5aea2ba9bb2ba : BitVec 162) ++ (0x3fff0000007fffffc000001e1e3c7bf80fe0fe0fe : BitVec 162)
def signal409 : W := (0x3beeeefbbb4210002110888101000004401200000 : BitVec 162) ++ (0x3fffffffff8000000000000000000000000000000 : BitVec 162)
def signal410 : W := (0x3beeeefbbb4a3242655199af0f1c39dc477276076 : BitVec 162) ++ (0x3fffffffff8000000000001e1e3c7bf80fe0fe0fe : BitVec 162)
def signal411 : W := (0x3beeffffffc210002110889111204224489288088 : BitVec 162) ++ (0x3fffffffff8000000000000000000000000000000 : BitVec 162)
def signal412 : W := (0x3c00f700007801c03dc0001dddbb7000000000000 : BitVec 162) ++ (0x3e00ff80007c01e03fe0001ffffffc00000000000 : BitVec 162)
def signal413 : W := (0x3c01f70040f803c07dc0103dddbb703800e00e00e : BitVec 162) ++ (0x3e00ff80007c01e03fe0001ffffffc3800e00e00e : BitVec 162)
def signal414 : W := (0x3c02f703c07805c0bdc0205dddbb703870000e300 : BitVec 162) ++ (0x3e00ff83c07c01e03fe0001ffffffc3870000e300 : BitVec 162)
def signal415 : W := (0x3c04f700817809c13dc0f01dddbb703870e300000 : BitVec 162) ++ (0x3e00ff80007c01e03fe0f01ffffffc3870e300000 : BitVec 162)
def signal416 : W := (0x3c08f70102781fc03dc0f0fdddbb7008102002102 : BitVec 162) ++ (0x3e00ff80007c1fe03fe0f0fffffffc00000000000 : BitVec 162)
def signal417 : W := (0x3c0f800200781fc1d000400888922010204104204 : BitVec 162) ++ (0x3e0f0000007c1fe1c000000000000000000000000 : BitVec 162)
def signal418 : W := (0x3c0f88be3c781fc1d2374f0aaad6aed5ab55b4eb5 : BitVec 162) ++ (0x3e0f007c3c7c1fe1c01f0f00000003c78f1cf1cf1 : BitVec 162)
def signal419 : W := (0x3c0ff70200781fc1fdc0401dddbb7010204104204 : BitVec 162) ++ (0x3e0fff80007c1fe1ffe0001ffffffc00000000000 : BitVec 162)
def signal420 : W := (0x3c0ff703c3c010002100809111204020408208008 : BitVec 162) ++ (0x3e0fff83c38000000000000000000000000000000 : BitVec 162)
def signal421 : W := (0x3c0ff703c3c5f03e232f87933364cde3c78e79c79 : BitVec 162) ++ (0x3e0fff83c383e01e001f0f00000003c78f1cf1cf1 : BitVec 162)
def signal422 : W := (0x3c0ff703c3f811c03dc0809dddbb7020408208008 : BitVec 162) ++ (0x3e0fff83c3fc01e03fe0001ffffffc00000000000 : BitVec 162)
def signal423 : W := (0x3d70f76c2c7ae1ce3ddb0b1dddbb73870e18e18e0 : BitVec 162) ++ (0x3ff0fffc3c7fe1fe3fff0f1fffffffc78f1cf1cf1 : BitVec 162)
def signal424 : W := (0x3d7f8042007affcfd008400888922112244945244 : BitVec 162) ++ (0x3fff0000007fffffc000000000000000000000000 : BitVec 162)
def signal425 : W := (0x3d7f8042007fffcfd008400888922112244945244 : BitVec 162) ++ (0x3fff0000007fffffc000000000000000000000000 : BitVec 162)
def signal426 : W := (0x3d7f8042007fffffd008400888922112244945244 : BitVec 162) ++ (0x3fff0000007fffffc000000000000000000000000 : BitVec 162)
def signal427 : W := (0x3d7f88d2107affcfd22c440aaad6ad52a54d55655 : BitVec 162) ++ (0x3fff0000007fffffc000000000000000000000000 : BitVec 162)
def signal428 : W := (0x3d7ff76fefc210002110889111204224489288088 : BitVec 162) ++ (0x3fffffffff8000000000000000000000000000000 : BitVec 162)
def signal429 : W := (0x3d7ff76fefc7103023348c933364ce64c99698499 : BitVec 162) ++ (0x3fffffffff8000000000000000000000000000000 : BitVec 162)
def signal430 : W := (0x3d7fff7fefc210002110889111204224489288088 : BitVec 162) ++ (0x3fffffffff8000000000000000000000000000000 : BitVec 162)
def signal431 : W := (0x3d7fffffffc210002110889111204224489288088 : BitVec 162) ++ (0x3fffffffff8000000000000000000000000000000 : BitVec 162)
def signal432 : W := (0x3e808000007d01f01000000888922000000000000 : BitVec 162) ++ (0x3e000000007c01e00000000000000000000000000 : BitVec 162)
def signal433 : W := (0x3e808890107d01f01224040aaad6ac40810410411 : BitVec 162) ++ (0x3e000000007c01e00000000000000000000000000 : BitVec 162)
def signal434 : W := (0x3e80bf90106d01f03764041bbff6fc40810410411 : BitVec 162) ++ (0x3e00ff80007c01e03fe0001ffffffc00000000000 : BitVec 162)
def signal435 : W := (0x3e80ff90104000002100001111204000000000000 : BitVec 162) ++ (0x3e00ff80000000000000000000000000000000000 : BitVec 162)
def signal436 : W := (0x3e80ff9010450030232404133364cc40810410411 : BitVec 162) ++ (0x3e00ff80000000000000000000000000000000000 : BitVec 162)
def signal437 : W := (0x3e80ff90107501f03ba4041bfbf7ec40810410411 : BitVec 162) ++ (0x3e00ff80007c01e03fe0001ffffffc00000000000 : BitVec 162)
def signal438 : W := (0x3e80ff90107d01f03fe4041ffffffc40810410411 : BitVec 162) ++ (0x3e00ff80007c01e03fe0001ffffffc00000000000 : BitVec 162)
def signal439 : W := (0x3e80ff90107d23f03fe5153ffffffcc8832432433 : BitVec 162) ++ (0x3e00ff80007c01e03fe0001ffffffc00000000000 : BitVec 162)
def signal440 : W := (0x3e80ffb1107d45f03fe6265ffffffcc9910432d11 : BitVec 162) ++ (0x3e00ff80007c01e03fe0001ffffffc00000000000 : BitVec 162)
def signal441 : W := (0x3e81ff9050fd03f07fe4143ffffffc7881e41e41f : BitVec 162) ++ (0x3e00ff80007c01e03fe0001ffffffc3800e00e00e : BitVec 162)
def signal442 : W := (0x3e82ff93d07d05f0bfe4245ffffffc78f1041e711 : BitVec 162) ++ (0x3e00ff83c07c01e03fe0001ffffffc3870000e300 : BitVec 162)
def signal443 : W := (0x3e84ff90917d09f13fe4f41ffffffc78f1e710411 : BitVec 162) ++ (0x3e00ff80007c01e03fe0f01ffffffc3870e300000 : BitVec 162)
def signal444 : W := (0x3e88ff91127d1ff03fe4f4fffffffc48912412513 : BitVec 162) ++ (0x3e00ff80007c1fe03fe0f0fffffffc00000000000 : BitVec 162)
def signal445 : W := (0x3e8fff92107d1ff1ffe4441ffffffc50a14514615 : BitVec 162) ++ (0x3e0fff80007c1fe1ffe0001ffffffc00000000000 : BitVec 162)
def signal446 : W := (0x3e8fff93d3fd11f03fe4849ffffffc60c18618419 : BitVec 162) ++ (0x3e0fff83c3fc01e03fe0001ffffffc00000000000 : BitVec 162)
def signal447 : W := (0x3e91ff90107d23f27fe4041ffffffd50854454455 : BitVec 162) ++ (0x3e00ff80007c01e03fe0001ffffffc00000000000 : BitVec 162)
def signal448 : W := (0x3e91ff9454fd01f03fe4041ffffffe60898498499 : BitVec 162) ++ (0x3e00ff80007c01e03fe0001ffffffc00000000000 : BitVec 162)
def signal449 : W := (0x3e91ff9454fd23f27fe5153ffffffff88fe4fe4ff : BitVec 162) ++ (0x3e00ff80007c01e03fe0001ffffffff80fe0fe0fe : BitVec 162)
def signal450 : W := (0x3ea2ffd2107d45f4bfe4041ffffffd52a10455611 : BitVec 162) ++ (0x3e00ff80007c01e03fe0001ffffffc00000000000 : BitVec 162)
def signal451 : W := (0x3ea2ffffd07d45f4bfe6265ffffffffff104fff11 : BitVec 162) ++ (0x3e00ffffc07c01e03fe0001ffffffffff000fff00 : BitVec 162)
def signal452 : W := (0x3ec4ff90107d89f93fec441ffffffd52a54d10411 : BitVec 162) ++ (0x3e00ff80007c01e03fe0001ffffffc00000000000 : BitVec 162)
def signal453 : W := (0x3ec4ff98997d01f03ff4841ffffffe64c99610411 : BitVec 162) ++ (0x3e00ff80007c01e03fe0001ffffffc00000000000 : BitVec 162)
def signal454 : W := (0x3ec4ff98997d89f93ffff41fffffffffffff10411 : BitVec 162) ++ (0x3e00ff80007c01e03ffff01fffffffffffff00000 : BitVec 162)
def signal455 : W := (0x3f88ffb1327f11f03ff48c9ffffffc40810410411 : BitVec 162) ++ (0x3e00ff80007c01e03fe0001ffffffc00000000000 : BitVec 162)
def signal456 : W := (0x3f88ffb1327ffff03ffffffffffffcc9932432d33 : BitVec 162) ++ (0x3e00ff80007fffe03ffffffffffffc00000000000 : BitVec 162)
def signal457 : W := (0x3ff0fffc3c7fe1fe3fff0f1fffffffc78f1cf1cf1 : BitVec 162) ++ (0x3ff0fffc3c7fe1fe3fff0f1fffffffc78f1cf1cf1 : BitVec 162)
def signal458 : W := (0x3fff8042004210000000000000000000000000000 : BitVec 162) ++ (0x3fff0000000000000000000000000000000000000 : BitVec 162)
def signal459 : W := (0x3fff8042006fbbffd008400888922112244945244 : BitVec 162) ++ (0x3fff0000007fffffc000000000000000000000000 : BitVec 162)
def signal460 : W := (0x3fff80420077ddffd008400888922112244945244 : BitVec 162) ++ (0x3fff0000007fffffc000000000000000000000000 : BitVec 162)
def signal461 : W := (0x3fff8042007affcfd008400888922112244945244 : BitVec 162) ++ (0x3fff0000007fffffc000000000000000000000000 : BitVec 162)
def signal462 : W := (0x3fff8042007affffd008400888922112244945244 : BitVec 162) ++ (0x3fff0000007fffffc000000000000000000000000 : BitVec 162)
def signal463 : W := (0x3fff8042007fffffd008400888922112244945244 : BitVec 162) ++ (0x3fff0000007fffffc000000000000000000000000 : BitVec 162)
def signal464 : W := (0x3fff8042007fffffd008400a8a962952254955254 : BitVec 162) ++ (0x3fff0000007fffffc000000000000000000000000 : BitVec 162)
def signal465 : W := (0x3fff8042007fffffd20c400aaad22152a54d45244 : BitVec 162) ++ (0x3fff0000007fffffc000000000000000000000000 : BitVec 162)
def signal466 : W := (0x3fff8042007fffffd22c440888922112244945244 : BitVec 162) ++ (0x3fff0000007fffffc000000000000000000000000 : BitVec 162)
def signal467 : W := (0x3fff8042007fffffd22c440aaad6ad52a54d55655 : BitVec 162) ++ (0x3fff0000007fffffc000000000000000000000000 : BitVec 162)
def signal468 : W := (0x3fff8042007fffffd449512c8c9a319a266967266 : BitVec 162) ++ (0x3fff0000007fffffc000000000000000000000000 : BitVec 162)
def signal469 : W := (0x3fff80c2107fffffd22c44088ad22d12254d45255 : BitVec 162) ++ (0x3fff0000007fffffc000000000000000000000000 : BitVec 162)
def signal470 : W := (0x3fff87c23ffffffff118c888999261122cdb452cc : BitVec 162) ++ (0x3fff07803fffffffc000000000000000000000000 : BitVec 162)
def signal471 : W := (0x3fff8852007fffffd008400aa896a152a44955644 : BitVec 162) ++ (0x3fff0000007fffffc000000000000000000000000 : BitVec 162)
def signal472 : W := (0x3fff88d2107fffffd008400888922112244945244 : BitVec 162) ++ (0x3fff0000007fffffc000000000000000000000000 : BitVec 162)
def signal473 : W := (0x3fff88d2107fffffd008400aaad6ad52a54d55655 : BitVec 162) ++ (0x3fff0000007fffffc000000000000000000000000 : BitVec 162)
def signal474 : W := (0x3fff88d2107fffffd02844088896ad12244955655 : BitVec 162) ++ (0x3fff0000007fffffc000000000000000000000000 : BitVec 162)
def signal475 : W := (0x3fff88d2107fffffd22c4408a8d2a512a44d45645 : BitVec 162) ++ (0x3fff0000007fffffc000000000000000000000000 : BitVec 162)
def signal476 : W := (0x3fff88d2107fffffd22c440aaad6ad52a54d55655 : BitVec 162) ++ (0x3fff0000007fffffc000000000000000000000000 : BitVec 162)
def signal477 : W := (0x3fff88fe3c7fffffd23f4f0aaad6afd7af5df5ef5 : BitVec 162) ++ (0x3fff007c3c7fffffc01f0f00000003c78f1cf1cf1 : BitVec 162)
def signal478 : W := (0x3fff914644ffffffd008401898b263322cc9cd2cc : BitVec 162) ++ (0x3fff0000007fffffc000000000000000000000000 : BitVec 162)
def signal479 : W := (0x3fff914644ffffffd449513e9ebe7bfa2fe9ff2fe : BitVec 162) ++ (0x3fff0000007fffffc000001e1e3c7bf80fe0fe0fe : BitVec 162)
def signal480 : W := (0x3fffa24a897ffffff018c019999223366cdb45244 : BitVec 162) ++ (0x3fff0000007fffffc000000000000000000000000 : BitVec 162)
def signal481 : W := (0x3fffa24a897ffffffe1ff01fffd223ffffff45244 : BitVec 162) ++ (0x3fff0000007ffffffe1ff01fffc003ffffff00000 : BitVec 162)
def signal482 : W := (0x3fffbfdeffc210002110889111204224489288088 : BitVec 162) ++ (0x3fffffffff8000000000000000000000000000000 : BitVec 162)
def signal483 : W := (0x3fffc063007fffffd88a624cc89b219b344967b44 : BitVec 162) ++ (0x3fff0000007fffffc000000000000000000000000 : BitVec 162)
def signal484 : W := (0x3fffc463227fffffd1e84fe8889b3112244967b66 : BitVec 162) ++ (0x3fff0000007fffffc1e00fe000000000000000000 : BitVec 162)
def signal485 : W := (0x3fffc463227ffffff118c88888922112244945244 : BitVec 162) ++ (0x3fff0000007fffffc000000000000000000000000 : BitVec 162)
def signal486 : W := (0x3fffc463227fffffffffffeccc9b319b366967b66 : BitVec 162) ++ (0x3fff0000007fffffffffffe000000000000000000 : BitVec 162)
def signal487 : W := (0x3ffff76fefc210002110889111204224489288088 : BitVec 162) ++ (0x3fffffffff8000000000000000000000000000000 : BitVec 162)
def signal488 : W := (0x3ffff7efffc210002110889111204224489288088 : BitVec 162) ++ (0x3fffffffff8000000000000000000000000000000 : BitVec 162)
def signal489 : W := (0x3ffff87fc07fffffd88a625fe8bfa3fff449fff44 : BitVec 162) ++ (0x3ffff87fc07fffffc000001fe03f83fff000fff00 : BitVec 162)
def signal490 : W := (0x3fffffd2107fffffffec441ffffffd52a54d55655 : BitVec 162) ++ (0x3fffff80007fffffffe0001ffffffc00000000000 : BitVec 162)
def signal491 : W := (0x3fffffffffc210002110889111204224489288088 : BitVec 162) ++ (0x3fffffffff8000000000000000000000000000000 : BitVec 162)
def signal492 : W := (0x3fffffffffc210002110889313244a64499298098 : BitVec 162) ++ (0x3fffffffff8000000000000000000000000000000 : BitVec 162)
def signal493 : W := (0x3fffffffffc21000211088933124c264c89298488 : BitVec 162) ++ (0x3fffffffff8000000000000000000000000000000 : BitVec 162)
def signal494 : W := (0x3fffffffffc210002314889333604264c99688088 : BitVec 162) ++ (0x3fffffffff8000000000000000000000000000000 : BitVec 162)
def signal495 : W := (0x3fffffffffc2100023348c933364ce64c99698499 : BitVec 162) ++ (0x3fffffffff8000000000000000000000000000000 : BitVec 162)
def signal496 : W := (0x3fffffffffc21030211088933364ce64c99698499 : BitVec 162) ++ (0x3fffffffff8000000000000000000000000000000 : BitVec 162)
def signal497 : W := (0x3fffffffffc211ffe110889999b263366cdbcd2cc : BitVec 162) ++ (0x3fffffffff8001ffc000000000000000000000000 : BitVec 162)
def signal498 : W := (0x3fffffffffc7100023348c9111204224489288088 : BitVec 162) ++ (0x3fffffffff8000000000000000000000000000000 : BitVec 162)
def signal499 : W := (0x3fffffffffc710302110889111204224489288088 : BitVec 162) ++ (0x3fffffffff8000000000000000000000000000000 : BitVec 162)
def signal500 : W := (0x3fffffffffc7103021308c911124ce24489298499 : BitVec 162) ++ (0x3fffffffff8000000000000000000000000000000 : BitVec 162)
def signal501 : W := (0x3fffffffffc7103023348c9113604e24499688099 : BitVec 162) ++ (0x3fffffffff8000000000000000000000000000000 : BitVec 162)
def signal502 : W := (0x3fffffffffc7103023348c913160c624c89688489 : BitVec 162) ++ (0x3fffffffff8000000000000000000000000000000 : BitVec 162)
def signal503 : W := (0x3fffffffffc7103023348c933364ce64c99698499 : BitVec 162) ++ (0x3fffffffff8000000000000000000000000000000 : BitVec 162)
def signal504 : W := (0x3fffffffffc7f03e233f8f933364cfe7cf9ef9cf9 : BitVec 162) ++ (0x3fffffffff83e01e001f0f00000003c78f1cf1cf1 : BitVec 162)
def signal505 : W := (0x3fffffffffca3200255199b5152852ac4ab2aa0aa : BitVec 162) ++ (0x3fffffffff8000000000000000000000000000000 : BitVec 162)
def signal506 : W := (0x3fffffffffca324261108899193063344cd2cc0cc : BitVec 162) ++ (0x3fffffffff8000000000000000000000000000000 : BitVec 162)
def signal507 : W := (0x3fffffffffca3242655199bf1f3c7bfc4ff2fe0fe : BitVec 162) ++ (0x3fffffffff8000000000001e1e3c7bf80fe0fe0fe : BitVec 162)
def signal508 : W := (0x3fffffffffd254002992aad5512942ad5892aa988 : BitVec 162) ++ (0x3fffffffff8000000000000000000000000000000 : BitVec 162)
def signal509 : W := (0x3fffffffffd25484a1108899913243366892cd288 : BitVec 162) ++ (0x3fffffffff8000000000000000000000000000000 : BitVec 162)
def signal510 : W := (0x3fffffffffd25484a992aadff13fc3fff892fff88 : BitVec 162) ++ (0x3fffffffff8000000000001fe03f83fff000fff00 : BitVec 162)
def signal511 : W := (0x3fffffffffe299093118c89999a043366cdb88088 : BitVec 162) ++ (0x3fffffffff8000000000000000000000000000000 : BitVec 162)
def signal512 : W := (0x3fffffffffe299093f1ff89fffe043ffffff88088 : BitVec 162) ++ (0x3fffffffff8000003e1ff01fffc003ffffff00000 : BitVec 162)
def signal513 : W := (0x3fffffffffff11f03ff48c9ffffffe64c99698499 : BitVec 162) ++ (0x3ffffffffffc01e03fe0001ffffffc00000000000 : BitVec 162)
def signal514 : W := (0x3ffffffffffffe003ffffff5552952ad5ab2aa9aa : BitVec 162) ++ (0x3ffffffffffffe003fffffe000000000000000000 : BitVec 162)
def signal515 : W := (0x3ffffffffffffffff118c89999b263366cdbcd2cc : BitVec 162) ++ (0x3fffffffffffffffc000000000000000000000000 : BitVec 162)
def ins : List W := [signal94,signal122,signal182,signal260,signal438,signal344,signal463,signal491]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
def layer0 : BinaryTree (List W) := .nil
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok0 : everyKey (fun q => !doneTest q) layer0=true := by decide +kernel
theorem closed0 : Closed 0 layer0 := closed_nil _ ok0
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
def layer1 : BinaryTree (List W) := .nil
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok1 : everyKey (rowOK 0 layer0) layer1=true := by decide +kernel
theorem closed1 : Closed 1 layer1 := closed_next 0 (by decide) _ _ closed0 ok1
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
def layer2 : BinaryTree (List W) := .nil
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok2 : everyKey (rowOK 1 layer1) layer2=true := by decide +kernel
theorem closed2 : Closed 2 layer2 := closed_next 1 (by decide) _ _ closed1 ok2
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
def layer3 : BinaryTree (List W) := .nil
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok3 : everyKey (rowOK 2 layer2) layer3=true := by decide +kernel
theorem closed3 : Closed 3 layer3 := closed_next 2 (by decide) _ _ closed2 ok3
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
def layer4 : BinaryTree (List W) := (.node [signal225,signal309,signal362,signal463,signal491] (.node [signal224,signal310,signal344,signal476,signal491] (.node [signal224,signal310,signal344,signal463,signal503] (.node [signal224,signal309,signal362,signal463,signal503] .nil .nil) .nil) (.node [signal225,signal309,signal344,signal476,signal491] .nil .nil)) (.node [signal225,signal310,signal344,signal476,signal491] (.node [signal225,signal310,signal344,signal463,signal503] .nil .nil) (.node [signal225,signal310,signal362,signal463,signal491] .nil .nil)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok4 : everyKey (rowOK 3 layer3) layer4=true := by decide +kernel
theorem closed4 : Closed 4 layer4 := closed_next 3 (by decide) _ _ closed3 ok4
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
def layer5 : BinaryTree (List W) := (.node [signal122,signal187,signal260,signal362,signal463,signal491] (.node [signal117,signal182,signal289,signal344,signal463,signal503] (.node [signal53,signal216,signal260,signal344,signal463,signal491] (.node [signal53,signal182,signal260,signal367,signal463,signal491] (.node [signal53,signal122,signal260,signal344,signal399,signal491] (.node [signal53,signal122,signal182,signal344,signal381,signal491] (.node [signal53,signal122,signal182,signal260,signal324,signal463] (.node [signal27,signal53,signal122,signal182,signal260,signal344] .nil .nil) (.node [signal53,signal122,signal182,signal260,signal325,signal491] .nil .nil)) (.node [signal53,signal122,signal182,signal387,signal463,signal491] (.node [signal53,signal122,signal182,signal344,signal384,signal463] .nil .nil) (.node [signal53,signal122,signal260,signal344,signal398,signal463] .nil .nil))) (.node [signal53,signal182,signal260,signal344,signal408,signal491] (.node [signal53,signal122,signal312,signal344,signal463,signal491] (.node [signal53,signal122,signal260,signal370,signal463,signal491] .nil .nil) (.node [signal53,signal129,signal316,signal344,signal463,signal491] .nil .nil)) (.node [signal53,signal182,signal260,signal366,signal463,signal514] (.node [signal53,signal182,signal260,signal344,signal410,signal463] .nil .nil) .nil))) (.node [signal53,signal182,signal309,signal344,signal468,signal491] (.node [signal53,signal182,signal304,signal344,signal463,signal491] (.node [signal53,signal182,signal260,signal369,signal463,signal505] (.node [signal53,signal182,signal260,signal368,signal463,signal507] .nil .nil) (.node [signal53,signal182,signal303,signal344,signal463,signal491] .nil .nil)) (.node [signal53,signal182,signal309,signal344,signal463,signal505] (.node [signal53,signal182,signal305,signal344,signal463,signal491] .nil .nil) .nil)) (.node [signal53,signal191,signal309,signal344,signal463,signal491] (.node [signal53,signal188,signal309,signal344,signal463,signal491] (.node [signal53,signal185,signal309,signal344,signal463,signal491] .nil .nil) (.node [signal53,signal189,signal309,signal344,signal463,signal491] .nil .nil)) (.node [signal53,signal215,signal260,signal344,signal463,signal491] (.node [signal53,signal214,signal260,signal344,signal463,signal491] .nil .nil) .nil)))) (.node [signal53,signal224,signal309,signal338,signal463,signal491] (.node [signal53,signal224,signal269,signal344,signal463,signal491] (.node [signal53,signal223,signal309,signal344,signal463,signal491] (.node [signal53,signal218,signal309,signal344,signal463,signal491] (.node [signal53,signal217,signal309,signal344,signal463,signal491] .nil .nil) (.node [signal53,signal223,signal308,signal344,signal463,signal491] .nil .nil)) (.node [signal53,signal224,signal260,signal368,signal463,signal491] (.node [signal53,signal224,signal260,signal344,signal478,signal491] .nil .nil) .nil)) (.node [signal53,signal224,signal306,signal344,signal463,signal491] (.node [signal53,signal224,signal301,signal344,signal463,signal491] (.node [signal53,signal224,signal270,signal344,signal463,signal491] .nil .nil) (.node [signal53,signal224,signal302,signal344,signal463,signal491] .nil .nil)) (.node [signal53,signal224,signal308,signal344,signal463,signal491] (.node [signal53,signal224,signal307,signal344,signal463,signal491] .nil .nil) .nil))) (.node [signal53,signal224,signal310,signal344,signal463,signal491] (.node [signal53,signal224,signal309,signal344,signal463,signal503] (.node [signal53,signal224,signal309,signal344,signal428,signal463] (.node [signal53,signal224,signal309,signal344,signal424,signal491] .nil .nil) (.node [signal53,signal224,signal309,signal344,signal463,signal491] .nil .nil)) (.node [signal53,signal224,signal309,signal362,signal463,signal491] (.node [signal53,signal224,signal309,signal344,signal476,signal491] .nil .nil) .nil)) (.node [signal57,signal182,signal309,signal344,signal463,signal491] (.node [signal53,signal225,signal310,signal344,signal463,signal491] (.node [signal53,signal225,signal309,signal344,signal463,signal491] .nil .nil) (.node [signal57,signal182,signal260,signal369,signal463,signal491] .nil .nil)) (.node [signal117,signal182,signal260,signal362,signal463,signal503] (.node [signal62,signal122,signal260,signal373,signal463,signal491] .nil .nil) .nil))))) (.node [signal122,signal182,signal281,signal344,signal463,signal512] (.node [signal122,signal182,signal260,signal357,signal463,signal514] (.node [signal122,signal167,signal260,signal362,signal463,signal503] (.node [signal122,signal159,signal260,signal362,signal463,signal503] (.node [signal117,signal207,signal260,signal344,signal476,signal491] (.node [signal117,signal182,signal289,signal344,signal476,signal491] .nil .nil) (.node [signal117,signal207,signal260,signal362,signal463,signal491] .nil .nil)) (.node [signal122,signal159,signal289,signal344,signal476,signal491] (.node [signal122,signal159,signal289,signal344,signal463,signal503] .nil .nil) .nil)) (.node [signal122,signal182,signal246,signal362,signal463,signal503] (.node [signal122,signal167,signal289,signal344,signal476,signal491] (.node [signal122,signal167,signal289,signal344,signal463,signal503] .nil .nil) (.node [signal122,signal182,signal238,signal362,signal463,signal503] .nil .nil)) (.node [signal122,signal182,signal260,signal344,signal429,signal463] (.node [signal122,signal182,signal260,signal344,signal427,signal491] .nil .nil) .nil))) (.node [signal122,signal182,signal260,signal362,signal463,signal501] (.node [signal122,signal182,signal260,signal361,signal463,signal503] (.node [signal122,signal182,signal260,signal359,signal463,signal503] (.node [signal122,signal182,signal260,signal358,signal463,signal491] .nil .nil) (.node [signal122,signal182,signal260,signal360,signal463,signal503] .nil .nil)) (.node [signal122,signal182,signal260,signal362,signal463,signal498] (.node [signal122,signal182,signal260,signal362,signal424,signal503] .nil .nil) .nil)) (.node [signal122,signal182,signal278,signal344,signal481,signal491] (.node [signal122,signal182,signal260,signal362,signal463,signal503] (.node [signal122,signal182,signal260,signal362,signal463,signal502] .nil .nil) (.node [signal122,signal182,signal260,signal362,signal476,signal503] .nil .nil)) (.node [signal122,signal182,signal280,signal344,signal476,signal491] (.node [signal122,signal182,signal279,signal344,signal476,signal491] .nil .nil) .nil)))) (.node [signal122,signal182,signal289,signal344,signal428,signal476] (.node [signal122,signal182,signal286,signal344,signal476,signal491] (.node [signal122,signal182,signal285,signal344,signal463,signal503] (.node [signal122,signal182,signal283,signal344,signal463,signal503] (.node [signal122,signal182,signal282,signal344,signal463,signal503] .nil .nil) (.node [signal122,signal182,signal284,signal344,signal463,signal491] .nil .nil)) (.node [signal122,signal182,signal286,signal344,signal463,signal503] (.node [signal122,signal182,signal285,signal344,signal476,signal491] .nil .nil) .nil)) (.node [signal122,signal182,signal289,signal338,signal463,signal503] (.node [signal122,signal182,signal288,signal344,signal463,signal503] (.node [signal122,signal182,signal287,signal344,signal463,signal491] .nil .nil) (.node [signal122,signal182,signal288,signal344,signal476,signal491] .nil .nil)) (.node [signal122,signal182,signal289,signal344,signal424,signal503] (.node [signal122,signal182,signal289,signal338,signal476,signal491] .nil .nil) .nil))) (.node [signal122,signal182,signal289,signal344,signal476,signal503] (.node [signal122,signal182,signal289,signal344,signal465,signal491] (.node [signal122,signal182,signal289,signal344,signal463,signal495] (.node [signal122,signal182,signal289,signal344,signal463,signal494] .nil .nil) (.node [signal122,signal182,signal289,signal344,signal463,signal503] .nil .nil)) (.node [signal122,signal182,signal289,signal344,signal476,signal491] (.node [signal122,signal182,signal289,signal344,signal467,signal491] .nil .nil) .nil)) (.node [signal122,signal182,signal310,signal344,signal463,signal503] (.node [signal122,signal182,signal289,signal362,signal476,signal491] (.node [signal122,signal182,signal289,signal362,signal463,signal503] .nil .nil) (.node [signal122,signal182,signal309,signal362,signal463,signal503] .nil .nil)) (.node [signal122,signal186,signal260,signal362,signal463,signal491] (.node [signal122,signal182,signal310,signal344,signal476,signal491] .nil .nil) .nil)))))) (.node [signal142,signal159,signal260,signal362,signal463,signal491] (.node [signal122,signal207,signal289,signal344,signal463,signal503] (.node [signal122,signal207,signal246,signal362,signal463,signal491] (.node [signal122,signal202,signal260,signal344,signal476,signal491] (.node [signal122,signal199,signal260,signal362,signal463,signal491] (.node [signal122,signal198,signal260,signal344,signal463,signal491] (.node [signal122,signal197,signal260,signal344,signal489,signal491] .nil .nil) (.node [signal122,signal199,signal260,signal344,signal476,signal491] .nil .nil)) (.node [signal122,signal200,signal260,signal362,signal463,signal491] (.node [signal122,signal200,signal260,signal344,signal476,signal491] .nil .nil) (.node [signal122,signal201,signal260,signal344,signal463,signal491] .nil .nil))) (.node [signal122,signal207,signal238,signal344,signal476,signal491] (.node [signal122,signal206,signal260,signal344,signal476,signal491] (.node [signal122,signal205,signal260,signal344,signal476,signal491] .nil .nil) (.node [signal122,signal206,signal260,signal362,signal463,signal491] .nil .nil)) (.node [signal122,signal207,signal246,signal344,signal476,signal491] (.node [signal122,signal207,signal238,signal362,signal463,signal491] .nil .nil) .nil))) (.node [signal122,signal207,signal260,signal349,signal463,signal491] (.node [signal122,signal207,signal260,signal344,signal473,signal491] (.node [signal122,signal207,signal260,signal344,signal428,signal476] (.node [signal122,signal207,signal260,signal338,signal476,signal491] .nil .nil) (.node [signal122,signal207,signal260,signal344,signal471,signal491] .nil .nil)) (.node [signal122,signal207,signal260,signal344,signal476,signal503] (.node [signal122,signal207,signal260,signal344,signal476,signal491] .nil .nil) .nil)) (.node [signal122,signal207,signal260,signal362,signal463,signal491] (.node [signal122,signal207,signal260,signal362,signal424,signal491] (.node [signal122,signal207,signal260,signal350,signal463,signal491] .nil .nil) (.node [signal122,signal207,signal260,signal362,signal428,signal463] .nil .nil)) (.node [signal122,signal207,signal260,signal362,signal476,signal491] (.node [signal122,signal207,signal260,signal362,signal463,signal503] .nil .nil) .nil)))) (.node [signal136,signal182,signal260,signal344,signal476,signal491] (.node [signal122,signal224,signal289,signal344,signal476,signal491] (.node [signal122,signal207,signal309,signal362,signal463,signal491] (.node [signal122,signal207,signal289,signal362,signal463,signal491] (.node [signal122,signal207,signal289,signal344,signal476,signal491] .nil .nil) (.node [signal122,signal207,signal309,signal344,signal476,signal491] .nil .nil)) (.node [signal122,signal224,signal289,signal344,signal463,signal503] (.node [signal122,signal224,signal260,signal362,signal463,signal503] .nil .nil) .nil)) (.node [signal125,signal182,signal260,signal362,signal463,signal491] (.node [signal122,signal225,signal260,signal362,signal463,signal491] (.node [signal122,signal225,signal260,signal344,signal476,signal491] .nil .nil) (.node [signal124,signal182,signal260,signal362,signal463,signal491] .nil .nil)) (.node [signal135,signal182,signal260,signal344,signal476,signal491] (.node [signal134,signal182,signal260,signal344,signal479,signal491] .nil .nil) .nil))) (.node [signal140,signal182,signal260,signal344,signal476,signal491] (.node [signal138,signal182,signal260,signal344,signal463,signal503] (.node [signal137,signal182,signal260,signal344,signal463,signal507] (.node [signal136,signal182,signal260,signal362,signal463,signal491] .nil .nil) (.node [signal137,signal224,signal260,signal344,signal463,signal491] .nil .nil)) (.node [signal140,signal182,signal260,signal344,signal463,signal503] (.node [signal139,signal182,signal260,signal344,signal463,signal503] .nil .nil) .nil)) (.node [signal142,signal158,signal260,signal362,signal463,signal491] (.node [signal142,signal158,signal260,signal344,signal463,signal503] (.node [signal141,signal182,signal260,signal344,signal463,signal491] .nil .nil) (.node [signal142,signal158,signal260,signal344,signal476,signal491] .nil .nil)) (.node [signal142,signal159,signal260,signal344,signal476,signal491] (.node [signal142,signal159,signal260,signal344,signal463,signal503] .nil .nil) .nil))))) (.node [signal142,signal182,signal260,signal350,signal463,signal491] (.node [signal142,signal182,signal260,signal338,signal476,signal491] (.node [signal142,signal182,signal238,signal344,signal463,signal503] (.node [signal142,signal182,signal237,signal344,signal463,signal503] (.node [signal142,signal167,signal260,signal344,signal476,signal491] (.node [signal142,signal167,signal260,signal344,signal463,signal503] .nil .nil) (.node [signal142,signal167,signal260,signal362,signal463,signal491] .nil .nil)) (.node [signal142,signal182,signal237,signal362,signal463,signal491] (.node [signal142,signal182,signal237,signal344,signal476,signal491] .nil .nil) .nil)) (.node [signal142,signal182,signal246,signal344,signal476,signal491] (.node [signal142,signal182,signal238,signal362,signal463,signal491] (.node [signal142,signal182,signal238,signal344,signal476,signal491] .nil .nil) (.node [signal142,signal182,signal246,signal344,signal463,signal503] .nil .nil)) (.node [signal142,signal182,signal260,signal338,signal463,signal503] (.node [signal142,signal182,signal246,signal362,signal463,signal491] .nil .nil) .nil))) (.node [signal142,signal182,signal260,signal344,signal464,signal491] (.node [signal142,signal182,signal260,signal344,signal463,signal495] (.node [signal142,signal182,signal260,signal344,signal428,signal476] (.node [signal142,signal182,signal260,signal344,signal424,signal503] .nil .nil) (.node [signal142,signal182,signal260,signal344,signal463,signal492] .nil .nil)) (.node [signal142,signal182,signal260,signal344,signal463,signal503] (.node [signal142,signal182,signal260,signal344,signal463,signal496] .nil .nil) .nil)) (.node [signal142,signal182,signal260,signal344,signal476,signal503] (.node [signal142,signal182,signal260,signal344,signal473,signal491] (.node [signal142,signal182,signal260,signal344,signal467,signal491] .nil .nil) (.node [signal142,signal182,signal260,signal344,signal476,signal491] .nil .nil)) (.node [signal142,signal182,signal260,signal347,signal463,signal491] (.node [signal142,signal182,signal260,signal345,signal463,signal491] .nil .nil) .nil)))) (.node [signal142,signal182,signal310,signal344,signal463,signal503] (.node [signal142,signal182,signal289,signal344,signal463,signal503] (.node [signal142,signal182,signal260,signal362,signal463,signal503] (.node [signal142,signal182,signal260,signal362,signal428,signal463] (.node [signal142,signal182,signal260,signal362,signal424,signal491] .nil .nil) (.node [signal142,signal182,signal260,signal362,signal463,signal491] .nil .nil)) (.node [signal142,signal182,signal286,signal344,signal463,signal491] (.node [signal142,signal182,signal260,signal362,signal476,signal491] .nil .nil) .nil)) (.node [signal142,signal182,signal309,signal344,signal463,signal503] (.node [signal142,signal182,signal289,signal362,signal463,signal491] (.node [signal142,signal182,signal289,signal344,signal476,signal491] .nil .nil) (.node [signal142,signal182,signal306,signal344,signal463,signal491] .nil .nil)) (.node [signal142,signal182,signal309,signal362,signal463,signal491] (.node [signal142,signal182,signal309,signal344,signal476,signal491] .nil .nil) .nil))) (.node [signal142,signal217,signal260,signal344,signal463,signal491] (.node [signal142,signal207,signal260,signal344,signal463,signal503] (.node [signal142,signal182,signal310,signal362,signal463,signal491] (.node [signal142,signal182,signal310,signal344,signal476,signal491] .nil .nil) (.node [signal142,signal200,signal260,signal344,signal463,signal491] .nil .nil)) (.node [signal142,signal207,signal260,signal362,signal463,signal491] (.node [signal142,signal207,signal260,signal344,signal476,signal491] .nil .nil) .nil)) (.node [signal142,signal225,signal260,signal344,signal463,signal503] (.node [signal142,signal224,signal260,signal344,signal476,signal491] (.node [signal142,signal224,signal260,signal344,signal463,signal503] .nil .nil) (.node [signal142,signal224,signal260,signal362,signal463,signal491] .nil .nil)) (.node [signal142,signal225,signal260,signal362,signal463,signal491] (.node [signal142,signal225,signal260,signal344,signal476,signal491] .nil .nil) .nil)))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok5 : everyKey (rowOK 4 layer4) layer5=true := by decide +kernel
theorem closed5 : Closed 5 layer5 := closed_next 4 (by decide) _ _ closed4 ok5
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
def layer6 : BinaryTree (List W) := (.node [signal53,signal122,signal182,signal260,signal362,signal463,signal491] (.node [signal53,signal122,signal177,signal260,signal344,signal463,signal491] (.node [signal53,signal117,signal160,signal260,signal344,signal463,signal491] (.node [signal46,signal94,signal122,signal182,signal260,signal344,signal491] (.node [signal15,signal122,signal207,signal260,signal344,signal463,signal491] (.node [signal7,signal53,signal182,signal260,signal369,signal463,signal491] (.node [signal5,signal122,signal182,signal260,signal344,signal428,signal463] (.node [signal3,signal53,signal182,signal309,signal344,signal463,signal491] (.node [signal2,signal122,signal182,signal289,signal344,signal463,signal491] (.node [signal1,signal142,signal182,signal260,signal344,signal463,signal491] .nil .nil) .nil) (.node [signal4,signal122,signal182,signal260,signal362,signal463,signal491] .nil .nil)) (.node [signal5,signal122,signal182,signal289,signal344,signal463,signal491] (.node [signal5,signal122,signal182,signal260,signal362,signal463,signal491] .nil .nil) (.node [signal5,signal142,signal182,signal260,signal344,signal463,signal491] .nil .nil))) (.node [signal10,signal53,signal122,signal182,signal390,signal463,signal491] (.node [signal8,signal53,signal182,signal309,signal344,signal463,signal491] (.node [signal8,signal53,signal182,signal260,signal344,signal409,signal463] (.node [signal7,signal53,signal182,signal309,signal344,signal463,signal491] .nil .nil) .nil) (.node [signal9,signal53,signal122,signal260,signal344,signal397,signal463] .nil .nil)) (.node [signal13,signal53,signal122,signal182,signal260,signal323,signal463] (.node [signal11,signal53,signal122,signal182,signal344,signal382,signal463] .nil .nil) (.node [signal14,signal26,signal53,signal122,signal182,signal260,signal344] .nil .nil)))) (.node [signal20,signal53,signal122,signal316,signal344,signal463,signal491] (.node [signal18,signal53,signal224,signal260,signal344,signal463,signal491] (.node [signal16,signal122,signal207,signal260,signal344,signal463,signal491] (.node [signal16,signal122,signal182,signal289,signal344,signal463,signal491] (.node [signal16,signal122,signal182,signal260,signal344,signal424,signal491] .nil .nil) .nil) (.node [signal16,signal142,signal182,signal260,signal344,signal463,signal491] .nil .nil)) (.node [signal19,signal53,signal182,signal309,signal344,signal463,signal491] (.node [signal19,signal53,signal182,signal260,signal344,signal406,signal491] .nil .nil) (.node [signal19,signal53,signal224,signal260,signal344,signal463,signal491] .nil .nil))) (.node [signal24,signal53,signal122,signal260,signal344,signal395,signal491] (.node [signal22,signal53,signal122,signal260,signal373,signal463,signal491] (.node [signal21,signal53,signal122,signal182,signal344,signal379,signal491] .nil .nil) (.node [signal23,signal53,signal122,signal182,signal260,signal320,signal491] .nil .nil)) (.node [signal36,signal94,signal224,signal309,signal344,signal463,signal491] (.node [signal27,signal94,signal122,signal182,signal260,signal344,signal438] .nil .nil) (.node [signal45,signal94,signal122,signal182,signal260,signal344,signal463] .nil .nil))))) (.node [signal53,signal105,signal182,signal260,signal344,signal479,signal491] (.node [signal50,signal142,signal182,signal260,signal344,signal463,signal491] (.node [signal49,signal122,signal182,signal260,signal344,signal463,signal503] (.node [signal48,signal122,signal182,signal260,signal344,signal476,signal491] (.node [signal48,signal122,signal167,signal260,signal344,signal463,signal491] (.node [signal47,signal122,signal182,signal260,signal344,signal476,signal491] .nil .nil) .nil) (.node [signal48,signal122,signal182,signal260,signal362,signal463,signal491] .nil .nil)) (.node [signal50,signal122,signal182,signal260,signal344,signal463,signal503] (.node [signal50,signal122,signal182,signal260,signal338,signal463,signal491] .nil .nil) (.node [signal50,signal122,signal207,signal260,signal344,signal463,signal491] .nil .nil))) (.node [signal52,signal122,signal182,signal260,signal344,signal463,signal503] (.node [signal51,signal122,signal182,signal260,signal344,signal476,signal491] (.node [signal51,signal122,signal182,signal260,signal344,signal463,signal503] (.node [signal51,signal122,signal182,signal246,signal344,signal463,signal491] .nil .nil) .nil) (.node [signal52,signal117,signal182,signal260,signal344,signal463,signal491] .nil .nil)) (.node [signal52,signal122,signal182,signal260,signal362,signal463,signal491] (.node [signal52,signal122,signal182,signal260,signal344,signal476,signal491] .nil .nil) (.node [signal53,signal94,signal224,signal309,signal344,signal463,signal491] .nil .nil)))) (.node [signal53,signal110,signal182,signal260,signal344,signal463,signal491] (.node [signal53,signal108,signal182,signal260,signal336,signal463,signal491] (.node [signal53,signal107,signal182,signal260,signal344,signal463,signal507] (.node [signal53,signal106,signal182,signal309,signal344,signal463,signal491] (.node [signal53,signal106,signal159,signal260,signal344,signal463,signal491] .nil .nil) .nil) (.node [signal53,signal107,signal224,signal260,signal344,signal463,signal491] .nil .nil)) (.node [signal53,signal109,signal182,signal238,signal344,signal463,signal491] (.node [signal53,signal108,signal224,signal260,signal344,signal463,signal491] .nil .nil) (.node [signal53,signal109,signal224,signal260,signal344,signal463,signal491] .nil .nil))) (.node [signal53,signal114,signal182,signal260,signal344,signal463,signal491] (.node [signal53,signal112,signal182,signal260,signal344,signal463,signal491] (.node [signal53,signal111,signal182,signal260,signal344,signal463,signal491] .nil .nil) (.node [signal53,signal113,signal182,signal260,signal344,signal463,signal491] .nil .nil)) (.node [signal53,signal116,signal182,signal260,signal344,signal463,signal491] (.node [signal53,signal115,signal182,signal260,signal344,signal463,signal491] .nil .nil) (.node [signal53,signal117,signal159,signal260,signal344,signal463,signal491] .nil .nil)))))) (.node [signal53,signal122,signal159,signal260,signal344,signal424,signal491] (.node [signal53,signal118,signal182,signal260,signal344,signal463,signal491] (.node [signal53,signal117,signal182,signal260,signal344,signal463,signal503] (.node [signal53,signal117,signal182,signal260,signal338,signal463,signal491] (.node [signal53,signal117,signal182,signal239,signal344,signal463,signal491] (.node [signal53,signal117,signal182,signal238,signal344,signal463,signal491] (.node [signal53,signal117,signal167,signal260,signal344,signal463,signal491] .nil .nil) .nil) (.node [signal53,signal117,signal182,signal246,signal344,signal463,signal491] .nil .nil)) (.node [signal53,signal117,signal182,signal260,signal344,signal428,signal463] (.node [signal53,signal117,signal182,signal260,signal344,signal424,signal491] .nil .nil) (.node [signal53,signal117,signal182,signal260,signal344,signal463,signal491] .nil .nil))) (.node [signal53,signal117,signal182,signal309,signal344,signal463,signal491] (.node [signal53,signal117,signal182,signal289,signal344,signal463,signal491] (.node [signal53,signal117,signal182,signal260,signal362,signal463,signal491] (.node [signal53,signal117,signal182,signal260,signal344,signal476,signal491] .nil .nil) .nil) (.node [signal53,signal117,signal182,signal308,signal344,signal463,signal491] .nil .nil)) (.node [signal53,signal117,signal223,signal260,signal344,signal463,signal491] (.node [signal53,signal117,signal207,signal260,signal344,signal463,signal491] .nil .nil) (.node [signal53,signal117,signal224,signal260,signal344,signal463,signal491] .nil .nil)))) (.node [signal53,signal122,signal154,signal260,signal344,signal463,signal491] (.node [signal53,signal122,signal150,signal260,signal344,signal463,signal491] (.node [signal53,signal121,signal182,signal260,signal344,signal463,signal491] (.node [signal53,signal120,signal182,signal260,signal344,signal463,signal491] (.node [signal53,signal119,signal182,signal260,signal344,signal463,signal491] .nil .nil) .nil) (.node [signal53,signal122,signal149,signal260,signal344,signal489,signal491] .nil .nil)) (.node [signal53,signal122,signal152,signal260,signal330,signal463,signal491] (.node [signal53,signal122,signal151,signal182,signal260,signal344,signal491] .nil .nil) (.node [signal53,signal122,signal153,signal260,signal344,signal463,signal491] .nil .nil))) (.node [signal53,signal122,signal158,signal260,signal344,signal463,signal491] (.node [signal53,signal122,signal156,signal260,signal344,signal463,signal491] (.node [signal53,signal122,signal155,signal229,signal344,signal463,signal491] .nil .nil) (.node [signal53,signal122,signal157,signal260,signal344,signal463,signal491] .nil .nil)) (.node [signal53,signal122,signal159,signal246,signal344,signal463,signal491] (.node [signal53,signal122,signal159,signal238,signal344,signal463,signal491] .nil .nil) (.node [signal53,signal122,signal159,signal260,signal338,signal463,signal491] .nil .nil))))) (.node [signal53,signal122,signal167,signal260,signal344,signal424,signal491] (.node [signal53,signal122,signal161,signal260,signal344,signal463,signal491] (.node [signal53,signal122,signal159,signal260,signal362,signal463,signal491] (.node [signal53,signal122,signal159,signal260,signal344,signal463,signal503] (.node [signal53,signal122,signal159,signal260,signal344,signal463,signal491] (.node [signal53,signal122,signal159,signal260,signal344,signal428,signal463] .nil .nil) .nil) (.node [signal53,signal122,signal159,signal260,signal344,signal476,signal491] .nil .nil)) (.node [signal53,signal122,signal159,signal309,signal344,signal463,signal491] (.node [signal53,signal122,signal159,signal289,signal344,signal463,signal491] .nil .nil) (.node [signal53,signal122,signal160,signal260,signal344,signal463,signal491] .nil .nil))) (.node [signal53,signal122,signal166,signal260,signal344,signal463,signal491] (.node [signal53,signal122,signal164,signal260,signal344,signal463,signal491] (.node [signal53,signal122,signal163,signal260,signal344,signal463,signal491] (.node [signal53,signal122,signal162,signal260,signal344,signal463,signal491] .nil .nil) .nil) (.node [signal53,signal122,signal165,signal260,signal344,signal463,signal491] .nil .nil)) (.node [signal53,signal122,signal167,signal246,signal344,signal463,signal491] (.node [signal53,signal122,signal167,signal238,signal344,signal463,signal491] .nil .nil) (.node [signal53,signal122,signal167,signal260,signal338,signal463,signal491] .nil .nil)))) (.node [signal53,signal122,signal169,signal260,signal344,signal463,signal491] (.node [signal53,signal122,signal167,signal260,signal362,signal463,signal491] (.node [signal53,signal122,signal167,signal260,signal344,signal463,signal503] (.node [signal53,signal122,signal167,signal260,signal344,signal463,signal491] (.node [signal53,signal122,signal167,signal260,signal344,signal428,signal463] .nil .nil) .nil) (.node [signal53,signal122,signal167,signal260,signal344,signal476,signal491] .nil .nil)) (.node [signal53,signal122,signal167,signal309,signal344,signal463,signal491] (.node [signal53,signal122,signal167,signal289,signal344,signal463,signal491] .nil .nil) (.node [signal53,signal122,signal168,signal260,signal344,signal463,signal491] .nil .nil))) (.node [signal53,signal122,signal173,signal260,signal344,signal463,signal510] (.node [signal53,signal122,signal171,signal260,signal344,signal463,signal491] (.node [signal53,signal122,signal170,signal260,signal344,signal463,signal491] .nil .nil) (.node [signal53,signal122,signal172,signal260,signal344,signal463,signal491] .nil .nil)) (.node [signal53,signal122,signal175,signal260,signal344,signal463,signal491] (.node [signal53,signal122,signal174,signal260,signal344,signal463,signal491] .nil .nil) (.node [signal53,signal122,signal176,signal260,signal344,signal463,signal491] .nil .nil))))))) (.node [signal53,signal122,signal182,signal260,signal344,signal407,signal491] (.node [signal53,signal122,signal182,signal247,signal344,signal463,signal491] (.node [signal53,signal122,signal182,signal238,signal344,signal463,signal503] (.node [signal53,signal122,signal182,signal233,signal344,signal463,signal491] (.node [signal53,signal122,signal182,signal228,signal344,signal481,signal491] (.node [signal53,signal122,signal180,signal260,signal344,signal463,signal491] (.node [signal53,signal122,signal179,signal260,signal344,signal463,signal491] (.node [signal53,signal122,signal178,signal260,signal344,signal463,signal491] .nil .nil) .nil) (.node [signal53,signal122,signal181,signal260,signal344,signal463,signal491] .nil .nil)) (.node [signal53,signal122,signal182,signal231,signal333,signal463,signal491] (.node [signal53,signal122,signal182,signal230,signal344,signal463,signal512] .nil .nil) (.node [signal53,signal122,signal182,signal232,signal344,signal463,signal491] .nil .nil))) (.node [signal53,signal122,signal182,signal238,signal338,signal463,signal491] (.node [signal53,signal122,signal182,signal236,signal344,signal463,signal491] (.node [signal53,signal122,signal182,signal235,signal344,signal463,signal491] (.node [signal53,signal122,signal182,signal234,signal344,signal463,signal491] .nil .nil) .nil) (.node [signal53,signal122,signal182,signal237,signal344,signal463,signal491] .nil .nil)) (.node [signal53,signal122,signal182,signal238,signal344,signal428,signal463] (.node [signal53,signal122,signal182,signal238,signal344,signal424,signal491] .nil .nil) (.node [signal53,signal122,signal182,signal238,signal344,signal463,signal491] .nil .nil)))) (.node [signal53,signal122,signal182,signal245,signal344,signal463,signal491] (.node [signal53,signal122,signal182,signal241,signal344,signal463,signal491] (.node [signal53,signal122,signal182,signal239,signal344,signal463,signal491] (.node [signal53,signal122,signal182,signal238,signal362,signal463,signal491] (.node [signal53,signal122,signal182,signal238,signal344,signal476,signal491] .nil .nil) .nil) (.node [signal53,signal122,signal182,signal240,signal344,signal463,signal491] .nil .nil)) (.node [signal53,signal122,signal182,signal243,signal344,signal463,signal491] (.node [signal53,signal122,signal182,signal242,signal344,signal463,signal491] .nil .nil) (.node [signal53,signal122,signal182,signal244,signal344,signal463,signal491] .nil .nil))) (.node [signal53,signal122,signal182,signal246,signal344,signal463,signal491] (.node [signal53,signal122,signal182,signal246,signal344,signal424,signal491] (.node [signal53,signal122,signal182,signal246,signal338,signal463,signal491] .nil .nil) (.node [signal53,signal122,signal182,signal246,signal344,signal428,signal463] .nil .nil)) (.node [signal53,signal122,signal182,signal246,signal344,signal476,signal491] (.node [signal53,signal122,signal182,signal246,signal344,signal463,signal503] .nil .nil) (.node [signal53,signal122,signal182,signal246,signal362,signal463,signal491] .nil .nil))))) (.node [signal53,signal122,signal182,signal260,signal334,signal463,signal491] (.node [signal53,signal122,signal182,signal256,signal344,signal463,signal491] (.node [signal53,signal122,signal182,signal252,signal344,signal463,signal491] (.node [signal53,signal122,signal182,signal250,signal344,signal463,signal491] (.node [signal53,signal122,signal182,signal249,signal344,signal463,signal491] (.node [signal53,signal122,signal182,signal248,signal344,signal463,signal491] .nil .nil) .nil) (.node [signal53,signal122,signal182,signal251,signal344,signal463,signal491] .nil .nil)) (.node [signal53,signal122,signal182,signal254,signal344,signal463,signal491] (.node [signal53,signal122,signal182,signal253,signal344,signal463,signal491] .nil .nil) (.node [signal53,signal122,signal182,signal255,signal344,signal463,signal491] .nil .nil))) (.node [signal53,signal122,signal182,signal260,signal322,signal344,signal491] (.node [signal53,signal122,signal182,signal259,signal344,signal463,signal491] (.node [signal53,signal122,signal182,signal258,signal344,signal463,signal491] (.node [signal53,signal122,signal182,signal257,signal344,signal463,signal491] .nil .nil) .nil) (.node [signal53,signal122,signal182,signal260,signal321,signal344,signal491] .nil .nil)) (.node [signal53,signal122,signal182,signal260,signal331,signal463,signal514] (.node [signal53,signal122,signal182,signal260,signal329,signal486,signal491] .nil .nil) (.node [signal53,signal122,signal182,signal260,signal332,signal463,signal491] .nil .nil)))) (.node [signal53,signal122,signal182,signal260,signal340,signal463,signal491] (.node [signal53,signal122,signal182,signal260,signal338,signal463,signal491] (.node [signal53,signal122,signal182,signal260,signal338,signal424,signal491] (.node [signal53,signal122,signal182,signal260,signal337,signal463,signal491] (.node [signal53,signal122,signal182,signal260,signal335,signal463,signal491] .nil .nil) .nil) (.node [signal53,signal122,signal182,signal260,signal338,signal428,signal463] .nil .nil)) (.node [signal53,signal122,signal182,signal260,signal338,signal476,signal491] (.node [signal53,signal122,signal182,signal260,signal338,signal463,signal503] .nil .nil) (.node [signal53,signal122,signal182,signal260,signal339,signal463,signal491] .nil .nil))) (.node [signal53,signal122,signal182,signal260,signal344,signal351,signal463] (.node [signal53,signal122,signal182,signal260,signal342,signal463,signal491] (.node [signal53,signal122,signal182,signal260,signal341,signal463,signal491] .nil .nil) (.node [signal53,signal122,signal182,signal260,signal343,signal463,signal491] .nil .nil)) (.node [signal53,signal122,signal182,signal260,signal344,signal385,signal463] (.node [signal53,signal122,signal182,signal260,signal344,signal380,signal491] .nil .nil) (.node [signal53,signal122,signal182,signal260,signal344,signal400,signal463] .nil .nil)))))) (.node [signal53,signal122,signal182,signal260,signal344,signal463,signal509] (.node [signal53,signal122,signal182,signal260,signal344,signal463,signal488] (.node [signal53,signal122,signal182,signal260,signal344,signal430,signal463] (.node [signal53,signal122,signal182,signal260,signal344,signal425,signal491] (.node [signal53,signal122,signal182,signal260,signal344,signal424,signal491] (.node [signal53,signal122,signal182,signal260,signal344,signal424,signal428] (.node [signal53,signal122,signal182,signal260,signal344,signal411,signal463] .nil .nil) .nil) (.node [signal53,signal122,signal182,signal260,signal344,signal424,signal503] .nil .nil)) (.node [signal53,signal122,signal182,signal260,signal344,signal428,signal463] (.node [signal53,signal122,signal182,signal260,signal344,signal426,signal491] .nil .nil) (.node [signal53,signal122,signal182,signal260,signal344,signal428,signal476] .nil .nil))) (.node [signal53,signal122,signal182,signal260,signal344,signal461,signal491] (.node [signal53,signal122,signal182,signal260,signal344,signal459,signal491] (.node [signal53,signal122,signal182,signal260,signal344,signal458,signal515] (.node [signal53,signal122,signal182,signal260,signal344,signal431,signal463] .nil .nil) .nil) (.node [signal53,signal122,signal182,signal260,signal344,signal460,signal491] .nil .nil)) (.node [signal53,signal122,signal182,signal260,signal344,signal463,signal482] (.node [signal53,signal122,signal182,signal260,signal344,signal462,signal491] .nil .nil) (.node [signal53,signal122,signal182,signal260,signal344,signal463,signal487] .nil .nil)))) (.node [signal53,signal122,signal182,signal260,signal344,signal463,signal499] (.node [signal53,signal122,signal182,signal260,signal344,signal463,signal495] (.node [signal53,signal122,signal182,signal260,signal344,signal463,signal493] (.node [signal53,signal122,signal182,signal260,signal344,signal463,signal492] (.node [signal53,signal122,signal182,signal260,signal344,signal463,signal491] .nil .nil) .nil) (.node [signal53,signal122,signal182,signal260,signal344,signal463,signal494] .nil .nil)) (.node [signal53,signal122,signal182,signal260,signal344,signal463,signal497] (.node [signal53,signal122,signal182,signal260,signal344,signal463,signal496] .nil .nil) (.node [signal53,signal122,signal182,signal260,signal344,signal463,signal498] .nil .nil))) (.node [signal53,signal122,signal182,signal260,signal344,signal463,signal503] (.node [signal53,signal122,signal182,signal260,signal344,signal463,signal501] (.node [signal53,signal122,signal182,signal260,signal344,signal463,signal500] .nil .nil) (.node [signal53,signal122,signal182,signal260,signal344,signal463,signal502] .nil .nil)) (.node [signal53,signal122,signal182,signal260,signal344,signal463,signal506] (.node [signal53,signal122,signal182,signal260,signal344,signal463,signal505] .nil .nil) (.node [signal53,signal122,signal182,signal260,signal344,signal463,signal508] .nil .nil))))) (.node [signal53,signal122,signal182,signal260,signal344,signal480,signal491] (.node [signal53,signal122,signal182,signal260,signal344,signal471,signal491] (.node [signal53,signal122,signal182,signal260,signal344,signal467,signal491] (.node [signal53,signal122,signal182,signal260,signal344,signal465,signal491] (.node [signal53,signal122,signal182,signal260,signal344,signal464,signal491] (.node [signal53,signal122,signal182,signal260,signal344,signal463,signal511] .nil .nil) .nil) (.node [signal53,signal122,signal182,signal260,signal344,signal466,signal491] .nil .nil)) (.node [signal53,signal122,signal182,signal260,signal344,signal469,signal491] (.node [signal53,signal122,signal182,signal260,signal344,signal468,signal491] .nil .nil) (.node [signal53,signal122,signal182,signal260,signal344,signal470,signal491] .nil .nil))) (.node [signal53,signal122,signal182,signal260,signal344,signal475,signal491] (.node [signal53,signal122,signal182,signal260,signal344,signal473,signal491] (.node [signal53,signal122,signal182,signal260,signal344,signal472,signal491] .nil .nil) (.node [signal53,signal122,signal182,signal260,signal344,signal474,signal491] .nil .nil)) (.node [signal53,signal122,signal182,signal260,signal344,signal476,signal503] (.node [signal53,signal122,signal182,signal260,signal344,signal476,signal491] .nil .nil) (.node [signal53,signal122,signal182,signal260,signal344,signal478,signal491] .nil .nil)))) (.node [signal53,signal122,signal182,signal260,signal350,signal463,signal491] (.node [signal53,signal122,signal182,signal260,signal346,signal463,signal491] (.node [signal53,signal122,signal182,signal260,signal344,signal485,signal491] (.node [signal53,signal122,signal182,signal260,signal344,signal484,signal491] (.node [signal53,signal122,signal182,signal260,signal344,signal483,signal491] .nil .nil) .nil) (.node [signal53,signal122,signal182,signal260,signal345,signal463,signal491] .nil .nil)) (.node [signal53,signal122,signal182,signal260,signal348,signal463,signal491] (.node [signal53,signal122,signal182,signal260,signal347,signal463,signal491] .nil .nil) (.node [signal53,signal122,signal182,signal260,signal349,signal463,signal491] .nil .nil))) (.node [signal53,signal122,signal182,signal260,signal360,signal463,signal491] (.node [signal53,signal122,signal182,signal260,signal356,signal463,signal491] (.node [signal53,signal122,signal182,signal260,signal355,signal463,signal491] .nil .nil) (.node [signal53,signal122,signal182,signal260,signal359,signal463,signal491] .nil .nil)) (.node [signal53,signal122,signal182,signal260,signal362,signal424,signal491] (.node [signal53,signal122,signal182,signal260,signal361,signal463,signal491] .nil .nil) (.node [signal53,signal122,signal182,signal260,signal362,signal428,signal463] .nil .nil)))))))) (.node [signal53,signal142,signal182,signal309,signal344,signal463,signal491] (.node [signal53,signal122,signal202,signal260,signal344,signal463,signal491] (.node [signal53,signal122,signal182,signal289,signal362,signal463,signal491] (.node [signal53,signal122,signal182,signal271,signal344,signal463,signal491] (.node [signal53,signal122,signal182,signal262,signal344,signal463,signal491] (.node [signal53,signal122,signal182,signal260,signal371,signal463,signal491] (.node [signal53,signal122,signal182,signal260,signal365,signal463,signal491] (.node [signal53,signal122,signal182,signal260,signal362,signal476,signal491] (.node [signal53,signal122,signal182,signal260,signal362,signal463,signal503] .nil .nil) .nil) (.node [signal53,signal122,signal182,signal260,signal368,signal463,signal491] .nil .nil)) (.node [signal53,signal122,signal182,signal260,signal389,signal463,signal491] (.node [signal53,signal122,signal182,signal260,signal386,signal463,signal491] .nil .nil) (.node [signal53,signal122,signal182,signal261,signal344,signal463,signal491] .nil .nil))) (.node [signal53,signal122,signal182,signal267,signal344,signal463,signal491] (.node [signal53,signal122,signal182,signal265,signal344,signal463,signal491] (.node [signal53,signal122,signal182,signal264,signal344,signal463,signal491] (.node [signal53,signal122,signal182,signal263,signal344,signal463,signal491] .nil .nil) .nil) (.node [signal53,signal122,signal182,signal266,signal344,signal463,signal491] .nil .nil)) (.node [signal53,signal122,signal182,signal269,signal344,signal463,signal491] (.node [signal53,signal122,signal182,signal268,signal344,signal463,signal491] .nil .nil) (.node [signal53,signal122,signal182,signal270,signal344,signal463,signal491] .nil .nil)))) (.node [signal53,signal122,signal182,signal286,signal344,signal463,signal491] (.node [signal53,signal122,signal182,signal280,signal344,signal463,signal491] (.node [signal53,signal122,signal182,signal274,signal344,signal463,signal491] (.node [signal53,signal122,signal182,signal273,signal344,signal463,signal491] (.node [signal53,signal122,signal182,signal272,signal344,signal463,signal491] .nil .nil) .nil) (.node [signal53,signal122,signal182,signal279,signal344,signal463,signal491] .nil .nil)) (.node [signal53,signal122,signal182,signal283,signal344,signal463,signal491] (.node [signal53,signal122,signal182,signal282,signal344,signal463,signal491] .nil .nil) (.node [signal53,signal122,signal182,signal285,signal344,signal463,signal491] .nil .nil))) (.node [signal53,signal122,signal182,signal289,signal344,signal428,signal463] (.node [signal53,signal122,signal182,signal289,signal338,signal463,signal491] (.node [signal53,signal122,signal182,signal288,signal344,signal463,signal491] .nil .nil) (.node [signal53,signal122,signal182,signal289,signal344,signal424,signal491] .nil .nil)) (.node [signal53,signal122,signal182,signal289,signal344,signal463,signal503] (.node [signal53,signal122,signal182,signal289,signal344,signal463,signal491] .nil .nil) (.node [signal53,signal122,signal182,signal289,signal344,signal476,signal491] .nil .nil))))) (.node [signal53,signal122,signal182,signal311,signal344,signal463,signal491] (.node [signal53,signal122,signal182,signal308,signal344,signal463,signal491] (.node [signal53,signal122,signal182,signal301,signal344,signal463,signal491] (.node [signal53,signal122,signal182,signal297,signal344,signal463,signal491] (.node [signal53,signal122,signal182,signal295,signal344,signal463,signal491] (.node [signal53,signal122,signal182,signal294,signal344,signal463,signal491] .nil .nil) .nil) (.node [signal53,signal122,signal182,signal298,signal344,signal463,signal491] .nil .nil)) (.node [signal53,signal122,signal182,signal306,signal344,signal463,signal491] (.node [signal53,signal122,signal182,signal302,signal344,signal463,signal491] .nil .nil) (.node [signal53,signal122,signal182,signal307,signal344,signal463,signal491] .nil .nil))) (.node [signal53,signal122,signal182,signal309,signal344,signal463,signal503] (.node [signal53,signal122,signal182,signal309,signal344,signal428,signal463] (.node [signal53,signal122,signal182,signal309,signal344,signal424,signal491] (.node [signal53,signal122,signal182,signal309,signal338,signal463,signal491] .nil .nil) .nil) (.node [signal53,signal122,signal182,signal309,signal344,signal463,signal491] .nil .nil)) (.node [signal53,signal122,signal182,signal309,signal362,signal463,signal491] (.node [signal53,signal122,signal182,signal309,signal344,signal476,signal491] .nil .nil) (.node [signal53,signal122,signal182,signal310,signal344,signal463,signal491] .nil .nil)))) (.node [signal53,signal122,signal189,signal260,signal344,signal463,signal491] (.node [signal53,signal122,signal185,signal260,signal344,signal463,signal491] (.node [signal53,signal122,signal183,signal260,signal344,signal463,signal491] (.node [signal53,signal122,signal182,signal344,signal388,signal463,signal491] (.node [signal53,signal122,signal182,signal344,signal383,signal463,signal491] .nil .nil) .nil) (.node [signal53,signal122,signal184,signal260,signal344,signal463,signal491] .nil .nil)) (.node [signal53,signal122,signal187,signal260,signal344,signal463,signal491] (.node [signal53,signal122,signal186,signal260,signal344,signal463,signal491] .nil .nil) (.node [signal53,signal122,signal188,signal260,signal344,signal463,signal491] .nil .nil))) (.node [signal53,signal122,signal193,signal260,signal344,signal463,signal491] (.node [signal53,signal122,signal191,signal260,signal344,signal463,signal491] (.node [signal53,signal122,signal190,signal260,signal344,signal463,signal491] .nil .nil) (.node [signal53,signal122,signal192,signal260,signal344,signal463,signal491] .nil .nil)) (.node [signal53,signal122,signal199,signal260,signal344,signal463,signal491] (.node [signal53,signal122,signal194,signal260,signal344,signal463,signal491] .nil .nil) (.node [signal53,signal122,signal200,signal260,signal344,signal463,signal491] .nil .nil)))))) (.node [signal53,signal122,signal224,signal309,signal344,signal463,signal491] (.node [signal53,signal122,signal217,signal260,signal344,signal463,signal491] (.node [signal53,signal122,signal207,signal260,signal344,signal428,signal463] (.node [signal53,signal122,signal207,signal238,signal344,signal463,signal491] (.node [signal53,signal122,signal205,signal260,signal344,signal463,signal491] (.node [signal53,signal122,signal204,signal260,signal344,signal463,signal491] (.node [signal53,signal122,signal203,signal260,signal344,signal463,signal491] .nil .nil) .nil) (.node [signal53,signal122,signal206,signal260,signal344,signal463,signal491] .nil .nil)) (.node [signal53,signal122,signal207,signal260,signal338,signal463,signal491] (.node [signal53,signal122,signal207,signal246,signal344,signal463,signal491] .nil .nil) (.node [signal53,signal122,signal207,signal260,signal344,signal424,signal491] .nil .nil))) (.node [signal53,signal122,signal207,signal289,signal344,signal463,signal491] (.node [signal53,signal122,signal207,signal260,signal344,signal476,signal491] (.node [signal53,signal122,signal207,signal260,signal344,signal463,signal503] (.node [signal53,signal122,signal207,signal260,signal344,signal463,signal491] .nil .nil) .nil) (.node [signal53,signal122,signal207,signal260,signal362,signal463,signal491] .nil .nil)) (.node [signal53,signal122,signal211,signal260,signal344,signal463,signal491] (.node [signal53,signal122,signal207,signal309,signal344,signal463,signal491] .nil .nil) (.node [signal53,signal122,signal212,signal260,signal344,signal463,signal491] .nil .nil)))) (.node [signal53,signal122,signal224,signal260,signal338,signal463,signal491] (.node [signal53,signal122,signal222,signal260,signal344,signal463,signal491] (.node [signal53,signal122,signal220,signal260,signal344,signal463,signal491] (.node [signal53,signal122,signal219,signal260,signal344,signal463,signal491] (.node [signal53,signal122,signal218,signal260,signal344,signal463,signal491] .nil .nil) .nil) (.node [signal53,signal122,signal221,signal260,signal344,signal463,signal491] .nil .nil)) (.node [signal53,signal122,signal224,signal238,signal344,signal463,signal491] (.node [signal53,signal122,signal223,signal260,signal344,signal463,signal491] .nil .nil) (.node [signal53,signal122,signal224,signal246,signal344,signal463,signal491] .nil .nil))) (.node [signal53,signal122,signal224,signal260,signal344,signal463,signal503] (.node [signal53,signal122,signal224,signal260,signal344,signal428,signal463] (.node [signal53,signal122,signal224,signal260,signal344,signal424,signal491] .nil .nil) (.node [signal53,signal122,signal224,signal260,signal344,signal463,signal491] .nil .nil)) (.node [signal53,signal122,signal224,signal260,signal362,signal463,signal491] (.node [signal53,signal122,signal224,signal260,signal344,signal476,signal491] .nil .nil) (.node [signal53,signal122,signal224,signal289,signal344,signal463,signal491] .nil .nil))))) (.node [signal53,signal138,signal182,signal260,signal344,signal463,signal491] (.node [signal53,signal125,signal182,signal260,signal344,signal463,signal491] (.node [signal53,signal122,signal260,signal344,signal372,signal463,signal491] (.node [signal53,signal122,signal260,signal314,signal344,signal463,signal491] (.node [signal53,signal122,signal260,signal313,signal344,signal463,signal491] (.node [signal53,signal122,signal225,signal260,signal344,signal463,signal491] .nil .nil) .nil) (.node [signal53,signal122,signal260,signal315,signal344,signal463,signal491] .nil .nil)) (.node [signal53,signal123,signal182,signal260,signal344,signal463,signal491] (.node [signal53,signal122,signal260,signal344,signal396,signal463,signal491] .nil .nil) (.node [signal53,signal124,signal182,signal260,signal344,signal463,signal491] .nil .nil))) (.node [signal53,signal129,signal182,signal260,signal344,signal463,signal491] (.node [signal53,signal127,signal182,signal260,signal344,signal463,signal491] (.node [signal53,signal126,signal182,signal260,signal344,signal463,signal491] .nil .nil) (.node [signal53,signal128,signal182,signal260,signal344,signal463,signal491] .nil .nil)) (.node [signal53,signal135,signal182,signal260,signal344,signal463,signal491] (.node [signal53,signal130,signal182,signal260,signal344,signal463,signal491] .nil .nil) (.node [signal53,signal136,signal182,signal260,signal344,signal463,signal491] .nil .nil)))) (.node [signal53,signal142,signal182,signal260,signal338,signal463,signal491] (.node [signal53,signal142,signal167,signal260,signal344,signal463,signal491] (.node [signal53,signal142,signal158,signal260,signal344,signal463,signal491] (.node [signal53,signal140,signal182,signal260,signal344,signal463,signal491] (.node [signal53,signal139,signal182,signal260,signal344,signal463,signal491] .nil .nil) .nil) (.node [signal53,signal142,signal159,signal260,signal344,signal463,signal491] .nil .nil)) (.node [signal53,signal142,signal182,signal238,signal344,signal463,signal491] (.node [signal53,signal142,signal182,signal237,signal344,signal463,signal491] .nil .nil) (.node [signal53,signal142,signal182,signal246,signal344,signal463,signal491] .nil .nil))) (.node [signal53,signal142,signal182,signal260,signal344,signal463,signal503] (.node [signal53,signal142,signal182,signal260,signal344,signal428,signal463] (.node [signal53,signal142,signal182,signal260,signal344,signal424,signal491] .nil .nil) (.node [signal53,signal142,signal182,signal260,signal344,signal463,signal491] .nil .nil)) (.node [signal53,signal142,signal182,signal260,signal362,signal463,signal491] (.node [signal53,signal142,signal182,signal260,signal344,signal476,signal491] .nil .nil) (.node [signal53,signal142,signal182,signal289,signal344,signal463,signal491] .nil .nil))))))) (.node [signal94,signal191,signal309,signal344,signal438,signal463,signal491] (.node [signal94,signal122,signal182,signal260,signal325,signal438,signal491] (.node [signal53,signal224,signal260,signal344,signal409,signal463,signal491] (.node [signal53,signal182,signal260,signal296,signal344,signal463,signal491] (.node [signal53,signal159,signal224,signal260,signal344,signal463,signal491] (.node [signal53,signal142,signal224,signal260,signal344,signal463,signal491] (.node [signal53,signal142,signal207,signal260,signal344,signal463,signal491] (.node [signal53,signal142,signal182,signal310,signal344,signal463,signal491] .nil .nil) .nil) (.node [signal53,signal142,signal225,signal260,signal344,signal463,signal491] .nil .nil)) (.node [signal53,signal182,signal224,signal309,signal344,signal463,signal491] (.node [signal53,signal182,signal213,signal260,signal344,signal463,signal491] .nil .nil) (.node [signal53,signal182,signal238,signal309,signal344,signal463,signal491] .nil .nil))) (.node [signal53,signal182,signal309,signal344,signal463,signal479,signal491] (.node [signal53,signal182,signal260,signal344,signal366,signal463,signal491] (.node [signal53,signal182,signal260,signal300,signal344,signal463,signal491] (.node [signal53,signal182,signal260,signal299,signal344,signal463,signal491] .nil .nil) .nil) (.node [signal53,signal182,signal309,signal336,signal344,signal463,signal491] .nil .nil)) (.node [signal53,signal224,signal260,signal309,signal344,signal463,signal491] (.node [signal53,signal182,signal309,signal344,signal463,signal491,signal507] .nil .nil) (.node [signal53,signal224,signal260,signal344,signal369,signal463,signal491] .nil .nil)))) (.node [signal62,signal122,signal182,signal260,signal344,signal463,signal491] (.node [signal56,signal122,signal182,signal260,signal344,signal463,signal491] (.node [signal53,signal224,signal309,signal344,signal463,signal491] (.node [signal53,signal224,signal309,signal344,signal438,signal463,signal491] (.node [signal53,signal224,signal260,signal344,signal463,signal479,signal491] .nil .nil) .nil) (.node [signal54,signal122,signal182,signal260,signal344,signal463,signal491] .nil .nil)) (.node [signal59,signal122,signal182,signal260,signal344,signal463,signal491] (.node [signal57,signal122,signal182,signal260,signal344,signal463,signal491] .nil .nil) (.node [signal61,signal122,signal182,signal260,signal344,signal463,signal491] .nil .nil))) (.node [signal69,signal122,signal182,signal260,signal344,signal463,signal491] (.node [signal65,signal122,signal182,signal260,signal344,signal463,signal491] (.node [signal64,signal122,signal182,signal260,signal344,signal463,signal491] .nil .nil) (.node [signal67,signal122,signal182,signal260,signal344,signal463,signal491] .nil .nil)) (.node [signal75,signal122,signal182,signal260,signal344,signal463,signal491] (.node [signal70,signal122,signal182,signal260,signal344,signal463,signal491] .nil .nil) (.node [signal94,signal122,signal182,signal260,signal324,signal438,signal463] .nil .nil))))) (.node [signal94,signal142,signal182,signal260,signal344,signal476,signal491] (.node [signal94,signal122,signal207,signal260,signal344,signal476,signal491] (.node [signal94,signal122,signal182,signal344,signal378,signal463,signal491] (.node [signal94,signal122,signal182,signal289,signal344,signal463,signal503] (.node [signal94,signal122,signal182,signal260,signal362,signal463,signal503] (.node [signal94,signal122,signal182,signal260,signal326,signal463,signal491] .nil .nil) .nil) (.node [signal94,signal122,signal182,signal289,signal344,signal476,signal491] .nil .nil)) (.node [signal94,signal122,signal182,signal344,signal384,signal438,signal463] (.node [signal94,signal122,signal182,signal344,signal381,signal438,signal491] .nil .nil) (.node [signal94,signal122,signal182,signal387,signal438,signal463,signal491] .nil .nil))) (.node [signal94,signal122,signal260,signal370,signal438,signal463,signal491] (.node [signal94,signal122,signal260,signal344,signal398,signal438,signal463] (.node [signal94,signal122,signal260,signal344,signal394,signal463,signal491] (.node [signal94,signal122,signal207,signal260,signal362,signal463,signal491] .nil .nil) .nil) (.node [signal94,signal122,signal260,signal344,signal399,signal438,signal491] .nil .nil)) (.node [signal94,signal129,signal316,signal344,signal438,signal463,signal491] (.node [signal94,signal122,signal312,signal344,signal438,signal463,signal491] .nil .nil) (.node [signal94,signal142,signal182,signal260,signal344,signal463,signal503] .nil .nil)))) (.node [signal94,signal182,signal303,signal344,signal438,signal463,signal491] (.node [signal94,signal182,signal260,signal366,signal438,signal463,signal514] (.node [signal94,signal182,signal260,signal344,signal408,signal438,signal491] (.node [signal94,signal182,signal260,signal344,signal405,signal463,signal491] (.node [signal94,signal142,signal182,signal260,signal362,signal463,signal491] .nil .nil) .nil) (.node [signal94,signal182,signal260,signal344,signal410,signal438,signal463] .nil .nil)) (.node [signal94,signal182,signal260,signal368,signal438,signal463,signal507] (.node [signal94,signal182,signal260,signal367,signal438,signal463,signal491] .nil .nil) (.node [signal94,signal182,signal260,signal369,signal438,signal463,signal505] .nil .nil))) (.node [signal94,signal182,signal309,signal344,signal438,signal468,signal491] (.node [signal94,signal182,signal305,signal344,signal438,signal463,signal491] (.node [signal94,signal182,signal304,signal344,signal438,signal463,signal491] .nil .nil) (.node [signal94,signal182,signal309,signal344,signal438,signal463,signal505] .nil .nil)) (.node [signal94,signal188,signal309,signal344,signal438,signal463,signal491] (.node [signal94,signal185,signal309,signal344,signal438,signal463,signal491] .nil .nil) (.node [signal94,signal189,signal309,signal344,signal438,signal463,signal491] .nil .nil)))))) (.node [signal122,signal182,signal260,signal344,signal418,signal438,signal491] (.node [signal122,signal142,signal182,signal260,signal362,signal463,signal491] (.node [signal94,signal224,signal302,signal344,signal438,signal463,signal491] (.node [signal94,signal224,signal260,signal368,signal438,signal463,signal491] (.node [signal94,signal216,signal260,signal344,signal438,signal463,signal491] (.node [signal94,signal215,signal260,signal344,signal438,signal463,signal491] (.node [signal94,signal214,signal260,signal344,signal438,signal463,signal491] .nil .nil) .nil) (.node [signal94,signal224,signal260,signal344,signal438,signal478,signal491] .nil .nil)) (.node [signal94,signal224,signal270,signal344,signal438,signal463,signal491] (.node [signal94,signal224,signal269,signal344,signal438,signal463,signal491] .nil .nil) (.node [signal94,signal224,signal301,signal344,signal438,signal463,signal491] .nil .nil))) (.node [signal122,signal134,signal182,signal260,signal344,signal463,signal491] (.node [signal122,signal131,signal182,signal260,signal344,signal463,signal491] (.node [signal117,signal142,signal182,signal260,signal344,signal463,signal491] (.node [signal94,signal224,signal309,signal344,signal438,signal463,signal491] .nil .nil) .nil) (.node [signal122,signal132,signal182,signal260,signal344,signal463,signal491] .nil .nil)) (.node [signal122,signal142,signal182,signal260,signal344,signal463,signal503] (.node [signal122,signal137,signal182,signal260,signal344,signal463,signal491] .nil .nil) (.node [signal122,signal142,signal182,signal260,signal344,signal476,signal491] .nil .nil)))) (.node [signal122,signal182,signal260,signal278,signal344,signal463,signal491] (.node [signal122,signal182,signal207,signal260,signal362,signal463,signal491] (.node [signal122,signal182,signal197,signal260,signal344,signal463,signal491] (.node [signal122,signal182,signal195,signal260,signal344,signal463,signal491] (.node [signal122,signal167,signal207,signal260,signal344,signal463,signal491] .nil .nil) .nil) (.node [signal122,signal182,signal207,signal260,signal344,signal476,signal491] .nil .nil)) (.node [signal122,signal182,signal260,signal275,signal344,signal463,signal491] (.node [signal122,signal182,signal246,signal289,signal344,signal463,signal491] .nil .nil) (.node [signal122,signal182,signal260,signal276,signal344,signal463,signal491] .nil .nil))) (.node [signal122,signal182,signal260,signal338,signal362,signal463,signal491] (.node [signal122,signal182,signal260,signal289,signal344,signal463,signal503] (.node [signal122,signal182,signal260,signal281,signal344,signal463,signal491] .nil .nil) (.node [signal122,signal182,signal260,signal289,signal344,signal476,signal491] .nil .nil)) (.node [signal122,signal182,signal260,signal344,signal357,signal463,signal491] (.node [signal122,signal182,signal260,signal344,signal352,signal463,signal491] .nil .nil) (.node [signal122,signal182,signal260,signal344,signal362,signal463,signal503] .nil .nil))))) (.node [signal122,signal207,signal260,signal344,signal438,signal476,signal491] (.node [signal122,signal182,signal289,signal344,signal438,signal463,signal503] (.node [signal122,signal182,signal260,signal354,signal438,signal463,signal491] (.node [signal122,signal182,signal260,signal344,signal424,signal476,signal491] (.node [signal122,signal182,signal260,signal344,signal423,signal463,signal491] (.node [signal122,signal182,signal260,signal344,signal421,signal438,signal463] .nil .nil) .nil) (.node [signal122,signal182,signal260,signal344,signal428,signal463,signal503] .nil .nil)) (.node [signal122,signal182,signal260,signal362,signal463,signal491,signal503] (.node [signal122,signal182,signal260,signal362,signal438,signal463,signal503] .nil .nil) (.node [signal122,signal182,signal260,signal362,signal463,signal503] .nil .nil))) (.node [signal122,signal182,signal289,signal344,signal463,signal503] (.node [signal122,signal182,signal289,signal344,signal463,signal476,signal491] (.node [signal122,signal182,signal289,signal344,signal438,signal476,signal491] .nil .nil) (.node [signal122,signal182,signal289,signal344,signal463,signal491,signal503] .nil .nil)) (.node [signal122,signal182,signal290,signal344,signal438,signal463,signal491] (.node [signal122,signal182,signal289,signal344,signal476,signal491] .nil .nil) (.node [signal122,signal207,signal260,signal344,signal362,signal463,signal491] .nil .nil)))) (.node [signal142,signal182,signal260,signal344,signal463,signal476,signal491] (.node [signal122,signal208,signal260,signal344,signal438,signal463,signal491] (.node [signal122,signal207,signal260,signal362,signal438,signal463,signal491] (.node [signal122,signal207,signal260,signal344,signal476,signal491] (.node [signal122,signal207,signal260,signal344,signal463,signal476,signal491] .nil .nil) .nil) (.node [signal122,signal207,signal260,signal362,signal463,signal491] .nil .nil)) (.node [signal142,signal182,signal260,signal344,signal438,signal463,signal503] (.node [signal142,signal182,signal260,signal344,signal362,signal463,signal491] .nil .nil) (.node [signal142,signal182,signal260,signal344,signal438,signal476,signal491] .nil .nil))) (.node [signal142,signal182,signal260,signal362,signal438,signal463,signal491] (.node [signal142,signal182,signal260,signal344,signal463,signal503] (.node [signal142,signal182,signal260,signal344,signal463,signal491,signal503] .nil .nil) (.node [signal142,signal182,signal260,signal344,signal476,signal491] .nil .nil)) (.node [signal143,signal182,signal260,signal344,signal438,signal463,signal491] (.node [signal142,signal182,signal260,signal362,signal463,signal491] .nil .nil) (.node [signal224,signal309,signal344,signal412,signal438,signal463,signal491] .nil .nil)))))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok6 : everyKey (rowOK 5 layer5) layer6=true := by decide +kernel
theorem closed6 : Closed 6 layer6 := closed_next 5 (by decide) _ _ closed5 ok6
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
def layer7 : BinaryTree (List W) := (.node [signal83,signal122,signal182,signal260,signal344,signal438,signal463,signal491] (.node [signal53,signal122,signal148,signal182,signal260,signal344,signal463,signal491] (.node [signal34,signal53,signal122,signal182,signal260,signal344,signal463,signal491] (.node [signal18,signal53,signal122,signal182,signal260,signal344,signal463,signal491] (.node [signal9,signal53,signal122,signal182,signal260,signal344,signal463,signal491] (.node [signal6,signal53,signal122,signal182,signal260,signal344,signal463,signal491] (.node [signal3,signal53,signal122,signal182,signal260,signal344,signal463,signal491] (.node [signal1,signal53,signal122,signal182,signal260,signal344,signal463,signal491] (.node [signal0,signal53,signal122,signal182,signal260,signal344,signal463,signal491] .nil .nil) (.node [signal2,signal53,signal122,signal182,signal260,signal344,signal463,signal491] .nil .nil)) (.node [signal4,signal53,signal122,signal182,signal260,signal344,signal463,signal491] (.node [signal3,signal94,signal182,signal309,signal344,signal438,signal463,signal491] .nil .nil) (.node [signal5,signal53,signal122,signal182,signal260,signal344,signal463,signal491] .nil .nil))) (.node [signal7,signal94,signal182,signal309,signal344,signal438,signal463,signal491] (.node [signal7,signal53,signal122,signal182,signal260,signal344,signal463,signal491] (.node [signal6,signal122,signal182,signal260,signal344,signal420,signal438,signal463] .nil .nil) (.node [signal7,signal94,signal182,signal260,signal369,signal438,signal463,signal491] .nil .nil)) (.node [signal8,signal94,signal182,signal260,signal344,signal409,signal438,signal463] (.node [signal8,signal53,signal122,signal182,signal260,signal344,signal463,signal491] .nil .nil) (.node [signal8,signal94,signal182,signal309,signal344,signal438,signal463,signal491] .nil .nil)))) (.node [signal13,signal53,signal122,signal182,signal260,signal344,signal463,signal491] (.node [signal11,signal53,signal122,signal182,signal260,signal344,signal463,signal491] (.node [signal10,signal53,signal122,signal182,signal260,signal344,signal463,signal491] (.node [signal9,signal94,signal122,signal260,signal344,signal397,signal438,signal463] .nil .nil) (.node [signal10,signal94,signal122,signal182,signal390,signal438,signal463,signal491] .nil .nil)) (.node [signal12,signal43,signal94,signal122,signal182,signal260,signal344,signal463] (.node [signal11,signal94,signal122,signal182,signal344,signal382,signal438,signal463] .nil .nil) (.node [signal12,signal53,signal122,signal182,signal260,signal344,signal463,signal491] .nil .nil))) (.node [signal15,signal53,signal122,signal182,signal260,signal344,signal463,signal491] (.node [signal14,signal26,signal94,signal122,signal182,signal260,signal344,signal438] (.node [signal13,signal94,signal122,signal182,signal260,signal323,signal438,signal463] .nil .nil) (.node [signal14,signal53,signal122,signal182,signal260,signal344,signal463,signal491] .nil .nil)) (.node [signal17,signal53,signal122,signal182,signal260,signal344,signal463,signal491] (.node [signal16,signal53,signal122,signal182,signal260,signal344,signal463,signal491] .nil .nil) (.node [signal17,signal122,signal182,signal260,signal344,signal417,signal438,signal491] .nil .nil))))) (.node [signal25,signal41,signal94,signal122,signal182,signal260,signal344,signal491] (.node [signal21,signal53,signal122,signal182,signal260,signal344,signal463,signal491] (.node [signal19,signal94,signal182,signal309,signal344,signal438,signal463,signal491] (.node [signal19,signal53,signal122,signal182,signal260,signal344,signal463,signal491] (.node [signal18,signal94,signal224,signal260,signal344,signal438,signal463,signal491] .nil .nil) (.node [signal19,signal94,signal182,signal260,signal344,signal406,signal438,signal491] .nil .nil)) (.node [signal20,signal53,signal122,signal182,signal260,signal344,signal463,signal491] (.node [signal19,signal94,signal224,signal260,signal344,signal438,signal463,signal491] .nil .nil) (.node [signal20,signal94,signal122,signal316,signal344,signal438,signal463,signal491] .nil .nil))) (.node [signal23,signal53,signal122,signal182,signal260,signal344,signal463,signal491] (.node [signal22,signal53,signal122,signal182,signal260,signal344,signal463,signal491] (.node [signal21,signal94,signal122,signal182,signal344,signal379,signal438,signal491] .nil .nil) (.node [signal22,signal94,signal122,signal260,signal373,signal438,signal463,signal491] .nil .nil)) (.node [signal24,signal53,signal122,signal182,signal260,signal344,signal463,signal491] (.node [signal23,signal94,signal122,signal182,signal260,signal320,signal438,signal491] .nil .nil) (.node [signal24,signal94,signal122,signal260,signal344,signal395,signal438,signal491] .nil .nil)))) (.node [signal30,signal122,signal210,signal260,signal344,signal438,signal463,signal491] (.node [signal28,signal146,signal182,signal260,signal344,signal438,signal463,signal491] (.node [signal26,signal53,signal122,signal182,signal260,signal344,signal463,signal491] (.node [signal25,signal53,signal122,signal182,signal260,signal344,signal463,signal491] .nil .nil) (.node [signal28,signal53,signal122,signal182,signal260,signal344,signal463,signal491] .nil .nil)) (.node [signal29,signal94,signal182,signal260,signal344,signal401,signal463,signal491] (.node [signal29,signal53,signal122,signal182,signal260,signal344,signal463,signal491] .nil .nil) (.node [signal30,signal53,signal122,signal182,signal260,signal344,signal463,signal491] .nil .nil))) (.node [signal32,signal122,signal182,signal293,signal344,signal438,signal463,signal491] (.node [signal31,signal94,signal122,signal260,signal344,signal391,signal463,signal491] (.node [signal31,signal53,signal122,signal182,signal260,signal344,signal463,signal491] .nil .nil) (.node [signal32,signal53,signal122,signal182,signal260,signal344,signal463,signal491] .nil .nil)) (.node [signal33,signal94,signal122,signal182,signal344,signal374,signal463,signal491] (.node [signal33,signal53,signal122,signal182,signal260,signal344,signal463,signal491] .nil .nil) .nil))))) (.node [signal53,signal91,signal122,signal182,signal260,signal344,signal463,signal491] (.node [signal42,signal94,signal122,signal182,signal260,signal344,signal463,signal491] (.node [signal36,signal94,signal122,signal182,signal309,signal344,signal463,signal491] (.node [signal36,signal53,signal122,signal182,signal260,signal344,signal463,signal491] (.node [signal35,signal53,signal122,signal182,signal260,signal344,signal463,signal491] (.node [signal34,signal122,signal182,signal260,signal364,signal438,signal463,signal491] .nil .nil) (.node [signal35,signal94,signal122,signal182,signal260,signal317,signal463,signal491] .nil .nil)) (.node [signal36,signal94,signal122,signal182,signal238,signal344,signal463,signal491] (.node [signal36,signal94,signal122,signal159,signal260,signal344,signal463,signal491] .nil .nil) (.node [signal36,signal94,signal122,signal182,signal260,signal344,signal463,signal491] .nil .nil))) (.node [signal38,signal94,signal122,signal182,signal260,signal344,signal463,signal491] (.node [signal36,signal122,signal182,signal260,signal344,signal412,signal463,signal491] (.node [signal36,signal94,signal122,signal224,signal260,signal344,signal463,signal491] .nil .nil) (.node [signal37,signal94,signal122,signal182,signal260,signal344,signal463,signal491] .nil .nil)) (.node [signal40,signal94,signal122,signal182,signal260,signal344,signal463,signal491] (.node [signal39,signal94,signal122,signal182,signal260,signal344,signal463,signal491] .nil .nil) (.node [signal41,signal53,signal122,signal182,signal260,signal344,signal463,signal491] .nil .nil)))) (.node [signal52,signal53,signal122,signal182,signal260,signal344,signal463,signal491] (.node [signal48,signal53,signal122,signal182,signal260,signal344,signal463,signal491] (.node [signal44,signal94,signal122,signal182,signal260,signal344,signal463,signal491] (.node [signal43,signal53,signal122,signal182,signal260,signal344,signal463,signal491] .nil .nil) (.node [signal47,signal53,signal122,signal182,signal260,signal344,signal463,signal491] .nil .nil)) (.node [signal50,signal53,signal122,signal182,signal260,signal344,signal463,signal491] (.node [signal49,signal53,signal122,signal182,signal260,signal344,signal463,signal491] .nil .nil) (.node [signal51,signal53,signal122,signal182,signal260,signal344,signal463,signal491] .nil .nil))) (.node [signal53,signal81,signal122,signal182,signal260,signal344,signal463,signal491] (.node [signal53,signal72,signal122,signal182,signal260,signal344,signal463,signal491] (.node [signal53,signal53,signal122,signal182,signal260,signal344,signal463,signal491] .nil .nil) (.node [signal53,signal77,signal122,signal182,signal260,signal344,signal463,signal491] .nil .nil)) (.node [signal53,signal88,signal122,signal182,signal260,signal344,signal463,signal491] (.node [signal53,signal84,signal122,signal182,signal260,signal344,signal463,signal491] .nil .nil) .nil)))) (.node [signal53,signal94,signal122,signal224,signal260,signal344,signal463,signal491] (.node [signal53,signal94,signal122,signal182,signal260,signal344,signal428,signal463] (.node [signal53,signal94,signal122,signal182,signal238,signal344,signal463,signal491] (.node [signal53,signal94,signal122,signal159,signal260,signal344,signal463,signal491] (.node [signal53,signal94,signal117,signal182,signal260,signal344,signal463,signal491] .nil .nil) (.node [signal53,signal94,signal122,signal167,signal260,signal344,signal463,signal491] .nil .nil)) (.node [signal53,signal94,signal122,signal182,signal260,signal338,signal463,signal491] (.node [signal53,signal94,signal122,signal182,signal246,signal344,signal463,signal491] .nil .nil) (.node [signal53,signal94,signal122,signal182,signal260,signal344,signal424,signal491] .nil .nil))) (.node [signal53,signal94,signal122,signal182,signal260,signal362,signal463,signal491] (.node [signal53,signal94,signal122,signal182,signal260,signal344,signal463,signal503] (.node [signal53,signal94,signal122,signal182,signal260,signal344,signal463,signal491] .nil .nil) (.node [signal53,signal94,signal122,signal182,signal260,signal344,signal476,signal491] .nil .nil)) (.node [signal53,signal94,signal122,signal182,signal309,signal344,signal463,signal491] (.node [signal53,signal94,signal122,signal182,signal289,signal344,signal463,signal491] .nil .nil) (.node [signal53,signal94,signal122,signal207,signal260,signal344,signal463,signal491] .nil .nil)))) (.node [signal53,signal109,signal122,signal182,signal260,signal344,signal463,signal491] (.node [signal53,signal105,signal122,signal182,signal260,signal344,signal463,signal491] (.node [signal53,signal103,signal122,signal182,signal260,signal344,signal463,signal491] (.node [signal53,signal94,signal142,signal182,signal260,signal344,signal463,signal491] .nil .nil) (.node [signal53,signal104,signal122,signal182,signal260,signal344,signal463,signal491] .nil .nil)) (.node [signal53,signal107,signal122,signal182,signal260,signal344,signal463,signal491] (.node [signal53,signal106,signal122,signal182,signal260,signal344,signal463,signal491] .nil .nil) (.node [signal53,signal108,signal122,signal182,signal260,signal344,signal463,signal491] .nil .nil))) (.node [signal53,signal122,signal142,signal182,signal260,signal344,signal463,signal491] (.node [signal53,signal117,signal182,signal260,signal344,signal438,signal463,signal491] (.node [signal53,signal117,signal122,signal182,signal260,signal344,signal463,signal491] .nil .nil) (.node [signal53,signal117,signal182,signal260,signal344,signal463,signal491] .nil .nil)) (.node [signal53,signal122,signal147,signal182,signal260,signal344,signal463,signal491] (.node [signal53,signal122,signal146,signal182,signal260,signal344,signal463,signal491] .nil .nil) .nil)))))) (.node [signal53,signal122,signal182,signal260,signal344,signal424,signal491] (.node [signal53,signal122,signal182,signal260,signal320,signal344,signal463,signal491] (.node [signal53,signal122,signal182,signal228,signal260,signal344,signal463,signal491] (.node [signal53,signal122,signal167,signal260,signal344,signal438,signal463,signal491] (.node [signal53,signal122,signal159,signal182,signal260,signal344,signal463,signal491] (.node [signal53,signal122,signal152,signal182,signal260,signal344,signal463,signal491] (.node [signal53,signal122,signal149,signal182,signal260,signal344,signal463,signal491] .nil .nil) (.node [signal53,signal122,signal155,signal182,signal260,signal344,signal463,signal491] .nil .nil)) (.node [signal53,signal122,signal159,signal260,signal344,signal463,signal491] (.node [signal53,signal122,signal159,signal260,signal344,signal438,signal463,signal491] .nil .nil) (.node [signal53,signal122,signal167,signal182,signal260,signal344,signal463,signal491] .nil .nil))) (.node [signal53,signal122,signal182,signal210,signal260,signal344,signal463,signal491] (.node [signal53,signal122,signal173,signal182,signal260,signal344,signal463,signal491] (.node [signal53,signal122,signal167,signal260,signal344,signal463,signal491] .nil .nil) (.node [signal53,signal122,signal182,signal207,signal260,signal344,signal463,signal491] .nil .nil)) (.node [signal53,signal122,signal182,signal226,signal260,signal344,signal463,signal491] (.node [signal53,signal122,signal182,signal224,signal260,signal344,signal463,signal491] .nil .nil) (.node [signal53,signal122,signal182,signal227,signal260,signal344,signal463,signal491] .nil .nil)))) (.node [signal53,signal122,signal182,signal246,signal344,signal438,signal463,signal491] (.node [signal53,signal122,signal182,signal238,signal260,signal344,signal463,signal491] (.node [signal53,signal122,signal182,signal230,signal260,signal344,signal463,signal491] (.node [signal53,signal122,signal182,signal229,signal260,signal344,signal463,signal491] .nil .nil) (.node [signal53,signal122,signal182,signal231,signal260,signal344,signal463,signal491] .nil .nil)) (.node [signal53,signal122,signal182,signal238,signal344,signal463,signal491] (.node [signal53,signal122,signal182,signal238,signal344,signal438,signal463,signal491] .nil .nil) (.node [signal53,signal122,signal182,signal246,signal260,signal344,signal463,signal491] .nil .nil))) (.node [signal53,signal122,signal182,signal260,signal309,signal344,signal463,signal491] (.node [signal53,signal122,signal182,signal260,signal289,signal344,signal463,signal491] (.node [signal53,signal122,signal182,signal246,signal344,signal463,signal491] .nil .nil) (.node [signal53,signal122,signal182,signal260,signal293,signal344,signal463,signal491] .nil .nil)) (.node [signal53,signal122,signal182,signal260,signal317,signal344,signal463,signal491] (.node [signal53,signal122,signal182,signal260,signal316,signal344,signal463,signal491] .nil .nil) .nil)))) (.node [signal53,signal122,signal182,signal260,signal344,signal374,signal463,signal491] (.node [signal53,signal122,signal182,signal260,signal336,signal344,signal463,signal491] (.node [signal53,signal122,signal182,signal260,signal329,signal344,signal463,signal491] (.node [signal53,signal122,signal182,signal260,signal327,signal344,signal463,signal491] (.node [signal53,signal122,signal182,signal260,signal323,signal344,signal463,signal491] .nil .nil) (.node [signal53,signal122,signal182,signal260,signal328,signal344,signal463,signal491] .nil .nil)) (.node [signal53,signal122,signal182,signal260,signal331,signal344,signal463,signal491] (.node [signal53,signal122,signal182,signal260,signal330,signal344,signal463,signal491] .nil .nil) (.node [signal53,signal122,signal182,signal260,signal333,signal344,signal463,signal491] .nil .nil))) (.node [signal53,signal122,signal182,signal260,signal344,signal362,signal463,signal491] (.node [signal53,signal122,signal182,signal260,signal338,signal438,signal463,signal491] (.node [signal53,signal122,signal182,signal260,signal338,signal344,signal463,signal491] .nil .nil) (.node [signal53,signal122,signal182,signal260,signal338,signal463,signal491] .nil .nil)) (.node [signal53,signal122,signal182,signal260,signal344,signal369,signal463,signal491] (.node [signal53,signal122,signal182,signal260,signal344,signal364,signal463,signal491] .nil .nil) (.node [signal53,signal122,signal182,signal260,signal344,signal373,signal463,signal491] .nil .nil)))) (.node [signal53,signal122,signal182,signal260,signal344,signal406,signal463,signal491] (.node [signal53,signal122,signal182,signal260,signal344,signal391,signal463,signal491] (.node [signal53,signal122,signal182,signal260,signal344,signal382,signal463,signal491] (.node [signal53,signal122,signal182,signal260,signal344,signal379,signal463,signal491] .nil .nil) (.node [signal53,signal122,signal182,signal260,signal344,signal390,signal463,signal491] .nil .nil)) (.node [signal53,signal122,signal182,signal260,signal344,signal397,signal463,signal491] (.node [signal53,signal122,signal182,signal260,signal344,signal395,signal463,signal491] .nil .nil) (.node [signal53,signal122,signal182,signal260,signal344,signal401,signal463,signal491] .nil .nil))) (.node [signal53,signal122,signal182,signal260,signal344,signal420,signal463,signal491] (.node [signal53,signal122,signal182,signal260,signal344,signal412,signal463,signal491] (.node [signal53,signal122,signal182,signal260,signal344,signal409,signal463,signal491] .nil .nil) (.node [signal53,signal122,signal182,signal260,signal344,signal417,signal463,signal491] .nil .nil)) (.node [signal53,signal122,signal182,signal260,signal344,signal424,signal463,signal491] (.node [signal53,signal122,signal182,signal260,signal344,signal424,signal438,signal491] .nil .nil) .nil))))) (.node [signal53,signal122,signal182,signal260,signal344,signal463,signal503] (.node [signal53,signal122,signal182,signal260,signal344,signal463,signal477,signal491] (.node [signal53,signal122,signal182,signal260,signal344,signal438,signal476,signal491] (.node [signal53,signal122,signal182,signal260,signal344,signal432,signal463,signal491] (.node [signal53,signal122,signal182,signal260,signal344,signal428,signal463] (.node [signal53,signal122,signal182,signal260,signal344,signal428,signal438,signal463] .nil .nil) (.node [signal53,signal122,signal182,signal260,signal344,signal428,signal463,signal491] .nil .nil)) (.node [signal53,signal122,signal182,signal260,signal344,signal438,signal463,signal491] (.node [signal53,signal122,signal182,signal260,signal344,signal435,signal463,signal491] .nil .nil) (.node [signal53,signal122,signal182,signal260,signal344,signal438,signal463,signal503] .nil .nil))) (.node [signal53,signal122,signal182,signal260,signal344,signal456,signal463,signal491] (.node [signal53,signal122,signal182,signal260,signal344,signal451,signal463,signal491] (.node [signal53,signal122,signal182,signal260,signal344,signal449,signal463,signal491] .nil .nil) (.node [signal53,signal122,signal182,signal260,signal344,signal454,signal463,signal491] .nil .nil)) (.node [signal53,signal122,signal182,signal260,signal344,signal458,signal463,signal491] (.node [signal53,signal122,signal182,signal260,signal344,signal457,signal463,signal491] .nil .nil) (.node [signal53,signal122,signal182,signal260,signal344,signal463,signal476,signal491] .nil .nil)))) (.node [signal53,signal122,signal182,signal260,signal344,signal463,signal491,signal504] (.node [signal53,signal122,signal182,signal260,signal344,signal463,signal489,signal491] (.node [signal53,signal122,signal182,signal260,signal344,signal463,signal481,signal491] (.node [signal53,signal122,signal182,signal260,signal344,signal463,signal479,signal491] .nil .nil) (.node [signal53,signal122,signal182,signal260,signal344,signal463,signal486,signal491] .nil .nil)) (.node [signal53,signal122,signal182,signal260,signal344,signal463,signal491] (.node [signal53,signal122,signal182,signal260,signal344,signal463,signal490,signal491] .nil .nil) (.node [signal53,signal122,signal182,signal260,signal344,signal463,signal491,signal503] .nil .nil))) (.node [signal53,signal122,signal182,signal260,signal344,signal463,signal491,signal513] (.node [signal53,signal122,signal182,signal260,signal344,signal463,signal491,signal510] (.node [signal53,signal122,signal182,signal260,signal344,signal463,signal491,signal507] .nil .nil) (.node [signal53,signal122,signal182,signal260,signal344,signal463,signal491,signal512] .nil .nil)) (.node [signal53,signal122,signal182,signal260,signal344,signal463,signal491,signal515] (.node [signal53,signal122,signal182,signal260,signal344,signal463,signal491,signal514] .nil .nil) .nil)))) (.node [signal60,signal122,signal182,signal260,signal344,signal438,signal463,signal491] (.node [signal53,signal122,signal207,signal260,signal344,signal438,signal463,signal491] (.node [signal53,signal122,signal182,signal289,signal344,signal438,signal463,signal491] (.node [signal53,signal122,signal182,signal260,signal362,signal438,signal463,signal491] (.node [signal53,signal122,signal182,signal260,signal344,signal476,signal491] .nil .nil) (.node [signal53,signal122,signal182,signal260,signal362,signal463,signal491] .nil .nil)) (.node [signal53,signal122,signal182,signal309,signal344,signal438,signal463,signal491] (.node [signal53,signal122,signal182,signal289,signal344,signal463,signal491] .nil .nil) (.node [signal53,signal122,signal182,signal309,signal344,signal463,signal491] .nil .nil))) (.node [signal53,signal142,signal182,signal260,signal344,signal438,signal463,signal491] (.node [signal53,signal122,signal224,signal260,signal344,signal438,signal463,signal491] (.node [signal53,signal122,signal207,signal260,signal344,signal463,signal491] .nil .nil) (.node [signal53,signal122,signal224,signal260,signal344,signal463,signal491] .nil .nil)) (.node [signal55,signal122,signal182,signal260,signal344,signal438,signal463,signal491] (.node [signal53,signal142,signal182,signal260,signal344,signal463,signal491] .nil .nil) (.node [signal58,signal94,signal122,signal182,signal260,signal344,signal463,signal491] .nil .nil)))) (.node [signal76,signal122,signal182,signal260,signal344,signal438,signal463,signal491] (.node [signal71,signal122,signal182,signal260,signal344,signal438,signal463,signal491] (.node [signal66,signal122,signal182,signal260,signal344,signal438,signal463,signal491] (.node [signal63,signal94,signal122,signal182,signal260,signal344,signal463,signal491] .nil .nil) (.node [signal68,signal122,signal182,signal260,signal344,signal438,signal463,signal491] .nil .nil)) (.node [signal73,signal122,signal182,signal260,signal344,signal438,signal463,signal491] (.node [signal72,signal122,signal182,signal260,signal328,signal438,signal463,signal491] .nil .nil) (.node [signal74,signal122,signal182,signal260,signal344,signal438,signal463,signal491] .nil .nil))) (.node [signal80,signal122,signal182,signal260,signal344,signal438,signal463,signal491] (.node [signal78,signal122,signal182,signal260,signal344,signal438,signal463,signal491] (.node [signal77,signal122,signal182,signal227,signal344,signal438,signal463,signal491] .nil .nil) (.node [signal79,signal122,signal182,signal260,signal344,signal438,signal463,signal491] .nil .nil)) (.node [signal82,signal122,signal182,signal260,signal344,signal438,signal463,signal491] (.node [signal81,signal122,signal148,signal260,signal344,signal438,signal463,signal491] .nil .nil) .nil))))))) (.node [signal94,signal122,signal182,signal260,signal344,signal438,signal463,signal491] (.node [signal94,signal122,signal182,signal231,signal333,signal438,signal463,signal491] (.node [signal94,signal122,signal149,signal260,signal344,signal438,signal489,signal491] (.node [signal94,signal107,signal224,signal260,signal344,signal438,signal463,signal491] (.node [signal91,signal122,signal182,signal260,signal344,signal438,signal463,signal504] (.node [signal87,signal122,signal182,signal260,signal344,signal438,signal463,signal491] (.node [signal85,signal122,signal182,signal260,signal344,signal438,signal463,signal491] (.node [signal84,signal104,signal182,signal260,signal344,signal438,signal463,signal491] .nil .nil) (.node [signal86,signal122,signal182,signal260,signal344,signal438,signal463,signal491] .nil .nil)) (.node [signal89,signal122,signal182,signal260,signal344,signal438,signal463,signal491] (.node [signal88,signal122,signal182,signal260,signal344,signal438,signal477,signal491] .nil .nil) (.node [signal90,signal122,signal182,signal260,signal344,signal438,signal463,signal491] .nil .nil))) (.node [signal94,signal105,signal182,signal260,signal344,signal438,signal479,signal491] (.node [signal93,signal122,signal182,signal260,signal344,signal438,signal463,signal491] (.node [signal92,signal122,signal182,signal260,signal344,signal438,signal463,signal491] .nil .nil) (.node [signal94,signal103,signal182,signal260,signal344,signal449,signal463,signal491] .nil .nil)) (.node [signal94,signal106,signal182,signal309,signal344,signal438,signal463,signal491] (.node [signal94,signal106,signal159,signal260,signal344,signal438,signal463,signal491] .nil .nil) (.node [signal94,signal107,signal182,signal260,signal344,signal438,signal463,signal507] .nil .nil)))) (.node [signal94,signal113,signal182,signal260,signal344,signal438,signal463,signal491] (.node [signal94,signal109,signal224,signal260,signal344,signal438,signal463,signal491] (.node [signal94,signal108,signal224,signal260,signal344,signal438,signal463,signal491] (.node [signal94,signal108,signal182,signal260,signal336,signal438,signal463,signal491] .nil .nil) (.node [signal94,signal109,signal182,signal238,signal344,signal438,signal463,signal491] .nil .nil)) (.node [signal94,signal111,signal182,signal260,signal344,signal438,signal463,signal491] (.node [signal94,signal110,signal182,signal260,signal344,signal438,signal463,signal491] .nil .nil) (.node [signal94,signal112,signal182,signal260,signal344,signal438,signal463,signal491] .nil .nil))) (.node [signal94,signal117,signal182,signal260,signal344,signal438,signal463,signal491] (.node [signal94,signal115,signal182,signal260,signal344,signal438,signal463,signal491] (.node [signal94,signal114,signal182,signal260,signal344,signal438,signal463,signal491] .nil .nil) (.node [signal94,signal116,signal182,signal260,signal344,signal438,signal463,signal491] .nil .nil)) (.node [signal94,signal122,signal147,signal260,signal344,signal451,signal463,signal491] (.node [signal94,signal122,signal133,signal182,signal260,signal344,signal463,signal491] .nil .nil) .nil)))) (.node [signal94,signal122,signal165,signal260,signal344,signal438,signal463,signal491] (.node [signal94,signal122,signal157,signal260,signal344,signal438,signal463,signal491] (.node [signal94,signal122,signal153,signal260,signal344,signal438,signal463,signal491] (.node [signal94,signal122,signal151,signal182,signal260,signal344,signal438,signal491] (.node [signal94,signal122,signal150,signal260,signal344,signal438,signal463,signal491] .nil .nil) (.node [signal94,signal122,signal152,signal260,signal330,signal438,signal463,signal491] .nil .nil)) (.node [signal94,signal122,signal155,signal229,signal344,signal438,signal463,signal491] (.node [signal94,signal122,signal154,signal260,signal344,signal438,signal463,signal491] .nil .nil) (.node [signal94,signal122,signal156,signal260,signal344,signal438,signal463,signal491] .nil .nil))) (.node [signal94,signal122,signal161,signal260,signal344,signal438,signal463,signal491] (.node [signal94,signal122,signal159,signal260,signal344,signal438,signal463,signal491] (.node [signal94,signal122,signal159,signal238,signal344,signal438,signal463,signal491] .nil .nil) (.node [signal94,signal122,signal159,signal309,signal344,signal438,signal463,signal491] .nil .nil)) (.node [signal94,signal122,signal163,signal260,signal344,signal438,signal463,signal491] (.node [signal94,signal122,signal162,signal260,signal344,signal438,signal463,signal491] .nil .nil) (.node [signal94,signal122,signal164,signal260,signal344,signal438,signal463,signal491] .nil .nil)))) (.node [signal94,signal122,signal176,signal260,signal344,signal438,signal463,signal491] (.node [signal94,signal122,signal172,signal260,signal344,signal438,signal463,signal491] (.node [signal94,signal122,signal167,signal260,signal344,signal438,signal463,signal491] (.node [signal94,signal122,signal166,signal260,signal344,signal438,signal463,signal491] .nil .nil) (.node [signal94,signal122,signal171,signal260,signal344,signal438,signal463,signal491] .nil .nil)) (.node [signal94,signal122,signal174,signal260,signal344,signal438,signal463,signal491] (.node [signal94,signal122,signal173,signal260,signal344,signal438,signal463,signal510] .nil .nil) (.node [signal94,signal122,signal175,signal260,signal344,signal438,signal463,signal491] .nil .nil))) (.node [signal94,signal122,signal182,signal226,signal344,signal454,signal463,signal491] (.node [signal94,signal122,signal178,signal260,signal344,signal438,signal463,signal491] (.node [signal94,signal122,signal177,signal260,signal344,signal438,signal463,signal491] .nil .nil) (.node [signal94,signal122,signal182,signal196,signal260,signal344,signal463,signal491] .nil .nil)) (.node [signal94,signal122,signal182,signal230,signal344,signal438,signal463,signal512] (.node [signal94,signal122,signal182,signal228,signal344,signal438,signal481,signal491] .nil .nil) .nil))))) (.node [signal94,signal122,signal182,signal260,signal335,signal438,signal463,signal491] (.node [signal94,signal122,signal182,signal252,signal344,signal438,signal463,signal491] (.node [signal94,signal122,signal182,signal241,signal344,signal438,signal463,signal491] (.node [signal94,signal122,signal182,signal235,signal344,signal438,signal463,signal491] (.node [signal94,signal122,signal182,signal233,signal344,signal438,signal463,signal491] (.node [signal94,signal122,signal182,signal232,signal344,signal438,signal463,signal491] .nil .nil) (.node [signal94,signal122,signal182,signal234,signal344,signal438,signal463,signal491] .nil .nil)) (.node [signal94,signal122,signal182,signal238,signal344,signal438,signal463,signal491] (.node [signal94,signal122,signal182,signal236,signal344,signal438,signal463,signal491] .nil .nil) (.node [signal94,signal122,signal182,signal240,signal344,signal438,signal463,signal491] .nil .nil))) (.node [signal94,signal122,signal182,signal245,signal344,signal438,signal463,signal491] (.node [signal94,signal122,signal182,signal243,signal344,signal438,signal463,signal491] (.node [signal94,signal122,signal182,signal242,signal344,signal438,signal463,signal491] .nil .nil) (.node [signal94,signal122,signal182,signal244,signal344,signal438,signal463,signal491] .nil .nil)) (.node [signal94,signal122,signal182,signal250,signal344,signal438,signal463,signal491] (.node [signal94,signal122,signal182,signal246,signal344,signal438,signal463,signal491] .nil .nil) (.node [signal94,signal122,signal182,signal251,signal344,signal438,signal463,signal491] .nil .nil)))) (.node [signal94,signal122,signal182,signal260,signal321,signal344,signal438,signal491] (.node [signal94,signal122,signal182,signal256,signal344,signal438,signal463,signal491] (.node [signal94,signal122,signal182,signal254,signal344,signal438,signal463,signal491] (.node [signal94,signal122,signal182,signal253,signal344,signal438,signal463,signal491] .nil .nil) (.node [signal94,signal122,signal182,signal255,signal344,signal438,signal463,signal491] .nil .nil)) (.node [signal94,signal122,signal182,signal260,signal318,signal344,signal463,signal491] (.node [signal94,signal122,signal182,signal260,signal277,signal344,signal463,signal491] .nil .nil) (.node [signal94,signal122,signal182,signal260,signal319,signal344,signal463,signal491] .nil .nil))) (.node [signal94,signal122,signal182,signal260,signal331,signal438,signal463,signal514] (.node [signal94,signal122,signal182,signal260,signal327,signal456,signal463,signal491] (.node [signal94,signal122,signal182,signal260,signal322,signal344,signal438,signal491] .nil .nil) (.node [signal94,signal122,signal182,signal260,signal329,signal438,signal486,signal491] .nil .nil)) (.node [signal94,signal122,signal182,signal260,signal334,signal438,signal463,signal491] (.node [signal94,signal122,signal182,signal260,signal332,signal438,signal463,signal491] .nil .nil) .nil)))) (.node [signal94,signal122,signal182,signal260,signal344,signal404,signal463,signal491] (.node [signal94,signal122,signal182,signal260,signal344,signal377,signal463,signal491] (.node [signal94,signal122,signal182,signal260,signal344,signal351,signal438,signal463] (.node [signal94,signal122,signal182,signal260,signal338,signal438,signal463,signal491] (.node [signal94,signal122,signal182,signal260,signal337,signal438,signal463,signal491] .nil .nil) (.node [signal94,signal122,signal182,signal260,signal341,signal438,signal463,signal491] .nil .nil)) (.node [signal94,signal122,signal182,signal260,signal344,signal375,signal463,signal491] (.node [signal94,signal122,signal182,signal260,signal344,signal353,signal463,signal491] .nil .nil) (.node [signal94,signal122,signal182,signal260,signal344,signal376,signal463,signal491] .nil .nil))) (.node [signal94,signal122,signal182,signal260,signal344,signal393,signal463,signal491] (.node [signal94,signal122,signal182,signal260,signal344,signal385,signal438,signal463] (.node [signal94,signal122,signal182,signal260,signal344,signal380,signal438,signal491] .nil .nil) (.node [signal94,signal122,signal182,signal260,signal344,signal392,signal463,signal491] .nil .nil)) (.node [signal94,signal122,signal182,signal260,signal344,signal402,signal463,signal491] (.node [signal94,signal122,signal182,signal260,signal344,signal400,signal438,signal463] .nil .nil) (.node [signal94,signal122,signal182,signal260,signal344,signal403,signal463,signal491] .nil .nil)))) (.node [signal94,signal122,signal182,signal260,signal344,signal435,signal463,signal513] (.node [signal94,signal122,signal182,signal260,signal344,signal428,signal438,signal463] (.node [signal94,signal122,signal182,signal260,signal344,signal411,signal438,signal463] (.node [signal94,signal122,signal182,signal260,signal344,signal407,signal438,signal491] .nil .nil) (.node [signal94,signal122,signal182,signal260,signal344,signal424,signal438,signal491] .nil .nil)) (.node [signal94,signal122,signal182,signal260,signal344,signal433,signal463,signal491] (.node [signal94,signal122,signal182,signal260,signal344,signal432,signal490,signal491] .nil .nil) (.node [signal94,signal122,signal182,signal260,signal344,signal434,signal463,signal491] .nil .nil))) (.node [signal94,signal122,signal182,signal260,signal344,signal438,signal459,signal491] (.node [signal94,signal122,signal182,signal260,signal344,signal437,signal463,signal491] (.node [signal94,signal122,signal182,signal260,signal344,signal436,signal463,signal491] .nil .nil) (.node [signal94,signal122,signal182,signal260,signal344,signal438,signal458,signal515] .nil .nil)) (.node [signal94,signal122,signal182,signal260,signal344,signal438,signal463,signal482] (.node [signal94,signal122,signal182,signal260,signal344,signal438,signal460,signal491] .nil .nil) .nil)))))) (.node [signal94,signal122,signal193,signal260,signal344,signal438,signal463,signal491] (.node [signal94,signal122,signal182,signal260,signal362,signal438,signal463,signal491] (.node [signal94,signal122,signal182,signal260,signal344,signal439,signal463,signal491] (.node [signal94,signal122,signal182,signal260,signal344,signal438,signal468,signal491] (.node [signal94,signal122,signal182,signal260,signal344,signal438,signal463,signal506] (.node [signal94,signal122,signal182,signal260,signal344,signal438,signal463,signal503] (.node [signal94,signal122,signal182,signal260,signal344,signal438,signal463,signal497] .nil .nil) (.node [signal94,signal122,signal182,signal260,signal344,signal438,signal463,signal505] .nil .nil)) (.node [signal94,signal122,signal182,signal260,signal344,signal438,signal463,signal509] (.node [signal94,signal122,signal182,signal260,signal344,signal438,signal463,signal508] .nil .nil) (.node [signal94,signal122,signal182,signal260,signal344,signal438,signal463,signal511] .nil .nil))) (.node [signal94,signal122,signal182,signal260,signal344,signal438,signal480,signal491] (.node [signal94,signal122,signal182,signal260,signal344,signal438,signal476,signal491] (.node [signal94,signal122,signal182,signal260,signal344,signal438,signal470,signal491] .nil .nil) (.node [signal94,signal122,signal182,signal260,signal344,signal438,signal478,signal491] .nil .nil)) (.node [signal94,signal122,signal182,signal260,signal344,signal438,signal484,signal491] (.node [signal94,signal122,signal182,signal260,signal344,signal438,signal483,signal491] .nil .nil) (.node [signal94,signal122,signal182,signal260,signal344,signal438,signal485,signal491] .nil .nil)))) (.node [signal94,signal122,signal182,signal260,signal344,signal447,signal463,signal491] (.node [signal94,signal122,signal182,signal260,signal344,signal443,signal463,signal491] (.node [signal94,signal122,signal182,signal260,signal344,signal441,signal463,signal491] (.node [signal94,signal122,signal182,signal260,signal344,signal440,signal463,signal491] .nil .nil) (.node [signal94,signal122,signal182,signal260,signal344,signal442,signal463,signal491] .nil .nil)) (.node [signal94,signal122,signal182,signal260,signal344,signal445,signal463,signal491] (.node [signal94,signal122,signal182,signal260,signal344,signal444,signal463,signal491] .nil .nil) (.node [signal94,signal122,signal182,signal260,signal344,signal446,signal463,signal491] .nil .nil))) (.node [signal94,signal122,signal182,signal260,signal344,signal453,signal463,signal491] (.node [signal94,signal122,signal182,signal260,signal344,signal450,signal463,signal491] (.node [signal94,signal122,signal182,signal260,signal344,signal448,signal463,signal491] .nil .nil) (.node [signal94,signal122,signal182,signal260,signal344,signal452,signal463,signal491] .nil .nil)) (.node [signal94,signal122,signal182,signal260,signal348,signal438,signal463,signal491] (.node [signal94,signal122,signal182,signal260,signal344,signal455,signal463,signal491] .nil .nil) .nil)))) (.node [signal94,signal122,signal182,signal294,signal344,signal438,signal463,signal491] (.node [signal94,signal122,signal182,signal266,signal344,signal438,signal463,signal491] (.node [signal94,signal122,signal182,signal260,signal386,signal438,signal463,signal491] (.node [signal94,signal122,signal182,signal260,signal368,signal438,signal463,signal491] (.node [signal94,signal122,signal182,signal260,signal365,signal438,signal463,signal491] .nil .nil) (.node [signal94,signal122,signal182,signal260,signal371,signal438,signal463,signal491] .nil .nil)) (.node [signal94,signal122,signal182,signal264,signal344,signal438,signal463,signal491] (.node [signal94,signal122,signal182,signal260,signal389,signal438,signal463,signal491] .nil .nil) (.node [signal94,signal122,signal182,signal265,signal344,signal438,signal463,signal491] .nil .nil))) (.node [signal94,signal122,signal182,signal272,signal344,signal438,signal463,signal491] (.node [signal94,signal122,signal182,signal270,signal344,signal438,signal463,signal491] (.node [signal94,signal122,signal182,signal269,signal344,signal438,signal463,signal491] .nil .nil) (.node [signal94,signal122,signal182,signal271,signal344,signal438,signal463,signal491] .nil .nil)) (.node [signal94,signal122,signal182,signal274,signal344,signal438,signal463,signal491] (.node [signal94,signal122,signal182,signal273,signal344,signal438,signal463,signal491] .nil .nil) (.node [signal94,signal122,signal182,signal289,signal344,signal438,signal463,signal491] .nil .nil)))) (.node [signal94,signal122,signal182,signal344,signal383,signal438,signal463,signal491] (.node [signal94,signal122,signal182,signal301,signal344,signal438,signal463,signal491] (.node [signal94,signal122,signal182,signal297,signal344,signal438,signal463,signal491] (.node [signal94,signal122,signal182,signal295,signal344,signal438,signal463,signal491] .nil .nil) (.node [signal94,signal122,signal182,signal298,signal344,signal438,signal463,signal491] .nil .nil)) (.node [signal94,signal122,signal182,signal309,signal344,signal438,signal463,signal491] (.node [signal94,signal122,signal182,signal302,signal344,signal438,signal463,signal491] .nil .nil) (.node [signal94,signal122,signal182,signal311,signal344,signal438,signal463,signal491] .nil .nil))) (.node [signal94,signal122,signal189,signal260,signal344,signal438,signal463,signal491] (.node [signal94,signal122,signal185,signal260,signal344,signal438,signal463,signal491] (.node [signal94,signal122,signal182,signal344,signal388,signal438,signal463,signal491] .nil .nil) (.node [signal94,signal122,signal188,signal260,signal344,signal438,signal463,signal491] .nil .nil)) (.node [signal94,signal122,signal192,signal260,signal344,signal438,signal463,signal491] (.node [signal94,signal122,signal191,signal260,signal344,signal438,signal463,signal491] .nil .nil) .nil))))) (.node [signal94,signal182,signal309,signal344,signal438,signal463,signal491,signal507] (.node [signal94,signal122,signal260,signal344,signal396,signal438,signal463,signal491] (.node [signal94,signal122,signal222,signal260,signal344,signal438,signal463,signal491] (.node [signal94,signal122,signal212,signal260,signal344,signal438,signal463,signal491] (.node [signal94,signal122,signal207,signal260,signal344,signal438,signal463,signal491] (.node [signal94,signal122,signal194,signal260,signal344,signal438,signal463,signal491] .nil .nil) (.node [signal94,signal122,signal211,signal260,signal344,signal438,signal463,signal491] .nil .nil)) (.node [signal94,signal122,signal220,signal260,signal344,signal438,signal463,signal491] (.node [signal94,signal122,signal219,signal260,signal344,signal438,signal463,signal491] .nil .nil) (.node [signal94,signal122,signal221,signal260,signal344,signal438,signal463,signal491] .nil .nil))) (.node [signal94,signal122,signal260,signal313,signal344,signal438,signal463,signal491] (.node [signal94,signal122,signal224,signal260,signal344,signal438,signal463,signal491] (.node [signal94,signal122,signal224,signal238,signal344,signal438,signal463,signal491] .nil .nil) (.node [signal94,signal122,signal224,signal309,signal344,signal438,signal463,signal491] .nil .nil)) (.node [signal94,signal122,signal260,signal315,signal344,signal438,signal463,signal491] (.node [signal94,signal122,signal260,signal314,signal344,signal438,signal463,signal491] .nil .nil) (.node [signal94,signal122,signal260,signal344,signal372,signal438,signal463,signal491] .nil .nil)))) (.node [signal94,signal182,signal238,signal309,signal344,signal438,signal463,signal491] (.node [signal94,signal142,signal182,signal260,signal344,signal438,signal463,signal491] (.node [signal94,signal129,signal182,signal260,signal344,signal438,signal463,signal491] (.node [signal94,signal126,signal182,signal260,signal344,signal438,signal463,signal491] .nil .nil) (.node [signal94,signal130,signal182,signal260,signal344,signal438,signal463,signal491] .nil .nil)) (.node [signal94,signal182,signal213,signal260,signal344,signal438,signal463,signal491] (.node [signal94,signal159,signal224,signal260,signal344,signal438,signal463,signal491] .nil .nil) (.node [signal94,signal182,signal224,signal309,signal344,signal438,signal463,signal491] .nil .nil))) (.node [signal94,signal182,signal260,signal344,signal366,signal438,signal463,signal491] (.node [signal94,signal182,signal260,signal299,signal344,signal438,signal463,signal491] (.node [signal94,signal182,signal260,signal296,signal344,signal438,signal463,signal491] .nil .nil) (.node [signal94,signal182,signal260,signal300,signal344,signal438,signal463,signal491] .nil .nil)) (.node [signal94,signal182,signal309,signal344,signal438,signal463,signal479,signal491] (.node [signal94,signal182,signal309,signal336,signal344,signal438,signal463,signal491] .nil .nil) .nil)))) (.node [signal122,signal159,signal260,signal344,signal412,signal438,signal463,signal491] (.node [signal97,signal122,signal182,signal260,signal344,signal438,signal463,signal491] (.node [signal94,signal224,signal260,signal344,signal438,signal463,signal479,signal491] (.node [signal94,signal224,signal260,signal344,signal369,signal438,signal463,signal491] (.node [signal94,signal224,signal260,signal309,signal344,signal438,signal463,signal491] .nil .nil) (.node [signal94,signal224,signal260,signal344,signal409,signal438,signal463,signal491] .nil .nil)) (.node [signal95,signal122,signal182,signal260,signal344,signal438,signal463,signal491] (.node [signal94,signal224,signal309,signal344,signal438,signal463,signal491] .nil .nil) (.node [signal96,signal122,signal182,signal260,signal344,signal438,signal463,signal491] .nil .nil))) (.node [signal101,signal122,signal182,signal260,signal344,signal438,signal463,signal491] (.node [signal99,signal122,signal182,signal260,signal344,signal438,signal463,signal491] (.node [signal98,signal122,signal182,signal260,signal344,signal438,signal463,signal491] .nil .nil) (.node [signal100,signal122,signal182,signal260,signal344,signal438,signal463,signal491] .nil .nil)) (.node [signal122,signal144,signal182,signal260,signal344,signal438,signal463,signal491] (.node [signal102,signal122,signal182,signal260,signal344,signal438,signal463,signal491] .nil .nil) (.node [signal122,signal145,signal182,signal260,signal344,signal438,signal463,signal491] .nil .nil)))) (.node [signal122,signal182,signal260,signal344,signal414,signal438,signal463,signal491] (.node [signal122,signal182,signal260,signal292,signal344,signal438,signal463,signal491] (.node [signal122,signal182,signal238,signal344,signal412,signal438,signal463,signal491] (.node [signal122,signal182,signal209,signal260,signal344,signal438,signal463,signal491] .nil .nil) (.node [signal122,signal182,signal260,signal291,signal344,signal438,signal463,signal491] .nil .nil)) (.node [signal122,signal182,signal260,signal344,signal412,signal438,signal463,signal491] (.node [signal122,signal182,signal260,signal344,signal363,signal438,signal463,signal491] .nil .nil) (.node [signal122,signal182,signal260,signal344,signal413,signal438,signal463,signal491] .nil .nil))) (.node [signal122,signal182,signal260,signal344,signal422,signal438,signal463,signal491] (.node [signal122,signal182,signal260,signal344,signal416,signal438,signal463,signal491] (.node [signal122,signal182,signal260,signal344,signal415,signal438,signal463,signal491] .nil .nil) (.node [signal122,signal182,signal260,signal344,signal419,signal438,signal463,signal491] .nil .nil)) (.node [signal122,signal224,signal260,signal344,signal412,signal438,signal463,signal491] (.node [signal122,signal182,signal309,signal344,signal412,signal438,signal463,signal491] .nil .nil) .nil))))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok7 : everyKey (rowOK 6 layer6) layer7=true := by decide +kernel
theorem closed7 : Closed 7 layer7 := closed_next 6 (by decide) _ _ closed6 ok7
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
def layer8 : BinaryTree (List W) := (.node [signal94,signal122,signal182,signal226,signal260,signal344,signal438,signal463,signal491] (.node [signal41,signal94,signal122,signal182,signal260,signal344,signal438,signal463,signal491] (.node [signal22,signal94,signal122,signal182,signal260,signal344,signal438,signal463,signal491] (.node [signal12,signal94,signal122,signal182,signal260,signal344,signal438,signal463,signal491] (.node [signal8,signal94,signal122,signal182,signal260,signal344,signal438,signal463,signal491] (.node [signal6,signal94,signal122,signal182,signal260,signal344,signal438,signal463,signal491] (.node [signal3,signal94,signal122,signal182,signal260,signal344,signal438,signal463,signal491] .nil .nil) (.node [signal7,signal94,signal122,signal182,signal260,signal344,signal438,signal463,signal491] .nil .nil)) (.node [signal10,signal94,signal122,signal182,signal260,signal344,signal438,signal463,signal491] (.node [signal9,signal94,signal122,signal182,signal260,signal344,signal438,signal463,signal491] .nil .nil) (.node [signal11,signal94,signal122,signal182,signal260,signal344,signal438,signal463,signal491] .nil .nil))) (.node [signal18,signal94,signal122,signal182,signal260,signal344,signal438,signal463,signal491] (.node [signal14,signal94,signal122,signal182,signal260,signal344,signal438,signal463,signal491] (.node [signal13,signal94,signal122,signal182,signal260,signal344,signal438,signal463,signal491] .nil .nil) (.node [signal17,signal94,signal122,signal182,signal260,signal344,signal438,signal463,signal491] .nil .nil)) (.node [signal20,signal94,signal122,signal182,signal260,signal344,signal438,signal463,signal491] (.node [signal19,signal94,signal122,signal182,signal260,signal344,signal438,signal463,signal491] .nil .nil) (.node [signal21,signal94,signal122,signal182,signal260,signal344,signal438,signal463,signal491] .nil .nil)))) (.node [signal31,signal94,signal122,signal182,signal260,signal344,signal438,signal463,signal491] (.node [signal26,signal94,signal122,signal182,signal260,signal344,signal438,signal463,signal491] (.node [signal24,signal94,signal122,signal182,signal260,signal344,signal438,signal463,signal491] (.node [signal23,signal94,signal122,signal182,signal260,signal344,signal438,signal463,signal491] .nil .nil) (.node [signal25,signal94,signal122,signal182,signal260,signal344,signal438,signal463,signal491] .nil .nil)) (.node [signal29,signal94,signal122,signal182,signal260,signal344,signal438,signal463,signal491] (.node [signal28,signal94,signal122,signal182,signal260,signal344,signal438,signal463,signal491] .nil .nil) (.node [signal30,signal94,signal122,signal182,signal260,signal344,signal438,signal463,signal491] .nil .nil))) (.node [signal35,signal94,signal122,signal182,signal260,signal344,signal438,signal463,signal491] (.node [signal33,signal94,signal122,signal182,signal260,signal344,signal438,signal463,signal491] (.node [signal32,signal94,signal122,signal182,signal260,signal344,signal438,signal463,signal491] .nil .nil) (.node [signal34,signal94,signal122,signal182,signal260,signal344,signal438,signal463,signal491] .nil .nil)) (.node [signal36,signal94,signal122,signal182,signal260,signal344,signal463,signal491] (.node [signal36,signal94,signal122,signal182,signal260,signal344,signal438,signal463,signal491] .nil .nil) .nil)))) (.node [signal94,signal106,signal122,signal182,signal260,signal344,signal438,signal463,signal491] (.node [signal81,signal94,signal122,signal182,signal260,signal344,signal438,signal463,signal491] (.node [signal53,signal122,signal182,signal260,signal344,signal438,signal463,signal491] (.node [signal53,signal94,signal122,signal182,signal260,signal344,signal438,signal463,signal491] (.node [signal43,signal94,signal122,signal182,signal260,signal344,signal438,signal463,signal491] .nil .nil) (.node [signal53,signal94,signal122,signal182,signal260,signal344,signal463,signal491] .nil .nil)) (.node [signal72,signal94,signal122,signal182,signal260,signal344,signal438,signal463,signal491] (.node [signal53,signal122,signal182,signal260,signal344,signal463,signal491] .nil .nil) (.node [signal77,signal94,signal122,signal182,signal260,signal344,signal438,signal463,signal491] .nil .nil))) (.node [signal94,signal103,signal122,signal182,signal260,signal344,signal438,signal463,signal491] (.node [signal88,signal94,signal122,signal182,signal260,signal344,signal438,signal463,signal491] (.node [signal84,signal94,signal122,signal182,signal260,signal344,signal438,signal463,signal491] .nil .nil) (.node [signal91,signal94,signal122,signal182,signal260,signal344,signal438,signal463,signal491] .nil .nil)) (.node [signal94,signal105,signal122,signal182,signal260,signal344,signal438,signal463,signal491] (.node [signal94,signal104,signal122,signal182,signal260,signal344,signal438,signal463,signal491] .nil .nil) .nil))) (.node [signal94,signal122,signal152,signal182,signal260,signal344,signal438,signal463,signal491] (.node [signal94,signal122,signal146,signal182,signal260,signal344,signal438,signal463,signal491] (.node [signal94,signal108,signal122,signal182,signal260,signal344,signal438,signal463,signal491] (.node [signal94,signal107,signal122,signal182,signal260,signal344,signal438,signal463,signal491] .nil .nil) (.node [signal94,signal109,signal122,signal182,signal260,signal344,signal438,signal463,signal491] .nil .nil)) (.node [signal94,signal122,signal148,signal182,signal260,signal344,signal438,signal463,signal491] (.node [signal94,signal122,signal147,signal182,signal260,signal344,signal438,signal463,signal491] .nil .nil) (.node [signal94,signal122,signal149,signal182,signal260,signal344,signal438,signal463,signal491] .nil .nil))) (.node [signal94,signal122,signal173,signal182,signal260,signal344,signal438,signal463,signal491] (.node [signal94,signal122,signal159,signal182,signal260,signal344,signal438,signal463,signal491] (.node [signal94,signal122,signal155,signal182,signal260,signal344,signal438,signal463,signal491] .nil .nil) (.node [signal94,signal122,signal159,signal260,signal344,signal438,signal463,signal491] .nil .nil)) (.node [signal94,signal122,signal182,signal224,signal260,signal344,signal438,signal463,signal491] (.node [signal94,signal122,signal182,signal210,signal260,signal344,signal438,signal463,signal491] .nil .nil) .nil))))) (.node [signal94,signal122,signal182,signal260,signal344,signal401,signal438,signal463,signal491] (.node [signal94,signal122,signal182,signal260,signal329,signal344,signal438,signal463,signal491] (.node [signal94,signal122,signal182,signal260,signal293,signal344,signal438,signal463,signal491] (.node [signal94,signal122,signal182,signal230,signal260,signal344,signal438,signal463,signal491] (.node [signal94,signal122,signal182,signal228,signal260,signal344,signal438,signal463,signal491] (.node [signal94,signal122,signal182,signal227,signal260,signal344,signal438,signal463,signal491] .nil .nil) (.node [signal94,signal122,signal182,signal229,signal260,signal344,signal438,signal463,signal491] .nil .nil)) (.node [signal94,signal122,signal182,signal238,signal260,signal344,signal438,signal463,signal491] (.node [signal94,signal122,signal182,signal231,signal260,signal344,signal438,signal463,signal491] .nil .nil) (.node [signal94,signal122,signal182,signal238,signal344,signal438,signal463,signal491] .nil .nil))) (.node [signal94,signal122,signal182,signal260,signal320,signal344,signal438,signal463,signal491] (.node [signal94,signal122,signal182,signal260,signal316,signal344,signal438,signal463,signal491] (.node [signal94,signal122,signal182,signal260,signal309,signal344,signal438,signal463,signal491] .nil .nil) (.node [signal94,signal122,signal182,signal260,signal317,signal344,signal438,signal463,signal491] .nil .nil)) (.node [signal94,signal122,signal182,signal260,signal327,signal344,signal438,signal463,signal491] (.node [signal94,signal122,signal182,signal260,signal323,signal344,signal438,signal463,signal491] .nil .nil) (.node [signal94,signal122,signal182,signal260,signal328,signal344,signal438,signal463,signal491] .nil .nil)))) (.node [signal94,signal122,signal182,signal260,signal344,signal374,signal438,signal463,signal491] (.node [signal94,signal122,signal182,signal260,signal336,signal344,signal438,signal463,signal491] (.node [signal94,signal122,signal182,signal260,signal331,signal344,signal438,signal463,signal491] (.node [signal94,signal122,signal182,signal260,signal330,signal344,signal438,signal463,signal491] .nil .nil) (.node [signal94,signal122,signal182,signal260,signal333,signal344,signal438,signal463,signal491] .nil .nil)) (.node [signal94,signal122,signal182,signal260,signal344,signal369,signal438,signal463,signal491] (.node [signal94,signal122,signal182,signal260,signal344,signal364,signal438,signal463,signal491] .nil .nil) (.node [signal94,signal122,signal182,signal260,signal344,signal373,signal438,signal463,signal491] .nil .nil))) (.node [signal94,signal122,signal182,signal260,signal344,signal391,signal438,signal463,signal491] (.node [signal94,signal122,signal182,signal260,signal344,signal382,signal438,signal463,signal491] (.node [signal94,signal122,signal182,signal260,signal344,signal379,signal438,signal463,signal491] .nil .nil) (.node [signal94,signal122,signal182,signal260,signal344,signal390,signal438,signal463,signal491] .nil .nil)) (.node [signal94,signal122,signal182,signal260,signal344,signal397,signal438,signal463,signal491] (.node [signal94,signal122,signal182,signal260,signal344,signal395,signal438,signal463,signal491] .nil .nil) .nil)))) (.node [signal94,signal122,signal182,signal260,signal344,signal438,signal463,signal479,signal491] (.node [signal94,signal122,signal182,signal260,signal344,signal438,signal449,signal463,signal491] (.node [signal94,signal122,signal182,signal260,signal344,signal417,signal438,signal463,signal491] (.node [signal94,signal122,signal182,signal260,signal344,signal409,signal438,signal463,signal491] (.node [signal94,signal122,signal182,signal260,signal344,signal406,signal438,signal463,signal491] .nil .nil) (.node [signal94,signal122,signal182,signal260,signal344,signal412,signal438,signal463,signal491] .nil .nil)) (.node [signal94,signal122,signal182,signal260,signal344,signal432,signal438,signal463,signal491] (.node [signal94,signal122,signal182,signal260,signal344,signal420,signal438,signal463,signal491] .nil .nil) (.node [signal94,signal122,signal182,signal260,signal344,signal435,signal438,signal463,signal491] .nil .nil))) (.node [signal94,signal122,signal182,signal260,signal344,signal438,signal457,signal463,signal491] (.node [signal94,signal122,signal182,signal260,signal344,signal438,signal454,signal463,signal491] (.node [signal94,signal122,signal182,signal260,signal344,signal438,signal451,signal463,signal491] .nil .nil) (.node [signal94,signal122,signal182,signal260,signal344,signal438,signal456,signal463,signal491] .nil .nil)) (.node [signal94,signal122,signal182,signal260,signal344,signal438,signal463,signal477,signal491] (.node [signal94,signal122,signal182,signal260,signal344,signal438,signal458,signal463,signal491] .nil .nil) .nil))) (.node [signal94,signal122,signal182,signal260,signal344,signal438,signal463,signal491,signal512] (.node [signal94,signal122,signal182,signal260,signal344,signal438,signal463,signal490,signal491] (.node [signal94,signal122,signal182,signal260,signal344,signal438,signal463,signal486,signal491] (.node [signal94,signal122,signal182,signal260,signal344,signal438,signal463,signal481,signal491] .nil .nil) (.node [signal94,signal122,signal182,signal260,signal344,signal438,signal463,signal489,signal491] .nil .nil)) (.node [signal94,signal122,signal182,signal260,signal344,signal438,signal463,signal491,signal507] (.node [signal94,signal122,signal182,signal260,signal344,signal438,signal463,signal491,signal504] .nil .nil) (.node [signal94,signal122,signal182,signal260,signal344,signal438,signal463,signal491,signal510] .nil .nil))) (.node [signal94,signal122,signal182,signal309,signal344,signal438,signal463,signal491] (.node [signal94,signal122,signal182,signal260,signal344,signal438,signal463,signal491,signal514] (.node [signal94,signal122,signal182,signal260,signal344,signal438,signal463,signal491,signal513] .nil .nil) (.node [signal94,signal122,signal182,signal260,signal344,signal438,signal463,signal491,signal515] .nil .nil)) (.node [signal122,signal182,signal260,signal344,signal412,signal438,signal463,signal491] (.node [signal94,signal122,signal224,signal260,signal344,signal438,signal463,signal491] .nil .nil) .nil))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok8 : everyKey (rowOK 7 layer7) layer8=true := by decide +kernel
theorem closed8 : Closed 8 layer8 := closed_next 7 (by decide) _ _ closed7 ok8
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
def layer9 : BinaryTree (List W) := (.node [signal94,signal122,signal182,signal260,signal344,signal438,signal463,signal491] .nil .nil)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok9 : everyKey (rowOK 8 layer8) layer9=true := by decide +kernel
theorem closed9 : Closed 9 layer9 := closed_next 8 (by decide) _ _ closed8 ok9
def table : ℕ := 0xfefefcfcaaaa0000 + 0xfffefffcfffefffc * 2 ^ 64 + 0xffffffffffeeffcc * 2 ^ 128 + 0xfffffffffffefffc * 2 ^ 192
theorem row : ∀j : Fin 324, Nat.testBit table (∑i : Fin 8, if (ins.getD i.val 0)[j.val] then 2^(i:ℕ) else 0)=goal[j.val] := by decide +kernel
theorem reject : ∀z, z=goal ∨ z = ~~~goal → ¬build basicOps z 9 ins.toFinset := no_build 9 layer9 ins (by decide) (by decide) closed9 (by decide +kernel)
open PEqualNP.CircuitLowerBounds
def monoGates : List Gate := [⟨.or,[3,1]⟩,⟨.or,[6,7]⟩,⟨.and,[8,9]⟩,⟨.and,[0,4]⟩,⟨.or,[10,11]⟩,⟨.or,[2,7]⟩,⟨.and,[6,2]⟩,⟨.or,[13,1]⟩,⟨.or,[14,12]⟩,⟨.and,[5,15]⟩,⟨.or,[16,17]⟩]
theorem upper : ∃(gs : List Gate) (o : ℕ), (∀g∈gs,(g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2) ∧ gs.length=11 ∧ ∀x : Fin 8 → Bool,Circuit.eval ⟨gs,o⟩ (List.ofFn x)=Nat.testBit table (∑i : Fin 8,if x i then 2^(i:ℕ) else 0) := ⟨monoGates,18,by simp [monoGates],rfl,by decide +kernel⟩
theorem tableSpec : ∀x : Fin 8 → Bool, decide (∃ i < ([0, 4, 1, 5, 2, 5, 1, 6, 2, 6, 3, 6, 1, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 1, 6, 2, 6, 3, 6, 1, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 1, 6, 2, 6, 3, 6, 1, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) = Nat.testBit table (∑i : Fin 8,if x i then 2^(i:ℕ) else 0) := by decide +kernel
end PEqualNP.Outside.L_meta_14784

open PEqualNP.Outside.L_meta_14784 in
theorem PEqualNP.Outside.L_meta_14784 : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 5, 2, 5, 1, 6, 2, 6, 3, 6, 1, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 1, 6, 2, 6, 3, 6, 1, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 1, 6, 2, 6, 3, 6, 1, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 5, 2, 5, 1, 6, 2, 6, 3, 6, 1, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 1, 6, 2, 6, 3, 6, 1, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 1, 6, 2, 6, 3, 6, 1, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) := by
  intro gs o legalGates _ correct
  obtain ⟨ds,p,mono,size,ev⟩ := replace table 11 ins (by decide) row rfl reject upper gs o legalGates
    (fun x => (correct x).trans (tableSpec x))
  exact ⟨ds,p,mono,size,fun x => (ev x).trans (tableSpec x).symm⟩
