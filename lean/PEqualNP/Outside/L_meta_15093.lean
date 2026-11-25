import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_15093

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

-- The upper and lower halves represent opposite target labels on 34 pairs of assignments.
abbrev W := BitVec 68
-- Free complementation leaves four binary choices up to output polarity.
def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 34 := ((x >>> 34) ^^^ x).setWidth 34
def cuts (ws : List W) : BitVec 34 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 34) ++ (0 : BitVec 34)
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

def differs (i : Fin 34) (w : W) : Prop :=
  w.getLsbD (34+i.val) ≠ w.getLsbD i.val

theorem ops_differs (i : Fin 34) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 34+i.val < 68 := by omega
  have hi' : i.val < 68 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

theorem cuts_spec (ws : List W) (i : Fin 34) :
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
  change (cuts ws)[j] = (BitVec.allOnes 34)[j]
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
    ws.Nodup → ws.length ≤ 9 → containsKey ws tr = true → ¬ live basicOps g k ws.toFinset

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

theorem closed_next (k : Nat) (hk : k < 9) (tr next : BinaryTree (List W))
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
      have sz : (ordered (z :: kept)).length ≤ 9 := by rw [hp'.length_eq]; simp only [List.length_cons]; omega
      apply hnext g hg _ (hp'.nodup_iff.mpr hnd) sz (hy.2 _ mem)
      rwa [perm_set hp']
    rcases hm with direct | swap
    · exact go hp direct hs hz
    · exact go (hp.trans (.swap _ _ _)) swap (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)

def startOK (n : Nat) (tr : BinaryTree (List W)) (ws : List W) : Bool :=
  !(decide (ws.length ≤ n+1) && (cuts ws == -1)) || containsKey (ordered ws) tr

theorem no_build (n : Nat) (tr : BinaryTree (List W)) (ins : List W) (nd : ins.Nodup)
    (small : ins.length ≤ 9) (hc : Closed n tr) (hi : ins.sublists.all (startOK n tr) = true)
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
  · change reachable av (BitVec.allOnes 68 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 68)
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

private def bit (k : Fin 68) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 68) :
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
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 68) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> try simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#68)[k.val] = false; simp
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
    (row : ∀ j : Fin 68, Nat.testBit T (∑ i : Fin 6, if (ins.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val])
    (width : ins.length = 6) (rejection : ∀ z, z = goal ∨ z = ~~~goal → ¬ build basicOps z n ins.toFinset)
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) =
      Nat.testBit T (∑ i : Fin 6, if x i then 2^(i : ℕ) else 0)) : n < binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ ins, holds ins.toFinset u := fun u hu =>
    .inr (.inr ⟨u,List.mem_toFinset.mpr hu,.inl rfl⟩)
  have evaluate (k : Fin 68) :
      (gs.foldl step (ins.map (bit k))).getD o false = bit k goal := by
    let x (i : Fin 6) : Bool := bit k (ins.getD i.val 0)
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
    (row : ∀ j : Fin 68, Nat.testBit T (∑ i : Fin 6, if (ins.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val])
    (width : ins.length = 6) (rejection : ∀ z, z = goal ∨ z = ~~~goal → ¬ build basicOps z (m-2) ins.toFinset)
    (upper : ∃ (gs : List Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
      ∧ gs.length = m ∧ ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) =
        Nat.testBit T (∑ i : Fin 6, if x i then 2^(i : ℕ) else 0))
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) =
      Nat.testBit T (∑ i : Fin 6, if x i then 2^(i : ℕ) else 0)) :
    ∃ (ds : List Gate) (p : ℕ), (∀ g ∈ ds, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
      ∧ ds.length ≤ gs.length ∧ ∀ x : Fin 6 → Bool, Circuit.eval ⟨ds,p⟩ (List.ofFn x) =
        Nat.testBit T (∑ i : Fin 6, if x i then 2^(i : ℕ) else 0) := by
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

def signal0 : W := (0x0 : BitVec 34) ++ (0x290944a00 : BitVec 34)
def signal1 : W := (0x0 : BitVec 34) ++ (0x310844200 : BitVec 34)
def signal2 : W := (0x0 : BitVec 34) ++ (0x380904800 : BitVec 34)
def signal3 : W := (0x0 : BitVec 34) ++ (0x390004a00 : BitVec 34)
def signal4 : W := (0x0 : BitVec 34) ++ (0x390940000 : BitVec 34)
def signal5 : W := (0x0 : BitVec 34) ++ (0x390944a00 : BitVec 34)
def signal6 : W := (0x5351 : BitVec 34) ++ (0x7333 : BitVec 34)
def signal7 : W := (0x5c94 : BitVec 34) ++ (0x7c3c : BitVec 34)
def signal8 : W := (0x5fd5 : BitVec 34) ++ (0x35ff : BitVec 34)
def signal9 : W := (0x5fd5 : BitVec 34) ++ (0x4aff : BitVec 34)
def signal10 : W := (0x5fd5 : BitVec 34) ++ (0x77ff : BitVec 34)
def signal11 : W := (0x5fd5 : BitVec 34) ++ (0x7bff : BitVec 34)
def signal12 : W := (0x5fd5 : BitVec 34) ++ (0x7dff : BitVec 34)
def signal13 : W := (0x5fd5 : BitVec 34) ++ (0x7eff : BitVec 34)
def signal14 : W := (0x5fd5 : BitVec 34) ++ (0x7f3f : BitVec 34)
def signal15 : W := (0x5fd5 : BitVec 34) ++ (0x7fc0 : BitVec 34)
def signal16 : W := (0x5fd5 : BitVec 34) ++ (0x7fff : BitVec 34)
def signal17 : W := (0x5fd5 : BitVec 34) ++ (0x3909435ff : BitVec 34)
def signal18 : W := (0xa68022 : BitVec 34) ++ (0xe60033 : BitVec 34)
def signal19 : W := (0xb90028 : BitVec 34) ++ (0xf8003c : BitVec 34)
def signal20 : W := (0xbf802a : BitVec 34) ++ (0x6b803f : BitVec 34)
def signal21 : W := (0xbf802a : BitVec 34) ++ (0x95803f : BitVec 34)
def signal22 : W := (0xbf802a : BitVec 34) ++ (0xef803f : BitVec 34)
def signal23 : W := (0xbf802a : BitVec 34) ++ (0xf7803f : BitVec 34)
def signal24 : W := (0xbf802a : BitVec 34) ++ (0xfb803f : BitVec 34)
def signal25 : W := (0xbf802a : BitVec 34) ++ (0xfd803f : BitVec 34)
def signal26 : W := (0xbf802a : BitVec 34) ++ (0xfe003f : BitVec 34)
def signal27 : W := (0xbf802a : BitVec 34) ++ (0xff8000 : BitVec 34)
def signal28 : W := (0xbf802a : BitVec 34) ++ (0xff803f : BitVec 34)
def signal29 : W := (0xbf802a : BitVec 34) ++ (0x3906bca3f : BitVec 34)
def signal30 : W := (0xbfdfff : BitVec 34) ++ (0xffffc0 : BitVec 34)
def signal31 : W := (0x15000341 : BitVec 34) ++ (0x1f0003c0 : BitVec 34)
def signal32 : W := (0x15068002 : BitVec 34) ++ (0x1f078000 : BitVec 34)
def signal33 : W := (0x15068343 : BitVec 34) ++ (0xf0381c3 : BitVec 34)
def signal34 : W := (0x15068343 : BitVec 34) ++ (0x130582c3 : BitVec 34)
def signal35 : W := (0x15068343 : BitVec 34) ++ (0x1c060303 : BitVec 34)
def signal36 : W := (0x15068343 : BitVec 34) ++ (0x1f0383c3 : BitVec 34)
def signal37 : W := (0x15068343 : BitVec 34) ++ (0x1f0583c3 : BitVec 34)
def signal38 : W := (0x15068343 : BitVec 34) ++ (0x1f0781c3 : BitVec 34)
def signal39 : W := (0x15068343 : BitVec 34) ++ (0x1f0782c3 : BitVec 34)
def signal40 : W := (0x15068343 : BitVec 34) ++ (0x1f0783c0 : BitVec 34)
def signal41 : W := (0x15068343 : BitVec 34) ++ (0x1f0783c3 : BitVec 34)
def signal42 : W := (0x15068343 : BitVec 34) ++ (0x38f93c9c3 : BitVec 34)
def signal43 : W := (0x1506dc96 : BitVec 34) ++ (0x1f07fc3c : BitVec 34)
def signal44 : W := (0x15b90369 : BitVec 34) ++ (0x1ff803fc : BitVec 34)
def signal45 : W := (0xa2000c84 : BitVec 34) ++ (0xe3000cc0 : BitVec 34)
def signal46 : W := (0xa2190008 : BitVec 34) ++ (0xe3198000 : BitVec 34)
def signal47 : W := (0xa2190c8c : BitVec 34) ++ (0x630984cc : BitVec 34)
def signal48 : W := (0xa2190c8c : BitVec 34) ++ (0x831188cc : BitVec 34)
def signal49 : W := (0xa2190c8c : BitVec 34) ++ (0xe0180c0c : BitVec 34)
def signal50 : W := (0xa2190c8c : BitVec 34) ++ (0xe3098ccc : BitVec 34)
def signal51 : W := (0xa2190c8c : BitVec 34) ++ (0xe3118ccc : BitVec 34)
def signal52 : W := (0xa2190c8c : BitVec 34) ++ (0xe31984cc : BitVec 34)
def signal53 : W := (0xa2190c8c : BitVec 34) ++ (0xe31988cc : BitVec 34)
def signal54 : W := (0xa2190c8c : BitVec 34) ++ (0xe3198cc0 : BitVec 34)
def signal55 : W := (0xa2190c8c : BitVec 34) ++ (0xe3198ccc : BitVec 34)
def signal56 : W := (0xa2190c8c : BitVec 34) ++ (0x3738dc6cc : BitVec 34)
def signal57 : W := (0xa2195359 : BitVec 34) ++ (0xe319f333 : BitVec 34)
def signal58 : W := (0xa2a68ca6 : BitVec 34) ++ (0xe3e60cf3 : BitVec 34)
def signal59 : W := (0xb71f8fcf : BitVec 34) ++ (0xfc1e0f0f : BitVec 34)
def signal60 : W := (0x148402000 : BitVec 34) ++ (0x6c6a3500 : BitVec 34)
def signal61 : W := (0x148402000 : BitVec 34) ++ (0x10c623100 : BitVec 34)
def signal62 : W := (0x148402000 : BitVec 34) ++ (0x160683400 : BitVec 34)
def signal63 : W := (0x148402000 : BitVec 34) ++ (0x16c003500 : BitVec 34)
def signal64 : W := (0x148402000 : BitVec 34) ++ (0x16c6a0000 : BitVec 34)
def signal65 : W := (0x148402000 : BitVec 34) ++ (0x16c6a3500 : BitVec 34)
def signal66 : W := (0x148402000 : BitVec 34) ++ (0x2fcfe7f00 : BitVec 34)
def signal67 : W := (0x148407fd5 : BitVec 34) ++ (0x16c007fc0 : BitVec 34)
def signal68 : W := (0x148407fd5 : BitVec 34) ++ (0x16c6a4aff : BitVec 34)
def signal69 : W := (0x148ffa02a : BitVec 34) ++ (0x16c95b53f : BitVec 34)
def signal70 : W := (0x148ffa02a : BitVec 34) ++ (0x16cff8000 : BitVec 34)
def signal71 : W := (0x15d46a343 : BitVec 34) ++ (0x11c663303 : BitVec 34)
def signal72 : W := (0x15d46a343 : BitVec 34) ++ (0x1736db6c3 : BitVec 34)
def signal73 : W := (0x1ea592c8c : BitVec 34) ++ (0x18f73b9cc : BitVec 34)
def signal74 : W := (0x1ea592c8c : BitVec 34) ++ (0x1e0783c0c : BitVec 34)
def signal75 : W := (0x215a6d373 : BitVec 34) ++ (0x210844233 : BitVec 34)
def signal76 : W := (0x2a2b95cbc : BitVec 34) ++ (0x28090483c : BitVec 34)
def signal77 : W := (0x2b7005fd5 : BitVec 34) ++ (0x293004ac0 : BitVec 34)
def signal78 : W := (0x2b7bf802a : BitVec 34) ++ (0x293958000 : BitVec 34)
def signal79 : W := (0x2b7bfdfff : BitVec 34) ++ (0x30180ff : BitVec 34)
def signal80 : W := (0x2b7bfdfff : BitVec 34) ++ (0x301caff : BitVec 34)
def signal81 : W := (0x2b7bfdfff : BitVec 34) ++ (0x39580ff : BitVec 34)
def signal82 : W := (0x2b7bfdfff : BitVec 34) ++ (0x130582ff : BitVec 34)
def signal83 : W := (0x2b7bfdfff : BitVec 34) ++ (0x831188ff : BitVec 34)
def signal84 : W := (0x2b7bfdfff : BitVec 34) ++ (0x21385c2ff : BitVec 34)
def signal85 : W := (0x2b7bfdfff : BitVec 34) ++ (0x28391c8ff : BitVec 34)
def signal86 : W := (0x2b7bfdfff : BitVec 34) ++ (0x290944a3f : BitVec 34)
def signal87 : W := (0x2b7bfdfff : BitVec 34) ++ (0x29301caff : BitVec 34)
def signal88 : W := (0x2b7bfdfff : BitVec 34) ++ (0x2939580ff : BitVec 34)
def signal89 : W := (0x2b7bfdfff : BitVec 34) ++ (0x29395cac0 : BitVec 34)
def signal90 : W := (0x2b7bfdfff : BitVec 34) ++ (0x29395caff : BitVec 34)
def signal91 : W := (0x2b7bfdfff : BitVec 34) ++ (0x39395caff : BitVec 34)
def signal92 : W := (0x348e07030 : BitVec 34) ++ (0x300e07030 : BitVec 34)
def signal93 : W := (0x35d407351 : BitVec 34) ++ (0x31c007300 : BitVec 34)
def signal94 : W := (0x35d407fd5 : BitVec 34) ++ (0x31c007fc0 : BitVec 34)
def signal95 : W := (0x35d46f353 : BitVec 34) ++ (0x31c067303 : BitVec 34)
def signal96 : W := (0x35de6a022 : BitVec 34) ++ (0x31ce60000 : BitVec 34)
def signal97 : W := (0x35de6a363 : BitVec 34) ++ (0x31ce60303 : BitVec 34)
def signal98 : W := (0x35de6f373 : BitVec 34) ++ (0xc623133 : BitVec 34)
def signal99 : W := (0x35de6f373 : BitVec 34) ++ (0xc627333 : BitVec 34)
def signal100 : W := (0x35de6f373 : BitVec 34) ++ (0xce63133 : BitVec 34)
def signal101 : W := (0x35de6f373 : BitVec 34) ++ (0x1c663333 : BitVec 34)
def signal102 : W := (0x35de6f373 : BitVec 34) ++ (0x10c623133 : BitVec 34)
def signal103 : W := (0x35de6f373 : BitVec 34) ++ (0x21ce67333 : BitVec 34)
def signal104 : W := (0x35de6f373 : BitVec 34) ++ (0x30ce27133 : BitVec 34)
def signal105 : W := (0x35de6f373 : BitVec 34) ++ (0x310e47233 : BitVec 34)
def signal106 : W := (0x35de6f373 : BitVec 34) ++ (0x31c627333 : BitVec 34)
def signal107 : W := (0x35de6f373 : BitVec 34) ++ (0x31c847333 : BitVec 34)
def signal108 : W := (0x35de6f373 : BitVec 34) ++ (0x31ce63133 : BitVec 34)
def signal109 : W := (0x35de6f373 : BitVec 34) ++ (0x31ce64233 : BitVec 34)
def signal110 : W := (0x35de6f373 : BitVec 34) ++ (0x31ce67300 : BitVec 34)
def signal111 : W := (0x35de6f373 : BitVec 34) ++ (0x31ce67333 : BitVec 34)
def signal112 : W := (0x35de6f373 : BitVec 34) ++ (0x39ce67b33 : BitVec 34)
def signal113 : W := (0x35de6f373 : BitVec 34) ++ (0x39cf67333 : BitVec 34)
def signal114 : W := (0x35de6f373 : BitVec 34) ++ (0x39cf67b33 : BitVec 34)
def signal115 : W := (0x35de6fff7 : BitVec 34) ++ (0x31ce67f3f : BitVec 34)
def signal116 : W := (0x35dffa02a : BitVec 34) ++ (0x31cff8000 : BitVec 34)
def signal117 : W := (0x35dfff37b : BitVec 34) ++ (0x31cfe733f : BitVec 34)
def signal118 : W := (0x3ea407c94 : BitVec 34) ++ (0x3e0007c00 : BitVec 34)
def signal119 : W := (0x3ea407fd5 : BitVec 34) ++ (0x3e0007fc0 : BitVec 34)
def signal120 : W := (0x3ea597c9c : BitVec 34) ++ (0x3e0187c0c : BitVec 34)
def signal121 : W := (0x3eaf92028 : BitVec 34) ++ (0x3e0f80000 : BitVec 34)
def signal122 : W := (0x3eaf92cac : BitVec 34) ++ (0x3e0f80c0c : BitVec 34)
def signal123 : W := (0x3eaf97cbc : BitVec 34) ++ (0x6068343c : BitVec 34)
def signal124 : W := (0x3eaf97cbc : BitVec 34) ++ (0x60687c3c : BitVec 34)
def signal125 : W := (0x3eaf97cbc : BitVec 34) ++ (0x60f8343c : BitVec 34)
def signal126 : W := (0x3eaf97cbc : BitVec 34) ++ (0xe0783c3c : BitVec 34)
def signal127 : W := (0x3eaf97cbc : BitVec 34) ++ (0x16068343c : BitVec 34)
def signal128 : W := (0x3eaf97cbc : BitVec 34) ++ (0x2e0f87c3c : BitVec 34)
def signal129 : W := (0x3eaf97cbc : BitVec 34) ++ (0x360e8743c : BitVec 34)
def signal130 : W := (0x3eaf97cbc : BitVec 34) ++ (0x380f0783c : BitVec 34)
def signal131 : W := (0x3eaf97cbc : BitVec 34) ++ (0x3e0687c3c : BitVec 34)
def signal132 : W := (0x3eaf97cbc : BitVec 34) ++ (0x3e0907c3c : BitVec 34)
def signal133 : W := (0x3eaf97cbc : BitVec 34) ++ (0x3e0f8343c : BitVec 34)
def signal134 : W := (0x3eaf97cbc : BitVec 34) ++ (0x3e0f8483c : BitVec 34)
def signal135 : W := (0x3eaf97cbc : BitVec 34) ++ (0x3e0f87c00 : BitVec 34)
def signal136 : W := (0x3eaf97cbc : BitVec 34) ++ (0x3e0f87c3c : BitVec 34)
def signal137 : W := (0x3eaf97cbc : BitVec 34) ++ (0x3f0f87e3c : BitVec 34)
def signal138 : W := (0x3eaf97cbc : BitVec 34) ++ (0x3f0fc7c3c : BitVec 34)
def signal139 : W := (0x3eaf97cbc : BitVec 34) ++ (0x3f0fc7e3c : BitVec 34)
def signal140 : W := (0x3eaf97ffd : BitVec 34) ++ (0x3e0f87f3f : BitVec 34)
def signal141 : W := (0x3eaffa02a : BitVec 34) ++ (0x3e0ff8000 : BitVec 34)
def signal142 : W := (0x3eafffcbe : BitVec 34) ++ (0x3e0fe7c3f : BitVec 34)
def signal143 : W := (0x3ff402000 : BitVec 34) ++ (0x3ff000000 : BitVec 34)
def signal144 : W := (0x3ff407fd5 : BitVec 34) ++ (0x6f0035c0 : BitVec 34)
def signal145 : W := (0x3ff407fd5 : BitVec 34) ++ (0x6f007fc0 : BitVec 34)
def signal146 : W := (0x3ff407fd5 : BitVec 34) ++ (0x7f0037c0 : BitVec 34)
def signal147 : W := (0x3ff407fd5 : BitVec 34) ++ (0xef003dc0 : BitVec 34)
def signal148 : W := (0x3ff407fd5 : BitVec 34) ++ (0x16f0035c0 : BitVec 34)
def signal149 : W := (0x3ff407fd5 : BitVec 34) ++ (0x2ff007fc0 : BitVec 34)
def signal150 : W := (0x3ff407fd5 : BitVec 34) ++ (0x37f0077c0 : BitVec 34)
def signal151 : W := (0x3ff407fd5 : BitVec 34) ++ (0x39f007bc0 : BitVec 34)
def signal152 : W := (0x3ff407fd5 : BitVec 34) ++ (0x3ef007dc0 : BitVec 34)
def signal153 : W := (0x3ff407fd5 : BitVec 34) ++ (0x3f3007ec0 : BitVec 34)
def signal154 : W := (0x3ff407fd5 : BitVec 34) ++ (0x3fc007f00 : BitVec 34)
def signal155 : W := (0x3ff407fd5 : BitVec 34) ++ (0x3ff0035c0 : BitVec 34)
def signal156 : W := (0x3ff407fd5 : BitVec 34) ++ (0x3ff004ac0 : BitVec 34)
def signal157 : W := (0x3ff407fd5 : BitVec 34) ++ (0x3ff007fc0 : BitVec 34)
def signal158 : W := (0x3ff407fd5 : BitVec 34) ++ (0x3ff847fc0 : BitVec 34)
def signal159 : W := (0x3ff407fd5 : BitVec 34) ++ (0x3ff907fc0 : BitVec 34)
def signal160 : W := (0x3ff407fd5 : BitVec 34) ++ (0x3ff947fc0 : BitVec 34)
def signal161 : W := (0x3ff46ffd7 : BitVec 34) ++ (0x3ff07ffc0 : BitVec 34)
def signal162 : W := (0x3ff597fdd : BitVec 34) ++ (0x3ff19ffc0 : BitVec 34)
def signal163 : W := (0x3ffe6fff7 : BitVec 34) ++ (0x3ffe67ff3 : BitVec 34)
def signal164 : W := (0x3fff97ffd : BitVec 34) ++ (0x3fff87ffc : BitVec 34)
def signal165 : W := (0x3ffffa02a : BitVec 34) ++ (0x6f6b8000 : BitVec 34)
def signal166 : W := (0x3ffffa02a : BitVec 34) ++ (0x6fff8000 : BitVec 34)
def signal167 : W := (0x3ffffa02a : BitVec 34) ++ (0x7f6f8000 : BitVec 34)
def signal168 : W := (0x3ffffa02a : BitVec 34) ++ (0xef7b8000 : BitVec 34)
def signal169 : W := (0x3ffffa02a : BitVec 34) ++ (0x16f6b8000 : BitVec 34)
def signal170 : W := (0x3ffffa02a : BitVec 34) ++ (0x2ffff8000 : BitVec 34)
def signal171 : W := (0x3ffffa02a : BitVec 34) ++ (0x37fef8000 : BitVec 34)
def signal172 : W := (0x3ffffa02a : BitVec 34) ++ (0x39ff78000 : BitVec 34)
def signal173 : W := (0x3ffffa02a : BitVec 34) ++ (0x3effb8000 : BitVec 34)
def signal174 : W := (0x3ffffa02a : BitVec 34) ++ (0x3f3fd8000 : BitVec 34)
def signal175 : W := (0x3ffffa02a : BitVec 34) ++ (0x3fcfe0000 : BitVec 34)
def signal176 : W := (0x3ffffa02a : BitVec 34) ++ (0x3ff6b8000 : BitVec 34)
def signal177 : W := (0x3ffffa02a : BitVec 34) ++ (0x3ff958000 : BitVec 34)
def signal178 : W := (0x3ffffa02a : BitVec 34) ++ (0x3ffff8000 : BitVec 34)
def signal179 : W := (0x3ffffa02a : BitVec 34) ++ (0x3ffffc200 : BitVec 34)
def signal180 : W := (0x3ffffa02a : BitVec 34) ++ (0x3ffffc800 : BitVec 34)
def signal181 : W := (0x3ffffa02a : BitVec 34) ++ (0x3ffffca00 : BitVec 34)
def signal182 : W := (0x3ffffa36b : BitVec 34) ++ (0x3ffff83c0 : BitVec 34)
def signal183 : W := (0x3ffffacae : BitVec 34) ++ (0x3ffff8cc0 : BitVec 34)
def signal184 : W := (0x3fffff37b : BitVec 34) ++ (0x3fffff333 : BitVec 34)
def signal185 : W := (0x3fffffcbe : BitVec 34) ++ (0x3fffffc3c : BitVec 34)
def signal186 : W := (0x3ffffffff : BitVec 34) ++ (0xc62313f : BitVec 34)
def signal187 : W := (0x3ffffffff : BitVec 34) ++ (0xf63b1ff : BitVec 34)
def signal188 : W := (0x3ffffffff : BitVec 34) ++ (0x6068343f : BitVec 34)
def signal189 : W := (0x3ffffffff : BitVec 34) ++ (0x6369b4ff : BitVec 34)
def signal190 : W := (0x3ffffffff : BitVec 34) ++ (0x6c6a353f : BitVec 34)
def signal191 : W := (0x3ffffffff : BitVec 34) ++ (0x6f01b5c0 : BitVec 34)
def signal192 : W := (0x3ffffffff : BitVec 34) ++ (0x6f01b5ff : BitVec 34)
def signal193 : W := (0x3ffffffff : BitVec 34) ++ (0x6f6b80c0 : BitVec 34)
def signal194 : W := (0x3ffffffff : BitVec 34) ++ (0x6f6b80ff : BitVec 34)
def signal195 : W := (0x3ffffffff : BitVec 34) ++ (0x6f6bb5c0 : BitVec 34)
def signal196 : W := (0x3ffffffff : BitVec 34) ++ (0x6f6bb5ff : BitVec 34)
def signal197 : W := (0x3ffffffff : BitVec 34) ++ (0x2ffffffff : BitVec 34)
def signal198 : W := (0x3ffffffff : BitVec 34) ++ (0x37feff7ff : BitVec 34)
def signal199 : W := (0x3ffffffff : BitVec 34) ++ (0x39cf67b3f : BitVec 34)
def signal200 : W := (0x3ffffffff : BitVec 34) ++ (0x39ff7fbff : BitVec 34)
def signal201 : W := (0x3ffffffff : BitVec 34) ++ (0x3effbfdff : BitVec 34)
def signal202 : W := (0x3ffffffff : BitVec 34) ++ (0x3f0fc7e3f : BitVec 34)
def signal203 : W := (0x3ffffffff : BitVec 34) ++ (0x3f3fdfeff : BitVec 34)
def signal204 : W := (0x3ffffffff : BitVec 34) ++ (0x3fcfe7f3f : BitVec 34)
def signal205 : W := (0x3ffffffff : BitVec 34) ++ (0x3ff6bffff : BitVec 34)
def signal206 : W := (0x3ffffffff : BitVec 34) ++ (0x3ff95ffc0 : BitVec 34)
def signal207 : W := (0x3ffffffff : BitVec 34) ++ (0x3ff95ffff : BitVec 34)
def signal208 : W := (0x3ffffffff : BitVec 34) ++ (0x3ffffb5ff : BitVec 34)
def signal209 : W := (0x3ffffffff : BitVec 34) ++ (0x3ffffcac0 : BitVec 34)
def signal210 : W := (0x3ffffffff : BitVec 34) ++ (0x3ffffcaff : BitVec 34)
def signal211 : W := (0x3ffffffff : BitVec 34) ++ (0x3ffffffc0 : BitVec 34)

def ins : List W := [signal196,signal90,signal111,signal136,signal157,signal178]
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
def layer4 : BinaryTree (List W) := (.node [signal79,signal103,signal136,signal157,signal178] (.node [signal58,signal90,signal136,signal178,signal196] (.node [signal33,signal79,signal111,signal144,signal178] (.node [signal20,signal79,signal111,signal123,signal178] (.node [signal8,signal90,signal98,signal123,signal157] (.node [signal8,signal79,signal111,signal123,signal157] (.node [signal8,signal79,signal98,signal136,signal157] .nil .nil) (.node [signal8,signal79,signal111,signal136,signal144] .nil .nil)) (.node [signal20,signal79,signal98,signal136,signal178] (.node [signal17,signal90,signal111,signal136,signal157] .nil .nil) .nil)) (.node [signal29,signal90,signal111,signal136,signal178] (.node [signal20,signal90,signal98,signal123,signal178] (.node [signal20,signal79,signal111,signal136,signal165] .nil .nil) .nil) (.node [signal33,signal79,signal98,signal157,signal178] (.node [signal30,signal90,signal111,signal136,signal196] .nil .nil) .nil))) (.node [signal47,signal79,signal123,signal157,signal178] (.node [signal42,signal90,signal111,signal157,signal178] (.node [signal33,signal90,signal111,signal144,signal165] (.node [signal33,signal79,signal111,signal157,signal165] .nil .nil) .nil) (.node [signal44,signal90,signal111,signal178,signal196] (.node [signal43,signal90,signal111,signal157,signal196] .nil .nil) .nil)) (.node [signal47,signal90,signal136,signal144,signal165] (.node [signal47,signal79,signal136,signal157,signal165] (.node [signal47,signal79,signal136,signal144,signal178] .nil .nil) .nil) (.node [signal57,signal90,signal136,signal157,signal196] (.node [signal56,signal90,signal136,signal157,signal178] .nil .nil) .nil)))) (.node [signal76,signal111,signal157,signal178,signal189] (.node [signal69,signal111,signal136,signal178,signal196] (.node [signal60,signal111,signal136,signal144,signal165] (.node [signal60,signal98,signal123,signal157,signal178] (.node [signal59,signal90,signal157,signal178,signal196] .nil .nil) .nil) (.node [signal68,signal111,signal136,signal157,signal196] (.node [signal66,signal111,signal136,signal157,signal178] .nil .nil) .nil)) (.node [signal75,signal130,signal157,signal178,signal196] (.node [signal73,signal136,signal157,signal178,signal196] (.node [signal72,signal111,signal157,signal178,signal196] .nil .nil) .nil) (.node [signal76,signal105,signal157,signal178,signal196] (.node [signal75,signal136,signal157,signal178,signal187] .nil .nil) .nil))) (.node [signal79,signal98,signal136,signal144,signal178] (.node [signal78,signal111,signal136,signal156,signal196] (.node [signal77,signal111,signal136,signal178,signal192] (.node [signal77,signal111,signal136,signal177,signal196] .nil .nil) .nil) (.node [signal79,signal98,signal123,signal157,signal178] (.node [signal78,signal111,signal136,signal157,signal194] .nil .nil) .nil)) (.node [signal79,signal99,signal136,signal157,signal178] (.node [signal79,signal98,signal136,signal157,signal178] (.node [signal79,signal98,signal136,signal157,signal165] .nil .nil) .nil) (.node [signal79,signal101,signal136,signal157,signal178] (.node [signal79,signal100,signal136,signal157,signal178] .nil .nil) .nil))))) (.node [signal86,signal92,signal157,signal178,signal196] (.node [signal79,signal111,signal136,signal149,signal178] (.node [signal79,signal111,signal128,signal157,signal178] (.node [signal79,signal111,signal124,signal157,signal178] (.node [signal79,signal111,signal123,signal157,signal165] (.node [signal79,signal111,signal123,signal144,signal178] .nil .nil) (.node [signal79,signal111,signal123,signal157,signal178] .nil .nil)) (.node [signal79,signal111,signal126,signal157,signal178] (.node [signal79,signal111,signal125,signal157,signal178] .nil .nil) .nil)) (.node [signal79,signal111,signal136,signal145,signal178] (.node [signal79,signal111,signal136,signal144,signal178] (.node [signal79,signal111,signal136,signal144,signal165] .nil .nil) .nil) (.node [signal79,signal111,signal136,signal147,signal178] (.node [signal79,signal111,signal136,signal146,signal178] .nil .nil) .nil))) (.node [signal80,signal111,signal136,signal144,signal178] (.node [signal79,signal111,signal136,signal157,signal167] (.node [signal79,signal111,signal136,signal157,signal166] (.node [signal79,signal111,signal136,signal157,signal165] .nil .nil) .nil) (.node [signal79,signal111,signal136,signal157,signal170] (.node [signal79,signal111,signal136,signal157,signal168] .nil .nil) .nil)) (.node [signal83,signal111,signal123,signal157,signal178] (.node [signal82,signal98,signal136,signal157,signal178] (.node [signal81,signal111,signal136,signal157,signal165] .nil .nil) .nil) (.node [signal85,signal111,signal123,signal157,signal178] (.node [signal84,signal98,signal136,signal157,signal178] .nil .nil) .nil)))) (.node [signal90,signal104,signal123,signal157,signal178] (.node [signal90,signal98,signal123,signal157,signal165] (.node [signal89,signal111,signal136,signal143,signal196] (.node [signal88,signal111,signal136,signal157,signal165] (.node [signal87,signal111,signal136,signal144,signal178] .nil .nil) .nil) (.node [signal90,signal98,signal123,signal144,signal178] (.node [signal90,signal92,signal157,signal178,signal190] .nil .nil) .nil)) (.node [signal90,signal98,signal129,signal157,signal178] (.node [signal90,signal98,signal127,signal157,signal178] (.node [signal90,signal98,signal123,signal157,signal178] .nil .nil) .nil) (.node [signal90,signal102,signal123,signal157,signal178] (.node [signal90,signal98,signal136,signal144,signal165] .nil .nil) .nil))) (.node [signal90,signal111,signal136,signal148,signal165] (.node [signal90,signal111,signal136,signal144,signal165] (.node [signal90,signal111,signal136,signal143,signal195] (.node [signal90,signal111,signal123,signal144,signal165] .nil .nil) .nil) (.node [signal90,signal111,signal136,signal144,signal176] (.node [signal90,signal111,signal136,signal144,signal169] .nil .nil) .nil)) (.node [signal90,signal111,signal136,signal178,signal191] (.node [signal90,signal111,signal136,signal157,signal193] (.node [signal90,signal111,signal136,signal155,signal165] .nil .nil) .nil) (.node [signal90,signal136,signal157,signal178,signal186] (.node [signal90,signal111,signal157,signal178,signal188] .nil .nil) .nil))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok4 : everyKey (rowOK 3 layer3) layer4=true := by decide +kernel
theorem closed4 : Closed 4 layer4 := closed_next 3 (by decide) _ _ closed3 ok4
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
def layer5 : BinaryTree (List W) := (.node [signal82,signal111,signal136,signal157,signal178,signal196] (.node [signal33,signal90,signal111,signal123,signal157,signal178] (.node [signal9,signal64,signal111,signal136,signal157,signal196] (.node [signal4,signal79,signal111,signal136,signal157,signal178] (.node [signal1,signal90,signal111,signal123,signal157,signal178] (.node [signal0,signal90,signal111,signal136,signal144,signal178] (.node [signal0,signal90,signal98,signal136,signal157,signal178] (.node [signal0,signal60,signal111,signal136,signal157,signal178] .nil .nil) (.node [signal0,signal90,signal111,signal123,signal157,signal178] .nil .nil)) (.node [signal1,signal47,signal90,signal136,signal157,signal178] (.node [signal0,signal90,signal111,signal136,signal157,signal165] .nil .nil) (.node [signal1,signal79,signal111,signal136,signal157,signal178] .nil .nil))) (.node [signal3,signal20,signal90,signal111,signal136,signal178] (.node [signal2,signal79,signal111,signal136,signal157,signal178] (.node [signal2,signal33,signal90,signal111,signal157,signal178] .nil .nil) (.node [signal2,signal90,signal98,signal136,signal157,signal178] .nil .nil)) (.node [signal3,signal90,signal111,signal136,signal157,signal165] (.node [signal3,signal79,signal111,signal136,signal157,signal178] .nil .nil) (.node [signal4,signal8,signal90,signal111,signal136,signal157] .nil .nil)))) (.node [signal8,signal60,signal111,signal136,signal157,signal196] (.node [signal7,signal32,signal90,signal111,signal157,signal196] (.node [signal5,signal90,signal111,signal136,signal157,signal178] (.node [signal4,signal90,signal111,signal136,signal144,signal178] .nil .nil) (.node [signal6,signal46,signal90,signal136,signal157,signal196] .nil .nil)) (.node [signal8,signal33,signal90,signal111,signal157,signal196] (.node [signal8,signal20,signal90,signal111,signal136,signal196] .nil .nil) (.node [signal8,signal47,signal90,signal136,signal157,signal196] .nil .nil))) (.node [signal8,signal90,signal111,signal136,signal144,signal196] (.node [signal8,signal90,signal98,signal136,signal157,signal196] (.node [signal8,signal79,signal111,signal136,signal157,signal196] .nil .nil) (.node [signal8,signal90,signal111,signal123,signal157,signal196] .nil .nil)) (.node [signal8,signal90,signal111,signal136,signal157,signal196] (.node [signal8,signal90,signal111,signal136,signal157,signal165] .nil .nil) .nil)))) (.node [signal20,signal90,signal111,signal123,signal178,signal196] (.node [signal18,signal45,signal90,signal136,signal178,signal196] (.node [signal13,signal90,signal111,signal136,signal157,signal196] (.node [signal11,signal90,signal111,signal136,signal157,signal196] (.node [signal10,signal90,signal111,signal136,signal157,signal196] .nil .nil) (.node [signal12,signal90,signal111,signal136,signal157,signal196] .nil .nil)) (.node [signal15,signal27,signal90,signal111,signal136,signal196] (.node [signal14,signal90,signal111,signal136,signal157,signal196] .nil .nil) (.node [signal16,signal90,signal111,signal136,signal157,signal196] .nil .nil))) (.node [signal20,signal60,signal111,signal136,signal178,signal196] (.node [signal20,signal33,signal90,signal111,signal178,signal196] (.node [signal19,signal31,signal90,signal111,signal178,signal196] .nil .nil) (.node [signal20,signal47,signal90,signal136,signal178,signal196] .nil .nil)) (.node [signal20,signal90,signal98,signal136,signal178,signal196] (.node [signal20,signal79,signal111,signal136,signal178,signal196] .nil .nil) .nil))) (.node [signal25,signal90,signal111,signal136,signal178,signal196] (.node [signal21,signal63,signal111,signal136,signal178,signal196] (.node [signal20,signal90,signal111,signal136,signal165,signal196] (.node [signal20,signal90,signal111,signal136,signal144,signal178] .nil .nil) (.node [signal20,signal90,signal111,signal136,signal178,signal196] .nil .nil)) (.node [signal23,signal90,signal111,signal136,signal178,signal196] (.node [signal22,signal90,signal111,signal136,signal178,signal196] .nil .nil) (.node [signal24,signal90,signal111,signal136,signal178,signal196] .nil .nil))) (.node [signal33,signal60,signal111,signal157,signal178,signal196] (.node [signal28,signal90,signal111,signal136,signal178,signal196] (.node [signal26,signal90,signal111,signal136,signal178,signal196] .nil .nil) (.node [signal33,signal47,signal90,signal157,signal178,signal196] .nil .nil)) (.node [signal33,signal90,signal98,signal157,signal178,signal196] (.node [signal33,signal79,signal111,signal157,signal178,signal196] .nil .nil) .nil))))) (.node [signal60,signal111,signal136,signal157,signal178,signal196] (.node [signal47,signal90,signal136,signal144,signal178,signal196] (.node [signal38,signal90,signal111,signal157,signal178,signal196] (.node [signal34,signal62,signal111,signal157,signal178,signal196] (.node [signal33,signal90,signal111,signal157,signal165,signal196] (.node [signal33,signal90,signal111,signal144,signal178,signal196] .nil .nil) (.node [signal33,signal90,signal111,signal157,signal178,signal196] .nil .nil)) (.node [signal36,signal90,signal111,signal157,signal178,signal196] (.node [signal35,signal49,signal90,signal157,signal178,signal196] .nil .nil) (.node [signal37,signal90,signal111,signal157,signal178,signal196] .nil .nil))) (.node [signal47,signal60,signal136,signal157,signal178,signal196] (.node [signal40,signal90,signal111,signal157,signal178,signal196] (.node [signal39,signal90,signal111,signal157,signal178,signal196] .nil .nil) (.node [signal41,signal90,signal111,signal157,signal178,signal196] .nil .nil)) (.node [signal47,signal90,signal98,signal136,signal157,signal178] (.node [signal47,signal79,signal136,signal157,signal178,signal196] .nil .nil) (.node [signal47,signal90,signal123,signal157,signal178,signal196] .nil .nil)))) (.node [signal54,signal90,signal136,signal157,signal178,signal196] (.node [signal50,signal90,signal136,signal157,signal178,signal196] (.node [signal47,signal90,signal136,signal157,signal178,signal196] (.node [signal47,signal90,signal136,signal157,signal165,signal196] .nil .nil) (.node [signal48,signal61,signal136,signal157,signal178,signal196] .nil .nil)) (.node [signal52,signal90,signal136,signal157,signal178,signal196] (.node [signal51,signal90,signal136,signal157,signal178,signal196] .nil .nil) (.node [signal53,signal90,signal136,signal157,signal178,signal196] .nil .nil))) (.node [signal60,signal111,signal123,signal157,signal178,signal196] (.node [signal60,signal79,signal111,signal136,signal157,signal178] (.node [signal55,signal90,signal136,signal157,signal178,signal196] .nil .nil) (.node [signal60,signal98,signal136,signal157,signal178,signal196] .nil .nil)) (.node [signal60,signal111,signal136,signal157,signal165,signal196] (.node [signal60,signal111,signal136,signal144,signal178,signal196] .nil .nil) .nil)))) (.node [signal79,signal98,signal136,signal157,signal178] (.node [signal77,signal111,signal136,signal178,signal196,signal207] (.node [signal71,signal90,signal136,signal157,signal178,signal196] (.node [signal67,signal90,signal111,signal136,signal178,signal196] (.node [signal65,signal111,signal136,signal157,signal178,signal196] .nil .nil) (.node [signal70,signal90,signal111,signal136,signal157,signal196] .nil .nil)) (.node [signal75,signal136,signal157,signal178,signal196,signal200] (.node [signal74,signal90,signal111,signal157,signal178,signal196] .nil .nil) (.node [signal76,signal111,signal157,signal178,signal196,signal203] .nil .nil))) (.node [signal79,signal90,signal111,signal136,signal144,signal178] (.node [signal79,signal90,signal98,signal136,signal157,signal178] (.node [signal78,signal111,signal136,signal157,signal196,signal210] .nil .nil) (.node [signal79,signal90,signal111,signal123,signal157,signal178] .nil .nil)) (.node [signal79,signal98,signal111,signal136,signal157,signal178] (.node [signal79,signal90,signal111,signal136,signal157,signal165] .nil .nil) .nil))) (.node [signal79,signal111,signal136,signal157,signal165] (.node [signal79,signal111,signal123,signal157,signal178,signal196] (.node [signal79,signal111,signal123,signal136,signal157,signal178] (.node [signal79,signal98,signal136,signal157,signal178,signal196] .nil .nil) (.node [signal79,signal111,signal123,signal157,signal178] .nil .nil)) (.node [signal79,signal111,signal136,signal144,signal178] (.node [signal79,signal111,signal136,signal144,signal157,signal178] .nil .nil) (.node [signal79,signal111,signal136,signal144,signal178,signal196] .nil .nil))) (.node [signal79,signal111,signal136,signal157,signal178,signal197] (.node [signal79,signal111,signal136,signal157,signal165,signal196] (.node [signal79,signal111,signal136,signal157,signal165,signal178] .nil .nil) (.node [signal79,signal111,signal136,signal157,signal178,signal196] .nil .nil)) (.node [signal81,signal111,signal136,signal157,signal178,signal196] (.node [signal80,signal111,signal136,signal157,signal178,signal196] .nil .nil) .nil)))))) (.node [signal90,signal111,signal136,signal144,signal165,signal196] (.node [signal90,signal108,signal136,signal157,signal178,signal196] (.node [signal90,signal98,signal123,signal157,signal178] (.node [signal90,signal92,signal157,signal178,signal196,signal204] (.node [signal86,signal111,signal136,signal157,signal178,signal196] (.node [signal84,signal111,signal136,signal157,signal178,signal196] (.node [signal83,signal111,signal136,signal157,signal178,signal196] .nil .nil) (.node [signal85,signal111,signal136,signal157,signal178,signal196] .nil .nil)) (.node [signal88,signal111,signal136,signal157,signal178,signal196] (.node [signal87,signal111,signal136,signal157,signal178,signal196] .nil .nil) (.node [signal89,signal111,signal136,signal157,signal178,signal196] .nil .nil))) (.node [signal90,signal96,signal136,signal157,signal184,signal196] (.node [signal90,signal94,signal111,signal136,signal178,signal196] (.node [signal90,signal93,signal136,signal163,signal178,signal196] .nil .nil) (.node [signal90,signal95,signal136,signal157,signal178,signal196] .nil .nil)) (.node [signal90,signal98,signal111,signal123,signal157,signal178] (.node [signal90,signal97,signal136,signal157,signal178,signal196] .nil .nil) (.node [signal90,signal98,signal123,signal136,signal157,signal178] .nil .nil)))) (.node [signal90,signal101,signal136,signal157,signal178,signal196] (.node [signal90,signal98,signal136,signal157,signal178,signal196] (.node [signal90,signal98,signal136,signal144,signal178,signal196] (.node [signal90,signal98,signal123,signal157,signal178,signal196] .nil .nil) (.node [signal90,signal98,signal136,signal157,signal165,signal196] .nil .nil)) (.node [signal90,signal99,signal136,signal157,signal178,signal196] (.node [signal90,signal98,signal136,signal157,signal178,signal198] .nil .nil) (.node [signal90,signal100,signal136,signal157,signal178,signal196] .nil .nil))) (.node [signal90,signal105,signal136,signal157,signal178,signal196] (.node [signal90,signal103,signal136,signal157,signal178,signal196] (.node [signal90,signal102,signal136,signal157,signal178,signal196] .nil .nil) (.node [signal90,signal104,signal136,signal157,signal178,signal196] .nil .nil)) (.node [signal90,signal107,signal136,signal157,signal178,signal196] (.node [signal90,signal106,signal136,signal157,signal178,signal196] .nil .nil) .nil)))) (.node [signal90,signal111,signal126,signal157,signal178,signal196] (.node [signal90,signal111,signal122,signal157,signal178,signal196] (.node [signal90,signal111,signal118,signal164,signal178,signal196] (.node [signal90,signal110,signal136,signal157,signal178,signal196] (.node [signal90,signal109,signal136,signal157,signal178,signal196] .nil .nil) (.node [signal90,signal111,signal116,signal136,signal157,signal196] .nil .nil)) (.node [signal90,signal111,signal120,signal157,signal178,signal196] (.node [signal90,signal111,signal119,signal136,signal178,signal196] .nil .nil) (.node [signal90,signal111,signal121,signal157,signal185,signal196] .nil .nil))) (.node [signal90,signal111,signal123,signal157,signal178,signal201] (.node [signal90,signal111,signal123,signal157,signal165,signal196] (.node [signal90,signal111,signal123,signal144,signal178,signal196] .nil .nil) (.node [signal90,signal111,signal123,signal157,signal178,signal196] .nil .nil)) (.node [signal90,signal111,signal125,signal157,signal178,signal196] (.node [signal90,signal111,signal124,signal157,signal178,signal196] .nil .nil) .nil))) (.node [signal90,signal111,signal134,signal157,signal178,signal196] (.node [signal90,signal111,signal130,signal157,signal178,signal196] (.node [signal90,signal111,signal128,signal157,signal178,signal196] (.node [signal90,signal111,signal127,signal157,signal178,signal196] .nil .nil) (.node [signal90,signal111,signal129,signal157,signal178,signal196] .nil .nil)) (.node [signal90,signal111,signal132,signal157,signal178,signal196] (.node [signal90,signal111,signal131,signal157,signal178,signal196] .nil .nil) (.node [signal90,signal111,signal133,signal157,signal178,signal196] .nil .nil))) (.node [signal90,signal111,signal136,signal144,signal157,signal165] (.node [signal90,signal111,signal136,signal141,signal157,signal196] (.node [signal90,signal111,signal135,signal157,signal178,signal196] .nil .nil) (.node [signal90,signal111,signal136,signal143,signal196,signal211] .nil .nil)) (.node [signal90,signal111,signal136,signal144,signal165,signal178] (.node [signal90,signal111,signal136,signal144,signal165] .nil .nil) .nil))))) (.node [signal90,signal111,signal136,signal157,signal178,signal190] (.node [signal90,signal111,signal136,signal157,signal165,signal208] (.node [signal90,signal111,signal136,signal150,signal178,signal196] (.node [signal90,signal111,signal136,signal146,signal178,signal196] (.node [signal90,signal111,signal136,signal144,signal178,signal205] (.node [signal90,signal111,signal136,signal144,signal178,signal196] .nil .nil) (.node [signal90,signal111,signal136,signal145,signal178,signal196] .nil .nil)) (.node [signal90,signal111,signal136,signal148,signal178,signal196] (.node [signal90,signal111,signal136,signal147,signal178,signal196] .nil .nil) (.node [signal90,signal111,signal136,signal149,signal178,signal196] .nil .nil))) (.node [signal90,signal111,signal136,signal154,signal178,signal196] (.node [signal90,signal111,signal136,signal152,signal178,signal196] (.node [signal90,signal111,signal136,signal151,signal178,signal196] .nil .nil) (.node [signal90,signal111,signal136,signal153,signal178,signal196] .nil .nil)) (.node [signal90,signal111,signal136,signal156,signal178,signal196] (.node [signal90,signal111,signal136,signal155,signal178,signal196] .nil .nil) (.node [signal90,signal111,signal136,signal157,signal165,signal196] .nil .nil)))) (.node [signal90,signal111,signal136,signal157,signal173,signal196] (.node [signal90,signal111,signal136,signal157,signal169,signal196] (.node [signal90,signal111,signal136,signal157,signal167,signal196] (.node [signal90,signal111,signal136,signal157,signal166,signal196] .nil .nil) (.node [signal90,signal111,signal136,signal157,signal168,signal196] .nil .nil)) (.node [signal90,signal111,signal136,signal157,signal171,signal196] (.node [signal90,signal111,signal136,signal157,signal170,signal196] .nil .nil) (.node [signal90,signal111,signal136,signal157,signal172,signal196] .nil .nil))) (.node [signal90,signal111,signal136,signal157,signal177,signal196] (.node [signal90,signal111,signal136,signal157,signal175,signal196] (.node [signal90,signal111,signal136,signal157,signal174,signal196] .nil .nil) (.node [signal90,signal111,signal136,signal157,signal176,signal196] .nil .nil)) (.node [signal90,signal111,signal136,signal157,signal178,signal189] (.node [signal90,signal111,signal136,signal157,signal178,signal187] .nil .nil) .nil)))) (.node [signal90,signal111,signal136,signal162,signal178,signal196] (.node [signal90,signal111,signal136,signal157,signal182,signal196] (.node [signal90,signal111,signal136,signal157,signal178,signal196] (.node [signal90,signal111,signal136,signal157,signal178,signal194] (.node [signal90,signal111,signal136,signal157,signal178,signal192] .nil .nil) (.node [signal90,signal111,signal136,signal157,signal178,signal195] .nil .nil)) (.node [signal90,signal111,signal136,signal157,signal180,signal196] (.node [signal90,signal111,signal136,signal157,signal179,signal196] .nil .nil) (.node [signal90,signal111,signal136,signal157,signal181,signal196] .nil .nil))) (.node [signal90,signal111,signal136,signal159,signal178,signal196] (.node [signal90,signal111,signal136,signal157,signal196,signal209] (.node [signal90,signal111,signal136,signal157,signal183,signal196] .nil .nil) (.node [signal90,signal111,signal136,signal158,signal178,signal196] .nil .nil)) (.node [signal90,signal111,signal136,signal161,signal178,signal196] (.node [signal90,signal111,signal136,signal160,signal178,signal196] .nil .nil) .nil))) (.node [signal90,signal112,signal136,signal157,signal178,signal196] (.node [signal90,signal111,signal139,signal157,signal178,signal196] (.node [signal90,signal111,signal137,signal157,signal178,signal196] (.node [signal90,signal111,signal136,signal178,signal196,signal206] .nil .nil) (.node [signal90,signal111,signal138,signal157,signal178,signal196] .nil .nil)) (.node [signal90,signal111,signal142,signal157,signal178,signal196] (.node [signal90,signal111,signal140,signal157,signal178,signal196] .nil .nil) (.node [signal90,signal111,signal157,signal178,signal196,signal202] .nil .nil))) (.node [signal90,signal117,signal136,signal157,signal178,signal196] (.node [signal90,signal114,signal136,signal157,signal178,signal196] (.node [signal90,signal113,signal136,signal157,signal178,signal196] .nil .nil) (.node [signal90,signal115,signal136,signal157,signal178,signal196] .nil .nil)) (.node [signal91,signal111,signal136,signal157,signal178,signal196] (.node [signal90,signal136,signal157,signal178,signal196,signal199] .nil .nil) .nil)))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok5 : everyKey (rowOK 4 layer4) layer5=true := by decide +kernel
theorem closed5 : Closed 5 layer5 := closed_next 4 (by decide) _ _ closed4 ok5
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
def layer6 : BinaryTree (List W) := (.node [signal75,signal90,signal111,signal136,signal157,signal178,signal196] (.node [signal31,signal90,signal111,signal136,signal157,signal178,signal196] (.node [signal8,signal90,signal111,signal136,signal157,signal196] (.node [signal4,signal90,signal111,signal136,signal157,signal178,signal196] (.node [signal2,signal90,signal111,signal136,signal157,signal178,signal196] (.node [signal1,signal90,signal111,signal136,signal157,signal178,signal196] (.node [signal0,signal90,signal111,signal136,signal157,signal178,signal196] .nil .nil) .nil) (.node [signal3,signal90,signal111,signal136,signal157,signal178,signal196] .nil .nil)) (.node [signal7,signal90,signal111,signal136,signal157,signal178,signal196] (.node [signal6,signal90,signal111,signal136,signal157,signal178,signal196] .nil .nil) (.node [signal8,signal90,signal111,signal136,signal157,signal178,signal196] .nil .nil))) (.node [signal20,signal90,signal111,signal136,signal157,signal178,signal196] (.node [signal18,signal90,signal111,signal136,signal157,signal178,signal196] (.node [signal15,signal90,signal111,signal136,signal157,signal178,signal196] (.node [signal9,signal90,signal111,signal136,signal157,signal178,signal196] .nil .nil) .nil) (.node [signal19,signal90,signal111,signal136,signal157,signal178,signal196] .nil .nil)) (.node [signal21,signal90,signal111,signal136,signal157,signal178,signal196] (.node [signal20,signal90,signal111,signal136,signal178,signal196] .nil .nil) (.node [signal27,signal90,signal111,signal136,signal157,signal178,signal196] .nil .nil)))) (.node [signal47,signal90,signal136,signal157,signal178,signal196] (.node [signal35,signal90,signal111,signal136,signal157,signal178,signal196] (.node [signal33,signal90,signal111,signal157,signal178,signal196] (.node [signal33,signal90,signal111,signal136,signal157,signal178,signal196] (.node [signal32,signal90,signal111,signal136,signal157,signal178,signal196] .nil .nil) .nil) (.node [signal34,signal90,signal111,signal136,signal157,signal178,signal196] .nil .nil)) (.node [signal46,signal90,signal111,signal136,signal157,signal178,signal196] (.node [signal45,signal90,signal111,signal136,signal157,signal178,signal196] .nil .nil) (.node [signal47,signal90,signal111,signal136,signal157,signal178,signal196] .nil .nil))) (.node [signal61,signal90,signal111,signal136,signal157,signal178,signal196] (.node [signal60,signal90,signal111,signal136,signal157,signal178,signal196] (.node [signal49,signal90,signal111,signal136,signal157,signal178,signal196] (.node [signal48,signal90,signal111,signal136,signal157,signal178,signal196] .nil .nil) .nil) (.node [signal60,signal111,signal136,signal157,signal178,signal196] .nil .nil)) (.node [signal63,signal90,signal111,signal136,signal157,signal178,signal196] (.node [signal62,signal90,signal111,signal136,signal157,signal178,signal196] .nil .nil) (.node [signal64,signal90,signal111,signal136,signal157,signal178,signal196] .nil .nil))))) (.node [signal90,signal111,signal136,signal157,signal163,signal178,signal196] (.node [signal90,signal98,signal111,signal136,signal157,signal178,signal196] (.node [signal79,signal111,signal136,signal157,signal178,signal196] (.node [signal78,signal90,signal111,signal136,signal157,signal178,signal196] (.node [signal77,signal90,signal111,signal136,signal157,signal178,signal196] (.node [signal76,signal90,signal111,signal136,signal157,signal178,signal196] .nil .nil) .nil) (.node [signal79,signal90,signal111,signal136,signal157,signal178,signal196] .nil .nil)) (.node [signal90,signal93,signal111,signal136,signal157,signal178,signal196] (.node [signal90,signal92,signal111,signal136,signal157,signal178,signal196] .nil .nil) (.node [signal90,signal96,signal111,signal136,signal157,signal178,signal196] .nil .nil))) (.node [signal90,signal111,signal123,signal157,signal178,signal196] (.node [signal90,signal111,signal121,signal136,signal157,signal178,signal196] (.node [signal90,signal111,signal118,signal136,signal157,signal178,signal196] (.node [signal90,signal98,signal136,signal157,signal178,signal196] .nil .nil) .nil) (.node [signal90,signal111,signal123,signal136,signal157,signal178,signal196] .nil .nil)) (.node [signal90,signal111,signal136,signal144,signal157,signal178,signal196] (.node [signal90,signal111,signal136,signal143,signal157,signal178,signal196] .nil .nil) (.node [signal90,signal111,signal136,signal144,signal178,signal196] .nil .nil)))) (.node [signal90,signal111,signal136,signal157,signal178,signal196,signal201] (.node [signal90,signal111,signal136,signal157,signal178,signal185,signal196] (.node [signal90,signal111,signal136,signal157,signal165,signal196] (.node [signal90,signal111,signal136,signal157,signal165,signal178,signal196] (.node [signal90,signal111,signal136,signal157,signal164,signal178,signal196] .nil .nil) .nil) (.node [signal90,signal111,signal136,signal157,signal178,signal184,signal196] .nil .nil)) (.node [signal90,signal111,signal136,signal157,signal178,signal196,signal198] (.node [signal90,signal111,signal136,signal157,signal178,signal196,signal197] .nil .nil) (.node [signal90,signal111,signal136,signal157,signal178,signal196,signal200] .nil .nil))) (.node [signal90,signal111,signal136,signal157,signal178,signal196,signal207] (.node [signal90,signal111,signal136,signal157,signal178,signal196,signal204] (.node [signal90,signal111,signal136,signal157,signal178,signal196,signal203] .nil .nil) (.node [signal90,signal111,signal136,signal157,signal178,signal196,signal205] .nil .nil)) (.node [signal90,signal111,signal136,signal157,signal178,signal196,signal210] (.node [signal90,signal111,signal136,signal157,signal178,signal196,signal208] .nil .nil) (.node [signal90,signal111,signal136,signal157,signal178,signal196,signal211] .nil .nil))))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok6 : everyKey (rowOK 5 layer5) layer6=true := by decide +kernel
theorem closed6 : Closed 6 layer6 := closed_next 5 (by decide) _ _ closed5 ok6
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
def layer7 : BinaryTree (List W) := (.node [signal90,signal111,signal136,signal157,signal178,signal196] .nil .nil)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok7 : everyKey (rowOK 6 layer6) layer7=true := by decide +kernel
theorem closed7 : Closed 7 layer7 := closed_next 6 (by decide) _ _ closed6 ok7
def table : ℕ := 2826995840 * 2 ^ 32 + 2290089984
theorem row : ∀j : Fin 68, Nat.testBit table (∑i : Fin 6, if (ins.getD i.val 0)[j.val] then 2^(i:ℕ) else 0)=goal[j.val] := by decide +kernel
theorem reject : ∀z, z=goal ∨ z = ~~~goal → ¬build basicOps z 7 ins.toFinset := no_build 7 layer7 ins (by decide) (by decide) closed7 (by decide +kernel)
open PEqualNP.CircuitLowerBounds
def monoGates : List Gate := [⟨.or,[2,3]⟩,⟨.or,[5,4]⟩,⟨.and,[4,2]⟩,⟨.and,[3,5]⟩,⟨.and,[9,8]⟩,⟨.and,[7,6]⟩,⟨.and,[11,0]⟩,⟨.or,[10,1]⟩,⟨.and,[12,13]⟩]
theorem upper : ∃(gs : List Gate) (o : ℕ), (∀g∈gs,(g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2) ∧ gs.length=9 ∧ ∀x : Fin 6 → Bool,Circuit.eval ⟨gs,o⟩ (List.ofFn x)=Nat.testBit table (∑i : Fin 6,if x i then 2^(i:ℕ) else 0) := ⟨monoGates,14,by simp [monoGates],rfl,by decide +kernel⟩
end PEqualNP.Outside.L_meta_15093

open PEqualNP.Outside.L_meta_15093 in
theorem PEqualNP.Outside.L_meta_15093 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (2826995840 * 2 ^ 32 + 2290089984) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (2826995840 * 2 ^ 32 + 2290089984) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
  intro s h
  obtain ⟨C, hfan, hsize, hev⟩ := h
  obtain ⟨gates, o⟩ := C
  have hleg : ∀ g ∈ gates, legal g := by
    intro g hg
    obtain ⟨hop, cap⟩ := hfan g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    exact ⟨hop, cap⟩
  obtain ⟨ds, p, mono, len, ev⟩ := replace table 9 ins (by decide) row rfl reject upper gates o hleg hev
  refine ⟨⟨ds, p⟩, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨hop, cap⟩ := mono g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    exact ⟨hop, cap⟩
  · exact le_trans len hsize
  · exact ev
