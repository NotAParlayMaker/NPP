import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_12274

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

abbrev W := BitVec 104
def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 52 := ((x >>> 52) ^^^ x).setWidth 52
def cuts (ws : List W) : BitVec 52 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 52) ++ (0 : BitVec 52)
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

def differs (i : Fin 52) (w : W) : Prop :=
  w.getLsbD (52+i.val) ≠ w.getLsbD i.val

theorem ops_differs (i : Fin 52) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 52+i.val < 104 := by omega
  have hi' : i.val < 104 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

theorem cuts_spec (ws : List W) (i : Fin 52) :
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
  change (cuts ws)[j] = (BitVec.allOnes 52)[j]
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
  · change reachable av (BitVec.allOnes 104 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 104)
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

private def bit (k : Fin 104) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 104) :
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
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 104) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> try simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#104)[k.val] = false; simp
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
    (row : ∀ j : Fin 104, Nat.testBit T (∑ i : Fin 6, if (ins.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val])
    (width : ins.length = 6) (rejection : ∀ z, z = goal ∨ z = ~~~goal → ¬ build basicOps z n ins.toFinset)
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) =
      Nat.testBit T (∑ i : Fin 6, if x i then 2^(i : ℕ) else 0)) : n < binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ ins, holds ins.toFinset u := fun u hu =>
    .inr (.inr ⟨u,List.mem_toFinset.mpr hu,.inl rfl⟩)
  have evaluate (k : Fin 104) :
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
    (row : ∀ j : Fin 104, Nat.testBit T (∑ i : Fin 6, if (ins.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val])
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

def v0 : W := 0x49fcc6398c7ff4974c6318c6ee
def v1 : W := 0x8e7f07c60f8ff8c6f07860f0dd
def v2 : W := 0xf07ff807f00ffe05ff007e00bb
def v3 : W := 0xff87fffffff0f1282ad6d5ad07
def v4 : W := 0xfff80007ffff0ffb80002b5b70
def v5 : W := 0xfffffff800000fffd5ad800000
def v6 : W := 0x8e7f07c60f8f08c28000205050
def v7 : W := 0xff87fffffff0f12820d4c1a905
def v8 : W := 0x49fcc6398c7ff493084218c666
def v9 : W := 0x8e7f07c60f8ff8c2a05060f055
def v10 : W := 0xff87fffffff001280084810900
def v11 : W := 0xff807f80fff0f2dd5d6abadbc
def v12 : W := 0xffffffffffff0ffb80adab5b70
def v13 : W := 0xf8007f80ff001fa00d681ff44
def v14 : W := 0x7c0000000ff0044000000088
def v15 : W := 0xff87fffffff0f0002a5254a407
def v16 : W := 0xffffffffffff0ffb8084ab5b70
def v17 : W := 0xf8007f80ff0f1fe7f84d55bcb
def v18 : W := 0x49fcc6398c7ff082084210c446
def v19 : W := 0x49fcc6398c7f04930000084260
def v20 : W := 0xff87fffffff0f12808c6918d06
def v21 : W := 0x4984c6398c70f0000842108406
def v22 : W := 0xffffffffffff05bb0084894b60
def v23 : W := 0x7180f839f07007390a869f0f22
def v24 : W := 0x49fcc6398c7ff4010842188426
def v25 : W := 0x7180f839f070f73d70fccbabad
def v26 : W := 0x49fcc6398c7ff493086318c666
def v27 : W := 0xf07ff807f00ffe01aa007e0033
def v28 : W := 0x49fcc6398c7ff4930c4318c666
def v29 : W := 0x7e00ffc1ff8006c30f781ef066
def v30 : W := 0x71f8f839f07f09eedaaeb55dda
def v31 : W := 0xffffffffffff0ffb8585ab5b70
def v32 : W := 0x8e0707c60f80f000205040a005
def v33 : W := 0xffffffffffff09ea8084a15950
def v34 : W := 0x8e7f07c60f8ff8c2b05860f055
def v35 : W := 0x8e7f07c60f8ff800a05060a015
def v36 : W := 0x8e7f07c60f8ff082205040e045
def v37 : W := 0x8e7f07c60f8ff8c2a07860f055
def v38 : W := 0xf07ff807f00ff4012a005c0023
def v39 : W := 0xf07ff807f00f0e0180002a0030
def v40 : W := 0xff87fffffff0f1282a84d50903
def v41 : W := 0xf007f807f000f0002a00540003
def v42 : W := 0xffffffffffff0f298084ab0930
def v43 : W := 0xf07ff807f00ff800aa00740013
def v44 : W := 0xb67b39c6738f05bf66b5cd6be9
def v45 : W := 0xb60339c673800b68a294e73911
def v46 : W := 0xf07ff807f00ffe01bb007e0033
def v47 : W := 0xf07ff807f00ffe01af007e0033
def v48 : W := 0xb60339c67380fb6ccce7b39d9e
def v49 : W := 0xc783c1ff83f00c51bc1b783633
def v50 : W := 0xb9833e3e7c700a92b36366c655
def v51 : W := 0xffffffffffff0ffb918cab5b70
def v52 : W := 0xff83fffffff00ed3bf7b7ef677
def v53 : W := 0xff0002a527ef677
def v54 : W := 0x7ffff8000ffed3aad6fef677
def v55 : W := 0xf0002a5254a407
def v56 : W := 0x45028000088
def v57 : W := 0x44421000088
def v58 : W := 0x45500000088
def v59 : W := 0xf0047a7a54a48f
def v60 : W := 0xf0046e7354a48f
def v61 : W := 0xf0044c6310848e
def v62 : W := 0xb60339c673800b688084a31910
def v63 : W := 0xf004707840a08d
def v64 : W := 0x7180f839f070073900848b0b20
def v65 : W := 0xf0047f5254a48f
def v66 : W := 0xf0047f0054008b
def v67 : W := 0xf8007f80ff001fa0084815b40
def v68 : W := 0x7fff0f0002a5255ad07
def v69 : W := 0xb604c63e7380fb6ccc63339d9e
def v70 : W := 0x718707c1f070f73d70784babad
def v71 : W := 0xf87f8000ff0f1fe7f00555bcb
def v72 : W := 0x7fffff0002a525defef
def v73 : W := 0x7fffff0002a527fadbf
def v74 : W := 0x7fffff0002a5275fddf
def v75 : W := 0x7fff80000000455ad800000
def v76 : W := 0x7fff8000000000084800000
def v77 : W := 0x707c00000f004707840a08d
def v78 : W := 0x7187fff9f070073d55ad8b0b20
def v79 : W := 0x4c6380000f0044c6310848e
def v80 : W := 0xb607fffe73800b6cd5ada31910
def v81 : W := 0x7f8000000f0047f0054008b
def v82 : W := 0xf87fff80ff001fe55ad815b40
def v83 : W := 0x780000000f049744210842e8
def v84 : W := 0xb60339c6738001282294c52901
def v85 : W := 0x7fff80000f0047afed4a48f
def v86 : W := 0x7fff80000f0002ad6d4a407
def v87 : W := 0x7ffff8000f0ed38084aa5270
def v88 : W := 0x780000000ffed3aa527ef677
def v89 : W := 0x7fff80000f0046ef7d4a48f
def v90 : W := 0x7ffffffff000455adab5b70
def v91 : W := 0x7fff80000f0047fd6d4a48f
def v92 : W := 0x780000000f08c6d0282050d8
def v93 : W := 0x7180f839f07001280a86950d02
def v94 : W := 0x780000000f0e05d5002a00b8
def v95 : W := 0xf8007f80ff0012800d681ad04
def v96 : W := 0x7fffff0002a527fff77
def v97 : W := 0x7ffff800000ed38084800000
def v98 : W := 0x780000000f0ed7d5292a5270
def v99 : W := 0xffffffffffff0fffd5adab5b70
def v100 : W := 0x780000000f0ed7d5002a52f8
def v101 : W := 0x780000000f0ed7d0282a52f8
def v102 : W := 0x780007fff0fed7ff7b55ad07
def v103 : W := 0x780000000ffed7ff7b7ef677
def v104 : W := 0xfffffffffffffffbaad6ffff77
def v105 : W := 0x780007ffff0ed380002b5b70
def v106 : W := 0xfffffffffffffed7ff7b7ef6ff
def v107 : W := 0xff87fff8000001280084800000
def v108 : W := 0x7ffff800000ed7d5ad800000
def v109 : W := 0xfffffff8000f0fffd5adaa5270
def v110 : W := 0xfffffff800000ffb8084800000
def v111 : W := 0xff87fff80000012c55ad800000
def v112 : W := 0xfffffffffff00fffd5ad810900
def v113 : W := 0x9fc06380c7ff096406300c6cc
def v114 : W := 0xf67ff9c7f38ffe45ff187e30bb
def v115 : W := 0x87c06000c0ff086406000c0cc
def v116 : W := 0x67c01c0038ff0444018003088
def v117 : W := 0x1fc0038007ff0144003000688
def v118 : W := 0x7fffffffff0ed38084ab5b70
def v119 : W := 0xfe7fffc7ff8ffec7ff787ef0ff
def v120 : W := 0xcfffc7ff8ffffcd7fc7b78f6ff
def v121 : W := 0xf9fffe3ffc7ffe97ff637ec6ff
def v122 : W := 0x9f806398c7ff4974c6318c6ee
def v123 : W := 0x98006380c700092006300c644
def v124 : W := 0xb003380670000a00b300660011
def v125 : W := 0xf7fff9fff3fffe55ff1b7e36bb
def v126 : W := 0xf603f9c7f3800e41bf187e3033
def v127 : W := 0xf8007f80ff000d2007b00f644
def v128 : W := 0xf003f807f0000e01bf007e0033
def v129 : W := 0xe7c07c00f8ff0c6407800f0cc
def v130 : W := 0xe0007c00f8000c2007800f044
def v131 : W := 0xf183f83ff0700e11bf037e0633
def v132 : W := 0x7000f801f00006010f001e0022
def v133 : W := 0xe7807c60f8ff8c6f07860f0dd
def v134 : W := 0xf1fff83ff07ffe15ff037e06bb
def v135 : W := 0xf8007f80ff001ea00fe81fd44
def v136 : W := 0xf8007f80ff001ba00f781ef44
def v137 : W := 0x780000000f0ed7c4212a52f8
def v138 : W := 0xfffffffff00f0fffd5adaa0030
def v139 : W := 0xf8007fff00ff1fa2aadfe00bb
def v140 : W := 0xf8007f80ff001fa00fc81fb44
def v141 : W := 0xf8007f80ff001fa00e781df44
def v142 : W := 0xf0780007ffff0e0180002b5b70
def v143 : W := 0xf8007f80ff0f1fa2aadd55bcb
def v144 : W := 0xf87fff8000001fe55ad800000
def v145 : W := 0xfff807ffffff0ffb80adab5b70
def v146 : W := 0xf07ffff800000e05d5ad800000
def v147 : W := 0xfffffff80ff00fffd5ad815b40
def v148 : W := 0xff87fff8000001fa00ad800000
def v149 : W := 0x7180f839f07007290f869f0d22
def v150 : W := 0xf87ffffffff01fe55adab5b70
def v151 : W := 0x49fcc6398c7ff4054c421884ae
def v152 : W := 0x8e7f07c60f8ff804f05060a09d
def v153 : W := 0xfffffff8000f0fffd5adaa00b8
def v154 : W := 0xfffffff800000f2dd584800000
def v155 : W := 0xfff80007ffff0f2980002b0930
def v156 : W := 0xb60339c673800b28b394e72911
def v157 : W := 0x467cc1c1838ff52d4c949929aa
def v158 : W := 0x407cc001800ff4054c001800aa
def v159 : W := 0xbfff3ffe7ffffad6f37b66f6dd
def v160 : W := 0x387c3e007c0ff1ae42e485c9cc
def v161 : W := 0x307c3800700ff2044300060088
def v162 : W := 0xffc07f80ffff0d6407b00f6cc
def v163 : W := 0x41fcc039807ff4154c031806aa
def v164 : W := 0x4180c039807004110c03180622
def v165 : W := 0xbe033fc67f800ac2b37866f055
def v166 : W := 0x860301c603800840b018603011
def v167 : W := 0x41f8c0398c7ff4974c6318c6ee
def v168 : W := 0xbe7f3fc67f8ffac6f37866f0dd
def v169 : W := 0xfffffffffffff5bf6ef7ddefef
def v170 : W := 0xfff80007ffff05bb0000094b60
def v171 : W := 0x49f800018c7f04930000084260
def v172 : W := 0x4980c6398c7004930c6318c666
def v173 : W := 0xb60339c673800a40b318663011
def v174 : W := 0x8e7f07c60f8ff086607040e0cd
def v175 : W := 0xf07ff807f00ff4056e005c00ab
def v176 : W := 0xffffffffffff05bf44a5894b60
def v177 : W := 0xfffffff8000005bf44a5800000
def v178 : W := 0x49f800018c7ff493084218c6ee
def v179 : W := 0xfffb39c7ffff0ffb918cab5b70
def v180 : W := 0xff84c63ffff0f1280842118d06
def v181 : W := 0xfffffffffffff5bb2ad6ddef67
def v182 : W := 0x49f806398c7ff493086318c6ee
def v183 : W := 0x49f80007ffff049300002b5b70
def v184 : W := 0xb60339c18c7ffb6899ce98c6ee
def v185 : W := 0xff807fff00fff2dff84fe00bb
def v186 : W := 0x49fcc6398c7ff086486210c4ce
def v187 : W := 0xf07ff807f00ff804fa0074009b
def v188 : W := 0x49fcc6398c7f04974421084260
def v189 : W := 0x49fb39c18c7ff49319ce98c6ee
def v190 : W := 0x49fb39c18c7f04932294cc6261
def v191 : W := 0xffffffffffffffffcce7bbdffe
def v192 : W := 0xff800007fff001280000010900
def v193 : W := 0x49fcc6398c7ff493084218c6ee
def v194 : W := 0x7180f839f07007390f849f0b22
def v195 : W := 0x707cf801f00ff6054f001e00aa
def v196 : W := 0x49fcc6398c7ff4974c001842ea
def v197 : W := 0x49fcc6398c7ff497406008c2ec
def v198 : W := 0x7078f807f00ffe05ff007e00bb
def v199 : W := 0x49fcc6398c7ff4974c6318c666
def v200 : W := 0x7180f839f07005390e879d0f22
def v201 : W := 0x7180f839f07007390c879b0f22
def v202 : W := 0x7180f83e0f8ff73925d5e0f0dd
def v203 : W := 0xfff8f83fffff0ffb8585ab5b70
def v204 : W := 0x8e780007ffff08c280002b5b70
def v205 : W := 0x7180f839f070f73925d5cbabad
def v206 : W := 0x8e7ffff8000008c6d5ad800000
def v207 : W := 0x7187fff80000073d55ad800000
def v208 : W := 0xfffffffe0f8f0fffd5ada05050
def v209 : W := 0xfffffff9f0700fffd5ad8b0b20
def v210 : W := 0x7187ffffffff073d55adab5b70
def v211 : W := 0x49f8c0398c7ff4930c4318c6ee
def v212 : W := 0x807f0006000ff804f000600099
def v213 : W := 0xfffffff8000009eed0ac800000
def v214 : W := 0xff87fff8000007390585800000
def v215 : W := 0xfff80007ffff09ea8000215950
def v216 : W := 0xfffffff8000f0fffd5ada050d8
def v217 : W := 0x71f8f83e0f8ff9eef0fce0f0dd
def v218 : W := 0x7f80fff9fff006d30f7b1ef666
def v219 : W := 0xffffffffffff09eed0aca15950
def v220 : W := 0x8e7800060f8f08c28000205050
def v221 : W := 0x867b01c60f8ff8c6f07860f0dd
def v222 : W := 0x81ff003e007ff92cf086e10d99
def v223 : W := 0x867f01c6038ff844f018603099
def v224 : W := 0x8e7800060f8ff8c2a05060f0dd
def v225 : W := 0xfffffffffffff9eaaad6f5fd57
def v226 : W := 0xfffffffffffff9eefafef5fddf
def v227 : W := 0xff8707c7fff0f128205041a905
def v228 : W := 0x8e78f83e0f8f08c28a86b45452
def v229 : W := 0x8e7807c60f8ff8c2a07860f0dd
def v230 : W := 0x8e7f07c60f8f08c6d028205050
def v231 : W := 0x8e7f07c1f07f08c6da2a355dda
def v232 : W := 0x8e7b01c60f8ff8c2b05860f0dd
def v233 : W := 0xfffffffffffffffff0fcebfbfd
def v234 : W := 0x8e7f07c60f8ff8c2a05060f0dd
def v235 : W := 0x8e7f07c60f8ff8c6c06020d0dc
def v236 : W := 0x8e78f83e0f8ff8c2a5d5e0f0dd
def v237 : W := 0xf07807fff00ffe01aaadfe00bb
def v238 : W := 0xb607ffffffff0b6cd5adab5b70
def v239 : W := 0xb07b3807f00ffe05ff007e00bb
def v240 : W := 0x8e7f07c60f8ff8c6f07860f055
def v241 : W := 0xb07f3806700ffa04f300660099
def v242 : W := 0xf0780007f00f0e0180002a0030
def v243 : W := 0xff87f807fff0f1282a00550903
def v244 : W := 0xffffffffffffff2dffd6ffadbf
def v245 : W := 0xffffffffffff0f2dd584ab0930
def v246 : W := 0xffffffffffffff29aad6ffad37
def v247 : W := 0xf07807fff00f0e0180d6aaa434
def v248 : W := 0xf0780007f00ffe01aa007e00bb
def v249 : W := 0xffffffffffffffffff84ff5bfb
def v250 : W := 0xf07b3807f00ffe01bb007e00bb
def v251 : W := 0xf078f807f00ffe01af007e00bb
def v252 : W := 0xf07ff8000fff0e05d5522badbc
def v253 : W := 0xf07ff807f00f0e05d5002a0030
def v254 : W := 0xf07ff807f00ffe05ff007e0033
def v255 : W := 0xf07ff807f00ffe01aa007e00bb
def v256 : W := 0xf07ff807f00ffe05f0006a00b9
def v257 : W := 0xf07ff807f00ffe05cc003a00ba
def v258 : W := 0xfffcc63ffffffffb88423bdf76
def v259 : W := 0xff800007fff0f12c7f7b55ad07
def v260 : W := 0xff800007fff0f1282a5255ad07
def v261 : W := 0xfff80007fffffffbaa527fff77
def v262 : W := 0xfffff807fffffffbaa007f5b73
def v263 : W := 0xffff07c7fffffffba0506bfb75
def v264 : W := 0x8e7f07c60f8ff8c6f0006050d9
def v265 : W := 0xfffbffffffff0ffb95adab5b70
def v266 : W := 0xff87fffffff0012c55ad810900
def v267 : W := 0xfff80000000ffffbaa527ef677
def v268 : W := 0xff87ffffffff012c55adab5b70
def v269 : W := 0xffffffffffff09ea8084ab5b70
def v270 : W := 0xffffffffffff05bb0084ab5b70
def v271 : W := 0xffffffffffff0f298084ab5b70
def v272 : W := 0xffffffffffff0ffb8485ab5b70
def v273 : W := 0xffffffffffff0ffb80acab5b70
def v274 : W := 0xffffffffffff0ffb808cab5b70
def v275 : W := 0xffffffffffff0ffb8085ab5b70
def v276 : W := 0xffffffffffff0ffb80a5ab5b70
def v277 : W := 0xffffffffffff0ffb8184ab5b70
def v278 : W := 0xffffffffffff0ffb908cab5b70
def v279 : W := 0xffffffffffff0ffb8584ab5b70
def v280 : W := 0xffffffffffff0ffb85adab5b70
def v281 : W := 0xffffffffffff0ffb9184ab5b70
def v282 : W := 0xfe03ffc7ff800ec3bf787ef077
def v283 : W := 0xfe7fffc7f00ffe05ff007e00bb
def v284 : W := 0xff87fffffff0f12c7fffd5ad07
def v285 : W := 0xffffffffffff0ffb958dab5b70
def v286 : W := 0xf07ff807f00ffe05ff297e00bb
def v287 : W := 0xf9fffe3ff00ffe05ff007e00bb
def v288 : W := 0x8fff07fe0ffff8d6f07b60f6dd
def v289 : W := 0x8e7f07c60f8ff8c6f57960f0dd
def v290 : W := 0xb67f39c6738ffa44f318663099
def v291 : W := 0xfe7fffc60f8ff8c6f07860f0dd
def v292 : W := 0xcfffc7fe0f8ff8c6f07860f0dd
def v293 : W := 0x4ffcc7f98ffff4d74c7b18f6ee
def v294 : W := 0x4f80c7f98ff004d30c7b18f666
def v295 : W := 0x49fcc63e738f049766314d6be9
def v296 : W := 0x49fcc6398c7ff4975d6b18c6ee
def v297 : W := 0x49fffff80000049755ad800000
def v298 : W := 0x8f8307fe0ff008d2b07b60f655
def v299 : W := 0x7180f839f07006110f031e0622
def v300 : W := 0x8e0307c60f8008c2b07860f055
def v301 : W := 0xffffffffffff0ffb91adab5b70
def v302 : W := 0x7ffcfff9fffff6d74f7b1ef6ee
def v303 : W := 0x79fcfe39fc7ff6974f631ec6ee
def v304 : W := 0x7980fe39fc7006930f631ec666
def v305 : W := 0x71fcf839f07ff6154f031e06aa
def v306 : W := 0xb60339c673800968b29ce53911
def v307 : W := 0xb607fff800000b6cd5ad800000
def v308 : W := 0xb60339c673800b68b09ce33911
def v309 : W := 0xb60339c67380fb6899ceb39d9e
def v310 : W := 0xb60339c673800b68b384e71911
def v311 : W := 0xfffffffe73800fffd5ada31910
def v312 : W := 0xfffffff98c7f0fffd5ad884260
def v313 : W := 0xb67b39c18c7ff5bf4ce798c6ee
def v314 : W := 0xf983fe3ffc700e93bf637ec677
def v315 : W := 0xff87fff800000b68918c800000
def v316 : W := 0xfffffff8000f0fffd5ad8842e8
def v317 : W := 0xbf833ffe7ff00ad2b37b66f655
def v318 : W := 0xf9fffe398c7ff4974c6318c6ee
def v319 : W := 0xcfffc7f98c7ff4974c6318c6ee
def v320 : W := 0xf783f9fff3f00e51bf1b7e3633
def v321 : W := 0xcf83c7ff8ff00cd3bc7b78f677
def v322 : W := 0xf000084210848e
def v323 : W := 0xb60339c673800b68918ca31910
def v324 : W := 0x0
def v325 : W := 0x45529000000
def v326 : W := 0xf0002a0054008b
def v327 : W := 0xf8007f80ff001fa00ad815b40
def v328 : W := 0xf000205040a08d
def v329 : W := 0x7180f839f070073905858b0b20
def v330 : W := 0x780000000f0ed380002a5270
def v331 : W := 0xfff80000000f0ffb80002a5270
def v332 : W := 0xf0002a5254a48f
def v333 : W := 0x1f07000000a02150d02
def v334 : W := 0x8e7f07c0000f08c6d0282050d8
def v335 : W := 0x18c7ff000084218c6ee
def v336 : W := 0x18c70f0000842108406
def v337 : W := 0x49fcc63ffffff4976e735defef
def v338 : W := 0xff00000005201ad04
def v339 : W := 0xf07ff800000f0e05d5002a00b8
def v340 : W := 0xff0f0002a5255ad07
def v341 : W := 0xb60339c000000b68918c800000
def v342 : W := 0x18c70f0002a5254a407
def v343 : W := 0x18c7ff0002a525ce6ef
def v344 : W := 0x60f8ff000205060f0dd
def v345 : W := 0x7180f838000007390585800000
def v346 : W := 0x60f80f000205040a005
def v347 : W := 0x8e7f07c7fffff8c6fa7a75fddf
def v348 : W := 0x1f070f0002a5255ad07
def v349 : W := 0x60f80f0002a5254a407
def v350 : W := 0x60f8ff0002a5274f4df
def v351 : W := 0x67380f0002a5255ad07
def v352 : W := 0x6738000002210452901
def v353 : W := 0x49fcc638000f049744210842e8
def v354 : W := 0xf8000000ff001fa0000015b40
def v355 : W := 0x7f00ff0002a007e00bb
def v356 : W := 0xf8007f8000001fa00ad800000
def v357 : W := 0x7f000f0002a5254a407
def v358 : W := 0xb600000673800b688000231910
def v359 : W := 0x7f00ff0002a527ea4bf
def v360 : W := 0xf07ff807fffffe05ff527fadbf
def v361 : W := 0x7fff000000000010900
def v362 : W := 0x71800001f070073900000b0b20
def v363 : W := 0x4c6380000f0046e7354a48f
def v364 : W := 0x707c00000f0047a7a54a48f
def v365 : W := 0x7f8000000f0047f5254a48f
def v366 : W := 0x78000000000ed7d529000000
def v367 : W := 0x780000000f0ed7d5292a00b8
def v368 : W := 0x780000000f0ed7d5290842e8
def v369 : W := 0x780000000f0ed7d5292050d8
def v370 : W := 0x49f80007ffff04930000094b60
def v371 : W := 0xfffcc63fffffffffcc633bdffe
def v372 : W := 0xffff07c7fffffffff0786bfbfd
def v373 : W := 0x8e780007ffff08c28000215950
def v374 : W := 0x7f000f0002a00540003
def v375 : W := 0xff87fff98c70f12808c6908406
def v376 : W := 0xf0780007ffff0e0180002b0930
def v377 : W := 0xfffff807ffffffffff007f5bfb
def v378 : W := 0xff87fff80000f1282ad6d4a407
def v379 : W := 0xff87fff80ff0012800d681ad04
def v380 : W := 0xff87fffff000f1282a84d40003
def v381 : W := 0xff87fffe0f80f12820d4c0a005
def v382 : W := 0xff87fff9f07001280a86950d02
def v383 : W := 0xff87fffe738001282294c52901
def v384 : W := 0xff87fffffffff1282ad6ddefef
def v385 : W := 0x7fff0f0002a5255ff47
def v386 : W := 0xff87fffffffff1282ad6ffff77
def v387 : W := 0xff87fffffffff1282ad6ffadbf
def v388 : W := 0x7fff0f0002a5255ad8f
def v389 : W := 0x7fff0f0002a5255fd47
def v390 : W := 0x7fff0f0002a5255ef47
def v391 : W := 0x7ffff000000002b5b70
def v392 : W := 0x7fff0f0002a5275bd17
def v393 : W := 0x7fff0f0002a525fad27
def v394 : W := 0x7fff0f0002a525daf27
def v395 : W := 0x7fff0f0002a525faf27
def v396 : W := 0x7fff0f0002a5277bd17
def v397 : W := 0x7fff0f0002a5277ad17
def v398 : W := 0xff87fffffffff1282ad6f5fddf
def v399 : W := 0x7fffff0002a5275ad9f
def v400 : W := 0x7fffff0002a5255edcf
def v401 : W := 0x7fffff0002a525def67
def v402 : W := 0x7fffff0002a525dadaf
def v403 : W := 0x7fffff0002a5275fd57
def v404 : W := 0x7fffff0002a527fad37
def v405 : W := 0x7fffff0002a527dffff
def v406 : W := 0x7fffff0002a527ef6ff
def v407 : W := 0x7fffff0002a527fefff
def v408 : W := 0x7fffff0002a527ffdff
def v409 : W := 0x406000000f004406000808c
def v410 : W := 0xf838000000000585800000
def v411 : W := 0x7f80000000000ad800000
def v412 : W := 0x7fffff0002a527fffff
def v413 : W := 0x7f80000000000d680a404
def v414 : W := 0x339c000000000118c800000
def v415 : W := 0xf838000000000a86940402
def v416 : W := 0x339c0000000002294c42001
def v417 : W := 0x4c638000000044421000000
def v418 : W := 0x49fffff98c7ff4975def98c6ee
def v419 : W := 0x4c0000000f0044c0010008a
def v420 : W := 0x4c6398c7ff0044c6318c6ee
def v421 : W := 0x49fffff98c7ff4976ef7dce6ef
def v422 : W := 0x707c0000000045028000000
def v423 : W := 0x8e7ffffe0f8ff8c6f5fde0f0dd
def v424 : W := 0x700000000f0047000400089
def v425 : W := 0x707c60f8ff004707860f0dd
def v426 : W := 0x8e7ffffe0f8ff8c6fafef4f4df
def v427 : W := 0x7f800000000045500000000
def v428 : W := 0xf07ffffff00ffe05ffadfe00bb
def v429 : W := 0x7c7f80000f0047c7b50a48f
def v430 : W := 0xf07ffffff00ffe05ffd6fea4bf
def v431 : W := 0x7fff80000000450ac800000
def v432 : W := 0x7fe380000f0047f6354848f
def v433 : W := 0x7f807f00ff0047f007e00bb
def v434 : W := 0x7ffc00000f0047f7854a08f
def v435 : W := 0x7fff800000000118c800000
def v436 : W := 0x7fff80000000000ad800000
def v437 : W := 0x7fff8000000000585800000
def v438 : W := 0x7fff80000000444a5800000
def v439 : W := 0x7fff8000000045584800000
def v440 : W := 0xf800007ffff01fa00002b5b70
def v441 : W := 0x71800007ffff073900002b5b70
def v442 : W := 0xff800007ffff012800002b5b70
def v443 : W := 0xb6000007ffff0b6880002b5b70
def v444 : W := 0xfff80007ffff0fffd5292b5b70
def v445 : W := 0xffff07c7ffff0fffd0282b5b70
def v446 : W := 0xfffcc63fffff0fffc4212b5b70
def v447 : W := 0xfffff807ffff0fffd5002b5b70
def v448 : W := 0xf07fffc7f00ffe05ff287e00bb
def v449 : W := 0x8e7fffc60f8ff8c6f57860f0dd
def v450 : W := 0x8e7fc7fe0f8ff8c6f47960f0dd
def v451 : W := 0x49ffc7f98c7ff4975c6b18c6ee
def v452 : W := 0x49fffe398c7ff4975d6318c6ee
def v453 : W := 0x7fff800000a44d5ad800000
def v454 : W := 0x7fff8000000d655ad800000
def v455 : W := 0x7fff80000000455ad800088
def v456 : W := 0x7fff80000061555ad800000
def v457 : W := 0xf07ffe3ff00ffe05ff217e00bb
def v458 : W := 0xff87fffffff0f12c7afed5ad8f
def v459 : W := 0xff87fffffff0f12c6ef7d5ad8f
def v460 : W := 0x7fff80000f0046ed6d4a48f
def v461 : W := 0x7fff80000f0045def90848e
def v462 : W := 0xff87fffffff0f12c7fd6d5ad8f
def v463 : W := 0x7fff80000f0046af6d4a48f
def v464 : W := 0x7fff80000f0047ad6d4a48f
def v465 : W := 0x7fff80000f00475fdc0a08d
def v466 : W := 0x7fff80000f0047ff7d4a48f
def v467 : W := 0x7fff80000f0047f7b54a48f
def v468 : W := 0x7fff80000f0047effd4a48f
def v469 : W := 0x7fff80000f0047fadd4008b
def v470 : W := 0x7fffffff0f0002ad6d5ad07
def v471 : W := 0x7fff80000f0047fffd4a407
def v472 : W := 0x7fff80000f0047ffed4a48f
def v473 : W := 0x7fff80000f0047fffd4a48f
def v474 : W := 0xfff8000000000ffb8000000000
def v475 : W := 0x78000000000ed38000000000
def v476 : W := 0x780000000f04930000084260
def v477 : W := 0x780000000f08c28000205050
def v478 : W := 0x780000000f0e0180002a0030
def v479 : W := 0x7800060f8ff8c6f07860f0dd
def v480 : W := 0x7180f838000001280084800000
def v481 : W := 0x7800018c7ff4974c6318c6ee
def v482 : W := 0x780000000f0ed7d5292a52f8
def v483 : W := 0xb60339c0000001280084800000
def v484 : W := 0x780007f00ffe05ff007e00bb
def v485 : W := 0xf8007f8000001280084800000
def v486 : W := 0x780007ffff049300002b5b70
def v487 : W := 0xfffffffffff0ffffffffd5ad07
def v488 : W := 0x780007ffff08c280002b5b70
def v489 : W := 0x7ffff8000008c6d5ad800000
def v490 : W := 0x780007fffff4976e735defef
def v491 : W := 0x780007ffff0e0180002b5b70
def v492 : W := 0x780007fffffe05ff527fadbf
def v493 : W := 0x780007fffff8c6fa7a75fddf
def v494 : W := 0x780007fffffed3aa527fff77
def v495 : W := 0x7ffff80000049755ad800000
def v496 : W := 0x7ffff8000f049755ad8842e8
def v497 : W := 0x7ffff800000e05d5ad800000
def v498 : W := 0x7ffff8000f0e05d5adaa00b8
def v499 : W := 0x7ffff8000f08c6d5ada050d8
def v500 : W := 0x7ffff8000f0ed7d5adaa5270
def v501 : W := 0x187fff80000013c55ad800000
def v502 : W := 0x1800038007001280086810d00
def v503 : W := 0xcfffc7ff8ffff4976c7358e6ef
def v504 : W := 0x87800000c0f00820000004040
def v505 : W := 0x607fff80000016c55ad800000
def v506 : W := 0x8780007ffff008200002b5b70
def v507 : W := 0x30003800700001280284850900
def v508 : W := 0xcf87c7ff8ff0f000285250a407
def v509 : W := 0xcfffc7ff8ffff8c6f87a70f4df
def v510 : W := 0x87ffff80000008655ad800000
def v511 : W := 0x4ffcc7f98ffff5bf4cf799efee
def v512 : W := 0x60001c0038001280094812900
def v513 : W := 0x984c6380c70f0964c6310c6ce
def v514 : W := 0x98006380c7001ba00e781cf44
def v515 : W := 0x987fff80000009655ad800000
def v516 : W := 0x9fc06380c7ff086406200c4cc
def v517 : W := 0x9fcc6380c7ff0964c6310c6ce
def v518 : W := 0x9fc06380c7ff497446308c6ec
def v519 : W := 0x9fc06398c7ff096486318c6ee
def v520 : W := 0x9fcc6380c7ff4974c6318c6ee
def v521 : W := 0xe0707c00f80f0c6707840f0cd
def v522 : W := 0x8fff07fe0ffff9eef0fee1fddd
def v523 : W := 0xe0007c00f8001ea00fc81f944
def v524 : W := 0xe7c07c00f8ff086407000e0cc
def v525 : W := 0xe07fff8000000c655ad800000
def v526 : W := 0xe7c07c00f8ff8c6d07820f0dc
def v527 : W := 0xe7f07c00f8ff8c6f07860f0dd
def v528 : W := 0xe7f07c00f8ff0c6707840f0cd
def v529 : W := 0xf800007fff0f1282a5255ad07
def v530 : W := 0xfff807ffffff0ffb80d6abff74
def v531 : W := 0xf800007fff0f1fa2a5255ff47
def v532 : W := 0xff87fffffff0f1ea2afed5fd47
def v533 : W := 0xff87fffffff0f1ba2af7d5ef47
def v534 : W := 0xf8007f80ff001aa00f681ed44
def v535 : W := 0xff87fffffff0f1fa2ad6d5ff47
def v536 : W := 0xf8007f80ff001ba00d681ef44
def v537 : W := 0xf8007f80ff001ea00d681fd44
def v538 : W := 0xf8007f80ff001fa00f781ff44
def v539 : W := 0xf8007f80ff001fa00ef81df44
def v540 : W := 0xf8007f80ff001fa00fd81fb44
def v541 : W := 0xe7c07c60f8ff0c6607860f0dd
def v542 : W := 0xf87fff8000001280084800000
def v543 : W := 0xf8007f80ff001fa00ff81ff44
def v544 : W := 0xf8007f80ff001fa00ff81fd44
def v545 : W := 0xf8007f80ff001fa00ff81ef44
def v546 : W := 0xf07ff80000000e05d500000000
def v547 : W := 0xf8007fffff0f1282ad6d5ad07
def v548 : W := 0xfffffffff00fffffffadfe00bb
def v549 : W := 0xf87fff8000001fa00ad800000
def v550 : W := 0xf87fff80000012c55ad800000
def v551 : W := 0xff80007ffff0ffb80002b5b70
def v552 : W := 0xff800000fff0ffb80002b5b70
def v553 : W := 0xf987fe3ffc70f0002a42548407
def v554 : W := 0x3007fff80000032c55ad800000
def v555 : W := 0xffffff800000fffd5ad800000
def v556 : W := 0x40780007ffff040100002b5b70
def v557 : W := 0x40780001800f04010000080020
def v558 : W := 0x407ffff80000040555ad800000
def v559 : W := 0xf9fffe3ffc7ffe05ff427e84bf
def v560 : W := 0xf9fffe3ffc7ff4976e635cc6ef
def v561 : W := 0x79fcfe39fc7ff5bf4ee79dcfee
def v562 : W := 0x4184c6398070f4154c631886ae
def v563 : W := 0x4180c039807005390c87990f22
def v564 : W := 0x4187fff80000041555ad800000
def v565 : W := 0x41fcc039807ff4054c021804aa
def v566 : W := 0x41fcc639807ff4974c6318c6ee
def v567 : W := 0x41fcc0398c7ff4154c4318c6ee
def v568 : W := 0x41fcc039807ff4974c231846ea
def v569 : W := 0x41fcc639807ff4154c631886ae
def v570 : W := 0x49800007fff0f0002a5255ad07
def v571 : W := 0x4984c638000000000000000000
def v572 : W := 0xfffffff98c7ff5bf4ce798c6ee
def v573 : W := 0x4984c6398c70f0044c6310848e
def v574 : W := 0xfffffffffffff52d6ed6ddadaf
def v575 : W := 0xfffffffffffff1ae6af6d5edcf
def v576 : W := 0x49f80000000004930000000000
def v577 : W := 0x4987fff8000000000084800000
def v578 : W := 0x4984c63ffff0f0002a5255ad07
def v579 : W := 0x4987fff80000000455ad800000
def v580 : W := 0x49fcc63ffffff4974c633bdffe
def v581 : W := 0xfffcc63ffffff5bf4c6319cfee
def v582 : W := 0x49f800018c7f0ed380002a5270
def v583 : W := 0x49f80007ffff0ed380002b5b70
def v584 : W := 0x49f8c0398c7f04930c03184662
def v585 : W := 0x49f806398c7f0493006308c664
def v586 : W := 0x49f80007fffff4932a525def67
def v587 : W := 0x49fc06398c7ff497406308c6ec
def v588 : W := 0x49fcc6380c7ff497446300c6cc
def v589 : W := 0x49fcc638000004974421000000
def v590 : W := 0xfffffff98c7fffffddef98c6ee
def v591 : W := 0xffffffffffffffffddefbbdffe
def v592 : W := 0x49fcc639807ff4974c231806aa
def v593 : W := 0x49fcc6398c7ff004484210848e
def v594 : W := 0x49fcc6398c7ff0864c6310c4ce
def v595 : W := 0x49fcc6398c7ff086486218c6ee
def v596 : W := 0x49fcc6398c7ff096486310c6ce
def v597 : W := 0x49fcc0398c7ff4974c031846ea
def v598 : W := 0x49fcc6398c7ff4054c631884ae
def v599 : W := 0x49fcc6398c7ff4054c4218c6ee
def v600 : W := 0x49fcc6398c7ff4874c6218c4ee
def v601 : W := 0x49fcc6398c7ff4154c431886ae
def v602 : W := 0x49fcc6398c7ff497446108c2ec
def v603 : W := 0x49fcc6398c7ff497486218c6ee
def v604 : W := 0x49fcc6398c7ff4974c631884ae
def v605 : W := 0x49fcc6398c7ff4974c4218c6ee
def v606 : W := 0x49fcc6398c7ff4974c211842ea
def v607 : W := 0x49fcc6398c7ff4974c6310c4ce
def v608 : W := 0x49fffff80000049744a5800000
def v609 : W := 0x4ff800018fff05fb0000095b60
def v610 : W := 0x49fffff98c7f049755ad884260
def v611 : W := 0x49fffff800000ed7d5ad800000
def v612 : W := 0x4ffffff8000005ff55ad800000
def v613 : W := 0x4ff80007ffff05fb00002b5b70
def v614 : W := 0x7007fff80000060555ad800000
def v615 : W := 0xf1fff83ff07fff2dff86ff0dbb
def v616 : W := 0x7000f801f00007290f849f0922
def v617 : W := 0x7007f801f000f6057f005e00ab
def v618 : W := 0x707cf801f00ff4054e001c00aa
def v619 : W := 0xf8007f80ff001fa00fe81ff44
def v620 : W := 0x71800007fff0f7392a525faf27
def v621 : W := 0x707ff801f00ff6057f005e00ab
def v622 : W := 0x707cf807f00ff6056f007e00bb
def v623 : W := 0x707ff801f00ffe05ff007e00bb
def v624 : W := 0xfff8f83fffff0ffb8a86bf5f72
def v625 : W := 0x71800007fff0f1282a5255ad07
def v626 : W := 0xff87fffffff0f7292fd6dfad27
def v627 : W := 0xff87fffffff0f5392ed7ddaf27
def v628 : W := 0x7180f839f07005290e869d0d22
def v629 : W := 0xff87fffffff0f7392ad6dfaf27
def v630 : W := 0x7180f839f07005390a869d0f22
def v631 : W := 0x7180f839f07007290a869f0d22
def v632 : W := 0x7180f839f07007390d879b0f22
def v633 : W := 0x7180f839f07007390f879f0f22
def v634 : W := 0x7180f839f07007390f869f0f22
def v635 : W := 0x7180f839f07007390f859f0b22
def v636 : W := 0x7180f839f07007390e879f0f22
def v637 : W := 0x7180f839f07007390f879f0d22
def v638 : W := 0x7180f839f07007390f879d0f22
def v639 : W := 0x8e7f07c0000008c6d028000000
def v640 : W := 0x7180f83ffff0f1282ad6d5ad07
def v641 : W := 0xfffffffe0f8ffffff5fde0f0dd
def v642 : W := 0x71f80007ffff0ffb80002b5b70
def v643 : W := 0x7187fff80000012c55ad800000
def v644 : W := 0x7187fff8000001280084800000
def v645 : W := 0x7187fff8000007390585800000
def v646 : W := 0x71f80001f07f0ffb80002b5b70
def v647 : W := 0x71fffff800000fffd5ad800000
def v648 : W := 0x79f80007ffff07bb00002b5b70
def v649 : W := 0x79f80001fc7f07bb00000b4b60
def v650 : W := 0x79fffff8000007bf55ad800000
def v651 : W := 0x80780007ffff080080002b5b70
def v652 : W := 0x7f87fff8000007ff55ad800000
def v653 : W := 0x80780006000f08008000200010
def v654 : W := 0xfe7fffc7ff8ff8c6fa7874f0df
def v655 : W := 0xfe07ffc7ff80f0002a5054a007
def v656 : W := 0xfe7fffc7ff8ffe05ff507ea0bf
def v657 : W := 0x867f01c6038ff804f010602099
def v658 : W := 0x860707c60380f844f07860b09d
def v659 : W := 0x807ffff800000804d5ad800000
def v660 : W := 0x8607fff800000844d5ad800000
def v661 : W := 0x8e0707c0000000000000000000
def v662 : W := 0xfffffffe0f8ff9eef0fce0f0dd
def v663 : W := 0x867f07c6038ff844f07860b09d
def v664 : W := 0x867f01c6038ff8c6f0386070d9
def v665 : W := 0x867f01c60f8ff844f05860f0dd
def v666 : W := 0x8e000007fff0f0002a5255ad07
def v667 : W := 0x867f07c6038ff8c6f07860f0dd
def v668 : W := 0x8e0707c60f80f004707840a08d
def v669 : W := 0xfffffffffffff92cfad6f5ad9f
def v670 : W := 0x8e780000000008c28000000000
def v671 : W := 0x8e07fff8000000000084800000
def v672 : W := 0x8e0707c7fff0f0002a5255ad07
def v673 : W := 0x8e07fff80000000455ad800000
def v674 : W := 0x8e7f07c7fffff8c6f0786bfbfd
def v675 : W := 0xffff07c7fffff9eef07861f9dd
def v676 : W := 0x8e7800060f8f0ed380002a5270
def v677 : W := 0x8e780007fffff8c2aa5275fd57
def v678 : W := 0x8e780007ffff0ed380002b5b70
def v679 : W := 0x8e7807c60f8f08c2807820f054
def v680 : W := 0x8e7b01c60f8f08c2b018607051
def v681 : W := 0x8e7f01c60f8ff8c6f0186070d9
def v682 : W := 0x8e7c07c60f8ff8c6c07820f0dc
def v683 : W := 0x8e7f07c60f8ff086607060f0dd
def v684 : W := 0x8e7f07c00f8ff8c6d07800f0cc
def v685 : W := 0x8e7f07c6038ff8c6f038603099
def v686 : W := 0xfffffffffffffffff5fdebfbfd
def v687 : W := 0x8e7f07c60f8ff004605040a08d
def v688 : W := 0x8e7f07c60f8ff0c6607840f0cd
def v689 : W := 0x8e7f07c60f8ff086707840e0cd
def v690 : W := 0x8e7f07c60f8ff804f07860a09d
def v691 : W := 0x8e7f07c60f8ff804f05060f0dd
def v692 : W := 0x8e7f07c60f8ff886f07060e0dd
def v693 : W := 0x8e7f07c60f8ff844f05860b09d
def v694 : W := 0x8e7f07c60f8ff8c6d06820d0dc
def v695 : W := 0x8e7f07c60f8ff8c6f05060f0dd
def v696 : W := 0x8e7f07c60f8ff8c6f0286050d9
def v697 : W := 0x8e7f07c60f8ff8c6e07060f0dd
def v698 : W := 0x8e7f07c60f8ff8c6f07860a09d
def v699 : W := 0x8e7f07c60f8ff8c6f07840e0cd
def v700 : W := 0x8e7ffffe0f8f08c6d5ada05050
def v701 : W := 0x8e7ffff8000008c6d0ac800000
def v702 : W := 0x8e7ffff800000ed7d5ad800000
def v703 : W := 0x8ff80007ffff09fa80002b5b70
def v704 : W := 0x8ff800060fff09fa8000215b50
def v705 : W := 0xb6000007fff0fb68aa5277bd17
def v706 : W := 0xb007f8067000fa04ff0076009b
def v707 : W := 0xb007fff800000a04d5ad800000
def v708 : W := 0xb07f3806700ff804f200640099
def v709 : W := 0xb07ff806700ffa04ff0076009b
def v710 : W := 0xb07f3806700ffe05f7006e00b9
def v711 : W := 0xb07f3807f00ffa04fb007e00bb
def v712 : W := 0xb07ff806700ffe05ff007e00bb
def v713 : W := 0xb6000007fff0f1282a5255ad07
def v714 : W := 0xb607fff8000001280084800000
def v715 : W := 0xb60339c7fff0f1282ad6d5ad07
def v716 : W := 0xb607fff800000b68918c800000
def v717 : W := 0xb607fff80000012c55ad800000
def v718 : W := 0xf0000007fff0f0002a5255ad07
def v719 : W := 0xbe780007ffff0bea80002b5b70
def v720 : W := 0xb67ffff800000fffd5ad800000
def v721 : W := 0xb6780007ffff0ffb80002b5b70
def v722 : W := 0xbe7800067f8f0bea8000235950
def v723 : W := 0xcff80007ffff0cd380002b5b70
def v724 : W := 0xbf87fff800000bfed5ad800000
def v725 : W := 0xbe7ffff800000beed5ad800000
def v726 : W := 0xcff800078fff0cd38000285270
def v727 : W := 0xcffffff800000cd7d5ad800000
def v728 : W := 0xf007f800000000000000000000
def v729 : W := 0xfffffffff00fff2dff84fe00bb
def v730 : W := 0xb6780006738f0ffb80002b5b70
def v731 : W := 0xf078000000000e018000000000
def v732 : W := 0xf007fff8000000000084800000
def v733 : W := 0xf007f807fff0f0002a5255ad07
def v734 : W := 0xf007fff80000000455ad800000
def v735 : W := 0xf07ff807fffffe05ff007f5bfb
def v736 : W := 0xfffff807ffffff2dff007f09bb
def v737 : W := 0xf0780007f00f0ed380002a5270
def v738 : W := 0xf078f807f00f0e018f003e0032
def v739 : W := 0xf0780007ffff0ed380002b5b70
def v740 : W := 0xf0780007fffffe01aa527fad37
def v741 : W := 0xf07b3807f00f0e01b3006e0031
def v742 : W := 0xf07f3807f00ffe05f3006e00b9
def v743 : W := 0xf07cf807f00ffe05cf003e00ba
def v744 : W := 0xf07ff806700ffe05f700660099
def v745 : W := 0xf07ff801f00ffe05df001e00aa
def v746 : W := 0xf07ff807f00ff0046a0054008b
def v747 : W := 0xffffffffffffffffffadff5bfb
def v748 : W := 0xf07ff807f00ff6056f005e00ab
def v749 : W := 0xf07ff807f00ff4056e007e00bb
def v750 : W := 0xf07ff807f00ff4057f005c00ab
def v751 : W := 0xf007f807f000f0047f0054008b
def v752 : W := 0xf07ff807f00ffa04fb0076009b
def v753 : W := 0xf07ff807f00ff804ff0074009b
def v754 : W := 0xf07ff807f00ffc05fe007c00bb
def v755 : W := 0xf07ff807f00ffe05ff0074009b
def v756 : W := 0xf07ff807f00ffe05f5006a00b9
def v757 : W := 0xf07ff807f00ffe05dd003a00ba
def v758 : W := 0xf07ff807f00ffe05ee007e00bb
def v759 : W := 0xf07ff807f00ffe05fa007e00bb
def v760 : W := 0xf07ff807f00ffe05ff005c00ab
def v761 : W := 0xf07ffff800000e05d584800000
def v762 : W := 0xf07ffffff00f0e05d5adaa0030
def v763 : W := 0xf07ffff800000ed7d5ad800000
def v764 : W := 0xff800000000001280000000000
def v765 : W := 0xf9f80007ffff0e9380002b5b70
def v766 : W := 0xf6780007ffff0f6980002b5b70
def v767 : W := 0xf1fffff800000f3dd5ad800000
def v768 : W := 0xf1f80007ffff0f3980002b5b70
def v769 : W := 0xf6780007f38f0f6980002b1930
def v770 : W := 0xf787fff800000f7dd5ad800000
def v771 : W := 0xf67ffff800000f6dd5ad800000
def v772 : W := 0xf9f80007fc7f0e9380002a4270
def v773 : W := 0xfe780007ffff0ec380002b5b70
def v774 : W := 0xf9fffff800000e97d5ad800000
def v775 : W := 0xfe780007ff8f0ec380002a5070
def v776 : W := 0xfe7ffff800000ec7d5ad800000
def v777 : W := 0xff83fff800000ffb95ad800000
def v778 : W := 0xf1f80007f07f0f3980002b0b30
def v779 : W := 0xfffff807ffff0ffb80002b5b70
def v780 : W := 0xfff807ffffff0ffb8084ab5b70
def v781 : W := 0xfff8f83fffff0ffb8084ab5b70
def v782 : W := 0xfffb39c7ffff0ffb8084ab5b70
def v783 : W := 0xffff07c7ffff0ffb80002b5b70
def v784 : W := 0xfffcc63fffff0ffb80002b5b70
def v785 : W := 0xfffffffffff0ff2dffd6d5ad07
def v786 : W := 0xff87fffffff0f7392fd7d5ad07
def v787 : W := 0xff87fffffff0f1fa2affd5ad07
def v788 : W := 0xfffffffffff0f5bf6ef7d5ad07
def v789 : W := 0xff87fffffff0fb68bbded5ad07
def v790 : W := 0xfffffffffff0f9eefafed5ad07
def v791 : W := 0xff87fff80000012800ad800000
def v792 : W := 0xfffffffffff0fffbaad6d5ad07
def v793 : W := 0xff87fff800000128118c800000
def v794 : W := 0xff87fff8000001280585800000
def v795 : W := 0xff87fff8000007290584800000
def v796 : W := 0xff87fff8000001ea00ac800000
def v797 : W := 0xff87fff80000012c5584800000
def v798 : W := 0xff87fff80000012c50ac800000
def v799 : W := 0xff87fff800000168008c800000
def v800 : W := 0xff87fff8000001380085800000
def v801 : W := 0xff87fff8000001ba00a5800000
def v802 : W := 0xff87fff8000001fe55ad800000
def v803 : W := 0xff87fff8000001fa0084800000
def v804 : W := 0xff87fff8000005390485800000
def v805 : W := 0xff87fff8000003280184800000
def v806 : W := 0xff87fff800000b688084800000
def v807 : W := 0xff87fff80000073d55ad800000
def v808 : W := 0xff87fff8000007390084800000
def v809 : W := 0xff87fff800000968908c800000
def v810 : W := 0xff87fff8000007fb05ad800000
def v811 : W := 0xff87fff800000b289184800000
def v812 : W := 0xff87fff800000bfa91ad800000
def v813 : W := 0xff87fff800000b6cd5ad800000
def v814 : W := 0xff87fff80ff001280084810900
def v815 : W := 0xff87fff800000f79958d800000
def v816 : W := 0xff87fff80000012c44a5800000
def v817 : W := 0xf07ff807f00ff804fa007e00bb
def v818 : W := 0x8ffffff8000009fed5ad800000
def v819 : W := 0xff87fffe0f8001280084800000
def v820 : W := 0xff87fff9f07001280084810900
def v821 : W := 0xff87fff98c7001280084800000
def v822 : W := 0xff87fff9f070073900848b0b20
def v823 : W := 0xff87fffe73800b688084a31910
def v824 : W := 0xff87fffe738001280084810900
def v825 : W := 0xff87fffff00001280084800000
def v826 : W := 0xffffffffffffffffffffffff77
def v827 : W := 0xff87fffffff0073905858b0b20
def v828 : W := 0xff87fffffff001fa00ad815b40
def v829 : W := 0xff87fffffff00b68918ca31910
def v830 : W := 0xfff80007ffff01aa0000014940
def v831 : W := 0xfff800018c7f0ffb8000084260
def v832 : W := 0xff87ffffffff01280084ab5b70
def v833 : W := 0xfff800000ff00ffb8000015b40
def v834 : W := 0xfff80007f00f0ffb80002a0030
def v835 : W := 0xfff800060f8f0ffb8000205050
def v836 : W := 0xfff80001f0700ffb80000b0b20
def v837 : W := 0xfff8000673800ffb8000231910
def v838 : W := 0xfff80007fff0fffbaa5255ad07
def v839 : W := 0xfff80007fff00ffb8000010900
def v840 : W := 0xfff80007ffff07bb00000b4b60
def v841 : W := 0xffffffffffff0fffd5ad894b60
def v842 : W := 0xfff80007ffff05290000090920
def v843 : W := 0xfff80007ffff05bb00002b5b70
def v844 : W := 0xfff80007ffff05fb0000095b60
def v845 : W := 0xffffffffffff0fffd5ada15950
def v846 : W := 0xfff80007ffff09288000210910
def v847 : W := 0xfff80007ffff09ea80002b5b70
def v848 : W := 0xfff80007fffff5bb2a525defef
def v849 : W := 0xfff80007ffff0f2980002b5b70
def v850 : W := 0xfff80007ffff0dfb8000295b70
def v851 : W := 0xfff80007ffff0bea8000235950
def v852 : W := 0xfff80007ffff0ed380002a5270
def v853 : W := 0xffffffffffff0fffd5adab0930
def v854 : W := 0xfff80007ffff0feb80002b5970
def v855 : W := 0xfff80007ffff0f6980002b1930
def v856 : W := 0xfff80007ffff0f3980002b0b30
def v857 : W := 0xfff80007ffff0fbb80002b4b70
def v858 : W := 0xfff80007ffff0ffb8000215950
def v859 : W := 0xfff80007ffff0ffb8000094b60
def v860 : W := 0xfff80007ffff0ffb80002b0930
def v861 : W := 0xfff80007fffffffbaa527fffff
def v862 : W := 0xfff80007ffffff29aa527fadbf
def v863 : W := 0xfff80007fffff9eaaa5275fddf
def v864 : W := 0xfffffff80000052d4484800000
def v865 : W := 0xfffffff8000001ae40a4800000
def v866 : W := 0xfffffff8000005bb0084800000
def v867 : W := 0xfffffff80000092cd084800000
def v868 : W := 0xfffffff8000005ff44ad800000
def v869 : W := 0xfffffff8000005bf55ad800000
def v870 : W := 0xfffffff8000007bf45a5800000
def v871 : W := 0xfffffff8000009ea8084800000
def v872 : W := 0xfffffff800000ffb918c800000
def v873 : W := 0xfffffff800000f3dd585800000
def v874 : W := 0xfffffff800000ed7d529000000
def v875 : W := 0xfffffff800000beed1ac800000
def v876 : W := 0xfffffff8000009fed0ad800000
def v877 : W := 0xfffffff800000dffd4ad800000
def v878 : W := 0xfffffff800000f298084800000
def v879 : W := 0xfffffff800000f2dd5ad800000
def v880 : W := 0xfffffff800000fbfd5a5800000
def v881 : W := 0xfffffff800000f6dd58c800000
def v882 : W := 0xfffffff800000fefd5ac800000
def v883 : W := 0xfffffff800000ffb8585800000
def v884 : W := 0xfffffff800000ffb80ad800000
def v885 : W := 0xfffffff800000fffd5ad805240
def v886 : W := 0xfffffff800000fffd0ac800000
def v887 : W := 0xfffffff800000fffc4a5800000
def v888 : W := 0xfffffff800000fffd584800000
def v889 : W := 0xfffffff800000fffd5ad804240
def v890 : W := 0xfffffff800000fffd5ad800088
def v891 : W := 0xfffffff800000fffd5ad805040
def v892 : W := 0xfffffff800000fffd5ada01010
def v893 : W := 0xfffffff800000fffd5ad8a0020
def v894 : W := 0xfffffff800000fffd5ad880220
def v895 : W := 0xfffffff800000fffd5ad8a0220
def v896 : W := 0xfffffff800000fffd5ada21010
def v897 : W := 0xfffffff800000fffd5ada20010
def v898 : W := 0xfffffff8000009eed5ad800000
def v899 : W := 0xfff80007ffff09fa8000215b50
def v900 : W := 0xfffffff8000f0fffd5ada00098
def v901 : W := 0xfffffff8000f0fffd5ad8040c8
def v902 : W := 0xfffffff8000f0f2dd584aa00b8
def v903 : W := 0xfffffff8000f09eed0aca050d8
def v904 : W := 0xfffffff8000f0ffb8084aa5270
def v905 : W := 0xfffffff8000f0fffd5ad884260
def v906 : W := 0xfffffff8000f0fffd5ad8800a8
def v907 : W := 0xfffffff8000f0fffd5adaa0030
def v908 : W := 0xfffffff8000f0fffd5ada05050
def v909 : W := 0xfffffff8000f0fffd5ada852f8
def v910 : W := 0xfffffff8000f0fffd5adaa42f8
def v911 : W := 0xfffffff8000f0fffd5adaa50f8
def v912 : W := 0xfffffff80ff00fffd5ad810900
def v913 : W := 0xfffffff803800fffd5ad811900
def v914 : W := 0xfffffff8000fffffd5ad800088
def v915 : W := 0xfffffff8000f0fffd5adaa52f8
def v916 : W := 0xfffffff800700fffd5ad810b00
def v917 : W := 0xfffffff80c700fffd5ad804240
def v918 : W := 0xfffffff80c0f0fffd5ad804040
def v919 : W := 0xfffffff80f800fffd5ad805040
def v920 : W := 0xfffffff9800f0fffd5ad880020
def v921 : W := 0xfffffff80fff0fffd5adab5b70
def v922 : W := 0xfffffff870000fffd5ad830900
def v923 : W := 0xfffffff98c700fffd5ad800000
def v924 : W := 0xfffffff980700fffd5ad880220
def v925 : W := 0xfffffff9f07f0fffd5adab5b70
def v926 : W := 0xfffffff98fff0fffd5ad895b60
def v927 : W := 0xfffffff98c7f0fffd5ad8842e8
def v928 : W := 0xfffffff98c7f0fffd5adaa5270
def v929 : W := 0xfffffff9f0700fffd5ad810900
def v930 : W := 0xfffffff9f0000fffd5ad8a0020
def v931 : W := 0xfffffffe03800fffd5ada01010
def v932 : W := 0xfffffff9fff00fffd5ad8b5b60
def v933 : W := 0xfffffff9fc7f0fffd5ad8b4b60
def v934 : W := 0xfffffffe000f0fffd5ada00010
def v935 : W := 0xfffffffe0f8f09ea8084a05050
def v936 : W := 0xfffffffe0f800fffd5ad800000
def v937 : W := 0xfffffffe7f8f0fffd5ada35950
def v938 : W := 0xfffffffe70000fffd5ada20010
def v939 : W := 0xfffffffe0f8f0fffd5adaa5270
def v940 : W := 0xfffffffe0f8f0fffd5ada050d8
def v941 : W := 0xfffffffe0fff0fffd5ada15b50
def v942 : W := 0xfffffffe73800fffd5ad810900
def v943 : W := 0xfffffffe738f0fffd5adab5b70
def v944 : W := 0xfffffffff00f0f298084aa0030
def v945 : W := 0xffffffff8fff0fffd5ada85270
def v946 : W := 0xfffffffe7ff00fffd5ada35b50
def v947 : W := 0xfffffffff0000fffd5ad800000
def v948 : W := 0xfffffffff00f0fffd5adaa00b8
def v949 : W := 0xfffffff98c7f05bb0084884260
def v950 : W := 0xfffffffffff00fffd5ad8b0b20
def v951 : W := 0xfffffffffc7f0fffd5adaa4270
def v952 : W := 0xfffffffff38f0fffd5adab1930
def v953 : W := 0xfffffffff07f0fffd5adab0b30
def v954 : W := 0xfffffffff3f00fffd5adab1b30
def v955 : W := 0xffffffffff8f0fffd5adaa5070
def v956 : W := 0xfffffffffff00fffd5ad815b40
def v957 : W := 0xfffffffffff00fffd5ada31910
def v958 : W := 0xffffffffffff0fffd584ab5b70
def v959 : W := 0xffffffffffff0fffc4a5ab5b70
def v960 : W := 0xffffffffffff0fffd0acab5b70
def v961 : W := 0xfff80007ffff0ffb80292b5b70
def v962 : W := 0xfff80007ffff0ffb80212b5b70
def v963 : W := 0xffffffffffff0fffd5adab5bf8
def v964 : W := 0xfff80007ffff0ffb80282b5b70
def v965 : W := 0xfff80007ffff0ffb85002b5b70
def v966 : W := 0xfff80007ffff0ffb84012b5b70
def v967 : W := 0xfff8003fffff0ffb8085ab5b70
def v968 : W := 0xfff80007fffffffb88423bdffe
def v969 : W := 0xfff80007ffff0ffb91002b5b70
def v970 : W := 0xfff80007ffff0ffb90082b5b70
def v971 : W := 0xfff80007ffff0ffb91082b5b70
def v972 : W := 0xfff80007fffffffbaa007f5bfb
def v973 : W := 0xfff80007fffffffba0506bfbfd
def v974 : W := 0xfff807c7ffff0ffb80282b5b70
def v975 : W := 0xfff8063fffff0ffb80212b5b70
def v976 : W := 0xfff801c7ffff0ffb808cab5b70
def v977 : W := 0xfff8063fffff0ffb80632bdf74
def v978 : W := 0xfff807f800000ffb80ad800000
def v979 : W := 0xfff807c7ffff0ffb80782bfb74
def v980 : W := 0xfff8f807ffff0ffb8f003f5b72
def v981 : W := 0xfff83807ffff0ffb8184ab5b70
def v982 : W := 0xfff8c03fffff0ffb8c033b5f72
def v983 : W := 0xfff8c03fffff0ffb84012b5b70
def v984 : W := 0xfff8f807ffff0ffb85002b5b70
def v985 : W := 0xfff8f83800000ffb8585800000
def v986 : W := 0xfff8ffffffff0ffb85adab5b70
def v987 : W := 0xfff80007ffff0ffb85012b5b70
def v988 : W := 0xfffffffff00f0fffd5adaa5270
def v989 : W := 0xfffffff8000f05bf44a58842e8
def v990 : W := 0xfffb39c7ffff0ffba294ef7b71
def v991 : W := 0xfffb39c000000ffb918c800000
def v992 : W := 0xfffb3807ffff0ffb91002b5b70
def v993 : W := 0xfffb01c7ffff0ffbb0186b7b71
def v994 : W := 0xfffb3807ffff0ffbb3006f5b71
def v995 : W := 0xfffbf9ffffff0ffb958dab5b70
def v996 : W := 0xfffb3fffffff0ffb91adab5b70
def v997 : W := 0xf07ff807f00ffe05ff217e00bb
def v998 : W := 0xf07ff807f00ffe05ff287e00bb
def v999 : W := 0xf07ff807f00ffe45ff007e10bb
def v1000 : W := 0xf07ff807f00ffe15ff017e00bb
def v1001 : W := 0xf07ff807f00ffe15ff007e02bb
def v1002 : W := 0xf07ff807f00ffe15ff017e02bb
def v1003 : W := 0xf07ff807f00ffe45ff087e10bb
def v1004 : W := 0xf07ff807f00ffe45ff087e00bb
def v1005 : W := 0xf1fff83ff07ffe05ff027e04bb
def v1006 : W := 0xf07ff83ff00ffe05ff037e04bb
def v1007 : W := 0xf07ff807f38ffe05ff107e30bb
def v1008 : W := 0xf07ff9c7f00ffe05ff187e20bb
def v1009 : W := 0xf1fff807f07ffe15ff007e02bb
def v1010 : W := 0xf1fff83ff00ffe15ff017e00bb
def v1011 : W := 0xf67ff807f38ffe45ff007e10bb
def v1012 : W := 0xf67ff9c7f38ffe05ff107e20bb
def v1013 : W := 0xf67ff9c7f00ffe45ff087e00bb
def v1014 : W := 0xf9fff807fc7ffe05ff007e00bb
def v1015 : W := 0xfe7ff807ff8ffe05ff007e00bb
def v1016 : W := 0x8e7f07c60f8ff8d6f07860f2dd
def v1017 : W := 0x8e7f07c60f8ff8c6f57860f0dd
def v1018 : W := 0x8e7f07c60f8ff8c6f47960f0dd
def v1019 : W := 0x8e7f07c60f8ff8d6f07960f2dd
def v1020 : W := 0x8e7f07c60f8ff8d6f07960f0dd
def v1021 : W := 0x8e7f07c67f8ff8c6f27866f0dd
def v1022 : W := 0x8e7f07c60f8ffac6f17862f0dd
def v1023 : W := 0x8e7f07c60f8ffac6f17860f0dd
def v1024 : W := 0x8e7f07c60ffff8c6f07a60f6dd
def v1025 : W := 0x8e7f3fc60f8ff8c6f37864f0dd
def v1026 : W := 0x8e7f07fe0f8ff8c6f07b60f4dd
def v1027 : W := 0x8fff07fe0f8ff8d6f07960f0dd
def v1028 : W := 0x8fff07c60ffff8d6f07860f2dd
def v1029 : W := 0x8fff07fe0ffff8c6f07a60f4dd
def v1030 : W := 0xbe7f3fc60f8ffac6f17860f0dd
def v1031 : W := 0xbe7f07c67f8ffac6f07862f0dd
def v1032 : W := 0xbe7f3fc67f8ff8c6f27864f0dd
def v1033 : W := 0xcfff07c78ffff8c6f07860f0dd
def v1034 : W := 0xfe7f07c7ff8ff8c6f07860f0dd
def v1035 : W := 0x8e7f07c60f8ffac6f07862f0dd
def v1036 : W := 0xf07ff807f07ffe05ff027e06bb
def v1037 : W := 0x49fcc6398c7ff6974c631ac6ee
def v1038 : W := 0x49fcc6398c7ff4975c6b18c6ee
def v1039 : W := 0x49fcc6398c7ff4975d6318c6ee
def v1040 : W := 0x49fcc6398c7ff4d74c6b18c6ee
def v1041 : W := 0x49fcc6398c7ff4d74c6318d6ee
def v1042 : W := 0x49fcc6398c7ff4d74c6b18d6ee
def v1043 : W := 0x49fcc639fc7ff4974e631ec6ee
def v1044 : W := 0x49fcc6398c7ff6974d631ac6ee
def v1045 : W := 0x49fcc6398c7ff6974d6318c6ee
def v1046 : W := 0x49fcc6398ffff4974c7318f6ee
def v1047 : W := 0x49fcfe398c7ff4974f631cc6ee
def v1048 : W := 0x49fcc7f98c7ff4974c7b18e6ee
def v1049 : W := 0x4ffcc7f98c7ff4d74c6b18c6ee
def v1050 : W := 0x4ffcc6398ffff4d74c6318d6ee
def v1051 : W := 0x4ffcc7f98ffff4974c7318e6ee
def v1052 : W := 0x79fcfe398c7ff6974d6318c6ee
def v1053 : W := 0x79fcc639fc7ff6974c631ac6ee
def v1054 : W := 0x79fcfe39fc7ff4974e631cc6ee
def v1055 : W := 0xbe7f3fc67f8ff9eef2fce5f9dd
def v1056 : W := 0x860301c603800968b09ce13911
def v1057 : W := 0xf67ff9c7f38fff2dff94ff29bb
def v1058 : W := 0xb003380670000b28b384e70911
def v1059 : W := 0xb60339c673800b28a294e72911
def v1060 : W := 0xb60339c673800968a294e53911
def v1061 : W := 0xff87fffffff0f968badef5bd17
def v1062 : W := 0xff87fffffff0fb68aad6f7bd17
def v1063 : W := 0xff87fffffff0fb28bbd6f7ad17
def v1064 : W := 0xb60339c673800928b294e52911
def v1065 : W := 0xb60339c673800b68b19ce33911
def v1066 : W := 0xb60339c673800b68b39ce73911
def v1067 : W := 0xb60339c673800b68b394e73911
def v1068 : W := 0xb60339c673800b68b38ce71911
def v1069 : W := 0xb60339c673800b68b29ce73911
def v1070 : W := 0xb60339c673800b68b39ce72911
def v1071 : W := 0xb60339c673800b68b39ce53911
def v1072 : W := 0xf9fcc63ffc7ff4974c6318c6ee
def v1073 : W := 0xcffcc63f8ffff4974c6318c6ee
def v1074 : W := 0xfffb01c7ffff0ffb90082b5b70
def v1075 : W := 0xff87fff80ff001fa0084815b40
def v1076 : W := 0x707cf801f00ffe05df003e00ba
def v1077 : W := 0xc20028005040
def v1078 : W := 0x920021004240
def v1079 : W := 0x6110501000000
def v1080 : W := 0x4110401080220
def v1081 : W := 0xd20029000000
def v1082 : W := 0xd20000005240
def v1083 : W := 0x61100000a0220
def v1084 : W := 0x60105000a0020
def v1085 : W := 0xa408000221010
def v1086 : W := 0xa009100220010
def v1087 : W := 0x8409008201010
def v1088 : W := 0xa409108000000
def v1089 : W := 0xf000000000842e8
def v1090 : W := 0xf800000005000f044
def v1091 : W := 0xf000000002a5270
def v1092 : W := 0xf000000002a00b8
def v1093 : W := 0xf000000002050d8
def v1094 : W := 0xc700000004200c644
def v1095 : W := 0xc0ff000004000c0cc
def v1096 : W := 0xff000000000015b40
def v1097 : W := 0x1800ff00008001800aa
def v1098 : W := 0x60f8f00000000205050
def v1099 : W := 0x18c7f00000000084260
def v1100 : W := 0x1f00000000a001e0022
def v1101 : W := 0x1f070000000000b0b20
def v1102 : W := 0x6038000002010603011
def v1103 : W := 0x6000ff0002000600099
def v1104 : W := 0x6700000002200660011
def v1105 : W := 0x6738000000000231910
def v1106 : W := 0x78ffff000285278f6ff
def v1107 : W := 0x7f00f000000002a0030
def v1108 : W := 0x1807000000802180622
def v1109 : W := 0x7ff8ff0002a507ef0ff
def v1110 : W := 0x7fc7ff0002a427ec6ff
def v1111 : W := 0x7fffff00008423bdffe
def v1112 : W := 0x7fffff0002a007f5bfb
def v1113 : W := 0x7fffff00020506bfbfd
def v1114 : W := 0x301c0000000003018402001
def v1115 : W := 0xc038000000000c03100402
def v1116 : W := 0x7c000000000007800a004
def v1117 : W := 0x638000000000063008404
def v1118 : W := 0xf800000000000f00140002
def v1119 : W := 0x33800000000003300440001
def v1120 : W := 0x4c6380000f0000842108406
def v1121 : W := 0x707c00000f000205040a005
def v1122 : W := 0x7f8000000f0002a00540003
def v1123 : W := 0x780000000f040544000800a8
def v1124 : W := 0x780000000008c6d028000000
def v1125 : W := 0x780000000004974421000000
def v1126 : W := 0x78000000000e05d500000000
def v1127 : W := 0x780000000f008640200040c8
def v1128 : W := 0x780000000f0804d000200098
def v1129 : W := 0x780000000f0cd7d4292852f8
def v1130 : W := 0x780000000f0e97d5212a42f8
def v1131 : W := 0x780000000f0ec7d5282a50f8
def v1132 : W := 0x6000000038001680000011900
def v1133 : W := 0x7ff800000ffe05ff007e00bb
def v1134 : W := 0x7f07c0000ff8c6f07860f0dd
def v1135 : W := 0x7cc638000ff4974c6318c6ee
def v1136 : W := 0x1800038007000100003000600
def v1137 : W := 0x1800038000001380085800000
def v1138 : W := 0x1800000007001380000010b00
def v1139 : W := 0x60001c0038000400018003000
def v1140 : W := 0x60001c000000168008c800000
def v1141 : W := 0x80406000c00f0000040008004
def v1142 : W := 0x80006000c000082006000c044
def v1143 : W := 0x87c0600000000864020000000
def v1144 : W := 0x87cc6380c0ff0864c6310c4ce
def v1145 : W := 0x87c06000c0ff8c6d06820d0dc
def v1146 : W := 0x87c06000c0ff497446108c2ec
def v1147 : W := 0x87c06060f8ff086607060f0dd
def v1148 : W := 0x87c06018c7ff086486218c6ee
def v1149 : W := 0x9800638000000920021000000
def v1150 : W := 0x98000000c7000920000004240
def v1151 : W := 0x87f07c00c0ff086707840e0cd
def v1152 : W := 0x98006380c7000000042008404
def v1153 : W := 0xe0007c0000000c20028000000
def v1154 : W := 0x9f806380c7f0497446308c6ec
def v1155 : W := 0x98006398c7ff092086318c6ee
def v1156 : W := 0xe0000000f8000c20000005040
def v1157 : W := 0xe0007c00f800000005000a004
def v1158 : W := 0xe0007c60f8ff0c2207860f0dd
def v1159 : W := 0xe7807c00f8f08c6d07820f0dc
def v1160 : W := 0xf8000000ff001280000010900
def v1161 : W := 0xf800000000001fa0000000000
def v1162 : W := 0xf8007c00ff001fa007801fb44
def v1163 : W := 0xf8006380ff001fa006301df44
def v1164 : W := 0xf8007f80f8001fa00fd80f044
def v1165 : W := 0xf8007f80c7001fa00ef80c644
def v1166 : W := 0xf87fff80ff0f1282ad6d5ad07
def v1167 : W := 0xf8007f80ff001fa00ff81ad04
def v1168 : W := 0x30000000700003280000030900
def v1169 : W := 0xff807f800000fffd5ad800000
def v1170 : W := 0x30003800000003280184800000
def v1171 : W := 0x4004c0018000f0000800100002
def v1172 : W := 0x4000c001800004010c00180022
def v1173 : W := 0x30003800700002000300060000
def v1174 : W := 0x407cc000000004054400000000
def v1175 : W := 0x407cc0018c7ff4054c4218c6ee
def v1176 : W := 0x407cc001800ff4974c211842ea
def v1177 : W := 0x407cc001800ffe05dd003a00ba
def v1178 : W := 0x4180c039807000000802100402
def v1179 : W := 0x407ff801800ff4057f005c00ab
def v1180 : W := 0x407cc639800ff4054c631884ae
def v1181 : W := 0x407cc007f00ff4056e007e00bb
def v1182 : W := 0x4180c038000004110401000000
def v1183 : W := 0x41800001807004110000080220
def v1184 : W := 0x41f8c039807f04974c231846ea
def v1185 : W := 0x4180c0398c7ff4110c4318c6ee
def v1186 : W := 0x487cc6018c0ff4874c6018c0ee
def v1187 : W := 0x498000018c7000000000000000
def v1188 : W := 0x4984c6398c7ff000084218c6ee
def v1189 : W := 0x4984c6398c70f092086310c646
def v1190 : W := 0x4984c6398c70f4110c43188626
def v1191 : W := 0x4987fff98c70f0002ad6d4a407
def v1192 : W := 0x49f800018c7f049744210842e8
def v1193 : W := 0x49fc06018c7ff497406008c2ec
def v1194 : W := 0x49fcc0018c7ff4974c001842ea
def v1195 : W := 0x49fcc639800ff4974c211800aa
def v1196 : W := 0x49fcc6380000f4974c6310848e
def v1197 : W := 0x49fcc63800000ed7d529000000
def v1198 : W := 0x49fcc6380c700497446300c644
def v1199 : W := 0x49fcc6380c0ff497446100c0cc
def v1200 : W := 0x49fcc6398c70f4974c63108406
def v1201 : W := 0x49fcc639807004974c23180622
def v1202 : W := 0x49fcc6398c7ffcd7dc6b38d6fe
def v1203 : W := 0x7000f801f00000000a00140002
def v1204 : W := 0x49fcc63f8ffff4976c7378f6ff
def v1205 : W := 0x49fcc6398c7ffed7dd6b18c6ee
def v1206 : W := 0x49fcc6398c7ffed7cc633ad6fe
def v1207 : W := 0x49fcc63ffc7ff4976e637ec6ff
def v1208 : W := 0x49fffe398c7ff4977f635cc6ef
def v1209 : W := 0x49ffc7f98c7ff4977c7b58e6ef
def v1210 : W := 0x4ffcc7f98c7ff5ff4cef98c6ee
def v1211 : W := 0x4f84c7f98ff0f12808d691ad06
def v1212 : W := 0x4ffcc7f8000005ff44ad800000
def v1213 : W := 0x4ffcc6398ffff5ff4c6319dfee
def v1214 : W := 0x70000001f000060100000a0020
def v1215 : W := 0x7000f800000006010500000000
def v1216 : W := 0x7000f807f00ff6012f007e00bb
def v1217 : W := 0x71800001f07001280000010900
def v1218 : W := 0x7078f801f00f0e05df003e00ba
def v1219 : W := 0x71800000000007390000000000
def v1220 : W := 0x7180c039f07007390c031b0f22
def v1221 : W := 0x7180f801f07007390f001f0b22
def v1222 : W := 0x7180f839807007390d87980622
def v1223 : W := 0x7180f839f00007390f859e0022
def v1224 : W := 0x7180f839f07007390f87950d02
def v1225 : W := 0x7187fff9f070f1282ad6d5ad07
def v1226 : W := 0x8003000600000800b000600011
def v1227 : W := 0x79fcfe398c7ff7bf4de798c6ee
def v1228 : W := 0x7984fe39fc70f1280ac6958d06
def v1229 : W := 0x71f8f83800000fffd5ad800000
def v1230 : W := 0x79fcfe38000007bf45a5800000
def v1231 : W := 0x79fcc639fc7ff7bf4c631bcfee
def v1232 : W := 0x7f800001fff007fb00000b5b60
def v1233 : W := 0x7f80fff9fff001280ad695ad06
def v1234 : W := 0x7f80fff8000007fb05ad800000
def v1235 : W := 0x807f000000000804d000000000
def v1236 : W := 0x800700060000f0002000400001
def v1237 : W := 0x86000006038008408000201010
def v1238 : W := 0x807f0006000ffe05f5006a00b9
def v1239 : W := 0x807f0006000ff8c6f0286050d9
def v1240 : W := 0x807f07c6000ff804f07860a09d
def v1241 : W := 0x807f0007f00ff804fa007e00bb
def v1242 : W := 0x807f00060f8ff804f05060f0dd
def v1243 : W := 0x807ff806000ff804ff0074009b
def v1244 : W := 0x860301c6038000002010402001
def v1245 : W := 0x860301c0000008409008000000
def v1246 : W := 0x867b01c6038f08c6f0386070d9
def v1247 : W := 0x860301c60f8ff840b05860f0dd
def v1248 : W := 0x8e0000060f8000000000000000
def v1249 : W := 0x887f06060c0ff886f06060c0dd
def v1250 : W := 0x8e0707c60f80f0c2207840f045
def v1251 : W := 0x8e0707c60f8ff000205060f0dd
def v1252 : W := 0x8e0707c60f80f840b05860b015
def v1253 : W := 0x8e07fffe0f80f0002ad6d4a407
def v1254 : W := 0x8e7800060f8f08c6d0282050d8
def v1255 : W := 0x8e7f00060f8ff8c6f0006050d9
def v1256 : W := 0x8e7c06060f8ff8c6c06020d0dc
def v1257 : W := 0x8e7f07c60f8ffed7f0786af2fd
def v1258 : W := 0x8e7f07c6000ff8c6f028600099
def v1259 : W := 0x8e7f07c00000f8c6f07840a08d
def v1260 : W := 0x8e7f07c000000ed7d529000000
def v1261 : W := 0x8e7f07c00f8008c6d07800f044
def v1262 : W := 0x8e7f07c00c0ff8c6d06800c0cc
def v1263 : W := 0x8e7f07c60f80f8c6f07840a005
def v1264 : W := 0x8e7f07c6038008c6f038603011
def v1265 : W := 0x8e7f07c60f8ffcd7f47968f2fd
def v1266 : W := 0x8e7f07c60f8ffec7f5786af0fd
def v1267 : W := 0x8e7fc7fe0f8ff8c6fc7b70f4df
def v1268 : W := 0x8e7f07c7ff8ff8c6fa787ef0ff
def v1269 : W := 0x8e7f07c78ffff8c6f87a78f6ff
def v1270 : W := 0x8e7f07c60f8ffed7f57960f0dd
def v1271 : W := 0x8e7fffc60f8ff8c6ff7874f0df
def v1272 : W := 0x8fff07c60ffff9fef07861fbdd
def v1273 : W := 0x8f8707fe0ff0f12820d6c1ad05
def v1274 : W := 0x8fff07fe0f8ff9fef0fde0f0dd
def v1275 : W := 0x8fff07f8000009fed0ad800000
def v1276 : W := 0xb003380000000a009100000000
def v1277 : W := 0xb000000670000a008000220010
def v1278 : W := 0xb0033806700000002200440001
def v1279 : W := 0xb0033807f00ffa00bb007e00bb
def v1280 : W := 0xb07b3806700f0e05f7006e00b9
def v1281 : W := 0xb6000006738001280000010900
def v1282 : W := 0xb600000000000b688000000000
def v1283 : W := 0xb603380673800b68b300671911
def v1284 : W := 0xb60301c673800b68b018633911
def v1285 : W := 0xb60339c670000b68b38ce60011
def v1286 : W := 0xb60339c603800b68b19ce03011
def v1287 : W := 0xb60339c673800b68b39cc52901
def v1288 : W := 0xb607fffe7380f1282ad6d5ad07
def v1289 : W := 0xbe073fc67f80f12822d4c5a905
def v1290 : W := 0xb67b39c000000fffd5ad800000
def v1291 : W := 0xbe7f07c67f8ffbeef07863f9dd
def v1292 : W := 0xf0000007f00000000000000000
def v1293 : W := 0xbf833ffe7ff0012822d6c5ad05
def v1294 : W := 0xbe7f3fc60f8ffbeef1fce0f0dd
def v1295 : W := 0xbf833ff800000bfa91ad800000
def v1296 : W := 0xbf8000067ff00bfa8000235b50
def v1297 : W := 0xce7fc7c78f8ffcc7fc7878f0ff
def v1298 : W := 0xc9ffc63f8c7ffc97fc6378c6ff
def v1299 : W := 0xc07fc007800ffc05fc007800bb
def v1300 : W := 0xcfffc7f800000cd7d429000000
def v1301 : W := 0xcfff07c78ffffcd7f07868f2fd
def v1302 : W := 0xcffcc63f8ffffcd7cc6338d6fe
def v1303 : W := 0xcfffc7fe0f8ffcd7f47960f0dd
def v1304 : W := 0xcfffc7f98c7ffcd7dc6b18c6ee
def v1305 : W := 0xf007f807f00ff0002a007e00bb
def v1306 : W := 0xf007f807f000fa00bb00760013
def v1307 : W := 0xf007f807f000f6012f005e0023
def v1308 : W := 0xf007fffff000f0002ad6d4a407
def v1309 : W := 0xf07ff8000000fe05ff0054008b
def v1310 : W := 0xf0780007f00f0e05d5002a00b8
def v1311 : W := 0xf07f0007f00ffe05f0006a00b9
def v1312 : W := 0xf07cc007f00ffe05cc003a00ba
def v1313 : W := 0xf07ff80000000ed7d529000000
def v1314 : W := 0xf07ff807f000fe05ff00540003
def v1315 : W := 0xf07ff801f0000e05df001e0022
def v1316 : W := 0xf07ff801800ffe05dd001800aa
def v1317 : W := 0xf07ff80670000e05f700660011
def v1318 : W := 0xf07ff806000ffe05f500600099
def v1319 : W := 0xf07ff807f00ffec7ff287e50fb
def v1320 : W := 0xf07ff807f00ffe97ff217e42fb
def v1321 : W := 0xf07ff807f00ffed7ff007e52fb
def v1322 : W := 0xbe7f3fc000000beed1ac800000
def v1323 : W := 0xf07fffc7f00ffe05ff787ea0bf
def v1324 : W := 0xf07ff807ff8ffe05ff507ef0ff
def v1325 : W := 0xf07ff807fc7ffe05ff427ec6ff
def v1326 : W := 0xf07ffe3ff00ffe05ff637e84bf
def v1327 : W := 0xf187f83ff070f1282a86d50d03
def v1328 : W := 0xf607f9c7f380f1282a94d52903
def v1329 : W := 0xf1fff83ff00fff3dff85fe00bb
def v1330 : W := 0xf1fff83800000f3dd585800000
def v1331 : W := 0xf1fff807f07fff3dff007f0bbb
def v1332 : W := 0xf67ff9c000000f6dd58c800000
def v1333 : W := 0xf67ff807f38fff6dff007f19bb
def v1334 : W := 0xf67ff9c7f00fff6dff8cfe00bb
def v1335 : W := 0xf9fffe398c7ffe97dd6318c6ee
def v1336 : W := 0xf783f9f800000f79958d800000
def v1337 : W := 0xf7800007f3f00f7980002b1b30
def v1338 : W := 0xf87ffe07fc0ffe87ff607ec0ff
def v1339 : W := 0xf783f9fff3f001282a96d52d03
def v1340 : W := 0xf9fff807fc7ffe97ff007e42fb
def v1341 : W := 0xf9fcc63ffc7ffe97cc633ac6fe
def v1342 : W := 0xf9fffe3800000e97d521000000
def v1343 : W := 0xf9fffe3ff00ffe97ff217e00bb
def v1344 : W := 0xfe7f07c7ff8ffec7f0786af0fd
def v1345 : W := 0xfe7ff807ff8ffec7ff007e50fb
def v1346 : W := 0xfe7fffc7f00ffec7ff287e00bb
def v1347 : W := 0xfe7fffc60f8ffec7f57860f0dd
def v1348 : W := 0xff800007fff001fa0000015b40
def v1349 : W := 0xff800007fff00b688000231910
def v1350 : W := 0xff800007fff0073900000b0b20
def v1351 : W := 0xff8339c7fff001282294c52901
def v1352 : W := 0xff80f83ffff001280a86950d02
def v1353 : W := 0xff8007fffff0012800d681ad04
def v1354 : W := 0xfe7fffc000000ec7d528000000
def v1355 : W := 0xfff8000000000fffd529000000
def v1356 : W := 0xfff80007ffff0fffd5002b5bf8
def v1357 : W := 0xfff80007ffff0fffd0282b5bf8
def v1358 : W := 0xfff80007ffff0fffc4212b5bf8
def v1359 : W := 0xfffcc6398c7fffffcc6318c6ee
def v1360 : W := 0xfffc0607ffffffffc0602bdbfc
def v1361 : W := 0xfffcc63800000fffc421000000
def v1362 : W := 0xfffcc007ffffffffcc003b5bfa
def v1363 : W := 0xffff0007fffffffff0006b5bf9
def v1364 : W := 0xffff07c60f8ffffff07860f0dd
def v1365 : W := 0xffff07c000000fffd028000000
def v1366 : W := 0xfffffe3fffffffffff637fdfff
def v1367 : W := 0xffffc7fffffffffffc7b7bffff
def v1368 : W := 0xfffff807f00fffffff007e00bb
def v1369 : W := 0xfffff80000000fffd500000000
def v1370 : W := 0xffffffc7ffffffffff787ffbff
def v1371 : W := 0xfffffff80000fffff5fdc0a08d
def v1372 : W := 0xfffffff80000ffffddef90848e
def v1373 : W := 0xfffffff80000ffffffffd4a407
def v1374 : W := 0xfffffff80000ffffffadd4008b
def v1375 : W := 0xfffffff80ff00fffd5ff81ad04
def v1376 : W := 0xfffffff80c700fffd5ef80c644
def v1377 : W := 0xfffffff80c0fffffd5ed80c0cc
def v1378 : W := 0xfffffff80f800fffd5fd80f044
def v1379 : W := 0xfffffff98c70ffffddef908406
def v1380 : W := 0xfffffff980700fffddaf980622
def v1381 : W := 0xfffffff9800fffffddad9800aa
def v1382 : W := 0xfffffffe70000ffff7ade60011
def v1383 : W := 0xfffffffe03800ffff5bde03011
def v1384 : W := 0xfffffff9f0000fffdfad9e0022
def v1385 : W := 0xfffffffe000ffffff5ade00099
def v1386 : W := 0xfffffff9f0700fffdfaf950d02
def v1387 : W := 0xfffffffe0f80fffff5fdc0a005
def v1388 : W := 0xffffffff8ffffffffdfff8f6ff
def v1389 : W := 0xfffffffe73800ffff7bdc52901
def v1390 : W := 0xfffffffff000ffffffadd40003
def v1391 : W := 0xffffffffff8ffffffffdfef0ff
def v1392 : W := 0xfffffffffc7fffffffeffec6ff
def v1393 : W := 0xffffffffffffffffeef7ffffff
def v1394 : W := 0xfffffffffffffdfffefffdffff
def v1395 : W := 0xffffffffffffffeffffefffdff
def v1396 : W := 0xffffffffffffffbffff7ffefff
def v1397 : W := 0xfffffffffffffffffffff5fddf
def v1398 : W := 0xfffffffffffffffffafeffffff
def v1399 : W := 0xffffffffffffffffffffddefef
def v1400 : W := 0xffffffffffffffffffd6ffffff
def v1401 : W := 0xffffffffffffffffffffffadbf
def v1402 : W := 0xf07ff807f00ffed7ff297e00bb
def v1403 : W := 0x49fcc6398c7ffe97dd633ac6fe

def ins6 : List W := [v0, v1, v2, v3, v4, v5]
theorem nd6 : ins6.Nodup := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem rows6 : ∀ j : Fin 104, Nat.testBit (4269866496 * 2 ^ 32 + 4269834240) (∑ i : Fin 6, if (ins6.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val] := by decide +kernel
def tree_0 : BinaryTree (List W) := .nil
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_0 : everyKey (fun q => !doneTest q) tree_0 = true := by decide +kernel
theorem closed_0 : Closed 0 tree_0 := closed_nil tree_0 ok_tree_0
def tree_1 : BinaryTree (List W) := .nil
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_1 : everyKey (rowOK 0 tree_0) tree_1 = true := by decide +kernel
theorem closed_1 : Closed 1 tree_1 := closed_next 0 (by decide) tree_1 tree_0 closed_0 ok_tree_1
def tree_2 : BinaryTree (List W) := .nil
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_2 : everyKey (rowOK 1 tree_1) tree_2 = true := by decide +kernel
theorem closed_2 : Closed 2 tree_2 := closed_next 1 (by decide) tree_2 tree_1 closed_1 ok_tree_2
def tree_3 : BinaryTree (List W) := (.node [v0,v6,v2,v7] (.node [v8,v9,v2,v10] (.node [v11,v0,v1,v12] (.node [v13,v0,v9,v10] (.node [v13,v8,v1,v10] (.node [v14,v15,v4,v5] .nil .nil) .nil) (.node [v11,v0,v1,v16] (.node [v17,v0,v1,v3] .nil .nil) .nil)) (.node [v18,v1,v2,v10] (.node [v19,v1,v2,v20] (.node [v21,v1,v2,v22] .nil .nil) .nil) (.node [v8,v23,v2,v10] (.node [v24,v1,v2,v10] .nil .nil) .nil))) (.node [v0,v25,v2,v3] (.node [v26,v1,v2,v10] (.node [v8,v1,v2,v10] (.node [v8,v1,v27,v10] .nil .nil) .nil) (.node [v0,v23,v27,v10] (.node [v28,v1,v2,v10] .nil .nil) .nil)) (.node [v0,v29,v3,v16] (.node [v0,v30,v2,v31] (.node [v0,v30,v2,v16] .nil .nil) .nil) (.node [v0,v32,v2,v33] .nil .nil)))) (.node [v0,v1,v27,v10] (.node [v0,v34,v2,v10] (.node [v0,v9,v27,v10] (.node [v0,v35,v2,v10] (.node [v0,v36,v2,v10] .nil .nil) .nil) (.node [v0,v37,v2,v10] (.node [v0,v9,v2,v10] .nil .nil) .nil)) (.node [v0,v1,v38,v10] (.node [v0,v1,v39,v40] (.node [v0,v1,v41,v42] .nil .nil) .nil) (.node [v0,v1,v43,v10] .nil .nil))) (.node [v1,v44,v2,v16] (.node [v9,v45,v2,v10] (.node [v0,v1,v46,v10] (.node [v0,v1,v47,v10] .nil .nil) .nil) (.node [v1,v48,v2,v3] (.node [v1,v45,v27,v10] .nil .nil) .nil)) (.node [v49,v2,v3,v16] (.node [v1,v50,v3,v16] (.node [v1,v44,v2,v51] .nil .nil) .nil) (.node [v52,v3,v4,v5] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_3 : everyKey (rowOK 2 tree_2) tree_3 = true := by decide +kernel
theorem closed_3 : Closed 3 tree_3 := closed_next 2 (by decide) tree_3 tree_2 closed_2 ok_tree_3
def tree_4llll : BinaryTree (List W) := (.node [v53,v54,v0,v1,v2] (.node [v55,v0,v1,v27,v3] (.node [v55,v54,v0,v1,v2] (.node [v56,v0,v1,v2,v10] (.node [v57,v0,v1,v2,v10] .nil .nil) (.node [v58,v0,v1,v2,v10] .nil .nil)) (.node [v55,v0,v9,v2,v3] (.node [v55,v8,v1,v2,v3] .nil .nil) .nil)) (.node [v59,v0,v1,v2,v3] (.node [v60,v0,v1,v2,v3] (.node [v61,v1,v62,v2,v3] .nil .nil) (.node [v63,v0,v64,v2,v3] .nil .nil)) (.node [v65,v0,v1,v2,v3] (.node [v66,v67,v0,v1,v3] .nil .nil) .nil))) (.node [v68,v1,v69,v2,v3] (.node [v68,v0,v70,v2,v3] (.node [v68,v71,v0,v1,v3] (.node [v68,v54,v0,v1,v2] .nil .nil) (.node [v68,v11,v0,v1,v4] .nil .nil)) (.node [v68,v0,v29,v3,v4] (.node [v68,v0,v30,v2,v4] .nil .nil) .nil)) (.node [v72,v1,v44,v2,v4] (.node [v68,v1,v50,v3,v4] (.node [v68,v1,v44,v2,v4] .nil .nil) (.node [v68,v49,v2,v3,v4] .nil .nil)) (.node [v73,v11,v0,v1,v4] (.node [v74,v0,v30,v2,v4] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_4llll : everyKey (rowOK 3 tree_3) tree_4llll = true := by decide +kernel
def tree_4lllr : BinaryTree (List W) := (.node [v75,v49,v2,v3,v4] (.node [v75,v11,v0,v1,v4] (.node [v76,v54,v0,v1,v2] (.node [v77,v0,v78,v2,v3] (.node [v79,v1,v80,v2,v3] .nil .nil) (.node [v81,v82,v0,v1,v3] .nil .nil)) (.node [v75,v71,v0,v1,v3] (.node [v75,v54,v0,v1,v2] .nil .nil) .nil)) (.node [v75,v1,v69,v2,v3] (.node [v75,v0,v30,v2,v4] (.node [v75,v0,v70,v2,v3] .nil .nil) (.node [v75,v0,v29,v3,v4] .nil .nil)) (.node [v75,v1,v50,v3,v4] (.node [v75,v1,v44,v2,v4] .nil .nil) .nil))) (.node [v83,v1,v84,v2,v16] (.node [v85,v0,v30,v2,v5] (.node [v86,v87,v0,v1,v2] (.node [v86,v88,v0,v1,v2] .nil .nil) (.node [v89,v1,v44,v2,v5] .nil .nil)) (.node [v90,v0,v1,v2,v3] (.node [v91,v11,v0,v1,v5] .nil .nil) .nil)) (.node [v92,v0,v93,v2,v31] (.node [v92,v0,v93,v2,v16] (.node [v83,v1,v84,v2,v51] .nil .nil) .nil) (.node [v94,v95,v0,v1,v12] (.node [v94,v95,v0,v1,v16] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_4lllr : everyKey (rowOK 3 tree_3) tree_4lllr = true := by decide +kernel
def tree_4lll : BinaryTree (List W) := .node [v96,v54,v0,v1,v2] tree_4llll tree_4lllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_4lll : everyKey (rowOK 3 tree_3) tree_4lll = true := by
  change (_ && everyKey _ tree_4llll && everyKey _ tree_4lllr) = true
  rw [ok_tree_4llll, ok_tree_4lllr]
  decide +kernel
def tree_4llrl : BinaryTree (List W) := (.node [v97,v54,v0,v1,v2] (.node [v88,v0,v1,v2,v3] (.node [v98,v0,v9,v2,v99] (.node [v100,v0,v1,v2,v16] (.node [v101,v0,v1,v2,v16] .nil .nil) (.node [v98,v8,v1,v2,v99] .nil .nil)) (.node [v88,v0,v1,v2,v10] (.node [v98,v0,v1,v27,v99] .nil .nil) .nil)) (.node [v102,v0,v1,v2,v4] (.node [v103,v0,v1,v2,v4] (.node [v88,v0,v1,v2,v104] .nil .nil) (.node [v102,v105,v0,v1,v2] .nil .nil)) (.node [v14,v3,v4,v5,v106] (.node [v102,v0,v1,v2,v16] .nil .nil) .nil))) (.node [v54,v0,v1,v2,v107] (.node [v54,v0,v23,v2,v5] (.node [v54,v13,v0,v1,v5] (.node [v108,v54,v0,v1,v2] .nil .nil) (.node [v54,v8,v1,v2,v5] .nil .nil)) (.node [v54,v0,v1,v27,v5] (.node [v54,v0,v9,v2,v5] .nil .nil) .nil)) (.node [v54,v0,v1,v2,v109] (.node [v54,v0,v1,v2,v110] (.node [v54,v0,v1,v2,v111] .nil .nil) (.node [v54,v0,v1,v2,v5] .nil .nil)) (.node [v54,v0,v1,v2,v99] (.node [v54,v0,v1,v2,v112] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_4llrl : everyKey (rowOK 3 tree_3) tree_4llrl = true := by decide +kernel
def tree_4llrr : BinaryTree (List W) := (.node [v113,v114,v3,v4,v5] (.node [v115,v2,v15,v4,v5] (.node [v116,v50,v3,v4,v5] (.node [v117,v29,v3,v4,v5] (.node [v118,v0,v1,v2,v3] .nil .nil) (.node [v117,v119,v3,v4,v5] .nil .nil)) (.node [v115,v120,v2,v3,v16] (.node [v116,v121,v3,v4,v5] .nil .nil) .nil)) (.node [v122,v1,v2,v3,v16] (.node [v123,v1,v124,v3,v16] (.node [v115,v125,v3,v4,v5] .nil .nil) (.node [v123,v126,v3,v4,v5] .nil .nil)) (.node [v113,v1,v2,v3,v16] (.node [v113,v29,v3,v4,v5] .nil .nil) .nil))) (.node [v127,v128,v3,v4,v5] (.node [v129,v0,v2,v3,v16] (.node [v130,v131,v3,v4,v5] (.node [v130,v0,v132,v3,v16] .nil .nil) (.node [v133,v0,v2,v3,v16] .nil .nil)) (.node [v129,v134,v3,v4,v5] (.node [v129,v50,v3,v4,v5] .nil .nil) .nil)) (.node [v135,v0,v30,v4,v5] (.node [v136,v1,v44,v4,v5] (.node [v136,v0,v1,v3,v16] .nil .nil) .nil) (.node [v13,v8,v1,v3,v99] (.node [v135,v0,v1,v3,v16] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_4llrr : everyKey (rowOK 3 tree_3) tree_4llrr = true := by decide +kernel
def tree_4llr : BinaryTree (List W) := .node [v54,v1,v45,v2,v5] tree_4llrl tree_4llrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_4llr : everyKey (rowOK 3 tree_3) tree_4llr = true := by
  change (_ && everyKey _ tree_4llrl && everyKey _ tree_4llrr) = true
  rw [ok_tree_4llrl, ok_tree_4llrr]
  decide +kernel
def tree_4ll : BinaryTree (List W) := .node [v137,v0,v1,v2,v16] tree_4lll tree_4llr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_4ll : everyKey (rowOK 3 tree_3) tree_4ll = true := by
  change (_ && everyKey _ tree_4lll && everyKey _ tree_4llr) = true
  rw [ok_tree_4lll, ok_tree_4llr]
  decide +kernel
def tree_4lrll : BinaryTree (List W) := (.node [v71,v0,v1,v3,v138] (.node [v139,v0,v1,v3,v4] (.node [v140,v0,v1,v3,v16] (.node [v13,v0,v1,v3,v16] (.node [v13,v0,v1,v10,v104] .nil .nil) (.node [v141,v0,v1,v3,v16] .nil .nil)) (.node [v139,v0,v1,v142,v3] (.node [v143,v0,v1,v3,v4] .nil .nil) .nil)) (.node [v71,v0,v1,v107,v3] (.node [v71,v144,v0,v1,v3] (.node [v139,v0,v1,v3,v145] .nil .nil) (.node [v71,v0,v1,v146,v3] .nil .nil)) (.node [v71,v0,v1,v3,v147] (.node [v71,v0,v1,v3,v5] .nil .nil) .nil))) (.node [v11,v0,v1,v148,v4] (.node [v11,v0,v149,v4,v5] (.node [v150,v0,v1,v2,v3] (.node [v71,v0,v1,v3,v99] .nil .nil) (.node [v11,v151,v1,v4,v5] .nil .nil)) (.node [v11,v0,v1,v107,v4] (.node [v11,v0,v152,v4,v5] .nil .nil) .nil)) (.node [v11,v0,v1,v4,v153] (.node [v11,v0,v1,v4,v154] (.node [v11,v0,v1,v155,v5] .nil .nil) (.node [v11,v0,v1,v4,v5] .nil .nil)) (.node [v11,v1,v156,v4,v5] (.node [v11,v0,v1,v4,v99] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_4lrll : everyKey (rowOK 3 tree_3) tree_4lrll = true := by decide +kernel
def tree_4lrlr : BinaryTree (List W) := (.node [v157,v1,v3,v4,v5] (.node [v158,v159,v3,v4,v5] (.node [v160,v2,v3,v4,v5] (.node [v161,v49,v3,v4,v5] (.node [v162,v2,v3,v4,v5] .nil .nil) (.node [v161,v120,v3,v4,v5] .nil .nil)) (.node [v158,v1,v15,v4,v5] (.node [v158,v1,v121,v3,v16] .nil .nil) .nil)) (.node [v163,v29,v3,v4,v5] (.node [v164,v165,v3,v4,v5] (.node [v164,v166,v2,v3,v16] .nil .nil) (.node [v167,v1,v2,v3,v16] .nil .nil)) (.node [v163,v168,v3,v4,v5] (.node [v163,v1,v2,v3,v16] .nil .nil) .nil))) (.node [v21,v1,v2,v16,v169] (.node [v21,v1,v2,v107,v170] (.node [v21,v171,v1,v2,v10] (.node [v172,v173,v3,v4,v5] .nil .nil) (.node [v21,v174,v175,v4,v5] .nil .nil)) (.node [v21,v1,v2,v4,v176] (.node [v21,v1,v2,v170,v177] .nil .nil) .nil)) (.node [v178,v1,v2,v3,v179] (.node [v171,v1,v2,v180,v107] (.node [v21,v1,v2,v99,v181] .nil .nil) .nil) (.node [v182,v1,v2,v3,v99] (.node [v183,v1,v184,v2,v3] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_4lrlr : everyKey (rowOK 3 tree_3) tree_4lrlr = true := by decide +kernel
def tree_4lrl : BinaryTree (List W) := .node [v185,v0,v1,v3,v4] tree_4lrll tree_4lrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_4lrl : everyKey (rowOK 3 tree_3) tree_4lrl = true := by
  change (_ && everyKey _ tree_4lrll && everyKey _ tree_4lrlr) = true
  rw [ok_tree_4lrll, ok_tree_4lrlr]
  decide +kernel
def tree_4lrrl : BinaryTree (List W) := (.node [v8,v9,v2,v3,v99] (.node [v186,v32,v187,v4,v5] (.node [v188,v1,v2,v20,v4] (.node [v189,v1,v2,v3,v4] (.node [v190,v1,v2,v3,v5] .nil .nil) (.node [v19,v1,v2,v3,v191] .nil .nil)) (.node [v186,v30,v2,v4,v5] (.node [v18,v1,v2,v3,v99] .nil .nil) .nil)) (.node [v151,v1,v2,v3,v16] (.node [v24,v1,v2,v3,v99] (.node [v186,v1,v2,v3,v16] .nil .nil) (.node [v151,v152,v41,v4,v5] .nil .nil)) (.node [v8,v23,v2,v3,v99] (.node [v8,v0,v1,v2,v10] .nil .nil) .nil))) (.node [v8,v1,v2,v10,v5] (.node [v8,v1,v2,v10] (.node [v8,v1,v2,v192,v107] (.node [v8,v1,v27,v3,v99] .nil .nil) (.node [v8,v1,v2,v192,v110] .nil .nil)) (.node [v8,v1,v2,v10,v4] (.node [v8,v1,v2,v10,v3] .nil .nil) .nil)) (.node [v8,v1,v2,v3,v16] (.node [v8,v1,v2,v10,v104] (.node [v8,v1,v2,v10,v99] .nil .nil) (.node [v8,v1,v2,v3,v112] .nil .nil)) (.node [v193,v1,v2,v3,v16] (.node [v8,v1,v2,v3,v99] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_4lrrl : everyKey (rowOK 3 tree_3) tree_4lrrl = true := by decide +kernel
def tree_4lrrr : BinaryTree (List W) := (.node [v0,v194,v2,v3,v16] (.node [v0,v195,v1,v3,v16] (.node [v196,v1,v2,v3,v16] (.node [v28,v1,v2,v3,v99] (.node [v26,v1,v2,v3,v99] .nil .nil) (.node [v197,v1,v2,v3,v16] .nil .nil)) (.node [v0,v198,v1,v3,v16] (.node [v199,v1,v2,v10,v4] .nil .nil) .nil)) (.node [v0,v23,v2,v10,v104] (.node [v0,v149,v2,v3,v16] (.node [v0,v200,v2,v3,v16] .nil .nil) (.node [v0,v23,v27,v3,v99] .nil .nil)) (.node [v0,v201,v2,v3,v16] (.node [v0,v23,v2,v3,v16] .nil .nil) .nil))) (.node [v0,v70,v2,v107,v3] (.node [v0,v202,v2,v3,v203] (.node [v0,v202,v204,v2,v3] (.node [v0,v205,v2,v3,v4] .nil .nil) (.node [v0,v202,v2,v3,v4] .nil .nil)) (.node [v0,v70,v206,v2,v3] (.node [v0,v70,v207,v2,v3] .nil .nil) .nil)) (.node [v0,v70,v2,v3,v208] (.node [v0,v70,v2,v3,v209] (.node [v0,v70,v2,v3,v5] .nil .nil) .nil) (.node [v0,v210,v1,v2,v3] (.node [v0,v70,v2,v3,v99] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_4lrrr : everyKey (rowOK 3 tree_3) tree_4lrrr = true := by decide +kernel
def tree_4lrr : BinaryTree (List W) := .node [v193,v1,v2,v3,v99] tree_4lrrl tree_4lrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_4lrr : everyKey (rowOK 3 tree_3) tree_4lrr = true := by
  change (_ && everyKey _ tree_4lrrl && everyKey _ tree_4lrrr) = true
  rw [ok_tree_4lrrl, ok_tree_4lrrr]
  decide +kernel
def tree_4lr : BinaryTree (List W) := .node [v211,v1,v2,v3,v99] tree_4lrl tree_4lrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_4lr : everyKey (rowOK 3 tree_3) tree_4lr = true := by
  change (_ && everyKey _ tree_4lrl && everyKey _ tree_4lrr) = true
  rw [ok_tree_4lrl, ok_tree_4lrr]
  decide +kernel
def tree_4l : BinaryTree (List W) := .node [v13,v0,v9,v3,v99] tree_4ll tree_4lr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_4l : everyKey (rowOK 3 tree_3) tree_4l = true := by
  change (_ && everyKey _ tree_4ll && everyKey _ tree_4lr) = true
  rw [ok_tree_4ll, ok_tree_4lr]
  decide +kernel
def tree_4rlll : BinaryTree (List W) := (.node [v0,v212,v15,v4,v5] (.node [v0,v30,v2,v4,v99] (.node [v0,v30,v2,v4,v213] (.node [v0,v30,v2,v214,v4] (.node [v0,v30,v2,v107,v4] .nil .nil) (.node [v0,v30,v2,v215,v5] .nil .nil)) (.node [v0,v30,v2,v4,v216] (.node [v0,v30,v2,v4,v5] .nil .nil) .nil)) (.node [v0,v29,v3,v4,v99] (.node [v0,v29,v107,v3,v4] (.node [v0,v217,v2,v3,v4] .nil .nil) (.node [v0,v29,v3,v4,v5] .nil .nil)) (.node [v0,v212,v119,v3,v16] (.node [v0,v218,v3,v4,v5] .nil .nil) .nil))) (.node [v0,v32,v2,v4,v219] (.node [v0,v32,v220,v2,v10] (.node [v0,v221,v2,v3,v16] (.node [v0,v222,v3,v4,v5] .nil .nil) (.node [v0,v223,v2,v3,v16] .nil .nil)) (.node [v0,v32,v2,v215,v213] (.node [v0,v32,v2,v107,v215] .nil .nil) .nil)) (.node [v0,v224,v2,v3,v203] (.node [v0,v32,v2,v99,v225] (.node [v0,v32,v2,v16,v226] .nil .nil) (.node [v0,v220,v2,v227,v107] .nil .nil)) (.node [v0,v228,v2,v3,v5] (.node [v0,v229,v2,v3,v99] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_4rlll : everyKey (rowOK 3 tree_3) tree_4rlll = true := by decide +kernel
def tree_4rllr : BinaryTree (List W) := (.node [v0,v9,v2,v10,v3] (.node [v0,v35,v2,v3,v99] (.node [v0,v230,v2,v7,v4] (.node [v0,v231,v2,v3,v4] (.node [v0,v232,v2,v3,v99] .nil .nil) (.node [v0,v6,v2,v3,v233] .nil .nil)) (.node [v0,v174,v2,v3,v16] (.node [v0,v36,v2,v3,v99] .nil .nil) .nil)) (.node [v0,v9,v2,v192,v107] (.node [v0,v9,v1,v2,v10] (.node [v0,v152,v2,v3,v16] .nil .nil) (.node [v0,v9,v27,v3,v99] .nil .nil)) (.node [v0,v9,v2,v10] (.node [v0,v9,v2,v192,v110] .nil .nil) .nil))) (.node [v0,v9,v2,v3,v99] (.node [v0,v9,v2,v10,v104] (.node [v0,v9,v2,v10,v5] (.node [v0,v9,v2,v10,v4] .nil .nil) (.node [v0,v9,v2,v10,v99] .nil .nil)) (.node [v0,v9,v2,v3,v16] (.node [v0,v9,v2,v3,v112] .nil .nil) .nil)) (.node [v0,v37,v2,v3,v99] (.node [v0,v234,v2,v3,v99] (.node [v0,v234,v2,v3,v16] .nil .nil) .nil) (.node [v0,v235,v2,v3,v16] (.node [v0,v34,v2,v3,v99] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_4rllr : everyKey (rowOK 3 tree_3) tree_4rllr = true := by decide +kernel
def tree_4rll : BinaryTree (List W) := .node [v0,v236,v2,v3,v4] tree_4rlll tree_4rllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_4rll : everyKey (rowOK 3 tree_3) tree_4rll = true := by
  change (_ && everyKey _ tree_4rlll && everyKey _ tree_4rllr) = true
  rw [ok_tree_4rlll, ok_tree_4rllr]
  decide +kernel
def tree_4rlrl : BinaryTree (List W) := (.node [v0,v1,v237,v3,v4] (.node [v0,v1,v41,v155,v154] (.node [v0,v1,v238,v2,v3] (.node [v0,v1,v239,v3,v16] (.node [v0,v240,v2,v10,v4] .nil .nil) (.node [v0,v1,v241,v3,v16] .nil .nil)) (.node [v0,v1,v41,v107,v155] (.node [v0,v1,v41,v242,v10] .nil .nil) .nil)) (.node [v0,v1,v242,v243,v107] (.node [v0,v1,v41,v16,v244] (.node [v0,v1,v41,v4,v245] .nil .nil) (.node [v0,v1,v41,v99,v246] .nil .nil)) (.node [v0,v1,v247,v3,v5] (.node [v0,v1,v248,v3,v145] .nil .nil) .nil))) (.node [v0,v1,v175,v3,v16] (.node [v0,v1,v39,v3,v249] (.node [v0,v1,v250,v3,v99] (.node [v0,v1,v251,v3,v99] .nil .nil) (.node [v0,v1,v252,v3,v4] .nil .nil)) (.node [v0,v1,v38,v3,v99] (.node [v0,v1,v253,v40,v4] .nil .nil) .nil)) (.node [v0,v1,v27,v192,v107] (.node [v0,v1,v187,v3,v16] (.node [v0,v1,v43,v3,v99] .nil .nil) (.node [v0,v1,v27,v2,v10] .nil .nil)) (.node [v0,v1,v27,v10] (.node [v0,v1,v27,v192,v110] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_4rlrl : everyKey (rowOK 3 tree_3) tree_4rlrl = true := by decide +kernel
def tree_4rlrr : BinaryTree (List W) := (.node [v0,v1,v254,v10,v4] (.node [v0,v1,v27,v3,v99] (.node [v0,v1,v27,v10,v104] (.node [v0,v1,v27,v10,v5] (.node [v0,v1,v27,v10,v4] .nil .nil) (.node [v0,v1,v27,v10,v99] .nil .nil)) (.node [v0,v1,v27,v3,v16] (.node [v0,v1,v27,v3,v112] .nil .nil) .nil)) (.node [v0,v1,v46,v3,v99] (.node [v0,v1,v255,v3,v99] (.node [v0,v1,v255,v3,v16] .nil .nil) (.node [v0,v1,v47,v3,v99] .nil .nil)) (.node [v0,v1,v256,v3,v16] (.node [v0,v1,v257,v3,v16] .nil .nil) .nil))) (.node [v0,v1,v2,v10,v258] (.node [v0,v1,v2,v227,v16] (.node [v0,v1,v2,v259,v4] (.node [v0,v1,v2,v260,v16] .nil .nil) (.node [v0,v1,v2,v180,v16] .nil .nil)) (.node [v0,v1,v2,v10,v261] (.node [v0,v1,v2,v243,v16] .nil .nil) .nil)) (.node [v0,v1,v2,v10,v181] (.node [v0,v1,v2,v10,v262] (.node [v0,v1,v2,v10,v263] .nil .nil) .nil) (.node [v0,v1,v2,v10,v246] (.node [v0,v1,v2,v10,v225] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_4rlrr : everyKey (rowOK 3 tree_3) tree_4rlrr = true := by decide +kernel
def tree_4rlr : BinaryTree (List W) := .node [v0,v1,v27,v10,v3] tree_4rlrl tree_4rlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_4rlr : everyKey (rowOK 3 tree_3) tree_4rlr = true := by
  change (_ && everyKey _ tree_4rlrl && everyKey _ tree_4rlrr) = true
  rw [ok_tree_4rlrl, ok_tree_4rlrr]
  decide +kernel
def tree_4rl : BinaryTree (List W) := .node [v0,v264,v2,v3,v16] tree_4rll tree_4rlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_4rl : everyKey (rowOK 3 tree_3) tree_4rl = true := by
  change (_ && everyKey _ tree_4rll && everyKey _ tree_4rlr) = true
  rw [ok_tree_4rll, ok_tree_4rlr]
  decide +kernel
def tree_4rrll : BinaryTree (List W) := (.node [v0,v1,v2,v3,v16] (.node [v0,v1,v2,v3,v265] (.node [v0,v1,v2,v40,v16] (.node [v0,v1,v2,v20,v16] (.node [v0,v1,v2,v266,v104] .nil .nil) (.node [v0,v1,v2,v7,v16] .nil .nil)) (.node [v0,v1,v2,v3,v267] (.node [v0,v1,v2,v3,v268] .nil .nil) .nil)) (.node [v0,v1,v2,v3,v269] (.node [v0,v1,v2,v3,v270] (.node [v0,v1,v2,v3,v22] .nil .nil) (.node [v0,v1,v2,v3,v33] .nil .nil)) (.node [v0,v1,v2,v3,v271] (.node [v0,v1,v2,v3,v42] .nil .nil) .nil))) (.node [v0,v1,v2,v3,v272] (.node [v0,v1,v2,v3,v273] (.node [v0,v1,v2,v3,v274] (.node [v0,v1,v2,v3,v275] .nil .nil) (.node [v0,v1,v2,v3,v276] .nil .nil)) (.node [v0,v1,v2,v3,v277] (.node [v0,v1,v2,v3,v12] .nil .nil) .nil)) (.node [v0,v1,v2,v3,v278] (.node [v0,v1,v2,v3,v31] (.node [v0,v1,v2,v3,v279] .nil .nil) (.node [v0,v1,v2,v3,v280] .nil .nil)) (.node [v0,v1,v2,v3,v51] (.node [v0,v1,v2,v3,v281] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_4rrll : everyKey (rowOK 3 tree_3) tree_4rrll = true := by decide +kernel
def tree_4rrlr : BinaryTree (List W) := (.node [v0,v282,v3,v4,v5] (.node [v0,v1,v283,v3,v16] (.node [v0,v1,v134,v3,v16] (.node [v0,v1,v2,v284,v16] (.node [v0,v1,v2,v3,v285] .nil .nil) (.node [v0,v1,v286,v3,v16] .nil .nil)) (.node [v0,v1,v287,v3,v16] (.node [v0,v1,v114,v3,v16] .nil .nil) .nil)) (.node [v0,v168,v2,v3,v16] (.node [v0,v288,v2,v3,v16] (.node [v0,v289,v2,v3,v16] .nil .nil) (.node [v0,v290,v3,v4,v5] .nil .nil)) (.node [v0,v2,v291,v3,v16] (.node [v0,v292,v2,v3,v16] .nil .nil) .nil))) (.node [v293,v241,v3,v4,v5] (.node [v294,v124,v3,v4,v5] (.node [v295,v1,v2,v3,v4] (.node [v296,v1,v2,v3,v16] .nil .nil) (.node [v297,v1,v69,v2,v3] .nil .nil)) (.node [v293,v1,v2,v3,v16] (.node [v293,v29,v3,v4,v5] .nil .nil) .nil)) (.node [v195,v49,v3,v4,v5] (.node [v195,v288,v3,v4,v5] (.node [v132,v298,v3,v4,v5] .nil .nil) .nil) (.node [v299,v300,v3,v4,v5] (.node [v200,v44,v2,v4,v5] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_4rrlr : everyKey (rowOK 3 tree_3) tree_4rrlr = true := by decide +kernel
def tree_4rrl : BinaryTree (List W) := .node [v0,v1,v2,v3,v301] tree_4rrll tree_4rrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_4rrl : everyKey (rowOK 3 tree_3) tree_4rrl = true := by
  change (_ && everyKey _ tree_4rrll && everyKey _ tree_4rrlr) = true
  rw [ok_tree_4rrll, ok_tree_4rrlr]
  decide +kernel
def tree_4rrrl : BinaryTree (List W) := (.node [v1,v156,v2,v3,v16] (.node [v302,v212,v3,v4,v5] (.node [v303,v223,v3,v4,v5] (.node [v304,v166,v3,v4,v5] (.node [v305,v1,v3,v4,v5] .nil .nil) (.node [v303,v29,v3,v4,v5] .nil .nil)) (.node [v29,v302,v3,v4,v5] (.node [v303,v1,v2,v3,v16] .nil .nil) .nil)) (.node [v1,v184,v2,v3,v4] (.node [v174,v44,v2,v4,v5] (.node [v223,v50,v3,v4,v5] .nil .nil) (.node [v9,v45,v2,v3,v99] .nil .nil)) (.node [v1,v306,v2,v3,v16] (.node [v1,v184,v2,v3,v179] .nil .nil) .nil))) (.node [v1,v69,v307,v2,v3] (.node [v1,v308,v2,v3,v16] (.node [v1,v45,v2,v10,v104] (.node [v1,v45,v27,v3,v99] .nil .nil) (.node [v1,v45,v2,v3,v16] .nil .nil)) (.node [v1,v309,v2,v3,v4] (.node [v1,v310,v2,v3,v16] .nil .nil) .nil)) (.node [v1,v69,v2,v3,v311] (.node [v1,v69,v2,v3,v5] (.node [v1,v69,v2,v107,v3] .nil .nil) (.node [v1,v69,v2,v3,v312] .nil .nil)) (.node [v1,v313,v2,v3,v4] (.node [v1,v69,v2,v3,v99] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_4rrrl : everyKey (rowOK 3 tree_3) tree_4rrrl = true := by decide +kernel
def tree_4rrrr : BinaryTree (List W) := (.node [v1,v314,v3,v4,v5] (.node [v1,v44,v2,v4,v99] (.node [v1,v44,v2,v4,v177] (.node [v1,v44,v2,v315,v4] (.node [v1,v44,v2,v107,v4] .nil .nil) (.node [v1,v44,v2,v170,v5] .nil .nil)) (.node [v1,v44,v2,v4,v316] (.node [v1,v44,v2,v4,v5] .nil .nil) .nil)) (.node [v1,v317,v3,v4,v5] (.node [v1,v50,v3,v4,v5] (.node [v1,v50,v107,v3,v4] .nil .nil) (.node [v1,v50,v3,v4,v99] .nil .nil)) (.node [v1,v2,v318,v3,v16] (.node [v1,v319,v2,v3,v16] .nil .nil) .nil))) (.node [v49,v2,v3,v4,v99] (.node [v50,v159,v3,v4,v5] (.node [v241,v49,v3,v4,v5] (.node [v288,v50,v3,v4,v5] .nil .nil) (.node [v50,v168,v3,v4,v5] .nil .nil)) (.node [v49,v2,v3,v4,v5] (.node [v49,v2,v107,v3,v4] .nil .nil) .nil)) (.node [v49,v125,v3,v4,v5] (.node [v49,v114,v3,v4,v5] (.node [v49,v134,v3,v4,v5] .nil .nil) .nil) (.node [v2,v320,v3,v4,v5] (.node [v321,v2,v3,v4,v5] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_4rrrr : everyKey (rowOK 3 tree_3) tree_4rrrr = true := by decide +kernel
def tree_4rrr : BinaryTree (List W) := .node [v1,v44,v175,v4,v5] tree_4rrrl tree_4rrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_4rrr : everyKey (rowOK 3 tree_3) tree_4rrr = true := by
  change (_ && everyKey _ tree_4rrrl && everyKey _ tree_4rrrr) = true
  rw [ok_tree_4rrrl, ok_tree_4rrrr]
  decide +kernel
def tree_4rr : BinaryTree (List W) := .node [v30,v306,v2,v4,v5] tree_4rrl tree_4rrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_4rr : everyKey (rowOK 3 tree_3) tree_4rr = true := by
  change (_ && everyKey _ tree_4rrl && everyKey _ tree_4rrr) = true
  rw [ok_tree_4rrl, ok_tree_4rrr]
  decide +kernel
def tree_4r : BinaryTree (List W) := .node [v0,v1,v2,v10,v104] tree_4rl tree_4rr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_4r : everyKey (rowOK 3 tree_3) tree_4r = true := by
  change (_ && everyKey _ tree_4rl && everyKey _ tree_4rr) = true
  rw [ok_tree_4rl, ok_tree_4rr]
  decide +kernel
def tree_4 : BinaryTree (List W) := .node [v0,v30,v187,v4,v5] tree_4l tree_4r
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_4 : everyKey (rowOK 3 tree_3) tree_4 = true := by
  change (_ && everyKey _ tree_4l && everyKey _ tree_4r) = true
  rw [ok_tree_4l, ok_tree_4r]
  decide +kernel
theorem closed_4 : Closed 4 tree_4 := closed_next 3 (by decide) tree_4 tree_3 closed_3 ok_tree_4
def tree_5llllll : BinaryTree (List W) := (.node [v55,v98,v0,v1,v2,v4] (.node [v322,v1,v323,v2,v3,v4] (.node [v58,v0,v1,v2,v3,v99] (.node [v57,v0,v1,v2,v3,v99] (.node [v324,v0,v1,v2,v3,v16] .nil .nil) (.node [v56,v0,v1,v2,v3,v99] .nil .nil)) (.node [v325,v0,v1,v2,v3,v16] (.node [v325,v0,v1,v2,v260,v4] .nil .nil) (.node [v325,v0,v1,v2,v3,v99] .nil .nil))) (.node [v55,v77,v0,v1,v2,v3] (.node [v326,v327,v0,v1,v3,v4] (.node [v328,v0,v329,v2,v3,v4] .nil .nil) (.node [v55,v79,v0,v1,v2,v3] .nil .nil)) (.node [v55,v86,v330,v0,v1,v2] (.node [v55,v81,v0,v1,v2,v3] .nil .nil) (.node [v55,v330,v0,v1,v2,v3] .nil .nil)))) (.node [v55,v0,v1,v2,v3,v16] (.node [v55,v0,v1,v2,v10,v4] (.node [v55,v0,v220,v1,v2,v3] (.node [v55,v171,v0,v1,v2,v3] .nil .nil) (.node [v55,v0,v1,v242,v2,v3] .nil .nil)) (.node [v55,v0,v1,v2,v3,v4] (.node [v55,v0,v1,v2,v3,v331] .nil .nil) (.node [v55,v0,v1,v2,v3,v261] .nil .nil))) (.node [v332,v91,v0,v1,v2,v3] (.node [v332,v89,v0,v1,v2,v3] (.node [v55,v0,v1,v2,v3,v104] .nil .nil) (.node [v332,v85,v0,v1,v2,v3] .nil .nil)) (.node [v61,v0,v1,v2,v3,v16] (.node [v332,v0,v1,v2,v3,v4] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5llllll : everyKey (rowOK 4 tree_4) tree_5llllll = true := by decide +kernel
def tree_5lllllr : BinaryTree (List W) := (.node [v333,v0,v334,v2,v3,v4] (.node [v335,v0,v1,v2,v3,v16] (.node [v336,v337,v1,v2,v3,v4] (.node [v338,v0,v1,v339,v3,v4] (.node [v66,v0,v1,v2,v3,v16] .nil .nil) (.node [v340,v0,v1,v2,v3,v4] .nil .nil)) (.node [v335,v183,v1,v341,v2,v3] (.node [v342,v0,v1,v2,v3,v4] .nil .nil) (.node [v335,v0,v1,v2,v3,v179] .nil .nil))) (.node [v335,v1,v184,v2,v3,v4] (.node [v335,v1,v341,v2,v3,v4] (.node [v335,v337,v1,v2,v3,v4] .nil .nil) (.node [v335,v1,v341,v2,v3,v179] .nil .nil)) (.node [v343,v0,v1,v2,v3,v4] (.node [v335,v1,v323,v2,v3,v4] .nil .nil) .nil))) (.node [v344,v0,v202,v2,v3,v4] (.node [v344,v0,v345,v204,v2,v3] (.node [v346,v0,v347,v2,v3,v4] (.node [v348,v0,v1,v2,v3,v4] .nil .nil) (.node [v349,v0,v1,v2,v3,v4] .nil .nil)) (.node [v344,v0,v345,v2,v3,v203] (.node [v344,v0,v345,v2,v3,v4] .nil .nil) (.node [v344,v0,v329,v2,v3,v4] .nil .nil))) (.node [v350,v0,v1,v2,v3,v4] (.node [v344,v0,v1,v2,v3,v16] (.node [v344,v0,v1,v2,v3,v203] .nil .nil) (.node [v344,v0,v347,v2,v3,v4] .nil .nil)) (.node [v351,v0,v1,v2,v3,v4] (.node [v352,v353,v1,v2,v3,v4] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5lllllr : everyKey (rowOK 4 tree_4) tree_5lllllr = true := by decide +kernel
def tree_5lllll : BinaryTree (List W) := .node [v63,v0,v1,v2,v3,v16] tree_5llllll tree_5lllllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5lllll : everyKey (rowOK 4 tree_4) tree_5lllll = true := by
  change (_ && everyKey _ tree_5llllll && everyKey _ tree_5lllllr) = true
  rw [ok_tree_5llllll, ok_tree_5lllllr]
  decide +kernel
def tree_5llllrl : BinaryTree (List W) := (.node [v68,v81,v354,v0,v1,v3] (.node [v355,v0,v1,v2,v3,v16] (.node [v355,v356,v0,v1,v3,v145] (.node [v355,v356,v0,v1,v142,v3] (.node [v357,v0,v1,v2,v3,v4] .nil .nil) (.node [v355,v356,v0,v1,v3,v4] .nil .nil)) (.node [v355,v139,v0,v1,v3,v4] (.node [v355,v327,v0,v1,v3,v4] .nil .nil) (.node [v355,v0,v1,v2,v3,v145] .nil .nil))) (.node [v68,v79,v1,v358,v2,v3] (.node [v359,v0,v1,v2,v3,v4] (.node [v355,v0,v1,v360,v3,v4] .nil .nil) (.node [v361,v0,v1,v2,v3,v261] .nil .nil)) (.node [v68,v77,v0,v362,v2,v3] (.node [v68,v363,v0,v1,v2,v3] .nil .nil) (.node [v68,v364,v0,v1,v2,v3] .nil .nil)))) (.node [v68,v92,v0,v93,v2,v4] (.node [v68,v85,v0,v1,v2,v3] (.node [v68,v86,v330,v0,v1,v2] (.node [v68,v365,v0,v1,v2,v3] .nil .nil) (.node [v68,v89,v0,v1,v2,v3] .nil .nil)) (.node [v68,v366,v0,v1,v2,v4] (.node [v68,v91,v0,v1,v2,v3] .nil .nil) (.node [v68,v83,v1,v84,v2,v4] .nil .nil))) (.node [v68,v367,v0,v1,v2,v4] (.node [v68,v368,v0,v1,v2,v4] (.node [v68,v94,v95,v0,v1,v4] .nil .nil) (.node [v68,v369,v0,v1,v2,v4] .nil .nil)) (.node [v68,v102,v0,v1,v2,v4] (.node [v68,v98,v0,v1,v2,v4] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5llllrl : everyKey (rowOK 4 tree_4) tree_5llllrl = true := by decide +kernel
def tree_5llllrr : BinaryTree (List W) := (.node [v68,v370,v0,v1,v2,v3] (.node [v68,v135,v0,v1,v3,v4] (.node [v68,v113,v1,v2,v3,v4] (.node [v68,v115,v120,v2,v3,v4] (.node [v68,v105,v0,v1,v2,v3] .nil .nil) (.node [v68,v123,v1,v124,v3,v4] .nil .nil)) (.node [v68,v129,v0,v2,v3,v4] (.node [v68,v130,v0,v132,v3,v4] .nil .nil) (.node [v68,v136,v0,v1,v3,v4] .nil .nil))) (.node [v68,v163,v1,v2,v3,v4] (.node [v68,v158,v1,v121,v3,v4] (.node [v68,v13,v0,v1,v3,v4] .nil .nil) (.node [v68,v164,v166,v2,v3,v4] .nil .nil)) (.node [v68,v171,v1,v2,v3,v371] (.node [v68,v21,v1,v2,v4,v169] .nil .nil) .nil))) (.node [v68,v0,v23,v2,v3,v4] (.node [v68,v8,v1,v2,v3,v4] (.node [v68,v186,v1,v2,v3,v4] (.node [v68,v183,v0,v1,v2,v3] .nil .nil) (.node [v68,v151,v1,v2,v3,v4] .nil .nil)) (.node [v68,v0,v200,v2,v3,v4] (.node [v68,v0,v195,v1,v3,v4] .nil .nil) (.node [v68,v0,v149,v2,v3,v4] .nil .nil))) (.node [v68,v0,v220,v2,v3,v372] (.node [v68,v0,v223,v2,v3,v4] (.node [v68,v0,v212,v119,v3,v4] .nil .nil) (.node [v68,v0,v32,v2,v4,v226] .nil .nil)) (.node [v68,v0,v204,v1,v2,v3] (.node [v68,v0,v373,v1,v2,v3] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5llllrr : everyKey (rowOK 4 tree_4) tree_5llllrr = true := by decide +kernel
def tree_5llllr : BinaryTree (List W) := .node [v68,v105,v0,v1,v2,v107] tree_5llllrl tree_5llllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5llllr : everyKey (rowOK 4 tree_4) tree_5llllr = true := by
  change (_ && everyKey _ tree_5llllrl && everyKey _ tree_5llllrr) = true
  rw [ok_tree_5llllrl, ok_tree_5llllrr]
  decide +kernel
def tree_5llll : BinaryTree (List W) := .node [v374,v0,v1,v360,v3,v4] tree_5lllll tree_5llllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5llll : everyKey (rowOK 4 tree_4) tree_5llll = true := by
  change (_ && everyKey _ tree_5lllll && everyKey _ tree_5llllr) = true
  rw [ok_tree_5lllll, ok_tree_5llllr]
  decide +kernel
def tree_5lllrll : BinaryTree (List W) := (.node [v68,v0,v1,v2,v375,v4] (.node [v68,v0,v1,v175,v3,v4] (.node [v68,v0,v1,v41,v4,v244] (.node [v68,v0,v9,v2,v3,v4] (.node [v68,v0,v152,v2,v3,v4] .nil .nil) (.node [v68,v0,v1,v241,v3,v4] .nil .nil)) (.node [v68,v0,v1,v376,v2,v3] (.node [v68,v0,v1,v242,v3,v377] .nil .nil) (.node [v68,v0,v1,v142,v2,v3] .nil .nil))) (.node [v68,v0,v1,v2,v107,v4] (.node [v68,v0,v1,v27,v3,v4] (.node [v68,v0,v1,v187,v3,v4] .nil .nil) (.node [v68,v0,v1,v2,v192,v104] .nil .nil)) (.node [v68,v0,v1,v2,v378,v4] (.node [v68,v0,v1,v2,v107,v16] .nil .nil) (.node [v68,v0,v1,v2,v379,v4] .nil .nil)))) (.node [v68,v0,v1,v2,v3,v155] (.node [v68,v0,v1,v2,v380,v4] (.node [v68,v0,v1,v2,v381,v4] (.node [v68,v0,v1,v2,v382,v4] .nil .nil) (.node [v68,v0,v1,v2,v383,v4] .nil .nil)) (.node [v68,v0,v1,v2,v3,v170] (.node [v68,v0,v1,v2,v10,v4] .nil .nil) (.node [v68,v0,v1,v2,v3,v215] .nil .nil))) (.node [v68,v0,v1,v2,v3,v179] (.node [v68,v0,v1,v2,v3,v145] (.node [v68,v0,v1,v2,v3,v4] .nil .nil) (.node [v68,v0,v1,v2,v3,v203] .nil .nil)) (.node [v68,v0,v1,v2,v384,v4] (.node [v68,v0,v1,v2,v3,v16] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5lllrll : everyKey (rowOK 4 tree_4) tree_5lllrll = true := by decide +kernel
def tree_5lllrlr : BinaryTree (List W) := (.node [v385,v0,v1,v2,v3,v4] (.node [v68,v303,v1,v2,v3,v4] (.node [v68,v0,v1,v114,v3,v4] (.node [v68,v0,v1,v2,v386,v4] (.node [v68,v0,v1,v2,v387,v4] .nil .nil) (.node [v68,v0,v1,v134,v3,v4] .nil .nil)) (.node [v68,v0,v168,v2,v3,v4] (.node [v68,v0,v288,v2,v3,v4] .nil .nil) (.node [v68,v293,v1,v2,v3,v4] .nil .nil))) (.node [v388,v0,v1,v2,v3,v4] (.node [v68,v1,v156,v2,v3,v4] (.node [v68,v1,v306,v2,v3,v4] .nil .nil) (.node [v68,v1,v45,v2,v3,v4] .nil .nil)) (.node [v389,v0,v1,v2,v3,v4] (.node [v390,v0,v1,v2,v3,v4] .nil .nil) .nil))) (.node [v391,v90,v0,v1,v2,v3] (.node [v392,v0,v1,v2,v3,v4] (.node [v393,v0,v1,v2,v3,v4] (.node [v394,v0,v1,v2,v3,v4] .nil .nil) (.node [v395,v0,v1,v2,v3,v4] .nil .nil)) (.node [v396,v0,v1,v2,v3,v4] (.node [v397,v0,v1,v2,v3,v4] .nil .nil) (.node [v391,v75,v0,v1,v2,v3] .nil .nil))) (.node [v391,v0,v9,v2,v3,v5] (.node [v391,v8,v1,v2,v3,v5] (.node [v391,v144,v0,v1,v2,v3] .nil .nil) (.node [v391,v0,v207,v1,v2,v3] .nil .nil)) (.node [v391,v0,v1,v27,v3,v5] (.node [v391,v0,v1,v307,v2,v3] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5lllrlr : everyKey (rowOK 4 tree_4) tree_5lllrlr = true := by decide +kernel
def tree_5lllrl : BinaryTree (List W) := .node [v68,v0,v1,v2,v398,v4] tree_5lllrll tree_5lllrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5lllrl : everyKey (rowOK 4 tree_4) tree_5lllrl = true := by
  change (_ && everyKey _ tree_5lllrll && everyKey _ tree_5lllrlr) = true
  rw [ok_tree_5lllrll, ok_tree_5lllrlr]
  decide +kernel
def tree_5lllrrl : BinaryTree (List W) := (.node [v399,v0,v1,v2,v3,v4] (.node [v72,v136,v0,v1,v3,v4] (.node [v400,v0,v1,v2,v3,v4] (.node [v391,v0,v1,v2,v3,v110] (.node [v391,v0,v1,v2,v3,v261] .nil .nil) (.node [v391,v0,v1,v2,v3,v16] .nil .nil)) (.node [v401,v0,v1,v2,v3,v4] (.node [v402,v0,v1,v2,v3,v4] .nil .nil) (.node [v72,v89,v0,v1,v2,v3] .nil .nil))) (.node [v72,v0,v1,v175,v3,v4] (.node [v72,v0,v200,v2,v3,v4] (.node [v72,v21,v1,v2,v4,v169] .nil .nil) (.node [v72,v0,v174,v2,v3,v4] .nil .nil)) (.node [v72,v0,v1,v2,v3,v4] (.node [v72,v0,v1,v2,v3,v170] .nil .nil) .nil))) (.node [v74,v0,v1,v2,v3,v4] (.node [v74,v186,v1,v2,v3,v4] (.node [v74,v85,v0,v1,v2,v3] (.node [v403,v0,v1,v2,v3,v4] .nil .nil) (.node [v74,v135,v0,v1,v3,v4] .nil .nil)) (.node [v74,v0,v1,v187,v3,v4] (.node [v74,v0,v32,v2,v4,v226] .nil .nil) (.node [v74,v0,v1,v2,v3,v215] .nil .nil))) (.node [v404,v0,v1,v2,v3,v4] (.node [v405,v0,v1,v2,v3,v4] (.node [v74,v1,v306,v2,v3,v4] .nil .nil) (.node [v406,v0,v1,v2,v3,v4] .nil .nil)) (.node [v73,v151,v1,v2,v3,v4] (.node [v73,v91,v0,v1,v2,v3] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5lllrrl : everyKey (rowOK 4 tree_4) tree_5lllrrl = true := by decide +kernel
def tree_5lllrrr : BinaryTree (List W) := (.node [v96,v1,v45,v2,v3,v4] (.node [v96,v13,v0,v1,v3,v4] (.node [v73,v0,v1,v2,v3,v4] (.node [v73,v0,v1,v41,v4,v244] (.node [v73,v0,v152,v2,v3,v4] .nil .nil) (.node [v73,v0,v1,v2,v3,v155] .nil .nil)) (.node [v407,v0,v1,v2,v3,v4] (.node [v73,v1,v156,v2,v3,v4] .nil .nil) (.node [v408,v0,v1,v2,v3,v4] .nil .nil))) (.node [v96,v0,v1,v27,v3,v4] (.node [v96,v0,v23,v2,v3,v4] (.node [v96,v8,v1,v2,v3,v4] .nil .nil) (.node [v96,v0,v9,v2,v3,v4] .nil .nil)) (.node [v96,v0,v1,v2,v3,v4] (.node [v96,v0,v1,v2,v192,v104] .nil .nil) .nil))) (.node [v409,v0,v1,v2,v3,v99] (.node [v410,v0,v224,v2,v3,v4] (.node [v411,v0,v1,v248,v3,v4] (.node [v412,v0,v1,v2,v3,v4] .nil .nil) (.node [v413,v0,v1,v242,v3,v5] .nil .nil)) (.node [v414,v178,v1,v2,v3,v4] (.node [v415,v0,v220,v2,v3,v5] .nil .nil) (.node [v416,v171,v1,v2,v3,v5] .nil .nil))) (.node [v417,v418,v1,v2,v3,v4] (.node [v417,v0,v1,v2,v3,v179] (.node [v419,v0,v1,v2,v3,v99] .nil .nil) (.node [v417,v0,v1,v2,v3,v99] .nil .nil)) (.node [v79,v171,v1,v2,v3,v99] (.node [v79,v75,v1,v358,v2,v3] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5lllrrr : everyKey (rowOK 4 tree_4) tree_5lllrrr = true := by decide +kernel
def tree_5lllrr : BinaryTree (List W) := .node [v73,v0,v149,v2,v3,v4] tree_5lllrrl tree_5lllrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5lllrr : everyKey (rowOK 4 tree_4) tree_5lllrr = true := by
  change (_ && everyKey _ tree_5lllrrl && everyKey _ tree_5lllrrr) = true
  rw [ok_tree_5lllrrl, ok_tree_5lllrrr]
  decide +kernel
def tree_5lllr : BinaryTree (List W) := .node [v391,v0,v1,v2,v111,v3] tree_5lllrl tree_5lllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5lllr : everyKey (rowOK 4 tree_4) tree_5lllr = true := by
  change (_ && everyKey _ tree_5lllrl && everyKey _ tree_5lllrr) = true
  rw [ok_tree_5lllrl, ok_tree_5lllrr]
  decide +kernel
def tree_5lll : BinaryTree (List W) := .node [v68,v0,v174,v2,v3,v4] tree_5llll tree_5lllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5lll : everyKey (rowOK 4 tree_4) tree_5lll = true := by
  change (_ && everyKey _ tree_5llll && everyKey _ tree_5lllr) = true
  rw [ok_tree_5llll, ok_tree_5lllr]
  decide +kernel
def tree_5llrlll : BinaryTree (List W) := (.node [v420,v0,v1,v2,v3,v99] (.node [v79,v1,v358,v2,v107,v3] (.node [v79,v0,v1,v2,v3,v16] (.node [v79,v0,v1,v2,v3,v311] (.node [v79,v0,v1,v2,v10,v3] .nil .nil) (.node [v79,v0,v1,v2,v3,v112] .nil .nil)) (.node [v79,v297,v1,v358,v2,v3] (.node [v79,v0,v1,v2,v3,v99] .nil .nil) (.node [v79,v421,v1,v2,v3,v5] .nil .nil))) (.node [v79,v1,v323,v2,v3,v5] (.node [v79,v1,v358,v2,v3,v311] (.node [v79,v1,v358,v2,v3,v5] .nil .nil) (.node [v79,v1,v358,v2,v3,v99] .nil .nil)) (.node [v79,v1,v69,v2,v3,v5] (.node [v79,v1,v323,v2,v3,v99] .nil .nil) (.node [v363,v0,v1,v2,v3,v5] .nil .nil)))) (.node [v77,v0,v362,v2,v3,v5] (.node [v422,v0,v423,v2,v3,v4] (.node [v422,v0,v1,v2,v3,v203] (.node [v424,v0,v1,v2,v3,v99] .nil .nil) (.node [v422,v0,v1,v2,v3,v99] .nil .nil)) (.node [v77,v0,v362,v206,v2,v3] (.node [v77,v75,v0,v362,v2,v3] .nil .nil) (.node [v77,v0,v362,v2,v107,v3] .nil .nil))) (.node [v77,v0,v329,v2,v3,v99] (.node [v77,v0,v362,v2,v3,v99] (.node [v77,v0,v362,v2,v3,v209] .nil .nil) (.node [v77,v0,v329,v2,v3,v5] .nil .nil)) (.node [v77,v0,v220,v2,v3,v99] (.node [v77,v0,v70,v2,v3,v5] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5llrlll : everyKey (rowOK 4 tree_4) tree_5llrlll = true := by decide +kernel
def tree_5llrllr : BinaryTree (List W) := (.node [v81,v354,v0,v1,v107,v3] (.node [v425,v0,v1,v2,v3,v99] (.node [v77,v0,v1,v2,v3,v16] (.node [v77,v0,v1,v2,v3,v209] (.node [v77,v0,v1,v2,v10,v3] .nil .nil) (.node [v77,v0,v1,v2,v3,v112] .nil .nil)) (.node [v77,v0,v426,v2,v3,v5] (.node [v77,v0,v1,v2,v3,v99] .nil .nil) (.node [v364,v0,v1,v2,v3,v5] .nil .nil))) (.node [v427,v0,v1,v428,v3,v4] (.node [v427,v0,v1,v2,v3,v145] (.node [v429,v0,v1,v2,v3,v99] .nil .nil) (.node [v427,v0,v1,v2,v3,v99] .nil .nil)) (.node [v81,v354,v0,v1,v146,v3] (.node [v81,v75,v354,v0,v1,v3] .nil .nil) .nil))) (.node [v81,v0,v1,v253,v3,v99] (.node [v81,v327,v0,v1,v3,v5] (.node [v81,v354,v0,v1,v3,v147] (.node [v81,v354,v0,v1,v3,v5] .nil .nil) (.node [v81,v354,v0,v1,v3,v99] .nil .nil)) (.node [v81,v71,v0,v1,v3,v5] (.node [v81,v327,v0,v1,v3,v99] .nil .nil) (.node [v81,v0,v1,v242,v3,v99] .nil .nil))) (.node [v81,v0,v1,v2,v3,v16] (.node [v81,v0,v1,v2,v3,v147] (.node [v81,v0,v1,v2,v10,v3] .nil .nil) (.node [v81,v0,v1,v2,v3,v112] .nil .nil)) (.node [v81,v0,v1,v430,v3,v5] (.node [v81,v0,v1,v2,v3,v99] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5llrllr : everyKey (rowOK 4 tree_4) tree_5llrllr = true := by decide +kernel
def tree_5llrll : BinaryTree (List W) := .node [v77,v0,v230,v2,v3,v99] tree_5llrlll tree_5llrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5llrll : everyKey (rowOK 4 tree_4) tree_5llrll = true := by
  change (_ && everyKey _ tree_5llrlll && everyKey _ tree_5llrllr) = true
  rw [ok_tree_5llrlll, ok_tree_5llrllr]
  decide +kernel
def tree_5llrlrl : BinaryTree (List W) := (.node [v431,v0,v1,v2,v3,v4] (.node [v76,v0,v1,v2,v3,v16] (.node [v76,v86,v330,v0,v1,v2] (.node [v432,v0,v1,v2,v3,v99] (.node [v433,v0,v1,v2,v3,v99] .nil .nil) (.node [v434,v0,v1,v2,v3,v99] .nil .nil)) (.node [v76,v0,v1,v2,v260,v4] (.node [v76,v105,v0,v1,v2,v3] .nil .nil) (.node [v76,v0,v1,v2,v3,v4] .nil .nil))) (.node [v435,v0,v1,v2,v3,v4] (.node [v436,v0,v1,v2,v3,v4] (.node [v76,v0,v1,v2,v284,v4] .nil .nil) (.node [v437,v0,v1,v2,v3,v4] .nil .nil)) (.node [v438,v0,v1,v2,v3,v4] (.node [v438,v89,v0,v1,v2,v3] .nil .nil) (.node [v431,v85,v0,v1,v2,v3] .nil .nil)))) (.node [v75,v83,v1,v84,v2,v4] (.node [v75,v89,v0,v1,v2,v3] (.node [v439,v0,v1,v2,v3,v4] (.node [v439,v91,v0,v1,v2,v3] .nil .nil) (.node [v75,v86,v330,v0,v1,v2] .nil .nil)) (.node [v75,v91,v0,v1,v2,v3] (.node [v75,v85,v0,v1,v2,v3] .nil .nil) (.node [v75,v90,v0,v1,v2,v3] .nil .nil))) (.node [v75,v115,v120,v2,v3,v4] (.node [v75,v94,v95,v0,v1,v4] (.node [v75,v92,v0,v93,v2,v4] .nil .nil) (.node [v75,v105,v0,v1,v2,v3] .nil .nil)) (.node [v75,v113,v1,v2,v3,v4] (.node [v75,v123,v1,v124,v3,v4] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5llrlrl : everyKey (rowOK 4 tree_4) tree_5llrlrl = true := by decide +kernel
def tree_5llrlrr : BinaryTree (List W) := (.node [v75,v151,v1,v2,v3,v4] (.node [v75,v163,v1,v2,v3,v4] (.node [v75,v135,v0,v1,v3,v4] (.node [v75,v440,v0,v1,v2,v3] (.node [v75,v129,v0,v2,v3,v4] .nil .nil) (.node [v75,v136,v0,v1,v3,v4] .nil .nil)) (.node [v75,v158,v1,v121,v3,v4] (.node [v75,v13,v0,v1,v3,v4] .nil .nil) (.node [v75,v164,v166,v2,v3,v4] .nil .nil))) (.node [v75,v182,v1,v2,v3,v4] (.node [v75,v171,v1,v2,v3,v371] (.node [v75,v21,v1,v2,v4,v169] .nil .nil) (.node [v75,v183,v0,v1,v2,v3] .nil .nil)) (.node [v75,v186,v1,v2,v3,v4] (.node [v75,v211,v1,v2,v3,v4] .nil .nil) .nil))) (.node [v75,v0,v212,v119,v3,v4] (.node [v75,v0,v441,v1,v2,v3] (.node [v75,v193,v1,v2,v3,v4] (.node [v75,v8,v1,v2,v3,v4] .nil .nil) (.node [v75,v0,v195,v1,v3,v4] .nil .nil)) (.node [v75,v0,v149,v2,v3,v4] (.node [v75,v0,v200,v2,v3,v4] .nil .nil) (.node [v75,v0,v23,v2,v3,v4] .nil .nil))) (.node [v75,v0,v204,v1,v2,v3] (.node [v75,v0,v32,v2,v4,v226] (.node [v75,v0,v223,v2,v3,v4] .nil .nil) (.node [v75,v0,v220,v2,v3,v372] .nil .nil)) (.node [v75,v0,v232,v2,v3,v4] (.node [v75,v0,v229,v2,v3,v4] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5llrlrr : everyKey (rowOK 4 tree_4) tree_5llrlrr = true := by decide +kernel
def tree_5llrlr : BinaryTree (List W) := .node [v75,v130,v0,v132,v3,v4] tree_5llrlrl tree_5llrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5llrlr : everyKey (rowOK 4 tree_4) tree_5llrlr = true := by
  change (_ && everyKey _ tree_5llrlrl && everyKey _ tree_5llrlrr) = true
  rw [ok_tree_5llrlrl, ok_tree_5llrlrr]
  decide +kernel
def tree_5llrl : BinaryTree (List W) := .node [v365,v0,v1,v2,v3,v5] tree_5llrll tree_5llrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5llrl : everyKey (rowOK 4 tree_4) tree_5llrl = true := by
  change (_ && everyKey _ tree_5llrll && everyKey _ tree_5llrlr) = true
  rw [ok_tree_5llrll, ok_tree_5llrlr]
  decide +kernel
def tree_5llrrll : BinaryTree (List W) := (.node [v75,v0,v1,v2,v442,v3] (.node [v75,v0,v1,v142,v2,v3] (.node [v75,v0,v1,v241,v3,v4] (.node [v75,v0,v9,v2,v3,v4] (.node [v75,v0,v152,v2,v3,v4] .nil .nil) (.node [v75,v0,v234,v2,v3,v4] .nil .nil)) (.node [v75,v0,v1,v41,v4,v244] (.node [v75,v0,v1,v443,v2,v3] .nil .nil) (.node [v75,v0,v1,v242,v3,v377] .nil .nil))) (.node [v75,v0,v1,v187,v3,v4] (.node [v75,v0,v1,v250,v3,v4] (.node [v75,v0,v1,v251,v3,v4] .nil .nil) (.node [v75,v0,v1,v175,v3,v4] .nil .nil)) (.node [v75,v0,v1,v255,v3,v4] (.node [v75,v0,v1,v27,v3,v4] .nil .nil) (.node [v75,v0,v1,v2,v192,v104] .nil .nil)))) (.node [v75,v0,v1,v2,v3,v179] (.node [v75,v0,v1,v2,v3,v4] (.node [v75,v0,v1,v2,v3,v215] (.node [v75,v0,v1,v2,v3,v170] .nil .nil) (.node [v75,v0,v1,v2,v3,v155] .nil .nil)) (.node [v75,v0,v1,v2,v3,v145] (.node [v75,v0,v1,v2,v3,v444] .nil .nil) (.node [v75,v0,v1,v2,v3,v203] .nil .nil))) (.node [v75,v0,v1,v2,v3,v16] (.node [v75,v0,v1,v2,v3,v445] (.node [v75,v0,v1,v2,v3,v446] .nil .nil) (.node [v75,v0,v1,v2,v3,v447] .nil .nil)) (.node [v75,v0,v1,v286,v3,v4] (.node [v75,v0,v1,v2,v3,v99] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5llrrll : everyKey (rowOK 4 tree_4) tree_5llrrll = true := by decide +kernel
def tree_5llrrlr : BinaryTree (List W) := (.node [v75,v1,v156,v2,v3,v4] (.node [v75,v0,v168,v2,v3,v4] (.node [v75,v0,v289,v2,v3,v4] (.node [v75,v0,v1,v134,v3,v4] (.node [v75,v0,v1,v448,v3,v4] .nil .nil) (.node [v75,v0,v1,v114,v3,v4] .nil .nil)) (.node [v75,v0,v449,v2,v3,v4] (.node [v75,v0,v450,v2,v3,v4] .nil .nil) (.node [v75,v0,v288,v2,v3,v4] .nil .nil))) (.node [v75,v293,v1,v2,v3,v4] (.node [v75,v451,v1,v2,v3,v4] (.node [v75,v296,v1,v2,v3,v4] .nil .nil) (.node [v75,v452,v1,v2,v3,v4] .nil .nil)) (.node [v75,v1,v306,v2,v3,v4] (.node [v75,v303,v1,v2,v3,v4] .nil .nil) .nil))) (.node [v453,v0,v1,v2,v3,v4] (.node [v454,v0,v1,v2,v3,v4] (.node [v455,v0,v1,v2,v3,v4] (.node [v75,v1,v45,v2,v3,v4] .nil .nil) (.node [v454,v0,v1,v2,v3,v155] .nil .nil)) (.node [v456,v0,v1,v2,v3,v4] (.node [v456,v0,v1,v2,v3,v215] .nil .nil) (.node [v453,v0,v1,v2,v3,v170] .nil .nil))) (.node [v86,v330,v0,v1,v2,v109] (.node [v86,v330,v0,v1,v2,v111] (.node [v86,v330,v0,v1,v2,v107] .nil .nil) (.node [v86,v330,v0,v1,v2,v5] .nil .nil)) (.node [v86,v54,v0,v1,v2,v5] (.node [v86,v330,v0,v1,v2,v99] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5llrrlr : everyKey (rowOK 4 tree_4) tree_5llrrlr = true := by decide +kernel
def tree_5llrrl : BinaryTree (List W) := .node [v75,v0,v1,v457,v3,v4] tree_5llrrll tree_5llrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5llrrl : everyKey (rowOK 4 tree_4) tree_5llrrl = true := by
  change (_ && everyKey _ tree_5llrrll && everyKey _ tree_5llrrlr) = true
  rw [ok_tree_5llrrll, ok_tree_5llrrlr]
  decide +kernel
def tree_5llrrrl : BinaryTree (List W) := (.node [v89,v0,v200,v2,v3,v5] (.node [v86,v0,v1,v2,v458,v5] (.node [v86,v0,v1,v2,v10,v4] (.node [v86,v0,v1,v27,v3,v5] (.node [v86,v0,v9,v2,v3,v5] .nil .nil) (.node [v86,v0,v1,v2,v260,v4] .nil .nil)) (.node [v86,v0,v1,v2,v3,v16] (.node [v86,v0,v1,v2,v3,v261] .nil .nil) (.node [v86,v0,v1,v2,v459,v5] .nil .nil))) (.node [v460,v0,v1,v2,v3,v5] (.node [v461,v0,v1,v2,v3,v99] (.node [v86,v0,v1,v2,v462,v5] .nil .nil) (.node [v463,v0,v1,v2,v3,v5] .nil .nil)) (.node [v89,v21,v1,v2,v5,v169] (.node [v89,v136,v0,v1,v3,v5] .nil .nil) .nil))) (.node [v464,v0,v1,v2,v3,v5] (.node [v89,v0,v1,v2,v3,v177] (.node [v89,v0,v1,v175,v3,v5] (.node [v89,v0,v174,v2,v3,v5] .nil .nil) (.node [v89,v0,v1,v2,v107,v3] .nil .nil)) (.node [v89,v0,v1,v2,v3,v99] (.node [v89,v0,v1,v2,v3,v5] .nil .nil) (.node [v465,v0,v1,v2,v3,v99] .nil .nil))) (.node [v85,v0,v1,v187,v3,v5] (.node [v85,v186,v1,v2,v3,v5] (.node [v85,v135,v0,v1,v3,v5] .nil .nil) (.node [v85,v0,v32,v2,v5,v226] .nil .nil)) (.node [v85,v0,v1,v2,v3,v213] (.node [v85,v0,v1,v2,v107,v3] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5llrrrl : everyKey (rowOK 4 tree_4) tree_5llrrrl = true := by decide +kernel
def tree_5llrrrr : BinaryTree (List W) := (.node [v466,v0,v1,v2,v3,v5] (.node [v91,v0,v152,v2,v3,v5] (.node [v467,v0,v1,v2,v3,v5] (.node [v85,v1,v306,v2,v3,v5] (.node [v85,v0,v1,v2,v3,v99] .nil .nil) (.node [v468,v0,v1,v2,v3,v5] .nil .nil)) (.node [v91,v151,v1,v2,v3,v5] (.node [v469,v0,v1,v2,v3,v99] .nil .nil) (.node [v91,v0,v149,v2,v3,v5] .nil .nil))) (.node [v91,v0,v1,v2,v3,v5] (.node [v91,v0,v1,v2,v107,v3] (.node [v91,v0,v1,v41,v5,v244] .nil .nil) (.node [v91,v0,v1,v2,v3,v154] .nil .nil)) (.node [v91,v1,v156,v2,v3,v5] (.node [v91,v0,v1,v2,v3,v99] .nil .nil) .nil))) (.node [v90,v0,v1,v2,v3,v5] (.node [v470,v0,v1,v2,v107,v4] (.node [v471,v0,v1,v2,v3,v99] (.node [v472,v0,v1,v2,v3,v5] .nil .nil) (.node [v473,v0,v1,v2,v3,v5] .nil .nil)) (.node [v90,v0,v1,v2,v3,v474] (.node [v90,v0,v1,v2,v3] .nil .nil) (.node [v90,v0,v1,v2,v3,v4] .nil .nil))) (.node [v366,v0,v1,v2,v260,v4] (.node [v475,v0,v1,v2,v3,v99] (.node [v90,v0,v1,v2,v3,v99] .nil .nil) (.node [v366,v102,v0,v1,v2,v4] .nil .nil)) (.node [v476,v0,v1,v2,v3,v99] (.node [v366,v0,v1,v2,v3,v16] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5llrrrr : everyKey (rowOK 4 tree_4) tree_5llrrrr = true := by decide +kernel
def tree_5llrrr : BinaryTree (List W) := .node [v85,v0,v1,v2,v3,v5] tree_5llrrrl tree_5llrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5llrrr : everyKey (rowOK 4 tree_4) tree_5llrrr = true := by
  change (_ && everyKey _ tree_5llrrrl && everyKey _ tree_5llrrrr) = true
  rw [ok_tree_5llrrrl, ok_tree_5llrrrr]
  decide +kernel
def tree_5llrr : BinaryTree (List W) := .node [v86,v8,v1,v2,v3,v5] tree_5llrrl tree_5llrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5llrr : everyKey (rowOK 4 tree_4) tree_5llrr = true := by
  change (_ && everyKey _ tree_5llrrl && everyKey _ tree_5llrrr) = true
  rw [ok_tree_5llrrl, ok_tree_5llrrr]
  decide +kernel
def tree_5llr : BinaryTree (List W) := .node [v75,v0,v174,v2,v3,v4] tree_5llrl tree_5llrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5llr : everyKey (rowOK 4 tree_4) tree_5llr = true := by
  change (_ && everyKey _ tree_5llrl && everyKey _ tree_5llrr) = true
  rw [ok_tree_5llrl, ok_tree_5llrr]
  decide +kernel
def tree_5ll : BinaryTree (List W) := .node [v79,v188,v1,v2,v3,v99] tree_5lll tree_5llr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5ll : everyKey (rowOK 4 tree_4) tree_5ll = true := by
  change (_ && everyKey _ tree_5lll && everyKey _ tree_5llr) = true
  rw [ok_tree_5lll, ok_tree_5llr]
  decide +kernel
def tree_5lrllll : BinaryTree (List W) := (.node [v92,v0,v1,v2,v10,v4] (.node [v83,v1,v44,v2,v4,v5] (.node [v83,v1,v84,v2,v315,v4] (.node [v83,v0,v1,v2,v3,v51] (.node [v83,v0,v1,v2,v3,v16] .nil .nil) (.node [v83,v1,v84,v2,v107,v4] .nil .nil)) (.node [v83,v1,v84,v2,v4,v316] (.node [v83,v1,v84,v2,v4,v5] .nil .nil) (.node [v83,v1,v84,v2,v4,v99] .nil .nil))) (.node [v92,v0,v93,v2,v4,v5] (.node [v92,v0,v93,v2,v107,v4] (.node [v477,v0,v1,v2,v3,v99] .nil .nil) (.node [v92,v0,v93,v2,v214,v4] .nil .nil)) (.node [v92,v0,v93,v2,v4,v99] (.node [v92,v0,v93,v2,v4,v216] .nil .nil) (.node [v92,v0,v30,v2,v4,v5] .nil .nil)))) (.node [v94,v95,v0,v1,v4,v99] (.node [v94,v95,v0,v1,v107,v4] (.node [v92,v0,v1,v2,v3,v31] (.node [v92,v0,v1,v2,v3,v16] .nil .nil) (.node [v478,v0,v1,v2,v3,v99] .nil .nil)) (.node [v94,v95,v0,v1,v4,v5] (.node [v94,v95,v0,v1,v148,v4] .nil .nil) (.node [v94,v95,v0,v1,v4,v153] .nil .nil))) (.node [v94,v0,v1,v2,v3,v12] (.node [v94,v0,v1,v2,v10,v4] (.node [v94,v11,v0,v1,v4,v5] .nil .nil) (.node [v94,v0,v1,v2,v3,v16] .nil .nil)) (.node [v330,v0,v1,v2,v378,v5] (.node [v330,v54,v0,v1,v2,v5] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5lrllll : everyKey (rowOK 4 tree_4) tree_5lrllll = true := by decide +kernel
def tree_5lrlllr : BinaryTree (List W) := (.node [v479,v0,v480,v2,v3,v4] (.node [v100,v0,v1,v2,v107,v4] (.node [v330,v0,v1,v2,v3,v99] (.node [v330,v0,v1,v2,v3,v112] (.node [v330,v0,v1,v2,v266,v3] .nil .nil) (.node [v330,v0,v1,v2,v3,v16] .nil .nil)) (.node [v137,v0,v1,v2,v107,v4] (.node [v330,v0,v1,v2,v99,v104] .nil .nil) (.node [v101,v0,v1,v2,v107,v4] .nil .nil))) (.node [v481,v0,v1,v2,v3,v16] (.node [v482,v0,v1,v2,v4,v5] (.node [v98,v0,v1,v2,v99,v104] .nil .nil) (.node [v482,v0,v1,v2,v4,v99] .nil .nil)) (.node [v481,v1,v341,v2,v3,v4] (.node [v481,v1,v483,v2,v3,v4] .nil .nil) .nil))) (.node [v102,v0,v1,v2,v4] (.node [v484,v356,v0,v1,v3,v4] (.node [v479,v0,v1,v2,v3,v16] (.node [v479,v0,v345,v2,v3,v4] .nil .nil) (.node [v484,v485,v0,v1,v3,v4] .nil .nil)) (.node [v102,v0,v1,v2,v107,v4] (.node [v484,v0,v1,v2,v3,v16] .nil .nil) (.node [v102,v0,v1,v2,v3,v4] .nil .nil))) (.node [v486,v0,v1,v2,v3,v5] (.node [v102,v0,v1,v2,v4,v487] (.node [v102,v0,v1,v2,v4,v5] .nil .nil) (.node [v486,v0,v1,v2,v315,v3] .nil .nil)) (.node [v488,v0,v1,v2,v3,v5] (.node [v488,v0,v1,v2,v214,v3] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5lrlllr : everyKey (rowOK 4 tree_4) tree_5lrlllr = true := by decide +kernel
def tree_5lrlll : BinaryTree (List W) := .node [v330,v0,v1,v2,v10,v3] tree_5lrllll tree_5lrlllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5lrlll : everyKey (rowOK 4 tree_4) tree_5lrlll = true := by
  change (_ && everyKey _ tree_5lrllll && everyKey _ tree_5lrlllr) = true
  rw [ok_tree_5lrllll, ok_tree_5lrlllr]
  decide +kernel
def tree_5lrllrl : BinaryTree (List W) := (.node [v489,v0,v1,v2,v3,v4] (.node [v490,v0,v1,v2,v3,v4] (.node [v105,v0,v1,v2,v111,v3] (.node [v105,v0,v1,v2,v107,v3] (.node [v491,v0,v1,v2,v3,v5] .nil .nil) (.node [v105,v0,v1,v2,v107,v487] .nil .nil)) (.node [v105,v0,v1,v2,v3,v16] (.node [v105,v0,v1,v2,v3,v5] .nil .nil) (.node [v105,v0,v1,v2,v3,v99] .nil .nil))) (.node [v14,v0,v119,v3,v4,v5] (.node [v492,v0,v1,v2,v3,v4] (.node [v493,v0,v1,v2,v3,v4] .nil .nil) (.node [v494,v0,v1,v2,v3,v4] .nil .nil)) (.node [v14,v120,v2,v3,v4,v5] (.node [v14,v1,v121,v3,v4,v5] .nil .nil) (.node [v495,v0,v1,v2,v3,v4] .nil .nil)))) (.node [v54,v0,v1,v2,v192,v5] (.node [v496,v0,v1,v2,v3,v4] (.node [v108,v0,v1,v2,v192,v104] (.node [v497,v0,v1,v2,v3,v4] .nil .nil) (.node [v108,v0,v1,v2,v3,v4] .nil .nil)) (.node [v498,v0,v1,v2,v3,v4] (.node [v499,v0,v1,v2,v3,v4] .nil .nil) (.node [v500,v0,v1,v2,v3,v4] .nil .nil))) (.node [v54,v0,v1,v2,v5,v104] (.node [v54,v0,v1,v2,v4,v5] (.node [v54,v0,v1,v2,v3,v5] .nil .nil) (.node [v54,v0,v1,v2,v5] .nil .nil)) (.node [v501,v0,v1,v2,v3,v4] (.node [v502,v0,v212,v3,v4,v5] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5lrllrl : everyKey (rowOK 4 tree_4) tree_5lrllrl = true := by decide +kernel
def tree_5lrllrr : BinaryTree (List W) := (.node [v115,v503,v2,v3,v4,v5] (.node [v115,v0,v1,v2,v3,v16] (.node [v115,v123,v119,v3,v4,v5] (.node [v504,v0,v1,v2,v3,v99] (.node [v505,v0,v1,v2,v3,v4] .nil .nil) (.node [v506,v0,v1,v2,v3,v5] .nil .nil)) (.node [v115,v127,v2,v3,v4,v5] (.node [v115,v130,v121,v3,v4,v5] .nil .nil) (.node [v115,v507,v2,v3,v4,v5] .nil .nil))) (.node [v115,v288,v2,v3,v4,v5] (.node [v115,v293,v2,v3,v4,v5] (.node [v115,v0,v114,v3,v4,v5] .nil .nil) (.node [v115,v1,v134,v3,v4,v5] .nil .nil)) (.node [v115,v508,v2,v3,v4,v5] (.node [v115,v49,v2,v3,v4,v5] .nil .nil) .nil))) (.node [v123,v129,v2,v3,v4,v5] (.node [v115,v120,v2,v3,v4,v99] (.node [v115,v120,v2,v107,v3,v4] (.node [v115,v509,v2,v3,v4,v5] .nil .nil) (.node [v115,v120,v2,v3,v4,v5] .nil .nil)) (.node [v510,v0,v1,v2,v3,v4] (.node [v115,v2,v3,v4,v5,v106] .nil .nil) (.node [v123,v129,v124,v3,v4,v5] .nil .nil))) (.node [v123,v132,v166,v3,v4,v5] (.node [v123,v0,v168,v3,v4,v5] (.node [v123,v0,v1,v2,v3,v16] .nil .nil) (.node [v123,v511,v1,v3,v4,v5] .nil .nil)) (.node [v123,v303,v1,v3,v4,v5] (.node [v123,v195,v1,v3,v4,v5] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5lrllrr : everyKey (rowOK 4 tree_4) tree_5lrllrr = true := by decide +kernel
def tree_5lrllr : BinaryTree (List W) := .node [v512,v158,v1,v3,v4,v5] tree_5lrllrl tree_5lrllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5lrllr : everyKey (rowOK 4 tree_4) tree_5lrllr = true := by
  change (_ && everyKey _ tree_5lrllrl && everyKey _ tree_5lrllrr) = true
  rw [ok_tree_5lrllrl, ok_tree_5lrllrr]
  decide +kernel
def tree_5lrll : BinaryTree (List W) := .node [v491,v0,v1,v2,v148,v3] tree_5lrlll tree_5lrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5lrll : everyKey (rowOK 4 tree_4) tree_5lrll = true := by
  change (_ && everyKey _ tree_5lrlll && everyKey _ tree_5lrllr) = true
  rw [ok_tree_5lrlll, ok_tree_5lrllr]
  decide +kernel
def tree_5lrlrll : BinaryTree (List W) := (.node [v113,v130,v2,v3,v4,v5] (.node [v123,v124,v168,v3,v4,v5] (.node [v123,v1,v173,v3,v4,v5] (.node [v123,v1,v124,v3,v4,v5] (.node [v123,v1,v124,v107,v3,v4] .nil .nil) (.node [v123,v1,v124,v3,v4,v99] .nil .nil)) (.node [v123,v1,v128,v3,v4,v5] (.node [v123,v1,v50,v3,v4,v5] .nil .nil) (.node [v123,v288,v124,v3,v4,v5] .nil .nil))) (.node [v122,v1,v2,v107,v3,v4] (.node [v513,v0,v1,v2,v3,v99] (.node [v514,v0,v1,v3,v4,v5] .nil .nil) (.node [v515,v0,v1,v2,v3,v4] .nil .nil)) (.node [v516,v1,v2,v3,v4,v5] (.node [v122,v1,v2,v3,v4,v5] .nil .nil) (.node [v113,v130,v132,v3,v4,v5] .nil .nil)))) (.node [v113,v120,v2,v3,v4,v5] (.node [v113,v1,v2,v107,v3,v4] (.node [v113,v166,v2,v3,v4,v5] (.node [v113,v93,v2,v3,v4,v5] .nil .nil) (.node [v113,v32,v2,v3,v4,v5] .nil .nil)) (.node [v113,v1,v2,v3,v4,v99] (.node [v113,v1,v2,v3,v4,v5] .nil .nil) (.node [v113,v288,v2,v3,v4,v5] .nil .nil))) (.node [v517,v1,v2,v3,v4,v5] (.node [v518,v1,v2,v3,v4,v5] (.node [v113,v2,v119,v3,v4,v5] .nil .nil) (.node [v519,v1,v2,v3,v4,v5] .nil .nil)) (.node [v130,v164,v124,v3,v4,v5] (.node [v520,v1,v2,v3,v4,v5] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5lrlrll : everyKey (rowOK 4 tree_4) tree_5lrlrll = true := by decide +kernel
def tree_5lrlrlr : BinaryTree (List W) := (.node [v521,v0,v1,v2,v3,v99] (.node [v130,v0,v241,v3,v4,v5] (.node [v130,v0,v299,v3,v4,v5] (.node [v130,v0,v132,v3,v4,v5] (.node [v130,v0,v132,v107,v3,v4] .nil .nil) (.node [v130,v0,v132,v3,v4,v99] .nil .nil)) (.node [v130,v0,v1,v2,v3,v16] (.node [v130,v0,v29,v3,v4,v5] .nil .nil) (.node [v130,v0,v522,v3,v4,v5] .nil .nil))) (.node [v130,v132,v303,v3,v4,v5] (.node [v130,v0,v128,v3,v4,v5] (.node [v130,v0,v168,v3,v4,v5] .nil .nil) (.node [v130,v293,v132,v3,v4,v5] .nil .nil)) (.node [v523,v0,v1,v3,v4,v5] (.node [v130,v303,v1,v3,v4,v5] .nil .nil) .nil))) (.node [v129,v0,v2,v3,v4,v5] (.node [v524,v0,v2,v3,v4,v5] (.node [v133,v0,v2,v107,v3,v4] (.node [v525,v0,v1,v2,v3,v4] .nil .nil) (.node [v133,v0,v2,v3,v4,v5] .nil .nil)) (.node [v129,v21,v2,v3,v4,v5] (.node [v129,v164,v2,v3,v4,v5] .nil .nil) (.node [v129,v0,v2,v107,v3,v4] .nil .nil))) (.node [v129,v120,v2,v3,v4,v5] (.node [v129,v293,v2,v3,v4,v5] (.node [v129,v0,v2,v3,v4,v99] .nil .nil) (.node [v129,v84,v2,v3,v4,v5] .nil .nil)) (.node [v526,v0,v2,v3,v4,v5] (.node [v129,v2,v121,v3,v4,v5] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5lrlrlr : everyKey (rowOK 4 tree_4) tree_5lrlrlr = true := by decide +kernel
def tree_5lrlrl : BinaryTree (List W) := .node [v130,v163,v132,v3,v4,v5] tree_5lrlrll tree_5lrlrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5lrlrl : everyKey (rowOK 4 tree_4) tree_5lrlrl = true := by
  change (_ && everyKey _ tree_5lrlrll && everyKey _ tree_5lrlrlr) = true
  rw [ok_tree_5lrlrll, ok_tree_5lrlrlr]
  decide +kernel
def tree_5lrlrrl : BinaryTree (List W) := (.node [v95,v163,v1,v3,v4,v5] (.node [v485,v0,v1,v2,v3,v16] (.node [v354,v0,v1,v2,v3,v16] (.node [v527,v0,v2,v3,v4,v5] (.node [v528,v0,v2,v3,v4,v5] .nil .nil) (.node [v354,v71,v0,v1,v3,v5] .nil .nil)) (.node [v529,v0,v1,v2,v3,v4] (.node [v354,v0,v1,v3,v530,v5] .nil .nil) (.node [v531,v0,v1,v2,v3,v4] .nil .nil))) (.node [v127,v0,v132,v3,v4,v5] (.node [v356,v0,v1,v248,v3,v4] (.node [v356,v139,v0,v1,v3,v4] .nil .nil) (.node [v356,v0,v1,v2,v3,v16] .nil .nil)) (.node [v95,v11,v0,v1,v4,v5] (.node [v127,v1,v124,v3,v4,v5] .nil .nil) .nil))) (.node [v95,v0,v1,v532,v4,v5] (.node [v95,v0,v1,v242,v3,v99] (.node [v95,v0,v223,v3,v4,v5] (.node [v95,v151,v1,v3,v4,v5] .nil .nil) (.node [v95,v0,v152,v3,v4,v5] .nil .nil)) (.node [v95,v0,v1,v3,v155,v5] (.node [v95,v0,v1,v2,v3,v16] .nil .nil) (.node [v95,v0,v1,v533,v4,v5] .nil .nil))) (.node [v136,v21,v1,v4,v5,v169] (.node [v534,v0,v1,v3,v4,v5] (.node [v95,v0,v1,v535,v4,v5] .nil .nil) (.node [v536,v0,v1,v3,v4,v5] .nil .nil)) (.node [v136,v0,v174,v3,v4,v5] (.node [v136,v0,v200,v3,v4,v5] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5lrlrrl : everyKey (rowOK 4 tree_4) tree_5lrlrrl = true := by decide +kernel
def tree_5lrlrrr : BinaryTree (List W) := (.node [v13,v8,v1,v3,v4,v5] (.node [v135,v0,v1,v107,v3,v4] (.node [v136,v0,v1,v3,v4,v99] (.node [v136,v0,v1,v3,v4,v177] (.node [v136,v0,v1,v3,v170,v5] .nil .nil) (.node [v136,v0,v1,v3,v4,v5] .nil .nil)) (.node [v135,v186,v1,v3,v4,v5] (.node [v537,v0,v1,v3,v4,v5] .nil .nil) (.node [v135,v0,v32,v4,v5,v226] .nil .nil))) (.node [v135,v0,v1,v3,v4,v99] (.node [v135,v0,v1,v3,v4,v213] (.node [v135,v0,v1,v3,v215,v5] .nil .nil) (.node [v135,v0,v1,v3,v4,v5] .nil .nil)) (.node [v67,v0,v1,v2,v3,v16] (.node [v135,v1,v306,v3,v4,v5] .nil .nil) .nil))) (.node [v13,v0,v1,v3,v99,v104] (.node [v13,v0,v1,v107,v3,v4] (.node [v13,v0,v9,v3,v4,v5] (.node [v13,v0,v23,v3,v4,v5] .nil .nil) (.node [v13,v0,v1,v192,v5,v104] .nil .nil)) (.node [v13,v0,v1,v3,v4,v5] (.node [v13,v0,v1,v3,v4,v110] .nil .nil) (.node [v13,v0,v1,v3,v4,v99] .nil .nil))) (.node [v538,v0,v1,v3,v4,v5] (.node [v539,v0,v1,v3,v4,v5] (.node [v13,v1,v45,v3,v4,v5] .nil .nil) (.node [v539,v0,v1,v3,v4,v99] .nil .nil)) (.node [v540,v0,v1,v3,v4,v99] (.node [v540,v0,v1,v3,v4,v5] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5lrlrrr : everyKey (rowOK 4 tree_4) tree_5lrlrrr = true := by decide +kernel
def tree_5lrlrr : BinaryTree (List W) := .node [v136,v0,v1,v107,v3,v4] tree_5lrlrrl tree_5lrlrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5lrlrr : everyKey (rowOK 4 tree_4) tree_5lrlrr = true := by
  change (_ && everyKey _ tree_5lrlrrl && everyKey _ tree_5lrlrrr) = true
  rw [ok_tree_5lrlrrl, ok_tree_5lrlrrr]
  decide +kernel
def tree_5lrlr : BinaryTree (List W) := .node [v541,v0,v2,v3,v4,v5] tree_5lrlrl tree_5lrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5lrlr : everyKey (rowOK 4 tree_4) tree_5lrlr = true := by
  change (_ && everyKey _ tree_5lrlrl && everyKey _ tree_5lrlrr) = true
  rw [ok_tree_5lrlrl, ok_tree_5lrlrr]
  decide +kernel
def tree_5lrl : BinaryTree (List W) := .node [v123,v223,v124,v3,v4,v5] tree_5lrll tree_5lrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5lrl : everyKey (rowOK 4 tree_4) tree_5lrl = true := by
  change (_ && everyKey _ tree_5lrll && everyKey _ tree_5lrlr) = true
  rw [ok_tree_5lrll, ok_tree_5lrlr]
  decide +kernel
def tree_5lrrlll : BinaryTree (List W) := (.node [v542,v0,v1,v2,v3,v4] (.node [v139,v0,v1,v3,v4,v5] (.node [v543,v0,v1,v3,v4,v99] (.node [v544,v0,v1,v3,v4,v5] (.node [v545,v0,v1,v3,v4,v5] .nil .nil) (.node [v543,v0,v1,v3,v4,v5] .nil .nil)) (.node [v139,v0,v1,v2,v3,v4] (.node [v139,v0,v1,v546,v3,v4] .nil .nil) (.node [v139,v0,v1,v3,v4] .nil .nil))) (.node [v71,v0,v1,v2,v3,v5] (.node [v547,v0,v1,v2,v107,v4] (.node [v139,v0,v1,v3,v4,v548] .nil .nil) (.node [v71,v0,v1,v242,v3,v5] .nil .nil)) (.node [v71,v0,v1,v3,v377,v5] (.node [v71,v0,v1,v3,v4,v5] .nil .nil) (.node [v71,v0,v1,v3,v5] .nil .nil)))) (.node [v82,v0,v1,v2,v3,v4] (.node [v144,v0,v1,v142,v2,v3] (.node [v549,v0,v1,v2,v3,v4] (.node [v550,v0,v1,v2,v3,v4] .nil .nil) (.node [v144,v0,v1,v242,v3,v377] .nil .nil)) (.node [v144,v0,v1,v2,v3,v99] (.node [v144,v0,v1,v2,v3,v4] .nil .nil) (.node [v82,v0,v1,v242,v2,v3] .nil .nil))) (.node [v551,v0,v1,v2,v3,v5] (.node [v552,v0,v1,v2,v3,v99] (.node [v82,v0,v1,v2,v3,v99] .nil .nil) (.node [v551,v0,v1,v2,v107,v3] .nil .nil)) (.node [v11,v0,v1,v2,v4,v5] (.node [v11,v0,v1,v41,v4,v5] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5lrrlll : everyKey (rowOK 4 tree_4) tree_5lrrlll = true := by decide +kernel
def tree_5lrrllr : BinaryTree (List W) := (.node [v158,v1,v553,v3,v4,v5] (.node [v158,v0,v1,v2,v3,v16] (.node [v554,v0,v1,v2,v3,v4] (.node [v11,v0,v1,v4,v5,v244] (.node [v11,v0,v1,v4,v5] .nil .nil) (.node [v555,v0,v1,v2,v3,v4] .nil .nil)) (.node [v556,v0,v1,v2,v3,v5] (.node [v557,v0,v1,v2,v3,v99] .nil .nil) (.node [v158,v164,v119,v3,v4,v5] .nil .nil))) (.node [v158,v303,v1,v3,v4,v5] (.node [v158,v132,v120,v3,v4,v5] (.node [v158,v0,v168,v3,v4,v5] .nil .nil) (.node [v158,v299,v1,v3,v4,v5] .nil .nil)) (.node [v158,v1,v134,v3,v4,v5] (.node [v158,v1,v50,v3,v4,v5] .nil .nil) .nil))) (.node [v558,v0,v1,v2,v3,v4] (.node [v158,v1,v121,v3,v4,v5] (.node [v158,v1,v559,v3,v4,v5] (.node [v158,v1,v560,v3,v4,v5] .nil .nil) (.node [v158,v1,v121,v107,v3,v4] .nil .nil)) (.node [v158,v1,v3,v4,v5,v106] (.node [v158,v1,v121,v3,v4,v99] .nil .nil) (.node [v158,v288,v2,v3,v4,v5] .nil .nil))) (.node [v164,v195,v166,v3,v4,v5] (.node [v164,v0,v114,v3,v4,v5] (.node [v164,v0,v1,v2,v3,v16] .nil .nil) (.node [v164,v293,v2,v3,v4,v5] .nil .nil)) (.node [v164,v561,v2,v3,v4,v5] (.node [v164,v195,v1,v3,v4,v5] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5lrrllr : everyKey (rowOK 4 tree_4) tree_5lrrllr = true := by decide +kernel
def tree_5lrrll : BinaryTree (List W) := .node [v11,v0,v1,v3,v4,v5] tree_5lrrlll tree_5lrrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5lrrll : everyKey (rowOK 4 tree_4) tree_5lrrll = true := by
  change (_ && everyKey _ tree_5lrrlll && everyKey _ tree_5lrrllr) = true
  rw [ok_tree_5lrrlll, ok_tree_5lrrllr]
  decide +kernel
def tree_5lrrlrl : BinaryTree (List W) := (.node [v163,v132,v1,v3,v4,v5] (.node [v164,v49,v2,v3,v4,v5] (.node [v164,v166,v134,v3,v4,v5] (.node [v164,v166,v2,v3,v4,v5] (.node [v164,v166,v2,v107,v3,v4] .nil .nil) (.node [v164,v166,v2,v3,v4,v99] .nil .nil)) (.node [v164,v300,v2,v3,v4,v5] (.node [v164,v166,v114,v3,v4,v5] .nil .nil) (.node [v164,v173,v2,v3,v4,v5] .nil .nil))) (.node [v167,v1,v2,v107,v3,v4] (.node [v562,v0,v1,v2,v3,v99] (.node [v563,v0,v2,v3,v4,v5] .nil .nil) (.node [v564,v0,v1,v2,v3,v4] .nil .nil)) (.node [v565,v1,v2,v3,v4,v5] (.node [v167,v1,v2,v3,v4,v5] .nil .nil) .nil))) (.node [v163,v1,v119,v3,v4,v5] (.node [v163,v1,v2,v3,v4,v5] (.node [v163,v1,v41,v3,v4,v5] (.node [v163,v1,v124,v3,v4,v5] .nil .nil) (.node [v163,v1,v2,v107,v3,v4] .nil .nil)) (.node [v163,v1,v134,v3,v4,v5] (.node [v163,v1,v2,v3,v4,v99] .nil .nil) (.node [v163,v1,v121,v3,v4,v5] .nil .nil))) (.node [v566,v1,v2,v3,v4,v5] (.node [v567,v1,v2,v3,v4,v5] (.node [v568,v1,v2,v3,v4,v5] .nil .nil) (.node [v569,v1,v2,v3,v4,v5] .nil .nil)) (.node [v172,v0,v119,v3,v4,v5] (.node [v570,v0,v1,v2,v3,v4] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5lrrlrl : everyKey (rowOK 4 tree_4) tree_5lrrlrl = true := by decide +kernel
def tree_5lrrlrr : BinaryTree (List W) := (.node [v21,v1,v2,v3,v170,v5] (.node [v21,v200,v2,v4,v5,v169] (.node [v21,v171,v1,v2,v3,v99] (.node [v571,v0,v1,v2,v3,v16] (.node [v172,v1,v124,v3,v4,v5] .nil .nil) (.node [v571,v1,v2,v3,v4,v572] .nil .nil)) (.node [v21,v0,v1,v2,v3,v16] (.node [v21,v0,v1,v2,v10,v4] .nil .nil) (.node [v21,v195,v1,v3,v4,v5] .nil .nil))) (.node [v21,v1,v175,v3,v4,v5] (.node [v21,v174,v2,v4,v5,v169] (.node [v21,v174,v2,v3,v4,v5] .nil .nil) (.node [v21,v1,v44,v2,v4,v5] .nil .nil)) (.node [v21,v1,v2,v107,v4,v169] (.node [v21,v1,v175,v4,v5,v169] .nil .nil) .nil))) (.node [v573,v0,v1,v2,v3,v99] (.node [v21,v1,v2,v4,v5,v574] (.node [v21,v1,v2,v4,v177,v169] (.node [v21,v1,v2,v170,v5,v169] .nil .nil) (.node [v21,v1,v2,v4,v5,v575] .nil .nil)) (.node [v21,v1,v2,v4,v5,v169] (.node [v21,v1,v2,v4,v5,v181] .nil .nil) (.node [v21,v1,v2,v4,v99,v169] .nil .nil))) (.node [v576,v0,v1,v2,v3,v99] (.node [v577,v0,v1,v2,v3,v4] (.node [v578,v0,v1,v2,v107,v4] .nil .nil) (.node [v579,v0,v1,v2,v3,v4] .nil .nil)) (.node [v171,v0,v1,v2,v10,v3] (.node [v171,v0,v1,v80,v2,v3] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5lrrlrr : everyKey (rowOK 4 tree_4) tree_5lrrlrr = true := by decide +kernel
def tree_5lrrlr : BinaryTree (List W) := .node [v172,v166,v2,v3,v4,v5] tree_5lrrlrl tree_5lrrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5lrrlr : everyKey (rowOK 4 tree_4) tree_5lrrlr = true := by
  change (_ && everyKey _ tree_5lrrlrl && everyKey _ tree_5lrrlrr) = true
  rw [ok_tree_5lrrlrl, ok_tree_5lrrlrr]
  decide +kernel
def tree_5lrrl : BinaryTree (List W) := .node [v164,v166,v241,v3,v4,v5] tree_5lrrll tree_5lrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5lrrl : everyKey (rowOK 4 tree_4) tree_5lrrl = true := by
  change (_ && everyKey _ tree_5lrrll && everyKey _ tree_5lrrlr) = true
  rw [ok_tree_5lrrll, ok_tree_5lrrlr]
  decide +kernel
def tree_5lrrrll : BinaryTree (List W) := (.node [v178,v0,v1,v2,v3,v99] (.node [v171,v1,v2,v180,v3,v5] (.node [v171,v580,v1,v2,v3,v5] (.node [v171,v0,v1,v2,v3,v16] (.node [v171,v0,v1,v2,v3,v112] .nil .nil) (.node [v171,v0,v1,v2,v3,v99] .nil .nil)) (.node [v171,v1,v69,v2,v3,v5] (.node [v171,v1,v84,v2,v3,v99] .nil .nil) (.node [v171,v1,v307,v2,v3,v371] .nil .nil))) (.node [v171,v1,v2,v3,v371,v5] (.node [v171,v1,v2,v3,v581,v5] (.node [v171,v1,v2,v107,v3,v371] .nil .nil) (.node [v171,v1,v2,v3,v258,v5] .nil .nil)) (.node [v171,v1,v2,v3,v371,v99] (.node [v171,v1,v2,v3,v371,v312] .nil .nil) (.node [v582,v0,v1,v2,v3,v99] .nil .nil)))) (.node [v583,v0,v1,v2,v3,v5] (.node [v183,v0,v1,v2,v107,v3] (.node [v370,v0,v1,v2,v3,v5] (.node [v178,v1,v341,v2,v3,v4] .nil .nil) (.node [v183,v0,v1,v307,v2,v3] .nil .nil)) (.node [v183,v0,v1,v2,v3,v99] (.node [v183,v0,v1,v2,v3,v5] .nil .nil) (.node [v583,v0,v1,v2,v107,v3] .nil .nil))) (.node [v584,v0,v1,v2,v3,v99] (.node [v585,v0,v1,v2,v3,v99] (.node [v586,v0,v1,v2,v3,v4] .nil .nil) (.node [v182,v1,v2,v3,v4,v5] .nil .nil)) (.node [v587,v1,v2,v3,v4,v5] (.node [v211,v1,v2,v3,v4,v5] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5lrrrll : everyKey (rowOK 4 tree_4) tree_5lrrrll = true := by decide +kernel
def tree_5lrrrlr : BinaryTree (List W) := (.node [v186,v93,v2,v3,v4,v5] (.node [v588,v1,v2,v3,v4,v5] (.node [v589,v1,v184,v2,v3,v4] (.node [v589,v0,v1,v2,v3,v16] (.node [v589,v0,v1,v2,v3,v179] .nil .nil) (.node [v589,v418,v1,v2,v3,v4] .nil .nil)) (.node [v589,v1,v2,v3,v4,v590] (.node [v589,v1,v2,v3,v4,v572] .nil .nil) (.node [v353,v1,v2,v3,v4,v590] .nil .nil))) (.node [v188,v1,v2,v3,v4,v591] (.node [v19,v0,v1,v2,v3,v16] (.node [v592,v1,v2,v3,v4,v5] .nil .nil) (.node [v188,v1,v2,v3,v4,v590] .nil .nil)) (.node [v18,v1,v2,v3,v4,v5] (.node [v593,v1,v2,v3,v4,v5] .nil .nil) .nil))) (.node [v186,v1,v2,v3,v4,v99] (.node [v186,v1,v2,v107,v3,v4] (.node [v186,v32,v2,v4,v5,v226] (.node [v186,v32,v2,v3,v4,v5] .nil .nil) (.node [v186,v1,v187,v3,v4,v5] .nil .nil)) (.node [v186,v1,v2,v3,v4,v213] (.node [v186,v1,v2,v3,v215,v5] .nil .nil) (.node [v186,v1,v2,v3,v4,v5] .nil .nil))) (.node [v24,v1,v2,v3,v4,v5] (.node [v594,v1,v2,v3,v4,v5] (.node [v595,v1,v2,v3,v4,v5] .nil .nil) (.node [v596,v1,v2,v3,v4,v5] .nil .nil)) (.node [v151,v152,v2,v3,v4,v5] (.node [v151,v149,v2,v3,v4,v5] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5lrrrlr : everyKey (rowOK 4 tree_4) tree_5lrrrlr = true := by decide +kernel
def tree_5lrrrl : BinaryTree (List W) := .node [v597,v1,v2,v3,v4,v5] tree_5lrrrll tree_5lrrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5lrrrl : everyKey (rowOK 4 tree_4) tree_5lrrrl = true := by
  change (_ && everyKey _ tree_5lrrrll && everyKey _ tree_5lrrrlr) = true
  rw [ok_tree_5lrrrll, ok_tree_5lrrrlr]
  decide +kernel
def tree_5lrrrrl : BinaryTree (List W) := (.node [v8,v1,v2,v192,v3,v5] (.node [v598,v1,v2,v3,v4,v5] (.node [v151,v1,v2,v3,v4,v154] (.node [v151,v1,v2,v107,v3,v4] (.node [v151,v1,v41,v4,v5,v244] .nil .nil) (.node [v151,v1,v2,v3,v155,v5] .nil .nil)) (.node [v151,v1,v2,v3,v4,v99] (.node [v151,v1,v2,v3,v4,v5] .nil .nil) (.node [v599,v1,v2,v3,v4,v5] .nil .nil))) (.node [v8,v23,v2,v3,v4,v5] (.node [v600,v1,v2,v3,v4,v5] (.node [v601,v1,v2,v3,v4,v5] .nil .nil) (.node [v8,v0,v1,v2,v3,v99] .nil .nil)) (.node [v8,v1,v27,v3,v4,v5] (.node [v8,v9,v2,v3,v4,v5] .nil .nil) .nil))) (.node [v8,v1,v2,v3,v99,v104] (.node [v8,v1,v2,v3,v4,v5] (.node [v8,v1,v2,v107,v3,v4] (.node [v8,v1,v2,v192,v5,v104] .nil .nil) (.node [v8,v1,v2,v3,v4,v110] .nil .nil)) (.node [v8,v1,v2,v3,v5,v99] (.node [v8,v1,v2,v3,v4,v99] .nil .nil) (.node [v8,v1,v2,v3,v99] .nil .nil))) (.node [v602,v1,v2,v3,v4,v5] (.node [v26,v1,v2,v3,v4,v5] (.node [v193,v1,v2,v3,v4,v5] .nil .nil) (.node [v28,v1,v2,v3,v4,v5] .nil .nil)) (.node [v603,v1,v2,v3,v4,v5] (.node [v602,v1,v2,v3,v4,v99] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5lrrrrl : everyKey (rowOK 4 tree_4) tree_5lrrrrl = true := by decide +kernel
def tree_5lrrrrr : BinaryTree (List W) := (.node [v0,v132,v29,v3,v4,v5] (.node [v0,v297,v1,v2,v3,v4] (.node [v604,v1,v2,v3,v4,v5] (.node [v605,v1,v2,v3,v4,v5] (.node [v606,v1,v2,v3,v4,v99] .nil .nil) (.node [v607,v1,v2,v3,v4,v5] .nil .nil)) (.node [v199,v1,v2,v3,v4,v99] (.node [v199,v1,v2,v3,v4,v5] .nil .nil) (.node [v0,v608,v1,v2,v3,v4] .nil .nil))) (.node [v0,v609,v1,v2,v3,v99] (.node [v0,v610,v1,v2,v3,v4] (.node [v0,v611,v1,v2,v3,v4] .nil .nil) (.node [v0,v294,v2,v3,v4,v5] .nil .nil)) (.node [v0,v612,v1,v2,v3,v4] (.node [v0,v613,v1,v2,v3,v5] .nil .nil) .nil))) (.node [v0,v614,v1,v2,v3,v4] (.node [v0,v132,v615,v3,v4,v5] (.node [v0,v132,v300,v3,v4,v5] (.node [v0,v132,v223,v3,v4,v5] .nil .nil) (.node [v0,v132,v1,v2,v3,v16] .nil .nil)) (.node [v0,v616,v2,v3,v4,v5] (.node [v0,v132,v114,v3,v4,v5] .nil .nil) (.node [v0,v617,v1,v2,v3,v99] .nil .nil))) (.node [v0,v195,v1,v107,v3,v4] (.node [v0,v198,v1,v3,v4,v5] (.node [v0,v198,v1,v107,v3,v4] .nil .nil) (.node [v0,v618,v1,v3,v4,v5] .nil .nil)) (.node [v0,v195,v1,v3,v4,v99] (.node [v0,v195,v1,v3,v4,v5] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5lrrrrr : everyKey (rowOK 4 tree_4) tree_5lrrrrr = true := by decide +kernel
def tree_5lrrrr : BinaryTree (List W) := .node [v606,v1,v2,v3,v4,v5] tree_5lrrrrl tree_5lrrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5lrrrr : everyKey (rowOK 4 tree_4) tree_5lrrrr = true := by
  change (_ && everyKey _ tree_5lrrrrl && everyKey _ tree_5lrrrrr) = true
  rw [ok_tree_5lrrrrl, ok_tree_5lrrrrr]
  decide +kernel
def tree_5lrrr : BinaryTree (List W) := .node [v151,v1,v41,v3,v4,v5] tree_5lrrrl tree_5lrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5lrrr : everyKey (rowOK 4 tree_4) tree_5lrrr = true := by
  change (_ && everyKey _ tree_5lrrrl && everyKey _ tree_5lrrrr) = true
  rw [ok_tree_5lrrrl, ok_tree_5lrrrr]
  decide +kernel
def tree_5lrr : BinaryTree (List W) := .node [v171,v0,v1,v2,v3,v311] tree_5lrrl tree_5lrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5lrr : everyKey (rowOK 4 tree_4) tree_5lrr = true := by
  change (_ && everyKey _ tree_5lrrl && everyKey _ tree_5lrrr) = true
  rw [ok_tree_5lrrl, ok_tree_5lrrr]
  decide +kernel
def tree_5lr : BinaryTree (List W) := .node [v619,v0,v1,v3,v4,v5] tree_5lrl tree_5lrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5lr : everyKey (rowOK 4 tree_4) tree_5lr = true := by
  change (_ && everyKey _ tree_5lrl && everyKey _ tree_5lrr) = true
  rw [ok_tree_5lrl, ok_tree_5lrr]
  decide +kernel
def tree_5l : BinaryTree (List W) := .node [v83,v0,v1,v2,v10,v4] tree_5ll tree_5lr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5l : everyKey (rowOK 4 tree_4) tree_5l = true := by
  change (_ && everyKey _ tree_5ll && everyKey _ tree_5lr) = true
  rw [ok_tree_5ll, ok_tree_5lr]
  decide +kernel
def tree_5rlllll : BinaryTree (List W) := (.node [v0,v93,v241,v3,v4,v5] (.node [v0,v620,v1,v2,v3,v4] (.node [v0,v362,v70,v2,v3,v5] (.node [v0,v621,v1,v3,v4,v5] (.node [v0,v622,v1,v3,v4,v5] .nil .nil) (.node [v0,v623,v1,v3,v4,v5] .nil .nil)) (.node [v0,v362,v2,v3,v624,v5] (.node [v0,v362,v1,v2,v3,v16] .nil .nil) (.node [v0,v625,v1,v2,v3,v4] .nil .nil))) (.node [v0,v345,v1,v2,v3,v16] (.node [v0,v345,v202,v2,v3,v4] (.node [v0,v480,v1,v2,v3,v16] .nil .nil) (.node [v0,v345,v224,v2,v3,v4] .nil .nil)) (.node [v0,v93,v220,v2,v3,v99] (.node [v0,v93,v30,v2,v4,v5] .nil .nil) (.node [v0,v93,v1,v2,v3,v16] .nil .nil)))) (.node [v0,v200,v175,v3,v4,v5] (.node [v0,v93,v2,v626,v4,v5] (.node [v0,v93,v2,v3,v215,v5] (.node [v0,v93,v187,v3,v4,v5] .nil .nil) (.node [v0,v93,v2,v627,v4,v5] .nil .nil)) (.node [v0,v628,v2,v3,v4,v5] (.node [v0,v93,v2,v629,v4,v5] .nil .nil) (.node [v0,v630,v2,v3,v4,v5] .nil .nil))) (.node [v0,v200,v2,v3,v4,v5] (.node [v0,v200,v2,v3,v170,v5] (.node [v0,v200,v2,v107,v3,v4] .nil .nil) (.node [v0,v200,v2,v3,v4,v177] .nil .nil)) (.node [v0,v631,v2,v3,v4,v5] (.node [v0,v200,v2,v3,v4,v99] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5rlllll : everyKey (rowOK 4 tree_4) tree_5rlllll = true := by decide +kernel
def tree_5rllllr : BinaryTree (List W) := (.node [v0,v632,v2,v3,v4,v99] (.node [v0,v23,v2,v192,v5,v104] (.node [v0,v149,v2,v3,v4,v5] (.node [v0,v149,v2,v3,v155,v5] (.node [v0,v149,v2,v107,v3,v4] .nil .nil) (.node [v0,v149,v2,v3,v4,v154] .nil .nil)) (.node [v0,v64,v1,v2,v3,v16] (.node [v0,v149,v2,v3,v4,v99] .nil .nil) (.node [v0,v23,v27,v3,v4,v5] .nil .nil))) (.node [v0,v23,v2,v3,v4,v99] (.node [v0,v23,v2,v3,v4,v110] (.node [v0,v23,v2,v107,v3,v4] .nil .nil) (.node [v0,v23,v2,v3,v4,v5] .nil .nil)) (.node [v0,v632,v2,v3,v4,v5] (.node [v0,v23,v2,v3,v99,v104] .nil .nil) .nil))) (.node [v0,v633,v2,v3,v4,v99] (.node [v0,v634,v2,v3,v4,v5] (.node [v0,v635,v2,v3,v4,v5] (.node [v0,v636,v2,v3,v4,v5] .nil .nil) (.node [v0,v635,v2,v3,v4,v99] .nil .nil)) (.node [v0,v637,v2,v3,v4,v5] (.node [v0,v638,v2,v3,v4,v5] .nil .nil) (.node [v0,v633,v2,v3,v4,v5] .nil .nil))) (.node [v0,v202,v2,v3,v4,v5] (.node [v0,v202,v1,v2,v3,v4] (.node [v0,v202,v639,v2,v3,v4] .nil .nil) (.node [v0,v202,v2,v3,v4] .nil .nil)) (.node [v0,v640,v1,v2,v107,v4] (.node [v0,v202,v2,v3,v4,v641] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5rllllr : everyKey (rowOK 4 tree_4) tree_5rllllr = true := by decide +kernel
def tree_5rllll : BinaryTree (List W) := .node [v0,v149,v41,v4,v5,v244] tree_5rlllll tree_5rllllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5rllll : everyKey (rowOK 4 tree_4) tree_5rllll = true := by
  change (_ && everyKey _ tree_5rlllll && everyKey _ tree_5rllllr) = true
  rw [ok_tree_5rlllll, ok_tree_5rllllr]
  decide +kernel
def tree_5rlllrl : BinaryTree (List W) := (.node [v0,v642,v1,v2,v107,v3] (.node [v0,v207,v220,v2,v3,v372] (.node [v0,v70,v2,v3,v5] (.node [v0,v70,v2,v3,v4,v5] (.node [v0,v70,v1,v2,v3,v5] .nil .nil) (.node [v0,v70,v2,v3,v372,v5] .nil .nil)) (.node [v0,v643,v1,v2,v3,v4] (.node [v0,v644,v1,v2,v3,v4] .nil .nil) (.node [v0,v645,v1,v2,v3,v4] .nil .nil))) (.node [v0,v78,v220,v1,v2,v3] (.node [v0,v207,v1,v2,v3,v4] (.node [v0,v207,v204,v1,v2,v3] .nil .nil) (.node [v0,v207,v1,v2,v3,v99] .nil .nil)) (.node [v0,v78,v1,v2,v3,v99] (.node [v0,v78,v1,v2,v3,v4] .nil .nil) (.node [v0,v646,v1,v2,v3,v99] .nil .nil)))) (.node [v0,v304,v1,v3,v4,v5] (.node [v0,v30,v2,v3,v4,v5] (.node [v0,v30,v32,v2,v4,v5] (.node [v0,v642,v1,v2,v3,v5] .nil .nil) (.node [v0,v30,v1,v2,v4,v5] .nil .nil)) (.node [v0,v30,v2,v4,v5,v226] (.node [v0,v30,v2,v4,v5] .nil .nil) (.node [v0,v647,v1,v2,v3,v4] .nil .nil))) (.node [v0,v29,v212,v3,v4,v5] (.node [v0,v648,v1,v2,v3,v5] (.node [v0,v649,v1,v2,v3,v99] .nil .nil) (.node [v0,v650,v1,v2,v3,v4] .nil .nil)) (.node [v0,v29,v2,v3,v4,v5] (.node [v0,v29,v1,v3,v4,v5] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5rlllrl : everyKey (rowOK 4 tree_4) tree_5rlllrl = true := by decide +kernel
def tree_5rlllrr : BinaryTree (List W) := (.node [v0,v212,v3,v4,v5,v106] (.node [v0,v212,v114,v3,v4,v5] (.node [v0,v651,v1,v2,v3,v5] (.node [v0,v652,v1,v2,v3,v4] (.node [v0,v29,v3,v4,v5] .nil .nil) (.node [v0,v653,v1,v2,v3,v99] .nil .nil)) (.node [v0,v212,v173,v3,v4,v5] (.node [v0,v212,v1,v2,v3,v16] .nil .nil) (.node [v0,v212,v168,v3,v4,v5] .nil .nil))) (.node [v0,v212,v119,v107,v3,v4] (.node [v0,v212,v654,v3,v4,v5] (.node [v0,v212,v655,v3,v4,v5] .nil .nil) (.node [v0,v212,v656,v3,v4,v5] .nil .nil)) (.node [v0,v212,v119,v3,v4,v99] (.node [v0,v212,v119,v3,v4,v5] .nil .nil) .nil))) (.node [v0,v657,v2,v3,v4,v5] (.node [v0,v658,v1,v2,v3,v99] (.node [v0,v166,v1,v2,v3,v16] (.node [v0,v659,v1,v2,v3,v4] .nil .nil) (.node [v0,v166,v241,v3,v4,v5] .nil .nil)) (.node [v0,v221,v2,v107,v3,v4] (.node [v0,v660,v1,v2,v3,v4] .nil .nil) (.node [v0,v221,v2,v3,v4,v5] .nil .nil))) (.node [v0,v223,v2,v3,v4,v5] (.node [v0,v223,v41,v3,v4,v5] (.node [v0,v223,v124,v3,v4,v5] .nil .nil) (.node [v0,v223,v2,v107,v3,v4] .nil .nil)) (.node [v0,v223,v114,v3,v4,v5] (.node [v0,v223,v2,v3,v4,v99] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5rlllrr : everyKey (rowOK 4 tree_4) tree_5rlllrr = true := by decide +kernel
def tree_5rlllr : BinaryTree (List W) := .node [v0,v29,v119,v3,v4,v5] tree_5rlllrl tree_5rlllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5rlllr : everyKey (rowOK 4 tree_4) tree_5rlllr = true := by
  change (_ && everyKey _ tree_5rlllrl && everyKey _ tree_5rlllrr) = true
  rw [ok_tree_5rlllrl, ok_tree_5rlllrr]
  decide +kernel
def tree_5rlll : BinaryTree (List W) := .node [v0,v70,v220,v2,v3,v5] tree_5rllll tree_5rlllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5rlll : everyKey (rowOK 4 tree_4) tree_5rlll = true := by
  change (_ && everyKey _ tree_5rllll && everyKey _ tree_5rlllr) = true
  rw [ok_tree_5rllll, ok_tree_5rlllr]
  decide +kernel
def tree_5rllrll : BinaryTree (List W) := (.node [v0,v32,v2,v3,v215,v5] (.node [v0,v661,v2,v3,v4,v662] (.node [v0,v663,v2,v3,v4,v5] (.node [v0,v664,v2,v3,v4,v5] (.node [v0,v223,v119,v3,v4,v5] .nil .nil) (.node [v0,v665,v2,v3,v4,v5] .nil .nil)) (.node [v0,v666,v1,v2,v3,v4] (.node [v0,v667,v2,v3,v4,v5] .nil .nil) (.node [v0,v661,v1,v2,v3,v16] .nil .nil))) (.node [v0,v32,v241,v3,v4,v5] (.node [v0,v32,v1,v2,v10,v4] (.node [v0,v32,v220,v2,v3,v99] .nil .nil) (.node [v0,v32,v1,v2,v3,v16] .nil .nil)) (.node [v0,v32,v187,v4,v5,v226] (.node [v0,v32,v187,v3,v4,v5] .nil .nil) (.node [v0,v32,v2,v107,v4,v226] .nil .nil)))) (.node [v0,v668,v1,v2,v3,v99] (.node [v0,v32,v2,v4,v5,v669] (.node [v0,v32,v2,v4,v213,v226] (.node [v0,v32,v2,v215,v5,v226] .nil .nil) (.node [v0,v32,v2,v4,v5,v575] .nil .nil)) (.node [v0,v32,v2,v4,v5,v226] (.node [v0,v32,v2,v4,v5,v225] .nil .nil) (.node [v0,v32,v2,v4,v99,v226] .nil .nil))) (.node [v0,v670,v1,v2,v3,v99] (.node [v0,v671,v1,v2,v3,v4] (.node [v0,v672,v1,v2,v107,v4] .nil .nil) (.node [v0,v673,v1,v2,v3,v4] .nil .nil)) (.node [v0,v220,v1,v2,v3,v209] (.node [v0,v220,v1,v2,v10,v3] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5rllrll : everyKey (rowOK 4 tree_4) tree_5rllrll = true := by decide +kernel
def tree_5rllrlr : BinaryTree (List W) := (.node [v0,v204,v1,v2,v3,v5] (.node [v0,v220,v2,v3,v372,v5] (.node [v0,v220,v2,v227,v3,v5] (.node [v0,v220,v1,v2,v3,v99] (.node [v0,v220,v1,v2,v3,v16] .nil .nil) (.node [v0,v220,v674,v2,v3,v5] .nil .nil)) (.node [v0,v220,v2,v3,v675,v5] (.node [v0,v220,v2,v107,v3,v372] .nil .nil) (.node [v0,v220,v2,v3,v263,v5] .nil .nil))) (.node [v0,v224,v1,v2,v3,v99] (.node [v0,v220,v2,v3,v372,v99] (.node [v0,v220,v2,v3,v372,v208] .nil .nil) (.node [v0,v676,v1,v2,v3,v99] .nil .nil)) (.node [v0,v204,v1,v2,v107,v3] (.node [v0,v373,v1,v2,v3,v5] .nil .nil) .nil))) (.node [v0,v232,v2,v3,v4,v5] (.node [v0,v677,v1,v2,v3,v4] (.node [v0,v678,v1,v2,v107,v3] (.node [v0,v204,v1,v2,v3,v99] .nil .nil) (.node [v0,v678,v1,v2,v3,v5] .nil .nil)) (.node [v0,v229,v2,v3,v4,v5] (.node [v0,v679,v1,v2,v3,v99] .nil .nil) (.node [v0,v680,v1,v2,v3,v99] .nil .nil))) (.node [v0,v639,v1,v2,v3,v16] (.node [v0,v681,v2,v3,v4,v5] (.node [v0,v682,v2,v3,v4,v5] .nil .nil) (.node [v0,v639,v1,v2,v3,v203] .nil .nil)) (.node [v0,v639,v2,v3,v4,v662] (.node [v0,v639,v423,v2,v3,v4] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5rllrlr : everyKey (rowOK 4 tree_4) tree_5rllrlr = true := by decide +kernel
def tree_5rllrl : BinaryTree (List W) := .node [v0,v220,v1,v2,v3,v112] tree_5rllrll tree_5rllrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5rllrl : everyKey (rowOK 4 tree_4) tree_5rllrl = true := by
  change (_ && everyKey _ tree_5rllrll && everyKey _ tree_5rllrlr) = true
  rw [ok_tree_5rllrll, ok_tree_5rllrlr]
  decide +kernel
def tree_5rllrrl : BinaryTree (List W) := (.node [v0,v683,v2,v3,v4,v5] (.node [v0,v36,v2,v3,v4,v5] (.node [v0,v6,v1,v2,v3,v16] (.node [v0,v684,v2,v3,v4,v5] (.node [v0,v334,v2,v3,v4,v641] .nil .nil) (.node [v0,v685,v2,v3,v4,v5] .nil .nil)) (.node [v0,v230,v2,v3,v4,v686] (.node [v0,v230,v2,v3,v4,v641] .nil .nil) (.node [v0,v687,v2,v3,v4,v5] .nil .nil))) (.node [v0,v174,v2,v3,v4,v177] (.node [v0,v174,v2,v107,v3,v4] (.node [v0,v174,v175,v3,v4,v5] .nil .nil) (.node [v0,v174,v2,v3,v170,v5] .nil .nil)) (.node [v0,v174,v2,v3,v4,v99] (.node [v0,v174,v2,v3,v4,v5] .nil .nil) .nil))) (.node [v0,v152,v2,v3,v4,v154] (.node [v0,v152,v41,v3,v4,v5] (.node [v0,v688,v2,v3,v4,v5] (.node [v0,v689,v2,v3,v4,v5] .nil .nil) (.node [v0,v35,v2,v3,v4,v5] .nil .nil)) (.node [v0,v152,v2,v107,v3,v4] (.node [v0,v152,v41,v4,v5,v244] .nil .nil) (.node [v0,v152,v2,v3,v155,v5] .nil .nil))) (.node [v0,v690,v2,v3,v4,v5] (.node [v0,v152,v2,v3,v4,v99] (.node [v0,v152,v2,v3,v4,v5] .nil .nil) (.node [v0,v691,v2,v3,v4,v5] .nil .nil)) (.node [v0,v692,v2,v3,v4,v5] (.node [v0,v693,v2,v3,v4,v5] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5rllrrl : everyKey (rowOK 4 tree_4) tree_5rllrrl = true := by decide +kernel
def tree_5rllrrr : BinaryTree (List W) := (.node [v0,v694,v2,v3,v4,v99] (.node [v0,v9,v2,v3,v5,v99] (.node [v0,v9,v2,v107,v3,v4] (.node [v0,v9,v2,v192,v3,v5] (.node [v0,v9,v27,v3,v4,v5] .nil .nil) (.node [v0,v9,v2,v192,v5,v104] .nil .nil)) (.node [v0,v9,v2,v3,v4,v5] (.node [v0,v9,v2,v3,v4,v110] .nil .nil) (.node [v0,v9,v2,v3,v4,v99] .nil .nil))) (.node [v0,v37,v2,v3,v4,v5] (.node [v0,v9,v2,v3,v99,v104] (.node [v0,v9,v2,v3,v99] .nil .nil) (.node [v0,v234,v2,v3,v4,v5] .nil .nil)) (.node [v0,v694,v2,v3,v4,v5] (.node [v0,v34,v2,v3,v4,v5] .nil .nil) .nil))) (.node [v0,v240,v2,v3,v4,v99] (.node [v0,v695,v2,v3,v4,v5] (.node [v0,v696,v2,v3,v4,v5] (.node [v0,v697,v2,v3,v4,v5] .nil .nil) (.node [v0,v696,v2,v3,v4,v99] .nil .nil)) (.node [v0,v698,v2,v3,v4,v5] (.node [v0,v699,v2,v3,v4,v5] .nil .nil) (.node [v0,v240,v2,v3,v4,v5] .nil .nil))) (.node [v0,v1,v700,v2,v3,v4] (.node [v0,v1,v206,v2,v3,v4] (.node [v0,v1,v701,v2,v3,v4] .nil .nil) (.node [v0,v1,v702,v2,v3,v4] .nil .nil)) (.node [v0,v1,v703,v2,v3,v5] (.node [v0,v1,v704,v2,v3,v99] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5rllrrr : everyKey (rowOK 4 tree_4) tree_5rllrrr = true := by decide +kernel
def tree_5rllrr : BinaryTree (List W) := .node [v0,v9,v1,v2,v3,v99] tree_5rllrrl tree_5rllrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5rllrr : everyKey (rowOK 4 tree_4) tree_5rllrr = true := by
  change (_ && everyKey _ tree_5rllrrl && everyKey _ tree_5rllrrr) = true
  rw [ok_tree_5rllrrl, ok_tree_5rllrrr]
  decide +kernel
def tree_5rllr : BinaryTree (List W) := .node [v0,v639,v2,v3,v4,v641] tree_5rllrl tree_5rllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5rllr : everyKey (rowOK 4 tree_4) tree_5rllr = true := by
  change (_ && everyKey _ tree_5rllrl && everyKey _ tree_5rllrr) = true
  rw [ok_tree_5rllrl, ok_tree_5rllrr]
  decide +kernel
def tree_5rll : BinaryTree (List W) := .node [v0,v223,v121,v3,v4,v5] tree_5rlll tree_5rllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5rll : everyKey (rowOK 4 tree_4) tree_5rll = true := by
  change (_ && everyKey _ tree_5rlll && everyKey _ tree_5rllr) = true
  rw [ok_tree_5rlll, ok_tree_5rllr]
  decide +kernel
def tree_5rlrlll : BinaryTree (List W) := (.node [v0,v1,v705,v2,v3,v4] (.node [v0,v1,v241,v3,v4,v5] (.node [v0,v1,v239,v107,v3,v4] (.node [v0,v1,v706,v2,v3,v99] (.node [v0,v1,v124,v2,v3,v16] .nil .nil) (.node [v0,v1,v707,v2,v3,v4] .nil .nil)) (.node [v0,v1,v708,v3,v4,v5] (.node [v0,v1,v239,v3,v4,v5] .nil .nil) (.node [v0,v1,v241,v107,v3,v4] .nil .nil))) (.node [v0,v1,v709,v3,v4,v5] (.node [v0,v1,v710,v3,v4,v5] (.node [v0,v1,v241,v3,v4,v99] .nil .nil) (.node [v0,v1,v711,v3,v4,v5] .nil .nil)) (.node [v0,v1,v358,v2,v3,v16] (.node [v0,v1,v712,v3,v4,v5] .nil .nil) (.node [v0,v1,v713,v2,v3,v4] .nil .nil)))) (.node [v0,v1,v714,v2,v3,v4] (.node [v0,v1,v84,v2,v3,v16] (.node [v0,v1,v341,v2,v3,v16] (.node [v0,v1,v483,v2,v3,v16] .nil .nil) (.node [v0,v1,v184,v2,v3,v4] .nil .nil)) (.node [v0,v1,v715,v2,v107,v4] (.node [v0,v1,v62,v2,v3,v16] .nil .nil) (.node [v0,v1,v69,v2,v3,v5] .nil .nil))) (.node [v0,v1,v307,v2,v3,v99] (.node [v0,v1,v716,v2,v3,v4] (.node [v0,v1,v717,v2,v3,v4] .nil .nil) (.node [v0,v1,v307,v2,v3,v4] .nil .nil)) (.node [v0,v1,v80,v2,v3,v99] (.node [v0,v1,v80,v2,v3,v4] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5rlrlll : everyKey (rowOK 4 tree_4) tree_5rlrlll = true := by decide +kernel
def tree_5rlrllr : BinaryTree (List W) := (.node [v0,v1,v718,v2,v3,v4] (.node [v0,v1,v719,v2,v3,v5] (.node [v0,v1,v720,v2,v3,v4] (.node [v0,v1,v721,v2,v3,v5] (.node [v0,v1,v721,v2,v107,v3] .nil .nil) (.node [v0,v1,v44,v2,v4,v5] .nil .nil)) (.node [v0,v1,v165,v3,v4,v5] (.node [v0,v1,v50,v3,v4,v5] .nil .nil) (.node [v0,v1,v722,v2,v3,v99] .nil .nil))) (.node [v0,v1,v723,v2,v3,v5] (.node [v0,v1,v724,v2,v3,v4] (.node [v0,v1,v725,v2,v3,v4] .nil .nil) (.node [v0,v1,v726,v2,v3,v99] .nil .nil)) (.node [v0,v1,v727,v2,v3,v4] (.node [v0,v1,v120,v2,v3,v16] .nil .nil) .nil))) (.node [v0,v1,v41,v155,v5,v244] (.node [v0,v1,v41,v2,v10,v4] (.node [v0,v1,v728,v3,v4,v729] (.node [v0,v1,v728,v2,v3,v16] .nil .nil) (.node [v0,v1,v41,v242,v3,v99] .nil .nil)) (.node [v0,v1,v41,v107,v4,v244] (.node [v0,v1,v41,v2,v3,v16] .nil .nil) (.node [v0,v1,v41,v3,v155,v5] .nil .nil))) (.node [v0,v1,v41,v4,v5,v246] (.node [v0,v1,v41,v4,v5,v574] (.node [v0,v1,v41,v4,v154,v244] .nil .nil) (.node [v0,v1,v41,v4,v5,v669] .nil .nil)) (.node [v0,v1,v41,v4,v99,v244] (.node [v0,v1,v41,v4,v5,v244] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5rlrllr : everyKey (rowOK 4 tree_4) tree_5rlrllr = true := by decide +kernel
def tree_5rlrll : BinaryTree (List W) := .node [v0,v1,v730,v2,v3,v99] tree_5rlrlll tree_5rlrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5rlrll : everyKey (rowOK 4 tree_4) tree_5rlrll = true := by
  change (_ && everyKey _ tree_5rlrlll && everyKey _ tree_5rlrllr) = true
  rw [ok_tree_5rlrlll, ok_tree_5rlrllr]
  decide +kernel
def tree_5rlrlrl : BinaryTree (List W) := (.node [v0,v1,v242,v3,v377,v5] (.node [v0,v1,v242,v2,v3,v16] (.node [v0,v1,v731,v2,v3,v99] (.node [v0,v1,v732,v2,v3,v4] (.node [v0,v1,v733,v2,v107,v4] .nil .nil) (.node [v0,v1,v734,v2,v3,v4] .nil .nil)) (.node [v0,v1,v242,v2,v3,v147] (.node [v0,v1,v242,v2,v10,v3] .nil .nil) (.node [v0,v1,v242,v2,v3,v112] .nil .nil))) (.node [v0,v1,v242,v107,v3,v377] (.node [v0,v1,v242,v735,v3,v5] (.node [v0,v1,v242,v2,v3,v99] .nil .nil) (.node [v0,v1,v242,v243,v3,v5] .nil .nil)) (.node [v0,v1,v242,v3,v262,v5] (.node [v0,v1,v242,v3,v736,v5] .nil .nil) .nil))) (.node [v0,v1,v142,v2,v3,v99] (.node [v0,v1,v248,v2,v3,v99] (.node [v0,v1,v242,v3,v377,v99] (.node [v0,v1,v242,v3,v377,v138] .nil .nil) (.node [v0,v1,v737,v2,v3,v99] .nil .nil)) (.node [v0,v1,v142,v2,v107,v3] (.node [v0,v1,v376,v2,v3,v5] .nil .nil) (.node [v0,v1,v142,v2,v3,v5] .nil .nil))) (.node [v0,v1,v738,v2,v3,v99] (.node [v0,v1,v739,v2,v3,v5] (.node [v0,v1,v739,v2,v107,v3] .nil .nil) (.node [v0,v1,v740,v2,v3,v4] .nil .nil)) (.node [v0,v1,v741,v2,v3,v99] (.node [v0,v1,v251,v3,v4,v5] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5rlrlrl : everyKey (rowOK 4 tree_4) tree_5rlrlrl = true := by decide +kernel
def tree_5rlrlrr : BinaryTree (List W) := (.node [v0,v1,v38,v3,v4,v5] (.node [v0,v1,v339,v3,v4,v548] (.node [v0,v1,v546,v2,v3,v16] (.node [v0,v1,v742,v3,v4,v5] (.node [v0,v1,v743,v3,v4,v5] .nil .nil) (.node [v0,v1,v546,v2,v3,v145] .nil .nil)) (.node [v0,v1,v546,v3,v4,v729] (.node [v0,v1,v546,v428,v3,v4] .nil .nil) (.node [v0,v1,v546,v3,v4,v548] .nil .nil))) (.node [v0,v1,v253,v3,v4,v548] (.node [v0,v1,v744,v3,v4,v5] (.node [v0,v1,v745,v3,v4,v5] .nil .nil) (.node [v0,v1,v39,v2,v3,v16] .nil .nil)) (.node [v0,v1,v746,v3,v4,v5] (.node [v0,v1,v253,v3,v4,v747] .nil .nil) .nil))) (.node [v0,v1,v748,v3,v4,v5] (.node [v0,v1,v175,v3,v4,v5] (.node [v0,v1,v175,v3,v170,v5] (.node [v0,v1,v175,v107,v3,v4] .nil .nil) (.node [v0,v1,v175,v3,v4,v177] .nil .nil)) (.node [v0,v1,v749,v3,v4,v5] (.node [v0,v1,v175,v3,v4,v99] .nil .nil) (.node [v0,v1,v750,v3,v4,v5] .nil .nil))) (.node [v0,v1,v187,v3,v4,v213] (.node [v0,v1,v187,v107,v3,v4] (.node [v0,v1,v43,v3,v4,v5] .nil .nil) (.node [v0,v1,v187,v3,v215,v5] .nil .nil)) (.node [v0,v1,v187,v3,v4,v99] (.node [v0,v1,v187,v3,v4,v5] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5rlrlrr : everyKey (rowOK 4 tree_4) tree_5rlrlrr = true := by decide +kernel
def tree_5rlrlr : BinaryTree (List W) := .node [v0,v1,v250,v3,v4,v5] tree_5rlrlrl tree_5rlrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5rlrlr : everyKey (rowOK 4 tree_4) tree_5rlrlr = true := by
  change (_ && everyKey _ tree_5rlrlrl && everyKey _ tree_5rlrlrr) = true
  rw [ok_tree_5rlrlrl, ok_tree_5rlrlrr]
  decide +kernel
def tree_5rlrl : BinaryTree (List W) := .node [v0,v1,v751,v2,v3,v99] tree_5rlrll tree_5rlrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5rlrl : everyKey (rowOK 4 tree_4) tree_5rlrl = true := by
  change (_ && everyKey _ tree_5rlrll && everyKey _ tree_5rlrlr) = true
  rw [ok_tree_5rlrll, ok_tree_5rlrlr]
  decide +kernel
def tree_5rlrrll : BinaryTree (List W) := (.node [v0,v1,v46,v3,v4,v5] (.node [v0,v1,v27,v3,v4,v110] (.node [v0,v1,v27,v2,v3,v99] (.node [v0,v1,v752,v3,v4,v5] (.node [v0,v1,v753,v3,v4,v5] .nil .nil) (.node [v0,v1,v754,v3,v4,v5] .nil .nil)) (.node [v0,v1,v27,v192,v5,v104] (.node [v0,v1,v27,v192,v3,v5] .nil .nil) (.node [v0,v1,v27,v107,v3,v4] .nil .nil))) (.node [v0,v1,v27,v3,v99] (.node [v0,v1,v27,v3,v4,v99] (.node [v0,v1,v27,v3,v4,v5] .nil .nil) (.node [v0,v1,v27,v3,v5,v99] .nil .nil)) (.node [v0,v1,v255,v3,v4,v5] (.node [v0,v1,v27,v3,v99,v104] .nil .nil) (.node [v0,v1,v47,v3,v4,v5] .nil .nil)))) (.node [v0,v1,v755,v3,v4,v5] (.node [v0,v1,v756,v3,v4,v5] (.node [v0,v1,v757,v3,v4,v99] (.node [v0,v1,v757,v3,v4,v5] .nil .nil) (.node [v0,v1,v758,v3,v4,v5] .nil .nil)) (.node [v0,v1,v759,v3,v4,v5] (.node [v0,v1,v756,v3,v4,v99] .nil .nil) (.node [v0,v1,v760,v3,v4,v5] .nil .nil))) (.node [v0,v1,v2,v146,v3,v4] (.node [v0,v1,v254,v3,v4,v99] (.node [v0,v1,v254,v3,v4,v5] .nil .nil) (.node [v0,v1,v2,v761,v3,v4] .nil .nil)) (.node [v0,v1,v2,v762,v3,v4] (.node [v0,v1,v2,v763,v3,v4] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5rlrrll : everyKey (rowOK 4 tree_4) tree_5rlrrll = true := by decide +kernel
def tree_5rlrrlr : BinaryTree (List W) := (.node [v0,v1,v2,v764,v3,v16] (.node [v0,v1,v2,v765,v3,v5] (.node [v0,v1,v2,v766,v3,v5] (.node [v0,v1,v2,v767,v3,v4] (.node [v0,v1,v2,v768,v3,v5] .nil .nil) (.node [v0,v1,v2,v769,v3,v99] .nil .nil)) (.node [v0,v1,v2,v770,v3,v4] (.node [v0,v1,v2,v771,v3,v4] .nil .nil) (.node [v0,v1,v2,v772,v3,v99] .nil .nil))) (.node [v0,v1,v2,v773,v3,v5] (.node [v0,v1,v2,v774,v3,v4] (.node [v0,v1,v2,v121,v3,v16] .nil .nil) (.node [v0,v1,v2,v775,v3,v99] .nil .nil)) (.node [v0,v1,v2,v776,v3,v4] (.node [v0,v1,v2,v119,v3,v16] .nil .nil) .nil))) (.node [v0,v1,v2,v192,v5,v104] (.node [v0,v1,v2,v192,v110,v104] (.node [v0,v1,v2,v192,v3,v261] (.node [v0,v1,v2,v192,v107,v104] .nil .nil) (.node [v0,v1,v2,v192,v3,v16] .nil .nil)) (.node [v0,v1,v2,v192,v5,v225] (.node [v0,v1,v2,v192,v5,v181] .nil .nil) (.node [v0,v1,v2,v192,v5,v246] .nil .nil))) (.node [v0,v1,v2,v260,v3,v4] (.node [v0,v1,v2,v192,v99,v104] (.node [v0,v1,v2,v192,v112,v104] .nil .nil) (.node [v0,v1,v2,v260,v107,v4] .nil .nil)) (.node [v0,v1,v2,v777,v3,v4] (.node [v0,v1,v2,v260,v4,v104] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5rlrrlr : everyKey (rowOK 4 tree_4) tree_5rlrrlr = true := by decide +kernel
def tree_5rlrrl : BinaryTree (List W) := .node [v0,v1,v2,v778,v3,v99] tree_5rlrrll tree_5rlrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5rlrrl : everyKey (rowOK 4 tree_4) tree_5rlrrl = true := by
  change (_ && everyKey _ tree_5rlrrll && everyKey _ tree_5rlrrlr) = true
  rw [ok_tree_5rlrrll, ok_tree_5rlrrlr]
  decide +kernel
def tree_5rlrrrl : BinaryTree (List W) := (.node [v0,v1,v2,v107,v3,v779] (.node [v0,v1,v2,v107,v3,v145] (.node [v0,v1,v2,v107,v3,v215] (.node [v0,v1,v2,v243,v107,v4] (.node [v0,v1,v2,v227,v107,v4] .nil .nil) (.node [v0,v1,v2,v107,v3,v170] .nil .nil)) (.node [v0,v1,v2,v107,v3,v4] (.node [v0,v1,v2,v107,v3,v155] .nil .nil) (.node [v0,v1,v2,v107,v3,v780] .nil .nil))) (.node [v0,v1,v2,v107,v3,v179] (.node [v0,v1,v2,v107,v3,v203] (.node [v0,v1,v2,v107,v3,v781] .nil .nil) (.node [v0,v1,v2,v107,v3,v782] .nil .nil)) (.node [v0,v1,v2,v107,v3,v783] (.node [v0,v1,v2,v107,v3,v784] .nil .nil) .nil))) (.node [v0,v1,v2,v107,v4,v785] (.node [v0,v1,v2,v107,v786,v4] (.node [v0,v1,v2,v107,v284,v4] (.node [v0,v1,v2,v107,v3,v16] .nil .nil) (.node [v0,v1,v2,v107,v787,v4] .nil .nil)) (.node [v0,v1,v2,v107,v4,v788] (.node [v0,v1,v2,v107,v789,v4] .nil .nil) (.node [v0,v1,v2,v107,v4,v790] .nil .nil))) (.node [v0,v1,v2,v791,v3,v4] (.node [v0,v1,v2,v107,v4,v487] (.node [v0,v1,v2,v107,v4,v792] .nil .nil) (.node [v0,v1,v2,v107,v487,v16] .nil .nil)) (.node [v0,v1,v2,v793,v3,v4] (.node [v0,v1,v2,v794,v3,v4] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5rlrrrl : everyKey (rowOK 4 tree_4) tree_5rlrrrl = true := by decide +kernel
def tree_5rlrrrr : BinaryTree (List W) := (.node [v0,v1,v2,v795,v3,v4] (.node [v0,v1,v2,v796,v3,v4] (.node [v0,v1,v2,v111,v3,v99] (.node [v0,v1,v2,v797,v3,v4] (.node [v0,v1,v2,v798,v3,v4] .nil .nil) (.node [v0,v1,v2,v111,v3,v4] .nil .nil)) (.node [v0,v1,v2,v799,v3,v4] (.node [v0,v1,v2,v800,v3,v4] .nil .nil) (.node [v0,v1,v2,v801,v3,v4] .nil .nil))) (.node [v0,v1,v2,v802,v3,v4] (.node [v0,v1,v2,v148,v3,v4] (.node [v0,v1,v2,v803,v3,v4] .nil .nil) (.node [v0,v1,v2,v148,v3,v12] .nil .nil)) (.node [v0,v1,v2,v804,v3,v4] (.node [v0,v1,v2,v805,v3,v4] .nil .nil) .nil))) (.node [v0,v1,v2,v806,v3,v4] (.node [v0,v1,v2,v807,v3,v4] (.node [v0,v1,v2,v214,v3,v4] (.node [v0,v1,v2,v808,v3,v4] .nil .nil) (.node [v0,v1,v2,v214,v3,v31] .nil .nil)) (.node [v0,v1,v2,v809,v3,v4] (.node [v0,v1,v2,v810,v3,v4] .nil .nil) (.node [v0,v1,v2,v811,v3,v4] .nil .nil))) (.node [v0,v1,v2,v812,v3,v4] (.node [v0,v1,v2,v315,v3,v51] (.node [v0,v1,v2,v315,v3,v4] .nil .nil) (.node [v0,v1,v2,v813,v3,v4] .nil .nil)) (.node [v0,v1,v2,v814,v3,v4] (.node [v0,v1,v2,v815,v3,v4] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5rlrrrr : everyKey (rowOK 4 tree_4) tree_5rlrrrr = true := by decide +kernel
def tree_5rlrrr : BinaryTree (List W) := .node [v0,v1,v2,v816,v3,v4] tree_5rlrrrl tree_5rlrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5rlrrr : everyKey (rowOK 4 tree_4) tree_5rlrrr = true := by
  change (_ && everyKey _ tree_5rlrrrl && everyKey _ tree_5rlrrrr) = true
  rw [ok_tree_5rlrrrl, ok_tree_5rlrrrr]
  decide +kernel
def tree_5rlrr : BinaryTree (List W) := .node [v0,v1,v2,v180,v107,v4] tree_5rlrrl tree_5rlrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5rlrr : everyKey (rowOK 4 tree_4) tree_5rlrr = true := by
  change (_ && everyKey _ tree_5rlrrl && everyKey _ tree_5rlrrr) = true
  rw [ok_tree_5rlrrl, ok_tree_5rlrrr]
  decide +kernel
def tree_5rlr : BinaryTree (List W) := .node [v0,v1,v817,v3,v4,v5] tree_5rlrl tree_5rlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5rlr : everyKey (rowOK 4 tree_4) tree_5rlr = true := by
  change (_ && everyKey _ tree_5rlrl && everyKey _ tree_5rlrr) = true
  rw [ok_tree_5rlrl, ok_tree_5rlrr]
  decide +kernel
def tree_5rl : BinaryTree (List W) := .node [v0,v1,v818,v2,v3,v4] tree_5rll tree_5rlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5rl : everyKey (rowOK 4 tree_4) tree_5rl = true := by
  change (_ && everyKey _ tree_5rll && everyKey _ tree_5rlr) = true
  rw [ok_tree_5rll, ok_tree_5rlr]
  decide +kernel
def tree_5rrllll : BinaryTree (List W) := (.node [v0,v1,v2,v10,v104] (.node [v0,v1,v2,v10,v3,v4] (.node [v0,v1,v2,v819,v3,v4] (.node [v0,v1,v2,v820,v3,v4] (.node [v0,v1,v2,v821,v3,v4] .nil .nil) (.node [v0,v1,v2,v822,v3,v4] .nil .nil)) (.node [v0,v1,v2,v823,v3,v4] (.node [v0,v1,v2,v824,v3,v4] .nil .nil) (.node [v0,v1,v2,v825,v3,v4] .nil .nil))) (.node [v0,v1,v2,v10,v4,v104] (.node [v0,v1,v2,v10,v3,v104] (.node [v0,v1,v2,v10,v3,v16] .nil .nil) (.node [v0,v1,v2,v10,v4,v487] .nil .nil)) (.node [v0,v1,v2,v10,v5,v104] (.node [v0,v1,v2,v10,v4,v826] .nil .nil) (.node [v0,v1,v2,v10,v99,v104] .nil .nil)))) (.node [v0,v1,v2,v20,v4,v99] (.node [v0,v1,v2,v827,v3,v4] (.node [v0,v1,v2,v266,v3,v99] (.node [v0,v1,v2,v266,v3,v4] .nil .nil) (.node [v0,v1,v2,v828,v3,v4] .nil .nil)) (.node [v0,v1,v2,v15,v4,v5] (.node [v0,v1,v2,v829,v3,v4] .nil .nil) (.node [v0,v1,v2,v20,v4,v5] .nil .nil))) (.node [v0,v1,v2,v40,v4,v99] (.node [v0,v1,v2,v7,v4,v99] (.node [v0,v1,v2,v7,v4,v5] .nil .nil) (.node [v0,v1,v2,v40,v4,v5] .nil .nil)) (.node [v0,v1,v2,v3,v459,v99] (.node [v0,v1,v2,v3,v3,v16] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5rrllll : everyKey (rowOK 4 tree_4) tree_5rrllll = true := by decide +kernel
def tree_5rrlllr : BinaryTree (List W) := (.node [v0,v1,v2,v3,v830,v5] (.node [v0,v1,v2,v3,v831,v99] (.node [v0,v1,v2,v3,v474,v16] (.node [v0,v1,v2,v3,v284,v99] (.node [v0,v1,v2,v3,v462,v99] .nil .nil) (.node [v0,v1,v2,v3,v832,v4] .nil .nil)) (.node [v0,v1,v2,v3,v331,v99] (.node [v0,v1,v2,v3,v474,v99] .nil .nil) (.node [v0,v1,v2,v3,v833,v99] .nil .nil))) (.node [v0,v1,v2,v3,v834,v99] (.node [v0,v1,v2,v3,v835,v99] (.node [v0,v1,v2,v3,v836,v99] .nil .nil) (.node [v0,v1,v2,v3,v837,v99] .nil .nil)) (.node [v0,v1,v2,v3,v838,v4] (.node [v0,v1,v2,v3,v839,v99] .nil .nil) .nil))) (.node [v0,v1,v2,v3,v840,v5] (.node [v0,v1,v2,v3,v170,v841] (.node [v0,v1,v2,v3,v170,v177] (.node [v0,v1,v2,v3,v842,v5] .nil .nil) (.node [v0,v1,v2,v3,v170,v5] .nil .nil)) (.node [v0,v1,v2,v3,v843,v5] (.node [v0,v1,v2,v3,v170,v99] .nil .nil) (.node [v0,v1,v2,v3,v844,v5] .nil .nil))) (.node [v0,v1,v2,v3,v215,v845] (.node [v0,v1,v2,v3,v215,v213] (.node [v0,v1,v2,v3,v846,v5] .nil .nil) (.node [v0,v1,v2,v3,v215,v5] .nil .nil)) (.node [v0,v1,v2,v3,v847,v5] (.node [v0,v1,v2,v3,v215,v99] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5rrlllr : everyKey (rowOK 4 tree_4) tree_5rrlllr = true := by decide +kernel
def tree_5rrlll : BinaryTree (List W) := .node [v0,v1,v2,v3,v458,v99] tree_5rrllll tree_5rrlllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5rrlll : everyKey (rowOK 4 tree_4) tree_5rrlll = true := by
  change (_ && everyKey _ tree_5rrllll && everyKey _ tree_5rrlllr) = true
  rw [ok_tree_5rrllll, ok_tree_5rrlllr]
  decide +kernel
def tree_5rrllrl : BinaryTree (List W) := (.node [v0,v1,v2,v3,v4,v848] (.node [v0,v1,v2,v3,v849,v5] (.node [v0,v1,v2,v3,v155,v154] (.node [v0,v1,v2,v3,v850,v5] (.node [v0,v1,v2,v3,v851,v5] .nil .nil) (.node [v0,v1,v2,v3,v852,v5] .nil .nil)) (.node [v0,v1,v2,v3,v155,v853] (.node [v0,v1,v2,v3,v155,v5] .nil .nil) (.node [v0,v1,v2,v3,v155,v99] .nil .nil))) (.node [v0,v1,v2,v3,v854,v5] (.node [v0,v1,v2,v3,v855,v5] (.node [v0,v1,v2,v3,v856,v5] .nil .nil) (.node [v0,v1,v2,v3,v857,v5] .nil .nil)) (.node [v0,v1,v2,v3,v858,v5] (.node [v0,v1,v2,v3,v859,v5] .nil .nil) (.node [v0,v1,v2,v3,v860,v5] .nil .nil)))) (.node [v0,v1,v2,v3,v4,v177] (.node [v0,v1,v2,v3,v4,v861] (.node [v0,v1,v2,v3,v4,v862] (.node [v0,v1,v2,v3,v4,v863] .nil .nil) (.node [v0,v1,v2,v3,v4,v261] .nil .nil)) (.node [v0,v1,v2,v3,v4,v864] (.node [v0,v1,v2,v3,v4,v865] .nil .nil) (.node [v0,v1,v2,v3,v4,v866] .nil .nil))) (.node [v0,v1,v2,v3,v4,v867] (.node [v0,v1,v2,v3,v4,v868] (.node [v0,v1,v2,v3,v4,v869] .nil .nil) (.node [v0,v1,v2,v3,v4,v870] .nil .nil)) (.node [v0,v1,v2,v3,v4,v213] (.node [v0,v1,v2,v3,v4,v871] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5rrllrl : everyKey (rowOK 4 tree_4) tree_5rrllrl = true := by decide +kernel
def tree_5rrllrr : BinaryTree (List W) := (.node [v0,v1,v2,v3,v4,v872] (.node [v0,v1,v2,v3,v4,v873] (.node [v0,v1,v2,v3,v4,v874] (.node [v0,v1,v2,v3,v4,v875] (.node [v0,v1,v2,v3,v4,v876] .nil .nil) (.node [v0,v1,v2,v3,v4,v877] .nil .nil)) (.node [v0,v1,v2,v3,v4,v154] (.node [v0,v1,v2,v3,v4,v878] .nil .nil) (.node [v0,v1,v2,v3,v4,v879] .nil .nil))) (.node [v0,v1,v2,v3,v4,v110] (.node [v0,v1,v2,v3,v4,v880] (.node [v0,v1,v2,v3,v4,v881] .nil .nil) (.node [v0,v1,v2,v3,v4,v882] .nil .nil)) (.node [v0,v1,v2,v3,v4,v883] (.node [v0,v1,v2,v3,v4,v884] .nil .nil) .nil))) (.node [v0,v1,v2,v3,v4,v885] (.node [v0,v1,v2,v3,v4,v5] (.node [v0,v1,v2,v3,v4,v886] (.node [v0,v1,v2,v3,v4,v887] .nil .nil) (.node [v0,v1,v2,v3,v4,v888] .nil .nil)) (.node [v0,v1,v2,v3,v4,v889] (.node [v0,v1,v2,v3,v4,v890] .nil .nil) (.node [v0,v1,v2,v3,v4,v891] .nil .nil))) (.node [v0,v1,v2,v3,v4,v892] (.node [v0,v1,v2,v3,v4,v893] (.node [v0,v1,v2,v3,v4,v894] .nil .nil) (.node [v0,v1,v2,v3,v4,v895] .nil .nil)) (.node [v0,v1,v2,v3,v4,v896] (.node [v0,v1,v2,v3,v4,v897] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5rrllrr : everyKey (rowOK 4 tree_4) tree_5rrllrr = true := by decide +kernel
def tree_5rrllr : BinaryTree (List W) := .node [v0,v1,v2,v3,v4,v898] tree_5rrllrl tree_5rrllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5rrllr : everyKey (rowOK 4 tree_4) tree_5rrllr = true := by
  change (_ && everyKey _ tree_5rrllrl && everyKey _ tree_5rrllrr) = true
  rw [ok_tree_5rrllrl, ok_tree_5rrllrr]
  decide +kernel
def tree_5rrll : BinaryTree (List W) := .node [v0,v1,v2,v3,v899,v5] tree_5rrlll tree_5rrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5rrll : everyKey (rowOK 4 tree_4) tree_5rrll = true := by
  change (_ && everyKey _ tree_5rrlll && everyKey _ tree_5rrllr) = true
  rw [ok_tree_5rrlll, ok_tree_5rrllr]
  decide +kernel
def tree_5rrlrll : BinaryTree (List W) := (.node [v0,v1,v2,v3,v4,v109] (.node [v0,v1,v2,v3,v4,v900] (.node [v0,v1,v2,v3,v4,v901] (.node [v0,v1,v2,v3,v4,v902] (.node [v0,v1,v2,v3,v4,v903] .nil .nil) (.node [v0,v1,v2,v3,v4,v904] .nil .nil)) (.node [v0,v1,v2,v3,v4,v905] (.node [v0,v1,v2,v3,v4,v906] .nil .nil) (.node [v0,v1,v2,v3,v4,v316] .nil .nil))) (.node [v0,v1,v2,v3,v4,v907] (.node [v0,v1,v2,v3,v4,v216] (.node [v0,v1,v2,v3,v4,v908] .nil .nil) (.node [v0,v1,v2,v3,v4,v909] .nil .nil)) (.node [v0,v1,v2,v3,v4,v910] (.node [v0,v1,v2,v3,v4,v153] .nil .nil) (.node [v0,v1,v2,v3,v4,v911] .nil .nil)))) (.node [v0,v1,v2,v3,v4,v912] (.node [v0,v1,v2,v3,v4,v913] (.node [v0,v1,v2,v3,v4,v914] (.node [v0,v1,v2,v3,v4,v915] .nil .nil) (.node [v0,v1,v2,v3,v4,v916] .nil .nil)) (.node [v0,v1,v2,v3,v4,v917] (.node [v0,v1,v2,v3,v4,v918] .nil .nil) (.node [v0,v1,v2,v3,v4,v919] .nil .nil))) (.node [v0,v1,v2,v3,v4,v920] (.node [v0,v1,v2,v3,v4,v921] (.node [v0,v1,v2,v3,v4,v147] .nil .nil) (.node [v0,v1,v2,v3,v4,v922] .nil .nil)) (.node [v0,v1,v2,v3,v4,v923] (.node [v0,v1,v2,v3,v4,v924] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5rrlrll : everyKey (rowOK 4 tree_4) tree_5rrlrll = true := by decide +kernel
def tree_5rrlrlr : BinaryTree (List W) := (.node [v0,v1,v2,v3,v4,v208] (.node [v0,v1,v2,v3,v4,v925] (.node [v0,v1,v2,v3,v4,v926] (.node [v0,v1,v2,v3,v4,v927] (.node [v0,v1,v2,v3,v4,v312] .nil .nil) (.node [v0,v1,v2,v3,v4,v928] .nil .nil)) (.node [v0,v1,v2,v3,v4,v929] (.node [v0,v1,v2,v3,v4,v930] .nil .nil) (.node [v0,v1,v2,v3,v4,v209] .nil .nil))) (.node [v0,v1,v2,v3,v4,v931] (.node [v0,v1,v2,v3,v4,v932] (.node [v0,v1,v2,v3,v4,v933] .nil .nil) (.node [v0,v1,v2,v3,v4,v934] .nil .nil)) (.node [v0,v1,v2,v3,v4,v935] (.node [v0,v1,v2,v3,v4,v936] .nil .nil) .nil))) (.node [v0,v1,v2,v3,v4,v937] (.node [v0,v1,v2,v3,v4,v938] (.node [v0,v1,v2,v3,v4,v939] (.node [v0,v1,v2,v3,v4,v940] .nil .nil) (.node [v0,v1,v2,v3,v4,v941] .nil .nil)) (.node [v0,v1,v2,v3,v4,v311] (.node [v0,v1,v2,v3,v4,v942] .nil .nil) (.node [v0,v1,v2,v3,v4,v943] .nil .nil))) (.node [v0,v1,v2,v3,v4,v944] (.node [v0,v1,v2,v3,v4,v945] (.node [v0,v1,v2,v3,v4,v946] .nil .nil) (.node [v0,v1,v2,v3,v4,v947] .nil .nil)) (.node [v0,v1,v2,v3,v4,v948] (.node [v0,v1,v2,v3,v4,v138] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5rrlrlr : everyKey (rowOK 4 tree_4) tree_5rrlrlr = true := by decide +kernel
def tree_5rrlrl : BinaryTree (List W) := .node [v0,v1,v2,v3,v4,v949] tree_5rrlrll tree_5rrlrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5rrlrl : everyKey (rowOK 4 tree_4) tree_5rrlrl = true := by
  change (_ && everyKey _ tree_5rrlrll && everyKey _ tree_5rrlrlr) = true
  rw [ok_tree_5rrlrll, ok_tree_5rrlrlr]
  decide +kernel
def tree_5rrlrrl : BinaryTree (List W) := (.node [v0,v1,v2,v3,v4,v31] (.node [v0,v1,v2,v3,v4,v950] (.node [v0,v1,v2,v3,v4,v951] (.node [v0,v1,v2,v3,v4,v952] (.node [v0,v1,v2,v3,v4,v953] .nil .nil) (.node [v0,v1,v2,v3,v4,v954] .nil .nil)) (.node [v0,v1,v2,v3,v4,v112] (.node [v0,v1,v2,v3,v4,v955] .nil .nil) (.node [v0,v1,v2,v3,v4,v956] .nil .nil))) (.node [v0,v1,v2,v3,v4,v245] (.node [v0,v1,v2,v3,v4,v176] (.node [v0,v1,v2,v3,v4,v957] .nil .nil) (.node [v0,v1,v2,v3,v4,v219] .nil .nil)) (.node [v0,v1,v2,v3,v4,v12] (.node [v0,v1,v2,v3,v4,v16] .nil .nil) .nil))) (.node [v0,v1,v2,v3,v4,v99] (.node [v0,v1,v2,v3,v4,v958] (.node [v0,v1,v2,v3,v4,v959] (.node [v0,v1,v2,v3,v4,v51] .nil .nil) (.node [v0,v1,v2,v3,v4,v960] .nil .nil)) (.node [v0,v1,v2,v3,v4,v845] (.node [v0,v1,v2,v3,v4,v841] .nil .nil) (.node [v0,v1,v2,v3,v4,v853] .nil .nil))) (.node [v0,v1,v2,v3,v961,v5] (.node [v0,v1,v2,v3,v962,v5] (.node [v0,v1,v2,v3,v4,v963] .nil .nil) (.node [v0,v1,v2,v3,v964,v5] .nil .nil)) (.node [v0,v1,v2,v3,v965,v5] (.node [v0,v1,v2,v3,v966,v5] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5rrlrrl : everyKey (rowOK 4 tree_4) tree_5rrlrrl = true := by decide +kernel
def tree_5rrlrrr : BinaryTree (List W) := (.node [v0,v1,v2,v3,v780,v5] (.node [v0,v1,v2,v3,v967,v5] (.node [v0,v1,v2,v3,v968,v99] (.node [v0,v1,v2,v3,v969,v5] (.node [v0,v1,v2,v3,v970,v5] .nil .nil) (.node [v0,v1,v2,v3,v971,v5] .nil .nil)) (.node [v0,v1,v2,v3,v972,v99] (.node [v0,v1,v2,v3,v973,v99] .nil .nil) (.node [v0,v1,v2,v3,v261,v99] .nil .nil))) (.node [v0,v1,v2,v3,v974,v5] (.node [v0,v1,v2,v3,v975,v5] (.node [v0,v1,v2,v3,v976,v5] .nil .nil) (.node [v0,v1,v2,v3,v977,v99] .nil .nil)) (.node [v0,v1,v2,v3,v978,v99] (.node [v0,v1,v2,v3,v979,v99] .nil .nil) .nil))) (.node [v0,v1,v2,v3,v980,v99] (.node [v0,v1,v2,v3,v981,v5] (.node [v0,v1,v2,v3,v145,v99] (.node [v0,v1,v2,v3,v145,v5] .nil .nil) (.node [v0,v1,v2,v3,v530,v99] .nil .nil)) (.node [v0,v1,v2,v3,v982,v99] (.node [v0,v1,v2,v3,v983,v5] .nil .nil) (.node [v0,v1,v2,v3,v984,v5] .nil .nil))) (.node [v0,v1,v2,v3,v203,v99] (.node [v0,v1,v2,v3,v781,v5] (.node [v0,v1,v2,v3,v985,v99] .nil .nil) (.node [v0,v1,v2,v3,v203,v5] .nil .nil)) (.node [v0,v1,v2,v3,v986,v5] (.node [v0,v1,v2,v3,v624,v99] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5rrlrrr : everyKey (rowOK 4 tree_4) tree_5rrlrrr = true := by decide +kernel
def tree_5rrlrr : BinaryTree (List W) := .node [v0,v1,v2,v3,v987,v5] tree_5rrlrrl tree_5rrlrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5rrlrr : everyKey (rowOK 4 tree_4) tree_5rrlrr = true := by
  change (_ && everyKey _ tree_5rrlrrl && everyKey _ tree_5rrlrrr) = true
  rw [ok_tree_5rrlrrl, ok_tree_5rrlrrr]
  decide +kernel
def tree_5rrlr : BinaryTree (List W) := .node [v0,v1,v2,v3,v4,v988] tree_5rrlrl tree_5rrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5rrlr : everyKey (rowOK 4 tree_4) tree_5rrlr = true := by
  change (_ && everyKey _ tree_5rrlrl && everyKey _ tree_5rrlrr) = true
  rw [ok_tree_5rrlrl, ok_tree_5rrlrr]
  decide +kernel
def tree_5rrl : BinaryTree (List W) := .node [v0,v1,v2,v3,v4,v989] tree_5rrll tree_5rrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5rrl : everyKey (rowOK 4 tree_4) tree_5rrl = true := by
  change (_ && everyKey _ tree_5rrll && everyKey _ tree_5rrlr) = true
  rw [ok_tree_5rrll, ok_tree_5rrlr]
  decide +kernel
def tree_5rrrlll : BinaryTree (List W) := (.node [v0,v1,v2,v3,v372,v16] (.node [v0,v1,v2,v3,v990,v99] (.node [v0,v1,v2,v3,v991,v99] (.node [v0,v1,v2,v3,v992,v5] (.node [v0,v1,v2,v3,v993,v99] .nil .nil) (.node [v0,v1,v2,v3,v994,v99] .nil .nil)) (.node [v0,v1,v2,v3,v179,v5] (.node [v0,v1,v2,v3,v782,v5] .nil .nil) (.node [v0,v1,v2,v3,v179,v99] .nil .nil))) (.node [v0,v1,v2,v3,v258,v99] (.node [v0,v1,v2,v3,v995,v5] (.node [v0,v1,v2,v3,v996,v5] .nil .nil) (.node [v0,v1,v2,v3,v784,v5] .nil .nil)) (.node [v0,v1,v2,v3,v783,v5] (.node [v0,v1,v2,v3,v371,v16] .nil .nil) (.node [v0,v1,v2,v3,v263,v99] .nil .nil)))) (.node [v0,v1,v2,v3,v5,v31] (.node [v0,v1,v2,v3,v110,v16] (.node [v0,v1,v2,v3,v262,v99] (.node [v0,v1,v2,v3,v779,v5] .nil .nil) (.node [v0,v1,v2,v3,v377,v16] .nil .nil)) (.node [v0,v1,v2,v3,v5,v16] (.node [v0,v1,v2,v3,v110,v99] .nil .nil) (.node [v0,v1,v2,v3,v5,v12] .nil .nil))) (.node [v0,v1,v2,v3,v662,v16] (.node [v0,v1,v2,v3,v572,v16] (.node [v0,v1,v2,v3,v5,v51] .nil .nil) (.node [v0,v1,v2,v3,v590,v16] .nil .nil)) (.node [v0,v1,v2,v3,v729,v16] (.node [v0,v1,v2,v3,v641,v16] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5rrrlll : everyKey (rowOK 4 tree_4) tree_5rrrlll = true := by decide +kernel
def tree_5rrrllr : BinaryTree (List W) := (.node [v0,v1,v2,v3,v31] (.node [v0,v1,v2,v3,v16,v226] (.node [v0,v1,v2,v3,v16] (.node [v0,v1,v2,v3,v792,v99] (.node [v0,v1,v2,v3,v112,v104] .nil .nil) (.node [v0,v1,v2,v3,v487,v16] .nil .nil)) (.node [v0,v1,v2,v3,v16,v99] (.node [v0,v1,v2,v3,v16,v16] .nil .nil) (.node [v0,v1,v2,v3,v16,v169] .nil .nil))) (.node [v0,v1,v2,v3,v16,v233] (.node [v0,v1,v2,v3,v16,v104] (.node [v0,v1,v2,v3,v16,v244] .nil .nil) (.node [v0,v1,v2,v3,v16,v191] .nil .nil)) (.node [v0,v1,v2,v3,v12] (.node [v0,v1,v2,v3,v16,v249] .nil .nil) .nil))) (.node [v0,v1,v286,v3,v4,v5] (.node [v0,v1,v2,v3,v99,v246] (.node [v0,v1,v2,v3,v99,v181] (.node [v0,v1,v2,v3,v51] .nil .nil) (.node [v0,v1,v2,v3,v99,v225] .nil .nil)) (.node [v0,v1,v997,v3,v4,v5] (.node [v0,v1,v2,v3,v99,v104] .nil .nil) (.node [v0,v1,v998,v3,v4,v5] .nil .nil))) (.node [v0,v1,v999,v3,v4,v5] (.node [v0,v1,v1000,v3,v4,v5] (.node [v0,v1,v1001,v3,v4,v5] .nil .nil) (.node [v0,v1,v1002,v3,v4,v5] .nil .nil)) (.node [v0,v1,v1003,v3,v4,v5] (.node [v0,v1,v1004,v3,v4,v5] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5rrrllr : everyKey (rowOK 4 tree_4) tree_5rrrllr = true := by decide +kernel
def tree_5rrrll : BinaryTree (List W) := .node [v0,v1,v2,v3,v548,v16] tree_5rrrlll tree_5rrrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5rrrll : everyKey (rowOK 4 tree_4) tree_5rrrll = true := by
  change (_ && everyKey _ tree_5rrrlll && everyKey _ tree_5rrrllr) = true
  rw [ok_tree_5rrrlll, ok_tree_5rrrllr]
  decide +kernel
def tree_5rrrlrl : BinaryTree (List W) := (.node [v0,v1,v114,v107,v3,v4] (.node [v0,v1,v1005,v3,v4,v5] (.node [v0,v1,v457,v3,v4,v5] (.node [v0,v1,v1006,v3,v4,v5] (.node [v0,v1,v1007,v3,v4,v5] .nil .nil) (.node [v0,v1,v1008,v3,v4,v5] .nil .nil)) (.node [v0,v1,v1009,v3,v4,v5] (.node [v0,v1,v448,v3,v4,v5] .nil .nil) (.node [v0,v1,v1010,v3,v4,v5] .nil .nil))) (.node [v0,v1,v1011,v3,v4,v5] (.node [v0,v1,v134,v3,v4,v5] (.node [v0,v1,v134,v107,v3,v4] .nil .nil) (.node [v0,v1,v134,v3,v4,v99] .nil .nil)) (.node [v0,v1,v1012,v3,v4,v5] (.node [v0,v1,v1013,v3,v4,v5] .nil .nil) .nil))) (.node [v0,v1,v283,v3,v4,v5] (.node [v0,v1,v287,v107,v3,v4] (.node [v0,v1,v114,v3,v4,v99] (.node [v0,v1,v114,v3,v4,v5] .nil .nil) (.node [v0,v1,v1014,v3,v4,v5] .nil .nil)) (.node [v0,v1,v1015,v3,v4,v5] (.node [v0,v1,v287,v3,v4,v5] .nil .nil) (.node [v0,v1,v283,v107,v3,v4] .nil .nil))) (.node [v0,v1016,v2,v3,v4,v5] (.node [v0,v1017,v2,v3,v4,v5] (.node [v0,v1018,v2,v3,v4,v5] .nil .nil) (.node [v0,v289,v2,v3,v4,v5] .nil .nil)) (.node [v0,v1019,v2,v3,v4,v5] (.node [v0,v1020,v2,v3,v4,v5] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5rrrlrl : everyKey (rowOK 4 tree_4) tree_5rrrlrl = true := by decide +kernel
def tree_5rrrlrr : BinaryTree (List W) := (.node [v0,v241,v168,v3,v4,v5] (.node [v0,v449,v2,v3,v4,v5] (.node [v0,v1021,v2,v3,v4,v5] (.node [v0,v1022,v2,v3,v4,v5] (.node [v0,v1023,v2,v3,v4,v5] .nil .nil) (.node [v0,v1024,v2,v3,v4,v5] .nil .nil)) (.node [v0,v1025,v2,v3,v4,v5] (.node [v0,v1026,v2,v3,v4,v5] .nil .nil) (.node [v0,v450,v2,v3,v4,v5] .nil .nil))) (.node [v0,v288,v2,v107,v3,v4] (.node [v0,v1027,v2,v3,v4,v5] (.node [v0,v1028,v2,v3,v4,v5] .nil .nil) (.node [v0,v1029,v2,v3,v4,v5] .nil .nil)) (.node [v0,v288,v2,v3,v4,v99] (.node [v0,v288,v2,v3,v4,v5] .nil .nil) .nil))) (.node [v0,v168,v2,v3,v4,v99] (.node [v0,v1030,v2,v3,v4,v5] (.node [v0,v241,v119,v3,v4,v5] (.node [v0,v241,v120,v3,v4,v5] .nil .nil) (.node [v0,v1031,v2,v3,v4,v5] .nil .nil)) (.node [v0,v168,v2,v107,v3,v4] (.node [v0,v1032,v2,v3,v4,v5] .nil .nil) (.node [v0,v168,v2,v3,v4,v5] .nil .nil))) (.node [v0,v292,v2,v3,v4,v5] (.node [v0,v1033,v2,v3,v4,v5] (.node [v0,v49,v2,v3,v4,v5] .nil .nil) (.node [v0,v292,v2,v107,v3,v4] .nil .nil)) (.node [v0,v2,v1034,v3,v4,v5] (.node [v0,v2,v126,v3,v4,v5] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5rrrlrr : everyKey (rowOK 4 tree_4) tree_5rrrlrr = true := by decide +kernel
def tree_5rrrlr : BinaryTree (List W) := .node [v0,v1035,v2,v3,v4,v5] tree_5rrrlrl tree_5rrrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5rrrlr : everyKey (rowOK 4 tree_4) tree_5rrrlr = true := by
  change (_ && everyKey _ tree_5rrrlrl && everyKey _ tree_5rrrlrr) = true
  rw [ok_tree_5rrrlrl, ok_tree_5rrrlrr]
  decide +kernel
def tree_5rrrl : BinaryTree (List W) := .node [v0,v1,v1036,v3,v4,v5] tree_5rrrll tree_5rrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5rrrl : everyKey (rowOK 4 tree_4) tree_5rrrl = true := by
  change (_ && everyKey _ tree_5rrrll && everyKey _ tree_5rrrlr) = true
  rw [ok_tree_5rrrll, ok_tree_5rrrlr]
  decide +kernel
def tree_5rrrrll : BinaryTree (List W) := (.node [v452,v1,v2,v3,v4,v5] (.node [v1037,v1,v2,v3,v4,v5] (.node [v296,v1,v2,v3,v4,v5] (.node [v1038,v1,v2,v3,v4,v5] (.node [v0,v2,v291,v3,v4,v5] .nil .nil) (.node [v1039,v1,v2,v3,v4,v5] .nil .nil)) (.node [v1040,v1,v2,v3,v4,v5] (.node [v1041,v1,v2,v3,v4,v5] .nil .nil) (.node [v1042,v1,v2,v3,v4,v5] .nil .nil))) (.node [v1043,v1,v2,v3,v4,v5] (.node [v1044,v1,v2,v3,v4,v5] (.node [v1045,v1,v2,v3,v4,v5] .nil .nil) (.node [v1046,v1,v2,v3,v4,v5] .nil .nil)) (.node [v1047,v1,v2,v3,v4,v5] (.node [v1048,v1,v2,v3,v4,v5] .nil .nil) (.node [v451,v1,v2,v3,v4,v5] .nil .nil)))) (.node [v293,v1,v2,v3,v4,v99] (.node [v293,v132,v2,v3,v4,v5] (.node [v1049,v1,v2,v3,v4,v5] (.node [v1050,v1,v2,v3,v4,v5] .nil .nil) (.node [v1051,v1,v2,v3,v4,v5] .nil .nil)) (.node [v293,v1,v2,v107,v3,v4] (.node [v293,v212,v2,v3,v4,v5] .nil .nil) (.node [v293,v1,v2,v3,v4,v5] .nil .nil))) (.node [v195,v1,v121,v3,v4,v5] (.node [v195,v1,v84,v3,v4,v5] (.node [v195,v303,v1,v3,v4,v5] .nil .nil) (.node [v195,v1,v120,v3,v4,v5] .nil .nil)) (.node [v149,v156,v2,v3,v4,v5] (.node [v299,v166,v2,v3,v4,v5] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5rrrrll : everyKey (rowOK 4 tree_4) tree_5rrrrll = true := by decide +kernel
def tree_5rrrrlr : BinaryTree (List W) := (.node [v300,v1,v121,v3,v4,v5] (.node [v212,v166,v121,v3,v4,v5] (.node [v303,v212,v1,v3,v4,v5] (.node [v1052,v1,v2,v3,v4,v5] (.node [v1053,v1,v2,v3,v4,v5] .nil .nil) (.node [v1054,v1,v2,v3,v4,v5] .nil .nil)) (.node [v303,v1,v2,v3,v4,v5] (.node [v303,v1,v2,v107,v3,v4] .nil .nil) (.node [v303,v1,v2,v3,v4,v99] .nil .nil))) (.node [v166,v1055,v2,v3,v4,v5] (.node [v166,v1,v134,v3,v4,v5] (.node [v212,v124,v120,v3,v4,v5] .nil .nil) (.node [v166,v288,v2,v3,v4,v5] .nil .nil)) (.node [v1056,v1,v2,v3,v4,v5] (.node [v166,v49,v2,v3,v4,v5] .nil .nil) .nil))) (.node [v1,v124,v1057,v3,v4,v5] (.node [v9,v45,v2,v3,v4,v5] (.node [v174,v84,v2,v3,v4,v5] (.node [v32,v306,v2,v4,v5,v226] .nil .nil) (.node [v152,v156,v2,v3,v4,v5] .nil .nil)) (.node [v1,v124,v50,v3,v4,v5] (.node [v1,v298,v2,v3,v4,v5] .nil .nil) (.node [v1,v124,v134,v3,v4,v5] .nil .nil))) (.node [v1,v341,v184,v2,v3,v4] (.node [v1,v358,v69,v2,v3,v5] (.node [v1,v1058,v2,v3,v4,v5] .nil .nil) (.node [v1,v358,v2,v3,v990,v5] .nil .nil)) (.node [v1,v184,v2,v3,v4,v5] (.node [v1,v184,v2,v3,v4] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5rrrrlr : everyKey (rowOK 4 tree_4) tree_5rrrrlr = true := by decide +kernel
def tree_5rrrrl : BinaryTree (List W) := .node [v23,v45,v2,v3,v4,v5] tree_5rrrrll tree_5rrrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5rrrrl : everyKey (rowOK 4 tree_4) tree_5rrrrl = true := by
  change (_ && everyKey _ tree_5rrrrll && everyKey _ tree_5rrrrlr) = true
  rw [ok_tree_5rrrrll, ok_tree_5rrrrlr]
  decide +kernel
def tree_5rrrrrl : BinaryTree (List W) := (.node [v1,v1059,v2,v3,v4,v5] (.node [v1,v1060,v2,v3,v4,v5] (.node [v1,v84,v2,v1061,v4,v5] (.node [v1,v84,v175,v3,v4,v5] (.node [v1,v84,v44,v2,v4,v5] .nil .nil) (.node [v1,v84,v2,v3,v170,v5] .nil .nil)) (.node [v1,v84,v2,v1062,v4,v5] (.node [v1,v84,v2,v1063,v4,v5] .nil .nil) (.node [v1,v1064,v2,v3,v4,v5] .nil .nil))) (.node [v1,v306,v2,v3,v4,v213] (.node [v1,v306,v2,v107,v3,v4] (.node [v1,v306,v187,v3,v4,v5] .nil .nil) (.node [v1,v306,v2,v3,v215,v5] .nil .nil)) (.node [v1,v306,v2,v3,v4,v99] (.node [v1,v306,v2,v3,v4,v5] .nil .nil) .nil))) (.node [v1,v45,v2,v192,v5,v104] (.node [v1,v156,v2,v3,v4,v154] (.node [v1,v156,v2,v107,v3,v4] (.node [v1,v156,v41,v4,v5,v244] .nil .nil) (.node [v1,v156,v2,v3,v155,v5] .nil .nil)) (.node [v1,v156,v2,v3,v4,v99] (.node [v1,v156,v2,v3,v4,v5] .nil .nil) (.node [v1,v45,v27,v3,v4,v5] .nil .nil))) (.node [v1,v45,v2,v3,v4,v99] (.node [v1,v45,v2,v3,v4,v110] (.node [v1,v45,v2,v107,v3,v4] .nil .nil) (.node [v1,v45,v2,v3,v4,v5] .nil .nil)) (.node [v1,v1065,v2,v3,v4,v5] (.node [v1,v45,v2,v3,v99,v104] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5rrrrrl : everyKey (rowOK 4 tree_4) tree_5rrrrrl = true := by decide +kernel
def tree_5rrrrrr : BinaryTree (List W) := (.node [v1,v50,v2,v3,v4,v5] (.node [v1,v1066,v2,v3,v4,v99] (.node [v1,v1067,v2,v3,v4,v5] (.node [v1,v1068,v2,v3,v4,v5] (.node [v1,v1069,v2,v3,v4,v5] .nil .nil) (.node [v1,v1068,v2,v3,v4,v99] .nil .nil)) (.node [v1,v1070,v2,v3,v4,v5] (.node [v1,v1071,v2,v3,v4,v5] .nil .nil) (.node [v1,v1066,v2,v3,v4,v5] .nil .nil))) (.node [v1,v44,v2,v3,v4,v5] (.node [v1,v69,v2,v3,v371,v5] (.node [v1,v69,v2,v3,v4,v5] .nil .nil) (.node [v1,v69,v2,v3,v5] .nil .nil)) (.node [v1,v44,v2,v4,v5,v169] (.node [v1,v44,v2,v4,v5] .nil .nil) .nil))) (.node [v1,v2,v1072,v3,v4,v5] (.node [v1,v1073,v2,v3,v4,v5] (.node [v1,v50,v3,v4,v5] (.node [v1,v50,v121,v3,v4,v5] .nil .nil) (.node [v1,v49,v2,v3,v4,v5] .nil .nil)) (.node [v1,v319,v2,v3,v4,v5] (.node [v1,v319,v2,v107,v3,v4] .nil .nil) (.node [v1,v2,v131,v3,v4,v5] .nil .nil))) (.node [v49,v120,v2,v3,v4,v5] (.node [v1,v2,v318,v3,v4,v5] (.node [v1,v2,v318,v107,v3,v4] .nil .nil) (.node [v288,v124,v2,v3,v4,v5] .nil .nil)) (.node [v120,v128,v2,v3,v4,v5] (.node [v49,v2,v3,v4,v5] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5rrrrrr : everyKey (rowOK 4 tree_4) tree_5rrrrrr = true := by decide +kernel
def tree_5rrrrr : BinaryTree (List W) := .node [v1,v1065,v2,v3,v4,v99] tree_5rrrrrl tree_5rrrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5rrrrr : everyKey (rowOK 4 tree_4) tree_5rrrrr = true := by
  change (_ && everyKey _ tree_5rrrrrl && everyKey _ tree_5rrrrrr) = true
  rw [ok_tree_5rrrrrl, ok_tree_5rrrrrr]
  decide +kernel
def tree_5rrrr : BinaryTree (List W) := .node [v1,v184,v2,v3,v4,v590] tree_5rrrrl tree_5rrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5rrrr : everyKey (rowOK 4 tree_4) tree_5rrrr = true := by
  change (_ && everyKey _ tree_5rrrrl && everyKey _ tree_5rrrrr) = true
  rw [ok_tree_5rrrrl, ok_tree_5rrrrr]
  decide +kernel
def tree_5rrr : BinaryTree (List W) := .node [v0,v2,v291,v107,v3,v4] tree_5rrrl tree_5rrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5rrr : everyKey (rowOK 4 tree_4) tree_5rrr = true := by
  change (_ && everyKey _ tree_5rrrl && everyKey _ tree_5rrrr) = true
  rw [ok_tree_5rrrl, ok_tree_5rrrr]
  decide +kernel
def tree_5rr : BinaryTree (List W) := .node [v0,v1,v2,v3,v1074,v5] tree_5rrl tree_5rrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5rr : everyKey (rowOK 4 tree_4) tree_5rr = true := by
  change (_ && everyKey _ tree_5rrl && everyKey _ tree_5rrr) = true
  rw [ok_tree_5rrl, ok_tree_5rrr]
  decide +kernel
def tree_5r : BinaryTree (List W) := .node [v0,v1,v2,v1075,v3,v4] tree_5rl tree_5rr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5r : everyKey (rowOK 4 tree_4) tree_5r = true := by
  change (_ && everyKey _ tree_5rl && everyKey _ tree_5rr) = true
  rw [ok_tree_5rl, ok_tree_5rr]
  decide +kernel
def tree_5 : BinaryTree (List W) := .node [v0,v1076,v1,v3,v4,v5] tree_5l tree_5r
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_5 : everyKey (rowOK 4 tree_4) tree_5 = true := by
  change (_ && everyKey _ tree_5l && everyKey _ tree_5r) = true
  rw [ok_tree_5l, ok_tree_5r]
  decide +kernel
theorem closed_5 : Closed 5 tree_5 := closed_next 4 (by decide) tree_5 tree_4 closed_4 ok_tree_5
def tree_6lllll : BinaryTree (List W) := (.node [v322,v0,v1,v2,v3,v4,v5] (.node [v1077,v0,v1,v2,v3,v4,v5] (.node [v57,v0,v1,v2,v3,v4,v5] (.node [v324,v0,v1,v2,v107,v3,v4] (.node [v324,v75,v0,v1,v2,v3,v4] (.node [v324,v68,v0,v1,v2,v3,v4] .nil .nil) .nil) (.node [v324,v0,v1,v2,v3,v4,v99] (.node [v324,v0,v1,v2,v3,v4,v5] .nil .nil) .nil)) (.node [v325,v75,v0,v1,v2,v3,v4] (.node [v58,v0,v1,v2,v3,v4,v5] (.node [v56,v0,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v1078,v0,v1,v2,v3,v4,v5] (.node [v325,v0,v1,v2,v3,v4,v5] .nil .nil) .nil))) (.node [v1079,v0,v1,v2,v3,v4,v5] (.node [v1080,v0,v1,v2,v3,v4,v5] (.node [v1081,v0,v1,v2,v3,v4,v5] (.node [v1082,v0,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v1083,v0,v1,v2,v3,v4,v5] (.node [v1084,v0,v1,v2,v3,v4,v5] .nil .nil) .nil)) (.node [v1085,v0,v1,v2,v3,v4,v5] (.node [v1086,v0,v1,v2,v3,v4,v5] (.node [v1087,v0,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v1088,v0,v1,v2,v3,v4,v5] .nil .nil)))) (.node [v1089,v0,v1,v2,v3,v4,v5] (.node [v55,v68,v0,v1,v2,v3,v4] (.node [v328,v0,v1,v2,v3,v4,v99] (.node [v328,v0,v1,v2,v3,v4,v5] (.node [v322,v0,v1,v2,v3,v4,v99] .nil .nil) .nil) (.node [v326,v0,v1,v2,v3,v4,v99] (.node [v326,v0,v1,v2,v3,v4,v5] .nil .nil) .nil)) (.node [v55,v0,v1,v2,v3,v4,v5] (.node [v55,v0,v1,v2,v3,v4] (.node [v55,v86,v0,v1,v2,v3,v4] .nil .nil) .nil) (.node [v55,v0,v1,v2,v3,v4,v99] .nil .nil))) (.node [v1090,v0,v1,v2,v3,v4,v5] (.node [v1091,v0,v1,v2,v3,v4,v5] (.node [v1092,v0,v1,v2,v3,v4,v5] (.node [v1093,v0,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v1094,v0,v1,v2,v3,v4,v5] (.node [v1095,v0,v1,v2,v3,v4,v5] .nil .nil) .nil)) (.node [v338,v0,v1,v2,v3,v4,v5] (.node [v338,v68,v0,v1,v2,v3,v4] (.node [v1096,v0,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v1097,v0,v1,v2,v3,v4,v5] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6lllll : everyKey (rowOK 5 tree_5) tree_6lllll = true := by decide +kernel
def tree_6llllr : BinaryTree (List W) := (.node [v1098,v0,v1,v2,v3,v4,v5] (.node [v335,v0,v1,v2,v3,v4,v99] (.node [v335,v589,v1,v2,v3,v4,v5] (.node [v1099,v0,v1,v2,v3,v4,v5] (.node [v336,v0,v1,v2,v3,v4,v5] (.node [v336,v68,v0,v1,v2,v3,v4] .nil .nil) .nil) (.node [v335,v75,v0,v1,v2,v3,v4] (.node [v335,v68,v0,v1,v2,v3,v4] .nil .nil) .nil)) (.node [v335,v0,v1,v2,v3,v4,v5] (.node [v335,v0,v1,v2,v107,v3,v4] (.node [v335,v0,v1,v341,v2,v3,v4] .nil .nil) .nil) (.node [v335,v0,v1,v2,v3,v4,v590] .nil .nil))) (.node [v333,v0,v1,v2,v3,v4,v5] (.node [v1100,v0,v1,v2,v3,v4,v5] (.node [v335,v1,v341,v2,v3,v4,v5] (.node [v335,v1,v341,v2,v3,v4] .nil .nil) .nil) (.node [v333,v68,v0,v1,v2,v3,v4] (.node [v1101,v0,v1,v2,v3,v4,v5] .nil .nil) .nil)) (.node [v346,v68,v0,v1,v2,v3,v4] (.node [v1102,v0,v1,v2,v3,v4,v5] (.node [v1103,v0,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v346,v0,v1,v2,v3,v4,v5] .nil .nil)))) (.node [v1104,v0,v1,v2,v3,v4,v5] (.node [v344,v0,v639,v2,v3,v4,v5] (.node [v344,v0,v345,v1,v2,v3,v4] (.node [v344,v75,v0,v1,v2,v3,v4] (.node [v344,v68,v0,v1,v2,v3,v4] .nil .nil) .nil) (.node [v344,v0,v345,v2,v3,v4,v5] (.node [v344,v0,v345,v2,v3,v4] .nil .nil) .nil)) (.node [v344,v0,v1,v2,v3,v4,v641] (.node [v344,v0,v1,v2,v3,v4,v5] (.node [v344,v0,v1,v2,v107,v3,v4] .nil .nil) .nil) (.node [v344,v0,v1,v2,v3,v4,v99] .nil .nil))) (.node [v374,v0,v1,v2,v3,v4,v5] (.node [v352,v0,v1,v2,v3,v4,v5] (.node [v352,v68,v0,v1,v2,v3,v4] (.node [v1105,v0,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v374,v68,v0,v1,v2,v3,v4] (.node [v1106,v0,v1,v2,v3,v4,v5] .nil .nil) .nil)) (.node [v355,v75,v0,v1,v2,v3,v4] (.node [v355,v68,v0,v1,v2,v3,v4] (.node [v1107,v0,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v355,v356,v0,v1,v2,v3,v4] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6llllr : everyKey (rowOK 5 tree_5) tree_6llllr = true := by decide +kernel
def tree_6llll : BinaryTree (List W) := .node [v1108,v0,v1,v2,v3,v4,v5] tree_6lllll tree_6llllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6llll : everyKey (rowOK 5 tree_5) tree_6llll = true := by
  change (_ && everyKey _ tree_6lllll && everyKey _ tree_6llllr) = true
  rw [ok_tree_6lllll, ok_tree_6llllr]
  decide +kernel
def tree_6lllrl : BinaryTree (List W) := (.node [v68,v94,v0,v1,v2,v3,v4] (.node [v68,v391,v0,v1,v2,v3,v4] (.node [v355,v0,v1,v2,v3,v4,v99] (.node [v355,v0,v1,v2,v107,v3,v4] (.node [v355,v0,v1,v546,v3,v4,v5] (.node [v355,v356,v0,v1,v3,v4,v5] .nil .nil) .nil) (.node [v355,v0,v1,v2,v3,v4,v548] (.node [v355,v0,v1,v2,v3,v4,v5] .nil .nil) .nil)) (.node [v361,v68,v0,v1,v2,v3,v4] (.node [v1109,v0,v1,v2,v3,v4,v5] (.node [v1110,v0,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v68,v68,v0,v1,v2,v3,v4] (.node [v361,v0,v1,v2,v3,v4,v5] .nil .nil) .nil))) (.node [v68,v366,v0,v1,v2,v3,v4] (.node [v68,v81,v0,v1,v2,v3,v4] (.node [v68,v77,v0,v1,v2,v3,v4] (.node [v68,v79,v0,v1,v2,v3,v4] .nil .nil) .nil) (.node [v68,v86,v0,v1,v2,v3,v4] (.node [v68,v75,v0,v1,v2,v3,v4] .nil .nil) .nil)) (.node [v68,v83,v0,v1,v2,v3,v4] (.node [v68,v366,v0,v1,v2,v4,v5] (.node [v68,v366,v0,v1,v2,v4] .nil .nil) .nil) (.node [v68,v92,v0,v1,v2,v3,v4] .nil .nil)))) (.node [v68,v171,v0,v1,v2,v3,v4] (.node [v68,v356,v0,v1,v2,v3,v4] (.node [v68,v123,v0,v1,v2,v3,v4] (.node [v68,v115,v0,v1,v2,v3,v4] (.node [v68,v330,v0,v1,v2,v3,v4] .nil .nil) .nil) (.node [v68,v354,v0,v1,v2,v3,v4] (.node [v68,v130,v0,v1,v2,v3,v4] .nil .nil) .nil)) (.node [v68,v164,v0,v1,v2,v3,v4] (.node [v68,v158,v0,v1,v2,v3,v4] (.node [v68,v95,v0,v1,v2,v3,v4] .nil .nil) .nil) (.node [v68,v21,v0,v1,v2,v3,v4] .nil .nil))) (.node [v68,v0,v345,v1,v2,v3,v4] (.node [v68,v0,v337,v1,v2,v3,v4] (.node [v68,v353,v0,v1,v2,v3,v4] (.node [v68,v589,v0,v1,v2,v3,v4] .nil .nil) .nil) (.node [v68,v0,v362,v1,v2,v3,v4] (.node [v68,v0,v132,v1,v2,v3,v4] .nil .nil) .nil)) (.node [v68,v0,v166,v1,v2,v3,v4] (.node [v68,v0,v212,v1,v2,v3,v4] (.node [v68,v0,v93,v1,v2,v3,v4] .nil .nil) .nil) (.node [v68,v0,v32,v1,v2,v3,v4] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6lllrl : everyKey (rowOK 5 tree_5) tree_6lllrl = true := by decide +kernel
def tree_6lllrr : BinaryTree (List W) := (.node [v68,v0,v1,v2,v3,v331,v4] (.node [v68,v0,v1,v546,v2,v3,v4] (.node [v68,v0,v1,v341,v2,v3,v4] (.node [v68,v0,v1,v347,v2,v3,v4] (.node [v68,v0,v334,v1,v2,v3,v4] (.node [v68,v0,v639,v1,v2,v3,v4] .nil .nil) .nil) (.node [v68,v0,v1,v358,v2,v3,v4] (.node [v68,v0,v1,v124,v2,v3,v4] .nil .nil) .nil)) (.node [v68,v0,v1,v41,v2,v3,v4] (.node [v68,v0,v1,v120,v2,v3,v4] (.node [v68,v0,v1,v84,v2,v3,v4] .nil .nil) .nil) (.node [v68,v0,v1,v242,v2,v3,v4] .nil .nil))) (.node [v68,v0,v1,v2,v107,v3,v4] (.node [v68,v0,v1,v2,v121,v3,v4] (.node [v68,v0,v1,v2,v360,v3,v4] (.node [v68,v0,v1,v339,v2,v3,v4] .nil .nil) .nil) (.node [v68,v0,v1,v2,v192,v3,v4] (.node [v68,v0,v1,v2,v119,v3,v4] .nil .nil) .nil)) (.node [v68,v0,v1,v2,v3,v3,v4] (.node [v68,v0,v1,v2,v107,v4,v5] (.node [v68,v0,v1,v2,v107,v4] .nil .nil) .nil) (.node [v68,v0,v1,v2,v3,v474,v4] .nil .nil)))) (.node [v68,v0,v1,v2,v3,v4,v99] (.node [v68,v0,v1,v2,v3,v4,v5] (.node [v68,v0,v1,v2,v3,v4,v371] (.node [v68,v0,v1,v2,v3,v4,v261] (.node [v68,v0,v1,v2,v3,v4] .nil .nil) .nil) (.node [v68,v0,v1,v2,v3,v4,v377] (.node [v68,v0,v1,v2,v3,v4,v372] .nil .nil) .nil)) (.node [v68,v0,v1,v2,v3,v4,v548] (.node [v68,v0,v1,v2,v3,v4,v641] (.node [v68,v0,v1,v2,v3,v4,v590] .nil .nil) .nil) (.node [v68,v0,v1,v2,v3,v4,v487] .nil .nil))) (.node [v391,v77,v0,v1,v2,v3,v5] (.node [v68,v0,v1,v2,v3,v4,v244] (.node [v68,v0,v1,v2,v3,v4,v226] (.node [v68,v0,v1,v2,v3,v4,v169] .nil .nil) .nil) (.node [v391,v79,v0,v1,v2,v3,v5] (.node [v68,v0,v1,v2,v3,v4,v104] .nil .nil) .nil)) (.node [v391,v75,v0,v1,v2,v3,v4] (.node [v391,v75,v0,v1,v2,v3] (.node [v391,v81,v0,v1,v2,v3,v5] .nil .nil) .nil) (.node [v391,v75,v0,v1,v2,v3,v5] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6lllrr : everyKey (rowOK 5 tree_5) tree_6lllrr = true := by decide +kernel
def tree_6lllr : BinaryTree (List W) := .node [v68,v0,v220,v1,v2,v3,v4] tree_6lllrl tree_6lllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6lllr : everyKey (rowOK 5 tree_5) tree_6lllr = true := by
  change (_ && everyKey _ tree_6lllrl && everyKey _ tree_6lllrr) = true
  rw [ok_tree_6lllrl, ok_tree_6lllrr]
  decide +kernel
def tree_6lll : BinaryTree (List W) := .node [v355,v356,v0,v1,v3,v4] tree_6llll tree_6lllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6lll : everyKey (rowOK 5 tree_5) tree_6lll = true := by
  change (_ && everyKey _ tree_6llll && everyKey _ tree_6lllr) = true
  rw [ok_tree_6llll, ok_tree_6lllr]
  decide +kernel
def tree_6llrll : BinaryTree (List W) := (.node [v96,v0,v1,v2,v3,v4,v104] (.node [v72,v0,v1,v2,v3,v4] (.node [v391,v0,v1,v2,v3,v4,v5] (.node [v391,v0,v1,v242,v2,v3,v5] (.node [v391,v0,v220,v1,v2,v3,v5] (.node [v391,v171,v0,v1,v2,v3,v5] .nil .nil) .nil) (.node [v391,v0,v1,v2,v3,v474,v5] (.node [v391,v0,v1,v2,v107,v3,v4] .nil .nil) .nil)) (.node [v1111,v0,v1,v2,v3,v4,v5] (.node [v391,v0,v1,v2,v3,v5,v104] (.node [v391,v0,v1,v2,v3,v4,v99] .nil .nil) .nil) (.node [v1112,v0,v1,v2,v3,v4,v5] (.node [v1113,v0,v1,v2,v3,v4,v5] .nil .nil) .nil))) (.node [v73,v0,v1,v2,v3,v4] (.node [v74,v0,v1,v2,v3,v4] (.node [v72,v0,v1,v2,v3,v4,v169] (.node [v72,v0,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v74,v0,v1,v2,v3,v4,v226] (.node [v74,v0,v1,v2,v3,v4,v5] .nil .nil) .nil)) (.node [v96,v0,v1,v2,v3,v4] (.node [v73,v0,v1,v2,v3,v4,v244] (.node [v73,v0,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v96,v0,v1,v2,v3,v4,v5] .nil .nil)))) (.node [v1114,v0,v1,v2,v3,v4,v5] (.node [v1115,v0,v1,v2,v3,v4,v5] (.node [v411,v75,v0,v1,v2,v3,v4] (.node [v1116,v0,v1,v2,v3,v4,v5] (.node [v1117,v0,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v413,v0,v1,v2,v3,v4,v5] (.node [v411,v0,v1,v2,v3,v4,v5] .nil .nil) .nil)) (.node [v410,v0,v1,v2,v3,v4,v5] (.node [v410,v75,v0,v1,v2,v3,v4] (.node [v1118,v0,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v415,v0,v1,v2,v3,v4,v5] .nil .nil))) (.node [v419,v0,v1,v2,v3,v4,v5] (.node [v414,v0,v1,v2,v3,v4,v5] (.node [v414,v75,v0,v1,v2,v3,v4] (.node [v1119,v0,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v409,v0,v1,v2,v3,v4,v5] (.node [v416,v0,v1,v2,v3,v4,v5] .nil .nil) .nil)) (.node [v1120,v0,v1,v2,v3,v4,v5] (.node [v417,v0,v1,v2,v3,v4,v5] (.node [v417,v75,v0,v1,v2,v3,v4] .nil .nil) .nil) (.node [v79,v75,v0,v1,v2,v3,v4] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6llrll : everyKey (rowOK 5 tree_5) tree_6llrll = true := by decide +kernel
def tree_6llrlr : BinaryTree (List W) := (.node [v77,v0,v220,v2,v3,v4,v5] (.node [v79,v1,v358,v2,v3,v5] (.node [v79,v0,v1,v2,v3,v4,v99] (.node [v79,v0,v1,v2,v192,v3,v5] (.node [v79,v0,v1,v358,v2,v3,v5] (.node [v79,v171,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v79,v0,v1,v2,v3,v4,v5] (.node [v79,v0,v1,v2,v107,v3,v4] .nil .nil) .nil)) (.node [v79,v0,v1,v2,v3,v99] (.node [v79,v0,v1,v2,v3,v5,v99] (.node [v79,v0,v1,v2,v3,v371,v5] .nil .nil) .nil) (.node [v79,v1,v358,v2,v3,v4,v5] .nil .nil))) (.node [v77,v75,v0,v1,v2,v3,v4] (.node [v422,v75,v0,v1,v2,v3,v4] (.node [v424,v0,v1,v2,v3,v4,v5] (.node [v420,v0,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v1121,v0,v1,v2,v3,v4,v5] (.node [v422,v0,v1,v2,v3,v4,v5] .nil .nil) .nil)) (.node [v77,v0,v362,v2,v3,v4,v5] (.node [v77,v0,v362,v1,v2,v3,v5] (.node [v77,v86,v0,v1,v2,v3,v5] .nil .nil) .nil) (.node [v77,v0,v362,v2,v3,v5] .nil .nil)))) (.node [v427,v0,v1,v2,v3,v4,v5] (.node [v77,v0,v1,v2,v3,v5,v99] (.node [v77,v0,v1,v2,v3,v4,v5] (.node [v77,v0,v1,v2,v107,v3,v4] (.node [v77,v0,v1,v2,v192,v3,v5] .nil .nil) .nil) (.node [v77,v0,v1,v2,v3,v372,v5] (.node [v77,v0,v1,v2,v3,v4,v99] .nil .nil) .nil)) (.node [v429,v0,v1,v2,v3,v4,v5] (.node [v425,v0,v1,v2,v3,v4,v5] (.node [v77,v0,v1,v2,v3,v99] .nil .nil) .nil) (.node [v427,v75,v0,v1,v2,v3,v4] .nil .nil))) (.node [v81,v354,v0,v1,v3,v5] (.node [v81,v86,v0,v1,v2,v3,v5] (.node [v81,v75,v0,v1,v2,v3,v4] (.node [v1122,v0,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v81,v354,v0,v1,v3,v4,v5] (.node [v81,v354,v0,v1,v2,v3,v5] .nil .nil) .nil)) (.node [v81,v0,v1,v2,v107,v3,v4] (.node [v81,v0,v1,v2,v192,v3,v5] (.node [v81,v0,v1,v242,v3,v4,v5] .nil .nil) .nil) (.node [v81,v0,v1,v2,v3,v4,v5] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6llrlr : everyKey (rowOK 5 tree_5) tree_6llrlr = true := by decide +kernel
def tree_6llrl : BinaryTree (List W) := .node [v79,v86,v0,v1,v2,v3,v5] tree_6llrll tree_6llrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6llrl : everyKey (rowOK 5 tree_5) tree_6llrl = true := by
  change (_ && everyKey _ tree_6llrll && everyKey _ tree_6llrlr) = true
  rw [ok_tree_6llrll, ok_tree_6llrlr]
  decide +kernel
def tree_6llrrl : BinaryTree (List W) := (.node [v75,v354,v0,v1,v2,v3,v4] (.node [v76,v0,v1,v2,v3,v4,v5] (.node [v434,v0,v1,v2,v3,v4,v5] (.node [v81,v0,v1,v2,v3,v99] (.node [v81,v0,v1,v2,v3,v5,v99] (.node [v81,v0,v1,v2,v3,v377,v5] .nil .nil) .nil) (.node [v432,v0,v1,v2,v3,v4,v5] (.node [v433,v0,v1,v2,v3,v4,v5] .nil .nil) .nil)) (.node [v76,v0,v1,v2,v107,v3,v4] (.node [v76,v86,v0,v1,v2,v3,v4] (.node [v76,v75,v0,v1,v2,v3,v4] .nil .nil) .nil) (.node [v76,v0,v1,v2,v3,v4] .nil .nil))) (.node [v75,v94,v0,v1,v2,v3,v4] (.node [v75,v366,v0,v1,v2,v3,v4] (.node [v75,v86,v0,v1,v2,v3,v4] (.node [v75,v75,v0,v1,v2,v3,v4] .nil .nil) .nil) (.node [v75,v92,v0,v1,v2,v3,v4] (.node [v75,v83,v0,v1,v2,v3,v4] .nil .nil) .nil)) (.node [v75,v123,v0,v1,v2,v3,v4] (.node [v75,v115,v0,v1,v2,v3,v4] (.node [v75,v330,v0,v1,v2,v3,v4] .nil .nil) .nil) (.node [v75,v130,v0,v1,v2,v3,v4] .nil .nil)))) (.node [v75,v0,v362,v1,v2,v3,v4] (.node [v75,v171,v0,v1,v2,v3,v4] (.node [v75,v158,v0,v1,v2,v3,v4] (.node [v75,v95,v0,v1,v2,v3,v4] (.node [v75,v356,v0,v1,v2,v3,v4] .nil .nil) .nil) (.node [v75,v21,v0,v1,v2,v3,v4] (.node [v75,v164,v0,v1,v2,v3,v4] .nil .nil) .nil)) (.node [v75,v0,v418,v1,v2,v3,v4] (.node [v75,v589,v0,v1,v2,v3,v4] (.node [v75,v178,v0,v1,v2,v3,v4] .nil .nil) .nil) (.node [v75,v0,v132,v1,v2,v3,v4] .nil .nil))) (.node [v75,v0,v220,v1,v2,v3,v4] (.node [v75,v0,v212,v1,v2,v3,v4] (.node [v75,v0,v93,v1,v2,v3,v4] (.node [v75,v0,v345,v1,v2,v3,v4] .nil .nil) .nil) (.node [v75,v0,v32,v1,v2,v3,v4] (.node [v75,v0,v166,v1,v2,v3,v4] .nil .nil) .nil)) (.node [v75,v0,v1,v423,v2,v3,v4] (.node [v75,v0,v639,v1,v2,v3,v4] (.node [v75,v0,v224,v1,v2,v3,v4] .nil .nil) .nil) (.node [v75,v0,v1,v124,v2,v3,v4] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6llrrl : everyKey (rowOK 5 tree_5) tree_6llrrl = true := by decide +kernel
def tree_6llrrr : BinaryTree (List W) := (.node [v75,v0,v1,v2,v3,v4,v590] (.node [v75,v0,v1,v2,v192,v3,v4] (.node [v75,v0,v1,v248,v2,v3,v4] (.node [v75,v0,v1,v120,v2,v3,v4] (.node [v75,v0,v1,v84,v2,v3,v4] (.node [v75,v0,v1,v341,v2,v3,v4] .nil .nil) .nil) (.node [v75,v0,v1,v242,v2,v3,v4] (.node [v75,v0,v1,v41,v2,v3,v4] .nil .nil) .nil)) (.node [v75,v0,v1,v2,v121,v3,v4] (.node [v75,v0,v1,v2,v428,v3,v4] (.node [v75,v0,v1,v546,v2,v3,v4] .nil .nil) .nil) (.node [v75,v0,v1,v2,v119,v3,v4] .nil .nil))) (.node [v75,v0,v1,v2,v3,v4,v4] (.node [v75,v0,v1,v2,v3,v284,v4] (.node [v75,v0,v1,v2,v107,v3,v4] (.node [v75,v0,v1,v2,v260,v3,v4] .nil .nil) .nil) (.node [v75,v0,v1,v2,v3,v4] (.node [v75,v0,v1,v2,v3,v474,v4] .nil .nil) .nil)) (.node [v75,v0,v1,v2,v3,v4,v377] (.node [v75,v0,v1,v2,v3,v4,v372] (.node [v75,v0,v1,v2,v3,v4,v371] .nil .nil) .nil) (.node [v75,v0,v1,v2,v3,v4,v5] .nil .nil)))) (.node [v86,v330,v0,v1,v2,v3,v5] (.node [v75,v0,v1,v2,v3,v4,v226] (.node [v75,v0,v1,v2,v3,v4,v487] (.node [v75,v0,v1,v2,v3,v4,v548] (.node [v75,v0,v1,v2,v3,v4,v641] .nil .nil) .nil) (.node [v75,v0,v1,v2,v3,v4,v169] (.node [v75,v0,v1,v2,v3,v4,v99] .nil .nil) .nil)) (.node [v75,v0,v1,v2,v3,v5,v99] (.node [v75,v0,v1,v2,v3,v4,v104] (.node [v75,v0,v1,v2,v3,v4,v244] .nil .nil) .nil) (.node [v75,v0,v1,v2,v3,v99] .nil .nil))) (.node [v86,v0,v1,v2,v192,v4,v5] (.node [v86,v171,v0,v1,v2,v3,v5] (.node [v86,v330,v0,v1,v2,v5] (.node [v86,v330,v0,v1,v2,v4,v5] .nil .nil) .nil) (.node [v86,v0,v1,v242,v2,v3,v5] (.node [v86,v0,v220,v1,v2,v3,v5] .nil .nil) .nil)) (.node [v86,v0,v1,v2,v3,v4,v99] (.node [v86,v0,v1,v2,v3,v4,v5] (.node [v86,v0,v1,v2,v107,v3,v4] .nil .nil) .nil) (.node [v86,v0,v1,v2,v3,v5,v104] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6llrrr : everyKey (rowOK 5 tree_5) tree_6llrrr = true := by decide +kernel
def tree_6llrr : BinaryTree (List W) := .node [v75,v0,v1,v358,v2,v3,v4] tree_6llrrl tree_6llrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6llrr : everyKey (rowOK 5 tree_5) tree_6llrr = true := by
  change (_ && everyKey _ tree_6llrrl && everyKey _ tree_6llrrr) = true
  rw [ok_tree_6llrrl, ok_tree_6llrrr]
  decide +kernel
def tree_6llr : BinaryTree (List W) := .node [v81,v0,v1,v2,v3,v4,v99] tree_6llrl tree_6llrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6llr : everyKey (rowOK 5 tree_5) tree_6llr = true := by
  change (_ && everyKey _ tree_6llrl && everyKey _ tree_6llrr) = true
  rw [ok_tree_6llrl, ok_tree_6llrr]
  decide +kernel
def tree_6ll : BinaryTree (List W) := .node [v391,v330,v0,v1,v2,v3,v5] tree_6lll tree_6llr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6ll : everyKey (rowOK 5 tree_5) tree_6ll = true := by
  change (_ && everyKey _ tree_6lll && everyKey _ tree_6llr) = true
  rw [ok_tree_6lll, ok_tree_6llr]
  decide +kernel
def tree_6lrlll : BinaryTree (List W) := (.node [v1123,v0,v1,v2,v3,v4,v5] (.node [v471,v0,v1,v2,v3,v4,v5] (.node [v85,v0,v1,v2,v3,v5] (.node [v89,v0,v1,v2,v3,v5,v169] (.node [v89,v0,v1,v2,v3,v5] (.node [v89,v0,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v85,v0,v1,v2,v3,v4,v5] (.node [v465,v0,v1,v2,v3,v4,v5] .nil .nil) .nil)) (.node [v91,v0,v1,v2,v3,v4,v5] (.node [v469,v0,v1,v2,v3,v4,v5] (.node [v85,v0,v1,v2,v3,v5,v226] .nil .nil) .nil) (.node [v91,v0,v1,v2,v3,v5,v244] (.node [v91,v0,v1,v2,v3,v5] .nil .nil) .nil))) (.node [v366,v0,v1,v2,v107,v3,v4] (.node [v1124,v0,v1,v2,v3,v4,v5] (.node [v1125,v0,v1,v2,v3,v4,v5] (.node [v470,v0,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v475,v0,v1,v2,v3,v4,v5] (.node [v1126,v0,v1,v2,v3,v4,v5] .nil .nil) .nil)) (.node [v366,v0,v1,v2,v4,v5,v487] (.node [v366,v0,v1,v2,v3,v4,v99] (.node [v366,v0,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v1127,v0,v1,v2,v3,v4,v5] .nil .nil)))) (.node [v83,v1,v84,v2,v4,v5] (.node [v83,v0,v1,v2,v3,v4,v5] (.node [v83,v0,v1,v84,v2,v4,v5] (.node [v83,v21,v1,v2,v3,v4,v5] (.node [v476,v0,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v83,v0,v1,v2,v315,v3,v4] (.node [v83,v0,v1,v2,v107,v3,v4] .nil .nil) .nil)) (.node [v83,v0,v1,v2,v4,v5,v169] (.node [v83,v0,v1,v2,v3,v4,v99] (.node [v83,v0,v1,v2,v3,v4,v316] .nil .nil) .nil) (.node [v83,v1,v84,v2,v3,v4,v5] .nil .nil))) (.node [v92,v0,v32,v2,v3,v4,v5] (.node [v92,v0,v93,v1,v2,v4,v5] (.node [v477,v0,v1,v2,v3,v4,v5] (.node [v1128,v0,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v92,v0,v93,v2,v4,v5] (.node [v92,v0,v93,v2,v3,v4,v5] .nil .nil) .nil)) (.node [v92,v0,v1,v2,v3,v4,v5] (.node [v92,v0,v1,v2,v214,v3,v4] (.node [v92,v0,v1,v2,v107,v3,v4] .nil .nil) .nil) (.node [v92,v0,v1,v2,v3,v4,v216] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6lrlll : everyKey (rowOK 5 tree_5) tree_6lrlll = true := by decide +kernel
def tree_6lrllr : BinaryTree (List W) := (.node [v330,v0,v1,v2,v3,v5,v99] (.node [v94,v0,v1,v2,v3,v4,v153] (.node [v94,v95,v0,v1,v4,v5] (.node [v478,v0,v1,v2,v3,v4,v5] (.node [v1129,v0,v1,v2,v3,v4,v5] (.node [v92,v0,v1,v2,v4,v5,v226] .nil .nil) .nil) (.node [v94,v95,v0,v1,v3,v4,v5] (.node [v94,v95,v0,v1,v2,v4,v5] .nil .nil) .nil)) (.node [v94,v0,v1,v2,v148,v3,v4] (.node [v94,v0,v1,v2,v107,v3,v4] (.node [v94,v0,v1,v41,v3,v4,v5] .nil .nil) .nil) (.node [v94,v0,v1,v2,v3,v4,v5] .nil .nil))) (.node [v330,v0,v1,v2,v107,v3,v4] (.node [v1130,v0,v1,v2,v3,v4,v5] (.node [v94,v0,v1,v2,v4,v5,v244] (.node [v94,v0,v1,v2,v3,v4,v99] .nil .nil) .nil) (.node [v330,v0,v1,v2,v192,v3,v5] (.node [v1131,v0,v1,v2,v3,v4,v5] .nil .nil) .nil)) (.node [v330,v0,v1,v2,v3,v4,v109] (.node [v330,v0,v1,v2,v3,v4,v5] (.node [v330,v0,v1,v2,v111,v3,v4] .nil .nil) .nil) (.node [v330,v0,v1,v2,v3,v4,v99] .nil .nil)))) (.node [v481,v0,v1,v2,v107,v3,v4] (.node [v368,v0,v1,v2,v3,v4,v5] (.node [v137,v0,v1,v2,v3,v4,v5] (.node [v330,v0,v1,v2,v4,v5,v104] (.node [v330,v0,v1,v2,v3,v99] .nil .nil) .nil) (.node [v100,v0,v1,v2,v3,v4,v5] (.node [v101,v0,v1,v2,v3,v4,v5] .nil .nil) .nil)) (.node [v98,v0,v1,v2,v3,v4,v5] (.node [v367,v0,v1,v2,v3,v4,v5] (.node [v369,v0,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v98,v0,v1,v2,v3,v4,v99] .nil .nil))) (.node [v105,v0,v1,v2,v107,v3] (.node [v479,v0,v1,v2,v3,v4,v5] (.node [v479,v0,v1,v2,v107,v3,v4] (.node [v481,v0,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v484,v0,v1,v2,v3,v4,v5] (.node [v484,v0,v1,v2,v107,v3,v4] .nil .nil) .nil)) (.node [v105,v0,v1,v2,v3,v4,v5] (.node [v105,v0,v1,v2,v107,v3,v5] (.node [v105,v0,v1,v2,v107,v3,v4] .nil .nil) .nil) (.node [v105,v0,v1,v2,v3,v5] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6lrllr : everyKey (rowOK 5 tree_5) tree_6lrllr = true := by decide +kernel
def tree_6lrll : BinaryTree (List W) := .node [v92,v0,v1,v2,v3,v4,v99] tree_6lrlll tree_6lrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6lrll : everyKey (rowOK 5 tree_5) tree_6lrll = true := by
  change (_ && everyKey _ tree_6lrlll && everyKey _ tree_6lrllr) = true
  rw [ok_tree_6lrlll, ok_tree_6lrllr]
  decide +kernel
def tree_6lrlrl : BinaryTree (List W) := (.node [v115,v21,v1,v2,v3,v4,v5] (.node [v1132,v0,v1,v2,v3,v4,v5] (.node [v108,v0,v1,v2,v3,v4,v5] (.node [v1133,v0,v1,v2,v3,v4,v5] (.node [v1134,v0,v1,v2,v3,v4,v5] (.node [v1135,v0,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v108,v0,v1,v2,v3,v4] (.node [v108,v0,v1,v2,v192,v3,v4] .nil .nil) .nil)) (.node [v1136,v0,v1,v2,v3,v4,v5] (.node [v1137,v0,v1,v2,v3,v4,v5] (.node [v1138,v0,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v502,v0,v1,v2,v3,v4,v5] .nil .nil))) (.node [v504,v0,v1,v2,v3,v4,v5] (.node [v512,v0,v1,v2,v3,v4,v5] (.node [v1139,v0,v1,v2,v3,v4,v5] (.node [v1140,v0,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v1141,v0,v1,v2,v3,v4,v5] (.node [v1142,v0,v1,v2,v3,v4,v5] .nil .nil) .nil)) (.node [v115,v130,v0,v2,v3,v4,v5] (.node [v115,v123,v1,v2,v3,v4,v5] (.node [v1143,v0,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v115,v164,v1,v2,v3,v4,v5] .nil .nil)))) (.node [v115,v1,v2,v121,v3,v4,v5] (.node [v115,v0,v1,v2,v3,v4,v99] (.node [v115,v0,v32,v2,v3,v4,v5] (.node [v115,v0,v166,v2,v3,v4,v5] (.node [v115,v0,v93,v2,v3,v4,v5] .nil .nil) .nil) (.node [v115,v0,v1,v2,v3,v4,v5] (.node [v115,v0,v1,v2,v107,v3,v4] .nil .nil) .nil)) (.node [v115,v1,v84,v2,v3,v4,v5] (.node [v115,v0,v2,v119,v3,v4,v5] (.node [v115,v0,v120,v2,v3,v4,v5] .nil .nil) .nil) (.node [v115,v1,v120,v2,v3,v4,v5] .nil .nil))) (.node [v1144,v0,v1,v2,v3,v4,v5] (.node [v1145,v0,v1,v2,v3,v4,v5] (.node [v1146,v0,v1,v2,v3,v4,v5] (.node [v115,v120,v2,v3,v4,v5] .nil .nil) .nil) (.node [v1147,v0,v1,v2,v3,v4,v5] (.node [v1148,v0,v1,v2,v3,v4,v5] .nil .nil) .nil)) (.node [v1149,v0,v1,v2,v3,v4,v5] (.node [v1150,v0,v1,v2,v3,v4,v5] (.node [v1151,v0,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v1152,v0,v1,v2,v3,v4,v5] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6lrlrl : everyKey (rowOK 5 tree_5) tree_6lrlrl = true := by decide +kernel
def tree_6lrlrr : BinaryTree (List W) := (.node [v1153,v0,v1,v2,v3,v4,v5] (.node [v123,v0,v288,v2,v3,v4,v5] (.node [v123,v0,v1,v2,v107,v3,v4] (.node [v123,v0,v223,v2,v3,v4,v5] (.node [v123,v0,v132,v1,v3,v4,v5] (.node [v123,v158,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v123,v0,v1,v41,v3,v4,v5] (.node [v123,v0,v1,v124,v3,v4,v5] .nil .nil) .nil)) (.node [v123,v0,v1,v121,v3,v4,v5] (.node [v123,v0,v1,v2,v3,v4,v99] (.node [v123,v0,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v123,v0,v1,v119,v3,v4,v5] .nil .nil))) (.node [v1154,v0,v1,v2,v3,v4,v5] (.node [v123,v1,v124,v3,v4,v5] (.node [v123,v1,v124,v2,v3,v4,v5] (.node [v123,v166,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v513,v0,v1,v2,v3,v4,v5] (.node [v1155,v0,v1,v2,v3,v4,v5] .nil .nil) .nil)) (.node [v113,v1,v2,v3,v4,v5] (.node [v113,v132,v1,v2,v3,v4,v5] (.node [v113,v0,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v1156,v0,v1,v2,v3,v4,v5] .nil .nil)))) (.node [v130,v0,v1,v2,v107,v3,v4] (.node [v130,v0,v132,v2,v3,v4,v5] (.node [v130,v164,v0,v2,v3,v4,v5] (.node [v130,v95,v0,v1,v3,v4,v5] (.node [v1157,v0,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v130,v0,v132,v1,v3,v4,v5] (.node [v130,v163,v1,v2,v3,v4,v5] .nil .nil) .nil)) (.node [v130,v0,v1,v124,v3,v4,v5] (.node [v130,v0,v212,v2,v3,v4,v5] (.node [v130,v0,v132,v3,v4,v5] .nil .nil) .nil) (.node [v130,v0,v1,v41,v3,v4,v5] .nil .nil))) (.node [v1158,v0,v1,v2,v3,v4,v5] (.node [v130,v0,v1,v121,v3,v4,v5] (.node [v130,v0,v1,v2,v3,v4,v99] (.node [v130,v0,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v130,v293,v1,v2,v3,v4,v5] (.node [v130,v0,v1,v119,v3,v4,v5] .nil .nil) .nil)) (.node [v129,v0,v1,v2,v3,v4,v5] (.node [v1159,v0,v1,v2,v3,v4,v5] (.node [v521,v0,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v129,v0,v124,v2,v3,v4,v5] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6lrlrr : everyKey (rowOK 5 tree_5) tree_6lrlrr = true := by decide +kernel
def tree_6lrlr : BinaryTree (List W) := .node [v123,v95,v0,v1,v3,v4,v5] tree_6lrlrl tree_6lrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6lrlr : everyKey (rowOK 5 tree_5) tree_6lrlr = true := by
  change (_ && everyKey _ tree_6lrlrl && everyKey _ tree_6lrlrr) = true
  rw [ok_tree_6lrlrl, ok_tree_6lrlrr]
  decide +kernel
def tree_6lrl : BinaryTree (List W) := .node [v14,v0,v1,v2,v3,v4,v5] tree_6lrll tree_6lrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6lrl : everyKey (rowOK 5 tree_5) tree_6lrl = true := by
  change (_ && everyKey _ tree_6lrll && everyKey _ tree_6lrlr) = true
  rw [ok_tree_6lrll, ok_tree_6lrlr]
  decide +kernel
def tree_6lrrll : BinaryTree (List W) := (.node [v356,v0,v1,v3,v4,v5,v548] (.node [v440,v0,v1,v2,v3,v4,v5] (.node [v354,v0,v1,v2,v146,v3,v4] (.node [v354,v95,v0,v1,v3,v4,v5] (.node [v1160,v0,v1,v2,v3,v4,v5] (.node [v1161,v0,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v354,v0,v1,v242,v2,v3,v5] (.node [v354,v0,v1,v41,v3,v4,v5] .nil .nil) .nil)) (.node [v354,v0,v1,v2,v3,v4,v147] (.node [v354,v0,v1,v2,v3,v4,v5] (.node [v354,v0,v1,v2,v107,v3,v4] .nil .nil) .nil) (.node [v354,v0,v1,v3,v4,v377,v5] (.node [v354,v0,v1,v2,v3,v4,v99] .nil .nil) .nil))) (.node [v356,v0,v1,v546,v2,v3,v4] (.node [v485,v0,v1,v2,v107,v3,v4] (.node [v1162,v0,v1,v2,v3,v4,v5] (.node [v1163,v0,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v356,v0,v1,v142,v2,v3,v5] (.node [v485,v0,v1,v2,v3,v4,v5] .nil .nil) .nil)) (.node [v356,v0,v1,v2,v3,v4,v99] (.node [v356,v0,v1,v2,v3,v4,v5] (.node [v356,v0,v1,v2,v107,v3,v4] .nil .nil) .nil) (.node [v356,v0,v1,v2,v3,v145,v5] .nil .nil)))) (.node [v95,v0,v1,v3,v4,v5,v244] (.node [v95,v0,v1,v41,v2,v4,v5] (.node [v127,v0,v1,v2,v3,v4,v5] (.node [v1164,v0,v1,v2,v3,v4,v5] (.node [v1165,v0,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v95,v0,v212,v1,v3,v4,v5] (.node [v95,v158,v0,v1,v3,v4,v5] .nil .nil) .nil)) (.node [v95,v0,v1,v2,v3,v4,v5] (.node [v95,v0,v1,v2,v107,v3,v4] (.node [v95,v0,v1,v242,v3,v4,v5] .nil .nil) .nil) (.node [v95,v0,v1,v2,v3,v4,v99] .nil .nil))) (.node [v135,v0,v1,v3,v4,v5,v226] (.node [v136,v0,v1,v3,v4,v5,v169] (.node [v136,v0,v1,v3,v4,v5] (.node [v136,v0,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v135,v0,v1,v3,v4,v5] (.node [v135,v0,v1,v2,v3,v4,v5] .nil .nil) .nil)) (.node [v13,v0,v1,v2,v3,v4,v5] (.node [v327,v0,v1,v2,v3,v4,v99] (.node [v327,v0,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v13,v0,v1,v3,v4,v5] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6lrrll : everyKey (rowOK 5 tree_5) tree_6lrrll = true := by decide +kernel
def tree_6lrrlr : BinaryTree (List W) := (.node [v158,v0,v1,v2,v107,v3,v4] (.node [v507,v0,v1,v2,v3,v4,v5] (.node [v1166,v0,v1,v2,v3,v4,v5] (.node [v144,v0,v1,v242,v2,v3,v4] (.node [v547,v0,v1,v2,v3,v4,v5] (.node [v1167,v0,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v144,v0,v1,v2,v3,v4,v5] (.node [v144,v0,v1,v2,v3,v4] .nil .nil) .nil)) (.node [v1168,v0,v1,v2,v3,v4,v5] (.node [v1169,v0,v1,v2,v3,v4,v5] (.node [v552,v0,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v1170,v0,v1,v2,v3,v4,v5] .nil .nil))) (.node [v158,v164,v1,v2,v3,v4,v5] (.node [v1171,v0,v1,v2,v3,v4,v5] (.node [v1172,v0,v1,v2,v3,v4,v5] (.node [v1173,v0,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v1174,v0,v1,v2,v3,v4,v5] (.node [v557,v0,v1,v2,v3,v4,v5] .nil .nil) .nil)) (.node [v158,v0,v1,v124,v3,v4,v5] (.node [v158,v0,v132,v1,v3,v4,v5] (.node [v158,v21,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v158,v0,v1,v41,v3,v4,v5] .nil .nil)))) (.node [v1175,v0,v1,v2,v3,v4,v5] (.node [v158,v1,v120,v2,v3,v4,v5] (.node [v158,v0,v1,v121,v3,v4,v5] (.node [v158,v0,v1,v2,v3,v4,v99] (.node [v158,v0,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v158,v1,v84,v2,v3,v4,v5] (.node [v158,v0,v1,v119,v3,v4,v5] .nil .nil) .nil)) (.node [v1176,v0,v1,v2,v3,v4,v5] (.node [v158,v1,v121,v3,v4,v5] (.node [v158,v1,v2,v121,v3,v4,v5] .nil .nil) .nil) (.node [v1177,v0,v1,v2,v3,v4,v5] .nil .nil))) (.node [v1178,v0,v1,v2,v3,v4,v5] (.node [v1179,v0,v1,v2,v3,v4,v5] (.node [v1180,v0,v1,v2,v3,v4,v5] (.node [v1181,v0,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v1182,v0,v1,v2,v3,v4,v5] (.node [v1183,v0,v1,v2,v3,v4,v5] .nil .nil) .nil)) (.node [v164,v0,v32,v2,v3,v4,v5] (.node [v164,v0,v166,v2,v3,v4,v5] (.node [v164,v0,v93,v2,v3,v4,v5] .nil .nil) .nil) (.node [v164,v0,v1,v241,v3,v4,v5] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6lrrlr : everyKey (rowOK 5 tree_5) tree_6lrrlr = true := by decide +kernel
def tree_6lrrl : BinaryTree (List W) := .node [v13,v0,v1,v3,v4,v5,v104] tree_6lrrll tree_6lrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6lrrl : everyKey (rowOK 5 tree_5) tree_6lrrl = true := by
  change (_ && everyKey _ tree_6lrrll && everyKey _ tree_6lrrlr) = true
  rw [ok_tree_6lrrll, ok_tree_6lrrlr]
  decide +kernel
def tree_6lrrrl : BinaryTree (List W) := (.node [v21,v0,v1,v2,v3,v4,v5] (.node [v1184,v0,v1,v2,v3,v4,v5] (.node [v164,v166,v1,v2,v3,v4,v5] (.node [v164,v0,v1,v134,v3,v4,v5] (.node [v164,v0,v1,v2,v3,v4,v99] (.node [v164,v0,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v164,v0,v2,v119,v3,v4,v5] (.node [v164,v0,v120,v2,v3,v4,v5] .nil .nil) .nil)) (.node [v1185,v0,v1,v2,v3,v4,v5] (.node [v164,v1,v124,v2,v3,v4,v5] (.node [v164,v166,v2,v3,v4,v5] .nil .nil) .nil) (.node [v562,v0,v1,v2,v3,v4,v5] .nil .nil))) (.node [v571,v0,v1,v2,v107,v3,v4] (.node [v1186,v0,v1,v2,v3,v4,v5] (.node [v163,v1,v2,v3,v4,v5] (.node [v163,v0,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v172,v0,v1,v2,v3,v4,v5] (.node [v1187,v0,v1,v2,v3,v4,v5] .nil .nil) .nil)) (.node [v21,v0,v1,v84,v2,v4,v5] (.node [v21,v171,v1,v2,v3,v4,v5] (.node [v571,v0,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v21,v0,v1,v2,v107,v3,v4] .nil .nil)))) (.node [v1188,v0,v1,v2,v3,v4,v5] (.node [v21,v1,v2,v3,v4,v5,v169] (.node [v21,v166,v1,v2,v3,v4,v5] (.node [v21,v0,v1,v2,v4,v5,v169] (.node [v21,v0,v1,v2,v3,v4,v99] .nil .nil) .nil) (.node [v21,v1,v358,v2,v3,v4,v5] (.node [v21,v1,v124,v2,v3,v4,v5] .nil .nil) .nil)) (.node [v1189,v0,v1,v2,v3,v4,v5] (.node [v573,v0,v1,v2,v3,v4,v5] (.node [v21,v1,v2,v4,v5,v169] .nil .nil) .nil) (.node [v1190,v0,v1,v2,v3,v4,v5] .nil .nil))) (.node [v171,v0,v1,v2,v192,v3,v5] (.node [v576,v0,v1,v2,v3,v4,v5] (.node [v1191,v0,v1,v2,v3,v4,v5] (.node [v578,v0,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v171,v0,v1,v307,v2,v3,v4] (.node [v171,v0,v1,v358,v2,v3,v5] .nil .nil) .nil)) (.node [v171,v0,v1,v2,v3,v4,v312] (.node [v171,v0,v1,v2,v3,v4,v5] (.node [v171,v0,v1,v2,v107,v3,v4] .nil .nil) .nil) (.node [v171,v0,v1,v2,v3,v4,v99] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6lrrrl : everyKey (rowOK 5 tree_5) tree_6lrrrl = true := by decide +kernel
def tree_6lrrrr : BinaryTree (List W) := (.node [v589,v1,v2,v3,v4,v590] (.node [v183,v0,v1,v2,v3,v5] (.node [v1192,v0,v1,v2,v3,v4,v5] (.node [v171,v1,v84,v2,v3,v4,v5] (.node [v171,v0,v1,v2,v3,v99] (.node [v171,v0,v1,v2,v3,v5,v99] .nil .nil) .nil) (.node [v171,v1,v2,v3,v371,v5] (.node [v171,v1,v2,v3,v4,v371,v5] .nil .nil) .nil)) (.node [v183,v0,v1,v341,v2,v3,v5] (.node [v178,v0,v1,v2,v3,v4,v5] (.node [v582,v0,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v183,v0,v1,v2,v3,v4,v5] .nil .nil))) (.node [v589,v0,v1,v2,v107,v3,v4] (.node [v1193,v0,v1,v2,v3,v4,v5] (.node [v584,v0,v1,v2,v3,v4,v5] (.node [v585,v0,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v589,v0,v1,v341,v2,v3,v4] (.node [v1194,v0,v1,v2,v3,v4,v5] .nil .nil) .nil)) (.node [v589,v0,v1,v2,v3,v4,v99] (.node [v589,v0,v1,v2,v3,v4,v590] (.node [v589,v0,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v589,v1,v2,v3,v4,v5,v590] .nil .nil)))) (.node [v186,v0,v1,v2,v3,v4,v5] (.node [v1195,v0,v1,v2,v3,v4,v5] (.node [v353,v0,v1,v2,v3,v4,v5] (.node [v1196,v0,v1,v2,v3,v4,v5] (.node [v1197,v0,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v1198,v0,v1,v2,v3,v4,v5] (.node [v1199,v0,v1,v2,v3,v4,v5] .nil .nil) .nil)) (.node [v188,v0,v1,v2,v3,v4,v5] (.node [v1200,v0,v1,v2,v3,v4,v5] (.node [v1201,v0,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v188,v0,v1,v2,v3,v4,v99] .nil .nil))) (.node [v8,v0,v1,v2,v3,v4,v5] (.node [v151,v0,v1,v2,v3,v4,v5] (.node [v186,v1,v2,v3,v4,v5,v226] (.node [v186,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v151,v1,v2,v3,v4,v5,v244] (.node [v151,v1,v2,v3,v4,v5] .nil .nil) .nil)) (.node [v0,v0,v1,v2,v3,v4,v5] (.node [v8,v1,v2,v3,v4,v5,v104] (.node [v8,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v0,v1202,v1,v2,v3,v4,v5] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6lrrrr : everyKey (rowOK 5 tree_5) tree_6lrrrr = true := by decide +kernel
def tree_6lrrr : BinaryTree (List W) := .node [v171,v0,v1,v2,v3,v371,v5] tree_6lrrrl tree_6lrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6lrrr : everyKey (rowOK 5 tree_5) tree_6lrrr = true := by
  change (_ && everyKey _ tree_6lrrrl && everyKey _ tree_6lrrrr) = true
  rw [ok_tree_6lrrrl, ok_tree_6lrrrr]
  decide +kernel
def tree_6lrr : BinaryTree (List W) := .node [v164,v0,v1,v2,v107,v3,v4] tree_6lrrl tree_6lrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6lrr : everyKey (rowOK 5 tree_5) tree_6lrr = true := by
  change (_ && everyKey _ tree_6lrrl && everyKey _ tree_6lrrr) = true
  rw [ok_tree_6lrrl, ok_tree_6lrrr]
  decide +kernel
def tree_6lr : BinaryTree (List W) := .node [v129,v0,v2,v3,v4,v5] tree_6lrl tree_6lrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6lr : everyKey (rowOK 5 tree_5) tree_6lr = true := by
  change (_ && everyKey _ tree_6lrl && everyKey _ tree_6lrr) = true
  rw [ok_tree_6lrl, ok_tree_6lrr]
  decide +kernel
def tree_6l : BinaryTree (List W) := .node [v461,v0,v1,v2,v3,v4,v5] tree_6ll tree_6lr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6l : everyKey (rowOK 5 tree_5) tree_6l = true := by
  change (_ && everyKey _ tree_6ll && everyKey _ tree_6lr) = true
  rw [ok_tree_6ll, ok_tree_6lr]
  decide +kernel
def tree_6rllll : BinaryTree (List W) := (.node [v0,v1203,v1,v2,v3,v4,v5] (.node [v0,v418,v1,v2,v3,v4,v5] (.node [v0,v337,v1,v2,v3,v4,v5] (.node [v0,v1204,v1,v2,v3,v4,v5] (.node [v0,v1205,v1,v2,v3,v4,v5] (.node [v0,v1206,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v0,v580,v1,v2,v3,v4,v5] (.node [v0,v1207,v1,v2,v3,v4,v5] .nil .nil) .nil)) (.node [v0,v297,v1,v358,v2,v3,v4] (.node [v0,v1208,v1,v2,v3,v4,v5] (.node [v0,v1209,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v0,v297,v1,v2,v3,v4,v5] (.node [v0,v297,v1,v2,v3,v4] .nil .nil) .nil))) (.node [v0,v1210,v1,v2,v3,v4,v5] (.node [v0,v609,v1,v2,v3,v4,v5] (.node [v0,v1211,v1,v2,v3,v4,v5] (.node [v0,v421,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v0,v1212,v1,v2,v3,v4,v5] (.node [v0,v1213,v1,v2,v3,v4,v5] .nil .nil) .nil)) (.node [v0,v1214,v1,v2,v3,v4,v5] (.node [v0,v511,v1,v2,v3,v4,v5] (.node [v0,v293,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v0,v1215,v1,v2,v3,v4,v5] .nil .nil)))) (.node [v0,v617,v1,v2,v3,v4,v5] (.node [v0,v132,v1,v2,v3,v4,v5] (.node [v0,v132,v166,v2,v3,v4,v5] (.node [v0,v132,v212,v1,v3,v4,v5] (.node [v0,v132,v93,v2,v3,v4,v5] .nil .nil) .nil) (.node [v0,v132,v1,v2,v107,v3,v4] (.node [v0,v132,v32,v2,v3,v4,v5] .nil .nil) .nil)) (.node [v0,v132,v2,v119,v3,v4,v5] (.node [v0,v132,v120,v2,v3,v4,v5] (.node [v0,v132,v1,v2,v3,v4,v99] .nil .nil) .nil) (.node [v0,v1216,v1,v2,v3,v4,v5] .nil .nil))) (.node [v0,v1217,v1,v2,v3,v4,v5] (.node [v0,v195,v1,v2,v3,v4,v5] (.node [v0,v195,v166,v1,v3,v4,v5] (.node [v0,v1218,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v0,v1219,v1,v2,v3,v4,v5] (.node [v0,v195,v1,v3,v4,v5] .nil .nil) .nil)) (.node [v0,v362,v220,v1,v2,v3,v5] (.node [v0,v362,v32,v2,v3,v4,v5] (.node [v0,v362,v93,v2,v3,v4,v5] .nil .nil) .nil) (.node [v0,v362,v1,v206,v2,v3,v4] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6rllll : everyKey (rowOK 5 tree_5) tree_6rllll = true := by decide +kernel
def tree_6rlllr : BinaryTree (List W) := (.node [v0,v93,v1,v2,v107,v3,v4] (.node [v0,v345,v639,v1,v2,v3,v4] (.node [v0,v1220,v1,v2,v3,v4,v5] (.node [v0,v362,v1,v2,v3,v4,v99] (.node [v0,v362,v1,v2,v3,v4,v209] (.node [v0,v362,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v0,v441,v1,v2,v3,v4,v5] (.node [v0,v362,v2,v3,v4,v372,v5] .nil .nil) .nil)) (.node [v0,v480,v1,v2,v3,v4,v5] (.node [v0,v480,v1,v2,v107,v3,v4] (.node [v0,v1221,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v0,v345,v204,v1,v2,v3,v5] .nil .nil))) (.node [v0,v1222,v1,v2,v3,v4,v5] (.node [v0,v345,v1,v2,v3,v4,v99] (.node [v0,v345,v1,v2,v3,v4,v5] (.node [v0,v345,v1,v2,v107,v3,v4] .nil .nil) .nil) (.node [v0,v345,v2,v3,v4,v5,v641] (.node [v0,v345,v1,v2,v3,v203,v5] .nil .nil) .nil)) (.node [v0,v93,v32,v1,v2,v4,v5] (.node [v0,v93,v212,v2,v3,v4,v5] (.node [v0,v1223,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v0,v93,v220,v2,v3,v4,v5] .nil .nil)))) (.node [v0,v329,v1,v2,v3,v4,v5] (.node [v0,v200,v2,v3,v4,v5,v169] (.node [v0,v93,v2,v3,v4,v5,v226] (.node [v0,v93,v1,v2,v3,v4,v99] (.node [v0,v93,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v0,v200,v2,v3,v4,v5] (.node [v0,v200,v1,v2,v3,v4,v5] .nil .nil) .nil)) (.node [v0,v149,v2,v3,v4,v5] (.node [v0,v149,v1,v2,v3,v4,v5] (.node [v0,v299,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v0,v149,v2,v3,v4,v5,v244] .nil .nil))) (.node [v0,v640,v1,v2,v3,v4,v5] (.node [v0,v23,v2,v3,v4,v5] (.node [v0,v23,v1,v2,v3,v4,v5] (.node [v0,v329,v1,v2,v3,v4,v99] .nil .nil) .nil) (.node [v0,v1224,v1,v2,v3,v4,v5] (.node [v0,v23,v2,v3,v4,v5,v104] .nil .nil) .nil)) (.node [v0,v207,v1,v2,v3,v4,v5] (.node [v0,v207,v1,v2,v3,v4] (.node [v0,v207,v220,v1,v2,v3,v4] .nil .nil) .nil) (.node [v0,v1225,v1,v2,v3,v4,v5] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6rlllr : everyKey (rowOK 5 tree_5) tree_6rlllr = true := by decide +kernel
def tree_6rlll : BinaryTree (List W) := .node [v0,v362,v1,v2,v107,v3,v4] tree_6rllll tree_6rlllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6rlll : everyKey (rowOK 5 tree_5) tree_6rlll = true := by
  change (_ && everyKey _ tree_6rllll && everyKey _ tree_6rlllr) = true
  rw [ok_tree_6rllll, ok_tree_6rlllr]
  decide +kernel
def tree_6rllrl : BinaryTree (List W) := (.node [v0,v212,v1,v121,v3,v4,v5] (.node [v0,v1226,v1,v2,v3,v4,v5] (.node [v0,v1227,v1,v2,v3,v4,v5] (.node [v0,v649,v1,v2,v3,v4,v5] (.node [v0,v1228,v1,v2,v3,v4,v5] (.node [v0,v1229,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v0,v1230,v1,v2,v3,v4,v5] (.node [v0,v1231,v1,v2,v3,v4,v5] .nil .nil) .nil)) (.node [v0,v1232,v1,v2,v3,v4,v5] (.node [v0,v303,v1,v2,v3,v4,v5] (.node [v0,v561,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v0,v1233,v1,v2,v3,v4,v5] (.node [v0,v1234,v1,v2,v3,v4,v5] .nil .nil) .nil))) (.node [v0,v212,v1,v124,v3,v4,v5] (.node [v0,v1235,v1,v2,v3,v4,v5] (.node [v0,v653,v1,v2,v3,v4,v5] (.node [v0,v1236,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v0,v212,v32,v2,v3,v4,v5] (.node [v0,v212,v166,v2,v3,v4,v5] .nil .nil) .nil)) (.node [v0,v212,v1,v2,v3,v4,v5] (.node [v0,v212,v1,v2,v107,v3,v4] (.node [v0,v212,v1,v41,v3,v4,v5] .nil .nil) .nil) (.node [v0,v212,v1,v2,v3,v4,v99] .nil .nil)))) (.node [v0,v1237,v1,v2,v3,v4,v5] (.node [v0,v1238,v1,v2,v3,v4,v5] (.node [v0,v212,v2,v119,v3,v4,v5] (.node [v0,v212,v120,v2,v3,v4,v5] (.node [v0,v212,v1,v119,v3,v4,v5] .nil .nil) .nil) (.node [v0,v1239,v1,v2,v3,v4,v5] (.node [v0,v212,v119,v3,v4,v5] .nil .nil) .nil)) (.node [v0,v1240,v1,v2,v3,v4,v5] (.node [v0,v1241,v1,v2,v3,v4,v5] (.node [v0,v1242,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v0,v1243,v1,v2,v3,v4,v5] .nil .nil))) (.node [v0,v166,v1,v114,v3,v4,v5] (.node [v0,v166,v1,v2,v107,v3,v4] (.node [v0,v1244,v1,v2,v3,v4,v5] (.node [v0,v1245,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v0,v166,v1,v2,v3,v4,v99] (.node [v0,v166,v1,v2,v3,v4,v5] .nil .nil) .nil)) (.node [v0,v1246,v1,v2,v3,v4,v5] (.node [v0,v658,v1,v2,v3,v4,v5] (.node [v0,v1247,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v0,v223,v1,v2,v3,v4,v5] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6rllrl : everyKey (rowOK 5 tree_5) tree_6rllrl = true := by decide +kernel
def tree_6rllrr : BinaryTree (List W) := (.node [v0,v220,v1,v2,v3,v4,v5] (.node [v0,v32,v2,v3,v4,v5,v226] (.node [v0,v32,v220,v2,v3,v4,v5] (.node [v0,v300,v1,v2,v3,v4,v5] (.node [v0,v1248,v1,v2,v3,v4,v5] (.node [v0,v1249,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v0,v661,v1,v2,v3,v4,v5] (.node [v0,v661,v1,v2,v107,v3,v4] .nil .nil) .nil)) (.node [v0,v32,v1,v2,v3,v4,v99] (.node [v0,v32,v1,v2,v3,v4,v5] (.node [v0,v32,v1,v2,v107,v3,v4] .nil .nil) .nil) (.node [v0,v32,v1,v2,v4,v5,v226] .nil .nil))) (.node [v0,v672,v1,v2,v3,v4,v5] (.node [v0,v1250,v1,v2,v3,v4,v5] (.node [v0,v668,v1,v2,v3,v4,v5] (.node [v0,v32,v2,v4,v5,v226] .nil .nil) .nil) (.node [v0,v1251,v1,v2,v3,v4,v5] (.node [v0,v1252,v1,v2,v3,v4,v5] .nil .nil) .nil)) (.node [v0,v220,v1,v2,v192,v3,v5] (.node [v0,v670,v1,v2,v3,v4,v5] (.node [v0,v1253,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v0,v220,v1,v2,v107,v3,v4] .nil .nil)))) (.node [v0,v204,v1,v2,v3,v4,v5] (.node [v0,v220,v2,v3,v4,v372,v5] (.node [v0,v220,v1,v2,v3,v372,v5] (.node [v0,v220,v1,v2,v3,v4,v99] (.node [v0,v220,v1,v2,v3,v4,v208] .nil .nil) .nil) (.node [v0,v220,v1,v2,v3,v99] (.node [v0,v220,v1,v2,v3,v5,v99] .nil .nil) .nil)) (.node [v0,v676,v1,v2,v3,v4,v5] (.node [v0,v1254,v1,v2,v3,v4,v5] (.node [v0,v220,v2,v3,v372,v5] .nil .nil) .nil) (.node [v0,v224,v1,v2,v3,v4,v5] .nil .nil))) (.node [v0,v639,v1,v2,v107,v3,v4] (.node [v0,v680,v1,v2,v3,v4,v5] (.node [v0,v679,v1,v2,v3,v4,v5] (.node [v0,v204,v1,v2,v3,v5] .nil .nil) .nil) (.node [v0,v1255,v1,v2,v3,v4,v5] (.node [v0,v1256,v1,v2,v3,v4,v5] .nil .nil) .nil)) (.node [v0,v639,v1,v2,v3,v4,v99] (.node [v0,v639,v1,v2,v3,v4,v641] (.node [v0,v639,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v0,v639,v2,v3,v4,v5,v641] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6rllrr : everyKey (rowOK 5 tree_5) tree_6rllrr = true := by decide +kernel
def tree_6rllr : BinaryTree (List W) := .node [v0,v223,v2,v3,v4,v5] tree_6rllrl tree_6rllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6rllr : everyKey (rowOK 5 tree_5) tree_6rllr = true := by
  change (_ && everyKey _ tree_6rllrl && everyKey _ tree_6rllrr) = true
  rw [ok_tree_6rllrl, ok_tree_6rllrr]
  decide +kernel
def tree_6rll : BinaryTree (List W) := .node [v0,v646,v1,v2,v3,v4,v5] tree_6rlll tree_6rllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6rll : everyKey (rowOK 5 tree_5) tree_6rll = true := by
  change (_ && everyKey _ tree_6rlll && everyKey _ tree_6rllr) = true
  rw [ok_tree_6rlll, ok_tree_6rllr]
  decide +kernel
def tree_6rlrll : BinaryTree (List W) := (.node [v0,v1,v1257,v2,v3,v4,v5] (.node [v0,v174,v2,v3,v4,v5] (.node [v0,v1258,v1,v2,v3,v4,v5] (.node [v0,v334,v1,v2,v3,v4,v5] (.node [v0,v1259,v1,v2,v3,v4,v5] (.node [v0,v1260,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v0,v1261,v1,v2,v3,v4,v5] (.node [v0,v1262,v1,v2,v3,v4,v5] .nil .nil) .nil)) (.node [v0,v230,v1,v2,v3,v4,v5] (.node [v0,v1263,v1,v2,v3,v4,v5] (.node [v0,v1264,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v0,v174,v1,v2,v3,v4,v5] (.node [v0,v230,v1,v2,v3,v4,v99] .nil .nil) .nil))) (.node [v0,v9,v2,v3,v4,v5] (.node [v0,v152,v2,v3,v4,v5] (.node [v0,v152,v1,v2,v3,v4,v5] (.node [v0,v174,v2,v3,v4,v5,v169] .nil .nil) .nil) (.node [v0,v9,v1,v2,v3,v4,v5] (.node [v0,v152,v2,v3,v4,v5,v244] .nil .nil) .nil)) (.node [v0,v1,v1265,v2,v3,v4,v5] (.node [v0,v1,v1,v2,v3,v4,v5] (.node [v0,v9,v2,v3,v4,v5,v104] .nil .nil) .nil) (.node [v0,v1,v1266,v2,v3,v4,v5] .nil .nil)))) (.node [v0,v1,v426,v2,v3,v4,v5] (.node [v0,v1,v1267,v2,v3,v4,v5] (.node [v0,v1,v1268,v2,v3,v4,v5] (.node [v0,v1,v1269,v2,v3,v4,v5] (.node [v0,v1,v1270,v2,v3,v4,v5] .nil .nil) .nil) (.node [v0,v1,v347,v2,v3,v4,v5] (.node [v0,v1,v674,v2,v3,v4,v5] .nil .nil) .nil)) (.node [v0,v1,v206,v2,v3,v4,v5] (.node [v0,v1,v206,v2,v3,v4] (.node [v0,v1,v1271,v2,v3,v4,v5] .nil .nil) .nil) (.node [v0,v1,v423,v2,v3,v4,v5] .nil .nil))) (.node [v0,v1,v288,v2,v3,v4,v5] (.node [v0,v1,v1272,v2,v3,v4,v5] (.node [v0,v1,v704,v2,v3,v4,v5] (.node [v0,v1,v1273,v2,v3,v4,v5] .nil .nil) .nil) (.node [v0,v1,v1274,v2,v3,v4,v5] (.node [v0,v1,v1275,v2,v3,v4,v5] .nil .nil) .nil)) (.node [v0,v1,v1276,v2,v3,v4,v5] (.node [v0,v1,v1277,v2,v3,v4,v5] (.node [v0,v1,v522,v2,v3,v4,v5] .nil .nil) .nil) (.node [v0,v1,v1278,v2,v3,v4,v5] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6rlrll : everyKey (rowOK 5 tree_5) tree_6rlrll = true := by decide +kernel
def tree_6rlrlr : BinaryTree (List W) := (.node [v0,v1,v341,v2,v3,v179,v5] (.node [v0,v1,v358,v2,v3,v4,v5] (.node [v0,v1,v241,v2,v3,v4,v5] (.node [v0,v1,v1279,v2,v3,v4,v5] (.node [v0,v1,v124,v2,v3,v4,v99] (.node [v0,v1,v124,v2,v3,v4,v5] .nil .nil) .nil) (.node [v0,v1,v1280,v2,v3,v4,v5] (.node [v0,v1,v706,v2,v3,v4,v5] .nil .nil) .nil)) (.node [v0,v1,v1281,v2,v3,v4,v5] (.node [v0,v1,v1282,v2,v3,v4,v5] (.node [v0,v1,v241,v3,v4,v5] .nil .nil) .nil) (.node [v0,v1,v358,v2,v107,v3,v4] .nil .nil))) (.node [v0,v1,v483,v2,v107,v3,v4] (.node [v0,v1,v443,v2,v3,v4,v5] (.node [v0,v1,v358,v2,v3,v4,v99] (.node [v0,v1,v358,v2,v3,v4,v311] .nil .nil) .nil) (.node [v0,v1,v1283,v2,v3,v4,v5] (.node [v0,v1,v1284,v2,v3,v4,v5] .nil .nil) .nil)) (.node [v0,v1,v341,v2,v3,v4,v5] (.node [v0,v1,v341,v2,v107,v3,v4] (.node [v0,v1,v483,v2,v3,v4,v5] .nil .nil) .nil) (.node [v0,v1,v341,v2,v3,v4,v99] .nil .nil)))) (.node [v0,v1,v45,v2,v3,v4,v5] (.node [v0,v1,v306,v2,v3,v4,v5] (.node [v0,v1,v84,v2,v107,v3,v4] (.node [v0,v1,v1285,v2,v3,v4,v5] (.node [v0,v1,v1286,v2,v3,v4,v5] .nil .nil) .nil) (.node [v0,v1,v84,v2,v3,v4,v99] (.node [v0,v1,v84,v2,v3,v4,v5] .nil .nil) .nil)) (.node [v0,v1,v323,v2,v3,v4,v5] (.node [v0,v1,v156,v2,v3,v4,v5] (.node [v0,v1,v173,v2,v3,v4,v5] .nil .nil) .nil) (.node [v0,v1,v323,v2,v3,v4,v99] .nil .nil))) (.node [v0,v1,v730,v2,v3,v4,v5] (.node [v0,v1,v307,v2,v3,v4] (.node [v0,v1,v715,v2,v3,v4,v5] (.node [v0,v1,v1287,v2,v3,v4,v5] .nil .nil) .nil) (.node [v0,v1,v1288,v2,v3,v4,v5] (.node [v0,v1,v307,v2,v3,v4,v5] .nil .nil) .nil)) (.node [v0,v1,v722,v2,v3,v4,v5] (.node [v0,v1,v1289,v2,v3,v4,v5] (.node [v0,v1,v1290,v2,v3,v4,v5] .nil .nil) .nil) (.node [v0,v1,v1291,v2,v3,v4,v5] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6rlrlr : everyKey (rowOK 5 tree_5) tree_6rlrlr = true := by decide +kernel
def tree_6rlrl : BinaryTree (List W) := .node [v0,v1,v124,v2,v107,v3,v4] tree_6rlrll tree_6rlrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6rlrl : everyKey (rowOK 5 tree_5) tree_6rlrl = true := by
  change (_ && everyKey _ tree_6rlrll && everyKey _ tree_6rlrlr) = true
  rw [ok_tree_6rlrll, ok_tree_6rlrlr]
  decide +kernel
def tree_6rlrrl : BinaryTree (List W) := (.node [v0,v1,v1292,v2,v3,v4,v5] (.node [v0,v1,v726,v2,v3,v4,v5] (.node [v0,v1,v1293,v2,v3,v4,v5] (.node [v0,v1,v168,v2,v3,v4,v5] (.node [v0,v1,v1055,v2,v3,v4,v5] (.node [v0,v1,v1294,v2,v3,v4,v5] .nil .nil) .nil) (.node [v0,v1,v1295,v2,v3,v4,v5] (.node [v0,v1,v1296,v2,v3,v4,v5] .nil .nil) .nil)) (.node [v0,v1,v1297,v2,v3,v4,v5] (.node [v0,v1,v1298,v2,v3,v4,v5] (.node [v0,v1,v1299,v2,v3,v4,v5] .nil .nil) .nil) (.node [v0,v1,v508,v2,v3,v4,v5] .nil .nil))) (.node [v0,v1,v503,v2,v3,v4,v5] (.node [v0,v1,v1300,v2,v3,v4,v5] (.node [v0,v1,v1301,v2,v3,v4,v5] (.node [v0,v1,v1302,v2,v3,v4,v5] .nil .nil) .nil) (.node [v0,v1,v1303,v2,v3,v4,v5] (.node [v0,v1,v1304,v2,v3,v4,v5] .nil .nil) .nil)) (.node [v0,v1,v120,v2,v3,v4,v5] (.node [v0,v1,v120,v2,v107,v3,v4] (.node [v0,v1,v509,v2,v3,v4,v5] .nil .nil) .nil) (.node [v0,v1,v120,v2,v3,v4,v99] .nil .nil)))) (.node [v0,v1,v751,v2,v3,v4,v5] (.node [v0,v1,v41,v2,v3,v4,v5] (.node [v0,v1,v728,v2,v3,v4,v5] (.node [v0,v1,v728,v2,v107,v3,v4] (.node [v0,v1,v128,v2,v3,v4,v5] .nil .nil) .nil) (.node [v0,v1,v41,v2,v107,v3,v4] (.node [v0,v1,v41,v242,v3,v4,v5] .nil .nil) .nil)) (.node [v0,v1,v41,v3,v4,v5,v244] (.node [v0,v1,v41,v2,v4,v5,v244] (.node [v0,v1,v41,v2,v3,v4,v99] .nil .nil) .nil) (.node [v0,v1,v41,v4,v5,v244] .nil .nil))) (.node [v0,v1,v731,v2,v3,v4,v5] (.node [v0,v1,v1305,v2,v3,v4,v5] (.node [v0,v1,v1306,v2,v3,v4,v5] (.node [v0,v1,v1307,v2,v3,v4,v5] .nil .nil) .nil) (.node [v0,v1,v1308,v2,v3,v4,v5] (.node [v0,v1,v733,v2,v3,v4,v5] .nil .nil) .nil)) (.node [v0,v1,v242,v2,v3,v4,v5] (.node [v0,v1,v242,v2,v107,v3,v4] (.node [v0,v1,v242,v2,v192,v3,v5] .nil .nil) .nil) (.node [v0,v1,v242,v2,v3,v4,v138] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6rlrrl : everyKey (rowOK 5 tree_5) tree_6rlrrl = true := by decide +kernel
def tree_6rlrrr : BinaryTree (List W) := (.node [v0,v1,v1309,v2,v3,v4,v5] (.node [v0,v1,v738,v2,v3,v4,v5] (.node [v0,v1,v1310,v2,v3,v4,v5] (.node [v0,v1,v242,v2,v3,v99] (.node [v0,v1,v242,v2,v3,v5,v99] (.node [v0,v1,v242,v2,v3,v377,v5] .nil .nil) .nil) (.node [v0,v1,v242,v3,v377,v5] (.node [v0,v1,v242,v3,v4,v377,v5] .nil .nil) .nil)) (.node [v0,v1,v142,v2,v3,v4,v5] (.node [v0,v1,v248,v2,v3,v4,v5] (.node [v0,v1,v737,v2,v3,v4,v5] .nil .nil) .nil) (.node [v0,v1,v142,v2,v3,v5] .nil .nil))) (.node [v0,v1,v546,v2,v3,v4,v548] (.node [v0,v1,v1311,v2,v3,v4,v5] (.node [v0,v1,v1312,v2,v3,v4,v5] (.node [v0,v1,v741,v2,v3,v4,v5] .nil .nil) .nil) (.node [v0,v1,v546,v2,v3,v4,v5] (.node [v0,v1,v546,v2,v107,v3,v4] .nil .nil) .nil)) (.node [v0,v1,v546,v3,v4,v548] (.node [v0,v1,v546,v3,v4,v5,v548] (.node [v0,v1,v546,v2,v3,v4,v99] .nil .nil) .nil) (.node [v0,v1,v1313,v2,v3,v4,v5] .nil .nil)))) (.node [v0,v1,v175,v3,v4,v5,v169] (.node [v0,v1,v1314,v2,v3,v4,v5] (.node [v0,v1,v1315,v2,v3,v4,v5] (.node [v0,v1,v1316,v2,v3,v4,v5] (.node [v0,v1,v339,v2,v3,v4,v5] .nil .nil) .nil) (.node [v0,v1,v1317,v2,v3,v4,v5] (.node [v0,v1,v1318,v2,v3,v4,v5] .nil .nil) .nil)) (.node [v0,v1,v175,v2,v3,v4,v5] (.node [v0,v1,v253,v2,v3,v4,v99] (.node [v0,v1,v253,v2,v3,v4,v5] .nil .nil) .nil) (.node [v0,v1,v175,v3,v4,v5] .nil .nil))) (.node [v0,v1,v27,v3,v4,v5,v104] (.node [v0,v1,v187,v3,v4,v5,v226] (.node [v0,v1,v187,v3,v4,v5] (.node [v0,v1,v187,v2,v3,v4,v5] .nil .nil) .nil) (.node [v0,v1,v27,v3,v4,v5] (.node [v0,v1,v27,v2,v3,v4,v5] .nil .nil) .nil)) (.node [v0,v1,v2,v1319,v3,v4,v5] (.node [v0,v1,v2,v1320,v3,v4,v5] (.node [v0,v1,v2,v2,v3,v4,v5] .nil .nil) .nil) (.node [v0,v1,v2,v1321,v3,v4,v5] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6rlrrr : everyKey (rowOK 5 tree_5) tree_6rlrrr = true := by decide +kernel
def tree_6rlrr : BinaryTree (List W) := .node [v0,v1,v242,v2,v3,v4,v99] tree_6rlrrl tree_6rlrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6rlrr : everyKey (rowOK 5 tree_5) tree_6rlrr = true := by
  change (_ && everyKey _ tree_6rlrrl && everyKey _ tree_6rlrrr) = true
  rw [ok_tree_6rlrrl, ok_tree_6rlrrr]
  decide +kernel
def tree_6rlr : BinaryTree (List W) := .node [v0,v1,v1322,v2,v3,v4,v5] tree_6rlrl tree_6rlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6rlr : everyKey (rowOK 5 tree_5) tree_6rlr = true := by
  change (_ && everyKey _ tree_6rlrl && everyKey _ tree_6rlrr) = true
  rw [ok_tree_6rlrl, ok_tree_6rlrr]
  decide +kernel
def tree_6rl : BinaryTree (List W) := .node [v0,v639,v2,v3,v4,v641] tree_6rll tree_6rlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6rl : everyKey (rowOK 5 tree_5) tree_6rl = true := by
  change (_ && everyKey _ tree_6rll && everyKey _ tree_6rlr) = true
  rw [ok_tree_6rll, ok_tree_6rlr]
  decide +kernel
def tree_6rrlll : BinaryTree (List W) := (.node [v0,v1,v2,v114,v3,v4,v5] (.node [v0,v1,v2,v778,v3,v4,v5] (.node [v0,v1,v2,v1323,v3,v4,v5] (.node [v0,v1,v2,v735,v3,v4,v5] (.node [v0,v1,v2,v1324,v3,v4,v5] (.node [v0,v1,v2,v1325,v3,v4,v5] .nil .nil) .nil) (.node [v0,v1,v2,v1326,v3,v4,v5] (.node [v0,v1,v2,v360,v3,v4,v5] .nil .nil) .nil)) (.node [v0,v1,v2,v428,v3,v4,v5] (.node [v0,v1,v2,v146,v3,v4,v5] (.node [v0,v1,v2,v146,v3,v4] .nil .nil) .nil) (.node [v0,v1,v2,v1327,v3,v4,v5] (.node [v0,v1,v2,v430,v3,v4,v5] .nil .nil) .nil))) (.node [v0,v1,v2,v1328,v3,v4,v5] (.node [v0,v1,v2,v1329,v3,v4,v5] (.node [v0,v1,v2,v1330,v3,v4,v5] (.node [v0,v1,v2,v1331,v3,v4,v5] .nil .nil) .nil) (.node [v0,v1,v2,v615,v3,v4,v5] (.node [v0,v1,v2,v134,v3,v4,v5] .nil .nil) .nil)) (.node [v0,v1,v2,v1332,v3,v4,v5] (.node [v0,v1,v2,v1333,v3,v4,v5] (.node [v0,v1,v2,v769,v3,v4,v5] .nil .nil) .nil) (.node [v0,v1,v2,v1334,v3,v4,v5] .nil .nil)))) (.node [v0,v1,v2,v1335,v3,v4,v5] (.node [v0,v1,v2,v553,v3,v4,v5] (.node [v0,v1,v2,v1336,v3,v4,v5] (.node [v0,v1,v2,v1337,v3,v4,v5] (.node [v0,v1,v2,v1057,v3,v4,v5] .nil .nil) .nil) (.node [v0,v1,v2,v1338,v3,v4,v5] (.node [v0,v1,v2,v1339,v3,v4,v5] .nil .nil) .nil)) (.node [v0,v1,v2,v1340,v3,v4,v5] (.node [v0,v1,v2,v1341,v3,v4,v5] (.node [v0,v1,v2,v772,v3,v4,v5] .nil .nil) .nil) (.node [v0,v1,v2,v1342,v3,v4,v5] .nil .nil))) (.node [v0,v1,v2,v121,v3,v4,v99] (.node [v0,v1,v2,v559,v3,v4,v5] (.node [v0,v1,v2,v560,v3,v4,v5] (.node [v0,v1,v2,v1343,v3,v4,v5] .nil .nil) .nil) (.node [v0,v1,v2,v121,v3,v4,v5] (.node [v0,v1,v2,v121,v107,v3,v4] .nil .nil) .nil)) (.node [v0,v1,v2,v1344,v3,v4,v5] (.node [v0,v1,v2,v775,v3,v4,v5] (.node [v0,v1,v2,v655,v3,v4,v5] .nil .nil) .nil) (.node [v0,v1,v2,v1345,v3,v4,v5] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6rrlll : everyKey (rowOK 5 tree_5) tree_6rrlll = true := by decide +kernel
def tree_6rrllr : BinaryTree (List W) := (.node [v0,v1,v2,v442,v3,v4,v5] (.node [v0,v1,v2,v192,v3,v4,v5] (.node [v0,v1,v2,v119,v3,v4,v5] (.node [v0,v1,v2,v654,v3,v4,v5] (.node [v0,v1,v2,v1346,v3,v4,v5] (.node [v0,v1,v2,v1347,v3,v4,v5] .nil .nil) .nil) (.node [v0,v1,v2,v119,v107,v3,v4] (.node [v0,v1,v2,v656,v3,v4,v5] .nil .nil) .nil)) (.node [v0,v1,v2,v764,v3,v4,v5] (.node [v0,v1,v2,v764,v107,v3,v4] (.node [v0,v1,v2,v119,v3,v4,v99] .nil .nil) .nil) (.node [v0,v1,v2,v192,v107,v3,v4] .nil .nil))) (.node [v0,v1,v2,v1348,v3,v4,v5] (.node [v0,v1,v2,v192,v3,v5,v104] (.node [v0,v1,v2,v192,v3,v4,v99] (.node [v0,v1,v2,v192,v3,v4,v112] .nil .nil) .nil) (.node [v0,v1,v2,v192,v5,v104] (.node [v0,v1,v2,v192,v4,v5,v104] .nil .nil) .nil)) (.node [v0,v1,v2,v260,v3,v4] (.node [v0,v1,v2,v1349,v3,v4,v5] (.node [v0,v1,v2,v1350,v3,v4,v5] .nil .nil) .nil) (.node [v0,v1,v2,v260,v3,v4,v5] .nil .nil)))) (.node [v0,v1,v2,v107,v3,v4,v371] (.node [v0,v1,v2,v243,v3,v4,v5] (.node [v0,v1,v2,v1351,v3,v4,v5] (.node [v0,v1,v2,v1352,v3,v4,v5] (.node [v0,v1,v2,v1353,v3,v4,v5] .nil .nil) .nil) (.node [v0,v1,v2,v227,v3,v4,v5] (.node [v0,v1,v2,v180,v3,v4,v5] .nil .nil) .nil)) (.node [v0,v1,v2,v107,v3,v474,v4] (.node [v0,v1,v2,v107,v3,v3,v4] (.node [v0,v1,v2,v107,v107,v3,v4] .nil .nil) .nil) (.node [v0,v1,v2,v107,v3,v4] .nil .nil))) (.node [v0,v1,v2,v107,v3,v4,v662] (.node [v0,v1,v2,v107,v3,v4,v5] (.node [v0,v1,v2,v107,v3,v4,v377] (.node [v0,v1,v2,v107,v3,v4,v372] .nil .nil) .nil) (.node [v0,v1,v2,v107,v3,v4,v590] (.node [v0,v1,v2,v107,v3,v4,v572] .nil .nil) .nil)) (.node [v0,v1,v2,v107,v3,v4,v548] (.node [v0,v1,v2,v107,v3,v4,v729] (.node [v0,v1,v2,v107,v3,v4,v641] .nil .nil) .nil) (.node [v0,v1,v2,v107,v3,v4,v487] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6rrllr : everyKey (rowOK 5 tree_5) tree_6rrllr = true := by decide +kernel
def tree_6rrll : BinaryTree (List W) := .node [v0,v1,v2,v1354,v3,v4,v5] tree_6rrlll tree_6rrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6rrll : everyKey (rowOK 5 tree_5) tree_6rrll = true := by
  change (_ && everyKey _ tree_6rrlll && everyKey _ tree_6rrllr) = true
  rw [ok_tree_6rrlll, ok_tree_6rrllr]
  decide +kernel
def tree_6rrlrl : BinaryTree (List W) := (.node [v0,v1,v2,v381,v3,v4,v5] (.node [v0,v1,v2,v111,v3,v4,v5] (.node [v0,v1,v2,v107,v3,v5,v16] (.node [v0,v1,v2,v107,v3,v4,v226] (.node [v0,v1,v2,v107,v3,v4,v169] (.node [v0,v1,v2,v107,v3,v4,v99] .nil .nil) .nil) (.node [v0,v1,v2,v107,v3,v4,v104] (.node [v0,v1,v2,v107,v3,v4,v244] .nil .nil) .nil)) (.node [v0,v1,v2,v107,v4,v487] (.node [v0,v1,v2,v107,v4,v5,v487] (.node [v0,v1,v2,v107,v3,v16] .nil .nil) .nil) (.node [v0,v1,v2,v111,v3,v4] .nil .nil))) (.node [v0,v1,v2,v315,v3,v4,v5] (.node [v0,v1,v2,v214,v3,v4] (.node [v0,v1,v2,v148,v3,v4,v5] (.node [v0,v1,v2,v148,v3,v4] .nil .nil) .nil) (.node [v0,v1,v2,v315,v3,v4] (.node [v0,v1,v2,v214,v3,v4,v5] .nil .nil) .nil)) (.node [v0,v1,v2,v375,v3,v4,v5] (.node [v0,v1,v2,v379,v3,v4,v5] (.node [v0,v1,v2,v378,v3,v4,v5] .nil .nil) .nil) (.node [v0,v1,v2,v382,v3,v4,v5] .nil .nil)))) (.node [v0,v1,v2,v3,v533,v4,v5] (.node [v0,v1,v2,v3,v3,v4,v5] (.node [v0,v1,v2,v10,v3,v4] (.node [v0,v1,v2,v380,v3,v4,v5] (.node [v0,v1,v2,v383,v3,v4,v5] .nil .nil) .nil) (.node [v0,v1,v2,v10,v3,v4,v99] (.node [v0,v1,v2,v10,v3,v4,v5] .nil .nil) .nil)) (.node [v0,v1,v2,v3,v462,v4,v5] (.node [v0,v1,v2,v3,v458,v4,v5] (.node [v0,v1,v2,v3,v459,v4,v5] .nil .nil) .nil) (.node [v0,v1,v2,v3,v284,v4,v5] .nil .nil))) (.node [v0,v1,v2,v3,v629,v4,v5] (.node [v0,v1,v2,v3,v787,v4,v5] (.node [v0,v1,v2,v3,v535,v4,v5] (.node [v0,v1,v2,v3,v532,v4,v5] .nil .nil) .nil) (.node [v0,v1,v2,v3,v626,v4,v5] (.node [v0,v1,v2,v3,v627,v4,v5] .nil .nil) .nil)) (.node [v0,v1,v2,v3,v1063,v4,v5] (.node [v0,v1,v2,v3,v1061,v4,v5] (.node [v0,v1,v2,v3,v786,v4,v5] .nil .nil) .nil) (.node [v0,v1,v2,v3,v1062,v4,v5] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6rrlrl : everyKey (rowOK 5 tree_5) tree_6rrlrl = true := by decide +kernel
def tree_6rrlrr : BinaryTree (List W) := (.node [v0,v1,v2,v3,v215,v5] (.node [v0,v1,v2,v3,v833,v4,v5] (.node [v0,v1,v2,v3,v474,v4,v99] (.node [v0,v1,v2,v3,v387,v4,v5] (.node [v0,v1,v2,v3,v398,v4,v5] (.node [v0,v1,v2,v3,v384,v4,v5] .nil .nil) .nil) (.node [v0,v1,v2,v3,v474,v4,v5] (.node [v0,v1,v2,v3,v386,v4,v5] .nil .nil) .nil)) (.node [v0,v1,v2,v3,v1355,v4,v5] (.node [v0,v1,v2,v3,v474,v99] (.node [v0,v1,v2,v3,v474,v5,v99] .nil .nil) .nil) (.node [v0,v1,v2,v3,v331,v4,v5] .nil .nil))) (.node [v0,v1,v2,v3,v839,v4,v5] (.node [v0,v1,v2,v3,v835,v4,v5] (.node [v0,v1,v2,v3,v836,v4,v5] (.node [v0,v1,v2,v3,v831,v4,v5] .nil .nil) .nil) (.node [v0,v1,v2,v3,v834,v4,v5] (.node [v0,v1,v2,v3,v837,v4,v5] .nil .nil) .nil)) (.node [v0,v1,v2,v3,v170,v5,v169] (.node [v0,v1,v2,v3,v170,v5] (.node [v0,v1,v2,v3,v170,v4,v5] .nil .nil) .nil) (.node [v0,v1,v2,v3,v215,v4,v5] .nil .nil)))) (.node [v0,v1,v2,v3,v4,v968,v5] (.node [v0,v1,v2,v3,v4,v4,v99] (.node [v0,v1,v2,v3,v155,v5] (.node [v0,v1,v2,v3,v155,v4,v5] (.node [v0,v1,v2,v3,v215,v5,v226] .nil .nil) .nil) (.node [v0,v1,v2,v3,v4,v4,v5] (.node [v0,v1,v2,v3,v155,v5,v244] .nil .nil) .nil)) (.node [v0,v1,v2,v3,v4,v1356,v5] (.node [v0,v1,v2,v3,v4,v1357,v5] (.node [v0,v1,v2,v3,v4,v1358,v5] .nil .nil) .nil) (.node [v0,v1,v2,v3,v4,v444,v5] .nil .nil))) (.node [v0,v1,v2,v3,v4,v979,v5] (.node [v0,v1,v2,v3,v4,v261] (.node [v0,v1,v2,v3,v4,v972,v5] (.node [v0,v1,v2,v3,v4,v973,v5] .nil .nil) .nil) (.node [v0,v1,v2,v3,v4,v977,v5] (.node [v0,v1,v2,v3,v4,v261,v5] .nil .nil) .nil)) (.node [v0,v1,v2,v3,v4,v530,v5] (.node [v0,v1,v2,v3,v4,v145,v5] (.node [v0,v1,v2,v3,v4,v978,v5] .nil .nil) .nil) (.node [v0,v1,v2,v3,v4,v982,v5] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6rrlrr : everyKey (rowOK 5 tree_5) tree_6rrlrr = true := by decide +kernel
def tree_6rrlr : BinaryTree (List W) := .node [v0,v1,v2,v3,v789,v4,v5] tree_6rrlrl tree_6rrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6rrlr : everyKey (rowOK 5 tree_5) tree_6rrlr = true := by
  change (_ && everyKey _ tree_6rrlrl && everyKey _ tree_6rrlrr) = true
  rw [ok_tree_6rrlrl, ok_tree_6rrlrr]
  decide +kernel
def tree_6rrl : BinaryTree (List W) := .node [v0,v1,v2,v107,v3,v4,v16] tree_6rrll tree_6rrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6rrl : everyKey (rowOK 5 tree_5) tree_6rrl = true := by
  change (_ && everyKey _ tree_6rrll && everyKey _ tree_6rrlr) = true
  rw [ok_tree_6rrll, ok_tree_6rrlr]
  decide +kernel
def tree_6rrrll : BinaryTree (List W) := (.node [v0,v1,v2,v3,v4,v263,v5] (.node [v0,v1,v2,v3,v4,v1359,v5] (.node [v0,v1,v2,v3,v4,v991,v5] (.node [v0,v1,v2,v3,v4,v624,v5] (.node [v0,v1,v2,v3,v4,v203,v5] (.node [v0,v1,v2,v3,v4,v985,v5] .nil .nil) .nil) (.node [v0,v1,v2,v3,v4,v994,v5] (.node [v0,v1,v2,v3,v4,v993,v5] .nil .nil) .nil)) (.node [v0,v1,v2,v3,v4,v1360,v5] (.node [v0,v1,v2,v3,v4,v990,v5] (.node [v0,v1,v2,v3,v4,v179,v5] .nil .nil) .nil) (.node [v0,v1,v2,v3,v4,v1361,v5] (.node [v0,v1,v2,v3,v4,v1362,v5] .nil .nil) .nil))) (.node [v0,v1,v2,v3,v4,v1363,v5] (.node [v0,v1,v2,v3,v4,v258,v5] (.node [v0,v1,v2,v3,v4,v581,v5] (.node [v0,v1,v2,v3,v4,v446,v5] .nil .nil) .nil) (.node [v0,v1,v2,v3,v4,v371,v99] (.node [v0,v1,v2,v3,v4,v371,v5] .nil .nil) .nil)) (.node [v0,v1,v2,v3,v4,v445,v5] (.node [v0,v1,v2,v3,v4,v1364,v5] (.node [v0,v1,v2,v3,v4,v1365,v5] .nil .nil) .nil) (.node [v0,v1,v2,v3,v4,v675,v5] .nil .nil)))) (.node [v0,v1,v2,v3,v4,v1366,v5] (.node [v0,v1,v2,v3,v4,v447,v5] (.node [v0,v1,v2,v3,v4,v1367,v5] (.node [v0,v1,v2,v3,v4,v372,v99] (.node [v0,v1,v2,v3,v4,v372,v5] .nil .nil) .nil) (.node [v0,v1,v2,v3,v4,v1368,v5] (.node [v0,v1,v2,v3,v4,v1369,v5] .nil .nil) .nil)) (.node [v0,v1,v2,v3,v4,v377,v5] (.node [v0,v1,v2,v3,v4,v262,v5] (.node [v0,v1,v2,v3,v4,v736,v5] .nil .nil) .nil) (.node [v0,v1,v2,v3,v4,v377,v99] .nil .nil))) (.node [v0,v1,v2,v3,v4,v213,v5] (.node [v0,v1,v2,v3,v4,v177,v5] (.node [v0,v1,v2,v3,v4,v177] (.node [v0,v1,v2,v3,v4,v1370,v5] .nil .nil) .nil) (.node [v0,v1,v2,v3,v4,v213] (.node [v0,v1,v2,v3,v4,v177,v169] .nil .nil) .nil)) (.node [v0,v1,v2,v3,v4,v154,v5] (.node [v0,v1,v2,v3,v4,v154] (.node [v0,v1,v2,v3,v4,v213,v226] .nil .nil) .nil) (.node [v0,v1,v2,v3,v4,v154,v244] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6rrrll : everyKey (rowOK 5 tree_5) tree_6rrrll = true := by decide +kernel
def tree_6rrrlr : BinaryTree (List W) := (.node [v0,v1,v2,v3,v4,v5,v572] (.node [v0,v1,v2,v3,v4,v5,v153] (.node [v0,v1,v2,v3,v4,v5,v1371] (.node [v0,v1,v2,v3,v4,v5] (.node [v0,v1,v2,v3,v4,v110,v104] (.node [v0,v1,v2,v3,v4,v110,v5] .nil .nil) .nil) (.node [v0,v1,v2,v3,v4,v5,v1372] (.node [v0,v1,v2,v3,v4,v5,v5] .nil .nil) .nil)) (.node [v0,v1,v2,v3,v4,v5,v316] (.node [v0,v1,v2,v3,v4,v5,v1373] (.node [v0,v1,v2,v3,v4,v5,v1374] .nil .nil) .nil) (.node [v0,v1,v2,v3,v4,v5,v216] .nil .nil))) (.node [v0,v1,v2,v3,v4,v5,v1375] (.node [v0,v1,v2,v3,v4,v5,v1376] (.node [v0,v1,v2,v3,v4,v5,v1377] (.node [v0,v1,v2,v3,v4,v5,v109] .nil .nil) .nil) (.node [v0,v1,v2,v3,v4,v5,v147] (.node [v0,v1,v2,v3,v4,v5,v1378] .nil .nil) .nil)) (.node [v0,v1,v2,v3,v4,v5,v1379] (.node [v0,v1,v2,v3,v4,v5,v1380] (.node [v0,v1,v2,v3,v4,v5,v1381] .nil .nil) .nil) (.node [v0,v1,v2,v3,v4,v5,v312] .nil .nil)))) (.node [v0,v1,v2,v3,v4,v5,v1382] (.node [v0,v1,v2,v3,v4,v5,v1383] (.node [v0,v1,v2,v3,v4,v5,v209] (.node [v0,v1,v2,v3,v4,v5,v1384] (.node [v0,v1,v2,v3,v4,v5,v590] .nil .nil) .nil) (.node [v0,v1,v2,v3,v4,v5,v1385] (.node [v0,v1,v2,v3,v4,v5,v1386] .nil .nil) .nil)) (.node [v0,v1,v2,v3,v4,v5,v662] (.node [v0,v1,v2,v3,v4,v5,v208] (.node [v0,v1,v2,v3,v4,v5,v1387] .nil .nil) .nil) (.node [v0,v1,v2,v3,v4,v5,v641] .nil .nil))) (.node [v0,v1,v2,v3,v4,v5,v729] (.node [v0,v1,v2,v3,v4,v5,v1388] (.node [v0,v1,v2,v3,v4,v5,v1389] (.node [v0,v1,v2,v3,v4,v5,v311] .nil .nil) .nil) (.node [v0,v1,v2,v3,v4,v5,v138] (.node [v0,v1,v2,v3,v4,v5,v1390] .nil .nil) .nil)) (.node [v0,v1,v2,v3,v4,v5,v1391] (.node [v0,v1,v2,v3,v4,v5,v1392] (.node [v0,v1,v2,v3,v4,v5,v548] .nil .nil) .nil) (.node [v0,v1,v2,v3,v4,v5,v112] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6rrrlr : everyKey (rowOK 5 tree_5) tree_6rrrlr = true := by decide +kernel
def tree_6rrrl : BinaryTree (List W) := .node [v0,v1,v2,v3,v4,v110] tree_6rrrll tree_6rrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6rrrl : everyKey (rowOK 5 tree_5) tree_6rrrl = true := by
  change (_ && everyKey _ tree_6rrrll && everyKey _ tree_6rrrlr) = true
  rw [ok_tree_6rrrll, ok_tree_6rrrlr]
  decide +kernel
def tree_6rrrrl : BinaryTree (List W) := (.node [v0,v1,v2,v3,v4,v5,v1393] (.node [v0,v1,v2,v3,v4,v5,v669] (.node [v0,v1,v2,v3,v4,v5,v99] (.node [v0,v1,v2,v3,v4,v5,v792] (.node [v0,v1,v2,v3,v4,v5,v785] (.node [v0,v1,v2,v3,v4,v5,v790] .nil .nil) .nil) (.node [v0,v1,v2,v3,v4,v5,v16] (.node [v0,v1,v2,v3,v4,v5,v487] .nil .nil) .nil)) (.node [v0,v1,v2,v3,v4,v5,v181] (.node [v0,v1,v2,v3,v4,v5,v574] (.node [v0,v1,v2,v3,v4,v5,v575] .nil .nil) .nil) (.node [v0,v1,v2,v3,v4,v5,v169] .nil .nil))) (.node [v0,v1,v2,v3,v4,v5,v244] (.node [v0,v1,v2,v3,v4,v5,v1394] (.node [v0,v1,v2,v3,v4,v5,v226] (.node [v0,v1,v2,v3,v4,v5,v225] .nil .nil) .nil) (.node [v0,v1,v2,v3,v4,v5,v246] (.node [v0,v1,v2,v3,v4,v5,v106] .nil .nil) .nil)) (.node [v0,v1,v2,v3,v4,v5,v104] (.node [v0,v1,v2,v3,v4,v5,v1395] (.node [v0,v1,v2,v3,v4,v5,v1396] .nil .nil) .nil) (.node [v0,v1,v2,v3,v4,v5,v591] .nil .nil)))) (.node [v0,v1,v2,v3,v4,v153] (.node [v0,v1,v2,v3,v4,v5,v1397] (.node [v0,v1,v2,v3,v4,v5,v747] (.node [v0,v1,v2,v3,v4,v5,v1398] (.node [v0,v1,v2,v3,v4,v5,v686] .nil .nil) .nil) (.node [v0,v1,v2,v3,v4,v5,v1399] (.node [v0,v1,v2,v3,v4,v5,v1400] .nil .nil) .nil)) (.node [v0,v1,v2,v3,v4,v316] (.node [v0,v1,v2,v3,v4,v5,v826] (.node [v0,v1,v2,v3,v4,v5,v1401] .nil .nil) .nil) (.node [v0,v1,v2,v3,v4,v216] .nil .nil))) (.node [v0,v1,v2,v3,v4,v208] (.node [v0,v1,v2,v3,v4,v312] (.node [v0,v1,v2,v3,v4,v147] (.node [v0,v1,v2,v3,v4,v109] .nil .nil) .nil) (.node [v0,v1,v2,v3,v4,v209] (.node [v0,v1,v2,v3,v4,v590,v99] .nil .nil) .nil)) (.node [v0,v1,v2,v3,v4,v138] (.node [v0,v1,v2,v3,v4,v311] (.node [v0,v1,v2,v3,v4,v641,v99] .nil .nil) .nil) (.node [v0,v1,v2,v3,v4,v548,v99] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6rrrrl : everyKey (rowOK 5 tree_5) tree_6rrrrl = true := by decide +kernel
def tree_6rrrrr : BinaryTree (List W) := (.node [v0,v288,v2,v3,v4,v5] (.node [v0,v1,v2,v3,v4,v99,v747] (.node [v0,v1,v2,v3,v4,v99,v226] (.node [v0,v1,v2,v3,v4,v99] (.node [v0,v1,v2,v3,v4,v16] (.node [v0,v1,v2,v3,v4,v487,v99] .nil .nil) .nil) (.node [v0,v1,v2,v3,v4,v99,v169] (.node [v0,v1,v2,v3,v4,v99,v99] .nil .nil) .nil)) (.node [v0,v1,v2,v3,v4,v99,v591] (.node [v0,v1,v2,v3,v4,v99,v104] (.node [v0,v1,v2,v3,v4,v99,v244] .nil .nil) .nil) (.node [v0,v1,v2,v3,v4,v99,v686] .nil .nil))) (.node [v0,v1,v2,v3,v5,v99,v104] (.node [v0,v1,v2,v3,v203,v5] (.node [v0,v1,v2,v3,v145,v5] (.node [v0,v1,v2,v3,v4,v99,v826] .nil .nil) .nil) (.node [v0,v1,v2,v3,v5,v16] (.node [v0,v1,v2,v3,v179,v5] .nil .nil) .nil)) (.node [v0,v1,v134,v3,v4,v5] (.node [v0,v1,v2,v3,v99,v104] (.node [v0,v1,v2,v3,v16] .nil .nil) .nil) (.node [v0,v1,v114,v3,v4,v5] .nil .nil)))) (.node [v1,v124,v2,v121,v3,v4,v5] (.node [v166,v1,v84,v2,v3,v4,v5] (.node [v293,v1,v2,v3,v4,v5] (.node [v0,v168,v2,v3,v4,v5] (.node [v0,v124,v168,v2,v3,v4,v5] .nil .nil) .nil) (.node [v303,v1,v2,v3,v4,v5] (.node [v132,v303,v1,v2,v3,v4,v5] .nil .nil) .nil)) (.node [v1,v124,v84,v2,v3,v4,v5] (.node [v166,v1,v2,v121,v3,v4,v5] (.node [v166,v1,v120,v2,v3,v4,v5] .nil .nil) .nil) (.node [v1,v124,v120,v2,v3,v4,v5] .nil .nil))) (.node [v1,v306,v2,v3,v4,v5,v226] (.node [v1,v341,v2,v3,v4,v5,v590] (.node [v1,v358,v2,v3,v4,v371,v5] (.node [v1,v358,v84,v2,v3,v4,v5] .nil .nil) .nil) (.node [v1,v306,v2,v3,v4,v5] (.node [v1,v84,v2,v3,v4,v5,v169] .nil .nil) .nil)) (.node [v1,v45,v2,v3,v4,v5] (.node [v1,v156,v2,v3,v4,v5,v244] (.node [v1,v156,v2,v3,v4,v5] .nil .nil) .nil) (.node [v1,v45,v2,v3,v4,v5,v104] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6rrrrr : everyKey (rowOK 5 tree_5) tree_6rrrrr = true := by decide +kernel
def tree_6rrrr : BinaryTree (List W) := .node [v0,v1,v2,v3,v4,v112] tree_6rrrrl tree_6rrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6rrrr : everyKey (rowOK 5 tree_5) tree_6rrrr = true := by
  change (_ && everyKey _ tree_6rrrrl && everyKey _ tree_6rrrrr) = true
  rw [ok_tree_6rrrrl, ok_tree_6rrrrr]
  decide +kernel
def tree_6rrr : BinaryTree (List W) := .node [v0,v1,v2,v3,v4,v5,v788] tree_6rrrl tree_6rrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6rrr : everyKey (rowOK 5 tree_5) tree_6rrr = true := by
  change (_ && everyKey _ tree_6rrrl && everyKey _ tree_6rrrr) = true
  rw [ok_tree_6rrrl, ok_tree_6rrrr]
  decide +kernel
def tree_6rr : BinaryTree (List W) := .node [v0,v1,v2,v3,v4,v980,v5] tree_6rrl tree_6rrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6rr : everyKey (rowOK 5 tree_5) tree_6rr = true := by
  change (_ && everyKey _ tree_6rrl && everyKey _ tree_6rrr) = true
  rw [ok_tree_6rrl, ok_tree_6rrr]
  decide +kernel
def tree_6r : BinaryTree (List W) := .node [v0,v1,v2,v1402,v3,v4,v5] tree_6rl tree_6rr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6r : everyKey (rowOK 5 tree_5) tree_6r = true := by
  change (_ && everyKey _ tree_6rl && everyKey _ tree_6rr) = true
  rw [ok_tree_6rl, ok_tree_6rr]
  decide +kernel
def tree_6 : BinaryTree (List W) := .node [v0,v1403,v1,v2,v3,v4,v5] tree_6l tree_6r
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_6 : everyKey (rowOK 5 tree_5) tree_6 = true := by
  change (_ && everyKey _ tree_6l && everyKey _ tree_6r) = true
  rw [ok_tree_6l, ok_tree_6r]
  decide +kernel
theorem closed_6 : Closed 6 tree_6 := closed_next 5 (by decide) tree_6 tree_5 closed_5 ok_tree_6
def tree_7l : BinaryTree (List W) := (.node [v330,v0,v1,v2,v3,v4,v5] (.node [v81,v0,v1,v2,v3,v4,v5] (.node [v68,v0,v1,v2,v3,v4,v5] (.node [v355,v0,v1,v2,v3,v4,v5] (.node [v344,v0,v1,v2,v3,v4,v5] (.node [v335,v0,v1,v2,v3,v4,v5] .nil .nil) .nil) (.node [v68,v0,v1,v2,v3,v4] .nil .nil)) (.node [v79,v0,v1,v2,v3,v4,v5] (.node [v391,v0,v1,v2,v3,v4,v5] .nil .nil) (.node [v77,v0,v1,v2,v3,v4,v5] .nil .nil))) (.node [v366,v0,v1,v2,v3,v4,v5] (.node [v75,v0,v1,v2,v3,v4,v5] (.node [v75,v0,v1,v2,v3,v4] .nil .nil) (.node [v86,v0,v1,v2,v3,v4,v5] .nil .nil)) (.node [v92,v0,v1,v2,v3,v4,v5] (.node [v83,v0,v1,v2,v3,v4,v5] .nil .nil) (.node [v94,v0,v1,v2,v3,v4,v5] .nil .nil)))) (.node [v164,v0,v1,v2,v3,v4,v5] (.node [v354,v0,v1,v2,v3,v4,v5] (.node [v123,v0,v1,v2,v3,v4,v5] (.node [v115,v0,v1,v2,v3,v4,v5] .nil .nil) (.node [v130,v0,v1,v2,v3,v4,v5] .nil .nil)) (.node [v95,v0,v1,v2,v3,v4,v5] (.node [v356,v0,v1,v2,v3,v4,v5] .nil .nil) (.node [v158,v0,v1,v2,v3,v4,v5] .nil .nil))) (.node [v0,v132,v1,v2,v3,v4,v5] (.node [v171,v0,v1,v2,v3,v4,v5] (.node [v21,v0,v1,v2,v3,v4,v5] .nil .nil) (.node [v589,v0,v1,v2,v3,v4,v5] .nil .nil)) (.node [v0,v345,v1,v2,v3,v4,v5] (.node [v0,v362,v1,v2,v3,v4,v5] .nil .nil) (.node [v0,v93,v1,v2,v3,v4,v5] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_7l : everyKey (rowOK 6 tree_6) tree_7l = true := by decide +kernel
def tree_7r : BinaryTree (List W) := (.node [v0,v1,v2,v107,v3,v4] (.node [v0,v1,v84,v2,v3,v4,v5] (.node [v0,v639,v1,v2,v3,v4,v5] (.node [v0,v32,v1,v2,v3,v4,v5] (.node [v0,v166,v1,v2,v3,v4,v5] .nil .nil) (.node [v0,v220,v1,v2,v3,v4,v5] .nil .nil)) (.node [v0,v1,v358,v2,v3,v4,v5] (.node [v0,v1,v124,v2,v3,v4,v5] .nil .nil) (.node [v0,v1,v341,v2,v3,v4,v5] .nil .nil))) (.node [v0,v1,v546,v2,v3,v4,v5] (.node [v0,v1,v41,v2,v3,v4,v5] (.node [v0,v1,v120,v2,v3,v4,v5] .nil .nil) (.node [v0,v1,v242,v2,v3,v4,v5] .nil .nil)) (.node [v0,v1,v2,v119,v3,v4,v5] (.node [v0,v1,v2,v121,v3,v4,v5] .nil .nil) (.node [v0,v1,v2,v192,v3,v4,v5] .nil .nil)))) (.node [v0,v1,v2,v3,v4,v5,v548] (.node [v0,v1,v2,v3,v4,v372,v5] (.node [v0,v1,v2,v3,v474,v4,v5] (.node [v0,v1,v2,v107,v3,v4,v5] .nil .nil) (.node [v0,v1,v2,v3,v4,v371,v5] .nil .nil)) (.node [v0,v1,v2,v3,v4,v5,v590] (.node [v0,v1,v2,v3,v4,v377,v5] .nil .nil) (.node [v0,v1,v2,v3,v4,v5,v641] .nil .nil))) (.node [v0,v1,v2,v3,v4,v5,v226] (.node [v0,v1,v2,v3,v4,v5,v99] (.node [v0,v1,v2,v3,v4,v5,v487] .nil .nil) (.node [v0,v1,v2,v3,v4,v5,v169] .nil .nil)) (.node [v0,v1,v2,v3,v4,v5,v104] (.node [v0,v1,v2,v3,v4,v5,v244] .nil .nil) (.node [v0,v1,v2,v3,v4,v99] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_7r : everyKey (rowOK 6 tree_6) tree_7r = true := by decide +kernel
def tree_7 : BinaryTree (List W) := .node [v0,v212,v1,v2,v3,v4,v5] tree_7l tree_7r
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_7 : everyKey (rowOK 6 tree_6) tree_7 = true := by
  change (_ && everyKey _ tree_7l && everyKey _ tree_7r) = true
  rw [ok_tree_7l, ok_tree_7r]
  decide +kernel
theorem closed_7 : Closed 7 tree_7 := closed_next 6 (by decide) tree_7 tree_6 closed_6 ok_tree_7
def tree_8 : BinaryTree (List W) := (.node [v0,v1,v2,v3,v4,v5] .nil .nil)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_8 : everyKey (rowOK 7 tree_7) tree_8 = true := by decide +kernel
theorem closed_8 : Closed 8 tree_8 := closed_next 7 (by decide) tree_8 tree_7 closed_7 ok_tree_8
theorem lower6 : ∀ z, z = goal ∨ z = ~~~goal → ¬ build basicOps z 8 ins6.toFinset := @no_build 8 tree_8 ins6 nd6 (by decide) closed_8 (by decide +kernel)
def gates6 : List Gate := [⟨.and, [1, 2]⟩, ⟨.and, [0, 6]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [7, 5]⟩, ⟨.or, [9, 4]⟩, ⟨.and, [7, 4]⟩, ⟨.or, [0, 8]⟩, ⟨.or, [11, 3]⟩, ⟨.and, [13, 10]⟩, ⟨.and, [14, 12]⟩]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem upper6 : ∃ (gs : List Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs.length = 10 ∧ ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = Nat.testBit (4269866496 * 2 ^ 32 + 4269834240) (∑ i : Fin 6, if x i then 2^(i : ℕ) else 0) := by
  exact ⟨gates6, 15, by simp [gates6], rfl, by decide +kernel⟩

end PEqualNP.Outside.L_meta_12274

open PEqualNP.Outside.L_meta_12274 in
theorem PEqualNP.Outside.L_meta_12274 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4269866496 * 2 ^ 32 + 4269834240) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4269866496 * 2 ^ 32 + 4269834240) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
  intro s h
  obtain ⟨C, basis, size, computes⟩ := h
  obtain ⟨gates, output, mono, bound, correct⟩ :=
    replace (4269866496 * 2 ^ 32 + 4269834240) 10 ins6 nd6 rows6 rfl
      lower6 upper6 C.gates C.output basis computes
  exact ⟨⟨gates, output⟩, mono, bound.trans size, correct⟩
