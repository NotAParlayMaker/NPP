import PEqualNP.Defs

-- The witness has eleven binary gates. Any circuit with a NOT and fewer gates
-- would have at most nine binary gates even with every negation available for free.
-- Finite signed-circuit certificates below exclude that possibility.
-- Signed-wire search and gate projections adapt the project’s Apache 2.0 proofs.
namespace PEqualNP.Outside.L_meta_12074_aux
namespace CoreSigned

-- The signed live-wire search follows L-meta-8463 and L-meta-1449, Apache-2.0.

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

set_option maxRecDepth 100000 in
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

set_option maxRecDepth 100000 in
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

set_option maxRecDepth 100000 in
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

set_option maxRecDepth 100000 in
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

def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

set_option maxRecDepth 100000 in
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

set_option maxRecDepth 100000 in
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

def F (x : Fin 6 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 3) || (x 1 && x 5) || (x 2 && x 3) || (x 2 && x 4)

end CoreSigned

namespace SignedProjection
variable {α β : Type} [DecidableEq α] [DecidableEq β] [Zero β]

def avail (pin : α → β) (S : Finset α) := (S.image pin).erase 0
def lost (pin : α → β) (S : Finset α) := (S.filter fun x => pin x = 0).card

theorem avail_mem (pin : α → β) {S : Finset α} {x : β} :
    x ∈ avail pin S ↔ x ≠ 0 ∧ ∃ a ∈ S, pin a = x := by simp [avail]

theorem avail_mono (pin : α → β) {S T : Finset α} (h : S ⊆ T) : avail pin S ⊆ avail pin T := by
  intro y hy
  obtain ⟨hn,x,hx,rfl⟩ := (avail_mem pin).mp hy
  exact (avail_mem pin).mpr ⟨hn,x,h hx,rfl⟩

theorem avail_cases (pin : α → β) {S : Finset α} {c : α} {x : β} (h : x ∈ avail pin (insert c S)) :
    x = pin c ∨ x ∈ avail pin S := by
  obtain ⟨hn,y,hy,rfl⟩ := (avail_mem pin).mp h
  rcases Finset.mem_insert.mp hy with rfl|hy
  · exact Or.inl rfl
  · exact Or.inr ((avail_mem pin).mpr ⟨hn,y,hy,rfl⟩)

theorem lost_insert (pin : α → β) (c : α) (S : Finset α) :
    lost pin (insert c S) = lost pin S + (if pin c = 0 ∧ c ∉ S then 1 else 0) := by
  by_cases mem : c ∈ S
  · rw [Finset.insert_eq_of_mem mem,ite_eq_right (fun q => q.2 mem),Nat.add_zero]
  · by_cases h : pin c = 0
    · rw [ite_eq_left ⟨h,mem⟩]
      unfold lost
      rw [Finset.filter_insert,ite_eq_left h,Finset.card_insert_of_notMem]
      exact fun q => mem (Finset.mem_filter.mp q).1
    · rw [ite_eq_right (fun q => h q.1),Nat.add_zero]
      unfold lost
      rw [Finset.filter_insert,ite_eq_right h]

theorem projected (pin : α → β) (ops : α → α → Finset α) (ops2 : β → β → Finset β) (goal : α)
    (hgoal : pin goal ≠ 0)
    (maps : ∀ {a b c}, c ∈ ops a b → pin c ∈ ops2 (pin a) (pin b))
    (idA : ∀ {a b c}, c ∈ ops2 a b → a = 0 → c = 0 ∨ c = b)
    (idB : ∀ {a b c}, c ∈ ops2 a b → b = 0 → c = 0 ∨ c = a)
    (idS : ∀ {a b c}, c ∈ ops2 a b → a = b → c = 0 ∨ c = b)
    {k : Nat} {S : Finset α} (h : CoreSigned.live ops goal k S) :
    ∃ j, j + lost pin S ≤ k ∧ ∃ T ⊆ avail pin S, CoreSigned.live ops2 (pin goal) j T := by
  induction k generalizing S with
  | zero =>
    change S = {goal} at h
    subst S
    exact ⟨0,by simp [lost,hgoal],{(pin goal)},by simp [avail,hgoal],rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a,_,b,_,ne,c,op,fresh,U,rfl,tail⟩
    · obtain ⟨j,hj,ws,sub,hws⟩ := ih skip
      exact ⟨j,by omega,ws,sub,hws⟩
    let prev := insert a (insert b U)
    have cnew : c ∉ U := fun h => fresh (by simp [h])
    have repr := maps op
    obtain ⟨j,limit,T,sub,path⟩ := ih tail
    have both (ha : pin a = 0) (hb : pin b = 0) : pin c = 0 := by
      exact (idA repr ha).elim id (fun e => e.trans hb)
    have skipcost : lost pin prev ≤ lost pin (insert c U) + 1 := by
      simp only [prev,lost_insert]
      split_ifs <;> grind
    have liftU : avail pin U ⊆ avail pin prev := avail_mono pin (by intro u hu; simp [prev,hu])
    by_cases useful : pin c ∈ T ∧ pin c ∉ avail pin prev
    · have nz := ((avail_mem pin).mp (sub useful.1)).1
      have df (v : α) (hv : v ∈ prev) : pin c ≠ pin v := by
        intro e
        exact useful.2 ((avail_mem pin).mpr ⟨nz,v,hv,e.symm⟩)
      have da := df a (by simp [prev])
      have db := df b (by simp [prev])
      have ha : pin a ≠ 0 := fun e => (idA repr e).elim nz db
      have hb : pin b ≠ 0 := fun e => (idB repr e).elim nz da
      have distinct : pin a ≠ pin b := fun e => (idS repr e).elim nz db
      have vcost : lost pin prev ≤ lost pin (insert c U) := by
        simp only [prev,lost_insert]
        split_ifs <;> grind
      let V := T.erase (pin c)
      have old (v : β) (hv : v ∈ V) : v ∈ avail pin U :=
        (avail_cases pin (sub (Finset.mem_erase.mp hv).2)).resolve_left (Finset.mem_erase.mp hv).1
      let B := insert (pin a) (insert (pin b) V)
      refine ⟨j+1,by change j+1+lost pin prev ≤ k+1; omega,B,?_,Or.inr ?_⟩
      · intro v hv
        rcases Finset.mem_insert.mp hv with rfl|hv
        · exact (avail_mem pin).mpr ⟨ha,a,by simp,rfl⟩
        rcases Finset.mem_insert.mp hv with rfl|hv
        · exact (avail_mem pin).mpr ⟨hb,b,by simp,rfl⟩
        exact liftU (old _ hv)
      · refine ⟨pin a,by simp [B],pin b,by simp [B],distinct,pin c,?_,?_,V,rfl,?_⟩
        · exact repr
        · simp [B,V,da,db]
        · rwa [show insert (pin c) V = T from Finset.insert_erase useful.1]
    · refine ⟨j,by change j+lost pin prev ≤ k+1; omega,T,?_,path⟩
      intro v hv
      rcases avail_cases pin (sub hv) with rfl|old
      · by_contra miss
        exact useful ⟨hv,miss⟩
      · exact liftU old


end SignedProjection

namespace SignedProjection
variable {n : Nat}

def signedOps (a b : BitVec n) := [a &&& b, a ||| b, a &&& ~~~b, b &&& ~~~a].toFinset

theorem zero_left {a b c : BitVec n} (h : c ∈ signedOps a b) (eq : a = 0) : c = 0 ∨ c = b := by
  subst a
  simpa [signedOps,or_comm] using h

theorem zero_right {a b c : BitVec n} (h : c ∈ signedOps a b) (eq : b = 0) : c = 0 ∨ c = a := by
  subst b
  simpa [signedOps,or_comm] using h

theorem equal_inputs {a b c : BitVec n} (h : c ∈ signedOps a b) (eq : a = b) : c = 0 ∨ c = b := by
  subst a
  simpa [signedOps,or_comm] using h

def signedPin (mask : BitVec n) (base : Fin n) (x : BitVec n) : BitVec n :=
  (if x[base.val] then ~~~x else x) &&& mask

theorem masked_ops (m : BitVec n) {a b c : BitVec n} (h : c ∈ signedOps a b) :
    c &&& m ∈ signedOps (a &&& m) (b &&& m) := by
  simp only [signedOps,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at *
  rcases h with rfl|rfl|rfl|rfl
  · left; ext i h; simp [Bool.and_assoc, Bool.and_left_comm, Bool.and_comm]
  · right;left; ext i h; simp only [BitVec.getElem_or,BitVec.getElem_and]; cases a[i] <;> cases b[i] <;> simp
  · right;right;left; ext i h
    simp only [BitVec.getElem_and,BitVec.getElem_not]
    cases a[i] <;> cases b[i] <;> cases m[i] <;> decide
  · right;right;right; ext i h
    simp only [BitVec.getElem_and,BitVec.getElem_not]
    cases a[i] <;> cases b[i] <;> cases m[i] <;> decide

def polarity (b : Bool) (x : BitVec n) := if b then ~~~x else x

theorem polarity_ops (i : Fin n) {a b c : BitVec n} (h : c ∈ signedOps a b) :
    polarity (c[i.val]) c ∈ signedOps (polarity (a[i.val]) a) (polarity (b[i.val]) b) := by
  simp only [signedOps,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at *
  rcases h with rfl|rfl|rfl|rfl <;>
    simp only [BitVec.getElem_and,BitVec.getElem_or,BitVec.getElem_not] <;>
    cases a[i.val] <;> cases b[i.val] <;>
    simp [polarity,BitVec.not_and,BitVec.not_or,BitVec.and_comm,BitVec.or_comm]

theorem signedPin_ops (m : BitVec n) (i : Fin n) {a b c : BitVec n} (h : c ∈ signedOps a b) :
    signedPin m i c ∈ signedOps (signedPin m i a) (signedPin m i b) :=
  masked_ops m (polarity_ops i h)

theorem live_build {α : Type} [DecidableEq α] {ops : α → α → Finset α} {goal : α}
    {k : Nat} {S V : Finset α} (h : CoreSigned.live ops goal k S) (sub : S ⊆ V) :
    CoreSigned.build ops goal k V := by
  induction k generalizing S V with
  | zero => change S = {goal} at h; subst S; exact sub (Finset.mem_singleton_self _)
  | succ k ih =>
    rcases h with skip|⟨a,ha,b,hb,ne,c,opc,_,rest,eq,tail⟩
    · exact Or.inl (ih skip sub)
    · refine Or.inr ⟨a,sub ha,b,sub hb,ne,c,opc,ih tail ?_⟩
      intro v hv
      rcases Finset.mem_insert.mp hv with rfl|hr
      · simp
      · exact Finset.mem_insert_of_mem (sub (eq ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hr)))

end SignedProjection

namespace SignedProjection
variable {α : Type} [DecidableEq α]

def generated (ops : α → α → Finset α) (stock : Finset α) : List (α × α × α) → Finset α → Prop
  | [], result => stock = result
  | (a,b,w) :: rest, result =>
    a ∈ stock ∧ b ∈ stock ∧ a ≠ b ∧ w ∈ ops a b ∧ generated ops (insert w stock) rest result

theorem extend_generated {ops : α → α → Finset α} {goal : α} {stock result : Finset α}
    {recipe : List (α × α × α)} {k : ℕ}
    (h : generated ops stock recipe result) (tail : CoreSigned.build ops goal k result) :
    CoreSigned.build ops goal (k + recipe.length) stock := by
  induction recipe generalizing stock with
  | nil => change stock = result at h; simpa [h] using tail
  | cons step rest ih =>
    obtain ⟨a,b,w⟩ := step
    rcases h with ⟨ha,hb,hn,ho,hrest⟩
    change CoreSigned.build ops goal (k+rest.length+1) stock
    exact Or.inr ⟨a,ha,b,hb,hn,w,ho,ih hrest⟩

theorem pad_build {ops : α → α → Finset α} {goal : α} {S : Finset α} {a b : Nat}
    (le : a ≤ b) (ha : CoreSigned.build ops goal a S) : CoreSigned.build ops goal b S := by
  induction le with
  | refl => exact ha
  | step _ ih => exact Or.inl ih

end SignedProjection

namespace SignedProjection
variable {n : Nat}

theorem exclude_cut (m : BitVec n) (i : Fin n) (goal : BitVec n) (k cap : ℕ)
    (S A U : Finset (BitVec n)) (recipes : List (BitVec n × BitVec n × BitVec n))
    (nonzero : signedPin m i goal ≠ 0)
    (bound : ¬ CoreSigned.build signedOps (signedPin m i goal) cap A)
    (regen : generated signedOps A recipes U) (sub : avail (signedPin m i) S ⊆ U)
    (budget : recipes.length + k ≤ cap + lost (signedPin m i) S) :
    ¬ CoreSigned.live signedOps goal k S := by
  intro h
  obtain ⟨j, hj, T, ht, path⟩ := projected (signedPin m i) signedOps signedOps goal nonzero
    (signedPin_ops m i) zero_left zero_right equal_inputs h
  have localRun := live_build path (ht.trans sub)
  exact bound (pad_build (by omega) (extend_generated regen localRun))

end SignedProjection

namespace SignedProjection
open CoreSigned (live build first_live live_card pairs pick_two live_separates)

abbrev Word := BitVec 64
def signedList (a b : Word) := [a &&& b, a ||| b, a &&& ~~~b, b &&& ~~~a]
theorem ops_swap (a b : Word) : signedOps a b = signedOps b a := by
  ext z
  simp only [signedOps, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto
def keepChoices (a b : Word) (r : List Word) : List (List Word) := [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept {ws r : List Word} {a b : Word} {needed : Finset Word}
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

theorem singleton_list {goal : Word} {ws : List Word} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

def insertW (v : Word) : List Word → List Word
  | [] => [v]
  | x :: xs => if v ≤ x then v :: x :: xs else x :: insertW v xs

def ordered (ws : List Word) := ws.foldr insertW []

theorem insertW_perm (v : Word) (ws : List Word) : (insertW v ws).Perm (v :: ws) := by
  induction ws with
  | nil => exact .refl _
  | cons x xs ih =>
    simp only [insertW]
    split
    · exact .refl _
    · exact (ih.cons x).trans (.swap _ _ _)

theorem ordered_perm (ws : List Word) : (ordered ws).Perm ws := by
  induction ws with
  | nil => exact .refl _
  | cons x xs ih => exact (insertW_perm x (ordered xs)).trans (ih.cons x)

theorem perm_set {u v : List Word} (p : u.Perm v) : u.toFinset = v.toFinset := by
  ext a
  simpa only [List.mem_toFinset] using (p.mem_iff : a ∈ u ↔ a ∈ v)


def children (k : Nat) (ws : List Word) : List (List Word) :=
  (pairs ws).flatMap fun (a,b,r) => (signedList a b).flatMap fun z =>
    if z ∈ ws then [] else
      (keepChoices a b r).filterMap fun kept =>
        if kept.length ≤ k then some (ordered (z :: kept)) else none

theorem zero_prune {goal : Word} (nz : goal ≠ 0) {k : Nat} {S : Finset Word}
    (h : live signedOps goal k S) : ∃ j ≤ k, ∃ T ⊆ S.erase 0, live signedOps goal j T := by
  obtain ⟨j,le,T,sub,path⟩ := projected id signedOps signedOps goal nz (fun q => q)
    zero_left zero_right equal_inputs h
  refine ⟨j,by omega,T,?_,path⟩
  simpa [avail] using sub

theorem step_no (goal : Word) (n : Nat) (ws : List Word) (hn : ws.Nodup)
    (done_ : ws ≠ [goal])
    (children_ : ∀ qs ∈ children n ws, ¬ live signedOps goal n qs.toFinset)
    : ¬ live signedOps goal (n+1) ws.toFinset := by
  intro h
  rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
  · exact done_ (singleton_list hn done)
  obtain ⟨r,hm,hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
  have go {a b : Word} (hp : ws.Perm (a :: b :: r)) (hmem : (a,b,r) ∈ pairs ws)
      (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ signedOps a b) : False := by
    obtain ⟨kept,hkeep,hnk,hfin⟩ := recover_kept hp hn hset
    have hznew : z ∉ kept := by
      intro hu
      apply hout
      rw [hset]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ List.mem_toFinset.mpr hu))
    have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
    have hraw : live signedOps goal n (z :: kept).toFinset := by simpa [hfin] using tail
    have hc := live_card hraw
    rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
    have hzws : z ∉ ws := by simpa using hout
    have hp' := ordered_perm (z :: kept)
    have mem : ordered (z :: kept) ∈ children n ws := by
      apply List.mem_flatMap.mpr
      refine ⟨(a,b,r),hmem,List.mem_flatMap.mpr ⟨z,List.mem_toFinset.mp hop,?_⟩⟩
      simpa only [hzws,ite_false] using
        (List.mem_filterMap.mpr ⟨kept,hkeep,by simp [show kept.length ≤ n by omega]⟩ :
          ordered (z::kept) ∈ ((keepChoices a b r).filterMap fun kept =>
            if kept.length ≤ n then some (ordered (z :: kept)) else none))
    exact children_ _ mem ((perm_set hp').symm ▸ hraw)
  rcases hm with direct|swap
  · exact go hp direct hs hz
  · exact go (hp.trans (.swap _ _ _)) swap (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)
end SignedProjection

namespace SignedProjection
abbrev V64 := BitVec 64

def bitAt (w : V64) (n : Nat) := w.getLsbD n
def mismatch (g : V64) (ws : List V64) (p q : Nat) :=
  (bitAt g p != bitAt g q) && ws.all (fun w => bitAt w p == bitAt w q)

theorem mismatch_sound {g : V64} {ws : List V64} {p q : Nat} (pp : p < 64) (qq : q < 64)
    (cert : mismatch g ws p q = true) (k : ℕ) : ¬ CoreSigned.live signedOps g k ws.toFinset := by
  intro h
  have parts := Bool.and_eq_true_iff.mp cert
  let D : V64 → Prop := fun w => bitAt w p ≠ bitAt w q
  have dg : D g := by simpa [D] using parts.1
  have hop (a b : V64) (z : V64) (hz : z ∈ signedOps a b) (dz : D z) : D a ∨ D b := by
    by_contra! fail
    apply dz
    obtain ⟨ea,eb⟩ := fail
    simp only [D, not_not] at ea eb
    change bitAt a p = bitAt a q at ea
    change bitAt b p = bitAt b q at eb
    simp only [signedOps, List.mem_toFinset,List.mem_cons, List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl|rfl|rfl <;>
      simpa only [bitAt, BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not,
        pp,qq,decide_true, Bool.true_and, show a.getLsbD p = a.getLsbD q from ea,
        show b.getLsbD p = b.getLsbD q from eb]
  obtain ⟨x,hx,dx⟩ := CoreSigned.live_separates D dg hop h
  exact dx (beq_iff_eq.mp (List.all_eq_true.mp parts.2 x (List.mem_toFinset.mp hx)))

end SignedProjection

namespace SignedProjection
abbrev View := Word × Fin 64 × Word × List Word × Nat × (Nat → Nat)
abbrev Node := Nat × Nat × List Word × (Nat → Nat)
def vm (v : View) := v.1
def va (v : View) := v.2.1
def vg (v : View) := v.2.2.1
def vs (v : View) := v.2.2.2.1
def vk (v : View) := v.2.2.2.2.1
def vh (v : View) := v.2.2.2.2.2
def nv (a : Node) := a.1
def nk (a : Node) := a.2.1
def ns (a : Node) := a.2.2.1
def nh (a : Node) := a.2.2.2

def recipeRun : Nat → Nat → List Word → Option (List (Word × Word × Word) × List Word)
  | 0, code, ws => if code = 1 then some ([],ws) else none
  | fuel+1, code, ws => if code = 1 then some ([],ws) else
    let i := code % 16
    let j := (code / 16) % 16
    let o := (code / 256) % 4
    match ws[i]?, ws[j]? with
    | some a, some b => if a = b then none else
      let w := (signedList a b).getD o 0
      match recipeRun fuel (code / 1024) (ws++[w]) with
      | some (rs,ws') => some ((a,b,w)::rs,ws')
      | none => none
    | _,_ => none

theorem recipeRun_sound (fuel code : Nat) (ws : List Word) {rs out}
    (h : recipeRun fuel code ws = some (rs,out)) :
    generated signedOps ws.toFinset rs out.toFinset := by
  induction fuel generalizing code ws rs out with
  | zero =>
    simp only [recipeRun] at h
    split at h
    · cases h; rfl
    · contradiction
  | succ k ih =>
    simp only [recipeRun] at h
    split at h
    · cases h; rfl
    split at h <;> try contradiction
    rename_i a b ha hb
    split at h <;> try contradiction
    rename_i ne
    split at h <;> try contradiction
    rename_i tail end_ ht
    cases h
    set r := (code / 256) % 4
    let w := (signedList a b).getD r 0
    change a ∈ ws.toFinset ∧ b ∈ ws.toFinset ∧ a ≠ b ∧ w ∈ signedOps a b ∧ _
    refine ⟨List.mem_toFinset.mpr (List.mem_of_getElem? ha),
      List.mem_toFinset.mpr (List.mem_of_getElem? hb),ne,?_,?_⟩
    · have hr : r < 4 := Nat.mod_lt _ (by decide)
      change w ∈ (signedList a b).toFinset
      simp only [List.mem_toFinset]
      have hr' : r < (signedList a b).length := by simpa [signedList] using hr
      simpa [w, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr'] using
        (List.getElem_mem (l := signedList a b) (i := r) hr')
    · have eq : (ws++[w]).toFinset = insert w ws.toFinset := by
        ext x
        simp [or_comm]
      rw [← eq]
      exact ih _ _ ht

def ViewOK (v : View) := ¬ CoreSigned.build signedOps (vg v) (vk v) (vs v).toFinset

def cutOK (v : View) (g : Word) (k : Nat) (ws : List Word) (recipe : Nat) : Bool :=
  let p := signedPin (vm v) (va v)
  if p g != vg v || p g == 0 then false else
    match recipeRun 12 recipe (vs v) with
    | none => false
    | some (rs,out) =>
      decide (avail p ws.toFinset ⊆ out.toFinset) &&
      decide (rs.length+k ≤ vk v + lost p ws.toFinset)

theorem cutOK_sound {v : View} {g : Word} {k : Nat} {ws : List Word} {recipe : Nat}
    (hv : ViewOK v) (hc : cutOK v g k ws recipe = true) :
    ¬ CoreSigned.live signedOps g k ws.toFinset := by
  simp only [cutOK] at hc
  split at hc <;> try contradiction
  rename_i ok
  split at hc <;> try contradiction
  rename_i rs out hr
  have parts := Bool.and_eq_true_iff.mp hc
  have good : signedPin (vm v) (va v) g = vg v ∧ signedPin (vm v) (va v) g ≠ 0 := by
    simpa using ok
  apply exclude_cut (vm v) (va v) g k (vk v) ws.toFinset (vs v).toFinset out.toFinset rs good.2
    (good.1 ▸ hv) (recipeRun_sound _ _ _ hr) (of_decide_eq_true parts.1)
    (of_decide_eq_true parts.2)

end SignedProjection
namespace SignedProjection

def quickCut (v : View) (g : Word) (k : Nat) (ws : List Word) (receipt : Nat) : Bool :=
  let p := signedPin (vm v) (va v)
  if p g != vg v || p g == 0 then false else
    match recipeRun 12 receipt (vs v) with
    | none => false
    | some (rs,out) =>
      decide ws.Nodup &&
      ws.all (fun w => p w == 0 || out.contains (p w)) &&
      decide (rs.length+k ≤ vk v + ws.countP (fun w => p w = 0))

theorem quickCut_sound {v : View} {g : Word} {k : Nat} {ws : List Word} {receipt : Nat}
    (hv : ViewOK v) (ok : quickCut v g k ws receipt = true) :
    ¬ CoreSigned.live signedOps g k ws.toFinset := by
  simp only [quickCut] at ok
  split at ok <;> try contradiction
  rename_i good
  split at ok <;> try contradiction
  rename_i rs out hr
  have parts := Bool.and_eq_true_iff.mp ok
  have pp := Bool.and_eq_true_iff.mp parts.1
  have nd := of_decide_eq_true pp.1
  have gg : signedPin (vm v) (va v) g = vg v ∧ signedPin (vm v) (va v) g ≠ 0 := by
    simpa using good
  apply exclude_cut (vm v) (va v) g k (vk v) ws.toFinset (vs v).toFinset out.toFinset rs gg.2
    (gg.1 ▸ hv) (recipeRun_sound _ _ _ hr)
  · intro x hx
    obtain ⟨ne,w,hw,rfl⟩ := (avail_mem _).mp hx
    have has := List.all_eq_true.mp pp.2 w (List.mem_toFinset.mp hw)
    simp only [Bool.or_eq_true,beq_iff_eq,List.contains_iff_mem] at has
    exact List.mem_toFinset.mpr (has.resolve_left ne)
  · unfold lost
    rw [List.Nodup.card_eq_countP nd]
    exact of_decide_eq_true parts.2

end SignedProjection

namespace SignedProjection.QFast
abbrev Table (α : Type) := Nat × (Nat → Option α)
def get {α : Type} (t : Table α) (i : Nat) : Option α := if i < t.1 then t.2 i else none

def checkHint (views : Table View) (nodes : Table Node) (vID : Nat) (g : Word)
    (k : Nat) (ws : List Word) (hint : Nat) : Bool :=
  let val := hint/4
  match hint % 4 with
  | 0 => mismatch g ws (val % 64) ((val/64)%64)
  | 1 => match (get nodes val) with
    | some a => (nv a == vID) && (nk a == k) && (ns a == ws)
    | none => false
  | 2 =>
    let j := val % 1024
    if j < vID then
      match (get views j) with
      | some v => quickCut v g k ws (val/1024)
      | none => false
    else false
  | _ => (k == 0 && ws.toFinset != {g}) || decide (k+1 < ws.toFinset.card)

theorem checkHint_sound {views : Table View} {nodes : Table Node} {vID : Nat} {g : Word}
    {k : Nat} {ws : List Word} {h : Nat}
    (known : ∀ i < vID, ∀ v, (get views i) = some v → ViewOK v)
    (closed : ∀ (i : Nat) (a : Node), (get nodes i) = some a → nv a = vID → nk a = k →
      ¬ CoreSigned.live signedOps g k (ns a).toFinset)
    (ok : checkHint views nodes vID g k ws h = true) : ¬ CoreSigned.live signedOps g k ws.toFinset := by
  simp only [checkHint] at ok
  split at ok
  · exact mismatch_sound (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)) ok k
  · split at ok <;> try contradiction
    rename_i a ha
    simp only [Bool.and_eq_true,beq_iff_eq] at ok
    exact ok.2 ▸ closed _ a ha ok.1.1 ok.1.2
  · split at ok <;> try contradiction
    rename_i lt
    split at ok <;> try contradiction
    rename_i v hv
    exact quickCut_sound (known _ lt _ hv) ok
  · simp only [Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq,bne_iff_ne,decide_eq_true_eq] at ok
    intro h
    rcases ok with ⟨rfl,ne⟩|wide
    · exact ne h
    · exact (Nat.not_lt_of_ge (CoreSigned.live_card h)) wide

def scanFrom {α : Type} (f : Nat → α → Bool) : Nat → List α → Bool
  | _, [] => true
  | i, x::xs => f i x && scanFrom f (i+1) xs

theorem scanFrom_sound {α : Type} (f : Nat → α → Bool) {i : Nat} {xs : List α}
    (ok : scanFrom f i xs = true) {x : α} (hx : x ∈ xs) : ∃ j, f j x = true := by
  induction xs generalizing i with
  | nil => simp at hx
  | cons a xs ih =>
    have parts := Bool.and_eq_true_iff.mp ok
    rcases List.mem_cons.mp hx with rfl|hm
    · exact ⟨_,parts.1⟩
    · exact ih parts.2 hm

def evalNode (views : Table View) (nodes : Table Node) (a : Node) : Bool :=
  match (get views (nv a)) with
  | none => false
  | some v => decide (ns a).Nodup && (ns a != [vg v]) &&
    match nk a with
    | 0 => true
    | k+1 => scanFrom (fun i ws => checkHint views nodes (nv a) (vg v) k ws (nh a i)) 0
               (children k (ns a))

def evalRoot (views : Table View) (nodes : Table Node) (i : Nat) (v : View) : Bool :=
  scanFrom (fun q ws => checkHint views nodes i (vg v) (vk v) ws (vh v q)) 0 (vs v).sublists

theorem view_from_earlier (views : Table View) (nodes : Table Node) (vID : Nat) (v : View)
    (hv : (get views vID) = some v)
    (earlier : ∀ i < vID, ∀ w, (get views i) = some w → ViewOK w)
    (hroots : evalRoot views nodes vID v = true)
    (hnodes : ∀ (i : Nat) (a : Node), (get nodes i) = some a → evalNode views nodes a = true) :
    ViewOK v := by
  have closed (k : Nat) : ∀ (i : Nat) (a : Node), (get nodes i) = some a → nv a = vID → nk a = k →
      ¬ CoreSigned.live signedOps (vg v) k (ns a).toFinset := by
    induction k with
    | zero =>
      intro i a found owner fuel h
      have ok := hnodes i a found
      simp only [evalNode,owner,hv,fuel,Bool.and_true,Bool.and_eq_true,decide_eq_true_eq,bne_iff_ne] at ok
      exact ok.2 (singleton_list ok.1 h)
    | succ k ih =>
      intro i a found owner fuel
      have ok := hnodes i a found
      simp only [evalNode,owner,hv,fuel,Bool.and_eq_true,decide_eq_true_eq,bne_iff_ne] at ok
      apply step_no _ _ _ ok.1.1 ok.1.2
      intro ws hm
      obtain ⟨j,good⟩ := scanFrom_sound _ ok.2 hm
      exact checkHint_sound earlier ih good
  intro build_
  classical
  obtain ⟨S, sub, path⟩ := CoreSigned.compress build_
  let ws := (vs v).filter (· ∈ S)
  have eq : ws.toFinset = S := by
    ext w
    simp only [ws,List.mem_toFinset,List.mem_filter,decide_eq_true_eq,and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (sub hw)
  obtain ⟨q,hq⟩ := scanFrom_sound _ hroots (show ws ∈ (vs v).sublists from
    List.mem_sublists.mpr (List.filter_sublist ..))
  exact checkHint_sound earlier (closed _) hq (eq.symm ▸ path)

theorem whole_sound (views : Table View) (nodes : Table Node)
    (allRoots : ∀ (i : Nat) (v : View), (get views i) = some v → evalRoot views nodes i v = true)
    (allNodes : ∀ (i : Nat) (a : Node), (get nodes i) = some a → evalNode views nodes a = true)
    (i : Nat) (v : View) (hv : (get views i) = some v) : ViewOK v := by
  induction i using Nat.strong_induction_on generalizing v with
  | ind i ih => exact view_from_earlier views nodes i v hv ih (allRoots i v hv) allNodes

def checkRootAt (views : Table View) (nodes : Table Node) (i : Nat) : Bool :=
  match (get views i) with
  | some v => evalRoot views nodes i v
  | none => true

def checkNodeAt (views : Table View) (nodes : Table Node) (i : Nat) : Bool :=
  match (get nodes i) with
  | some a => evalNode views nodes a
  | none => true

def passBlock (check : Nat → Bool) (start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => passBlock check start n && check (start+n)

theorem block_at (check : Nat → Bool) {s n i} (ok : passBlock check s n = true)
    (lo : s ≤ i) (hi : i < s+n) : check i = true := by
  induction n with
  | zero => omega
  | succ n ih =>
    have parts := Bool.and_eq_true_iff.mp ok
    by_cases lt : i < s+n
    · exact ih parts.1 lt
    · have eq : i = s+n := by omega
      exact eq ▸ parts.2

theorem merge_blocks {c : Nat → Bool} {s a b : Nat} (x : passBlock c s a = true)
    (y : passBlock c (s+a) b = true) : passBlock c s (a+b) = true := by
  induction b with
  | zero => simpa using x
  | succ b ih =>
    have parts := Bool.and_eq_true_iff.mp y
    change passBlock c s (a+b) && c (s+(a+b)) = true
    exact Bool.and_eq_true_iff.mpr ⟨ih parts.1,by simpa [Nat.add_assoc] using parts.2⟩

theorem certified_view (views : Table View) (nodes : Table Node)
    (roots : passBlock (checkRootAt views nodes) 0 views.1 = true)
    (states : passBlock (checkNodeAt views nodes) 0 nodes.1 = true)
    {i : Nat} {v : View} (hv : (get views i) = some v) : ViewOK v := by
  apply whole_sound views nodes _ _ i v hv
  · intro j w hw
    have hj : j < views.1 := by by_contra! lo; simp [get, Nat.not_lt_of_ge lo] at hw
    have ok := block_at _ roots (i := j) (Nat.zero_le _) (by omega)
    simpa [checkRootAt,hw] using ok
  · intro j a ha
    have hj : j < nodes.1 := by by_contra! lo; simp [get, Nat.not_lt_of_ge lo] at ha
    have ok := block_at _ states (i := j) (Nat.zero_le _) (by omega)
    simpa [checkNodeAt,ha] using ok

end SignedProjection.QFast
namespace SignedProjection.QFast

def rowAt (m : Array Nat) (k : Fin 64) := Fin.ofNat 64 (m[k.val]?.getD 0)
def rowWord (m : Array Nat) (w : Word) : Word :=
  (BitVec.ofBoolListLE (List.ofFn (fun k : Fin 64 => w[(rowAt m k).val]))).cast List.length_ofFn

theorem rowWord_bit (m : Array Nat) (w : Word) (j : Nat) (hj : j < 64) :
    (rowWord m w)[j] = w[(rowAt m ⟨j,hj⟩).val] := by
  rw [← BitVec.getLsbD_eq_getElem hj]
  simp only [rowWord, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn, hj, dite_true, Option.getD_some]

theorem rowWord_and (m : Array Nat) (x y : Word) : rowWord m (x &&& y) = rowWord m x &&& rowWord m y :=
  BitVec.eq_of_getElem_eq fun j hj => by simp only [rowWord_bit,BitVec.getElem_and]
theorem rowWord_or (m : Array Nat) (x y : Word) : rowWord m (x ||| y) = rowWord m x ||| rowWord m y :=
  BitVec.eq_of_getElem_eq fun j hj => by simp only [rowWord_bit,BitVec.getElem_or]
theorem rowWord_not (m : Array Nat) (x : Word) : rowWord m (~~~x) = ~~~rowWord m x :=
  BitVec.eq_of_getElem_eq fun j hj => by simp only [rowWord_bit,BitVec.getElem_not]

def viewMap (m : Array Nat) (v : View) (w : Word) := signedPin (vm v) (va v) (rowWord m w)
theorem viewMap_ops (m : Array Nat) (v : View) {a b c : Word} (hc : c ∈ signedOps a b) :
    viewMap m v c ∈ signedOps (viewMap m v a) (viewMap m v b) := by
  apply signedPin_ops
  simp only [signedOps,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hc ⊢
  rcases hc with rfl|rfl|rfl|rfl
  · exact Or.inl (rowWord_and ..)
  · exact Or.inr (Or.inl (rowWord_or ..))
  · exact Or.inr (Or.inr (Or.inl (by rw [rowWord_and,rowWord_not])))
  · exact Or.inr (Or.inr (Or.inr (by rw [rowWord_and,rowWord_not])))

def viewAliasOK (m : Array Nat) (src dst : View) : Bool :=
  (vg dst != 0) && (viewMap m dst (vg src) == vg dst) && decide (vk src ≤ vk dst) &&
  (vs src).all fun w => viewMap m dst w == 0 || (vs dst).contains (viewMap m dst w)

theorem viewAlias_sound {m : Array Nat} {src dst : View} (yes : ViewOK dst)
    (valid : viewAliasOK m src dst = true) : ViewOK src := by
  simp only [viewAliasOK,Bool.and_eq_true, bne_iff_ne,beq_iff_eq,decide_eq_true_eq] at valid
  obtain ⟨⟨⟨nz,go⟩,le⟩,all⟩ := valid
  intro run
  obtain ⟨S,sub,path⟩ := CoreSigned.compress run
  have ng := fun h : viewMap m dst (vg src) = 0 => nz (go.symm.trans h)
  obtain ⟨j,hj,T,ts,tail⟩ := projected (viewMap m dst) signedOps signedOps _ ng
    (viewMap_ops m dst) zero_left zero_right equal_inputs path
  have supply : T ⊆ (vs dst).toFinset := by
    intro y hy
    obtain ⟨pn,w,hw,rfl⟩ := (avail_mem _).mp (ts hy)
    have h := List.all_eq_true.mp all w (List.mem_toFinset.mp (sub hw))
    simp only [Bool.or_eq_true,beq_iff_eq] at h
    exact List.mem_toFinset.mpr (List.contains_iff_mem.mp (h.resolve_left pn))
  rw [go] at tail
  exact yes (pad_build (by omega) (live_build tail supply))

abbrev AliasTable := Nat → Option (Nat × Array Nat)
def symCheckRoot (aliases : AliasTable) (views : Table View) (nodes : Table Node) (i : Nat) : Bool :=
  match get views i with
  | none => true
  | some v => match aliases i with
    | none => evalRoot views nodes i v
    | some (j,m) => decide (j < i) &&
      match get views j with
      | none => false
      | some w => viewAliasOK m v w

theorem symCertified (aliases : AliasTable) (views : Table View) (nodes : Table Node)
    (roots : passBlock (symCheckRoot aliases views nodes) 0 views.1 = true)
    (states : passBlock (checkNodeAt views nodes) 0 nodes.1 = true)
    {i : Nat} {v : View} (hv : get views i = some v) : ViewOK v := by
  have allNodes (j : Nat) (a : Node) (ha : get nodes j = some a) : evalNode views nodes a = true := by
    have hj : j < nodes.1 := by by_contra! lo; simp [get, Nat.not_lt_of_ge lo] at ha
    have ok := block_at _ states (i := j) (Nat.zero_le _) (by omega)
    simpa [checkNodeAt,ha] using ok
  induction i using Nat.strong_induction_on generalizing v with
  | ind i ih =>
    have hi : i < views.1 := by by_contra! lo; simp [get, Nat.not_lt_of_ge lo] at hv
    have ok := block_at _ roots (i := i) (Nat.zero_le _) (by omega)
    simp only [symCheckRoot,hv] at ok
    cases he : aliases i with
    | none =>
      exact view_from_earlier views nodes i v hv ih (by simpa only [he] using ok) allNodes
    | some x =>
      rcases x with ⟨j,m⟩
      simp only [he,Bool.and_eq_true,decide_eq_true_eq] at ok
      cases hh : get views j with
      | none => simp [hh] at ok
      | some w => exact viewAlias_sound (ih j ok.1 hh) (by simpa only [hh] using ok.2)

end SignedProjection.QFast


namespace LowerSymSix
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit :=
  ⟨[⟨.and,[0,1]⟩, ⟨.and,[2,3]⟩, ⟨.and,[4,2]⟩, ⟨.or,[6,7]⟩, ⟨.and,[5,9]⟩, ⟨.or,[0,1]⟩, ⟨.and,[3,11]⟩, ⟨.and,[8,9]⟩, ⟨.or,[4,10]⟩, ⟨.or,[12,13]⟩, ⟨.and,[14,15]⟩],16⟩

theorem size : witness.size = 11 := rfl

theorem monotone : Monotone2 witness := by
  simp [Monotone2,witness]

set_option maxRecDepth 16000 in
theorem correct : ∀ x : Fin 6 → Bool, witness.eval (List.ofFn x) =
    Nat.testBit (4269860864 * 2 ^ 32 + 4269801472) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel

end LowerSymSix

namespace Direct64
open PEqualNP.CircuitLowerBounds SignedProjection
abbrev W := BitVec 64
abbrev basicOps (a b : W) := signedOps a b
abbrev goal : W := ~~~0xfe80e800fe800000
open CoreSigned (build)
def tableB (x : Fin 6 → Bool) :=
  Nat.testBit (4269860864 * 2 ^ 32 + 4269801472) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def holds (av : Finset W) (z : W) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

set_option maxRecDepth 100000 in
theorem holds_insert {av : Finset W} {z a : W} (h : holds av z) : holds (insert a av) z := by
  rcases h with h|h|⟨u,hu,he⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨u,Finset.mem_insert_of_mem hu,he⟩)

set_option maxRecDepth 100000 in
theorem holds_not {av : Finset W} {z : W} (h : holds av z) : holds av (~~~z) := by
  rcases h with rfl|rfl|⟨a,ha,he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he|he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable (av : Finset W) (z : W) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps a b, holds (insert w av) z

set_option maxRecDepth 100000 in
theorem reachable_not {av : Finset W} {z : W} (h : reachable av z) : reachable av (~~~z) := by
  rcases h with h|⟨a,ha,b,hb,ne,w,hop,hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a,ha,b,hb,ne,w,hop,holds_not hw⟩

set_option maxRecDepth 100000 in
theorem and_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x &&& y) := by
  have const : holds av (0 : W) := .inl rfl
  have oldx := hx
  rcases hx with rfl|rfl|⟨a,ha,ea⟩
  · rw [show (0 : W) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · change reachable av (BitVec.allOnes 64 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 64)
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
  · exact add _ (by simp [basicOps,SignedProjection.signedOps] : a &&& b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,SignedProjection.signedOps] : a &&& ~~~b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,SignedProjection.signedOps] : b &&& ~~~a ∈ basicOps a b) _ (.inl (BitVec.and_comm ..))
  · exact add _ (by simp [basicOps,SignedProjection.signedOps] : a ||| b ∈ basicOps a b) _ (.inr BitVec.not_or.symm)

set_option maxRecDepth 100000 in
theorem or_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))

private def bit (k : Fin 64) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

set_option maxRecDepth 100000 in
private theorem read_bit (w : List W) (i : ℕ) (k : Fin 64) :
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

set_option maxRecDepth 100000 in
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 64) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#64)[k.val] = false; simp
  all_goals rcases hop with rfl|rfl|rfl <;>
    simp only [step, List.map_cons,List.map_nil,read_bit,List.map_append] <;>
    simp only [action, GateOp.eval, List.foldr_cons,List.foldr_nil,List.head?_cons,List.head?_nil,
      List.headD_cons,List.headD_nil,Option.map_some,Option.map_none,Option.getD_some,Option.getD_none,
      List.all_cons,List.all_nil,List.any_cons,List.any_nil,List.map_cons,List.map_nil,id_eq,
      Bool.and_true,Bool.or_false, bit,BitVec.getElem_and,BitVec.getElem_or,BitVec.getElem_not,
      bit0,Bool.not_false]

def isBinary (g : Gate) : Bool := match g.op with
  | .not => false
  | _ => true
def binaryCost (gs : List Gate) := (gs.filter isBinary).length

set_option maxRecDepth 100000 in
theorem available_read {av : Finset W} {w : List W} (hw : ∀ u ∈ w, holds av u) (i : ℕ) :
    holds av (w.getD i 0) := by
  by_cases h : i < w.length
  · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    exact .inl rfl

set_option maxRecDepth 100000 in
theorem gate_reach (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (g : Gate) (hg : legal g) :
    if isBinary g then reachable av (action w g) else holds av (action w g) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
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

set_option maxRecDepth 100000 in
theorem compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k (~~~goal)) :
    ∃ t, (t = goal ∨ t = ~~~goal) ∧ build basicOps t (binaryCost gs) av := by
  induction gs generalizing w av with
  | nil =>
    have hv : w.getD out 0 = ~~~goal := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i,hi⟩
    have h := hv ▸ available_read hw out
    rcases h with zero|ones|⟨t,ht,eq|eq⟩
    · exact False.elim ((by decide : ~~~goal ≠ 0) zero)
    · exact False.elim ((by decide : ~~~goal ≠ ~~~0) ones)
    · exact ⟨t, .inr eq.symm, ht⟩
    · exact ⟨t, .inl (by simpa only [BitVec.not_not] using congrArg (fun w : W => ~~~w) eq.symm), ht⟩
  | cons g gs ih =>
    let z := action w g
    have stepOK := action_spec w g (hg g (by simp))
    have nextEval : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k (~~~goal) := by
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


def cols : List W := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]

theorem sample64 : ∀ k : Fin 64, tableB (fun i => (cols.getD i.val 0)[k.val]) = (~~~goal)[k.val] := by
  decide +kernel

theorem zero_open (k : ℕ) {t : W} (av : Finset W) (hz : ∀ u ∈ av, u.getLsbD 0 = false)
    (h : build basicOps t k av) : t.getLsbD 0 = false := by
  induction k generalizing av with
  | zero => exact hz t h
  | succ k ih =>
    rcases h with skip | ⟨a,ha,b,hb,_,z,hop,tail⟩
    · exact ih av hz skip
    · apply ih (insert z av) _ tail
      intro u hu
      rcases Finset.mem_insert.mp hu with rfl|hu
      · simp only [basicOps,signedOps,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hop
        rcases hop with rfl|rfl|rfl|rfl <;> simp only [BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,hz a ha,hz b hb,Bool.false_and,Bool.or_self]
      · exact hz u hu

theorem low (reject : ¬ build basicOps (0xfe80e800fe800000 : W) 9 cols.toFinset)
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = tableB x) : 9 < binaryCost gs := by
  by_contra! low
  have width : cols.length = 6 := rfl
  have init : ∀ u ∈ cols, holds cols.toFinset u := by
    intro u hu
    exact .inr (.inr ⟨u, List.mem_toFinset.mpr hu, .inl rfl⟩)
  have evaluate (k : Fin 64) :
      (gs.foldl step (cols.map (bit k))).getD o false = bit k (~~~goal) := by
    let x (i : Fin 6) : Bool := bit k (cols.getD i.val 0)
    have same : List.ofFn x = cols.map (bit k) := by
      apply List.ext_getElem
      · simp [width]
      · intro i hi hj
        have hlt : i < cols.length := by simpa using hj
        simp only [List.getElem_ofFn, List.getElem_map, x, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs,o⟩ (cols.map (bit k)) = bit k (~~~goal)
    rw [← same, he]
    exact sample64 k
  obtain ⟨t, ht, run⟩ := compile gs o hg cols cols.toFinset init evaluate

  have h0 : ∀ u ∈ cols.toFinset, u.getLsbD 0 = false := by
    intro u hu
    simp only [cols,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel
  rcases ht with rfl|rfl
  · have odd : goal.getLsbD 0 ≠ false := by decide +kernel
    exact odd (zero_open _ _ h0 run)
  · apply reject
    apply pad_build low
    exact run
end Direct64

namespace LowerSymSix
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
theorem finish
    (reject : ¬ CoreSigned.build SignedProjection.signedOps (0xfe80e800fe800000 : BitVec 64) 9 Direct64.cols.toFinset) :
∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4269860864 * 2 ^ 32 + 4269801472) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4269860864 * 2 ^ 32 + 4269801472) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  rintro s ⟨C, hg, hs, he⟩
  by_cases neg : ∃ g ∈ C.gates, g.op = .not
  · obtain ⟨g, hm, op⟩ := neg
    have lo := Direct64.low reject C.gates C.output hg he
    have proper : Direct64.binaryCost C.gates < C.gates.length := by
      apply List.length_filter_lt_length_iff_exists.mpr
      exact ⟨g, hm, by simp [Direct64.isBinary, op]⟩
    have cap : C.gates.length ≤ s := hs
    exact ⟨witness, monotone, by rw [size]; omega, correct⟩
  · refine ⟨C, ?_, hs, he⟩
    intro g hm
    obtain ⟨hop, hin⟩ := hg g hm
    refine ⟨?_, hin⟩
    rcases hop with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (neg ⟨g, hm, h⟩).elim

end LowerSymSix


namespace SignedProjection

def ew0 : Word := 0xaa00aa

def ew1 : Word := 0xcc00cc

def ew2 : Word := 0xf000f0

def ew3 : Word := 0xaa00000

def ew4 : Word := 0xaa00aa0

def ew5 : Word := 0xcc00000

def ew6 : Word := 0xcc00cc0

def ew7 : Word := 0xf000000

def ew8 : Word := 0xf000f00

def ew9 : Word := 0xff00000

def ew10 : Word := 0x22882288

def ew11 : Word := 0x30c030c0

def ew12 : Word := 0x33003300

def ew13 : Word := 0x33cc0000

def ew14 : Word := 0x44884488

def ew15 : Word := 0x50a050a0

def ew16 : Word := 0x55005500

def ew17 : Word := 0x55aa0000

def ew18 : Word := 0x82828282

def ew19 : Word := 0x84848484

def ew20 : Word := 0x88880000

def ew21 : Word := 0x88888888

def ew22 : Word := 0x90900000

def ew23 : Word := 0x90909090

def ew24 : Word := 0x99000000

def ew25 : Word := 0x99009900

def ew26 : Word := 0x99990000

def ew27 : Word := 0xa0a0a0a0

def ew28 : Word := 0xa500a500

def ew29 : Word := 0xa5a50000

def ew30 : Word := 0xaaaa0000

def ew31 : Word := 0xaaaaaaaa

def ew32 : Word := 0xc0c0c0c0

def ew33 : Word := 0xc300c300

def ew34 : Word := 0xc3c30000

def ew35 : Word := 0xcccc0000

def ew36 : Word := 0xcccccccc

def ew37 : Word := 0xeeeeeeee

def ew38 : Word := 0xf0f00000

def ew39 : Word := 0xf0f0f0f0

def ew40 : Word := 0xfafafafa

def ew41 : Word := 0xfcfcfcfc

def ew42 : Word := 0xff000000

def ew43 : Word := 0xff00ff00

def ew44 : Word := 0xffff0000

def ew45 : Word := 0xa0a0a0a0000

def ew46 : Word := 0xaa00aa00000

def ew47 : Word := 0xc0c0c0c0000

def ew48 : Word := 0xcc00cc00000

def ew49 : Word := 0xf000f000000

def ew50 : Word := 0xf0f00000000

def ew51 : Word := 0xff000000000

def ew52 : Word := 0x222222220000

def ew53 : Word := 0x303030300000

def ew54 : Word := 0x330033000000

def ew55 : Word := 0x333300000000

def ew56 : Word := 0x444444440000

def ew57 : Word := 0x505050500000

def ew58 : Word := 0x550055000000

def ew59 : Word := 0x555500000000

def ew60 : Word := 0x888888880000

def ew61 : Word := 0x909090900000

def ew62 : Word := 0x990099000000

def ew63 : Word := 0x999900000000

def ew64 : Word := 0xa0a0a0a00000

def ew65 : Word := 0xaa0000000000

def ew66 : Word := 0xaa00000000aa

def ew67 : Word := 0xaa000000aa00

def ew68 : Word := 0xaa00aa000000

def ew69 : Word := 0xaaaa00000000

def ew70 : Word := 0xaaaa0000aaaa

def ew71 : Word := 0xaaaaaaaa0000

def ew72 : Word := 0xcc00000000cc

def ew73 : Word := 0xcc000000cc00

def ew74 : Word := 0xcccc0000cccc

def ew75 : Word := 0xcccccccc0000

def ew76 : Word := 0xf000000000f0

def ew77 : Word := 0xf0000000f000

def ew78 : Word := 0xf0f00000f0f0

def ew79 : Word := 0xf0f0f0f00000

def ew80 : Word := 0xff0000000000

def ew81 : Word := 0xff000000ff00

def ew82 : Word := 0xff00ff000000

def ew83 : Word := 0xffff00000000

def ew84 : Word := 0x8000000800000

def ew85 : Word := 0x8080000000000

def ew86 : Word := 0x8080000808000

def ew87 : Word := 0xa000000a00000

def ew88 : Word := 0xa0a0000000000

def ew89 : Word := 0xa0a0000a0a000

def ew90 : Word := 0xc0c0000c0c000

def ew91 : Word := 0xf000000f00000

def ew92 : Word := 0xf0f0000000000

def ew93 : Word := 0x22220000888800

def ew94 : Word := 0x30300000c0c000

def ew95 : Word := 0x33000000cc0000

def ew96 : Word := 0x33330000000000

def ew97 : Word := 0x44440000888800

def ew98 : Word := 0x50500000a0a000

def ew99 : Word := 0x55000000aa0000

def ew100 : Word := 0x55550000000000

def ew101 : Word := 0x88008800880088

def ew102 : Word := 0x88008844004400

def ew103 : Word := 0x88880000000000

def ew104 : Word := 0x88880000222200

def ew105 : Word := 0x88880000444400

def ew106 : Word := 0x88880000888800

def ew107 : Word := 0xa000a000a000a0

def ew108 : Word := 0xa000a050005000

def ew109 : Word := 0xa0a00000000000

def ew110 : Word := 0xa0a000000a0a00

def ew111 : Word := 0xa0a00000505000

def ew112 : Word := 0xa0a00000a0a000

def ew113 : Word := 0xaa000000000000

def ew114 : Word := 0xaa000000550000

def ew115 : Word := 0xaa000000aa0000

def ew116 : Word := 0xaa000055000000

def ew117 : Word := 0xaa00aa00000000

def ew118 : Word := 0xaaaa0000000000

def ew119 : Word := 0xaaaa0000aaaa00

def ew120 : Word := 0xc0c000000c0c00

def ew121 : Word := 0xc0c00000303000

def ew122 : Word := 0xc0c00000c0c000

def ew123 : Word := 0xcc000000330000

def ew124 : Word := 0xcc000000cc0000

def ew125 : Word := 0xcccc0000000000

def ew126 : Word := 0xcccc0000cccc00

def ew127 : Word := 0xf00000000f0000

def ew128 : Word := 0xf0000000f00000

def ew129 : Word := 0xf0f00000000000

def ew130 : Word := 0xf0f00000f0f000

def ew131 : Word := 0xff000000ff0000

def ew132 : Word := 0xffff0000000000

def ew133 : Word := 0x800080080008000

def ew134 : Word := 0x808000080800000

def ew135 : Word := 0x808080800000000

def ew136 : Word := 0x808080804040404

def ew137 : Word := 0x808080880808080

def ew138 : Word := 0x880088000000000

def ew139 : Word := 0x880088002200220

def ew140 : Word := 0x880088004400440

def ew141 : Word := 0x880088008800880

def ew142 : Word := 0xa000a0000000000

def ew143 : Word := 0xa000a00000a000a

def ew144 : Word := 0xa000a0000a000a0

def ew145 : Word := 0xa000a0005000500

def ew146 : Word := 0xa000a000a000a00

def ew147 : Word := 0xa000a00a000a000

def ew148 : Word := 0xa0a000005050000

def ew149 : Word := 0xa0a0000a0a00000

def ew150 : Word := 0xa0a0a0a00000000

def ew151 : Word := 0xa0a0a0a0a0a0a0a

def ew152 : Word := 0xaa0000000000000

def ew153 : Word := 0xaa0000005500000

def ew154 : Word := 0xaa000000aa00000

def ew155 : Word := 0xaa00aa000000000

def ew156 : Word := 0xaa00aa00aa00aa0

def ew157 : Word := 0xc000c00000c000c

def ew158 : Word := 0xc000c0000c000c0

def ew159 : Word := 0xc000c0003000300

def ew160 : Word := 0xc000c000c000c00

def ew161 : Word := 0xc0c0c0c0c0c0c0c

def ew162 : Word := 0xcc0000003300000

def ew163 : Word := 0xcc000000cc00000

def ew164 : Word := 0xcc00cc000000000

def ew165 : Word := 0xcc00cc00cc00cc0

def ew166 : Word := 0xf000000000f0000

def ew167 : Word := 0xf00000000f00000

def ew168 : Word := 0xf0000000f000000

def ew169 : Word := 0xf000f0000000000

def ew170 : Word := 0xf000f000f000f00

def ew171 : Word := 0xf0f00000f0f0000

def ew172 : Word := 0xf0f0f0f00000000

def ew173 : Word := 0xff0000000000000

def ew174 : Word := 0xff000000ff00000

def ew175 : Word := 0xff00ff000000000

def ew176 : Word := 0x1090109010901090

def ew177 : Word := 0x2020202010101010

def ew178 : Word := 0x2020202080808080

def ew179 : Word := 0x2080208020802080

def ew180 : Word := 0x2200220000220022

def ew181 : Word := 0x2200220011001100

def ew182 : Word := 0x2200220022002200

def ew183 : Word := 0x2200220088008800

def ew184 : Word := 0x2222000011110000

def ew185 : Word := 0x2222000088880000

def ew186 : Word := 0x2222222200000000

def ew187 : Word := 0x2222222222222222

def ew188 : Word := 0x2288000022880000

def ew189 : Word := 0x2288228800000000

def ew190 : Word := 0x2288228822882288

def ew191 : Word := 0x3000300000300030

def ew192 : Word := 0x3000300030003000

def ew193 : Word := 0x3030303030303030

def ew194 : Word := 0x30c0000030c00000

def ew195 : Word := 0x30c030c030c030c0

def ew196 : Word := 0x3300000000330000

def ew197 : Word := 0x3300000033000000

def ew198 : Word := 0x3300330000000000

def ew199 : Word := 0x3300330033003300

def ew200 : Word := 0x3333000033330000

def ew201 : Word := 0x3333333300000000

def ew202 : Word := 0x33cc000000000000

def ew203 : Word := 0x33cc000033cc0000

def ew204 : Word := 0x33cc33cc00000000

def ew205 : Word := 0x4400440000440044

def ew206 : Word := 0x4400440044004400

def ew207 : Word := 0x4444444444444444

def ew208 : Word := 0x4488000044880000

def ew209 : Word := 0x4488448844884488

def ew210 : Word := 0x5000500000500050

def ew211 : Word := 0x5000500050005000

def ew212 : Word := 0x5050505050505050

def ew213 : Word := 0x50a0000050a00000

def ew214 : Word := 0x50a050a050a050a0

def ew215 : Word := 0x5500000000550000

def ew216 : Word := 0x5500000055000000

def ew217 : Word := 0x5500550000000000

def ew218 : Word := 0x5500550055005500

def ew219 : Word := 0x5555000055550000

def ew220 : Word := 0x5555555500000000

def ew221 : Word := 0x55aa000000000000

def ew222 : Word := 0x55aa000055aa0000

def ew223 : Word := 0x55aa55aa00000000

def ew224 : Word := 0x8000800008000800

def ew225 : Word := 0x8080000008080000

def ew226 : Word := 0x8080080880800808

def ew227 : Word := 0x8080202080802020

def ew228 : Word := 0x8080808000000000

def ew229 : Word := 0x8080808008080808

def ew230 : Word := 0x8080808010101010

def ew231 : Word := 0x8080808020202020

def ew232 : Word := 0x8080808080808080

def ew233 : Word := 0x8200820082008200

def ew234 : Word := 0x8282000082820000

def ew235 : Word := 0x8282828200000000

def ew236 : Word := 0x8282828282828282

def ew237 : Word := 0x8484000084840000

def ew238 : Word := 0x8484848484848484

def ew239 : Word := 0x8800220088002200

def ew240 : Word := 0x8800880000880088

def ew241 : Word := 0x8800880011001100

def ew242 : Word := 0x8800880022002200

def ew243 : Word := 0x8800880044004400

def ew244 : Word := 0x8800880088008800

def ew245 : Word := 0x8888000011110000

def ew246 : Word := 0x8888000022220000

def ew247 : Word := 0x8888000044440000

def ew248 : Word := 0x8888000088880000

def ew249 : Word := 0x8888222200000000

def ew250 : Word := 0x8888888800000000

def ew251 : Word := 0x8888888822222222

def ew252 : Word := 0x8888888844444444

def ew253 : Word := 0x8888888888888888

def ew254 : Word := 0x9000090090000900

def ew255 : Word := 0x9000900000900090

def ew256 : Word := 0x9000900090009000

def ew257 : Word := 0x9090000090900000

def ew258 : Word := 0x9090090900000000

def ew259 : Word := 0x9090909000000000

def ew260 : Word := 0x9090909090909090

def ew261 : Word := 0x9900000000990000

def ew262 : Word := 0x9900000099000000

def ew263 : Word := 0x9900990000000000

def ew264 : Word := 0x9900990099009900

def ew265 : Word := 0x9999000000000000

def ew266 : Word := 0x9999000099990000

def ew267 : Word := 0x9999999900000000

def ew268 : Word := 0xa0000a00a0000a00

def ew269 : Word := 0xa000a00000a000a0

def ew270 : Word := 0xa000a0000a000a00

def ew271 : Word := 0xa000a00050005000

def ew272 : Word := 0xa000a000a000a000

def ew273 : Word := 0xa0a000000a0a0000

def ew274 : Word := 0xa0a0000050500000

def ew275 : Word := 0xa0a00000a0a00000

def ew276 : Word := 0xa0a00a0a00000000

def ew277 : Word := 0xa0a0a0a000000000

def ew278 : Word := 0xa0a0a0a00a0a0a0a

def ew279 : Word := 0xa0a0a0a050505050

def ew280 : Word := 0xa0a0a0a0a0a0a0a0

def ew281 : Word := 0xa5000000a5000000

def ew282 : Word := 0xa500a500a500a500

def ew283 : Word := 0xa5a5000000000000

def ew284 : Word := 0xa5a50000a5a50000

def ew285 : Word := 0xa5a5a5a500000000

def ew286 : Word := 0xaa00000000aa0000

def ew287 : Word := 0xaa00000055000000

def ew288 : Word := 0xaa000000aa00aa00

def ew289 : Word := 0xaa00aa0000000000

def ew290 : Word := 0xaa00aa0000aa00aa

def ew291 : Word := 0xaa00aa0055005500

def ew292 : Word := 0xaa00aa00aa00aa00

def ew293 : Word := 0xaaaa000000000000

def ew294 : Word := 0xaaaa000055550000

def ew295 : Word := 0xaaaa0000aaaa0000

def ew296 : Word := 0xaaaaaa00aaaa0000

def ew297 : Word := 0xaaaaaaaa00000000

def ew298 : Word := 0xaaaaaaaaaaaaaaaa

def ew299 : Word := 0xc000c000c000c000

def ew300 : Word := 0xc0c00000c0c00000

def ew301 : Word := 0xc0c0c0c000000000

def ew302 : Word := 0xc0c0c0c00c0c0c0c

def ew303 : Word := 0xc0c0c0c030303030

def ew304 : Word := 0xc0c0c0c0c0c0c0c0

def ew305 : Word := 0xc3000000c3000000

def ew306 : Word := 0xc300c300c300c300

def ew307 : Word := 0xc3c3000000000000

def ew308 : Word := 0xc3c30000c3c30000

def ew309 : Word := 0xc3c3c3c300000000

def ew310 : Word := 0xcc00cc0000cc00cc

def ew311 : Word := 0xcc00cc0033003300

def ew312 : Word := 0xcc00cc00cc00cc00

def ew313 : Word := 0xcccc000033330000

def ew314 : Word := 0xcccc0000cccc0000

def ew315 : Word := 0xcccccccc00000000

def ew316 : Word := 0xcccccccccccccccc

def ew317 : Word := 0xeeee0000eeee0000

def ew318 : Word := 0xf000f00000f000f0

def ew319 : Word := 0xf000f0000f000f00

def ew320 : Word := 0xf000f000f000f000

def ew321 : Word := 0xf0f000000f0f0000

def ew322 : Word := 0xf0f00000f0f00000

def ew323 : Word := 0xf0f0f0f000000000

def ew324 : Word := 0xf0f0f0f0f0f0f0f0

def ew325 : Word := 0xfafa0000fafa0000

def ew326 : Word := 0xfcfc0000fcfc0000

def ew327 : Word := 0xff00000000ff0000

def ew328 : Word := 0xff000000ff000000

def ew329 : Word := 0xff000000ff00ff00

def ew330 : Word := 0xff00ff0000000000

def ew331 : Word := 0xff00ff00ff000000

def ew332 : Word := 0xff00ff00ff00ff00

def ew333 : Word := 0xffff000000000000

def ew334 : Word := 0xffff0000ffff0000

def ew335 : Word := 0xffffffff00000000

def ew336 : Word := 0xffffffffffff0000

def labelsBlock0 : Array Nat := #[
  0x2b2c,
  0x171c,
  0x1944,
  0x174c,
  0x1754,
  0x1758,
  0x1924,
  0x1960,
  0x1a60,
  0x1c60,
  0x2d34,
  0x1a48,
  0x2ba4,
  0x2da4,
  0x2b0c,
  0x1c50
]

def labelsBlock1 : Array Nat := #[
  0x1a28,
  0x2ba8,
  0x1122,
  0x1750,
  0x2b8c,
  0x113e,
  0x1126,
  0x2e38,
  0x116e,
  0x1c40,
  0x170c,
  0x1904,
  0x1744,
  0x1176,
  0x1146,
  0x1940
]

def labelsBlock2 : Array Nat := #[
  0x1a40,
  0x1714,
  0x2b24,
  0x2d24,
  0x1748,
  0x2b28,
  0x1718,
  0x114a,
  0x1b4c,
  0x1072,
  0x1c30,
  0x112e,
  0x112a,
  0x19a4,
  0x443122,
  0x10aa
]

def labelsBlock3 : Array Nat := #[
  0x2d14,
  0x1c20,
  0x2ea8,
  0x2db0,
  0x179c,
  0x1152,
  0x114e,
  0x1954,
  0x1920,
  0x1132,
  0x1d54,
  0x2eb0,
  0x1a20,
  0x1026,
  0x1b2c,
  0x1156
]

def labelsBlock4 : Array Nat := #[
  0x2b20,
  0x115e,
  0x379c,
  0x1740,
  0x106e,
  0x743146,
  0x173c,
  0x1052,
  0x10be,
  0x115a,
  0x74313e,
  0x117a,
  0x543146,
  0x39a4,
  0x1022,
  0x2b3c
]

def labelsBlock5 : Array Nat := #[
  0x1b60,
  0x1710,
  0x2b04,
  0x74316e,
  0x430122,
  0x74312a,
  0x431122,
  0x432122,
  0x11494313e,
  0x1a08,
  0x371c,
  0x2d94,
  0x2e18,
  0x410122,
  0x420122,
  0x421122
]

def labelsBlock6 : Array Nat := #[
  0x2d04,
  0x10a2,
  0x11494316e,
  0x2b08,
  0x1e58,
  0x1092,
  0x743176,
  0x1136,
  0x440122,
  0x441122,
  0x442122,
  0x443126,
  0x114943176,
  0x1b44,
  0x1d44,
  0x2ba0
]

def labelsBlock7 : Array Nat := #[
  0x1162,
  0x743132,
  0x105e,
  0x194c,
  0x103e,
  0x1b0c,
  0x1700,
  0x3924,
  0x640122,
  0x1166,
  0x641122,
  0x642122,
  0x643122,
  0x37cc,
  0x1aa8,
  0x1900
]

def labelsBlock8 : Array Nat := #[
  0x1a58,
  0x10ae,
  0x10ba,
  0x43113e,
  0x63113e,
  0x74312e,
  0x743156,
  0x43013e,
  0x63013e,
  0x1a00,
  0x2b00,
  0x1950,
  0x1a50,
  0x10e6,
  0x10ca,
  0x1062
]

def labelsBlock9 : Array Nat := #[
  0x41013e,
  0x63213e,
  0x1142,
  0x1d34,
  0x1036,
  0x1046,
  0x2d30,
  0x106a,
  0x2e98,
  0x43016e,
  0x63016e,
  0x43116e,
  0x63116e,
  0x63216e,
  0x64213e,
  0x1c974313e
]

def labelsBlock10 : Array Nat := #[
  0x17cc,
  0x1b40,
  0x1c00,
  0x41016e,
  0x74315e,
  0x42013e,
  0x42113e,
  0x43213e,
  0x632176,
  0x64216e,
  0x1c974316e,
  0x2b1c,
  0x1734,
  0x109e,
  0x1914,
  0x10f2
]

def labelsBlock11 : Array Nat := #[
  0x37d4,
  0x2d20,
  0x3944,
  0x743136,
  0x743152,
  0x2e28,
  0x430176,
  0x630176,
  0x431176,
  0x631176,
  0x42116e,
  0x43216e,
  0x44213e,
  0x642176,
  0x54313e,
  0x1c9743176
]

def labelsBlock12 : Array Nat := #[
  0x1704,
  0x41017a,
  0x743162,
  0x74315a,
  0x410176,
  0x42017a,
  0x42016e,
  0x1066,
  0x42117a,
  0x430146,
  0x44017a,
  0x630146,
  0x64017a,
  0x431146,
  0x44117a,
  0x631146
]

def labelsBlock13 : Array Nat := #[
  0x64117a,
  0x432146,
  0x44217a,
  0x632146,
  0x64217a,
  0x432176,
  0x64317a,
  0x44216e,
  0x54316e,
  0x2bcc,
  0x1c10,
  0x1b20,
  0x431052,
  0x3904,
  0x3aa8,
  0x10c6
]

def labelsBlock14 : Array Nat := #[
  0x410146,
  0x7320aa,
  0x420146,
  0x420176,
  0x743166,
  0x421146,
  0x421176,
  0x11083213e,
  0x442176,
  0x543176,
  0x2b34,
  0x1738,
  0x172c,
  0x10e2,
  0x3758,
  0x192c
]

def labelsBlock15 : Array Nat := #[
  0x1934,
  0x1116,
  0x110a,
  0x11083216e,
  0x44317a,
  0x2d00,
  0x2e20,
  0x1d14,
  0x1056,
  0x105a,
  0x1e48,
  0x1a4c,
  0x1082,
  0x108a,
  0x2b4c,
  0x2b9c
]

def labelsBlock16 : Array Nat := #[
  0x2f2c,
  0x2f3c,
  0x110e,
  0x1112,
  0x10de,
  0x10fe,
  0x1102,
  0x1106,
  0x111e,
  0x2e30,
  0x37d8,
  0x43017a,
  0x1e38,
  0x3a28,
  0x43117a,
  0x43217a
]

def labelsBlock17 : Array Nat := #[
  0x110832176,
  0x1006,
  0x1708,
  0x2e00,
  0x178c,
  0x10da,
  0x10ee,
  0x3718,
  0x10d2,
  0x10b2,
  0x103a,
  0x85,
  0x2da0,
  0x2ea0,
  0x7320be,
  0x113a
]

def labelsBlock18 : Array Nat := #[
  0x734126,
  0x1a10,
  0x1910,
  0x1730,
  0x1724,
  0x2b14,
  0x100e,
  0x1b48,
  0x1c54,
  0x1d50,
  0x1c58,
  0x1e50,
  0x104e,
  0x104a,
  0x2ed8,
  0x107a
]

def labelsBlock19 : Array Nat := #[
  0x2dd4,
  0x1076,
  0x1086,
  0x1032,
  0x108e,
  0x4200da,
  0x55,
  0x4210ea,
  0x5d,
  0x63102e,
  0x10ea,
  0x107e,
  0x2f9c,
  0x1d24,
  0x1b24,
  0x2b84
]

def labelsBlock20 : Array Nat := #[
  0x2d84,
  0x8d,
  0x10b6,
  0x10d6,
  0x10fa,
  0x10ce,
  0x10c2,
  0x1042,
  0xe5,
  0xe9,
  0xed,
  0xf5,
  0xf9,
  0xfd,
  0x105,
  0x111a
]

def labelsBlock21 : Array Nat := #[
  0x1a2c,
  0x10d,
  0x115,
  0x116a,
  0x11d,
  0x125,
  0x135,
  0x145,
  0x39c4,
  0x1002,
  0x2b80,
  0x1720,
  0x1b00,
  0x3900,
  0x3934,
  0x11
]

def labelsBlock22 : Array Nat := #[
  0x15,
  0x19,
  0x1d,
  0x21,
  0x25,
  0x29,
  0x2d,
  0x31,
  0x35,
  0x39,
  0x3d,
  0x1096,
  0x109a,
  0x10a6,
  0x102a,
  0x4d
]

def labelsBlock23 : Array Nat := #[
  0x3750,
  0x3c50,
  0x1c2c,
  0x10c430052,
  0x1ca0,
  0x3c20,
  0x1c3c,
  0x430052,
  0x1cb0,
  0x370c,
  0x10c831052,
  0x4310f6,
  0x432052,
  0x51,
  0x59,
  0x61
]

def labelsBlock24 : Array Nat := #[
  0x65,
  0x102e,
  0x190c,
  0x1b04,
  0x1d04,
  0x1ba4,
  0x1da4,
  0x95,
  0x732036,
  0x9d,
  0x71,
  0x75,
  0x79,
  0x7d,
  0x81,
  0x89
]

def labelsBlock25 : Array Nat := #[
  0x91,
  0x99,
  0xa1,
  0xb1,
  0xb5,
  0xb9,
  0xbd,
  0xc1,
  0xc5,
  0xc9,
  0xcd,
  0xd1,
  0xd5,
  0xd9,
  0xdd,
  0x41014e
]

def labelsBlock26 : Array Nat := #[
  0x42014e,
  0x43014e,
  0x430126,
  0x42114e,
  0x43114e,
  0x431126,
  0x43214e,
  0x432126,
  0x1172,
  0x1798,
  0x1794,
  0x1984,
  0x159,
  0x15d,
  0x73414e,
  0x165
]

def labelsBlock27 : Array Nat := #[
  0xf1,
  0x101,
  0x109,
  0x111,
  0x119,
  0x121,
  0x129,
  0x12d,
  0x131,
  0x139,
  0x13d,
  0x141,
  0x149,
  0x14d,
  0x151,
  0x155
]

def labelsBlock28 : Array Nat := #[
  0x161,
  0x169,
  0x1,
  0x5,
  0x9,
  0x1012,
  0x2b30,
  0x2b38,
  0x100a,
  0x1016,
  0xd,
  0x101a,
  0x101e,
  0x41,
  0x2e80,
  0x2d80
]

def labelsBlock29 : Array Nat := #[
  0x2b88,
  0x1728,
  0x45,
  0x2b10,
  0x2b18,
  0x49,
  0x69,
  0x3700,
  0x3708,
  0x3710,
  0x6d,
  0xa5,
  0x3c00,
  0x3a00,
  0xa9,
  0xad
]

def labelsBlock30 : Array Nat := #[
  0xe1,
  0x16d
]

def labelsGet (i : Nat) : Nat :=
  if i < 240 then
    if i < 112 then
      if i < 48 then
        if i < 16 then
          labelsBlock0.getD (i-0) 3
        else
          if i < 32 then
            labelsBlock1.getD (i-16) 3
          else
            labelsBlock2.getD (i-32) 3
      else
        if i < 80 then
          if i < 64 then
            labelsBlock3.getD (i-48) 3
          else
            labelsBlock4.getD (i-64) 3
        else
          if i < 96 then
            labelsBlock5.getD (i-80) 3
          else
            labelsBlock6.getD (i-96) 3
    else
      if i < 176 then
        if i < 144 then
          if i < 128 then
            labelsBlock7.getD (i-112) 3
          else
            labelsBlock8.getD (i-128) 3
        else
          if i < 160 then
            labelsBlock9.getD (i-144) 3
          else
            labelsBlock10.getD (i-160) 3
      else
        if i < 208 then
          if i < 192 then
            labelsBlock11.getD (i-176) 3
          else
            labelsBlock12.getD (i-192) 3
        else
          if i < 224 then
            labelsBlock13.getD (i-208) 3
          else
            labelsBlock14.getD (i-224) 3
  else
    if i < 368 then
      if i < 304 then
        if i < 272 then
          if i < 256 then
            labelsBlock15.getD (i-240) 3
          else
            labelsBlock16.getD (i-256) 3
        else
          if i < 288 then
            labelsBlock17.getD (i-272) 3
          else
            labelsBlock18.getD (i-288) 3
      else
        if i < 336 then
          if i < 320 then
            labelsBlock19.getD (i-304) 3
          else
            labelsBlock20.getD (i-320) 3
        else
          if i < 352 then
            labelsBlock21.getD (i-336) 3
          else
            labelsBlock22.getD (i-352) 3
    else
      if i < 432 then
        if i < 400 then
          if i < 384 then
            labelsBlock23.getD (i-368) 3
          else
            labelsBlock24.getD (i-384) 3
        else
          if i < 416 then
            labelsBlock25.getD (i-400) 3
          else
            labelsBlock26.getD (i-416) 3
      else
        if i < 464 then
          if i < 448 then
            labelsBlock27.getD (i-432) 3
          else
            labelsBlock28.getD (i-448) 3
        else
          if i < 480 then
            labelsBlock29.getD (i-464) 3
          else
            labelsBlock30.getD (i-480) 3

def decodeHints (enc i : Nat) := labelsGet ((enc >>> (i * 9)) % 512)

def localHints (stride dict enc i : Nat) : Nat :=
  let q := (enc >>> (stride*i)) % (2^stride)
  labelsGet ((dict >>> (9*q)) % 512)

def viewsBlock0 : Array View := #[
  ⟨0x8080000808000,⟨15,by decide⟩,0x80000800000,[ew84,ew85],2,decodeHints 0xe11189e46⟩,
  ⟨0xff00000,⟨20,by decide⟩,0xe800000,[ew3,ew5,ew7],3,decodeHints 0xe181408131ba2d1813⟩,
  ⟨0xa0a0000a0a000,⟨13,by decide⟩,0x80000800000,[ew86,ew87,ew88],3,decodeHints 0xac8108cac27ba88cac⟩,
  ⟨0x808080880808080,⟨7,by decide⟩,0x800080080800000,[ew133,ew134,ew135],2,decodeHints 0xac850020127aac0201⟩,
  ⟨0x99990000,⟨16,by decide⟩,0x98800000,[ew20,ew22,ew24],3,decodeHints 0x0⟩,
  ⟨0xaaaa0000000000,⟨41,by decide⟩,0x80a80000000000,[ew103,ew109,ew113],3,decodeHints 0x0⟩,
  ⟨0xaa00aa000000000,⟨37,by decide⟩,0xa80080000000000,[ew138,ew142,ew152],3,decodeHints 0x0⟩,
  ⟨0x8080808008080808,⟨3,by decide⟩,0x8080800008000000,[ew224,ew225,ew228],3,decodeHints 0x0⟩,
  ⟨0xff00ff0,⟨4,by decide⟩,0xe800000,[ew4,ew6,ew8,ew9],4,decodeHints 0x8881408131ba2d18130089842515748a4251⟩,
  ⟨0xffff0000,⟨16,by decide⟩,0xfe800000,[ew30,ew35,ew38,ew42],4,decodeHints 0xe201408130189038430107c401f0c87c4043⟩,
  ⟨0xff00ff00000,⟨20,by decide⟩,0x8000e800000,[ew46,ew48,ew49,ew51],4,localHints 3 0x888d00a041ba2d1813 0xf60688d60688⟩,
  ⟨0x999999990000,⟨16,by decide⟩,0x880098800000,[ew60,ew61,ew62,ew63],4,localHints 3 0xe28d02603142843243 0xf60688d60688⟩,
  ⟨0xf0f0000f0f000,⟨12,by decide⟩,0x80000800000,[ew89,ew90,ew91,ew92],4,decodeHints 0xe40140813233ad592327f1dd5c6233ad5923⟩,
  ⟨0xaaaa0000aaaa00,⟨9,by decide⟩,0x80a80000800000,[ew106,ew112,ew115,ew118],4,decodeHints 0xe4810061c232b1d924000884622000884724⟩,
  ⟨0xa0a0a0aa0a0a0a0,⟨5,by decide⟩,0xa000800a0800000,[ew137,ew147,ew149,ew150],4,decodeHints 0xe5010740400885ee2127ba9572500885ee21⟩,
  ⟨0xaa00aa00aa00aa0,⟨5,by decide⟩,0xa8008000a800000,[ew141,ew146,ew154,ew155],4,decodeHints 0xe58106e04008855c21000895725008855c21⟩
]

def viewsBlock1 : Array View := #[
  ⟨0xff000000ff00000,⟨20,by decide⟩,0xe8000000e800000,[ew154,ew163,ew168,ew173],3,localHints 3 0x4440a041ba2d1813 0xd60688d60688⟩,
  ⟨0x8888888888888888,⟨3,by decide⟩,0x8880880088800000,[ew232,ew244,ew248,ew250],3,localHints 3 0xe60a0060007004ea1a 0xf7540891b408⟩,
  ⟨0x33cc33cc,⟨2,by decide⟩,0x32800000,[ew10,ew11,ew12,ew13],4,decodeHints 0x0⟩,
  ⟨0x55aa55aa,⟨1,by decide⟩,0x54800000,[ew14,ew15,ew16,ew17],4,decodeHints 0x0⟩,
  ⟨0x99999999,⟨0,by decide⟩,0x98800000,[ew21,ew23,ew25,ew26],4,decodeHints 0x0⟩,
  ⟨0xa5a5a5a5,⟨0,by decide⟩,0xa4800000,[ew19,ew27,ew28,ew29],4,decodeHints 0x0⟩,
  ⟨0xc3c3c3c3,⟨0,by decide⟩,0xc2800000,[ew18,ew32,ew33,ew34],4,decodeHints 0x0⟩,
  ⟨0xf0f0f0f0000,⟨16,by decide⟩,0x8000e000000,[ew45,ew47,ew49,ew50],4,decodeHints 0x0⟩,
  ⟨0x333333330000,⟨16,by decide⟩,0x200032000000,[ew52,ew53,ew54,ew55],4,decodeHints 0x0⟩,
  ⟨0x555555550000,⟨16,by decide⟩,0x400054000000,[ew56,ew57,ew58,ew59],4,decodeHints 0x0⟩,
  ⟨0xaaaaaaaa0000,⟨17,by decide⟩,0xa800aa800000,[ew60,ew64,ew68,ew69],4,decodeHints 0x0⟩,
  ⟨0xff00000000ff,⟨0,by decide⟩,0xe80000000000,[ew66,ew72,ew76,ew80],4,decodeHints 0x0⟩,
  ⟨0xff000000ff00,⟨8,by decide⟩,0xe80000000000,[ew67,ew73,ew77,ew80],4,decodeHints 0x0⟩,
  ⟨0x33330000cccc00,⟨10,by decide⟩,0x200000800000,[ew93,ew94,ew95,ew96],4,decodeHints 0x0⟩,
  ⟨0x55550000aaaa00,⟨9,by decide⟩,0x400000800000,[ew97,ew98,ew99,ew100],4,decodeHints 0x0⟩,
  ⟨0xaa00aa55005500,⟨8,by decide⟩,0x80000054000000,[ew102,ew108,ew116,ew117],4,decodeHints 0x0⟩
]

def viewsBlock2 : Array View := #[
  ⟨0xaaaa0000555500,⟨8,by decide⟩,0x80a80000000000,[ew105,ew111,ew114,ew118],4,decodeHints 0x0⟩,
  ⟨0xcccc0000333300,⟨8,by decide⟩,0x80c80000000000,[ew104,ew121,ew123,ew125],4,decodeHints 0x0⟩,
  ⟨0xcccc0000cccc00,⟨10,by decide⟩,0x80c80000800000,[ew106,ew122,ew124,ew125],4,decodeHints 0x0⟩,
  ⟨0xf0f000000f0f00,⟨8,by decide⟩,0x80e00000000000,[ew110,ew120,ew127,ew129],4,decodeHints 0x0⟩,
  ⟨0xa0a0a0a05050505,⟨0,by decide⟩,0xa00080004000000,[ew136,ew145,ew148,ew150],4,decodeHints 0x0⟩,
  ⟨0xaa00aa005500550,⟨4,by decide⟩,0xa80080004000000,[ew140,ew145,ew153,ew155],4,decodeHints 0x0⟩,
  ⟨0xcc00cc003300330,⟨4,by decide⟩,0xc80080002000000,[ew139,ew159,ew162,ew164],4,decodeHints 0x0⟩,
  ⟨0xcc00cc00cc00cc0,⟨6,by decide⟩,0xc8008000c800000,[ew141,ew160,ew163,ew164],4,decodeHints 0x0⟩,
  ⟨0xf000f00000f000f,⟨0,by decide⟩,0xe00080000000000,[ew143,ew157,ew166,ew169],4,decodeHints 0x0⟩,
  ⟨0xf000f0000f000f0,⟨4,by decide⟩,0xe00080000800000,[ew144,ew158,ew167,ew169],4,decodeHints 0x0⟩,
  ⟨0xf000f000f000f00,⟨8,by decide⟩,0xe0008000e000000,[ew146,ew160,ew168,ew169],4,decodeHints 0x0⟩,
  ⟨0x2222222211111111,⟨0,by decide⟩,0x2200200010000000,[ew177,ew181,ew184,ew186],4,decodeHints 0x0⟩,
  ⟨0x2222222288888888,⟨3,by decide⟩,0x2200200088800000,[ew178,ew183,ew185,ew186],4,decodeHints 0x0⟩,
  ⟨0x2288228822882288,⟨3,by decide⟩,0x2280200022800000,[ew179,ew182,ew188,ew189],4,decodeHints 0x0⟩,
  ⟨0x3300330000330033,⟨0,by decide⟩,0x3200200000000000,[ew180,ew191,ew196,ew198],4,decodeHints 0x0⟩,
  ⟨0x3300330033003300,⟨8,by decide⟩,0x3200200032000000,[ew182,ew192,ew197,ew198],4,decodeHints 0x0⟩
]

def viewsBlock3 : Array View := #[
  ⟨0x33cc000033cc0000,⟨18,by decide⟩,0x3280000032800000,[ew188,ew194,ew197,ew202],3,decodeHints 0x0⟩,
  ⟨0x5500550000550055,⟨0,by decide⟩,0x5400400000000000,[ew205,ew210,ew215,ew217],4,decodeHints 0x0⟩,
  ⟨0x5500550055005500,⟨8,by decide⟩,0x5400400054000000,[ew206,ew211,ew216,ew217],4,decodeHints 0x0⟩,
  ⟨0x55aa000055aa0000,⟨17,by decide⟩,0x5480000054800000,[ew208,ew213,ew216,ew221],3,decodeHints 0x0⟩,
  ⟨0x8282828282828282,⟨1,by decide⟩,0x8280800082800000,[ew232,ew233,ew234,ew235],4,decodeHints 0x0⟩,
  ⟨0x8888222288882222,⟨1,by decide⟩,0x8880200088800000,[ew227,ew239,ew248,ew249],4,decodeHints 0x0⟩,
  ⟨0x8888888811111111,⟨0,by decide⟩,0x8880880010000000,[ew230,ew241,ew245,ew250],4,decodeHints 0x0⟩,
  ⟨0x8888888822222222,⟨1,by decide⟩,0x8880880022000000,[ew231,ew242,ew246,ew250],4,decodeHints 0x0⟩,
  ⟨0x9090090990900909,⟨0,by decide⟩,0x9080080090800000,[ew226,ew254,ew257,ew258],4,decodeHints 0x0⟩,
  ⟨0x9090909090909090,⟨4,by decide⟩,0x9080800090800000,[ew232,ew256,ew257,ew259],4,decodeHints 0x0⟩,
  ⟨0x9900990000990099,⟨0,by decide⟩,0x9800880000800000,[ew240,ew255,ew261,ew263],4,decodeHints 0x0⟩,
  ⟨0x9900990099009900,⟨8,by decide⟩,0x9800880098000000,[ew244,ew256,ew262,ew263],3,decodeHints 0x0⟩,
  ⟨0x9999000099990000,⟨16,by decide⟩,0x9880000098800000,[ew248,ew257,ew262,ew265],3,decodeHints 0x0⟩,
  ⟨0x9999999900000000,⟨32,by decide⟩,0x9880880000000000,[ew250,ew259,ew263,ew265],4,decodeHints 0x0⟩,
  ⟨0xa0a00a0aa0a00a0a,⟨1,by decide⟩,0xa0800800a0800000,[ew226,ew268,ew275,ew276],4,decodeHints 0x0⟩,
  ⟨0xa0a0a0a00a0a0a0a,⟨1,by decide⟩,0xa080a0000a000000,[ew229,ew270,ew273,ew277],4,decodeHints 0x0⟩
]

def viewsBlock4 : Array View := #[
  ⟨0xa0a0a0a0a0a0a0a0,⟨5,by decide⟩,0xa080a000a0800000,[ew232,ew272,ew275,ew277],3,decodeHints 0x0⟩,
  ⟨0xa5a50000a5a50000,⟨16,by decide⟩,0xa4800000a4800000,[ew237,ew275,ew281,ew283],3,decodeHints 0x0⟩,
  ⟨0xaa00aa0000aa00aa,⟨1,by decide⟩,0xaa00a80000800000,[ew240,ew269,ew286,ew289],4,decodeHints 0x0⟩,
  ⟨0xaa00aa0055005500,⟨8,by decide⟩,0xaa00a80054000000,[ew243,ew271,ew287,ew289],4,decodeHints 0x0⟩,
  ⟨0xaaaa000055550000,⟨16,by decide⟩,0xaa80000054000000,[ew247,ew274,ew287,ew293],4,decodeHints 0x0⟩,
  ⟨0xaaaaaaaa00000000,⟨33,by decide⟩,0xaa80a80000000000,[ew250,ew277,ew289,ew293],4,decodeHints 0x0⟩,
  ⟨0xc0c0c0c0c0c0c0c0,⟨6,by decide⟩,0xc080c000c0800000,[ew232,ew299,ew300,ew301],3,decodeHints 0x0⟩,
  ⟨0xc3c30000c3c30000,⟨16,by decide⟩,0xc2800000c2800000,[ew234,ew300,ew305,ew307],3,decodeHints 0x0⟩,
  ⟨0xffffffff,⟨0,by decide⟩,0xfe800000,[ew31,ew36,ew39,ew43,ew44],6,decodeHints 0xe681408130189038430107c401f0c87c40430089842510d44980760d9fd127f511fd1276⟩,
  ⟨0xffff0000ffff,⟨0,by decide⟩,0xe80000000000,[ew70,ew74,ew78,ew81,ew83],5,decodeHints 0x14844186f06c723a6f0a7427f5aa073f9d5a00094444011ac5ec400718ca48a303d6268a⟩,
  ⟨0xffff0000ffff00,⟨8,by decide⟩,0x80e80000800000,[ew119,ew126,ew130,ew131,ew132],6,decodeHints 0xe90140813018903843233ad592376746495b00094444011ac5ec4000094444011ac5ed5b⟩,
  ⟨0xf0f0f0f0f0f0f0f,⟨0,by decide⟩,0xe0008000e000000,[ew151,ew161,ew170,ew171,ew172],5,decodeHints 0x1781c10070107c401f030e078380d9fd127f0009444400718ca48a030e078380d9fd127f⟩,
  ⟨0xff00ff00ff00ff0,⟨4,by decide⟩,0xe8008000e800000,[ew156,ew165,ew170,ew174,ew175],6,decodeHints 0xea81408131ba2d18130089842515748a425100094444055f524bd30089842515748a4251⟩,
  ⟨0x9999999999999999,⟨0,by decide⟩,0x9880880098800000,[ew253,ew260,ew264,ew266,ew267],6,decodeHints 0xeb04c06431428432430094434763ad714476001000040072281c8a0094434763ad714476⟩,
  ⟨0xaaaaaaaa55555555,⟨0,by decide⟩,0xaa80a80054000000,[ew252,ew279,ew291,ew294,ew297],6,decodeHints 0xed0201208058803220080f0623c2ca25448912901624031a29ea8a8bf67b1d7aea254489⟩,
  ⟨0xaaaaaaaaaaaaaaaa,⟨1,by decide⟩,0xaa80a800aa800000,[ew253,ew280,ew292,ew295,ew297],6,decodeHints 0xed810061c01008041c0088434c00d86c36c000088462207148c0520088434c00d86c36c0⟩
]

def viewsBlock5 : Array View := #[
  ⟨0xff00ff0000ff00ff,⟨0,by decide⟩,0xfe00e80000800000,[ew290,ew310,ew318,ew327,ew330],6,decodeHints 0xef01408130189038430089842510d44980760718ca48a303d6268a6ed77ba8aee3d62676⟩,
  ⟨0xff00ff00ff00ff00,⟨8,by decide⟩,0xfe00e800fe000000,[ew292,ew312,ew320,ew328,ew330],6,localHints 4 0x77c1208038004a2211ac5ec40030c47838 0xebcbdbcb30102010a984765430102010⟩,
  ⟨0xffff0000ffff0000,⟨16,by decide⟩,0xfe800000fe800000,[ew295,ew314,ew322,ew328,ew333],5,localHints 4 0x3df001408130189038020c87c4043 0xca98765042123210ba98765042123210⟩,
  ⟨0xffffffff0000,⟨16,by decide⟩,0xe800fe800000,[ew71,ew75,ew79,ew82,ew83],6,decodeHints 0x0⟩,
  ⟨0x3333333333333333,⟨0,by decide⟩,0x3200200032000000,[ew187,ew193,ew199,ew200,ew201],5,decodeHints 0x0⟩,
  ⟨0x33cc33cc33cc33cc,⟨2,by decide⟩,0x3280200032800000,[ew190,ew195,ew199,ew203,ew204],6,decodeHints 0x0⟩,
  ⟨0x5555555555555555,⟨0,by decide⟩,0x5400400054000000,[ew207,ew212,ew218,ew219,ew220],5,decodeHints 0x0⟩,
  ⟨0x55aa55aa55aa55aa,⟨1,by decide⟩,0x5480400054800000,[ew209,ew214,ew218,ew222,ew223],6,decodeHints 0x0⟩,
  ⟨0xa5a5a5a5a5a5a5a5,⟨0,by decide⟩,0xa480a000a4800000,[ew238,ew280,ew282,ew284,ew285],6,decodeHints 0x0⟩,
  ⟨0xc3c3c3c3c3c3c3c3,⟨0,by decide⟩,0xc280c000c2800000,[ew236,ew304,ew306,ew308,ew309],6,decodeHints 0x0⟩,
  ⟨0xcccccccc33333333,⟨0,by decide⟩,0xcc80c80032000000,[ew251,ew303,ew311,ew313,ew315],6,decodeHints 0x0⟩,
  ⟨0xcccccccccccccccc,⟨2,by decide⟩,0xcc80c800cc800000,[ew253,ew304,ew312,ew314,ew315],6,decodeHints 0x0⟩,
  ⟨0xf0f0f0f00f0f0f0f,⟨0,by decide⟩,0xf080e0000e000000,[ew278,ew302,ew319,ew321,ew323],6,decodeHints 0x0⟩,
  ⟨0xf0f0f0f0f0f0f0f0,⟨4,by decide⟩,0xf080e000f0800000,[ew280,ew304,ew320,ew322,ew323],6,decodeHints 0x0⟩,
  ⟨0xffffffff00000000,⟨32,by decide⟩,0xfe80e80000000000,[ew297,ew315,ew323,ew330,ew333],6,decodeHints 0x0⟩,
  ⟨0xffffffffffffffff,⟨0,by decide⟩,0xfe80e800fe800000,[ew298,ew316,ew324,ew332,ew334,ew335],9,decodeHints 0xf081408130189038430107c401f0c87c40430089842510d44980760d9fd127f511fd127600094444011ac5ec400718ca48a303d6268a0089842510d44980760d9fd127f511fd1276⟩
]

def viewsGet (i : Nat) : Option View :=
  if i < 48 then
    if i < 16 then
      viewsBlock0[(i-0)]?
    else
      if i < 32 then
        viewsBlock1[(i-16)]?
      else
        viewsBlock2[(i-32)]?
  else
    if i < 64 then
      viewsBlock3[(i-48)]?
    else
      if i < 80 then
        viewsBlock4[(i-64)]?
      else
        viewsBlock5[(i-80)]?

def nodesBlock0 : Array Node := #[
  ⟨0,2,[ew84,ew85],localHints 2 0x6ca809e46 0x235e84⟩,
  ⟨1,3,[ew3,ew5,ew7],localHints 4 0x8c458dd0013028101007 0x258168155262367057066353024314322010⟩,
  ⟨9,4,[ew30,ew35,ew38,ew42],localHints 4 0x641e200e07c040b1200c1213028101007 0x6de59e5dd69928c19c18829916b25b26615139a08a099388067357366050024314322010⟩,
  ⟨14,4,[ew137,ew147,ew149,ew150],localHints 4 0xaf13628ab503ddd44f930840293060507404 0x5b5e8febd58518c2bc2881b124a15a144255089379388070356046055344020311322010⟩,
  ⟨72,5,[ew21,ew31,ew36,ew39,ew43,ew44],localHints 5 0x1b0d0641e3c100e0201f0581c1047008185002018240805 0x52863ce6734a5121e0733deb20c4349dc76b18458c4352928398e6290a41886208400⟩,
  ⟨72,5,[ew31,ew36,ew37,ew39,ew43,ew44],localHints 5 0x361a0c8a81e21031b43808130042002058900609038100a47 0x56af5528a7ce7142a4a92228894852420a7b907435a52304b5a9283a0e63148308820⟩,
  ⟨72,5,[ew27,ew31,ew36,ew39,ew43,ew44],localHints 5 0x1b188641e21100e0201f05825f007008187402018101005 0x528639e6734a512420733deb2044209dc76b1845a14910448398e6290a418c4110400⟩,
  ⟨72,5,[ew31,ew36,ew39,ew40,ew43,ew44],localHints 5 0x1b0d1b81e0910818401c1300420020581c06057c04c0808 0x528e5292a4a0e83ce6a74911440af7a9cd69d000840c6140b5a9283a0e62148310820⟩,
  ⟨72,5,[ew0,ew31,ew36,ew39,ew43,ew44],localHints 5 0x2c86832211003c38380807c1607008180403048101005 0x4e663ca473462e4c20733de9735a409d875a90920c8810448398e62948320c4110400⟩,
  ⟨72,5,[ew16,ew31,ew36,ew39,ew43,ew44],decodeHints 0x6c3606008683401031b80437010844201031b40473010703803040984c010807c04051209006090984c08080800420010580812030480c1004040100e05⟩,
  ⟨72,5,[ew31,ew32,ew36,ew39,ew43,ew44],localHints 5 0x1b188641e3c1002012f903190060413004201f0102c0a07 0x528b31a665ca5119a065bde21b9ac32ccb50d434a50839cc521062004200042000420⟩,
  ⟨72,5,[ew31,ew36,ew39,ew41,ew43,ew44],localHints 5 0x1b0d3e81e091081810f913004201f0102c0a240184c0807 0x528e529ca718e63ce6a748f13c06f7a9c6398ed08c2c5ad49420e6014a02106010820⟩,
  ⟨72,5,[ew1,ew31,ew36,ew39,ew43,ew44],localHints 5 0xd868323c100204c100f83c48010302c0403048100a07 0x4e6744a483c62a2a2083bdc520c8e6b50c5acaa4a4800042041d073148320c4208020⟩,
  ⟨72,5,[ew12,ew31,ew36,ew39,ew43,ew44],decodeHints 0x164b206008683401033e816800588442010308016040e07006091309802109382df60b1209006070984c0807030040c010100812030480c1004038140e05⟩,
  ⟨72,5,[ew2,ew31,ew36,ew39,ew43,ew44],localHints 5 0xd8c43209108804c100f82c26010303c0403020200a07 0x4e67422483c6057bd077394510c626b50c5acaa004204a46041d07314841886208020⟩,
  ⟨72,5,[ew8,ew31,ew36,ew39,ew43,ew44],decodeHints 0x369b406008683401030641e031088402069583e540f0e07006081309802109483e500f1209006070984c0807030040c01010081203040101004038140e05⟩
]

def nodesBlock1 : Array Node := #[
  ⟨72,6,[ew31,ew36,ew39,ew43,ew44],localHints 6 0x1b0d5aad219079384206b459c412d7c872cd65130047a10b258c3e029602df024b100ec2092384ec0050257c1007 0x5558285505a85508205555965555a754a82754a59655582098a8e49484248888e388a4105555a15438215435965558207c339d78141d70138e7034106c129a6c321a64328a6012015555975445175445965555144c44114803913c04103c438e34028c34420c2c428a2402001c00c61c40461440c3080040⟩,
  ⟨74,6,[ew119,ew126,ew130,ew131,ew132],localHints 6 0x3fa682399bb1b332114c414ac98071fa0d063f04a009785dd64614cb84803190442605022507633 0x2cc2cc2dd4102dd2e22cc4108486608544207d46597c84102d431e2c875e2c830c2d475470341b71365b6934106836592d33182c35d82c330c2d35d35532165435165432085535134844114863913c64103c438e2c630d2c428d2c430c2c62860862090841c90842080861c60800c50840450840c3080040⟩,
  ⟨76,6,[ew156,ew165,ew170,ew174,ew175],localHints 6 0x5a215b8696d55ab85effb6088420c032315b6b128009c2600844208b1ba002605021d01007 0x34b34b35f3a035f79d34b38b34739b35871b35838e3473476584da6472da6474d36582cb3433963545d635438e3433434542d54434d54432cb4544d34431924411d24411864431c334438f34a40f34a38e34434408a2cc08424c0842cb08a2490841c80801880801c70841840800c50840450840c3080040⟩,
  ⟨77,4,[ew176,ew253,ew264,ew266,ew267],decodeHints 0x96868010703800283a9d47c0120100001328944022a50a8450130180140000d068023e0c8641e032190c0650⟩,
  ⟨77,5,[ew244,ew253,ew260,ew264,ew266,ew267],decodeHints 0x4b43400802e20007b69b43e00c00004f0006834011f064320f01802e00009944a2011504c1e952190c06090045400471f0047c01140a2de034680ca013⟩,
  ⟨77,4,[ew248,ew253,ew257,ew264,ew267],decodeHints 0x1c0e000a06375ba0c544a21880c8040005cc500f1403c0631b90c47c009a8f8ea751f03c341a018c5b6db⟩,
  ⟨77,5,[ew248,ew253,ew260,ew264,ew266,ew267],decodeHints 0xa80178000381c0014369b42a0a400004f000c4622a9b064320f019008000bb9bc55761403c500f018240609238022a0000804500f1403c0609018242613⟩,
  ⟨77,4,[ew253,ew257,ew262,ew264,ew267],decodeHints 0x1c0e005e87c009b8f8ea750d5e6281a0d025d81a0d0c4121a20100001309940a0136db6c7c133b1d83450⟩,
  ⟨77,5,[ew253,ew257,ew264,ew266,ew267],localHints 5 0x1399b838eb380a1f6f6a076868333520001b8af6d8fa6c6f508a01e430980c1250 0x14d535ce6f38a728ced5f7abb9c669aeac999932957c5c4d159ceb568273a73909521162134425288c21b9e883d0e70da34296362c6a52128198e029c0630ca3008830906210020⟩,
  ⟨77,5,[ew253,ew260,ew262,ew264,ew266,ew267],decodeHints 0x4b434008381c00be05002462380274001f0045028800009e000d068033801824120301824120320100001328944026f09940a01309940a0132190c0650⟩,
  ⟨77,6,[ew253,ew260,ew264,ew266,ew267],localHints 6 0x2d10b02349d038eb800a400fb0127bb4357f1f0662a400011d5e5100df8de2a8b2852a28be83c861301a341250 0x48f48f4a64e74a696448f4cf4884e249f8e249f4d34884882df5e14483e12c85d781f3cf48371e49d4d349d71b4834d369a3d96835d90833cf0985d70831960812160811860832034844d448d55448d4d348448424d3d04443102443cf38d30c24420a2c018a2402081c41840800c50840450840c3080040⟩,
  ⟨78,6,[ew252,ew279,ew291,ew294,ew297],localHints 5 0x22f0331ceddd022cbf08414588c41a19200952c3c08030542005a041eb03e9941208 0xe2f3de55dde5739e2dcbc1ddbc533bd51ced1f27c5177c1eb7b1d6bb52b4105b3145d3145ad105ce1453210572105291456b10cb0104f0104a510ce7301cf329af329ce301ad3296c3012c3016b32929310e8300a8300e7310a510060110211106310020⟩,
  ⟨79,5,[ew232,ew253,ew280,ew292,ew295,ew297],decodeHints 0x4b434008381c000106c36060088c460a000040c01031b80437010884400050040c01031b40473010301b188080202000081802069e00a78020180c0804⟩,
  ⟨79,5,[ew101,ew253,ew280,ew292,ew295,ew297],decodeHints 0x4b434008c060000106c36060088c460a000683401031b80437010884400050040c01031b4180201834060c8c802080000818020614008060d018340804⟩,
  ⟨79,5,[ew248,ew253,ew280,ew292,ew295,ew297],decodeHints 0x18ee2d030381c000106c36060a08c460a004f40cf0031b80437010884400050300cef14008500201834060c4b802080000804500214008060d018340804⟩,
  ⟨79,5,[ew107,ew253,ew280,ew292,ew295,ew297],decodeHints 0x4b434008381c000106c36060088c460a000040c01031b81a0211088000a10884020636808e60206010080c8d0020a000081802061d008060302030080c⟩
]

def nodesBlock2 : Array Node := #[
  ⟨79,5,[ew253,ew275,ew280,ew292,ew295,ew297],decodeHints 0x18ee2d030381c000106c36060a08c460a000340cf01d00874024b8020a000080474021d008060311088000a9f019de0636808e60206010080c06010080c⟩,
  ⟨79,4,[ew65,ew253,ew280,ew292,ew295],decodeHints 0xd86c0c010d0680206370086e0210884020636808e6020e070060c168041c0e1188c140011088000a⟩,
  ⟨79,5,[ew67,ew253,ew280,ew292,ew295,ew297],decodeHints 0x4b4340080164000106c04011188c14000d068020d370086e0211088000a10884020c36808e6020e070060c0025c011b0300428020680c1a03060101804⟩,
  ⟨79,4,[ew115,ew253,ew280,ew289,ew295],decodeHints 0x6e86c5a1bc206d5c1b30180600ec186f041b291481c300e070060c0086d640e010dcdc02011ccda02⟩,
  ⟨79,5,[ew115,ew253,ew280,ew292,ew295,ew297],decodeHints 0x18ee2d030381c00a086c0c141188c14009e819e00601d00b60311088000a9f019de06024fc28040e070060c4b801e20000804040201834060d02030080c⟩,
  ⟨79,4,[ew253,ew280,ew292,ew295,ew296],decodeHints 0x2010703800971680804fe1188c1400c300c062d370086e0211088000ac2810082d36808e6020e070060c⟩,
  ⟨79,5,[ew253,ew280,ew289,ew292,ew295],localHints 5 0x2821bc41de3787268b5e40e0d1b87437118840206368a0e60211000141c0200c1a0c 0x3ace21bc4319b6b4d7d65adc5ec66b6b5a19140b66264c4d6858c146414203180908115e133c25288c6035c36386d6818c1a9604200a48d08198e029c0630ca5008830906210020⟩,
  ⟨79,4,[ew253,ew280,ew288,ew292,ew295],localHints 4 0x1068c023108040c52070c0000a11070060c 0x7a979a9af7eea9dd6745ccbba9887654332210⟩,
  ⟨79,5,[ew69,ew253,ew280,ew292,ew295],localHints 5 0x6c346e1d0dc4206368a0e61c4b8d0038907052360211834062206000080a 0x154d21ba4528a6b4cdc96992b5a6a50b7c190835ec54206da86950b5a3a503298d081ca2142065804d0094a330def709ad6296242c4a12508118e029c06008a200c820904310020⟩,
  ⟨79,6,[ew253,ew280,ew292,ew295,ew297],localHints 6 0x3245a210d12ef2073c72390c786d28148288e35440d63a0c6ec68e86e748208801190550c4201c6018db8b141ce84028c0712a0401e281a0c 0xa90c50aaf570b6fb6eb50550b0856bb24b2baa4555a88a48a243a69c842694838e9644108c34e28c15628414d384355580141f80339f74341078138e74369c6c12086016996032085c45565c04d65005555044d34804114843911444103c038e1442cd3002082402ca2442081c00c61c40461440c3080040⟩,
  ⟨80,6,[ew290,ew310,ew318,ew327,ew330],localHints 5 0x1bab230068a43010934380d0618c1cdf2e09802446f0900661190442605022087633 0x6379d65a3d65b9c636314271b4523b4531842631651ba626da625ad652d410e3914f1914e3110f1864db760ed760dad64ed344d3540e9540d2944e9381232819f281a31811ef619ae6116e611ad619664192a410ea41129418e610065110251106310020⟩,
  ⟨81,6,[ew292,ew312,ew320,ew328,ew330],localHints 5 0x3b9345a23188a8440a1e0ec6425002382e38030a42033068bc1211061201007 0x52d4b569fb5695952deb3169831df831e94315ef51ed751577516d651d6b105f510e9510def1069450d33505735052950d6b30621348a534a31304a1701f0711b0711ef701ad5116c5012c5016b51129300e0320a5320e7300a010060110211106310020⟩,
  ⟨82,4,[ew248,ew295,ew314,ew322,ew328],localHints 4 0x320f1007c1607042bc5002018240805 0xddc4bb943237aa493238876545432321100⟩,
  ⟨82,4,[ew295,ew314,ew317,ew322,ew328],localHints 4 0x320f368701002058900609038100aaf 0xddc88c8c5454b878aa54928787665431210⟩,
  ⟨82,4,[ew275,ew295,ew314,ew322,ew328],localHints 4 0x320f1007c16098381c7402018101005 0xddc4bb941221aa496872126545433212100⟩,
  ⟨82,4,[ew295,ew314,ew322,ew325,ew328],localHints 4 0xdc0f0488038020581c06058384c0808 0x8787d8c8b5aa78011099508787645432210⟩
]

def nodesBlock3 : Array Node := #[
  ⟨82,4,[ew115,ew295,ew314,ew322,ew328],localHints 4 0x191003c381f0581c0403048101005 0xcca7bb7a994186743462126554343212100⟩,
  ⟨82,4,[ew216,ew295,ew314,ew322,ew328],localHints 4 0x370dcda730e07c4813058081203040100e05 0xf6e6d6c6bb43a6099458823765454323210⟩,
  ⟨82,4,[ew295,ew300,ew314,ew322,ew328],localHints 4 0x320f1002013083200c081f0102c0a07 0xddc3bb23a98737366554432011001100110⟩,
  ⟨82,4,[ew295,ew314,ew322,ew326,ew328],localHints 4 0x1f40f04822101f0102c0a240184c0807 0x6767d7c7b36767a13198876055044302210⟩,
  ⟨82,4,[ew124,ew295,ew314,ew322,ew328],localHints 4 0x19100203e0f1202c0403048100a07 0xcc85ba5434a995877400110654343221010⟩,
  ⟨82,4,[ew197,ew295,ew314,ew322,ew328],localHints 4 0x7d200401c93bec1624098081203040100e05 0xf9e9d92cc45b9a988417721665454321010⟩,
  ⟨82,4,[ew128,ew295,ew314,ew322,ew328],localHints 4 0x19048803e0b0983c0403020200a07 0xcb5aa852332995801107730654432321010⟩,
  ⟨82,4,[ew168,ew295,ew314,ew322,ew328],localHints 4 0xccae541c94ca01e24098081203040100e05 0xf94e9d9cc43b9a988417721665432321010⟩,
  ⟨82,5,[ew295,ew314,ew322,ew328],decodeHints 0xcf00c1e19ce8240419a38241e0fa380c0402ce0101620cd8200420a3020160ba3010040284020061c84010121ccd0100603cc8201208cc014041fcb81c161fa281c0402a2814160b8381c0624838141224cb0140603ca81c12075781c0813578141013ca0140804c981c1007⟩,
  ⟨95,7,[ew253,ew298,ew316,ew322,ew324,ew332,ew334,ew335],decodeHints 0xc77168181c0e00008361b030504623050001a067803c040f0117400c100004020f0103c0403018021200050f0781003080400b010223a32040206a18040012c000b8e070060807c3e020581e380d0381c92150381c108300028000a1f0187c06140085002158343a0d0b0d52a16020100a05⟩,
  ⟨95,7,[ew78,ew253,ew298,ew316,ew324,ew332,ew334,ew335],decodeHints 0xc77168181c0e00008361b03050140005000340303064320f010021200050f0781003080400b0100c1203040012c000b8e070060807c3e020580c12030381c108400028000a1f0187c06140085002018240609020100a0505000140000804b6022d8081a031d82076081981c66071a8ad2a2b⟩,
  ⟨95,7,[ew83,ew253,ew298,ew316,ew324,ew332,ew334],localHints 6 0xd868320f1e14c40380807d860b252d04e16031145086611990a09022cc0b9f1a0063c0e0a008460d01c2476084b0cc0e172e800240a 0xf7ef392bce7df3d248c4ae2dfb8b49231f7cbb2d60eb58b2c2ce38949221fac849225f7ea92920ea4892488e3882cb2586092cb218206492167a054921a79e33a616498538e9649052cb1986062cb1581455855882238e38124a27df8524a07df45d75e38e79d75c38e64b2db61868b2d96185965c12175965411555034c249244f40239008f08338e08c3402cd00c0022c20092822020890802001061c2142086084144003002042083080040⟩,
  ⟨95,8,[ew253,ew298,ew316,ew324,ew332,ew334,ew335],localHints 6 0x528b442478d1040e0d85047490d5201a1907c2478201d8612c171c0403e49058cc2b1f6092c000a138042c06243803c281f808e0c40e80c6a2b0482008672e8480e05 0xd6e966f86796f8df60d66560ce6746f2d744b26590ce4ce4b25334ce5b348e5144f25960ca6316ed67132d6180ca65932d5afc0a52f30a596bad51430aaec4873ac307aeb4ca38e0c66599a762a9a76590c66189a75969865299865969a75149a67e89863a89867df98938e98628a9a71c79a728a9861c60c165975e92575e6590c192475e5967418a374159675e8a275d3a17417e174138e7607df74128a75e1c775e28a7411c110110110418675d75d0c26596dc6186da6590c261825559624951425759625551425341049138e49141024f38e24828a30d1c730b28a2481c71041050c21851041000c2040⟩,
  ⟨95,7,[ew280,ew298,ew314,ew316,ew324,ew332,ew334,ew335],decodeHints 0xc77168181c0e00008361b030516ab50500062311501832190780844220002818067782c040b0147412320497800c500004020b0102c042b048741204020944a000b8e070061507c3e020581c1287039bc1807039242a070500014004981926061d00874020180c6a0c0c0302c2b830580a05⟩,
  ⟨95,7,[ew74,ew280,ew298,ew316,ew324,ew332,ew334,ew335],decodeHints 0xc77168181c0e00008361b030516ab505000623115018321907808000a00028420403080400b010200804040944a000b8e070061507c3e020581c12880202008070500014004981926061d00874020180c0808020200a0500028000a0080428020a00864091902418040881c2207158d60c2b⟩,
  ⟨95,7,[ew83,ew280,ew298,ew316,ew324,ew332,ew334],localHints 6 0xd8c4cc190788440380807d860b2509c2c06228e8e2035a2cca685043080ba01a005c20e0a0096a32048881804128440e172f0282400 0xf82f392bce8203d248c4922e0b8b49232082daec2ceb0baeb60e3894aa220a884922608089295cea5792420e39731720b2083085cb5c6492167a054921a79e33a616498538e96490558558b2e38e31482065d71882055c58524988208924a182045e79f38e7de79d38e5967012dc6c821a5d76482185d75965411555034c049244f40039000f00338e00c3422cd08c0802c008928020a0090022021061c0147006004144003002042083080040⟩
]

def nodesBlock4 : Array Node := #[
  ⟨95,8,[ew280,ew298,ew316,ew324,ew332,ew334,ew335],localHints 6 0x534b442390d0c20e0d8516a310c83c454c10d2c1820190744a171c0403e49058442b1f6292c1400138042c0617b883c3a1c80812031a99d4618020ac10702f0480e05 0xd6e966f86396f8df60d66160ce6346f2d744b26180ce4ce4b25334ce5b348e5144f25960cd6719a76319a76590cd6189a759698d53098d5969a75149a6baf98d3af98dbae98638e0c762d6e966d2696180c76592695abb0752b247596aa95142477e84853a82457df4c738e2459c59873472479c79853450c162575e92575e6180c192475e5967418a374159675e8a275d3a17417e174138e7607df10110110434d75d75d7411c775e14575e1c77411410c26596dc6186da6590c261819559618651419759619551419341049138e49141018f38e10410c0c234c18b1c724a1452481c71861451041000c2040⟩,
  ⟨95,7,[ew83,ew292,ew298,ew316,ew324,ew332,ew334],localHints 6 0x590d0644220078704da2083ec480909b0c101613818aa0242998e2b429a1894a403e84680122971300b1183406220601014052a0002417 0xd7b0310c0c79e35040a42f25ebc941029e789aee90cba4aeb24c30742d19eb464101de78632c86bb2130c1abae126a1a4a86249864855429127a44410a279c450450c3145265499449251092629245468c48631061a286181e7944107de79d41055470131c6ca29424968a2992496071d41865c71d61865544c11044834424103cd38230e08d08330c08a2c524b14a142242147202188087085185003002102083080100003002042083080040⟩,
  ⟨95,8,[ew292,ew298,ew316,ew324,ew332,ew334,ew335],localHints 6 0x538b442638d0b8594c08c3419858881448108a4401e07b8c38c617c284c107d89012132482096000b8584e06160041602158741a39018d4300c1f8102a41039502405 0x92e92bf8639bf8df6092612091635a33a35a33618091a11a33534a114b4a11514a3349208bb72bcd63298db6d08b61898d4b18cb53198b492a8d51498b9f0a1d47099d9e7a0b45108662ebc8b6e908618086b6d9084abb0652b906492a88514906469a1a9e991a451a069e791a2e59867659062cb8da75a0806181625d71626180805d71454a114082114049215b82010010010445110411f1452de14075e1402cb15b75d14519c14069c14018615b69a0816181045d71196180815d711651410449211551411349210511008145010f34d1042cb10e34d10c2cb10a208104186109208107186105103081000⟩,
  ⟨95,7,[ew295,ew298,ew304,ew316,ew324,ew332,ew334,ew335],decodeHints 0x210d3f0401c0e00008b25908050462305000623115040321907808442200028783c080a840200580810094c85c001700430210c0819004640100c0604020944a000b84421500102c040b8e0241a09378201808089242a112f801900000804040b0102c56090e8246a080c0205616a78580a05⟩,
  ⟨95,8,[ew295,ew298,ew316,ew324,ew332,ew334,ew335],localHints 6 0x435bc7e22038b214118c41a1907888143c060a8401ca88942f50248ce3eca25800200114b243c021602c56705b07406091a99d3218020202a16340482205 0xd91197356b67351340d96990d46b2730cf25b069a0d45d45b06711145f15946591301300cda6f72d6af3eda690cd69a3ed9ae10d66e3cd9a612d6593cdaec58c52c3ccaeb5cd5140c76aa727a6a26769a0c7a692676681079a82476591279a62474a55865252464925c75142463643c732424734d8c63060c36a214186214169a0c386114114114465914516014551414149214151415f49214134d15e30c15e34d14130c15e1c71411861411c715e1860c210271d69a71b11b0c269a1451580c265811751459549259551411349211134d3d030c3ce34d10430c10b1c724a1862481c71041861451000c2040⟩,
  ⟨95,7,[ew70,ew298,ew304,ew316,ew324,ew332,ew334,ew335],decodeHints 0x210d3f0401c0e00008b25908050462305000623115040321907808442200028783c080a840200580810094d05c001700430210c0819004640100c0604020002e000b8980a100f87c040b038140a07038140a07038140a070005c00170080428020a0081a09068241808060205649a78ac2205⟩,
  ⟨95,8,[ew70,ew298,ew316,ew324,ew332,ew334,ew335],localHints 6 0x10d6f1f9be0e1e96446310c83c440a138f054200e54a14260f82c4809098200e366612c0017080051c2c658782841011c16e1d068ac06674d06018491a8102a16089e02405 0x9bbdb7fb77c7fbbfa09b75b0937787d5e785d575d093dd35d56f6bd3bf65d36db11565508dc357cf77544fc3008d75d44fb74bcd6f444db6d10f6db44dcb35e44f3464cb264d4d30867717c9c312c975d086c302c96eebc6b6e2c66db109b6d2c69ac5e24ec2e29a66464d32e236b44692b2c634daa292208075d16971c16975d08071c1451681401401446db1404e71619a71614d31409a616136514092514034d1619211611a31408a31401861618a108175d7e071c7de75d08171c14515a0816da2195555d84d35d65552144d320e3cf45234d4503cf20e34d2072492cc1862ca249207186145103081000⟩,
  ⟨95,7,[ew83,ew298,ew304,ew316,ew324,ew332,ew334],localHints 6 0xd8c4cc19078f040b42989c2c0622990e203720104c100f82d66c3252140fa31a005c20e0a008460d0488818080517c2425088000a17 0xf92f392bce9243d248c4922e4b8b49232492daec2ceb0baeb58e389492224a884922649276a920ea4869aa0e3887c87cb2e79e79524969249924a59244628a338e8e28a138e7df8052e07df78521e0d274171d05248371c04e6d569b54e38169a54c5412c104c0552d55495412010490552155595416010570555955064c249244f40239008f08638e08c3472cd1cc1c22c21c928220a089087207086080140006002142003102044083080040⟩,
  ⟨95,8,[ew298,ew304,ew316,ew324,ew332,ew334,ew335],localHints 6 0x550b442390d0c20e0d85046310c83c440a1e0806b532589c2c060f19072033c84808c812800be17a9098035108841ca1f010bc160d0e82418180419c92900a8145607 0x655e957386b9738df665569564f6b4732d7447269a64f38f47293338f57344f9243b255564ab312cc6b12ccb2c64a69a2cc5552ca9302ca5552cc9242cbbaf2ca3ef2cabae2c13cf6476ad209b2d20969a647b2c20955520792b20755520992420836a2073ea20734d2293cf7c77c77df28a20820865e61872869a72761865e69a06555504192406655506592404e8a24633cf4638a20613cf7df7e065e2a07df7dd65e1dd64269b71361b11369a6426181135565c24961025555134921023d04403501003cf38234d1003002c22821023022c02801002402021c21022422001c01001800421421020c2040040⟩,
  ⟨95,7,[ew83,ew298,ew312,ew316,ew324,ew332,ew334],localHints 6 0x1b0d06443a5031cc3816139541685330c8e208130403e0f12024a6135a01d864a436906801228c0b6021183406042b0481425088000a17 0xdaf0310c0caeb35040a42f26bbc94102abac972e68cb9a71c24c31942d22bb48410b2bac84c84cc3134ea649a486a920925769aa1e7934109de7a641065394630c9228932498e28a12496538062080d07c179f05040379e04c75671d58c30171c5896c169b0492566965886016580482165d60530435430d40c14c14874424103cd38230e08d08730c08a2c524b14a142242147142202087085205147142182087085185003102044083080040⟩,
  ⟨95,8,[ew298,ew312,ew316,ew324,ew332,ew334,ew335],localHints 6 0x554b442478d0601b2d88c340d0cac0420639870960a0b09c580b1587464390404a1c25001582e8e1300452100f8083c0f73090062f0484d4a040c0d40e490a8447e05 0x696e967786f9778df66966d66926f54734754736db692452473b344525b4452b2c47359668da327706f23f0a2868d6db3f05b130db313cd596570b2c3cd42f44b4af3cb41044d4926886db1eea281ee6db688a281c75ad1c8b2d1c85961c6b2c04804804149204106b1c736a1c82ea1c834d1c62cb69e6db041a280696db69ea2806751404159606651406559604706469e49206386104134d06286106034d04705f69e2086806dc74265c2426db68065924259760051724059654251424049344541324549244041024534e3c02ce24034d3052c524520a1c01ca2402081c51850400400421020420c2040040⟩,
  ⟨95,8,[ew298,ew314,ew316,ew324,ew332,ew334,ew335],localHints 6 0x1dc9a2d220383614118c41a190788814ef1ad4c96010f0b056790e84808ce12800d2171c018222a6687c042905ae04803a582418181d99c92870a8142c07 0x6560567356b67350746566966516b2730cf24f069a6514114f05b10514314d159607007064ca6f72d6af3ada6964c69a3ad52e04c5ae38c51406d59638caec4ca46c38aaeb40c4516596aa209a6a20969a659a692092092015962082282083cf2094512093cf22745120930c20728a20730c20928a65e05e72669a72506565e69a20822465e5a40503cf4e34514e33cf06245106130c3a028a39f30c04128a20805d65e25d64269b71561b11569a6426181155970425171025960555141024524c03d21004514023cf10030d38228d10230c2c02801002402021c21022422001c01001800421421020c2040040⟩,
  ⟨95,8,[ew74,ew298,ew316,ew324,ew332,ew334,ew335],localHints 6 0xee4d16a081c3d0d88c620d0c83d6021100704a17138e0541f058929809098200e366812c000a03004902c67878283f011e5721d190ac06180b030f41202124ce880a8446a05 0x25badb7fc77d7fcafb25b75b2537797d5eb95d575d253e135d56f7ad3af75d36db2d565524d7367f477647471c24d75d474a75acd6f544da692f46db44dcb35e44f3464cb264d4d324775d33171c33175d24771c30c33030730730b6db3079ef3224ef3229e73074d332236e30792e30734d32292224076d7c2b2d10275d240b2c1026eaac0a6a1006db2c2a691004e85e19e81214d36409e712136644092610034d9619211211e33008a31001c73218a124875d7e071c7de75d24871c30c31a2486da0595555d84d35d65550544d304e3cf45234d4503cf04e34d30c2ca2481c7046082105000103082041000⟩,
  ⟨95,7,[ew83,ew298,ew316,ew320,ew324,ew332,ew334],localHints 6 0x361ad38dc2c27151541e0910818401c5a14c76260807c166612215864a199c4260803e9868012283828020195c2422060101425088000a17 0xd9b1310c4c9a635041c4302e6c0b410be698b58b58c3165aeb6bad6410b2baea410716a4930c716a092cb1d09c69a71904079a619d95432551d74630c50b90672418b2d46941961a18e18628465860d08017e00504037df04c79375e4cc30175d4cb6c171b04b2d36930560576575d85c15814c654151504619351348a4424103cd38230e08d08a30c08a0852c514a1422c208a08524514a142242147202188087085185003102044083080040⟩,
  ⟨95,8,[ew298,ew316,ew320,ew324,ew332,ew334,ew335],localHints 6 0xab16884721a03836143e8686e4b0b09c542c078242422050841806100706a181dc3c4a002b85d1c26008a422100f8083c0b1200c3a2b2485466395d04d4c05021201007 0x6d7ed77b973a7b9e376d77176d273647447647471c6d24524749354525f54529244745d76ce9e737371c3739e76ce71c34d5f234e93234e5d734c92420e20e2084922082316e99e720871c2309e76e971c22fb6d2085d722eb6d22c5d720d22b6e949220d22a6e938e6c37287a59e81e571c6c39e71e55e60839261c35d75a59241c34234414a31c14104434921c13a23433621c338e34130120320321f85f21f81f2032036c471d79569d15571c6c469a1555d86445181445d759551414449344041314049244441014038f34434f14438e3403002042042092c92092892042041400c61c40461440c3080040⟩,
  ⟨95,8,[ew298,ew316,ew322,ew324,ew332,ew334,ew335],localHints 6 0x1dc9a2d22038361411bc057a8258043c0f160480622050f018203c8d430d212800d4171c01822106887c0429058343a32381242a164d84d0605025201007 0x6562167356b67352346566966516b2730cf24f069a6514114f05b12114314d15962302306598ef34e6af34e8e365969a34e34e34859634d36e34da2834e45134ea2836d45166622672c69a72b22b66669a34d36a6665aa210a284e94514e9a2822745134d2256663a56436a47218e41e169a6438e31e15222035a21c35142215961c33e04c14601c13cf4034511c13013433831c33033413811c17c12037831c374320120164469b71561b15569a6446181555972045171445962155141444524c03d21404514043cf1403803443041443843403001402c02042841442442002001400c61c40461440c3080040⟩
]

def nodesBlock5 : Array Node := #[
  ⟨95,8,[ew78,ew298,ew316,ew324,ew332,ew334,ew335],localHints 6 0x3b9345a61070f436143e868320f110f018200e0942e271c044201f058901213a48200e366a12c1400030045e2c69878b639010742c0d3d84806353ca70303b02124e0840a8cc5605 0x3dbb1b7fe73f7feb3d3db71b3d373b7f8f3b5f871c3d3e935f86f9b13b395d36db4786783cd75d4b771c4b775d3cd71c4924b648d48d4916db48dd354a54f54a5d3448d4d33c77337f17732b171c3c775d2b1a72b076f2287a694716db2879f05e24f02a29e76474d32a236f48796f28734d4a29623c072e7eab6e12a71c3c0b6d12a6ebb00a6b1006db46aa691004e85e19e81214d36409e712136648096610034d4a19611211e42808a41001c78e18a13ce75d7e071c7de75d3ce71c49249a3ce6da0595555d84d35d65550544d34924503ce34d04c20828b1c72892080411c7046082105000103082041000⟩,
  ⟨95,7,[ew298,ew316,ew324,ew328,ew330,ew334],localHints 6 0xfe0f06c6c1a30034320f109481830100707a26009acc611070b8b81f0115417101200c5e097984dce05021201007 0x4934934925d74964a84935d33a73a648f5e648f48f4924d34923a548f4d33225e458a66430a5d75a25a248a7234a24e34a271c48a4d338a8213883e138882038a3cf1dd5df58365f1c35d759d59d4834de49d71e49d4d348371c38335b3813db38134d3833cf1c129a30321a1c328a2412011545d85846581445d75945944844d54944554944d34844513843d03803503803cf38434d14028b30420b14428a2402001400c61c40461440c3080040⟩,
  ⟨95,8,[ew298,ew316,ew324,ew328,ew332,ew334,ew335],localHints 6 0x2d108680eab918960609008461a068ac3a2205084185b1a86038f4128005c17470980216088503c982485458d51200c5e095d84d4e05021201007 0x6555157326b37325316556956596b045247045269a65946f35235234d55534d36e66b36b34d69a36d36d66b69a35136c66b55535136a66b4aa64a8e97276a93278e364a69a32756850a26830a55552752730a80a44848830880844a48a34a34a34898834894834a34a6436a47218e41e169a6438e31e15625030a21c35555215211c34834418011c14814438033433433417c13417813433431c129d30321d1c328a24120164469b71361b15369a6446181535565045d61445555135131444844404001404804444043443443403c034038034434414028b30420b14428a2402001400c61c40461440c3080040⟩,
  ⟨95,8,[ew81,ew298,ew316,ew324,ew332,ew334,ew335],localHints 6 0x2d10868b2ac06c461a0c83c440a1088038250b8982c290f87816241782426480401c6cd6258000c0116050f812010ad501d068e406354e860183f0212522150889c8205 0x55809873a6bb73a0b955869855369a9b79b89b769a5539939a69b65d35d35d761854dc3570f6b544fc3054d69a44f63408d0b444d618a4fa0f44dcb39a24f3462cb298d4d35476b1709c312c969a547c302c962f0870af2c7618a49a092c796e99f4ee2df9659874d32df36d4478ad2c734d8df89f5406ac703aec14369a540aeb14362a0800aa140618a43a031404e799e96715e4d398096515e3644408a414034d8de89e15e1e12c07e11401c781e7de55469a71d09d71b69a5540945d75d95546185d75d65544d30923cf45034d4503cf08e34d08c2492ca1c72ca2490881c70860c31440001440c3081000⟩,
  ⟨95,8,[ew298,ew316,ew324,ew330,ew332,ew334],localHints 6 0x6eae77139345a9207068320f11834420610088180a0e0f44c01148403e020f02c4a11000482ee81200c5e096b84d7805021201007 0x4d382e4d462e4d48204ed61838faac38e6183abaa938f6183a83a738f52732262668a82630a6185e282030a9254c85253089244ca51438a7233a23e33a271c38a3cf1dd6216838211c36185dd8201c349f4c151f1c14924c35143833de39d71e39d3cf38371c1c129b30321b1c328a2412011506196845991446185d05961445154c04951405144c44923843d13903513903cf38434d14028b30420b14428a2402001400c61c40461440c3080040⟩,
  ⟨95,8,[ew43,ew298,ew316,ew324,ew332,ew334],localHints 6 0xdd590681a6010830a4300e37c4c4408840c61e2e090c213410d84e0600808240e5e82406235482014041127800074905c0a25 0x71052c72b4ec72b5147104d03e94ea64d52a3cd4d38295143cd92870e4283ce92470d4102e64e75c85272c84d38265142c842570a9252ca4107089242ca3633c83a32c834d64a38a19f4e18817a11814d381f79e18141d7046dd1844107016db18435a3c139a18134d6443841842182c12981812085c42840c55140d64d30d55140c54d34514524454100c53853c93493c938c0c534c0c92892c52052c52870c92070c21021850451851000c2040⟩,
  ⟨95,7,[ew298,ew316,ew324,ew331,ew334],localHints 6 0x4c1706c04550d034c021060b4a4300e09c4c0135844fc630731cb86c1200ce4093104cb0050223c1007 0x90f6a28e15225a16a180f50f31e51f58a69f30a5144de69a30a61d2483dd30861824a3cf1db51c58369c1c35144db69a1c33d90816191c13cf0836181c12973032171c328a2412011525155844551445144d24511443d03803501403cf38434d14028b30420b14428a2402001400c61c40461440c3080040⟩,
  ⟨95,7,[ew298,ew316,ew324,ew331,ew332,ew334],localHints 6 0x231540c121b0b81c1a0688c420c16888141c13898026b089f898250031c2e6c1200ce4093104cb0050223c1007 0x4516db4575554516e746655544f6e58a45554646db44f5558e38e188f8a131f5605ca6e030a55551f6db30a30a44844830830844a24a30a65e2483de30865924a3cf1dc55d5c36dd1c355551c6db1c31c34414411c11c14430831c33da08165a1c13cf0836591c12983032181c328a2412011535565c44961445555134921441444404401401404443841443d03803501403cf38434d14028b30420b14428a2402001400c61c40461440c3080040⟩,
  ⟨95,8,[ew298,ew316,ew324,ew332,ew334,ew336],localHints 6 0x90041dadd66ac28fe11c501a190788815aa060b4401c128006c17d489c6816089f8981f0131c16e91200ce4096c04d7c050223c1007 0xbefbeebd56ae6596ad64f66d64f69a659b2b4697aa58f54f44f78f52956865986764a6a764a86165969a32556658a78a30a54a52579e30a8e44483e43088e324a3cf6596a264386264369a6598611df5605837831c354351f79e1c335d4413dd1c134d0833cf1c129c30321c1c328a24120165969b64461b64469a6596181535575844841445445134921443d04403501403cf38434d14028b30420b14428a2402001400c61c40461440c3080040⟩,
  ⟨95,7,[ew298,ew316,ew324,ew329,ew332,ew334],localHints 6 0x6b86c02090681a60118841806290c014220e09c4c0190044206307114b8002205c4abf1200dc2095504d3e05024781007 0x49381349a618492820493613490820aa96184a98204906189e79e89d04d332562668a82630a6185e582030a7a44884e430879e48a4d330a75d3c84103087633ca4231e16226838221c36185e18201c34df48179f1c14d348379e1c34103c175d1c141c3c375c1c129b30321b1c328a2412011566196845591446185d65551444d44804541404d34844511444103c038e14040d3c438d14028b30420b14428a2402001400c61c40461440c3080040⟩,
  ⟨95,8,[ew83,ew298,ew316,ew324,ew332,ew334],localHints 6 0x1b0d0641f561081841550e5504e260b0408a1fa702ccc24a6824a6132552810071b0d003af0705004230680c440c020284a11000480a17 0x84eab094d47084daaa8ce45174b46f94aaaf74a4518cbaaa74ab6e85a36e75ab6db0a34d64846b947aab6474518c8aaa6477a985536965579ea0734d6552a77476a764728a9956955c44649418a45c14518c48a25c13608547a05d434d7c179e5d429c74169c5c128a6d46945d41d86415585c11c759455409309208345109038f08334f08338308234d0832cc08628c0862c60832830862090831c90832030861c6080105083045083103080040⟩,
  ⟨95,9,[ew298,ew316,ew324,ew332,ew334,ew335],localHints 6 0xe096885c01a6fc1dbede86f781411eec35ba068641fb91102b7021db8300c20db0736a4b128002417da09803b3088403c1f016c8161d1200f62090c04c2a05026c01007 0x655ed57396ba739e3765569564f6b5730db547069a64fd0f470872ccf57244f861c7055564a9af72b6af32b9a664a69a32b56db8a86d30a555b2b86130aa6a4483ea308a69a0a3cf6436a77229a71e269a6439a61e25649438641c35558e28611c33604413e01c134d7c33cf1c129e30321e1c328a74120164469b71361b15369a6446181535565c44961445555134921443d04403501403cf38434d14028b30420b14428a2402001400c61c40461440c3080040⟩
]

def nodesGet (i : Nat) : Option Node :=
  if i < 48 then
    if i < 16 then
      nodesBlock0[(i-0)]?
    else
      if i < 32 then
        nodesBlock1[(i-16)]?
      else
        nodesBlock2[(i-32)]?
  else
    if i < 64 then
      nodesBlock3[(i-48)]?
    else
      if i < 80 then
        nodesBlock4[(i-64)]?
      else
        nodesBlock5[(i-80)]?

def fastViews : QFast.Table View := ⟨96,viewsGet⟩

def fastNodes : QFast.Table Node := ⟨92,nodesGet⟩

end SignedProjection


namespace SignedProjection
def aliasMap1 : Array Nat := #[32,33,34,35,36,37,38,39,0,0,0,0,0,0,0,0,48,49,50,51,52,53,54,55,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,40,41,42,43,44,45,46,47,0,0,0,0,0,0,0,0,56,57,58,59,60,61,62,63]
def aliasMap2 : Array Nat := #[0,0,0,0,0,2,4,6,16,18,20,22,0,0,0,0,0,0,0,0,40,42,44,46,56,58,60,62,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap3 : Array Nat := #[0,0,0,0,0,1,4,5,16,17,20,21,0,0,0,0,0,0,0,0,40,41,44,45,56,57,60,61,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap4 : Array Nat := #[0,0,0,0,0,1,2,3,16,17,18,19,0,0,0,0,0,0,0,0,40,41,42,43,56,57,58,59,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap5 : Array Nat := #[0,0,0,0,0,1,2,3,4,5,6,7,0,0,0,0,0,0,0,0,40,41,42,43,44,45,46,47,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap6 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,16,17,22,23,24,25,30,31,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,48,49,54,55,56,57,62,63,0,0,0,0]
def aliasMap7 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,16,18,21,23,24,26,29,31,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,48,50,53,55,56,58,61,63,0,0,0,0]
def aliasMap8 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,16,19,20,23,24,27,28,31,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,48,51,52,55,56,59,60,63,0,0,0,0]
def aliasMap9 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,17,19,21,23,24,26,28,30,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,49,51,53,55,56,58,60,62,0,0,0,0]
def aliasMap10 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,18,19,22,23,24,25,28,29,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,50,51,54,55,56,57,60,61,0,0,0,0]
def aliasMap11 : Array Nat := #[0,0,0,0,0,8,0,10,0,12,0,14,0,0,0,0,0,0,0,0,0,24,0,26,0,28,0,30,0,0,0,0,0,0,0,0,0,40,0,42,0,44,0,46,0,0,0,0,0,0,0,0,0,56,0,58,0,60,0,62,0,0,0,0]
def aliasMap12 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,37,39,41,43,53,55,57,59,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap13 : Array Nat := #[0,0,0,0,0,8,0,9,0,12,0,13,0,0,0,0,0,0,0,0,0,24,0,25,0,28,0,29,0,0,0,0,0,0,0,0,0,40,0,41,0,44,0,45,0,0,0,0,0,0,0,0,0,56,0,57,0,60,0,61,0,0,0,0]
def aliasMap14 : Array Nat := #[0,0,0,0,0,8,0,9,0,10,0,11,0,0,0,0,0,0,0,0,0,24,0,25,0,26,0,27,0,0,0,0,0,0,0,0,0,40,0,41,0,42,0,43,0,0,0,0,0,0,0,0,0,56,0,57,0,58,0,59,0,0,0,0]
def aliasMap15 : Array Nat := #[0,0,0,0,8,9,10,11,12,13,14,15,0,0,0,0,0,0,0,0,40,41,42,43,44,45,46,47,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap16 : Array Nat := #[0,4,0,5,0,6,0,7,0,12,0,13,0,14,0,15,0,20,0,21,0,22,0,23,0,28,0,29,0,30,0,31,0,36,0,37,0,38,0,39,0,44,0,45,0,46,0,47,0,52,0,53,0,54,0,55,0,60,0,61,0,62,0,63]
def aliasMap17 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,63,61,59,57,47,45,43,41,55,53,51,49,39,37,35,33,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap18 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,3,5,7,17,19,21,23,41,43,45,47,57,59,61,63,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap19 : Array Nat := #[0,0,0,5,0,0,0,7,0,0,0,13,0,0,0,15,0,0,0,21,0,0,0,23,0,0,0,29,0,0,0,31,0,0,0,37,0,0,0,39,0,0,0,45,0,0,0,47,0,0,0,53,0,0,0,55,0,0,0,61,0,0,0,63]
def aliasMap20 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,11,19,27,39,47,55,63,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap21 : Array Nat := #[0,0,0,0,0,1,0,17,0,37,0,53,0,0,0,0,0,0,0,0,0,9,0,25,0,45,0,61,0,0,0,0,0,0,0,0,0,3,0,19,0,39,0,55,0,0,0,0,0,0,0,0,0,11,0,27,0,47,0,63,0,0,0,0]
def aliasMap22 : Array Nat := #[0,0,0,0,0,1,0,3,0,9,0,11,0,0,0,0,0,0,0,0,0,21,0,23,0,29,0,31,0,0,0,0,0,0,0,0,0,33,0,35,0,41,0,43,0,0,0,0,0,0,0,0,0,53,0,55,0,61,0,63,0,0,0,0]
def aliasMap23 : Array Nat := #[0,0,0,0,0,1,0,17,0,35,0,51,0,0,0,0,0,0,0,0,0,9,0,25,0,43,0,59,0,0,0,0,0,0,0,0,0,5,0,21,0,39,0,55,0,0,0,0,0,0,0,0,0,13,0,29,0,47,0,63,0,0,0,0]
def aliasMap24 : Array Nat := #[0,0,0,0,0,1,0,5,0,9,0,13,0,0,0,0,0,0,0,0,0,19,0,23,0,27,0,31,0,0,0,0,0,0,0,0,0,33,0,37,0,41,0,45,0,0,0,0,0,0,0,0,0,51,0,55,0,59,0,63,0,0,0,0]
def aliasMap25 : Array Nat := #[0,0,0,0,0,1,0,7,0,9,0,15,0,0,0,0,0,0,0,0,0,17,0,23,0,25,0,31,0,0,0,0,0,0,0,0,0,33,0,39,0,41,0,47,0,0,0,0,0,0,0,0,0,49,0,55,0,57,0,63,0,0,0,0]
def aliasMap26 : Array Nat := #[0,0,0,0,0,3,0,7,0,9,0,13,0,0,0,0,0,0,0,0,0,19,0,23,0,25,0,29,0,0,0,0,0,0,0,0,0,35,0,39,0,41,0,45,0,0,0,0,0,0,0,0,0,51,0,55,0,57,0,61,0,0,0,0]
def aliasMap27 : Array Nat := #[0,0,0,0,0,3,0,7,0,0,0,0,0,11,0,15,0,0,0,0,0,19,0,23,0,0,0,0,0,27,0,31,0,33,0,37,0,0,0,0,0,41,0,45,0,0,0,0,0,49,0,53,0,0,0,0,0,57,0,61,0,0,0,0]
def aliasMap28 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,47,45,43,41,55,53,51,49,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap29 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,33,35,37,39,17,19,21,23,41,43,45,47,25,27,29,31,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap30 : Array Nat := #[0,0,1,0,2,0,3,0,8,0,9,0,10,0,11,0,16,0,17,0,18,0,19,0,24,0,25,0,26,0,27,0,0,36,0,37,0,38,0,39,0,44,0,45,0,46,0,47,0,52,0,53,0,54,0,55,0,60,0,61,0,62,0,63]
def aliasMap31 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,63,61,59,57,30,28,26,24,55,53,51,49,22,20,18,16,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap32 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,59,0,0,43,57,0,0,41,26,0,0,10,24,0,0,8,63,0,0,47,61,0,0,45,30,0,0,14,28,0,0,12,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap33 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,16,19,20,23,24,27,28,31,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap34 : Array Nat := #[0,0,0,0,0,4,16,20,33,37,49,53,0,0,0,0,0,0,0,0,8,12,24,28,41,45,57,61,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap35 : Array Nat := #[0,0,0,0,0,2,16,18,33,35,49,51,0,0,0,0,0,0,0,0,8,10,24,26,41,43,57,59,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap36 : Array Nat := #[0,0,0,0,16,18,20,22,8,10,12,14,0,0,0,0,0,0,0,0,49,51,53,55,41,43,45,47,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap37 : Array Nat := #[0,0,0,0,33,35,37,39,8,10,12,14,0,0,0,0,0,0,0,0,49,51,53,55,24,26,28,30,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap38 : Array Nat := #[0,2,0,3,0,6,0,7,0,10,0,11,0,14,0,15,0,18,0,19,0,22,0,23,0,26,0,27,0,30,0,31,0,34,0,35,0,38,0,39,0,42,0,43,0,46,0,47,0,50,0,51,0,54,0,55,0,58,0,59,0,62,0,63]
def aliasMap39 : Array Nat := #[0,0,1,0,4,0,5,0,8,0,9,0,12,0,13,0,16,0,17,0,20,0,21,0,24,0,25,0,28,0,29,0,0,34,0,35,0,38,0,39,0,42,0,43,0,46,0,47,0,50,0,51,0,54,0,55,0,58,0,59,0,62,0,63]
def aliasMap40 : Array Nat := #[0,0,0,6,1,0,0,7,8,0,0,14,9,0,0,15,16,0,0,22,17,0,0,23,24,0,0,30,25,0,0,31,32,0,0,38,33,0,0,39,40,0,0,46,41,0,0,47,48,0,0,54,49,0,0,55,56,0,0,62,57,0,0,63]
def aliasMap41 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,48,0,0,51,52,0,0,55,56,0,0,59,60,0,0,63,32,0,0,35,36,0,0,39,40,0,0,43,44,0,0,47,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap42 : Array Nat := #[0,0,0,8,0,0,0,12,0,0,0,11,0,0,0,15,0,0,0,24,0,0,0,28,0,0,0,27,0,0,0,31,0,0,0,40,0,0,0,44,0,0,0,43,0,0,0,47,0,0,0,56,0,0,0,60,0,0,0,59,0,0,0,63]
def aliasMap43 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,16,0,0,19,20,0,0,23,56,0,0,59,60,0,0,63,0,0,0,3,4,0,0,7,40,0,0,43,44,0,0,47,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap44 : Array Nat := #[0,0,0,0,0,4,0,7,0,12,0,15,0,0,0,0,0,0,0,0,0,20,0,23,0,28,0,31,0,0,0,0,0,0,0,0,0,36,0,39,0,44,0,47,0,0,0,0,0,0,0,0,0,52,0,55,0,60,0,63,0,0,0,0]
def aliasMap45 : Array Nat := #[0,0,0,0,0,0,0,3,0,8,0,11,0,0,0,0,0,0,0,0,0,20,0,23,0,28,0,31,0,0,0,0,0,0,0,0,0,32,0,35,0,40,0,43,0,0,0,0,0,0,0,0,0,52,0,55,0,60,0,63,0,0,0,0]
def aliasMap46 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,16,0,0,24,20,0,0,28,51,0,0,59,55,0,0,63,0,0,0,8,4,0,0,12,35,0,0,43,39,0,0,47,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap47 : Array Nat := #[0,0,0,0,0,3,4,7,8,11,12,15,0,0,0,0,0,0,0,0,16,19,20,23,24,27,28,31,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap48 : Array Nat := #[0,0,0,6,0,0,0,7,0,0,0,14,0,0,0,15,0,0,0,22,0,0,0,23,0,0,0,30,0,0,0,31,0,0,0,38,0,0,0,39,0,0,0,46,0,0,0,47,0,0,0,54,0,0,0,55,0,0,0,62,0,0,0,63]
def aliasMap49 : Array Nat := #[0,0,0,5,2,0,0,7,8,0,0,13,10,0,0,15,16,0,0,21,18,0,0,23,24,0,0,29,26,0,0,31,32,0,0,37,34,0,0,39,40,0,0,45,42,0,0,47,48,0,0,53,50,0,0,55,56,0,0,61,58,0,0,63]
def aliasMap50 : Array Nat := #[0,0,0,0,1,3,5,7,8,10,12,14,0,0,0,0,0,0,0,0,17,19,21,23,24,26,28,30,0,0,0,0,0,0,0,0,33,35,37,39,40,42,44,46,0,0,0,0,0,0,0,0,49,51,53,55,56,58,60,62,0,0,0,0]
def aliasMap51 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,40,41,42,43,56,57,58,59,0,0,0,0,0,0,0,0,4,5,6,7,20,21,22,23,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap52 : Array Nat := #[0,0,0,0,0,6,0,7,0,10,0,11,0,0,0,0,0,0,0,0,0,22,0,23,0,26,0,27,0,0,0,0,0,0,0,0,0,38,0,39,0,42,0,43,0,0,0,0,0,0,0,0,0,54,0,55,0,58,0,59,0,0,0,0]
def aliasMap53 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,38,39,42,43,54,55,58,59,0,0,0,0,0,0,0,0,4,5,8,9,20,21,24,25,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap54 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,37,39,41,43,53,55,57,59,0,0,0,0,0,0,0,0,4,6,8,10,20,22,24,26,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap55 : Array Nat := #[0,2,4,6,0,0,0,0,8,10,12,14,0,0,0,0,16,18,20,22,0,0,0,0,24,26,28,30,0,0,0,0,32,34,36,38,0,0,0,0,40,42,44,46,0,0,0,0,48,50,52,54,0,0,0,0,56,58,60,62,0,0,0,0]
def aliasMap56 : Array Nat := #[0,0,0,0,2,3,6,7,8,9,12,13,0,0,0,0,0,0,0,0,18,19,22,23,24,25,28,29,0,0,0,0,0,0,0,0,34,35,38,39,40,41,44,45,0,0,0,0,0,0,0,0,50,51,54,55,56,57,60,61,0,0,0,0]
def aliasMap57 : Array Nat := #[0,1,4,5,0,0,0,0,8,9,12,13,0,0,0,0,16,17,20,21,0,0,0,0,24,25,28,29,0,0,0,0,32,33,36,37,0,0,0,0,40,41,44,45,0,0,0,0,48,49,52,53,0,0,0,0,56,57,60,61,0,0,0,0]
def aliasMap58 : Array Nat := #[0,0,0,0,16,17,18,19,8,9,10,11,0,0,0,0,0,0,0,0,52,53,54,55,44,45,46,47,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap59 : Array Nat := #[0,0,0,0,0,0,0,0,0,10,0,11,0,14,0,15,0,18,0,19,0,22,0,23,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,0,43,0,46,0,47,0,50,0,51,0,54,0,55,0,0,0,0,0,0,0,0]
def aliasMap60 : Array Nat := #[0,0,0,0,16,17,20,21,8,9,12,13,0,0,0,0,0,0,0,0,50,51,54,55,42,43,46,47,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap61 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,9,11,13,15,0,0,0,0,17,19,21,23,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,40,42,44,46,0,0,0,0,48,50,52,54,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap62 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,10,11,14,15,0,0,0,0,18,19,22,23,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,40,41,44,45,0,0,0,0,48,49,52,53,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap63 : Array Nat := #[32,33,34,35,36,37,38,39,0,0,0,0,0,0,0,0,16,17,18,19,20,21,22,23,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,40,41,42,43,44,45,46,47,0,0,0,0,0,0,0,0,24,25,26,27,28,29,30,31]
def aliasMap64 : Array Nat := #[0,0,0,0,32,34,36,38,16,18,20,22,0,0,0,0,0,0,0,0,40,42,44,46,24,26,28,30,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap65 : Array Nat := #[0,0,0,0,32,33,36,37,16,17,20,21,0,0,0,0,0,0,0,0,40,41,44,45,24,25,28,29,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap66 : Array Nat := #[0,0,0,0,32,33,34,35,16,17,18,19,0,0,0,0,0,0,0,0,40,41,42,43,24,25,26,27,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap67 : Array Nat := #[0,0,0,0,0,1,6,7,8,9,14,15,0,0,0,0,0,0,0,0,16,17,22,23,24,25,30,31,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap68 : Array Nat := #[0,0,0,0,0,2,5,7,8,10,13,15,0,0,0,0,0,0,0,0,16,18,21,23,24,26,29,31,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap69 : Array Nat := #[0,0,0,0,1,3,5,7,8,10,12,14,0,0,0,0,0,0,0,0,17,19,21,23,24,26,28,30,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap70 : Array Nat := #[0,0,0,0,2,3,6,7,8,9,12,13,0,0,0,0,0,0,0,0,18,19,22,23,24,25,28,29,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def rootAliases : QFast.AliasTable
  | 4 => some (1, aliasMap33)
  | 5 => some (1, aliasMap28)
  | 6 => some (1, aliasMap12)
  | 7 => some (1, aliasMap20)
  | 18 => some (8, aliasMap70)
  | 19 => some (8, aliasMap69)
  | 20 => some (8, aliasMap47)
  | 21 => some (8, aliasMap68)
  | 22 => some (8, aliasMap67)
  | 23 => some (8, aliasMap66)
  | 24 => some (8, aliasMap65)
  | 25 => some (8, aliasMap64)
  | 26 => some (9, aliasMap29)
  | 27 => some (8, aliasMap5)
  | 28 => some (8, aliasMap15)
  | 29 => some (12, aliasMap62)
  | 30 => some (12, aliasMap61)
  | 31 => some (8, aliasMap37)
  | 32 => some (8, aliasMap36)
  | 33 => some (8, aliasMap60)
  | 34 => some (13, aliasMap59)
  | 35 => some (8, aliasMap58)
  | 36 => some (8, aliasMap35)
  | 37 => some (10, aliasMap54)
  | 38 => some (10, aliasMap53)
  | 39 => some (15, aliasMap52)
  | 40 => some (8, aliasMap4)
  | 41 => some (10, aliasMap51)
  | 42 => some (15, aliasMap14)
  | 43 => some (8, aliasMap34)
  | 44 => some (14, aliasMap27)
  | 45 => some (15, aliasMap26)
  | 46 => some (8, aliasMap3)
  | 47 => some (15, aliasMap13)
  | 48 => some (16, aliasMap10)
  | 49 => some (8, aliasMap2)
  | 50 => some (15, aliasMap11)
  | 51 => some (16, aliasMap9)
  | 52 => some (15, aliasMap25)
  | 53 => some (15, aliasMap24)
  | 54 => some (11, aliasMap46)
  | 55 => some (15, aliasMap23)
  | 56 => some (15, aliasMap45)
  | 57 => some (15, aliasMap44)
  | 58 => some (11, aliasMap43)
  | 59 => some (17, aliasMap42)
  | 60 => some (16, aliasMap8)
  | 61 => some (11, aliasMap41)
  | 62 => some (15, aliasMap22)
  | 63 => some (15, aliasMap21)
  | 64 => some (17, aliasMap19)
  | 65 => some (16, aliasMap7)
  | 66 => some (9, aliasMap18)
  | 67 => some (11, aliasMap32)
  | 68 => some (9, aliasMap31)
  | 69 => some (9, aliasMap17)
  | 70 => some (17, aliasMap48)
  | 71 => some (16, aliasMap6)
  | 83 => some (80, aliasMap63)
  | 84 => some (75, aliasMap57)
  | 85 => some (76, aliasMap56)
  | 86 => some (75, aliasMap55)
  | 87 => some (76, aliasMap50)
  | 88 => some (77, aliasMap49)
  | 89 => some (77, aliasMap40)
  | 90 => some (78, aliasMap39)
  | 91 => some (79, aliasMap38)
  | 92 => some (78, aliasMap30)
  | 93 => some (79, aliasMap16)
  | 94 => some (80, aliasMap1)
  | _ => none
end SignedProjection


namespace SignedProjection

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockRoots_0 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 0 16 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockRoots_16 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 16 16 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockRoots_32 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 32 16 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockRoots_48 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 48 16 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockRoots_64 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 64 16 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockRoots_80 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 80 16 = true := by decide +kernel

theorem joinRoots_0_0 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 0 32 = true :=
  @QFast.merge_blocks (QFast.symCheckRoot rootAliases fastViews fastNodes) 0 16 16 blockRoots_0 blockRoots_16

theorem joinRoots_0_32 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 32 32 = true :=
  @QFast.merge_blocks (QFast.symCheckRoot rootAliases fastViews fastNodes) 32 16 16 blockRoots_32 blockRoots_48

theorem joinRoots_0_64 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 64 32 = true :=
  @QFast.merge_blocks (QFast.symCheckRoot rootAliases fastViews fastNodes) 64 16 16 blockRoots_64 blockRoots_80

theorem joinRoots_1_0 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 0 64 = true :=
  @QFast.merge_blocks (QFast.symCheckRoot rootAliases fastViews fastNodes) 0 32 32 joinRoots_0_0 joinRoots_0_32

theorem joinRoots_2_0 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 0 96 = true :=
  @QFast.merge_blocks (QFast.symCheckRoot rootAliases fastViews fastNodes) 0 64 32 joinRoots_1_0 joinRoots_0_64

theorem certifiedRoots : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 0 96 = true := joinRoots_2_0

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_0 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_12 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 12 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_24 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 24 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_36 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 36 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_48 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 48 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_60 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 60 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_72 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 72 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_84 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 84 8 = true := by decide +kernel

theorem joinNodes_0_0 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 24 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 0 12 12 blockNodes_0 blockNodes_12

theorem joinNodes_0_24 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 24 24 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 24 12 12 blockNodes_24 blockNodes_36

theorem joinNodes_0_48 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 48 24 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 48 12 12 blockNodes_48 blockNodes_60

theorem joinNodes_0_72 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 72 20 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 72 12 8 blockNodes_72 blockNodes_84

theorem joinNodes_1_0 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 48 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 0 24 24 joinNodes_0_0 joinNodes_0_24

theorem joinNodes_1_48 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 48 44 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 48 24 20 joinNodes_0_48 joinNodes_0_72

theorem joinNodes_2_0 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 92 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 0 48 44 joinNodes_1_0 joinNodes_1_48

theorem certifiedNodes : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 92 = true := joinNodes_2_0

end SignedProjection

namespace SignedProjection
def bMatches (z : Option View) : Bool :=
  match z with
  | none => false
  | some v => vg v == (0xfe80e800fe800000 : Word) && vk v == 9 && (vs v).toFinset == Direct64.cols.toFinset

theorem rootNegative : ¬ CoreSigned.build signedOps (0xfe80e800fe800000 : BitVec 64) 9 Direct64.cols.toFinset := by
  have shape : bMatches (QFast.get fastViews 95) = true := by decide +kernel
  cases ev : QFast.get fastViews 95 with
  | none => simp [ev, bMatches] at shape
  | some v =>
    have valid := QFast.symCertified rootAliases fastViews fastNodes certifiedRoots certifiedNodes ev
    simp only [ev,bMatches,Bool.and_eq_true,beq_iff_eq] at shape
    change ¬ CoreSigned.build signedOps (vg v) (vk v) (vs v).toFinset at valid
    rwa [shape.1.1,shape.1.2,shape.2] at valid
end SignedProjection
end PEqualNP.Outside.L_meta_12074_aux

open PEqualNP.Outside.L_meta_12074_aux in
theorem PEqualNP.Outside.L_meta_12074 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4269860864 * 2 ^ 32 + 4269801472) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4269860864 * 2 ^ 32 + 4269801472) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  LowerSymSix.finish SignedProjection.rootNegative
