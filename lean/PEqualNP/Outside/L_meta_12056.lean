import PEqualNP.Defs

-- The witness has 12 binary gates. Any circuit with a NOT and fewer gates
-- would have at most 10 binary gates even with every negation available for free.
-- Finite signed-circuit certificates below exclude that possibility.
-- Signed-wire search and gate projections adapt the project’s Apache 2.0 proofs.
namespace PEqualNP.Outside.L_meta_12056_aux
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
  ⟨[⟨.and,[0,1]⟩, ⟨.and,[4,5]⟩, ⟨.and,[2,7]⟩, ⟨.or,[0,1]⟩, ⟨.and,[3,9]⟩, ⟨.or,[4,5]⟩, ⟨.or,[8,10]⟩, ⟨.or,[2,7]⟩, ⟨.and,[3,13]⟩, ⟨.or,[6,14]⟩, ⟨.and,[11,12]⟩, ⟨.and,[15,16]⟩],17⟩

theorem size : witness.size = 12 := rfl

theorem monotone : Monotone2 witness := by
  simp [Monotone2,witness]

set_option maxRecDepth 16000 in
theorem correct : ∀ x : Fin 6 → Bool, witness.eval (List.ofFn x) =
    Nat.testBit (4269860864 * 2 ^ 32 + 3892314112) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel

end LowerSymSix

namespace Direct64
open PEqualNP.CircuitLowerBounds SignedProjection
abbrev W := BitVec 64
abbrev basicOps (a b : W) := signedOps a b
abbrev goal : W := ~~~0xfe80e800e8000000
open CoreSigned (build)
def tableB (x : Fin 6 → Bool) :=
  Nat.testBit (4269860864 * 2 ^ 32 + 3892314112) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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

theorem low (reject : ¬ build basicOps (0xfe80e800e8000000 : W) 10 cols.toFinset)
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = tableB x) : 10 < binaryCost gs := by
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
    (reject : ¬ CoreSigned.build SignedProjection.signedOps (0xfe80e800e8000000 : BitVec 64) 10 Direct64.cols.toFinset) :
∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4269860864 * 2 ^ 32 + 3892314112) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4269860864 * 2 ^ 32 + 3892314112) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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

def ew0 : Word := 0x88008800

def ew1 : Word := 0xa000a000

def ew2 : Word := 0xaa000000

def ew3 : Word := 0xaa0000aa

def ew4 : Word := 0xaa00aa00

def ew5 : Word := 0xaaaaaaaa

def ew6 : Word := 0xc000c000

def ew7 : Word := 0xcc000000

def ew8 : Word := 0xcc0000cc

def ew9 : Word := 0xcc00cc00

def ew10 : Word := 0xcccccccc

def ew11 : Word := 0xee0000ee

def ew12 : Word := 0xf0000000

def ew13 : Word := 0xf00000f0

def ew14 : Word := 0xf000f000

def ew15 : Word := 0xf0f0f0f0

def ew16 : Word := 0xfa0000fa

def ew17 : Word := 0xfc0000fc

def ew18 : Word := 0xfe0000fe

def ew19 : Word := 0xff000000

def ew20 : Word := 0xff00ff00

def ew21 : Word := 0xffff0000

def ew22 : Word := 0x440000004400

def ew23 : Word := 0x440088000000

def ew24 : Word := 0x500000005000

def ew25 : Word := 0x5000a0000000

def ew26 : Word := 0x550000000000

def ew27 : Word := 0x2a002a2a002a00

def ew28 : Word := 0x4c004c4c004c00

def ew29 : Word := 0x70007070007000

def ew30 : Word := 0x80008080008000

def ew31 : Word := 0x88000088000000

def ew32 : Word := 0x88008888008800

def ew33 : Word := 0xa00000a0000000

def ew34 : Word := 0xa000a0a000a000

def ew35 : Word := 0xaa000000000000

def ew36 : Word := 0xaa0000aa000000

def ew37 : Word := 0xaa00aa00000000

def ew38 : Word := 0xaa00aa0a000a00

def ew39 : Word := 0xaa00aa22002200

def ew40 : Word := 0xaa00aa2a002a00

def ew41 : Word := 0xaa00aaaa00aa00

def ew42 : Word := 0xaaaa0000aaaa00

def ew43 : Word := 0xc00000c0000000

def ew44 : Word := 0xc000c0c000c000

def ew45 : Word := 0xcc000000000000

def ew46 : Word := 0xcc0000cc000000

def ew47 : Word := 0xcc00cc00000000

def ew48 : Word := 0xcc00cc0c000c00

def ew49 : Word := 0xcc00cc44004400

def ew50 : Word := 0xcc00cc4c004c00

def ew51 : Word := 0xcc00cccc00cc00

def ew52 : Word := 0xcccc0000cccc00

def ew53 : Word := 0xf00000f0000000

def ew54 : Word := 0xf000f000000000

def ew55 : Word := 0xf000f030003000

def ew56 : Word := 0xf000f050005000

def ew57 : Word := 0xf000f070007000

def ew58 : Word := 0xf000f0f000f000

def ew59 : Word := 0xf0f00000f0f000

def ew60 : Word := 0xff000000000000

def ew61 : Word := 0xff000000ff0000

def ew62 : Word := 0xff0000ff000000

def ew63 : Word := 0xff00ff00000000

def ew64 : Word := 0xff00ff80008000

def ew65 : Word := 0xff00ff88008800

def ew66 : Word := 0xff00ffa000a000

def ew67 : Word := 0xff00ffc000c000

def ew68 : Word := 0xffff0000000000

def ew69 : Word := 0x800400008004000

def ew70 : Word := 0x808040488884444

def ew71 : Word := 0x808080808080808

def ew72 : Word := 0x880088008800880

def ew73 : Word := 0xa0000000a000000

def ew74 : Word := 0xa00000a0a00000a

def ew75 : Word := 0xa000a000a000a00

def ew76 : Word := 0xa00500000000000

def ew77 : Word := 0xa0a00000a0a0000

def ew78 : Word := 0xa0a0a0a00000000

def ew79 : Word := 0xa0a0a0a0a0a0a0a

def ew80 : Word := 0xaa000000aa00000

def ew81 : Word := 0xaa00aa000000000

def ew82 : Word := 0xc00000c0c00000c

def ew83 : Word := 0xc000c000c000c00

def ew84 : Word := 0xc0c0c0c0c0c0c0c

def ew85 : Word := 0xcc000000cc00000

def ew86 : Word := 0xe00000e0e00000e

def ew87 : Word := 0xf0000000f000000

def ew88 : Word := 0xf00000f00000000

def ew89 : Word := 0xf00000f0a00000a

def ew90 : Word := 0xf00000f0c00000c

def ew91 : Word := 0xf00000f0e00000e

def ew92 : Word := 0xf000f0000000000

def ew93 : Word := 0xf000f000f000f00

def ew94 : Word := 0xf0f00000f0f0000

def ew95 : Word := 0xf0f0f0f00000000

def ew96 : Word := 0xff0000000000000

def ew97 : Word := 0x2000400020004000

def ew98 : Word := 0x20201010a0a05050

def ew99 : Word := 0x2020202020202020

def ew100 : Word := 0x2080208020802080

def ew101 : Word := 0x2200000022000000

def ew102 : Word := 0x2200002222000022

def ew103 : Word := 0x2200220022002200

def ew104 : Word := 0x2200440000000000

def ew105 : Word := 0x2222000022220000

def ew106 : Word := 0x2222222200000000

def ew107 : Word := 0x2222222222222222

def ew108 : Word := 0x2288000022880000

def ew109 : Word := 0x2288228800000000

def ew110 : Word := 0x2a2a151500000000

def ew111 : Word := 0x3000003030000030

def ew112 : Word := 0x3000300030003000

def ew113 : Word := 0x3030303030303030

def ew114 : Word := 0x30c0000030c00000

def ew115 : Word := 0x3200003232000032

def ew116 : Word := 0x3300000033000000

def ew117 : Word := 0x3300003300000000

def ew118 : Word := 0x3300003322000022

def ew119 : Word := 0x3300003330000030

def ew120 : Word := 0x3300003332000032

def ew121 : Word := 0x3300330000000000

def ew122 : Word := 0x3300330033003300

def ew123 : Word := 0x3333000033330000

def ew124 : Word := 0x3333333300000000

def ew125 : Word := 0x33cc000000000000

def ew126 : Word := 0x4400004444000044

def ew127 : Word := 0x4400440044004400

def ew128 : Word := 0x4444444444444444

def ew129 : Word := 0x4488000044880000

def ew130 : Word := 0x5000005050000050

def ew131 : Word := 0x5000500050005000

def ew132 : Word := 0x5050505050505050

def ew133 : Word := 0x50a0000050a00000

def ew134 : Word := 0x5400005454000054

def ew135 : Word := 0x5500000055000000

def ew136 : Word := 0x5500005500000000

def ew137 : Word := 0x5500005544000044

def ew138 : Word := 0x5500005550000050

def ew139 : Word := 0x5500005554000054

def ew140 : Word := 0x5500550000000000

def ew141 : Word := 0x5500550055005500

def ew142 : Word := 0x5555000055550000

def ew143 : Word := 0x5555555500000000

def ew144 : Word := 0x55aa000000000000

def ew145 : Word := 0x8000200080002000

def ew146 : Word := 0x8000400008000400

def ew147 : Word := 0x8000400020001000

def ew148 : Word := 0x8000400080004000

def ew149 : Word := 0x8000800080008000

def ew150 : Word := 0x8080000080800000

def ew151 : Word := 0x8080202000000000

def ew152 : Word := 0x8080202080802020

def ew153 : Word := 0x8080404000000000

def ew154 : Word := 0x8080404008080404

def ew155 : Word := 0x8080404020201010

def ew156 : Word := 0x8080404080804040

def ew157 : Word := 0x8080808000000000

def ew158 : Word := 0x8080808080808080

def ew159 : Word := 0x8200000082000000

def ew160 : Word := 0x8200410000000000

def ew161 : Word := 0x8200410082004100

def ew162 : Word := 0x8200820082008200

def ew163 : Word := 0x8282000082820000

def ew164 : Word := 0x8282414100000000

def ew165 : Word := 0x8282828200000000

def ew166 : Word := 0x8800000022000000

def ew167 : Word := 0x8800220088002200

def ew168 : Word := 0x8800440000000000

def ew169 : Word := 0x8800440022001100

def ew170 : Word := 0x8800440088004400

def ew171 : Word := 0x8800880088008800

def ew172 : Word := 0x8888000022220000

def ew173 : Word := 0x8888000088880000

def ew174 : Word := 0x8888222200000000

def ew175 : Word := 0x8888222288882222

def ew176 : Word := 0x8888444400000000

def ew177 : Word := 0x8888444488884444

def ew178 : Word := 0x8888888800000000

def ew179 : Word := 0x8888888888888888

def ew180 : Word := 0xa00000000a000000

def ew181 : Word := 0xa000500000000000

def ew182 : Word := 0xa00050000a000500

def ew183 : Word := 0xa0005000a0005000

def ew184 : Word := 0xa000a000a000a000

def ew185 : Word := 0xa0a000000a0a0000

def ew186 : Word := 0xa0a00000a0a00000

def ew187 : Word := 0xa0a00a0aa0a00a0a

def ew188 : Word := 0xa0a0505000000000

def ew189 : Word := 0xa0a05050a0a05050

def ew190 : Word := 0xa0a0a0a000000000

def ew191 : Word := 0xa0a0a0a0a0a0a0a0

def ew192 : Word := 0xa8005400a8005400

def ew193 : Word := 0xaa000000aa000000

def ew194 : Word := 0xaa0000aaaa0000aa

def ew195 : Word := 0xaa00550000000000

def ew196 : Word := 0xaa00550088004400

def ew197 : Word := 0xaa005500a0005000

def ew198 : Word := 0xaa005500aa005500

def ew199 : Word := 0xaa00aa0000000000

def ew200 : Word := 0xaa00aa0000aa00aa

def ew201 : Word := 0xaa00aa00aa00aa00

def ew202 : Word := 0xaaaa000000000000

def ew203 : Word := 0xaaaa0000aaaa0000

def ew204 : Word := 0xaaaa555500000000

def ew205 : Word := 0xaaaaaaaa00000000

def ew206 : Word := 0xaaaaaaaaaaaaaaaa

def ew207 : Word := 0xc0c00000c0c00000

def ew208 : Word := 0xc0c00c0cc0c00c0c

def ew209 : Word := 0xc0c03030c0c03030

def ew210 : Word := 0xc0c0c0c0c0c0c0c0

def ew211 : Word := 0xcc000000cc000000

def ew212 : Word := 0xcc0000cccc0000cc

def ew213 : Word := 0xcc003300cc003300

def ew214 : Word := 0xcc00cc0000000000

def ew215 : Word := 0xcc00cc0000cc00cc

def ew216 : Word := 0xcc00cc00cc00cc00

def ew217 : Word := 0xcccc000000000000

def ew218 : Word := 0xcccc0000cccc0000

def ew219 : Word := 0xcccc333300000000

def ew220 : Word := 0xcccccccc00000000

def ew221 : Word := 0xcccccccccccccccc

def ew222 : Word := 0xee0000eeee0000ee

def ew223 : Word := 0xf0000000f0000000

def ew224 : Word := 0xf00000f0f00000f0

def ew225 : Word := 0xf0000f00f0000f00

def ew226 : Word := 0xf000f00000000000

def ew227 : Word := 0xf000f00000f000f0

def ew228 : Word := 0xf000f000f000f000

def ew229 : Word := 0xf0f0000000000000

def ew230 : Word := 0xf0f00000f0f00000

def ew231 : Word := 0xf0f00f0f00000000

def ew232 : Word := 0xf0f0f0f000000000

def ew233 : Word := 0xf0f0f0f0f0f0f0f0

def ew234 : Word := 0xfa0000fafa0000fa

def ew235 : Word := 0xfc0000fcfc0000fc

def ew236 : Word := 0xfe000000fe000000

def ew237 : Word := 0xfe0000fefe0000fe

def ew238 : Word := 0xff00000000000000

def ew239 : Word := 0xff00000000ff0000

def ew240 : Word := 0xff000000ee000000

def ew241 : Word := 0xff000000fa000000

def ew242 : Word := 0xff000000fc000000

def ew243 : Word := 0xff000000ff000000

def ew244 : Word := 0xff0000ff00000000

def ew245 : Word := 0xff0000ffaa0000aa

def ew246 : Word := 0xff0000ffcc0000cc

def ew247 : Word := 0xff0000ffee0000ee

def ew248 : Word := 0xff0000fff00000f0

def ew249 : Word := 0xff0000fffa0000fa

def ew250 : Word := 0xff0000fffc0000fc

def ew251 : Word := 0xff00ff0000000000

def ew252 : Word := 0xff00ff00ff00ff00

def ew253 : Word := 0xffff000000000000

def ew254 : Word := 0xffff0000ffff0000

def ew255 : Word := 0xffffffff00000000

def labelsBlock0 : Array Nat := #[
  0x1b64,
  0x1d64,
  0x1b68,
  0x1b2c,
  0x1b0c,
  0x3964,
  0x1e68,
  0x1d70,
  0x1e70,
  0x1b28,
  0x1d34,
  0x1b4c,
  0x1bcc,
  0x1d14,
  0x1b60,
  0x3a68
]

def labelsBlock1 : Array Nat := #[
  0x1d60,
  0x1e60,
  0x2e38,
  0x2b2c,
  0x1e38,
  0x1dd4,
  0x37cc,
  0x379c,
  0x375c,
  0x1d30,
  0x1b08,
  0x37d4,
  0x1b24,
  0x1d54,
  0x1d24,
  0x1b04
]

def labelsBlock2 : Array Nat := #[
  0x3c70,
  0x1e18,
  0x37d8,
  0x1d04,
  0x1ed8,
  0x2ea8,
  0x3904,
  0x1042,
  0x10b2,
  0x2b8c,
  0x102e,
  0x39e0,
  0x2da4,
  0x2ba4,
  0x2eb0,
  0x1b20
]

def labelsBlock3 : Array Nat := #[
  0x1032,
  0x3ae0,
  0x2ba8,
  0x1046,
  0x10a2,
  0x105a,
  0x10c2,
  0x3ce0,
  0x2d34,
  0x2e98,
  0x1d20,
  0x104a,
  0x106e,
  0x4430da,
  0x10da,
  0x7340c2
]

def labelsBlock4 : Array Nat := #[
  0x4430c2,
  0x1b44,
  0x2b0c,
  0x1d44,
  0x371c,
  0x110f340c2,
  0x3798,
  0x3984,
  0x10d6,
  0x3920,
  0x104e,
  0x107a,
  0x3960,
  0x3a60,
  0x3c60,
  0x1b8c
]

def labelsBlock5 : Array Nat := #[
  0x1086,
  0x1bc8,
  0x1bc4,
  0x1dc4,
  0x2e30,
  0x2e28,
  0x103e,
  0x1e28,
  0x1e08,
  0x1b00,
  0x7430da,
  0x2b24,
  0x2d24,
  0x3a08,
  0x1e58,
  0x4430d2
]

def labelsBlock6 : Array Nat := #[
  0x105e,
  0x373c,
  0x108e,
  0x1b48,
  0x2d94,
  0x10d2,
  0x39a0,
  0x2b28,
  0x1108320de,
  0x4320de,
  0x10fe,
  0x10de,
  0x4420de,
  0x4430de,
  0x1002,
  0x3944
]

def labelsBlock7 : Array Nat := #[
  0x110f430da,
  0x1108320e2,
  0x4320e2,
  0x10e2,
  0x4420e2,
  0x10a6,
  0x1d00,
  0x1072,
  0x1108320e6,
  0x4320e6,
  0x10e6,
  0x4420e6,
  0x1ec8,
  0x1096,
  0x10ca,
  0x4430e2
]

def labelsBlock8 : Array Nat := #[
  0x1e30,
  0x410032,
  0x420032,
  0x630032,
  0x421032,
  0x631032,
  0x632032,
  0x2e18,
  0x3718,
  0x1d10,
  0x1e10,
  0x1e00,
  0x5100b2,
  0x5200b2,
  0x5300b2,
  0x5210b2
]

def labelsBlock9 : Array Nat := #[
  0x5310b2,
  0x5320b2,
  0x10aa,
  0x110c320de,
  0x10ee,
  0x110c420de,
  0x4430ca,
  0x4430e6,
  0x3a88,
  0x3758,
  0x3754,
  0x374c,
  0x110c320e2,
  0x10f6,
  0x110c420e2,
  0x4430ee
]

def labelsBlock10 : Array Nat := #[
  0x100a,
  0x1e20,
  0x39c4,
  0x3c90,
  0x107e,
  0x4430d6,
  0x110c320ca,
  0x110c320e6,
  0x4320ca,
  0x110c420ca,
  0x110c420e6,
  0x4420ca,
  0x4430f6,
  0x1b40,
  0x1dd0,
  0x1ed0
]

def labelsBlock11 : Array Nat := #[
  0x1d94,
  0x3900,
  0x2d14,
  0x110c320ee,
  0x4320ee,
  0x110c420ee,
  0x4420ee,
  0x1f38,
  0x2ea0,
  0x3760,
  0x41003e,
  0x4100a2,
  0x43003e,
  0x4300a2,
  0x43103e,
  0x4310a2
]

def labelsBlock12 : Array Nat := #[
  0x3a00,
  0x3c00,
  0x3c10,
  0x39a4,
  0x10ae,
  0x443108320de,
  0x1108320ca,
  0x10ce,
  0x110c320f6,
  0x4320f6,
  0x110c420f6,
  0x4420f6,
  0x3764,
  0x1b70,
  0x443108320e2,
  0x2b04
]

def labelsBlock13 : Array Nat := #[
  0x3714,
  0x2d04,
  0x370c,
  0x4430ce,
  0x1108320ee,
  0x100e,
  0x1022,
  0x1026,
  0x102a,
  0x1f3c,
  0x1e98,
  0x3768,
  0x1f5c,
  0x1092,
  0x443108320ca,
  0x443108320e6
]

def labelsBlock14 : Array Nat := #[
  0x2bcc,
  0x1108320f6,
  0x10fa,
  0x2e20,
  0x1e40,
  0x1d40,
  0x2b20,
  0x55,
  0x3770,
  0x5d,
  0x41,
  0x51,
  0x81,
  0x7d,
  0xb9,
  0xb5
]

def labelsBlock15 : Array Nat := #[
  0x430086,
  0x430096,
  0xe9,
  0x10d,
  0x1be0,
  0x1fe0,
  0x115,
  0x12d,
  0x13d,
  0x1de0,
  0x149,
  0x165,
  0x1ee0,
  0x189,
  0x19d,
  0x3924
]

def labelsBlock16 : Array Nat := #[
  0x2b08,
  0x443108320ee,
  0x2b88,
  0x2b84,
  0x3794,
  0x2d84,
  0x378c,
  0x1d1,
  0x4430fa,
  0x3704,
  0x1f28,
  0x3b28,
  0x3ba8,
  0x3d30,
  0x3db0,
  0x1016
]

def labelsBlock17 : Array Nat := #[
  0x1012,
  0x1006,
  0x1f64,
  0x1fcc,
  0x37c8,
  0x37c4,
  0x59,
  0x61,
  0x65,
  0x69,
  0x3728,
  0x37d0,
  0x85,
  0x89,
  0x8d,
  0x9d
]

def labelsBlock18 : Array Nat := #[
  0xa1,
  0x3724,
  0xbd,
  0xc1,
  0xd1,
  0x40308e,
  0x109a,
  0x430092,
  0x1052,
  0x103a,
  0x108a,
  0x106a,
  0x1056,
  0x3980,
  0x3a80,
  0x111
]

def labelsBlock19 : Array Nat := #[
  0x119,
  0x11d,
  0x121,
  0x3c80,
  0x14d,
  0x151,
  0x159,
  0x171,
  0x179,
  0x18d,
  0x191,
  0x1ad,
  0x1082,
  0x1076,
  0x1062,
  0x443108320f6
]

def labelsBlock20 : Array Nat := #[
  0x4430fe,
  0x6430c2,
  0x1d5,
  0x1d9,
  0x4340c2,
  0x1e1,
  0x10ba,
  0x3700,
  0x3708,
  0x3710,
  0x2e00,
  0x2d20,
  0x2b00,
  0x1b38,
  0x1d38,
  0x1f30
]

def labelsBlock21 : Array Nat := #[
  0x3ba0,
  0x3da0,
  0x9,
  0xd,
  0x11,
  0x15,
  0x19,
  0x1d,
  0x21,
  0x25,
  0x29,
  0x2d,
  0x31,
  0x35,
  0x3d,
  0x1f68
]

def labelsBlock22 : Array Nat := #[
  0x1f2c,
  0x4d,
  0x1bc0,
  0x1dc0,
  0x1ec0,
  0x3730,
  0x45,
  0x49,
  0x1fd4,
  0x79,
  0x71,
  0x75,
  0x95,
  0x99,
  0x1fd8,
  0xb1
]

def labelsBlock23 : Array Nat := #[
  0xa9,
  0xad,
  0xc9,
  0xcd,
  0xd9,
  0xdd,
  0x6d,
  0x91,
  0xa5,
  0xc5,
  0xd5,
  0xe1,
  0x730086,
  0xed,
  0x70308e,
  0xf5
]

def labelsBlock24 : Array Nat := #[
  0x43009a,
  0x630096,
  0xfd,
  0x43008e,
  0xf1,
  0xf9,
  0x101,
  0x1066,
  0x109e,
  0x3c8c,
  0x1b10,
  0x3b70,
  0x3c1c,
  0x1b80,
  0x1d68,
  0x1e14
]

def labelsBlock25 : Array Nat := #[
  0x1b14,
  0x3968,
  0x125,
  0x129,
  0x135,
  0x139,
  0x131,
  0x141,
  0x3a1c,
  0x1d80,
  0x1e0c,
  0x1d0c,
  0x3970,
  0x15d,
  0x161,
  0x155
]

def labelsBlock26 : Array Nat := #[
  0x169,
  0x3a0c,
  0x390c,
  0x3c14,
  0x175,
  0x17d,
  0x391c,
  0x1e80,
  0x3a70,
  0x195,
  0x199,
  0x185,
  0x1a1,
  0x1a9,
  0x1b1,
  0x1b9
]

def labelsBlock27 : Array Nat := #[
  0x1bd,
  0x145,
  0x16d,
  0x181,
  0x1a5,
  0x1b5,
  0x1c1,
  0x4340fa,
  0x10b6,
  0x10c6,
  0x10ea,
  0x10f2,
  0x10be,
  0x1dd,
  0x1e5,
  0x1e9
]

def labelsBlock28 : Array Nat := #[
  0x1,
  0x5,
  0x101a,
  0x101e,
  0x39,
  0xe5,
  0x2e08,
  0x2e10,
  0x105,
  0x109,
  0x1c5,
  0x3c20,
  0x3a20,
  0x1c9,
  0x3c40,
  0x3a40
]

def labelsBlock29 : Array Nat := #[
  0x3940,
  0x3740,
  0x3744,
  0x3748,
  0x3750,
  0x1cd,
  0x2d00,
  0x1ed
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
    if i < 352 then
      if i < 288 then
        if i < 256 then
          labelsBlock15.getD (i-240) 3
        else
          if i < 272 then
            labelsBlock16.getD (i-256) 3
          else
            labelsBlock17.getD (i-272) 3
      else
        if i < 320 then
          if i < 304 then
            labelsBlock18.getD (i-288) 3
          else
            labelsBlock19.getD (i-304) 3
        else
          if i < 336 then
            labelsBlock20.getD (i-320) 3
          else
            labelsBlock21.getD (i-336) 3
    else
      if i < 416 then
        if i < 384 then
          if i < 368 then
            labelsBlock22.getD (i-352) 3
          else
            labelsBlock23.getD (i-368) 3
        else
          if i < 400 then
            labelsBlock24.getD (i-384) 3
          else
            labelsBlock25.getD (i-400) 3
      else
        if i < 448 then
          if i < 432 then
            labelsBlock26.getD (i-416) 3
          else
            labelsBlock27.getD (i-432) 3
        else
          if i < 464 then
            labelsBlock28.getD (i-448) 3
          else
            labelsBlock29.getD (i-464) 3

def decodeHints (enc i : Nat) := labelsGet ((enc >>> (i * 9)) % 512)

def localHints (stride dict enc i : Nat) : Nat :=
  let q := (enc >>> (stride*i)) % (2^stride)
  labelsGet ((dict >>> (9*q)) % 512)

def viewsBlock0 : Array View := #[
  ⟨0xff000000,⟨24,by decide⟩,0xe8000000,[ew2,ew7,ew12],3,decodeHints 0xe0008000e00840220e⟩,
  ⟨0x5500aa000000,⟨25,by decide⟩,0x4000a8000000,[ew23,ew25,ew26],3,decodeHints 0x0⟩,
  ⟨0xaa0000aa000000,⟨25,by decide⟩,0x800000a8000000,[ew31,ew33,ew35],3,decodeHints 0x0⟩,
  ⟨0xcc0000cc000000,⟨26,by decide⟩,0x800000c8000000,[ew31,ew43,ew45],3,decodeHints 0x0⟩,
  ⟨0xa0050000a005000,⟨12,by decide⟩,0xa00400008000000,[ew69,ew73,ew76],3,decodeHints 0x0⟩,
  ⟨0x2200440022004400,⟨10,by decide⟩,0x2200400020000000,[ew97,ew101,ew104],3,decodeHints 0x0⟩,
  ⟨0x8080202080802020,⟨5,by decide⟩,0x8080200080000000,[ew145,ew150,ew151],3,decodeHints 0x0⟩,
  ⟨0x8080808080808080,⟨7,by decide⟩,0x8080800080000000,[ew149,ew150,ew157],3,decodeHints 0x0⟩,
  ⟨0x8200410082004100,⟨8,by decide⟩,0x8200400080000000,[ew148,ew159,ew160],3,decodeHints 0x0⟩,
  ⟨0x8800440022001100,⟨8,by decide⟩,0x8800400020000000,[ew147,ew166,ew168],3,decodeHints 0x0⟩,
  ⟨0xa00050000a000500,⟨8,by decide⟩,0xa000400008000000,[ew146,ew180,ew181],3,decodeHints 0x0⟩,
  ⟨0xff0000ff,⟨0,by decide⟩,0xe8000000,[ew3,ew8,ew13,ew19],4,decodeHints 0x37008000e00840220e020683e59119d91659⟩,
  ⟨0xff0000ff000000,⟨24,by decide⟩,0x800000e8000000,[ew36,ew46,ew53,ew60],5,localHints 3 0xe0830040000840220e 0xf60688d60688⟩,
  ⟨0x8888222288882222,⟨1,by decide⟩,0x8880200088000000,[ew152,ew167,ew173,ew174],4,decodeHints 0xe10b0160b0e0703e1f1c17164d1684243e1f⟩,
  ⟨0x8888888888888888,⟨3,by decide⟩,0x8880880088000000,[ew158,ew171,ew173,ew178],4,decodeHints 0xe1858160b0180c08040984c8442223480804⟩,
  ⟨0xaa005500aa005500,⟨8,by decide⟩,0xaa004000a8000000,[ew170,ew183,ew193,ew195],5,decodeHints 0xe20000200048bc742f09150aae3248bc742f⟩
]

def viewsBlock1 : Array View := #[
  ⟨0xff00ff00,⟨8,by decide⟩,0xe8000000,[ew4,ew9,ew14,ew19],4,decodeHints 0x0⟩,
  ⟨0xaa00aaaa00aa00,⟨9,by decide⟩,0x800000a8000000,[ew32,ew34,ew36,ew37],4,decodeHints 0x0⟩,
  ⟨0xcc00cccc00cc00,⟨10,by decide⟩,0x800000c8000000,[ew32,ew44,ew46,ew47],4,decodeHints 0x0⟩,
  ⟨0xf000f0f000f000,⟨12,by decide⟩,0x800000e0000000,[ew34,ew44,ew53,ew54],4,decodeHints 0x0⟩,
  ⟨0xa0a0a0a0a0a0a0a,⟨1,by decide⟩,0xa00080008000000,[ew71,ew75,ew77,ew78],4,decodeHints 0x0⟩,
  ⟨0xaa00aa00aa00aa0,⟨5,by decide⟩,0xa80080008000000,[ew72,ew75,ew80,ew81],5,decodeHints 0x0⟩,
  ⟨0xf00000f0f00000f,⟨0,by decide⟩,0xe00000008000000,[ew74,ew82,ew87,ew88],4,decodeHints 0x0⟩,
  ⟨0xf000f000f000f00,⟨8,by decide⟩,0xe00080008000000,[ew75,ew83,ew87,ew92],5,decodeHints 0x0⟩,
  ⟨0xff000000ff00000,⟨20,by decide⟩,0xe80000008000000,[ew80,ew85,ew87,ew96],5,decodeHints 0x0⟩,
  ⟨0x2222222222222222,⟨1,by decide⟩,0x2200200020000000,[ew99,ew103,ew105,ew106],4,decodeHints 0x0⟩,
  ⟨0x2288228822882288,⟨3,by decide⟩,0x2280200020000000,[ew100,ew103,ew108,ew109],5,decodeHints 0x0⟩,
  ⟨0x3300003333000033,⟨0,by decide⟩,0x3200000020000000,[ew102,ew111,ew116,ew117],4,decodeHints 0x0⟩,
  ⟨0x3300330033003300,⟨8,by decide⟩,0x3200200020000000,[ew103,ew112,ew116,ew121],5,decodeHints 0x0⟩,
  ⟨0x33cc000033cc0000,⟨18,by decide⟩,0x3280000020000000,[ew108,ew114,ew116,ew125],5,decodeHints 0x0⟩,
  ⟨0x5500005555000055,⟨0,by decide⟩,0x5400000040000000,[ew126,ew130,ew135,ew136],4,decodeHints 0x0⟩,
  ⟨0x5500550055005500,⟨8,by decide⟩,0x5400400040000000,[ew127,ew131,ew135,ew140],5,decodeHints 0x0⟩
]

def viewsBlock2 : Array View := #[
  ⟨0x55aa000055aa0000,⟨17,by decide⟩,0x5480000040000000,[ew129,ew133,ew135,ew144],5,decodeHints 0x0⟩,
  ⟨0x8282414182824141,⟨0,by decide⟩,0x8280400080000000,[ew156,ew161,ew163,ew164],5,decodeHints 0x0⟩,
  ⟨0x8282828282828282,⟨1,by decide⟩,0x8280800080000000,[ew158,ew162,ew163,ew165],5,decodeHints 0x0⟩,
  ⟨0x8888444422221111,⟨0,by decide⟩,0x8880400020000000,[ew155,ew169,ew172,ew176],5,decodeHints 0x0⟩,
  ⟨0x8888444488884444,⟨2,by decide⟩,0x8880400088000000,[ew156,ew170,ew173,ew176],4,decodeHints 0x0⟩,
  ⟨0xa0a050500a0a0505,⟨0,by decide⟩,0xa080400008000000,[ew154,ew182,ew185,ew188],5,decodeHints 0x0⟩,
  ⟨0xa0a05050a0a05050,⟨4,by decide⟩,0xa0804000a0000000,[ew156,ew183,ew186,ew188],4,decodeHints 0x0⟩,
  ⟨0xa0a0a0a0a0a0a0a0,⟨5,by decide⟩,0xa080a000a0000000,[ew158,ew184,ew186,ew190],4,decodeHints 0x0⟩,
  ⟨0xaaaa0000aaaa0000,⟨17,by decide⟩,0xaa800000a8000000,[ew173,ew186,ew193,ew202],5,decodeHints 0x0⟩,
  ⟨0xaaaaaaaa00000000,⟨33,by decide⟩,0xaa80a80000000000,[ew178,ew190,ew199,ew202],5,decodeHints 0x0⟩,
  ⟨0xcccc0000cccc0000,⟨18,by decide⟩,0xcc800000c8000000,[ew173,ew207,ew211,ew217],5,decodeHints 0x0⟩,
  ⟨0xf0f00000f0f00000,⟨20,by decide⟩,0xf0800000e0000000,[ew186,ew207,ew223,ew229],5,decodeHints 0x0⟩,
  ⟨0xff000000ff000000,⟨24,by decide⟩,0xfe000000e8000000,[ew193,ew211,ew223,ew238],5,decodeHints 0x0⟩,
  ⟨0xff00ff0000000000,⟨40,by decide⟩,0xfe00e80000000000,[ew199,ew214,ew226,ew238],5,decodeHints 0x0⟩,
  ⟨0xffff000000000000,⟨48,by decide⟩,0xfe80000000000000,[ew202,ew217,ew229,ew238],5,decodeHints 0x0⟩,
  ⟨0xffffffff,⟨0,by decide⟩,0xe8000000,[ew5,ew10,ew15,ew20,ew21],5,decodeHints 0x13808000e00840220e0598c82ad21b95c8ad01824382f0f0e9422f020683e59119d91659⟩
]

def viewsBlock3 : Array View := #[
  ⟨0xff00ffff00ff00,⟨8,by decide⟩,0x800000e8000000,[ew41,ew51,ew58,ew62,ew63],7,localHints 4 0x71418020000420110700c121c0f0e9422f 0xecb7a98765403210dcb7a98765403210⟩,
  ⟨0xaaaa5555aaaa5555,⟨0,by decide⟩,0xaa804000a8000000,[ew177,ew189,ew198,ew203,ew204],7,decodeHints 0xe40000200059048641048bc742f0d164ec5909150aae343f1f8d4a44526914758964ec59⟩,
  ⟨0xaaaaaaaaaaaaaaaa,⟨1,by decide⟩,0xaa80a800a8000000,[ew179,ew191,ew201,ew203,ew205],7,decodeHints 0xe48000200059048641018703c1c0207c461f0996cb85b2133da2cf22341a5091307c461f⟩,
  ⟨0xff0000ffff0000ff,⟨0,by decide⟩,0xfe000000e8000000,[ew194,ew212,ew224,ew243,ew244],7,decodeHints 0xe5008000e00840220e020683e59119d91659029309a0e27040220e132c58059609d91659⟩,
  ⟨0xff00ff00ff00ff00,⟨8,by decide⟩,0xfe00e800e8000000,[ew201,ew216,ew228,ew243,ew251],7,decodeHints 0xe6808000e00840220e01824382f0f0e9422f0999cb6e62e52dc6e67f927982fe58e9422f⟩,
  ⟨0xffff0000ffff0000,⟨16,by decide⟩,0xfe800000e8000000,[ew203,ew218,ew230,ew243,ew253],7,decodeHints 0xea808000e00840220e0598c82ad21b95c8ad0c26535d44df4fa5d137f439eade7395c8ad⟩,
  ⟨0xffff0000ffff00,⟨8,by decide⟩,0x80e80000000000,[ew42,ew52,ew59,ew61,ew68],7,decodeHints 0x0⟩,
  ⟨0xf0f0f0f0f0f0f0f,⟨0,by decide⟩,0xe00080008000000,[ew79,ew84,ew93,ew94,ew95],7,decodeHints 0x0⟩,
  ⟨0x3333333333333333,⟨0,by decide⟩,0x3200200020000000,[ew107,ew113,ew122,ew123,ew124],7,decodeHints 0x0⟩,
  ⟨0x5555555555555555,⟨0,by decide⟩,0x5400400040000000,[ew128,ew132,ew141,ew142,ew143],7,decodeHints 0x0⟩,
  ⟨0xcccc3333cccc3333,⟨0,by decide⟩,0xcc802000c8000000,[ew175,ew209,ew213,ew218,ew219],7,decodeHints 0x0⟩,
  ⟨0xcccccccccccccccc,⟨2,by decide⟩,0xcc80c800c8000000,[ew179,ew210,ew216,ew218,ew220],7,decodeHints 0x0⟩,
  ⟨0xf0f00f0ff0f00f0f,⟨0,by decide⟩,0xf0800800e0000000,[ew187,ew208,ew225,ew230,ew231],7,decodeHints 0x0⟩,
  ⟨0xf0f0f0f0f0f0f0f0,⟨4,by decide⟩,0xf080e000e0000000,[ew191,ew210,ew228,ew230,ew232],7,decodeHints 0x0⟩,
  ⟨0xff00ff0000ff00ff,⟨0,by decide⟩,0xfe00e80000000000,[ew200,ew215,ew227,ew239,ew251],7,decodeHints 0x0⟩,
  ⟨0xffffffff00000000,⟨32,by decide⟩,0xfe80e80000000000,[ew205,ew220,ew232,ew251,ew253],7,decodeHints 0x0⟩
]

def viewsBlock4 : Array View := #[
  ⟨0xffffffffffffffff,⟨0,by decide⟩,0xfe80e800e8000000,[ew206,ew221,ew233,ew252,ew254,ew255],10,decodeHints 0xeb808000e00840220e0598c82ad21b95c8ad01824382f0f0e9422f020683e59119d916590999cb6e62e52dc6e6214019f4c68f5a954c22221a149695221347132c58059609d91659⟩
]

def viewsGet (i : Nat) : Option View :=
  if i < 32 then
    if i < 16 then
      viewsBlock0[(i-0)]?
    else
      viewsBlock1[(i-16)]?
  else
    if i < 48 then
      viewsBlock2[(i-32)]?
    else
      if i < 64 then
        viewsBlock3[(i-48)]?
      else
        viewsBlock4[(i-64)]?

def nodesBlock0 : Array Node := #[
  ⟨0,3,[ew2,ew7,ew12],localHints 4 0x11080040c0e010001007 0x258168155262367057066353024314322010⟩,
  ⟨12,5,[ew36,ew46,ew53,ew60],localHints 5 0x162986ca41508b54440c289b84810008181c02002801007 0x51e075518c5521351d8750d8354a105499150e0370ccf704ef704c670ce351184535295358b51124110e8100c8100e7110c410065110251106310020⟩,
  ⟨15,4,[ew148,ew170,ew183,ew193,ew195],localHints 4 0x491d0bc32d6090156e09128045c00 0xcc647672bb947670aa49028767654543210⟩,
  ⟨15,4,[ew170,ew183,ew192,ew193,ew195],localHints 4 0x92662ac280254090141219000945cd6 0xdd6576765c5cbb76a545998876545433210⟩,
  ⟨15,4,[ew22,ew170,ew183,ew193,ew195],localHints 4 0x492a8e8cc2f0c8480a09128045c00 0xcc57bb62aa7965608070230656544323210⟩,
  ⟨15,4,[ew101,ew170,ew183,ew193,ew195],localHints 4 0x42cab0aa69505e2e5c0142419048044a00 0x3e63dd52c3b3aa569387212656543212100⟩,
  ⟨15,4,[ew168,ew170,ew183,ew193,ew195],localHints 4 0x491d015ae2f0c84a1809128045c00 0xcca42a32bb740a988470230665454323210⟩,
  ⟨15,4,[ew170,ew183,ew193,ew195,ew196],localHints 4 0xb0b331547400090b9ae090cae04a01 0xd734434cb40110aa7099348876543432010⟩,
  ⟨15,4,[ew24,ew170,ew183,ew193,ew195],localHints 4 0x491d1505e66090143209128045c00 0xcc647672b24aa7099480210767654321010⟩,
  ⟨15,4,[ew73,ew170,ew183,ew193,ew195],localHints 4 0x434aa3a2a53e9c195c0940a1204804002e 0x8e58dd45c86bb41a8981761545433221010⟩,
  ⟨15,4,[ew170,ew181,ew183,ew193,ew195],localHints 4 0x496c0e8250e128145e090c8045c00 0xcc6426baa34998484720610554302100110⟩,
  ⟨15,4,[ew170,ew183,ew193,ew195,ew197],localHints 4 0xb0d33005b02e2a0485e090cae04a00 0xd643344cb4aa61934340880776055430210⟩,
  ⟨15,4,[ew2,ew170,ew183,ew193,ew195],localHints 4 0x492ad44a95033014240900894002e 0xc75bb53a337995181171321654432321010⟩,
  ⟨15,4,[ew26,ew170,ew183,ew193,ew195],localHints 4 0x248e80a2f0c848cc09128045c00 0xb942932aa74091088470230665432321010⟩,
  ⟨15,5,[ew170,ew183,ew193,ew195],localHints 5 0xaed70926688b60ab5bad566b03a8835ca957095580b55aa0bc130f0cb5aa62e12d480200 0xfa5bdf71fddf1adda5e9d05f9d0db9c0defb85a1b0cf4a8534984e798d29901f1911b1811ef701a06112a580ea40129410e730060310212906310020⟩,
  ⟨48,4,[ew41,ew51,ew58,ew62,ew64],decodeHints 0x1b65b20300830a6010f078140300054a4000e070060a088440c0001090a202048240614080400202070380007⟩
]

def nodesBlock1 : Array Node := #[
  ⟨48,5,[ew30,ew41,ew51,ew58,ew62,ew63],decodeHints 0x6612780c020c298043c1e0500c001529000381c018282211030000424288081209018502010008081c0e0001c4e0caf031b2036c80c2c010d8004402⟩,
  ⟨48,5,[ew29,ew41,ew51,ew58,ew62,ew63],localHints 5 0xc24f89d80a41c89090a2090a57c1c15060280601040000e02 0xb5a150799e453144888a102984f1880e6818c2ac0a081291050741cc5314841886208020⟩,
  ⟨48,5,[ew41,ew51,ew58,ew62,ew63,ew65],decodeHints 0x2a0c0500c060a019849e03008582c010083226010f07814030000036080406ca40801a00060a088440c0101008440703888a207018640614080400206038203607⟩,
  ⟨48,4,[ew41,ew51,ew57,ew62,ew63],decodeHints 0x185c9e0300830a6010f078140300054a4000e070060a088440c0001090a202048240614080400202070380007⟩,
  ⟨48,5,[ew0,ew41,ew51,ew58,ew62,ew63],decodeHints 0x6175800c0216298043c1e0500c1015578200680018282211030040e245701c0619018502010008180e080d81c180c01828060ab08049401000000402⟩,
  ⟨48,4,[ew32,ew34,ew44,ew62,ew63],decodeHints 0x19849e0308832c81150a84280308032c6101d0e8140308044661007056c40e178bc060a07044660e07040760e⟩,
  ⟨48,5,[ew32,ew34,ew51,ew58,ew62,ew63],decodeHints 0x19849e0303030f8062b95c140304054180801a00060a088440ce7038315c070c80c1403080400e081d81c0415288081209018280406250081c0e0101c7602⟩,
  ⟨48,4,[ew4,ew9,ew32,ew58,ew62],decodeHints 0xf078140301d94060a5cae5d00101a00060a088440c01000004e08018640614080400206010084e07038206607⟩,
  ⟨48,5,[ew4,ew32,ew51,ew58,ew62,ew63],decodeHints 0x185db40300858f8010f0781403043a55e0801a00060a088440c0113890442401828060a8a0042c01000001807018640614080400206038207607010084e07⟩,
  ⟨48,5,[ew32,ew41,ew44,ew58,ew62,ew63],decodeHints 0x19849e0300830a6010f0781403040315e084000c2803088440e240601c061901850201000b9c0e081981c001529000381c018280001250000008198001c0e⟩,
  ⟨48,5,[ew9,ew32,ew41,ew58,ew62,ew63],decodeHints 0x185d600300858a6010f078140303ba55c0701864061408040020613854361501828060a8a8042c0101008180801a00060a088440c010401c6607000004e08⟩,
  ⟨48,6,[ew32,ew41,ew51,ew58,ew62,ew63],localHints 6 0x3085c9e530f46500118c45c48190a0422c0675d9c18270a80d020ab31282cea0082000331d8c00e02 0xe44e88d8e246138d3873c72514493e01d11cd31f1ce7c730c34e38644678f3c345118f18d38e18c74638e34c30351c1877065146c71c144169964445105904d38e05760138e3575c41d60545811c75545011010c61841044114533cf4914503cf34e38230c08e38d30c2c924a1c72892481c7104142185103002040⟩,
  ⟨48,5,[ew28,ew41,ew51,ew58,ew62,ew63],localHints 5 0x1849e530f448485104850200c0a80c1406008000407 0xd28986880def2990741cc5315c320c2d6056b32929184010810741cc53148320c4208020⟩,
  ⟨48,5,[ew41,ew51,ew58,ew62,ew63,ew66],decodeHints 0x180c018281403019856003008042c0603058a6062b95c14030006c360000056d0000e070060a088440c000101c4402010895c02048240614010182c02070380008⟩,
  ⟨48,4,[ew41,ew50,ew58,ew62,ew63],decodeHints 0x185c9e0300830a6010f078140300054a4000e070060a088440c0001090a202048240614080400202070380007⟩,
  ⟨48,5,[ew1,ew41,ew51,ew58,ew62,ew63],decodeHints 0x6172780c0c0c3e018ae570500c001b29000381c0182822110300004242880812090185004060b0081c0e000202a0c0500c140300806d2001d8000e02⟩
]

def nodesBlock2 : Array Node := #[
  ⟨48,4,[ew4,ew14,ew34,ew51,ew62],decodeHints 0xe070060a8d46814035cae5b6002b95c1403088440c00008044e060482406140703800080136c4e02010186602⟩,
  ⟨48,5,[ew4,ew34,ew51,ew58,ew62,ew63],decodeHints 0x185db403033b0f8062b95c14030006d5e000e070060a088440c001389044240500c14030080636000d800a2020482406140101894020703800080101c4e02⟩,
  ⟨48,5,[ew34,ew41,ew44,ew51,ew62,ew63],decodeHints 0x19849e0300054a4000e070060a03030f8062b95c2803088440424288081209018501c0e0039c040619808020c298043c1e0500c02001d8000206198042010⟩,
  ⟨48,5,[ew14,ew34,ew41,ew51,ew62,ew63],decodeHints 0x185c9e030006ca4000e070060a013b0a202048240614070380008138302c0c0500c14038a8002c0003808f8062b95c1403088440c00030086602008044e06⟩,
  ⟨48,6,[ew34,ew41,ew51,ew58,ew62,ew63],localHints 6 0xc21727c78f85729070231d8e14448090a03a2c0876dac2a2706029040303006d43b0dba800332501c6002 0xc3cc90d9643e330d30b44b88f3c34612cf2cd3a02cc80b38e34c3053c51d14473df15114d31e14e78530c34e3852dd5037542cb15c1403c06d96443da01900d31801760030c3575c01000cb2c41041055805160051555144114533cf4914503cf34e38130c04e38d30c1042812ca2471c81452071c6145103081000⟩,
  ⟨48,5,[ew41,ew49,ew51,ew58,ew62,ew63],decodeHints 0x6175800c0216298043c1e0500c001529000381c01828000103000180c1205428030a00c0c01030041000038915c07018640614080400206070380007038880402⟩,
  ⟨48,5,[ew41,ew51,ew56,ew58,ew62,ew63],decodeHints 0x6172780c020c298043c1e0500c2a0c1203028030a00c0c010006ca4000e070060a00004100000020100001090a202048240614080400202010880e02070380008⟩,
  ⟨48,5,[ew4,ew9,ew41,ew51,ew58,ew62],localHints 5 0x1e743a4140011090061400818363b010306615 0x841a94b52d31cc74a128398e67bcae4b52d31cc76314b0a9284a0e6398052006310820⟩,
  ⟨48,5,[ew4,ew14,ew41,ew51,ew58,ew62],localHints 5 0x1c6dbb014011109006140b128000801054660c 0x6a5a98412d290854a1287bcee290a46a5a9630852154b0a9284a007300a42906300820⟩,
  ⟨48,6,[ew4,ew41,ew51,ew58,ew62,ew63],localHints 6 0x2eda90058f81e8f86d5e1c05046391719890180341852da4a00bb40d6c1d801d608138c04402 0x1049084f8614a040f40b48b79f79e49d2c32cf5dc2d070b5d73d040648669b69a49918318f4181976064103d75c625610b58424918b1830c30530434923d040138e05040f38e4cb2c124904b2d52494c61811040461941040d34424913d040238e09040f38e34b2cc24930b2ca2492061871041c61851040c3002040⟩,
  ⟨48,5,[ew27,ew41,ew51,ew58,ew62,ew63],localHints 5 0xc24f298782a520e028220c1200c2801030001002 0xd181888791ce5184d6096b329291890741cc53148320c411050741cc53148320c4110400⟩,
  ⟨48,5,[ew41,ew51,ew58,ew62,ew63,ew67],decodeHints 0x180c01850280301985b403008182c0100858f8010f07814030002036000006d5e000e070060a000042c0001088440201092dc02048240614080400202070380007⟩,
  ⟨48,4,[ew40,ew51,ew58,ew62,ew63],decodeHints 0x185c9e0300830a6010f078140300054a4000e070060a088440c0001090a202048240614080400202070380007⟩,
  ⟨48,5,[ew6,ew41,ew51,ew58,ew62,ew63],decodeHints 0x6172780c020c298043c1e0500c001529000381c0182800010b0000422288081209018502010008081c0e0001c480c0a00c2803030041000b78086602⟩,
  ⟨48,4,[ew9,ew14,ew41,ew44,ew62],decodeHints 0x90c8428030482406145cae598020f078140300b304e010804002020e070060a003304e00070380007000047600⟩,
  ⟨48,5,[ew9,ew41,ew44,ew58,ew62,ew63],decodeHints 0x185d600300bb8a6010f07814031385436150a00c280303004042257008120901850201000808051b0d808a4000e070060a000049400000204e00070380007⟩
]

def nodesBlock3 : Array Node := #[
  ⟨48,5,[ew14,ew41,ew44,ew51,ew62,ew63],decodeHints 0x185c9e03003b8a4000e070060a138302c0c0a00c2803040000422288081209018501c0e0001c05140b008a6010f0781403008007600008184e01080400202⟩,
  ⟨48,6,[ew41,ew44,ew51,ew58,ew62,ew63],localHints 6 0xc21727c8ca61e911482a1c053bee22703020600c28890120342050941000c74760e004600f7019889d402 0x1051090f96452340f40b74b89450d7612d42cf6e02d080b6db3d04075077dd74951e1dd1cf41c1db7074103db6c724734b2c924961249a5146524985143ce39541054e38f4102495d52cb24d5951c70140024920944c04803d044039101040f38e00b30534c14b2c02801472002480071c5185003002102083080040⟩,
  ⟨48,5,[ew39,ew41,ew51,ew58,ew62,ew63],decodeHints 0x6175800c0216298043c1e0500c1015578200680018282211030040424288081209018500206008081c0e01020180c0a89014030500c0206008183608000000e02⟩,
  ⟨48,5,[ew41,ew51,ew55,ew58,ew62,ew63],localHints 5 0x5c9e7c2b83002152907014110d82044510480c2806010380007 0xd6a9892a127369a12849a669a310c1e1738cd630810ad411a50339cc5190031800310820⟩,
  ⟨48,5,[ew9,ew14,ew41,ew51,ew58,ew62],localHints 4 0x663b812140086c060a0b128000203854760c 0x89899898ff7edd9c433434438989bb2a123434989807605543430210⟩,
  ⟨48,6,[ew9,ew41,ew51,ew58,ew62,ew63],localHints 6 0x2eb092058a61e9147c44ae0485021191d85418034282ae64a033bc02271806c017219809d607 0x1049084f8614a040f40948979f79e49d24824f39c25070938e3d04082081931884923d040638e19040f38e4cb2c624918b2db2490920996996526022023d05c259709040f5960895402d50092422c20060024c20860805002134474913d040738e1d040f38e34b2cc24930b2ca2492081471851020830000c2081000⟩,
  ⟨48,5,[ew38,ew41,ew51,ew58,ew62,ew63],localHints 5 0x5c9e7c2b86ca41c088642810038541824018282c06008001002 0xf6a9c89a127331c5288a10399ef209684acee3b58c5904112d2a4a0e6398a418c4110400⟩,
  ⟨48,5,[ew41,ew48,ew51,ew58,ew62,ew63],localHints 5 0x2e4f298790011040302a0a0b0180022288240614080040407 0xb5a144e98a52615ed73cb12b210789cd734ac2b162509290a0e1318a418c410042000420⟩,
  ⟨48,6,[ew14,ew41,ew51,ew58,ew62,ew63],localHints 6 0x2e4f9206ca41c91c804451048523c0e25054180a4300c4e300b006ea3b043bc01741981dda02 0xe44e84f86146038f38d34d2d32cd4513d040b38e2d040f38e15115e7de7917453453ce70541c14e38f41014b1474c71cb1c56c50110196996516003403ce5c059700e38f59600b0024c208b0805400855001d40051421c235348c4513d040c38e31040f38e34d28c2ca2471c81452071c61451020830000c2081000⟩,
  ⟨48,7,[ew41,ew51,ew58,ew62,ew63],localHints 6 0xc21727dec2c530f5e836520a8701411bcde0440c2889c4809018c0284a08006ee061d8386602005d81007 0x38f50f3a43a53a452338f38f48a6ca8a15143216e048a50a38e65f38a3df38a65938e3cf48350379d6db1dd51c4836c338e3da38365a3833cf38e6591c32183012981c12085c328348450459545115551348444438e3d03843503843cf38e34d14428b30020b14028a2442041400c61c40461440c3080040⟩,
  ⟨49,5,[ew153,ew177,ew189,ew198,ew203,ew204],decodeHints 0x924902824de6f0282c341a048e4020578804743a0c82486430e82c0005928005e2f048648241058740001780002412230248c091c82c720b128045c00⟩,
  ⟨49,5,[ew110,ew177,ew189,ew198,ew203,ew204],decodeHints 0x110880c0250e870902c341a048e4aa5509004743a0c82486430e82ca854090005e2f048648241058740001be0000a1233024cc095102d440b280044a01280005c00⟩,
  ⟨49,6,[ew156,ew177,ew189,ew198,ew203,ew204],localHints 6 0x110870c0688c3978c98744392b745e1920876fa62093c80a345baec12566e2e81625008b8a000 0x97e174f85d7df24f2453e071f81c3cf15f15c25e15d78524971d7033cf6cd35a3cf0cd0ca5190c96435142892464980c56034921851403cf5cd3563cf00d00a2550145402492945061530124c01451924800400430c104144f3d034d40f3ce34d28b2cc24930b2ca2491871c81452071c61450411010c3041081000⟩,
  ⟨49,5,[ew98,ew177,ew189,ew198,ew203,ew204],localHints 5 0x49378687255bf0bc82b8129400a120c8243a0b009885c00 0x29449a7349252346105a4e6398a429009781ce31dad2140c58149420e6398a42906310020⟩,
  ⟨49,6,[ew176,ew177,ew189,ew198,ew203,ew204],localHints 5 0x249bc34f1c00e8861617864821d783740a121a1197a092b0e5780bbf895e401310b8a000 0xc8fdcdfba31635888f949f2a314250a6750eea18c53944e10d189b6624486b688cd12d633198a6488c9294c21001807188c636b2e0b5c0c636d64a2a0a54084269401813212463008018e018c1ae73d8c7b9cd6312a52d085a949420e630484098c52106310400⟩,
  ⟨49,5,[ew70,ew177,ew189,ew198,ew203,ew204],localHints 5 0x493786873811d10ca8b8171400a1204864161d310940200 0x29449e73496523c429805ef31dce215ad5a4e6398a42918158549420e6398a42906110400⟩
]

def nodesBlock4 : Array Node := #[
  ⟨49,6,[ew177,ew188,ew189,ew198,ew203,ew204],localHints 5 0x124de1a1d10c2434232fcac395f1f44b83028bc12192082c361d7849c0382280b9e400 0xd7faf6f5def6d9aa7f693ed1ef54d546f157e29ada5e859164f7ca52b33656ecac659ad9a345568a844d4a94b237e6d7be1adc5ef66b674a554aad29352a5288ca5040027bc46101e0135c06380d6898c4a96042c0a5250801c0229446100a000c022084310020⟩,
  ⟨49,7,[ew177,ew189,ew198,ew203,ew204],localHints 6 0x110870c0688c393e9564d861d10c2c622a04b0a051782468192082cac1b0e941ba2e12e100200 0x34e7e135d4a135d7df34e48e24a4a025c7e025c49224a7ca25c39e24a75e24a38e25c75c6c149a6c341a64349260140134331734139734130c34338e2551d62412962411c725528a50049350441314449244040034438f34030f34038e34430c24828b2401cb24028a2481c71800c01840411440c3080040⟩,
  ⟨50,7,[ew179,ew191,ew201,ew203,ew205],localHints 6 0x44210600817149703c2cc410e585b099d4701c018d05a0ac3904172b0ecaa521b0b4a00200 0x38f7a039c4e039c79e38f4cf4894df49b79f49b4d348978939b3dd38971d3893cf39b71b48145a4984da4984514814d33983193813d938130c3983cf5c31d60812565411c75432494804d448d45448d4d348045138d3d03803103803cf38d30c14424a2c01ca2002492041c71800c01840411440c3080040⟩,
  ⟨51,4,[ew222,ew234,ew235,ew243,ew244],localHints 4 0x1307c8e0f0d260798b02e280989003340435 0xff7537c3ee5d7c71bb5a31397872565432301210⟩,
  ⟨51,5,[ew212,ew222,ew224,ew234,ew243,ew244],localHints 5 0x260d26046061022546071a8141e1f02034043c00bcc1000 0xa5147525459ccf21a9e38c4c780d4f530ee3b4ac2ac6c1ac0a48108398a00100310020⟩,
  ⟨51,4,[ew222,ew224,ew243,ew245,ew246],decodeHints 0x8003c0f87c080d0d0680821008000c000300402021188c1a0400020002a0101c042a02634098c00bd402f4⟩,
  ⟨51,5,[ew212,ew222,ew224,ew243,ew244,ew245],localHints 5 0x1e1a108984607154b546371580878057b07c080d008181000 0xaa2942ce52414431a86860e312155053d0b43cae2b46c1ad4002408380c62900310020⟩,
  ⟨51,5,[ew194,ew222,ew224,ew235,ew243,ew244],localHints 5 0x983e472c64002204528c10061a83c0a1a0263c004bc73cc0e02 0xb59272a545ad4f4626099ce47895304b4ef3b8ad2ad8d62d2a48108398a02900310020⟩,
  ⟨51,5,[ew194,ew222,ew224,ew243,ew244,ew246],decodeHints 0x28003e1f02034ba5d07810020003000020f1b8044623068100008000a81e31078a8092e0228c0237008c400020012c05917b008341a020840206008080e02⟩,
  ⟨51,4,[ew194,ew212,ew224,ew236,ew244],localHints 4 0x9840230f8341e050d0104206008080007 0xee8638d3cca61891bb6a13418982776534321210⟩,
  ⟨51,4,[ew18,ew194,ew212,ew224,ew243],localHints 4 0x305800d032c44204130049c00268080a4c 0xeec8dd8c35b3aa89056003408177656543432010⟩,
  ⟨51,5,[ew194,ew212,ew224,ew237,ew243,ew244],decodeHints 0x4c26028100b93028a80828026480205100044623068106e01000141e000f87c080d188000001030000a0f02808341a020845602008180202000080007⟩,
  ⟨51,5,[ew86,ew194,ew212,ew224,ew243,ew244],localHints 5 0x262707c220f0d0842005100101a01000200407 0x210419ef3a0a62986860dce315ad10d0c4056b32929004611810741cc5314841886208020⟩,
  ⟨51,4,[ew91,ew194,ew212,ew243,ew244],localHints 4 0x3041e8b3b0840a4e020344600088080210 0xee8738d3cc760890bb7a03401898765543432010⟩,
  ⟨51,4,[ew194,ew212,ew224,ew240,ew244],localHints 4 0x986e230f8341e050d010420600808002b 0xee8638d3cca61891bb6a13418982776534321210⟩,
  ⟨51,5,[ew194,ew212,ew224,ew243,ew244,ew247],decodeHints 0x4005140100995130980a04ca0040235008146e011188c1a04040000005078003e1f020340001030000e020283c0a020d068082100818020200008002b⟩
]

def nodesBlock5 : Array Node := #[
  ⟨51,5,[ew11,ew194,ew212,ew224,ew243,ew244],localHints 5 0x1844e1008c9a1f069303421030140847008dc10001881c042b 0x1359a69499e527a631192104bc87591ce005ad4b0eb384812014a4a128398e62148308820⟩,
  ⟨51,6,[ew194,ew212,ew222,ew224,ew243,ew244],localHints 6 0x4c472708f2ef81508147967b8d46f320f8366208980141e1a02230432f008180e280012c043c 0xb3a180a86038e2ca2c769f54e7d569a1ce1ca49e1cb78749228b2db38e75a69c38e6da68a2cb1196442cb2996561c76155571c759554334300e39434d0ce0ca2d30d24c32cb2924831830071d11860c70c20100c40c138e08d34f38e04d04a2cc0493012cb2892411c70861881c70460400050440400c3042040000⟩,
  ⟨51,4,[ew212,ew234,ew243,ew245,ew248],decodeHints 0x83c02351188c1a0444810082100818022a010080e2a0266409980000410000400000070f87c080d7a80000f9⟩,
  ⟨51,5,[ew212,ew224,ew234,ew243,ew244,ew245],localHints 5 0x1e8910898042a96a606afa118180e050f8101a31158041000 0xaa28634e5241a314c103440cf33922134486096b29942080090208039cc52000300820⟩,
  ⟨51,5,[ew194,ew212,ew234,ew235,ew243,ew244],localHints 5 0x4c2323961308acd80010061e0141e8902668024b01335e607 0xad5472a925a50f35254c948f12b0ab4a92a3c0ef7398d62d49524e8398a02906310820⟩,
  ⟨51,5,[ew115,ew194,ew212,ew224,ew243,ew244],localHints 5 0x261008c9a110d0841c05078340801030000e02 0x21041488791ce315ad3a0a62998c191074016b2a883201290050741cc53148320c4208020⟩,
  ⟨51,5,[ew194,ew212,ew234,ew243,ew244,ew248],decodeHints 0x280446230681008c2100100206008a84037100a80933022600001040000020188003e1f020346200000c402070092c0f9c7d01c0889020840402000200007⟩,
  ⟨51,4,[ew120,ew194,ew224,ew243,ew244],localHints 4 0x300408b2c8840a4d068103e010881c000e 0xee8638d3cc760890bb6a03401898765513432010⟩,
  ⟨51,4,[ew194,ew212,ew224,ew241,ew244],localHints 4 0x9846310f83440050d0104201158200007 0xee864894dda618c1bb6a14218980776540431210⟩,
  ⟨51,5,[ew194,ew212,ew224,ew243,ew244,ew249],decodeHints 0x1e0514010099e130980a04030040205100044623068133a00000f00005188003e1f020340001040000402028800a070222408210081c022b000200007⟩,
  ⟨51,5,[ew16,ew194,ew212,ew224,ew243,ew244],localHints 5 0xba4e119343e0d2603d1221040140847030046e00188080e2b 0x2b57269429a7382652712314c086591ef0392d4b0c13008b2054a4a12831cc520c8310820⟩,
  ⟨51,6,[ew194,ew212,ew224,ew234,ew243,ew244],localHints 6 0x4c47d03ec54989b08046062687c1b9f7b8f063359a0141e89022344228010046a4b978001007 0xb3a180a86038e2ca2dd38e7cd35e38e74d34a2cb21c7082cb29c70668614e39b69a18e18a55918b64655528b2c415818818235744e5d134d08e08a2d60955822cb2955515110920824c245244214204618140108608038e10d34f38e00d34a2cb0093002cb2892451470081c51860040051450020840410c2080040⟩,
  ⟨51,5,[ew194,ew212,ew224,ew243,ew245,ew246],localHints 5 0x1317446001883c780dd10149602108134201033d1ec2b 0x5394d9cccc948c722864190838c586841cf734cc32c64191405250831cc520c8310820⟩,
  ⟨51,5,[ew118,ew194,ew212,ew224,ew243,ew244],localHints 5 0x130dc464d450443421070200a0f0681002060001c5602 0x273498a99163139a10424cf31dce21528481ad330a42816b029284a0e6398a42906310020⟩,
  ⟨51,5,[ew194,ew212,ew224,ew243,ew245,ew248],localHints 5 0x789984011b8806a1f0681496021081346f97d0ac0008 0x54d4d94966898c7841cf735665982a004010818c32c20005425250831cc52106208020⟩,
  ⟨51,5,[ew89,ew194,ew212,ew224,ew243,ew244],localHints 5 0x2627160621f08a2442100303c0a20020340200040085607 0x29449e734265231c8989210399ef59128480ee3b58c02c832012a4a0e6398a520c8310820⟩
]

def nodesBlock6 : Array Node := #[
  ⟨51,6,[ew194,ew212,ew224,ew243,ew244,ew245],localHints 5 0x78988fa57d8d6703711e91f03c9b8c43e0d088a00405150111c219a0040c4b980005608 0x45fd8e621c85254a729094299eea7dd6314951785368c6d98ba29966c3198ce0cc3261732ae68412a502c015042a881400962931929c84c125511422252930808af019e02944612d6d0b9ab630240ad6b4a9414202a52508098c4294e6304a5088440006210400⟩,
  ⟨51,5,[ew134,ew194,ew212,ew224,ew243,ew244],localHints 5 0x261008c3e0d260401c0f028840806008200002 0x2103946778dce61427405ad2b0232056b3a0a62994a191290890741cc53148320c4110400⟩,
  ⟨51,4,[ew194,ew235,ew243,ew246,ew248],decodeHints 0x28140c352c1601a0445010080d008040c2a00000102a0269c09a6010180e020380804070d06808217a80804fc⟩,
  ⟨51,5,[ew194,ew224,ew235,ew243,ew244,ew246],localHints 5 0xa8a2e800622a9711c10357e9601a01078680821158180e02 0xad6852a673396526c0f13c0af2b9a2130475894a495080800101c60318a41800300820⟩,
  ⟨51,5,[ew194,ew212,ew235,ew243,ew244,ew248],decodeHints 0x2814b0580681008c2100100201030a84037100a809330211c0c08030f011a87e820088a020340000010180e020108056020d068082115808042b038080407⟩,
  ⟨51,4,[ew139,ew212,ew224,ew243,ew244],localHints 4 0x2c440762c8341e4c1081034060801c040e 0xee8638d3cca60890bb6a03401898765513432010⟩,
  ⟨51,4,[ew194,ew212,ew224,ew242,ew244],localHints 4 0x9846200f8341031078ac3404108180407 0xee7427c2dda47c79bb4a29281761554312010110⟩,
  ⟨51,5,[ew194,ew212,ew224,ew243,ew244,ew250],decodeHints 0xa051401009aa2e9741e04008040c0f10018b058068100000078801e0802228080d030200c31d4808044b0103c56020d0680821010180e02038080407⟩,
  ⟨51,5,[ew17,ew194,ew212,ew224,ew243,ew244],localHints 5 0x4c4e2c135140d260684207078140847008186e00040c4042b 0x2b5526942aa7382652129314c0c3309ef505ce4b426605810b16a4a12839cc52106208020⟩,
  ⟨51,6,[ew194,ew212,ew224,ew235,ew243,ew244],localHints 6 0x26d63f854479d080b0019ca281a28001300a0f0d0111e21d5bdc962b1acd40c3c988081007 0xe46070d81c45138d39d4107d145e41075144d38e51c71438e35c7056851d145b69a15144d55914e64555534e3841d815460141011145741005144d38e05558138e3555471d30544c71450440471c709148841221144240234e3c230f08e38d30c20b20224208a088248087080145006002142004002042083080040⟩,
  ⟨51,5,[ew137,ew194,ew212,ew224,ew243,ew244],localHints 5 0x130dc461f0693112100701c1e05108100c01040c40002 0x2734188891231798284861033c24285ce424cd31d8c2156b0a9284a0e6398a42906110400⟩,
  ⟨51,5,[ew194,ew212,ew224,ew243,ew246,ew248],localHints 5 0x14bac2008dc40351e0001afc7e8c41e1a020840407 0x948ac8c52380c697bdae6b12348ca62ad4a1a469420e60940100420210620800100420⟩,
  ⟨51,5,[ew90,ew194,ew212,ew224,ew243,ew244],localHints 5 0x5d2708d14111586842100283c4004068180200188200407 0x29452273496523a1495091141e101142a785ce4358c284010816b5250741cc52106208020⟩,
  ⟨51,6,[ew194,ew212,ew224,ew243,ew244,ew246],localHints 5 0x29748fae7f0d67637118a0000d9ceb5f04b154dc560f0d0112021080040c3c990086207 0x47fd96fd2d45254ab2a89a299eea7dd6314951b862e8a5d94da319e6c3198ce0cc3269732ae6a512a53df50daaf630240bdef4a941a502a52694094a431a65284c604802808511020013c4d631ae689824a96242c4a52508118e029c06308a2010020884310020⟩,
  ⟨51,5,[ew138,ew194,ew212,ew224,ew243,ew244],localHints 5 0x26118c43e0d26068200e078800a21020186e01040000e02 0x29449c895127381c4990a313c044189ef481ce3a1ad2018c10d695250741cc42906218820⟩,
  ⟨51,5,[ew119,ew194,ew212,ew224,ew243,ew244],localHints 5 0x5d2c1343e1115868420e028801e0d020046e06040000e02 0x29449c895127341e5248a313a21020809781ce3b4040818c1056b5250741cc62906208020⟩
]

def nodesBlock7 : Array Node := #[
  ⟨51,6,[ew194,ew212,ew224,ew243,ew244,ew248],localHints 5 0x2b088e2800ec1fc3c9d8c43e0d9d6bdf64b154e056200d01122211acd86e0e010001007 0x77fd9cfab8aa2694e51495298aea7dd6314953dfb2f36f630a72bdef4d285528b4a254a16841c043908b0213c56632d7b09824aaa2a544a5269411c4128433088a21c8608001100e031bc6d631ae68d834a96342c6a5250819c602800600ca3008830906210020⟩,
  ⟨51,7,[ew194,ew212,ew224,ew243,ew244],localHints 6 0x262393b6c371008c9bb51887c1a11da133662b028a81e1a020a04210d90046a062583b6202000f01007 0x38f4e43a33a43a34d338f38f48a7e22604e28607df48a4ca38e65e38a3de38a65938e3cf48345d09b4dd71b4514834c338e3da38365a3833cf38e6592432180812985c12082432834844d61d44565544d348444438e3d03843503843cf38e34d24428c1c020c2c028a2442040800c61c40461440c3080040⟩,
  ⟨52,7,[ew201,ew216,ew228,ew243,ew251],localHints 5 0x3fd8605141703c2c2d8e0382d05044ce130902406a4190502001300181c02001dc1007 0xdb79edf61edf79cdb60d3a2da3e21a3e2d63a2103e2793a1b93a2733e1ad10e17152d71521010ed6151b510e7510dad1527338cd238512384c638d036121162df162e10611ef62dae6114e611ad62d4a39109380c938108390c410065110251106310020⟩,
  ⟨53,7,[ew203,ew218,ew230,ew243,ew253],localHints 6 0x506f510c136c421cf82c9a029067a1b0e84524990c03cc60b9e088bc10008181c02000d01007 0x84c5e085f3e079f5d778c3cc7073dd7195dd7193cf7075c77194db70731b6874d369930c4433d84545d84543cf4435c34543164434d654330c5544d34431924411d24411864431c30843d008a39008a3cf08438408a30d08424d2c430c2ca2490841c80801880801c70841840800c50840450840c3080040⟩,
  ⟨64,7,[ew206,ew221,ew233,ew243,ew251,ew253],localHints 6 0x1eb80803f0634da53f0b1a1a22316340367167ac83e2d06846028811110f100211150e1a021c06421080058a066f839bc02003381007 0x4934934925964af4ae49359348f48f4925964adb2b48f58f48f48f4924d34923aa48f4cfa0a5a92679a9a2759624a98a48a7a54a34e54a379e48a4d33a36e438a3e438a6db3a33cf6435a20a18226615960838034834df49c79f49c4d348379e39c3dd3836dd3833cf39c6db24321a08129a6412082432831445981d75581575961c45444844d448d45448d4d348445138d3d03843103843cf38d30c24428b1c020b14028a2442040800c61c40461440c3080040⟩,
  ⟨64,8,[ew206,ew221,ew233,ew243,ew251,ew254,ew255],localHints 6 0x141225014b07db909c0e20634c08c74dc19c305218b1350481990822d0e845a8990c1182f02148fc726305968645e08004d0063c0398c02001c41007 0x38e5f3d15d33c555d7c72c704af4ae4935ee4934934925554a84ad49355348f48f4925d73ac3ab48f5cf3aa3a948f56948f48f4924d34923a848f4cf94a5e72622679625d724a24a96256624a24a94a54a26226248a78a4a24e44a279e48a4ca3a26e338a3e338a6db3a23cf6435e109c0a165c5d708308365c56008308364354309c09c4834c349c79f49c4d348378339c3dd3836dd3833cf39c6db24321a08129a6412082432831445d81cd1d814d5d71c41c414d5561c41c41445441cd1cd4844c448d45448d4d348444438d3d03843103843cf38d30c24428b1c020b14028a2442040800c61c40461440c3080040⟩,
  ⟨64,8,[ew206,ew221,ew233,ew243,ew252,ew253,ew255],localHints 6 0x241121042a041d8ee03517c6cd3021720c6982b202c1e1616c71043940c36640e0b414115999c26122305cf302148887209018f46414080052606538394c02002701007 0xefbefa39667a38e678e53e78c93659cb7cb639339338e596cb2d7439359338f38f38e6593b33b338f64f38f38f38e5963b23b138f58f3b03af38f4efa8a96e26766eaa796524a659a8a58a269b2daa959624ab0aaa982b24a4caa8a80a2694d33a776838a3e838a75d3a73cf6c366609e9666de6590839656c35830a18e46e15960838c36e14e20838036c34c30a182039e3df38375f3833cf39e75d24321c08129c6c120824328314465a1cd61a14d6591c46181445841d25571525961c45441524d41c44441444c41d245138d3d03843103843cf38d30c24428b1c020b14028a2442040800c61c40461440c3080040⟩,
  ⟨64,9,[ew206,ew221,ew233,ew243,ew252,ew254,ew255],localHints 6 0x1109143211968418700a0d40501b1c6c0b2e41a0ac90b1ad3a2c2d8e209030d990e694168456867098488c17810a444393d1f87c3208004d2063c8395002001c81007 0xe79d3ae545fae54d34e785d7db65f7d92d37d925d7db5d3435235234d51434d373372c3034d5d7371c3036d5d736e36f36d52f36e36c36d4aca0a8ab2645eba248a224a5d7a2452a24a24aa0a50a264264a277a924a48aa0a78a26749236436434a98a34a94a3643646435e309b8a365b5d70838a265b52108308364350309b09b65f4a008378364348309f79e35b35b34374334370335b35b24321a08129a6412082432831445d81cc59814c5d71c459614c5151c41c41445041cc1cc1514931c44041444841d141034c34c3443c434438434c34c24428b1c020b14028a2442040800c61c40461440c3080040⟩,
  ⟨64,8,[ew206,ew221,ew233,ew251,ew252,ew253,ew254],localHints 6 0x6a22511a60452c1dc40c2417c7d0821079366c21b282c5c16070149a3a104361d2d8b470115a82406144c860f66305888bc671904c8012080052a06550395202002781007 0xdf7f3b35667beba678e53e78c93659cb7cb635335334d596cb2d7435359334e34e34d65937337334e65934e34e34d59637237134e58e37036f34e4efaa796e24a66ea8a965267659a8a5ad269b2daa959624ab0aaa982b24a4eba8a8202694d334a7683673a836775d34a38e6de6660839666c365909e9656c35a40a18e46e15960838c36e14e20838226c34d30a182034339f35e75f35e38e34375d24321c08129c6c120824328314f65a1c461a1446591cf6181445971d25571525961c45441524d41c44541444d31d245134439034f31034f38e34430c24428b1c020b14028a2442040800c61c40461440c3080040⟩,
  ⟨64,9,[ew206,ew221,ew233,ew251,ew252,ew254,ew255],localHints 6 0x1114a6aa28300865a105c27b82430dc4294d87886cb0b1ad3a2c4d07014410d874e694168456c990c02406143182c445e3d1f8643608004d8063d8395602001d01007 0xe555fae32e3ae725d7e15dd531231230c5d730c336d34575d12cb5d12555d33cb232d33130c5f1330bae30c55532fbae30c55532d32c30c492a0a5eb26426ba245d724a24aa2486a24a56aa0a861264555a277a924a4a9a0a79e26749230a30a3249a432496430a30a6435e309b0a365b5d708308365b56208386264355509b86165f4a00837a064349209f79e30330331b75b31b71b30330324321a08129a6412082432831445d81cd1d814d5d71c41c414d5561c45161445551cd5141514931c44131444921d141030430430d3cd30d38d30430424428b1c020b14028a2442040800c61c40461440c3080040⟩,
  ⟨64,9,[ew206,ew221,ew233,ew252,ew253,ew254,ew255],localHints 6 0xc05c846aa2810914314b1e8c5f32a8b78362e07859bb4e9ac86ac0b16c701c1682b749439904361d08a7cce130902406320a6e4fc7a3182c445e08004da064b8392c02001fc1007 0xe55e55e7c618e79e79e79e7f270618e79f3e270555d0e63df37f3dd37618f0eeced3757ae4ee7ad0e555e77e37d0ed8ed72d72d32cf2c4ec0ea0a96f26d62fa2d96524a618a2d8ae24a56ea0a8a226d555a0ab0a267aa7a27ae724aa8aa2772924a3a9a0a71c26738e6836260a39666a36180839656a35640838a46835550a38a268384309d7dd69d81d0837c369d39e08371e68338e09d71c24321b08129b6812082432831446191d45d91546181c45d71545561c44d61445551d44d31444841cd40d14d44d1c440414d38f1c430f14438e1cd30c24428b1c020b14028a2442040800c61c40461440c3080040⟩,
  ⟨64,10,[ew206,ew221,ew233,ew252,ew254,ew255],localHints 6 0x1137e6a216f83048021977a17149703c2c21a742c5b1c0705a0a2086c3a114a19c26120480c64143182c445e08004d6063d038fc02001cc1007 0xb12b72c28572b28b6dc52552a8e56fc27b6faa7555b8eb4eaa74abb0ea2ba8e492a67a2788a7e62645668a47df24a5558a472524a4a588a71c2644928a166324a3a388a65926138e5c356009d7e05dd5550837df5dd49e08371e5c349209d71c5da39b08365b5c338e09a6592432180812985c12082432831445561d15161515551c45141514931c44131444921d141014d38f1c430f14438e1cd30c24428b1c020b14028a2442040800c61c40461440c3080040⟩
]

def nodesGet (i : Nat) : Option Node :=
  if i < 64 then
    if i < 32 then
      if i < 16 then
        nodesBlock0[(i-0)]?
      else
        nodesBlock1[(i-16)]?
    else
      if i < 48 then
        nodesBlock2[(i-32)]?
      else
        nodesBlock3[(i-48)]?
  else
    if i < 96 then
      if i < 80 then
        nodesBlock4[(i-64)]?
      else
        nodesBlock5[(i-80)]?
    else
      if i < 112 then
        nodesBlock6[(i-96)]?
      else
        nodesBlock7[(i-112)]?

def fastViews : QFast.Table View := ⟨65,viewsGet⟩

def fastNodes : QFast.Table Node := ⟨124,nodesGet⟩

end SignedProjection


namespace SignedProjection
def aliasMap1 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63]
def aliasMap2 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,31,30,29,28,27,26,25,24,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,63,62,61,60,59,58,57,56,0,0,0,0,0,0,0,0]
def aliasMap3 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,31,30,27,26,55,54,51,50,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap4 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,31,29,27,25,55,53,51,49,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap5 : Array Nat := #[0,0,0,0,0,0,0,0,20,0,21,0,22,0,23,0,0,0,0,0,0,0,0,0,0,28,0,29,0,30,0,31,0,0,0,0,0,0,0,0,52,0,53,0,54,0,55,0,0,0,0,0,0,0,0,0,0,60,0,61,0,62,0,63]
def aliasMap6 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,8,10,25,27,44,46,61,63,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap7 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,8,12,25,29,42,46,59,63,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap8 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,8,14,25,31,40,46,57,63,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap9 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,10,14,25,29,42,46,57,61,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap10 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,12,14,25,27,44,46,57,59,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap11 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,31,29,27,25,46,44,42,40,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap12 : Array Nat := #[0,0,0,0,0,0,0,0,18,0,19,0,22,0,23,0,0,0,0,0,0,0,0,0,0,26,0,27,0,30,0,31,0,0,0,0,0,0,0,0,50,0,51,0,54,0,55,0,0,0,0,0,0,0,0,0,0,58,0,59,0,62,0,63]
def aliasMap13 : Array Nat := #[0,0,0,0,0,0,0,0,17,0,19,0,21,0,23,0,0,0,0,0,0,0,0,0,0,25,0,27,0,29,0,31,0,0,0,0,0,0,0,0,49,0,51,0,53,0,55,0,0,0,0,0,0,0,0,0,0,57,0,59,0,61,0,63]
def aliasMap14 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,49,51,53,55,56,58,60,62,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,17,19,21,23,24,26,28,30,0,0,0,0,0,0,0,0]
def aliasMap15 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,50,51,54,55,56,57,60,61,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,18,19,22,23,24,25,28,29,0,0,0,0,0,0,0,0]
def aliasMap16 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,52,53,54,55,56,57,58,59,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,20,21,22,23,24,25,26,27,0,0,0,0,0,0,0,0]
def aliasMap17 : Array Nat := #[0,0,0,0,0,0,0,0,63,0,62,0,61,0,60,0,0,0,0,0,0,0,0,0,0,55,0,54,0,53,0,52,0,0,0,0,0,0,0,0,59,0,58,0,57,0,56,0,0,0,0,0,0,0,0,0,0,51,0,50,0,49,0,48]
def aliasMap18 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,40,42,44,46,56,58,60,62,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,8,10,12,14,24,26,28,30,0,0,0,0,0,0,0,0]
def aliasMap19 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,40,41,44,45,56,57,60,61,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,8,9,12,13,24,25,28,29,0,0,0,0,0,0,0,0]
def aliasMap20 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,40,41,42,43,56,57,58,59,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,8,9,10,11,24,25,26,27,0,0,0,0,0,0,0,0]
def aliasMap21 : Array Nat := #[0,1,2,3,4,5,6,7,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,40,41,42,43,44,45,46,47,16,17,18,19,20,21,22,23,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,56,57,58,59,60,61,62,63]
def aliasMap22 : Array Nat := #[0,2,4,6,32,34,36,38,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,24,26,28,30,56,58,60,62,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap23 : Array Nat := #[0,1,4,5,32,33,36,37,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,24,25,28,29,56,57,60,61,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap24 : Array Nat := #[0,1,2,3,32,33,34,35,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,24,25,26,27,56,57,58,59,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap25 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,47,46,45,44,43,42,41,40,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,63,62,61,60,59,58,57,56,0,0,0,0,0,0,0,0]
def aliasMap26 : Array Nat := #[0,4,0,5,0,6,0,7,0,12,0,13,0,14,0,15,0,20,0,21,0,22,0,23,0,28,0,29,0,30,0,31,0,36,0,37,0,38,0,39,0,44,0,45,0,46,0,47,0,52,0,53,0,54,0,55,0,60,0,61,0,62,0,63]
def aliasMap27 : Array Nat := #[0,0,0,0,0,0,0,0,33,0,35,0,37,0,39,0,0,0,0,0,0,0,0,0,0,41,0,43,0,45,0,47,0,0,0,0,0,0,0,0,49,0,51,0,53,0,55,0,0,0,0,0,0,0,0,0,0,57,0,59,0,61,0,63]
def aliasMap28 : Array Nat := #[0,0,0,5,0,0,0,7,0,0,0,13,0,0,0,15,0,0,0,21,0,0,0,23,0,0,0,29,0,0,0,31,0,0,0,37,0,0,0,39,0,0,0,45,0,0,0,47,0,0,0,53,0,0,0,55,0,0,0,61,0,0,0,63]
def aliasMap29 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,7,15,23,31,39,47,55,63,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap30 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,33,39,41,47,49,55,57,63,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,7,9,15,17,23,25,31,0,0,0,0,0,0,0,0]
def aliasMap31 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,35,39,41,45,51,55,57,61,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,7,9,13,19,23,25,29,0,0,0,0,0,0,0,0]
def aliasMap32 : Array Nat := #[1,5,17,21,33,37,49,53,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,9,13,25,29,41,45,57,61,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap33 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,37,39,41,43,53,55,57,59,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,5,7,9,11,21,23,25,27,0,0,0,0,0,0,0,0]
def aliasMap34 : Array Nat := #[1,3,17,19,33,35,49,51,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,9,11,25,27,41,43,57,59,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap35 : Array Nat := #[0,0,1,0,2,0,3,0,8,0,9,0,10,0,11,0,0,20,0,21,0,22,0,23,0,28,0,29,0,30,0,31,32,0,33,0,34,0,35,0,40,0,41,0,42,0,43,0,0,52,0,53,0,54,0,55,0,60,0,61,0,62,0,63]
def aliasMap36 : Array Nat := #[0,4,0,0,0,6,0,0,0,12,0,0,0,14,0,0,0,0,0,21,0,0,0,23,0,0,0,29,0,0,0,31,0,36,0,0,0,38,0,0,0,44,0,0,0,46,0,0,0,0,0,53,0,0,0,55,0,0,0,61,0,0,0,63]
def aliasMap37 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,5,13,23,31,37,45,55,63,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap38 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,36,38,44,46,53,55,61,63,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,8,10,17,19,25,27,0,0,0,0,0,0,0,0]
def aliasMap39 : Array Nat := #[0,2,0,0,0,6,0,0,0,10,0,0,0,14,0,0,0,0,0,19,0,0,0,23,0,0,0,27,0,0,0,31,0,34,0,0,0,38,0,0,0,42,0,0,0,46,0,0,0,0,0,51,0,0,0,55,0,0,0,59,0,0,0,63]
def aliasMap40 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,34,38,42,46,51,55,59,63,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,8,12,17,21,25,29,0,0,0,0,0,0,0,0]
def aliasMap41 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,32,38,40,46,49,55,57,63,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,6,8,14,17,23,25,31,0,0,0,0,0,0,0,0]
def aliasMap42 : Array Nat := #[0,2,0,3,0,6,0,7,0,10,0,11,0,14,0,15,0,18,0,19,0,22,0,23,0,26,0,27,0,30,0,31,0,34,0,35,0,38,0,39,0,42,0,43,0,46,0,47,0,50,0,51,0,54,0,55,0,58,0,59,0,62,0,63]
def aliasMap43 : Array Nat := #[0,0,1,0,4,0,5,0,8,0,9,0,12,0,13,0,0,18,0,19,0,22,0,23,0,26,0,27,0,30,0,31,32,0,33,0,36,0,37,0,40,0,41,0,44,0,45,0,0,50,0,51,0,54,0,55,0,58,0,59,0,62,0,63]
def aliasMap44 : Array Nat := #[0,0,0,0,0,0,0,0,32,34,36,38,48,50,52,54,0,0,0,0,0,0,0,0,40,42,44,46,56,58,60,62,0,2,4,6,16,18,20,22,0,0,0,0,0,0,0,0,8,10,12,14,24,26,28,30,0,0,0,0,0,0,0,0]
def aliasMap45 : Array Nat := #[36,37,38,39,12,13,14,15,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,52,53,54,55,28,29,30,31,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap46 : Array Nat := #[34,35,38,39,10,11,14,15,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,50,51,54,55,26,27,30,31,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap47 : Array Nat := #[33,35,37,39,9,11,13,15,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,49,51,53,55,25,27,29,31,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap48 : Array Nat := #[8,9,10,11,12,13,14,15,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,24,25,26,27,28,29,30,31,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap49 : Array Nat := #[0,0,0,0,0,0,0,0,32,33,36,37,48,49,52,53,0,0,0,0,0,0,0,0,40,41,44,45,56,57,60,61,0,1,4,5,16,17,20,21,0,0,0,0,0,0,0,0,8,9,12,13,24,25,28,29,0,0,0,0,0,0,0,0]
def aliasMap50 : Array Nat := #[0,0,0,0,0,0,0,0,32,33,34,35,48,49,50,51,0,0,0,0,0,0,0,0,40,41,42,43,56,57,58,59,0,1,2,3,16,17,18,19,0,0,0,0,0,0,0,0,8,9,10,11,24,25,26,27,0,0,0,0,0,0,0,0]
def aliasMap51 : Array Nat := #[0,0,0,0,0,0,0,0,8,9,10,11,12,13,14,15,0,0,0,0,0,0,0,0,40,41,42,43,44,45,46,47,16,17,18,19,20,21,22,23,0,0,0,0,0,0,0,0,48,49,50,51,52,53,54,55,0,0,0,0,0,0,0,0]
def rootAliases : QFast.AliasTable
  | 1 => some (0, aliasMap11)
  | 2 => some (0, aliasMap4)
  | 3 => some (0, aliasMap3)
  | 4 => some (0, aliasMap10)
  | 5 => some (0, aliasMap9)
  | 6 => some (0, aliasMap37)
  | 7 => some (0, aliasMap29)
  | 8 => some (0, aliasMap8)
  | 9 => some (0, aliasMap7)
  | 10 => some (0, aliasMap6)
  | 16 => some (11, aliasMap48)
  | 17 => some (11, aliasMap47)
  | 18 => some (11, aliasMap46)
  | 19 => some (11, aliasMap45)
  | 20 => some (11, aliasMap34)
  | 21 => some (12, aliasMap33)
  | 22 => some (11, aliasMap24)
  | 23 => some (12, aliasMap20)
  | 24 => some (12, aliasMap16)
  | 25 => some (11, aliasMap32)
  | 26 => some (12, aliasMap31)
  | 27 => some (11, aliasMap23)
  | 28 => some (12, aliasMap19)
  | 29 => some (12, aliasMap15)
  | 30 => some (11, aliasMap22)
  | 31 => some (12, aliasMap18)
  | 32 => some (12, aliasMap14)
  | 33 => some (12, aliasMap41)
  | 34 => some (12, aliasMap30)
  | 35 => some (12, aliasMap40)
  | 36 => some (13, aliasMap39)
  | 37 => some (12, aliasMap38)
  | 38 => some (13, aliasMap36)
  | 39 => some (14, aliasMap28)
  | 40 => some (15, aliasMap13)
  | 41 => some (15, aliasMap27)
  | 42 => some (15, aliasMap12)
  | 43 => some (15, aliasMap5)
  | 44 => some (12, aliasMap2)
  | 45 => some (12, aliasMap25)
  | 46 => some (15, aliasMap17)
  | 54 => some (48, aliasMap51)
  | 55 => some (48, aliasMap50)
  | 56 => some (48, aliasMap49)
  | 57 => some (48, aliasMap44)
  | 58 => some (49, aliasMap43)
  | 59 => some (50, aliasMap42)
  | 60 => some (49, aliasMap35)
  | 61 => some (50, aliasMap26)
  | 62 => some (51, aliasMap21)
  | 63 => some (53, aliasMap1)
  | _ => none
end SignedProjection


namespace SignedProjection

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockRoots_0 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 0 8 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockRoots_8 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 8 8 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockRoots_16 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 16 8 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockRoots_24 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 24 8 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockRoots_32 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 32 8 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockRoots_40 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 40 8 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockRoots_48 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 48 8 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockRoots_56 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 56 8 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockRoots_64 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 64 1 = true := by decide +kernel

theorem joinRoots_0_0 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 0 16 = true :=
  @QFast.merge_blocks (QFast.symCheckRoot rootAliases fastViews fastNodes) 0 8 8 blockRoots_0 blockRoots_8

theorem joinRoots_0_16 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 16 16 = true :=
  @QFast.merge_blocks (QFast.symCheckRoot rootAliases fastViews fastNodes) 16 8 8 blockRoots_16 blockRoots_24

theorem joinRoots_0_32 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 32 16 = true :=
  @QFast.merge_blocks (QFast.symCheckRoot rootAliases fastViews fastNodes) 32 8 8 blockRoots_32 blockRoots_40

theorem joinRoots_0_48 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 48 16 = true :=
  @QFast.merge_blocks (QFast.symCheckRoot rootAliases fastViews fastNodes) 48 8 8 blockRoots_48 blockRoots_56

theorem joinRoots_1_0 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 0 32 = true :=
  @QFast.merge_blocks (QFast.symCheckRoot rootAliases fastViews fastNodes) 0 16 16 joinRoots_0_0 joinRoots_0_16

theorem joinRoots_1_32 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 32 32 = true :=
  @QFast.merge_blocks (QFast.symCheckRoot rootAliases fastViews fastNodes) 32 16 16 joinRoots_0_32 joinRoots_0_48

theorem joinRoots_2_0 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 0 64 = true :=
  @QFast.merge_blocks (QFast.symCheckRoot rootAliases fastViews fastNodes) 0 32 32 joinRoots_1_0 joinRoots_1_32

theorem joinRoots_3_0 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 0 65 = true :=
  @QFast.merge_blocks (QFast.symCheckRoot rootAliases fastViews fastNodes) 0 64 1 joinRoots_2_0 blockRoots_64

theorem certifiedRoots : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 0 65 = true := joinRoots_3_0

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_0 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_6 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 6 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_12 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 12 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_18 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 18 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_24 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 24 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_30 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 30 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_36 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 36 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_42 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 42 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_48 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 48 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_54 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 54 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_60 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 60 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_66 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 66 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_72 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 72 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_78 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 78 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_84 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 84 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_90 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 90 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_96 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 96 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_102 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 102 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_108 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 108 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_114 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 114 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_120 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 120 4 = true := by decide +kernel

theorem joinNodes_0_0 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 12 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 0 6 6 blockNodes_0 blockNodes_6

theorem joinNodes_0_12 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 12 12 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 12 6 6 blockNodes_12 blockNodes_18

theorem joinNodes_0_24 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 24 12 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 24 6 6 blockNodes_24 blockNodes_30

theorem joinNodes_0_36 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 36 12 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 36 6 6 blockNodes_36 blockNodes_42

theorem joinNodes_0_48 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 48 12 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 48 6 6 blockNodes_48 blockNodes_54

theorem joinNodes_0_60 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 60 12 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 60 6 6 blockNodes_60 blockNodes_66

theorem joinNodes_0_72 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 72 12 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 72 6 6 blockNodes_72 blockNodes_78

theorem joinNodes_0_84 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 84 12 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 84 6 6 blockNodes_84 blockNodes_90

theorem joinNodes_0_96 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 96 12 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 96 6 6 blockNodes_96 blockNodes_102

theorem joinNodes_0_108 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 108 12 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 108 6 6 blockNodes_108 blockNodes_114

theorem joinNodes_1_0 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 24 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 0 12 12 joinNodes_0_0 joinNodes_0_12

theorem joinNodes_1_24 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 24 24 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 24 12 12 joinNodes_0_24 joinNodes_0_36

theorem joinNodes_1_48 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 48 24 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 48 12 12 joinNodes_0_48 joinNodes_0_60

theorem joinNodes_1_72 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 72 24 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 72 12 12 joinNodes_0_72 joinNodes_0_84

theorem joinNodes_1_96 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 96 24 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 96 12 12 joinNodes_0_96 joinNodes_0_108

theorem joinNodes_2_0 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 48 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 0 24 24 joinNodes_1_0 joinNodes_1_24

theorem joinNodes_2_48 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 48 48 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 48 24 24 joinNodes_1_48 joinNodes_1_72

theorem joinNodes_2_96 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 96 28 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 96 24 4 joinNodes_1_96 blockNodes_120

theorem joinNodes_3_0 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 96 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 0 48 48 joinNodes_2_0 joinNodes_2_48

theorem joinNodes_4_0 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 124 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 0 96 28 joinNodes_3_0 joinNodes_2_96

theorem certifiedNodes : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 124 = true := joinNodes_4_0

end SignedProjection

namespace SignedProjection
def bMatches (z : Option View) : Bool :=
  match z with
  | none => false
  | some v => vg v == (0xfe80e800e8000000 : Word) && vk v == 10 && (vs v).toFinset == Direct64.cols.toFinset

theorem rootNegative : ¬ CoreSigned.build signedOps (0xfe80e800e8000000 : BitVec 64) 10 Direct64.cols.toFinset := by
  have shape : bMatches (QFast.get fastViews 64) = true := by decide +kernel
  cases ev : QFast.get fastViews 64 with
  | none => simp [ev, bMatches] at shape
  | some v =>
    have valid := QFast.symCertified rootAliases fastViews fastNodes certifiedRoots certifiedNodes ev
    simp only [ev,bMatches,Bool.and_eq_true,beq_iff_eq] at shape
    change ¬ CoreSigned.build signedOps (vg v) (vk v) (vs v).toFinset at valid
    rwa [shape.1.1,shape.1.2,shape.2] at valid
end SignedProjection
end PEqualNP.Outside.L_meta_12056_aux

open PEqualNP.Outside.L_meta_12056_aux in
theorem PEqualNP.Outside.L_meta_12056 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4269860864 * 2 ^ 32 + 3892314112) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4269860864 * 2 ^ 32 + 3892314112) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  LowerSymSix.finish SignedProjection.rootNegative
