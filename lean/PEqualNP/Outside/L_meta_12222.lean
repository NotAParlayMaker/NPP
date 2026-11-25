import PEqualNP.Defs

-- The witness has 11 binary gates. Any circuit with a NOT and fewer gates
-- would have at most 9 binary gates even with every negation available for free.
-- Finite signed-circuit certificates below exclude that possibility.
-- Signed-wire search and gate projections adapt the project’s Apache 2.0 proofs.
namespace PEqualNP.Outside.L_meta_12222_aux
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


namespace LowerSymSix
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit :=
  ⟨[⟨.and,[0,1]⟩, ⟨.or,[0,1]⟩, ⟨.and,[2,7]⟩, ⟨.or,[6,8]⟩, ⟨.and,[2,6]⟩, ⟨.or,[3,4]⟩, ⟨.and,[3,4]⟩, ⟨.or,[5,12]⟩, ⟨.or,[10,13]⟩, ⟨.and,[9,11]⟩, ⟨.and,[14,15]⟩],16⟩

theorem size : witness.size = 11 := rfl

theorem monotone : Monotone2 witness := by
  simp [Monotone2,witness]

set_option maxRecDepth 16000 in
theorem correct : ∀ x : Fin 6 → Bool, witness.eval (List.ofFn x) =
    Nat.testBit (3907577856 * 2 ^ 32 + 3900735488) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel

end LowerSymSix

namespace Direct64
open PEqualNP.CircuitLowerBounds SignedProjection
abbrev W := BitVec 64
abbrev basicOps (a b : W) := signedOps a b
abbrev goal : W := ~~~0xe8e8e800e8808000
open CoreSigned (build)
def tableB (x : Fin 6 → Bool) :=
  Nat.testBit (3907577856 * 2 ^ 32 + 3900735488) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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

theorem low (reject : ¬ build basicOps (0xe8e8e800e8808000 : W) 9 cols.toFinset)
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
    (reject : ¬ CoreSigned.build SignedProjection.signedOps (0xe8e8e800e8808000 : BitVec 64) 9 Direct64.cols.toFinset) :
∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3907577856 * 2 ^ 32 + 3900735488) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3907577856 * 2 ^ 32 + 3900735488) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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

def ew0 : Word := 0x888888

def ew1 : Word := 0xa0a0a0

def ew2 : Word := 0xc0c0c0

def ew3 : Word := 0x8088888

def ew4 : Word := 0x8880888

def ew5 : Word := 0x8888888

def ew6 : Word := 0xa00aa00

def ew7 : Word := 0xaaa0000

def ew8 : Word := 0xc00cc00

def ew9 : Word := 0xccc0000

def ew10 : Word := 0x2020a0a0

def ew11 : Word := 0x20a020a0

def ew12 : Word := 0x20a0a0a0

def ew13 : Word := 0x2200aa00

def ew14 : Word := 0x22aa0000

def ew15 : Word := 0x2a002a00

def ew16 : Word := 0x2a00aa00

def ew17 : Word := 0x2a2a0000

def ew18 : Word := 0x2aaa0000

def ew19 : Word := 0x3000f000

def ew20 : Word := 0x30f00000

def ew21 : Word := 0x3f000000

def ew22 : Word := 0x4040c0c0

def ew23 : Word := 0x40c040c0

def ew24 : Word := 0x40c0c0c0

def ew25 : Word := 0x4400cc00

def ew26 : Word := 0x44cc0000

def ew27 : Word := 0x4c004c00

def ew28 : Word := 0x4c00cc00

def ew29 : Word := 0x4c4c0000

def ew30 : Word := 0x4ccc0000

def ew31 : Word := 0x5000f000

def ew32 : Word := 0x50f00000

def ew33 : Word := 0x5f000000

def ew34 : Word := 0x70007000

def ew35 : Word := 0x7000f000

def ew36 : Word := 0x70700000

def ew37 : Word := 0x70f00000

def ew38 : Word := 0x77000000

def ew39 : Word := 0x7f000000

def ew40 : Word := 0x80008000

def ew41 : Word := 0x80800000

def ew42 : Word := 0x80808080

def ew43 : Word := 0x88000000

def ew44 : Word := 0x88008800

def ew45 : Word := 0x88880000

def ew46 : Word := 0x88888888

def ew47 : Word := 0xa0000000

def ew48 : Word := 0xa000a000

def ew49 : Word := 0xa0a00000

def ew50 : Word := 0xa0a0a0a0

def ew51 : Word := 0xaa000000

def ew52 : Word := 0xaa00aa00

def ew53 : Word := 0xaaaa0000

def ew54 : Word := 0xaaaaaaaa

def ew55 : Word := 0xc0000000

def ew56 : Word := 0xc000c000

def ew57 : Word := 0xc0c00000

def ew58 : Word := 0xc0c0c0c0

def ew59 : Word := 0xcc000000

def ew60 : Word := 0xcc00cc00

def ew61 : Word := 0xcccc0000

def ew62 : Word := 0xcccccccc

def ew63 : Word := 0xf0000000

def ew64 : Word := 0xf000f000

def ew65 : Word := 0xf0f00000

def ew66 : Word := 0xf0f0f0f0

def ew67 : Word := 0xff000000

def ew68 : Word := 0xff00ff00

def ew69 : Word := 0xffff0000

def ew70 : Word := 0xaaaaaaaaaaaaaaaa

def ew71 : Word := 0xcccccccccccccccc

def ew72 : Word := 0xf0f0f0f0f0f0f0f0

def ew73 : Word := 0xff00ff00ff00ff00

def ew74 : Word := 0xffff0000ffff0000

def ew75 : Word := 0xffffffff00000000

def labelsBlock0 : Array Nat := #[
  0xf1c,
  0xf2c,
  0x171c,
  0xf34,
  0xf38,
  0x1b2c,
  0x1d34,
  0x174c,
  0x1e38,
  0x1754,
  0x1758,
  0x1b4c,
  0x1b64,
  0x1b68,
  0x1002,
  0x1d54
]

def labelsBlock1 : Array Nat := #[
  0x1d70,
  0x1d64,
  0xf0c,
  0xf14,
  0xf18,
  0xf24,
  0xf28,
  0xf30,
  0x1006,
  0x170c,
  0x1714,
  0x1718,
  0x1b0c,
  0x100a,
  0x1e58,
  0x1e68
]

def labelsBlock2 : Array Nat := #[
  0x1012,
  0x1e70,
  0x1d14,
  0x1016,
  0x1b24,
  0x1b28,
  0x1d24,
  0x101e,
  0x1e18,
  0x1e28,
  0x1d30,
  0x1e30,
  0x100e,
  0x101a,
  0x1022,
  0x1026
]

def labelsBlock3 : Array Nat := #[
  0x1744,
  0x1748,
  0x1750,
  0x1b60,
  0x1b44,
  0x1b48,
  0x1d50,
  0x1d60,
  0x1d44,
  0x1e48,
  0x1e50,
  0x1e60,
  0x102a,
  0x102e,
  0xf20,
  0x1b04
]

def labelsBlock4 : Array Nat := #[
  0x1d04,
  0xf04,
  0x1b08,
  0xf08,
  0xf10,
  0x1704,
  0x1708,
  0x1710,
  0x1032,
  0x1e08,
  0x1d10,
  0x1e10,
  0x1b20,
  0x1d20,
  0x1e20,
  0xf00
]

def labelsBlock5 : Array Nat := #[
  0x1036,
  0x41,
  0x49,
  0x2d,
  0x39,
  0x6d,
  0x65,
  0xa5,
  0x9d,
  0xed,
  0xf5,
  0xd9,
  0xe5,
  0x119,
  0x111,
  0x151
]

def labelsBlock6 : Array Nat := #[
  0x149,
  0x199,
  0x1a1,
  0x185,
  0x191,
  0x1c5,
  0x1bd,
  0x1fd,
  0x1f5,
  0x245,
  0x24d,
  0x231,
  0x23d,
  0x271,
  0x269,
  0x2a9
]

def labelsBlock7 : Array Nat := #[
  0x2a1,
  0x1e00,
  0x1d00,
  0x1b00,
  0x1700,
  0x45,
  0x4d,
  0x51,
  0x55,
  0x71,
  0x75,
  0x79,
  0x89,
  0x8d,
  0xa9,
  0xad
]

def labelsBlock8 : Array Nat := #[
  0xbd,
  0xf1,
  0xf9,
  0xfd,
  0x101,
  0x11d,
  0x121,
  0x125,
  0x135,
  0x139,
  0x155,
  0x159,
  0x169,
  0x19d,
  0x1a5,
  0x1a9
]

def labelsBlock9 : Array Nat := #[
  0x1ad,
  0x1c9,
  0x1cd,
  0x1d1,
  0x1e1,
  0x1e5,
  0x201,
  0x205,
  0x215,
  0x249,
  0x251,
  0x255,
  0x259,
  0x275,
  0x279,
  0x27d
]

def labelsBlock10 : Array Nat := #[
  0x28d,
  0x291,
  0x2ad,
  0x2b1,
  0x2c1,
  0x29,
  0x35,
  0x31,
  0x3d,
  0x61,
  0x5d,
  0x69,
  0x81,
  0x85,
  0x99,
  0x95
]

def labelsBlock11 : Array Nat := #[
  0xa1,
  0xb5,
  0xb9,
  0xc5,
  0xc9,
  0x59,
  0x7d,
  0x91,
  0xb1,
  0xc1,
  0xcd,
  0xd5,
  0xe1,
  0xdd,
  0xe9,
  0x10d
]

def labelsBlock12 : Array Nat := #[
  0x109,
  0x115,
  0x12d,
  0x131,
  0x145,
  0x141,
  0x14d,
  0x161,
  0x165,
  0x171,
  0x175,
  0x105,
  0x129,
  0x13d,
  0x15d,
  0x16d
]

def labelsBlock13 : Array Nat := #[
  0x179,
  0x181,
  0x18d,
  0x189,
  0x195,
  0x1b9,
  0x1b5,
  0x1c1,
  0x1d9,
  0x1dd,
  0x1f1,
  0x1ed,
  0x1f9,
  0x20d,
  0x211,
  0x21d
]

def labelsBlock14 : Array Nat := #[
  0x221,
  0x1b1,
  0x1d5,
  0x1e9,
  0x209,
  0x219,
  0x225,
  0x22d,
  0x239,
  0x235,
  0x241,
  0x265,
  0x261,
  0x26d,
  0x285,
  0x289
]

def labelsBlock15 : Array Nat := #[
  0x29d,
  0x299,
  0x2a5,
  0x2b9,
  0x2bd,
  0x2c9,
  0x2cd,
  0x25d,
  0x281,
  0x295,
  0x2b5,
  0x2c5,
  0x2d1,
  0x1,
  0x5,
  0x9
]

def labelsBlock16 : Array Nat := #[
  0xd,
  0x11,
  0x15,
  0x19,
  0x1d,
  0x21,
  0x25,
  0xd1,
  0x17d,
  0x229,
  0x2d5,
  0x2d9,
  0x3600,
  0x3500,
  0x3504,
  0x3300
]

def labelsBlock17 : Array Nat := #[
  0x3304,
  0x3308,
  0x330c,
  0x2e00,
  0x2d00,
  0x2d04,
  0x2b00,
  0x2b04,
  0x2b08,
  0x2b0c,
  0x2e20,
  0x2d20,
  0x2d24,
  0x2b20,
  0x2b24,
  0x2b28
]

def labelsBlock18 : Array Nat := #[
  0x2b2c,
  0x103a
]

def labelsGet (i : Nat) : Nat :=
  if i < 144 then
    if i < 64 then
      if i < 32 then
        if i < 16 then
          labelsBlock0.getD (i-0) 3
        else
          labelsBlock1.getD (i-16) 3
      else
        if i < 48 then
          labelsBlock2.getD (i-32) 3
        else
          labelsBlock3.getD (i-48) 3
    else
      if i < 96 then
        if i < 80 then
          labelsBlock4.getD (i-64) 3
        else
          labelsBlock5.getD (i-80) 3
      else
        if i < 112 then
          labelsBlock6.getD (i-96) 3
        else
          if i < 128 then
            labelsBlock7.getD (i-112) 3
          else
            labelsBlock8.getD (i-128) 3
  else
    if i < 224 then
      if i < 176 then
        if i < 160 then
          labelsBlock9.getD (i-144) 3
        else
          labelsBlock10.getD (i-160) 3
      else
        if i < 192 then
          labelsBlock11.getD (i-176) 3
        else
          if i < 208 then
            labelsBlock12.getD (i-192) 3
          else
            labelsBlock13.getD (i-208) 3
    else
      if i < 256 then
        if i < 240 then
          labelsBlock14.getD (i-224) 3
        else
          labelsBlock15.getD (i-240) 3
      else
        if i < 272 then
          labelsBlock16.getD (i-256) 3
        else
          if i < 288 then
            labelsBlock17.getD (i-272) 3
          else
            labelsBlock18.getD (i-288) 3

def decodeHints (enc i : Nat) := labelsGet ((enc >>> (i * 9)) % 512)

def localHints (stride dict enc i : Nat) : Nat :=
  let q := (enc >>> (stride*i)) % (2^stride)
  labelsGet ((dict >>> (9*q)) % 512)

def viewsBlock0 : Array View := #[
  ⟨0x88888888,⟨3,by decide⟩,0x88808000,[ew42,ew44,ew45],3,decodeHints 0x7e8040012010643812⟩,
  ⟨0xa0a0a0a0,⟨5,by decide⟩,0xa0808000,[ew42,ew48,ew49],3,decodeHints 0x7f00c0013010684413⟩,
  ⟨0xaa00aa00,⟨9,by decide⟩,0xa8008000,[ew44,ew48,ew51],3,decodeHints 0x7f80c0215028904c15⟩,
  ⟨0xaaaa0000,⟨17,by decide⟩,0xa8800000,[ew45,ew49,ew51],3,decodeHints 0x800240e30058d07030⟩,
  ⟨0xc0c0c0c0,⟨6,by decide⟩,0xc0808000,[ew42,ew56,ew57],3,decodeHints 0x8081000140106c5014⟩,
  ⟨0xcc00cc00,⟨10,by decide⟩,0xc8008000,[ew44,ew56,ew59],3,decodeHints 0x810100216028945216⟩,
  ⟨0xcccc0000,⟨18,by decide⟩,0xc8800000,[ew45,ew57,ew59],3,decodeHints 0x818280e31058d47231⟩,
  ⟨0xf000f000,⟨12,by decide⟩,0xe0008000,[ew48,ew56,ew63],3,decodeHints 0x820100617030a85617⟩,
  ⟨0xf0f00000,⟨20,by decide⟩,0xe0800000,[ew49,ew57,ew63],3,decodeHints 0x828281232078d87432⟩,
  ⟨0xff000000,⟨24,by decide⟩,0xe8000000,[ew51,ew59,ew63],3,decodeHints 0x830341833088dc7633⟩,
  ⟨0xaaaaaaaa,⟨1,by decide⟩,0xa8808000,[ew46,ew50,ew52,ew53],6,decodeHints 0x8380c02150004c24410106832450e0fc8041⟩,
  ⟨0xcccccccc,⟨2,by decide⟩,0xc8808000,[ew46,ew58,ew60,ew61],6,decodeHints 0x8401002160005024430106c32460e1089243⟩,
  ⟨0xf0f0f0f0,⟨4,by decide⟩,0xe0808000,[ew50,ew58,ew64,ew65],6,decodeHints 0x8481006170005026440106c3447111289644⟩,
  ⟨0xff00ff00,⟨8,by decide⟩,0xe8008000,[ew52,ew60,ew64,ew67],6,decodeHints 0x850100617008582a3e02894484c131349c3e⟩,
  ⟨0xffffffff,⟨0,by decide⟩,0xe8808000,[ew54,ew62,ew66,ew68,ew69],8,decodeHints 0x858100617008582a3e0005026440910c824f0106c34470c9188a740e1087e73201c8e24f⟩,
  ⟨0xffffffffffffffff,⟨0,by decide⟩,0xe8e8e800e8808000,[ew70,ew71,ew72,ew73,ew74,ew75],9,decodeHints 0x908100617008582a3e0005026440910c824f0106c34470c9188a740e1087e73201c8e24f9047e3d1d8e46e343e8cc622f168ac52264f89446210f8743618740e1087e73201c8e24f⟩
]

def viewsGet (i : Nat) : Option View :=
  viewsBlock0[(i-0)]?

def nodesBlock0 : Array Node := #[
  ⟨0,3,[ew42,ew44,ew45],localHints 4 0x1c0c8080a12008001607 0x258168155262367057066353024314322010⟩,
  ⟨1,3,[ew42,ew48,ew49],localHints 4 0x220d0080c13018001e09 0x258168155262367057066353024314322010⟩,
  ⟨2,3,[ew44,ew48,ew51],localHints 4 0x26120140c1501804220c 0x258168155262367057066353024314322010⟩,
  ⟨3,3,[ew45,ew49,ew51],localHints 4 0x381a02c1e300481c220c 0x258168155262367057066353024314322010⟩,
  ⟨4,3,[ew42,ew56,ew57],localHints 4 0x280d8081014020003c0a 0x258168155262367057066353024314322010⟩,
  ⟨5,3,[ew44,ew56,ew59],localHints 4 0x29128141016020043e0d 0x258168155262367057066353024314322010⟩,
  ⟨6,3,[ew45,ew57,ew59],localHints 4 0x391a82c3c310501c3e0d 0x258168155262367057066353024314322010⟩,
  ⟨7,3,[ew48,ew56,ew63],localHints 4 0x2b1501810170200c4210 0x258168155262367057066353024314322010⟩,
  ⟨8,3,[ew49,ew57,ew63],localHints 4 0x3a1b03c3c32050244210 0x258168155262367057066353024314322010⟩,
  ⟨9,3,[ew51,ew59,ew63],localHints 4 0x3b1b8443e33068304210 0x258168155262367057066353024314322010⟩,
  ⟨10,3,[ew18,ew46,ew50,ew52],decodeHints 0x904800070984c00090a854020c0e0700a000c86404010d0680403⟩,
  ⟨10,4,[ew40,ew46,ew50,ew52,ew53],decodeHints 0x381c0280832190101470380781c341a010186834058246030038314a02160080000008040603⟩,
  ⟨10,4,[ew15,ew46,ew50,ew52,ew53],localHints 4 0xc8483406098c00a02058002207008301203 0x6896ff89ee64dd8cbb61aa4298987654332100⟩,
  ⟨10,3,[ew16,ew46,ew50,ew53],decodeHints 0xc86404010d06804030a854020c0e0700a000904800070984c0009⟩,
  ⟨10,4,[ew41,ew46,ew50,ew52,ew53],decodeHints 0x381c028004c260300424120002c48240280c26130003c2a15008300402530003a00038041203⟩,
  ⟨10,4,[ew17,ew46,ew50,ew52,ew53],localHints 4 0xc8483413078540a02058002207008301203 0x6876ff83ee67dd80cc6baa3298767653432010⟩
]

def nodesBlock1 : Array Node := #[
  ⟨10,3,[ew42,ew44,ew48,ew53],decodeHints 0x201000c021f8fc0a02000001c34229140405008041c300180c3030⟩,
  ⟨10,4,[ew42,ew44,ew50,ew52,ew53],decodeHints 0x110880a020109804051c0e01e51120080a020000018110c030341a01014120f0e82402010180c3009⟩,
  ⟨10,3,[ew42,ew45,ew49,ew52],localHints 4 0x1007e02208001626070903015 0xaa4699268832776504300210⟩,
  ⟨10,4,[ew42,ew45,ew50,ew52,ew53],decodeHints 0x110880c00130980c52000e0000b0100868000580018110c03006061600c26130002c2a15018243003⟩,
  ⟨10,4,[ew42,ew46,ew48,ew52,ew53],decodeHints 0xe0700a02130080c02000000424010186834059441811070303219010140e0b0e81c02010701c0603⟩,
  ⟨10,4,[ew42,ew46,ew49,ew52,ew53],decodeHints 0xe0700a000100870000780048240294800340003c18110703002051600424120002c0207070042a15⟩,
  ⟨10,5,[ew42,ew46,ew50,ew52,ew53],localHints 5 0x704c781c1dc4876030d0ea0f540b0045402a9c3a002982c22010c0381803 0x85e8cdd196b435036b4abc95adc2d63420a6b9508b18c26b433a85ada4e6242030905088c20110465288427b5ae5adcd6b16b521093192841cc6108822904300820⟩,
  ⟨10,4,[ew11,ew46,ew50,ew52,ew53],localHints 4 0xe04834061a05404050782c0007008241803 0xff899893ee36dd9cbb62aa3198987655432100⟩,
  ⟨10,3,[ew12,ew46,ew52,ew53],decodeHints 0xe0700a000d06804030984c00090c86404010904800070a854020c⟩,
  ⟨10,4,[ew43,ew46,ew50,ew52,ew53],decodeHints 0x44220300032190100424120001c341a0100c2613000242a15008440a020580152010c0041803⟩,
  ⟨10,4,[ew14,ew46,ew50,ew52,ew53],localHints 4 0x7024240284c2a110103c1600038041203 0xeeb42b32dd43ccb0aa41992877645432321010⟩,
  ⟨10,3,[ew44,ew45,ew50,ew51],localHints 4 0x8045008881c41038683a13 0x996726528827065044030210⟩,
  ⟨10,4,[ew44,ew45,ew50,ew52,ew53],localHints 4 0x111544c380d03c60061604c2a01038243a03 0xff8edd84c443bb2a12943408706655430210⟩,
  ⟨10,4,[ew44,ew46,ew48,ew50,ew53],decodeHints 0xc8640405110880c0200804341a01018603003944120f07024381c0280816070c01c00000702c0603⟩,
  ⟨10,4,[ew44,ew46,ew50,ew51,ew53],decodeHints 0x11088321901004023807804341a01154120f07024023000844000216000000b0700024120001c2613⟩,
  ⟨10,5,[ew44,ew46,ew50,ew52,ew53],localHints 5 0x88f6191c1e83479030c0ea11558b00a560103c00aa0c004a6070e8381203 0x36e94bd29adcad665e08dc116b334c455cc331946258825d433a856ba4e611046a50842118c184826346107b5ae5adcd6b16b109225250631c84398c52104300820⟩
]

def nodesBlock2 : Array Node := #[
  ⟨10,4,[ew10,ew46,ew50,ew52,ew53],localHints 4 0xe0640e240983c600602808000b008300609 0xff75ee87545dcc71bb5a911287665454331210⟩,
  ⟨10,4,[ew13,ew46,ew50,ew52,ew53],localHints 4 0x38190d0d02a110301404000081c0609 0xdd75cc532332bb51a110993875654432321010⟩,
  ⟨10,4,[ew45,ew46,ew49,ew50,ew52],decodeHints 0x9048000b110880c001309826130003c2a150094806060700c381c028000a010c0040402070144824⟩,
  ⟨10,4,[ew45,ew46,ew50,ew51,ew52],decodeHints 0x1108824120001c4c260300426130015406060700c2a150084404000e800040507008321901004341a⟩,
  ⟨10,5,[ew45,ew46,ew50,ew52,ew53],localHints 5 0x88fa263e048267907854ec11030095a1d0595800ac0c01ca801160241c03 0x97e963d2def4e5247e0c3c19ef25c864d88bb112932cc00806f784210a6a09d4094d273092408480424610085c17b9ab5b12962d6a4a50631c84398c52102310400⟩,
  ⟨10,4,[ew4,ew46,ew50,ew52,ew53],localHints 4 0xe0640a380985404060583c0007088041203 0xffd9ee9dcc649890bb06aa0398987655432210⟩,
  ⟨10,3,[ew5,ew50,ew52,ew53],decodeHints 0xe0700a000c86404010904800070d06804030984c00090a854020c⟩,
  ⟨10,4,[ew46,ew47,ew50,ew52,ew53],decodeHints 0x381c0280032190100424120001c0c020780022010d06804030984c00090a854020c01ab81c03⟩,
  ⟨10,4,[ew7,ew46,ew50,ew52,ew53],localHints 4 0x4426090182615060081600038041203 0xdda4cca2bb430a109941882766545432321010⟩,
  ⟨10,3,[ew46,ew48,ew49,ew51],localHints 4 0x301d1f8708a19019042409 0x469416911481776355432210⟩,
  ⟨10,4,[ew46,ew48,ew49,ew52,ew53],localHints 4 0xe15c320b160483a24028d06007018540209 0xff7edd4c9417b1aa14918873633035432210⟩,
  ⟨10,4,[ew46,ew48,ew50,ew51,ew53],decodeHints 0xe07032190115c0e0b0c01c000216000000b0c00024120d0680403018d016031800c060c0984c0009⟩,
  ⟨10,5,[ew46,ew48,ew50,ew52,ew53],localHints 5 0x70fe193f015602c2c000021a01018681d059e86018039dc18af0700ca609 0xcb696fd2ed6cbde87e0f6c1defbdac741d8b5a108ab9d47be8e74def422435c90c88cf113e007400f789c202da26084b1014029d2240847114c500c022084310020⟩,
  ⟨10,4,[ew3,ew46,ew50,ew52,ew53],localHints 4 0xe098240b0d024600503008000f088040e03 0xff85ee72dd5cbb87545a292387665454232100⟩,
  ⟨10,4,[ew6,ew46,ew50,ew52,ew53],localHints 4 0x220c8e034150601404000081c0609 0xcc65bb53a33299510110883765654432321010⟩,
  ⟨10,4,[ew46,ew49,ew50,ew51,ew52],decodeHints 0xe07024120015c02050c00404000e80004050c00832190984c0009120900a030a854020c0d0680403⟩
]

def nodesBlock3 : Array Node := #[
  ⟨10,5,[ew46,ew49,ew50,ew52,ew53],localHints 5 0x7100123f02c04b20e9600e2c12014f8130003c3015009e018b107024a803 0xb76ad0d59ce5e56749e0e725294af07b60eb5ded64a6a37568a54d6b9a9525ad3088ce7039e283c4e701a012d805300b5894229d004a007394c500c022084310020⟩,
  ⟨10,4,[ew0,ew46,ew50,ew52,ew53],localHints 4 0x110642407120d01806010141e00058042203 0xff84ee72dd4c7b784a45212978764543212100⟩,
  ⟨10,4,[ew1,ew46,ew50,ew52,ew53],localHints 4 0x1c130e03413048080a0005804060c 0xcc546b654a4399618847011065654343221010⟩,
  ⟨10,5,[ew46,ew50,ew51,ew52,ew53],localHints 5 0x14161940048fe075a060b02c0d008fa1d09800f60959838ac1501804220c 0xa62a0e7318c6334673990c994a13b148628e70ae2a2ac26584a552b4148419843208a221b9e883d0e70da34296362c6a52128198603800600ca3008830906210020⟩,
  ⟨10,6,[ew46,ew50,ew52,ew53],localHints 5 0xe2e832b902849700b038b034025b8183a13002d81e090c0541c0300ad4220c 0x6aefb9521b6d2f7d2e0b38e1994ef93ce10c0ee33cd7668e9638d6bace9329211921d12a210791c42a16c6912c2916b5212828066390262906310020⟩,
  ⟨11,3,[ew30,ew46,ew58,ew60],decodeHints 0x904800070a050000a0b058020d0e0700a000c86404010d86c0404⟩,
  ⟨11,4,[ew40,ew46,ew58,ew60,ew61],decodeHints 0x381c0280832190101472390f01c361b010206a35058286231038357602168080000008040804⟩,
  ⟨11,4,[ew27,ew46,ew58,ew60,ew61],localHints 4 0xc84836080a0c40a02058003e07008341404 0x6896ff89ee64dd8cbb61aa4298987654332100⟩,
  ⟨11,3,[ew28,ew46,ew58,ew61],decodeHints 0xc86404010d86c04040b058020d0e0700a000904800070a050000a⟩,
  ⟨11,4,[ew41,ew46,ew58,ew60,ew61],decodeHints 0x381c0280052290400424120002c4a25028102814000782c160083404025e0004600038041404⟩,
  ⟨11,4,[ew29,ew46,ew58,ew60,ew61],localHints 4 0xc84836140f0580a02058003e07008341404 0x6876ff83ee67dd80cc6baa3298767653432010⟩,
  ⟨11,3,[ew42,ew44,ew56,ew61],decodeHints 0x249241002211080a02000001c35231180405008041c31020104031⟩,
  ⟨11,4,[ew42,ew44,ew58,ew60,ew61],decodeHints 0x140a00a02010a404051c8e43c59128080a02000001a1f10034361b01014141e11828020102010400a⟩,
  ⟨11,3,[ew42,ew45,ew57,ew60],localHints 4 0x1248402218001629070944016 0xaa4699268832776504300210⟩,
  ⟨11,4,[ew42,ew45,ew58,ew60,ew61],decodeHints 0x140a01000148a4105a000e4000b010086a00058001a1f1003408081681028140002c2c16020284004⟩,
  ⟨11,4,[ew42,ew46,ew56,ew60,ew61],decodeHints 0xe0700a02148081002000000425010206a35059641a1f070343219010140e0b1181c02010701c0804⟩
]

def nodesBlock4 : Array Node := #[
  ⟨11,4,[ew42,ew46,ew57,ew60,ew61],decodeHints 0xe0700a000100872000f0004a25029680035000781a1f0703402051680424120002c0207070042c16⟩,
  ⟨11,5,[ew42,ew46,ew58,ew60,ew61],localHints 5 0x7052841ca0c4a82040d5021e5f0b4045c02af446002d82c3e01100381a04 0x85e8cdd196b435036b4abc95adc2d63420a6b9508b18c26b433a85ada4e6242030905088c20110465288427b5ae5adcd6b16b521093192841cc6108822904300820⟩,
  ⟨11,4,[ew23,ew46,ew58,ew60,ew61],localHints 4 0xe04836081a85804050f02c0007008281a04 0xff899893ee36dd9cbb62aa3198987655432100⟩,
  ⟨11,3,[ew24,ew46,ew60,ew61],decodeHints 0xe0700a000d86c04040a050000a0c86404010904800070b058020d⟩,
  ⟨11,4,[ew43,ew46,ew58,ew60,ew61],decodeHints 0x50280400032190100424120001c361b010102814000282c160087c0a02058017e01100041a04⟩,
  ⟨11,4,[ew26,ew46,ew58,ew60,ew61],localHints 4 0x702425028502c1f010781600038041404 0xeeb42b32dd43ccb0aa41992877645432321010⟩,
  ⟨11,3,[ew44,ew45,ew58,ew59],localHints 4 0x9246008a01c430386c4614 0x996726528827065044030210⟩,
  ⟨11,4,[ew44,ew45,ew58,ew60,ew61],localHints 4 0x1417452390d8786208168502c01038284604 0xff8edd84c443bb2a12943408706655430210⟩,
  ⟨11,4,[ew44,ew46,ew56,ew58,ew61],decodeHints 0xc8640405140a0100200804361b01020623103964141e07028381c0280816071001c00000702c0804⟩,
  ⟨11,4,[ew44,ew46,ew58,ew59,ew61],decodeHints 0x140a032190100402390f004361b01174141e0702802310087c000216800000b0700024120001c2814⟩,
  ⟨11,5,[ew44,ew46,ew58,ew60,ew61],localHints 5 0xa10e191ca183685040c5021f608b40a5e0107800c010004b607118381404 0x36e94bd29adcad665e08dc116b334c455cc331946258825d433a856ba4e611046a50842118c184826346107b5ae5adcd6b16b109225250631c84398c52104300820⟩,
  ⟨11,4,[ew22,ew46,ew58,ew60,ew61],localHints 4 0xe0640e250a078620802808000b00834080a 0xff75ee87545dcc71bb5a911287665454331210⟩,
  ⟨11,4,[ew25,ew46,ew58,ew60,ew61],localHints 4 0x38190d8d42c1f0401404000081c080a 0xdd75cc532332bb51a110993875654432321010⟩,
  ⟨11,4,[ew45,ew46,ew57,ew58,ew60],decodeHints 0x9048000b140a01000148a42814000782c1600968080807010381c028000a01100040402070144a25⟩,
  ⟨11,4,[ew45,ew46,ew58,ew59,ew60],decodeHints 0x140a024120001c5229040042814001740808070102c160087c040011800040507008321901004361b⟩,
  ⟨11,5,[ew45,ew46,ew58,ew60,ew61],localHints 5 0xa112294404828850f059041f0400986230597800c21001cb801168281c04 0x97e963d2def4e5247e0c3c19ef25c864d88bb112932cc00806f784210a6a09d4094d273092408480424610085c17b9ab5b12962d6a4a50631c84398c52102310400⟩
]

def nodesBlock5 : Array Node := #[
  ⟨11,4,[ew4,ew46,ew58,ew60,ew61],localHints 4 0xe0640a390a05804080587800070f8041404 0xffd9ee9dcc649890bb06aa0398987655432210⟩,
  ⟨11,3,[ew5,ew58,ew60,ew61],decodeHints 0xe0700a000c86404010904800070d86c04040a050000a0b058020d⟩,
  ⟨11,4,[ew46,ew55,ew58,ew60,ew61],decodeHints 0x381c0280032190100424120001c10020f0003e010d86c04040a050000a0b058020d023101c04⟩,
  ⟨11,4,[ew9,ew46,ew58,ew60,ew61],localHints 4 0x5029090202816068081600038041404 0xdda4cca2bb430a109941882766545432321010⟩,
  ⟨11,3,[ew46,ew56,ew57,ew59],localHints 4 0x4023210708c190210c240a 0x469416911481776355432210⟩,
  ⟨11,4,[ew46,ew56,ew57,ew60,ew61],localHints 4 0xe17c320b168484625028d4620702058020a 0xff7edd4c9417b1aa14918873633035432210⟩,
  ⟨11,4,[ew46,ew56,ew58,ew59,ew61],decodeHints 0xe07032190117c0e0b1001c000216800000b1000024120d86c0404020d4160418810080d0a050000a⟩,
  ⟨11,5,[ew46,ew56,ew58,ew60,ew61],localHints 5 0x711619450158c2d30000021b010206a2305a18622003a0c1ac507010b60a 0xcb696fd2ed6cbde87e0f6c1defbdac741d8b5a108ab9d47be8e74def422435c90c88cf113e007400f789c202da26084b1014029d2240847114c500c022084310020⟩,
  ⟨11,4,[ew3,ew46,ew58,ew60,ew61],localHints 4 0xe0a4240b0d828620504008001e0f8040e04 0xff85ee72dd5cbb87545a292387665454232100⟩,
  ⟨11,4,[ew8,ew46,ew58,ew60,ew61],localHints 4 0x280c8e436160681404000081c080a 0xcc65bb53a33299510110883765654432321010⟩,
  ⟨11,4,[ew46,ew57,ew58,ew59,ew60],decodeHints 0xe07024120017c02051000404001180004051000832190a050000a128940a040b058020d0d86c0404⟩,
  ⟨11,5,[ew46,ew57,ew58,ew60,ew61],localHints 5 0x7118124502c04c8119800e2d12815101400078401600a101ac707028b804 0xb76ad0d59ce5e56749e0e725294af07b60eb5ded64a6a37568a54d6b9a9525ad3088ce7039e283c4e701a012d805300b5894229d004a007394c500c022084310020⟩,
  ⟨11,4,[ew0,ew46,ew58,ew60,ew61],localHints 4 0x140642407128d41a08010143c00058043e04 0xff84ee72dd4c7b784a45212978764543212100⟩,
  ⟨11,4,[ew2,ew46,ew58,ew60,ew61],localHints 4 0x1c148e43614050080a0005804080d 0xcc546b654a4399618847011065654343221010⟩,
  ⟨11,5,[ew46,ew58,ew59,ew60,ew61],localHints 5 0x14161946049160765080c02d0d80912230a0010e0a64838bc16020043e0d 0xa62a0e7318c6334673990c994a13b148628e70ae2a2ac26584a552b4148419843208a221b9e883d0e70da34296362c6a52128198603800600ca3008830906210020⟩,
  ⟨11,6,[ew46,ew58,ew60,ew61],localHints 5 0xe34032cf028499c0b038b43602668204614003303c0a100581c0400b2c3e0d 0x6aefb9521b6d2f7d2e0b38e1994ef93ce10c0ee33cd7668e9638d6bace9329211921d12a210791c42a16c6912c2916b5212828066390262906310020⟩
]

def nodesBlock6 : Array Node := #[
  ⟨12,3,[ew37,ew50,ew58,ew64],decodeHints 0x984c00090a050000a0b85c0610110880c000d06804030d86c0404⟩,
  ⟨12,4,[ew40,ew50,ew58,ew64,ew65],decodeHints 0x442203008341a01018743a0f024361b010206c3607828643204841a2021700800000180c0804⟩,
  ⟨12,4,[ew34,ew50,ew58,ew64,ew65],localHints 4 0xd04c36080a0c80c02078004209018401404 0x6896ff89ee64dd8cbb61aa4298987654332100⟩,
  ⟨12,3,[ew35,ew50,ew58,ew65],decodeHints 0xd06804030d86c04040b85c0610110880c000984c00090a050000a⟩,
  ⟨12,4,[ew41,ew50,ew58,ew64,ew65],decodeHints 0x442203000562b0400c26130003c542a030102814000782e17018400402690004e000480c1404⟩,
  ⟨12,4,[ew36,ew50,ew58,ew64,ew65],localHints 4 0xd04c36140f05c0c02078004209018401404 0x6876ff83ee67dd80cc6baa3298767653432010⟩,
  ⟨12,3,[ew42,ew48,ew56,ew65],decodeHints 0x2592c1002251280c020000030362391c04060180c3032020104032⟩,
  ⟨12,4,[ew42,ew48,ew58,ew64,ew65],decodeHints 0x140a00c02010ac04061d0e83c61150080c0200000202110040361b01018141e13828060302010400a⟩,
  ⟨12,3,[ew42,ew49,ew57,ew64],localHints 4 0x12c9402220001e2b0c0a84017 0xaa4699268832776504300210⟩,
  ⟨12,4,[ew42,ew49,ew58,ew64,ew65],decodeHints 0x140a01000158ac1062000e8000f010086c000780020211004008081701028140003c2e17020284004⟩,
  ⟨12,4,[ew42,ew50,ew56,ew64,ew65],decodeHints 0x110880c0215808100200000042a010206c360798420210c040341a01018120f1382406030c0240804⟩,
  ⟨12,4,[ew42,ew50,ew57,ew64,ew65],decodeHints 0x110880c000100874000f000542a0318800360007820210c04006061700c26130003c06090c00c2e17⟩,
  ⟨12,5,[ew42,ew50,ew58,ew64,ew65],localHints 5 0x8856901d23c548e040d91a1e6a0b804640334c4e003183c4203100602004 0x85e8cdd196b435036b4abc95adc2d63420a6b9508b18c26b433a85ada4e6242030905088c20110465288427b5ae5adcd6b16b521093192841cc6108822904300820⟩,
  ⟨12,4,[ew23,ew50,ew58,ew64,ew65],localHints 4 0x1104c36081b05c04060f03c0009018282004 0xff899893ee36dd9cbb62aa3198987655432100⟩,
  ⟨12,3,[ew24,ew50,ew64,ew65],decodeHints 0x110880c000d86c04040a050000a0d06804030984c00090b85c0610⟩,
  ⟨12,4,[ew47,ew50,ew58,ew64,ew65],decodeHints 0x502804000341a0100c261300024361b010102814000282e17018840c0207801aa031000c2004⟩
]

def nodesBlock7 : Array Node := #[
  ⟨12,4,[ew32,ew50,ew58,ew64,ew65],localHints 4 0x88262a030502e21010781e000480c1404 0xeeb42b32dd43ccb0aa41992877645432321010⟩,
  ⟨12,3,[ew48,ew49,ew58,ew63],localHints 4 0x9647018a030440486c4e14 0x996726528827065044030210⟩,
  ⟨12,4,[ew48,ew49,ew58,ew64,ew65],localHints 4 0x14194563a0d8786408170502e03048284e04 0xff8edd84c443bb2a12943408706655430210⟩,
  ⟨12,4,[ew48,ew50,ew56,ew58,ew65],decodeHints 0xd0680406140a010020180c361b01020643204984141e0c0284422030081e091002400000c03c0804⟩,
  ⟨12,4,[ew48,ew50,ew58,ew63,ew65],decodeHints 0x140a0341a0100c063a0f00c361b01194141e0c028063201884000217000000f0c0002613000242814⟩,
  ⟨12,5,[ew48,ew50,ew58,ew64,ew65],localHints 5 0xa1261a1d2483691040c91a216b8b80c660107800d61000cc609138601404 0x36e94bd29adcad665e08dc116b334c455cc331946258825d433a856ba4e611046a50842118c184826346107b5ae5adcd6b16b109225250631c84398c52104300820⟩,
  ⟨12,4,[ew22,ew50,ew58,ew64,ew65],localHints 4 0x11068122a0a078640803008000f01840080a 0xff75ee87545dcc71bb5a911287665454331210⟩,
  ⟨12,4,[ew31,ew50,ew58,ew64,ew65],localHints 4 0x441a0d8d82e2104018040001824080a 0xdd75cc532332bb51a110993875654432321010⟩,
  ⟨12,4,[ew49,ew50,ew57,ew58,ew64],decodeHints 0x984c000f140a01000158ac2814000782e170198808080c0104422030000c031000c04020c018542a⟩,
  ⟨12,4,[ew49,ew50,ew58,ew63,ew64],decodeHints 0x140a0261300024562b0400c28140019408080c0102e170188404001380004060c008341a0100c361b⟩,
  ⟨12,5,[ew49,ew50,ew58,ew64,ew65],localHints 5 0xa12a2b4a04c28910f05d1c2104009b2270799800d810024c803170283004 0x97e963d2def4e5247e0c3c19ef25c864d88bb112932cc00806f784210a6a09d4094d273092408480424610085c17b9ab5b12962d6a4a50631c84398c52102310400⟩,
  ⟨12,4,[ew11,ew50,ew58,ew64,ew65],localHints 4 0x110680c3a0a05c04080787800091080c1404 0xffd9ee9dcc649890bb06aa0398987655432210⟩,
  ⟨12,3,[ew12,ew58,ew64,ew65],decodeHints 0x110880c000d06804030984c00090d86c04040a050000a0b85c0610⟩,
  ⟨12,4,[ew50,ew55,ew58,ew64,ew65],decodeHints 0x442203000341a0100c26130002410020f00042030d86c04040a050000a0b85c0610023683004⟩,
  ⟨12,4,[ew20,ew50,ew58,ew64,ew65],localHints 4 0x502b098202817080081e000480c1404 0xdda4cca2bb430a109941882766545432321010⟩,
  ⟨12,3,[ew50,ew56,ew57,ew63],localHints 4 0x4027250888e1a02110260a 0x469416911481776355432210⟩
]

def nodesBlock8 : Array Node := #[
  ⟨12,4,[ew50,ew56,ew57,ew64,ew65],localHints 4 0x1119c340f1704c4e2a030d864090205c060a 0xff7edd4c9417b1aa14918873633035432210⟩,
  ⟨12,4,[ew50,ew56,ew58,ew63,ew65],decodeHints 0x11088341a0119c120f10024000217000000f1000026130d86c0404020d81e041901008100a050000a⟩,
  ⟨12,5,[ew50,ew56,ew58,ew64,ew65],localHints 5 0x892e1a4b019b82e34000061b010206c2707a48642004a3c20db0c010c60a 0xcb696fd2ed6cbde87e0f6c1defbdac741d8b5a108ab9d47be8e74def422435c90c88cf113e007400f789c202da26084b1014029d2240847114c500c022084310020⟩,
  ⟨12,4,[ew10,ew50,ew58,ew64,ew65],localHints 4 0x110ac260f0d828640604008001e1080c1204 0xff85ee72dd5cbb87545a292387665454232100⟩,
  ⟨12,4,[ew19,ew50,ew58,ew64,ew65],localHints 4 0x280d0e8361708018040001824080a 0xcc65bb53a33299510110883765654432321010⟩,
  ⟨12,4,[ew50,ew57,ew58,ew63,ew64],decodeHints 0x1108826130019c06061000c040013800040610008341a0a050000a150a80c040b85c06100d86c0404⟩,
  ⟨12,5,[ew50,ew57,ew58,ew64,ew65],localHints 5 0x8930134b03c04de139a0122e15019281400078401701a4020dd0c028c804 0xb76ad0d59ce5e56749e0e725294af07b60eb5ded64a6a37568a54d6b9a9525ad3088ce7039e283c4e701a012d805300b5894229d004a007394c500c022084310020⟩,
  ⟨12,4,[ew1,ew50,ew58,ew64,ew65],localHints 4 0x140682609150d82008010183c000780c4204 0xff84ee72dd4c7b784a45212978764543212100⟩,
  ⟨12,4,[ew2,ew50,ew58,ew64,ew65],localHints 4 0x22158e83614050080c000780c0810 0xcc546b654a4399618847011065654343221010⟩,
  ⟨12,5,[ew50,ew58,ew63,ew64,ew65],localHints 5 0x181e1a4c04d2e0970080d02e0d8092a270a001260a6f860cc170200c4210 0xa62a0e7318c6334673990c994a13b148628e70ae2a2ac26584a552b4148419843208a221b9e883d0e70da34296362c6a52128198603800600ca3008830906210020⟩,
  ⟨12,6,[ew50,ew58,ew64,ew65],localHints 5 0x1139834e50304dc80f048b83602718204e14003883c0a1005c300401b844210 0x6aefb9521b6d2f7d2e0b38e1994ef93ce10c0ee33cd7668e9638d6bace9329211921d12a210791c42a16c6912c2916b5212828066390262906310020⟩,
  ⟨13,3,[ew39,ew52,ew60,ew64],decodeHints 0xa854020c0b058020d0b85c0610130980c01120900a03128940a04⟩,
  ⟨13,4,[ew40,ew52,ew60,ew64,ew67],decodeHints 0x4c2603014482402818763b0f8304a25028206e3708834663306041ce051781402010180c0804⟩,
  ⟨13,4,[ew34,ew52,ew60,ew64,ew67],localHints 4 0x120544a080b0cc0c0508804420c018401a04 0x6896ff89ee64dd8cbb61aa4298987654332100⟩,
  ⟨13,3,[ew35,ew52,ew60,ew67],decodeHints 0x120900a03128940a040b85c0610130980c010a854020c0b058020d⟩,
  ⟨13,4,[ew43,ew52,ew60,ew64,ew67],decodeHints 0x4c2603004562b0400c2a1500844542a030102c160087c2e17018400a05740044e010600c1a04⟩
]

def nodesBlock9 : Array Node := #[
  ⟨13,4,[ew38,ew52,ew60,ew64,ew67],localHints 4 0x120544a160f85c0c0508804420c018401a04 0x6876ff83ee67dd80cc6baa3298767653432010⟩,
  ⟨13,3,[ew44,ew48,ew56,ew67],decodeHints 0x271381005269340c05008043a37261300a060180c3a33020104633⟩,
  ⟨13,4,[ew44,ew48,ew60,ew64,ew67],decodeHints 0x148a40c05028ac0a061d8ec3e69150140c05008042021118404a25028181a1f13834060302010460d⟩,
  ⟨13,3,[ew44,ew51,ew59,ew64],localHints 4 0x1389a051f004222b0e8a84617 0xaa4699268832776504300210⟩,
  ⟨13,4,[ew44,ew51,ew60,ew64,ew67],decodeHints 0x148a41001158ac106a008ec0211028146e01088042021118400808178102c16008442e17020344604⟩,
  ⟨13,4,[ew44,ew52,ew56,ew64,ew67],decodeHints 0x130980c05158141005008040a2a028206e37089a420210e84048240281818111383006030e8300804⟩,
  ⟨13,4,[ew44,ew52,ew59,ew64,ew67],decodeHints 0x130980c010281476010f804542a031a802370087c20210e84006061780c2a1500844060c0e80c2e17⟩,
  ⟨13,5,[ew44,ew52,ew60,ew64,ew67],localHints 5 0x98569c1da6c549a040dd321f750bc0a6c033a44e01358444203118742004 0x85e8cdd196b435036b4abc95adc2d63420a6b9508b18c26b433a85ada4e6242030905088c20110465288427b5ae5adcd6b16b521093192841cc6108822904300820⟩,
  ⟨13,4,[ew27,ew52,ew60,ew64,ew67],localHints 4 0x130544a081b85c0a060f844020c018342004 0xff899893ee36dd9cbb62aa3198987655432100⟩,
  ⟨13,3,[ew28,ew52,ew64,ew67],decodeHints 0x130980c01128940a040b058020d120900a030a854020c0b85c0610⟩,
  ⟨13,4,[ew47,ew52,ew60,ew64,ew67],decodeHints 0x52290400448240280c2a15008304a25028102c16008342e17018840c0508805d6031180c2004⟩,
  ⟨13,4,[ew33,ew52,ew60,ew64,ew67],localHints 4 0x982a2a030582e210287c22010600c1a04 0xeeb42b32dd43ccb0aa41992877645432321010⟩,
  ⟨13,3,[ew48,ew51,ew60,ew63],localHints 4 0x9c4c018a43a3e060944e16 0x996726528827065044030210⟩,
  ⟨13,4,[ew48,ew51,ew60,ew64,ew67],localHints 4 0x149b4563b1287c6608178582e03060344e04 0xff8edd84c443bb2a12943408706655430210⟩,
  ⟨13,4,[ew48,ew52,ew56,ew60,ew67],decodeHints 0x120900a06148a410050180c4a25028206633061a41a1f0e8344c2603014220c1183002010e8440804⟩,
  ⟨13,4,[ew48,ew52,ew60,ew63,ew67],decodeHints 0x148a448240280c063b0f80c4a25029b41a1f0e83406330188402051780402110e8042a15008302c16⟩
]

def nodesBlock10 : Array Node := #[
  ⟨13,5,[ew48,ew52,ew60,ew64,ew67],localHints 5 0xa53e241da784a9d040cd3221768bc0c6e0287c02ec1180cd60c138741a04 0x36e94bd29adcad665e08dc116b334c455cc331946258825d433a856ba4e611046a50842118c184826346107b5ae5adcd6b16b109225250631c84398c52104300820⟩,
  ⟨13,4,[ew25,ew52,ew60,ew64,ew67],localHints 4 0x13090182a0b07c660803014021101840080d 0xff75ee87545dcc71bb5a911287665454331210⟩,
  ⟨13,4,[ew31,ew52,ew60,ew64,ew67],localHints 4 0x4c24128dc2e21040180a0101830080d 0xdd75cc532332bb51a110993875654432321010⟩,
  ⟨13,4,[ew51,ew52,ew59,ew60,ew64],decodeHints 0xa8540211148a41001158ac2c160087c2e17019a808080e8104c26030040c031180c0a050e818542a⟩,
  ⟨13,4,[ew51,ew52,ew60,ew63,ew64],decodeHints 0x148a42a1500830562b0400c2c16009b408080e8102e17018840a01138040a060e81448240280c4a25⟩,
  ⟨13,5,[ew51,ew52,ew60,ew64,ew67],localHints 5 0xa5422b500542c9d0f85d342104015de27089b802ee11830d803178343a04 0x97e963d2def4e5247e0c3c19ef25c864d88bb112932cc00806f784210a6a09d4094d273092408480424610085c17b9ab5b12962d6a4a50631c84398c52102310400⟩,
  ⟨13,4,[ew15,ew52,ew60,ew64,ew67],localHints 4 0x130900c3b0b05c0a080887c020c1080c1a04 0xffd9ee9dcc649890bb06aa0398987655432210⟩,
  ⟨13,3,[ew16,ew60,ew64,ew67],decodeHints 0x130980c01120900a030a854020c128940a040b058020d0b85c0610⟩,
  ⟨13,4,[ew52,ew55,ew60,ew64,ew67],decodeHints 0x4c260300448240280c2a150083010050f8044203128940a040b058020d0b85c0610023c03a04⟩,
  ⟨13,4,[ew21,ew52,ew60,ew64,ew67],localHints 4 0x522b0a8202c170801422010600c1a04 0xdda4cca2bb430a109941882766545432321010⟩,
  ⟨13,3,[ew52,ew56,ew59,ew63],localHints 4 0x4627268989824020f82a0d 0x469416911481776355432210⟩,
  ⟨13,4,[ew52,ew56,ew59,ew64,ew67],localHints 4 0x131bc4811178544e2a030dc660c0205c060d 0xff7edd4c9417b1aa14918873633035432210⟩,
  ⟨13,4,[ew52,ew56,ew60,ew63,ew67],decodeHints 0x130984824029bc1811118300205178040211118042a15128940a04020dc22041981008100b058020d⟩,
  ⟨13,5,[ew52,ew56,ew60,ew64,ew67],localHints 5 0x99462451019e42f380040625028206e2708a7866230626c20f10e810d60d 0xcb696fd2ed6cbde87e0f6c1defbdac741d8b5a108ab9d47be8e74def422435c90c88cf113e007400f789c202da26084b1014029d2240847114c500c022084310020⟩,
  ⟨13,4,[ew13,ew52,ew60,ew64,ew67],localHints 4 0x130ac2a1112834660604014021f1080c1804 0xff85ee72dd5cbb87545a292387665454232100⟩,
  ⟨13,4,[ew19,ew52,ew60,ew64,ew67],localHints 4 0x29120ec4a17080180a0101830080d 0xcc65bb53a33299510110883765654432321010⟩
]

def nodesBlock11 : Array Node := #[
  ⟨13,4,[ew52,ew59,ew60,ew63,ew64],decodeHints 0x130982a15009bc06061180c0a01138040a061181448240b058020d150a80c040b85c0610128940a04⟩,
  ⟨13,5,[ew52,ew59,ew60,ew64,ew67],localHints 5 0x994815510440af4139c0182f1501940160087c461701a7020f30e834d804 0xb76ad0d59ce5e56749e0e725294af07b60eb5ded64a6a37568a54d6b9a9525ad3088ce7039e283c4e701a012d805300b5894229d004a007394c500c022084310020⟩,
  ⟨13,4,[ew6,ew52,ew60,ew64,ew67],localHints 4 0x148902a0c150dc2008028183e010880c4204 0xff84ee72dd4c7b784a45212978764543212100⟩,
  ⟨13,4,[ew8,ew52,ew60,ew64,ew67],localHints 4 0x26158ec4a16068140c010880c0810 0xcc546b654a4399618847011065654343221010⟩,
  ⟨13,5,[ew52,ew60,ew63,ew64,ew67],localHints 5 0x18222452055460c7b08ce02f1281542270b0053e0d7a874dc170200c4210 0xa62a0e7318c6334673990c994a13b148628e70ae2a2ac26584a552b4148419843208a221b9e883d0e70da34296362c6a52128198603800600ca3008830906210020⟩,
  ⟨13,6,[ew52,ew60,ew64,ew67],localHints 5 0x133f048fb03055f411060bc4a057c8204e1600be03e0d1185c3a0401bdc4210 0x6aefb9521b6d2f7d2e0b38e1994ef93ce10c0ee33cd7668e9638d6bace9329211921d12a210791c42a16c6912c2916b5212828066390262906310020⟩,
  ⟨14,8,[ew54,ew62,ew66,ew68,ew69],localHints 6 0x38500c81424480581c34060983c12151e844181b0102028000f0282c010f8342e04018f04210 0x80c7a181b3e181b79e80c3cc7083df71a79f71a3cf70878871a31d7086dd70830c71a6da4c33d94d56194d53cf4c36034d53174c35974c330c4d55954d12144c34944c32084d14910843d008a39008a3cf08438408a30d0842cd08430c08a2ca0862090841c90842080861c60800c50840450840c3080040⟩
]

def nodesGet (i : Nat) : Option Node :=
  if i < 96 then
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
  else
    if i < 144 then
      if i < 112 then
        nodesBlock6[(i-96)]?
      else
        if i < 128 then
          nodesBlock7[(i-112)]?
        else
          nodesBlock8[(i-128)]?
    else
      if i < 160 then
        nodesBlock9[(i-144)]?
      else
        if i < 176 then
          nodesBlock10[(i-160)]?
        else
          nodesBlock11[(i-176)]?

def fastViews : QFast.Table View := ⟨16,viewsGet⟩

def fastNodes : QFast.Table Node := ⟨183,nodesGet⟩

end SignedProjection



namespace SignedProjection

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockRoots_0 : QFast.passBlock (QFast.checkRootAt fastViews fastNodes) 0 8 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockRoots_8 : QFast.passBlock (QFast.checkRootAt fastViews fastNodes) 8 8 = true := by decide +kernel

theorem joinRoots_0_0 : QFast.passBlock (QFast.checkRootAt fastViews fastNodes) 0 16 = true :=
  @QFast.merge_blocks (QFast.checkRootAt fastViews fastNodes) 0 8 8 blockRoots_0 blockRoots_8

theorem certifiedRoots : QFast.passBlock (QFast.checkRootAt fastViews fastNodes) 0 16 = true := joinRoots_0_0

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
theorem blockNodes_120 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 120 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_126 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 126 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_132 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 132 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_138 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 138 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_144 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 144 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_150 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 150 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_156 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 156 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_162 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 162 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_168 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 168 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_174 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 174 6 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_180 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 180 3 = true := by decide +kernel

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

theorem joinNodes_0_120 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 120 12 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 120 6 6 blockNodes_120 blockNodes_126

theorem joinNodes_0_132 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 132 12 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 132 6 6 blockNodes_132 blockNodes_138

theorem joinNodes_0_144 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 144 12 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 144 6 6 blockNodes_144 blockNodes_150

theorem joinNodes_0_156 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 156 12 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 156 6 6 blockNodes_156 blockNodes_162

theorem joinNodes_0_168 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 168 12 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 168 6 6 blockNodes_168 blockNodes_174

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

theorem joinNodes_1_120 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 120 24 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 120 12 12 joinNodes_0_120 joinNodes_0_132

theorem joinNodes_1_144 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 144 24 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 144 12 12 joinNodes_0_144 joinNodes_0_156

theorem joinNodes_1_168 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 168 15 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 168 12 3 joinNodes_0_168 blockNodes_180

theorem joinNodes_2_0 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 48 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 0 24 24 joinNodes_1_0 joinNodes_1_24

theorem joinNodes_2_48 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 48 48 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 48 24 24 joinNodes_1_48 joinNodes_1_72

theorem joinNodes_2_96 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 96 48 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 96 24 24 joinNodes_1_96 joinNodes_1_120

theorem joinNodes_2_144 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 144 39 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 144 24 15 joinNodes_1_144 joinNodes_1_168

theorem joinNodes_3_0 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 96 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 0 48 48 joinNodes_2_0 joinNodes_2_48

theorem joinNodes_3_96 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 96 87 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 96 48 39 joinNodes_2_96 joinNodes_2_144

theorem joinNodes_4_0 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 183 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 0 96 87 joinNodes_3_0 joinNodes_3_96

theorem certifiedNodes : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 183 = true := joinNodes_4_0

end SignedProjection

namespace SignedProjection
def bMatches (z : Option View) : Bool :=
  match z with
  | none => false
  | some v => vg v == (0xe8e8e800e8808000 : Word) && vk v == 9 && (vs v).toFinset == Direct64.cols.toFinset

theorem rootNegative : ¬ CoreSigned.build signedOps (0xe8e8e800e8808000 : BitVec 64) 9 Direct64.cols.toFinset := by
  have shape : bMatches (QFast.get fastViews 15) = true := by decide +kernel
  cases ev : QFast.get fastViews 15 with
  | none => simp [ev, bMatches] at shape
  | some v =>
    have valid := QFast.certified_view fastViews fastNodes certifiedRoots certifiedNodes ev
    simp only [ev,bMatches,Bool.and_eq_true,beq_iff_eq] at shape
    change ¬ CoreSigned.build signedOps (vg v) (vk v) (vs v).toFinset at valid
    rwa [shape.1.1,shape.1.2,shape.2] at valid
end SignedProjection
end PEqualNP.Outside.L_meta_12222_aux

open PEqualNP.Outside.L_meta_12222_aux in
theorem PEqualNP.Outside.L_meta_12222 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3907577856 * 2 ^ 32 + 3900735488) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3907577856 * 2 ^ 32 + 3900735488) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  LowerSymSix.finish SignedProjection.rootNegative
