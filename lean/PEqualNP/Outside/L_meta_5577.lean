import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5577_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents Finset

def rel (u v : Fin 4) := (4703 : Nat).testBit (4*u.val+v.val)
def val (r : Nat) : List Bool := List.ofFn fun i : Fin 8 => r.testBit i.val

theorem upper : RepSizeAtMost rel 7 := by
  let C : Circuit := ⟨[⟨.or,[4,6]⟩,⟨.and,[1,8]⟩,⟨.and,[2,5]⟩,⟨.and,[3,4]⟩,
    ⟨.or,[0,9]⟩,⟨.or,[10,11]⟩,⟨.or,[12,13]⟩],14⟩
  exact ⟨C, by simp [Monotone2, C], by decide, by decide⟩

-- Each test cell pairs an accepting promise row with a rejecting promise row.
-- The first nine cells each have exactly one raw signal that is on in the
-- positive row and off in the negative row. The last cell tests overlap.
def pos (i : Fin 10) := ([17,18,36,24,18,36,66,66,24,18] : List Nat).getD i.val 0
def neg (i : Fin 10) := ([20,20,34,20,34,20,34,72,72,72] : List Nat).getD i.val 0
def tag (i : Fin 9) := ([0,1,2,3,4,5,6,1,4] : List Nat).getD i.val 0

private theorem rows (C : Circuit) (h : Represents rel C) (i : Fin 10) :
    C.eval (val (pos i)) = true ∧ C.eval (val (neg i)) = false := by
  have test : ∀ i : Fin 10, ∃ a b c d : Fin 4,
      val (pos i) = oneEach a b ∧ val (neg i) = oneEach c d ∧ rel a b = true ∧ rel c d = false := by decide
  obtain ⟨a,b,c,d,hp,hn,one,zero⟩ := test i
  exact ⟨hp ▸ (h a b).trans one, hn ▸ (h c d).trans zero⟩

private def run (gs : List Gate) (r : Nat) :=
  gs.foldl (fun vs g => vs ++ [g.op.eval (g.inputs.map fun k => vs.getD k false)]) (val r)

private def splitAt (gs : List Gate) (i : Fin 10) (w : Nat) :=
  (run gs (pos i)).getD w false = true ∧ (run gs (neg i)).getD w false = false

private theorem snoc (gs : List Gate) (g : Gate) (r : Nat) :
    run (gs++[g]) r = run gs r ++ [g.op.eval (g.inputs.map fun k => (run gs r).getD k false)] := by
  simp [run,List.foldl_append]

private theorem end_length (gs : List Gate) (r : Nat) : (run gs r).length = 8 + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run,val]
  | append_singleton gs g ih => simp [snoc,ih,Nat.add_assoc]

private theorem pop {gs : List Gate} {g : Gate} {w : Nat} (h : w ≠ 8+gs.length) (r : Nat) :
    (run (gs++[g]) r).getD w false = (run gs r).getD w false := by
  rw [snoc]
  by_cases small : w < (run gs r).length
  · exact List.getD_append _ _ _ _ small
  · rw [List.getD_eq_default _ _ (by simp [end_length] at *; omega), List.getD_eq_default _ _ (by omega)]

private theorem topval (gs : List Gate) (g : Gate) (r : Nat) :
    (run (gs++[g]) r).getD (8+gs.length) false =
    g.op.eval (g.inputs.map fun w => (run gs r).getD w false) := by
  rw [snoc, ← end_length gs r, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero]

private def labels (f : Fin 10 → Nat) : Finset Nat := univ.image f

private theorem raw_forced (f : Fin 10 → Nat) (ok : ∀ i, splitAt [] i (f i)) :
    ∀ i : Fin 9, f i.castSucc = tag i := by
  intro i
  have h := ok i.castSucc
  change (val (pos i.castSucc)).getD _ false = true ∧ _ at h
  have small : f i.castSucc < 8 := by
    by_contra! fail
    have := List.getD_eq_default (val (pos i.castSucc)) false (show (val (pos i.castSucc)).length ≤ _ by simpa [val] using fail)
    exact Bool.noConfusion (this.symm.trans h.1)
  exact (show ∀ (i : Fin 9) (w : Fin 8), splitAt [] i.castSucc w.val → w.val=tag i from by unfold splitAt; decide) i ⟨_,small⟩ h

private theorem raw_count (f : Fin 10 → Nat) (ok : ∀ i, splitAt [] i (f i)) :
    7 ≤ (labels f).card := by
  have sub : range 7 ⊆ labels f := by
    intro w hw
    have found : ∃ i : Fin 9, tag i=w := (show ∀ w : Fin 7, ∃ i : Fin 9, tag i=w.val from by decide) ⟨w,mem_range.mp hw⟩
    obtain ⟨i,rfl⟩ := found
    exact mem_image.mpr ⟨i.castSucc,mem_univ _,raw_forced f ok i⟩
  simpa using card_le_card sub

private def route (f : Fin 10 → Nat) (w a b : Nat) (c : Fin 10 → Bool) (i : Fin 10) :=
  if f i = w then if c i then a else b else f i

private def Side (c : Fin 10 → Bool) : Prop :=
  (∀ i k, pos i=pos k → c i=c k) ∨ (∀ i k, neg i=neg k → c i=c k)

-- The cells of each label are closed under the row-column crosses in our test set.
private def Rect (f : Fin 10 → Nat) : Prop :=
  ∀ i k z, pos z=pos i → neg z=neg k → f i=f k → f z=f i

private theorem rect_of_route {f : Fin 10 → Nat} {w a b : Nat} {c : Fin 10 → Bool}
    (r : Rect f) (s : Side c)
    (refines : ∀ i k, route f w a b c i=route f w a b c k → f i=f k) :
    Rect (route f w a b c) := by
  intro i k z p n same
  have old := refines i k same
  have rz := r i k z p n old
  by_cases hi : f i=w
  · have hk := old.symm.trans hi
    have hz := rz.trans hi
    rcases s with pc|nc
    · simp [route,hi,hz,pc z i p]
    · rw [same]
      simp [route,hk,hz,nc z k n]
  · simp [route,rz,hi]

-- Splitting one label gains at most one distinct label. A gain of one
-- requires both new labels to stay separate from every unchanged label.
private theorem count_route (f : Fin 10 → Nat) (w a b : Nat) (c : Fin 10 → Bool) :
    (labels (route f w a b c)).card ≤ (labels f).card+1 ∧
    ((labels f).card+1 ≤ (labels (route f w a b c)).card →
      ∀ i k, route f w a b c i=route f w a b c k → f i=f k) := by
  classical
  let S := labels f
  let T := S.erase w
  have memS (i : Fin 10) : f i ∈ S := mem_image.mpr ⟨i,mem_univ _,rfl⟩
  by_cases hw : w ∈ S
  · have hc : T.card+1=S.card := card_erase_add_one hw
    have incl : labels (route f w a b c) ⊆ insert a (insert b T) := by
      intro z hz
      obtain ⟨i,_,rfl⟩ := mem_image.mp hz
      by_cases hi : f i=w
      · cases cc : c i <;> simp [route,hi,cc]
      · exact (by simpa only [route,ite_eq_right hi] using
          (mem_insert_of_mem (mem_insert_of_mem (mem_erase.mpr ⟨hi,memS i⟩)) : f i ∈ insert a (insert b T)))
    have hBound := card_le_card incl
    have h1 := card_insert_le a (insert b T)
    have h2 := card_insert_le b T
    change _ ≤ S.card+1 ∧ (S.card+1 ≤ _ → _)
    refine ⟨by omega, ?_⟩
    intro tight
    have ha : a ∉ T := by
      intro bad
      have eq : insert a (insert b T)=insert b T := insert_eq_of_mem (mem_insert_of_mem bad)
      rw [eq] at hBound
      omega
    have hb : b ∉ T := by
      intro bad
      rw [insert_eq_of_mem bad] at h1 hBound
      omega
    intro i k eq
    by_cases hi : f i=w <;> by_cases hk : f k=w
    · exact hi.trans hk.symm
    · have mem : f k ∈ T := mem_erase.mpr ⟨hk,memS k⟩
      cases cc : c i <;> simp only [route,hi,hk,cc,ite_true,ite_false,Bool.false_eq_true] at eq
      · exact (hb (eq ▸ mem)).elim
      · exact (ha (eq ▸ mem)).elim
    · have mem : f i ∈ T := mem_erase.mpr ⟨hi,memS i⟩
      cases cc : c k <;> simp only [route,hi,hk,cc,ite_true,ite_false,Bool.false_eq_true] at eq
      · exact (hb (eq ▸ mem)).elim
      · exact (ha (eq ▸ mem)).elim
    · simpa [route,hi,hk] using eq
  · have same : route f w a b c = f := by
      funext i
      have ne : f i ≠ w := fun eq => hw (eq ▸ memS i)
      simp [route,ne]
    rw [same]
    exact ⟨by omega,fun _ i k h => h⟩

private def firstPin (g : Gate) := g.inputs.getD 0 0
private def secondPin (g : Gate) := g.inputs.getD 1 (firstPin g)

-- AND routes by the rejecting row, OR by the accepting row.
private def choosePin (g : Gate) (P N : List Bool) :=
  match g.op with
  | .and => !(N.getD (firstPin g) false)
  | _ => P.getD (firstPin g) false

private theorem pin_separates (g : Gate) (kind : g.op=.and ∨ g.op=.or)
    (len : g.inputs.length ≤ 2) (P N : List Bool)
    (hp : g.op.eval (g.inputs.map fun w => P.getD w false) = true)
    (hn : g.op.eval (g.inputs.map fun w => N.getD w false) = false) :
    let k := if choosePin g P N then firstPin g else secondPin g
    P.getD k false = true ∧ N.getD k false = false := by
  obtain ⟨op,ls⟩ := g
  rcases ls with _|⟨a,_|⟨b,cs⟩⟩
  · rcases kind with h|h <;> cases h <;> contradiction
  · rcases kind with h|h <;> cases h <;>
      simpa [choosePin,firstPin,secondPin,GateOp.eval] using And.intro hp hn
  · have tail : cs = [] := List.length_eq_zero_iff.mp (by simpa using len)
    subst cs
    rcases kind with h|h <;> cases h <;>
      simp only [List.map_cons,List.map_nil,GateOp.eval,List.all_cons,List.all_nil,
        List.any_cons,List.any_nil,id_eq,Bool.and_true,Bool.or_false] at hp hn
    · cases hh : N.getD a false <;>
        simp [choosePin,firstPin,secondPin] <;> simp_all
    · cases hh : P.getD a false <;>
        simp [choosePin,firstPin,secondPin] <;> simp_all

private theorem peel (gs : List Gate) (g : Gate) (kind : g.op=.and ∨ g.op=.or)
    (len : g.inputs.length ≤ 2) (f : Fin 10 → Nat) (safe : ∀ i, splitAt (gs++[g]) i (f i)) :
    ∃ f' : Fin 10 → Nat, (∀ i,splitAt gs i (f' i)) ∧
      (labels f').card ≤ (labels f).card+1 ∧
      ((labels f).card+1 ≤ (labels f').card → Rect f → Rect f') := by
  let w := 8+gs.length
  let c (i : Fin 10) := choosePin g (run gs (pos i)) (run gs (neg i))
  let f' := route f w (firstPin g) (secondPin g) c
  have side : Side c := by
    rcases kind with hh|hh
    · exact Or.inr (fun i k h => by simp [c,choosePin,hh,h])
    · exact Or.inl (fun i k h => by simp [c,choosePin,hh,h])
  have sizes := count_route f w (firstPin g) (secondPin g) c
  refine ⟨f',?_,sizes.1,fun tight rect => rect_of_route rect side (sizes.2 tight)⟩
  intro i
  have h := safe i
  by_cases hi : f i=w
  · rw [hi] at h
    obtain ⟨hp,hn⟩ := h
    rw [show w=8+gs.length from rfl, topval] at hp hn
    simpa only [f',route,hi,ite_true,splitAt,c] using pin_separates g kind len _ _ hp hn
  · obtain ⟨hp,hn⟩ := h
    rw [pop hi] at hp hn
    simpa only [f',route,hi,ite_false,splitAt] using And.intro hp hn

-- With seven raw labels required, a budget of seven forces a gain at every
-- split, so all the routed rectangles retain their cross-closure. At the
-- inputs, cell 9 would lie in both the rectangles for labels 1 and 4.
private theorem obstruction (gs : List Gate) (mono : ∀ g ∈ gs,
    (g.op=.and ∨ g.op=.or) ∧ g.inputs.length ≤ 2) (f : Fin 10 → Nat)
    (safe : ∀ i, splitAt gs i (f i)) :
    7 ≤ (labels f).card+gs.length ∧ ((labels f).card+gs.length ≤ 7 → ¬Rect f) := by
  induction gs using List.reverseRecOn generalizing f with
  | nil =>
    refine ⟨by simpa using raw_count f safe,fun _ rect => ?_⟩
    have h (i : Fin 9) := raw_forced f safe i
    have a : f 1=1 := h 1
    have b : f 7=1 := h 7
    have c : f 4=4 := h 4
    have d : f 8=4 := h 8
    have one := rect 1 7 9 (by decide) (by decide) (a.trans b.symm)
    have four := rect 4 8 9 (by decide) (by decide) (c.trans d.symm)
    omega
  | append_singleton gs g ih =>
    have hg := mono g (by simp)
    obtain ⟨f',safe',bound,trans⟩ := peel gs g hg.1 hg.2 f safe
    obtain ⟨need,fail⟩ := ih (fun g' h => mono g' (by simp [h])) f' safe'
    simp only [List.length_append,List.length_singleton]
    exact ⟨by omega,fun tight rect => fail (by omega) (trans (by omega) rect)⟩

theorem lower : ¬ RepSizeAtMost rel 6 := by
  rintro ⟨C,mono,small,correct⟩
  have h := obstruction C.gates (fun g hg => mono g hg) (fun _ => C.output) (rows C correct)
  have one : (labels fun _ => C.output).card = 1 := by
    have he : labels (fun _ => C.output) = {C.output} := by
      ext x
      simp [labels]
      exact eq_comm
    rw [he,card_singleton]
  change C.gates.length ≤ 6 at small
  exact h.2 (by omega) (fun _ _ _ _ _ _ => rfl)

end PEqualNP.Outside.L_meta_5577_aux

open PEqualNP.Outside.L_meta_5577_aux

theorem PEqualNP.Outside.L_meta_5577 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (4703 : ℕ).testBit (4 * u.val + v.val)) 7 ∧
  ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (4703 : ℕ).testBit (4 * u.val + v.val)) 6 := ⟨upper, lower⟩
