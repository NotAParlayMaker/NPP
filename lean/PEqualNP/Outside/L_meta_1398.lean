import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1398

-- The low five bits test neighboring pairs in cyclic order. The next five
-- test the pairs at distance two, again in cyclic order.
def leaf (i : BitVec 3) : BitVec 10 :=
  if i = 0 then 305 else if i = 1 then 579 else if i = 2 then 166 else if i = 3 then 332 else 664

def gate (op : Bool) (a b : BitVec 10) : BitVec 10 := if op then a &&& b else a ||| b

def possible : ℕ → BitVec 10 → Prop
  | 0, w => ∃ i, w = leaf i
  | k + 1, w => ∃ op a b, possible k a ∧ possible k b ∧ w = gate op a b

def test (j : Fin 10) (i : Fin 5) := (leaf (BitVec.ofNat 3 i.val)).getLsbD j.val

def tracks (k : ℕ) (f : (Fin 5 → Bool) → Bool) :=
  ∃ w, possible k w ∧ ∀ j : Fin 10, f (test j) = w.getLsbD j.val

-- Repeating a child at an AND handles all the formulas shorter than three levels.
lemma carry {k f} (h : tracks k f) : tracks (k+1) f := by
  obtain ⟨w,hw,obs⟩ := h
  exact ⟨w,⟨true,w,w,hw,hw,by simp [gate]⟩,obs⟩

lemma combine {k f g} (hf : tracks k f) (hg : tracks k g) :
    tracks (k+1) (fun x => f x && g x) ∧ tracks (k+1) (fun x => f x || g x) := by
  obtain ⟨a,ha,fa⟩ := hf
  obtain ⟨b,hb,gb⟩ := hg
  exact ⟨⟨_,⟨true,a,b,ha,hb,rfl⟩,fun j => by simp [gate,fa j,gb j]⟩,
    ⟨_,⟨false,a,b,ha,hb,rfl⟩,fun j => by simp [gate,fa j,gb j]⟩⟩

lemma eight_leaves (a b c d e f g h : BitVec 3) (o p q r s t u : Bool) :
    gate o (gate p (gate r (leaf a) (leaf b)) (gate s (leaf c) (leaf d)))
      (gate q (gate t (leaf e) (leaf f)) (gate u (leaf g) (leaf h))) ≠ 31 := by
  unfold gate leaf
  bv_decide

lemma excludes (w : BitVec 10) (hw : possible 3 w) : w ≠ 31 := by
  obtain ⟨o,l,v,hl,hv,rfl⟩ := hw
  obtain ⟨p,ab,cd,hab,hcd,rfl⟩ := hl
  obtain ⟨q,ef,gh,hef,hgh,rfl⟩ := hv
  obtain ⟨r,_,_,⟨a,rfl⟩,⟨b,rfl⟩,rfl⟩ := hab
  obtain ⟨s,_,_,⟨c,rfl⟩,⟨d,rfl⟩,rfl⟩ := hcd
  obtain ⟨t,_,_,⟨e,rfl⟩,⟨f,rfl⟩,rfl⟩ := hef
  obtain ⟨u,_,_,⟨g,rfl⟩,⟨h,rfl⟩,rfl⟩ := hgh
  exact eight_leaves a b c d e f g h o p q r s t u

lemma tests_target : ∀ j : Fin 10,
    ((test j 0 && test j 1) || (test j 1 && test j 2) || (test j 2 && test j 3) ||
      (test j 3 && test j 4) || (test j 4 && test j 0)) = (31 : BitVec 10).getLsbD j.val := by decide

end PEqualNP.Outside.L_meta_1398

theorem PEqualNP.Outside.L_meta_1398 : ¬ (∀ T : ℕ → Set ((Fin 5 → Bool) → Bool), (∀ i : Fin 5, (fun x : Fin 5 → Bool => x i) ∈ T 0) → (∀ (k : ℕ) (f : (Fin 5 → Bool) → Bool), f ∈ T k → f ∈ T (k + 1)) → (∀ (k : ℕ) (f g : (Fin 5 → Bool) → Bool), f ∈ T k → g ∈ T k → (fun y : Fin 5 → Bool => f y && g y) ∈ T (k + 1) ∧ (fun y : Fin 5 → Bool => f y || g y) ∈ T (k + 1)) → (fun z : Fin 5 → Bool => (z 0 && z 1) || (z 1 && z 2) || (z 2 && z 3) || (z 3 && z 4) || (z 4 && z 0)) ∈ T 3) := by
  intro alleged
  obtain ⟨w,hw,obs⟩ := alleged (fun k => {f | PEqualNP.Outside.L_meta_1398.tracks k f})
    (fun i => ⟨_,⟨BitVec.ofNat 3 i.val,rfl⟩,fun _ => rfl⟩)
    (fun _ _ => PEqualNP.Outside.L_meta_1398.carry)
    (fun _ _ _ => PEqualNP.Outside.L_meta_1398.combine)
  apply PEqualNP.Outside.L_meta_1398.excludes w hw
  exact BitVec.eq_of_getLsbD_eq fun j hj => (obs ⟨j,hj⟩).symm.trans (PEqualNP.Outside.L_meta_1398.tests_target ⟨j,hj⟩)
