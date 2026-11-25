import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17727

def hits {n : ℕ} (gs : List (Fin n × List (Fin n))) (r : ℕ) : Bool :=
  gs.any fun g => r.testBit g.1.val && g.2.any (fun v => r.testBit v.val)

theorem partition (xs : List ℕ) (f p : ℕ → Bool) :
    (xs.filter f).length = ((xs.filter p).filter f).length +
      ((xs.filter fun z => !(p z)).filter f).length := by
  induction xs with
  | nil => simp
  | cons a as ih =>
    cases hp : p a <;> cases hf : f a <;> simp [hp,hf,ih] <;> omega

end PEqualNP.Outside.L_meta_17727

open PEqualNP.Outside.L_meta_17727

theorem PEqualNP.Outside.L_meta_17727 : (∀ (x1 : ℕ) (x2 x3 : List ℕ) (x4 : Finset (Fin x1)),   (∀ x5 ∈ x2, x5 ∉ x3) →     (∀ x6 ∈ x2, ∃ x8 ∈ x4, x6.testBit ↑x8 = Bool.true) →       (∀ x7 ∈ x2, ∀ (x9 : Fin x1), x7.testBit ↑x9 = Bool.true → ∃ (x11 : Fin x1), ∀ x12 ∈ x2 ++ x3, (x12.testBit ↑x9 && x12.testBit ↑x11) = Decidable.decide (x12 = x7)) →         ∃ (x8 : List (Fin x1 × List (Fin x1))),           (∀ x9 ∈ x8, (2 : ℕ) ≤ x9.2.length) ∧             have x9 : ℕ → Bool := fun (x9 : ℕ) => x8.any fun (x10 : Fin x1 × List (Fin x1)) => x9.testBit ↑x10.1 && x10.2.any fun (x11 : Fin x1) => x9.testBit ↑x11;             (List.map (fun (x10 : Fin x1 × List (Fin x1)) => x10.2.length + (1 : ℕ)) x8).sum + (2 : ℕ) * (List.filter (fun (x10 : ℕ) => !x9 x10) x2).length ≤ x2.length + x4.card ∧ ∀ x10 ∈ x3, x9 x10 = Bool.false) := by
  classical
  intro n R N S
  induction S using Finset.induction_on generalizing R with
  | empty =>
    intro _ cover _
    cases R with
    | nil => exact ⟨[],by simp,by simp⟩
    | cons a as => simpa using cover a (by simp)
  | @insert u S fresh ih =>
    intro dis cover pair
    let p (t : ℕ) := t.testBit u.val
    let yes := R.filter p
    let no := R.filter fun t => !(p t)
    have orig {t : ℕ} (ht : t ∈ no) : t ∈ R := (List.mem_filter.mp ht).1
    have cov0 (t : ℕ) (ht : t ∈ no) : ∃ v ∈ S, t.testBit v.val = true := by
      obtain ⟨v,hv,bit⟩ := cover t (orig ht)
      rcases Finset.mem_insert.mp hv with h | h
      · subst v
        have hp := (List.mem_filter.mp ht).2
        simp [p,bit] at hp
      · exact ⟨v,h,bit⟩
    obtain ⟨gs,wide,cost,neg⟩ := ih no (fun t ht => dis t (orig ht)) cov0 (fun t ht v hv => by
      obtain ⟨w,hw⟩ := pair t (orig ht) v hv
      refine ⟨w,fun k hk => hw k ?_⟩
      exact (List.mem_append.mp hk).elim (fun h => List.mem_append_left _ (orig h)) (List.mem_append_right _))
    change (gs.map fun g => g.2.length+1).sum + 2*(no.filter fun r => !(hits gs r)).length ≤ no.length+S.card at cost
    change ∀ t ∈ N, hits gs t = false at neg
    have lens : R.length = yes.length + no.length := by
      simpa [yes,no] using partition R (fun _ => true) p
    have card := Finset.card_insert_of_notMem fresh
    by_cases small : yes.length < 2
    · refine ⟨gs,wide,?_,neg⟩
      change (gs.map fun g => g.2.length+1).sum + 2*(R.filter fun r => !(hits gs r)).length ≤ _
      have part := partition R (fun r => !(hits gs r)) p
      change _ = (yes.filter fun r => !(hits gs r)).length + (no.filter fun r => !(hits gs r)).length at part
      have bound := List.length_filter_le (fun r => !(hits gs r)) yes
      omega
    · have data (a : {r // r ∈ yes}) := pair a.val (List.mem_filter.mp a.property).1 u (List.mem_filter.mp a.property).2
      let leaf (a : {r // r ∈ yes}) : Fin n := (data a).choose
      let leaves := yes.attach.map leaf
      let g : Fin n × List (Fin n) := (u,leaves)
      have lsize : leaves.length = yes.length := by simp [leaves]
      have gw : 2 ≤ g.2.length := by change 2 ≤ leaves.length; omega
      have eval (a : {r // r ∈ yes}) (t : ℕ) (ht : t ∈ R ++ N) :
          (p t && t.testBit (leaf a).val) = decide (t = a.val) := (data a).choose_spec t ht
      have newYes (t : ℕ) (ht : t ∈ yes) : hits (g::gs) t = true := by
        let a : {r // r ∈ yes} := ⟨t,ht⟩
        have h := eval a t (List.mem_append_left _ (List.mem_filter.mp ht).1)
        have both : (p t && t.testBit (leaf a).val) = true := by simpa [a] using h
        obtain ⟨hu,hv⟩ := Bool.and_eq_true_iff.mp both
        have hm : leaf a ∈ leaves := List.mem_map.mpr ⟨a,List.mem_attach _ _,rfl⟩
        have any : (leaves.any fun v => t.testBit v.val) = true := List.any_eq_true.mpr ⟨leaf a,hm,hv⟩
        change ((p t && leaves.any (fun v => t.testBit v.val)) || hits gs t) = true
        simp [hu,any]
      have same : (R.filter fun r => !(hits (g::gs) r)) = no.filter fun r => !(hits gs r) := by
        rw [List.filter_filter]
        apply List.filter_congr
        intro r hr
        cases h : p r with
        | false =>
          change (!((p r && leaves.any (fun v => r.testBit v.val)) || hits gs r)) = _
          simp [h]
        | true =>
          have hn := newYes r (List.mem_filter.mpr ⟨hr,h⟩)
          simp [hn]
      refine ⟨g::gs,?_,?_,?_⟩
      · intro a ha
        rcases List.mem_cons.mp ha with h | h
        · simpa [h] using gw
        · exact wide a h
      · change ((g::gs).map fun a => a.2.length+1).sum + 2*(R.filter fun r => !(hits (g::gs) r)).length ≤ _
        rw [same]
        simp only [List.map_cons,List.sum_cons]
        change leaves.length+1+_+_ ≤ _
        omega
      · intro t ht
        change ((p t && leaves.any (fun v => t.testBit v.val)) || hits gs t) = false
        rw [neg t ht,Bool.or_false]
        cases hp : p t with
        | false => simp
        | true =>
          simp only [Bool.true_and]
          apply List.any_eq_false.mpr
          intro v hv
          obtain ⟨a,_,rfl⟩ := List.mem_map.mp hv
          have ne : t ≠ a.val := by
            intro e
            exact dis a.val (List.mem_filter.mp a.property).1 (e ▸ ht)
          have hx := eval a t (List.mem_append_right _ ht)
          simpa [hp,ne] using hx
