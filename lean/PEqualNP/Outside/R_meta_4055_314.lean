import Mathlib
import PEqualNP.Defs
theorem PEqualNP.Outside.R_meta_4055_314
    (compile : ∀ (E : Finset (Fin 21 × Fin 21)) (r : (Fin 21 × Fin 21) → Fin 42 → Bool) (P : List (Finset Nat × Finset Nat)) (out : Finset Nat),
    let val := fun (b : Fin 42 → Bool) => decide (∀ i ∈ out,
      (P.foldl (fun z p => z ++ [decide (∀ j∈p.1, z.getD j false = true) || decide (∀ j∈p.2, z.getD j false = true)]) (List.ofFn b ++ [false])).getD i false = true)
    (∀ e ∈ E, val (r e) = true) →
    ∃ L : List (Finset (Fin 21 × Fin 21) × Finset (Fin 21 × Fin 21)), L.length ≤ P.length ∧ (∀ p ∈ L, Disjoint p.1 p.2 ∧ p.1 ∪ p.2 ⊆ E) ∧
    ∀ b c : Fin 42 → Bool, (∀ i, c i=false → b i=false) → val c=false →
      L.foldl (fun (K : Finset (Fin 21 × Fin 21) → Prop) (p : Finset (Fin 21 × Fin 21) × Finset (Fin 21 × Fin 21)) (S : Finset (Fin 21 × Fin 21)) =>
    K S ∨ S ⊆ p.1 ∪ p.2 ∧ K p.1 ∧ K p.2) ((fun (b : Fin 42 → Bool) (S : Finset (Fin 21 × Fin 21)) => S=∅ ∨ ∃ i, b i=false ∧ ∀ e ∈ S, r e i=true) b) E)
    (partition : ∀ (U : Finset (Fin 21 × Fin 21)) (L : List (Finset (Fin 21 × Fin 21) × Finset (Fin 21 × Fin 21))), (∀ p∈L, Disjoint p.1 p.2) →
    (∀ a∈U, ∀ b∈U, a≠b → L.countP ((fun (a b : Fin 21 × Fin 21) (p : Finset (Fin 21 × Fin 21) × Finset (Fin 21 × Fin 21)) => decide ((a∈p.1 ∧ b∈p.2) ∨ (a∈p.2 ∧ b∈p.1))) a b) = 1) → U.card ≤ L.length+1)
    (obstruction : let adj := fun (p l : Fin 21) => ([(p.val+20)%21,p.val,(p.val+5)%21,(p.val+7)%21,(p.val+17)%21] : List Nat).contains l.val
    let E := Finset.univ.filter fun e : Fin 21 × Fin 21 => adj e.1 e.2
    let r := fun (e : Fin 21 × Fin 21) (v : Fin 42) => decide (v=Fin.castAdd 21 e.1 ∨ v=Fin.natAdd 21 e.2)
    ∀ L : List (Finset (Fin 21 × Fin 21) × Finset (Fin 21 × Fin 21)), (∀ p ∈ L, Disjoint p.1 p.2 ∧ p.1 ∪ p.2 ⊆ E) →
      (∀ b : Fin 42 → Bool, (∀ e ∈ E, b (Fin.castAdd 21 e.1)=false ∨ b (Fin.natAdd 21 e.2)=false) →
      L.foldl (fun (K : Finset (Fin 21 × Fin 21) → Prop) (p : Finset (Fin 21 × Fin 21) × Finset (Fin 21 × Fin 21)) (S : Finset (Fin 21 × Fin 21)) =>
    K S ∨ S ⊆ p.1 ∪ p.2 ∧ K p.1 ∧ K p.2) ((fun (b : Fin 42 → Bool) (S : Finset (Fin 21 × Fin 21)) => S=∅ ∨ ∃ i, b i=false ∧ ∀ e ∈ S, r e i=true) b) E) → (∃ a∈E, ∃ b∈E, a≠b ∧ 2 ≤ L.countP ((fun (a b : Fin 21 × Fin 21) (p : Finset (Fin 21 × Fin 21) × Finset (Fin 21 × Fin 21)) => decide ((a∈p.1 ∧ b∈p.2) ∨ (a∈p.2 ∧ b∈p.1))) a b)) → 104 ≤ L.length) :
∀ (x1 : List (Finset ℕ × Finset ℕ)) (x2 : Finset ℕ),   have x3 : Fin (21 : ℕ) → Fin (21 : ℕ) → Bool := fun (x3 x4 : Fin (21 : ℕ)) => [(↑x3 + (20 : ℕ)) % (21 : ℕ), ↑x3, (↑x3 + (5 : ℕ)) % (21 : ℕ), (↑x3 + (7 : ℕ)) % (21 : ℕ), (↑x3 + (17 : ℕ)) % (21 : ℕ)].contains ↑x4;   have x4 : (Fin (42 : ℕ) → Bool) → Bool := fun (x4 : Fin (42 : ℕ) → Bool) =>     have x5 : List Bool := List.foldl (fun (x5 : List Bool) (x6 : Finset ℕ × Finset ℕ) => x5 ++ [Decidable.decide (∀ x7 ∈ x6.1, x5.getD x7 Bool.false = Bool.true) || Decidable.decide (∀ x7 ∈ x6.2, x5.getD x7 Bool.false = Bool.true)]) (List.ofFn x4 ++ [Bool.false]) x1;     Decidable.decide (∀ x6 ∈ x2, x5.getD x6 Bool.false = Bool.true);   have x5 : (Fin (42 : ℕ) → Bool) → Prop := fun (x5 : Fin (42 : ℕ) → Bool) => ∀ (x6 x7 : Fin (21 : ℕ)), x3 x6 x7 = Bool.true → x5 (Fin.castAdd (21 : ℕ) x6) = Bool.false ∨ x5 (Fin.natAdd (21 : ℕ) x7) = Bool.false;   (∀ (x6 : ℕ) (x7 : x6 < x1.length), ∀ x8 ∈ x1[x6].1 ∪ x1[x6].2, x8 < (43 : ℕ) + x6) → (∀ x7 ∈ x2, x7 < (43 : ℕ) + x1.length) → (∀ (x8 x9 : Fin (21 : ℕ)), x3 x8 x9 = Bool.true → (x4 fun (x11 : Fin (42 : ℕ)) => Decidable.decide (x11 = Fin.castAdd (21 : ℕ) x8 ∨ x11 = Fin.natAdd (21 : ℕ) x9)) = Bool.true) → (∀ (x9 : Fin (42 : ℕ) → Bool), x5 x9 → (∀ (x11 : Fin (42 : ℕ) → Bool), x5 x11 → (∀ (x13 : Fin (42 : ℕ)), x9 x13 = Bool.true → x11 x13 = Bool.true) → x11 = x9) → x4 x9 = Bool.false) → (104 : ℕ) ≤ x1.length := by
  classical
  intro P out
  let adj := fun (p l : Fin 21) => ([(p.val+20)%21,p.val,(p.val+5)%21,(p.val+7)%21,(p.val+17)%21] : List Nat).contains l.val
  let E := Finset.univ.filter fun e : Fin 21 × Fin 21 => adj e.1 e.2
  let r := fun (e : Fin 21 × Fin 21) (v : Fin 42) => decide (v=Fin.castAdd 21 e.1 ∨ v=Fin.natAdd 21 e.2)
  let val := fun (b : Fin 42 → Bool) => decide (∀ i ∈ out,
      (P.foldl (fun z p => z ++ [decide (∀ j∈p.1, z.getD j false = true) || decide (∀ j∈p.2, z.getD j false = true)]) (List.ofFn b ++ [false])).getD i false = true)
  let safe := fun (b : Fin 42 → Bool) => ∀ p l, adj p l = true → b (Fin.castAdd 21 p) = false ∨ b (Fin.natAdd 21 l) = false
  intro _ _ _ _ _ pos neg
  have accepted : ∀ e ∈ E, val (r e) = true := fun e h => pos e.1 e.2 (Finset.mem_filter.mp h).2
  obtain ⟨L,len,shape,run⟩ := compile E r P out accepted
  let advance := fun (K : Finset (Fin 21 × Fin 21) → Prop) (p : Finset (Fin 21 × Fin 21) × Finset (Fin 21 × Fin 21)) (S : Finset (Fin 21 × Fin 21)) =>
    K S ∨ S ⊆ p.1 ∪ p.2 ∧ K p.1 ∧ K p.2
  let seed := fun (b : Fin 42 → Bool) (S : Finset (Fin 21 × Fin 21)) => S=∅ ∨ ∃ i, b i=false ∧ ∀ e ∈ S, r e i=true
  have works : ∀ b : Fin 42 → Bool, (∀ e∈E, b (Fin.castAdd 21 e.1)=false ∨ b (Fin.natAdd 21 e.2)=false) → L.foldl advance (seed b) E := by
    intro b noEdge
    have startSafe : safe b := fun p l h => noEdge (p,l) (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
    obtain ⟨c,le,maximal⟩ := Finite.exists_le_maximal (p := safe) startSafe
    apply run b c
    · intro i off
      have h := le i
      rw [off] at h
      exact le_antisymm h (Bool.false_le _)
    · apply neg c maximal.prop
      intro d hd up
      have larger : c ≤ d := by
        intro i
        cases h : c i with
        | false => exact Bool.false_le _
        | true => rw [up i h]
      exact le_antisymm (maximal.2 hd larger) larger
  let cross := fun (a b : Fin 21 × Fin 21) (p : Finset (Fin 21 × Fin 21) × Finset (Fin 21 × Fin 21)) => decide ((a∈p.1 ∧ b∈p.2) ∨ (a∈p.2 ∧ b∈p.1))
  by_cases twiceSplit : ∃ a∈E, ∃ b∈E, a≠b ∧ 2 ≤ L.countP (cross a b)
  · exact (obstruction L shape works twiceSplit).trans len
  have countOne (a : Fin 21 × Fin 21) (ha : a∈E) (b : Fin 21 × Fin 21) (hb : b∈E) (ne : a≠b) :
      L.countP (cross a b) = 1 := by
    have low : ¬2 ≤ L.countP (cross a b) := fun h => twiceSplit ⟨a,ha,b,hb,ne,h⟩
    by_contra fail
    have zero : L.countP (cross a b) = 0 := by omega
    have apart (p) (hp : p∈L) : cross a b p = false := Bool.eq_false_iff.mpr (List.countP_eq_zero.mp zero p hp)
    let both (v : Fin 42) := r a v && r b v
    have noEdge (e : Fin 21 × Fin 21) (_ : e∈E) :
        both (Fin.castAdd 21 e.1)=false ∨ both (Fin.natAdd 21 e.2)=false := by
      have lr (u v : Fin 21) : Fin.castAdd 21 u ≠ Fin.natAdd 21 v := by
        intro equality
        have bad := congrArg Fin.val equality
        change u.val = 21+v.val at bad
        omega
      have inj (u v : Fin 21) : Fin.natAdd 21 u = Fin.natAdd 21 v ↔ u=v := by
        constructor
        · intro equality
          exact Fin.ext (Nat.add_left_cancel (congrArg Fin.val equality : 21+u.val=21+v.val))
        · rintro rfl; rfl
      have castInj (u v : Fin 21) : Fin.castAdd 21 u = Fin.castAdd 21 v ↔ u=v := by
        constructor
        · intro equality
          exact Fin.ext (congrArg (fun z : Fin 42 => z.val) equality)
        · rintro rfl; rfl
      have left (h : both (Fin.castAdd 21 e.1) = true) : e.1=a.1 ∧ e.1=b.1 := by
        simpa only [both,r,Bool.and_eq_true,decide_eq_true_eq,lr,castInj,or_false] using h
      have right (h : both (Fin.natAdd 21 e.2) = true) : e.2=a.2 ∧ e.2=b.2 := by
        simpa only [both,r,Bool.and_eq_true,decide_eq_true_eq,inj,fun u v => (lr u v).symm,false_or] using h
      by_contra! h
      obtain ⟨a1,b1⟩ := left (Bool.eq_true_of_not_eq_false h.1)
      obtain ⟨a2,b2⟩ := right (Bool.eq_true_of_not_eq_false h.2)
      exact ne (Prod.ext (a1.symm.trans b1) (a2.symm.trans b2))
    let except := fun (K : Finset (Fin 21 × Fin 21) → Prop) => ∀ S, K S → a∈S → b∉S
    have keep (J : List (Finset (Fin 21 × Fin 21) × Finset (Fin 21 × Fin 21))) (K)
        (old : except K) (never : ∀ p∈J, cross a b p = false) : except (J.foldl advance K) := by
      induction J generalizing K with
      | nil => exact old
      | cons p tail ih =>
        apply ih (advance K p) _ (fun q h => never q (List.mem_cons_of_mem _ h))
        intro S hs am bm
        rcases hs with h|⟨sub,h₁,h₂⟩
        · exact old S h am bm
        · have no := never p List.mem_cons_self
          have casesA := Finset.mem_union.mp (sub am)
          have casesB := Finset.mem_union.mp (sub bm)
          simp only [cross,decide_eq_false_iff_not] at no
          rcases casesA with al|ar <;> rcases casesB with bl|br
          · exact old p.1 h₁ al bl
          · exact no (Or.inl ⟨al,br⟩)
          · exact no (Or.inr ⟨ar,bl⟩)
          · exact old p.2 h₂ ar br
    have initial : except (seed both) := by
      intro S hs am bm
      rcases hs with rfl|⟨i,off,all⟩
      · exact Finset.notMem_empty _ am
      · simp [both,all a am,all b bm] at off
    exact keep L (seed both) initial apart E (works both noEdge) ha hb
  have atLeast := partition E L (fun p h => (shape p h).1) countOne
  have card : E.card = 105 := by decide
  omega
