import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.GenericRejection PEqualNP.ReadK

set_option maxHeartbeats 800000 in
theorem PEqualNP.Outside.R_meta_3682_492
    (accounting : ∀ (N : ℕ) (S : Fin N → Finset (Fin N)) (C : Circuit),
    (∀ a b : Fin N, a ≠ b → ∃! l, a ∈ S l ∧ b ∈ S l) → IsAO2 (N+N) C →
    (∀ X Y, X.card ≤ 2 → Y.card ≤ 2 → IsFalseInput S X Y →
       C.eval (incidenceInput X Y)=false) →
    let good (p l : Fin N) := readsAtMost C (N+N) [p.val,N+l.val] 2=true
    let hits (l : Fin N) : Finset (Fin N) := (S l).filter fun p => good p l
    (∑ l : Fin N, (hits l).card) ≤
       94*C.size + 2*N)
    (obstruction : ∀ (q N : ℕ) (S : Fin N → Finset (Fin N)), 200 ≤ q → N=q^2+q+1 →
    (∀ l, (S l).card=q+1) → (∀ a b : Fin N, a≠b → ∃! l, a∈S l ∧ b∈S l) →
    let admissible (D : Circuit) := IsAO2 (N+N) D ∧ D.output < N+N+D.size ∧
      RightOnIncidentPairs S D ∧ ∀ (X Y : Finset (Fin N)), Y.card ≤ q →
        IsFalseInput S X Y → D.eval (incidenceInput X Y)=false
    ∀ (D : Circuit), admissible D → (∀ C, admissible C → D.size ≤ C.size) →
    let hard (p l : Fin N) := p ∈ S l ∧ readsAtMost D (N+N) [p.val,N+l.val] 2≠true
    ∀ P L : Finset (Fin N), P.Nonempty → L.Nonempty →
    (∀ p ∈ P, q/40 < (L.filter (hard p)).card) →
    (∀ l ∈ L, q/40 < (P.filter fun p => hard p l).card) → N*q ≤ 100*D.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (200 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) → PEqualNP.TopForm.IsAO2 (x2 + x2) x4 → ¬PEqualNP.ReadK.IsReadK (x2 + x2) x4 (2 : ℕ) → x4.output < x2 + x2 + x4.size → PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 → (∀ (x13 x14 : Finset (Fin x2)), x14.card ≤ x1 → PEqualNP.GenericRejection.IsFalseInput x3 x13 x14 → x4.eval (PEqualNP.GenericRejection.incidenceInput x13 x14) = Bool.false) → x2 * x1 ≤ (100 : ℕ) * x4.size := by
  -- Minimize the number of surviving vertices subject to a positive edge surplus.
  have peel (N k : ℕ) (r : Fin N → Fin N → Prop) [DecidableRel r]
      (many : k*(N+N) < ∑ l : Fin N, (Finset.univ.filter fun p => r p l).card) :
      ∃ P L : Finset (Fin N), P.Nonempty ∧ L.Nonempty ∧
        (∀ p ∈ P, k < (L.filter (r p)).card) ∧ (∀ l ∈ L, k < (P.filter fun p => r p l).card) := by
    classical
    let m (P L : Finset (Fin N)) := ∑ l ∈ L, (P.filter fun p => r p l).card
    have rows (P L : Finset (Fin N)) :
        m P L = ∑ p ∈ P, (L.filter (r p)).card := by
      simp only [m,Finset.card_filter]
      exact Finset.sum_comm
    let possible (j : ℕ) := ∃ P L : Finset (Fin N), P.card+L.card=j ∧ k*(P.card+L.card)<m P L
    have start : ∃ j, possible j :=
      ⟨_,Finset.univ,Finset.univ,rfl,by simpa [m] using many⟩
    obtain ⟨P,L,num,rich⟩ := Nat.find_spec start
    have pn : P.Nonempty := by
      by_contra! empty
      simp [empty,m] at rich
    have ln : L.Nonempty := by
      by_contra! empty
      simp [empty,m] at rich
    refine ⟨P,L,pn,ln,?_,?_⟩
    · intro p hp
      by_contra! small
      have split : m P L = (L.filter (r p)).card + m (P.erase p) L := by
        rw [rows,rows (P.erase p)]
        exact (Finset.add_sum_erase P (fun p => (L.filter (r p)).card) hp).symm
      have c := Finset.card_erase_add_one hp
      have eq : k*(P.card+L.card) = k*((P.erase p).card+L.card)+k := by
        rw [← c]; ring
      have still : possible ((P.erase p).card+L.card) := ⟨P.erase p,L,rfl,by omega⟩
      have lower := Nat.find_min' start still
      omega
    · intro l hl
      by_contra! small
      have split : m P L = (P.filter fun p => r p l).card + m P (L.erase l) :=
        (Finset.add_sum_erase L (fun l => (P.filter fun p => r p l).card) hl).symm
      have c := Finset.card_erase_add_one hl
      have eq : k*(P.card+L.card) = k*(P.card+(L.erase l).card)+k := by rw [← c]; ring
      have still : possible (P.card+(L.erase l).card) := ⟨P,L.erase l,rfl,by omega⟩
      have lower := Nat.find_min' start still
      omega
  intro q N S C hq order lines unique ao _ out yes no
  classical
  let A (D : Circuit) := IsAO2 (N+N) D ∧ D.output<N+N+D.size ∧
    RightOnIncidentPairs S D ∧ ∀ (X Y : Finset (Fin N)), Y.card≤q → IsFalseInput S X Y →
      D.eval (incidenceInput X Y)=false
  -- Choose among circuits satisfying the stated tests, so redundant repetitions cannot
  -- create a difficult instance merely by inflating a positive computation.
  have existsSize : ∃ j, ∃ D : Circuit, A D ∧ D.size=j := ⟨C.size,C,⟨ao,out,yes,no⟩,rfl⟩
  obtain ⟨D,hd,minSize⟩ := Nat.find_spec existsSize
  have least (E : Circuit) (hE : A E) : D.size ≤ E.size := minSize ▸ Nat.find_min' existsSize ⟨E,hE,rfl⟩
  have le := least C ⟨ao,out,yes,no⟩
  suffices result : N*q ≤ 100*D.size by omega
  by_contra! small
  let read (p l : Fin N) := readsAtMost D (N+N) [p.val,N+l.val] 2=true
  let bad (p l : Fin N) := p ∈ S l ∧ ¬read p l
  let easyCount := ∑ l : Fin N, ((S l).filter fun p => read p l).card
  let hardCount := ∑ l : Fin N, ((S l).filter fun p => ¬read p l).card
  have bound : easyCount ≤ 94*D.size+2*N :=
    accounting N S D unique hd.1 (fun X Y _ y h => hd.2.2.2 X Y (by omega) h)
  have total : easyCount+hardCount=N*(q+1) := by
    dsimp only [easyCount,hardCount]
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ _l : Fin N, (q+1) := Finset.sum_congr rfl (fun l _ =>
        (Finset.card_filter_add_card_filter_not (s := S l) (fun p => read p l)).trans (lines l))
      _ = _ := by simp
  let k := q/40
  have cap : 40*k ≤ q := by simpa [k,Nat.mul_comm] using Nat.div_mul_le_self q 40
  have major := Nat.mul_le_mul_left N hq
  have product := Nat.mul_le_mul_left N cap
  have many : k*(N+N)<hardCount := by nlinarith only [bound,total,small,major,product]
  have column (l : Fin N) : (Finset.univ.filter fun p => bad p l) =
        ((S l).filter fun p => ¬read p l) := by ext p; simp [bad]
  obtain ⟨P,L,pn,ln,pc,lc⟩ := peel N k bad (by simpa only [column,hardCount] using many)
  have res := obstruction q N S hq order lines unique D hd least P L pn ln pc lc
  omega
