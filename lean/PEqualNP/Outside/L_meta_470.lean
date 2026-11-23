import Mathlib
import PEqualNP.Defs

private lemma end470 {w i n r : ℕ} (hi : i < n) (hr : r < w) :
    w*i+r < w*n := by
  have h := Nat.mul_le_mul_left w (Nat.succ_le_of_lt hi)
  rw [Nat.mul_succ] at h
  omega

private lemma block470 {w a b i j : ℕ} (hi : i < w) (hj : j < w)
    (h : w*a+i = w*b+j) : a = b ∧ i = j := by
  have hab : a = b := by
    rcases lt_trichotomy a b with hl | he | hg
    · have := end470 hl hi
      omega
    · exact he
    · have := end470 hg hj
      omega
  subst b
  exact ⟨rfl, by omega⟩

private def old470 {m : ℕ} (k : ℕ) (u : Fin m) : Fin (m + 2*k*(m*m)) :=
  ⟨u.val, by have := u.isLt; omega⟩

private def walk470 {m : ℕ} (k : ℕ) (e : Fin m × Fin m) (p : ℕ) :
    Fin (m + 2*k*(m*m)) :=
  if h0 : p = 0 then old470 k e.1 else
  if hp : p ≤ 2*k then
    ⟨m + 2*k*(e.1.val*m+e.2.val) + (p-1), by
      have hid : e.1.val*m+e.2.val < m*m := by
        simpa only [Nat.mul_comm m e.1.val] using end470 e.1.isLt e.2.isLt
      have h := end470 hid (show p-1 < 2*k by omega)
      omega⟩
  else old470 k e.2

private lemma walk470val {m k : ℕ} (e : Fin m × Fin m) {p : ℕ}
    (hp : 1 ≤ p) (hP : p ≤ 2*k) :
    (walk470 k e p).val = m + 2*k*(e.1.val*m+e.2.val) + (p-1) := by
  simp [walk470, show p ≠ 0 by omega, hP]

private lemma walk470inj {m k : ℕ} {e f : Fin m × Fin m} {p q : ℕ}
    (hp : 1 ≤ p) (hP : p ≤ 2*k) (hq : 1 ≤ q) (hQ : q ≤ 2*k)
    (h : walk470 k e p = walk470 k f q) : e = f ∧ p = q := by
  have hval := congrArg Fin.val h
  rw [walk470val e hp hP, walk470val f hq hQ] at hval
  have hh : 2*k*(e.1.val*m+e.2.val)+(p-1) = 2*k*(f.1.val*m+f.2.val)+(q-1) := by omega
  obtain ⟨hid, hoff⟩ := block470 (by omega : p-1 < 2*k) (by omega : q-1 < 2*k) hh
  rw [Nat.mul_comm e.1.val m, Nat.mul_comm f.1.val m] at hid
  obtain ⟨ha,hb⟩ := block470 e.2.isLt f.2.isLt hid
  exact ⟨Prod.ext (Fin.ext ha) (Fin.ext hb), by omega⟩

private lemma pathCount470 (k : ℕ) (_hk : 1 ≤ k) (V : ℕ → Prop) [DecidablePred V]
    (hcov : ∀ p : ℕ, p ≤ 2*k → V p ∨ V (p+1)) :
    k + (if (¬ V 0 ∧ ¬ V (2*k+1)) then 1 else 0) ≤
      ((Finset.Icc 1 (2*k)).filter V).card := by
  let pick (p : ℕ) := if V p then p else p + 1
  have hp (p : ℕ) : p ≤ pick p ∧ pick p ≤ p+1 := by
    dsimp [pick]
    split <;> omega
  have hv (p : ℕ) (h : p ≤ 2*k) : V (pick p) := by
    dsimp [pick]
    split
    · assumption
    · exact (hcov p h).resolve_left (by assumption)
  have count (a n : ℕ)
      (inside : ∀ i < n, 1 ≤ pick (a+2*i) ∧ pick (a+2*i) ≤ 2*k)
      (last : ∀ i < n, a+2*i ≤ 2*k) :
      n ≤ ((Finset.Icc 1 (2*k)).filter V).card := by
    rw [← Finset.card_range n]
    apply Finset.card_le_card_of_injOn (fun i => pick (a+2*i))
    · intro i hi
      have hi' : i < n := Finset.mem_range.mp hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr (inside i hi'), hv _ (last i hi')⟩
    · intro i _ j _ he
      change pick (a+2*i) = pick (a+2*j) at he
      have := hp (a+2*i)
      have := hp (a+2*j)
      omega
  by_cases ends : ¬ V 0 ∧ ¬ V (2*k+1)
  · simp only [ite_eq_left ends]
    apply count 0 (k+1) _ (by intros; omega)
    intro i hi
    have h := hp (0+2*i)
    have v := hv (0+2*i) (by omega)
    have hn0 : pick (0+2*i) ≠ 0 := fun e => ends.1 (e ▸ v)
    have hn1 : pick (0+2*i) ≠ 2*k+1 := fun e => ends.2 (e ▸ v)
    omega
  · simp only [ite_eq_right ends, Nat.add_zero]
    apply count 1 k _ (by intros; omega)
    intro i hi
    have := hp (1+2*i)
    omega

private lemma edge470 {m : ℕ} (H : SimpleGraph (Fin m)) (D : Finset (Fin m × Fin m))
    (hD : ∀ e : Fin m × Fin m, e ∈ D ↔ e.1 < e.2 ∧ H.Adj e.1 e.2) :
    H.edgeSet.ncard ≤ D.card := by
  classical
  let f (e : Fin m × Fin m) : Sym2 (Fin m) := s(e.1,e.2)
  have hsub : H.edgeFinset ⊆ D.image f := by
    intro x hx
    let a := (Quot.out x).1
    let b := (Quot.out x).2
    have he : s(a,b) = x := Quot.out_eq _
    have hab : H.Adj a b := by
      change s(a,b) ∈ H.edgeSet
      rw [← SimpleGraph.mem_edgeFinset, he]
      exact hx
    rcases lt_or_gt_of_ne hab.ne with h | h
    · exact Finset.mem_image.mpr ⟨(a,b), (hD _).mpr ⟨h,hab⟩, he⟩
    · exact Finset.mem_image.mpr ⟨(b,a), (hD _).mpr ⟨h,hab.symm⟩,
        (Sym2.eq_iff.mpr (Or.inr ⟨rfl,rfl⟩) : s(b,a) = s(a,b)) |>.trans he⟩
  calc H.edgeSet.ncard = (↑H.edgeFinset : Set (Sym2 (Fin m))).ncard := by simp
       _ = H.edgeFinset.card := Set.ncard_coe_finset _
       _ ≤ (D.image f).card := Finset.card_le_card hsub
       _ ≤ D.card := Finset.card_image_le

set_option maxHeartbeats 1800000 in
theorem PEqualNP.Outside.L_meta_470 : ∀ (m k : ℕ) (H : SimpleGraph (Fin m)) (Q : Fin m → Fin m → ℕ → Fin (m + 2 * k * (m * m)) → Prop) (S : SimpleGraph (Fin (m + 2 * k * (m * m)))), 1 ≤ k → (∀ (u v : Fin m) (p : ℕ) (x : Fin (m + 2 * k * (m * m))), Q u v p x ↔ (p = 0 ∧ x.val = u.val) ∨ (p = 2 * k + 1 ∧ x.val = v.val) ∨ (1 ≤ p ∧ p ≤ 2 * k ∧ x.val + 1 = m + 2 * k * (u.val * m + v.val) + p)) → (∀ x y : Fin (m + 2 * k * (m * m)), S.Adj x y ↔ ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ p : ℕ, p ≤ 2 * k ∧ ((Q u v p x ∧ Q u v (p + 1) y) ∨ (Q u v p y ∧ Q u v (p + 1) x))) → ∀ c : ℕ, (∀ R : Finset (Fin m), (∀ u v : Fin m, H.Adj u v → u ∈ R ∨ v ∈ R) → c ≤ R.card) → ∀ U : Finset (Fin (m + 2 * k * (m * m))), (∀ x y : Fin (m + 2 * k * (m * m)), S.Adj x y → x ∈ U ∨ y ∈ U) → c + k * H.edgeSet.ncard ≤ U.card := by
  classical
  intro m k H Q S hk hQ hS c hc U hU
  let D := Finset.univ.filter fun e : Fin m × Fin m => e.1 < e.2 ∧ H.Adj e.1 e.2
  have hD (e : Fin m × Fin m) : e ∈ D ↔ e.1 < e.2 ∧ H.Adj e.1 e.2 := by simp [D]
  let O := Finset.univ.filter fun a : Fin m => old470 k a ∈ U
  let bad (e : Fin m × Fin m) := old470 k e.1 ∉ U ∧ old470 k e.2 ∉ U
  let R := O ∪ (D.filter bad).image Prod.fst
  have hR : c ≤ R.card := by
    apply hc
    intro a b hab
    by_cases ha : old470 k a ∈ U
    · exact Or.inl (Finset.mem_union_left _ (by simpa [O] using ha))
    by_cases hb : old470 k b ∈ U
    · exact Or.inr (Finset.mem_union_left _ (by simpa [O] using hb))
    rcases lt_or_gt_of_ne hab.ne with h | h
    · left
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(a,b),
        Finset.mem_filter.mpr ⟨(hD _).mpr ⟨h,hab⟩,ha,hb⟩,rfl⟩)
    · right
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(b,a),
        Finset.mem_filter.mpr ⟨(hD _).mpr ⟨h,hab.symm⟩,hb,ha⟩,rfl⟩)
  have horig : c ≤ O.card + (D.filter bad).card :=
    hR.trans ((Finset.card_union_le _ _).trans (Nat.add_le_add_left Finset.card_image_le _))
  have hwalk (e : Fin m × Fin m) (p : ℕ) (hp : p ≤ 2*k+1) :
      Q e.1 e.2 p (walk470 k e p) := by
    apply (hQ _ _ _ _).mpr
    by_cases hz : p = 0
    · exact Or.inl ⟨hz,by simp [walk470,hz,old470]⟩
    by_cases hi : p ≤ 2*k
    · right; right
      exact ⟨by omega,hi,by rw [walk470val e (by omega) hi]; omega⟩
    · right; left
      exact ⟨by omega,by simp [walk470,hz,hi,old470]⟩
  let P (e : Fin m × Fin m) :=
    (Finset.Icc 1 (2*k)).filter fun p => walk470 k e p ∈ U
  let T (e : Fin m × Fin m) := (P e).image (walk470 k e)
  have hpos {e : Fin m × Fin m} {p : ℕ} (h : p ∈ P e) :
      (1 ≤ p ∧ p ≤ 2*k) ∧ walk470 k e p ∈ U := by
    simpa [P] using h
  have hcnt (e : Fin m × Fin m) (he : e ∈ D) :
      k + (if bad e then 1 else 0) ≤ (T e).card := by
    have hcov (p : ℕ) (hp : p ≤ 2*k) : walk470 k e p ∈ U ∨ walk470 k e (p+1) ∈ U := by
      apply hU
      apply (hS _ _).mpr
      exact ⟨e.1,e.2,((hD _).mp he).1,((hD _).mp he).2,p,hp,
        Or.inl ⟨hwalk _ _ (by omega),hwalk _ _ (by omega)⟩⟩
    have h1 := pathCount470 k hk (fun p => walk470 k e p ∈ U) hcov
    have h2 : k + (if bad e then 1 else 0) ≤ (P e).card := by
      have hzero : walk470 k e 0 = old470 k e.1 := by simp [walk470]
      have hlast : walk470 k e (2*k+1) = old470 k e.2 := by simp [walk470]
      simpa only [P,bad,hzero,hlast] using h1
    have hcard : (T e).card = (P e).card := by
      apply Finset.card_image_of_injOn
      intro p hp q hq h
      exact (walk470inj (hpos hp).1.1 (hpos hp).1.2 (hpos hq).1.1 (hpos hq).1.2 h).2
    rwa [hcard]
  have hd : (D : Set (Fin m × Fin m)).PairwiseDisjoint T := by
    intro e he f hf hef
    rw [Function.onFun, Finset.disjoint_left]
    intro x hx hy
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨q,hq,hqp⟩ := Finset.mem_image.mp hy
    exact hef ((walk470inj (hpos hp).1.1 (hpos hp).1.2 (hpos hq).1.1 (hpos hq).1.2 hqp.symm).1)
  have hdup : Disjoint (O.image (old470 k)) (D.biUnion T) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨e,he,hx⟩ := Finset.mem_biUnion.mp hy
    obtain ⟨p,hp,heq⟩ := Finset.mem_image.mp hx
    have hh := congrArg Fin.val heq
    rw [walk470val e (hpos hp).1.1 (hpos hp).1.2] at hh
    change _ = a.val at hh
    have := a.isLt
    omega
  have hsub : O.image (old470 k) ∪ D.biUnion T ⊆ U := by
    intro x hx
    rcases Finset.mem_union.mp hx with h | h
    · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp h
      exact (Finset.mem_filter.mp ha).2
    · obtain ⟨e,_,he⟩ := Finset.mem_biUnion.mp h
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp he
      exact (hpos hp).2
  have hbig := Finset.card_le_card hsub
  have hoi : Function.Injective (old470 (m := m) k) := by
    intro a b h
    have hh := congrArg Fin.val h
    exact Fin.ext hh
  rw [Finset.card_union_of_disjoint hdup, Finset.card_image_of_injective _ hoi,
    Finset.card_biUnion hd] at hbig
  have hsum := Finset.sum_le_sum hcnt
  simp only [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, Finset.sum_boole] at hsum
  have hsum' : D.card*k + (D.filter bad).card ≤ ∑ e ∈ D, (T e).card := by simpa using hsum
  have hedge := Nat.mul_le_mul_left k (edge470 H D hD)
  rw [Nat.mul_comm k D.card] at hedge
  omega
