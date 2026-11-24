import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3364_97
  (charge : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (_nonzero : 0<N) (_degree : ∀ l, Fintype.card {p // I p l} = q+1) (_un : ∀ p t, p≠t → ∃! l, I p l ∧ I t l) (n r : ℕ) (W : ℕ → Set ((Fin N → Bool) × (Fin N → Bool))),
  let k := N+N
  let s := fun p i : Fin N => decide (i=p)
  let z := fun _ : Fin N => false
  let step := fun (e : Bool) (v : ℕ) =>
    ∃ a<v, ∃ b<v, W v=W a∪W b ∨ W v=W a ∨ W v=∅ ∨
      W v=W a∩W b ∧ (e=false ∨ ∃ X Y : Set (Fin N→Bool), W a=X×ˢSet.univ ∧ W b=Set.univ×ˢY)
  let costly := fun (v : ℕ) =>
    (∃ l, 32 < Set.ncard {p | I p l ∧ (s p,z) ∈ W v}) ∨
    (∃ p, 32 < Set.ncard {l | I p l ∧ (z,s l) ∈ W v}) ∨
    (W v⊆W r ∧ 32 < Set.ncard {t : Fin N × Fin N | (s t.1,s t.2) ∈ W v})
  r<k+n →
  (∀ i : Fin N, W i.val={t | t.1 i=true} ∧ W (N+i.val)={t | t.2 i=true}) →
  (∀ j<n, step false (k+j)) →
  (∀ p l, I p l → (s p,s l) ∈ W r) →
  ((∀ p l, (s p,s l)∈W r → I p l) ∧ (∀ p, (s p,z)∉W r) ∧ (∀ l,(z,s l)∉W r)) →
  100*n < N*(q+1) →
  (∃ j<n, ¬step true (k+j) ∧ costly (k+j)))
  (lone : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (_hq : 100<q) (_size : N=q^2+q+1) (_degree : ∀ l, Fintype.card {p // I p l} = q+1) (_un : ∀ p t, p≠t → ∃! l, I p l ∧ I t l) (n r : ℕ) (W : ℕ → Set ((Fin N → Bool) × (Fin N → Bool))),
  let k := N+N
  let s := fun p i : Fin N => decide (i=p)
  let step := fun (e : Bool) (v : ℕ) =>
    ∃ a<v, ∃ b<v, W v=W a∪W b ∨ W v=W a ∨ W v=∅ ∨
      W v=W a∩W b ∧ (e=false ∨ ∃ X Y : Set (Fin N→Bool), W a=X×ˢSet.univ ∧ W b=Set.univ×ˢY)
  r<k+n →
  (∀ i : Fin N, W i.val={t | t.1 i=true} ∧ W (N+i.val)={t | t.2 i=true}) →
  (∀ j<n, step false (k+j)) →
  (∀ p l, I p l → (s p,s l) ∈ W r) →
  (∀ y : Fin N→Bool, Fintype.card {l // y l=true}≤q →
    ((fun p => decide ¬∃ l, I p l ∧ y l=true),y) ∉ W r) →
  Set.ncard {j : Fin n | ¬step true (k+j.val)} ≤ 1 → N*(q+1)≤100*n)
  (hard : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (_hq : 100<q) (_size : N=q^2+q+1) (_degree : ∀ l, Fintype.card {p // I p l} = q+1) (_un : ∀ p t, p≠t → ∃! l, I p l ∧ I t l) (n r : ℕ) (W : ℕ → Set ((Fin N → Bool) × (Fin N → Bool))),
  let k := N+N
  let s := fun p i : Fin N => decide (i=p)
  let z := fun _ : Fin N => false
  let step := fun (e : Bool) (v : ℕ) =>
    ∃ a<v, ∃ b<v, W v=W a∪W b ∨ W v=W a ∨ W v=∅ ∨
      W v=W a∩W b ∧ (e=false ∨ ∃ X Y : Set (Fin N→Bool), W a=X×ˢSet.univ ∧ W b=Set.univ×ˢY)
  let costly := fun (v : ℕ) =>
    (∃ l, 32 < Set.ncard {p | I p l ∧ (s p,z) ∈ W v}) ∨
    (∃ p, 32 < Set.ncard {l | I p l ∧ (z,s l) ∈ W v}) ∨
    (W v⊆W r ∧ 32 < Set.ncard {t : Fin N × Fin N | (s t.1,s t.2) ∈ W v})
  r<k+n →
  (∀ i : Fin N, W i.val={t | t.1 i=true} ∧ W (N+i.val)={t | t.2 i=true}) →
  (∀ j<n, step false (k+j)) →
  (∀ p l, I p l → (s p,s l) ∈ W r) →
  (∀ y : Fin N→Bool, Fintype.card {l // y l=true}≤q →
    ((fun p => decide ¬∃ l, I p l ∧ y l=true),y) ∉ W r) →
  Set.ncard {j : Fin n | ¬step true (k+j.val)} ∈ Set.Ioc 1 ((N*q-1)/100) →
  (∃ j<n, ¬step true (k+j) ∧ costly (k+j)) → N*(q+1)≤100*n) :
  ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [_x4 : DecidableRel x3],   (100 : ℕ) < x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) →         (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) →           ∀ (x9 x10 : ℕ) (x11 : Finset ℕ) (x12 : ℕ → Set ((Fin x2 → Bool) × (Fin x2 → Bool))),             x10 < x2 + x2 + x9 →               (∀ (x14 : Fin x2), x12 ↑x14 = {x15 : (Fin x2 → Bool) × (Fin x2 → Bool) | x15.1 x14 = Bool.true} ∧ x12 (x2 + ↑x14) = {x15 : (Fin x2 → Bool) × (Fin x2 → Bool) | x15.2 x14 = Bool.true}) →                 (∀ x15 < x9,                     ∃ x17 < x2 + x2 + x15,                       ∃ x18 < x2 + x2 + x15,                         have x19 : Set ((Fin x2 → Bool) × (Fin x2 → Bool)) := x12 (x2 + x2 + x15);                         x19 = x12 x17 ∪ x12 x18 ∨ x19 = x12 x17 ∨ x19 = ∅ ∨ x19 = x12 x17 ∩ x12 x18 ∧ (x15 ∈ x11 ∨ ∃ (x20 : Set (Fin x2 → Bool)) (x21 : Set (Fin x2 → Bool)), x12 x17 = x20 ×ˢ Set.univ ∧ x12 x18 = Set.univ ×ˢ x21)) →                   (∀ (x16 x17 : Fin x2), x3 x16 x17 → (fun (x19 : Fin x2) => Decidable.decide (x19 = x16), fun (x19 : Fin x2) => Decidable.decide (x19 = x17)) ∈ x12 x10) → (∀ (x17 : Fin x2 → Bool), Fintype.card { x18 : Fin x2 // x17 x18 = Bool.true } ≤ x1 → (fun (x19 : Fin x2) => Decidable.decide ¬∃ (x20 : Fin x2), x3 x19 x20 ∧ x17 x20 = Bool.true, x17) ∉ x12 x10) → (100 : ℕ) * x11.card < x2 * x1 → ∃ (x19 : Fin x9 → Finset (Fin x2)) (x20 : Fin x9 → Finset (Fin x2)), (∀ (x21 : Fin x9), ∀ x22 ∈ x19 x21, ∀ x24 ∈ x20 x21, x3 x22 x24) ∧ (∀ (x21 x22 : Fin x2), x3 x21 x22 → ∃ (x24 : Fin x9), x21 ∈ x19 x24 ∧ x22 ∈ x20 x24) ∧ ∑ x21 : Fin x9, ((x19 x21).card + (x20 x21).card) ≤ (100 : ℕ) * x9 + x2 := by
  intro q N I inst hq size degree un n r B W hr raw gs pos sound budget
  classical
  let Z := (Fin N → Bool) × (Fin N → Bool)
  let bitLE (x y : Fin N→Bool) := ∀i, x i=true → y i=true
  let s (p i : Fin N) := decide (i=p)
  let step (e : Bool) (v : ℕ) := ∃ a<v, ∃ b<v, W v=W a∪W b ∨ W v=W a ∨ W v=∅ ∨ W v=W a∩W b ∧ (e=false ∨ ∃ X Y : Set (Fin N→Bool), W a=X×ˢSet.univ ∧ W b=Set.univ×ˢY)
  have all (j : ℕ) (hj : j<n) : step false (N+N+j) := by
    obtain ⟨a,ha,b,hb,op⟩ := gs j hj
    refine ⟨a,ha,b,hb,?_⟩
    rcases op with h|h|h|⟨h,_⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr ⟨h,Or.inl rfl⟩))
  have part (j : Fin n) (no : ¬step true (N+N+j.val)) : j.val∈B := by
    by_contra out
    apply no
    obtain ⟨a,ha,b,hb,op⟩ := gs j j.isLt
    refine ⟨a,ha,b,hb,?_⟩
    rcases op with h|h|h|⟨h,bad|ok⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact False.elim (out bad)
    · exact Or.inr (Or.inr (Or.inr ⟨h,Or.inr ok⟩))
  have total : Set.ncard {j : Fin n | ¬step true (N+N+j.val)} ≤ B.card := by
    let E := Finset.univ.filter (fun j : Fin n => ¬step true (N+N+j.val))
    have eq : {j : Fin n | ¬step true (N+N+j.val)} = (E:Set (Fin n)) := by ext j; simp [E]
    rw [eq,Set.ncard_coe_finset]
    exact Finset.card_le_card_of_injOn Fin.val (fun j hj=>part j (Finset.mem_filter.mp hj).2) (fun _ _ _ _ h=>Fin.ext h)
  have monotone : ∀ w < N+N+n, ((fun _ => false),(fun _ => false)) ∉ W w ∧
      ∀ x y : Z, bitLE x.1 y.1 → bitLE x.2 y.2 → x ∈ W w → y ∈ W w := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw
      by_cases first : w<N
      · let p : Fin N := ⟨w,first⟩
        rw [show w=p.val from rfl,(raw p).1]
        exact ⟨by simp,fun _ _ h _ hx => h _ hx⟩
      by_cases second : w<N+N
      · let l : Fin N := ⟨w-N,by omega⟩
        have heq : w=N+l.val := by dsimp [l]; omega
        rw [heq,(raw l).2]
        exact ⟨by simp,fun _ _ _ h hx => h _ hx⟩
      let j := w-(N+N)
      have heq : N+N+j=w := by dsimp [j]; omega
      obtain ⟨a,ha,b,hb,op⟩ := gs j (by omega)
      change W (N+N+j) = W a ∪ W b ∨ W (N+N+j) = W a ∨ W (N+N+j) = ∅ ∨ _ at op
      rw [heq] at ha hb op
      obtain ⟨az,am⟩ := ih a ha (by omega)
      obtain ⟨bz,bm⟩ := ih b hb (by omega)
      rcases op with h | h | h | ⟨h,_⟩
      · rw [h]
        exact ⟨fun x => x.elim az bz,fun x y p l k => k.elim (fun v => Or.inl (am x y p l v)) (fun v => Or.inr (bm x y p l v))⟩
      · rw [h]; exact ⟨az,am⟩
      · rw [h]; exact ⟨id,fun _ _ _ _ k => k⟩
      · rw [h]; exact ⟨fun v => az v.1,fun x y p l k => ⟨am x y p l k.1,bm x y p l k.2⟩⟩
  have mono := (monotone r hr).2
  have tests : (∀ p l, (s p,s l) ∈ W r → I p l) ∧ (∀ p, (s p,fun _ => false) ∉ W r) ∧ (∀ l, (fun _ => false,s l) ∉ W r) := by
    have one (l : Fin N) : Fintype.card {i : Fin N // s l i=true} ≤ q := by
      have eq : Fintype.card {i : Fin N // s l i=true} = 1 := by
        rw [Fintype.card_subtype]
        have filt : (Finset.univ.filter (fun i : Fin N => s l i=true)) = {l} := by
          ext i; simp [s]
        rw [filt,Finset.card_singleton]
      exact eq ▸ (by omega : 1 ≤ q)
    have zero : Fintype.card {i : Fin N // false=true} ≤ q := by simp
    refine ⟨?_,?_,?_⟩
    · intro p l hit
      by_contra bad
      apply sound (s l) (one l)
      refine mono (s p,s l) (_,s l) ?_ (fun _ h => h) hit
      intro i hi
      have ip : i=p := by simpa [s] using hi
      subst i
      simp [s,bad]
    · intro p hit
      apply sound (fun _ => false) zero
      exact mono (s p,fun _ => false) (_,fun _ => false) (by intro i hi; simp) (fun _ h => h) hit
    · intro l hit
      apply sound (s l) (one l)
      exact mono (fun _ => false,s l) (_,s l) (by intro i hi; contradiction) (fun _ h => h) hit
  have bound : N*(q+1) ≤ 100*n := by
    by_contra! small
    have bad := charge q N I (by omega) degree un n r W hr raw all pos tests small
    have more : 1 < Set.ncard {j : Fin n | ¬step true (N+N+j.val)} := by
      by_contra! few
      exact (Nat.not_lt_of_ge (lone q N I hq size degree un n r W hr raw all pos sound few)) small
    have lim : Set.ncard {j : Fin n | ¬step true (N+N+j.val)} ≤ (N*q-1)/100 := by
      apply (Nat.le_div_iff_mul_le (by decide : 0<100)).mpr
      have paid := (Nat.mul_le_mul_left 100 total).trans_lt budget
      rw [Nat.mul_comm] at paid
      omega
    have final := hard q N I hq size degree un n r W hr raw all pos sound ⟨more,lim⟩ bad
    omega
  have enough : N≤n := by
    by_contra! bad
    have small := Nat.mul_lt_mul_of_pos_left bad (by decide : 0<100)
    have big := Nat.mul_le_mul_left N (by omega : 100≤q+1)
    omega
  let A (j : Fin n) : Finset (Fin N) := if h:j.val<N then Finset.univ.filter (fun p=>I p ⟨j.val,h⟩) else ∅
  let D (j : Fin n) : Finset (Fin N) := if h:j.val<N then {⟨j.val,h⟩} else ∅
  refine ⟨A,D,?_,?_,?_⟩
  · intro j p hp l hl
    by_cases h : j.val<N
    · have e : l=⟨j.val,h⟩ := by simpa [D,h] using hl
      subst l; simpa [A,h] using hp
    · simp [A,h] at hp
  · intro p l inc
    let j : Fin n := ⟨l.val,lt_of_lt_of_le l.isLt enough⟩
    refine ⟨j,?_,?_⟩
    · simpa [A,j,l.isLt] using inc
    · simp [D,j,l.isLt]
  · let f (j : Fin n) := (A j).card + (D j).card
    let embed : Fin N → Fin n := Fin.castLE enough
    have total : ∑j, f j = ∑l : Fin N, f (embed l) := by
      symm
      apply Finset.sum_of_injOn embed
      · intro a _ b _ h; exact Fin.ext (congrArg (fun k : Fin n => k.val) h)
      · intro a _; exact Finset.mem_univ _
      · intro j _ missing
        by_cases h : j.val<N
        · exact False.elim (missing ⟨⟨j.val,h⟩,Finset.mem_univ _,Fin.ext rfl⟩)
        · simp [f,A,D,h]
      · intros; rfl
    have val (l : Fin N) : f (embed l) = (q+1)+1 := by
      have de := degree l
      rw [Fintype.card_subtype] at de
      simpa [f,A,D,embed,l.isLt] using congrArg (fun t : ℕ=>t+1) de
    change (∑j, f j) ≤ _
    rw [total]
    simp only [val,Finset.sum_const,Finset.card_univ,Fintype.card_fin,Nat.nsmul_eq_mul,Nat.mul_add,Nat.mul_one]
    rw [Nat.mul_add,Nat.mul_one] at bound
    omega

