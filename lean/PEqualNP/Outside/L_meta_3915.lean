import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3915

open PEqualNP.MetaComplexity

def stepW (w : List Bool) (g : BinaryGate) : List Bool :=
  w ++ [g.op (w.getD g.left false) (w.getD g.right false)]

lemma wires_eq (gs : List BinaryGate) (o : ℕ) (x : List Bool) :
    (BinaryCircuit.mk gs o).wires x = gs.foldl stepW x := rfl

lemma foldl_ext (gs : List BinaryGate) : ∀ w : List Bool, ∃ t, gs.foldl stepW w = w ++ t := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht⟩ := ih (stepW w g)
    refine ⟨[g.op (w.getD g.left false) (w.getD g.right false)] ++ t, ?_⟩
    simp only [List.foldl_cons]
    rw [ht]
    simp [stepW]

lemma foldl_len (gs : List BinaryGate) : ∀ w : List Bool,
    (gs.foldl stepW w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp
  | cons g gs ih =>
    intro w
    simp only [List.foldl_cons, ih, stepW, List.length_append, List.length_cons,
      List.length_nil]
    omega

lemma foldl_getD (gs : List BinaryGate) (w : List Bool) (k : ℕ) (hk : k < w.length) :
    (gs.foldl stepW w).getD k false = w.getD k false := by
  obtain ⟨t, ht⟩ := foldl_ext gs w
  rw [ht, List.getD_append _ _ _ _ hk]

lemma foldl_snoc (gs : List BinaryGate) (g : BinaryGate) (w : List Bool) :
    (gs ++ [g]).foldl stepW w = stepW (gs.foldl stepW w) g := by
  simp [List.foldl_append]

def ev (w : List Bool) : Bool ⊕ (ℕ × Bool) → Bool
  | Sum.inl c => c
  | Sum.inr (d, p) => w.getD d false ^^ p

def andG (a b : Bool) (l r : ℕ) : BinaryGate :=
  { op := fun u v => u == a && v == b, left := l, right := r }

def comb (top : ℕ) (a b : Bool) :
    Bool ⊕ (ℕ × Bool) → Bool ⊕ (ℕ × Bool) → (Bool ⊕ (ℕ × Bool)) × List BinaryGate
  | Sum.inl c, Sum.inl e => (Sum.inl ((c == a) && (e == b)), [])
  | Sum.inl c, Sum.inr (d, p) => (if c == a then Sum.inr (d, p ^^ !b) else Sum.inl false, [])
  | Sum.inr (d, p), Sum.inl e => (if e == b then Sum.inr (d, p ^^ !a) else Sum.inl false, [])
  | Sum.inr (d1, p1), Sum.inr (d2, p2) =>
    if d1 = d2 then
      (if (a ^^ p1) = (b ^^ p2) then Sum.inr (d1, !(a ^^ p1)) else Sum.inl false, [])
    else if d1 < d2 then (Sum.inr (top, false), [andG (a ^^ p1) (b ^^ p2) d1 d2])
    else (Sum.inr (top, false), [andG (b ^^ p2) (a ^^ p1) d2 d1])

def okR (m : ℕ) : Bool ⊕ (ℕ × Bool) → Prop
  | Sum.inl _ => True
  | Sum.inr (d, _) => d < m

lemma okR_mono {m m' : ℕ} (h : m ≤ m') : ∀ u, okR m u → okR m' u
  | Sum.inl _, _ => trivial
  | Sum.inr (d, _), hu => by simp only [okR] at hu ⊢; omega

lemma ev_ext (w t : List Bool) : ∀ u, okR w.length u → ev (w ++ t) u = ev w u
  | Sum.inl _, _ => rfl
  | Sum.inr (d, p), hu => by
    simp only [okR] at hu
    simp only [ev, List.getD_append _ _ _ _ hu]

lemma xor_beq (u p a : Bool) : ((u ^^ p) == a) = (u ^^ (p ^^ !a)) := by
  cases u <;> cases p <;> cases a <;> rfl

lemma comb_spec (w : List Bool) (a b : Bool) (u v : Bool ⊕ (ℕ × Bool))
    (hu : okR w.length u) (hv : okR w.length v) :
    let c := comb w.length a b u v
    (c.2.foldl stepW w).length ≤ w.length + 1 ∧
    okR (c.2.foldl stepW w).length c.1 ∧
    (∀ g ∈ c.2, ∃ a' b' : Bool, g.op = fun x y => x == a' && y == b') ∧
    (∀ g ∈ c.2, g.left < g.right ∧ g.right < w.length) ∧
    ev (c.2.foldl stepW w) c.1 = ((ev w u == a) && (ev w v == b)) := by
  rcases u with c | ⟨d1, p1⟩ <;> rcases v with e | ⟨d2, p2⟩
  · simp [comb, okR, ev]
  · simp only [okR] at hv
    by_cases h : (c == a) = true
    · simp [comb, h, okR, ev, hv, xor_beq]
    · simp [comb, h, okR, ev]
  · simp only [okR] at hu
    by_cases h : (e == b) = true
    · simp [comb, h, okR, ev, hu, xor_beq]
    · simp [comb, h, okR, ev]
  · simp only [okR] at hu hv
    by_cases hd : d1 = d2
    · subst hd
      by_cases hp : (a ^^ p1) = (b ^^ p2)
      · refine ⟨by simp [comb, hp], by simp [comb, hp, okR, hu], by simp [comb, hp],
          by simp [comb, hp], ?_⟩
        simp only [comb, ite_true, hp, List.foldl_nil, ev]
        cases hw : w.getD d1 false <;> cases a <;> cases b <;> cases p1 <;> cases p2 <;>
          simp_all
      · refine ⟨by simp [comb, hp], by simp [comb, hp, okR], by simp [comb, hp],
          by simp [comb, hp], ?_⟩
        simp only [comb, ite_true, hp, ite_false, List.foldl_nil, ev]
        cases hw : w.getD d1 false <;> cases a <;> cases b <;> cases p1 <;> cases p2 <;>
          simp_all
    · by_cases hlt : d1 < d2
      · refine ⟨by simp [comb, hd, hlt, stepW], by simp [comb, hd, hlt, okR, stepW],
          ⟨by simp only [comb, hd, hlt, ite_false, ite_true, List.mem_singleton]
              rintro g rfl; exact ⟨_, _, rfl⟩,
           by simp only [comb, hd, hlt, ite_false, ite_true, List.mem_singleton]
              rintro g rfl; exact ⟨hlt, hv⟩, ?_⟩⟩
        simp only [comb, hd, hlt, ite_false, ite_true, List.foldl_cons, List.foldl_nil, stepW,
          ev, andG]
        rw [List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self]
        simp only [List.getD_cons_zero, Bool.xor_false]
        cases w.getD d1 false <;> cases w.getD d2 false <;> cases a <;> cases b <;>
          cases p1 <;> cases p2 <;> rfl
      · have hgt : d2 < d1 := by omega
        refine ⟨by simp [comb, hd, hlt, stepW], by simp [comb, hd, hlt, okR, stepW],
          ⟨by simp only [comb, hd, hlt, ite_false, List.mem_singleton]
              rintro g rfl; exact ⟨_, _, rfl⟩,
           by simp only [comb, hd, hlt, ite_false, List.mem_singleton]
              rintro g rfl; exact ⟨hgt, hu⟩, ?_⟩⟩
        simp only [comb, hd, hlt, ite_false, List.foldl_cons, List.foldl_nil, stepW, ev, andG]
        rw [List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self]
        simp only [List.getD_cons_zero, Bool.xor_false]
        cases w.getD d1 false <;> cases w.getD d2 false <;> cases a <;> cases b <;>
          cases p1 <;> cases p2 <;> rfl

lemma comb_struct (top : ℕ) (a b : Bool) (u v : Bool ⊕ (ℕ × Bool))
    (hu : okR top u) (hv : okR top v) :
    let c := comb top a b u v
    c.2.length ≤ 1 ∧ okR (top + c.2.length) c.1 ∧
    (∀ g ∈ c.2, ∃ a' b' : Bool, g.op = fun x y => x == a' && y == b') ∧
    (∀ g ∈ c.2, g.left < g.right ∧ g.right < top) := by
  have hl : (List.replicate top false).length = top := List.length_replicate
  have h := comb_spec (List.replicate top false) a b u v (by rw [hl]; exact hu)
    (by rw [hl]; exact hv)
  dsimp only at h ⊢
  rw [hl, foldl_len, hl] at h
  obtain ⟨h1, h2, h3, h4, -⟩ := h
  exact ⟨by omega, h2, h3, h4⟩

lemma stepW_getD_ne (w : List Bool) (g : BinaryGate) (k : ℕ) (hk : k ≠ w.length) :
    (stepW w g).getD k false = w.getD k false := by
  rcases Nat.lt_or_gt_of_ne hk with h | h
  · simp only [stepW]; rw [List.getD_append _ _ _ _ h]
  · rw [List.getD_eq_default _ _ (by simp [stepW]; omega),
      List.getD_eq_default _ _ (by omega)]

def Inv (n : ℕ) (gs : List BinaryGate) : Prop :=
  ∃ (ds : List BinaryGate) (r : ℕ → Bool ⊕ (ℕ × Bool)),
    ds.length ≤ gs.length ∧
    (∀ g ∈ ds, ∃ a b : Bool, g.op = fun x y => x == a && y == b) ∧
    (∀ i (h : i < ds.length), ds[i].left < ds[i].right ∧ ds[i].right < n + i) ∧
    (∀ k, okR (n + ds.length) (r k)) ∧
    (∀ x : List Bool, x.length = n → ∀ k,
      (gs.foldl stepW (x ++ [false])).getD k false = ev (ds.foldl stepW x) (r k))

lemma inv_all (n : ℕ) (gs : List BinaryGate)
    (hg : ∀ g ∈ gs, ∃ a b : Bool, g.op = fun x y => x == a && y == b) : Inv n gs := by
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨[], fun k => if k < n then Sum.inr (k, false) else Sum.inl false,
      by simp, by simp, by simp, ?_, ?_⟩
    · intro k
      by_cases hk : k < n <;> simp [hk, okR]
    · intro x hx k
      by_cases hk : k < n
      · simp only [hk, ite_true, List.foldl_nil, ev, Bool.xor_false]
        rw [List.getD_append _ _ _ _ (by omega)]
      · simp only [hk, ite_false, List.foldl_nil, ev]
        by_cases hkn : k = n
        · subst hkn
          rw [List.getD_append_right _ _ _ _ (by omega)]
          simp [hx]
        · rw [List.getD_eq_default _ _ (by simp; omega)]
  | append_singleton gs g ih =>
    obtain ⟨ds, r, hlen, hand, hord, hok, hev⟩ :=
      ih (fun g' hg' => hg g' (List.mem_append_left _ hg'))
    obtain ⟨a, b, hab⟩ := hg g (by simp)
    let K := n + 1 + gs.length
    let rl := if g.left < K then r g.left else Sum.inl false
    let rr := if g.right < K then r g.right else Sum.inl false
    have hrl : okR (n + ds.length) rl := by
      simp only [rl]; split_ifs
      · exact hok _
      · trivial
    have hrr : okR (n + ds.length) rr := by
      simp only [rr]; split_ifs
      · exact hok _
      · trivial
    let c := comb (n + ds.length) a b rl rr
    obtain ⟨s1, s2, s3, s4⟩ : c.2.length ≤ 1 ∧ okR (n + ds.length + c.2.length) c.1 ∧
        (∀ g ∈ c.2, ∃ a' b' : Bool, g.op = fun x y => x == a' && y == b') ∧
        (∀ g ∈ c.2, g.left < g.right ∧ g.right < n + ds.length) :=
      comb_struct (n + ds.length) a b rl rr hrl hrr
    refine ⟨ds ++ c.2, fun k => if k = K then c.1 else r k, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [List.length_append, List.length_singleton]; omega
    · intro g' hg'
      rcases List.mem_append.1 hg' with h | h
      · exact hand g' h
      · exact s3 g' h
    · intro i hi
      by_cases hid : i < ds.length
      · rw [List.getElem_append_left hid]; exact hord i hid
      · have hi1 : i - ds.length < c.2.length := by
          simp only [List.length_append] at hi; omega
        rw [List.getElem_append_right (by omega)]
        have := s4 _ (List.getElem_mem hi1)
        omega
    · intro k
      simp only [List.length_append]
      split_ifs
      · simpa [Nat.add_assoc] using s2
      · exact okR_mono (by omega) _ (hok k)
    · intro x hx k
      have hCl : (gs.foldl stepW (x ++ [false])).length = K := by
        rw [foldl_len]; simp only [List.length_append, List.length_singleton, hx, K]
      have hDl : (ds.foldl stepW x).length = n + ds.length := by rw [foldl_len, hx]
      rw [foldl_snoc, List.foldl_append]
      by_cases hkK : k = K
      · subst hkK
        simp only [ite_true]
        have hspec := comb_spec (ds.foldl stepW x) a b rl rr (by rw [hDl]; exact hrl)
          (by rw [hDl]; exact hrr)
        rw [hDl] at hspec
        rw [hspec.2.2.2.2]
        simp only [stepW]
        rw [← hCl, List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self]
        simp only [List.getD_cons_zero, hab]
        have hside : ∀ j, (gs.foldl stepW (x ++ [false])).getD j false =
            ev (ds.foldl stepW x) (if j < K then r j else Sum.inl false) := by
          intro j
          split_ifs with hj
          · exact hev x hx j
          · rw [List.getD_eq_default _ _ (by omega)]; rfl
        rw [hside g.left, hside g.right]
      · simp only [hkK, ite_false]
        rw [stepW_getD_ne _ _ _ (by omega), hev x hx k]
        obtain ⟨t, ht⟩ := foldl_ext c.2 (ds.foldl stepW x)
        rw [ht, ev_ext _ _ _ (by rw [hDl]; exact hok k)]
end PEqualNP.Outside.L_meta_3915

theorem PEqualNP.Outside.L_meta_3915 : have x1 : PEqualNP.MetaComplexity.BinaryCircuit → Prop := fun (x1 : PEqualNP.MetaComplexity.BinaryCircuit) => ∀ x2 ∈ x1.gates, ∃ (x4 : Bool) (x5 : Bool), x2.op = fun (x6 x7 : Bool) => x6 == x4 && x7 == x5; have x2 : ℕ → PEqualNP.MetaComplexity.BinaryCircuit → Prop := fun (x2 : ℕ) (x3 : PEqualNP.MetaComplexity.BinaryCircuit) => ∀ (x4 : Fin x3.size), (x3.gates.get x4).left < (x3.gates.get x4).right ∧ (x3.gates.get x4).right < x2 + ↑x4; ∀ (x3 : ℕ) (x4 : PEqualNP.MetaComplexity.BinaryCircuit) (x5 : Bool), x1 x4 → ∃ (x7 : PEqualNP.MetaComplexity.BinaryCircuit) (x8 : Bool), x7.size ≤ x4.size ∧ x1 x7 ∧ x2 x3 x7 ∧ (x7.size = (0 : ℕ) ∨ x7.output = x3 + x7.size - (1 : ℕ)) ∧ ∀ (x9 : List Bool), x9.length = x3 → (x7.eval x9 != x8) = (x4.eval (x9 ++ [Bool.false]) != x5) := by
  intro P Q n C x5 hC
  obtain ⟨ds, r, hlen, hand, hord, hok, hev⟩ := L_meta_3915.inv_all n C.gates hC
  have hCe : ∀ x : List Bool, x.length = n →
      C.eval (x ++ [false]) = L_meta_3915.ev (ds.foldl L_meta_3915.stepW x) (r C.output) := by
    intro x hx
    rw [← hev x hx C.output]
    rfl
  have hord' : ∀ j, ∀ i (h : i < (ds.take j).length),
      (ds.take j)[i].left < (ds.take j)[i].right ∧ (ds.take j)[i].right < n + i := by
    intro j i h
    rw [List.getElem_take]
    exact hord i (by simp at h; omega)
  have hokC := hok C.output
  rcases hro : r C.output with c | ⟨d, p⟩
  · refine ⟨⟨[], n⟩, c != x5, by simp [MetaComplexity.BinaryCircuit.size],
      by simp [P], by intro i; exact absurd i.2 (by simp [MetaComplexity.BinaryCircuit.size]),
      Or.inl rfl, ?_⟩
    intro x hx
    rw [hCe x hx, hro]
    have : (MetaComplexity.BinaryCircuit.mk [] n).eval x = false := by
      show x.getD n false = false
      exact List.getD_eq_default _ _ (le_of_eq hx)
    rw [this]
    cases c <;> cases x5 <;> rfl
  · rw [hro] at hokC
    simp only [L_meta_3915.okR] at hokC
    by_cases hdn : d < n
    · refine ⟨⟨[], d⟩, p ^^ x5, by simp [MetaComplexity.BinaryCircuit.size],
        by simp [P], by intro i; exact absurd i.2 (by simp [MetaComplexity.BinaryCircuit.size]),
        Or.inl rfl, ?_⟩
      intro x hx
      rw [hCe x hx, hro]
      simp only [L_meta_3915.ev]
      rw [L_meta_3915.foldl_getD _ _ _ (by omega)]
      show ((x.getD d false) != (p ^^ x5)) = ((x.getD d false ^^ p) != x5)
      cases x.getD d false <;> cases p <;> cases x5 <;> rfl
    · refine ⟨⟨ds.take (d - n + 1), d⟩, p ^^ x5, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [MetaComplexity.BinaryCircuit.size, List.length_take]; omega
      · intro g hg
        exact hand g (List.mem_of_mem_take hg)
      · intro i
        have := hord' (d - n + 1) i.1 i.2
        simp only [MetaComplexity.BinaryCircuit.size, List.get_eq_getElem]
        exact this
      · right
        simp only [MetaComplexity.BinaryCircuit.size, List.length_take]; omega
      · intro x hx
        rw [hCe x hx, hro]
        simp only [L_meta_3915.ev]
        have hsplit : ds.foldl L_meta_3915.stepW x =
            (ds.drop (d - n + 1)).foldl L_meta_3915.stepW
              ((ds.take (d - n + 1)).foldl L_meta_3915.stepW x) := by
          rw [← List.foldl_append, List.take_append_drop]
        rw [hsplit, L_meta_3915.foldl_getD _ _ _ (by rw [L_meta_3915.foldl_len]; simp; omega)]
        show (((ds.take (d - n + 1)).foldl L_meta_3915.stepW x).getD d false != (p ^^ x5)) =
          ((((ds.take (d - n + 1)).foldl L_meta_3915.stepW x).getD d false ^^ p) != x5)
        cases ((ds.take (d - n + 1)).foldl L_meta_3915.stepW x).getD d false <;> cases p <;>
          cases x5 <;> rfl
