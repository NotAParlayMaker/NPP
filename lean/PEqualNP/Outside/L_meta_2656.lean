import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2656

open PEqualNP.CircuitLowerBounds PEqualNP.BicliqueBlockCost
variable {n : ℕ}
abbrev V (n : ℕ) := Fin n
abbrev Sig (n : ℕ) := (V n → Bool) → Bool
abbrev Bank (n : ℕ) := ℕ → Sig n
abbrev Term (n : ℕ) := Option (V n) × ℕ
def pairX (u v : V n) (i : V n) := decide (i = u ∨ i = v)
def supp (f : Sig n) := Finset.univ.filter fun u => f (pairX u u)
lemma in_supp {f : Sig n} {u : V n} : u ∈ supp f ↔ f (pairX u u) = true := by simp [supp]
def MonoS (f : Sig n) := ∀ x y : V n → Bool, (∀ i, x i = true → y i = true) → f x = true → f y = true
def Good (G : SimpleGraph (V n)) (f : Sig n) := ∀ x, f x = true → ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true
def Four (G : SimpleGraph (V n)) := ∀ a b c d, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d → G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a
lemma pair_edge {G : SimpleGraph (V n)} {u v : V n}
    (h : ∃ a b, G.Adj a b ∧ pairX u v a = true ∧ pairX u v b = true) : G.Adj u v := by
  obtain ⟨a,b,hab,ha,hb⟩ := h
  simp only [pairX, decide_eq_true_eq] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with h | h <;> subst_vars <;> first | exact hab | exact hab.symm | exact (G.loopless.irrefl _ hab).elim
lemma safe_empty {G : SimpleGraph (V n)} {f : Sig n} (h : Good G f) : supp f = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro u hu
  exact G.loopless.irrefl u (pair_edge (h _ (in_supp.mp hu)))
lemma common {G : SimpleGraph (V n)} (h : Four G) {S : Finset (V n)} (hs : 1 < S.card)
    {c d : V n} (hc : ∀ v ∈ S, G.Adj c v) (hd : ∀ v ∈ S, G.Adj d v) : c = d := by
  by_contra hcd
  obtain ⟨a,b,ha,hb,hab⟩ := Finset.one_lt_card_iff.mp hs
  exact h c a d b (hc _ ha).ne hcd (hc _ hb).ne (hd _ ha).ne.symm hab (hd _ hb).ne
    (hc _ ha) (hd _ ha).symm (hd _ hb) (hc _ hb).symm
def Hit (W : Bank n) (t : Term n) (u v : V n) : Prop :=
  match t.1 with
  | none => W t.2 (pairX u v) = true
  | some c => (u = c ∧ v ∈ supp (W t.2)) ∨ (v = c ∧ u ∈ supp (W t.2))
def Valid (G : SimpleGraph (V n)) (W : Bank n) (K : Finset (V n)) (t : Term n) : Prop :=
  match t.1 with
  | none => supp (W t.2) = ∅
  | some c => c ∈ K ∧ (∀ v ∈ supp (W t.2), G.Adj c v) ∧ (t.2 < n ∨ 1 < (supp (W t.2)).card)
def Miss (f : Sig n) (u v : V n) := (supp f).Nonempty ∧ f (pairX u v) = true ∧ u ∉ supp f ∧ v ∉ supp f
def Covers (G : SimpleGraph (V n)) (W : Bank n) (K : Finset (V n)) (Q : Finset (Term n)) :=
  (∀ t ∈ Q, Valid G W K t) ∧ ∀ u v, G.Adj u v → (∃ t ∈ Q, Hit W t u v) ∨ ∃ i, Miss (W i) u v
def Inputs (W : Bank n) := ∀ i : V n, W i = fun x => x i
lemma input_supp {W : Bank n} (h : Inputs W) (i : V n) : supp (W i) = {i} := by
  ext u
  simp [in_supp, h i, pairX, eq_comm]
lemma canonical {W : Bank n} (hi : Inputs W) (j : ℕ) (hs : (supp (W j)).Nonempty) :
    ∃ i, supp (W i) = supp (W j) ∧ (i < n ∨ 1 < (supp (W i)).card) := by
  by_cases h : 1 < (supp (W j)).card
  · exact ⟨j,rfl,Or.inr h⟩
  · have hc := Finset.card_pos.mpr hs
    obtain ⟨a,ha⟩ := Finset.card_eq_one.mp (show (supp (W j)).card = 1 by omega)
    exact ⟨a, (input_supp hi a).trans ha.symm, Or.inl a.isLt⟩
lemma cross {G : SimpleGraph (V n)} {f g : Sig n} (hf : MonoS f) (hg : MonoS g)
    (hs : Good G (fun x => f x && g x)) {a b : V n} (ha : a ∈ supp f) (hb : b ∈ supp g) : G.Adj a b := by
  apply pair_edge (u := a) (v := b)
  apply hs
  apply Bool.and_eq_true_iff.mpr
  exact ⟨hf _ _ (by simp [pairX]) (in_supp.mp ha), hg _ _ (by simp [pairX]) (in_supp.mp hb)⟩
def CostBound (G : SimpleGraph (V n)) (m : ℕ) := ∃ F : Finset (Block n), IsBlockCover G F ∧
  (∑ p ∈ F, (p.1.card + p.2.card)) ≤ m
lemma finishCost {G : SimpleGraph (V n)} {m : ℕ} (h : CostBound G (m+1)) :
    HasBlockCost G m := by
  obtain ⟨F,hF,hc⟩ := h
  refine ⟨F,hF,?_⟩
  have hh : (∑ p ∈ F, blockCost p) + F.card = ∑ p ∈ F, (p.1.card + p.2.card) := by
    rw [show F.card = ∑ _p ∈ F, (1 : ℕ) by simp, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    have := Finset.card_pos.mpr (hF.1 p hp).2.1
    unfold blockCost
    omega
  by_cases he : F = ∅
  · simp [he, familyCost]
  · have := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr he)
    unfold familyCost
    omega
def Start (n : ℕ) : Bank n := fun j x => (List.ofFn x).getD j false
lemma start_in (i : V n) : Start n i = fun x => x i := by
  funext x
  simp [Start,List.getD_eq_getElem?_getD,i.isLt]
lemma start_out {j : ℕ} (hj : n ≤ j) : Start n j = fun _ => false := by
  funext x
  exact List.getD_eq_default _ _ (by simpa using hj)
lemma start_mem {j : ℕ} {u : V n} : u ∈ supp (Start n j) ↔ u.val = j := by
  by_cases hj : j < n
  · rw [input_supp (W := Start n) (fun i => start_in i) ⟨j,hj⟩]
    simp [Fin.ext_iff]
  · simp [in_supp,start_out (by omega : n ≤ j)]
    omega
def Budget (G : SimpleGraph (V n)) (W : Bank n) (m : ℕ) := ∀ K Q, Covers G W K Q → CostBound G (m + K.card + Q.card)
lemma start_budget (G : SimpleGraph (V n)) : Budget G (Start n) 0 := by
  classical
  intro K Q h
  let L (c : V n) := Finset.univ.filter fun v : V n => (some c, v.val) ∈ Q
  let A := K.filter fun c => (L c).Nonempty
  let p (c : V n) : Block n := ({c},L c)
  have adj (c v : V n) (hv : v ∈ L c) : G.Adj c v := by
    have ht : (some c,v.val) ∈ Q := (Finset.mem_filter.mp hv).2
    exact (h.1 _ ht).2.1 _ (start_mem.mpr rfl)
  have block (c : V n) (hc : c ∈ A) : IsBlock G (p c) := by
    refine ⟨Finset.disjoint_left.mpr ?_, by simp [p], (Finset.mem_filter.mp hc).2, ?_⟩
    · intro a ha hb
      have e : a = c := Finset.mem_singleton.mp ha
      subst a
      exact (adj c c hb).ne rfl
    · intro a ha v hv
      simpa [Finset.mem_singleton.mp ha] using adj c v hv
  refine ⟨A.image p, ⟨?_,?_⟩,?_⟩
  · intro b hb
    obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hb
    exact block c hc
  · intro u v huv
    rcases h.2 u v huv with ⟨⟨o,j⟩,ht,hh⟩ | ⟨j,hs,hon,hnu,hnv⟩
    · cases o with
      | none =>
        have hem : supp (Start n j) = ∅ := h.1 _ ht
        by_cases hj : j < n
        · have hm := start_mem (n := n) (u := ⟨j,hj⟩) (j := j) |>.mpr rfl
          simp [hem] at hm
        · change Start n j _ = true at hh
          simp [start_out (by omega : n ≤ j)] at hh
      | some c =>
        have hk := (h.1 _ ht).1
        have emit (a b : V n) (ha : a = c) (hb : b ∈ supp (Start n j)) :
            ∃ z ∈ A.image p, a ∈ z.1 ∧ b ∈ z.2 := by
          have e := start_mem.mp hb
          have hb' : b ∈ L c := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa only [e] using ht⟩
          exact ⟨p c, Finset.mem_image.mpr ⟨c,Finset.mem_filter.mpr ⟨hk,b,hb'⟩,rfl⟩, by simpa [p] using ha,hb'⟩
        rcases hh with ⟨ha,hb⟩ | ⟨ha,hb⟩
        · obtain ⟨z,hz,hh⟩ := emit _ _ ha hb
          exact ⟨z,hz,Or.inl hh⟩
        · obtain ⟨z,hz,hh⟩ := emit _ _ ha hb
          exact ⟨z,hz,Or.inr hh⟩
    · obtain ⟨a,ha⟩ := hs
      have e := start_mem.mp ha
      subst j
      rw [start_in] at hon
      simp only [pairX,decide_eq_true_eq] at hon
      rcases hon with rfl | rfl <;> exact False.elim (by first | exact hnu ha | exact hnv ha)
  · have hf (c : V n) : (L c).card ≤ (Q.filter fun t => t.1 = some c).card := by
      apply Finset.card_le_card_of_injOn (fun v : V n => (some c,v.val))
      · intro v hv
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hv).2,rfl⟩
      · intro u hu v hv eq
        exact Fin.ext (congrArg Prod.snd eq)
    have sumh : (∑ c ∈ A, (L c).card) ≤ Q.card := by
      calc
        _ ≤ ∑ c ∈ A, (Q.filter fun t => t.1 = some c).card := Finset.sum_le_sum fun c _ => hf c
        _ ≤ Q.card := by
          rw [← Finset.card_biUnion]
          · apply Finset.card_le_card
            intro t ht
            obtain ⟨c,_,hc⟩ := Finset.mem_biUnion.mp ht
            exact (Finset.mem_filter.mp hc).1
          · intro c hc d hd hcd
            exact Finset.disjoint_left.mpr (fun t h1 h2 => hcd (Option.some.inj ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)))
    rw [Finset.sum_image]
    · simp only [p, Finset.card_singleton, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one, zero_add]
      have := Finset.card_le_card (Finset.filter_subset (fun c => (L c).Nonempty) K)
      change A.card ≤ K.card at this
      omega
    · intro a ha b hb e
      simpa [p] using congrArg Prod.fst e
def New (W : Bank n) (k : ℕ) (f : Sig n) : Bank n := Function.update W k f
def trim (Q : Finset (Term n)) (k : ℕ) := Q.filter fun t => t.2 ≠ k
def Res (W : Bank n) (R : Finset (Term n)) (u v : V n) :=
  (∃ t ∈ R, Hit W t u v) ∨ ∃ i, Miss (W i) u v
lemma transfer {G : SimpleGraph (V n)} {W : Bank n} {m k : ℕ} {f : Sig n} (ind : Budget G W m)
    {K Q} (h : Covers G (New W k f) K Q) {J R} (inc : K ⊆ J)
    (val : ∀ t ∈ R, Valid G W J t)
    (cost : J.card + (trim Q k).card + R.card ≤ K.card + Q.card + 1)
    (rep : ∀ u v, (Miss f u v ∨ ∃ t ∈ Q, t.2 = k ∧ Hit (New W k f) t u v) → Res W R u v) :
    CostBound G (m+1+K.card+Q.card) := by
  classical
  have old {t : Term n} (ht : t.2 ≠ k) : New W k f t.2 = W t.2 := Function.update_of_ne ht ..
  obtain ⟨F,hF,hc⟩ := ind J (trim Q k ∪ R) (by
    constructor
    · intro t ht
      rcases Finset.mem_union.mp ht with ht | ht
      · obtain ⟨hq,hne⟩ := Finset.mem_filter.mp ht
        have hv := h.1 t hq
        cases t with
        | mk o w =>
          cases o with
          | none => simpa only [Valid,old hne] using hv
          | some c =>
            exact ⟨inc hv.1, by simpa only [old hne] using hv.2⟩
      · exact val _ ht
    · intro u v huv
      have liftR (hh : Res W R u v) : Res W (trim Q k ∪ R) u v := by
        rcases hh with ⟨t,ht,hh⟩ | hh
        · exact Or.inl ⟨t,Finset.mem_union_right _ ht,hh⟩
        · exact Or.inr hh
      rcases h.2 u v huv with ⟨t,ht,hh⟩ | ⟨i,hm⟩
      · by_cases he : t.2 = k
        · exact liftR (rep _ _ (Or.inr ⟨t,ht,he,hh⟩))
        · refine Or.inl ⟨t,Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨ht,he⟩),?_⟩
          unfold Hit at hh ⊢
          rwa [old he] at hh
      · by_cases he : i = k
        · subst i
          exact liftR (rep _ _ (Or.inl (by simpa [New] using hm)))
        · exact Or.inr ⟨i,by simpa [New,he] using hm⟩)
  have := Finset.card_union_le (trim Q k) R
  exact ⟨F,hF,by omega⟩
lemma trim_le (Q : Finset (Term n)) (k : ℕ) : (trim Q k).card ≤ Q.card := Finset.card_filter_le ..
lemma trim_lt {Q : Finset (Term n)} {k : ℕ} {o : Option (V n)} (h : (o,k) ∈ Q) :
    (trim Q k).card < Q.card := by
  apply Finset.card_lt_card
  exact Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _,fun he => by
    have hm : (o,k) ∈ trim Q k := by rw [he]; exact h
    exact (Finset.mem_filter.mp hm).2 rfl⟩
lemma used_unique {G : SimpleGraph (V n)} {W : Bank n} {K Q} (hv : Covers G W K Q)
    (four : Four G) {k : ℕ} (hk : n ≤ k) {o p : Option (V n)} (ho : (o,k) ∈ Q) (hp : (p,k) ∈ Q) : o = p := by
  have h1 := hv.1 _ ho
  have h2 := hv.1 _ hp
  cases o <;> cases p
  · rfl
  · have h0 : supp (W k) = ∅ := h1
    have hpos := h2.2.2
    simp [h0, Nat.not_lt.mpr hk] at hpos
  · have h0 : supp (W k) = ∅ := h2
    have hpos := h1.2.2
    simp [h0, Nat.not_lt.mpr hk] at hpos
  · exact congrArg some (common four (h1.2.2.resolve_left (Nat.not_lt.mpr hk)) h1.2.1 h2.2.1)
lemma skip {G : SimpleGraph (V n)} {W : Bank n} {m k : ℕ} {f : Sig n} (ind : Budget G W m)
    {K Q} (h : Covers G (New W k f) K Q) (hu : ∀ o, (o,k) ∉ Q) (he : supp f = ∅) :
    CostBound G (m+1+K.card+Q.card) := by
  apply transfer ind h (J := K) (R := ∅) (by rfl) (by simp)
  · have := trim_le Q k
    simp; omega
  · rintro u v (hm | ⟨⟨o,j⟩,ht,rfl,hh⟩)
    · exact False.elim (by simpa [he] using hm.1)
    · exact (hu o ht).elim
lemma or_sup (f g : Sig n) : supp (fun x => f x || g x) = supp f ∪ supp g := by
  ext i
  simp [in_supp]
lemma and_star {G : SimpleGraph (V n)} {W : Bank n} {a b : ℕ} (hi : Inputs W)
    {c : V n} (ha : supp (W a) = {c}) (hb : (supp (W b)).Nonempty)
    (hadj : ∀ v ∈ supp (W b), G.Adj c v) (K : Finset (V n)) :
    ∃ t : Term n, Valid G W (insert c K) t ∧ ∀ u v, W a (pairX u v) = true → W b (pairX u v) = true →
      Res W {t} u v := by
  obtain ⟨j,hj,hj'⟩ := canonical hi b hb
  refine ⟨(some c,j), ⟨by simp,by simpa [hj] using hadj,hj'⟩,?_⟩
  intro u v hua hub
  by_cases hcu : u = c ∨ v = c
  · by_cases hl : u ∈ supp (W b) ∨ v ∈ supp (W b)
    · apply Or.inl
      refine ⟨_,Finset.mem_singleton_self _,?_⟩
      change (u = c ∧ v ∈ supp (W j)) ∨ (v = c ∧ u ∈ supp (W j))
      rw [hj]
      have hn : c ∉ supp (W b) := fun h => (hadj c h).ne rfl
      grind
    · exact Or.inr ⟨b,hb,hub,fun h => hl (Or.inl h),fun h => hl (Or.inr h)⟩
  · refine Or.inr ⟨a,by simp [ha],hua,?_,?_⟩
    · intro hu
      exact hcu (Or.inl (by simpa [ha] using hu))
    · intro hv
      exact hcu (Or.inr (by simpa [ha] using hv))
lemma and_step {G : SimpleGraph (V n)} {W : Bank n} {k m a b : ℕ} (hi : Inputs W)
    (ind : Budget G W m) (four : Four G) (hk : n ≤ k) (ma : MonoS (W a)) (mb : MonoS (W b))
    (safe : Good G (fun x => W a x && W b x)) :
    Budget G (New W k (fun x => W a x && W b x)) (m+1) := by
  classical
  intro K Q h
  let f : Sig n := fun x => W a x && W b x
  have hem : supp f = ∅ := safe_empty safe
  by_cases used : ∃ o, (o,k) ∈ Q
  · obtain ⟨o,ho⟩ := used
    have oe : o = none := by
      cases o with
      | none => rfl
      | some c =>
        have hh := (h.1 _ ho).2.2
        change k < n ∨ 1 < (supp (New W k f k)).card at hh
        simp [New,hem,Nat.not_lt.mpr hk] at hh
    subst o
    have cost := trim_lt ho
    have extract (u v : V n) (hh : Miss f u v ∨ ∃ t ∈ Q, t.2 = k ∧ Hit (New W k f) t u v) :
        W a (pairX u v) = true ∧ W b (pairX u v) = true := by
      rcases hh with hm | ⟨⟨p,j⟩,ht,rfl,hh⟩
      · exact False.elim (by simpa [hem] using hm.1)
      · have eq := used_unique h four hk ht ho
        subst p
        simpa [Hit,New,f] using hh
    by_cases en : supp (W a) = ∅ ∨ supp (W b) = ∅
    · obtain ⟨j,hj,which⟩ : ∃ j, supp (W j) = ∅ ∧ (j = a ∨ j = b) := by
        rcases en with he | he
        · exact ⟨a,he,Or.inl rfl⟩
        · exact ⟨b,he,Or.inr rfl⟩
      apply transfer ind h (J := K) (R := {(none,j)}) (by rfl)
      · simpa [Valid] using hj
      · simp; omega
      · intro u v hh
        obtain ⟨ha,hb⟩ := extract u v hh
        exact Or.inl ⟨_,Finset.mem_singleton_self _,by rcases which with rfl | rfl <;> assumption⟩
    · have ea := Finset.nonempty_iff_ne_empty.mpr (not_or.mp en).1
      have eb := Finset.nonempty_iff_ne_empty.mpr (not_or.mp en).2
      have ab := fun x hx y hy => cross ma mb safe (a := x) (b := y) hx hy
      have ss : (supp (W a)).card = 1 ∨ (supp (W b)).card = 1 := by
        by_cases ha : 1 < (supp (W a)).card
        · right
          obtain ⟨y,hy⟩ := eb
          apply Finset.card_eq_one.mpr
          refine ⟨y,Finset.eq_singleton_iff_unique_mem.mpr ⟨hy,?_⟩⟩
          intro z hz
          exact common four ha (fun v hv => (ab _ hv _ hz).symm) (fun v hv => (ab _ hv _ hy).symm)
        · have := Finset.card_pos.mpr ea
          omega
      obtain ⟨c,t,ht,hr⟩ : ∃ c t, Valid G W (insert c K) t ∧ ∀ u v, W a (pairX u v) = true →
          W b (pairX u v) = true → Res W {t} u v := by
        rcases ss with hs | hs
        · obtain ⟨c,hc⟩ := Finset.card_eq_one.mp hs
          obtain ⟨t,ht,hr⟩ := and_star hi hc eb (ab c (by simp [hc])) K
          exact ⟨c,t,ht,hr⟩
        · obtain ⟨c,hc⟩ := Finset.card_eq_one.mp hs
          obtain ⟨t,ht,hr⟩ := and_star hi hc ea (fun v hv => (ab v hv c (by simp [hc])).symm) K
          exact ⟨c,t,ht,fun u v ha hb => hr u v hb ha⟩
      apply transfer ind h (J := insert c K) (R := {t}) (Finset.subset_insert ..) (by simpa using ht)
      · have := Finset.card_insert_le c K
        simp only [Finset.card_singleton]
        omega
      · intro u v hh
        exact hr _ _ (extract _ _ hh).1 (extract _ _ hh).2
  · exact skip ind h (by simpa using used) hem
lemma child {G : SimpleGraph (V n)} {W : Bank n} (hi : Inputs W) (K : Finset (V n)) (j : ℕ)
    (o : Option (V n)) (ok : ∀ c, o = some c → c ∈ K ∧ ∀ v ∈ supp (W j), G.Adj c v) :
    ∃ R : Finset (Term n), (∀ t ∈ R, Valid G W K t) ∧ R.card ≤ 1 ∧
      (o = none → (supp (W j)).Nonempty → R = ∅) ∧
      (∀ u v, W j (pairX u v) = true → u ∉ supp (W j) → v ∉ supp (W j) → Res W R u v) ∧
      ∀ c, o = some c → ∀ u v, ((u = c ∧ v ∈ supp (W j)) ∨ (v = c ∧ u ∈ supp (W j))) → Res W R u v := by
  classical
  by_cases he : supp (W j) = ∅
  · refine ⟨{(none,j)}, by simpa [Valid] using he, by simp, by simp [he], ?_, by simp [he]⟩
    exact fun u v hh _ _ => Or.inl ⟨_,Finset.mem_singleton_self _,hh⟩
  · have hn := Finset.nonempty_iff_ne_empty.mpr he
    cases o with
    | none =>
      exact ⟨∅,by simp,by simp,by simp,fun u v hh hu hv => Or.inr ⟨j,hn,hh,hu,hv⟩,by simp⟩
    | some c =>
      obtain ⟨l,hl,hs⟩ := canonical hi j hn
      have hv : Valid G W K (some c,l) := ⟨(ok c rfl).1, by simpa [hl] using (ok c rfl).2,hs⟩
      refine ⟨{(some c,l)},by simpa using hv,by simp,by simp,fun u v hh hu hv => Or.inr ⟨j,hn,hh,hu,hv⟩,?_⟩
      rintro d eq u v hh
      cases eq
      exact Or.inl ⟨_,Finset.mem_singleton_self _,by simpa [Hit,hl] using hh⟩
lemma res_mono {W : Bank n} {R S : Finset (Term n)} (h : R ⊆ S) {u v} (hh : Res W R u v) : Res W S u v := by
  rcases hh with ⟨t,ht,hh⟩ | hh
  · exact Or.inl ⟨t,h ht,hh⟩
  · exact Or.inr hh
lemma or_step {G : SimpleGraph (V n)} {W : Bank n} {k m a b : ℕ} (hi : Inputs W)
    (ind : Budget G W m) (four : Four G) (hk : n ≤ k) :
    Budget G (New W k (fun x => W a x || W b x)) (m+1) := by
  classical
  intro K Q h
  let f : Sig n := fun x => W a x || W b x
  let U := New W k f
  have hek : U k = f := Function.update_self ..
  have hs : supp f = supp (W a) ∪ supp (W b) := or_sup ..
  by_cases sk : (∀ o, (o,k) ∉ Q) ∧ supp f = ∅
  · exact skip ind h sk.1 sk.2
  obtain ⟨o,unique,ok⟩ : ∃ o : Option (V n), (∀ p, (p,k) ∈ Q → p = o) ∧
      (∀ c, o = some c → c ∈ K ∧ ∀ v ∈ supp f, G.Adj c v) ∧ (o = none ∨ (o,k) ∈ Q) := by
    by_cases ex : ∃ p, (p,k) ∈ Q
    · obtain ⟨p,hp⟩ := ex
      refine ⟨p,fun q hq => used_unique h four hk hq hp,?_,Or.inr hp⟩
      rintro c rfl
      have H : Valid G U K (some c,k) := h.1 _ hp
      exact ⟨H.1,by simpa only [← hek] using H.2.1⟩
    · exact ⟨none,fun p hp => (ex ⟨p,hp⟩).elim,by simp,Or.inl rfl⟩
  obtain ⟨A,vA,cA,eA,mA,lA⟩ := child (G := G) hi K a o (by
    intro c he
    exact ⟨(ok.1 c he).1,fun v hv => (ok.1 c he).2 v (by rw [hs]; exact Finset.mem_union_left _ hv)⟩)
  obtain ⟨B,vB,cB,eB,mB,lB⟩ := child (G := G) hi K b o (by
    intro c he
    exact ⟨(ok.1 c he).1,fun v hv => (ok.1 c he).2 v (by rw [hs]; exact Finset.mem_union_right _ hv)⟩)
  apply transfer ind h (J := K) (R := A ∪ B) (by rfl)
  · intro t ht
    exact (Finset.mem_union.mp ht).elim (vA t) (vB t)
  · have hu := Finset.card_union_le A B
    by_cases used : (o,k) ∈ Q
    · have := trim_lt used
      omega
    · have hno : ∀ p, (p,k) ∉ Q := fun p hp => used (unique p hp ▸ hp)
      have hne : supp f ≠ ∅ := fun he => sk ⟨hno,he⟩
      have hnone := ok.2.resolve_right used
      have := trim_le Q k
      by_cases emp : supp (W a) = ∅
      · have neb : supp (W b) ≠ ∅ := by intro e; simp [hs,emp,e] at hne
        have cz : B.card = 0 := by simp [eB hnone (Finset.nonempty_iff_ne_empty.mpr neb)]
        omega
      · have cz : A.card = 0 := by simp [eA hnone (Finset.nonempty_iff_ne_empty.mpr emp)]
        omega
  · intro u v hh
    have leftR := @res_mono n W A (A ∪ B) Finset.subset_union_left u v
    have rightR := @res_mono n W B (A ∪ B) Finset.subset_union_right u v
    have pass (onf : f (pairX u v) = true) (nu : u ∉ supp f) (nv : v ∉ supp f) : Res W (A ∪ B) u v := by
      simp only [hs,Finset.mem_union,not_or] at nu nv
      rcases Bool.or_eq_true_iff.mp onf with ha | hb
      · exact leftR (mA u v ha nu.1 nv.1)
      · exact rightR (mB u v hb nu.2 nv.2)
    rcases hh with hm | ⟨⟨p,j⟩,ht,hej,hit⟩
    · exact pass hm.2.1 hm.2.2.1 hm.2.2.2
    · change j = k at hej
      subst j
      cases p with
      | none =>
        have he : supp (U k) = ∅ := h.1 _ ht
        rw [hek] at he
        exact pass (by simpa [Hit,New,f] using hit) (by simp [he]) (by simp [he])
      | some c =>
        have eq := (unique _ ht).symm
        change (u = c ∧ v ∈ supp (U k)) ∨ (v = c ∧ u ∈ supp (U k)) at hit
        rw [hek,hs] at hit
        simp only [Finset.mem_union] at hit
        rcases hit with ⟨eq',ha | hb⟩ | ⟨eq',ha | hb⟩
        · exact leftR (lA c eq _ _ (Or.inl ⟨eq',ha⟩))
        · exact rightR (lB c eq _ _ (Or.inl ⟨eq',hb⟩))
        · exact leftR (lA c eq _ _ (Or.inr ⟨eq',ha⟩))
        · exact rightR (lB c eq _ _ (Or.inr ⟨eq',hb⟩))

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem eval_eq (gs : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.eval ⟨gs, o⟩ x = (wf gs x).getD o false := rfl

theorem wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
  simp [wf, List.foldl_append]

theorem wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i (by simp; omega)
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem wf_prefix (pre post : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length + pre.length) :
    (wf (pre ++ post) w).getD i false = (wf pre w).getD i false := by
  have : wf (pre ++ post) w = wf post (wf pre w) := by simp [wf, List.foldl_append]
  rw [this]
  exact wf_keep post _ i (by rw [wf_len]; exact hi)

theorem getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega

def bank (gs : List Gate) : Bank n := fun i x => (wf gs (List.ofFn x)).getD i false
def gateSig (gs : List Gate) (g : Gate) : Sig n := fun x =>
  g.op.eval (g.inputs.map fun i => bank gs i x)
lemma blen (gs : List Gate) (x : V n → Bool) : (wf gs (List.ofFn x)).length = n + gs.length := by simp [wf_len]
lemma binputs (gs : List Gate) : Inputs (bank (n := n) gs) := by
  intro i
  funext x
  change (wf gs (List.ofFn x)).getD i false = _
  rw [wf_keep _ _ _ (by simp)]
  exact congrFun (start_in i) x
lemma bdead (gs : List Gate) : bank (n := n) gs (n+gs.length) = fun _ => false := by
  funext x
  exact List.getD_eq_default _ _ (by rw [blen])
lemma bsnoc (gs : List Gate) (g : Gate) : bank (n := n) (gs ++ [g]) = New (bank gs) (n+gs.length) (gateSig gs g) := by
  funext j x
  unfold bank New
  rw [wf_snoc]
  rcases Nat.lt_trichotomy j (n+gs.length) with hj | rfl | hj
  · rw [getD_snoc_lt _ _ _ (by rwa [blen]),Function.update_of_ne (by omega : j ≠ n+gs.length)]
  · rw [← blen gs x,getD_snoc_eq,Function.update_self]
    rfl
  · rw [getD_snoc_gt _ _ _ (by rwa [blen]),Function.update_of_ne (by omega : j ≠ n+gs.length)]
    symm
    exact List.getD_eq_default _ _ (by rw [blen]; omega)
lemma mono_new {W : Bank n} {k : ℕ} {f : Sig n} (hw : ∀ i, MonoS (W i)) (hf : MonoS f) :
    ∀ i, MonoS (New W k f i) := by
  intro i
  by_cases h : i = k
  · simpa [New,h] using hf
  · simpa [New,h] using hw i
lemma main_ind (G : SimpleGraph (V n)) (four : Four G) (gs : List Gate)
    (leg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (safe : ∀ pre g post, gs = pre ++ g :: post → g.op = GateOp.and → Good G (gateSig pre g)) :
    Budget G (bank gs) gs.length ∧ ∀ i, MonoS (bank (n := n) gs i) := by
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨start_budget G,?_⟩
    intro i
    change MonoS (Start n i)
    by_cases hj : i < n
    · rw [start_in (⟨i,hj⟩ : V n)]
      exact fun x y h => h _
    · rw [start_out (by omega)]
      simp [MonoS]
  | append_singleton gs g ih =>
    obtain ⟨ih,im⟩ := ih (fun g hg => leg g (List.mem_append_left _ hg)) (by
      intro pre g' post he hop
      apply safe pre g' (post ++ [g]) _ hop
      simp [he,List.append_assoc])
    obtain ⟨hop,hl⟩ := leg g (by simp)
    rw [bsnoc, List.length_append,List.length_singleton]
    have hh := binputs (n := n) gs
    have hk : n ≤ n + gs.length := by omega
    rcases hop with hop | hop
    · have sg := safe gs g [] rfl hop
      obtain ⟨a,b,he⟩ : ∃ a b, gateSig (n := n) gs g = fun x => bank gs a x && bank gs b x := by
        cases he : g.inputs with
        | nil =>
          obtain ⟨u,v,_,hu,_⟩ := sg (fun _ => false) (by simp [gateSig,hop,he,GateOp.eval])
          contradiction
        | cons a t =>
          cases t with
          | nil => exact ⟨a,a,by funext x; simp [gateSig,hop,he,GateOp.eval]⟩
          | cons b t =>
            have ht : t = [] := by simpa [he] using hl
            subst t
            exact ⟨a,b,by funext x; simp [gateSig,hop,he,GateOp.eval]⟩
      rw [he] at sg ⊢
      refine ⟨and_step hh ih four hk (im _) (im _) sg,mono_new im ?_⟩
      intro x y hxy h
      exact Bool.and_eq_true_iff.mpr ⟨im a x y hxy (Bool.and_eq_true_iff.mp h).1,im b x y hxy (Bool.and_eq_true_iff.mp h).2⟩
    · obtain ⟨a,b,he⟩ : ∃ a b, gateSig (n := n) gs g = fun x => bank gs a x || bank gs b x := by
        cases he : g.inputs with
        | nil => exact ⟨n+gs.length,n+gs.length,by funext x; simp [gateSig,hop,he,GateOp.eval,bdead]⟩
        | cons a t =>
          cases t with
          | nil => exact ⟨a,a,by funext x; simp [gateSig,hop,he,GateOp.eval]⟩
          | cons b t =>
            have ht : t = [] := by simpa [he] using hl
            subst t
            exact ⟨a,b,by funext x; simp [gateSig,hop,he,GateOp.eval]⟩
      rw [he]
      refine ⟨or_step hh ih four hk,mono_new im ?_⟩
      intro x y hxy h
      exact Bool.or_eq_true_iff.mpr ((Bool.or_eq_true_iff.mp h).imp (im a x y hxy) (im b x y hxy))
end PEqualNP.Outside.L_meta_2656

open PEqualNP.Outside.L_meta_2656 in
theorem PEqualNP.Outside.L_meta_2656 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), (∃ (x4 : Fin x1) (x5 : Fin x1), x2.Adj x4 x5) → (∀ (x5 x6 x7 x8 : Fin x1), x5 ≠ x6 → x5 ≠ x7 → x5 ≠ x8 → x6 ≠ x7 → x6 ≠ x8 → x7 ≠ x8 → x2.Adj x5 x6 → x2.Adj x6 x7 → x2.Adj x7 x8 → ¬x2.Adj x8 x5) → PEqualNP.MetaComplexity.Monotone2 x3 → (∀ (x7 : Fin x1 → Bool), x3.eval (List.ofFn x7) = Bool.true ↔ ∃ (x8 : Fin x1) (x9 : Fin x1), x2.Adj x8 x9 ∧ x7 x8 = Bool.true ∧ x7 x9 = Bool.true) → (∀ (x8 : ℕ) (x9 : PEqualNP.CircuitLowerBounds.Gate), x3.gates[x8]? = Option.some x9 → x9.op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ (x12 : Fin x1 → Bool), (x3.wires (List.ofFn x12)).getD (x1 + x8) Bool.false = Bool.true → ∃ (x14 : Fin x1) (x15 : Fin x1), x2.Adj x14 x15 ∧ x12 x14 = Bool.true ∧ x12 x15 = Bool.true) → PEqualNP.BicliqueBlockCost.HasBlockCost x2 x3.size := by
  intro n G C hedge four mono computes safe
  classical
  have hb := (main_ind G four C.gates (by
    intro g hg
    exact mono g hg) (by
    intro pre g post he hop x hx
    have hgate : C.gates[pre.length]? = some g := by
      rw [he,List.getElem?_append_right (le_refl pre.length)]
      simp
    apply safe pre.length g hgate hop x
    change (wf C.gates (List.ofFn x)).getD (n+pre.length) false = true
    rw [he,show pre ++ g :: post = (pre ++ [g]) ++ post by simp]
    rw [wf_prefix _ _ _ _ (by simp)]
    change bank (pre ++ [g]) (n+pre.length) x = true
    simpa [bsnoc,New] using hx)).1
  let f : Sig n := bank C.gates C.output
  have good : Good G f := fun x => (computes x).mp
  apply finishCost
  have hh := hb ∅ {(none,C.output)} (by
    constructor
    · simpa [Valid] using safe_empty good
    · intro u v huv
      apply Or.inl
      refine ⟨_,Finset.mem_singleton_self _,(computes _).mpr ⟨u,v,huv,?_,?_⟩⟩ <;> simp [pairX])
  simpa [PEqualNP.CircuitLowerBounds.Circuit.size] using hh
