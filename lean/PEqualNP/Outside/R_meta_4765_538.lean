import Mathlib
import PEqualNP.Defs

-- Remove a line at infinity and the points on it. The remaining directions
-- form q+1 orthogonal coordinates, not a presumed field coordinatization.
-- Each pair of deleted essential inputs pays for at least one removed gate.
set_option maxRecDepth 4096 in
set_option maxHeartbeats 2500000 in
theorem PEqualNP.Outside.R_meta_4765_538
    (bounded : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I], 100 < q → q ≤ 289 → N=q^2+q+1 →
      (∀ l, Fintype.card {p : Fin N // I p l}=q+1) → (∀ p r : Fin N, p≠r → ∃! l, I p l ∧ I r l) →
      ∀ (s o : ℕ) (W : ℕ → Set ((Fin N → Bool) × (Fin N → Bool))), let m := N+N
      o < m+s → (∀ p : Fin N, W p.val={z | z.1 p=true} ∧ W (N+p.val)={z | z.2 p=true}) →
      (∀ j < s, ∃ a b, max a b < m+j ∧ W (m+j) ∈ [W a ∪ W b,W a,∅,W a ∩ W b]) →
      (∀ z, Fintype.card {l : Fin N // z.2 l=true} ≤ q → (z∈W o ↔ ∃ p l, I p l ∧ z.1 p=true ∧ z.2 l=true)) → N*q≤100*s)
    (chart : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I], 2 ≤ q → N=q^2+q+1 →
      (∀ l, Fintype.card {p : Fin N // I p l}=q+1) → (∀ p r : Fin N, p≠r → ∃! l, I p l ∧ I r l) →
      ∃ (P : Fin (q^2) ↪ Fin N) (L : (Fin (q+1) × Fin q) ↪ Fin N) (C : Fin (q^2) → Fin (q+1) → Fin q),
      (∀ x d k, I (P x) (L (d,k)) ↔ C x d=k) ∧ ∀ d e, d≠e → Function.Bijective (fun x => (C x d,C x e)))
    (trim : ∀ (α β : Type) (m s o : ℕ) (W : ℕ → Set α) (f : β → α) (E : Finset ℕ), o < m+s →
      (∀ j < s, ∃ a b, max a b < m+j ∧ W (m+j) ∈ [W a ∪ W b,W a,∅,W a ∩ W b]) →
      (∀ i ∈ E, i < m ∧ f ⁻¹' W i = ∅ ∧ ∃ z∈W o, ∃ y∉W o, ∀ k < m, k≠i → (z∈W k ↔ y∈W k)) →
      ∃ (t v : ℕ) (U : ℕ → Set β), 2*t+E.card ≤ 2*s+1 ∧ v < m+t ∧ U v=f ⁻¹' W o ∧
        (∀ i < m, U i=f ⁻¹' W i) ∧ ∀ j < t, ∃ a b, max a b < m+j ∧ U (m+j) ∈ [U a ∪ U b,U a,∅,U a ∩ U b])
    (affine : ∀ (q : ℕ), 290 ≤ q → ∀ C : Fin (q^2) → Fin (q+1) → Fin q,
      (∀ d e, d≠e → Function.Bijective (fun x => (C x d,C x e))) →
      ∀ (m s o : ℕ) (U : ℕ → Set (Finset (Fin (q^2)) × Finset (Fin (q+1) × Fin q))), o < m+s →
      (∀ i < m, U i=∅ ∨ (∃ p, U i={z | p∈z.1}) ∨ ∃ l, U i={z | l∈z.2}) →
      (∀ j < s, ∃ a b, max a b < m+j ∧ U (m+j) ∈ [U a ∪ U b,U a,∅,U a ∩ U b]) →
      (∀ z, z.2.card ≤ q → (z∈U o ↔ ∃ p∈z.1, ∃ d, (d,C p d)∈z.2)) → q^2*(q+1) ≤ 100*s) :
∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3],   (100 : ℕ) < x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) →         (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) →           (∀ (x9 : Finset (Fin x2)), ∀ x10 ∈ x9, x1 + (2 : ℕ) ≤ x9.card + Fintype.card { x12 : Fin x2 // x3 x12 x10 ∧ ∀ x13 ∈ x9.erase x10, ¬x3 x12 x13 }) →             ∀ (x10 x11 : ℕ) (x12 : ℕ → Set ((Fin x2 → Bool) × (Fin x2 → Bool))),               have x13 : ℕ := x2 + x2;               have x14 : Fin x2 → Fin x2 → Bool := fun (x14 x15 : Fin x2) => Decidable.decide (x15 = x14);               have x15 : Bool → ℕ → Set (Fin x2) := fun (x15 : Bool) (x16 : ℕ) => {x17 : Fin x2 | (if x15 = Bool.true then (x14 x17, fun (x18 : Fin x2) => Bool.false) else (fun (x18 : Fin x2) => Bool.false, x14 x17)) ∈ x12 x16};               x11 < x13 + x10 → (∀ (x17 : Fin x2), x12 ↑x17 = {x18 : (Fin x2 → Bool) × (Fin x2 → Bool) | x18.1 x17 = Bool.true} ∧ x12 (x2 + ↑x17) = {x18 : (Fin x2 → Bool) × (Fin x2 → Bool) | x18.2 x17 = Bool.true}) → (∀ x18 < x10, ∃ (x20 : ℕ) (x21 : ℕ), Max.max x20 x21 < x13 + x18 ∧ x12 (x13 + x18) ∈ [x12 x20 ∪ x12 x21, x12 x20, ∅, x12 x20 ∩ x12 x21]) → (∀ (x19 : (Fin x2 → Bool) × (Fin x2 → Bool)), Fintype.card { x20 : Fin x2 // x19.2 x20 = Bool.true } ≤ x1 → (x19 ∈ x12 x11 ↔ ∃ (x21 : Fin x2) (x22 : Fin x2), x3 x21 x22 ∧ x19.1 x21 = Bool.true ∧ x19.2 x22 = Bool.true)) → (∃ x20 < x10, ∃ (x21 : Bool) (x22 : Fin x2) (x23 : Fin x2), x22 ≠ x23 ∧ x22 ∈ x15 x21 (x13 + x20) ∧ x23 ∈ x15 x21 (x13 + x20) ∧ ¬∃ x24 < x13 + x20, ∃ x25 < x13 + x20, x15 x21 (x13 + x20) = x15 x21 x24 ∪ x15 x21 x25) → x2 * x1 ≤ (100 : ℕ) * x10 := by
  classical
  intro q N I decI lo order degree join priv s o W m atom axis room raw gate good anomaly
  by_cases small : q≤289
  · exact bounded q N I lo small order degree join s o W room raw gate good
  obtain ⟨P,L,C,inc,orth⟩ := chart q N I (by omega) order degree join
  let B := Finset (Fin (q^2)) × Finset (Fin (q+1) × Fin q)
  let f (z : B) : (Fin N → Bool) × (Fin N → Bool) :=
    (fun p => decide (p ∈ z.1.map P),fun l => decide (l ∈ z.2.map L))
  let absent := (Finset.univ.map P)ᶜ
  let E := absent.map Fin.valEmbedding
  have es : E.card=q+1 := by simp only [E,absent,Finset.card_map,Finset.card_compl,Finset.card_univ,Fintype.card_fin]; omega
  have smallOne (l : Fin N) : Fintype.card {i : Fin N // atom l i=true} ≤ q := by simpa [atom] using (by omega : 1≤q)
  have cut (i : ℕ) (hi : i∈E) : i < m ∧ f ⁻¹' W i = ∅ ∧ ∃ z∈W o, ∃ y∉W o, ∀ k < m, k≠i → (z∈W k ↔ y∈W k) := by
    obtain ⟨p,hp,rfl⟩ := Finset.mem_map.mp hi
    change p.val < m ∧ _
    have no : ∀ z : B, p ∉ z.1.map P := by
      intro z hin
      exact Finset.mem_compl.mp hp (Finset.map_subset_map.mpr (Finset.subset_univ _) hin)
    refine ⟨by dsimp [m]; omega,?_,?_⟩
    · change f ⁻¹' W p.val=∅
      rw [(raw p).1]; ext z; exact (by simpa only [Set.mem_preimage,Set.mem_setOf_eq,f,decide_eq_true_eq,Set.mem_empty_iff_false,iff_false] using no z)
    · have hn : 1<N := by omega
      letI : Nontrivial (Fin N) := Fin.nontrivial_iff_two_le.mpr (by omega)
      obtain ⟨r,ne⟩ := exists_ne p
      obtain ⟨l,pl,_⟩ := join p r (Ne.symm ne)
      let z := (atom p,atom l)
      let y := ((fun _ : Fin N => false),atom l)
      have yes : z∈W o := (good z (smallOne l)).mpr ⟨p,l,pl.1,by simp [z,atom],by simp [z,atom]⟩
      have noY : y∉W o := by intro h; obtain ⟨u,v,_,bad,_⟩ := (good y (smallOne l)).mp h; exact Bool.noConfusion bad
      refine ⟨z,yes,y,noY,?_⟩
      intro k hk nk
      by_cases pt : k<N
      · let t : Fin N := ⟨k,pt⟩
        have diff : t≠p := fun e => nk (congrArg Fin.val e)
        change z∈W t.val ↔ y∈W t.val
        rw [(raw t).1]; simp [z,y,atom,diff]
      · let t : Fin N := ⟨k-N,by dsimp [m] at hk; omega⟩
        have ek : k=N+t.val := by dsimp [t]; omega
        rw [ek,(raw t).2]; rfl
  obtain ⟨t,v,U,cost,vr,out,inputs,ops⟩ := trim _ B m s o W f E room gate cut
  have coords (i : ℕ) (h : i < m) : U i=∅ ∨ (∃ p, U i={z : B | p∈z.1}) ∨ ∃ l, U i={z : B | l∈z.2} := by
    rw [inputs i h]
    by_cases pt : i<N
    · let p : Fin N := ⟨i,pt⟩
      change f ⁻¹' W p.val=∅ ∨ (∃ x, f ⁻¹' W p.val={z : B | x∈z.1}) ∨ ∃ l, f ⁻¹' W p.val={z : B | l∈z.2}
      rw [(raw p).1]
      by_cases ex : ∃ x, P x=p
      · obtain ⟨x,e⟩ := ex; right; left; refine ⟨x,?_⟩; ext z; simp [f,←e]
      · left; ext z; simp [f,Finset.mem_map]; grind
    · let l : Fin N := ⟨i-N,by dsimp [m] at h; omega⟩
      have ei : i=N+l.val := by dsimp [l]; omega
      rw [ei,(raw l).2]
      by_cases ex : ∃ a, L a=l
      · obtain ⟨⟨d,k⟩,e⟩ := ex; right; right; refine ⟨(d,k),?_⟩; ext z; simp [f,←e]
      · left; ext z; simp [f,Finset.mem_map]; grind
  have answer (z : B) (sz : z.2.card≤q) : z∈U v ↔ ∃ p∈z.1, ∃ d, (d,C p d)∈z.2 := by
    rw [out]; change f z∈W o ↔ _
    have num : Fintype.card {l : Fin N // (f z).2 l=true} ≤ q := by
      change Fintype.card {l : Fin N // decide (l∈z.2.map L)=true} ≤ q
      simpa only [decide_eq_true_eq,Fintype.card_subtype,Finset.filter_mem_eq_inter,Finset.univ_inter,Finset.card_map] using sz
    rw [good (f z) num]
    constructor
    · rintro ⟨p,l,flag,hp,hl⟩
      obtain ⟨x,hx,e⟩ := Finset.mem_map.mp (of_decide_eq_true hp)
      obtain ⟨⟨d,k⟩,hk,e'⟩ := Finset.mem_map.mp (of_decide_eq_true hl)
      have val := (inc x d k).mp (e ▸ e' ▸ flag)
      exact ⟨x,hx,d,val ▸ hk⟩
    · rintro ⟨x,hx,d,hd⟩
      exact ⟨P x,L (d,C x d),(inc ..).mpr rfl,decide_eq_true (Finset.mem_map.mpr ⟨x,hx,rfl⟩),decide_eq_true (Finset.mem_map.mpr ⟨_,hd,rfl⟩)⟩
  have lower := affine q (by omega) C orth m t v U vr coords ops answer
  rw [es] at cost
  rw [order]; nlinarith
