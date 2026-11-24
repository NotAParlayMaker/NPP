import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_4476_418
    (resources : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I],200 ≤ q → N=q^2+q+1 → (∀ l : Fin N,Fintype.card {p : Fin N // I p l}=q+1) → (∀ p r,p≠r → ∃! l,I p l ∧ I r l) →
      let m := N+N
      ∀ (s o : ℕ) (F : ℕ → Set (Finset ℕ)),o < m+s → (∀ i < m,F i={{i}}) → (∀ j < s,∃ a < m+j,∃ b < m+j,F (m+j)=Set.image2 (fun (x y : Finset ℕ) => x∪y) (F a) (F b) ∨ F (m+j)=F a ∨ F (m+j)={∅} ∨ F (m+j)=F a∪F b) →
      (∀ A∈F o,∀ p l,I p l → p.val∈A ∨ N+l.val∈A) → (∀ T : Finset (Fin N),T.card ≤ q → ∃ A∈F o,∀ p : Fin N,(p.val∈A ↔ ∃ l∈T,I p l) ∧ (N+p.val∈A ↔ p∉T)) → 2*q^2+7*q+1 ≤ s)
    (normalize : ∀ (m s o : ℕ) (F : ℕ → Set (Finset ℕ)) (X : Set (Finset ℕ)),o < m+s →
      (∀ i < m,F i={{i}}) → (∀ j < s,∃ a < m+j,∃ b < m+j,F (m+j)=Set.image2 (fun (x y : Finset ℕ) => x∪y) (F a) (F b) ∨ F (m+j)=F a ∨ F (m+j)={∅} ∨ F (m+j)=F a∪F b) →
      ∃ k ≤ s,∃ u < m+1+k,∃ W : ℕ → Set (Finset ℕ),(∀ i < m,W i={M∈X | i∈M}) ∧ W m=∅ ∧
      (∀ j < k,∃ a < m+1+j,∃ b < m+1+j,a<b ∧ (W (m+1+j)=W a∩W b ∨ W (m+1+j)=W a∪W b) ∧ ∀ i < m+1+j,W (m+1+j)≠W i) ∧ W u={M∈X | ∀ A∈F o,¬Disjoint M A})
    (reduced : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I],203 ≤ q → N=q^2+q+1 → (∀ l : Fin N,Fintype.card {p : Fin N // I p l}=q+1) → (∀ p r,p≠r → ∃! l,I p l ∧ I r l) →
      let m := N+N
      let positive : Set (Finset ℕ) := {M | ∃ p l : Fin N,I p l ∧ M={p.val,N+l.val}}
      let neg (T : Finset (Fin N)) := ((Finset.univ.filter (fun p : Fin N => ∀ l∈T,¬I p l)).image Fin.val) ∪ T.image (fun l => N+l.val)
      let X := positive ∪ {M | ∃ T : Finset (Fin N),T.card ≤ q ∧ M=neg T}
      ∀ (k u : ℕ) (W : ℕ → Set (Finset ℕ)),u < m+1+k → (∀ i < m,W i={M∈X | i∈M}) → W m=∅ →
      (∀ j < k,∃ a < m+1+j,∃ b < m+1+j,a<b ∧ (W (m+1+j)=W a∩W b ∨ W (m+1+j)=W a∪W b) ∧ ∀ i < m+1+j,W (m+1+j)≠W i) → W u=positive → N*q ≤ 100*k) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3], (200 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) → ∀ (x9 x10 : ℕ) (x11 : ℕ → Set (Finset ℕ)), x10 < x2 + x2 + x9 → (∀ x13 < x2 + x2, x11 x13 = {{x13}}) → (∀ x14 < x9, ∃ x16 < x2 + x2 + x14, ∃ x17 < x2 + x2 + x14, x11 (x2 + x2 + x14) = Set.image2 (fun (x18 x19 : Finset ℕ) => x18 ∪ x19) (x11 x16) (x11 x17) ∨ x11 (x2 + x2 + x14) = x11 x16 ∨ x11 (x2 + x2 + x14) = {∅} ∨ x11 (x2 + x2 + x14) = x11 x16 ∪ x11 x17) → (∃ x15 < x9, ∃ x16 < x2 + x2 + x15, ∃ x17 < x2 + x2 + x15, x11 (x2 + x2 + x15) = x11 x16 ∪ x11 x17 ∧ ∃ x18 ∈ x11 x16, ∃ x19 ∈ x11 x17, ¬Disjoint x18 x19) → (∀ x16 ∈ x11 x10, ∀ (x18 x19 : Fin x2), x3 x18 x19 → ↑x18 ∈ x16 ∨ x2 + ↑x19 ∈ x16) → (∀ (x17 : Finset (Fin x2)), x17.card ≤ x1 → ∃ x19 ∈ x11 x10, ∀ (x20 : Fin x2), (↑x20 ∈ x19 ↔ ∃ x21 ∈ x17, x3 x20 x21) ∧ (x2 + ↑x20 ∈ x19 ↔ x20 ∉ x17)) → x2 * x1 ≤ (100 : ℕ) * x9 := by
  classical
  intro q N I inst hq ord deg un s o F room inputs gates _ safe saturated
  by_cases lo : q≤202
  · have lower := resources q N I hq ord deg un s o F room inputs gates safe saturated
    interval_cases q <;> norm_num at ord lower ⊢ <;> omega
  · have large : 203 ≤ q := by omega
    let m := N+N
    let positive : Set (Finset ℕ) := {M | ∃ p l : Fin N,I p l ∧ M={p.val,N+l.val}}
    let neg (T : Finset (Fin N)) := ((Finset.univ.filter (fun p : Fin N => ∀ l∈T,¬I p l)).image Fin.val) ∪ T.image (fun l => N+l.val)
    let X := positive ∪ {M | ∃ T : Finset (Fin N),T.card ≤ q ∧ M=neg T}
    obtain ⟨k,le,u,hu,W,hb,hzero,steps,last⟩ := normalize m s o F X room inputs gates
    have plus (M) (hm : M∈positive) : ∀ A∈F o,¬Disjoint M A := by
      obtain ⟨p,l,inc,rfl⟩ := hm
      intro A ha dis
      rcases safe A ha p l inc with hp|hl
      · exact (Finset.disjoint_left.mp dis) (by simp) hp
      · exact (Finset.disjoint_left.mp dis) (by simp) hl
    have minus (T : Finset (Fin N)) (size : T.card ≤ q) : ∃ A∈F o,Disjoint (neg T) A := by
      obtain ⟨A,ha,sp⟩ := saturated T size
      refine ⟨A,ha,Finset.disjoint_left.mpr ?_⟩
      intro w hw inA
      rcases Finset.mem_union.mp hw with pt|ln
      · obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp pt
        obtain ⟨l,hl,inc⟩ := (sp p).1.mp inA
        exact (Finset.mem_filter.mp hp).2 l hl inc
      · obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp ln
        exact (sp l).2.mp inA hl
    have target : W u=positive := by
      rw [last]
      ext M
      constructor
      · rintro ⟨mx,all⟩
        rcases mx with pos|⟨T,sz,rfl⟩
        · exact pos
        · obtain ⟨A,ha,dis⟩ := minus T sz
          exact (all A ha dis).elim
      · exact fun pos => ⟨Or.inl pos,plus M pos⟩
    exact (reduced q N I large ord deg un k u W hu hb hzero steps target).trans (Nat.mul_le_mul_left _ le)
