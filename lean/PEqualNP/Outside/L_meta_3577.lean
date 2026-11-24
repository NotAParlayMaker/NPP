import PEqualNP.Defs
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Data.Nat.ModEq

namespace PEqualNP.Outside.L_meta_3577

abbrev q : ℕ := 7500
abbrev Point := Fin q × Fin (2*q^2)
abbrev Line := Fin q × Fin (q^2)
abbrev V := Point ⊕ Line
abbrev J := Bool ⊕ ((i : Fin 19) × Fin (i.val+1) × Fin (i.val+1))

def valAt (l : Line) (x : Fin q) : ℕ := l.1.val*x.val + l.2.val

lemma valAt_lt (l : Line) (x : Fin q) : valAt l x < 2*q^2 := by
  have h := Nat.mul_le_mul (Nat.le_of_lt l.1.isLt) (Nat.le_of_lt x.isLt)
  have b := l.2.isLt
  dsimp [valAt, q] at *
  omega

def incident (p : Point) (l : Line) : Prop := p.2.val = valAt l p.1

lemma rectangle (p r : Point) (l t : Line)
    (h₁ : incident p l) (h₂ : incident r l) (h₃ : incident r t) (h₄ : incident p t) :
    p = r ∨ l = t := by
  obtain ⟨x,y⟩ := p
  obtain ⟨z,w⟩ := r
  obtain ⟨a,b⟩ := l
  obtain ⟨c,d⟩ := t
  simp only [incident, valAt] at *
  by_cases hx : x = z
  · subst z
    exact Or.inl (Prod.ext rfl (Fin.ext (h₁.trans h₂.symm)))
  · right
    have h : ((a.val : ℤ) - c.val) * ((x.val : ℤ) - z.val) = 0 := by
      have h₅ : (a.val : ℤ)*x.val + b.val = c.val*x.val + d.val := by exact_mod_cast h₁.symm.trans h₄
      have h₆ : (a.val : ℤ)*z.val + b.val = c.val*z.val + d.val := by exact_mod_cast h₂.symm.trans h₃
      linear_combination h₅ - h₆
    rcases mul_eq_zero.mp h with ha | hz
    · have he : a = c := by apply Fin.ext; exact_mod_cast sub_eq_zero.mp ha
      subst c
      exact Prod.ext rfl (Fin.ext (by change b.val = d.val; omega))
    · exact (hx (Fin.ext (by exact_mod_cast sub_eq_zero.mp hz))).elim

def rel : V → V → Prop
  | .inl p, .inr l => incident p l
  | .inr l, .inl p => incident p l
  | _, _ => False

lemma rel_symm (a b : V) : rel a b → rel b a := by cases a <;> cases b <;> exact id

lemma square (a b c d : V) (hac : a ≠ c) (hbd : b ≠ d) :
    ¬ (rel a b ∧ rel b c ∧ rel c d ∧ rel d a) := by
  rintro ⟨h₁,h₂,h₃,h₄⟩
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all only [rel]
  · rcases rectangle _ _ _ _ h₁ h₂ h₃ h₄ with h | h <;> subst_vars <;> contradiction
  · rcases rectangle _ _ _ _ h₁ h₄ h₃ h₂ with h | h <;> subst_vars <;> contradiction

def modulus (i : Fin 19) := i.val+1

lemma modular_detect {u v : ℕ} (hu : u < 2*q^2) (hv : v < 2*q^2) (hne : u ≠ v) :
    ∃ i : Fin 19, u % modulus i ≠ v % modulus i := by
  by_contra! h
  have aux (s t : ℕ) (hst : s < t) (ht : t < 2*q^2)
      (he : ∀ i : Fin 19, s % modulus i = t % modulus i) : False := by
    let M := (Finset.range 19).lcm (fun j : ℕ => j+1)
    have hm : 2*q^2 ≤ M := by decide +kernel
    have hd : M ∣ t-s := by
      apply Finset.lcm_dvd
      intro j hj
      exact (Nat.modEq_iff_dvd' hst.le).mp (he ⟨j,Finset.mem_range.mp hj⟩)
    have := Nat.le_of_dvd (by omega : 0 < t-s) hd
    omega
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact aux u v hlt hv h
  · exact aux v u hgt hu (fun i => (h i).symm)

def belongs : J → V → Prop
  | .inl false, .inl _ => True
  | .inl true, .inr _ => True
  | .inr ⟨i,A,B⟩, .inl p => p.2.val % modulus i ≠ (A.val * p.1.val + B.val) % modulus i
  | .inr ⟨i,A,B⟩, .inr l => l.1.val % modulus i = A.val ∧ l.2.val % modulus i = B.val
  | _, _ => False

lemma residue (l : Line) (x : Fin q) (i : Fin 19) (A B : Fin (modulus i))
    (ha : l.1.val % modulus i = A.val) (hb : l.2.val % modulus i = B.val) :
    valAt l x % modulus i = (A.val*x.val+B.val)%modulus i := by
  exact ((Nat.mod_modEq _ _).symm.mul (Nat.ModEq.refl x.val) |>.add (Nat.mod_modEq _ _).symm :
    valAt l x ≡ _ [MOD modulus i]) |>.trans (by rw [ha,hb])

lemma independent (j : J) (p : Point) (l : Line) (hp : belongs j (.inl p)) (hl : belongs j (.inr l)) :
    ¬ incident p l := by
  rcases j with b | ⟨i,A,B⟩
  · cases b <;> contradiction
  · intro h
    exact hp ((congrArg (· % modulus i) h).trans (residue l p.1 i A B hl.1 hl.2))

lemma cross (p : Point) (l : Line) (h : ¬ incident p l) :
    ∃ j : J, belongs j (.inl p) ∧ belongs j (.inr l) := by
  obtain ⟨i,hi⟩ := modular_detect p.2.isLt (valAt_lt l p.1) h
  let A : Fin (modulus i) := ⟨_, Nat.mod_lt l.1.val (Nat.succ_pos _)⟩
  let B : Fin (modulus i) := ⟨_, Nat.mod_lt l.2.val (Nat.succ_pos _)⟩
  exact ⟨.inr ⟨i,A,B⟩,fun he => hi (he.trans (residue l p.1 i A B rfl rfl).symm),rfl,rfl⟩

lemma two_out (j : J) : ∃ u v : V, u ≠ v ∧ ¬ belongs j u ∧ ¬ belongs j v := by
  rcases j with b | ⟨i,A,B⟩
  · cases b
    · exact ⟨.inr (0,0), .inr (0,1), by decide, id, id⟩
    · exact ⟨.inl (0,0), .inl (0,1), by decide, id, id⟩
  · have hi := i.isLt
    have hB := B.isLt
    let p : Point := (0, ⟨B.val, by dsimp [q]; omega⟩)
    let r : Point := (0, ⟨B.val+modulus i, by dsimp [q,modulus]; omega⟩)
    refine ⟨.inl p, .inl r, ?_, ?_, ?_⟩
    · intro he
      have hh := congrArg (fun s : Point => s.2.val) (Sum.inl.inj he)
      dsimp [p,r,modulus] at hh
      omega
    · simp [belongs,p]
    · simp [belongs,r]

noncomputable def code := Fintype.equivFin V
noncomputable def key := Fintype.equivFin J
abbrev N := Fintype.card V
abbrev K := Fintype.card J

lemma block_count : K = 2472 := by
  simp only [K,J,Fintype.card_sum,Fintype.card_bool,Fintype.card_sigma,Fintype.card_prod,Fintype.card_fin]
  decide +kernel

noncomputable def graph : SimpleGraph (Fin N) where
  Adj a b := rel (code.symm a) (code.symm b)
  symm := ⟨fun _ _ => rel_symm _ _⟩
  loopless := ⟨fun a => by cases code.symm a <;> exact id⟩

noncomputable def block (j : Fin K) : Finset (Fin N) := by
  classical
  exact Finset.univ.filter (fun v => belongs (key.symm j) (code.symm v))

lemma mem_block (j : Fin K) (v : Fin N) : v ∈ block j ↔ belongs (key.symm j) (code.symm v) := by
  classical
  simp [block]

def onLine (l : Line) (x : Fin q) : Point := (x,⟨valAt l x, valAt_lt l x⟩)

noncomputable def edge (e : Line × Fin q) : Sym2 (Fin N) :=
  s(code (.inl (onLine e.1 e.2)), code (.inr e.1))

lemma edge_injective : Function.Injective edge := by
  rintro ⟨l,x⟩ ⟨t,y⟩ h
  rcases Sym2.eq_iff.mp h with ⟨hp,hl⟩ | ⟨hp,_⟩
  · have hl' := Sum.inr.inj (code.injective hl)
    have hp' := Sum.inl.inj (code.injective hp)
    exact Prod.ext hl' (congrArg Prod.fst hp')
  · have hh := code.injective hp
    cases hh

lemma edge_count [DecidableRel graph.Adj] : q^4 ≤ graph.edgeFinset.card := by
  have h := Finset.card_le_card_of_injOn (s := Finset.univ) (t := graph.edgeFinset) edge (by
    intro e _
    change edge e ∈ graph.edgeFinset
    rw [SimpleGraph.mem_edgeFinset]
    change rel (code.symm (code (.inl (onLine e.1 e.2)))) (code.symm (code (.inr e.1)))
    simp only [Equiv.symm_apply_apply]
    rfl) edge_injective.injOn
  simpa [Line,q] using h

lemma size_block (j : Fin K) : (block j).card + 2 ≤ N := by
  classical
  obtain ⟨a,b,hab,ha,hb⟩ := two_out (key.symm j)
  let outside := Finset.univ \ block j
  have h (z : V) (hz : ¬ belongs (key.symm j) z) : code z ∈ outside := by
    simpa [outside,mem_block] using hz
  have hs : {code a, code b} ⊆ outside := Finset.insert_subset (h a ha) (Finset.singleton_subset_iff.mpr (h b hb))
  have hc := Finset.card_le_card hs
  have hne : code a ≠ code b := fun he => hab (code.injective he)
  have hp : ({code a, code b} : Finset (Fin N)).card = 2 := Finset.card_pair hne
  have hc' := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (block j))
  change outside.card + (block j).card = _ at hc'
  rw [Finset.card_univ, Fintype.card_fin] at hc'
  omega

lemma find_block (a b : Fin N) (h : ¬ graph.Adj a b) : ∃ j, a ∈ block j ∧ b ∈ block j := by
  change ¬ rel (code.symm a) (code.symm b) at h
  suffices hh : ∃ j : J, belongs j (code.symm a) ∧ belongs j (code.symm b) by
    obtain ⟨j,h₁,h₂⟩ := hh
    exact ⟨key j, (mem_block _ _).mpr (by simpa using h₁), (mem_block _ _).mpr (by simpa using h₂)⟩
  cases ea : code.symm a with
  | inl p =>
    cases eb : code.symm b with
    | inl r => exact ⟨.inl false, trivial, trivial⟩
    | inr l => exact cross p l (by simpa [ea,eb,rel] using h)
  | inr l =>
    cases eb : code.symm b with
    | inl p =>
      obtain ⟨j,hp,hl⟩ := cross p l (by simpa [ea,eb,rel] using h)
      exact ⟨j,hl,hp⟩
    | inr t => exact ⟨.inl true, trivial,trivial⟩

lemma inside_outside (v : Fin N) : (∃ j, v ∈ block j) ∧ (∃ j, v ∉ block j) := by
  cases e : code.symm v with
  | inl p =>
    refine ⟨⟨key (.inl false), ?_⟩, ⟨key (.inl true), ?_⟩⟩ <;> simp [mem_block,e,belongs]
  | inr l =>
    refine ⟨⟨key (.inl true), ?_⟩, ⟨key (.inl false), ?_⟩⟩ <;> simp [mem_block,e,belongs]

lemma block_independent (j : Fin K) (a b : Fin N) (ha : a ∈ block j) (hb : b ∈ block j) :
    ¬ graph.Adj a b := by
  replace ha := (mem_block _ _).mp ha
  replace hb := (mem_block _ _).mp hb
  change ¬ rel (code.symm a) (code.symm b)
  cases e : code.symm a <;> cases f : code.symm b <;> simp only [e,f] at ha hb <;>
    first | exact id | exact independent _ _ _ ha hb | exact independent _ _ _ hb ha

end PEqualNP.Outside.L_meta_3577

open PEqualNP.Outside.L_meta_3577

theorem PEqualNP.Outside.L_meta_3577 : ¬ (∀ (n k : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (side : Fin n → Bool) (I : Fin k → Finset (Fin n)), (∀ a b : Fin n, G.Adj a b → side a ≠ side b) → (∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) → 2 ≤ k → (∀ j : Fin k, ∀ a ∈ I j, ∀ b ∈ I j, ¬ G.Adj a b) → (∀ v : Fin n, ∃ j : Fin k, v ∈ I j) → (∀ v : Fin n, ∃ j : Fin k, v ∉ I j) → (∀ j : Fin k, (I j).card + 2 ≤ n) → (∀ a b : Fin n, a ≠ b → ¬ G.Adj a b → ∃ j : Fin k, a ∈ I j ∧ b ∈ I j) → ∃ T : Finset (Fin n), (∀ a b : Fin n, G.Adj a b → a ∈ T ∨ b ∈ T) ∧ G.edgeFinset.card + T.card + 1 ≤ ∑ j : Fin k, (n - (I j).card)) := by
  classical
  intro claim
  obtain ⟨T,_,h⟩ := claim N K graph (fun v => (code.symm v).isRight) block (by
    intro a b
    change rel (code.symm a) (code.symm b) → _
    cases code.symm a <;> cases code.symm b <;> simp [rel])
    (fun a b c d hac hbd => square _ _ _ _ (fun h => hac (code.symm.injective h))
      (fun h => hbd (code.symm.injective h)))
    (by rw [block_count]; decide) (fun j a ha b hb => block_independent j a b ha hb)
    (fun v => (inside_outside v).1) (fun v => (inside_outside v).2) size_block
    (fun a b _ => find_block a b)
  have upper : (∑ j : Fin K, (N - (block j).card)) ≤ K*N := by
    calc
      _ ≤ ∑ _j : Fin K, N := Finset.sum_le_sum (fun _ _ => Nat.sub_le _ _)
      _ = _ := by simp
  have gap : K*N < q^4 := by rw [block_count]; norm_num [N,V,Point,Line,q]
  have lower := edge_count
  omega
