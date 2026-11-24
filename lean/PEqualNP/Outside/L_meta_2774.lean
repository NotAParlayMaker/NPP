import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2774

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover


open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wiresFrom (gs ++ [g]) w = wiresFrom gs w ++
      [g.op.eval (g.inputs.map fun i => (wiresFrom gs w).getD i false)] := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [wiresFrom]
  | append_singleton gs g ih => rw [wiresFrom_snoc, List.length_append, ih]; simp; omega

theorem wiresFrom_getD_lt (gs : List Gate) (g : Gate) (w : List Bool) (i : ℕ)
    (hi : i < (wiresFrom gs w).length) :
    (wiresFrom (gs ++ [g]) w).getD i false = (wiresFrom gs w).getD i false := by
  rw [wiresFrom_snoc, List.getD_append _ _ _ _ hi]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

/-- One step of compression: `st = (M, D)` with `M` the new index of every old wire so far and
`D` the new gates. A kept gate is emitted with remapped inputs; a dropped gate is not. -/
def cstep (n : ℕ) (keep : ℕ → Bool) (st : List ℕ × List Gate) (g : Gate) : List ℕ × List Gate :=
  if keep (st.1.length - n) then
    (st.1 ++ [n + st.2.length], st.2 ++ [⟨g.op, g.inputs.map fun i => st.1.getD i 0⟩])
  else (st.1 ++ [0], st.2)

def comp (n : ℕ) (keep : ℕ → Bool) (gs : List Gate) (st : List ℕ × List Gate) :
    List ℕ × List Gate := gs.foldl (cstep n keep) st

theorem comp_snoc (n : ℕ) (keep : ℕ → Bool) (gs : List Gate) (g : Gate) (st : List ℕ × List Gate) :
    comp n keep (gs ++ [g]) st = cstep n keep (comp n keep gs st) g := by
  simp [comp, List.foldl_append]

theorem comp_len (n : ℕ) (keep : ℕ → Bool) (gs : List Gate) (st : List ℕ × List Gate) :
    (comp n keep gs st).1.length = st.1.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [comp]
  | append_singleton gs g ih =>
    rw [comp_snoc]; unfold cstep; split_ifs <;> simp [ih] <;> omega

/-- A wire is good if it is an input or a kept gate. -/
def Good (n : ℕ) (keep : ℕ → Bool) (i : ℕ) : Prop := i < n ∨ keep (i - n) = true

/-- The invariant after processing the first `gs`: lengths, and every good old wire is found at
its new index with the same value, the new index lying among the new wires. -/
def CInv (n : ℕ) (keep : ℕ → Bool) (y : List Bool) (gs : List Gate) : Prop :=
  (comp n keep gs ((List.range n), [])).1.length = n + gs.length ∧
  ∀ i < n + gs.length, Good n keep i →
    (comp n keep gs ((List.range n), [])).1.getD i 0 < n + (comp n keep gs ((List.range n), [])).2.length ∧
    (wiresFrom (comp n keep gs ((List.range n), [])).2 y).getD
        ((comp n keep gs ((List.range n), [])).1.getD i 0) false = (wiresFrom gs y).getD i false

theorem cinv (n : ℕ) (keep : ℕ → Bool) (y : List Bool) (hy : y.length = n) :
    ∀ gs : List Gate, (∀ j < gs.length, keep j = true → ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs,
      i < n + j ∧ Good n keep i) → CInv n keep y gs := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil =>
    intro _
    refine ⟨by simp [comp], ?_⟩
    intro i hi _
    simp only [List.length_nil, Nat.add_zero] at hi
    simp only [comp, List.foldl_nil, List.length_nil, Nat.add_zero]
    rw [List.getD_eq_getElem _ _ (by simpa using hi)]
    simp only [List.getElem_range]
    refine ⟨hi, ?_⟩
    simp [wiresFrom]
  | append_singleton gs g ih =>
    intro hcl
    have hcl' : ∀ j < gs.length, keep j = true → ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs,
        i < n + j ∧ Good n keep i := by
      intro j hj hk i hi
      apply hcl j (by simp; omega) hk i
      rwa [List.getD_append _ _ _ _ hj]
    obtain ⟨hlen, hval⟩ := ih hcl'
    set st := comp n keep gs ((List.range n), []) with hst
    have hwl : (wiresFrom gs y).length = n + gs.length := by rw [wiresFrom_length, hy]
    have hdl : (wiresFrom st.2 y).length = n + st.2.length := by rw [wiresFrom_length, hy]
    rw [CInv, comp_snoc, ← hst]
    unfold cstep
    rw [hlen, show n + gs.length - n = gs.length by omega]
    by_cases hk : keep gs.length = true
    · rw [if_pos hk]
      refine ⟨by simp [hlen]; omega, ?_⟩
      intro i hi hg
      simp only [List.length_append, List.length_singleton] at hi ⊢
      by_cases hlt : i < n + gs.length
      · rw [List.getD_append _ _ _ _ (by rw [hlen]; exact hlt)]
        obtain ⟨h1, h2⟩ := hval i hlt hg
        refine ⟨by omega, ?_⟩
        rw [wiresFrom_getD_lt _ _ _ _ (by rw [hdl]; exact h1), h2,
          wiresFrom_getD_lt _ _ _ _ (by rw [hwl]; exact hlt)]
      · have hieq : i = n + gs.length := by omega
        subst hieq
        rw [List.getD_append_right _ _ _ _ (by rw [hlen]), hlen, Nat.sub_self, List.getD_cons_zero]
        refine ⟨by omega, ?_⟩
        rw [wiresFrom_snoc, List.getD_append_right _ _ _ _ (by rw [hdl]), hdl, Nat.sub_self,
          List.getD_cons_zero, wiresFrom_snoc, List.getD_append_right _ _ _ _ (by rw [hwl]), hwl,
          Nat.sub_self, List.getD_cons_zero]
        simp only [List.map_map]
        congr 1
        apply List.map_congr_left
        intro u hu
        have hgg : g = (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ := by simp
        obtain ⟨hu1, hu2⟩ := hcl gs.length (by simp) hk u (by rw [← hgg]; exact hu)
        exact (hval u hu1 hu2).2
    · rw [if_neg hk]
      refine ⟨by simp only [List.length_append, List.length_singleton, hlen]; omega, ?_⟩
      intro i hi hg
      simp only [List.length_append, List.length_singleton] at hi ⊢
      have hlt : i < n + gs.length := by
        by_contra hc
        have hieq : i = n + gs.length := by omega
        subst hieq
        rcases hg with h | h
        · omega
        · simp only [show n + gs.length - n = gs.length by omega] at h
          exact hk h
      rw [List.getD_append _ _ _ _ (by rw [hlen]; exact hlt)]
      obtain ⟨h1, h2⟩ := hval i hlt hg
      refine ⟨h1, ?_⟩
      rw [h2, wiresFrom_getD_lt _ _ _ _ (by rw [hwl]; exact hlt)]

theorem comp_snd_len (n : ℕ) (keep : ℕ → Bool) (gs : List Gate) :
    (comp n keep gs ((List.range n), [])).2.length =
      ((Finset.range gs.length).filter (fun j => keep j = true)).card := by
  induction gs using List.reverseRecOn with
  | nil => simp [comp]
  | append_singleton gs g ih =>
    rw [comp_snoc]
    have hl := comp_len n keep gs ((List.range n), [])
    simp only [List.length_range] at hl
    unfold cstep
    rw [hl, show n + gs.length - n = gs.length by omega, List.length_append, List.length_singleton,
      Finset.range_add_one, Finset.filter_insert]
    split_ifs with hk
    · simp [ih, Finset.card_insert_of_notMem]
    · simp [ih]

theorem comp_gates (n : ℕ) (keep : ℕ → Bool) (gs : List Gate) :
    ∀ g' ∈ (comp n keep gs ((List.range n), [])).2, ∃ g ∈ gs, g'.op = g.op ∧ g'.inputs.length = g.inputs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [comp]
  | append_singleton gs g ih =>
    intro g' hg'
    rw [comp_snoc] at hg'
    unfold cstep at hg'
    split_ifs at hg' with hk
    · rcases List.mem_append.mp hg' with h | h
      · obtain ⟨g0, hg0, e⟩ := ih g' h
        exact ⟨g0, List.mem_append_left _ hg0, e⟩
      · simp only [List.mem_singleton] at h
        subst h
        exact ⟨g, by simp, rfl, by simp⟩
    · obtain ⟨g0, hg0, e⟩ := ih g' hg'
      exact ⟨g0, List.mem_append_left _ hg0, e⟩

theorem comp_readsback (n : ℕ) (keep : ℕ → Bool) (y : List Bool) (hy : y.length = n) :
    ∀ gs : List Gate, (∀ j < gs.length, keep j = true → ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs,
      i < n + j ∧ Good n keep i) →
    ∀ k < (comp n keep gs ((List.range n), [])).2.length,
      ∀ u ∈ ((comp n keep gs ((List.range n), [])).2.getD k ⟨GateOp.or, []⟩).inputs, u < n + k := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil => intro _ k hk; simp [comp] at hk
  | append_singleton gs g ih =>
    intro hcl k hk u hu
    have hcl' : ∀ j < gs.length, keep j = true → ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs,
        i < n + j ∧ Good n keep i := by
      intro j hj hkj i hi
      apply hcl j (by simp; omega) hkj i
      rwa [List.getD_append _ _ _ _ hj]
    have hinv := cinv n keep y hy gs hcl'
    set st := comp n keep gs ((List.range n), []) with hst
    have hlen := hinv.1
    rw [comp_snoc, ← hst] at hk hu
    unfold cstep at hk hu
    rw [hlen, show n + gs.length - n = gs.length by omega] at hk hu
    split_ifs at hk hu with hkk
    · simp only [List.length_append, List.length_singleton] at hk
      by_cases hlt : k < st.2.length
      · rw [List.getD_append _ _ _ _ hlt] at hu
        exact ih hcl' k hlt u hu
      · have hk' : k = st.2.length := by omega
        subst hk'
        rw [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero] at hu
        simp only [List.mem_map] at hu
        obtain ⟨i, hi, rfl⟩ := hu
        have hgg : g = (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ := by simp
        obtain ⟨hi1, hi2⟩ := hcl gs.length (by simp) hkk i (by rw [← hgg]; exact hi)
        exact (hinv.2 i hi1 hi2).1
    · exact ih hcl' k hk u hu




theorem wiresFrom_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wiresFrom (g :: gs) w = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) :=
  rfl

theorem wiresFrom_append (gs hs : List Gate) (w : List Bool) :
    wiresFrom (gs ++ hs) w = wiresFrom hs (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  induction gs using List.reverseRecOn with
  | nil => rfl
  | append_singleton gs g ih =>
    rw [wiresFrom_snoc, List.getD_append _ _ _ _ (by rw [wiresFrom_length]; omega), ih]

/-- The OR chain: from accumulator wire `acc`, each listed wire is ORed in by a new gate. -/
def chain (acc idx : ℕ) : List ℕ → List Gate
  | [] => []
  | w :: ws => ⟨GateOp.or, [acc, w]⟩ :: chain idx (idx + 1) ws

def chainOut (acc idx : ℕ) : List ℕ → ℕ
  | [] => acc
  | _ :: ws => chainOut idx (idx + 1) ws

theorem chain_length (acc idx : ℕ) (ws : List ℕ) : (chain acc idx ws).length = ws.length := by
  induction ws generalizing acc idx with
  | nil => rfl
  | cons w ws ih => simp [chain, ih]

theorem chain_eval (ws : List ℕ) : ∀ (acc : ℕ) (V : List Bool), acc < V.length →
    (∀ w ∈ ws, w < V.length) →
    (wiresFrom (chain acc V.length ws) V).getD (chainOut acc V.length ws) false =
      (V.getD acc false || ws.any (fun w => V.getD w false)) := by
  induction ws with
  | nil => intro acc V hacc _; simp [chain, chainOut, wiresFrom]
  | cons w ws ih =>
    intro acc V hacc hws
    simp only [chain, chainOut, wiresFrom_cons]
    set V' := V ++ [GateOp.or.eval ([acc, w].map fun i => V.getD i false)] with hV'
    have hl : V'.length = V.length + 1 := by simp [hV']
    have h := ih V.length V' (by omega) (fun u hu => by have := hws u (by simp [hu]); omega)
    rw [show V.length + 1 = V'.length by omega, h]
    have e1 : V'.getD V.length false = (V.getD acc false || V.getD w false) := by
      rw [hV', List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero]
      simp [GateOp.eval]
    have e2 : ∀ u ∈ ws, V'.getD u false = V.getD u false := by
      intro u hu
      rw [hV', List.getD_append _ _ _ _ (hws u (by simp [hu]))]
    have e3 : ws.any (fun u => V'.getD u false) = ws.any (fun u => V.getD u false) := by
      rw [Bool.eq_iff_iff]
      simp only [List.any_eq_true]
      constructor
      · rintro ⟨u, hu, h⟩
        exact ⟨u, hu, by rw [← e2 u hu]; exact h⟩
      · rintro ⟨u, hu, h⟩
        exact ⟨u, hu, by rw [e2 u hu]; exact h⟩
    rw [e1, e3, List.any_cons]
    cases V.getD acc false <;> cases V.getD w false <;> simp


section Tree
variable {n : ℕ} {C : Circuit} {G L : Finset ℕ} {ρ : ℕ}


lemma pF (W:Finset ℕ) (b:List ℕ)
  (d:∀w∈b,w∈W):
  (∑w∈W,b.count w)=b.length:=by
 induction b with
 | nil=>simp
 | cons a b ih=>
   have e:a∈W:=d a (by simp);have ht:∀w∈b,w∈W:=fun w c=>d w (by simp[c])
   calc
    (∑w∈W,(a::b).count w)=
        (∑w∈W,b.count w)+∑w∈W,(if w=a then 1 else 0):=by
      rw[←Finset.sum_add_distrib];apply Finset.sum_congr rfl;intro w _;by_cases c:w=a
      ·subst w;simp
      ·simp[c,Ne.symm c]
    _=(a::b).length:=by rw[ih ht];simp[e]
lemma gN (h:IsOrTree n C G L ρ):G.card+1=L.card:=by
 rcases h with⟨q,hl,hr,a⟩
 by_cases m:G= ∅
 ·simp only[m,ite_true] at a;simp[m,a]
 ·let W:=L∪G.image (fun j=>n+j)
  have b:ρ∈W:=by rw[ite_eq_right m] at a;obtain⟨j,d,rfl⟩:=a;exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ d)
  have g:Disjoint L (G.image (fun j=>n+j)):=by refine Finset.disjoint_left.mpr ?_;intro w c r;obtain⟨j,d,rfl⟩:=Finset.mem_image.mp r;exact(hl _ c).1 ⟨Nat.le_add_right n j,by simpa using d⟩
  have f:W.card=L.card+G.card:=by
   exact(Finset.card_union_of_disjoint g).trans
    (congrArg (L.card+ ·) (Finset.card_image_of_injective _ (fun _ _ h=>Nat.add_left_cancel h)))
  have e:∀w∈W,readsIn C G w=if w=ρ then 0 else 1:=by
   intro w c;rcases Finset.mem_union.mp c with c|c
   ·exact(hl _ c).2
   ·obtain⟨j,d,rfl⟩:=Finset.mem_image.mp c;exact hr j d
  have l:(∑w∈W,readsIn C G w)+1=W.card:=by
   have s:readsIn C G ρ=0:=by simp[e ρ b]
   rw[←Finset.sum_erase_add _ _ b,s,add_zero];have hs:(∑w∈W.erase ρ,readsIn C G w)=(W.erase ρ).card:=by
    calc
     (∑w∈W.erase ρ,readsIn C G w)=∑v∈W.erase ρ,1:=by
       apply Finset.sum_congr rfl;intro w c;rw[e w (Finset.mem_of_mem_erase c),ite_eq_right (Finset.ne_of_mem_erase c)]
     _=(W.erase ρ).card:=by simp
   rw[hs];exact Finset.card_erase_add_one b
  have k:(∑w∈W,readsIn C G w)=G.card*2:=by
   unfold readsIn;rw[Finset.sum_comm]
   calc
    (∑j∈G,∑w∈W,(gateAt C j).inputs.count w)=∑u∈G,2:=by
      apply Finset.sum_congr rfl;intro j d;rw[pF,(q j d).2.1];intro i o;rcases (q j d).2.2 i o with o|⟨t,p⟩
      ·exact Finset.mem_union_left _ o
      ·exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i-n,p,by omega⟩)
    _=G.card*2:=by simp
  rw[k,f] at l;omega
lemma vO (b:IsOrTree n C G L ρ) {w:ℕ}
  (f:w∈L∨∃j∈G,w=n+j) (a:w≠ρ):
  ∃j∈G,w∈(gateAt C j).inputs:=by
 have g:readsIn C G w=1:=by
  rcases f with e|⟨j,c,rfl⟩
  ·simpa[a] using(b.2.1 w e).2
  ·simpa[a] using b.2.2.1 j c
 by_contra d
 push Not at d
 have h:readsIn C G w=0:=Finset.sum_eq_zero (fun j c=>List.count_eq_zero_of_not_mem (d j c));omega
lemma pI (p:IsOrTree n C G L ρ)
  (d:ReadsBack n C) (q:∀j∈G,j<C.gates.length)
  (P:ℕ→Prop)
  (e:∀j∈G,∀w∈(gateAt C j).inputs,P w→P (n+j))
  {i:ℕ} (r:i∈L∨∃j∈G,i=n+j) (k:P i):P ρ:=by
 classical
 let S:=(L∪G.image (fun j=>n+j)).filter P
 have a (w:ℕ):w∈S↔(w∈L∨∃j∈G,w=n+j)∧P w:=by simp only[S,Finset.mem_filter,Finset.mem_union,Finset.mem_image,eq_comm]
 have l:S.Nonempty:=⟨i,(a i).2 ⟨r,k⟩⟩
 let m:=S.max' l
 have s:m∈S:=S.max'_mem l;obtain⟨c,f⟩:=(a m).1 s;by_cases g:m=ρ
 ·simpa[g] using f
 ·obtain⟨j,h,b⟩:=vO p c g;have o:n+j∈S:=(a (n+j)).2
   ⟨Or.inr ⟨j,h,rfl⟩,e j h m b f⟩
  exact False.elim ((not_lt_of_ge (S.le_max' _ o)) (d j (q j h) m b))
lemma tV (o:IsOrTree n C G L ρ)
  (c:ReadsBack n C) (p:∀j∈G,j<C.gates.length)
  (P:ℕ→Prop)
  (m:∀j∈G,P (n+j)↔∃i∈(gateAt C j).inputs,P i):
  ∀j∈G,P (n+j)→∃i∈L,P i∧i≤n+j:=by
 intro j
 induction j using Nat.strong_induction_on with
 | ind j ih=>
   intro d f;obtain⟨i,a,e⟩:=(m j d).1 f;have l:=c j (p j d) i a;rcases (o.1 j d).2.2 i a with q|⟨s,k⟩
   ·exact⟨i,q,e,l.le⟩
   ·have h:n+(i-n)=i:=by omega
    have b:P (n+(i-n)):=by rwa [h]
    obtain⟨w,r,g,t⟩:=ih (i-n) (by omega) k b;exact⟨w,r,g,by omega⟩
lemma fI (c:IsOrTree n C G L ρ)
  (b:ReadsBack n C) (k:∀j∈G,j<C.gates.length)
  (P:ℕ→Prop)
  (f:∀j∈G,P (n+j)↔∃i∈(gateAt C j).inputs,P i):
  P ρ↔∃i∈L,P i:=by
 constructor
 ·intro l;by_cases a:G= ∅
  ·have o:L={ρ}:=by simpa[a] using c.2.2.2
   exact⟨ρ,by simp[o],l⟩
  ·have e:∃j∈G,ρ=n+j:=by simpa[a] using c.2.2.2
   obtain⟨j,h,rfl⟩:=e;obtain⟨i,g,d,_⟩:=tV c b k P f j h l;exact⟨i,g,d⟩
 ·rintro⟨i,g,d⟩;exact pI c b k P
   (fun j h w p m=>(f j h).2 ⟨w,p,m⟩) (Or.inl g) d

end Tree

theorem gate_val (gs : List Gate) (y : List Bool) (j : ℕ) (hj : j < gs.length)
    (hrb : ∀ u ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, u < y.length + j) :
    (wiresFrom gs y).getD (y.length + j) false = (gs.getD j ⟨GateOp.or, []⟩).op.eval
      ((gs.getD j ⟨GateOp.or, []⟩).inputs.map fun u => (wiresFrom gs y).getD u false) := by
  have hsplit : gs = gs.take j ++ [gs.getD j ⟨GateOp.or, []⟩] ++ gs.drop (j + 1) := by
    rw [List.getD_eq_getElem _ _ hj, List.append_assoc, List.singleton_append,
      ← List.drop_eq_getElem_cons hj, List.take_append_drop]
  have hlt : ∀ u, u < y.length + j + 1 → (wiresFrom gs y).getD u false =
      (wiresFrom (gs.take j ++ [gs.getD j ⟨GateOp.or, []⟩]) y).getD u false := by
    intro u hu
    conv_lhs => rw [hsplit]
    rw [wiresFrom_append, wiresFrom_prefix _ _ _ (by rw [wiresFrom_length]; simp <;> omega)]
  rw [hlt _ (by omega), wiresFrom_snoc, List.getD_append_right _ _ _ _
    (by rw [wiresFrom_length]; simp <;> omega)]
  have hl : (wiresFrom (gs.take j) y).length = y.length + j := by
    rw [wiresFrom_length, List.length_take, min_eq_left hj.le]
  rw [hl, Nat.sub_self, List.getD_cons_zero]
  congr 1
  apply List.map_congr_left
  intro u hu
  rw [hlt u (by have := hrb u hu; omega), wiresFrom_snoc,
    List.getD_append _ _ _ _ (by rw [hl]; exact hrb u hu)]

theorem chain_shape (ws : List ℕ) : ∀ (acc idx : ℕ), acc < idx → (∀ w ∈ ws, w < idx) →
    ∀ k < ws.length, ((chain acc idx ws).getD k ⟨GateOp.or, []⟩).op = GateOp.or ∧
      ((chain acc idx ws).getD k ⟨GateOp.or, []⟩).inputs.length = 2 ∧
      ∀ u ∈ ((chain acc idx ws).getD k ⟨GateOp.or, []⟩).inputs, u < idx + k := by
  induction ws with
  | nil => intro _ _ _ _ k hk; simp at hk
  | cons w ws ih =>
    intro acc idx hacc hws k hk
    cases k with
    | zero =>
      simp only [chain, List.getD_cons_zero]
      refine ⟨by simp, by simp, ?_⟩
      intro u hu
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl
      · omega
      · have := hws u (by simp); omega
    | succ k =>
      simp only [chain, List.getD_cons_succ]
      have h := ih idx (idx + 1) (by omega) (fun u hu => by have := hws u (by simp [hu]); omega) k
        (by simp at hk; omega)
      refine ⟨h.1, h.2.1, fun u hu => by have := h.2.2 u hu; omega⟩

theorem chain_mem (ws : List ℕ) : ∀ (acc idx : ℕ), ∀ g ∈ chain acc idx ws,
    g.op = GateOp.or ∧ g.inputs.length = 2 := by
  induction ws with
  | nil => intro _ _ g hg; simp [chain] at hg
  | cons w ws ih =>
    intro acc idx g hg
    simp only [chain, List.mem_cons] at hg
    rcases hg with rfl | hg
    · exact ⟨rfl, rfl⟩
    · exact ih idx (idx + 1) g hg

theorem chainOut_lt (ws : List ℕ) : ∀ (acc idx : ℕ), acc < idx →
    chainOut acc idx ws < idx + ws.length := by
  induction ws with
  | nil => intro acc idx h; simp [chainOut]; omega
  | cons w ws ih => intro acc idx h; simp only [chainOut, List.length_cons]; have := ih idx (idx + 1) (by omega); omega

end PEqualNP.Outside.L_meta_2774

open PEqualNP.Outside.L_meta_2774 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_2774 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (T L : Finset ℕ) (i₁ i₂ a b c : ℕ),
  (PEqualNP.TopForm.IsAO2 n C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack n C ∧ PEqualNP.MetaComplexity.NestedCover.IsOrTree n C T L C.output ∧
  n + i₁ ∈ L ∧ n + i₂ ∈ L ∧ i₁ ≠ i₂ ∧
  (PEqualNP.MetaComplexity.NestedCover.gateAt C i₁).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C i₁).inputs = [a, b] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C i₁).inputs = [b, a]) ∧
  (PEqualNP.MetaComplexity.NestedCover.gateAt C i₂).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C i₂).inputs = [a, c] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C i₂).inputs = [c, a]) ∧
  (∀ k < C.gates.length, k ∉ T → n + i₁ ∉ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs ∧ n + i₂ ∉ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs ∧
    ∀ j ∈ T, n + j ∉ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs)) →
  ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 n D ∧
  PEqualNP.MetaComplexity.circuitFun n D = PEqualNP.MetaComplexity.circuitFun n C ∧ D.size + 1 ≤ C.size := by
  intro n C T L i₁ i₂ a b c h
  classical
  obtain ⟨hAO2, hRB, hT, hL1, hL2, hne, hop1, hin1, hop2, hin2, hside⟩ := h
  obtain ⟨hAO, -, hlen2⟩ := hAO2
  set gs := C.gates with hgs
  have gat : ∀ j, PEqualNP.MetaComplexity.NestedCover.gateAt C j = gs.getD j ⟨GateOp.or, []⟩ :=
    fun j => rfl
  have hTlt : ∀ j ∈ T, j < gs.length := by
    intro j hj
    by_contra hc
    have h2 := (hT.1 j hj).2.1
    rw [gat, List.getD_eq_default _ _ (by omega)] at h2
    simp at h2
  have hi1lt : i₁ < gs.length := by
    by_contra hc
    rw [gat, List.getD_eq_default _ _ (by omega)] at hop1
    simp at hop1
  have hi2lt : i₂ < gs.length := by
    by_contra hc
    rw [gat, List.getD_eq_default _ _ (by omega)] at hop2
    simp at hop2
  have hi1T : i₁ ∉ T := fun hm => (hT.2.1 _ hL1).1 ⟨by omega, by simpa using hm⟩
  have hi2T : i₂ ∉ T := fun hm => (hT.2.1 _ hL2).1 ⟨by omega, by simpa using hm⟩
  let keep : ℕ → Bool := fun j => decide (j ∉ T ∧ j ≠ i₁ ∧ j ≠ i₂)
  have hcl : ∀ j < gs.length, keep j = true → ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs,
      i < n + j ∧ Good n keep i := by
    intro j hj hk i hi
    have hk' : j ∉ T ∧ j ≠ i₁ ∧ j ≠ i₂ := by simpa [keep] using hk
    have hrb : i < n + j := hRB j hj i (by rw [gat]; exact hi)
    refine ⟨hrb, ?_⟩
    by_cases hin : i < n
    · exact Or.inl hin
    · right
      obtain ⟨s1, s2, s3⟩ := hside j hj hk'.1
      rw [gat] at s1 s2 s3
      simp only [keep, decide_eq_true_eq]
      refine ⟨fun hm => s3 (i - n) hm (by rwa [show n + (i - n) = i by omega]), ?_, ?_⟩
      · intro e; exact s1 (by rwa [show n + i₁ = i by omega])
      · intro e; exact s2 (by rwa [show n + i₂ = i by omega])
  set st := comp n keep gs ((List.range n), []) with hst
  set M := st.1 with hM
  set D0 := st.2 with hD0
  let d := D0.length
  let g1 : Gate := ⟨GateOp.or, [M.getD b 0, M.getD c 0]⟩
  let g2 : Gate := ⟨GateOp.and, [M.getD a 0, n + d]⟩
  let Lr : List ℕ := ((L.erase (n + i₁)).erase (n + i₂)).toList
  let ws := Lr.map (fun l => M.getD l 0)
  let D : Circuit := ⟨D0 ++ [g1, g2] ++ chain (n + d + 1) (n + d + 2) ws,
    chainOut (n + d + 1) (n + d + 2) ws⟩
  have goodOf : ∀ j < gs.length, j ∉ T → ∀ u ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs,
      u < n + j ∧ Good n keep u := by
    intro j hj hjT u hu
    have hrb : u < n + j := hRB j hj u (by rw [gat]; exact hu)
    refine ⟨hrb, ?_⟩
    by_cases hin : u < n
    · exact Or.inl hin
    · right
      obtain ⟨s1, s2, s3⟩ := hside j hj hjT
      rw [gat] at s1 s2 s3
      simp only [keep, decide_eq_true_eq]
      refine ⟨fun hm => s3 (u - n) hm (by rwa [show n + (u - n) = u by omega]), ?_, ?_⟩
      · intro e; exact s1 (by rwa [show n + i₁ = u by omega])
      · intro e; exact s2 (by rwa [show n + i₂ = u by omega])
  have ha : a < n + gs.length ∧ Good n keep a := by
    have hm : a ∈ (gs.getD i₁ ⟨GateOp.or, []⟩).inputs := by
      rw [← gat]; rcases hin1 with e | e <;> rw [e] <;> simp
    have := goodOf i₁ hi1lt hi1T a hm; exact ⟨by omega, this.2⟩
  have hb : b < n + gs.length ∧ Good n keep b := by
    have hm : b ∈ (gs.getD i₁ ⟨GateOp.or, []⟩).inputs := by
      rw [← gat]; rcases hin1 with e | e <;> rw [e] <;> simp
    have := goodOf i₁ hi1lt hi1T b hm; exact ⟨by omega, this.2⟩
  have hc : c < n + gs.length ∧ Good n keep c := by
    have hm : c ∈ (gs.getD i₂ ⟨GateOp.or, []⟩).inputs := by
      rw [← gat]; rcases hin2 with e | e <;> rw [e] <;> simp
    have := goodOf i₂ hi2lt hi2T c hm; exact ⟨by omega, this.2⟩
  have hTne : T ≠ ∅ := by
    intro e
    have hLs : L = {C.output} := by simpa [e] using hT.2.2.2
    rw [hLs, Finset.mem_singleton] at hL1 hL2
    omega
  obtain ⟨j0, hj0, hρ⟩ : ∃ j ∈ T, C.output = n + j := by simpa [hTne] using hT.2.2.2
  have hLgood : ∀ l ∈ L, l ≠ n + i₁ → l ≠ n + i₂ → l < n + gs.length ∧ Good n keep l := by
    intro l hl h1 h2
    have hnot := (hT.2.1 l hl).1
    have hlρ : l ≠ C.output := by
      intro e; rw [e, hρ] at hnot; exact hnot ⟨by omega, by simpa using hj0⟩
    obtain ⟨j, hj, hlj⟩ := vO hT (Or.inl hl) hlρ
    have hlt := hRB j (hTlt j hj) l hlj
    refine ⟨by have := hTlt j hj; omega, ?_⟩
    by_cases hin : l < n
    · exact Or.inl hin
    · right
      simp only [keep, decide_eq_true_eq]
      refine ⟨fun hm => hnot ⟨by omega, hm⟩, ?_, ?_⟩
      · intro e; exact h1 (by omega)
      · intro e; exact h2 (by omega)
  have y0 : (List.replicate n false).length = n := by simp
  have hinv0 := cinv n keep (List.replicate n false) y0 gs hcl
  have Mlt : ∀ i < n + gs.length, Good n keep i → M.getD i 0 < n + D0.length :=
    fun i hi hg => (hinv0.2 i hi hg).1
  have hLr : ∀ l ∈ Lr, l < n + gs.length ∧ Good n keep l := by
    intro l hl
    simp only [Lr, Finset.mem_toList, Finset.mem_erase] at hl
    exact hLgood l hl.2.2 hl.2.1 hl.1
  have hws : ∀ w ∈ ws, w < n + d := by
    intro w hw
    simp only [ws, List.mem_map] at hw
    obtain ⟨l, hl, rfl⟩ := hw
    exact Mlt l (hLr l hl).1 (hLr l hl).2
  have hDg : D.gates = D0 ++ ([g1, g2] ++ chain (n + d + 1) (n + d + 2) ws) := by
    simp only [D, List.append_assoc]
  refine ⟨D, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro g hg
    rw [hDg, List.mem_append, List.mem_append] at hg
    rcases hg with h | h | h
    · obtain ⟨g0, hg0, hop, -⟩ := comp_gates n keep gs g h
      rw [hop]; exact hAO g0 hg0
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl
      · exact Or.inr rfl
      · exact Or.inl rfl
    · exact Or.inr (chain_mem _ _ _ g h).1
  · intro j hj i hi
    rw [PEqualNP.MetaComplexity.NestedCover.gateAt, hDg] at hi
    have hjl : j < D0.length + (2 + ws.length) := by
      have : D.gates.length = D0.length + (2 + ws.length) := by
        rw [hDg]; simp [chain_length]; omega
      omega
    by_cases h1 : j < D0.length
    · rw [List.getD_append _ _ _ _ h1] at hi
      exact comp_readsback n keep (List.replicate n false) y0 gs hcl j h1 i hi
    · rw [List.getD_append_right _ _ _ _ (by omega)] at hi
      by_cases h2 : j - D0.length < 2
      · rw [List.getD_append _ _ _ _ (by simpa using h2)] at hi
        by_cases h3 : j = D0.length
        · subst h3
          simp only [Nat.sub_self, List.getD_cons_zero, g1, List.mem_cons, List.not_mem_nil,
            or_false] at hi
          rcases hi with rfl | rfl
          · exact Mlt b hb.1 hb.2
          · exact Mlt c hc.1 hc.2
        · have h4 : j - D0.length = 1 := by omega
          rw [h4] at hi
          simp only [List.getD_cons_succ, List.getD_cons_zero, g2, List.mem_cons, List.not_mem_nil,
            or_false] at hi
          rcases hi with rfl | rfl
          · have := Mlt a ha.1 ha.2; omega
          · omega
      · rw [List.getD_append_right _ _ _ _ (by simp; omega)] at hi
        simp only [List.length_cons, List.length_nil] at hi
        have hk : j - D0.length - 2 < ws.length := by omega
        have := (chain_shape ws (n + d + 1) (n + d + 2) (by omega)
          (fun w hw => by have := hws w hw; omega) (j - D0.length - 2) hk).2.2 i hi
        omega
  · intro g hg
    rw [hDg, List.mem_append, List.mem_append] at hg
    rcases hg with h | h | h
    · obtain ⟨g0, hg0, -, hl⟩ := comp_gates n keep gs g h
      rw [hl]; exact hlen2 g0 hg0
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl <;> rfl
    · exact (chain_mem _ _ _ g h).2
  · funext x
    show D.eval (List.ofFn x) = C.eval (List.ofFn x)
    set y := List.ofFn x with hyd
    have hy : y.length = n := by simp [hyd]
    have hinv := cinv n keep y hy gs hcl
    have hM' : ∀ i < n + gs.length, Good n keep i →
        (wiresFrom D0 y).getD (M.getD i 0) false = (wiresFrom gs y).getD i false :=
      fun i hi hg => (hinv.2 i hi hg).2
    set V0 := wiresFrom D0 y with hV0
    have hV0l : V0.length = n + d := by rw [hV0, wiresFrom_length, hy]
    have hMa := Mlt a ha.1 ha.2
    have hMb := Mlt b hb.1 hb.2
    have hMc := Mlt c hc.1 hc.2
    set e1 := (V0.getD (M.getD b 0) false || V0.getD (M.getD c 0) false) with he1
    set e2 := (V0.getD (M.getD a 0) false && e1) with he2
    have hV1 : wiresFrom [g1, g2] V0 = V0 ++ [e1] ++ [e2] := by
      simp only [wiresFrom, List.foldl_cons, List.foldl_nil, g1, g2, List.map_cons, List.map_nil]
      rw [List.getD_append _ _ _ _ (by omega : M.getD a 0 < V0.length),
        List.getD_append_right _ _ _ _ (by omega : V0.length ≤ n + d),
        show n + d - V0.length = 0 by omega, List.getD_cons_zero]
      simp [GateOp.eval, he1, he2]
    set V1 := V0 ++ [e1] ++ [e2] with hV1d
    have hV1l : V1.length = n + d + 2 := by simp [hV1d, hV0l]
    have hce := chain_eval ws (n + d + 1) V1 (by omega) (fun w hw => by have := hws w hw; omega)
    rw [hV1l] at hce
    have hDeval : D.eval y = (e2 || Lr.any (fun l => (wiresFrom gs y).getD l false)) := by
      change (wiresFrom D.gates y).getD D.output false = _
      rw [hDg, wiresFrom_append, wiresFrom_append, hV1]
      change (wiresFrom (chain (n + d + 1) (n + d + 2) ws) V1).getD
        (chainOut (n + d + 1) (n + d + 2) ws) false = _
      rw [hce]
      have hlast : V1.getD (n + d + 1) false = e2 := by
        rw [hV1d, List.getD_append_right _ _ _ _ (by simp [hV0l])]
        simp [hV0l]
      rw [hlast]
      congr 1
      simp only [ws, List.any_map]
      rw [Bool.eq_iff_iff]
      simp only [List.any_eq_true, Function.comp]
      constructor
      · rintro ⟨l, hl, hv⟩
        refine ⟨l, hl, ?_⟩
        have hlt := Mlt l (hLr l hl).1 (hLr l hl).2
        rw [hV1d, List.append_assoc, List.getD_append _ _ _ _ (by omega)] at hv
        rwa [← hM' l (hLr l hl).1 (hLr l hl).2]
      · rintro ⟨l, hl, hv⟩
        refine ⟨l, hl, ?_⟩
        have hlt := Mlt l (hLr l hl).1 (hLr l hl).2
        rw [hV1d, List.append_assoc, List.getD_append _ _ _ _ (by omega)]
        rwa [hM' l (hLr l hl).1 (hLr l hl).2]
    have hCeval : C.eval y = true ↔ ∃ l ∈ L, (wiresFrom gs y).getD l false = true := by
      change (wiresFrom gs y).getD C.output false = true ↔ _
      exact fI hT hRB hTlt (fun w => (wiresFrom gs y).getD w false = true) (fun j hj => by
        have hv := gate_val gs y j (hTlt j hj)
          (fun u hu => by rw [hy]; exact hRB j (hTlt j hj) u (by rw [gat]; exact hu))
        rw [hy] at hv
        rw [hv, ← gat, (hT.1 j hj).1]
        simp [GateOp.eval, List.any_map])
    have h1v : (wiresFrom gs y).getD (n + i₁) false =
        ((wiresFrom gs y).getD a false && (wiresFrom gs y).getD b false) := by
      have hv := gate_val gs y i₁ hi1lt
        (fun u hu => by rw [hy]; exact hRB i₁ hi1lt u (by rw [gat]; exact hu))
      rw [hy] at hv
      rw [hv, ← gat, hop1]
      rcases hin1 with e | e <;> rw [e] <;> simp [GateOp.eval, Bool.and_comm]
    have h2v : (wiresFrom gs y).getD (n + i₂) false =
        ((wiresFrom gs y).getD a false && (wiresFrom gs y).getD c false) := by
      have hv := gate_val gs y i₂ hi2lt
        (fun u hu => by rw [hy]; exact hRB i₂ hi2lt u (by rw [gat]; exact hu))
      rw [hy] at hv
      rw [hv, ← gat, hop2]
      rcases hin2 with e | e <;> rw [e] <;> simp [GateOp.eval, Bool.and_comm]
    have he2' : e2 = ((wiresFrom gs y).getD a false &&
        ((wiresFrom gs y).getD b false || (wiresFrom gs y).getD c false)) := by
      rw [he2, he1, hM' a ha.1 ha.2, hM' b hb.1 hb.2, hM' c hc.1 hc.2]
    have hLrmem : ∀ l, l ∈ Lr ↔ (l ≠ n + i₂ ∧ l ≠ n + i₁ ∧ l ∈ L) := by
      intro l
      simp only [Lr, Finset.mem_toList, Finset.mem_erase]
    rw [hDeval, Bool.eq_iff_iff, hCeval, he2']
    simp only [Bool.or_eq_true, Bool.and_eq_true, List.any_eq_true]
    constructor
    · rintro (⟨hA, hB | hC⟩ | ⟨l, hl, hv⟩)
      · exact ⟨n + i₁, hL1, by rw [h1v, Bool.and_eq_true]; exact ⟨hA, hB⟩⟩
      · exact ⟨n + i₂, hL2, by rw [h2v, Bool.and_eq_true]; exact ⟨hA, hC⟩⟩
      · exact ⟨l, ((hLrmem l).mp hl).2.2, hv⟩
    · rintro ⟨l, hl, hv⟩
      by_cases e1' : l = n + i₁
      · subst e1'
        rw [h1v] at hv
        simp only [Bool.and_eq_true] at hv
        exact Or.inl ⟨hv.1, Or.inl hv.2⟩
      · by_cases e2' : l = n + i₂
        · subst e2'
          rw [h2v] at hv
          simp only [Bool.and_eq_true] at hv
          exact Or.inl ⟨hv.1, Or.inr hv.2⟩
        · exact Or.inr ⟨l, (hLrmem l).mpr ⟨e2', e1', hl⟩, hv⟩
  · show D.gates.length + 1 ≤ C.gates.length
    rw [hDg]
    simp only [List.length_append, List.length_cons, List.length_nil, chain_length, List.length_map]
    have hsub : insert i₁ (insert i₂ T) ⊆ Finset.range gs.length := by
      intro j hj
      simp only [Finset.mem_insert] at hj
      rw [Finset.mem_range]
      rcases hj with rfl | rfl | hj
      · exact hi1lt
      · exact hi2lt
      · exact hTlt j hj
    have hcardI : (insert i₁ (insert i₂ T)).card = T.card + 2 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem hi2T]
      simp only [Finset.mem_insert, not_or]
      exact ⟨hne, hi1T⟩
    have hfil : (Finset.range gs.length).filter (fun j => keep j = true) =
        Finset.range gs.length \ insert i₁ (insert i₂ T) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_insert, keep, decide_eq_true_eq]
      tauto
    have h1 : D0.length = gs.length - (T.card + 2) := by
      rw [hD0, hst, comp_snd_len, hfil, Finset.card_sdiff_of_subset hsub, Finset.card_range, hcardI]
    have hle := Finset.card_le_card hsub
    rw [Finset.card_range, hcardI] at hle
    have e1 : n + i₂ ∈ L.erase (n + i₁) := Finset.mem_erase.mpr ⟨by omega, hL2⟩
    have h2 : ws.length = L.card - 2 := by
      change (List.map _ ((L.erase (n + i₁)).erase (n + i₂)).toList).length = L.card - 2
      rw [List.length_map, Finset.length_toList, Finset.card_erase_of_mem e1,
        Finset.card_erase_of_mem hL1]
      omega
    have h3 := gN hT
    have hL2c : 2 ≤ L.card := by
      have hs : ({n + i₁, n + i₂} : Finset ℕ) ⊆ L := by
        intro w hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl
        · exact hL1
        · exact hL2
      have := Finset.card_le_card hs
      rwa [Finset.card_pair (by omega)] at this
    rw [← hgs, h1, h2]
    omega
