import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_1482_682
    (transport :
    let E := fun p l : Fin 13 => p = l ∨ p = l+1 ∨ p = l+3 ∨ p = l+9
    ∀ p l, E p l → ∃ P L : Equiv.Perm (Fin 13),
      P p = 0 ∧ L l = 0 ∧ ∀ i j, E (P i) (L j) ↔ E i j)
    (semantics :
    ∀ n (C : Circuit) (x : Fin n → Bool),
    let W := fun i => (C.wires (List.ofFn x)).getD i false
    (∀ i : Fin n, W i.val = x i) ∧ (∀ i, n+C.size ≤ i → W i = false) ∧
    ∀ j g a b, C.gates[j]? = some g → g.inputs = [a,b] → a < n+j → b < n+j →
      (g.op = .and → W (n+j) = (W a && W b)) ∧ (g.op = .or → W (n+j) = (W a || W b)))
    (safe :
    let X := Fin 26 → Bool
    let T := (X → Bool) × Bool × Bool
    let atom := fun i : Fin 26 => (((fun x => x i), decide (i = 13), decide (i = 0)) : T)
    let J := fun a b : T => (((fun x => a.1 x || b.1 x), a.2.1 || b.2.1, a.2.2 || b.2.2) : T)
    let cross := fun (i : Fin 26) (f g : X → Bool) (r s : Bool) =>
      (f (fun j => decide (j = i)) && s) || (r && g (fun j => decide (j = i)))
    let M := fun a b : T => (((fun x => a.1 x && b.1 x), cross 0 a.1 b.1 a.2.1 b.2.1,
      cross 13 a.1 b.1 a.2.2 b.2.2) : T)
    let F := fun x : X => decide (∃ i j : Fin 13, (i = j ∨ i = j+1 ∨ i = j+3 ∨ i = j+9) ∧
      x (Fin.castAdd 13 i) = true ∧ x (Fin.natAdd 13 j) = true)
    ∃ U : Set (Multiset T), Finset.univ.val.map atom ∈ U ∧
      (∀ K ∈ U, K.card < 90 → ∀ a b, a ::ₘ b ::ₘ 0 ≤ K →
        J a b ::ₘ K ∈ U ∧ M a b ::ₘ K ∈ U) ∧
      ∀ K ∈ U, (F,false,false) ∉ K) :
    ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, C.size ≤ 64 ∧ (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ a b : ℕ, g.inputs = [a, b] ∧ a ≠ b ∧ a < 26 + j ∧ b < 26 + j) ∧ (∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔ ∃ u t : Fin 13, (u = t ∨ u = t + 1 ∨ u = t + 3 ∨ u = t + 9) ∧ x (Fin.castAdd 13 u) = true ∧ x (Fin.natAdd 13 t) = true) ∧ ∃ p l : Fin 13, (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) ∧ (∃ v : ℕ → Bool, (∀ my : Fin 13, v my.val = false ∧ v (13 + my.val) = decide (my = l)) ∧ (∀ (ky : ℕ) (hy : PEqualNP.CircuitLowerBounds.Gate) (cy dy : ℕ), C.gates[ky]? = some hy → hy.inputs = [cy, dy] → (hy.op = PEqualNP.CircuitLowerBounds.GateOp.and → v (26 + ky) = (((C.wires (List.ofFn (fun iy : Fin 26 => decide (iy = Fin.castAdd 13 p)))).getD cy false && v dy) || (v cy && (C.wires (List.ofFn (fun ey : Fin 26 => decide (ey = Fin.castAdd 13 p)))).getD dy false))) ∧ (hy.op = PEqualNP.CircuitLowerBounds.GateOp.or → v (26 + ky) = (v cy || v dy))) ∧ v C.output = false) ∧ (∃ w : ℕ → Bool, (∀ mx : Fin 13, w mx.val = decide (mx = p) ∧ w (13 + mx.val) = false) ∧ (∀ (kx : ℕ) (hx : PEqualNP.CircuitLowerBounds.Gate) (cx dx : ℕ), C.gates[kx]? = some hx → hx.inputs = [cx, dx] → (hx.op = PEqualNP.CircuitLowerBounds.GateOp.and → w (26 + kx) = (((C.wires (List.ofFn (fun ix : Fin 26 => decide (ix = Fin.natAdd 13 l)))).getD cx false && w dx) || (w cx && (C.wires (List.ofFn (fun ex : Fin 26 => decide (ex = Fin.natAdd 13 l)))).getD dx false))) ∧ (hx.op = PEqualNP.CircuitLowerBounds.GateOp.or → w (26 + kx) = (w cx || w dx))) ∧ w C.output = false)) := by
  classical
  rintro ⟨C,cap,model,spec,p,l,flag,⟨v,vi,vg,vo⟩,w,wi,wg,wo⟩
  obtain ⟨P,L,hp,hl,adj⟩ := transport p l flag
  let X := Fin 26 → Bool
  let T := (X → Bool) × Bool × Bool
  let atom := fun i : Fin 26 => (((fun x => x i), decide (i = 13), decide (i = 0)) : T)
  let J := fun a b : T => (((fun x => a.1 x || b.1 x), a.2.1 || b.2.1, a.2.2 || b.2.2) : T)
  let cross := fun (i : Fin 26) (f g : X → Bool) (r s : Bool) =>
    (f (fun j => decide (j = i)) && s) || (r && g (fun j => decide (j = i)))
  let M := fun a b : T => (((fun x => a.1 x && b.1 x), cross 0 a.1 b.1 a.2.1 b.2.1,
    cross 13 a.1 b.1 a.2.2 b.2.2) : T)
  let F := fun x : X => decide (∃ i j : Fin 13, (i = j ∨ i = j+1 ∨ i = j+3 ∨ i = j+9) ∧
    x (Fin.castAdd 13 i) = true ∧ x (Fin.natAdd 13 j) = true)
  let f : (Fin 13 ⊕ Fin 13) ≃ Fin 26 := finSumFinEquiv
  let e : Equiv.Perm (Fin 26) := (f.symm.trans (P.sumCongr L)).trans f
  have ep (u : Fin 13) : e (Fin.castAdd 13 u) = Fin.castAdd 13 (P u) := by
    change f ((P.sumCongr L) (f.symm (f (.inl u)))) = _
    rw [f.symm_apply_apply]
    rfl
  have el (t : Fin 13) : e (Fin.natAdd 13 t) = Fin.natAdd 13 (L t) := by
    change f ((P.sumCongr L) (f.symm (f (.inr t)))) = _
    rw [f.symm_apply_apply]
    rfl
  have e0 : e (Fin.castAdd 13 p) = 0 := by rw [ep,hp]; rfl
  have e13 : e (Fin.natAdd 13 l) = 13 := by rw [el,hl]; rfl
  let rename (x : X) (i : Fin 26) := x (e i)
  let single (i j : Fin 26) := decide (j=i)
  have pull (i : Fin 26) : rename (single (e i)) = single i := by
    funext j; simp [rename,single]
  have pullP : rename (single 0) = single (Fin.castAdd 13 p) := e0 ▸ pull _
  have pullL : rename (single 13) = single (Fin.natAdd 13 l) := e13 ▸ pull _
  let W (k : ℕ) (x : X) := (C.wires (List.ofFn (rename x))).getD k false
  let A (k : ℕ) : T := (W k,v k,w k)
  have init (i : Fin 26) : A i.val = atom (e i) := by
    have val : W i.val = fun x : X => x (e i) := by
      funext x; exact (semantics 26 C (rename x)).1 i
    have components (k : Fin 26) :
        v k.val = decide (k = Fin.natAdd 13 l) ∧ w k.val = decide (k = Fin.castAdd 13 p) := by
      refine Fin.addCases (m := 13) (n := 13) ?_ ?_ k
      · intro u
        have hn : Fin.castAdd 13 u ≠ Fin.natAdd 13 l := by
          intro h; have hh := congrArg Fin.val h; change u.val = 13+l.val at hh; omega
        have eq : Fin.castAdd 13 u = Fin.castAdd 13 p ↔ u=p := by
          rw [Fin.ext_iff,Fin.ext_iff (a:=u) (b:=p)]
          rfl
        simp only [hn,decide_false,eq]
        exact ⟨(vi u).1,(wi u).1⟩
      · intro t
        have hn : Fin.natAdd 13 t ≠ Fin.castAdd 13 p := by
          intro h; have hh := congrArg Fin.val h; change 13+t.val = p.val at hh; omega
        have eq : Fin.natAdd 13 t = Fin.natAdd 13 l ↔ t=l := by
          rw [Fin.ext_iff,Fin.ext_iff (a:=t) (b:=l)]
          exact Nat.add_left_cancel_iff
        simp only [hn,decide_false,eq]
        exact ⟨(vi t).2,(wi t).2⟩
    obtain ⟨hv,hw⟩ := components i
    have s13 : e i = 13 ↔ i = Fin.natAdd 13 l := by rw [←e13,e.injective.eq_iff]
    have s0 : e i = 0 ↔ i = Fin.castAdd 13 p := by rw [←e0,e.injective.eq_iff]
    simp only [A,atom,val,s13,s0,hv,hw]
  obtain ⟨U,base,move,exclude⟩ := safe
  let bag (j : ℕ) := (Multiset.range (26+j)).map A
  have bags (j : ℕ) (hj : j ≤ C.size) : bag j ∈ U := by
    induction j with
    | zero =>
      change (Multiset.range 26).map A ∈ U
      have hr : Multiset.range 26 = (Finset.univ : Finset (Fin 26)).val.map Fin.val := by decide
      rw [hr,Multiset.map_map]
      have hfun : A ∘ Fin.val = atom ∘ e := funext init
      rw [hfun,← Multiset.map_map,Multiset.map_univ_val_equiv]
      exact base
    | succ j ih =>
      have hlen : j < C.gates.length := by change j < C.size; omega
      let g := C.gates[j]
      have hit : C.gates[j]? = some g := List.getElem?_eq_getElem hlen
      obtain ⟨tag,a,b,ins,ne,ha,hb⟩ := model j g hit
      have hpair : a ::ₘ b ::ₘ (0 : Multiset ℕ) ≤ Multiset.range (26+j) := by
        apply (Multiset.le_iff_subset (by simp [ne])).2
        intro k hk
        rcases (show k=a ∨ k=b by simpa using hk) with rfl | rfl
        · exact Multiset.mem_range.mpr ha
        · exact Multiset.mem_range.mpr hb
      have pair : A a ::ₘ A b ::ₘ 0 ≤ bag j := by simpa [bag] using Multiset.map_le_map (f := A) hpair
      have next := move (bag j) (ih (by omega)) (by simp [bag]; omega) (A a) (A b) pair
      change (Multiset.range ((26+j)+1)).map A ∈ U
      rw [Multiset.range_succ,Multiset.map_cons]
      have vals (x : X) := (semantics 26 C (rename x)).2.2 j g a b hit ins ha hb
      have vs := vg j g a b hit ins
      have ws := wg j g a b hit ins
      rcases tag with tag | tag
      · have prod : W (26+j) = fun x => W a x && W b x := funext fun x => (vals x).1 tag
        have va : v (26+j) = cross 0 (W a) (W b) (v a) (v b) := by
          simpa only [cross,W,←show (fun j : Fin 26 => decide (j = 0)) = single 0 from rfl,pullP,single] using vs.1 tag
        have wa : w (26+j) = cross 13 (W a) (W b) (w a) (w b) := by
          simpa only [cross,W,←show (fun j : Fin 26 => decide (j = 13)) = single 13 from rfl,pullL,single] using ws.1 tag
        have eq : A (26+j) = M (A a) (A b) := by
          change (W (26+j),v (26+j),w (26+j)) = _
          rw [prod,va,wa]
        rw [eq]
        exact next.2
      · have sum : W (26+j) = fun x => W a x || W b x := funext fun x => (vals x).2 tag
        have eq : A (26+j) = J (A a) (A b) := by
          change (W (26+j),v (26+j),w (26+j)) = _
          rw [sum,vs.2 tag,ws.2 tag]
        rw [eq]
        exact next.1
  have root : W C.output = F := by
    funext x
    apply Bool.eq_iff_iff.mpr
    change (C.eval (List.ofFn (rename x)) = true) ↔ decide _ = true
    rw [decide_eq_true_eq,spec]
    constructor
    · rintro ⟨i,j,ij,hi,hj⟩
      exact ⟨P i,L j,(adj i j).2 ij,by simpa only [rename,ep] using hi,by simpa only [rename,el] using hj⟩
    · rintro ⟨i,j,ij,hi,hj⟩
      obtain ⟨u,rfl⟩ := P.surjective i
      obtain ⟨t,rfl⟩ := L.surjective j
      exact ⟨u,t,(adj u t).1 ij,by simpa only [rename,ep] using hi,by simpa only [rename,el] using hj⟩
  have out : C.output < 26+C.size := by
    by_contra! h
    let x : X := fun _ => true
    have no := (semantics 26 C (rename x)).2.1 _ h
    have yes : C.eval (List.ofFn (rename x)) = true := (spec _).2 ⟨0,0,Or.inl rfl,rfl,rfl⟩
    exact Bool.noConfusion (no.symm.trans yes)
  have last : A C.output = (F,false,false) := by change (W C.output,v C.output,w C.output) = _; rw [root,vo,wo]
  apply exclude _ (bags C.size (le_refl _))
  exact Multiset.mem_map.mpr ⟨_,Multiset.mem_range.mpr out,last⟩
