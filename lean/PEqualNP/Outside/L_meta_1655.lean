import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1655

-- Wire evaluation lemmas adapted from the L-meta-1460 proof.
def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih => rw [run_cons, ih]; simp; omega

lemma run_getD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (run gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

lemma run_split (gs : List Gate) (x : List Bool) (j : ℕ) :
    run gs x = run (gs.drop j) (run (gs.take j) x) := by
  simpa only [run, List.foldl_append] using
    congrArg (fun l : List Gate => run l x) (List.take_append_drop j gs).symm

def value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma input_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (p : Fin n) :
    value C x p = x p := by
  change (run C.gates (List.ofFn x)).getD p false = x p
  have hp : (p : ℕ) < (List.ofFn x).length := by simp
  rw [run_getD _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp

lemma missing_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.size ≤ w) : value C x w = false := by
  change (run C.gates (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by simpa [run_length, Circuit.size] using hw)

lemma gate_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + C.size) :
    let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
    value C x w = g.op.eval (g.inputs.map fun r => if r < w then value C x r else false) := by
  let j := w - n
  have hj : j < C.gates.length := by unfold j Circuit.size at *; omega
  let g := C.gates[j]
  let earlier := run (C.gates.take j) (List.ofFn x)
  have plen : earlier.length = w := by
    simp [earlier, run_length, Nat.min_eq_left hj.le, j]; omega
  have split : run C.gates (List.ofFn x) = run (g :: C.gates.drop (j + 1)) earlier := by
    rw [run_split C.gates (List.ofFn x) j, List.drop_eq_getElem_cons hj]
  have read (r : ℕ) : earlier.getD r false = if r < w then value C x r else false := by
    by_cases hr : r < w
    · rw [ite_eq_left hr]
      change earlier.getD r false = (run C.gates (List.ofFn x)).getD r false
      rw [split]
      exact (run_getD _ earlier r (by simpa only [plen] using hr)).symm
    · rw [ite_eq_right hr]
      exact List.getD_eq_default _ _ (by omega)
  change (run C.gates (List.ofFn x)).getD w false =
    g.op.eval (g.inputs.map fun r => if r < w then value C x r else false)
  rw (occs := [1]) [split]
  rw (occs := [1]) [run_cons]
  rw [run_getD _ _ _ (by simp [plen]), List.getD_append_right _ _ _ _ (by omega)]
  simp only [plen, Nat.sub_self, List.getD_cons_zero, read]

lemma gate_mono {n : ℕ} (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : C.gates[k].op = GateOp.and ∨ C.gates[k].op = GateOp.or)
    (x y : Fin n → Bool)
    (h : ∀ r ∈ C.gates[k].inputs, r < n + k → value C x r = true → value C y r = true) :
    value C x (n + k) = true → value C y (n + k) = true := by
  have hw : n + k < n + C.size := by unfold Circuit.size; omega
  have hx := gate_value C x (n + k) (by omega) hw
  have hy := gate_value C y (n + k) (by omega) hw
  simp only [Nat.add_sub_cancel_left] at hx hy
  rw [hx, hy]
  have hr (r : ℕ) (hm : r ∈ C.gates[k].inputs) :
      (if r < n + k then value C x r else false) = true →
      (if r < n + k then value C y r else false) = true := by
    by_cases h' : r < n + k
    · simpa [h'] using h r hm h'
    · simp [h']
  rcases hop with hop | hop
  · simp only [hop, GateOp.eval, List.all_eq_true, id_eq]
    intro hx b hb
    obtain ⟨r, hm, rfl⟩ := List.mem_map.mp hb
    exact hr r hm (hx _ (List.mem_map.mpr ⟨r, hm, rfl⟩))
  · simp only [hop, GateOp.eval, List.any_eq_true, id_eq]
    intro hx
    obtain ⟨b, hb, rfl⟩ := hx
    obtain ⟨r, hm, hv⟩ := List.mem_map.mp hb
    exact ⟨_, List.mem_map.mpr ⟨r, hm, rfl⟩, hr r hm hv⟩

lemma or_value {n : ℕ} (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : C.gates[k].op = GateOp.or) (x : Fin n → Bool) :
    value C x (n + k) = true ↔ ∃ r ∈ C.gates[k].inputs, r < n + k ∧ value C x r = true := by
  have hw : n + k < n + C.size := by unfold Circuit.size; omega
  have hx := gate_value C x (n + k) (by omega) hw
  simp only [Nat.add_sub_cancel_left] at hx
  rw [hx, hop]
  simp [GateOp.eval]

lemma and_value {n : ℕ} (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : C.gates[k].op = GateOp.and) (x : Fin n → Bool) :
    value C x (n + k) = true ↔ ∀ r ∈ C.gates[k].inputs, r < n + k ∧ value C x r = true := by
  have hw : n + k < n + C.size := by unfold Circuit.size; omega
  have hx := gate_value C x (n + k) (by omega) hw
  simp only [Nat.add_sub_cancel_left] at hx
  rw [hx, hop]
  simp [GateOp.eval]

private lemma monotoneCut {n : ℕ} (C : Circuit)
    (j : Fin C.gates.length)
    (ops : ∀ i : Fin C.gates.length, i ≠ j →
      (C.gates.get i).op = .and ∨ (C.gates.get i).op = .or)
    (x y : Fin n → Bool) (hxy : ∀ p, x p = true → y p = true)
    (cut : ℕ) (hn : n+(j:ℕ) < cut →
      value C x (n+(j:ℕ)) = true → value C y (n+(j:ℕ)) = true)
    (w : ℕ) (hw : w<cut) : value C x w = true → value C y w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hraw : w<n
    · let p : Fin n := ⟨w,hraw⟩
      change value C x p = true → value C y p = true
      simpa only [input_value] using hxy p
    by_cases hmissing : n+C.size ≤ w
    · rw [missing_value C x w hmissing]
      simp
    let i : Fin C.gates.length := ⟨w-n,by unfold Circuit.size at hmissing; omega⟩
    have he : w = n+(i:ℕ) := by simp [i]; omega
    by_cases hi : i=j
    · rw [he,hi] at hw ⊢
      exact hn hw
    · rw [he]
      exact gate_mono C i i.isLt (ops i hi) x y
        (fun r _ hr => ih r (by omega) (by omega))

private lemma not_eval {n : ℕ} (C : Circuit) (j h : Fin C.gates.length)
    (hop : (C.gates.get j).op = .not) (hlt : h<j)
    (hin : ∃ rs, (C.gates.get j).inputs = (n+(h:ℕ))::rs)
    (x : Fin n → Bool) :
    value C x (n+(j:ℕ)) = !(value C x (n+(h:ℕ))) := by
  have hj : n+(j:ℕ) < n+C.size := by unfold Circuit.size; exact Nat.add_lt_add_left j.isLt _
  have hread : n+(h:ℕ) < n+(j:ℕ) := Nat.add_lt_add_left hlt _
  have hv := gate_value C x (n+(j:ℕ)) (by omega) hj
  simp only [Nat.add_sub_cancel_left] at hv
  obtain ⟨rs,hrs⟩ := hin
  change value C x (n+(j:ℕ)) =
    (C.gates.get j).op.eval ((C.gates.get j).inputs.map
      fun r => if r<n+(j:ℕ) then value C x r else false) at hv
  rw [hv,hop,hrs]
  simp [GateOp.eval,hread]

private def avoids {n : ℕ} (A : Finset (Fin n)) (x : Fin n → Bool) : Prop :=
  ∀ p, x p = true → p ∉ A

private lemma monotoneOff {n : ℕ} (C : Circuit) (j h : Fin C.gates.length)
    (ops : ∀ i : Fin C.gates.length, i ≠ j →
      (C.gates.get i).op = .and ∨ (C.gates.get i).op = .or)
    (hop : (C.gates.get j).op = .not) (hlt : h<j)
    (hin : ∃ rs, (C.gates.get j).inputs = (n+(h:ℕ))::rs)
    (A : Finset (Fin n)) (hA : value C (fun p => decide (p ∉ A)) (n+(h:ℕ)) = false)
    (x y : Fin n → Bool) (hy : avoids A y)
    (hxy : ∀ p, x p = true → y p = true) (w : ℕ) :
    value C x w = true → value C y w = true := by
  have hs : value C y (n+(h:ℕ)) = false := by
    by_contra ht
    have ht' : value C y (n+(h:ℕ)) = true := by
      cases hv : value C y (n+(h:ℕ))
      · contradiction
      · rfl
    have hdom (p : Fin n) (hp : y p = true) : decide (p ∉ A) = true :=
      decide_eq_true (hy p hp)
    have hlt' : n+(h:ℕ) < n+(j:ℕ) := Nat.add_lt_add_left hlt _
    have hcross := monotoneCut C j ops y (fun p => decide (p ∉ A)) hdom
      (n+(j:ℕ)) (fun hh => False.elim ((Nat.lt_irrefl _) hh)) _ hlt' ht'
    rw [hA] at hcross
    cases hcross
  refine monotoneCut C j ops x y hxy (w+1) ?_ w (by omega)
  intro _ _
  rw [not_eval C j h hop hlt hin y,hs]
  rfl

end PEqualNP.Outside.L_meta_1655

open PEqualNP.Outside.L_meta_1655 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_1655 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N),
    2 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    p0 ≠ p1 → p0 ∈ L i0 → p1 ∈ L i0 →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin N → ℕ) (j h : Fin gates.length),
    (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ gt.inputs.length ≤ 2) →
    (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
    (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) →
    h < j → (∃ r : List ℕ, (gates.get j).inputs = (N + (h : ℕ)) :: r) →
    (∀ (t : Fin N) (x : Fin N → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
    ∀ ev : ℕ → (Fin N → Bool) → Bool, (∀ (w : ℕ) (x : Fin N → Bool), ev w x = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w⟩ (List.ofFn x)) →
    ev (N + (h : ℕ)) (fun v : Fin N => decide (v = p0)) = true → ev (N + (h : ℕ)) (fun v : Fin N => decide (v = p1)) = true → (∀ p : Fin N, p ≠ p0 → p ≠ p1 → ev (N + (h : ℕ)) (fun v : Fin N => decide (v = p)) = false) →
    ev (N + (h : ℕ)) (fun v : Fin N => decide (v ∉ L i0)) = false →
    ∀ Sm Dm : Fin N → ℕ → Prop,
    (∀ (t : Fin N) (w : ℕ), Sm t w ↔ ∀ x : Fin N → Bool, (∀ v : Fin N, x v = true → v ∉ L i0) → ev w x = true → ∃ v ∈ L t, x v = true) →
    (∀ (t : Fin N) (w : ℕ), Dm t w ↔ (Sm t w ∧ ∀ p ∈ L i0, ev w (fun v : Fin N => decide (v = p)) = true → p ∈ L t)) →
    ∀ Vs : Fin N → ℕ → Fin N → Prop,
    (∀ (t : Fin N) (w : ℕ) (v : Fin N), Vs t w v ↔ ((Dm t w ∧ ev w (fun uu : Fin N => decide (uu = v)) = true) ∨ (¬ Dm t w ∧ v ∉ L i0 ∧ ev w (fun uu : Fin N => decide (uu = v)) = true))) →
    ∀ t : Fin N,
    (∀ (w : ℕ) (v : Fin N), Dm t w → ev w (fun uu : Fin N => decide (uu = v)) = true → v ∈ L t) ∧
    (∀ (w : ℕ) (v : Fin N), Sm t w → v ∉ L i0 → ev w (fun uu : Fin N => decide (uu = v)) = true → v ∈ L t) ∧
    (∀ g : Fin gates.length, (gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.or → (Sm t (N + (g : ℕ)) → ∀ e ∈ (gates.get g).inputs, Sm t e) ∧ (Dm t (N + (g : ℕ)) → ∀ e ∈ (gates.get g).inputs, Dm t e)) ∧
    (∀ g : Fin gates.length, (gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.and → Sm t (N + (g : ℕ)) → ∃ e ∈ (gates.get g).inputs, Sm t e) ∧
    (∀ (w : ℕ) (v : Fin N), Sm t w → Vs t w v → v ∈ L t) := by
  intro q N L i0 p0 p1 _ _ _ _ _ _ _ _
  intro gates o j h hgates hread hnot huniq hlt hhead _
  intro ev hev _ _ _ hA Sm Dm hSm hDm Vs hVs t
  let C : Circuit := ⟨gates,0⟩
  have he : ev = fun w x => value C x w := by
    funext w x
    exact hev w x
  subst ev
  have ops (i : Fin C.gates.length) (hi : i ≠ j) :
      (C.gates.get i).op = .and ∨ (C.gates.get i).op = .or := by
    rcases (hgates (gates.get i) (List.get_mem gates i)).1 with ha | hb | hn
    · exact Or.inl ha
    · exact Or.inr hb
    · exact False.elim (hi (huniq i hn))
  have oneSound (w : ℕ) (v : Fin N) (hw : Sm t w) (hv : v ∉ L i0)
      (hs : value C (fun p => decide (p=v)) w = true) : v ∈ L t := by
    obtain ⟨p,hp,hpv⟩ := (hSm t w).1 hw (fun p => decide (p=v))
      (fun p hp => (of_decide_eq_true hp).symm ▸ hv) hs
    exact (of_decide_eq_true hpv) ▸ hp
  have dSound (w : ℕ) (v : Fin N) (hw : Dm t w)
      (hv : value C (fun p => decide (p=v)) w = true) : v ∈ L t := by
    have hh := (hDm t w).1 hw
    by_cases hv0 : v ∈ L i0
    · exact hh.2 v hv0 hv
    · exact oneSound w v hh.1 hv0 hv
  have orCarry (g : Fin gates.length) (hop : (gates.get g).op = .or)
      (e : ℕ) (he : e ∈ (gates.get g).inputs) (x : Fin N → Bool)
      (hx : value C x e = true) : value C x (N+(g:ℕ)) = true :=
    (or_value C g g.isLt hop x).2 ⟨e,he,hread g e he,hx⟩
  have orSm (g : Fin gates.length) (hop : (gates.get g).op = .or)
      (hg : Sm t (N+(g:ℕ))) (e : ℕ) (he : e ∈ (gates.get g).inputs) : Sm t e := by
    apply (hSm t e).2
    intro x hx hval
    exact (hSm t _).1 hg x hx (orCarry g hop e he x hval)
  let bad : Fin N → Bool := fun v => decide (v ∉ L i0 ∧ v ∉ L t)
  have badOff : avoids (L i0) bad := fun v h => (of_decide_eq_true h).1
  have belowOfFalse (w : ℕ) (hf : value C bad w = false) : Sm t w := by
    apply (hSm t w).2
    intro x hx hxw
    by_contra hbad
    have hdom (v : Fin N) (hv : x v = true) : bad v = true :=
      decide_eq_true ⟨hx v hv, fun hn => hbad ⟨v,hn,hv⟩⟩
    have hh := monotoneOff C j h ops hnot hlt hhead (L i0) hA x bad badOff hdom w hxw
    rw [hf] at hh
    cases hh
  refine ⟨dSound, oneSound, ?_, ?_, ?_⟩
  · intro g hop
    refine ⟨orSm g hop,?_⟩
    intro hg e he
    have hg' := (hDm t _).1 hg
    exact (hDm t e).2
      ⟨orSm g hop hg'.1 e he, fun p hp hv => hg'.2 p hp (orCarry g hop e he _ hv)⟩
  · intro g hop hsound
    by_contra hne
    have hvals (w : ℕ) (hw : w ∈ (gates.get g).inputs) : value C bad w = true := by
      cases hv : value C bad w
      · exact False.elim (hne ⟨w,hw,belowOfFalse w hv⟩)
      · rfl
    have hall : value C bad (N+(g:ℕ)) = true :=
      (and_value C g g.isLt hop bad).2 (fun w hw => ⟨hread g w hw,hvals w hw⟩)
    obtain ⟨v,hv,hb⟩ := (hSm t _).1 hsound bad badOff hall
    exact (of_decide_eq_true hb).2 hv
  · intro w v hw hv
    rcases (hVs t w v).1 hv with ⟨hd,ht⟩ | ⟨_,hn,ht⟩
    · exact dSound w v hd ht
    · exact oneSound w v hw hn ht
