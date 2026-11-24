import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2920_Aux

open PEqualNP.CircuitLowerBounds

def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem run_nil (w : List Bool) : run [] w = w := rfl

theorem run_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    run (g :: gs) w = run gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

theorem run_append (gs gs' : List Gate) (w : List Bool) :
    run (gs ++ gs') w = run gs' (run gs w) := by
  unfold run; rw [List.foldl_append]

theorem run_length : ∀ (gs : List Gate) (w : List Bool), (run gs w).length = w.length + gs.length := by
  intro gs
  induction gs with
  | nil => intro w; simp [run_nil]
  | cons g gs ih =>
    intro w
    rw [run_cons, ih]
    simp
    omega

theorem run_getD : ∀ (gs : List Gate) (w : List Bool) (i : ℕ), i < w.length →
    (run gs w).getD i false = w.getD i false := by
  intro gs
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i h
    rw [run_cons, ih _ _ (by simp only [List.length_append, List.length_singleton]; omega),
      List.getD_append _ _ _ _ h]

theorem run_take_succ (gs : List Gate) (w : List Bool) (k : ℕ) (g : Gate) (hk : gs[k]? = some g) :
    run (gs.take (k + 1)) w
      = run (gs.take k) w ++ [g.op.eval (g.inputs.map fun i => (run (gs.take k) w).getD i false)] := by
  rw [List.take_succ, hk, run_append]
  rfl

theorem run_take_length (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k ≤ gs.length) :
    (run (gs.take k) w).length = w.length + k := by
  rw [run_length, List.length_take]
  omega

theorem run_take_prefix (gs : List Gate) (w : List Bool) (k : ℕ) :
    ∀ d : ℕ, k + d ≤ gs.length → ∃ t, run (gs.take (k + d)) w = run (gs.take k) w ++ t := by
  intro d
  induction d with
  | zero => intro _; exact ⟨[], by simp⟩
  | succ d ih =>
    intro h
    obtain ⟨t, ht⟩ := ih (by omega)
    have hk : gs[k + d]? = some gs[k + d] := by
      rw [List.getElem?_eq_getElem (by omega)]
    refine ⟨t ++ [gs[k + d].op.eval (gs[k + d].inputs.map fun i =>
      (run (gs.take (k + d)) w).getD i false)], ?_⟩
    rw [← Nat.add_assoc, run_take_succ gs w (k + d) _ hk, ht, List.append_assoc]

theorem run_take_mono (gs : List Gate) (w : List Bool) (k k' : ℕ) (hk : k ≤ k')
    (hk' : k' ≤ gs.length) (p : ℕ) (hp : p < w.length + k) :
    (run (gs.take k') w).getD p false = (run (gs.take k) w).getD p false := by
  obtain ⟨t, ht⟩ := run_take_prefix gs w k (k' - k) (by omega)
  have : k + (k' - k) = k' := by omega
  rw [this] at ht
  rw [ht, List.getD_append _ _ _ _ (by rw [run_take_length gs w k (by omega)]; exact hp)]

theorem getD_new (l : List Bool) (v : Bool) : (l ++ [v]).getD l.length false = v := by
  simp


abbrev W (G : List Gate) (x : List Bool) (k : ℕ) : List Bool := run (G.take k) x

theorem lt_of_some {gs : List Gate} {k : ℕ} {g : Gate} (h : gs[k]? = some g) : k < gs.length :=
  (List.getElem?_eq_some_iff.mp h).1

theorem W_len (G : List Gate) (x : List Bool) (k : ℕ) (hk : k ≤ G.length) :
    (W G x k).length = x.length + k := run_take_length G x k hk

theorem W_succ (G : List Gate) (x : List Bool) (k : ℕ) (g : Gate) (hk : G[k]? = some g) :
    W G x (k + 1) = W G x k ++ [g.op.eval (g.inputs.map fun i => (W G x k).getD i false)] :=
  run_take_succ G x k g hk

theorem W_val (n : ℕ) (G : List Gate) (x : List Bool) (hx : x.length = n) (m : ℕ) (g : Gate)
    (hm : G[m]? = some g) :
    (W G x (m + 1)).getD (n + m) false
      = g.op.eval (g.inputs.map fun i => (W G x m).getD i false) := by
  have hlt := lt_of_some hm
  rw [W_succ G x m g hm]
  have h : n + m = (W G x m).length := by rw [W_len G x m (by omega)]; omega
  rw [h, getD_new]

theorem W_mono (G : List Gate) (x : List Bool) (k k' : ℕ) (hk : k ≤ k') (hk' : k' ≤ G.length)
    (p : ℕ) (hp : p < x.length + k) : (W G x k').getD p false = (W G x k).getD p false :=
  run_take_mono G x k k' hk hk' p hp

theorem eval_and2 (x y : Bool) : GateOp.eval GateOp.and [x, y] = (x && y) := by
  simp [GateOp.eval]

theorem eval_or2 (x y : Bool) : GateOp.eval GateOp.or [x, y] = (x || y) := by
  simp [GateOp.eval]

theorem jstep (n : ℕ) (G G' : List Gate) (x : List Bool) (hx : x.length = n)
    (iv iw j is a b c z : ℕ) (op1 op2 : GateOp)
    (hops : (op1 = GateOp.and ∧ op2 = GateOp.or) ∨ (op1 = GateOp.or ∧ op2 = GateOp.and))
    (hIs : G[is]? = some { op := op2, inputs := [a, b] })
    (hIv : G[iv]? = some { op := op2, inputs := [a, c] })
    (hIw : G[iw]? = some { op := op1, inputs := [n + iv, z] })
    (hJ : G[j]? = some { op := op1, inputs := [n + is, n + iw] } ∨
      G[j]? = some { op := op1, inputs := [n + iw, n + is] })
    (hIv' : G'[iv]? = some { op := op1, inputs := [b, c] })
    (hIw' : G'[iw]? = some { op := op2, inputs := [a, n + iv] })
    (hJ' : G'[j]? = some { op := op1, inputs := [n + iw, z] })
    (hisj : is < j) (hviw : iv < iw) (hiwj : iw < j)
    (ha1 : a < n + is) (hb1 : b < n + is) (ha2 : a < n + iv) (hb2 : b < n + iv)
    (hc2 : c < n + iv) (hz : z < n + iw) (hzv : z ≠ n + iv)
    (hLG : G.length = G'.length) (hjL : j < G.length)
    (hagree : ∀ p, p ≠ n + iv → p ≠ n + iw → (W G' x j).getD p false = (W G x j).getD p false) :
    (W G' x (j + 1)).getD (n + j) false = (W G x (j + 1)).getD (n + j) false := by
  have hxj : ∀ m, m ≤ j → x.length + m = n + m := fun m _ => by omega
  -- values of the original wires
  have hvIs : (W G x j).getD (n + is) false
      = op2.eval [(W G x j).getD a false, (W G x j).getD b false] := by
    rw [W_mono G x (is + 1) j (by omega) (by omega) (n + is) (by omega), W_val n G x hx is _ hIs]
    simp only [List.map_cons, List.map_nil]
    rw [W_mono G x is j (by omega) (by omega) a (by omega),
      W_mono G x is j (by omega) (by omega) b (by omega)]
  have hvIv : (W G x j).getD (n + iv) false
      = op2.eval [(W G x j).getD a false, (W G x j).getD c false] := by
    rw [W_mono G x (iv + 1) j (by omega) (by omega) (n + iv) (by omega), W_val n G x hx iv _ hIv]
    simp only [List.map_cons, List.map_nil]
    rw [W_mono G x iv j (by omega) (by omega) a (by omega),
      W_mono G x iv j (by omega) (by omega) c (by omega)]
  have hvIw : (W G x j).getD (n + iw) false
      = op1.eval [(W G x j).getD (n + iv) false, (W G x j).getD z false] := by
    rw [W_mono G x (iw + 1) j (by omega) (by omega) (n + iw) (by omega), W_val n G x hx iw _ hIw]
    simp only [List.map_cons, List.map_nil]
    rw [W_mono G x iw j (by omega) (by omega) (n + iv) (by omega),
      W_mono G x iw j (by omega) (by omega) z (by omega)]
  -- values of the rewritten wires
  have hvIv' : (W G' x j).getD (n + iv) false
      = op1.eval [(W G' x j).getD b false, (W G' x j).getD c false] := by
    rw [W_mono G' x (iv + 1) j (by omega) (by omega) (n + iv) (by omega), W_val n G' x hx iv _ hIv']
    simp only [List.map_cons, List.map_nil]
    rw [W_mono G' x iv j (by omega) (by omega) b (by omega),
      W_mono G' x iv j (by omega) (by omega) c (by omega)]
  have hvIw' : (W G' x j).getD (n + iw) false
      = op2.eval [(W G' x j).getD a false, (W G' x j).getD (n + iv) false] := by
    rw [W_mono G' x (iw + 1) j (by omega) (by omega) (n + iw) (by omega), W_val n G' x hx iw _ hIw']
    simp only [List.map_cons, List.map_nil]
    rw [W_mono G' x iw j (by omega) (by omega) a (by omega),
      W_mono G' x iw j (by omega) (by omega) (n + iv) (by omega)]
  -- agreement on the inputs a b c z
  have hna : a ≠ n + iv := by omega
  have hnb : b ≠ n + iv := by omega
  have hnc : c ≠ n + iv := by omega
  have hna' : a ≠ n + iw := by omega
  have hnb' : b ≠ n + iw := by omega
  have hnc' : c ≠ n + iw := by omega
  have hzw : z ≠ n + iw := by omega
  have eA := hagree a hna hna'
  have eB := hagree b hnb hnb'
  have eC := hagree c hnc hnc'
  have eZ := hagree z hzv hzw
  rw [W_val n G' x hx j _ hJ']
  simp only [List.map_cons, List.map_nil]
  rw [hvIw', hvIv', eA, eB, eC, eZ]
  rcases hJ with hJ | hJ
  · rw [W_val n G x hx j _ hJ]
    simp only [List.map_cons, List.map_nil]
    rw [hvIs, hvIw, hvIv]
    rcases hops with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · generalize (W G x j).getD a false = va
      generalize (W G x j).getD b false = vb
      generalize (W G x j).getD c false = vc
      generalize (W G x j).getD z false = vz
      cases va <;> cases vb <;> cases vc <;> cases vz <;> simp [GateOp.eval]
  · rw [W_val n G x hx j _ hJ]
    simp only [List.map_cons, List.map_nil]
    rw [hvIs, hvIw, hvIv]
    rcases hops with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · generalize (W G x j).getD a false = va
      generalize (W G x j).getD b false = vb
      generalize (W G x j).getD c false = vc
      generalize (W G x j).getD z false = vz
      cases va <;> cases vb <;> cases vc <;> cases vz <;> simp [GateOp.eval]


theorem getD_at_len (l l' : List Bool) (v : Bool) (h : l.length = l'.length) :
    (l ++ [v]).getD l'.length false = v := by
  rw [← h]; exact getD_new l v

theorem inv_all (n : ℕ) (G G' : List Gate) (x : List Bool) (hx : x.length = n) (iv iw j : ℕ)
    (hLG : G.length = G'.length)
    (hsame : ∀ k, k ≠ iv → k ≠ iw → k ≠ j → G'[k]? = G[k]?)
    (hno1 : ∀ (k : ℕ) (g : Gate), G[k]? = some g → k ≠ iw → n + iv ∉ g.inputs)
    (hno2 : ∀ (k : ℕ) (g : Gate), G[k]? = some g → k ≠ j → n + iw ∉ g.inputs)
    (hjfun : (∀ p, p ≠ n + iv → p ≠ n + iw →
        (W G' x j).getD p false = (W G x j).getD p false) →
      (W G' x (j + 1)).getD (n + j) false = (W G x (j + 1)).getD (n + j) false) :
    ∀ k, k ≤ G.length → (W G' x k).length = x.length + k ∧ (W G x k).length = x.length + k ∧
      ∀ p, p ≠ n + iv → p ≠ n + iw → (W G' x k).getD p false = (W G x k).getD p false := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨by simp [W, run_nil], by simp [W, run_nil], ?_⟩
    intro p _ _
    simp [W, run_nil]
  | succ k ih =>
    intro hk
    obtain ⟨h1, h2, h3⟩ := ih (by omega)
    have hgk : G[k]? = some G[k] := List.getElem?_eq_getElem (by omega)
    have hgk' : G'[k]? = some G'[k] := List.getElem?_eq_getElem (by omega)
    have hlen1 : (W G' x (k + 1)).length = x.length + (k + 1) := W_len G' x (k + 1) (by omega)
    have hlen2 : (W G x (k + 1)).length = x.length + (k + 1) := W_len G x (k + 1) (by omega)
    have hnew : k ≠ iv → k ≠ iw →
        (W G' x (k + 1)).getD (n + k) false = (W G x (k + 1)).getD (n + k) false := by
      intro hkv hkw
      by_cases hkj : k = j
      · subst hkj
        exact hjfun h3
      · have hg' : G'[k]? = some G[k] := by rw [hsame k hkv hkw hkj]; exact hgk
        rw [W_val n G x hx k _ hgk, W_val n G' x hx k _ hg']
        congr 1
        apply List.map_congr_left
        intro i hi
        apply h3
        · intro h; exact hno1 k _ hgk hkw (h ▸ hi)
        · intro h; exact hno2 k _ hgk hkj (h ▸ hi)
    refine ⟨hlen1, hlen2, ?_⟩
    intro p hp1 hp2
    by_cases hlt : p < x.length + k
    · rw [W_mono G' x k (k + 1) (by omega) (by omega) p hlt,
        W_mono G x k (k + 1) (by omega) (by omega) p hlt]
      exact h3 p hp1 hp2
    · by_cases hpe : p = x.length + k
      · have hpn : p = n + k := by omega
        rw [hpn]
        apply hnew
        · intro h; apply hp1; omega
        · intro h; apply hp2; omega
      · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]

end PEqualNP.Outside.L_meta_2920_Aux

theorem PEqualNP.Outside.L_meta_2920 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (j is iv iw a b c z : ℕ)
    (op1 op2 : PEqualNP.CircuitLowerBounds.GateOp),
  ((op1 = PEqualNP.CircuitLowerBounds.GateOp.and ∧ op2 = PEqualNP.CircuitLowerBounds.GateOp.or) ∨
    (op1 = PEqualNP.CircuitLowerBounds.GateOp.or ∧ op2 = PEqualNP.CircuitLowerBounds.GateOp.and)) →
  C.gates[is]? = some { op := op2, inputs := [a, b] } →
  C.gates[iv]? = some { op := op2, inputs := [a, c] } →
  C.gates[iw]? = some { op := op1, inputs := [n + iv, z] } →
  (C.gates[j]? = some { op := op1, inputs := [n + is, n + iw] } ∨
    C.gates[j]? = some { op := op1, inputs := [n + iw, n + is] }) →
  is < j → iv < iw → iw < j →
  a < n + is → b < n + is → a < n + iv → b < n + iv → c < n + iv →
  z < n + iw → z ≠ n + iv →
  (∀ (k : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[k]? = some g → k ≠ iw → n + iv ∉ g.inputs) →
  (∀ (k : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[k]? = some g → k ≠ j → n + iw ∉ g.inputs) →
  C.output ≠ n + iv → C.output ≠ n + iw →
  PEqualNP.MetaComplexity.circuitFun n
      { gates := ((C.gates.set iv { op := op1, inputs := [b, c] }).set iw
            { op := op2, inputs := [a, n + iv] }).set j { op := op1, inputs := [n + iw, z] },
        output := C.output } =
    PEqualNP.MetaComplexity.circuitFun n C ∧
  (((C.gates.set iv { op := op1, inputs := [b, c] }).set iw
      { op := op2, inputs := [a, n + iv] }).set j { op := op1, inputs := [n + iw, z] }).length =
    C.gates.length := by
  intro n C j is iv iw a b c z op1 op2 hops hIs hIv hIw hJ hisj hviw hiwj ha1 hb1 ha2 hb2 hc2 hz
    hzv hno1 hno2 hout1 hout2
  have hjL : j < C.gates.length := by
    rcases hJ with h | h <;> exact PEqualNP.Outside.L_meta_2920_Aux.lt_of_some h
  have hvL : iv < C.gates.length := PEqualNP.Outside.L_meta_2920_Aux.lt_of_some hIv
  have hwL : iw < C.gates.length := PEqualNP.Outside.L_meta_2920_Aux.lt_of_some hIw
  have hget : ∀ k, (((C.gates.set iv ⟨op1, [b, c]⟩).set iw ⟨op2, [a, n + iv]⟩).set j
      ⟨op1, [n + iw, z]⟩)[k]? = if k = j then some ⟨op1, [n + iw, z]⟩ else
        if k = iw then some ⟨op2, [a, n + iv]⟩ else
          if k = iv then some ⟨op1, [b, c]⟩ else C.gates[k]? := by
    intro k
    by_cases h1 : k = j
    · subst h1
      simp [hjL]
    · by_cases h2 : k = iw
      · subst h2
        simp [h1, hwL, Ne.symm h1]
      · by_cases h3 : k = iv
        · subst h3
          simp [h1, h2, hvL, Ne.symm h1, Ne.symm h2]
        · simp [h1, h2, h3, Ne.symm h1, Ne.symm h2, Ne.symm h3]
  have hLG : C.gates.length = (((C.gates.set iv ⟨op1, [b, c]⟩).set iw ⟨op2, [a, n + iv]⟩).set j
      ⟨op1, [n + iw, z]⟩).length := by simp
  have hsame : ∀ k, k ≠ iv → k ≠ iw → k ≠ j →
      (((C.gates.set iv ⟨op1, [b, c]⟩).set iw ⟨op2, [a, n + iv]⟩).set j
        ⟨op1, [n + iw, z]⟩)[k]? = C.gates[k]? := by
    intro k hkv hkw hkj
    rw [hget k]; simp [hkj, hkw, hkv]
  have hJ' : (((C.gates.set iv ⟨op1, [b, c]⟩).set iw ⟨op2, [a, n + iv]⟩).set j
      ⟨op1, [n + iw, z]⟩)[j]? = some ⟨op1, [n + iw, z]⟩ := by
    rw [hget j]; simp
  have hIw' : (((C.gates.set iv ⟨op1, [b, c]⟩).set iw ⟨op2, [a, n + iv]⟩).set j
      ⟨op1, [n + iw, z]⟩)[iw]? = some ⟨op2, [a, n + iv]⟩ := by
    rw [hget iw]; simp [Nat.ne_of_lt hiwj]
  have hIv' : (((C.gates.set iv ⟨op1, [b, c]⟩).set iw ⟨op2, [a, n + iv]⟩).set j
      ⟨op1, [n + iw, z]⟩)[iv]? = some ⟨op1, [b, c]⟩ := by
    rw [hget iv]; simp [Nat.ne_of_lt (Nat.lt_trans hviw hiwj), Nat.ne_of_lt hviw]
  refine ⟨?_, by simp⟩
  funext xs
  have hx : (List.ofFn xs).length = n := by simp
  have hinv := PEqualNP.Outside.L_meta_2920_Aux.inv_all n C.gates
    (((C.gates.set iv ⟨op1, [b, c]⟩).set iw ⟨op2, [a, n + iv]⟩).set j ⟨op1, [n + iw, z]⟩)
    (List.ofFn xs) hx iv iw j hLG hsame hno1 hno2
    (fun hag => 
      PEqualNP.Outside.L_meta_2920_Aux.jstep n C.gates _ (List.ofFn xs) hx iv iw j is a b c z op1 op2 hops hIs hIv hIw hJ
      hIv' hIw' hJ' hisj hviw hiwj ha1 hb1 ha2 hb2 hc2 hz hzv hLG hjL hag)
  have hfin := (hinv C.gates.length le_rfl).2.2 C.output hout1 hout2
  simp only [PEqualNP.MetaComplexity.circuitFun, PEqualNP.CircuitLowerBounds.Circuit.eval,
    PEqualNP.CircuitLowerBounds.Circuit.wires]
  have hT : (((C.gates.set iv ⟨op1, [b, c]⟩).set iw ⟨op2, [a, n + iv]⟩).set j
      ⟨op1, [n + iw, z]⟩).take C.gates.length = (((C.gates.set iv ⟨op1, [b, c]⟩).set iw
      ⟨op2, [a, n + iv]⟩).set j ⟨op1, [n + iw, z]⟩) := by
    rw [hLG]; exact List.take_length
  have hT2 : C.gates.take C.gates.length = C.gates := List.take_length
  simp only [PEqualNP.Outside.L_meta_2920_Aux.W, PEqualNP.Outside.L_meta_2920_Aux.run, hT, hT2] at hfin
  exact hfin
