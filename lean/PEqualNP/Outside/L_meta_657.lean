import PEqualNP.Defs
import PEqualNP.MetaComplexity.L532

namespace PEqualNP.Outside.LM657

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.Readers PEqualNP.MetaComplexity.EdgeFn

def NCy {N : ℕ} (F : (Fin N → Bool) → Bool) (y : Fin N) : Prop :=
  ∀ b : Bool, ∃ x x' : Fin N → Bool, F (Function.update x y b) ≠ F (Function.update x' y b)

section Circ

variable {n : ℕ} {F : (Fin (n + 1) → Bool) → Bool} {D : Finset (Fin (n + 1))} {gs : List Gate}
  {o : ℕ}

theorem nlit (hnc : ∀ y ∈ D, NCy F y) {y : Fin (n + 1)} (hy : y ∈ D) (c : Bool) :
    ¬ ∀ u, F u = xor (u y) c := by
  intro h
  obtain ⟨x, x', hx⟩ := hnc y hy false
  apply hx
  rw [h, h]
  simp

theorem fnc (hnc : ∀ y ∈ D, NCy F y) {y : Fin (n + 1)} (hy : y ∈ D) :
    ∃ x x' : Fin (n + 1) → Bool, F x ≠ F x' := by
  obtain ⟨x, x', hx⟩ := hnc y hy false
  exact ⟨_, _, hx⟩

theorem dep_supp (L : Least (n + 1) F gs o) {y : Fin (n + 1)} (hd : Dep F y) :
    y ∈ (suppsFrom gs (inputSupps (n + 1))).getD o ∅ := by
  obtain ⟨x, hx⟩ := hd
  by_contra hno
  have hag := (agree_wiresFrom (Function.update x y (!x y)) x gs _ _ _
    (agree_inputs _ _)).2.2 o (by
      intro k hk
      have : k ≠ y := fun e => hno (e ▸ hk)
      simp [Function.update_of_ne this])
  apply hx
  rw [← L.hev, ← L.hev]
  exact hag

theorem out_ne (hnc : ∀ y ∈ D, NCy F y) (L : Least (n + 1) F gs o) (p : ℕ) (g : Gate)
    (hg : gs[p]? = some g) (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (l : ℕ)
    (hl : l ∈ g.inputs) {y : Fin (n + 1)} (hy : y ∈ D) (c : Bool)
    (hv : ∀ u, vl gs u l = xor (u y) c) : o ≠ n + 1 + p := by
  intro e
  obtain ⟨x, x', hx⟩ := hnc y hy (xor (fixBit g) c)
  have hc : ∀ z : Fin (n + 1) → Bool, F (Function.update z y (xor (fixBit g) c)) = fixBit g := by
    intro z
    rw [← L.hev, e]
    refine vl_abs gs L.hcl _ p g hg hop l hl ?_
    rw [hv]
    simp
  exact hx (by rw [hc, hc])

theorem two (hnc : ∀ y ∈ D, NCy F y) (hnf : ∀ y ∈ D, ∀ y' ∈ D, y ≠ y' → ¬ PairFunnel F y y')
    (L : Least (n + 1) F gs o) (OR : OneReader D gs) (p : ℕ)
    (g : Gate) (hg : gs[p]? = some g) (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (j k : ℕ)
    (hin : g.inputs = [j, k]) (hj : j < n + 1 + p) (hk : k < n + 1 + p)
    (yj : Fin (n + 1)) (hyj : yj ∈ D) (cj : Bool) (hvj : ∀ u, vl gs u j = xor (u yj) cj)
    (hsj : j = yj ∨ ∃ pn, pn < p ∧ j = n + 1 + pn ∧ gs[pn]? = some ⟨GateOp.not, [(yj : ℕ)]⟩)
    (yk : Fin (n + 1)) (hyk : yk ∈ D) (ck : Bool) (hvk : ∀ u, vl gs u k = xor (u yk) ck)
    (hsk : k = yk ∨ ∃ pn, pn < p ∧ k = n + 1 + pn ∧ gs[pn]? = some ⟨GateOp.not, [(yk : ℕ)]⟩) :
    False := by
  have hfnc := fnc hnc hyj
  have htl : p < gs.length := (List.getElem?_eq_some_iff.1 hg).1
  have hRj : Reads gs p j := ⟨g, hg, by rw [hin]; simp⟩
  have hRk : Reads gs p k := ⟨g, hg, by rw [hin]; simp⟩
  have hopnd : ∀ (w : ℕ) (v : Fin (n + 1)), v ∈ D → Reads gs p w →
      (w = v ∨ ∃ pn, pn < p ∧ w = n + 1 + pn ∧ gs[pn]? = some ⟨GateOp.not, [(v : ℕ)]⟩) →
      ∀ p' a, (a = (v : ℕ) ∨ a = w) → Reads gs p' a → n + 1 + p' ≠ w → p' = p := by
    intro w v hv hw hs p' a ha hr hne
    rcases hs with e | ⟨r, _, er, hg'⟩
    · have ha' : a = v := by
        rcases ha with ha | ha
        · exact ha
        · rw [ha, e]
      rw [ha'] at hr
      exact OR.1 v hv p' p hr (by rw [← e]; exact hw)
    · have hrv : Reads gs r v := ⟨_, hg', by simp⟩
      rcases ha with ha | ha
      · rw [ha] at hr
        have := OR.1 v hv p' r hr hrv
        exact (hne (by rw [this, er])).elim
      · rw [ha, er] at hr
        rw [er] at hw
        exact OR.2 v hv r hg' p' p hr hw
  have hvjk : yj ≠ yk := by
    intro e
    have hjk : j ≠ k := by
      intro e'
      subst e'
      exact L.no_alias hfnc p htl j hj (fun u => by
        rw [vl_gate gs L.hcl u p g hg, hin]
        rcases hop with h | h <;> rw [h] <;> simp [GateOp.eval])
    rcases hsj with ej | ⟨r1, hr1, ej, hg1⟩ <;> rcases hsk with ek | ⟨r2, hr2, ek, hg2⟩
    · exact hjk (by rw [ej, ek, e])
    · have := OR.1 yj hyj p r2 (by rw [← ej]; exact hRj) ⟨_, hg2, by rw [← e]; simp⟩
      omega
    · have := OR.1 yk hyk p r1 (by rw [← ek]; exact hRk) ⟨_, hg1, by rw [e]; simp⟩
      omega
    · have := OR.1 yj hyj r1 r2 ⟨_, hg1, by simp⟩ ⟨_, hg2, by rw [← e]; simp⟩
      exact hjk (by rw [ej, ek, this])
  have KC : ∀ u u' : Fin (n + 1) → Bool, (∀ i, i ≠ yj → i ≠ yk → u i = u' i) →
      vl gs u (n + 1 + p) = vl gs u' (n + 1 + p) → F u = F u' := by
    intro u u' hagr hgv
    rw [← L.hev, ← L.hev]
    refine agree_B gs L.hcl u u' (fun a => a = (yj : ℕ) ∨ a = (yk : ℕ) ∨ a = j ∨ a = k) (o + 1)
      ?_ ?_ o (by omega) ?_
    · intro a ha hBa
      have hBa' : ¬ (a = (yj : ℕ) ∨ a = (yk : ℕ) ∨ a = j ∨ a = k) := hBa
      rw [vl_input gs u a ha, vl_input gs u' a ha]
      apply hagr
      · intro e
        exact hBa' (Or.inl (congrArg Fin.val e))
      · intro e
        exact hBa' (Or.inr (Or.inl (congrArg Fin.val e)))
    · intro p' g' hp' _ hB' hr _
      have hB'' : ¬ (n + 1 + p' = (yj : ℕ) ∨ n + 1 + p' = (yk : ℕ) ∨ n + 1 + p' = j ∨
          n + 1 + p' = k) := hB'
      obtain ⟨a, ha, hBa⟩ := hr
      have hBa' : a = (yj : ℕ) ∨ a = (yk : ℕ) ∨ a = j ∨ a = k := hBa
      have hR : Reads gs p' a := ⟨g', hp', ha⟩
      have hpt : p' = p := by
        rcases hBa' with e | e | e | e
        · exact hopnd j yj hyj hRj hsj p' a (Or.inl e) hR
            (fun e' => hB'' (Or.inr (Or.inr (Or.inl e'))))
        · exact hopnd k yk hyk hRk hsk p' a (Or.inl e) hR
            (fun e' => hB'' (Or.inr (Or.inr (Or.inr e'))))
        · exact hopnd j yj hyj hRj hsj p' a (Or.inr e) hR
            (fun e' => hB'' (Or.inr (Or.inr (Or.inl e'))))
        · exact hopnd k yk hyk hRk hsk p' a (Or.inr e) hR
            (fun e' => hB'' (Or.inr (Or.inr (Or.inr e'))))
      rw [hpt]
      exact hgv
    · intro hB
      have hB' : o = (yj : ℕ) ∨ o = (yk : ℕ) ∨ o = j ∨ o = k := hB
      rcases hB' with e | e | e | e
      · exact nlit hnc hyj false (fun x => by
          rw [← L.hev, e, vl_input gs x yj yj.isLt]; simp)
      · exact nlit hnc hyk false (fun x => by
          rw [← L.hev, e, vl_input gs x yk yk.isLt]; simp)
      · exact nlit hnc hyj cj (fun x => by rw [← L.hev, e, hvj])
      · exact nlit hnc hyk ck (fun x => by rw [← L.hev, e, hvk])
  have hag : ∀ (x : Fin (n + 1) → Bool) (a b a' b' : Bool), ∀ i, i ≠ yj → i ≠ yk →
      set2 x yj a yk b i = set2 x yj a' yk b' i := by
    intro x a b a' b' i e1 e2
    rw [set2_o x yj yk a b i e1 e2, set2_o x yj yk a' b' i e1 e2]
  have hval : ∀ (x : Fin (n + 1) → Bool) (a b : Bool),
      vl gs (set2 x yj a yk b) (n + 1 + p) = g.op.eval [xor a cj, xor b ck] := by
    intro x a b
    rw [vl_gate gs L.hcl _ p g hg, hin]
    simp only [List.map_cons, List.map_nil]
    rw [hvj, hvk, set2_p x hvjk, set2_q x]
  apply hnf yj hyj yk hyk hvjk
  rcases hop with hop | hop
  · refine ⟨!cj, !ck, fun x => ⟨KC _ _ (hag x _ _ _ _) ?_, KC _ _ (hag x _ _ _ _) ?_⟩⟩ <;>
      rw [hval, hval, hop] <;> cases cj <;> cases ck <;> rfl
  · refine ⟨cj, ck, fun x => ⟨KC _ _ (hag x _ _ _ _) ?_, KC _ _ (hag x _ _ _ _) ?_⟩⟩ <;>
      rw [hval, hval, hop] <;> cases cj <;> cases ck <;> rfl

theorem front (hnc : ∀ y ∈ D, NCy F y)
    (hnf : ∀ y ∈ D, ∀ y' ∈ D, y ≠ y' → ¬ PairFunnel F y y')
    (hdep : ∀ y ∈ D, Dep F y) (hD : D.Nonempty) (L : Least (n + 1) F gs o)
    (OR : OneReader D gs) :
    ∃ (p : ℕ) (g : Gate) (y : Fin (n + 1)) (l h : ℕ), Front D gs p g y l h ∧
      o ≠ n + 1 + p := by
  classical
  obtain ⟨y0, hy0⟩ := hD
  have hfnc := fnc hnc hy0
  by_cases hex : ∃ p g, gs[p]? = some g ∧ (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      ∃ i ∈ D, i ∈ (suppsFrom gs (inputSupps (n + 1))).getD (n + 1 + p) ∅
  · obtain ⟨g, hg, hop, i, hi, his⟩ := Nat.find_spec hex
    set p := Nat.find hex with hpdef
    have hmin : ∀ r < p, ∀ g', gs[r]? = some g' → (g'.op = GateOp.and ∨ g'.op = GateOp.or) →
        ∀ i ∈ D, i ∉ (suppsFrom gs (inputSupps (n + 1))).getD (n + 1 + r) ∅ :=
      fun r hr g' hg' hop' i hi his => Nat.find_min hex hr ⟨g', hg', hop', i, hi, his⟩
    rcases L.hcl p g hg with ⟨hop2, _⟩ | ⟨_, j, k, hj, hk, hin⟩
    · rcases hop with h | h <;> rw [h] at hop2 <;> cases hop2
    obtain ⟨a, ha, hia⟩ := (front_supp_gate gs L.hcl p g hg i).1 his
    rw [hin] at ha
    have hlitof : ∀ (w : ℕ) (y : Fin (n + 1)),
        (w = y ∨ ∃ pn, pn < p ∧ w = n + 1 + pn ∧ gs[pn]? = some ⟨GateOp.not, [(y : ℕ)]⟩) →
        IsLit (n + 1) gs y w := by
      rintro w y (e | ⟨pn, _, e, hpn⟩)
      · exact Or.inl e
      · exact Or.inr ⟨pn, e, hpn⟩
    by_cases mj : ∃ i ∈ D, i ∈ (suppsFrom gs (inputSupps (n + 1))).getD j ∅ <;>
      by_cases mk : ∃ i ∈ D, i ∈ (suppsFrom gs (inputSupps (n + 1))).getD k ∅
    · exfalso
      obtain ⟨yj, hyj, cj, hvj, hsj⟩ := front_dlit L hfnc p hmin j hj mj
      obtain ⟨yk, hyk, ck, hvk, hsk⟩ := front_dlit L hfnc p hmin k hk mk
      exact two hnc hnf L OR p g hg hop j k hin hj hk yj hyj cj hvj hsj yk hyk ck hvk hsk
    · obtain ⟨y, hy, c, hv, hs⟩ := front_dlit L hfnc p hmin j hj mj
      refine ⟨p, g, y, j, k, ⟨hg, hop, Or.inl hin, hy, hlitof j y hs,
        fun y' hy' hm => mk ⟨y', hy', hm⟩⟩,
        out_ne hnc L p g hg hop j (by rw [hin]; simp) hy c hv⟩
    · obtain ⟨y, hy, c, hv, hs⟩ := front_dlit L hfnc p hmin k hk mk
      refine ⟨p, g, y, k, j, ⟨hg, hop, Or.inr hin, hy, hlitof k y hs,
        fun y' hy' hm => mj ⟨y', hy', hm⟩⟩,
        out_ne hnc L p g hg hop k (by rw [hin]; simp) hy c hv⟩
    · exfalso
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · exact mj ⟨i, hi, hia⟩
      · exact mk ⟨i, hi, hia⟩
  · exfalso
    have hmin : ∀ r < gs.length, ∀ g', gs[r]? = some g' →
        (g'.op = GateOp.and ∨ g'.op = GateOp.or) →
        ∀ i ∈ D, i ∉ (suppsFrom gs (inputSupps (n + 1))).getD (n + 1 + r) ∅ :=
      fun r _ g' hg' hop' i hi his => hex ⟨r, g', hg', hop', i, hi, his⟩
    by_cases hol : o < n + 1 + gs.length
    · obtain ⟨y, hy, c, hv, _⟩ := front_dlit L hfnc gs.length hmin o hol
        ⟨y0, hy0, dep_supp L (hdep y0 hy0)⟩
      exact nlit hnc hy c (fun u => by rw [← L.hev, hv])
    · obtain ⟨x, x', hxx⟩ := hfnc
      apply hxx
      rw [← L.hev, ← L.hev, vl_beyond gs x o (by omega), vl_beyond gs x' o (by omega)]

theorem via_one (L : Least (n + 1) F gs o) (i : Fin (n + 1)) (l p : ℕ)
    (hR : ∀ q a, (a = (i : ℕ) ∨ a = l) → Reads gs q a → n + 1 + q ≠ l → q = p)
    (ho1 : o ≠ i) (ho2 : o ≠ l)
    (u u' : Fin (n + 1) → Bool) (hagr : ∀ j, j ≠ i → u j = u' j)
    (hp : vl gs u (n + 1 + p) = vl gs u' (n + 1 + p)) : F u = F u' := by
  rw [← L.hev, ← L.hev]
  refine agree_B gs L.hcl u u' (fun a => a = (i : ℕ) ∨ a = l) (o + 1) ?_ ?_ o (by omega) ?_
  · intro a ha hBa
    rw [vl_input gs u a ha, vl_input gs u' a ha]
    apply hagr
    intro e
    exact hBa (Or.inl (congrArg Fin.val e))
  · intro q g' hq' _ hB' hr _
    obtain ⟨a, ha, hBa⟩ := hr
    have hq : q = p := hR q a hBa ⟨g', hq', ha⟩ (fun e => hB' (Or.inr e))
    subst hq
    exact hp
  · rintro (e | e)
    · exact ho1 e
    · exact ho2 e

theorem dfree_val (h : ℕ) (hD : DFree D gs h) (u u' : Fin (n + 1) → Bool)
    (hagr : ∀ j, j ∉ D → u j = u' j) : vl gs u h = vl gs u' h := by
  unfold vl
  exact (agree_wiresFrom u u' gs _ _ _ (agree_inputs _ _)).2.2 h
    (fun k hk => hagr k (fun hkD => hD k hkD hk))

end Circ

theorem orSwap_agree {N : ℕ} (gs : List Gate) (hcl : CleanL N gs) (p ph l : ℕ) (g : Gate)
    (y : Fin N) (hph : ph < gs.length) (hgp : gs[p]? = some g) (hop : g.op = GateOp.or)
    (hin : g.inputs = [l, N + ph] ∨ g.inputs = [N + ph, l]) (hlne : l ≠ N + ph)
    (hone : ∀ t, Reads gs t (N + ph) → t = p) (x : Fin N → Bool) (hlx : vl gs x l = true) :
    ∀ w, w ≠ N + ph → vl (andSwap gs ph y) x w = vl gs x w := by
  have hcl' := andSwap_clean gs ph y hcl hph
  have hlen := andSwap_length gs ph y
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hwk : w < N
    · rw [vl_input _ x w hwk, vl_input gs x w hwk]
    · obtain ⟨r, rfl⟩ : ∃ r, w = N + r := ⟨w - N, by omega⟩
      have hrp : r ≠ ph := fun e => hw (by rw [e])
      cases hr : gs[r]? with
      | none =>
        have hl : gs.length ≤ r := List.getElem?_eq_none_iff.1 hr
        rw [vl_beyond _ x _ (by omega), vl_beyond gs x _ (by omega)]
      | some g' =>
        have hr' : (andSwap gs ph y)[r]? = some g' := by
          rw [andSwap_get_ne gs ph y r hrp]; exact hr
        rw [vl_gate _ hcl' x r g' hr', vl_gate gs hcl x r g' hr]
        by_cases hrp' : r = p
        · subst hrp'
          rw [hgp] at hr
          cases hr
          have hllt : l < N + r := (hcl r g hgp).lt l (by rcases hin with h | h <;> simp [h])
          have hl' : vl (andSwap gs ph y) x l = true := by rw [ih l hllt hlne]; exact hlx
          rw [hop]
          rcases hin with h | h <;> rw [h] <;> simp [GateOp.eval, hl', hlx]
        · congr 1
          apply List.map_congr_left
          intro a ha
          have hlt := (hcl r g' hr).lt a ha
          exact ih a hlt (fun e => hrp' (hone r ⟨g', hr, e ▸ ha⟩))

theorem or_core (n : ℕ) (F : (Fin (n + 1) → Bool) → Bool) (gs : List Gate) (o p ph l : ℕ)
    (g : Gate) (y : Fin (n + 1)) (L : Least (n + 1) F gs o) (b : Bool)
    (hnc : ∃ x x' : Fin (n + 1) → Bool,
      F (Function.update x y b) ≠ F (Function.update x' y b))
    (hgp : gs[p]? = some g) (hop : g.op = GateOp.or)
    (hin : g.inputs = [l, n + 1 + ph] ∨ g.inputs = [n + 1 + ph, l]) (hlne : l ≠ n + 1 + ph)
    (hph : ph < gs.length) (hone : ∀ t, Reads gs t (n + 1 + ph) → t = p)
    (ho2 : o ≠ n + 1 + ph)
    (hlx : ∀ x : Fin (n + 1) → Bool, x y = b → vl gs x l = true)
    (S : Finset ℕ) (hS : ∀ q ∈ S, RC n (andSwap gs ph y) y b q) :
    Drop F y b S.card gs.length := by
  have hcl' := andSwap_clean gs ph y L.hcl hph
  have hag : ∀ x : Fin (n + 1) → Bool,
      vl (andSwap gs ph y) (Function.update x y b) o = F (Function.update x y b) := by
    intro x
    rw [orSwap_agree gs L.hcl p ph l g y hph hgp hop hin hlne hone _
      (hlx _ (andUpd_self x y b)) o ho2, L.hev]
  have hnc' : ∃ x x' : Fin (n + 1) → Bool,
      vl (andSwap gs ph y) (Function.update x y b) o
        ≠ vl (andSwap gs ph y) (Function.update x' y b) o := by
    obtain ⟨x, x', h⟩ := hnc
    exact ⟨x, x', by rw [hag, hag]; exact h⟩
  obtain ⟨s', hs', hc⟩ := save n (fun x => vl (andSwap gs ph y) x o) (andSwap gs ph y) o hcl'
    (fun _ => rfl) y b hnc' S hS
  refine ⟨s', by rw [andSwap_length] at hs'; exact hs', ?_⟩
  have e : (fun x : Fin (n + 1) → Bool => F (Function.update x y b))
      = fun x => (fun x => vl (andSwap gs ph y) x o) (Function.update x y b) := by
    funext x
    exact (hag x).symm
  rw [e]
  exact hc

theorem or_pay (n : ℕ) (F : (Fin (n + 1) → Bool) → Bool) (gs : List Gate) (o p ph : ℕ)
    (g : Gate) (y : Fin (n + 1)) (L : Least (n + 1) F gs o) (hnc : NCy F y)
    (hgp : gs[p]? = some g) (hop : g.op = GateOp.or)
    (hin : g.inputs = [(y : ℕ), n + 1 + ph] ∨ g.inputs = [n + 1 + ph, (y : ℕ)])
    (hph : ph < gs.length) (hone : ∀ t, Reads gs t (n + 1 + ph) → t = p)
    (ho1 : o ≠ n + 1 + p) (ho2 : o ≠ n + 1 + ph) : Drop F y true 3 gs.length := by
  have hfnc : ∃ x x' : Fin (n + 1) → Bool, F x ≠ F x' := by
    obtain ⟨x, x', h⟩ := hnc false
    exact ⟨_, _, h⟩
  have hlmem : (y : ℕ) ∈ g.inputs := by rcases hin with h | h <;> simp [h]
  have hhmem : n + 1 + ph ∈ g.inputs := by rcases hin with h | h <;> simp [h]
  have hp : p < gs.length := (List.getElem?_eq_some_iff.1 hgp).1
  have hphp : n + 1 + ph < n + 1 + p := (L.hcl p g hgp).lt _ hhmem
  have hlne : (y : ℕ) ≠ n + 1 + ph := by have := y.isLt; omega
  have hcl' := andSwap_clean gs ph y L.hcl hph
  have hgp' : (andSwap gs ph y)[p]? = some g := by
    rw [andSwap_get_ne gs ph y p (by omega)]; exact hgp
  obtain ⟨S, hpS, hSr⟩ := L.live hfnc p hp ho1
  have hSr' : Reads (andSwap gs ph y) S (n + 1 + p) := by
    obtain ⟨g', hg', hm⟩ := hSr
    exact ⟨g', by rw [andSwap_get_ne gs ph y S (by omega)]; exact hg', hm⟩
  have hphR : Reads (andSwap gs ph y) ph y := ⟨_, andSwap_get_eq gs ph y hph, by simp⟩
  have hpR : Reads (andSwap gs ph y) p y := ⟨g, hgp', hlmem⟩
  have hlx : ∀ x : Fin (n + 1) → Bool, x y = true → vl gs x y = true := by
    intro x hx
    rw [vl_input gs x y y.isLt]
    exact hx
  have hcp : IsC n (andSwap gs ph y) y true (n + 1 + p) :=
    isC_reader hcl' y p g hgp' hlmem true (Or.inr (by simp [fixBit, hop]))
  have h3 := or_core n F gs o p ph y g y L true (hnc true) hgp hop hin hlne hph hone ho2 hlx
    {ph, p, S} (by
      intro q hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl | rfl
      · exact rc_input true hphR
      · exact rc_input true hpR
      · exact rc_of_reads hSr' hcp)
  rwa [Finset.card_eq_three.2 ⟨ph, p, S, by omega, by omega, by omega, rfl⟩] at h3

theorem set_clean {N : ℕ} (gs : List Gate) (ph : ℕ) (g0 : Gate) (hcl : CleanL N gs)
    (hph : ph < gs.length) (hc0 : CleanGate (N + ph) g0) : CleanL N (gs.set ph g0) := by
  intro r g' hr'
  by_cases hrp : r = ph
  · subst hrp
    rw [List.getElem?_set_self hph] at hr'
    cases hr'
    exact hc0
  · rw [List.getElem?_set_ne (Ne.symm hrp)] at hr'
    exact hcl r g' hr'

theorem zswap_agree {N : ℕ} (gs : List Gate) (hcl : CleanL N gs) (ph : ℕ) (g0 : Gate)
    (hph : ph < gs.length) (hc0 : CleanGate (N + ph) g0) (u : Fin N → Bool)
    (hv : vl gs u (N + ph) = g0.op.eval (g0.inputs.map (vl gs u))) :
    ∀ w, vl (gs.set ph g0) u w = vl gs u w := by
  have hcl' := set_clean gs ph g0 hcl hph hc0
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hwk : w < N
    · rw [vl_input _ u w hwk, vl_input gs u w hwk]
    · obtain ⟨r, rfl⟩ : ∃ r, w = N + r := ⟨w - N, by omega⟩
      by_cases hrp : r = ph
      · subst hrp
        have hg0 : (gs.set r g0)[r]? = some g0 := List.getElem?_set_self hph
        rw [vl_gate _ hcl' u r g0 hg0, hv]
        congr 1
        apply List.map_congr_left
        intro a ha
        exact ih a (hc0.lt a ha)
      · cases hr : gs[r]? with
        | none =>
          have hl : gs.length ≤ r := List.getElem?_eq_none_iff.1 hr
          rw [vl_beyond _ u _ (by simp; omega), vl_beyond gs u _ (by omega)]
        | some g' =>
          have hr' : (gs.set ph g0)[r]? = some g' := by
            rw [List.getElem?_set_ne (Ne.symm hrp)]; exact hr
          rw [vl_gate _ hcl' u r g' hr', vl_gate gs hcl u r g' hr]
          congr 1
          apply List.map_congr_left
          intro a ha
          exact ih a ((hcl r g' hr).lt a ha)

theorem circ {n : ℕ} (F : (Fin (n + 1) → Bool) → Bool) (D O M : Finset (Fin (n + 1)))
    (z0 z1 : Fin (n + 1)) (B s : ℕ)
    (hDc : ∀ i, i ∉ D → i = z0 ∨ i = z1) (hz0 : z0 ∉ D) (hz1D : z1 ∉ D) (hz01 : z0 ≠ z1)
    (hOM : ∀ y ∈ D, y ∈ O ∨ y ∈ M)
    (hnc : ∀ y ∈ D, NCy F y) (hnc0 : NCy F z0)
    (hnf : ∀ y ∈ D, ∀ y' ∈ D, y ≠ y' → ¬ PairFunnel F y y')
    (hdep : ∀ y ∈ D, Dep F y) (hDne : D.Nonempty)
    (hsepO : ∀ y ∈ O, ∀ c0 c1 : Bool, ∃ x : Fin (n + 1) → Bool, x z0 = c0 ∧ x z1 = c1 ∧
      F (Function.update x y false) ≠ F (Function.update x y true))
    (hsepM : ∀ y ∈ M, ∀ c0 c1 : Bool, (c0 = false ∨ c1 = false) →
      ∃ x : Fin (n + 1) → Bool, x z0 = c0 ∧ x z1 = c1 ∧
      F (Function.update x y false) ≠ F (Function.update x y true))
    (hz1 : ∃ x : Fin (n + 1) → Bool, x z1 = false ∧
      F (Function.update x z0 false) ≠ F (Function.update x z0 true))
    (bO : ∀ y ∈ O, ∀ s', HasCircuitSize (n + 1) (fun x => F (Function.update x y false)) s' →
      B ≤ s' + 2)
    (bM : ∀ y ∈ M, ∀ (b : Bool) (s' : ℕ),
      HasCircuitSize (n + 1) (fun x => F (Function.update x y b)) s' → B ≤ s' + 3)
    (b0 : ∀ s', HasCircuitSize (n + 1) (fun x => F (Function.update x z0 false)) s' →
      B ≤ s' + 4)
    (hC : HasCircuitSize (n + 1) F s) : B ≤ s := by
  have hfnc : ∃ x y : Fin (n + 1) → Bool, F x ≠ F y := by
    obtain ⟨x, x', h⟩ := hnc0 false
    exact ⟨_, _, h⟩
  obtain ⟨gs, o, L, hlen⟩ := exists_least (n + 1) F s hfnc hC
  suffices key : B ≤ gs.length by omega
  have pay3 : ∀ y ∈ M, ∀ (b : Bool) (k : ℕ), 3 ≤ k → Drop F y b k gs.length →
      B ≤ gs.length := by
    rintro y hy b k hk ⟨s', hs', hc⟩
    have := bM y hy b s' hc
    omega
  have pay2 : ∀ y ∈ O, ∀ k : ℕ, 2 ≤ k → Drop F y false k gs.length → B ≤ gs.length := by
    rintro y hy k hk ⟨s', hs', hc⟩
    have := bO y hy s' hc
    omega
  have payD : ∀ y ∈ D, Pays F y gs.length → B ≤ gs.length := by
    intro y hy hP
    rcases hOM y hy with hO | hM
    · rcases hP with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
      · exact pay2 y hO 3 (by norm_num) h1
      · exact pay2 y hO 4 (by norm_num) h1
      · exact pay2 y hO 2 le_rfl h1
    · rcases hP with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, h1⟩
      · exact pay3 y hM false 3 le_rfl h1
      · exact pay3 y hM false 4 (by norm_num) h1
      · exact pay3 y hM true 4 (by norm_num) h1
  by_cases hOR : OneReader D gs
  swap
  · rcases not_and_or.1 hOR with h | h
    · push_neg at h
      obtain ⟨y, hy, p, q, hp, hq, hpq⟩ := h
      exact payD y hy (L.two_readers y (hnc y hy) p q hpq hp hq)
    · push_neg at h
      obtain ⟨y, hy, pn, hpn, p, q, hp, hq, hpq⟩ := h
      exact payD y hy (Or.inl (L.not_two_readers y (hnc y hy) pn _ hpn rfl (by simp)
        p q hpq hp hq))
  obtain ⟨p, g, y, l, h, ⟨hg, hop, hin, hyD, hlit, hfree⟩, hout⟩ :=
    front hnc hnf hdep hDne L hOR
  have hpl : p < gs.length := (List.getElem?_eq_some_iff.1 hg).1
  have hlmem : l ∈ g.inputs := by rcases hin with e | e <;> simp [e]
  have hhmem : h ∈ g.inputs := by rcases hin with e | e <;> simp [e]
  have hRl : Reads gs p l := ⟨g, hg, hlmem⟩
  have hyz0 : y ≠ z0 := fun e => hz0 (e ▸ hyD)
  have hyz1 : y ≠ z1 := fun e => hz1D (e ▸ hyD)
  obtain ⟨c, hlv⟩ : ∃ c : Bool, ∀ u, vl gs u l = xor (u y) c := by
    rcases hlit with e | ⟨pn, e, hpn⟩
    · exact ⟨false, fun u => by rw [e, vl_input gs u y y.isLt]; simp⟩
    · exact ⟨true, fun u => by
        rw [e, vl_not gs L.hcl u pn _ hpn (y : ℕ) rfl rfl, vl_input gs u y y.isLt]; simp⟩
  have hR : ∀ q a, (a = (y : ℕ) ∨ a = l) → Reads gs q a → n + 1 + q ≠ l → q = p := by
    intro q a ha hq hne
    rcases hlit with e | ⟨pn, e, hpn⟩
    · have ha' : a = y := by
        rcases ha with ha | ha
        · exact ha
        · rw [ha, e]
      rw [ha'] at hq
      exact hOR.1 y hyD q p hq (by rw [← e]; exact hRl)
    · rcases ha with ha | ha
      · rw [ha] at hq
        have := hOR.1 y hyD q pn hq ⟨_, hpn, by simp⟩
        exact absurd (by rw [this, e]) hne
      · rw [ha, e] at hq
        exact hOR.2 y hyD pn hpn q p hq (by rw [← e]; exact hRl)
  have ho1 : o ≠ y := by
    intro e
    exact nlit hnc hyD false (fun u => by rw [← L.hev, e, vl_input gs u y y.isLt]; simp)
  have ho2 : o ≠ l := by
    intro e
    exact nlit hnc hyD c (fun u => by rw [← L.hev, e, hlv])
  have hhv : ∀ u u' : Fin (n + 1) → Bool, u z0 = u' z0 → u z1 = u' z1 →
      vl gs u h = vl gs u' h := by
    intro u u' e0 e1
    refine dfree_val h hfree u u' (fun j hj => ?_)
    rcases hDc j hj with rfl | rfl
    · exact e0
    · exact e1
  have NONC : ∀ x : Fin (n + 1) → Bool,
      F (Function.update x y false) ≠ F (Function.update x y true) →
      ∀ u : Fin (n + 1) → Bool, u z0 = x z0 → u z1 = x z1 → vl gs u h = !fixBit g := by
    intro x hx u e0 e1
    have hh : vl gs u h = vl gs (Function.update x y false) h :=
      hhv _ _ (by rw [Function.update_of_ne (Ne.symm hyz0), e0])
        (by rw [Function.update_of_ne (Ne.symm hyz1), e1])
    have hh' : vl gs (Function.update x y true) h = vl gs (Function.update x y false) h :=
      hhv _ _ (by rw [Function.update_of_ne (Ne.symm hyz0), Function.update_of_ne (Ne.symm hyz0)])
        (by rw [Function.update_of_ne (Ne.symm hyz1), Function.update_of_ne (Ne.symm hyz1)])
    by_contra hne
    have hfx : vl gs u h = fixBit g := by
      cases hfb : fixBit g <;> cases hv : vl gs u h <;> simp_all
    apply hx
    apply via_one L y l p hR ho1 ho2
    · intro j hj
      rw [Function.update_of_ne hj, Function.update_of_ne hj]
    · rw [vl_abs gs L.hcl _ p g hg hop h hhmem (by rw [← hh, hfx]),
        vl_abs gs L.hcl _ p g hg hop h hhmem (by rw [hh', ← hh, hfx])]
  have hnconst : ¬ ∀ u : Fin (n + 1) → Bool, vl gs u h = !fixBit g := by
    intro hall
    by_cases hhn : h < n + 1
    · have := hall (fun _ => fixBit g)
      rw [vl_input gs _ h hhn] at this
      cases hfb : fixBit g <;> simp [hfb] at this
    · obtain ⟨ph, rfl⟩ : ∃ ph, h = n + 1 + ph := ⟨h - (n + 1), by omega⟩
      have hph : ph < gs.length := by
        have := (L.hcl p g hg).lt _ hhmem
        omega
      exact L.no_const hfnc ph hph _ hall
  rcases hOM y hyD with hyO | hyM
  · exfalso
    apply hnconst
    intro u
    obtain ⟨x, e0, e1, hx⟩ := hsepO y hyO (u z0) (u z1)
    exact NONC x hx u e0.symm e1.symm
  have hlow : ∀ u : Fin (n + 1) → Bool, (u z0 = false ∨ u z1 = false) →
      vl gs u h = !fixBit g := by
    intro u hu
    obtain ⟨x, e0, e1, hx⟩ := hsepM y hyM (u z0) (u z1) hu
    exact NONC x hx u e0.symm e1.symm
  have hhg : n + 1 ≤ h := by
    by_contra hlt
    push_neg at hlt
    have hhD : (⟨h, hlt⟩ : Fin (n + 1)) ∉ D := by
      intro hm
      apply hfree _ hm
      rw [front_supp_input gs h hlt]
      simp
    have key2 : ∀ z : Fin (n + 1), (⟨h, hlt⟩ : Fin (n + 1)) = z →
        (∀ b : Bool, (Function.update (fun _ => false) z b) z0 = false ∨
          (Function.update (fun _ => false) z b) z1 = false) → False := by
      intro z e hz
      have h1 := hlow _ (hz false)
      have h2 := hlow _ (hz true)
      rw [vl_input gs _ h hlt, e, Function.update_self] at h1 h2
      rw [← h1] at h2
      cases h2
    rcases hDc _ hhD with e | e
    · exact key2 z0 e (fun b => Or.inr (by simp [Ne.symm hz01]))
    · exact key2 z1 e (fun b => Or.inl (by simp [hz01]))
  obtain ⟨ph, rfl⟩ : ∃ ph, h = n + 1 + ph := ⟨h - (n + 1), by omega⟩
  have hph : ph < gs.length := by
    have := (L.hcl p g hg).lt _ hhmem
    omega
  have hpph : ph < p := by
    have := (L.hcl p g hg).lt _ hhmem
    omega
  have hoh : o ≠ n + 1 + ph := by
    intro e
    obtain ⟨x, hx⟩ := hdep y hyD
    apply hx
    rw [← L.hev, ← L.hev, e]
    exact hhv _ _ (by rw [Function.update_of_ne (Ne.symm hyz0)])
      (by rw [Function.update_of_ne (Ne.symm hyz1)])
  rcases hlit with hly | ⟨pn, hlpn, hpn⟩
  swap
  · have hpnR : Reads gs pn y := ⟨_, hpn, by simp⟩
    obtain ⟨cc, hcc⟩ := isC_reader L.hcl y pn _ hpn (by simp) (!fixBit g) (Or.inl rfl)
    have hcc' : cc = fixBit g := by
      have h1 := st_val_const n gs L.hcl y (!fixBit g) _ cc hcc (fun _ => false)
      rw [vl_not gs L.hcl _ pn _ hpn (y : ℕ) rfl rfl, vl_input gs _ y y.isLt] at h1
      simp [ins] at h1
      rw [← h1]
    subst hcc'
    have hcp : IsC n gs y (!fixBit g) (n + 1 + p) :=
      const_read n gs L.hcl y (!fixBit g) p g hg l hlmem (by rw [hlpn]; exact hcc)
    obtain ⟨S, hpS, hSr, hSrc⟩ := L.next y (!fixBit g) (hnc y hyD _) p hpl hcp
    have hpnp : pn < p := by
      have := (L.hcl p g hg).lt _ hlmem
      omega
    exact pay3 y hyM _ 3 le_rfl (L.save3 y _ (hnc y hyD _) pn p S (by omega) (by omega)
      (by omega) (rc_input _ hpnR) (rc_of_reads hRl ⟨_, by rw [hlpn]; exact hcc⟩) hSrc)
  by_cases hone : ∀ t, Reads gs t (n + 1 + ph) → t = p
  · have hin' : g.inputs = [l, n + 1 + ph] ∨ g.inputs = [n + 1 + ph, l] := hin
    rcases hop with hand | hor
    · have := (stmtAnd n F gs o p ph l g y L (hnc y hyD) (hdep y hyD) hg hand hin'
        (Or.inl hly) hph hone hout hoh).1 hly
      exact pay3 y hyM false 3 le_rfl this
    · rw [hly] at hin'
      exact pay3 y hyM true 3 le_rfl
        (or_pay n F gs o p ph g y L (hnc y hyD) hg hor hin' hph hone hout hoh)
  push_neg at hone
  obtain ⟨t, htR, htp⟩ := hone
  have htph : ph < t := by
    obtain ⟨gt, hgt, hm⟩ := htR
    have := (L.hcl t gt hgt).lt _ hm
    omega
  obtain ⟨g0, hc0, hz0m, hval0, hcz⟩ : ∃ g0 : Gate, CleanGate (n + 1 + ph) g0 ∧
      (z0 : ℕ) ∈ g0.inputs ∧
      (∀ u : Fin (n + 1) → Bool, u z0 = false →
        g0.op.eval (g0.inputs.map (vl gs u)) = !fixBit g) ∧
      (g0.op = GateOp.not ∨ false = fixBit g0) := by
    have hz0lt := z0.isLt
    cases hfb : fixBit g
    · refine ⟨⟨GateOp.not, [(z0 : ℕ)]⟩, Or.inl ⟨rfl, z0, by omega, rfl⟩, by simp,
        fun u hu => ?_, Or.inl rfl⟩
      simp [GateOp.eval, vl_input gs u z0 z0.isLt, hu]
    · refine ⟨⟨GateOp.and, [(z0 : ℕ), (z0 : ℕ)]⟩,
        Or.inr ⟨Or.inl rfl, z0, z0, by omega, by omega, rfl⟩, by simp, fun u hu => ?_,
        Or.inr rfl⟩
      simp [GateOp.eval, vl_input gs u z0 z0.isLt, hu]
  have hcl' : CleanL (n + 1) (gs.set ph g0) := set_clean gs ph g0 L.hcl hph hc0
  have hlen' : (gs.set ph g0).length = gs.length := by simp
  have hget : ∀ r, r ≠ ph → (gs.set ph g0)[r]? = gs[r]? := fun r hr =>
    List.getElem?_set_ne (Ne.symm hr)
  have hget0 : (gs.set ph g0)[ph]? = some g0 := List.getElem?_set_self hph
  have hagree : ∀ u : Fin (n + 1) → Bool, u z0 = false →
      ∀ w, vl (gs.set ph g0) u w = vl gs u w := by
    intro u hu
    apply zswap_agree gs L.hcl ph g0 hph hc0 u
    rw [hval0 u hu, hlow u (Or.inl hu)]
  have hfz : ∀ x : Fin (n + 1) → Bool,
      vl (gs.set ph g0) (Function.update x z0 false) o = F (Function.update x z0 false) := by
    intro x
    rw [hagree _ (Function.update_self z0 false x), L.hev]
  have hnc' : ∃ x x' : Fin (n + 1) → Bool, vl (gs.set ph g0) (Function.update x z0 false) o
      ≠ vl (gs.set ph g0) (Function.update x' z0 false) o := by
    obtain ⟨x, x', hx⟩ := hnc0 false
    exact ⟨x, x', by rw [hfz, hfz]; exact hx⟩
  have hcph : IsC n (gs.set ph g0) z0 false (n + 1 + ph) :=
    isC_reader hcl' z0 ph g0 hget0 hz0m false hcz
  have hRC : ∀ q, Reads gs q (n + 1 + ph) → q ≠ ph → RC n (gs.set ph g0) z0 false q := by
    intro q hq hqph
    obtain ⟨gq, hgq, hm⟩ := hq
    exact rc_of_reads ⟨gq, by rw [hget q hqph]; exact hgq, hm⟩ hcph
  have hRCz : ∀ q, Reads gs q z0 → q ≠ ph → RC n (gs.set ph g0) z0 false q := by
    intro q hq hqph
    obtain ⟨gq, hgq, hm⟩ := hq
    exact rc_input false ⟨gq, by rw [hget q hqph]; exact hgq, hm⟩
  have hph0 : RC n (gs.set ph g0) z0 false ph := rc_input false ⟨g0, hget0, hz0m⟩
  have hpRC := hRC p ⟨g, hg, hhmem⟩ (by omega)
  have htRC := hRC t htR (by omega)
  have fin4 : ∀ q4, q4 ≠ ph → q4 ≠ p → q4 ≠ t → RC n (gs.set ph g0) z0 false q4 →
      B ≤ gs.length := by
    intro q4 h1 h2 h3 h4
    have hd := save n (fun x => vl (gs.set ph g0) x o) (gs.set ph g0) o hcl' (fun _ => rfl)
      z0 false hnc' {ph, p, t, q4} (by
        intro q hq
        simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl | rfl
        · exact hph0
        · exact hpRC
        · exact htRC
        · exact h4)
    have hcard : ({ph, p, t, q4} : Finset ℕ).card = 4 := by
      rw [Finset.card_insert_of_notMem (by simp; omega),
        Finset.card_eq_three.2 ⟨p, t, q4, by omega, by omega, by omega, rfl⟩]
    rw [hcard, hlen'] at hd
    obtain ⟨s', hs', hc⟩ := hd
    have e : (fun x : Fin (n + 1) → Bool => F (Function.update x z0 false))
        = fun x => (fun x => vl (gs.set ph g0) x o) (Function.update x z0 false) := by
      funext x
      exact (hfz x).symm
    have := b0 s' (by rw [e]; exact hc)
    omega
  have hz0lt := z0.isLt
  have hylt := y.isLt
  by_cases hq : ∃ q, Reads gs q z0 ∧ q ≠ ph ∧ q ≠ t
  · obtain ⟨q, hqR, hqph, hqt⟩ := hq
    have hqp : q ≠ p := by
      rintro rfl
      obtain ⟨gq, hgq, hm⟩ := hqR
      rw [hg] at hgq
      cases hgq
      rcases hin with e | e <;> rw [e, hly] at hm <;>
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hm <;>
        rcases hm with hm | hm <;> first | exact hyz0 (Fin.ext hm.symm) | omega
    exact fin4 q hqph hqp hqt (hRCz q hqR hqph)
  push_neg at hq
  by_cases ht0 : Reads gs t z0
  · obtain ⟨gt, hgt, hzt⟩ := ht0
    have hht : n + 1 + ph ∈ gt.inputs := by
      obtain ⟨gt', hgt', hm⟩ := htR
      rw [hgt] at hgt'
      cases hgt'
      exact hm
    have hgt' : (gs.set ph g0)[t]? = some gt := by rw [hget t (by omega)]; exact hgt
    have hct : IsC n (gs.set ph g0) z0 false (n + 1 + t) := by
      apply st_allconst n _ hcl' z0 false t gt hgt'
      intro a ha
      have : a = (z0 : ℕ) ∨ a = n + 1 + ph := by
        rcases L.hcl t gt hgt with ⟨_, j, _, hjn⟩ | ⟨_, j, k, _, _, hjk⟩
        · rw [hjn] at hzt hht ha
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hzt hht ha
          omega
        · rw [hjk] at hzt hht ha
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hzt hht ha
          omega
      rcases this with rfl | rfl
      · exact ⟨false, stF_self n _ z0 false⟩
      · exact hcph
    have hot : o ≠ n + 1 + t := by
      intro e
      obtain ⟨cc, hcc⟩ := hct
      obtain ⟨x, x', hx⟩ := hnc'
      apply hx
      rw [e, upd_ins, upd_ins, st_val_const n _ hcl' z0 false _ cc hcc,
        st_val_const n _ hcl' z0 false _ cc hcc]
    have htl : t < gs.length := reads_len htR
    obtain ⟨S, htS, hSR⟩ := L.live hfnc t htl hot
    have hSRC : RC n (gs.set ph g0) z0 false S := by
      obtain ⟨gS, hgS, hm⟩ := hSR
      exact rc_of_reads ⟨gS, by rw [hget S (by omega)]; exact hgS, hm⟩ hct
    have hSp : S ≠ p := by
      rintro rfl
      obtain ⟨gS, hgS, hm⟩ := hSR
      rw [hg] at hgS
      cases hgS
      rcases hin with e | e <;> rw [e, hly] at hm <;>
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hm <;> omega
    exact fin4 S (by omega) hSp (by omega) hSRC
  · exfalso
    obtain ⟨x, hx1, hxd⟩ := hz1
    apply hxd
    apply via_one L z0 z0 ph
    · intro q a ha hqa _
      have ha' : a = z0 := by rcases ha with ha | ha <;> exact ha
      rw [ha'] at hqa
      by_contra hqph
      have := hq q hqa hqph
      subst this
      exact ht0 hqa
    · intro e
      obtain ⟨u, u', hu⟩ := hnc0 false
      apply hu
      rw [← L.hev, ← L.hev, e, vl_input gs _ z0 z0.isLt, vl_input gs _ z0 z0.isLt]
      simp
    · intro e
      obtain ⟨u, u', hu⟩ := hnc0 false
      apply hu
      rw [← L.hev, ← L.hev, e, vl_input gs _ z0 z0.isLt, vl_input gs _ z0 z0.isLt]
      simp
    · intro j hj
      rw [Function.update_of_ne hj, Function.update_of_ne hj]
    · rw [hlow _ (Or.inr (by rw [Function.update_of_ne (Ne.symm hz01)]; exact hx1)),
        hlow _ (Or.inr (by rw [Function.update_of_ne (Ne.symm hz01)]; exact hx1))]

section Theta

open PEqualNP.Library.Peel (delVerts HasPeel IsRun Peelable)
open PEqualNP.Library.Peel.Scratch (delVerts_adj delVerts_delVerts delV_eq a1_peelable)
open PEqualNP.MetaComplexity.Loc (delV tau_attained Phi1 AFree)
open PEqualNP.MetaComplexity.Helpers.Forest (F F_true Cov forest_good_leaf)

theorem acyc_rank {V : Type*} (G : SimpleGraph V) (r : V → ℕ) (hr : Function.Injective r)
    (h : ∀ v a b, G.Adj v a → G.Adj v b → r a < r v → r b < r v → a = b) : G.IsAcyclic := by
  intro v c hc
  classical
  obtain ⟨m, hm', hmax'⟩ := c.support.toFinset.exists_max_image r
    ⟨v, List.mem_toFinset.2 c.start_mem_support⟩
  have hm : m ∈ c.support := List.mem_toFinset.1 hm'
  have hmax : ∀ x ∈ c.support, r x ≤ r m := fun x hx => hmax' x (List.mem_toFinset.2 hx)
  have hc' := hc.rotate hm
  have hnil : ¬ (c.rotate m hm).Nil := hc'.not_nil
  have h1 : G.Adj m (c.rotate m hm).snd := (c.rotate m hm).adj_snd hnil
  have h2 : G.Adj (c.rotate m hm).penultimate m := (c.rotate m hm).adj_penultimate hnil
  have hne := hc'.snd_ne_penultimate
  have hs1 : (c.rotate m hm).snd ∈ c.support :=
    (c.mem_support_rotate_iff m hm).1 ((c.rotate m hm).getVert_mem_support 1)
  have hs2 : (c.rotate m hm).penultimate ∈ c.support :=
    (c.mem_support_rotate_iff m hm).1 ((c.rotate m hm).getVert_mem_support _)
  have hlt1 : r (c.rotate m hm).snd < r m :=
    lt_of_le_of_ne (hmax _ hs1) (fun e => h1.ne (hr e).symm)
  have hlt2 : r (c.rotate m hm).penultimate < r m :=
    lt_of_le_of_ne (hmax _ hs2) (fun e => h2.ne (hr e))
  exact hne (h m _ _ h1 h2.symm hlt1 hlt2)

def tb (i j : Fin 11) : Bool :=
  [(0, 2), (2, 3), (3, 4), (4, 1), (0, 5), (5, 6), (6, 7), (7, 1), (0, 8), (8, 9), (9, 10),
    (10, 1)].contains (i.val, j.val)

abbrev Th : SimpleGraph (Fin 11) := SimpleGraph.fromRel fun i j => tb i j = true

def fT (x : Fin 11 → Bool) : Bool :=
  (x 0 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 1) || (x 0 && x 5) ||
    (x 5 && x 6) || (x 6 && x 7) || (x 7 && x 1) || (x 0 && x 8) || (x 8 && x 9) ||
    (x 9 && x 10) || (x 10 && x 1)

theorem fT_eq : fT = F Th ∅ := by
  funext x
  rw [Bool.eq_iff_iff, F_true]
  simp only [Finset.notMem_empty, false_and, exists_false, false_or]
  constructor
  · intro h
    simp only [fT, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with ((((((((((h | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h
    · exact ⟨0, 2, by decide, h.1, h.2⟩
    · exact ⟨2, 3, by decide, h.1, h.2⟩
    · exact ⟨3, 4, by decide, h.1, h.2⟩
    · exact ⟨4, 1, by decide, h.1, h.2⟩
    · exact ⟨0, 5, by decide, h.1, h.2⟩
    · exact ⟨5, 6, by decide, h.1, h.2⟩
    · exact ⟨6, 7, by decide, h.1, h.2⟩
    · exact ⟨7, 1, by decide, h.1, h.2⟩
    · exact ⟨0, 8, by decide, h.1, h.2⟩
    · exact ⟨8, 9, by decide, h.1, h.2⟩
    · exact ⟨9, 10, by decide, h.1, h.2⟩
    · exact ⟨10, 1, by decide, h.1, h.2⟩
  · rintro ⟨i, j, hij, hi, hj⟩
    have key : ∀ i j : Fin 11, Th.Adj i j → ∀ x : Fin 11 → Bool, x i = true → x j = true →
        fT x = true := by
      intro i j hij x hi hj
      fin_cases i <;> fin_cases j <;>
        first | (exfalso; revert hij; decide) | (simp at hi hj; simp [fT, hi, hj])
    exact key i j hij x hi hj

def rk (L : List ℕ) (v : Fin 11) : ℕ := L.getD v.val 0

theorem anti {X Y : Finset (Fin 11)} (h : X ⊆ Y) : delVerts Th Y ≤ delVerts Th X :=
  fun _ _ hij => ⟨hij.1, fun hi => hij.2.1 (h hi), fun hj => hij.2.2 (h hj)⟩

theorem acyc0 : (delVerts Th {0}).IsAcyclic :=
  acyc_rank _ (rk [10, 0, 7, 4, 1, 8, 5, 2, 9, 6, 3])
    (by intro a b e; revert a b; decide) (by decide)

theorem acyc1 : (delVerts Th {1}).IsAcyclic :=
  acyc_rank _ (rk [0, 10, 1, 4, 7, 2, 5, 8, 3, 6, 9])
    (by intro a b e; revert a b; decide) (by decide)

theorem acyc12 : ∀ u ∈ ({2, 3, 4} : Finset (Fin 11)), ∀ w ∈ ({5, 6, 7} : Finset (Fin 11)),
    (delVerts Th {u, w}).IsAcyclic := by
  have hr : Function.Injective (rk [0, 4, 5, 9, 7, 6, 10, 8, 1, 2, 3]) := by
    intro a b e; revert a b; decide
  have key : ∀ u ∈ ({2, 3, 4} : Finset (Fin 11)), ∀ w ∈ ({5, 6, 7} : Finset (Fin 11)),
      ∀ v a b : Fin 11, (delVerts Th {u, w}).Adj v a → (delVerts Th {u, w}).Adj v b →
        rk [0, 4, 5, 9, 7, 6, 10, 8, 1, 2, 3] a < rk [0, 4, 5, 9, 7, 6, 10, 8, 1, 2, 3] v →
        rk [0, 4, 5, 9, 7, 6, 10, 8, 1, 2, 3] b < rk [0, 4, 5, 9, 7, 6, 10, 8, 1, 2, 3] v →
        a = b := by decide
  intro u hu w hw
  exact acyc_rank _ _ hr (key u hu w hw)

theorem acyc13 : ∀ u ∈ ({2, 3, 4} : Finset (Fin 11)), ∀ w ∈ ({8, 9, 10} : Finset (Fin 11)),
    (delVerts Th {u, w}).IsAcyclic := by
  have hr : Function.Injective (rk [0, 4, 5, 9, 7, 1, 2, 3, 6, 10, 8]) := by
    intro a b e; revert a b; decide
  have key : ∀ u ∈ ({2, 3, 4} : Finset (Fin 11)), ∀ w ∈ ({8, 9, 10} : Finset (Fin 11)),
      ∀ v a b : Fin 11, (delVerts Th {u, w}).Adj v a → (delVerts Th {u, w}).Adj v b →
        rk [0, 4, 5, 9, 7, 1, 2, 3, 6, 10, 8] a < rk [0, 4, 5, 9, 7, 1, 2, 3, 6, 10, 8] v →
        rk [0, 4, 5, 9, 7, 1, 2, 3, 6, 10, 8] b < rk [0, 4, 5, 9, 7, 1, 2, 3, 6, 10, 8] v →
        a = b := by decide
  intro u hu w hw
  exact acyc_rank _ _ hr (key u hu w hw)

theorem acyc23 : ∀ u ∈ ({5, 6, 7} : Finset (Fin 11)), ∀ w ∈ ({8, 9, 10} : Finset (Fin 11)),
    (delVerts Th {u, w}).IsAcyclic := by
  have hr : Function.Injective (rk [0, 4, 1, 2, 3, 5, 9, 7, 6, 10, 8]) := by
    intro a b e; revert a b; decide
  have key : ∀ u ∈ ({5, 6, 7} : Finset (Fin 11)), ∀ w ∈ ({8, 9, 10} : Finset (Fin 11)),
      ∀ v a b : Fin 11, (delVerts Th {u, w}).Adj v a → (delVerts Th {u, w}).Adj v b →
        rk [0, 4, 1, 2, 3, 5, 9, 7, 6, 10, 8] a < rk [0, 4, 1, 2, 3, 5, 9, 7, 6, 10, 8] v →
        rk [0, 4, 1, 2, 3, 5, 9, 7, 6, 10, 8] b < rk [0, 4, 1, 2, 3, 5, 9, 7, 6, 10, 8] v →
        a = b := by decide
  intro u hu w hw
  exact acyc_rank _ _ hr (key u hu w hw)

theorem nbr2 (Y : Finset (Fin 11)) (v l r : Fin 11) (Ex : Finset (Fin 11))
    (hN : ∀ w, Th.Adj v w ↔ w = l ∨ w = r ∨ w ∈ Ex) (hv : v ∉ Y) (hl : l ∉ Y) (hr : r ∉ Y)
    (hE : ∀ w ∈ Ex, w ∈ Y) : ∀ w, (delVerts Th Y).Adj v w ↔ w = l ∨ w = r := by
  intro w
  rw [delVerts_adj, hN]
  constructor
  · rintro ⟨h | h | h, -, hw⟩
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd (hE w h) hw
  · rintro (rfl | rfl)
    · exact ⟨Or.inl rfl, hv, hl⟩
    · exact ⟨Or.inr (Or.inl rfl), hv, hr⟩

theorem run_gen (Y : Finset (Fin 11)) (a' a s t b b' c1 c2 : Fin 11) (Ex : Finset (Fin 11))
    (hnd : [a', a, s, t, b, b'].Nodup)
    (Na : ∀ w, Th.Adj a w ↔ w = a' ∨ w = s ∨ w ∈ (∅ : Finset (Fin 11)))
    (Ns : ∀ w, Th.Adj s w ↔ w = a ∨ w = t ∨ w ∈ Ex)
    (Nt : ∀ w, Th.Adj t w ↔ w = s ∨ w = b ∨ w ∈ (∅ : Finset (Fin 11)))
    (Nb : ∀ w, Th.Adj b w ↔ w = t ∨ w = b' ∨ w ∈ (∅ : Finset (Fin 11)))
    (Na' : ∀ w, Th.Adj a' w → w = a ∨ w = c1) (Nb' : ∀ w, Th.Adj b' w → w = b ∨ w = c2)
    (hEx : ∀ w ∈ Ex, w ∈ Y) (h1 : a' ∉ Y) (h2 : a ∉ Y) (h3 : s ∉ Y) (h4 : t ∉ Y)
    (h5 : b ∉ Y) (h6 : b' ∉ Y) :
    IsRun (delVerts Th Y) a' a s t b b' :=
  ⟨hnd, nbr2 Y a a' s ∅ Na h2 h1 h3 (by simp), nbr2 Y s a t Ex Ns h3 h2 h4 hEx,
    nbr2 Y t s b ∅ Nt h4 h3 h5 (by simp), nbr2 Y b t b' ∅ Nb h5 h4 h6 (by simp),
    ⟨c1, fun w hw => Na' w hw.1⟩, ⟨c2, fun w hw => Nb' w hw.1⟩⟩

theorem pair_sub {Y : Finset (Fin 11)} {u w : Fin 11} (hu : u ∈ Y) (hw : w ∈ Y) :
    ({u, w} : Finset (Fin 11)) ⊆ Y := by
  intro z hz
  simp only [Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with rfl | rfl
  · exact hu
  · exact hw

theorem peel_gen (Y : Finset (Fin 11)) (v : Fin 11) (Ij Ik : Finset (Fin 11)) (hv : v ∈ Y)
    (acj : ∀ w ∈ Ij, (delVerts Th {v, w}).IsAcyclic)
    (ack : ∀ w ∈ Ik, (delVerts Th {v, w}).IsAcyclic)
    (hrun : (0 : Fin 11) ∉ Y → (1 : Fin 11) ∉ Y → (∀ w ∈ Ij, w ∉ Y) → (∀ w ∈ Ik, w ∉ Y) →
      ∃ a' a s t b b' : Fin 11, IsRun (delVerts Th Y) a' a s t b b') :
    HasPeel (delVerts Th Y) := by
  intro hE
  by_cases h0 : (0 : Fin 11) ∈ Y
  · exact Or.inl (forest_good_leaf _ (acyc0.anti (anti (Finset.singleton_subset_iff.2 h0))) hE)
  by_cases h1 : (1 : Fin 11) ∈ Y
  · exact Or.inl (forest_good_leaf _ (acyc1.anti (anti (Finset.singleton_subset_iff.2 h1))) hE)
  by_cases hj : ∃ w ∈ Ij, w ∈ Y
  · obtain ⟨w, hw, hwY⟩ := hj
    exact Or.inl (forest_good_leaf _ ((acj w hw).anti (anti (pair_sub hv hwY))) hE)
  by_cases hk : ∃ w ∈ Ik, w ∈ Y
  · obtain ⟨w, hw, hwY⟩ := hk
    exact Or.inl (forest_good_leaf _ ((ack w hw).anti (anti (pair_sub hv hwY))) hE)
  push_neg at hj hk
  exact Or.inr (hrun h0 h1 hj hk)

theorem sing_sub {Y : Finset (Fin 11)} {v : Fin 11} (hv : v ∈ Y) : ∀ w ∈ ({v} : Finset (Fin 11)), w ∈ Y := by
  intro w hw
  rw [Finset.mem_singleton] at hw
  rw [hw]
  exact hv

theorem peel2 (Y : Finset (Fin 11)) (hv : (2 : Fin 11) ∈ Y) : HasPeel (delVerts Th Y) :=
  peel_gen Y 2 {5, 6, 7} {8, 9, 10} hv (acyc12 2 (by decide)) (acyc13 2 (by decide))
    (fun h0 _ hj hk => ⟨9, 8, 0, 5, 6, 7, run_gen Y 9 8 0 5 6 7 10 1 {2} (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (sing_sub hv)
      (hk 9 (by decide)) (hk 8 (by decide)) h0 (hj 5 (by decide)) (hj 6 (by decide))
      (hj 7 (by decide))⟩)

theorem peel4 (Y : Finset (Fin 11)) (hv : (4 : Fin 11) ∈ Y) : HasPeel (delVerts Th Y) :=
  peel_gen Y 4 {5, 6, 7} {8, 9, 10} hv (acyc12 4 (by decide)) (acyc13 4 (by decide))
    (fun _ h1 hj hk => ⟨9, 10, 1, 7, 6, 5, run_gen Y 9 10 1 7 6 5 8 0 {4} (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (sing_sub hv)
      (hk 9 (by decide)) (hk 10 (by decide)) h1 (hj 7 (by decide)) (hj 6 (by decide))
      (hj 5 (by decide))⟩)

theorem peel5 (Y : Finset (Fin 11)) (hv : (5 : Fin 11) ∈ Y) : HasPeel (delVerts Th Y) :=
  peel_gen Y 5 {2, 3, 4} {8, 9, 10} hv
    (fun w hw => by rw [Finset.pair_comm]; exact acyc12 w hw 5 (by decide))
    (acyc23 5 (by decide))
    (fun h0 _ hj hk => ⟨9, 8, 0, 2, 3, 4, run_gen Y 9 8 0 2 3 4 10 1 {5} (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (sing_sub hv)
      (hk 9 (by decide)) (hk 8 (by decide)) h0 (hj 2 (by decide)) (hj 3 (by decide))
      (hj 4 (by decide))⟩)

theorem peel7 (Y : Finset (Fin 11)) (hv : (7 : Fin 11) ∈ Y) : HasPeel (delVerts Th Y) :=
  peel_gen Y 7 {2, 3, 4} {8, 9, 10} hv
    (fun w hw => by rw [Finset.pair_comm]; exact acyc12 w hw 7 (by decide))
    (acyc23 7 (by decide))
    (fun _ h1 hj hk => ⟨9, 10, 1, 4, 3, 2, run_gen Y 9 10 1 4 3 2 8 0 {7} (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (sing_sub hv)
      (hk 9 (by decide)) (hk 10 (by decide)) h1 (hj 4 (by decide)) (hj 3 (by decide))
      (hj 2 (by decide))⟩)

theorem peel8 (Y : Finset (Fin 11)) (hv : (8 : Fin 11) ∈ Y) : HasPeel (delVerts Th Y) :=
  peel_gen Y 8 {2, 3, 4} {5, 6, 7} hv
    (fun w hw => by rw [Finset.pair_comm]; exact acyc13 w hw 8 (by decide))
    (fun w hw => by rw [Finset.pair_comm]; exact acyc23 w hw 8 (by decide))
    (fun h0 _ hj hk => ⟨6, 5, 0, 2, 3, 4, run_gen Y 6 5 0 2 3 4 7 1 {8} (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (sing_sub hv)
      (hk 6 (by decide)) (hk 5 (by decide)) h0 (hj 2 (by decide)) (hj 3 (by decide))
      (hj 4 (by decide))⟩)

theorem peel10 (Y : Finset (Fin 11)) (hv : (10 : Fin 11) ∈ Y) : HasPeel (delVerts Th Y) :=
  peel_gen Y 10 {2, 3, 4} {5, 6, 7} hv
    (fun w hw => by rw [Finset.pair_comm]; exact acyc13 w hw 10 (by decide))
    (fun w hw => by rw [Finset.pair_comm]; exact acyc23 w hw 10 (by decide))
    (fun _ h1 hj hk => ⟨6, 7, 1, 4, 3, 2, run_gen Y 6 7 1 4 3 2 5 0 {10} (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (sing_sub hv)
      (hk 6 (by decide)) (hk 7 (by decide)) h1 (hj 4 (by decide)) (hj 3 (by decide))
      (hj 2 (by decide))⟩)

theorem peel0 (Y : Finset (Fin 11)) (hv : (0 : Fin 11) ∈ Y) : HasPeel (delVerts Th Y) :=
  fun hE => Or.inl (forest_good_leaf _ (acyc0.anti (anti (Finset.singleton_subset_iff.2 hv))) hE)

theorem peelable_of (X : Finset (Fin 11)) (v : Fin 11) (hv : v ∈ X)
    (hp : ∀ Y : Finset (Fin 11), v ∈ Y → HasPeel (delVerts Th Y)) :
    Peelable (delVerts Th X) := by
  intro Z
  rw [delVerts_delVerts]
  exact hp _ (Finset.mem_union_left _ hv)

theorem cov_match (G : SimpleGraph (Fin 11)) (k : ℕ) (u w : Fin k → Fin 11)
    (hadj : ∀ i, G.Adj (u i) (w i))
    (hd : ∀ i j, i ≠ j → u i ≠ u j ∧ u i ≠ w j ∧ w i ≠ w j)
    (T : Finset (Fin 11)) (hT : Cov G T) : k ≤ T.card := by
  classical
  let c : Fin k → Fin 11 := fun i => if u i ∈ T then u i else w i
  have hc : ∀ i, c i ∈ T := by
    intro i
    by_cases h : u i ∈ T
    · simp only [c, h, if_true]
    · simp only [c, h, if_false]
      rcases hT _ _ (hadj i) with h' | h'
      · exact absurd h' h
      · exact h'
  have hinj : Function.Injective c := by
    intro i j e
    by_contra hij
    have h1 := hd i j hij
    have h2 := hd j i (Ne.symm hij)
    simp only [c] at e
    split_ifs at e
    · exact h1.1 e
    · exact h1.2.1 e
    · exact h2.2.1 e.symm
    · exact h1.2.2 e
  calc k = (Finset.univ.image c).card := by
        rw [Finset.card_image_of_injective _ hinj]; simp
    _ ≤ T.card := Finset.card_le_card (fun x hx => by
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
        exact hc i)

theorem bnd (X A : Finset (Fin 11)) (E k s : ℕ) (hP : Peelable (delVerts Th X))
    (hA : ∀ i j, (delVerts Th X).Adj i j → i ∉ A) (hE : (delVerts Th X).edgeFinset.card = E)
    (hk : ∀ T, Cov (delVerts Th X) T → k ≤ T.card)
    (hC : HasCircuitSize 11 (F (delV Th X) A) s) : A.card + E + k ≤ s + 1 := by
  have hb := a1_peelable 11 (delV Th X) A (by show Peelable (delV Th X); rw [delV_eq]; exact hP)
    (fun i j h => hA i j (by rw [delV_eq] at h; exact h)) s hC
  obtain ⟨T, hT, hTc⟩ := tau_attained (delV Th X)
  have h1 := hk T (by rw [← delV_eq]; exact hT)
  have h2 : (delV Th X).edgeSet.ncard = E := by
    rw [delV_eq, ← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset, hE]
  unfold Phi1 at hb
  omega

theorem res0 (y : Fin 11) : (fun x => fT (Function.update x y false)) = F (delV Th {y}) ∅ := by
  funext x
  rw [fT_eq]
  exact PEqualNP.MetaComplexity.Loc.Res.ToolRes0_proof 11 Th ∅ y x (Finset.notMem_empty y)

def Dset : Finset (Fin 11) := {2, 3, 4, 5, 6, 7, 8, 9, 10}
def Oset : Finset (Fin 11) := {2, 4, 5, 7, 8, 10}
def Mset : Finset (Fin 11) := {3, 6, 9}

theorem bO : ∀ y ∈ Oset, ∀ s', HasCircuitSize (10 + 1)
    (fun x => fT (Function.update x y false)) s' → 16 ≤ s' + 2 := by
  intro y hy s' hC
  rw [res0] at hC
  have hA : ∀ (X : Finset (Fin 11)) (i j : Fin 11), (delVerts Th X).Adj i j →
      i ∉ (∅ : Finset (Fin 11)) := fun _ i _ _ => Finset.notMem_empty i
  simp only [Oset, Finset.mem_insert, Finset.mem_singleton] at hy
  rcases hy with rfl | rfl | rfl | rfl | rfl | rfl
  · have := bnd {2} ∅ 10 5 s' (peelable_of _ 2 (by decide) peel2) (hA _) (by decide)
      (cov_match _ 5 ![3, 0, 6, 1, 8] ![4, 5, 7, 10, 9] (by decide) (by decide)) hC
    simp at this
    omega
  · have := bnd {4} ∅ 10 5 s' (peelable_of _ 4 (by decide) peel4) (hA _) (by decide)
      (cov_match _ 5 ![2, 0, 6, 1, 8] ![3, 5, 7, 10, 9] (by decide) (by decide)) hC
    simp at this
    omega
  · have := bnd {5} ∅ 10 5 s' (peelable_of _ 5 (by decide) peel5) (hA _) (by decide)
      (cov_match _ 5 ![0, 3, 6, 1, 8] ![2, 4, 7, 10, 9] (by decide) (by decide)) hC
    simp at this
    omega
  · have := bnd {7} ∅ 10 5 s' (peelable_of _ 7 (by decide) peel7) (hA _) (by decide)
      (cov_match _ 5 ![0, 3, 5, 1, 8] ![2, 4, 6, 10, 9] (by decide) (by decide)) hC
    simp at this
    omega
  · have := bnd {8} ∅ 10 5 s' (peelable_of _ 8 (by decide) peel8) (hA _) (by decide)
      (cov_match _ 5 ![0, 3, 5, 7, 9] ![2, 4, 6, 1, 10] (by decide) (by decide)) hC
    simp at this
    omega
  · have := bnd {10} ∅ 10 5 s' (peelable_of _ 10 (by decide) peel10) (hA _) (by decide)
      (cov_match _ 5 ![0, 3, 5, 7, 8] ![2, 4, 6, 1, 9] (by decide) (by decide)) hC
    simp at this
    omega

theorem b0 : ∀ s', HasCircuitSize (10 + 1)
    (fun x => fT (Function.update x 0 false)) s' → 16 ≤ s' + 4 := by
  intro s' hC
  rw [res0] at hC
  have := bnd {0} ∅ 9 4 s' (peelable_of _ 0 (by decide) peel0)
    (fun i _ _ => Finset.notMem_empty i) (by decide)
    (cov_match _ 4 ![2, 4, 5, 8] ![3, 1, 6, 9] (by decide) (by decide)) hC
  simp at this
  omega

theorem one_gate (F1 : (Fin 11 → Bool) → Bool) (a : Fin 11) (s : ℕ) (hd : Dep F1 a)
    (hnc : NCy F1 a) (hC : HasCircuitSize 11 F1 s) :
    ∃ s', s' + 1 ≤ s ∧ HasCircuitSize 11 (fun x => F1 (Function.update x a false)) s' := by
  have hfnc : ∃ x y : Fin 11 → Bool, F1 x ≠ F1 y := by
    obtain ⟨x, x', h⟩ := hnc false
    exact ⟨_, _, h⟩
  obtain ⟨gs, o, L, hlen⟩ := exists_least 11 F1 s hfnc hC
  obtain ⟨q, hq⟩ := L.dep_read a hd hnc
  obtain ⟨s', hs', hc⟩ := L.save a false (hnc false) {q} (by
    intro p hp
    rw [Finset.mem_singleton] at hp
    subst hp
    exact rc_input false hq)
  refine ⟨s', ?_, hc⟩
  rw [Finset.card_singleton] at hs'
  omega

theorem resM0 (y a : Fin 11) : (fun x => fT (Function.update (Function.update x a false) y false))
    = F (delV Th ({y} ∪ {a})) ∅ := by
  funext x
  rw [fT_eq]
  rw [PEqualNP.MetaComplexity.Loc.Res.ToolRes0_proof 11 Th ∅ y _ (Finset.notMem_empty y),
    PEqualNP.MetaComplexity.Loc.Res.ToolRes0_proof 11 _ ∅ a x (Finset.notMem_empty a), delV_eq, delV_eq, delV_eq,
    delVerts_delVerts]

theorem resM1 (y : Fin 11) (N : Finset (Fin 11)) (hN : ∀ w, Th.Adj y w ↔ w ∈ N) :
    (fun x => fT (Function.update x y true)) = F (delV Th (insert y N)) (∅ ∪ N) := by
  funext x
  rw [fT_eq]
  exact PEqualNP.MetaComplexity.Loc.Res.ToolRes1_proof 11 Th ∅ y N x (Finset.notMem_empty y) hN

theorem bMf (y a : Fin 11) (X : Finset (Fin 11)) (hX : X = {y} ∪ {a})
    (hd : Dep (fun x => fT (Function.update x y false)) a)
    (hnc : NCy (fun x => fT (Function.update x y false)) a)
    (hP : Peelable (delVerts Th X)) (hE : (delVerts Th X).edgeFinset.card = 9)
    (hk : ∀ T, Cov (delVerts Th X) T → 4 ≤ T.card) (s' : ℕ)
    (hC : HasCircuitSize (10 + 1) (fun x => fT (Function.update x y false)) s') :
    16 ≤ s' + 3 := by
  obtain ⟨s'', hs'', hc⟩ := one_gate _ a s' hd hnc hC
  rw [resM0, ← hX] at hc
  have := bnd X ∅ 9 4 s'' hP (fun i _ _ => Finset.notMem_empty i) hE hk hc
  simp at this
  omega

theorem bMt (y : Fin 11) (N : Finset (Fin 11)) (hN : ∀ w, Th.Adj y w ↔ w ∈ N)
    (hP : Peelable (delVerts Th (insert y N)))
    (hA : ∀ i j, (delVerts Th (insert y N)).Adj i j → i ∉ ∅ ∪ N) (hcard : (∅ ∪ N).card = 2)
    (hE : (delVerts Th (insert y N)).edgeFinset.card = 8)
    (hk : ∀ T, Cov (delVerts Th (insert y N)) T → 4 ≤ T.card) (s' : ℕ)
    (hC : HasCircuitSize (10 + 1) (fun x => fT (Function.update x y true)) s') :
    16 ≤ s' + 3 := by
  rw [resM1 y N hN] at hC
  have := bnd _ _ 8 4 s' hP hA hE hk hC
  omega

theorem bM : ∀ y ∈ Mset, ∀ (b : Bool) (s' : ℕ), HasCircuitSize (10 + 1)
    (fun x => fT (Function.update x y b)) s' → 16 ≤ s' + 3 := by
  intro y hy b s' hC
  simp only [Mset, Finset.mem_insert, Finset.mem_singleton] at hy
  rcases hy with rfl | rfl | rfl <;> cases b
  · exact bMf 3 2 {3, 2} (by decide) ⟨fun i => decide (i = 0), by decide⟩
      (fun b => ⟨fun _ => false, fun _ => true, by revert b; decide⟩)
      (peelable_of _ 2 (by decide) peel2) (by decide)
      (cov_match _ 4 ![0, 6, 1, 8] ![5, 7, 10, 9] (by decide) (by decide)) s' hC
  · exact bMt 3 {2, 4} (by decide) (peelable_of _ 2 (by decide) peel2) (by decide)
      (by decide) (by decide)
      (cov_match _ 4 ![0, 6, 1, 8] ![5, 7, 10, 9] (by decide) (by decide)) s' hC
  · exact bMf 6 5 {6, 5} (by decide) ⟨fun i => decide (i = 0), by decide⟩
      (fun b => ⟨fun _ => false, fun _ => true, by revert b; decide⟩)
      (peelable_of _ 5 (by decide) peel5) (by decide)
      (cov_match _ 4 ![0, 3, 1, 8] ![2, 4, 10, 9] (by decide) (by decide)) s' hC
  · exact bMt 6 {5, 7} (by decide) (peelable_of _ 5 (by decide) peel5) (by decide)
      (by decide) (by decide)
      (cov_match _ 4 ![0, 3, 1, 8] ![2, 4, 10, 9] (by decide) (by decide)) s' hC
  · exact bMf 9 8 {9, 8} (by decide) ⟨fun i => decide (i = 0), by decide⟩
      (fun b => ⟨fun _ => false, fun _ => true, by revert b; decide⟩)
      (peelable_of _ 8 (by decide) peel8) (by decide)
      (cov_match _ 4 ![0, 3, 1, 5] ![2, 4, 7, 6] (by decide) (by decide)) s' hC
  · exact bMt 9 {8, 10} (by decide) (peelable_of _ 8 (by decide) peel8) (by decide)
      (by decide) (by decide)
      (cov_match _ 4 ![0, 3, 1, 5] ![2, 4, 7, 6] (by decide) (by decide)) s' hC

def bx (k : ℕ) : Fin 11 → Bool := fun i => k.testBit i.val

def nfw : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 8, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 8, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 1, 1, 1, 1, 4, 4, 4, 4, 2, 2, 2, 2, 1, 1, 1, 1, 4, 4, 4, 4, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 2, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 8, 2, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 8, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 8, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 64, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 4, 4, 4, 4, 2, 2, 2, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 1, 1, 1, 1, 32, 32, 32, 32, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 8, 2, 2, 2, 1, 1, 1, 1, 0, 0, 0, 2, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 64, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 8, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 64, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 4, 4, 4, 4, 2, 2, 2, 2, 1, 1, 1, 1, 32, 32, 32, 32, 2, 2, 2, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 8, 2, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 64, 2, 2, 2, 1, 1, 1, 1, 0, 0, 0, 2, 0, 0, 0, 0]

def sepw : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 8, 10, 1, 3, 4, 6, 17, 0, 8, 2, 9, 3, 64, 66, 1, 3, 32, 34, 129, 0, 64, 2, 65, 3, 512, 514, 1, 3, 256, 258, 1025, 0, 512, 2, 513, 3]

def depw : List ℕ := [0, 0, 1, 4, 2, 1, 32, 2, 1, 256, 2]

set_option maxRecDepth 100000 in
theorem nf_key : ∀ p ∈ Dset, ∀ q ∈ Dset, p ≠ q → ∀ a b : Bool,
    ¬ (fT (set2 (bx (nfw.getD (p.val * 44 + q.val * 4 + a.toNat * 2 + b.toNat) 0)) p (!a) q b) =
        fT (set2 (bx (nfw.getD (p.val * 44 + q.val * 4 + a.toNat * 2 + b.toNat) 0)) p a q (!b)) ∧
      fT (set2 (bx (nfw.getD (p.val * 44 + q.val * 4 + a.toNat * 2 + b.toNat) 0)) p a q (!b)) =
        fT (set2 (bx (nfw.getD (p.val * 44 + q.val * 4 + a.toNat * 2 + b.toNat) 0)) p (!a)
          q (!b))) := by
  decide

theorem sep_key : ∀ y ∈ Dset, ∀ c0 c1 : Bool, (y ∈ Oset ∨ c0 = false ∨ c1 = false) →
    bx (sepw.getD (y.val * 4 + c0.toNat * 2 + c1.toNat) 0) 0 = c0 ∧
    bx (sepw.getD (y.val * 4 + c0.toNat * 2 + c1.toNat) 0) 1 = c1 ∧
    fT (Function.update (bx (sepw.getD (y.val * 4 + c0.toNat * 2 + c1.toNat) 0)) y false) ≠
      fT (Function.update (bx (sepw.getD (y.val * 4 + c0.toNat * 2 + c1.toNat) 0)) y true) := by
  decide

theorem dep_key : ∀ y ∈ Dset, fT (Function.update (bx (depw.getD y.val 0)) y
    (!bx (depw.getD y.val 0) y)) ≠ fT (bx (depw.getD y.val 0)) := by
  decide

theorem nc_key : ∀ (y : Fin 11) (b : Bool), fT (Function.update (fun _ => false) y b) ≠
    fT (Function.update (fun _ => true) y b) := by
  decide

theorem main (s : ℕ) (hC : HasCircuitSize 11 fT s) : 16 ≤ s := by
  refine circ (n := 10) fT Dset Oset Mset 0 1 16 s (by decide) (by decide) (by decide)
    (by decide) (by decide) (fun y _ b => ⟨_, _, nc_key y b⟩) (fun b => ⟨_, _, nc_key 0 b⟩)
    ?_ (fun y hy => ⟨_, dep_key y hy⟩) ⟨2, by decide⟩ ?_ ?_ ⟨bx 4, by decide, by decide⟩
    bO bM b0 hC
  · rintro p hp q hq hpq ⟨a, b, h⟩
    exact nf_key p hp q hq hpq a b (h _)
  · intro y hy c0 c1
    have hyD : y ∈ Dset := by
      simp only [Oset, Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact ⟨_, sep_key y hyD c0 c1 (Or.inl hy)⟩
  · intro y hy c0 c1 hc
    have hyD : y ∈ Dset := by
      simp only [Mset, Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl | rfl <;> decide
    exact ⟨_, sep_key y hyD c0 c1 (Or.inr hc)⟩

end Theta

end PEqualNP.Outside.LM657

theorem PEqualNP.Outside.L_meta_657 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 11 (fun x : Fin 11 → Bool => (x 0 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 1) || (x 0 && x 5) || (x 5 && x 6) || (x 6 && x 7) || (x 7 && x 1) || (x 0 && x 8) || (x 8 && x 9) || (x 9 && x 10) || (x 10 && x 1)) s → 16 ≤ s :=
  fun s h => PEqualNP.Outside.LM657.main s h
