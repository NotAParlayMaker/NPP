import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.R_meta_5176_676
    (compiler :
    ∀ n (C : Circuit), PEqualNP.TopForm.IsAO2 n C →
    ∀ D : Set ℕ → Set ℕ → Set ℕ, ∃ w : ℕ → Set ℕ,
      (∀ i : Fin n, w i.val = {m | m.testBit i.val = true}) ∧
      (∀ i, n + C.size ≤ i → w i = ∅) ∧
      (∀ j g a b, C.gates[j]? = some g → g.inputs = [a,b] →
        (g.op = GateOp.and → w (n+j) = D (w a) (w b)) ∧
        (g.op = GateOp.or → w (n+j) = w a ∪ w b)) ∧
      ∀ m : ℕ, (∀ a b, m ∈ D a b ↔ m ∈ a ∩ b) → ∀ i,
        m ∈ w i ↔ (C.wires (List.ofFn fun k : Fin n => m.testBit k.val)).getD i false = true)
    (safe :
    let ok := fun (a b : Set ℕ) (s x y : ℕ) => s ∈ a ∪ b ∨ x ∈ a ∩ b ∨ y ∈ a ∩ b
    let D := fun a b : Set ℕ => {m ∈ a ∩ b |
      (m = 92143615 → ok a b 1 8191 25018369) ∧ (m = 134217205 → ok a b 8192 67100672 15860)}
    let G := {m : ℕ | m ∉ ([92143615,134217205] : List ℕ) ∧ ∃ p l : Fin 13,
      (p=l ∨ p=l+1 ∨ p=l+3 ∨ p=l+9) ∧ m.testBit p.val = true ∧ m.testBit (13+l.val) = true}
    ∃ U : Set (Multiset (Set ℕ)),
      (Multiset.range 26).map (fun i => {m : ℕ | m.testBit i = true}) ∈ U ∧
      (∀ K ∈ U, K.card < 90 → ∀ a b, a ::ₘ b ::ₘ 0 ≤ K →
        ((a ∪ b) ::ₘ K) ∈ U ∧ ((D a b) ::ₘ K) ∈ U) ∧
      ∀ K ∈ U, G ∉ K) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   (63 : ℕ) ≤ x1.size →     x1.size ≤ (64 : ℕ) →       PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 →         (∀ x5 ∈ x1.gates, x5.inputs.Nodup) →           (∀ (x6 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x6) = Bool.true ↔ ∃ (x7 : Fin (13 : ℕ)) (x8 : Fin (13 : ℕ)), (x7 = x8 ∨ x7 = x8 + (1 : Fin (13 : ℕ)) ∨ x7 = x8 + (3 : Fin (13 : ℕ)) ∨ x7 = x8 + (9 : Fin (13 : ℕ))) ∧ x6 (Fin.castAdd (13 : ℕ) x7) = Bool.true ∧ x6 (Fin.natAdd (13 : ℕ) x8) = Bool.true) →             have x7 : ℕ → ℕ → Bool := fun (x7 x8 : ℕ) => (x1.wires (List.ofFn fun (x9 : Fin (26 : ℕ)) => x7.testBit ↑x9)).getD x8 Bool.false;             ∃ x8 ∈ [(0 : ℕ), (13 : ℕ)],               have x9 : ℕ := if x8 = (0 : ℕ) then (25034751 : ℕ) else (67108341 : ℕ);               have x10 : ℕ := if x8 = (0 : ℕ) then (8191 : ℕ) else (67100672 : ℕ);               have x11 : ℕ := if x8 = (0 : ℕ) then (25018369 : ℕ) else (15860 : ℕ);               ∀ (x12 : Set ℕ), x1.output ∈ x12 → (∀ (x14 : Fin (26 : ℕ)), ↑x14 ∈ x12 → x9.testBit ↑x14 = Bool.false) → ¬∀ (x15 : ℕ) (x16 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x15]? = Option.some x16 → (26 : ℕ) + x15 ∈ x12 → (x16.op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ x20 ∈ x16.inputs, x20 ∈ x12) ∧ (x16.op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ x20 ∈ x16.inputs, x20 ∈ x12) ∨ (∀ x20 ∈ x16.inputs, x7 ((2 : ℕ) ^ x8) x20 = Bool.false) ∧ x7 x10 ((26 : ℕ) + x15) = Bool.false ∧ x7 x11 ((26 : ℕ) + x15) = Bool.false) := by
  classical
  intro C _ hi model nodup spec
  let ok := fun (a b : Set ℕ) (s x y : ℕ) => s ∈ a ∪ b ∨ x ∈ a ∩ b ∨ y ∈ a ∩ b
  let D := fun a b : Set ℕ => {m ∈ a ∩ b |
    (m = 92143615 → ok a b 1 8191 25018369) ∧ (m = 134217205 → ok a b 8192 67100672 15860)}
  let G := {m : ℕ | m ∉ ([92143615,134217205] : List ℕ) ∧ ∃ p l : Fin 13,
    (p=l ∨ p=l+1 ∨ p=l+3 ∨ p=l+9) ∧ m.testBit p.val = true ∧ m.testBit (13+l.val) = true}
  obtain ⟨w,inp,missing,gate,proj⟩ := compiler 26 C model D
  obtain ⟨U,base,move,exclude⟩ := safe
  let val (m k : ℕ) := (C.wires (List.ofFn fun i : Fin 26 => m.testBit i.val)).getD k false
  have live (m : ℕ) (hm : m ∉ ([92143615,134217205] : List ℕ)) (i : ℕ) :
      m ∈ w i ↔ val m i = true := by
    apply proj
    obtain ⟨ha,hb⟩ : m ≠ 92143615 ∧ m ≠ 134217205 := by simpa using hm
    intro a b
    simp [D,ha,hb]
  have desc (j : ℕ) (hj : j < C.size) :
      ∃ g a b, C.gates[j]? = some g ∧ g.inputs = [a,b] ∧ a ≠ b ∧ a < 26+j ∧ b < 26+j ∧
        (g.op = GateOp.and ∨ g.op = GateOp.or) := by
    let g := C.gates[j]'hj
    have mem : g ∈ C.gates := List.getElem_mem _
    obtain ⟨a,b,ins⟩ := List.length_eq_two.mp (model.2.2 g mem)
    have back (i) (h : i ∈ g.inputs) : i < 26+j := by
      apply model.2.1 j hj
      change i ∈ (C.gates.getD j _).inputs
      rwa [List.getD_eq_getElem _ _ hj]
    exact ⟨g,a,b,List.getElem?_eq_getElem hj,ins,by simpa [ins] using nodup g mem,
      back a (by simp [ins]), back b (by simp [ins]), model.1 g mem⟩
  let bag (j : ℕ) := (Multiset.range (26+j)).map w
  have bags (j : ℕ) (hj : j ≤ C.size) : bag j ∈ U := by
    induction j with
    | zero =>
      change (Multiset.range 26).map w ∈ U
      convert base using 1
      apply Multiset.map_congr rfl
      intro i h
      exact inp ⟨i,Multiset.mem_range.mp h⟩
    | succ j ih =>
      obtain ⟨g,a,b,hit,ins,ne,ha,hb,tag⟩ := desc j (by omega)
      have hpair : a ::ₘ b ::ₘ (0 : Multiset ℕ) ≤ Multiset.range (26+j) := by
        apply (Multiset.le_iff_subset (by simp [ne])).2
        intro k hk
        rcases (show k=a ∨ k=b by simpa using hk) with rfl | rfl
        · exact Multiset.mem_range.mpr ha
        · exact Multiset.mem_range.mpr hb
      have pair : w a ::ₘ w b ::ₘ 0 ≤ bag j := by simpa [bag] using Multiset.map_le_map (f := w) hpair
      have next := move (bag j) (ih (by omega)) (by simp [bag]; omega) (w a) (w b) pair
      change (Multiset.range ((26+j)+1)).map w ∈ U
      rw [Multiset.range_succ,Multiset.map_cons]
      rcases tag with h | h
      · rw [(gate j g a b hit ins).1 h]
        exact next.2
      · rw [(gate j g a b hit ins).2 h]
        exact next.1
  have known := exclude (bag C.size) (bags _ (le_refl _))
  have actual (m : ℕ) (hm : m ∉ ([92143615,134217205] : List ℕ)) :
      m ∈ w C.output ↔ m ∈ G := by
    rw [live m hm]
    exact (spec _).trans ⟨fun h => ⟨hm,h⟩,fun h => h.2⟩
  have pos : 8193 ∈ w C.output := by
    apply (actual _ (by decide)).2
    exact ⟨by decide,0,0,Or.inl rfl,by decide,by decide⟩
  have bound : C.output < 26 + C.size := by
    by_contra! h
    rw [missing _ h] at pos
    exact pos
  have outmem : w C.output ∈ bag C.size := Multiset.mem_map.mpr ⟨_,Multiset.mem_range.mpr bound,rfl⟩
  have ghost : 92143615 ∈ w C.output ∨ 134217205 ∈ w C.output := by
    by_contra! h
    apply known
    have eq : w C.output = G := by
      ext m
      by_cases he : m ∈ ([92143615,134217205] : List ℕ)
      · rcases (show m=92143615 ∨ m=134217205 by simpa using he) with rfl | rfl
        · exact ⟨fun hh => (h.1 hh).elim,fun hh => (hh.1 he).elim⟩
        · exact ⟨fun hh => (h.2 hh).elim,fun hh => (hh.1 he).elim⟩
      · exact actual m he
    change G ∈ bag C.size
    rwa [← eq]
  obtain ⟨b,side,yes⟩ : ∃ b : ℕ, (b = 0 ∨ b = 13) ∧
      (if b=0 then 92143615 else 134217205) ∈ w C.output := by
    rcases ghost with h | h
    · exact ⟨0,Or.inl rfl,h⟩
    · exact ⟨13,Or.inr rfl,h⟩
  refine ⟨b,by simpa using side,?_⟩
  let z : ℕ := if b=0 then 92143615 else 134217205
  let u : ℕ := if b=0 then 25034751 else 67108341
  let x : ℕ := if b=0 then 8191 else 67100672
  let y : ℕ := if b=0 then 25018369 else 15860
  have bits : ∀ i : Fin 26, z.testBit i.val = u.testBit i.val := by
    rcases side with rfl | rfl <;> decide
  have clear : (2^b : ℕ) ∉ ([92143615,134217205] : List ℕ) ∧
      x ∉ ([92143615,134217205] : List ℕ) ∧ y ∉ ([92143615,134217205] : List ℕ) := by
    rcases side with rfl | rfl <;> decide
  dsimp only
  intro S root init close
  have sound (k : ℕ) (hk : k < 26+C.size) (hs : k ∈ S) : z ∉ w k := by
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      by_cases hi : k < 26
      · let i : Fin 26 := ⟨k,hi⟩
        change z ∉ w i.val
        rw [inp i]
        exact fun h => Bool.noConfusion ((init i hs).symm.trans ((bits i).symm.trans h))
      · let j := k-26
        have kj : k=26+j := by dsimp [j]; omega
        obtain ⟨g,a,c,hit,ins,_,ha,hc,tag⟩ := desc j (by omega)
        have cl := close j g hit (kj ▸ hs)
        have step := gate j g a c hit ins
        have ma : a ∈ g.inputs := by simp [ins]
        have mc : c ∈ g.inputs := by simp [ins]
        intro hz
        rw [kj] at hz
        rcases tag with t | t
        · rw [step.1 t] at hz
          rcases cl.2 t with ⟨i,mi,si⟩ | ⟨seed,dx,dy⟩
          · rcases (show i=a ∨ i=c by simpa [ins] using mi) with rfl | rfl
            · exact ih _ (by omega) (by omega) si hz.1.1
            · exact ih _ (by omega) (by omega) si hz.1.2
          · have force : ok (w a) (w c) (2^b) x y := by
              rcases side with rfl | rfl
              · exact hz.2.1 rfl
              · exact hz.2.2 rfl
            have dead (m : ℕ) (hm : m ∉ ([92143615,134217205] : List ℕ))
                (hmz : val m (26+j) = false) (h : m ∈ w a ∩ w c) : False := by
              apply Bool.noConfusion (hmz.symm.trans ((live m hm _).1 ?_))
              rw [step.1 t]
              refine ⟨h,?_,?_⟩
              · exact fun e => (hm (by simp [e])).elim
              · exact fun e => (hm (by simp [e])).elim
            rcases force with h | h | h
            · rcases h with h | h
              · exact Bool.noConfusion ((seed a ma).symm.trans ((live _ clear.1 _).1 h))
              · exact Bool.noConfusion ((seed c mc).symm.trans ((live _ clear.1 _).1 h))
            · exact dead x clear.2.1 dx h
            · exact dead y clear.2.2 dy h
        · rw [step.2 t] at hz
          rcases hz with h | h
          · exact ih _ (by omega) (by omega) (cl.1 t a ma) h
          · exact ih _ (by omega) (by omega) (cl.1 t c mc) h
  exact sound C.output bound root yes
