import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 0 in
set_option maxRecDepth 8000 in
theorem PEqualNP.Outside.R_meta_3541_1
    (compile : let op := fun (w : List Nat) (x : Nat) => ∃ a ∈ (0::w), ∃ b ∈ (0::w), x=a &&& b ∨ x=a ||| b
    let valid := fun (w xs : List Nat) => ∀ i : Fin xs.length, op (w++xs.take i.val) (xs.get i)
    let step := fun (w : List Nat) (z : Nat) => w++[if z<4096 then w.getD (z % 64) 0 &&& w.getD (z / 64 % 64) 0 else w.getD (z % 64) 0 ||| w.getD (z / 64 % 64) 0]
    ∀ (w xs : List Nat) (y : Nat), w.length=16 → xs.length≤23 → valid w xs → op (w++xs) y →
      ∃ zs : List (Fin 8192), zs.length≤24 ∧ ((zs.map Fin.val).foldl step w).getD (15+zs.length) 0=y)
    (search : let op := fun (w : List Nat) (x : Nat) => ∃ a ∈ (0::w), ∃ b ∈ (0::w), x=a &&& b ∨ x=a ||| b
    let valid := fun (w xs : List Nat) => ∀ i : Fin xs.length, op (w++xs.take i.val) (xs.get i)
    let raw : List Nat := [95229015649943559, 63038587666488, 256462815680, 4292497062759936, 8521481482240, 14003410187812864, 55389823207997440, 189297016294081033, 155696362464477250, 218994303132270608, 183565875465490436, 229736628138025984, 270286071508633728, 288160007407550752]
    ∃ (i : Fin 59) (xs : List Nat),
      let d := (226131379097400301252716726621337676406640570459594802058434200882244816316059964149557119437365627524128536685985871902300658673893597245207666400755673936233446394815901165690001459735446107557489143507355871795847806551060195304461518452092617615 >>> (14*i.val)) % 16384
      let c := d / 4
      let z := if d % 4 ≥ 2 then raw.getD 0 0 ||| raw.getD (c/225 % 14) 0 else raw.getD 0 0 &&& raw.getD (c/225 % 14) 0
      let u := (raw++[z]).getD (c % 225 / 15) 0
      let v := (raw++[z]).getD (c % 15) 0
      let bank := raw++[z,if d % 2 = 1 then u ||| v else u &&& v]
      xs.length≤23 ∧ valid bank xs ∧ op (bank++xs) 2097151 ∧
      ∀ j : Fin xs.length, ∀ t ∈ 0::(bank++xs.take j.val),
        (t ^^^ 2097151) &&& (xs.get j ^^^ 2097151) ≠ (t ^^^ 2097151)) : have x1 : List ℕ := [(95229015649943559 : ℕ), (63038587666488 : ℕ), (256462815680 : ℕ), (4292497062759936 : ℕ), (8521481482240 : ℕ), (14003410187812864 : ℕ), (55389823207997440 : ℕ), (189297016294081033 : ℕ), (155696362464477250 : ℕ), (218994303132270608 : ℕ), (183565875465490436 : ℕ), (229736628138025984 : ℕ), (270286071508633728 : ℕ), (288160007407550752 : ℕ)]; have x2 : List ℕ → ℕ → List ℕ := fun (x2 : List ℕ) (x3 : ℕ) => x2 ++ [if x3 < (4096 : ℕ) then x2.getD (x3 % (64 : ℕ)) (0 : ℕ) &&& x2.getD (x3 / (64 : ℕ) % (64 : ℕ)) (0 : ℕ) else x2.getD (x3 % (64 : ℕ)) (0 : ℕ) ||| x2.getD (x3 / (64 : ℕ) % (64 : ℕ)) (0 : ℕ)]; have x3 : ℕ → ℕ → Bool → ℕ := fun (x3 x4 : ℕ) (x5 : Bool) => x3 + (64 : ℕ) * x4 + if x5 = Bool.true then (4096 : ℕ) else (0 : ℕ); ∃ (x4 : Fin (65 : ℕ)) (x5 : Bool) (x6 : Bool) (x7 : List (Fin (8192 : ℕ))),   x7.length ≤ (24 : ℕ) ∧     have x8 : ℕ := ([[(226 : ℕ), (227 : ℕ), (228 : ℕ), (232 : ℕ), (233 : ℕ), (234 : ℕ), (236 : ℕ), (239 : ℕ), (258 : ℕ), (259 : ℕ), (260 : ℕ), (262 : ℕ), (263 : ℕ)], [(264 : ℕ), (266 : ℕ), (267 : ℕ), (269 : ℕ), (277 : ℕ), (278 : ℕ), (281 : ℕ), (284 : ℕ), (338 : ℕ), (341 : ℕ), (344 : ℕ), (354 : ℕ), (355 : ℕ)], [(356 : ℕ), (359 : ℕ), (402 : ℕ), (404 : ℕ), (1576 : ℕ), (1577 : ℕ), (1582 : ℕ), (1583 : ℕ), (1584 : ℕ), (1589 : ℕ), (1592 : ℕ), (1593 : ℕ), (1598 : ℕ)], [(1599 : ℕ), (1601 : ℕ), (1604 : ℕ), (1609 : ℕ), (1611 : ℕ), (1614 : ℕ), (1617 : ℕ), (1619 : ℕ), (2026 : ℕ), (2027 : ℕ), (2032 : ℕ), (2034 : ℕ), (2036 : ℕ)], [(2039 : ℕ), (2042 : ℕ), (2043 : ℕ), (2045 : ℕ), (2047 : ℕ), (2048 : ℕ), (2051 : ℕ), (2053 : ℕ), (2054 : ℕ), (2058 : ℕ), (2066 : ℕ), (2067 : ℕ), (2069 : ℕ)]].getD (↑x4 / (13 : ℕ)) []).getD (↑x4 % (13 : ℕ)) (0 : ℕ);     have x9 : List ℕ := x3 (0 : ℕ) (↑(Fin.ofNat (14 : ℕ) (x8 / (225 : ℕ)))) x5 :: x3 (↑(Fin.ofNat (15 : ℕ) (x8 % (225 : ℕ) / (15 : ℕ)))) (↑(Fin.ofNat (15 : ℕ) (x8 % (15 : ℕ)))) x6 :: List.map Fin.val x7;     (List.foldl x2 x1 x9).getD ((13 : ℕ) + x9.length) (0 : ℕ) = (2097151 : ℕ) := by
  let raw : List Nat := [95229015649943559, 63038587666488, 256462815680, 4292497062759936, 8521481482240, 14003410187812864, 55389823207997440, 189297016294081033, 155696362464477250, 218994303132270608, 183565875465490436, 229736628138025984, 270286071508633728, 288160007407550752]
  let step := fun (w : List Nat) (z : Nat) => w++[if z<4096 then w.getD (z % 64) 0 &&& w.getD (z / 64 % 64) 0 else w.getD (z % 64) 0 ||| w.getD (z / 64 % 64) 0]
  let op := fun (w : List Nat) (x : Nat) => ∃ a ∈ (0::w), ∃ b ∈ (0::w), x=a &&& b ∨ x=a ||| b
  let valid := fun (w xs : List Nat) => ∀ i : Fin xs.length, op (w++xs.take i.val) (xs.get i)
  let encode (a b : Nat) (d : Bool) := a+64*b+if d then 4096 else 0
  let code (k : Fin 65) : Nat := (([[226, 227, 228, 232, 233, 234, 236, 239, 258, 259, 260, 262, 263], [264, 266, 267, 269, 277, 278, 281, 284, 338, 341, 344, 354, 355], [356, 359, 402, 404, 1576, 1577, 1582, 1583, 1584, 1589, 1592, 1593, 1598], [1599, 1601, 1604, 1609, 1611, 1614, 1617, 1619, 2026, 2027, 2032, 2034, 2036], [2039, 2042, 2043, 2045, 2047, 2048, 2051, 2053, 2054, 2058, 2066, 2067, 2069]] : List (List Nat)).getD (k.val/13) []).getD (k.val % 13) 0
  let descriptor (i : Fin 59) : Nat := (226131379097400301252716726621337676406640570459594802058434200882244816316059964149557119437365627524128536685985871902300658673893597245207666400755673936233446394815901165690001459735446107557489143507355871795847806551060195304461518452092617615 >>> (14*i.val)) % 16384
  let slot (i : Fin 59) : Nat := (3562708658556365641650257115941975631549887717527046887694613480084079508532766641880867576340888461434485527450761225063906376547662661069992472883782812964359 >>> (9*i.val)) % 512
  let pos (i : Fin 59) := Fin.ofNat 65 (slot i/4)
  let pair (i : Fin 59) : List Nat :=
    let c := code (pos i)
    [encode 0 (Fin.ofNat 14 (c/225)).val (decide (slot i % 4 ≥ 2)),
     encode (Fin.ofNat 15 (c % 225 / 15)).val (Fin.ofNat 15 (c % 15)).val (decide (slot i % 2 = 1))]
  let bank (i : Fin 59) : List Nat :=
    let d := descriptor i
    let c := d/4
    let z := if d % 4 ≥ 2 then raw.getD 0 0 ||| raw.getD (c/225 % 14) 0 else raw.getD 0 0 &&& raw.getD (c/225 % 14) 0
    let u := (raw++[z]).getD (c % 225 / 15) 0
    let v := (raw++[z]).getD (c % 15) 0
    raw++[z,if d % 2=1 then u ||| v else u &&& v]
  have same : ∀ i, (pair i).foldl step raw=bank i := by decide +kernel
  have length : ∀ i, (bank i).length=16 := by decide +kernel
  change ∀ (w xs : List Nat) (y : Nat), w.length=16 → xs.length≤23 → valid w xs → op (w++xs) y →
    ∃ zs : List (Fin 8192), zs.length≤24 ∧ ((zs.map Fin.val).foldl step w).getD (15+zs.length) 0=y at compile
  change ∃ (i : Fin 59) (xs : List Nat), xs.length≤23 ∧ valid (bank i) xs ∧ op (bank i++xs) 2097151 ∧
    (∀ j : Fin xs.length, ∀ t ∈ 0::(bank i++xs.take j.val), (t ^^^ 2097151) &&& (xs.get j ^^^ 2097151) ≠ (t ^^^ 2097151)) at search
  obtain ⟨i,xs,short,validPath,finalGate,_⟩ := search
  obtain ⟨zs,le,hit⟩ := compile (bank i) xs 2097151 (length i) short validPath finalGate
  refine ⟨pos i,decide (slot i % 4≥2),decide (slot i % 2=1),zs,le,?_⟩
  change ((pair i++zs.map Fin.val).foldl step raw).getD (13+(pair i++zs.map Fin.val).length) 0=2097151
  rw [List.foldl_append,same,List.length_append,List.length_map]
  have two : (pair i).length=2 := rfl
  rw [two,show 13+(2+zs.length)=15+zs.length by omega]
  exact hit
