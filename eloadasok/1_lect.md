# Ellentmondásmentességi alak

**Tétel** -- Gödel--Rosser, 1936 -- Legyen PA a Peano-aritmetika axiómarendszere, legyen K olyan axiómarendszer, amely PA bővítése és amely rekurzív és ellentmondásmentes. Ekkor létezik (konstruálható) olyan G mondat a PA nyelvén, amelyre teljesül, hogy

1. [![\\ K\!\not\,\vdash G ](https://latex.codecogs.com/svg.latex?%5C%5C%20K%5C!%5Cnot%5C%2C%5Cvdash%20G%20)](#_) és
2. [![\\ K\!\not\,\vdash \neg G ](https://latex.codecogs.com/svg.latex?%5C%5C%20K%5C!%5Cnot%5C%2C%5Cvdash%20%5Cneg%20G%20)](#_). 

## Fogalmak magyarázata

Peano-aritmetika: a természetes számok következő axiomatikus felépítése: 

````coq
(* Ez az alábbi a PA-nak egy olyan implementációja, amelyben a nyelv nincs teljesen formalizálva,
 de az axiómák már újként "ráíródnak" a természetes számokra.*)


Structure PA := mk_PA {

  PA_1 : forall x : nat, ~ (0 = S x);

  PA_2 : forall x y : nat, S x =  S y -> x = y;

  PA_3 : forall x : nat, x + 0 = x;

  PA_4 : forall x y : nat, x + S y = S(x + y);

  PA_5 : forall x : nat, x * 0 = 0;

  PA_6 : forall x y : nat, x * S y = x * y + x;

  PA_7 : forall P : nat -> Prop, P 0 /\
(forall n : nat, P n -> P (S n) )-> forall n : nat, P n;  

}.

Context (Ari : PA).


(* Ebben a furcsa algebrában az axiómák alapján
igazolni lehet más tételeket.*)


Theorem zero_left_PA : forall x : nat, 0 + x = x.
Proof.
  (* Feltételes állítás feltételének áttolása premisszákhoz.*)
  intros x.

  (* Indukciós elv alkalmazása *)
  apply (PA_7 Ari (fun n => 0 + n = n)).

  (* Esetenként.*)
  split.

  (* Kezdő lépés: P(0).*)
  - apply (PA_3).
    exact Ari.

  (* Indukciós lépés: P(n) -> P(S n) *)
  - intros n H.
    
    (* PA_4 egyenlőség alkalmazása *)
    rewrite (PA_4 Ari 0 n).
    
    (* A hipotézis alapján az egyenlőség *)
    rewrite H.
    reflexivity.
Qed.

(*Az elméleti számítástudományban nem ez PA természetes setupja,
hanem egy komputációsan értelmes adatruktúra, ahol az adattípusra
vonatkozó "axiómák" összhangban vannak azzal, ahogy az adatokon a
függvények kiszámolódnak.*)

Theorem zero_left_nat : forall x : nat, 0 + x = x.
Proof.
auto.
Qed.
````


````
