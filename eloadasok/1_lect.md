# Ellentmondásmentességi alak

**Tétel** -- Gödel--Rosser, 1936 -- Legyen PA a Peano-aritmetika axiómarendszere, legyen K olyan axiómarendszer, amely PA bővítése és amely rekurzív és ellentmondásmentes. Ekkor létezik (konstruálható) olyan G mondat a PA nyelvén, amelyre teljesül, hogy

1. [![\\ K\!\not\,\vdash G ](https://latex.codecogs.com/svg.latex?%5C%5C%20K%5C!%5Cnot%5C%2C%5Cvdash%20G%20)](#_) és
2. [![\\ K\!\not\,\vdash \neg G ](https://latex.codecogs.com/svg.latex?%5C%5C%20K%5C!%5Cnot%5C%2C%5Cvdash%20%5Cneg%20G%20)](#_). 

## Fogalmak magyarázata

### Peano-aritmetika

A természetes számok következő axiomatikus felépítése: 

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

PA lényegében az az elmélet, ami arra jó, amire a számelmélet (oszthatóság, prímszámok, egyértelmű prímfaktorizáció). Lényeges, hogy elsőrendű elmélet abban az értelemben, hogy csak tárgya (természetes számok) felett képes kvantifikálni. Azok a dolgok, amikről beszél számok és nem számok halmazai vagy függvényei. Körmönfont módon bizonyos részhalmazokról PA-ban lehet utalni, pl. egy diafantikus egyenlet megoldáshalmazáról (pl.: { (x,y,z) | 2x + 3y = 7z } számhármasok halmaza), de nem korlátlanul.

### Rekurzivitás

Egy halmaz (a természetes számok egy részhalmaza) rekurzív, ha létezik olyan véges eljárás, amely véges időben eldönti, hogy bármely dolog benne van-e a halmazban vagy sem (az ilyen algoritmikus problémák halmaza az R bonyolultsági osztály, a legbővebb algoritmikus bonyolultsági osztály). Ha úgy tetszik f rekurzív számelméleti függvény (totálisan rekurzív), ha létezik olyan véges algoritmus, ami bármely értékét véges lépésben kiszámítja. Egy halmaz ilyen értelemben rekurzív, ha a karakterisztikus függvénye rekurzív. 

Ennek egy spéci esete PR, a primitív rekurzív függvények halmaza. Ezek olyan függvények, amik esetén létezik olyan rekurzív függvény, amelyik minden elem esetén megmondja, hogy hány lépésben lehet kiszámítani a függvényt azon a helyen. Ez azért fontos osztály, mert ezek a bolodbiztosan kiszámítható függvények. Ezekről beszél az eredeti Gödel-cikk.

R-nél bővebb algoritmikusan megfogalmazható eldöntési problémák halmaza a _félig eldönthető problémák._ Ezek olyan számelméleti függvényekkel azonosíthatók, amelyek nem mindenhol vannak értelmezve, de van egy eljárás, amely véges lépésben kiszámítha bármely értelmes értékét. 

### Ellentmondásmentesség

Egy S logikai levezetési rendszer (formálisan, nyelvileg, betonbiztosan) _elletmondásmentes_ (ellentmondástalan, widerspruchsfreiheit), ha nincs olyan A mondat S nyelvében, amire S |- A **és** S |- ~A. 

(Néha _konzisztensnek_ nevezik, de ez utóbbi egy úgy halmazelméleti, modellelméleti fogalom. Ha tanulnánk modellelméletet, amit lehet, hogy egy picit tanulunk, akkor tudnak lenni teljességi tételek, ami azt mondják, hogy az ellentmondásmentesség ekvivalens a konzisztenciával. Mi alapvetően bizonyításelméletet, típuselméletet és kategóriaelméletet tanulunk. A Curry--Howard--Lambek-izomorfizmus szerint ez utóbbi három lényegében ugyanaz a matematikai keretrendszer. Ettől élesen elválik a modellemélet, ami a halmazelmélet egy része. 

A halmazelméletet sokszor _ZFC_-nek választják, **Z**ermelo-**F**raenkel (set theory with the axiom of) **C**hoice. Óriási koncepcionális különbség van a ZFC és a Curry--Howard--Lambek-izomorfizmus világ a között. Halmazba összegyűjteni szoktunk dolgokat, amelyek egy tulajdonságnak megfelelnek. A típus elemeit legyártjuk, felépítjük, megkonstruáljuk.)

## Problémák az eldönthetetlen mondatok igazságértékével

Egy olyan mondat, amire se K |- A, se K |- ~A nem teljesül, eldönthetetlen K-ban. Itt A tehát olyan eldöntendő kérdés, amire K nem tud válaszolni. De ha eldöntendő, akkor azért vagy igaz vagy hamis, nem?

### Megfelelés a valóságnak

G tartalmát tekinte olyan lesz, ami azt mondja: "ez a mondat nem levezethető". Mivel ez igaz, ezért G igaz. Egy mondat pontosan akkor igaz, ha a valóságban az van, amit mond. Ez az elv (korreszpondencia elv) a bivalencia elvével (egy mondat igaz vagy hamis, de sosem egyszerre) ellentmondást okoz: "ez a mondat hamis" (a hazug paradoxona).  

### Episztemológiai modalitás

Valami igaz, ha igazolhatóan igaz, a többi helyet valamilyen értelemben hamis vagy mert lehetetlen igazolni, vagy mert még nem igazolta senki.

### Metafizikai igazolás


