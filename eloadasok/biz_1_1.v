(*Nyelv: implikációs kijelentő mondatok*)

(* pusztán ha..., akkor...-ral

TrueS ∈ Sent

FalseS ∈ Sent

A ⊃ B ∈ Sent, ha A, B ∈ Sent *)

Inductive Sent : Set :=
  | TrueS : Sent 
  | FalseS : Sent 
  | Imp : Sent -> Sent -> Sent.

Infix "⊃" := Imp (at level 20, right associativity).

(*IMPLIKÁCIÓS LOGIKA*)

(*Hilbert-féle levezetési rendszer*)

(* Levezethetőség: Γ ⊢ A, ahol Γ állítások egy listája, A állítás.

Sok axióma, egy-két levezetési szabály.

"Ami igaz, az igaz" axióma:

⊢ (A ⊃ B ⊃ A)

"Láncszabály" axióma:

⊢ ((C ⊃ A ⊃ B) ⊃ (C ⊃ A) ⊃ (C ⊃ B))

"Modus ponens" levezetési szabály:

Γ ⊢ A ⊃ B és Γ ⊢ A, akkor Γ ⊢ B

Strukturális szabályok:

Γ ∪ {A} ⊢ A

Γ ⊢ A akkor Γ ∪ {B} ⊢ A
 *)


Inductive PrHilb : list Sent -> Sent -> Prop :=
  | strZ : forall G A, PrHilb (A :: G) A 
  | strS : forall G A B, PrHilb G A -> PrHilb (B :: G) A 
  | ax1 : forall G A B, PrHilb G (A ⊃ B ⊃ A)
  | ax2 : forall G A B C, PrHilb G ((C ⊃ A ⊃ B) ⊃ (C ⊃ A) ⊃ (C ⊃ B))
  | mp : forall G A B, PrHilb G (A ⊃ B) -> PrHilb G A -> PrHilb G B.

(* 

(A ⊃ (A ⊃ A) ⊃ A)

(A ⊃ (A ⊃ A) ⊃ A) ⊃ ( A ⊃ (A ⊃ A) ) ⊃ (A ⊃ A)

( A ⊃ (A ⊃ A) ) ⊃ (A ⊃ A)

(A ⊃ A)

*)

Notation "G '⊢Hilb' A" := (PrHilb G A) (at level 70, no associativity) : type_scope.

Notation "'⊢Hilb' A" := (PrHilb nil A) (at level 70, no associativity) : type_scope.

Theorem relfexive : forall A, ⊢Hilb (A ⊃ A).
Proof.
intros.
apply mp with (G:=nil) (A:=( A ⊃ (A ⊃ A) )) (B:=(A ⊃ A)) .
apply mp with (G:=nil) (A:=(A ⊃ (A ⊃ A) ⊃ A)) (B:=( A ⊃ (A ⊃ A) ) ⊃ (A ⊃ A)) .
apply ax2  with (G:=nil) (A:=(A ⊃ A)) (B:=A) (C:=A).
apply ax1.
apply ax1.
Qed.

(*Gentzen-féle levezetési rendszer*)

(* Nincsenek axiómák

"Modus ponens" levezetési szabály:

Γ ⊢ A ⊃ B és Γ ⊢ A, akkor Γ ⊢ B

"Dedukciótétel" levezetési szabály:

Γ ∪ {A} ⊢ B akkor Γ ⊢ A ⊃ B

Strukturális szabályok:

Γ ∪ {A} ⊢ A

Γ ⊢ A akkor Γ ∪ {B} ⊢ A

 *)


Inductive PrGent : list Sent -> Sent -> Prop :=
  | strZG : forall G A, PrGent (A :: G) A 
  | srtSG : forall G A B, PrGent G A -> PrGent (B :: G) A 
  | mpG : forall G A B, PrGent G (A ⊃ B) -> PrGent G A -> PrGent G B
  | dedG : forall G A B, PrGent (A :: G) B -> PrGent G (A ⊃ B).

(* 

{A} ⊢ A

(A ⊃ A)

*)

Notation "G '⊢Gent' A" := (PrGent G A) (at level 70, no associativity) : type_scope.

Notation "'⊢Gent' A" := (PrGent nil A) (at level 70, no associativity) : type_scope.

Theorem relfexiveG : forall A, ⊢Gent (A ⊃ A).
Proof.
intros.
apply dedG.
apply strZG.
Qed.

(*Un. másodrendű algebrai elméletként:*)

Class Imp_logic := mk_imp {

  Pf : Sent -> Prop;
  
  ded2nd : forall A B, (Pf A -> Pf B) -> Pf (A ⊃ B);
  mp2nd : forall A B, Pf (A ⊃ B) -> Pf A -> Pf B }.

Context (L : Imp_logic).

Theorem relfexiveS : forall A, Pf (A ⊃ A).
Proof.
intros.
apply mp2nd.
auto.
Qed.
  
Theorem eq1 : forall G A, (G ⊢Gent A) -> (G ⊢Hilb A).
Proof.
intros.
induction H.
apply strZ.
apply strS.
auto. 
apply mp with (A:=A).
all: auto.
Abort.
Qed.





