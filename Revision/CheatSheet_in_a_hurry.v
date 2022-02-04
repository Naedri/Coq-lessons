
(** types *)

(*Des types de la forme 3 A→B, où A et B sont deux types ;
 les types de cette forme sont appelés des types flèche.*)

(* Inférence de types Le typage explicite d’une λ-abstraction peut être omis
 dans certains cas où le contexte de cette expression suffit à le déterminer. *)

(** Définition vs.  Déclaration *)
(*
Une déclaration permet d’attacher un type à un identificateur, sans lui donner de valeur. 
Comme dans les fichiers d’interface de C ou Java, 
La déclaration d’un identificateur x de type A se note "(x : A)".

Une définition donne une valeur à un identificateur (typé) sous la forme d’un terme associé. 
La définition d’un identificateur x par un terme t de type A se note "(x := t : A)". 
*)

(** inférence de type *)
(*
Le typage explicite d’une λ-abstraction peut être omis dans certains cas 
où le contexte de cette expression suffit à le déterminer. 
*)


(** variable anonyme *)
(*
Dans une abstraction "fun v:A ⇒ t", 
il peut arriver que la variable v n’ait aucune occurrence libre dans t. 
Dans ce cas, on peut utiliser la variable anonyme "_" au lieu de v.
*)

(** Sorte *)
(*
on appelle sorte le type d’un type (considéré en tant que terme). 
Une sorte est toujours un identificateur. 

Si le type A d’un terme t est de sorte s, 
on dira de façon abrégée que t a pour sorte s.

Exemple
le type "nat→nat" est une spécification, 
celle des fonctions totales de nat dans nat.


les sortes "Set" et "Prop" sont au même niveau dans la hiérarchie des types 
Set a pour type : Type(0)
Prop a pour type : tous les univers Type(i).

type Prop : formule logique et demonstration
type Type : Structure de données et calcul 
*)

(*
En pratique, on utilisera deux "sort" : 
  + Prop pour les propositions,
  + Type pour les données
*) 



(** Propositions et preuves *)
(*
La démarche de Heyting remplace la question « La proposition P est-elle vraie ? » 
par la suivante : 
"Quelles sont les (éventuelles) preuves de P ?".
*)

(*
Selon Heyting, une preuve d’une implication P ⇒ Q 
est l’expression même de la relation de cause à effet liant P et Q, 
autrement dit 
"Comment une preuve de Q peut se déduire d’une preuve de P ?"

En d’autres termes, 
  une preuve de P ⇒ Q est une fonction qui, 
  étant donnée une preuve arbitraire de P , construit une preuve de Q.
*)


(*
L'implication de Heyting "P ⇒ Q"  devient "P → Q", 
une preuve de cette implication sera une simple abstraction de la forme "fun H:P ⇒ t", 
où t est un terme de type Q dans un contexte étendu par la déclaration (H:P ).
*)

(*
proposition A : "(P →Q)→(Q→R)→P →R"
preuve : "fun (H:P →Q)(H’:Q→R)(p:P ) ⇒ H’ (H p)"
  qui consiste à appliquer 
    H à p pour obtenir une preuve de Q, 
    puis à appliquer H’ à cette dernière preuve pour obtenir une preuve de R. 
*)


(** Définition p.79*)
(* 
Proposition, terme de preuve 
Hypothèse
Axiome
Jugement
But
Tactique
*)

(** check *)
(*whether a formula is well-formed.*)

Check False.
Check 3.
Check (3+4).
Check (3=5).
Check (3,4).
Check ((3=5)/\True).
Check nat -> Prop.
Check (3 <= 6).

(*Being explicit with type*)
Check (3,3=5):nat*Prop.

(** fun *)
Check (fun x:nat => x = 3).

(** forall *)

Check (forall x:nat, x < 3 \/ (exists y:nat, x = y + 3)).
(*For every natural number x, either x is less than 3 or there exists a natural number y such that x = y + 3*)

(** let .. in *) 
(*to give a temporary name to an expression*)
(*notation for applying a function f to a value, here 3,*)
Check (let f := fun x => (x * 3,x) in f 3).

(** Locate *)
(*can find the function hidden behind a notation*)
Locate "_ <= _".

(** Definition *)
(*to define a new constant by using the keyword Definition*) 
Definition example1 := fun x : nat => x*x+2*x+1.
Definition example1' (x : nat) := x*x+2*x+1.

(** Compute *)
(*to evaluate an expression*)
Compute let f := fun x => (x * 3, x) in f 3.
(*to use a given function*)
Compute example1 3.

(** Print *)
(*see the definition of an object*) 
Print example1.
Print le_S.
Print le.
(* Inductive le (n : nat) : nat -> Prop :=
    le_n : n <= n
  | le_S : forall m : nat, n <= m -> n <= S m. *)
(* statement of le S reads as : 
    for every n and m, numbers of type nat, 
    if n is less than or equal to m, 
    then n is less than or equal to the successor of m *)	

(** Reset *)
(*to forget a definition that you just made*) 
Reset example1'.

(** Require *)
(*boolean conditional expressions*) 
Require Import Bool.
Compute if true then 3 else 5.
(*Computing with natural numbers*) 
Require Import Arith.

(** match *)
(*The idea is to express that every number satisfies one of two cases:
either it is 0, 
or it is the successor of another natural number p, and this is written S p.
Thus, 1 is actually S 0, 2 is S (S 0) and so on.*) 
Definition is_zero (n:nat) :=
match n with
0 => true
| S p => false
end.

(** pred *)
(*maps any successor number larger than 0 to its predecessor and which maps 0 to itself.*) 
Print pred. 
Print Init.Nat.pred.
Compute pred 5.
Compute S 5.

(** Fixpoint *)
(*to use a function inside itselves in order to do recursivity*)
(*the argument of the recursive call must be a variable, and this variable must have
been obtained from the initial argument through pattern matching *)
(*=> structural recursion for the first argument*)
Fixpoint sum_n n :=
match n with
0 => 0
| S p => p + sum_n p
end. 

Fixpoint sum_n2 n s :=
match n with
0 => s
| S p => sum_n2 p (p + s)
end.

Fixpoint evenb n :=
match n with
0 => true
| 1 => false
| S (S p) => evenb p
end.




(*Computing with lists*) 
Require Import List.

(** nil *)
(*To group several elements in the same list,*)
(*::’ is actually used to add an element at the head of another list.*)
Check 1::2::3::nil.

(*apply a function to a list and returns it.*) 
(* map *)
Compute map (fun x => x + 3) (1::3::2::nil).
Compute map S (1::22::3::nil).

(** app or ++*)
(*To concatenate list*)
Compute let l := (1::2::3::nil) in l ++ map (fun x => x + 3) l.

Locate "++".
Locate app.
Print "++".
Print Coq.Lists.List.app.

(** sorts a list of natural numbers,*)
(*x <=? y to compare two natural numbers and return a boolean value*)
(*tl tuple list*) 
Fixpoint insert n l :=
match l with
nil => n::nil
| a::tl => if n <=? a then n::l else a::insert n tl
end.

Fixpoint sort l :=
match l with
nil => nil
| a::tl => insert a (sort tl)
end.


(** module *)
(* We put this section in a module so that our own definition of
    natural numbers does not interfere with the one from the
    standard library.  In the rest of the book, we'll want to use
    the standard library's. *)
Module NatPlayground.
Inductive nat : Type :=
  | O
  | S (n : nat).

End NatPlayground.


(** Arrow

  + "->"  to represent implication between proposition OR function types
  + "=>"    
  + ":="  "Definition id := M" définit dans l'environnement courant une nouvelle constante id égale à M, 
          sous réserve que le terme M est bien typé. 
          La constante id hérite du type de M, tel qu'il est inféré par le système.
 *)

(** Symbols 
  ⊤   	  True  
  ⊥   	  False  
  ¬A   	  ~ A  
  A∧B   	  A /\ B  
  A∨B   	  A \/ B  
  A⇒B   	  A -> B  
  A⇔B   	  A <-> B  
  ∀x∈D A(x)   	  forall x : D, A x  
  ∃x∈D A(x)   	  exists x : D, A x 
*)



(** Finding more functions  *)

(*to enumerate all the functions that return a value of type nat -> nat -> bool*) 
SearchPattern (nat -> nat -> bool).
SearchPattern (nat -> nat -> Prop).

Print Nat.leb.
(** Propositions and proofs *)

(** Searching proof*)
Search True.
SearchPattern (_ <= _).
SearchRewrite (_ + (_ - _)). (* rewritten theorems *)


(** Constructing new proofs *) 
(*
  scenario: 
    1. the user enters a STATEMENT that they want to prove, 
        using the command "Theorem" or "Lemma", 
        at the same time giving a name for later reference, 
    2. the Coq system displays the formula as a formula to be proved, 
        possibly giving a context of local facts 
          that can be used for this proof 
        (
          + the CONTEXT is displayed ABOVE a horizontal line written "=====", 
          + the GOAL is displayed UNDER the horizontal line
        ), 
    3. the user enters in "Proof." mode.
    3. the user declares variables to use and hypothesis with "intros".
    3. the user enters a command ("tactics") to decompose the goal into simpler ones, 
    4. the Coq system displays a list of formulas that still need to be proved, 
    5. back to step 3,
         while there is still a goal to prove,
    6. Use "Qed." to save the new theorem.
*) 

(** Exemple - OR*) 
Lemma example2 : forall a b : Prop, a /\ b -> b /\ a.
Proof.
  intros a b H. (* 2var and 1 hypothesis *)
  split .
  destruct H as [H1 H2].
  exact H2.
  intuition.
Qed.
Print example2.


Lemma example2_alternative : forall a b : Prop, a /\ b -> b /\ a.
Proof.
  intros a b H. (* 2var and 1 hypothesis *)
  split .
  destruct H as [H1 H2].
  exact H2.
  destruct H as [H1 H2].
  exact H1.
Qed.
Print example2_alternative.

(** Exemple - AND *) 
Lemma example3 : forall A B : Prop, A \/ B -> B \/ A.
Proof.
  intros Ap Bp H.
  destruct H as [H1 | H2].
  (* On voit qu il y a H1 : Ap , on veut donc récupérer dans le subgoals le Ap.*)
  right ; assumption. (* ";" permet d'appliquer "assumption" à tous les goals produits par "right"*)
  (* Maintenant H2 : Bp*)
  left ; assumption.
Qed.

Lemma example3_2 : forall A B : Prop, A \/ B -> B \/ A.
Proof.
  intros Ap Bp H.
  destruct H as [H1 | H2].
    - right.
      exact H1.
    - left.
      exact H2.
Qed.



(** Example - APPLY *) 
Check le_n.
Check le_S.
(*S (S (S 0)) = 3*) 
Lemma example4 : 3 <= 5.
Proof.
apply le_S.
apply le_S.
apply le_n.
Qed.

(** Example - APPLY with *) 
Check le_trans.
(**) 
Lemma example5 : forall x y, x <= 10 -> 10 <= y -> x <= y. 
Proof. 
intros x y x10 y10.
(* apply le_trans.*)
(*Error: Unable to find an instance for the variable m.*)
apply le_trans with (m := 10).
assumption.
assumption.
Qed.


(** *) 
(**) 
Print nat. 
Inductive nat : Set := 
    O : nat 
  | S : nat -> nat.

(*
   * Pour appliquer la règle droite de l'implication, 
     - intro H. (H est le nom choisi pour l'hypothèse)
   * Pour appliquer une règle droite décomposant l'opérateur logique C (ou/et) : 
     - apply C.
   * Pour appliquer une règle gauche décomposant l'opérateur logique C (ou/et): 
     - case C as [premisses].
   * On indique dans [premisses] pour chaque règle les noms des variables associées 
   * à chaque prémisse de la règle. Le séparateur est |.
   * Exemples : 
     - Ou -> [p | q] (deux règles, chaque règle ayant une prémisse).
     - Et -> [p q] (une règle, avec deux prémisses).
   *)


(** Inductive *)
(* permet de definir des types variables*)
(* Dans la théorie des types, 
    un système a des types inductifs s'il dispose de facilités pour créer un nouveau type 
    ainsi que de constantes et de fonctions qui créent des termes de ce type. 
   Cette caractéristique joue un rôle similaire aux structures de données dans un langage de programmation 
    et permet à la théorie des types d'ajouter des concepts tels que les nombres, les relations et les arbres. 

   Comme leur nom l'indique, les types inductifs peuvent être autoréférentiels, 
    mais généralement seulement d'une manière qui permet la récursion structurelle.

   L'exemple standard est le codage des nombres naturels en utilisant le codage de Peano.
*)

(* Exemple - NAT *)
Print nat. 
Inductive nat : Set := 
    O : nat 
  | S : nat -> nat.

(*
Ici, un nombre naturel est créé 
  soit à partir de la constante "0", 
  soit en appliquant la fonction "S" à un autre nombre naturel. 
Le "S" est la fonction de successeur qui représente l'addition de 1 à un nombre. 
Ainsi, "0" est zéro, "S 0" est un, "S (S 0)" est deux, "S (S (S 0))" est trois, et ainsi de suite.
*) 

(*Example - EVEN*) 
Inductive even : nat -> Prop :=
  even0 : 0 
| evenS : forall x:nat, even x -> even (S (S x)).


Inductive even_spec (n:nat) : bool -> Prop :=
| even_true : forall (Heven : Even n), even_spec n true 
| even_false : forall (Hodd : Odd n), even_spec n false.


