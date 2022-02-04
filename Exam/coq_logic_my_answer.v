Require Import List.
Import ListNotations.

(** *Bibliothèque standard *)

Print nat.
Locate "+".
Print Nat.add.
Locate "*".
Print Nat.mul.

Print list.
Locate "++".
Print app.

Print True.

Print False.

Print or.
Locate "\/".

Print and.
Locate "/\".

Print not.
Locate "~".

(** *Logique : le tiers exclu *)

(* Axiomes possibles pour la logique classique *)

Definition tiersExclu : Prop := forall P : Prop, P \/ ~P. 
Definition involutionNegation : Prop := forall P : Prop, ~~P -> P. 
Definition implicationMaterielle : Prop := forall P Q : Prop, (P -> Q) -> (~P \/ Q). 
Definition reciproqueContraposition : Prop := forall P Q : Prop, (~Q -> ~P) -> (P -> Q). 
(* Indication pour la suite : si besoin, utiliser la tactique "unfold" pour déplier
   la définition d'une des propositions précédentes. *)

(* Réciproques valides *)

(*
  Indication :
  - la négation *~P* est définie comme *P -> False*.            
 *)
Proposition reciproqueInvolutionNegation :
  forall P : Prop, P -> ~~P.
Proof.
  unfold not.
  intros.
  apply H0.
  exact H.
Defined.

(*
  Indication :
  - décomposer la disjonction en hypothèse,
  - lorsque les hypothèses entrainent une contradiction,
  utiliser la tactique exfalso.
 *)
Proposition reciproqueImplicationMaterielle :
  forall P Q : Prop, (~P \/ Q) -> P -> Q.
Proof.
  intros.
  case H.
  - intros.
    exfalso.
    apply H1.
    apply H0.
  - intros.
    exact H1.
Defined.

Proposition contraposition :
  forall P Q : Prop, (P -> Q) -> (~Q -> ~P).
Proof.
  intros.
  apply H0 in H.
  - exfalso.
    apply H. 
  - exfalso.
    apply H0.
Admitted.
(* Equivalence des axiomes *)

(*
  Indication :
  - décomposer le tiers exclu appliqué à la proposition.
 *)
Proposition tiersExcluVersInvolutionNegation :
  tiersExclu -> involutionNegation.
  Proof.
  unfold tiersExclu .
  unfold involutionNegation.
  intros.
Admitted.

(*
  Indication :
  - appliquer l'involution de la négation à (P \/ ~P),
  - utiliser le fait que (~(P \/ ~P)) entraine ~P,
  - utiliser les tactiques "left" et "right" pour prouver une disjonction. 
 *)
Proposition involutionNegationVersTiersExclu :
  involutionNegation -> tiersExclu.
Proof.
  intros.
  apply H.
  apply reciproqueInvolutionNegation.
(*
  left ; assumption.
  right ; assumption. 
  exfalso.
  *)
Admitted.

(*
  Indication :
  - décomposer la preuve de la disjonction (P \/ ~P) obtenue en appliquant
  le lemme involutionNegationVersTiersExclu à la proposition P.
 *)
Proposition involutionNegationVersImplicationMaterielle :
  involutionNegation -> implicationMaterielle.
Proof.
  unfold involutionNegation.
  unfold implicationMaterielle.
  intros.
  apply involutionNegationVersTiersExclu in H.
Admitted.

Check or_comm.
(*
  Indication :
  - utiliser la proposition or_comm exprimant la commutativité de la disjonction (or).
 *)
Proposition implicationMaterielleVersTiersExclu :
  implicationMaterielle -> tiersExclu.
Proof.
  unfold implicationMaterielle.
  unfold tiersExclu.
  intros.
  apply or_comm.
  apply H.
  intros.
  exact H0.
Defined.
(*
  Indication :
  - utiliser deux propositions déjà montrées.
 *)
Proposition implicationMaterielleVersInvolutionNegation :
  implicationMaterielle -> involutionNegation.
Proof.
  unfold implicationMaterielle.
  unfold involutionNegation.
  intro h.
  apply tiersExcluVersInvolutionNegation.
  apply implicationMaterielleVersTiersExclu.
  exact h.
Defined.

(*
  Indication :
  - utiliser l'involution de la négation.
 *)
Proposition implicationMaterielleVersReciproqueContraposition :
  implicationMaterielle -> reciproqueContraposition.
Proof.
  intros.
(*   apply involutionNegation. *)
Admitted.

(*
  Indication :
  - appliquer la réciproque de la contraposition à True et P.
 *)
Proposition reciproqueContrapositionVersInvolutionNegation :
  reciproqueContraposition -> involutionNegation.
Proof.
Admitted.

(** *Définitions inductives - La croissance de listes *)

Inductive EstCroissante : list nat -> Prop :=
| videCroissante : EstCroissante []
| singletonCroissante : forall a, EstCroissante [a]
| consConsCroissante :
    forall a b l, (a <= b)
             -> EstCroissante (b :: l) -> EstCroissante( a :: b :: l).

(*
  --------- [precVide]
  Prec m []
  
  (t : nat)  (r : list nat)  (m <= t)
  ----------------------------------- [precCons]
  Prec m (t :: r)
 *)
Inductive Prec(m : nat) : list nat -> Prop :=
| precVide : Prec m []
| precCons : forall t r, (m <= t) -> Prec m (t :: r).


(* 

---------------------- [videCroissante2]
  EstCroissante2 []

  (t : nat)  (r : list nat)  (Prec t r) -> EstCroissante2 r
------------------------------------------------------------- [consCroissante2]
  EstCroissante2 (t :: r)
 *)
Inductive EstCroissante2 : list nat -> Prop :=
| videCroissante2 : EstCroissante2 [] 
| consCroissante2 : forall t r, (Prec t r) -> EstCroissante2 r -> EstCroissante2 (t :: r).

(*
  Indication :
  - procéder par induction sur la preuve de (EstCroissante2 l) ;
  dans le cas d'une liste non vide, décomposer par cas la preuve
  du prédicat Prec.
 *)
Proposition adequation_estCroissante2 : forall l,
    EstCroissante2 l -> EstCroissante l.
Proof.
  intros.
  induction H as [| t r h h2 h3 ].
  - apply videCroissante.
  - case h as [| t2 r2 h1].
    + apply singletonCroissante.
    + apply consConsCroissante.
  exact h1.
  exact h3.
Defined.

(*
  Indication :
  - procéder par induction sur la preuve de (EstCroissante l).
 *)
Proposition completude_estCroissante2 : forall l,
    EstCroissante l -> EstCroissante2 l.
Proof.
  intros.
  induction H.
  - exact videCroissante2.
  - apply consCroissante2.
    + exact (precVide a).
    + exact videCroissante2.
  - apply consCroissante2.
    + apply precCons.
      exact H.
    + exact IHEstCroissante.
Defined.

(** *Définitions inductives - Facteurs d'une liste *)

Proposition associativite_concatenation :
  forall T : Type,
  forall l1 l2 l3 : list T,
    l1 ++ (l2 ++ l3) = (l1 ++ l2) ++ l3.
Proof.
  intros.
  induction l1.
  simpl. 
  reflexivity.
Admitted.

(*
 
-------------------------------------- [facteurPrefixe]
      (Facteur k k ++ l)

    (l l' k : list A) (Facteur k l')
-------------------------------------- [facteurInterne]
          (Facteur k  l ++ l')
*)
Inductive Facteur{A : Type}(k : list A) : list A -> Prop :=
| facteurPrefixe : forall l , Facteur k (k ++ l)
| facteurInterne : forall l l', Facteur k l' -> Facteur k (l ++ l').


(*
  Indication :
  - procéder par induction sur la preuve de *Facteur k l*,
  - pour prouver l'existence, utiliser la tactique "exists w", où w est le terme
  montrant l'existence.
 *)
Lemma adequation_Facteur :
  forall A, forall k l : list A, Facteur k l -> exists k' k'', k' ++ k ++ k'' = l.
Proof.
  intros.
  induction H.
  - exists [].
    exists l.
    simpl.
    reflexivity.
  - case IHFacteur.
Admitted.

(*
  Indication :
  - utiliser directement les constructeurs de Facteur.
 *)
Lemma completude_Facteur :
  forall A, forall k' k k'' l : list A, k' ++ k ++ k'' = l -> Facteur k l.
Proof.
  intros.
  induction H.
  apply facteurInterne.
  apply facteurPrefixe.
Defined.

(** *Entiers naturels - Des fonctions et des propositions utiles *)

(* Addition et ordre *)

Lemma neutraliteDroite_addition :
  forall n : nat, n = n + 0.
Proof.
  intros.
  induction n.
  - simpl.
    reflexivity.
  - simpl.
    rewrite <- IHn.
    reflexivity.
Defined.

Lemma sommeSuccesseurs :
  forall n m : nat,
    S n + S m = S (S (n + m)).
Proof.
  intros.
  induction n.
 - simpl. 
   reflexivity.
 - simpl.
   rewrite <- IHn.
   reflexivity.
Admitted.

(*
  Indication :
  - procéder par induction sur la preuve de (n2 <= n3).
 *)
Proposition transitivite_le :
  forall n1 n2 n3, n1 <= n2 -> n2 <= n3 -> n1 <= n3.
Proof.
  intros.
  induction H0.
  - apply H.
  - apply le_S.
    apply IHle.
Defined.

Proposition zeroMin_le :
  forall n, 0 <= n.
Proof.
  fix HR 1.
  intros.
  case n as [ | pn].
  - apply le_n.
  - apply le_S.
    apply HR.
Defined.

Lemma successeurCroissant_le :
  forall m n, m <= n -> S m <= S n.
Proof.
  intros.
  induction H.
  - apply le_n.
  - apply le_S.
    apply IHle.
Defined.

(*
  Indication :
  - procéder par induction sur m,
  - utiliser successeurCroissant_le.
 *)
Lemma compatibiliteAdditionGauche_le : 
  forall m n1 n2, n1 <= n2 -> (m + n1) <= (m + n2).
Proof.
  intros.
  induction m.
  - simpl.
    apply H.
  - apply successeurCroissant_le in IHm.
    simpl.
    apply IHm.
Defined.

(*
  Indication :
  - procéder par induction sur la preuve de (m1 <= m2),
  - utiliser compatibiliteAdditionGauche_le.
 *)
Proposition compatibiliteAddition_le :
  forall m1 m2 n1 n2, m1 <= m2 -> n1 <= n2 -> (m1 + n1) <= (m2 + n2).
Proof.
  intros.
  induction H.
  - apply compatibiliteAdditionGauche_le.
    apply H0.
  - simpl.
    rewrite -> IHle.
(*     apply successeurCroissant_le. *)
Admitted.

(*
  Indication :
  - utiliser compatibiliteAddition_le.
 *)
Proposition compatibiliteAddition_zeroMinDroite_le :
  forall m1 m2 n, m1 <= m2 -> m1 <= (m2 + n).
Proof.
Admitted.

(* Maximum et puissance *)

Fixpoint max(m n : nat) : nat.
  exact (Nat.max m n). (* à modifier *)
Defined.

(*
  Indication :
  - procéder par induction sur m, avec une hypothèse de récurrence
  quantifiée universellement sur n. 
 *)
Proposition commutativite_max :
  forall m n, max m n = max n m.
Proof.
Admitted.

Proposition idempotence_max :
  forall n, n = max n n.
Proof.
Admitted.

(*
  Indication :
  - procéder par induction sur m, avec une hypothèse de récurrence
  quantifiée universellement sur n. 
 *)
Proposition majorantGauche_max :
  forall m n, m <= max m n.
Proof.
Admitted.

(*
  Indication :
  - utiliser la commutativité.
 *)
Proposition majorantDroite_max :
  forall m n, n <= max m n.
Proof.
Admitted.

Fixpoint puissance(m n : nat) : nat.
  exact (Nat.pow m n). (* à modifier *)
Defined.

(*
  Indication :
  - procéder par induction sur la preuve de (n1 <= n2).
 *)
Proposition croissance_puissance :
  forall (m n1 n2 : nat),
    n1 <= n2 -> puissance (S m) n1 <= puissance (S m) n2.
Proof.
Admitted.

(** *Arbres binaires - Un encadrement de la taille    *)

(* à compléter

-------  [arbreVide]



-----------------------  [arbreCons]

*)
 
Inductive Arbre(T : Type) : Type :=
  |arbreVide : Arbre T
  |arbreCons : T -> (Arbre T) -> (Arbre T) -> (Arbre T)
.

Proposition principeInductif_Arbre : 
  forall (T : Type) (P : Arbre T -> Prop),
    (* à compléter *)
    forall (a : Arbre T), P a.
Proof.
Admitted.

Fixpoint hauteur{T : Type}(a : Arbre T) : nat.
  exact 0. (* à modifier *)
Defined.

Fixpoint taille{T : Type}(a : Arbre T) : nat.
  exact 0. (* à modifier *)
Defined.

Definition unArbre : Arbre nat.
Admitted.


Example hauteurArbre : hauteur (unArbre) = 3.
Admitted.

Example tailleArbre : taille (unArbre) = 5.
Admitted.

(*
  Indication :
  - procéder par induction sur l'arbre,
  - utiliser les propositions démontrées sur les entiers naturels.
 *)
Proposition majorationTaille_Arbre :
  forall T : Type,
  forall a : Arbre T,
    S (taille a) <= (puissance 2 (hauteur a)). 
Proof.
Admitted.

(*
  Indication :
  - décomposer la preuve de (inhabited T) en hypothèse 
  pour obtenir un élément de T,            
  - procéder par induction sur n,
  - utiliser les propositions démontrées sur les entiers naturels,
  - pour prouver une conjonction, utiliser "split".
 *)
Print inhabited.
Proposition majorationOptimaleTaille_Arbre :
  forall T : Type,
    inhabited T ->
    forall n : nat,
    exists a : Arbre T,
      hauteur a = n
      /\
      S (taille a) = (puissance 2 (hauteur a)). 
Proof.
Admitted.
