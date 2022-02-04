# Introduction

## Décrire la correspondance de Curry-Howard

Correspondance entre programmation (fonctionnelle) et démonstration (démontrer comme si on programmait, programmer comme si on démontrait).

Va au-delà de la programmation fonctionnelle (avec Haskell par ex. avec un langage monalique).

Tout langage de programmation rentre dans cette correspondance (beaucoup d'aspect on la correspondance, plutôt des langages séquentiels).

`Isomorphisme, bijection dans un sens comme dans un autre`

Quand on programme, on spécifie (spécification minimale : les types, comme les interfaces).

Peut se décrire par deux séries d'équivalences :

- En termes d'actions :

```coq
- programmer = démontrer
- spécifier = conjecturer
```

- En termes d'objets :

```
-              programme = démonstration
  - fonction de A vers B = preuve de `A implique B`
  -    couple de `A * B` = preuve de `A et B`
  -   élément de `A + B` = preuve de `A ou B`

-                   type = proposition
  -          type flèche = implication
  -  produit cartésien * (ex: tuple) = conjonction (et)
  -    somme disjointe + (opérateur d'union |) = disjonction (ou)
```

Un programme a un type, une démonstration prouve une proposition.

## Commenter le code du test

```coq
Definition F1 : nat -> nat.
  fix REC 1.
  intro n.
  case n as [ | pn].
  {
    exact 1.
  }
  {
    apply mult.
    exact (S pn).
    exact (REC pn).
  }
Defined.
```

Definition d'une fonction qui prend un NAT et retourne un NAT.

`fix REC 1.` : veut dire qu'on va faire de la récursion. donne un nom propre à la fonction F1

`intro n` : tactique pour dire `soit n notre argument, notre paramètre`. La partie gauche de l'implication va partir dans l'environnement. Transforme une partie gauche dans les hypothèses.

`case n as [ | pn]` Explorer les cas. Premier cas : NAT correspondant au 0. Second cas : prédécesseur de n, appelé pn .

### Examinons tous les cas pour et décomposons n pour tous les cas de sa définition, et détruisons n

`apply mult.` : appliquer la multiplication (nom de l'opérateur `*`), pour produire le nat. Attend deux arguments (donc créé deux buts).

`S`: succésseur (pn +1) (constructeur des entiers naturels). Correspond à n. le n disparaît à la ligne 4 avec le case.

`REC` : appel récursif.

Sucre syntaxique pour les nombre ( 2 = S (S 0)) )

`Fixpoint` : fonction récursive.

`Match n` : filtrons le n.

Example : Proposition logique : Est-ce que F1(5) est bien égal à 120.= ?

Peut être vraie ou fausse.

### Rappel

`réflexivité : x = x, symétrie : x = y => y = x, transitivité : x = y & y = z => x = z_`

`reflexivity` : relation d'égalité est par def réflexive (x toujours égal à x). Pour montrer que f1(5) égal à 120, on utilise la propriété de réflexivité : 120 = 120.

`Qed.` "Qui est démontré", pour les propositions logiques.

`Type` de `F1 5 = 120` est une proposition logique.

`Defined.` : là ou il y a des calculs, pour les fonctions.

`intro` : créé la variable n de type nat.

`case` avec une induction : hypothèse de récurrence

`simpl.` : développe les calculs.

`S pn \* f1(pn) = (pn+1)_(f1(pn)) = f1(pn) + pn_(f1(pn))`

`f_equal` : pour toute fonction appliquée à des arguments. `f(x) = y, f(x')=y', x'=x' & y=y'`

# Systèmes d'inférence

## Expliquer le paradoxe de Russell

**_Énoncé:_** _L'ensemble des ensemble n'appartenant pas à lui même appartient-il à lui-même ?_

paradoxe car si on répond:

- _oui_
  - Alors par définition, les éléments de cet ensemble n'appartiennent pas à lui même, donc cet ensemble n'appartient pas à lui-même, or en disant _oui_ on a dit qu'il appartenait à lui même (contradiction)
- _non_: Il n'appartient plus à lui même, or d'après la définition de l'ensemble, il s'agit d'une propriété suffisante pour appartenir à lui-même, donc il appartient de nouveau à lui-même (contradiction de nouveau)

  Autre ex. : Un barbier qui doit se raser lui même sachant qu'il rase les personnes qui ne se rasent pas eux mêmes.

Solution : interdire la construction de cette ensemble (théorie sous-jacente aux mathématiques, permet d'exprimer toute la théorie des mathématiques), avec la théorie des types ou des ensembles.

## Définir un système d'inférence

**Prémisse** : hypothèse au dessus

Permet de définir un ensemble juste avec une règle, exemple de l'ensemble Unité : un ensemble à un élément.

Une **inférence** : passage de prémisse à une conclusion.

Prouver les jugements en appliquant les règles.

Un système d'inférence est l'ensemble des règles permettant de fonder le système de déduction, dérivation et démonstration.

`n+1` est un calcul, une propriété de l'ensemble des nat.

`S` correspond vraiment à la manière dont on représente les `S`.

`new Cons` (en typescript) correspond au `S`

## Que peut-on déduire du faux ? Montrez le

faux implique non vrai

## Définir inductivement un type unité, puis booléen. Donner les principes inductifs

### Définition inductive Unité

```coq
Inductive Unité : Type :=
| un : Unité
(* un : unique constructeur de Unité. *).
```

Principe inductif :

- Si un objet de type unité vérifie P, alors pour tout objet x du même type, x vérifie P.
- Un type inductif est un type qui a la propriété d'être défini par des cas, et avec la possibilité de récursion en plus.

### Définition inductive Booléen

```coq
Inductive bool : Set :=
| true : bool
(* Premier constructeur. *)
| false : bool
(* Second constructeur. *)
.
```

Principe inductif :

Pour tout prédicat P sur `bool`, si P est vérifié par true et false alors P est vérifié par n'importe quel `bool`

## Définir inductivement les entiers naturels

Un entier naturel est:

- soit 0
- soit le successeur d'un entier naturel

Omega : autre nom mathématique des entiers naturels

On peut utiliser le `:` pour type directement:

```coq
| sucesseur : Omega -> Omega
au lieu de
| sucesseur n : Omega
```

## Définir le principe d'induction pour les entiers naturels. Montrez le

Définition du principe inductif:

- Si 0 vérifie P, et si tout successeur vérifie P également, alors tous les entiers naturels vérifient P.
- U NA partir d'un petit nombre de fait, énoncer une loi plus général. Déduire une loi universelle.

Pour tout prédicat P sur les naturels, si ...

- 0 vérifie P
- tout entier naturel vérifiant P implique que le successeur de cet entier naturel vérifie aussi P
  ... alors P est vérifié par tout entier naturel

**Note à part** : Type 1 : Quelque que soit T, `type`. Dès qu'on utilise un quantificateur avec un type.

## Définir le principe de récursion primitive pour les entiers naturels. Montrez-le

Se rappeler des patrons de conception vu en cours : patron composition avec visiteur récursif primitif.

On part de l'entier naturel 0 : On associe une valeur à l'entier 0. (Fonction d’amorçage).

Exemple : `(Factoriel + 10)!` : À zéro on associe 1 + 10.

Le premier élément que l'on donne, c'est l’élément de P 0.

Ensuite, on fourni une fonction pour le cas des successeurs, de type R(n) -> (R (S n)).

```coq
(* avec nat_rect, on donne les arguments qui sont les traitements de chaque cas *)
Definition FG(n : nat) : nat.
 Check nat_rect.
 apply nat_rect.
 - exact 0.
 - Check nat_rect.
   intros m rm. (* rm représente la somme jusqu'à m *)
   exact ((S m) + rm). (* calcul au rang (S m) *)
 - Check nat_rect.
   exact n.
Defined.

Compute (FG 10).
Print FG.
```

C'est toujours de la même manière qu'on fait un calcul. On part du cas de base, et on traite les autres cas.

On part de l'entier naturel égal à 0 (rang 0), chaque successeur est égal à la somme entre prédécesseur et 1.

## Définir inductivement des listes génériques

Une liste est soit vide, soit une liste à laquelle on ajoute un élément en tête.

## Définir le principe d'induction pour les listes. Montrez-le

## Définir le principe de récursion primitive pour les listes. Montrez-le

On part de la liste vide (rang 0), chaque successeur est égal à la liste du prédécesseur à laquelle on a joute un élément.

## Définir inductivement des arbres binaires génériques

Un arbre est soit une feuille, soit une branche avec un ou deux arbres au bout.

## Définir le principe d'induction pour les arbres. Montrez-le

## Définir le principe de récursion primitive pour les arbres. Montrez-le

On part d'une feuille (rang 0), chaque successeur est égal à l'arbre du prédécesseur auquel on rajoute une branche

## Définir inductivement des vecteurs (des listes d'une taille donnée)

Un vecteur est une liste vide de taille 0, ou une liste de taille n+1 à laquelle on a ajouter un élément,

## Définir l'opération de concaténation

On réalise une matrice

## Définir le prédicat d'égalité

Soit x et y, deux objets mathématiques, si il est impossible de trouver une propriété vérifiée par l'un mais pas par l'autre, alors on a égalité entre x et y.
