# IIMT FIL Coq

Ce répertoire a pout but de rassembler les notions vues dans le cadre du cours de programmation logique en Coq donné à l'[IMT](https://www.imt-atlantique.fr/fr/formation/ingenieur-par-apprentissage/ingenierie-logicielle).

## Contenu

### Aides mémoires

Notamment grâce au livre [Coq in a Hurry](https://cel.archives-ouvertes.fr/inria-00001173), un aide mémoire personnalisé a pu être rédigé : [CheatSheet_in_a_hurry.v](https://github.com/Naedri/IMT-Coq-revision_sheet/blob/main/Revision/CheatSheet_in_a_hurry.v).

D'autres fichiers plus court, on pour objectif de présenter succintement des structures essentielles de Coq :

- [Les fonctions](https://github.com/Naedri/IMT-Coq-revision_sheet/blob/main/Revision/functions.v)
- [Les types inductifs](https://github.com/Naedri/IMT-Coq-revision_sheet/blob/main/Revision/inductions.v)

#### Quizz

En intéraction lors des enseignements, un quizz a pu être réalisé progressivement : [quiz_logique.md](https://github.com/Naedri/IMT-Coq-revision_sheet/blob/main/Quizz/quiz_logique.md).

### Travaux Pratiques - Logical Foundations

A partir des exercices proposés par le Volume 1 de Software Foundations : Logical Foundations, des réponses ont été discutées :

- [Basics: Functional Programming in Coq](https://github.com/Naedri/IMT-Coq-revision_sheet/blob/main/Lectures/Basics.v)
- [Induction: Proof by Induction](https://github.com/Naedri/IMT-Coq-revision_sheet/blob/main/Lectures/Induction.v)
- [Lists: Working with Structured Data](https://github.com/Naedri/IMT-Coq-revision_sheet/blob/main/Lectures/Lists.v)
- [Poly: Polymorphism and Higher-Order Functions](https://github.com/Naedri/IMT-Coq-revision_sheet/blob/main/Lectures/Poly.v)

#### Tactiques

Les réponses sont données en utilisant un sous-ensemble restreint de tactiques.

Échantillon

- `case H as [ cas1 | ... | casN].` : analyse par cas décomposant l'hypothèse `(H : I)`, où `I` est un type inductif. `casI` est une énumération des variables intervenant dans la `I`-ème règle.
- `exact H.` : preuve du but `X` avec l'hypothèse `(H : X)`.
- `assumption.` : preuve du but `X` avec une hypothèse `(H : X)`.
- `intro H.` : lorsque le but est une fonction à construire (de type `A -> B` ou `∀ (x : A), B`), introduction du paramètre `(H : A)` de la fonction dans l'environnement.
- `intros H1 ... HN.` : généralisation au cas de `N` paramètres.
- `apply F.` : application de la fonction (hypothèse ou constructeur) `(F : A -> B)` pour prouver `B`, le but devenant `A`.

#### Egalité - Analyse de cas et réécriture

L'égalité est définie inductivement ainsi.

Prédicat `(eq T x y)` - deux paramètres `(T : Type)` et `(x : T)` - un index ```(y : T)

```

    ----- [eq_refl]
    x = x
```

Si `(H : (a = b))` est une hypothèse,

- `case H.` réécrit toute occurrence de `b` en `a`, et est donc équivalent à `rewrite <- H.`,
- `case (eq_sym H)).` réécrit toute occurrence de `a` en `b` et est donc équivalent à `rewrite H.`, `eq_sym` étant le théorème `∀ T, ∀ (x y : T), (x = y) -> (y = x)` exprimant la symétrie de l'égalité.

### Examens

Afin de mesurer le niveau attendu des compétences de ce cours, un sujet d'examen a pu être ajouté :

- [Coq-Logique-2021](./Exam/coq_logic_sujet.hs) pour lequel mes [réponses](https://github.com/Naedri/IMT-Coq-revision_sheet/blob/main/Exam/coq_logic_my_answer.v) sont disponibles ainsi qu'une [correction](https://github.com/Naedri/IMT-Coq-revision_sheet/blob/main/Exam/coq_logic_another_answer.v).

## Ressources pédagogiques

### Logique

- [Logique avec Coq](https://www.grall.name/teaching/logic/2022/index.html)
- [Programmer = démontrer ? La correspondance de Curry-Howard aujourd'hui](https://www.college-de-france.fr/site/xavier-leroy/course-2018-2019.htm)

### Programmation certifiée

- [Programmation certifiée avec Coq](https://grall.name/teaching/certifiedProgramming/2022/)

### Programmation avec Coq

#### Mini-guide

- [Coq - Un mini-guide](https://www.grall.name/teaching/logic/2022/coqMiniGuide.html)
- [Petit guide de survie en Coq](http://lim.univ-reunion.fr/staff/fred/Enseignement/IntroCoq/Exos-Coq/Petit-guide-de-survie-en-Coq.html#htoc22)

#### Tactics

- [Coq Tactics Index](https://pjreddie.com/coq-tactics/#reflexivity)
- [Coq Tactics Cheatsheet](https://www.cs.cornell.edu/courses/cs3110/2018sp/a5/coq-tactics-cheatsheet.html)
