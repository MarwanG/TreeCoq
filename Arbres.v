(*
L’objectif de ce projet est d’implémenter en Coq les opérations principales des ensembles :

test d’appartenance à l’ensemble
ajout d’un élément
retrait d’un élément
Et si le temps le permet :
prédicats sous-ensemble et égalité ensemblistes
union, intersection et différence ensemblitse
La représentation des ensembles exploitera les arbres 2/3/4 auto-équilibrés.
On montrera que les propriétés d’équilibre sont respectées par les opérations.

On formalisera la correspondance entre les arbres rouge/noirs et les arbres 2/3/4.
Si le temps le permet, on proposera une seconde implémentation basée sur
les arbres rouges/noirs et on exploitera la correspondance avec les arbres 2/3/4
pour faciliter les preuves de proptiétés.
*)
Require Import Arith.
Require Import List.

Module Arbre.
Inductive tree (A: Type ) : Type :=
  leaf : tree A
 |binode: A -> tree A -> tree A -> tree A
 |trinode : A -> A -> tree A -> tree A -> tree A -> tree A
 |fournode : A -> A -> A -> tree A -> tree A -> tree A -> tree A -> tree A.

Arguments leaf [A].
Arguments binode [A] _ _ _.
Arguments trinode [A]_ _ _ _ _.
Arguments fournode [A]_ _ _ _ _ _ _.
