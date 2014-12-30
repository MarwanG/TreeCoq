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
Require Import ZArith.

Module Arbre.
Inductive tree (A: Type ) : Type :=
  leaf : tree A
 |binode: A -> tree A -> tree A -> tree A
 |trinode : A -> A -> tree A -> tree A -> tree A -> tree A
 |quadnode : A -> A -> A -> tree A -> tree A -> tree A -> tree A -> tree A.

Arguments leaf[A].
Arguments binode [A] _ _ _.
Arguments trinode [A]_ _ _ _ _.
Arguments quadnode [A]_ _ _ _ _ _ _.


Definition tree_1 : tree nat :=
  (binode 5
          (binode 1
             (leaf) (leaf))
         ( binode 6
             (leaf) (leaf))
   ).

Definition tree_2: tree nat :=
  (trinode 10 20
          (binode 2
              (binode 1
                 (leaf) (leaf))
              (binode 3
                 (leaf) (leaf)))
          (binode 13
              (binode 12
                 (leaf) (leaf))
              (binode 15
                 (leaf) (leaf)))
          (binode 22
                 (leaf) (leaf))).

Definition tree_3: tree nat :=
  (quadnode 10 20 30
      (binode 5 leaf leaf)
      (binode 15 leaf leaf)
      (binode 25 leaf leaf)
      (binode 32 leaf leaf)
     ).

Fixpoint ble_nat (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => ble_nat n' m'
      end
  end.

Fixpoint exist (a:nat)(T:tree nat): bool :=
  match T with
    |leaf => false
    |binode e fg fd => (if beq_nat a e 
                        then true
                        else (if ble_nat a e then exist a fg else exist a fd))
    |trinode e1 e2 fg fm fd =>(if beq_nat a e1
                               then true
                               else( 
                                     if beq_nat a e2 then true else(
                                     if ble_nat a e1 then exist a fg 
                                     else
                                     (if ble_nat a e2 then exist a fm else exist a fd)
                                    )
                               )) 
    | quadnode e1 e2 e3 f1 f2 f3 f4=> if beq_nat a e1 
                                         then true
                                      else if beq_nat a e2 
                                         then true 
                                      else if beq_nat a e3 
                                         then true
                                      else if ble_nat a e1 
                                         then exist a f1
                                      else if ble_nat a e2 
                                         then exist a f2
                                      else if ble_nat a e3 
                                         then exist a f3
                                      else exist a f4    
 end.


Example test_1: exist 5 tree_1 = true.
Proof.
simpl.
reflexivity.
Qed.

Example test_2: exist 2 tree_2 = true.
Proof.
simpl.
reflexivity.
Qed.


Example test_3: exist 5 tree_2 = false.
Proof.
simpl.
reflexivity.
Qed.

(* les nouveaux élément sont toujours ajoutés en bas de l'arbre *)
(* le probleme du point fix vient des éclatement, il faut appeler add au niveau le plus bas
*)
Fixpoint add (a:nat) (T : tree nat): tree nat :=
match T with
|leaf => binode a leaf leaf
|binode e fg fd => if ble_nat e a then
                      match fd with
                      |leaf => trinode e a leaf leaf leaf
                      |quadnode e1 e2 e3 f1 f2 f3 f4 => (*add a (trinode e e2 fg 
                                                           (binode e1 f1 f2) (binode e3 f3 f4))) *)
                      |_ => binode e fg (add a fd)
                      end
                   else 
                      match fg with
                      |leaf => trinode a e leaf leaf leaf
                      |quadnode e1 e2 e3 f1 f2 f3 f4 => leaf (* add a (trinode e2 a 
                                                          (binode e1 f1 f2) (binode e3 f3 f4) fd) *)
                      |_ => binode e (add a fg) fd
                      end
                  
|trinode e1 e2 fg fm fd => if ble_nat a e1 then
                              match fg with 
                              |leaf => quadnode a e1 e2 leaf leaf leaf leaf
                              |quadnode i1 i2 i3 f1 f2 f3 f4=> leaf
                              |_ => trinode e1 e2 (add a fg) fm fd
                              end
                           else if ble_nat a e2 then
                              match fm with
                              |leaf => quadnode e1 a e2 leaf leaf leaf leaf
                              |quadnode i1 i2 i3 f1 f2 f3 f4 => leaf
                              |_=> trinode e1 e2 fg (add a fm) fd
                              end
                           else
                              match fd with
                              |leaf => quadnode e1 e2 a leaf leaf leaf leaf
                              |quadnode i1 i2 i3 f1 f2 f3 f4 => leaf
                              |_=> trinode e1 e2 fg fm (add a fd)
                              end
|quadnode e1 e2 e3 f1 f2 f3 f4 => (* ce cas n'arrive que si c'est la racine *)
                                leaf(* add a (binode e2 (binode e1 f1 f2) (binode e3 f3 f4))*)
end.





