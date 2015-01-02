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

Definition tree_4: tree nat :=
  (trinode 5 20
           (trinode 1 2 (leaf)(leaf)(leaf))
           (trinode 6 7 (leaf)(leaf)(leaf))
           (trinode 21 22 (leaf)(leaf)(leaf))).
          
(*Fonction pour teste less than or equal*)
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


Example test_3: exist 32 tree_3 = true.
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
                      |quadnode e1 e2 e3 f1 f2 f3 f4 => if ble_nat a e1 then (trinode e e2 fg 
                                                           (binode e1 (add a f1) f2) (binode e3 f3 f4))
                                                        else if ble_nat a e2 then (trinode e e2 fg 
                                                           (binode e1 f1 (add a f2)) (binode e3 f3 f4)) 
                                                        else if ble_nat a e3 then (trinode e e2 fg 
                                                           (binode e1 f1 f2) (binode e3 (add a f3) f4)) 
                                                        else trinode e e2 fg 
                                                           (binode e1 f1 f2) (binode e3 f3 (add a f4))
                      |_ => binode e fg (add a fd)
                      end
                   else 
                      match fg with
                      |leaf => trinode a e leaf leaf leaf
                      |quadnode e1 e2 e3 f1 f2 f3 f4 =>if ble_nat a e1 then (trinode e e2
                                                           (binode e1 (add a f1) f2) (binode e3 f3 f4) fd)
                                                        else if ble_nat a e2 then (trinode e e2 fg 
                                                           (binode e1 f1 (add a f2)) (binode e3 f3 f4)) 
                                                        else if ble_nat a e3 then (trinode e e2 
                                                           (binode e1 f1 f2) (binode e3 (add a f3) f4) fd) 
                                                        else (trinode e e2 
                                                           (binode e1 f1 f2) (binode e3 f3 (add a f4)) fd) 
                      |_ => binode e (add a fg) fd
                      end
                  
|trinode e1 e2 fg fm fd => if ble_nat a e1 then
                              match fg with 
                              |leaf => quadnode a e1 e2 leaf leaf leaf leaf
                              |quadnode i1 i2 i3 f1 f2 f3 f4=> if ble_nat a i1 then 
                                                                (quadnode i2 e1 e2 
                                                                (binode i1 (add a f1) f2) (binode i3 f3 f4) fm fd)
                                                               else if ble_nat a i2 then 
                                                                (quadnode i1 e1 e2 
                                                                (binode i2 f1 (add a f2)) (binode i3 f3 f4) fm fd)
                                                               else if ble_nat a i3 then 
                                                                 (quadnode i1 e1 e2 
                                                                 (binode i2 f1 f2) (binode i3 (add a f3) f4) fm fd)
                                                               else (quadnode i1 e1 e2 
                                                                 (binode i2 f1 f2) (binode i3 f3 (add a f4)) fm fd)
                              |_ => trinode e1 e2 (add a fg) fm fd
                              end
                           else if ble_nat a e2 then
                              match fm with
                              |leaf => quadnode e1 a e2 leaf leaf leaf leaf
                              |quadnode i1 i2 i3 f1 f2 f3 f4 => if ble_nat a i1 then 
                                                                 (quadnode e1 i2 e2
                                                                 fg (binode i1 (add a f1) f2) (binode i3 f3 f4) fd)                                                                 
                                                                else if ble_nat a i2 then 
                                                                 (quadnode e1 i2 e2
                                                                 fg (binode i1 f1 (add a f2)) (binode i3 f3 f4) fd)  
                                                                else if ble_nat a i3 then  
                                                                 (quadnode e1 i2 e2
                                                                 fg (binode i1 f1 f2) (binode i3 (add a f3) f4) fd)  
                                                                else 
                                                                 (quadnode e1 i2 e2
                                                                 fg (binode i1 f1 f2) (binode i3 f3 (add a f4)) fd)  
                              |_=> trinode e1 e2 fg (add a fm) fd
                              end
                           else
                              match fd with
                              |leaf => quadnode e1 e2 a leaf leaf leaf leaf
                              |quadnode i1 i2 i3 f1 f2 f3 f4 => if ble_nat a i1 then 
                                                                 (quadnode e1 e2 i2
                                                                 fg fm (binode i1 (add a f1) f2) (binode i3 f3 f4))
                                                                else if ble_nat a i2 then 
                                                                 (quadnode e1 e2 i2
                                                                 fg fm (binode i1 f1 (add a f2)) (binode i3 f3 f4))
                                                                else if ble_nat a i3 then 
                                                                 (quadnode e1 e2 i2
                                                                 fg fm (binode i1 f1 f2)) (binode i3 (add a f3) f4)
                                                                else (quadnode e1 e2 i2
                                                                 fg fm (binode i1 f1 f2)) (binode i3 f3 (add a f4))
                              |_=> trinode e1 e2 fg fm (add a fd)
                              end
|quadnode e1 e2 e3 f1 f2 f3 f4 => if ble_nat a e1 then
                                   binode e2 (binode e1 (add a f1) f2) (binode e3 f3 f4) 
                                  else if ble_nat a e2 then
                                   binode e2 (binode e1 f1 (add a f2)) (binode e3 f3 f4) 
                                  else if ble_nat a e3 then
                                   binode e2 (binode e1 f1 f2) (binode e3 (add a f3) f4) 
                                  else  
                                   binode e2 (binode e1 f1 f2) (binode e3 f3 (add a f4))
end.


Definition ex1 : tree nat :=
(add 1 ( add 5 (add 15 (add 13 (add 3 (add 14 (add 2 (leaf)))))))).

Example test_add2: exist 15 ex1 = true.
Proof.
compute.
reflexivity.
Qed.

Example test_add5: exist 7 ex1 = false.
Proof.
compute.
reflexivity.
Qed.



Example test_add9: exist 2 ex1 = true.
Proof.
compute.
reflexivity.
Qed.



Fixpoint find_closet(T: tree nat): nat :=
  match T with
    |binode e fg fd => match fd with
		       |leaf => e
		       |_ => find_closet fd
		       end
    |trinode e1 e2 fg fm fd => match fd with
			       |leaf => e2 
			       |_ => find_closet fd
			       end
    |quadnode e1 e2 e3 f1 f2 f3 f4 => match f4 with  
				      |leaf => e3
				      |_ => find_closet f4
                                       end
    | _ => 0 (*sens d'etre jamais dans cette cas*)
end.

Definition ex1 : tree nat :=
(add 1 ( add 5 (add 2 (leaf)))).


                          

(*sans le cas de racine*)
Fixpoint delete (a:nat)(T: tree nat): tree nat :=
match T with
|trinode e1 e2 fg fm fd => (if beq_nat a e1 then
                               match fg with
                               |leaf => binode e2 fg fd
                               | _ => (let r := find_closet fg in
                                      trinode  r e2 (delete r fg) fm fd)
                               end
                            else if beq_nat a e2 then
                               match fm with
                               |leaf => binode e1 fd fm
                               | _ => (let r := find_closet fm in
                                      trinode e1 e2 fg (delete r fm) fd)
                               end       
                           else if ble_nat a e1 then
                               match fg with
                               |leaf => trinode e1 e2 fg fm fd
                               | _   => trinode e1 e2 (delete a fg) fm fd
                               end
                           else if ble_nat a e2 then
                               match fm with
                               |leaf => trinode e1 e2 fg fm fd
                               | _ => trinode e1 e2 fg (delete a fm) fd
                               end               
                           else
                             match fd with
                               |leaf => trinode e1 e2 fg fm fd
                               |_ => trinode e1 e2 fg fm (delete a fm)
                               end
                           )
|quadnode e1 e2 e3 f1 f2 f3 f4 =>( if beq_nat a e1 then
                                   match f1 with
                                     |leaf => trinode e2 e3 f2 f3 f4
                                     | _ => (let r := find_closet f1 in
                                             quadnode r e2 e3 (delete r f1) f2 f3 f4)
                                   end                         
                                   else if beq_nat a e2 then
                                   match f2 with
                                     |leaf => trinode e1 e3 f1 f2 f3
                                     |_ => (let r := find_closet f2 in
                                            quadnode e1 r e3 f1 (delete r f2) f3 f4)                                              end
                                   else if beq_nat a e3 then
                                   match f3 with
                                     |leaf => trinode e1 e2 f1 f2 f3
                                     | _ => (let r := find_closet f3 in
                                             quadnode e1 e2 r f1 f2 (delete r f3) f4)                                             end
                                   else if ble_nat a e1 then
                                   match f1 with
                                     |leaf => quadnode e1 e2 e3 f1 f2 f3 f4
                                     | _ => quadnode e1 e2 e3 (delete a f1) f2 f3 f4                                             end
                                   else if ble_nat a e2 then
                                   match f2 with
                                     |leaf => quadnode e1 e2 e3 f1 f2 f3 f4
                                     | _ => quadnode e1 e2 e3 f1 (delete a f2) f3 f4                                             end
                                   else if ble_nat a e3 then
                                   match f3 with
                                     |leaf => quadnode e1 e2 e3 f1 f2 f3 f4
                                     | _ => quadnode e1 e2 e3 f1 f2 (delete a f3) f4                                             end
                                   else quadnode e1 e2 e3 f1 f2 f3 (delete a f4)
                                 )
| binode e fg fd => (if beq_nat a e then
                       match fg with
                         |leaf => (*MERDE SEUL TRUC QUI MANQUE*) binode e fg fd
                         |_ => (let r := find_closet fg in
                                binode r (delete r fg) fd)
                       end
                     else if ble_nat a e then
                         match fg with
                           |leaf => binode e fg fd
                           | _ => binode e (delete a fg) fd
                         end
                     else
                       match fd with
                         |leaf => binode e fg fd
                         | _ => binode e fg (delete a fd)
                       end
                    )
|leaf => leaf
end.


                       

(*petit test pour savoir si ca marche ou pas*)
Example test_4: exist 21 (delete 21 tree_4) = false.
Proof.
compute.
simpl.
reflexivity.
Qed.

