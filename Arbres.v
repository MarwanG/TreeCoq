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
Require Import Bool.

(* Structure of the tree which includes 4 types of objects *)
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


(* Definition of different trees *)

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
          
(* Function to test if value is equal or less than l*)

Fixpoint ble_nat (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => ble_nat n' m'
      end
  end.

(*Function to test if value is equal *)
Fixpoint eq_nat (n m : nat) : bool :=
match (n,m) with
|(0,0) => true
|(0,S m') => false
|(S n' , 0) => false
|(S n',S m') => eq_nat n' m' 
end.

(* Function to test if value a exists in the T  *)

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


(* Examples for function exist *)

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

(* Examples *)

Definition ex1 : tree nat :=
(add 1 ( add 5 (add 15 (add 13 (add 3 (add 14 (add 2 (leaf)))))))).

Definition ex2 : tree nat :=
  (add 1 ( add 5 (add 2 (leaf)))).

Example test_5: exist 15 ex1 = true.
Proof.
compute.
reflexivity.
Qed.

Example test_6: exist 7 ex1 = false.
Proof.
compute.
reflexivity.
Qed.

Example test_7: exist 2 ex1 = true.
Proof.
compute.
reflexivity.
Qed.

                           

(* function places all values of T in a tree except for a *)
                         
Fixpoint to_list (a:nat)(T: tree nat): list nat :=
  match T with
    |trinode e1 e2 fg fm fd => (if beq_nat e1 a then
                                  e2 :: (to_list a fg) ++ (to_list a fd) ++ (to_list a fm)
                                else if beq_nat e2 a then
                                  e1 :: (to_list a fg) ++ (to_list a fd) ++ (to_list a fm)
                                else
                                  e1 :: e2 :: (to_list a fg) ++ (to_list a fd) ++ (to_list a fm)
                               )
    |quadnode e1 e2 e3 f1 f2 f3 f4 => (if beq_nat e1 a then
                                  e2 :: e3 :: (to_list a f1) ++ (to_list a f2) ++ (to_list a f3) ++ (to_list a f4)
                                else if beq_nat e2 a then
                                  e1 :: e3  :: (to_list a f1) ++ (to_list a f2) ++ (to_list a f3) ++ (to_list a f4)
                                else if beq_nat e3 a then
                                  e1 :: e2 :: (to_list a f1) ++ (to_list a f2) ++ (to_list a f3) ++ (to_list a f4)          
                                else
                                  e1 :: e2 :: e3 :: (to_list a f1) ++ (to_list a f2) ++ (to_list a f3) ++ (to_list a f4)
                                )
    |binode e1 f1 f2 =>(if beq_nat e1 a then
                          (to_list a f1) ++ (to_list a f2)
                        else
                          a :: (to_list a f1) ++ (to_list a f2)
                        )
    |leaf => nil
  end.


(* function that converts a list into a tree *)

Fixpoint from_list (l : list nat): tree nat :=
match l with
  |x :: xs => add x (from_list xs)
  | nil => leaf
end.


(* function to the delete a from T *)

Definition delete (a:nat)(T: tree nat): tree nat :=
  from_list (to_list a T).


Example test_8: to_list 5 ex2 = 1::2::nil.
Proof.
compute.
reflexivity.
Qed.

Example test_9: exist 5 (delete 5 ex2) = false.
Proof.
compute.
reflexivity.
Qed.

Fixpoint count (T: tree nat): nat :=
  match T with
    |leaf => 0
    |binode _ f1 f2 => 1 + (count f1) + (count f2)
    |trinode _ _ f1 f2 f3 => 2 + (count f1) + (count f2) + (count f3)
    |quadnode _ _ _ f1 f2 f3 f4 => 3 + (count f1) + (count f2) + (count f3) + (count f4)           end.  


Definition equals_nb (t1: tree nat)(t2 : tree nat): bool :=
  beq_nat (count t1) (count t2).
  

Fixpoint equals_value (t1 : tree nat)(t2 : tree nat): bool :=
  match t1 with
    |leaf => true
    |binode e1 f1 f2 => andb (andb (exist e1 t2)  (equals_value f1 t2)) (equals_value f2 t2) 
    |trinode e1 e2 f1 f2 f3 =>  (andb
                                   (andb
                                      (andb (exist e1 t2)  (exist e2 t2))
                                      (andb (equals_value f1 t2)  (equals_value f2 t2)))
                                   (equals_value f3 t2))
    |quadnode e1 e2 e3 f1 f2 f3 f4 => (andb  (andb
                                          (andb (exist e1 t2) (exist e2 t2))
                                          (andb (exist e3 t2) (equals_value f1 t2)))
                                       (andb
                                          (andb (equals_value f2 t2) (equals_value f3 t2))
                                          (equals_value f4 t2)))
  end.

Definition equal (t1: tree nat)(t2: tree nat) : bool :=
  andb (equals_value t1 t2) (equals_nb t1 t2).


Example test_10: equal tree_4 tree_4  = true.
Proof.
compute.
reflexivity.
Qed.

Example test_11:equal tree_4 tree_3 = false.
Proof.
compute.
reflexivity.
Qed.


Definition max (a:nat) (b:nat) : nat :=
if ble_nat b a 
then a else b.

Definition min (a:nat) (b:nat) :nat :=
if ble_nat b a 
then b else a.

Fixpoint hauteurMax(t:tree nat ) : nat :=
match t with
|leaf => 0
|binode _ tg td => 1 + (max (hauteurMax tg) (hauteurMax td))
|trinode _ _ tg tm td => 1 + (max (hauteurMax tg) (max (hauteurMax tm) (hauteurMax td)))
|quadnode _ _ _ t1 t2 t3 t4 => 1+ (max (hauteurMax t1) (max (hauteurMax t2) (max (hauteurMax t3) (hauteurMax t4))))
end.

Fixpoint hauteurMin(t:tree nat ) : nat :=
match t with
|leaf => 0
|binode _ tg td => 1 + (min (hauteurMax tg) (hauteurMax td))
|trinode _ _ tg tm td => 1 + (min (hauteurMax tg) (min (hauteurMax tm) (hauteurMax td)))
|quadnode _ _ _ t1 t2 t3 t4 => 1+ (min (hauteurMax t1) (min (hauteurMax t2) (min (hauteurMax t3) (hauteurMax t4))))
end.

(* inspiré de lafonction estComplet
http://pauillac.inria.fr/~cheno/taupe/transparents/arbres-par4.pdf *)

Fixpoint estEquilibre (t : tree nat) : bool :=
match t with
|leaf =>true
|binode _ tg td =>  if (beq_nat (hauteurMax tg) (hauteurMax td)) then 
                      andb (estEquilibre tg) (estEquilibre td)
                      else false

|trinode _ _ tg tm td =>  if (beq_nat (hauteurMax tg) (hauteurMax td)) then
                              if (beq_nat (hauteurMax tg) (hauteurMax tm)) then
                                  (estEquilibre tg) && (estEquilibre td) && (estEquilibre tm)
                                 else false
                         else false
|quadnode _ _ _ t1 t2 t3 t4 => if (beq_nat (hauteurMax t1) (hauteurMax t2)) then
                                   if (beq_nat (hauteurMax t1) (hauteurMax t3)) then
                                      if (beq_nat (hauteurMax t1) (hauteurMax t4 )) then
                                         (estEquilibre t1) && (estEquilibre t2) && (estEquilibre t3) && (estEquilibre t4)
                                      else false
                                   else false
                                else false
end.


(* PROBLEM WITH MATCH AFTER MATCH NEED HELP !!! THEN SHOULD START LEMMES ONCE THIS IS DONE *)

Fixpoint ordered(t: tree nat): bool :=
  match t with
    |leaf => true
    |binode e f1 f2 => match f1 with
                         |leaf => true
                         |binode e1 _ _ => if ble_nat e1 e then
                                            ordered f1
                                          else
                                            false
                         |trinode e1 e2 _ _ _ => if ble_nat e2 e then
                                                    ordered f1
                                                  else
                                                    false
                         |quadnode e1 e2 e3 _ _ _ _ => if (ble_nat e3 e) then
                                                         ordered f1
                                                       else
                                                        false
                       end
    |trinode e1 e2 f1 f2 f3 => if ble_nat e1 e2 then(
                                 match f1 with  (*first son smaller than e *)
                                   |leaf => true
                                   |binode e1' _ _ => if ble_nat e1' e1 then
                                                      ordered f1
                                                    else
                                                      false
                                   |trinode _ e2' _ _ _ => if ble_nat e2' e1 then
                                                             ordered f1
                                                           else
                                                             false
                                   |quadnode _ _ e3' _ _ _ _ => if ble_nat e3' e1 then
                                                                  ordered f1
                                                                else
                                                                  false
                                 end
                                 (*match f2 with
                                   |leaf => true
                                   |binode e1' _ _ => if andb (ble_nat e1 e1')(ble_nat e1' e2) then
                                                        ordered f2
                                                      else
                                                        false
                                   |trinode _ e2' _ _ _ => if andb (ble_nat e1 e2')(ble_nat e2' e2) then
                                                             ordered f2
                                                           else
                                                             false
                                   |quadnode _ _ e3' _ _ _ _ => if andb (ble_nat e1 e3') (ble_nat e2 e3') then
                                                                  ordered f2
                                                                else
                                                                  false
                                     end*)
                                    match f3 with
                                     |leaf => true
                                     |binode e1' _ _ => if ble_nat e2 e1' then
                                                          ordered f3
                                                        else
                                                          false
                                     |trinode _ e2' _ _ _ => if ble_nat e2 e2' then
                                                               ordered f3
                                                             else
                                                               false
                                     |quadnode _ _ e3' _ _ _ _ => if ble_nat e2 e3' then
                                                                    ordered f3
                                                                  else
                                                                    false
                                   end
                               )else
                                  false
                                 
    |_ => true
  end.

(*
Fixpoint ordered (t: tree nat): bool :=
  match t with
    |leaf => true 
    |binode e f1 f2 => match f1 with  (*first son smaller than e  *)
                         |leaf => true
                         |binode e1 _ _ => if ble_nat e1 e then
                                             ordered f1
                                           else
                                             false
                         |trinode e1 e2 _ _ _ => if ble_nat e2 e then
                                                    ordered f1
                                                  else
                                                    false
                         |quadnode e1 e2 e3 _ _ _ _ => if (ble_nat e3 e) then
                                                         ordered f1
                                                       else
                                                         false
                        end
                       match f2 with (*second son bigger than e*)
                         |binode e1 _ _ => if ble_nat e e1 then
                                             ordered f2
                                           else
                                             false
                         |trinode e1 e2 _ _ _ => if ble_nat e e2 then
                                                    ordered f2
                                                  else
                                                    false
                         |quadnode e1 e2 e3 _ _ _ _ => if ble_nat e e3 then
                                                         ordered f2
                                                       else
                                                         false
                         |leaf => true
                        end  
    |trinode e1 e2 f1 f2 f3 => if ble_nat e1 e2 then
                                 match f1 with  (*first son smaller than e *)
                                   |leaf => true
                                   |binode e1' _ _ => if ble_nat e1' e1 then
                                                      ordered f1
                                                    else
                                                      false
                                   |trinode _ e2' _ _ _ => if ble_nat e2' e1 then
                                                             ordered f1
                                                           else
                                                             false
                                   |quadnode _ _ e3' _ _ _ _ => if ble_nat e3' e1 then
                                                                  ordered f1
                                                                else
                                                                  false
                                 end
                                   match f2 with
                                     |leaf => true
                                     |binode e1' _ _ => if andb (ble_nat e1 e1')(ble_nat e1' e2) then
                                                          ordered f2
                                                        else
                                                          false
                                     |trinode _ e2' _ _ _ => if andb (ble_nat e1 e2')(ble_nat e2' e2) then
                                                               ordered f2
                                                             else
                                                               false
                                     |quadnode _ _ e3' _ _ _ _ => if andb (ble_nat e1 e3') (ble_nat e2 e3') then
                                                                    ordered f2
                                                                  else
                                                                    false
                                    end
                                   match f3 with
                                     |_ => true
                                     |binode e1' _ _ => if ble_nat e2 e1' then
                                                          ordered f3
                                                        else
                                                          false
                                     |trinode _ e2' _ _ _ => if ble_nat e2 e2' then
                                                               ordered f3
                                                             else
                                                               false
                                     |quadnode _ _ e3' _ _ _ _ => if ble_nat e2 e3' then
                                                                    ordered f3
                                                                  else
                                                                    false
                                   end
                               else
                                 false
    |quadnode e1 e2 e3 f1 f2 f3 f4 => if andb (ble_nat e1 e2) (ble_nat e2 e3) then
                                        match f1 with  (*first son smaller than e *)
                                          |leaf => true
                                          |binode e1' _ _ => if ble_nat e1' e1 then
                                                               ordered f1
                                                             else
                                                               false
                                          |trinode _ e2' _ _ _ => if ble_nat e2' e1 then
                                                                    ordered f1
                                                                  else
                                                                    false
                                          |quadnode _ _ e3' _ _ _ _ => if ble_nat e3' e1 then
                                                                         ordered f1
                                                                       else
                                                                         false
                                        end
                                        match f2 with
                                          |_ => true
                                          |binode e1' _ _ => if andb (ble_nat e1 e1')(ble_nat e1' e2) then
                                                               ordered f2
                                                             else
                                                               false
                                          |trinode _ e2' _ _ _ => if andb (ble_nat e1 e2')(ble_nat e2' e2) then
                                                                    ordered f2
                                                                  else
                                                                    false
                                          |quadnode _ _ e3' _ _ _ _ => if andb (ble_nat e1 e3') (ble_nat e2 e3') then
                                                                         ordered f2
                                                                       else
                                                                         false
                                        end
                                        match f3 with
                                          |_ => true
                                          |binode e1' _ _ => if andb (ble_nat e2 e1')(ble_nat e1' e3) then
                                                               ordered f3
                                                             else
                                                               false
                                          |trinode _ e2' _ _ _ => if andb (ble_nat e1 e2')(ble_nat e2' e2) then
                                                                    ordered f3
                                                                  else
                                                                    false
                                          |quadnode _ _ e3' _ _ _ _ => if andb (ble_nat e2 e3')(ble_nat e3' e3) then
                                                                         ordered f3
                                                                       else
                                                                         false                   
                                        end
                                        match f4 with
                                          |_ => true
                                          |binode e1' _ _ => if ble_nat e3 e1 then
                                                               ordered f4
                                                             else
                                                               false
                                          |trinode _ e2' _ _ _ => if ble_nat e3 e2' then
                                                                    ordered f4
                                                                  else
                                                                    false
                                          |quadnode _ _ e3' _ _ _ _ => if ble_nat e3 e3' then
                                                                         ordered f4
                                                                       else
                                                                         false
                                        end
                                      else
                                        false
  end. *)



