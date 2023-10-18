(*
    Definitions from https://arxiv.org/pdf/1102.1323.pdf
    https://arxiv.org/abs/1102.1323
    *)


(* TODO:// finish the transcription of the classes
 and verify if any libraries are needed *)
Class Arrows (O: Type): Type := Arrow: O -> O -> Type.
Infix "-->" := Arrow (at level 90, right associativity).


Class CatId O `{Arrows O} := cat_id: forall x , (x --> x).

Class CatComp O `{Arrows O} :=
    comp: forall {x y z}, (y --> z) -> (x --> y) -> (x --> z).
Infix "o" := comp (at level 40, left associativity).



Class Category (O: Type) 
    `{Arrows O} 
    (* `{forall x y: O, Equiv (x --> y) } *)
    `{CatId O}
    `{CatComp O} 
    :=
    { 
        (* arrow_equiv :> forall x y, Setoid (x --> y)
    ; comp_proper :> forall x y z, Proper (equiv -> equiv -> equiv) comp *)
    comp_assoc : forall w x y z, 
    (y --> z) o ((x --> y) o (w --> x)) = (( y --> z )o (x --> y)) o (w --> x)
    ; id_l x y : forall (a: x --> y), cat_id o a = a
    ; id_r x y : forall (a: x --> y), a o cat_id = a 
    }.

(*
Class Category (O: Type) 
    `{Arrows O} 
    `{forall x y: O, Equiv (x --> y) }
    `{CatId O}
    `{CatComp O}: 
    Prop :=
    { arrow_equiv :> forall x y, Setoid (x --> y)
    ; comp_proper :> forall x y z, Proper (equiv -> equiv -> equiv) comp
    ; comp_assoc w x y z (a: w --> x) (b: x --> y) (c: y --> z):
        c o (b o a) = (c o b) o a 
    ; id_l `(a: x --> y): cat_id o a = a
    ; id_r `(a: x --> y): a o cat_id = a 
    }.
*)