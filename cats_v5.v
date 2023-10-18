(*
TODO:// make a semi category without ids
*)

Class Category (Ob: Type) (Hom: Ob -> Ob -> Type) 
(id : forall x, Hom x x) (comp : forall {x y z : Ob} (f: Hom y z) (g : Hom x y), Hom x z)
:=
{
    Assoc : forall a b c d (f : Hom c d) (g : Hom b c) (h : Hom a b),
        comp f (comp g h) = comp (comp f g) h ;
    LeftId : forall a b (f : Hom a b), comp (id b) f = f ;
    RightId : forall a b (f : Hom a b), comp f (id a) = f ;
}.

Inductive Z_0 : Type :=
    | O.

Inductive HomZ0 (n m : Z_0) : Type :=
    | Homid.

Definition idZ0 (x : Z_0) : HomZ0 x x :=
    Homid x x.

Definition compZ0 (x y z : Z_0) (f : HomZ0 y z) (g : HomZ0 x y) : HomZ0 x z :=
    Homid x z.

(* if you get an equivalance error with arbitray (cant just destruct the exact morphisms) then you need the setoids in the def*)
#[export] Instance Z0_C : Category Z_0 HomZ0 idZ0 compZ0.
Proof.
    constructor; repeat intros []; reflexivity.
Defined.

(* TODO:// learn github*)
(* TODO:// make functors*)
(* TODO:// make subcats*)
(* TODO:// make embeddings*)
(* TODO:// define naturality*)
(* TODO:// state yolenda lemma*)