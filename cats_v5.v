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

 Inductive Z_1 : Type :=
    | M 
    | N.

Inductive HomZ1 : Z_1 -> Z_1 -> Type :=
    | Homid1 (n: Z_1): HomZ1 n n
    | HomMN : HomZ1 M N
    | HomCom (x y z: Z_1) (f : HomZ1 y z) (g : HomZ1 x y) : HomZ1 x z.

Definition idZ1 (x : Z_1) : HomZ1 x x :=
    Homid1 x.

Definition compZ1 (x y z : Z_1) (f : HomZ1 y z) (g : HomZ1 x y) : HomZ1 x z :=
    HomCom x y z f g.

#[export] Instance Z1_C : Category Z_1 HomZ1 Homid1 HomCom.
Proof.
    (* constructor. repeat intros []. reflexivity. *)
    constructor.
    - intros. rewrite <- f.     
Defined.
