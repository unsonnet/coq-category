
Class Category (Ob: Type) (Hom: Ob -> Ob -> Type) 
:=
{
    id (x : Ob): Hom x x ; (* can also be: id {x}: Hom x x ;*)
    comp {x y z : Ob} (f: Hom y z) (g : Hom x y) : Hom x z ;
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

Theorem AssocZ0 (a b c d: Z_0) (f : HomZ0 c d) (g : HomZ0 b c) (h : HomZ0 a b):
compZ0 a c d f (compZ0 a b c g h) = compZ0 a b d (compZ0 b c d f g) h .
Proof.
    destruct a,b,c,d. reflexivity.
Qed.

Theorem LeftIdZ0 (a b: Z_0) (f : HomZ0 a b): compZ0 a b b (idZ0 b) f = f .
Proof.
    destruct a,b,f. reflexivity.
Qed.

Theorem RightIdZ0 (a b: Z_0) (f : HomZ0 a b): compZ0 a a b f (idZ0 a)= f .
Proof.
    destruct a,b,f. reflexivity.
Qed.

#[export] Instance Z0_C : Category Z_0 HomZ0 :=
    {|  id := idZ0;
        comp := compZ0;
        Assoc := AssocZ0;
        LeftId := LeftIdZ0;
        RightId := RightIdZ0
    |}.
