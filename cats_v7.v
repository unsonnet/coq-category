Class SemiCategory (Ob: Type) (Hom: Ob -> Ob -> Type) 
(comp : forall {x y z : Ob} (f: Hom y z) (g : Hom x y), Hom x z)
: Type
:=
{
    Assoc : forall a b c d (f : Hom c d) (g : Hom b c) (h : Hom a b),
        comp f (comp g h) = comp (comp f g) h
}.

Class Category Ob `{M: SemiCategory Ob} 
(id : forall x, Hom x x) 
: Type
:=
{
    LeftId : forall a b (f : Hom a b), comp a b b (id b) f = f ;
    RightId : forall a b (f : Hom a b), comp a a b f (id a) = f ;
}.

Class Functor C D `{M: Category C} `{N: Category D} (fobj: C -> D)
 ( fmap : forall {x y : C} (f : Hom x y), Hom0 (fobj x) (fobj y) ): Type :=
{ 
    fmap_id {x : C} : fmap (id0 x) = id1 (fobj x);
    fmap_comp {x y z : C} (f : Hom y z) (g : Hom x y) :
        fmap (comp x y z f g) = comp0 (fobj x) (fobj y) (fobj z) (fmap f) (fmap g)
  }.