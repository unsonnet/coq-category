Definition relation (X: Type) := X -> X -> Type.


Class ReflexiveC {A: Type} (R: A -> A -> Type) :=
{
    C_refelxtive (x y : A) : R x y -> R x y
}.
Class SymetricC {A: Type} (R: A -> A -> Type)  :=
{
    C_symetric (x y: A) : R x y -> R y x 
}.
Class TransitiveC {A: Type} (R: relation A) :=
{
    C_transitive (x y z: A) : R x y -> R y z -> R x z 
}.
Class Setoid {A: Type}(R: A -> A -> Type)  `{!ReflexiveC R} `{!SymetricC R} `{!TransitiveC R}. 

Class Setoid3 {A: Type} (R: A -> A -> Type)  := 
{
    R_refelxtive (x y : A) : R x y -> R x y
;   R_symetric (x y: A) : R x y -> R y x 
;   R_transitive (x y z: A) : R x y -> R y z -> R x z
}.


Inductive Z_2 : Type :=
    | O 
    | I.

Definition R_Z_2 (n m: Z_2) : Prop :=
    match n, m with
        | O,O => True
        | I,I => True
        | _, _ => False
        end.

    
#[export] Instance Z2_Set3 : Setoid3 R_Z_2.
Proof.
    constructor; intros [] [] []; simpl; try reflexivity;
    intros; try apply H; try apply H0.
Defined.

#[export] Instance Z2_Ref : ReflexiveC R_Z_2.
Proof.
    constructor; intros [] []; simpl; intros; try apply H; try apply H0.
Defined.

#[export] Instance Z2_Sym : SymetricC R_Z_2.
Proof.
    constructor; intros [] []; simpl; intros; try apply H; try apply H0.
Defined.

#[export] Instance Z2_Tran : TransitiveC R_Z_2.
Proof.
    constructor; intros [] [] []; simpl; intros; try apply H; try ( exfalso; apply H0).
Defined.

#[export] Instance Z2_Set : Setoid R_Z_2. Defined.


Definition R_Trivial_Z_2 (n m: Z_2) : Prop :=
    True.

#[export] Instance Z2_T_Ref : ReflexiveC R_Trivial_Z_2.
Proof.
    constructor; intros [] []; simpl; intros; try apply H; try apply H0.
Defined.

#[export] Instance Z2_T_Sym : SymetricC R_Trivial_Z_2.
Proof.
    constructor; intros [] []; simpl; intros; try apply H; try apply H0.
Defined.

#[export] Instance Z2_T_Tran : TransitiveC R_Trivial_Z_2.
Proof.
    constructor; intros [] [] []; simpl; intros; try apply H; try ( exfalso; apply H0).
Defined.

#[export] Instance Z2_T_Set : Setoid R_Trivial_Z_2. Defined.


(****************************************)
Class Arrows (O: Type): Type := Arrow: O -> O -> Type.
Infix "-->" := Arrow (at level 90, right associativity).


Class CatId O `{Arrows O} := cat_id: forall x , (x --> x).

Class CatComp O `{Arrows O} :=
    comp: forall {x y z}, (y --> z) -> (x --> y) -> (x --> z).
Infix "o" := comp (at level 40, left associativity).


Class Category (O: Type) 
    `{Arrows O} 
    `{forall x y: O, (x --> y) }
    `{CatId O}
    `{CatComp O}: 
    Prop :=
    { arrow_equiv :> forall x y , Setoid Arrow 
    (* ; comp_proper :> forall x y z, Proper (equiv -> equiv -> equiv) comp *)
    ; comp_assoc w x y z (a: w --> x) (b: x --> y) (c: y --> z):
        c o (b o a) = (c o b) o a 
    ; id_l x y `(a: x --> y): cat_id o a = a
    ; id_r x y `(a: x --> y): a o cat_id = a 
    }.