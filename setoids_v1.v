Definition relation (X: Type) := X -> X -> Prop.

Definition partial_function {X: Type} (R: relation X) :=
    forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.

Definition reflexive {X: Type} (R: relation X) :=
    forall a : X, R a a.

Definition transitive {X: Type} (R: relation X) :=
    forall a b c : X, (R a b) -> (R b c) -> (R a c).

Definition symmetric {X: Type} (R: relation X):=
    forall a b : X, (R a b) -> (R b a).

Definition antisymmetric {X: Type} (R: relation X):=
    forall a b : X, (R a b) -> (R b a) -> a = b.

Definition equi {X: Type} (R: relation X):=
    (reflexive R) /\ (symmetric R) /\ (transitive R).

Definition order {X:Type} (R: relation X) :=
    (reflexive R) /\ (antisymmetric R) /\ (transitive R).

Definition preorder {X:Type} (R: relation X) :=
    (reflexive R) /\  (transitive R).

Inductive equivalance {X: Type} (R: relation X) : relation X :=
    | Reflexive x : equivalance R x x
    | Symetric x y (Hxy : equivalance R x y) :
        equivalance R y x
    | Transitive x y z
        (Hxy : equivalance R x y)
        (Hyz : equivalance R x y) :
        equivalance R x z.

Inductive equal {X: Type} (R: X->X->Prop) : X -> X -> Prop :=
    | e_step (x y : X) : R x y -> equal R x y
    | e_Reflextive (x : X): equal R x x
    | e_Symetric (x y: X) : equal R x y -> equal R y x 
    | e_Transitive (x y z: X) : equal R x y -> equal R y z -> equal R x z.

(* Class Setoid2 {A: Type} `{R: relation A} (E: equal R). := 
{
    equal_relate : equal R
}. *)

Class ReflexiveC {A: Type} (R: relation A) :=
{
    C_refelxtive (x y : A) : R x y -> R x y
}.
Class SymetricC {A: Type} (R: relation A) :=
{
    C_symetric (x y: A) : R x y -> R y x 
}.
Class TransitiveC {A: Type} (R: relation A) :=
{
    C_transitive (x y z: A) : R x y -> R y z -> R x z 
}.
Class Setoid4 {A: Type} (R: relation A) `{!ReflexiveC R} `{!SymetricC R} `{!TransitiveC R}. 

Class Setoid3 {A: Type} (R: relation A) := 
{
    R_refelxtive (x y : A) : R x y -> R x y
;   R_symetric (x y: A) : R x y -> R y x 
;   R_transitive (x y z: A) : R x y -> R y z -> R x z
}.

Class Setoid {A: Type} (R: relation A) := 
{
    equal_relate : equi R
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

#[export] Instance Z2_Set : Setoid R_Z_2.
Proof.
    constructor.
    unfold equi.
    repeat try split.
    -   unfold reflexive.
        intros []; reflexivity.
    -   unfold symmetric.
        intros [] []; simpl; try reflexivity; intro H; apply H.
    -   unfold transitive.
        intros [] [] []; simpl; intros; try apply H; try (exfalso ; apply H0).
Defined.
    
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

#[export] Instance Z2_Set4 : Setoid4 R_Z_2.



