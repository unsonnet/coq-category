
(* DONE::// Define semigroups up to abelian groups*)

Class Semigroup (A : Type) (add : A -> A -> A) :=
{
    addrA : forall x y z, add (add x y) z = add x (add y z) 
}.

(* Notation "x + y" := (add x y) (at level 50, left associativity). *)
(*TODO// dont know how to get the infix here *)
(* dont know why the ` is needed below *)
(* maybe the ` is the inheritance symbol? *)

Class Monoid A `{M : Semigroup A} (zero : A) := 
{
    add0r : forall x, add zero x = x;
    addr0 : forall x, add x zero = x
}.

Class ComMonoid A `{M : Monoid A} := 
{ 
    addrC : forall x y, add x y = add y x
}.

Class Group A `{M : Monoid A} (opp : A -> A) := 
{
    addNr : forall x, add (opp x) x = zero
}.

(* ! needed below so that commoid can implicitly 
inherit the monoid instance from G*)

Class AbGroup A `{G : Group A} `{CM : !ComMonoid A}.

Lemma example A `{M : AbGroup A} (a b : A)
  : add (add (opp b) (add b a)) (opp a) = zero.
Proof. 
    rewrite <- addrA.
    rewrite addrC.
    rewrite addNr.
    rewrite add0r with a.
    rewrite addNr.
    reflexivity.
Qed.

(* DONE::// Define the group over 2 elements *)

Inductive Z_2 : Type :=
    | O 
    | I.

Definition add_2 (n m : Z_2): Z_2 :=
    match n, m with 
        | O , O => O 
        | I , I => O
        | O , I => I 
        | I , O => I
    end.


Theorem add_2_assoc : forall x y z : Z_2 , add_2 (add_2 x y) z = add_2 x (add_2 y z).
Proof.
    intros [] [] []; reflexivity.
Qed.

(* #[export] is currently needed because I did not give a scope for the instance *)
#[export] Instance Z2_S : Semigroup Z_2 add_2 := 
{
    addrA := add_2_assoc
}.

(* either provide a predone proof as above
    or enter proof mode and just prove it here and now. *)
#[export] Instance Z2_M : Monoid Z_2 O.
Proof.
    constructor.
    - intros []; reflexivity.
    - intros []; reflexivity.
Defined.

#[export] Instance Z2_CM : ComMonoid Z_2.
Proof.
    constructor.
    intros [] []; reflexivity.
Defined. (* or Qed. *)

Definition opp_2 (n : Z_2): Z_2 :=
    match n with 
        | O => O
        | I => I
    end.

#[export] Instance Z2_G : Group Z_2 opp_2.
Proof.
    constructor; intros []; reflexivity.
Qed.

#[export] Instance Z2_AG : AbGroup Z_2. Defined.

(* DONE:// Define the trivial group on one element *)
Inductive Z_1 : Type :=
    | l.

Definition add_1 (n m : Z_1) : Z_1 := l.

#[export] Instance Z1_S : Semigroup Z_1 add_1.
Proof.
    constructor.
    intros [] [] []; reflexivity.
Defined.

#[export] Instance Z1_M : Monoid Z_1 l.
Proof.
    constructor;
    intros []; reflexivity.
Defined.

#[export] Instance Z1_CM : ComMonoid Z_1.
Proof.
    constructor.
    intros [] []; reflexivity.
Defined.

Definition opp_1 (n : Z_1): Z_1 := l.

#[export] Instance Z1_G : Group Z_1 opp_1.
Proof.
    constructor.
    intros []; reflexivity.
Defined.

#[export] Instance Z1_AG : AbGroup Z_1. Defined.

(* DONE:// Define Z4 *)

Inductive Z_4 : Type :=
    | w 
    | x
    | y
    | z.

Definition add_4 (n m : Z_4) := 
    match n , m with
    | w , w => w 
    | w , x => x
    | w , y => y
    | w , z => z
    | x , w => x
    | x , x => y
    | x , y => z
    | x , z => w 
    | y , w => y
    | y , x => z
    | y , y => w
    | y , z => x
    | z , w => z 
    | z , x => w
    | z , y => x
    | z , z => y
    end.

#[export] Instance Z4_S : Semigroup Z_4 add_4.
Proof.
    constructor.
    intros [] [] []; reflexivity.
Defined.

#[export] Instance Z4_M : Monoid Z_4 w.
Proof.
    constructor;
    intros []; reflexivity.
Defined.

#[export] Instance Z4_CM : ComMonoid Z_4.
Proof.
    constructor.
    intros [] []; reflexivity.
Defined.

Definition opp_4 (n : Z_4): Z_4 :=
    match n with 
        | w => w
        | x => z
        | y => y
        | z => x
    end.

#[export] Instance Z4_G : Group Z_4 opp_4.
Proof.
    constructor.
    intros []; reflexivity.
Defined.

#[export] Instance Z4_AG : AbGroup Z_4. Defined.

(*TODO:// find out how to show a group is a subgroup of another. *)
(* TODO:// define a sub group as an inductive def that takes in 2 groups and a function f
    between the two and shows that f preserves add op and zero which may be enough?*)

Inductive subgroup G H `{M : Group G } `{N : Group H} (f : G -> H) : Prop :=
    | zero_dis : f zero = zero0.
(* TODO:// define group equality as two groups A B  and two functions f g show that 
    A is a subgroup of B and B is a subgroup of A.*)

(* here are libraries for defining cats as classes *)
(*
https://github.com/jwiegley/category-theory/
*)
(*
https://github.com/coq-community/math-classes/blob/master/interfaces/abstract_algebra.v
*)
(*
https://arxiv.org/pdf/1102.1323.pdf
*)