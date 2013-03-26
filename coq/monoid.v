Set Implicit Arguments.
Open Scope list_scope.

Class Monoid (A: Type) := 
{
mempty : A;
mappend : A -> A -> A;
monoid_left_id : 
    forall a: A, 
        mappend mempty a = a;
monoid_right_id : 
    forall a: A, 
        mappend a mempty = a;
monoid_assoc : 
    forall a b c: A, 
        mappend a (mappend b c) = mappend (mappend a b) c
}.

Fixpoint append {A: Type} (xs ys: list A) : (list A) := 
match xs with
| nil => ys
| cons h t => cons h (append t ys)
end.

Instance list_Monoid {A: Type} : Monoid (list A) := 
{
mempty := nil;
mappend := append
}.

Proof.
intros a.
simpl.
reflexivity.

intros.
induction a.
simpl.
reflexivity.
simpl.
rewrite IHa.
reflexivity.

intros.
induction a.
simpl.
reflexivity.
simpl.
rewrite IHa.
reflexivity.
Qed.

Extraction Language Haskell.
Extraction "extraction/append.hs" append.

