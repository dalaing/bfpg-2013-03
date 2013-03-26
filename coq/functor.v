
Require Import Coq.Program.Basics.
Set Implicit Arguments.
Open Scope list_scope.

Definition id {A: Type} (e: A): A := e.
 
Class Functor (F: Type -> Type) :=
{
fmap : forall (A B: Type), (A -> B) -> F A -> F B;
functor_id : 
    forall (A: Type) (e: F A), 
        fmap id e = e;
functor_compose : 
    forall (A B C: Type) (f: A -> B) (g: B -> C) (e: F A), 
        fmap (compose g f) e = fmap g (fmap f e) 
}.

Fixpoint map (A B: Type) (f: A -> B) (xs: list A) : list B :=
match xs with
| nil => nil
| cons h t => cons (f h) (map f t)
end.

Instance list_Functor : Functor list := 
{
fmap := map
}.

(* Thanks to Adam Chlipala *)
Load CpdtTactics.

Proof.
induction e; crush.
induction e; crush.
Qed.

Extraction Language Haskell.
Extraction "extraction/map.hs" map.

