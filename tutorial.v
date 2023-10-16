(** * A one-hour tutorial with the Coq proof assistant

The purpose of this tutorial is to give a practical glimpse of the proof assistant Coq, in less that one hour :O.

Hopefully, you can run code in this same page you are currently reading in your web browser.
It is possible to add some code or edit it in this same page, at any line. Feel free to experiment! 

The following command loads the SSReflect plugin and activates the SSReflect set of tactics. *)

From Coq Require Import ssreflect.

(** With this set of tactics, one can achieve the same formal proofs with fewer tactics to know.*)

(** * A few properties involving lists 
You are probably looking forward to see some proof scripts in action. We are going replay some little proof scripts around lists.
Therefore, we need a definition of lists. Lists are already defined in the standard library of Coq. One can import some definitions and results about lists with the command [From Coq Require Import List]. 

Instead, we are going write our own definition. *)
Section OurLists.

Variable (A : Type).

Inductive list : Type :=  
| empty : list 
| add : A -> list -> list.
(** ** The type system 
The Coq proof assistant is based on the Calculus of Constructions.
In this proof assistant, any object (we should rather say term) has a type.
One can check the type of an object (we should rather say "term") with the [Check] command, for example: *)
Check add.
(** The answer to this last command means that the constant [add] has type [A -> list -> list].
In other words, the constant [add] is a function that eats a first argument of type [A], then eats a second argument of type [list]. The output value has type [list].
We also say that [add] inhabits [A -> list -> list]. 
We also say that [add] is an inhabitant of [A -> list -> list].
We also say that [A -> list -> list] is inhabitated by [add].
We also write [add : A -> list -> list].
The type itself has a type. *)
Check A -> list -> list.
Check Type.
Check list.
Check A.
Check add.
Check empty.
(** The [Variable] command we have used above can be used to add to the context an arbitrary variable with a given type.
It provides a convenient way to try partial applications and check that they are accepted by the proof assistant. 
An example of partial application is the term [add a] below. 
It is called a partial application, because the function [add] expects two arguments, but we provide only one. *)
Section PartialApplicationExample.

Variable (a : A).
Variable (l : list).
Check (add a).
Check (add a l).

End PartialApplicationExample.
(* ** Dependent type 
The arrow [->] is a particular case of dependant quantification.
 *)
Section MorePartialApplication.
Variable (B' : A -> Type).
Check (forall (x : A), B' x).
Variable (B : Type).
Check (forall (x : A), B).
End MorePartialApplication.
(** We see that [A -> B] is a special case of the type [forall (x : A), B] where the variable [x] does not occur in [B]. 
If a function has one of those types, it consumes an argument of type [A] and outputs a value. The type of the output may or may not depend on the argument. In the non-dependent case the output has type [B]. In the dependent case, which generalises the dependent case, the output has type [B x] for some value [x] of type [A]. In the dependent case, the type of the output varies according to the input value. *)

(** * Inductive type 
The ability to define an inductive type is a mechanism that let one define a new type and ways to create inhabitants of that type. 
We give the new (inductive) type a name and provide a finite number of constructors.
After each vertical bar [|] is introduced a constructor (see our definition of [list]) but the first bar can be ommited.
Each constructor is given a name and a type (or signature). 
The ending type of a constructor must be the inductive type that is being defined,
because once it has consumed each argument, the result is expected to have the new type.
A constructor may consume no argument (one also says that it has arity 0) as it is the case for the constructor [empty].
The values inhabitating the inductive type are the only possible values.
One can visualise a value (belonging to an inductive type) as a finite tree where each node is labeled by one of the constructors. 
(Indeed, an inductive type can be used to describe the syntax tree of a programming language.)
The children of the node are the necessary arguments of the constructor.

You are invited to try to define your own inductive types! :) 
For instance, one can define natural numbers, booleans, etc. *)

(** We now define a function [concat] that eats two lists and outputs a list. 
The output is the concatenation of the lists.
While being defined, the (name of the) function itself is used in the body of its definition.
It is said that the function is recursive. 
*)
Fixpoint concat (l m : list) : list :=
match l with
| empty => m
| add a l' => add a (concat l' m)
end. 

(** This definition uses a feature called "pattern matching" between the keywords [match] and [end].
Since [l] holds in an inductive type, it can be obtained only though the application of one of the constructors. As a result, one can match it against potential applications of constructors. For instance, in this specific case, a list [l] is either [empty] or [add a l'] for some [a : A] and some [l' : list]. In the body of the function, the argument [l] is first matched against [empty]. If [l] is the value [empty] then the function outputs the second argument [m],
else [l] is matched against the pattern [add a l'].
In the latter case, the system tries to fill the variables [a] and [l'] so that [add a l'] is [l].
The order of the patterns matters, because if two or more patterns apply, the first one only is used and the following ones are skipped.
The pattern matching must be exhaustive - that is at least one pattern can be applied - otherwise the function may not effectively compute. (It may arise that we know that some pattern cases cannot be reached. This can be formally stated and proved afterwards.)
This exhaustiveness is checked by the proof assistant and it will complain if it cannot see it.
*)

(** In general, a function may not terminate on some inputs.
However, the proof assistant Coq let you write only terminating functions. *)

Fail Fixpoint non_terminate (l : list) : list :=
match l with
| empty => empty
| add a l' => non_terminate (add a l)
end. 
(** It is good news, since we get guarantee of termination for free. In other words, we do not need to formally state and prove the termination.
There are ways to emulate non-terminating functions, if necessary; this won't be tackled in this page. *)

(** In the section below, the command [Compute] is introduced, just to show that it is possible to run computations within the proof assistant. Later, in a similar way, computations will be done within goals (of proofs) with the tactic [rewrite /=]. *)
Section ComputeExample.

Variables (a b c d e : A).
Check (add a (add b (add c empty))).
Compute (add a (add b (add c empty))).
Compute (concat (add a (add b (add c empty))) 
                (add d (add e empty))).

End ComputeExample.
(** The concatenation of the lists [[a b c]] and [[d e]] results in the list [[a b c d e]]. *)

Check (forall (l m n : list), 
         concat (concat l m) n = concat l (concat m n)).
(** We see a new type, [Prop]. 
The type [Prop] is the type of (mathematical) statements.
The question of truth (through providing a proof) is dealt with a posteriori. 

Let's say we have some [P] of type [Prop].
A proof [pr] of [P] is an inhabitant of [P].
We have [P : Prop] and if one is able to provide some [pr] such that [pr : P]
then [pr] is a proof of [P].*)

(** In the first proof script below, some tactics are introduced: 

[elim:] 

[rewrite /=] 

[move=>] 

[rewrite] 

[by []] *)
Lemma associative_concat : forall (l m n : list),
concat (concat l m) n = concat l (concat m n).
Proof.
move=> l.
move=> m.
move=> n.
elim: l.
+ rewrite /=.
  by [].
+ move=> a.
  move=> l'.
  move=> IH.
  rewrite /=.
  rewrite IH.
  by [].
Show Proof.
Qed.
(** The [Show Proof] command displays the term currently being built.
Just at the end of a successful proof (before an accepted [Qed] command) it displays the whole term whose type is the statement. 
Below we have just copied the result of the [Show Proof] command (some variables need to be renamed). 
You can see that it is a well-formed object, whose type is exactly the statement we wanted to prove.
In other words, the following chunck of code is a proof of the statement. *)
Check ((fun l m n : list =>
  (fun (x : (fun l0 : list =>
  concat (concat l0 m) n =
concat l0 (concat m n))
  empty) (y : forall (a : A) (l0 : list),
  (fun l1 : list =>
  concat
  (concat
  l1 m)
  n =
concat l1
  (concat
  m n))
  l0
-> (fun l1 : list =>
  concat
  (concat
  l1
  m)
  n =
concat
  l1
  (concat
  m
  n))
  (add a l0)) =>
  list_ind
  (fun l0 : list =>
  concat (concat l0 m) n =
concat l0 (concat m n))
  x y
  l)
  eq_refl
  (fun (a : A) (l' : list) (IH : concat (concat l' m)
  n =
concat l'
  (concat m n)) =>
  (fun x : add a (concat l' (concat m n)) =
add a (concat l' (concat m n)) =>
  eq_ind_r
  (fun z : list =>
  add a z =
add a (concat l' (concat m n)))
  x
  IH)
  eq_refl))).
(** It is convenient not to have to provide this chunck of code by oneself in order to prove the statement.
Instead, we use the tactics language between the keywords [Proof] and [Qed] in a similar same way
we do reasoning steps in a pen-and-paper mathematical proof. This feature can be seen as a kind of assistance from the system to let one guide it through writing a proof-term.

A tool that provides only the check of formal proofs is called proof checker.
Tools such as Coq which provide more features around the proof-checker are called proof assistants. 
The automation features are not addressed in this tutorial.
Getting higher level of confidence in the statements of the checked proofs requires higher level of confidence in the type-checker (.i.e. it does not contain bug). *)

(** The following piece of code just shows an alternate way to express the lemma [associative_concat]. *)
Lemma associative_concat' (l m n : list) :
concat (concat l m) n = concat l (concat m n).
Proof.
elim: l.
+ rewrite /=.
  by [].
+ move=> a.
  move=> l'.
  move=> IH.
  rewrite /=.
  rewrite IH.
  by [].
Qed.

(** In the following proof, a new tactic [case:] is introduced. *)
Lemma concat_empty_left (l m : list) :
concat l m = empty -> l = empty.
Proof.
case: l.
+ move=> _.
  by [].
+ move=> a. 
  move=> l'.
  rewrite /=.
  by [].
Qed.

Section TestPartialApplications.

Variables (a b : list).

Check concat_empty_left.
Check concat_empty_left a.
Check concat_empty_left b.
Check concat_empty_left a b.

End TestPartialApplications.

(** In the following proof, a new tactic [apply:] is introduced. *)
Lemma concat_empty_right (l m : list) :
concat l m = empty -> m = empty.
Proof.
move=> H.
have l_empty : l = empty.
+ apply: (concat_empty_left l m).
  apply: H.
+ move: H.
  rewrite l_empty.
  rewrite /=.
  by [].
Qed.

Fixpoint append (a : A) (l : list) : list :=
match l with
| empty => add a empty
| add b l' => add b (append a l') 
end.

Lemma concat_append (a : A) (l m : list) : 
append a (concat l m) = concat l (append a m).
Proof.
elim: l.
+ rewrite /=.
  by [].
+ move=> b.
  move=> l'.
  move=> IH.
  rewrite /=.
  rewrite IH.
  by [].
Qed.

Fixpoint reverse (l : list) : list :=
match l with
| empty => empty
| add a l' => append a (reverse l')
end.

Lemma reverse_reverse (l : list) :
  reverse (reverse l) = l.
Proof.
elim: l.
+ rewrite /=.
  by [].
+ move=> a.
  move=> l'.
  move=> IH.
  rewrite /=.
  have H : forall (m : list), 
             reverse (append a m) = add a (reverse m).
  - admit.
  - Check (H (reverse l')).
    rewrite (H (reverse l')). (* Indeed it suffices to write: rewrite H. *)
    rewrite IH.    
    by [].
Abort.

Lemma reverse_append (a : A) (m : list) : 
  reverse (append a m) = add a (reverse m).
Proof.
elim: m.
+ rewrite /=.
      by [].
+ move=> b.
  move=> n.
  move=> IH.
  rewrite /=.
  rewrite IH.
  by [].
Qed.

Lemma reverse_reverse (l : list) :
  reverse (reverse l) = l.
Proof.
elim: l.
+ rewrite /=.
  by [].
+ move=> a.
  move=> l'.
  move=> IH.
  rewrite /=.
  - Check (reverse_append a (reverse l')).
    rewrite (reverse_append a (reverse l')).
    rewrite IH.    
    by [].
Qed.

Lemma reverse_concat (l m : list) :
reverse (concat l m) = concat (reverse m) (reverse l).
Proof.
elim: l.
+ rewrite /=.
Abort.

Lemma concat_l_empty (l : list) :
concat l empty = l.
Proof.
elim: l.
+ rewrite /=.
  by [].
+ move=> a.
  move=> m. 
  move=> IH.
  rewrite /=.
  rewrite IH.  
  by [].
Qed.

Lemma reverse_concat (l m : list) :
reverse (concat l m) = concat (reverse m) (reverse l).
Proof.
elim: l.
+ rewrite /=.
  rewrite concat_l_empty.
  by [].
+ move=> a.
  move=> l.
  move=> IH.
  rewrite /=.
  rewrite IH.
  rewrite concat_append.
  by [].
Qed.

End OurLists.

Section MapList.

Check list.

Variables (A B : Type).
Variable (f : A -> B).

Check list A.
Check list B.
Check empty.
Check empty A.
Check empty B.
Check add.
Check add A.
Check add B.


Fixpoint map (l : list A) : list B :=
match l with
| empty _ => empty B
| add _ a l' => add _ (f a) (map l')
end.

Lemma map_concat (l m : list A) : 
  map (concat _ l m) = concat _ (map l) (map m).
Proof.
elim: l.
+ rewrite /=.
  by [].
+ move=> a. 
  move=> l'.
  move=> IH.
  rewrite /=.
  rewrite IH.
  by [].
Qed.

End MapList.

Section MoreList.

Variable (A : Type).

Lemma concat_append' (a : A) (l m : list A) : 
append _ a (concat _ l m) = concat _ l (append _ a m).
Proof.
elim: l.
+ rewrite /=.
  by [].
+ move=> b.
  move=> l'.
  move=> IH.
  rewrite /=.
  rewrite IH.
  by [].
Qed.

End MoreList.

(** ** Some links 
One can check this page:
https://bevis.w.uib.no/

Feel free to ask me any question around the proof assistant, in-person or by sending me an e-mail.
One can find lots of technical information about the Coq proof assistant here:
https://coq.inria.fr/doc/

You probably first need to pick a version of Coq you want to use and click on "User manual".
The online community use some channels where beginners can search for previous messages and ask questions. You can find more information about these channels here:
https://coq.inria.fr/community *)

(** ** Credit
This web page is hosted on the Norwegian Research and Education Cloud, NREC :)
The position of the author is funded by the Research Council of Norway, Norges forskningsrådet (through the project Symboalgo).
This web page uses a template kindly made by Emilio Jesús Gallego Arias and available here:
https://github.com/jscoq/coqdoc-template
This template offers a quick way to use jsCoq. The latter let us try some Coq code in web browsers, which I hope is more koselig.

The cheatsheet is a modification of the cheatsheet made available by Enrico Tassi, here:
https://github.com/gares/math-comp-school-2022/commits/master/cheat-sheet *)

(** * Feedback, please!
I would like to listen to or read your feedback!
You can also write directly there:
https://docs.google.com/document/d/13Ec6Ybij6PLfIn1_Vgr8lKqa7lsfibrKHioBBiZdy_0/edit?usp=sharing

This tutorial targets PhD students in informatics. 

If there there were no talk, what written information would be missing to understand?

In a 3-page limit tutorial about Coq, what would you like to see or learn? *)
