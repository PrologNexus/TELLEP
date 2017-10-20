:- module(tellep_al, []).
:- reexport(tellep_op).

/** <module> TELLEP: AL

AL rules.

@author Wouter Beek
@version 2017/10
*/

:- use_module(tellep_print).

/* bottom concept
FL_0, FL^-, AL

a . ¬C
a .  C
──────
⊥
*/
bottom_concept@
  A :: not C, A :: C <=>
  chr_msg(rule([A :: not C,A :: C],[concept(fail)])) |
  fail.

/* intersection
FL_0, FL^-, AL

a . C ⊓ D
─────────
a . C
a . D
*/
intersection@
  A :: C and D <=>
  chr_msg(rule([A :: C and D],[A :: C,A :: D])) |
  A :: C, A :: D.

/* limited existential quantification
FL^-, AL

a . ∃R C
──────────
〈a,b〉 . R
b . C
*/
limited_existential_quantification@
  A :: R some C <=>
  chr_msg(rule([A :: R some C],[(A,B) :: R,B :: C])) |
  (A,B) :: R, B :: C.

/* value restriction
FL_0, FL^-, AL

a . ∀R C
〈a,b〉 . R
──────────
b . C
*/
value_restriction@
  A :: R only C, (A,B) :: R <=>
  chr_msg(rule([A :: R only C,(A,B) :: R],[B :: C])) |
  B :: C.

/* equivalence
TBox

C ≡ D
─────
C ⊑ D
D ⊑ C
*/
equivalence@
  C equiv D <=>
  chr_msg(rule([C equiv D],[C subclass D,D subclass C])) |
  C subclass D,
  D subclass C.

/* subsumption
TBox

a . C
C ⊑ D
─────
a . D

a . ¬C
C ⊑ D
──────
a . ¬D
*/
positive_subsumption@
  A :: C,
  C subclass D <=>
  chr_msg(rule([A :: C,C subclass D],[A :: D])) |
  A :: D.
negative_subsumption@
  A :: not C,
  C subclass D <=>
  chr_msg(rule([A :: not C,C subclass D],[A :: not D])) |
  A :: not D.
