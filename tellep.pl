:- module(
  tellep,
  [
    '::'/2,
    equiv/2,
    subclass/2,
    op(952, xfx, equiv),
    op(951, xfy, subclass),
    op(950, xfx, ::),
    op(940, xfy, or),
    op(930, xfy, and),
    op(670, xfy, some),
    op(660, xfy, only),
    op(650, fy, not)
  ]
).

/** <module> TELLEP: Term rewriting and entailment engine

This module implements the core of the TELLEP engine.

It has constraints for the entailment of ALC, and it has rewriting
rules from ALC to ALC-NNF.

@author Wouter Beek
@version 2017/10
*/

:- use_module(library(chr)).

:- chr_constraint
   (::)/2, equiv/2, subclass/2.

/* bottom concept
FL_0, FL^-, AL

a . ⊥
──────
⊥

a . ¬C
a .  C
──────
⊥
*/
bottom_concept@
  A :: bottom <=>
  chr_msg(rule([A :: bottom],[false])) |
  fail.
contradiction@
  A :: not C, A :: C <=>
  chr_msg(rule([A :: not C,A :: C],[false])) |
  fail.

/* intersection
FL_0, FL^`, AL

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

a . ∃R ⊤
──────────
〈a,b〉 . R
*/
limited_existential_quantification@
  A :: R some top <=>
  chr_msg(rule([A :: R some top],[(A,B) :: R])) |
  (A,B) :: R.

/* existential quantification
???

a . ∃R C
──────────
〈a,b〉 . R
b . C
*/
existential_quantification@
  A :: R some C <=>
  chr_msg(rule([A :: R some C],[(A,B) :: R,B :: C])) |
  (A,B) :: R,
  B :: C.

/* top concept
FL_0, FL^-, AL

a . ⊤
*/
top_concept@
  A :: top <=>
  chr_msg(rule([A :: top],[true])) |
  true.

/* union
U

a . C ⊔ D
──────┬──────
a . C │ a . D
*/
union@
  A :: C or D <=>
  chr_msg(rule([A :: C or D],[A :: C,A :: D])) |
  A :: C ; A :: D.

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



/* TBox */

/* equivalence

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



/* NNF */

% a . ¬¬C
% ───────
% a . C
'¬¬-elimination'@
  A :: not not C <=>
  chr_msg(rule([A :: not not C],[A :: C])) |
  A :: C.

% a . ¬(C ⊓ D)
% ────────────
% a . ¬C ⊔ ¬D
'⊓-DeMorgan'@
  A :: not (C and D) <=>
  chr_msg(rule([A :: not (C and D)],[A :: not C or not D])) |
  A :: not C or not D.

% a . ¬(C ⊔ D)
% ────────────
% a . ¬C ⊓ ¬D
'⊔-DeMorgan'@
  A :: not (C or D) <=>
  chr_msg(rule([A :: not (C or D)],[A :: not C and not D])) |
  A :: not C and not D.

% a . ¬(∃R C)
% ───────────
% a . ∀R ¬C
'∀-NNF'@
  A :: not (R some C) <=>
  chr_msg(rule([A :: not (R some C)],[A :: R only not C])) |
  A :: R only not C.

% a . ¬(∀R C)
% ───────────
% a . ∃R ¬C
'∃-NNF'@
  A :: not (R only C) <=>
  chr_msg(rule([A :: not (R only C)], [A :: R some not C])) |
  A :: R some not C.
