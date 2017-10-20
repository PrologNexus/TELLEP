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

% a . ¬C
% a .  C
% ──────
% ⊥
'⊥'@
  A :: not C, A :: C <=>
  chr_msg(rule([A :: not C,A :: C],[concept(fail)])) |
  fail.

% a . C ⊓ D
% ─────────
% a . C
% a . D
'⊓-elimination'@
  A :: C and D <=>
  chr_msg(rule([A :: C and D],[A :: C,A :: D])) |
  A :: C, A :: D.

% a . C ⊔ D
% ──────┬──────
% a . C │ a . D
'⊔-elimination'@
  A :: C or D <=>
  chr_msg(rule([A :: C or D],[A :: C,A :: D])) |
  A :: C ; A :: D.

% a . ∃R C
% ──────────
% 〈a,b〉 . R
% b . C
'∃-elimination'@
  A :: R some C <=>
  chr_msg(rule([A :: R some C],[(A,B) :: R,B :: C])) |
  (A,B) :: R, B :: C.

% a . ∀R C
% 〈a,b〉 . R
% ──────────
% b . C
'∀-elimination'@
  A :: R only C, (A,B) :: R <=>
  chr_msg(rule([A :: R only C,(A,B) :: R],[B :: C])) |
  B :: C.

% C ≡ D
% ─────
% C ⊑ D
% D ⊑ C
'≡-elimination'@
  C equiv D <=>
  chr_msg(rule([C equiv D],[C subclass D,D subclass C])) |
  C subclass D,
  D subclass C.

% a . C
% C ⊑ D
% ─────
% a . D
'T-Box'@
  A :: C,
  C subclass D <=>
  chr_msg(rule([A :: C,C subclass D],[A :: D])) |
  A :: D.

% a . ¬C
% C ⊑ D
% ──────
% a . ¬D
'T-Box'@
  A :: not C,
  C subclass D <=>
  chr_msg(rule([A :: not C,C subclass D],[A :: not D])) |
  A :: not D.

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
