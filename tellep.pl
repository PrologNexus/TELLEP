:- module(
  tellep,
  [
    subClassOf/2,
    '::'/2,
    op(950, xfx, ::),
    op(940, xfy, or),
    op(930, xfy, and),
    op(670, xfy, some),
    op(660, xfy, only),
    op(650, fy, not)
  ]
).

/** <module> Tellep

@author Wouter Beek
@version 2017/10
*/

:- use_module(library(chr)).

:- dynamic
    subClassOf/2.

:- chr_constraint
   (::)/2.


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

% a . C
% C ⊑ D
% ─────
% a . D
'T-Box'@
  A :: C <=>
  subClassOf(C,D),
  chr_msg(rule([A :: C,subClassOf(C,D)],[A :: D])) |
  A :: D.

% a . ¬C
% C ⊑ D
% ──────
% a . ¬D
'T-Box'@
  A :: not C <=>
  subClassOf(C,D),
  chr_msg(rule([A :: not C,subClassOf(C,D)],[A :: not D])) |
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
