:- module(tellep_nnf, []).
:- reexport(tellep_op).

/** <module> TELLEP: NNF

Rewrite rules from any ALC formulate to its NNF.

@author Wouter Beek
@version 2017/10
*/

:- use_module(tellep_print).

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
