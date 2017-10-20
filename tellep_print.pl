:- module(tellep_print, [chr_msg/1]).

/** <module> TELLEP: Print statements

This module defines ‘portray’ clauses that allow messages to be
printed in an application-specific way.  Since our application in a DL
reasoner, we want messages to be printed in DL style.

Our DL notation for printing is based on the formulas in Chapter 2 of
the /Description Logic Handbook/ by Baader and Nutt.  We deviate from
this notation in the following two ways:

  1. Because the dot is somewhat sacred in Prolog, we do not print ‘∀R
     . C’ and ‘∃R . D’, but we print ‘∀R C’ and ‘∃R D’ instead.

  2. Because we treat concept and role assertions as the same type of
     constraint (they just have different arity), we do not print them
     as ‘C(a)’ and ‘R(a,b)’ but as ‘a . C’ and ‘(a,b) . R’ (notice our
     use of the same operator ‘.’ in both cases).

@author Wouter Beek
@version 2017/10
*/

:- use_module(library(ansi_term)).
:- use_module(tellep).


%! chr_msg(+Arg:compound) is det.

chr_msg(Arg) :-
  debugging(tellep), !,
  ansi_format([], "~p", [Arg]).
chr_msg(_).


% rule
user:portray(rule(Froms,Tos)) :-
  forall(member(From, Froms), format("~p\n", [From])),
  % TBD: dynamic width of line
  format("────────────────────\n"),
  forall(member(To, Tos), format("~p\n", [To])),
  format("\n").

% clause
user:portray(true) :-
  format("✓").
user:portray(false) :-
  format("❌").
user:portray(A :: C) :-
  format("~p . ~p", [individual(A),concept(C)]).
user:portray(C equiv D) :-
  format("~p ≡ ~p", [concept(C),concept(D)]).
user:portray(C subclass D) :-
  format("~p ⊑ ~p", [concept(C),concept(D)]).

% individual
user:portray(individual(X)) :-
  var(X), !,
  % TBD: pp vars
  format("~p", [X]).
user:portray(individual((A,B))) :-
  format("〈~p,~p〉", [A,B]).
user:portray(individual(A)) :-
  format("~a", [A]).

% concept
user:portray(concept(bottom)) :-
  format("⊥").
user:portray(concept(top)) :-
  format("⊤").
user:portray(concept(not C)) :-
  format("¬~p", [concept(C)]).
user:portray(concept(C and D)) :-
  format("~p ⊓ ~p", [C,D]).
user:portray(concept(C or D)) :-
  format("~p ⊔ ~p", [C,D]).
user:portray(concept(R some C)) :-
  format("∃~p ~p", [concept(R),concept(C)]).
user:portray(concept(R only C)) :-
  format("∀~p ~p", [concept(R),concept(C)]).
user:portray(concept(C)) :-
  format("~a", [C]).
