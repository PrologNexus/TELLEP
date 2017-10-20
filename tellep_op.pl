:- module(tellep_op, ['::'/2,equiv/2,subclass/2]).
:- reexport(library(chr)).

/** <module> TELLEP: Operators

Operator definitions.

@author Wouter Beek
@version 2017/10
*/

:- op(952, xfx, user:equiv).
:- op(951, xfy, user:subclass).
:- op(950, xfx, user:(::)).
:- op(940, xfy, user:or).
:- op(930, xfy, user:and).
:- op(670, xfy, user:some).
:- op(660, xfy, user:only).
:- op(650, fy, user:not).

:- chr_constraint
   (::)/2, equiv/2, subclass/2.
