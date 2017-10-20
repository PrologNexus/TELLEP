:- module(tellep_u, []).
:- reexport(telleop_op).

:- use_module(tellep_print).

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
