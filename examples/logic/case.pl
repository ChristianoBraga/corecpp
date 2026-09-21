% Core C++ course, UD VII. The case study of Lecture 29 in the logic
% language. The sum of the even numbers from 1 to N is a relation between N
% and S, and the two recursive clauses are the two cases of the filter.
% Expected: S = 30.
soma_pares(0, 0).
soma_pares(N, S) :-
  N > 0, 0 =:= N mod 2,
  M is N - 1, soma_pares(M, T), S is T + N.
soma_pares(N, S) :-
  N > 0, 1 =:= N mod 2,
  M is N - 1, soma_pares(M, S).

?- soma_pares(10, S).
?- soma_pares(4, S).
