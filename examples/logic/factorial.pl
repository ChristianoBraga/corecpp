% Core C++ course, Unit VII. The factorial of Lecture 1, now as a relation,
% with the built in `is` for the arithmetic. Expected: F = 120.
fatorial(0, 1).
fatorial(N, F) :-
  N > 0,
  M is N - 1,
  fatorial(M, G),
  F is N * G.

?- fatorial(5, F).
?- fatorial(0, F).
