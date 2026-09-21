% Logic language example, recursion. The factorial as a relation, with the
% built in `is` for the arithmetic. Expected: F = 120.
factorial(0, 1).
factorial(N, F) :-
  N > 0,
  M is N - 1,
  factorial(M, G),
  F is N * G.

?- factorial(5, F).
?- factorial(0, F).
