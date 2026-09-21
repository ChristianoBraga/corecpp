% Core C++ course, UD VII. The case study of Lecture 29 in the logic
% language. The sum of the even numbers from 1 to N is a relation between N
% and S, and the two recursive clauses are the two cases of the filter.
% Expected: S = 30.
sum_even(0, 0).
sum_even(N, S) :-
  N > 0, 0 =:= N mod 2,
  M is N - 1, sum_even(M, T), S is T + N.
sum_even(N, S) :-
  N > 0, 1 =:= N mod 2,
  M is N - 1, sum_even(M, S).

?- sum_even(10, S).
?- sum_even(4, S).
