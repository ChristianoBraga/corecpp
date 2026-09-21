% Core C++ course, Unit VII. Concatenation of lists as a relation.
% The same clauses answer three questions, which is the point of the
% paradigm. Expected: three answers to the third query.
append([], L, L).
append([H|T], L, [H|R]) :- append(T, L, R).

?- append([1, 2], [3, 4], R).
?- append(X, [3, 4], [1, 2, 3, 4]).
?- append(X, Y, [1, 2]).
