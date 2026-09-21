% Core C++ course, Unit VII. Membership as a relation, over the
% concatenation of the previous example. Expected: three answers to the
% second query, one per element.
member(X, [X|_]).
member(X, [_|T]) :- member(X, T).

?- member(2, [1, 2, 3]).
?- member(X, [1, 2, 3]).
?- member(4, [1, 2, 3]).
