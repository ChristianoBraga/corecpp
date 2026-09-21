% Logic language example, backtracking. Membership as a relation. The second
% query has three answers, one per element, found by backtracking.
member(X, [X|_]).
member(X, [_|T]) :- member(X, T).

?- member(2, [1, 2, 3]).
?- member(X, [1, 2, 3]).
?- member(4, [1, 2, 3]).
