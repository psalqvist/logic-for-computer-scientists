/*
# Uppgift 1
# T=f(a,Y,Z), T=f(X,X,b). give us the bindings:
# T = f(a,a,b)
# X = a
# Y = a
# Z = b
# We want to unify f(a,Y,Z) = f(X, X, b)
# The complex terms have the same functor, so that is ok.
# Then we want to unify a = X, which succeeds and we get X = a.
# After this, we want to unify Y = X, Y and X are variables which means they will share value,
# so we get Y = X = a
# And finally we want to unify Z = b, Z is a variable and b is a constant so
# the unification works and we get the result Z = b.
*/


/*
Uppgift 2
fail starts backtracking, and cut stops the backtracking. So if fish(X) is true,
we reach cut, which blocks us from the second line. Then fail starts backtracking,
but the cut blocks it, so the program fails. If fish(X) is false, then we move to
the second line.
*/

likes(philip, X) :- fish(X), !, fail.
likes(philip, X) :- food(X).

food(X) :- pizza(X).
food(X) :- hamburger(X).
fish(X) :- sushi(X).

pizza(a).
hamburger(b).
sushi(c).




% Uppgift 3

%adds empty list as argument, to store the new list
remove_duplicates(List, E) :-
  remove_duplicates_2(List, [], E).

%basecase to unify the new list with E when the tail is empty
remove_duplicates_2([], Temp, Temp).

 %if the head is not a member of Temp, then do recursive call without adding anything to the new list
remove_duplicates_2([H|T], Temp, E) :-
  member(H, Temp),
  remove_duplicates_2(T, Temp, E).

%we know that H is not a member of Temp, so add it to New_temp
remove_duplicates_2([H|T], Temp, E) :-
  \+member(H, Temp),
  append(Temp, [H], New_temp),
  remove_duplicates_2(T, New_temp, E).
