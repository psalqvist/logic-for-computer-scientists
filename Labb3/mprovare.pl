verify(Input) :-
see(Input), read(T), read(L), read(S), read(F), seen,
check(T, L, S, [], F).

check(T, L, S, [], X) :-
	member([S, Holds], L),
	member(X, Holds).

check(T, L, S, [], neg(F)) :-
	\+ check(T, L, S, [], F).

% And
check(T, L, S, [], and(F,G)) :-
	check(T, L, S, [], F),
	check(T, L, S, [], G).

% Or
check(T, L, S, [], or(F,_)) :-
	check(T, L, S, [], F).
check(T, L, S, [], or(_,G)) :-
	check(T, L, S, [], G).

% AX
check(T, L, S, [], ax(F)) :-
	 check_all(T, L, S, [], F).

/*Will check all members of adj, due to backtracking. We just have to find one
adjecent state where F holds.*/

%EX
check(T, L, S, [], ex(F)) :-
	member([S, Adj], T),
	member(MemberOfAdj, Adj),
	check(T, L, MemberOfAdj, [], F).

% AG
check(T, L, S, U, ag(F)) :-
  member(S, U).
check(T, L, S, U, ag(F)) :-
  \+ member(S, U),
  check(T, L, S, [], F),
  check_all(T, L, S, [S|U], ag(F)).



/* Does there exist a path where F globally holds?
1. If S is a member of u
2. If S is not a member osv */

% EG
check(_, _, S, U, eg(_)) :-
  member(S, U).
check(T, L, S, U, eg(F)) :-
  \+ member(S, U),
  check(T, L, S, [], F),
  member([S, Adj], T),
  member(MemberOfAdj, Adj),
  check(T, L, MemberOfAdj, [S|U], eg(F)).


% EF
check(T, L, S, U, ef(F)) :-
  \+ member(S, U),
  check(T, L, S, [], F).
check(T, L, S, U, ef(F)) :-
  \+ member(S, U),
  member([S, Adj], T),
  member(MemberOfAdj, Adj),
  check(T, L, MemberOfAdj, [S|U], ef(F)).

% AF
check(T, L, S, U, af(F)) :-
	\+ member(S, U),
	check(T, L, S, [], F).
check(T, L, S, U, af(F)) :-
	\+ member(S, U),
  check_all(T, L, S, [S|U], af(F)).


% check all
check_all(_, _, _, _, []).

check_all(T, L, S, U, F) :-
  member([S, Next_branch], T),
  check_all(T, L, U, F, Next_branch).

check_all(T, L, U, F, [Head|Tail]) :-
  check(T, L, Head, U, F),
  check_all(T, L, U, F, Tail).
