% For SICStus, uncomment line below: (needed for member/2)
%:- use_module(library(lists)).
% Load model, initial state and formula from file.
verify(Input) :-
see(Input), read(T), read(L), read(S), read(F), seen,
check(T, L, S, [], F).
% check(T, L, S, U, F)
% T - The transitions in form of adjacency lists
% L - The labeling
% S - Current state
% U - Currently recorded states
% F - CTL Formula to check.
%
% Should evaluate to true iff the sequent below is valid.
%
% (T,L), S |- F
% U
% To execute: consult('your_file.pl'). verify('input.txt').
% Literals
check(_, L, S, [], F) :-
	member([S, Holds], L),
	member(F, Holds).

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
	member([S,N],T),
	check_all(T, L, N, [], F).

% Will check all members of adj, due to backtracking. We just have to find one
% adjecent state where F holds.
% EX
check(T, L, S, [], ex(F)) :-
	member([S, Adj], T),
	member(MemberOfAdj, Adj),
	check(T, L, MemberOfAdj, [], F).

% AG
check(T, L, S, U, ag(F)) :-
  member(S, U).
check(T, L, S, U, ag(F)) :-
  \+member(S, U),
	member([S,N],T),
  check(T, L, S, [], F),
  check_all(T, L, N, [S|U], ag(F)).



%Does there exist a path where F globally holds?
%1. If S is a member of u
%2. If S is not a member osv

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
	member([S, N], T),
  check_all(T, L, N, [S|U], af(F)).

% check all
%check_all(_, _, _, _, []).

check_all(T, L, [S|N], U, F) :-
	check(T, L, S, U, F),!,
	check_all(T, L, N, U, F).
check_all(_, _, [], _, _).
