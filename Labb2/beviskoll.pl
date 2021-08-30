verify(InputFileName) :-
	see(InputFileName),
	read(Prems), read(Goal), read(Proof),
	seen,
	proof_check(Prems, Goal, Proof).

proof_check(Prems, Goal, Proof) :-
  proof_check(Prems, Goal, Proof, []).

%basecase of recursion where Proof_t = [] and Goal can unify with Goal.
%If Goal and Goal have different values, they won´t unify and algorithm will answer no.

proof_check(Prems, Goal, [], [[_, Goal, _]|Valid_list]).

%If the rule (Proof_h) is valid, we run proof_check recursively,
%with Proof_t as the list with remaining proofs to check and adding
%Proof_h to the beginning of Valid_list

proof_check(Prems, Goal, [Proof_h|Proof_t], Valid_list) :-
	rule(Prems, Proof_h, Valid_list),
	proof_check(Prems, Goal, Proof_t, [Proof_h|Valid_list]).

%boxes
%If the row doesn´t match any of our rules, the other option is that
%the row is an assumption and we have opened a box.

proof_check(Prems, Goal, [[[Row_nr, A, assumption]|Box_t]|Proof_t], Valid_list) :-

%run check_box while adding the assumption to the valid_list

	check_box(Prems, Goal, Box_t, [[Row_nr, A, assumption]|Valid_list]),
	proof_check(Prems, Goal, Proof_t, [[[Row_nr, A, assumption]|Box_t]|Valid_list]).

%base case for a box

check_box(Prems, Goal, [], Valid_list).

check_box(Prems, Goal, [[[Row_nr, A, assumption]|Box_t]|Proof_t], Valid_list) :-
	check_box(Prems, Goal, Box_t, [[Row_nr, A, assumption]|Valid_list]),
	check_box(Prems, Goal, Proof_t, [[[Row_nr, A, assumption]|Box_t]|Valid_list]).

%checking rules inside a box

check_box(Prems, Goal, [Proof_h|Proof_t], Valid_list) :-
	rule(Prems, Proof_h, Valid_list),
	check_box(Prems, Goal, Proof_t, [Proof_h|Valid_list]).

%checking if a row belongs to the previously added element in Valid_list.
%If it does, we will return that row.
%cut in end of statement to prevent backtracking loop.

get_row(Row_nr, [Box_h|Remaining_valid], [Row_nr, A, Rule]) :-
	member([Row_nr, A, Rule], Box_h),
  !.

get_row(Row_nr, [Box_h|Remaining_valid], [Row_nr, A, Rule]) :-
  get_row(Row_nr, Ramaining_valid, [Row_nr, A, Rule]).

%get_box(Row_nr, [Box_h|Remaining_valid], Box_h) :-
  %member([Row_nr, _, _], Box_h).

%get_box(Row_nr, [Box_h|Remaining_valid], Box) :-
  %get_box(Row_nr, Remaining_valid, Box).

get_box(Row_nr, Valid_list, [[Row_nr, A, assumption]|Box_t]) :-
  member([[Row_nr, A, assumption]|Box_t], Valid_list).



%rules

rule(Prems, [Row_nr, A, premise], Valid_list) :-
	member(A, Prems).

rule(Prems, [Row_nr, A, impel(X,Y)], Valid_list) :-
	member([X, Premise, _], Valid_list),
	member([Y, imp(Premise, A), _], Valid_list).

rule(Prems, [Row_nr, A, copy(X)], Valid_list) :-
  member([X, A, _], Valid_list).

rule(Prems, [Row_nr, A, andel1(X)], Valid_list) :-
  member([X, and(A,_), _], Valid_list).

rule(Prems, [Row_nr, B, andel2(X)], Valid_list) :-
  member([X, and(_,B), _], Valid_list).

rule(Prems, [Row_nr, or(A,_), orint1(X)], Valid_list) :-
  member([X, A, _], Valid_list).

rule(Prems, [Row_nr, or(_,B), orint2(X)], Valid_list) :-
  member([X, B, _], Valid_list).

rule(Prems, [Row_nr, B, impel(X, Y)], Valid_list) :-
  member([X, A, _], Valid_list),
  member([Y, imp(A, B), _], Valid_list).

rule(Prems, [Row_nr, cont, negel(X, Y)], Valid_list) :-
  member([X, A, _], Valid_list),
  member([Y, neg(A), _], Valid_list).

rule(Prems, [Row_nr, A, contel(X)], Valid_list) :-
  member([X, cont, _], Valid_list).

rule(Prems, [Row_nr, neg(neg(A)), negnegint(X)], Valid_list) :-
  member([X, A, _], Valid_list).

rule(Prems, [Row_nr, A, negnegel(X)], Valid_list) :-
  member([X, neg(neg(A)), _], Valid_list).

rule(Prems, [Row_nr, neg(A), mt(X, Y)], Valid_list) :-
  member([X, imp(A, B), _], Valid_list),
  member([Y, neg(B), _], Valid_list).


rule(Prems, [Row_nr, imp(A, B), impint(X, Y)], Valid_list) :-
  get_box(X, Valid_list, Box),
  get_row(X, Box, First_row),
  get_row(Y, Box, Last_row),
  [X, A, assumption] = First_row,
  [Y, B, _] = Last_row.


rule(Prems, [Row_nr, or(A, neg(A)), lem], Valid_list).

rule(Prems, [Row_nr, and(A, B), andint(X, Y)], Valid_list) :-
  member([X, A, _], Valid_list),
  member([Y, B, _], Valid_list).

rule(Prems, [Row_nr, neg(A), negint(X,Y)], Valid_list) :-
	get_row(X, Valid_list, First_row),
  get_row(Y, Valid_list, Last_row),
	[X, A, assumption] = First_row,
	[Y, cont, _] = Last_row.

rule(Prems, [Row_nr, A, orel(X,Y,Z,U,V)], Valid_list) :-
  get_box(Y, Valid_list, Box_1),
  get_row(Y, Box_1, First_row_1),
  get_row(Z, Box_1, Last_row_1),
  get_box(U, Valid_list, Box_2),
  get_row(U, Box_2, First_row_2),
  get_row(V, Box_2, Last_row_2),
	member([X, or(_Y, _U), _], Valid_list),
  [Y, _Y, assumption] = First_row_1,
  [U, _U, assumption] = First_row_2,
  [Z, A, _] = Last_row_1,
  [V, A, _] = Last_row_2.

rule(Prems, [Row_nr, A, pbc(X,Y)], Valid_list) :-
  	get_box(X, Valid_list, Box),
  	member([X, neg(A), assumption], Box),
  	member([Y, cont, _], Box).
