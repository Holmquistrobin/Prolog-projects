member(X,L) :- select(X,L,_).
memberchk(X,L) :- select(X,L,_), !.

select(X,[X|T],T).
select(X,[Y|T],[Y|R]) :- select(X,T,R).

appendEl(X, [], [X]).
appendEl(X, [H | T], [H | Y]) :-
appendEl(X, T, Y).

/*
T - The transitions in form of adjacency lists
L - The labeling
S - Current state
U - Currently recorded states
F - CTL Formula to check.
*/
verify(Input) :- see(Input), read(T), read(L), read(S), read(F), seen,
  check(T, L, S, [], F).

/*And*/
check(_,L,S,_, and(F,G)):- member([S,Labels_S],L),member(F,Labels_S), member(G,Labels_S).
check(T,L,S,U, and(F,G)):- check(T,L,S,U,F),member([S,Labels_S],L),member(G,Labels_S).
check(T,L,S,U, and(F,G)):- check(T,L,S,U,G),member([S,Labels_S],L),member(F,Labels_S).
check(T,L,S,U, and(F,G)):- check(T,L,S,U,F), check(T,L,S,U,G).
/*Or*/
check(_,L,S,_, or(F,G)):- member([S,Labels_S],L),member(F,Labels_S),!; member([S,Labels_S],L), member(G,Labels_S),!.
check(T,L,S,U, or(F,G)):- check(T,L,S,U,F),!;member([S,Labels_S],L),member(G,Labels_S),!.
check(T,L,S,U, or(F,G)):- check(T,L,S,U,G),!;member([S,Labels_S],L),member(F,Labels_S),!.
/*AX*/
check(T,L,S,U, ax(X)):- member([S,Adjacent], T),!, check_ax(T,L,Adjacent,U,X).
/*EX*/
check(T,L,S,U, ex(X)):- member([S,Adjacent], T),!, check_ex(T,L,Adjacent,U,X).
/*AG*/
check(T,L,S,U, ag(X)):- \+ member(S,U),check(T,L,S,U,X),!, appendEl(S,U,U_new),
  member([S,Adjacent], T), check_ag(T,L,Adjacent,U_new, X).
check(T,L,S,U, ag(X)):- \+ member(S,U),!, appendEl(S,U,U_new), member([S,Adjacent], T),
  member([S,Labels_S], L),member(X, Labels_S), check_ag(T,L,Adjacent,U_new,X).
check(_,_,S,U, ag(_)):-member(S,U).
/*EG*/
check(T,L,S,U, eg(X)):- \+ member(S,U),check(T,L,S,U,X), appendEl(S,U,U_new),
  member([S,Adjacent], T), check_eg(T,L,Adjacent,U_new,X).
check(_,_,S,U, eg(_)):-member(S,U).
/*EF*/
check(T,L,S,U, ef(X)):- check(T,L,S,U,X),!.
check(T,L,S,U, ef(X)):- !, member([Node,_],L), check(T,L,Node,U,X),
  track_node(T,S,Node,[]).
/*AF*/
check(T,L,S,_, af(X)):- check(T,L,S,[],X),!.
check(T,L,S,U, af(X)):- \+ member(S,U), member([S,Adjacent],T), member(S, Adjacent),!,
  check(T,L,S,[],X), appendEl(S,U,U_new), check_af(T,L,Adjacent,U_new, X).
check(T,L,S,U, af(X)):- \+ member(S,U), appendEl(S,U,U_new), member([S,Adjacent], T),
  check_af(T,L,Adjacent,U_new, X).
/*Labels*/
check(_,L,S,_,neg(X)):- member([S,Labels_S],L), \+ member(X, Labels_S).
check(_,L,S,_,X):- member([S,Labels_S], L),member(X, Labels_S).

/*
Handle EF.
*/
track_node(T,S,Node,Previous_nodes):- \+ member(S,Previous_nodes),
  member([S,Adjacent],T), member(Node,Adjacent).
track_node(T,S,Node,Previous_nodes):- \+ member(S,Previous_nodes),
  appendEl(S,Previous_nodes,New_previous),
  member([S,Adjacent],T),!, member(Next_node, Adjacent),
  track_node(T,Next_node,Node,New_previous).
/*Loop through adjacency list and check*/
check_ag(_,_,[],_,_):-!.
check_ag(T,L,[Head|Tail],U, X):- check(T,L,Head,U,ag(X)), check_ag(T,L,Tail,U,X).

check_eg(_,_,[],_,_):-!,fail.
check_eg(T,L,[Head|Tail],U, X):- check(T,L,Head,U,eg(X)),!;check_eg(T,L,Tail,U,X).

check_af(_,_,[],_,_):-!.
check_af(T,L,[Head|Tail],U,X):- check(T,L,Head,U,af(X)),check_af(T,L,Tail,U,X).

check_ax(_,_,[],_,_):-!.
check_ax(T,L,[Head|Tail],U,neg(X)):- !, member([Head, Labels_S],L),\+ member(X,Labels_S),
  check_ax(T,L,Tail,U,neg(X)).
check_ax(T,L,[Head|Tail],U,X):- member([Head, Labels_S],L), member(X,Labels_S),
  check_ax(T,L,Tail,U,X).
check_ax(T,L,[Head|Tail],U,X):- check(T,L,Head,U,X), check_ax(T,L,Tail,U,X).

check_ex(_,_,[],_,_):- !,fail.
check_ex(T,L,[Head|Tail], U, X):- check(T,L,Head,U,X); check_ex(T,L,Tail,U,X).
