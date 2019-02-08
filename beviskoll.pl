
/*Extract element E from the list L, where E is element nr N in L.*/
nth(N,L,E) :- nth(1,N,L,E).
nth(N,N,[H|_],H).
nth(K,N,[_|T],H) :- K1 is K+1, nth(K1,N,T,H).

findlast([E],[],E).
findlast([H1|T1], [H2|T2], E) :-
H2=H1,findlast(T1,T2,E).

/*Verify proof contained in InputFileName*/
verify(InputFileName) :- see(InputFileName),
  read(Prems), read(Goal), read(Proof),
  seen,assert(box_position(0)), findlast(Proof,_,Last_proof_line), nth(1,Last_proof_line, Endline),
  assert(end_line(Endline)), valid_proof(Prems, Goal, Proof).

clean():-retract(prem(_,_)), clean()
        ;retract(box(_,_,_,_)), clean()
        ;retract(box_position(_)),clean()
        ;retract(end_line(_)),clean()
        ;true.

/*Part of handling incorrect proofs*/
assump(0,0,0).

/*Use box_counter to determine where to start validating lines again after being in a box_counter
(i.e. Don't try to validate lines inside the box here).*/
valid_proof(Prems,Goal,[Hpro|Tpro]):- valid_line(Hpro,Prems,Updated_prems),
  valid_proof(Updated_prems,Goal,Tpro).
valid_proof(_,Goal,[]):- end_line(Line),prem(Line,Goal), \+assump(_,Goal,_),!, clean().
valid_proof(_,_,_):- clean(),!,fail.

/*Check if a line is valid depending on what rule is stated.*/
/*premise*/
valid_line(Proof,Prems,Updated_prems):-nth(3,Proof,premise),!,nth(1,Proof,Line),
  nth(2,Proof,New_prem),select(New_prem,Prems,Updated_prems), assert(prem(Line,New_prem)),!.
/*copy*/
valid_line(Proof,_,_):-nth(3,Proof,copy(X)),!,nth(1,Proof,Line),nth(2,Proof,New_prem),
  prem(X,New_prem), assert(prem(Line,New_prem)),!.
/*andel1/andel2*/
valid_line(Proof,_,_):-nth(3,Proof,andel1(L)),!,nth(1,Proof,Line),nth(2,Proof,X),
  prem(L,and(X,_)), assert(prem(Line,X)).
valid_line(Proof,_,_):-nth(3,Proof,andel2(L)),!,nth(1,Proof,Line),nth(2,Proof,X),
  prem(L,and(_,X)), assert(prem(Line,X)).
/*LEM*/
valid_line(Proof,_,_):-nth(3,Proof,lem),!,nth(1,Proof,Line),nth(2,Proof,or(X,neg(X))),
  assert(prem(Line,or(X,neg(X)))).
/*impel*/
valid_line(Proof,_,_):-nth(3,Proof,impel(L1,L2)),!,nth(1,Proof,Line),nth(2,Proof,Y),
   prem(L1,X),prem(L2,imp(X,Y)),assert(prem(Line,Y)).
/*negel*/
valid_line(Proof,_,_):-nth(3,Proof,negel(L1,L2)), prem(L1,X),prem(L2,neg(X)), nth(1,Proof,Line),
  assert(prem(Line,cont)).
valid_line(Proof,_,_):-nth(3,Proof,negel(L1,L2)),!, prem(L1,neg(X)),prem(L2,X), nth(1,Proof,Line),
  assert(prem(Line,cont)).
/*negint*/
valid_line(Proof,_,_):-nth(3,Proof,negint(L1,L2)),!, nth(2, Proof,neg(X)),box_position(N), N1 is N+1, box(L1,X,L2,cont,N1),
  nth(1,Proof,Line), assert(prem(Line,neg(X))).
/*negnegel*/
valid_line(Proof,_,_):-nth(3,Proof,negnegel(L)),!, nth(1, Proof, Line), nth(2, Proof, X), prem(L,neg(neg(X))),
  assert(prem(Line,X)).
/*orel*/
valid_line(Proof,_,_):-nth(3,Proof,orel(Lor,L1stat1,L2stat1,L1stat2,L2stat2)),!, box_position(N),prem(Lor, or(X,Y)),
 box(L1stat1,X,L2stat1,C,N1),box(L1stat2,Y,L2stat2,C,N1),N1 is N+1, nth(2,Proof,C), nth(1,Proof,Line), assert(prem(Line,C)).
/*contel*/
valid_line(Proof,_,_):-nth(3,Proof,contel(L)),!,nth(2,Proof,New_prem),nth(1,Proof,Line), prem(L,cont),
  assert(prem(Line,New_prem)).
/*assumption*/
valid_line(Proof,_,_):-nth(3,Proof,assumption),!,\+box_position(0), nth(1,Proof,Line), nth(2,Proof,Assumption),
  assert(prem(Line,Assumption)),box_position(N), assert(assump(Line,Assumption,N)).
/*andint*/
valid_line(Proof,_,_):-nth(3,Proof,andint(L1,L2)),!, nth(1,Proof,Line),nth(2,Proof,and(X,Y)),
  prem(L1,X),prem(L2,Y),assert(prem(Line,and(X,Y))).
/*orint1/orint2*/
valid_line(Proof,_,_):-nth(3,Proof,orint1(L)),!, nth(1,Proof,Line),nth(2,Proof, or(X,Y)),
  prem(L,X), assert(prem(Line,or(X,Y))).
valid_line(Proof,_,_):-nth(3,Proof,orint2(L)),!, nth(1,Proof,Line),nth(2,Proof, or(X,Y)),
  prem(L,Y),assert(prem(Line, or(X,Y))).
/*impint*/
valid_line(Proof,_,_):-nth(3,Proof,impint(L1,L2)),!, box_position(N), nth(2,Proof,imp(X,Y)), nth(1,Proof,Line),box(L1,X,L2,Y,N1),N1 is N+1,assert(prem(Line,imp(X,Y))).
/*negnegint*/
valid_line(Proof,_,_):-nth(3,Proof,negnegint(L)),!, nth(2,Proof,neg(neg(X))), nth(1,Proof, Line), prem(L,X), assert(prem(Line,neg(neg(X)))).
/*MT*/
valid_line(Proof,_,_):-nth(3,Proof,mt(L1,L2)),!,nth(2,Proof,neg(X)), nth(1,Proof,Line), prem(L1,imp(X,Y)), prem(L2,neg(Y)), assert(prem(Line,neg(X))).
/*PBC*/
valid_line(Proof,_,_):-nth(3,Proof,pbc(L1,L2)),!, box_position(N), N1 is N+1, nth(2,Proof,X), nth(1, Proof, Line), box(L1,neg(X),L2,cont,N1), assert(prem(Line,X)).
/*box*/
valid_line(Proof,_,_):-box_position(N),!, N1 is N+1, retract(box_position(N)),assert(box_position(N1)),validbox(Proof), assump(Line,Assumption, N1),
  endbox(L2,Y,N1), retract(assump(Line,Assumption, N1)), retract(endbox(L2,Y,N1)), assert(box(Line,Assumption,L2,Y,N1)), retract(box_position(N1)),
  assert(box_position(N)).

/*Verify box*/
validbox([H]):-valid_line(H,_,_),!, nth(1,H,Line), nth(2,H,New_prem),
  clean_box(H), box_position(N), assert(endbox(Line,New_prem,N)).
validbox([H|T]):-valid_line(H,_,_),!,validbox(T), clean_box(H).

clean_box(Input):-nth(1,Input,[_|_]),!.
clean_box(Input):-nth(1,Input,Line), nth(2,Input,New_prem), retract(prem(Line,New_prem)).
