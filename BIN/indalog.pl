


%%%% INDALOG 
%%%% Jesœs Manuel Almendros-JimŽnez 
%%%% Fco. Javier Enciso Ba–os
%%%% University of Almer’a 
%%%% Spain
%%%% Contact jalmen@ual.es
%%%% October 2006



%%%%%%%%%%%
% INDALOG
%%%%%%%%%%  

 

 
 
 
 
 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
% LOAD, LOAD2 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 
dynamic_pred:-
      dynamic (:=)/2,
      (=:)/2, 
      (=>)/2, 
      (<=)/2,        
      (==:)/2,
      (==>)/2, 
      sol/1, 
      value/2, 
      valuem/2, 
      reached/2, 
      ok/0, 
      ok2/0, 
      funct/1,
      safe_variable/2,
      intfun/2,
      (database)/1,
      (key)/1,
      data/2,
      dataaux/2,
      keyaux/2. 

      
 
load:- 
      op(1125,xfy,[:=]), 
      op(1128,xfy,[=:]), 
      op(1130,xfy,[=>]), 
      op(1132,xfy,[<=]),
      op(1133,xfy,[==>]), 
      op(875,xfy,[><]), 
      op(1140,xfy,[==:]),
	 op(1060,xfy,[::]),
      op(1103,xfy,[::=]),       
      op(801,fx,[database]),      
	 op(914,fx,[datatype]),
      op(913,fx,[type]), 
      op(851,fx,[key]),
      op(824,fx,[select]),
      op(814,xfy,[from]),
      op(811,xfy,[as]), 
      op(804,xfy,[where]),
	 op(738,xfy,[div]),
      op(729,xfy,[++]),
      op(721,xfy,[&&]),
      op(720,xfy,[#]),
      op(955,fx,[ld]),
      op(956,fx,[cp]),
      op(957,fx,[evq]),
      op(958,fx,[evs]).
      

        


:-load.  


 
%%%%%%%%%%%%%%%%%%%%%%
% COMMANDS
%%%%%%%%%%%%%%%%%%%%%% 
%%%%%%%%%%%%%%%%%%%%%
% LD, EVQ, EVS
%%%%%%%%%%%%%%%%%%%%%

ld Name :- loadf(Name).
evq Goal :- check_goal(Goal),!,call_goal(Goal).
evq _:- wrong_goal,fail.
evs Select:- call(Select).


  


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% LOAD FILE
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


loadf(Name):-  
			 abolish((:=)/2),
			 abolish((::=)/2),
             abolish((::)/2),
             abolish((database)/1),
			 abolish((key)/1),	 
			 dynamic_pred,              
             clean,
             style_check(-discontiguous),   
             consult(Name),
			 flatting,
			 generate_data,
			 generate_intfun,
			 backup.

%%%%%%%%%%%%%%%%%%%%%%%%%
% CLEAN
%%%%%%%%%%%%%%%%%%%%%%%%
 
clean:-retract(_==:_:-_),fail.
clean:-retract(_==>_:-_),fail.
clean:-retract(data(_,_)),fail.
clean:-retract(intfun(_,_)),fail.
clean.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% FLATTING
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%



flatting:-clause(X | C := R, true), R \= (_:=_), assert(X ==> R :- C),fail.
flatting:-clause(X | C := R, true), R = (_:=_), flatting_boolean(X,(C:=R)), fail.
flatting:-clause(X:=Y,true),nonvar(Y),Y=case(Z),flatting_case(X,Z),fail. flatting. 



flatting_boolean(X, A:=B ):-B=((C|E):=F),!,assert(X ==> C :- A),flatting_boolean(X,(E:=F)).
flatting_boolean(X, A:=B ):-assert(X ==> B :- A).


flatting_case(X,Z):- Z=..[_,R1,_],flattening(X,R1),fail. flatting_case(X,Z):- Z=..[_,_,REST],flattening(X,REST),fail. flatting_case(_,_).  flattening(X,P=Q-->T):-nonvar(T),T=case(U),!,P=Q,flatting_case(X,U). flattening(X,P=Q-->T):-nonvar(T),T=..[_,C,R],!,P=Q,assert(X==>R:-C). flattening(X,P=Q-->T):-P=Q,assert(X==>T:-true). 

 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% GENERATE DATA
%%%%%%%%%%%%%%%%%%%%%%%%%%%

generate_data:-(datatype _::=C), 
			C=..['|'|V], 
			generate_op_data(['|'|V]),
			fail.
generate_data:-(datatype _::=C), 
			functor(C,D,N), 
			D\=='|', 
			
			assert(data(D,N)),
			fail.
generate_data.

generate_op_data([_,V1,V2]):-functor(V1,D1,N1), 
					
					assert(data(D1,N1)),
					(V2=..['|'|V]->generate_op_data(['|'|V]);
					functor(V2,D2,N2),  assert(data(D2,N2))).


%%%%%%%%%%%%%%%%%%%%%%%%%%%
% GENERATE INTFUN
%%%%%%%%%%%%%%%%%%%%%%%%%%


generate_intfun:- (A::T),
				\+field(A,_),
                   nonvar(T),
				T=..['->'|RT],
				generate_op_fun(A,['->'|RT],1),
				fail.

generate_intfun:- (A::T),
				\+field(A,_), 
                   nonvar(T),                  
				functor(T,D,_),
				D\=='->',
				
				assert(intfun(A,0)),
				fail.

generate_intfun:- (A::T),
				\+field(A,_),
                   var(T),                   
				
				assert(intfun(A,0)),
				fail.

generate_intfun.

generate_op_fun(A,[_,_,V2],N):-
		(nonvar(V2),V2=..['->'|V] -> M is N+1,
		generate_op_fun(A,['->'|V],M);
		assert(intfun(A,N))).

%%%%%%%%%%%%%%%%%%%%%%%%%%%
% BACKUP
%%%%%%%%%%%%%%%%%%%%%%%%%%

backup:- 
    clause(X:=Y,Z),  
    \+rule?(X==:Y,Z), 
    assert(X==:Y:-Z), 
    fail.
backup:- 
    clause(X==>Y,Z), 
    \+rule?(X==:Y,Z), 
    assert(X==:Y:-Z), 
    fail.

backup:-clause(X | C ==: R,true),
        retract(X | C ==: R :-true),
        fail.
 
backup.



%%%%%%%%%%%%%%%%%%%%%%%%
% CHECK GOAL
%%%%%%%%%%%%%%%%%%%%%%%%%

check_goal(_):-getfunctions,fail.
check_goal(_):-get_safe,fail. 
check_goal(_):-copy,fail.
check_goal(true):-!.
check_goal(E1><E2):-check_expr(E1),check_expr(E2),!.
check_goal((EQ,REQ)):-check_goal(EQ),check_goal(REQ),!.

%%%%%%%%%%%%%%%%%%%%%%%
% CHECK EXPR
%%%%%%%%%%%%%%%%%%%%%%%

check_expr(X):-var(X),!.
check_expr(C):-constant(C),data(C,0),!.
check_expr(C):-constantfun(C),intfun(C,0),!.
check_expr(C):-constantfun(C),field(C,_),\+is_key(C),!.
check_expr(CON):-compound(CON),constructor(CON),CON=..[C|Args],data(C,Arity),check_args(Args,0,Arity),!.
check_expr(FUN):-compound(FUN),function(FUN),FUN=..[F|Args],database D, D=..[F|_],key E,E=..[F|LKEYS],length(LKEYS,Arity),check_args(Args,0,Arity),!.
check_expr(FUN):-compound(FUN),function(FUN),FUN=..[F|Args],field(F,Arity),\+is_key(F),check_args(Args,0,Arity),!.
check_expr(FUN):-compound(FUN),function(FUN),FUN=..[F|Args],intfun(F,Arity),check_args(Args,0,Arity),!.

check_args([],Arity,Arity):-!.
check_args([Arg|RArg],N,Arity):-M is N+1,check_expr(Arg),check_args(RArg,M,Arity),!.

%%%%%%%%%%%%%%%%%%%%%%%%%
% WRONG GOAL
%%%%%%%%%%%%%%%%%%%%%%%%

wrong_goal:-write('WARNING: Wrong goal').


%%%%%%%%%%%%%%%%%%%%%%%%%%%
% FIELD
%%%%%%%%%%%%%%%%%%%%%%%%%%


field(A,Arity):-database D, D=..[A|_],key E,E=..[A|LKEYS],length(LKEYS,Arity),!.

field(A,Arity):-database D,
		D=..[R|LFIELDS],
		member(A,LFIELDS),
		key E, E=..[R|LKEYS],
        length(LKEYS,Arity),!.

%%%%%%%%%%%%%%%%%%%%%%%%%
% IS KEY
%%%%%%%%%%%%%%%%%%%%%%%%


is_key(A):-key D,
		D=..[_|LKEYS],
        member(A,LKEYS),!.







 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% CALL GOAL
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 
call_goal(G):-prepare_goal,goal(G).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
% PREPARE GOAL 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 

  
prepare_goal:-retract(_:=_:-_),fail.  
prepare_goal:-retract(_=:_:-_),fail. 
prepare_goal:-retract(_<=_:-_),fail. 
prepare_goal:-retract(_=>_:-_),fail. 
prepare_goal:-retract(value(_,_)),fail. 
prepare_goal:-retract(valuem(_,_)),fail. 
prepare_goal:-retract(sol(_)),fail. 
prepare_goal:-retract(reached(_,_)),fail.
prepare_goal:-retract(safe_variable(_,_)),fail. 
prepare_goal:-retract(ok),fail. 
prepare_goal:-retract(ok2),fail. 
prepare_goal:-retract(funct(_)),fail.
prepare_goal:-clause(X==:Y,Z),
			\+rule?(X:=Y,Z),
			assert(X:=Y:-Z),
			fail. 
prepare_goal.


 


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
% GOAL 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
 
goal(_):-getfunctions,fail.

goal(_):-get_safe,fail. 
 
goal(_):-copy,fail.

goal(G):- 
    passing((G),[],true), 
    recover_magic,
    fail. 
 
goal(G):-asserta(ok2),bottom_up(G).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
% COPY 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
 
copy:- 
    clause(X:=Y,Z), 
    \+rule?(X=:Y,Z), 
    assert(X=:Y:-Z), 
    fail.
 
copy:-clause(X | C =: R,true),
        retract(X | C =: R:-true),
        fail.
 
copy:-retract(_:=_:-_),fail. 
 
copy:-!.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
% GETFUNCTIONS 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
 
getfunctions:-clause(H:=_,_), 
       H=..[F|_],
       \+funct(F), 
       assert(funct(F)), 
       fail. 
 
getfunctions:-!.

get_safe:-clause(H:=R,C), 
       H=..[F|Args],
       position(Args,I,ArgI),
       (var(ArgI),safe(ArgI,R,C)->
       assert(safe_variable(F,I));
       true), 
       fail. 
 
get_safe:-!.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
% BOTTOM-UP 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
 
bottom_up(G):-bottom_main(G). 
 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
% BOTTOM_MAIN 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
 
 
bottom_main(G):-call(G),\+exists_solution(G),asserta(sol(G)). 
bottom_main(_):-ok2,retractall(ok2),bottom_up_main,fail.
bottom_main(G):-ok2,bottom_main(G). 


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
% JOINABILITY 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 

 
X><Y:-value_of_goal(X,U),value_of_goal(Y,V),U=V. 
  
 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
% VALUE_OF_GOAL 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 

 
 
value_of_goal(X,Y):-var(X),!,Y=X. 
 
value_of_goal(C,Y):-constant(C),!,Y=C.

value_of_goal(E,X):-constantfun(E),
    E=..[F|_], 
    atom_concat(mg_,_,F),!,
    valuem(E2,X),
    unify2(E2,E). 

value_of_goal(E,X):-constantfun(E),!, 
    value(E2,X),
    unify2(E2,E). 
     
 
value_of_goal(E,X):- 
    compound(E), 
    constructor(E),!, 
    E=..[C|ArgsC], 
    values_of_goal(ArgsC,Xs), 
    X=..[C|Xs].
 
value_of_goal(E,X):- 
    compound(E), 
    function(E), 
    E=..[F|_], 
    atom_concat(mg_,_,F),!, 
    valuem(E2,X),
    unify2(E2,E).     
      
value_of_goal(E,X):- 
    compound(E), 
    function(E),!, 
    value(E2,X),
    unify2(E2,E).      
     
       
 
 
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
% VALUES_OF_GOAL 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
 
 
values_of_goal([],[]):-!. 
values_of_goal([E|LE],[X|LX]):- 
          value_of_goal(E,X), 
          values_of_goal(LE,LX). 


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
% BOTTOM UP MAIN 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 

  
bottom_up_main:- 
    apply_rule(X:=Y,Z),  
    call(Z), 
    (var(Y)->  
    retractrules(X:=Y,Z), 
    \+exists_value(X,Y),  
    X=..[F|_],  
    (atom_concat(mg_,_,F)-> 
    asserta(valuem(X,Y)); 
    asserta(value(X,Y))), 
    (\+ok2->asserta(ok2);true),
      
    bottom_up_main(X,Y); 
    (constant(Y)->   
    retractrules(X:=Y,Z), 
    \+exists_value(X,Y),  
    X=..[F|_],  
    (atom_concat(mg_,_,F)-> 
    asserta(valuem(X,Y)); 
    asserta(value(X,Y))), 
    (\+ok2->asserta(ok2);true),
     
    bottom_up_main(X,Y);
    (constantfun(Y)-> 
    value_of_goal(Y,T), 
    retractrules(X:=Y,Z), 
    \+exists_value(X,T),  
    X=..[F|_],  
    (atom_concat(mg_,_,F)-> 
    asserta(valuem(X,T)); 
    asserta(value(X,T))), 
    (\+ok2->asserta(ok2);true),
	  
    bottom_up_main(X,T); 
    (compound(Y)-> 
    value_of_goal(Y,T), 
    retractrules(X:=Y,Z), 
    \+exists_value(X,T),  
    X=..[F|_],  
    (atom_concat(mg_,_,F)-> 
    asserta(valuem(X,T)); 
    asserta(value(X,T))), 
    (\+ok2->asserta(ok2);true),
	  
    bottom_up_main(X,T))))). 
 
bottom_up_main:-ok2. 

bottom_up_main(E,T):- bottom_up_main2(E,T). 
 
bottom_up_main2(E,T):- 
   E=..[F|Args], 
   atom_concat(mg_,FUN,F), 
   NEW=..[FUN|Args], 
   \+none_value(NEW,T), 
   position(Args,I,Nesting), 
   check_constructor(NEW,FUN,I,Args,Nesting), 
   init_ok,   
   b_aux(NEW,I,Nesting).

bottom_up_main2(E,T):- 
  E=..[F|Args], 
  atom_concat(mg_,FUN,F), 
  NEW=..[FUN|Args], 
  \+none_value(NEW,T), 
  Args=[],
  init_ok,   
  b_aux(NEW,0,_).

 
b_aux(NEW,I,Nesting):-new_rules(NEW,I,Nesting),fail. 
b_aux(_,_,_):-ok. 
 
  
 

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
%  INIT OK 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
 
init_ok:-ok,!,retractall(ok). 
init_ok. 
 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
% CHECK CONSTRUCTOR 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
 
 
check_constructor(E,FUN,I,Args,Nesting):- 
     \+is_reached(E,I), 
     compound(Nesting), 
     test_safe(FUN,I,Args,Nesting),!, 
     asserta(reached(E,I)). 
 
check_constructor(E,_,I,_,_):- 
    is_reached(E,I),!, 
    fail. 
 
check_constructor(_,_,_,_,_). 

 
 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
%       NEW RULES 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 


 
new_rules(NEW,I,ArgI):-  
     new_rules2(NEW,I,ArgI,H,R,Z,1),   
     new_passing(H,R,Z),
     (\+ok -> asserta(ok);true).

  
      
 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
% NEW PASSING 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
 
new_passing(A,B,C):- 
     var(A),var(B),var(C),!. 
 
new_passing(HEAD,R,Z):-  
      magic_pred(HEAD,MHEAD), 
      passing_rules(HEAD,R,Z), 
      passing((Z),[],MHEAD),  
      recover_magic. 
 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
% NEW RULES2 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 

new_rules2(NEW,0,_,NEW,R,Z,1):- 
      retrieve_clause(NEW:=R,Z), 
      magic_pred(NEW,MNEW), 
      \+rule?(NEW:=R,(MNEW><true,Z)), 
      assert(NEW:=R:-(MNEW><true,Z)). 
 
 
new_rules2(NEW,0,_,_,_,_,2):-
	 retrieve_clause(NEW<=R,Z),  
      \+rule?(NEW<=R,Z), 
      assert(NEW<=R:-Z). 


 
new_rules2(NEW,I,ArgI,NEW,R,Z,1):-
      I>0, 
      var(ArgI), 
      retrieve_clause(NEW:=R,Z), 
      magic_pred(NEW,MNEW), 
      \+rule?(NEW:=R,(MNEW><true,Z)), 
      assert(NEW:=R:-(MNEW><true,Z)). 
 
 
new_rules2(NEW,I,ArgI,_,_,_,2):-
      I>0, 
      var(ArgI),   
      retrieve_clause(NEW<=R,Z),  
      \+rule?(NEW<=R,Z), 
      assert(NEW<=R:-Z). 
 
 
new_rules2(NEW,I,ArgI,NEW,R,Z,1):-
      I>0, 
      constant(ArgI), 
      retrieve_clause(NEW:=R,Z),  
      magic_pred(NEW,MNEW), 
      \+rule?(NEW:=R,(MNEW><true,Z)), 
      assert(NEW:=R:-(MNEW><true,Z)). 
 
 
new_rules2(NEW,I,ArgI,_,_,_,2):-
	 I>0, 
      constant(ArgI), 
      retrieve_clause(NEW<=R,Z), 
      \+rule?(NEW<=R,Z), 
      assert(NEW<=R:-Z). 
 
 

new_rules2(NEW,I,ArgI,_,_,_,_):-
	 I>0, 
      NEW=..[FUN|Args], 
      compound(ArgI), 
      function(ArgI), 
      test_safe(FUN,I,Args,ArgI), 
      ArgI=..[G|ArgsG], 
      position(ArgsG,J,ArgJ),  
      check_constructor(ArgI,G,J,ArgsG,ArgJ), 
      new_rules2(ArgI,J,ArgJ,_,_,_,2),
      fail. 
 
new_rules2(NEW,I,ArgI,_,_,_,_):-
	 I>0, 
      NEW=..[FUN|Args], 
      constantfun(ArgI), 
      test_safe(FUN,I,Args,ArgI), 
      new_rules2(ArgI,0,_,_,_,_,2),
      fail. 

 
new_rules2(NEW,I,ArgI,H,R,Z,CASE):- 
		new_rules2_nesting(NEW,I,ArgI,H,R,Z,CASE).
						    
new_rules2(NEW,I,ArgI,NEW,R,Z,1):-
	 I>0,  
      compound(ArgI), 
      constructor(ArgI),
      retrieve_clause(NEW:=R,Z),   
      magic_pred(NEW,MNEW),   
      \+rule?(NEW:=R,(MNEW><true,Z)), 
      assert(NEW:=R:-(MNEW><true,Z)). 
 
new_rules2(NEW,I,ArgI,_,_,_,2):-
      I>0,
      compound(ArgI), 
      constructor(ArgI), 
      retrieve_clause(NEW<=R,Z),    
      \+rule?(NEW<=R,Z),
      assert(NEW<=R:-Z).

new_rules2(NEW,I,ArgI,H,R,Z,1):-
      I>0, 
      NEW=..[FUN|Args], 
      constantfun(ArgI), 
      (\+test_safe(FUN,I,Args,ArgI),\+is_reached(ArgI,0)-> 
      H=..[FUN|Args], 
      retrieve_clause(NEW:=R,Z), 
      magic_pred(NEW,MNEW), 
      \+rule?(NEW:=R,(MNEW><true,Z)), 
      assert(NEW:=R:-(MNEW><true,Z));true). 
 
new_rules2(NEW,I,ArgI,_,_,_,2):-
      I>0, 
      NEW=..[FUN|Args], 
      constantfun(ArgI), 
      (\+test_safe(FUN,I,Args,ArgI),\+is_reached(ArgI,0)-> 
      retrieve_clause(NEW<=R,Z), 
      \+rule?(NEW<=R,Z), 
      assert(NEW<=R:-Z);true).



new_rules2(NEW,I,ArgI,H,R,Z,1):- 
      I>0, 
      NEW=..[FUN|Args], 
      compound(ArgI), 
      function(ArgI), 
      (\+test_safe(FUN,I,Args,ArgI),\+is_reached(ArgI,0)-> 
      H=..[FUN|Args], 
      retrieve_clause(NEW:=R,Z), 
      magic_pred(NEW,MNEW), 
      \+rule?(NEW:=R,(MNEW><true,Z)), 
      assert(NEW:=R:-(MNEW><true,Z));true). 
 
new_rules2(NEW,I,ArgI,_,_,_,2):-
      I>0, 
      NEW=..[FUN|Args], 
      compound(ArgI), 
      function(ArgI), 
      (\+test_safe(FUN,I,Args,ArgI),\+is_reached(ArgI,0)-> 
      retrieve_clause(NEW<=R,Z), 
      \+rule?(NEW<=R,Z), 
      assert(NEW<=R:-Z);true). 
 

new_rules2(NEW,I,ArgI,NEW,B,true,1):-
      I>0, 
      NEW=..[FUN|Args], 
      compound(ArgI), 
      constructor(ArgI), 
      ArgI=..[CON|ArgsC], 
      test_safe(FUN,I,Args,ArgI), 
      add_list(Args,I,ArgsC,ArgsAux), 
      atom_concat(FUN,I,FUN1), 
      (\+funct(FUN1)->asserta(funct(FUN1));true), 
      B=..[FUN1|ArgsAux], 
      magic_pred(NEW,MNEW),        
      \+rule?(NEW:=B,(MNEW><true)), 
      assert(NEW:=B:-(MNEW><true)), 
      new_values(FUN,FUN1,I,CON,Args,ArgsC,_,_,_,1). 
 
new_rules2(NEW,I,ArgI,_,_,_,2):-
      I>0, 
      NEW=..[FUN|Args], 
      compound(ArgI), 
      constructor(ArgI), 
      ArgI=..[CON|ArgsC], 
      test_safe(FUN,I,Args,ArgI), 
      add_list(Args,I,ArgsC,ArgsAux), 
      atom_concat(FUN,I,FUN1), 
      (\+funct(FUN1)->asserta(funct(FUN1));true),  
      B=..[FUN1|ArgsAux],       
      \+rule?(NEW<=B,true), 
      assert(NEW<=B:-true), 
      new_values(FUN,FUN1,I,CON,Args,ArgsC,_,_,_,2). 
 
 
 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
% NEW RULES2 NESTING 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
 
 
new_rules2_nesting(NEW,I,ArgI,NEW,B,Z,1):-
      I>0, 
      NEW=..[FUN|Args], 
      constantfun(ArgI), 
      test_safe(FUN,I,Args,ArgI), 
      exact_clause(ArgI<=R,Z),        
      magic_pred(NEW,MNEW), 
      substitute(Args,I,R,ArgsR), 
      B=..[FUN|ArgsR], 
      \+rule?(NEW:=B,(MNEW><true,Z)), 
      assert(NEW:=B:-(MNEW><true,Z)). 
 
new_rules2_nesting(NEW,I,ArgI,_,_,_,2):-
      I>0, 
      NEW=..[FUN|Args],        
      constantfun(ArgI), 
      test_safe(FUN,I,Args,ArgI),        
      exact_clause(ArgI<=R,Z),      
      substitute(Args,I,R,ArgsR), 
      B=..[FUN|ArgsR], 
      \+rule?(NEW<=B,Z), 
      assert(NEW<=B:-Z). 

new_rules2_nesting(NEW,I,ArgI,NEW,B,Z,1):-
      I>0, 
      NEW=..[FUN|Args], 
      compound(ArgI), 
      function(ArgI), 
      test_safe(FUN,I,Args,ArgI),  
      exact_clause(ArgI<=R,Z),        
      magic_pred(NEW,MNEW), 
      substitute(Args,I,R,ArgsR), 
      B=..[FUN|ArgsR], 
      \+rule?(NEW:=B,(MNEW><true,Z)), 
      assert(NEW:=B:-(MNEW><true,Z)). 
 
new_rules2_nesting(NEW,I,ArgI,_,_,_,2):-
      I>0, 
      NEW=..[FUN|Args],        
      compound(ArgI), 
      function(ArgI), 
      test_safe(FUN,I,Args,ArgI),        
      exact_clause(ArgI<=R,Z),        
      substitute(Args,I,R,ArgsR), 
      B=..[FUN|ArgsR], 
      \+rule?(NEW<=B,Z), 
      assert(NEW<=B:-Z). 
 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
% NEW VALUES 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
 
 
new_values(FUN,FUN1,I,CON,Args,ArgsC,B,R,Z,1):- 
      generate_vars(Args,Vars), 
      generate_vars(ArgsC,VarsC), 
      T=..[CON|VarsC], 
      substitute(Vars,I,T,VarsH), 
      H=..[FUN|VarsH], 
      retrieve_clause(H:=R,Z), 
      add_list(VarsH,I,VarsC,VarsB), 
      B=..[FUN1|VarsB], 
      \+(B=@=R), 
      retract(H:=R:-Z), 
      \+rule?(B=:R,Z), 
      assert(B=:R:-Z). 
 
new_values(FUN,FUN1,I,CON,Args,ArgsC,_,_,_,2):- 
      generate_vars(Args,Vars), 
      generate_vars(ArgsC,VarsC), 
      T=..[CON|VarsC], 
      substitute(Vars,I,T,VarsH), 
      H=..[FUN|VarsH], 
      retrieve_clause(H<=R,Z), 
      add_list(VarsH,I,VarsC,VarsB), 
      B=..[FUN1|VarsB], 
      \+(B=@=R), 
      retract(H<=R:-Z), 
      \+rule?(B<=R,Z), 
      assert(B<=R:-Z). 



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
% TEST SAFE 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
 
 
test_safe(F,I,Vars,Nesting):- 
        generate_vars(Vars,VarsTest), 
        H=..[F|VarsTest], 
        clause(H=:_,_), 
        position(VarsTest,I,T), 
        term_or_safe(F,T,I,Nesting),!. 
 
test_safe(F,I,Vars,Nesting):- 
        generate_vars(Vars,VarsTest), 
        H=..[F|VarsTest], 
        clause(H<=_,_), 
        position(VarsTest,I,T), 
        term_or_safe(F,T,I,Nesting),!. 
 
 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
% TERM OR SAFE 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
 
term_or_safe(F,T,I,_):-var(T),safe_variable(F,I),!. 
term_or_safe(_,T,_,_):-constant(T),!. 
term_or_safe(_,T,_,Nesting):-compound(T),constructor(T), \+vars(T), 
                Nesting=..[CON|_], 
                T=..[CON|_],!.
term_or_safe(_,T,_,Nesting):-compound(T),constructor(T), 
                constantfun(Nesting),!. 
term_or_safe(_,T,_,Nesting):-compound(T),constructor(T), 
                function(Nesting),!. 
 
vars(T):-T=..[_|Vars],all_vars(Vars). 
 
all_vars([]). 
all_vars([X|Vars]):-var(X),all_vars(Vars). 
 
 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
% SAFE 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
 
safe(X,E,_):-safe_exp(X,E),!. 
safe(X,_,C):-safe_cond(X,C). 
 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
% SAFE EXP 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
 
safe_exp(X,Y):-X==Y,!. 
safe_exp(X,E):- 
    compound(E), 
    E=..[_|LE], 
    constructor(E),!, 
    safe_list_exp(X,LE). 
 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
% SAFE LIST EXP 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
 
safe_list_exp(X,[E|_]):-safe_exp(X,E),!. 
safe_list_exp(X,[_|RE]):-safe_list_exp(X,RE),!. 
 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
% SAFE COND 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
 
safe_cond(X,(E1><_)):-safe_exp(X,E1),!. 
safe_cond(X,(_><E2)):-safe_exp(X,E2).

safe_cond(X,(E1==_)):-safe_exp(X,E1),!. 
safe_cond(X,(_==E2)):-safe_exp(X,E2). 

safe_cond(X,(E1=\=_)):-safe_exp(X,E1),!. 
safe_cond(X,(_=\=E2)):-safe_exp(X,E2). 

safe_cond(X,(E1>_)):-safe_exp(X,E1),!. 
safe_cond(X,(_>E2)):-safe_exp(X,E2). 

safe_cond(X,(E1<_)):-safe_exp(X,E1),!. 
safe_cond(X,(_<E2)):-safe_exp(X,E2). 

safe_cond(X,(E1>=_)):-safe_exp(X,E1),!. 
safe_cond(X,(_>=E2)):-safe_exp(X,E2). 

safe_cond(X,(E1=<_)):-safe_exp(X,E1),!. 
safe_cond(X,(_=<E2)):-safe_exp(X,E2). 


safe_cond(X,(EQ,_)):-safe_cond(X,EQ),!. 
safe_cond(X,(_,REQ)):-safe_cond(X,REQ). 
 
 

 
 
 
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
% MAGIC_PRED 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
 
magic_pred(E,ME):- 
    E=..[F|Args], 
    atom_concat(mg_,F,MG), 
    ME=..[MG|Args]. 
 
 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
% PASSING RULES 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
 
passing_rules(X,Y,Z):- 
    compound(Y), 
    constructor(Y), 
    Y=..[_|ArgC], 
    passings_rules(X,ArgC,Z), 
    fail. 


passing_rules(X,Y,Z):-     
    constantfun(Y), 
    magic_pred(Y,MY), 
    magic_pred(X,MX), 
    \+rule?(MY=>MX,Z), 
    assert(MY=>MX:-Z), 
    fail.
 
passing_rules(X,Y,Z):- 
    compound(Y), 
    function(Y), 
    magic_pred(Y,MY), 
    magic_pred(X,MX), 
    \+rule?(MY=>MX,Z), 
    assert(MY=>MX:-Z), 
    fail. 
 
 
passing_rules(_,_,_). 
 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
% PASSINGS RULES 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
 
passings_rules(_,[],_):-!. 
passings_rules(X,[Y|ArgY],Z):- 
    passing_rules(X,Y,Z), 
    passings_rules(X,ArgY,Z). 
 
 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
% PASSING 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
 
passing((EQ),C,MX):-passing_rule(EQ,C,MX). 
passing((EQ,REQ),C,MX):- 
    passing_rule(EQ,C,MX), 
    passing((REQ),[EQ|C],MX). 
 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
% PASSING RULE %modified 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
 
passing_rule(true,_,_):-!. 
passing_rule(E1><E2,C,MX):-!,passing_exp(E1,C,MX),
					      passing_exp(E2,C,MX). 
passing_rule(_,_,_).
 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
% PASSING EXP 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
 
passing_exp(X,_,_):-var(X),fail. 
passing_exp(D,_,_):-constant(D),fail. 
passing_exp(E,C,MX):- 
    compound(E), 
    constructor(E), 
    E=..[_|ArgsH], 
    passings_exp(ArgsH,C,MX), 
    fail. 

passing_exp(E,C,MX):- 
    constantfun(E), 
    magic_pred(E,ME), 
    cond(C,CR), 
    \+rule?(ME=>MX,CR), 
    assert(ME=>MX:-CR), 
    fail.
 
passing_exp(E,C,MX):- 
    compound(E), 
    function(E), 
    magic_pred(E,ME), 
    cond(C,CR), 
    \+rule?(ME=>MX,CR), 
    assert(ME=>MX:-CR), 
    fail. 
 
passing_exp(_,_,_). 
 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
% PASSINGS EXP 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
 
passings_exp([],_,_):-!. 
passings_exp([Arg|RArgs],C,MX):- 
    passing_exp(Arg,C,MX), 
    passings_exp(RArgs,C,MX). 
 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
% COND 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
 
cond([],true):-!. 
cond([EQ],EQ):-!. 
cond([EQ|REQ],(EQ,RC)):-cond(REQ,RC). 

 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% AUXILIARY PREDICATES
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%
% constant
%%%%%%%%%%%%%%%

constant(Arg):-atomic(Arg),\+function(Arg),!.

 

%%%%%%%%%%%%%%%%%
% constantfun
%%%%%%%%%%%%%%%

constantfun(Arg):-atomic(Arg),function(Arg),!.
 
 

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
% CONSTRUCTOR 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
 
constructor(Arg):- 
    \+function(Arg),!. 
 
 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
% FUNCTION 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 

  
function(Arg):- 
    Arg=..[F|_], 
    funct(F),!. 
 
function(Arg):- 
    Arg=..[F|_], 
    atom_concat(mg_,FUN,F), 
    funct(FUN),!.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
% UNIFY % WITHOUT FUNCTIONS 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
 
unify(X,Y):-var(X),var(Y),!,X=Y. 
unify(X,Y):-var(X),constant(Y),!,X=Y. 
unify(X,Y):-constant(X),constant(Y),!,X=Y.
unify(X,Y):-constantfun(X),constantfun(Y),!,X=Y. 
unify(X,Y):-var(X),compound(Y),constructor(Y), 
                Y=..[C|Args],generate_vars(Args,VarsX), 
            X=..[C|VarsX], unify_list(VarsX,Args),!. 
 
unify(X,Y):-compound(X),compound(Y), 
              X=..[F|ArgsX],Y=..[F|ArgsY], 
                unify_list(ArgsX,ArgsY),!. 
 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
% UNIFY2 % BIDIRECTIONAL 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
 
 
unify2(X,Y):-unify(X,Y),!. 
unify2(X,Y):-unify(Y,X),!. 
 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
% UNIFY_LIST 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
 
unify_list([],[]):-!. 
unify_list([X|L1],[Y|L2]):-unify2(X,Y),unify_list(L1,L2),!.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
% RULE? 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
 
rule?(X:=Y,Z):-clause(U:=V,W),U=@=X,V=@=Y,Z=@=W,!. 
rule?(X<=Y,Z):-clause(U<=V,W),U=@=X,V=@=Y,Z=@=W,!.
rule?(X==:Y,Z):-clause(U==:V,W),U=@=X,V=@=Y,Z=@=W,!.
rule?(X=:Y,Z):-clause(U=:V,W),U=@=X,V=@=Y,Z=@=W,!.
rule?(X=>Y,Z):-clause(U=>V,W),U=@=X,V=@=Y,Z=@=W,!. 


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% RETRIEVE CLAUSE
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 
retrieve_clause(X:=Y,Z):-clause(X=:Y,Z). 
retrieve_clause(X<=Y,Z):-clause(X=:Y,Z). 
retrieve_clause(X<=Y,Z):-clause(X<=Y,Z). 

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% EXACT CLAUSE
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 
exact_clause(X<=Y,true):-clause(A<=Y,true),unify2(X,A). 
exact_clause(X<=Y,Z):-clause(A<=Y,Z),unify2(X,A). 

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% APPLY RULE
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 
 
apply_rule(X:=Y,M><true):-                          
                        clause(X:=Y,M><true),
					valuem(M,true).

apply_rule(X:=Y,(M><true,Z)):-  
                        clause(X:=Y,(M><true,Z)),
					valuem(M,true). 
 
 apply_rule(X:=true,true):- 
                        clause(X:=true,true), 
                        X=..[F|_], 
                        atom_concat(mg_,_,F). 


apply_rule(X:=true,Z):- 
                        clause(X:=true,Z),
                        Z\==true, 
                        X=..[F|_], 
                        atom_concat(mg_,_,F). 
apply_rule(X:=M,true):- 
                        clause(X:=M,true),
					valuem(M,true), 
                        M=..[F|_], 
                        atom_concat(mg_,_,F). 
 
apply_rule(X:=M,Z):- 
                        clause(X:=M,Z), 
                        Z\==true,
					valuem(M,true), 
                        M=..[F|_], 
                        atom_concat(mg_,_,F). 
 

  
 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
% exists_solution 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
 
exists_solution(X):-sol(Y),X=@=Y,!.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
% is_reached 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
 
is_reached(E,I):-reached(F,J),E=@=F,I>=J,!. 
is_reached(E,I):-reached(F,J),E=@=F,I=<J,!. 
 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
% EXISTS VALUE 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
 
 
exists_value(X,Y):-value(Z,W),Z=@=X,Y=@=W,!. 
exists_value(X,Y):-valuem(Z,W),Z=@=X,Y=@=W,!.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% NONE VALUE
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 
 
none_value(X,_):-value(Z,_),Z=@=X,!. 
 


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
% RETRACT RULES 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
 
 
retractrules(X:=Y,Z):- rule?(X:=Y,Z),retract(X:=Y:-Z),fail. 
retractrules(_:=_,_).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
% RECOVER MAGIC 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
 
recover_magic:- 
    clause(X=>Y,Z), 
    \+rule?(X:=Y,Z), 
    assert(X:=Y:-Z), 
    fail. 
 
recover_magic:- 
    retractall(_=>_),!.



%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
% MEMBER 
%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
 
member(X,[X|_]):-!. 
member(X,[_|L]):-member(X,L). 


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
%  SUBSTITUTE 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
 
substitute([_|L],1,Arg,[Arg|L]):-!. 
substitute([X|L],J,Arg,[X|L2]):-J>1,I is J-1,substitute(L,I,Arg,L2),!. 
 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
% ADD_LIST 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
 
add_list([_|RVars],1,CC,Vars):-append(CC,RVars,Vars),!. 
add_list([X|RVars],I,CC,[X|Vars]):-I>1,J is I-1, add_list(RVars,J,CC,Vars),!.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
% POSITION 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
 
position([T|_],1,T). 
position([_|RT],I,M):- 
    position(RT,J,M), 
    I is J+1.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
% GENERATE VARS 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
 
generate_vars([],[]). 
generate_vars([_|LAR],[_|LV]):-generate_vars(LAR,LV). 
 
 
 
 
 
 
 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
% DATABASE 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
% SELECT 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 

 


select FIELDS as RENAMES from RELATIONS where CONDITIONS:-!,
    %[indalog],
    write(RENAMES),nl,
    select(FIELDS,RELATIONS,CONDITIONS,VALUES,_),     
    write(VALUES),nl,fail.
    
select FIELDS as RENAMES from RELATIONS:-!,
    %[indalog],
    write(RENAMES),nl,
    select(FIELDS,RELATIONS,[],VALUES,_),     
    write(VALUES),nl,fail.
    
select FIELDS from RELATIONS where CONDITIONS:-!,
    %[indalog],
    write(FIELDS),nl,
    select(FIELDS,RELATIONS,CONDITIONS,VALUES,_),     
    write(VALUES),nl,fail.

select FIELDS from RELATIONS:-!,
    %[indalog],
    write(FIELDS),nl,
    select(FIELDS,RELATIONS,[],VALUES,_),    
    write(VALUES),nl,fail.
    
 

 
select(LISTFIELDS,RELATIONS,CONDITIONS,LISTVALUES,GOAL):-
                clean_aux, 
                (relations(RELATIONS,[],LISTVARSKEYS,true,GOALSKEYS),   
                generate_conditions(RELATIONS,LISTVARSKEYS,[],LISTINVERSES,CONDITIONS,GOALSKEYS,GOALSCONDS),
  			    select_aux(RELATIONS,LISTVARSKEYS,LISTINVERSES,_,LISTFIELDS,LISTVALUES,GOALSCONDS,GOAL)-> 
                write('Translation   :'),nl,write(GOAL),nl,  
                (check_goal(GOAL)->	call_goal(GOAL);wrong_goal,fail);
                wrong_select,fail). 

wrong_select:-write('WARNING: Wrong select expression'),nl.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% CLEAN AUX
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


clean_aux:-clause(dataaux(X,Y),Z),retract(dataaux(X,Y):-Z),fail.
clean_aux:-clause(keyaux(X,Y),Z),retract(keyaux(X,Y):-Z),fail.
clean_aux.
 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
% RELATIONS 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
 
relations([RELATION|RELATIONS],STOREDVARS,LISTVARSKEYS,STORED,GOALSKEYS):- 
                key K, K=..[RELATION|LKEYS],!,  
                generate_vars(LKEYS,VARSKEYS), 
                KEYS=..[RELATION|VARSKEYS], 
                STORED2=..[',',KEYS><ok,STORED],
                append(STOREDVARS,[VARSKEYS],STORED3), 
                relations(RELATIONS,STORED3,LISTVARSKEYS,STORED2,GOALSKEYS). 

relations([select LISTFIELDS as RENAMES from RELATIONS2 where 
				CONDITIONS|RELATIONS],STOREDVARS,LISTVARSKEYS,STORED,GOALSKEYS):-!, 
			     nested_select(LISTFIELDS,RELATIONS2,CONDITIONS,LISTVARSKEYS2,_,GOAL),
                 NAME=(select LISTFIELDS as RENAMES from RELATIONS2 where CONDITIONS),
                 insert_database(NAME,LISTFIELDS),  
                 insert_key(NAME,RELATIONS2,LISTFIELDS,[]), 
			    concat_goal(STORED,GOAL,STORED2), 
                 append(STOREDVARS,LISTVARSKEYS2,STORED3),
			   relations(RELATIONS,STORED3,LISTVARSKEYS,STORED2,GOALSKEYS).  

relations([select LISTFIELDS as RENAMES from RELATIONS2 |RELATIONS],STOREDVARS,LISTVARSKEYS,STORED,GOALSKEYS):-!, 
			     nested_select(LISTFIELDS,RELATIONS2,[],LISTVARSKEYS2,_,GOAL),
                 NAME=(select LISTFIELDS as RENAMES from RELATIONS2),
			    insert_database(NAME,LISTFIELDS), 
                 insert_key(NAME,RELATIONS2,LISTFIELDS,[]), 
			    concat_goal(STORED,GOAL,STORED2), 
                 append(STOREDVARS,LISTVARSKEYS2,STORED3),
			    relations(RELATIONS,STORED3,LISTVARSKEYS,STORED2,GOALSKEYS).  



relations([select LISTFIELDS from RELATIONS2 where CONDITIONS|RELATIONS],STOREDVARS,LISTVARSKEYS,STORED,GOALSKEYS):-!,
			   nested_select(LISTFIELDS,RELATIONS2,CONDITIONS,LISTVARSKEYS2,_,GOAL),
                 NAME=(select LISTFIELDS from RELATIONS2 where CONDITIONS),
                 insert_database(NAME,LISTFIELDS),
                 insert_key(NAME,RELATIONS2,LISTFIELDS,[]),
			     concat_goal(STORED,GOAL,STORED2), 
                 append(STOREDVARS,LISTVARSKEYS2,STORED3),
			    relations(RELATIONS,STORED3,LISTVARSKEYS,STORED2,GOALSKEYS).  



relations([select LISTFIELDS from RELATIONS2|RELATIONS],STOREDVARS,LISTVARSKEYS,STORED,GOALSKEYS):-!,
			   nested_select(LISTFIELDS,RELATIONS2,[],LISTVARSKEYS2,_,GOAL),
                 NAME=(select LISTFIELDS from RELATIONS2), 
                 insert_database(NAME,LISTFIELDS),
                 insert_key(NAME,RELATIONS2,LISTFIELDS,[]),
			   concat_goal(STORED,GOAL,STORED2),  
                 append(STOREDVARS,LISTVARSKEYS2,STORED3),
			   relations(RELATIONS,STORED3,LISTVARSKEYS,STORED2,GOALSKEYS).  

relations([],VARS,VARS,GOALS,GOALS).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% NESTED SELECT
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

nested_select(LISTFIELDS,RELATIONS,CONDITIONS,LISTVARSKEYS,LISTVALUES,GOAL):- 
                 relations(RELATIONS,[],LISTVARSKEYS,true,GOALSKEYS),    
                 generate_conditions(RELATIONS,LISTVARSKEYS,[],LISTINVERSES,CONDITIONS,GOALSKEYS,GOALSCONDS),                 			   	            select_aux(RELATIONS,LISTVARSKEYS,LISTINVERSES,_,LISTFIELDS,LISTVALUES,GOALSCONDS,GOAL).
                                 
 



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% CONCAT GOAL
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%                 


concat_goal((G),GOALS,GOALS2):- \+functor(G,',',_),GOALS2=..[',',G,GOALS],!.

concat_goal((G1,RGOALS),GOALS,GOALS2):-concat_goal(RGOALS,GOALS,GOALS3),GOALS2=..[',',G1,GOALS3].




%%%%%%%%%%%%%%%%%%%%%%%%%%
% INSERT DATABASE
%%%%%%%%%%%%%%%%%%%%%%%%%%

insert_database(NAME,_):-					  
                         NAME=(select LF as _ from RELATIONS where _),!,
                         recover_fields(RELATIONS,[],LRENAMES,[],LFIELDS), 
                         search_fields(LF,LRENAMES,LFIELDS,LD),
                 		 assert(dataaux(NAME,LD):-true).
         


insert_database(NAME,_):-					  
                         NAME=(select LF as _ from RELATIONS),!,
					  recover_fields(RELATIONS,[],LRENAMES,[],LFIELDS),  
                         search_fields(LF,LRENAMES,LFIELDS,LD), 
                 		  assert(dataaux(NAME,LD):-true).
                          
insert_database(NAME,_):-					  
                         NAME=(select LF from RELATIONS where _),!,
                         recover_fields(RELATIONS,[],LRENAMES,[],LFIELDS), 
                         search_fields(LF,LRENAMES,LFIELDS,LD),
                 		 assert(dataaux(NAME,LD):-true).
         


insert_database(NAME,_):-					  
                         NAME=(select LF from RELATIONS),!,
					  recover_fields(RELATIONS,[],LRENAMES,[],LFIELDS),  
                         search_fields(LF,LRENAMES,LFIELDS,LD),
                 		  assert(dataaux(NAME,LD):-true).
                          


insert_database(NAME,LISTFIELDS):-                  
                 assert(dataaux(NAME,LISTFIELDS):-true).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% SEARCH FIELDS
%%%%%%%%%%%%%%%%%%%%%%%%%%%%

search_fields([X|REN],REN2,L1,L2):-
     search_fields_aux(X,REN2,L1,L3),!,
     search_fields(REN,REN2,L1,L4),
     append([L3],L4,L2).

search_fields([X|REN],REN2,L1,[X|L2]):-!,
     search_fields(REN,REN2,L1,L2).

search_fields([],_,_,[]).



search_fields_aux(X,[X|_],[Y|_],Y):-!.

search_fields_aux(inv(S,J,X),LREN,LF,inv(S,J,Y)):-search_fields_aux(X,LREN,LF,Y).

search_fields_aux((E,X),LREN,LF,(E,Y)):-search_fields_aux(X,LREN,LF,Y).

search_fields_aux(X,[_|LREN],[_|LF],Y):- search_fields_aux(X,LREN,LF,Y).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% RECOVER fields
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

recover_fields([],L,L,L2,L2):-!.

recover_fields([RELATION|RELATIONS],LREN,LREN2,LFIELD,LFIELD2):-
			database D,D=..[RELATION|LFIELDS],!,
			append(LREN,LFIELDS,LREN3),
			append(LFIELD,LFIELDS,LFIELD3),
			recover_fields(RELATIONS,LREN3,LREN2,LFIELD3,LFIELD2). 

recover_fields([RELATION|RELATIONS],LREN,LREN2,LFIELD,LFIELD2):-
			RELATION=(select _ as LR from _ where _),!,
              dataaux(RELATION,LFIELDS),
			append(LREN,LR,LREN3),
			append(LFIELD,LFIELDS,LFIELD3),
			recover_fields(RELATIONS,LREN3,LREN2,LFIELD3,LFIELD2). 

recover_fields([RELATION|RELATIONS],LREN,LREN2,LFIELD,LFIELD2):-
			RELATION=(select _ as LR from _),!,
              dataaux(RELATION,LFIELDS),
			append(LREN,LR,LREN3),
			append(LFIELD,LFIELDS,LFIELD3),
			recover_fields(RELATIONS,LREN3,LREN2,LFIELD3,LFIELD2). 

recover_fields([RELATION|RELATIONS],LREN,LREN2,LFIELD,LFIELD2):-
			RELATION=(select LF from _ where _),!,
              dataaux(RELATION,LFIELDS),
			append(LREN,LF,LREN3),
			append(LFIELD,LFIELDS,LFIELD3),
			recover_fields(RELATIONS,LREN3,LREN2,LFIELD3,LFIELD2). 

recover_fields([RELATION|RELATIONS],LREN,LREN2,LFIELD,LFIELD2):-
			RELATION=(select LF from _),!,
              dataaux(RELATION,LFIELDS),
			append(LREN,LF,LREN3),
			append(LFIELD,LFIELDS,LFIELD3),
			recover_fields(RELATIONS,LREN3,LREN2,LFIELD3,LFIELD2). 


  

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% INSERT KEY
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

insert_key(_,_,[],[]):-!.


insert_key(NAME,_,[],KEYS):-assert(keyaux(NAME,KEYS):-true).


insert_key(NAME,RELATIONS,[inv(_,_,FIELD)|RFIELDS],KEYS):-
	    				   insert_key(NAME,RELATIONS,[FIELD|RFIELDS],KEYS),!.

insert_key(NAME,RELATIONS,[(RELATION,FIELD)|RFIELDS],KEYS):-
	    				   member(RELATION,RELATIONS),                       
					   insert_key(NAME,RELATIONS,[FIELD|RFIELDS],KEYS),!.

insert_key(NAME,RELATIONS,[CON|RFIELDS],KEYS):- 
						CON=..[C|Args],
						data(C,_), !, 
                            append(Args,RFIELDS,NEW),
						insert_key(NAME,RELATIONS,NEW,KEYS).

 
insert_key(NAME,RELATIONS,[FUN|RFIELDS],KEYS):-
						FUN=..[F|Args],
						intfun(F,_),!,
                            append(Args,RFIELDS,NEW),
						insert_key(NAME,RELATIONS,NEW,KEYS).
						 

insert_key(NAME,RELATIONS,[FIELD|RFIELDS],KEYS):-
	    				   key K, 
                           K=..[RELATION|LFIELDS],  
		                 member(RELATION,RELATIONS),                       
                          member(FIELD,LFIELDS),!,            
					   append(LFIELDS,KEYS,KEYS2),           
					   insert_key(NAME,RELATIONS,RFIELDS,KEYS2).

insert_key(NAME,RELATIONS,[FIELD|RFIELDS],KEYS):-
					   keyaux(RELATION,LFIELDS),  
					   member(RELATION,RELATIONS),                       
                           member(FIELD,LFIELDS),!,                       
					   append(LFIELDS,KEYS,KEYS2),           
					   insert_key(NAME,RELATIONS,RFIELDS,KEYS2).

insert_key(NAME,RELATIONS,[FIELD|RFIELDS],KEYS):-					  
                         RELATION=(select _ as RENAMES from _ where _),
                         dataaux(RELATION,LFIELDS),
                         search_rename(FIELD,RENAMES,LFIELDS,FIELDNAME),                        
					  keyaux(RELATION,LKEYS),  
                         member(FIELDNAME,LKEYS),!,
					 append(LKEYS,KEYS,KEYS2),           
                         insert_key(NAME,RELATIONS,RFIELDS,KEYS2).

insert_key(NAME,RELATIONS,[FIELD|RFIELDS],KEYS):-					  
                         RELATION=(select _ as RENAMES from _),  
                         dataaux(RELATION,LFIELDS),  
                         search_rename(FIELD,RENAMES,LFIELDS,FIELDNAME),                         
					  keyaux(RELATION,LKEYS),  
                         member(FIELDNAME,LKEYS),!, 
					  append(LKEYS,KEYS,KEYS2),
                         insert_key(NAME,RELATIONS,RFIELDS,KEYS2).

insert_key(NAME,RELATIONS,[FIELD|RFIELDS],KEYS):-					  
                         RELATION=(select LF from _ where _),  
                         dataaux(RELATION,LFIELDS),
                         search_rename(FIELD,LF,LFIELDS,FIELDNAME),                        
					 keyaux(RELATION,LKEYS),  
                         member(FIELDNAME,LKEYS),!,
                          append(LKEYS,KEYS,KEYS2),
                         insert_key(NAME,RELATIONS,RFIELDS,KEYS2).

insert_key(NAME,RELATIONS,[FIELD|RFIELDS],KEYS):-					  
                         RELATION=(select LF from _), 
                         dataaux(RELATION,LFIELDS),
                         search_rename(FIELD,LF,LFIELDS,FIELDNAME),                        
					 keyaux(RELATION,LKEYS),  
                         member(FIELDNAME,LKEYS),!,
					 append(LKEYS,KEYS,KEYS2),
                         insert_key(NAME,RELATIONS,RFIELDS,KEYS2).
          

insert_key(NAME,RELATIONS,[_|RFIELDS],KEYS):-
					   insert_key(NAME,RELATIONS,RFIELDS,KEYS).                  

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% SEARCH RENAME
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

search_rename(REN,[REN|_],[(_,ORIG)|_],ORIG):-!.
search_rename(REN,[REN|_],[ORIG|_],ORIG):-!.
search_rename(REN,[_|LREN],[_|LORIG],ORIG2):-search_rename(REN,LREN,LORIG,ORIG2),!.

 

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
% SELECT AUX 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
 
select_aux(_,_,LINV,LINV,[],[],GOALS,GOALS). 
 
select_aux(RELATIONS,LISTVARSKEYS, LINV,LINVOUT, [FIELD|RF],[X|RVALUES],STORED,GOALS):- 
                is_key(RELATIONS,FIELD,FIELDNAME,LKEYS,LISTVARSKEYS,_,VARSKEYS), 
                is_field(RELATIONS,FIELD,_,LISTVARSKEYS,_),   
                look_key(VARSKEYS,LKEYS,FIELDNAME,X), !,    
                select_aux(RELATIONS,LISTVARSKEYS, LINV,LINVOUT, RF,RVALUES,STORED,GOALS). 
 

select_aux(RELATIONS,LISTVARSKEYS, LINV, LINVOUT, [FIELD|RF],VALUES,STORED,GOALS):-
                is_field(RELATIONS,FIELD,FIELDNAME,LISTVARSKEYS,_), 
                FIELDNAME=(RELATION,X),
                member(RELATION,RELATIONS),!, 
                select_aux(RELATIONS,LISTVARSKEYS, LINV, LINVOUT, [X|RF],VALUES,STORED,GOALS).
        
select_aux(RELATIONS,LISTVARSKEYS, LINV, LINVOUT2, [FIELD|RF],[VAR|RVALUES],STORED,GOALS):-
                is_field(RELATIONS,FIELD,FIELDNAME,LISTVARSKEYS,_),
                FIELDNAME=inv(_,_,_),!,    
                generate_fun(RELATIONS,LISTVARSKEYS, LINV,LINVOUT,FIELDNAME,GOAL,VAR,STRUCT,STORED,GOALOUT),    
                new_goal(LINVOUT,FIELDNAME,GOAL,STRUCT,GOALOUT,NEW),   
                select_aux(RELATIONS,LISTVARSKEYS, LINVOUT, LINVOUT2, RF,RVALUES,NEW,GOALS).
 
select_aux(RELATIONS,LISTVARSKEYS, LINV, LINVOUT2, [FIELD|RF],[VAR|RVALUES],STORED,GOALS):-
                is_field(RELATIONS,FIELD,FIELDNAME,LISTVARSKEYS,_),
                data(C,_), FIELDNAME=..[C|_],!, 
                generate_fun(RELATIONS,LISTVARSKEYS, LINV,LINVOUT,FIELDNAME,GOAL,VAR,STRUCT,STORED,GOALOUT),  
                new_goal(LINVOUT,FIELDNAME,GOAL,STRUCT,GOALOUT,NEW),   
                select_aux(RELATIONS,LISTVARSKEYS, LINVOUT, LINVOUT2, RF,RVALUES,NEW,GOALS).
 
select_aux(RELATIONS,LISTVARSKEYS, LINV, LINVOUT2, [FIELD|RF],[VAR|RVALUES],STORED,GOALS):-
                is_field(RELATIONS,FIELD,FIELDNAME,LISTVARSKEYS,_),
                intfun(F,_), FIELDNAME=..[F|_],!,    
                generate_fun(RELATIONS,LISTVARSKEYS, LINV,LINVOUT,FIELDNAME,GOAL,VAR,STRUCT,STORED,GOALOUT),  
                new_goal(LINVOUT,FIELDNAME,GOAL,STRUCT,GOALOUT,NEW), 
                select_aux(RELATIONS,LISTVARSKEYS, LINVOUT, LINVOUT2, RF,RVALUES,NEW,GOALS). 
 
select_aux(RELATIONS,LISTVARSKEYS, LINV, LINVOUT,[FIELD|RF],[X|RVALUES],STORED,GOALS):-  
                is_field(RELATIONS,FIELD,FIELDNAME,LISTVARSKEYS,VARSKEYS),!,       
                FUN=..[FIELDNAME|VARSKEYS],
			  new_goal(LINVOUT,FIELDNAME,FUN,X,STORED,NEW), 
                select_aux(RELATIONS,LISTVARSKEYS, LINV, LINVOUT, RF,RVALUES,NEW,GOALS). 
 
select_aux(RELATIONS,LISTVARSKEYS, LINV, LINVOUT2, [FIELD|RF],[VAR|RVALUES],STORED,GOALS):-   
                generate_fun(RELATIONS,LISTVARSKEYS, LINV,LINVOUT,FIELD,GOAL,VAR,STRUCT,STORED,GOALOUT),                  
                new_goal(LINVOUT,FIELD,GOAL,STRUCT,GOALOUT,NEW), 
                select_aux(RELATIONS,LISTVARSKEYS, LINVOUT, LINVOUT2, RF,RVALUES,NEW,GOALS).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
% LOOK KEY 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
 
look_key([X|_],[KEY|_],KEY,X):-!. 
look_key([_|RV],[_|RKEY],NKEY,Y):-look_key(RV,RKEY,NKEY,Y),!. 
 

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% NEW GOAL
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

new_goal(LINVOUT,FIELD,_,STRUCT,GOALOUT,GOALOUT):-
    FIELD=inv(FUN,I,EXPR), 
    is_inverse(FUN,I,EXPR,LINVOUT,STRUCT2),!, 
    STRUCT=STRUCT2.

new_goal(_,_,GOAL,STRUCT,GOALOUT,NEW):-
	NEW=..[',',GOAL><STRUCT,GOALOUT].

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% IS INVERSE
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 
is_inverse(FUN,I,EXPR,[inv(FUN,J,EXPR,STRUCT)|_],STRUCT):-I\==J,!.
is_inverse(FUN,I,EXPR,[_|RI],STRUCT):-is_inverse(FUN,I,EXPR,RI,STRUCT).
 
 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
% GENERATE CONDITIONS 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
 
generate_conditions(RELATIONS,LISTVARSKEYS,LINV,LINVOUT3,[EQ1><EQ2|RC],STORED,GOAL):- 
                        generate_fun(RELATIONS,LISTVARSKEYS,LINV,LINVOUT,EQ1,GOAL1,VAR1,STRUCT1,STORED,GOALOUT1), 
                    generate_fun(RELATIONS,LISTVARSKEYS,LINVOUT,LINVOUT2,EQ2,GOAL2,VAR2,STRUCT2,GOALOUT1,GOALOUT2), 
                        VAR1=GOAL2, 
                        VAR2=GOAL1, 
                        STORED2=..[',',STRUCT1><STRUCT2,GOALOUT2], 
                        generate_conditions(RELATIONS,LISTVARSKEYS,LINVOUT2,LINVOUT3,RC,STORED2,GOAL). 
 
generate_conditions(RELATIONS,LISTVARSKEYS,LINV,LINVOUT3,[EQ1>EQ2|RC],STORED,GOAL):- 
                        generate_fun(RELATIONS,LISTVARSKEYS,LINV,LINVOUT,EQ1,GOAL1,VAR1,STRUCT1,STORED,GOALOUT1), 
                      generate_fun(RELATIONS,LISTVARSKEYS,LINVOUT,LINVOUT2,EQ2,GOAL2,VAR2,STRUCT2,GOALOUT1,GOALOUT2), 
                        VAR1=GOAL2, 
                        VAR2=GOAL1, 
                        STRUCT1=STRUCT2, 
                  	  generate_conditions(RELATIONS,LISTVARSKEYS, LINVOUT2,LINVOUT3,RC,GOALOUT2,GOAL). 
 
generate_conditions(RELATIONS,LISTVARSKEYS,LINV,LINVOUT3,[EQ1=EQ2|RC],STORED,GOAL):- 
                        generate_fun(RELATIONS,LISTVARSKEYS,LINV,LINVOUT,EQ1,GOAL1,VAR1,STRUCT1,STORED,GOALOUT1), 
                     generate_fun(RELATIONS,LISTVARSKEYS,LINVOUT,LINVOUT2,EQ2,GOAL2,VAR2,STRUCT2,GOALOUT1,GOALOUT2), 
                        VAR1=GOAL2, 
                        VAR2=GOAL1, 
                        STRUCT1=STRUCT2, 
                        generate_conditions(RELATIONS,LISTVARSKEYS,LINVOUT2,LINVOUT3,RC,GOALOUT2,GOAL). 
 
generate_conditions(_,_,LINV,LINV,[],STORED,STORED). 
 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
% GENERATE FUN 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
generate_fun(RELATIONS,LISTVARSKEYS,LINV,LINV,FIELD,FUN,Z1,Z1,GOALS,GOALS):-  
                        is_key(RELATIONS,FIELD,FIELDNAME,LFIELDS,LISTVARSKEYS,_,VARSKEYS),
                        is_field(RELATIONS,FIELD,_,LISTVARSKEYS,_),!,  
                        look_key(VARSKEYS,LFIELDS,FIELDNAME,FUN). 
	      
generate_fun(RELATIONS,LISTVARSKEYS,LINV,LOUT,FIELD,FUN,Z1,Z2,GOALS,GOALS2):-  
                        is_field(RELATIONS,FIELD,FIELDNAME,LISTVARSKEYS,VARSKEYS),
                        \+atomic(FIELDNAME),!,   
                   generate_fun_field(RELATIONS,LISTVARSKEYS,LINV,LOUT,FIELDNAME,FUN,Z1,Z2,GOALS,GOALS2,VARSKEYS).

generate_fun(RELATIONS,LISTVARSKEYS,LINV,LINV,FIELD,FUN,Z1,Z1,GOALS,GOALS):-  
                        is_field(RELATIONS,FIELD,FIELDNAME,LISTVARSKEYS,VARSKEYS),!, 
                        atomic(FIELDNAME),              
                        FUN=..[FIELDNAME|VARSKEYS],!. 
 
generate_fun(RELATIONS,LISTVARSKEYS,LINV,[inv(C,I,EXPR,X2)|LINVOUT],FIELD,FUN2,X,CON2,GOAL,GOALOUT):-  
                        FIELD=inv(C,I,EXPR),   
                        data(C,K), 
                        !,    
                        generate_fun(RELATIONS,LISTVARSKEYS,LINV,LINVOUT,EXPR,FUN2,X2,CON2,GOAL,GOALOUT), 	             
                        generate_template(C,K,[],VARSC,I,X), 
                        CON=..[C|VARSC], 
                        X2=CON.

generate_fun(RELATIONS,LISTVARSKEYS,LINV,[inv(F,I,EXPR,X2)|LINVOUT],FIELD,FUN2,X,CON2,GOAL,GOALOUT):-   
                        FIELD=inv(F,I,EXPR), 
                        intfun(F,K), 
                        !, 
                        generate_fun(RELATIONS,LISTVARSKEYS,LINV,LINVOUT,EXPR,FUN2,X2,CON2,GOAL,GOALOUT), 
                        generate_template(F,K,[],VARSF,I,X), 
                        CON=..[F|VARSF], 
                        X2=CON. 
 
generate_fun(RELATIONS,LISTVARSKEYS,LINV,LINVOUT,FIELD,FUN,NZ1,NZ1,GOALS,GOALSOUT):- 
                        FIELD=..[C|Args], 
                        data(C,_), 
                        !,   
                        generate_fun_args(RELATIONS,LISTVARSKEYS,LINV,LINVOUT,Args,NewArgs,_,_,GOALS,GOALSOUT), 
                        FUN=..[C|NewArgs]. 
 
generate_fun(RELATIONS,LISTVARSKEYS,LINV,LINVOUT,FIELD,FUN,NZ1,NZ1,GOALS,GOALSOUT):- 
                        FIELD=..[F|Args], 
                        intfun(F,_), 
                        !, 
                        generate_fun_args(RELATIONS,LISTVARSKEYS,LINV,LINVOUT,Args,NewArgs,_,_,GOALS,GOALSOUT), 
                        FUN=..[F|NewArgs]. 
 
 
generate_fun(_,_,LINV,LINV,N,N,Z1,Z1,GOAL,GOAL). 

 
generate_fun_args(REL,LIST,LINV,LINVOUT2,[X|L],[Y|L9],[Z1|ZS1],[Z2|ZS2],GOALS,GOALSOUT):- 
                generate_fun(REL,LIST,LINV,LINVOUT,X,Y,Z1,Z2,GOALS,GOALSOUT1),  
                var(Z2),!, 
                generate_fun_args(REL,LIST,LINVOUT,LINVOUT2, L,L9,ZS1,ZS2,GOALSOUT1,GOALSOUT). 
 
generate_fun_args(REL,LIST,LINV,LINVOUT2,[X|L],[Z1|L9],[Z1|ZS1],[Z2|ZS2],GOALS,GOALSOUT):- 
                generate_fun(REL,LIST,LINV,LINVOUT,X,Y,Z1,Z2,GOALS,GOALSOUT1), 
                GOALS2=..[',',Y><Z2,GOALSOUT1], 
                generate_fun_args(REL,LIST,LINVOUT,LINVOUT2,L,L9,ZS1,ZS2,GOALS2,GOALSOUT). 
 
 
generate_fun_args(_,_,LINV,LINV,[],[],[],[],GOALS,GOALS). 

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% GENERATE FUN FIELD
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


generate_fun_field(RELATIONS,LISTVARSKEYS,LINV,[inv(C,I,EXPR,X2)|LINVOUT],FIELD,FUN2,X,CON2,GOAL,GOALOUT,VARSKEYS):-  
                        FIELD=inv(C,I,EXPR),    
                        data(C,K), 
                        !,    
                generate_fun_field(RELATIONS,LISTVARSKEYS,LINV,LINVOUT,EXPR,FUN2,X2,CON2,GOAL,GOALOUT,VARSKEYS), 	             
                        generate_template(C,K,[],VARSC,I,X), 
                        CON=..[C|VARSC], 
                        X2=CON.

generate_fun_field(RELATIONS,LISTVARSKEYS,LINV,[inv(F,I,EXPR,X2)|LINVOUT],FIELD,FUN2,X,CON2,GOAL,GOALOUT,VARSKEYS):-   
                        FIELD=inv(F,I,EXPR), 
                        intfun(F,K), 
                        !, 
                        generate_fun_field(RELATIONS,LISTVARSKEYS,LINV,LINVOUT,EXPR,FUN2,X2,CON2,GOAL,GOALOUT,VARSKEYS), 
                        generate_template(F,K,[],VARSF,I,X), 
                        CON=..[F|VARSF], 
                        X2=CON. 
 
generate_fun_field(RELATIONS,LISTVARSKEYS,LINV,LINVOUT,FIELD,FUN,NZ1,NZ1,GOALS,GOALSOUT,VARSKEYS):- 
                        FIELD=..[C|Args], 
                        data(C,_), 
                        !,     
             generate_fun_args_field(RELATIONS,LISTVARSKEYS,LINV,LINVOUT,Args,NewArgs,_,_,GOALS,GOALSOUT,VARSKEYS), 
                        FUN=..[C|NewArgs]. 
 
generate_fun_field(RELATIONS,LISTVARSKEYS,LINV,LINVOUT,FIELD,FUN,NZ1,NZ1,GOALS,GOALSOUT,VARSKEYS):- 
                        FIELD=..[F|Args], 
                        intfun(F,_), 
                        !, 
            generate_fun_args_field(RELATIONS,LISTVARSKEYS,LINV,LINVOUT,Args,NewArgs,_,_,GOALS,GOALSOUT,VARSKEYS), 
                        FUN=..[F|NewArgs]. 

 
generate_fun_field(_,_,LINV,LINV,FIELD,FUN,Z1,Z1,GOALS,GOALS,VARSKEYS):-   
                        atomic(FIELD),              
                        FUN=..[FIELD|VARSKEYS],!.

generate_fun_field(_,_,LINV,LINV,N,N,Z1,Z1,GOAL,GOAL,_). 
 
 
generate_fun_args_field(REL,LIST,LINV,LINVOUT2,[X|L],[Y|L9],[Z1|ZS1],[Z2|ZS2],GOALS,GOALSOUT,VARSKEYS):- 
                generate_fun_field(REL,LIST,LINV,LINVOUT,X,Y,Z1,Z2,GOALS,GOALSOUT1,VARSKEYS), 
                var(Z2),!,  
                generate_fun_args_field(REL,LIST,LINVOUT,LINVOUT2, L,L9,ZS1,ZS2,GOALSOUT1,GOALSOUT,VARSKEYS). 
 
generate_fun_args_field(REL,LIST,LINV,LINVOUT2,[X|L],[Z1|L9],[Z1|ZS1],[Z2|ZS2],GOALS,GOALSOUT,VARSKEYS):- 
                generate_fun_field(REL,LIST,LINV,LINVOUT,X,Y,Z1,Z2,GOALS,GOALSOUT1,VARSKEYS), 
                GOALS2=..[',',Y><Z2,GOALSOUT1],   
                generate_fun_args_field(REL,LIST,LINVOUT,LINVOUT2,L,L9,ZS1,ZS2,GOALS2,GOALSOUT,VARSKEYS). 
 
 
generate_fun_args_field(_,_,LINV,LINV,[],[],[],[],GOALS,GOALS,_). 
 

 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
% GENERATE TEMPLATE 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 
generate_template(_,0,L,L,_,_):-!. 
generate_template(C,K,L,L2,I,X):-I=K,!,K2 is K-1,generate_template(C,K2,[X|L],L2,I,X). 
generate_template(C,K,L,L2,I,Y):-I\==K,!,K2 is K-1,generate_template(C,K2,[_|L],L2,I,Y).		 

 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
% IS FIELD 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 

is_field(RELATIONS,FIELD,FIELDNAME2,LISTVARSKEYS,VARSKEYS):- 
                FIELD=(RELATION,FIELDNAME), 
			  member(RELATION,RELATIONS),
			  is_field(RELATIONS,FIELDNAME, FIELDNAME2,LISTVARSKEYS,VARSKEYS),!.                             

is_field(RELATIONS,FIELD,inv(S,J,FIELDNAME),LISTVARSKEYS,VARSKEYS):- 
                FIELD=inv(S,J,EXPR),
			  is_field(RELATIONS,EXPR, FIELDNAME,LISTVARSKEYS,VARSKEYS),!.                             
 

 
is_field([RELATION|_],FIELD,FIELDNAME,[VARSKEYS|_],VARSKEYS):-
					RELATION=(select _ as RENAMES from _ where _), 
                        dataaux(RELATION,LFIELDS),
                        search_rename(FIELD,RENAMES,LFIELDS,FIELDNAME),!. 


is_field([RELATION|_],FIELD,FIELDNAME,[VARSKEYS|_],VARSKEYS):-
					RELATION=(select _ as RENAMES from _),   
                        dataaux(RELATION,LFIELDS),
                        search_rename(FIELD,RENAMES,LFIELDS,FIELDNAME),!.                        

is_field([RELATION|_],FIELD,FIELDNAME,[VARSKEYS|_],VARSKEYS):-
					RELATION=(select LF from _ where _),    
                        dataaux(RELATION,LFIELDS),
                        search_rename(FIELD,LF,LFIELDS,FIELDNAME),!. 
 
is_field([RELATION|_],FIELD,FIELDNAME,[VARSKEYS|_],VARSKEYS):-
					RELATION=(select LF from _),    
                        dataaux(RELATION,LFIELDS),
                        search_rename(FIELD,LF,LFIELDS,FIELDNAME),!. 

is_field([RELATION|_],FIELD,FIELD,[VARSKEYS|_],VARSKEYS):-  
                        dataaux(RELATION,LFIELDS), 
                        member(FIELD,LFIELDS),!.
                    
is_field([RELATION|_],FIELD,FIELD,[VARSKEYS|_],VARSKEYS):- 
                        database D, 
                        D=..[RELATION|LFIELDS], 
                        member(FIELD,LFIELDS),!. 

is_field([_|RELATIONS],FIELD,FIELDNAME,[_|LISTVARSKEYS],VARSKEYS2):- 
                        is_field(RELATIONS,FIELD,FIELDNAME,LISTVARSKEYS,VARSKEYS2). 
 
 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
% IS KEY 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
 
is_key(RELATIONS,FIELD,FIELDNAME2,LFIELDS,LISTVARSKEYS,RELATION,VARSKEYS):- 
                        FIELD=(RELATION,FIELDNAME), 
                        member(RELATION,RELATIONS),
					is_key(RELATIONS,FIELDNAME,FIELDNAME2,LFIELDS,LISTVARSKEYS,RELATION,VARSKEYS),!. 
 

is_key(RELATIONS,FIELD,FIELDNAME,LFIELDS,LISTVARSKEYS,RELATION,VARSKEYS):- 
                        FIELD=(_,_,EXPR),   
					is_key(RELATIONS,EXPR,FIELDNAME,LFIELDS,LISTVARSKEYS,RELATION,VARSKEYS),!. 
                         


is_key([RELATION|_],FIELD,FIELDNAME,LKEYS,[VARSKEYS|_],RELATION,VARSKEYS):-   
                         RELATION=(select _ as RENAMES from _ where _),
                         keyaux(RELATION,LKEYS), 
					 dataaux(RELATION,LFIELDS),
                         search_rename(FIELD,RENAMES,LFIELDS,FIELDNAME),                       
                         member(FIELDNAME,LKEYS),!.

is_key([RELATION|_],FIELD,FIELDNAME,LKEYS,[VARSKEYS|_],RELATION,VARSKEYS):- 
                          RELATION=(select _ as RENAMES from _), 
					  keyaux(RELATION,LKEYS),
                         dataaux(RELATION,LFIELDS),
                         search_rename(FIELD,RENAMES,LFIELDS,FIELDNAME),                          
                         member(FIELDNAME,LKEYS),!. 

is_key([RELATION|_],FIELD,FIELDNAME,LKEYS,[VARSKEYS|_],RELATION,VARSKEYS):- 
                         RELATION=(select LF from _ where _), 
                         keyaux(RELATION,LKEYS), 
                         dataaux(RELATION,LFIELDS),
                         search_rename(FIELD,LF,LFIELDS,FIELDNAME),                         
                         member(FIELDNAME,LKEYS),!.

is_key([RELATION|_],FIELD,FIELDNAME,LKEYS,[VARSKEYS|_],RELATION,VARSKEYS):- 
                         RELATION=(select LF from _), 
                         keyaux(RELATION,LKEYS), 
                         dataaux(RELATION,LFIELDS),
                         search_rename(FIELD,LF,LFIELDS,FIELDNAME),                         
                         member(FIELDNAME,LKEYS),!.            
 
is_key([RELATION|_],FIELD,FIELD,LFIELDS,[VARSKEYS|_],RELATION,VARSKEYS):- 
                        keyaux(RELATION,LFIELDS), 
                        member(FIELD,LFIELDS),!.

 is_key([RELATION|_],FIELD,FIELD,LFIELDS,[VARSKEYS|_],RELATION,VARSKEYS):- 
                        key K, 
                        K=..[RELATION|LFIELDS], 
                        member(FIELD,LFIELDS),!.
 
is_key([_|RELATIONS],FIELD,FIELDNAME,LFIELDS,[_|LISTVARSKEYS],RELATION2,VARSKEYS2):-   
                is_key(RELATIONS,FIELD,FIELDNAME,LFIELDS,LISTVARSKEYS,RELATION2,VARSKEYS2). 


 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% GO, MAIN PROGRAM
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
  
go:- 
       cgi_get_form(Arguments),
       format('~n~n------------------------------------------------~n~n',[]),
       format('WELCOME TO THE INDALOG PROTOTYPE~n~n',[]),
       format('DEVELOPED IN THE UNIVERSITY OF ALMERIA-SPAIN~n~n',[]),
       format('2004-2006~n~n',[]),
       format('CONTACT jalmen@ual.es~n~n',[]),
       format('------------------------------------------------~n~n',[]), 
       format('Running Indalog Prototype, Please be Patient~n~n',[]),  
       getenv("REMOTE_ADDR",Directorio),        
       chdir('../../DATA'), 
       catch(create_dir(Directorio),_,(delete_parcial('parcial'),create_dir(Directorio))), 
       chdir(Directorio),         
       create_internet_file(Arguments,Goal),         
       [localcode],                   
       atom_to_term(Goal,GoalA,ListVars),         
       catch(answer_goal(GoalA,ListVars),_,execution_no). 
  
go2:- 
       cgi_get_form(Arguments),
       format('~n~n------------------------------------------------~n~n',[]),
       format('WELCOME TO THE INDALOG PROTOTYPE~n~n',[]),
       format('DEVELOPED IN THE UNIVERSITY OF ALMERIA-SPAIN~n~n',[]),
       format('2004-2006~n~n',[]),
       format('CONTACT jalmen@ual.es~n~n',[]),
       format('------------------------------------------------~n~n',[]), 
       format('Running Indalog Prototype, Please be Patient~n~n',[]),  
       getenv("REMOTE_ADDR",Directorio),        
       chdir('../../DATA'), 
       catch(create_dir(Directorio),_,(delete_parcial('parcial'),create_dir(Directorio))), 
       chdir(Directorio),         
       create_internet_file(Arguments,Goal),         
       [localcode],                   
       atom_to_term(Goal,GoalA,ListVars),         
       catch(answer_goal2(GoalA,ListVars),_,execution_no).
     
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% ANSWER_GOAL
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

answer_goal(GoalA,ListVars):-goal(GoalA),!,format('Yes~n~n~==>~w~?~n~n',[ListVars]).
answer_goal(_,_):-format('No~n~n',[]).

answer_goal2(GoalA,_):-GoalA=..[select,L1,L2,L3],
			GoalB=..[select,L1,L2,L3,L],
			findall(L,call(GoalB),RES),!,
			format('Yes~n~n~==>~w~?~n~n',[RES]).
answer_goal2(_,_):-format('No~n~n',[]).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% EXECUTION NO
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

execution_no:-format('Wrong Goal~n~n',[]).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% CREATE INTERNET FILE
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
          
create_internet_file([_,A2,A3],Goal):- 
        A2 =..[_|[Code]], 
        A3 =.. [_,Goal], 
        open('localcode.pl',write,File), 
        write(File,Code), 
        close(File).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% CREATE DIR
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
 
create_dir(Directorio):- 
       exists_directory(Directorio),!, 
       chdir(Directorio), 
       delete_files(Directorio), 
       make_directory(Directorio). 
 
create_dir(Directorio):- 
       make_directory(Directorio). 

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% DELETE FILES
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 
delete_files([]). 
 
delete_files([X|L]):- 
       delete_file(X), 
       delete_files(L). 
 
delete_files(Directorio):- 
       expand_file_name(*,L), 
       delete_files(L), 
       chdir(..), 
       delete_directory(Directorio). 
 
 
:-style_check(-discontiguous).
:-dynamic_pred. 
:-include(prelude). 
 
 
 
 
  
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
