% INDALOG prelude

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% PRELUDE PROLOG
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

data(X,0):-integer(X).
data(X,0):-float(X).
data(X,0):-string(X).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%
   
datatype ok ::= ok.
datatype bool ::= true | false.
datatype nat ::= 0 | s(nat).    
datatype list(A) ::= nil | (A : list(A)).
 
type [A] ::= list(A).

%%%%%%%%%%%%%%%%%%%%%%
% bool
%%%%%%%%%%%%%%%%%%%%

&& :: bool -> bool -> bool.

true && X := X.
false && _ := false.

# :: bool -> bool -> bool.

true # _ := true.
false # X := X.

if_then_else :: bool -> A -> A -> A.

if_then_else(true,X,_):=X.
if_then_else(false,_,Y):=Y.

otherwise :: boolean.

otherwise := true.

not :: _ -> bool.

not(true) := false.
not(false) := true.

%%%%%%%%%%%%%%%%%%%%%%
% list
%%%%%%%%%%%%%%%%%%%%%


head :: [A] -> A.

head(X:_) := X.

tail :: [A] -> A.

tail(_:L) := L.

++ :: [A] -> [A] -> [A].

nil++L:=L.
(X:L)++L2:=X:(L++L2).

member :: A -> [A] -> bool.

member(X,Y:_):=true :- eq(X,Y)><true.
member(X,_:L):=member(X,L).

%%%%%%%%%%%%%%%%%%%%%%%
% int
%%%%%%%%%%%%%%%%%%%%%%

eq :: A -> A -> bool.

eq(X,Y):=true :- X==Y><true.
eq(X,Y):=false :-  X\==Y><true.

is :: float -> float -> bool.

X is Y := true :- X is Y.

+ :: float -> float -> float.

X+Y:=Z :- Z is X+Y.

- :: float -> float -> float.

X-Y:=Z :- Z is X-Y.

* :: float -> float -> float.

X*Y:=Z :- Z is X*Y.

/ :: float -> float -> float.

X/Y:=Z :- Z is X/Y.  

mod :: int -> int -> int.

X mod Y:=Z :- Z is X mod Y.  

div :: int -> int -> int.

X div Y:=Z :- U is X mod Y, Z is (X-U)/Y.

> :: float -> float -> float.

X>Y := true :- X>Y.

< :: float -> float -> float.

X<Y := true :- X<Y.
 
>= :: float -> float -> float.

X>=Y := true :- X>=Y.
  
=< :: float -> float -> float.

X=<Y := true :- X=<Y.

== :: A -> A -> bool.

X==Y := true :-  X==Y.
 
\== :: A -> A -> bool.

X\==Y := true :-  X\==Y.



  