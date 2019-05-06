% Example of Spatial Problem in Indalog

database point(coord).
key point(coord).

database line(orig,orient,set_points,list_points).
key line(orig,orient).
  
datatype ok ::= ok.
datatype bool ::= true | false.
datatype nat ::= 0 | s(nat). 
datatype orientation ::= south | north | east | oest.
datatype list(A) ::= nil | (A : list(A)).
datatype pair(A,B) ::= (A,B).

type [A] ::= list(A).

point :: pair(nat,nat) -> ok.

point((0,0)):=ok.
point((s(X),Y)):=point((X,Y)).
point((X,s(Y))):=point((X,Y)).

line :: pair(nat,nat) -> orientation -> ok.

line(X,north) | point(X)><ok := ok.
line(X,east) | point(X)><ok := ok.
line(X,south) | point(X)><ok := ok.
line(X,oest) | point(X)><ok := ok.

set_points :: pair(nat,nat) -> orientation -> pair(nat,nat).

set_points(X,_):=X.
set_points(X,Z):=set_points(next(X,Z),Z).

list_points :: pair(nat,nat) -> orientation -> [pair(nat,nat)].

list_points(X,Z):= X : list_points(next(X,Z),Z).

next :: pair(nat,nat) -> orientation -> pair(nat,nat).

next((X,Y),north):=(X,s(Y)).
next((X,s(Y)),south):=(X,Y).
next((X,Y),east):=(s(X),Y).
next((s(X),Y),oest):=(X,Y).

member :: pair(nat,nat) -> [pair(nat,nat)]  -> bool.

member(X,Y:_) | eqp(X,Y)><true := true.
member(X,_:L):=member(X,L). 

eq :: nat -> nat -> bool.

eq(0,0):=true.
eq(s(X),s(Y)):=eq(X,Y).

eqp :: pair(nat,nat) -> pair(nat,nat) -> bool.

eqp((X,Y),(Z,T)) | eq(X,Z)><true, eq(Y,T)><true := true.

ocoord :: pair(nat,nat).

ocoord:=(0,0).
ocoord:=(s(0),s(0)).


         


