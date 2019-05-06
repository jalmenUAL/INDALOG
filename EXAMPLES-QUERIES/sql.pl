%%%%%%%%%%%%%% EMPLOYER EXAMPLES

?- evs select [name] from [employer].
?- evs select [name] from [employer_age] where [age><19].
?- evs select [name,number] from [employer] where [number><8].
?- evs select [bonus(name)] from [employer].
?- evs select [inv(bonus,1,2)] from [employer].
?- evs select [(employer,name),age] from [employer,employer_age] where [(employer,name)=(employer_age,name)].
?- evs select [d1] from [select [a1,b1] as [e1,d1] from [select [name,address] as [a1,b1] from [employer]]].
?- evs select [a1,c1] from [select [name] as [a1] from [employer],select [name,age] as [b1,c1] from [employer_age]] where [a1=b1].
?- evs select [inv(bonus,1,1)] from [employer].
?- evs select [inv(add,1,address),inv(add,2,address)] from [employer].
?- evs select [inv(add,1,address),inv(add,2,address)] from [employer] where[name=peter].

%%%%%%%% POINTS EXAMPLES Warning: Some of them have infinite answers!

?- evs select [next(coord,north)] from [point] where [coord=(0,0)].
?- evs select [orig,orient,next(orig,orient)] from [line] where [orig=(0,0),orient=north]. 
?- evs select [coord] from [point].
?- evs select [orig] from [line].
?- evs select [orig,orient] from [line].
?- evs select [coord] from [point].
?- evs select [next(coord,north)] from [point].
?- evs select [orig,orient] from [line].
?- evs select [orig] from [line] where [orient=north].
?- evs select [inv(',',1,a1),inv(',',2,a1)] from [select [ocoord,east] as [a1,b1] from [point]].
?- evs select [inv(member,1,true)] from [line] where [orig=(0,0),orient=north,inv(member,2,true)><list_points].
?- evs select [inv(member,1,true)] from [line] where [orig=(0,0),inv(member,2,true)><list_points].
?- evs select [inv(s,1,b1)] from [select [inv(',',1,ocoord)] as [b1] from [point]].






  
 
 