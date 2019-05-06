% Example of functional logic database INDALOG


database employer(name,address,number,phone).
database employer_age(name,age).
key employer(name).
key employer_age(name).

datatype ok ::= ok.
datatype addresstype ::= add(number_st,flattype).
datatype flattype ::= flat(number_fl,letter).
datatype letter ::= a | b | c | d | e.
datatype person ::= peter  | mark | frank.
datatype number_st ::= first | second | third | fourth | fifth.
datatype number_fl ::= '1' | '2' | '3' | '4' | '5'.
 
employer :: person -> ok. 

employer(peter):=ok.
employer(mark):=ok.
employer(frank):=ok.

employer_age :: person -> ok.

employer_age(peter):=ok.
employer_age(mark):=ok.
employer_age(frank):=ok.

address :: person -> addresstype.

address(peter):=add(fifth,flat(4,a)).
address(mark):=add(second,flat(5,b)).
address(frank):=add(first,flat(3,c)).

age :: person -> number.

age(peter):=age(mark).
age(mark):=19.
age(frank):=29.


number :: person -> number.

number(frank):=29.
number(peter):=14.
number(mark):=8.

phone :: person -> number.

phone(peter):=238987.
phone(mark):=123456.
phone(frank):=198976.

bonus :: person -> number.

bonus(peter):=1.
bonus(frank):=2.
