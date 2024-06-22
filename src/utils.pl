:- [ops].

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% Auxiliary predicates

identmember(X, [Y|YS]) :- X == Y ; identmember(X, YS).

%% subseq(A, Bs):-
%% Every element of A exists in Bs. A should be unmodified after this.
subseq([], _).
subseq([A|Ar], B):-
    identmember(A, B),
    subseq(Ar, B).

%% Simplification of proof terms.
simplify(v(X), v(X)).
simplify(A, A):- % constants
    functor(A, _, 0).

simplify(let(X=E, Target), Result):-
    simplify(E, E1),
    simplify(Target, Target1),
    substitute(E1, X, Target1, Result).

simplify(A@B, Result):-
    simplify(A, A1),
    simplify(B, B1),
    % beta reduction
    once((A1 = Var\Value, substitute(B1, Var, Value, Result);
	  Result = A1@B1)).    

simplify(Var\Term, Result):-
    simplify(Term, Term1),
    % eta reduction    
    once((Term = Z@v(Var1), Var1==Var, Result=Z;
          Result = Var\Term1)).
    %Result = Var\Term1.

simplify(fst(X), Y):-
    simplify(X, X1),
    once((X1 = (A,_), Y=A; Y=fst(X1))).

simplify(snd(X), Y):-
    simplify(X, X1),
    once((X1 = (_,B), Y=B; Y=snd(X1))).

simplify((A,B), (A1,B1)):-
    simplify(A, A1),
    simplify(B, B1).

% substitute E for X in Y yielding R.
substitute(_E, _X, Const, R):-
    functor(Const, _, 0),
    R = Const.

substitute(E, X, v(Y), R):-
    once(((X == Y, R=E); R=v(Y) )).

substitute(E, X, fst(Y), fst(Z)):-
    substitute(E, X, Y, Z).

substitute(E, X, snd(Y), snd(Z)):-
    substitute(E, X, Y, Z).

substitute(E, X, (A,B), (A1, B1)):-
    substitute(E, X, A, A1),
    substitute(E, X, B, B1).

substitute(E, X, A@B, A1@B1):-
    substitute(E, X, A, A1),
    substitute(E, X, B, B1).
     
substitute(E, X, let(A=B,C), Result):-
    % Avoid variable capture. Gen a new variable for A
%    substitute(v(A1), A, C, C1),
    substitute(B, A, C, C2),
    substitute(E, X, C2, Result).

substitute(E, X, Y\Term, Y1\Term2):-
    substitute(v(Y1), Y, Term, Term1), % Generate a new var Y1
    substitute(E, X, Term1, Term2).
    


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

paren(A -> B, [A1-> B1]):- paren(A, A1), paren(B, B1).
paren(A * B, [A1 * B1]):- paren(A, A1), paren(B, B1).
paren(A, A):- A \= (_ -> _), A \= (_*_).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
pretty_print(Term):-
     \+ \+ ( numbervars(Term, 0, _, [singletons(true)]),
            format('~W', [Term, [numbervars(true)]])
           ),
     nl.

readings(M,J) :-
   writeln('Judgement:'), tab(1), pretty_print(J),  % portray_clause(J)
   writeln('Readings:'), tab(1), J, tab(1), pretty_print(M), fail; true.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
