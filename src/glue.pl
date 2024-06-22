% Instant Glue
% Version: 1.5
% (c) 2024 Vijay Saraswat
% Date: 17 June 2024

% Version 1.4
% Author: Miltiadis Kokkonidis
% Date: 9 June 2009
% (c) 2009 Miltiadis Kokkonidis

% Supported by Social Sciences and Humanities Research Council of Canada, 
% Standard Research Grant #410-2006-1650 to Ash Asudeh.
%
% Licence Agreement:
%
% Permission is granted to use and distribute this code as is.  Any code derived
% from the code herein must be publically available in source code form, be
% available free of charge, and carry the same licence and disclaimer.  It
% should both clearly acknowledge the current work, as well as provide a
% reasonably clear statement of the ways in which the derived work differs from
% the original work.  While the acknowledgements section may differ, mention
% should be made to both the AHRC (UK) and the SSHRC (Canada) grants that
% made the development of this software possible.  Licence to use this software
% is conditional upon acceptance of the disclaimer below.
%
% Disclaimer:
%
% This software comes as-is with no warranties of any kind, express or implied.
% The user assumes full responsibility for its use and is solely liable for
% resulting damages, if any.
%
% Versions and acknowledgesments:
%
% Versions 1.0, 1.1 and 1.2 were developed during the course of the author's
% DPhil studies at the University of Oxford supported by AHRC grant 2005/118667.
% The author wishes to thank his thesis advisor, Mary Dalrymple, for her
% support, as well as Maya Bangerter and Simon Clematide, for developing tools
% for Instant Glue.
%
%
% Version 1.4 is the first publically available version of Instant Glue.  Unlike
% earlier versions it supports not only linear implication, but also the
% tensor.  As a result, it is the first version of Instant Glue that directly
% supports analyses involving products such as the basic Glue analysis of
% anaphora and the Glue analysis of resumption. Work towards versions 1.3 and
% 1.4 was supported by  the Social Sciences and Humanities Research Council of
% Canada, Grant #410-2006-1650.  The author wishes to thank Ash Asudeh, the
% grant's Principal Investigator, for encouraging and funding this project.

% Version 1.5 (c) Vijay Saraswat, Language Machines Corporation, 2024
% Redone as follows:
% 1. v 1.4 does not actually handle all formulas built from (x, ->). In particular it
%   discharges all conditions A1,.., An in an implication A1 -> ... An -> A  all together.
%   This cannot handle the licensing technique we are developing. So the "endsIn" heuristic
%   is not (cannot be) used.
%   We go back and restructure the proof procedure to follow the sequent formulation of the logic.
%   The proof procedure has a number of heuristics, e.g. eagerly decomposing * on the Right.
%   I believe focusing rules can be used to justify this. (TBD.)
%   
% 2. Now handles the constant 1. (needed for licensing).
% 3. Introduce simplification rules for meaning terms (beta and eta reduction).
% 4. TBD: simplification of let's.
% 5. Changed the representation of meaning terms to make them easier to read.


:- [ops, utils].

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% glue(Term, Proof):-
%% Run the solver for Term, producing in Proof a representation of the proof tree

glue(Term):- glue(Term, _).
glue( G =- M:T, Proof ) :-  g( G - [] =- M1:T, Proof ), simplify(M1, M).

%%% Main proof procedure
% g(SG-EG =- Consequent, ProofTree) :-
%  there is a proof of Consequent from SG (with left over formulas in EG),
%  with the proof tree having the structure given in ProofTree.
%  We keep ProofTree because it simplifies debugging.

% T |- T
g((SG-EG =- X:T), id(T)):-
    T \= (_ -> _),
    T \= (_*_),
    T \= 1,
    select(X:T, SG, EG).


% |- 1
g( (X-X =- _:1), r(1)). 


% Gamma |- T
% -------------
% Gamma, 1 |- T
g( (SG-EG =- M:T), lt(1,P)):-
    once((select(_:1, SG, IG), g(IG-EG =- M:T,P))).

% Gamma, T1,T2 |- T 
% -----------------
% Gamma, T1*T2 |- T
g( (SG-EG =- M:T), lt(P, Proof)) :-
    once((select(P:T1*T2, SG, IG),
	  g(([fst(P):T1, snd(P):T2 | IG] - EG =- M:T), Proof)
	 )
	).

% Gamma1 |- T1   Gamma2 |- T2 
% ------------------------------
% Gamma1, Gamma2 |- T1*T2
g(( SG-EG =- (M1,M2):T1 * T2), r((M1,M2), P1, P2) ) :-
   g( (SG-IG =- M1:T1), P1),
   g( (IG-EG =- M2:T2), P2).

% Gamma, T |- S
% ----------------
% Gamma |- T -> S
g(( SG-EG =- (X\M): T->S), r(X\M, P )) :- 
    %!,
    g( [v(X):T|SG]-EG =- M:S, P),

    % T must be used up in the proof of S, cannot leak out through
    % the not used terms.
   not(identmember(v(X):T, EG)).

%  Gamma1 |- U  Gamma2, V |- T
% -------------------------------------------
% U ->V, Gamma1, Gamma2 |- T 
g( (SG - EG =- let(X=(A@Um),E):T), lt(let(X=(A@Um), E),P1,P2)) :-
    T \= (_ -> _),
    T \= (_ * _),
    select(A:U->V, SG, IG1),  % select an implication to discharge
    g((IG1-IG2 =- Um:U), P1),

    % IG2, the residual terms, must all exist in IG1.
    % Cannot contain new elements produced by discharging ->, e.g. the v(X):V we introduce
    % in the next line.
    once(subseq(IG2, IG1)),
    g(([v(X):V| IG2]-EG =- E:T), P2).


example(M) :-
 bagof(B,
       C^(glue([everyone:l(l2)->(l(l1)->e(e1)->t(D))->t(D),
	      someone:l(l1)->(l(l2)->e(e2)->t(E))->t(E),
	      likes:e(e1)->e(e2)->t(f),
	      lic1:l(l2),
	      lic2:l(l2)->1]=-C:t(f)), simplify(C, B)),
       M).

% Returns 21 solutions, all with everyone outscoping someone.
