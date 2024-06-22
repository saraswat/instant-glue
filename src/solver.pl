
% T |- T
h(SG-EG =- T):-
    T \= (_ -> _),
    T \= (_*_),
    T \= 1,
    select(T, SG, EG).


% |- 1
h(X-X =- 1). 


% Gamma |- T
% -------------
% Gamma, 1 |- T
h(SG-EG =- T):-
    once((select(1, SG, IG), h(IG-EG =- T))).

% Gamma, T1,T2 |- T 
% -----------------
% Gamma, T1*T2 |- T
h( SG-EG =- T):-
    once((select(T1*T2, SG, IG),
	  h([T1, T2 | IG] - EG =- T)
	 )
	).

% Gamma1 |- T1   Gamma2 |- T2 
% ------------------------------
% Gamma1, Gamma2 |- T1*T2
h( SG-EG =- T1 * T2) :-
   h(SG-IG =- T1),
   h(IG-EG =- T2).

% Gamma, T |- S
% ----------------
% Gamma |- T -> S
h( SG-EG =- T->S) :-
    h( [T|SG]-EG =- S),

    % T must be used up in the proof of S, cannot leak out through
    % the not used terms.
   not(identmember(T, EG)).

%  Gamma1 |- U  Gamma2, V |- T
% -------------------------------------------
% U ->V, Gamma1, Gamma2 |- T 
h(SG - EG =- T) :-
    T \= (_ -> _),
    T \= (_ * _),
    select(U->V, SG, IG1),  % select an implication to discharge
    h(IG1-IG2 =- U),

    % IG2, the residual terms, must all exist in IG1.
    % Cannot contain new elements produced by discharging ->, e.g. the v(X):V we introduce
    % in the next line.
    once(subseq(IG2, IG1)),
    h([V| IG2]-EG =- T).
