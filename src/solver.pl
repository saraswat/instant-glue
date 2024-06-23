

% Gamma |- T
% -------------
% Gamma, 1 |- T

% Gamma, T1,T2 |- T 
% -----------------
% Gamma, T1*T2 |- T

h(SG-EG =- T):-
    simplify_sequent(SG, SG1),
    h1(SG1-EG =- T).

% T |- T
h1(SG-EG =- T):-
    pred(T),
    select(T, SG, EG).

% |- 1
h1(X-X =- 1). 
% Gamma1 |- T1   Gamma2 |- T2 
% ------------------------------
% Gamma1, Gamma2 |- T1*T2
h1( SG-EG =- T1 * T2) :-
   h(SG-IG =- T1),
   h(IG-EG =- T2).

% Gamma, T |- S
% ----------------
% Gamma |- T -> S
h1( SG-EG =- T->S) :-
    h( [T|SG]-EG =- S),

    % T must be used up in the proof of S, cannot leak out through
    % the not used terms.
    once(identsubset(EG, SG)).


%  Gamma1 |- U  Gamma2, V |- T
% -------------------------------------------
% U ->V, Gamma1, Gamma2 |- T 
h1(SG - EG =- T) :-
    pred1(T),
    select(U->V, SG, IG1),  % select an implication to discharge
    h(IG1-IG2 =- U),

    % IG2, the residual terms, must all exist in IG1.
    % Cannot contain new elements produced by discharging ->, e.g. the v(X):V we introduce
    % in the next line.
    once(identsubset(IG2, IG1)),
    h([V| IG2]-EG =- T).
