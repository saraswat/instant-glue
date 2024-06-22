:- set_prolog_flag(answer_write_options, [quoted(true), portrayed(true), max_depth(100), spacing(next_argument)]).
:- op(597, xfy, user:( \ )). % lambda abstraction
:- op(598, yfx, user:( @ )).  % lambda application (in meaning term space)
:- op(599, xfy, user:( -> )). % linear implication -o
:- op(649, xfx, user:( =- )). % |- 
