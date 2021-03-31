append a b c :-
    a = [], b = c;
    a = ah : at, c = ch : ct, ah = ch, append at b ct.
append a b c abc :-
    append a b ab, append ab c abc.
reverse a l :-
    a = [], l = [];
    a = h : t, reverse t r, append r (h : []) l.
