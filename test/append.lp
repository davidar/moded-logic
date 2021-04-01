append [] xs xs.
append (ah : at) b (ch : ct) :- ah = ch, append at b ct.
append a b c abc :-
    append a b ab, append ab c abc.
reverse [] [].
reverse (h : t) l :- reverse t r, append r (h : []) l.
