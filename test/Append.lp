append [] b b.
append (h:t) b (h:tb) :- append t b tb.
append a b c abc :-
    append a b ab, append ab c abc.
reverse [] [].
reverse (h:t) l :- reverse t r, append r [h] l.
palindrome a :- reverse a a.
duplicate a b :- append a a b.
