append(A,B,C) :-
    A = [], B = C;
    A = [AH | AT], C = [CH | CT], AH = CH, append(AT, B, CT).
append(A,B,C,ABC) :-
    append(A,B,AB), append(AB,C,ABC).
reverse(A,L) :-
    A = [], L = [];
    A = [H | T], reverse(T, R), N = [], S = [H | N], append(R, S, L).
