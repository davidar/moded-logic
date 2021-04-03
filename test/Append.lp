append [] x x.
append (ah:t) b (ch:tb) :- ah = ch, append t b tb.
