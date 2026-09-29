my $Q = qr/(?:(?:SailStdpp\.)?(?:Values|Operators_mwords)\.)?/;
my $N = qr/(?:get_word|to_word|with_word'?)(?![\w'])/;
my $T = qr/\b$Q$N/;
# term-level identity applications: (get_word X) / (to_word X) -> X
s/\($Q(?:get_word|to_word)\s+(\((?:[^()]++|(?1))*\))\)/$1/g;
# whole tactic steps that only unfold/reduce the wrappers
s/\bunfold\s+$T(?:\s*,\s*$T)*\s+in\s+[\w']+\s*\.[ \t]*//g;
s/\b(?:unfold|cbn|cbv|simpl|lazy)\s+(?:\[\s*)?$T(?:[\s,]+$T)*\s*\]?\s*([.;])/idtac$1/g;
# list elements (lists may span lines)
s/,\s*$T//g;
s/$T\s*,\s*//g;
s/(?<=\s)$T(?=[\s\]])[ \t]?//g;
s/\[\s*$T\s+/[/g;
