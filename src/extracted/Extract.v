Require Extraction.
Require ExtrOcamlIntConv.
Require ExtrOcamlBasic.
Unset Universe Checking.
Require Mem.SC.
Require Mem.TSO.
Require Mem.PS.
Require Mem.Interp.
Require Mem.Examples.

Extraction Language OCaml.
Extraction Blacklist String List Char Core Z.

Cd "extracted".
Recursive Extraction Library ExtrOcamlIntConv.
Recursive Extraction Library ExtrOcamlBasic.
Recursive Extraction Library SC.
Recursive Extraction Library TSO.
Recursive Extraction Library PS.
Recursive Extraction Library Interp.
Recursive Extraction Library Examples.
Cd "..".
