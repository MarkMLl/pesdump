# pesdump
A dump utility for PES files as used by Brother embroidery machines

This is a no-frills program to parse and dump the content of a PES file as
described at https://edutechwiki.unige.ch/en/Embroidery_format_PES with no
attempt at converting it into a machine-readable format. The initial impetus
was having a file which crashed a Brother Innovis-97E when it was loaded,
this appeared (and with the help of this program is now confirmed) to be
because it contained pause commands but the ability to compare a troublesome
file against a good one would have been useful.

It is written in the style of a conventional "recursive descent" parser,
without lookahead but with limited backtracking, and is intentionally naive
to allow it to be read and possibly modified by non-specialists. Assume that
like most Pascal programs the highest-level elements (i.e. the description
of the overall file, the description of the standard header etc.) are at the
bottom of this program unit.  Copyright (c) 2020 Mark Morgan Lloyd

The principal reference for factual information used while writing this
program was from EduTechWiki which is subject to the CC BY-NC-SA Licence.
The above document cites Trevor Adams's "Frno7's Wiki" as its major source,
this explicitly uses GFDLv1.3 and GPLv3. Trevor Adams cites Linus Torvalds's
PesConvert program which is not accompanied by a licence indication but is
hosted by kernel.org and as such it is reasonable to assume that the same
license (GPLv2 with no "or any later version" clause) is intended to apply.
Torvalds cites a PHP script by Robert Heel which is covered by GPLv2 with an
"any later version" clause, this indirectly cites Trevor Adams (GPLv3).

Because of this mixed heritage, and taking into account that my use of the
EduTechWiki document (hence other cited material) has been restricted to
factual information plus some type and field names, and noting that Torvalds
omits an explicit license choice, I think it appropriate that this program
should be licensed using GPLv3.
