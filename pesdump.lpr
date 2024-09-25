(* FPC 2.6.0 FPC 2.6.0 FPC 2.6.0 FPC 2.6.0 FPC 2.6.0 FPC 2.6.0 FPC 2.6.0 FPC 2. *)

program PesDump;

(* This is a no-frills program to parse and dump the content of a PES file as   *)
(* described at https://edutechwiki.unige.ch/en/Embroidery_format_PES with no   *)
(* attempt at converting it into a machine-readable format. The initial impetus *)
(* was having a file which crashed a Brother Innovis-97E when it was loaded,    *)
(* this appeared (and with the help of this program is now confirmed) to be     *)
(* because it contained pause commands but the ability to compare a troublesome *)
(* file against a good one would have been useful.                              *)
(*                                                                              *)
(* It is written in the style of a conventional "recursive descent" parser,     *)
(* without lookahead, and is intentionally naive to allow it to be read and     *)
(* possibly modified by non-specialists. Assume that like most Pascal programs  *)
(* the highest-level elements (i.e. the description of the overall file, the    *)
(* description of the standard header etc.) are at the bottom of this program   *)
(* unit.                                Copyright (c) 2020 Mark Morgan Lloyd    *)

(********************************************************************************)
(*                                                                              *)
(* The principal reference for factual information used while writing this      *)
(* program was from EduTechWiki which is subject to the CC BY-NC-SA Licence.    *)
(* The above document cites Trevor Adams's "Frno7's Wiki" as its major source,  *)
(* this explicitly uses GFDLv1.3 and GPLv3. Trevor Adams cites Linus Torvalds's *)
(* PesConvert program which is not accompanied by a licence indication but is   *)
(* hosted by kernel.org and as such it is reasonable to assume that the same    *)
(* license (GPLv2 with no "or any later version" clause) is intended to apply.  *)
(* Torvalds cites a PHP script by Robert Heel which is covered by GPLv2 with an *)
(* "any later version" clause, this indirectly cites Trevor Adams (GPLv3).      *)
(*                                                                              *)
(* Because of this mixed heritage, and taking into account that my use of the   *)
(* EduTechWiki document (hence other cited material) has been restricted to     *)
(* factual information plus some type and field names, and noting that Torvalds *)
(* omits an explicit license choice, I think it appropriate that this program   *)
(* should be licensed using GPLv3.

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <https://www.gnu.org/licenses/>.
                                                                                *)
(*                                                              MarkMLl         *)
(*                                                                              *)
(********************************************************************************)

// Current state: supports PES v1, some support for other versions roughed in
// but inoperative.

{$mode objfpc}{$H+}

uses
  Classes, SysUtils, PatchAndIO, MidlevelIO,
                        StrUtils, DateUtils;    (* Last two units are optional  *)

(* If FPC version 3.2.0 or later is used, it is able to validate that error     *)
(* messages correctly identify what function was being executed at the time:    *)
(* this is important since it includes parsing rules where an error indicates   *)
(* either something wrong in the input file or a flaw in the program. Versions  *)
(* of FPC predating 2.2.4 lack the FPC_FULLVERSION predefined, so cannot fail   *)
(* gracefully when they try to determine whether the CURRENTROUTINE expansion   *)
(* is available. Other factors mandate that in practice FPC older than 2.6.0    *)
(* will be unable to compile this source file without significant modification. *)

{$undef HAS_CURRENTROUTINE     }
{$if FPC_FULLVERSION >= 030200 }        (* Requires FPC 2.2.4 minimum           *)
{$define HAS_CURRENTROUTINE    }        (* Requires FPC 3.2.0 minimum           *)
{$assertions on                }        (* Make sure name checks are operative  *)
{$endif FPC_FULLVERSION        }

(* State variables: rule stack for diagnostics, counters etc.                   *)

var
  params: TStringList= nil;
  hasOptions: boolean= false;
  hasCommands: boolean= false;
  pesIn, pesOut: file;
  ruleStack: TStringList;
  poppedRule: string= '[Empty]';

(* Counters and min/max sizes output at program termination.                    *)

  countPesStitchesNormal: longword= 0;
  countPesStitchesJump: longword= 0;
  countPesStitchesOther: longword= 0;
  countPesStitchesTotal: longword= 0;
  countPesColours: longword= 0;
  minPesX: longint= 0;
  maxPesX: longint= 0;
  minPesY: longint= 0;
  maxPesY: longint= 0;
  countPecHalfstitches: longword= 0;
  countPecColourChanges: longword= 0;
  countPecPauseCommands: longword= 0;
  countPecTrimCommands: longword= 0;
  countPecJumpCommands: longword= 0;
  minPecX: longint= 0;
  maxPecX: longint= 0;
  minPecY: longint= 0;
  maxPecY: longint= 0;


(********************************************************************************)
(*                                                                              *)
(* Sundry code to help diagnostics.                                             *)
(*                                                                              *)
(********************************************************************************)


(* Push the name of the current rule onto a stack.
*)
procedure pushRule(const rule: string);

begin
  ruleStack.Append(rule)
end { pushRule } ;


(* Pop the top of the rule name stack. The popped string is saved since it will
  be needed if the file ends prematurely.
*)
function popRule(): string;

var
  i: integer;

begin
  result := '';
  i := ruleStack.Count - 1;
  if i >= 0 then begin
    result := ruleStack[i];
    poppedRule := result;
    ruleStack.Delete(i)
  end else begin
    result := '';                       (* Empty string indicates empty stack   *)
    poppedRule := '[Rule stack underflow]'
  end
end { popRule } ;


(* Peek at the rule at the top of the stack.
*)
function peekRule(): string;

var
  i: integer;

begin
  result := '';
  i := ruleStack.Count - 1;
  if i >= 0 then
    result := ruleStack[i]
end { peekRule } ;


(* Pretty-print a header for the start of rule execution.
*)
procedure header;

var
  i: integer;
  hdr, underline: string;

begin
  hdr := '';
  for i := 0 to ruleStack.Count - 1 do begin
    if hdr <> '' then
      hdr += Arrow;
    hdr += ruleStack[i]
  end;
  underline := '';

// "Temporary" hack here to allow for multibyte UTF-8 arrows.

  i := Length(hdr);
{$ifdef VER3 }
  i -= 2 * (ruleStack.Count - 1);
{$endif VER3 }
  while Length(underline) <> i do
    underline += '-';
  WriteLn(hdr);
  WriteLn(underline)
end { header } ;


(********************************************************************************)
(*                                                                              *)
(* Rules defining the file format (start reading at the end of this section).   *)
(*                                                                              *)
(********************************************************************************)

(* If a rule returns false then it indicates that it doesn't match the input,   *)
(* and broadly speaking it is valid for the caller to try another rule; in this *)
(* case the rule name is popped off the stack used for diagnostic output. If a  *)
(* rule raises an exception then no recovery is possible, the rule name is left *)
(* on the stack and will appear in diagnostic output. The working principle of  *)
(* the parser is that on exit from the top-level rule (pes_file) the rule name  *)
(* stack will be empty and the input file will be at EOF.                       *)

var
  pecSectionByteOffset: longword= $ffffffff;
  waitingForPec: boolean= false;
  segmentBlockCount: longword= $ffffffff;
  cSewSegBlockCount: longword= $ffffffff;
  pecThumbnailByteOffset: longword= $ffffffff;
  thumbnailWidth: longword= 0;          (* In bytes, 8x pixels per byte         *)
  thumbnailHeight: longword= 0;         (* In rows/pixels                       *)
  thumbnailColours: longword= 0;        (* Zero is 1 colour, 0xff is no colour  *)


(* Parse the PEC stitchlist section.
*)
function pec_stitchListSubsection(): boolean;

const
  thisName= 'pec_stitchListSubsection()';

var
  backtrack: int64;
  count, colour, ignoreOrdinates: integer;
  stitch: PecStitch;
  x: longint= 0;
  y: longint= 0;

begin
{$ifdef HAS_CURRENTROUTINE }
  Assert(thisName = {$I %CURRENTROUTINE%} + '()', 'Internal error: bad name in ' +
                                                {$I %CURRENTROUTINE%} + '()');
{$endif HAS_CURRENTROUTINE }
  result := false;
  pushRule(thisName);
  backtrack := FilePos(pesIn);
  header;
  WriteLn('Colour: [1] ', ThumbnailColourMap[1]);
  count := 0;
  colour := 1;
  ignoreOrdinates := 0;
  stitch := ReadQ(pesIn, pesOut, count div 2 + 1, Odd(count), not Odd(countPecTrimCommands div 2));
  while stitch.command <> $ff do begin
    Write('Stitch ', count div 2 + 1);

(* A colour change is documented as two bytes $fe $b0, after they've been       *)
(* decoded to a command and an ordinate they're $f0 and -336 respectively. What *)
(* is and what isn't counted as a valid half-stitch here is a bit of a hack but *)
(* appears to produce the right result when compared with what's in the PES.    *)

// Optimisation/command here: suppress colour change if it's actually the same colour.

    if (stitch.command = { $fe } $f0) and (stitch.ordinate = { $b0 } -336) then begin
      Write(' colour change from [', colour, '] ', ThumbnailColourMap[colour]);
      colour += 1;
      Write(' to [', colour, '] ', ThumbnailColourMap[colour], ',');
      countPecColourChanges += 1;
      ignoreOrdinates := 2;
      countPecHalfstitches += 1
    end else begin
      if stitch.command and $40 <> $00 then begin
        Write(' pause,');
        countPecPauseCommands += 1
      end;
      if stitch.command and $20 <> $00 then begin
        Write(' trim,');
        countPecTrimCommands += 1
      end;
      if stitch.command and $10 <> $00 then begin
        Write(' jump,');
        countPecJumpCommands += 1
      end;
      if stitch.command and $60 = $00 then
        countPecHalfstitches += 1
    end;
    if not Odd(count) then              (* Count starts at zero. First (half-)  *)
      Write(' x: ')                     (* stitch is 1 x, second 1 y, etc.      *)
    else
      Write(' y: ');

(* The stitch positions are relative so always output a sign. Ignore the        *)
(* ordinate associated with a colour change, and pragmatically assume that the  *)
(* next ordinate (i.e. the y associated with the colour change's x) is also to  *)
(* be ignored although it does appear to be slightly variable (alternating 1    *)
(* and 2 as mentioned in one of the documents).                                 *)

    if stitch.ordinate >= 0 then
      Write('+');
    WriteLn(stitch.ordinate);
    if ignoreOrdinates = 0 then begin
      if Odd(count) then begin
        x += stitch.ordinate;
//        WriteLn('X absolute ', x);      (* For debugging                        *)
        if x < minPecX then
          minPecX := x;
        if x > maxPecX then
          maxPecX := x
      end else begin
        y += stitch.ordinate;
//        WriteLn('Y absolute ', y);      (* For debugging                        *)
        if y < minPecY then
          minPecY := y;
        if y > maxPecY then
          maxPecY := y
      end
    end else
      ignoreOrdinates -= 1;
    stitch := ReadQ(pesIn, pesOut, count div 2 + 1, Odd(count), not Odd(countPecTrimCommands div 2));
    count += 1
  end;
  WriteLn('End of stitch sequence');
  WriteLn(Up + 'OK ', popRule());
  result := true
end { pec_stitchListSubsection } ;


(* Parse the PEC thumbnail section.
*)
function pec_thumbnailImageSubsection(): boolean;

const
  thisName= 'pec_thumbnailImageSubsection()';

var
  backtrack: int64;
  i: integer;

begin
{$ifdef HAS_CURRENTROUTINE }
  Assert(thisName = {$I %CURRENTROUTINE%} + '()', 'Internal error: bad name in ' +
                                                {$I %CURRENTROUTINE%} + '()');
{$endif HAS_CURRENTROUTINE }
  result := false;
  pushRule(thisName);
  backtrack := FilePos(pesIn);
  header;
  if FilePos(pesIn) <> pecThumbnailByteOffset then begin
    WriteLn('*** In ', peekRule(), ': thumbnail image isn''t contiguous with stitchlist');
    WriteLn(Up + 'Backtrack ', popRule());
    Seek(pesIn, backtrack);
    exit
  end;
  for i := 0 to thumbnailColours do begin
    WriteLn('Thumbnail colour: ', i);
    ReadU8G(pesIn, pesOut, thumbnailWidth, thumbnailHeight, i)
  end;
  WriteLn(Up + 'OK ', popRule());
  result := true
end { pec_thumbnailImageSubsection } ;


(* Parse the PEC header.
*)
function pec_header(): boolean;

const
  thisName= 'pec_header()';

var
  backtrack: int64;
  i, v: integer;

begin
{$ifdef HAS_CURRENTROUTINE }
  Assert(thisName = {$I %CURRENTROUTINE%} + '()', 'Internal error: bad name in ' +
                                                {$I %CURRENTROUTINE%} + '()');
{$endif HAS_CURRENTROUTINE }
  result := false;
  pushRule(thisName);
  backtrack := FilePos(pesIn);
  header;
  WriteLn('NOTE: absolute location of the PEC header is stored in the PES header');
  if ReadN(pesIn, pesOut, 3) <> 'LA:' then begin
    WriteLn('*** In ', peekRule(), ': bad PEC magic number');
    WriteLn(Up + 'Backtrack ', popRule());
    Seek(pesIn, backtrack);
    exit
  end;
  ReadN(pesIn, pesOut, 16);
  if ReadN(pesIn, pesOut, 1) <> #$0d then begin
    WriteLn('*** In ', peekRule(), ': bad PEC name termination');
    WriteLn(Up + 'Backtrack ', popRule());
    Seek(pesIn, backtrack);
    exit
  end;
  ReadU8N(pesIn, pesOut, 12);
  ReadU16N(pesIn, pesOut, 1);
  thumbnailWidth := ReadU8(pesIn, pesOut);
  WriteLn('Thumbnail width (bytes): ', thumbnailWidth);
  thumbnailHeight := ReadU8(pesIn, pesOut);
  WriteLn('Thumbnail height (rows): ', thumbnailHeight);
  ReadU8N(pesIn, pesOut, 12);
  for i := 0 to 255 do
    ThumbnailColourMap[i] := -1;
  thumbnailColours := ReadU8(pesIn, pesOut);
  WriteLn('Thumbnail colours (-1): ', thumbnailColours);
  thumbnailColours := (thumbnailColours + 1) mod 256;
  for i := 0 to thumbnailColours - 1 do begin
    v := ReadU8(pesIn, pesOut);
    WriteLn('Thumbnail colour ', i, ': ', v, ' (', ColourName(v), ')');
    if i <= 255 then
      ThumbnailColourMap[i] := v
  end;
  ReadU8N(pesIn, pesOut, 462 - (thumbnailColours - 1));
  WriteLn('NOTE: padding must keep PEC header length constant at 512 (0x200) bytes');
  WriteLn(Up + 'OK ', popRule());
  result := true
end { pec_header } ;


(* Parse the PEC body, comprising stitchlist and thumbnail bitmaps.
*)
function pec_body(): boolean;

const
  thisName= 'pec_body()';

var
  backtrack: int64;
  v, width, height: integer;

begin
{$ifdef HAS_CURRENTROUTINE }
  Assert(thisName = {$I %CURRENTROUTINE%} + '()', 'Internal error: bad name in ' +
                                                {$I %CURRENTROUTINE%} + '()');
{$endif HAS_CURRENTROUTINE }
  result := false;
  pushRule(thisName);
  backtrack := FilePos(pesIn);
  header;
  if FilePos(pesIn) <> pecSectionByteOffset + 512 then begin
    WriteLn('*** In ', peekRule(), ': bad PEC header padding length');
    WriteLn(Up + 'Backtrack ', popRule());
    Seek(pesIn, backtrack);
    exit
  end;
  ReadS16(pesIn, pesOut);
  v := ReadU16(pesIn, pesOut);
  pecThumbnailByteOffset := pecSectionByteOffset + v + 512;
  WriteLn('Thumbnail image offset: ', v, ' (0x', HexStr(pecThumbnailByteOffset, 6), ')');
  WriteLn('NOTE: this must be adjusted if there are insertion/deletion patches in the PEC stitchlist');
  ReadU16N(pesIn, pesOut, 2);
  width := ReadS16(pesIn, pesOut);
  WriteLn('Width: ', width);
  height := ReadS16(pesIn, pesOut);
  WriteLn('height: ', height);
  ReadU16N(pesIn, pesOut, 2);
  if not pec_stitchListSubsection() then begin
{$ifdef ERROR2 }
    WriteLn('*** In ', peekRule(), ': unable to parse ', poppedRule);
{$endif ERROR2 }
    WriteLn(Up + 'Backtrack ', popRule());
    Seek(pesIn, backtrack);
    exit
  end;
  if not pec_thumbnailImageSubsection() then begin
{$ifdef ERROR2 }
    WriteLn('*** In ', peekRule(), ': unable to parse ', poppedRule);
{$endif ERROR2 }
    WriteLn(Up + 'Backtrack ', popRule());
    Seek(pesIn, backtrack);
    exit
  end;
  WriteLn(Up + 'OK ', popRule());
  result := true
end { pec_body } ;


(* Parse the PEC header and body.
*)
function pec_part(): boolean;

const
  thisName= 'pec_part()';

var
  backtrack: int64;

begin
{$ifdef HAS_CURRENTROUTINE }
  Assert(thisName = {$I %CURRENTROUTINE%} + '()', 'Internal error: bad name in ' +
                                                {$I %CURRENTROUTINE%} + '()');
{$endif HAS_CURRENTROUTINE }
  result := false;
  pushRule(thisName);
  backtrack := FilePos(pesIn);
  header;
  if not pec_header() then begin
{$ifdef ERROR2 }
    WriteLn('*** In ', peekRule(), ': unable to parse ', poppedRule);
{$endif ERROR2 }
    WriteLn(Up + 'Backtrack ', popRule());
    Seek(pesIn, backtrack);
    exit
  end;
  if not pec_body() then begin
{$ifdef ERROR2 }
    WriteLn('*** In ', peekRule(), ': unable to parse ', poppedRule);
{$endif ERROR2 }
    WriteLn(Up + 'Backtrack ', popRule());
    Seek(pesIn, backtrack);
    exit
  end;
  WriteLn(Up + 'OK ', popRule());
  result := true
end { pec_part } ;


(* Parse a PEC addendum.
*)
function pec_addendum(): boolean;

const
  thisName= 'pec_addendum()';

var
  backtrack: int64;

begin
{$ifdef HAS_CURRENTROUTINE }
  Assert(thisName = {$I %CURRENTROUTINE%} + '()', 'Internal error: bad name in ' +
                                                {$I %CURRENTROUTINE%} + '()');
{$endif HAS_CURRENTROUTINE }
  result := false;
  pushRule(thisName);
  backtrack := FilePos(pesIn);
  header;

// TODO : Fill this in.
WriteLn('In pec_addendum, at ', FilePos(pesIn), ' of total ', FileSize(pesIn));

  WriteLn(Up + 'OK ', popRule());
  result := true
end { pec_addendum } ;


(* Parse extents.
*)
function pes_extents(): boolean;

const
  thisName= 'pes_extents()';

var
  backtrack: int64;
  v: integer;

begin
{$ifdef HAS_CURRENTROUTINE }
  Assert(thisName = {$I %CURRENTROUTINE%} + '()', 'Internal error: bad name in ' +
                                                {$I %CURRENTROUTINE%} + '()');
{$endif HAS_CURRENTROUTINE }
  result := false;
  pushRule(thisName);
  backtrack := FilePos(pesIn);
  header;
  v := ReadS16(pesIn, pesOut);
  WriteLn('Extents left: ', v);
  v := ReadS16(pesIn, pesOut);
  WriteLn('Extents top: ', v);
  v := ReadS16(pesIn, pesOut);
  WriteLn('Extents right: ', v);
  v := ReadS16(pesIn, pesOut);
  WriteLn('Extents bottom: ', v);
  v := ReadS16(pesIn, pesOut);
  WriteLn('Extents left position: ', v);
  v := ReadS16(pesIn, pesOut);
  WriteLn('Extents top position: ', v);
  v := ReadS16(pesIn, pesOut);
  WriteLn('Extents right position: ', v);
  v := ReadS16(pesIn, pesOut);
  WriteLn('Extents bottom position: ', v);
  WriteLn(Up + 'OK ', popRule());
  result := true
end { pes_extents } ;


(* Parse affine transform.
*)
function pes_affineTransform(): boolean;

const
  thisName= 'pes_affineTransform()';

var
  backtrack: int64;
  v: single;

begin
{$ifdef HAS_CURRENTROUTINE }
  Assert(thisName = {$I %CURRENTROUTINE%} + '()', 'Internal error: bad name in ' +
                                                {$I %CURRENTROUTINE%} + '()');
{$endif HAS_CURRENTROUTINE }
  result := false;
  pushRule(thisName);
  backtrack := FilePos(pesIn);
  header;
  v := ReadF32(pesIn, pesOut);
  WriteLn('Transform scale X: ', v);
  v := ReadF32(pesIn, pesOut);
  WriteLn('Transform skew Y: ', v);
  v := ReadF32(pesIn, pesOut);
  WriteLn('Transform skew X: ', v);
  v := ReadF32(pesIn, pesOut);
  WriteLn('Transform scale Y: ', v);
  v := ReadF32(pesIn, pesOut);
  WriteLn('Transform xlate X: ', v);
  v := ReadF32(pesIn, pesOut);
  WriteLn('Transform xlate Y: ', v);
  WriteLn(Up + 'OK ', popRule());
  result := true
end { pes_affinetransform } ;


(* Parse block geometry comprising extents and affine transform.
*)
function pes_blockGeometry(): boolean;

const
  thisName= 'pes_blockGeometry()';

var
  backtrack: int64;

begin
{$ifdef HAS_CURRENTROUTINE }
  Assert(thisName = {$I %CURRENTROUTINE%} + '()', 'Internal error: bad name in ' +
                                                {$I %CURRENTROUTINE%} + '()');
{$endif HAS_CURRENTROUTINE }
  result := false;
  pushRule(thisName);
  backtrack := FilePos(pesIn);
  header;
  if not pes_extents() then begin
{$ifdef ERROR2 }
    WriteLn('*** In ', peekRule(), ': unable to parse ', poppedRule);
{$endif ERROR2 }
    WriteLn(Up + 'Backtrack ', popRule());
    Seek(pesIn, backtrack);
    exit
  end;
  if not pes_affineTransform() then begin
{$ifdef ERROR2 }
    WriteLn('*** In ', peekRule(), ': unable to parse ', poppedRule);
{$endif ERROR2 }
    WriteLn(Up + 'Backtrack ', popRule());
    Seek(pesIn, backtrack);
    exit
  end;
  WriteLn(Up + 'OK ', popRule());
  result := true
end { pes_blockGeometry } ;


(* Parse a CEmbOne section. Because the parser does not have lookahead, the
  magic number was handled by the caller.
*)
function pes_embOne(): boolean;

const
  thisName= 'pes_embOne()';

var
  backtrack: int64;
  v: integer;

begin
{$ifdef HAS_CURRENTROUTINE }
  Assert(thisName = {$I %CURRENTROUTINE%} + '()', 'Internal error: bad name in ' +
                                                {$I %CURRENTROUTINE%} + '()');
{$endif HAS_CURRENTROUTINE }
  result := false;
  pushRule(thisName);
  backtrack := FilePos(pesIn);
  header;
  if not pes_blockGeometry() then begin
{$ifdef ERROR2 }
    WriteLn('*** In ', peekRule(), ': unable to parse ', poppedRule);
{$endif ERROR2 }
    WriteLn(Up + 'Backtrack ', popRule());
    Seek(pesIn, backtrack);
    exit
  end;
  v := ReadU16(pesIn, pesOut);          (* Annotated as "'1' (typical)"         *)
  v := ReadS16(pesIn, pesOut);
  WriteLn('CSewSeg x coordinate translation(?): ', v);
  v := ReadS16(pesIn, pesOut);
  WriteLn('CSewSeg y coordinate translation(?): ', v);
  v := ReadS16(pesIn, pesOut);
  WriteLn('CSewSeg width: ', v);
  v := ReadS16(pesIn, pesOut);
  WriteLn('CSewSeg height: ', v);
  ReadU8N(pesIn, pesOut, 8);            (* Padding                              *)
  cSewSegBlockCount := ReadU16(pesIn, pesOut);
  WriteLn('CSewSeg blockCount: ', cSewSegBlockCount);

(* Undocumented padding.                                                        *)

  v := ReadU16(pesIn, pesOut);
  if v <> $ffff then begin
    WriteLn('*** In ', peekRule(), ': unexpected padding (1)');
    WriteLn(Up + 'Backtrack ', popRule());
    Seek(pesIn, backtrack);
    exit
  end;
  v := ReadU16(pesIn, pesOut);
  if v <> $0000 then begin
    WriteLn('*** In ', peekRule(), ': unexpected padding (2)');
    WriteLn(Up + 'Backtrack ', popRule());
    Seek(pesIn, backtrack);
    exit
  end;
  WriteLn(Up + 'OK ', popRule());
  result := true
end { pes_embOne } ;


(* CSewSeg stitch list.
*)
function pes_sewSegStitchList(): boolean;

const
  thisName= 'pes_sewSegStitchList()';

var
  backtrack: int64;
  i, t, v: integer;
{$ifdef FPC }
  stitch: TScalarArray;
{$endif FPC }

begin
{$ifdef HAS_CURRENTROUTINE }
  Assert(thisName = {$I %CURRENTROUTINE%} + '()', 'Internal error: bad name in ' +
                                                {$I %CURRENTROUTINE%} + '()');
{$endif HAS_CURRENTROUTINE }
  result := false;
  pushRule(thisName);
  backtrack := FilePos(pesIn);
  header;
  t := ReadU16(pesIn, pesOut);
  Write('Stitch type: ');
  case t of
    0: WriteLn('normal');
    1: WriteLn('jump');
  otherwise
    WriteLn(t)
  end;
  v := ReadU16(pesIn, pesOut);
  WriteLn('Thread index (+1): ', v);
  v := ReadU16(pesIn, pesOut);
  WriteLn('Number of coordinates: ', v);
  for i := 0 to v - 1 do begin
{$ifdef FPC }
    stitch := ReadS16N(pesIn, pesOut, 2);
    WriteLn('Stitch ', i + 1, ': ', stitch[0].s16, ',', stitch[1].s16);
    if stitch[0].s16 < minPesX then
      minPesX := stitch[0].s16;
    if stitch[0].s16 > maxPesX then
      maxPesX := stitch[0].s16;
    if stitch[1].s16 < minPesY then
      minPesY := stitch[1].s16;
    if stitch[1].s16 > maxPesY then
      maxPesY := stitch[1].s16;
{$else }
    x := ReadS16();
    y := ReadS16();
    WriteLn('Stitch ', i + 1, ': ', x, ',', y);
    if x < minPesX then
      minPesX := x;
    if x > maxPesX then
      maxPesX := x;
    if y < minPesY then
      minPesY := y;
    if y > maxPesY then
      maxPesY := y;
{$endif FPC }
    case t of
      0: countPesStitchesNormal += 1;
      1: countPesStitchesJump += 1
    otherwise
      countPesStitchesOther += 1
    end;
    countPesStitchesTotal += 1
  end;
  WriteLn(Up + 'OK ', popRule());
  result := true
end { pes_sewSegStitchList } ;


(* CSewSeg colo(u)r list.
*)
function pes_sewSegColorList(): boolean;

const
  thisName= 'pes_sewSegColorList()';

var
  backtrack: int64;
  v: integer;

begin
{$ifdef HAS_CURRENTROUTINE }
  Assert(thisName = {$I %CURRENTROUTINE%} + '()', 'Internal error: bad name in ' +
                                                {$I %CURRENTROUTINE%} + '()');
{$endif HAS_CURRENTROUTINE }
  result := false;
  pushRule(thisName);
  backtrack := FilePos(pesIn);
  header;
  v := ReadU16(pesIn, pesOut);
  WriteLn('Block index of change: ', v);
  v := ReadU16(pesIn, pesOut);
  WriteLn('Thread palette/index: ', v);
  countPesColours += 1;
  WriteLn(Up + 'OK ', popRule());
  result := true
end { pes_sewSegColorList } ;


(* CSewSeg segment block.
*)
function pes_sewSegSegmentBlock(): boolean;

const
  thisName= 'pes_sewSegSegmentBlock()';

var
  backtrack: int64;
  v: integer;


  function endStitchBlocks(): boolean;

  begin

// This is a "temporary" warning in case the block counter is also being used to
// indicate cut/pause etc.

    if (v > 1000) and ( v <> $8003) then
      WriteLn('WARNING: unreasonably large colour count.');
    endStitchBlocks := v <> $8003
  end { endStitchBlocks } ;


begin
{$ifdef HAS_CURRENTROUTINE }
  Assert(thisName = {$I %CURRENTROUTINE%} + '()', 'Internal error: bad name in ' +
                                                {$I %CURRENTROUTINE%} + '()');
{$endif HAS_CURRENTROUTINE }
  result := false;
  pushRule(thisName);
  backtrack := FilePos(pesIn);
  header;
  repeat
    if not pes_sewSegStitchList() then begin
{$ifdef ERROR2 }
      WriteLn('*** In ', peekRule(), ': unable to parse ', poppedRule);
{$endif ERROR2 }
      WriteLn(Up + 'Backtrack ', popRule());
      Seek(pesIn, backtrack);
      exit
    end;
    v := ReadU16(pesIn, pesOut);
  until endStitchBlocks();              (* Special repeat-stitch-block code     *)
  while v > 0 do
    if not pes_sewSegColorList() then begin
{$ifdef ERROR2 }
      WriteLn('*** In ', peekRule(), ': unable to parse ', poppedRule);
{$endif ERROR2 }
      WriteLn(Up + 'Backtrack ', popRule());
      Seek(pesIn, backtrack);
      exit
    end else
      v -= 1;
  WriteLn(Up + 'OK ', popRule());
  result := true
end { pes_sewSegSegmentBlock } ;


(* Parse a CSewSeg section. Because the parser does not have lookahead, the
  magic number was handled by the caller.
*)
function pes_sewSeg(): boolean;

const
  thisName= 'pes_sewSeg()';

var
  backtrack: int64;

begin
{$ifdef HAS_CURRENTROUTINE }
  Assert(thisName = {$I %CURRENTROUTINE%} + '()', 'Internal error: bad name in ' +
                                                {$I %CURRENTROUTINE%} + '()');
{$endif HAS_CURRENTROUTINE }
  result := false;
  pushRule(thisName);
  backtrack := FilePos(pesIn);
  header;
  if not pes_sewSegSegmentBlock() then begin
{$ifdef ERROR2 }
    WriteLn('*** In ', peekRule(), ': unable to parse ', poppedRule);
{$endif ERROR2 }
    WriteLn(Up + 'Backtrack ', popRule());
    Seek(pesIn, backtrack);
    exit
  end;
  WriteLn(Up + 'OK ', popRule());
  result := true
end { pes_sewSeg } ;


// TODO : Fill these in

function pes_embCirc(): boolean;

begin
  result := false
end { pes_embCirc } ;


function pes_embRect(): boolean;

begin
  result := false
end { pes_embRect } ;


function pes_embLine(): boolean;

begin
  result := false
end { pes_embLine } ;


function pes_embPunch(): boolean;

begin
  result := false
end { pes_embPunch } ;


function pes_embNText(): boolean;

begin
  result := false
end { pes_embNText } ;


(* Expect a PES body. This will comprise a number of sections, in particular
  one or more CEmbOne and CSewSeg sections, an embedded PEC part, and possibly
  a PEC addendum which unlike the other sections is not identified by a magic
  number.
*)
function pes_body(): boolean;

const
  thisName= 'pes_body()';

var
  backtrack: int64;
  s: string;

begin
{$ifdef HAS_CURRENTROUTINE }
  Assert(thisName = {$I %CURRENTROUTINE%} + '()', 'Internal error: bad name in ' +
                                                {$I %CURRENTROUTINE%} + '()');
{$endif HAS_CURRENTROUTINE }
  result := false;
  pushRule(thisName);
  backtrack := FilePos(pesIn);
  header;
  while not Eof(pesIn) do begin
    if FilePos(pesIn) = pecSectionByteOffset then begin
      waitingForPec := false;
      if not pec_part() then begin
{$ifdef ERROR2 }
        WriteLn('*** In ', peekRule(), ': unable to parse ', poppedRule);
{$endif ERROR2 }
        WriteLn(Up + 'Backtrack ', popRule());
        Seek(pesIn, backtrack);
        exit
      end;
      if FilePos(pesIn) <> FileSize(pesIn) then
        WriteLn('NOTE: at ', FilePos(pesIn), ' (', HexStr(FileSize(pesIn), 5), ') of total ', FileSize(pesIn));
        if not pec_addendum() then begin
{$ifdef ERROR2 }
          WriteLn('*** In ', peekRule(), ': unable to parse ', poppedRule);
{$endif ERROR2 }
          WriteLn(Up + 'Backtrack ', popRule());
          Seek(pesIn, backtrack);
          exit
        end
    end else begin

(* Read a counted string, from which the section type may be deduced. Using     *)
(* strings in a case statement like this has been supported by FPC from v2.6,   *)
(* but is probably non-portable.                                                *)

      s := readC(pesIn, pesOut);
      case s of
        '':           ;                 (* Padding before PEC part etc.         *)
        'CEmbOne':    if not pes_embOne() then begin
{$ifdef ERROR2 }
                        WriteLn('*** In ', peekRule(), ': unable to parse ', poppedRule);
{$endif ERROR2 }
                        WriteLn(Up + 'Backtrack ', popRule());
                        Seek(pesIn, backtrack);
                        exit
                      end;
        'CSewSeg':    if not pes_sewSeg() then begin
{$ifdef ERROR2 }
                        WriteLn('*** In ', peekRule(), ': unable to parse ', poppedRule);
{$endif ERROR2 }
                        WriteLn(Up + 'Backtrack ', popRule());
                        Seek(pesIn, backtrack);
                        exit
                      end;
        'CEmbCirc':   exit(false); // Placeholder
        'CEmbRect':   exit(false); // Placeholder
        'CEmbLine':   exit(false); // Placeholder
        'CEmbPunch':  exit(false); // Placeholder
        'CSewFigSeq': exit(false); // Placeholder
        'CEmbNText':  exit(false) // Placeholder
      otherwise
        WriteLn('*** In ', peekRule(), ': unknown section type ', s);
        WriteLn(Up + 'Backtrack ', popRule());
        Seek(pesIn, backtrack);
        exit
      end
    end
  end;
  WriteLn(Up + 'OK ', popRule());
  result := true
end { pes_body } ;


(* Expect a hoop subsection for v2 and later headers.
*)
function pes_hoopsize(): boolean;

const
  thisName= 'pes_hoopsize()';

var
  backtrack: int64;
  width, height: word;

begin
{$ifdef HAS_CURRENTROUTINE }
  Assert(thisName = {$I %CURRENTROUTINE%} + '()', 'Internal error: bad name in ' +
                                                {$I %CURRENTROUTINE%} + '()');
{$endif HAS_CURRENTROUTINE }
  result := false;
  pushRule(thisName);
  backtrack := FilePos(pesIn);
  header;
  width := ReadU16(pesIn, pesOut);
  height := ReadU16(pesIn, pesOut);
  WriteLn('Hoop size: ', width, 'x', height, 'mm');
  if (width > 1000) or (height > 1000) then begin
    WriteLn('*** In ', peekRule(), ': hoop size is unreasonably large');
    WriteLn(Up + 'Backtrack ', popRule());
    Seek(pesIn, backtrack);
    exit
  end;
  WriteLn(Up + 'OK ', popRule());
  result := true
end { pes_hoopsize } ;


(* Expect a PES v1.0 header.
*)
function pes_header_1x0(): boolean;

const
  thisName= 'pes_header_1x0()';

var
  backtrack: int64;
  v: integer;


  (* Output what is assumed to be a 20-bit address as five hex digits plus a
    padding space.
  *)
  function hex6(l: longint; padding: string= ' '): string;

  begin
    result := HexStr(l, 5);
    while Length(result) < 5 do
      result := '0' + result;
    result += padding;
  end { hex6 } ;


begin
{$ifdef HAS_CURRENTROUTINE }
  Assert(thisName = {$I %CURRENTROUTINE%} + '()', 'Internal error: bad name in ' +
                                                {$I %CURRENTROUTINE%} + '()');
{$endif HAS_CURRENTROUTINE }
  result := false;
  pushRule(thisName);
  backtrack := FilePos(pesIn);
  header;
  pecSectionByteOffset := ReadU32(pesIn, pesOut);
  WriteLn('Absolute PEC section byte offset: 0x', hex6(pecSectionByteOffset, ''));
  WriteLn('NOTE: this must be adjusted if there are insertion/deletion patches in the PES part');
  waitingForPec := true;

// The note "Writing Ultra-Truncated PES v.1" in the EduTechWiki document implies
// that all fields and sections between this point and the start of the PEC (i.e.
// the offset above) should be considered to be optional.
//
// This can probably be handled by raising an exception if the file is about to
// be read with waitingForPec true and the file position at pecSectionByteOffset,
// with all rules explicitly handling this in a way that doesn't break EOF and
// returning true until we get to the PEC handler at which point the flag is
// flipped false.

  v := ReadU16(pesIn, pesOut);
  case v of
    0: WriteLn('Hoop size: 100x100mm');
    1: WriteLn('Hoop size: 130x180mm')
  otherwise
    WriteLn('Hoop type: ', v)
  end;
  v := ReadU16(pesIn, pesOut);
  WriteLn('Use existing design: ', v);
  segmentBlockCount := ReadU16(pesIn, pesOut);
  WriteLn('Segment block count: ', segmentBlockCount);

(* Undocumented padding.                                                        *)

  v := ReadU16(pesIn, pesOut);
  if v <> $ffff then begin
    WriteLn('*** In ', peekRule(), ': unexpected padding (1)');
    WriteLn(Up + 'Backtrack ', popRule());
    Seek(pesIn, backtrack);
    exit
  end;
  v := ReadU16(pesIn, pesOut);
  if v <> $0000 then begin
    WriteLn('*** In ', peekRule(), ': unexpected padding (2)');
    WriteLn(Up + 'Backtrack ', popRule());
    Seek(pesIn, backtrack);
    exit
  end;
  WriteLn(Up + 'OK ', popRule());
  result := true
end { pes_header_1x0 } ;


(* Expect a PES v2.0 header.
*)
function pes_header_2x0(): boolean;

begin
  result := false
end { pes_header_2x0 } ;


(* Expect a PES v2.5 header.
*)
function pes_header_2x5(): boolean;

begin
  result := false
end { pes_header_2x5 } ;


(* Expect a PES v3.0 header.
*)
function pes_header_3x0(): boolean;

begin
  result := false
end { pes_header_3x0 } ;


(* Expect a PES v4.0 header.
*)
function pes_header_4x0(): boolean;

begin
  result := false
end { pes_header_4x0 } ;


(* Expect a PES v5.0 header.
*)
function pes_header_5x0(): boolean;

begin
  result := false
end { pes_header_5x0 } ;


(* Expect a PES v5.5 header.
*)
function pes_header_5x5(): boolean;

begin
  result := false
end { pes_header_5x5 } ;


(* Expect a PES v5.6 header.
*)
function pes_header_5x6(): boolean;

begin
  result := false
end { pes_header_5x6 } ;


(* Expect a PES v6.0 header.
*)
function pes_header_6x0(): boolean;

begin
  result := false
end { pes_header_6x0 } ;


(* Expect a PES header of one of the known types.
*)
function pes_header(): boolean;

const
  thisName= 'pes_header()';

var
  backtrack: int64;
  s: string;

begin
{$ifdef HAS_CURRENTROUTINE }
  Assert(thisName = {$I %CURRENTROUTINE%} + '()', 'Internal error: bad name in ' +
                                                {$I %CURRENTROUTINE%} + '()');
{$endif HAS_CURRENTROUTINE }
  result := false;
  pushRule(thisName);
  backtrack := FilePos(pesIn);
  header;

(* Read four bytes. If these aren't correct then it can't be a valid header.    *)

  s := ReadN(pesIn, pesOut, 4);
  if s <> '#PES' then begin
    WriteLn('Bad PES header signature "', s, '"');
    WriteLn(Up + 'Backtrack ', popRule());
    Seek(pesIn, backtrack);
    exit
  end;

(* Read four bytes, from which the header version may be deduced. Using strings *)
(* in a case statement like this has been supported by FPC from v2.6, but is    *)
(* probably non-portable.                                                       *)

  s := ReadN(pesIn, pesOut, 4);
  case s of
    '0001': result := pes_header_1x0();
    '0002': result := pes_header_2x0();
    '0025': result := pes_header_2x5();
    '0003': result := pes_header_3x0();
    '0004': result := pes_header_4x0();
    '0005': result := pes_header_5x0();
    '0055': result := pes_header_5x5();
    '0056': result := pes_header_5x6();
    '0006': result := pes_header_6x0()
  otherwise
    WriteLn('*** In ', peekRule(), ': bad header version "', s, '"');
    WriteLn(Up + 'Backtrack ', popRule());
    Seek(pesIn, backtrack);
    exit
  end;
  WriteLn(Up + 'OK ', popRule());
  result := true
end { pes_header } ;


(* Expect a correctly-formed PES file, comprising a header and a body. In common
  with all other rules the file should not terminate prematurely, and on exit
  we should find that we are positioned at EOF i.e. there's nothing unexpected
  trailing the body.
*)
function pes_file(): boolean;

  const
  thisName= 'pes_file()';

var
  backtrack: int64;

begin
{$ifdef HAS_CURRENTROUTINE }
  Assert(thisName = {$I %CURRENTROUTINE%} + '()', 'Internal error: bad name in ' +
                                                {$I %CURRENTROUTINE%} + '()');
{$endif HAS_CURRENTROUTINE }
  result := false;
  pushRule(thisName);
  backtrack := FilePos(pesIn);
  header;
  if not pes_header() then begin
{$ifdef ERROR2 }
    WriteLn('*** In ', peekRule(), ': unable to parse ', poppedRule);
{$endif ERROR2 }
    WriteLn(Up + 'Backtrack ', popRule());
    Seek(pesIn, backtrack);
    exit;
  end;
  if not pes_body() then begin
{$ifdef ERROR2 }
    WriteLn('*** In ', peekRule(), ': unable to parse ', poppedRule);
{$endif ERROR2 }
    WriteLn(Up + 'Backtrack ', popRule());
    Seek(pesIn, backtrack);
    exit
  end;
  WriteLn(Up + 'OK ', popRule());
  result := true
end { pes_file } ;


(* Recognise a PEC magic number and if found assume it's a "naked" PEC file.
*)
function pec_file(): boolean;

const
  thisName= 'pec_file';

var
  backtrack: int64;
  s: string;

begin
{$ifdef HAS_CURRENTROUTINE }
  Assert(thisName = {$I %CURRENTROUTINE%} + '()', 'Internal error: bad name in ' +
                                                {$I %CURRENTROUTINE%} + '()');
{$endif HAS_CURRENTROUTINE }
  result := false;
  pushRule(thisName);
  backtrack := FilePos(pesIn);
  header;
  s := ReadN(pesIn, pesOut, 8);
  if s <> '#PEC0001' then begin
    WriteLn('Bad PEC header signature "', s, '"');
    WriteLn(Up + 'Backtrack ', popRule());
    Seek(pesIn, backtrack);
    exit
  end;
  pecSectionByteOffset := FilePos(pesIn);
  waitingForPec := false;
  if not pec_part() then begin
{$ifdef ERROR2 }
    WriteLn('*** In ', peekRule(), ': unable to parse ', poppedRule);
{$endif ERROR2 }
    WriteLn(Up + 'Backtrack ', popRule());
    Seek(pesIn, backtrack);
    exit
  end;
  if FilePos(pesIn) <> FileSize(pesIn) then // xxxxxxxxxxxxxxxxxxxxxxxxxx
    WriteLn('NOTE: at ', FilePos(pesIn), ' (', HexStr(FileSize(pesIn), 5), ') of total ', FileSize(pesIn));
    if not pec_addendum() then begin
{$ifdef ERROR2 }
      WriteLn('*** In ', peekRule(), ': unable to parse ', poppedRule);
{$endif ERROR2 }
      WriteLn(Up + 'Backtrack ', popRule());
      Seek(pesIn, backtrack);
      exit
    end;
  WriteLn(Up + 'OK ', popRule());
  result := true
end { pec_file } ;


(********************************************************************************)
(*                                                                              *)
(* Utility procedures: stuff used at the beginning and end of the program run.  *)
(*                                                                              *)
(********************************************************************************)


(* Display help information to standard error.
*)
procedure helpMe;

begin
  WriteLn(ErrOutput, 'PES v1 file parser/dumper. Command line:');
  WriteLn(ErrOutput);
  WriteLn(ErrOutput, '        pesdump [options] input_file [output file [commands]]');
  WriteLn(ErrOutput);
  WriteLn(ErrOutput, 'The input file name is mandatory, standard input will not be used if it is omitted.');
  WriteLn(ErrOutput, 'The output file name is optional, but required for most options to be effective.');
  WriteLn(ErrOutput);
  WriteLn(ErrOutput, 'Options:');
  WriteLn(ErrOutput);
  WriteLn(ErrOutput, '  --help                Return this help text and terminate.');
  WriteLn(ErrOutput, '  --version             Return version information and terminate.');
  WriteLn(ErrOutput);
  WriteLn(ErrOutput, '  --TrimToPause         Convert PEC trim commands to pause.');
  WriteLn(ErrOutput, '  --TrimToChange        Convert PEC trim commands to colour changes.');
  WriteLn(ErrOutput, '  --ChangeToDummy       Convert PEC colour changes to dummy jumps.');
  WriteLn(ErrOutput);
  WriteLn(ErrOutput, 'Commands:');
  WriteLn(ErrOutput);
  WriteLn(ErrOutput, '  @<num>  Continue to this point in the input file, assumed to be in order.');
  WriteLn(ErrOutput, '  {<num>  Delete the indicated number of bytes etc.');
  WriteLn(ErrOutput, '  }<bytes etc.> Insert the indicated bytes or stitch locations etc.');
  WriteLn(ErrOutput, '  =<bytes etc.> Overwrite the indicated bytes or stitch locations etc.');
  WriteLn(ErrOutput, '  +       Increment a byte or stitch location etc.');
  WriteLn(ErrOutput, '  -       Decrement a byte or stitch location etc.');
  WriteLn(ErrOutput);
  WriteLn(ErrOutput, 'e.g. to remove one colour change command:');
  WriteLn(ErrOutput);
  WriteLn(ErrOutput, '@0x0ad28 -1     Decrement number of colours in pec_header');
  WriteLn(ErrOutput, '@0x0ad48 =0x20  Change final colour map entry to padding');
  WriteLn(ErrOutput, '@0x0aefa -3     Decrement thumbnail image offset');
  WriteLn(ErrOutput, '@0x10469 {      Remove one colour change (x)');
  WriteLn(ErrOutput, '@0x1046b {      Remove one colour change (y)');
  WriteLn(ErrOutput, '@0x1213e {      Remove thumbnail');
  WriteLn(ErrOutput);
  WriteLn(ErrOutput, 'The { command "tries to do the right thing" if there is no parameter, but');
  WriteLn(ErrOutput, 'might not always get things right: inspect output diligently.');
  WriteLn(ErrOutput);
  WriteLn(ErrOutput, '** WARNING: the options and commands are experimental and might result **');
  WriteLn(ErrOutput, '**  in command sequences which crash or damage the embroidery machine. **');
  WriteLn(ErrOutput, '**   NO RESPONSIBILITY FOR DAMAGE OR LOSS OR INJURY WILL BE ACCEPTED.  **');
  WriteLn(ErrOutput)
end { helpMe } ;


(* Display version information to standard error.
*)
procedure versionMe;

// This string *SHOULD* be identical to one embedded in the RTL portion of the
// binary, accessible from 3.2.0 onwards using
//
// var
//   _FPCIdentA: record end external name '__fpc_ident';
//   FPCIdentA: PChar = @_FPCIdentA;

const
  FPCIdent= 'FPC ' + {$I %FPCVERSION%} + ' [' + {$I %FPCDATE%} + '] for ' +
                                {$I %FPCTARGETCPU%} + ' - ' + {$I %FPCTARGETOS%};

begin
  WriteLn(ErrOutput, 'Built using ', FPCIdent);
  WriteLn(ErrOutput)
end { versionMe } ;


(* If there is a parameter on the command line, attempt to open it as the input
  file. Return true if the specified file can be successfully opened, otherwise
  false which will probably result in help text being output.
*)
function openInput(const fn: string): boolean;

begin
  if fn = '' then
    exit(false);
{$push }
{$i- }
  AssignFile(pesIn, fn);
  Reset(pesIn, 1);
  result := IOResult = 0
{$pop  }
end { openInput } ;


function openOutput(const fn: string): boolean;

var
  scratch: longint;

begin
  if fn = '' then
    exit(false);
  scratch := TFileRec(pesOut).Handle;   (* Visible for debugging                *)
  {$push }
  {$i- }
    AssignFile(pesOut, fn);
    Rewrite(pesOut, 1);
    result := IOResult = 0;
  {$pop  }

(* Check that we can use the handle to determine whether an output file is open *)

  scratch := TFileRec(pesOut).Handle;   (* Visible for debugging                *)
  Assert(scratch > NotOpen, 'Internal error: unexpected output handle');
  scratch := TFileRec(pesOut).mode
end { openOutput } ;


(* Output what the program can tell us about why it's terminating. This should
  be at the end of the input file, but might instead tell us that a particular
  rule has encountered something unexpected.
*)
procedure summarise(why: string);

var
  rule: string;

begin
  if why <> '' then
    WriteLn(why);
  rule := popRule();
  while rule <> '' do begin
    WriteLn(rule);
    rule := popRule()
  end
end { summarise } ;


procedure summarise(success: boolean);

begin
  if not success then
    summarise('')
end { summarise } ;


(* Output counts of stitches, embedded commands etc.
*)
procedure counters;

begin
{$if declared(AddChar) }
  WriteLn(AddChar('=', '', Length(Banner)));
{$else }
  WriteLn(Banner);
{$endif }
  WriteLn('PES normal stitches: ', countPesStitchesNormal);
  WriteLn('PES jump stitches: ', countPesStitchesJump);
  WriteLn('PES other stitches: ', countPesStitchesOther);
  WriteLn('PES total stitches: ', countPesStitchesTotal);
  WriteLn('PES colours: ', countPesColours);
  WriteLn('PES X range: ', minPesX, '..', maxPesX);
  WriteLn('PES Y range: ', minPesY, '..', maxPesY);
  WriteLn('PEC half stitches: ', countPecHalfStitches);
  Write('PEC total stitches: ');
  if not Odd(countPecHalfStitches) then
    WriteLn(countPecHalfStitches div 2)
  else
    WriteLn((countPecHalfStitches / 2):3:1);
  WriteLn('PEC colour changes: ', countPecColourChanges);
  WriteLn('PEC pause commands: ', countPecPauseCommands);
  WriteLn('PEC trim commands: ', countPecTrimCommands);
  WriteLn('PEC jump commands: ', countPecJumpCommands);
  WriteLn('PEC X range: ', minPecX, '..', maxPecX);
  WriteLn('PEC Y range: ', minPecY, '..', maxPecY);
{$if declared(AddChar) }
  WriteLn(AddChar('=', '', Length(Banner)))
{$else }
  WriteLn(Banner)
{$endif }
end { counters } ;


(* Store commandline parameters in a StringList so that options can be removed
  as they are parsed. The list stores the program name at [0], followed by
  options and parameters ordered as on the commandline.
*)
procedure initParams;

var
  i: integer;

begin
  params :=TStringList.Create;
  for i := 0 to System.ParamCount() do
    params.Append(System.ParamStr(i))
end { initParams } ;


(* Local redefinition of System.ParamCount(), referring to a StringList. If the
  list contains the program name and no options or parameters, the result is zero.
*)
function paramCount(): integer;

begin
  if not Assigned(params) then
    initParams;
  result := params.Count - 1
end { paramCount } ;


type
  paramCase= (verbatim, uc, lc);


(* Local redefinition of System.ParamCount(), referring to a StringList. The
  result is blank if out of range.
*)
function paramStr(index: integer; forceCase: paramCase= verbatim): AnsiString;

begin
  result := '';
  if not Assigned(params) then
    initParams;
  if index <= paramCount() then
    case forceCase of
      uc: result := UpperCase(params[index]);
      lc: result := LowerCase(params[index])
    otherwise
      result := params[index]
    end
end { paramStr } ;


(* Remove an entry from the parameters StringList. [0] refers to the program
  name, which is protected from deletion.
*)
procedure paramDel(index: integer);

begin
  if not Assigned(params) then
    initParams;
  if (index >= 1) and (index <= paramCount()) then
    params.Delete(index)
end { paramDel } ;


type
  TdoStuff= procedure();


(* Parse the command line, setup anything else necessary, do the stuff that
  matters, and wrap up in good order.
*)
procedure setupAndWrapup(ds: TdoStuff);

begin
  try

(* Deal with the cases where there are no options/parameters or the options     *)
(* preclude normal operation.                                                   *)

    if paramCount() = 0 then begin
      helpMe;
      Halt(1)
    end;
{$ifdef UNIX }
    if (paramStr(1)[1] = '-') and       (* Unix/GNU convention is --help        *)
                          (Pos('-help', paramStr(1, lc)) > 0) then begin
{$else       }
      if (paramStr(1) = '/?') or        (* DOS/Windows convention is /help etc. *)
                          (Copy(paramStr(1, lc), 1, 2) = '/h') then begin
{$endif UNIX }
      helpMe;
      Halt(1)
    end;
    if paramStr(1, lc) = '--version' then begin
      versionMe;
      Halt(1)
    end;
    WriteLn('Program: ', paramStr(0));

(* Recognise and delete options which tune normal operation (e.g. convert every *)
(* trim to a pause), terminating when something which does not start with - or  *)
(* + is encountered or on an explicit -- . It would be reasonable for an option *)
(* which resulted in methodical deletions and/or insertions to be mutually      *)
(* exclusive with offset-based operations.                                  TBD *)

    while (paramCount() >= 1) and (paramStr(1)[1] in ['+', '-']) do
      try
        hasOptions := true;
        if (paramStr(1) = '--') or (paramStr(1) = '-') then
          break;
        case paramStr(1, lc) of
          '--trimtopause':   OptionTrimToPause := true;
          '--trimtochange':  OptionTrimToChange := true;
          '--changetodummy': OptionChangeToDummy := true
        otherwise
          WriteLn(ErrOutput);
          WriteLn(ErrOutput, 'Unknown option ', paramStr(1));
          helpMe;
          Halt(1)
        end
      finally
        paramDel(1)
      end;
    if hasOptions then begin
      Write('Options:');
      if OptionTrimToPause then
        Write(' --TrimToPause');
      if OptionTrimToChange then
        Write(' --TrimToChange');
      if OptionChangeToDummy then
        Write(' --ChangeToDummy');

      WriteLn
    end;

(* Recognise and delete a parameter naming an input file.                       *)

    if not openInput(paramStr(1)) then begin
      WriteLn(ErrOutput);
      WriteLn(ErrOutput, 'Unable to open input file ', paramStr(1));
      helpMe;
      Halt(1)
    end;
    try
      Write('Input: ', paramStr(1));
{$if declared(FormatDateTime) }
      WriteLn(' (', FormatDateTime('YYYY-MM-DD hh:mm:ss', FileDateToDateTime(FileAge(paramStr(1)))), ')');
{$else }
      WriteLn;
{$endif }
      paramDel(1);

(* Recognise and delete an optional parameter naming a binary output file. This *)
(* does not start with a command character (see below).                     TBD *)

      if (paramCount() >= 1) and not (paramStr(1)[1] in ['+', '-', '=', '@', '{', '}']) then begin
        if not openOutput(paramStr(1)) then begin
          WriteLn(ErrOutput);
          WriteLn(ErrOutput, 'Unable to open output file ', paramStr(1));
//          helpMe;
          Halt(1)
        end;
        WriteLn('Output: ', paramStr(1));
        paramDel(1)
      end;

(* The remaining parameters are commands to be applied to locations identified  *)
(* by offset in the file. These are assumed to be in the PEC part, so it is not *)
(* necessary to apply an automatic correction to pecSectionByteOffset; the      *)
(* actual data manipulation is done at the point where the input file is read.  *)

      while (paramCount() >= 1) and (paramStr(1)[1] in ['+', '-', '=', '@', '{', '}']) do
        try
          hasCommands := true;
          try
            AddPatch(ParsePatch(paramStr(1)))
          except
            WriteLn(ErrOutput);
            WriteLn(ErrOutput, 'Error parsing patch ', paramStr(1));
//            helpMe;
            Halt(1)
          end;
          paramDel(1)
        finally
        end;
      if hasCommands then begin
        Write('Commands:');
        DumpPatches;
        WriteLn
      end;
{$if declared(AddChar) }
      WriteLn(AddChar('=', '', Length(Banner)));
{$else }
      WriteLn(Banner);
{$endif }

      ds()                              (* <===== HERE'S THE STUFF THAT MATTERS *)

    finally
      if not (hasOptions or hasCommands) then
        if TFileRec(pesOut).Handle > NotOpen then
          if FileSize(pesOut) <> FileSize(pesIn) then begin
            WriteLn('#');
            WriteLn('# WARNING: Output file should be the same size as input file');
            WriteLn('#')
          end;
      CloseFile(pesIn);
      if TFileRec(pesOut).Handle > NotOpen then
        CloseFile(pesOut)
    end
  finally
    FreeAndNil(params)
  end
end { setupAndWrapup } ;


(********************************************************************************)
(*                                                                              *)
(* Main code: parse a PES or PEC file.                                          *)
(*                                                                              *)
(********************************************************************************)


(* A file should now be available on the pesIn file. Parse it, summarise the
  termination condition, and summarise the counters monitoring stitches,
  embedded commands and so on.
*)
procedure doStuff();

begin
  ruleStack := TStringList.Create;
  try
    try
      if pes_file() or pec_file() then begin
        summarise(true);                (* File parsed OK, rule stack empty     *)
        counters
      end else begin
        WriteLn('Unable to parse PES or PEC file');
        summarise(false)                (* Parse error, look at rule stack      *)
      end
    except
      on e: Exception do
        summarise(e.message)            (* Unexpected EOF etc., look at rule stack *)
    end
  finally
    ruleStack.Free
  end
end { doStuff } ;


begin
  TestUnpackStitch;                     (* Fails by assertion on error          *)
  setupAndWrapup(@doStuff)
end { PesDump } .

