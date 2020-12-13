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
  Classes, SysUtils,
  StrUtils, DateUtils;                  (* These units are optional             *)

(* If FPC version 3.2.0 or later is used, it is able to validate that error     *)
(* messages correctly identify what function was being executed at the time:    *)
(* this is important since it includes parsing rules where an error indicates   *)
(* either something wrong in the input file or a flaw in the program. Versions  *)
(* of FPC predating 2.2.4 lack the FPC_FULLVERSION predefined, so cannot fail   *)
(* gracefully when they try to determine whether the CURRENTROUTINE expansion   *)
(* is available. Other factors mandate that in practice FPC older than 2.6.0    *)
(* will be unable to compile this source file without modification.             *)

{$undef HAS_CURRENTROUTINE    }
{$if FPC_FULLVERSION > 030200 }         (* Requires FPC 2.2.4 minimum           *)
{$define HAS_CURRENTROUTINE   }         (* Requires FPC 3.2.0 minimum           *)
{$assertions                  }         (* Make sure name checks are operative  *)
{$endif FPC_FULLVERSION       }

{ define ERROR2 }                       (* Extra parser error messages          *)

(* State variables: rule stack for diagnostics, counters etc.                   *)

const
  traceTop= (1024 * 1024) - 1;
  notOpen= 0;                           (* Handle value for output file checks  *)

{$ifdef FPC }
type
  byteArray= array of byte;
  wordArray= array of word;
  smallintArray= array of smallint;
  singleArray= array of single;
{$endif FPC }

type
  pecStitch= record
               command: byte;
               ordinate: longint
             end;

var
  params: TStringList= nil;
  optionTrimToPause: boolean= false;
  optionTrimToChange: boolean= false;
  hasOptions: boolean= false;
  hasCommands: boolean= false;
  pesIn, pesOut: file;
  ruleStack: TStringList;
  poppedRule: string= '[Empty]';
  traceStart, traceBytes: longint;
  trace: array[0..traceTop] of byte;

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
  countPecPauseCommands: longword= 0;
  countPecTrimCommands: longword= 0;
  countPecJumpCommands: longword= 0;
  minPecX: longint= 0;
  maxPecX: longint= 0;
  minPecY: longint= 0;
  maxPecY: longint= 0;
  countPecColourChanges: longword= 0;

(********************************************************************************)
(*                                                                              *)
(* Utility procedures: input/output formatting etc. available to all rules.     *)
(*                                                                              *)
(********************************************************************************)

(* Inspection of a PES file indicates that it is little-endian. Exceptions      *)
(* raised in these functions are assumed to be fatal, and to result in a back-  *)
(* trace of the rules that got us here.                                         *)

const
(* Note: these characters might be contentious with old FPC etc. versions that
  aren't happy with UTF-8.
*)
{$ifndef VER3 }
  dot= '.';
  arrow= ' -> ';
  up= '^ ';
{$else        }
  dot= '·';
  arrow= ' → ';
  up= '↑ ';
{$endif VER3  }

(* The banner matches address + 16 hex bytes + padding but should optimise to a
  length if StrUtils is imported, other underlines match the text with which
  they're associated.
*)
  banner= '========================================================';


(* Assuming 16 bytes per row of hex bytes, mark the middle.
*)
function pad(index: integer; bytes: integer= 16): string;

begin
  if index = bytes div 2 - 1 then
    result := dot
  else
    result := ' '
end { pad } ;


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


(* Output a byte as two hex digits plus a padding space.
*)
function hex3(b: byte; padding: string= ' '): string;

begin
  result := HexStr(b, 2);
  while Length(result) < 2 do
    result := '0' + result;
  result += padding;
end { hex3 } ;


(* Sanitise an output character.
*)
function safeChar(b: byte): string;

begin
  case b of
    $00..
    $1f:  result := dot;
    $7f..
    $ff:  result := dot
  otherwise
    result := Chr(b)
  end
end { safeChar } ;


(* Common dump output for raw hex-formatted data, i.e. just about everything
  except possibly some graphics. Assume that once a field has been parsed as a
  specific type it will also be output in that format, so that we don't have to
  worry about e.g. decoding floating-point numbers here.
*)
procedure doneReadHexAscii(bytes: integer= 16);

var
  lines, i, j, charsOutput: integer;
  chars: string;

begin
  lines := traceBytes div bytes;
  for i := 0 to lines do begin
    if traceBytes = 0 then              // TODO : Tidy this up!
      break;
    Write(hex6(traceStart));            (* Five digits plus padding             *)
    Write(' ');
    charsOutput := 7;
    chars := '';
    for j := 0 to bytes - 1 do begin
      if j >= traceBytes then
        break;
      Write(hex3(trace[bytes * i + j], pad(j, bytes))); (* Two digits plus padding *)
      chars += safeChar(trace[bytes * i + j]);
      charsOutput += 3;
    end;

(* Assuming 16 bytes expressed as hex, the address + bytes + padding will match *)
(* the === banner used to separate major sections of output.                    *)

    while charsOutput < (7 + 3 * bytes + 1) do begin
      Write(' ');
      charsOutput += 1
    end;
    WriteLn(chars);
    traceStart += bytes;
    traceBytes -= bytes;
    if traceBytes < 0 then
      traceBytes := 0
  end
end { doneReadHexAscii } ;


var
  (* Optional thumbnail colours from the PEC header. These are not necessarily the
    same as the expected thread colours.
  *)
  thumbnailColourMap: array[0..255] of integer;


(* These believed to be from a Brother Innovis 955.
*)
function colourName(index: integer): string;

begin
  case index of
    0:  result := 'Zero';
    1:  result := 'Prussian Blue';
    2:  result := 'Blue';
    3:  result := 'Teal Green';
    4:  result := 'Corn Flower Blue';
    5:  result := 'Red';
    6:  result := 'Reddish Brown';
    7:  result := 'Magenta';
    8:  result := 'Light Lilac';
    9:  result := 'Lilac';
    10: result := 'Mint Green';
    11: result := 'Deep Gold';
    12: result := 'Orange';
    13: result := 'Yellow';
    14: result := 'Lime Green';
    15: result := 'Brass';
    16: result := 'Silver';
    17: result := 'Russet Brown';
    18: result := 'Cream Brown';
    19: result := 'Pewter';
    20: result := 'Black';
    21: result := 'Ultramarine';
    22: result := 'Royal Purple';
    23: result := 'Dark Gray';
    24: result := 'Dark Brown';
    25: result := 'Deep Rose';
    26: result := 'Light Brown';
    27: result := 'Salmon Pink';
    28: result := 'Vermilion';
    29: result := 'White';
    30: result := 'Violet';
    31: result := 'Seacrest';
    32: result := 'Sky Blue';
    33: result := 'Pumpkin';
    34: result := 'Cream Yellow';
    35: result := 'Khaki';              (* How did this get to be #feca15?      *)
    36: result := 'Clay Brown';
    37: result := 'Leaf Green';
    38: result := 'Peacock Blue';
    39: result := 'Gray';
    40: result := 'Warm Gray';
    41: result := 'Dark Olive';
    42: result := 'Linen';
    43: result := 'Pink';
    44: result := 'Deep Green';
    45: result := 'Lavender';
    46: result := 'Wisteria Violet';
    47: result := 'Beige';
    48: result := 'Carmine';
    49: result := 'Amber Red';
    50: result := 'Olive Green';
    51: result := 'Dark Fuchsia';
    52: result := 'Tangerine';
    53: result := 'Light Blue';
    54: result := 'Emerald Green';
    55: result := 'Purple';
    56: result := 'Moss Green';
    57: result := 'Flesh Pink';
    58: result := 'Harvest Gold';
    59: result := 'Electric Blue';
    60: result := 'Lemon Yellow';
    61: result := 'Fresh Green';
    62: result := 'Applique Material';
    63: result := 'Applique Position';
    64: result := 'Applique'
  otherwise
    result := ''
  end
end { colourName } ;


procedure doneReadHexPbm(width, height, index: integer; bytes: integer= 8);

var
  lines, i, j, charsOutput: integer;
  chars: string;


  (* Convert a byte into 0/1 bits, LSB first. Note that IntToBin() does this
    MSB first.
  *)
  function byteToStr(b: byte; bits: integer): string;

  begin
    result := '';
    while bits > 0 do begin
      if Odd(b) then
        result += '1'
      else
        result += '0';
      b := b >> 1;
      bits -= 1
    end
  end { byteToStr } ;


begin
  for i := 1 to 7 + (3 * bytes) + 1 do
    chars += ' ';
  WriteLn(chars, '|P1');
  Write(chars, '|# Thumbnail ', index);
  if (index <= 255) and (thumbnailColourMap[index] <> -1) then
    WriteLn(', colour ', thumbnailColourMap[index], ' (',
                                colourName(thumbnailColourMap[index]), ')')
  else
    WriteLn;
  WriteLn(chars, '|', width, ' ', height);
  lines := traceBytes div bytes;
  for i := 0 to lines do begin
    if traceBytes = 0 then              // TODO : Tidy this up!
      break;
    Write(hex6(traceStart));            (* Five digits plus padding             *)
    Write(' ');
    charsOutput := 7;
    chars := '';
    for j := 0 to bytes - 1 do begin
      if j >= traceBytes then
        break;
      Write(hex3(trace[bytes * i + j], pad(j, bytes))); (* Two digits plus padding *)
      chars += byteToStr(trace[bytes * i + j], 8);
      charsOutput += 3;
    end;
    while charsOutput < (7 + 3 * bytes + 1) do begin
      Write(' ');
      charsOutput += 1
    end;
    WriteLn('|', chars);
    traceStart += bytes;
    traceBytes -= bytes;
    if traceBytes < 0 then
      traceBytes := 0
  end
end { doneReadHexPbm } ;


(* Clear storage used to dump what's been read, and note the start point in the
  file. If there's anything buffered on entry this will be output in generic
  hex/ASCII format.
*)
procedure startRead(readPos: longint);

begin
  if traceBytes <> 0 then
    doneReadHexAscii;
  traceStart := readPos;
  traceBytes := 0
end { startRead } ;


(* Store intermediate data that's been read, the parameter type here does not
  determine the output format.
*)
procedure dumpRead(const s: string);

var
  i: integer;

begin
  for i := 1 to Length(s) do begin
    trace[traceBytes] := Ord(s[i]);
    traceBytes += 1;
    Assert(traceBytes <= traceTop, 'Internal error: trace buffer overflow')
  end
end { dumpRead } ;


(* Store intermediate data that's been read, the parameter type here does not
  determine the output format.
*)
procedure dumpRead(b: byte);

begin
  trace[traceBytes] := b;
  traceBytes += 1;
  Assert(traceBytes <= traceTop, 'Internal error: trace buffer overflow')
end { dumpRead } ;


(* Store intermediate data that's been read, the parameter type here does not
  determine the output format.
*)
procedure dumpRead(w: word);

var
  scratch: record
             case boolean of
               false: (b: array[0..1] of byte);
               true:  (w: word)
             end;
  i: integer;

begin
  scratch.w := w;                       (* Parameter order as read from file    *)
  for i := 0 to 1 do
    dumpRead(scratch.b[i])
end { dumpRead } ;


(* Store intermediate data that's been read, the parameter type here does not
  determine the output format.
*)
procedure dumpRead(s: smallint);

begin
{$push }
{$r-   }
  dumpRead(word(s))
{$pop  }
end { dumpRead } ;


(* Store intermediate data that's been read, the parameter type here does not
  determine the output format.
*)
procedure dumpRead(l: longword);

var
  scratch: record
             case boolean of
               false: (b: array[0..3] of byte);
               true:  (l: longword)
             end;
  i: integer;

begin
  scratch.l := l;                       (* Parameter order as read from file    *)
  for i := 0 to 3 do
    dumpRead(scratch.b[i])
end { dumpRead } ;


(* Store intermediate data that's been read, the parameter type here does not
  determine the output format.
*)
procedure dumpRead(s: single);

begin
{$push }
{$r-   }
  dumpRead(longword(s))
{$pop  }
end { dumpRead } ;


(* Output data that's been read, the parameter type determines the format
  (string, decimal numeric, graphics block).
*)
procedure doneRead(const s: string);

begin
  dumpRead(s);
  doneReadHexAscii
end { doneRead } ;


(* Output data that's been read, the parameter type determines the format
  (string, decimal numeric, graphics block).
*)
procedure doneRead(b: byte);

begin
  dumpRead(b);
  doneReadHexAscii
end { doneRead } ;


(* Output data that's been read, the parameter type determines the format
  (string, decimal numeric, graphics block).
*)
procedure doneRead(w: word);

begin
  dumpRead(w);
  doneReadHexAscii
end { doneRead } ;


(* Output data that's been read, the parameter type determines the format
  (string, decimal numeric, graphics block).
*)
procedure doneRead(s: smallint);

begin
  dumpRead(s);
  doneReadHexAscii
end { doneRead } ;


(* Output data that's been read, the parameter type determines the format
  (string, decimal numeric, graphics block).
*)
procedure doneRead(l: longword);

begin
  dumpRead(l);
  doneReadHexAscii
end { doneRead } ;


(* Output data that's been read, the parameter type determines the format
  (string, decimal numeric, graphics block).
*)
procedure doneRead(f: single);

begin
  dumpRead(f);
  doneReadHexAscii
end { doneRead } ;


(* Read an unsigned 8-bit number.
*)
function readU8(): byte;

const
  thisName= 'readU8()';

var
  buffer: byte;
  r: integer;

begin
{$ifdef HAS_CURRENTROUTINE }
  Assert(thisName = {$I %CURRENTROUTINE%} + '()', 'Internal error: bad name in ' + {$I %CURRENTROUTINE%} + '()');
{$endif HAS_CURRENTROUTINE }
  Assert(SizeOf(result) = 1, 'Internal error: bad U8 size');
  startRead(FilePos(pesIn));
  BlockRead(pesIn, buffer, sizeOf(buffer), r);
  if r <> sizeOf(buffer) then
    raise Exception.Create('In ' + thisName + ', unexpected EOF');
  result := buffer;
  doneRead(buffer);

(* The result might be adjusted for endianness, but is always returned without  *)
(* other modification so that the parser can validate the content of the file.  *)
(* If any systematic modification is to be done in response to a command-line   *)
(* option it will affect what is written to a binary output file, but the text  *)
(* output for user inspection will be unaffected although a comment might be    *)
(* inserted.                                                                    *)

  if TFileRec(pesOut).Handle > notOpen then begin
    BlockWrite(pesOut, buffer, sizeOf(buffer), r);
    if r <> sizeOf(buffer) then
      raise Exception.Create('In ' + thisName + ', write error')
  end
end { readU8 } ;


(* Read an unsigned 16-bit number.
*)
function readU16(): word;

const
  thisName= 'readU16()';

var
  buffer: word;
  r: integer;

begin
{$ifdef HAS_CURRENTROUTINE }
  Assert(thisName = {$I %CURRENTROUTINE%} + '()', 'Internal error: bad name in ' + {$I %CURRENTROUTINE%} + '()');
{$endif HAS_CURRENTROUTINE }
  Assert(SizeOf(result) = 2, 'Internal error: bad U16 size');
  startRead(FilePos(pesIn));
  BlockRead(pesIn, buffer, SizeOf(result), r);
  if r <> SizeOf(result) then
    raise Exception.Create('In ' + thisName + ', unexpected EOF');
  result := LEtoN(buffer);
  doneRead(buffer);

(* The result might be adjusted for endianness, but is always returned without  *)
(* other modification so that the parser can validate the content of the file.  *)
(* If any systematic modification is to be done in response to a command-line   *)
(* option it will affect what is written to a binary output file, but the text  *)
(* output for user inspection will be unaffected although a comment might be    *)
(* inserted.                                                                    *)

  if TFileRec(pesOut).Handle > notOpen then begin
    BlockWrite(pesOut, buffer, sizeOf(buffer), r);
    if r <> sizeOf(buffer) then
      raise Exception.Create('In ' + thisName + ', write error')
  end
end { readU16 } ;


(* Read a signed 16-bit number.
*)
function readS16(): smallint;

const
  thisName= 'readS16()';

var
  buffer: smallint;
  r: integer;

begin
{$ifdef HAS_CURRENTROUTINE }
  Assert(thisName = {$I %CURRENTROUTINE%} + '()', 'Internal error: bad name in ' + {$I %CURRENTROUTINE%} + '()');
{$endif HAS_CURRENTROUTINE }
  Assert(SizeOf(result) = 2, 'Internal error: bad S16 size');
  startRead(FilePos(pesIn));
  BlockRead(pesIn, buffer, SizeOf(result), r);
  if r <> SizeOf(result) then
    raise Exception.Create('In ' + thisName + ', unexpected EOF');
  result := LEtoN(buffer);
  doneRead(buffer);

(* The result might be adjusted for endianness, but is always returned without  *)
(* other modification so that the parser can validate the content of the file.  *)
(* If any systematic modification is to be done in response to a command-line   *)
(* option it will affect what is written to a binary output file, but the text  *)
(* output for user inspection will be unaffected although a comment might be    *)
(* inserted.                                                                    *)

  if TFileRec(pesOut).Handle > notOpen then begin
    BlockWrite(pesOut, buffer, sizeOf(buffer), r);
    if r <> sizeOf(buffer) then
      raise Exception.Create('In ' + thisName + ', write error')
  end
end { readS16 } ;


(* Read an unsigned 32-bit number.
*)
function readU32(): longword;

const
  thisName= 'readU32()';

var
  buffer: longword;
  r: integer;

begin
{$ifdef HAS_CURRENTROUTINE }
  Assert(thisName = {$I %CURRENTROUTINE%} + '()', 'Internal error: bad name in ' + {$I %CURRENTROUTINE%} + '()');
{$endif HAS_CURRENTROUTINE }
  Assert(SizeOf(result) = 4, 'Internal error: bad U32 size');
  startRead(FilePos(pesIn));
  BlockRead(pesIn, buffer, SizeOf(result), r);
  if r <> SizeOf(result) then
    raise Exception.Create('In ' + thisName + ', unexpected EOF');
  result := LEtoN(buffer);
  doneRead(buffer);

(* The result might be adjusted for endianness, but is always returned without  *)
(* other modification so that the parser can validate the content of the file.  *)
(* If any systematic modification is to be done in response to a command-line   *)
(* option it will affect what is written to a binary output file, but the text  *)
(* output for user inspection will be unaffected although a comment might be    *)
(* inserted.                                                                    *)

  if TFileRec(pesOut).Handle > notOpen then begin
    BlockWrite(pesOut, buffer, sizeOf(buffer), r);
    if r <> sizeOf(buffer) then
      raise Exception.Create('In ' + thisName + ', write error')
  end
end { readU32 } ;


(* Read a 32-bit float. PES files appear to use the standard IEEE format, but
  this should not be assumed in the general case.
*)
function readF32(): single;

const
  thisName= 'readF32()';

type
  fixup= record
           case boolean of
             false: (l: longword);
             true:  (s: single)
           end;

var
  r: integer;
  buffer: fixup;

begin
{$ifdef HAS_CURRENTROUTINE }
  Assert(thisName = {$I %CURRENTROUTINE%} + '()', 'Internal error: bad name in ' + {$I %CURRENTROUTINE%} + '()');
{$endif HAS_CURRENTROUTINE }
  Assert(SizeOf(result) = 4, 'Internal error: bad F32 size');
  startRead(FilePos(pesIn));
  BlockRead(pesIn, buffer.s, SizeOf(result), r);
  if r <> SizeOf(result) then
    raise Exception.Create('In ' + thisName + ', unexpected EOF');
  doneRead(buffer.s);                   (* Dump before in-situ endianness swap  *)
  buffer.l := LEtoN(buffer.l);
  result := buffer.s;

(* The result might be adjusted for endianness, but is always returned without  *)
(* other modification so that the parser can validate the content of the file.  *)
(* If any systematic modification is to be done in response to a command-line   *)
(* option it will affect what is written to a binary output file, but the text  *)
(* output for user inspection will be unaffected although a comment might be    *)
(* inserted.                                                                    *)

  if TFileRec(pesOut).Handle > notOpen then begin
    buffer.l := NtoLE(buffer.l);
    BlockWrite(pesOut, buffer, sizeOf(buffer), r);
    if r <> sizeOf(buffer) then
      raise Exception.Create('In ' + thisName + ', write error')
  end
end { readF32 } ;


{$ifdef FPC }

(* Read a block of bytes. This would normally be called for padding etc. and
  any attempt to return a block will probably be non-portable.
*)
function readU8N(n: integer): byteArray;

const
  thisName= 'readU8N()';

var
  i, r: integer;

begin
{$ifdef HAS_CURRENTROUTINE }
  Assert(thisName = {$I %CURRENTROUTINE%} + '()', 'Internal error: bad name in ' + {$I %CURRENTROUTINE%} + '()');
{$endif HAS_CURRENTROUTINE }
  startRead(FilePos(pesIn));
  SetLength(result, n);
  if n > 0 then begin
    BlockRead(pesIn, result[0], Length(result), r);
    if r <> Length(result) then
      raise Exception.Create('In ' + thisName + ', unexpected EOF');
    for i := 0 to Length(result) - 2 do
      dumpRead(result[i]);
    doneRead(result[Length(result) - 1]);

(* The result might be adjusted for endianness, but is always returned without  *)
(* other modification so that the parser can validate the content of the file.  *)
(* If any systematic modification is to be done in response to a command-line   *)
(* option it will affect what is written to a binary output file, but the text  *)
(* output for user inspection will be unaffected although a comment might be    *)
(* inserted.                                                                    *)

    if TFileRec(pesOut).Handle > notOpen then begin
      BlockWrite(pesOut, result[0], Length(result), r);
      if r <> Length(result) then
        raise Exception.Create('In ' + thisName + ', write error')
    end
  end
end { readU8N } ;


(* Read a block of words. This would normally be called for padding etc. and
  any attempt to return a block will probably be non-portable.
*)
function readU16N(n: integer): wordArray;

const
  thisName= 'readU16N()';

var
  i, r: integer;

begin
{$ifdef HAS_CURRENTROUTINE }
  Assert(thisName = {$I %CURRENTROUTINE%} + '()', 'Internal error: bad name in ' + {$I %CURRENTROUTINE%} + '()');
{$endif HAS_CURRENTROUTINE }
  startRead(FilePos(pesIn));
  SetLength(result, n);
  if n > 0 then begin
    BlockRead(pesIn, result[0], Length(result) * 2, r);
    if r <> Length(result) * 2 then
      raise Exception.Create('In ' + thisName + ', unexpected EOF');
    for i := 0 to Length(result) - 2 do
      dumpRead(result[i]);
    doneRead(result[Length(result) - 1]);

(* The result might be adjusted for endianness, but is always returned without  *)
(* other modification so that the parser can validate the content of the file.  *)
(* If any systematic modification is to be done in response to a command-line   *)
(* option it will affect what is written to a binary output file, but the text  *)
(* output for user inspection will be unaffected although a comment might be    *)
(* inserted.                                                                    *)

    if TFileRec(pesOut).Handle > notOpen then begin
      BlockWrite(pesOut, result[0], Length(result) * 2, r);
      if r <> Length(result) * 2 then
        raise Exception.Create('In ' + thisName + ', write error')
    end
  end
end { readU16N } ;


(* Read a block of words. This would normally be called for padding etc. and
  any attempt to return a block will probably be non-portable.
*)
function readS16N(n: integer): smallintArray;

const
  thisName= 'readS16N()';

var
  i, r: integer;

begin
{$ifdef HAS_CURRENTROUTINE }
  Assert(thisName = {$I %CURRENTROUTINE%} + '()', 'Internal error: bad name in ' + {$I %CURRENTROUTINE%} + '()');
{$endif HAS_CURRENTROUTINE }
  startRead(FilePos(pesIn));
  SetLength(result, n);
  if n > 0 then begin
    BlockRead(pesIn, result[0], Length(result) * 2, r);
    if r <> Length(result) * 2 then
      raise Exception.Create('In ' + thisName + ', unexpected EOF');
    for i := 0 to Length(result) - 2 do
      dumpRead(result[i]);
    doneRead(result[Length(result) - 1]);

(* The result might be adjusted for endianness, but is always returned without  *)
(* other modification so that the parser can validate the content of the file.  *)
(* If any systematic modification is to be done in response to a command-line   *)
(* option it will affect what is written to a binary output file, but the text  *)
(* output for user inspection will be unaffected although a comment might be    *)
(* inserted.                                                                    *)

    if TFileRec(pesOut).Handle > notOpen then begin
      BlockWrite(pesOut, result[0], Length(result) * 2, r);
      if r <> Length(result) * 2 then
        raise Exception.Create('In ' + thisName + ', write error')
    end
  end
end { readS16N } ;


(* Read a block of floats. This would normally be called for padding etc. and
  any attempt to return a block will probably be non-portable.
*)
function readF32N(n: integer): singleArray;

const
  thisName= 'readF32N()';

var
  i, r: integer;

begin
{$ifdef HAS_CURRENTROUTINE }
  Assert(thisName = {$I %CURRENTROUTINE%} + '()', 'Internal error: bad name in ' + {$I %CURRENTROUTINE%} + '()');
{$endif HAS_CURRENTROUTINE }
  startRead(FilePos(pesIn));
  SetLength(result, n);
  if n > 0 then begin
    BlockRead(pesIn, result[0], Length(result) * 4, r);
    if r <> Length(result) * 4 then
      raise Exception.Create('In ' + thisName + ', unexpected EOF');
    for i := 0 to Length(result) - 2 do
      dumpRead(result[i]);
    doneRead(result[Length(result) - 1]);

(* The result might be adjusted for endianness, but is always returned without  *)
(* other modification so that the parser can validate the content of the file.  *)
(* If any systematic modification is to be done in response to a command-line   *)
(* option it will affect what is written to a binary output file, but the text  *)
(* output for user inspection will be unaffected although a comment might be    *)
(* inserted.                                                                    *)

    if TFileRec(pesOut).Handle > notOpen then begin
      BlockWrite(pesOut, result[0], Length(result) * 4, r);
      if r <> Length(result) * 4 then
        raise Exception.Create('In ' + thisName + ', write error')
    end
  end
end { readF32N } ;

{$else      }
// TODO : Equivalent procedures for Pascal implementations without dynamic arrays.
{$endif FPC }


(* Read and discard a block of bytes. Assume that this represents a thumbnail
  in simple bitmap format and if possible dump it using PNM format rather than
  ASCII.
*)
procedure readU8G(width, height, index: integer);

const
  thisName= 'readU8G()';

var
  bitmap: byteArray;
  i, r: integer;

begin
{$ifdef HAS_CURRENTROUTINE }
  Assert(thisName = {$I %CURRENTROUTINE%} + '()', 'Internal error: bad name in ' + {$I %CURRENTROUTINE%} + '()');
{$endif HAS_CURRENTROUTINE }
  startRead(FilePos(pesIn));
  SetLength(bitmap, width * height);
  if width * height > 0 then begin
    BlockRead(pesIn, bitmap[0], Length(bitmap), r);
    if r <> Length(bitmap) then
      raise Exception.Create('In ' + thisName + ', unexpected EOF');
    for i := 0 to Length(bitmap) - 1 do
      dumpRead(bitmap[i]);
    doneReadHexPbm(width * 8, height, index, width);

(* The result might be adjusted for endianness, but is always returned without  *)
(* other modification so that the parser can validate the content of the file.  *)
(* If any systematic modification is to be done in response to a command-line   *)
(* option it will affect what is written to a binary output file, but the text  *)
(* output for user inspection will be unaffected although a comment might be    *)
(* inserted.                                                                    *)

    if TFileRec(pesOut).Handle > notOpen then begin
      BlockWrite(pesOut, bitmap[0], Length(bitmap), r);
      if r <> Length(bitmap) then
        raise Exception.Create('In ' + thisName + ', write error')
    end
  end
end { readU8G } ;


(* Read a string of fixed length. Raise an exception at EOF.
*)
function readN(n: integer= 1): ansistring;

const
  thisName= 'readN()';

var
  r: integer;

begin
{$ifdef HAS_CURRENTROUTINE }
  Assert(thisName = {$I %CURRENTROUTINE%} + '()', 'Internal error: bad name in ' + {$I %CURRENTROUTINE%} + '()');
{$endif HAS_CURRENTROUTINE }
  startRead(FilePos(pesIn));
  SetLength(result, n);
  if n > 0 then begin
    BlockRead(pesIn, result[1], n, r);
    if r <> n then
      raise Exception.Create('In ' + thisName + ', unexpected EOF');
    doneRead(result);

(* The result might be adjusted for endianness, but is always returned without  *)
(* other modification so that the parser can validate the content of the file.  *)
(* If any systematic modification is to be done in response to a command-line   *)
(* option it will affect what is written to a binary output file, but the text  *)
(* output for user inspection will be unaffected although a comment might be    *)
(* inserted.                                                                    *)

    if TFileRec(pesOut).Handle > notOpen then begin
      BlockWrite(pesOut, result[1], Length(result), r);
      if r <> Length(result) then
        raise Exception.Create('In ' + thisName + ', write error')
    end
  end
end { readN } ;


(* Read a length byte followed by a string (i.e. this is a "Pascal-style" or
  "counted" string with a 16-bit length). Raise an exception at EOF.
*)
function readC(): ansistring;

const
  thisName= 'readC()';

var
  n: word;
  r: integer;

begin
{$ifdef HAS_CURRENTROUTINE }
  Assert(thisName = {$I %CURRENTROUTINE%} + '()', 'Internal error: bad name in ' + {$I %CURRENTROUTINE%} + '()');
{$endif HAS_CURRENTROUTINE }
  n := readU16();                       (* Note: handles own output etc.        *)
  startRead(FilePos(pesIn));
  try
    SetLength(result, n);
    if n > 0 then begin
      BlockRead(pesIn, result[1], n, r);
      if r <> n then
        raise Exception.Create('In ' + thisName + ', unexpected EOF');
    end
  except
    raise Exception.Create('In ' + thisName + ', unexpected EOF')
  end;
  doneRead(result);

(* The result might be adjusted for endianness, but is always returned without  *)
(* other modification so that the parser can validate the content of the file.  *)
(* If any systematic modification is to be done in response to a command-line   *)
(* option it will affect what is written to a binary output file, but the text  *)
(* output for user inspection will be unaffected although a comment might be    *)
(* inserted.                                                                    *)

  if TFileRec(pesOut).Handle > notOpen then begin
    BlockWrite(pesOut, result[1], Length(result), r);
    if r <> Length(result) then
      raise Exception.Create('In ' + thisName + ', write error')
  end
end { readC } ;


(* Read a string terminated by a zero byte. Raise an exception at EOF.
*)
function readZ(): ansistring;

const
  thisName= 'readZ()';

var
  n: byte;
  r: integer;

begin
{$ifdef HAS_CURRENTROUTINE }
  Assert(thisName = {$I %CURRENTROUTINE%} + '()', 'Internal error: bad name in ' + {$I %CURRENTROUTINE%} + '()');
{$endif HAS_CURRENTROUTINE }
  startRead(FilePos(pesIn));
  result := '';
  BlockRead(pesIn, n, 1, r);
  if r <> 1 then
    raise Exception.Create('In ' + thisName + ', unexpected EOF');
  while n <> 0 do begin
    result := Chr(n);
    BlockRead(pesIn, n, 1, r);
    if r <> 1 then
      raise Exception.Create('In ' + thisName + ', unexpected EOF')
  end;
  doneRead(result + #$00);

(* The result might be adjusted for endianness, but is always returned without  *)
(* other modification so that the parser can validate the content of the file.  *)
(* If any systematic modification is to be done in response to a command-line   *)
(* option it will affect what is written to a binary output file, but the text  *)
(* output for user inspection will be unaffected although a comment might be    *)
(* inserted.                                                                    *)

  if TFileRec(pesOut).Handle > notOpen then begin
    BlockWrite(pesOut, result[1], Length(result), r);
    if r <> Length(result) then
      raise Exception.Create('In ' + thisName + ', write error');
    n := 0;
    BlockWrite(pesOut, n, 1, r);
    if r <> 1 then
      raise Exception.Create('In ' + thisName + ', write error')
  end
end { readZ } ;


(* Unpack a one- or two-byte half-stitch, assuming that the end-of-section case
  (command being 0xff) has already been handled. Call it first with only the
  first byte, if this indicates that a second byte is needed then the result's
  command field will be set to 0xff.
*)
function unpackStitch(both: boolean; first, second: byte): pecStitch;

var
  w: word;

begin
  result.command := $ff;
  result.ordinate := 0;
{$push }
{$r- }
  if first and $80 = $00 then begin
    result.command := $00;
    w := first;
    if w and $0040 <> $0000 then        (* Sign-extend if necessary             *)
      w := w or $ff80;
    result.ordinate := shortint(w)
  end else

(* If we don't have two bytes then fall through returning $ff in the command    *)
(* field which will result in the second byte being read and this function      *)
(* called a second time.                                                        *)

    if both then begin
      result.command := first and $f0;
      w := ((first and $0f) << 8) or second;
      if w and $0800 <> $0000 then      (* Sign-extend if necessary             *)
        w := w or $f000;
      result.ordinate := smallint(w)
    end
{$pop  }
end { unpackStitch } ;


procedure testUnpackStitch();

var
  stitch: pecStitch;

begin
  stitch := unpackStitch(false, $00, $00);
  Assert((stitch.command = $00) and (stitch.ordinate = 0), 'Internal error: failed to unpack short 0');
  stitch := unpackStitch(false, $01, $00);
  Assert((stitch.command = $00) and (stitch.ordinate = 1), 'Internal error: failed to unpack short 1');
  stitch := unpackStitch(false, $3f, $00);
  Assert((stitch.command = $00) and (stitch.ordinate = 63), 'Internal error: failed to unpack short 63');

  stitch := unpackStitch(false, $7f, $00);
  Assert((stitch.command = $00) and (stitch.ordinate = -1), 'Internal error: failed to unpack short -1');
  stitch := unpackStitch(false, $40, $00);
  Assert((stitch.command = $00) and (stitch.ordinate = -64), 'Internal error: failed to unpack short -64');

  stitch := unpackStitch(false, $80, $00);
  Assert(stitch.command = $ff);
  stitch := unpackStitch(true, $80, $00);
  Assert((stitch.command = $80) and (stitch.ordinate = 0), 'Internal error: failed to unpack long 0');
  stitch := unpackStitch(false, $80, $ff);
  Assert(stitch.command = $ff);
  stitch := unpackStitch(true, $80, $ff);
  Assert((stitch.command = $80) and (stitch.ordinate = 255), 'Internal error: failed to unpack long 255');
  stitch := unpackStitch(false, $81, $00);
  Assert(stitch.command = $ff);
  stitch := unpackStitch(true, $81, $00);
  Assert((stitch.command = $80) and (stitch.ordinate = 256), 'Internal error: failed to unpack long 256');
  stitch := unpackStitch(false, $87, $ff);
  Assert(stitch.command = $ff);
  stitch := unpackStitch(true, $87, $ff);
  Assert((stitch.command = $80) and (stitch.ordinate = 2047), 'Internal error: failed to unpack long 2047');

  stitch := unpackStitch(false, $8f, $01);
  Assert(stitch.command = $ff);
  stitch := unpackStitch(true, $8f, $01);
  Assert((stitch.command = $80) and (stitch.ordinate = -255), 'Internal error: failed to unpack long -255');
  stitch := unpackStitch(false, $8f, $00);
  Assert(stitch.command = $ff);
  stitch := unpackStitch(true, $8f, $00);
  Assert((stitch.command = $80) and (stitch.ordinate = -256), 'Internal error: failed to unpack long -256');
  stitch := unpackStitch(false, $88, $00);
  Assert(stitch.command = $ff);
  stitch := unpackStitch(true, $88, $00);
  Assert((stitch.command = $80) and (stitch.ordinate = -2048), 'Internal error: failed to unpack long -2048')
end { testUnpackStitch } ;


(* Read either one or two bytes comprising a stitch ordinate (signed) and
  optional command bits masked into a separate byte.
*)
function readQ(stitch: longint; x: boolean): pecStitch;

const
  thisName= 'readQ()';

var
  r: integer;
  b1, b2: byte;                         (* For command and optional ordinate    *)
  twoBytes: boolean= false;

begin
{$ifdef HAS_CURRENTROUTINE }
  Assert(thisName = {$I %CURRENTROUTINE%} + '()', 'Internal error: bad name in ' + {$I %CURRENTROUTINE%} + '()');
{$endif HAS_CURRENTROUTINE }
  startRead(FilePos(pesIn));
  result.command := $ff;                (* Defaults to end of sequence          *)
  result.ordinate := 0;
  BlockRead(pesIn, b1, 1, r);
  if r <> 1 then
    raise Exception.Create('In ' + thisName + ', unexpected EOF');
  dumpRead(b1);
  if b1 <> $ff then begin               (* Not end of sequence                  *)
    result := unpackStitch(false, b1, 0);
    if result.command = $ff then begin  (* Needs second byte                    *)
      BlockRead(pesIn, b2, 1, r);
      if r <> 1 then
        raise Exception.Create('In ' + thisName + ', unexpected EOF');
      dumpRead(b2);
      twoBytes := true;
      result := unpackStitch(true, b1, b2)
    end
  end;
  doneReadHexAscii;

(* The result might be adjusted for endianness, but is always returned without  *)
(* other modification so that the parser can validate the content of the file.  *)
(* If any systematic modification is to be done in response to a command-line   *)
(* option it will affect what is written to a binary output file, but the text  *)
(* output for user inspection will be unaffected although a comment might be    *)
(* inserted.                                                                    *)

  if TFileRec(pesOut).Handle > notOpen then begin

(* A trim command is ax xx, optionally convert this to a pause cx xx. Assuming  *)
(* that a standard PES/PEC file has a trim on both x and y, this tentatively    *)
(* only changes the second so as not to do a double pause lest the embroidery   *)
(* chooses to obey both.                                                        *)

(* ***** This turns out to crash an Innovis-97E when loaded.                    *)

    if twoBytes and optionTrimToPause and (b1 and $f0 = $a0) and not x then begin
      b1 := $c0;
      b2 := $00;
      if x then
        WriteLn('# Trim at ', stitch + Ord(x), ' x rewritten to pause')
      else
        WriteLn('# Trim at ', stitch + Ord(x), ' y rewritten to pause')
    end;

(* Alternatively yry a colour change, although I don't know how safe this is    *)
(* when there's not an adequate series of prededined colours.                   *)

(* ***** This turns out to crash an Innovis-97E when loaded.                    *)

    if twoBytes and optionTrimToChange and (b1 and $f0 = $a0) then begin
      if x then begin
        b1 := $fe;
        b2 := $b0;
        WriteLn('# Trim at ', stitch + Ord(x), ' x rewritten to colour change')
      end else begin
        b1 := $80;
        if not Odd(countPecTrimCommands div 2) then
          b2 := $01
        else
          b2 := $02;
        WriteLn('# Trim at ', stitch + Ord(x), ' y rewritten to dummy parameter')
      end
    end;

    BlockWrite(pesOut, b1, 1, r);
    if r <> 1 then
      raise Exception.Create('In ' + thisName + ', write error');
    if twoBytes then begin
      BlockWrite(pesOut, b2, 1, r);
      if r <> 1 then
        raise Exception.Create('In ' + thisName + ', write error')
    end
  end
end { readQ } ;


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
      hdr += arrow;
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
  thisName= 'pec_stitchListSubsection';

var
  backtrack: int64;
  count, colour, ignoreOrdinates: integer;
  stitch: pecStitch;
  x: longint= 0;
  y: longint= 0;

begin
{$ifdef HAS_CURRENTROUTINE }
  Assert(thisName = {$I %CURRENTROUTINE%}, 'Internal error: bad name in ' + {$I %CURRENTROUTINE%});
{$endif HAS_CURRENTROUTINE }
  result := false;
  pushRule(thisName);
  backtrack := FilePos(pesIn);
  header;
  WriteLn('Colour: [1] ', thumbnailColourMap[1]);
  count := 0;
  colour := 1;
  ignoreOrdinates := 0;
  stitch := readQ(count div 2 + 1, Odd(count));
  while stitch.command <> $ff do begin
    Write('Stitch ', count div 2 + 1);

(* A colour change is documented as two bytes $fe $b0, after they've been       *)
(* decoded to a command and an ordinate they're $f0 and -336 respectively. What *)
(* is and what isn't counted as a valid half-stitch here is a bit of a hack but *)
(* appears to produce the right result when compared with what's in the PES.    *)

// Optimisation/command here: suppress colour change if it's actually the same colour.

    if (stitch.command = { $fe } $f0) and (stitch.ordinate = { $b0 } -336) then begin
      Write(' colour change from [', colour, '] ', thumbnailColourMap[colour]);
      colour += 1;
      Write(' to [', colour, '] ', thumbnailColourMap[colour], ',');
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
    stitch := readQ(count div 2 + 1, Odd(count));
    count += 1
  end;
  WriteLn('End of stitch sequence');
  WriteLn(up + 'OK ', popRule());
  result := true
end { pec_stitchListSubsection } ;


(* Parse the PEC thumbnail section.
*)
function pec_thumbnailImageSubsection(): boolean;

const
  thisName= 'pec_thumbnailImageSubsection';

var
  backtrack: int64;
  i: integer;

begin
{$ifdef HAS_CURRENTROUTINE }
  Assert(thisName = {$I %CURRENTROUTINE%}, 'Internal error: bad name in ' + {$I %CURRENTROUTINE%});
{$endif HAS_CURRENTROUTINE }
  result := false;
  pushRule(thisName);
  backtrack := FilePos(pesIn);
  header;
  if FilePos(pesIn) <> pecThumbnailByteOffset then begin
    WriteLn('*** In ', peekRule(), ': thumbnail image isn''t contiguous with stitchlist');
    WriteLn(up + 'Backtrack ', popRule());
    Seek(pesIn, backtrack);
    exit
  end;
  for i := 0 to thumbnailColours do begin
    WriteLn('Thumbnail colour: ', i);
    readU8G(thumbnailWidth, thumbnailHeight, i)
  end;
  WriteLn(up + 'OK ', popRule());
  result := true
end { pec_thumbnailImageSubsection } ;


(* Parse the PEC header.
*)
function pec_header(): boolean;

const
  thisName= 'pec_header';

var
  backtrack: int64;
  i, v: integer;

begin
{$ifdef HAS_CURRENTROUTINE }
  Assert(thisName = {$I %CURRENTROUTINE%}, 'Internal error: bad name in ' + {$I %CURRENTROUTINE%});
{$endif HAS_CURRENTROUTINE }
  result := false;
  pushRule(thisName);
  backtrack := FilePos(pesIn);
  header;
  if readN(3) <> 'LA:' then begin
    WriteLn('*** In ', peekRule(), ': bad PEC magic number');
    WriteLn(up + 'Backtrack ', popRule());
    Seek(pesIn, backtrack);
    exit
  end;
  readN(16);
  if readN(1) <> #$0d then begin
    WriteLn('*** In ', peekRule(), ': bad PEC name termination');
    WriteLn(up + 'Backtrack ', popRule());
    Seek(pesIn, backtrack);
    exit
  end;
  readU8N(12);
  readU16N(1);
  thumbnailWidth := readU8();
  WriteLn('Thumbnail width (bytes): ', thumbnailWidth);
  thumbnailHeight := readU8();
  WriteLn('Thumbnail height (rows): ', thumbnailHeight);
  readU8N(12);
  for i := 0 to 255 do
    thumbnailColourMap[i] := -1;
  thumbnailColours := readU8();
  WriteLn('Thumbnail colours (-1): ', thumbnailColours);
  thumbnailColours := (thumbnailColours + 1) mod 256;
  for i := 0 to thumbnailColours - 1 do begin
    v := readU8();
    WriteLn('Thumbnail colour ', i, ': ', v, ' (', colourName(v), ')');
    if i <= 255 then
      thumbnailColourMap[i] := v
  end;
  readU8N(462 - (thumbnailColours - 1));
  WriteLn(up + 'OK ', popRule());
  result := true
end { pec_header } ;


(* Parse the PEC body, comprising stitchlist and thumbnail bitmaps.
*)
function pec_body(): boolean;

const
  thisName= 'pec_body';

var
  backtrack: int64;
  v, width, height: integer;

begin
{$ifdef HAS_CURRENTROUTINE }
  Assert(thisName = {$I %CURRENTROUTINE%}, 'Internal error: bad name in ' + {$I %CURRENTROUTINE%});
{$endif HAS_CURRENTROUTINE }
  result := false;
  pushRule(thisName);
  backtrack := FilePos(pesIn);
  header;
  if FilePos(pesIn) <> pecSectionByteOffset + 512 then begin
    WriteLn('*** In ', peekRule(), ': bad PEC header padding length');
    WriteLn(up + 'Backtrack ', popRule());
    Seek(pesIn, backtrack);
    exit
  end;
  readS16();
  v := readU16();
  pecThumbnailByteOffset := pecSectionByteOffset + v + 512;
  WriteLn('Thumbnail image offset: ', v, ' (0x', HexStr(pecThumbnailByteOffset, 6), ')');
  readU16N(2);
  width := readS16();
  WriteLn('Width: ', width);
  height := readS16();
  WriteLn('height: ', height);
  readU16N(2);
  if not pec_stitchListSubsection() then begin
{$ifdef ERROR2 }
    WriteLn('*** In ', peekRule(), ': unable to parse ', poppedRule);
{$endif ERROR2 }
    WriteLn(up + 'Backtrack ', popRule());
    Seek(pesIn, backtrack);
    exit
  end;
  if not pec_thumbnailImageSubsection() then begin
{$ifdef ERROR2 }
    WriteLn('*** In ', peekRule(), ': unable to parse ', poppedRule);
{$endif ERROR2 }
    WriteLn(up + 'Backtrack ', popRule());
    Seek(pesIn, backtrack);
    exit
  end;
  WriteLn(up + 'OK ', popRule());
  result := true
end { pec_body } ;


(* Parse the PEC header and body.
*)
function pec_part(): boolean;

const
  thisName= 'pec_part';

var
  backtrack: int64;

begin
{$ifdef HAS_CURRENTROUTINE }
  Assert(thisName = {$I %CURRENTROUTINE%}, 'Internal error: bad name in ' + {$I %CURRENTROUTINE%});
{$endif HAS_CURRENTROUTINE }
  result := false;
  pushRule(thisName);
  backtrack := FilePos(pesIn);
  header;
  if not pec_header() then begin
{$ifdef ERROR2 }
    WriteLn('*** In ', peekRule(), ': unable to parse ', poppedRule);
{$endif ERROR2 }
    WriteLn(up + 'Backtrack ', popRule());
    Seek(pesIn, backtrack);
    exit
  end;
  if not pec_body() then begin
{$ifdef ERROR2 }
    WriteLn('*** In ', peekRule(), ': unable to parse ', poppedRule);
{$endif ERROR2 }
    WriteLn(up + 'Backtrack ', popRule());
    Seek(pesIn, backtrack);
    exit
  end;
  WriteLn(up + 'OK ', popRule());
  result := true
end { pec_part } ;


(* Parse a PEC addendum.
*)
function pec_addendum(): boolean;

const
  thisName= 'pec_addendum';

var
  backtrack: int64;

begin
{$ifdef HAS_CURRENTROUTINE }
  Assert(thisName = {$I %CURRENTROUTINE%}, 'Internal error: bad name in ' + {$I %CURRENTROUTINE%});
{$endif HAS_CURRENTROUTINE }
  result := false;
  pushRule(thisName);
  backtrack := FilePos(pesIn);
  header;

// TODO : Fill this in.
WriteLn('In pec_addendum, at ', FilePos(pesIn), ' of total ', FileSize(pesIn));

  WriteLn(up + 'OK ', popRule());
  result := true
end { pec_addendum } ;


(* Parse extents.
*)
function pes_extents(): boolean;

const
  thisName= 'pes_extents';

var
  backtrack: int64;
  v: integer;

begin
{$ifdef HAS_CURRENTROUTINE }
  Assert(thisName = {$I %CURRENTROUTINE%}, 'Internal error: bad name in ' + {$I %CURRENTROUTINE%});
{$endif HAS_CURRENTROUTINE }
  result := false;
  pushRule(thisName);
  backtrack := FilePos(pesIn);
  header;
  v := readS16();
  WriteLn('Extents left: ', v);
  v := readS16();
  WriteLn('Extents top: ', v);
  v := readS16();
  WriteLn('Extents right: ', v);
  v := readS16();
  WriteLn('Extents bottom: ', v);
  v := readS16();
  WriteLn('Extents left position: ', v);
  v := readS16();
  WriteLn('Extents top position: ', v);
  v := readS16();
  WriteLn('Extents right position: ', v);
  v := readS16();
  WriteLn('Extents bottom position: ', v);
  WriteLn(up + 'OK ', popRule());
  result := true
end { pes_extents } ;


(* Parse affine transform.
*)
function pes_affineTransform(): boolean;

const
  thisName= 'pes_affineTransform';

var
  backtrack: int64;
  v: single;

begin
{$ifdef HAS_CURRENTROUTINE }
  Assert(thisName = {$I %CURRENTROUTINE%}, 'Internal error: bad name in ' + {$I %CURRENTROUTINE%});
{$endif HAS_CURRENTROUTINE }
  result := false;
  pushRule(thisName);
  backtrack := FilePos(pesIn);
  header;
  v := readF32();
  WriteLn('Transform scale X: ', v);
  v := readF32();
  WriteLn('Transform skew Y: ', v);
  v := readF32();
  WriteLn('Transform skew X: ', v);
  v := readF32();
  WriteLn('Transform scale Y: ', v);
  v := readF32();
  WriteLn('Transform xlate X: ', v);
  v := readF32();
  WriteLn('Transform xlate Y: ', v);
  WriteLn(up + 'OK ', popRule());
  result := true
end { pes_affinetransform } ;


(* Parse block geometry comprising extents and affine transform.
*)
function pes_blockGeometry(): boolean;

const
  thisName= 'pes_blockGeometry';

var
  backtrack: int64;

begin
{$ifdef HAS_CURRENTROUTINE }
  Assert(thisName = {$I %CURRENTROUTINE%}, 'Internal error: bad name in ' + {$I %CURRENTROUTINE%});
{$endif HAS_CURRENTROUTINE }
  result := false;
  pushRule(thisName);
  backtrack := FilePos(pesIn);
  header;
  if not pes_extents() then begin
{$ifdef ERROR2 }
    WriteLn('*** In ', peekRule(), ': unable to parse ', poppedRule);
{$endif ERROR2 }
    WriteLn(up + 'Backtrack ', popRule());
    Seek(pesIn, backtrack);
    exit
  end;
  if not pes_affineTransform() then begin
{$ifdef ERROR2 }
    WriteLn('*** In ', peekRule(), ': unable to parse ', poppedRule);
{$endif ERROR2 }
    WriteLn(up + 'Backtrack ', popRule());
    Seek(pesIn, backtrack);
    exit
  end;
  WriteLn(up + 'OK ', popRule());
  result := true
end { pes_blockGeometry } ;


(* Parse a CEmbOne section. Because the parser does not have lookahead, the
  magic number was handled by the caller.
*)
function pes_embOne(): boolean;

const
  thisName= 'pes_embOne';

var
  backtrack: int64;
  i, v: integer;

begin
{$ifdef HAS_CURRENTROUTINE }
  Assert(thisName = {$I %CURRENTROUTINE%}, 'Internal error: bad name in ' + {$I %CURRENTROUTINE%});
{$endif HAS_CURRENTROUTINE }
  result := false;
  pushRule(thisName);
  backtrack := FilePos(pesIn);
  header;
  if not pes_blockGeometry() then begin
{$ifdef ERROR2 }
    WriteLn('*** In ', peekRule(), ': unable to parse ', poppedRule);
{$endif ERROR2 }
    WriteLn(up + 'Backtrack ', popRule());
    Seek(pesIn, backtrack);
    exit
  end;
  v := readU16();                       (* Annotated as "'1' (typical)"         *)
  v := readS16();
  WriteLn('CSewSeg x coordinate translation(?): ', v);
  v := readS16();
  WriteLn('CSewSeg y coordinate translation(?): ', v);
  v := readS16();
  WriteLn('CSewSeg width: ', v);
  v := readS16();
  WriteLn('CSewSeg height: ', v);
  readU8N(8);                           (* Padding                              *)
  cSewSegBlockCount := readU16();
  WriteLn('CSewSeg blockCount: ', cSewSegBlockCount);

(* Undocumented padding.                                                        *)

  v := readU16();
  if v <> $ffff then begin
    WriteLn('*** In ', peekRule(), ': unexpected padding (1)');
    WriteLn(up + 'Backtrack ', popRule());
    Seek(pesIn, backtrack);
    exit
  end;
  v := readU16();
  if v <> $0000 then begin
    WriteLn('*** In ', peekRule(), ': unexpected padding (2)');
    WriteLn(up + 'Backtrack ', popRule());
    Seek(pesIn, backtrack);
    exit
  end;
  WriteLn(up + 'OK ', popRule());
  result := true
end { pes_embOne } ;


(* CSewSeg stitch list.
*)
function pes_sewSegStitchList(): boolean;

const
  thisName= 'pes_sewSegStitchList';

var
  backtrack: int64;
  i, t, v, x, y: integer;
{$ifdef FPC }
  stitch: smallintarray;
{$endif FPC }

begin
{$ifdef HAS_CURRENTROUTINE }
  Assert(thisName = {$I %CURRENTROUTINE%}, 'Internal error: bad name in ' + {$I %CURRENTROUTINE%});
{$endif HAS_CURRENTROUTINE }
  result := false;
  pushRule(thisName);
  backtrack := FilePos(pesIn);
  header;
  t := readU16();
  Write('Stitch type: ');
  case t of
    0: WriteLn('normal');
    1: WriteLn('jump');
  otherwise
    WriteLn(t)
  end;
  v := readU16();
  WriteLn('Thread index (+1): ', v);
  v := readU16();
  WriteLn('Number of coordinates: ', v);
  for i := 0 to v - 1 do begin
{$ifdef FPC }
    stitch := readS16N(2);
    WriteLn('Stitch ', i + 1, ': ', stitch[0], ',', stitch[1]);
    if stitch[0] < minPesX then
      minPesX := stitch[0];
    if stitch[0] > maxPesX then
      maxPesX := stitch[0];
    if stitch[1] < minPesY then
      minPesY := stitch[1];
    if stitch[1] > maxPesY then
      maxPesY := stitch[1];
{$else }
    x := readS16();
    y := readS16();
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
  WriteLn(up + 'OK ', popRule());
  result := true
end { pes_sewSegStitchList } ;


(* CSewSeg colo(u)r list.
*)
function pes_sewSegColorList(): boolean;

const
  thisName= 'pes_sewSegColorList';

var
  backtrack: int64;
  v: integer;

begin
{$ifdef HAS_CURRENTROUTINE }
  Assert(thisName = {$I %CURRENTROUTINE%}, 'Internal error: bad name in ' + {$I %CURRENTROUTINE%});
{$endif HAS_CURRENTROUTINE }
  result := false;
  pushRule(thisName);
  backtrack := FilePos(pesIn);
  header;
  v := readU16();
  WriteLn('Block index of change: ', v);
  v := readU16();
  WriteLn('Thread palette/index: ', v);
  countPesColours += 1;
  WriteLn(up + 'OK ', popRule());
  result := true
end { pes_sewSegColorList } ;


(* CSewSeg segment block.
*)
function pes_sewSegSegmentBlock(): boolean;

const
  thisName= 'pes_sewSegSegmentBlock';

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
  Assert(thisName = {$I %CURRENTROUTINE%}, 'Internal error: bad name in ' + {$I %CURRENTROUTINE%});
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
      WriteLn(up + 'Backtrack ', popRule());
      Seek(pesIn, backtrack);
      exit
    end;
    v := readU16();
  until endStitchBlocks();              (* Special repeat-stitch-block code     *)
  while v > 0 do
    if not pes_sewSegColorList() then begin
{$ifdef ERROR2 }
      WriteLn('*** In ', peekRule(), ': unable to parse ', poppedRule);
{$endif ERROR2 }
      WriteLn(up + 'Backtrack ', popRule());
      Seek(pesIn, backtrack);
      exit
    end else
      v -= 1;
  WriteLn(up + 'OK ', popRule());
  result := true
end { pes_sewSegSegmentBlock } ;


(* Parse a CSewSeg section. Because the parser does not have lookahead, the
  magic number was handled by the caller.
*)
function pes_sewSeg(): boolean;

const
  thisName= 'pes_sewSeg';

var
  backtrack: int64;

begin
{$ifdef HAS_CURRENTROUTINE }
  Assert(thisName = {$I %CURRENTROUTINE%}, 'Internal error: bad name in ' + {$I %CURRENTROUTINE%});
{$endif HAS_CURRENTROUTINE }
  result := false;
  pushRule(thisName);
  backtrack := FilePos(pesIn);
  header;
  if not pes_sewSegSegmentBlock() then begin
{$ifdef ERROR2 }
    WriteLn('*** In ', peekRule(), ': unable to parse ', poppedRule);
{$endif ERROR2 }
    WriteLn(up + 'Backtrack ', popRule());
    Seek(pesIn, backtrack);
    exit
  end;
  WriteLn(up + 'OK ', popRule());
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
  thisName= 'pes_body';

var
  backtrack: int64;
  s: string;

begin
{$ifdef HAS_CURRENTROUTINE }
  Assert(thisName = {$I %CURRENTROUTINE%}, 'Internal error: bad name in ' + {$I %CURRENTROUTINE%});
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
        WriteLn(up + 'Backtrack ', popRule());
        Seek(pesIn, backtrack);
        exit
      end;
      if FilePos(pesIn) <> FileSize(pesIn) then
        if not pec_addendum() then begin
{$ifdef ERROR2 }
          WriteLn('*** In ', peekRule(), ': unable to parse ', poppedRule);
{$endif ERROR2 }
          WriteLn(up + 'Backtrack ', popRule());
          Seek(pesIn, backtrack);
          exit
        end
    end else begin

(* Read a counted string, from which the section type may be deduced. Using     *)
(* strings in a case statement like this has been supported by FPC from v2.6,   *)
(* but is probably non-portable.                                                *)

      s := readC();
      case s of
        '':           ;                 (* Padding before PEC part etc.         *)
        'CEmbOne':    if not pes_embOne() then begin
{$ifdef ERROR2 }
                        WriteLn('*** In ', peekRule(), ': unable to parse ', poppedRule);
{$endif ERROR2 }
                        WriteLn(up + 'Backtrack ', popRule());
                        Seek(pesIn, backtrack);
                        exit
                      end;
        'CSewSeg':    if not pes_sewSeg() then begin
{$ifdef ERROR2 }
                        WriteLn('*** In ', peekRule(), ': unable to parse ', poppedRule);
{$endif ERROR2 }
                        WriteLn(up + 'Backtrack ', popRule());
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
        WriteLn(up + 'Backtrack ', popRule());
        Seek(pesIn, backtrack);
        exit
      end
    end
  end;
  WriteLn(up + 'OK ', popRule());
  result := true
end { pes_body } ;


(* Expect a hoop subsection for v2 and later headers.
*)
function pes_hoopsize(): boolean;

const
  thisName= 'pes_hoopsize';

var
  backtrack: int64;
  width, height: word;

begin
{$ifdef HAS_CURRENTROUTINE }
  Assert(thisName = {$I %CURRENTROUTINE%}, 'Internal error: bad name in ' + {$I %CURRENTROUTINE%});
{$endif HAS_CURRENTROUTINE }
  result := false;
  pushRule(thisName);
  backtrack := FilePos(pesIn);
  header;
  width := readU16();
  height := readU16();
  WriteLn('Hoop size: ', width, 'x', height, 'mm');
  if (width > 1000) or (height > 1000) then begin
    WriteLn('*** In ', peekRule(), ': hoop size is unreasonably large');
    WriteLn(up + 'Backtrack ', popRule());
    Seek(pesIn, backtrack);
    exit
  end;
  WriteLn(up + 'OK ', popRule());
  result := true
end { pes_hoopsize } ;


(* Expect a PES v1.0 header.
*)
function pes_header_1x0(): boolean;

const
  thisName= 'pes_header_1x0';

var
  backtrack: int64;
  v: integer;

begin
{$ifdef HAS_CURRENTROUTINE }
  Assert(thisName = {$I %CURRENTROUTINE%}, 'Internal error: bad name in ' + {$I %CURRENTROUTINE%});
{$endif HAS_CURRENTROUTINE }
  result := false;
  pushRule(thisName);
  backtrack := FilePos(pesIn);
  header;
  pecSectionByteOffset := readU32();
  WriteLn('Absolute PEC section byte offset: 0x', hex6(pecSectionByteOffset, ''));
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

  v := readU16();
  case v of
    0: WriteLn('Hoop size: 100x100mm');
    1: WriteLn('Hoop size: 130x180mm')
  otherwise
    WriteLn('Hoop type: ', v)
  end;
  v := readU16();
  WriteLn('Use existing design: ', v);
  segmentBlockCount := readU16();
  WriteLn('Segment block count: ', segmentBlockCount);

(* Undocumented padding.                                                        *)

  v := readU16();
  if v <> $ffff then begin
    WriteLn('*** In ', peekRule(), ': unexpected padding (1)');
    WriteLn(up + 'Backtrack ', popRule());
    Seek(pesIn, backtrack);
    exit
  end;
  v := readU16();
  if v <> $0000 then begin
    WriteLn('*** In ', peekRule(), ': unexpected padding (2)');
    WriteLn(up + 'Backtrack ', popRule());
    Seek(pesIn, backtrack);
    exit
  end;
  WriteLn(up + 'OK ', popRule());
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
  thisName= 'pes_header';

var
  backtrack: int64;
  s: string;

begin
{$ifdef HAS_CURRENTROUTINE }
  Assert(thisName = {$I %CURRENTROUTINE%}, 'Internal error: bad name in ' + {$I %CURRENTROUTINE%});
{$endif HAS_CURRENTROUTINE }
  result := false;
  pushRule(thisName);
  backtrack := FilePos(pesIn);
  header;

(* Read four bytes. If these aren't correct then it can't be a valid header.    *)

  s := readN(4);
  if s <> '#PES' then begin
    WriteLn('Bad PES header signature "', s, '"');
    WriteLn(up + 'Backtrack ', popRule());
    Seek(pesIn, backtrack);
    exit
  end;

(* Read four bytes, from which the header version may be deduced. Using strings *)
(* in a case statement like this has been supported by FPC from v2.6, but is    *)
(* probably non-portable.                                                       *)

  s := readN(4);
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
    WriteLn(up + 'Backtrack ', popRule());
    Seek(pesIn, backtrack);
    exit
  end;
  WriteLn(up + 'OK ', popRule());
  result := true
end { pes_header } ;


(* Expect a correctly-formed PES file, comprising a header and a body. In common
  with all other rules the file should not terminate prematurely, and on exit
  we should find that we are positioned at EOF i.e. there's nothing unexpected
  trailing the body.
*)
function pes_file(): boolean;

  const
  thisName= 'pes_file';

var
  backtrack: int64;

begin
{$ifdef HAS_CURRENTROUTINE }
  Assert(thisName = {$I %CURRENTROUTINE%}, 'Internal error: bad name in ' + {$I %CURRENTROUTINE%});
{$endif HAS_CURRENTROUTINE }
  result := false;
  pushRule(thisName);
  backtrack := FilePos(pesIn);
  header;
  if not pes_header() then begin
{$ifdef ERROR2 }
    WriteLn('*** In ', peekRule(), ': unable to parse ', poppedRule);
{$endif ERROR2 }
    WriteLn(up + 'Backtrack ', popRule());
    Seek(pesIn, backtrack);
    exit;
  end;
  if not pes_body() then begin
{$ifdef ERROR2 }
    WriteLn('*** In ', peekRule(), ': unable to parse ', poppedRule);
{$endif ERROR2 }
    WriteLn(up + 'Backtrack ', popRule());
    Seek(pesIn, backtrack);
    exit
  end;
  WriteLn(up + 'OK ', popRule());
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
  Assert(thisName = {$I %CURRENTROUTINE%}, 'Internal error: bad name in ' + {$I %CURRENTROUTINE%});
{$endif HAS_CURRENTROUTINE }
  result := false;
  pushRule(thisName);
  backtrack := FilePos(pesIn);
  header;
  s := readN(8);
  if s <> '#PEC0001' then begin
    WriteLn('Bad PEC header signature "', s, '"');
    WriteLn(up + 'Backtrack ', popRule());
    Seek(pesIn, backtrack);
    exit
  end;
  pecSectionByteOffset := FilePos(pesIn);
  waitingForPec := false;
  if not pec_part() then begin
{$ifdef ERROR2 }
    WriteLn('*** In ', peekRule(), ': unable to parse ', poppedRule);
{$endif ERROR2 }
    WriteLn(up + 'Backtrack ', popRule());
    Seek(pesIn, backtrack);
    exit
  end;
  if FilePos(pesIn) <> FileSize(pesIn) then
    if not pec_addendum() then begin
{$ifdef ERROR2 }
      WriteLn('*** In ', peekRule(), ': unable to parse ', poppedRule);
{$endif ERROR2 }
      WriteLn(up + 'Backtrack ', popRule());
      Seek(pesIn, backtrack);
      exit
    end;
  WriteLn(up + 'OK ', popRule());
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
  WriteLn(ErrOutput, '        pesdump [options] input_file [output file]');
  WriteLn(ErrOutput);
  WriteLn(ErrOutput, 'The input file name is mandatory, standard input will not be used if it is omitted.');
  WriteLn(ErrOutput, 'The output file name is optional, but requred for most options to be effective.');
  WriteLn(ErrOutput);
  WriteLn(ErrOutput, 'Options:');
  WriteLn(ErrOutput);
  WriteLn(ErrOutput, '  --TrimToPause         Convert trim commands in the PEC section to pause.');
  WriteLn(ErrOutput, '  --TrimToChange        Convert trim commands to colour changes.');
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
  FPCIdent= 'FPC ' + {$I %FPCVERSION%} + ' [' + {$I %FPCDATE%} + '] for ' + {$I %FPCTARGETCPU%} + ' - ' + {$I %FPCTARGETOS%};

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
  Assert(scratch > notOpen, 'Internal error: unexpected output handle');
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
  WriteLn(AddChar('=', '', Length(banner)));
{$else }
  WriteLn(banner);
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
  WriteLn('PEC pause commands: ', countPecPauseCommands);
  WriteLn('PEC trim commands: ', countPecTrimCommands);
  WriteLn('PEC jump commands: ', countPecJumpCommands);
  WriteLn('PEC X range: ', minPecX, '..', maxPecX);
  WriteLn('PEC Y range: ', minPecY, '..', maxPecY);
  WriteLn('PEC colour changes: ', countPecColourChanges);
{$if declared(AddChar) }
  WriteLn(AddChar('=', '', Length(banner)))
{$else }
  WriteLn(banner)
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


begin
  testUnpackStitch;                     (* Fails by assertion on error          *)
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
          '--trimtopause':  optionTrimToPause := true;
          '--trimtochange': optionTrimToChange := true

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
      if optionTrimToPause then
        Write(' --TrimToPause');
      if optionTrimToChange then
        Write(' --TrimToChange');

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

      if (paramCount() >= 1) and not (paramStr(1)[1] in ['+', '-', '=', '@']) then begin
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
(* by offset in the file.

@<num>  Continue to this point in the input file. These must be in numerical order.
-<num>  Delete the indicated number of bytes.
+<bytes etc.> Insert the indicated bytes or stitch locations etc.
=<bytes etc.> Overwrite the indicated bytes or stitch locations etc.
=+      Increment a byte or stitch location etc.
=-      Decrement a byte or stitch location etc.

The actual data manipulation is done at the point where the input file is read,
(look for  function readU8(  etc.) since this has available to it (a) the input
file position (b) the current rule and (c) implicit indication of data type by
virtue of the function parameters.                                          TBD *)

      while (paramCount() >= 1) and (paramStr(1)[1] in ['+', '-', '=', '@']) do
        try
          hasCommands := true;
        finally
        end;
      if hasCommands then begin
        Write('Commands:');
        WriteLn
      end;

(* A file should now be available on standard input. Parse it, summarise the    *)
(* termination condition, and summarise the counters monitoring stitches,       *)
(* embedded commands and so on.                                                 *)

{$if declared(AddChar) }
      WriteLn(AddChar('=', '', Length(banner)));
{$else }
      WriteLn(banner);
{$endif }
      ruleStack := TStringList.Create;
      try
        try
          if pes_file() or pec_file() then begin
            summarise(true);            (* File parsed OK, rule stack empty     *)
            counters
          end else begin
            WriteLn('Unable to parse PES or PEC file');
            summarise(false)            (* Parse error, look at rule stack      *)
          end
        except
          on e: Exception do
            summarise(e.message)        (* Unexpected EOF etc., look at rule stack *)
        end
      finally
        ruleStack.Free
      end
    finally
      if not (hasOptions or hasCommands) then
        if TFileRec(pesOut).Handle > notOpen then
          if FileSize(pesOut) <> FileSize(pesIn) then begin
            WriteLn('#');
            WriteLn('# WARNING: Output file should be the same size as input file');
            WriteLn('#')
          end;
      CloseFile(pesIn);
      if TFileRec(pesOut).Handle > notOpen then
        CloseFile(pesOut)
    end
  finally
    FreeAndNil(params)
  end
end { PesDump }.

