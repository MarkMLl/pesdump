(* FPC 2.6.0 FPC 2.6.0 FPC 2.6.0 FPC 2.6.0 FPC 2.6.0 FPC 2.6.0 FPC 2.6.0 FPC 2. *)

unit MidlevelIO;

(* Mid-level stuff supporting the parser, covered by the same license etc. The  *)
(* entry points are named ReadXXX() but each one has substantial side effects   *)
(* in that it optionally outputs the data to a second file for checking etc.    *)
(* and optionally applies patches at locations identified on the command line.  *)
(*                                                              MarkMLl         *)

{$mode objfpc}{$H+}

interface

uses
  Classes, SysUtils, PatchAndIO;

const
  NotOpen= 0;                           (* Handle value for output file checks  *)

(* Note: these characters might be contentious with old FPC etc. versions that
  aren't happy with UTF-8.
*)
{$ifndef VER3 }
  Dot= '.';
  Arrow= ' -> ';
  Up= '^ ';
{$else        }
  Dot= '·';
  Arrow= ' → ';
  Up= '↑ ';
{$endif VER3  }

(* The banner matches address + 16 hex bytes + padding but should optimise to a
  length if StrUtils is imported, other underlines match the text with which
  they're associated.
*)
  Banner= '========================================================';

type
  PecStitch= record
               command: byte;
               ordinate: longint
             end;

var
  OptionTrimToPause: boolean= false;
  OptionTrimToChange: boolean= false;
  OptionChangeToDummy: boolean= false;

  (* Optional thumbnail colours from the PEC header. These are not necessarily the
    same as the expected thread colours.
  *)
  ThumbnailColourMap: array[0..255] of integer;

(* Read an unsigned 8-bit number.
*)
function ReadU8(var pesIn, pesOut: File): byte;

(* Read an unsigned 16-bit number.
*)
function ReadU16(var pesIn, pesOut: File): word;

(* Read a signed 16-bit number.
*)
function ReadS16(var pesIn, pesOut: File): smallint;

(* Read an unsigned 32-bit number.
*)
function ReadU32(var pesIn, pesOut: File): longword;

(* Read a 32-bit float. PES files appear to use the standard IEEE format, but
  this should not be assumed in the general case.
*)
function ReadF32(var pesIn, pesOut: File): single;

(* Read a block of bytes. This would normally be called for padding etc. and
  any attempt to return a block will probably be non-portable.
*)
function ReadU8N(var pesIn, pesOut: File; n: integer): TScalarArray;

(* Read a block of words. This would normally be called for padding etc. and
  any attempt to return a block will probably be non-portable.
*)
function ReadU16N(var pesIn, pesOut: File; n: integer): TScalarArray;

(* Read a block of words. This would normally be called for padding etc. and
  any attempt to return a block will probably be non-portable.
*)
function ReadS16N(var pesIn, pesOut: File; n: integer): TScalarArray;

(* Read a block of floats. This would normally be called for padding etc. and
  any attempt to return a block will probably be non-portable.
*)
function ReadF32N(var pesIn, pesOut: File; n: integer): TScalarArray; // NOT USED

(* Read and discard a block of bytes. Assume that this represents a thumbnail
  in simple bitmap format and if possible dump it using PNM format rather than
  ASCII.
*)
procedure ReadU8G(var pesIn, pesOut: File; width, height, index: integer);

(* Read a string of fixed length. Raise an exception at EOF.
*)
function ReadN(var pesIn, pesOut: File; n: integer= 1): ansistring;

(* Read a length word followed by a string (i.e. this is a "Pascal-style" or
  "counted" string with a 16-bit length). Raise an exception at EOF.
*)
function ReadC(var pesIn, pesOut: File): ansistring;

(* Read a string terminated by a zero byte. Raise an exception at EOF.
*)
function ReadZ(var pesIn, pesOut: File): ansistring; // NOT USED

(* Used during testing/debugging.
*)
procedure TestUnpackStitch();

(* Read either one or two bytes comprising a stitch ordinate (signed) and
  optional command bits masked into a separate byte. The x parameter indicates
  whether it is the x or y stitch of a pair, the t1 parameter controls the y
  parameter after a trim which should alternate between 1 and 2.
*)
function ReadQ(var pesIn, pesOut: File; stitch: longint; x, t1: boolean): PecStitch;

(* These believed to be from a Brother Innovis 955.
*)
function ColourName(index: integer): string;


implementation

const
  traceTop= (1024 * 1024) - 1;

var
  traceStart, traceBytes: longint;
  trace: array[0..traceTop] of byte;

(********************************************************************************)
(*                                                                              *)
(* Utility procedures: input/output formatting etc. available to all rules.     *)
(*                                                                              *)
(********************************************************************************)

(* Inspection of a PES file indicates that it is little-endian. Exceptions      *)
(* raised in these functions are assumed to be fatal, and to result in a back-  *)
(* trace of the rules that got us here.                                         *)


(* Assuming 16 bytes per row of hex bytes, mark the middle.
*)
function pad(index: integer; bytes: integer= 16): string;

begin
  if index = bytes div 2 - 1 then
    result := Dot
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
    $1f:  result := Dot;
    $7f..
    $ff:  result := Dot
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
// TODO : Data type (U8 etc.) here?
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


(* These believed to be from a Brother Innovis 955.
*)
function ColourName(index: integer): string;

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
end { ColourName } ;


procedure doneReadHexPbm(width, height, index: integer; bytes: integer= 8);

var
  lines, i, j, charsOutput: integer;
  chars: string;


  (* Convert a byte into 0/1 bits, LSB first. Note that IntToBin() does this
    MSB first.
  *)
  function byteToStr(b: byte; bits: integer): string;

{$define MONOSPACED_RELIABLE }

  const
{$ifdef MONOSPACED_RELIABLE }
    mark= Dot;
    space= ' ';
{$else                      }
    mark= '1';
    space= '0';
{$endif MONOSPACED_RELIABLE }

  begin
    result := '';
    while bits > 0 do begin
      if Odd(b) then
        result += mark
      else
        result += space;
      b := b >> 1;
      bits -= 1
    end
  end { byteToStr } ;


begin
  for i := 1 to 7 + (3 * bytes) + 1 do
    chars += ' ';
  WriteLn(chars, '|P1');
  Write(chars, '|# Thumbnail ', index);
  if (index <= 255) and (ThumbnailColourMap[index] <> -1) then
    WriteLn(', colour ', ThumbnailColourMap[index], ' (',
                                ColourName(ThumbnailColourMap[index]), ')')
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
// TODO : Data type (U8 etc.) here?
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
function ReadU8(var pesIn, pesOut: File): byte;

const
  thisName= 'ReadU8()';
  sz= SizeOf(byte);

var
  patchLoc: longint;
  buffer: TScalar;

begin
{$ifdef HAS_CURRENTROUTINE }
  Assert(thisName = {$I %CURRENTROUTINE%} + '()', 'Internal error: bad name in ' +
                                                {$I %CURRENTROUTINE%} + '()');
{$endif HAS_CURRENTROUTINE }
  Assert(sz = 1, 'Internal error: bad U8 size');
  Assert(SizeOf(result) = sz, 'Internal error: bad U8 result size');
  Assert(SizeOf(buffer.u8) = sz, 'Internal error: bad U8 buffer size');
  patchLoc := FilePos(pesIn);
  startRead(patchLoc);
  StartPatch(patchLoc);
  ReadScalar(pesIn, thisName, buffer, sz);
  result := buffer.u8;
  doneRead(buffer.u8);

(* The result might be adjusted for endianness, but is always returned without  *)
(* other modification so that the parser can validate the content of the file.  *)
(* If any systematic modification is to be done in response to a command-line   *)
(* option it will affect what is written to a binary output file, but the text  *)
(* output for user inspection will be unaffected although a comment might be    *)
(* inserted.                                                                    *)

  if TFileRec(pesOut).Handle > NotOpen then
    if PatchVerb(patchLoc) <> PatchNone then
      PatchAndWriteScalar(pesOut, thisName, buffer, sz, 'U8', patchLoc)
    else
      WriteScalar(pesOut, thisName, buffer, sz)
end { ReadU8 } ;


(* Read an unsigned 16-bit number.
*)
function ReadU16(var pesIn, pesOut: File): word;

const
  thisName= 'ReadU16()';
  sz= SizeOf(word);

var
  patchLoc: longint;
  buffer: TScalar;

begin
{$ifdef HAS_CURRENTROUTINE }
  Assert(thisName = {$I %CURRENTROUTINE%} + '()', 'Internal error: bad name in ' +
                                                {$I %CURRENTROUTINE%} + '()');
{$endif HAS_CURRENTROUTINE }
  Assert(sz = 2, 'Internal error: bad U16 size');
  Assert(SizeOf(result) = sz, 'Internal error: bad U16 result size');
  Assert(SizeOf(buffer.u16) = sz, 'Internal error: bad U16 buffer size');
  patchLoc := FilePos(pesIn);
  startRead(patchLoc);
  StartPatch(patchLoc);
  ReadScalar(pesIn, thisName, buffer, sz);
  result := LEtoN(buffer.u16);
  doneRead(buffer.u16);

(* The result might be adjusted for endianness, but is always returned without  *)
(* other modification so that the parser can validate the content of the file.  *)
(* If any systematic modification is to be done in response to a command-line   *)
(* option it will affect what is written to a binary output file, but the text  *)
(* output for user inspection will be unaffected although a comment might be    *)
(* inserted.                                                                    *)

  if TFileRec(pesOut).Handle > NotOpen then
    if PatchVerb(patchLoc) <> PatchNone then
      PatchAndWriteScalar(pesOut, thisName, buffer, sz, 'U16', patchLoc)
    else
      WriteScalar(pesOut, thisName, buffer, sz)
end { ReadU16 } ;


(* Read a signed 16-bit number.
*)
function ReadS16(var pesIn, pesOut: File): smallint;

const
  thisName= 'ReadS16()';
  sz= SizeOf(smallint);

var
  patchLoc: longint;
  buffer: TScalar;

begin
{$ifdef HAS_CURRENTROUTINE }
  Assert(thisName = {$I %CURRENTROUTINE%} + '()', 'Internal error: bad name in ' +
                                                {$I %CURRENTROUTINE%} + '()');
{$endif HAS_CURRENTROUTINE }
  Assert(sz = 2, 'Internal error: bad S16 size');
  Assert(SizeOf(result) = sz, 'Internal error: bad S16 result size');
  Assert(SizeOf(buffer.s16) = sz, 'Internal error: bad S16 buffer size');
  patchLoc := FilePos(pesIn);
  startRead(patchLoc);
  StartPatch(patchLoc);
  ReadScalar(pesIn, thisName, buffer, sz);
  result := LEtoN(buffer.s16);
  doneRead(buffer.s16);

(* The result might be adjusted for endianness, but is always returned without  *)
(* other modification so that the parser can validate the content of the file.  *)
(* If any systematic modification is to be done in response to a command-line   *)
(* option it will affect what is written to a binary output file, but the text  *)
(* output for user inspection will be unaffected although a comment might be    *)
(* inserted.                                                                    *)

  if TFileRec(pesOut).Handle > NotOpen then
    if PatchVerb(patchLoc) <> PatchNone then
      PatchAndWriteScalar(pesOut, thisName, buffer, sz, 'S16', patchLoc)
    else
      WriteScalar(pesOut, thisName, buffer, sz)
end { ReadS16 } ;


(* Read an unsigned 32-bit number.
*)
function ReadU32(var pesIn, pesOut: File): longword;

const
  thisName= 'ReadU32()';
  sz= SizeOf(longword);

var
  patchLoc: longint;
  buffer: TScalar;

begin
{$ifdef HAS_CURRENTROUTINE }
  Assert(thisName = {$I %CURRENTROUTINE%} + '()', 'Internal error: bad name in ' +
                                                {$I %CURRENTROUTINE%} + '()');
{$endif HAS_CURRENTROUTINE }
  Assert(sz = 4, 'Internal error: bad U32 size');
  Assert(SizeOf(result) = sz, 'Internal error: bad U32 result size');
  Assert(SizeOf(buffer.u32) = sz, 'Internal error: bad U32 buffer size');
  patchLoc := FilePos(pesIn);
  startRead(patchLoc);
  StartPatch(patchLoc);
  ReadScalar(pesIn, thisName, buffer, sz);
  result := LEtoN(buffer.u32);
  doneRead(buffer.u32);

(* The result might be adjusted for endianness, but is always returned without  *)
(* other modification so that the parser can validate the content of the file.  *)
(* If any systematic modification is to be done in response to a command-line   *)
(* option it will affect what is written to a binary output file, but the text  *)
(* output for user inspection will be unaffected although a comment might be    *)
(* inserted.                                                                    *)

  if TFileRec(pesOut).Handle > NotOpen then
    if PatchVerb(patchLoc) <> PatchNone then
      PatchAndWriteScalar(pesOut, thisName, buffer, sz, 'U32', patchLoc)
    else
      WriteScalar(pesOut, thisName, buffer, sz)
end { ReadU32 } ;


(* Read a 32-bit float. PES files appear to use the standard IEEE format, but
  this should not be assumed in the general case.
*)
function ReadF32(var pesIn, pesOut: File): single;

const
  thisName= 'ReadF32()';
  sz= SizeOf(single);

var
  patchLoc: longint;
  buffer: TScalar;

begin
{$ifdef HAS_CURRENTROUTINE }
  Assert(thisName = {$I %CURRENTROUTINE%} + '()', 'Internal error: bad name in ' +
                                                {$I %CURRENTROUTINE%} + '()');
{$endif HAS_CURRENTROUTINE }
  Assert(sz = 4, 'Internal error: bad F32 size');
  Assert(SizeOf(result) = sz, 'Internal error: bad F32 result size');
  Assert(SizeOf(buffer.f32) = sz, 'Internal error: bad F32 buffer size');
  patchLoc := FilePos(pesIn);
  startRead(patchLoc);
  StartPatch(patchLoc);
  ReadScalar(pesIn, thisName, buffer, sz);
  doneRead(buffer.f32);                 (* Dump before in-situ endianness swap  *)
  buffer.u32 := LEtoN(buffer.u32);
  result := buffer.f32;

(* The result might be adjusted for endianness, but is always returned without  *)
(* other modification so that the parser can validate the content of the file.  *)
(* If any systematic modification is to be done in response to a command-line   *)
(* option it will affect what is written to a binary output file, but the text  *)
(* output for user inspection will be unaffected although a comment might be    *)
(* inserted.                                                                    *)

  if TFileRec(pesOut).Handle > NotOpen then begin
    buffer.u32 := NtoLE(buffer.u32);
    if PatchVerb(patchLoc) <> PatchNone then
// TODO : This patch variant untested
      PatchAndWriteScalar(pesOut, thisName, buffer, sz, 'F32', patchLoc)
    else
      WriteScalar(pesOut, thisName, buffer, sz)
  end
end { ReadF32 } ;


(* Read a block of bytes. This would normally be called for padding etc. and
  any attempt to return a block will probably be non-portable.
*)
function ReadU8N(var pesIn, pesOut: File; n: integer): TScalarArray;

const
  thisName= 'ReadU8N()';
  sfx= 'U8';
  sz= 1;

var
  patchLoc: longint;
  i: integer;

begin
{$ifdef HAS_CURRENTROUTINE }
  Assert(thisName = {$I %CURRENTROUTINE%} + '()', 'Internal error: bad name in ' +
                                                {$I %CURRENTROUTINE%} + '()');
{$endif HAS_CURRENTROUTINE }
  patchLoc := FilePos(pesIn);
  startRead(patchLoc);
  StartPatch(patchLoc);
  SetLength(result, n);
  if n > 0 then begin
    readVector(pesIn, thisName, result, sz);
    for i := 0 to Length(result) - 2 do
      dumpRead(result[i].u8);
    doneRead(result[Length(result) - 1].u8);

(* The result might be adjusted for endianness, but is always returned without  *)
(* other modification so that the parser can validate the content of the file.  *)
(* If any systematic modification is to be done in response to a command-line   *)
(* option it will affect what is written to a binary output file, but the text  *)
(* output for user inspection will be unaffected although a comment might be    *)
(* inserted.                                                                    *)

    if TFileRec(pesOut).Handle > NotOpen then
      if PatchVerb(patchLoc) <> PatchNone then
        patchAndWriteVector(pesOut, thisName, result, sz, sfx, patchLoc)
      else
        writeVector(pesOut, thisName, result, sz)
  end
end { ReadU8N } ;


(* Read a block of words. This would normally be called for padding etc. and
  any attempt to return a block will probably be non-portable.
*)
function ReadU16N(var pesIn, pesOut: File; n: integer): TScalarArray;

const
  thisName= 'ReadU16N()';
  sfx= 'U16';
  sz= 2;

var
  patchLoc: longint;
  i: integer;

begin
{$ifdef HAS_CURRENTROUTINE }
  Assert(thisName = {$I %CURRENTROUTINE%} + '()', 'Internal error: bad name in ' +
                                                {$I %CURRENTROUTINE%} + '()');
{$endif HAS_CURRENTROUTINE }
  patchLoc := FilePos(pesIn);
  startRead(patchLoc);
  StartPatch(patchLoc);
  SetLength(result, n);
  if n > 0 then begin
    readVector(pesIn, thisName, result, sz);
    for i := 0 to Length(result) - 2 do
      dumpRead(result[i].u16);
    doneRead(result[Length(result) - 1].u16);

(* The result might be adjusted for endianness, but is always returned without  *)
(* other modification so that the parser can validate the content of the file.  *)
(* If any systematic modification is to be done in response to a command-line   *)
(* option it will affect what is written to a binary output file, but the text  *)
(* output for user inspection will be unaffected although a comment might be    *)
(* inserted.                                                                    *)

    if TFileRec(pesOut).Handle > NotOpen then
      if PatchVerb(patchLoc) <> PatchNone then
        patchAndWriteVector(pesOut, thisName, result, sz, sfx, patchLoc)
      else
        writeVector(pesOut, thisName, result, sz)
  end
end { ReadU16N } ;


(* Read a block of words. This would normally be called for padding etc. and
  any attempt to return a block will probably be non-portable.
*)
function ReadS16N(var pesIn, pesOut: File; n: integer): TScalarArray;

const
  thisName= 'ReadS16N()';
  sfx= 'S16';
  sz= 2;

var
  patchLoc: longint;
  i: integer;

begin
{$ifdef HAS_CURRENTROUTINE }
  Assert(thisName = {$I %CURRENTROUTINE%} + '()', 'Internal error: bad name in ' +
                                                {$I %CURRENTROUTINE%} + '()');
{$endif HAS_CURRENTROUTINE }
  patchLoc := FilePos(pesIn);
  startRead(patchLoc);
  StartPatch(patchLoc);
  SetLength(result, n);
  if n > 0 then begin
    readVector(pesIn, thisName, result, sz);
    for i := 0 to Length(result) - 2 do
      dumpRead(result[i].s16);
    doneRead(result[Length(result) - 1].s16);

(* The result might be adjusted for endianness, but is always returned without  *)
(* other modification so that the parser can validate the content of the file.  *)
(* If any systematic modification is to be done in response to a command-line   *)
(* option it will affect what is written to a binary output file, but the text  *)
(* output for user inspection will be unaffected although a comment might be    *)
(* inserted.                                                                    *)

    if TFileRec(pesOut).Handle > NotOpen then
      if PatchVerb(patchLoc) <> PatchNone then
        patchAndWriteVector(pesOut, thisName, result, sz, sfx, patchLoc)
      else
        writeVector(pesOut, thisName, result, sz)
  end
end { ReadS16N } ;


(* Read a block of floats. This would normally be called for padding etc. and
  any attempt to return a block will probably be non-portable.
*)
function ReadF32N(var pesIn, pesOut: File; n: integer): TScalarArray; // NOT USED

const
  thisName= 'ReadF32N()';
  sfx= 'F32';
  sz= 4;

var
  patchLoc: longint;
  i: integer;

begin
{$ifdef HAS_CURRENTROUTINE }
  Assert(thisName = {$I %CURRENTROUTINE%} + '()', 'Internal error: bad name in ' +
                                                {$I %CURRENTROUTINE%} + '()');
{$endif HAS_CURRENTROUTINE }
  patchLoc := FilePos(pesIn);
  startRead(patchLoc);
  StartPatch(patchLoc);
  SetLength(result, n);
  if n > 0 then begin
    readVector(pesIn, thisName, result, sz);
    for i := 0 to Length(result) - 2 do
      dumpRead(result[i].f32);
    doneRead(result[Length(result) - 1].f32);

(* The result might be adjusted for endianness, but is always returned without  *)
(* other modification so that the parser can validate the content of the file.  *)
(* If any systematic modification is to be done in response to a command-line   *)
(* option it will affect what is written to a binary output file, but the text  *)
(* output for user inspection will be unaffected although a comment might be    *)
(* inserted.                                                                    *)

    if TFileRec(pesOut).Handle > NotOpen then
      if PatchVerb(patchLoc) <> PatchNone then
        patchAndWriteVector(pesOut, thisName, result, sz, sfx, patchLoc)
      else
        writeVector(pesOut, thisName, result, sz)
  end
end { ReadF32N } ;


(* Read and discard a block of bytes. Assume that this represents a thumbnail
  in simple bitmap format and if possible dump it using PNM format rather than
  ASCII.
*)
procedure ReadU8G(var pesIn, pesOut: File; width, height, index: integer);

const
  thisName= 'ReadU8G()';
  sfx= 'U8';
  sz= 1;

var
  patchLoc: longint;
  bitmap: TScalarArray;
  i: integer;

begin
{$ifdef HAS_CURRENTROUTINE }
  Assert(thisName = {$I %CURRENTROUTINE%} + '()', 'Internal error: bad name in ' +
                                                {$I %CURRENTROUTINE%} + '()');
{$endif HAS_CURRENTROUTINE }
  patchLoc := FilePos(pesIn);
  startRead(patchLoc);
  StartPatch(patchLoc);
  SetLength(bitmap, width * height);
  if width * height > 0 then begin
    readVector(pesIn, thisName, bitmap, sz);
    for i := 0 to Length(bitmap) - 1 do
      dumpRead(bitmap[i].u8);
    doneReadHexPbm(width * 8, height, index, width);

(* The result might be adjusted for endianness, but is always returned without  *)
(* other modification so that the parser can validate the content of the file.  *)
(* If any systematic modification is to be done in response to a command-line   *)
(* option it will affect what is written to a binary output file, but the text  *)
(* output for user inspection will be unaffected although a comment might be    *)
(* inserted.                                                                    *)

    if TFileRec(pesOut).Handle > NotOpen then
      if PatchVerb(patchLoc) <> PatchNone then
        patchAndWriteVector(pesOut, thisName, bitmap, sz, sfx, patchLoc)
      else
        writeVector(pesOut, thisName, bitmap, sz)
  end
end { ReadU8G } ;


(* Read a string of fixed length. Raise an exception at EOF.
*)
function ReadN(var pesIn, pesOut: File; n: integer= 1): ansistring;

const
  thisName= 'ReadN()';

var
  patchLoc: longint;
  r: integer;

begin
{$ifdef HAS_CURRENTROUTINE }
  Assert(thisName = {$I %CURRENTROUTINE%} + '()', 'Internal error: bad name in ' +
                                                {$I %CURRENTROUTINE%} + '()');
{$endif HAS_CURRENTROUTINE }
  patchLoc := FilePos(pesIn);
  startRead(patchLoc);
  StartPatch(patchLoc);
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

    if TFileRec(pesOut).Handle > NotOpen then
      case PatchVerb(patchLoc) of
      patchDelete: if (NextPatchNumberCount() <> n) and (NextPatchNumberCount() <> 0) then
                       raise Exception.Create('In ' + thisName +
                                        ', partial/multiple deletion not supported')
                     else
                       PatchNext;
        PatchNone:   begin
                       BlockWrite(pesOut, result[1], Length(result), r);
                       if r <> Length(result) then
                         raise Exception.Create('In ' + thisName + ', write error')
                     end
      otherwise
        raise Exception.Create('In ' + thisName + ', patch verb not supported')
      end
  end
end { ReadN } ;


(* Read a length word followed by a string (i.e. this is a "Pascal-style" or
  "counted" string with a 16-bit length). Raise an exception at EOF.
*)
function ReadC(var pesIn, pesOut: File): ansistring;

const
  thisName= 'readC()';

var
  patchLoc: longint;
  n: word;
  r: integer;

begin
{$ifdef HAS_CURRENTROUTINE }
  Assert(thisName = {$I %CURRENTROUTINE%} + '()', 'Internal error: bad name in ' +
                                                {$I %CURRENTROUTINE%} + '()');
{$endif HAS_CURRENTROUTINE }
  n := ReadU16(pesIn, pesOut);          (* Note: handles own output etc.        *)
  patchLoc := FilePos(pesIn);
  startRead(patchLoc);
  StartPatch(patchLoc);
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

  if TFileRec(pesOut).Handle > NotOpen then
    case PatchVerb(patchLoc) of
      patchDelete: if (NextPatchNumberCount() <> n) and (NextPatchNumberCount() <> 0) then
                     raise Exception.Create('In ' + thisName +
                                        ', partial/multiple deletion not supported')
                   else
                     PatchNext;
      PatchNone:   begin
                     BlockWrite(pesOut, result[1], Length(result), r);
                     if r <> Length(result) then
                       raise Exception.Create('In ' + thisName + ', write error')
                   end
    otherwise
      raise Exception.Create('In ' + thisName + ', patch verb not supported')
    end
end { readC } ;


(* Read a string terminated by a zero byte. Raise an exception at EOF.
*)
function ReadZ(var pesIn, pesOut: File): ansistring; // NOT USED

const
  thisName= 'readZ()';

var
  patchLoc: longint;
  n: byte;
  r: integer;

begin
{$ifdef HAS_CURRENTROUTINE }
  Assert(thisName = {$I %CURRENTROUTINE%} + '()', 'Internal error: bad name in ' +
                                                {$I %CURRENTROUTINE%} + '()');
{$endif HAS_CURRENTROUTINE }
  patchLoc := FilePos(pesIn);
  startRead(patchLoc);
  StartPatch(patchLoc);
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

  if TFileRec(pesOut).Handle > NotOpen then
    case PatchVerb(patchLoc) of
      patchDelete: if (NextPatchNumberCount() <> n) and (NextPatchNumberCount() <> 0) then
                     raise Exception.Create('In ' + thisName +
                                        ', partial/multiple deletion not supported')
                   else
                     PatchNext;
      PatchNone:   begin
                     BlockWrite(pesOut, result[1], Length(result), r);
                     if r <> Length(result) then
                       raise Exception.Create('In ' + thisName + ', write error');
                     n := 0;
                     BlockWrite(pesOut, n, 1, r);
                     if r <> 1 then
                       raise Exception.Create('In ' + thisName + ', write error')
                   end
    otherwise
      raise Exception.Create('In ' + thisName + ', patch verb not supported')
    end
end { readZ } ;


(* Unpack a one- or two-byte half-stitch, assuming that the end-of-section case
  (command being 0xff) has already been handled. Call it first with only the
  first byte, if this indicates that a second byte is needed then the result's
  command field will be set to 0xff.
*)
function unpackStitch(both: boolean; first, second: byte): PecStitch;

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


(* Used during testing/debugging.
*)
procedure TestUnpackStitch();

var
  stitch: PecStitch;

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
end { TestUnpackStitch } ;


(* Read either one or two bytes comprising a stitch ordinate (signed) and
  optional command bits masked into a separate byte. The x parameter indicates
  whether it is the x or y stitch of a pair, the t1 parameter controls the y
  parameter after a trim which should alternate between 1 and 2.
*)
function ReadQ(var pesIn, pesOut: File; stitch: longint; x, t1: boolean): PecStitch;

const
  thisName= 'ReadQ()';

const
  forceZero: boolean= false;            (* Static variable                      *)

var
  patchLoc: longint;
  r: integer;
  b1, b2: byte;                         (* For command and optional ordinate    *)
  twoBytes: boolean= false;

begin
{$ifdef HAS_CURRENTROUTINE }
  Assert(thisName = {$I %CURRENTROUTINE%} + '()', 'Internal error: bad name in ' +
                                                {$I %CURRENTROUTINE%} + '()');
{$endif HAS_CURRENTROUTINE }
  patchLoc := FilePos(pesIn);
  startRead(patchLoc);
  StartPatch(patchLoc);
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

  if TFileRec(pesOut).Handle > NotOpen then
    case PatchVerb(patchLoc) of
      patchDelete: if not (NextPatchNumberCount() in [0, 1]) then
                       raise Exception.Create('In ' + thisName +
                                        ', partial/multiple deletion not supported')
                   else
                     PatchNext;
      PatchNone:   begin

(* A trim command is ax xx, optionally convert this to a pause cx xx. Assuming  *)
(* that a standard PES/PEC file has a trim on both x and y, this tentatively    *)
(* only changes the second so as not to do a double pause lest the embroidery   *)
(* chooses to obey both.                                                        *)

(* ***** This turns out to crash an Innovis-97E when loaded.                    *)

                     if twoBytes and OptionTrimToPause and (b1 and $f0 = $a0) and not x then begin
                       b1 := $c0;
                       b2 := $00;
                       if x then
                         WriteLn('# Trim at ', stitch + Ord(x), ' x rewritten to pause')
                       else
                         WriteLn('# Trim at ', stitch + Ord(x), ' y rewritten to pause')
                     end;

(* Alternatively try a colour change, although I don't know how safe this is    *)
(* when there's not an adequate series of prededined colours.                   *)

(* ***** This turns out to crash an Innovis-97E when loaded.                    *)

                     if twoBytes and OptionTrimToChange and (b1 and $f0 = $a0) then begin
                       if x then begin
                         b1 := $fe;
                         b2 := $b0;
                         WriteLn('# Trim at ', stitch + Ord(x), ' x rewritten to colour change')
                       end else begin
                         b1 := $80;
                         if t1 then
                           b2 := $01
                         else
                           b2 := $02;
                         WriteLn('# Trim at ', stitch + Ord(x), ' y rewritten to dummy parameter')
                       end
                     end;

(* Convert a colour change to a dummy jump.                                     *)

(* ***** This turns out to crash an Innovis-97E when loaded.                    *)

                     if twoBytes and OptionChangeToDummy and (b1 = $fe) and (b2 = $b0) then
                       if x then begin
                         b1 := $90;
                         b2 := $00;
                         forceZero := true;
                         WriteLn('# Colour change at ', stitch + Ord(x), ' x rewritten to dummy jump')
                       end;
                     if not twoBytes and forceZero then begin
                       if not x then
                         b1 := $00;
                       forceZero := false;
                       WriteLn('# Colour change at ', stitch + Ord(x), ' y rewritten to zero')
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
    otherwise
      raise Exception.Create('In ' + thisName + ', patch verb not supported')
    end
end { ReadQ } ;


end.

