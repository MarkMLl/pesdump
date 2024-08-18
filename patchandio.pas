(* FPC 2.6.0 FPC 2.6.0 FPC 2.6.0 FPC 2.6.0 FPC 2.6.0 FPC 2.6.0 FPC 2.6.0 FPC 2. *)

unit PatchAndIO;

(* Support routines for PesDump, covered by the same license etc.  MarkMLl      *)

{$mode objfpc}{$H+}

interface

uses
  Classes, SysUtils;

type
  (* This is used as the parameter for the procedure that writes patched or
    unpatched data back to a file, and also where needed to do things like e.g.
    fix the endianness of a floating-point number.
  *)
  TScalar= record
           case longword of
             0: (u8: byte);
             1: (s8: shortint);
             2: (u16: word);
             3: (s16: smallint);
             4: (u32: longword);
             5: (s32: longint);
             6: (f32: single)
           end;

  (* This is an array of scalars, read from the input file as e.g. a sequence
    of 8-bit unsigned bytes and unpacked for convenience during patching or
    subsequent processing.
  *)
  TScalarArray= array of TScalar;

  TPatchOp= (PatchNone, PatchAt, PatchDelete, PatchInsert, PatchOverwrite,
                                        PatchIncrement, PatchDecrement);
  TPatch= record
            op: TPatchOp;
            numbers: array of longint
          end;

(* Call this before any data is input and optionally output, to make sure that
  NextPatch etc. is brought up to date.
*)
procedure StartPatch(readPos: longint);

(* Advance to the next patch, which typically starts with specification of a
  patch offset. This is exported for the use of a couple of simple patch
  routines relating to strings and stitches which haven't yet been moved into
  this unit.
*)
procedure PatchNext;

(* Write a scalar (i.e. a single byte etc.) to disc. Raise an exception on
  error.
*)
procedure WriteScalar(var pesOut: File; const callerName: string; buffer: TScalar;
                                sz: integer; const errorMsg: string= 'write error');

(* Read a scalar (i.e. single byte etc.) from disc, do not alter endianness
  etc., zero the remainder of the parameter. Raise an exception on error.
*)
procedure ReadScalar (var pesIn: File; const callerName: string; var buffer: TScalar;
                                                                sz: integer);

(* Return the kind of patch to be applied at the current address, including all
  cases where there is nothing to be done (which for the purpose of this
  function includes specification of a patch offset).
*)
function PatchVerb(readPos: longint): TpatchOp;

(* For the use of a couple of simple patch routines relating to strings etc.
  which haven't yet been moved into this unit.
*)
function NextPatchNumberCount(): integer;

(* Patch and write a scalar, with ptovision for both a pre- and post-insert.
*)
procedure PatchAndWriteScalar(var pesOut: File; const callerName: string; buffer:
                        TScalar; sz: integer; const sfx: string; patchLoc: integer);

(* Read a sequence of scalars (i.e. single bytes etc.) from disc, do not alter
  endianness etc., zero the remainder of the parameter. Raise an exception on
  error.
*)
procedure ReadVector(var pesIn: File; const callerName: string;
                                        var buffer: TScalarArray; sz: integer);

(* Write an array of scalars to disc, assume that the parameter is unpacked.
  Raise an exception on error.
*)
procedure WriteVector(var pesOut: File; const callerName: string;
                                        const buffer: TScalarArray; sz: integer;
                                        const errorMsg: string= 'write error');

(* This is a partial patch implementation intended to be sufficient to
  manipulate the padding in the PEC header (which might need to be adjusted in
  length) and NOTHING MORE.
*)
procedure PatchAndWriteVector(var pesOut: File; const callerName: string;
                                        const buffer: TScalarArray; sz: integer;
                                        const sfx: string; patchLoc: integer);

(* Parse a patch from the command line. The operation is determined by the
  first or possibly first two characters, followed by a sequence of comma-
  separated numbers of size appropriate to the data being patched (determined
  in ReadU8() etc.).

  @<num>  Continue to this point in the input file, assumed to be in order.
  {<num>  Delete the indicated number of bytes.
  }<bytes etc.> Insert the indicated bytes or stitch locations etc.
  =<bytes etc.> Overwrite the indicated bytes or stitch locations etc.
  +       Increment a byte or stitch location etc.
  -       Decrement a byte or stitch location etc.

  Assume that an exception is raised on error.
*)
function ParsePatch(s: string): tPatch;

(* Add a patch specified on the command line to the internal array.
*)
procedure AddPatch(patch: TPatch);

(* Dump patches for debugging purposes.
*)
procedure DumpPatches;


implementation

var
  patches: array of tPatch;
  nextpatch: integer= $7fffffff;
  nextpatchOffset: int64= -1;


(* Call this before any data is input and optionally output, to make sure that
  nextpatch etc. is brought up to date.
*)
procedure StartPatch(readPos: longint);

begin
  if (nextpatch = $7fffffff) and (Length(patches) > 0) then
    nextpatch := 0;
  if nextpatch <= Length(patches) - 1 then
    if (patches[nextpatch].op = patchAt) and (Length(patches[nextpatch].numbers) > 0) then begin
      nextpatchoffset := patches[nextpatch].numbers[0];
      nextpatch += 1
    end;
{$ifdef ERROR2 }
  if (readPos = nextpatchoffset) and (nextpatch <= Length(patches) - 1) then begin
    Write('%%%%% ', HexStr(readPos, 5));
    if Length(patches[nextpatch].numbers) >= 1 then
      case patches[nextpatch].op of
        patchDelete:    Write(': Delete(', patches[nextpatch].numbers[0], ')');
        patchInsert:    Write(': Insert(', Length(patches[nextpatch].numbers), ')');
        patchOverwrite: Write(': Overwrite(', Length(patches[nextpatch].numbers), ')')
      end
    else
      case patches[nextpatch].op of
        patchIncrement: Write(': Increment');
        patchDecrement: Write(': Decrement')
      end;
    WriteLn(' %%%%%')
  end
{$endif ERROR2 }
end { StartPatch } ;


(* Advance to the next patch, which typically starts with specification of a
  patch offset. This is exported for the use of a couple of simple patch
  routines relating to strings and stitches which haven't yet been moved into
  this unit.
*)
procedure PatchNext;

begin
  nextpatch += 1;
  if nextpatch <= Length(patches) - 1 then
    if (patches[nextpatch].op = patchAt) and (Length(patches[nextpatch].numbers) > 0) then begin
      nextpatchoffset := patches[nextpatch].numbers[0];
      nextpatch += 1
    end
end { PatchNext } ;


(* Write a scalar (i.e. a single byte etc.) to disc. Raise an exception on
  error.
*)
procedure WriteScalar(var pesOut: File; const callerName: string; buffer: TScalar;
                                sz: integer; const errorMsg: string= 'write error');

var
  r: integer;

begin
  BlockWrite(pesOut, buffer, sz, r);
  if r <> sz then
    raise Exception.Create('In ' + callerName + ', ' + errorMsg)
end { WriteScalar } ;


(* Read a scalar (i.e. single byte etc.) from disc, do not alter endianness
  etc., zero the remainder of the parameter. Raise an exception on error.
*)
procedure ReadScalar (var pesIn: File; const callerName: string; var buffer: TScalar;
                                                                sz: integer);

var
  r: integer;

begin
  buffer.u32 := 0;
  BlockRead(pesIn, buffer, sz, r);
  if r <> sz then
    raise Exception.Create('In ' + callerName + ', unexpected EOF')
end { ReadScalar } ;


(* Return the kind of patch to be applied at the current address, including all
  cases where there is nothing to be done (which for the purpose of this
  function includes specification of a patch offset).
*)
function PatchVerb(readPos: longint): TpatchOp;

begin
  if nextpatch > Length(patches) - 1 then
    exit(patchNone);
  if readPos <> nextpatchoffset then
    exit(patchNone);
  result := patches[nextpatch].op;
  if result = PatchAt then
    result := PatchNone
end { PatchVerb } ;


(* For the use of a couple of simple patch routines relating to strings etc.
  which haven't yet been moved into this unit.
*)
function nextpatchNumberCount(): integer;

begin
  result := Length(patches[nextpatch].numbers)
end { nextpatchNumberCount } ;


(* Patch and write a scalar, with ptovision for both a pre- and post-insert.
*)
procedure PatchAndWriteScalar(var pesOut: File; const callerName: string; buffer:
                        TScalar; sz: integer; const sfx: string; patchLoc: integer);

var
  i: integer;

begin

(* An insert patch has to be handled first, so that an extra byte (etc.) could  *)
(* be inserted right at the start of the file.                                  *)

  case PatchVerb(patchLoc) of
    PatchInsert: begin
                   for i := 0 to Length(patches[nextpatch].numbers) - 1 do
// TODO : Consider any endianness implications
                     WriteScalar(pesOut, callerName, TScalar(patches[nextpatch].numbers[i]),
                                        sz, 'leading patch insert error');
{$ifdef ERROR2 }
                   Write('%%%%% Inserted ', Length(patches[nextpatch].numbers),
                                        'x ', sfx, ' ->');
                   for i := 0 to Length(patches[nextpatch].numbers) - 1 do
// TODO : Consider any endianness implications
                     Write(' ', HexStr(patches[nextpatch].numbers[i], sz * 2));
                   WriteLn(' %%%%%');
{$endif ERROR2 }
                   PatchNext
                 end
  otherwise
  end;

(* Next is handled any deletion or in-place modification, after which the data  *)
(* is written with size determined by the caller.                               *)

  case PatchVerb(patchLoc) of
    PatchOverwrite: if Length(patches[nextpatch].numbers) = 1 then begin
// TODO : Consider any endianness implications
                      buffer.s32 := patches[nextpatch].numbers[0];
{$ifdef ERROR2 }
// TODO : Consider any endianness implications
                      WriteLn('%%%%% Overwrote 1x ',
                                        sfx, ' -> ', HexStr(buffer.u32, sz * 2), ' %%%%%')
{$endif ERROR2 }
                    end;
    PatchIncrement: if Length(patches[nextpatch].numbers) = 1 then begin
// TODO : Consider any endianness implications
                      i := buffer.s32;
                      i += patches[nextpatch].numbers[0];
                      buffer.s32 := i;
{$ifdef ERROR2 }
// TODO : Consider any endianness implications
                      WriteLn('%%%%% Incremented 1x ',
                                        sfx, ' -> ', HexStr(buffer.u32, sz * 2), ' %%%%%')
{$endif ERROR2 }
                    end;
    PatchDecrement: if Length(patches[nextpatch].numbers) = 1 then begin
// TODO : Consider any endianness implications
                      i := buffer.s32;
                      i -= patches[nextpatch].numbers[0];
                      buffer.s32 := i;
{$ifdef ERROR2 }
// TODO : Consider any endianness implications
                      WriteLn('%%%%% Decremented 1x ',
                                        sfx, ' -> ', HexStr(buffer.u32, sz * 2), ' %%%%%')
{$endif ERROR2 }
                    end
  otherwise
  end;
  case PatchVerb(patchLoc) of
    PatchDelete: begin
                   if not (patches[nextpatch].numbers[0] in [0, 1]) then
                     raise Exception.Create('In ' + callerName +
                                        ', partial/multiple deletion not supported');
{$ifdef ERROR2 }
                   WriteLn('%%%%% Deleted 1x ', sfx, ' %%%%%')
{$endif ERROR2 }
                 end
  otherwise
    WriteScalar(pesOut, callerName, buffer, sz)
  end;
  PatchNext;

(* There's no longer scope for deletion/modification patches, but if one or     *)
(* more inserts follow process them.                                            *)

  while PatchVerb(patchLoc) = PatchInsert do begin
{$ifdef ERROR2 }
    WriteLn('%%%%% ', HexStr(patchLoc, 5), ': Insert(', Length(patches[nextpatch].numbers), ') %%%%%');
{$endif ERROR2 }
    for i := 0 to Length(patches[nextpatch].numbers) - 1 do begin
// TODO : Consider any endianness implications
      WriteScalar(pesOut, callerName, TScalar(patches[nextpatch].numbers[i]), sz, 'trailing patch insert error')
    end;
{$ifdef ERROR2 }
    Write('%%%%% Inserted ', Length(patches[nextpatch].numbers), 'x U8 ->');
    for i := 0 to Length(patches[nextpatch].numbers) - 1 do
// TODO : Consider any endianness implications
      Write(' ', HexStr(patches[nextpatch].numbers[i], sz * 2));
    WriteLn(' %%%%%');
{$endif ERROR2 }
    PatchNext
  end
end { PatchAndWriteScalar } ;


(* Read a sequence of scalars (i.e. single bytes etc.) from disc, do not alter
  endianness etc., zero the remainder of the parameter. Raise an exception on
  error.
*)
procedure ReadVector(var pesIn: File; const callerName: string;
                                        var buffer: TScalarArray; sz: integer);

var
  i, r: integer;

begin
  for i := Low(buffer) to High(buffer) do begin
    buffer[i].u32 := 0;
    BlockRead(pesIn, buffer[i].u32, sz, r);
    if r <> sz then
      raise Exception.Create('In ' + callerName + ', unexpected EOF')
  end
end { ReadVector } ;


(* Write an array of scalars to disc, assume that the parameter is unpacked.
  Raise an exception on error.
*)
procedure WriteVector(var pesOut: File; const callerName: string;
                                        const buffer: TScalarArray; sz: integer;
                                        const errorMsg: string= 'write error');

var
  i, r: integer;

begin
  for i := Low(buffer) to High(buffer) do begin
    BlockWrite(pesOut, buffer[i], sz, r);
    if r <> sz then
      raise Exception.Create('In ' + callerName + ', ' + errorMsg)
  end
end { WriteVector } ;


(* This is a partial patch implementation intended to be sufficient to
  manipulate the padding in the PEC header (which might need to be adjusted in
  length) and NOTHING MORE.
*)
procedure PatchAndWriteVector(var pesOut: File; const callerName: string;
                                        const buffer: TScalarArray; sz: integer;
                                        const sfx: string; patchLoc: integer);

label
  666;

var
  i, j: integer;
  scratch: array[0..0] of TScalar;

begin
  i := Low(buffer);
  while i <= High(buffer) do begin
    case PatchVerb(patchLoc + i) of
      PatchDelete: begin
                     j := patches[nextpatch].numbers[0];
                     if j = 0 then
                       j := Length(buffer);
                     if j <> Length(buffer) then
                       raise Exception.Create('In ' + callerName +
                                        ', partial/multiple deletion not supported');
                     i += j;
{$ifdef ERROR2 }
                     WriteLn('%%%%% Deleted ', j, 'x ', sfx, ' %%%%%');
{$endif ERROR2 }
                     PatchNext
                   end;
      PatchNone:   begin
666:                 scratch[0] := buffer[i];
                     WriteVector(pesOut, callerName, scratch, sz)
// TODO : is the i loop sufficient for post-block patch insertion?
                   end;
      PatchInsert: begin
                     for j := 0 to Length(patches[nextpatch].numbers) - 1 do begin
                       scratch[0].s32 := patches[nextpatch].numbers[j];
                       WriteVector(pesOut, callerName, scratch, sz, 'insertion error')
                     end;
{$ifdef ERROR2 }
                     Write('%%%%% Inserted ', Length(patches[nextpatch].numbers),
                                                        'x ', sfx, ' ->');
                     for j := 0 to Length(patches[nextpatch].numbers) - 1 do
                       Write(' ', HexStr(patches[nextpatch].numbers[i], sz * 2));
                     WriteLn(' %%%%%');
{$endif ERROR2 }
                     PatchNext;
                     goto 666
                   end
    otherwise
      raise Exception.Create('In ' + callerName + ', patch verb not supported')
    end;
    i += 1
  end
end { PatchAndWriteVector } ;


(* Parse a number from a string, referring to the help text (main unit) for the
  acceptable formats. Return true on success. This is ripped out of TBD but
  with various block-oriented stuff rempved and modified to return an int64.
*)
function ParseNumber(var s: string; out q: int64): boolean;

label   666;

type    charset= set of char;

var     negative: boolean= false;
        radix: integer= 10;
        acceptable: charset= [];
        scratch: qword;
        i: integer;

begin
  ParseNumber := false;
  q := 0;

(* If the test size is non-zero and there's a leading / or - parse it. This  *)
(* is primarily so that -1 etc. can be specified as the stride.              *)

  while (s <> '') and (s[1] = '-') do begin
    negative := not negative;
    Delete(s, 1, 1);
    q += 1                              (* Characters moved from beginning   *)
  end;
  if s = '' then
    exit;                               (* Returning false                   *)

(* Special cases: leading 0x, $ and 0 change the default radix.              *)

  if Pos('0x', s) = 1 then begin
    radix := 16;
    Delete(s, 1, 2);
    q += 2                              (* Characters removed from beginning *)
  end;
  if Pos('$', s) = 1 then begin
    radix := 16;
    Delete(s, 1, 1);
    q += 1                              (* Characters removed from beginning *)
  end;
  if (Length(s) > 1) and (s[1] = '0') and (radix <> 16) then
    radix := 8;
  q := 0;

(* Parse a sequence of digits. There must be at least one digit in either    *)
(* the radix or value part, note that we /didn't/ remove octal's leading     *)
(* zero since doing so would make it impossible to enter 0 (i.e. a single    *)
(* character) as a parameter.                                                *)

666:
  acceptable := [];
  for i := 0 to radix - 1 do
    if i <= 9 then
      acceptable += [Chr(Ord('0') + i)]
    else
      acceptable += [Chr(Ord('a') + i - 10)];
  scratch := 0;
  while (s <> '') and (s[1] in acceptable) do begin
    scratch *= radix;
    if s[1] <= '9' then
      scratch += Ord(s[1]) - Ord('0')
    else
      scratch += Ord(s[1]) - Ord('a') + 10;
    Delete(s, 1, 1);
    q += 1                              (* Count of digits parsed            *)
  end;
  if q = 0 then
    exit;                               (* Returning false                   *)
  q := 0;

(* If we encounter R then we've just read a new radix, iterate.              *)

  if (s <> '') and (UpCase(s[1]) = 'R') then begin
    radix := scratch;
    Delete(s, 1, 1);
    goto 666
  end;

(* Otherwise we've had an actual numeric parameter.                          *)

  q := scratch;
  if s <> '' then
    exit;                              (* Returning false                    *)

(* The numeric result is in q.                                               *)

  if negative then
    q := -q;
  ParseNumber := true                   (* q contains a valid number         *)
end { ParseNumber } ;


(* Parse a sequence of comma-separated signed numbers, appending them to the
  first parameter. On success leave nothing in the second parameter, on
  failure an indeterminate count of numbers will have been transferred into the
  first parameter.
*)
procedure parseNumbers(var r: tPatch; var s: string);

var
  delim: integer;
  scratch: string;
  q: int64;

begin
  repeat
    delim := Pos(',', s);
    if delim >= 1 then begin
      scratch := Copy(s, 1, delim - 1);
      Delete(s, 1, delim)
    end else begin
      scratch := s;
      s := ''
    end;
    if not parseNumber(scratch, q) then begin
      s += ' ';                         (* Make sure it's not blank             *)
      exit
    end;
    SetLength(r.numbers, Length(r.numbers) + 1);
    r.numbers[Length(r.numbers) - 1] := q
  until s = ''
end { parseNumbers } ;


(* Parse a patch from the command line. The operation is determined by the
  first or possibly first two characters, followed by a sequence of comma-
  separated numbers of size appropriate to the data being patched (determined
  in ReadU8() etc.).

  @<num>  Continue to this point in the input file, assumed to be in order.
  {<num>  Delete the indicated number of bytes.
  }<bytes etc.> Insert the indicated bytes or stitch locations etc.
  =<bytes etc.> Overwrite the indicated bytes or stitch locations etc.
  +       Increment a byte or stitch location etc.
  -       Decrement a byte or stitch location etc.

  Assume that an exception is raised on error.
*)
function ParsePatch(s: string): tPatch;

(* As of FPC 3.0 result.numbers might not be automatically initialised empty.   *)
(* I'm not happy putting in an explicit SetLength() since if the length has not *)
(* been initialised any internal pointers might contain garbage, but having a   *)
(* temporary variable like this appears OK.                                     *)

var
  patch: tPatch;

begin
  Assert(Length(patch.numbers) = 0, 'Internal error: uninitialised dynamic array');
  SetLength(patch.numbers, 0);
  case s[1] of
    '@': begin
           patch.op := patchAt;
           Delete(s, 1, 1);
           parseNumbers(patch, s);
           if (Length(patch.numbers) <> 1) or (s <> '') then
             raise Exception.Create('Can''t parse patch offset')
         end;
    '-': begin
           patch.op := patchDecrement;
           Delete(s, 1, 1);
           if s = '' then
             s := '1';
           parseNumbers(patch, s);
           if (Length(patch.numbers) <> 1) or (s <> '') then
             raise Exception.Create('Can''t parse patch decrement')
         end;
    '+': begin
           patch.op := patchIncrement;
           Delete(s, 1, 1);
           if s = '' then
             s := '1';
           parseNumbers(patch, s);
           if (Length(patch.numbers) <> 1) or (s <> '') then
             raise Exception.Create('Can''t parse patch increment')
         end;
    '=': begin
           patch.op := patchOverwrite;
           Delete(s, 1, 1);
           parseNumbers(patch, s);
           if (Length(patch.numbers) < 1) or (s <> '') then
             raise Exception.Create('Can''t parse patch overwrite')
         end;
    '{': begin
           patch.op := patchDelete;
           Delete(s, 1, 1);
           if s = '' then
             s := '0';                  (* "As much as there is"                *)
           parseNumbers(patch, s);
           if (Length(patch.numbers) <> 1) or (s <> '') or
                                        (patch.numbers[0] < 0) then
             raise Exception.Create('Can''t parse patch deletion')
         end;
    '}': begin
           patch.op := patchInsert;
           Delete(s, 1, 1);
           parseNumbers(patch, s);
           if (Length(patch.numbers) < 1) or (s <> '') then
             raise Exception.Create('Can''t parse patch insertion')
         end
  otherwise
    raise Exception.Create('Unknown patch operation')
  end;
  ParsePatch := patch
end { ParsePatch } ;


(* Add a patch specified on the command line to the internal array.
*)
procedure AddPatch(patch: TPatch);

begin
  SetLength(patches, Length(Patches) + 1);
  Patches[Length(patches) - 1] := patch
end { AddPatch } ;


(* Dump patches for debugging purposes.
*)
procedure DumpPatches;

var
  i, j: integer;
  k: int64;

begin
  for i := 0 to Length(patches) - 1 do
    with patches[i] do begin
      case op of
        PatchAt:        Write(' @');
        PatchDelete:    Write(' {');
        PatchInsert:    Write(' }');
        PatchOverwrite: Write(' =');
        PatchIncrement: Write(' +');
        PatchDecrement: Write(' -')
      end;
      for j := 0 to Length(numbers) - 1 do begin
        if j > 0 then
          Write(',');
        k := numbers[j];

(* Hex output is most useful since it is the radix used by the address and raw  *)
(* data. Patch commands may contain -ve numbers particularly where referring to *)
(* stitches, but continue to use hex for consistency.                           *)

        if op = patchAt then
          Write(HexStr(k, 5))
        else begin
          if k < 0 then
            Write('-');
          k := Abs(k);
          if k > $ffff then
            Write(HexStr(k, 8))
          else
            if k > $ff then
              Write(HexStr(k, 4))
            else
              Write(HexStr(k, 2))
        end
      end
    end
end { DumpPatches } ;


end.

