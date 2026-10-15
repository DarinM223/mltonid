(**
 * Parses the filenames from an array buffer.
 *
 * Example:
 * val fd = INotify.init ()
 * val mask = Word32.orb (INotify.IN_CREATE, INotify.IN_MODIFY)
 * val wd = INotify.addWatch(fd, ".", mask)
 * val arr = Word8Array.array (1024, 0w0)
 * val size = INotify.readEvents (fd, arr)
 * val result = INotifyParser.parseFilenames (arr, size)
 *)
structure INotifyParser =
struct
  (* Helper to decode a 4-byte little-endian integer from Word8Array *)
  fun readInt32 (buf, offset) =
    let
      val b0 = Word8.toLarge (Word8Array.sub (buf, offset))
      val b1 = Word8.toLarge (Word8Array.sub (buf, offset + 1))
      val b2 = Word8.toLarge (Word8Array.sub (buf, offset + 2))
      val b3 = Word8.toLarge (Word8Array.sub (buf, offset + 3))
      open LargeWord
      infix << orb
    in
      toInt (b0 orb (b1 << 0w8) orb (b2 << 0w16) orb (b3 << 0w24))
    end

  (* Extracts the null-terminated string from the name sub-array *)
  fun extractString (buf, startOffset, len) =
    let
      fun collect (i, acc) =
        if i >= len then
          List.rev acc
        else
          let
            val byte = Word8Array.sub (buf, startOffset + i)
          in
            (* Stop collecting characters if we hit the C null terminator \0 *)
            if byte = 0w0 then List.rev acc
            else collect (i + 1, Byte.byteToChar byte :: acc)
          end
    in
      String.implode (collect (0, []))
    end

  (* Iterates over the raw byte buffer to extract all filename strings *)
  fun parseFilenames (buf, bytesRead) =
    let
      fun parse (offset, acc) =
        if offset >= bytesRead then
          List.rev acc
        else
          let
            val wd = readInt32 (buf, offset)
            val mask = readInt32 (buf, offset + 4)
            val len = readInt32 (buf, offset + 12)

            (* Extract name if length > 0, otherwise it's an empty event on the dir itself *)
            val filenameOpt =
              if len > 0 then SOME (extractString (buf, offset + 16, len))
              else NONE

            (* The layout struct pads name length to align to 16-byte boundaries *)
            val nextOffset = offset + 16 + len
          in
            case filenameOpt of
              SOME name => parse (nextOffset, name :: acc)
            | NONE => parse (nextOffset, acc)
          end
    in
      parse (0, [])
    end
end
