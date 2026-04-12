#!/bin/bash
cat > build.sml <<EOL
structure Int64 = Int63
structure Unsafe =
struct
  structure Basis =
  struct
    structure Array = Array
    structure Vector = Vector
    structure CharArray = CharArray
    structure CharVector = CharVector
    structure Word8Array = Word8Array
    structure Word8Vector = Word8Vector
  end

  structure Vector = struct val sub = Basis.Vector.sub end

  structure Array =
  struct
    val sub = Basis.Array.sub
    val update = Basis.Array.update
    val create = Basis.Array.array
  end

  structure CharArray =
  struct
    open Basis.CharArray
    fun create i =
      array (i, chr 0)
  end

  structure CharVector =
  struct
    open Basis.CharVector
    fun create i =
      Basis.CharArray.vector (Basis.CharArray.array (i, chr 0))
    fun update (vec, i, el) =
      raise Fail "Unimplemented: Unsafe.CharVector.update"
  end

  structure Word8Array =
  struct
    open Basis.Word8Array
    fun create i = array (i, 0w0)
  end

  structure Word8Vector =
  struct
    open Basis.Word8Vector
    fun create i =
      Basis.Word8Array.vector (Basis.Word8Array.array (i, 0w0))
    fun update (vec, i, el) =
      raise Fail "Unimplemented: Unsafe.Word8Vector.update"
  end

  structure Real64Array =
  struct
    open Basis.Array
    type elem = Real.real
    type array = elem array
    fun create i = array (i, 0.0)
  end
end;
structure Real64 = Real;
structure PackReal64Little = PackRealLittle;
structure PackWord64Little : PACK_WORD = struct
   val bytesPerElem = 8
   val isBigEndian = false
   fun subVec _ = raise Fail "PackWord64Little.subVec"
   fun subVecX _ = raise Fail "PackWord64Little.subVecX"
   fun subArr _ = raise Fail "PackWord64Little.subArr"
   fun subArrX _ = raise Fail "PackWord64Little.subArrX"
   fun update _ = raise Fail "PackWord64Little.update"
end;
fun useProject root' file =
  let val root = OS.FileSys.getDir ()
  in
    OS.FileSys.chDir root';
    use file;
    OS.FileSys.chDir root
  end;
structure MLtonProcess =
 struct
    type pid = Posix.Process.pid

    local
       fun mk (exec, args) =
          case Posix.Process.fork () of
             NONE => exec args
           | SOME pid => pid
    in
       fun spawne {path, args, env} =
          mk (Posix.Process.exece, (path, args, env))
       fun spawnp {file, args} =
          mk (Posix.Process.execp, (file, args))
    end

    fun spawn {path, args} =
       spawne {path = path, args = args,
               env = Posix.ProcEnv.environ ()}
 end;
 structure MLtonRandom =
   struct
      (* Uses /dev/random and /dev/urandom to get a random word.
       * If they can't be read from, return NONE.
       *)
      local
         fun make (file, name) =
            let
               val buf = Word8Array.array (4, 0w0)
            in
               fn () =>
               (let
                   val fd =
                      let
                         open Posix.FileSys
                      in
                         openf (file, O_RDONLY, O.flags [])
                      end
                   fun loop rem =
                      let
                         val n = Posix.IO.readArr (fd,
                                                   Word8ArraySlice.slice
                                                   (buf, 4 - rem, SOME rem))
                         val _ = if n = 0
                                    then (Posix.IO.close fd; raise Fail name)
                                 else ()
                         val rem = rem - n
                      in
                         if rem = 0
                            then ()
                         else loop rem
                      end
                   val _ = loop 4
                   val _ = Posix.IO.close fd
                in
                   SOME (Word.fromLarge (PackWord32Little.subArr (buf, 0)))
                end
                   handle OS.SysErr _ => NONE)
            end
      in
         val seed = make ("/dev/random", "Random.seed")
         val useed = make ("/dev/urandom", "Random.useed")
      end

      local
         open Word
         val seed: word ref = ref 0w13
      in
         (* From page 284 of Numerical Recipes in C. *)
         fun rand (): word =
            let
               val res = 0w1664525 * !seed + 0w1013904223
               val _ = seed := res
            in
               res
            end

         fun srand (w: word): unit = seed := w
      end

      local
         val chars =
            "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz"
         val numChars = String.size chars
         val refresh =
            let
               val numChars = IntInf.fromInt numChars
               fun loop (i: IntInf.int, c: int): int =
                  if IntInf.< (i, numChars)
                     then c
                  else loop (IntInf.div (i, numChars), c + 1)
            in
               loop (IntInf.pow (2, Word.wordSize), 0)
            end
         val r: word ref = ref 0w0
         val count: int ref = ref refresh
         val numChars = Word.fromInt numChars
      in
         fun alphaNumChar (): char =
            let
               val n = !count
               val _ = if n = refresh
                          then (r := rand ()
                                ; count := 1)
                       else (count := n + 1)
               val w = !r
               val c = String.sub (chars, Word.toInt (Word.mod (w, numChars)))
               val _ = r := Word.div (w, numChars)
            in
               c
            end
      end

      fun alphaNumString (length: int): string =
         CharVector.tabulate (length, fn _ => alphaNumChar ())
   end;
structure MLtonPlatform =
   struct
      local
         val toLower = CharVector.map Char.toLower
         fun peek (l, f) = List.find f l
         fun omap (opt, f) = Option.map f opt
      in
         fun fromString_toString all =
            let
               fun fromString s =
                  let
                     val s = toLower s
                  in
                     omap (peek (all, fn (_, s') => s = toLower s'), #1)
                  end
               fun toString a = #2 (valOf (peek (all, fn (a', _) => a = a')))
            in
               (fromString, toString)
            end
      end

      structure Arch =
         struct
            datatype t =
               Alpha
             | AMD64
             | ARM
             | ARM64
             | HPPA
             | IA64
             | LoongArch64
             | m68k
             | MIPS
             | PowerPC
             | PowerPC64
             | RISCV
             | S390
             | Sparc
             | Wasm32
             | X86

            val all =
               (Alpha, "Alpha")::
               (AMD64, "AMD64")::
               (ARM, "ARM")::
               (ARM64, "ARM64")::
               (HPPA, "HPPA")::
               (IA64, "IA64")::
               (LoongArch64,"LoongArch64")::
               (m68k, "m68k")::
               (MIPS, "MIPS")::
               (PowerPC, "PowerPC")::
               (PowerPC64, "PowerPC64")::
               (RISCV, "RISCV")::
               (S390, "S390")::
               (Sparc, "Sparc")::
               (Wasm32, "Wasm32")::
               (X86, "X86")::
               nil

            val (fromString, toString) = fromString_toString all

            val host: t = X86
         end

      structure Format =
         struct
            datatype t =
               Archive
             | Executable
             | LibArchive
             | Library

            val all =
               (Archive, "Archive")::
               (Executable, "Executable")::
               (LibArchive, "LibArchive")::
               (Library, "Library")::
               nil

            val (fromString, toString) = fromString_toString all

            val host: t = Library
         end

      structure OS =
         struct
            datatype t =
               AIX
             | Cygwin
             | Darwin
             | FreeBSD
             | Hurd
             | HPUX
             | Linux
             | MinGW
             | NetBSD
             | OpenBSD
             | Solaris
             | WASI

            val all =
               (AIX, "AIX")::
               (Cygwin, "Cygwin")::
               (Darwin, "Darwin")::
               (FreeBSD, "FreeBSD")::
               (HPUX, "HPUX")::
               (Hurd, "Hurd")::
               (Linux, "Linux")::
               (MinGW, "MinGW")::
               (NetBSD, "NetBSD")::
               (OpenBSD, "OpenBSD")::
               (Solaris, "Solaris")::
               (WASI, "WASI")::
               nil

            val (fromString, toString) = fromString_toString all

            val host: t = Linux
         end
   end
functor MkIO (S : sig
                  type outstream
                  val openOut: string -> outstream
               end) =
struct
   open S

   fun mkstemps {prefix, suffix} =
      let
         val name = concat [prefix, MLtonRandom.alphaNumString 6, suffix]
      in
         (* Make sure the temporary file name doesn't already exist. *)
         if OS.FileSys.access (name, [])
             then mkstemps {prefix = prefix, suffix = suffix}
             else (name, openOut name)
      end
   fun mkstemp s = mkstemps {prefix = s, suffix = ""}
   fun tempPrefix _ = raise Fail "MLton.IO.tempPrefix"
end;
structure MLton = struct
  val debug = false
  val isMLton = false
  structure Exn =
     struct
        val history : exn -> string list = fn _ => []
     end
  structure GC =
     struct
        fun collect () = PolyML.fullGC ()
        fun pack () = collect ()
     end
  structure Process = MLtonProcess
  structure Random = MLtonRandom
  structure Platform = MLtonPlatform
  structure TextIO = MkIO (TextIO)
  structure Array =
   struct
      open Array

      fun unfoldi (n, a, f) =
         let
            val r = ref a
            val a =
               tabulate (n, fn i =>
                         let
                            val (b, a') = f (i, !r)
                            val _ = r := a'
                         in
                            b
                         end)
         in
            (a, !r)
         end
   end
  structure Vector =
   struct
      open Vector

      fun create n =
         let
            val r = ref (Array.fromList [])
            val subLim = ref 0
            fun sub i =
               if 0 <= i andalso i < !subLim
                  then Array.sub (!r, i)
               else raise Subscript
            val updateLim = ref 0
            fun update (i, x) =
               if 0 <= i andalso i < !updateLim
                  then if i = !updateLim andalso i < n
                          then (r := (Array.tabulate (i + 1, fn j =>
                                                      if i = j
                                                         then x
                                                      else Array.sub (!r, j)));
                                subLim := i + 1;
                                updateLim := i + 1)
                       else raise Subscript
               else
                  Array.update (!r, i, x)
            val gotIt = ref false
            fun done () =
               if !gotIt then
                  raise Fail "already got vector"
               else
                  if n = !updateLim then
                     (gotIt := true;
                      updateLim := 0;
                      Array.vector (!r))
                  else
                     raise Fail "vector not full"
         in
            {done = done,
             sub = sub,
             update = update}
         end

      fun unfoldi (n, a, f) =
         let
            val r = ref a
            val v =
               tabulate (n, fn i =>
                         let
                            val (b, a') = f (i, !r)
                            val _ = r := a'
                         in
                            b
                         end)
         in
            (v, !r)
         end
   end
   structure Profile =
   struct
      structure Data =
         struct
            type t = unit

            val equals = fn _ => raise Fail "Profile.Data.equals"
            val free = fn _ => raise Fail "Profile.Data.free"
            val malloc = fn _ => raise Fail "Profile.Data.malloc"
            val write = fn _ => raise Fail "Profile.Data.write"
         end
      val isOn = false
      val withData = fn _ => raise Fail "Profile.withData"
   end
  val eq = fn _ => raise Fail "MLton.eq"
  val equal = fn _ => raise Fail "MLton.equal"
  val hash = fn _ => raise Fail "MLton.hash"
  val safe = true
  val share = fn _ => raise Fail "MLton.share"
  val shareAll = fn _ => raise Fail "MLton.shareAll"
  val size: 'a -> IntInf.int = fn _ => ~1
  val sizeAll: 'a -> IntInf.int = fn _ => ~1
end;
(* Uncomment this and put library files in here to prevent reloading them each time. *)
(*
PolyML.SaveState.loadState "save" handle _ => (
PolyML.SaveState.saveState "save" );
*)
EOL

mlton -stop f mltonid.mlb \
    | grep -v "\.mlb" \
    | grep -v "/lib/mlton/sml/basis/" \
    | grep -v "/lib/mlton/targets/" \
    | while read line ; do \
     if [[ $line == *.mlton.sml ]] ; then \
       if [ -f "${line/%.mlton.sml/.polyml.sml}" ]; then \
         echo "use \"${line/%.mlton.sml/.polyml.sml}\";" ; \
       elif [ -f "${line/%.mlton.sml/.default.sml}" ]; then \
         echo "use \"${line/%.mlton.sml/.default.sml}\";" ; \
       elif [ -f "${line/%.mlton.sml/.common.sml}" ]; then \
         echo "use \"${line/%.mlton.sml/.common.sml}\";" ; \
       elif [ -f "${line/%.mlton.sml/.sml}" ]; then \
         echo "use \"${line/%.mlton.sml/.sml}\";" ; \
       fi \
     elif [[ $line == *.mlton.fun ]] ; then \
       if [ -f "${line/%.mlton.fun/.polyml.fun}" ]; then \
         echo "use \"${line/%.mlton.fun/.polyml.fun}\";" ; \
       elif [ -f "${line/%.mlton.fun/.default.fun}" ]; then \
         echo "use \"${line/%.mlton.fun/.default.fun}\";" ; \
       elif [ -f "${line/%.mlton.fun/.common.fun}" ]; then \
         echo "use \"${line/%.mlton.fun/.common.fun}\";" ; \
       elif [ -f "${line/%.mlton.fun/.fun}" ]; then \
         echo "use \"${line/%.mlton.fun/.fun}\";" ; \
       fi \
     elif [[ $line == *.mlton.sig ]] ; then \
       if [ -f "${line/%.mlton.sig/.polyml.sig}" ]; then \
         echo "use \"${line/%.mlton.sig/.polyml.sig}\";" ; \
       elif [ -f "${line/%.mlton.sig/.default.sig}" ]; then \
         echo "use \"${line/%.mlton.sig/.default.sig}\";" ; \
       elif [ -f "${line/%.mlton.sig/.common.sig}" ]; then \
         echo "use \"${line/%.mlton.sig/.common.sig}\";" ; \
       elif [ -f "${line/%.mlton.sig/.sig}" ]; then \
         echo "use \"${line/%.mlton.sig/.sig}\";" ; \
       fi \
     else\
       echo "use \"$line\";" ; \
     fi \
    done \
    >> build.sml
