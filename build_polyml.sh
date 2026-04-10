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
fun useProject root' file =
  let val root = OS.FileSys.getDir ()
  in
    OS.FileSys.chDir root';
    use file;
    OS.FileSys.chDir root
  end;
(* Uncomment this and put library files in here to prevent reloading them each time. *)
(*
PolyML.SaveState.loadState "save" handle _ => (
PolyML.SaveState.saveState "save" );
*)
EOL

mlton -stop f mltonid.mlb \
    | grep -v ".mlb" \
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
