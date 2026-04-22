(* Copyright (C) 2022 Matthew Fluet.
 *
 * MLton is released under a HPND-style license.
 * See the file MLton-LICENSE for details.
 *)

structure PreMLton =
struct

   open MLton

   val debug = false

   structure Platform =
      struct
         structure Arch =
            struct
               val host = "amd64"
            end
         structure Format =
            struct
               val host = "executable"
            end
         structure OS =
            struct
               val host = "linux"
            end
      end

end
