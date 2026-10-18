fun matchSMLFile path =
  case OS.Path.ext path of
    SOME "sml" => true
  | SOME "sig" => true
  | SOME "fun" => true
  | SOME "mlb" => true
  | SOME "cm" => true
  | _ => false

structure Main =
  MainFn
    (structure Poll =
       INotifyCache
         (structure INotify = INotify
          val log = print
          val matchFile = matchSMLFile)
     val pollTime = SOME (Time.seconds 1))

fun main () =
  ignore (Main.main ("", []))
val () = if MLton.isMLton then main () else ()
