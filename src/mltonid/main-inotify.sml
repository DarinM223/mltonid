structure Main =
  MainFn(INotifyCache (structure INotify = INotify val log = print))

fun main () =
  ignore (Main.main ("", []))
val () = if MLton.isMLton then main () else ()