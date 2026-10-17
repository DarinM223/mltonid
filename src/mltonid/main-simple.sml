structure Main = MainFn(DummyEventPoll)

fun main () =
  ignore (Main.main ("", []))
val () = if MLton.isMLton then main () else ()
