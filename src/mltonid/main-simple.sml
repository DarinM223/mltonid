structure Main =
  MainFn (structure Poll = DummyEventPoll val pollTime = SOME (Time.seconds 1))

fun main () =
  ignore (Main.main ("", []))
val () = if MLton.isMLton then main () else ()
