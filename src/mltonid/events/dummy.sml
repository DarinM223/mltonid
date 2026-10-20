structure DummyEventPoll :> EVENT_POLL =
struct
  type marked = unit
  fun empty () = ()
  fun addFilepath _ () = ()
  fun init () = ()
  fun apply _ = ()
  fun poll (SOME time) = OS.Process.sleep time
    | poll NONE = OS.Process.sleep Time.zeroTime
end
