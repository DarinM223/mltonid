signature EVENT_POLL =
sig
  type marked
  val empty: unit -> marked
  val addFilepath: string -> marked -> marked
  val init: unit -> unit
  val apply: marked -> unit
  val poll: Time.time option -> unit
end
