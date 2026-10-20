(**
 * Signature for working with the inotify API through FFI.
 *
 * Example:
 * val fd = INotify.init ()
 * val mask = Word32.orb (INotify.IN_CREATE, INotify.IN_MODIFY)
 * val wd = INotify.addWatch(fd, ".", mask)
 * val pollDesc = INotify.fdToPollDesc fd
 * val result = OS.IO.poll ([pollDesc], NONE)
 * val arr = Word8Array.array (1024, 0w0)
 * val size = INotify.readEvents (fd, arr)
 * val () = INotify.rmWatch (fd, wd)
 *)
signature INOTIFY =
sig
  type fd
  type wd

  datatype error_reason =
    ErrorInit
  | ErrorAddWatch of string
  | ErrorRemoveWatch of fd * wd
  | ErrorClose of fd
  | ErrorConvertPollDesc of fd
  exception Error of error_reason
  val showError_reason: error_reason -> string

  val IN_ACCESS: Word32.word
  val IN_ATTRIB: Word32.word
  val IN_CLOSE_WRITE: Word32.word
  val IN_CREATE: Word32.word
  val IN_DELETE: Word32.word
  val IN_MODIFY: Word32.word

  val init: unit -> fd
  val addWatch: fd * string * Word32.word -> wd
  val readEvents: fd * Word8Array.array -> int
  val rmWatch: fd * wd -> unit
  val close: fd -> unit
  val fdToPollDesc: fd -> OS.IO.poll_desc
end
