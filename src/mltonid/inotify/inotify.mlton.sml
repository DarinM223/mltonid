structure INotify :> INOTIFY =
struct
  type fd = int
  type wd = int

  val IN_ACCESS = 0wx00000001
  val IN_MODIFY = 0wx00000002
  val IN_ATTRIB = 0wx00000004
  val IN_CLOSE_WRITE = 0wx00000008
  val IN_CREATE = 0wx00000100
  val IN_DELETE = 0wx00000200

  val IN_NONBLOCK = 0x00000800

  datatype error_reason =
    ErrorInit
  | ErrorAddWatch of string
  | ErrorRemoveWatch of fd * wd
  | ErrorClose of fd
  | ErrorConvertPollDesc of fd
  val showError_reason =
    fn ErrorInit => "ErrorInit"
     | ErrorAddWatch t0 => "ErrorAddWatch " ^ "(" ^ "\"" ^ t0 ^ "\"" ^ ")"
     | ErrorRemoveWatch (t1, t2) =>
      "ErrorRemoveWatch " ^ "("
      ^ String.concatWith ", " [Int.toString t1, Int.toString t2] ^ ")"
     | ErrorClose t3 => "ErrorClose " ^ "(" ^ Int.toString t3 ^ ")"
     | ErrorConvertPollDesc t4 =>
      "ErrorConvertPollDesc " ^ "(" ^ Int.toString t4 ^ ")"
  exception Error of error_reason

  val c_inotify_init1 = _import "inotify_init1" : int -> int;
  val c_inotify_add_watch =
    _import "inotify_add_watch" : int * string * Word32.word -> int;
  val c_inotify_rm_watch = _import "inotify_rm_watch" : int * int -> int;
  val c_read = _import "read" : int * Word8Array.array * int -> int;
  val c_close = _import "close" : int -> int;

  fun toCString s = s ^ "\000"

  fun init () =
    let val fd = c_inotify_init1 IN_NONBLOCK
    in if fd < 0 then raise Error ErrorInit else fd
    end

  fun addWatch (fd, path, mask) =
    let val wd = c_inotify_add_watch (fd, toCString path, mask)
    in if wd < 0 then raise Error (ErrorAddWatch path) else wd
    end

  fun rmWatch (fd, wd) =
    if c_inotify_rm_watch (fd, wd) < 0 then
      raise Error (ErrorRemoveWatch (fd, wd))
    else
      ()

  fun close fd =
    if c_close fd < 0 then raise Error (ErrorClose fd) else ()

  (* Non-blocking buffer read. Returns -1 instead of hanging if empty *)
  fun readEvents (fd, buf) =
    c_read (fd, buf, Word8Array.length buf)

  fun fdToPollDesc fd =
    let
      val posixFD = Posix.FileSys.wordToFD (SysWord.fromInt fd)
      val iod = Posix.FileSys.fdToIOD posixFD
      val pollDesc =
        case OS.IO.pollDesc iod of
          SOME pd => pd
        | NONE => raise Error (ErrorConvertPollDesc fd)
    in
      OS.IO.pollIn pollDesc
    end
end
