structure INotify :> INOTIFY =
struct
  type fd = int
  type wd = int

  (* Common inotify mask constants *)
  val IN_ACCESS = 0wx00000001
  val IN_MODIFY = 0wx00000002
  val IN_ATTRIB = 0wx00000004
  val IN_CLOSE_WRITE = 0wx00000008
  val IN_CREATE = 0wx00000100
  val IN_DELETE = 0wx00000200

  (* Linux kernel constant to enforce O_NONBLOCK behavior on the descriptor *)
  val IN_NONBLOCK = 0x00000800

  datatype error_reason =
    ErrorInit
  | ErrorAddWatch of string
  | ErrorRemoveWatch of fd * wd
  | ErrorClose of fd
  | ErrorConvertPollDesc of fd
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

  val libc = Foreign.loadLibrary "libc.so.6"

  (* 1. Swap for inotify_init1 which accepts flags *)
  val inotify_init1_ptr = Foreign.getSymbol libc "inotify_init1"
  val inotify_add_watch_ptr = Foreign.getSymbol libc "inotify_add_watch"
  val inotify_rm_watch_ptr = Foreign.getSymbol libc "inotify_rm_watch"
  val read_ptr = Foreign.getSymbol libc "read"
  val close_ptr = Foreign.getSymbol libc "close"

  (* 2. Map wrapper with an explicit cInt configuration *)
  val inotify_init1_sym =
    Foreign.buildCall1 (inotify_init1_ptr, Foreign.cInt, Foreign.cInt)

  val inotify_add_watch_sym =
    Foreign.buildCall3
      ( inotify_add_watch_ptr
      , (Foreign.cInt, Foreign.cString, Foreign.cUint32)
      , Foreign.cInt
      )

  val inotify_rm_watch_sym =
    Foreign.buildCall2
      (inotify_rm_watch_ptr, (Foreign.cInt, Foreign.cInt), Foreign.cInt)

  val read_sym =
    Foreign.buildCall3
      (read_ptr, (Foreign.cInt, Foreign.cPointer, Foreign.cInt), Foreign.cInt)

  val close_sym = Foreign.buildCall1 (close_ptr, Foreign.cInt, Foreign.cInt)

  fun toCString s = s ^ "\000"

  (* Call init with the non-blocking flag enabled *)
  fun init () =
    let val fd = inotify_init1_sym IN_NONBLOCK
    in if fd < 0 then raise Error ErrorInit else fd
    end

  fun addWatch (fd, path, mask) =
    let
      val maskInt = Word32.toInt mask
      val wd = inotify_add_watch_sym (fd, toCString path, maskInt)
    in
      if wd < 0 then raise Error (ErrorAddWatch path) else wd
    end

  fun rmWatch (fd, wd) =
    if inotify_rm_watch_sym (fd, wd) < 0 then
      raise Error (ErrorRemoveWatch (fd, wd))
    else
      ()

  fun close fd =
    if close_sym fd < 0 then raise Error (ErrorClose fd) else ()

  (* Updated non-blocking event read *)
  fun readEvents (fd, buf) =
    let
      val len = Word8Array.length buf
      val cBuf = Foreign.Memory.malloc (Word.fromInt len)
      val bytesRead = read_sym (fd, cBuf, len)
    in
      if bytesRead < 0 then
        (* If bytesRead is -1, it means no data was ready (EAGAIN) or another error occurred *)
        (Foreign.Memory.free cBuf; bytesRead)
      else
        let
          fun copy i =
            if i >= bytesRead then
              ()
            else
              let val byte = Foreign.Memory.get8 (cBuf, Word.fromInt i)
              in Word8Array.update (buf, i, byte); copy (i + 1)
              end
        in
          copy 0;
          Foreign.Memory.free cBuf;
          bytesRead
        end
    end

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
