structure INotify :> INOTIFY =
struct
  type fd = int
  type wd = int

  val IN_ACCESS: Word32.word = 0wx00000001
  val IN_MODIFY: Word32.word = 0wx00000002
  val IN_ATTRIB: Word32.word = 0wx00000004
  val IN_CLOSE_WRITE: Word32.word = 0wx00000008
  val IN_CREATE: Word32.word = 0wx00000100
  val IN_DELETE: Word32.word = 0wx00000200

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

  fun init () =
    raise Fail "INotify not implemented for SML/NJ"
  fun addWatch _ =
    raise Fail "INotify not implemented for SML/NJ"
  fun rmWatch _ =
    raise Fail "INotify not implemented for SML/NJ"
  fun close _ =
    raise Fail "INotify not implemented for SML/NJ"
  fun readEvents _ =
    raise Fail "INotify not implemented for SML/NJ"
  fun fdToPollDesc _ =
    raise Fail "INotify not implemented for SML/NJ"
end
