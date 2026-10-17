functor INotifyCache (structure INotify: INOTIFY val log: string -> unit) :>
  EVENT_POLL =
struct
  type marked = INotify.wd AtomMap.map

  val state = ref NONE

  val mask = Word32.orb (INotify.IN_CREATE, INotify.IN_MODIFY)

  val watched: INotify.wd AtomMap.map ref = ref AtomMap.empty

  fun init () =
    let
      val fd = INotify.init ()
      val pollDesc = INotify.fdToPollDesc fd
      val rootWd = INotify.addWatch (fd, ".", mask)
    in
      state := SOME {fd = fd, pollDesc = pollDesc, rootWd = rootWd}
    end

  val getState = fn () => Option.valOf (!state)

  fun empty () = AtomMap.empty

  fun trim str =
    let
      val ss = Substring.full str
      val leftTrimmed = Substring.dropl Char.isSpace ss
      val fullyTrimmed = Substring.dropr Char.isSpace leftTrimmed
    in
      Substring.string fullyTrimmed
    end
  fun addFilepath path marked =
    let
      val {rootWd, ...} = getState ()
      val path = trim path
    in
      if path = "" then marked
      else AtomMap.insert (marked, Atom.atom (OS.Path.dir path), rootWd)
    end
  fun apply marked =
    let
      val {fd, ...} = getState ()
      fun merge (_, SOME wd, SOME _) = SOME wd
        | merge (dir, SOME wd, NONE) =
            ( log ("Removing watch at path: " ^ Atom.toString dir ^ "\n")
            ; INotify.rmWatch (fd, wd)
            ; NONE
            )
        | merge (dir, NONE, SOME _) =
            let
              val dir = Atom.toString dir
            in
              if dir = "" then
                NONE
              else
                ( log ("Adding watch at path: " ^ dir ^ "\n")
                ; SOME (INotify.addWatch (fd, dir, mask))
                )
            end
        | merge (_, NONE, NONE) = NONE
    in
      watched := AtomMap.mergeWithi merge (!watched, marked)
    end

  fun pollWithExt (pollDesc, matchExt, originalTimeout) =
    let
      val {fd, ...} = getState ()
      val buf = Word8Array.array (1024, 0w0)
      fun loop NONE =
            (case OS.IO.poll ([pollDesc], NONE) of
               [] => loop NONE (* Spurious wake up, poll again *)
             | _ =>
                 let
                   val size = INotify.readEvents (fd, buf)
                   val paths = INotifyParser.parseFilenames (buf, size)
                 in
                   if List.exists matchExt paths then () else loop NONE
                 end)
        | loop (SOME remTime) =
            if Time.<= (remTime, Time.zeroTime) then
              () (* Timeout expired entirely *)
            else
              let
                val start = Time.now ()
                val activeEvents = OS.IO.poll ([pollDesc], SOME remTime)
                val stop = Time.now ()
                val elapsed = Time.- (stop, start)
                val newTimeout = Time.- (remTime, elapsed)
              in
                case activeEvents of
                  [] => () (* Natural timeout: no events fired *)
                | _ =>
                    let
                      val size = INotify.readEvents (fd, buf)
                      val paths = INotifyParser.parseFilenames (buf, size)
                    in
                      if List.exists matchExt paths then
                        () (* Target file extension matched *)
                      else
                        loop (SOME newTimeout) (* Retry with remaining time *)
                    end
              end
    in
      loop originalTimeout
    end

  fun matchSMLFile path =
    case OS.Path.ext path of
      SOME "sml" => true
    | SOME "sig" => true
    | SOME "fun" => true
    | SOME "mlb" => true
    | SOME "cm" => true
    | _ => false

  fun poll timeout =
    let val {pollDesc, ...} = getState ()
    in pollWithExt (pollDesc, matchSMLFile, timeout)
    end
end
