  val {hom = loopTy, ...} =
    CoreML.Type.makeHom {con = TypeEnv.Type.con, var = TypeEnv.Type.var}
fun patToNestedPat (pat: CoreML.Pat.t) : MatchCompile.NestedPat.t =
  let
    val ty = CoreML.Pat.ty pat
    val ty' = loopTy ty
    val pat =
      case CoreML.Pat.node pat of
        CoreML.Pat.Con {arg, con, targs} =>
          MatchCompile.NestedPat.Con
            {arg = Option.map (arg, patToNestedPat), con = con, targs = Vector.map (targs, loopTy)}
      | CoreML.Pat.Const const =>
          let
            val const = const ()
          in
            MatchCompile.NestedPat.Const
              { const = const
              , isChar = CoreML.Type.isCharX ty
              , isInt = CoreML.Type.isInt ty
              }
          end
      | CoreML.Pat.Layered (v, t) =>
          MatchCompile.NestedPat.Layered (v, patToNestedPat t)
      | CoreML.Pat.List ts =>
          let
            open MatchCompile
            val targs = Vector.map(#2 (valOf (CoreML.Type.deConOpt ty)), loopTy)
          in
            Vector.fold
              ( ts
              , NestedPat.Con {arg = NONE, con = CoreML.Con.nill, targs = targs}
              , fn (p, np) =>
                  NestedPat.Con
                    { arg = SOME (NestedPat.tuple (Vector.new2
                        (patToNestedPat p, NestedPat.make (np, ty'))))
                    , con = CoreML.Con.cons
                    , targs = targs
                    }
              )
          end
      | CoreML.Pat.Or ts =>
          MatchCompile.NestedPat.Or (Vector.map (ts, patToNestedPat))
      | CoreML.Pat.Record r =>
          let
            open MatchCompile
          in
            NestedPat.Record
              (SortedRecord.fromVector
                 (Vector.map
                    ( CoreML.Type.deRecord ty
                    , fn (f: Field.t, t: CoreML.Type.t) =>
                        ( f
                        , case Record.peek (r, f) of
                            NONE => NestedPat.make (NestedPat.Wild, loopTy t)
                          | SOME p => patToNestedPat p
                        )
                    )))
          end
      | CoreML.Pat.Var v => MatchCompile.NestedPat.Var v
      | CoreML.Pat.Vector ts =>
          MatchCompile.NestedPat.Vector (Vector.map (ts, patToNestedPat))
      | CoreML.Pat.Wild => MatchCompile.NestedPat.Wild
  in
    MatchCompile.NestedPat.make (pat, ty')
  end

local
  val {get = conTycon, set = setConTycon, ...} = Property.getSet
    (CoreML.Con.plist, Property.initRaise ("conTycon", CoreML.Con.layout))
  val conTycon = Trace.trace ("Defunctorize.conTycon", CoreML.Con.layout, CoreML.Tycon.layout) conTycon
  val setConTycon =
         Trace.trace2
         ("Defunctorize.setConTycon",
          CoreML.Con.layout, CoreML.Tycon.layout, Unit.layout)
         setConTycon
  val {get = tyconCons, set = setTyconCons, ...} = Property.getSet
    (CoreML.Tycon.plist, Property.initRaise ("tyconCons", CoreML.Tycon.layout))
  fun recLayout {con, hasArg} = Layout.record [("con", CoreML.Con.layout con), ("hasArg", Bool.layout hasArg)]
  val tyconCons = Trace.trace ("Defunctorize.tyconCons", CoreML.Tycon.layout, Vector.layout recLayout) tyconCons
in
  fun compileMatches (dec: CoreML.Dec.t) : unit =
    let
      fun goCase {exp, matchDiags, rules, test, noMatch, region, ctxt} =
        let
          val caseType = loopTy (CoreML.Exp.ty exp)
          val cases = Vector.map (rules, fn {exp, pat, ...} =>
            (goExp exp; (patToNestedPat pat, fn _ => fn _ => ())))

          fun raiseExn () =
            let
              val e = CoreML.Var.newNoname ()
              val pat =
                MatchCompile.NestedPat.make
                  (MatchCompile.NestedPat.Var e, CoreML.Exp.ty test)
            in
              Vector.concat [cases, Vector.new1 (pat, fn _ => fn _ => ())]
            end
          val cases =
            let
              datatype z = datatype CoreML.Exp.noMatch
            in
              case noMatch of
                Impossible =>
                  ( print ("Impossible" ^ "\n")
                  ; Layout.outputl (CoreML.Exp.layout exp, Out.error)
                  ; cases
                  )
              | RaiseAgain => raiseExn ()
              | RaiseBind => raiseExn ()
              | RaiseMatch =>
                  ( print ("RaiseMatch" ^ "\n")
                  ; Layout.outputl (CoreML.Exp.layout exp, Out.error)
                  ; let val cases = raiseExn ()
                     in
                      Layout.outputl (Vector.layout MatchCompile.NestedPat.layout (Vector.map (cases, #1)), Out.error);
                      cases
                     end
                  )
            end
          val testType = loopTy (CoreML.Exp.ty test)
          val () = print ("Case Type: " ^ "\n")
          val () = Layout.outputl (CoreML.Type.layout caseType, Out.error)
          val () = print ("Test Type: " ^ "\n")
          val () = Layout.outputl (CoreML.Type.layout testType, Out.error)
          val test = CoreML.Var.newNoname ()
          val ((), nonexhaustive) =
            MatchCompile.matchCompile
              { caseType = CoreML.Type.bool
              , cases = cases
              , conTycon = conTycon
              , test = test
              , testType = CoreML.Type.bool
              , tyconCons = tyconCons
              }
            handle Fail text =>
              ( print ("Match compile error: " ^ text ^ "\n")
              ; print ("In case: " ^ "\n")
              ; Layout.outputl (CoreML.Exp.layout exp, Out.error)
              ; ((), fn _ => NONE)
              )
          val dropOnlyExns =
            case #nonexhaustiveExn matchDiags of
              Control.Elaborate.DiagDI.Default => false
            | Control.Elaborate.DiagDI.Ignore => true
        in
          case nonexhaustive {dropOnlyExns = false} of
            SOME layout =>
              (case #nonexhaustive matchDiags of
                 Control.Elaborate.DiagEIW.Error =>
                   ignore (Control.error
                     ( region
                     , Layout.seq [Layout.str "Match compile error: ", layout]
                     , ctxt ()
                     ))
               | Control.Elaborate.DiagEIW.Warn =>
                   ignore (Control.warning
                     ( region
                     , Layout.seq [Layout.str "Match compile warning: ", layout]
                     , ctxt ()
                     ))
               | Control.Elaborate.DiagEIW.Ignore => ())
          | NONE => ()
        end
      and goExp (exp: CoreML.Exp.t) : unit =
        case CoreML.Exp.node exp of
          CoreML.Exp.App (l, r) => (goExp l; goExp r)
        | CoreML.Exp.Con _ => ()
        | CoreML.Exp.Const _ => ()
        | CoreML.Exp.EnterLeave (t, _) => goExp t
        | CoreML.Exp.Handle {catch = _, handler, try} =>
            (goExp try; goExp handler)
        | CoreML.Exp.Lambda lambda => goLambda lambda
        | CoreML.Exp.Let (decs, t) =>
            (Vector.foreach (decs, compileMatches); goExp t)
        | CoreML.Exp.List exps => Vector.foreach (exps, goExp)
        | CoreML.Exp.PrimApp {args, ...} => Vector.foreach (args, goExp)
        | CoreML.Exp.Raise t => goExp t
        | CoreML.Exp.Record r => CoreML.Record.foreach (r, goExp)
        | CoreML.Exp.Var _ => ()
        | CoreML.Exp.Seq exps => Vector.foreach (exps, goExp)
        | CoreML.Exp.Vector exps => Vector.foreach (exps, goExp)
        | CoreML.Exp.Case {matchDiags, rules, test, noMatch, region, ctxt, ...} =>
            goCase
              { exp = exp
              , matchDiags = matchDiags
              , rules = rules
              , test = test
              , noMatch = noMatch
              , region = region
              , ctxt = ctxt
              }
      and goLambda lambda =
        goExp (#body (CoreML.Lambda.dest lambda))
    in
      case dec of
        CoreML.Dec.Datatype dbs =>
          let
            val frees: CoreML.Tyvar.t list ref = ref []
            val _ = Vector.foreach (dbs, fn {cons, tyvars, ...} =>
              let
                fun var (a: CoreML.Tyvar.t) : unit =
                  let
                    fun eq a' = CoreML.Tyvar.equals (a, a')
                  in
                    if
                      Vector.exists (tyvars, eq) orelse List.exists (!frees, eq)
                    then ()
                    else List.push (frees, a)
                  end
                val {destroy, hom} =
                  CoreML.Type.makeHom {con = fn _ => (), var = var}
                val _ = Vector.foreach (cons, fn {arg, ...} =>
                  Option.app (arg, hom))
                val _ = destroy ()
              in
                ()
              end)
            val frees = !frees
            val dbs =
              if List.isEmpty frees then
                dbs
              else
                let
                  val frees = Vector.fromList frees
                in
                  Vector.map (dbs, fn {cons, tycon, tyvars} =>
                    { cons = cons
                    , tycon = tycon
                    , tyvars = Vector.concat [frees, tyvars]
                    })
                end
          in
            Vector.foreach (dbs, fn {cons, tycon, tyvars} =>
              let
                val _ = setTyconCons (tycon, Vector.map (cons, fn {arg, con} =>
                  {con = con, hasArg = isSome arg}))
                val cons = Vector.map (cons, fn {arg, con} =>
                  (setConTycon (con, tycon); {arg = Option.map (arg, loopTy), con = con}))
              in
                ()
              end)
          end
      | CoreML.Dec.Exception {con, ...} => setConTycon (con, CoreML.Tycon.exn)
      | CoreML.Dec.Fun {decs, ...} =>
          Vector.foreach (decs, fn {lambda, ...} => goLambda lambda)
      | CoreML.Dec.Val {matchDiags, rvbs, vbs, tyvars} =>
          ( Vector.foreach (rvbs, fn {lambda, ...} => goLambda lambda)
          ; Vector.foreach (vbs, fn {ctxt, exp, pat, layPat, regionPat, ...} =>
              ( goCase
                  { exp = exp
                  , matchDiags = matchDiags
                  , rules = Vector.new1
                      { exp = exp
                      , layPat = SOME layPat
                      , pat = pat
                      , regionPat = regionPat
                      }
                  , test = exp
                  , noMatch = CoreML.Exp.RaiseBind
                  , region = regionPat
                  , ctxt = ctxt
                  }
              ; goExp exp
              ))
          )
    end
end

val lexAndParseMLB: MLBString.t -> Ast.Basdec.t = fn input =>
  let
    val ast = MLBString.lexAndParseMLB input
    val _ = Control.checkForErrors ()
  in
    ast
  end

fun parseAndElaborateMLB input =
  let
    val (E, decs) = Elaborate.elaborateMLB (input, {addPrim = Prim.addPrim})
    val _ = Control.checkForErrors ()
    fun checkMatches () =
      Vector.foreach (decs, fn (decs, _) => List.foreach (decs, compileMatches))
      before Control.checkForErrors ()
  in
    case Control.Elaborate.current (Control.Elaborate.nonexhaustiveMatch) of
      Control.Elaborate.DiagEIW.Error => checkMatches ()
    | Control.Elaborate.DiagEIW.Warn => checkMatches ()
    | Control.Elaborate.DiagEIW.Ignore => ()
  end

val escapeCode = "\^[[H\^["

fun clearScreen () = ()
(* let val strm = TextIO.openOut (Posix.ProcEnv.ctermid ())
in TextIO.output (strm, escapeCode ^ "c"); TextIO.closeOut strm
end *)

fun printTopLeft text = print text
(* let
  val strm = TextIO.openOut (Posix.ProcEnv.ctermid ())
in
  (* pad X by 15 spaces so that it is to the right of the status line *)
  TextIO.output (strm, escapeCode ^ "[1;15H" ^ text);
  TextIO.closeOut strm
end *)

fun inGreen text = text
  (* escapeCode ^ "[32m" ^ text ^ escapeCode ^ "[0m" *)
fun inRed text = text
  (* escapeCode ^ "[31m" ^ text ^ escapeCode ^ "[0m" *)

fun reelaborateForChanges lastTime mlb basdec =
  let
    fun isModified file =
      Time.> (File.modTime file, lastTime)
    fun reelaborateMLB mlb =
      ( if Option.isSome (HashTable.peek (Elaborate.psi, mlb)) then
          printTopLeft ("Reelaborating " ^ mlb ^ "\n")
        else
          ()
      ; HashTable.remove (Elaborate.psi, mlb) handle _ => ()
      ; true
      )
    fun reelaborateForChanges mlb (Ast.Basdec.Ann (_, _, basdec)) =
          reelaborateForChanges mlb (Ast.Basdec.node basdec)
      | reelaborateForChanges mlb (Ast.Basdec.MLB ({fileAbs, ...}, basdec)) =
          (if isModified fileAbs then
             reelaborateMLB fileAbs
           else
             reelaborateForChanges fileAbs
               (Ast.Basdec.node (Promise.force basdec)))
          andalso reelaborateMLB mlb
      | reelaborateForChanges mlb (Ast.Basdec.Seq basdecs) =
          List.exists
            ( List.map (basdecs, reelaborateForChanges mlb o Ast.Basdec.node)
            , fn b => b
            ) andalso reelaborateMLB mlb
      | reelaborateForChanges mlb (Ast.Basdec.Local (l, body)) =
          (reelaborateForChanges mlb (Ast.Basdec.node l)
           orelse reelaborateForChanges mlb (Ast.Basdec.node body))
          andalso reelaborateMLB mlb
      | reelaborateForChanges mlb (Ast.Basdec.Basis basexps) =
          let
            fun go (Ast.Basexp.Bas basdec) =
                  reelaborateForChanges mlb (Ast.Basdec.node basdec)
              | go (Ast.Basexp.Let (basdec, basexp)) =
                  reelaborateForChanges mlb (Ast.Basdec.node basdec)
                  orelse go (Ast.Basexp.node basexp)
              | go _ = false
            val basexps = Vector.map (basexps, fn {def, ...} =>
              go (Ast.Basexp.node def))
          in
            Vector.exists (basexps, fn b => b) andalso reelaborateMLB mlb
          end
      | reelaborateForChanges mlb (Ast.Basdec.Prog ({fileAbs, ...}, _)) =
          isModified fileAbs andalso reelaborateMLB mlb
      | reelaborateForChanges _ _ = false
  in
    reelaborateForChanges mlb (Ast.Basdec.node basdec)
  end

fun diagnosticToFile file thunk =
  File.withOut (file, fn out =>
    let
      val writer = ! Control.diagnosticWriter
      val () =
        Control.diagnosticWriter
        := SOME (fn layout => Layout.outputl (layout, out))
      val result = thunk ()
                   handle e => (Control.diagnosticWriter := writer; raise e);
    in
      Control.diagnosticWriter := writer;
      result
    end)

fun printStatus seconds =
  if ! Control.numErrors > 0 then
    print (inRed ("Error (" ^ IntInf.toString seconds ^ "s):\n"))
  else
    print (inGreen ("Success (" ^ IntInf.toString seconds ^ "s):\n"))

fun setControlRefs () =
  let
    exception InvalidEnvVar
    val mltonDir =
      case OS.Process.getEnv "LIB_MLTON_DIR" of
        SOME path => path
      | NONE =>
          ( print "Expected LIB_MLTON_DIR environment variable to be set\n"
          ; raise InvalidEnvVar
          )
    val target =
      case OS.Process.getEnv "TARGET" of
        SOME path => path
      | NONE => "self"
    fun addVar tup =
      Control.mlbPathVars := tup :: ! Control.mlbPathVars
  in
    case OS.Process.getEnv "SML_LIB" of
      SOME path => addVar {var = "SML_LIB", path = path}
    | NONE =>
        ( print "Expected SML_LIB environment variable to be set\n"
        ; raise InvalidEnvVar
        );
    addVar {var = "LIB_MLTON_DIR", path = mltonDir};
    addVar {var = "TARGET", path = target};
    Control.libTargetDir := mltonDir ^ "/targets/" ^ target
  end

structure Main =
struct
  fun main _ =
    let
      (* val () = Trace.Immediate.on ["Defunctorize.conTycon", "Defunctorize.tyconCons", "Defunctorize.setConTycon"] *)
      val () = Trace.Immediate.all ()
      val () = setControlRefs ()
      exception InvalidArgument
      val arg =
        case CommandLine.arguments () of
          [arg] => arg
        | _ =>
            (print "Expected MLB file path argument\n"; raise InvalidArgument)
      val () = clearScreen ()
      val time = ref (Time.now ())
      val errorFile = OS.FileSys.tmpName ()
    in
      Control.diagnosticWriter
      := SOME (fn layout => Layout.outputl (layout, Out.error));
      print "Initial elaboration...\n";
      ( parseAndElaborateMLB (lexAndParseMLB (MLBString.fromMLBFile arg))
      ; clearScreen ()
      ; printStatus (Time.toSeconds (Time.- (Time.now (), !time)))
      )
      handle
        Fail text => (print ("Fail: " ^ text ^ "\n"); raise Fail text)
      | _ => ();
      while true do
        let
          val () = Control.numErrors := 0
          val startTime = Time.now ()
          val basis = lexAndParseMLB (MLBString.fromMLBFile arg)
          val changed =
            diagnosticToFile errorFile (fn () =>
              let
                val changed = reelaborateForChanges (!time) arg basis
              in
                if changed then
                  (time := Time.now (); parseAndElaborateMLB basis)
                else
                  ();
                changed
              end)
            handle
              Fail text => (print ("Fail: " ^ text ^ "\n"); raise Fail text)
            | _ => true
          val seconds = Time.toSeconds (Time.- (Time.now (), startTime))
        in
          if changed then
            ( clearScreen ()
            ; printStatus seconds
            ; File.withIn (errorFile, fn inn => In.foreachLine (inn, print))
            )
          else
            OS.Process.sleep (Time.seconds 1)
        end
        handle _ => print "Error parsing MLB\n";
      OS.Process.success
    end
end

fun main () =
  ignore (Main.main ("", []))
val () = if MLton.isMLton then main () else ()

(* fun a (SOME 1, SOME 2) = NONE *)
fun a (1, 2) = (3, 4)

