structure Atoms = Atoms()
structure Symbol = Atoms.Symbol
structure Ast = Ast(open Atoms)
structure TypeEnv = TypeEnv(open Atoms)
structure CoreML =
  CoreML
    (open Atoms
     structure Type =
     struct
       open TypeEnv.Type

       val makeHom = fn {con, var} =>
         makeHom {con = con, expandOpaque = true, var = var}

       fun layout t =
         #1 (layoutPretty
           ( t
           , { expandOpaque = true
             , layoutPrettyTycon = Tycon.layout
             , layoutPrettyTyvar = Tyvar.layout
             }
           ))
     end)
structure FrontEnd = FrontEnd (structure Ast = Ast)
structure MLBFrontEnd =
  MLBFrontEnd (structure Ast = Ast structure FrontEnd = FrontEnd)
structure Elaborate =
  Elaborate
    (structure Ast = Ast structure CoreML = CoreML structure TypeEnv = TypeEnv)
structure Env = Elaborate.Env

structure MatchCompile =
  MatchCompile
    (open CoreML
     structure Type =
     struct open Type val deTuple = fn t => Vector.map (deRecord t, #2) end
     structure Pat =
     struct
       datatype t =
         T of {arg: (Var.t * Type.t) option, con: Con.t, targs: Type.t vector}
     end
     structure Exp =
     struct
       type t = unit

       val casee = fn _ => ()
       val const = fn _ => ()
       val deref = fn _ => ()
       val detuple = fn _ => ()
       val devector = fn _ => ()
       val equal = fn _ => ()
       val iff = fn _ => ()
       val lett = fn _ => ()
       val var = fn _ => ()
       val vectorLength = fn _ => ()
     end
     structure NestedPat = NestedPat(open CoreML))

structure MLBString :>
sig
  type t

  val fromMLBFile: File.t -> t
  val fromSMLFile: File.t -> t
  val lexAndParseMLB: t -> Ast.Basdec.t
end =
struct
  type t = string

  fun quoteFile s =
    concat ["\"", String.escapeSML s, "\""]

  val fromMLBFile = quoteFile

  fun fromSMLFile input =
    let
      val basis = "$(SML_LIB)/basis/default.mlb"
    in
      String.concat
        ["local\n", basis, "\n", "in\n", quoteFile input, "\n", "end\n"]
    end

  val lexAndParseMLB = MLBFrontEnd.lexAndParseString
end

(* ------------------------------------------------- *)
(*                   Primitive Env                   *)
(* ------------------------------------------------- *)

local
  structure Con = TypeEnv.Con
  structure Tycon = TypeEnv.Tycon
  structure Type = TypeEnv.Type
  structure Tyvar = struct open TypeEnv.Tyvar open TypeEnv.TyvarExt end

  val primitiveDatatypes = Vector.new3
    ( { tycon = Tycon.bool
      , tyvars = Vector.new0 ()
      , cons =
          Vector.new2
            ({con = Con.falsee, arg = NONE}, {con = Con.truee, arg = NONE})
      }
    , let
        val a = Tyvar.makeNoname {equality = false}
      in
        { tycon = Tycon.list
        , tyvars = Vector.new1 a
        , cons = Vector.new2
            ( {con = Con.nill, arg = NONE}
            , { con = Con.cons
              , arg = SOME (Type.tuple (Vector.new2
                  (Type.var a, Type.list (Type.var a))))
              }
            )
        }
      end
    , let
        val a = Tyvar.makeNoname {equality = false}
      in
        { tycon = Tycon.reff
        , tyvars = Vector.new1 a
        , cons = Vector.new1 {con = Con.reff, arg = SOME (Type.var a)}
        }
      end
    )

  val primitiveExcons = let open CoreML.Con in [bind, match] end

  structure Con =
  struct
    open Con

    fun toAst c =
      Ast.Con.fromSymbol (Symbol.fromString (Con.toString c), Region.bogus)
  end

  structure Env =
  struct
    open Env

    structure Tycon =
    struct
      open Tycon

      fun toAst c =
        Ast.Tycon.fromSymbol
          (Symbol.fromString (Tycon.toString c), Region.bogus)
    end
    structure Type = TypeEnv.Type
    structure Scheme = TypeEnv.Scheme

    fun addPrim (E: t) : unit =
      let
        val _ = List.foreach (Tycon.prims, fn {name, tycon, ...} =>
          if List.contains ([Tycon.arrow, Tycon.tuple], tycon, Tycon.equals) then
            ()
          else
            extendTycon
              ( E
              , Ast.Tycon.fromSymbol (Symbol.fromString name, Region.bogus)
              , TypeStr.tycon tycon
              , {forceUsed = false, isRebind = false}
              ))
        val _ = Vector.foreach (primitiveDatatypes, fn {tyvars, tycon, cons} =>
          let
            val cons = Vector.map (cons, fn {con, arg} =>
              let
                val res = Type.con (tycon, Vector.map (tyvars, Type.var))
                val ty =
                  case arg of
                    NONE => res
                  | SOME arg => Type.arrow (arg, res)
                val scheme =
                  Scheme.make {canGeneralize = true, ty = ty, tyvars = tyvars}
              in
                {con = con, name = Con.toAst con, scheme = scheme}
              end)
            val cons = Env.newCons (E, cons)
          in
            extendTycon
              ( E
              , Tycon.toAst tycon
              , TypeStr.data (tycon, cons)
              , {forceUsed = false, isRebind = false}
              )
          end)
        val _ = extendTycon
          ( E
          , Ast.Tycon.fromSymbol (Symbol.unit, Region.bogus)
          , TypeStr.def (Scheme.fromType Type.unit)
          , {forceUsed = false, isRebind = false}
          )
        val scheme = Scheme.fromType Type.exn
        val _ = List.foreach (primitiveExcons, fn c =>
          extendExn (E, Con.toAst c, c, scheme))
      in
        ()
      end
  end

  val primitiveDecs: CoreML.Dec.t list =
    let
      open CoreML.Dec
    in
      List.concat
        [ [Datatype primitiveDatatypes]
        , List.map (primitiveExcons, fn c => Exception {con = c, arg = NONE})
        ]
    end

in
  fun addPrim E =
    (Env.addPrim E; primitiveDecs)
end

fun patToNestedPat (pat: CoreML.Pat.t) : MatchCompile.NestedPat.t =
  let
    val ty = CoreML.Pat.ty pat
    val pat =
      case CoreML.Pat.node pat of
        CoreML.Pat.Con {arg, con, targs} =>
          MatchCompile.NestedPat.Con
            {arg = Option.map (arg, patToNestedPat), con = con, targs = targs}
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
            val targs = #2 (valOf (CoreML.Type.deConOpt ty))
          in
            Vector.fold
              ( ts
              , NestedPat.Con {arg = NONE, con = CoreML.Con.nill, targs = targs}
              , fn (p, np) =>
                  NestedPat.Con
                    { arg = SOME (NestedPat.tuple (Vector.new2
                        (patToNestedPat p, NestedPat.make (np, ty))))
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
            NestedPat.Record (SortedRecord.fromVector (Record.toVector
              (Record.map (r, patToNestedPat))))
          end
      | CoreML.Pat.Var v => MatchCompile.NestedPat.Var v
      | CoreML.Pat.Vector ts =>
          MatchCompile.NestedPat.Vector (Vector.map (ts, patToNestedPat))
      | CoreML.Pat.Wild => MatchCompile.NestedPat.Wild
  in
    MatchCompile.NestedPat.T {pat = pat, ty = ty}
  end

(* datatype t = T of {pat: node, ty: Type.t}
and node =
   Con of {arg: t option,
           con: Con.t,
           targs: Type.t vector}
  | Const of {const: Const.t,
              isChar: bool,
              isInt: bool}
  | Layered of Var.t * t
  | Or of t vector
  | Record of t SortedRecord.t
  | Var of Var.t
  | Vector of t vector
  | Wild *)

(* datatype node =
   Con of {arg: t option,
           con: Con.t,
           targs: Type.t vector}
 | Const of unit -> Const.t
 | Layered of Var.t * t
 | List of t vector
 | Or of t vector
 | Record of t Record.t
 | Var of Var.t
 | Vector of t vector
 | Wild *)

local
  val tmp = ref (CoreML.Var.fromString "tmp")
  fun freshVar () =
    (tmp := CoreML.Var.new (!tmp); !tmp)
  val {get = conTycon, set = setConTycon, ...} = Property.getSetOnce
    (CoreML.Con.plist, Property.initRaise ("conTycon", CoreML.Con.layout))
  val {get = tyconCons, set = setTyconCons, ...} = Property.getSetOnce
    (CoreML.Tycon.plist, Property.initRaise ("tyconCons", CoreML.Tycon.layout))
in
  fun compileMatches (dec: CoreML.Dec.t) : unit =
    let
      val () = print ("Dec: " ^ "\n")
      val () = Layout.outputl (CoreML.Dec.layout dec, Out.error)
      fun goExp (exp: CoreML.Exp.t) : unit =
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
        | CoreML.Exp.Case {matchDiags, rules, test, ...} =>
            let
              val () = print ("Hitting case: " ^ "\n")
              val () = Layout.outputl (CoreML.Exp.layout exp, Out.error)
              val caseType = CoreML.Exp.ty exp
              val cases = Vector.map (rules, fn {exp, pat, ...} =>
                (goExp exp; (patToNestedPat pat, fn _ => fn _ => ())))
              val testType = CoreML.Exp.ty test
              val test = freshVar ()
              val ((), nonexhaustive) = MatchCompile.matchCompile
                { caseType = caseType
                , cases = cases
                , conTycon = conTycon
                , test = test
                , testType = testType
                , tyconCons = tyconCons
                }
            in
              case nonexhaustive {dropOnlyExns = true} of
                SOME layout =>
                  (case
                     Control.Elaborate.current
                       (Control.Elaborate.nonexhaustiveMatch)
                   of
                     Control.Elaborate.DiagEIW.Error =>
                       ignore
                         (Control.error
                            ( Region.bogus
                            , Layout.str "Match compile error:"
                            , layout
                            ))
                   | Control.Elaborate.DiagEIW.Warn =>
                       ignore
                         (Control.warning
                            ( Region.bogus
                            , Layout.str "Match compile warning:"
                            , layout
                            ))
                   | Control.Elaborate.DiagEIW.Ignore => ())
              | NONE => ();
              print "Completed\n"
            end
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
                  (setConTycon (con, tycon); {arg = arg, con = con}))
              in
                ()
              end)
          end
      | CoreML.Dec.Exception {con, ...} => setConTycon (con, CoreML.Tycon.exn)
      | CoreML.Dec.Fun {decs, ...} =>
          Vector.foreach (decs, fn {lambda, ...} => goLambda lambda)
      | CoreML.Dec.Val {matchDiags, rvbs, vbs, ...} =>
          ( Vector.foreach (rvbs, fn {lambda, ...} => goLambda lambda)
          ; Vector.foreach (vbs, fn {exp, pat, ...} =>
              (* TODO: check if pat and exp are exhaustive *)
              goExp exp)
          )
    end
end

(* datatype node =
   App of t * t
 | Case of {ctxt: unit -> Layout.t,
            kind: string * string,
            nest: string list,
            matchDiags: {nonexhaustiveExn: Control.Elaborate.DiagDI.t,
                         nonexhaustive: Control.Elaborate.DiagEIW.t,
                         redundant: Control.Elaborate.DiagEIW.t},
            noMatch: noMatch,
            region: Region.t,
            rules: {exp: t,
                    layPat: (unit -> Layout.t) option,
                    pat: Pat.t,
                    regionPat: Region.t} vector,
            test: t}
 | Con of Con.t * Type.t vector
 | Const of unit -> Const.t
 | EnterLeave of t * SourceInfo.t
 | Handle of {catch: Var.t * Type.t,
              handler: t,
              try: t}
 | Lambda of lambda
 | Let of dec vector * t
 | List of t vector
 | PrimApp of {args: t vector,
               prim: Type.t Prim.t,
               targs: Type.t vector}
 | Raise of t
 | Record of t Record.t
 | Seq of t vector
 | Var of (unit -> Var.t) * (unit -> Type.t vector)
 | Vector of t vector *)
(* structure Lambda:
   sig
      type t

      val bogus: t
      val dest: t -> {arg: Var.t,
                      argType: Type.t,
                      body: Exp.t,
                      mayInline: bool}
      val make: {arg: Var.t,
                 argType: Type.t,
                 body: Exp.t,
                 mayInline: bool} -> t
   end
sharing type Exp.lambda = Lambda.t *)

(* datatype t =
   Datatype of {cons: {arg: Type.t option,
                       con: Con.t} vector,
                tycon: Tycon.t,
                tyvars: Tyvar.t vector} vector
 | Exception of {arg: Type.t option,
                 con: Con.t}
 | Fun of {decs: {lambda: Lambda.t,
                  var: Var.t} vector,
           tyvars: unit -> Tyvar.t vector}
 | Val of {matchDiags: {nonexhaustiveExn: Control.Elaborate.DiagDI.t,
                        nonexhaustive: Control.Elaborate.DiagEIW.t,
                        redundant: Control.Elaborate.DiagEIW.t},
           rvbs: {lambda: Lambda.t,
                  var: Var.t} vector,
           tyvars: unit -> Tyvar.t vector,
           vbs: {ctxt: unit -> Layout.t,
                 exp: Exp.t,
                 layPat: unit -> Layout.t,
                 nest: string list,
                 pat: Pat.t,
                 regionPat: Region.t} vector} *)

val lexAndParseMLB: MLBString.t -> Ast.Basdec.t = fn input =>
  let
    val ast = MLBString.lexAndParseMLB input
    val _ = Control.checkForErrors ()
  in
    ast
  end

fun parseAndElaborateMLB input =
  let
    val (E, decs) = Elaborate.elaborateMLB (input, {addPrim = addPrim})
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

fun clearScreen () =
  let val strm = TextIO.openOut (Posix.ProcEnv.ctermid ())
  in TextIO.output (strm, escapeCode ^ "c"); TextIO.closeOut strm
  end

fun printTopLeft text =
  let
    val strm = TextIO.openOut (Posix.ProcEnv.ctermid ())
  in
    (* pad X by 15 spaces so that it is to the right of the status line *)
    TextIO.output (strm, escapeCode ^ "[1;15H" ^ text);
    TextIO.closeOut strm
  end

fun inGreen text =
  escapeCode ^ "[32m" ^ text ^ escapeCode ^ "[0m"
fun inRed text =
  escapeCode ^ "[31m" ^ text ^ escapeCode ^ "[0m"

fun reelaborateForChanges lastTime mlb basdec =
  let
    fun isModified file =
      Time.> (File.modTime file, lastTime)
    fun reelaborateMLB mlb =
      ( if Option.isSome (HashTable.peek (Elaborate.psi, mlb)) then
          print ("Reelaborating " ^ mlb ^ "\n")
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
    print ( (* inRed *)("Error (" ^ IntInf.toString seconds ^ "s):\n"))
  else
    print ( (* inGreen *)("Success (" ^ IntInf.toString seconds ^ "s):\n"))

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

fun main () =
  let
    val () = setControlRefs ()
    exception InvalidArgument
    val arg =
      case CommandLine.arguments () of
        [arg] => arg
      | _ => (print "Expected MLB file path argument\n"; raise InvalidArgument)
    (* val () = clearScreen () *)
    val time = ref (Time.now ())
    val errorFile = OS.FileSys.tmpName ()
  in
    Control.diagnosticWriter
    := SOME (fn layout => Layout.outputl (layout, Out.error));
    print "Initial elaboration...\n";
    ( parseAndElaborateMLB (lexAndParseMLB (MLBString.fromMLBFile arg))
    (* ; clearScreen () *)
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
              if changed then (time := Time.now (); parseAndElaborateMLB basis)
              else ();
              changed
            end)
          handle
            Fail text => (print ("Fail: " ^ text ^ "\n"); raise Fail text)
          | _ => true
        val seconds = Time.toSeconds (Time.- (Time.now (), startTime))
      in
        if changed then
          ( (* clearScreen () ; *) printStatus seconds
          ; File.withIn (errorFile, fn inn => In.foreachLine (inn, print))
          )
        else
          OS.Process.sleep (Time.seconds 1)
      end
      handle _ => print "Error parsing MLB\n"
  end

val () = if MLton.isMLton then main () else ()

structure Foo =
struct
  fun foo (SOME 1) = print "hello"
end
