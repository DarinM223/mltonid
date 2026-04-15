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
  in
    ()
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

fun main () =
  let
    val () = setControlRefs ()
    exception InvalidArgument
    val arg =
      case CommandLine.arguments () of
        [arg] => arg
      | _ => (print "Expected MLB file path argument\n"; raise InvalidArgument)
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
    handle _ => ();
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
          handle _ => true
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
      handle _ => print "Error parsing MLB\n"
  end

val () = if MLton.isMLton then main () else ()
