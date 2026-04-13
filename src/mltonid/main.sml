structure Atoms = Atoms ()
structure Symbol = Atoms.Symbol
structure Ast = Ast (open Atoms)
structure TypeEnv = TypeEnv (open Atoms)
structure CoreML = CoreML (open Atoms
                           structure Type =
                              struct
                                 open TypeEnv.Type

                                 val makeHom =
                                    fn {con, var} =>
                                    makeHom {con = con,
                                             expandOpaque = true,
                                             var = var}

                                 fun layout t =
                                    #1 (layoutPretty
                                        (t, {expandOpaque = true,
                                             layoutPrettyTycon = Tycon.layout,
                                             layoutPrettyTyvar = Tyvar.layout}))
                              end)
structure FrontEnd = FrontEnd (structure Ast = Ast)
structure MLBFrontEnd = MLBFrontEnd (structure Ast = Ast
                                     structure FrontEnd = FrontEnd)
structure Elaborate = Elaborate (structure Ast = Ast
                                 structure CoreML = CoreML
                                 structure TypeEnv = TypeEnv)
structure Env = Elaborate.Env

structure MLBString:>
   sig
      type t

      val fromMLBFile: File.t -> t
      val fromSMLFile: File.t -> t
      val lexAndParseMLB: t -> Ast.Basdec.t
   end =
   struct
      type t = string

      fun quoteFile s = concat ["\"", String.escapeSML s, "\""]

      val fromMLBFile = quoteFile

      fun fromSMLFile input =
         let
            val basis = "$(SML_LIB)/basis/default.mlb"
         in
            String.concat
            ["local\n",
             basis, "\n",
             "in\n",
             quoteFile input, "\n",
             "end\n"]
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
   structure Tyvar =
      struct
         open TypeEnv.Tyvar
         open TypeEnv.TyvarExt
      end

   val primitiveDatatypes =
      Vector.new3
      ({tycon = Tycon.bool,
        tyvars = Vector.new0 (),
        cons = Vector.new2 ({con = Con.falsee, arg = NONE},
                            {con = Con.truee, arg = NONE})},
       let
          val a = Tyvar.makeNoname {equality = false}
       in
          {tycon = Tycon.list,
           tyvars = Vector.new1 a,
           cons = Vector.new2 ({con = Con.nill, arg = NONE},
                               {con = Con.cons,
                                arg = SOME (Type.tuple
                                            (Vector.new2
                                             (Type.var a,
                                              Type.list (Type.var a))))})}
       end,
       let
          val a = Tyvar.makeNoname {equality = false}
       in
          {tycon = Tycon.reff,
           tyvars = Vector.new1 a,
           cons = Vector.new1 {con = Con.reff, arg = SOME (Type.var a)}}
       end)

   val primitiveExcons =
      let
         open CoreML.Con
      in
         [bind, match]
      end

   structure Con =
      struct
         open Con

         fun toAst c =
            Ast.Con.fromSymbol (Symbol.fromString (Con.toString c),
                                Region.bogus)
      end

   structure Env =
      struct
         open Env

         structure Tycon =
            struct
               open Tycon

               fun toAst c =
                  Ast.Tycon.fromSymbol (Symbol.fromString (Tycon.toString c),
                                        Region.bogus)
            end
         structure Type = TypeEnv.Type
         structure Scheme = TypeEnv.Scheme

         fun addPrim (E: t): unit =
            let
               val _ =
                  List.foreach
                  (Tycon.prims, fn {name, tycon, ...} =>
                   if List.contains ([Tycon.arrow, Tycon.tuple], tycon, Tycon.equals)
                      then ()
                      else extendTycon
                           (E, Ast.Tycon.fromSymbol (Symbol.fromString name,
                                                     Region.bogus),
                            TypeStr.tycon tycon,
                            {forceUsed = false, isRebind = false}))
               val _ =
                  Vector.foreach
                  (primitiveDatatypes, fn {tyvars, tycon, cons} =>
                   let
                      val cons =
                         Vector.map
                         (cons, fn {con, arg} =>
                          let
                             val res =
                                Type.con (tycon, Vector.map (tyvars, Type.var))
                             val ty =
                                case arg of
                                   NONE => res
                                 | SOME arg => Type.arrow (arg, res)
                             val scheme =
                                Scheme.make
                                {canGeneralize = true,
                                 ty = ty,
                                 tyvars = tyvars}
                          in
                             {con = con,
                              name = Con.toAst con,
                              scheme = scheme}
                          end)
                      val cons = Env.newCons (E, cons)
                   in
                      extendTycon
                      (E, Tycon.toAst tycon,
                       TypeStr.data (tycon, cons),
                       {forceUsed = false, isRebind = false})
                   end)
               val _ =
                  extendTycon (E,
                               Ast.Tycon.fromSymbol (Symbol.unit, Region.bogus),
                               TypeStr.def (Scheme.fromType Type.unit),
                               {forceUsed = false, isRebind = false})
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
         List.concat [[Datatype primitiveDatatypes],
                      List.map
                      (primitiveExcons, fn c =>
                       Exception {con = c, arg = NONE})]
      end

in
   fun addPrim E =
      (Env.addPrim E
       ; primitiveDecs)
end

val lexAndParseMLB: MLBString.t -> Ast.Basdec.t =
   fn input =>
   let
      val ast = MLBString.lexAndParseMLB input
      val _ = Control.checkForErrors ()
   in
      ast
   end

fun parseAndElaborateMLB input addPrim =
   let
      val (E, decs) = Elaborate.elaborateMLB (input, {addPrim = addPrim})
      val _ = Control.checkForErrors ()
   in
      ()
   end

(* TODO: put this in configuration file or environment variables *)
val () = Control.mlbPathVars := {var = "SML_LIB", path = "/usr/local/lib/mlton/sml"}
   :: {var = "LIB_MLTON_DIR", path = "/home/d/Documents/mirrored/mlton/build/lib/mlton"}
   :: {var = "TARGET", path = "self"}
   :: !Control.mlbPathVars

fun reelaborateForChanges (lastTime, basdec) =
let
   exception NotInTable
   val changed = HashTable.new {hash = String.hash, equals = String.equals}
   fun isModified file = Time.>(File.modTime file, lastTime)
   fun reelaborateMLB basis =
      case Ast.Basdec.node basis of
         Ast.Basdec.MLB ({fileAbs, ...}, basdec) =>
            HashTable.lookupOrInsert (changed, fileAbs, fn () =>
            let
               val () = print ("Reelaborating: " ^ fileAbs ^ "\n")
               val oldBasis = HashTable.lookupOrInsert (Elaborate.psi, fileAbs, fn () => raise NotInTable)
               val () = HashTable.remove (Elaborate.psi, fileAbs)
               val () = parseAndElaborateMLB basis (fn _ => [])
               val newBasis = HashTable.lookupOrInsert (Elaborate.psi, fileAbs, fn () => raise NotInTable)
            in
               (* Layout.toString (Layout.compact (Env.Basis.layout oldBasis)) <> Layout.toString (Layout.compact (Env.Basis.layout newBasis)) *)
               true
            end
            handle NotInTable => (HashTable.remove (Elaborate.psi, fileAbs) handle _ => (); true))
      |  _ => true
   fun reelaborateForChanges (mlb : Ast.Basdec.t) (basis : Ast.Basdec.t) =
      case Ast.Basdec.node basis of
        Ast.Basdec.Ann (_, _, basdec) => reelaborateForChanges mlb basdec
      | Ast.Basdec.MLB ({fileAbs, ...}, basdec) =>
          let val basdec = Promise.force basdec
          in
           (if isModified fileAbs then reelaborateMLB basis
            else reelaborateForChanges basis basdec)
           andalso reelaborateMLB mlb
          end
      | Ast.Basdec.Seq basdecs =>
          List.exists (List.map (basdecs, reelaborateForChanges mlb), fn b => b)
      | Ast.Basdec.Local (l, body) =>
          ( ignore (reelaborateForChanges mlb l)
          ; reelaborateForChanges mlb body
          )
      | Ast.Basdec.Basis basexps =>
          let
            fun go (Ast.Basexp.Bas basdec) = reelaborateForChanges mlb basdec
              | go (Ast.Basexp.Let (basdec, basexp)) =
                reelaborateForChanges mlb basdec
                orelse go (Ast.Basexp.node basexp)
              | go _ = false
            val basexps = Vector.map (basexps, fn {def, ...} => go (Ast.Basexp.node def))
          in
            Vector.exists (basexps, fn b => b)
          end
      | Ast.Basdec.Prog ({fileAbs, ...}, _) =>
          isModified fileAbs andalso reelaborateMLB mlb
      | _ => false
in
   reelaborateForChanges basdec basdec
end

(* datatype basexpNode =
   Bas of basdec
 | Let of basdec * basexp
 | Var of Basid.t *)
   (* Ann of string * Region.t * basdec
 | Basis of {name: Basid.t, def: basexp} vector
 | Defs of ModIdBind.t
 | Local of basdec * basdec
 | MLB of {fileAbs: File.t, fileUse: File.t} * basdec Promise.t
 | Open of Basid.t vector
 | Prim
 | Prog of {fileAbs: File.t, fileUse: File.t} * Program.t Promise.t
 | Seq of basdec list *)

fun main () =
let
   val arg =
      case CommandLine.arguments () of
        [arg] => arg
      | _ => raise Fail "Expected argument"
   val () = print ("Arg: " ^ arg ^ "\n")
   val time = ref (Time.now ())
   val () = parseAndElaborateMLB (lexAndParseMLB (MLBString.fromMLBFile arg)) addPrim handle _ => ()
in
   while true do
   let
      val () = Control.numErrors := 0
      val basis = lexAndParseMLB (MLBString.fromMLBFile arg)
      val time' = Time.now ()
      val changed = reelaborateForChanges (!time, basis) handle _ => true
      val () = time := time'
      val finishTime = Time.now ()
      val seconds: IntInf.int = Time.toSeconds (Time.-(finishTime, time'))
      val () = if changed then print ("Finished reelaborating in " ^ IntInf.toString seconds ^ " seconds\n") else ()
      val () = if not changed then OS.Process.sleep (Time.seconds 1) else ()
   in
      ()
   end
end

val () = if MLton.isMLton then main () else ()