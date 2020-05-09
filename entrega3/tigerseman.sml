structure tigerseman :> tigerseman =
struct

open tigerabs
open tigersres
open tigertrans
open tigertopsort

type expty = {exp: unit, ty: Tipo}

type venv = (string, EnvEntry) tigertab.Tabla
type tenv = (string, Tipo) tigertab.Tabla

val tab_tipos : (string, Tipo) Tabla = tabInserList(
    tabNueva(),
    [("int", TInt), ("string", TString)])

val levelPila: tigertrans.level tigerpila.Pila = tigerpila.nuevaPila1(tigertrans.outermost)
fun pushLevel l = tigerpila.pushPila levelPila l
fun popLevel() = tigerpila.popPila levelPila
fun topLevel() = tigerpila.topPila levelPila

val tab_vars : (string, EnvEntry) Tabla = tabInserList(
    tabNueva(),
    [("print", Func{level=topLevel(), label="print",
        formals=[TString], result=TUnit, extern=true}),
    ("flush", Func{level=topLevel(), label="flush",
        formals=[], result=TUnit, extern=true}),
    ("getchar", Func{level=topLevel(), label="getstr",
        formals=[], result=TString, extern=true}),
    ("ord", Func{level=topLevel(), label="ord",
        formals=[TString], result=TInt, extern=true}),
    ("chr", Func{level=topLevel(), label="chr",
        formals=[TInt], result=TString, extern=true}),
    ("size", Func{level=topLevel(), label="size",
        formals=[TString], result=TInt, extern=true}),
    ("substring", Func{level=topLevel(), label="substring",
        formals=[TString, TInt, TInt], result=TString, extern=true}),
    ("concat", Func{level=topLevel(), label="concat",
        formals=[TString, TString], result=TString, extern=true}),
    ("not", Func{level=topLevel(), label="not",
        formals=[TInt], result=TInt, extern=true}),
    ("exit", Func{level=topLevel(), label="exit",
        formals=[TInt], result=TUnit, extern=true})
    ])

(*fun tipoReal (TTipo (s, ref (SOME (t)))) = tipoReal t
  | tipoReal t = t*)

(* Print the keys of of the given table/map *)
fun printTable location tenv =
    let
        val _ = print ("["^location^"] type environment >>>\n")
        val _ = List.app (fn (name) => print ("\t"^name^"\n")) (tabClaves tenv)
        val _ = print ("["^location^"] type environment <<<\n")
    in
        ()
    end

(* PrettyTipo convert a tigertips.Tipo object to string *)
fun pt ty = tigerpp.prettyPrintTipo ty

(* PrintPrettyTipo print the PrettyTipo *)
fun ppt ty = print ((pt ty)^"\n")


(* Compare the nature of the Tipos *)
fun tiposIguales (TRecord _) TNil = true
  | tiposIguales TNil (TRecord _) = true
  | tiposIguales (TRecord (_, u1)) (TRecord (_, u2 )) = (u1=u2)
  | tiposIguales (TArray (_, u1)) (TArray (_, u2)) = (u1=u2)
  | tiposIguales a b = (a=b)

fun transExp(venv, tenv) =
    let fun error(s, p) = raise Fail ("Error -- línea "^Int.toString(p)^": "^s^"\n")
        fun trexp(VarExp v) = trvar(v)
        | trexp(UnitExp _) = {exp=unitExp(), ty=TUnit}
        | trexp(NilExp _)= {exp=nilExp(), ty=TNil}
        | trexp(IntExp(i, _)) = {exp=intExp i, ty=TInt}
        | trexp(StringExp(s, _)) = {exp=stringExp(s), ty=TString}
        | trexp(CallExp({func, args}, nl)) =
            let
                val (argtypes, resultstype, level, label, extern) =
                    case tabBusca(func, venv) of
                        SOME (Func {formals=formals, result=result, level=level, label=label, extern=extern}) => (formals, result, level, label, extern)
                        | _ => error("trexp::CallExp - Funcion "^func^" no definida", nl)
                val argexplist = List.map trexp args
                val argexplist_onlyexp = List.map (#exp) argexplist
                val isproc = TUnit = resultstype
                val argexplisttypes = List.map (#ty) argexplist
                val _ = if List.length argtypes = List.length argexplisttypes then ()
                            else error("trexp::CallExp - Funcion "^func^" invocada con una cantidad incorrecta de argumentos!", nl)
                val _ = List.map (fn(x, y) => if tiposIguales x y then x
                            else error("trexp::CallExp error de tipos", nl)) (ListPair.zip(argexplisttypes, argtypes))
                        handle Empty => error("trexp::CallExp - Nº de args", nl)
            in
                {exp=callExp(label, extern, isproc, level, argexplist_onlyexp), ty=resultstype}
            end
        | trexp(OpExp({left, oper=EqOp, right}, nl)) =
            let
                val {exp=expl, ty=tyl} = trexp left
                val {exp=expr, ty=tyr} = trexp right
                val opExp = if tiposIguales tyl TString
                            then binOpStrExp {left=expl,oper=EqOp,right=expr}
                            else binOpIntRelExp {left=expl,oper=EqOp,right=expr}
            in
                if tiposIguales tyl tyr andalso not (tyl=TNil andalso tyr=TNil) andalso tyl<>TUnit
                then {exp=opExp, ty=TInt}
                else error("Tipos no comparables "^pt(tyl)^" "^pt(tyr), nl)
            end
        | trexp(OpExp({left, oper=NeqOp, right}, nl)) =
            let
                val {exp=expl, ty=tyl} = trexp left
                val {exp=expr, ty=tyr} = trexp right
            in
                if tiposIguales tyl tyr andalso not (tyl=TNil andalso tyr=TNil) andalso tyl<>TUnit then
                    {exp=if tiposIguales tyl TString then binOpStrExp {left=expl,oper=NeqOp,right=expr} else binOpIntRelExp {left=expl,oper=NeqOp,right=expr}, ty=TInt}
                    else error("Tipos no comparables "^pt(tyl)^" "^pt(tyr), nl)
                    (*else error("Tipos no comparables", nl)*)
            end
        | trexp(OpExp({left, oper, right}, nl)) =
            let
                val {exp=expl, ty=tyl} = trexp left
                val {exp=expr, ty=tyr} = trexp right
            in
                if tiposIguales tyl tyr then
                    case oper of
                        PlusOp => if tiposIguales tyl TInt then {exp=binOpIntExp {left=expl, oper=oper, right=expr},ty=TInt} else error("Error de tipos", nl)
                        | MinusOp => if tiposIguales tyl TInt then {exp=binOpIntExp {left=expl, oper=oper, right=expr},ty=TInt} else error("Error de tipos", nl)
                        | TimesOp => if tiposIguales tyl TInt then {exp=binOpIntExp {left=expl, oper=oper, right=expr},ty=TInt} else error("Error de tipos", nl)
                        | DivideOp => if tiposIguales tyl TInt then {exp=binOpIntExp {left=expl, oper=oper, right=expr},ty=TInt} else error("Error de tipos", nl)
                        | LtOp => if tiposIguales tyl TInt orelse tiposIguales tyl TString then
                            {exp=if tiposIguales tyl TInt then binOpIntRelExp {left=expl,oper=oper,right=expr} else binOpStrExp {left=expl,oper=oper,right=expr},ty=TInt}
                            else error("Error de tipos", nl)
                        | LeOp => if tiposIguales tyl TInt orelse tiposIguales tyl TString then
                            {exp=if tiposIguales tyl TInt then binOpIntRelExp {left=expl,oper=oper,right=expr} else binOpStrExp {left=expl,oper=oper,right=expr},ty=TInt}
                            else error("Error de tipos", nl)
                        | GtOp => if tiposIguales tyl TInt orelse tiposIguales tyl TString then
                            {exp=if tiposIguales tyl TInt then binOpIntRelExp {left=expl,oper=oper,right=expr} else binOpStrExp {left=expl,oper=oper,right=expr},ty=TInt}
                            else error("Error de tipos", nl)
                        | GeOp => if tiposIguales tyl TInt orelse tiposIguales tyl TString then
                            {exp=if tiposIguales tyl TInt then binOpIntRelExp {left=expl,oper=oper,right=expr} else binOpStrExp {left=expl,oper=oper,right=expr},ty=TInt}
                            else error("Error de tipos", nl)
                        | _ => raise Fail "No debería pasar! (3)"
                else error("Error de tipos", nl)
            end
        | trexp(RecordExp({fields, typ}, nl)) =
            let
                (* Traducir cada expresión de fields *)
                val tfields = map (fn (sy,ex) => (sy, trexp ex)) fields
                (* Buscar el tipo *)
                val (tyr, cs) = case tabBusca(typ, tenv) of
                    SOME t => (case t of
                        TRecord (cs, u) => (TRecord (cs, u), cs)
                        | _ => error(typ^" no es de tipo record", nl))
                    | NONE => error("Tipo inexistente ("^typ^")", nl)

                (* Verificar que cada campo esté en orden y tenga una expresión del tipo que corresponde *)
                fun verificar _ [] [] = []
                  | verificar _ (c::cs) [] = error("Faltan campos", nl)
                  | verificar _ [] (c::cs) = error("Sobran campos", nl)
                  | verificar n ((s,t,_)::cs) ((sy,{exp,ty})::ds) =
                        if s<>sy then error("Error de campo", nl)
                        else if tiposIguales ty (!t) then (exp, n)::(verificar (n+1) cs ds)
                             else error("Error de tipo del campo "^s, nl)
                val lf = verificar 0 cs tfields
            in
                {exp=recordExp lf, ty=tyr}
            end
        | trexp(SeqExp(s, nl)) =
          let
              val lexti = map trexp s
              val exprs = map (fn{exp, ty} => exp) lexti
              val {exp, ty=tipo} = hd(rev lexti)
          in
              {exp=seqExp (exprs), ty=tipo}
          end
        (*| trexp(AssignExp({var=SimpleVar s, exp}, nl)) =
            {exp=SCAF, ty=TUnit} (*COMPLETAR*)*)
        | trexp(AssignExp({var, exp}, nl)) =
             let
                val {exp=varexp, ty=vartype} = trvar(var, nl)
                val _ = case vartype of
                    TIntRO => error("trexp::AssingExp - La variable es readonly",nl)
                    | _ => ()
                val {exp=expexp, ty=exptype} = trexp exp
                val _ = if exptype <> TUnit andalso tiposIguales exptype vartype then () else error("trexp::AssignExp - El tipo declarado no coincide con el tipo asignado", nl)
            in
                {exp=assignExp{var=varexp, exp=expexp}, ty=TUnit}
            end
        | trexp(IfExp({test, then', else'=SOME else'}, nl)) =
            let val {exp=testexp, ty=tytest} = trexp test
                val {exp=thenexp, ty=tythen} = trexp then'
                val {exp=elseexp, ty=tyelse} = trexp else'
            in
                if tiposIguales tytest TInt andalso tiposIguales tythen tyelse then
                {exp=if tiposIguales tythen TUnit then ifThenElseExpUnit {test=testexp,then'=thenexp,else'=elseexp} else ifThenElseExp {test=testexp,then'=thenexp,else'=elseexp}, ty=tythen}
                else error("Error de tipos en if" ,nl)
            end
        | trexp(IfExp({test, then', else'=NONE}, nl)) =
            let val {exp=exptest,ty=tytest} = trexp test
                val {exp=expthen,ty=tythen} = trexp then'
            in
                if tiposIguales tytest TInt andalso tythen=TUnit then
                {exp=ifThenExp{test=exptest, then'=expthen}, ty=TUnit}
                else error("Error de tipos en if", nl)
            end
        | trexp(WhileExp({test, body}, nl)) =
            let
                val ttest = trexp test
                val _ = preWhileForExp()
                val tbody = trexp body
                val expwhile = whileExp {test=(#exp ttest), body=(#exp tbody), lev=topLevel()}
                val _ = postWhileForExp()
            in
                if tiposIguales (#ty ttest)   TInt andalso #ty tbody = TUnit then {exp=expwhile, ty=TUnit}
                else if not (tiposIguales (#ty ttest) TInt) then error("Error de tipo en la condición", nl)
                else error("El cuerpo de un while no puede devolver un valor", nl)
            end
        | trexp(ForExp({var, escape, lo, hi, body}, nl)) =
            let
                val {exp=explo, ty=tylo} = trexp lo
                val _ = if tylo = TInt then () else error("trexp::ForExp - lo no es TInt",nl)
                val {exp=exphi, ty=tyhi} = trexp hi
                val _ = if tyhi = TInt then () else error("trexp::ForExp - hi no es TInt",nl)
                val access = allocLocal (topLevel()) (!escape)
                val level = getActualLev()
                val varEntry = {level=level, access=access}
                val _ = preWhileForExp()
                val venv' = tabInserta(var, (VIntro varEntry), venv)
                val var = simpleVar(access, level)
                val {exp=expbody, ty=tybody} = transExp(venv', tenv) body
                val _ = if tybody = TUnit then () else error("trexp::ForExp - El cuerpo de for no es TUnit" ,nl)
                val expfor = forExp{lo=explo, hi=exphi, var=var, body=expbody}
                val _ = postWhileForExp()
            in
                {exp=expfor, ty=TUnit}
            end
        | trexp(LetExp({decs, body}, _)) =
            let
                fun aux (d, (v, t, exps1)) =
                    let
                        val (v', t', exps2) = trdec (v, t) d
                    in
                        (v', t', exps1@exps2)
                    end
                val (venv', tenv', expdecs) = List.foldl aux (venv, tenv, []) decs
                val {exp=expbody,ty=tybody}=transExp (venv', tenv') body
            in
                {exp=seqExp(expdecs@[expbody]), ty=tybody}
            end
        | trexp(BreakExp nl) =
            {exp=breakExp(), ty=TUnit} (*COMPLETAR*)
        | trexp(ArrayExp({typ, size, init}, nl)) =
            let
                val {exp=sizeexp,ty=sizetype} = trexp size
                val {exp=initexp,ty=inittype} = trexp init
                val (ta,ur) = (case tabBusca(typ, tenv) of
                                SOME t => (case t of
                                            TArray (ta',ur') => (ta',ur')
                                            | _ => error("trexp::ArrayExp - El tipo "^typ^" no es un arreglo", nl))
                                | _ => error("trexp::ArrayExp - Tipo "^typ^" no definido", nl))
                val _ = if tiposIguales (!ta) inittype then () else error("trexp::ArrayExp - El tipo de la expresion inicializadora "^pt(inittype)^"no coincide con el tipo declarado "^typ, nl)
            in
                print "Pase por ArrayExp!!\n";
                {exp=arrayExp{size=sizeexp, init=initexp}, ty=TArray (ta, ur)}
            end
        and trvar(SimpleVar s, nl) =
            let
                val (access, level, typ) =
                    case tabBusca(s, venv) of
                        SOME (VIntro{access, level}) => (access, level, TInt)
                        | SOME (Var{ty, access, level}) => (access, level, ty)
                        | _ => error("Variable "^s^" no definida en el scope", nl)
            in
                {exp=simpleVar(access, level), ty=typ}
            end
          | trvar(FieldVar(v, s), nl) =
                    let
                        val {exp=varexp, ty=vartype} = trvar(v, nl)
                        val (vtype, vindex)  = case vartype of
                                        TRecord (ls, _) =>
                                        (case List.filter (fn x => #1x = s) ls of
                                             [] => error("trvar: El nombre de la variable no existe en este record "^s, nl)
                                           | (x::_) => (#2x, #3x))
                                      | _ => (pt(vartype) ; error("trvar: No se puede indexar por que no es Record", nl))
                    in
                        {exp=fieldVar(varexp, vindex), ty=(!vtype)}
                    end
          | trvar(SubscriptVar(v, e), nl) =
                    (* v es el arreglo - e es el indice *)
                    let
                        val {exp=expexp, ty=exptype} = trexp(e)
                        val {exp=varexp, ty=vartype} = trvar(v, nl)
                        val _ = if tiposIguales exptype (TInt) then () else error("trvar::SubscriptVar El indice debe ser entero pero es "^pt(exptype), nl)
                    in
                        case vartype of
                            TArray (ty, _) => {exp=subscriptVar(varexp, expexp), ty=(!ty)}
                          | _ => error("trvar: Indexando algo que no es un arreglo", nl)
                    end
        and trdec (venv, tenv) (VarDec ({name,escape,typ=NONE,init},nl)) =
            let
                val {exp=expinit, ty=tyinit} = transExp (venv, tenv) init
                val _ = case tyinit of
                            TNil => error("Variable "^name^" inicializada en nil sin tipar.",nl)  (* var a := nil, tiene que dar error, test45.tig *)
                           |_ => ()
                val level = getActualLev()
                val acc = allocLocal (topLevel()) (!escape)
                val venv' = tabInserta(name, (Var{ty=tyinit, access=acc, level=level}), venv)
                val ci = varDec acc
            in
                print "Pase por trdec::VarDec1!!\n";
                (venv', tenv, [assignExp{var=ci, exp=expinit}])
            end
        | trdec (venv,tenv) (VarDec ({name,escape,typ=SOME s,init},pos)) =
            let
                val {exp=expinit, ty=tyinit} = transExp (venv, tenv) init
                val tyv = case tabBusca(s, tenv) of
                              SOME t' => t'
                              | NONE => error("trdec: Tipo indefinido "^s^" en variable "^name , pos)
                val _ = if tiposIguales tyinit tyv then () else error("trdec::VarDec El valor de la variable "^name^" no coincide con su tipo "^pt(tyv), pos)
                val level = getActualLev()
                val acc = allocLocal (topLevel()) (!escape)
                val venv' = tabRInserta(name, (Var{ty=tyv, access=acc, level=level}), venv)
                val ci = varDec acc
            in
                print "Pase por trdec::VarDec2!!\n";
                (venv', tenv, [assignExp{var=ci, exp=expinit}])
            end
        | trdec (venv,tenv) (FunctionDec fs) =
            let (* Buscar si hay nombres repetidos. Recordar que no se pueden sobreescribir funciones dentro de un mismo batch *)
                fun reps [] = false
                    | reps (({name,...},nl) :: t) = if List.exists(fn ({name = x,...},_) => x = name) t then true else reps t
                val _ = if reps fs then raise Fail ("trdec: Nombres repetidos\n") else ()

                (* Mapea todos los ty de los parametros a sus Tipos. *)
                (* [field] -> [Tipos] *)
                fun tyToTipo [] = []
                    | tyToTipo ({typ=NameTy s, ... } :: ss) =
                        (case tabBusca(s, tenv) of
                            SOME t => (t :: tyToTipo ss)
                            | _ => raise Fail ("trdec: el tipo "^s^" es inexistente\n"))
                    | tyToTipo _ = raise Fail ("trdec: esto no deberia pasar!\n") (* no puede pasar ya que la sintaxis de tiger no permite que los argumentos tengan explicitamente tipo record o array. Para ello hay que definir una etiqueta *)

                (* Chequea que todos los tipos de las funciones existan y crea los niveles e inserta las funciones en venv *)
                fun aux venv' [] = venv'
                    | aux venv' (({name, params, result, ...}, nl)::fss) =
                      let
                          val resultType = case result of
                                            NONE => TUnit
                                            | SOME t => case tabBusca(t, tenv) of
                                                            NONE => error ("trdec: (FunctionDec) (aux): el tipo "^t^" no existe!", nl)
                                                            | SOME t' => t'
                          (* level and Func MUST! have the same LABEL otherwise function calls won't match to the right function*)
                          val lab = if name = "_tigermain" then name else name^"_"^tigertemp.newlabel()^"_"^(Int.toString nl)
                          (* extern=false ya que las funciones externas se definen en runtime *)
                          val lvl = newLevel {parent=topLevel(), name=lab, formals=map (! o #escape) params}
                          val entry = Func {level=lvl, label=lab, formals=tyToTipo params, result=resultType, extern=false}
                          val venv'' = tabRInserta(name, entry, venv')
                      in
                        aux venv'' fss
                      end
                (* *)
                fun addParams venv [] cis = cis
                   | addParams venv (({name, params, body, ...}, nl)::fss) cis =
                     let
                        val tipos = tyToTipo params
                        val nombres = map #name params
                        (* Busca en venv el Tipo del resulto y el nivel. Esta informacion la agregamos en el paso anterior ejecutando aux *)
                        val (tyResult, funcLevel)= case tabBusca(name, venv) of
                                           NONE => error("trdec: Funcion no declarada "^name ,nl)
                                         | SOME (Func{result, level,...}) => (result, level)
                                         | SOME _ => error("trdec: No se puede definir una variable y una funcion con el mismo nombre",nl)

                        (* Para traducir el cuerpo de la función necesitamos actualizar las varaibles de entorno utilizadas por actualLevel y topPila. *)
                        (* Al traducir el cuerpo de la función el contexto debe ser el de la función y no el actual *)
                        (* Pregunta para Guille -> Agrega a la pila la etiqueta vacia? e incrementa la variable de entorno actualLevel*)
                        val _ = preFunctionDec()
                        val _ = pushLevel(funcLevel) (* actualizo pilaLevel para que topLevel() devuelva el nivel de la función *)

                        (* Agrega los parametros de la funcion a venv *)
                        fun addParam [] [] venv = venv
                          | addParam (t::ts) ({name=name, escape=escape,...}::fields) venv =
                            let
                                val acc = allocArg (topLevel()) true (*)(!escape)*)
                                val lvl = getActualLev()
                                val venv' = tabRInserta(name, Var{ty=t, access=acc, level=lvl}, venv)
                            in
                                addParam ts fields venv'
                            end
                          | addParam _ _ _ = error("trdec: La longitud de los nombres y los tipos no coincide",nl)
                        val venv' = addParam tipos params venv
                        val {ty=tyBody, exp=expBody} = transExp (venv', tenv) body
                        (*
                        val _ = ppt tyBody
                        val _ = ppt tyResult
                        *)
                        val _ = if tiposIguales tyBody tyResult then () else error("trdec: Los tipos de retorno de la funcion "^name^" es "^pt(tyResult)^" y el tipo de su cuerpo "^pt(tyBody)^" no coinciden",nl)
                        val isProc = (tyResult = TUnit)
                        val ci = functionDec(expBody, funcLevel, isProc)

                        (* Retornamos al nivel y levelPila original. *)
                        val _ = popLevel()
                        val _ = postFunctionDec()
                     in
                         addParams venv fss ([ci] @ cis)
                     end
                val venv' = aux venv fs
                val cis = addParams venv' fs []
            in
                print "Pase por trdec::FunctionDec!!\n";
                (venv', tenv, cis)
            end
        | trdec (venv,tenv) (TypeDec ts) =
          let
              val sortedNames = Listsort.sort (fn (({name=x,ty=_},_), ({name=y,ty=_},_)) => if x<y then LESS else (if x>y then GREATER else EQUAL)) ts
              val _ = List.foldr (* Chequea que no hay dos seguidos iguales en sortedNames *)
                          (fn (t1 as ({name=n1,ty=_},posx), ({name=n2,ty=_},_)) => if n1=n2 then error("Se definio dos veces el tipo "^n1^" en un mismo batch.", posx) else t1)
                          ({name="",ty=NameTy ""},0) (* Invento un tipo con nombre "" que no va a ser igual a ninguno de los que se definan. *)
                          sortedNames
              val ltsinpos = List.map (fn (x,pos) => x) ts
              val tenv' = tigertopsort.fijaTipos ltsinpos tenv
          in
              print "Pase por trdec::TypeDec!!\n";
              (venv, tenv', [])
          end
    in trexp end
fun transProg ex =
    let
        val main = LetExp({decs=[FunctionDec[({name="_tigermain", params=[],
                                               result=SOME "int", body=ex}, 0)]],
                           body=UnitExp 0}, 0)
        val _ = transExp(tab_vars, tab_tipos) main
    in  print "bien!\n" end
end
