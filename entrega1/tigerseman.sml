structure tigerseman :> tigerseman =
struct

open tigerabs
open tigersres
open tigertopsort
open tigertrans
open tigerpp


type expty = {exp: exp, ty: Tipo}

type venv = (string, EnvEntry) tigertab.Tabla
type tenv = (string, Tipo) tigertab.Tabla

val tab_tipos : (string, Tipo) Tabla = tabInserList(
    tabNueva(),
    [("int", TInt), ("string", TString)])

val tab_vars : (string, EnvEntry) Tabla = tabInserList(
    tabNueva(),
    [("print", Func{level=mainLevel, label="print",
        formals=[TString], result=TUnit, extern=true}),
    ("flush", Func{level=mainLevel, label="flush",
        formals=[], result=TUnit, extern=true}),
    ("getchar", Func{level=mainLevel, label="getstr",
        formals=[], result=TString, extern=true}),
    ("ord", Func{level=mainLevel, label="ord",
        formals=[TString], result=TInt, extern=true}),
    ("chr", Func{level=mainLevel, label="chr",
        formals=[TInt], result=TString, extern=true}),
    ("size", Func{level=mainLevel, label="size",
        formals=[TString], result=TInt, extern=true}),
    ("substring", Func{level=mainLevel, label="substring",
        formals=[TString, TInt, TInt], result=TString, extern=true}),
    ("concat", Func{level=mainLevel, label="concat",
        formals=[TString, TString], result=TString, extern=true}),
    ("not", Func{level=mainLevel, label="not",
        formals=[TInt], result=TInt, extern=true}),
    ("exit", Func{level=mainLevel, label="exit",
        formals=[TInt], result=TUnit, extern=true})
    ])

fun tiposIguales (TRecord _) TNil = true
  | tiposIguales TNil (TRecord _) = true 
  | tiposIguales (TRecord (_, u1)) (TRecord (_, u2 )) = (u1=u2)
  | tiposIguales (TArray (_, u1)) (TArray (_, u2)) = (u1=u2)
  | tiposIguales a b = (a=b)

fun transExp(venv, tenv) =
    let fun error(s, p) = raise Fail ("Error -- línea "^Int.toString(p)^": "^s^"\n")
        fun trexp(VarExp v) = trvar(v)
        | trexp(UnitExp _) = {exp=SCAF, ty=TUnit}
        | trexp(NilExp _)= {exp=SCAF, ty=TNil}
        | trexp(IntExp(i, _)) = {exp=SCAF, ty=TInt}
        | trexp(StringExp(s, _)) = {exp=SCAF, ty=TString}
        | trexp(CallExp({func, args}, nl)) =
            {exp=SCAF, ty=TUnit} (*COMPLETAR*)
        | trexp(OpExp({left, oper=EqOp, right}, nl)) =
            let
                val {exp=_, ty=tyl} = trexp left
                val {exp=_, ty=tyr} = trexp right
            in
                if tiposIguales tyl tyr andalso not (tyl=TNil andalso tyr=TNil) andalso tyl<>TUnit then {exp=SCAF, ty=TInt}
                    else error("Tipos no comparables", nl)
            end
        | trexp(OpExp({left, oper=NeqOp, right}, nl)) = 
            let
                val {exp=_, ty=tyl} = trexp left
                val {exp=_, ty=tyr} = trexp right
            in
                if tiposIguales tyl tyr andalso not (tyl=TNil andalso tyr=TNil) andalso tyl<>TUnit then {exp=SCAF, ty=TInt}
                    else error("Tipos no comparables", nl)
            end
        | trexp(OpExp({left, oper, right}, nl)) = 
            let
                val {exp=_, ty=tyl} = trexp left
                val {exp=_, ty=tyr} = trexp right
            in
                if tiposIguales tyl tyr then
                    case oper of
                        PlusOp => if tyl=TInt then {exp=SCAF,ty=TInt} else error("Error de tipos", nl)
                        | MinusOp => if tyl=TInt then {exp=SCAF,ty=TInt} else error("Error de tipos", nl)
                        | TimesOp => if tyl=TInt then {exp=SCAF,ty=TInt} else error("Error de tipos", nl)
                        | DivideOp => if tyl=TInt then {exp=SCAF,ty=TInt} else error("Error de tipos", nl)
                        | LtOp => if tyl=TInt orelse tyl=TString then {exp=SCAF,ty=TInt} else error("Error de tipos", nl)
                        | LeOp => if tyl=TInt orelse tyl=TString then {exp=SCAF,ty=TInt} else error("Error de tipos", nl)
                        | GtOp => if tyl=TInt orelse tyl=TString then {exp=SCAF,ty=TInt} else error("Error de tipos", nl)
                        | GeOp => if tyl=TInt orelse tyl=TString then {exp=SCAF,ty=TInt} else error("Error de tipos", nl)
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
                fun verificar [] [] = ()
                  | verificar (c::cs) [] = error("Faltan campos", nl)
                  | verificar [] (c::cs) = error("Sobran campos", nl)
                  | verificar ((s,t,_)::cs) ((sy,{exp,ty})::ds) =
                        if s<>sy then error("Error de campo", nl)
                        else if tiposIguales ty (!t) then verificar cs ds
                             else error("Error de tipo del campo "^s, nl)
                val _ = verificar cs tfields
            in
                {exp=SCAF, ty=tyr}
            end
        | trexp(SeqExp(s, nl)) =
            let    
                val lexti = map trexp s
                val exprs = map (fn{exp, ty} => exp) lexti
                val {exp, ty=tipo} = hd(rev lexti)
            in    
                {exp=SCAF, ty=tipo} 
            end
        | trexp(AssignExp({var=SimpleVar s, exp}, nl)) =
            let 
                val {exp=expexp, ty=exptype} = trexp exp
                val vartype = if tabEsta(s, tenv) then tabSaca(s, tenv) else error("trexp::AssignExp - Tipo sin definir", nl)
                val _ = if not(tiposIguales vartype TIntRO) then error("trexp::AssignExp - Asignacion en variable de solo lectura", nl) else ()
            in
                {exp=SCAF, ty=TUnit}
            end
        | trexp(AssignExp({var, exp}, nl)) = 
            let
                val {exp=varexp, ty=vartype} = trvar(var, nl)
                val {exp=expexp, ty=exptype} = trexp exp
                val _ = if exptype <> TUnit andalso tiposIguales exptype vartype then () else error("trexp::AssignExp - El tipo declarado no coincide con el tipo asignado", nl)
            in
                {exp=SCAF, ty=TUnit}
            end
        | trexp(IfExp({test, then', else'=SOME else'}, nl)) =
            let val {exp=testexp, ty=tytest} = trexp test
                val {exp=thenexp, ty=tythen} = trexp then'
                val {exp=elseexp, ty=tyelse} = trexp else'
            in
                if tytest=TInt andalso tiposIguales tythen tyelse then {exp=SCAF, ty=tythen}
                else error("Error de tipos en if" ,nl)
            end
        | trexp(IfExp({test, then', else'=NONE}, nl)) =
            let val {exp=exptest,ty=tytest} = trexp test
                val {exp=expthen,ty=tythen} = trexp then'
            in
                if tytest=TInt andalso tythen=TUnit then {exp=SCAF, ty=TUnit}
                else error("Error de tipos en if", nl)
            end
        | trexp(WhileExp({test, body}, nl)) =
            let
                val ttest = trexp test
                val tbody = trexp body
            in
                if (#ty ttest) = TInt andalso #ty tbody = TUnit then {exp=SCAF, ty=TUnit}
                else if (#ty ttest) <> TInt then error("Error de tipo en la condición", nl)
                else error("El cuerpo de un while no puede devolver un valor", nl)
            end
        | trexp(ForExp({var, escape, lo, hi, body}, nl)) =
            {exp=SCAF, ty=TUnit} (*COMPLETAR*)
        | trexp(LetExp({decs, body}, _)) =
            let
                val (venv', tenv', _) = List.foldl (fn (d, (v, t, _)) => trdec(v, t) d) (venv, tenv, []) decs
                val {exp=expbody,ty=tybody}=transExp (venv', tenv') body
            in 
                {exp=SCAF, ty=tybody}
            end
        | trexp(BreakExp nl) =
            {exp=SCAF, ty=TUnit} (*COMPLETAR*)
        | trexp(ArrayExp({typ, size, init}, nl)) =
            {exp=SCAF, ty=TUnit} (*COMPLETAR*)
        and trvar(SimpleVar s, nl) = (* Buscamos si esta definida la variable en el scope actual *)
            let
                val vartype = case tabBusca(s, venv) of
                    SOME (Var{ty}) => ty
                    | _ => error("Variable no definida en el scope", nl)
            in
                (* tigerpp.prettyPrintTipo(vartype); *)
                {exp=SCAF, ty=vartype}
            end
        | trvar(FieldVar(v, s), nl) =
            let
                val {exp=varexp, ty=vartype} = trvar(v, nl)
                val vtype = case vartype of
                                TRecord (ls, _) =>
                                    (case List.filter (fn x => #1x = s) ls of
                                        [] => error("trvar: El nombre de la variable no existe en este record "^s, nl)
                                        | (x::_) => #2x)
                                | _ => (tigerpp.prettyPrintTipo(vartype) ; error("trvar: No se puede indexar por que no es Record", nl))
            in
                {exp=SCAF, ty=(!vtype)}
            end
        | trvar(SubscriptVar(v, e), nl) =
            let
                val {exp=expexp, ty=exptype} = trexp(e)
                val {exp=varexp, ty=vartype} = trvar(v, nl)
                val _ = if tiposIguales exptype (TInt) then () else error("trvar: El indice debe ser entero", nl)
            in
                case vartype of
                    TArray (ty, _) => {exp=SCAF, ty=(!ty)}
                    | _ => error("trvar: Indexando algo que no es un arreglo", nl)
            end
        and trdec (venv, tenv) (VarDec ({name,escape,typ=NONE,init},pos)) =
            let
                val {exp=expinit, ty=tyinit} = trexp(init)
                val _ = if tiposIguales tyinit TNil then tyinit else error("trdec: El valor tiene que ser nulo", pos)
                val venv' = tabInserta(name, (Var{ty=tyinit}), venv)
            in
                (venv', tenv, [])
            end
        | trdec (venv,tenv) (VarDec ({name,escape,typ=SOME s,init},pos)) =
            let
                val {exp=expinit, ty=tyinit} = trexp(init)
                val tyv = case tabBusca(s, tenv) of
                              SOME t' => t'
                              | NONE => error("trdec: Tipo indefinido "^s , pos)
                val _ = if tiposIguales tyinit tyv then () else error("trdec: El valor de la variable no coincide con su tipo", pos)
                val venv' = tabInserta(name, (Var{ty=tyv}), venv)
            in
                (venv', tenv, [])
            end
        | trdec (venv,tenv) (FunctionDec fs) =
            let (* Buscar si hay nombres repetidos. Recordar que no se pueden sobreescribir funciones dentro de un mismo batch *)
                fun reps [] = false
                    | reps (({name,...},nl) :: t) = if List.exists(fn ({name = x,...},_) => x = name) t then true else reps t
                val _ = if reps fs then raise Fail ("trdec: Nombres repetidos\n") else ()

                fun tyToTipo [] = []
                    | tyToTipo ({typ=NameTy s, ... } :: ss) =
                        (case tabBusca(s, tenv) of
                            SOME t => (t :: tyToTipo ss)
                            | _ => raise Fail ("trdec: el tipo "^s^" es inexistente\n"))
                    | tyToTipo _ = raise Fail ("trdec: esto no deberia pasar!\n") (* no puede pasar ya que la sintaxis de tiger no permite que los argumentos tengan explicitamente tipo record o array. Para ello hay que definir una etiqueta *)

                fun aux venv' [] = venv'
                    | aux venv' (({name, params, result, ...}, nl)::fss) =
                    let val resultType = case result of
                                            NONE => TUnit
                                            | SOME t => case tabBusca(t, tenv) of
                                                            NONE => error ("trdec: (FunctionDec) (aux): el tipo "^t^" no existe!", nl)
                                                            | SOME t' => t'
                        (* extern=false ya que las funciones externas se definen en runtime *)
                        val entry = Func {level=(), label=tigertemp.newlabel(), formals=tyToTipo params, result=resultType, extern=false}
                        val venv'' = tabRInserta(name, entry, venv')
            in
		        aux venv'' fss
		    end
                fun addParams venv [] = ()
                | addParams venv (({name, params, body, ...}, nl)::fss) =
                    let
                        val tipos = tyToTipo params
                        val nombres = map #name params
                        fun addParam [] [] venv = venv
                        | addParam (n::ns) (t::ts) venv = addParam ns ts (tabRInserta(n,Var{ty=t},venv))
                        | addParam _ _ _ = error("trdec: La longitud de los nombres y los tipos no coincide",nl)
                        val venv' = addParam nombres tipos venv
                        val {ty = tyBody,...} = transExp (venv',tenv) body
                        val tyResult = case tabBusca(name,venv) of
                                            NONE => error("trdec: Funcion no declarada "^name ,nl)
                                            | SOME (Func{result,...}) => result
                                            | SOME _ => error("trdec: No se puede definir una variable y una funcion con el mismo nombre",nl)
                      (* val _ = printTipo tyBody
                        val _ = printTipo tyResult *)
                        val _ = if tiposIguales tyBody tyResult then () else error("trdec: Los tipos de retorno de la funcion "^name^" es "^tigerpp.prettyPrintTipo(tyResult)^" y el tipo de su cuerpo "^tigerpp.prettyPrintTipo(tyBody)^" no coinciden",nl)
                    in
		                addParams venv fss
		            end
                val venv' = aux venv fs
                val _ = addParams venv' fs
	        in
	            (venv', tenv, [])
	        end
        | trdec (venv,tenv) (TypeDec ts) =
            let val sortedNames = Listsort.sort (fn (({name=x,ty=_},_), ({name=y,ty=_},_)) => if x<y then LESS else (if x>y then GREATER else EQUAL)) ts
                val _ = List.foldr (* Chequea que no hay dos seguidos iguales en sortedNames *)
			        (fn (t1 as ({name=n1,ty=_},posx), ({name=n2,ty=_},_)) => if n1=n2 then error("Se definio dos veces el tipo "^n1^" en un mismo batch.", posx) else t1)
			    ({name="",ty=NameTy ""},0) (* Invento un tipo con nombre "" que no va a ser igual a ninguno de los que se definan. *)
			    sortedNames
                val ltsinpos = List.map (fn (x,pos) => x) ts
                val tenv' = tigertopsort.fijaTipos ltsinpos tenv
	        in
	            (venv, tenv', [])
	        end
    in trexp end
fun transProg ex =
    let
        val main = LetExp({decs=[FunctionDec[({name="_tigermain",
					       params=[],
					       result=SOME "int", (* Tiger's main funcion return an int *)
					       body=ex}, 0)]],
                           body=UnitExp 0}, 0)
        val _ = transExp(tab_vars, tab_tipos) main
    in
        print "bien!\n"
    end
end
