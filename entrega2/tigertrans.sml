structure tigertrans :> tigertrans = struct

open tigerframe
open tigertree
open tigertemp
open tigerabs

exception breakexc
exception divCero
	
type level = {parent:frame option , frame: frame, level: int}
type access = tigerframe.access

type frag = tigerframe.frag
val fraglist = ref ([]: frag list)

val actualLevel = ref ~1 (* _tigermain debe tener level = 0. *)
fun getActualLev() = !actualLevel

val outermost: level = {parent=NONE,
	frame=newFrame{name="_tigermain", formals=[]}, level=getActualLev()}
fun newLevel{parent={parent, frame, level}, name, formals} =
	{
	parent=SOME frame,
	frame=newFrame{name=name, formals=formals},
	level=level+1}
fun allocArg{parent, frame, level} b = tigerframe.allocArg frame b
fun allocLocal{parent, frame, level} b = tigerframe.allocLocal frame b
fun formals{parent, frame, level} = tigerframe.formals frame

datatype exp =
	Ex of tigertree.exp
	| Nx of tigertree.stm
	| Cx of label * label -> tigertree.stm
	| scaf

val SCAF = scaf

fun seq [] = EXP (CONST 0)
	| seq [s] = s
	| seq (x::xs) = SEQ (x, seq xs)

fun unEx (Ex e) = e
	| unEx (Nx s) = ESEQ(s, CONST 0)
	| unEx (Cx cf) =
	let
		val r = newtemp()
		val t = newlabel()
		val f = newlabel()
	in
		ESEQ(seq [MOVE(TEMP r, CONST 1),
			cf (t, f),
			LABEL f,
			MOVE(TEMP r, CONST 0),
			LABEL t],
			TEMP r)
	end

fun unNx (Ex e) = EXP e
	| unNx (Nx s) = s
	| unNx (Cx cf) =
	let
		val t = newlabel()
		val f = newlabel()
	in
		seq [cf(t,f),
			LABEL t,
			LABEL f]
	end

fun unCx (Nx s) = raise Fail ("Error (UnCx(Nx..))")
	| unCx (Cx cf) = cf
	| unCx (Ex (CONST 0)) =
	(fn (t,f) => JUMP(NAME f, [f]))
	| unCx (Ex (CONST _)) =
	(fn (t,f) => JUMP(NAME t, [t]))
	| unCx (Ex e) =
	(fn (t,f) => CJUMP(NE, e, CONST 0, t, f))

fun Ir(e) =
	let	fun aux(Ex e) = tigerit.tree(EXP e)
		| aux(Nx s) = tigerit.tree(s)
		| aux _ = raise Fail "bueno, a completar!"
		fun aux2(PROC{body, frame}) = aux(Nx body)
		| aux2(STRING(l, "")) = l^":\n"
		| aux2(STRING("", s)) = "\t"^s^"\n"
		| aux2(STRING(l, s)) = l^":\t"^s^"\n"
		fun aux3 [] = ""
		| aux3(h::t) = (aux2 h)^(aux3 t)
	in	aux3 e end
fun nombreFrame frame = print(".globl " ^ tigerframe.name frame ^ "\n")

(* While y for necesitan la u'ltima etiqueta para un break *)
local
	val salidas: label option tigerpila.Pila = tigerpila.nuevaPila1 NONE
in
	val pushSalida = tigerpila.pushPila salidas
	fun popSalida() = tigerpila.popPila salidas
	fun topSalida() =
		case tigerpila.topPila salidas of
		SOME l => l
		| NONE => raise Fail "break incorrecto!"			
end

val datosGlobs = ref ([]: frag list)
fun procEntryExit{level: level, body} =
	let	val label = STRING(name(#frame level), "")
		val body' = PROC{frame= #frame level, body=unNx body}
		val final = STRING(";;-------", "")
	in	datosGlobs:=(!datosGlobs@[label, body', final]) end
fun getResult() = !datosGlobs

fun stringLen s =
	let	fun aux[] = 0
		| aux(#"\\":: #"x"::_::_::t) = 1+aux(t)
		| aux(_::t) = 1+aux(t)
	in	aux(explode s) end

fun stringExp(s: string) =
	let	val l = newlabel()
		val len = ".long "^makestring(stringLen s)
		val str = ".string \""^s^"\""
		val _ = datosGlobs:=(!datosGlobs @ [STRING(l, len), STRING("", str)])
	in	Ex(NAME l) end
fun preFunctionDec() =
	(pushSalida(NONE);
	actualLevel := !actualLevel+1)
fun functionDec(e, l, proc) =
	let	val body =
				if proc then unNx e
				else MOVE(TEMP rv, unEx e)
		val body' = procEntryExit1(#frame l, body)
		val () = procEntryExit{body=Nx body', level=l}
	in	Ex(CONST 0) end
fun postFunctionDec() =
	(popSalida(); actualLevel := !actualLevel-1)

fun unitExp() = Ex (CONST 0)

fun nilExp() = Ex (CONST 0)

fun intExp i = Ex (CONST i)

fun simpleVar(acc, nivel) =
    case acc of
        InReg t => Ex (TEMP t)
        | InFrame off =>
            let fun aux 0 = TEMP fp
                | aux n = MEM (BINOP (PLUS, CONST fpPrevLev, aux (n-1)))
            in
                Ex (MEM (BINOP (PLUS, aux(!actualLevel - nivel), CONST off)))
            end

fun varDec(acc) = simpleVar(acc, getActualLev())

fun fieldVar(var, field) =
    (* field es la posicion dentro del record de var *)
    let
        val v = unEx var
        val rv = newtemp()
    in
        (* Muevo la exp a el registro rv, y calculo donde esta el valor del field en el frame *)
        Ex( ESEQ(MOVE(TEMP rv, v),
                 MEM(BINOP(PLUS, TEMP rv,
                                 BINOP(MUL, CONST field, CONST tigerframe.wSz)))))
    end

fun subscriptVar(arr, ind) =
let
	val a = unEx arr
	val i = unEx ind
	val ra = newtemp()
	val ri = newtemp()
in
	Ex( ESEQ(seq[MOVE(TEMP ra, a),
		MOVE(TEMP ri, i),
		EXP(externalCall("_checkindex", [TEMP ra, TEMP ri]))],
		MEM(BINOP(PLUS, TEMP ra,
			BINOP(MUL, TEMP ri, CONST tigerframe.wSz)))))
end

fun recordExp l =
    let val ret = newtemp()
        fun genTemps 0 = []
            | genTemps n = newtemp()::genTemps (n-1)
        val regs = genTemps (length l)
        fun aux ((e, s), t) = (MOVE (TEMP t, unEx e), s, TEMP t)
        val lexps = map aux (ListPair.zip(l, regs))
        val lexps' = map #1 lexps
        val l' = Listsort.sort(fn ((_, m, _), (_, n, _)) => Int.compare(m,n)) lexps
    in Ex ( ESEQ (
            seq
            (
                lexps'
                @
                [EXP (externalCall("_allocRecord", CONST (length l) :: (map #3 l'))), MOVE (TEMP ret, TEMP rv)]
            ),
            TEMP ret))
    end

fun arrayExp{size, init} =
let
	val s = unEx size
	val i = unEx init
in
	Ex (externalCall("allocArray", [s, i]))
end

fun callExp (name,external,isproc,lev:level,ls) = 
     let fun menAMay 0 = TEMP fp
        | menAMay n = MEM (BINOP (PLUS, menAMay(n-1), CONST fpPrevLev))
        val fplev = if (#level lev) = getActualLev()
                    then MEM (BINOP (PLUS, TEMP fp, CONST fpPrevLev))
                    else if (#level lev) > getActualLev()
                         then menAMay (getActualLev() - (#level lev) + 1)
                         else TEMP fp

        fun preparaArgs [] (rt,re) = (rt, re)
        | preparaArgs (h::t) (rt,re) =  (* rt constantes,etc y re expresiones a evaluar *)
            case h of
            Ex(CONST s) => preparaArgs t ((CONST s)::rt, re)
            |Ex(NAME s) => preparaArgs t ((NAME s)::rt, re)
            |Ex(TEMP s) => preparaArgs t ((TEMP s)::rt, re)
            |_ =>
                let
                    val t' = newtemp()
                in preparaArgs t ((TEMP t')::rt, (MOVE(TEMP t', unEx h))::re)
                end

        val (ta, ls') = preparaArgs (ls) ([],[]) (* no hacemos rev, ya que se preparan al reves en preparaArgs *)
        (* extern=true significa que la funcion es de runtime por lo cual no se pasara el fp *)
        val ta' = if extern then ta else fplev::ta
    in
        if isproc (* La funcion no devuelve nada (TUnit) *)
        then Nx (seq (ls'@[EXP(CALL(NAME name, ta'))]))
        else let
                val tmp = newtemp()
             in
                Ex (ESEQ ( seq(ls'@[EXP(CALL(NAME name, ta')), MOVE(TEMP tmp, TEMP rv)]), TEMP tmp))
             end
    end

fun letExp ([], body) = Ex (unEx body)
 |  letExp (inits, body) = Ex (ESEQ(seq inits,unEx body))

fun breakExp() = 
    let val ts = topSalida()
    in Nx(JUMP(NAME ts, [ts])) end

fun seqExp ([]:exp list) = Nx (EXP(CONST 0))
	| seqExp (exps:exp list) =
		let
			fun unx [e] = []
				| unx (s::ss) = (unNx s)::(unx ss)
				| unx[] = []
		in
			case List.last exps of
				Nx s =>
					let val unexps = map unNx exps
					in Nx (seq unexps) end
				| Ex e => Ex (ESEQ(seq(unx exps), e))
				| cond => Ex (ESEQ(seq(unx exps), unEx cond))
		end

fun preWhileForExp() = pushSalida(SOME(newlabel()))

fun postWhileForExp() = (popSalida(); ())

fun whileExp {test: exp, body: exp, lev:level} =
let
	val cf = unCx test
	val expb = unNx body
	val (l1, l2, l3) = (newlabel(), newlabel(), topSalida())
in
	Nx (seq[LABEL l1,
		cf(l2,l3),
		LABEL l2,
		expb,
		JUMP(NAME l1, [l1]),
		LABEL l3])
end

fun forExp {lo, hi, var, body} =
    let val var' = unEx var
        val (l1,l2,sal) = (newlabel(), newlabel(), topSalida())
    in
        Nx (seq (case hi of
            Ex (CONST n) =>
                if n<valOf(Int.maxInt) (* Parche para el caso en que n=maxInt *) 
                then [ MOVE(var',unEx lo),
                       JUMP(NAME l2,[l2]),
                       LABEL l1, unNx body,
                       MOVE(var',BINOP(PLUS,var',CONST 1)),
                       LABEL l2, CJUMP(GT,var',CONST n,sal,l1),
                       LABEL sal ]
                else [ MOVE(var',unEx lo), (* Si n=maxInt entonces debo hacer al menos una iteraciÃ³n y tener como condiciÃ³n de salida que var'=n, ya que nunca va a ser mayor. *)
                       LABEL l2, unNx body, CJUMP(EQ,var',CONST n,sal,l1),
                       LABEL l1, MOVE(var',BINOP(PLUS,var',CONST 1)),
                       JUMP(NAME l2,[l2]),
                       LABEL sal ]
           | _ => 
                let val t = newtemp()
                in [ MOVE(var',unEx lo),
                     MOVE(TEMP t, unEx hi),
                     CJUMP(LE,var',TEMP t,l2,sal),
                     LABEL l2, unNx body,
                     CJUMP(EQ,TEMP t,var',sal,l1), (* Parche para el caso en que hi=maxInt *)
                     LABEL l1, MOVE(var',BINOP(PLUS,var',CONST 1)),
                     JUMP(NAME l2,[l2]),
                     LABEL sal ]
                end ))
    end

fun ifThenExp{test, then'} =
    let
        val (t, f) = (newlabel(), newlabel())
        val test' = unCx test
        val then'' = unNx then'
    in
        Nx (seq [test'(t,f), LABEL t, then'', LABEL f])
    end

fun ifThenElseExp {test,then',else'} =
  let
        val (t, f, final) = (newlabel(), newlabel(), newlabel())
        val temp = newtemp()
        val test' = unCx test
        val then'' = unEx then'
        val else'' = unEx else'
    in
        Ex (ESEQ (seq ([test'(t,f),
                        LABEL t, 
                        MOVE(TEMP temp, then''),
                        JUMP(NAME final, [final]),
                        LABEL f,
                        MOVE(TEMP temp, else''),
                        LABEL final]),
                TEMP temp))
    end

fun ifThenElseExpUnit {test,then',else'} =
    let
        val (t, f, final) = (newlabel(), newlabel(), newlabel())
        val temp = newtemp()
    in
        Nx (seq ([unCx(test) (t,f),
                    LABEL t, unNx(then'),
                    JUMP (NAME final, [final]),
                    LABEL f,
                    unNx(else'),
                    LABEL final]))
    end

fun assignExp{var, exp} =
    let
	    val v = unEx var
	    val vl = unEx exp
    in
	    Nx (MOVE(v,vl))
    end

fun binOpIntExp {left, oper, right} =
    let val l = unEx left
        val r = unEx right
        val oper' = case oper of
                        PlusOp => PLUS
                       |MinusOp => MINUS
                       |TimesOp => MUL
                       |DivideOp => DIV
                       |_ => raise Fail "Unknown operator"
    in 
        Ex(BINOP(oper',l,r))
    end

fun binOpIntRelExp {left,oper,right} =
    let val l = unEx left
        val r = unEx right
        val rta = newtemp()
        val (t,f) = (newlabel(),newlabel())
        val oper' = case oper of
                        EqOp => EQ
                       |NeqOp => NE
                       |LtOp => LT
                       |GtOp => GT
                       |LteOp => LE
                       |GteOp => GE
                       |_ => raise Fail "Unknown operator"
    in
        Ex(ESEQ(seq[MOVE(TEMP rta,CONST 0),
                    CJUMP(oper',l,r,t,f),
                    LABEL t, MOVE(TEMP rta,CONST 1),
                    LABEL f],
                TEMP rta))
    end
             
fun binOpStrExp {left,oper,right} = 
    let
	    val l = unEx left
	    val r = unEx right
	    val (tl,tr,rta) = (newtemp(),newtemp(),newtemp())
        val (t,f) = (newlabel(),newlabel())
        val oper' = case oper of
                        EqOp => EQ
                       |NeqOp => NE
                       |LtOp => LT
                       |GtOp => GT
                       |LteOp => LE
                       |GteOp => GE
                       |_ => raise Fail "Unknown operator"
    in
	    Ex (ESEQ(seq [MOVE(TEMP tl,l),
	                  MOVE(TEMP tr,r),
	                  EXP(externalCall("_stringCompare", [TEMP tl, TEMP tr])),
                      MOVE(TEMP rta,CONST 0),
	                  CJUMP(oper',TEMP rv,CONST 0,t,f),
                      LABEL t, MOVE(TEMP rta,CONST 1),
                      LABEL f],
	             TEMP rta))
    end
 
end

fun genSL 0 = []
    | genSL n =
        let val tmp = newtemp()
            fun aux 0 = []
                | aux n = MOVE(TEMP tmp, MEM(OPER(TEMP tmp, CONST(2*tigerframe.wSz)))) :: aux(n-1)
        in
            MOVE(tmp, MEM(OPER(PLUS(TEMP tigerframe.fp, CONST(2*tigerframe.wSz))))) :: aux n
        end

