(*
	Frames para el 80386 (sin displays ni registers).

		|    argn    |	fp+4*(n+1)
		|    ...     |
		|    arg2    |	fp+16
		|    arg1    |	fp+12
		|  fp level  |  fp+8
		|  retorno   |	fp+4
		|   fp ant   |	fp
		--------------	fp
		|   local1   |	fp-4
		|   local2   |	fp-8
		|    ...     |
		|   localn   |	fp-4*n
*)

structure tigerframe :> tigerframe = struct
open tigertree

(* The code generator will handle the body of functions or procedures but not *)
(* the entry / exit sequences. Here the entry sequence is the prolog and the *)
(* exit sequence is the prolog. *)
(* The body is the instructions of the function/procedure.*)
type procEntryExit = {
    prolog: string,
    body: tigerassem.instr list,
    epilog: string
}
(*  *)

val rv = "%eax"				(* return value  *)
val ov = "%edx"				(* overflow value (edx en el 386) *)
val fp = "%ebp"				(* frame pointer *)
val sp = "%esp"				(* stack pointer *)
val si = "%esi"
val di = "%edi"
val ip = "%eip"
val bx = "%ebx"
val cx = "%ecx"

val fpPrev = 0				(* offset (bytes) *)
val fpPrevLev = 8			(* offset (bytes) *)
val wSz = 4				(* word size in bytes *)
val log2WSz = 2				(* base two logarithm of word size in bytes *)
val calldefs = [rv]
val callersaves = [rv, cx, ov] (* ax, cx, dx *)
val calleesaves = [bx, di, si] (* the rest of regirsters *)
val argsInicial = 2    (* words *)
val argsOffInicial = 4 (* words *)
val localsInicial = 0			(* words *)
val localsGap = ~4 			(* bytes *)
val specialregs = [rv, fp, sp]
val argsGap = wSz

type frame = {
    name: string,
    formals: bool list,
    locals: bool list,
    actualLocal: int ref,
    actualArg: int ref
}

type register = string
datatype access = InFrame of int | InReg of tigertemp.label
datatype frag = PROC of {body: tigertree.stm, frame: frame}
	| STRING of tigertemp.label * string

fun newFrame{name, formals} = {
    name=name,
    formals=formals,
    locals=[],
    actualLocal=ref localsInicial,
    actualArg=ref argsInicial
}

fun name(f: frame) = #name f

fun formals({formals=f, ...}: frame) =
    let  fun aux(n, []) = []
        | aux(n, h::t) = InFrame(n)::aux(n+argsGap, t)
    in
        aux(argsInicial * wSz, f)
    end

(*
Aloca un argumento, y setea la variable #actualArg apuntando al proximo espacio
El primer argumento es:
fp+12 siendo 12 = (#actualArg * 4) + 4 = 4 * (#actualArg + 1) con #actualArg=2
Y setea #actualArg = 3
*)
fun allocArg (f: frame) b =
    case b of
        true =>
            let val ret = (!(#actualArg f) * wSz) + argsOffInicial
                val _ = #actualArg f := !(#actualArg f)+1
            in
                InFrame ret
            end
        | false => InReg(tigertemp.newtemp())

(*
Aloca una variable local, y setea la variable #actualLocal apuntando al proximo espacio disponible
La primer variable local es:
fp-4 siendo -4 = (#actualLocal * 4) - 4 = (#actualLocal - 1) * 4 siendo #actualLocal=0
Y setea #actualLocal=-1
*)
fun allocLocal (f: frame) b =
    case b of
        true =>
            let val ret =  (!(#actualLocal f) * wSz) + localsGap
                val _ = #actualLocal f:=(!(#actualLocal f)-1);
            in
                InFrame ret
            end
        | false => InReg(tigertemp.newtemp())

fun string(l, s) = l^tigertemp.makeString(s)^"\n"

fun exp(InFrame k) e = MEM(BINOP(PLUS, TEMP(fp), CONST k))
    | exp(InReg l) e = TEMP l

(*fun externalCall(s, l) = CALL(NAME s, l)*)
fun externalCall(s, l) =
    let
        val raux = tigertemp.newtemp()
    in
        (* save the %eax return by CALL in a new TEMP *)
        ESEQ(SEQ(EXP(CALL(NAME s, l)),MOVE(TEMP raux,TEMP rv)),TEMP raux)
    end

fun seq [] = EXP (CONST 0)
    | seq [s] = s
    | seq (x::xs) = SEQ (x, seq xs)

fun procEntryExit1 (frame,body) =
    let
        val inFrames = List.map (fn _ => allocLocal frame true) calleesaves
        val calleesaves' = List.map TEMP calleesaves
        val saveCallee = List.map (fn (f, r) => MOVE (exp f (TEMP fp), r)) (ListPair.zip (inFrames, calleesaves'))
        val restoreCallee = List.map (fn (r, f) => MOVE (r, exp f (TEMP fp))) (ListPair.zip (calleesaves', inFrames))
    in
        seq (saveCallee @ [body] @ restoreCallee)
    end

fun procEntryExit2 (f,body) = body

fun procEntryExit3(frame, body) =
    let
        val prolog =".globl "^ name frame ^ "\n"
                ^ name frame ^ ":\n"
                ^ "\tpushl %ebp\n"
                ^ "\tmovl %esp, %ebp\n"
                ^ "\tsubl $" ^ Int.toString (abs(!(#actualLocal frame)) * wSz) ^", %esp\n"
        val epilog = "\tleave\n\tret\n\n"
        val _ = print("procEntryExit3 :: name="^(name frame)^" actualLocal="^Int.toString (abs(!(#actualLocal frame))) ^"\n")
    in
        {prolog = prolog, body = body, epilog = epilog}
    end

end
