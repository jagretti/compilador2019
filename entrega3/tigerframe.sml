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

type frame = {
	name: string,
	formals: bool list,
	locals: bool list,
	actualLocal: int ref
}
type register = string

datatype access = InFrame of int | InReg of tigertemp.label
datatype frag = PROC of {body: tigertree.stm, frame: frame}
	| STRING of tigertemp.label * string

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
val callersaves = [rv, cx, ov]
val calleesaves = [bx, di, si]

val localsInicial = 0			(* words *)
val localsGap = ~4 			(* bytes *)
val specialregs = [rv, fp, sp]
val argregs = []

fun newFrame{name, formals} = {
	name=name,
	formals=formals,
	locals=[],
	actualLocal=ref localsInicial
}
fun name(f: frame) = #name f
fun formals({formals=f, ...}: frame) = [] (* COMPLETAR *)
fun allocLocal (f: frame) b =
	case b of
	  true =>
		let
			val ret = InFrame(!(#actualLocal f)*wSz+localsGap)
			val _ = #actualLocal f:=(!(#actualLocal f)-1)
		in ret end
	| false => InReg(tigertemp.newtemp())
val allocArg = allocLocal

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

fun procEntryExit1 (frame,body) = body

fun procEntryExit2 (f,body) =
    let
        val isMain = (name f) = "_tigermain"
    in case isMain of
        false => (let fun store r =
                    let
                        val newTemp = tigertemp.newtemp()
                    in (tigerassem.MOVE {assem="movl `s0, `d0\n",dst=newTemp,src=r},newTemp) end
                    val (storeList,tempList) = ListPair.unzip (map store calleesaves)
                    val fetchTemps = ListPair.zip (tempList, calleesaves)
                    fun fetch (t,c) = tigerassem.MOVE {assem="movl `s0, `d0\n",dst=c,src=t}
                    val fetchList = map fetch fetchTemps
                  in storeList@body@fetchList end) 
        | true => body end

fun procEntryExit3(frame, body) =
  let
    val prolog =".globl "^ name frame ^ "\n"
              ^ name frame ^ ":\n"
              ^ "\tpushl %ebp\n"
              ^ "\tmovl %esp, %ebp\n"
              ^ "\tsubl $" ^ Int.toString (abs(!(#actualLocal frame)) * wSz) ^", %esp\n"
    val epilog = "\tleave\n\tret\n\n"
  in
    {prolog = prolog, body = body, epilog = epilog}
  end

end
