open tigerlex
open tigergrm
open tigerescap
open tigerseman
open tigertrans
open tigerframe
open tigercanon
open tigerinterp
open tigercodegen
open BasicIO Nonstdio

fun lexstream(is: instream) =
    Lexing.createLexer(fn b => fn n => buff_input is b 0 n);
fun errParsing(lbuf) = (print("Error en parsing!("
    ^(makestring(!num_linea))^
    ")["^(Lexing.getLexeme lbuf)^"]\n"); raise Fail "fin!")

(* apply tigercodegen.codegen *)
fun applyCodegen (f : tigerframe.frame, stm : tigertree.stm) : tigerassem.instr list = tigercodegen.codegen f stm
(* apply tigercodegen.codegen to each tigertree.stm *)
fun generateCode (f : tigerframe.frame, stms : tigertree.stm list) : tigerassem.instr list = List.concat (map (fn stm => applyCodegen(f, stm)) stms)

(* apply tigersimpleregalloc.simpleregalloc *)
fun applySimpleRegAlloc (f : tigerframe.frame, instrs : tigerassem.instr list) : tigerassem.instr list  = tigersimpleregalloc.simpleregalloc f instrs

(* build assembly file *)
fun generateAssembly (instrs: {prolog: string, body: tigerassem.instr list, epilog: string} list) : unit  =
    let
        (* Create  tigermain.s *)
        val fd = TextIO.openOut "tigermain.s"
        (* Put .data *)
        val _ = TextIO.output (fd, ".data\n") handle e => (TextIO.closeOut fd; raise Fail "failed to create .data")
        (* Put .text *)
        val _ = TextIO.output (fd, ".text\n") handle e => (TextIO.closeOut fd; raise Fail "failed to create .text")
        fun genAss (instr) =
            let
                val _ = TextIO.output (fd, (#prolog instr)) handle e => (TextIO.closeOut fd; raise Fail "failed to create .text")
                (* Put instructions inside .text *)
                val str : string = List.foldr (fn(l, r) => l^"\n"^r) "" (map (fn (i) => tigerassem.format (fn (j) => j) i) (#body instr))
                val _ = TextIO.output (fd, str) handle e => (TextIO.closeOut fd; raise Fail "failed to put instructions inside .text")
                val _ = TextIO.output (fd, (#epilog instr)) handle e => (TextIO.closeOut fd; raise Fail "failed to create .text")
            in
                ()
            end
        val _ = map genAss instrs
        (* Close file *)
        val _ = TextIO.closeOut fd
    in
        ()
    end

fun main(args) =
    let
        fun arg(l, s) = (List.exists (fn x => x=s) l, List.filter (fn x => x<>s) l)
        val (arbol, l1)     = arg(args, "-arbol")
        val (escapes, l2)   = arg(l1, "-escapes")
        val (ir, l3)        = arg(l2, "-ir")
        val (canon, l4)     = arg(l3, "-canon")
        val (code, l5)      = arg(l4, "-code")
        val (flow, l6)      = arg(l5, "-flow")
        val (interp, l7)    = arg(l6, "-inter")
        val (debug, l8)     = arg(l7, "-debug")
        val entrada = case l8 of
                      [n] => ((open_in n)
                              handle _ => raise Fail (n^" no existe!"))
                      | [] => std_in
                      | _ => raise Fail "opcio'n dsconocida!"
        (* 1 - Lexer *)
        val lexbuf = lexstream entrada
        val expr = prog Tok lexbuf handle _ => errParsing lexbuf
        (* 2 - Escape *)
        val _ = findEscape(expr)
        val _ = if arbol then tigerpp.exprAst expr else ()

        (* 3 - Semantic analisys - type-checking expression and generation of intermediate code *)
        val _ = transProg(expr);
        val frags : tigerframe.frag list = getResult();

        (* 4 - Canonize function's body *)
        (* split frag list  into  {body, frame} list and (label, string) list *)
        fun splitFrags [] pl sl = (rev pl, rev sl)
          | splitFrags ((PROC r)::fs) pl sl = splitFrags fs (r::pl) sl
          | splitFrags ((STRING t)::fs) pl sl = splitFrags fs pl (t::sl)

        (* split  frags into functions bodys list and (label, string) list because the canonization *)
        (* only applies to function's bodies *)
        val (procList, stringList) = splitFrags frags [] []

        (* function's bodies *)
        val bs = map #body procList
        (* function's frames *)
        val fs = map #frame procList
        (* canonize the function's bodies *)
        val stmss = map (traceSchedule o basicBlocks o linearize) bs
        (* pair tigertree.stm list to its function frame. *)
        val canonProcs : (tigertree.stm list * tigerframe.frame) list = ListPair.zip (stmss, fs)

        (* call interpreter *)
        val _ = if interp then inter debug canonProcs stringList else ()

        (* generateCode        =>  translation to x86 instruction set *)
        (* applySimpleRegAllec =>  select registers *)
        fun generateInstructions(stms, frame) =
            let
                val bodyCode : tigerassem.instr list = generateCode(frame, stms)
                val bodyCode' : tigerassem.instr list = tigerframe.procEntryExit2(frame, bodyCode)
                val bodyCode'' : tigerassem.instr list = applySimpleRegAlloc(frame, bodyCode')
                val bodyCode''' : {prolog: string, body: tigerassem.instr list, epilog: string} = tigerframe.procEntryExit3(frame, bodyCode'')
            in
                bodyCode'''
            end
        val instructions = map (fn(stms, frame) => generateInstructions(stms, frame)) canonProcs
        (*val instructions = List.concat bodiesCode*)
        (*
        fun printInstr (tigerassem.OPER oper) = print (((#assem) oper)^"\n")
          | printInstr (tigerassem.LABEL lab) = print (((#assem) lab)^"\n")
          | printInstr (tigerassem.MOVE move) = print (((#assem) move)^"\n")
        val _ = map (fn (i) => printInstr i) instructions
        *)

        (* assing registers to placeholders (temps) created at codegen *)
        (*val formatedInstructions = map (fn (i) => tigerassem.format (fn (j) => j) i) instructions*)
        (* val _ = map (fn (i) => print (i^"\n")) formatedInstructions *)
        val _ = generateAssembly(instructions)
    in
        print "yes!!\n"
    end     handle Fail s => print("Fail: "^s^"\n")

val _ = main(CommandLine.arguments())
