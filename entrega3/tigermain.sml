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
fun generateAssembly (instrs: procEntryExit list, strings : (string * string) list) : unit  =
    let
        (* Write to file descriptor "fd" the string "text" if fails close the file and raise "errorMsg" *)
        fun output (fd, text, errorMsg) = TextIO.output (fd, text) handle e => (TextIO.closeOut fd; raise Fail errorMsg)
        (* Format instruction's string if is a label do nothing, otherwise add a tab caracter *)
        fun instrToString (instr) =
            let
                val formated = tigerassem.format (fn (j) => j) instr
            in
                if String.isPrefix "L" formated
                then formated
                else "\t"^formated
            end

        (* Create  tigermain.s *)
        val fd = TextIO.openOut "tigermain.s"
        (* Put .data *)
        val _ = output (fd, ".data\n", "failed to create .data")
        fun printData (label, string)  =
            let
                val str = label^": " ^string^"\n"

            in
                if label = ""
                then output (fd, (string^"\n"), "failed in printData")
                else output (fd, str, "failed in printData")

            end
        val _ =  map printData strings
        (* Put .text *)
        val _ = output (fd, ".text\n", "failed to create .text")
        fun genAss (instr : procEntryExit) =
            let
                val _ = output (fd, (#prolog instr), "failed to create .text")
                (* Put instructions inside .text *)
                val strs : string list = map instrToString (#body instr)
                val str : string = List.foldr (fn(l, r) => l^"\n"^r) "" strs
                val _ = output (fd, str, "failed to put instructions inside .text")
                val _ = output (fd, (#epilog instr), "failed to create .text")
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

        fun generateInstructions(stms, frame) =
            let
                (* generateCode        =>  translation to x86 instruction set *)
                val bodyCode : tigerassem.instr list = generateCode(frame, stms)
                (* applySimpleRegAllec =>  select registers *)
                val bodyCode'' : tigerassem.instr list = applySimpleRegAlloc(frame, bodyCode)
                val bodyCode''' : procEntryExit = tigerframe.procEntryExit3(frame, bodyCode'')
            in
                bodyCode'''
            end
        val instructions = map (fn(stms, frame) => generateInstructions(stms, frame)) canonProcs
        val _ = generateAssembly(instructions, stringList)
    in
        print "yes!!\n"
    end     handle Fail s => print("Fail: "^s^"\n")

val _ = main(CommandLine.arguments())
