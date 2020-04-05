open tigerlex
open tigergrm
open tigerescap
open tigerseman
open tigertrans
open tigerframe
open tigercanon
open tigerinterp
open BasicIO Nonstdio

fun lexstream(is: instream) =
    Lexing.createLexer(fn b => fn n => buff_input is b 0 n);
fun errParsing(lbuf) = (print("Error en parsing!("
    ^(makestring(!num_linea))^
    ")["^(Lexing.getLexeme lbuf)^"]\n"); raise Fail "fin!")
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
        val lexbuf = lexstream entrada
        val expr = prog Tok lexbuf handle _ => errParsing lexbuf
        val _ = findEscape(expr)
        val _ = if arbol then tigerpp.exprAst expr else ()
        val _ = transProg(expr);
        val frags = getResult();
        (*  *)
        fun splitFrags [] pl sl = (rev pl, rev sl)
          | splitFrags ((PROC r)::fs) pl sl = splitFrags fs (r::pl) sl
          | splitFrags ((STRING t)::fs) pl sl = splitFrags fs pl (t::sl)

        val (procList, stringList) = splitFrags frags [] []

        (* functions bodies *)
        val bs = map #body procList
        (* canonize of type tigertree.stm list list *)
        val stmss = map (traceSchedule o basicBlocks o linearize) bs
        (* function frames *)
        val fs = map #frame procList
        (* pair tigertree.stm list to its function frame. *)
        val fracss = ListPair.zip (stmss, fs) (* tigertree.stm list * frame *)

        (* call interpreter *)
        val _ = if interp then inter debug fracss stringList else ()

    in
        print "yes!!\n"
    end     handle Fail s => print("Fail: "^s^"\n")

val _ = main(CommandLine.arguments())
