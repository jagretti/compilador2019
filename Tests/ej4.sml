open tigerlex
open tigergrm
open tigerescap
open tigerseman
open tigerabs
open BasicIO Nonstdio

fun maxargs (VarExp(var,_)) = printInVar var
| maxargs (CallExp({func, args},_)) = if func = "print" then Int.max(length args, maxargs args) else maxargs args
| maxargs (OpExp({left, oper, right},_)) = Int.max(maxargs left, maxargs right)
| maxargs (RecordExp({fields,...},_)) = maxargs #2(fields)
| maxargs (SeqExp(exp,_)) = maxargs exp
| maxargs (AssignExp({exp,...},_)) = maxargs exp
| maxargs (IfExp({test, then', else'},_)) = Int.max(Int.max(maxargs test, maxargs then'), maxargs else')
| maxargs (WhileExp({test, body},_)) = Int.max(maxargs test, maxargs body)
| maxargs (ForExp({lo, hi, body,...},_)) = Int.max(Int.max(maxargs lo, maxargs hi), maxargs body)
| maxargs (LetExp({decs,body},_)) = Int.max(maxargs body, printInDec decs)
| maxargs (ArrayExp({size,init,...},_)) = Int.max(maxargs size, maxargs init)
| maxargs _ = 0

fun printInVar (SubscriptVar(var,exp)) = Int.max(printInVar var, maxargs exp)
| printInVar (FieldVar(var,_)) = printInVar var
| printInVar _ = 0

fun printInDec (FunctionDec({body,...},_)) = maxargs body
| printInDec (VarDec({init,...},_)) = maxargs init
| printInDec _ = 0

fun lexstream(is: instream) =
	Lexing.createLexer(fn b => fn n => buff_input is b 0 n);
fun errParsing(lbuf) = (print("Error en parsing!("
	^(makestring(!num_linea))^
	")["^(Lexing.getLexeme lbuf)^"]\n"); raise Fail "fin!")
fun main(args) =
	let	fun arg(l, s) =
			(List.exists (fn x => x=s) l, List.filter (fn x => x<>s) l)
		val (arbol, l1)		= arg(args, "-arbol")
		val (escapes, l2)	= arg(l1, "-escapes") 
		val (ir, l3)		= arg(l2, "-ir") 
		val (canon, l4)		= arg(l3, "-canon") 
		val (code, l5)		= arg(l4, "-code") 
		val (flow, l6)		= arg(l5, "-flow") 
		val (inter, l7)		= arg(l6, "-inter") 
		val entrada =
			case l7 of
			[n] => ((open_in n)
					handle _ => raise Fail (n^" no existe!"))
			| [] => std_in
			| _ => raise Fail "opcio'n dsconocida!"
		val lexbuf = lexstream entrada
		val expr = prog Tok lexbuf handle _ => errParsing lexbuf
		val _ = findEscape(expr)
		val _ = if arbol then tigerpp.exprAst expr else ()
	in
		transProg(expr);
		print "yes!!\n"
	end	handle Fail s => print("Fail: "^s^"\n")

val _ = main(CommandLine.arguments())
