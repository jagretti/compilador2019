open tigerabs
open tigertab
open tigertips

infix -- --- (* resta de listas *)
infix rs ls (* right y left sections *)
fun x ls f = fn y => f(x,y)
fun f rs y = fn x => f(x,y)
fun l -- e = List.filter (op<> rs e) l
fun fst(x,_) = x and snd (_,y) = y
fun lp --- e = List.filter ((op<> rs e) o fst) lp

exception Ciclo

fun printTipo TUnit = print("TUnit\n")
|   printTipo TNil = print("TNil\n")
|   printTipo TInt = print("TInt\n")
|   printTipo TString = print("TString\n")
|   printTipo (TArray (t, u)) = (print("TArray of "); printTipo t)
|   printTipo (TRecord (xs, _)) = (print("TRecord of "); (List.app (fn (s,t,_) => (print(s);print(" ");printTipo(t))) xs))
|   printTipo (TFunc (xs, t)) = (List.map printTipo xs; printTipo t)
|   printTipo (TTipo (s, ref (SOME t))) = (print(s); printTipo t)
|   printTipo (TTipo (s, ref NONE)) = (print(s); print("\n"))

fun printTEnv [] = print("------------------------------------------------------\n")
|   printTEnv ((s,t) :: ee) = (print(s^"->"); printTipo(t);print("\n");printTEnv(ee))

fun topsort P =
    let
        fun candidato P E = List.filter (fn e => List.all ((op<> rs e) o snd) P) E (* trata de encontrar elementos de E que no sean sucesores de algun par en P *)
        fun tsort _ [] Res = rev Res
        | tsort [] St Res = rev (St @ Res)
        | tsort P (St as (h::t)) Res =
            let val x = hd (candidato P St)
                        handle Empty => raise Ciclo (* Si no hay un candidato, existe un Ciclo en las declaraciones de tipo *)
            in tsort (P --- x) (St -- x) (x::Res) end
        fun elementos lt = List.foldr (fn ((x,y),l) => let val l1 = case List.find (op= rs x) l of
                                                                    NONE => x::l
                                                                    | _ => l
                                                           val l2 = case List.find (op= rs y) l1 of
                                                                    NONE => y::l1
                                                                    | _ => l1
                                                       in l2 end) [] lt
(*
        fun elementos [] = []
        |   elementos (p::ls) = let val x = #1 p
                                    val y = #2 p
                                    val ls' = elementos ls
                                    val ls'' = if List.Exist x ls' then ls' else (x::ls')
                                in if List.exist y ls'' then ls'' else (y::ls'') end
*)
    in tsort P (elementos P) [] end

fun buscaRecords lt =
    let fun buscaRecs [] recs = recs
    | buscaRecs ((r as {name,ty=RecordTy _})::t) recs = buscaRecs t (r::recs)
    | buscaRecs (_::t) recs = buscaRecs t recs
    in buscaRecs lt [] end

fun genPares lt =
    let val lrecs = buscaRecords lt
        fun genP [] res = res
        | genP({name,ty=NameTy s}::t) res = genP t ((s,name)::res)
        | genP({name,ty=ArrayTy s}::t) res = genP t ((s,name)::res)
        | genP({name,ty=RecordTy lf}::t) res = genP t res
            (*let fun recorre({typ=NameTy x,...}::tt) = 
                (case List.find((op= rs x) o #name) lrecs of
                    SOME _ => recorre tt
                    | _ => x::recorre tt)
                | recorre (_::tt) = recorre tt
                | recorre [] = []
                val res' = recorre lf
                val res'' = List.map (fn x =>(x,name)) res'
            in genP t (res''@res) end *) 
            
        (* esto fue cambiado debido al siguiente ejemplo, el cual deberia ser valido
        
            let type b = a
            type a = {hd:b, tl:b}
            in 0 end       
            
            
        en todos los campos se usan sinonimos de tipos, los cuales ya van a estar trabajados antes de procesar el record *)
            
    in genP lt [] end

(* cuando procesa es llamada, env==tenv *)
fun procesa [] pares recs env = env
| procesa (sorted as (h::t)) (pares:{name:symbol,ty:ty} list) (recs:{name:symbol, ty:ty} list) env =
    let fun filt h {name, ty = NameTy t} = h = t
        | filt h {name, ty = ArrayTy t} = h = t
        | filt h {name, ty = RecordTy lt} = List.exists ((h ls op=) o #name) lt

        val (ps,ps') = List.partition (filt h) pares
        val ttopt = case List.find ((h ls op=) o #name) recs of
                    SOME _ => TTipo (h, ref NONE)
                    | NONE => (case tabBusca(h,env) of
                                SOME t => t
                                | _ => raise Fail (h^" no existe!!\n"))

        val env' = List.foldr(fn ({name,ty=NameTy q}, e) => tabRInserta(name, ttopt, e)
                              |  ({name,ty=ArrayTy q}, e) => tabRInserta(name, TArray (ttopt, ref ()), e)
                              |  ({name,...},_) => raise Fail ("Error interno 666+2 "^name)) env ps
    in procesa t ps' recs env' end

(* Arrays y record *)
fun procRecords recs env =
    let fun buscaEnv env' t =
        case tabBusca(t, env) of
        SOME (x as (TRecord _)) => TTipo (t, ref (SOME x))
        | SOME t' => t'
        | _ => case tabBusca(t, env') of
                SOME (x as (TRecord _)) => TTipo (t, ref (SOME x))
                | SOME t' => t'
                | _ => case List.find(fn {name, ...} => name = t) recs of
                        SOME {name, ...} => TTipo (name, ref NONE)
                        | _ => raise Fail (t^" *** no existe\n")

        fun procs [] env' = env'
        | procs ({name, ty=RecordTy lf} :: t) env' =
            let val lf' = List.foldl(fn ({name, typ=NameTy t, ...}, l) => (name, buscaEnv env' t) :: l
                                        | ({name, typ=ArrayTy t, ...}, l) => (name, TArray (buscaEnv env' t, ref ())) :: l
                                        | (_, l) => l) [] lf
                val (_, lf'') = List.foldl (fn ((x,y), (n,l)) => (n+1, (x,y,n) :: l)) (0,[]) lf'
                val lf''' = Listsort.sort (fn ((x1, y1, z1), (x2, y2, z2)) => String.compare(x1, x2)) lf'' 
                val env'' = tabRInserta(name, TRecord (lf''', ref()), env')
            in procs t env'' end
        | procs _ _ = raise Fail ("error interno 666\n")
    in procs recs (fromTab env) end

(* busca todos los tipos "imaginarios" (TTipo), con referencia a NONE, y les pone su referencia real.
 Esto sucede debido a que hay tipos que, por ejemplo, utilizan tipos que aun no han sido procesados. *)

fun fijaNONE [] env = env
|   fijaNONE ((name,TTipo(s,ref NONE))::t) env =
        (case tabBusca(s,env) of
            SOME (r as (TRecord _)) => fijaNONE t (tabRInserta(name,TTipo(s,ref(SOME r)),env))
            | _ => raise Fail "error 666+00\n")
|   fijaNONE ((name,TArray(TTipo(s,ref NONE), n))::t) env =
        (case tabBusca (s,env) of
            SOME (r as (TRecord _)) => fijaNONE t (tabRInserta(name,TArray (TTipo (s,ref (SOME r)), n), env))
            | _ => raise Fail "error 666+1\n")
|   fijaNONE ((name, TRecord(lf,n))::t) env =
        let fun busNONE((s, TTipo(t, ref NONE), n), l) = ((s,TTipo(t, ref (SOME(tabSaca (t,env)))), n)::l)
            | busNONE(d,l) = d::l
            val lf' = List.foldr busNONE [] lf
        in fijaNONE t (tabRInserta(name, TRecord(lf',n),env)) end
|   fijaNONE (_::t) env = fijaNONE t env

(*
(* para debugging *)
fun fijaRecords decs env =
    let fun buscaEnv t =
                case tabBusca(t,env) of
                    SOME t' => t'
                    |_ => raise Fail (t^"no existe!!\n")
        fun fija1(name,TTipo(s,ref NONE),n) = (name,TTipo(s,ref (SOME (buscaEnv s))), n)
        | fija1(name,TRecord(lf,u),n) =
            let val (nr,r) = valOf (List.find (fn(_,TRecord(_,u')) => u = u'
                                               | _ => false) decs)
            in (name, TTipo(nr,ref (SOME r)), n) end
        | fija1 x = x
        fun fija(name,TRecord(lf,u)) = (name,TRecord(List.map fija1 lf, u))
        | fija x = x
    in List.map fija decs end
*)
fun fijaTipos batch env =
    let val pares = genPares batch
        val recs = buscaRecords batch
        val ordered = topsort pares
        val env' = procesa ordered batch recs env
        (*val _ = (print("env':\n\n");printTEnv (tabAList env'))*)
        val env'' = procRecords recs env'
        (*val _ = (print("env'':\n\n");printTEnv (tabAList env''))*)
        val env''' = fijaNONE(tabAList env'') env''
    in env''' end
