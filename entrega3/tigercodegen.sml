structure tigercodegen :> tigercodegen = struct

open tigertemp
open tigerassem
open tigerframe
open tigertree

structure A = tigerassem

fun codegen (frame: tigerframe.frame) (stm:tigertree.stm) : tigerassem.instr list =
    let
        val intToString = Int.toString
        val ilist = ref ([] : tigerassem.instr list)

        fun emit x = ilist := x :: !ilist

        fun result (gen) = let val t = tigertemp.newtemp() in gen t; t end
        (*COMLETAR*)

        fun munchStm (SEQ(a, b)) = (munchStm a, munchStm b)
          | munchStm (MOVE(MEM(BINOP(PLUS, e1, CONST i)), e2)) =
            (* Libro *)
            (* movl s0, i(s1)  =>  mem[s1 + i] = s0 *)
            emit(A.OPER{assem = "movl `s0, "^ Int.toString i^"(`s1)",
                        src = [munchExp e2, munchExp e1],
                        dst = [],
                        jump = NONE})
          | munchStm (MOVE(TEMP t1, TEMP t2)) =
            (* movl s0, d0  =>  d0 = s0 *)
            emit(A.MOVE{assem = "movl `s0, `d0",
                        src = [t2],
                        dst = [t1]})
          | munchStm (MOVE(TEMP t, CONST 0)) =
            (* xorl d0, d0  =>  d0 = 0x0 *)
            emit(A.OPER {assem = "xorl `d0, `d0",
                         src = [],
                         dst = [t],
                         jump = NONE})
          | munchStm (MOVE(TEMP t, CONST n)) =
            (* movl $n, d0  =>  d0 = $n *)
            emit (A.OPER {assem = "movl $" ^ Int.toString n ^", `d0",
                          src = [],
                          dst = [t],
                          jump = NONE})
          | munchStm (MOVE(TEMP t1, MEM (BINOP (PLUS, CONST i, TEMP t2)))) =
            (* movl i(s0), d0  =>  d0 = mem[s0 + i] *)
            emit (A.OPER {assem = "movl " ^ Int.toString i ^ "(`s0), `d0" ,
                          src = [t2],
                          dst = [t1],
                          jump = NONE})
          | munchStm (MOVE (TEMP t1, MEM (BINOP (PLUS, TEMP t2, CONST i)))) =
            (* movl i(s0), d0  =>  d0 = mem[s0 + i] *)
            emit (A.OPER {assem = "movl " ^ Int.toString i ^ "(`s0), `d0" ,
                          src = [t2],
                          dst = [t1],
                          jump = NONE})
          | munchStm (MOVE (MEM e1, MEM e2)) =
            (* Libro *)
            (* movl (s0), t  =>  t = mem[s0] *)
            (* movl t, (s1)  =>  mem[s1] = t *)
            let
                val t = tigertemp.newtemp()
            in
                emit (A.OPER {assem = "movl (`s0), `d0",
                              src = [munchExp e2],
                              dst = [t],
                              jump = NONE});
                emit (A.OPER {assem = "movl `s0, (`s1)",
                              src = [t, munchExp e1],
                              dst = [],
                              jump = NONE})
            end
          | munchStm (MOVE (MEM (CONST i), e)) =
            (* Libro *)
            (* movl s0, i  =>  mem[i] = s0  *)
            emit (A.OPER {assem = "movl `s0, "^ Int.toString i,
                          src = [munchExp e],
                          dst = [],
                          jump = NONE})
          | munchStm (MOVE (MEM (BINOP (PLUS, e1, CONST i)), e2)) =
            (* Libro *)
            (* movl s0, i(s1)  =>  mem[s1 + i] = s0  *)
            emit (A.OPER {assem = "movl `s0, "^ Int.toString i^"(`s1)",
                          src = [munchExp e2, munchExp e1],
                          dst = [],
                          jump = NONE})
          | munchStm (MOVE (MEM (BINOP (PLUS, CONST i, e1)), e2)) =
            (* Libro *)
            (* movl s0, i(s1)  =>  mem[s1 + i] = s0  *)
            emit (A.OPER {assem = "movl `s0, "^ Int.toString i^"(`s1)",
                          src = [munchExp e2, munchExp e1],
                          dst = [],
                          jump = NONE})
          | munchStm (MOVE (MEM e1, e2)) =
            (* Libro *)
            (* movl s0, (s1)  =>  mem[s1] = s0  *)
            emit (A.OPER {assem = "movl `s0, (`s1)",
                          src = [munchExp e2, munchExp e1],
                          dst = [],
                          jump = NONE})
          | munchStm (MOVE (TEMP t, e)) =
            (* Libro *)
            (* movl s0, d0  =>  d0 = s0  *)
            emit(A.MOVE {assem = "movl `s0, `d0",
                         src = [munchExp e],
                         dst = [t]})
          | munchStm (MOVE (e1, e2)) = raise Fail "Shouldn't happen (munchStm): MISSING CASES"
          | munchStm (EXP (CALL (NAME f, args))) =
            (munchArgs (List.rev args);
             emit (A.OPER {assem = "call "^f,
                           src = [],
                           dst = callersaves,
                           jump = NONE}))
          | munchStm (EXP (CALL _)) = raise Fail "Shouldn't happen (munchStm CALL _)"
          | munchStm (EXP e) =
            (* movl s0, d0  =>  d0 = s0  *)
            emit (A.MOVE {assem = "movl `s0 `d0",
                          src = [munchExp e],
                          dst = [tigertemp.newtemp()]})
          | munchStm (JUMP (NAME l, ls)) =
            emit (A.OPER {assem = "jmp `j0",
                          src = [],
                          dst = [],
                          jump = SOME ls})
          | munchStm (JUMP (e, ls)) =
            emit (A.OPER {assem = "jmp `s0",
                          src = [munchExp e],
                          dst = [],
                          jump = SOME ls})
          | munchStm (CJUMP (oper, CONST a, CONST b, l1, l2)) =
            let
                fun comp oper x y =
                    case oper of
                        EQ  => x = y
                      | NE  => x <> y
                      | LT  => x < y
                      | GT  => x > y
                      | LE  => x <= y
                      | GE  => x >= y
                      | ULT => x < y
                      | ULE => x <= y
                      | UGT => x > y
                      | UGE => x >= y
            in
                emit (A.OPER {assem = "jmp `j0",
                             src = [],
                             dst = [],
                             jump = SOME [if (comp oper a b)
                                          then l1 else l2]})
            end
          | munchStm (CJUMP (oper, e1, e2, l1, l2)) =
            let
                val t1 = munchExp e1
                val t2 = munchExp e2
                fun emitjmps j =  emit (A.OPER {assem = j^" `j0",
                                                src = [],
                                                dst = [],
                                                jump = SOME [l1, l2]})
                val _ = emit (A.OPER {assem = "cmpl `s1, `s0",
                                      src = [t1, t2],
                                      dst = [],
                                      jump = NONE})
            in
                case oper of
                    EQ  => emitjmps "je"
                  | NE  => emitjmps "jne"
                  | LT  => emitjmps "jl"
                  | GT  => emitjmps "jg"
                  | LE  => emitjmps "jle"
                  | GE  => emitjmps "jge"
                  | ULT => emitjmps "jb"
                  | ULE => emitjmps "jbe"
                  | UGT => emitjmps "ja"
                  | UGE => emitjmps "jae"
            end
          | munchStm (LABEL lb) =
            emit (A.LABEL {assem = lb^":",
                           lab = lb})

        and munchExp (CONST i) =
            (* movl $i, d0  =>  d0 = $i *)
            result (fn r => emit (OPER {assem = "movl $"^Int.toString(i)^", d0",src=[],dst=[r],jump=NONE}))
         |  munchExp (MEM (BINOP (PLUS, e1, CONST i))) =
            (* Libro *)
            (* movl i(s0), d0  =>  d0 = mem[e1 + i] *)
            result (fn r => emit (A.OPER {assem = "movl "^ Int.toString i ^"(`s0), `d0",
                                                   src = [munchExp e1],
                                                   dst = [r],
                                                   jump = NONE}))
         | munchExp (MEM (BINOP (PLUS, CONST i, e1))) =
           (* Libro *)
           (* movl i(s0), d0  =>  d0 = mem[e1 + i] *)
           result (fn r => emit (A.OPER {assem = "movl "^ Int.toString i ^"(`s0), `d0",
                                                  src = [munchExp e1],
                                                  dst = [r],
                                                  jump = NONE}))
         | munchExp (MEM e) =
           (* Libro *)
           (* movl (s0), d0  =>  d0 = mem[s0] *)
           result (fn r => emit (A.OPER {assem = "movl (`s0), `d0",
                                                  src = [munchExp e],
                                                  dst = [r],
                                                  jump = NONE}))
         | munchExp (BINOP (PLUS, e1, CONST i)) = munchExp (BINOP (PLUS, CONST i, e1))
         | munchExp (BINOP (PLUS, CONST i, e1)) =
           (* Libro *)
           (* movl $i, d0  =>  d0 = $i *)
           (* addl s0, d0  =>  %eax = s0 + d0 *)
           result (fn r => (emit (OPER {assem = "movl $"^ Int.toString i ^", `d0",
                                        src = [],
                                        dst = [r],
                                        jump = NONE});
                            emit (A.OPER {assem = "addl `s0, `d0",
                                                   src = [munchExp e1, r],
                                                   dst = [r],
                                                   jump = NONE})))
         | munchExp (BINOP (oper, e1, e2)) =
           let
               fun emitOp instr =
                   (* molv  s0, d0  =>  r = e1 *)
                   (* instr s0, d0  =>  r = instr(e2, r)  *)
                   result (fn r => (emit (A.MOVE {assem = "movl `s0, `d0",
                                                  src = munchExp e1,
                                                  dst = r});
                                    emit (A.OPER {assem = instr^" `s0, `d0",
                                                  src = [munchExp e2, r],
                                                  dst = [r],
                                                  jump = NONE})))
               fun emitDiv () =
                   (* xorl  d0, d0  =>  ov = 0x0 *)
                   (* movl  s0, d0  =>  rv = e1  *)
                   (* movl  s0, d0  =>  r  = e2  *)
                   (* idivl s0      =>  idivl r  *)
                   (* movl  s0, d0  =>  r  = rv  *)
                   result (fn r => (emit (A.OPER {assem = "xorl `d0, `d0",
                                                  src = [],
                                                  dst = [ov],
                                                  jump = NONE});
                                    emit (A.MOVE {assem = "movl `s0, `d0",
                                                  src = munchExp e1,
                                                  dst = rv});
                                    emit (A.MOVE {assem = "movl `s0, `d0",
                                                  src = munchExp e2,
                                                  dst = r});
                                    emit (A.OPER {assem = "idivl `s0",
                                                  src = [r, rv, ov],
                                                  dst = [ov, rv],
                                                  jump = NONE});
                                    emit (A.MOVE {assem = "movl `s0, `d0",
                                                  src = rv,
                                                  dst = r})))
           in
               case oper of
                   PLUS  => emitOp "addl"
                 | MINUS => emitOp "subl"
                 | MUL   => emitOp "imull"
                 | AND   => emitOp "andl"
                 | OR    => emitOp "orl"
                 | XOR   => emitOp "xorl"
                 | DIV   => emitDiv()
                 | _     => raise Fail "Shouldn't happen (munchExp)"
           end
         | munchExp (NAME s) =
           (* movl $s, d0  =>  d0 = $s *)
           result (fn r => emit (OPER {assem = "movl $" ^ s ^", `d0",
                                       src = [],
                                       dst = [r],
                                       jump = NONE}))
         | munchExp (TEMP t) = t
         | _ => raise Fail "Shouldn't happen (munchExp (_))"


        and munchArgs params =
            let
                fun munchArgsSt (CONST i) =
                    emit (OPER {assem = "pushl $" ^ Int.toString i,
                                src = [],
                                dst = [],
                                jump = NONE})
                  | munchArgsSt (NAME m) =
                    emit (OPER {assem = "pushl $" ^ m,
                                src = [],
                                dst = [],
                                jump = NONE})
                  | munchArgsSt  (TEMP t) =
                    emit (OPER {assem = "pushl `s0",
                                src = [t],
                                dst = [],
                                jump = NONE})
                  | munchArgsSt  (MEM e) =
                    emit (OPER {assem = "pushl (`s0)"
                                src = [munchExp e],
                                dst = [],
                                jump = NONE})
                  | munchArgsSt h =
                    emit (OPER {assem = "pushl `s0",
                                src = [munchExp h],
                                dst = [],
                                jump = NONE})
            in
                List.map munchArgsSt t
            end
    in
        munchArgsSt params
    end
in
    munchStm stm;
    rev(!ilist)
end
