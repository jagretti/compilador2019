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
            emit(A.OPER{assem = "movl `s0, "^ Int.toString i^"(`s1)",
                        src = [munchExp e2, munchExp e1],
                        dst = [],
                        jump = NONE})
          | munchStm (MOVE(TEMP t1, TEMP t2)) =
            emit(A.MOVE{assem = "movl `s0, `d0",
                        src = [t2],
                        dst = [t1]})
          | munchStm (MOVE(TEMP t, CONST 0)) =
            emit(A.OPER {assem = "xorl `d0, `d0",
                         src = [],
                         dst = [t],
                         jump = NONE})
          | munchStm (MOVE(TEMP t, CONST n)) =
            emit (A.OPER {assem = "movl $" ^ Int.toString n ^", `d0",
                          src = [],
                          dst = [t],
                          jump = NONE})
          | munchStm (MOVE(TEMP t1, MEM (BINOP (PLUS, CONST i, TEMP t2)))) =
            emit (A.OPER {assem = "movl " ^ Int.toString i ^ "(`s0), `d0" ,
                          src = [t2],
                          dst = [t1],
                          jump = NONE})
          | munchStm (MOVE (TEMP t1, MEM (BINOP (PLUS, TEMP t2, CONST i)))) =
            emit (A.OPER {assem = "movl " ^ Int.toString i ^ "(`s0), `d0" ,
                          src = [t2],
                          dst = [t1],
                          jump = NONE})
          | munchStm (MOVE (MEM e1, MEM e2)) =
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
            emit (A.OPER {assem = "movl `s0, "^ Int.toString i,
                          src = [munchExp e],
                          dst = [],
                          jump = NONE})
          | munchStm (MOVE (MEM (BINOP (PLUS, e1, CONST i)), e2)) =
            emit (A.OPER {assem = "movl `s0, "^ Int.toString i^"(`s1)",
                          src = [munchExp e2, munchExp e1],
                          dst = [],
                          jump = NONE})
          | munchStm (MOVE (MEM (BINOP (PLUS, CONST i, e1)), e2)) =
            emit (A.OPER {assem = "movl `s0, "^ Int.toString i^"(`s1)",
                          src = [munchExp e2, munchExp e1],
                          dst = [],
                          jump = NONE})
          | munchStm (MOVE (MEM e1, e2)) =
            emit (A.OPER {assem = "movl `s0, (`s1)",
                          src = [munchExp e2, munchExp e1],
                          dst = [],
                          jump = NONE})
          | munchStm (MOVE (TEMP t, e)) = emit(A.MOVE {assem = "movl `s0, `d0",
                                                       src = munchExp e,
                                                       dst = t})
          | munchStm (MOVE (e1, e2)) = raise Fail "Shouldn't happen (munchStm): MISSING CASES"
          | munchStm (EXP (CALL (NAME f, args))) =
            (munchArgs (List.rev args);
             emit (A.OPER {assem = "call "^f,
                           src = [],
                           dst = callersaves,
                           jump = NONE}))
          | munchStm (EXP (CALL _)) = raise Fail "Shouldn't happen (munchStm CALL _)"
          | munchStm (EXP e) =
            emit (A.MOVE {assem = "movl `s0 `d0",
                          src = munchExp e,
                          dst = tigertemp.newtemp()})
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
            let fun comp oper x y =
                    case oper of
                        EQ => x = y
                      | NE => x <> y
                      | LT => x < y
                      | GT => x > y
                      | LE => x <= y
                      | GE => x >= y
                      | ULT => x < y
                      | ULE => x <= y
                      | UGT => x > y
                      | UGE => x >= y
            in emit (A.OPER {assem = "jmp `j0",
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
                    EQ => emitjmps "je"
                   |NE => emitjmps "jne"
                   |LT => emitjmps "jl"
                   |GT => emitjmps "jg"
                   |LE => emitjmps "jle"
                   |GE => emitjmps "jge"
                   |ULT => emitjmps "jb"
                   |ULE => emitjmps "jbe"
                   |UGT => emitjmps "ja"
                   |UGE => emitjmps "jae"
            end
          | munchStm (LABEL lb) =
            emit (A.LABEL {assem = lb^":",
                           lab = lb})

        and munchExp (MEM (BINOP (PLUS, e1, CONST i))) =
            result (fn r => emit (tigerassem.OPER {assem = "movl "^ Int.toString i ^"(`s0), `d0",
                                                   src = [munchExp e1],
                                                   dst = [r],
                                                   jump = NONE}))
          | munchExp (MEM (BINOP (PLUS, CONST i, e1))) =
            result (fn r => emit (tigerassem.OPER {assem = "movl "^ Int.toString i ^"(`s0), `d0",
                                                   src = [munchExp e1],
                                                   dst = [r],
                                                   jump = NONE}))
          | munchExp (MEM (CONST i)) =
            result (fn r => emit (OPER {assem = "movl "^ Int.toString i ^", `d0",
                                        src = [],
                                        dst = [r],
                                        jump = NONE}))
          | munchExp (MEM e) =
            result (fn r => emit (tigerassem.OPER {assem = "movl (`s0), `d0",
                                                   src = [munchExp e],
                                                   dst = [r],
                                                   jump = NONE}))
          | munchExp (BINOP (PLUS, e1, CONST i)) =>
            (*let val r = munchExp e1
        in  (emit (tigerassem.OPER {assem = "addl $" ^ Int.toString i ^ ", `d0",
                  src = [r],
                  dst = [r],
                  jump = NONE}) ; r)
        end*)
            result (fn r => (emit (OPER {assem = "movl $"^ Int.toString i ^", `d0",
                                         src = [],
                                         dst = [r],
                                         jump = NONE});
                             emit (tigerassem.OPER {assem = "addl `s0, `d0",
                                                    src = [munchExp e1, r],
                                                    dst = [r],
                                                    jump = NONE})))
          | munchExp (BINOP (PLUS, CONST i, e1)) =>
            (*let val r = munchExp e1
         in  (emit (tigerassem.OPER {assem = "addl $" ^ Int.toString i ^ ", `d0",
                   src = [r],
                   dst = [r],
                   jump = NONE}) ; r)
         end*)
            result (fn r => (emit (OPER {assem = "movl $"^ Int.toString i ^", `d0",
                                         src = [],
                                         dst = [r],
                                         jump = NONE});
                             emit (tigerassem.OPER {assem = "addl `s0, `d0",
                                                    src = [munchExp e1, r],
                                                    dst = [r],
                                                    jump = NONE})))
          | munchExp  (BINOP (oper, e1, e2)) =>
            let fun emitOp instr =  result (fn r => (emit (tigerassem.MOVE {assem = "movl `s0, `d0",
                                                                            src = munchExp e1,
                                                                            dst = r});
                                                     emit (tigerassem.OPER {assem = instr^" `s0, `d0",
                                                                            src = [munchExp e2, r],
                                                                            dst = [r],
                                                                            jump = NONE})))
                fun emitDiv () = result (fn r => (emit (tigerassem.OPER {assem = "xorl `d0, `d0",
                                                                         src = [],
                                                                         dst = [ov],
                                                                         jump = NONE});
                                                  emit (tigerassem.MOVE {assem = "movl `s0, `d0",
                                                                         src = munchExp e1,
                                                                         dst = rv});
                                                  emit (tigerassem.MOVE {assem = "movl `s0, `d0",
                                                                         src = munchExp e2,
                                                                         dst = r});
                                                  emit (tigerassem.OPER {assem = "idivl `s0",
                                                                         src = [r, rv, ov],
                                                                         dst = [ov, rv],
                                                                         jump = NONE});
                                                  emit (tigerassem.MOVE {assem = "movl `s0, `d0",
                                                                         src = rv,
                                                                         dst = r})))
            in case oper of
                   PLUS => emitOp "addl"
                  |MINUS => emitOp "subl"
                  |MUL => emitOp "imull"
                  |DIV => emitDiv()
                  |AND => emitOp "andl"
                  |OR => emitOp "orl"
                  |XOR => emitOp "xorl"
                  | _ => raise Fail "Shouldn't happen (munchExp)"
            end

          | munchExp (CONST 0) =>
            result (fn r => emit (OPER {assem = "xorl `d0, `d0",
                                        src = [],
                                        dst = [r],
                                        jump = NONE}))
          | munchExp (CONST i) =>
            result (fn r => emit (OPER {assem = "movl $" ^ Int.toString i ^", `d0",
                                        src = [],
                                        dst = [r],
                                        jump = NONE}))
          | munchExp (NAME s) =>
            result (fn r => emit (OPER {assem = "movl $" ^ s ^", `d0",
                                        src = [],
                                        dst = [r],
                                        jump = NONE}))
          | muchExp (TEMP t) => t
          | _ => raise Fail "Shouldn't happen (munchExp (Call))"


        and munchArgs params =
            let fun munchArgsSt (CONST i) =
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
                  | munchArgsSt  (MEM (CONST i)) =
                    emit (OPER {assem = "pushl "^ Int.toString i,
                                src = [],
                                dst = [],
                                jump = NONE})
                  | munchArgsSt (MEM (TEMP t)) =
                    emit (OPER {assem = "pushl (`s0)",
                                src = [t],
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
