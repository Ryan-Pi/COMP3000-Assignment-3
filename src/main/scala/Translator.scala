/**
 * FunLang to SEC translator.
 *
 * Copyright 2022, Anthony Sloane, Kym Haines, Macquarie University, All rights reserved.
 */

package funlang

/**
 * Translator from FunLang source programs to SEC target programs.
 */
object Translator {

    import SECTree._
    import FunLangTree._
    import scala.collection.mutable.ListBuffer

    /**
     * Return a frame that represents the SEC instructions for a FunLang program.
     */
    def translate (program : Program) : Frame = {

        // An instruction buffer for accumulating the program instructions
        val programInstrBuffer = new ListBuffer[Instr] ()

        /**
         * Translate the program by translating its expression.
         */
        val expInstrs = translateExpression (program.exp)
        programInstrBuffer.appendAll (expInstrs)
        programInstrBuffer.append (IPrint ())

        // Gather the program's instructions and return them
        programInstrBuffer.result ()

    }

    /**
     * Translate an expression and return a list of the instructions that
     * form the translation.
     */
    def translateExpression (exp : Exp) : Frame = {

        // An instruction buffer for accumulating the expression instructions
        val expInstrBuffer = new ListBuffer[Instr] ()

        /**
         * Generate an instruction by appending it to the instruction buffer.
         */
        def gen (instr : Instr) {
            expInstrBuffer.append (instr)
        }

        /**
         * Generate a sequence of instructions by appending them all to the
         * instruction buffer.
         */
        def genall (frame : Frame) {
            expInstrBuffer.appendAll (frame)
        }

        /**
         * Generate code to make a closure (argName => body).
         */
        def genMkClosure (argName : String, body : Exp) {
            val bodyInstrs = translateExpression (body)
            gen (IClosure (argName, bodyInstrs :+ IPopEnv ()))
        }

        exp match {

        case IdnUse (value) =>
            gen (IVar (value))

        case IntExp (value) =>
            gen (IInt (value))

        case BoolExp (value) =>
            gen (IBool (value))

        case PlusExp (l, r) =>
            genall (translateExpression (l))
            genall (translateExpression (r))
            gen (IAdd ())

        case MinusExp (l, r) =>
            genall (translateExpression (l))
            genall (translateExpression (r))
            gen (ISub ())

        case SlashExp (l, r) =>
            genall (translateExpression (l))
            genall (translateExpression (r))
            gen (IDiv ())

        case StarExp (l, r) =>
            genall (translateExpression (l))
            genall (translateExpression (r))
            gen (IMul ())

        case LessExp (l, r) =>
            genall (translateExpression (l))
            genall (translateExpression (r))
            gen (ILess ())

        case EqualExp (l, r) =>
            genall (translateExpression (l))
            genall (translateExpression (r))
            gen (IEqual ())

        case LamExp (IdnDef (name, _), body) =>
            genMkClosure(name, body)

        case ConsExp (l, r) =>
            genall (translateExpression (l))
            genall (translateExpression (r))
            gen (ICons ())

        case IfExp (cond, stmt, fail) =>
            genall(translateExpression (cond))
            gen(IBranch (translateExpression(stmt), translateExpression(fail)))

        case AppExp (l, r) =>
            l match {
                case IdnUse("head") =>
                    genall(translateExpression (r))
                    gen (IHead ())
                
                case IdnUse("tail") =>
                    genall(translateExpression (r))
                    gen (ITail ())

                case IdnUse("length") =>
                    genall(translateExpression (r))
                    gen (ILength ())

                case _ =>
                    genall(translateExpression(l))
                    genall(translateExpression (r))
                    gen (ICall ())
            }

        case ListExp (exps) =>
            exps.length match {
                case 0 =>
                    gen(INil())

                case _ =>
                    for(a <- exps){
                        genall(translateExpression (a))
                    }
                    gen(INil())
                    for(a <- exps){
                        gen(ICons())
                    }
                    
            }

            case BlockExp (defns, exp) =>
                defns.length match {
                    case 1 =>
                        for(defn <- defns){
                            defn match {
                                case Defn(a,b)  =>
                                    genall(translateExpression(LamExp(a,exp)))
                                    genall(translateExpression(b))
                                    gen(ICall ())
                            }
                        }

                    case _ =>
                        defns.head match {
                            case Defn(a,b) =>
                                genall(translateExpression(LamExp(a, BlockExp(defns.tail, exp))))
                                genall(translateExpression(b))
                                gen(ICall ())
                        }
                }

            case MatchExp (exp, cases) =>
                cases.head match {
                    case (a,b) =>
                        a match {
                            case LiteralPat(d) =>
                                //NOTE: rewrite implementation to be similar to IdentPat
                                //genall(translateExpression(LamExp(IdnDef("x", IntType()), IfExp(EqualExp(IdnUse("x"),d), b, IntExp(999)))))
                                // genall(translateExpression(exp))
                                // gen(ICall ())
                                genall(translateExpression(BlockExp(Vector(Defn(IdnDef("x", IntType()), exp)), IfExp(EqualExp(IdnUse("x"),d), b, IntExp(999)))))

                            case IdentPat(d) =>
                                genall(translateExpression(BlockExp(Vector(Defn(IdnDef("x", IntType()),exp), Defn(IdnDef(d, IntType()), IdnUse("x"))), b)))

                            case AnyPat() =>
                                genall(translateExpression(BlockExp(Vector(Defn(IdnDef("x", IntType()), exp)), b)))
                            case _ =>
                                //println(a) test
                        }
                        
                        
                    
                    }

                    


        // FIXME
        // handle:
        //    IfExp
        //    AppExp - "head" (exp)
        //           - "tail" (exp)
        //           - "length" (exp)
        //           - all other: exp (exp)
        //    ListExp
        //    BlockExp
        //    MatchExp

        case _ =>
            gen (IPrint ())
        }

        // Gather the expression's instructions and return them
        expInstrBuffer.result ()

    }

}
