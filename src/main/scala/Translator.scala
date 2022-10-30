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
                                    //println(defn)
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
                //NOTE: change exp and cases names, they do not accurately represent what they are
                cases.head match {
                    case (a,b) =>
                        a match {
                            case LiteralPat(d) =>
                                //check this later, there is probably a better way
                                cases.length match {
                                    case 1 =>
                                         genall(translateExpression(BlockExp(Vector(Defn(IdnDef("x", IntType()), exp)), IfExp(EqualExp(IdnUse("x"),d), b, IntExp(999)))))
                                    case _ =>
                                        cases.tail match {
                                            case Vector(h) =>
                                                h match {
                                                    case (o, p) =>
                                                        o match {
                                                            case IdentPat(name) =>
                                                                genall(translateExpression(BlockExp(Vector(Defn(IdnDef("x", IntType()), exp)), IfExp(EqualExp(IdnUse("x"),d), b, BlockExp(Vector(Defn(IdnDef(name, IntType()), IdnUse("x"))), p)))))
                                                                
                                                            case _ =>
                                                                
                                                        }
                                                }
                                        }
                                }
                                
                            case IdentPat(d) =>
                                genall(translateExpression(BlockExp(Vector(Defn(IdnDef("x", IntType()),exp), Defn(IdnDef(d, IntType()), IdnUse("x"))), b)))

                            case AnyPat() =>
                                genall(translateExpression(BlockExp(Vector(Defn(IdnDef("x", IntType()), exp)), b)))
                            
                            //everything below this comment is black magic.
                            case ConsPat(l, r) =>
                                l match {
                                    case LiteralPat(thing) =>
                                       r match {
                                        case AnyPat() =>
                                            genall(translateExpression(BlockExp(Vector(Defn(IdnDef("x", IntType()), b)), IfExp(LessExp(IntExp(0), AppExp(IdnUse("length"), exp)), IfExp(EqualExp(AppExp(IdnUse("head"), exp), thing), IdnUse("x"), IntExp(999)), IntExp(999)))))
                                       //AppExp(IdnUse("length"), exp) length of list, compare to less than 0
                                       //IfExp(EqualExp(exp, r), thing, IntExp(999))
                                       case IdentPat(thing2) =>
                                            //println(thing2)
                                            //genall(translateExpression(BlockExp(Vector(Defn(IdnDef("x", IntType()), b)), IfExp(LessExp(IntExp(0), AppExp(IdnUse("length"), exp)), IfExp(EqualExp(AppExp(IdnUse("head"), exp), thing), IdnUse("x"), IntExp(999)), IntExp(999)))))
                                        case _ =>
                                       }

                                    case IdentPat(thing) =>
                                        r match {
                                            case IdentPat(thing2) =>
                                                b match {
                                                    case ConsExp(left, right) =>
                                                        //println(right)
                                                        right match {
                                                            case ConsExp(le, ri) =>
                                                                //le = the int in g :: 4 :: h

                                                            
                                                            case _ =>

                                                        }
                                                        //genall(translateExpression(b))
                                                    
                                                    case _ =>
                                                }
                                                //genall(translateExpression(BlockExp(Vector(Defn(IdnDef("x", IntType()), b)), IfExp(LessExp(IntExp(0), AppExp(IdnUse("length"), exp)), IfExp(EqualExp(AppExp(IdnUse("head"), exp), thing), IdnUse("x"), IntExp(999)), IntExp(999)))))
                                                //genall(ListExp(Vector(AppExp(IdnUse("head"), exp), ,AppExp(IdnUse("tail"), exp))))
                                            
                                            case AnyPat() =>
                                            
                                             case _ =>

                                        }



                                    case AnyPat() =>
                                        r match {
                                            case LiteralPat(thing) =>


                                            case IdentPat(thing) =>
                                                 //genall(translateExpression(BlockExp(Vector(Defn(IdnDef("x", IntType()), b)), IfExp(LessExp(IntExp(0), AppExp(IdnUse("length"), exp)), IfExp(EqualExp(AppExp(IdnUse("head"), exp), thing), IdnUse("x"), IntExp(999)), IntExp(999)))))

                                            case AnyPat() =>
                                                

                                            case _ =>
                                        }


                                    case _ =>


                                }


                                

                            case ListPat(pats) =>
                                pats.length match {
                                    case 0 =>
                                        genall(translateExpression(BlockExp(Vector(Defn(IdnDef("x", IntType()), b)), IfExp(EqualExp(IntExp(0), AppExp(IdnUse("length"), exp)), b, IntExp(999)))))
                                    
                                    case 1 =>
                                        pats.head match {
                                            case thing => 
                                                thing match {
                                                    case LiteralPat(inside) =>
                                                        genall(translateExpression(BlockExp(Vector(Defn(IdnDef("x", IntType()), b)), IfExp(EqualExp(IntExp(1), AppExp(IdnUse("length"), exp)), IfExp(EqualExp(AppExp(IdnUse("head"), exp), inside), IdnUse("x"), IntExp(999)), IntExp(999)))))

                                                    case IdentPat(inside) =>
                                                        genall(translateExpression(BlockExp(Vector(Defn(IdnDef("x", IntType()), exp)), IfExp(EqualExp(IntExp(1), AppExp(IdnUse("length"), exp)), BlockExp(Vector(Defn(IdnDef(inside, IntType()), AppExp(IdnUse("head"), exp))), b), IntExp(999)))))
                                                        //b = matched operation
                                                        //exp = the idn being matched
                                                        //BlockExp(Vector(Defn(IdnDef(inside, IntType(), b))))
                                                        //if List length is 1
                                                        // take the head
                                                    case AnyPat() =>
                                                        genall(translateExpression(BlockExp(Vector(Defn(IdnDef("x", IntType()), b)), IfExp(EqualExp(IntExp(1), AppExp(IdnUse("length"), exp)), b, IntExp(999)))))
                                                    case _ =>
                                                }
                                                
                                        }
                                        
                                    case 2 => 
                                        pats.head match {
                                            case thing =>
                                                thing match {
                                                    case LiteralPat(inside) =>

                                                    case IdentPat(inside) =>

                                                    case AnyPat() =>
                                                        pats.tail match {
                                                            case Vector(pat) =>
                                                                pat match {
                                                                    case IdentPat(patIn) =>
                                                                        genall(translateExpression(BlockExp(Vector(Defn(IdnDef("x", IntType()), exp)), IfExp(EqualExp(IntExp(2), AppExp(IdnUse("length"), exp)), BlockExp(Vector(Defn(IdnDef(patIn, IntType()), AppExp(IdnUse("tail"), exp))), b), IntExp(999)))))
                                                                    case _ =>
                                                                }
                                                                
                                                        }
                                                        

                                                    case _ =>
                                                }
                                        }

                                    case 3 =>


                                    case _ =>
                                        
                                }
                                
                            case _ =>
                                
                                
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
