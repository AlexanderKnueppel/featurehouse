// Automatically generated code.  Edit at your own risk!
// Generated by bali2jak v2002.09.03.



public class ExprStmt extends Statement {

    final public static int ARG_LENGTH = 1 ;
    final public static int TOK_LENGTH = 1 ;

    public AST_Exp getAST_Exp () {
        
        return (AST_Exp) arg [0] ;
    }

    public boolean[] printorder () {
        
        return new boolean[] {false, true} ;
    }

    public ExprStmt setParms (AST_Exp arg0, AstToken tok0) {
        
        arg = new AstNode [ARG_LENGTH] ;
        tok = new AstTokenInterface [TOK_LENGTH] ;
        
        arg [0] = arg0 ;            /* AST_Exp */
        tok [0] = tok0 ;            /* ";" */
        
        InitChildren () ;
        return (ExprStmt) this ;
    }

}