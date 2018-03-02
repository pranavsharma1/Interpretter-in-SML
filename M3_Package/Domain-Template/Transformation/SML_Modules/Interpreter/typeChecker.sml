(* =========================================================================================================== *)
structure TypeChecker =
struct

open Model;
open CONCRETE_REPRESENTATION;

(* =========================================================================================================== *)
(*
    Here is where your typeCheck and typeOf definitions go. The primary challenge here is to translate the parse 
    expression notation we used in M2 to the actual SML tree patterns used in the TL System. See the comments in
    the semantics.sml file for a more detailed discussion on this topic. 
*)


fun typeCheck( itree(inode("program",_), [ stmtList, period ] ), m) = m
  
  |typeCheck( itree(inode("stmtList",_), [ epsilon ] ), m0) = m0
  
  | typeCheck( itree(inode("stmtList",_),
				[
				stmt1,
                                itree(inode(";",_),[]),
				stmtList1
				]
			),
		m0
             )
	=
		let
			val m1	= typeCheck(stmt1, m0)
			val m2	= typeCheck(stmtList1, m1)
		in
			m2
		end 
                
  (*stmt::=assignment*)
  | typeCheck( itree(inode("stmt",_),
				[
				assignment1
				]
			),
		m0
             )
	=
		let
			val m1	= typeCheck(assignment1, m0)
			
		in
			m1
		end 
   
  (*stmt::= declaration*)
  | typeCheck( itree(inode("stmt",_),
				[
				declaration1
				]
			),
		m0
             )
	=
		let
			val m1	= typeCheck(declaration1, m0)
			
		in
			m1
		end 
     
  (*stmt ::= block*)
  | typeCheck( itree(inode("stmt",_),
				[
				block1
				]
			),
		m0
             )
	=
		let
			val m1	= typeCheck(block1, m0)
			
		in
			m1
		end 
  
  (*stmt ::= forBlock*)
  | typeCheck( itree(inode("stmt",_),
				[
				forBlock1
				]
			),
		m0
             )
	=
		let
			val m1	= typeCheck(forBlock1, m0)
			
		in
			m1
		end

  (*stmt ::= whileBlock*)
  | typeCheck( itree(inode("stmt",_),
				[
				whileBlock1
				]
			),
		m0
             )
	=
		let
			val m1	= typeCheck(whileBlock1, m0)
			
		in
			m1
		end

  (*stmt ::= ifBlock*)
  | typeCheck( itree(inode("stmt",_),
				[
				ifBlock1
				]
			),
		m0
             )
	=
		let
			val m1	= typeCheck(ifBlock1, m0)
			
		in
			m1
		end
  (*stmt ::= print need to work on this one*)

  (*Block Statement*)
  (*block::= "{" stmtList"}"*)
  | typeCheck( itree(inode("block",_),
				[
				itree(inode("{",_),[]),
                                stmtList1,
                                itree(inode("}",_),[])
				]
			),
		m0
             )
	=
		let
			val m1	= typeCheck(stmtList1, m0)
			
		in
			m0
		end
                
  (*forBlock	::= "for" "(" id = expr ";" expr ";" id = expr ")" block*)
  | typeCheck( itree(inode("forBlock",_),
				[
				itree(inode("for",_),[]),
                                itree(inode("(",_),[]),
                                id1,
                                itree(inode("=",_),[]),
                                expr1,
                                itree(inode(";",_),[]),
                                expr2
                                itree(inode(";",_),[]),
                                id2,
                                itree(inode("=",_),[]),
                                expr_3,
                                itree(inode(")",_),[]),
                                block1
				]
			),
		m0
             )
	=
		let
			val t1      = getType(accessEnv( id1, m0 ))
                        val t2      = typeOf( expr1, m0 )
                        val t3      = typeOf( expr2, m0 )
                        val t4      = getType(accessEnv( id2, m0 ))
                        val t5      = typeOf( expr_3, m0 )
                        val m1      = typeCheck( block1, m0 )
			
		in
			if t1 = t2 andalso t3 = BOOL andalso t4 = t5 then m1
                        else raise Fail ("Error in For Block")
		end

  (*whileBlock ::= "while" expr do block*)
  | typeCheck( itree(inode("whileBlock",_),
				[
				itree(inode("while",_),[]),
                                expr1,
                                itree(inode("do",_),[]),
                                block1
				]
			),
		m0
             )
	=
		let
			val t1	= typeOf(expr1, m0)
                        val m1  = typeCheck(block1,m0)
			
		in
			if t1 = BOOL then m0
                        else raise Fail ("Error in While Block")
		end

  (*assignment Statement*)
  | typeCheck( itree(inode("assignment",_),
				[
				id1,
                                itree(inode("=",_),[]),
                                expr1
				]
			),
		m0
             )
	=
		let
			val t1	= typeOf(expr1, m0)
                        val t2  = getType(accessEnv(id1,m0))
			
		in
			if t1 = t2 then m0
                        else raise Fail("Error in Assignment Level Statement")
		end

  (*declarattion Statement INT*)
  | typeCheck( itree(inode("declaration",_),
				[
				itree(inode("int",_),[]),
                                id1
				]
			),
		m0
             )
	=
		updateEnv(id1,INT,m0)

  (*declarattion Statement BOOL*)
  | typeCheck( itree(inode("declaration",_),
				[
				itree(inode("bool",_),[]),
                                id1
				]
			),
		m0
             )
	=
		updateEnv(id1, BOOL ,m0)

  (*Conditional Statement 1*)
  | typeCheck( itree(inode("ifBlock",_),
				[
				itree(inode("if",_),[]),
                                expr1,
                                itree(inode("then",_),[]),
                                block1
				]
			),
		m0
             )
	=
		let
			val t1	= typeOf(expr1, m0)
                        val m1  = typeCheck(block1,m0)
			
		in
			if t1 = BOOL then m0
                        else raise Fail("Error in If Then Block")
		end

  (*Conditional Statement 2 *)
  | typeCheck( itree(inode("ifBlock",_),
				[
				itree(inode("if",_),[]),
                                expr1,
                                itree(inode("then",_),[]),
                                block1,
                                itree(inode("else",_),[]),
                                block2
				]
			),
		m0
             )
	=
		let
			val t1	= typeOf(expr1, m0)
                        val m1  = typeCheck(block1,m0)
                        val m2  = typeCheck(block2,m0)
			
		in
			if t1 = BOOL then m0
                        else raise Fail ("Error in If Then Else Block")
		end
   (*increment ::= inc "id*)              
  | typeCheck( itree(inode("increment",_),
				[
				inc,
                                id1
				]
			),
		m0
             )
	=
		let
			val t1	= typeOf(id1, m0)
                        
			
		in
			if t1 = INT then m0
                        else raise Fail ("Error in the Pre Increment/Decremnt Statement")
		end 
 
  | typeCheck( itree(inode("increment",_),
				[
                                id1,
                                inc
				]
			),
		m0
             )
	=
		let
			val t1	= typeOf(id1, m0)
                        
			
		in
			if t1 = INT then m0
                        else raise Fail ("Error in the Post Increment/Decrement Statement")
		end 
  
   
  
  
  | typeCheck( itree(inode(x_root,_), children),_) = raise General.Fail("\n\nIn typeCheck root = " ^ x_root ^ "\n\n")
  | typeCheck _ = raise Fail("Error in Model.typeCheck - this should never occur")





(*expr ::= expr or exprAnd*)
and typeOf( itree(inode("expr",_),
				[
				expr1,
                                itree(inode("||",_),[]),
				exprAnd1
				]
			),
		m0
             )
	=
		let
			val t1	= typeOf(expr1, m0)
			val t2	= typeOf(exprAnd1, m0)
		in
			if t1 = t2 andalso t1 = BOOL then BOOL
                        else raise Fail("Error in expr")
		end 
                
  (*expr ::= exprAnd*)              
  | typeOf( itree(inode("expr",_),
				[
				exprAnd1
				]
			),
		m0
             )
	=
		typeOf(exprAnd1, m0)

  (*exprAnd ::= exprAnd and exprRel*)
  | typeOf( itree(inode("exprAnd",_),
				[
				exprAnd1,
                                itree(inode("&&",_),[]),
				exprRel1
				]
			),
		m0
             )
	=
		let
			val t1	= typeOf(exprAnd1, m0)
			val t2	= typeOf(exprRel1, m0)
		in
			if t1 = t2 andalso t1 = BOOL then BOOL
                        else raise Fail ("Error in exprAnd")
		end

  (*exprAnd ::= exprRel*)              
  | typeOf( itree(inode("exprAnd",_),
				[
				exprRel1
				]
			),
		m0
             )
	=
		typeOf(exprAnd1, m0)

  (*exprRel ::= exprRel rel exprAdd*)(* > *)
  | typeOf( itree(inode("exprRel",_),
				[
				exprRel1,
                                itree(inode(">",_),[]),
				exprAdd1
				]
			),
		m0
             )
	=
		let
			val t1	= typeOf(exprRel1, m0)
			val t2	= typeOf(exprAdd1, m0)
		in
			if t1 = t2 andalso t1 = INT then BOOL
                        else raise Fail ("Error in exprRel '>'")
		end

  (*exprRel ::= exprRel rel exprAdd*)(* >= *)
  | typeOf( itree(inode("exprRel",_),
				[
				exprRel1,
                                itree(inode(">=",_),[]),
				exprAdd1
				]
			),
		m0
             )
	=
		let
			val t1	= typeOf(exprRel1, m0)
			val t2	= typeOf(exprAdd1, m0)
		in
			if t1 = t2 andalso t1 = INT then BOOL
                        else raise Fail ("Error in exprRel ' >= '")
		end

  (*exprRel ::= exprRel rel exprAdd*)(* LT *)
  | typeOf( itree(inode("exprRel",_),
				[
				exprRel1,
                                itree(inode("<",_),[]),
				exprAdd1
				]
			),
		m0
             )
	=
		let
			val t1	= typeOf(exprRel1, m0)
			val t2	= typeOf(exprAdd1, m0)
		in
			if t1 = t2 andalso t1 = INT then BOOL
                        else raise Fail ("Error in exprRel '<'")
		end
  
  (*exprRel ::= exprRel rel exprAdd*)(* LT=  *)
  | typeOf( itree(inode("exprRel",_),
				[
				exprRel1,
                                itree(inode("<=",_),[]),
				exprAdd1
				]
			),
		m0
             )
	=
		let
			val t1	= typeOf(exprRel1, m0)
			val t2	= typeOf(exprAdd1, m0)
		in
			if t1 = t2 andalso t1 = INT then BOOL
                        else raise Fail ("Error in exprRel '<='")
		end

  (*exprRel ::= exprRel rel exprAdd*)(* ==  *)
  | typeOf( itree(inode("exprRel",_),
				[
				exprRel1,
                                itree(inode("==",_),[]),
				exprAdd1
				]
			),
		m0
             )
	=
		let
			val t1	= typeOf(exprRel1, m0)
			val t2	= typeOf(exprAdd1, m0)
		in
			if t1 = t2 andalso t1 <> ERROR then BOOL
                        else raise Fail ("Error in exprRel '=='")
		end

  (*exprRel ::= exprRel rel exprAdd*)(* !=  *)
  | typeOf( itree(inode("exprRel",_),
				[
				exprRel1,
                                itree(inode("!=",_),[]),
				exprAdd1
				]
			),
		m0
             )
	=
		let
			val t1	= typeOf(exprRel1, m0)
			val t2	= typeOf(exprAdd1, m0)
		in
			if (t1 = t2 orelse t1 <> t2)andalso t1 <> ERROR then BOOL
                        else raise Fail ("Error in exprRel '!='")
		end


  (*exprRel ::= exprAdd*)              
  | typeOf( itree(inode("exprRel",_),
				[
				exprAdd1
				]
			),
		m0
             )
	=
		typeOf(exprAdd1, m0)

  (*exprAdd ::= exprAdd Add exprTerm*)(*+*)
  | typeOf( itree(inode("exprAdd",_),
				[
				exprAdd1,
                                itree(inode("+",_),[]),
				exprTerm1
				]
			),
		m0
             )
	=
		let
			val t1	= typeOf(exprAdd1, m0)
			val t2	= typeOf(exprTerm1, m0)
		in
			if t1 = t2 andalso t1 = INT then INT
                        else raise Fail ("Error in exprAdd '+'")
		end

  (*exprAdd ::= exprAdd Add exprTerm*)(*-*)
  | typeOf( itree(inode("exprAdd",_),
				[
				exprAdd1,
                                itree(inode("-",_),[]),
				exprTerm1
				]
			),
		m0
             )
	=
		let
			val t1	= typeOf(exprAdd1, m0)
			val t2	= typeOf(exprTerm1, m0)
		in
			if t1 = t2 andalso t1 = INT then INT
                        else raise Fail ("Error in exprAdd '-'")
		end

  (*exprAdd ::= exprTerm*)              
  | typeOf( itree(inode("exprAdd",_),
				[
				exprTerm1
				]
			),
		m0
             )
	=
		typeOf(exprTerm1, m0)   
                
  (*exprTerm ::= exprTerm mult exprUnary*)(* mult *)
  | typeOf( itree(inode("exprTerm",_),
				[
				exprTerm1,
                                itree(inode("*",_),[]),
				exprUnary1
				]
			),
		m0
             )
	=
		let
			val t1	= typeOf(exprTerm1, m0)
			val t2	= typeOf(exprUnary1, m0)
		in
			if t1 = t2 andalso t1 = INT then INT
                        else raise Fail ("Error in exprTerm '*'")
		end

  (*exprTerm ::= exprTerm mult exprUnary*)(* div *)
  | typeOf( itree(inode("exprTerm",_),
				[
				exprTerm1,
                                itree(inode("/",_),[]),
				exprUnary1
				]
			),
		m0
             )
	=
		let
			val t1	= typeOf(exprTerm1, m0)
			val t2	= typeOf(exprUnary1, m0)
		in
			if t1 = t2 andalso t1 = INT then INT
                        else raise Fail ("Error in exprTerm '/'")
		end
  (*exprTerm ::= exprTerm mult exprUnary*)(* mod *)
  | typeOf( itree(inode("exprTerm",_),
				[
				exprTerm1,
                                itree(inode("%",_),[]),
				exprUnary1
				]
			),
		m0
             )
	=
		let
			val t1	= typeOf(exprTerm1, m0)
			val t2	= typeOf(exprUnary1, m0)
		in
			if t1 = t2 andalso t1 = INT then INT
                        else raise Fail ("Error in exprTerm 'mod'")
		end
                
  (*exprTerm ::= exprUnary*)              
  | typeOf( itree(inode("exprTerm",_),
				[
				exprUnary1
				]
			),
		m0
             )
	=
		typeOf(exprUnary1, m0)

  (*exprUnary ::= neg exprUnary*)
  | typeOf( itree(inode("exprUnary",_),
				[
				
                                itree(inode("~",_),[]),
				exprUnary1
				]
			),
		m0
             )
	=
		let
			val t1	= typeOf(exprUnary1, m0)
		in
			if t1 = INT then INT
                        else raise Fail ("Error in exprUnary 'Unary'")
		end

  (*exprUnary ::= exprExpo*)              
  | typeOf( itree(inode("exprUnary",_),
				[
				exprExpo1
				]
			),
		m0
             )
	=
		typeOf(exprExpo1, m0)

  (*exprExpo ::= exprNot expo exprExpo*)
  | typeOf( itree(inode("exprExpo",_),
				[
				exprNot1
                                itree(inode("^",_),[]),
				exprExpo1
				]
			),
		m0
             )
	=
		let
			val t1	= typeOf(exprNot1, m0)
                        val t2	= typeOf(exprExpo1, m0)
                        
		in
			if t1 = t2 andalso t1 = INT then INT
                        else raise Fail ("Error in exprExpo 'pow'")
		end

  (*exprExpo ::= exprNot*)              
  | typeOf( itree(inode("exprExpo",_),
				[
				exprNot1
				]
			),
		m0
             )
	=
		typeOf(exprNot1, m0)
                
  (*exprNot ::= not exprFactor*)
  | typeOf( itree(inode("exprNot",_),
				[
				
                                itree(inode("!",_),[]),
				exprFactor1
				]
			),
		m0
             )
	=
		let
			val t1	= typeOf(exprFactor1, m0)
                        
		in
			if t1 = BOOL then BOOL
                        else raise Fail ("Error in exprNot ' ! '")
		end             




  (*exprNot ::= exprFactor*)              
  | typeOf( itree(inode("exprNot",_),
				[
				exprFactor1
				]
			),
		m0
             )
	=
		typeOf(exprFactor1, m0)

  (*exprFactor ::= "(" expr ")"*)              
  | typeOf( itree(inode("exprFactor",_),
				[
                                itree(inode("(",_),[]),
				expr1,
                                itree(inode(")",_),[])
				]
			),
		m0
             )
	=
		typeOf(expr1, m0)

  (*exprFactor ::= "integer" *)              
  | typeOf( itree(inode("exprFactor",_),
				[
                                itree(inode("integer",_),[])
				]
			),
		m0
             )
	=
		INT

  (*exprFactor ::= "id" *)              
  | typeOf( itree(inode("exprFactor",_),
				[
                                id1
				]
			),
		m0
             )
	=
		getType(accessEnv(id1,m0))
  
  (*exprFactor ::= increment *)              
  | typeOf( itree(inode("exprFactor",_),
				[
                                increment1
				]
			),
		m0
             )
	=
		typeOf(increment1,m0)
                

  (*exprFactor ::= inc "id" *) (* ++id *)
  | typeOf( itree(inode("exprFactor",_),
				[
				
                                itree(inode("++",_),[]),
				id1
				]
			),
		m0
             )
	=
		let
			val t1	= getType(accessEnv(id1, m0))
                        
		in
			if t1 = INT then INT
                        else raise Fail ("Error in exprFactor '++id'")
		end

  (*increment ::= inc "id" *) (* --id *)
  | typeOf( itree(inode("exprFactor",_),
				[
				
                                inc,
				id1
				]
			),
		m0
             )
	=
		let
			val t1	= getType(accessEnv(id1, m0))
                        
		in
			if t1 = INT then INT
                        else raise Fail ("Error in exprFactor '--id'")
		end

  (*increment ::= "id" inc *) (* id++ *)
  | typeOf( itree(inode("increment",_),
				[
				id1,
                                inc
				
				]
			),
		m0
             )
	=
		let
			val t1	= getType(accessEnv(id1, m0))
                        
		in
			if t1 = INT then INT
                        else raise Fail ("Error in exprFactor 'id++'")
		end
  
  (*exprFactor ::= "id" inc *) (* id-- *)
  | typeOf( itree(inode("increment",_),
				[
				id1,
                                itree(inode("--",_),[])
				
				]
			),
		m0
             )
	=
		let
			val t1	= getType(accessEnv(id1, m0))
                        
		in
			if t1 = INT then INT
                        else raise Fail ("Error in exprFactor 'id--'")
		end


  (*exprFactor ::= "true" *)              
  | typeOf( itree(inode("exprFactor",_),
				[
                                itree(inode("true",_),[])
				]
			),
		m0
             )
	=
		BOOL

  (*exprFactor ::= "false" *)              
  | typeOf( itree(inode("exprFactor",_),
				[
                                itree(inode("false",_),[])
				]
			),
		m0
             )
	=
		BOOL


  (*exprFactor ::= "|" expr "|" *) 
  | typeOf( itree(inode("exprFactor",_),
				[
				
                                itree(inode("|",_),[]),
                                expr1,
                                itree(inode("|",_),[])
				
				]
			),
		m0
             )
	=
		let
			val t1	= typeOf(expr1, m0)
                        
		in
			if t1 = INT then INT
                        else raise Fail("Error in ExprFactor 'abs' ")
		end;
  
  


(* =========================================================================================================== *)  
end (* struct *)
(* =========================================================================================================== *)
















