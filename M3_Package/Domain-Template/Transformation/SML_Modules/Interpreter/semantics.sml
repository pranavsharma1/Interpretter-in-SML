(* =========================================================================================================== *)
structure Semantics =
struct


(* This makes contents of the Model structure directly accessible (i.e., the prefix "Model." is not needed. *)            
open Model; 
            
(* This makes the internal representation of parse trees directly accessible. *)            
open CONCRETE_REPRESENTATION;

(* The following tree structure, defined in the CONCERETE_REPRESENTATION structure, is used in the TL System:

    datatype NODE_INFO = info of { id : IntInf.int, line : int * int , column : int * int, label : string };
	datatype INODE = inode of string * NODE_INFO
	                 | ...  
															
	datatype ITREE = itree of INODE * ITREE list;
*)


(* =========================================================================================================== *)
(* Here is where you add the M and E (as well as any other) definitions you developed in M2. The primary challenge here
   is to translate the parse expression notation we used in M2 to the actual SML tree patterns used in the TL System. 
   
   Example:
   
   M1: <stmtList> ::= <stmt> ";" <stmList>
   
   M2: M( [[ stmt_1 ; stmtList_1 ]], m) = M(stmtList_1, M(stmt_1,m))
    
   M4: 
        M( itree(inode("stmtList",_),
                    [
                        stmt,       (* this is a regular variable in SML and has no other special meaning *)
                        semiColon,  (* this is a regular variable in SML and has no other special meaning *)
                        stmtList    (* this is a regular variable in SML and has no other special meaning *) 
                    ]
                ),
           m
           
        ) = M( stmtList, M(stmt, m) )  
        
        
        Note that the above M4 implementation will match ANY tree whose root is "stmtList" having three children.
        Such matches can be further constrained by explicitly exposing more of the tree structure.
        
        M( itree(inode("stmtList",_),
                    [
                        stmt,                       (* this is a regular variable in SML and has no other special meaning *)
                        itree(inode(";",_), [] ),   (* A semi-colon is a leaf node. All leaf nodes have an empty children list. *)
                        
                        stmtList                    (* this is a regular variable in SML and has no other special meaning *) 
                    ]
                ),
           m
           
        ) = M( stmtList, M(stmt, m) )  
        
        Note that the above M4 implementation will match ANY tree satisifying the following constraints:
            (1) the root is "stmtList"
            (2) the root has three children
            (3) the second child is a semi-colon   
*)

fun M(itree(inode("program", _),
        [
          stmtList1
        ]
      ),
      m0
    ) = M(stmtList1,m0)
	
  | M(itree(inode("stmtList", _),
        [
					stmt1,
					itree(inode(";",_),[]),
					stmtList1
				]
			),
		m0
	) = M(stmtList1, M(stmt1, m0))
  
  (* stmt *)
  | M(itree(inode("stmt", _),
        [
          assignment1
        ]
      ),
      m0
    ) = M(assignment1, m0)
  
  | M(itree(inode("stmt", _),
        [
          declaration1
        ]
      ),
      m0
    ) = M(declaration1, m0)
  
  | M(itree(inode("stmt", _),
        [
          block1
        ]
      ),
      m0
    ) = M(block1, m0)
  
  | M(itree(inode("stmt", _),
        [
          forBlock1
        ]
      ),
      m0
    ) = M(forBlock1, m0)
  
  | M(itree(inode("stmt", _),
        [
          whileBlock1
        ]
      ),
      m0
  ) = M(whileBlock1, m0)
  
  | M(itree(inode("stmt", _),
        [
          ifBlock1
        ]
      ),
      m0
    ) = M(ifBlock1, m0)
  
  | M(itree(inode("stmt", _),
        [
          printstmt1
        ]
      ),
      m0
    ) = M(printstmt1, m0)
  
  (* Block *)
  | M(itree(inode("block", _),
				[
					itree(inode("{", _), []),
					stmtList1,
					itree(inode("}", _), [])
				]
			),
		(env0,s0)
	) =  
                let
			  val (env1, s1) = M(stmtList1,(env0,s0))
			  val m2       = (env0,s1)
		  in
			  m2
		  end
                 
  (* assignment *)
  | M(itree(inode("assignment", _),
        [
          id1,
          itree(inode("=", _), []),
          expr1
        ]
      ),
      m0
	) =
                  let
			  val (v1, m1) = E(expr1, m0)
			  val loc      = getLoc(accessEnv(getLeaf(id1), m1))
			  val m2       = updateStore(loc, v1, m1)
		  in
			  m2
		  end
  
  (*assignment goes to increment*)
  | M(itree(inode("assignment", _),
        [
          id1,
          itree(inode("=", _), []),
          increment1
        ]
      ),
      m0
	) =
            M(increment1, m0)		  
		
  (* Declaration integer*)
  | M(itree(inode("declaration", _),
        [
          type1,
          id1
        ]
      ),
      m0
    ) = updateEnv(id1, type1, new(), m0)
   
	
	(* ======== Conditional Statements ======== *)
  (* ifBlock *)
  | M(itree(inode("ifBlock", _),
        [
          itree(inode("if", _), []),
          expr1,
          itree(inode("then", _), []),
          block1
        ]
			),
		  m0
	  ) =
		  let
			  val (v1, m1) = E(expr1, m0)
		  in
			  if v1 then M(block1,m0)
			  else m1
		  end
      
  | M(itree(inode("ifBlock", _),
				[
					itree(inode("if", _), []),
					expr1,
					itree(inode("then", _), []),
					block1,
					itree(inode("else", _), []),
					block2
				]
			),
		  m0
	  ) =
		  let
			  val (v1, m1) 	= E(expr1, m0)
		  in
		  	if v1 then M(block1, m1)
		  	else M(block2, m1)
		  end
	
	
	(* ======== Looping Structures ======== *)
  (* For loop *)
  | M(itree(inode("forBlock",_),
				[
					itree(inode("for", _), []),
					itree(inode("(", _), []),
					id1,
					itree(inode("=", _), []),
					expr1,
					itree(inode(";", _), []),
					expr2,
					itree(inode(";", _), []),
					id2,
					itree(inode("=", _), []),
					expr3,
					itree(inode(")", _), []),
					block1
				]
			),
		  m0
	  ) =
		  let
			  val (v1, m1) = E(expr1, m0)
			  val  loc     = getLoc(id1, m1)
			  val  m2      = updateStore(loc, v1, m1)
			  val (v2, m3) = E(expr2, m2)
		  in
		  	  if v2 then N(expr2, id2, expr3, block1, m3)
			  else m3
		  end
    
 
		
	  (* While Loop *)
  | M(itree(inode("whileBlock", _),
				[
					itree(inode("while", _), []),
					expr1,
                                        itree(inode("do", _), []),
					block1
				]
			),
		  m0
	  ) = P (expr1, block1, m0)


  (* ======== End Looping Structure ======== *)
 
 
  | M(itree(inode("increment", _),
        [
          itree(inode("++", _), []),
          id1
        ]
			),
		  m0
	  ) =
		  let
			  val loc = getLoc(accessEnv(getLeaf(id1),m0))
                          val v0  = accessStore(loc,m0)
                          val m1  = updateStore(loc, v0 + 1, m0)
		  in
			  m1
		  end
  
  | M(itree(inode("increment", _),
        [
          itree(inode("--", _), []),
          id1
        ]
			),
		  m0
	  ) =
		  let
			  val loc = getLoc(accessEnv(getLeaf(id1),m0))
                          val v0  = accessStore(loc,m0)
                          val m1  = updateStore(loc, v0 - 1, m0)
		  in
			  m1
		  end
  
  | M(itree(inode("increment", _),
        [
          id1,
          itree(inode("++", _), [])
          
        ]
			),
		  m0
	  ) =
		  let
			  val loc = getLoc(accessEnv(getLeaf(id1),m0))
                          val v0  = accessStore(loc,m0)
                          val m1  = updateStore(loc, v0 + 1, m0)
		  in
			  m1
		  end
   
  | M(itree(inode("increment", _),
        [
          id1,
          itree(inode("--", _), [])
          
        ]
			),
		  m0
	  ) =
		  let
			  val loc = getLoc(accessEnv(getLeaf(id1),m0))
                          val v0  = accessStore(loc,m0)
                          val m1  = updateStore(loc, v0 - 1, m0)
		  in
			  m1
		  end
  (* ======== End  Statement Level Increment Statements ======== *)


| M(	itree(inode("printstmt", _),
				[
					itree(inode("print", _), []),
					itree(inode("(", _), []),
					expr1,
					itree(inode(")", _), [])
				]
			),
		  m0
	  ) =
		  let
			  val (v1, m1)	= E(expr1, m0)
			  val _         = print(Bool.toString(v1))
		  in
			  m1
		  end


        
  | M(itree(inode(x_root,_), children),_) =
      raise General.Fail("\n\nIn M root = " ^ x_root ^ "\n\n")
  
  | M _ = raise Fail("Error in Semantics.M - this should never occur.")
  
  (* ======== Expressions ======== *)
	(* expr *)
  and  E(itree(inode("expr", _),
				[
					expr1,
					itree(inode("||", _), []),
					exprAnd1
				]
			),
		  m0
    ) =
		  let
			  val (v1, m1) = E(expr1, m0)
			 
		  in
			  if v1 then (v1,m1)
                          else 
                                let
                                     val(v2,m2) = E(exprAnd1, m1)
                                
                                in
                                     (v2,m2)
                                end
                           
                           (v1 orelse v2,m2)
		  end
		
  | E(itree(inode("expr", _),
				[
                                  exprAnd1
                                ]
      ),
      m0
    ) = E(exprAnd1, m0)
    
  (* And *)
  | E(itree(inode("exprAnd", _),
				[
					exprAnd1,
					itree(inode("&&", _), []),
					exprRel1
				]
			),
		  m0
    ) =
		  let
			  val (v1, m1) = E(exprAnd1, m0)
			  
		  in
                  
                        if v1 then 
                                 let
                                    val (v2, m2) = E(exprRel1, m1)
                                 in
                                    if v2 then (true,m2)
                                    else (false,m2)
                                 end
			else (false,m2)
		  end
      
  | E(itree(inode("exprAnd", _),
        [
          exprRel1
        ]
      ),
      m0
    ) = E(exprRel1, m0)
    
  (* GT *)
  | E(itree(inode("exprRel", _),
				[
					exprRel1,
					itree(inode(">", _), []),
					exprAdd1
				]
			),
		  m0
	  ) =
		  let
			  val (v1, m1) = E(exprRel1, m0)
			  val (v2, m2) = E(exprAdd1, m1)
		  in
			  (v1 > v2, m2)
		  end
    
	(* LT *)
  | E(itree(inode("exprRel",_),
				[
					exprRel1,
					itree(inode("<", _), []),
					exprAdd1
				]
			),
		  m0
	  ) =
		  let
			  val (v1, m1) = E(exprRel1, m0)
			  val (v2, m2) = E(exprAdd1, m1)
		  in
			  (v1 < v2, m2)
		  end
    
	(* GTE *)
  | E(itree(inode("exprRel",_),
				[
					exprRel1,
					itree(inode(">=", _), []),
					exprAdd1
				]
			),
		  m0
	  ) =
		  let
			  val (v1, m1) = E(exprRel1, m0)
			  val (v2, m2) = E(exprAdd1, m1)
		  in
			  (v1 >= v2, m2)
		  end
      
  (* LTE *)
  | E(itree(inode("exprRel", _),
				[
					exprRel1,
					itree(inode("<=", _), []),
					exprAdd1
				]
			),
		  m0
	  ) =
		  let
			  val (v1, m1) = E(exprRel1, m0)
			  val (v2, m2) = E(exprAdd1, m1)
		  in
		  	(v1 <= v2, m2)
		  end
	
	(* Equality *)
  | E(itree(inode("exprRel", _),
				[
					exprRel1,
					itree(inode("==", _), []),
					exprAdd1
				]
			),
		  m0
	  ) =
		  let
		  	val (v1, m1) = E(exprRel1, m0)
		  	val (v2, m2) = E(exprAdd1, m1)
		  in
			  (v1 = v2, m2)
		  end
		
	(* Negative Equality *)
  | E(itree(inode("exprRel", _),
				[
					exprRel1,
					itree(inode("!=", _), []),
					exprAdd1
				]
			),
		  m0
	  ) =
		  let
			  val (v1, m1) = E(exprRel1, m0)
			  val (v2, m2) = E(exprAdd1, m1)
		  in
			  (v1 <> v2, m2)
		  end
      
  | E(itree(inode("exprRel", _),
        [
          exprAdd1
        ]
      ),
      m0
    ) = E(exprAdd1, m0)

	(* exprAdd *)
  | E(itree(inode("exprAdd", _),
				[
					exprAdd1,
					itree(inode("+", _), []),
					exprTerm1
				]
			),
		  m0
    ) =
		  let
			  val (v1, m1) = E(exprAdd1, m0)
			  val (v2, m2) = E(exprTerm1, m1)
		  in
			  (v1 + v2, m2)
		  end
  | E(itree(inode("exprAdd", _),
        [
          exprAdd1,
          itree(inode("-", _), []),
          exprTerm1
        ]
      ),
      m0
    ) =
      let
        val (v1, m1) = E(exprAdd1, m0)
        val (v2, m2) = E(exprTerm1, m1)
      in
        (v1 - v2, m2)
      end
      
  | E(itree(inode("exprAdd", _),
         [
           exprTerm1
         ]
       ),
       m0
    ) = E(exprTerm1, m0)
		
	(* exprTerm *)
  | E(itree(inode("exprTerm", _),
				[
					exprTerm1,
					itree(inode("*", _), []),
					exprUnary1
				]
			),
		  m0
	  ) =
		  let
			  val (v1, m1) = E(exprTerm1, m0)
			  val (v2, m2) = E(exprUnary1, m1)
		  in
			  (v1 * v2, m2)
		  end
		
	(* Divide *)
  | E(itree(inode("exprTerm", _),
				[
					exprTerm1,
					itree(inode("/", _), []),
					exprUnary1
				]
			),
		m0
	) =
		let
			val (v1, m1) = E(exprTerm1, m0)
			val (v2, m2) = E(exprUnary1, m1)
		in
			(v1 div v2, m2)
		end
		
	(* Mod *)
  | E(itree(inode("exprTerm", _),
				[
					exprTerm1,
					itree(inode("%", _), []),
					exprUnary1
				]
			),
		m0
	) =
		let
			val (v1, m1) = E(exprTerm1, m0)
			val (v2, m2) = E(exprUnary1, m1)
		in
			(v1 mod v2, m2)
		end
    
  | E(itree(inode("exprTerm", _),
        [
          exprUnary1
        ]
      ),
      m0
    ) = E(exprUnary1, m0)

	(* Unary *)
  | E(itree(inode("exprUnary", _),
				[
					itree(inode("~", _), []),
					exprUnary1
				]
			),
		m0
	) =
		let
			val (v1, m1) = E(exprUnary1, m0)
		in
			(~v1, m1)
		end
		
  | E(itree(inode("exprUnary", _),
        [
          exprExpo1
        ]
      ),
      m0
    ) = E(exprExpo1, m0)
    
	(* Expo *)
  | E(itree(inode("exprExpo", _),
				[
					exprNot1,
					itree(inode("^", _), []),
					exprExpo1
				]
			),
		  m0
	  ) =
		  let
			  val (v1, m1) = E(exprNot1, m0)
			  val (v2, m2) = E(exprExpo1, m1)
		  in
			  (v1 pow v2, m2)
		  end

  | E(itree(inode("exprExpo", _),
        [
          exprNot1
        ]
      ),
      m0
    ) = E(exprNot1, m0)

	(* Not *)
  | E(itree(inode("exprNot", _),
				[
					itree(inode("!", _), []),
					exprFactor1
				]
			),
		  m0
	  ) =
		  let
			  val (v1, m1) = E(exprFactor1, m0)
		  in
			  (not v1, m1)
		  end
      
  | E(itree(inode("exprNot", _),
        [
          exprFactor1
        ]
      ),
      m0
    ) = E(exprFactor1, m0)
      
	(*Parenthesis*)
  | E(itree(inode("exprFactor",_),
				[
					itree(inode("(", _), []),
					expr1,
					itree(inode(")", _), [])
				]
			),
		  m0
	  ) = E(expr1, m0)
	
  | E(itree(inode("exprFactor",_),
        [
          itree(inode("integer", _), [])
        ]
      ),
      m0
    ) = E(integer, m0)
	
  | E(itree(inode("exprFactor",_),
                                [
          id1
        ]
      ),
      m0
    ) = 
        let
          val loc0 = getLoc(accessEnv(id1, m0))
          val v1   = accessStore(loc0, m0)
        in
          (v1, m0)
        end
        
  | E(itree(inode("exprFactor",_),
        [
          itree(inode("true", _), [])
        ]
      ),
      m0
    ) = E(true, m0)

  | E(itree(inode("exprFactor",_),
        [
          itree(inode("false", _), [])
        ]
      ),
      m0
    ) = E(false, m0)
  
  | E(itree(inode("exprFactor",_),
        [
          itree(inode("|", _), [])
          expr1
          itree(inode("|", _), [])
        ]
      ),
      m0
    ) =
      let
        val (v1, m1) = E(expr1, m0)
      in
        abs v1
      end

  | E(itree(inode("exprFactor", _),
				[
					itree(inode("++", _),[]),
					id1
				]
			),
		  m0
	  ) =
		  let
			  val loc	= getLoc(id1, m0)
			  val v1	= accessStore(loc, m0)
			  val m1	= updateStore(loc, v1 + 1, m0)
		  in
			  (v1 +1, m1)
		  end

  | E(itree(inode("exprFactor", _),
				[
					itree(inode("--", _), []),
					id1
				]
			),
		  m0
	  ) =
		  let
			  val loc	= getLoc(id1, m0)
			  val v1	= accessStore(loc, m0)
			  val m1	= updateStore(loc, v1 - 1, m0)
		  in
			  (v1 - 1,m1)
		  end
	
  | E(itree(inode("exprFactor", _),
				[
					id1,
					itree(inode("++", _), [])
				]
			),
		  m0
	  ) =
		  let
			  val loc	= getLoc(id1, m0)
			  val v1	= accessStore(loc, m0)
			  val m1	= updateStore(loc, v1 + 1, m0)
		  in
			  (v1 + 1,m1)
		  end

  | E(itree(inode("exprFactor", _),
				[
					id1,
					itree(inode("--", _), [])
				]
			),
		  m0
	  ) =
		  let
			  val loc	= getLoc(id1, m0)
			  val v1	= accessStore(loc, m0)
			  val m1	= updateStore(loc, v1 - 1, m0)
		  in
			  (v1 - 1,m1)
		  end
    
		
		
  (* ======== End expressions ======== *)
  	
 

  and P(itree(inode("whileBlock",_),
				[
					expr1,
					block1
				]
			),
		  m0
	  ) =
		  let
			   
                          val (v1,m1) = E(expr1, m0)
		  in
			  if v1 then P(expr1, block1, M(block1, m1))
			  else m1
		  end
 
 
  and N(itree(inode("forBlock", _),
				[
					expr1,
					id1,
					expr2,
					block1
				]
			),
		  m0
	  ) =
		  let
			  val m1 			 = M(block1, m0)
			  val loc 		         = getLoc(id1, m1)
			  val m2			 = E(expr2, m1)
			  val m3			 = updateStore(loc, v1, m2)
			  val (v1, m4)                   = E(expr1, m3)
		  in
			  if v1 then N(expr1, id1, expr2, block1, m4)
			  else m4
		  end;
(* =========================================================================================================== *)
end (* struct *)
(* =========================================================================================================== *)








