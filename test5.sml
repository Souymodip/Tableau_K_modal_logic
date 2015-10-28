signature PropLogic =

sig
    exception Atom_exception
    datatype Prop =
     	 ATOM of string	    | 
     	 NOT of Prop	    |
     	 AND of Prop * Prop |
     	 OR of Prop * Prop  |
     	 IMP of Prop * Prop |
     	 EQL of Prop * Prop
	type Argument = Prop list * Prop

 
 	datatype node =
 		ALPHA of Prop list	|
 		BETA of Prop list* Prop list
 
 
    val show    : Prop -> unit
    val Tableau : Prop -> bool 
    val TableauArg : Argument -> bool
    val unsatisfiable :	Prop list*int -> bool
    val Display : node*int*int	-> unit 	(* Display the tree structure *)
    val help    : unit -> unit
    val documentation :unit -> unit
    val showArg : Prop list * Prop -> unit
    
end;


(* Propositional formulas *)

structure PL:PropLogic = 
(* structure PL = *) (* This is for debugging purposes only *)
struct


datatype Prop =
     	 ATOM of string	    | 
     	 NOT of Prop	    |
     	 AND of Prop * Prop |
     	 OR of Prop * Prop  |
     	 IMP of Prop * Prop |
     	 EQL of Prop * Prop
     ;
     
     exception Atom_exception;
     fun newatom (s) = if s = "" then raise Atom_exception
		       else (ATOM s);
	fun drawChar (c, n) =
		  if n>0 then (print(str(c)); drawChar(c, (n-1)))
		  else ();

		
     
	fun show (P) = 
         let fun showPlain (ATOM a)     = print (a)
     	|   showPlain (NOT (P))    = (print ("~"); showPlain (P))
     	|   showPlain (AND (P, Q)) = (print ("("); showPlain (P); 
     				      print(" /\\ "); showPlain (Q); print(")")
     				     )
             |   showPlain (OR (P, Q))  = (print ("("); showPlain (P); 
     				      print(" \\/ "); showPlain (Q); print(")")
     				     )
             |   showPlain (IMP (P, Q)) = (print ("("); showPlain (P); 
     				      print(" => "); showPlain (Q); print(")")
     				     )
     	|   showPlain (EQL (P, Q)) = (print ("("); showPlain (P); 
     				      print(" <=> "); showPlain (Q); print(")")
     				     )
         in (print (" "); showPlain (P); print (" "))
         end
     ;

          
     (* Convert all formulas not containing IMP or EQL into Negation Normal 
	Form. 
     *)
     
     fun nnf (ATOM a)	   	= ATOM a
     |   nnf (NOT (ATOM a))	   = NOT (ATOM a)
     |   nnf (NOT (NOT (P)))	   = nnf (P)
     |   nnf (AND (P, Q))	   = AND (nnf(P), nnf(Q))
     |   nnf (NOT (AND (P, Q))) = nnf (OR (NOT (P), NOT (Q)))
     |   nnf (OR (P, Q))	   = OR (nnf(P), nnf(Q))
     |   nnf (NOT (OR (P, Q)))  = nnf (AND (NOT (P), NOT (Q)))
     |	 nnf (A)		= A
     ;


(* The properties of a node *)
	
	fun	repeat (A, P::L)	=	if P = nnf(NOT A) orelse A = nnf(NOT P)  then true 
							else repeat(A,L)
	|	repeat (A, [])		=	false
	;	

	fun	isClosed ([])		= 	false
	|	isClosed (h::L)		= 	if repeat(h,L)=false then isClosed(L)
						else true
	;

	fun	whichRule ([])			=	1
	|	whichRule (NOT(AND(A,B))::L)	=	3
	|	whichRule (NOT(EQL(A,B))::L)	=	3	
	|	whichRule (NOT(ATOM A)::L)	=	whichRule(L)	
	|	whichRule (OR(A,B)::L)		=	3
	|	whichRule (IMP(A,B)::L)		=	3
	|	whichRule (EQL(A,B)::L)		=	3
	|	whichRule ((ATOM A)::L)		=	whichRule(L)
	;

	fun	seek_alpha ([])			=	4
	|	seek_alpha (NOT(OR(A,B))::L)	=	2	
	|	seek_alpha (NOT(IMP(A,B))::L)	=	2
	|	seek_alpha (NOT(NOT A)::L)	=	2
	|	seek_alpha (AND(A,B)::L)	=	2
	|	seek_alpha (h::L)		=	seek_alpha(L)
	;

	(* The proposition List  has the following Property
		0:	Is Closed and thus we move on to other branch
		1:	Is Open and thus the formula is satisfiable
		2:	Alpha rule is applicable
		3:	Beta Rule is applicable
	*)

	fun 	property(L)	=	if isClosed(L)	then 0	else (if seek_alpha(L)=4 then whichRule(L) else 2);


	(* Alpha and Beta Rules *)
	fun 	A_rule(L)	=	let		
						fun	A_rule1([],_)			=	[]
						|	A_rule1(NOT(NOT A)::L,K)		=	K@(A::L)
						|	A_rule1(NOT(OR(A,B))::L,K)	=	K@[(NOT A),(NOT B)]@L
						|	A_rule1(NOT(IMP(A,B))::L,K)	=	K@[A,(NOT B)]@L
						|	A_rule1(AND(A,B)::L,K)		=	K@[A,B]@L
						|	A_rule1(H::L,K)			=	A_rule1(L,K@[H])	
					in A_rule1(L,[])
					end	
	;


	fun 	B_rule(L)	=	let
						fun	B_rule1([],_)			= 	([],[])
						|	B_rule1(NOT(AND(A,B))::L,K)	=	( K@((NOT A)::L) , K@((NOT B)::L) )
						|	B_rule1(NOT(EQL(A,B))::L,K)	=	(K@[A,(NOT B)]@L , K@[(NOT A),B]@L)
						|	B_rule1(OR(A,B)::L,K)		=	(K@(A::L) , K@(B::L))
						|	B_rule1(IMP(A,B)::L,K)		=	(K@((NOT A)::L) , K@(B::L))
						|	B_rule1(EQL(A,B)::L,K)		=	(K@[A,B]@L	, K@[(NOT A),(NOT B)]@L)
						|	B_rule1(H::L,K)			=	B_rule1(L,K@[H])	
					in	B_rule1(L,[])
					end
	;


	datatype node	=
		ALPHA of Prop list	|
		BETA of Prop list*Prop list
	;

	

	(* The Tree dsplay of an expanding tableau method *)

	fun	branch(0)	= print("\n |_")
	|	branch(i)	= (branch(i-1);print("__"))
	;
	
	fun 	printList([])	=	print("")
	|	printList(L::H)	=	(show(L);print(" ; ");printList(H))
	;	
	

	fun	Display(ALPHA L,0,i)		=	(branch(i);printList(L);print(" The Branch is Closed! "))
	|	Display(ALPHA L,1,i)		=	(branch(i);printList(L);print(" The Branch is Open! "))
	|	Display(ALPHA L,2,i)		=	(branch(i);printList(L))
	|	Display(BETA (L,R),_,i)	=	(branch(i);printList(L);print(" <---^---> ");printList(R))			
	;

	(* Unsatisfiablity Checker This function will be used a tableau for the prop list *)
	
	fun	unsatisfiable([],i)	=	(Display(ALPHA([]),0,i);false)
	|	unsatisfiable(P,i)	=	case property(P) of
							0	=> ( Display(ALPHA P,0,i);true)
						|	1	=> ( Display(ALPHA P,1,i);false)
						|	2	=> ( Display(ALPHA (A_rule(P)),2,i);unsatisfiable(A_rule(P),i))
						|	3	=> ( Display(BETA(B_rule P),3,(i+1)); if unsatisfiable(#1(B_rule P),(i+1))  
									then unsatisfiable(#2(B_rule P),(i+1)) else false)
	;


	
	type Argument = Prop list * Prop;

	fun showArg (A: Argument) =
         let fun printArg (A:Argument as ([], c)) = 
                 (drawChar (#"-", 80); print("\n");
                  show (c); print ("\n\n")
                 )
	     |   printArg (A:Argument as (p::plist, c)) = 
                  (show (p); print ("\n");
                   printArg (plist, c)
                  )
         in (print ("\n\n"); printArg (A))
	 end
     	;

	
	fun	TableauArg(A:Argument)	=	let val al = NOT(#2(A))::(#1(A));
						in
							(	print("|");showArg(A);print("|");	unsatisfiable(al,0)		)
						end
	;

	fun 	Tableau(P)		=	(print("|");show(NOT P);print("|");unsatisfiable([NOT P],0));


(* --------------------------------------------------------------------------------------------------------------------------------------------------------------*)
	
	fun 	help()		= 	(print(" ------------------------------------------- HELP -------------------------------------------- \n");
					print(".unsatisfaible takes Proposition List and 0.\n");
					print(".TableauArg takes the Argument to be cheked for Logical consequence.\n");	
					print(".Tableau takes the formula to be cheked for validity.\n\n\n\n"));
		
	fun 	documentation()	= (print("\n\n\n --------------------------------------- Documentation ----------------------------------------- \n");
				  print(".The show function is modified to show sentences in compact form rather than as trees.\n");
				  print(".The rules are divided into two groups alpha and beta .\n");
				  print(".The alpha makes the tableau expand downwards.\n");
				  print(".The beta rule creats additional branch which needed to be checked if necessary.\n");
				  print(".This algorithm has a fine tinkering. It gives priority to alpha sentences. If no alpha sentences are\n available at the present stage then only it goes for beta rule. I didn't need to sort the entire formula Set.\n I pick the formula with higher priority, in this case alpha formulas.\n");
				  print(".This version also contains construct to describe hypothesises and conclusion and hence check\n logical consequence.\n");
				  print(".The tableau now shows each step in a depth tree fashion in a tree representation.\n\n\n\n\n"));

end (*Struct*);



open K;

val A = ATOM "A is a Knave";
val B = ATOM "B is a Knave";
val Bs = ATOM "B said A said he is a Knave";
val As = ATOM "A said he is a Knave";
val T = IMP(AND(NOT As,Bs),B);
val T1 = IMP(AND(As,Bs),NOT B);
val Y = NOT(AND(A,As));
val Y1 = NOT(AND(NOT A,As));

val arg = ([Bs,T,T1,Y,Y1],B);
