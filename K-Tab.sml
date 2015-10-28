signature ModalLogic =

sig
	datatype World = WORLD of int
	
	datatype Form =
     	 ATOM of string	    |
	 BOX of Form	    |
	 DIA of Form	    |	
      	 NOT of Form	    |
     	 AND of Form * Form |
     	 OR of Form * Form  |
     	 IMP of Form * Form |
     	 EQL of Form * Form

	
	type Argument = Form list * Form
     
	val Tableau 	: Form -> bool
	val TableauArg	: Argument -> bool
	val Documentation	: unit	-> unit
	val Help		: unit	-> unit
end;
	     

structure K:ModalLogic = 
(* structure K = *) (* This is for debugging purposes only *)
struct

     datatype World = WORLD of int	;

     fun	newWorld(WORLD w,i)	=	WORLD (w*10+i);	
	
     datatype Form =
     	 ATOM of string	    |
	 BOX of Form	    |
	 DIA of Form	    |	
      	 NOT of Form	    |
     	 AND of Form * Form |
     	 OR of Form * Form  |
     	 IMP of Form * Form |
     	 EQL of Form * Form 
    ;
     
     type Pfrom = World * (Form	list);	(* predicate Formulas : w |= X *) 	
     
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
	|   showPlain (BOX P)	=   (print("[]");showPlain(P))
	|   showPlain (DIA P)	=   (print("<>");showPlain(P))
         in (print (" "); showPlain (P); print (" "))
         end
     ;


     (* The Negative normal is necessary to find Conjugate Pairs *)
     
     fun	nnf (ATOM a)	   	= ATOM a
     |   	nnf (NOT (ATOM a))	= NOT (ATOM a)
     |   	nnf (NOT (NOT (P)))	= nnf (P)
     |   	nnf (NOT (OR (P, Q)))  	= nnf (AND (NOT (P), NOT (Q)))
     |   	nnf (NOT (AND (P, Q))) 	= nnf (OR (NOT (P), NOT (Q)))
     |		nnf (NOT (BOX P))	= DIA (nnf (NOT P))
     |		nnf (NOT (DIA P))	= BOX (nnf (NOT P)) 	
     |   	nnf (AND (P, Q))	= AND (nnf(P), nnf(Q))
     |   	nnf (OR (P, Q))	   	= OR  (nnf(P), nnf(Q))
     |		nnf (BOX P)		= BOX (nnf P)
     |		nnf (DIA P)		= DIA (nnf P)
     |	 	nnf (A)			= A
     ;


	(* The Formulas are processed to give a CP saturated Formula set*)
	fun	repeat (A, P::L)	=	if P = nnf(NOT A) orelse A = nnf(NOT P)  then true 
							else repeat(A,L)
	|	repeat (A, [])		=	false
	;	

	fun	isClosed ([])		= 	false
	|	isClosed (h::L)		= 	if repeat(h,L)=false then isClosed(L)
						else true
	;
	

	fun	seek_beta ([])			=	1
	|	seek_beta (NOT(AND(A,B))::L)	=	3
	|	seek_beta (NOT(EQL(A,B))::L)	=	3	
	|	seek_beta (OR(A,B)::L)		=	3
	|	seek_beta (IMP(A,B)::L)		=	3
	|	seek_beta (EQL(A,B)::L)		=	3
	|	seek_beta (A::L)		=	seek_beta(L)
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
		4: 	Theta K Rule is applicable and the formula set is CP saturated
	*)

	fun 	property(L)	=	if isClosed(L)	then 0	else (if seek_alpha(L)=4 then seek_beta(L) else 2);
	
	fun	isDia ([])		= 	false
	|	isDia (NOT(BOX P)::L)	=	true
	|	isDia (DIA P::L)	=	true
	|	isDia (h::L)		= 	isDia L
	;

	fun	Mproperty(L)	=	let val v = property L in
					if  v = 1 then (if isDia L then 4 else 1) else v
					end	
	;
	
	(* The Rules take set of formulas and return a set Formulas . Beta rule returns pair of sets *)
	(* Returns empty if the rule cnnot be applied *)

	

	fun 	A_rule(L)	=	let		
						fun	A_rule1([],K)			=	K
						|	A_rule1(NOT(NOT A)::L,K)	=	K@(A::L)
						|	A_rule1(NOT(OR(A,B))::L,K)	=	(NOT A)::(NOT B)::K@L
						|	A_rule1(NOT(IMP(A,B))::L,K)	=	A::(NOT B)::K@L
						|	A_rule1(AND(A,B)::L,K)		=	A::B::K@L
						|	A_rule1(H::L,K)			=	A_rule1(L,H::K)	
		
										
					in 	A_rule1(L,[])
					end	
	;

	fun 	B_rule(L)	=	let
						fun	B_rule1([],_)			= 	([],[])
						|	B_rule1(NOT(AND(A,B))::L,K)	=	( K@((NOT A)::L) , K@((NOT B)::L))
						|	B_rule1(NOT(EQL(A,B))::L,K)	=	((A::(NOT B)::K@L) , (NOT A)::B::K@L)
						|	B_rule1(OR(A,B)::L,K)		=	((K@(A::L)) , K@(B::L))
						|	B_rule1(IMP(A,B)::L,K)		=	((K@((NOT A)::L)) , K@(B::L))
						|	B_rule1(EQL(A,B)::L,K)		=	(A::B::K@L , K@((NOT A)::(NOT B)::L))
						|	B_rule1(H::L,K)			=	B_rule1(L,H::K)	
		
						in	B_rule1(L,[])
						end
	;

	(* Tableau closed : true , Open : false *)

	fun	branch(0)	= print("\n |_")
	|	branch(i)	= (branch(i-1);print("___"))
	;
	
	fun 	printList([])	=	print("")
	|	printList(L::H)	=	(show(L);print(" ; ");printList(H))
	;	

	fun	printW(WORLD w)	=	(print("  w");print(Int.toString w);print(" |- "))
	

	fun	Display((w,L),0,i)		=	(branch(i);printW(w);printList(L);print(" The Branch is Closed! "))
	|	Display((w,L),1,i)		=	(branch(i);printW(w);printList(L);print(" The Branch is Open! "))
	|	Display((w,L),2,i)		=	(branch(i);printW(w);printList(L))
	;

	fun	CP_rules((w:World,L),i:int)	= let
	

		fun	TK_rule(w:World,L,i)	= let
						
			fun	Collect([],S,Y,Z)		=	(S,Y,Z)
			|	Collect(NOT(BOX P)::L,S,Y,Z)	=	Collect(L,S,Y,NOT(P)::Z)
			|	Collect(NOT(DIA P)::L,S,Y,Z)	=	Collect(L,S,NOT(P)::Y,Z)
			|	Collect(BOX P::L,S,Y,Z)		=	Collect(L,S,P::Y,Z)
			|	Collect(DIA P::L,S,Y,Z)		=	Collect(L,S,Y,P::Z) 			
			|	Collect(P::L,S,Y,Z)		=	Collect(L,P::S,Y,Z)
				
			val l =	Collect (L,[],[],[])
			
			fun	apply_CP ((_,Y,[]),_)	=	true
			|	apply_CP ((S,Y,h::Z),i)	=	if CP_rules((newWorld(w,i),h::Y),0) then apply_CP((S,Y,Z),i+1) 
								else false
						
		in
			 apply_CP (l,0)						
		end
						
	in
		case Mproperty(L) of
			0	=> (Display((w,L),2,i);false)			(* CLOSED *)
		|	1	=> (Display((w,L),2,i);true)			(* CP saturated and has Diamond Modal Variant*)
		|	2	=> (Display((w,L),2,i);CP_rules((w,A_rule(L)),i))
		|	3	=> let val v = (Display((w,L),2,i);B_rule L) 
				   in
					if CP_rules( (w,#1(v)),(i+1)) = false then CP_rules( (w,#2(v)),(i+1)) else true 
				   end
		|	4	=> (Display((w,L),2,i);TK_rule(w,L,i))
	end
	;

	

	(* S contains purely propositional formulas , Y = {[]Pi | i<n} , Z = {<>Pi | i<m}*)

	(*fun	TK_rule(w:World,L,i)	=	let
						fun	Collect([],S,Y,Z)	=	(S,Y,Z)
						|	Collect(BOX P::L,S,Y,Z)	=	Collect(L,S,P::Y,Z)
						|	Collect(DIA P::L,S,Y,Z)	=	Collect(L,S,Y,P::Z) 			
						|	Collect(P::L,S,Y,Z)	=	Collect(L,P::S,Y,Z)
				
						val l =	Collect (L,[],[],[])
						
						fun	create_world (S,Y,[],K)	=	K
						|	create_world (S,Y,h::Z,K)=	h
		
						fun	apply_CP ((_,Y,[]),_)	=	true
						|	apply_CP ((S,Y,h::Z),i)	=	if CP_rule((newWorld(w,i),h::Y),0) then apply_CP((S,Y,Z),i+1) 
											else false
						
						in
							 apply_CP (l,0)						
						end
	;	 
	*)						
	

	(* for DISPLAY

	


	fun	branch(0)	= print("\n |_")
	|	branch(i)	= (branch(i-1);print("___"))
	;
	
	fun 	printList([])	=	print("")
	|	printList(L::H)	=	(show(L);print(" ; ");printList(H))
	;	

	fun	printW(World w)	=	(print("  w");print(Int.toString w);print(" ||- "))
	

	fun	Display((w,L),0,i)		=	(branch(i);printList(L);print(" The Branch is Closed! "))
	|	Display((w,L),1,i)		=	(branch(i);printList(L);print(" The Branch is Open! "))
	|	Display((w,L),2,i)		=	(branch(i);printList(L))
	;
*)
	type Argument = Form list * Form;

	fun drawChar (c, n) =
		  if n>0 then (print(str(c)); drawChar(c, (n-1)))
		  else ();

			

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

	fun	Tableau (F)	=	not (CP_rules ((WORLD 0,[NOT F]),0));

	fun	TableauArg (H,C)=	not (CP_rules ((WORLD 0,(NOT C)::H),0));

	fun	Documentation() =	(print("\n ----------------------------  Documentation  -----------------------------------\n");
					 print(" Don't Have anything Clever to say \n"));

	fun	Help()		= 	(print("\n ---------------------------- HELP ----------------------------------------------\n");
					 print(". Tableau formula : for running \n");print(". TableauArg Argument : for consequence \n"));	

end (*struct*);

val P= ATOM "P";
val Q= ATOM "Q";
val f = AND(AND (P,Q),NOT P);
val f1 = IMP(P,IMP(Q,P));
val f2 = IMP(BOX(IMP(P,Q)),IMP(BOX P,BOX Q));
val w = WORLD 1;

CP_rules ((w,[NOT f2]),0);
