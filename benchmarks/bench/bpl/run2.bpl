/*
				T1							T2
					Pre := {x == 0, y == 0}					
					
		P0							Q0

((x == 0)||(x == 2))		                                    (x == 0)||(x == 2)


		  	s1:	x := x + 1;					x := x + 2;
		P1							Q1

((x == 1) || (x == 3)))		      			     (x == 2||(x == 3))




					Post := {x == 3}




function {:existential true} {:inline} P0(x: int, y: int) : bool {
  ((x == 0)||(x == 2))&&((y == 2)||(y == 0))
}
function {:existential true} {:inline} P1(x: int, y: int) : bool {
  ((x == 1)||(x == 3))&&((y == 2)||(y == 0))
}
function {:existential true} {:inline} P2(x: int, y: int) : bool {
  ((x == 1)||(x == 3))&&((y == 3)||(y == 1))
}
function {:existential true} {:inline} Q0(x: int, y: int) : bool {
  ((x == 0)||(x == 1))&&((y == 2)||(y == 3))  
}
function {:existential true} {:inline} Q1(x: int, y: int) : bool {
  ((x == 2)||(x == 3))&&((y == 2)||(y == 3))
}
function {:existential true} {:inline} Q2(x: int, y: int) : bool {
  ((x == 2)||(x == 3))&&((y == 0)||(y == 1))  
}
	
*/

var x: int;

function {:existential true} {:inline} P0(x: int) : bool;
function {:existential true} {:inline} P1(x: int) : bool;
//function {:existential true} {:inline} P2(x: int, y: int) : bool;
function {:existential true} {:inline} Q0(x: int) : bool;
function {:existential true} {:inline} Q1(x: int) : bool;
//function {:existential true} {:inline} Q2(x: int, y: int) : bool;

procedure pre_condition()
requires x == 0;
{ 
	assert P0(x);
  	assert Q0(x);
}

procedure post_condition()
requires P1(x);
requires Q1(x);
{ 
  	assert x == 3;
}


procedure t1_transition_s1()
modifies x; 
requires P0(x);
ensures P1(x);
{ 
	x := x + 1;
}



procedure t2_transition_s1()
modifies x; 
requires Q0(x);
ensures Q1(x);
{ 
	x := x + 2;
}



procedure P0_Stable_t2_s1()
modifies x; 
requires P0(x);
requires Q0(x);
ensures P0(x);
{ 
	x := x + 2;
}

procedure P1_Stable_t2_s1()
modifies x; 
requires P1(x);
requires Q0(x);
ensures P1(x);
{ 
	x := x + 2;
}


procedure Q0_Stable_t1_s1()
modifies x; 
requires P0(x);
requires Q0(x);
ensures Q0(x);
{ 
	x := x + 1;
}


procedure Q1_Stable_t1_s1()
modifies x; 
requires P0(x);
requires Q1(x);
ensures Q1(x);
{ 
	x := x + 1;
}











