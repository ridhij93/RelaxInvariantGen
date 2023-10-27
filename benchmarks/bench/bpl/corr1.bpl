/*
				T1							T2
					Pre := {x == 1, a == 0}					
					
		P0							Q0

(x == 1) && (a == 0)						(x == 1)&&(a == 0)

		s1:	x := 2;				    p = x;
								Q1: (x == 1 || x == 2) && (a == 0) && (p == 1 || p == 2)
		s2:						    q = x;
	 							Q2: (x == 1 || x == 2) && (a == 0) && ((p == 1 && (q == 1 || q == 2))|| (p == 2 && q == 2))  
	        s3: 					           if((p == 2) && (q == 1))
									a = 1;
		P1							Q3

(x == 2) && (a == 0)
		        


					Post := {a != 1}




	
*/

var x: int;
var a: int;
var p: int;
var q: int;

function {:existential true} {:inline} P0(x: int, a: int, p: int, q: int) : bool;
function {:existential true} {:inline} P1(x: int, a: int, p: int, q: int) : bool;

function {:existential true} {:inline} Q0(x: int, a: int, p: int, q: int) : bool;
function {:existential true} {:inline} Q1(x: int, a: int, p: int, q: int) : bool;
function {:existential true} {:inline} Q2(x: int, a: int, p: int, q: int) : bool;
function {:existential true} {:inline} Q3(x: int, a: int, p: int, q: int) : bool;


procedure pre_condition()
requires x == 1 && a == 0;
{ 
	assert P0(x, a, p, q);
  	assert Q0(x, a, p, q);
}

procedure post_condition()
requires P1(x, a, p, q);
requires Q3(x, a, p, q);
{ 
  	assert (a != 1);
}


procedure t1_transition_s1()
modifies x; 
requires P0(x, a, p, q);
ensures P1(x, a, p, q);
{ 
	x := 2;
}



procedure t2_transition_s1()
modifies p; 
requires Q0(x, a, p, q);
ensures Q1(x, a, p, q);
{ 
	p := x;
}

procedure t2_transition_s2()
modifies q; 
requires Q1(x, a, p, q);
ensures Q2(x, a, p, q);
{ 
	q := x;
}

procedure t2_transition_s3()
modifies a; 
requires Q2(x, a, p, q);
ensures Q3(x, a, p, q);
{ 
	if((p == 2) && (q == 1))
	{
		a := 1;
	}								
}


procedure P0_Stable_t2_s1()
modifies p; 
requires P0(x, a, p, q);
requires Q0(x, a, p, q);
ensures P0(x, a, p, q);
{ 
	p := x;
}

procedure P0_Stable_t2_s2()
modifies q; 
requires P0(x, a, p, q);
requires Q1(x, a, p, q);
ensures P0(x, a, p, q);
{ 
	q := x;
}

procedure P0_Stable_t2_s3()
modifies a; 
requires P0(x, a, p, q);
requires Q2(x, a, p, q);
ensures P0(x, a, p, q);
{ 
	if((p == 2) && (q == 1))
	{
		a := 1;
	}
}


procedure Q0_Stable_t1_s1()
modifies x; 
requires P0(x, a, p, q);
requires Q0(x, a, p, q);
ensures Q0(x, a, p, q);
{ 
	x := 2;
}

procedure Q1_Stable_t1_s1()
modifies x; 
requires P0(x, a, p, q);
requires Q1(x, a, p, q);
ensures Q1(x, a, p, q);
{ 
	x := 2;
}

procedure Q2_Stable_t1_s1()
modifies x; 
requires P0(x, a, p, q);
requires Q2(x, a, p, q);
ensures Q2(x, a, p, q);
{ 
	x := 2;
}
