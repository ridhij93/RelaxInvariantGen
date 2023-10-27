/*
				T1							T2
					Pre := {x == 1, a == 0}					
					
		P0							Q0

(x == 0) && (a == 0)						(x == 0)&&(a == 0)

    s1: x = 1;	    						x = 2;	
    P1: (x == 0 || x == 2) && (p == 0 || p == 2)
    s2: p = x;							Q1: ( x == 2) 
    P2: (x == 1) && (p == 0 || p == 2)							
    							
    s3: if (p == 2)
	    a = 1;				   
    P3:						
		
					Post := {(a!=1 || x!=2);}

*/

var x: int;
var a: int;
var p: int;


function {:existential true} {:inline} Q0(x: int, a: int, p: int) : bool;
function {:existential true} {:inline} Q1(x: int, a: int, p: int) : bool;

function {:existential true} {:inline} P0(x: int, a: int, p: int) : bool;
function {:existential true} {:inline} P1(x: int, a: int, p: int) : bool;
function {:existential true} {:inline} P2(x: int, a: int, p: int) : bool;
function {:existential true} {:inline} P3(x: int, a: int, p: int) : bool;

procedure pre_condition()
requires x == 0 && a == 0;
{ 
	assert P0(x, a, p);
  	assert Q0(x, a, p);
}

procedure post_condition()
requires P3(x, a, p);
requires Q1(x, a, p);
{ 
  	assert (a != 1 || x != 2);
}


procedure t2_transition_s1()
modifies x; 
requires Q0(x, a, p);
ensures Q1(x, a, p);
{ 
	x := 2;
}




procedure t1_transition_s1()
modifies x; 
requires P0(x, a, p);
ensures P1(x, a, p);
{ 
	x := 1;
}

procedure t1_transition_s2()
modifies p; 
requires P1(x, a, p);
ensures P2(x, a, p);
{ 
	p := x;
}

procedure t1_transition_s3()
modifies a; 
requires P2(x, a, p);
ensures P3(x, a, p);
{ 
	if (p == 2)
	{
	    a := 1;
	}    							
}

procedure Q0_Stable_t2_s1()
modifies x; 
requires P0(x, a, p);
requires Q0(x, a, p);
ensures P0(x, a, p);
{ 
	x := 2;
}

procedure Q0_Stable_t2_s2()
modifies x; 
requires Q0(x, a, p);
requires P1(x, a, p);
ensures P1(x, a, p);
{ 
	x := 2;
}

procedure Q0_Stable_t2_s3()
modifies x; 
requires Q0(x, a, p);
requires P2(x, a, p);
ensures P2(x, a, p);
{ 
	x := 2;
}

procedure P0_Stable_t2_s2()
modifies x; 
requires P0(x, a, p);
requires Q0(x, a, p);
ensures Q0(x, a, p);
{ 
	x := 1;
}

procedure P1_Stable_t2_s2()
modifies p; 
requires Q0(x, a, p);
requires P1(x, a, p);
ensures Q0(x, a, p);
{ 
	p := x;
}

procedure P2_Stable_t2_s2()
modifies a; 
requires Q0(x, a, p);
requires P2(x, a, p);
ensures Q0(x, a, p);
{ 
	if (p == 2)
	{
	    a := 1;
	}    							
}

