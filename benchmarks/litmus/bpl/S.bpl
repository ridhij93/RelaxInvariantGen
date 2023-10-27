/*
				T1							T2
					Pre := {x == 0, a == 0, y == 0}					
					
		P0						Q0

(x == 0 || x == 1)  && (a == 0) && (y == 0 )				(x == 0 || x == 2) && (a == 0) && (y == 0 || y == 1)

        s1: x = 2;	    						p=y;
    
P1: (x == 2) && (a == 0) && (y == 0 || y == 2)   	 	Q1: (x == 0 || x == 1) && (a == 0) && (y == 2)
   	 							
	s2: y = 1;							x=1;
								
P2: (x == 1 || x = 2) && (y == 1)				        Q2: ( x == 1) && (a == 0) && (y == 0 || y == 1) && (p == 0 || p == 1)
								
									if(p==1)
										a=1;
								  							
    							
						
		
					Post := {x != 2 || a != 1;}

*/

var x: int;
var y: int;
var a: int;
var p: int;


function {:existential true} {:inline} P0(x: int, a: int, p: int, y: int) : bool;
function {:existential true} {:inline} P1(x: int, a: int, p: int, y: int) : bool;
function {:existential true} {:inline} P2(x: int, a: int, p: int, y: int) : bool;
function {:existential true} {:inline} Q0(x: int, a: int, p: int, y: int) : bool;
function {:existential true} {:inline} Q1(x: int, a: int, p: int, y: int) : bool;
function {:existential true} {:inline} Q2(x: int, a: int, p: int, y: int) : bool;
function {:existential true} {:inline} Q3(x: int, a: int, p: int, y: int) : bool;

procedure pre_condition()
requires x == 0 && a == 0 && y == 0;
{ 
	assert P0(x, a, p, y);
  	assert Q0(x, a, p, y);
}

procedure post_condition()
requires P1(x, a, p, y);
requires Q3(x, a, p, y);
{ 
  	assert (a != 1 || x != 2);
}



procedure t1_transition_s1()
modifies x; 
requires P0(x, a, p, y);
ensures P1(x, a, p, y);
{ 
	x := 2;
}


procedure t1_transition_s2()
modifies y; 
requires P1(x, a, p, y);
ensures P2(x, a, p, y);
{ 
	y := 1;
}

procedure t2_transition_s1()
modifies p; 
requires Q0(x, a, p, y);
ensures Q1(x, a, p, y);
{ 
	p := y;
}

procedure t2_transition_s2()
modifies x; 
requires Q1(x, a, p, y);
ensures Q2(x, a, p, y);
{ 
	x := 1;
}

procedure t2_transition_s3()
modifies a; 
requires Q2(x, a, p, y);
ensures Q3(x, a, p, y);
{ 
	if (p == 1)
	{
	    a := 1;
	}    							
}

procedure P0_Stable_t2_s1()
modifies p; 
requires P0(x, a, p, y);
requires Q0(x, a, p, y);
ensures P0(x, a, p, y);
{ 
	p := y;
}

procedure P0_Stable_t2_s2()
modifies x; 
requires P0(x, a, p, y);
requires Q1(x, a, p, y);
ensures P0(x, a, p, y);
{ 
	x := 1;
}

procedure P0_Stable_t2_s3()
modifies a; 
requires P0(x, a, p, y);
requires Q2(x, a, p, y);
ensures P0(x, a, p, y);
{ 
	if( p == 1)
	{
		a := 1;
	}
										
}

procedure P1_Stable_t2_s1()
modifies p; 
requires P1(x, a, p, y);
requires Q0(x, a, p, y);
ensures P1(x, a, p, y);
{ 
	p := y;
}

procedure P1_Stable_t2_s2()
modifies x; 
requires P1(x, a, p, y);
requires Q1(x, a, p, y);
ensures P1(x, a, p, y);
{ 
	x := 1;
}

procedure P1_Stable_t2_s3()
modifies a; 
requires P1(x, a, p, y);
requires Q2(x, a, p, y);
ensures P1(x, a, p, y);
{ 
	if(p == 1)
	{
		a := 1;
	}
										
}


procedure Q0_Stable_t1_s1()
modifies x; 
requires P0(x, a, p, y);
requires Q0(x, a, p, y);
ensures Q0(x, a, p, y);
{ 
	x := 2;
}

procedure Q1_Stable_t1_s1()
modifies x; 
requires P0(x, a, p, y);
requires Q1(x, a, p, y);
ensures Q1(x, a, p, y);
{ 
	x := 2;
}

procedure Q2_Stable_t1_s1()
modifies x; 
requires P0(x, a, p, y);
requires Q2(x, a, p, y);
ensures Q2(x, a, p, y);
{ 
	x := 2;
}

procedure Q0_Stable_t1_s2()
modifies y; 
requires P1(x, a, p, y);
requires Q0(x, a, p, y);
ensures Q0(x, a, p, y);
{ 
	y := 1;
}

procedure Q1_Stable_t1_s2()
modifies y; 
requires P1(x, a, p, y);
requires Q1(x, a, p, y);
ensures Q1(x, a, p, y);
{ 
	y := 1;
}

procedure Q2_Stable_t1_s2()
modifies y; 
requires P1(x, a, p, y);
requires Q2(x, a, p, y);
ensures Q2(x, a, p, y);
{ 
	y := 1;
}
