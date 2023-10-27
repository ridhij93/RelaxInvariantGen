/*
				T1							T2
					Pre := {x == 0, a == 0, y == 0}					
					
		P0						Q0

(x == 0 || x == 1)  && (a == 0) && (y == 0 )				(x == 0 || x == 2) && (a == 0) && (y == 0 || y == 1)

        s1: x = 1;	    						y=1;
    
P1: (x == 2) && (a == 0) && (y == 0 || y == 2)   	 	Q1: (x == 0 || x == 1) && (a == 0) && (y == 2)
   	 							
	s2: p = y;							q=x;
								
P2: (x == 1 || x = 2) && (y == 1)				        Q2: ( x == 1) && (a == 0) && (y == 0 || y == 1) && (p == 0 || p == 1)
								
	s3: if (p == 0)						if(q == 0)
		a = 1								b = 1;
P3:									Q3	
								  							
    							
						
		
					Post := {a != 1 || b != 1;}

P0
    x = 1;
P1



Q0
    p = x;
Q1    
    q = y;
Q2
    if (p==1 && q==0)
		  a=1;
Q3



R0
    y = 1;
R1
    r = x;
R2
    if (r==0)
			b=1;
R3


  assert (a != 1 || b != 1);

*/

var x: int;
var y: int;
var a: int;
var p: int;
var q: int;
var r: int;
var b: int;



function {:existential true} {:inline} P0(x: int, a: int, p: int, q: int, r: int, b: int, y: int) : bool;
function {:existential true} {:inline} P1(x: int, a: int, p: int, q: int, r: int, b: int, y: int) : bool;


function {:existential true} {:inline} Q0(x: int, a: int, p: int, q: int, r: int, b: int, y: int) : bool;
function {:existential true} {:inline} Q1(x: int, a: int, p: int, q: int, r: int, b: int, y: int) : bool;
function {:existential true} {:inline} Q2(x: int, a: int, p: int, q: int, r: int, b: int, y: int) : bool;
function {:existential true} {:inline} Q3(x: int, a: int, p: int, q: int, r: int, b: int, y: int) : bool;

function {:existential true} {:inline} R0(x: int, a: int, p: int, q: int, r: int, b: int, y: int) : bool;
function {:existential true} {:inline} R1(x: int, a: int, p: int, q: int, r: int, b: int, y: int) : bool;
function {:existential true} {:inline} R2(x: int, a: int, p: int, q: int, r: int, b: int, y: int) : bool;
function {:existential true} {:inline} R3(x: int, a: int, p: int, q: int, r: int, b: int, y: int) : bool;



procedure pre_condition()
requires x == 0 && a == 0 && b == 0 && y == 0;
{ 
	assert P0(x, a, p, q, r, b, y);
  	assert Q0(x, a, p, q, r, b, y);
  	assert R0(x, a, p, q, r, b, y);
}

procedure post_condition()
requires P1(x, a, p, q, r, b, y);
requires Q3(x, a, p, q, r, b, y);
requires R3(x, a, p, q, r, b, y);
{ 
  	assert ( a != 1 || b != 1 );
}



procedure t1_transition_s1()
modifies x; 
requires P0(x, a, p, q, r, b, y);
ensures P1(x, a, p, q, r, b, y);
{ 
	x := 1;
}



procedure t2_transition_s1()
modifies p; 
requires Q0(x, a, p, q, r, b, y);
ensures Q1(x, a, p, q, r, b, y);
{ 
	p := x;
}

procedure t2_transition_s2()
modifies q; 
requires Q1(x, a, p, q, r, b, y);
ensures Q2(x, a, p, q, r, b, y);
{ 
	q := y;
}

procedure t2_transition_s3()
modifies a; 
requires Q2(x, a, p, q, r, b, y);
ensures Q3(x, a, p, q, r, b, y);
{ 
	if (p==1 && q==0)
	{
	    a := 1;
	}    							
}

procedure t3_transition_s1()
modifies y; 
requires R0(x, a, p, q, r, b, y);
ensures R1(x, a, p, q, r, b, y);
{ 
	y := 1;
}

procedure t3_transition_s2()
modifies r; 
requires R1(x, a, p, q, r, b, y);
ensures R2(x, a, p, q, r, b, y);
{ 
	r := x;
}

procedure t3_transition_s3()
modifies b; 
requires R2(x, a, p, q, r, b, y);
ensures R3(x, a, p, q, r, b, y);
{ 
	if (r==0)
	{
		b := 1;
	}	
}

procedure P0_Stable_t2_s1()
modifies p; 
requires P0(x, a, p, q, r, b, y);
requires Q0(x, a, p, q, r, b, y);
ensures P0(x, a, p, q, r, b, y);
{ 
	p := x;
}




procedure P0_Stable_t2_s2()
modifies q; 
requires P0(x, a, p, q, r, b, y);
requires Q1(x, a, p, q, r, b, y);
ensures P0(x, a, p, q, r, b, y);
{ 
	q := y;
}

procedure P0_Stable_t2_s3()
modifies a; 
requires P0(x, a, p, q, r, b, y);
requires Q2(x, a, p, q, r, b, y);
ensures P0(x, a, p, q, r, b, y);
{ 
	if (p==1 && q==0)
	{
	    a := 1;
	} 
}


procedure R0_Stable_t2_s1()
modifies p; 
requires R0(x, a, p, q, r, b, y);
requires Q0(x, a, p, q, r, b, y);
ensures R0(x, a, p, q, r, b, y);
{ 
	p := x;
}



procedure R0_Stable_t2_s2()
modifies q; 
requires R0(x, a, p, q, r, b, y);
requires Q1(x, a, p, q, r, b, y);
ensures R0(x, a, p, q, r, b, y);
{ 
	q := y;
}

procedure R0_Stable_t2_s3()
modifies a; 
requires R0(x, a, p, q, r, b, y);
requires Q2(x, a, p, q, r, b, y);
ensures R0(x, a, p, q, r, b, y);
{ 
	if (p==1 && q==0)
	{
	    a := 1;
	}
}



procedure R1_Stable_t2_s1()
modifies p; 
requires R1(x, a, p, q, r, b, y);
requires Q0(x, a, p, q, r, b, y);
ensures R1(x, a, p, q, r, b, y);
{ 
	p := x;
}



procedure R1_Stable_t2_s2()
modifies q; 
requires R1(x, a, p, q, r, b, y);
requires Q1(x, a, p, q, r, b, y);
ensures R1(x, a, p, q, r, b, y);
{ 
	q := y;
}

procedure R1_Stable_t2_s3()
modifies a; 
requires R1(x, a, p, q, r, b, y);
requires Q2(x, a, p, q, r, b, y);
ensures R1(x, a, p, q, r, b, y);
{ 
	if (p==1 && q==0)
	{
	    a := 1;
	}
}



procedure R2_Stable_t2_s1()
modifies p; 
requires R2(x, a, p, q, r, b, y);
requires Q0(x, a, p, q, r, b, y);
ensures R2(x, a, p, q, r, b, y);
{ 
	p := x;
}



procedure R2_Stable_t2_s2()
modifies q; 
requires R2(x, a, p, q, r, b, y);
requires Q1(x, a, p, q, r, b, y);
ensures R2(x, a, p, q, r, b, y);
{ 
	q := y;
}

procedure R2_Stable_t2_s3()
modifies a; 
requires R2(x, a, p, q, r, b, y);
requires Q2(x, a, p, q, r, b, y);
ensures R2(x, a, p, q, r, b, y);
{ 
	if (p==1 && q==0)
	{
	    a := 1;
	}
}



procedure Q0_Stable_t1_s1()
modifies x; 
requires P0(x, a, p, q, r, b, y);
requires Q0(x, a, p, q, r, b, y);
ensures Q0(x, a, p, q, r, b, y);
{ 
	x := 1;
}

procedure Q1_Stable_t1_s1()
modifies x; 
requires P0(x, a, p, q, r, b, y);
requires Q1(x, a, p, q, r, b, y);
ensures Q1(x, a, p, q, r, b, y);
{ 
	x := 1;
}


procedure Q2_Stable_t1_s1()
modifies x; 
requires P0(x, a, p, q, r, b, y);
requires Q2(x, a, p, q, r, b, y);
ensures Q2(x, a, p, q, r, b, y);
{ 
	x := 1;
}


procedure R0_Stable_t1_s1()
modifies x; 
requires P0(x, a, p, q, r, b, y);
requires R0(x, a, p, q, r, b, y);
ensures R0(x, a, p, q, r, b, y);
{ 
	x := 1;
}

procedure R1_Stable_t1_s1()
modifies x; 
requires P0(x, a, p, q, r, b, y);
requires R1(x, a, p, q, r, b, y);
ensures R1(x, a, p, q, r, b, y);
{ 
	x := 1;
}

procedure R2_Stable_t1_s1()
modifies x; 
requires P0(x, a, p, q, r, b, y);
requires R2(x, a, p, q, r, b, y);
ensures R2(x, a, p, q, r, b, y);
{ 
	x := 1;
}




procedure P0_Stable_t3_s1()
modifies y; 
requires P0(x, a, p, q, r, b, y);
requires R0(x, a, p, q, r, b, y);
ensures P0(x, a, p, q, r, b, y);
{ 
	y := 1;
}

procedure P0_Stable_t3_s2()
modifies r; 
requires P0(x, a, p, q, r, b, y);
requires R1(x, a, p, q, r, b, y);
ensures P0(x, a, p, q, r, b, y);
{ 
	r := x;
}


procedure P0_Stable_t3_s3()
modifies b; 
requires P0(x, a, p, q, r, b, y);
requires R2(x, a, p, q, r, b, y);
ensures P0(x, a, p, q, r, b, y);
{ 

	if (r==0)
	{
		b := 1;
	}	
}



procedure Q0_Stable_t3_s1()
modifies y; 
requires Q0(x, a, p, q, r, b, y);
requires R0(x, a, p, q, r, b, y);
ensures Q0(x, a, p, q, r, b, y);
{ 
	y := 1;
}

procedure Q0_Stable_t3_s2()
modifies r; 
requires Q0(x, a, p, q, r, b, y);
requires R1(x, a, p, q, r, b, y);
ensures Q0(x, a, p, q, r, b, y);
{ 
	r := x;
}


procedure Q0_Stable_t3_s3()
modifies b; 
requires Q0(x, a, p, q, r, b, y);
requires R2(x, a, p, q, r, b, y);
ensures Q0(x, a, p, q, r, b, y);
{ 

	if (r==0)
	{
		b := 1;
	}	
}



procedure Q1_Stable_t3_s1()
modifies y; 
requires Q1(x, a, p, q, r, b, y);
requires R0(x, a, p, q, r, b, y);
ensures Q1(x, a, p, q, r, b, y);
{ 
	y := 1;
}

procedure Q1_Stable_t3_s2()
modifies r; 
requires Q1(x, a, p, q, r, b, y);
requires R1(x, a, p, q, r, b, y);
ensures Q1(x, a, p, q, r, b, y);
{ 
	r := x;
}


procedure Q1_Stable_t3_s3()
modifies b; 
requires Q1(x, a, p, q, r, b, y);
requires R2(x, a, p, q, r, b, y);
ensures Q1(x, a, p, q, r, b, y);
{ 

	if (r==0)
	{
		b := 1;
	}	
}


procedure Q2_Stable_t3_s1()
modifies y; 
requires Q2(x, a, p, q, r, b, y);
requires R0(x, a, p, q, r, b, y);
ensures Q2(x, a, p, q, r, b, y);
{ 
	y := 1;
}

procedure Q2_Stable_t3_s2()
modifies r; 
requires Q2(x, a, p, q, r, b, y);
requires R1(x, a, p, q, r, b, y);
ensures Q2(x, a, p, q, r, b, y);
{ 
	r := x;
}


procedure Q2_Stable_t3_s3()
modifies b; 
requires Q2(x, a, p, q, r, b, y);
requires R2(x, a, p, q, r, b, y);
ensures Q2(x, a, p, q, r, b, y);
{ 

	if (r==0)
	{
		b := 1;
	}	
}


