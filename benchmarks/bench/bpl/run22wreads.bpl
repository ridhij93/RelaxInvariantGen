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
x=2;
P1
y=1;
P2



Q0
y=2;
Q1
x=1;
Q2

R0
p = x;
R1
q = x;
R2
if(p==1 && q==2)
    a=1;
R3


S0
r = y;
S1
s = y;
S2
if (r==1 && s==2)
    b=1;
S3



  assert (a != 1 || b != 1);

*/

var x: int;
var y: int;
var a: int;
var p: int;
var q: int;
var r: int;
var s: int;
var b: int;



function {:existential true} {:inline} P0(x: int, a: int, p: int, q: int, r: int, s: int, b: int, y: int) : bool;
function {:existential true} {:inline} P1(x: int, a: int, p: int, q: int, r: int, s: int, b: int, y: int) : bool;
function {:existential true} {:inline} P2(x: int, a: int, p: int, q: int, r: int, s: int, b: int, y: int) : bool;


function {:existential true} {:inline} Q0(x: int, a: int, p: int, q: int, r: int, s: int, b: int, y: int) : bool;
function {:existential true} {:inline} Q1(x: int, a: int, p: int, q: int, r: int, s: int, b: int, y: int) : bool;
function {:existential true} {:inline} Q2(x: int, a: int, p: int, q: int, r: int, s: int, b: int, y: int) : bool;
function {:existential true} {:inline} Q3(x: int, a: int, p: int, q: int, r: int, s: int, b: int, y: int) : bool;

function {:existential true} {:inline} R0(x: int, a: int, p: int, q: int, r: int, s: int, b: int, y: int) : bool;
function {:existential true} {:inline} R1(x: int, a: int, p: int, q: int, r: int, s: int, b: int, y: int) : bool;
function {:existential true} {:inline} R2(x: int, a: int, p: int, q: int, r: int, s: int, b: int, y: int) : bool;
function {:existential true} {:inline} R3(x: int, a: int, p: int, q: int, r: int, s: int, b: int, y: int) : bool;

function {:existential true} {:inline} S0(x: int, a: int, p: int, q: int, r: int, s: int, b: int, y: int) : bool;
function {:existential true} {:inline} S1(x: int, a: int, p: int, q: int, r: int, s: int, b: int, y: int) : bool;
function {:existential true} {:inline} S2(x: int, a: int, p: int, q: int, r: int, s: int, b: int, y: int) : bool;
function {:existential true} {:inline} S3(x: int, a: int, p: int, q: int, r: int, s: int, b: int, y: int) : bool;


procedure pre_condition()
requires x == 0 && a == 0 && b == 0 && y == 0;
{ 
	assert P0(x, a, p, q, r, s, b, y);
  	assert Q0(x, a, p, q, r, s, b, y);
  	assert R0(x, a, p, q, r, s, b, y);
  	assert S0(x, a, p, q, r, s, b, y);
}

procedure post_condition()
requires P2(x, a, p, q, r, s, b, y);
requires Q2(x, a, p, q, r, s, b, y);
requires R3(x, a, p, q, r, s, b, y);
requires S3(x, a, p, q, r, s, b, y);
{ 
  	assert ( a != 1 || b != 1 );
}



procedure t1_transition_s1()
modifies x; 
requires P0(x, a, p, q, r, s, b, y);
ensures P1(x, a, p, q, r, s, b, y);
{ 
	x := 2;
}

procedure t1_transition_s2()
modifies y; 
requires P1(x, a, p, q, r, s, b, y);
ensures P2(x, a, p, q, r, s, b, y);
{ 
	y := 1;
}


procedure t2_transition_s1()
modifies y; 
requires Q0(x, a, p, q, r, s, b, y);
ensures Q1(x, a, p, q, r, s, b, y);
{ 
	y := 2;
}

procedure t2_transition_s2()
modifies x; 
requires Q1(x, a, p, q, r, s, b, y);
ensures Q2(x, a, p, q, r, s, b, y);
{ 
	x := 1;
}



procedure t3_transition_s1()
modifies p; 
requires R0(x, a, p, q, r, s, b, y);
ensures R1(x, a, p, q, r, s, b, y);
{ 
	p := x;
}

procedure t3_transition_s2()
modifies q; 
requires R1(x, a, p, q, r, s, b, y);
ensures R2(x, a, p, q, r, s, b, y);
{ 
	q := x;
}

procedure t3_transition_s3()
modifies a; 
requires R2(x, a, p, q, r, s, b, y);
ensures R3(x, a, p, q, r, s, b, y);
{ 
	if(p==1 && q==2)
    	{
    		a := 1;
    	}	
}


procedure t4_transition_s1()
modifies r; 
requires S0(x, a, p, q, r, s, b, y);
ensures S1(x, a, p, q, r, s, b, y);
{ 
	r := y;
}

procedure t4_transition_s2()
modifies s; 
requires S1(x, a, p, q, r, s, b, y);
ensures S2(x, a, p, q, r, s, b, y);
{ 
	s := y;
}

procedure t4_transition_s3()
modifies b; 
requires S2(x, a, p, q, r, s, b, y);
ensures S3(x, a, p, q, r, s, b, y);
{ 
	if(r==1 && s==2)
    	{
    		b := 1;
    	}	
}


procedure P0_Stable_t2_s1()
modifies y; 
requires P0(x, a, p, q, r, s, b, y);
requires Q0(x, a, p, q, r, s, b, y);
ensures P0(x, a, p, q, r, s, b, y);
{ 
	y := 2;
}


procedure P0_Stable_t2_s2()
modifies x; 
requires P0(x, a, p, q, r, s, b, y);
requires Q1(x, a, p, q, r, s, b, y);
ensures P0(x, a, p, q, r, s, b, y);
{ 
	x := 1;
}


procedure P1_Stable_t2_s1()
modifies y; 
requires P1(x, a, p, q, r, s, b, y);
requires Q0(x, a, p, q, r, s, b, y);
ensures P1(x, a, p, q, r, s, b, y);
{ 
	y := 2;
}


procedure P1_Stable_t2_s2()
modifies x; 
requires P1(x, a, p, q, r, s, b, y);
requires Q1(x, a, p, q, r, s, b, y);
ensures P1(x, a, p, q, r, s, b, y);
{ 
	x := 1;
}

procedure R0_Stable_t2_s1()
modifies y; 
requires R0(x, a, p, q, r, s, b, y);
requires Q0(x, a, p, q, r, s, b, y);
ensures R0(x, a, p, q, r, s, b, y);
{ 
	y := 2;
}


procedure R0_Stable_t2_s2()
modifies x; 
requires R0(x, a, p, q, r, s, b, y);
requires Q1(x, a, p, q, r, s, b, y);
ensures R0(x, a, p, q, r, s, b, y);
{ 
	x := 1;
}

procedure R1_Stable_t2_s1()
modifies y; 
requires R1(x, a, p, q, r, s, b, y);
requires Q0(x, a, p, q, r, s, b, y);
ensures R1(x, a, p, q, r, s, b, y);
{ 
	y := 2;
}


procedure R1_Stable_t2_s2()
modifies x; 
requires R1(x, a, p, q, r, s, b, y);
requires Q1(x, a, p, q, r, s, b, y);
ensures R1(x, a, p, q, r, s, b, y);
{ 
	x := 1;
}


procedure R2_Stable_t2_s1()
modifies y; 
requires R2(x, a, p, q, r, s, b, y);
requires Q0(x, a, p, q, r, s, b, y);
ensures R2(x, a, p, q, r, s, b, y);
{ 
	y := 2;
}


procedure R2_Stable_t2_s2()
modifies x; 
requires R2(x, a, p, q, r, s, b, y);
requires Q1(x, a, p, q, r, s, b, y);
ensures R2(x, a, p, q, r, s, b, y);
{ 
	x := 1;
}




procedure S0_Stable_t2_s1()
modifies y; 
requires S0(x, a, p, q, r, s, b, y);
requires Q0(x, a, p, q, r, s, b, y);
ensures S0(x, a, p, q, r, s, b, y);
{ 
	y := 2;
}


procedure S0_Stable_t2_s2()
modifies x; 
requires S0(x, a, p, q, r, s, b, y);
requires Q1(x, a, p, q, r, s, b, y);
ensures S0(x, a, p, q, r, s, b, y);
{ 
	x := 1;
}

procedure S1_Stable_t2_s1()
modifies y; 
requires S1(x, a, p, q, r, s, b, y);
requires Q0(x, a, p, q, r, s, b, y);
ensures S1(x, a, p, q, r, s, b, y);
{ 
	y := 2;
}


procedure S1_Stable_t2_s2()
modifies x; 
requires S1(x, a, p, q, r, s, b, y);
requires Q1(x, a, p, q, r, s, b, y);
ensures S1(x, a, p, q, r, s, b, y);
{ 
	x := 1;
}


procedure S2_Stable_t2_s1()
modifies y; 
requires S2(x, a, p, q, r, s, b, y);
requires Q0(x, a, p, q, r, s, b, y);
ensures S2(x, a, p, q, r, s, b, y);
{ 
	y := 2;
}


procedure S2_Stable_t2_s2()
modifies x; 
requires S2(x, a, p, q, r, s, b, y);
requires Q1(x, a, p, q, r, s, b, y);
ensures S2(x, a, p, q, r, s, b, y);
{ 
	x := 1;
}


procedure Q0_Stable_t1_s1()
modifies x; 
requires Q0(x, a, p, q, r, s, b, y);
requires P0(x, a, p, q, r, s, b, y);
ensures Q0(x, a, p, q, r, s, b, y);
{ 
	x := 2;
}

procedure Q0_Stable_t1_s2()
modifies y; 
requires Q0(x, a, p, q, r, s, b, y);
requires P1(x, a, p, q, r, s, b, y);
ensures Q0(x, a, p, q, r, s, b, y);
{ 
	y := 1;
}


procedure Q1_Stable_t1_s1()
modifies x; 
requires Q1(x, a, p, q, r, s, b, y);
requires P0(x, a, p, q, r, s, b, y);
ensures Q1(x, a, p, q, r, s, b, y);
{ 
	x := 2;
}

procedure Q1_Stable_t1_s2()
modifies y; 
requires Q1(x, a, p, q, r, s, b, y);
requires P1(x, a, p, q, r, s, b, y);
ensures Q1(x, a, p, q, r, s, b, y);
{ 
	y := 1;
}

procedure Q2_Stable_t1_s1()
modifies x; 
requires Q2(x, a, p, q, r, s, b, y);
requires P0(x, a, p, q, r, s, b, y);
ensures Q2(x, a, p, q, r, s, b, y);
{ 
	x := 2;
}

procedure Q2_Stable_t1_s2()
modifies y; 
requires Q2(x, a, p, q, r, s, b, y);
requires P1(x, a, p, q, r, s, b, y);
ensures Q2(x, a, p, q, r, s, b, y);
{ 
	y := 1;
}

procedure R0_Stable_t1_s1()
modifies x; 
requires R0(x, a, p, q, r, s, b, y);
requires P0(x, a, p, q, r, s, b, y);
ensures R0(x, a, p, q, r, s, b, y);
{ 
	x := 2;
}

procedure R0_Stable_t1_s2()
modifies y; 
requires R0(x, a, p, q, r, s, b, y);
requires P1(x, a, p, q, r, s, b, y);
ensures R0(x, a, p, q, r, s, b, y);
{ 
	y := 1;
}

procedure R1_Stable_t1_s1()
modifies x; 
requires R1(x, a, p, q, r, s, b, y);
requires P0(x, a, p, q, r, s, b, y);
ensures R1(x, a, p, q, r, s, b, y);
{ 
	x := 2;
}

procedure R1_Stable_t1_s2()
modifies y; 
requires R1(x, a, p, q, r, s, b, y);
requires P1(x, a, p, q, r, s, b, y);
ensures R1(x, a, p, q, r, s, b, y);
{ 
	y := 1;
}

procedure R2_Stable_t1_s1()
modifies x; 
requires R2(x, a, p, q, r, s, b, y);
requires P0(x, a, p, q, r, s, b, y);
ensures R2(x, a, p, q, r, s, b, y);
{ 
	x := 2;
}

procedure R2_Stable_t1_s2()
modifies y; 
requires R2(x, a, p, q, r, s, b, y);
requires P1(x, a, p, q, r, s, b, y);
ensures R2(x, a, p, q, r, s, b, y);
{ 
	y := 1;
}

procedure S0_Stable_t1_s1()
modifies x; 
requires S0(x, a, p, q, r, s, b, y);
requires P0(x, a, p, q, r, s, b, y);
ensures S0(x, a, p, q, r, s, b, y);
{ 
	x := 2;
}

procedure S0_Stable_t1_s2()
modifies y; 
requires S0(x, a, p, q, r, s, b, y);
requires P1(x, a, p, q, r, s, b, y);
ensures S0(x, a, p, q, r, s, b, y);
{ 
	y := 1;
}

procedure S1_Stable_t1_s1()
modifies x; 
requires S1(x, a, p, q, r, s, b, y);
requires P0(x, a, p, q, r, s, b, y);
ensures S1(x, a, p, q, r, s, b, y);
{ 
	x := 2;
}

procedure S1_Stable_t1_s2()
modifies y; 
requires S1(x, a, p, q, r, s, b, y);
requires P1(x, a, p, q, r, s, b, y);
ensures S1(x, a, p, q, r, s, b, y);
{ 
	y := 1;
}

procedure S2_Stable_t1_s1()
modifies x; 
requires S2(x, a, p, q, r, s, b, y);
requires P0(x, a, p, q, r, s, b, y);
ensures S2(x, a, p, q, r, s, b, y);
{ 
	x := 2;
}

procedure S2_Stable_t1_s2()
modifies y; 
requires S2(x, a, p, q, r, s, b, y);
requires P1(x, a, p, q, r, s, b, y);
ensures S2(x, a, p, q, r, s, b, y);
{ 
	y := 1;
}

procedure P0_Stable_t3_s1()
modifies p; 
requires P0(x, a, p, q, r, s, b, y);
requires R0(x, a, p, q, r, s, b, y);
ensures P0(x, a, p, q, r, s, b, y);
{ 
	p := x;
}


procedure P0_Stable_t3_s2()
modifies q; 
requires P0(x, a, p, q, r, s, b, y);
requires R1(x, a, p, q, r, s, b, y);
ensures P0(x, a, p, q, r, s, b, y);
{ 
	q := x;
}

procedure P0_Stable_t3_s3()
modifies a; 
requires P0(x, a, p, q, r, s, b, y);
requires R2(x, a, p, q, r, s, b, y);
ensures P0(x, a, p, q, r, s, b, y);
{ 
	if(p==1 && q==2)
    	{
    		a := 1;
    	}
}

procedure P1_Stable_t3_s1()
modifies p; 
requires P1(x, a, p, q, r, s, b, y);
requires R0(x, a, p, q, r, s, b, y);
ensures P1(x, a, p, q, r, s, b, y);
{ 
	p := x;
}


procedure P1_Stable_t3_s2()
modifies q; 
requires P1(x, a, p, q, r, s, b, y);
requires R1(x, a, p, q, r, s, b, y);
ensures P1(x, a, p, q, r, s, b, y);
{ 
	q := x;
}

procedure P1_Stable_t3_s3()
modifies a; 
requires P1(x, a, p, q, r, s, b, y);
requires R2(x, a, p, q, r, s, b, y);
ensures P1(x, a, p, q, r, s, b, y);
{ 
	if(p==1 && q==2)
    	{
    		a := 1;
    	}
}







procedure Q0_Stable_t3_s1()
modifies p; 
requires Q0(x, a, p, q, r, s, b, y);
requires R0(x, a, p, q, r, s, b, y);
ensures Q0(x, a, p, q, r, s, b, y);
{ 
	p := x;
}


procedure Q0_Stable_t3_s2()
modifies q; 
requires Q0(x, a, p, q, r, s, b, y);
requires R1(x, a, p, q, r, s, b, y);
ensures Q0(x, a, p, q, r, s, b, y);
{ 
	q := x;
}

procedure Q0_Stable_t3_s3()
modifies a; 
requires Q0(x, a, p, q, r, s, b, y);
requires R2(x, a, p, q, r, s, b, y);
ensures Q0(x, a, p, q, r, s, b, y);
{ 
	if(p==1 && q==2)
    	{
    		a := 1;
    	}
}

procedure Q1_Stable_t3_s1()
modifies p; 
requires Q1(x, a, p, q, r, s, b, y);
requires R0(x, a, p, q, r, s, b, y);
ensures Q1(x, a, p, q, r, s, b, y);
{ 
	p := x;
}


procedure Q1_Stable_t3_s2()
modifies q; 
requires Q1(x, a, p, q, r, s, b, y);
requires R1(x, a, p, q, r, s, b, y);
ensures Q1(x, a, p, q, r, s, b, y);
{ 
	q := x;
}

procedure Q1_Stable_t3_s3()
modifies a; 
requires Q1(x, a, p, q, r, s, b, y);
requires R2(x, a, p, q, r, s, b, y);
ensures Q1(x, a, p, q, r, s, b, y);
{ 
	if(p==1 && q==2)
    	{
    		a := 1;
    	}
}


procedure S0_Stable_t3_s1()
modifies p; 
requires S0(x, a, p, q, r, s, b, y);
requires R0(x, a, p, q, r, s, b, y);
ensures S0(x, a, p, q, r, s, b, y);
{ 
	p := x;
}


procedure S0_Stable_t3_s2()
modifies q; 
requires S0(x, a, p, q, r, s, b, y);
requires R1(x, a, p, q, r, s, b, y);
ensures S0(x, a, p, q, r, s, b, y);
{ 
	q := x;
}

procedure S0_Stable_t3_s3()
modifies a; 
requires S0(x, a, p, q, r, s, b, y);
requires R2(x, a, p, q, r, s, b, y);
ensures S0(x, a, p, q, r, s, b, y);
{ 
	if(p==1 && q==2)
    	{
    		a := 1;
    	}
}


procedure S1_Stable_t3_s1()
modifies p; 
requires S1(x, a, p, q, r, s, b, y);
requires R0(x, a, p, q, r, s, b, y);
ensures S1(x, a, p, q, r, s, b, y);
{ 
	p := x;
}


procedure S1_Stable_t3_s2()
modifies q; 
requires S1(x, a, p, q, r, s, b, y);
requires R1(x, a, p, q, r, s, b, y);
ensures S1(x, a, p, q, r, s, b, y);
{ 
	q := x;
}

procedure S1_Stable_t3_s3()
modifies a; 
requires S1(x, a, p, q, r, s, b, y);
requires R2(x, a, p, q, r, s, b, y);
ensures S1(x, a, p, q, r, s, b, y);
{ 
	if(p==1 && q==2)
    	{
    		a := 1;
    	}
}


procedure S2_Stable_t3_s1()
modifies p; 
requires S2(x, a, p, q, r, s, b, y);
requires R0(x, a, p, q, r, s, b, y);
ensures S2(x, a, p, q, r, s, b, y);
{ 
	p := x;
}


procedure S2_Stable_t3_s2()
modifies q; 
requires S2(x, a, p, q, r, s, b, y);
requires R1(x, a, p, q, r, s, b, y);
ensures S2(x, a, p, q, r, s, b, y);
{ 
	q := x;
}

procedure S2_Stable_t3_s3()
modifies a; 
requires S2(x, a, p, q, r, s, b, y);
requires R2(x, a, p, q, r, s, b, y);
ensures S2(x, a, p, q, r, s, b, y);
{ 
	if(p==1 && q==2)
    	{
    		a := 1;
    	}
}


procedure P0_Stable_t4_s1()
modifies r; 
requires P0(x, a, p, q, r, s, b, y);
requires S0(x, a, p, q, r, s, b, y);
ensures P0(x, a, p, q, r, s, b, y);
{ 
	r := y;
}


procedure P0_Stable_t4_s2()
modifies s; 
requires P0(x, a, p, q, r, s, b, y);
requires S1(x, a, p, q, r, s, b, y);
ensures P0(x, a, p, q, r, s, b, y);
{ 
	s := y;
}

procedure P0_Stable_t4_s3()
modifies b; 
requires P0(x, a, p, q, r, s, b, y);
requires S2(x, a, p, q, r, s, b, y);
ensures P0(x, a, p, q, r, s, b, y);
{ 
	if(r==1 && s==2)
    	{
    		b := 1;
    	}
}

procedure P1_Stable_t4_s1()
modifies r; 
requires P1(x, a, p, q, r, s, b, y);
requires S0(x, a, p, q, r, s, b, y);
ensures P1(x, a, p, q, r, s, b, y);
{ 
	r := y;
}


procedure P1_Stable_t4_s2()
modifies s; 
requires P1(x, a, p, q, r, s, b, y);
requires S1(x, a, p, q, r, s, b, y);
ensures P1(x, a, p, q, r, s, b, y);
{ 
	s := y;
}

procedure P1_Stable_t4_s3()
modifies b; 
requires P1(x, a, p, q, r, s, b, y);
requires S2(x, a, p, q, r, s, b, y);
ensures P1(x, a, p, q, r, s, b, y);
{ 
	if(r==1 && s==2)
    	{
    		b := 1;
    	}
}







procedure Q0_Stable_t4_s1()
modifies r; 
requires Q0(x, a, p, q, r, s, b, y);
requires S0(x, a, p, q, r, s, b, y);
ensures Q0(x, a, p, q, r, s, b, y);
{ 
	r := y;
}


procedure Q0_Stable_t4_s2()
modifies s; 
requires Q0(x, a, p, q, r, s, b, y);
requires S1(x, a, p, q, r, s, b, y);
ensures Q0(x, a, p, q, r, s, b, y);
{ 
	s := y;
}

procedure Q0_Stable_t4_s3()
modifies b; 
requires Q0(x, a, p, q, r, s, b, y);
requires S2(x, a, p, q, r, s, b, y);
ensures Q0(x, a, p, q, r, s, b, y);
{ 
	if(r==1 && s==2)
    	{
    		b := 1;
    	}
}

procedure Q1_Stable_t4_s1()
modifies r; 
requires Q1(x, a, p, q, r, s, b, y);
requires S0(x, a, p, q, r, s, b, y);
ensures Q1(x, a, p, q, r, s, b, y);
{ 
	r := y;
}


procedure Q1_Stable_t4_s2()
modifies s; 
requires Q1(x, a, p, q, r, s, b, y);
requires S1(x, a, p, q, r, s, b, y);
ensures Q1(x, a, p, q, r, s, b, y);
{ 
	s := y;
}

procedure Q1_Stable_t4_s3()
modifies b; 
requires Q1(x, a, p, q, r, s, b, y);
requires S2(x, a, p, q, r, s, b, y);
ensures Q1(x, a, p, q, r, s, b, y);
{ 
	if(r==1 && s==2)
    	{
    		b := 1;
    	}
}


procedure R0_Stable_t4_s1()
modifies r; 
requires R0(x, a, p, q, r, s, b, y);
requires S0(x, a, p, q, r, s, b, y);
ensures R0(x, a, p, q, r, s, b, y);
{ 
	r := y;
}


procedure R0_Stable_t4_s2()
modifies s; 
requires R0(x, a, p, q, r, s, b, y);
requires S1(x, a, p, q, r, s, b, y);
ensures R0(x, a, p, q, r, s, b, y);
{ 
	s := y;
}

procedure R0_Stable_t4_s3()
modifies b; 
requires R0(x, a, p, q, r, s, b, y);
requires S2(x, a, p, q, r, s, b, y);
ensures R0(x, a, p, q, r, s, b, y);
{ 
	if(r==1 && s==2)
    	{
    		b := 1;
    	}
}


procedure R1_Stable_t4_s1()
modifies r; 
requires R1(x, a, p, q, r, s, b, y);
requires S0(x, a, p, q, r, s, b, y);
ensures R1(x, a, p, q, r, s, b, y);
{ 
	r := y;
}


procedure R1_Stable_t4_s2()
modifies s; 
requires R1(x, a, p, q, r, s, b, y);
requires S1(x, a, p, q, r, s, b, y);
ensures R1(x, a, p, q, r, s, b, y);
{ 
	s := y;
}

procedure R1_Stable_t4_s3()
modifies b; 
requires R1(x, a, p, q, r, s, b, y);
requires S2(x, a, p, q, r, s, b, y);
ensures R1(x, a, p, q, r, s, b, y);
{ 
	if(r==1 && s==2)
    	{
    		b := 1;
    	}
}


procedure R2_Stable_t4_s1()
modifies r; 
requires R2(x, a, p, q, r, s, b, y);
requires S0(x, a, p, q, r, s, b, y);
ensures R2(x, a, p, q, r, s, b, y);
{ 
	r := y;
}


procedure R2_Stable_t4_s2()
modifies s; 
requires R2(x, a, p, q, r, s, b, y);
requires S1(x, a, p, q, r, s, b, y);
ensures R2(x, a, p, q, r, s, b, y);
{ 
	s := y;
}

procedure R2_Stable_t4_s3()
modifies b; 
requires R2(x, a, p, q, r, s, b, y);
requires S2(x, a, p, q, r, s, b, y);
ensures R2(x, a, p, q, r, s, b, y);
{ 
	if(r==1 && s==2)
    	{
    		b := 1;
    	}
}
