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
								  							
    							
						
		
					Post := {x != 2 || a != 1;}



void *thread1(void * threadid)
{
int p; 
x=1;
p = y;
if (p==0)
    a=1;

}

void *thread2(void * threadid)
{
int q;
y=1;
q=x;
if (q==0)
    b=1;
}

*/

var x: int;
var y: int;
var a: int;
var p: int;
var b: int;
var q: int;


function {:existential true} {:inline} P0(x: int, a: int, p: int, b: int, q: int, y: int) : bool;
function {:existential true} {:inline} P1(x: int, a: int, p: int, b: int, q: int, y: int) : bool;
function {:existential true} {:inline} P2(x: int, a: int, p: int, b: int, q: int, y: int) : bool;
function {:existential true} {:inline} P3(x: int, a: int, p: int, b: int, q: int, y: int) : bool;
function {:existential true} {:inline} Q0(x: int, a: int, p: int, b: int, q: int, y: int) : bool;
function {:existential true} {:inline} Q1(x: int, a: int, p: int, b: int, q: int, y: int) : bool;
function {:existential true} {:inline} Q2(x: int, a: int, p: int, b: int, q: int, y: int) : bool;
function {:existential true} {:inline} Q3(x: int, a: int, p: int, b: int, q: int, y: int) : bool;

procedure pre_condition()
requires x == 0 && a == 0 && b == 0 && y == 0;
{ 
	assert P0(x, a, p, b, q, y);
  	assert Q0(x, a, p, b, q, y);
}

procedure post_condition()
requires P3(x, a, p, b, q, y);
requires Q3(x, a, p, b, q, y);
{ 
  	assert (a != 1 || b != 1);
}



procedure t1_transition_s1()
modifies x; 
requires P0(x, a, p, b, q, y);
ensures P1(x, a, p, b, q, y);
{ 
	x := 1;
}


procedure t1_transition_s2()
modifies p; 
requires P1(x, a, p, b, q, y);
ensures P2(x, a, p, b, q, y);
{ 
	p := y;
}

procedure t1_transition_s3()
modifies a; 
requires P2(x, a, p, b, q, y);
ensures P3(x, a, p, b, q, y);
{ 
	if (p == 0)
	{
		a := 1;
	}	
}

procedure t2_transition_s1()
modifies y; 
requires Q0(x, a, p, b, q, y);
ensures Q1(x, a, p, b, q, y);
{ 
	y := 1;
}

procedure t2_transition_s2()
modifies q; 
requires Q1(x, a, p, b, q, y);
ensures Q2(x, a, p, b, q, y);
{ 
	q := x;
}

procedure t2_transition_s3()
modifies b; 
requires Q2(x, a, p, b, q, y);
ensures Q3(x, a, p, b, q, y);
{ 
	if (q == 0)
	{
	    b := 1;
	}    							
}

procedure P0_Stable_t2_s1()
modifies y; 
requires P0(x, a, p, b, q, y);
requires Q0(x, a, p, b, q, y);
ensures P0(x, a, p, b, q, y);
{ 
	y := 1;
}

procedure P0_Stable_t2_s2()
modifies q; 
requires P0(x, a, p, b, q, y);
requires Q1(x, a, p, b, q, y);
ensures P0(x, a, p, b, q, y);
{ 
	q := x;
}

procedure P0_Stable_t2_s3()
modifies b; 
requires P0(x, a, p, b, q, y);
requires Q2(x, a, p, b, q, y);
ensures P0(x, a, p, b, q, y);
{ 
	if( q == 0)
	{
		b := 1;
	}
										
}

procedure P1_Stable_t2_s1()
modifies y; 
requires P1(x, a, p, b, q, y);
requires Q0(x, a, p, b, q, y);
ensures P1(x, a, p, b, q, y);
{ 
	y := 1;
}

procedure P1_Stable_t2_s2()
modifies q; 
requires P1(x, a, p, b, q, y);
requires Q1(x, a, p, b, q, y);
ensures P1(x, a, p, b, q, y);
{ 
	q := x;
}

procedure P1_Stable_t2_s3()
modifies b; 
requires P1(x, a, p, b, q, y);
requires Q2(x, a, p, b, q, y);
ensures P1(x, a, p, b, q, y);
{ 
	if(q == 0)
	{
		b := 1;
	}
										
}


procedure P2_Stable_t2_s1()
modifies y; 
requires P2(x, a, p, b, q, y);
requires Q0(x, a, p, b, q, y);
ensures P2(x, a, p, b, q, y);
{ 
	y := 1;
}

procedure P2_Stable_t2_s2()
modifies q; 
requires P2(x, a, p, b, q, y);
requires Q1(x, a, p, b, q, y);
ensures P2(x, a, p, b, q, y);
{ 
	q := x;
}

procedure P2_Stable_t2_s3()
modifies b; 
requires P2(x, a, p, b, q, y);
requires Q2(x, a, p, b, q, y);
ensures P2(x, a, p, b, q, y);
{ 
	if(q == 0)
	{
		b := 1;
	}
										
}

procedure Q0_Stable_t1_s1()
modifies x; 
requires P0(x, a, p, b, q, y);
requires Q0(x, a, p, b, q, y);
ensures Q0(x, a, p, b, q, y);
{ 
	x := 1;
}

procedure Q1_Stable_t1_s1()
modifies x; 
requires P0(x, a, p, b, q, y);
requires Q1(x, a, p, b, q, y);
ensures Q1(x, a, p, b, q, y);
{ 
	x := 1;
}

procedure Q2_Stable_t1_s1()
modifies x; 
requires P0(x, a, p, b, q, y);
requires Q2(x, a, p, b, q, y);
ensures Q2(x, a, p, b, q, y);
{ 
	x := 1;
}

procedure Q0_Stable_t1_s2()
modifies p; 
requires P1(x, a, p, b, q, y);
requires Q0(x, a, p, b, q, y);
ensures Q0(x, a, p, b, q, y);
{ 
	p := y;
}

procedure Q1_Stable_t1_s2()
modifies p; 
requires P1(x, a, p, b, q, y);
requires Q1(x, a, p, b, q, y);
ensures Q1(x, a, p, b, q, y);
{ 
	p := y;
}

procedure Q2_Stable_t1_s2()
modifies p; 
requires P1(x, a, p, b, q, y);
requires Q2(x, a, p, b, q, y);
ensures Q2(x, a, p, b, q, y);
{ 
	p := y;
}


procedure Q0_Stable_t1_s3()
modifies a; 
requires P2(x, a, p, b, q, y);
requires Q0(x, a, p, b, q, y);
ensures Q0(x, a, p, b, q, y);
{ 
	if (p==0)
	{
		a := 1;
	}
}

procedure Q1_Stable_t1_s3()
modifies a; 
requires P2(x, a, p, b, q, y);
requires Q1(x, a, p, b, q, y);
ensures Q1(x, a, p, b, q, y);
{ 
	if (p==0)
	{
		a := 1;
	}
}

procedure Q2_Stable_t1_s3()
modifies a; 
requires P2(x, a, p, b, q, y);
requires Q2(x, a, p, b, q, y);
ensures Q2(x, a, p, b, q, y);
{ 
	if (p==0)
	{
		a := 1;
	}
}
/**/
