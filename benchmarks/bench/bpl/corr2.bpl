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




P0
    x = 1;
P1


Q0
    x = 2;
Q1

R0
    p = x;
R1    
    q = x;
R2    
    if (p==1 && q==2)
	a = 1;
R3	
    if (p==2 && q==1)
        a = 2;
R4


S0
    r = x;
S1    
    s = x;
S2    
    if (r==2 && s==1)
	b = 1;
S3	
    if (r==1 && s==2)
        b = 2;
S4


  assert ( ( a != 1 || b != 1) && (a != 2 || b != 2));


	
*/

var x: int;
var a: int;
var p: int;
var q: int;
var r: int;
var s: int;
var b: int;



function {:existential true} {:inline} P0(x: int, a: int, p: int, q: int, r: int, s: int, b: int) : bool;
function {:existential true} {:inline} P1(x: int, a: int, p: int, q: int, r: int, s: int, b: int) : bool;



function {:existential true} {:inline} Q0(x: int, a: int, p: int, q: int, r: int, s: int, b: int) : bool;
function {:existential true} {:inline} Q1(x: int, a: int, p: int, q: int, r: int, s: int, b: int) : bool;

function {:existential true} {:inline} R0(x: int, a: int, p: int, q: int, r: int, s: int, b: int) : bool;
function {:existential true} {:inline} R1(x: int, a: int, p: int, q: int, r: int, s: int, b: int) : bool;
function {:existential true} {:inline} R2(x: int, a: int, p: int, q: int, r: int, s: int, b: int) : bool;
function {:existential true} {:inline} R3(x: int, a: int, p: int, q: int, r: int, s: int, b: int) : bool;
function {:existential true} {:inline} R4(x: int, a: int, p: int, q: int, r: int, s: int, b: int) : bool;

function {:existential true} {:inline} S0(x: int, a: int, p: int, q: int, r: int, s: int, b: int) : bool;
function {:existential true} {:inline} S1(x: int, a: int, p: int, q: int, r: int, s: int, b: int) : bool;
function {:existential true} {:inline} S2(x: int, a: int, p: int, q: int, r: int, s: int, b: int) : bool;
function {:existential true} {:inline} S3(x: int, a: int, p: int, q: int, r: int, s: int, b: int) : bool;
function {:existential true} {:inline} S4(x: int, a: int, p: int, q: int, r: int, s: int, b: int) : bool;

procedure pre_condition()
requires x == 0 && a == 0 && b == 0 ;
{ 
	assert P0(x, a, p, q, r, s, b);
  	assert Q0(x, a, p, q, r, s, b);
  	assert R0(x, a, p, q, r, s, b);
  	assert S0(x, a, p, q, r, s, b);
}

procedure post_condition()
requires P1(x, a, p, q, r, s, b);
requires Q1(x, a, p, q, r, s, b);
requires R4(x, a, p, q, r, s, b);
requires S4(x, a, p, q, r, s, b);
{ 
  	assert ( ( a != 1 || b != 1) && (a != 2 || b != 2));
}



procedure t1_transition_s1()
modifies x; 
requires P0(x, a, p, q, r, s, b);
ensures P1(x, a, p, q, r, s, b);
{ 
	x := 1;
}





procedure t2_transition_s1()
modifies x; 
requires Q0(x, a, p, q, r, s, b);
ensures Q1(x, a, p, q, r, s, b);
{ 
	x := 2;
}

procedure t3_transition_s1()
modifies p; 
requires R0(x, a, p, q, r, s, b);
ensures R1(x, a, p, q, r, s, b);
{ 
	p := x;							
}

procedure t3_transition_s2()
modifies q; 
requires R1(x, a, p, q, r, s, b);
ensures R2(x, a, p, q, r, s, b);
{ 
	q := x;							
}

procedure t3_transition_s3()
modifies a; 
requires R2(x, a, p, q, r, s, b);
ensures R3(x, a, p, q, r, s, b);
{ 
	if (p==1 && q==2)
	{
		a := 1;	
	}							
}


procedure t3_transition_s4()
modifies a; 
requires R3(x, a, p, q, r, s, b);
ensures R4(x, a, p, q, r, s, b);
{ 
	if (p==2 && q==1)
	{
		a := 2;	
	}							
}


procedure t4_transition_s1()
modifies r; 
requires S0(x, a, p, q, r, s, b);
ensures S1(x, a, p, q, r, s, b);
{ 
	r := x;							
}

procedure t4_transition_s2()
modifies s; 
requires S1(x, a, p, q, r, s, b);
ensures S2(x, a, p, q, r, s, b);
{ 
	s := x;							
}

procedure t4_transition_s3()
modifies b; 
requires S2(x, a, p, q, r, s, b);
ensures S3(x, a, p, q, r, s, b);
{ 
	if (r==2 && s==1)
	{
		b := 1;	
	}							
}


procedure t4_transition_s4()
modifies b; 
requires S3(x, a, p, q, r, s, b);
ensures S4(x, a, p, q, r, s, b);
{ 
	if (r==1 && s==2)
	{
		b := 2;	
	}							
}


procedure P0_Stable_t2_s1()
modifies x; 
requires P0(x, a, p, q, r, s, b);
requires Q0(x, a, p, q, r, s, b);
ensures P0(x, a, p, q, r, s, b);
{ 
	x := 2;
}

procedure R0_Stable_t2_s1()
modifies x; 
requires R0(x, a, p, q, r, s, b);
requires Q0(x, a, p, q, r, s, b);
ensures R0(x, a, p, q, r, s, b);
{ 
	x := 2;
}

procedure R1_Stable_t2_s1()
modifies x; 
requires R1(x, a, p, q, r, s, b);
requires Q0(x, a, p, q, r, s, b);
ensures R1(x, a, p, q, r, s, b);
{ 
	x := 2;
}

procedure R2_Stable_t2_s1()
modifies x; 
requires R2(x, a, p, q, r, s, b);
requires Q0(x, a, p, q, r, s, b);
ensures R2(x, a, p, q, r, s, b);
{ 
	x := 2;
}

procedure R3_Stable_t2_s1()
modifies x; 
requires R3(x, a, p, q, r, s, b);
requires Q0(x, a, p, q, r, s, b);
ensures R3(x, a, p, q, r, s, b);
{ 
	x := 2;
}


procedure S0_Stable_t2_s1()
modifies x; 
requires S0(x, a, p, q, r, s, b);
requires Q0(x, a, p, q, r, s, b);
ensures S0(x, a, p, q, r, s, b);
{ 
	x := 2;
}

procedure S1_Stable_t2_s1()
modifies x; 
requires S1(x, a, p, q, r, s, b);
requires Q0(x, a, p, q, r, s, b);
ensures S1(x, a, p, q, r, s, b);
{ 
	x := 2;
}

procedure S2_Stable_t2_s1()
modifies x; 
requires S2(x, a, p, q, r, s, b);
requires Q0(x, a, p, q, r, s, b);
ensures S2(x, a, p, q, r, s, b);
{ 
	x := 2;
}

procedure S3_Stable_t2_s1()
modifies x; 
requires S3(x, a, p, q, r, s, b);
requires Q0(x, a, p, q, r, s, b);
ensures S3(x, a, p, q, r, s, b);
{ 
	x := 2;
}


procedure Q0_Stable_t1_s1()
modifies x; 
requires P0(x, a, p, q, r, s, b);
requires Q0(x, a, p, q, r, s, b);
ensures Q0(x, a, p, q, r, s, b);
{ 
	x := 1;
}


procedure R0_Stable_t1_s1()
modifies x; 
requires P0(x, a, p, q, r, s, b);
requires R0(x, a, p, q, r, s, b);
ensures R0(x, a, p, q, r, s, b);
{ 
	x := 1;
}

procedure R1_Stable_t1_s1()
modifies x; 
requires P0(x, a, p, q, r, s, b);
requires R1(x, a, p, q, r, s, b);
ensures R1(x, a, p, q, r, s, b);
{ 
	x := 1;
}

procedure R2_Stable_t1_s1()
modifies x; 
requires P0(x, a, p, q, r, s, b);
requires R2(x, a, p, q, r, s, b);
ensures R2(x, a, p, q, r, s, b);
{ 
	x := 1;
}

procedure R3_Stable_t1_s1()
modifies x; 
requires P0(x, a, p, q, r, s, b);
requires R3(x, a, p, q, r, s, b);
ensures R3(x, a, p, q, r, s, b);
{ 
	x := 1;
}

procedure S0_Stable_t1_s1()
modifies x; 
requires P0(x, a, p, q, r, s, b);
requires S0(x, a, p, q, r, s, b);
ensures S0(x, a, p, q, r, s, b);
{ 
	x := 1;
}

procedure S1_Stable_t1_s1()
modifies x; 
requires P0(x, a, p, q, r, s, b);
requires S1(x, a, p, q, r, s, b);
ensures S1(x, a, p, q, r, s, b);
{ 
	x := 1;
}

procedure S2_Stable_t1_s1()
modifies x; 
requires P0(x, a, p, q, r, s, b);
requires S2(x, a, p, q, r, s, b);
ensures S2(x, a, p, q, r, s, b);
{ 
	x := 1;
}

procedure S3_Stable_t1_s1()
modifies x; 
requires P0(x, a, p, q, r, s, b);
requires S3(x, a, p, q, r, s, b);
ensures S3(x, a, p, q, r, s, b);
{ 
	x := 1;
}

procedure P0_Stable_t3_s1()
modifies p; 
requires P0(x, a, p, q, r, s, b);
requires R0(x, a, p, q, r, s, b);
ensures P0(x, a, p, q, r, s, b);
{ 
	p := x;
}

procedure P0_Stable_t3_s2()
modifies q; 
requires P0(x, a, p, q, r, s, b);
requires R1(x, a, p, q, r, s, b);
ensures P0(x, a, p, q, r, s, b);
{ 
	q := x;
}

procedure P0_Stable_t3_s3()
modifies a; 
requires P0(x, a, p, q, r, s, b);
requires R3(x, a, p, q, r, s, b);
ensures P0(x, a, p, q, r, s, b);
{ 
	if (p==1 && q==2)
	{
		a := 1;
	}	
}

procedure P0_Stable_t3_s4()
modifies a; 
requires P0(x, a, p, q, r, s, b);
requires R4(x, a, p, q, r, s, b);
ensures P0(x, a, p, q, r, s, b);
{ 
	if (p==2 && q==1)
	{
		a := 2;
	}	
}


procedure Q0_Stable_t3_s1()
modifies p; 
requires Q0(x, a, p, q, r, s, b);
requires R0(x, a, p, q, r, s, b);
ensures Q0(x, a, p, q, r, s, b);
{ 
	p := x;
}

procedure Q0_Stable_t3_s2()
modifies q; 
requires Q0(x, a, p, q, r, s, b);
requires R1(x, a, p, q, r, s, b);
ensures Q0(x, a, p, q, r, s, b);
{ 
	q := x;
}

procedure Q0_Stable_t3_s3()
modifies a; 
requires Q0(x, a, p, q, r, s, b);
requires R3(x, a, p, q, r, s, b);
ensures Q0(x, a, p, q, r, s, b);
{ 
	if (p==1 && q==2)
	{
		a := 1;
	}	
}

procedure Q0_Stable_t3_s4()
modifies a; 
requires Q0(x, a, p, q, r, s, b);
requires R4(x, a, p, q, r, s, b);
ensures Q0(x, a, p, q, r, s, b);
{ 
	if (p==2 && q==1)
	{
		a := 2;
	}	
}




procedure S0_Stable_t3_s1()
modifies p; 
requires S0(x, a, p, q, r, s, b);
requires R0(x, a, p, q, r, s, b);
ensures S0(x, a, p, q, r, s, b);
{ 
	p := x;
}

procedure S0_Stable_t3_s2()
modifies q; 
requires S0(x, a, p, q, r, s, b);
requires R1(x, a, p, q, r, s, b);
ensures S0(x, a, p, q, r, s, b);
{ 
	q := x;
}

procedure S0_Stable_t3_s3()
modifies a; 
requires S0(x, a, p, q, r, s, b);
requires R3(x, a, p, q, r, s, b);
ensures S0(x, a, p, q, r, s, b);
{ 
	if (p==1 && q==2)
	{
		a := 1;
	}	
}

procedure S0_Stable_t3_s4()
modifies a; 
requires S0(x, a, p, q, r, s, b);
requires R4(x, a, p, q, r, s, b);
ensures S0(x, a, p, q, r, s, b);
{ 
	if (p==2 && q==1)
	{
		a := 2;
	}	
}


procedure S1_Stable_t3_s1()
modifies p; 
requires S1(x, a, p, q, r, s, b);
requires R0(x, a, p, q, r, s, b);
ensures S1(x, a, p, q, r, s, b);
{ 
	p := x;
}

procedure S1_Stable_t3_s2()
modifies q; 
requires S1(x, a, p, q, r, s, b);
requires R1(x, a, p, q, r, s, b);
ensures S1(x, a, p, q, r, s, b);
{ 
	q := x;
}

procedure S1_Stable_t3_s3()
modifies a; 
requires S1(x, a, p, q, r, s, b);
requires R3(x, a, p, q, r, s, b);
ensures S1(x, a, p, q, r, s, b);
{ 
	if (p==1 && q==2)
	{
		a := 1;
	}	
}

procedure S1_Stable_t3_s4()
modifies a; 
requires S1(x, a, p, q, r, s, b);
requires R4(x, a, p, q, r, s, b);
ensures S1(x, a, p, q, r, s, b);
{ 
	if (p==2 && q==1)
	{
		a := 2;
	}	
}



procedure S2_Stable_t3_s1()
modifies p; 
requires S2(x, a, p, q, r, s, b);
requires R0(x, a, p, q, r, s, b);
ensures S2(x, a, p, q, r, s, b);
{ 
	p := x;
}

procedure S2_Stable_t3_s2()
modifies q; 
requires S2(x, a, p, q, r, s, b);
requires R1(x, a, p, q, r, s, b);
ensures S2(x, a, p, q, r, s, b);
{ 
	q := x;
}

procedure S2_Stable_t3_s3()
modifies a; 
requires S2(x, a, p, q, r, s, b);
requires R3(x, a, p, q, r, s, b);
ensures S2(x, a, p, q, r, s, b);
{ 
	if (p==1 && q==2)
	{
		a := 1;
	}	
}

procedure S2_Stable_t3_s4()
modifies a; 
requires S2(x, a, p, q, r, s, b);
requires R4(x, a, p, q, r, s, b);
ensures S2(x, a, p, q, r, s, b);
{ 
	if (p==2 && q==1)
	{
		a := 2;
	}	
}



procedure S3_Stable_t3_s1()
modifies p; 
requires S3(x, a, p, q, r, s, b);
requires R0(x, a, p, q, r, s, b);
ensures S3(x, a, p, q, r, s, b);
{ 
	p := x;
}

procedure S3_Stable_t3_s2()
modifies q; 
requires S3(x, a, p, q, r, s, b);
requires R1(x, a, p, q, r, s, b);
ensures S3(x, a, p, q, r, s, b);
{ 
	q := x;
}

procedure S3_Stable_t3_s3()
modifies a; 
requires S3(x, a, p, q, r, s, b);
requires R3(x, a, p, q, r, s, b);
ensures S3(x, a, p, q, r, s, b);
{ 
	if (p==1 && q==2)
	{
		a := 1;
	}	
}

procedure S3_Stable_t3_s4()
modifies a; 
requires S3(x, a, p, q, r, s, b);
requires R4(x, a, p, q, r, s, b);
ensures S3(x, a, p, q, r, s, b);
{ 
	if (p==2 && q==1)
	{
		a := 2;
	}	
}




procedure P0_Stable_t4_s1()
modifies r; 
requires P0(x, a, p, q, r, s, b);
requires S0(x, a, p, q, r, s, b);
ensures P0(x, a, p, q, r, s, b);
{ 
	r := x;
}

procedure P0_Stable_t4_s2()
modifies s; 
requires P0(x, a, p, q, r, s, b);
requires S1(x, a, p, q, r, s, b);
ensures P0(x, a, p, q, r, s, b);
{ 
	s := x;
}

procedure P0_Stable_t4_s3()
modifies b; 
requires P0(x, a, p, q, r, s, b);
requires S3(x, a, p, q, r, s, b);
ensures P0(x, a, p, q, r, s, b);
{ 
	if (r==2 && s==1)
	{
		b := 1;
	}	
}

procedure P0_Stable_t4_s4()
modifies b; 
requires P0(x, a, p, q, r, s, b);
requires S4(x, a, p, q, r, s, b);
ensures P0(x, a, p, q, r, s, b);
{ 
	if (r==1 && s==2)
	{
		b := 2;
	}	
}



procedure Q0_Stable_t4_s1()
modifies r; 
requires Q0(x, a, p, q, r, s, b);
requires S0(x, a, p, q, r, s, b);
ensures Q0(x, a, p, q, r, s, b);
{ 
	r := x;
}

procedure Q0_Stable_t4_s2()
modifies s; 
requires Q0(x, a, p, q, r, s, b);
requires S1(x, a, p, q, r, s, b);
ensures Q0(x, a, p, q, r, s, b);
{ 
	s := x;
}

procedure Q0_Stable_t4_s3()
modifies b; 
requires Q0(x, a, p, q, r, s, b);
requires S3(x, a, p, q, r, s, b);
ensures Q0(x, a, p, q, r, s, b);
{ 
	if (r==2 && s==1)
	{
		b := 1;
	}	
}

procedure Q0_Stable_t4_s4()
modifies b; 
requires Q0(x, a, p, q, r, s, b);
requires S4(x, a, p, q, r, s, b);
ensures Q0(x, a, p, q, r, s, b);
{ 
	if (r==1 && s==2)
	{
		b := 2;
	}	
}


procedure R0_Stable_t4_s1()
modifies r; 
requires R0(x, a, p, q, r, s, b);
requires S0(x, a, p, q, r, s, b);
ensures R0(x, a, p, q, r, s, b);
{ 
	r := x;
}

procedure R0_Stable_t4_s2()
modifies s; 
requires R0(x, a, p, q, r, s, b);
requires S1(x, a, p, q, r, s, b);
ensures R0(x, a, p, q, r, s, b);
{ 
	s := x;
}

procedure R0_Stable_t4_s3()
modifies b; 
requires R0(x, a, p, q, r, s, b);
requires S3(x, a, p, q, r, s, b);
ensures R0(x, a, p, q, r, s, b);
{ 
	if (r==2 && s==1)
	{
		b := 1;
	}	
}

procedure R0_Stable_t4_s4()
modifies b; 
requires R0(x, a, p, q, r, s, b);
requires S4(x, a, p, q, r, s, b);
ensures R0(x, a, p, q, r, s, b);
{ 
	if (r==1 && s==2)
	{
		b := 2;
	}	
}



procedure R1_Stable_t4_s1()
modifies r; 
requires R1(x, a, p, q, r, s, b);
requires S0(x, a, p, q, r, s, b);
ensures R1(x, a, p, q, r, s, b);
{ 
	r := x;
}

procedure R1_Stable_t4_s2()
modifies s; 
requires R1(x, a, p, q, r, s, b);
requires S1(x, a, p, q, r, s, b);
ensures R1(x, a, p, q, r, s, b);
{ 
	s := x;
}

procedure R1_Stable_t4_s3()
modifies b; 
requires R1(x, a, p, q, r, s, b);
requires S3(x, a, p, q, r, s, b);
ensures R1(x, a, p, q, r, s, b);
{ 
	if (r==2 && s==1)
	{
		b := 1;
	}	
}

procedure R1_Stable_t4_s4()
modifies b; 
requires R1(x, a, p, q, r, s, b);
requires S4(x, a, p, q, r, s, b);
ensures R1(x, a, p, q, r, s, b);
{ 
	if (r==1 && s==2)
	{
		b := 2;
	}	
}



procedure R2_Stable_t4_s1()
modifies r; 
requires R2(x, a, p, q, r, s, b);
requires S0(x, a, p, q, r, s, b);
ensures R2(x, a, p, q, r, s, b);
{ 
	r := x;
}

procedure R2_Stable_t4_s2()
modifies s; 
requires R2(x, a, p, q, r, s, b);
requires S1(x, a, p, q, r, s, b);
ensures R2(x, a, p, q, r, s, b);
{ 
	s := x;
}

procedure R2_Stable_t4_s3()
modifies b; 
requires R2(x, a, p, q, r, s, b);
requires S3(x, a, p, q, r, s, b);
ensures R2(x, a, p, q, r, s, b);
{ 
	if (r==2 && s==1)
	{
		b := 1;
	}	
}

procedure R2_Stable_t4_s4()
modifies b; 
requires R2(x, a, p, q, r, s, b);
requires S4(x, a, p, q, r, s, b);
ensures R2(x, a, p, q, r, s, b);
{ 
	if (r==1 && s==2)
	{
		b := 2;
	}	
}



procedure R3_Stable_t4_s1()
modifies r; 
requires R3(x, a, p, q, r, s, b);
requires S0(x, a, p, q, r, s, b);
ensures R3(x, a, p, q, r, s, b);
{ 
	r := x;
}

procedure R3_Stable_t4_s2()
modifies s; 
requires R3(x, a, p, q, r, s, b);
requires S1(x, a, p, q, r, s, b);
ensures R3(x, a, p, q, r, s, b);
{ 
	s := x;
}

procedure R3_Stable_t4_s3()
modifies b; 
requires R3(x, a, p, q, r, s, b);
requires S3(x, a, p, q, r, s, b);
ensures R3(x, a, p, q, r, s, b);
{ 
	if (r==2 && s==1)
	{
		b := 1;
	}	
}

procedure R3_Stable_t4_s4()
modifies b; 
requires R3(x, a, p, q, r, s, b);
requires S4(x, a, p, q, r, s, b);
ensures R3(x, a, p, q, r, s, b);
{ 
	if (r==1 && s==2)
	{
		b := 2;
	}	
}
