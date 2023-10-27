/*



P0
x=2; 
P1


Q0
p=x;
Q1
y=1;
Q2
if (p==2)
   a=1;
Q3

R0
y=2;
R1
x=1;
R2


  assert( x != 2 || y != 2 || a != 1);



*/

var x: int;
var y: int;
var a: int;
var p: int;
var b: int;



function {:existential true} {:inline} P0(x: int, a: int, p: int, b: int, y: int) : bool;
function {:existential true} {:inline} P1(x: int, a: int, p: int, b: int, y: int) : bool;


function {:existential true} {:inline} Q0(x: int, a: int, p: int, b: int, y: int) : bool;
function {:existential true} {:inline} Q1(x: int, a: int, p: int, b: int, y: int) : bool;
function {:existential true} {:inline} Q2(x: int, a: int, p: int, b: int, y: int) : bool;
function {:existential true} {:inline} Q3(x: int, a: int, p: int, b: int, y: int) : bool;

function {:existential true} {:inline} R0(x: int, a: int, p: int, b: int, y: int) : bool;
function {:existential true} {:inline} R1(x: int, a: int, p: int, b: int, y: int) : bool;
function {:existential true} {:inline} R2(x: int, a: int, p: int, b: int, y: int) : bool;



procedure pre_condition()
requires x == 0 && a == 0 && b == 0 && y == 0;
{ 
	assert P0(x, a, p, b, y);
  	assert Q0(x, a, p, b, y);
  	assert R0(x, a, p, b, y);
}

procedure post_condition()
requires P1(x, a, p, b, y);
requires Q3(x, a, p, b, y);
requires R2(x, a, p, b, y);
{ 
  	assert ( x != 2 || y != 2 || a != 1);
}



procedure t1_transition_s1()
modifies x; 
requires P0(x, a, p, b, y);
ensures P1(x, a, p, b, y);
{ 
	x := 2;
}



procedure t2_transition_s1()
modifies p; 
requires Q0(x, a, p, b, y);
ensures Q1(x, a, p, b, y);
{ 
	p := x;
}

procedure t2_transition_s2()
modifies y; 
requires Q1(x, a, p, b, y);
ensures Q2(x, a, p, b, y);
{ 
	y := 1;
}

procedure t2_transition_s3()
modifies a; 
requires Q2(x, a, p, b, y);
ensures Q3(x, a, p, b, y);
{ 
	if (p == 2)
	{
	    a := 1;
	}    							
}

procedure t3_transition_s1()
modifies y; 
requires R0(x, a, p, b, y);
ensures R1(x, a, p, b, y);
{ 
	y := 2;
}

procedure t3_transition_s2()
modifies x; 
requires R1(x, a, p, b, y);
ensures R2(x, a, p, b, y);
{ 
	x := 1;
}

procedure P0_Stable_t2_s1()
modifies p; 
requires P0(x, a, p, b, y);
requires Q0(x, a, p, b, y);
ensures P0(x, a, p, b, y);
{ 
	p := x;
}




procedure P0_Stable_t2_s2()
modifies y; 
requires P0(x, a, p, b, y);
requires Q1(x, a, p, b, y);
ensures P0(x, a, p, b, y);
{ 
	y := 1;
}

procedure P0_Stable_t2_s3()
modifies a; 
requires P0(x, a, p, b, y);
requires Q2(x, a, p, b, y);
ensures P0(x, a, p, b, y);
{ 
	if (p==2)
	{
		a := 1;
	}
}


procedure R0_Stable_t2_s1()
modifies p; 
requires R0(x, a, p, b, y);
requires Q0(x, a, p, b, y);
ensures R0(x, a, p, b, y);
{ 
	p := x;
}



procedure R0_Stable_t2_s2()
modifies y; 
requires R0(x, a, p, b, y);
requires Q1(x, a, p, b, y);
ensures R0(x, a, p, b, y);
{ 
	y := 1;
}

procedure R0_Stable_t2_s3()
modifies a; 
requires R0(x, a, p, b, y);
requires Q2(x, a, p, b, y);
ensures R0(x, a, p, b, y);
{ 
	if (p==2)
	{
		a := 1;
	}
}



procedure R1_Stable_t2_s1()
modifies p; 
requires R1(x, a, p, b, y);
requires Q0(x, a, p, b, y);
ensures R1(x, a, p, b, y);
{ 
	p := x;
}



procedure R1_Stable_t2_s2()
modifies y; 
requires R1(x, a, p, b, y);
requires Q1(x, a, p, b, y);
ensures R1(x, a, p, b, y);
{ 
	y := 1;
}

procedure R1_Stable_t2_s3()
modifies a; 
requires R1(x, a, p, b, y);
requires Q2(x, a, p, b, y);
ensures R1(x, a, p, b, y);
{ 
	if (p==2)
	{
		a := 1;
	}
}

procedure Q0_Stable_t1_s1()
modifies x; 
requires P0(x, a, p, b, y);
requires Q0(x, a, p, b, y);
ensures Q0(x, a, p, b, y);
{ 
	x := 2;
}

procedure Q1_Stable_t1_s1()
modifies x; 
requires P0(x, a, p, b, y);
requires Q1(x, a, p, b, y);
ensures Q1(x, a, p, b, y);
{ 
	x := 2;
}


procedure Q2_Stable_t1_s1()
modifies x; 
requires P0(x, a, p, b, y);
requires Q2(x, a, p, b, y);
ensures Q2(x, a, p, b, y);
{ 
	x := 2;
}


procedure R0_Stable_t1_s1()
modifies x; 
requires P0(x, a, p, b, y);
requires R0(x, a, p, b, y);
ensures R0(x, a, p, b, y);
{ 
	x := 2;
}

procedure R1_Stable_t1_s1()
modifies x; 
requires P0(x, a, p, b, y);
requires R1(x, a, p, b, y);
ensures R1(x, a, p, b, y);
{ 
	x := 2;
}



procedure P0_Stable_t3_s1()
modifies y; 
requires P0(x, a, p, b, y);
requires R0(x, a, p, b, y);
ensures P0(x, a, p, b, y);
{ 
	y := 2;
}


procedure P0_Stable_t3_s2()
modifies x; 
requires P0(x, a, p, b, y);
requires R1(x, a, p, b, y);
ensures P0(x, a, p, b, y);
{ 
	x := 1;
}


procedure Q0_Stable_t3_s1()
modifies y; 
requires Q0(x, a, p, b, y);
requires R0(x, a, p, b, y);
ensures Q0(x, a, p, b, y);
{ 
	y := 2;
}


procedure Q0_Stable_t3_s2()
modifies x; 
requires Q0(x, a, p, b, y);
requires R1(x, a, p, b, y);
ensures Q0(x, a, p, b, y);
{ 
	x := 1;
}

procedure Q1_Stable_t3_s1()
modifies y; 
requires Q1(x, a, p, b, y);
requires R0(x, a, p, b, y);
ensures Q1(x, a, p, b, y);
{ 
	y := 2;
}


procedure Q1_Stable_t3_s2()
modifies x; 
requires Q1(x, a, p, b, y);
requires R1(x, a, p, b, y);
ensures Q1(x, a, p, b, y);
{ 
	x := 1;
}

procedure Q2_Stable_t3_s1()
modifies y; 
requires Q2(x, a, p, b, y);
requires R0(x, a, p, b, y);
ensures Q2(x, a, p, b, y);
{ 
	y := 2;
}

procedure Q2_Stable_t3_s2()
modifies x; 
requires Q2(x, a, p, b, y);
requires R1(x, a, p, b, y);
ensures Q2(x, a, p, b, y);
{ 
	x := 1;
}

/*



*/
