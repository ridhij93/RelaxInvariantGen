/*
				T1							T2
					Pre := {x == 0, y == 0}					
					
		P0							Q0

((x == 0)||(x == 2))&&((y == 0)||(y == 1))		((x == 0)||(x == 1))&&((y == 2)||(y == 0))


		  	s1:	x := 1;					y := 1;
		P1							Q1

((x == 1))&&((y == 1)||(y == 0))		        ((x == 1)||(x == 0))&&((y == 1))


			s2:	y := 2;					x := 2;
		P2							Q2

((x == 1)||(x == 2))&&((y == 2))		        ((y == 2)||(y == 1))&&((x == 2))

					Post := {x == 1, y == 1}




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
var y: int;

function {:existential true} {:inline} P0(x: int, y: int) : bool;
function {:existential true} {:inline} P1(x: int, y: int) : bool;
function {:existential true} {:inline} P2(x: int, y: int) : bool;
function {:existential true} {:inline} Q0(x: int, y: int) : bool;
function {:existential true} {:inline} Q1(x: int, y: int) : bool;
function {:existential true} {:inline} Q2(x: int, y: int) : bool;

procedure pre_condition()
requires x == 0 && y == 0;
{ 
	assert P0(x, y);
  	assert Q0(x, y);
}

procedure post_condition()
requires P2(x, y);
requires Q2(x, y);
{ 
  	assert (x != 1 ||  y != 1);
}


procedure t1_transition_s1()
modifies x; 
requires P0(x, y);
ensures P1(x, y);
{ 
	x := 1;
}

procedure t1_transition_s2()
modifies y; 
requires P1(x, y);
ensures P2(x, y);
{ 
	y := 2;
}

procedure t2_transition_s1()
modifies y; 
requires Q0(x, y);
ensures Q1(x, y);
{ 
	y := 1;
}

procedure t2_transition_s2()
modifies x; 
requires Q1(x, y);
ensures Q2(x, y);
{ 
	x := 2;
}

procedure P0_Stable_t2_s1()
modifies y; 
requires P0(x, y);
requires Q0(x, y);
ensures P0(x, y);
{ 
	y := 1;
}

procedure P1_Stable_t2_s1()
modifies y; 
requires P1(x, y);
requires Q0(x, y);
ensures P1(x, y);
{ 
	y := 1;
}

procedure P2_Stable_t2_s1()  // was thrwing errors
modifies y; 
requires P2(x, y);	
requires Q0(x, y);
ensures P2(x, y);
{ 
	y := 2; // changed y from 1 to 2
}

procedure P0_Stable_t2_s2()
modifies x; 
requires P0(x, y);
requires Q1(x, y);
ensures P0(x, y);
{ 
	x := 2;
}

procedure P1_Stable_t2_s2()
modifies x; 
requires P1(x, y);
requires Q1(x, y);
ensures P1(x, y);
{ 
	x := 2;
}

procedure P2_Stable_t2_s2()
modifies x; 
requires P2(x, y);
requires Q1(x, y);
ensures P2(x, y);
{ 
	x := 2;
}

procedure Q0_Stable_t1_s1()
modifies x; 
requires P0(x, y);
requires Q0(x, y);
ensures Q0(x, y);
{ 
	x := 1;
}


procedure Q1_Stable_t1_s1()
modifies x; 
requires P0(x, y);
requires Q1(x, y);
ensures Q1(x, y);
{ 
	x := 1;
}

procedure Q2_Stable_t1_s1()
modifies x; 
requires P0(x, y);
requires Q2(x, y);
ensures Q2(x, y);
{ 
	x := 2; // changed x from 1 to 2
}


procedure Q0_Stable_t1_s2()
modifies y; 
requires P1(x, y);
requires Q0(x, y);
ensures Q0(x, y);
{ 
	y := 2;
}


procedure Q1_Stable_t1_s2()
modifies y; 
requires P1(x, y);
requires Q1(x, y);
ensures Q1(x, y);
{ 
	y := 2;
}


procedure Q2_Stable_t1_s2()
modifies y; 
requires P1(x, y);
requires Q2(x, y);
ensures Q2(x, y);
{ 
	y := 2;
}

