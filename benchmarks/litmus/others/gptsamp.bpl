// Shared variables
var sharedVar: int;

// Procedure to increment sharedVar by 1
procedure Increment() {
    // Precondition: None
    
    // Increment sharedVar by 1
    sharedVar := sharedVar + 1;
    
    // Postcondition: sharedVar increased by 1
}

// Threads that increment sharedVar
procedure Thread1() {
    call Increment();
}

procedure Thread2() {
    call Increment();
}

// The main procedure that starts the threads
procedure Main() {
    // Initialize shared variable
    sharedVar := 0;
    
    // Start threads
    par {call Thread1(); call Thread2();};
    
    // Assertion: The sum of increments is 2
    assert sharedVar == 2;
}

// Entrypoint
procedure {:entrypoint} Program() {
    call Main();
}

