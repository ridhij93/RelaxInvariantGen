type threadId;

var x: int;
var y: int;

procedure thread1(tid: threadId)
{
    x := 2;
    y := 1;
}

procedure thread2(tid: threadId)
{
    y := 3;
    x := 4;
}

procedure main()
    requires true
    ensures (x != 2 || y != 3)
{
    var i: threadId;
    var j: threadId;
    call thread1(i);
    call thread2(j);
}


