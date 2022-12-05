#include <iostream>
int x,y;
int main ()
{
int c = 6;
int d;
std::cin >> x;
std::cin >> y;
d = y;

y = 10;
if (d > 10)
	c = x;

std::cout << x << "--"<< y << " -- " << c << " -- "  << d << "\n";

}
