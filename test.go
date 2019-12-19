package main

import "fmt"

type L struct {
	x    int
	next *L
}

func main() {
	z := new(L)
	z.x = 42
	fmt.Print(z.x)
	fmt.Print(z.next)
	fmt.Print("\n")
	z.next = new(L)
	n := z.next
	n.x = 43;
	fmt.Print(z.x)
	fmt.Print(z.next.x)
	fmt.Print(z.next.next)
	fmt.Print("\n")
}



/*

package main
import "fmt"

func main() {
	x := 1 -> 
	p := (& x-> true) false
	*p ->
	fmt.Print(*p)
	fmt.Print("\n")
}
 
*/

/*package main
import "fmt"
type T struct { a int; b bool; p *int }
func main() {
	t := new(T)
	t.p = &t.a
	fmt.Print(-t.a)
	fmt.Print(!t.b)
	fmt.Print(*t.p)
}*/
/*package main
func foo(x bool) { x := 1; x++}
func main() {} 
This is suppose to give an error? why is it typing good? */

