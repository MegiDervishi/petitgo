package main

import "fmt"
func foo() { var x int; fmt.Print(x); x := 1; fmt.Print(x) }
func main() {}


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

