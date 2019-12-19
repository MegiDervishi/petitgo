package main
import "fmt"
func main() {
	fmt.Print("a")
	fmt.Print()
	fmt.Print("b\n")
	fmt.Print(true, "\n")
	fmt.Print(false, "\n")
	fmt.Print(1, 2, 3, "\n")
	fmt.Print(1, "2", 3, "\n")
	fmt.Print(1, "2", 3, 4, "5", "\n")
	fmt.Print(1, "2", 3, true, "5", "\n")
	s := "s"
	fmt.Print(1, s, 3, "\n")
	fmt.Print(nil, "\n")
	var p *int = nil
	fmt.Print("a", p, "b\n")
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

