package main

import "fmt"

type L struct {
	x    int
	next *L
}

func main() {
	z := new(L)
	z.x = 42
	z.next = new(L)
	n := z.next
	n.x = 43;
	fmt.Print(z.x)
	fmt.Print(z.next.x)
	fmt.Print(z.next.next)
	fmt.Print("\n")
}

