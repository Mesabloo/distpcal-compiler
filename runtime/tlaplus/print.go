package tlaplus

import "fmt"

// Print writes a value to standard output, followed by a newline.
//
// PlusCal's print is a debugging construct, and this is deliberately the whole
// of its contract: a specification that prints says nothing about the format.
// Go's builtin println cannot be used, since it accepts only basic types and
// every TLA+ value here is a defined type or a struct.
//
// Int carries a String method, so integers print as themselves rather than as
// their representation; the composite types fall back on fmt's own rendering of
// slices and structs, which is faithful enough to read but is not a syntax any
// part of this system parses back.
func Print(v any) { fmt.Println(v) }
