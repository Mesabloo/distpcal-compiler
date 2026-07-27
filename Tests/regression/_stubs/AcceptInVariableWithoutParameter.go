package fixture

import "github.com/mesabloo/fugue/runtime/tlaplus"

// Vals is the fixture's own CONSTANT. A CONSTANT compiles to a plain Go identifier that the
// specification's user is expected to define, so the emitted code does not build until something
// supplies one. This is that something.
var Vals = tlaplus.MkSet(tlaplus.IntOrd, tlaplus.MkInt(1), tlaplus.MkInt(2), tlaplus.MkInt(3))
