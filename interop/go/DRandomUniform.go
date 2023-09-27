package UniformImplementationxxx

import (
  "dafny"
	"math/rand"
)

var r = rand.New(rand.NewSource(99))

type FOO struct {}

var DRandomUniform = FOO{}

func (d FOO) Uniform(n dafny.Int) dafny.Int {
  return n
}





