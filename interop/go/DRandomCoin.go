package BaseInterfacexxx

import (
	"math/rand"
)

var r = rand.New(rand.NewSource(99))

type FOO struct {}

var DRandomCoin = FOO{}

func (d FOO) Coin() bool {
  return rand.Intn(2) == 1
}

