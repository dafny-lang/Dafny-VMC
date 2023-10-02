package CoinImplementation

import (
	"math/rand"
)

var r = rand.New()

type DRandomCoin_ struct {}

var DRandomCoin = DRandomCoin_{}

func (d DRandomCoin_) CoinSample() bool {
  return rand.Intn(2) == 1
}

