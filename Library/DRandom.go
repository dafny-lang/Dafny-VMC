/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT
*******************************************************************************/

package DafnyLibraries

import(
  "math/rand"
)

func *DRandom Ctor__(self) {
}

func *DRandom Coin() bool {
  return rand.Intn(2)
}


