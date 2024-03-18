
module Pos {

  newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

  type pos = x: nat | x > 0 witness 1

  type nat32 = x: int32 | x >= 0 witness 1

  type pos32 = x: nat32 | x > 0 witness 1

}