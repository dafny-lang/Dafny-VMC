/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module DiscreteLaplace.Equivalence {
  import Rand
  import Monad
  import Rationals
  import BernoulliExpNeg
  import Uniform
  import Coin
  import Model
  import Loops

  /*******
   Lemmas
  *******/

  lemma SampleLiftToEnsures(scale: Rationals.Rational, s: Rand.Bitstream, t: Rand.Bitstream, x: (bool, int))
    requires R1: scale.numer >= 1
    requires R2: Monad.Result(x, s) == Model.SampleLoop(scale)(t)
    ensures Model.Sample(scale)(t) == Monad.Result(if x.0 then -x.1 else x.1, s)
  {
    var f := (x: (bool, int)) => if x.0 then -x.1 else x.1;

    calc {
      Monad.Result(if x.0 then -x.1 else x.1, s);
      Monad.Result(f(x), s);
      Monad.Result(x, s).Map(f);
      { reveal R1; reveal R2; }
      Model.SampleLoop(scale)(t).Map(f);
      Monad.Map(Model.SampleLoop(scale), f)(t);
      { reveal Model.Sample(); }
      Model.Sample(scale)(t);
    }
  }

  lemma SampleLoopLiftToEnsures(scale: Rationals.Rational, s: Rand.Bitstream, t: Rand.Bitstream, bY: (bool, int))
    requires R1: scale.numer >= 1
    requires R2: Model.SampleLoop(scale)(s) == Model.SampleLoop(scale, bY)(t)
    requires R3: !(bY.0 && (bY.1 == 0))
    ensures Model.SampleLoop(scale)(s) == Monad.Result(bY, t)
  {
    calc {
      Monad.Result(bY, t);
      Monad.Return(bY)(t);
      { reveal R1; SampleLoopTailRecursiveEquivalence(scale, t, bY); reveal R3; }
      Model.SampleLoop(scale, bY)(t);
      { reveal R1; reveal R2; }
      Model.SampleLoop(scale)(s);
    }
  }

  lemma SampleInnerLoopLiftToEnsures(s: Rand.Bitstream, t: Rand.Bitstream, a: bool, v: int)
    requires R1: Model.SampleInnerLoop()(s) == Model.SampleInnerLoop((a, v))(t)
    requires R2: !a
    ensures Model.SampleInnerLoopFull()(s) == Monad.Result(v, t)
  {
    var f := (x: (bool, int)) => x.1;

    assert A: Model.SampleInnerLoop()(s) == Monad.Result((a, v), t) by {
      calc {
        Model.SampleInnerLoop()(s);
        { reveal R1; }
        Model.SampleInnerLoop((a, v))(t);
        { SampleInnerLoopTailRecursiveEquivalence(t, (a, v)); reveal R2; }
        Monad.Return((a, v))(t);
        Monad.Result((a, v), t);
      }
    }

    calc {
      Model.SampleInnerLoopFull()(s);
      { reveal Model.SampleInnerLoopFull(); }
      Model.SampleInnerLoop()(s).Map(f);
      { reveal A; }
      Monad.Result((a, v), t).Map(f);
      Monad.Result(v, t);
    }
  }

  lemma {:rlimit 100000} SampleLoopTailRecursiveEquivalence(scale: Rationals.Rational, s: Rand.Bitstream, bY: (bool, int) := (true, 0))
    requires scale.numer >= 1
    ensures
      Model.SampleLoop(scale, bY)(s) ==
      if bY.0 && (bY.1 == 0) then
        Monad.Bind(
          Uniform.Model.Sample(scale.numer),
          (u: nat) =>
            Monad.Bind(
              BernoulliExpNeg.Model.Sample(Rationals.Rational(u, scale.numer)),
              (d: bool) =>
                if d then
                  Monad.Bind(
                    Model.SampleInnerLoopFull(),
                    (v: int) =>
                      Monad.Bind(
                        Coin.Model.Sample,
                        (b: bool) =>
                          var x := u + scale.numer * v;
                          var y := x / scale.denom;
                          Model.SampleLoop(scale, (b, y))
                      )
                  )
                else
                  Model.SampleLoop(scale, bY)
            )
        )(s)
      else
        Monad.Return(bY)(s)
  {
    calc {
      Model.SampleLoop(scale, bY)(s);
    == { reveal Model.SampleLoop();
         reveal Loops.While();
         reveal Model.SampleLoopCondition();
         reveal Model.SampleLoopBody(); }
      Loops.While(Model.SampleLoopCondition, Model.SampleLoopBody(scale))(bY)(s);
    == { Model.SampleLoopTerminatesAlmostSurely(scale);
         Loops.WhileUnroll(Model.SampleLoopCondition, Model.SampleLoopBody(scale), bY, s);
         reveal Model.SampleLoop();
         reveal Model.SampleLoopCondition();
         reveal Model.SampleLoopBody(); }
      if Model.SampleLoopCondition(bY) then
        Monad.Bind(Model.SampleLoopBody(scale)(bY), (bY: (bool, int)) => Model.SampleLoop(scale, bY))(s)
      else
        Monad.Return(bY)(s);
    == { reveal Model.SampleLoopCondition();
         reveal Model.SampleLoopBody(); }
      if bY.0 && (bY.1 == 0) then
        Monad.Bind(
          Monad.Bind(
            Uniform.Model.Sample(scale.numer),
            (u: nat) =>
              Monad.Bind(
                BernoulliExpNeg.Model.Sample(Rationals.Rational(u, scale.numer)),
                (d: bool) =>
                  if d then
                    Monad.Bind(
                      Model.SampleInnerLoopFull(),
                      (v: int) =>
                        Monad.Bind(
                          Coin.Model.Sample,
                          (b: bool) =>
                            var x := u + scale.numer * v;
                            var y := x / scale.denom;
                            Monad.Return((b, y))
                        )
                    )
                  else
                    Monad.Return(bY)
              )
          ),
          (bY: (bool, int)) => Model.SampleLoop(scale, bY)
        )(s)
      else
        Monad.Return(bY)(s);
    ==
      if bY.0 && (bY.1 == 0) then
        Monad.Bind(
          Uniform.Model.Sample(scale.numer),
          (u: nat) =>
            Monad.Bind(
              Monad.Bind(
                BernoulliExpNeg.Model.Sample(Rationals.Rational(u, scale.numer)),
                (d: bool) =>
                  if d then
                    Monad.Bind(
                      Model.SampleInnerLoopFull(),
                      (v: int) =>
                        Monad.Bind(
                          Coin.Model.Sample,
                          (b: bool) =>
                            var x := u + scale.numer * v;
                            var y := x / scale.denom;
                            Monad.Return((b, y))
                        )
                    )
                  else
                    Monad.Return(bY)
              ),
              (bY: (bool, int)) => Model.SampleLoop(scale, bY)
            )
        )(s)
      else
        Monad.Return(bY)(s);
    ==
      if bY.0 && (bY.1 == 0) then
        Monad.Bind(
          Uniform.Model.Sample(scale.numer),
          (u: nat) =>
            Monad.Bind(
              BernoulliExpNeg.Model.Sample(Rationals.Rational(u, scale.numer)),
              (d: bool) =>
                Monad.Bind(
                  if d then
                    Monad.Bind(
                      Model.SampleInnerLoopFull(),
                      (v: int) =>
                        Monad.Bind(
                          Coin.Model.Sample,
                          (b: bool) =>
                            var x := u + scale.numer * v;
                            var y := x / scale.denom;
                            Monad.Return((b, y))
                        )
                    )
                  else
                    Monad.Return(bY),
                  (bY: (bool, int)) => Model.SampleLoop(scale, bY)
                )
            )
        )(s)
      else
        Monad.Return(bY)(s);
    ==
      if bY.0 && (bY.1 == 0) then
        Monad.Bind(
          Uniform.Model.Sample(scale.numer),
          (u: nat) =>
            Monad.Bind(
              BernoulliExpNeg.Model.Sample(Rationals.Rational(u, scale.numer)),
              (d: bool) =>
                if d then
                  Monad.Bind(
                    Monad.Bind(
                      Model.SampleInnerLoopFull(),
                      (v: int) =>
                        Monad.Bind(
                          Coin.Model.Sample,
                          (b: bool) =>
                            var x := u + scale.numer * v;
                            var y := x / scale.denom;
                            Monad.Return((b, y))
                        )
                    ),
                    (bY: (bool, int)) => Model.SampleLoop(scale, bY)
                  )
                else
                  Monad.Bind(
                    Monad.Return(bY),
                    (bY: (bool, int)) => Model.SampleLoop(scale, bY)
                  )
            )
        )(s)
      else
        Monad.Return(bY)(s);
    ==
      if bY.0 && (bY.1 == 0) then
        Monad.Bind(
          Uniform.Model.Sample(scale.numer),
          (u: nat) =>
            Monad.Bind(
              BernoulliExpNeg.Model.Sample(Rationals.Rational(u, scale.numer)),
              (d: bool) =>
                if d then
                  Monad.Bind(
                    Model.SampleInnerLoopFull(),
                    (v: int) =>
                      Monad.Bind(
                        Monad.Bind(
                          Coin.Model.Sample,
                          (b: bool) =>
                            var x := u + scale.numer * v;
                            var y := x / scale.denom;
                            Monad.Return((b, y))
                        ),
                        (bY: (bool, int)) => Model.SampleLoop(scale, bY)
                      )
                  )
                else
                  Model.SampleLoop(scale, bY)
            )
        )(s)
      else
        Monad.Return(bY)(s);
    ==
      if bY.0 && (bY.1 == 0) then
        Monad.Bind(
          Uniform.Model.Sample(scale.numer),
          (u: nat) =>
            Monad.Bind(
              BernoulliExpNeg.Model.Sample(Rationals.Rational(u, scale.numer)),
              (d: bool) =>
                if d then
                  Monad.Bind(
                    Model.SampleInnerLoopFull(),
                    (v: int) =>
                      Monad.Bind(
                        Coin.Model.Sample,
                        (b: bool) =>
                          var x := u + scale.numer * v;
                          var y := x / scale.denom;
                          Monad.Bind(
                            Monad.Return((b, y)),
                            (bY: (bool, int)) => Model.SampleLoop(scale, bY)
                          )
                      )
                  )
                else
                  Model.SampleLoop(scale, bY)
            )
        )(s)
      else
        Monad.Return(bY)(s);
    ==
      if bY.0 && (bY.1 == 0) then
        Monad.Bind(
          Uniform.Model.Sample(scale.numer),
          (u: nat) =>
            Monad.Bind(
              BernoulliExpNeg.Model.Sample(Rationals.Rational(u, scale.numer)),
              (d: bool) =>
                if d then
                  Monad.Bind(
                    Model.SampleInnerLoopFull(),
                    (v: int) =>
                      Monad.Bind(
                        Coin.Model.Sample,
                        (b: bool) =>
                          var x := u + scale.numer * v;
                          var y := x / scale.denom;
                          Model.SampleLoop(scale, (b, y))
                      )
                  )
                else
                  Model.SampleLoop(scale, bY)
            )
        )(s)
      else
        Monad.Return(bY)(s);
    }
  }

  lemma SampleInnerLoopTailRecursiveEquivalence(s: Rand.Bitstream, x: (bool, int) := (true, 0))
    ensures
      Model.SampleInnerLoop(x)(s) ==
      if x.0 then
        Monad.Bind(
          BernoulliExpNeg.Model.Sample(Rationals.Int(1)),
          (a: bool) => Model.SampleInnerLoop((a, if a then x.1 + 1 else x.1))
        )(s)
      else
        Monad.Return(x)(s)
  {
    calc {
      Model.SampleInnerLoop(x)(s);
    == { reveal Loops.While();
         reveal Model.SampleInnerLoop();
         reveal Model.SampleInnerLoopBody();
         reveal Model.SampleInnerLoopCondition(); }
      Loops.While(Model.SampleInnerLoopCondition, Model.SampleInnerLoopBody)(x)(s);
    == { Model.SampleInnerLoopTerminatesAlmostSurely();
         Loops.WhileUnroll(Model.SampleInnerLoopCondition, Model.SampleInnerLoopBody, x, s);
         reveal Model.SampleInnerLoop();
         reveal Model.SampleInnerLoopBody();
         reveal Model.SampleInnerLoopCondition(); }
      if Model.SampleInnerLoopCondition(x) then
        Monad.Bind(Model.SampleInnerLoopBody(x), (y: (bool, int)) => Model.SampleInnerLoop(y))(s)
      else
        Monad.Return(x)(s);
    == { reveal Model.SampleInnerLoopBody();
         reveal Model.SampleInnerLoopCondition(); }
      if x.0 then
        Monad.Bind(
          Monad.Bind(
            BernoulliExpNeg.Model.Sample(Rationals.Int(1)),
            (a: bool) => Monad.Return((a, if a then x.1 + 1 else x.1))
          ),
          (y: (bool, int)) => Model.SampleInnerLoop(y)
        )(s)
      else
        Monad.Return(x)(s);
    ==
      if x.0 then
        Monad.Bind(
          BernoulliExpNeg.Model.Sample(Rationals.Int(1)),
          (a: bool) =>
            Monad.Bind(
              Monad.Return((a, if a then x.1 + 1 else x.1)),
              (y: (bool, int)) => Model.SampleInnerLoop(y)
            )
        )(s)
      else
        Monad.Return(x)(s);
    ==
      if x.0 then
        Monad.Bind(
          BernoulliExpNeg.Model.Sample(Rationals.Int(1)),
          (a: bool) => Model.SampleInnerLoop((a, if a then x.1 + 1 else x.1))
        )(s)
      else
        Monad.Return(x)(s);
    }
  }
}