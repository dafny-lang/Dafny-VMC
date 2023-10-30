// module FreeMonad {
//   datatype Free<A, !B> =
//   | Return(A)
//   | Coin(bool -> Free<A, B>)
//   | While(depth: nat, B -> bool, B -> Free<B, B>, B, B -> Free<A, B>) {
//     function Map<C>(f: A -> C): Free<C, B> {
//       match this
//       case Return(a) => Return(f(a))
//       case Coin(cont) => Coin(b => cont(b).Map(f))
//       case While(cond, body, init, cont) => While(cond, body, init, b => cont(b).Map(f))
//     }

//     function Bind<C>(f: A -> Free<C, B>): Free<C, B> {
//       match this
//       case Return(a) => f(a)
//       case Coin(cont) => Coin((b: bool) => cont(b).Bind(f))
//       case While(cond, body, init, cont) => While(cond, body, init, b => cont(b).Bind(f))
//     }

//     ghost function Depth(): nat {
//       match this
//       case Return(_) => 0
//       case Coin(f) => if f(false).Depth() < f(true).Depth() then f(true).Depth() else f(false).Depth()
//       case While(depth, cond, body, init, cont) =>
//     }
//   }

  datatype Syntax<!T, A> =
  | Coin(T -> A)
  | While(cond: T -> bool, body: T -> A, init: T, cont: T -> A) {
    function Map<B>(f: A -> B): Syntax<T, B> {
      match this
      case Coin(g) => Coin(t => f(g(t)))
      case While(cond, body, init, cont) => While(cond, t => f(body(t)), init, t => f(cont(t)))
    }
  }

  datatype FreeM<!T, A> =
  | Return(A)
  | Free(Syntax<T, FreeM<T, A>>) {
    function Bind<B>(f: A -> FreeM<T, B>): FreeM<T, B> {
      match this
      case Return(a) => f(a)
      case Free(g) => Free(g.Map((x: FreeM<T, A>) => x.Bind(f)))
    }
  }
// }
