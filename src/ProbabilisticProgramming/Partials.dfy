module Partials {
  datatype Partial<T> = Diverging | Terminating(value: T) {
    predicate IsFailure() {
      Diverging?
    }

    function PropagateFailure<U>(): Partial<U> {
      Diverging
    }

    function Extract(): T
      requires !IsFailure()
    {
      this.value
    }

    function Map<U>(f: T -> U): Partial<U> {
      match this
      case Terminating(value) => Terminating(f(value))
      case Diverging => Diverging
    }

    function UnwrapOr(default: T): T {
      match this
      case Terminating(value) => value
      case Diverging => default
    }

    function Satisfies(f: T -> bool): bool {
      this.Map(f).UnwrapOr(false)
    }

    function Bind<U>(f: T -> Partial<U>): Partial<U> {
      match this
      case Terminating(value) => f(value)
      case Diverging => Diverging
    }
  }
}
