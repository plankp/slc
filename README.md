# slc

We went a bit further than simply lambda calculus... Whatever :metal:

## Build instructions

```sh
dune exec --display=quiet slc
```

and then you punch in all your code then end with Ctrl-D or whatever your shell uses as EOF.

## Sample snippet

```
export pack, call, tail, map

data Option +a =
  | None
  | Some a

data Obj = Obj a (a -> {})

let call : Obj -> {}
and call = \(Obj v f) -> f v

let pack (x : a) (y : b) = {x, y}
let tail = \case {
  _ :: xs -> xs;
  [] -> [];
}

rec map : (a -> b) -> [a] -> [b]
and map f (x :: xs) = f x :: map f xs
and map _ []        = []
```

## Supported features

As mentioned earlier, this was only meant to support simple lambda calculus, so the features are very lacking when compared to a full-blown language.

*  Anonymous functions (duh...)
*  Let bindings (recursive ones must be functions)
*  Pattern matching + pattern-bound (scoped) type variables
*  Ref cells with relaxed value restriction
*  Algebraic data types (with existentials but no GADTs)
