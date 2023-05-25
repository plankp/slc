# slc

We went a bit further than simply lambda calculus... Whatever :metal:

## Build instructions

```
$ dune build slc
```

and then you can execute the `slc` program (should be under the `_build/install/default/bin` directory).

For example, you can take the snippet in the [section below](#sample-snippet),
save it in `Sample.sl` (it really has to be a valid module name followed by `.sl`),
and feed it to `slc`.

```
$ slc ./Sample.sl
```

For more information, use the `--help` flag.

```
$ slc --help

slc <options> <files>
  -entry Mark a module as an entry point
  -I Include a directory when searching for modules
  (... more options omitted here ...)
  -help  Display this list of options
  --help  Display this list of options
  -Xdump-hir Dump HIR (for debugging purposes)
  -Xdump-lir Dump LIR (for debugging purposes)
```

Alternatively, you can compile-and-run as follows.

```
$ dune exec slc -- flags-to-slc-go-here
```

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
*  Module support (with separate compilation but not first class like OCaml)
