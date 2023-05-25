export map, bind, value, unit
     , T

data T +a =
  | None
  | Some a

let value : a -> T a -> a
and value _ (Some v) = v
and value v None     = v

let map : (a -> b) -> T a -> T b
and map _ None     = None
and map f (Some v) = Some (f v)

let bind : T a -> (a -> T b) -> T b
and bind None     _ = None
and bind (Some v) f = f v

let unit : a -> T a
and unit v = Some v
