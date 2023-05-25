export map, bind, unit, rev, rev_append, append

# The list data constructors are magically implemented within the compiler,
# but if they weren't, it would look something like this:
#
#   data [+a] =
#     | []
#     | a :: [a]

let rev_append : [a] -> [a] -> [a]
and rev_append xs acc =
  rec go acc []        = acc
  and go acc (x :: xs) = go (x :: acc) xs in
  go acc xs

let rev : [a] -> [a]
and rev xs = rev_append xs []

rec append : [a] -> [a] -> [a]
and append []        acc = acc
and append (x :: xs) acc = x :: append xs acc

let unit : a -> [a]
and unit v = [v]

rec map : (a -> b) -> [a] -> [b]
and map _ []        = []
and map f (x :: xs) = let hd = f x in hd :: map f xs

rec bind : [a] -> (a -> [b]) -> [b]
and bind []        _ = []
and bind (x :: xs) f = let prefix = f x in append prefix (bind xs f)
