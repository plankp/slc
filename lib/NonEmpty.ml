type +'a t = 'a * 'a list

let hd ((v, _) : 'a t) : 'a = v
let tl ((_, v) : 'a t) : 'a list = v
let cons (v : 'a) ((y, ys) : 'a t) : 'a t = (v, y :: ys)
let singleton (v : 'a) : 'a t = (v, [])
