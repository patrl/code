type l = L;;
type r = R;;
type app = L | R;;

let f (x: l) : l = L;;
let g (y: r) : r = R;;
let h (z: app) : l = L;;

type ot = Int | Bool;;

let f (x: ot) = 2;;
let g (f: ot -> int) = 2;;
