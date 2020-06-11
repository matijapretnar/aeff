open Js_browser

let source = "
let absurd void = (match void with)

(* Booleans *)
let not x = if x then false else true

type 'a option = None | Some of 'a
let rec assoc x = function
  | [] |-> None
  | (key, v) :: lst |-> if x = key then Some v else assoc x lst

let rec range m n =
  if m > n then
    []
  else
    m :: range (m + 1) n

let reverse lst =
  let rec reverse_acc acc = function
    | [] |-> acc
    | x :: xs |-> reverse_acc (x :: acc) xs
  in
  reverse_acc [] lst

let rec map f = function
  | [] |-> []
  | x :: xs |->
    let y = f x in
    let ys = map f xs in
    y :: ys

let hd = function
  | x :: _ |-> x

let tl = function
  | x :: xs |-> xs

let take f k =
  let r = range 0 k in map f r

let rec fold_left f acc = function
  | [] |-> acc
  | y :: ys |->
    let acc' = f acc y in
    fold_left f acc' ys

let rec fold_right f xs acc =
  match xs with
    | [] |-> acc
    | x :: xs |->
      let acc' = fold_right f xs acc in
      f x acc'
    
    let rec iter f = function
  | [] |-> ()
  | x :: xs |-> f x; iter f xs

let rec forall p = function
  | [] |-> true
  | x :: xs |-> if p x then forall p xs else false

let rec exists p = function
  | [] |-> false
  | x :: xs |-> if p x then true else exists p xs

let mem x = exists (fun x' |-> x = x')
let rec filter p = function
  | [] |-> []
  | x :: xs |->
    if p x then (x :: filter p xs) else filter p xs

let complement xs ys = filter (fun x |-> not (mem x ys)) xs
let intersection xs ys = filter (fun x |-> mem x ys) xs
let rec zip xs ys =
  match (xs, ys) with
  | ([], []) |-> []
  | (x :: xs, y :: ys) |-> (x, y) :: (zip xs ys)

let rec unzip = function
  | [] |-> ([], [])
  | (x, y) :: xys |->
    let xs, ys = unzip xys in
    (x :: xs, y :: ys)

let rec (@) (xs, ys) =
  match xs with
  | [] |-> ys
  | x :: xs |-> x :: (xs @ ys)

let rec length = function
  | [] |-> 0
  | x :: xs |-> length xs + 1

let rec nth (x::xs) n =
  if n = 0 then x else nth xs (n - 1)

(* Basic functions *)
let abs x = if x < 0 then -x else x
let min x y = if x < y then x else y
let max x y = if x < y then y else x
let rec gcd m n =
  match n with
  | 0 |-> m
  | _ |-> let g = gcd n in g (m mod n)

let rec lcm m n =
  let d = gcd m n in (m * n) / d

let odd x = (x mod 2) = 1
let even x = (x mod 2) = 0
let id x = x
let compose f g x = f (g x)
let (|>) x f = f x
let ignore _ = ()
let fst (x, _) = x
let snd (_, y) = y
  
let return x = x

let awaitValue p =
    await p until <<value>> in return value

operation request : int
operation response : int list
operation nextItem : unit
operation display : string
operation batchSizeRequest : unit
operation batchSizeResponse : int


let client () =
    let cachedData = ref [] in
    let requestInProgress = ref false in
    let currentItem = ref 0 in

    send batchSizeRequest ();
    promise (batchSizeResponse batchSize |-> return <<batchSize>>) as batchSizePromise in

    let requestNewData offset =
        requestInProgress := true;
        send request offset;
        promise (response newBatch |->
            cachedData := !cachedData @ newBatch;
            requestInProgress := false;
            return <<()>>)
        as _ in
        return ()
    in

    let rec clientLoop batchSize =
        promise (nextItem () |->
            let cachedSize = length !cachedData in
            (if (!currentItem > cachedSize - batchSize / 2) && (not !requestInProgress) then
                 requestNewData (cachedSize + 1)
             else
                 return ());
            (if (!currentItem) < cachedSize then
                 send display (toString (nth !cachedData !currentItem));
                 currentItem := !currentItem + 1
             else  
                 send display \"please wait a bit and try again\");
            clientLoop batchSize)
        as p in
        return p
    in

    await batchSizePromise until <<batchSize>> in
    clientLoop batchSize

let server batchSize =
    let rec waitForBatchSize () =
        promise (batchSizeRequest () |->
            send batchSizeResponse batchSize;
            waitForBatchSize ())
        as p in
        return p
    in
    let rec waitForRequest () =
        promise (request offset |->
            let payload = map (fun x |-> 10 * x) (range offset (offset + batchSize - 1)) in
            send response payload;
            waitForRequest ())
        as p in
        return p
    in
    waitForBatchSize ();
    waitForRequest ()


let rec user () =
    let rec wait n = 
      if n = 0 then return () else wait (n - 1)
    in
    send nextItem ();
    wait 10;
    user ()


run (server 42)
run (client ())
run (user ())
"

let make_process = function
    | [] -> Ast.Run (Ast.Return (Ast.Tuple []))
    | comp :: comps ->
        List.fold_left (fun proc comp -> Ast.Parallel (proc, Ast.Run comp)) (Ast.Run comp) comps

let init =
  try
    let state = Loader.load_source source in
    let proc = make_process state.Loader.top_computations in
    Model.init state proc
  with
  | Error.Error (_, _, msg) -> failwith msg

let app = Vdom.simple_app ~init ~view:View.view ~update:Model.update ()
let run () = Vdom_blit.run app |> Vdom_blit.dom |> Element.append_child (Document.body document)
let () = Window.set_onload window run
