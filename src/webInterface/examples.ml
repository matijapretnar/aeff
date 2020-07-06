let stdlib =
  "let absurd void = (match void with)

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
    await p until <<value>> in return value"

let async =
  "operation question : unit -> int
operation answer : int

let get_answer f =
  promise (answer x |-> <<x>>)
  as result in
  send question f;
  result

run
  let r = get_answer (fun () |-> 3 + 3) in
  let y = 1 + 1 in
  let z = y + y in
  let w = y + z in
  let u = (w + 1) * (awaitValue r) in
  u

run
  promise (question f |->
    let y = f () in
    send answer y;
    return <<()>>
  ) as p in
  p
  "

let cancellableCall =
  "operation call : int * int
operation result : int * int
operation cancel : int
operation dummy : empty

let callWith callCounter =
    fun x |->
        let callNo = !callCounter in
        send call (x, callNo);
        callCounter := callNo + 1;
        let rec awaitLoop () =
            promise (result (y, callNo') |->
                if callNo = callNo' then
                    <<y>>
                else
                    awaitLoop ()
            ) as resultPromise in return resultPromise
        in
        let actualPromise = awaitLoop () in
        let valueThunk () = awaitValue actualPromise in
        let cancelThunk () = send cancel callNo in
        let changeMind x = cancelThunk (); send call (x, callNo) in
        return (valueThunk, cancelThunk, changeMind)

let rec awaitCancel callNo runBeforeStall =
    promise (cancel callNo' |->
        if callNo = callNo' then
            promise (dummy empty |-> return <<empty>>) as dummyPromise in
            runBeforeStall ();
            awaitValue dummyPromise;
            awaitCancel callNo runBeforeStall
        else
            awaitCancel callNo runBeforeStall
    ) as p in return p

let remote f =
    let rec loop () =
        promise (call (x, callNo) |->
            awaitCancel callNo loop;
            let y = f x in
            send result (y, callNo);
            loop ()
        ) as p in return p
    in
    loop ()

let remoteCallReInvoker () =
    let callsToReInvoke = ref [] in
    let rec reInvokerCall () =
        promise (call (x,callNo) |->
            callsToReInvoke := !callsToReInvoke @ [(x, callNo)];
            reInvokerCall ()
        ) as _ in return <<()>>
    in
    let rec reInvokerResult () =
        promise (result (y, callNo) |->
            callsToReInvoke := filter (fun (_, callNo') |-> callNo <> callNo') !callsToReInvoke;
            reInvokerResult ()
        ) as _ in return <<()>>
    in
    let rec reInvokerWrapper (calls:(int * int) list) =
        match calls with
        | [] |-> return ()
        | (x, callNo) :: calls |-> send call (x, callNo); reInvokerWrapper calls
    in
    let rec reInvokerCancel () =
        promise (cancel callNo |->
            callsToReInvoke := filter (fun (_, callNo') |-> callNo <> callNo') !callsToReInvoke;
            reInvokerWrapper !callsToReInvoke;
            reInvokerCancel ()
        ) as _ in return <<()>>
    in
    reInvokerCall ();
    reInvokerResult ();
    reInvokerCancel ()

run
    remoteCallReInvoker ()

run
    let callCounter = ref 0 in
    let result1, cancel1, changeMind1 = callWith callCounter 10 in
    let result2, cancel2, changeMind2 = callWith callCounter 20 in
    cancel1 ();
    let result3, cancel3, changeMind3 = callWith callCounter 30 in
    changeMind3 (result2 ());
    result3 ()

run
    remote (fun x |-> 10 * (20 * (30 * x)))"

let feed =
  "operation request : int
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

let heapPure =
  "type loc = int
type val = int

type payloadRec =
  | LookupReq of loc
  | UpdateReq of loc * int
  | AllocReq of val

type payloadRes =
  | LookupRes of int
  | UpdateRes of unit
  | AllocRes of loc

operation opReq : payloadRec * int
operation opRes : payloadRes * int

let empty = []

let rec lookupHeap ((l', v) :: heap') l =
  if l = l' then v else lookupHeap heap' l

let rec updateHeap ((l', v') :: heap') l v =
  if l = l' then (l, v) :: heap' else (l', v') :: updateHeap heap' l v

let allocHeap heap v =
  let l = length heap in
  (l, v) :: heap, l

let rec heapRunner heap =
    promise (opReq (reqPayload, callNo) |->
        let heap', resPayload =
            match reqPayload with
            | LookupReq l |->
                let v = lookupHeap heap l in
                return (heap, LookupRes v)
            | UpdateReq (l, v) |->
                let heap' = updateHeap heap l v in
                return (heap', UpdateRes ())
            | AllocReq v |->
                let heap', l = allocHeap heap v in
                return (heap', AllocRes l)
        in
        send opRes (resPayload, callNo);
        heapRunner heap'
    )
    as p in return p

let callWith callCounter x =
    let callNo = !callCounter in
    send opReq (x, callNo);
    callCounter := callNo + 1;
    promise (opRes (y, callNo') when callNo = callNo' |->
        return <<y>>
    ) as p in awaitValue p

let lookup callCounter l =
    match callWith callCounter (LookupReq l) with LookupRes v |-> return v
let update callCounter l v =
    match callWith callCounter (UpdateReq (l, v)) with UpdateRes () |-> return ()
let alloc callCounter v =
    match callWith callCounter (AllocReq v) with AllocRes l |-> return l

run
    let callCounter = ref 0 in
    let l = alloc callCounter 0 in
    let l' = alloc callCounter 10 in
    update callCounter l 10;
    update callCounter l' (lookup callCounter l + 4);
    return (lookup callCounter l, lookup callCounter l')

run
    heapRunner []"

let heapRef =
  "type callId = int
type loc = int
type val = int

operation lookupReq : loc * callId
operation updateReq : loc * val * callId
operation allocReq : val * callId

operation lookupRes : val * callId
operation updateRes : callId
operation allocRes : loc * callId

let empty = []

let rec lookupHeap ((l', v) :: heap') l =
  if l = l' then v else lookupHeap heap' l

let rec updateHeap ((l', v') :: heap') l v =
  if l = l' then (l, v) :: heap' else (l', v') :: updateHeap heap' l v

let allocHeap heap v =
  let l = length heap in
  (l, v) :: heap, l

let heapRunner () =
    let heap = ref empty in
    let rec awaitLookup () =
        promise (lookupReq (l, callId) |->
            let v = lookupHeap !heap l in
            send lookupRes (v, callId);
            awaitLookup ()
        ) as p in return p
    in
    let rec awaitUpdate () =
        promise (updateReq (l, v, callId) |->
            let heap' = updateHeap !heap l v in
            send updateRes callId;
            heap := heap';
            awaitUpdate ()
        ) as p in return p
    in
    let rec awaitAlloc () =
        promise (allocReq (v, callId) |->
            let heap', l = allocHeap !heap v in
            send allocRes (l, callId);
            heap := heap';
            awaitAlloc ()
        ) as p in return p
    in
    awaitLookup ();
    awaitUpdate ();
    awaitAlloc ()

let lookup callCounter l =
    let callNo = !callCounter in
    send lookupReq (l, callNo);
    callCounter := callNo + 1;
    promise (lookupRes (v, callNo') when callNo = callNo' |->
        return <<v>>
    ) as p in awaitValue p

let update callCounter l v =
    let callNo = !callCounter in
    send updateReq (l, v, callNo);
    callCounter := callNo + 1;
    promise (updateRes (callNo') when callNo = callNo' |->
        return <<()>>
    ) as p in awaitValue p

let alloc callCounter v =
    let callNo = !callCounter in
    send allocReq (v, callNo);
    callCounter := callNo + 1;
    promise (allocRes (l, callNo') when callNo = callNo' |->
        return <<l>>
    ) as p in awaitValue p

run
    let callCounter = ref 0 in
    let l = alloc callCounter 0 in
    let l' = alloc callCounter 10 in
    update callCounter l 10;
    update callCounter l' (lookup callCounter l + 4);
    return (lookup callCounter l, lookup callCounter l')

run
    heapRunner ()"

let preemptive =
  "operation stop : int
operation go : int

(*
let rec preempt () =
  promise (stop _ |->
    promise (go _ |->
      return <<()>>
    ) as p in
    await p until <<y>> in
    preempt ()
  ) as p in
  p
*)

let rec waitForStop threadID =
  promise (stop threadID' when threadID = threadID' |->
    promise (go threadID' when threadID = threadID' |->
      <<()>>
    ) as p in
    await p until <<_>> in
    waitForStop threadID
  ) as p in
  p

run
  waitForStop 1; 1 + 1 + 1 + 1 + 1

run
  waitForStop 2; 10 + 10 + 10 + 10 + 10
  "

let process_with =
  "operation listInterrupt : int list
operation productSignal : int

let process_with p comp cont =
  promise (listInterrupt _ |->
    await p until <<x>> in
    let y = comp x in
    return <<y>>) as q in
  cont q

run
  promise (listInterrupt is |-> return <<is>>) as p in
  process_with p (filter (fun i |-> i > 0)) (fun q |->
  process_with q (fold_left (fun j j' |-> j * j') 1) (fun r |-> 
  process_with r (fun k |-> send productSignal k) (fun _ |->
  (fun _ |-> return r) ()
  )))

run
  send listInterrupt [-3;-2;-1;0;1;2;3]

"

let remoteCall =
  "operation call : int * int
operation result : int * int

let naiveCallWith x =
    send call x;
    promise (result y |-> return <<y>>) as p in
    fun () |-> return awaitValue p

let callWith callCounter =
    fun x |->
        let callNo = !callCounter in
        send call (x, callNo);
        callCounter := callNo + 1;
        promise (result (y, callNo') when callNo = callNo' |->
            return <<y>>
        ) as p in
        let valueThunk () = awaitValue p in
        return valueThunk

let remote f =
    let rec loop () =
        promise (call (x, callNo) |->
            let y = f x in
            send result (y, callNo);
            loop ()
        ) as p in return p
    in
    loop ()

run
    let callCounter = ref 0 in
    let yt = callWith callCounter 20 in
    let zt = callWith callCounter 30 in
    return (yt () * yt () + zt () * zt ())

run
    remote (fun x |-> 10 * (20 * (30 * x)))"

let runner =
  "operation randomReq : int
operation randomRes : int * int

let lcgRunner modulus a c seed =
    let rec loop seed =
        promise (randomReq callNo |->
            let seed' = (a * seed + c) mod modulus in
            send randomRes (callNo, seed);
            loop seed'
        ) as p in return p
    in
    loop seed

let randomDigit callCounter =
    let callNo = !callCounter in
    send randomReq callNo;
    callCounter := callNo + 1;
    promise (randomRes (callNo', seed) when callNo = callNo' |->
        return <<seed mod 10>>
    ) as p in
    awaitValue p

run
    lcgRunner 1234 567 89 1

run
    let callCounter = ref 0 in
    (randomDigit callCounter, randomDigit callCounter, randomDigit callCounter, randomDigit callCounter)"

let ticktock =
  "operation tick : int
operation tock : int

let ticktock () =
  send tick 1;
  send tock 2

run
  ticktock ()
  "

let examples =
  [
    ("Asynchronous computation", async);
    ("Cancellable calls", cancellableCall);
    ("Client feed", feed);
    ("Pure heap", heapPure);
    ("Heap with references", heapRef);
    ("Post-processing", process_with);
    ("Preemptive multi-threading", preemptive);
    ("Remote call", remoteCall);
    ("Runners", runner);
    ("Timer", ticktock);
  ]
