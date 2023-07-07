  $ for f in *.aeff examples/*.aeff
  > do
  >   echo "======================================================================"
  >   echo $f
  >   echo "======================================================================"
  >   ../aeff.exe --fixed-random-seed $f
  >   :  # this command is here to suppress potential non-zero exit codes in the output
  > done
  ======================================================================
  theGoodTheBadAndTheUgly.aeff
  ======================================================================
  val (=) : α × α → bool
  val (<) : α × α → bool
  val (>) : α × α → bool
  val (<=) : α × α → bool
  val (>=) : α × α → bool
  val (<>) : α × α → bool
  val (~-) : int → int
  val (+) : int × int → int
  val (*) : int × int → int
  val (-) : int × int → int
  val (mod) : int × int → int
  val (/) : int × int → int
  val ref : α → α ref
  val (!) : α ref → α
  val (:=) : α ref × α → unit
  val toString : α → string
  val absurd : α → β
  val not : bool → bool
  type option
  val assoc : α → (α × β) list → β option
  val range : int → int → int list
  val reverse : α list → α list
  val map : (α → β) → α list → β list
  val hd : α list → α
  val tl : α list → α list
  val take : (int → α) → int → α list
  val fold_left : (α → β → α) → α → β list → α
  val fold_right : (α → β → β) → α list → β → β
  val iter : (α → β) → α list → unit
  val forall : (α → bool) → α list → bool
  val exists : (α → bool) → α list → bool
  val mem : α → α list → bool
  val filter : (α → bool) → α list → α list
  val complement : α list → α list → α list
  val intersection : α list → α list → α list
  val zip : α list → β list → (α × β) list
  val unzip : (α × β) list → α list × β list
  val (@) : α list × α list → α list
  val length : α list → int
  val nth : α list → int → α
  val abs : int → int
  val min : α → α → α
  val max : α → α → α
  val gcd : int → int → int
  val lcm : int → int → int
  val odd : int → bool
  val even : int → bool
  val id : α → α
  val compose : (α → β) → (γ → α) → γ → β
  val (|>) : α → (α → β) → β
  val ignore : α → unit
  val fst : α × β → α
  val snd : α × β → β
  val return : α → α
  val awaitValue : ⟨α⟩ → α
  type mobile_list
  operation the_good : (unit → int) mobile_list
  type left1
  type right1
  operation and_the_ugly : int left1
  type foo
  operation bar1 : (⟨int⟩, int) foo
  The process has terminated in the configuration:
  run (return ())
  ======================================================================
  examples/async.aeff
  ======================================================================
  val (=) : α × α → bool
  val (<) : α × α → bool
  val (>) : α × α → bool
  val (<=) : α × α → bool
  val (>=) : α × α → bool
  val (<>) : α × α → bool
  val (~-) : int → int
  val (+) : int × int → int
  val (*) : int × int → int
  val (-) : int × int → int
  val (mod) : int × int → int
  val (/) : int × int → int
  val ref : α → α ref
  val (!) : α ref → α
  val (:=) : α ref × α → unit
  val toString : α → string
  val absurd : α → β
  val not : bool → bool
  type option
  val assoc : α → (α × β) list → β option
  val range : int → int → int list
  val reverse : α list → α list
  val map : (α → β) → α list → β list
  val hd : α list → α
  val tl : α list → α list
  val take : (int → α) → int → α list
  val fold_left : (α → β → α) → α → β list → α
  val fold_right : (α → β → β) → α list → β → β
  val iter : (α → β) → α list → unit
  val forall : (α → bool) → α list → bool
  val exists : (α → bool) → α list → bool
  val mem : α → α list → bool
  val filter : (α → bool) → α list → α list
  val complement : α list → α list → α list
  val intersection : α list → α list → α list
  val zip : α list → β list → (α × β) list
  val unzip : (α × β) list → α list × β list
  val (@) : α list × α list → α list
  val length : α list → int
  val nth : α list → int → α
  val abs : int → int
  val min : α → α → α
  val max : α → α → α
  val gcd : int → int → int
  val lcm : int → int → int
  val odd : int → bool
  val even : int → bool
  val id : α → α
  val compose : (α → β) → (γ → α) → γ → β
  val (|>) : α → (α → β) → β
  val ignore : α → unit
  val fst : α × β → α
  val snd : α × β → β
  val return : α → α
  val awaitValue : ⟨α⟩ → α
  operation question : [(unit → int)]
  operation answer : int
  val get_answer : [(unit → int)] → ⟨int⟩
  ↑ question [fun () ↦ (+) (3, 3)]
  ↑ answer 6
  The process has terminated in the configuration:
  run (return ⟨()⟩) ||  run (return 42)
  ======================================================================
  examples/cancellableCall.aeff
  ======================================================================
  val (=) : α × α → bool
  val (<) : α × α → bool
  val (>) : α × α → bool
  val (<=) : α × α → bool
  val (>=) : α × α → bool
  val (<>) : α × α → bool
  val (~-) : int → int
  val (+) : int × int → int
  val (*) : int × int → int
  val (-) : int × int → int
  val (mod) : int × int → int
  val (/) : int × int → int
  val ref : α → α ref
  val (!) : α ref → α
  val (:=) : α ref × α → unit
  val toString : α → string
  val absurd : α → β
  val not : bool → bool
  type option
  val assoc : α → (α × β) list → β option
  val range : int → int → int list
  val reverse : α list → α list
  val map : (α → β) → α list → β list
  val hd : α list → α
  val tl : α list → α list
  val take : (int → α) → int → α list
  val fold_left : (α → β → α) → α → β list → α
  val fold_right : (α → β → β) → α list → β → β
  val iter : (α → β) → α list → unit
  val forall : (α → bool) → α list → bool
  val exists : (α → bool) → α list → bool
  val mem : α → α list → bool
  val filter : (α → bool) → α list → α list
  val complement : α list → α list → α list
  val intersection : α list → α list → α list
  val zip : α list → β list → (α × β) list
  val unzip : (α × β) list → α list × β list
  val (@) : α list × α list → α list
  val length : α list → int
  val nth : α list → int → α
  val abs : int → int
  val min : α → α → α
  val max : α → α → α
  val gcd : int → int → int
  val lcm : int → int → int
  val odd : int → bool
  val even : int → bool
  val id : α → α
  val compose : (α → β) → (γ → α) → γ → β
  val (|>) : α → (α → β) → β
  val ignore : α → unit
  val fst : α × β → α
  val snd : α × β → β
  val return : α → α
  val awaitValue : ⟨α⟩ → α
  operation call : int × int
  operation result : int × int
  operation cancel : int
  operation dummy : empty
  val callWith : int ref → int → (unit → int) × (unit → unit) × 
                 (int → unit)
  val awaitCancel : int → (unit → α) → ⟨β⟩
  val remote : (int → int) → ⟨α⟩
  val remoteCallReInvoker : unit → ⟨unit⟩
  ↑ call (1, 0)
  ↑ call (2, 1)
  ↑ result (120, 0)
  ↑ cancel 0
  ↑ call (3, 2)
  ↑ result (360, 2)
  ↑ call (2, 1)
  ↑ result (240, 1)
  ↑ cancel 2
  ↑ call (240, 2)
  ↑ result (28800, 2)
  The process has terminated in the configuration:
  run promise (dummy empty ↦ return ⟨empty⟩)
      as dummyPromise in
      promise (dummy empty ↦ return ⟨empty⟩)
      as dummyPromise in
      promise (cancel callNo' k ↦
               let b = (=) (2, callNo') in
               match b with (true ↦ promise (dummy empty ↦
                                               return ⟨empty⟩)
                                      as dummyPromise in
                                      (rec loop ...) ();
                                      awaitValue dummyPromise;
                                      let b = (rec awaitCancel ...) 2 in
                                      b (rec loop ...) | false ↦ k ()))
      as p in
      promise (call (x, callNo) ↦
               let b = awaitCancel callNo in b (rec loop ...);
               let y =
                  (fun x ↦ let b = let b = (*) (6, x) in (*) (5, b) in
                             (*) (4, b))
                  x in ↑result((y, callNo), return ()); (rec loop ...) ())
      as p in
      ↓call((240, 2),
              let p =
                 await dummyPromise until ⟨value⟩ in return value;
                 let b = (rec awaitCancel ...) 2 in b (rec loop ...) in
              ↓cancel(2,
                        promise (cancel callNo' k ↦
                                 let b = (=) (1, callNo') in
                                 match b with (true ↦ promise (dummy empty ↦
                                                                 return
                                                                 ⟨empty⟩)
                                                        as dummyPromise in
                                                        (rec loop ...) ();
                                                        awaitValue dummyPromise;
                                                        let b =
                                                           (rec awaitCancel ...)
                                                           1 in
                                                        b (rec loop ...) | 
                                               false ↦ k ()))
                        as p in
                        promise (call (x, callNo) ↦
                                 let b = awaitCancel callNo in b (rec loop ...);
                                 let y =
                                    (fun x ↦ let b =
                                                  let b = (*) (6, x) in
                                                  (*) (5, b) in (*) (4, b))
                                    x in
                                 ↑result((y, callNo), return ());
                                 (rec loop ...) ())
                        as p in
                        ↓call((2, 1),
                                ↓call((3, 2),
                                        let p =
                                           await dummyPromise until ⟨value⟩ in
                                           return value;
                                           let b = (rec awaitCancel ...) 0 in
                                           b (rec loop ...) in
                                        ↓cancel(0,
                                                  promise (cancel callNo' k ↦
                                                           let b =
                                                              (=) (1, callNo') in
                                                           match b with (
                                                           true ↦ promise (
                                                                    dummy empty ↦
                                                                    return
                                                                    ⟨empty⟩)
                                                                    as dummyPromise in
                                                                    (rec loop ...)
                                                                    ();
                                                                    awaitValue
                                                                    dummyPromise;
                                                                    let
                                                                     b =
                                                                    (rec awaitCancel ...)
                                                                    1 in
                                                                    b
                                                                    (rec loop ...) | 
                                                           false ↦ k ()))
                                                  as p in
                                                  let p =
                                                     let y =
                                                        let b =
                                                           let b = (*) (6, 2) in
                                                           (*) (5, b) in
                                                        (*) (4, b) in
                                                     ↑result((y, 1),
                                                               return ());
                                                     (rec loop ...) () in
                                                  ↓call((2, 1),
                                                          ↓call((1, 0),
                                                                  return p)))))))
  || 
  run promise (call (x, callNo) ↦
               let b = (!) { contents = [] } in
               (:=) ({ contents = [] }, (x, callNo)::b);
               (rec reInvokerCall ...) ())
      as _ in
      promise (result (y, callNo) ↦
               let b =
                  let b = filter (fun (_, callNo') ↦ (<>) (callNo, callNo')) in
                  let b = (!) { contents = [] } in b b in
               (:=) ({ contents = [] }, b); (rec reInvokerResult ...) ())
      as _ in
      promise (cancel callNo ↦
               let b =
                  let b = filter (fun (_, callNo') ↦ (<>) (callNo, callNo')) in
                  let b = (!) { contents = [] } in b b in
               (:=) ({ contents = [] }, b);
               let b = let b = (!) { contents = [] } in reverse b in
               (rec reInvokerWrapper ...) b; (rec reInvokerCancel ...) ())
      as _ in
      return ⟨()⟩
  || 
  run (return 360)
  ======================================================================
  examples/feed.aeff
  ======================================================================
  val (=) : α × α → bool
  val (<) : α × α → bool
  val (>) : α × α → bool
  val (<=) : α × α → bool
  val (>=) : α × α → bool
  val (<>) : α × α → bool
  val (~-) : int → int
  val (+) : int × int → int
  val (*) : int × int → int
  val (-) : int × int → int
  val (mod) : int × int → int
  val (/) : int × int → int
  val ref : α → α ref
  val (!) : α ref → α
  val (:=) : α ref × α → unit
  val toString : α → string
  val absurd : α → β
  val not : bool → bool
  type option
  val assoc : α → (α × β) list → β option
  val range : int → int → int list
  val reverse : α list → α list
  val map : (α → β) → α list → β list
  val hd : α list → α
  val tl : α list → α list
  val take : (int → α) → int → α list
  val fold_left : (α → β → α) → α → β list → α
  val fold_right : (α → β → β) → α list → β → β
  val iter : (α → β) → α list → unit
  val forall : (α → bool) → α list → bool
  val exists : (α → bool) → α list → bool
  val mem : α → α list → bool
  val filter : (α → bool) → α list → α list
  val complement : α list → α list → α list
  val intersection : α list → α list → α list
  val zip : α list → β list → (α × β) list
  val unzip : (α × β) list → α list × β list
  val (@) : α list × α list → α list
  val length : α list → int
  val nth : α list → int → α
  val abs : int → int
  val min : α → α → α
  val max : α → α → α
  val gcd : int → int → int
  val lcm : int → int → int
  val odd : int → bool
  val even : int → bool
  val id : α → α
  val compose : (α → β) → (γ → α) → γ → β
  val (|>) : α → (α → β) → β
  val ignore : α → unit
  val fst : α × β → α
  val snd : α × β → β
  val return : α → α
  val awaitValue : ⟨α⟩ → α
  operation request : int
  operation response : int list
  operation nextItem : unit
  operation display : string
  operation batchSizeRequest : unit
  operation batchSizeResponse : int
  val client : unit → ⟨α⟩
  val server : int → ⟨α⟩
  val user : int → unit
  ↑ nextItem ()
  ↑ batchSizeRequest ()
  ↑ batchSizeResponse 42
  ↑ request 1
  ↑ display "please wait a bit and try again"
  ↑ nextItem ()
  ↑ display "please wait a bit and try again"
  ↑ nextItem ()
  ↑ display "please wait a bit and try again"
  ↑ nextItem ()
  ↑ display "please wait a bit and try again"
  ↑ nextItem ()
  ↑ display "please wait a bit and try again"
  ↑ nextItem ()
  ↑ display "please wait a bit and try again"
  ↑ nextItem ()
  ↑ display "please wait a bit and try again"
  ↑ nextItem ()
  ↑ display "please wait a bit and try again"
  ↑ nextItem ()
  ↑ display "please wait a bit and try again"
  ↑ nextItem ()
  ↑ display "please wait a bit and try again"
  ↑ nextItem ()
  ↑ display "please wait a bit and try again"
  ↑ nextItem ()
  ↑ response 10::20::30::40::50::60::70::80::90::100::110::120::130::140::150::160::170::180::190::200::210::220::230::240::250::260::270::280::290::300::310::320::330::340::350::360::370::380::390::400::410::420::[]
  ↑ request 1
  ↑ nextItem ()
  ↑ nextItem ()
  ↑ display "please wait a bit and try again"
  ↑ nextItem ()
  ↑ nextItem ()
  ↑ nextItem ()
  ↑ nextItem ()
  ↑ nextItem ()
  ↑ nextItem ()
  ↑ display "10"
  ↑ nextItem ()
  ↑ nextItem ()
  ↑ response 10::20::30::40::50::60::70::80::90::100::110::120::130::140::150::160::170::180::190::200::210::220::230::240::250::260::270::280::290::300::310::320::330::340::350::360::370::380::390::400::410::420::[]
  ↑ nextItem ()
  ↑ nextItem ()
  ↑ display "20"
  ↑ nextItem ()
  ↑ nextItem ()
  ↑ nextItem ()
  ↑ nextItem ()
  ↑ nextItem ()
  ↑ nextItem ()
  ↑ display "30"
  ↑ nextItem ()
  ↑ nextItem ()
  ↑ nextItem ()
  ↑ nextItem ()
  ↑ nextItem ()
  ↑ nextItem ()
  ↑ display "40"
  ↑ nextItem ()
  ↑ nextItem ()
  ↑ nextItem ()
  ↑ nextItem ()
  ↑ nextItem ()
  ↑ display "50"
  ↑ nextItem ()
  ↑ display "60"
  ↑ display "70"
  ↑ display "80"
  ↑ display "90"
  ↑ display "100"
  ↑ display "110"
  ↑ display "120"
  ↑ display "130"
  ↑ display "140"
  ↑ display "150"
  ↑ display "160"
  ↑ display "170"
  ↑ display "180"
  ↑ display "190"
  ↑ display "200"
  ↑ display "210"
  ↑ display "220"
  ↑ display "230"
  ↑ display "240"
  ↑ display "250"
  ↑ display "260"
  ↑ display "270"
  ↑ display "280"
  ↑ display "290"
  ↑ display "300"
  The process has terminated in the configuration:
  run (return ())
  || 
  run promise (nextItem () ↦
               let cachedSize =
                  let b =
                     (!)
                     { contents = 10::20::30::40::50::60::70::80::90::100::110::120::130::140::150::160::170::180::190::200::210::220::230::240::250::260::270::280::290::300::310::320::330::340::350::360::370::380::390::400::410::420::10::20::30::40::50::60::70::80::90::100::110::120::130::140::150::160::170::180::190::200::210::220::230::240::250::260::270::280::290::300::310::320::330::340::350::360::370::380::390::400::410::420::[] } in
                  length b in
               let b =
                  let b =
                     let b = (!) { contents = 30 } in
                     let b = let b = (/) (42, 2) in (-) (cachedSize, b) in
                     (>) (b, b) in
                  match b with (true ↦ let b = (!) { contents = false } in
                                         not b | false ↦ return false) in
               match b with (true ↦ let b = (+) (cachedSize, 1) in
                                      (fun offset ↦ (:=)
                                                      ({ contents = false }, 
                                                       true);
                                                      ↑request(offset,
                                                                 return ());
                                                      promise (response newBatch ↦
                                                               let b =
                                                                  let b =
                                                                     (!)
                                                                     { contents = 10::20::30::40::50::60::70::80::90::100::110::120::130::140::150::160::170::180::190::200::210::220::230::240::250::260::270::280::290::300::310::320::330::340::350::360::370::380::390::400::410::420::10::20::30::40::50::60::70::80::90::100::110::120::130::140::150::160::170::180::190::200::210::220::230::240::250::260::270::280::290::300::310::320::330::340::350::360::370::380::390::400::410::420::[] } in
                                                                  (@)
                                                                  (b, newBatch) in
                                                               (:=)
                                                               ({ contents = 10::20::30::40::50::60::70::80::90::100::110::120::130::140::150::160::170::180::190::200::210::220::230::240::250::260::270::280::290::300::310::320::330::340::350::360::370::380::390::400::410::420::10::20::30::40::50::60::70::80::90::100::110::120::130::140::150::160::170::180::190::200::210::220::230::240::250::260::270::280::290::300::310::320::330::340::350::360::370::380::390::400::410::420::[] }, 
                                                                b);
                                                               (:=)
                                                               ({ contents = false }, 
                                                                false);
                                                               return ⟨()⟩)
                                                      as _ in
                                                      return ())
                                      b | false ↦ return ());
               let b = let b = (!) { contents = 30 } in (<) (b, cachedSize) in
               match b with (true ↦ let b =
                                         let b =
                                            let b =
                                               let b =
                                                  (!)
                                                  { contents = 10::20::30::40::50::60::70::80::90::100::110::120::130::140::150::160::170::180::190::200::210::220::230::240::250::260::270::280::290::300::310::320::330::340::350::360::370::380::390::400::410::420::10::20::30::40::50::60::70::80::90::100::110::120::130::140::150::160::170::180::190::200::210::220::230::240::250::260::270::280::290::300::310::320::330::340::350::360::370::380::390::400::410::420::[] } in
                                               nth b in
                                            let b = (!) { contents = 30 } in
                                            b b in toString b in
                                      ↑display(b, return ());
                                      let b =
                                         let b = (!) { contents = 30 } in
                                         (+) (b, 1) in
                                      (:=) ({ contents = 30 }, b) | 
                             false ↦ ↑display("please wait a bit and try again",
                                                  return ()));
               (rec clientLoop ...) 42)
      as p in
      return p
  || 
  run promise (batchSizeRequest () ↦
               ↑batchSizeResponse(42, return ());
               (rec waitForBatchSize ...) ())
      as p in
      promise (request offset ↦
               let payload =
                  let b = map (fun x ↦ (*) (10, x)) in
                  let b =
                     let b = range offset in
                     let b = let b = (-) (42, 1) in (+) (offset, b) in b b in
                  b b in
               ↑response(payload, return ()); (rec waitForRequest ...) ())
      as p in
      return p
  ======================================================================
  examples/heapPure.aeff
  ======================================================================
  val (=) : α × α → bool
  val (<) : α × α → bool
  val (>) : α × α → bool
  val (<=) : α × α → bool
  val (>=) : α × α → bool
  val (<>) : α × α → bool
  val (~-) : int → int
  val (+) : int × int → int
  val (*) : int × int → int
  val (-) : int × int → int
  val (mod) : int × int → int
  val (/) : int × int → int
  val ref : α → α ref
  val (!) : α ref → α
  val (:=) : α ref × α → unit
  val toString : α → string
  val absurd : α → β
  val not : bool → bool
  type option
  val assoc : α → (α × β) list → β option
  val range : int → int → int list
  val reverse : α list → α list
  val map : (α → β) → α list → β list
  val hd : α list → α
  val tl : α list → α list
  val take : (int → α) → int → α list
  val fold_left : (α → β → α) → α → β list → α
  val fold_right : (α → β → β) → α list → β → β
  val iter : (α → β) → α list → unit
  val forall : (α → bool) → α list → bool
  val exists : (α → bool) → α list → bool
  val mem : α → α list → bool
  val filter : (α → bool) → α list → α list
  val complement : α list → α list → α list
  val intersection : α list → α list → α list
  val zip : α list → β list → (α × β) list
  val unzip : (α × β) list → α list × β list
  val (@) : α list × α list → α list
  val length : α list → int
  val nth : α list → int → α
  val abs : int → int
  val min : α → α → α
  val max : α → α → α
  val gcd : int → int → int
  val lcm : int → int → int
  val odd : int → bool
  val even : int → bool
  val id : α → α
  val compose : (α → β) → (γ → α) → γ → β
  val (|>) : α → (α → β) → β
  val ignore : α → unit
  val fst : α × β → α
  val snd : α × β → β
  val return : α → α
  val awaitValue : ⟨α⟩ → α
  type loc
  type val
  type payloadRec
  type payloadRes
  operation opReq : payloadRec × int
  operation opRes : payloadRes × int
  val empty : α list
  val lookupHeap : (α × β) list → α → β
  val updateHeap : (α × β) list → α → β → (α × β) list
  val allocHeap : (int × α) list → α → (int × α) list × int
  val heapRunner : (int × int) list → ⟨α⟩
  val callWith : int ref → payloadRec → payloadRes
  val lookup : int ref → int → int
  val update : int ref → int → int → unit
  val alloc : int ref → int → int
  ↑ opReq (AllocReq 0, 0)
  ↑ opRes (AllocRes 0, 0)
  ↑ opReq (AllocReq 10, 1)
  ↑ opRes (AllocRes 1, 1)
  ↑ opReq (UpdateReq (0, 10), 2)
  ↑ opRes (UpdateRes (), 2)
  ↑ opReq (LookupReq 0, 3)
  ↑ opRes (LookupRes 10, 3)
  ↑ opReq (UpdateReq (1, 14), 4)
  ↑ opRes (UpdateRes (), 4)
  ↑ opReq (LookupReq 0, 5)
  ↑ opRes (LookupRes 10, 5)
  ↑ opReq (LookupReq 1, 6)
  ↑ opRes (LookupRes 14, 6)
  The process has terminated in the configuration:
  run promise (opReq (reqPayload, callNo) ↦
               let (heap', resPayload) =
                  match reqPayload with (LookupReq l ↦ let v =
                                                            let b =
                                                               lookupHeap
                                                               ((1, 14)::(
                                                               0, 10)::[]) in
                                                            b l in
                                                         return
                                                         ((1, 14)::(0, 10)::[], 
                                                          LookupRes v) | 
                                         UpdateReq (l, v) ↦ let heap' =
                                                                 let b =
                                                                    let
                                                                     b =
                                                                    updateHeap
                                                                    ((1, 14)::(
                                                                    0, 10)::[]) in
                                                                    b l in 
                                                                 b v in
                                                              return
                                                              (heap', 
                                                               UpdateRes 
                                                               ()) | 
                                         AllocReq v ↦ let (heap', l) =
                                                           let b =
                                                              allocHeap
                                                              ((1, 14)::(
                                                              0, 10)::[]) in
                                                           b v in
                                                        return
                                                        (heap', AllocRes l)) in
               ↑opRes((resPayload, callNo), return ());
               (rec heapRunner ...) heap')
      as p in
      return p
  || 
  run (return (10, 14))
  ======================================================================
  examples/heapRef.aeff
  ======================================================================
  val (=) : α × α → bool
  val (<) : α × α → bool
  val (>) : α × α → bool
  val (<=) : α × α → bool
  val (>=) : α × α → bool
  val (<>) : α × α → bool
  val (~-) : int → int
  val (+) : int × int → int
  val (*) : int × int → int
  val (-) : int × int → int
  val (mod) : int × int → int
  val (/) : int × int → int
  val ref : α → α ref
  val (!) : α ref → α
  val (:=) : α ref × α → unit
  val toString : α → string
  val absurd : α → β
  val not : bool → bool
  type option
  val assoc : α → (α × β) list → β option
  val range : int → int → int list
  val reverse : α list → α list
  val map : (α → β) → α list → β list
  val hd : α list → α
  val tl : α list → α list
  val take : (int → α) → int → α list
  val fold_left : (α → β → α) → α → β list → α
  val fold_right : (α → β → β) → α list → β → β
  val iter : (α → β) → α list → unit
  val forall : (α → bool) → α list → bool
  val exists : (α → bool) → α list → bool
  val mem : α → α list → bool
  val filter : (α → bool) → α list → α list
  val complement : α list → α list → α list
  val intersection : α list → α list → α list
  val zip : α list → β list → (α × β) list
  val unzip : (α × β) list → α list × β list
  val (@) : α list × α list → α list
  val length : α list → int
  val nth : α list → int → α
  val abs : int → int
  val min : α → α → α
  val max : α → α → α
  val gcd : int → int → int
  val lcm : int → int → int
  val odd : int → bool
  val even : int → bool
  val id : α → α
  val compose : (α → β) → (γ → α) → γ → β
  val (|>) : α → (α → β) → β
  val ignore : α → unit
  val fst : α × β → α
  val snd : α × β → β
  val return : α → α
  val awaitValue : ⟨α⟩ → α
  type callId
  type loc
  type val
  operation lookupReq : loc × callId
  operation updateReq : loc × val × callId
  operation allocReq : val × callId
  operation lookupRes : val × callId
  operation updateRes : callId
  operation allocRes : loc × callId
  val empty : α list
  val lookupHeap : (α × β) list → α → β
  val updateHeap : (α × β) list → α → β → (α × β) list
  val allocHeap : (int × α) list → α → (int × α) list × int
  val heapRunner : unit → ⟨α⟩
  val lookup : int ref → int → int
  val update : int ref → int → int → unit
  val alloc : int ref → int → int
  ↑ allocReq (0, 0)
  ↑ allocRes (0, 0)
  ↑ allocReq (10, 1)
  ↑ allocRes (1, 1)
  ↑ updateReq (0, 10, 2)
  ↑ updateRes 2
  ↑ lookupReq (0, 3)
  ↑ lookupRes (10, 3)
  ↑ updateReq (1, 14, 4)
  ↑ updateRes 4
  ↑ lookupReq (0, 5)
  ↑ lookupRes (10, 5)
  ↑ lookupReq (1, 6)
  ↑ lookupRes (14, 6)
  The process has terminated in the configuration:
  run promise (lookupReq (l, callId) ↦
               let v =
                  let b =
                     let b = (!) { contents = (1, 14)::(0, 10)::empty } in
                     lookupHeap b in b l in
               ↑lookupRes((v, callId), return ()); (rec awaitLookup ...) ())
      as p in
      promise (updateReq (l, v, callId) ↦
               let heap' =
                  let b =
                     let b =
                        let b = (!) { contents = (1, 14)::(0, 10)::empty } in
                        updateHeap b in b l in b v in
               ↑updateRes(callId, return ());
               (:=) ({ contents = (1, 14)::(0, 10)::empty }, heap');
               (rec awaitUpdate ...) ())
      as p in
      promise (allocReq (v, callId) ↦
               let (heap', l) =
                  let b =
                     let b = (!) { contents = (1, 14)::(0, 10)::empty } in
                     allocHeap b in b v in
               ↑allocRes((l, callId), return ());
               (:=) ({ contents = (1, 14)::(0, 10)::empty }, heap');
               (rec awaitAlloc ...) ())
      as p in
      return p
  || 
  run (return (10, 14))
  ======================================================================
  examples/preemptive.aeff
  ======================================================================
  val (=) : α × α → bool
  val (<) : α × α → bool
  val (>) : α × α → bool
  val (<=) : α × α → bool
  val (>=) : α × α → bool
  val (<>) : α × α → bool
  val (~-) : int → int
  val (+) : int × int → int
  val (*) : int × int → int
  val (-) : int × int → int
  val (mod) : int × int → int
  val (/) : int × int → int
  val ref : α → α ref
  val (!) : α ref → α
  val (:=) : α ref × α → unit
  val toString : α → string
  val absurd : α → β
  val not : bool → bool
  type option
  val assoc : α → (α × β) list → β option
  val range : int → int → int list
  val reverse : α list → α list
  val map : (α → β) → α list → β list
  val hd : α list → α
  val tl : α list → α list
  val take : (int → α) → int → α list
  val fold_left : (α → β → α) → α → β list → α
  val fold_right : (α → β → β) → α list → β → β
  val iter : (α → β) → α list → unit
  val forall : (α → bool) → α list → bool
  val exists : (α → bool) → α list → bool
  val mem : α → α list → bool
  val filter : (α → bool) → α list → α list
  val complement : α list → α list → α list
  val intersection : α list → α list → α list
  val zip : α list → β list → (α × β) list
  val unzip : (α × β) list → α list × β list
  val (@) : α list × α list → α list
  val length : α list → int
  val nth : α list → int → α
  val abs : int → int
  val min : α → α → α
  val max : α → α → α
  val gcd : int → int → int
  val lcm : int → int → int
  val odd : int → bool
  val even : int → bool
  val id : α → α
  val compose : (α → β) → (γ → α) → γ → β
  val (|>) : α → (α → β) → β
  val ignore : α → unit
  val fst : α × β → α
  val snd : α × β → β
  val return : α → α
  val awaitValue : ⟨α⟩ → α
  operation stop : int
  operation go : int
  val waitForStop : int → ⟨α⟩
  The process has terminated in the configuration:
  run promise (stop threadID' k ↦
               let b = (=) (2, threadID') in
               match b with (true ↦ promise (go threadID' k ↦
                                               let b = (=) (2, threadID') in
                                               match b with (true ↦ return ⟨()⟩ | 
                                                             false ↦ 
                                                             k ()))
                                      as p in
                                      await p until ⟨_⟩ in
                                      (rec waitForStop ...) 2 | false ↦ 
                             k ()))
      as p in
      return 50
  || 
  run promise (stop threadID' k ↦
               let b = (=) (1, threadID') in
               match b with (true ↦ promise (go threadID' k ↦
                                               let b = (=) (1, threadID') in
                                               match b with (true ↦ return ⟨()⟩ | 
                                                             false ↦ 
                                                             k ()))
                                      as p in
                                      await p until ⟨_⟩ in
                                      (rec waitForStop ...) 1 | false ↦ 
                             k ()))
      as p in
      return 5
  ======================================================================
  examples/process_with.aeff
  ======================================================================
  val (=) : α × α → bool
  val (<) : α × α → bool
  val (>) : α × α → bool
  val (<=) : α × α → bool
  val (>=) : α × α → bool
  val (<>) : α × α → bool
  val (~-) : int → int
  val (+) : int × int → int
  val (*) : int × int → int
  val (-) : int × int → int
  val (mod) : int × int → int
  val (/) : int × int → int
  val ref : α → α ref
  val (!) : α ref → α
  val (:=) : α ref × α → unit
  val toString : α → string
  val absurd : α → β
  val not : bool → bool
  type option
  val assoc : α → (α × β) list → β option
  val range : int → int → int list
  val reverse : α list → α list
  val map : (α → β) → α list → β list
  val hd : α list → α
  val tl : α list → α list
  val take : (int → α) → int → α list
  val fold_left : (α → β → α) → α → β list → α
  val fold_right : (α → β → β) → α list → β → β
  val iter : (α → β) → α list → unit
  val forall : (α → bool) → α list → bool
  val exists : (α → bool) → α list → bool
  val mem : α → α list → bool
  val filter : (α → bool) → α list → α list
  val complement : α list → α list → α list
  val intersection : α list → α list → α list
  val zip : α list → β list → (α × β) list
  val unzip : (α × β) list → α list × β list
  val (@) : α list × α list → α list
  val length : α list → int
  val nth : α list → int → α
  val abs : int → int
  val min : α → α → α
  val max : α → α → α
  val gcd : int → int → int
  val lcm : int → int → int
  val odd : int → bool
  val even : int → bool
  val id : α → α
  val compose : (α → β) → (γ → α) → γ → β
  val (|>) : α → (α → β) → β
  val ignore : α → unit
  val fst : α × β → α
  val snd : α × β → β
  val return : α → α
  val awaitValue : ⟨α⟩ → α
  operation listInterrupt : int list
  operation productSignal : int
  val process_with : ⟨α⟩ → (α → β) → (⟨β⟩ → γ) → γ
  ↑ listInterrupt -3::-2::-1::0::1::2::3::[]
  ↑ productSignal 6
  The process has terminated in the configuration:
  run (return ()) ||  run (return ⟨6⟩)
  ======================================================================
  examples/remoteCall.aeff
  ======================================================================
  val (=) : α × α → bool
  val (<) : α × α → bool
  val (>) : α × α → bool
  val (<=) : α × α → bool
  val (>=) : α × α → bool
  val (<>) : α × α → bool
  val (~-) : int → int
  val (+) : int × int → int
  val (*) : int × int → int
  val (-) : int × int → int
  val (mod) : int × int → int
  val (/) : int × int → int
  val ref : α → α ref
  val (!) : α ref → α
  val (:=) : α ref × α → unit
  val toString : α → string
  val absurd : α → β
  val not : bool → bool
  type option
  val assoc : α → (α × β) list → β option
  val range : int → int → int list
  val reverse : α list → α list
  val map : (α → β) → α list → β list
  val hd : α list → α
  val tl : α list → α list
  val take : (int → α) → int → α list
  val fold_left : (α → β → α) → α → β list → α
  val fold_right : (α → β → β) → α list → β → β
  val iter : (α → β) → α list → unit
  val forall : (α → bool) → α list → bool
  val exists : (α → bool) → α list → bool
  val mem : α → α list → bool
  val filter : (α → bool) → α list → α list
  val complement : α list → α list → α list
  val intersection : α list → α list → α list
  val zip : α list → β list → (α × β) list
  val unzip : (α × β) list → α list × β list
  val (@) : α list × α list → α list
  val length : α list → int
  val nth : α list → int → α
  val abs : int → int
  val min : α → α → α
  val max : α → α → α
  val gcd : int → int → int
  val lcm : int → int → int
  val odd : int → bool
  val even : int → bool
  val id : α → α
  val compose : (α → β) → (γ → α) → γ → β
  val (|>) : α → (α → β) → β
  val ignore : α → unit
  val fst : α × β → α
  val snd : α × β → β
  val return : α → α
  val awaitValue : ⟨α⟩ → α
  operation call : int × int
  operation result : int × int
  val naiveCallWith : int × int → unit → int × int
  val callWith : int ref → int → unit → int
  val remote : (int → int) → ⟨α⟩
  ↑ call (2, 0)
  ↑ result (240, 0)
  ↑ call (3, 1)
  ↑ result (360, 1)
  The process has terminated in the configuration:
  run promise (call (x, callNo) ↦
               let y =
                  (fun x ↦ let b = let b = (*) (6, x) in (*) (5, b) in
                             (*) (4, b))
                  x in ↑result((y, callNo), return ()); (rec loop ...) ())
      as p in
      return p
  || 
  run (return 187200)
  ======================================================================
  examples/runner.aeff
  ======================================================================
  val (=) : α × α → bool
  val (<) : α × α → bool
  val (>) : α × α → bool
  val (<=) : α × α → bool
  val (>=) : α × α → bool
  val (<>) : α × α → bool
  val (~-) : int → int
  val (+) : int × int → int
  val (*) : int × int → int
  val (-) : int × int → int
  val (mod) : int × int → int
  val (/) : int × int → int
  val ref : α → α ref
  val (!) : α ref → α
  val (:=) : α ref × α → unit
  val toString : α → string
  val absurd : α → β
  val not : bool → bool
  type option
  val assoc : α → (α × β) list → β option
  val range : int → int → int list
  val reverse : α list → α list
  val map : (α → β) → α list → β list
  val hd : α list → α
  val tl : α list → α list
  val take : (int → α) → int → α list
  val fold_left : (α → β → α) → α → β list → α
  val fold_right : (α → β → β) → α list → β → β
  val iter : (α → β) → α list → unit
  val forall : (α → bool) → α list → bool
  val exists : (α → bool) → α list → bool
  val mem : α → α list → bool
  val filter : (α → bool) → α list → α list
  val complement : α list → α list → α list
  val intersection : α list → α list → α list
  val zip : α list → β list → (α × β) list
  val unzip : (α × β) list → α list × β list
  val (@) : α list × α list → α list
  val length : α list → int
  val nth : α list → int → α
  val abs : int → int
  val min : α → α → α
  val max : α → α → α
  val gcd : int → int → int
  val lcm : int → int → int
  val odd : int → bool
  val even : int → bool
  val id : α → α
  val compose : (α → β) → (γ → α) → γ → β
  val (|>) : α → (α → β) → β
  val ignore : α → unit
  val fst : α × β → α
  val snd : α × β → β
  val return : α → α
  val awaitValue : ⟨α⟩ → α
  operation randomReq : int
  operation randomRes : int × int
  val lcgRunner : int → int → int → int → ⟨α⟩
  val randomDigit : int ref → int
  ↑ randomReq 0
  ↑ randomRes (0, 1)
  ↑ randomReq 1
  ↑ randomRes (1, 436)
  ↑ randomReq 2
  ↑ randomRes (2, 281)
  ↑ randomReq 3
  ↑ randomRes (3, 10)
  The process has terminated in the configuration:
  run (return (1, 6, 1, 0))
  || 
  run promise (randomReq callNo ↦
               let seed' =
                  let b = let b = (+) (603, 89) in (*) (567, b) in
                  (mod) (b, 1234) in
               ↑randomRes((callNo, 603), return ()); (rec loop ...) seed')
      as p in
      return p
  ======================================================================
  examples/select.aeff
  ======================================================================
  val (=) : α × α → bool
  val (<) : α × α → bool
  val (>) : α × α → bool
  val (<=) : α × α → bool
  val (>=) : α × α → bool
  val (<>) : α × α → bool
  val (~-) : int → int
  val (+) : int × int → int
  val (*) : int × int → int
  val (-) : int × int → int
  val (mod) : int × int → int
  val (/) : int × int → int
  val ref : α → α ref
  val (!) : α ref → α
  val (:=) : α ref × α → unit
  val toString : α → string
  val absurd : α → β
  val not : bool → bool
  type option
  val assoc : α → (α × β) list → β option
  val range : int → int → int list
  val reverse : α list → α list
  val map : (α → β) → α list → β list
  val hd : α list → α
  val tl : α list → α list
  val take : (int → α) → int → α list
  val fold_left : (α → β → α) → α → β list → α
  val fold_right : (α → β → β) → α list → β → β
  val iter : (α → β) → α list → unit
  val forall : (α → bool) → α list → bool
  val exists : (α → bool) → α list → bool
  val mem : α → α list → bool
  val filter : (α → bool) → α list → α list
  val complement : α list → α list → α list
  val intersection : α list → α list → α list
  val zip : α list → β list → (α × β) list
  val unzip : (α × β) list → α list × β list
  val (@) : α list × α list → α list
  val length : α list → int
  val nth : α list → int → α
  val abs : int → int
  val min : α → α → α
  val max : α → α → α
  val gcd : int → int → int
  val lcm : int → int → int
  val odd : int → bool
  val even : int → bool
  val id : α → α
  val compose : (α → β) → (γ → α) → γ → β
  val (|>) : α → (α → β) → β
  val ignore : α → unit
  val fst : α × β → α
  val snd : α × β → β
  val return : α → α
  val awaitValue : ⟨α⟩ → α
  operation op1 : int
  operation op2 : int
  val select : (int → ⟨α⟩) → (int → ⟨α⟩) → (⟨α⟩ → β) → β
  ↑ op2 2
  ↑ op1 1
  The process has terminated in the configuration:
  run (return 625) ||  run (return ()) ||  run (return ())
  ======================================================================
  examples/spawnProcess.aeff
  ======================================================================
  val (=) : α × α → bool
  val (<) : α × α → bool
  val (>) : α × α → bool
  val (<=) : α × α → bool
  val (>=) : α × α → bool
  val (<>) : α × α → bool
  val (~-) : int → int
  val (+) : int × int → int
  val (*) : int × int → int
  val (-) : int × int → int
  val (mod) : int × int → int
  val (/) : int × int → int
  val ref : α → α ref
  val (!) : α ref → α
  val (:=) : α ref × α → unit
  val toString : α → string
  val absurd : α → β
  val not : bool → bool
  type option
  val assoc : α → (α × β) list → β option
  val range : int → int → int list
  val reverse : α list → α list
  val map : (α → β) → α list → β list
  val hd : α list → α
  val tl : α list → α list
  val take : (int → α) → int → α list
  val fold_left : (α → β → α) → α → β list → α
  val fold_right : (α → β → β) → α list → β → β
  val iter : (α → β) → α list → unit
  val forall : (α → bool) → α list → bool
  val exists : (α → bool) → α list → bool
  val mem : α → α list → bool
  val filter : (α → bool) → α list → α list
  val complement : α list → α list → α list
  val intersection : α list → α list → α list
  val zip : α list → β list → (α × β) list
  val unzip : (α × β) list → α list × β list
  val (@) : α list × α list → α list
  val length : α list → int
  val nth : α list → int → α
  val abs : int → int
  val min : α → α → α
  val max : α → α → α
  val gcd : int → int → int
  val lcm : int → int → int
  val odd : int → bool
  val even : int → bool
  val id : α → α
  val compose : (α → β) → (γ → α) → γ → β
  val (|>) : α → (α → β) → β
  val ignore : α → unit
  val fst : α × β → α
  val snd : α × β → β
  val return : α → α
  val awaitValue : ⟨α⟩ → α
  operation task : int × [(int → int)]
  operation result : int × int
  val boxed_func : [(int → int)]
  val parallel_map : [(int → int)] → int list → int list
  ↑ result (1, 2)
  ↑ result (2, 4)
  ↑ result (3, 6)
  ↑ result (4, 8)
  ↑ result (5, 10)
  The process has terminated in the configuration:
  run (return ()) ||  run (return ()) ||  run (return (2::4::6::8::10::[]))
  || 
  run (return ())
  || 
  run (return ())
  || 
  run (return ())
  ======================================================================
  examples/spawnSimple.aeff
  ======================================================================
  val (=) : α × α → bool
  val (<) : α × α → bool
  val (>) : α × α → bool
  val (<=) : α × α → bool
  val (>=) : α × α → bool
  val (<>) : α × α → bool
  val (~-) : int → int
  val (+) : int × int → int
  val (*) : int × int → int
  val (-) : int × int → int
  val (mod) : int × int → int
  val (/) : int × int → int
  val ref : α → α ref
  val (!) : α ref → α
  val (:=) : α ref × α → unit
  val toString : α → string
  val absurd : α → β
  val not : bool → bool
  type option
  val assoc : α → (α × β) list → β option
  val range : int → int → int list
  val reverse : α list → α list
  val map : (α → β) → α list → β list
  val hd : α list → α
  val tl : α list → α list
  val take : (int → α) → int → α list
  val fold_left : (α → β → α) → α → β list → α
  val fold_right : (α → β → β) → α list → β → β
  val iter : (α → β) → α list → unit
  val forall : (α → bool) → α list → bool
  val exists : (α → bool) → α list → bool
  val mem : α → α list → bool
  val filter : (α → bool) → α list → α list
  val complement : α list → α list → α list
  val intersection : α list → α list → α list
  val zip : α list → β list → (α × β) list
  val unzip : (α × β) list → α list × β list
  val (@) : α list × α list → α list
  val length : α list → int
  val nth : α list → int → α
  val abs : int → int
  val min : α → α → α
  val max : α → α → α
  val gcd : int → int → int
  val lcm : int → int → int
  val odd : int → bool
  val even : int → bool
  val id : α → α
  val compose : (α → β) → (γ → α) → γ → β
  val (|>) : α → (α → β) → β
  val ignore : α → unit
  val fst : α × β → α
  val snd : α × β → β
  val return : α → α
  val awaitValue : ⟨α⟩ → α
  operation std_out : string
  ↑ std_out "Hello world"
  The process has terminated in the configuration:
  run (return 42) ||  run (return ())
  ======================================================================
  examples/ticktock.aeff
  ======================================================================
  val (=) : α × α → bool
  val (<) : α × α → bool
  val (>) : α × α → bool
  val (<=) : α × α → bool
  val (>=) : α × α → bool
  val (<>) : α × α → bool
  val (~-) : int → int
  val (+) : int × int → int
  val (*) : int × int → int
  val (-) : int × int → int
  val (mod) : int × int → int
  val (/) : int × int → int
  val ref : α → α ref
  val (!) : α ref → α
  val (:=) : α ref × α → unit
  val toString : α → string
  val absurd : α → β
  val not : bool → bool
  type option
  val assoc : α → (α × β) list → β option
  val range : int → int → int list
  val reverse : α list → α list
  val map : (α → β) → α list → β list
  val hd : α list → α
  val tl : α list → α list
  val take : (int → α) → int → α list
  val fold_left : (α → β → α) → α → β list → α
  val fold_right : (α → β → β) → α list → β → β
  val iter : (α → β) → α list → unit
  val forall : (α → bool) → α list → bool
  val exists : (α → bool) → α list → bool
  val mem : α → α list → bool
  val filter : (α → bool) → α list → α list
  val complement : α list → α list → α list
  val intersection : α list → α list → α list
  val zip : α list → β list → (α × β) list
  val unzip : (α × β) list → α list × β list
  val (@) : α list × α list → α list
  val length : α list → int
  val nth : α list → int → α
  val abs : int → int
  val min : α → α → α
  val max : α → α → α
  val gcd : int → int → int
  val lcm : int → int → int
  val odd : int → bool
  val even : int → bool
  val id : α → α
  val compose : (α → β) → (γ → α) → γ → β
  val (|>) : α → (α → β) → β
  val ignore : α → unit
  val fst : α × β → α
  val snd : α × β → β
  val return : α → α
  val awaitValue : ⟨α⟩ → α
  operation tick : int
  operation tock : int
  val ticktock : unit → unit
  ↑ tick 1
  ↑ tock 2
  The process has terminated in the configuration:
  run (return ())
