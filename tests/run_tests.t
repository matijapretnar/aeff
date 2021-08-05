  $ for f in *.aeff
  > do
  >   echo "======================================================================"
  >   echo $f
  >   echo "======================================================================"
  >   ../aeff.exe --fixed-random-seed $f
  >   :  # this command is here to suppress potential non-zero exit codes in the output
  > done
  ======================================================================
  async.aeff
  ======================================================================
  ↑ question [fun () ↦ (+) (3, 3)]
  ↑ answer 6
  The process has terminated in the configuration:
  run (return ⟨()⟩) ||  run (return 42)
  ======================================================================
  cancellableCall.aeff
  ======================================================================
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
  heapPure.aeff
  ======================================================================
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
  heapRef.aeff
  ======================================================================
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
  preemptive.aeff
  ======================================================================
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
  process_with.aeff
  ======================================================================
  ↑ listInterrupt -3::-2::-1::0::1::2::3::[]
  ↑ productSignal 6
  The process has terminated in the configuration:
  run (return ()) ||  run (return ⟨6⟩)
  ======================================================================
  remoteCall.aeff
  ======================================================================
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
  runner.aeff
  ======================================================================
  ↑ randomReq 0
  ↑ randomRes (0, 1)
  ↑ randomReq 1
  ↑ randomRes (1, 656)
  ↑ randomReq 2
  ↑ randomRes (2, 607)
  ↑ randomReq 3
  ↑ randomRes (3, 1206)
  The process has terminated in the configuration:
  run (return (1, 6, 7, 6))
  || 
  run promise (randomReq callNo ↦
               let seed' =
                  let b = let b = (*) (567, 255) in (+) (b, 89) in
                  (mod) (b, 1234) in
               ↑randomRes((callNo, 255), return ()); (rec loop ...) seed')
      as p in
      return p
  ======================================================================
  select.aeff
  ======================================================================
  ↑ op2 2
  ↑ op1 1
  The process has terminated in the configuration:
  run (return 625) ||  run (return ()) ||  run (return ())
  ======================================================================
  spawnProcess.aeff
  ======================================================================
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
  theGoodTheBadAndTheUgly.aeff
  ======================================================================
  The process has terminated in the configuration:
  run (return ())
