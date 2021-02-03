(rule
 (deps
  ../../src/aeff/aeff.exe
  (source_tree .))
   (target "async.aeff.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       0
       (run ../../src/aeff/aeff.exe --fixed-random-seed "./async.aeff")))))

(rule
 (deps "async.aeff.out")
  (alias runtest)
   (action
    (diff "async.aeff.ref" "async.aeff.out")))

(rule
 (deps
  ../../src/aeff/aeff.exe
  (source_tree .))
   (target "cancellableCall.aeff.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       0
       (run ../../src/aeff/aeff.exe --fixed-random-seed "./cancellableCall.aeff")))))

(rule
 (deps "cancellableCall.aeff.out")
  (alias runtest)
   (action
    (diff "cancellableCall.aeff.ref" "cancellableCall.aeff.out")))

(rule
 (deps
  ../../src/aeff/aeff.exe
  (source_tree .))
   (target "heapPure.aeff.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       0
       (run ../../src/aeff/aeff.exe --fixed-random-seed "./heapPure.aeff")))))

(rule
 (deps "heapPure.aeff.out")
  (alias runtest)
   (action
    (diff "heapPure.aeff.ref" "heapPure.aeff.out")))

(rule
 (deps
  ../../src/aeff/aeff.exe
  (source_tree .))
   (target "heapRef.aeff.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       0
       (run ../../src/aeff/aeff.exe --fixed-random-seed "./heapRef.aeff")))))

(rule
 (deps "heapRef.aeff.out")
  (alias runtest)
   (action
    (diff "heapRef.aeff.ref" "heapRef.aeff.out")))

(rule
 (deps
  ../../src/aeff/aeff.exe
  (source_tree .))
   (target "preemptive.aeff.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       0
       (run ../../src/aeff/aeff.exe --fixed-random-seed "./preemptive.aeff")))))

(rule
 (deps "preemptive.aeff.out")
  (alias runtest)
   (action
    (diff "preemptive.aeff.ref" "preemptive.aeff.out")))

(rule
 (deps
  ../../src/aeff/aeff.exe
  (source_tree .))
   (target "process_with.aeff.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       0
       (run ../../src/aeff/aeff.exe --fixed-random-seed "./process_with.aeff")))))

(rule
 (deps "process_with.aeff.out")
  (alias runtest)
   (action
    (diff "process_with.aeff.ref" "process_with.aeff.out")))

(rule
 (deps
  ../../src/aeff/aeff.exe
  (source_tree .))
   (target "remoteCall.aeff.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       0
       (run ../../src/aeff/aeff.exe --fixed-random-seed "./remoteCall.aeff")))))

(rule
 (deps "remoteCall.aeff.out")
  (alias runtest)
   (action
    (diff "remoteCall.aeff.ref" "remoteCall.aeff.out")))

(rule
 (deps
  ../../src/aeff/aeff.exe
  (source_tree .))
   (target "runner.aeff.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       0
       (run ../../src/aeff/aeff.exe --fixed-random-seed "./runner.aeff")))))

(rule
 (deps "runner.aeff.out")
  (alias runtest)
   (action
    (diff "runner.aeff.ref" "runner.aeff.out")))

(rule
 (deps
  ../../src/aeff/aeff.exe
  (source_tree .))
   (target "select.aeff.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       0
       (run ../../src/aeff/aeff.exe --fixed-random-seed "./select.aeff")))))

(rule
 (deps "select.aeff.out")
  (alias runtest)
   (action
    (diff "select.aeff.ref" "select.aeff.out")))

