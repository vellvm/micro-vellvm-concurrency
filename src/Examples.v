From Coq Require Import List String ZArith QArith.
From CTree Require Import CTree.

Unset Universe Checking.
From Mem Require Import Events lang SC TSO Interp Sched Pick Thrd.

Import ListNotations.

#[local] Notation "(I) t" := (@Maps.TMap.M.Mkt _ t _) (at level 10, only printing).
#[local] Notation "(Q) t" := (@Message.QMap.M.Mkt _ t _) (at level 10, only printing).

(* Example in which the main thread creates two threads and joins one. *)

Example ex_join : toplevel :=
  ([
    thrd_init;
    thrd_cleanup;
    ("main",
      mkCFG "0" ([
        mk_block "0" (
          thrd_create "f" (OP_Atom nullval) "f")
          (Jmp1 "1")
      ] ++ thrd_join "1" (EXP_Ident "f") "2" "j" ++ [
        mk_block "2" [
          ] (Return (OP_Atom (EXP_Ident "j")))
      ]) []);
    ("f",
      mkCFG "0" [mk_block "0" [
      ] (Return (OP_Atom 8%Z))] [])
  ], [
  ]).

Compute burn 3000 (eval_ll_rand_sc ex_join).
Compute burn 6000 (eval_ll_rand_tso ex_join).
(* slow *)
(*Compute burn 6000 (eval_ll_rand_ps ex_join).*)

(* Example with a data race on a counter *)

Example incr : toplevel :=
  ([
    thrd_init;
    thrd_cleanup;
    ("main",
      mkCFG "0" ([
        mk_block "0" (
          [("0", AtomicStore seq_cst (OP_Atom (EXP_Cst (CST_Integer 0%Z))) (OP_Atom (EXP_Global "a")))] ++
          thrd_create "f" (OP_Atom nullval) "2" ++
          thrd_create "f" (OP_Atom nullval) "3")
          (Jmp1 "1")
      ] ++ thrd_join "1" (EXP_Ident "3") "2" "4" ++ [
        mk_block "2"
          [("5", AtomicStore seq_cst (OP_Atom (EXP_Ident "4")) (OP_Atom (EXP_Global "b")))]
          (Return (OP_Atom 0%Z))
      ]) []);
    ("f",
      mkCFG "0" [mk_block "0" [
        ("0", AtomicLoad not_atomic (OP_Atom (EXP_Global "a")));
        ("1", AtomicStore not_atomic (OP_IBinop Add (EXP_Ident "0") 1) (OP_Atom (EXP_Global "a")))
      ] (Return (OP_Atom 8%Z))] [])
  ], [
    "a"; "b"
  ]).

Compute (fst (init_globals (snd incr)), burn 5000 (eval_ll_rand_sc incr)).
Compute (fst (init_globals (snd incr)), burn 10000 (eval_ll_rand_tso incr)).
(* eats all my ram *)
(*Compute (fst (init_globals (snd incr)), burn 20000 (eval_ll_rand_ps incr)).*)

(* Example that distinguishes SC and TSO *)

Example ex_tso : toplevel :=
  ([
    simple_thrd_init;
    simple_thrd_cleanup;
    ("main",
      mkCFG "0" ([
        mk_block "0" ([
          ("1", AtomicStore monotonic (OP_Atom 0) (OP_Atom (EXP_Global "a")));
          ("2", AtomicStore monotonic (OP_Atom 0) (OP_Atom (EXP_Global "b")))
        ] ++
          simple_thrd_create "t2" (OP_Atom nullval) "4" ++ [
          ("1", AtomicStore monotonic (OP_Atom 1) (OP_Atom (EXP_Global "a")));
          ("2", AtomicLoad monotonic (OP_Atom (EXP_Global "b")));
          ("3", AtomicStore monotonic (OP_Atom (EXP_Ident "2")) (OP_Atom (EXP_Global "b1")))
        ])
          (Return (OP_Atom 0%Z))
      ]) []
    );
    ("t2",
      mkCFG "0" ([
        mk_block "0" [
          ("1", AtomicStore monotonic (OP_Atom 1) (OP_Atom (EXP_Global "b")));
          ("2", AtomicLoad monotonic (OP_Atom (EXP_Global "a")));
          ("3", AtomicStore monotonic (OP_Atom (EXP_Ident "2")) (OP_Atom (EXP_Global "a1")))
        ] (Return (OP_Atom 0%Z))
      ]) []
    )
  ], [
    "a"; "b"; "a1"; "b1"
  ]).

Definition ex_tso_sc := final_state_sc (interp_ll_sc ex_tso) ["a1"; "b1"].
Definition ex_tso_tso := final_state_tso (interp_ll_tso ex_tso) ["a1"; "b1"].
Definition ex_tso_ps := final_state_ps (interp_ll_ps ex_tso) ["a1"; "b1"].

Compute burn 3000 (interp_sched handle_sched_random _
    (interp_pick handle_pick_random _ ex_tso_sc 0%N) 0%N).
Compute burn 4000 (interp_sched handle_sched_random _
    (interp_pick handle_pick_random _
      (interp_flush handle_flush_random _ ex_tso_tso 1%N) 0%N) 0%N).
Compute (burn 4000 (refine_rand_ps ex_tso_ps 0%N 0%N 0%N)).

(* Example that distinguishes SC/TSO and PS *)

Example ex_ps : toplevel :=
  ([
    simple_thrd_init;
    simple_thrd_cleanup;
    ("main",
      mkCFG "0" ([
        mk_block "0" ([
          ("", AtomicStore monotonic (OP_Atom 0) (OP_Atom (EXP_Global "a")));
          ("", AtomicStore monotonic (OP_Atom 0) (OP_Atom (EXP_Global "b")))
        ] ++
          simple_thrd_create "t2" (OP_Atom 0) "t2" ++ [
          ("a1", AtomicRMW monotonic ATOMIC_xchg (OP_Atom 1) (OP_Atom (EXP_Global "a")));
          ("b1", AtomicRMW monotonic ATOMIC_xchg (OP_Atom 1) (OP_Atom (EXP_Global "b")))
        ])
          (Return (OP_Atom 0%Z))
      ]) []
    );
    ("t2",
      mkCFG "0" ([
        mk_block "0" [
          ("b1", AtomicRMW monotonic ATOMIC_xchg (OP_Atom 2) (OP_Atom (EXP_Global "b")));
          ("a1", AtomicLoad monotonic (OP_Atom (EXP_Global "a")));
          ("", AtomicStore monotonic (OP_Atom (EXP_Ident "a1")) (OP_Atom (EXP_Global "a1")));
          ("", AtomicStore monotonic (OP_Atom (EXP_Ident "b1")) (OP_Atom (EXP_Global "b1")))
        ] (Return (OP_Atom 0%Z))
      ]) []
    )
  ], [
    "a"; "b"; "a1"; "b1"
  ]).

(* Example that distinguishes monotonic and acq_rel orderings *)

Example ex_ra : toplevel :=
  ([
    simple_thrd_init;
    simple_thrd_cleanup;
    ("main",
      mkCFG "0" ([
        mk_block "0" ([
          ("", AtomicStore monotonic (OP_Atom 0) (OP_Atom (EXP_Global "a")));
          ("", AtomicStore monotonic (OP_Atom 0) (OP_Atom (EXP_Global "b")))
        ] ++
          simple_thrd_create "t2" (OP_Atom 0) "t2" ++ [
          ("a1", AtomicRMW monotonic ATOMIC_xchg (OP_Atom 1) (OP_Atom (EXP_Global "a")));
          ("b1", AtomicRMW release ATOMIC_xchg (OP_Atom 1) (OP_Atom (EXP_Global "b")))
        ])
          (Return (OP_Atom 0%Z))
      ]) []
    );
    ("t2",
      mkCFG "0" ([
        mk_block "0" [
          ("b1", AtomicRMW acquire ATOMIC_xchg (OP_Atom 2) (OP_Atom (EXP_Global "b")));
          ("a1", AtomicLoad monotonic (OP_Atom (EXP_Global "a")));
          ("", AtomicStore monotonic (OP_Atom (EXP_Ident "a1")) (OP_Atom (EXP_Global "a1")));
          ("", AtomicStore monotonic (OP_Atom (EXP_Ident "b1")) (OP_Atom (EXP_Global "b1")))
        ] (Return (OP_Atom 0%Z))
      ]) []
    )
  ], [
    "a"; "b"; "a1"; "b1"
  ]).

Definition ex_ps_sc := final_state_sc (interp_ll_sc ex_ps) ["a1"; "b1"].
Definition ex_ps_tso := final_state_tso (interp_ll_tso ex_ps) ["a1"; "b1"].
Definition ex_ps_ps := final_state_ps (interp_ll_ps ex_ps) ["a1"; "b1"].
Definition ex_ra_ps := final_state_ps (interp_ll_ps ex_ra) ["a1"; "b1"].

Compute (fst (init_globals (snd ex_ps)), burn 5000 (eval_ll_rand_sc ex_ps)).
Compute (fst (init_globals (snd ex_ps)), burn 5000 (eval_ll_rand_tso ex_ps)).
Compute (fst (init_globals (snd ex_ps)), burn 5000 (eval_ll_rand_ps ex_ps)).
