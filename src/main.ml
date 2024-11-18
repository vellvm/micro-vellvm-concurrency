open CTreeDefinitions;;
open ExtrOcamlIntConv;;
open Datatypes;;
open Printf;;
open TSO;;
open PS;;
open Examples;;

module TidSet = Set.Make(Int);;

module MemSet = Set.Make(struct
  type t = int list
  let compare = List.compare Int.compare
end);;

let print_memset ms =
  print_string "[\n";
  MemSet.iter (fun x -> List.iter (printf "%d ") x; print_newline ()) ms;
  print_string "]\n";;

let sublists l =
  match l with
  | [] -> [[]]
  | [x] -> [[]; [x]]
  | [x; y] -> [[]; [x]; [y]; [x; y]; [y; x]]
  | _ -> failwith "complicated";;

let rec collect_sc t depth =
  let ret = match observe t with
  | RetF r -> MemSet.singleton(List.map int_of_z r)
  | StuckF -> MemSet.empty
  | GuardF t -> collect_sc t depth
  | StepF t -> collect_sc t depth
  | VisF (_e, _k) -> failwith "Vis (unreachable)"
  | BrF (c, k) ->
    match c with
    | (* Pick *) Coq_inl _ -> (*print_string "pick";*) collect_sc (k (Obj.magic (z_of_int (-50)))) (depth + 1)
    | (* Sched *) Coq_inr (Coq_inl tl) ->
                        (*for i = 0 to depth do print_string " " done;
                    print_string "sched ";
                    List.iter (fun tid -> print_int (int_of_nat tid); print_string " ") tl;
                    print_newline ();*)
        List.fold_left (fun memset tid ->
          MemSet.union
            memset
            (collect_sc (k (Obj.magic tid)) (depth + 1))
        ) MemSet.empty tl
    | (* void1 *) Coq_inr (Coq_inr _) -> MemSet.empty
  in
  ret
;;

let rec collect_tso t depth =
  let ret = match observe t with
  | RetF r -> MemSet.singleton(List.map int_of_z r)
  | StuckF -> MemSet.empty
  | GuardF t -> collect_tso t depth
  | StepF t -> collect_tso t depth
  | VisF (_e, _k) -> failwith "Vis (unreachable)"
  | BrF (c, k) ->
    match c with
    | (* Flush *) Coq_inl s ->
        let to_flush_lists = sublists (flushable s) in
          List.fold_left (fun memset to_flush ->
            MemSet.union
              memset
              (collect_tso (k (Obj.magic to_flush)) (depth + 1))
        ) MemSet.empty to_flush_lists
    | (* Pick *) Coq_inr (Coq_inl _) -> collect_tso (k (Obj.magic (z_of_int (-50)))) (depth + 1)
    | (* Sched *) Coq_inr (Coq_inr (Coq_inl tl)) ->
        List.fold_left (fun memset tid ->
          MemSet.union
            memset
            (collect_tso (k (Obj.magic tid)) (depth + 1))
        ) MemSet.empty tl
    | (* void1 *) Coq_inr (Coq_inr (Coq_inr _)) -> MemSet.empty
  in
  ret
;;

let rec collect_ps t depth =
  let ret = match observe t with
  | RetF r -> MemSet.singleton(List.map int_of_z r)
  | StuckF -> MemSet.empty
  | GuardF t -> collect_ps t depth
  | StepF t -> collect_ps t depth
  | VisF (_e, _k) -> failwith "Vis (unreachable)"
  | BrF (c, k) ->
    match c with
    | (* UpdateView *) Coq_inl (mem, tid, a, kind) ->
        let timestamps = possible_timestamps tid a kind mem in
          List.fold_left (fun memset ts ->
            MemSet.union
              memset
              (collect_ps (k (Obj.magic ts)) (depth + 1))
        ) MemSet.empty timestamps
    | (* Pick *) Coq_inr (Coq_inl _) -> collect_ps (k (Obj.magic (z_of_int (-50)))) (depth + 1)
    | (* Sched *) Coq_inr (Coq_inr (Coq_inl tl)) ->
        List.fold_left (fun memset tid ->
          MemSet.union
            memset
            (collect_ps (k (Obj.magic tid)) (depth + 1))
        ) MemSet.empty tl
    | (* void1 *) Coq_inr (Coq_inr (Coq_inr (Coq_inr (Coq_inr _)))) -> MemSet.empty
    | (* misc *) _ -> collect_ps (k (Obj.magic ())) depth
  in
  ret
;;

Random.self_init ();;
print_string "TSO example (ex_tso in Examples.v)\n";;
print_string "SC:";;
let results = collect_sc (Obj.magic ex_tso_sc) 0;;
print_memset results;;
print_string "TSO:";;
let results = collect_tso (Obj.magic ex_tso_tso) 0;;
print_memset results;;
print_string "PS:";;
let results = collect_ps (Obj.magic ex_tso_ps) 0;;
print_memset results;;
print_string "\nPS example (ex_ps in Examples.v)\n";;
print_string "SC:";;
let results = collect_sc (Obj.magic ex_ps_sc) 0;;
print_memset results;;
print_string "TSO:";;
let results = collect_tso (Obj.magic ex_ps_tso) 0;;
print_memset results;;
print_string "PS:";;
let results = collect_ps (Obj.magic ex_ps_ps) 0;;
print_memset results;;
print_string "PS (acq/rel variant, ex_ra in Examples.v):";;
let results = collect_ps (Obj.magic ex_ra_ps) 0;;
print_memset results;;
