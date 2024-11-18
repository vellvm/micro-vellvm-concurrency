From ITree Require Import Events.Exception.
From CTree Require Import CTree.
From Coq Require Import String ZArith List.
From ExtLib Require Import Structures.Monads.
Unset Universe Checking.
From Mem Require Import Utils Events Thread.

Import ListNotations.

Open Scope string_scope.

Section Syntax.

  Definition block_id := ident.
  Definition register := ident.

  Variant ibinop : Set := | Add | Sub | Mul | UDiv.
  Variant icmp   : Set := Eq|Ne|Ugt|Uge|Ult|Ule.

  Variant constant : Set :=
  | CST_Integer (x:Z)
  | CST_Bool    (b:bool)
  | CST_Null.

  Variant atom : Set :=
  | EXP_Ident   (id:ident)
  | EXP_Global  (id:ident)
  | EXP_Cst     (c:constant).

  Variant exp : Set :=
    | OP_Atom     (v:atom)
    | OP_IBinop   (iop:ibinop) (v1:atom) (v2:atom)
    | OP_ICmp     (cmp:icmp) (v1:atom) (v2:atom).

  Variant atomic_op : Set :=
  | ATOMIC_xchg
  | ATOMIC_add.

  Variant instr : Set :=
    | Op              (op:exp)
    | Alloca          (size : exp)
    | AtomicLoad      (ord : ordering) (ptr:exp)
    | AtomicStore     (ord : ordering) (val:exp) (ptr:exp)
    | AtomicRMW       (ord : ordering) (op: atomic_op) (val:exp) (ptr:exp)
    | AtomicCmpXchg   (ord : ordering) (cmp new ptr: exp)
    | Fence           (ord : ordering)
    | ThreadCreate    (f init cleanup : function_id) (arg : exp)
  .

  Variant terminator : Set :=
    | Return   (v:exp)
    | Jmp1     (br:block_id)
    | Jmp2     (v:exp) (br1:block_id) (br2:block_id)
  .

  Definition code := list (register * instr).

  Record block : Set :=
    mk_block
      {
        blk_id    : block_id;
        blk_code  : code;
        blk_term  : terminator;
      }.


  (** * Open cfg
      A potentially open cfg ([ocfg]) is simply a list of blocks.
   *)
  Definition ocfg := list block.

  (** * cfg
      Each function definition corresponds to a control-flow graph
   - init is the entry block
   - blks is a list of labeled blocks
   - args is the list of identifiers brought into scope by this function
   *)
  Record cfg := mkCFG
                  {
                    init : block_id;
                    blks : ocfg;
                    args : list ident;
                  }.

  Definition definition := (function_id * cfg)%type.

  Definition global := ident.

  Definition toplevel := (list definition * list global)%type.

  Definition find_block (bs: list block) block_id : option block :=
    find (fun b => String.eqb (blk_id b) block_id) bs.

End Syntax.

Section Semantics.

  Context {E B : Type -> Type}.
  Context {HasB0 : B0 -< B} {HasB1 : B1 -< B}.
  Context {HasExcept : exceptE string -< E}
          {HasVar : VarE -< E}
          {HasAlloc : AllocE -< E}
          {HasMemory : MemoryE -< E}
          {HasThread : @ThreadE (list value) -< E}.

  Import MonadNotation.

  Open Scope Z_scope.

  Definition repr_bool (b: bool) : value :=
    (if b then 1 else 0).

  Definition repr_constant (c : constant) : ctree E B value :=
    match c with
    | CST_Integer z => Ret z
    | CST_Bool b => Ret (repr_bool b)
    | CST_Null => Ret nullval
    end.

  Definition repr_atom (a : atom) : ctree E B value :=
    match a with
    | EXP_Ident id => trigger (LocalRead id)
    | EXP_Global id => trigger (GlobalRead id)
    | EXP_Cst cst => repr_constant cst
    end.

  Definition eval_binop op v1 v2 :=
    match op with
    | Add => v1 + v2
    | Sub => v1 - v2
    | Mul => v1 * v2
    | UDiv => v1 / v2
    end.

  Definition eval_cmp op v1 v2 :=
    repr_bool (
      match op with
      | Eq => Z.eqb v1 v2
      | Ne => negb (Z.eqb v1 v2)
      | Ugt => Z.gtb v1 v2
      | Uge => Z.geb v1 v2
      | Ult => Z.ltb v1 v2
      | Ule => Z.leb v1 v2
      end).

  Definition repr_exp (e : exp) : ctree E B value :=
    match e with
    | OP_Atom v =>
      repr_atom v
    | OP_IBinop op v1 v2 =>
      v1 <- repr_atom v1;;
      v2 <- repr_atom v2;;
      Ret (eval_binop op v1 v2)
    | OP_ICmp op v1 v2 =>
      v1 <- repr_atom v1;;
      v2 <- repr_atom v2;;
      Ret (eval_cmp op v1 v2)
    end.

  Definition lift_Z_atomic_fun (f : Z -> Z -> Z) (v x : value) :=
    f v x.

  Definition atomic_fun (op : atomic_op) v :=
    match op with
    | ATOMIC_xchg => fun x => v
    | ATOMIC_add => lift_Z_atomic_fun (fun v x => x + v) v
    end.

  Definition cmpxchg cmp new :=
    fun v => if value_eqb v cmp then new else v.

  Definition get_int v : ctree E B value :=
    Ret v.

  Definition get_pointer v : ctree E B addr :=
    Ret (Z.to_nat v).

  Definition cmpxchg_block addr cmp new : ctree E B unit :=
    v <- trigger (ReadWrite acq_rel addr
      (cmpxchg cmp new));;
    if value_eqb v cmp then Ret tt else Stuck.

  Definition spin_cmpxchg addr cmp new : ctree E B unit :=
    CTree.iter
      (fun _ =>
        v <- trigger (ReadWrite acq_rel addr
          (cmpxchg cmp new));;
        Ret (if value_eqb v cmp then inr tt else inl tt))
      tt.

  Definition repr_instr (i : instr) : ctree E B value :=
    match i with
    | Op e =>
      r <- repr_exp e;;
      trigger Yield;;
      Ret r
    | Alloca size =>
      size <- repr_exp size;;
      addr <- trigger (Alloc (Z.to_nat size));;
      Ret (Z.of_nat addr)
    | AtomicLoad o addr =>
      addr <- repr_exp addr;;
      addr <- get_pointer addr;;
      trigger (Read o addr)
    | AtomicStore o v addr =>
      addr <- repr_exp addr;;
      addr <- get_pointer addr;;
      v <- repr_exp v;;
      trigger (Write o addr v);;
      Ret nullval
    | AtomicRMW o op v addr =>
      addr <- repr_exp addr;;
      addr <- get_pointer addr;;
      v <- repr_exp v;;
      trigger (ReadWrite o addr (atomic_fun op v))
    | AtomicCmpXchg o cmp new addr =>
      addr <- repr_exp addr;;
      addr <- get_pointer addr;;
      cmp <- repr_exp cmp;;
      new <- repr_exp new;;
      trigger (ReadWrite o addr (cmpxchg cmp new))
    | Fence o => trigger (Events.Fence o);; Ret nullval
    | ThreadCreate f init cleanup arg =>
      arg <- repr_exp arg;;
      trigger (Spawn f init cleanup [arg]);;
      Ret nullval
    end.

  Definition is_0 v :=
    match v with
    | 0 => true
    | _ => false
    end.

  Definition repr_term  (t : terminator) : ctree E B (block_id + value) :=
    match t with
    | Return e => v <- repr_exp e;;
                  Ret (inr v)
    | Jmp1 bid         => Ret (inl bid)
    | Jmp2 c bid1 bid2 => v <- repr_exp c;;
                          Ret (inl (if is_0 v then bid1 else bid2))
    end.

  Definition repr_instr' (i : register * instr) : ctree E B unit :=
    v <- repr_instr (snd i);;
    trigger (LocalWrite (fst i) v).

  Definition repr_code (c: code): ctree E B unit :=
    map_monad_ repr_instr' c.

  Definition repr_block (b: block) : ctree E B (block_id + value) :=
    repr_code (blk_code b);;
    repr_term (blk_term b).

  Definition repr_ocfg (bks: ocfg)
    : block_id -> ctree E B (block_id + value) :=
    CTree.iter
      (fun bid => match find_block bks bid with
               | None => Ret (inr (inl bid))
               | Some block => trigger Yield;; bd <- repr_block block;;
                              match bd with
                              | inr dv   => Ret (inr (inr dv))
                              | inl bid' => Ret (inl bid')
                              end
               end).

  Definition repr_cfg (f: cfg) : ctree E B value :=
    r <- repr_ocfg (blks f) (init f) ;;
    match r with
    | inl bid => throw ("Can't find block in repr_cfg " ++ bid)
    | inr uv  => ret uv
    end.

  Definition repr_definition (df: definition) : function_id * ctree E B value :=
    (fst df, repr_cfg (snd df)).

  Definition repr_definitions fns := StringMapFacts.of_list (List.map repr_definition fns).

  Definition repr_global (g: global) := g.

  Definition repr_globals (g: list global) := g.

  Definition repr_toplevel (ll: toplevel) (main: function_id) :
      FnMap.t (ctree E B value) * list global :=
    (repr_definitions (fst ll), snd ll).

End Semantics.

Coercion CST_Integer : Z >-> constant.
Coercion EXP_Cst : constant >-> atom.

Import MonadNotation.

(* Write the function arguments to argN registers.
   They are written in reverse order. *)
Definition wrap_thread {E B X} {HasThread : @ThreadE (list value) -< E} {HasVar : VarE -< E}
    (t : ctree E B X) (args : list value) : ctree E B X :=
  map_monad_
    (fun '(n, arg) => trigger Yield;; trigger (LocalWrite ("arg" ++ String.nat2string10 n)%string arg))
    (combine (List.seq 0 (List.length args)) args);;
  t.
